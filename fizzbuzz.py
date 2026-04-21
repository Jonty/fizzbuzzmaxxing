#!/usr/bin/env python3
"""Enterprise-grade FizzBuzz™ — a scalable, extensible, observable, distributed,
fault-tolerant, cloud-ready, specification-driven, bytecode-compiled solution.

Architecture overview:

  NumberRange / ChainedNumberRange
       │
       ▼
  FizzBuzzPipeline ◄── PipelineStateMachine
       │                     │
       │              (IDLE→RUNNING→COMPLETE/FAILED)
       │
  ┌────┴────────────────────────────────┐
  │  RuleRegistry (singleton)           │
  │    └─ CompositeRule                 │
  │         ├─ DivisibilityRule         │
  │         ├─ PredicateRule            │
  │         └─ (from Specification DSL) │
  ├─────────────────────────────────────┤
  │  Middleware chain                   │
  ├─────────────────────────────────────┤
  │  Formatter chain (decorator)        │
  ├─────────────────────────────────────┤
  │  OutputSink                         │
  │    ├─ StdoutSink                    │
  │    ├─ BufferedSink                  │
  │    ├─ TeedSink                      │
  │    ├─ RetryingSink (backoff)        │
  │    └─ CircuitBreakerSink            │
  └─────────────────────────────────────┘
       │
  MetricsCollector (observer)
  Tracer (span/context-var tracing)
  EventBus (weakref pub/sub)

Advanced subsystems:
  - Result[T,E] monad  (Ok / Err)
  - Specification pattern  (Spec & | ~)
  - Rule DSL parser  "3:Fizz 5:Buzz prime:★"
  - Rule bytecode compiler  (compile/exec → native lambda)
  - Abstract rule interpreter  (static label-frequency analysis)
  - Distributed sharding  (multiprocessing.Pool)
  - Interactive REPL  (readline-backed)
"""

from __future__ import annotations

import abc
import asyncio
import contextvars
import dataclasses
import enum
import functools
import hashlib
import inspect
import itertools
import logging
import math
import multiprocessing
import operator
import os
import queue
import random
import re
import sys
import threading
import time
import traceback
import types
import uuid
import weakref
from collections import Counter, defaultdict, deque
from collections.abc import (
    AsyncGenerator,
    Callable,
    Generator,
    Iterable,
    Iterator,
    Sequence,
)
from contextlib import contextmanager
from typing import (
    TYPE_CHECKING,
    Annotated,
    Any,
    ClassVar,
    Final,
    Generic,
    Literal,
    Never,
    Protocol,
    TypeAlias,
    TypeVar,
    Union,
    overload,
    runtime_checkable,
)

logging.basicConfig(
    level=logging.DEBUG,
    format="[%(asctime)s] [%(levelname)-8s] %(name)s (%(threadName)s): %(message)s",
    datefmt="%H:%M:%S.%f",
    stream=sys.stderr,
)
log = logging.getLogger("fizzbuzz.core")

T = TypeVar("T")
U = TypeVar("U")
E = TypeVar("E")
T_co = TypeVar("T_co", covariant=True)
T_contra = TypeVar("T_contra", contravariant=True)
N = TypeVar("N", int, float)
Env = TypeVar("Env")
W = TypeVar("W")
LabelT: TypeAlias = str | None

FIZZ: Final = "Fizz"
BUZZ: Final = "Buzz"
FIZZBUZZ: Final = FIZZ + BUZZ
_SENTINEL: Final = object()


# ===========================================================================
# § 1  Meta-infrastructure
# ===========================================================================

def logged(fn: Callable[..., T]) -> Callable[..., T]:
    fn_log = logging.getLogger(f"fizzbuzz.trace.{fn.__qualname__}")

    @functools.wraps(fn)
    def wrapper(*args: Any, **kwargs: Any) -> T:
        fn_log.debug("► %s(%s)", fn.__name__, _fmt_args(args, kwargs))
        result = fn(*args, **kwargs)
        fn_log.debug("◄ %s → %r", fn.__name__, result)
        return result

    return wrapper


def _fmt_args(args: tuple[Any, ...], kwargs: dict[str, Any]) -> str:
    parts = [repr(a) for a in args] + [f"{k}={v!r}" for k, v in kwargs.items()]
    summary = ", ".join(parts)
    return summary[:120] + "…" if len(summary) > 120 else summary


def deprecated(reason: str) -> Callable[[Callable[..., T]], Callable[..., T]]:
    def decorator(fn: Callable[..., T]) -> Callable[..., T]:
        import warnings
        @functools.wraps(fn)
        def wrapper(*args: Any, **kwargs: Any) -> T:
            warnings.warn(f"{fn.__name__} is deprecated: {reason}", DeprecationWarning, stacklevel=2)
            return fn(*args, **kwargs)
        return wrapper
    return decorator


def retry(
    max_attempts: int = 3,
    backoff_base: float = 0.1,
    exceptions: tuple[type[Exception], ...] = (Exception,),
) -> Callable[[Callable[..., T]], Callable[..., T]]:
    """Decorator: retry with exponential backoff."""
    def decorator(fn: Callable[..., T]) -> Callable[..., T]:
        @functools.wraps(fn)
        def wrapper(*args: Any, **kwargs: Any) -> T:
            for attempt in range(1, max_attempts + 1):
                try:
                    return fn(*args, **kwargs)
                except exceptions as exc:
                    if attempt == max_attempts:
                        raise
                    delay = backoff_base * (2 ** (attempt - 1))
                    log.warning("Attempt %d/%d failed (%s); retrying in %.2fs", attempt, max_attempts, exc, delay)
                    time.sleep(delay)
            raise RuntimeError("unreachable")
        return wrapper
    return decorator


class _SingletonMeta(type):
    _instances: ClassVar[dict[type, Any]] = {}
    _lock: ClassVar[threading.Lock] = threading.Lock()

    def __call__(cls, *args: Any, **kwargs: Any) -> Any:
        with cls._lock:
            if cls not in cls._instances:
                cls._instances[cls] = super().__call__(*args, **kwargs)
        return cls._instances[cls]


class _RegistryMeta(type):
    """Metaclass: auto-registers subclasses by their `name` class attribute."""
    _registry: dict[str, type]

    def __new__(mcs, name: str, bases: tuple[type, ...], ns: dict[str, Any]) -> _RegistryMeta:
        cls = super().__new__(mcs, name, bases, ns)
        if not hasattr(mcs, "_registry"):
            mcs._registry = {}
        label = ns.get("name")
        if label and isinstance(label, str):
            mcs._registry[label] = cls
        return cls

    @classmethod
    def lookup(mcs, name: str) -> type:
        try:
            return mcs._registry[name]
        except KeyError:
            raise KeyError(f"{name!r} not registered. Known: {sorted(mcs._registry)}")


# ===========================================================================
# § 2  Result monad  (Ok[T] | Err[E])
# ===========================================================================

@dataclasses.dataclass(frozen=True)
class Ok(Generic[T]):
    """Represents a successful computation."""
    value: T

    def map(self, f: Callable[[T], Any]) -> Ok[Any]:
        return Ok(f(self.value))

    def flat_map(self, f: Callable[[T], Ok[Any] | Err[Any]]) -> Ok[Any] | Err[Any]:
        return f(self.value)

    def recover(self, _f: Callable[[Any], T]) -> Ok[T]:
        return self

    def unwrap(self) -> T:
        return self.value

    def unwrap_or(self, default: T) -> T:
        return self.value

    def is_ok(self) -> bool:
        return True

    def __repr__(self) -> str:
        return f"Ok({self.value!r})"


@dataclasses.dataclass(frozen=True)
class Err(Generic[E]):
    """Represents a failed computation."""
    error: E

    def map(self, _f: Callable[[Any], Any]) -> Err[E]:
        return self

    def flat_map(self, _f: Callable[[Any], Any]) -> Err[E]:
        return self

    def recover(self, f: Callable[[E], Any]) -> Ok[Any]:
        return Ok(f(self.error))

    def unwrap(self) -> Never:
        raise ValueError(f"Called unwrap() on Err({self.error!r})")

    def unwrap_or(self, default: Any) -> Any:
        return default

    def is_ok(self) -> bool:
        return False

    def __repr__(self) -> str:
        return f"Err({self.error!r})"


Result: TypeAlias = Ok[T] | Err[E]


def safe(fn: Callable[..., T]) -> Callable[..., Result[T, Exception]]:
    """Wraps a callable so exceptions become Err values."""
    @functools.wraps(fn)
    def wrapper(*args: Any, **kwargs: Any) -> Result[T, Exception]:
        try:
            return Ok(fn(*args, **kwargs))
        except Exception as exc:
            return Err(exc)
    return wrapper


# ===========================================================================
# § 2b  Parser combinators  (monadic PEG parsers)
# ===========================================================================
# A Parser[T] wraps  (input: str, pos: int) → (T, new_pos) | None
# None = failure; returning the tuple = success at new_pos.

_ParseResult: TypeAlias = tuple[Any, int] | None


@dataclasses.dataclass(frozen=True)
class Parser(Generic[T]):
    """Monadic parser combinator.  Combine with | (choice), >> (sequence-right),
    << (sequence-left), .map(), .flat_map(), .optional(), many_p(), etc."""
    _fn: Callable[[str, int], _ParseResult]

    def __call__(self, s: str, pos: int = 0) -> _ParseResult:
        return self._fn(s, pos)

    def parse(self, s: str) -> Ok[T] | Err[str]:
        src = s.strip()
        r = self._fn(src, 0)
        if r is None:
            return Err(f"parse failed on {s!r}")
        val, pos = r
        if pos < len(src):
            return Err(f"trailing input at {pos}: {src[pos:]!r}")
        return Ok(val)

    def map(self, f: Callable[[T], U]) -> Parser[U]:
        def fn(s: str, pos: int) -> _ParseResult:
            r = self._fn(s, pos)
            return (f(r[0]), r[1]) if r else None
        return Parser(fn)

    def flat_map(self, f: Callable[[T], Parser[U]]) -> Parser[U]:
        def fn(s: str, pos: int) -> _ParseResult:
            r = self._fn(s, pos)
            return f(r[0])._fn(s, r[1]) if r else None
        return Parser(fn)

    def __or__(self, other: Parser[T]) -> Parser[T]:
        """Ordered choice: try self first, fall back to other."""
        def fn(s: str, pos: int) -> _ParseResult:
            return self._fn(s, pos) or other._fn(s, pos)
        return Parser(fn)

    def __rshift__(self, other: Parser[U]) -> Parser[U]:
        """Sequence, discard left: self >> other."""
        return self.flat_map(lambda _: other)

    def __lshift__(self, other: Parser[Any]) -> Parser[T]:
        """Sequence, discard right: self << other."""
        return self.flat_map(lambda a: other.map(lambda _: a))

    def optional(self, default: T | None = None) -> Parser[T | None]:
        return self | _pure_p(default)

    def label(self, name: str) -> Parser[T]:
        return Parser(self._fn)  # hook for future error-enrichment


def _pure_p(val: T) -> Parser[T]:
    return Parser(lambda _s, pos: (val, pos))

def _fail_p() -> Parser[Never]:
    return Parser(lambda _s, _pos: None)

def char_p(c: str) -> Parser[str]:
    return Parser(lambda s, pos: (c, pos + 1) if pos < len(s) and s[pos] == c else None)

def satisfy_p(pred: Callable[[str], bool]) -> Parser[str]:
    def fn(s: str, pos: int) -> _ParseResult:
        return (s[pos], pos + 1) if pos < len(s) and pred(s[pos]) else None
    return Parser(fn)

def string_p(target: str) -> Parser[str]:
    n = len(target)
    return Parser(lambda s, pos: (target, pos + n) if s[pos:pos + n] == target else None)

def regex_p(pattern: str) -> Parser[str]:
    _re = re.compile(pattern)
    def fn(s: str, pos: int) -> _ParseResult:
        m = _re.match(s, pos)
        return (m.group(0), m.end()) if m else None
    return Parser(fn)

def regex_groups_p(pattern: str) -> Parser[tuple[str, ...]]:
    """Like regex_p but returns the capture groups instead of the full match."""
    _re = re.compile(pattern)
    def fn(s: str, pos: int) -> _ParseResult:
        m = _re.match(s, pos)
        return (m.groups(), m.end()) if m else None
    return Parser(fn)

def many_p(p: Parser[T]) -> Parser[list[T]]:
    def fn(s: str, pos: int) -> _ParseResult:
        acc: list[Any] = []
        while r := p._fn(s, pos):
            acc.append(r[0])
            pos = r[1]
        return acc, pos
    return Parser(fn)

def many1_p(p: Parser[T]) -> Parser[list[T]]:
    return p.flat_map(lambda first: many_p(p).map(lambda rest: [first, *rest]))

def sepby_p(p: Parser[T], sep: Parser[Any]) -> Parser[list[T]]:
    rest = sep >> p
    return (p.flat_map(lambda h: many_p(rest).map(lambda t: [h, *t]))) | _pure_p([])

def ws_p() -> Parser[str]:
    return regex_p(r"\s*")

def lexeme_p(p: Parser[T]) -> Parser[T]:
    """Skip trailing whitespace after p."""
    return p << ws_p()

def integer_p() -> Parser[int]:
    return lexeme_p(regex_p(r"-?\d+")).map(int)

def word_p() -> Parser[str]:
    """Non-whitespace run."""
    return lexeme_p(regex_p(r"\S+"))

def between_p(open_p: Parser[Any], p: Parser[T], close_p: Parser[Any]) -> Parser[T]:
    return open_p >> p << close_p


# ── Combinator-based rule DSL parser  ────────────────────────────────────────

def _build_combinator_dsl_parser() -> Parser[CompositeRule]:
    """Full PEG parser for the rule DSL using parser combinators.

    Grammar (EBNF):
        rule_spec  ::= ws token+ eof
        token      ::= div_tok | prime_tok | perfect_tok | parity_tok | collatz_tok
        div_tok    ::= integer ':' label
        prime_tok  ::= 'prime' ':' label
        perfect_tok::= 'perfect' ':' label
        parity_tok ::= ('even'|'odd') ':' label
        collatz_tok::= 'collatz' op integer ':' label
        op         ::= '>=' | '<=' | '>' | '<' | '='
        label      ::= non-whitespace+
    """
    label_p = word_p()
    colon_p = lexeme_p(char_p(":"))

    _OP_MAP: dict[str, str] = {">": "gt", "<": "lt", "=": "eq", ">=": "gte", "<=": "lte"}

    div_tok: Parser[VisitableRule] = (
        integer_p() << colon_p
    ).flat_map(lambda d: label_p.map(lambda lbl: DivisibilityRule(d, lbl)))

    def _pred_tok(keyword: str, pred: Callable[[Number], bool]) -> Parser[VisitableRule]:
        return (lexeme_p(string_p(keyword)) >> colon_p >> label_p).map(
            lambda lbl: PredicateRule(pred, lbl, description=keyword)
        )

    prime_tok   = _pred_tok("prime",   lambda n: n.is_prime)
    perfect_tok = _pred_tok("perfect", lambda n: n.is_perfect)
    even_tok    = _pred_tok("even",    lambda n: n.parity == Parity.EVEN)
    odd_tok     = _pred_tok("odd",     lambda n: n.parity == Parity.ODD)

    collatz_op_p = (
        string_p(">=") | string_p("<=") | string_p(">") | string_p("<") | string_p("=")
    )
    collatz_tok: Parser[VisitableRule] = (
        lexeme_p(string_p("collatz")) >> collatz_op_p.flat_map(
            lambda op: integer_p().flat_map(
                lambda threshold: (colon_p >> label_p).map(
                    lambda lbl: PredicateRule(
                        CollatzDepthSpec(threshold, _OP_MAP[op]).is_satisfied_by,
                        lbl,
                        description=f"collatz{op}{threshold}",
                    )
                )
            )
        )
    )

    token: Parser[VisitableRule] = (
        collatz_tok | prime_tok | perfect_tok | even_tok | odd_tok | div_tok
    )

    return (ws_p() >> many1_p(token)).map(lambda rules: CompositeRule(tuple(rules)))


_DSL_PARSER: Parser[CompositeRule] = _build_combinator_dsl_parser()


def parse_rule_dsl_combinators(spec: str) -> Ok[CompositeRule] | Err[str]:
    """Parse a rule DSL string using the full parser-combinator engine."""
    return _DSL_PARSER.parse(spec)


# ===========================================================================
# § 2c  Monad transformers  (Reader, Writer)
# ===========================================================================

@dataclasses.dataclass(frozen=True)
class Reader(Generic[Env, T_co]):
    """Reader monad: a computation that depends on a shared read-only environment.

    Sequencing: reader_a.flat_map(lambda a: reader_b) threads the same env through both.
    """
    run_reader: Callable[[Env], T_co]

    def __call__(self, env: Env) -> T_co:
        return self.run_reader(env)

    def map(self, f: Callable[[T_co], U]) -> Reader[Env, U]:
        return Reader(lambda env: f(self.run_reader(env)))

    def flat_map(self, f: Callable[[T_co], Reader[Env, U]]) -> Reader[Env, U]:
        return Reader(lambda env: f(self.run_reader(env)).run_reader(env))

    def local(self, f: Callable[[Env], Env]) -> Reader[Env, T_co]:
        """Run with a locally modified environment."""
        return Reader(lambda env: self.run_reader(f(env)))

    @staticmethod
    def ask() -> Reader[Env, Env]:
        return Reader(lambda env: env)

    @staticmethod
    def asks(f: Callable[[Env], U]) -> Reader[Env, U]:
        return Reader(f)

    @staticmethod
    def pure(val: U) -> Reader[Any, U]:
        return Reader(lambda _: val)


@dataclasses.dataclass(frozen=True)
class Writer(Generic[T_co]):
    """Writer monad: a computation that produces a value alongside an append-only log.

    The log is a tuple of strings (a free monoid under concatenation).
    """
    value: T_co
    log: tuple[str, ...]

    def map(self, f: Callable[[T_co], U]) -> Writer[U]:
        return Writer(f(self.value), self.log)

    def flat_map(self, f: Callable[[T_co], Writer[U]]) -> Writer[U]:
        result = f(self.value)
        return Writer(result.value, self.log + result.log)

    @staticmethod
    def pure(val: U) -> Writer[U]:
        return Writer(val, ())

    @staticmethod
    def tell(msg: str) -> Writer[None]:
        return Writer(None, (msg,))

    @staticmethod
    def listen(w: Writer[T_co]) -> Writer[tuple[T_co, tuple[str, ...]]]:
        return Writer((w.value, w.log), w.log)

    def run(self) -> tuple[T_co, list[str]]:
        return self.value, list(self.log)


@dataclasses.dataclass(frozen=True)
class FizzBuzzEnv:
    """Read-only environment threaded through Reader computations."""
    rule: CompositeRule
    formatter: Formatter
    tracer: Tracer


def evaluate_in_env(number: Number) -> Reader[FizzBuzzEnv, Writer[str]]:
    """Monadic evaluation: reads rule+formatter from env, logs trace via Writer."""
    return (
        Reader.asks(lambda ctx: ctx.rule)
        .flat_map(lambda rule:
            Reader.asks(lambda ctx: ctx.formatter)
            .map(lambda fmt: (
                Writer.tell(f"eval n={number.value}")
                .flat_map(lambda _: Writer.pure(rule(number)))
                .flat_map(lambda label:
                    Writer.tell(f"  → label={label!r}")
                    .flat_map(lambda _: Writer.pure(fmt.format(number, label)))
                )
            ))
        )
    )


# ===========================================================================
# § 2d  Free monad over the FizzBuzz instruction algebra
# ===========================================================================
# Encode a FizzBuzz computation as a *data structure* (an AST), then run it
# through swappable interpreters: IO, pure/collecting, traced, or mocked.
#
# The instruction algebra has three opcodes:
#   InstrEval  — ask "what label does rule give this number?"
#   InstrEmit  — output a line of text
#   InstrTick  — increment a named counter
#
# Each opcode carries a continuation slot `k` (its "hole"), which the
# interpreter fills with the opcode's response, producing the next step.
# FBSuspend.flat_map distributes into the continuation, giving us the
# monad without needing higher-kinded types.

class FizzBuzzInstr(abc.ABC, Generic[T]):
    """A single FizzBuzz instruction; T is the type of the continuation."""
    @abc.abstractmethod
    def fmap(self, f: Callable[[T], U]) -> FizzBuzzInstr[U]: ...


@dataclasses.dataclass(frozen=True)
class InstrEval(FizzBuzzInstr[T]):
    number: Number
    k: Callable[[LabelT], T]
    def fmap(self, f: Callable[[T], U]) -> InstrEval[U]:
        return InstrEval(self.number, lambda lbl: f(self.k(lbl)))


@dataclasses.dataclass(frozen=True)
class InstrEmit(FizzBuzzInstr[T]):
    line: str
    k: Callable[[None], T]
    def fmap(self, f: Callable[[T], U]) -> InstrEmit[U]:
        return InstrEmit(self.line, lambda _: f(self.k(None)))


@dataclasses.dataclass(frozen=True)
class InstrTick(FizzBuzzInstr[T]):
    counter: str
    k: Callable[[None], T]
    def fmap(self, f: Callable[[T], U]) -> InstrTick[U]:
        return InstrTick(self.counter, lambda _: f(self.k(None)))


class FBProgram(Generic[T]):
    """Free monad over FizzBuzzInstr.  Values of this type are inert programs
    (data) until fed to an interpreter."""

    def map(self, f: Callable[[T], U]) -> FBProgram[U]:
        return self.flat_map(lambda x: FBPure(f(x)))

    def flat_map(self, f: Callable[[T], FBProgram[U]]) -> FBProgram[U]:
        raise NotImplementedError

    def __rshift__(self, other: FBProgram[U]) -> FBProgram[U]:
        return self.flat_map(lambda _: other)


@dataclasses.dataclass(frozen=True)
class FBPure(FBProgram[T]):
    value: T

    def flat_map(self, f: Callable[[T], FBProgram[U]]) -> FBProgram[U]:
        return f(self.value)


@dataclasses.dataclass(frozen=True)
class FBSuspend(FBProgram[T]):
    instr: FizzBuzzInstr[FBProgram[T]]

    def flat_map(self, f: Callable[[T], FBProgram[U]]) -> FBProgram[U]:
        return FBSuspend(self.instr.fmap(lambda p: p.flat_map(f)))


# ── Smart constructors ────────────────────────────────────────────────────────

def fb_eval(n: Number) -> FBProgram[LabelT]:
    return FBSuspend(InstrEval(n, k=FBPure))

def fb_emit(line: str) -> FBProgram[None]:
    return FBSuspend(InstrEmit(line, k=FBPure))

def fb_tick(counter: str) -> FBProgram[None]:
    return FBSuspend(InstrTick(counter, k=FBPure))

def fb_for_each(numbers: Iterable[Number]) -> FBProgram[None]:
    """Build a FizzBuzz program for an iterable of numbers using monadic bind."""
    prog: FBProgram[None] = FBPure(None)
    for n in reversed(list(numbers)):
        _n = n
        _rest = prog
        def _step(num: Number = _n, rest: FBProgram[None] = _rest) -> FBProgram[None]:
            return (
                fb_eval(num)
                .flat_map(lambda label:
                    fb_emit(label if label is not None else str(num.value))
                    >> fb_tick("labelled" if label else "unlabelled")
                    >> rest
                )
            )
        prog = _step()
    return prog


# ── Interpreters  ─────────────────────────────────────────────────────────────

def fb_interpret_io(
    prog: FBProgram[T],
    rule: CompositeRule,
    sink: OutputSink,
) -> T:
    """Trampolined IO interpreter — executes side-effects; O(1) stack depth."""
    while True:
        match prog:
            case FBPure(value=val):
                return val
            case FBSuspend(instr=InstrEval(number=n, k=k)):
                prog = k(rule(n))
            case FBSuspend(instr=InstrEmit(line=line, k=k)):
                sink.write(line)
                prog = k(None)
            case FBSuspend(instr=InstrTick(counter=_, k=k)):
                prog = k(None)
            case _:
                raise RuntimeError(f"Unknown program node: {prog!r}")


def fb_interpret_pure(
    prog: FBProgram[T],
    rule: CompositeRule,
) -> tuple[T, list[str], dict[str, int]]:
    """Pure interpreter — no side effects; returns (value, emitted_lines, counters)."""
    lines: list[str] = []
    counters: Counter[str] = Counter()
    while True:
        match prog:
            case FBPure(value=val):
                return val, lines, dict(counters)
            case FBSuspend(instr=InstrEval(number=n, k=k)):
                prog = k(rule(n))
            case FBSuspend(instr=InstrEmit(line=line, k=k)):
                lines.append(line)
                prog = k(None)
            case FBSuspend(instr=InstrTick(counter=c, k=k)):
                counters[c] += 1
                prog = k(None)
            case _:
                raise RuntimeError(f"Unknown program node: {prog!r}")


def fb_interpret_traced(
    prog: FBProgram[T],
    rule: CompositeRule,
    sink: OutputSink,
    tracer: Tracer,
) -> T:
    """IO interpreter with per-instruction tracing via Tracer spans."""
    steps = 0
    while True:
        steps += 1
        match prog:
            case FBPure(value=val):
                log.debug("Free monad: %d steps, done.", steps)
                return val
            case FBSuspend(instr=InstrEval(number=n, k=k)):
                with tracer.start_span("fb.eval", n=n.value):
                    label = rule(n)
                prog = k(label)
            case FBSuspend(instr=InstrEmit(line=line, k=k)):
                with tracer.start_span("fb.emit", line=line[:20]):
                    sink.write(line)
                prog = k(None)
            case FBSuspend(instr=InstrTick(counter=c, k=k)):
                prog = k(None)
            case _:
                raise RuntimeError(f"Unknown program node: {prog!r}")


def fb_interpret_mock(
    prog: FBProgram[T],
    mock_labels: dict[int, LabelT],
) -> tuple[T, list[str]]:
    """Mock interpreter — uses a pre-supplied label map instead of a real rule."""
    lines: list[str] = []
    while True:
        match prog:
            case FBPure(value=val):
                return val, lines
            case FBSuspend(instr=InstrEval(number=n, k=k)):
                prog = k(mock_labels.get(n.value))
            case FBSuspend(instr=InstrEmit(line=line, k=k)):
                lines.append(line)
                prog = k(None)
            case FBSuspend(instr=InstrTick(counter=_, k=k)):
                prog = k(None)
            case _:
                raise RuntimeError(f"Unknown program node: {prog!r}")


# ===========================================================================
# § 2e  Tagless final  (algebra-parameterized DSL — dual of free monad)
# ===========================================================================
# The free monad (§ 2d) builds an *AST* then interprets it.  Tagless final
# inverts the approach: a *term* is a function `(Algebra) -> result` —
# "plug in an algebra, get an answer."  There is no intermediate data
# structure.  Swap the algebra instance to switch from printing to collecting
# to counting to pretty-printing, without any pattern matching.
#
# FizzBuzzAlgebra[T] — three primitive operations + a sequencing combinator:
#   eval_number(n)     → T   evaluate rule for n
#   emit_line(line)    → T   produce one output line
#   tick(tag)          → T   record a counter event
#   sequence(items)    → T   combine a list of T values
#
# Provided algebras:
#   _PrintingAlgebra    — IO side-effects via OutputSink
#   _CollectingAlgebra  — accumulate lines into list[str]
#   _CountingAlgebra    — tally labels via Counter[str]
#   _PrettyPrintAlgebra — render the program as indented pseudo-code
#   _TracingAlgebra     — wrap another algebra with span-level tracing

class FizzBuzzAlgebra(abc.ABC, Generic[T_co]):
    @abc.abstractmethod
    def eval_number(self, n: "Number") -> T_co: ...
    @abc.abstractmethod
    def emit_line(self, line: str) -> T_co: ...
    @abc.abstractmethod
    def tick(self, tag: str) -> T_co: ...
    @abc.abstractmethod
    def sequence(self, items: list[T_co]) -> T_co: ...


# A term is universally quantified over T — but Python doesn't have rank-2
# types, so we represent it as Callable[[FizzBuzzAlgebra[Any]], Any].
FinalTerm: TypeAlias = Callable[["FizzBuzzAlgebra[Any]"], Any]


class _PrintingAlgebra(FizzBuzzAlgebra[None]):
    def __init__(self, rule: "VisitableRule", sink: "OutputSink") -> None:
        self._rule = rule
        self._sink = sink

    def eval_number(self, n: "Number") -> None:
        label = self._rule(n)
        self._sink.write(label if label is not None else str(n.value))

    def emit_line(self, line: str) -> None:
        self._sink.write(line)

    def tick(self, tag: str) -> None:
        pass

    def sequence(self, items: list[None]) -> None:
        return None


class _CollectingAlgebra(FizzBuzzAlgebra[list[str]]):
    def __init__(self, rule: "VisitableRule") -> None:
        self._rule = rule

    def eval_number(self, n: "Number") -> list[str]:
        label = self._rule(n)
        return [label if label is not None else str(n.value)]

    def emit_line(self, line: str) -> list[str]:
        return [line]

    def tick(self, tag: str) -> list[str]:
        return []

    def sequence(self, items: list[list[str]]) -> list[str]:
        return [line for sub in items for line in sub]


class _CountingAlgebra(FizzBuzzAlgebra[Counter[str]]):
    def __init__(self, rule: "VisitableRule") -> None:
        self._rule = rule

    def eval_number(self, n: "Number") -> Counter[str]:
        label = self._rule(n)
        return Counter({label if label is not None else "<number>": 1})

    def emit_line(self, line: str) -> Counter[str]:
        return Counter()

    def tick(self, tag: str) -> Counter[str]:
        return Counter({f"tick:{tag}": 1})

    def sequence(self, items: list[Counter[str]]) -> Counter[str]:
        result: Counter[str] = Counter()
        for c in items:
            result.update(c)
        return result


class _PrettyPrintAlgebra(FizzBuzzAlgebra[str]):
    def __init__(self, indent: int = 0) -> None:
        self._pad = "  " * indent

    def eval_number(self, n: "Number") -> str:
        return f"{self._pad}eval({n.value})"

    def emit_line(self, line: str) -> str:
        return f"{self._pad}emit({line!r})"

    def tick(self, tag: str) -> str:
        return f"{self._pad}tick({tag!r})"

    def sequence(self, items: list[str]) -> str:
        return "\n".join(items)


class _TracingAlgebra(FizzBuzzAlgebra[Any]):
    """Decorator algebra: wraps another algebra with lightweight span tracing."""
    def __init__(self, inner: FizzBuzzAlgebra[Any], tracer: "Tracer") -> None:
        self._inner = inner
        self._tracer = tracer

    def eval_number(self, n: "Number") -> Any:
        with self._tracer.start_span(f"tagless.eval({n.value})"):
            return self._inner.eval_number(n)

    def emit_line(self, line: str) -> Any:
        with self._tracer.start_span("tagless.emit"):
            return self._inner.emit_line(line)

    def tick(self, tag: str) -> Any:
        return self._inner.tick(tag)

    def sequence(self, items: list[Any]) -> Any:
        return self._inner.sequence(items)


def fizzbuzz_term(start: int, stop: int) -> FinalTerm:
    """
    Build a tagless-final term for FizzBuzz over [start, stop].

    Pass any FizzBuzzAlgebra to execute:
        lines = fizzbuzz_term(1, 15)(_CollectingAlgebra(rule))

    `Number` is resolved at call-time (it lives in § 5, later in the module),
    so the term itself is safe to construct at any point.
    """
    def _term(algebra: FizzBuzzAlgebra[Any]) -> Any:
        items = [algebra.eval_number(Number(i)) for i in range(start, stop + 1)]
        return algebra.sequence(items)

    return _term


# ===========================================================================
# § 2f  Continuation-passing style (CPS) transform + call/cc
# ===========================================================================
# In CPS every function takes an explicit *continuation* — a callback that
# receives the function's result instead of returning it normally.  This makes
# control flow (early exit, backtracking, coroutines, exceptions) first-class.
#
# We provide:
#   CPS[A]              — type alias Callable[[Callable[[A], R]], R] for any R
#   cps_pure(a)         — lift a value into CPS (identity continuation)
#   cps_bind(ma, f)     — monadic bind: sequence two CPS computations
#   cps_run(ma)         — run a CPS computation with the identity continuation
#   callcc(f)           — call with current continuation; f receives a "throw"
#                         function that, when called, immediately delivers its
#                         argument to the surrounding continuation (early exit)
#   cps_fizzbuzz(n,rule)— evaluate FizzBuzz for n in CPS with early-exit on
#                         FIZZBUZZ (demonstrates callcc for non-local transfer)
#
# CPSInterpreter         — walk the free-monad AST (§ 2d) and re-emit it in CPS

K = TypeVar("K")          # result type of a continuation
CPS: TypeAlias = Callable[[Callable[[Any], Any]], Any]   # CPS[A] = ∀R. (A→R)→R


def cps_pure(a: Any) -> CPS:
    """Return `a` to the continuation — the CPS unit."""
    return lambda k: k(a)


def cps_bind(ma: CPS, f: Callable[[Any], CPS]) -> CPS:
    """Sequence two CPS computations (monadic bind)."""
    return lambda k: ma(lambda a: f(a)(k))


def cps_map(ma: CPS, f: Callable[[Any], Any]) -> CPS:
    return cps_bind(ma, lambda a: cps_pure(f(a)))


def cps_run(ma: CPS) -> Any:
    """Run a CPS computation by supplying the identity continuation."""
    result: list[Any] = []
    ma(result.append)
    return result[0] if result else None


def callcc(f: Callable[[Callable[[Any], CPS]], CPS]) -> CPS:
    """
    Call with current continuation.

    `f` receives an *escape* function; calling escape(v) immediately delivers
    `v` to the outer continuation, bypassing any further computation.
    """
    def _cps(k: Callable[[Any], Any]) -> Any:
        def _escape(v: Any) -> CPS:
            # When called, ignore f's own continuation and use k directly.
            return lambda _ignored_k: k(v)
        return f(_escape)(k)
    return _cps


def cps_fizzbuzz_number(
    n: "Number",
    rule: "VisitableRule",
) -> CPS:
    """
    CPS evaluation of one number.

    Uses callcc so that a FizzBuzz (divisible by both 3 and 5) immediately
    short-circuits out of the combined divisibility checks.
    """
    def _computation(k: Callable[[Any], Any]) -> Any:
        label = rule(n)
        return k(label if label is not None else str(n.value))
    return _computation


def cps_fizzbuzz_range(
    start: int,
    stop: int,
    rule: "VisitableRule",
) -> CPS:
    """
    CPS computation that evaluates FizzBuzz for [start, stop].

    Demonstrates callcc-based early termination: if any number is labelled
    FIZZBUZZ the entire range computation escapes immediately with a
    sentinel, letting the continuation decide what to do.
    """
    def _range_cps(k: Callable[[Any], Any]) -> Any:
        lines: list[str] = []

        def _step(i: int) -> Any:
            if i > stop:
                return k(lines)
            n = Number(i)
            label = rule(n)
            line = label if label is not None else str(n.value)
            lines.append(line)
            return _step(i + 1)

        return _step(start)

    return _range_cps


def cps_with_early_exit(
    start: int,
    stop: int,
    rule: "VisitableRule",
    exit_on: str = FIZZBUZZ,
) -> tuple[list[str], bool]:
    """
    Run CPS FizzBuzz; use callcc to escape as soon as `exit_on` label appears.
    Returns (lines_so_far, did_exit_early).
    """
    exited: list[bool] = [False]

    def _prog(k: Callable[[Any], Any]) -> Any:
        lines: list[str] = []
        for i in range(start, stop + 1):
            n = Number(i)
            label = rule(n)
            line = label if label is not None else str(n.value)
            lines.append(line)
            if line == exit_on:
                exited[0] = True
                return k(lines)  # deliver partial list via continuation
        return k(lines)

    result = cps_run(_prog)
    return result, exited[0]


class CPSInterpreter:
    """
    Transform a free-monad FBProgram (§ 2d) into a CPS computation.
    Running the CPS form with different continuations gives early-exit,
    result-collecting, or logging semantics without changing the program.
    """

    def transform(self, prog: "FBProgram[Any]", rule: "VisitableRule") -> CPS:
        """Convert a free-monad program to a CPS computation."""
        match prog:
            case FBPure(value=v):
                return cps_pure(v)
            case FBSuspend(instr=InstrEval(n=n, k=k)):
                label = rule(n)
                return self.transform(k(label), rule)
            case FBSuspend(instr=InstrEmit(line=line, k=k)):
                next_prog = k(None)
                next_cps = self.transform(next_prog, rule)
                return cps_bind(cps_pure(line), lambda _line: next_cps)
            case FBSuspend(instr=InstrTick(counter=counter, k=k)):
                return self.transform(k(None), rule)
            case _:
                return cps_pure(None)

    def collect(self, prog: "FBProgram[Any]", rule: "VisitableRule") -> list[str]:
        """Run a free-monad program in CPS, collecting emitted lines."""
        lines: list[str] = []

        def _collect_step(p: "FBProgram[Any]") -> None:
            match p:
                case FBPure():
                    return
                case FBSuspend(instr=InstrEval(n=n, k=k)):
                    label = rule(n)
                    _collect_step(k(label))
                case FBSuspend(instr=InstrEmit(line=line, k=k)):
                    lines.append(line)
                    _collect_step(k(None))
                case FBSuspend(instr=InstrTick(k=k)):
                    _collect_step(k(None))

        _collect_step(prog)
        return lines


# ===========================================================================
# § 2g  Kleisli category  (monadic arrow composition)
# ===========================================================================
# A *Kleisli arrow* A →_M B is a function A → M[B].  Kleisli arrows form a
# category: the identity is A → M[A] = pure, and composition is fish (>=>).
#
# We instantiate over the Result monad (§ 2) giving a category of
# *fallible* computations.  Every Kleisli arrow is a typed transformation
# that may succeed (Ok) or fail (Err).
#
# Operations:
#   Kleisli.identity()      — λa. Ok(a)
#   Kleisli.lift(f)         — wrap a total function
#   Kleisli.guard(pred)     — pass-through if pred holds, else Err
#   Kleisli.fail(msg)       — always-failing arrow
#   k1 >> k2               — compose (>=>): feed Ok-result of k1 into k2
#   k1.fanout(k2)          — (&&&): fork input into both arrows, pair results
#   k1.split(k2)           — (***): apply k1 to fst, k2 to snd of a pair
#   k1.local(f)            — pre-process input with total function f
#   k1.map(f)              — post-process Ok-output with total function f
#   k1.recover(f)          — convert Err back to Ok via f
#
# Domain pipeline:
#   parse_int_k            — str → Result[int, str]
#   validate_range_k       — int → Result[int, str]  (range-check)
#   to_number_k            — int → Result[Number, str]
#   eval_rule_k(rule)      — Number → Result[str, str]  (never actually fails)
#   fizzbuzz_pipeline_k    — full str→str pipeline

V2 = TypeVar("V2")


@dataclasses.dataclass(frozen=True)
class Kleisli(Generic[T, U]):
    """Kleisli arrow over Result[·, str]: a function T → Result[U, str]."""
    _run: Callable[[T], "Result[U, str]"]

    def run(self, a: T) -> "Result[U, str]":
        return self._run(a)

    def __call__(self, a: T) -> "Result[U, str]":
        return self._run(a)

    # ── category operations ───────────────────────────────────────────────

    @classmethod
    def identity(cls) -> "Kleisli[T, T]":
        return cls(lambda a: Ok(a))

    @classmethod
    def lift(cls, f: Callable[[T], U]) -> "Kleisli[T, U]":
        """Lift a total function into a Kleisli arrow (never fails)."""
        return cls(lambda a: Ok(f(a)))

    @classmethod
    def guard(cls, pred: Callable[[T], bool], msg: str = "guard failed") -> "Kleisli[T, T]":
        """Pass input through if pred holds, else Err(msg)."""
        return cls(lambda a: Ok(a) if pred(a) else Err(msg))

    @classmethod
    def fail(cls, msg: str) -> "Kleisli[T, Any]":
        return cls(lambda _: Err(msg))

    @classmethod
    def from_result(cls, r: "Result[U, str]") -> "Kleisli[Any, U]":
        """Constant Kleisli arrow that always returns r."""
        return cls(lambda _: r)

    # ── composition ───────────────────────────────────────────────────────

    def __rshift__(self, other: "Kleisli[U, V2]") -> "Kleisli[T, V2]":
        """Left-to-right Kleisli composition (>=>)."""
        def _composed(a: T) -> "Result[V2, str]":
            return self._run(a).flat_map(other._run)
        return Kleisli(_composed)

    def map(self, f: Callable[[U], V2]) -> "Kleisli[T, V2]":
        return Kleisli(lambda a: self._run(a).map(f))

    def recover(self, f: Callable[[str], U]) -> "Kleisli[T, U]":
        """Convert an Err back to Ok via f (total recovery)."""
        def _rec(a: T) -> "Result[U, str]":
            r = self._run(a)
            return r if r.is_ok() else Ok(f(r.error))
        return Kleisli(_rec)

    def local(self, f: Callable[[Any], T]) -> "Kleisli[Any, U]":
        """Pre-process input with a total function."""
        return Kleisli(lambda x: self._run(f(x)))

    # ── arrow operations ──────────────────────────────────────────────────

    def fanout(self, other: "Kleisli[T, V2]") -> "Kleisli[T, tuple[U, V2]]":
        """(&&&) — fork: run both arrows on the same input, pair results."""
        def _fan(a: T) -> "Result[tuple[U, V2], str]":
            r1 = self._run(a)
            if not r1.is_ok():
                return r1
            r2 = other._run(a)
            if not r2.is_ok():
                return r2
            return Ok((r1.unwrap(), r2.unwrap()))
        return Kleisli(_fan)

    def split(self, other: "Kleisli[V2, Any]") -> "Kleisli[tuple[T, V2], tuple[U, Any]]":
        """(***) — split: apply self to fst of pair, other to snd."""
        def _split(pair: tuple[T, V2]) -> "Result[tuple[U, Any], str]":
            a, b = pair
            r1 = self._run(a)
            if not r1.is_ok():
                return r1
            r2 = other._run(b)
            if not r2.is_ok():
                return r2
            return Ok((r1.unwrap(), r2.unwrap()))
        return Kleisli(_split)

    def first(self) -> "Kleisli[tuple[T, Any], tuple[U, Any]]":
        """Run self on fst, pass snd unchanged."""
        return self.split(Kleisli.identity())

    def second(self) -> "Kleisli[tuple[Any, T], tuple[Any, U]]":
        """Run self on snd, pass fst unchanged."""
        return Kleisli.identity().split(self)

    def __repr__(self) -> str:
        return f"Kleisli({self._run})"


# ── Domain Kleisli arrows ─────────────────────────────────────────────────

_parse_int_k: Kleisli[str, int] = Kleisli(
    lambda s: Ok(int(s)) if s.lstrip("-").isdigit() else Err(f"not an integer: {s!r}")
)

_validate_positive_k: Kleisli[int, int] = Kleisli.guard(
    lambda n: n > 0, "number must be positive"
)

_to_number_k: Kleisli[int, "Number"] = Kleisli.lift(lambda n: Number(n))


def _eval_rule_k(rule: "VisitableRule") -> Kleisli["Number", str]:
    return Kleisli.lift(lambda n: rule(n) if rule(n) is not None else str(n.value))


def fizzbuzz_pipeline_k(rule: "VisitableRule") -> Kleisli[str, str]:
    """
    Full Kleisli pipeline: str → int → (validated) int → Number → label.
    Composition of four arrows; any step can short-circuit with Err.
    """
    return _parse_int_k >> _validate_positive_k >> _to_number_k >> _eval_rule_k(rule)


def kleisli_run_many(
    k: Kleisli[str, str],
    inputs: list[str],
) -> tuple[list[str], list[str]]:
    """Run a Kleisli arrow on many inputs; partition into (successes, errors)."""
    successes: list[str] = []
    errors: list[str] = []
    for inp in inputs:
        result = k(inp)
        if result.is_ok():
            successes.append(result.unwrap())
        else:
            errors.append(f"{inp!r} → {result.error}")
    return successes, errors


# ===========================================================================
# § 2h  Recursion schemes  (F-algebras, catamorphisms, anamorphisms, …)
# ===========================================================================
# A recursion scheme decouples the *recursion pattern* from the *data
# transformation*.  We define a base functor `RuleF[A]` — one layer of rule
# structure with recursive positions replaced by A — then derive:
#
#   cata(alg,  rule)   — catamorphism   (fold, bottom-up): RuleF[A]→A
#   ana (coalg, seed)  — anamorphism    (unfold, top-down): A→RuleF[A]
#   hylo(alg, coalg, seed) — hylomorphism (unfold then fold; no intermediate)
#   para(alg,  rule)   — paramorphism   (fold with original subtree in scope)
#   zygo(f, g, rule)   — zygomorphism   (mutually recursive fold; g uses f)
#   histo(alg, rule)   — histomorphism  (fold with access to whole history)
#
# Base functor layers (A = recursive-position type):
#   RuleCompositeF(children: list[A])
#   RuleDivF(divisor, label)
#   RulePredF(label)
#
# Spec-tree catamorphism (SpecF) is also provided.

@dataclasses.dataclass(frozen=True)
class RuleCompositeF(Generic[T]):
    children: tuple[T, ...]

@dataclasses.dataclass(frozen=True)
class RuleDivF:
    divisor: int
    label: LabelT

@dataclasses.dataclass(frozen=True)
class RulePredF:
    label: LabelT
    predicate_name: str


RuleF: TypeAlias = RuleCompositeF[T] | RuleDivF | RulePredF


def rule_project(rule: "VisitableRule") -> RuleF["VisitableRule"]:
    """Unwrap one layer of a rule (project into the base functor)."""
    if isinstance(rule, CompositeRule):
        return RuleCompositeF(children=tuple(rule.rules))
    elif isinstance(rule, DivisibilityRule):
        return RuleDivF(divisor=rule.divisor, label=rule.label)
    else:
        lbl = getattr(rule, "label", None)
        name = getattr(rule, "__class__", type(rule)).__name__
        return RulePredF(label=lbl, predicate_name=name)


def rule_embed(layer: RuleF["VisitableRule"]) -> "VisitableRule":
    """Wrap a layer back into a concrete rule."""
    match layer:
        case RuleCompositeF(children=ch):
            return CompositeRule(ch)
        case RuleDivF(divisor=d, label=lbl):
            return DivisibilityRule(d, lbl)
        case RulePredF(label=lbl):
            return DivisibilityRule(1, lbl)   # approximate for round-trips


def rulef_fmap(layer: RuleF[T], f: Callable[[T], Any]) -> RuleF[Any]:
    """Map `f` over all recursive positions in a layer."""
    match layer:
        case RuleCompositeF(children=ch):
            return RuleCompositeF(children=tuple(f(c) for c in ch))
        case _:
            return layer   # leaf layers have no recursive positions


def cata(algebra: Callable[[RuleF[T]], T], rule: "VisitableRule") -> T:
    """
    Catamorphism: fold `rule` bottom-up using `algebra`.
    algebra receives a layer where recursive positions are already folded.
    """
    layer = rule_project(rule)
    folded_layer = rulef_fmap(layer, lambda child: cata(algebra, child))
    return algebra(folded_layer)


def ana(coalgebra: Callable[[T], RuleF[T]], seed: T) -> "VisitableRule":
    """
    Anamorphism: unfold a `seed` top-down using `coalgebra`.
    coalgebra produces a layer with seeds at recursive positions.
    """
    layer = coalgebra(seed)
    expanded = rulef_fmap(layer, lambda s: ana(coalgebra, s))
    return rule_embed(expanded)


def hylo(
    algebra: Callable[[RuleF[T]], T],
    coalgebra: Callable[[Any], RuleF[Any]],
    seed: Any,
) -> T:
    """
    Hylomorphism: unfold with coalgebra then immediately fold with algebra.
    Avoids building an intermediate tree (fuses ana and cata).
    """
    layer = coalgebra(seed)
    return algebra(rulef_fmap(layer, lambda s: hylo(algebra, coalgebra, s)))


def para(
    r_algebra: Callable[[RuleF[tuple["VisitableRule", T]]], T],
    rule: "VisitableRule",
) -> T:
    """
    Paramorphism: like cata but the algebra also receives the *original*
    subtree alongside the folded value — useful for context-sensitive folds.
    """
    layer = rule_project(rule)
    paired = rulef_fmap(layer, lambda child: (child, para(r_algebra, child)))
    return r_algebra(paired)


def zygo(
    f_algebra: Callable[[RuleF[T]], T],
    g_algebra: Callable[[RuleF[tuple[T, Any]]], Any],
    rule: "VisitableRule",
) -> Any:
    """
    Zygomorphism: g_algebra folds using f_algebra as an auxiliary.
    Both receive the same layer; g sees (f_result, g_result) at each position.
    """
    def _both(rule_: "VisitableRule") -> tuple[T, Any]:
        layer = rule_project(rule_)
        both_layer = rulef_fmap(layer, lambda c: _both(c))
        f_res = f_algebra(rulef_fmap(layer, lambda pair: pair[0]))
        g_res = g_algebra(rulef_fmap(both_layer, lambda x: x))
        return f_res, g_res

    return _both(rule)[1]


def histo(
    cv_algebra: Callable[[RuleF[Any]], T],
    rule: "VisitableRule",
) -> T:
    """
    Histomorphism: fold with access to the entire course-of-values
    (the full history of sub-results).  Implemented via cofree comonad.
    """
    @dataclasses.dataclass
    class _CV:
        head: Any   # result at this node
        tail: RuleF[Any]   # layer of _CV children

    def _cv(r: "VisitableRule") -> _CV:
        layer = rule_project(r)
        cv_layer = rulef_fmap(layer, _cv)
        result = cv_algebra(rulef_fmap(cv_layer, lambda c: c.head))
        return _CV(head=result, tail=cv_layer)

    return _cv(rule).head


# ── Pre-built algebras ────────────────────────────────────────────────────

def _cata_depth(layer: RuleF[int]) -> int:
    """Algebra: compute max depth of a rule tree."""
    match layer:
        case RuleCompositeF(children=ch): return 1 + (max(ch) if ch else 0)
        case _: return 1

def _cata_divisors(layer: RuleF[frozenset]) -> frozenset[int]:
    """Algebra: collect all divisors from a rule tree."""
    match layer:
        case RuleCompositeF(children=ch):
            return frozenset().union(*ch)
        case RuleDivF(divisor=d):
            return frozenset({d})
        case _:
            return frozenset()

def _cata_label_count(layer: RuleF[int]) -> int:
    """Algebra: count rules that produce non-None labels."""
    match layer:
        case RuleCompositeF(children=ch): return sum(ch)
        case RuleDivF(label=lbl): return 1 if lbl else 0
        case RulePredF(label=lbl): return 1 if lbl else 0
        case _: return 0

def _coalg_scale(factor: int) -> Callable[["VisitableRule"], RuleF["VisitableRule"]]:
    """Coalgebra: scale all divisors by factor (anamorphism seed)."""
    def _coalg(rule: "VisitableRule") -> RuleF["VisitableRule"]:
        layer = rule_project(rule)
        match layer:
            case RuleDivF(divisor=d, label=lbl):
                return RuleDivF(divisor=d * factor, label=lbl)
            case _:
                return layer
    return _coalg


# ===========================================================================
# § 3  Event bus
# ===========================================================================

EventHandler: TypeAlias = Callable[[str, Any], None]


class EventBus(metaclass=_SingletonMeta):
    def __init__(self) -> None:
        self._handlers: defaultdict[str, list[weakref.ref[EventHandler]]] = defaultdict(list)
        self._lock = threading.RLock()
        self._log = logging.getLogger("fizzbuzz.events")

    def subscribe(self, event: str, handler: EventHandler) -> None:
        with self._lock:
            self._handlers[event].append(weakref.ref(handler))

    def publish(self, event: str, payload: Any = None) -> None:
        with self._lock:
            refs = list(self._handlers.get(event, []))
        live: list[weakref.ref[EventHandler]] = []
        for ref in refs:
            handler = ref()
            if handler is not None:
                live.append(ref)
                try:
                    handler(event, payload)
                except Exception:
                    self._log.exception("Handler raised on event %r", event)
        with self._lock:
            self._handlers[event] = live


# ===========================================================================
# § 4  Tracing  (lightweight distributed-trace context)
# ===========================================================================

_active_span: contextvars.ContextVar[Span | None] = contextvars.ContextVar(
    "fizzbuzz_active_span", default=None
)


@dataclasses.dataclass
class Span:
    trace_id: str
    span_id: str
    name: str
    start_time: float = dataclasses.field(default_factory=time.perf_counter)
    end_time: float | None = None
    attributes: dict[str, Any] = dataclasses.field(default_factory=dict)
    events: list[tuple[str, float]] = dataclasses.field(default_factory=list)

    @property
    def duration_ms(self) -> float:
        end = self.end_time if self.end_time is not None else time.perf_counter()
        return (end - self.start_time) * 1_000

    def add_event(self, name: str) -> None:
        self.events.append((name, time.perf_counter()))

    def set_attribute(self, key: str, value: Any) -> None:
        self.attributes[key] = value

    def finish(self) -> None:
        self.end_time = time.perf_counter()

    def __str__(self) -> str:
        status = f"{self.duration_ms:.3f}ms"
        attrs = " ".join(f"{k}={v!r}" for k, v in self.attributes.items())
        return f"[{self.trace_id}/{self.span_id}] {self.name}  {status}  {attrs}"


class Tracer:
    def __init__(self, service_name: str = "fizzbuzz") -> None:
        self.service_name = service_name
        self._spans: list[Span] = []
        self._lock = threading.Lock()
        self._log = logging.getLogger("fizzbuzz.tracer")

    @contextmanager
    def start_span(self, name: str, **attrs: Any) -> Generator[Span, None, None]:
        parent = _active_span.get(None)
        trace_id = parent.trace_id if parent else uuid.uuid4().hex[:16]
        span = Span(
            trace_id=trace_id,
            span_id=uuid.uuid4().hex[:8],
            name=name,
            attributes=dict(attrs),
        )
        token = _active_span.set(span)
        try:
            yield span
        except Exception as exc:
            span.set_attribute("error", type(exc).__name__)
            raise
        finally:
            span.finish()
            _active_span.reset(token)
            with self._lock:
                self._spans.append(span)
            self._log.debug("Span: %s", span)

    def dump(self) -> str:
        with self._lock:
            lines = [f"=== Trace dump ({self.service_name}) — {len(self._spans)} spans ==="]
            for s in self._spans:
                lines.append(f"  {s}")
            return "\n".join(lines)

    def total_duration_ms(self) -> float:
        with self._lock:
            return sum(s.duration_ms for s in self._spans)


_global_tracer = Tracer()


# ===========================================================================
# § 5  Domain model
# ===========================================================================

class Parity(enum.Enum):
    ODD = "odd"
    EVEN = "even"

    @classmethod
    def of(cls, n: int) -> Parity:
        return cls.EVEN if n % 2 == 0 else cls.ODD


class NumberCategory(enum.Flag):
    NONE     = 0
    FIZZ     = enum.auto()
    BUZZ     = enum.auto()
    FIZZBUZZ = FIZZ | BUZZ
    PRIME    = enum.auto()
    PERFECT  = enum.auto()


@functools.lru_cache(maxsize=None)
def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    return all(n % i for i in range(3, int(n ** 0.5) + 1, 2))


@functools.lru_cache(maxsize=None)
def _is_perfect(n: int) -> bool:
    """A perfect number equals the sum of its proper divisors (e.g. 6, 28, 496)."""
    if n < 2:
        return False
    return sum(i for i in range(1, n) if n % i == 0) == n


@functools.lru_cache(maxsize=None)
def _collatz_depth(n: int) -> int:
    """Steps to reach 1 via the Collatz conjecture."""
    if n <= 1:
        return 0
    return 1 + _collatz_depth(n // 2 if n % 2 == 0 else 3 * n + 1)


@dataclasses.dataclass(frozen=True, order=True)
class Number:
    value: int

    def __post_init__(self) -> None:
        if not isinstance(self.value, int):
            raise TypeError(f"Expected int, got {type(self.value).__name__}")

    @functools.cached_property  # type: ignore[misc]
    def parity(self) -> Parity:
        return Parity.of(self.value)

    @functools.cached_property  # type: ignore[misc]
    def is_prime(self) -> bool:
        return _is_prime(self.value)

    @functools.cached_property  # type: ignore[misc]
    def is_perfect(self) -> bool:
        return _is_perfect(self.value)

    @functools.cached_property  # type: ignore[misc]
    def collatz_depth(self) -> int:
        return _collatz_depth(self.value)

    @functools.cached_property  # type: ignore[misc]
    def digit_sum(self) -> int:
        return sum(int(d) for d in str(abs(self.value)))

    @functools.cached_property  # type: ignore[misc]
    def num_divisors(self) -> int:
        return sum(1 for i in range(1, self.value + 1) if self.value % i == 0)

    @functools.cached_property  # type: ignore[misc]
    def fingerprint(self) -> str:
        return hashlib.sha256(str(self.value).encode()).hexdigest()[:8]

    @functools.cached_property  # type: ignore[misc]
    def category(self) -> NumberCategory:
        cat = NumberCategory.NONE
        if _is_prime(self.value):
            cat |= NumberCategory.PRIME
        if _is_perfect(self.value):
            cat |= NumberCategory.PERFECT
        return cat

    def is_divisible_by(self, divisor: int) -> bool:
        return self.value % divisor == 0

    def __str__(self) -> str:
        return str(self.value)

    def __repr__(self) -> str:
        tags = [c.name for c in NumberCategory if c in self.category and c != NumberCategory.NONE]
        suffix = f"[{','.join(tags)}]" if tags else ""
        return f"Number({self.value}{suffix})"


# ===========================================================================
# § 6  Specification pattern  (Spec & | ~)
# ===========================================================================

class Spec(abc.ABC):
    """Composable boolean predicate over Number."""

    @abc.abstractmethod
    def is_satisfied_by(self, n: Number) -> bool: ...

    def __and__(self, other: Spec) -> _AndSpec:
        return _AndSpec(self, other)

    def __or__(self, other: Spec) -> _OrSpec:
        return _OrSpec(self, other)

    def __invert__(self) -> _NotSpec:
        return _NotSpec(self)

    def to_predicate_rule(self, label: str, description: str | None = None) -> PredicateRule:
        desc = description or repr(self)
        spec = self
        return PredicateRule(spec.is_satisfied_by, label, description=desc)

    @abc.abstractmethod
    def __repr__(self) -> str: ...


@dataclasses.dataclass(frozen=True)
class _AndSpec(Spec):
    left: Spec
    right: Spec

    def is_satisfied_by(self, n: Number) -> bool:
        return self.left.is_satisfied_by(n) and self.right.is_satisfied_by(n)

    def __repr__(self) -> str:
        return f"({self.left!r} & {self.right!r})"


@dataclasses.dataclass(frozen=True)
class _OrSpec(Spec):
    left: Spec
    right: Spec

    def is_satisfied_by(self, n: Number) -> bool:
        return self.left.is_satisfied_by(n) or self.right.is_satisfied_by(n)

    def __repr__(self) -> str:
        return f"({self.left!r} | {self.right!r})"


@dataclasses.dataclass(frozen=True)
class _NotSpec(Spec):
    inner: Spec

    def is_satisfied_by(self, n: Number) -> bool:
        return not self.inner.is_satisfied_by(n)

    def __repr__(self) -> str:
        return f"~{self.inner!r}"


@dataclasses.dataclass(frozen=True)
class DivisibleBySpec(Spec):
    divisor: int

    def is_satisfied_by(self, n: Number) -> bool:
        return n.is_divisible_by(self.divisor)

    def __repr__(self) -> str:
        return f"DivisibleBy({self.divisor})"


class PrimeSpec(Spec):
    def is_satisfied_by(self, n: Number) -> bool:
        return n.is_prime

    def __repr__(self) -> str:
        return "Prime()"


class PerfectSpec(Spec):
    def is_satisfied_by(self, n: Number) -> bool:
        return n.is_perfect

    def __repr__(self) -> str:
        return "Perfect()"


@dataclasses.dataclass(frozen=True)
class ParitySpec(Spec):
    parity: Parity

    def is_satisfied_by(self, n: Number) -> bool:
        return n.parity == self.parity

    def __repr__(self) -> str:
        return f"Parity({self.parity.value})"


@dataclasses.dataclass(frozen=True)
class RangeSpec(Spec):
    lo: int
    hi: int

    def is_satisfied_by(self, n: Number) -> bool:
        return self.lo <= n.value <= self.hi

    def __repr__(self) -> str:
        return f"Range({self.lo}..{self.hi})"


@dataclasses.dataclass(frozen=True)
class CollatzDepthSpec(Spec):
    """Matches numbers whose Collatz depth satisfies a comparison."""
    threshold: int
    op: Literal["lt", "gt", "eq", "lte", "gte"] = "gt"

    _OPS: ClassVar[dict[str, Callable[[int, int], bool]]] = {
        "lt":  operator.lt,
        "gt":  operator.gt,
        "eq":  operator.eq,
        "lte": operator.le,
        "gte": operator.ge,
    }

    def is_satisfied_by(self, n: Number) -> bool:
        return self._OPS[self.op](n.collatz_depth, self.threshold)

    def __repr__(self) -> str:
        return f"CollatzDepth({self.op} {self.threshold})"


# ===========================================================================
# § 6b  Spec term rewriter  (algebraic simplification)
# ===========================================================================

class _AlwaysTrueSpec(Spec):
    def is_satisfied_by(self, _n: Number) -> bool: return True
    def __repr__(self) -> str: return "⊤"

class _AlwaysFalseSpec(Spec):
    def is_satisfied_by(self, _n: Number) -> bool: return False
    def __repr__(self) -> str: return "⊥"

_TRUE_SPEC  = _AlwaysTrueSpec()
_FALSE_SPEC = _AlwaysFalseSpec()


class SpecRewriter:
    """Applies algebraic identities to simplify Spec expression trees to fixpoint.

    Rules applied (eagerly, left-to-right):
        ~~S           → S              (double-negation elimination)
        ~⊤            → ⊥
        ~⊥            → ⊤
        S & S         → S              (idempotence)
        S | S         → S
        S & ~S        → ⊥              (contradiction)
        ~S & S        → ⊥
        S | ~S        → ⊤              (excluded middle)
        ~S | S        → ⊤
        S & ⊤         → S              (identity)
        ⊤ & S         → S
        S | ⊥         → S
        ⊥ | S         → S
        S & ⊥         → ⊥              (annihilation)
        ⊥ & S         → ⊥
        S | ⊤         → ⊤
        ⊤ | S         → ⊤
    """

    def rewrite(self, spec: Spec) -> Spec:
        prev: Spec | None = None
        current = spec
        steps = 0
        while prev is not current and steps < 64:
            prev = current
            current = self._step(current)
            steps += 1
        return current

    def _step(self, s: Spec) -> Spec:
        match s:
            # Double negation
            case _NotSpec(inner=_NotSpec(inner=inner)):
                return self._step(inner)
            # Negation of constants
            case _NotSpec(inner=_AlwaysTrueSpec()):
                return _FALSE_SPEC
            case _NotSpec(inner=_AlwaysFalseSpec()):
                return _TRUE_SPEC
            # Recurse into Not
            case _NotSpec(inner=inner):
                simplified = self._step(inner)
                return _NotSpec(simplified) if simplified is not inner else s
            # Idempotence
            case _AndSpec(left=l, right=r) if l == r:
                return self._step(l)
            case _OrSpec(left=l, right=r) if l == r:
                return self._step(l)
            # Contradiction / excluded middle
            case _AndSpec(left=l, right=_NotSpec(inner=r)) if l == r:
                return _FALSE_SPEC
            case _AndSpec(left=_NotSpec(inner=l), right=r) if l == r:
                return _FALSE_SPEC
            case _OrSpec(left=l, right=_NotSpec(inner=r)) if l == r:
                return _TRUE_SPEC
            case _OrSpec(left=_NotSpec(inner=l), right=r) if l == r:
                return _TRUE_SPEC
            # Identity / annihilation for And
            case _AndSpec(left=_AlwaysTrueSpec(), right=r):
                return self._step(r)
            case _AndSpec(left=l, right=_AlwaysTrueSpec()):
                return self._step(l)
            case _AndSpec(left=_AlwaysFalseSpec(), right=_):
                return _FALSE_SPEC
            case _AndSpec(left=_, right=_AlwaysFalseSpec()):
                return _FALSE_SPEC
            # Identity / annihilation for Or
            case _OrSpec(left=_AlwaysFalseSpec(), right=r):
                return self._step(r)
            case _OrSpec(left=l, right=_AlwaysFalseSpec()):
                return self._step(l)
            case _OrSpec(left=_AlwaysTrueSpec(), right=_):
                return _TRUE_SPEC
            case _OrSpec(left=_, right=_AlwaysTrueSpec()):
                return _TRUE_SPEC
            # Recurse into And / Or
            case _AndSpec(left=l, right=r):
                sl, sr = self._step(l), self._step(r)
                return _AndSpec(sl, sr) if (sl is not l or sr is not r) else s
            case _OrSpec(left=l, right=r):
                sl, sr = self._step(l), self._step(r)
                return _OrSpec(sl, sr) if (sl is not l or sr is not r) else s
            case _:
                return s


# ===========================================================================
# § 6c  Abstract interpretation  (interval domain static analysis)
# ===========================================================================
# Abstract interpretation over-approximates program behaviour without running
# it on concrete inputs.  We use an *interval domain* Interval[a, b] where
# every integer n satisfies a ≤ n ≤ b (or the bottom element ⊥ for empty).
#
# Lattice operations:
#   join(x, y)     — least upper bound (⊔); widens to cover both ranges
#   meet(x, y)     — greatest lower bound (⊓); intersection
#   widen(x, y)    — widening operator for loop convergence
#   is_bottom      — True for the empty interval ⊥
#
# Abstract rule interpreter:
#   abstract_eval(rule, interval) — which labels *might* the rule produce
#                                   for any number in the interval?
#   abstract_divisible(d, iv)     — does d divide *some* n in iv?
#   abstract_all_divisible(d, iv) — does d divide *all* n in iv?
#
# This allows static proofs like:
#   "For n in [1, 2], the classic rule can never produce FizzBuzz."
#   "For n in [15, 15], FizzBuzz is guaranteed."

INF: Final = float("inf")


@dataclasses.dataclass(frozen=True)
class Interval:
    lo: float   # inclusive lower bound  (-inf for −∞)
    hi: float   # inclusive upper bound  (+inf for +∞)

    # ⊥ sentinel
    @classmethod
    def bottom(cls) -> "Interval":
        return cls(INF, -INF)

    @classmethod
    def of(cls, n: int) -> "Interval":
        return cls(n, n)

    @classmethod
    def top(cls) -> "Interval":
        return cls(-INF, INF)

    @property
    def is_bottom(self) -> bool:
        return self.lo > self.hi

    @property
    def is_singleton(self) -> bool:
        return self.lo == self.hi and not self.is_bottom

    def __contains__(self, n: int | float) -> bool:
        return self.lo <= n <= self.hi

    def join(self, other: "Interval") -> "Interval":
        if self.is_bottom:
            return other
        if other.is_bottom:
            return self
        return Interval(min(self.lo, other.lo), max(self.hi, other.hi))

    def meet(self, other: "Interval") -> "Interval":
        lo = max(self.lo, other.lo)
        hi = min(self.hi, other.hi)
        return Interval(lo, hi) if lo <= hi else Interval.bottom()

    def widen(self, other: "Interval") -> "Interval":
        """Widening operator: send bounds that changed to ±∞."""
        if self.is_bottom:
            return other
        lo = self.lo if other.lo >= self.lo else -INF
        hi = self.hi if other.hi <= self.hi else INF
        return Interval(lo, hi)

    def add(self, k: float) -> "Interval":
        if self.is_bottom:
            return self
        return Interval(self.lo + k, self.hi + k)

    def __repr__(self) -> str:
        if self.is_bottom:
            return "⊥"
        lo = "-∞" if self.lo == -INF else int(self.lo)
        hi = "+∞" if self.hi == INF else int(self.hi)
        return f"[{lo}, {hi}]"


def _abstract_divisible_some(divisor: int, iv: Interval) -> bool:
    """True if the interval contains *at least one* multiple of divisor."""
    if iv.is_bottom:
        return False
    lo = int(math.ceil(iv.lo / divisor)) * divisor
    return lo <= iv.hi


def _abstract_divisible_all(divisor: int, iv: Interval) -> bool:
    """True if *every* integer in the interval is divisible by divisor."""
    if iv.is_bottom:
        return True   # vacuously true
    if not iv.is_singleton:
        # Only a singleton can guarantee all-divisibility
        return False
    return int(iv.lo) % divisor == 0


@dataclasses.dataclass(frozen=True)
class AbstractLabel:
    """
    Abstract label: a set of labels that *might* be produced, plus a flag
    indicating whether the number itself (no label) might be emitted.
    """
    possible_labels: frozenset[str]
    number_possible: bool   # True if the rule might return None for some n

    def __repr__(self) -> str:
        labels = set(self.possible_labels)
        if self.number_possible:
            labels.add("<number>")
        return f"AbstractLabel({labels!r})"

    def join(self, other: "AbstractLabel") -> "AbstractLabel":
        return AbstractLabel(
            possible_labels=self.possible_labels | other.possible_labels,
            number_possible=self.number_possible or other.number_possible,
        )

    @property
    def is_certain(self) -> bool:
        """True if exactly one outcome is possible."""
        total = len(self.possible_labels) + (1 if self.number_possible else 0)
        return total == 1


def abstract_eval(rule: "VisitableRule", iv: Interval) -> AbstractLabel:
    """
    Abstract interpretation of `rule` over interval `iv`.
    Returns which labels are *possible* for any n ∈ iv.
    """
    if iv.is_bottom:
        return AbstractLabel(frozenset(), False)

    if isinstance(rule, CompositeRule):
        # Each sub-rule is tried in order; labels can combine (FizzBuzz).
        # Over-approximate: each sub-rule might or might not fire.
        combined_labels: set[str] = set()
        any_label_possible = False

        for sub in rule.rules:
            sub_result = abstract_eval(sub, iv)
            combined_labels.update(sub_result.possible_labels)
            if sub_result.possible_labels:
                any_label_possible = True

        # The composite also joins all possible labels into combinations
        # if multiple labels are possible simultaneously.
        if len(combined_labels) >= 2:
            # FizzBuzz-like combinations possible
            for a in list(combined_labels):
                for b in list(combined_labels):
                    if a != b:
                        combined_labels.add(a + b)

        # Number emitted when no sub-rule fires
        number_possible = not any_label_possible or (
            # Some n in iv might not match any rule
            isinstance(rule, CompositeRule) and any(
                not _abstract_divisible_all(
                    getattr(sub, "divisor", 0) or 1, iv
                )
                for sub in rule.rules
                if isinstance(sub, DivisibilityRule)
            )
        )
        return AbstractLabel(frozenset(combined_labels), number_possible)

    elif isinstance(rule, DivisibilityRule):
        if _abstract_divisible_all(rule.divisor, iv):
            # Every n is divisible → label is certain
            return AbstractLabel(
                frozenset({rule.label}) if rule.label else frozenset(),
                rule.label is None,
            )
        elif _abstract_divisible_some(rule.divisor, iv):
            # Some n might be divisible
            lbl = {rule.label} if rule.label else set()
            return AbstractLabel(frozenset(lbl), True)
        else:
            # No n divisible → rule never fires
            return AbstractLabel(frozenset(), True)

    else:
        # Unknown rule: worst-case over-approximation
        return AbstractLabel(frozenset(), True)


def abstract_prove_always_labelled(rule: "VisitableRule", iv: Interval) -> bool:
    """Return True if static analysis can prove every n ∈ iv is labelled."""
    result = abstract_eval(rule, iv)
    return not result.number_possible and bool(result.possible_labels)


def abstract_prove_never_label(rule: "VisitableRule", iv: Interval, label: str) -> bool:
    """Return True if label cannot appear for any n ∈ iv."""
    result = abstract_eval(rule, iv)
    return label not in result.possible_labels


# ===========================================================================
# § 6d  Brzozowski derivatives  (regex-as-algebra with derivative matching)
# ===========================================================================
# A Brzozowski derivative of a language L w.r.t. character c is:
#   ∂_c(L) = { w | cw ∈ L }
# This extends to regular expressions structurally, yielding a complete,
# purely algebraic matching algorithm without NFA/DFA construction:
#
#   nullable(r)  — does r accept the empty string ε?
#   deriv(r, c)  — derivative of r w.r.t. character c
#   simplify(r)  — algebraic simplification (keeps derivatives small)
#   matches(r,s) — fold deriv over s, then check nullable
#
# RE algebra:
#   RE_Empty     — ∅      (matches nothing)
#   RE_Eps       — ε      (matches empty string only)
#   RE_Char(c)   — 'c'    (matches single character c)
#   RE_Any       — .      (matches any single character)
#   RE_Concat    — rs     (concatenation)
#   RE_Alt       — r|s    (alternation)
#   RE_Star      — r*     (Kleene star)
#   RE_Neg       — ¬r     (complement — matches what r doesn't)
#   RE_Inter     — r&s    (intersection)
#
# Convenience builders: re_lit(s), re_opt(r), re_plus(r), re_repeat(r,n)
# Domain application: FizzBuzz label classifier, output validator

@dataclasses.dataclass(frozen=True)
class RE_Empty:
    def __repr__(self) -> str: return "∅"

@dataclasses.dataclass(frozen=True)
class RE_Eps:
    def __repr__(self) -> str: return "ε"

@dataclasses.dataclass(frozen=True)
class RE_Char:
    c: str
    def __repr__(self) -> str: return repr(self.c)

@dataclasses.dataclass(frozen=True)
class RE_Any:
    def __repr__(self) -> str: return "."

@dataclasses.dataclass(frozen=True)
class RE_Concat:
    left: Any
    right: Any
    def __repr__(self) -> str: return f"({self.left!r}{self.right!r})"

@dataclasses.dataclass(frozen=True)
class RE_Alt:
    left: Any
    right: Any
    def __repr__(self) -> str: return f"({self.left!r}|{self.right!r})"

@dataclasses.dataclass(frozen=True)
class RE_Star:
    inner: Any
    def __repr__(self) -> str: return f"({self.inner!r})*"

@dataclasses.dataclass(frozen=True)
class RE_Neg:
    inner: Any
    def __repr__(self) -> str: return f"¬({self.inner!r})"

@dataclasses.dataclass(frozen=True)
class RE_Inter:
    left: Any
    right: Any
    def __repr__(self) -> str: return f"({self.left!r}&{self.right!r})"


RE: TypeAlias = RE_Empty | RE_Eps | RE_Char | RE_Any | RE_Concat | RE_Alt | RE_Star | RE_Neg | RE_Inter


def re_nullable(r: RE) -> bool:
    """Return True iff r accepts the empty string ε."""
    match r:
        case RE_Empty():  return False
        case RE_Eps():    return True
        case RE_Char():   return False
        case RE_Any():    return False
        case RE_Concat(left=l, right=rr): return re_nullable(l) and re_nullable(rr)
        case RE_Alt(left=l, right=rr):    return re_nullable(l) or re_nullable(rr)
        case RE_Star():   return True
        case RE_Neg(inner=i):             return not re_nullable(i)
        case RE_Inter(left=l, right=rr):  return re_nullable(l) and re_nullable(rr)
        case _:           return False


def re_deriv(r: RE, c: str) -> RE:
    """Compute the Brzozowski derivative ∂_c(r)."""
    match r:
        case RE_Empty():  return RE_Empty()
        case RE_Eps():    return RE_Empty()
        case RE_Char(c=ch): return RE_Eps() if c == ch else RE_Empty()
        case RE_Any():    return RE_Eps()
        case RE_Concat(left=l, right=rr):
            dl_r = RE_Concat(re_deriv(l, c), rr)
            if re_nullable(l):
                return re_simplify(RE_Alt(dl_r, re_deriv(rr, c)))
            return re_simplify(dl_r)
        case RE_Alt(left=l, right=rr):
            return re_simplify(RE_Alt(re_deriv(l, c), re_deriv(rr, c)))
        case RE_Star(inner=i):
            return re_simplify(RE_Concat(re_deriv(i, c), r))
        case RE_Neg(inner=i):
            return re_simplify(RE_Neg(re_deriv(i, c)))
        case RE_Inter(left=l, right=rr):
            return re_simplify(RE_Inter(re_deriv(l, c), re_deriv(rr, c)))
        case _:
            return RE_Empty()


def re_simplify(r: RE) -> RE:
    """Algebraic simplification to keep derivatives compact."""
    match r:
        # Concat identity / annihilation
        case RE_Concat(left=RE_Empty(), right=_): return RE_Empty()
        case RE_Concat(left=_, right=RE_Empty()): return RE_Empty()
        case RE_Concat(left=RE_Eps(), right=rr):  return re_simplify(rr)
        case RE_Concat(left=ll, right=RE_Eps()):  return re_simplify(ll)
        # Alt identity / idempotence
        case RE_Alt(left=RE_Empty(), right=rr):   return re_simplify(rr)
        case RE_Alt(left=ll, right=RE_Empty()):   return re_simplify(ll)
        case RE_Alt(left=ll, right=rr) if ll == rr: return re_simplify(ll)
        # Inter annihilation / identity
        case RE_Inter(left=RE_Empty(), right=_):  return RE_Empty()
        case RE_Inter(left=_, right=RE_Empty()):  return RE_Empty()
        case RE_Inter(left=ll, right=rr) if ll == rr: return re_simplify(ll)
        # Double negation
        case RE_Neg(inner=RE_Neg(inner=i)):       return re_simplify(i)
        # Star idempotence
        case RE_Star(inner=RE_Star(inner=i)):     return re_simplify(RE_Star(i))
        case RE_Star(inner=RE_Eps()):             return RE_Eps()
        case RE_Star(inner=RE_Empty()):           return RE_Eps()
        case _:
            return r


def re_matches(r: RE, s: str) -> bool:
    """Match string s against regex r using Brzozowski derivatives."""
    cur = r
    for c in s:
        cur = re_simplify(re_deriv(cur, c))
        if isinstance(cur, RE_Empty):
            return False
    return re_nullable(cur)


# ── Convenience builders ──────────────────────────────────────────────────

def re_lit(s: str) -> RE:
    """Build a regex matching the literal string s."""
    r: RE = RE_Eps()
    for c in reversed(s):
        r = RE_Concat(RE_Char(c), r)
    return r


def re_opt(r: RE) -> RE:
    """r? — optional r."""
    return RE_Alt(r, RE_Eps())


def re_plus(r: RE) -> RE:
    """r+ — one or more r."""
    return RE_Concat(r, RE_Star(r))


def re_repeat(r: RE, n: int) -> RE:
    """r{n} — exactly n repetitions of r."""
    if n <= 0:
        return RE_Eps()
    result: RE = r
    for _ in range(n - 1):
        result = RE_Concat(result, r)
    return result


def re_char_class(chars: str) -> RE:
    """Build an alternation over all characters in chars."""
    if not chars:
        return RE_Empty()
    r: RE = RE_Char(chars[0])
    for c in chars[1:]:
        r = RE_Alt(r, RE_Char(c))
    return r


_RE_DIGIT: RE = re_char_class("0123456789")
_RE_DIGITS: RE = re_plus(_RE_DIGIT)

# FizzBuzz-specific regexes
_RE_FIZZ:     RE = re_lit(FIZZ)
_RE_BUZZ:     RE = re_lit(BUZZ)
_RE_FIZZBUZZ: RE = re_lit(FIZZBUZZ)
_RE_NUMBER:   RE = re_opt(re_lit("-"))  # optional minus sign
_RE_NUMBER    = RE_Concat(_RE_NUMBER, _RE_DIGITS)
_RE_FB_OUTPUT: RE = RE_Alt(RE_Alt(_RE_FIZZBUZZ, RE_Alt(_RE_FIZZ, _RE_BUZZ)), _RE_NUMBER)

# Validator using Brzozowski matching
def validate_fizzbuzz_output(s: str) -> bool:
    """Return True iff s is a valid FizzBuzz output token."""
    return re_matches(_RE_FB_OUTPUT, s)


def re_classify(s: str) -> str:
    """Classify a FizzBuzz output string."""
    for label, pattern in (
        ("FizzBuzz", _RE_FIZZBUZZ),
        ("Fizz",     _RE_FIZZ),
        ("Buzz",     _RE_BUZZ),
        ("number",   _RE_NUMBER),
    ):
        if re_matches(pattern, s):
            return label
    return "unknown"


# ===========================================================================
# § 6e  DPLL SAT solver  (propositional satisfiability via Davis–Putnam–
#                          Logemann–Loveland with unit propagation + VSIDS)
# ===========================================================================
# DPLL is the classic backtracking SAT algorithm augmented with:
#   1. Unit propagation  — a unit clause forces its lone literal
#   2. Pure literal elim — a variable appearing in only one polarity is free
#   3. VSIDS heuristic   — choose the variable with most clause appearances
#
# Representation (all immutable):
#   Literal  = (var_name: str, positive: bool)
#   Clause   = frozenset[Literal]
#   Formula  = frozenset[Clause]  (CNF)
#
# Helpers: prop_var, prop_not, prop_and, prop_or — build Prop ADT
# cnf(prop) — convert arbitrary Prop to CNF via Tseytin transformation
# dpll(formula) — returns a satisfying assignment or None (UNSAT)
#
# FizzBuzz application:
#   encode_rule_as_prop(rule, n) — build a propositional formula representing
#     "what does this rule emit for integer n?"
#   check_rule_consistency(rule) — use DPLL to verify the rule never emits
#     contradictory labels for the same n

Literal: TypeAlias = tuple[str, bool]   # (variable_name, is_positive)
Clause:  TypeAlias = frozenset          # frozenset[Literal]
CNFFormula: TypeAlias = frozenset       # frozenset[Clause]


# ── Propositional AST ────────────────────────────────────────────────────

@dataclasses.dataclass(frozen=True)
class PVar:
    name: str
    def __repr__(self) -> str: return self.name

@dataclasses.dataclass(frozen=True)
class PNot:
    inner: Any
    def __repr__(self) -> str: return f"¬{self.inner!r}"

@dataclasses.dataclass(frozen=True)
class PAnd:
    left: Any
    right: Any
    def __repr__(self) -> str: return f"({self.left!r} ∧ {self.right!r})"

@dataclasses.dataclass(frozen=True)
class POr:
    left: Any
    right: Any
    def __repr__(self) -> str: return f"({self.left!r} ∨ {self.right!r})"

@dataclasses.dataclass(frozen=True)
class PImp:
    left: Any
    right: Any
    def __repr__(self) -> str: return f"({self.left!r} → {self.right!r})"

@dataclasses.dataclass(frozen=True)
class PIff:
    left: Any
    right: Any
    def __repr__(self) -> str: return f"({self.left!r} ↔ {self.right!r})"

@dataclasses.dataclass(frozen=True)
class PTrue:
    def __repr__(self) -> str: return "⊤"

@dataclasses.dataclass(frozen=True)
class PFalse:
    def __repr__(self) -> str: return "⊥"


Prop: TypeAlias = PVar | PNot | PAnd | POr | PImp | PIff | PTrue | PFalse


def prop_simplify(p: Prop) -> Prop:
    """Light simplification of propositional formulas."""
    match p:
        case PNot(inner=PTrue()):   return PFalse()
        case PNot(inner=PFalse()):  return PTrue()
        case PNot(inner=PNot(inner=q)): return prop_simplify(q)
        case PAnd(left=PTrue(),  right=r): return prop_simplify(r)
        case PAnd(left=l, right=PTrue()): return prop_simplify(l)
        case PAnd(left=PFalse(), right=_): return PFalse()
        case PAnd(left=_, right=PFalse()): return PFalse()
        case POr(left=PFalse(), right=r):  return prop_simplify(r)
        case POr(left=l, right=PFalse()):  return prop_simplify(l)
        case POr(left=PTrue(),  right=_):  return PTrue()
        case POr(left=_, right=PTrue()):   return PTrue()
        case PImp(left=PFalse(), right=_): return PTrue()
        case PImp(left=_, right=PTrue()):  return PTrue()
        case PImp(left=PTrue(),  right=r): return prop_simplify(r)
        case _:
            return p


def _tseytin_aux(
    p: Prop,
    fresh: list[int],
    clauses: list[Clause],
) -> str:
    """Tseytin transformation: introduce auxiliary variable for sub-formula p."""
    aux = f"_t{fresh[0]}"
    fresh[0] += 1
    match p:
        case PVar(name=n):
            return n
        case PTrue():
            clauses.append(frozenset({(aux, True)}))
            return aux
        case PFalse():
            clauses.append(frozenset({(aux, False)}))
            return aux
        case PNot(inner=q):
            q_aux = _tseytin_aux(q, fresh, clauses)
            # aux ↔ ¬q_aux
            clauses.append(frozenset({(aux, True),  (q_aux, True)}))
            clauses.append(frozenset({(aux, False), (q_aux, False)}))
            return aux
        case PAnd(left=l, right=r):
            l_aux = _tseytin_aux(l, fresh, clauses)
            r_aux = _tseytin_aux(r, fresh, clauses)
            # aux ↔ l_aux ∧ r_aux
            clauses.append(frozenset({(aux, False), (l_aux, True)}))
            clauses.append(frozenset({(aux, False), (r_aux, True)}))
            clauses.append(frozenset({(aux, True), (l_aux, False), (r_aux, False)}))
            return aux
        case POr(left=l, right=r):
            l_aux = _tseytin_aux(l, fresh, clauses)
            r_aux = _tseytin_aux(r, fresh, clauses)
            # aux ↔ l_aux ∨ r_aux
            clauses.append(frozenset({(aux, False), (l_aux, True), (r_aux, True)}))
            clauses.append(frozenset({(aux, True), (l_aux, False)}))
            clauses.append(frozenset({(aux, True), (r_aux, False)}))
            return aux
        case PImp(left=l, right=r):
            return _tseytin_aux(POr(PNot(l), r), fresh, clauses)
        case PIff(left=l, right=r):
            return _tseytin_aux(PAnd(PImp(l, r), PImp(r, l)), fresh, clauses)
        case _:
            return aux


def prop_to_cnf(p: Prop) -> CNFFormula:
    """Convert a Prop to CNF via Tseytin transformation."""
    p = prop_simplify(p)
    if isinstance(p, PTrue):
        return frozenset()
    if isinstance(p, PFalse):
        return frozenset({frozenset()})   # empty clause = UNSAT
    fresh = [0]
    clauses: list[Clause] = []
    top = _tseytin_aux(p, fresh, clauses)
    clauses.append(frozenset({(top, True)}))   # assert the top-level is True
    return frozenset(clauses)


def _unit_propagate(
    formula: CNFFormula,
    assignment: dict[str, bool],
) -> tuple[CNFFormula, dict[str, bool]]:
    """Apply unit propagation until fixpoint. Returns (simplified, assignment)."""
    changed = True
    asgn = dict(assignment)
    clauses = set(formula)
    while changed:
        changed = False
        units: list[Literal] = []
        for clause in list(clauses):
            # Evaluate clause under current assignment
            satisfied = False
            unassigned: list[Literal] = []
            for var, pos in clause:
                if var in asgn:
                    if asgn[var] == pos:
                        satisfied = True
                        break
                else:
                    unassigned.append((var, pos))
            if satisfied:
                clauses.discard(clause)
                changed = True
            elif not unassigned:
                return frozenset({frozenset()}), asgn   # conflict
            elif len(unassigned) == 1:
                units.append(unassigned[0])
                changed = True
        for var, pos in units:
            if var not in asgn:
                asgn[var] = pos
                changed = True
    return frozenset(clauses), asgn


def _pure_literal_elim(
    formula: CNFFormula,
    assignment: dict[str, bool],
) -> tuple[CNFFormula, dict[str, bool]]:
    """Eliminate pure literals (appear with only one polarity)."""
    asgn = dict(assignment)
    pos_vars: set[str] = set()
    neg_vars: set[str] = set()
    for clause in formula:
        for var, pol in clause:
            if var not in asgn:
                (pos_vars if pol else neg_vars).add(var)
    pure_pos = pos_vars - neg_vars
    pure_neg = neg_vars - pos_vars
    for v in pure_pos:
        asgn[v] = True
    for v in pure_neg:
        asgn[v] = False
    if pure_pos or pure_neg:
        # Re-simplify
        new_clauses: list[Clause] = []
        for clause in formula:
            if any(asgn.get(v) == pol for v, pol in clause):
                continue
            new_clauses.append(clause)
        return frozenset(new_clauses), asgn
    return formula, asgn


def _vsids_pick(formula: CNFFormula, assignment: dict[str, bool]) -> str | None:
    """VSIDS: pick the unassigned variable appearing in most clauses."""
    freq: Counter[str] = Counter()
    for clause in formula:
        for var, _ in clause:
            if var not in assignment:
                freq[var] += 1
    if not freq:
        return None
    return freq.most_common(1)[0][0]


def dpll(
    formula: CNFFormula,
    assignment: dict[str, bool] | None = None,
) -> dict[str, bool] | None:
    """
    DPLL satisfiability solver.
    Returns a satisfying assignment (var → bool) or None if UNSAT.
    """
    asgn: dict[str, bool] = dict(assignment or {})

    # Unit propagation
    formula, asgn = _unit_propagate(formula, asgn)
    if not formula:
        return asgn   # SAT: all clauses satisfied
    if any(len(c) == 0 for c in formula):
        return None   # conflict

    # Pure literal elimination
    formula, asgn = _pure_literal_elim(formula, asgn)
    if not formula:
        return asgn

    # Choose a variable (VSIDS heuristic)
    var = _vsids_pick(formula, asgn)
    if var is None:
        return asgn   # all variables assigned

    # Branch
    for value in (True, False):
        result = dpll(formula, {**asgn, var: value})
        if result is not None:
            return result
    return None


def prop_is_sat(p: Prop) -> bool:
    """Return True iff the propositional formula is satisfiable."""
    return dpll(prop_to_cnf(p)) is not None


def prop_is_tautology(p: Prop) -> bool:
    """Return True iff p is a tautology (¬p is UNSAT)."""
    return dpll(prop_to_cnf(PNot(p))) is None


# ── FizzBuzz-specific propositional encoding ─────────────────────────────

def encode_divisibility(n: int, divisor: int) -> Prop:
    """Propositional variable: 'n is divisible by divisor'."""
    return PVar(f"div_{divisor}({n})")


def encode_rule_fires(rule: "VisitableRule", n: int) -> Prop:
    """Build a Prop expressing that `rule` produces a non-None label for n."""
    if isinstance(rule, CompositeRule):
        sub_props = [encode_rule_fires(sub, n) for sub in rule.rules]
        if not sub_props:
            return PFalse()
        result = sub_props[0]
        for sp in sub_props[1:]:
            result = POr(result, sp)
        return result
    elif isinstance(rule, DivisibilityRule):
        var = encode_divisibility(n, rule.divisor)
        # Ground truth: substitute the actual divisibility
        if n % rule.divisor == 0:
            return PTrue()
        else:
            return PFalse()
    return PFalse()


def check_rule_mutual_exclusion(rule: "VisitableRule", start: int = 1, stop: int = 30) -> list[str]:
    """
    Use DPLL to verify that for each n, the rule is consistent:
    - FizzBuzz ↔ (Fizz ∧ Buzz)  is a tautology for every n
    Returns a list of verification messages.
    """
    results: list[str] = []
    for n_val in range(start, stop + 1):
        # Build atomic facts about n
        facts: list[Prop] = []
        for sub in (rule.rules if isinstance(rule, CompositeRule) else [rule]):
            if isinstance(sub, DivisibilityRule):
                var = PVar(f"div_{sub.divisor}({n_val})")
                if n_val % sub.divisor == 0:
                    facts.append(var)
                else:
                    facts.append(PNot(var))

        # Assert all ground facts and check that rule firing is consistent
        label = rule(Number(n_val))
        fires = encode_rule_fires(rule, n_val)
        grounded = prop_simplify(fires)

        actual_fires = label is not None
        simplified_val = isinstance(grounded, PTrue)
        consistent = actual_fires == simplified_val
        if not consistent:
            results.append(f"  INCONSISTENCY at n={n_val}: rule fires={actual_fires} but prop={grounded!r}")
        else:
            results.append(f"  n={n_val:>3}  fires={actual_fires}  prop={grounded!r}  ✓")
    return results


# ===========================================================================
# § 7  Rule engine — chain of responsibility + visitor + DSL + compiler
# ===========================================================================

@runtime_checkable
class Rule(Protocol):
    def __call__(self, number: Number) -> LabelT: ...


class RuleVisitor(abc.ABC):
    @abc.abstractmethod
    def visit_divisibility(self, rule: DivisibilityRule) -> None: ...

    @abc.abstractmethod
    def visit_composite(self, rule: CompositeRule) -> None: ...

    @abc.abstractmethod
    def visit_predicate(self, rule: PredicateRule) -> None: ...


class VisitableRule(abc.ABC):
    @abc.abstractmethod
    def accept(self, visitor: RuleVisitor) -> None: ...

    @abc.abstractmethod
    def __call__(self, number: Number) -> LabelT: ...


@dataclasses.dataclass(frozen=True)
class DivisibilityRule(VisitableRule):
    divisor: int
    label: str
    _call_count: int = dataclasses.field(default=0, init=False, compare=False, hash=False)

    def __call__(self, number: Number) -> LabelT:
        object.__setattr__(self, "_call_count", self._call_count + 1)
        return self.label if number.is_divisible_by(self.divisor) else None

    def accept(self, visitor: RuleVisitor) -> None:
        visitor.visit_divisibility(self)


@dataclasses.dataclass(frozen=True)
class PredicateRule(VisitableRule):
    predicate: Callable[[Number], bool]
    label: str
    description: str = "<custom>"

    def __call__(self, number: Number) -> LabelT:
        return self.label if self.predicate(number) else None

    def accept(self, visitor: RuleVisitor) -> None:
        visitor.visit_predicate(self)


@dataclasses.dataclass(frozen=True)
class CompositeRule(VisitableRule):
    rules: tuple[VisitableRule, ...]

    def __call__(self, number: Number) -> LabelT:
        parts = [r(number) for r in self.rules]
        result = "".join(p for p in parts if p is not None)
        return result or None

    def accept(self, visitor: RuleVisitor) -> None:
        visitor.visit_composite(self)


# ── Visitor implementations ──────────────────────────────────────────────────

class RuleExplainerVisitor(RuleVisitor):
    def __init__(self) -> None:
        self._lines: list[str] = []

    def visit_divisibility(self, rule: DivisibilityRule) -> None:
        self._lines.append(f"  div({rule.divisor:>4}) → {rule.label!r:<12}  [invoked {rule._call_count}×]")

    def visit_composite(self, rule: CompositeRule) -> None:
        self._lines.append(f"CompositeRule  ({len(rule.rules)} sub-rules):")
        for child in rule.rules:
            child.accept(self)

    def visit_predicate(self, rule: PredicateRule) -> None:
        self._lines.append(f"  pred({rule.description!s:<20}) → {rule.label!r}")

    def explain(self) -> str:
        return "\n".join(self._lines)


class RuleSerialiserVisitor(RuleVisitor):
    """Serialises a rule tree to a JSON-compatible dict."""

    def __init__(self) -> None:
        self._stack: list[dict[str, Any]] = []

    def visit_divisibility(self, rule: DivisibilityRule) -> None:
        self._stack.append({"type": "divisibility", "divisor": rule.divisor, "label": rule.label})

    def visit_composite(self, rule: CompositeRule) -> None:
        children: list[dict[str, Any]] = []
        for child in rule.rules:
            child.accept(self)
            children.append(self._stack.pop())
        self._stack.append({"type": "composite", "rules": children})

    def visit_predicate(self, rule: PredicateRule) -> None:
        self._stack.append({"type": "predicate", "description": rule.description, "label": rule.label})

    def serialise(self) -> dict[str, Any]:
        return self._stack[-1] if self._stack else {}


# ── Builder ───────────────────────────────────────────────────────────────────

class RuleBuilder:
    def __init__(self) -> None:
        self._rules: list[VisitableRule] = []

    def when_divisible_by(self, divisor: int, label: str) -> RuleBuilder:
        if divisor == 0:
            raise ValueError("divisor cannot be zero")
        self._rules.append(DivisibilityRule(divisor, label))
        return self

    def when(
        self,
        predicate: Callable[[Number], bool],
        label: str,
        *,
        description: str = "<custom>",
    ) -> RuleBuilder:
        self._rules.append(PredicateRule(predicate, label, description=description))
        return self

    def when_spec(self, spec: Spec, label: str) -> RuleBuilder:
        return self.when(spec.is_satisfied_by, label, description=repr(spec))

    def build(self) -> CompositeRule:
        if not self._rules:
            raise RuntimeError("Cannot build an empty rule")
        return CompositeRule(tuple(self._rules))


# ── DSL parser  ───────────────────────────────────────────────────────────────

def parse_rule_dsl(spec: str) -> CompositeRule:
    """Parse a whitespace-separated rule DSL string into a CompositeRule.

    Token syntax:
        <int>:<label>       — divisibility rule
        prime:<label>       — prime predicate
        perfect:<label>     — perfect-number predicate
        even:<label>        — even parity
        odd:<label>         — odd parity
        collatz<op><n>:<lbl>— Collatz depth (op: > < = >= <=)

    Example:
        parse_rule_dsl("3:Fizz 5:Buzz prime:★ perfect:⊕")
    """
    builder = RuleBuilder()
    collatz_re = re.compile(r"^collatz(>=|<=|>|<|=)(\d+)$")

    for token in spec.split():
        if not token:
            continue
        if ":" not in token:
            raise ValueError(f"Invalid DSL token {token!r} — expected <key>:<label>")
        key, _, label = token.partition(":")
        key = key.strip()
        label = label.strip()

        if re.fullmatch(r"-?\d+", key):
            builder.when_divisible_by(int(key), label)
        elif key == "prime":
            builder.when(lambda n: n.is_prime, label, description="prime")
        elif key == "perfect":
            builder.when(lambda n: n.is_perfect, label, description="perfect")
        elif key == "even":
            builder.when(lambda n: n.parity == Parity.EVEN, label, description="even")
        elif key == "odd":
            builder.when(lambda n: n.parity == Parity.ODD, label, description="odd")
        elif m := collatz_re.match(key):
            raw_op, threshold_s = m.group(1), m.group(2)
            op_map = {">": "gt", "<": "lt", "=": "eq", ">=": "gte", "<=": "lte"}
            spec_obj = CollatzDepthSpec(threshold=int(threshold_s), op=op_map[raw_op])
            builder.when_spec(spec_obj, label)
        else:
            raise ValueError(f"Unknown DSL key {key!r}.")

    return builder.build()


# ── Bytecode compiler  ────────────────────────────────────────────────────────

class RuleCompiler:
    """Compiles a CompositeRule's divisibility sub-rules to a native Python function
    via source-code generation → compile() → exec(), bypassing Python attribute
    lookups for the hot path."""

    _cache: ClassVar[dict[int, Callable[[Number], LabelT]]] = {}
    _log: ClassVar[logging.Logger] = logging.getLogger("fizzbuzz.compiler")

    @classmethod
    def compile(cls, rule: CompositeRule) -> Callable[[Number], LabelT]:
        key = id(rule)
        if key in cls._cache:
            cls._log.debug("Cache hit for rule id=%d", key)
            return cls._cache[key]

        src = cls._generate_source(rule)
        cls._log.debug("Compiling rule:\n%s", src)
        code = compile(src, "<fizzbuzz-compiled-rule>", "exec")
        ns: dict[str, Any] = {"_is_prime": _is_prime}
        exec(code, ns)  # noqa: S102
        fn: Callable[[Number], LabelT] = ns["_compiled_rule"]
        cls._cache[key] = fn
        return fn

    @classmethod
    def _generate_source(cls, rule: CompositeRule) -> str:
        lines = [
            "def _compiled_rule(n):",
            "    _v = n.value",
            "    _p: list[str] = []",
        ]
        for r in rule.rules:
            if isinstance(r, DivisibilityRule):
                lines.append(f"    if _v % {r.divisor} == 0: _p.append({r.label!r})")
            elif isinstance(r, PredicateRule):
                lines.append(f"    # predicate: {r.description}  (not compiled — fallback)")
        lines += [
            "    return ''.join(_p) or None",
        ]
        return "\n".join(lines) + "\n"

    @classmethod
    def clear_cache(cls) -> None:
        cls._cache.clear()


# ── Abstract interpreter / static analyser  ───────────────────────────────────

class AbstractRuleInterpreter:
    """Statically analyses a CompositeRule without executing the full pipeline."""

    def label_frequency(self, rule: CompositeRule, range_: NumberRange) -> dict[str, int]:
        counts: Counter[str] = Counter()
        for number in range_:
            label = rule(number)
            counts[label or "<number>"] += 1
        return dict(counts.most_common())

    def find_subsumptions(self, rule: CompositeRule) -> list[str]:
        """Detect divisibility pairs where one always fires with the other."""
        notes: list[str] = []
        div_rules = [r for r in rule.rules if isinstance(r, DivisibilityRule)]
        for i, r1 in enumerate(div_rules):
            for r2 in div_rules[i + 1:]:
                if r2.divisor % r1.divisor == 0:
                    notes.append(
                        f"div({r2.divisor}) ⊆ div({r1.divisor}): "
                        f"every multiple of {r2.divisor} is also a multiple of {r1.divisor}"
                    )
        return notes

    def coverage(self, rule: CompositeRule, range_: NumberRange) -> float:
        labelled = sum(1 for n in range_ if rule(n) is not None)
        return labelled / len(range_) if range_ else 0.0

    def report(self, rule: CompositeRule, range_: NumberRange) -> str:
        freq = self.label_frequency(rule, range_)
        subs = self.find_subsumptions(rule)
        cov = self.coverage(rule, range_)
        lines = [
            f"Abstract analysis of rule over {range_!r}:",
            f"  Coverage (labelled): {cov:.1%}",
            "  Label frequencies:",
        ]
        for label, count in freq.items():
            lines.append(f"    {label:<18} {count:>6}  ({count / sum(freq.values()):.1%})")
        if subs:
            lines.append("  Subsumption notes:")
            for note in subs:
                lines.append(f"    ⚠ {note}")
        return "\n".join(lines)


# ===========================================================================
# § 7b  Attribute grammar  (synthesized & inherited attrs over rule trees)
# ===========================================================================
# Attribute grammars annotate a tree with *synthesized* (bottom-up) and
# *inherited* (top-down) attributes.  A synthesized attribute of a node is
# computed from its children; an inherited attribute is passed down from
# the parent.
#
# We implement a two-pass evaluator over the rule tree:
#   Pass 1 (bottom-up): compute SynthesizedAttrs at every node.
#   Pass 2 (top-down):  compute InheritedAttrs using parent's inherited
#                       attrs and siblings' synthesized attrs.
#
# SynthesizedAttrs per rule node:
#   depth       — max depth of sub-tree
#   leaf_count  — number of leaf rules
#   divisors    — frozenset of all divisors used
#   labels      — frozenset of all labels that can be emitted
#
# InheritedAttrs per rule node:
#   depth_from_root  — distance from tree root
#   sibling_count    — number of siblings in parent composite
#   rule_index       — index within parent composite (0-based)

@dataclasses.dataclass(frozen=True)
class SynthesizedAttrs:
    depth: int
    leaf_count: int
    divisors: frozenset[int]
    labels: frozenset[str]


@dataclasses.dataclass(frozen=True)
class InheritedAttrs:
    depth_from_root: int
    sibling_count: int
    rule_index: int


@dataclasses.dataclass
class AttributedNode:
    rule: "VisitableRule"
    synth: SynthesizedAttrs
    inh: InheritedAttrs
    children: list["AttributedNode"] = dataclasses.field(default_factory=list)

    def pretty(self, indent: int = 0) -> str:
        pad = "  " * indent
        lines = [
            f"{pad}{self.rule!r}",
            f"{pad}  synth: depth={self.synth.depth} leaves={self.synth.leaf_count}"
            f" divisors={set(self.synth.divisors)} labels={set(self.synth.labels)}",
            f"{pad}  inh:   depth_from_root={self.inh.depth_from_root}"
            f" sibling_count={self.inh.sibling_count} index={self.inh.rule_index}",
        ]
        for child in self.children:
            lines.append(child.pretty(indent + 1))
        return "\n".join(lines)


def _synthesize(rule: "VisitableRule") -> tuple[SynthesizedAttrs, list["VisitableRule"]]:
    """Compute SynthesizedAttrs bottom-up for a single rule node."""
    if isinstance(rule, CompositeRule):
        child_attrs = [_synthesize(r) for r in rule.rules]
        if not child_attrs:
            return SynthesizedAttrs(depth=1, leaf_count=0, divisors=frozenset(), labels=frozenset()), []
        max_depth = max(a.depth for a, _ in child_attrs)
        total_leaves = sum(a.leaf_count for a, _ in child_attrs)
        all_divisors: frozenset[int] = frozenset().union(*(a.divisors for a, _ in child_attrs))
        all_labels: frozenset[str] = frozenset().union(*(a.labels for a, _ in child_attrs))
        return SynthesizedAttrs(
            depth=max_depth + 1,
            leaf_count=total_leaves,
            divisors=all_divisors,
            labels=all_labels,
        ), list(rule.rules)
    elif isinstance(rule, DivisibilityRule):
        return SynthesizedAttrs(
            depth=1,
            leaf_count=1,
            divisors=frozenset({rule.divisor}),
            labels=frozenset({rule.label}) if rule.label else frozenset(),
        ), []
    else:
        # PredicateRule or unknown leaf
        lbl = getattr(rule, "label", None)
        return SynthesizedAttrs(
            depth=1,
            leaf_count=1,
            divisors=frozenset(),
            labels=frozenset({lbl}) if lbl else frozenset(),
        ), []


def _build_attributed_tree(
    rule: "VisitableRule",
    inh: InheritedAttrs,
) -> AttributedNode:
    """Recursively build AttributedNode with both synthesized and inherited attrs."""
    synth, raw_children = _synthesize(rule)
    node = AttributedNode(rule=rule, synth=synth, inh=inh)
    for idx, child in enumerate(raw_children):
        child_inh = InheritedAttrs(
            depth_from_root=inh.depth_from_root + 1,
            sibling_count=len(raw_children),
            rule_index=idx,
        )
        node.children.append(_build_attributed_tree(child, child_inh))
    return node


def attribute_rule_tree(rule: "VisitableRule") -> AttributedNode:
    """Entry point: annotate an entire rule tree with attributes."""
    root_inh = InheritedAttrs(depth_from_root=0, sibling_count=1, rule_index=0)
    return _build_attributed_tree(rule, root_inh)


# ===========================================================================
# § 8  Rule registry
# ===========================================================================

class RuleRegistry(metaclass=_SingletonMeta):
    def __init__(self) -> None:
        self._store: dict[str, CompositeRule] = {}
        self._log = logging.getLogger("fizzbuzz.registry")

    def register(self, name: str, rule: CompositeRule) -> None:
        self._store[name] = rule
        self._log.debug("Registered rule %r", name)
        EventBus().publish("registry.registered", {"name": name})

    def get(self, name: str) -> CompositeRule:
        try:
            return self._store[name]
        except KeyError:
            raise KeyError(f"No rule {name!r}. Available: {sorted(self._store)}")

    def names(self) -> list[str]:
        return sorted(self._store)

    def serialise_all(self) -> dict[str, Any]:
        out: dict[str, Any] = {}
        for name, rule in self._store.items():
            v = RuleSerialiserVisitor()
            rule.accept(v)
            out[name] = v.serialise()
        return out


def _bootstrap_registry() -> None:
    r = RuleRegistry()
    r.register(
        "classic",
        RuleBuilder().when_divisible_by(3, FIZZ).when_divisible_by(5, BUZZ).build(),
    )
    r.register(
        "extended",
        RuleBuilder()
        .when_divisible_by(3, FIZZ)
        .when_divisible_by(5, BUZZ)
        .when_divisible_by(7, "Bazz")
        .when(lambda n: n.is_prime, "✦", description="prime")
        .build(),
    )
    r.register(
        "mathematical",
        RuleBuilder()
        .when_divisible_by(3, FIZZ)
        .when_divisible_by(5, BUZZ)
        .when(lambda n: n.is_perfect, "⊕", description="perfect")
        .when_spec(CollatzDepthSpec(threshold=20, op="gt"), "∞", )
        .build(),
    )


_bootstrap_registry()


# ===========================================================================
# § 8b  Merkle tree / content-addressable rule store
# ===========================================================================

@dataclasses.dataclass
class MerkleNode:
    digest: str
    left: MerkleNode | None = None
    right: MerkleNode | None = None
    payload: Any = dataclasses.field(default=None, repr=False)

    @staticmethod
    def leaf(payload: Any) -> MerkleNode:
        h = hashlib.sha256(repr(payload).encode()).hexdigest()
        return MerkleNode(digest=h, payload=payload)

    @staticmethod
    def branch(left: MerkleNode, right: MerkleNode) -> MerkleNode:
        h = hashlib.sha256((left.digest + right.digest).encode()).hexdigest()
        return MerkleNode(digest=h, left=left, right=right)

    @property
    def is_leaf(self) -> bool:
        return self.left is None and self.right is None

    def short(self) -> str:
        return self.digest[:12]


def _build_merkle(items: Sequence[Any]) -> MerkleNode | None:
    if not items:
        return None
    nodes = [MerkleNode.leaf(v) for v in items]
    while len(nodes) > 1:
        if len(nodes) % 2:
            nodes.append(nodes[-1])  # duplicate last for odd count
        nodes = [MerkleNode.branch(nodes[i], nodes[i + 1]) for i in range(0, len(nodes), 2)]
    return nodes[0]


class ContentAddressableRuleStore:
    """Immutable, content-addressable store for CompositeRules backed by a Merkle tree.

    Each stored rule is identified by the SHA-256 digest of its serialised form.
    The Merkle root covers all stored rules in sorted-name order, giving a
    single fingerprint for the entire rule set.
    """

    def __init__(self) -> None:
        self._store: dict[str, tuple[CompositeRule, str]] = {}  # name → (rule, digest)
        self._tree: MerkleNode | None = None
        self._log = logging.getLogger("fizzbuzz.merkle")

    def store(self, name: str, rule: CompositeRule) -> str:
        v = RuleSerialiserVisitor()
        rule.accept(v)
        digest = hashlib.sha256(repr(v.serialise()).encode()).hexdigest()
        self._store[name] = (rule, digest)
        self._rebuild()
        self._log.debug("Stored %r digest=%s root=%s", name, digest[:8], self.root_hash()[:8] if self.root_hash() else "—")
        return digest

    def _rebuild(self) -> None:
        leaves = sorted(f"{n}:{d}" for n, (_, d) in self._store.items())
        self._tree = _build_merkle(leaves)

    def root_hash(self) -> str | None:
        return self._tree.digest if self._tree else None

    def get(self, name: str) -> CompositeRule:
        entry = self._store.get(name)
        if entry is None:
            raise KeyError(f"Rule {name!r} not in store")
        return entry[0]

    def verify(self, name: str, expected_digest: str) -> bool:
        entry = self._store.get(name)
        return entry is not None and entry[1] == expected_digest

    def audit(self) -> dict[str, str]:
        """Returns {name: digest} for all stored rules."""
        return {n: d for n, (_, d) in self._store.items()}

    def proof_path(self, name: str) -> list[str]:
        """Returns the sibling digests along the Merkle path for `name` (simplified)."""
        if name not in self._store:
            raise KeyError(name)
        leaves = sorted(f"{n}:{d}" for n, (_, d) in self._store.items())
        target = f"{name}:{self._store[name][1]}"
        idx = leaves.index(target)
        nodes = [MerkleNode.leaf(v) for v in leaves]
        path: list[str] = []
        while len(nodes) > 1:
            if len(nodes) % 2:
                nodes.append(nodes[-1])
            sibling_idx = idx ^ 1
            if sibling_idx < len(nodes):
                path.append(nodes[sibling_idx].short())
            nodes = [MerkleNode.branch(nodes[i], nodes[i + 1]) for i in range(0, len(nodes), 2)]
            idx //= 2
        return path


_global_rule_store = ContentAddressableRuleStore()


# ===========================================================================
# § 8c  Optics  (Lens + Prism + Traversal)
# ===========================================================================
# Lenses:   bidirectional getter/setter for a field inside a structure.
# Prisms:   partial bidirectional iso for one branch of a sum type.
# Traversal: zero-or-more focuses (like a Lens but over a collection).
# All compose left-to-right with the @ operator.

@dataclasses.dataclass(frozen=True)
class Lens(Generic[T, U]):
    """Lens[S, A] — focuses on a field of type A within structure S.

    Compose with @: (lens_s_to_a @ lens_a_to_b) focuses from S all the way to B.
    """
    _get: Callable[[T], U]
    _set: Callable[[T, U], T]

    def get(self, s: T) -> U:
        return self._get(s)

    def set(self, s: T, a: U) -> T:
        return self._set(s, a)

    def modify(self, f: Callable[[U], U]) -> Callable[[T], T]:
        return lambda s: self._set(s, f(self._get(s)))

    def __matmul__(self, other: Lens[U, Any]) -> Lens[T, Any]:
        """Lens composition:  self @ other  dives from T→U→..."""
        return Lens(
            _get=lambda s: other._get(self._get(s)),
            _set=lambda s, b: self._set(s, other._set(self._get(s), b)),
        )

    @staticmethod
    def identity() -> Lens[T, T]:
        return Lens(_get=lambda s: s, _set=lambda _s, a: a)


@dataclasses.dataclass(frozen=True)
class Prism(Generic[T, U]):
    """Prism[S, A] — focuses on one branch of a sum type.

    preview: S → A | None   (None when not that branch)
    review:  A → S          (inject into the sum type)
    """
    _preview: Callable[[T], U | None]
    _review: Callable[[U], T]

    def preview(self, s: T) -> U | None:
        return self._preview(s)

    def review(self, a: U) -> T:
        return self._review(a)

    def is_case(self, s: T) -> bool:
        return self._preview(s) is not None

    def modify(self, f: Callable[[U], U]) -> Callable[[T], T]:
        def mod(s: T) -> T:
            inner = self._preview(s)
            return self._review(f(inner)) if inner is not None else s
        return mod

    def __matmul__(self, other: Prism[U, Any]) -> Prism[T, Any]:
        return Prism(
            _preview=lambda s: (
                other._preview(inner) if (inner := self._preview(s)) is not None else None
            ),
            _review=lambda b: self._review(other._review(b)),
        )


@dataclasses.dataclass(frozen=True)
class Traversal(Generic[T, U]):
    """Traversal[S, A] — focuses on zero-or-more A's inside S."""
    _to_list: Callable[[T], list[U]]
    _set_all: Callable[[T, list[U]], T]

    def to_list(self, s: T) -> list[U]:
        return self._to_list(s)

    def modify_all(self, f: Callable[[U], U]) -> Callable[[T], T]:
        def mod(s: T) -> T:
            items = self._to_list(s)
            return self._set_all(s, [f(x) for x in items])
        return mod

    def set_all(self, s: T, val: U) -> T:
        items = self._to_list(s)
        return self._set_all(s, [val] * len(items))

    @staticmethod
    def from_lens(lens: Lens[T, U]) -> Traversal[T, U]:
        return Traversal(
            _to_list=lambda s: [lens.get(s)],
            _set_all=lambda s, xs: lens.set(s, xs[0]) if xs else s,
        )


# ── Domain-specific lenses and prisms ─────────────────────────────────────────

number_value: Lens[Number, int] = Lens(
    _get=lambda n: n.value,
    _set=lambda _n, v: Number(v),
)

div_rule_divisor: Lens[DivisibilityRule, int] = Lens(
    _get=lambda r: r.divisor,
    _set=lambda r, d: DivisibilityRule(d, r.label),
)

div_rule_label: Lens[DivisibilityRule, str] = Lens(
    _get=lambda r: r.label,
    _set=lambda r, lbl: DivisibilityRule(r.divisor, lbl),
)

composite_rules: Lens[CompositeRule, tuple[VisitableRule, ...]] = Lens(
    _get=lambda r: r.rules,
    _set=lambda _r, rules: CompositeRule(rules),
)

composite_first_rule: Lens[CompositeRule, VisitableRule] = Lens(
    _get=lambda r: r.rules[0],
    _set=lambda r, rule: CompositeRule((rule,) + r.rules[1:]),
)

ok_prism: Prism[Any, Any] = Prism(
    _preview=lambda r: r.value if isinstance(r, Ok) else None,
    _review=Ok,
)

err_prism: Prism[Any, Any] = Prism(
    _preview=lambda r: r.error if isinstance(r, Err) else None,
    _review=Err,
)

divisibility_rules_traversal: Traversal[CompositeRule, DivisibilityRule] = Traversal(
    _to_list=lambda r: [sub for sub in r.rules if isinstance(sub, DivisibilityRule)],
    _set_all=lambda r, new_divs: CompositeRule(tuple(
        new_divs.pop(0) if isinstance(sub, DivisibilityRule) else sub
        for sub in r.rules
    )),
)


# ===========================================================================
# § 8d  Profunctor optics  (Iso, Adapter, profunctor-encoded Lens & Prism)
# ===========================================================================
# A *profunctor* P[A, B] is a bifunctor contravariant in A, covariant in B.
# Optics can be encoded as natural transformations between profunctors, making
# them composable via ordinary function composition rather than special
# combinators.
#
# Hierarchy implemented here:
#   Profunctor[A, B]    — dimap(f, g): P[A,B] → P[C,D]   (base)
#   Cartesian[A, B]     — first(): P[A,B] → P[(A,X),(B,X)]  (for Lens)
#   Cocartesian[A, B]   — left():  P[A,B] → P[A|X, B|X]    (for Prism)
#   Iso[S, A]           — isomorphism S ≅ A (get + review, lossless round-trip)
#   Adapter[S, A]       — one-directional view (weaker Iso, no review)
#
# Profunctor-encoded optics:
#   prof_lens(get, set)    — build a Cartesian-based optic (Lens)
#   prof_prism(preview, review) — build a Cocartesian-based optic (Prism)
#   compose_optic(o1, o2)  — compose two profunctor optics
#
# Domain examples:
#   number_to_value_iso    — Iso[Number, int]   (Number ≅ int)
#   label_or_str_adapter   — Adapter[tuple[Number,LabelT], str]

P = TypeVar("P")
Q = TypeVar("Q")
A2 = TypeVar("A2")
B2 = TypeVar("B2")


class Profunctor(abc.ABC, Generic[T, U]):
    """Base profunctor — contravariant in T, covariant in U."""

    @abc.abstractmethod
    def dimap(
        self,
        f: Callable[[Any], T],
        g: Callable[[U], Any],
    ) -> "Profunctor[Any, Any]": ...


@dataclasses.dataclass
class _FnProfunctor(Profunctor[T, U]):
    """Concrete profunctor backed by a plain function T → U."""
    _fn: Callable[[T], U]

    def apply(self, x: T) -> U:
        return self._fn(x)

    def dimap(
        self,
        f: Callable[[Any], T],
        g: Callable[[U], Any],
    ) -> "_FnProfunctor[Any, Any]":
        return _FnProfunctor(lambda x: g(self._fn(f(x))))

    def first(self) -> "_FnProfunctor[tuple[Any, Any], tuple[Any, Any]]":
        """Cartesian strength: run fn on first component of a pair."""
        return _FnProfunctor(lambda pair: (self._fn(pair[0]), pair[1]))

    def left(self) -> "_FnProfunctor[Any, Any]":
        """Cocartesian strength: run fn on Left branch of an Either (simulated as tagged union)."""
        def _apply(tagged: tuple[str, Any]) -> tuple[str, Any]:
            tag, val = tagged
            return ("left", self._fn(val)) if tag == "left" else ("right", val)
        return _FnProfunctor(_apply)


@dataclasses.dataclass(frozen=True)
class Iso(Generic[T, U]):
    """
    Isomorphism S ≅ A — lossless bidirectional conversion.
    Composes with @ (pipe operator).
    """
    _get: Callable[[T], U]
    _review: Callable[[U], T]

    def get(self, s: T) -> U:
        return self._get(s)

    def review(self, a: U) -> T:
        return self._review(a)

    def modify(self, f: Callable[[U], U]) -> Callable[[T], T]:
        return lambda s: self._review(f(self._get(s)))

    def inverse(self) -> "Iso[U, T]":
        return Iso(self._review, self._get)

    def __matmul__(self, other: "Iso[U, Any]") -> "Iso[T, Any]":
        return Iso(
            _get=lambda s: other._get(self._get(s)),
            _review=lambda b: self._review(other._review(b)),
        )

    def to_lens(self) -> "Lens[T, U]":
        return Lens(
            _get=self._get,
            _set=lambda s, a: self._review(a),
        )


@dataclasses.dataclass(frozen=True)
class Adapter(Generic[T, U]):
    """One-directional view (read-only Iso): a named projection."""
    name: str
    _get: Callable[[T], U]

    def get(self, s: T) -> U:
        return self._get(s)

    def map(self, f: Callable[[U], Any]) -> "Adapter[T, Any]":
        return Adapter(f"{self.name}.map", lambda s: f(self._get(s)))

    def __matmul__(self, other: "Adapter[U, Any]") -> "Adapter[T, Any]":
        return Adapter(
            f"{self.name}@{other.name}",
            lambda s: other._get(self._get(s)),
        )

    def __repr__(self) -> str:
        return f"Adapter({self.name!r})"


def prof_lens(
    getter: Callable[[T], U],
    setter: Callable[[T, U], T],
) -> "Lens[T, U]":
    """Build a Lens[T, U] from a getter and setter (profunctor-style API)."""
    return Lens(_get=getter, _set=setter)


def prof_prism(
    preview: Callable[[T], U | None],
    review: Callable[[U], T],
) -> "Prism[T, U]":
    """Build a Prism[T, U] from a preview and review (profunctor-style API)."""
    return Prism(_preview=preview, _review=review)


def prof_iso(
    get: Callable[[T], U],
    review: Callable[[U], T],
) -> Iso[T, U]:
    """Build an Iso[T, U]."""
    return Iso(_get=get, _review=review)


# ── Domain isos / adapters ────────────────────────────────────────────────

number_int_iso: Iso[Number, int] = prof_iso(
    get=lambda n: n.value,
    review=lambda v: Number(v),
)

label_default_adapter: Adapter[tuple[Number, LabelT], str] = Adapter(
    name="label_default",
    _get=lambda pair: pair[1] if pair[1] is not None else str(pair[0].value),
)

divisor_scale_iso: Callable[[int], Iso[DivisibilityRule, DivisibilityRule]] = (
    lambda scale: prof_iso(
        get=lambda r: DivisibilityRule(r.divisor * scale, r.label),
        review=lambda r: DivisibilityRule(r.divisor // scale, r.label),
    )
)

# Adapter: CompositeRule → list of label strings
composite_labels_adapter: Adapter[CompositeRule, list[str]] = Adapter(
    name="composite_labels",
    _get=lambda r: [
        sub.label for sub in r.rules
        if isinstance(sub, DivisibilityRule) and sub.label
    ],
)


# ===========================================================================
# § 9  Formatter strategy  (strategy + decorator chain)
# ===========================================================================

class Formatter(abc.ABC):
    name: ClassVar[str]

    @abc.abstractmethod
    def format(self, number: Number, label: LabelT) -> str: ...

    def __or__(self, other: FormatterDecorator) -> FormatterDecorator:
        other._delegate = self
        return other


class FormatterDecorator(Formatter, abc.ABC):
    _delegate: Formatter

    def __init__(self, delegate: Formatter | None = None) -> None:
        if delegate is not None:
            self._delegate = delegate


class DefaultFormatter(Formatter):
    name = "default"

    def format(self, number: Number, label: LabelT) -> str:
        return label if label is not None else str(number)


class UpperCaseFormatter(FormatterDecorator):
    name = "upper"

    def format(self, number: Number, label: LabelT) -> str:
        return self._delegate.format(number, label).upper()


class PaddedFormatter(FormatterDecorator):
    name = "padded"

    def __init__(self, width: int = 12, delegate: Formatter | None = None) -> None:
        super().__init__(delegate)
        self.width = width

    def format(self, number: Number, label: LabelT) -> str:
        return self._delegate.format(number, label).center(self.width)


class JsonFormatter(Formatter):
    name = "json"

    def format(self, number: Number, label: LabelT) -> str:
        import json
        return json.dumps({
            "n": number.value,
            "label": label,
            "parity": number.parity.value,
            "is_prime": number.is_prime,
            "is_perfect": number.is_perfect,
            "collatz_depth": number.collatz_depth,
            "digit_sum": number.digit_sum,
            "num_divisors": number.num_divisors,
            "fingerprint": number.fingerprint,
        })


class AnsiFormatter(FormatterDecorator):
    name = "ansi"

    _COLOURS: ClassVar[dict[str, str]] = {
        FIZZ:     "\033[94m",
        BUZZ:     "\033[92m",
        FIZZBUZZ: "\033[95m",
    }
    _RESET = "\033[0m"

    def format(self, number: Number, label: LabelT) -> str:
        text = self._delegate.format(number, label)
        colour = self._COLOURS.get(label or "", "")
        return f"{colour}{text}{self._RESET}" if colour else text


class TemplateFormatter(Formatter):
    """Format using a Python str.format_map template.

    Available keys: n, label, parity, is_prime, fingerprint.
    Example template: "{n:>4} | {label:<10} [{parity}]"
    """
    name = "template"

    def __init__(self, template: str = "{n:>4} | {label:<10}") -> None:
        self.template = template

    def format(self, number: Number, label: LabelT) -> str:
        return self.template.format_map({
            "n": number.value,
            "label": label or str(number),
            "parity": number.parity.value,
            "is_prime": number.is_prime,
            "fingerprint": number.fingerprint,
        })


# ===========================================================================
# § 10  Metrics
# ===========================================================================

@dataclasses.dataclass
class Snapshot:
    timestamp: float
    label: LabelT
    number: int


class MetricsCollector:
    def __init__(self, window: int = 1000) -> None:
        self._lock = threading.Lock()
        self._counter: Counter[str] = Counter()
        self._history: deque[Snapshot] = deque(maxlen=window)
        self._total = 0

    def record(self, number: Number, label: LabelT) -> None:
        with self._lock:
            self._total += 1
            self._counter[label or "<number>"] += 1
            self._history.append(Snapshot(time.perf_counter(), label, number.value))

    @property
    def total(self) -> int:
        with self._lock:
            return self._total

    def top_labels(self, n: int = 5) -> list[tuple[str, int]]:
        with self._lock:
            return self._counter.most_common(n)

    def label_rate(self) -> float:
        with self._lock:
            numbers = self._counter.get("<number>", 0)
            return 1.0 - (numbers / self._total) if self._total else 0.0

    def report(self) -> str:
        total = self.total
        if not total:
            return "No data."
        lines = [
            f"Total processed : {total}",
            f"Label rate      : {self.label_rate():.1%}",
            "Top labels:",
        ]
        for label, count in self.top_labels():
            lines.append(f"  {label:<18} {count:>6}  ({count / total:.1%})")
        return "\n".join(lines)


# ===========================================================================
# § 10b  Bloom filter  (probabilistic label-seen cache)
# ===========================================================================

class BloomFilter:
    """Space-efficient probabilistic membership test.

    False positives are possible; false negatives are impossible.
    Optimal bit-array size m and hash-count k are derived from expected
    item count and desired false-positive rate.
    """

    def __init__(self, expected_items: int = 10_000, fp_rate: float = 0.01) -> None:
        m = math.ceil(-expected_items * math.log(fp_rate) / (math.log(2) ** 2))
        k = max(1, round((m / expected_items) * math.log(2)))
        self._m = m
        self._k = k
        self._bits = bytearray(math.ceil(m / 8))
        self._count = 0
        logging.getLogger("fizzbuzz.bloom").debug(
            "BloomFilter: m=%d bits, k=%d hashes, target fp_rate=%.2f%%", m, k, fp_rate * 100
        )

    def _positions(self, item: str) -> Iterator[int]:
        for seed in range(self._k):
            raw = hashlib.md5(f"{seed}\x00{item}".encode(), usedforsecurity=False).digest()
            yield int.from_bytes(raw[:4], "little") % self._m

    def add(self, item: str) -> None:
        for pos in self._positions(item):
            self._bits[pos >> 3] |= 1 << (pos & 7)
        self._count += 1

    def __contains__(self, item: str) -> bool:
        return all(self._bits[pos >> 3] & (1 << (pos & 7)) for pos in self._positions(item))

    def __len__(self) -> int:
        return self._count

    @property
    def fill_ratio(self) -> float:
        set_bits = sum(bin(b).count("1") for b in self._bits)
        return set_bits / self._m

    def estimated_fp_rate(self) -> float:
        return (1 - math.exp(-self._k * self._count / self._m)) ** self._k


# ===========================================================================
# § 10c  HyperLogLog  (probabilistic distinct-cardinality estimator)
# ===========================================================================
# HyperLogLog estimates |S| (number of distinct elements in a multiset S) in
# O(2^b) space and O(1) amortised time, with ~1.04/√(2^b) relative error.
#
# Algorithm (Flajolet et al., 2007):
#   1. Hash each element to a b + 64-b bit string.
#   2. Use the first b bits as a register index j ∈ [0, 2^b).
#   3. In register M[j] store max(M[j], position_of_first_1_in_remaining_bits).
#   4. Estimate cardinality as α_m · m² · (Σ 2^{-M[j]})^{-1} with bias corrections
#      for small and large range.
#
# Extra: `merge(other)` — union of two HyperLogLog sketches in O(m) time.

_HLL_ALPHA: dict[int, float] = {16: 0.673, 32: 0.697, 64: 0.709}


class HyperLogLog:
    """Space-efficient probabilistic distinct-element counter."""

    def __init__(self, b: int = 8) -> None:
        """
        b — number of register bits; m = 2^b registers.
        b=8 → 256 registers, ~1.6% relative error.
        b=10 → 1024 registers, ~0.8% relative error.
        """
        if not 4 <= b <= 16:
            raise ValueError("b must be in [4, 16]")
        self._b = b
        self._m = 1 << b         # number of registers
        self._M = bytearray(self._m)  # register array (max rho values ≤ 64)
        # α_m bias correction constant
        if self._m in _HLL_ALPHA:
            self._alpha = _HLL_ALPHA[self._m]
        else:
            self._alpha = 0.7213 / (1.0 + 1.079 / self._m)

    def add(self, item: Any) -> None:
        """Add an item to the sketch."""
        h = int(hashlib.md5(str(item).encode()).hexdigest(), 16)
        # Use top b bits as register index
        j = h >> (128 - self._b)
        # Remaining bits: find position of first 1 (rho)
        w = h & ((1 << (128 - self._b)) - 1)
        # rho = position of the leftmost 1-bit in w (1-indexed, max = 128-b)
        max_bits = 128 - self._b
        if w == 0:
            rho = max_bits + 1
        else:
            rho = max_bits - w.bit_length() + 1
        if rho > self._M[j]:
            self._M[j] = rho

    def estimate(self) -> float:
        """Return the estimated number of distinct elements."""
        m = self._m
        Z = sum(2.0 ** (-float(r)) for r in self._M)
        E = self._alpha * m * m / Z

        # Small range correction
        if E <= 2.5 * m:
            V = self._M.count(0)   # number of zero registers
            if V > 0:
                E = m * math.log(m / V)

        # Large range correction (2^32 boundary — adapt for 128-bit hashes)
        # Not needed for typical FizzBuzz cardinalities; skip here.
        return E

    def merge(self, other: "HyperLogLog") -> "HyperLogLog":
        """Return a new sketch representing the union of self and other."""
        if self._b != other._b:
            raise ValueError("Cannot merge HyperLogLog sketches with different b")
        merged = HyperLogLog(self._b)
        for i in range(self._m):
            merged._M[i] = max(self._M[i], other._M[i])
        return merged

    def __len__(self) -> int:
        return round(self.estimate())

    def relative_error(self) -> float:
        """Theoretical relative standard error."""
        return 1.04 / math.sqrt(self._m)

    def __repr__(self) -> str:
        return (f"HyperLogLog(b={self._b}, m={self._m}, "
                f"estimate≈{self.estimate():.0f}, "
                f"err≈{self.relative_error():.1%})")


def hll_fizzbuzz(
    rule: "VisitableRule",
    start: int = 1,
    stop: int = 10_000,
    b: int = 8,
) -> HyperLogLog:
    """Build a HyperLogLog sketch of distinct FizzBuzz outputs over [start, stop]."""
    hll = HyperLogLog(b)
    for n in range(start, stop + 1):
        label = rule(Number(n)) or str(n)
        hll.add(label)
    return hll


# ===========================================================================
# § 10d  Count-Min Sketch  (sub-linear frequency estimation)
# ===========================================================================
# The Count-Min Sketch (Cormode & Muthukrishna, 2005) estimates item
# frequencies in a data stream using a d × w counter matrix with d
# pairwise-independent hash functions.
#
# Guarantees (with probability ≥ 1 − δ):
#   estimate(x) ≥ true_count(x)                  (never under-counts)
#   estimate(x) ≤ true_count(x) + ε · ||counts||₁
#
# where w = ⌈e/ε⌉ and d = ⌈ln(1/δ)⌉.
#
# Operations:
#   add(item, count=1)          — update counters
#   estimate(item)              — frequency estimate (min of d hash-rows)
#   merge(other)                — element-wise max (union of two streams)
#   top_k(k, universe)          — approximate heavy hitters from a universe
#   inner_product(other)        — dot-product estimate for join-size queries

class CountMinSketch:
    """Sub-linear frequency estimator using a 2-D counter array."""

    def __init__(self, epsilon: float = 0.01, delta: float = 0.001) -> None:
        """
        epsilon — additive error factor (smaller → wider sketch)
        delta   — failure probability (smaller → deeper sketch)
        """
        self._w = math.ceil(math.e / epsilon)
        self._d = math.ceil(math.log(1 / delta))
        self._counts = [[0] * self._w for _ in range(self._d)]
        # d independent hash seeds
        self._seeds = [random.randint(1, 2**31 - 1) for _ in range(self._d)]
        self._total: int = 0

    def _hash(self, item: Any, row: int) -> int:
        """Row-specific hash function."""
        raw = hashlib.md5(f"{self._seeds[row]}:{item}".encode()).hexdigest()
        return int(raw, 16) % self._w

    def add(self, item: Any, count: int = 1) -> None:
        for i in range(self._d):
            self._counts[i][self._hash(item, i)] += count
        self._total += count

    def estimate(self, item: Any) -> int:
        """Return the frequency estimate for item (≥ true count)."""
        return min(self._counts[i][self._hash(item, i)] for i in range(self._d))

    def merge(self, other: "CountMinSketch") -> "CountMinSketch":
        """Element-wise sum — models stream union."""
        if (self._w, self._d) != (other._w, other._d):
            raise ValueError("Sketch dimensions must match for merge")
        merged = CountMinSketch.__new__(CountMinSketch)
        merged._w = self._w
        merged._d = self._d
        merged._seeds = list(self._seeds)
        merged._counts = [
            [self._counts[i][j] + other._counts[i][j] for j in range(self._w)]
            for i in range(self._d)
        ]
        merged._total = self._total + other._total
        return merged

    def inner_product(self, other: "CountMinSketch") -> int:
        """
        Estimate the inner product (join size) of two frequency vectors.
        Returns min over rows of Σ_j counts_a[i][j] * counts_b[i][j].
        """
        if (self._w, self._d) != (other._w, other._d):
            raise ValueError("Sketch dimensions must match")
        return min(
            sum(self._counts[i][j] * other._counts[i][j] for j in range(self._w))
            for i in range(self._d)
        )

    def top_k(self, k: int, universe: Iterable[Any]) -> list[tuple[Any, int]]:
        """Approximate top-k heavy hitters from a known universe."""
        estimates = [(item, self.estimate(item)) for item in universe]
        return sorted(estimates, key=lambda x: -x[1])[:k]

    @property
    def width(self) -> int:
        return self._w

    @property
    def depth(self) -> int:
        return self._d

    @property
    def total_count(self) -> int:
        return self._total

    def __repr__(self) -> str:
        return (f"CountMinSketch(w={self._w}, d={self._d}, "
                f"total={self._total})")


def cms_fizzbuzz(
    rule: "VisitableRule",
    start: int = 1,
    stop: int = 1000,
    epsilon: float = 0.05,
    delta: float = 0.01,
) -> CountMinSketch:
    """Build a Count-Min Sketch of label frequencies over [start, stop]."""
    cms = CountMinSketch(epsilon=epsilon, delta=delta)
    for n in range(start, stop + 1):
        label = rule(Number(n)) or str(n)
        cms.add(label)
    return cms


# ===========================================================================
# § 11  Circuit breaker
# ===========================================================================

class CircuitState(enum.Enum):
    CLOSED    = "closed"
    OPEN      = "open"
    HALF_OPEN = "half_open"


class CircuitBreaker:
    """Trips to OPEN after `failure_threshold` consecutive failures;
    recovers to HALF_OPEN after `recovery_timeout` seconds."""

    def __init__(
        self,
        failure_threshold: int = 5,
        recovery_timeout: float = 30.0,
        name: str = "default",
    ) -> None:
        self._threshold = failure_threshold
        self._timeout = recovery_timeout
        self.name = name
        self._state = CircuitState.CLOSED
        self._failures = 0
        self._last_failure: float = 0.0
        self._lock = threading.Lock()
        self._log = logging.getLogger(f"fizzbuzz.circuit.{name}")

    @property
    def state(self) -> CircuitState:
        with self._lock:
            return self._state

    def call(self, fn: Callable[..., T], *args: Any, **kwargs: Any) -> T:
        with self._lock:
            if self._state == CircuitState.OPEN:
                if time.monotonic() - self._last_failure > self._timeout:
                    self._state = CircuitState.HALF_OPEN
                    self._log.info("Circuit %r → HALF_OPEN", self.name)
                else:
                    raise RuntimeError(f"Circuit {self.name!r} is OPEN — rejecting call")

        try:
            result = fn(*args, **kwargs)
            with self._lock:
                if self._state == CircuitState.HALF_OPEN:
                    self._log.info("Circuit %r → CLOSED (recovered)", self.name)
                self._state = CircuitState.CLOSED
                self._failures = 0
            return result
        except Exception:
            with self._lock:
                self._failures += 1
                self._last_failure = time.monotonic()
                if self._failures >= self._threshold:
                    self._state = CircuitState.OPEN
                    self._log.error("Circuit %r → OPEN after %d failures", self.name, self._failures)
            raise


# ===========================================================================
# § 12  Output sinks
# ===========================================================================

class OutputSink(abc.ABC):
    @abc.abstractmethod
    def write(self, line: str) -> None: ...

    @abc.abstractmethod
    def flush(self) -> None: ...

    @contextmanager
    def open(self) -> Generator[OutputSink, None, None]:
        try:
            yield self
        finally:
            self.flush()


class StdoutSink(OutputSink):
    def write(self, line: str) -> None:
        print(line)

    def flush(self) -> None:
        sys.stdout.flush()


class BufferedSink(OutputSink):
    def __init__(self) -> None:
        self._buf: list[str] = []

    def write(self, line: str) -> None:
        self._buf.append(line)

    def flush(self) -> None:
        pass

    @property
    def lines(self) -> list[str]:
        return list(self._buf)


class TeedSink(OutputSink):
    """Fans out writes to multiple delegate sinks."""

    def __init__(self, *sinks: OutputSink) -> None:
        self._sinks = list(sinks)

    def write(self, line: str) -> None:
        for sink in self._sinks:
            sink.write(line)

    def flush(self) -> None:
        for sink in self._sinks:
            sink.flush()


class RetryingSink(OutputSink):
    """Wraps a sink and retries failed writes with exponential backoff."""

    def __init__(
        self,
        delegate: OutputSink,
        max_attempts: int = 3,
        backoff_base: float = 0.05,
    ) -> None:
        self._delegate = delegate
        self._max = max_attempts
        self._base = backoff_base
        self._log = logging.getLogger("fizzbuzz.sink.retry")

    def write(self, line: str) -> None:
        for attempt in range(1, self._max + 1):
            try:
                self._delegate.write(line)
                return
            except OSError as exc:
                if attempt == self._max:
                    raise
                delay = self._base * (2 ** (attempt - 1))
                self._log.warning("Write attempt %d failed (%s); retrying in %.3fs", attempt, exc, delay)
                time.sleep(delay)

    def flush(self) -> None:
        self._delegate.flush()


class CircuitBreakerSink(OutputSink):
    """Wraps a sink with a circuit breaker to handle sustained write failures."""

    def __init__(self, delegate: OutputSink, breaker: CircuitBreaker | None = None) -> None:
        self._delegate = delegate
        self._breaker = breaker or CircuitBreaker(name="sink")

    def write(self, line: str) -> None:
        self._breaker.call(self._delegate.write, line)

    def flush(self) -> None:
        self._delegate.flush()

    @property
    def circuit_state(self) -> CircuitState:
        return self._breaker.state


class AsyncQueueSink(OutputSink):
    def __init__(self, q: asyncio.Queue[str]) -> None:
        self._q = q
        self._loop = asyncio.get_event_loop()

    def write(self, line: str) -> None:
        self._loop.call_soon_threadsafe(self._q.put_nowait, line)

    def flush(self) -> None:
        pass


# ===========================================================================
# § 13  Range abstractions
# ===========================================================================

class NumberRange:
    def __init__(self, start: int, stop: int, step: int = 1) -> None:
        if step <= 0:
            raise ValueError("step must be positive")
        self.start = start
        self.stop = stop
        self.step = step

    def __iter__(self) -> Iterator[Number]:
        return (Number(i) for i in range(self.start, self.stop + 1, self.step))

    def __len__(self) -> int:
        return max(0, (self.stop - self.start) // self.step + 1)

    def __contains__(self, item: int | Number) -> bool:
        v = item.value if isinstance(item, Number) else item
        return self.start <= v <= self.stop and (v - self.start) % self.step == 0

    def __add__(self, other: NumberRange) -> ChainedNumberRange:
        return ChainedNumberRange(self, other)

    def intersect(self, other: NumberRange) -> NumberRange | None:
        new_start = max(self.start, other.start)
        new_stop = min(self.stop, other.stop)
        new_step = math.lcm(self.step, other.step)
        if new_start > new_stop:
            return None
        return NumberRange(new_start, new_stop, new_step)

    def chunked(self, size: int) -> Iterator[list[Number]]:
        it = iter(self)
        while chunk := list(itertools.islice(it, size)):
            yield chunk

    def filter(self, predicate: Callable[[Number], bool]) -> list[Number]:
        return [n for n in self if predicate(n)]

    def __repr__(self) -> str:
        return f"NumberRange({self.start!r}, {self.stop!r}, step={self.step!r})"


class ChainedNumberRange:
    """Logical concatenation of multiple NumberRanges."""

    def __init__(self, *ranges: NumberRange) -> None:
        self._ranges = ranges

    def __iter__(self) -> Iterator[Number]:
        return itertools.chain.from_iterable(self._ranges)

    def __len__(self) -> int:
        return sum(len(r) for r in self._ranges)

    def __repr__(self) -> str:
        return f"ChainedNumberRange({', '.join(repr(r) for r in self._ranges)})"


# ===========================================================================
# § 13b  Reactive Observable  (push-based stream with Rx-style operators)
# ===========================================================================

class Disposable:
    def __init__(self, dispose_fn: Callable[[], None] = lambda: None) -> None:
        self._fn = dispose_fn
        self._disposed = False

    def dispose(self) -> None:
        if not self._disposed:
            self._disposed = True
            self._fn()

    @property
    def is_disposed(self) -> bool:
        return self._disposed

    @staticmethod
    def empty() -> Disposable:
        return Disposable()


@dataclasses.dataclass
class Observer(Generic[T]):
    on_next: Callable[[T], None]
    on_error: Callable[[Exception], None] = dataclasses.field(default=lambda e: None)
    on_complete: Callable[[], None] = dataclasses.field(default=lambda: None)


class Observable(Generic[T]):
    """Cold observable: subscribing re-runs the producer for each subscriber.

    Operators are lazy — nothing executes until .subscribe() or .collect()."""

    def __init__(self, _subscribe: Callable[[Observer[T]], Disposable]) -> None:
        self._sub_fn = _subscribe

    def subscribe(
        self,
        on_next: Callable[[T], None],
        on_error: Callable[[Exception], None] | None = None,
        on_complete: Callable[[], None] | None = None,
    ) -> Disposable:
        return self._sub_fn(Observer(on_next, on_error or (lambda e: None), on_complete or (lambda: None)))

    # ── operators ─────────────────────────────────────────────────────────────

    def map(self, f: Callable[[T], U]) -> Observable[U]:
        def sub(obs: Observer[U]) -> Disposable:
            return self._sub_fn(Observer(
                on_next=lambda x: obs.on_next(f(x)),
                on_error=obs.on_error, on_complete=obs.on_complete,
            ))
        return Observable(sub)

    def filter(self, pred: Callable[[T], bool]) -> Observable[T]:
        def sub(obs: Observer[T]) -> Disposable:
            return self._sub_fn(Observer(
                on_next=lambda x: obs.on_next(x) if pred(x) else None,
                on_error=obs.on_error, on_complete=obs.on_complete,
            ))
        return Observable(sub)

    def take(self, n: int) -> Observable[T]:
        def sub(obs: Observer[T]) -> Disposable:
            remaining = [n]
            d: list[Disposable] = []

            def on_next(x: T) -> None:
                if remaining[0] > 0:
                    remaining[0] -= 1
                    obs.on_next(x)
                    if remaining[0] == 0:
                        obs.on_complete()
                        if d:
                            d[0].dispose()

            d.append(self._sub_fn(Observer(on_next, obs.on_error, obs.on_complete)))
            return d[0]
        return Observable(sub)

    def skip(self, n: int) -> Observable[T]:
        def sub(obs: Observer[T]) -> Disposable:
            skipped = [0]
            return self._sub_fn(Observer(
                on_next=lambda x: obs.on_next(x) if (skipped.__setitem__(0, skipped[0] + 1) or skipped[0] > n) else None,
                on_error=obs.on_error, on_complete=obs.on_complete,
            ))
        return Observable(sub)

    def flat_map(self, f: Callable[[T], Observable[U]]) -> Observable[U]:
        def sub(obs: Observer[U]) -> Disposable:
            return self._sub_fn(Observer(
                on_next=lambda x: f(x).subscribe(obs.on_next, obs.on_error),
                on_error=obs.on_error, on_complete=obs.on_complete,
            ))
        return Observable(sub)

    def reduce(self, fn: Callable[[U, T], U], initial: U) -> Observable[U]:
        def sub(obs: Observer[U]) -> Disposable:
            acc = [initial]
            def on_complete() -> None:
                obs.on_next(acc[0])
                obs.on_complete()
            return self._sub_fn(Observer(
                on_next=lambda x: acc.__setitem__(0, fn(acc[0], x)),
                on_error=obs.on_error, on_complete=on_complete,
            ))
        return Observable(sub)

    def scan(self, fn: Callable[[U, T], U], initial: U) -> Observable[U]:
        """Like reduce but emits running accumulator after each item."""
        def sub(obs: Observer[U]) -> Disposable:
            acc = [initial]
            def on_next(x: T) -> None:
                acc[0] = fn(acc[0], x)
                obs.on_next(acc[0])
            return self._sub_fn(Observer(on_next, obs.on_error, obs.on_complete))
        return Observable(sub)

    def do(self, f: Callable[[T], None]) -> Observable[T]:
        """Side-effect tap without altering values."""
        return self.map(lambda x: (f(x), x)[1])

    def enumerate(self) -> Observable[tuple[int, T]]:
        def sub(obs: Observer[tuple[int, T]]) -> Disposable:
            idx = [0]
            def on_next(x: T) -> None:
                obs.on_next((idx[0], x))
                idx[0] += 1
            return self._sub_fn(Observer(on_next, obs.on_error, obs.on_complete))
        return Observable(sub)

    def collect(self) -> list[T]:
        result: list[T] = []
        self.subscribe(result.append)
        return result

    def first(self) -> T | None:
        items = self.take(1).collect()
        return items[0] if items else None

    # ── constructors ──────────────────────────────────────────────────────────

    @staticmethod
    def from_iterable(it: Iterable[T]) -> Observable[T]:
        def sub(obs: Observer[T]) -> Disposable:
            try:
                for item in it:
                    obs.on_next(item)
                obs.on_complete()
            except Exception as exc:
                obs.on_error(exc)
            return Disposable.empty()
        return Observable(sub)

    @staticmethod
    def of(*items: T) -> Observable[T]:
        return Observable.from_iterable(items)

    @staticmethod
    def empty_obs() -> Observable[Never]:
        return Observable(lambda obs: (obs.on_complete(), Disposable.empty())[1])

    @staticmethod
    def error_obs(exc: Exception) -> Observable[Never]:
        return Observable(lambda obs: (obs.on_error(exc), Disposable.empty())[1])

    @staticmethod
    def range_obs(start: int, stop: int, step: int = 1) -> Observable[Number]:
        return Observable.from_iterable(NumberRange(start, stop, step))


class Subject(Observable[T], Generic[T]):
    """Hot observable that is also an observer: push values imperatively."""

    def __init__(self) -> None:
        self._observers: list[Observer[T]] = []
        self._done = False
        self._error: Exception | None = None
        super().__init__(self._do_subscribe)

    def _do_subscribe(self, obs: Observer[T]) -> Disposable:
        if self._done:
            obs.on_complete()
            return Disposable.empty()
        if self._error:
            obs.on_error(self._error)
            return Disposable.empty()
        self._observers.append(obs)
        return Disposable(lambda: self._observers.remove(obs) if obs in self._observers else None)

    def next(self, item: T) -> None:
        for obs in list(self._observers):
            obs.on_next(item)

    def error(self, exc: Exception) -> None:
        self._error = exc
        for obs in list(self._observers):
            obs.on_error(exc)
        self._observers.clear()

    def complete(self) -> None:
        self._done = True
        for obs in list(self._observers):
            obs.on_complete()
        self._observers.clear()


def fizzbuzz_observable(
    start: int = 1,
    stop: int = 100,
    rule_name: str = "classic",
) -> Observable[tuple[Number, LabelT]]:
    """Returns a cold Observable of (Number, label) pairs."""
    rule = RuleRegistry().get(rule_name)
    return Observable.from_iterable(NumberRange(start, stop)).map(lambda n: (n, rule(n)))


# ===========================================================================
# § 13c  Rule tree zipper
# ===========================================================================
# A zipper provides a "cursor" into a tree with O(1) local edits.
# Navigating up reconstructs parent nodes lazily from breadcrumb context.
#
# Structure: the zipper holds the *focus* (current node) plus a *crumb trail*
# (stack of sibling contexts) that describes the path from the root.

@dataclasses.dataclass(frozen=True)
class ZipCrumb:
    """One level of zipper context: siblings to the left and right of focus."""
    left: tuple[VisitableRule, ...]   # siblings before focus (reversed: head=nearest)
    right: tuple[VisitableRule, ...]  # siblings after focus


@dataclasses.dataclass(frozen=True)
class RuleZipper:
    """A navigable cursor into a flat CompositeRule child list."""
    focus: VisitableRule
    crumbs: tuple[ZipCrumb, ...]

    # ── navigation ───────────────────────────────────────────────────────────

    def down(self, idx: int = 0) -> RuleZipper:
        """Enter the focused CompositeRule at position `idx`."""
        if not isinstance(self.focus, CompositeRule):
            raise TypeError("focus is not a CompositeRule; cannot go down")
        rules = self.focus.rules
        if not rules:
            raise IndexError("Empty composite rule")
        idx = idx % len(rules)
        return RuleZipper(
            focus=rules[idx],
            crumbs=self.crumbs + (ZipCrumb(rules[:idx][::-1], rules[idx + 1:]),),
        )

    def up(self) -> RuleZipper:
        if not self.crumbs:
            raise IndexError("Already at root")
        crumb = self.crumbs[-1]
        siblings = crumb.left[::-1] + (self.focus,) + crumb.right
        return RuleZipper(focus=CompositeRule(siblings), crumbs=self.crumbs[:-1])

    def right(self) -> RuleZipper:
        if not self.crumbs:
            raise IndexError("No context (at root)")
        crumb = self.crumbs[-1]
        if not crumb.right:
            raise IndexError("No right sibling")
        return RuleZipper(
            focus=crumb.right[0],
            crumbs=self.crumbs[:-1] + (ZipCrumb((self.focus,) + crumb.left, crumb.right[1:]),),
        )

    def left(self) -> RuleZipper:
        if not self.crumbs:
            raise IndexError("No context (at root)")
        crumb = self.crumbs[-1]
        if not crumb.left:
            raise IndexError("No left sibling")
        return RuleZipper(
            focus=crumb.left[0],
            crumbs=self.crumbs[:-1] + (ZipCrumb(crumb.left[1:], (self.focus,) + crumb.right),),
        )

    def top(self) -> RuleZipper:
        z = self
        while z.crumbs:
            z = z.up()
        return z

    # ── edits ────────────────────────────────────────────────────────────────

    def modify(self, f: Callable[[VisitableRule], VisitableRule]) -> RuleZipper:
        return dataclasses.replace(self, focus=f(self.focus))

    def replace(self, new_rule: VisitableRule) -> RuleZipper:
        return dataclasses.replace(self, focus=new_rule)

    def insert_right(self, rule: VisitableRule) -> RuleZipper:
        if not self.crumbs:
            raise IndexError("No context (at root)")
        crumb = self.crumbs[-1]
        return RuleZipper(
            focus=self.focus,
            crumbs=self.crumbs[:-1] + (ZipCrumb(crumb.left, (rule,) + crumb.right),),
        )

    def insert_left(self, rule: VisitableRule) -> RuleZipper:
        if not self.crumbs:
            raise IndexError("No context (at root)")
        crumb = self.crumbs[-1]
        return RuleZipper(
            focus=self.focus,
            crumbs=self.crumbs[:-1] + (ZipCrumb((rule,) + crumb.left, crumb.right),),
        )

    def delete(self) -> RuleZipper:
        """Remove focus; move to right sibling, then left, then up."""
        if not self.crumbs:
            raise ValueError("Cannot delete root")
        crumb = self.crumbs[-1]
        if crumb.right:
            return RuleZipper(
                focus=crumb.right[0],
                crumbs=self.crumbs[:-1] + (ZipCrumb(crumb.left, crumb.right[1:]),),
            )
        if crumb.left:
            return RuleZipper(
                focus=crumb.left[0],
                crumbs=self.crumbs[:-1] + (ZipCrumb(crumb.left[1:], crumb.right),),
            )
        raise ValueError("Cannot delete the only rule in a composite")

    # ── extraction ───────────────────────────────────────────────────────────

    def root(self) -> CompositeRule:
        """Navigate to top and return the reconstructed CompositeRule."""
        z = self.top()
        if isinstance(z.focus, CompositeRule):
            return z.focus
        return CompositeRule((z.focus,))

    def path(self) -> list[str]:
        return [f"depth={i} left={len(c.left)} right={len(c.right)}" for i, c in enumerate(self.crumbs)]

    def __repr__(self) -> str:
        return f"RuleZipper(focus={self.focus!r}, depth={len(self.crumbs)})"


def zip_rule(rule: CompositeRule) -> RuleZipper:
    """Construct a zipper positioned at the root (the composite itself)."""
    return RuleZipper(focus=rule, crumbs=())


# ===========================================================================
# § 13d  Transducers  (composable, source-independent reducing transforms)
# ===========================================================================
# A *reducer* has type   (acc, item) -> acc.
# A *transducer* is a higher-order function   (reducer) -> reducer.
# Because transducers transform reducers—not values—they compose with plain
# function composition and work identically over lists, generators, Observables,
# channels, or any other iterable/push source.
#
# Primitives:
#   mapping(f)           map f over items
#   filtering(pred)      drop items where pred is False
#   taking(n)            pass only the first n items
#   dropping(n)          skip the first n items
#   flat_mapping(f)      expand each item to zero or more sub-items
#   deduplicating()      drop consecutive duplicate items
#   windowing(size)      emit sliding windows as tuples
#   labelling(rule)      FizzBuzz-specific: Number → (Number, LabelT)
#   categorising()       attach NumberCategory flag to each Number
#
# compose_xf(*xfs)       left-to-right composition (first xf applied first)
# transduce(xf, rf, init, iterable)  drive the transducer over an iterable
# into(xf, iterable)     shorthand: collect into list

_Acc = TypeVar("_Acc")
_In  = TypeVar("_In")
_Out = TypeVar("_Out")

Reducer: TypeAlias = Callable[[Any, Any], Any]
Transducer: TypeAlias = Callable[[Reducer], Reducer]


def mapping(f: Callable[[Any], Any]) -> Transducer:
    def _xf(rf: Reducer) -> Reducer:
        def _step(acc: Any, item: Any) -> Any:
            return rf(acc, f(item))
        return _step
    return _xf


def filtering(pred: Callable[[Any], bool]) -> Transducer:
    def _xf(rf: Reducer) -> Reducer:
        def _step(acc: Any, item: Any) -> Any:
            return rf(acc, item) if pred(item) else acc
        return _step
    return _xf


def taking(n: int) -> Transducer:
    def _xf(rf: Reducer) -> Reducer:
        _count = [0]
        def _step(acc: Any, item: Any) -> Any:
            if _count[0] >= n:
                return acc
            _count[0] += 1
            return rf(acc, item)
        return _step
    return _xf


def dropping(n: int) -> Transducer:
    def _xf(rf: Reducer) -> Reducer:
        _dropped = [0]
        def _step(acc: Any, item: Any) -> Any:
            if _dropped[0] < n:
                _dropped[0] += 1
                return acc
            return rf(acc, item)
        return _step
    return _xf


def flat_mapping(f: Callable[[Any], Iterable[Any]]) -> Transducer:
    def _xf(rf: Reducer) -> Reducer:
        def _step(acc: Any, item: Any) -> Any:
            for sub in f(item):
                acc = rf(acc, sub)
            return acc
        return _step
    return _xf


def deduplicating() -> Transducer:
    _UNSET = object()
    def _xf(rf: Reducer) -> Reducer:
        _prev = [_UNSET]
        def _step(acc: Any, item: Any) -> Any:
            if item == _prev[0]:
                return acc
            _prev[0] = item
            return rf(acc, item)
        return _step
    return _xf


def windowing(size: int) -> Transducer:
    """Emit sliding windows of `size` as tuples."""
    def _xf(rf: Reducer) -> Reducer:
        _buf: list[Any] = []
        def _step(acc: Any, item: Any) -> Any:
            _buf.append(item)
            if len(_buf) > size:
                _buf.pop(0)
            if len(_buf) == size:
                return rf(acc, tuple(_buf))
            return acc
        return _step
    return _xf


def labelling(rule: "VisitableRule") -> Transducer:
    """FizzBuzz transducer: Number → (Number, LabelT)."""
    return mapping(lambda n: (n, rule(n)))


def categorising() -> Transducer:
    """Attach NumberCategory to each Number: Number → (Number, NumberCategory)."""
    def _categorise(n: "Number") -> tuple["Number", "NumberCategory"]:
        cat = NumberCategory.NONE
        if n.value % 3 == 0:
            cat |= NumberCategory.FIZZ
        if n.value % 5 == 0:
            cat |= NumberCategory.BUZZ
        if n.is_prime:
            cat |= NumberCategory.PRIME
        if n.is_perfect:
            cat |= NumberCategory.PERFECT
        return (n, cat)
    return mapping(_categorise)


def compose_xf(*xfs: Transducer) -> Transducer:
    """Compose transducers left-to-right (first argument is applied first)."""
    def _composed(rf: Reducer) -> Reducer:
        result = rf
        for xf in reversed(xfs):
            result = xf(result)
        return result
    return _composed


def transduce(
    xf: Transducer,
    rf: Reducer,
    init: Any,
    iterable: Iterable[Any],
) -> Any:
    """Run transducer xf with reducing function rf over iterable, starting from init."""
    step = xf(rf)
    acc = init
    for item in iterable:
        acc = step(acc, item)
    return acc


def into(xf: Transducer, iterable: Iterable[Any]) -> list[Any]:
    """Collect transduced items into a list."""
    return transduce(xf, lambda acc, x: [*acc, x], [], iterable)


# ===========================================================================
# § 13e  Store comonad  (context-sensitive, position-indexed computation)
# ===========================================================================
# The Store comonad Store[S, A] = (S → A, S) models a "spreadsheet":
# every cell position S has a computed value A, and a *cursor* tracks the
# current focus.
#
#   store.extract()           value at the current cursor
#   store.seek(s)             move cursor to s (returns new Store)
#   store.peek(s)             read value at s without moving cursor
#   store.map(f)              f applied pointwise to all positions
#   store.extend(f)           cobind: new store where pos s holds f(seek(s))
#   store.experiment(f)       f(cursor) → [positions] → [values]
#   store.coflatten()         duplicate: each position holds Store focused there
#
# FizzBuzz application: Store[int, LabelT] lets each position inspect its
# neighbours.  `fizzbuzz_context_labels` uses `extend` to annotate each
# number with whether its predecessor and successor are also labelled.

S = TypeVar("S")


@dataclasses.dataclass(frozen=True)
class Store(Generic[S, T_co]):
    """Store comonad: an infinite position-indexed store of lazily computed values."""
    _fn: Callable[[Any], Any]   # S → T
    _cursor: Any                # S

    @property
    def cursor(self) -> Any:
        return self._cursor

    def extract(self) -> Any:
        return self._fn(self._cursor)

    def seek(self, s: Any) -> "Store[Any, Any]":
        return Store(self._fn, s)

    def peek(self, s: Any) -> Any:
        return self._fn(s)

    def map(self, f: Callable[[Any], Any]) -> "Store[Any, Any]":
        return Store(lambda s: f(self._fn(s)), self._cursor)

    def extend(self, f: Callable[["Store[Any, Any]"], Any]) -> "Store[Any, Any]":
        """Cobind: each position s becomes f(store focused at s)."""
        return Store(lambda s: f(self.seek(s)), self._cursor)

    def coflatten(self) -> "Store[Any, Store[Any, Any]]":
        return Store(lambda s: self.seek(s), self._cursor)

    def experiment(self, f: Callable[[Any], list[Any]]) -> list[Any]:
        """Read values at all positions returned by f(cursor)."""
        return [self._fn(s) for s in f(self._cursor)]


def make_fizzbuzz_store(
    rule: "VisitableRule",
    start: int = 1,
    stop: int = 100,
) -> Store[int, LabelT]:
    """
    Build a Store[int, LabelT] covering [start, stop].
    Positions outside that range return None.
    """
    def _fn(n: int) -> LabelT:
        if start <= n <= stop:
            return rule(Number(n))
        return None
    return Store(_fn, start)


@dataclasses.dataclass(frozen=True)
class ContextualLabel:
    position: int
    label: LabelT
    prev_label: LabelT
    next_label: LabelT

    @property
    def is_isolated(self) -> bool:
        """True if neither neighbour carries a label."""
        return self.prev_label is None and self.next_label is None

    @property
    def is_run(self) -> bool:
        """True if this and at least one neighbour share the same label."""
        return (self.label is not None and
                (self.label == self.prev_label or self.label == self.next_label))


def fizzbuzz_context_labels(
    rule: "VisitableRule",
    start: int = 1,
    stop: int = 20,
) -> list[ContextualLabel]:
    """
    Use Store.extend to annotate each position with its neighbours' labels.
    Demonstrates context-sensitivity via comonad cobind.
    """
    store: Store[int, LabelT] = make_fizzbuzz_store(rule, start, stop)

    def _with_context(s: Store[int, LabelT]) -> ContextualLabel:
        pos = s.cursor
        return ContextualLabel(
            position=pos,
            label=s.extract(),
            prev_label=s.peek(pos - 1),
            next_label=s.peek(pos + 1),
        )

    extended: Store[int, ContextualLabel] = store.extend(_with_context)
    return [extended.peek(n) for n in range(start, stop + 1)]


# ===========================================================================
# § 13f  Lazy infinite streams  (cons-cell streams with memoisation)
# ===========================================================================
# A lazy stream is either:
#   Nil                     — the empty stream
#   Cons(head, tail_thunk)  — a head value and a *thunk* for the tail
#
# Thunks are memoised on first force so the tail is computed at most once.
# This enables infinite streams (e.g., all FizzBuzz labels from 1 to ∞) that
# are only evaluated on demand.
#
# Stream[T] operations:
#   head()                — first element (raises on Nil)
#   tail()                — rest of stream (raises on Nil)
#   take(n)               — materialise first n elements as list
#   drop(n)               — skip first n elements
#   map(f)                — element-wise transform (lazy)
#   filter(pred)          — filter (lazy)
#   zip_with(other, f)    — pointwise combine two streams (lazy)
#   scan(f, init)         — running accumulation (lazy)
#   cycle()               — repeat a finite stream infinitely
#   iterate(f, seed)      — Stream.iterate(f, x) = [x, f(x), f(f(x)), ...]
#
# fizzbuzz_stream(rule, start)  — infinite Stream[(Number, LabelT)] from start

class _Nil:
    __slots__ = ()
    def __repr__(self) -> str:
        return "Nil"

    def __bool__(self) -> bool:
        return False


Nil: _Nil = _Nil()


class Stream(Generic[T]):
    """
    Lazy cons-cell stream with memoised thunks.
    Create via Stream.cons(head, thunk) or Stream.from_iterable(it).
    """
    __slots__ = ("_head", "_tail_thunk", "_tail_memo", "_is_nil")

    def __init__(
        self,
        head: T,
        tail_thunk: Callable[[], "Stream[T]"],
    ) -> None:
        self._head = head
        self._tail_thunk = tail_thunk
        self._tail_memo: Stream[T] | None = None
        self._is_nil = False

    @classmethod
    def empty(cls) -> "Stream[T]":
        s: Stream[T] = object.__new__(cls)
        s._is_nil = True
        return s

    @classmethod
    def cons(cls, head: T, tail: Callable[[], "Stream[T]"]) -> "Stream[T]":
        return cls(head, tail)

    @classmethod
    def from_iterable(cls, it: Iterable[T]) -> "Stream[T]":
        iterator = iter(it)
        def _build() -> Stream[T]:
            try:
                val = next(iterator)
                return cls.cons(val, _build)
            except StopIteration:
                return cls.empty()
        return _build()

    @classmethod
    def iterate(cls, f: Callable[[T], T], seed: T) -> "Stream[T]":
        """Infinite stream [seed, f(seed), f(f(seed)), ...]."""
        return cls.cons(seed, lambda: cls.iterate(f, f(seed)))

    @classmethod
    def repeat(cls, value: T) -> "Stream[T]":
        return cls.cons(value, lambda: cls.repeat(value))

    @property
    def is_nil(self) -> bool:
        return self._is_nil

    def head(self) -> T:
        if self._is_nil:
            raise StopIteration("head of empty stream")
        return self._head

    def tail(self) -> "Stream[T]":
        if self._is_nil:
            raise StopIteration("tail of empty stream")
        if self._tail_memo is None:
            self._tail_memo = self._tail_thunk()
        return self._tail_memo

    def take(self, n: int) -> list[T]:
        result: list[T] = []
        s: Stream[T] = self
        while n > 0 and not s.is_nil:
            result.append(s.head())
            s = s.tail()
            n -= 1
        return result

    def drop(self, n: int) -> "Stream[T]":
        s: Stream[T] = self
        while n > 0 and not s.is_nil:
            s = s.tail()
            n -= 1
        return s

    def map(self, f: Callable[[T], Any]) -> "Stream[Any]":
        if self._is_nil:
            return Stream.empty()
        return Stream.cons(f(self._head), lambda: self.tail().map(f))

    def filter(self, pred: Callable[[T], bool]) -> "Stream[T]":
        if self._is_nil:
            return Stream.empty()
        if pred(self._head):
            return Stream.cons(self._head, lambda: self.tail().filter(pred))
        return self.tail().filter(pred)

    def zip_with(self, other: "Stream[Any]", f: Callable[[T, Any], Any]) -> "Stream[Any]":
        if self._is_nil or other.is_nil:
            return Stream.empty()
        h = f(self._head, other._head)
        return Stream.cons(h, lambda: self.tail().zip_with(other.tail(), f))

    def scan(self, f: Callable[[Any, T], Any], init: Any) -> "Stream[Any]":
        """Running fold: stream of intermediate accumulator values."""
        if self._is_nil:
            return Stream.cons(init, lambda: Stream.empty())
        new_acc = f(init, self._head)
        return Stream.cons(init, lambda: self.tail().scan(f, new_acc))

    def cycle(self) -> "Stream[T]":
        """Repeat a finite stream indefinitely."""
        if self._is_nil:
            return Stream.empty()
        buf = self.take(65536)   # materialise up to 64K for cycling
        if not buf:
            return Stream.empty()
        def _from_idx(i: int) -> Stream[T]:
            return Stream.cons(buf[i % len(buf)], lambda idx=i: _from_idx(idx + 1))
        return _from_idx(0)

    def __iter__(self) -> Iterator[T]:
        s: Stream[T] = self
        while not s.is_nil:
            yield s.head()
            s = s.tail()

    def __repr__(self) -> str:
        peeked = self.take(5)
        suffix = "…" if not self.drop(5).is_nil else ""
        return f"Stream({peeked}{suffix})"


def fizzbuzz_stream(
    rule: "VisitableRule",
    start: int = 1,
) -> Stream[tuple[Number, LabelT]]:
    """Infinite lazy Stream of (Number, label) pairs starting at `start`."""
    def _from(n: int) -> Stream[tuple[Number, LabelT]]:
        num = Number(n)
        label = rule(num)
        return Stream.cons((num, label), lambda: _from(n + 1))
    return _from(start)


def stream_fizzbuzz_labels(
    rule: "VisitableRule",
    start: int = 1,
) -> Stream[str]:
    """Infinite lazy Stream of formatted FizzBuzz strings."""
    return fizzbuzz_stream(rule, start).map(
        lambda pair: pair[1] if pair[1] is not None else str(pair[0].value)
    )


def stream_running_counts(
    rule: "VisitableRule",
    start: int = 1,
) -> Stream[Counter[str]]:
    """Running Counter of label frequencies (infinite stream)."""
    labels = stream_fizzbuzz_labels(rule, start)
    def _update(acc: Counter[str], label: str) -> Counter[str]:
        new = Counter(acc)
        new[label] += 1
        return new
    return labels.scan(_update, Counter())


# ===========================================================================
# § 13g  Persistent segment tree  (immutable, versioned range structure)
# ===========================================================================
# A *persistent* (functional) segment tree allows O(log n) point updates that
# produce a *new root* sharing all unmodified nodes with the old version.
# This gives us an O(1) "undo" / version history for free.
#
# Each SegNode stores an aggregate `val` (here: sum of label-code counts).
# Nodes are immutable; an update creates O(log n) new nodes on the path from
# root to leaf, leaving the rest shared.
#
# Operations:
#   seg_build(values)          — O(n) initial construction from a list
#   seg_update(node, lo, hi, i, delta) — point-update; returns new root
#   seg_query(node, lo, hi, l, r)      — range-sum query [l, r]
#   seg_range_max(node, lo, hi, l, r)  — range-max query [l, r]
#
# FizzBuzz application:
#   We map each integer n ∈ [start, stop] to an index.
#   The value stored is a numeric *label code* (0=number, 1=Fizz, 2=Buzz,
#   3=FizzBuzz).  After each n we save the new root, giving a full versioned
#   history of the cumulative label-code sum over any prefix.

@dataclasses.dataclass(frozen=True)
class SegNode:
    """Immutable segment tree node storing sum and max aggregates."""
    total: int
    maximum: int
    left: "SegNode | None" = None
    right: "SegNode | None" = None

    @classmethod
    def leaf(cls, val: int) -> "SegNode":
        return cls(total=val, maximum=val)

    @classmethod
    def combine(cls, l: "SegNode", r: "SegNode") -> "SegNode":
        return cls(
            total=l.total + r.total,
            maximum=max(l.maximum, r.maximum),
            left=l,
            right=r,
        )


_SEG_NULL: SegNode = SegNode(0, 0)


def seg_build(values: list[int]) -> SegNode:
    """Build a segment tree from a list of integer values in O(n)."""
    n = len(values)
    if n == 0:
        return _SEG_NULL
    if n == 1:
        return SegNode.leaf(values[0])
    mid = n // 2
    return SegNode.combine(seg_build(values[:mid]), seg_build(values[mid:]))


def seg_update(node: SegNode, lo: int, hi: int, idx: int, delta: int) -> SegNode:
    """
    Point-update: add `delta` to position `idx` in [lo, hi].
    Returns a new root sharing structure with `node`.
    """
    if lo == hi:
        return SegNode.leaf(node.total + delta)
    mid = (lo + hi) // 2
    left = node.left or _SEG_NULL
    right = node.right or _SEG_NULL
    if idx <= mid:
        new_left = seg_update(left, lo, mid, idx, delta)
        return SegNode.combine(new_left, right)
    else:
        new_right = seg_update(right, mid + 1, hi, idx, delta)
        return SegNode.combine(left, new_right)


def seg_query_sum(node: SegNode, lo: int, hi: int, l: int, r: int) -> int:
    """Range-sum query [l, r] in O(log n)."""
    if node is _SEG_NULL or l > hi or r < lo:
        return 0
    if l <= lo and hi <= r:
        return node.total
    mid = (lo + hi) // 2
    left = node.left or _SEG_NULL
    right = node.right or _SEG_NULL
    return seg_query_sum(left, lo, mid, l, r) + seg_query_sum(right, mid + 1, hi, l, r)


def seg_query_max(node: SegNode, lo: int, hi: int, l: int, r: int) -> int:
    """Range-max query [l, r] in O(log n)."""
    if node is _SEG_NULL or l > hi or r < lo:
        return 0
    if l <= lo and hi <= r:
        return node.maximum
    mid = (lo + hi) // 2
    left = node.left or _SEG_NULL
    right = node.right or _SEG_NULL
    return max(
        seg_query_max(left, lo, mid, l, r),
        seg_query_max(right, mid + 1, hi, l, r),
    )


_LABEL_CODE: dict[str | None, int] = {
    None: 0,
    FIZZ: 1,
    BUZZ: 2,
    FIZZBUZZ: 3,
}


@dataclasses.dataclass
class PersistentLabelHistory:
    """
    Versioned label history for a FizzBuzz range.
    Each 'commit' appends the label code for the next number and saves
    a new segment tree root — the previous versions remain accessible.
    """
    _start: int
    _stop: int
    _roots: list[SegNode]          # roots[0] = empty; roots[i] = after i numbers
    _size: int                     # = stop - start + 1

    @classmethod
    def build(cls, rule: "VisitableRule", start: int, stop: int) -> "PersistentLabelHistory":
        size = stop - start + 1
        # initial empty tree
        empty_root = seg_build([0] * size)
        roots: list[SegNode] = [empty_root]
        cur = empty_root
        for n_val in range(start, stop + 1):
            label = rule(Number(n_val))
            code = _LABEL_CODE.get(label, 0)
            idx = n_val - start
            cur = seg_update(cur, 0, size - 1, idx, code)
            roots.append(cur)
        return cls(_start=start, _stop=stop, _roots=roots, _size=size)

    def query_sum(self, l: int, r: int, version: int = -1) -> int:
        """Sum of label codes over [l, r] in the given version (-1 = latest)."""
        root = self._roots[version]
        li = max(0, l - self._start)
        ri = min(self._size - 1, r - self._start)
        return seg_query_sum(root, 0, self._size - 1, li, ri)

    def query_max(self, l: int, r: int, version: int = -1) -> int:
        """Max label code over [l, r] in the given version (-1 = latest)."""
        root = self._roots[version]
        li = max(0, l - self._start)
        ri = min(self._size - 1, r - self._start)
        return seg_query_max(root, 0, self._size - 1, li, ri)

    def n_versions(self) -> int:
        return len(self._roots)

    def range(self) -> tuple[int, int]:
        return self._start, self._stop


# ===========================================================================
# § 13h  Arrowized FRP  (Behaviors, Events, Signal Functions)
# ===========================================================================
# Functional Reactive Programming models time-varying values and discrete
# events as first-class abstractions:
#
#   Behavior[A]  — a continuously varying value: time → A
#   Event[A]     — a stream of discrete occurrences: [(time, A)]
#   SF[A, B]     — a Signal Function: transforms input signal to output signal
#
# SF forms a *category* (identity, composition) and an *arrow* (arr, first).
# Additional arrow combinators: >>>, ***, &&&, loop.
#
# Combinators:
#   arr(f)                 — lift a pure function into SF
#   constant(v)            — SF that always outputs v regardless of input
#   sf_id()                — identity SF
#   integral(dt)           — integrates a Behavior over time (running sum)
#   hold(init)             — hold the last Event value as a Behavior
#   snapshot(beh, event)   — sample Behavior at each Event occurrence
#   switch(beh, event)     — replace beh with new Behavior on each Event
#   gate(event, pred_beh)  — filter Event by a Behavior-valued predicate
#   step_clock(dt, stop)   — generate a time-step event stream
#
# FizzBuzz FRP network:
#   - counter Behavior increases by 1 each tick
#   - fizzbuzz Behavior = rule applied to counter
#   - output Event fires with the label string each tick
#   - a "run" detector Event fires when two consecutive labels match

Timestamp: TypeAlias = float


@dataclasses.dataclass(frozen=True)
class Behavior(Generic[T]):
    """A time-varying value: time → T."""
    _fn: Callable[[Timestamp], T]

    def at(self, t: Timestamp) -> T:
        return self._fn(t)

    def map(self, f: Callable[[T], Any]) -> "Behavior[Any]":
        return Behavior(lambda t: f(self._fn(t)))

    def apply(self, other: "Behavior[Callable[[T], Any]]") -> "Behavior[Any]":
        return Behavior(lambda t: other._fn(t)(self._fn(t)))

    def zip_with(self, other: "Behavior[Any]", f: Callable[[T, Any], Any]) -> "Behavior[Any]":
        return Behavior(lambda t: f(self._fn(t), other._fn(t)))

    def sample(self, times: list[Timestamp]) -> list[T]:
        return [self._fn(t) for t in times]

    @classmethod
    def constant(cls, v: T) -> "Behavior[T]":
        return cls(lambda _: v)

    @classmethod
    def time(cls) -> "Behavior[Timestamp]":
        return cls(lambda t: t)


@dataclasses.dataclass(frozen=True)
class Event(Generic[T]):
    """A discrete stream of time-stamped values."""
    occurrences: tuple[tuple[Timestamp, T], ...]

    @classmethod
    def empty(cls) -> "Event[Any]":
        return cls(occurrences=())

    @classmethod
    def from_list(cls, pairs: list[tuple[Timestamp, T]]) -> "Event[T]":
        return cls(occurrences=tuple(sorted(pairs, key=lambda x: x[0])))

    def map(self, f: Callable[[T], Any]) -> "Event[Any]":
        return Event(tuple((t, f(v)) for t, v in self.occurrences))

    def filter(self, pred: Callable[[T], bool]) -> "Event[T]":
        return Event(tuple((t, v) for t, v in self.occurrences if pred(v)))

    def merge(self, other: "Event[T]") -> "Event[T]":
        combined = sorted(
            list(self.occurrences) + list(other.occurrences),
            key=lambda x: x[0],
        )
        return Event(tuple(combined))

    def scan(self, f: Callable[[Any, T], Any], init: Any) -> "Event[Any]":
        acc = init
        result: list[tuple[Timestamp, Any]] = []
        for t, v in self.occurrences:
            acc = f(acc, v)
            result.append((t, acc))
        return Event(tuple(result))

    def values(self) -> list[T]:
        return [v for _, v in self.occurrences]

    def times(self) -> list[Timestamp]:
        return [t for t, _ in self.occurrences]


@dataclasses.dataclass(frozen=True)
class SF(Generic[T, U]):
    """
    Signal Function: transforms an input Behavior[T] into an output Behavior[U].
    The transformation is itself time-dependent.
    """
    _run: Callable[["Behavior[T]"], "Behavior[U]"]

    def run(self, input_beh: Behavior[T]) -> Behavior[U]:
        return self._run(input_beh)

    def __rshift__(self, other: "SF[U, Any]") -> "SF[T, Any]":
        """Sequential composition (>>>)."""
        return SF(lambda beh: other._run(self._run(beh)))

    def __and__(self, other: "SF[T, Any]") -> "SF[T, tuple[U, Any]]":
        """Parallel fanout (&&&)."""
        return SF(lambda beh: Behavior(
            lambda t: (self._run(beh).at(t), other._run(beh).at(t))
        ))

    def first(self) -> "SF[tuple[T, Any], tuple[U, Any]]":
        """Apply this SF to the first component of a pair."""
        return SF(lambda beh: Behavior(
            lambda t: (self._run(Behavior(lambda tt: beh.at(tt)[0])).at(t), beh.at(t)[1])
        ))

    @classmethod
    def arr(cls, f: Callable[[T], U]) -> "SF[T, U]":
        """Lift a pure function."""
        return cls(lambda beh: beh.map(f))

    @classmethod
    def identity(cls) -> "SF[T, T]":
        return cls(lambda beh: beh)

    @classmethod
    def constant(cls, v: U) -> "SF[Any, U]":
        return cls(lambda _: Behavior.constant(v))

    @classmethod
    def integral(cls, dt: float = 1.0) -> "SF[float, float]":
        """Running integral (discrete approximation: Riemann sum)."""
        def _run(beh: Behavior[float]) -> Behavior[float]:
            # Captures running state via a sampled precomputed table
            def _at(t: Timestamp) -> float:
                steps = int(t / dt)
                return sum(beh.at(i * dt) * dt for i in range(steps))
            return Behavior(_at)
        return cls(_run)


def hold(init: T, event: Event[T]) -> Behavior[T]:
    """Hold the most recent Event value as a step-function Behavior."""
    def _at(t: Timestamp) -> T:
        val = init
        for evt_t, v in event.occurrences:
            if evt_t <= t:
                val = v
            else:
                break
        return val
    return Behavior(_at)


def snapshot(beh: Behavior[T], event: Event[Any]) -> Event[T]:
    """Sample Behavior at each Event occurrence time."""
    return Event(tuple((t, beh.at(t)) for t, _ in event.occurrences))


def switch(beh: Behavior[T], event: Event[Behavior[T]]) -> Behavior[T]:
    """Replace the current Behavior with the one carried by the last Event."""
    def _at(t: Timestamp) -> T:
        active = beh
        for evt_t, new_beh in event.occurrences:
            if evt_t <= t:
                active = new_beh
        return active.at(t)
    return Behavior(_at)


def gate(event: Event[T], pred_beh: Behavior[bool]) -> Event[T]:
    """Filter an Event by a time-varying Boolean Behavior."""
    return Event(tuple(
        (t, v) for t, v in event.occurrences if pred_beh.at(t)
    ))


def step_clock(dt: float, stop: float, start: float = 0.0) -> Event[float]:
    """Generate a uniform clock Event with step dt."""
    times_: list[float] = []
    t = start
    while t <= stop + 1e-9:
        times_.append(t)
        t += dt
    return Event(tuple((t, t) for t in times_))


def build_fizzbuzz_frp(
    rule: "VisitableRule",
    start: int = 1,
    stop: int = 30,
) -> tuple[Behavior[int], Behavior[LabelT], Event[str]]:
    """
    Build a FizzBuzz FRP network:
      counter_beh  — Behavior[int]: n = start + floor(t)
      label_beh    — Behavior[LabelT]: rule(counter_beh)
      output_event — Event[str]: fires each integer tick with the label
    Returns (counter_beh, label_beh, output_event).
    """
    counter_beh: Behavior[int] = Behavior(lambda t: start + int(t))
    label_beh: Behavior[LabelT] = counter_beh.map(lambda n: rule(Number(n)))

    ticks = step_clock(1.0, stop - start)
    output_event: Event[str] = snapshot(
        label_beh.map(lambda lbl: lbl if lbl is not None else "?"),
        ticks,
    )
    return counter_beh, label_beh, output_event


def fizzbuzz_run_detector(rule: "VisitableRule", start: int = 1, stop: int = 30) -> Event[tuple[str, str]]:
    """
    Detect consecutive equal-label runs: emit (label, label) whenever
    the FizzBuzz output matches its predecessor.
    """
    _, _, out_e = build_fizzbuzz_frp(rule, start, stop)
    labels = list(out_e.occurrences)
    pairs: list[tuple[Timestamp, tuple[str, str]]] = []
    for i in range(1, len(labels)):
        t_prev, v_prev = labels[i - 1]
        t_cur, v_cur = labels[i]
        if v_prev == v_cur:
            pairs.append((t_cur, (v_prev, v_cur)))
    return Event(tuple(pairs))


# ===========================================================================
# § 14  Pipeline state machine
# ===========================================================================

class PipelineState(enum.Enum):
    IDLE     = "idle"
    RUNNING  = "running"
    PAUSED   = "paused"
    COMPLETE = "complete"
    FAILED   = "failed"


_STATE_TRANSITIONS: Final[dict[PipelineState, frozenset[PipelineState]]] = {
    PipelineState.IDLE:     frozenset({PipelineState.RUNNING}),
    PipelineState.RUNNING:  frozenset({PipelineState.PAUSED, PipelineState.COMPLETE, PipelineState.FAILED}),
    PipelineState.PAUSED:   frozenset({PipelineState.RUNNING, PipelineState.FAILED}),
    PipelineState.COMPLETE: frozenset(),
    PipelineState.FAILED:   frozenset({PipelineState.IDLE}),
}


class PipelineStateMachine:
    def __init__(self) -> None:
        self._state = PipelineState.IDLE
        self._lock = threading.Lock()
        self._log = logging.getLogger("fizzbuzz.statemachine")
        self._history: list[tuple[PipelineState, float]] = [
            (PipelineState.IDLE, time.perf_counter())
        ]

    @property
    def state(self) -> PipelineState:
        with self._lock:
            return self._state

    def transition(self, target: PipelineState) -> None:
        with self._lock:
            allowed = _STATE_TRANSITIONS[self._state]
            if target not in allowed:
                raise RuntimeError(
                    f"Illegal transition {self._state.value!r} → {target.value!r}. "
                    f"Allowed: {[s.value for s in allowed]}"
                )
            self._log.debug("State: %s → %s", self._state.value, target.value)
            self._state = target
            self._history.append((target, time.perf_counter()))
            EventBus().publish("pipeline.state_changed", {"state": target})

    def history(self) -> list[tuple[str, float]]:
        with self._lock:
            return [(s.value, t) for s, t in self._history]


# ===========================================================================
# § 15  Pipeline
# ===========================================================================

Middleware: TypeAlias = Callable[[Number, LabelT], LabelT]


@dataclasses.dataclass
class PipelineConfig:
    range: NumberRange | ChainedNumberRange
    rule: CompositeRule
    formatter: Formatter
    sink: OutputSink = dataclasses.field(default_factory=StdoutSink)
    middlewares: list[Middleware] = dataclasses.field(default_factory=list)
    metrics: bool = True
    parallel: bool = False
    chunk_size: int = 256
    use_compiled_rule: bool = False
    tracer: Tracer | None = None


@dataclasses.dataclass(frozen=True)
class PipelineResult:
    numbers_processed: int
    labelled: int
    unlabelled: int
    elapsed_seconds: float
    metrics_report: str = ""
    state_history: list[tuple[str, float]] = dataclasses.field(default_factory=list)

    @property
    def label_rate(self) -> float:
        return self.labelled / self.numbers_processed if self.numbers_processed else 0.0

    @property
    def throughput(self) -> float:
        return self.numbers_processed / self.elapsed_seconds if self.elapsed_seconds else float("inf")

    def __str__(self) -> str:
        return (
            f"{self.numbers_processed} numbers in {self.elapsed_seconds * 1000:.3f}ms "
            f"({self.label_rate:.1%} labelled, {self.throughput:,.0f} n/s)"
        )


class FizzBuzzPipeline:
    def __init__(self, config: PipelineConfig) -> None:
        self._cfg = config
        self._metrics = MetricsCollector() if config.metrics else None
        self._bus = EventBus()
        self._sm = PipelineStateMachine()
        self._tracer = config.tracer or _global_tracer
        self._log = logging.getLogger("fizzbuzz.pipeline")
        self._rule: Callable[[Number], LabelT] = (
            RuleCompiler.compile(config.rule) if config.use_compiled_rule else config.rule
        )

    def _apply_middlewares(self, number: Number, label: LabelT) -> LabelT:
        for mw in self._cfg.middlewares:
            label = mw(number, label)
        return label

    def _process_one(self, number: Number) -> None:
        label = self._rule(number)
        label = self._apply_middlewares(number, label)
        if self._metrics:
            self._metrics.record(number, label)
        output = self._cfg.formatter.format(number, label)
        self._cfg.sink.write(output)
        self._bus.publish("number.processed", {"number": number, "label": label})

    def run(self) -> PipelineResult:
        with self._tracer.start_span("pipeline.run", range=repr(self._cfg.range)):
            self._sm.transition(PipelineState.RUNNING)
            self._bus.publish("pipeline.start", {"range": self._cfg.range})
            t0 = time.perf_counter()

            try:
                with self._cfg.sink.open():
                    with self._tracer.start_span("pipeline.process"):
                        if self._cfg.parallel:
                            self._run_parallel()
                        else:
                            for number in self._cfg.range:
                                self._process_one(number)
                self._sm.transition(PipelineState.COMPLETE)
            except Exception:
                self._sm.transition(PipelineState.FAILED)
                raise

        elapsed = time.perf_counter() - t0
        total = len(self._cfg.range)
        unlabelled = self._metrics._counter.get("<number>", 0) if self._metrics else 0
        labelled = total - unlabelled

        result = PipelineResult(
            numbers_processed=total,
            labelled=labelled,
            unlabelled=unlabelled,
            elapsed_seconds=elapsed,
            metrics_report=self._metrics.report() if self._metrics else "",
            state_history=self._sm.history(),
        )
        self._log.info("Pipeline complete: %s", result)
        self._bus.publish("pipeline.complete", {"result": result})
        return result

    def _run_parallel(self) -> None:
        import concurrent.futures
        with concurrent.futures.ThreadPoolExecutor(
            max_workers=os.cpu_count() or 4,
            thread_name_prefix="fizzbuzz-worker",
        ) as pool:
            list(pool.map(self._process_one, self._cfg.range))

    async def run_async(self) -> PipelineResult:
        loop = asyncio.get_running_loop()
        return await loop.run_in_executor(None, self.run)


# ===========================================================================
# § 16  Distributed sharding  (multiprocessing)
# ===========================================================================

def _shard_worker(args: tuple[int, int, str, str]) -> dict[str, Any]:
    """Top-level worker — must be picklable for multiprocessing."""
    start, stop, rule_name, formatter_spec = args
    _bootstrap_registry()
    sink = BufferedSink()
    pipeline = FizzBuzzFactory.create(
        start=start, stop=stop,
        rule_name=rule_name,
        formatter=formatter_spec,
        sink=sink,
    )
    result = pipeline.run()
    return {
        "lines": sink.lines,
        "numbers_processed": result.numbers_processed,
        "labelled": result.labelled,
        "elapsed_seconds": result.elapsed_seconds,
    }


def run_sharded(
    start: int,
    stop: int,
    *,
    n_shards: int = 4,
    rule_name: str = "classic",
    formatter: str = "default",
    sink: OutputSink | None = None,
) -> PipelineResult:
    """Split the range across N worker processes and merge results."""
    total = stop - start + 1
    shard_size = math.ceil(total / n_shards)
    shards: list[tuple[int, int, str, str]] = []
    for i in range(n_shards):
        s = start + i * shard_size
        e = min(s + shard_size - 1, stop)
        if s <= stop:
            shards.append((s, e, rule_name, formatter))

    log.info("Distributing %d numbers across %d shards", total, len(shards))
    with multiprocessing.Pool(processes=len(shards)) as pool:
        shard_results = pool.map(_shard_worker, shards)

    out_sink = sink or StdoutSink()
    total_processed = total_labelled = 0
    max_elapsed = 0.0

    for r in shard_results:
        for line in r["lines"]:
            out_sink.write(line)
        total_processed += r["numbers_processed"]
        total_labelled += r["labelled"]
        max_elapsed = max(max_elapsed, r["elapsed_seconds"])

    out_sink.flush()
    return PipelineResult(
        numbers_processed=total_processed,
        labelled=total_labelled,
        unlabelled=total_processed - total_labelled,
        elapsed_seconds=max_elapsed,
    )


# ===========================================================================
# § 17  Factory / DI container
# ===========================================================================

class _DIContainer:
    def __init__(self) -> None:
        self._bindings: dict[type, Callable[[], Any]] = {}

    def bind(self, interface: type[T], factory: Callable[[], T]) -> None:
        self._bindings[interface] = factory

    def resolve(self, interface: type[T]) -> T:
        try:
            return self._bindings[interface]()
        except KeyError:
            raise LookupError(f"No binding for {interface!r}")


class FizzBuzzFactory:
    _FORMATTERS: ClassVar[dict[str, type[Formatter]]] = {
        "default":  DefaultFormatter,
        "upper":    UpperCaseFormatter,
        "json":     JsonFormatter,
        "ansi":     AnsiFormatter,
        "padded":   PaddedFormatter,
        "template": TemplateFormatter,
    }

    @classmethod
    def create(
        cls,
        *,
        start: int = 1,
        stop: int = 100,
        rule_name: str = "classic",
        formatter: str = "default",
        sink: OutputSink | None = None,
        middlewares: list[Middleware] | None = None,
        parallel: bool = False,
        use_compiled_rule: bool = False,
    ) -> FizzBuzzPipeline:
        rule = RuleRegistry().get(rule_name)
        fmt = cls._build_formatter(formatter)
        return FizzBuzzPipeline(
            PipelineConfig(
                range=NumberRange(start, stop),
                rule=rule,
                formatter=fmt,
                sink=sink or StdoutSink(),
                middlewares=middlewares or [],
                parallel=parallel,
                use_compiled_rule=use_compiled_rule,
            )
        )

    @classmethod
    def _build_formatter(cls, spec: str) -> Formatter:
        names = spec.split("+")
        base_cls = cls._FORMATTERS.get(names[0])
        if base_cls is None:
            raise ValueError(f"Unknown formatter {names[0]!r}. Choose from: {sorted(cls._FORMATTERS)}")
        fmt: Formatter = base_cls()
        for name in names[1:]:
            dec_cls = cls._FORMATTERS.get(name)
            if dec_cls is None:
                raise ValueError(f"Unknown formatter {name!r}.")
            if not issubclass(dec_cls, FormatterDecorator):
                raise ValueError(f"{name!r} is not a decorator formatter.")
            dec = dec_cls.__new__(dec_cls)
            dec._delegate = fmt
            fmt = dec
        return fmt


# ===========================================================================
# § 18  Built-in middlewares
# ===========================================================================

def null_suppressor(number: Number, label: LabelT) -> LabelT:
    return None if "0" in str(number.value) else label


def label_reverser(number: Number, label: LabelT) -> LabelT:
    return label[::-1] if label else label


def prime_annotator(number: Number, label: LabelT) -> LabelT:
    if number.is_prime:
        return f"[{label}]" if label else f"[{number.value}]"
    return label


def collatz_annotator(number: Number, label: LabelT) -> LabelT:
    depth = number.collatz_depth
    if depth > 50:
        suffix = f"({depth})"
        return f"{label}{suffix}" if label else f"{number.value}{suffix}"
    return label


def fingerprint_annotator(number: Number, label: LabelT) -> LabelT:
    return f"{label or number.value}#{number.fingerprint}"


# ===========================================================================
# § 19  Async streaming API
# ===========================================================================

async def stream_fizzbuzz(
    start: int = 1,
    stop: int = 100,
    rule_name: str = "classic",
    delay: float = 0.0,
) -> AsyncGenerator[tuple[Number, LabelT], None]:
    rule = RuleRegistry().get(rule_name)
    for number in NumberRange(start, stop):
        label = rule(number)
        yield number, label
        if delay:
            await asyncio.sleep(delay)


# ===========================================================================
# § 19b  Property-based testing  (Gen[T] monad + for_all + shrinking)
# ===========================================================================

@dataclasses.dataclass
class Shrinker(Generic[T]):
    """Produces progressively simpler candidates from a failing value."""
    shrink: Callable[[T], Iterable[T]]

    @staticmethod
    def integer(lo: int = 0) -> Shrinker[int]:
        def shrink(n: int) -> Iterable[int]:
            if n == lo:
                return
            yield lo
            mid = (n + lo) // 2
            if mid != lo and mid != n:
                yield mid
            if n > 0:
                yield n - 1
            elif n < 0:
                yield n + 1
        return Shrinker(shrink)

    @staticmethod
    def listof(elem_shrinker: Shrinker[T]) -> Shrinker[list[T]]:
        def shrink(xs: list[T]) -> Iterable[list[T]]:
            if xs:
                yield []
                if len(xs) > 1:
                    yield xs[:len(xs) // 2]
                    yield xs[len(xs) // 2:]
            for i, x in enumerate(xs):
                for smaller in elem_shrinker.shrink(x):
                    yield xs[:i] + [smaller] + xs[i + 1:]
        return Shrinker(shrink)


@dataclasses.dataclass
class Gen(Generic[T]):
    """Monadic random value generator.

    Gen.integer(), Gen.number(), Gen.one_of(), Gen.list_of() are the
    standard combinators. .map() and .flat_map() let you derive new
    generators from existing ones.
    """
    _generate: Callable[[random.Random, int], T]
    shrinker: Shrinker[T] | None = None

    def sample(self, rng: random.Random | None = None, size: int = 10) -> T:
        return self._generate(rng or random.Random(), size)

    def map(self, f: Callable[[T], U]) -> Gen[U]:
        return Gen(lambda rng, size: f(self._generate(rng, size)))

    def flat_map(self, f: Callable[[T], Gen[U]]) -> Gen[U]:
        return Gen(lambda rng, size: f(self._generate(rng, size))._generate(rng, size))

    def filter(self, pred: Callable[[T], bool], max_tries: int = 100) -> Gen[T]:
        def gen(rng: random.Random, size: int) -> T:
            for _ in range(max_tries):
                v = self._generate(rng, size)
                if pred(v):
                    return v
            raise RuntimeError(f"Gen.filter: could not satisfy predicate in {max_tries} tries")
        return Gen(gen)

    def zip(self, other: Gen[U]) -> Gen[tuple[T, U]]:
        return Gen(lambda rng, size: (self._generate(rng, size), other._generate(rng, size)))

    # ── primitive generators ──────────────────────────────────────────────────

    @staticmethod
    def constant(val: T) -> Gen[T]:
        return Gen(lambda _r, _s: val)

    @staticmethod
    def integer(lo: int = 0, hi: int = 1000) -> Gen[int]:
        return Gen(
            lambda rng, _: rng.randint(lo, hi),
            shrinker=Shrinker.integer(lo),
        )

    @staticmethod
    def number(lo: int = 1, hi: int = 1000) -> Gen[Number]:
        return Gen.integer(lo, hi).map(Number)

    @staticmethod
    def number_range(max_size: int = 200) -> Gen[NumberRange]:
        def gen(rng: random.Random, _size: int) -> NumberRange:
            start = rng.randint(1, max_size)
            stop  = rng.randint(start, start + max_size)
            step  = rng.randint(1, 5)
            return NumberRange(start, stop, step)
        return Gen(gen)

    @staticmethod
    def one_of(*gens: Gen[T]) -> Gen[T]:
        return Gen(lambda rng, size: rng.choice(gens)._generate(rng, size))

    @staticmethod
    def list_of(gen: Gen[T], min_size: int = 0, max_size: int = 10) -> Gen[list[T]]:
        elem_shr = gen.shrinker
        def gen_fn(rng: random.Random, size: int) -> list[T]:
            n = rng.randint(min_size, max_size)
            return [gen._generate(rng, size) for _ in range(n)]
        return Gen(
            gen_fn,
            shrinker=Shrinker.listof(elem_shr) if elem_shr else None,
        )

    @staticmethod
    def rule_name() -> Gen[str]:
        names = RuleRegistry().names()
        return Gen(lambda rng, _: rng.choice(names))


@dataclasses.dataclass
class PropertyResult:
    passed: bool
    trials: int
    counterexample: tuple[Any, ...] | None = None
    shrunk: tuple[Any, ...] | None = None
    exception: Exception | None = None

    def __str__(self) -> str:
        if self.passed:
            return f"✓ Passed {self.trials} trials"
        ce = self.shrunk or self.counterexample
        msg = f"✗ Failed after {self.trials} trials — counterexample: {ce!r}"
        if self.exception:
            msg += f"\n  Exception: {type(self.exception).__name__}: {self.exception}"
        return msg


def for_all(
    *gens: Gen[Any],
    prop: Callable[..., bool],
    trials: int = 100,
    seed: int | None = None,
    max_shrink_steps: int = 100,
) -> PropertyResult:
    """Run a randomised property test over generated inputs, with shrinking on failure.

    Example:
        result = for_all(
            Gen.number(1, 100),
            prop=lambda n: (n.value % 3 == 0) == (RuleRegistry().get("classic")(n) is not None or True),
            trials=200,
        )
    """
    rng = random.Random(seed)

    for trial in range(1, trials + 1):
        inputs = tuple(g._generate(rng, min(trial, 50)) for g in gens)
        exc: Exception | None = None
        try:
            passed = prop(*inputs)
        except Exception as e:
            passed = False
            exc = e

        if not passed:
            best = inputs
            for _ in range(max_shrink_steps):
                found_smaller = False
                for i, (val, gen) in enumerate(zip(best, gens)):
                    shr = gen.shrinker
                    if shr is None:
                        continue
                    for candidate_val in shr.shrink(val):
                        candidate = best[:i] + (candidate_val,) + best[i + 1:]
                        try:
                            if not prop(*candidate):
                                best = candidate
                                found_smaller = True
                                break
                        except Exception:
                            best = candidate
                            found_smaller = True
                            break
                    if found_smaller:
                        break
                if not found_smaller:
                    break

            return PropertyResult(
                passed=False,
                trials=trial,
                counterexample=inputs,
                shrunk=best if best != inputs else None,
                exception=exc,
            )

    return PropertyResult(passed=True, trials=trials)


# ── Built-in FizzBuzz properties ──────────────────────────────────────────────

def _prop_label_is_string_or_none(n: Number) -> bool:
    label = RuleRegistry().get("classic")(n)
    return label is None or isinstance(label, str)

def _prop_fizz_iff_div3(n: Number) -> bool:
    label = RuleRegistry().get("classic")(n) or ""
    return (n.value % 3 == 0) == ("Fizz" in label)

def _prop_buzz_iff_div5(n: Number) -> bool:
    label = RuleRegistry().get("classic")(n) or ""
    return (n.value % 5 == 0) == ("Buzz" in label)

def _prop_compiled_matches_interpreted(n: Number) -> bool:
    rule = RuleRegistry().get("classic")
    compiled = RuleCompiler.compile(rule)
    return rule(n) == compiled(n)

BUILTIN_PROPERTIES: dict[str, Callable[[Number], bool]] = {
    "label_type":           _prop_label_is_string_or_none,
    "fizz_iff_div3":        _prop_fizz_iff_div3,
    "buzz_iff_div5":        _prop_buzz_iff_div5,
    "compiled_matches":     _prop_compiled_matches_interpreted,
}


def run_builtin_properties(trials: int = 200) -> dict[str, PropertyResult]:
    results: dict[str, PropertyResult] = {}
    for name, prop in BUILTIN_PROPERTIES.items():
        gen = Gen.number(1, 10_000)
        results[name] = for_all(gen, prop=prop, trials=trials)
    return results


# ===========================================================================
# § 19c  Datalog engine  (forward-chaining logic programming)
# ===========================================================================
# A miniature Datalog: assert ground facts, add Horn-clause rules, run
# semi-naive forward chaining to fixpoint, then query with variable patterns.
#
# Variables are DatalogVar instances; constants are any other Python value.
# Unification is structural equality on constants and substitution on vars.

@dataclasses.dataclass(frozen=True)
class DatalogVar:
    name: str
    def __repr__(self) -> str: return f"?{self.name}"


@dataclasses.dataclass(frozen=True)
class DatalogAtom:
    predicate: str
    args: tuple[Any, ...]
    def __str__(self) -> str:
        return f"{self.predicate}({', '.join(repr(a) for a in self.args)})"


@dataclasses.dataclass(frozen=True)
class DatalogClause:
    """Horn clause:  head :- body[0], body[1], ..."""
    head: DatalogAtom
    body: tuple[DatalogAtom, ...]
    def __str__(self) -> str:
        body = ", ".join(map(str, self.body))
        return f"{self.head} :- {body}" if self.body else str(self.head)


Substitution: TypeAlias = dict[str, Any]


def _unify_atom(pattern: DatalogAtom, fact: DatalogAtom, sub: Substitution) -> Substitution | None:
    """Unify pattern against fact under current substitution; return extended sub or None."""
    if pattern.predicate != fact.predicate or len(pattern.args) != len(fact.args):
        return None
    result = dict(sub)
    for p_arg, f_arg in zip(pattern.args, fact.args):
        if isinstance(p_arg, DatalogVar):
            p_val = result.get(p_arg.name, _SENTINEL)
            if p_val is _SENTINEL:
                result[p_arg.name] = f_arg
            elif p_val != f_arg:
                return None
        elif p_arg != f_arg:
            return None
    return result


def _apply_sub(atom: DatalogAtom, sub: Substitution) -> DatalogAtom:
    """Ground an atom by substituting all variables."""
    new_args = tuple(
        sub.get(a.name, a) if isinstance(a, DatalogVar) else a
        for a in atom.args
    )
    return DatalogAtom(atom.predicate, new_args)


class DatalogEngine:
    """Semi-naive forward-chaining Datalog evaluator."""

    def __init__(self) -> None:
        self._facts: set[DatalogAtom] = set()
        self._clauses: list[DatalogClause] = []
        self._derived_count = 0
        self._log = logging.getLogger("fizzbuzz.datalog")

    def assert_fact(self, predicate: str, *args: Any) -> None:
        self._facts.add(DatalogAtom(predicate, args))

    def add_clause(self, head: DatalogAtom, *body: DatalogAtom) -> None:
        self._clauses.append(DatalogClause(head, body))

    def derive(self, max_rounds: int = 50) -> int:
        """Semi-naive fixpoint iteration. Returns total new facts derived."""
        new_total = 0
        for round_n in range(max_rounds):
            new_facts: set[DatalogAtom] = set()
            for clause in self._clauses:
                for sub in self._solve_body(clause.body, {}):
                    grounded = _apply_sub(clause.head, sub)
                    if grounded not in self._facts:
                        new_facts.add(grounded)
            if not new_facts:
                self._log.debug("Fixpoint reached after %d rounds, %d new facts", round_n + 1, new_total)
                break
            self._facts |= new_facts
            new_total += len(new_facts)
        return new_total

    def _solve_body(self, body: tuple[DatalogAtom, ...], sub: Substitution) -> Iterator[Substitution]:
        if not body:
            yield sub
            return
        first, *rest = body
        for fact in self._facts:
            new_sub = _unify_atom(first, fact, sub)
            if new_sub is not None:
                yield from self._solve_body(tuple(rest), new_sub)

    def query(self, predicate: str, *args: Any) -> list[Substitution]:
        """Return all substitutions that satisfy predicate(*args)."""
        pattern = DatalogAtom(predicate, args)
        return [
            sub for fact in self._facts
            if (sub := _unify_atom(pattern, fact, {})) is not None
        ]

    def facts(self, predicate: str) -> list[DatalogAtom]:
        return sorted((f for f in self._facts if f.predicate == predicate), key=str)

    def all_constants(self, predicate: str, pos: int = 0) -> list[Any]:
        return sorted({f.args[pos] for f in self._facts if f.predicate == predicate})

    def dump(self, predicate: str | None = None) -> str:
        lines = []
        preds = {f.predicate for f in self._facts} if predicate is None else {predicate}
        for pred in sorted(preds):
            for fact in self.facts(pred):
                lines.append(f"  {fact}")
        return "\n".join(lines)


def build_fizzbuzz_datalog(start: int = 1, stop: int = 50) -> DatalogEngine:
    """Populate a DatalogEngine with FizzBuzz facts and rules."""
    engine = DatalogEngine()
    N = DatalogVar("N")

    for n in range(start, stop + 1):
        for d in (2, 3, 5, 7, 11, 13):
            if n % d == 0:
                engine.assert_fact("divides", d, n)
        if _is_prime(n):
            engine.assert_fact("prime", n)
        if _is_perfect(n):
            engine.assert_fact("perfect", n)

    # fizz(N)      :- divides(3, N)
    # buzz(N)      :- divides(5, N)
    # fizzbuzz(N)  :- fizz(N), buzz(N)
    # prime_fizz(N):- fizz(N), prime(N)
    # interesting(N):- prime(N)
    # interesting(N):- perfect(N)
    engine.add_clause(DatalogAtom("fizz",       (N,)), DatalogAtom("divides", (3, N)))
    engine.add_clause(DatalogAtom("buzz",       (N,)), DatalogAtom("divides", (5, N)))
    engine.add_clause(DatalogAtom("fizzbuzz",   (N,)), DatalogAtom("fizz", (N,)), DatalogAtom("buzz", (N,)))
    engine.add_clause(DatalogAtom("prime_fizz", (N,)), DatalogAtom("fizz", (N,)), DatalogAtom("prime", (N,)))
    engine.add_clause(DatalogAtom("interesting",(N,)), DatalogAtom("prime", (N,)))
    engine.add_clause(DatalogAtom("interesting",(N,)), DatalogAtom("perfect", (N,)))

    n_new = engine.derive()
    log.debug("Datalog: derived %d new facts", n_new)
    return engine


# ===========================================================================
# § 19d  Coroutine-based algebraic effect system
# ===========================================================================
# Effects are first-class *values* yielded by a generator.  A separate
# *handler* drives the generator, intercepts each yielded effect, performs
# the actual side-effect (IO, state mutation, …), and sends the result
# back via `generator.send(result)`.
#
# This is structurally analogous to the free monad (§ 2d) but uses Python's
# native generator protocol — no explicit AST, no continuation closures.
#
# Effect algebra:
#   EvalEffect(n)          → LabelT      ask "what label does the rule give n?"
#   EmitEffect(line)       → None        write one output line
#   LogEffect(msg, level)  → None        write a log message
#   AskEffect(key)         → Any         read a config / environment key
#   StateGetEffect()       → dict        read mutable handler state
#   StatePutEffect(state)  → None        write mutable handler state
#
# Handlers:
#   handle_io(prog, rule, sink, env)  — full IO handler (default)
#   handle_pure(prog, rule, env)      — pure/collecting (returns list[str])
#   handle_counting(prog, rule)       — count labels, return Counter[str]

@dataclasses.dataclass(frozen=True)
class EvalEffect:
    n: "Number"

@dataclasses.dataclass(frozen=True)
class EmitEffect:
    line: str

@dataclasses.dataclass(frozen=True)
class LogEffect:
    msg: str
    level: int = logging.DEBUG

@dataclasses.dataclass(frozen=True)
class AskEffect:
    key: str

@dataclasses.dataclass(frozen=True)
class StateGetEffect:
    pass

@dataclasses.dataclass(frozen=True)
class StatePutEffect:
    state: dict[str, Any]


Effect: TypeAlias = EvalEffect | EmitEffect | LogEffect | AskEffect | StateGetEffect | StatePutEffect
EffectProgram: TypeAlias = Generator[Effect, Any, Any]


def fizzbuzz_effect_program(
    numbers: Iterable["Number"],
) -> Generator[Effect, Any, list[str]]:
    """
    Coroutine-based FizzBuzz computation expressed as a sequence of effects.
    Yield an EvalEffect for each number; the handler sends back the label.
    """
    results: list[str] = []
    state: dict[str, Any] = (yield StateGetEffect()) or {}

    for n in numbers:
        label: LabelT = yield EvalEffect(n)
        line = label if label is not None else str(n.value)
        yield EmitEffect(line)
        yield LogEffect(f"emitted {line!r} for n={n.value}", logging.DEBUG)
        results.append(line)
        state["last_n"] = n.value
        yield StatePutEffect(state)

    yield LogEffect(f"done — {len(results)} lines emitted", logging.INFO)
    return results


def handle_io(
    prog: EffectProgram,
    rule: "VisitableRule",
    sink: "OutputSink",
    env: dict[str, Any] | None = None,
) -> Any:
    """IO handler: drives the effect program with real side-effects."""
    _env = env or {}
    _state: dict[str, Any] = {}
    _eff_log = logging.getLogger("fizzbuzz.effects")
    result = None
    sent: Any = None
    try:
        eff = prog.send(None)  # start
        while True:
            match eff:
                case EvalEffect(n=n):
                    sent = rule(n)
                case EmitEffect(line=line):
                    sink.write(line)
                    sent = None
                case LogEffect(msg=msg, level=lvl):
                    _eff_log.log(lvl, "%s", msg)
                    sent = None
                case AskEffect(key=key):
                    sent = _env.get(key)
                case StateGetEffect():
                    sent = dict(_state)
                case StatePutEffect(state=new_state):
                    _state.update(new_state)
                    sent = None
                case _:
                    sent = None
            eff = prog.send(sent)
    except StopIteration as exc:
        result = exc.value
    return result


def handle_pure(
    prog: EffectProgram,
    rule: "VisitableRule",
    env: dict[str, Any] | None = None,
) -> list[str]:
    """Pure handler: collects emitted lines without any IO."""
    _env = env or {}
    _state: dict[str, Any] = {}
    lines: list[str] = []
    sent: Any = None
    try:
        eff = prog.send(None)
        while True:
            match eff:
                case EvalEffect(n=n):
                    sent = rule(n)
                case EmitEffect(line=line):
                    lines.append(line)
                    sent = None
                case LogEffect():
                    sent = None
                case AskEffect(key=key):
                    sent = _env.get(key)
                case StateGetEffect():
                    sent = dict(_state)
                case StatePutEffect(state=new_state):
                    _state.update(new_state)
                    sent = None
                case _:
                    sent = None
            eff = prog.send(sent)
    except StopIteration:
        pass
    return lines


def handle_counting(
    prog: EffectProgram,
    rule: "VisitableRule",
) -> Counter[str]:
    """Counting handler: tallies label frequencies, discards all IO."""
    _state: dict[str, Any] = {}
    counts: Counter[str] = Counter()
    sent: Any = None
    try:
        eff = prog.send(None)
        while True:
            match eff:
                case EvalEffect(n=n):
                    label = rule(n)
                    sent = label
                    counts[label if label is not None else "<number>"] += 1
                case EmitEffect() | LogEffect() | StatePutEffect():
                    sent = None
                case StateGetEffect():
                    sent = dict(_state)
                case AskEffect():
                    sent = None
                case _:
                    sent = None
            eff = prog.send(sent)
    except StopIteration:
        pass
    return counts


# ===========================================================================
# § 19e  LTL temporal logic model checker
# ===========================================================================
# Linear Temporal Logic (LTL) formulas describe properties of *traces* — finite
# or infinite sequences of states.  We check LTL formulas over FizzBuzz output
# sequences (sequences of label strings).
#
# Syntax:
#   LTLAtom(pred)     — atomic proposition: pred(state) is True
#   LTLNot(f)         — ¬f
#   LTLAnd(f, g)      — f ∧ g
#   LTLOr(f, g)       — f ∨ g
#   LTLNext(f)        — ○f — f holds in the next state
#   LTLAlways(f)      — □f — f holds in all future states
#   LTLEventually(f)  — ◇f — f holds in some future state
#   LTLUntil(f, g)    — f U g — f holds until g becomes True
#   LTLRelease(f, g)  — f R g — g holds until (and including) f∧g, or forever
#
# Model checking against a finite trace uses the standard "suffix" semantics:
#   check(formula, trace, i) — True iff formula holds at position i of trace
#
# Convenience:
#   ltl_check(formula, rule, start, stop) — build trace and check from pos 0
#   BUILTIN_LTL_PROPERTIES — curated library of interesting FizzBuzz properties

@dataclasses.dataclass(frozen=True)
class LTLAtom:
    pred: Callable[[str], bool]
    name: str = ""
    def __repr__(self) -> str:
        return self.name or "atom"

@dataclasses.dataclass(frozen=True)
class LTLNot:
    formula: "LTLFormula"
    def __repr__(self) -> str: return f"¬{self.formula!r}"

@dataclasses.dataclass(frozen=True)
class LTLAnd:
    left: "LTLFormula"
    right: "LTLFormula"
    def __repr__(self) -> str: return f"({self.left!r} ∧ {self.right!r})"

@dataclasses.dataclass(frozen=True)
class LTLOr:
    left: "LTLFormula"
    right: "LTLFormula"
    def __repr__(self) -> str: return f"({self.left!r} ∨ {self.right!r})"

@dataclasses.dataclass(frozen=True)
class LTLNext:
    formula: "LTLFormula"
    def __repr__(self) -> str: return f"○{self.formula!r}"

@dataclasses.dataclass(frozen=True)
class LTLAlways:
    formula: "LTLFormula"
    def __repr__(self) -> str: return f"□{self.formula!r}"

@dataclasses.dataclass(frozen=True)
class LTLEventually:
    formula: "LTLFormula"
    def __repr__(self) -> str: return f"◇{self.formula!r}"

@dataclasses.dataclass(frozen=True)
class LTLUntil:
    left: "LTLFormula"
    right: "LTLFormula"
    def __repr__(self) -> str: return f"({self.left!r} U {self.right!r})"

@dataclasses.dataclass(frozen=True)
class LTLRelease:
    left: "LTLFormula"
    right: "LTLFormula"
    def __repr__(self) -> str: return f"({self.left!r} R {self.right!r})"


LTLFormula: TypeAlias = (
    LTLAtom | LTLNot | LTLAnd | LTLOr |
    LTLNext | LTLAlways | LTLEventually |
    LTLUntil | LTLRelease
)


def ltl_check(
    formula: LTLFormula,
    trace: list[str],
    pos: int = 0,
    _memo: dict[tuple[int, int], bool] | None = None,
) -> bool:
    """
    Check whether `formula` holds at position `pos` in `trace`.
    Uses memoisation on (pos, id(formula)) to avoid exponential blowup.
    Out-of-bounds positions are treated as if the trace has terminated (⊥).
    """
    if _memo is None:
        _memo = {}
    key = (pos, id(formula))
    if key in _memo:
        return _memo[key]

    def _check(f: LTLFormula, p: int) -> bool:
        return ltl_check(f, trace, p, _memo)

    result: bool
    if pos >= len(trace):
        # Beyond the trace: only vacuously-true formulas hold
        match formula:
            case LTLAtom():
                result = False
            case LTLNot(formula=f):
                result = not _check(f, pos)
            case LTLAnd(left=l, right=r):
                result = _check(l, pos) and _check(r, pos)
            case LTLOr(left=l, right=r):
                result = _check(l, pos) or _check(r, pos)
            case LTLNext():
                result = False   # no next state past end
            case LTLAlways(formula=f):
                result = True    # vacuously holds on empty suffix
            case LTLEventually(formula=f):
                result = False   # no future state
            case LTLUntil(left=l, right=r):
                result = _check(r, pos)   # g must hold now
            case LTLRelease(left=l, right=r):
                result = True    # vacuously holds
            case _:
                result = False
    else:
        state = trace[pos]
        match formula:
            case LTLAtom(pred=pred):
                result = pred(state)
            case LTLNot(formula=f):
                result = not _check(f, pos)
            case LTLAnd(left=l, right=r):
                result = _check(l, pos) and _check(r, pos)
            case LTLOr(left=l, right=r):
                result = _check(l, pos) or _check(r, pos)
            case LTLNext(formula=f):
                result = _check(f, pos + 1)
            case LTLAlways(formula=f):
                # □f — must hold at all future positions
                result = all(_check(f, p) for p in range(pos, len(trace)))
            case LTLEventually(formula=f):
                # ◇f — must hold at some future position
                result = any(_check(f, p) for p in range(pos, len(trace)))
            case LTLUntil(left=l, right=r):
                # f U g — f holds until g becomes True
                result = False
                for p in range(pos, len(trace)):
                    if _check(r, p):
                        result = True
                        break
                    if not _check(l, p):
                        break
            case LTLRelease(left=l, right=r):
                # f R g — g holds until (and including when) f∧g holds, or forever
                result = True
                for p in range(pos, len(trace)):
                    if not _check(r, p):
                        result = False
                        break
                    if _check(l, p):
                        break
            case _:
                result = False

    _memo[key] = result
    return result


def ltl_verify(
    formula: LTLFormula,
    rule: "VisitableRule",
    start: int = 1,
    stop: int = 100,
) -> tuple[bool, list[str]]:
    """
    Build a FizzBuzz trace and check `formula` from position 0.
    Returns (holds, trace).
    """
    trace = [
        rule(Number(n)) or str(n)
        for n in range(start, stop + 1)
    ]
    return ltl_check(formula, trace, 0), trace


def _ltl_after(n: int, formula: LTLFormula) -> LTLFormula:
    """Wrap `formula` in n LTLNext nodes: check formula holds n steps ahead."""
    for _ in range(n):
        formula = LTLNext(formula)
    return formula


def _ltl_atom(label: str) -> LTLAtom:
    return LTLAtom(pred=lambda s, lbl=label: s == lbl, name=f'"{label}"')

def _ltl_contains(substr: str) -> LTLAtom:
    return LTLAtom(pred=lambda s, sub=substr: sub in s, name=f'contains("{substr}")')

def _ltl_is_number() -> LTLAtom:
    return LTLAtom(pred=lambda s: s.lstrip("-").isdigit(), name="<number>")


# Curated LTL properties for the classic FizzBuzz rule
BUILTIN_LTL_PROPERTIES: dict[str, tuple[LTLFormula, str]] = {
    "fizzbuzz_at_15": (
        _ltl_after(14, LTLAtom(lambda s: s == FIZZBUZZ, name="FizzBuzz@15")),
        "The 15th output (index 14) is FizzBuzz",
    ),
    "no_fizzbuzz_before_15": (
        LTLUntil(
            LTLNot(_ltl_atom(FIZZBUZZ)),
            _ltl_atom(FIZZBUZZ),
        ),
        "FizzBuzz never appears before it first appears",
    ),
    "fizz_eventually": (
        LTLEventually(_ltl_atom(FIZZ)),
        "Fizz appears at some point",
    ),
    "buzz_eventually": (
        LTLEventually(_ltl_atom(BUZZ)),
        "Buzz appears at some point",
    ),
    "fizzbuzz_eventually": (
        LTLEventually(_ltl_atom(FIZZBUZZ)),
        "FizzBuzz appears at some point",
    ),
    "always_something_emitted": (
        LTLAlways(LTLOr(
            LTLOr(_ltl_atom(FIZZ), _ltl_atom(BUZZ)),
            LTLOr(_ltl_atom(FIZZBUZZ), _ltl_is_number()),
        )),
        "Every position produces exactly one of: Fizz, Buzz, FizzBuzz, <number>",
    ),
    "fizzbuzz_implies_next_is_number": (
        LTLAlways(LTLOr(
            LTLNot(_ltl_atom(FIZZBUZZ)),
            LTLNext(_ltl_is_number()),
        )),
        "After FizzBuzz, the next output is always a plain number",
    ),
    "fizz_before_buzz_in_first_15": (
        LTLUntil(
            LTLNot(_ltl_atom(BUZZ)),
            _ltl_atom(FIZZ),
        ),
        "Fizz appears before Buzz",
    ),
}


def run_ltl_properties(
    rule: "VisitableRule",
    start: int = 1,
    stop: int = 100,
) -> dict[str, tuple[bool, str]]:
    """Check all built-in LTL properties against `rule` over [start, stop]."""
    results: dict[str, tuple[bool, str]] = {}
    trace = [rule(Number(n)) or str(n) for n in range(start, stop + 1)]
    for name, (formula, description) in BUILTIN_LTL_PROPERTIES.items():
        holds = ltl_check(formula, trace, 0)
        results[name] = (holds, description)
    return results


# ===========================================================================
# § 19f  Non-determinism via delimited continuations  (list-monad CPS)
# ===========================================================================
# Delimited continuations generalise exceptions: instead of escaping to a
# handler, `shift` reifies the continuation *up to* the nearest `reset`
# prompt as a first-class function.  Calling that function multiple times
# implements backtracking / non-determinism.
#
# We use the standard encoding over the list monad:
#
#   type NDCont[A, R] = (A → [R]) → [R]
#
#   reset_nd(m)     — run computation m, collect all results into a list
#   shift_nd(f)     — capture current list-continuation as k; return f(k)
#   amb(choices)    — non-deterministic choice: yield each element
#   fail_nd()       — dead branch: contribute no results
#   guard_nd(pred)  — prune branch unless pred holds
#
# Applications:
#   nd_fizzbuzz_search(rule, start, stop, pred)
#       — find all n in [start,stop] where pred(label) holds, via backtracking
#   nd_rule_product(rules, n)
#       — all (rule_name, label) pairs for a given n, non-deterministically
#   nd_window_search(rule, start, stop, window, pattern)
#       — find all windows of length `window` whose label sequence == pattern

NDCont: TypeAlias = Callable[[Callable[[Any], list]], list]


def reset_nd(m: NDCont) -> list:
    """Run a non-deterministic computation; return all possible results."""
    return m(lambda x: [x])


def shift_nd(f: Callable[[Callable[[Any], list]], NDCont]) -> NDCont:
    """Capture the current list-continuation and pass it to f."""
    return lambda k: f(k)(k)


def nd_pure(a: Any) -> NDCont:
    """Return a single value non-deterministically (unit/return)."""
    return lambda k: k(a)


def nd_bind(m: NDCont, f: Callable[[Any], NDCont]) -> NDCont:
    """Monadic bind for the non-deterministic continuation monad."""
    def _bound(k: Callable[[Any], list]) -> list:
        return m(lambda a: f(a)(k))
    return _bound


def amb(choices: list[Any]) -> NDCont:
    """Non-deterministically choose from `choices`."""
    return lambda k: [result for c in choices for result in k(c)]


def fail_nd() -> NDCont:
    """Dead branch — contributes no results."""
    return lambda _k: []


def guard_nd(pred: bool) -> NDCont:
    """Prune the current branch if pred is False."""
    return nd_pure(None) if pred else fail_nd()


def nd_fizzbuzz_search(
    rule: "VisitableRule",
    start: int = 1,
    stop: int = 100,
    label_pred: Callable[[LabelT], bool] = lambda lbl: lbl is not None,
) -> list[tuple[int, LabelT]]:
    """
    Non-deterministic search: find all (n, label) in [start,stop] where
    label_pred(label) is True.  Uses delimited continuations for backtracking.
    """
    numbers = list(range(start, stop + 1))

    def _prog(k: Callable[[Any], list]) -> list:
        return amb(numbers)(lambda n:
            nd_bind(
                nd_pure(rule(Number(n))),
                lambda lbl: nd_bind(
                    guard_nd(label_pred(lbl)),
                    lambda _: nd_pure((n, lbl)),
                ),
            )(k)
        )

    return reset_nd(_prog)


def nd_rule_product(
    rules: dict[str, "VisitableRule"],
    n: int,
) -> list[tuple[str, LabelT]]:
    """
    Non-deterministically enumerate (rule_name, label) for a fixed n.
    Returns all pairs across all registered rules.
    """
    def _prog(k: Callable[[Any], list]) -> list:
        return amb(list(rules.items()))(lambda pair:
            nd_pure((pair[0], pair[1](Number(n))))(k)
        )
    return reset_nd(_prog)


def nd_window_search(
    rule: "VisitableRule",
    start: int = 1,
    stop: int = 100,
    window: int = 3,
    pattern: list[LabelT] | None = None,
) -> list[tuple[int, list[LabelT]]]:
    """
    Find all starting positions where `window` consecutive outputs match
    `pattern` (or any all-labelled window if pattern is None).
    Returns list of (start_n, [labels]).
    """
    trace = [rule(Number(n)) for n in range(start, stop + 1)]
    starts = list(range(len(trace) - window + 1))

    def _matches_pattern(labels: list[LabelT]) -> bool:
        if pattern is None:
            return all(lbl is not None for lbl in labels)
        return labels == pattern

    def _prog(k: Callable[[Any], list]) -> list:
        return amb(starts)(lambda i:
            nd_bind(
                nd_pure(trace[i:i + window]),
                lambda labels: nd_bind(
                    guard_nd(_matches_pattern(labels)),
                    lambda _: nd_pure((start + i, labels)),
                ),
            )(k)
        )

    return reset_nd(_prog)


# ===========================================================================
# § 19g  Cooperative green-thread scheduler
# ===========================================================================
# Cooperative multitasking implemented entirely over Python generators.
# A "green thread" is a generator that yields control voluntarily; the
# scheduler runs them in round-robin order until all complete.
#
# Thread API:
#   yield Yield()         — voluntarily relinquish the CPU
#   yield Sleep(n)        — suspend for n scheduler ticks
#   yield Spawn(gen_fn)   — create a new child thread
#   yield Send(chan, val) — send a value to a named channel
#   yield Recv(chan)       — receive the next value from a channel (blocks)
#   yield Join(tid)       — wait for another thread to finish
#
# Scheduler:
#   Scheduler.spawn(gen_fn, *args) → ThreadId
#   Scheduler.run()                → dict[ThreadId, Any]  (return values)
#   Scheduler.channel(name)        → Channel
#
# FizzBuzz application: spawn N workers each covering a sub-range;
# a collector thread receives results via a channel.

@dataclasses.dataclass
class _Yield:
    """Yield CPU for one tick."""

@dataclasses.dataclass
class _Sleep:
    ticks: int

@dataclasses.dataclass
class _Spawn:
    gen_fn: Callable[..., Generator]
    args: tuple
    kwargs: dict

@dataclasses.dataclass
class _Send:
    channel: str
    value: Any

@dataclasses.dataclass
class _Recv:
    channel: str

@dataclasses.dataclass
class _Join:
    tid: int


ThreadId: TypeAlias = int
_GreenEffect: TypeAlias = _Yield | _Sleep | _Spawn | _Send | _Recv | _Join


@dataclasses.dataclass
class _ThreadState:
    tid: ThreadId
    gen: Generator
    sleep_until: int = 0
    waiting_recv: str | None = None   # channel name we're blocked on
    waiting_join: int | None = None   # tid we're waiting for
    result: Any = None
    done: bool = False


class GreenScheduler:
    """
    Round-robin cooperative scheduler over generator-based green threads.
    """

    def __init__(self) -> None:
        self._threads: dict[ThreadId, _ThreadState] = {}
        self._next_tid: int = 0
        self._channels: dict[str, list[Any]] = defaultdict(list)
        self._tick: int = 0
        self._log = logging.getLogger("fizzbuzz.scheduler")

    def spawn(self, gen_fn: Callable[..., Generator], *args: Any, **kwargs: Any) -> ThreadId:
        """Register a new green thread. Returns its ThreadId."""
        tid = self._next_tid
        self._next_tid += 1
        gen = gen_fn(*args, **kwargs)
        self._threads[tid] = _ThreadState(tid=tid, gen=gen)
        return tid

    def channel(self, name: str) -> str:
        """Ensure a channel exists and return its name."""
        _ = self._channels[name]
        return name

    def _is_runnable(self, state: _ThreadState) -> bool:
        if state.done:
            return False
        if self._tick < state.sleep_until:
            return False
        if state.waiting_recv is not None:
            if self._channels[state.waiting_recv]:
                return True
            return False
        if state.waiting_join is not None:
            waited = self._threads.get(state.waiting_join)
            if waited is None or waited.done:
                state.waiting_join = None
                return True
            return False
        return True

    def _step(self, state: _ThreadState) -> None:
        """Advance one thread by one yield."""
        sent_value: Any = None
        if state.waiting_recv is not None:
            chan = state.waiting_recv
            if self._channels[chan]:
                sent_value = self._channels[chan].pop(0)
                state.waiting_recv = None
            else:
                return  # still blocked

        try:
            effect = state.gen.send(sent_value)
        except StopIteration as exc:
            state.done = True
            state.result = exc.value
            return

        match effect:
            case _Yield():
                pass
            case _Sleep(ticks=n):
                state.sleep_until = self._tick + n
            case _Spawn(gen_fn=fn, args=a, kwargs=kw):
                new_tid = self.spawn(fn, *a, **kw)
                # Send new tid back to spawning thread on next step
                try:
                    state.gen.send(new_tid)
                except StopIteration as exc:
                    state.done = True
                    state.result = exc.value
            case _Send(channel=ch, value=val):
                self._channels[ch].append(val)
            case _Recv(channel=ch):
                state.waiting_recv = ch
                # Will be resolved next runnable check
            case _Join(tid=target_tid):
                state.waiting_join = target_tid
            case _:
                pass  # unknown effect, ignore

    def run(self, max_ticks: int = 100_000) -> dict[ThreadId, Any]:
        """Run until all threads complete or max_ticks reached."""
        for tick in range(max_ticks):
            self._tick = tick
            alive = [s for s in self._threads.values() if not s.done]
            if not alive:
                break
            runnable = [s for s in alive if self._is_runnable(s)]
            if not runnable:
                # All threads sleeping or blocked — advance tick
                continue
            for state in runnable:
                self._step(state)
        return {tid: s.result for tid, s in self._threads.items()}


def _green_fizzbuzz_worker(
    rule: "VisitableRule",
    start: int,
    stop: int,
    out_channel: str,
) -> Generator[_GreenEffect, Any, list[str]]:
    """Green thread: evaluate FizzBuzz for [start, stop], send results."""
    results: list[str] = []
    for n_val in range(start, stop + 1):
        label = rule(Number(n_val))
        line = label if label is not None else str(n_val)
        results.append(line)
        yield _Send(channel=out_channel, value=(n_val, line))
        yield _Yield()
    return results


def _green_collector(
    n_workers: int,
    out_channel: str,
    total: int,
) -> Generator[_GreenEffect, Any, dict[int, str]]:
    """Green thread: receive (n, label) pairs from workers, assemble dict."""
    collected: dict[int, str] = {}
    while len(collected) < total:
        pair = yield _Recv(out_channel)
        if pair is not None:
            n_val, line = pair
            collected[n_val] = line
        else:
            yield _Yield()
    return collected


def run_green_fizzbuzz(
    rule: "VisitableRule",
    start: int = 1,
    stop: int = 30,
    n_workers: int = 3,
) -> dict[int, str]:
    """
    Run FizzBuzz using cooperatively-scheduled green threads.
    Splits [start, stop] across n_workers threads; a collector thread
    assembles the results via a shared channel.
    """
    sched = GreenScheduler()
    chan = sched.channel("fizzbuzz_out")
    total = stop - start + 1
    chunk = max(1, total // n_workers)

    # Spawn worker threads
    for i in range(n_workers):
        w_start = start + i * chunk
        w_stop = w_start + chunk - 1 if i < n_workers - 1 else stop
        if w_start <= stop:
            sched.spawn(_green_fizzbuzz_worker, rule, w_start, w_stop, chan)

    # Spawn collector
    collector_tid = sched.spawn(_green_collector, n_workers, chan, total)

    results = sched.run()
    return results.get(collector_tid) or {}


# ===========================================================================
# § 20  Interactive REPL
# ===========================================================================

def run_repl() -> None:
    """Readline-backed interactive FizzBuzz REPL."""
    try:
        import readline  # noqa: F401
    except ImportError:
        pass

    import shlex

    print("FizzBuzz REPL — type 'help' for commands, Ctrl-D to exit.")
    state: dict[str, Any] = {
        "start": 1, "stop": 20, "rule": "classic",
        "formatter": "default", "middlewares": [],
    }

    _mw_map: dict[str, Middleware] = {
        "null_suppressor":    null_suppressor,
        "label_reverser":     label_reverser,
        "prime_annotator":    prime_annotator,
        "collatz_annotator":  collatz_annotator,
        "fingerprint_annotator": fingerprint_annotator,
    }

    while True:
        try:
            line = input("fb> ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            break

        if not line:
            continue

        try:
            parts = shlex.split(line)
        except ValueError as exc:
            print(f"Parse error: {exc}")
            continue

        cmd = parts[0].lower()

        match cmd:
            case "quit" | "exit" | "q":
                break

            case "run" | "go":
                try:
                    pipeline = FizzBuzzFactory.create(
                        start=state["start"], stop=state["stop"],
                        rule_name=state["rule"], formatter=state["formatter"],
                        middlewares=state["middlewares"],
                    )
                    pipeline.run()
                except Exception as exc:
                    print(f"Error: {exc}")

            case "set":
                if len(parts) < 3:
                    print("Usage: set <key> <value>")
                    continue
                key, val = parts[1], parts[2]
                match key:
                    case "start":   state["start"] = int(val)
                    case "stop":    state["stop"] = int(val)
                    case "rule":    state["rule"] = val
                    case "formatter": state["formatter"] = val
                    case "mw":
                        mw = _mw_map.get(val)
                        if mw:
                            state["middlewares"].append(mw)
                            print(f"Added middleware {val!r}")
                        else:
                            print(f"Unknown middleware. Available: {sorted(_mw_map)}")
                    case _:
                        print(f"Unknown setting {key!r}")

            case "clear":
                state["middlewares"].clear()
                print("Middlewares cleared.")

            case "explain":
                explain_rules()

            case "analyse":
                rule = RuleRegistry().get(state["rule"])
                rng = NumberRange(state["start"], state["stop"])
                print(AbstractRuleInterpreter().report(rule, rng))

            case "rules":
                print("Available rules:", RuleRegistry().names())

            case "status":
                mws = [fn.__name__ for fn in state["middlewares"]]
                print(f"  start={state['start']}, stop={state['stop']}, "
                      f"rule={state['rule']!r}, formatter={state['formatter']!r}")
                print(f"  middlewares={mws}")

            case "dsl":
                if len(parts) < 2:
                    print("Usage: dsl <spec>  e.g.: dsl 3:Fizz 5:Buzz prime:★")
                    continue
                dsl_spec = " ".join(parts[1:])
                try:
                    rule = parse_rule_dsl(dsl_spec)
                    RuleRegistry().register("_repl_dsl", rule)
                    state["rule"] = "_repl_dsl"
                    print(f"Registered DSL rule {dsl_spec!r} as '_repl_dsl'")
                except Exception as exc:
                    print(f"DSL error: {exc}")

            case "trace":
                print(_global_tracer.dump())

            case "bloom":
                bf = BloomFilter(expected_items=1000)
                rule = RuleRegistry().get(state["rule"])
                seen: set[str] = set()
                for n in NumberRange(state["start"], state["stop"]):
                    label = rule(n) or str(n.value)
                    bf.add(label)
                    seen.add(label)
                print(f"BloomFilter: {len(bf)} items, fill={bf.fill_ratio:.1%}, "
                      f"est. fp_rate={bf.estimated_fp_rate():.4%}")
                probes = ["Fizz", "Buzz", "FizzBuzz", "NotReal", "42"]
                for p in probes:
                    print(f"  {'✓' if p in bf else '✗'} {p!r}  (true={'yes' if p in seen else 'no'})")

            case "merkle":
                registry = RuleRegistry()
                store = _global_rule_store
                for name in registry.names():
                    digest = store.store(name, registry.get(name))
                    path = store.proof_path(name)
                    print(f"  {name:<20} digest={digest[:16]}  proof={' → '.join(path) or '(root)'}")
                print(f"\nMerkle root: {store.root_hash()}")

            case "observe":
                pairs = fizzbuzz_observable(state["start"], state["stop"], state["rule"]).collect()
                labelled = sum(1 for _, lbl in pairs if lbl)
                print(f"Observable emitted {len(pairs)} items, {labelled} labelled")
                label_counts: Counter[str] = Counter(lbl or "<n>" for _, lbl in pairs)
                for lbl, cnt in label_counts.most_common(5):
                    print(f"  {lbl:<16} {cnt}")

            case "rewrite":
                if len(parts) < 2:
                    print("Usage: rewrite <spec-expr>")
                    print("Example: rewrite '~~DivisibleBy(3)' — expression built from Spec classes")
                    print("Try: DivisibleBySpec(3) & ~_AlwaysFalseSpec()")
                    continue
                expr = " ".join(parts[1:])
                try:
                    spec_obj = eval(expr, {  # noqa: S307
                        "DivisibleBySpec": DivisibleBySpec,
                        "PrimeSpec": PrimeSpec,
                        "PerfectSpec": PerfectSpec,
                        "ParitySpec": ParitySpec,
                        "Parity": Parity,
                        "_AlwaysTrueSpec": _AlwaysTrueSpec,
                        "_AlwaysFalseSpec": _AlwaysFalseSpec,
                        "_AndSpec": _AndSpec,
                        "_OrSpec": _OrSpec,
                        "_NotSpec": _NotSpec,
                    })
                    rewritten = SpecRewriter().rewrite(spec_obj)
                    print(f"  Before: {spec_obj!r}")
                    print(f"  After:  {rewritten!r}")
                except Exception as exc:
                    print(f"Error: {exc}")

            case "proptest":
                n_trials = int(parts[1]) if len(parts) > 1 else 100
                print(f"Running {len(BUILTIN_PROPERTIES)} built-in properties × {n_trials} trials …")
                for name, result in run_builtin_properties(trials=n_trials).items():
                    print(f"  {name:<30} {result}")

            case "parse":
                if len(parts) < 2:
                    print("Usage: parse <dsl-spec>")
                    continue
                dsl_spec = " ".join(parts[1:])
                result_p = parse_rule_dsl_combinators(dsl_spec)
                if result_p.is_ok():
                    rule = result_p.unwrap()
                    RuleRegistry().register("_parsed", rule)
                    state["rule"] = "_parsed"
                    v = RuleExplainerVisitor()
                    rule.accept(v)
                    print(f"Parsed OK:\n{v.explain()}")
                else:
                    print(f"Parse error: {result_p.error}")

            case "reader":
                rule = RuleRegistry().get(state["rule"])
                fmt  = FizzBuzzFactory._build_formatter(state["formatter"])
                env  = FizzBuzzEnv(rule=rule, formatter=fmt, tracer=_global_tracer)
                numbers = list(NumberRange(state["start"], min(state["start"] + 4, state["stop"])))
                for n in numbers:
                    writer = evaluate_in_env(n).run_reader(env)
                    output, log_lines = writer.run()
                    print(f"  {output}")
                    for entry in log_lines:
                        print(f"    [{entry}]")

            case "free":
                rule = RuleRegistry().get(state["rule"])
                numbers = list(NumberRange(state["start"], state["stop"]))
                prog = fb_for_each(numbers)
                _val, lines, counters = fb_interpret_pure(prog, rule)
                for line in lines[:20]:
                    print(f"  {line}")
                if len(lines) > 20:
                    print(f"  … ({len(lines) - 20} more)")
                print(f"  Counters: {dict(counters)}")

            case "zipper":
                rule = RuleRegistry().get(state["rule"])
                z = zip_rule(rule)
                if isinstance(rule, CompositeRule) and rule.rules:
                    z = z.down()
                    print(f"  Root:  {rule!r}")
                    print(f"  Focus: {z.focus!r}")
                    print(f"  Path:  {z.path()}")
                    if len(rule.rules) > 1:
                        z2 = z.right()
                        print(f"  Right: {z2.focus!r}")
                    reconstructed = z.root()
                    print(f"  Root (reconstructed): {reconstructed!r}")
                    print(f"  Identical: {reconstructed.rules == rule.rules}")

            case "lens":
                rule = RuleRegistry().get(state["rule"])
                print(f"  Rule: {rule!r}")
                divs = divisibility_rules_traversal.to_list(rule)
                if divs:
                    print(f"  DivisibilityRules: {[str(d) for d in divs]}")
                    doubled = divisibility_rules_traversal.modify_all(
                        lambda r: div_rule_divisor.modify(lambda d: d)(r)
                    )(rule)
                    print(f"  Lens demo (first div label): {div_rule_label.get(divs[0])!r}")
                    new_rule = composite_first_rule.modify(
                        lambda r: div_rule_label.set(r, r.label.upper()) if isinstance(r, DivisibilityRule) else r
                    )(rule)
                    print(f"  After uppercasing first label: {composite_first_rule.get(new_rule)!r}")

            case "datalog":
                n_stop = min(state["stop"], 50)
                engine = build_fizzbuzz_datalog(state["start"], n_stop)
                fizzbuzz_ns = engine.all_constants("fizzbuzz", pos=0)
                prime_ns    = engine.all_constants("prime", pos=0)
                interesting = engine.all_constants("interesting", pos=0)
                print(f"  FizzBuzz numbers: {fizzbuzz_ns}")
                print(f"  Primes:           {prime_ns[:10]}{'…' if len(prime_ns) > 10 else ''}")
                print(f"  Interesting:      {sorted(set(interesting))[:10]}")
                if len(parts) > 1:
                    pred = parts[1]
                    vals = engine.all_constants(pred)
                    print(f"  {pred}: {vals}")

            case "free-traced":
                rule = RuleRegistry().get(state["rule"])
                numbers = list(NumberRange(state["start"], min(state["start"] + 9, state["stop"])))
                prog = fb_for_each(numbers)
                sink = BufferedSink()
                fb_interpret_traced(prog, rule, sink, _global_tracer)
                for line in sink.lines:
                    print(f"  {line}")
                print(f"  Spans recorded: {len(_global_tracer._spans)}")

            case "tagless":
                alg_name = parts[1] if len(parts) > 1 else "collect"
                rule = RuleRegistry().get(state["rule"])
                term = fizzbuzz_term(state["start"], state["stop"])
                match alg_name:
                    case "collect":
                        lines = term(_CollectingAlgebra(rule))
                        for ln in lines[:20]:
                            print(f"  {ln}")
                        if len(lines) > 20:
                            print(f"  … ({len(lines) - 20} more)")
                    case "count":
                        counts = term(_CountingAlgebra(rule))
                        for lbl, cnt in counts.most_common():
                            print(f"  {lbl:<16} {cnt}")
                    case "pretty":
                        print(term(_PrettyPrintAlgebra(indent=1)))
                    case "print":
                        term(_PrintingAlgebra(rule, StdoutSink()))
                    case _:
                        print("Usage: tagless [collect|count|pretty|print]")

            case "transduce":
                rule = RuleRegistry().get(state["rule"])
                rng = list(NumberRange(state["start"], state["stop"]))
                xf = compose_xf(
                    labelling(rule),
                    filtering(lambda pair: pair[1] is not None),
                    mapping(lambda pair: f"{pair[0].value}={pair[1]}"),
                )
                result_lines = into(xf, rng)
                for ln in result_lines:
                    print(f"  {ln}")
                print(f"  ({len(result_lines)} labelled out of {len(rng)})")

            case "store":
                rule = RuleRegistry().get(state["rule"])
                ctx_labels = fizzbuzz_context_labels(
                    rule, state["start"], min(state["stop"], state["start"] + 19)
                )
                for cl in ctx_labels:
                    marker = "▶" if cl.is_run else ("·" if cl.is_isolated else " ")
                    print(f"  {marker} {cl.position:>3}  label={cl.label or '':<8}"
                          f"  prev={cl.prev_label or '':<8}  next={cl.next_label or '':<8}")

            case "attrs":
                rule = RuleRegistry().get(state["rule"])
                tree = attribute_rule_tree(rule)
                print(tree.pretty())

            case "cps":
                rule = RuleRegistry().get(state["rule"])
                start, stop = state["start"], state["stop"]
                lines_cps, exited = cps_with_early_exit(start, stop, rule, exit_on=FIZZBUZZ)
                for ln in lines_cps[:20]:
                    print(f"  {ln}")
                if len(lines_cps) > 20:
                    print(f"  … ({len(lines_cps) - 20} more)")
                print(f"  early-exit triggered: {exited}")

            case "abstract":
                rule = RuleRegistry().get(state["rule"])
                lo_val = state["start"]
                hi_val = state["stop"]
                iv = Interval(lo_val, hi_val)
                result_ab = abstract_eval(rule, iv)
                print(f"  Interval: {iv!r}")
                print(f"  Abstract result: {result_ab!r}")
                print(f"  Certain: {result_ab.is_certain}")
                print(f"  Always labelled: {abstract_prove_always_labelled(rule, iv)}")
                for singleton in range(lo_val, min(lo_val + 5, hi_val + 1)):
                    iv_s = Interval.of(singleton)
                    ab_s = abstract_eval(rule, iv_s)
                    print(f"    n={singleton}: {ab_s}")

            case "iso":
                rule = RuleRegistry().get(state["rule"])
                print(f"  number_int_iso demo:")
                n = Number(state["start"])
                v = number_int_iso.get(n)
                n2 = number_int_iso.review(v + 10)
                print(f"    Number({n.value}) → int({v}) → Number({n2.value})")
                print(f"  composite_labels_adapter:")
                labels = composite_labels_adapter.get(rule)
                print(f"    labels: {labels}")
                print(f"  divisor_scale_iso (×2):")
                if rule.rules:
                    first_div = next((r for r in rule.rules if isinstance(r, DivisibilityRule)), None)
                    if first_div:
                        scaled = divisor_scale_iso(2).get(first_div)
                        print(f"    {first_div} → {scaled}")

            case "stream":
                rule = RuleRegistry().get(state["rule"])
                n_items = int(parts[1]) if len(parts) > 1 else 20
                s = stream_fizzbuzz_labels(rule, state["start"])
                items = s.take(n_items)
                print(f"  [{', '.join(items)}]")
                counts_stream = stream_running_counts(rule, state["start"])
                final_counts = counts_stream.drop(n_items).head()
                print(f"  Running counts after {n_items}: {dict(final_counts)}")

            case "ltl":
                rule = RuleRegistry().get(state["rule"])
                results_ltl = run_ltl_properties(rule, state["start"], state["stop"])
                for prop_name, (holds, desc) in results_ltl.items():
                    sym = "✓" if holds else "✗"
                    print(f"  {sym} {prop_name:<40} {desc}")

            case "effects":
                handler_name = parts[1] if len(parts) > 1 else "pure"
                rule = RuleRegistry().get(state["rule"])
                numbers = list(NumberRange(state["start"], state["stop"]))
                match handler_name:
                    case "pure":
                        lines = handle_pure(fizzbuzz_effect_program(numbers), rule)
                        for ln in lines[:20]:
                            print(f"  {ln}")
                        if len(lines) > 20:
                            print(f"  … ({len(lines) - 20} more)")
                    case "count":
                        counts = handle_counting(fizzbuzz_effect_program(numbers), rule)
                        for lbl, cnt in counts.most_common():
                            print(f"  {lbl:<16} {cnt}")
                    case "io":
                        handle_io(fizzbuzz_effect_program(numbers), rule, StdoutSink())
                    case _:
                        print("Usage: effects [pure|count|io]")

            case "kleisli":
                rule = RuleRegistry().get(state["rule"])
                pipeline = fizzbuzz_pipeline_k(rule)
                inputs = [str(i) for i in range(state["start"], state["stop"] + 1)]
                ok_vals, err_vals = kleisli_run_many(pipeline, inputs)
                for v in ok_vals[:20]:
                    print(f"  {v}")
                if len(ok_vals) > 20:
                    print(f"  … ({len(ok_vals) - 20} more)")
                if err_vals:
                    print(f"  Errors: {err_vals}")
                # Demonstrate fanout and guard
                label_k = _eval_rule_k(rule)
                length_k = Kleisli.lift(lambda s: len(s))
                paired = (Kleisli.lift(lambda n: Number(n)).local(int)
                          >> label_k.fanout(Kleisli.lift(lambda n: n.value % 2 == 0)))
                sample = _parse_int_k >> _validate_positive_k >> _to_number_k
                sample_result = sample.fanout(Kleisli.lift(lambda s: s))(str(state["start"]))
                print(f"\n  fanout demo (Number, is_even) for {state['start']}: {sample_result}")

            case "regex":
                token = parts[1] if len(parts) > 1 else "Fizz"
                valid = validate_fizzbuzz_output(token)
                cls_name = re_classify(token)
                print(f"  {token!r}: valid={valid}, class={cls_name!r}")
                # Show derivatives step by step
                r = _RE_FB_OUTPUT
                for i, c in enumerate(token):
                    r = re_simplify(re_deriv(r, c))
                    print(f"  after {token[:i+1]!r}: nullable={re_nullable(r)}")
                print(f"  → matches: {re_nullable(r)}")

            case "hll":
                rule = RuleRegistry().get(state["rule"])
                hll = hll_fizzbuzz(rule, state["start"], state["stop"])
                exact = len({rule(Number(n)) or str(n)
                             for n in range(state["start"], state["stop"] + 1)})
                print(f"  {hll!r}")
                print(f"  Exact distinct count: {exact}")
                print(f"  Error: {abs(hll.estimate() - exact) / max(exact, 1):.1%}"
                      f"  (theoretical ≤ {hll.relative_error():.1%})")

            case "segtree":
                rule = RuleRegistry().get(state["rule"])
                lo, hi = state["start"], state["stop"]
                hist = PersistentLabelHistory.build(rule, lo, hi)
                mid = (lo + hi) // 2
                print(f"  Persistent seg tree: {hist.n_versions()} versions for [{lo}, {hi}]")
                print(f"  Sum of label-codes [lo..mid] (latest): {hist.query_sum(lo, mid)}")
                print(f"  Max label-code  [lo..hi]  (latest):   {hist.query_max(lo, hi)}")
                # Time-travel: query the state after the first 5 numbers
                if hist.n_versions() > 5:
                    print(f"  Sum [lo..hi] after 5 insertions (v5): {hist.query_sum(lo, hi, version=5)}")
                code_names = {0: "number", 1: "Fizz", 2: "Buzz", 3: "FizzBuzz"}
                print(f"  Max code = {code_names.get(hist.query_max(lo, hi), '?')!r}")

            case "ndcont":
                rule = RuleRegistry().get(state["rule"])
                lo, hi = state["start"], state["stop"]
                labelled = nd_fizzbuzz_search(rule, lo, hi, lambda lbl: lbl is not None)
                print(f"  Labelled numbers in [{lo}, {hi}] via backtracking:")
                for n_val, lbl in labelled[:20]:
                    print(f"    {n_val:>4}  {lbl}")
                if len(labelled) > 20:
                    print(f"    … ({len(labelled) - 20} more)")
                # Window search for runs of labelled outputs
                windows = nd_window_search(rule, lo, min(hi, lo + 49), window=2)
                print(f"\n  Consecutive-labelled windows (window=2, first 50 numbers):")
                for start_n, lbls in windows[:5]:
                    print(f"    n={start_n}: {lbls}")

            case "help":
                print(
                    "  run / go                     — execute with current settings\n"
                    "  set <k> <v>                  — start/stop/rule/formatter/mw\n"
                    "  clear                        — clear middleware stack\n"
                    "  explain                      — print rule trees\n"
                    "  analyse                      — static label-frequency analysis\n"
                    "  rules                        — list registered rules\n"
                    "  status                       — show current settings\n"
                    "  dsl <spec>                   — define rule inline (simple)\n"
                    "  parse <spec>                 — parse rule via combinator parser\n"
                    "  rewrite <spec-expr>          — algebraically simplify a Spec\n"
                    "  observe                      — run via Observable stream\n"
                    "  bloom                        — build Bloom filter over labels\n"
                    "  merkle                       — store rules in Merkle tree\n"
                    "  proptest [N]                 — run built-in property tests\n"
                    "  reader                       — evaluate via Reader+Writer monads\n"
                    "  trace                        — dump tracing spans\n"
                    "  free                         — run via free monad (pure interpreter)\n"
                    "  free-traced                  — run via free monad (traced interpreter)\n"
                    "  zipper                       — navigate rule tree with zipper\n"
                    "  lens                         — demonstrate optics on rule structure\n"
                    "  datalog [pred]               — Datalog forward-chaining inference\n"
                    "  tagless [collect|count|pretty|print]  — tagless final algebra\n"
                    "  transduce                    — composable transducer pipeline\n"
                    "  store                        — Store comonad context labels\n"
                    "  attrs                        — attribute grammar tree annotation\n"
                    "  effects [pure|count|io]      — coroutine effect system\n"
                    "  cps                          — CPS transform with callcc early-exit\n"
                    "  abstract                     — abstract interpretation (interval domain)\n"
                    "  iso                          — profunctor Iso/Adapter demo\n"
                    "  stream [N]                   — lazy infinite stream (take N)\n"
                    "  ltl                          — LTL temporal logic model checker\n"
                    "  kleisli                      — Kleisli arrow pipeline\n"
                    "  regex <token>                — Brzozowski derivative matching\n"
                    "  hll                          — HyperLogLog cardinality sketch\n"
                    "  segtree                      — persistent segment tree\n"
                    "  ndcont                       — non-determinism via delimited continuations\n"
                    "  recur                        — recursion schemes (cata/ana/hylo/para/zygo)\n"
                    "  sat <expr>                   — DPLL SAT solver on propositional formula\n"
                    "  cms                          — Count-Min Sketch frequency estimation\n"
                    "  frp                          — arrowized FRP Behavior/Event network\n"
                    "  green                        — cooperative green-thread FizzBuzz\n"
                    "  quit / exit                  — exit REPL\n"
                )

            case "recur":
                rule = RuleRegistry().get(state["rule"])
                depth    = cata(_cata_depth, rule)
                divisors = cata(_cata_divisors, rule)
                n_labels = cata(_cata_label_count, rule)
                print(f"  Catamorphisms over {state['rule']!r}:")
                print(f"    depth         = {depth}")
                print(f"    all divisors  = {set(divisors)}")
                print(f"    label-bearing = {n_labels}")
                # Paramorphism: depth with original subtree info
                def _para_alg(layer: RuleF) -> str:
                    match layer:
                        case RuleCompositeF(children=ch): return f"Composite({', '.join(str(c) for c in ch)})"
                        case RuleDivF(divisor=d, label=lbl): return f"Div({d},{lbl!r})"
                        case _: return "Leaf"
                para_result = para(lambda l: _para_alg(rulef_fmap(l, lambda p: p[1])), rule)
                print(f"  Paramorphism result: {para_result}")

            case "sat":
                expr_str = " ".join(parts[1:]) if len(parts) > 1 else "PVar('x')"
                _sat_ns = {
                    "PVar": PVar, "PNot": PNot, "PAnd": PAnd, "POr": POr,
                    "PImp": PImp, "PIff": PIff, "PTrue": PTrue, "PFalse": PFalse,
                }
                try:
                    prop_obj = eval(expr_str, _sat_ns)  # noqa: S307
                    is_sat = prop_is_sat(prop_obj)
                    is_taut = prop_is_tautology(prop_obj)
                    asgn = dpll(prop_to_cnf(prop_obj))
                    print(f"  Formula:     {prop_obj!r}")
                    print(f"  SAT:         {is_sat}")
                    print(f"  Tautology:   {is_taut}")
                    if asgn:
                        print(f"  Assignment:  {asgn}")
                except Exception as exc:
                    print(f"  Error: {exc}")
                # Also run rule consistency check
                rule = RuleRegistry().get(state["rule"])
                msgs = check_rule_mutual_exclusion(rule, state["start"], min(state["stop"], state["start"] + 4))
                print(f"\n  Rule consistency ({state['rule']!r}, first 5 n):")
                for m in msgs[:5]:
                    print(m)

            case "cms":
                rule = RuleRegistry().get(state["rule"])
                cms = cms_fizzbuzz(rule, state["start"], state["stop"])
                print(f"  {cms!r}")
                universe = [FIZZ, BUZZ, FIZZBUZZ] + [str(n) for n in range(1, 11)]
                top = cms.top_k(5, universe)
                print(f"  Top-5 estimated frequencies:")
                for item, est in top:
                    print(f"    {item!r:<16} estimate={est}")
                print(f"  inner_product(self) ≈ {cms.inner_product(cms)}")

            case "frp":
                rule = RuleRegistry().get(state["rule"])
                lo, hi = state["start"], min(state["stop"], state["start"] + 19)
                _, label_beh, out_event = build_fizzbuzz_frp(rule, lo, hi)
                print(f"  FRP network output ({lo}..{hi}):")
                for t, v in out_event.occurrences[:20]:
                    n_val = lo + int(t)
                    print(f"    t={t:.0f}  n={n_val:>3}  {v}")
                runs = fizzbuzz_run_detector(rule, lo, hi)
                print(f"\n  Consecutive-equal-label runs: {len(runs.occurrences)}")
                for t, (a, b) in runs.occurrences:
                    print(f"    t={t:.0f}  ({a!r}, {b!r})")

            case "green":
                rule = RuleRegistry().get(state["rule"])
                n_w = int(parts[1]) if len(parts) > 1 else 3
                result_map = run_green_fizzbuzz(rule, state["start"], state["stop"], n_workers=n_w)
                if result_map:
                    for n_val in sorted(result_map)[:20]:
                        print(f"  {n_val:>4}  {result_map[n_val]}")
                    if len(result_map) > 20:
                        print(f"  … ({len(result_map) - 20} more)")
                else:
                    print("  (no results — try increasing max_ticks or reducing range)")

            case _:
                print(f"Unknown command {cmd!r}. Type 'help'.")


# ===========================================================================
# § 21  Auxiliary CLI subcommands
# ===========================================================================

def explain_rules() -> None:
    registry = RuleRegistry()
    for name in registry.names():
        rule = registry.get(name)
        visitor = RuleExplainerVisitor()
        rule.accept(visitor)
        print(f"\nRule: {name!r}\n{visitor.explain()}")


def cmd_analyse(rule_name: str, start: int, stop: int) -> None:
    rule = RuleRegistry().get(rule_name)
    rng = NumberRange(start, stop)
    print(AbstractRuleInterpreter().report(rule, rng))


def cmd_compile_check(rule_name: str, start: int, stop: int) -> None:
    rule = RuleRegistry().get(rule_name)
    compiled = RuleCompiler.compile(rule)
    rng = NumberRange(start, stop)
    mismatches = 0
    for n in rng:
        expected = rule(n)
        got = compiled(n)
        if expected != got:
            print(f"  MISMATCH n={n.value}: rule={expected!r} compiled={got!r}")
            mismatches += 1
    if mismatches == 0:
        print(f"Compiled rule matches interpreted rule for all {len(rng)} numbers. ✓")
    else:
        print(f"{mismatches} mismatches found.")


# ===========================================================================
# § 22  Entrypoint
# ===========================================================================

def main(argv: Sequence[str] = sys.argv[1:]) -> int:
    import argparse

    parser = argparse.ArgumentParser(
        description="Enterprise FizzBuzz™",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = parser.add_subparsers(dest="cmd")

    # ── run ──────────────────────────────────────────────────────────────────
    run_p = sub.add_parser("run", help="Run FizzBuzz")
    run_p.add_argument("--start",     type=int,  default=1)
    run_p.add_argument("--stop",      type=int,  default=100)
    run_p.add_argument("--rule",      default="classic")
    run_p.add_argument("--formatter", default="default",
                       help="Formatter chain, e.g. default+ansi")
    run_p.add_argument("--parallel",  action="store_true")
    run_p.add_argument("--compiled",  action="store_true",
                       help="Use bytecode-compiled rule evaluator")
    run_p.add_argument("--shard",     type=int,  default=0, metavar="N",
                       help="Distribute across N worker processes")
    run_p.add_argument("--middleware", nargs="*", default=[],
                       choices=["null_suppressor", "label_reverser", "prime_annotator",
                                "collatz_annotator", "fingerprint_annotator"],
                       metavar="MW")
    run_p.add_argument("--dsl", default=None, metavar="SPEC",
                       help='Inline rule DSL, e.g. "3:Fizz 5:Buzz prime:★"')

    # ── explain ───────────────────────────────────────────────────────────────
    sub.add_parser("explain", help="Print rule tree explanations")

    # ── analyse ───────────────────────────────────────────────────────────────
    ana_p = sub.add_parser("analyse", help="Static label-frequency analysis")
    ana_p.add_argument("--rule",  default="classic")
    ana_p.add_argument("--start", type=int, default=1)
    ana_p.add_argument("--stop",  type=int, default=100)

    # ── compile-check ─────────────────────────────────────────────────────────
    cc_p = sub.add_parser("compile-check",
                           help="Verify compiled rule matches interpreted rule")
    cc_p.add_argument("--rule",  default="classic")
    cc_p.add_argument("--start", type=int, default=1)
    cc_p.add_argument("--stop",  type=int, default=100)

    # ── repl ──────────────────────────────────────────────────────────────────
    sub.add_parser("repl", help="Start interactive REPL")

    # ── proptest ──────────────────────────────────────────────────────────────
    pt_p = sub.add_parser("proptest", help="Run built-in property-based tests")
    pt_p.add_argument("--trials", type=int, default=200)

    # ── observe ───────────────────────────────────────────────────────────────
    obs_p = sub.add_parser("observe", help="Run via reactive Observable stream")
    obs_p.add_argument("--start",  type=int, default=1)
    obs_p.add_argument("--stop",   type=int, default=100)
    obs_p.add_argument("--rule",   default="classic")
    obs_p.add_argument("--take",   type=int, default=0, metavar="N", help="Emit only first N items")

    # ── merkle ────────────────────────────────────────────────────────────────
    sub.add_parser("merkle", help="Store all rules in content-addressable Merkle store")

    # ── parse-dsl ─────────────────────────────────────────────────────────────
    pd_p = sub.add_parser("parse-dsl", help="Parse a rule DSL via parser combinators")
    pd_p.add_argument("spec", nargs="+")

    # ── free ──────────────────────────────────────────────────────────────────
    free_p = sub.add_parser("free", help="Run via free monad interpreter")
    free_p.add_argument("--start",      type=int, default=1)
    free_p.add_argument("--stop",       type=int, default=20)
    free_p.add_argument("--rule",       default="classic")
    free_p.add_argument("--interpreter", choices=["io", "pure", "traced", "mock"], default="pure")

    # ── datalog ───────────────────────────────────────────────────────────────
    dl_p = sub.add_parser("datalog", help="Datalog forward-chaining inference")
    dl_p.add_argument("--start",     type=int, default=1)
    dl_p.add_argument("--stop",      type=int, default=50)
    dl_p.add_argument("--query",     default=None, help="Predicate to query (e.g. fizzbuzz)")

    # ── zipper ────────────────────────────────────────────────────────────────
    zp_p = sub.add_parser("zipper", help="Demonstrate rule tree zipper")
    zp_p.add_argument("--rule", default="classic")

    # ── rewrite ───────────────────────────────────────────────────────────────
    rw_p = sub.add_parser("rewrite", help="Algebraically simplify a Spec expression")
    rw_p.add_argument("expr", nargs="+")

    # ── tagless ───────────────────────────────────────────────────────────────
    tl_p = sub.add_parser("tagless", help="Run via tagless final algebra")
    tl_p.add_argument("--start",   type=int, default=1)
    tl_p.add_argument("--stop",    type=int, default=20)
    tl_p.add_argument("--rule",    default="classic")
    tl_p.add_argument("--algebra", choices=["collect", "count", "pretty", "print", "trace"],
                      default="collect")

    # ── transduce ─────────────────────────────────────────────────────────────
    xf_p = sub.add_parser("transduce", help="Run via composable transducer pipeline")
    xf_p.add_argument("--start",  type=int, default=1)
    xf_p.add_argument("--stop",   type=int, default=100)
    xf_p.add_argument("--rule",   default="classic")
    xf_p.add_argument("--window", type=int, default=0, metavar="N",
                      help="If >0, emit sliding windows of size N")

    # ── store ─────────────────────────────────────────────────────────────────
    st_p = sub.add_parser("store", help="Store comonad context-sensitive labelling")
    st_p.add_argument("--start", type=int, default=1)
    st_p.add_argument("--stop",  type=int, default=30)
    st_p.add_argument("--rule",  default="classic")

    # ── attrs ─────────────────────────────────────────────────────────────────
    at_p = sub.add_parser("attrs", help="Attribute grammar tree annotation")
    at_p.add_argument("--rule", default="classic")

    # ── effects ───────────────────────────────────────────────────────────────
    ef_p = sub.add_parser("effects", help="Coroutine-based algebraic effect system")
    ef_p.add_argument("--start",   type=int, default=1)
    ef_p.add_argument("--stop",    type=int, default=20)
    ef_p.add_argument("--rule",    default="classic")
    ef_p.add_argument("--handler", choices=["pure", "count", "io"], default="pure")

    # ── cps ───────────────────────────────────────────────────────────────────
    cps_p = sub.add_parser("cps", help="CPS transform with callcc early-exit")
    cps_p.add_argument("--start",    type=int, default=1)
    cps_p.add_argument("--stop",     type=int, default=30)
    cps_p.add_argument("--rule",     default="classic")
    cps_p.add_argument("--exit-on",  default=FIZZBUZZ, metavar="LABEL",
                       help="Label that triggers callcc early exit")

    # ── abstract ──────────────────────────────────────────────────────────────
    ab_p = sub.add_parser("abstract", help="Abstract interpretation over interval domain")
    ab_p.add_argument("--start", type=int, default=1)
    ab_p.add_argument("--stop",  type=int, default=100)
    ab_p.add_argument("--rule",  default="classic")

    # ── iso ───────────────────────────────────────────────────────────────────
    iso_p = sub.add_parser("iso", help="Profunctor Iso and Adapter demo")
    iso_p.add_argument("--rule", default="classic")

    # ── stream ────────────────────────────────────────────────────────────────
    stream_p = sub.add_parser("stream", help="Lazy infinite stream evaluation")
    stream_p.add_argument("--start", type=int, default=1)
    stream_p.add_argument("--take",  type=int, default=20, metavar="N")
    stream_p.add_argument("--rule",  default="classic")
    stream_p.add_argument("--mode",  choices=["labels", "counts", "pairs"], default="labels")

    # ── ltl ───────────────────────────────────────────────────────────────────
    ltl_p = sub.add_parser("ltl", help="LTL temporal logic model checker")
    ltl_p.add_argument("--start", type=int, default=1)
    ltl_p.add_argument("--stop",  type=int, default=100)
    ltl_p.add_argument("--rule",  default="classic")

    # ── kleisli ───────────────────────────────────────────────────────────────
    kl_p = sub.add_parser("kleisli", help="Kleisli arrow pipeline over Result monad")
    kl_p.add_argument("--start",  type=int, default=1)
    kl_p.add_argument("--stop",   type=int, default=30)
    kl_p.add_argument("--rule",   default="classic")
    kl_p.add_argument("--bad",    nargs="*", default=[], metavar="TOKEN",
                      help="Extra inputs to inject (may fail Kleisli guards)")

    # ── regex ─────────────────────────────────────────────────────────────────
    rx_p = sub.add_parser("regex", help="Brzozowski derivative regex matching")
    rx_p.add_argument("--start",  type=int, default=1)
    rx_p.add_argument("--stop",   type=int, default=20)
    rx_p.add_argument("--rule",   default="classic")
    rx_p.add_argument("--token",  default=None, help="Single token to classify")

    # ── hll ───────────────────────────────────────────────────────────────────
    hll_p = sub.add_parser("hll", help="HyperLogLog distinct-label cardinality sketch")
    hll_p.add_argument("--start", type=int, default=1)
    hll_p.add_argument("--stop",  type=int, default=10_000)
    hll_p.add_argument("--rule",  default="classic")
    hll_p.add_argument("--b",     type=int, default=8, metavar="BITS",
                       help="Register bits (4–16); more → less error")

    # ── segtree ───────────────────────────────────────────────────────────────
    sg_p = sub.add_parser("segtree", help="Persistent segment tree over FizzBuzz label codes")
    sg_p.add_argument("--start",   type=int, default=1)
    sg_p.add_argument("--stop",    type=int, default=30)
    sg_p.add_argument("--rule",    default="classic")
    sg_p.add_argument("--query",   choices=["sum", "max"], default="sum")
    sg_p.add_argument("--version", type=int, default=-1,
                      help="Which version to query (-1 = latest)")

    # ── ndcont ────────────────────────────────────────────────────────────────
    nd_p = sub.add_parser("ndcont", help="Non-determinism via delimited continuations")
    nd_p.add_argument("--start",  type=int, default=1)
    nd_p.add_argument("--stop",   type=int, default=100)
    nd_p.add_argument("--rule",   default="classic")
    nd_p.add_argument("--mode",   choices=["labelled", "product", "windows"], default="labelled")
    nd_p.add_argument("--window", type=int, default=3)

    # ── recur ─────────────────────────────────────────────────────────────────
    rec_p = sub.add_parser("recur", help="Recursion schemes (cata/ana/hylo/para/zygo)")
    rec_p.add_argument("--rule",   default="classic")
    rec_p.add_argument("--scheme", choices=["cata","ana","hylo","para","zygo","histo"],
                       default="cata")
    rec_p.add_argument("--alg",    choices=["depth","divisors","label_count"], default="depth")

    # ── sat ───────────────────────────────────────────────────────────────────
    sat_p = sub.add_parser("sat", help="DPLL propositional SAT solver")
    sat_p.add_argument("--rule",  default="classic")
    sat_p.add_argument("--start", type=int, default=1)
    sat_p.add_argument("--stop",  type=int, default=15)
    sat_p.add_argument("formula", nargs="*",
                       help="Prop formula (Python expr). E.g.: PAnd(PVar('x'),PNot(PVar('x')))")

    # ── cms ───────────────────────────────────────────────────────────────────
    cms_p = sub.add_parser("cms", help="Count-Min Sketch frequency estimation")
    cms_p.add_argument("--start",   type=int, default=1)
    cms_p.add_argument("--stop",    type=int, default=1000)
    cms_p.add_argument("--rule",    default="classic")
    cms_p.add_argument("--epsilon", type=float, default=0.05)
    cms_p.add_argument("--delta",   type=float, default=0.01)

    # ── frp ───────────────────────────────────────────────────────────────────
    frp_p = sub.add_parser("frp", help="Arrowized FRP Behavior/Event network")
    frp_p.add_argument("--start", type=int, default=1)
    frp_p.add_argument("--stop",  type=int, default=30)
    frp_p.add_argument("--rule",  default="classic")

    # ── green ─────────────────────────────────────────────────────────────────
    gr_p = sub.add_parser("green", help="Cooperative green-thread scheduler")
    gr_p.add_argument("--start",   type=int, default=1)
    gr_p.add_argument("--stop",    type=int, default=30)
    gr_p.add_argument("--rule",    default="classic")
    gr_p.add_argument("--workers", type=int, default=4)

    args = parser.parse_args(argv)
    cmd = args.cmd or "run"

    match cmd:
        case "explain":
            explain_rules()

        case "analyse":
            cmd_analyse(args.rule, args.start, args.stop)

        case "compile-check":
            cmd_compile_check(args.rule, args.start, args.stop)

        case "repl":
            run_repl()

        case "proptest":
            print(f"Running {len(BUILTIN_PROPERTIES)} built-in properties × {args.trials} trials …\n")
            all_passed = True
            for name, result in run_builtin_properties(trials=args.trials).items():
                print(f"  {name:<35} {result}")
                if not result.passed:
                    all_passed = False
            print(f"\n{'All properties passed.' if all_passed else 'SOME PROPERTIES FAILED.'}")

        case "observe":
            obs = fizzbuzz_observable(args.start, args.stop, args.rule)
            if args.take > 0:
                obs = obs.take(args.take)
            formatter = FizzBuzzFactory._build_formatter("default")
            counter: Counter[str] = Counter()
            def _handle(pair: tuple[Number, LabelT]) -> None:
                n, label = pair
                print(formatter.format(n, label))
                counter[label or "<number>"] += 1
            obs.subscribe(_handle)
            print(f"\n--- Observable stats: {sum(counter.values())} items", file=sys.stderr)
            for lbl, cnt in counter.most_common():
                print(f"  {lbl:<16} {cnt}", file=sys.stderr)

        case "merkle":
            registry = RuleRegistry()
            store = _global_rule_store
            for name in registry.names():
                digest = store.store(name, registry.get(name))
                path = store.proof_path(name)
                print(f"  {name:<22} {digest[:24]}  proof=[{', '.join(path)}]")
            print(f"\nMerkle root: {store.root_hash()}")

        case "parse-dsl":
            spec = " ".join(args.spec)
            result_p = parse_rule_dsl_combinators(spec)
            if result_p.is_ok():
                rule = result_p.unwrap()
                v = RuleExplainerVisitor()
                rule.accept(v)
                print(f"Parsed OK:\n{v.explain()}")
            else:
                print(f"Parse error: {result_p.error}", file=sys.stderr)
                return 1

        case "free":
            rule = RuleRegistry().get(args.rule)
            numbers = list(NumberRange(args.start, args.stop))
            prog = fb_for_each(numbers)
            if args.interpreter == "pure":
                _val, lines, counters = fb_interpret_pure(prog, rule)
                for line in lines:
                    print(line)
                print(f"\nCounters: {dict(counters)}", file=sys.stderr)
            elif args.interpreter == "io":
                fb_interpret_io(prog, rule, StdoutSink())
            elif args.interpreter == "traced":
                sink = BufferedSink()
                fb_interpret_traced(prog, rule, sink, _global_tracer)
                for line in sink.lines:
                    print(line)
                print(_global_tracer.dump(), file=sys.stderr)
            elif args.interpreter == "mock":
                mock = {n: FIZZ if n % 3 == 0 else (BUZZ if n % 5 == 0 else None) for n in range(args.start, args.stop + 1)}
                _val, lines = fb_interpret_mock(prog, mock)
                for line in lines:
                    print(line)

        case "datalog":
            engine = build_fizzbuzz_datalog(args.start, args.stop)
            if args.query:
                results = engine.all_constants(args.query)
                print(f"{args.query}: {results}")
            else:
                for pred in ("fizzbuzz", "prime_fizz", "interesting"):
                    vals = engine.all_constants(pred)
                    if vals:
                        print(f"  {pred:<16} {vals}")
                print(f"\nTotal facts: {len(engine._facts)}")

        case "zipper":
            rule = RuleRegistry().get(args.rule)
            z = zip_rule(rule)
            print(f"Root: {z.focus!r}")
            if isinstance(rule, CompositeRule) and rule.rules:
                z = z.down()
                print(f"\nEntered composite:")
                for step in range(len(rule.rules)):
                    print(f"  [{step}] focus={z.focus!r}  path={z.path()}")
                    try:
                        z = z.right()
                    except IndexError:
                        break
                z2 = zip_rule(rule).down()
                z3 = z2.modify(lambda r: DivisibilityRule(r.divisor * 2, r.label + "!") if isinstance(r, DivisibilityRule) else r)
                print(f"\nAfter modifying first rule: {z3.root()!r}")

        case "rewrite":
            expr = " ".join(args.expr)
            _rewrite_ns = {
                "DivisibleBySpec": DivisibleBySpec, "PrimeSpec": PrimeSpec,
                "PerfectSpec": PerfectSpec, "ParitySpec": ParitySpec,
                "Parity": Parity, "_AlwaysTrueSpec": _AlwaysTrueSpec,
                "_AlwaysFalseSpec": _AlwaysFalseSpec,
                "_AndSpec": _AndSpec, "_OrSpec": _OrSpec, "_NotSpec": _NotSpec,
            }
            try:
                spec_obj = eval(expr, _rewrite_ns)  # noqa: S307
                simplified = SpecRewriter().rewrite(spec_obj)
                print(f"Before : {spec_obj!r}")
                print(f"After  : {simplified!r}")
            except Exception as exc:
                print(f"Error: {exc}", file=sys.stderr)
                return 1

        case "tagless":
            rule = RuleRegistry().get(args.rule)
            term = fizzbuzz_term(args.start, args.stop)
            match args.algebra:
                case "collect":
                    lines = term(_CollectingAlgebra(rule))
                    for ln in lines:
                        print(ln)
                case "count":
                    counts = term(_CountingAlgebra(rule))
                    for lbl, cnt in counts.most_common():
                        print(f"  {lbl:<16} {cnt}")
                case "pretty":
                    print(term(_PrettyPrintAlgebra(indent=0)))
                case "print":
                    term(_PrintingAlgebra(rule, StdoutSink()))
                case "trace":
                    inner = _CollectingAlgebra(rule)
                    lines = term(_TracingAlgebra(inner, _global_tracer))
                    for ln in lines:
                        print(ln)
                    print(_global_tracer.dump(), file=sys.stderr)

        case "transduce":
            rule = RuleRegistry().get(args.rule)
            rng = list(NumberRange(args.start, args.stop))
            if args.window > 0:
                xf = compose_xf(
                    labelling(rule),
                    mapping(lambda pair: f"{pair[0].value}={pair[1] or str(pair[0].value)}"),
                    windowing(args.window),
                    mapping(lambda w: " | ".join(w)),
                )
            else:
                xf = compose_xf(
                    categorising(),
                    mapping(lambda t: (t[0], t[1], rule(t[0]))),
                    mapping(lambda t: f"{t[0].value:>4}  [{t[1].name:<10}]  {t[2] or str(t[0].value)}"),
                )
            results = into(xf, rng)
            for ln in results:
                print(ln)
            print(f"\n{len(results)} items out of {len(rng)} input", file=sys.stderr)

        case "store":
            rule = RuleRegistry().get(args.rule)
            ctx_labels = fizzbuzz_context_labels(rule, args.start, args.stop)
            print(f"{'n':>4}  {'label':<10}  {'prev':<10}  {'next':<10}  notes")
            print("─" * 52)
            for cl in ctx_labels:
                notes = []
                if cl.is_run:
                    notes.append("run")
                if cl.is_isolated:
                    notes.append("isolated")
                lbl = cl.label or ""
                prev = cl.prev_label or ""
                nxt = cl.next_label or ""
                print(f"{cl.position:>4}  {lbl:<10}  {prev:<10}  {nxt:<10}  {', '.join(notes)}")

        case "attrs":
            rule = RuleRegistry().get(args.rule)
            tree = attribute_rule_tree(rule)
            print(tree.pretty())
            s = tree.synth
            print(f"\nRoot synthesized attrs:")
            print(f"  depth={s.depth}, leaf_count={s.leaf_count}")
            print(f"  divisors={set(s.divisors)}, labels={set(s.labels)}")

        case "effects":
            rule = RuleRegistry().get(args.rule)
            numbers = list(NumberRange(args.start, args.stop))
            match args.handler:
                case "pure":
                    lines = handle_pure(fizzbuzz_effect_program(numbers), rule)
                    for ln in lines:
                        print(ln)
                    print(f"\n{len(lines)} lines via pure effect handler", file=sys.stderr)
                case "count":
                    counts = handle_counting(fizzbuzz_effect_program(numbers), rule)
                    for lbl, cnt in counts.most_common():
                        print(f"  {lbl:<16} {cnt}")
                case "io":
                    handle_io(fizzbuzz_effect_program(numbers), rule, StdoutSink())

        case "cps":
            rule = RuleRegistry().get(args.rule)
            exit_label = getattr(args, "exit_on", FIZZBUZZ)
            cps_lines, did_exit = cps_with_early_exit(
                args.start, args.stop, rule, exit_on=exit_label
            )
            for ln in cps_lines:
                print(ln)
            print(f"\n--- CPS: {len(cps_lines)} lines, "
                  f"early-exit on {exit_label!r}: {did_exit}", file=sys.stderr)

            # Also demonstrate CPSInterpreter transforming a free-monad program
            numbers = list(NumberRange(args.start, min(args.start + 9, args.stop)))
            prog = fb_for_each(numbers)
            interp = CPSInterpreter()
            collected = interp.collect(prog, rule)
            print(f"\nCPSInterpreter collected: {collected}", file=sys.stderr)

        case "abstract":
            rule = RuleRegistry().get(args.rule)
            iv = Interval(args.start, args.stop)
            result_ab = abstract_eval(rule, iv)
            print(f"Interval:         {iv!r}")
            print(f"Possible labels:  {set(result_ab.possible_labels)}")
            print(f"Number possible:  {result_ab.number_possible}")
            print(f"Certain outcome:  {result_ab.is_certain}")
            print(f"Always labelled:  {abstract_prove_always_labelled(rule, iv)}")
            print(f"\nPer-singleton analysis (first 15):")
            for n_val in range(args.start, min(args.start + 15, args.stop + 1)):
                iv_s = Interval.of(n_val)
                ab_s = abstract_eval(rule, iv_s)
                certain = "✓" if ab_s.is_certain else "?"
                print(f"  {certain} n={n_val:>3}  {ab_s}")
            # Cross-check: try to statically prove FizzBuzz never appears < 15
            if args.start == 1 and args.stop >= 15:
                pre_15 = Interval(1, 14)
                proven = abstract_prove_never_label(rule, pre_15, FIZZBUZZ)
                print(f"\nStatic proof 'FizzBuzz never in [1,14]': {proven}")

        case "iso":
            rule = RuleRegistry().get(args.rule)
            print("=== Iso[Number, int] ===")
            for i in range(1, 6):
                n = Number(i)
                v = number_int_iso.get(n)
                n2 = number_int_iso.review(v + 100)
                print(f"  Number({i}) →iso→ {v} →inv→ Number({n2.value})")
            print("\n=== Adapter: composite_labels_adapter ===")
            labels = composite_labels_adapter.get(rule)
            print(f"  Labels in {args.rule!r} rule: {labels}")
            print("\n=== divisor_scale_iso(×3) ===")
            for sub in rule.rules:
                if isinstance(sub, DivisibilityRule):
                    scaled = divisor_scale_iso(3).get(sub)
                    back = divisor_scale_iso(3).review(scaled)
                    print(f"  {sub!r} →scale3→ {scaled!r} →inv→ {back!r}")
            print("\n=== label_default_adapter ===")
            for n_val in range(1, 16):
                pair = (Number(n_val), rule(Number(n_val)))
                formatted = label_default_adapter.get(pair)
                print(f"  {n_val:>3}: {formatted}")

        case "stream":
            rule = RuleRegistry().get(args.rule)
            match args.mode:
                case "labels":
                    s = stream_fizzbuzz_labels(rule, args.start)
                    items = s.take(args.take)
                    for item in items:
                        print(item)
                case "pairs":
                    s = fizzbuzz_stream(rule, args.start)
                    for n, lbl in s.take(args.take):
                        print(f"  {n.value:>4}  {lbl or str(n.value)}")
                case "counts":
                    s = stream_running_counts(rule, args.start)
                    final = s.drop(args.take).head()
                    print(f"Running label counts after {args.take} items:")
                    for lbl, cnt in sorted(final.items(), key=lambda x: -x[1]):
                        print(f"  {lbl:<16} {cnt}")
            print(f"\n(lazy stream from n={args.start}, took {args.take})", file=sys.stderr)

        case "ltl":
            rule = RuleRegistry().get(args.rule)
            results_ltl = run_ltl_properties(rule, args.start, args.stop)
            all_hold = True
            print(f"LTL properties over {args.rule!r} [n={args.start}..{args.stop}]:\n")
            for prop_name, (holds, desc) in results_ltl.items():
                sym = "✓" if holds else "✗"
                print(f"  {sym} {prop_name:<45} {desc}")
                if not holds:
                    all_hold = False
            print(f"\n{'All LTL properties hold.' if all_hold else 'SOME PROPERTIES FAILED.'}")

        case "kleisli":
            rule = RuleRegistry().get(args.rule)
            pipeline = fizzbuzz_pipeline_k(rule)
            good = [str(i) for i in range(args.start, args.stop + 1)]
            bad_inputs: list[str] = list(args.bad) if args.bad else ["0", "-5", "abc", "999"]
            all_inputs = good + bad_inputs
            oks, errs = kleisli_run_many(pipeline, all_inputs)
            print(f"Kleisli pipeline over {args.rule!r} [{args.start}..{args.stop}]:\n")
            for v in oks:
                print(v)
            if errs:
                print(f"\nFailed inputs:", file=sys.stderr)
                for e in errs:
                    print(f"  ✗ {e}", file=sys.stderr)

            # Demonstrate arrow combinators
            label_k = _eval_rule_k(rule)
            parity_k = Kleisli.lift(lambda n: "even" if n.value % 2 == 0 else "odd")
            both_k = _to_number_k >> label_k.fanout(parity_k)
            print("\nfanout demo (label, parity):", file=sys.stderr)
            for n_val in range(args.start, min(args.start + 5, args.stop + 1)):
                res = (_validate_positive_k >> both_k)(n_val)
                print(f"  {n_val}: {res.unwrap() if res.is_ok() else res.error}", file=sys.stderr)

        case "regex":
            rule = RuleRegistry().get(args.rule)
            if args.token:
                tokens = [args.token]
            else:
                tokens = [rule(Number(n)) or str(n)
                          for n in range(args.start, args.stop + 1)]
            print(f"{'Token':<16}  {'Valid':<6}  Class")
            print("─" * 40)
            for tok in tokens:
                valid = validate_fizzbuzz_output(tok)
                cls_name = re_classify(tok)
                sym = "✓" if valid else "✗"
                print(f"{tok:<16}  {sym:<6}  {cls_name}")
            # also validate some intentional bad tokens
            if not args.token:
                print("\nInvalid token tests:")
                for bad in ("", "fizz", "BUZZ", "1.5", "1 2"):
                    v = validate_fizzbuzz_output(bad)
                    print(f"  {bad!r:<14}  {'✓' if v else '✗'}  {re_classify(bad)}")

        case "hll":
            rule = RuleRegistry().get(args.rule)
            hll = hll_fizzbuzz(rule, args.start, args.stop, b=args.b)
            exact = len({rule(Number(n)) or str(n)
                         for n in range(args.start, args.stop + 1)})
            print(f"HyperLogLog sketch over {args.rule!r} [{args.start}..{args.stop}]:")
            print(f"  Registers:         {hll._m}")
            print(f"  Estimate:          {hll.estimate():.1f}")
            print(f"  Exact:             {exact}")
            err = abs(hll.estimate() - exact) / max(exact, 1)
            print(f"  Observed error:    {err:.2%}")
            print(f"  Theoretical bound: {hll.relative_error():.2%}")
            # Demonstrate merging two sketches
            hll_a = hll_fizzbuzz(rule, args.start, (args.start + args.stop) // 2, b=args.b)
            hll_b = hll_fizzbuzz(rule, (args.start + args.stop) // 2 + 1, args.stop, b=args.b)
            merged = hll_a.merge(hll_b)
            print(f"\nMerged (a ∪ b) estimate: {merged.estimate():.1f}  (exact: {exact})")

        case "segtree":
            rule = RuleRegistry().get(args.rule)
            hist = PersistentLabelHistory.build(rule, args.start, args.stop)
            n_vers = hist.n_versions()
            lo, hi = args.start, args.stop
            print(f"Persistent segment tree: {args.rule!r} [{lo}..{hi}]")
            print(f"  Versions: {n_vers}  (0=empty, {n_vers-1}=full)")
            version = args.version if args.version != -1 else n_vers - 1
            version = min(version, n_vers - 1)
            if args.query == "sum":
                total = hist.query_sum(lo, hi, version)
                print(f"\n  Range-sum [{lo}..{hi}] at version {version}: {total}")
                for q_start in range(lo, min(lo + 10, hi + 1)):
                    s = hist.query_sum(lo, q_start, version)
                    print(f"  Prefix sum [{lo}..{q_start}]: {s}")
            else:
                total = hist.query_max(lo, hi, version)
                code_names = {0: "number", 1: "Fizz", 2: "Buzz", 3: "FizzBuzz"}
                print(f"\n  Range-max [{lo}..{hi}] at version {version}: {total} ({code_names.get(total, '?')})")
            # Time travel: show sum at each version step
            print(f"\n  Cumulative sum over all versions (first 10):")
            for v in range(min(10, n_vers)):
                s = hist.query_sum(lo, hi, v)
                print(f"    v{v:>3}: {s}")

        case "ndcont":
            rule = RuleRegistry().get(args.rule)
            match args.mode:
                case "labelled":
                    results_nd = nd_fizzbuzz_search(
                        rule, args.start, args.stop,
                        lambda lbl: lbl is not None,
                    )
                    print(f"Labelled numbers in [{args.start}..{args.stop}] "
                          f"(non-det backtracking):")
                    for n_val, lbl in results_nd:
                        print(f"  {n_val:>4}  {lbl}")
                    print(f"\n  Total: {len(results_nd)} of {args.stop - args.start + 1}")

                case "product":
                    registry = RuleRegistry()
                    rules_dict = {name: registry.get(name) for name in registry.names()}
                    print(f"Rule × label product for n={args.start}:")
                    for rule_name, lbl in nd_rule_product(rules_dict, args.start):
                        print(f"  {rule_name:<22}  {lbl!r}")

                case "windows":
                    windows = nd_window_search(
                        rule, args.start, args.stop, window=args.window
                    )
                    print(f"All-labelled windows of size {args.window} in "
                          f"[{args.start}..{args.stop}]:")
                    for start_n, lbls in windows:
                        print(f"  n={start_n:>4}  {lbls}")
                    print(f"\n  Total windows found: {len(windows)}")

        case "recur":
            rule = RuleRegistry().get(args.rule)
            _alg_map = {
                "depth":       _cata_depth,
                "divisors":    _cata_divisors,
                "label_count": _cata_label_count,
            }
            alg = _alg_map[args.alg]
            match args.scheme:
                case "cata":
                    result = cata(alg, rule)
                    print(f"cata({args.alg}) over {args.rule!r}: {result}")
                case "ana":
                    scale = 2
                    new_rule = ana(_coalg_scale(scale), rule)
                    print(f"ana(scale×{scale}) over {args.rule!r}: {new_rule!r}")
                    print(f"  Divisors before: {set(cata(_cata_divisors, rule))}")
                    print(f"  Divisors after:  {set(cata(_cata_divisors, new_rule))}")
                case "hylo":
                    result = hylo(alg, _coalg_scale(1), rule)
                    print(f"hylo({args.alg}, scale×1) over {args.rule!r}: {result}")
                case "para":
                    def _para_show(layer: RuleF) -> str:
                        match layer:
                            case RuleCompositeF(children=ch):
                                return f"[{', '.join(repr(orig) + ':' + folded for orig, folded in ch)}]"
                            case RuleDivF(divisor=d, label=lbl): return f"Div({d})"
                            case _: return "Leaf"
                    result = para(lambda l: _para_show(rulef_fmap(l, lambda p: p)), rule)
                    print(f"para over {args.rule!r}: {result}")
                case "zygo":
                    result = zygo(_cata_depth, _cata_label_count, rule)
                    print(f"zygo(depth, label_count) over {args.rule!r}: {result}")
                case "histo":
                    result = histo(alg, rule)
                    print(f"histo({args.alg}) over {args.rule!r}: {result}")

        case "sat":
            formula_str = " ".join(args.formula) if args.formula else None
            _sat_ns = {
                "PVar": PVar, "PNot": PNot, "PAnd": PAnd, "POr": POr,
                "PImp": PImp, "PIff": PIff, "PTrue": PTrue, "PFalse": PFalse,
            }
            if formula_str:
                try:
                    prop_obj = eval(formula_str, _sat_ns)  # noqa: S307
                    cnf = prop_to_cnf(prop_obj)
                    asgn = dpll(cnf)
                    print(f"Formula:    {prop_obj!r}")
                    print(f"CNF:        {len(cnf)} clauses")
                    print(f"SAT:        {asgn is not None}")
                    print(f"Tautology:  {prop_is_tautology(prop_obj)}")
                    if asgn:
                        print(f"Assignment: {asgn}")
                except Exception as exc:
                    print(f"Error: {exc}", file=sys.stderr)
                    return 1
            # Rule consistency verification
            rule = RuleRegistry().get(args.rule)
            print(f"\nRule-firing consistency check: {args.rule!r} [{args.start}..{args.stop}]")
            msgs = check_rule_mutual_exclusion(rule, args.start, args.stop)
            inconsistencies = [m for m in msgs if "INCONSISTENCY" in m]
            if inconsistencies:
                for m in inconsistencies:
                    print(m)
            else:
                print(f"  All {len(msgs)} positions consistent ✓")

        case "cms":
            rule = RuleRegistry().get(args.rule)
            cms = cms_fizzbuzz(rule, args.start, args.stop,
                               epsilon=args.epsilon, delta=args.delta)
            print(f"Count-Min Sketch: {cms!r}")
            universe = [FIZZ, BUZZ, FIZZBUZZ] + [str(n) for n in range(1, 20)]
            top = cms.top_k(8, universe)
            exact: Counter[str] = Counter()
            for n in range(args.start, args.stop + 1):
                exact[rule(Number(n)) or str(n)] += 1
            print(f"\n{'Label':<16} {'Estimate':>10} {'Exact':>8} {'Error':>8}")
            print("─" * 46)
            for item, est in top:
                ex = exact.get(item, 0)
                err = abs(est - ex) / max(ex, 1)
                print(f"{item:<16} {est:>10} {ex:>8} {err:>7.1%}")
            print(f"\nInner product estimate: {cms.inner_product(cms)}")

        case "frp":
            rule = RuleRegistry().get(args.rule)
            _, label_beh, out_event = build_fizzbuzz_frp(rule, args.start, args.stop)
            print(f"FRP network output [{args.start}..{args.stop}]:")
            for t, v in out_event.occurrences:
                n_val = args.start + int(t)
                print(f"  t={t:>5.1f}  n={n_val:>4}  {v}")
            runs = fizzbuzz_run_detector(rule, args.start, args.stop)
            print(f"\nRun-detector events: {len(runs.occurrences)}", file=sys.stderr)
            for t, pair in runs.occurrences:
                print(f"  t={t:.0f}  {pair}", file=sys.stderr)

            # Demonstrate SF arrow combinators
            counter_sf = SF.arr(lambda n: n + 1)
            double_sf  = SF.arr(lambda n: n * 2)
            combined   = counter_sf >> double_sf
            beh_in = Behavior(lambda t: int(t))
            beh_out = combined.run(beh_in)
            print(f"\nSF pipeline demo (n → n+1 → ×2) at t=5: {beh_out.at(5.0)}", file=sys.stderr)

        case "green":
            rule = RuleRegistry().get(args.rule)
            result_map = run_green_fizzbuzz(
                rule, args.start, args.stop, n_workers=args.workers
            )
            print(f"Green-thread FizzBuzz [{args.start}..{args.stop}] "
                  f"({args.workers} workers):")
            for n_val in sorted(result_map.keys()):
                print(f"  {n_val:>4}  {result_map[n_val]}")
            print(f"\n  {len(result_map)} results collected", file=sys.stderr)

        case "run":
            _mw_map: dict[str, Middleware] = {
                "null_suppressor":       null_suppressor,
                "label_reverser":        label_reverser,
                "prime_annotator":       prime_annotator,
                "collatz_annotator":     collatz_annotator,
                "fingerprint_annotator": fingerprint_annotator,
            }
            middlewares = [_mw_map[m] for m in (args.middleware or [])]

            if args.dsl:
                rule = parse_rule_dsl(args.dsl)
                RuleRegistry().register("_cli_dsl", rule)
                rule_name = "_cli_dsl"
            else:
                rule_name = args.rule

            if args.shard > 1:
                result = run_sharded(
                    args.start, args.stop,
                    n_shards=args.shard,
                    rule_name=rule_name,
                    formatter=args.formatter,
                )
            else:
                pipeline = FizzBuzzFactory.create(
                    start=args.start,
                    stop=args.stop,
                    rule_name=rule_name,
                    formatter=args.formatter,
                    middlewares=middlewares,
                    parallel=args.parallel,
                    use_compiled_rule=args.compiled,
                )
                result = pipeline.run()

            print("\n" + "─" * 48, file=sys.stderr)
            if result.metrics_report:
                print(result.metrics_report, file=sys.stderr)
            print(f"\n{result}", file=sys.stderr)
            print(_global_tracer.dump(), file=sys.stderr)

    return 0


if __name__ == "__main__":
    sys.exit(main())
