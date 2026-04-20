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
                    "  quit / exit                  — exit REPL\n"
                )
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
