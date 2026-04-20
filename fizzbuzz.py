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

    # ── rewrite ───────────────────────────────────────────────────────────────
    rw_p = sub.add_parser("rewrite", help="Algebraically simplify a Spec expression")
    rw_p.add_argument("expr", nargs="+")

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
