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
E = TypeVar("E")
T_co = TypeVar("T_co", covariant=True)
T_contra = TypeVar("T_contra", contravariant=True)
N = TypeVar("N", int, float)
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

            case "help":
                print(
                    "  run / go                     — execute with current settings\n"
                    "  set <k> <v>                  — start/stop/rule/formatter/mw\n"
                    "  clear                        — clear middleware stack\n"
                    "  explain                      — print rule trees\n"
                    "  analyse                      — static label-frequency analysis\n"
                    "  rules                        — list registered rules\n"
                    "  status                       — show current settings\n"
                    "  dsl <spec>                   — define rule inline\n"
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
