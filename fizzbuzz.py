#!/usr/bin/env python3
"""Enterprise-grade FizzBuzz™ — a scalable, extensible, observable, cloud-ready solution.

Architecture overview:

  NumberRange ──► FizzBuzzPipeline ──► OutputSink
                       │
              RuleRegistry (singleton)
                       │
              CompositeRule (chain-of-responsibility)
                       │
              Formatter (strategy, decorator-wrapped)
                       │
              MetricsCollector (observer, thread-safe)
"""

from __future__ import annotations

import abc
import asyncio
import contextlib
import dataclasses
import enum
import functools
import hashlib
import inspect
import itertools
import logging
import operator
import os
import queue
import sys
import threading
import time
import traceback
import types
import weakref
from collections import Counter, defaultdict, deque
from collections.abc import (
    AsyncGenerator,
    AsyncIterator,
    Callable,
    Generator,
    Iterable,
    Iterator,
    Sequence,
)
from contextlib import asynccontextmanager, contextmanager
from typing import (
    TYPE_CHECKING,
    Annotated,
    Any,
    ClassVar,
    Final,
    Generic,
    Literal,
    Optional,
    Protocol,
    TypeAlias,
    TypeVar,
    overload,
    runtime_checkable,
)

if TYPE_CHECKING:
    pass

logging.basicConfig(
    level=logging.DEBUG,
    format="[%(asctime)s] [%(levelname)-8s] %(name)s (%(threadName)s): %(message)s",
    datefmt="%H:%M:%S.%f",
    stream=sys.stderr,
)
log = logging.getLogger("fizzbuzz.core")

T = TypeVar("T")
T_co = TypeVar("T_co", covariant=True)
T_contra = TypeVar("T_contra", contravariant=True)
N = TypeVar("N", int, float)
LabelT: TypeAlias = str | None

FIZZ: Final = "Fizz"
BUZZ: Final = "Buzz"
FIZZBUZZ: Final = FIZZ + BUZZ
_SENTINEL: Final = object()


# ---------------------------------------------------------------------------
# Decorators / meta-infrastructure
# ---------------------------------------------------------------------------

def logged(fn: Callable[..., T]) -> Callable[..., T]:
    """Decorator that traces entry/exit of any callable at DEBUG level."""
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


class _SingletonMeta(type):
    """Thread-safe singleton metaclass."""
    _instances: ClassVar[dict[type, Any]] = {}
    _lock: ClassVar[threading.Lock] = threading.Lock()

    def __call__(cls, *args: Any, **kwargs: Any) -> Any:
        with cls._lock:
            if cls not in cls._instances:
                cls._instances[cls] = super().__call__(*args, **kwargs)
        return cls._instances[cls]


class _RegistryMeta(type):
    """Metaclass that auto-registers subclasses by their `name` class attribute."""
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


# ---------------------------------------------------------------------------
# Event bus (observer pattern)
# ---------------------------------------------------------------------------

EventHandler: TypeAlias = Callable[[str, Any], None]


class EventBus(metaclass=_SingletonMeta):
    """Process-wide publish/subscribe event bus."""

    def __init__(self) -> None:
        self._handlers: defaultdict[str, list[weakref.ref[EventHandler]]] = defaultdict(list)
        self._lock = threading.RLock()
        self._log = logging.getLogger("fizzbuzz.events")

    def subscribe(self, event: str, handler: EventHandler) -> None:
        with self._lock:
            self._handlers[event].append(weakref.ref(handler))
        self._log.debug("Subscribed %r to %r", handler, event)

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
                    self._log.exception("Handler %r raised on event %r", handler, event)
        with self._lock:
            self._handlers[event] = live


# ---------------------------------------------------------------------------
# Domain model
# ---------------------------------------------------------------------------

class Parity(enum.Enum):
    ODD = "odd"
    EVEN = "even"

    @classmethod
    def of(cls, n: int) -> Parity:
        return cls.EVEN if n % 2 == 0 else cls.ODD


class NumberCategory(enum.Flag):
    NONE      = 0
    FIZZ      = enum.auto()
    BUZZ      = enum.auto()
    FIZZBUZZ  = FIZZ | BUZZ
    PRIME     = enum.auto()


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    return all(n % i for i in range(3, int(n**0.5) + 1, 2))


@functools.lru_cache(maxsize=None)
def _cached_is_prime(n: int) -> bool:
    return _is_prime(n)


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
        return _cached_is_prime(self.value)

    @functools.cached_property  # type: ignore[misc]
    def digit_sum(self) -> int:
        return sum(int(d) for d in str(abs(self.value)))

    @functools.cached_property  # type: ignore[misc]
    def fingerprint(self) -> str:
        return hashlib.sha256(str(self.value).encode()).hexdigest()[:8]

    def is_divisible_by(self, divisor: int) -> bool:
        return self.value % divisor == 0

    def __str__(self) -> str:
        return str(self.value)

    def __repr__(self) -> str:
        flags = []
        if self.is_prime:
            flags.append("prime")
        if self.parity == Parity.EVEN:
            flags.append("even")
        return f"Number({self.value}{'[' + ','.join(flags) + ']' if flags else ''})"


# ---------------------------------------------------------------------------
# Rule engine — chain of responsibility + visitor
# ---------------------------------------------------------------------------

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
    """Emits a label when an arbitrary predicate is satisfied."""
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


class RuleExplainerVisitor(RuleVisitor):
    """Produces a human-readable description of a rule tree."""

    def __init__(self) -> None:
        self._lines: list[str] = []

    def visit_divisibility(self, rule: DivisibilityRule) -> None:
        self._lines.append(f"  divisible_by({rule.divisor}) → {rule.label!r}  [called {rule._call_count}×]")

    def visit_composite(self, rule: CompositeRule) -> None:
        self._lines.append("CompositeRule:")
        for child in rule.rules:
            child.accept(self)

    def visit_predicate(self, rule: PredicateRule) -> None:
        self._lines.append(f"  predicate({rule.description}) → {rule.label!r}")

    def explain(self) -> str:
        return "\n".join(self._lines)


class RuleBuilder:
    """Fluent, validated builder for CompositeRule."""

    def __init__(self) -> None:
        self._rules: list[VisitableRule] = []

    def when_divisible_by(self, divisor: int, label: str) -> RuleBuilder:
        if divisor == 0:
            raise ValueError("divisor cannot be zero")
        self._rules.append(DivisibilityRule(divisor, label))
        return self

    def when(self, predicate: Callable[[Number], bool], label: str, *, description: str = "<custom>") -> RuleBuilder:
        self._rules.append(PredicateRule(predicate, label, description))
        return self

    def build(self) -> CompositeRule:
        if not self._rules:
            raise RuntimeError("Cannot build an empty rule")
        return CompositeRule(tuple(self._rules))


# ---------------------------------------------------------------------------
# Rule registry
# ---------------------------------------------------------------------------

class RuleRegistry(metaclass=_SingletonMeta):
    """Named, versioned store of CompositeRule instances."""

    def __init__(self) -> None:
        self._store: dict[str, CompositeRule] = {}
        self._log = logging.getLogger("fizzbuzz.registry")

    def register(self, name: str, rule: CompositeRule) -> None:
        self._store[name] = rule
        self._log.debug("Registered rule %r", name)

    def get(self, name: str) -> CompositeRule:
        try:
            return self._store[name]
        except KeyError:
            raise KeyError(f"No rule named {name!r}. Available: {sorted(self._store)}")

    def names(self) -> list[str]:
        return sorted(self._store)


def _bootstrap_registry() -> None:
    registry = RuleRegistry()
    registry.register(
        "classic",
        RuleBuilder()
        .when_divisible_by(3, FIZZ)
        .when_divisible_by(5, BUZZ)
        .build(),
    )
    registry.register(
        "extended",
        RuleBuilder()
        .when_divisible_by(3, FIZZ)
        .when_divisible_by(5, BUZZ)
        .when_divisible_by(7, "Bazz")
        .when(lambda n: n.is_prime, "✦", description="is_prime")
        .build(),
    )


_bootstrap_registry()


# ---------------------------------------------------------------------------
# Formatter strategy — with decorator chain support
# ---------------------------------------------------------------------------

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
            "digit_sum": number.digit_sum,
            "fingerprint": number.fingerprint,
        })


class AnsiFormatter(FormatterDecorator):
    """Wraps output in ANSI colour codes based on category."""
    name = "ansi"

    _COLOURS: ClassVar[dict[str, str]] = {
        FIZZ:     "\033[94m",   # blue
        BUZZ:     "\033[92m",   # green
        FIZZBUZZ: "\033[95m",   # magenta
    }
    _RESET = "\033[0m"

    def format(self, number: Number, label: LabelT) -> str:
        text = self._delegate.format(number, label)
        colour = self._COLOURS.get(label or "", "")
        return f"{colour}{text}{self._RESET}" if colour else text


# ---------------------------------------------------------------------------
# Metrics — thread-safe observer
# ---------------------------------------------------------------------------

@dataclasses.dataclass
class Snapshot:
    timestamp: float
    label: LabelT
    number: int


class MetricsCollector:
    """Thread-safe rolling window of labelling events."""

    def __init__(self, window: int = 1000) -> None:
        self._lock = threading.Lock()
        self._counter: Counter[str] = Counter()
        self._history: deque[Snapshot] = deque(maxlen=window)
        self._total = 0

    def record(self, number: Number, label: LabelT) -> None:
        with self._lock:
            self._total += 1
            key = label or "<number>"
            self._counter[key] += 1
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
        lines = [
            f"Total processed : {self.total}",
            f"Label rate      : {self.label_rate():.1%}",
            "Top labels:",
        ]
        for label, count in self.top_labels():
            lines.append(f"  {label:<16} {count:>6}  ({count/self.total:.1%})")
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Output sinks
# ---------------------------------------------------------------------------

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
    """Accumulates output in memory; useful for testing."""

    def __init__(self) -> None:
        self._buf: list[str] = []

    def write(self, line: str) -> None:
        self._buf.append(line)

    def flush(self) -> None:
        pass

    @property
    def lines(self) -> list[str]:
        return list(self._buf)


class AsyncQueueSink(OutputSink):
    """Pushes output into an asyncio.Queue for async consumers."""

    def __init__(self, q: asyncio.Queue[str]) -> None:
        self._q = q
        self._loop = asyncio.get_event_loop()

    def write(self, line: str) -> None:
        self._loop.call_soon_threadsafe(self._q.put_nowait, line)

    def flush(self) -> None:
        pass


# ---------------------------------------------------------------------------
# Range abstraction
# ---------------------------------------------------------------------------

class NumberRange:
    """An inclusive integer range producing Number instances."""

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

    def chunked(self, size: int) -> Iterator[list[Number]]:
        it = iter(self)
        while chunk := list(itertools.islice(it, size)):
            yield chunk

    def __repr__(self) -> str:
        return f"NumberRange({self.start!r}, {self.stop!r}, step={self.step!r})"


# ---------------------------------------------------------------------------
# Pipeline — with middleware support
# ---------------------------------------------------------------------------

Middleware: TypeAlias = Callable[[Number, LabelT], LabelT]


@dataclasses.dataclass
class PipelineConfig:
    range: NumberRange
    rule: CompositeRule
    formatter: Formatter
    sink: OutputSink = dataclasses.field(default_factory=StdoutSink)
    middlewares: list[Middleware] = dataclasses.field(default_factory=list)
    metrics: bool = True
    parallel: bool = False
    chunk_size: int = 256


@dataclasses.dataclass(frozen=True)
class PipelineResult:
    numbers_processed: int
    labelled: int
    unlabelled: int
    elapsed_seconds: float
    metrics_report: str = ""

    @property
    def label_rate(self) -> float:
        return self.labelled / self.numbers_processed if self.numbers_processed else 0.0

    @property
    def throughput(self) -> float:
        return self.numbers_processed / self.elapsed_seconds if self.elapsed_seconds else float("inf")

    def __str__(self) -> str:
        return (
            f"{self.numbers_processed} numbers in {self.elapsed_seconds*1000:.3f}ms "
            f"({self.label_rate:.1%} labelled, {self.throughput:,.0f} n/s)"
        )


class FizzBuzzPipeline:
    """Processes a NumberRange through a configurable rule/middleware/formatter stack."""

    def __init__(self, config: PipelineConfig) -> None:
        self._cfg = config
        self._metrics = MetricsCollector() if config.metrics else None
        self._bus = EventBus()
        self._log = logging.getLogger("fizzbuzz.pipeline")

    def _apply_middlewares(self, number: Number, label: LabelT) -> LabelT:
        for mw in self._cfg.middlewares:
            label = mw(number, label)
        return label

    def _process_one(self, number: Number) -> None:
        label = self._cfg.rule(number)
        label = self._apply_middlewares(number, label)
        if self._metrics:
            self._metrics.record(number, label)
        output = self._cfg.formatter.format(number, label)
        self._cfg.sink.write(output)
        self._bus.publish("number.processed", {"number": number, "label": label})

    def run(self) -> PipelineResult:
        self._log.info("Pipeline starting: %r", self._cfg.range)
        self._bus.publish("pipeline.start", {"range": self._cfg.range})
        t0 = time.perf_counter()

        with self._cfg.sink.open():
            if self._cfg.parallel:
                self._run_parallel()
            else:
                for number in self._cfg.range:
                    self._process_one(number)

        elapsed = time.perf_counter() - t0
        total = len(self._cfg.range)
        labelled = self._metrics._counter.get("<number>", 0) if self._metrics else 0
        labelled = total - labelled

        result = PipelineResult(
            numbers_processed=total,
            labelled=labelled,
            unlabelled=total - labelled,
            elapsed_seconds=elapsed,
            metrics_report=self._metrics.report() if self._metrics else "",
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
        """Async variant — useful when the sink is an AsyncQueueSink."""
        loop = asyncio.get_running_loop()
        return await loop.run_in_executor(None, self.run)


# ---------------------------------------------------------------------------
# Factory / DI container
# ---------------------------------------------------------------------------

class _DIContainer:
    """Minimal dependency-injection container with scoped bindings."""

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
    """Assembles FizzBuzzPipeline from high-level parameters via the DI container."""

    _FORMATTERS: ClassVar[dict[str, type[Formatter]]] = {
        "default": DefaultFormatter,
        "upper":   UpperCaseFormatter,
        "json":    JsonFormatter,
        "ansi":    AnsiFormatter,
        "padded":  PaddedFormatter,
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
            )
        )

    @classmethod
    def _build_formatter(cls, spec: str) -> Formatter:
        """Parse a '+'-joined formatter chain, e.g. 'default+upper+ansi'."""
        names = spec.split("+")
        base_name = names[0]
        base_cls = cls._FORMATTERS.get(base_name)
        if base_cls is None:
            raise ValueError(f"Unknown formatter {base_name!r}. Choose from: {sorted(cls._FORMATTERS)}")

        fmt: Formatter = base_cls()
        for name in names[1:]:
            decorator_cls = cls._FORMATTERS.get(name)
            if decorator_cls is None:
                raise ValueError(f"Unknown formatter {name!r}.")
            if not issubclass(decorator_cls, FormatterDecorator):
                raise ValueError(f"{name!r} is not a decorator formatter.")
            decorator = decorator_cls.__new__(decorator_cls)
            decorator._delegate = fmt
            fmt = decorator

        return fmt


# ---------------------------------------------------------------------------
# Built-in middlewares
# ---------------------------------------------------------------------------

def null_suppressor(number: Number, label: LabelT) -> LabelT:
    """Suppresses output for numbers whose string repr contains '0'."""
    return None if "0" in str(number.value) else label


def label_reverser(number: Number, label: LabelT) -> LabelT:
    return label[::-1] if label else label


def prime_annotator(number: Number, label: LabelT) -> LabelT:
    if number.is_prime:
        return f"[{label}]" if label else f"[{number.value}]"
    return label


# ---------------------------------------------------------------------------
# Async streaming API
# ---------------------------------------------------------------------------

async def stream_fizzbuzz(
    start: int = 1,
    stop: int = 100,
    rule_name: str = "classic",
    delay: float = 0.0,
) -> AsyncGenerator[tuple[Number, LabelT], None]:
    """Async generator that yields (Number, label) pairs with optional throttling."""
    rule = RuleRegistry().get(rule_name)
    for number in NumberRange(start, stop):
        label = rule(number)
        yield number, label
        if delay:
            await asyncio.sleep(delay)


# ---------------------------------------------------------------------------
# Self-describing rule explainer CLI subcommand
# ---------------------------------------------------------------------------

def explain_rules() -> None:
    registry = RuleRegistry()
    for name in registry.names():
        rule = registry.get(name)
        visitor = RuleExplainerVisitor()
        rule.accept(visitor)
        print(f"\nRule: {name!r}\n{visitor.explain()}")


# ---------------------------------------------------------------------------
# Entrypoint
# ---------------------------------------------------------------------------

def main(argv: Sequence[str] = sys.argv[1:]) -> int:
    import argparse

    parser = argparse.ArgumentParser(
        description="Enterprise FizzBuzz™",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    sub = parser.add_subparsers(dest="cmd")

    run_p = sub.add_parser("run", help="Run FizzBuzz")
    run_p.add_argument("--start",      type=int,  default=1)
    run_p.add_argument("--stop",       type=int,  default=100)
    run_p.add_argument("--rule",       default="classic", help=f"Rule set (default: classic)")
    run_p.add_argument("--formatter",  default="default",
                       help="Formatter chain, e.g. default+ansi (default: default)")
    run_p.add_argument("--parallel",   action="store_true")
    run_p.add_argument("--middleware", nargs="*", choices=["null_suppressor", "label_reverser", "prime_annotator"],
                       default=[], metavar="MW")

    explain_p = sub.add_parser("explain", help="Print rule explanations")

    args = parser.parse_args(argv)
    cmd = args.cmd or "run"

    if cmd == "explain":
        explain_rules()
        return 0

    _mw_map: dict[str, Middleware] = {
        "null_suppressor": null_suppressor,
        "label_reverser":  label_reverser,
        "prime_annotator": prime_annotator,
    }
    middlewares = [_mw_map[m] for m in (args.middleware or [])]

    pipeline = FizzBuzzFactory.create(
        start=args.start,
        stop=args.stop,
        rule_name=args.rule,
        formatter=args.formatter,
        middlewares=middlewares,
        parallel=args.parallel,
    )

    result = pipeline.run()

    print("\n" + "─" * 40, file=sys.stderr)
    print(result.metrics_report, file=sys.stderr)
    print(f"\n{result}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
