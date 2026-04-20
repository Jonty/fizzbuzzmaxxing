#!/usr/bin/env python3
"""Enterprise-grade FizzBuzz™ — a scalable, extensible, cloud-ready solution."""

from __future__ import annotations

import abc
import dataclasses
import enum
import functools
import itertools
import logging
import operator
import sys
import time
from collections.abc import Callable, Generator, Iterable, Iterator, Sequence
from contextlib import contextmanager
from typing import Any, ClassVar, Final, Generic, Protocol, TypeVar, runtime_checkable

logging.basicConfig(level=logging.DEBUG, format="[%(levelname)s] %(name)s: %(message)s")
log = logging.getLogger("fizzbuzz.core")

T = TypeVar("T")
N = TypeVar("N", int, float)

FIZZ: Final = "Fizz"
BUZZ: Final = "Buzz"
FIZZBUZZ: Final = FIZZ + BUZZ


# ---------------------------------------------------------------------------
# Domain model
# ---------------------------------------------------------------------------

class Parity(enum.Enum):
    ODD = "odd"
    EVEN = "even"

    @classmethod
    def of(cls, n: int) -> Parity:
        return cls.EVEN if n % 2 == 0 else cls.ODD


@dataclasses.dataclass(frozen=True, order=True)
class Number:
    value: int

    def __post_init__(self) -> None:
        if not isinstance(self.value, int):
            raise TypeError(f"Expected int, got {type(self.value).__name__}")

    @property
    def parity(self) -> Parity:
        return Parity.of(self.value)

    def is_divisible_by(self, divisor: int) -> bool:
        return self.value % divisor == 0

    def __str__(self) -> str:
        return str(self.value)


# ---------------------------------------------------------------------------
# Rule engine
# ---------------------------------------------------------------------------

@runtime_checkable
class Rule(Protocol):
    """A callable that maps a Number to an optional string label."""
    def __call__(self, number: Number) -> str | None: ...


@dataclasses.dataclass(frozen=True)
class DivisibilityRule:
    """Emits a label when `number` is divisible by `divisor`."""
    divisor: int
    label: str

    def __call__(self, number: Number) -> str | None:
        return self.label if number.is_divisible_by(self.divisor) else None


@dataclasses.dataclass(frozen=True)
class CompositeRule:
    """Concatenates the output of multiple rules; returns None if all are silent."""
    rules: tuple[Rule, ...]

    def __call__(self, number: Number) -> str | None:
        parts = [r(number) for r in self.rules]
        result = "".join(p for p in parts if p is not None)
        return result or None


class RuleBuilder:
    """Fluent builder for CompositeRule."""

    def __init__(self) -> None:
        self._rules: list[Rule] = []

    def when_divisible_by(self, divisor: int, label: str) -> RuleBuilder:
        self._rules.append(DivisibilityRule(divisor, label))
        return self

    def build(self) -> CompositeRule:
        return CompositeRule(tuple(self._rules))


# ---------------------------------------------------------------------------
# Formatter strategy
# ---------------------------------------------------------------------------

class Formatter(abc.ABC):
    @abc.abstractmethod
    def format(self, number: Number, label: str | None) -> str: ...


class DefaultFormatter(Formatter):
    def format(self, number: Number, label: str | None) -> str:
        return label if label is not None else str(number)


class UpperCaseFormatter(Formatter):
    _delegate: Formatter

    def __init__(self, delegate: Formatter | None = None) -> None:
        self._delegate = delegate or DefaultFormatter()

    def format(self, number: Number, label: str | None) -> str:
        return self._delegate.format(number, label).upper()


class JsonFormatter(Formatter):
    def format(self, number: Number, label: str | None) -> str:
        import json
        return json.dumps({"n": number.value, "label": label, "parity": number.parity.value})


# ---------------------------------------------------------------------------
# Range abstraction
# ---------------------------------------------------------------------------

class NumberRange:
    """An inclusive integer range that yields Number instances."""

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

    def __repr__(self) -> str:
        return f"NumberRange({self.start}, {self.stop}, step={self.step})"


# ---------------------------------------------------------------------------
# Pipeline
# ---------------------------------------------------------------------------

@dataclasses.dataclass
class PipelineConfig:
    range: NumberRange
    rule: CompositeRule
    formatter: Formatter
    output: Callable[[str], None] = dataclasses.field(default=print)
    metrics: bool = True


class FizzBuzzPipeline:
    """Processes a NumberRange through a Rule and emits formatted output."""

    def __init__(self, config: PipelineConfig) -> None:
        self._cfg = config
        self._log = logging.getLogger("fizzbuzz.pipeline")

    def run(self) -> PipelineResult:
        self._log.info("Pipeline starting: %r", self._cfg.range)
        stats: dict[str, int] = {"total": 0, "labelled": 0, "unlabelled": 0}
        t0 = time.perf_counter()

        for number in self._cfg.range:
            label = self._cfg.rule(number)
            output = self._cfg.formatter.format(number, label)
            self._cfg.output(output)
            stats["total"] += 1
            if label:
                stats["labelled"] += 1
            else:
                stats["unlabelled"] += 1

        elapsed = time.perf_counter() - t0
        result = PipelineResult(
            numbers_processed=stats["total"],
            labelled=stats["labelled"],
            unlabelled=stats["unlabelled"],
            elapsed_seconds=elapsed,
        )
        self._log.info("Pipeline complete: %s", result)
        return result


@dataclasses.dataclass(frozen=True)
class PipelineResult:
    numbers_processed: int
    labelled: int
    unlabelled: int
    elapsed_seconds: float

    @property
    def label_rate(self) -> float:
        return self.labelled / self.numbers_processed if self.numbers_processed else 0.0

    def __str__(self) -> str:
        return (
            f"{self.numbers_processed} numbers in {self.elapsed_seconds*1000:.3f}ms "
            f"({self.label_rate:.1%} labelled)"
        )


# ---------------------------------------------------------------------------
# Factory / DI
# ---------------------------------------------------------------------------

class FizzBuzzFactory:
    """Assembles a ready-to-run FizzBuzzPipeline from high-level parameters."""

    _FORMATTERS: ClassVar[dict[str, type[Formatter]]] = {
        "default": DefaultFormatter,
        "upper": UpperCaseFormatter,
        "json": JsonFormatter,
    }

    @classmethod
    def create(
        cls,
        *,
        start: int = 1,
        stop: int = 100,
        formatter: str = "default",
        output: Callable[[str], None] = print,
    ) -> FizzBuzzPipeline:
        rule = (
            RuleBuilder()
            .when_divisible_by(3, FIZZ)
            .when_divisible_by(5, BUZZ)
            .build()
        )
        fmt_cls = cls._FORMATTERS.get(formatter)
        if fmt_cls is None:
            raise ValueError(f"Unknown formatter {formatter!r}. Choose from: {list(cls._FORMATTERS)}")
        return FizzBuzzPipeline(
            PipelineConfig(
                range=NumberRange(start, stop),
                rule=rule,
                formatter=fmt_cls(),
                output=output,
            )
        )


# ---------------------------------------------------------------------------
# Entrypoint
# ---------------------------------------------------------------------------

def main(argv: Sequence[str] = sys.argv[1:]) -> int:
    import argparse

    parser = argparse.ArgumentParser(description="Enterprise FizzBuzz™")
    parser.add_argument("--start", type=int, default=1)
    parser.add_argument("--stop", type=int, default=100)
    parser.add_argument("--formatter", choices=["default", "upper", "json"], default="default")
    args = parser.parse_args(argv)

    pipeline = FizzBuzzFactory.create(
        start=args.start,
        stop=args.stop,
        formatter=args.formatter,
    )
    result = pipeline.run()
    log.info("Result: %s", result)
    return 0


if __name__ == "__main__":
    sys.exit(main())
