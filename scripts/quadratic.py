"""Small exact real quadratic-field implementation; standard library only.

All decisions use rational arithmetic, not floating-point approximations.
Decimal conversion is for human-readable output and an initial floor guess only;
that guess is corrected using exact comparisons. Not a formal proof checker.
"""
from __future__ import annotations
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
from functools import total_ordering
from math import isqrt
from typing import Union

Rational = Union[int, Fraction]

@total_ordering
@dataclass(frozen=True, eq=False)
class Quad:
    u: Fraction
    v: Fraction
    d: int

    def __post_init__(self) -> None:
        if not isinstance(self.d, int) or self.d <= 0:
            raise ValueError("radicand must be a positive integer")
        u, v = Fraction(self.u), Fraction(self.v)
        r = isqrt(self.d)
        if r * r == self.d:
            u, v = u + v * r, Fraction(0)
        object.__setattr__(self, "u", u)
        object.__setattr__(self, "v", v)

    def _coerce(self, other):
        if isinstance(other, Quad):
            if other.d == self.d:
                return other
            if other.v == 0:
                return Quad(other.u, 0, self.d)
            if self.v == 0:
                # Caller arithmetic can use the other field instead.
                return NotImplemented
            raise ValueError("cannot combine different irrational fields")
        if isinstance(other, (int, Fraction)):
            return Quad(Fraction(other), 0, self.d)
        return NotImplemented

    def __add__(self, other):
        b = self._coerce(other)
        if b is NotImplemented:
            if isinstance(other, Quad) and self.v == 0:
                return other + self.u
            return NotImplemented
        return Quad(self.u + b.u, self.v + b.v, self.d)
    __radd__ = __add__

    def __neg__(self):
        return Quad(-self.u, -self.v, self.d)

    def __sub__(self, other):
        return self + (-other)

    def __rsub__(self, other):
        return other + (-self)

    def __mul__(self, other):
        b = self._coerce(other)
        if b is NotImplemented:
            if isinstance(other, Quad) and self.v == 0:
                return other * self.u
            return NotImplemented
        return Quad(self.u*b.u + self.v*b.v*self.d,
                    self.u*b.v + self.v*b.u, self.d)
    __rmul__ = __mul__

    def inverse(self):
        norm = self.u*self.u - self.d*self.v*self.v
        if norm == 0:
            raise ZeroDivisionError("zero quadratic number")
        return Quad(self.u/norm, -self.v/norm, self.d)

    def __truediv__(self, other):
        if isinstance(other, (int, Fraction)):
            q = Fraction(other)
            if q == 0:
                raise ZeroDivisionError
            return Quad(self.u/q, self.v/q, self.d)
        if isinstance(other, Quad):
            return self * other.inverse()
        return NotImplemented

    def __rtruediv__(self, other):
        return self.inverse() * other

    def __pow__(self, n: int):
        if not isinstance(n, int):
            return NotImplemented
        if n < 0:
            return self.inverse() ** (-n)
        ans, base = Quad(1, 0, self.d), self
        while n:
            if n & 1:
                ans = ans * base
            base = base * base
            n //= 2
        return ans

    def sign(self) -> int:
        u, v = self.u, self.v
        if v == 0:
            return (u > 0) - (u < 0)
        if u == 0:
            return (v > 0) - (v < 0)
        if u > 0 and v > 0:
            return 1
        if u < 0 and v < 0:
            return -1
        delta = u*u - self.d*v*v
        sign_delta = (delta > 0) - (delta < 0)
        return sign_delta if u > 0 else -sign_delta

    def __eq__(self, other):
        if not isinstance(other, (int, Fraction, Quad)):
            return False
        return (self - other).sign() == 0

    def __lt__(self, other):
        if not isinstance(other, (int, Fraction, Quad)):
            return NotImplemented
        return (self - other).sign() < 0

    def __abs__(self):
        return self if self.sign() >= 0 else -self

    def decimal(self, precision: int = 60) -> Decimal:
        with localcontext() as ctx:
            ctx.prec = precision
            return (Decimal(self.u.numerator)/Decimal(self.u.denominator)
                    + Decimal(self.v.numerator)/Decimal(self.v.denominator)
                    * Decimal(self.d).sqrt())

    def floor(self) -> int:
        n = int(self.decimal())
        while self < n:
            n -= 1
        while self >= n + 1:
            n += 1
        return n

    def exact_string(self) -> str:
        if self.v == 0:
            return str(self.u)
        return f"({self.u}) + ({self.v})*sqrt({self.d})"
