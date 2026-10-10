"""semimetrics.py

Python re-implementations of the distance functions of the example
ordered semimetric spaces formalized in semimetrics.v (Rocq/Flocq).

The correspondence with semimetrics.v is:

  - `Float64` mirrors Flocq's `BinarySingleNaN.binary_float 53 1024`
    (IEEE-754 binary64 with a single NaN datum).  A finite value is
    stored as (sign, significand m, exponent e) with
    value = (-1)^sign * m * 2^e and 0 < m < 2^53,
    -1074 <= e <= 971, canonical (see `Float64.of_float`).
  - `phi(x)` mirrors `phi 53 1024` in semimetrics.v: an injective
    embedding of the floats into the exact rationals:
        phi(NaN)        = 2^1024 + 1        (NaN is the largest value)
        phi(+inf)       = 2^1024
        phi(-inf)       = -2^1024
        phi(-0)         = -2^(-1075)       (just above -min_subnormal)
        phi(+0)         = 0
        phi(finite s m e) = (-1)^s * m * 2^e
    With emin = 3 - emax - prec = -1074.
  - `float_le(x, y)` mirrors `ieee_le`: the IEEE-754 total order
    (totalOrder) extended with the single NaN at the top:
        -inf < (negatives, then -0 < +0) < (positives) < +inf < NaN.
  - `float_dist(x, y)` mirrors `binary64_dist = float_dist`:
    d(x, y) = |phi(x) - phi(y)|, computed exactly over Fraction.
    It handles the non-numeric data (NaN, +-inf) and the signed
    zeros exactly as in the Rocq development, e.g.
    d(-0, +0) = 2^(-1075) and d(NaN, +inf) = 1.
  - `float_sq_dist(x, y)` mirrors `binary64_sq_dist`: the strictly
    convex variant d2(x, y) = (phi(x) - phi(y))^2 on the SAME IEEE-754
    order.  All examples above satisfy the antitriangle of
    Definition 9 (a <= b <= c -> d(a,b) + d(b,c) <= d(a,c)) with
    equality; the squared one makes it a STRICT inequality on every
    nondegenerate chain a < b < c (the gap is 2*p*q > 0).
  - `vec_dist_l1(xs, ys)` and `vec_dist_linf(xs, ys)` mirror
    `vec_dist_l1` / `vec_dist_linf` applied to `binary64_space`:
    components beyond the end of a list are read as the space point
    (NaN), and a length mismatch adds a +1 penalty to the distance
    (needed for the identity of indiscernibles).
  - `vec_le(xs, ys)` mirrors the order `vec_le` of the l_1 vector
    space: equal lengths and pointwise `float_le`.
  - `vec_le_sync(xs, ys)` mirrors the order `vec_le_sync` of the
    l_infty vector space: in addition to being pointwise ordered,
    all component distances of the pair must be equal.  This
    "synchronized shift" order is needed because the antitriangle
    (superadditivity along the order, Definition 9 of the paper)
    fails for the plain pointwise order with the max aggregation:
    e.g. [1;1] <= [11;1] <= [11;8] pointwise, but
    d_inf([1;1],[11;8]) = 10 < 10 + 7 = d_inf([1;1],[11;1]) +
    d_inf([11;1],[11;8]).

All arithmetic is exact: distances are returned as `fractions.Fraction`.
"""

from dataclasses import dataclass
from fractions import Fraction
from typing import List, Tuple

# ---------------------------------------------------------------------------
# binary64 parameters (Flocq: prec = 53, emax = 1024, emin = 3 - emax - prec)

PREC = 53
EMAX = 1024
EMIN = 3 - EMAX - PREC        # = -1074

TWO = Fraction(2)


def qpow2(e: int) -> Fraction:
    """Exact 2^e as a Fraction (mirrors Qpower 2 e)."""
    return TWO ** e


@dataclass(frozen=True)
class Float64:
    """A binary64 datum, mirroring Flocq's binary_float 53 1024.

    kind: 'zero' | 'inf' | 'nan' | 'finite'
    sign: True means negative (Flocq convention: s = true <-> negative)
    m:    significand (positive), only for 'finite'
    e:    exponent, only for 'finite' (value = (-1)^sign * m * 2^e)
    """
    kind: str
    sign: bool = False
    m: int = 0
    e: int = 0

    # -- constructors (mirror the B754_* constructors of Flocq) ----------
    @staticmethod
    def pos_zero() -> "Float64":
        return Float64("zero", False)

    @staticmethod
    def neg_zero() -> "Float64":
        return Float64("zero", True)

    @staticmethod
    def pos_inf() -> "Float64":
        return Float64("inf", False)

    @staticmethod
    def neg_inf() -> "Float64":
        return Float64("inf", True)

    @staticmethod
    def nan() -> "Float64":
        return Float64("nan", False)   # single NaN; Flocq's Bsign = false

    @staticmethod
    def finite(sign: bool, m: int, e: int) -> "Float64":
        """Mirror of B754_finite: the value must be a canonical
        (bounded) representation, i.e. 0 < m < 2^prec and
        prec-1 <= Zdigits2(m) + e (Flocq's SpecFloat.bounded)."""
        if not (0 < m < 2 ** PREC):
            raise ValueError("significand out of (0, 2^53)")
        if not (EMIN <= e <= EMAX - PREC):
            raise ValueError("exponent out of [emin, emax - prec]")
        # canonical_mantissa: fexp (Zdigits2 m + e) = e, i.e.
        # either digits2(m) = prec (normal), or e = emin (subnormal).
        if m.bit_length() != PREC and e != EMIN:
            raise ValueError("non-canonical representation")
        return Float64("finite", sign, m, e)

    # -- conversions ------------------------------------------------------
    @staticmethod
    def of_float(f: float) -> "Float64":
        """Convert a Python float (binary64) to its Flocq representation.
        NaN (any payload) maps to the single NaN; infinities and signed
        zeros are preserved."""
        if f != f:
            return Float64.nan()
        if f in (float("inf"), float("-inf")):
            return Float64("inf", f < 0)
        bits = float_bits(f)
        sign = bool(bits >> 63)
        expfield = (bits >> 52) & 0x7FF
        frac = bits & ((1 << 52) - 1)
        if expfield == 0:
            # zero or subnormal
            if frac == 0:
                return Float64("zero", sign)
            return Float64.finite(sign, frac, EMIN)
        return Float64.finite(sign, frac | (1 << 52), expfield - 1075)

    def value(self) -> Fraction:
        """Exact value as a Fraction (finite values only)."""
        if self.kind != "finite":
            raise ValueError("non-finite value")
        v = Fraction(self.m) * qpow2(self.e)
        return -v if self.sign else v

    def __repr__(self) -> str:
        if self.kind == "zero":
            return "-0.0" if self.sign else "+0.0"
        if self.kind == "inf":
            return "-inf" if self.sign else "+inf"
        if self.kind == "nan":
            return "NaN"
        return f"{'-' if self.sign else ''}{self.m}*(2^{self.e})"


def float_bits(f: float) -> int:
    import struct
    return struct.unpack("<Q", struct.pack("<d", f))[0]


# ---------------------------------------------------------------------------
# phi : the injective embedding into Q (mirrors phi 53 1024 in semimetrics.v)

def phi(x: Float64) -> Fraction:
    if x.kind == "nan":
        return qpow2(EMAX) + 1
    if x.kind == "inf":
        return -qpow2(EMAX) if x.sign else qpow2(EMAX)
    if x.kind == "zero":
        return -qpow2(EMIN - 1) if x.sign else Fraction(0)
    return x.value()


# ---------------------------------------------------------------------------
# The distance of the pure-float example space
# (mirrors binary64_dist = float_dist 53 1024 = Qabs (phi x - phi y))

def float_dist(x: Float64, y: Float64) -> Fraction:
    """d(x, y) = |phi(x) - phi(y)|, exactly."""
    return abs(phi(x) - phi(y))


def float_sq_dist(x: Float64, y: Float64) -> Fraction:
    """Strictly convex variant (mirrors binary64_sq_dist):
    d2(x, y) = (phi(x) - phi(y))^2, exactly.

    Same carrier and IEEE-754 order as float_dist, but the antitriangle
    of Definition 9 (d(a,b) + d(b,c) <= d(a,c) for a <= b <= c) is a
    STRICT inequality whenever a < b < c."""
    return (phi(x) - phi(y)) ** 2


# ---------------------------------------------------------------------------
# The order of the pure-float example space
# (mirrors ieee_le: IEEE-754 totalOrder with the single NaN at the top)

def float_le(x: Float64, y: Float64) -> bool:
    """IEEE-754 total order on binary64 (with single NaN largest)."""
    if x.kind == "nan":
        return y.kind == "nan"
    if y.kind == "nan":
        return True
    if x.kind == "inf":
        if y.kind == "inf":
            return x.sign or not y.sign
        return x.sign            # -inf <= anything; +inf <= only +inf/NaN
    if y.kind == "inf":
        return not y.sign       # anything <= +inf
    if x.kind == "zero":
        if y.kind == "zero":
            return x.sign or not y.sign     # -0 <= +0
        return y.kind == "finite" and not y.sign   # 0 <= positive finite
    # x finite
    if y.kind == "zero":
        return x.sign                   # negative finite <= 0
    # both finite: compare exact values (mirrors Rle (B2R x) (B2R y))
    return x.value() <= y.value()


# ---------------------------------------------------------------------------
# The vector example spaces over binary64
# (mirrors vec_dist_l1 / vec_dist_linf applied to binary64_space)

def _comps(xs: List[Float64], ys: List[Float64]) -> List[Fraction]:
    """Component distances, padding with the space point (NaN)."""
    pad = Float64.nan()
    n = max(len(xs), len(ys))
    return [
        float_dist(xs[i] if i < len(xs) else pad,
                   ys[i] if i < len(ys) else pad)
        for i in range(n)
    ]


def _penalty(xs: List[Float64], ys: List[Float64]) -> Fraction:
    return Fraction(0) if len(xs) == len(ys) else Fraction(1)


def vec_dist_l1(xs: List[Float64], ys: List[Float64]) -> Fraction:
    """l_1-like distance (mirrors binary64_l1_dist)."""
    return _penalty(xs, ys) + sum(_comps(xs, ys), Fraction(0))


def vec_dist_linf(xs: List[Float64], ys: List[Float64]) -> Fraction:
    """l_infty-like distance (mirrors binary64_linf_dist)."""
    comps = _comps(xs, ys)
    return _penalty(xs, ys) + (max(comps) if comps else Fraction(0))


# ---------------------------------------------------------------------------
# The pointwise order of the vector spaces (mirrors vec_le binary64_space)

def vec_le(xs: List[Float64], ys: List[Float64]) -> bool:
    """Pointwise order; only equal-length vectors are comparable."""
    if len(xs) != len(ys):
        return False
    return all(float_le(x, y) for x, y in zip(xs, ys))


def vec_le_sync(xs: List[Float64], ys: List[Float64]) -> bool:
    """Synchronized-shift order (mirrors vec_le_sync binary64_space):
    pointwise order AND all component distances equal.  This is the
    order of the l_infty vector space binary64_linf_space."""
    if not vec_le(xs, ys):
        return False
    comps = _comps(xs, ys)
    return all(c == comps[0] for c in comps)


# ---------------------------------------------------------------------------
# Self-test

if __name__ == "__main__":
    checks: List[Tuple[str, bool]] = []

    nan = Float64.nan()
    pinf, ninf = Float64.pos_inf(), Float64.neg_inf()
    pz, nz = Float64.pos_zero(), Float64.neg_zero()

    # sanity checks mirroring the Example lemmas of semimetrics.v
    checks.append(("d(NaN, +inf) == 1", float_dist(nan, pinf) == 1))
    checks.append(("d(-0, +0) == 2^-1075",
                  float_dist(nz, pz) == Fraction(1, 2 ** 1075)))
    maxf = Float64.finite(True, 2 ** 53 - 1, 971)
    checks.append(("d(NaN, -maxf) == 2^1025 - 2^971 + 1",
                  float_dist(nan, maxf) == 2 ** 1025 - 2 ** 971 + 1))

    one = Float64.of_float(1.0)
    half = Float64.of_float(0.5)
    checks.append(("d(1, 1/2) == 1/2", float_dist(one, half) == Fraction(1, 2)))
    checks.append(("d(pi, pi) == 0",
                  float_dist(Float64.of_float(3.141592653589793),
                             Float64.of_float(3.141592653589793)) == 0))
    checks.append(("d(-0, +0) != 0", float_dist(nz, pz) != 0))

    # vector checks mirroring the vector Examples of semimetrics.v
    v1 = [Float64.of_float(1.0), Float64.neg_zero()]
    v2 = [Float64.of_float(0.5), Float64.pos_zero()]
    checks.append(("l1([1,-0],[1/2,+0]) == 1/2 + 2^-1075",
                  vec_dist_l1(v1, v2) == Fraction(1, 2) + Fraction(1, 2 ** 1075)))
    checks.append(("linf([1,-0],[1/2,+0]) == 1/2",
                  vec_dist_linf(v1, v2) == Fraction(1, 2)))
    checks.append(("l1([NaN],[NaN,NaN]) == 1 (penalty)",
                  vec_dist_l1([nan], [nan, nan]) == 1))

    # order checks
    checks.append(("-inf <= -0 <= +0 <= 1 <= +inf <= NaN",
                   float_le(ninf, nz) and float_le(nz, pz)
                   and float_le(pz, one) and float_le(one, pinf)
                   and float_le(pinf, nan)))
    checks.append(("not (NaN <= +inf)", not float_le(nan, pinf)))

    # antitriangle of Definition 9: on the pure-float space it holds
    # with equality (mirrors binary64_antitriangle_example and
    # float_dist_add in semimetrics.v)
    one_f = Float64.of_float(1.0)
    two_f = Float64.of_float(2.0)
    three_f = Float64.of_float(3.0)
    checks.append(("d(1,3) == d(1,2) + d(2,3) (antitriangle, equality)",
                  float_dist(one_f, three_f)
                  == float_dist(one_f, two_f) + float_dist(two_f, three_f)))

    # the l_infty antitriangle FAILS under the plain pointwise order
    # (mirrors binary64_linf_pointwise_antitriangle_fails in
    # semimetrics.v): [1;1] <= [11;1] <= [11;8] pointwise but
    # d_inf([1;1],[11;8]) = 10 < 10 + 7.
    f1 = Float64.of_float(1.0)
    f8 = Float64.of_float(8.0)
    f11 = Float64.of_float(11.0)
    u, v, w = [f1, f1], [f11, f1], [f11, f8]
    checks.append(("[1;1] <= [11;1] <= [11;8] pointwise",
                   vec_le(u, v) and vec_le(v, w)))
    checks.append(("pointwise l_infty antitriangle fails: 10 < 10+7",
                   vec_dist_linf(u, w)
                   < vec_dist_linf(u, v) + vec_dist_linf(v, w)))

    # the synchronized-shift order repairs it: along sync chains the
    # l_infty antitriangle holds with equality (vec_le_sync)
    checks.append(("[1;1] not <= [11;1] in sync order (7 != 10)",
                   not vec_le_sync(u, v)))
    a2 = [Float64.of_float(2.0), Float64.of_float(2.0)]
    b2 = [Float64.of_float(5.0), Float64.of_float(5.0)]
    c2 = [Float64.of_float(9.0), Float64.of_float(9.0)]
    checks.append(("[2;2] <= [5;5] <= [9;9] in sync order",
                   vec_le_sync(a2, b2) and vec_le_sync(b2, c2)))
    checks.append(("sync l_infty antitriangle with equality: 7 == 3+4",
                  vec_dist_linf(a2, c2)
                  == vec_dist_linf(a2, b2) + vec_dist_linf(b2, c2)))

    # the squared distance: the antitriangle is necessarily a strict
    # inequality (mirrors binary64_sq_dist examples in semimetrics.v)
    checks.append(("sq d(NaN, +inf) == 1",
                  float_sq_dist(nan, pinf) == 1))
    checks.append(("sq d(-0, +0) == 2^-2150",
                  float_sq_dist(nz, pz) == Fraction(1, 2 ** 2150)))
    checks.append(("sq antitriangle strict: d2(1,2)+d2(2,3)=2 < 4=d2(1,3)",
                  float_sq_dist(one_f, two_f) + float_sq_dist(two_f, three_f)
                  < float_sq_dist(one_f, three_f)))
    checks.append(("sq antitriangle equality on degenerate chain 1<=1<=3",
                  float_sq_dist(one_f, one_f) + float_sq_dist(one_f, three_f)
                  == float_sq_dist(one_f, three_f)))
    checks.append(("sq antitriangle non-strict: 2 <= 4",
                  float_sq_dist(one_f, two_f) + float_sq_dist(two_f, three_f)
                  <= float_sq_dist(one_f, three_f)))

    ok = True
    for name, res in checks:
        print(("PASS" if res else "FAIL"), name)
        ok = ok and res
    print("ALL OK" if ok else "FAILURES")
    raise SystemExit(0 if ok else 1)
