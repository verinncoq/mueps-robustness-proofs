#!/usr/bin/env python3
"""test.py — differential testing between the Rocq (semimetrics.v) and the
Python (semimetrics.py) implementations of the example distances.

The test generates Rocq files that `Compute` the (Qnum, Qden) pairs of

    binary64_dist          (the pure-float space distance),
    binary64_sq_dist       (the strictly convex squared variant),
    binary64_l1_dist       (the l_1-like vector distance),
    binary64_linf_dist     (the l_infty-like vector distance)

for test data whose (kind, sign, significand, exponent) specs are
identical on both sides, compiles them with `coqc`, and compares the
results — after normalization, since Rocq's Qmake fractions are not
reduced — against the exact `fractions.Fraction` values computed by
semimetrics.py.  Any difference is a failure.

Two phases are run (see TASK.md):

  Phase 1 (fixed): a fixed dataset that includes the special binary64
    values — NaN, +inf, -inf, +0.0, -0.0 — plus assorted finite values
    (subnormals, min normal, max finite, huge/negative/irrational-ish
    values).  All ordered pairs of scalars are tested, plus fixed vector
    cases (same-length and length-mismatched, exercising the +1
    penalty).

  Phase 2 (random): a seeded random generator of binary64 values (raw
    bit patterns, stratified over exponent classes: subnormal/zero,
    normal, and infinity/NaN), run after the fixed dataset, plus random
    vector cases.

Both phases are deterministic (fixed default seed; override with
TEST_SEED).  Exit status is 0 iff all results match exactly.
"""

import os
import random
import re
import struct
import subprocess
import sys
from fractions import Fraction
from typing import List, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from semimetrics import (Float64, float_dist, float_sq_dist,
                         vec_dist_l1, vec_dist_linf)

HERE = os.path.dirname(os.path.abspath(__file__))
SEED = int(os.environ.get("TEST_SEED", "20261004"))


# ---------------------------------------------------------------------------
# Rocq code generation helpers

GEN_HEADER = """From Stdlib Require Import ZArith QArith List.
Import ListNotations.
From Flocq Require Import IEEE754.BinarySingleNaN.
Require Import semimetrics.
Open Scope Q_scope.
Set Printing Width 1000000.
"""


def emit_float(f: Float64) -> str:
    """Rocq term for a binary64 datum, mirroring semimetrics.py's Float64."""
    if f.kind == "nan":
        return "B754_nan"
    if f.kind == "inf":
        return f"@BinarySingleNaN.B754_infinity 53 1024 {'true' if f.sign else 'false'}"
    if f.kind == "zero":
        return f"@BinarySingleNaN.B754_zero 53 1024 {'true' if f.sign else 'false'}"
    assert f.kind == "finite"
    return (f"@BinarySingleNaN.B754_finite 53 1024 "
            f"{'true' if f.sign else 'false'} "
            f"{f.m}%positive ({f.e})%Z eq_refl")


def emit_list(vs: List[Float64]) -> str:
    if not vs:
        return "@nil (binary_float 53 1024)"
    return "[" + " ; ".join(emit_float(v) for v in vs) + "]"


def gen_file_body(prefix: str,
                  scalars: List[Float64],
                  vector_cases: List[Tuple[List[Float64], List[Float64]]]):
    """Return (file_text, ordered_expected_results)."""
    lines = [GEN_HEADER]
    expected = []  # (tag, Fraction) in emission order

    for i, f in enumerate(scalars):
        lines.append(f"Definition {prefix}{i} : binary_float 53 1024 := "
                     f"{emit_float(f)}.")
    for k, (xs, ys) in enumerate(vector_cases):
        lines.append(f"Definition {prefix}x{k} : list (binary_float 53 1024) := "
                     f"{emit_list(xs)}.")
        lines.append(f"Definition {prefix}y{k} : list (binary_float 53 1024) := "
                     f"{emit_list(ys)}.")

    # scalar distances: all ordered pairs, both scalar distances
    for i, a in enumerate(scalars):
        for j, b in enumerate(scalars):
            lines.append(
                f"Compute ((Qnum (binary64_dist {prefix}{i} {prefix}{j})), "
                f"(Z.pos (Qden (binary64_dist {prefix}{i} {prefix}{j})))).")
            expected.append((f"s{i}_{j}", float_dist(a, b)))
            lines.append(
                f"Compute ((Qnum (binary64_sq_dist {prefix}{i} {prefix}{j})), "
                f"(Z.pos (Qden (binary64_sq_dist {prefix}{i} {prefix}{j})))).")
            expected.append((f"q{i}_{j}", float_sq_dist(a, b)))

    # vector distances: l1 and linf for each vector case
    for k, (xs, ys) in enumerate(vector_cases):
        lines.append(
            f"Compute ((Qnum (binary64_l1_dist {prefix}x{k} {prefix}y{k})), "
            f"(Z.pos (Qden (binary64_l1_dist {prefix}x{k} {prefix}y{k})))).")
        expected.append((f"l1_{k}", vec_dist_l1(xs, ys)))
        lines.append(
            f"Compute ((Qnum (binary64_linf_dist {prefix}x{k} {prefix}y{k})), "
            f"(Z.pos (Qden (binary64_linf_dist {prefix}x{k} {prefix}y{k})))).")
        expected.append((f"li_{k}", vec_dist_linf(xs, ys)))

    return "\n".join(lines) + "\n", expected


RESULT_RE = re.compile(r"=\s*\(\s*(-?\d+)%Z\s*,\s*(-?\d+)%Z\s*\)")


def run_phase(name: str, gen_text: str, expected) -> Tuple[int, int]:
    """Compile gen_text with coqc, parse the results, compare with expected."""
    gen_v = os.path.join(HERE, f"difftest_gen_{name}.v")
    with open(gen_v, "w") as fh:
        fh.write(gen_text)
    artifacts = [gen_v]
    for ext in (".vo", ".glob", ".vok", ".vos", ".aux"):
        artifacts.append(os.path.join(HERE, f"difftest_gen_{name}{ext}"))
        artifacts.append(os.path.join(HERE, f".difftest_gen_{name}{ext}"))
    try:
        r = subprocess.run(["coqc", gen_v], capture_output=True, text=True,
                           cwd=HERE, timeout=1800)
        if r.returncode != 0:
            print(f"[{name}] coqc FAILED:")
            print(r.stdout[-2000:])
            print(r.stderr[-2000:])
            sys.exit(1)
        nums = RESULT_RE.findall(r.stdout)
        if len(nums) != len(expected):
            print(f"[{name}] PARSE MISMATCH: {len(nums)} results parsed, "
                  f"{len(expected)} expected")
            sys.exit(1)
        bad = 0
        for (tag, want), (num, den) in zip(expected, nums):
            got = Fraction(int(num), int(den))  # normalizes the unreduced Q
            if got != want:
                bad += 1
                print(f"[{name}] MISMATCH {tag}: rocq {got} != python {want}")
        print(f"[{name}] {len(expected)} cases, {bad} mismatches"
              + ("  -- FAIL" if bad else "  -- all exactly equal"))
        return len(expected), bad
    finally:
        for a in artifacts:
            try:
                os.remove(a)
            except OSError:
                pass


# ---------------------------------------------------------------------------
# Phase 1: fixed dataset (specials + assorted finite values)

def fixed_values() -> List[Float64]:
    nan = Float64.nan()
    pinf = Float64.pos_inf()
    ninf = Float64.neg_inf()
    pz = Float64.pos_zero()
    nz = Float64.neg_zero()
    specials = [nan, pinf, ninf, pz, nz]
    floats = [
        1.0, -1.0, 0.5, 2.0, -2.5,
        1e300, -1e300,
        5e-324, -5e-324,                       # min subnormal
        2.2250738585072014e-308, -2.2250738585072014e-308,  # min normal
        1.7976931348623157e308, -1.7976931348623157e308,   # max finite
        3.141592653589793, -3.141592653589793,
        0.1, 42.0,
    ]
    return specials + [Float64.of_float(f) for f in floats]


def fixed_vector_cases(vals) -> List[Tuple[List[Float64], List[Float64]]]:
    nan = vals[0]
    pinf = vals[1]
    ninf = vals[2]
    pz = vals[3]
    nz = vals[4]
    one = Float64.of_float(1.0)
    half = Float64.of_float(0.5)
    maxf = Float64.of_float(1.7976931348623157e308)
    minsub = Float64.of_float(5e-324)
    return [
        ([one, nz], [half, pz]),               # d = 1/2 + 2^-1075
        ([nan], [nan, nan]),                   # length mismatch: penalty 1
        ([], [nan]),                           # empty vs [NaN]
        ([], []),                              # empty vs empty
        ([pz, nan], [pz]),                     # mismatch, NaN padding
        ([one, one, one], [one, one]),          # mismatch
        ([maxf, minsub], [minsub, maxf]),       # same length, extreme swap
        ([ninf, nz], [pinf, pz]),               # specials in vectors
    ]


# ---------------------------------------------------------------------------
# Phase 2: random generator (runs after the fixed dataset)

def random_float64(rng: random.Random) -> Float64:
    """A random binary64 via a stratified raw bit pattern:
    exponent field 0 (zero/subnormal), 1..2046 (normal) or 2047
    (inf/NaN) are all reachable; NaN payloads collapse to the single
    NaN, mirroring Flocq's BinarySingleNaN."""
    sign = rng.getrandbits(1)
    expfield = rng.choice([0, rng.randint(0, 2047), 2047])
    if expfield == 2047 and rng.getrandbits(1):
        mantissa = 0            # infinity
    else:
        mantissa = rng.getrandbits(52)
    bits = (sign << 63) | (expfield << 52) | mantissa
    f = struct.unpack("<d", struct.pack("<Q", bits))[0]
    return Float64.of_float(f)


def random_values(rng: random.Random, n: int) -> List[Float64]:
    return [random_float64(rng) for _ in range(n)]


def random_vector_cases(rng: random.Random,
                        vals: List[Float64]) -> List[Tuple[List[Float64],
                                                          List[Float64]]]:
    cases = []
    for _ in range(4):
        n = rng.randint(1, 4)
        xs = [rng.choice(vals) for _ in range(n)]
        ys = [rng.choice(vals) for _ in range(n)]
        cases.append((xs, ys))
    for _ in range(2):
        # mismatched lengths (exercise the penalty)
        n = rng.randint(1, 4)
        m = rng.randint(1, 4)
        while m == n:
            m = rng.randint(1, 4)
        xs = [rng.choice(vals) for _ in range(n)]
        ys = [rng.choice(vals) for _ in range(m)]
        cases.append((xs, ys))
    return cases


# ---------------------------------------------------------------------------

def ensure_compiled():
    vo = os.path.join(HERE, "semimetrics.vo")
    v = os.path.join(HERE, "semimetrics.v")
    if os.path.exists(vo) and os.path.getmtime(vo) >= os.path.getmtime(v):
        return
    print("[setup] compiling semimetrics.v ...")
    r = subprocess.run(["coqc", v], capture_output=True, text=True,
                       cwd=HERE, timeout=1800)
    if r.returncode != 0:
        print("[setup] coqc semimetrics.v FAILED:")
        print(r.stdout[-2000:])
        print(r.stderr[-2000:])
        sys.exit(1)


def main() -> int:
    rng = random.Random(SEED)
    ensure_compiled()

    total = 0
    bad = 0

    # ---- phase 1: fixed dataset ----------------------------------------
    vals = fixed_values()
    vcases = fixed_vector_cases(vals)
    print(f"[fixed] {len(vals)} scalars -> {len(vals)**2} scalar pairs "
          f"x 2 distances, {len(vcases)} vector cases x 2 norms")
    gen_text, expected = gen_file_body("f", vals, vcases)
    t, b = run_phase("fixed", gen_text, expected)
    total += t
    bad += b

    # ---- phase 2: random dataset (after the fixed one) ------------------
    rvals = random_values(rng, 16)
    rcases = random_vector_cases(rng, rvals)
    print(f"[random] seed={SEED}: {len(rvals)} scalars -> "
          f"{len(rvals)**2} scalar pairs x 2 distances, "
          f"{len(rcases)} vector cases x 2 norms")
    gen_text, expected = gen_file_body("r", rvals, rcases)
    t, b = run_phase("random", gen_text, expected)
    total += t
    bad += b

    # ---- summary ---------------------------------------------------------
    print(f"differential test: {total} cases total, {bad} mismatches")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
