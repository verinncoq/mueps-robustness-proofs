/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.OrderedSemimetric
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Cast.Lemmas

/-!
A binary floating-point format specifies a precision and a range of exponents. Its finite values are supplemented by signed zeros, signed infinities, and one NaN. A real-valued embedding assigns distinct positions to these special values.

**Definition from the paper.**

Let $\mathcal F$ be a binary floating point format with $p\in\mathbb N$
mantissa bits. Its finite nonzero values are triples $(s,c,m)$ representing
$(-1)^s2^cm$, where $s\in\{0,1\}$,
$c\in\{c_{\min},\dots,c_{\max}\}\subset\mathbb Z$, and

$$m\in\{k2^{-p}\mid k\in\{1,\dots,2^{p+1}-1\}\}.$$

Each triple satisfies either $m\geq1$ (normal) or $c=c_{\min}$ (subnormal).
The format also contains $\pm0$, $\mathrm{NaN}$ and $\pm\mathrm{Inf}$.
Define $\phi:\mathcal F\rightarrow\mathbb R$ by

- $\phi((s,c,m))=(-1)^s2^cm$;
- $\phi(+0)=0$ and $\phi(-0)=-2^{c_{\min}-p-1}$;
- $\phi(\mathrm{NaN})=2^{c_{\max}+1}+1$;
- $\phi(\pm\mathrm{Inf})=\pm2^{c_{\max}+1}$.

# Formalization notes

This is the paper’s single-NaN abstraction, matching the supplied Flocq BinarySingleNaN examples, not the full set of IEEE NaN payloads. A finite mantissa is stored as the integer k with m=k·2^(−p); normality means k≥2^p. The independent order puts −∞ first, then negative finite values, −0, +0, positive finite values, +∞, and NaN. It is not defined by φ.
-/

universe u

namespace Mueps.BinaryFloats

open scoped NNReal

/-- The precision and nonempty exponent interval of a binary format. -/
structure Format where
  /-- Number of fractional bits in the significand. -/
  precision : ℕ
  /-- Least allowed exponent. -/
  minExponent : ℤ
  /-- Greatest allowed exponent. -/
  maxExponent : ℤ
  /-- The exponent interval is nonempty. -/
  exponent_le : minExponent ≤ maxExponent

/-- Canonical data for a nonzero finite number in a format. -/
structure FiniteValue (F : Format) where
  /-- Sign bit: 0 is positive and 1 is negative. -/
  sign : Fin 2
  /-- The exponent of the value. -/
  exponent : ℤ
  /-- The integer significand before scaling by 2^(−p). -/
  mantissa : ℕ
  /-- The exponent is allowed by the format. -/
  exponent_mem : F.minExponent ≤ exponent ∧ exponent ≤ F.maxExponent
  /-- The significand is nonzero and less than 2^(p+1). -/
  mantissa_mem : 0 < mantissa ∧ mantissa < 2 ^ (F.precision + 1)
  /-- A significand below the normal range occurs only at the minimum exponent. -/
  canonical : 2 ^ F.precision ≤ mantissa ∨ exponent = F.minExponent

/-- Canonical finite data and the four signed special values together with one NaN. -/
inductive Value (F : Format)
  /-- A nonzero finite floating-point value. -/
  | finite : FiniteValue F → Value F
  /-- A signed zero. -/
  | zero : Fin 2 → Value F
  /-- A signed infinity. -/
  | infinity : Fin 2 → Value F
  /-- The single, greatest NaN value. -/
  | nan : Value F

/-- The exact ordinary real value of canonical finite data. -/
noncomputable def finiteReal {F : Format} (f : FiniteValue F) : ℝ :=
  (-1 : ℝ) ^ f.sign.val * (2 : ℝ) ^ f.exponent *
    ((f.mantissa : ℝ) * (2 : ℝ) ^ (-(F.precision : ℤ)))

/-- The real embedding including separated signed zeros and bounded special values. -/
noncomputable def phi (F : Format) : Value F → ℝ
  | .finite f => finiteReal f
  | .zero s => if s.val = 0 then 0 else -(2 : ℝ) ^ (F.minExponent - (F.precision : ℤ) - 1)
  | .infinity s => if s.val = 0 then (2 : ℝ) ^ (F.maxExponent + 1)
    else -(2 : ℝ) ^ (F.maxExponent + 1)
  | .nan => (2 : ℝ) ^ (F.maxExponent + 1) + 1

/-- The position of each sign and special-value category in the total order. -/
def category {F : Format} : Value F → ℕ
  | .finite f => if f.sign.val = 0 then 4 else 1
  | .zero s => if s.val = 0 then 3 else 2
  | .infinity s => if s.val = 0 then 5 else 0
  | .nan => 6

/-- The ordinary finite value used to order members within a finite category. -/
noncomputable def withinCategory {F : Format} : Value F → ℝ
  | .finite f => finiteReal f
  | _ => 0

/-- IEEE category order with one positive NaN and exact comparison of finite values. -/
def ieeeLe (F : Format) (x y : Value F) : Prop :=
  category x < category y ∨
    (category x = category y ∧ withinCategory x ≤ withinCategory y)

end Mueps.BinaryFloats
