import Lax544225Proofs.FloatEmbedding
import Lax544225Proofs.FlocqStrict
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Cast.CharZero

/-!
A rational implementation of the single-NaN embedding from
`verinncoq/mueps-robustness-proofs/flocq_ordered_spaces/semimetrics.v`.
The cast lemmas connect exact rational computations to the paper's existing
real-valued definitions. This is a Lean translation of the mathematical model,
not an import of Rocq's Flocq datatype or its kernel proofs.
-/

namespace Lax544225Proofs.FlocqBridge

open scoped NNReal
open Lax544225 BinaryFloats FloatAbsoluteSpace FloatSquaredSpace OrderedSemimetric

/-- Translate Flocq's total precision and upper exponent parameter to the paper's format. -/
def format (prec : ℕ) (emax : ℤ) (hp : 0 < prec) (he : (prec : ℤ) < emax) : Format where
  precision := prec - 1
  minExponent := 2 - emax
  maxExponent := emax - 1
  exponent_le := by omega

/-- Flocq's binary32 parameters: total precision 24, emax 128. -/
def binary32 : Format := format 24 128 (by decide) (by decide)

/-- Flocq's binary64 parameters: total precision 53, emax 1024. -/
def binary64 : Format := format 53 1024 (by decide) (by decide)

/-- A Flocq integer-significand exponent e is represented by c=e+(prec-1). -/
lemma format_finite_exponent (prec : ℕ) (emax : ℤ) (hp : 0 < prec)
    (he : (prec : ℤ) < emax) (e : ℤ) :
    (format prec emax hp he).minExponent ≤ e + (prec - 1 : ℕ) ∧
      e + (prec - 1 : ℕ) ≤ (format prec emax hp he).maxExponent ↔
    3 - emax - prec ≤ e ∧ e ≤ emax - prec := by
  simp only [format]
  omega

/-- The signed-zero offset is Flocq's 2^(emin-1), where emin=3-emax-prec. -/
lemma format_zero_exponent (prec : ℕ) (emax : ℤ) (hp : 0 < prec)
    (he : (prec : ℤ) < emax) :
    (format prec emax hp he).minExponent -
      ((format prec emax hp he).precision : ℤ) - 1 = 2 - emax - prec := by
  simp only [format]
  omega

/-- The mantissa upper bound uses Flocq's total precision. -/
lemma format_mantissa_bound (prec : ℕ) (emax : ℤ) (hp : 0 < prec)
    (he : (prec : ℤ) < emax) :
    2 ^ ((format prec emax hp he).precision + 1) = (2 : ℕ) ^ prec := by
  congr 1
  simp only [format]
  omega

/-- Exact rational finite value; no machine floating-point arithmetic is used. -/
def finiteQ {F : Format} (f : FiniteValue F) : ℚ :=
  (-1 : ℚ) ^ f.sign.val * (2 : ℚ) ^ f.exponent *
    ((f.mantissa : ℚ) * (2 : ℚ) ^ (-(F.precision : ℤ)))

/-- Rational version of the paper's embedding, including NaN, infinities and signed zeros. -/
def phiQ (F : Format) : Value F → ℚ
  | .finite f => finiteQ f
  | .zero s => if s.val = 0 then 0 else -(2 : ℚ) ^ (F.minExponent - (F.precision : ℤ) - 1)
  | .infinity s => if s.val = 0 then (2 : ℚ) ^ (F.maxExponent + 1)
    else -(2 : ℚ) ^ (F.maxExponent + 1)
  | .nan => (2 : ℚ) ^ (F.maxExponent + 1) + 1

/-- Rational absolute distance from the Flocq development. -/
def distQ (F : Format) (x y : Value F) : ℚ := |phiQ F x - phiQ F y|

/-- Rational squared distance from the Flocq development. -/
def squareDistQ (F : Format) (x y : Value F) : ℚ := (phiQ F x - phiQ F y) ^ 2

lemma finiteQ_cast {F : Format} (f : FiniteValue F) : (finiteQ f : ℝ) = finiteReal f := by
  simp [finiteQ, finiteReal]

lemma phiQ_cast (F : Format) (x : Value F) : (phiQ F x : ℝ) = phi F x := by
  cases x with
  | finite f => exact finiteQ_cast f
  | zero s => by_cases h : s.val = 0 <;> simp [phiQ, phi, h]
  | infinity s => by_cases h : s.val = 0 <;> simp [phiQ, phi, h]
  | nan => simp [phiQ, phi]

lemma distQ_cast (F : Format) (x y : Value F) :
    (distQ F x y : ℝ) = (absDistance F x y : ℝ) := by
  simp [distQ, absDistance, phiQ_cast]

lemma squareDistQ_cast (F : Format) (x y : Value F) :
    (squareDistQ F x y : ℝ) = (squareDistance F x y : ℝ) := by
  simp [squareDistQ, squareDistance, phiQ_cast, Real.coe_toNNReal _ (sq_nonneg _)]

/-- Rational comparison agrees with the independently defined IEEE category order. -/
lemma ieeeLe_iff_phiQ_le (F : Format) (x y : Value F) :
    ieeeLe F x y ↔ phiQ F x ≤ phiQ F y := by
  rw [FloatEmbedding.ieeeLe_iff_phi_le]
  rw [← phiQ_cast F x, ← phiQ_cast F y]
  exact Rat.cast_le

lemma phiQ_injective (F : Format) : Function.Injective (phiQ F) := by
  intro x y h
  apply FloatEmbedding.phi_injective F
  simpa only [phiQ_cast] using congrArg (fun q : ℚ => (q : ℝ)) h

/-- Combine the stored exponent and fractional-bit scale into Flocq's exponent. -/
lemma finiteQ_eq {F : Format} (f : FiniteValue F) :
    finiteQ f = (-1 : ℚ) ^ f.sign.val * f.mantissa *
      (2 : ℚ) ^ (f.exponent - (F.precision : ℤ)) := by
  unfold finiteQ
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num)]
  ring

lemma format_finite_value (prec : ℕ) (emax : ℤ) (hp : 0 < prec)
    (he : (prec : ℤ) < emax) (f : FiniteValue (format prec emax hp he))
    (e : ℤ) (hc : f.exponent = e + (prec - 1 : ℕ)) :
    finiteQ f = (-1 : ℚ) ^ f.sign.val * f.mantissa * (2 : ℚ) ^ e := by
  rw [finiteQ_eq, hc]
  simp [format]

lemma distQ_nonneg (F : Format) (x y : Value F) : 0 ≤ distQ F x y := abs_nonneg _

lemma distQ_eq_zero_iff (F : Format) (x y : Value F) : distQ F x y = 0 ↔ x = y := by
  simp [distQ, sub_eq_zero, (phiQ_injective F).eq_iff]

lemma distQ_symm (F : Format) (x y : Value F) : distQ F x y = distQ F y x := by
  exact abs_sub_comm _ _

/-- The exact rational distance inherits the already proved scalar chain additivity. -/
lemma distQ_add (F : Format) (a b c : Value F)
    (hab : ieeeLe F a b) (hbc : ieeeLe F b c) :
    distQ F a c = distQ F a b + distQ F b c := by
  have h := congrArg (fun r : ℝ≥0 => (r : ℝ))
    (FloatEmbedding.floatAbsoluteAdditivity F a b c hab hbc)
  simp only [NNReal.coe_add, ← distQ_cast] at h
  exact_mod_cast h

lemma squareDistQ_nonneg (F : Format) (x y : Value F) :
    0 ≤ squareDistQ F x y := sq_nonneg _

lemma squareDistQ_eq_zero_iff (F : Format) (x y : Value F) :
    squareDistQ F x y = 0 ↔ x = y := by
  simp [squareDistQ, sub_eq_zero, (phiQ_injective F).eq_iff]

lemma squareDistQ_symm (F : Format) (x y : Value F) :
    squareDistQ F x y = squareDistQ F y x := by
  unfold squareDistQ
  ring

lemma squareDistQ_strict_antitriangle (F : Format) (a b c : Value F)
    (hab : ieeeLe F a b) (hbc : ieeeLe F b c) (habne : a ≠ b) (hbcne : b ≠ c) :
    squareDistQ F a b + squareDistQ F b c < squareDistQ F a c := by
  have h := NNReal.coe_lt_coe.mpr
    (FlocqStrict.squareDistance_strict_antitriangle F a b c hab hbc habne hbcne)
  simp only [NNReal.coe_add, ← squareDistQ_cast] at h
  exact_mod_cast h

end Lax544225Proofs.FlocqBridge
