import Lax544225Proofs.FloatEmbedding

/-! Strict squared-distance antitriangle fact, kept in the proof package. -/

universe u

namespace Lax544225Proofs.FlocqStrict

open scoped NNReal
open Lax544225.BinaryFloats Lax544225.FloatAbsoluteSpace Lax544225.FloatSquaredSpace

private lemma squareDistance_coe (F : Format) (x y : Value F) :
    (squareDistance F x y : ℝ) = (phi F x - phi F y) ^ 2 := by
  exact Real.coe_toNNReal _ (sq_nonneg _)

/-- The squared embedded distance has a strict antitriangle inequality on
every nondegenerate increasing chain.

# Attribution

The strict squared-distance antitriangle argument in
`flocq_ordered_spaces/semimetrics.v`, theorem `float_sq_antitriangle_strict`.
-/
lemma squareDistance_strict_antitriangle (F : Format) (a b c : Value F)
    (hab : ieeeLe F a b) (hbc : ieeeLe F b c) (habne : a ≠ b) (hbcne : b ≠ c) :
    squareDistance F a b + squareDistance F b c < squareDistance F a c := by
  have habLe : phi F a ≤ phi F b :=
    (Lax544225Proofs.FloatEmbedding.ieeeLe_iff_phi_le F a b).1 hab
  have hbcLe : phi F b ≤ phi F c :=
    (Lax544225Proofs.FloatEmbedding.ieeeLe_iff_phi_le F b c).1 hbc
  have habLt : phi F a < phi F b := by
    rcases lt_or_eq_of_le habLe with h | h
    · exact h
    · exact False.elim (habne (Lax544225Proofs.FloatEmbedding.phi_injective F h))
  have hbcLt : phi F b < phi F c := by
    rcases lt_or_eq_of_le hbcLe with h | h
    · exact h
    · exact False.elim (hbcne (Lax544225Proofs.FloatEmbedding.phi_injective F h))
  have hp : 0 < phi F b - phi F a := sub_pos.mpr habLt
  have hq : 0 < phi F c - phi F b := sub_pos.mpr hbcLt
  apply NNReal.coe_lt_coe.1
  simp only [NNReal.coe_add]
  rw [squareDistance_coe, squareDistance_coe, squareDistance_coe]
  nlinarith [mul_pos hp hq]

end Lax544225Proofs.FlocqStrict
