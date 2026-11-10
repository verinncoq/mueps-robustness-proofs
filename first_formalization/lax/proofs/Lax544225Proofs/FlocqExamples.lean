import Lax544225Proofs.FlocqBridge
import Lax544225Proofs.Lists

/-!
Concrete proof-side examples translated from the vector and special-value
examples in `mueps-robustness-proofs/flocq_ordered_spaces/semimetrics.v`
(verinncoq). The generic constructions remain the existing LAX results;
these declarations are illustrations and do not add concepts.
-/

namespace Lax544225Proofs.FlocqExamples

open Lax544225.Semimetric Lax544225.OrderedSemimetric
open Lax544225.BinaryFloats Lax544225.FloatAbsoluteSpace Lax544225.FloatSquaredSpace
open Lax544225.SumProductSpace Lax544225.MaximumProductSpace Lax544225.ListSpaces
open Lax544225Proofs.FlocqBridge
open scoped NNReal BigOperators

private def one64 : Value binary64 := .finite {
  sign := 0
  exponent := 0
  mantissa := 2 ^ 52
  exponent_mem := by norm_num [binary64, format]
  mantissa_mem := by norm_num [binary64, format]
  canonical := Or.inl (by norm_num [binary64, format])
}

private def two64 : Value binary64 := .finite {
  sign := 0
  exponent := 1
  mantissa := 2 ^ 52
  exponent_mem := by norm_num [binary64, format]
  mantissa_mem := by norm_num [binary64, format]
  canonical := Or.inl (by norm_num [binary64, format])
}

private def three64 : Value binary64 := .finite {
  sign := 0
  exponent := 1
  mantissa := 3 * 2 ^ 51
  exponent_mem := by norm_num [binary64, format]
  mantissa_mem := by norm_num [binary64, format]
  canonical := Or.inl (by norm_num [binary64, format])
}

private def eight64 : Value binary64 := .finite {
  sign := 0
  exponent := 3
  mantissa := 2 ^ 52
  exponent_mem := by norm_num [binary64, format]
  mantissa_mem := by norm_num [binary64, format]
  canonical := Or.inl (by norm_num [binary64, format])
}

private def eleven64 : Value binary64 := .finite {
  sign := 0
  exponent := 3
  mantissa := 11 * 2 ^ 49
  exponent_mem := by norm_num [binary64, format]
  mantissa_mem := by norm_num [binary64, format]
  canonical := Or.inl (by norm_num [binary64, format])
}

private lemma phi_one64 : phiQ binary64 one64 = 1 := by
  norm_num [phiQ, finiteQ, one64, binary64, format]

private lemma phi_two64 : phiQ binary64 two64 = 2 := by
  norm_num [phiQ, finiteQ, two64, binary64, format]

private lemma phi_three64 : phiQ binary64 three64 = 3 := by
  norm_num [phiQ, finiteQ, three64, binary64, format]

private lemma phi_eight64 : phiQ binary64 eight64 = 8 := by
  norm_num [phiQ, finiteQ, eight64, binary64, format]

private lemma phi_eleven64 : phiQ binary64 eleven64 = 11 := by
  norm_num [phiQ, finiteQ, eleven64, binary64, format]

lemma binary64NaNInfinityDistanceQ :
    distQ binary64 Value.nan (.infinity 0) = 1 := by
  norm_num [distQ, phiQ, binary64, format]

lemma binary64SignedZeroDistanceQ :
    distQ binary64 (.zero 1) (.zero 0) = (2 : ℚ) ^ (-1075 : ℤ) := by
  norm_num [distQ, phiQ, binary64, format]

lemma binary64SignedZeroSquaredDistanceQ :
    squareDistQ binary64 (.zero 1) (.zero 0) = (2 : ℚ) ^ (-2150 : ℤ) := by
  norm_num [squareDistQ, phiQ, binary64, format]
  rw [show (2150 : ℕ) = 1075 * 2 by norm_num, pow_mul]

lemma squaredStrictAntitriangleOneTwoThree :
    squareDistQ binary64 one64 two64 + squareDistQ binary64 two64 three64 <
    squareDistQ binary64 one64 three64 := by
  norm_num [squareDistQ, phi_one64, phi_two64, phi_three64]

private lemma distance_eq_nat_of_distQ {x y : Value binary64} {n : ℕ}
    (h : distQ binary64 x y = n) :
    absDistance binary64 x y = n := by
  apply NNReal.coe_injective
  have hcast : (distQ binary64 x y : ℝ) = (n : ℝ) := by exact_mod_cast h
  rw [← distQ_cast]
  exact hcast

private lemma d_one_eleven : absDistance binary64 one64 eleven64 = 10 := by
  apply distance_eq_nat_of_distQ
  rw [distQ, phi_one64, phi_eleven64]
  norm_num [distQ]

private lemma d_one_eight : absDistance binary64 one64 eight64 = 7 := by
  apply distance_eq_nat_of_distQ
  rw [distQ, phi_one64, phi_eight64]
  norm_num [distQ]

private lemma d_one_one : absDistance binary64 one64 one64 = 0 := by
  apply NNReal.coe_injective
  simp [absDistance]

private lemma d_eleven_eleven : absDistance binary64 eleven64 eleven64 = 0 := by
  apply NNReal.coe_injective
  simp [absDistance]

private lemma ieee_one_le_eleven : ieeeLe binary64 one64 eleven64 := by
  rw [ieeeLe_iff_phiQ_le, phi_one64, phi_eleven64]
  norm_num

private lemma ieee_one_le_eight : ieeeLe binary64 one64 eight64 := by
  rw [ieeeLe_iff_phiQ_le, phi_one64, phi_eight64]
  norm_num

private lemma ieee_refl (x : Value binary64) : ieeeLe binary64 x x :=
  (ieeeLe_iff_phiQ_le binary64 x x).2 le_rfl

private lemma sup_range_two {α : Type} [SemilatticeSup α] [OrderBot α]
    (f : ℕ → α) : (Finset.range 2).sup f = f 0 ⊔ f 1 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have hi' : i = 0 ∨ i = 1 := by
      have : i < 2 := Finset.mem_range.mp hi
      omega
    rcases hi' with rfl | rfl
    · exact le_sup_of_le_left le_rfl
    · exact le_sup_of_le_right le_rfl
  · apply sup_le
    · exact Finset.le_sup (f := f) (by norm_num : 0 ∈ Finset.range 2)
    · exact Finset.le_sup (f := f) (by norm_num : 1 ∈ Finset.range 2)

private lemma d_nan_nan : absDistance binary64 Value.nan Value.nan = 0 := by
  apply NNReal.coe_injective
  simp [absDistance]

private lemma pointwise_1_1_le_11_1 :
    listLe (ieeeLe binary64) Value.nan [one64, one64] [eleven64, one64] := by
  refine ⟨rfl, ?_⟩
  intro i hi
  have hi2 : i < 2 := by simpa using hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · simpa [List.getD] using ieee_one_le_eleven
  · simpa [List.getD] using ieee_refl one64

private lemma pointwise_11_1_le_11_8 :
    listLe (ieeeLe binary64) Value.nan [eleven64, one64] [eleven64, eight64] := by
  refine ⟨rfl, ?_⟩
  intro i hi
  have hi2 : i < 2 := by simpa using hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · simpa [List.getD] using ieee_refl eleven64
  · simpa [List.getD] using ieee_one_le_eight

private lemma linf_start_end :
    Lax544225.ListSpaces.maxDistance (absDistance binary64) Value.nan
      [one64, one64] [eleven64, eight64] = 10 := by
  norm_num [Lax544225.ListSpaces.maxDistance, Lax544225.ListSpaces.lengthPenalty,
    sup_range_two, List.getD,
    d_one_eleven, d_one_eight]

private lemma linf_start_middle :
    Lax544225.ListSpaces.maxDistance (absDistance binary64) Value.nan
      [one64, one64] [eleven64, one64] = 10 := by
  norm_num [Lax544225.ListSpaces.maxDistance, Lax544225.ListSpaces.lengthPenalty,
    sup_range_two, List.getD,
    d_one_eleven, d_one_one]

private lemma linf_middle_end :
    Lax544225.ListSpaces.maxDistance (absDistance binary64) Value.nan
      [eleven64, one64] [eleven64, eight64] = 7 := by
  norm_num [Lax544225.ListSpaces.maxDistance, Lax544225.ListSpaces.lengthPenalty,
    sup_range_two, List.getD,
    d_eleven_eleven, d_one_eight]

lemma binary64PointwiseMaximumFailure :
    listLe (ieeeLe binary64) Value.nan [one64, one64] [eleven64, one64] ∧
    listLe (ieeeLe binary64) Value.nan [eleven64, one64] [eleven64, eight64] ∧
    Lax544225.ListSpaces.maxDistance (absDistance binary64) Value.nan [one64, one64]
        [eleven64, eight64] <
      Lax544225.ListSpaces.maxDistance (absDistance binary64) Value.nan [one64, one64]
        [eleven64, one64] +
        Lax544225.ListSpaces.maxDistance (absDistance binary64) Value.nan [eleven64, one64]
          [eleven64, eight64] := by
  refine ⟨pointwise_1_1_le_11_1, pointwise_11_1_le_11_8, ?_⟩
  rw [linf_start_end, linf_start_middle, linf_middle_end]
  norm_num

lemma binary64NaNListLengthPenalty :
    Lax544225.ListSpaces.maxDistance (absDistance binary64) Value.nan [Value.nan]
      [Value.nan, Value.nan] = 1 := by
  simp [Lax544225.ListSpaces.maxDistance, Lax544225.ListSpaces.lengthPenalty,
    sup_range_two, List.getD, d_nan_nan]

lemma binary64SumProductOrdered (n : ℕ) :
    IsOrdered (sumDistance (absDistance binary64) n) (productLe (ieeeLe binary64) n) := by
  exact Lax544225Proofs.sumProductSpace (absDistance binary64) (ieeeLe binary64)
    (FloatEmbedding.floatAbsoluteSpace binary64) n

lemma binary64MaximumProductOrdered (n : ℕ) :
    IsOrdered (Lax544225.MaximumProductSpace.maxDistance (absDistance binary64) n)
      (Lax544225.MaximumProductSpace.synchronizedLe (absDistance binary64) (ieeeLe binary64) n) := by
  exact Lax544225Proofs.maximumProductSpace (absDistance binary64) (ieeeLe binary64)
    (FloatEmbedding.floatAbsoluteSpace binary64)
    (FloatEmbedding.floatAbsoluteAdditivity binary64) n

lemma binary64SumListOrdered :
    IsOrdered (Lax544225.ListSpaces.sumDistance (absDistance binary64) Value.nan)
      (Lax544225.ListSpaces.listLe (ieeeLe binary64) Value.nan) := by
  exact Lax544225Proofs.sumListSpace (absDistance binary64) (ieeeLe binary64)
    (FloatEmbedding.floatAbsoluteSpace binary64) Value.nan

lemma binary64MaximumListOrdered :
    IsOrdered (Lax544225.ListSpaces.maxDistance (absDistance binary64) Value.nan)
      (Lax544225.ListSpaces.synchronizedListLe (absDistance binary64) (ieeeLe binary64) Value.nan) := by
  exact Lax544225Proofs.maximumListSpace (absDistance binary64) (ieeeLe binary64)
    (FloatEmbedding.floatAbsoluteSpace binary64)
    (FloatEmbedding.floatAbsoluteAdditivity binary64) Value.nan

end Lax544225Proofs.FlocqExamples
