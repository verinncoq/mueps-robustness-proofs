import Lax544225.OrderedSemimetric

/-! Ordinary proof helpers for the revised paper's real-line examples (p. 8). -/

namespace Lax544225Proofs.PaperExamples

open scoped NNReal
open Lax544225.Semimetric Lax544225.OrderedSemimetric

/-- The ordinary absolute distance on the real line. -/
def realAbsDistance (x y : ℝ) : ℝ≥0 := Real.toNNReal |x - y|

/-- The squared distance on the real line. -/
def realSquaredDistance (x y : ℝ) : ℝ≥0 := Real.toNNReal ((x - y) ^ 2)

lemma realAbsDistance_coe (x y : ℝ) : (realAbsDistance x y : ℝ) = |x-y| := by
  exact Real.coe_toNNReal _ (abs_nonneg _)

lemma realSquaredDistance_coe (x y : ℝ) : (realSquaredDistance x y : ℝ) = (x-y)^2 := by
  exact Real.coe_toNNReal _ (sq_nonneg _)

/-- Absolute distance on ℝ is an ordered semimetric space. -/
lemma realAbsDistance_isOrdered : IsOrdered realAbsDistance (· ≤ ·) := by
  refine ⟨?_, inferInstance, ?_⟩
  · refine ⟨⟨⟨0⟩⟩, ?_, ?_⟩
    · intro x y
      change |x-y|.toNNReal = 0 ↔ x = y
      rw [Real.toNNReal_eq_zero]
      constructor
      · intro h
        have hz : |x-y| = 0 := le_antisymm h (abs_nonneg _)
        exact sub_eq_zero.mp (abs_eq_zero.mp hz)
      · rintro rfl
        simp
    · intro x y
      apply congrArg Real.toNNReal
      exact abs_sub_comm x y
  · intro a b c hab hbc
    change (↑(realAbsDistance a b) + ↑(realAbsDistance b c) : ℝ) ≤ ↑(realAbsDistance a c)
    rw [realAbsDistance_coe, realAbsDistance_coe, realAbsDistance_coe]
    rw [abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr hbc), abs_of_nonpos (sub_nonpos.mpr (le_trans hab hbc))]
    nlinarith

/-- Squared distance on ℝ is an ordered semimetric space. -/
lemma realSquaredDistance_isOrdered : IsOrdered realSquaredDistance (· ≤ ·) := by
  refine ⟨?_, inferInstance, ?_⟩
  · refine ⟨⟨⟨0⟩⟩, ?_, ?_⟩
    · intro x y
      change ((x-y)^2).toNNReal = 0 ↔ x = y
      rw [Real.toNNReal_eq_zero]
      constructor
      · intro h
        have hz : (x-y)^2 = 0 := le_antisymm h (sq_nonneg _)
        exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
      · rintro rfl
        simp
    · intro x y
      apply congrArg Real.toNNReal
      ring
  · intro a b c hab hbc
    change (↑(realSquaredDistance a b) + ↑(realSquaredDistance b c) : ℝ) ≤ ↑(realSquaredDistance a c)
    rw [realSquaredDistance_coe, realSquaredDistance_coe, realSquaredDistance_coe]
    have hab' : 0 ≤ b-a := sub_nonneg.mpr hab
    have hbc' : 0 ≤ c-b := sub_nonneg.mpr hbc
    nlinarith [mul_nonneg hab' hbc']

/-- Squared distance violates the metric triangle inequality at 0, 1, 2. -/
lemma realSquaredDistance_not_triangle :
    ¬ realSquaredDistance 0 2 ≤ realSquaredDistance 0 1 + realSquaredDistance 1 2 := by
  norm_num [realSquaredDistance, Real.toNNReal_of_nonneg, sq_nonneg]

end Lax544225Proofs.PaperExamples
