import Lax544225Proofs.SubspaceDistance
import Lax544225.Noncompositionality
import Lax544225Proofs.Basic
import Lax544225Proofs.Existence
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Lax544225Proofs.Counterexamples
open scoped NNReal
open Lax544225 SemimetricSpace Partitions PartitionRobustness Balls

private def line (x y : Fin 4) : ℝ≥0 := Nat.dist x.val y.val
private def low : Set (Fin 4) := {x | x.val < 2}
private def split : Set (Set (Fin 4)) := {low, lowᶜ}

private lemma line_semimetric : IsSemimetricSpace line := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;> norm_num [line, Nat.dist, Fin.ext_iff]
  · intro x y
    simp [line, Nat.dist_comm]

private lemma split_partition : IsPartition split := by
  apply Existence.cut_partition low
  · exact ⟨0, by norm_num [low]⟩
  · exact ⟨3, by norm_num [low]⟩

private lemma split_robust (hd : IsSemimetricSpace line) (hP : IsPartition split) :
    MuEpsilonRobustPartition line hd split hP 1 ⟨1, zero_lt_one⟩ := by
  intro x
  by_cases hx : x.val < 2
  · refine ⟨0, ?_, low, by simp [split], hx, ?_⟩
    · fin_cases x <;> norm_num [ball, line, Nat.dist, NNReal.sub_def, Real.toNNReal_of_nonpos] at *
    · intro y hy
      fin_cases y <;> norm_num [ball, line, Nat.dist, low, NNReal.sub_def, Real.toNNReal_of_nonpos] at *
  · refine ⟨3, ?_, lowᶜ, by simp [split], hx, ?_⟩
    · fin_cases x <;> norm_num [ball, line, Nat.dist, NNReal.sub_def, Real.toNNReal_of_nonpos] at *
    · intro y hy
      fin_cases y <;> norm_num [ball, line, Nat.dist, low, NNReal.sub_def, Real.toNNReal_of_nonpos] at *

private lemma split_nontrivial : ¬ IsTrivial split := by
  intro h
  have : low ∈ split := by simp [split]
  rw [h] at this
  have heq : low = Set.univ := Set.mem_singleton_iff.mp this
  have : (3 : Fin 4) ∈ low := heq ▸ Set.mem_univ _
  norm_num [low] at this

/-- If every ε-ball contains a common point, robustness forces a trivial partition. -/
private lemma common_ball_trivial {S : Type*} (d : Distance S) (hd : IsSemimetricSpace d)
    (pivot : S) (μ : ℝ≥0) (ε : ℝ>0) (hcommon : ∀ x, d pivot x ≤ ε) :
    OnlyTrivial d hd μ ε := by
  intro P hP hrob
  have hpart : ∀ B ∈ P, pivot ∈ B := by
    intro B hB
    obtain ⟨x, hx⟩ := Setoid.nonempty_of_mem_partition hP.2 hB
    obtain ⟨y, _, A, hA, hxA, hball⟩ := hrob x
    have heq := Basic.part_eq_of_mem hP hA hB hxA hx
    exact heq ▸ hball (hcommon y)
  have hall : ∀ B ∈ P, B = Set.univ := by
    intro B hB
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨A, ⟨hA, hxA⟩, _⟩ := hP.2.2 x
    have heq := Basic.part_eq_of_mem hP hA hB (hpart A hA) (hpart B hB)
    exact heq ▸ hxA
  change P = {Set.univ}
  apply Set.ext
  intro B
  constructor
  · intro hB
    exact Set.mem_singleton_iff.mpr (hall B hB)
  · intro hB
    have hBu := Set.mem_singleton_iff.mp hB
    obtain ⟨A, ⟨hA, _⟩, _⟩ := hP.2.2 pivot
    simpa [hBu, hall A hA] using hA

/--
The four-point line has a robust two-part partition, while its middle pair is
locally trivial and crosses both global parts.

# Proof strategy

Use ordinary integer distance on {0,1,2,3} and the cut at 2. Centers 0 and 3
witness robustness. In the restricted middle pair, every unit ball contains 1,
so the common-ball lemma forces triviality. The pair is in neither global part.

# Attribution

Lemma 1.1 of Aleksandrov, Kuske and Völlinger, *(μ,ε)-Robustness: Characterization, Existence, and Precision-Dependent Bounds*, revised FSEN 2027 manuscript (9 November 2026).
-/
lemma restrictionCounterexample : ∃ (d : Distance (Fin 4)) (hd : IsSemimetricSpace d)
    (P : Set (Set (Fin 4))) (hP : IsPartition P) (A : Set (Fin 4)),
    MuEpsilonRobustPartition d hd P hP 1 ⟨1, zero_lt_one⟩ ∧ A.Nonempty ∧ Aᶜ.Nonempty ∧
    (∀ hA : IsSemimetricSpace (fun x y : A => d x.val y.val),
      OnlyTrivial (fun x y : A => d x.val y.val) hA 1 ⟨1, zero_lt_one⟩) ∧
    ¬ ∃ B ∈ P, A ⊆ B := by
  let A : Set (Fin 4) := {x | x.val = 1 ∨ x.val = 2}
  refine ⟨line, line_semimetric, split, split_partition, A,
    split_robust line_semimetric split_partition,
    ⟨1, by simp [A]⟩, ⟨0, by simp [A]⟩, ?_, ?_⟩
  · intro hA
    apply common_ball_trivial (restrict line A) hA ⟨1, by simp [A]⟩ 1 ⟨1, zero_lt_one⟩
    intro x
    obtain ⟨x, hx⟩ := x
    change x.val = 1 ∨ x.val = 2 at hx
    fin_cases x
    all_goals norm_num [restrict, line, Nat.dist] at *
    all_goals simp_all
  · rintro ⟨B, hB, hsub⟩
    rcases Set.mem_insert_iff.mp hB with rfl | hB
    · have := hsub (show (2 : Fin 4) ∈ A by simp [A])
      norm_num [low] at this
    · have hB' : B = lowᶜ := Set.mem_singleton_iff.mp hB
      subst B
      have := hsub (show (1 : Fin 4) ∈ A by simp [A])
      norm_num [low] at this

/--
The overlapping triples of the four-point line are locally trivial, although
their union has a nontrivial robust partition.

# Proof strategy

Reuse the four-point line and split. Every unit ball in {0,1,2} contains 1,
and every unit ball in {1,2,3} contains 2. Apply the common-ball lemma on each
triple and verify their overlap and union directly.

# Attribution

Lemma 1.2 of Aleksandrov, Kuske and Völlinger, *(μ,ε)-Robustness: Characterization, Existence, and Precision-Dependent Bounds*, revised FSEN 2027 manuscript (9 November 2026).
-/
lemma unionCounterexample : ∃ (d : Distance (Fin 4)) (hd : IsSemimetricSpace d)
    (A B : Set (Fin 4)) (P : Set (Set (Fin 4))) (hP : IsPartition P),
    Aᶜ.Nonempty ∧ Bᶜ.Nonempty ∧ (A ∩ B).Nonempty ∧ A ∪ B = Set.univ ∧
    (∀ hA : IsSemimetricSpace (fun x y : A => d x.val y.val),
      OnlyTrivial (fun x y : A => d x.val y.val) hA 1 ⟨1, zero_lt_one⟩) ∧
    (∀ hB : IsSemimetricSpace (fun x y : B => d x.val y.val),
      OnlyTrivial (fun x y : B => d x.val y.val) hB 1 ⟨1, zero_lt_one⟩) ∧
    MuEpsilonRobustPartition d hd P hP 1 ⟨1, zero_lt_one⟩ ∧ ¬ IsTrivial P := by
  let A : Set (Fin 4) := {x | x.val < 3}
  let B : Set (Fin 4) := {x | 0 < x.val}
  refine ⟨line, line_semimetric, A, B, split, split_partition,
    ⟨3, by simp [A]⟩, ⟨0, by simp [B]⟩, ⟨1, by simp [A, B]⟩,
    ?_, ?_, ?_, split_robust line_semimetric split_partition, split_nontrivial⟩
  · apply Set.eq_univ_of_forall
    intro x
    change x.val < 3 ∨ 0 < x.val
    fin_cases x <;> norm_num
  · intro hA
    apply common_ball_trivial (restrict line A) hA ⟨1, by simp [A]⟩ 1 ⟨1, zero_lt_one⟩
    intro x
    obtain ⟨x, hx⟩ := x
    change x.val < 3 at hx
    fin_cases x
    all_goals norm_num [restrict, line, Nat.dist] at *
    all_goals simp_all
  · intro hB
    apply common_ball_trivial (restrict line B) hB ⟨2, by simp [B]⟩ 1 ⟨1, zero_lt_one⟩
    intro x
    obtain ⟨x, hx⟩ := x
    change 0 < x.val at hx
    fin_cases x
    all_goals norm_num [restrict, line, Nat.dist] at *
    all_goals simp_all

/--
---
conclusion: Lax544225.Noncompositionality.lemma1
---
Both compositionality implications fail.

# Proof strategy

Combine the restriction and union counterexample lemmas. Both reuse the same
four-point semimetric, robust two-part partition, and common-ball triviality
criterion; their subsets witness the two failures separately.

# Attribution

Lemma 1 of Aleksandrov, Kuske and Völlinger's revised FSEN 2027 manuscript (9 November 2026).
-/
lemma noncompositionality :
    ¬ Noncompositionality.RestrictionPrinciple ∧ ¬ Noncompositionality.UnionPrinciple := by
  constructor
  · intro h
    obtain ⟨d, hd, P, hP, A, hrob, hA, hAc, hlocal, hno⟩ := restrictionCounterexample
    have hsm := restrict_isSemimetric d hd A hA
    exact hno (h (Fin 4) d hd 1 ⟨1, zero_lt_one⟩ A hAc ⟨hsm, hlocal hsm⟩ P hP hrob)
  · intro h
    obtain ⟨d, hd, A, B, P, hP, hAc, hBc, hoverlap, hcover, hlocalA, hlocalB,
      hrob, hnontrivial⟩ := unionCounterexample
    have hsmA := restrict_isSemimetric d hd A (hoverlap.mono Set.inter_subset_left)
    have hsmB := restrict_isSemimetric d hd B (hoverlap.mono Set.inter_subset_right)
    have htrivial := h (Fin 4) d hd 1 ⟨1, zero_lt_one⟩ A B
      hAc hBc hoverlap hcover ⟨hsmA, hlocalA hsmA⟩ ⟨hsmB, hlocalB hsmB⟩
    exact hnontrivial (htrivial P hP hrob)

end Lax544225Proofs.Counterexamples
