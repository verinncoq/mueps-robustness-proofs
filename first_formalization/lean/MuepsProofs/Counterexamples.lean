/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.SubspaceDistance
import MuepsProofs.Basic
import MuepsProofs.Existence
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace MuepsProofs.Counterexamples
open scoped NNReal
open Mueps Semimetric Partitions PartitionRobustness Balls

private def line (x y : Fin 4) : ℝ≥0 := Nat.dist x.val y.val
private def low : Set (Fin 4) := {x | x.val < 2}
private def split : Set (Set (Fin 4)) := {low, lowᶜ}

private lemma line_semimetric : IsSemimetric line := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;> norm_num [line, Nat.dist, Fin.ext_iff]
  · intro x y
    simp [line, Nat.dist_comm]

private lemma split_partition : IsPartition split := by
  apply Existence.cut_partition low
  · exact ⟨0, by norm_num [low]⟩
  · exact ⟨3, by norm_num [low]⟩

private lemma split_robust (hd : IsSemimetric line) (hP : IsPartition split) :
    Robust line hd split hP 1 1 := by
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
private lemma common_ball_trivial {S : Type*} (d : Distance S) (hd : IsSemimetric d)
    (pivot : S) (μ ε : ℝ≥0) (hcommon : ∀ x, d pivot x ≤ ε) :
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

Lemma 1.1 of Aleksandrov and Völlinger, *Relaxing Global Classifier Robustness
on Semimetric Spaces*, supplied FSEN 2027 manuscript, p. 13.
-/
lemma restrictionCounterexample : ∃ (d : Distance (Fin 4)) (hd : IsSemimetric d)
    (P : Set (Set (Fin 4))) (hP : IsPartition P) (A : Set (Fin 4)),
    Robust d hd P hP 1 1 ∧ A.Nonempty ∧ Aᶜ.Nonempty ∧
    (∀ hA : IsSemimetric (fun x y : A => d x.val y.val),
      OnlyTrivial (fun x y : A => d x.val y.val) hA 1 1) ∧
    ¬ ∃ B ∈ P, A ⊆ B := by
  let A : Set (Fin 4) := {x | x.val = 1 ∨ x.val = 2}
  refine ⟨line, line_semimetric, split, split_partition, A,
    split_robust line_semimetric split_partition,
    ⟨1, by simp [A]⟩, ⟨0, by simp [A]⟩, ?_, ?_⟩
  · intro hA
    apply common_ball_trivial (restrict line A) hA ⟨1, by simp [A]⟩ 1 1
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

Lemma 1.2 of Aleksandrov and Völlinger, *Relaxing Global Classifier Robustness
on Semimetric Spaces*, supplied FSEN 2027 manuscript, p. 13.
-/
lemma unionCounterexample : ∃ (d : Distance (Fin 4)) (hd : IsSemimetric d)
    (A B : Set (Fin 4)) (P : Set (Set (Fin 4))) (hP : IsPartition P),
    Aᶜ.Nonempty ∧ Bᶜ.Nonempty ∧ (A ∩ B).Nonempty ∧ A ∪ B = Set.univ ∧
    (∀ hA : IsSemimetric (fun x y : A => d x.val y.val),
      OnlyTrivial (fun x y : A => d x.val y.val) hA 1 1) ∧
    (∀ hB : IsSemimetric (fun x y : B => d x.val y.val),
      OnlyTrivial (fun x y : B => d x.val y.val) hB 1 1) ∧
    Robust d hd P hP 1 1 ∧ ¬ IsTrivial P := by
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
    apply common_ball_trivial (restrict line A) hA ⟨1, by simp [A]⟩ 1 1
    intro x
    obtain ⟨x, hx⟩ := x
    change x.val < 3 at hx
    fin_cases x
    all_goals norm_num [restrict, line, Nat.dist] at *
    all_goals simp_all
  · intro hB
    apply common_ball_trivial (restrict line B) hB ⟨2, by simp [B]⟩ 1 1
    intro x
    obtain ⟨x, hx⟩ := x
    change 0 < x.val at hx
    fin_cases x
    all_goals norm_num [restrict, line, Nat.dist] at *
    all_goals simp_all

/--
Both compositionality implications fail.

# Proof strategy

Combine the restriction and union counterexample lemmas. Both reuse the same
four-point semimetric, robust two-part partition, and common-ball triviality
criterion; their subsets witness the two failures separately.

# Attribution

Lemma 1 of Aleksandrov and Völlinger's supplied FSEN 2027 manuscript, p. 13.
-/
lemma noncompositionality :
    (∃ (d : Distance (Fin 4)) (hd : IsSemimetric d)
      (P : Set (Set (Fin 4))) (hP : IsPartition P) (A : Set (Fin 4)),
    Robust d hd P hP 1 1 ∧ A.Nonempty ∧ Aᶜ.Nonempty ∧
    (∀ hA : IsSemimetric (fun x y : A => d x.val y.val),
      OnlyTrivial (fun x y : A => d x.val y.val) hA 1 1) ∧
    ¬ ∃ B ∈ P, A ⊆ B) ∧
    (∃ (d : Distance (Fin 4)) (hd : IsSemimetric d)
      (A B : Set (Fin 4)) (P : Set (Set (Fin 4))) (hP : IsPartition P),
    Aᶜ.Nonempty ∧ Bᶜ.Nonempty ∧ (A ∩ B).Nonempty ∧ A ∪ B = Set.univ ∧
    (∀ hA : IsSemimetric (fun x y : A => d x.val y.val),
      OnlyTrivial (fun x y : A => d x.val y.val) hA 1 1) ∧
    (∀ hB : IsSemimetric (fun x y : B => d x.val y.val),
      OnlyTrivial (fun x y : B => d x.val y.val) hB 1 1) ∧
    Robust d hd P hP 1 1 ∧ ¬ IsTrivial P) := by
  exact ⟨restrictionCounterexample, unionCounterexample⟩

end MuepsProofs.Counterexamples
