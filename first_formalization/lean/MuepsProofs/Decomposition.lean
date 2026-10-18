/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.PrecisionObstruction
import MuepsProofs.SubspaceDistance
import MuepsProofs.Basic
import Mathlib.Data.Set.Finite.Basic

universe u
namespace MuepsProofs.Decomposition
open scoped NNReal
open Mueps Semimetric Partitions PartitionRobustness Balls Decomposition OrderedSemimetric PrecisionGaps

private def trace {S : Type u} (A B : Set S) : Set A := {x | x.val ∈ B}
private def traceFamily {S : Type u} (A : Set S) (P : Set (Set S)) : Set (Set A) :=
  trace A '' {B | B ∈ P ∧ (trace A B).Nonempty}

private lemma trace_partition {S : Type u} (A : Set S) {P : Set (Set S)}
    (hP : IsPartition P) : IsPartition (traceFamily A P) := by
  classical
  apply (Basic.isPartition_iff _).mpr
  refine ⟨(hP.1.subset (by intro B hB; exact hB.1)).image (trace A), ?_, ?_⟩
  · rintro C ⟨B, hB, rfl⟩
    exact hB.2
  · intro x
    obtain ⟨B, hB, hu⟩ := hP.2.2 x.val
    refine ⟨trace A B, ⟨⟨B, ⟨hB.1, x, hB.2⟩, rfl⟩, hB.2⟩, ?_⟩
    rintro C ⟨⟨E, hE, rfl⟩, hxE⟩
    have hEB : E = B := hu E ⟨hE.1, hxE⟩
    rw [hEB]

private lemma trace_robust {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    {P : Set (Set S)} (hP : IsPartition P) (A : Set S) (hA : IsSemimetric (restrict d A))
    (μ ε : ℝ≥0) (hrob : Robust d hd P hP μ ε)
    (hclosed : ∀ x ∈ A, ball d hd x μ ⊆ A) :
    Robust (restrict d A) hA (traceFamily A P) (trace_partition A hP) μ ε := by
  intro x
  obtain ⟨y, hxy, B, hB, hxB, hball⟩ := hrob x.val
  have hyA := hclosed x.val x.property hxy
  refine ⟨⟨y, hyA⟩, hxy, trace A B, ?_, hxB, ?_⟩
  · exact ⟨B, ⟨hB, x, hxB⟩, rfl⟩
  · intro z hz
    exact hball hz

private lemma piece_monochromatic {S : Type u} (d : Distance S)
    (hd : IsSemimetric d) {P : Set (Set S)} (hP : IsPartition P) (μ ε : ℝ≥0)
    (hrob : Robust d hd P hP μ ε) (A : Set S) (hA : IsSemimetric (restrict d A))
    (hclosed : ∀ x ∈ A, ball d hd x μ ⊆ A)
    (hlocal : OnlyTrivial (restrict d A) hA μ ε) :
    ∀ B ∈ P, (A ∩ B).Nonempty → A ⊆ B := by
  intro B hB hAB
  have heq := hlocal (traceFamily A P) (trace_partition A hP)
    (trace_robust d hd hP A hA μ ε hrob hclosed)
  obtain ⟨x, hxA, hxB⟩ := hAB
  have hmem : trace A B ∈ traceFamily A P :=
    ⟨B, ⟨hB, ⟨⟨x, hxA⟩, hxB⟩⟩, rfl⟩
  rw [heq] at hmem
  have ht : trace A B = Set.univ := Set.mem_singleton_iff.mp hmem
  intro y hy
  have : (⟨y, hy⟩ : A) ∈ trace A B := ht ▸ Set.mem_univ _
  exact this

/--
Local triviality propagates through a closed overlap decomposition.

# Proof strategy

Intersect a robust partition with a μ-closed piece and discard empty traces.
The traces form a robust partition of the induced subspace, hence are trivial.
Each piece is therefore monochromatic. A finite overlap chain propagates its
part to any input, forcing that part to be the whole carrier.

# Attribution

Theorem 5 of Aleksandrov and Völlinger, *Relaxing Global Classifier Robustness
on Semimetric Spaces*, supplied FSEN 2027 manuscript, pp. 13–14.
-/
theorem decompositionObstruction {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (D : Set (Set S)) (μ ε : ℝ≥0) (_hε : 0 < ε)
    (hD : IsDecomposition d hd D μ)
    (hlocal : ∀ A ∈ D, ∀ hA : IsSemimetric (restrict d A),
      OnlyTrivial (restrict d A) hA μ ε) : OnlyTrivial d hd μ ε := by
  classical
  intro P hP hrob
  have hmono : ∀ A ∈ D, ∀ B ∈ P, (A ∩ B).Nonempty → A ⊆ B := by
    intro A hA
    have hsm : IsSemimetric (restrict d A) :=
      restrict_isSemimetric d hd A (hD.2.1 A hA)
    exact piece_monochromatic d hd hP μ ε hrob A hsm (hD.2.2.1 A hA)
      (hlocal A hA hsm)
  have hall : ∀ B ∈ P, B = Set.univ := by
    intro B hB
    obtain ⟨x, hx⟩ := Setoid.nonempty_of_mem_partition hP.2 hB
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨A, hA, E, hE, hxA, hyE, hpath⟩ := hD.2.2.2 x y
    have hstart : A ⊆ B := hmono A hA B hB ⟨x, hxA, hx⟩
    have hend : E ⊆ B := by
      clear hyE hE
      induction hpath with
      | refl => exact hstart
      | @tail C E hpath hCE ih =>
          obtain ⟨z, hzC, hzE⟩ := hCE.2.2
          exact hmono E hCE.2.1 B hB ⟨z, hzE, ih hzC⟩
    exact hend hyE
  change P = {Set.univ}
  apply Set.ext
  intro B
  constructor
  · intro hB
    exact Set.mem_singleton_iff.mpr (hall B hB)
  · intro hB
    have hBu := Set.mem_singleton_iff.mp hB
    obtain ⟨x⟩ := hd.1
    obtain ⟨A, ⟨hA, _⟩, _⟩ := hP.2.2 x
    simpa [hBu, hall A hA] using hA

/--
Precision bounds on totally ordered decomposition pieces imply global triviality.

# Proof strategy

Give each piece its inherited linear order, preserving the interval steps in
its precision measures. Apply the total-order precision obstruction on each
piece, then use the closed overlap decomposition theorem.

# Attribution

Corollary 3 of Aleksandrov and Völlinger, *Relaxing Global Classifier Robustness
on Semimetric Spaces*, supplied FSEN 2027 manuscript, p. 14.
-/
lemma partialOrderPrecisionBound {S : Type u} [Finite S] [PartialOrder S]
    (d : Distance S) (hd : IsOrdered d (· ≤ ·)) (D : Set (Set S))
    (μ ε : ℝ≥0) (hε : 0 < ε) (hD : IsDecomposition d hd.1 D μ)
    (hchain : ∀ A ∈ D, ∀ x ∈ A, ∀ y ∈ A, x ≤ y ∨ y ≤ x)
    (hbound : ∀ A ∈ D, ∀ hA : IsOrdered (restrict d A) (· ≤ ·),
      threshold (restrict d A) hA μ ≤ ε) : OnlyTrivial d hd.1 μ ε := by
  classical
  apply MuepsProofs.Decomposition.decompositionObstruction d hd.1 D μ ε hε hD
  intro A hA hsm
  let : LinearOrder A := {
    (inferInstance : PartialOrder A) with
    le_total := fun x y => hchain A hA x.val x.property y.val y.property
    toDecidableLE := Classical.decRel _ }
  have ho : IsOrdered (restrict d A) (· ≤ ·) := by
    refine ⟨hsm, inferInstance, ?_⟩
    intro x y z hxy hyz
    exact hd.2.2 x.val y.val z.val hxy hyz
  exact MuepsProofs.OrderedBounds.precisionObstruction (restrict d A) ho μ ε hε (hbound A hA ho)

end MuepsProofs.Decomposition
