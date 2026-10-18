/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import MuepsProofs

/-! Paper-facing statements. Each is an alias of a complete proof in MuepsProofs. -/

universe u


namespace Mueps.Paper.CoveringCharacterization

open Mueps
open scoped NNReal
open Semimetric Partitions PartitionRobustness Balls

/-- A finite partition is (μ,ε)-robust exactly when no μ-ball centered in a part is covered by ε-balls from its complement. -/
theorem from_paper {S : Type u} (d : Distance S) (hd : IsSemimetric d) (P : Set (Set S))
    (hP : IsPartition P) (μ ε : ℝ≥0) (hε : 0 < ε) :
    Robust d hd P hP μ ε ↔ (∀ A ∈ P, ∀ x ∈ A, ¬ ball d hd x μ ⊆ neighborhood d hd Aᶜ ε) := by
  exact MuepsProofs.MainResults.coveringCharacterization d hd P hP μ ε hε

end Mueps.Paper.CoveringCharacterization


namespace Mueps.Paper.FloatAbsoluteSpace

open Mueps
open BinaryFloats OrderedSemimetric
open scoped NNReal
open Mueps.FloatAbsoluteSpace

/-- The absolute-distance construction is an ordered semimetric space. -/
theorem from_paper (F : Format) : IsOrdered (absDistance F) (ieeeLe F) := by
  exact MuepsProofs.FloatEmbedding.floatAbsoluteSpace F

end Mueps.Paper.FloatAbsoluteSpace


namespace Mueps.Paper.FloatSquaredSpace

open Mueps
open BinaryFloats OrderedSemimetric
open scoped NNReal
open Mueps.FloatSquaredSpace

/-- The squared-distance construction is an ordered semimetric space. -/
theorem from_paper (F : Format) : IsOrdered (squareDistance F) (ieeeLe F) := by
  exact MuepsProofs.FloatEmbedding.floatSquaredSpace F

end Mueps.Paper.FloatSquaredSpace


namespace Mueps.Paper.SumProductSpace

open Mueps
open Semimetric OrderedSemimetric
open scoped BigOperators
open Mueps.SumProductSpace

/-- Sum products preserve ordered semimetric spaces. -/
theorem from_paper {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrdered d le) (n : ℕ) : IsOrdered (sumDistance d n) (productLe le n) := by
  exact MuepsProofs.sumProductSpace d le hd n

end Mueps.Paper.SumProductSpace


namespace Mueps.Paper.MaximumProductSpace

open Mueps
open Semimetric OrderedSemimetric SumProductSpace
open Mueps.MaximumProductSpace

/-- Synchronized maximum products preserve ordered semimetric spaces. -/
theorem from_paper {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrdered d le) (hadd : Additive d le) (n : ℕ) :
    IsOrdered (maxDistance d n) (synchronizedLe d le n) := by
  exact MuepsProofs.maximumProductSpace d le hd hadd n

end Mueps.Paper.MaximumProductSpace


namespace Mueps.Paper.ListSpaces

open Mueps
open scoped NNReal
open Semimetric OrderedSemimetric
open scoped BigOperators
open Mueps.ListSpaces

/-- Both padded-list constructions are ordered semimetric spaces. -/
theorem from_paper :
    (∀ {S : Type u} (d : Distance S) (le : S → S → Prop),
      IsOrdered d le → ∀ pad : S,
        IsOrdered (Mueps.ListSpaces.sumDistance d pad) (Mueps.ListSpaces.listLe le pad)) ∧
    (∀ {S : Type u} (d : Distance S) (le : S → S → Prop),
      IsOrdered d le → Additive d le → ∀ pad : S,
        IsOrdered (Mueps.ListSpaces.maxDistance d pad)
          (Mueps.ListSpaces.synchronizedListLe d le pad)) := by
  exact MuepsProofs.listSpaces

end Mueps.Paper.ListSpaces


namespace Mueps.Paper.GeneralExistence

open Mueps
open scoped NNReal
open Semimetric PartitionRobustness Balls

/-- The trivial partition is the only robust partition exactly when every nonempty proper cut admits a covering point on one side from ε-balls centered on the other side. -/
theorem from_paper {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (μ ε : ℝ≥0) (hε : 0 < ε) :
    OnlyTrivial d hd μ ε ↔ (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd x μ ⊆ neighborhood d hd Aᶜ ε) ∨
        (x ∈ Aᶜ ∧ ball d hd x μ ⊆ neighborhood d hd A ε)) := by
  exact MuepsProofs.MainResults.generalExistence d hd μ ε hε

end Mueps.Paper.GeneralExistence


namespace Mueps.Paper.BoundaryCoveringCharacterization

open Mueps
open scoped NNReal
open Semimetric OrderedSemimetric Balls Boundary

/-- In a finite totally ordered semimetric space, covering every proper cut is equivalent to covering its within-side μ-ball from the opposite boundary. -/
theorem from_paper {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε) :
    (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd.1 x μ ⊆ neighborhood d hd.1 Aᶜ ε) ∨
        (x ∈ Aᶜ ∧ ball d hd.1 x μ ⊆ neighborhood d hd.1 A ε)) ↔ (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd.1 x μ ∩ A ⊆ neighborhood d hd.1 (complementBoundary A) ε) ∨
        (x ∈ Aᶜ ∧ ball d hd.1 x μ ∩ Aᶜ ⊆ neighborhood d hd.1 (boundary A) ε)) := by
  exact MuepsProofs.MainResults.boundaryCoveringCharacterization d hd μ ε hε

end Mueps.Paper.BoundaryCoveringCharacterization


namespace Mueps.Paper.BoundaryExistence

open Mueps
open scoped NNReal
open Semimetric OrderedSemimetric PartitionRobustness Boundary Balls

/-- In a finite totally ordered semimetric space, only-trivial robustness is equivalent to opposite-boundary covering of every nonempty proper cut. -/
theorem from_paper {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε) :
    OnlyTrivial d hd.1 μ ε ↔ (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd.1 x μ ∩ A ⊆ neighborhood d hd.1 (complementBoundary A) ε) ∨
        (x ∈ Aᶜ ∧ ball d hd.1 x μ ∩ Aᶜ ⊆ neighborhood d hd.1 (boundary A) ε)) := by
  exact MuepsProofs.MainResults.boundaryExistence d hd μ ε hε

end Mueps.Paper.BoundaryExistence


namespace Mueps.Paper.SuccessorCovering

open Mueps
open scoped NNReal
open Semimetric OrderedSemimetric Balls Boundary PrecisionGaps

/-- In a finite totally ordered semimetric space, ε≥Δδμ+Δ implies B(x,μ)⊆B(y,ε) whenever y is the immediate successor of x. -/
theorem from_paper {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε)
    (hbound : threshold d hd μ ≤ ε) (x y : S) (hxy : Successor x y) :
    ball d hd.1 x μ ⊆ ball d hd.1 y ε := by
  exact MuepsProofs.OrderedBounds.successorCovering d hd μ ε hε hbound x y hxy

end Mueps.Paper.SuccessorCovering


namespace Mueps.Paper.PrecisionObstruction

open Mueps
open scoped NNReal
open Semimetric OrderedSemimetric PartitionRobustness PrecisionGaps

/-- In a finite totally ordered semimetric space, ε≥Δδμ+Δ forces every (μ,ε)-robust partition to be trivial. -/
theorem from_paper {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε)
    (hbound : threshold d hd μ ≤ ε) : OnlyTrivial d hd.1 μ ε := by
  exact MuepsProofs.OrderedBounds.precisionObstruction d hd μ ε hε hbound

end Mueps.Paper.PrecisionObstruction


namespace Mueps.Paper.Noncompositionality

open Mueps
open Semimetric Partitions PartitionRobustness

/-- Counterexamples to both compositionality implications in Lemma 1. -/
theorem from_paper :
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
  exact MuepsProofs.Counterexamples.noncompositionality

end Mueps.Paper.Noncompositionality


namespace Mueps.Paper.DecompositionObstruction

open Mueps
open scoped NNReal
open Semimetric Decomposition PartitionRobustness

/-- If a semimetric space has a (μ,ε)-decomposition and each induced subspace admits only trivial (μ,ε)-robust partitions, then the whole space admits only trivial (μ,ε)-robust partitions. -/
theorem from_paper {S : Type u} (d : Distance S) (hd : IsSemimetric d) (D : Set (Set S))
    (μ ε : ℝ≥0) (hε : 0 < ε) (hD : IsDecomposition d hd D μ)
    (hlocal : ∀ A ∈ D, ∀ hA : IsSemimetric (fun x y : A => d x.val y.val),
      OnlyTrivial (fun x y : A => d x.val y.val) hA μ ε) : OnlyTrivial d hd μ ε := by
  exact MuepsProofs.Decomposition.decompositionObstruction d hd D μ ε hε hD hlocal

end Mueps.Paper.DecompositionObstruction


namespace Mueps.Paper.PartialOrderPrecisionBound

open Mueps
open scoped NNReal
open Semimetric OrderedSemimetric Decomposition PartitionRobustness PrecisionGaps

/-- In a finite partially ordered semimetric space, a (μ,ε)-decomposition into totally ordered pieces admits only trivial robust partitions if ε≥Δᵢδᵢμ+Δᵢ for every piece. -/
theorem from_paper {S : Type u} [Finite S] [PartialOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (D : Set (Set S)) (μ ε : ℝ≥0) (hε : 0 < ε)
    (hD : IsDecomposition d hd.1 D μ)
    (hchain : ∀ A ∈ D, ∀ x ∈ A, ∀ y ∈ A, x ≤ y ∨ y ≤ x)
    (hbound : ∀ A ∈ D, ∀ hA : IsOrdered (fun x y : A => d x.val y.val) (· ≤ ·),
      threshold (fun x y : A => d x.val y.val) hA μ ≤ ε) : OnlyTrivial d hd.1 μ ε := by
  exact MuepsProofs.Decomposition.partialOrderPrecisionBound d hd D μ ε hε hD hchain hbound

end Mueps.Paper.PartialOrderPrecisionBound
