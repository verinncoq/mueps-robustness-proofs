/- Adapted from lax-544225, source dbdbc610628949634c5cedeaa81437b2f7ce1293.
   Standalone Lean port, synchronized 11 November 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import MuepsProofs
import Mathlib.Order.Preorder.Chain

/-! Paper-facing statements, each proved by the corresponding complete theorem. -/

universe u

namespace Mueps.Paper.CoveringCharacterization

open Mueps
open scoped NNReal
open SemimetricSpace Partitions PartitionRobustness Balls

/-- A finite partition is (μ,ε)-robust exactly when no μ-ball centered in a part is covered by ε-balls from its complement. -/
theorem theorem1 {S : Type u} (d : Distance S) (hd : IsSemimetricSpace d) (P : Set (Set S))
    (hP : IsPartition P) (μ : ℝ≥0) (ε : ℝ>0) :
    MuEpsilonRobustPartition d hd P hP μ ε ↔ (∀ Sᵢ ∈ P, ∀ x ∈ Sᵢ, ¬ ball d hd x μ ⊆ unionOfBalls d hd Sᵢᶜ ε) := by
  exact MuepsProofs.MainResults.coveringCharacterization d hd P hP μ ε

end Mueps.Paper.CoveringCharacterization

namespace Mueps.Paper.GeneralExistence

open Mueps
open scoped NNReal
open SemimetricSpace PartitionRobustness Balls

/-- The trivial partition is the only robust partition exactly when every nonempty proper cut admits a covering point on one side from ε-balls centered on the other side. -/
theorem theorem2 {S : Type u} (d : Distance S) (hd : IsSemimetricSpace d)
    (μ : ℝ≥0) (ε : ℝ>0) :
    OnlyTrivial d hd μ ε ↔ (∀ S' : Set S, S'.Nonempty → S'ᶜ.Nonempty →
      ∃ x, (x ∈ S' ∧ ball d hd x μ ⊆ unionOfBalls d hd S'ᶜ ε) ∨
        (x ∈ S'ᶜ ∧ ball d hd x μ ⊆ unionOfBalls d hd S' ε)) := by
  exact MuepsProofs.MainResults.generalExistence d hd μ ε

end Mueps.Paper.GeneralExistence

namespace Mueps.Paper.BoundaryCoveringCharacterization

open Mueps
open scoped NNReal
open SemimetricSpace OrderedSemimetric Balls Boundary

/-- In a finite totally ordered semimetric space, covering every proper cut is equivalent to covering its within-side μ-ball from the opposite boundary. -/
theorem theorem3 {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (μ : ℝ≥0) (ε : ℝ>0) :
    (∀ S' : Set S, S'.Nonempty → S'ᶜ.Nonempty →
      ∃ x, (x ∈ S' ∧ ball d hd.1 x μ ⊆ unionOfBalls d hd.1 S'ᶜ ε) ∨
        (x ∈ S'ᶜ ∧ ball d hd.1 x μ ⊆ unionOfBalls d hd.1 S' ε)) ↔ (∀ S' : Set S, S'.Nonempty → S'ᶜ.Nonempty →
      ∃ x, (x ∈ S' ∧ ball d hd.1 x μ ∩ S' ⊆ unionOfBalls d hd.1 (boundary S'ᶜ) ε) ∨
        (x ∈ S'ᶜ ∧ ball d hd.1 x μ ∩ S'ᶜ ⊆ unionOfBalls d hd.1 (boundary S') ε)) := by
  exact MuepsProofs.MainResults.boundaryCoveringCharacterization d hd μ ε

end Mueps.Paper.BoundaryCoveringCharacterization

namespace Mueps.Paper.BoundaryExistence

open Mueps
open scoped NNReal
open SemimetricSpace OrderedSemimetric PartitionRobustness Boundary Balls

/-- In a finite totally ordered semimetric space, only-trivial robustness is equivalent to opposite-boundary covering of every nonempty proper cut. -/
theorem corollary1 {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (μ : ℝ≥0) (ε : ℝ>0) :
    OnlyTrivial d hd.1 μ ε ↔ (∀ S' : Set S, S'.Nonempty → S'ᶜ.Nonempty →
      ∃ x, (x ∈ S' ∧ ball d hd.1 x μ ∩ S' ⊆ unionOfBalls d hd.1 (boundary S'ᶜ) ε) ∨
        (x ∈ S'ᶜ ∧ ball d hd.1 x μ ∩ S'ᶜ ⊆ unionOfBalls d hd.1 (boundary S') ε)) := by
  exact MuepsProofs.MainResults.boundaryExistence d hd μ ε

end Mueps.Paper.BoundaryExistence

namespace Mueps.Paper.SuccessorCovering

open Mueps
open scoped NNReal
open SemimetricSpace OrderedSemimetric Balls Boundary PrecisionGaps

/-- In a finite totally ordered semimetric space, ε≥Δδμ+Δ implies B(x,μ)⊆B(x',ε) whenever x' is the immediate successor of x. -/
theorem theorem4 {S : Type u} [Finite S] [LinearOrder S] [Nontrivial S] (d : Distance S)
    (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (μ : ℝ≥0) (ε : ℝ>0)
    (hbound : threshold d hd μ ≤ ε) (x x' : S) (hsucc : Successor x x') :
    ball d hd.1 x μ ⊆ ball d hd.1 x' ε := by
  exact MuepsProofs.OrderedBounds.successorCovering d hd μ ε hbound x x' hsucc

end Mueps.Paper.SuccessorCovering

namespace Mueps.Paper.PrecisionObstruction

open Mueps
open scoped NNReal
open SemimetricSpace OrderedSemimetric PartitionRobustness PrecisionGaps

/-- In a finite totally ordered semimetric space, ε≥Δδμ+Δ forces every (μ,ε)-robust partition to be trivial. -/
theorem corollary2 {S : Type u} [Finite S] [LinearOrder S] [Nontrivial S] (d : Distance S)
    (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (μ : ℝ≥0) (ε : ℝ>0)
    (hbound : threshold d hd μ ≤ ε) : OnlyTrivial d hd.1 μ ε := by
  exact MuepsProofs.OrderedBounds.precisionObstruction d hd μ ε hbound

end Mueps.Paper.PrecisionObstruction

namespace Mueps.Paper.Noncompositionality

open Mueps
open scoped NNReal
open SemimetricSpace Partitions PartitionRobustness

open Mueps.Noncompositionality

/-- Neither the restriction principle nor the union principle holds in general. -/
theorem lemma1 : ¬ RestrictionPrinciple ∧ ¬ UnionPrinciple := by
  exact MuepsProofs.Counterexamples.noncompositionality

end Mueps.Paper.Noncompositionality

namespace Mueps.Paper.DecompositionObstruction

open Mueps
open scoped NNReal
open SemimetricSpace Decomposition PartitionRobustness

/-- Triviality of robust partitions on each decomposition piece implies global triviality. -/
theorem theorem5 {S : Type u} (d : Distance S) (hd : IsSemimetricSpace d)
    (D : Set (Set S)) (μ : ℝ≥0) (ε : ℝ>0)
    (hD : IsDecomposition d hd D μ)
    (hlocal : ∀ Dᵢ ∈ D,
      let dᵢ : Distance Dᵢ := fun x y => d x.val y.val
      ∀ hDᵢ : IsSemimetricSpace dᵢ, OnlyTrivial dᵢ hDᵢ μ ε) :
    OnlyTrivial d hd μ ε := by
  exact MuepsProofs.Decomposition.decompositionObstruction d hd D μ ε hD hlocal

end Mueps.Paper.DecompositionObstruction

namespace Mueps.Paper.PartialOrderPrecisionBound

open Mueps
open scoped NNReal
open SemimetricSpace OrderedSemimetric Decomposition PartitionRobustness PrecisionGaps

/-- In a finite partially ordered semimetric space, a μ-decomposition into totally ordered pieces admits only trivial robust partitions if ε≥Δᵢδᵢμ+Δᵢ for every piece.

Singleton pieces have Δᵢ = δᵢ = 0 in the paper, so their bound is automatic.
Only nontrivial pieces require `hbound`; singleton pieces remain allowed. -/
theorem corollary3 {S : Type u} [Finite S] [PartialOrder S] [Nontrivial S] (d : Distance S)
    (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (D : Set (Set S)) (μ : ℝ≥0) (ε : ℝ>0)
    (hD : IsDecomposition d hd.1 D μ)
    (hchain : ∀ Dᵢ ∈ D, IsChain (· ≤ ·) Dᵢ)
    (hbound : ∀ (Dᵢ : Set S) (_hmem : Dᵢ ∈ D)
      [Std.Total (α := Dᵢ) (· ≤ ·)] [Nontrivial Dᵢ]
      (hDᵢ : IsOrderedSemimetricSpace (fun x y : Dᵢ => d x.val y.val) (· ≤ ·)),
      threshold (fun x y : Dᵢ => d x.val y.val) hDᵢ μ ≤ ε) : OnlyTrivial d hd.1 μ ε := by
  exact MuepsProofs.Decomposition.partialOrderPrecisionBound d hd D μ ε hD hchain hbound

end Mueps.Paper.PartialOrderPrecisionBound

namespace Mueps.Paper.FloatAbsoluteSpace

open Mueps
open BinaryFloats OrderedSemimetric
open scoped NNReal
open Mueps.FloatAbsoluteSpace

/-- The absolute-distance construction is an ordered semimetric space. -/
theorem proposition1_absolute (F : Format) : IsOrderedSemimetricSpace (absDistance F) (ieeeLe F) := by
  exact MuepsProofs.FloatEmbedding.floatAbsoluteSpace F

end Mueps.Paper.FloatAbsoluteSpace

namespace Mueps.Paper.FloatSquaredSpace

open Mueps
open BinaryFloats OrderedSemimetric
open scoped NNReal
open Mueps.FloatSquaredSpace

/-- The squared-distance construction is an ordered semimetric space. -/
theorem proposition1_squared (F : Format) : IsOrderedSemimetricSpace (squareDistance F) (ieeeLe F) := by
  exact MuepsProofs.FloatEmbedding.floatSquaredSpace F

end Mueps.Paper.FloatSquaredSpace

namespace Mueps.Paper.SumProductSpace

open Mueps
open SemimetricSpace OrderedSemimetric
open scoped BigOperators
open Mueps.SumProductSpace

/-- Sum products preserve ordered semimetric spaces. -/
theorem proposition1_sumProduct {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrderedSemimetricSpace d le) (n : ℕ) : IsOrderedSemimetricSpace (sumDistance d n) (productLe le n) := by
  exact MuepsProofs.sumProductSpace d le hd n

end Mueps.Paper.SumProductSpace

namespace Mueps.Paper.MaximumProductSpace

open Mueps
open SemimetricSpace OrderedSemimetric SumProductSpace
open Mueps.MaximumProductSpace

/-- Synchronized maximum products preserve ordered semimetric spaces. -/
theorem proposition1_maximumProduct {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrderedSemimetricSpace d le) (hadd : Additive d le) (n : ℕ) :
    IsOrderedSemimetricSpace (maxDistance d n) (synchronizedLe d le n) := by
  exact MuepsProofs.maximumProductSpace d le hd hadd n

end Mueps.Paper.MaximumProductSpace

namespace Mueps.Paper.ListSpaces

open Mueps
open scoped NNReal
open SemimetricSpace OrderedSemimetric
open scoped BigOperators
open Mueps.ListSpaces

/-- The sum-distance list extension is an ordered semimetric space. -/
theorem proposition1_sumList {S : Type u} (d : Distance S)
    (le : S → S → Prop) (hd : IsOrderedSemimetricSpace d le) (pad : S) :
    IsOrderedSemimetricSpace (sumDistance d pad) (listLe le pad) := by
  exact MuepsProofs.sumListSpace d le hd pad

/-- The maximum-distance list extension is ordered when the base is additive. -/
theorem proposition1_maximumList {S : Type u} (d : Distance S)
    (le : S → S → Prop) (hd : IsOrderedSemimetricSpace d le)
    (hadd : Additive d le) (pad : S) :
    IsOrderedSemimetricSpace (maxDistance d pad) (synchronizedListLe d le pad) := by
  exact MuepsProofs.maximumListSpace d le hd hadd pad

end Mueps.Paper.ListSpaces
