import Lax544225.Boundary
import Lax544225.PartitionRobustness
import Lax544225.OrderedSemimetric

/-!
---
title: Corollary 1 — Boundary criterion for triviality
type: corollary
---
In a finite totally ordered semimetric space, only-trivial robustness is equivalent to opposite-boundary covering of every nonempty proper cut.

# Formalization notes

Both directions are stated together as in the paper. Their separate arguments
remain supporting lemmas in the proof package.
-/

universe u

namespace Lax544225.BoundaryExistence

open scoped NNReal
open SemimetricSpace OrderedSemimetric PartitionRobustness Boundary Balls

/-- In a finite totally ordered semimetric space, only-trivial robustness is equivalent to opposite-boundary covering of every nonempty proper cut. -/
axiom corollary1 {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (μ : ℝ≥0) (ε : ℝ>0) :
    OnlyTrivial d hd.1 μ ε ↔ (∀ S' : Set S, S'.Nonempty → S'ᶜ.Nonempty →
      ∃ x, (x ∈ S' ∧ ball d hd.1 x μ ∩ S' ⊆ unionOfBalls d hd.1 (boundary S'ᶜ) ε) ∨
        (x ∈ S'ᶜ ∧ ball d hd.1 x μ ∩ S'ᶜ ⊆ unionOfBalls d hd.1 (boundary S') ε))

end Lax544225.BoundaryExistence
