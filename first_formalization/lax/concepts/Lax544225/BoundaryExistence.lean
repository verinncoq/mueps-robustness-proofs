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
open Semimetric OrderedSemimetric PartitionRobustness Boundary Balls

/-- In a finite totally ordered semimetric space, only-trivial robustness is equivalent to opposite-boundary covering of every nonempty proper cut. -/
axiom statement {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε) :
    OnlyTrivial d hd.1 μ ε ↔ (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd.1 x μ ∩ A ⊆ neighborhood d hd.1 (complementBoundary A) ε) ∨
        (x ∈ Aᶜ ∧ ball d hd.1 x μ ∩ Aᶜ ⊆ neighborhood d hd.1 (boundary A) ε))

end Lax544225.BoundaryExistence
