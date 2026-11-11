import Lax544225.Decomposition
import Lax544225.PartitionRobustness
import Lax544225.PrecisionGaps
import Lax544225.OrderedSemimetric
import Mathlib.Order.Preorder.Chain

/-!
---
title: Corollary 3 — Precision bound on ordered pieces
type: corollary
---
In a finite partially ordered semimetric space, a μ-decomposition into totally ordered pieces admits only trivial robust partitions if ε≥Δᵢδᵢμ+Δᵢ for every piece.

# Formalization notes

`hD` assumes a decomposition, `hchain` says each piece is totally ordered, and `hbound` gives the precision bound on each piece with at least two elements.

The revised paper assigns Δᵢ = δᵢ = 0 to singleton pieces. Their threshold is therefore zero, and its bound is automatic because ε > 0. Accordingly, `hbound` is required only for nontrivial pieces; singleton pieces are allowed and handled separately in the proof. The general precision-gap definitions retain their domain of finite total orders with at least two elements. For the finite family, these piecewise bounds are equivalent to the paper’s maximum bound. Each piece uses its inherited order and interval cardinalities. The ambient space has at least two elements, as stated in the corollary.
-/

universe u

namespace Lax544225.PartialOrderPrecisionBound

open scoped NNReal

open SemimetricSpace OrderedSemimetric Decomposition PartitionRobustness PrecisionGaps

/-- In a finite partially ordered semimetric space, a μ-decomposition into totally ordered pieces admits only trivial robust partitions if ε≥Δᵢδᵢμ+Δᵢ for every piece. -/
axiom corollary3 {S : Type u} [Finite S] [PartialOrder S] [Nontrivial S] (d : Distance S)
    (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (D : Set (Set S)) (μ : ℝ≥0) (ε : ℝ>0)
    (hD : IsDecomposition d hd.1 D μ)
    (hchain : ∀ Dᵢ ∈ D, IsChain (· ≤ ·) Dᵢ)
    (hbound : ∀ (Dᵢ : Set S) (_hmem : Dᵢ ∈ D)
      [Std.Total (α := Dᵢ) (· ≤ ·)] [Nontrivial Dᵢ]
      (hDᵢ : IsOrderedSemimetricSpace (fun x y : Dᵢ => d x.val y.val) (· ≤ ·)),
      threshold (fun x y : Dᵢ => d x.val y.val) hDᵢ μ ≤ ε) : OnlyTrivial d hd.1 μ ε

end Lax544225.PartialOrderPrecisionBound
