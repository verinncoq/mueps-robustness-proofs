import Lax544225.Decomposition
import Lax544225.PartitionRobustness

/-!
---
title: Theorem 5 — Decomposition transfers triviality
type: theorem
---
If every piece of a closed, overlapping decomposition admits only a trivial robust partition, then so does the whole space.

**Statement from the paper.**

Let $(S,d)$ be a semimetric space with $\mu\geq0$, $\epsilon>0$, and let
$D$ be a $\mu$-decomposition of $S$. If each $D_i\in D$ has the
trivial partition as its only $(\mu,\epsilon)$-robust partition, then the only
$(\mu,\epsilon)$-robust partition on $S$ is trivial.
-/

universe u

namespace Lax544225.DecompositionObstruction

open scoped NNReal

open SemimetricSpace Decomposition PartitionRobustness

/-- Triviality of robust partitions on each decomposition piece implies global triviality. -/
axiom theorem5 {S : Type u} (d : Distance S) (hd : IsSemimetricSpace d)
    (D : Set (Set S)) (μ : ℝ≥0) (ε : ℝ>0)
    (hD : IsDecomposition d hd D μ)
    (hlocal : ∀ Dᵢ ∈ D,
      let dᵢ : Distance Dᵢ := fun x y => d x.val y.val
      ∀ hDᵢ : IsSemimetricSpace dᵢ, OnlyTrivial dᵢ hDᵢ μ ε) :
    OnlyTrivial d hd μ ε

end Lax544225.DecompositionObstruction
