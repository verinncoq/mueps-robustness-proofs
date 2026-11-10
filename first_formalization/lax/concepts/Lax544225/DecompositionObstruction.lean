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
$D$ be a $(\mu,\epsilon)$-decomposition of $S$. If each $D_i\in D$ has the
trivial partition as its only $(\mu,\epsilon)$-robust partition, then the only
$(\mu,\epsilon)$-robust partition on $S$ is trivial.
-/

universe u

namespace Lax544225.DecompositionObstruction

open scoped NNReal

open Semimetric Decomposition PartitionRobustness

/-- If a semimetric space has a (μ,ε)-decomposition and each induced subspace admits only trivial (μ,ε)-robust partitions, then the whole space admits only trivial (μ,ε)-robust partitions. -/
axiom statement {S : Type u} (d : Distance S) (hd : IsSemimetric d) (D : Set (Set S))
    (μ ε : ℝ≥0) (hε : 0 < ε) (hD : IsDecomposition d hd D μ)
    (hlocal : ∀ A ∈ D, ∀ hA : IsSemimetric (fun x y : A => d x.val y.val),
      OnlyTrivial (fun x y : A => d x.val y.val) hA μ ε) : OnlyTrivial d hd μ ε

end Lax544225.DecompositionObstruction
