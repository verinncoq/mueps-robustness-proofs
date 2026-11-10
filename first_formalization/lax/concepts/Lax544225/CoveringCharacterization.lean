import Lax544225.PartitionRobustness

/-!
---
title: Theorem 1 — Covering characterization of robustness
type: theorem
---
A partition is robust exactly when every input has a nearby point that stays beyond the robustness radius of all points outside its part.

**Statement from the paper.**

Let $(S,d)$ be a semimetric space, $P:=\{S_1,\dots,S_n\}$ a partition of $S$,
and $\mu\geq0$, $\epsilon>0$. The following are equivalent:

1. $P$ is $(\mu,\epsilon)$-robust.
2. For all $S_i\in P$ and all $x\in S_i$,

   $$B(x,\mu)\not\subseteq\bigcup_{x^*\in S\setminus S_i}B(x^*,\epsilon).$$

# Formalization notes

Both directions are stated together as in the paper. Their separate arguments
remain supporting lemmas in the proof package.
-/

universe u

namespace Lax544225.CoveringCharacterization

open scoped NNReal
open Semimetric Partitions PartitionRobustness Balls

/-- A finite partition is (μ,ε)-robust exactly when no μ-ball centered in a part is covered by ε-balls from its complement. -/
axiom statement {S : Type u} (d : Distance S) (hd : IsSemimetric d) (P : Set (Set S))
    (hP : IsPartition P) (μ ε : ℝ≥0) (hε : 0 < ε) :
    Robust d hd P hP μ ε ↔ (∀ A ∈ P, ∀ x ∈ A, ¬ ball d hd x μ ⊆ neighborhood d hd Aᶜ ε)

end Lax544225.CoveringCharacterization
