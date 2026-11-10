import Lax544225.PartitionRobustness

/-!
---
title: Theorem 2 — General existence criterion
type: theorem
---
The possibility of a nontrivial robust partition is determined by how balls on opposite sides of a cut cover one another.

**Statement from the paper.**

Let $(S,d)$ be a semimetric space and $\mu\geq0$, $\epsilon>0$.
The following statements are equivalent:

1. The only $(\mu,\epsilon)$-robust partition on $S$ is trivial.
2. For every nonempty proper subset $S'\subset S$, there exists $x\in S$
   such that either

   $$x\in S'\quad\text{and}\quad B(x,\mu)\subseteq\bigcup_{x'\in S\setminus S'}B(x',\epsilon),$$

   or

   $$x\in S\setminus S'\quad\text{and}\quad B(x,\mu)\subseteq\bigcup_{x'\in S'}B(x',\epsilon).$$

# Formalization notes

Both directions are stated together as in the paper. Their separate arguments
remain supporting lemmas in the proof package.
-/

universe u

namespace Lax544225.GeneralExistence

open scoped NNReal
open Semimetric PartitionRobustness Balls

/-- The trivial partition is the only robust partition exactly when every nonempty proper cut admits a covering point on one side from ε-balls centered on the other side. -/
axiom statement {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (μ ε : ℝ≥0) (hε : 0 < ε) :
    OnlyTrivial d hd μ ε ↔ (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd x μ ⊆ neighborhood d hd Aᶜ ε) ∨
        (x ∈ Aᶜ ∧ ball d hd x μ ⊆ neighborhood d hd A ε))

end Lax544225.GeneralExistence
