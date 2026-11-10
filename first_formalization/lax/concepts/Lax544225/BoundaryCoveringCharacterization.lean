import Lax544225.Boundary
import Lax544225.OrderedSemimetric

/-!
---
title: Theorem 3 — Boundary covering characterization
type: theorem
---
In a finite ordered space, the covering criterion can be expressed using the boundaries of the two sides of each cut.

**Statement from the paper.**

Let $(S,<,d)$ be a finite totally ordered semimetric space and
$\mu\geq0$, $\epsilon>0$. The following statements are equivalent:

1. For every nonempty proper subset $S'\subset S$, there exists $x\in S$
   such that either

   $$x\in S'\quad\text{and}\quad B(x,\mu)\subseteq\bigcup_{x'\in S\setminus S'}B(x',\epsilon),$$

   or

   $$x\in S\setminus S'\quad\text{and}\quad B(x,\mu)\subseteq\bigcup_{x'\in S'}B(x',\epsilon).$$

2. For every nonempty proper subset $S'\subset S$, there exists $x\in S$
   such that either

   $$x\in S'\quad\text{and}\quad B(x,\mu)\cap S'\subseteq\bigcup_{x'\in\overline{\partial}S'}B(x',\epsilon),$$

   or

   $$x\in S\setminus S'\quad\text{and}\quad B(x,\mu)\cap(S\setminus S')\subseteq\bigcup_{x'\in\partial S'}B(x',\epsilon).$$

# Formalization notes

Both directions are stated together as in the paper. Their separate arguments
remain supporting lemmas in the proof package.
-/

universe u

namespace Lax544225.BoundaryCoveringCharacterization

open scoped NNReal
open Semimetric OrderedSemimetric Balls Boundary

/-- In a finite totally ordered semimetric space, covering every proper cut is equivalent to covering its within-side μ-ball from the opposite boundary. -/
axiom statement {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε) :
    (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd.1 x μ ⊆ neighborhood d hd.1 Aᶜ ε) ∨
        (x ∈ Aᶜ ∧ ball d hd.1 x μ ⊆ neighborhood d hd.1 A ε)) ↔ (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd.1 x μ ∩ A ⊆ neighborhood d hd.1 (complementBoundary A) ε) ∨
        (x ∈ Aᶜ ∧ ball d hd.1 x μ ∩ Aᶜ ⊆ neighborhood d hd.1 (boundary A) ε))

end Lax544225.BoundaryCoveringCharacterization
