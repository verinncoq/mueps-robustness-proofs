import Lax544225.Classifier
import Lax544225.Balls

/-!
---
title: ε-Robustness and (μ,ε)-Robustness
type: definition
---
Local robustness means that all inputs sufficiently close to a given input have the same label. Global robustness requires this at every input. Relaxed robustness allows each input to move a short distance to a locally robust input with the same label.

**Definition from the paper.**

Let $(S,d)$ be a semimetric space. A classifier $c:S\rightarrow[n]$ is
**locally robust** at a point $x^*\in S$ for $\epsilon>0$ if

$$\forall x\in S\;[d(x,x^*)\leq\epsilon\rightarrow c(x)=c(x^*)].$$

The classifier is **globally $\epsilon$-robust** if it is locally
$\epsilon$-robust at every point.

The classifier is **$(\mu,\epsilon)$-robust**, for
$\mu\in\mathbb{R}_{\geq0}$ and $\epsilon\in\mathbb{R}_{>0}$, if for every
$x\in S$ there exists $x'\in S$ with $d(x,x')\leq\mu$ such that
$c(x)=c(x')$ and $c$ is locally $\epsilon$-robust at $x'$.

# Formalization notes

Each predicate requires evidence that the distance defines a semimetric space. Radii are nonnegative reals. The predicates also make sense at ε=0; the paper’s results below explicitly require ε>0. The same-label requirement is present even when μ>ε.
-/

universe u

namespace Lax544225.ClassifierRobustness

open scoped NNReal

open Classifier Semimetric Balls
/-- Local robustness of the classifier at x. -/
def LocallyRobust {S : Type u} {n : ℕ} (d : Distance S) (hd : IsSemimetric d)
    (c : Classifier S n) (ε : ℝ≥0) (x : S) : Prop :=
  ∀ y ∈ ball d hd x ε, c.label y = c.label x

/-- Local robustness at every input. -/
def GloballyRobust {S : Type u} {n : ℕ} (d : Distance S) (hd : IsSemimetric d)
    (c : Classifier S n) (ε : ℝ≥0) : Prop :=
  ∀ x, LocallyRobust d hd c ε x

/-- Coverage of each input by a same-label locally robust input. -/
def RelaxedRobust {S : Type u} {n : ℕ} (d : Distance S) (hd : IsSemimetric d)
    (c : Classifier S n) (μ ε : ℝ≥0) : Prop :=
  ∀ x, ∃ x', x' ∈ ball d hd x μ ∧ c.label x = c.label x' ∧ LocallyRobust d hd c ε x'

end Lax544225.ClassifierRobustness
