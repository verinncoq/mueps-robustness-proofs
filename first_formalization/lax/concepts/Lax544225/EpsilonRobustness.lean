import Lax544225.Classifier
import Lax544225.SemimetricSpace

/-!
---
title: ε-Robustness
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

Each predicate requires evidence that the distance defines a semimetric space. The parameter types encode μ ≥ 0 and ε > 0 directly: `μ : ℝ≥0` and `ε : ℝ>0`. The latter is the subtype of strictly positive real numbers; no separate positivity hypothesis is needed. No robustness predicate can be applied at ε=0. The same-label requirement is present even when μ>ε. In Lean, `x_star` denotes the paper’s reference point $x^*$ and `x` the quantified input. Both robustness definitions use the paper’s distance inequalities directly; their ball characterizations are proved in the proof package.
-/

universe u

namespace Lax544225.EpsilonRobustness

open scoped NNReal

open Classifier SemimetricSpace
/-- Local robustness at the paper’s reference point x*. -/
def LocallyEpsilonRobust {S : Type u} {n : ℕ} (d : Distance S) (_hd : IsSemimetricSpace d)
    (c : Classifier S n) (ε : ℝ>0) (x_star : S) : Prop :=
  ∀ x, d x x_star ≤ ε → c.label x = c.label x_star

/-- Local robustness at every input. -/
def GloballyEpsilonRobust {S : Type u} {n : ℕ} (d : Distance S) (hd : IsSemimetricSpace d)
    (c : Classifier S n) (ε : ℝ>0) : Prop :=
  ∀ x, LocallyEpsilonRobust d hd c ε x

/-- (μ,ε)-robustness: each input is μ-close to a same-label locally ε-robust input. -/
def MuEpsilonRobustClassifier {S : Type u} {n : ℕ} (d : Distance S) (hd : IsSemimetricSpace d)
    (c : Classifier S n) (μ : ℝ≥0) (ε : ℝ>0) : Prop :=
  ∀ x, ∃ x', d x x' ≤ μ ∧ c.label x = c.label x' ∧ LocallyEpsilonRobust d hd c ε x'

end Lax544225.EpsilonRobustness
