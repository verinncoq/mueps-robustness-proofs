/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.OrderedSemimetric
import Mathlib.Data.Set.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Interval.Set.Basic

/-!
The precision gap measures compare distance with the number of ordered steps between two points. One measures the largest average distance per step; the other measures the largest number of steps per unit distance.

**Definition from the paper.**

Let $(S,<,d)$ be a finite totally ordered semimetric space with $|S|\geq2$.
For $a\leq b$, write $[a,b]:=\{x\in S\mid a\leq x\leq b\}$.
Define $\Delta$ and $\delta$ by

$$\Delta:=\max\left\{\frac{d(x,y)}{|[x,y]|-1}\;\middle|\;x,y\in S,\ x<y\right\},$$

$$\delta:=\max\left\{\frac{|[x,y]|-1}{d(x,y)}\;\middle|\;x,y\in S,\ x<y\right\},$$

where $|\cdot|$ denotes set cardinality.

# Formalization notes

The formulas take an ordered semimetric on a finite partially ordered carrier. The paper applies them to totally ordered carriers or pieces. The interval uses the ambient order of that carrier or piece. Natural cardinalities are cast into ℝ≥0 before division. Suprema of the finite ratio sets are their maxima. On a singleton the ratio sets are empty and Δ=δ=0, extending the paper’s undefined singleton case so decomposition pieces of size one need no arbitrary parameters. Δ equals the largest adjacent gap only for an additive distance; no such equality is presumed for general semimetrics.
-/

universe u

namespace Mueps.PrecisionGaps

open scoped NNReal

open Semimetric OrderedSemimetric
/-- The number of consecutive steps between the endpoints of a closed interval. -/
noncomputable def steps {S : Type u} [PartialOrder S] (x y : S) : ℕ :=
  (Set.Icc x y).ncard - 1

/-- The largest average distance per ordered step. -/
noncomputable def deltaUpper {S : Type u} [Finite S] [PartialOrder S] (d : Distance S)
    (_hd : IsOrdered d (· ≤ ·)) : ℝ≥0 :=
  sSup {r | ∃ x y, x < y ∧ r = d x y / (steps x y : ℝ≥0)}

/-- The largest number of ordered steps per unit distance. -/
noncomputable def deltaInverse {S : Type u} [Finite S] [PartialOrder S] (d : Distance S)
    (_hd : IsOrdered d (· ≤ ·)) : ℝ≥0 :=
  sSup {r | ∃ x y, x < y ∧ r = (steps x y : ℝ≥0) / d x y}

/-- The paper’s precision-dependent obstruction threshold Δδμ+Δ. -/
noncomputable def threshold {S : Type u} [Finite S] [PartialOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ : ℝ≥0) : ℝ≥0 := deltaUpper d hd * deltaInverse d hd * μ + deltaUpper d hd

end Mueps.PrecisionGaps
