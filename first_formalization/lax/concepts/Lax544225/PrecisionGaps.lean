import Lax544225.OrderedSemimetric
import Mathlib.Data.Set.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Interval.Set.Basic

/-!
---
title: Precision Gap Metrics
type: definition
---
The precision gap measures compare distance with the number of ordered steps between two points. One measures the largest average distance per step; the other measures the largest number of steps per unit distance.

**Definition from the paper.**

Let $(S,<,d)$ be a finite totally ordered semimetric space with $|S|\geq2$.
For $a\leq b$, write $[a,b]:=\{x\in S\mid a\leq x\leq b\}$.
Define $\Delta$ and $\delta$ by

$$\Delta:=\max\left\{\frac{d(x,y)}{|[x,y]|-1}\;\middle|\;x,y\in S,\ x<y\right\},$$

$$\delta:=\max\left\{\frac{|[x,y]|-1}{d(x,y)}\;\middle|\;x,y\in S,\ x<y\right\},$$

where $|\cdot|$ denotes set cardinality.

# Formalization notes

The formulas require a finite totally ordered carrier with at least two elements, as in the paper. `PartialOrder` together with `Std.Total` expresses a total order; `Nontrivial` expresses the existence of two distinct elements. The interval uses the inherited order of the carrier or piece. Natural cardinalities are cast into ℝ≥0 before division. The ratio sets are finite and nonempty, so their suprema are maxima. Δ equals the largest adjacent gap only for an additive distance; no such equality is presumed for general semimetrics.
-/

universe u

namespace Lax544225.PrecisionGaps

open scoped NNReal

open SemimetricSpace OrderedSemimetric
/-- The number of consecutive steps between the endpoints of a closed interval. -/
noncomputable def steps {S : Type u} [Finite S] [PartialOrder S]
    [Std.Total (α := S) (· ≤ ·)] (x y : S) : ℕ :=
  (Set.Icc x y).ncard - 1

/-- The largest average distance per ordered step. -/
noncomputable def deltaUpper {S : Type u} [Finite S] [PartialOrder S]
    [Std.Total (α := S) (· ≤ ·)] [Nontrivial S] (d : Distance S)
    (_hd : IsOrderedSemimetricSpace d (· ≤ ·)) : ℝ≥0 :=
  sSup {r | ∃ x y, x < y ∧ r = d x y / (steps x y : ℝ≥0)}

/-- The largest number of ordered steps per unit distance. -/
noncomputable def deltaInverse {S : Type u} [Finite S] [PartialOrder S]
    [Std.Total (α := S) (· ≤ ·)] [Nontrivial S] (d : Distance S)
    (_hd : IsOrderedSemimetricSpace d (· ≤ ·)) : ℝ≥0 :=
  sSup {r | ∃ x y, x < y ∧ r = (steps x y : ℝ≥0) / d x y}

/-- The paper’s precision-dependent obstruction threshold Δδμ+Δ. -/
noncomputable def threshold {S : Type u} [Finite S] [PartialOrder S]
    [Std.Total (α := S) (· ≤ ·)] [Nontrivial S] (d : Distance S)
    (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (μ : ℝ≥0) : ℝ≥0 := deltaUpper d hd * deltaInverse d hd * μ + deltaUpper d hd

end Lax544225.PrecisionGaps
