import Lax544225.Boundary
import Lax544225.PrecisionGaps
import Lax544225.OrderedSemimetric

/-!
---
title: Theorem 4 — Successor covering at the precision bound
type: theorem
---
Above the precision-dependent bound, the robustness ball of an immediate successor covers the smaller ball around the preceding point.

**Statement from the paper.**

Let $(S,<,d)$ be a finite totally ordered semimetric space and
$\mu\geq0$, $\epsilon>0$. If

$$\epsilon\geq\Delta\cdot\delta\cdot\mu+\Delta,$$

then for all $x,x'\in S$ with $Succ(x,x')$,

$$B(x,\mu)\subseteq B(x',\epsilon).$$
-/

universe u

namespace Lax544225.SuccessorCovering

open scoped NNReal

open Semimetric OrderedSemimetric Balls Boundary PrecisionGaps

/-- In a finite totally ordered semimetric space, ε≥Δδμ+Δ implies B(x,μ)⊆B(y,ε) whenever y is the immediate successor of x. -/
axiom statement {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε)
    (hbound : threshold d hd μ ≤ ε) (x y : S) (hxy : Successor x y) :
    ball d hd.1 x μ ⊆ ball d hd.1 y ε

end Lax544225.SuccessorCovering
