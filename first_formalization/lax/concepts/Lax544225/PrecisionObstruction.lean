import Lax544225.PartitionRobustness
import Lax544225.PrecisionGaps
import Lax544225.OrderedSemimetric

/-!
---
title: Corollary 2 — Precision obstruction
type: corollary
---
In a finite totally ordered semimetric space, ε≥Δδμ+Δ forces every (μ,ε)-robust partition to be trivial.

-/

universe u

namespace Lax544225.PrecisionObstruction

open scoped NNReal

open Semimetric OrderedSemimetric PartitionRobustness PrecisionGaps

/-- In a finite totally ordered semimetric space, ε≥Δδμ+Δ forces every (μ,ε)-robust partition to be trivial. -/
axiom statement {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε)
    (hbound : threshold d hd μ ≤ ε) : OnlyTrivial d hd.1 μ ε

end Lax544225.PrecisionObstruction
