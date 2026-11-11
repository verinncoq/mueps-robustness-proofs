import Lax544225.PartitionRobustness

/-!
---
title: Separability and Zero-Relaxation Robustness
type: lemma
---
A partition is ε-separated exactly when it is (0,ε)-robust.

Let $(S,d)$ be a semimetric space, $P$ a finite partition of $S$, and
$\epsilon>0$. Then

$$\operatorname{Separated}(P,\epsilon)\iff
\operatorname{MuEpsilonRobustPartition}(P,0,\epsilon).$$

Separation means that points in different parts have distance strictly greater
than ε. This corresponds to robustness on closed ε-balls. The equivalence follows
directly from the definitions and the partition assumptions.
-/

universe u

namespace Lax544225.PartitionSeparability

open scoped NNReal
open SemimetricSpace Partitions PartitionRobustness

/-- A partition is ε-separated if and only if it is (0,ε)-robust. -/
axiom separated_iff_robust_zero {S : Type u} (d : Distance S)
    (hd : IsSemimetricSpace d) (P : Set (Set S)) (hP : IsPartition P) (ε : ℝ>0) :
    Separated d hd P hP (ε : ℝ≥0) ↔ MuEpsilonRobustPartition d hd P hP 0 ε

end Lax544225.PartitionSeparability
