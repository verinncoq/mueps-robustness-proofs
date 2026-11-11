import Lax544225.PartitionSeparability
import Lax544225Proofs.Basic

universe u

namespace Lax544225Proofs.PartitionSeparability

open scoped NNReal
open Lax544225 SemimetricSpace Partitions PartitionRobustness

/--
---
conclusion: Lax544225.PartitionSeparability.separated_iff_robust_zero
---
Separation of the parts is equivalent to robustness with zero relaxation.

# Proof strategy

Reuse the two direct implications. Under separation, each input is its own
robust center because its closed ε-ball stays in its unique part. Conversely,
zero distance forces the robust center to equal the input. A point in another
part cannot lie in that ball, so its distance is strictly greater than ε.
Neither direction uses Theorem 1.

# Attribution

The separability observation after Theorem 1 in Aleksandrov, Kuske and
Völlinger, *(μ,ε)-Robustness: Characterization, Existence, and Precision-Dependent Bounds*.
-/
theorem separated_iff_robust_zero {S : Type u} (d : Distance S)
    (hd : IsSemimetricSpace d) (P : Set (Set S)) (hP : IsPartition P) (ε : ℝ>0) :
    Separated d hd P hP (ε : ℝ≥0) ↔ MuEpsilonRobustPartition d hd P hP 0 ε :=
  ⟨Basic.separatedToZeroRobust d hd P hP ε,
    Basic.zeroRobustToSeparated d hd P hP ε⟩

end Lax544225Proofs.PartitionSeparability
