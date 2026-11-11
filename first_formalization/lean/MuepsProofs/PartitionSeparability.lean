/- Adapted from lax-544225, source dbdbc610628949634c5cedeaa81437b2f7ce1293.
   Standalone Lean port, synchronized 11 November 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import MuepsProofs.Basic

universe u

namespace MuepsProofs.PartitionSeparability

open scoped NNReal
open Mueps SemimetricSpace Partitions PartitionRobustness

/--
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

end MuepsProofs.PartitionSeparability
