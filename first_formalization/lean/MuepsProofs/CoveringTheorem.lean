/- Adapted from lax-544225, source 62ba21d994907b076c31bc2328e0c3209bd1ea17.
   Standalone Lean port, synchronized 11 November 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.Basic

universe u

namespace MuepsProofs.MainResults

open scoped NNReal
open Mueps SemimetricSpace Partitions PartitionRobustness CoveringConditions
  OrderedSemimetric Boundary

/--
Theorem 1: robustness is equivalent to failure of opposite-part coverage.

# Proof strategy

Combine the two supporting implications. A robust center avoids the
ε-neighborhood of the complement of its part. Conversely, an uncovered μ-ball
supplies a center whose ε-ball stays within the selected part.

# Attribution

Theorem 1 of Aleksandrov, Kuske and Völlinger, *(μ,ε)-Robustness: Characterization, Existence, and Precision-Dependent Bounds*, revised FSEN 2027 manuscript (9 November 2026).
-/
theorem coveringCharacterization {S : Type u} (d : Distance S)
    (hd : IsSemimetricSpace d) (P : Set (Set S)) (hP : IsPartition P)
    (μ : ℝ≥0) (ε : ℝ>0) :
    MuEpsilonRobustPartition d hd P hP μ ε ↔ Uncovered d hd P μ ε :=
  ⟨Basic.robustToUncovered d hd P hP μ ε,
    Basic.uncoveredToRobust d hd P hP μ ε⟩

end MuepsProofs.MainResults
