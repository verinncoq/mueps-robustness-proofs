/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.Basic
universe u

namespace MuepsProofs.MainResults

open scoped NNReal
open Mueps Semimetric Partitions PartitionRobustness CoveringConditions OrderedSemimetric Boundary

/--
Theorem 1: robustness is equivalent to failure of opposite-part coverage.

# Proof strategy

Combine the two supporting implications. A robust center avoids the
ε-neighborhood of the complement of its part. Conversely, an uncovered μ-ball
supplies a center whose ε-ball stays within the selected part.

# Attribution

Theorem 1 of Aleksandrov and Völlinger, *Relaxing Global Classifier Robustness
on Semimetric Spaces*, supplied FSEN 2027 manuscript, p. 6.
-/
theorem coveringCharacterization {S : Type u} (d : Distance S)
    (hd : IsSemimetric d) (P : Set (Set S)) (hP : IsPartition P)
    (μ ε : ℝ≥0) (hε : 0 < ε) :
    Robust d hd P hP μ ε ↔ Uncovered d hd P μ ε :=
  ⟨Basic.robustToUncovered d hd P hP μ ε hε,
    Basic.uncoveredToRobust d hd P hP μ ε hε⟩


end MuepsProofs.MainResults
