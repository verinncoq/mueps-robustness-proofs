/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.BoundaryCovering
universe u

namespace MuepsProofs.MainResults

open scoped NNReal
open Mueps Semimetric Partitions PartitionRobustness CoveringConditions OrderedSemimetric Boundary

/--
Theorem 3: cut covering is equivalent to covering from opposite boundaries.

# Proof strategy

Combine the two supporting implications. Between a covered within-side point
and an opposite-side center, choose a consecutive boundary crossing. The ordered
antitriangle law bounds distance to that boundary. To recover whole-ball
coverage, opposite-side points cover themselves with their own ε-balls.

# Attribution

Theorem 3 of Aleksandrov and Völlinger, *Relaxing Global Classifier Robustness
on Semimetric Spaces*, supplied FSEN 2027 manuscript, p. 10.
-/
theorem boundaryCoveringCharacterization {S : Type u} [Finite S] [LinearOrder S]
    (d : Distance S) (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε) :
    EveryCutCovered d hd.1 μ ε ↔ EveryCutBoundaryCovered d hd.1 μ ε :=
  ⟨OrderedBounds.cutToBoundaryCovering d hd μ ε hε,
    OrderedBounds.boundaryToCutCovering d hd μ ε hε⟩


end MuepsProofs.MainResults
