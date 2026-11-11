/- Adapted from lax-544225, source 62ba21d994907b076c31bc2328e0c3209bd1ea17.
   Standalone Lean port, synchronized 11 November 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.BoundaryCovering

universe u

namespace MuepsProofs.MainResults

open scoped NNReal
open Mueps SemimetricSpace Partitions PartitionRobustness CoveringConditions
  OrderedSemimetric Boundary

/--
Theorem 3: cut covering is equivalent to covering from opposite boundaries.

# Proof strategy

Combine the two supporting implications. Between a covered within-side point
and an opposite-side center, choose a consecutive boundary crossing. The ordered
antitriangle law bounds distance to that boundary. To recover whole-ball
coverage, opposite-side points cover themselves with their own ε-balls.

# Attribution

Theorem 3 of Aleksandrov, Kuske and Völlinger, *(μ,ε)-Robustness: Characterization, Existence, and Precision-Dependent Bounds*, revised FSEN 2027 manuscript (9 November 2026).
-/
theorem boundaryCoveringCharacterization {S : Type u} [Finite S] [LinearOrder S]
    (d : Distance S) (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (μ : ℝ≥0) (ε : ℝ>0) :
    EveryCutCovered d hd.1 μ ε ↔ EveryCutBoundaryCovered d hd.1 μ ε :=
  ⟨OrderedBounds.cutToBoundaryCovering d hd μ ε,
    OrderedBounds.boundaryToCutCovering d hd μ ε⟩

end MuepsProofs.MainResults
