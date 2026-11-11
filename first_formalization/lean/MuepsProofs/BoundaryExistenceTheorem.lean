/- Adapted from lax-544225, source 62ba21d994907b076c31bc2328e0c3209bd1ea17.
   Standalone Lean port, synchronized 11 November 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.BoundaryExistence

universe u

namespace MuepsProofs.MainResults

open scoped NNReal
open Mueps SemimetricSpace Partitions PartitionRobustness CoveringConditions
  OrderedSemimetric Boundary

/--
Corollary 1: only-trivial robustness is equivalent to opposite-boundary covering.

# Proof strategy

Combine the two supporting compositions of Theorem 2 with Theorem 3. The
general existence criterion converts triviality to cut covering, and the
boundary characterization converts cut covering to boundary covering.

# Attribution

Corollary 1 of Aleksandrov, Kuske and Völlinger, *(μ,ε)-Robustness: Characterization, Existence, and Precision-Dependent Bounds*, revised FSEN 2027 manuscript (9 November 2026).
-/
lemma boundaryExistence {S : Type u} [Finite S] [LinearOrder S]
    (d : Distance S) (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (μ : ℝ≥0) (ε : ℝ>0) :
    OnlyTrivial d hd.1 μ ε ↔ EveryCutBoundaryCovered d hd.1 μ ε :=
  ⟨OrderedBounds.trivialityToBoundaryCovering d hd μ ε,
    OrderedBounds.boundaryCoveringToTriviality d hd μ ε⟩

end MuepsProofs.MainResults
