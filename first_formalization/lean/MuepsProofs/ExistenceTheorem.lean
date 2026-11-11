/- Adapted from lax-544225, source 62ba21d994907b076c31bc2328e0c3209bd1ea17.
   Standalone Lean port, synchronized 11 November 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.Existence

universe u

namespace MuepsProofs.MainResults

open scoped NNReal
open Mueps SemimetricSpace Partitions PartitionRobustness CoveringConditions
  OrderedSemimetric Boundary

/--
Theorem 2: only-trivial robustness is equivalent to coverage of every proper cut.

# Proof strategy

Combine the two cut arguments, using Theorem 1. An uncovered proper cut and its
complement give a nontrivial robust partition. In the converse direction, a
proper part of a robust partition contradicts coverage of that cut.

# Attribution

Theorem 2 of Aleksandrov, Kuske and Völlinger, *(μ,ε)-Robustness: Characterization, Existence, and Precision-Dependent Bounds*, revised FSEN 2027 manuscript (9 November 2026).
-/
theorem generalExistence {S : Type u} (d : Distance S) (hd : IsSemimetricSpace d)
    (μ : ℝ≥0) (ε : ℝ>0) :
    OnlyTrivial d hd μ ε ↔ EveryCutCovered d hd μ ε :=
  ⟨Existence.trivialityToCutCovering d hd μ ε,
    Existence.cutCoveringToTriviality d hd μ ε⟩

end MuepsProofs.MainResults
