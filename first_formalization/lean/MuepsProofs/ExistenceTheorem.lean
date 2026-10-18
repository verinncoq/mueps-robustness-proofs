/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.Existence
universe u

namespace MuepsProofs.MainResults

open scoped NNReal
open Mueps Semimetric Partitions PartitionRobustness CoveringConditions OrderedSemimetric Boundary

/--
Theorem 2: only-trivial robustness is equivalent to coverage of every proper cut.

# Proof strategy

Combine the two cut arguments, using Theorem 1. An uncovered proper cut and its
complement give a nontrivial robust partition. In the converse direction, a
proper part of a robust partition contradicts coverage of that cut.

# Attribution

Theorem 2 of Aleksandrov and Völlinger, *Relaxing Global Classifier Robustness
on Semimetric Spaces*, supplied FSEN 2027 manuscript, p. 9.
-/
theorem generalExistence {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (μ ε : ℝ≥0) (hε : 0 < ε) :
    OnlyTrivial d hd μ ε ↔ EveryCutCovered d hd μ ε :=
  ⟨Existence.trivialityToCutCovering d hd μ ε hε,
    Existence.cutCoveringToTriviality d hd μ ε hε⟩


end MuepsProofs.MainResults
