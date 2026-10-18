/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.ExistenceTheorem
import MuepsProofs.BoundaryTheorem
import MuepsProofs.CoveringConditions
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic

universe u

namespace MuepsProofs.OrderedBounds

open scoped NNReal
open Mueps Semimetric OrderedSemimetric Balls CoveringConditions Boundary PrecisionGaps

/--
Only-trivial robustness gives opposite-boundary covering.

# Proof strategy
Compose the general existence criterion with its finite-order boundary reduction.

# Attribution
Aleksandrov and Völlinger, Corollary 1, forward direction.
-/
lemma trivialityToBoundaryCovering {S : Type u} [Finite S] [LinearOrder S]
    (d : Distance S) (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε) :
    Mueps.PartitionRobustness.OnlyTrivial d hd.1 μ ε → EveryCutBoundaryCovered d hd.1 μ ε := by
  intro h
  exact (MuepsProofs.MainResults.boundaryCoveringCharacterization d hd μ ε hε).mp
    ((MuepsProofs.MainResults.generalExistence d hd.1 μ ε hε).mp h)

/--
Opposite-boundary covering excludes nontrivial robust partitions.

# Proof strategy
Compose the boundary extension with the previously established general cut criterion.

# Attribution
Aleksandrov and Völlinger, Corollary 1, reverse direction.
-/
lemma boundaryCoveringToTriviality {S : Type u} [Finite S] [LinearOrder S]
    (d : Distance S) (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε) :
    EveryCutBoundaryCovered d hd.1 μ ε → Mueps.PartitionRobustness.OnlyTrivial d hd.1 μ ε := by
  intro h
  exact (MuepsProofs.MainResults.generalExistence d hd.1 μ ε hε).mpr
    ((MuepsProofs.MainResults.boundaryCoveringCharacterization d hd μ ε hε).mpr h)

end MuepsProofs.OrderedBounds
