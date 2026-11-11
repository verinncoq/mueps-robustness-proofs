/- Adapted from lax-544225, source 62ba21d994907b076c31bc2328e0c3209bd1ea17.
   Standalone Lean port, synchronized 11 November 2026: archive assumptions replaced by proved dependencies.
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
open Mueps SemimetricSpace OrderedSemimetric Balls CoveringConditions Boundary PrecisionGaps

/--
Only-trivial robustness gives opposite-boundary covering.

# Proof strategy
Compose the general existence criterion with its finite-order boundary reduction.

# Attribution
Aleksandrov, Kuske and Völlinger, Corollary 1, forward direction.
-/
lemma trivialityToBoundaryCovering {S : Type u} [Finite S] [LinearOrder S]
    (d : Distance S) (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (μ : ℝ≥0) (ε : ℝ>0) :
    Mueps.PartitionRobustness.OnlyTrivial d hd.1 μ ε → EveryCutBoundaryCovered d hd.1 μ ε := by
  intro h
  exact (MuepsProofs.MainResults.boundaryCoveringCharacterization d hd μ ε).mp
    ((MuepsProofs.MainResults.generalExistence d hd.1 μ ε).mp h)

/--
Opposite-boundary covering excludes nontrivial robust partitions.

# Proof strategy
Compose the boundary extension with the previously established general cut criterion.

# Attribution
Aleksandrov, Kuske and Völlinger, Corollary 1, reverse direction.
-/
lemma boundaryCoveringToTriviality {S : Type u} [Finite S] [LinearOrder S]
    (d : Distance S) (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (μ : ℝ≥0) (ε : ℝ>0) :
    EveryCutBoundaryCovered d hd.1 μ ε → Mueps.PartitionRobustness.OnlyTrivial d hd.1 μ ε := by
  intro h
  exact (MuepsProofs.MainResults.generalExistence d hd.1 μ ε).mpr
    ((MuepsProofs.MainResults.boundaryCoveringCharacterization d hd μ ε).mpr h)

end MuepsProofs.OrderedBounds
