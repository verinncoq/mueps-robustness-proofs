/- Adapted from lax-544225, source 62ba21d994907b076c31bc2328e0c3209bd1ea17.
   Standalone Lean port, synchronized 11 November 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.PrecisionBounds
import MuepsProofs.BoundaryExistenceTheorem
import MuepsProofs.CoveringConditions
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic

universe u

namespace MuepsProofs.OrderedBounds

open scoped NNReal
open Mueps SemimetricSpace OrderedSemimetric Balls CoveringConditions Boundary PrecisionGaps

/--
The precision threshold excludes every nontrivial robust partition.

# Proof strategy
Each proper cut has a consecutive crossing pair. SuccessorCovering places the
ball at the lower point inside an epsilon-ball centered on the opposite boundary.
Restrict this covering to the lower point's side and apply BoundaryExistence.

# Attribution
Aleksandrov, Kuske and Völlinger, Corollary 2.
-/
lemma precisionObstruction {S : Type u} [Finite S] [LinearOrder S] [Nontrivial S] (d : Distance S)
    (hd : IsOrderedSemimetricSpace d (· ≤ ·)) (μ : ℝ≥0) (ε : ℝ>0)
    (hbound : threshold d hd μ ≤ ε) : Mueps.PartitionRobustness.OnlyTrivial d hd.1 μ ε := by
  apply (MuepsProofs.MainResults.boundaryExistence d hd μ ε).mpr
  intro A hA hAc
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hAc
  have hne : a ≠ b := by rintro rfl; exact hb ha
  rcases lt_or_gt_of_ne hne with hab | hba
  · obtain ⟨p, q, _, _, hpA, hqA, hpq⟩ := crossing_pair A hab ha hb
    refine ⟨p, Or.inl ⟨hpA, ?_⟩⟩
    intro z hz
    exact ⟨q, ⟨hqA, p, by simpa using hpA, Or.inr hpq⟩,
      MuepsProofs.OrderedBounds.successorCovering d hd μ ε hbound p q hpq hz.1⟩
  · obtain ⟨p, q, _, _, hpA, hqA, hpq⟩ := crossing_pair Aᶜ hba hb (by simpa using ha)
    refine ⟨p, Or.inr ⟨hpA, ?_⟩⟩
    intro z hz
    exact ⟨q, ⟨by simpa using hqA, p, hpA, Or.inr hpq⟩,
      MuepsProofs.OrderedBounds.successorCovering d hd μ ε hbound p q hpq hz.1⟩

end MuepsProofs.OrderedBounds
