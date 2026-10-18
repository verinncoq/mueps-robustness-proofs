/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
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
open Mueps Semimetric OrderedSemimetric Balls CoveringConditions Boundary PrecisionGaps

/--
The precision threshold excludes every nontrivial robust partition.

# Proof strategy
Each proper cut has a consecutive crossing pair. SuccessorCovering places the
ball at the lower point inside an epsilon-ball centered on the opposite boundary.
Restrict this covering to the lower point's side and apply BoundaryExistence.

# Attribution
Aleksandrov and Völlinger, Corollary 2.
-/
lemma precisionObstruction {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε)
    (hbound : threshold d hd μ ≤ ε) : Mueps.PartitionRobustness.OnlyTrivial d hd.1 μ ε := by
  apply (MuepsProofs.MainResults.boundaryExistence d hd μ ε hε).mpr
  intro A hA hAc
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hAc
  have hne : a ≠ b := by rintro rfl; exact hb ha
  rcases lt_or_gt_of_ne hne with hab | hba
  · obtain ⟨p, q, _, _, hpA, hqA, hpq⟩ := crossing_pair A hab ha hb
    refine ⟨p, Or.inl ⟨hpA, ?_⟩⟩
    intro z hz
    exact ⟨q, ⟨hqA, p, by simpa using hpA, Or.inr hpq⟩,
      MuepsProofs.OrderedBounds.successorCovering d hd μ ε hε hbound p q hpq hz.1⟩
  · obtain ⟨p, q, _, _, hpA, hqA, hpq⟩ := crossing_pair Aᶜ hba hb (by simpa using ha)
    refine ⟨p, Or.inr ⟨hpA, ?_⟩⟩
    intro z hz
    exact ⟨q, ⟨by simpa using hqA, p, hpA, Or.inr hpq⟩,
      MuepsProofs.OrderedBounds.successorCovering d hd μ ε hε hbound p q hpq hz.1⟩


end MuepsProofs.OrderedBounds
