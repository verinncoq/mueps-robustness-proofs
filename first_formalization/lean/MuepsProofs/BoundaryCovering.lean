/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.CoveringConditions
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic

universe u

namespace MuepsProofs.OrderedBounds

open scoped NNReal
open Mueps Semimetric OrderedSemimetric Balls CoveringConditions Boundary PrecisionGaps

lemma distance_self {S : Type u} {d : Distance S} (hd : IsSemimetric d) (x : S) :
    d x x = 0 := (hd.2.1 x x).2 rfl

/-- The standard cover relation is the paper's strict no-between successor relation. -/
lemma successor_iff {S : Type u} [LinearOrder S] (x y : S) :
    Successor x y ↔ x < y ∧ ¬ ∃ z, x < z ∧ z < y := by
  simp only [Successor, CovBy, not_exists, not_and]

/-- A finite ordered interval whose endpoints lie on opposite sides contains a crossing pair. -/
lemma crossing_pair {S : Type u} [Finite S] [LinearOrder S] (A : Set S)
    {a b : S} (hab : a < b) (ha : a ∈ A) (hb : b ∉ A) :
    ∃ p q, a ≤ p ∧ q ≤ b ∧ p ∈ A ∧ q ∉ A ∧ Successor p q := by
  classical
  let T : Set S := {z | a ≤ z ∧ z ≤ b ∧ z ∉ A}
  obtain ⟨q, hq, hmin⟩ := Set.exists_min_image T id T.toFinite ⟨b, hab.le, le_rfl, hb⟩
  have haq : a < q := lt_of_le_of_ne hq.1 (by intro h; exact hq.2.2 (h ▸ ha))
  let U : Set S := {z | a ≤ z ∧ z < q}
  obtain ⟨p, hp, hmax⟩ := Set.exists_max_image U id U.toFinite ⟨a, le_rfl, haq⟩
  have hpA : p ∈ A := by
    by_contra hn
    have hqp := hmin p ⟨hp.1, hp.2.le.trans hq.2.1, hn⟩
    exact (not_le_of_gt hp.2) hqp
  refine ⟨p, q, hp.1, hq.2.1, hpA, hq.2.2, (successor_iff p q).2 ⟨hp.2, ?_⟩⟩
  rintro ⟨z, hpz, hzq⟩
  exact (not_le_of_gt hpz) (hmax z ⟨hp.1.trans hpz.le, hzq⟩)

/-- Moving an opposite-side center towards the point gives a boundary center no farther away. -/
lemma boundary_center {S : Type u} [Finite S] [LinearOrder S] {d : Distance S}
    (hd : IsOrdered d (· ≤ ·)) (A : Set S) {a b : S} (ha : a ∈ A) (hb : b ∉ A) :
    ∃ z ∈ complementBoundary A, d a z ≤ d a b := by
  classical
  have hne : a ≠ b := by rintro rfl; exact hb ha
  rcases lt_or_gt_of_ne hne with hab | hba
  · obtain ⟨p, q, hap, hqb, hpA, hqA, hpq⟩ := crossing_pair A hab ha hb
    refine ⟨q, ⟨hqA, p, ?_, Or.inr hpq⟩, ?_⟩
    · simpa only [Set.mem_compl_iff, not_not] using hpA
    · exact (le_add_of_nonneg_right (show 0 ≤ d q b from zero_le)).trans
        (hd.2.2 a q b (hap.trans hpq.le) hqb)
  · obtain ⟨p, q, hbp, hqa, hpA, hqA, hpq⟩ := crossing_pair Aᶜ hba hb (by simpa using ha)
    refine ⟨p, ⟨hpA, q, hqA, Or.inl hpq⟩, ?_⟩
    rw [hd.1.2.2 a p, hd.1.2.2 a b]
    exact (le_add_of_nonneg_left (show 0 ≤ d b p from zero_le)).trans
      (hd.2.2 b p a hbp (hpq.le.trans hqa))

/--
Reduce opposite-side covering to opposite-boundary covering.

# Proof strategy
Find a consecutive crossing between each covered point and its opposite-side center.
The ordered antitriangle inequality makes the boundary center no farther away.

# Attribution
Aleksandrov and Völlinger, Theorem 3, forward direction.
-/
lemma cutToBoundaryCovering {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (_hε : 0 < ε) :
    EveryCutCovered d hd.1 μ ε → EveryCutBoundaryCovered d hd.1 μ ε := by
  intro h A hA hAc
  obtain ⟨x, hx | hx⟩ := h A hA hAc
  · refine ⟨x, Or.inl ⟨hx.1, ?_⟩⟩
    intro y hy
    obtain ⟨z, hz, hyz⟩ := hx.2 hy.1
    obtain ⟨b, hb, hyb⟩ := boundary_center hd A hy.2 hz
    exact ⟨b, hb, hyb.trans hyz⟩
  · refine ⟨x, Or.inr ⟨hx.1, ?_⟩⟩
    intro y hy
    obtain ⟨z, hz, hyz⟩ := hx.2 hy.1
    obtain ⟨b, hb, hyb⟩ := boundary_center hd Aᶜ hy.2 (by simpa using hz)
    exact ⟨b, by simpa [complementBoundary] using hb, hyb.trans hyz⟩

/--
Extend the side-restricted covering to the whole ball.

# Proof strategy
Points on the center's side use the given boundary covering. Opposite-side points
belong to their own closed epsilon-ball because their self-distance is zero.

# Attribution
Aleksandrov and Völlinger, Theorem 3, reverse direction.
-/
lemma boundaryToCutCovering {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (_hε : 0 < ε) :
    EveryCutBoundaryCovered d hd.1 μ ε → EveryCutCovered d hd.1 μ ε := by
  classical
  intro h A hA hAc
  obtain ⟨x, hx | hx⟩ := h A hA hAc
  · refine ⟨x, Or.inl ⟨hx.1, ?_⟩⟩
    intro y hy
    by_cases hyA : y ∈ A
    · obtain ⟨z, hz, hyz⟩ := hx.2 ⟨hy, hyA⟩
      exact ⟨z, hz.1, hyz⟩
    · exact ⟨y, hyA, by simp [ball, distance_self hd.1]⟩
  · refine ⟨x, Or.inr ⟨hx.1, ?_⟩⟩
    intro y hy
    by_cases hyA : y ∈ A
    · exact ⟨y, hyA, by simp [ball, distance_self hd.1]⟩
    · obtain ⟨z, hz, hyz⟩ := hx.2 ⟨hy, hyA⟩
      exact ⟨z, hz.1, hyz⟩


end MuepsProofs.OrderedBounds
