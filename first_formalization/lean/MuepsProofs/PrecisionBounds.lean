/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.BoundaryCovering
import MuepsProofs.CoveringConditions
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic

universe u

namespace MuepsProofs.OrderedBounds

open scoped NNReal
open Mueps Semimetric OrderedSemimetric Balls CoveringConditions Boundary PrecisionGaps

lemma steps_pos {S : Type u} [Finite S] [LinearOrder S] {x y : S} (hxy : x < y) :
    0 < steps x y := by
  have hcard : 1 < (Set.Icc x y).ncard :=
    (Set.one_lt_ncard_iff).2 ⟨x, y, ⟨le_rfl, hxy.le⟩, ⟨hxy.le, le_rfl⟩, hxy.ne⟩
  unfold steps
  omega

lemma interval_successor {S : Type u} [LinearOrder S] {a x y : S}
    (hax : a ≤ x) (hxy : Successor x y) :
    Set.Icc a y = insert y (Set.Icc a x) := by
  ext z
  constructor
  · intro hz
    by_cases hzy : z = y
    · exact Or.inl hzy
    · exact Or.inr ⟨hz.1, hxy.le_of_lt (lt_of_le_of_ne hz.2 hzy)⟩
  · rintro (rfl | hz)
    · exact ⟨hax.trans hxy.le, le_rfl⟩
    · exact ⟨hz.1, hz.2.trans hxy.le⟩

lemma steps_successor_add {S : Type u} [Finite S] [LinearOrder S] {a x y : S}
    (hax : a ≤ x) (hxy : Successor x y) : steps a y = steps a x + 1 := by
  have hn : y ∉ Set.Icc a x := by intro h; exact (not_le_of_gt hxy.lt) h.2
  have hcard : (Set.Icc a y).ncard = (Set.Icc a x).ncard + 1 := by
    rw [interval_successor hax hxy, Set.ncard_insert_of_notMem hn]
  have hp : 0 < (Set.Icc a x).ncard := (Set.ncard_pos).2 ⟨a, le_rfl, hax⟩
  unfold steps
  omega

lemma steps_successor {S : Type u} [Finite S] [LinearOrder S] {x y : S}
    (hxy : Successor x y) : steps x y = 1 := by
  rw [steps, hxy.Icc_eq, Set.ncard_pair hxy.ne]

lemma upper_ratios_bounded {S : Type u} [Finite S] [LinearOrder S] (d : Distance S) :
    BddAbove {r | ∃ x y, x < y ∧ r = d x y / (steps x y : ℝ≥0)} := by
  apply Set.Finite.bddAbove
  refine (Set.finite_range (fun p : S × S => d p.1 p.2 / (steps p.1 p.2 : ℝ≥0))).subset ?_
  rintro r ⟨x, y, _, rfl⟩
  exact ⟨(x, y), rfl⟩

lemma inverse_ratios_bounded {S : Type u} [Finite S] [LinearOrder S] (d : Distance S) :
    BddAbove {r | ∃ x y, x < y ∧ r = (steps x y : ℝ≥0) / d x y} := by
  apply Set.Finite.bddAbove
  refine (Set.finite_range (fun p : S × S => (steps p.1 p.2 : ℝ≥0) / d p.1 p.2)).subset ?_
  rintro r ⟨x, y, _, rfl⟩
  exact ⟨(x, y), rfl⟩

lemma distance_upper {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) {x y : S} (hxy : x < y) :
    d x y ≤ deltaUpper d hd * (steps x y : ℝ≥0) := by
  have hratio : d x y / (steps x y : ℝ≥0) ≤ deltaUpper d hd :=
    le_csSup (upper_ratios_bounded d) ⟨x, y, hxy, rfl⟩
  exact (div_le_iff₀ (by exact_mod_cast steps_pos hxy)).1 hratio

lemma steps_inverse {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) {x y : S} (hxy : x < y) :
    (steps x y : ℝ≥0) ≤ deltaInverse d hd * d x y := by
  have hdpos : 0 < d x y := pos_iff_ne_zero.2 (by
    intro hz
    exact hxy.ne ((hd.1.2.1 x y).1 hz))
  have hratio : (steps x y : ℝ≥0) / d x y ≤ deltaInverse d hd :=
    le_csSup (inverse_ratios_bounded d) ⟨x, y, hxy, rfl⟩
  exact (div_le_iff₀ hdpos).1 hratio

lemma precision_product_ge_one {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) {x y : S} (hxy : Successor x y) :
    1 ≤ deltaUpper d hd * deltaInverse d hd := by
  have hu := distance_upper d hd hxy.lt
  have hi := steps_inverse d hd hxy.lt
  rw [steps_successor hxy] at hu hi
  simp only [Nat.cast_one, mul_one] at hu hi
  calc
    1 ≤ deltaInverse d hd * d x y := hi
    _ ≤ deltaInverse d hd * deltaUpper d hd := mul_le_mul_of_nonneg_left hu zero_le
    _ = deltaUpper d hd * deltaInverse d hd := mul_comm _ _

/--
The precision threshold covers a ball from the next ordered point.

# Proof strategy
Use the finite ratio suprema to bound distance by Delta times interval steps and
steps by delta times distance. A successor adds exactly one interval step. On the
other side of the successor, the ordered antitriangle inequality gives monotonicity.

# Attribution
Aleksandrov and Völlinger, Theorem 4.
-/
theorem successorCovering {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (_hε : 0 < ε)
    (hbound : threshold d hd μ ≤ ε) (x y : S) (hxy : Successor x y) :
    ball d hd.1 x μ ⊆ ball d hd.1 y ε := by
  intro z hz
  change d z x ≤ μ at hz
  change d z y ≤ ε
  rcases lt_trichotomy z x with hzx | rfl | hxz
  · calc
      d z y ≤ deltaUpper d hd * (steps z y : ℝ≥0) := distance_upper d hd (hzx.trans hxy.lt)
      _ = deltaUpper d hd * (steps z x : ℝ≥0) + deltaUpper d hd := by
        rw [steps_successor_add hzx.le hxy, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ deltaUpper d hd * (deltaInverse d hd * d z x) + deltaUpper d hd := by
        gcongr
        exact steps_inverse d hd hzx
      _ = deltaUpper d hd * deltaInverse d hd * d z x + deltaUpper d hd := by ring
      _ ≤ threshold d hd μ := by
        unfold threshold
        gcongr
      _ ≤ ε := hbound
  · have hu := distance_upper d hd hxy.lt
    rw [steps_successor hxy, Nat.cast_one, mul_one] at hu
    exact hu.trans ((le_add_of_nonneg_left (show 0 ≤ deltaUpper d hd * deltaInverse d hd * μ
      from zero_le)).trans hbound)
  · have hyz : y ≤ z := hxy.ge_of_gt hxz
    have hμ : μ ≤ threshold d hd μ := by
      calc
        μ = 1 * μ := (one_mul μ).symm
        _ ≤ (deltaUpper d hd * deltaInverse d hd) * μ :=
          mul_le_mul_of_nonneg_right (precision_product_ge_one d hd hxy) zero_le
        _ ≤ threshold d hd μ := le_add_of_nonneg_right zero_le
    rw [hd.1.2.2 z y, hd.1.2.2 z x] at *
    exact ((le_add_of_nonneg_left (show 0 ≤ d x y from zero_le)).trans
      (hd.2.2 x y z hxy.le hyz)).trans (hz.trans (hμ.trans hbound))


end MuepsProofs.OrderedBounds
