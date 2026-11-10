import Lax544225Proofs.CoveringConditions
import Lax544225Proofs.Basic
import Lax544225.GeneralExistence
import Lax544225.BoundaryCoveringCharacterization
import Lax544225.BoundaryExistence
import Lax544225.SuccessorCovering
import Lax544225.PrecisionObstruction
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic

universe u

namespace Lax544225Proofs.OrderedBounds

open scoped NNReal
open Lax544225 Semimetric OrderedSemimetric Balls CoveringConditions Boundary PrecisionGaps

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
Aleksandrov, Kuske and Völlinger, Theorem 3, forward direction.
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
Aleksandrov, Kuske and Völlinger, Theorem 3, reverse direction.
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
    · exact ⟨y, hyA, by simp [ball, Basic.distance_self hd.1]⟩
  · refine ⟨x, Or.inr ⟨hx.1, ?_⟩⟩
    intro y hy
    by_cases hyA : y ∈ A
    · exact ⟨y, hyA, by simp [ball, Basic.distance_self hd.1]⟩
    · obtain ⟨z, hz, hyz⟩ := hx.2 ⟨hy, hyA⟩
      exact ⟨z, hz.1, hyz⟩

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
---
conclusion: Lax544225.SuccessorCovering.statement
---
The precision threshold covers a ball from the next ordered point.

# Proof strategy
Use the finite ratio suprema to bound distance by Delta times interval steps and
steps by delta times distance. A successor adds exactly one interval step. On the
other side of the successor, the ordered antitriangle inequality gives monotonicity.

# Attribution
Aleksandrov, Kuske and Völlinger, Theorem 4.
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

/--
---
conclusion: Lax544225.PrecisionObstruction.statement
---
The precision threshold excludes every nontrivial robust partition.

# Proof strategy
Each proper cut has a consecutive crossing pair. SuccessorCovering places the
ball at the lower point inside an epsilon-ball centered on the opposite boundary.
Restrict this covering to the lower point's side and apply BoundaryExistence.

# Attribution
Aleksandrov, Kuske and Völlinger, Corollary 2.
-/
lemma precisionObstruction {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε)
    (hbound : threshold d hd μ ≤ ε) : Lax544225.PartitionRobustness.OnlyTrivial d hd.1 μ ε := by
  apply (Lax544225.BoundaryExistence.statement d hd μ ε hε).mpr
  intro A hA hAc
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hAc
  have hne : a ≠ b := by rintro rfl; exact hb ha
  rcases lt_or_gt_of_ne hne with hab | hba
  · obtain ⟨p, q, _, _, hpA, hqA, hpq⟩ := crossing_pair A hab ha hb
    refine ⟨p, Or.inl ⟨hpA, ?_⟩⟩
    intro z hz
    exact ⟨q, ⟨hqA, p, by simpa using hpA, Or.inr hpq⟩,
      Lax544225.SuccessorCovering.statement d hd μ ε hε hbound p q hpq hz.1⟩
  · obtain ⟨p, q, _, _, hpA, hqA, hpq⟩ := crossing_pair Aᶜ hba hb (by simpa using ha)
    refine ⟨p, Or.inr ⟨hpA, ?_⟩⟩
    intro z hz
    exact ⟨q, ⟨by simpa using hqA, p, hpA, Or.inr hpq⟩,
      Lax544225.SuccessorCovering.statement d hd μ ε hε hbound p q hpq hz.1⟩

/--
Only-trivial robustness gives opposite-boundary covering.

# Proof strategy
Compose the general existence criterion with its finite-order boundary reduction.

# Attribution
Aleksandrov, Kuske and Völlinger, Corollary 1, forward direction.
-/
lemma trivialityToBoundaryCovering {S : Type u} [Finite S] [LinearOrder S]
    (d : Distance S) (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε) :
    Lax544225.PartitionRobustness.OnlyTrivial d hd.1 μ ε → EveryCutBoundaryCovered d hd.1 μ ε := by
  intro h
  exact (Lax544225.BoundaryCoveringCharacterization.statement d hd μ ε hε).mp
    ((Lax544225.GeneralExistence.statement d hd.1 μ ε hε).mp h)

/--
Opposite-boundary covering excludes nontrivial robust partitions.

# Proof strategy
Compose the boundary extension with the previously established general cut criterion.

# Attribution
Aleksandrov, Kuske and Völlinger, Corollary 1, reverse direction.
-/
lemma boundaryCoveringToTriviality {S : Type u} [Finite S] [LinearOrder S]
    (d : Distance S) (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε) :
    EveryCutBoundaryCovered d hd.1 μ ε → Lax544225.PartitionRobustness.OnlyTrivial d hd.1 μ ε := by
  intro h
  exact (Lax544225.GeneralExistence.statement d hd.1 μ ε hε).mpr
    ((Lax544225.BoundaryCoveringCharacterization.statement d hd μ ε hε).mpr h)

end Lax544225Proofs.OrderedBounds
