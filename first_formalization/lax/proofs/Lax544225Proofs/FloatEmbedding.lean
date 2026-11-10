import Lax544225.FloatAbsoluteSpace
import Lax544225.FloatSquaredSpace
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic

/-! Canonical finite values and the independent category order embed in the reals. -/

universe u

namespace Lax544225Proofs.FloatEmbedding

open scoped NNReal
open Lax544225.FloatAbsoluteSpace Lax544225.FloatSquaredSpace
open Lax544225.BinaryFloats Lax544225.Semimetric Lax544225.OrderedSemimetric

noncomputable def magnitude {F : Format} (f : FiniteValue F) : ℝ :=
  (f.mantissa : ℝ) * (2 : ℝ) ^ (f.exponent - (F.precision : ℤ))

lemma two_zpow_pos (e : ℤ) : 0 < (2 : ℝ) ^ e := zpow_pos (by norm_num) e

lemma magnitude_pos {F : Format} (f : FiniteValue F) : 0 < magnitude f := by
  exact mul_pos (by exact_mod_cast f.mantissa_mem.1) (two_zpow_pos _)

lemma finiteReal_eq {F : Format} (f : FiniteValue F) :
    finiteReal f = (-1 : ℝ) ^ f.sign.val * magnitude f := by
  unfold finiteReal magnitude
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num)]
  ring

lemma finiteReal_positive {F : Format} (f : FiniteValue F) (h : f.sign.val = 0) :
    finiteReal f = magnitude f := by simp [finiteReal_eq, h]

lemma finiteReal_negative {F : Format} (f : FiniteValue F) (h : f.sign.val ≠ 0) :
    finiteReal f = -magnitude f := by
  have hsign : f.sign.val = 1 := by have := f.sign.isLt; omega
  simp [finiteReal_eq, hsign]

lemma magnitude_upper {F : Format} (f : FiniteValue F) :
    magnitude f < (2 : ℝ) ^ (f.exponent + 1) := by
  have hm : (f.mantissa : ℝ) < (2 : ℝ) ^ (F.precision + 1) := by
    exact_mod_cast f.mantissa_mem.2
  calc
    magnitude f < (2 : ℝ) ^ (F.precision + 1) *
        (2 : ℝ) ^ (f.exponent - (F.precision : ℤ)) :=
      mul_lt_mul_of_pos_right hm (two_zpow_pos _)
    _ = (2 : ℝ) ^ (f.exponent + 1) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      omega

lemma magnitude_normal_lower {F : Format} (f : FiniteValue F)
    (h : F.minExponent < f.exponent) : (2 : ℝ) ^ f.exponent ≤ magnitude f := by
  have hm : 2 ^ F.precision ≤ f.mantissa := f.canonical.resolve_right (ne_of_gt h)
  have hmr : (2 : ℝ) ^ F.precision ≤ (f.mantissa : ℝ) := by exact_mod_cast hm
  calc
    (2 : ℝ) ^ f.exponent = (2 : ℝ) ^ F.precision *
        (2 : ℝ) ^ (f.exponent - (F.precision : ℤ)) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      omega
    _ ≤ magnitude f := mul_le_mul_of_nonneg_right hmr (two_zpow_pos _).le

lemma magnitude_lt_of_exponent_lt {F : Format} (f g : FiniteValue F)
    (h : f.exponent < g.exponent) : magnitude f < magnitude g := by
  calc
    magnitude f < (2 : ℝ) ^ (f.exponent + 1) := magnitude_upper f
    _ ≤ (2 : ℝ) ^ g.exponent := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ ≤ magnitude g := magnitude_normal_lower g (lt_of_le_of_lt f.exponent_mem.1 h)

lemma magnitude_injective {F : Format} (f g : FiniteValue F)
    (h : magnitude f = magnitude g) :
    f.exponent = g.exponent ∧ f.mantissa = g.mantissa := by
  have he : f.exponent = g.exponent := by
    rcases lt_trichotomy f.exponent g.exponent with hlt | heq | hgt
    · exact False.elim ((ne_of_lt (magnitude_lt_of_exponent_lt f g hlt)) h)
    · exact heq
    · exact False.elim ((ne_of_lt (magnitude_lt_of_exponent_lt g f hgt)) h.symm)
  refine ⟨he, ?_⟩
  unfold magnitude at h
  rw [he] at h
  have hm : (f.mantissa : ℝ) = (g.mantissa : ℝ) :=
    (mul_right_cancel₀ (ne_of_gt (two_zpow_pos _))) h
  exact_mod_cast hm

lemma finiteReal_injective {F : Format} : Function.Injective (@finiteReal F) := by
  intro f g h
  have hf := magnitude_pos f
  have hg := magnitude_pos g
  have hs : f.sign = g.sign := by
    apply Fin.ext
    by_cases hfs : f.sign.val = 0 <;> by_cases hgs : g.sign.val = 0
    · exact hfs.trans hgs.symm
    · rw [finiteReal_positive f hfs, finiteReal_negative g hgs] at h
      linarith
    · rw [finiteReal_negative f hfs, finiteReal_positive g hgs] at h
      linarith
    · have := f.sign.isLt; have := g.sign.isLt; omega
  have hm : magnitude f = magnitude g := by
    by_cases hfs : f.sign.val = 0
    · have hgs : g.sign.val = 0 := hs ▸ hfs
      simpa only [finiteReal_positive f hfs, finiteReal_positive g hgs] using h
    · have hgs : g.sign.val ≠ 0 := hs ▸ hfs
      simpa only [finiteReal_negative f hfs, finiteReal_negative g hgs, neg_inj] using h
  rcases magnitude_injective f g hm with ⟨he, hm⟩
  cases f
  cases g
  cases hs
  cases he
  cases hm
  rfl

lemma magnitude_bounds {F : Format} (f : FiniteValue F) :
    (2 : ℝ) ^ (F.minExponent - (F.precision : ℤ)) ≤ magnitude f ∧
      magnitude f < (2 : ℝ) ^ (F.maxExponent + 1) := by
  constructor
  · calc
      (2 : ℝ) ^ (F.minExponent - (F.precision : ℤ)) ≤
          (2 : ℝ) ^ (f.exponent - (F.precision : ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num) (sub_le_sub_right f.exponent_mem.1 _)
      _ ≤ magnitude f := by
        have hm : (1 : ℝ) ≤ (f.mantissa : ℝ) := by exact_mod_cast f.mantissa_mem.1
        simpa only [one_mul, magnitude] using mul_le_mul_of_nonneg_right hm (two_zpow_pos _).le
  · exact (magnitude_upper f).trans_le
      (zpow_le_zpow_right₀ (by norm_num) (by have := f.exponent_mem.2; omega))

noncomputable def upper (F : Format) : ℝ := (2 : ℝ) ^ (F.maxExponent + 1)
noncomputable def lower (F : Format) : ℝ := (2 : ℝ) ^ (F.minExponent - (F.precision : ℤ))
noncomputable def halfLower (F : Format) : ℝ :=
  (2 : ℝ) ^ (F.minExponent - (F.precision : ℤ) - 1)

lemma format_bounds (F : Format) :
    0 < halfLower F ∧ halfLower F < lower F ∧ lower F ≤ upper F := by
  refine ⟨two_zpow_pos _, ?_, ?_⟩
  · exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
  · exact zpow_le_zpow_right₀ (by norm_num)
      (by have := F.exponent_le; have := F.precision; omega)

lemma category_bounds {F : Format} (x : Value F) :
    category x ≤ 6 ∧
      (category x = 0 → phi F x = -upper F) ∧
      (category x = 1 → -upper F < phi F x ∧ phi F x ≤ -lower F) ∧
      (category x = 2 → phi F x = -halfLower F) ∧
      (category x = 3 → phi F x = 0) ∧
      (category x = 4 → lower F ≤ phi F x ∧ phi F x < upper F) ∧
      (category x = 5 → phi F x = upper F) ∧
      (category x = 6 → phi F x = upper F + 1) := by
  cases x with
  | finite f =>
      have hb := magnitude_bounds f
      by_cases hs : f.sign.val = 0
      · simpa [category, phi, hs, finiteReal_positive f hs, lower, upper] using hb
      · have hn : finiteReal f = -magnitude f := finiteReal_negative f hs
        simpa [category, phi, hs, hn, lower, upper] using And.intro hb.2 hb.1
  | zero s =>
      by_cases hs : s.val = 0 <;> simp [category, phi, hs, halfLower]
  | infinity s =>
      by_cases hs : s.val = 0 <;> simp [category, phi, hs, upper]
  | nan => simp [category, phi, upper]

lemma phi_category_strict {F : Format} {x y : Value F}
    (hcat : category x < category y) : phi F x < phi F y := by
  rcases category_bounds x with ⟨hxl, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩
  rcases category_bounds y with ⟨hyl, hy0, hy1, hy2, hy3, hy4, hy5, hy6⟩
  rcases format_bounds F with ⟨hp, hl, hu⟩
  interval_cases hcx : category x <;> interval_cases hcy : category y <;>
    norm_num [hcx, hcy] at hcat hx0 hx1 hx2 hx3 hx4 hx5 hx6 hy0 hy1 hy2 hy3 hy4 hy5 hy6 ⊢ <;>
    linarith

noncomputable def categoryOffset (F : Format) : ℕ → ℝ
  | 0 => -upper F
  | 2 => -halfLower F
  | 5 => upper F
  | 6 => upper F + 1
  | _ => 0

lemma phi_eq_within_add_offset {F : Format} (x : Value F) :
    phi F x = withinCategory x + categoryOffset F (category x) := by
  cases x with
  | finite f => by_cases hs : f.sign.val = 0 <;> simp [phi, withinCategory, category, hs, categoryOffset]
  | zero s => by_cases hs : s.val = 0 <;> simp [phi, withinCategory, category, hs, categoryOffset, halfLower]
  | infinity s => by_cases hs : s.val = 0 <;> simp [phi, withinCategory, category, hs, categoryOffset, upper]
  | nan => simp [phi, withinCategory, category, categoryOffset, upper]

lemma same_category_compare {F : Format} {x y : Value F}
    (hcat : category x = category y) :
    phi F x ≤ phi F y ↔ withinCategory x ≤ withinCategory y := by
  rw [phi_eq_within_add_offset x, phi_eq_within_add_offset y, hcat]
  exact add_le_add_iff_right _

lemma ieeeLe_iff_phi_le (F : Format) (x y : Value F) :
    ieeeLe F x y ↔ phi F x ≤ phi F y := by
  constructor
  · rintro (hcat | ⟨hcat, hwithin⟩)
    · exact (phi_category_strict hcat).le
    · exact (same_category_compare hcat).2 hwithin
  · intro hphi
    rcases lt_trichotomy (category x) (category y) with hlt | heq | hgt
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, (same_category_compare heq).1 hphi⟩
    · exact False.elim ((not_lt_of_ge hphi) (phi_category_strict hgt))

lemma category_within_injective {F : Format} {x y : Value F}
    (hcat : category x = category y) (hwithin : withinCategory x = withinCategory y) : x = y := by
  cases x with
  | finite f =>
      cases y with
      | finite g => exact congrArg Value.finite (finiteReal_injective hwithin)
      | zero s => simp only [category] at hcat; split_ifs at hcat <;> omega
      | infinity s => simp only [category] at hcat; split_ifs at hcat <;> omega
      | nan => simp only [category] at hcat; split_ifs at hcat <;> omega
  | zero s =>
      cases y with
      | finite g => simp only [category] at hcat; split_ifs at hcat <;> omega
      | zero t => fin_cases s <;> fin_cases t <;> simp_all [category]
      | infinity t => simp only [category] at hcat; split_ifs at hcat <;> omega
      | nan => simp only [category] at hcat; split_ifs at hcat <;> omega
  | infinity s =>
      cases y with
      | finite g => simp only [category] at hcat; split_ifs at hcat <;> omega
      | zero t => simp only [category] at hcat; split_ifs at hcat <;> omega
      | infinity t => fin_cases s <;> fin_cases t <;> simp_all [category]
      | nan => simp only [category] at hcat; split_ifs at hcat; omega
  | nan =>
      cases y with
      | finite g => simp only [category] at hcat; split_ifs at hcat <;> omega
      | zero t => simp only [category] at hcat; split_ifs at hcat <;> omega
      | infinity t => simp only [category] at hcat; split_ifs at hcat; omega
      | nan => rfl

lemma phi_injective (F : Format) : Function.Injective (phi F) := by
  intro x y hphi
  have hcat : category x = category y := by
    rcases lt_trichotomy (category x) (category y) with hlt | heq | hgt
    · exact False.elim ((ne_of_lt (phi_category_strict hlt)) hphi)
    · exact heq
    · exact False.elim ((ne_of_lt (phi_category_strict hgt)) hphi.symm)
  apply category_within_injective hcat
  rw [phi_eq_within_add_offset x, phi_eq_within_add_offset y, hcat] at hphi
  exact add_right_cancel hphi

/--
The independent IEEE category relation is a linear order.

# Proof strategy

Prove uniqueness of canonical finite representations from their sign and
exponent magnitude intervals. Separate the seven categories by their embedded
real ranges, obtaining an injective φ and equivalence between IEEE order and
ordinary real order. Pull back the real order laws through that bridge.

# Attribution

Proposition 1 of the source paper. The binary-float embedding argument in
`flocq_ordered_spaces/semimetrics.v` of verinncoq/mueps-robustness-proofs supplied
mathematical guidance; the canonical exponent-interval proof here is in Lean.
-/
lemma floatLinearOrder (F : Format) : IsLinearOrder (Value F) (ieeeLe F) where
  refl x := (ieeeLe_iff_phi_le F x x).2 le_rfl
  trans x y z hxy hyz := (ieeeLe_iff_phi_le F x z).2
    ((ieeeLe_iff_phi_le F x y).1 hxy |>.trans ((ieeeLe_iff_phi_le F y z).1 hyz))
  antisymm x y hxy hyx := phi_injective F
    (le_antisymm ((ieeeLe_iff_phi_le F x y).1 hxy) ((ieeeLe_iff_phi_le F y x).1 hyx))
  total x y := by
    rcases le_total (phi F x) (phi F y) with hxy | hyx
    · exact Or.inl ((ieeeLe_iff_phi_le F x y).2 hxy)
    · exact Or.inr ((ieeeLe_iff_phi_le F y x).2 hyx)

/--
Absolute embedded distance is additive along IEEE chains.

# Proof strategy

Use the proved order bridge to obtain an increasing chain of real values.
Each absolute difference equals the difference in increasing direction; the
two adjacent differences telescope. Nonnegativity makes NNReal conversion exact.

# Attribution

Proposition 1.4 of the source paper and its scalar absolute-difference identity.
-/
lemma floatAbsoluteAdditivity (F : Format) : Additive (absDistance F) (ieeeLe F) := by
  intro a b c hab hbc
  have hab' := (ieeeLe_iff_phi_le F a b).1 hab
  have hbc' := (ieeeLe_iff_phi_le F b c).1 hbc
  apply NNReal.coe_injective
  simp only [absDistance, NNReal.coe_add, Real.coe_toNNReal _ (abs_nonneg _)]
  rw [abs_of_nonpos (sub_nonpos.2 (hab'.trans hbc')),
    abs_of_nonpos (sub_nonpos.2 hab'), abs_of_nonpos (sub_nonpos.2 hbc')]
  ring

/--
---
conclusion: Lax544225.FloatAbsoluteSpace.statement
---
Absolute embedded distance forms an ordered semimetric.

**Lean statements for Model Validation**

The Lean counterparts of the supplied Rocq/Flocq model include:

- [`format_finite_value`](https://github.com/clemenskuske/semimetric-robustness-lax-submission/blob/6a0ab4b1b173c95435637d859b8fb1c698647781/proofs/Lax544225Proofs/FlocqBridge.lean#L114): the Flocq parameter conversion preserves finite values.
- [`phiQ_cast`](https://github.com/clemenskuske/semimetric-robustness-lax-submission/blob/6a0ab4b1b173c95435637d859b8fb1c698647781/proofs/Lax544225Proofs/FlocqBridge.lean#L79): the rational embedding agrees with the real embedding.
- [`ieeeLe_iff_phiQ_le`](https://github.com/clemenskuske/semimetric-robustness-lax-submission/blob/6a0ab4b1b173c95435637d859b8fb1c698647781/proofs/Lax544225Proofs/FlocqBridge.lean#L95): IEEE order agrees with rational comparison.
- [`squareDistQ_strict_antitriangle`](https://github.com/clemenskuske/semimetric-robustness-lax-submission/blob/6a0ab4b1b173c95435637d859b8fb1c698647781/proofs/Lax544225Proofs/FlocqBridge.lean#L150): squared distance is strictly superadditive along nondegenerate increasing chains.

# Proof strategy

Injectivity of φ gives distance-zero separation, and absolute differences are
symmetric. Reuse the proved IEEE linear order and scalar chain additivity,
whose equality implies the required antitriangle inequality.

# Attribution

Proposition 1.1 of the source paper.


-/
lemma floatAbsoluteSpace (F : Format) : IsOrdered (absDistance F) (ieeeLe F) := by
  refine ⟨⟨⟨Value.nan⟩, ?_, ?_⟩, (floatLinearOrder F).toIsPartialOrder, ?_⟩
  · intro x y
    simp only [absDistance, Real.toNNReal_eq_zero, abs_nonpos_iff, sub_eq_zero]
    exact ⟨fun h => phi_injective F h, fun h => congrArg (phi F) h⟩
  · intro x y
    simp only [absDistance, abs_sub_comm]
  · intro a b c hab hbc
    exact (floatAbsoluteAdditivity F a b c hab hbc).symm.le

private lemma square_ordered {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrdered d le) : IsOrdered (fun x y => d x y ^ 2) le := by
  refine ⟨⟨hd.1.1, ?_, ?_⟩, hd.2.1, ?_⟩
  · intro x y
    simpa only [sq_eq_zero_iff] using hd.1.2.1 x y
  · intro x y
    exact congrArg (fun r : ℝ≥0 => r ^ 2) (hd.1.2.2 x y)
  · intro a b c hab hbc
    have h := NNReal.coe_le_coe.2 (hd.2.2 a b c hab hbc)
    apply NNReal.coe_le_coe.1
    simp only [NNReal.coe_add, NNReal.coe_pow] at h ⊢
    nlinarith [NNReal.coe_nonneg (d a b), NNReal.coe_nonneg (d b c)]

private lemma squareDistance_eq_absDistance_sq (F : Format) (x y : Value F) :
    squareDistance F x y = absDistance F x y ^ 2 := by
  apply NNReal.coe_injective
  simp only [squareDistance, absDistance, NNReal.coe_pow,
    Real.coe_toNNReal _ (sq_nonneg _), Real.coe_toNNReal _ (abs_nonneg _)]
  rw [sq_abs]

/--
---
conclusion: Lax544225.FloatSquaredSpace.statement
---
Squared embedded distance forms an ordered semimetric.

# Proof strategy

Use the absolute-distance proposition and closure of ordered semimetrics under
squaring. Squaring preserves symmetry, separation and the partial order. The
base antitriangle inequality bounds the sum of adjacent distances; its square
dominates the sum of their squares because both distances are nonnegative.

# Attribution

Proposition 1.2 of the source paper and the squared-distance construction in
`flocq_ordered_spaces/semimetrics.v` of verinncoq/mueps-robustness-proofs.
-/
lemma floatSquaredSpace (F : Format) : IsOrdered (squareDistance F) (ieeeLe F) := by
  have hdist : squareDistance F = fun x y => absDistance F x y ^ 2 := by
    funext x y
    exact squareDistance_eq_absDistance_sq F x y
  rw [hdist]
  exact square_ordered (absDistance F) (ieeeLe F) (Lax544225.FloatAbsoluteSpace.statement F)

end Lax544225Proofs.FloatEmbedding
