import Lax544225.ListSpaces
import Lax544225Proofs.Products
import Mathlib.Algebra.BigOperators.Fin

universe u

namespace Lax544225Proofs

open Lax544225.SemimetricSpace Lax544225.OrderedSemimetric
open scoped NNReal BigOperators

private def coordinates {S : Type u} (pad : S) (n : ℕ) (f : List S) : Fin n → S :=
  fun i => f.getD i pad

private lemma list_eq_of_coordinates {S : Type u} (pad : S) (f g : List S)
    (hlen : f.length = g.length)
    (h : coordinates pad f.length f = coordinates pad f.length g) : f = g := by
  apply List.ext_getElem hlen
  intro i hi hj
  have hv := congrFun h (⟨i, hi⟩ : Fin f.length)
  change f.getD i pad = g.getD i pad at hv
  rw [List.getD_eq_getElem f pad hi, List.getD_eq_getElem g pad hj] at hv
  exact hv

private lemma range_sup_eq_univ_sup (n : ℕ) (h : ℕ → ℝ≥0) :
    (Finset.range n).sup h = Finset.univ.sup (fun i : Fin n => h i) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    exact Finset.le_sup (f := fun j : Fin n => h j) (Finset.mem_univ ⟨i, Finset.mem_range.1 hi⟩)
  · apply Finset.sup_le
    intro i _
    exact Finset.le_sup (f := h) (Finset.mem_range.2 i.isLt)

private lemma sum_list_as_product {S : Type u} (d : Distance S) (pad : S) (f g : List S) :
    Lax544225.ListSpaces.sumDistance d pad f g = Lax544225.ListSpaces.lengthPenalty f g +
      Lax544225.SumProductSpace.sumDistance d (max f.length g.length)
        (coordinates pad _ f) (coordinates pad _ g) := by
  unfold Lax544225.ListSpaces.sumDistance Lax544225.SumProductSpace.sumDistance coordinates
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun i => d (f.getD i pad) (g.getD i pad)) _).symm

private lemma max_list_as_product {S : Type u} (d : Distance S) (pad : S) (f g : List S) :
    Lax544225.ListSpaces.maxDistance d pad f g = Lax544225.ListSpaces.lengthPenalty f g +
      Lax544225.MaximumProductSpace.maxDistance d (max f.length g.length)
        (coordinates pad _ f) (coordinates pad _ g) := by
  simp only [Lax544225.ListSpaces.maxDistance, Lax544225.MaximumProductSpace.maxDistance,
    coordinates, range_sup_eq_univ_sup]

private lemma lengthPenalty_symm {S : Type u} (f g : List S) :
    Lax544225.ListSpaces.lengthPenalty f g = Lax544225.ListSpaces.lengthPenalty g f := by
  simp only [Lax544225.ListSpaces.lengthPenalty, eq_comm]

private lemma padded_semimetric {S : Type u} (pad : S)
    (D : (n : ℕ) → Distance (Fin n → S)) (hD : ∀ n, IsSemimetricSpace (D n))
    (dlist : Distance (List S))
    (hformula : ∀ f g, dlist f g = Lax544225.ListSpaces.lengthPenalty f g +
      D (max f.length g.length) (coordinates pad _ f) (coordinates pad _ g)) :
    IsSemimetricSpace dlist := by
  refine ⟨⟨[]⟩, ?_, ?_⟩
  · intro f g
    rw [hformula]
    constructor
    · intro hzero
      have hz := add_eq_zero.1 hzero
      have hlen : f.length = g.length := by
        by_contra hne
        have : (1 : ℝ≥0) = 0 := by
          simpa [Lax544225.ListSpaces.lengthPenalty, hne] using hz.1
        exact one_ne_zero this
      apply list_eq_of_coordinates pad f g hlen
      have hcoords := (hD (max f.length g.length)).2.1 _ _ |>.1 hz.2
      have hm : max f.length g.length = f.length := by rw [← hlen, max_self]
      exact Eq.mp (congrArg (fun n => coordinates pad n f = coordinates pad n g) hm) hcoords
    · intro hfg
      subst g
      have hz := (hD (max f.length f.length)).2.1
        (coordinates pad _ f) (coordinates pad _ f) |>.2 rfl
      rw [hz]
      simp [Lax544225.ListSpaces.lengthPenalty]
  · intro f g
    rw [hformula, hformula, lengthPenalty_symm, max_comm g.length f.length]
    congr 1
    exact (hD (max f.length g.length)).2.2 _ _

private lemma listLe_to_product {S : Type u} (le : S → S → Prop) (pad : S)
    (n : ℕ) (f g : List S) (hf : f.length = n)
    (hfg : Lax544225.ListSpaces.listLe le pad f g) :
    Lax544225.SumProductSpace.productLe le n (coordinates pad n f) (coordinates pad n g) := by
  intro i
  exact hfg.2 i (hf ▸ i.isLt)

private lemma synchronizedListLe_to_product {S : Type u} (d : Distance S)
    (le : S → S → Prop) (pad : S) (n : ℕ) (f g : List S) (hf : f.length = n)
    (hfg : Lax544225.ListSpaces.synchronizedListLe d le pad f g) :
    Lax544225.MaximumProductSpace.synchronizedLe d le n (coordinates pad n f) (coordinates pad n g) := by
  refine ⟨listLe_to_product le pad n f g hf hfg.1, ?_⟩
  intro i j
  exact hfg.2 i (hf ▸ i.isLt) j (hf ▸ j.isLt)

private lemma list_partialOrder {S : Type u} (le : S → S → Prop) (pad : S)
    (h : ∀ n, IsPartialOrder (Fin n → S) (Lax544225.SumProductSpace.productLe le n)) :
    IsPartialOrder (List S) (Lax544225.ListSpaces.listLe le pad) := by
  refine { refl := ?_, trans := ?_, antisymm := ?_ }
  · intro f
    refine ⟨rfl, ?_⟩
    intro i hi
    exact (h f.length).refl (coordinates pad f.length f) ⟨i, hi⟩
  · intro f g k hfg hgk
    refine ⟨hfg.1.trans hgk.1, ?_⟩
    have hfk := (h f.length).trans _ _ _
      (listLe_to_product le pad f.length f g rfl hfg)
      (listLe_to_product le pad f.length g k hfg.1.symm hgk)
    intro i hi
    exact hfk ⟨i, hi⟩
  · intro f g hfg hgf
    apply list_eq_of_coordinates pad f g hfg.1
    exact (h f.length).antisymm _ _
      (listLe_to_product le pad f.length f g rfl hfg)
      (listLe_to_product le pad f.length g f hfg.1.symm hgf)

private lemma synchronized_list_partialOrder {S : Type u} (d : Distance S)
    (le : S → S → Prop) (pad : S)
    (h : ∀ n, IsPartialOrder (Fin n → S) (Lax544225.MaximumProductSpace.synchronizedLe d le n)) :
    IsPartialOrder (List S) (Lax544225.ListSpaces.synchronizedListLe d le pad) := by
  refine { refl := ?_, trans := ?_, antisymm := ?_ }
  · intro f
    have hf := (h f.length).refl (coordinates pad f.length f)
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · intro i hi
      exact hf.1 ⟨i, hi⟩
    · intro i hi j hj
      exact hf.2 ⟨i, hi⟩ ⟨j, hj⟩
  · intro f g k hfg hgk
    have hfk := (h f.length).trans _ _ _
      (synchronizedListLe_to_product d le pad f.length f g rfl hfg)
      (synchronizedListLe_to_product d le pad f.length g k hfg.1.1.symm hgk)
    refine ⟨⟨hfg.1.1.trans hgk.1.1, ?_⟩, ?_⟩
    · intro i hi
      exact hfk.1 ⟨i, hi⟩
    · intro i hi j hj
      exact hfk.2 ⟨i, hi⟩ ⟨j, hj⟩
  · intro f g hfg hgf
    apply list_eq_of_coordinates pad f g hfg.1.1
    exact (h f.length).antisymm _ _
      (synchronizedListLe_to_product d le pad f.length f g rfl hfg)
      (synchronizedListLe_to_product d le pad f.length g f hfg.1.1.symm hgf)

private lemma sum_list_equal_length {S : Type u} (d : Distance S) (pad : S)
    (n : ℕ) (f g : List S) (hf : f.length = n) (hg : g.length = n) :
    Lax544225.ListSpaces.sumDistance d pad f g =
      Lax544225.SumProductSpace.sumDistance d n (coordinates pad n f) (coordinates pad n g) := by
  rw [sum_list_as_product]
  have hp : Lax544225.ListSpaces.lengthPenalty f g = 0 := by
    simp [Lax544225.ListSpaces.lengthPenalty, hf, hg]
  rw [hp, zero_add]
  have hm : max f.length g.length = n := by rw [hf, hg, max_self]
  exact congrArg (fun m => Lax544225.SumProductSpace.sumDistance d m
    (coordinates pad m f) (coordinates pad m g)) hm

private lemma max_list_equal_length {S : Type u} (d : Distance S) (pad : S)
    (n : ℕ) (f g : List S) (hf : f.length = n) (hg : g.length = n) :
    Lax544225.ListSpaces.maxDistance d pad f g =
      Lax544225.MaximumProductSpace.maxDistance d n (coordinates pad n f) (coordinates pad n g) := by
  rw [max_list_as_product]
  have hp : Lax544225.ListSpaces.lengthPenalty f g = 0 := by
    simp [Lax544225.ListSpaces.lengthPenalty, hf, hg]
  rw [hp, zero_add]
  have hm : max f.length g.length = n := by rw [hf, hg, max_self]
  exact congrArg (fun m => Lax544225.MaximumProductSpace.maxDistance d m
    (coordinates pad m f) (coordinates pad m g)) hm

/--
---
conclusion: Lax544225.ListSpaces.proposition1_sumList
---
Padded finite sums with a length penalty form an ordered semimetric space.

**Lean statements for Model Validation**

- [`binary64SumListOrdered`](https://github.com/clemenskuske/semimetric-robustness-lax-submission/blob/6a0ab4b1b173c95435637d859b8fb1c698647781/proofs/Lax544225Proofs/FlocqExamples.lean#L225): the sum-distance list instance is an ordered semimetric space.
- [`binary64NaNListLengthPenalty`](https://github.com/clemenskuske/semimetric-robustness-lax-submission/blob/6a0ab4b1b173c95435637d859b8fb1c698647781/proofs/Lax544225Proofs/FlocqExamples.lean#L207): appending the NaN padding value still incurs distance one.

# Proof strategy

Transfer the tuple semimetric and partial-order laws through padded coordinate
vectors. A vanishing length penalty forces equal lengths, and tuple separation
then forces list equality. On comparable lists the penalty is zero and all
lengths coincide, so the sum-product antitriangle result applies directly.

# Attribution

Proposition 1.5 of Aleksandrov, Kuske and Völlinger's supplied FSEN 2027 manuscript.
-/
lemma sumListSpace {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrderedSemimetricSpace d le) (pad : S) :
    IsOrderedSemimetricSpace (Lax544225.ListSpaces.sumDistance d pad) (Lax544225.ListSpaces.listLe le pad) := by
  have htuple := Lax544225.SumProductSpace.proposition1_sumProduct d le hd
  refine ⟨padded_semimetric pad (Lax544225.SumProductSpace.sumDistance d)
      (fun n => (htuple n).1) _ (sum_list_as_product d pad),
    list_partialOrder le pad (fun n => (htuple n).2.1), ?_⟩
  intro f g k hfg hgk
  have hgf := hfg.1.symm
  have hkf := (hfg.1.trans hgk.1).symm
  rw [sum_list_equal_length d pad f.length f g rfl hgf,
    sum_list_equal_length d pad f.length g k hgf hkf,
    sum_list_equal_length d pad f.length f k rfl hkf]
  exact (htuple f.length).2.2 _ _ _
    (listLe_to_product le pad f.length f g rfl hfg)
    (listLe_to_product le pad f.length g k hgf hgk)

/--
---
conclusion: Lax544225.ListSpaces.proposition1_maximumList
---
Padded synchronized maxima with a length penalty form an ordered semimetric space.

**Lean statements for Model Validation**

- [`binary64MaximumListOrdered`](https://github.com/clemenskuske/semimetric-robustness-lax-submission/blob/6a0ab4b1b173c95435637d859b8fb1c698647781/proofs/Lax544225Proofs/FlocqExamples.lean#L231): the maximum-distance list instance is ordered under the synchronized order.
- [`binary64PointwiseMaximumFailure`](https://github.com/clemenskuske/semimetric-robustness-lax-submission/blob/6a0ab4b1b173c95435637d859b8fb1c698647781/proofs/Lax544225Proofs/FlocqExamples.lean#L194): ordinary pointwise order fails the maximum-distance antitriangle law.

# Proof strategy

Use the synchronized maximum-product result on the padded coordinate vectors.
The length penalty and tuple separation distinguish lists. Equal-length
comparison transfers the synchronized partial order, including its transitivity,
and the chain distance bound from the corresponding tuple construction.

# Attribution

Proposition 1.5 of Aleksandrov, Kuske and Völlinger's supplied FSEN 2027 manuscript;
the padded length-penalty construction is also present in the cited Rocq reference.
-/
lemma maximumListSpace {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrderedSemimetricSpace d le) (hadd : Additive d le) (pad : S) :
    IsOrderedSemimetricSpace (Lax544225.ListSpaces.maxDistance d pad)
      (Lax544225.ListSpaces.synchronizedListLe d le pad) := by
  have htuple := Lax544225.MaximumProductSpace.proposition1_maximumProduct d le hd hadd
  refine ⟨padded_semimetric pad (Lax544225.MaximumProductSpace.maxDistance d)
      (fun n => (htuple n).1) _ (max_list_as_product d pad),
    synchronized_list_partialOrder d le pad (fun n => (htuple n).2.1), ?_⟩
  intro f g k hfg hgk
  have hgf := hfg.1.1.symm
  have hkf := (hfg.1.1.trans hgk.1.1).symm
  rw [max_list_equal_length d pad f.length f g rfl hgf,
    max_list_equal_length d pad f.length g k hgf hkf,
    max_list_equal_length d pad f.length f k rfl hkf]
  exact (htuple f.length).2.2 _ _ _
    (synchronizedListLe_to_product d le pad f.length f g rfl hfg)
    (synchronizedListLe_to_product d le pad f.length g k hgf hgk)

end Lax544225Proofs
