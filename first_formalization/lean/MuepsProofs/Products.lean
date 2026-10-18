/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions

universe u

namespace MuepsProofs

open Mueps.Semimetric Mueps.OrderedSemimetric Mueps.SumProductSpace Mueps.MaximumProductSpace
open scoped NNReal BigOperators

lemma product_partialOrder {S : Type u} (le : S → S → Prop)
    (h : IsPartialOrder S le) (n : ℕ) : IsPartialOrder (Fin n → S) (productLe le n) := by
  refine { refl := ?_, trans := ?_, antisymm := ?_ }
  · intro f i
    exact h.refl (f i)
  · intro f g k hfg hgk i
    exact h.trans (f i) (g i) (k i) (hfg i) (hgk i)
  · intro f g hfg hgf
    funext i
    exact h.antisymm (f i) (g i) (hfg i) (hgf i)

lemma sum_product_semimetric {S : Type u} (d : Distance S)
    (hd : IsSemimetric d) (n : ℕ) : IsSemimetric (sumDistance d n) := by
  classical
  rcases hd.1 with ⟨s⟩
  refine ⟨⟨fun _ => s⟩, ?_, ?_⟩
  · intro f g
    constructor
    · intro hzero
      funext i
      apply (hd.2.1 (f i) (g i)).1
      have hle : d (f i) (g i) ≤ sumDistance d n f g := by
        change d (f i) (g i) ≤ ∑ j, d (f j) (g j)
        exact Finset.single_le_sum (fun j _ => (show 0 ≤ d (f j) (g j) from zero_le)) (Finset.mem_univ i)
      exact le_antisymm (hzero ▸ hle) bot_le
    · intro hfg
      subst g
      simp [sumDistance, fun x => (hd.2.1 x x).2 rfl]
  · intro f g
    exact Finset.sum_congr rfl (fun i _ => hd.2.2 (f i) (g i))

lemma max_product_semimetric {S : Type u} (d : Distance S)
    (hd : IsSemimetric d) (n : ℕ) : IsSemimetric (maxDistance d n) := by
  classical
  rcases hd.1 with ⟨s⟩
  refine ⟨⟨fun _ => s⟩, ?_, ?_⟩
  · intro f g
    constructor
    · intro hzero
      funext i
      apply (hd.2.1 (f i) (g i)).1
      have hle : d (f i) (g i) ≤ maxDistance d n f g := by
        unfold maxDistance
        exact Finset.le_sup (f := fun j => d (f j) (g j)) (Finset.mem_univ i)
      exact le_antisymm (hzero ▸ hle) bot_le
    · intro hfg
      subst g
      simp [maxDistance, fun x => (hd.2.1 x x).2 rfl]
  · intro f g
    unfold maxDistance
    congr 1
    funext i
    exact hd.2.2 (f i) (g i)

/--
Finite sums preserve the ordered semimetric laws.

# Proof strategy

Zero sums force coordinate equality; symmetry and the antitriangle law follow
coordinatewise. The empty product is included by the same finite-sum laws.

# Attribution

Proposition 1.3 of Aleksandrov and Völlinger's supplied FSEN 2027 manuscript.
-/
lemma sumProductSpace {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrdered d le) (n : ℕ) : IsOrdered (sumDistance d n) (productLe le n) := by
  refine ⟨sum_product_semimetric d hd.1 n, product_partialOrder le hd.2.1 n, ?_⟩
  intro f g k hfg hgk
  unfold sumDistance
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => hd.2.2 (f i) (g i) (k i) (hfg i) (hgk i))

lemma synchronized_partialOrder {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrdered d le) (hadd : Additive d le) (n : ℕ) :
    IsPartialOrder (Fin n → S) (synchronizedLe d le n) := by
  refine { refl := ?_, trans := ?_, antisymm := ?_ }
  · intro f
    refine ⟨(product_partialOrder le hd.2.1 n).refl f, ?_⟩
    intro i j
    rw [(hd.1.2.1 (f i) (f i)).2 rfl, (hd.1.2.1 (f j) (f j)).2 rfl]
  · intro f g k hfg hgk
    refine ⟨(product_partialOrder le hd.2.1 n).trans f g k hfg.1 hgk.1, ?_⟩
    intro i j
    rw [hadd (f i) (g i) (k i) (hfg.1 i) (hgk.1 i),
      hadd (f j) (g j) (k j) (hfg.1 j) (hgk.1 j), hfg.2 i j, hgk.2 i j]
  · intro f g hfg hgf
    exact (product_partialOrder le hd.2.1 n).antisymm f g hfg.1 hgf.1

lemma synchronized_max_eq_coordinate {S : Type u} (d : Distance S) (le : S → S → Prop)
    (n : ℕ) (f g : Fin n → S) (hfg : synchronizedLe d le n f g) (i : Fin n) :
    maxDistance d n f g = d (f i) (g i) := by
  classical
  unfold maxDistance
  apply le_antisymm
  · exact Finset.sup_le (f := fun j => d (f j) (g j)) (fun j _ => le_of_eq (hfg.2 j i))
  · exact Finset.le_sup (f := fun j => d (f j) (g j)) (Finset.mem_univ i)

lemma synchronized_max_additive {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrdered d le) (hadd : Additive d le) (n : ℕ) :
    Additive (maxDistance d n) (synchronizedLe d le n) := by
  intro f g k hfg hgk
  cases n with
  | zero => simp [maxDistance]
  | succ n =>
    let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    have hfk := (synchronized_partialOrder d le hd hadd (n + 1)).trans f g k hfg hgk
    rw [synchronized_max_eq_coordinate d le (n + 1) f k hfk i,
      synchronized_max_eq_coordinate d le (n + 1) f g hfg i,
      synchronized_max_eq_coordinate d le (n + 1) g k hgk i]
    exact hadd (f i) (g i) (k i) (hfg.1 i) (hgk.1 i)

/--
Synchronized finite maxima preserve the ordered semimetric laws.

# Proof strategy

A maximum vanishes exactly when every coordinate distance vanishes. Exact
base additivity makes synchronization transitive. On a nonempty synchronized
product the maximum equals any coordinate distance, giving exact chain
additivity; the empty product has distance zero.

# Attribution

Proposition 1.4 of Aleksandrov and Völlinger's supplied FSEN 2027 manuscript;
the synchronized construction is also described in the cited Rocq reference.
-/
lemma maximumProductSpace {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrdered d le) (hadd : Additive d le) (n : ℕ) :
    IsOrdered (maxDistance d n) (synchronizedLe d le n) := by
  refine ⟨max_product_semimetric d hd.1 n, synchronized_partialOrder d le hd hadd n, ?_⟩
  intro f g k hfg hgk
  exact le_of_eq (synchronized_max_additive d le hd hadd n f g k hfg hgk).symm

end MuepsProofs
