import Lax544225.MaximumProductSpace
import Mathlib.Data.List.GetD

/-!
---
title: Finite List Distances and Orders
type: definition
---
For lists of different lengths, missing entries are filled with a padding value before comparing coordinates, and a unit penalty distinguishes different lengths. The orders compare only lists of equal length.

**Definition from the paper.**

The sum and maximum product distances extend to arbitrary finite lists of
floating-point numbers. For distance computation, the shorter list is padded
with $\mathrm{NaN}$, and a penalty equal to $1$ is added whenever the list
lengths differ. The partial orders compare only lists of the same length;
lists of different lengths are incomparable.
Both extensions are ordered semimetric spaces: the sum extension assumes an
ordered semimetric base, and the maximum extension additionally assumes
additivity along ordered chains.

# Formalization notes

The floating-point instance chooses NaN as padding. Without the length penalty, appending NaN would give distance zero between different lists. The list maximum construction uses an additive base distance just as the fixed-length construction does.

The definitions allow an arbitrary base space and padding point, specializing to the paper by choosing floating-point values and NaN.
-/

universe u

namespace Lax544225.ListSpaces

open scoped NNReal

open SemimetricSpace OrderedSemimetric
open scoped BigOperators
/-- Equal-length lists ordered coordinatewise; other lengths are incomparable. -/
def listLe {S : Type u} (le : S → S → Prop) (pad : S) (f g : List S) : Prop :=
  f.length = g.length ∧ ∀ i < f.length, le (f.getD i pad) (g.getD i pad)

/-- Equal-length coordinatewise order with equal base distances across coordinates. -/
def synchronizedListLe {S : Type u} (d : Distance S) (le : S → S → Prop)
    (pad : S) (f g : List S) : Prop :=
  listLe le pad f g ∧ ∀ i < f.length, ∀ j < f.length,
    d (f.getD i pad) (g.getD i pad) = d (f.getD j pad) (g.getD j pad)

/-- A positive penalty that distinguishes different list lengths. -/
def lengthPenalty {S : Type u} (f g : List S) : ℝ≥0 :=
  if f.length = g.length then 0 else 1

/-- Sum of padded coordinate distances, plus the length penalty. -/
noncomputable def sumDistance {S : Type u} (d : Distance S) (pad : S) : Distance (List S) :=
  fun f g => lengthPenalty f g +
    ∑ i ∈ Finset.range (max f.length g.length), d (f.getD i pad) (g.getD i pad)

/-- Maximum padded coordinate distance, plus the length penalty. -/
noncomputable def maxDistance {S : Type u} (d : Distance S) (pad : S) : Distance (List S) :=
  fun f g => lengthPenalty f g +
    (Finset.range (max f.length g.length)).sup (fun i => d (f.getD i pad) (g.getD i pad))

/-- The sum-distance list extension is an ordered semimetric space. -/
axiom proposition1_sumList {S : Type u} (d : Distance S)
    (le : S → S → Prop) (hd : IsOrderedSemimetricSpace d le) (pad : S) :
    IsOrderedSemimetricSpace (sumDistance d pad) (listLe le pad)

/-- The maximum-distance list extension is ordered when the base is additive. -/
axiom proposition1_maximumList {S : Type u} (d : Distance S)
    (le : S → S → Prop) (hd : IsOrderedSemimetricSpace d le)
    (hadd : Additive d le) (pad : S) :
    IsOrderedSemimetricSpace (maxDistance d pad) (synchronizedListLe d le pad)

end Lax544225.ListSpaces
