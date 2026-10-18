/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.OrderedSemimetric
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
For tuples, add the distances between corresponding coordinates and compare tuples coordinate by coordinate. This preserves the ordered semimetric laws.

**Definition from the paper.**

If $(\mathcal F,<,d)$ is an ordered semimetric space, define

$$d_3(f,g):=\sum_{i\in[n]}d(f_i,g_i)$$

on $\mathcal F^n$, with the $n$-wise product partial order $<^n$.
Then $(\mathcal F^n,<^n,d_3)$ is an ordered semimetric space.

# Formalization notes

The construction is proved for any base carrier, including floating-point values. Coordinates are Fin n; the empty tuple has distance zero. The non-strict product relation includes equality; the paper’s strict notation denotes its strict part.
-/

universe u

namespace Mueps.SumProductSpace

open Semimetric OrderedSemimetric
open scoped BigOperators

/-- Coordinatewise order on finite tuples. -/
def productLe {S : Type u} (le : S → S → Prop) (n : ℕ) (f g : Fin n → S) : Prop :=
  ∀ i, le (f i) (g i)

/-- Sum of the base distances between corresponding coordinates. -/
noncomputable def sumDistance {S : Type u} (d : Distance S) (n : ℕ) : Distance (Fin n → S) :=
  fun f g => ∑ i, d (f i) (g i)


end Mueps.SumProductSpace
