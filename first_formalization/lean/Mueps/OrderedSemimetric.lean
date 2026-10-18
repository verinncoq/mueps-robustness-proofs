/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Semimetric
import Mathlib.Order.Defs.PartialOrder

/-!
An ordered semimetric space relates its order to its distance: moving through an intermediate point in the order cannot cost more than the direct distance between the endpoints.

**Definition from the paper.**

A tuple $(S,<,d)$ with a set $S$, a partial order $<$ on $S$, and
$d:S\times S\rightarrow\mathbb{R}_{\geq0}$ is an **ordered semimetric space**
if $(S,d)$ is a semimetric space and, for all $a,b,c\in S$,

$$a\leq b\leq c\quad\Longrightarrow\quad d(a,c)\geq d(a,b)+d(b,c).$$

# Formalization notes

The order is an explicit non-strict relation. IsPartialOrder provides reflexivity, transitivity, and antisymmetry. The reverse triangle inequality is imposed only on ordered chains. Additivity is an additional property needed for synchronized maximum distances.

The auxiliary `Additive` predicate replaces the chain inequality by equality.
-/

universe u

namespace Mueps.OrderedSemimetric

open Semimetric
/-- The semimetric, partial-order, and ordered-chain distance laws. -/
def IsOrdered {S : Type u} (d : Distance S) (le : S → S → Prop) : Prop :=
  IsSemimetric d ∧ IsPartialOrder S le ∧
    (∀ a b c, le a b → le b c → d a b + d b c ≤ d a c)

/-- Exact additivity of distance along the given ordered chains. -/
def Additive {S : Type u} (d : Distance S) (le : S → S → Prop) : Prop :=
  ∀ a b c, le a b → le b c → d a c = d a b + d b c

end Mueps.OrderedSemimetric
