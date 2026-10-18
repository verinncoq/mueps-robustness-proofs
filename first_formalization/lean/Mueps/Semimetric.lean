/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mathlib.Data.NNReal.Basic

/-!
A semimetric space is a nonempty set equipped with a symmetric, nonnegative real distance that is zero exactly on equal inputs. No triangle inequality is imposed.

**Definition from the paper.**

Let $(S,d)$ be a pair of a nonempty set and a function
$d:S\times S\rightarrow\mathbb{R}_{\geq 0}$ such that, for all $x,y\in S$,

$$d(x,y)=0\iff x=y$$

(identity of indiscernibles) and

$$d(x,y)=d(y,x)$$

(symmetry). Then $(S,d)$ is a **semimetric space** and $d$ is a **distance**
function on $S$.

# Formalization notes

The codomain ℝ≥0 supplies nonnegativity. The carrier is a type; nonemptiness is part of the predicate. Subspaces carry the restriction of the same distance.
-/

universe u

namespace Mueps.Semimetric

open scoped NNReal

/-- A nonnegative real-valued distance on a carrier. -/
abbrev Distance (S : Type u) := S → S → ℝ≥0

/-- The defining properties of a semimetric space, including a nonempty carrier. -/
def IsSemimetric {S : Type u} (d : Distance S) : Prop :=
  Nonempty S ∧ (∀ x y, d x y = 0 ↔ x = y) ∧ (∀ x y, d x y = d y x)

end Mueps.Semimetric
