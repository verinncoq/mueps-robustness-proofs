/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.SumProductSpace
import Mathlib.Data.Finset.Lattice.Fold

/-!
For tuples, take the greatest coordinate distance. Compare tuples only when each coordinate moves in order by the same distance. The base distance must be additive along ordered chains.

**Definition from the paper.**

Suppose $(\mathcal F,<,d)$ is an ordered semimetric space and
$d(a,c)=d(a,b)+d(b,c)$ whenever $a\leq b\leq c$. Define

$$d_4(f,g):=\max_{i\in[n]}d(f_i,g_i),$$

$$<^n_*:=\{(f,g)\in\mathcal F^n\times\mathcal F^n\mid f<^n g\ \land
\forall i,j\in[n],\ d(f_i,g_i)=d(f_j,g_j)\}.$$

Then $(\mathcal F^n,<^n_*,d_4)$ is an ordered semimetric space.

# Formalization notes

The construction is proved for any base carrier. Coordinates are Fin n; the maximum over no coordinates is zero. The formal relation includes equality, with the paper’s strict notation denoting its strict part.
-/

universe u

namespace Mueps.MaximumProductSpace

open Semimetric OrderedSemimetric SumProductSpace

/-- Coordinatewise order restricted to equal distances in every coordinate. -/
def synchronizedLe {S : Type u} (d : Distance S) (le : S → S → Prop) (n : ℕ)
    (f g : Fin n → S) : Prop :=
  productLe le n f g ∧ ∀ i j, d (f i) (g i) = d (f j) (g j)

/-- Maximum of the base distances between corresponding coordinates. -/
noncomputable def maxDistance {S : Type u} (d : Distance S) (n : ℕ) : Distance (Fin n → S) :=
  fun f g => Finset.univ.sup (fun i => d (f i) (g i))


end Mueps.MaximumProductSpace
