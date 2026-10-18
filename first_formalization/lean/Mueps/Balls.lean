/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Semimetric
import Mathlib.Data.Set.Lattice

/-!
A closed ball consists of all inputs within a chosen distance of its center, including inputs exactly at that distance.

**Definition from the paper.**

Let $(S,d)$ be a semimetric space. Then

$$B(x^*,\epsilon):=\{x\in S\mid d(x,x^*)\leq\epsilon\}$$

is an **$\epsilon$-ball** around $x^*$.

# Formalization notes

Closed inequalities are essential: an input at distance exactly ε must have the same label. Ball membership uses d(y,x), matching the paper.

The auxiliary neighborhood of a set $A$ is $\bigcup_{x\in A}B(x,r)$.
-/

universe u

namespace Mueps.Balls

open scoped NNReal

open Semimetric
/-- The closed ball centered at x with radius r. -/
def ball {S : Type u} (d : Distance S) (_hd : IsSemimetric d)
    (x : S) (r : ℝ≥0) : Set S :=
  {y | d y x ≤ r}

/-- The union of closed r-balls with centers in A. -/
def neighborhood {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (A : Set S) (r : ℝ≥0) : Set S :=
  {y | ∃ x ∈ A, y ∈ ball d hd x r}

end Mueps.Balls
