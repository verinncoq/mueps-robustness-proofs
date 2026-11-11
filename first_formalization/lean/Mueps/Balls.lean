/- Adapted from lax-544225, source 62ba21d994907b076c31bc2328e0c3209bd1ea17.
   Standalone Lean port, synchronized 11 November 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.SemimetricSpace
import Mathlib.Data.Set.Lattice

/-!
A closed ball consists of all inputs within a chosen distance of its center, including inputs exactly at that distance.

**Definition from the paper.**

Let $(S,d)$ be a semimetric space. Then

$$B(x^*,\epsilon):=\{x\in S\mid d(x,x^*)\leq\epsilon\}$$

is an **$\epsilon$-ball** around $x^*$.

# Formalization notes

Closed inequalities are essential: an input at distance exactly ε must have the same label. Ball membership uses d(x,x*), matching the paper; Lean spells the center `x_star`.

The union of balls with centers in a set $A$ is $\bigcup_{x\in A}B(x,r)$.
-/

universe u

namespace Mueps.Balls

open scoped NNReal

open SemimetricSpace
/-- The closed ε-ball centered at the paper’s point x*. -/
def ball {S : Type u} (d : Distance S) (_hd : IsSemimetricSpace d)
    (x_star : S) (ε : ℝ≥0) : Set S :=
  {x | d x x_star ≤ ε}

/-- The union of closed r-balls with centers in A. -/
def unionOfBalls {S : Type u} (d : Distance S) (hd : IsSemimetricSpace d)
    (A : Set S) (r : ℝ≥0) : Set S :=
  {y | ∃ x ∈ A, y ∈ ball d hd x r}

end Mueps.Balls
