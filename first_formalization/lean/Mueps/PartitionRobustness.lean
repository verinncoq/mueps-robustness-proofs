/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Partitions
import Mueps.Balls

/-!
A partition is robust when each input has a nearby center whose entire robustness ball lies in the same part as that input.

**Definition from the paper.**

Let $(S,d)$ be a semimetric space. A partition $P:=\{S_1,\dots,S_p\}$ of $S$
is **globally robust** for $\mu\geq0$, $\epsilon>0$ if and only if

$$\forall x\in S\;\exists x'\in B(x,\mu)\;
\left[\bigvee_{i\in[p]}\bigl(\{x\}\cup B(x',\epsilon)\subseteq S_i\bigr)\right].$$

# Formalization notes

The robustness and separation predicates take explicit semimetric and partition evidence. Triviality of every robust partition quantifies over finite valid partitions. Separation uses a strict inequality because balls are closed.

The auxiliary separation predicate requires $\epsilon<d(x,y)$ for points in distinct parts.
-/

universe u

namespace Mueps.PartitionRobustness

open scoped NNReal

open Semimetric Partitions Balls
/-- Coverage by monochromatic balls whose centers are μ-close to the input. -/
def Robust {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (P : Set (Set S)) (_hP : IsPartition P) (μ ε : ℝ≥0) : Prop :=
  ∀ x, ∃ x', x' ∈ ball d hd x μ ∧ ∃ A ∈ P, x ∈ A ∧ ball d hd x' ε ⊆ A

/-- Distinct parts are separated by distance strictly greater than ε. -/
def Separated {S : Type u} (d : Distance S) (_hd : IsSemimetric d)
    (P : Set (Set S)) (_hP : IsPartition P) (ε : ℝ≥0) : Prop :=
  ∀ A ∈ P, ∀ B ∈ P, A ≠ B → ∀ x ∈ A, ∀ y ∈ B, ε < d x y

/-- Every robust finite partition of the carrier has only the whole carrier as a part. -/
def OnlyTrivial {S : Type u} (d : Distance S) (hd : IsSemimetric d) (μ ε : ℝ≥0) : Prop :=
  ∀ P (hP : IsPartition P), Robust d hd P hP μ ε → IsTrivial P

end Mueps.PartitionRobustness
