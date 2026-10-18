/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions

/-! Proof-side abbreviations for the covering conditions stated in Theorems 1–3. -/

universe u

namespace MuepsProofs.CoveringConditions

open scoped NNReal
open Mueps.Semimetric Mueps.Balls Mueps.Boundary

/-- No μ-ball centered in a part is covered by ε-balls from its complement. -/
def Uncovered {S : Type u} (d : Distance S) (hd : IsSemimetric d) (P : Set (Set S)) (μ ε : ℝ≥0) : Prop :=
  ∀ A ∈ P, ∀ x ∈ A, ¬ ball d hd x μ ⊆ neighborhood d hd Aᶜ ε

/-- Every nontrivial cut admits an opposite-side covering obstruction. -/
def EveryCutCovered {S : Type u} (d : Distance S) (hd : IsSemimetric d) (μ ε : ℝ≥0) : Prop :=
  ∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
    ∃ x, (x ∈ A ∧ ball d hd x μ ⊆ neighborhood d hd Aᶜ ε) ∨
      (x ∈ Aᶜ ∧ ball d hd x μ ⊆ neighborhood d hd A ε)

/-- Every nontrivial cut has a side-restricted μ-ball covered by the opposite boundary. -/
def EveryCutBoundaryCovered {S : Type u} [LinearOrder S] (d : Distance S) (hd : IsSemimetric d)
    (μ ε : ℝ≥0) : Prop :=
  ∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
    ∃ x, (x ∈ A ∧ ball d hd x μ ∩ A ⊆ neighborhood d hd (complementBoundary A) ε) ∨
      (x ∈ Aᶜ ∧ ball d hd x μ ∩ Aᶜ ⊆ neighborhood d hd (boundary A) ε)

end MuepsProofs.CoveringConditions
