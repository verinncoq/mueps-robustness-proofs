/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions

/-! Proof-side notation for the distance inherited by a subset. -/

universe u

namespace MuepsProofs

open Mueps.Semimetric

/-- The distance inherited by a subset. -/
def restrict {S : Type u} (d : Distance S) (A : Set S) : Distance A :=
  fun x y => d x.val y.val

/-- A nonempty subset inherits the semimetric laws. -/
lemma restrict_isSemimetric {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (A : Set S) (hA : A.Nonempty) : IsSemimetric (restrict d A) := by
  refine ⟨hA.to_subtype, ?_, ?_⟩
  · intro x y
    exact (hd.2.1 x.val y.val).trans Subtype.val_inj
  · intro x y
    exact hd.2.2 x.val y.val

end MuepsProofs
