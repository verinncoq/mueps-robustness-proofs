/- Adapted from lax-544225, source 62ba21d994907b076c31bc2328e0c3209bd1ea17.
   Standalone Lean port, synchronized 11 November 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.FloatAbsoluteSpace

/-!
Squaring the difference of the real embeddings gives another floating-point distance. It satisfies the ordered semimetric laws with the same IEEE total order.

**Definition from the paper.**

Let $\mathcal F$ and $\phi$ be the binary floating-point format and embedding defined above. Set

$$d_2(f_1,f_2):=(\phi(f_1)-\phi(f_2))^2.$$

Then $(\mathcal F,<_{IEEE},d_2)$ is an ordered semimetric space.
-/

universe u

namespace Mueps.FloatSquaredSpace

open BinaryFloats OrderedSemimetric
open scoped NNReal

/-- Squared embedded distance d₂. -/
noncomputable def squareDistance (F : Format) (f₁ f₂ : Value F) : ℝ≥0 :=
  Real.toNNReal ((phi F f₁ - phi F f₂) ^ 2)

end Mueps.FloatSquaredSpace
