/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.BinaryFloats

/-!
The distance between two floating-point values is the absolute difference of their real embeddings. Together with the IEEE total order, it forms an ordered semimetric space.

**Definition from the paper.**

Let $\mathcal F$ and $\phi$ be the binary floating-point format and embedding defined above. Set

$$d_1(f_1,f_2):=|\phi(f_1)-\phi(f_2)|.$$

Then $(\mathcal F,<_{IEEE},d_1)$ is an ordered semimetric space, where $<_{IEEE}$ is the IEEE total order.

# Formalization notes

The format uses the paper’s single-NaN abstraction and independently defined IEEE category order.
-/

universe u

namespace Mueps.FloatAbsoluteSpace

open BinaryFloats OrderedSemimetric
open scoped NNReal

/-- Absolute embedded distance d₁. -/
noncomputable def absDistance (F : Format) (x y : Value F) : ℝ≥0 :=
  Real.toNNReal (|phi F x - phi F y|)


end Mueps.FloatAbsoluteSpace
