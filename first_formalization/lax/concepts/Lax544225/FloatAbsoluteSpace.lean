import Lax544225.BinaryFloats

/-!
---
title: Absolute Floating-Point Distance
type: definition
---
The distance between two floating-point values is the absolute difference of their real embeddings. Together with the IEEE total order, it forms an ordered semimetric space.

**Definition from the paper.**

Let $\mathcal F$ and $\phi$ be the binary floating-point format and embedding defined above. Set

$$d_1(f_1,f_2):=|\phi(f_1)-\phi(f_2)|.$$

Then $(\mathcal F,<_{IEEE},d_1)$ is an ordered semimetric space, where $<_{IEEE}$ is the IEEE total order.

# Formalization notes

The format uses the paper’s single-NaN abstraction and independently defined IEEE category order.
-/

universe u

namespace Lax544225.FloatAbsoluteSpace

open BinaryFloats OrderedSemimetric
open scoped NNReal

/-- Absolute embedded distance d₁. -/
noncomputable def absDistance (F : Format) (f₁ f₂ : Value F) : ℝ≥0 :=
  Real.toNNReal (|phi F f₁ - phi F f₂|)

/-- The absolute-distance construction is an ordered semimetric space. -/
axiom proposition1_absolute (F : Format) : IsOrderedSemimetricSpace (absDistance F) (ieeeLe F)

end Lax544225.FloatAbsoluteSpace
