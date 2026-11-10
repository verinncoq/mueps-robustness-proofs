import Lax544225.FloatAbsoluteSpace

/-!
---
title: Squared Floating-Point Distance
type: definition
---
Squaring the difference of the real embeddings gives another floating-point distance. It satisfies the ordered semimetric laws with the same IEEE total order.

**Definition from the paper.**

Let $\mathcal F$ and $\phi$ be the binary floating-point format and embedding defined above. Set

$$d_2(f_1,f_2):=(\phi(f_1)-\phi(f_2))^2.$$

Then $(\mathcal F,<_{IEEE},d_2)$ is an ordered semimetric space.
-/

universe u

namespace Lax544225.FloatSquaredSpace

open BinaryFloats OrderedSemimetric
open scoped NNReal

/-- Squared embedded distance d₂. -/
noncomputable def squareDistance (F : Format) (x y : Value F) : ℝ≥0 :=
  Real.toNNReal ((phi F x - phi F y) ^ 2)

/-- The squared-distance construction is an ordered semimetric space. -/
axiom statement (F : Format) : IsOrdered (squareDistance F) (ieeeLe F)

end Lax544225.FloatSquaredSpace
