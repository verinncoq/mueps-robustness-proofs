import Lax544225.Balls
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Basic

/-!
---
title: (μ,ε)-Decomposition
type: definition
---
A decomposition covers the space by pieces that contain every sufficiently nearby point of each of their members. Overlapping pieces form chains connecting any two inputs.

**Definition from the paper.**

A collection of nonempty sets $D:=\{D_1,\dots,D_p\}$ is a
**$(\mu,\epsilon)$-decomposition** of a semimetric space $(S,d)$ if and only if

1. For each $x\in D_i$, $B(x,\mu)\subseteq D_i$.
2. For each $x_1,x_2\in S$, there is a sequence of sets
   $D_{i_1},\dots,D_{i_n}\in D$ such that
   $D_{i_j}\cap D_{i_{j+1}}\neq\emptyset$ for consecutive members,
   $x_1\in D_{i_1}$, and $x_2\in D_{i_n}$.

# Formalization notes

The definition depends only on μ; ε appears in the applications. ReflTransGen encodes a finite chain, including a chain consisting of a single member. Membership of each endpoint member and each link is explicit. Finiteness concerns the family, not the sizes of its members.
-/

universe u

namespace Lax544225.Decomposition

open scoped NNReal

open Semimetric Balls
/-- A finite family of nonempty μ-closed pieces connected by overlaps. -/
def IsDecomposition {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (D : Set (Set S)) (μ : ℝ≥0) : Prop :=
  D.Finite ∧ (∀ A ∈ D, A.Nonempty) ∧
    (∀ A ∈ D, ∀ x ∈ A, ball d hd x μ ⊆ A) ∧
    (∀ x y, ∃ A ∈ D, ∃ B ∈ D, x ∈ A ∧ y ∈ B ∧
      Relation.ReflTransGen (fun C E => C ∈ D ∧ E ∈ D ∧ (C ∩ E).Nonempty) A B)

end Lax544225.Decomposition
