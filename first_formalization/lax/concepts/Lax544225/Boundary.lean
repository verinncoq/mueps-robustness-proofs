import Lax544225.Balls
import Mathlib.Order.Cover

/-!
---
title: Successor and Boundary
type: definition
---
An immediate successor is the next point in the order, with no point in between. The boundary of a subset consists of its points adjacent to points outside it; the complement has its own boundary.

**Definition from the paper.**

In a totally ordered semimetric space $(S,<,d)$, $Succ(x,y)$ holds if
$x<y$ and there is no $z$ with $x<z<y$.
For each subset $S'\subseteq S$, its **boundary** is

$$\partial S':=\{x\in S'\mid\exists y\notin S',\ Succ(x,y)\lor Succ(y,x)\},$$

and its **complement boundary** is

$$\overline{\partial}S':=\{x\notin S'\mid\exists y\in S',\ Succ(x,y)\lor Succ(y,x)\}.$$

# Formalization notes

Successor is the standard mathlib cover relation `CovBy`, with the paper's name retained as an alias.

-/

universe u

namespace Lax544225.Boundary

open scoped NNReal

open Semimetric Balls
/-- Consecutive points in a linear order. -/
abbrev Successor {S : Type u} [LinearOrder S] (x y : S) : Prop :=
  CovBy x y

/-- Points of A adjacent to its complement in the ambient order. -/
def boundary {S : Type u} [LinearOrder S] (A : Set S) : Set S :=
  {x | x ∈ A ∧ ∃ y ∈ Aᶜ, Successor x y ∨ Successor y x}

/-- Points outside A adjacent to A in the ambient order. -/
def complementBoundary {S : Type u} [LinearOrder S] (A : Set S) : Set S :=
  boundary Aᶜ

end Lax544225.Boundary
