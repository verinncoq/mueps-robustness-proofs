import Mathlib.Data.Fin.Basic

/-!
---
title: Classifier
type: definition
---
A classifier assigns a class to every input, and every class occurs for at least one input.

**Definition from the paper.**

Let $S$ be a set of inputs and $[n]$ a set of classes. A **classifier** is a
total, surjective function $c:S\rightarrow[n]$.

# Formalization notes

Fin n labels the classes from 0 to n−1; adding 1 recovers the paper’s labels 1 to n. Surjectivity is retained. Existence of a classifier on a nonempty carrier implies n > 0.
-/

universe u

namespace Lax544225.Classifier

/-- A total classifier in which every label occurs. -/
structure Classifier (S : Type u) (n : ℕ) where
  /-- The label assigned to each input. -/
  label : S → Fin n
  /-- Every class has a representative. -/
  surjective : Function.Surjective label

end Lax544225.Classifier
