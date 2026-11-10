import Lax544225.Classifier
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Setoid.Partition

/-!
---
title: Partition and Classifier Induced Partition
type: definition
---
A partition divides a set into finitely many nonempty, disjoint parts. The trivial partition has just one part containing everything. A classifier induces a partition by grouping inputs with the same label.

**Definition from the paper.**

A collection of nonempty sets $\{P_1,\dots,P_p\}$ is a **partition** of a set
$S$ if and only if

1. $\bigcup_{i\in[p]}P_i=S$, and
2. $P_i\cap P_j=\emptyset$ for all $i\neq j$.

The partition $\{S\}$ on the set $S$ is called **trivial**.

A classifier $c:S\rightarrow[n]$ induces a partition
$P^c:=\{S^c_1,S^c_2,\dots,S^c_n\}$ with

$$S^c_i:=\{x\in S\mid c(x)=i\}.$$

# Formalization notes

The family is a set of sets, so enumeration and duplicate parts are absent. Mathlib's `Setoid.IsPartition` supplies nonempty parts and unique membership. Finite families are required even when S is infinite.
-/

universe u

namespace Lax544225.Partitions

open Classifier
/-- A finite partition into nonempty parts with unique membership for every input. -/
def IsPartition {S : Type u} (P : Set (Set S)) : Prop :=
  P.Finite ∧ Setoid.IsPartition P

/-- The partition consisting of the whole carrier as its only part. -/
def IsTrivial {S : Type u} (P : Set (Set S)) : Prop := P = {Set.univ}

/-- The part assigned a particular classifier label. -/
def fiber {S : Type u} {n : ℕ} (c : Classifier S n) (i : Fin n) : Set S :=
  {x | c.label x = i}

/-- The collection of all label fibers. -/
def induced {S : Type u} {n : ℕ} (c : Classifier S n) : Set (Set S) :=
  Set.range (fiber c)

end Lax544225.Partitions
