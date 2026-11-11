import Lax544225.PartitionRobustness

/-!
---
title: Lemma 1 — Noncompositionality of robustness
type: lemma
---
For a semimetric space $(S,d)$, overlapping proper subsets $S_1,S_2$, and
$\mu\geq 0$, $\epsilon>0$, the following implications are false in general:

1. If only the trivial partition on $S_1$ is $(\mu,\epsilon)$-robust, then every
   $(\mu,\epsilon)$-robust partition of $S$ contains a part including $S_1$.
2. If only the trivial partitions on $S_1$ and $S_2$ are $(\mu,\epsilon)$-robust,
   then only the trivial partition on $S_1\cup S_2$ is $(\mu,\epsilon)$-robust.

# Formalization notes

The two proposed universal implications are named `RestrictionPrinciple` and
`UnionPrinciple`. Lemma 1 states that both are false. For the union principle,
the ambient carrier is the union of the two subsets. `OnlyTrivialOn d hd A μ ε`
says that the nonempty subset `A`, with the distance inherited from `d`, admits
only trivial robust partitions. It packages the inherited semimetric certificate
with local triviality; in particular, it is false for an empty subset. Concrete
spaces, radii, and partitions belong to the proof.
-/

namespace Lax544225.Noncompositionality

open scoped NNReal

open SemimetricSpace Partitions PartitionRobustness

/-- The nonempty subspace A admits only trivial (μ,ε)-robust partitions. -/
def OnlyTrivialOn {S : Type} (d : Distance S) (_hd : IsSemimetricSpace d)
    (A : Set S) (μ : ℝ≥0) (ε : ℝ>0) : Prop :=
  let dA : Distance A := fun x y => d x.val y.val
  ∃ hA : IsSemimetricSpace dA, OnlyTrivial dA hA μ ε

/-- Proposed restriction principle: local triviality forces every robust ambient
partition to contain the subset in a single part. Lemma 1 refutes this principle. -/
def RestrictionPrinciple : Prop :=
  ∀ (S : Type) (d : Distance S) (hd : IsSemimetricSpace d)
    (μ : ℝ≥0) (ε : ℝ>0) (S₁ : Set S)
    (_proper : S₁ᶜ.Nonempty)
    (_local : OnlyTrivialOn d hd S₁ μ ε)
    (P : Set (Set S)) (hP : IsPartition P)
    (_robust : MuEpsilonRobustPartition d hd P hP μ ε),
    ∃ Sᵢ ∈ P, S₁ ⊆ Sᵢ

/-- Proposed union principle: local triviality on two overlapping proper subsets
forces triviality on their union. Lemma 1 refutes this principle. -/
def UnionPrinciple : Prop :=
  ∀ (S : Type) (d : Distance S) (hd : IsSemimetricSpace d)
    (μ : ℝ≥0) (ε : ℝ>0) (S₁ S₂ : Set S)
    (_proper₁ : S₁ᶜ.Nonempty) (_proper₂ : S₂ᶜ.Nonempty)
    (_overlap : (S₁ ∩ S₂).Nonempty)
    (_cover : S₁ ∪ S₂ = Set.univ)
    (_local₁ : OnlyTrivialOn d hd S₁ μ ε)
    (_local₂ : OnlyTrivialOn d hd S₂ μ ε),
    OnlyTrivial d hd μ ε

/-- Neither the restriction principle nor the union principle holds in general. -/
axiom lemma1 : ¬ RestrictionPrinciple ∧ ¬ UnionPrinciple

end Lax544225.Noncompositionality
