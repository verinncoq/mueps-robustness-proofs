import Lax544225.EpsilonRobustness
import Lax544225.PartitionRobustness

/-!
---
title: Classifier–Partition Robustness Equivalence
type: theorem
---
Every classifier induces a valid finite partition into its label classes.
A classifier is $(\mu,\epsilon)$-robust if and only if its induced partition is
$(\mu,\epsilon)$-robust, for $\mu\geq0$ and $\epsilon>0$.

These statements connect the classifier definitions to the partition results,
including Corollaries 2 and 3. Surjectivity of the classifier ensures that every
class is nonempty.

# Formalization notes

The equivalence accepts a validity certificate `hP` for the induced partition;
the first statement supplies this certificate for every classifier. The result
holds for any such certificate. These are supplementary statements derived from
the paper's definitions, without additional PDF markers.
-/

universe u

namespace Lax544225.ClassifierPartitionEquivalence

open scoped NNReal
open Classifier SemimetricSpace Partitions EpsilonRobustness PartitionRobustness

/-- The label classes of every classifier form a valid finite partition. -/
axiom classifierInducedPartition_isPartition {S : Type u} {n : ℕ}
    (c : Classifier S n) : IsPartition (classifierInducedPartition c)

/-- Classifier robustness is equivalent to robustness of the induced partition. -/
axiom muEpsilonRobust_iff {S : Type u} {n : ℕ} (d : Distance S)
    (hd : IsSemimetricSpace d) (c : Classifier S n)
    (hP : IsPartition (classifierInducedPartition c)) (μ : ℝ≥0) (ε : ℝ>0) :
    MuEpsilonRobustClassifier d hd c μ ε ↔
      MuEpsilonRobustPartition d hd (classifierInducedPartition c) hP μ ε

end Lax544225.ClassifierPartitionEquivalence
