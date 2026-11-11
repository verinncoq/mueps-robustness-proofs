import Lax544225.ClassifierPartitionEquivalence
import Lax544225Proofs.Basic

universe u

namespace Lax544225Proofs.ClassifierPartitionEquivalence

open scoped NNReal
open Lax544225 Classifier SemimetricSpace Partitions EpsilonRobustness PartitionRobustness

/--
---
conclusion: Lax544225.ClassifierPartitionEquivalence.classifierInducedPartition_isPartition
---
Every classifier induces a valid finite partition.

# Proof strategy

Reuse the finite-label partition lemma: surjectivity makes the classes nonempty,
and each input's label determines its unique class.

# Attribution

The classifier and induced-partition definitions in Aleksandrov, Kuske and
Völlinger, *(μ,ε)-Robustness: Characterization, Existence, and Precision-Dependent Bounds*.
-/
theorem classifierInducedPartition_isPartition {S : Type u} {n : ℕ}
    (c : Classifier S n) : IsPartition (classifierInducedPartition c) :=
  Basic.inducedPartition c

/--
---
conclusion: Lax544225.ClassifierPartitionEquivalence.muEpsilonRobust_iff
---
Classifier robustness is equivalent to robustness of its induced partition.

# Proof strategy

Combine the existing two implications. A classifier's robust center gives a
monochromatic ball in its label class. Conversely, the partition's center lies
in its own ball, so it has the input's label and is locally robust.

# Attribution

The classifier and partition robustness definitions in Aleksandrov, Kuske and
Völlinger, *(μ,ε)-Robustness: Characterization, Existence, and Precision-Dependent Bounds*.
-/
theorem muEpsilonRobust_iff {S : Type u} {n : ℕ} (d : Distance S)
    (hd : IsSemimetricSpace d) (c : Classifier S n)
    (hP : IsPartition (classifierInducedPartition c)) (μ : ℝ≥0) (ε : ℝ>0) :
    MuEpsilonRobustClassifier d hd c μ ε ↔
      MuEpsilonRobustPartition d hd (classifierInducedPartition c) hP μ ε :=
  ⟨Basic.classifierToPartition d hd c μ ε, Basic.partitionToClassifier d hd c μ ε⟩

end Lax544225Proofs.ClassifierPartitionEquivalence
