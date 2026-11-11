/- Adapted from lax-544225, source dbdbc610628949634c5cedeaa81437b2f7ce1293.
   Standalone Lean port, synchronized 11 November 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import MuepsProofs.ClassifierPartitionEquivalence
import MuepsProofs.PartitionSeparability

/-! Supplementary equivalences connecting the paper's definitions. These do not
add numbered paper results or PDF markers. -/

universe u

namespace Mueps.ClassifierPartitionEquivalence

open scoped NNReal
open Classifier SemimetricSpace Partitions EpsilonRobustness PartitionRobustness

/-- The label classes of every classifier form a valid finite partition. -/
theorem classifierInducedPartition_isPartition {S : Type u} {n : ℕ}
    (c : Classifier S n) : IsPartition (classifierInducedPartition c) := by
  exact MuepsProofs.ClassifierPartitionEquivalence.classifierInducedPartition_isPartition c

/-- Classifier robustness is equivalent to robustness of the induced partition. -/
theorem muEpsilonRobust_iff {S : Type u} {n : ℕ} (d : Distance S)
    (hd : IsSemimetricSpace d) (c : Classifier S n)
    (hP : IsPartition (classifierInducedPartition c)) (μ : ℝ≥0) (ε : ℝ>0) :
    MuEpsilonRobustClassifier d hd c μ ε ↔
      MuEpsilonRobustPartition d hd (classifierInducedPartition c) hP μ ε := by
  exact MuepsProofs.ClassifierPartitionEquivalence.muEpsilonRobust_iff d hd c hP μ ε

end Mueps.ClassifierPartitionEquivalence

namespace Mueps.PartitionSeparability

open scoped NNReal
open SemimetricSpace Partitions PartitionRobustness

/-- A partition is ε-separated if and only if it is (0,ε)-robust. -/
theorem separated_iff_robust_zero {S : Type u} (d : Distance S)
    (hd : IsSemimetricSpace d) (P : Set (Set S)) (hP : IsPartition P) (ε : ℝ>0) :
    Separated d hd P hP (ε : ℝ≥0) ↔ MuEpsilonRobustPartition d hd P hP 0 ε := by
  exact MuepsProofs.PartitionSeparability.separated_iff_robust_zero d hd P hP ε

end Mueps.PartitionSeparability

