/- Adapted from lax-544225, source 5d812af45275f298dec0e9e4465d6a665e95656b.
   Standalone Lean port, 18 October 2026: archive assumptions replaced by proved dependencies.
   Formalization: Clemens Kuske and Codex (OpenAI). Apache-2.0. -/

import Mueps.Definitions
import MuepsProofs.CoveringTheorem
import MuepsProofs.Basic

universe u
namespace MuepsProofs.Existence
open scoped NNReal
open Mueps Semimetric Partitions PartitionRobustness Balls CoveringConditions

lemma cut_partition {S : Type u} (A : Set S) (hA : A.Nonempty)
    (hAc : Aᶜ.Nonempty) : IsPartition ({A, Aᶜ} : Set (Set S)) := by
  classical
  apply (Basic.isPartition_iff _).mpr
  refine ⟨Set.toFinite _, ?_, ?_⟩
  · intro B hB
    rcases Set.mem_insert_iff.mp hB with rfl | hB
    · exact hA
    · simpa only [Set.mem_singleton_iff] using hB ▸ hAc
  · intro x
    by_cases hx : x ∈ A
    · refine ⟨A, ⟨by simp, hx⟩, ?_⟩
      intro B hB
      rcases Set.mem_insert_iff.mp hB.1 with rfl | hB'
      · rfl
      · have : B = Aᶜ := Set.mem_singleton_iff.mp hB'
        exact False.elim ((this ▸ hB.2) hx)
    · refine ⟨Aᶜ, ⟨by simp, hx⟩, ?_⟩
      intro B hB
      rcases Set.mem_insert_iff.mp hB.1 with rfl | hB'
      · exact False.elim (hx hB.2)
      · exact Set.mem_singleton_iff.mp hB'

lemma part_disjoint {S : Type u} {P : Set (Set S)} (hP : IsPartition P)
    {A B : Set S} (hA : A ∈ P) (hB : B ∈ P) (hne : A ≠ B) : A ⊆ Bᶜ := by
  intro x hx hxb
  exact (hP.2.pairwiseDisjoint hA hB hne).le_bot ⟨hx, hxb⟩

lemma neighborhood_mono {S : Type u} (d : Distance S) (hd : IsSemimetric d) (r : ℝ≥0)
    {A B : Set S} (h : A ⊆ B) : neighborhood d hd A r ⊆ neighborhood d hd B r := by
  rintro x ⟨y, hy, hxy⟩
  exact ⟨y, h hy, hxy⟩

/--
Every proper cut admits a covering point if all robust partitions are trivial.

# Proof strategy

An uncovered cut and its complement form a valid two-part partition. Apply the
uncovered-to-robust characterization and contradict its forced triviality.

# Attribution

Theorem 2 of Aleksandrov and Völlinger, *Relaxing Global Classifier Robustness
on Semimetric Spaces*, supplied FSEN 2027 manuscript, p. 9.
-/
lemma trivialityToCutCovering {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (μ ε : ℝ≥0) (hε : 0 < ε) :
    OnlyTrivial d hd μ ε → EveryCutCovered d hd μ ε := by
  classical
  intro htr A hA hAc
  by_contra hn
  have hP := cut_partition A hA hAc
  have hun : Uncovered d hd ({A, Aᶜ} : Set (Set S)) μ ε := by
    intro B hB x hx hcov
    rcases Set.mem_insert_iff.mp hB with rfl | hB
    · exact hn ⟨x, Or.inl ⟨hx, hcov⟩⟩
    · have hB' : B = Aᶜ := Set.mem_singleton_iff.mp hB
      subst B
      exact hn ⟨x, Or.inr ⟨hx, by simpa using hcov⟩⟩
  have hrob := (MuepsProofs.MainResults.coveringCharacterization d hd _ hP μ ε hε).mpr hun
  have heq := htr _ hP hrob
  have hAu : A = Set.univ := by
    have hmem : A ∈ ({A, Aᶜ} : Set (Set S)) := by simp
    rw [heq] at hmem
    exact Set.mem_singleton_iff.mp hmem
  obtain ⟨x, hx⟩ := hAc
  exact hx (hAu ▸ Set.mem_univ x)

/--
Covered proper cuts exclude nontrivial robust partitions.

# Proof strategy

Use robust-to-uncovered for every part. A proper part defines a cut. A covering
on that side contradicts its uncoveredness; a covering from that part on the
other side contradicts the uncoveredness of the unique part containing the
covering point. Thus every part is the whole carrier.

# Attribution

Theorem 2 of Aleksandrov and Völlinger, *Relaxing Global Classifier Robustness
on Semimetric Spaces*, supplied FSEN 2027 manuscript, p. 9.
-/
lemma cutCoveringToTriviality {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (μ ε : ℝ≥0) (hε : 0 < ε) :
    EveryCutCovered d hd μ ε → OnlyTrivial d hd μ ε := by
  classical
  intro hcut P hP hrob
  have hun := (MuepsProofs.MainResults.coveringCharacterization d hd P hP μ ε hε).mp hrob
  have hall : ∀ A ∈ P, A = Set.univ := by
    intro A hA
    by_contra hne
    have hAc : Aᶜ.Nonempty := Set.nonempty_compl.mpr hne
    obtain ⟨x, hx⟩ := hcut A (Setoid.nonempty_of_mem_partition hP.2 hA) hAc
    rcases hx with ⟨hx, hcov⟩ | ⟨hx, hcov⟩
    · exact hun A hA x hx hcov
    · obtain ⟨B, ⟨hB, hxB⟩, _⟩ := hP.2.2 x
      have hAB : A ≠ B := by
        intro heq
        exact hx (heq ▸ hxB)
      exact hun B hB x hxB
        (hcov.trans (neighborhood_mono d hd ε (part_disjoint hP hA hB hAB)))
  change P = {Set.univ}
  apply Set.ext
  intro A
  constructor
  · intro hA
    exact Set.mem_singleton_iff.mpr (hall A hA)
  · intro hA
    have hAu : A = Set.univ := Set.mem_singleton_iff.mp hA
    obtain ⟨x⟩ := hd.1
    obtain ⟨B, ⟨hB, _⟩, _⟩ := hP.2.2 x
    simpa [hAu, hall B hB] using hB

end MuepsProofs.Existence
