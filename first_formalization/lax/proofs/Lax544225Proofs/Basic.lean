import Lax544225.ClassifierRobustness
import Lax544225.PartitionRobustness
import Lax544225Proofs.CoveringConditions

/-! Foundational proofs for classifier fibers, coverings, and zero relaxation. -/

universe u

namespace Lax544225Proofs.Basic

open scoped NNReal
open Lax544225.Semimetric Lax544225.Classifier Lax544225.ClassifierRobustness
open Lax544225.Partitions Lax544225.PartitionRobustness Lax544225.Balls Lax544225Proofs.CoveringConditions

/-- The mathlib partition predicate preserves the finite-family formulation. -/
lemma isPartition_iff {S : Type u} (P : Set (Set S)) :
    IsPartition P ↔
      P.Finite ∧ (∀ A ∈ P, A.Nonempty) ∧ (∀ x, ∃! A, A ∈ P ∧ x ∈ A) := by
  constructor
  · rintro ⟨hfinite, hpartition⟩
    exact ⟨hfinite, fun _ hA => Setoid.nonempty_of_mem_partition hpartition hA,
      hpartition.2⟩
  · rintro ⟨hfinite, hnonempty, hunique⟩
    exact ⟨hfinite, fun h => Set.nonempty_iff_ne_empty.mp (hnonempty ∅ h) rfl, hunique⟩

lemma distance_self {S : Type u} {d : Distance S} (hd : IsSemimetric d) (x : S) :
    d x x = 0 := (hd.2.1 x x).2 rfl

lemma mem_ball_self {S : Type u} {d : Distance S} (hd : IsSemimetric d)
    (x : S) (r : ℝ≥0) : x ∈ ball d hd x r := by
  change d x x ≤ r
  rw [distance_self hd x]
  exact zero_le

lemma part_eq_of_mem {S : Type u} {P : Set (Set S)} (hP : IsPartition P)
    {A B : Set S} (hA : A ∈ P) (hB : B ∈ P) {x : S}
    (hxA : x ∈ A) (hxB : x ∈ B) : A = B :=
  Setoid.eq_of_mem_eqv_class hP.2.2 hA hxA hB hxB

lemma ball_subset_iff_not_mem_neighborhood {S : Type u} {d : Distance S}
    (hd : IsSemimetric d) (A : Set S) (x : S) (ε : ℝ≥0) :
    ball d hd x ε ⊆ A ↔ x ∉ neighborhood d hd Aᶜ ε := by
  classical
  constructor
  · intro hball hneigh
    rcases hneigh with ⟨y, hy, hxy⟩
    apply hy
    apply hball
    change d y x ≤ ε
    change d x y ≤ ε at hxy
    rw [hd.2.2 y x]
    exact hxy
  · intro hneigh y hy
    by_contra hyA
    apply hneigh
    refine ⟨y, hyA, ?_⟩
    change d x y ≤ ε
    change d y x ≤ ε at hy
    rw [hd.2.2 x y]
    exact hy

/--
Surjective classifier fibers form a finite partition.

# Proof strategy

The range of the finite label type is finite. Surjectivity supplies a point in
each fiber, and the label of an input determines its unique fiber.

# Attribution

Definitions 5–6 of *Relaxing Global Classifier Robustness on Semimetric Spaces*.
-/
lemma inducedPartition {S : Type u} {n : ℕ} (c : Classifier S n) :
    IsPartition (induced c) := by
  classical
  apply (isPartition_iff _).mpr
  refine ⟨Set.finite_range (fiber c), ?_, ?_⟩
  · intro A hA
    rcases hA with ⟨i, rfl⟩
    rcases c.surjective i with ⟨x, hx⟩
    exact ⟨x, hx⟩
  · intro x
    refine ⟨fiber c (c.label x), ⟨⟨c.label x, rfl⟩, rfl⟩, ?_⟩
    intro A hA
    rcases hA.1 with ⟨i, rfl⟩
    have hx : c.label x = i := hA.2
    rw [hx]

/--
Relaxed classifier robustness induces robustness of its fiber partition.

# Proof strategy

Choose the same robust center and the fiber of the input. Symmetry gives ball
membership with the partition convention, and equal labels put its ε-ball in
the same fiber.

# Attribution

Definitions 4 and 8 of the source paper.
-/
lemma classifierToPartition {S : Type u} {n : ℕ} (d : Distance S)
    (hd : IsSemimetric d) (c : Classifier S n) (μ ε : ℝ≥0) (_hε : 0 < ε) :
    RelaxedRobust d hd c μ ε → Robust d hd (induced c) (inducedPartition c) μ ε := by
  intro hc x
  rcases hc x with ⟨x', hdist, hlabel, hlocal⟩
  refine ⟨x', ?_, fiber c (c.label x), ⟨c.label x, rfl⟩, rfl, ?_⟩
  · exact hdist
  · intro y hy
    exact (hlocal y hy).trans hlabel.symm

/--
Robustness of the fiber partition gives relaxed classifier robustness.

# Proof strategy

Choose the partition's center and fiber. The center belongs to its own closed
ball, so it has the input's label; every point of the ball has that label too.

# Attribution

Definitions 4 and 8 of the source paper.
-/
lemma partitionToClassifier {S : Type u} {n : ℕ} (d : Distance S)
    (hd : IsSemimetric d) (c : Classifier S n) (μ ε : ℝ≥0) (_hε : 0 < ε) :
    Robust d hd (induced c) (inducedPartition c) μ ε → RelaxedRobust d hd c μ ε := by
  intro hP x
  rcases hP x with ⟨x', hdist, A, hA, hx, hball⟩
  rcases hA with ⟨i, rfl⟩
  have hx' : c.label x' = i := hball (mem_ball_self hd x' ε)
  refine ⟨x', ?_, hx.trans hx'.symm, ?_⟩
  · exact hdist
  · intro y hy
    exact (hball hy).trans hx'.symm

/--
Zero relaxation implies global classifier robustness.

# Proof strategy

The center's distance is zero, so semimetric separation identifies it with the
input. Its local robustness is therefore the required local robustness.

# Attribution

The zero-relaxation observation in Section 2 of the source paper.
-/
lemma zeroToGlobal {S : Type u} {n : ℕ} (d : Distance S)
    (hd : IsSemimetric d) (c : Classifier S n) (ε : ℝ≥0) (_hε : 0 < ε) :
    RelaxedRobust d hd c 0 ε → GloballyRobust d hd c ε := by
  intro h x
  rcases h x with ⟨x', hdist, _, hlocal⟩
  have hdist' : d x x' ≤ 0 := by
    rw [hd.2.2 x x']
    exact hdist
  have heq : x = x' := (hd.2.1 x x').1 (le_antisymm hdist' zero_le)
  simpa only [heq] using hlocal

/--
Global classifier robustness implies zero relaxation.

# Proof strategy

Use the input itself as the robust center, whose self-distance is zero.

# Attribution

The zero-relaxation observation in Section 2 of the source paper.
-/
lemma globalToZero {S : Type u} {n : ℕ} (d : Distance S)
    (hd : IsSemimetric d) (c : Classifier S n) (ε : ℝ≥0) (_hε : 0 < ε) :
    GloballyRobust d hd c ε → RelaxedRobust d hd c 0 ε := by
  intro h x
  exact ⟨x, (distance_self hd x).le, rfl, h x⟩

/--
Robust partitions have uncovered neighborhoods.

# Proof strategy

Unique part membership identifies the input's part with the chosen robust
part. The robust center avoids the opposite part's ε-neighborhood and witnesses
failure of coverage of the input's μ-ball.

# Attribution

The forward implication of Theorem 1 in the source paper.
-/
lemma robustToUncovered {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (P : Set (Set S)) (hP : IsPartition P) (μ ε : ℝ≥0) (_hε : 0 < ε) :
    Robust d hd P hP μ ε → Uncovered d hd P μ ε := by
  intro hrob A hA x hx hcovered
  rcases hrob x with ⟨x', hx', B, hB, hxB, hball⟩
  have hAB : A = B := part_eq_of_mem hP hA hB hx hxB
  subst B
  exact (ball_subset_iff_not_mem_neighborhood hd A x' ε).1 hball (hcovered hx')

/--
Uncovered neighborhoods yield a robust partition.

# Proof strategy

Select the input's unique part. Failure of μ-ball coverage supplies a nearby
center avoiding the opposite part's ε-neighborhood. Symmetry turns this
avoidance into containment of its ε-ball in the selected part.

# Attribution

The reverse implication of Theorem 1 in the source paper.
-/
lemma uncoveredToRobust {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (P : Set (Set S)) (hP : IsPartition P) (μ ε : ℝ≥0) (_hε : 0 < ε) :
    Uncovered d hd P μ ε → Robust d hd P hP μ ε := by
  classical
  intro hunc x
  rcases hP.2.2 x with ⟨A, ⟨hA, hxA⟩, _⟩
  rcases Set.not_subset.1 (hunc A hA x hxA) with ⟨x', hx', havoid⟩
  exact ⟨x', hx', A, hA, hxA,
    (ball_subset_iff_not_mem_neighborhood hd A x' ε).2 havoid⟩

/--
Zero-relaxation partition robustness separates distinct parts.

# Proof strategy

The nearby center must equal the input. Uniqueness identifies its robust part;
a point in a different part cannot lie in the resulting ε-ball. Closed balls
give the strict separation bound.

# Attribution

The μ=0 consequence of Theorem 1 in the source paper.
-/
lemma zeroRobustToSeparated {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (P : Set (Set S)) (hP : IsPartition P) (ε : ℝ≥0) (_hε : 0 < ε) :
    Robust d hd P hP 0 ε → Separated d hd P hP ε := by
  intro hrob A hA B hB hAB x hx y hy
  apply lt_of_not_ge
  intro hdist
  rcases hrob x with ⟨x', hx', C, hC, hxC, hball⟩
  have heq : x' = x := (hd.2.1 x' x).1 (le_antisymm hx' zero_le)
  subst x'
  have hyC : y ∈ C := by
    apply hball
    change d y x ≤ ε
    rw [hd.2.2 y x]
    exact hdist
  exact hAB ((part_eq_of_mem hP hA hC hx hxC).trans
    (part_eq_of_mem hP hB hC hy hyC).symm)

/--
Separation gives zero-relaxation partition robustness.

# Proof strategy

Use the input as its own center. Each point of its ε-ball belongs to some part;
the separation bound excludes every part different from the input's part.

# Attribution

The μ=0 consequence of Theorem 1 in the source paper.
-/
lemma separatedToZeroRobust {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (P : Set (Set S)) (hP : IsPartition P) (ε : ℝ≥0) (_hε : 0 < ε) :
    Separated d hd P hP ε → Robust d hd P hP 0 ε := by
  classical
  intro hsep x
  rcases hP.2.2 x with ⟨A, ⟨hA, hxA⟩, _⟩
  refine ⟨x, mem_ball_self hd x 0, A, hA, hxA, ?_⟩
  intro y hy
  rcases hP.2.2 y with ⟨B, ⟨hB, hyB⟩, _⟩
  by_cases hBA : B = A
  · simpa only [hBA] using hyB
  · exact False.elim ((not_lt_of_ge hy) (hsep B hB A hA hBA y hyB x hxA))

end Lax544225Proofs.Basic
