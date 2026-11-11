# Lean formalization of semimetric robustness

Lean 4 formalization of Andrei Aleksandrov, Clemens Kuske and Kim Völlinger's
*(μ,ε)-Robustness: Characterization, Existence, and Precision-Dependent Bounds*
(revised FSEN 2027 manuscript, `Bounds-12.pdf`, received 11 November 2026).

This package contains the definitions and complete proofs for Theorems 1–5,
Corollaries 1–3, Lemma 1 (both counterexamples), and the five constructions of
Proposition 1. The fifth construction contains both list variants.
Three supplementary results prove validity of the classifier-induced partition,
equivalence of classifier and partition robustness, and equivalence of
ε-separation and (0,ε)-robustness. All 18 public claims have complete proofs.

The supporting proofs also include the real-distance examples and the Lean
translation of the Rocq/Flocq model: exact rational embeddings, IEEE order
correspondence, strict squared-distance inequalities, and binary64 product/list
instances and examples. This translation proves the mathematical correspondence
in Lean; it does not import Rocq datatypes or kernel proofs.

## Build

Install Lean through [elan](https://github.com/leanprover/elan), then run from
this directory:

```sh
lake exe cache get
lake build
lake env lean CheckAxioms.lean
```

The toolchain and dependency lockfile pin Lean **v4.33.0** and mathlib
**db584cd6d46c92f209a44c0f1c829460d327499d**. No LAX installation or LAX
submission dependency is needed.

## Proofs and paper surface

- `Mueps/*.lean`: mathematical definitions; `Mueps/Definitions.lean` imports them.
- `MuepsProofs/*.lean`: complete proofs and supporting lemmas. Later results
  invoke earlier proved theorems directly.
- `Mueps/Paper.lean`: the paper-facing surface. Each result has its complete
  statement and a trivial proof of the form `by exact <proved result> ...`.
- `Mueps/Supplementary.lean`: thin aliases for the three supplementary equivalences,
  kept separate from the numbered paper statements.
- `Mueps.lean`: entry point for downstream users (`import Mueps`).
- `CheckAxioms.lean`: checks all eighteen public aliases and the added Flocq and real-distance lemmas, rejecting nonstandard axioms, including admitted proofs.

For example, the full proof of Theorem 1 is
`MuepsProofs.MainResults.coveringCharacterization` in
`MuepsProofs/CoveringTheorem.lean`. Its paper alias is
`Mueps.Paper.CoveringCharacterization.theorem1`:

```lean
import MuepsProofs.CoveringTheorem

open Mueps SemimetricSpace Partitions PartitionRobustness Balls
open scoped NNReal
universe u

example {S : Type u} (d : Distance S) (hd : IsSemimetricSpace d)
    (P : Set (Set S)) (hP : IsPartition P) (μ : ℝ≥0) (ε : ℝ>0) :
    MuEpsilonRobustPartition d hd P hP μ ε ↔
      (∀ A ∈ P, ∀ x ∈ A, ¬ ball d hd x μ ⊆ unionOfBalls d hd Aᶜ ε) := by
  exact MuepsProofs.MainResults.coveringCharacterization d hd P hP μ ε
```

| Paper result | Declaration in `Mueps.Paper` |
| --- | --- |
| Theorem 1 | `CoveringCharacterization.theorem1` |
| Theorem 2 | `GeneralExistence.theorem2` |
| Theorem 3 | `BoundaryCoveringCharacterization.theorem3` |
| Theorem 4 | `SuccessorCovering.theorem4` |
| Theorem 5 | `DecompositionObstruction.theorem5` |
| Corollary 1 | `BoundaryExistence.corollary1` |
| Corollary 2 | `PrecisionObstruction.corollary2` |
| Corollary 3 | `PartialOrderPrecisionBound.corollary3` |
| Lemma 1 | `Noncompositionality.lemma1` |
| Proposition 1, clause 1 | `FloatAbsoluteSpace.proposition1_absolute` |
| Proposition 1, clause 2 | `FloatSquaredSpace.proposition1_squared` |
| Proposition 1, clause 3 | `SumProductSpace.proposition1_sumProduct` |
| Proposition 1, clause 4 | `MaximumProductSpace.proposition1_maximumProduct` |
| Proposition 1, clause 5 (sum) | `ListSpaces.proposition1_sumList` |
| Proposition 1, clause 5 (maximum) | `ListSpaces.proposition1_maximumList` |

The standalone package introduces no axioms or admitted proofs. The paper aliases
have the same mathematical signatures as the synchronized LAX source, up to the
namespace change. The definitions use the paper's terminology, closed balls, nonnegative μ, and
strictly positive ε. Precision metrics require finite total orders with at least
two elements. Corollary 3 also allows singleton decomposition pieces, whose
paper precision metrics are Δᵢ = δᵢ = 0. Their bound is automatic because ε > 0;
the proof handles them through the general existence criterion and requires the
precision bound only for nontrivial pieces. `Chain` requires its endpoints
to belong to the decomposition family. Lemma 1 states the two failures abstractly;
its concrete counterexamples are confined to the proof package.
`Mueps.Noncompositionality.OnlyTrivialOn` packages local triviality on a nonempty
subspace, keeping both refuted principles short. Theorem 5 names each inherited
distance locally in its statement.
The existing Rocq file `../formalization.v` is a separate development.

## Provenance

Originally adapted on 18 October 2026 and synchronized on 11 November 2026
from the Lean formalization by Clemens Kuske and Codex (OpenAI),
[LAX submission lax-544225](https://laxarchive.org/lax-544225/),
[source commit dbdbc610628949634c5cedeaa81437b2f7ce1293](https://github.com/clemenskuske/semimetric-robustness-lax-submission/tree/dbdbc610628949634c5cedeaa81437b2f7ce1293).
This includes Corollary 3's singleton-piece convention, the simplified Lemma 1
and Theorem 5, and the three supplementary results. The supplied `Bounds-12.pdf`
has the same extracted text as `Bounds-11.pdf`; it requires no further
mathematical changes. Source synchronization does not assert that pending LAX
archive processing has finished.
The mathematical source and theorem-specific attribution remain in the files.
The port replaces archive statement assumptions with actual proved dependencies,
splits modules to preserve an acyclic import graph, and adds the thin paper aliases.
Licensed under the repository's Apache-2.0 license.
