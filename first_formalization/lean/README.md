# Lean formalization of semimetric robustness

Lean 4 formalization of Andrei Aleksandrov and Kim Völlinger's
*Relaxing Global Classifier Robustness on Semimetric Spaces*.

This package contains the definitions and complete proofs for Theorems 1–5,
Corollaries 1–3, Lemma 1 (both counterexamples), and the five constructions of
Proposition 1. The fifth construction contains both list variants.

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
- `Mueps.lean`: entry point for downstream users (`import Mueps`).
- `CheckAxioms.lean`: checks all fourteen aliases and rejects nonstandard axioms, including admitted proofs.

For example, the full proof of Theorem 1 is
`MuepsProofs.MainResults.coveringCharacterization` in
`MuepsProofs/CoveringTheorem.lean`. Its paper alias is
`Mueps.Paper.CoveringCharacterization.from_paper`:

```lean
import MuepsProofs.CoveringTheorem

open Mueps Semimetric Partitions PartitionRobustness Balls
open scoped NNReal
universe u

example {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (P : Set (Set S)) (hP : IsPartition P) (μ ε : ℝ≥0) (hε : 0 < ε) :
    Robust d hd P hP μ ε ↔
      (∀ A ∈ P, ∀ x ∈ A, ¬ ball d hd x μ ⊆ neighborhood d hd Aᶜ ε) := by
  exact MuepsProofs.MainResults.coveringCharacterization d hd P hP μ ε hε
```

| Paper result | Namespace of `from_paper` in `Mueps.Paper` |
| --- | --- |
| Theorem 1 | `CoveringCharacterization` |
| Theorem 2 | `GeneralExistence` |
| Theorem 3 | `BoundaryCoveringCharacterization` |
| Theorem 4 | `SuccessorCovering` |
| Theorem 5 | `DecompositionObstruction` |
| Corollary 1 | `BoundaryExistence` |
| Corollary 2 | `PrecisionObstruction` |
| Corollary 3 | `PartialOrderPrecisionBound` |
| Lemma 1 | `Noncompositionality` |
| Proposition 1, clauses 1–5 | `FloatAbsoluteSpace`, `FloatSquaredSpace`, `SumProductSpace`, `MaximumProductSpace`, `ListSpaces` |

The standalone package introduces no axioms or admitted proofs. The paper aliases
have the same mathematical signatures as the accepted formalization, up to the
namespace change. Formalization conventions, including closed balls, finite
partitions and singleton precision metrics, are documented with the definitions.
The existing Rocq file `../formalization.v` is a separate development.

## Provenance

Adapted on 18 October 2026 from the Lean formalization by Clemens Kuske and
Codex (OpenAI), accepted as [lax-544225](https://laxarchive.org/lax-544225/),
[source commit 5d812af45275f298dec0e9e4465d6a665e95656b](https://github.com/clemenskuske/semimetric-robustness-lax-submission/tree/5d812af45275f298dec0e9e4465d6a665e95656b).
The mathematical source and theorem-specific attribution remain in the files.
The port replaces archive statement assumptions with actual proved dependencies,
splits modules to preserve an acyclic import graph, and adds the thin paper aliases.
Licensed under the repository's Apache-2.0 license.
