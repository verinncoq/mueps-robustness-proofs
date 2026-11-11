# LAX source copy

This folder is synchronized with the maintained
[LAX source repository](https://github.com/clemenskuske/semimetric-robustness-lax-submission).
It retains the existing `lax-544225` identity; this copy is not a second submission.
The separate standalone package lives in [`../lean`](../lean).

Synchronized on 11 November 2026 from
[source commit `1f85280`](https://github.com/clemenskuske/semimetric-robustness-lax-submission/tree/1f852804ec4f54786be626ecc3b0e36853b567b8).
The source includes PDF revision 12 verification, all 18 proved claims, and
the latest Lemma 1 and Theorem 5 presentation. Archive deployment is independent
of this source copy; consult the submission record for its accepted commit.

# (μ,ε)-Robustness: Characterization, Existence, and Precision-Dependent Bounds

Lean 4 formalization of the mathematical statements in Andrei Aleksandrov,
Clemens Kuske and Kim Völlinger’s revised FSEN 2027 manuscript (TeX update received 11 November 2026).

The package contains 27 concepts: 16 definitions, six theorem concepts, three
corollaries, and two lemma concepts, including Lemma 1's two counterexamples. Each of
Proposition 1's five constructions has its own definition card and proof that
it is an ordered semimetric space. The fifth contains both list extensions, with a separate statement and proof for each.
All 18 claims are proved, with squared distance reusing absolute distance and
the list extensions reusing the product results. Supporting facts are lemmas.

Environment: Lean v4.33.0 and mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

Submission identity: **lax-544225**. The manifest requests an unlisted,
replaceable LAX draft. Unlisted content is accessible through its direct link;
this source repository is public. Registration requires a separate instruction.

This repository contains the Lean submission and the author-supplied TeX paper,
updated from the user-supplied TeX archive and revised to match the subsequent
`Bounds-12.pdf` received on 11 November 2026. Its text and rendered pages
are identical to `Bounds-11.pdf`; the compiled LAX paper matches this revision.
The paper viewer links 27 passages to the 25 paper concepts and results. The supplementary classifier–partition
and separability equivalence concepts have no PDF markers. Private working history and
unrelated formalizations are not included.

Validation:

```sh
lax build . --replay
```

Unused helper warnings are intentional: these lemmas validate the
classifier/partition and zero-relaxation definitions, the Flocq correspondence, and the revised paper’s illustrative examples
without adding public result entries.

Formalization credit: Clemens Kuske and Codex (OpenAI).
Source references are recorded in `manifest.yaml`; source code uses Apache 2.0.

Each of Theorems 1–5 is one concept with its full paper statement and one PDF
passage. Covering conditions are written directly in theorem statements; named
shorthands for these conditions are confined to the proof package.

Space-dependent definitions consistently require semimetric or ordered-semimetric
evidence. Partition robustness also requires a valid finite partition. The
definitions of classifier and partition robustness use a strictly positive
subtype for ε and a nonnegative real type for μ. Theorem statements and proofs pass their existing assumptions through these concepts;
classifier robustness uses the paper’s distance inequalities directly, with
ball characterizations in the proof package. Boundary results use the boundary of the complement directly. Subspace certificates remain proof helpers.

The proof package also translates the floating-point mathematics from the
[reference Flocq development](https://github.com/verinncoq/mueps-robustness-proofs/blob/d0d81caa28f9ffd166ffd245510c99b0db1c2962/flocq_ordered_spaces/semimetrics.v).
`FlocqBridge` maps total precision/exponent parameters and proves exact rational
embeddings agree with the existing real definitions. `FlocqStrict` proves the
strict squared-distance inequality. `FlocqExamples` checks binary64 special
values, list padding and the failure of maximum distance with ordinary pointwise
order, reusing the existing product/list construction proofs. These are
proof-side helpers and add no public claims.
This is an independent Lean proof of that mathematical model, not an import of
Rocq proofs or a port of Flocq's rounding library. The reference repository's
standalone `first_formalization/lean` package is maintained separately.

The Model Validation passage has no proof-card markers; its paper wording is
preserved. The scalar and list proofs remain available through their concepts.

Corollary 3 follows the 11 November TeX revision: singleton decomposition pieces
are allowed and contribute a zero precision bound. The proof handles them through
the general existence criterion; only nontrivial pieces need the precision bound.
Definition 11 now calls this a μ-decomposition, matching the existing Lean parameters.
The general definitions of Δ and δ retain their finite, totally ordered,
at-least-two-element domain.

The revised manuscript's real-line examples (absolute and squared distance,
including failure of the triangle inequality) are proved in `PaperExamples`.
These reuse the paper's existing concepts and remain supporting lemmas.
The unnumbered `{0,2,4,6}` illustration remains in the manuscript without a
separate Lean proof, as requested.

`ClassifierPartitionEquivalence` proves that every classifier induces a valid
partition and that its (μ,ε)-robustness is equivalent to robustness of that
partition. Both statements reuse the existing foundational lemmas. This exposes
the connection needed to apply the partition theorems to classifiers, without
changing the paper or its markers.

`PartitionSeparability` proves that ε-separation is equivalent to (0,ε)-robustness.
It combines the direct proofs from the partition definitions, independently of
Theorem 1, and has no additional PDF marker.

Lemma 1 uses `OnlyTrivialOn` in its own concept to express local triviality on
subsets. Both principles are equivalent to their previous expanded statements.
Theorem 5 names the inherited distance locally to keep its premise readable.
