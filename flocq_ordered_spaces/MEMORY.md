# MEMORY.md — semimetrics task (Rocq + Python ordered semimetric spaces)

Working notes for redoing this task from scratch. Deliverables:
`semimetrics.v` (compiles clean with `coqc semimetrics.v`, RC=0),
`semimetrics.py` (self-tests via `python semimetrics.py`),
`test.py` (two-phase differential test, `python test.py`, ~25 min
with the squared distances — huge exact rationals; 1508 cases,
exit 0 iff all exactly equal).

## Environment (verified)

- Rocq Platform 9.1 (2026.01), `coqc` on PATH. Everything is under the
  `Stdlib.*` prefix (`From Stdlib Require Import ...`), plus `From Flocq ...`.
- Flocq **4.2.2, restructured**: there is no `Fappli_IEEE` anymore. Use
  `From Flocq Require Import IEEE754.BinarySingleNaN.` The float type is
  `binary_float prec emax` with a **single NaN** constructor:
  `B754_zero s | B754_infinity s | B754_nan | B754_finite s m e : bounded prec emax m e = true -> ...`.
  `SpecFloat` (bounded, canonical_mantissa, fexp, emin, Zdigits2) lives in
  **Stdlib** `Floats.SpecFloat` (a.k.a. Corelib.Floats.SpecFloat).
- binary64 = `prec 53, emax 1024`; `SpecFloat.emin prec emax = 3 - emax - prec`
  = **-1074**. Finite exponent range: `emin <= e <= emax - prec = 971`.
- Sign convention: **s = true means negative** (like Flocq `cond_Zopp`);
  `Bsign B754_nan = false`.
- Canonical/bounded finite value (needed for `eq_refl` proofs of `bounded`):
  `0 < m < 2^prec` and `Zdigits2 m = prec` (normal) or `e = emin` (subnormal).
  In Python: `m.bit_length() == 53 or e == -1074`.
- Useful Flocq lemmas: `Bcompare_correct` (finite x,y -> Bcompare = Some
  (Rcompare (B2R x) (B2R y))); the stdlib `SFcompare` is a lexicographic
  (exponent, mantissa) comparison with sign flips — great as an R<->Z bridge.
  `Zdigits2_Zdigits` (Flocq.Core.Digits), `Zdigits_correct radix2`,
  `Z.max_spec`, `eqbool_irrelevance` (Flocq.Core.Zaux, for proof irrelevance
  of the `bounded ... = true` arguments).

## Design of semimetrics.v (what is proven)

- `ordered_semimetric_space` record = paper Def 2 (semimetric: nonneg,
  `d x y == 0 <-> x = y`, sym) + **Def 9 is the ANTITRIANGLE**
  (superadditivity along the order): `space_le_antitriangle :
  a <= b -> b <= c -> d a b + d b c <= d a c`. (Earlier reading had the
  ordinary triangle `d a c <= d a b + d b c` — that was WRONG; the paper
  says distances along an ordered chain are at least the sum of the
  pieces. For an order-embedding via phi this even holds with
  **equality**: `qabs_add_chained : phi a <= phi b -> phi b <= phi c ->
  |phi a - phi c| == |phi a - phi b| + |phi b - phi c|`.)
- Float example (generic Section over `prec emax`, `0 < prec`, `prec < emax`;
  instantiated as binary64 and binary32): injective embedding
  `phi : binary_float -> Q`:
  - NaN -> `2^emax + 1` (NaN largest; consistent with `Bsign nan = false`),
  - ±inf -> ±`2^emax`, -0 -> `-2^(emin-1)`, +0 -> `0`,
  - finite s m e -> `(-1)^s * m * 2^e` (exact value).
  `float_dist x y := Qabs (phi x - phi y)`. `ieee_le` = IEEE-754 totalOrder
  with single NaN on top. Main theorems: `ieee_le_phi_iff`
  (`ieee_le x y <-> phi x <= phi y`, 16 constructor cases; finite-finite via
  Bcompare/lexicographic + `qalign_*` Q<->Z alignment), `phi_inj`,
  `ieee_le_total`. `float_space` is `Defined` (transparent) so `Compute`
  reduces `binary64_dist`.
- Verified computation Examples: `d(NaN,+inf)=1`, `d(-0,+0)=2^(-1075)`,
  `d(NaN,-max)=2^1025-2^971+1`; vector examples incl. the length-mismatch
  penalty.
- Vector examples (Section over ANY space `V`, applied to `binary64_space`):
  carrier = lists of V, components past the end read as the space point
  (NaN); a **+1 penalty on length mismatch** is required for identity of
  indiscernibles (`d([nan],[nan,nan])` would otherwise be 0).
  - **l_1 vector space `vec_l1_space`**: order = pointwise `vec_le`
    (only equal lengths comparable); `vec_dist_l1` = penalty + sum.
    Antitriangle holds componentwise (`qsum_antitriangle`).
  - **l_infty vector space `vec_linf_space`**: the plain pointwise order
    **provably FAILS** the antitriangle — maxima are not superadditive.
    Verified counterexample (in the file, via `vm_compute`):
    `[1;1] <= [11;1] <= [11;8]` pointwise but
    `d_inf([1;1],[11;8]) = 10 < 10 + 7`. The construction therefore takes
    an extra parameter `Hadd` (antitriangle with equality in the base
    space, provided for binary64 by `binary64_dist_add` — `Qeq_sym` of
    `float_dist_add`) and uses the **synchronized-shift order
    `vec_le_sync`**: equal lengths + pointwise order + all component
    distances of the pair equal. Along sync chains the l_infty distance
    is exactly additive (`qmaxl_const_nonneg`). Key helper lemmas:
    `vec_comps_in` (every element of `vec_comps` is a component
    distance), `qabs_add_chained`, `qsum_antitriangle`.
  - **strictly convex example `float_sq_space` / `binary64_sq_space`**:
    same carrier, same IEEE order, but
    `float_sq_dist x y := (phi x - phi y)^2`. All other examples meet
    the antitriangle with equality; this one makes it a **strict**
    inequality on every nondegenerate chain a < b < c (gap 2*p*q > 0,
    `float_sq_antitriangle_strict`, `qsq_antitriangle_strict`;
    helper lemmas `qsq_nonneg`, `qsq_zero_iff`). Verified witness:
    `d2(1,2) + d2(2,3) = 1 + 1 < 4 = d2(1,3)`, plus
    `d2(-0,+0) = 2^-2150`, `d2(NaN,+inf) = 1`.

## Coq/Q gotchas found the hard way

- `From Stdlib Require Import Lia Lqa.` gives `lra` on Q goals (also
  understands `==` hypotheses). BUT `lra` is *flaky* on goals with
  `Qpower`-atoms (e.g. `0 < Qpower 2 e` fails; some contexts fail even when
  the goal is linear). Two robust moves:
  - prove positivity via lemmas (`Qpower_0_lt`, `Qpower_0_le`,
    `Qpower_lt_compat_l`, `Qpower_le_compat_l`) as hypotheses;
  - use the fallback chain `first [ lra | psatz Q 4 | nra ]` — it saved
    several otherwise-failing steps.
- `lia` can fail on trivial `Nat.max` goals inside big proof contexts even
  though the same shape succeeds in isolation (e.g. `i < max (length a)
  (length b)` + `length a = length b` |- `i < length a`). Deterministic
  replacement: `rewrite Hlen in Hi; rewrite Nat.max_id in Hi; rewrite
  Hlen; exact Hi`.
- After `apply` of a lemma whose conclusion is `qmaxl (vec_comps a b)`
  etc., the unifier REDUCES `vec_comps` to cons form, so a later
  `apply in_map_iff` on the hypothesis fails ("Unable to apply lemma").
  Fix: a general membership lemma (`vec_comps_in`) applied with
  **explicit** arguments (`destruct (vec_comps_in (a1::ar) (b1::br) z
  Hz)`) — conversion checking works where `_`-elaboration produces
  garbage.
- `destruct l as [|x xs]; [tac_empty | tac_cons]` — the FIRST bullet is
  the `[]` case, the SECOND is `x :: xs`. Getting this backwards makes
  `discriminate` fail with "No primitive equality found"; use explicit
  `discriminate Hab` and double-check which bullet is which.
- `{ ... }` bullet subgoals are ISOLATED: hypothesis rewrites inside one
  `{}` do not persist to sibling `{}` blocks.
- Bare numerals inside `Qeq_trans _ _ _ (H i 0 ...)` style terms
  elaborate in the ambient **Q_scope** (opened by QArith) — write
  `0%nat` for nat indices.
- `simpl in *` unfolds DEFINITIONS like `binary64_le` in the goal, so a
  later `apply binary64_le_compute` no longer matches. Use
  `cbn [nth]` (restricted unfolding) on the goal and `simpl in Hi` for
  the hypothesis.
- `Qmake` fractions are **not reduced** (`Qnum`/`Qden` can be unreduced);
  cross-checking against Python must go through `Fraction(num, den)`
  normalization.
- Setoid rewriting with `Qeq` lemmas inside hypotheses is unreliable
  ("Found no subterm matching ..." on unfolded Qeq/Qle). Prefer:
  explicit `pose proof` + `cbn [phi sign_Z] in H`-style normalization,
  `qeq_le`/`qeq_sym'`-style helpers (unfold Qeq/Qle + lia), transitivity
  chains, and `Qle_trans`/`Qplus_le_r` projections.
- `rewrite ... by lia` for `Z.pow_add_r` etc. needs nonneg side conditions
  (`0 <= b`, `0 <= c`); provide them explicitly.
- Numeric annotations in terms: wrap negative exponents in parens:
  `4503599627370496%positive (-52)%Z eq_refl` (NOT `-52%Z` — parses wrong
  under Q_scope).
- Constructor elaboration: `@BinarySingleNaN.B754_finite 53 1024 s m (e)%Z eq_refl`
  — the `eq_refl` is checked by kernel computation of `SpecFloat.bounded`.
- `Nat.eqb_sym` (not `Nat.eqb_comm`); `Pos2Z.inj_compare` (not `Z.Pos...`);
  `Z.lt_0_mul` needs explicit `Z.mul_lt_mono_pos_r` style iff-use;
  `Rcompare_not_Gt`/`Rcompare_not_Gt_inv` are in Flocq.Core.Raux.
- Bullet discipline: after `destruct x, y` on 4+4 constructors you get 16
  goals — write all 16 bullets; don't `rewrite` sign lemmas with implicit
  instantiation (give explicit arguments: `(sign_Z_true mx)`).

## semimetrics.py

- Mirrors the Rocq definitions: `Float64` (kind/sign/m/e dataclass),
  `phi`, `float_dist` (= `binary64_dist`), `float_sq_dist`
  (= `binary64_sq_dist`, the strictly convex variant),
  `float_le` (= `ieee_le`),
  `vec_dist_l1`/`vec_dist_linf` (= `binary64_l1_dist`/`binary64_linf_dist`
  incl. penalty), `vec_le` (= l_1 pointwise order) and `vec_le_sync`
  (= l_infty synchronized-shift order: pointwise + all component
  distances equal). All arithmetic exact via `fractions.Fraction`.
- Self-tests (22) mirror the Rocq `Example`s incl. the antitriangle
  equality `d(1,3) == d(1,2)+d(2,3)`, the pointwise l_infty failure
  (`10 < 10+7` on `[1;1],[11;1],[11;8]`), a sync-order chain where
  l_infty is exactly additive, and the STRICT squared antitriangle
  `d2(1,2)+d2(2,3) = 2 < 4 = d2(1,3)`.
- `Float64.of_float` maps a Python float to the Flocq representation via
  bit decomposition (any NaN -> the single NaN).

## Differential testing (test.py — how it works, how to redo)

- `python semimetrics.py` — 22 self-checks mirroring the Rocq `Example`s.
- `python test.py` — the differential test (TASK.md requires it as a file).
  It compiles `semimetrics.v` if `semimetrics.vo` is stale, then runs
  **two phases**, each of which generates a temp `difftest_gen_<phase>.v`
  (deleted afterwards, together with its build artifacts):
  1. **fixed dataset**: [NaN, +inf, -inf, +0.0, -0.0] + 17 finite floats
     (±1, 0.5, 2, -2.5, ±1e300, ±5e-324, ±min-normal, ±max-finite, ±pi,
     0.1, 42) — all 22×2 = 484 ordered scalar pairs, plus 8 fixed vector
     cases × 2 norms (same-length, length-mismatched/penalty, empty vs
     NaN, extreme swap, specials in vectors).
  2. **random generator (runs after the fixed one)**: seeded
     (`TEST_SEED` env var, default 20261004), 16 random binary64 from
     stratified raw bit patterns (sign bit, exponent field 0 / random
     0..2047 / 2047, random mantissa — so subnormals, zeros, normals,
     infinities and NaN payloads all occur; NaN payloads collapse to the
     single NaN via `of_float`), all 256 ordered pairs, plus 6 random
     vector cases (4 same-length, 2 mismatched-length) × 2 norms.
- Mechanics (the fragile bits): the gen file header must be
  `From Stdlib Require Import ZArith QArith List.` + `Import ListNotations.`
  + `From Flocq Require Import IEEE754.BinarySingleNaN.` +
  `Require Import semimetrics.` + `Open Scope Q_scope.` +
  `Set Printing Width 1000000.` (else the printed pairs wrap and the
  parser fails). Values are emitted as
  `@BinarySingleNaN.B754_finite 53 1024 s m%positive (e)%Z eq_refl`
  (**parens around negative exponents**, else misparse under Q_scope).
  Two `Compute` lines per scalar pair — `binary64_dist` and
  `binary64_sq_dist`, each as `Compute ((Qnum (...)), (Z.pos (Qden (...)))).`;
  results parsed with
  regex `=\s*\(\s*(-?\d+)%Z\s*,\s*(-?\d+)%Z\s*\)`; pairing is by emission
  order (dict/list order), so counts must match exactly. Compare with
  `Fraction(num, den)` — normalizes Rocq's **unreduced** Qmake.
- Result: **1508/1508 cases exactly equal, 0 mismatches** (984 fixed +
  524 random; every scalar pair is tested under BOTH distances). A
  separate negative control (corrupting one expected value by +1) was
  detected at the right case index, so the harness is sound.
- Runtime note: with the squared distance included, phase 1's `coqc`
  compile takes ~18 min and phase 2 ~7 min (squared extreme distances
  have ~620-digit numerators, e.g. d2(max,-max) = (2^1025-2^971+1)^2);
  run test.py with a generous timeout or in background (the internal
  per-coqc timeout is 1800 s).

## Cleanup state

`tmp/` scratch, generated `difftest_gen_*` files and `*.vo/.glob/.vok/.vos/
.aux/.lia.cache/.nra.cache/.csdp.cache` build artifacts were removed after
testing; the repo keeps only `semimetrics.v`, `semimetrics.py`, `test.py`,
this `MEMORY.md`, `TASK.md` and the PDF. (`python test.py` regenerates and
deletes its own temp files; it also recompiles `semimetrics.v` when the
`.vo` is missing or stale.)
