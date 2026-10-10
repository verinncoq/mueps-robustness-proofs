(** * semimetrics.v

    Formalization of (ordered) semimetric spaces as defined in:

      "Relaxing Global Classifier Robustness on Semimetric Spaces"
      (FSEN 2027; in this repository as a PDF).

    In that paper:

      - Definition 2 (Semimetric Space): a pair (S, d) of a nonempty set S
        and a function d : S * S -> R>=0 such that for all x, y in S,
          d(x, y) = 0  <->  x = y   (identity of indiscernibles)
          d(x, y) = d(y, x)         (symmetry)
        (no triangle inequality is required - hence "semi").

      - Definition 9 (Ordered Semimetric Space): a tuple (S, <, d) where <
        is a (partial) order and d is a distance function such that (S, d)
        is a semimetric space and additionally, for all a <= b <= c in S:
          d(a, b) + d(b, c) <= d(a, c)   (superadditivity along the
        order; we call it the "antitriangle").  For the usual distance
        |x - y| on an ordered set it holds with equality.

    In this file the codomain of d is the rationals [Q] instead of R>=0.

    The float examples are built on Flocq's BinarySingleNaN.binary_float
    (IEEE-754 binary floats with a single NaN datum), ordered by the
    IEEE-754 total order [ieee_le] (totalOrder) extended to NaN, and with
    distances induced by the injective embedding [phi] into Q:

      phi (B754_nan)            = 2^emax + 1            (NaN: largest)
      phi (B754_infinity true)  = -2^emax               (-oo)
      phi (B754_infinity false) = 2^emax                (+oo)
      phi (B754_zero true)      = -2^(emin-1)           (-0)
      phi (B754_zero false)     = 0                      (+0)
      phi (B754_finite s m e _) = (-1)^s * m * 2^e       (exact value)

    where prec, emax are the Flocq format parameters and
    emin = 3 - emax - prec (Flocq/SpecFloat convention; e.g. binary64:
    prec = 53, emax = 1024, emin = -1074).  The theorem
    [ieee_le_phi_iff] proves that this order is exactly the IEEE total
    order
      -oo < (negative floats, then -0 < +0) < (positive floats) < +oo < NaN
    (the single Flocq NaN plays the role of the *positive* NaN - Flocq's
    Bsign B754_nan = false - i.e. it is the largest element), as long as
    the format satisfies prec < emax, which every IEEE format does.

    The distance is d(x, y) = |phi x - phi y|.  On finite floats of one
    sign class this is the usual |x - y|; the distance also handles the
    non-numeric data (-oo, +oo, NaN) and the signed zeros exactly, e.g.
    d(-0, +0) = 2^(emin-1) (tiny but positive, keeping the identity of
    indiscernibles) and d(NaN, +oo) = 1.

    On vectors (lists of floats) we build the l_infty- and l_1-like
    ordered semimetric spaces: the order is the pointwise (partial)
    order and the distances are (essentially) max_i d(x_i,y_i) and
    sum_i d(x_i,y_i); a +1 length-mismatch penalty keeps the identity of
    indiscernibles (padding with the space point - NaN - is otherwise
    indistinguishable from a NaN component).

    Everything is proved: the record fields of each example are the
    paper's axioms, so [binary64_space], [binary32_space],
    [binary64_l1_space] and [binary64_linf_space] are verified ordered
    semimetric spaces over Q-valued distances. *)

From Stdlib Require Import ZArith Lia Lqa.
From Stdlib Require Import QArith QArith_base Qpower Qabs.
From Stdlib Require Import List Floats.SpecFloat Reals.
Import ListNotations.
From Flocq Require Import Core.
From Flocq Require Import IEEE754.BinarySingleNaN.

Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(** * Ordered semimetric spaces over Q (paper Definitions 2 and 9) *)

Record ordered_semimetric_space : Type :=
  {
    space_carrier : Type;
    space_point : space_carrier;                          (* nonempty witness *)
    space_le : space_carrier -> space_carrier -> Prop;    (* (partial) order *)
    space_dist : space_carrier -> space_carrier -> Q;     (* distance *)
    (* order laws *)
    space_le_refl : forall x, space_le x x;
    space_le_trans : forall x y z, space_le x y -> space_le y z -> space_le x z;
    space_le_antisym : forall x y, space_le x y -> space_le y x -> x = y;
    (* semimetric laws (Q-valued distance) *)
    space_dist_nonneg : forall x y, 0 <= space_dist x y;
    space_dist_zero : forall x y, space_dist x y == 0 <-> x = y;
    space_dist_sym : forall x y, space_dist x y == space_dist y x;
    (* antitriangle law of Definition 9: for a <= b <= c the distance
       of the outer pair is at least the sum of the two legs *)
    space_le_antitriangle : forall a b c,
      space_le a b -> space_le b c ->
      space_dist a b + space_dist b c <= space_dist a c
  }.

(** ** Arithmetic in Q used throughout *)

Lemma qabs_zero_iff : forall x, Qabs x == 0 <-> x == 0.
Proof.
  intros x. split.
  - intros H.
    assert (Hx : x <= 0).
    { apply (Qle_trans x (Qabs x) 0).
      - apply Qle_Qabs.
      - rewrite H. apply Qle_refl. }
    pose proof (Qabs_neg x Hx) as H2.
    rewrite H in H2.
    symmetry in H2.
    rewrite <- (Qopp_involutive x).
    rewrite H2.
    reflexivity.
  - intros H. rewrite H. apply Qabs_pos, Qle_refl.
Qed.

Lemma qabs_injZ : forall z : Z, Qabs (inject_Z z) == inject_Z (Z.abs z).
Proof. intros z. destruct z as [|p|p]; reflexivity. Qed.

Lemma qdiff_zero : forall a b, a - b == 0 -> a == b.
Proof.
  intros a b H. transitivity (a - b + b).
  - ring.
  - rewrite H. ring.
Qed.

(** For p <= q <= r the rational distance is additive along the chain:
    |p - r| == |p - q| + |q - r|.  This is the antitriangle of
    Definition 9 with equality. *)
Lemma qabs_add_chained :
  forall a b c : Q, a <= b -> b <= c ->
  Qabs (a - c) == Qabs (a - b) + Qabs (b - c).
Proof.
  intros a b c Hab Hbc.
  assert (Hac : a <= c) by (apply (Qle_trans a b c); assumption).
  assert (Hle0 : forall u v : Q, u <= v -> (u - v <= 0)%Q).
  { intros u v Huv.
    apply (Qle_trans _ (v + - v)%Q).
    - apply Qplus_le_compat; [exact Huv | apply Qle_refl].
    - rewrite Qplus_opp_r. apply Qle_refl. }
  rewrite (Qabs_neg (a - c)) by (apply Hle0; exact Hac).
  rewrite (Qabs_neg (a - b)) by (apply Hle0; exact Hab).
  rewrite (Qabs_neg (b - c)) by (apply Hle0; exact Hbc).
  ring.
Qed.

Lemma qsq_zero_iff : forall x : Q, x * x == 0 <-> x == 0.
Proof.
  intros x. split.
  - intros H.
    destruct (Qlt_le_dec x 0) as [Hx | Hx].
    + assert (Hpos : (0 < x * x)%Q).
      { assert (Hn : (x * x == - x * - x)%Q) by ring.
        rewrite Hn. apply Qmult_lt_0_compat; lra. }
      lra.
    + destruct (Qle_lt_or_eq 0 x Hx) as [Hx2 | Hx2].
      * assert (Hpos : (0 < x * x)%Q)
          by (apply Qmult_lt_0_compat; exact Hx2).
        lra.
      * apply Qeq_sym. exact Hx2.
  - intros H. rewrite H. ring.
Qed.

Lemma qsq_nonneg : forall x : Q, (0 <= x * x)%Q.
Proof.
  intros x. destruct (Qlt_le_dec x 0) as [Hx | Hx].
  - assert (Hn : (x * x == - x * - x)%Q) by ring.
    rewrite Hn. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

(** The SQUARED difference satisfies the antitriangle of Definition 9
    as well, and STRICTLY whenever both steps of the chain are
    nondegenerate: for p, q <= 0 the gap between (p+q)^2 and p^2+q^2
    is 2*p*q, which is > 0 exactly when p < 0 and q < 0. *)
Lemma qsq_antitriangle : forall p q : Q, (p <= 0)%Q -> (q <= 0)%Q ->
  (p * p + q * q <= (p + q) * (p + q))%Q.
Proof.
  intros p q Hp Hq.
  assert (Hpq : (0 <= p * q)%Q).
  { assert (Hn : (p * q == - p * - q)%Q) by ring.
    rewrite Hn. apply Qmult_le_0_compat; lra. }
  assert (Heq : ((p + q) * (p + q)
                 == p * p + 2 * p * q + q * q)%Q) by ring.
  rewrite Heq. lra.
Qed.

Lemma qsq_antitriangle_strict : forall p q : Q, (p < 0)%Q -> (q < 0)%Q ->
  (p * p + q * q < (p + q) * (p + q))%Q.
Proof.
  intros p q Hp Hq.
  assert (Hpq : (0 < p * q)%Q).
  { assert (Hn : (p * q == - p * - q)%Q) by ring.
    rewrite Hn. apply Qmult_lt_0_compat; lra. }
  assert (Heq : ((p + q) * (p + q)
                 == p * p + 2 * p * q + q * q)%Q) by ring.
  rewrite Heq. lra.
Qed.

Lemma qnot_le_of_lt : forall x y, x < y -> ~ (y <= x).
Proof.
  intros x y Hxy Hyx.
  apply (Qlt_irrefl x). apply (Qlt_le_trans x y x Hxy Hyx).
Qed.

Lemma qle_abs_neg : forall x : Q, (- x <= Qabs x)%Q.
Proof.
  intros x. pose proof (Qle_Qabs (- x)) as H.
  assert (E : (Qabs (- x) == Qabs x)%Q) by (apply Qabs_opp).
  lra.
Qed.

Lemma qeq_le : forall a b : Q, (a == b)%Q -> (a <= b)%Q.
Proof. intros a b H. unfold Qeq, Qle in *. lia. Qed.

Lemma qeq_sym' : forall a b : Q, (a == b)%Q -> (b == a)%Q.
Proof. intros a b H. unfold Qeq in *. lia. Qed.

(** ** The generic construction: an injective map into Q.

    If [phi : X -> Q] is injective, then ordering X by [phi] and setting
    d(x,y) = |phi x - phi y| yields an ordered semimetric space with a
    total order.  This is the arithmetic skeleton reused (through
    [qabs_add_chained]) by all the concrete examples below. *)

Section Embedding.
  Variables (X : Type) (x0 : X) (phi : X -> Q).
  Hypothesis phi_inj : forall x y, phi x == phi y -> x = y.

  Definition phi_le x y := (phi x <= phi y)%Q.
  Definition phi_dist x y := Qabs (phi x - phi y).

  Lemma phi_space : ordered_semimetric_space.
  Proof.
    refine {| space_carrier := X ; space_point := x0 ;
              space_le := phi_le ; space_dist := phi_dist |}.
    - intros x. apply Qle_refl.
    - intros x y z. apply Qle_trans.
    - intros x y H1 H2. apply phi_inj, Qle_antisym; assumption.
    - intros x y. apply Qabs_nonneg.
    - intros x y. split.
      + intros H. apply phi_inj, qdiff_zero, qabs_zero_iff.
        exact H.
      + intros ->. unfold phi_dist.
        assert (Hz : (phi y - phi y == 0)%Q) by ring.
        rewrite Hz. apply Qabs_pos, Qle_refl.
    - intros x y. unfold phi_dist. rewrite Qabs_Qminus. reflexivity.
    - intros a b c Hab Hbc. unfold phi_dist.
      apply qeq_le. apply qeq_sym'.
      apply qabs_add_chained; assumption.
  Defined.
End Embedding.

(* ------------------------------------------------------------------ *)
(** * Q <-> Z alignment machinery

    A number of the form [inject_Z a * 2^e] is compared with
    [inject_Z b * 2^f] by shifting both sides to nonnegative exponents,
    after which the comparison is an integer comparison between
    [a * 2^(e+K)] and [b * 2^(f+K)], K := max 0 (-e) + max 0 (-f). *)

Lemma q2_neq0 : ~ (2 == 0)%Q.
Proof. intros H. unfold Qeq in H. simpl in H. discriminate H. Qed.

Lemma qpow2_injZ : forall e, (0 <= e)%Z -> Qpower 2 e == inject_Z (2 ^ e).
Proof. intros e He. symmetry. apply Zpower_Qpower, He. Qed.

Lemma qpow_pos : forall e : Z, (0 < Qpower 2 e)%Q.
Proof. intros e. apply Qpower_0_lt. lra. Qed.

Lemma qpow_nonneg : forall e : Z, (0 <= Qpower 2 e)%Q.
Proof. intros e. apply Qpower_0_le. lra. Qed.

Lemma qpow_shift : forall a e k, (0 <= e + k)%Z ->
  inject_Z a * Qpower 2 e * Qpower 2 k == inject_Z (a * 2 ^ (e + k)).
Proof.
  intros a e k Hk.
  transitivity (inject_Z a * Qpower 2 (e + k)).
  - rewrite (Qpower_plus 2 e k) by exact q2_neq0.
    ring.
  - rewrite qpow2_injZ by exact Hk.
    rewrite inject_Z_mult.
    reflexivity.
Qed.

Lemma qalign_le : forall a b e f,
  (inject_Z a * Qpower 2 e <= inject_Z b * Qpower 2 f)%Q <->
  ((a * 2 ^ (e + (Z.max 0 (- e) + Z.max 0 (- f)))
    <= b * 2 ^ (f + (Z.max 0 (- e) + Z.max 0 (- f))))%Z).
Proof.
  intros a b e f.
  assert (Hk1 : (0 <= e + Z.max 0 (- e) + Z.max 0 (- f))%Z) by lia.
  assert (Hk2 : (0 <= f + Z.max 0 (- e) + Z.max 0 (- f))%Z) by lia.
  assert (Hpos : (0 < Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f)))%Q).
  { apply Qpower_0_lt. lra. }
  rewrite <- (Qmult_le_r (inject_Z a * Qpower 2 e)
              (inject_Z b * Qpower 2 f)
              (Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))) Hpos).
  assert (E1 : (inject_Z a * Qpower 2 e * Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))
             == inject_Z (a * 2 ^ (e + (Z.max 0 (- e) + Z.max 0 (- f)))))%Q)
    by (apply qpow_shift; lia).
  assert (E2 : (inject_Z b * Qpower 2 f * Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))
             == inject_Z (b * 2 ^ (f + (Z.max 0 (- e) + Z.max 0 (- f)))))%Q)
    by (apply qpow_shift; lia).
  setoid_rewrite E1. setoid_rewrite E2.
  rewrite <- Zle_Qle.
  reflexivity.
Qed.

Lemma qalign_lt : forall a b e f,
  (inject_Z a * Qpower 2 e < inject_Z b * Qpower 2 f)%Q <->
  ((a * 2 ^ (e + (Z.max 0 (- e) + Z.max 0 (- f)))
    < b * 2 ^ (f + (Z.max 0 (- e) + Z.max 0 (- f))))%Z).
Proof.
  intros a b e f.
  assert (Hk1 : (0 <= e + Z.max 0 (- e) + Z.max 0 (- f))%Z) by lia.
  assert (Hk2 : (0 <= f + Z.max 0 (- e) + Z.max 0 (- f))%Z) by lia.
  assert (Hpos : (0 < Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f)))%Q).
  { apply Qpower_0_lt. lra. }
  rewrite <- (Qmult_lt_r (inject_Z a * Qpower 2 e)
              (inject_Z b * Qpower 2 f)
              (Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))) Hpos).
  assert (E1 : (inject_Z a * Qpower 2 e * Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))
             == inject_Z (a * 2 ^ (e + (Z.max 0 (- e) + Z.max 0 (- f)))))%Q)
    by (apply qpow_shift; lia).
  assert (E2 : (inject_Z b * Qpower 2 f * Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))
             == inject_Z (b * 2 ^ (f + (Z.max 0 (- e) + Z.max 0 (- f)))))%Q)
    by (apply qpow_shift; lia).
  setoid_rewrite E1. setoid_rewrite E2.
  rewrite <- Zlt_Qlt.
  reflexivity.
Qed.

Lemma qalign_eq : forall a b e f,
  (inject_Z a * Qpower 2 e == inject_Z b * Qpower 2 f)%Q <->
  ((a * 2 ^ (e + (Z.max 0 (- e) + Z.max 0 (- f)))
    = b * 2 ^ (f + (Z.max 0 (- e) + Z.max 0 (- f))))%Z).
Proof.
  intros a b e f.
  assert (Hk1 : (0 <= e + Z.max 0 (- e) + Z.max 0 (- f))%Z) by lia.
  assert (Hk2 : (0 <= f + Z.max 0 (- e) + Z.max 0 (- f))%Z) by lia.
  assert (Hpos : (0 < Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f)))%Q).
  { apply Qpower_0_lt. lra. }
  assert (Hneq : ~ (Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f)) == 0)%Q) by lra.
  split.
  - intros H.
    assert (H' : inject_Z a * Qpower 2 e * Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))
              == inject_Z b * Qpower 2 f * Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f)))
      by (rewrite H; reflexivity).
    assert (E1 : (inject_Z a * Qpower 2 e * Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))
               == inject_Z (a * 2 ^ (e + (Z.max 0 (- e) + Z.max 0 (- f)))))%Q)
      by (apply qpow_shift; lia).
    assert (E2 : (inject_Z b * Qpower 2 f * Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))
               == inject_Z (b * 2 ^ (f + (Z.max 0 (- e) + Z.max 0 (- f)))))%Q)
      by (apply qpow_shift; lia).
    setoid_rewrite E1 in H'. setoid_rewrite E2 in H'.
    apply inject_Z_injective, H'.
  - intros H.
    assert (E1 : (inject_Z a * Qpower 2 e * Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))
               == inject_Z (a * 2 ^ (e + (Z.max 0 (- e) + Z.max 0 (- f)))))%Q)
      by (apply qpow_shift; lia).
    assert (E2 : (inject_Z b * Qpower 2 f * Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))
               == inject_Z (b * 2 ^ (f + (Z.max 0 (- e) + Z.max 0 (- f)))))%Q)
      by (apply qpow_shift; lia).
    apply (proj1 (Qmult_inj_r (inject_Z a * Qpower 2 e)
                (inject_Z b * Qpower 2 f)
                (Qpower 2 (Z.max 0 (- e) + Z.max 0 (- f))) Hneq)).
    setoid_rewrite E1. setoid_rewrite E2.
    apply (proj2 (inject_Z_injective _ _)). exact H.
Qed.

(** ** Integer power-of-two facts *)

Lemma zpow_pos : forall e, (0 <= e)%Z -> (0 < 2 ^ e)%Z.
Proof. intros e He. apply Z.pow_pos_nonneg; lia. Qed.

Lemma zmul_pow_lt_pow : forall m e E p,
  (0 < m)%Z -> (m < 2 ^ p)%Z -> (0 <= p)%Z -> (0 <= e)%Z -> (0 <= E)%Z ->
  (e <= E - p)%Z ->
  (m * 2 ^ e < 2 ^ E)%Z.
Proof.
  intros m e E p Hm Hm' Hp He HE Hle.
  assert (Hpe : (0 < 2 ^ e)%Z) by (apply zpow_pos; lia).
  assert (H1 : (m * 2 ^ e < 2 ^ p * 2 ^ e)%Z).
  { apply (proj1 (Z.mul_lt_mono_pos_r (2 ^ e) m (2 ^ p) Hpe)).
    exact Hm'. }
  rewrite <- (Z.pow_add_r 2 p e) in H1 by lia.
  assert (H2 : (2 ^ (p + e) <= 2 ^ E)%Z) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Lemma zmul_pow_ge_pow : forall m e E,
  (1 <= m)%Z -> (0 <= e)%Z -> (0 <= E)%Z -> (E <= e)%Z -> (2 ^ E <= m * 2 ^ e)%Z.
Proof.
  intros m e E Hm He HE Hle.
  assert (Hpe : (0 < 2 ^ e)%Z) by (apply zpow_pos; lia).
  assert (H1 : (1 * 2 ^ e <= m * 2 ^ e)%Z)
    by (apply (proj1 (Z.mul_le_mono_pos_r 1 m (2 ^ e) Hpe)); lia).
  rewrite Z.mul_1_l in H1.
  assert (H2 : (2 ^ E <= 2 ^ e)%Z) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

(** Key chain: for bounded (canonical) floats, a strictly larger
    exponent means a strictly larger value. *)
Lemma zmul_pow_lt_swap : forall m1 m2 E1 E2 p,
  (0 < m1)%Z -> (m1 < 2 ^ p)%Z -> (1 <= p)%Z -> (2 ^ (p - 1) <= m2)%Z ->
  (0 <= E1)%Z -> (0 <= E2)%Z -> (E1 < E2)%Z ->
  (m1 * 2 ^ E1 < m2 * 2 ^ E2)%Z.
Proof.
  intros m1 m2 E1 E2 p Hm1 Hm1' Hp Hm2 HE1 HE2 HE12.
  assert (Hb1 : (0 < 2 ^ E1)%Z) by (apply zpow_pos; lia).
  assert (Hb2 : (0 < 2 ^ E2)%Z) by (apply zpow_pos; lia).
  assert (H1 : (m1 * 2 ^ E1 < 2 ^ p * 2 ^ E1)%Z).
  { apply (proj1 (Z.mul_lt_mono_pos_r (2 ^ E1) m1 (2 ^ p) Hb1)).
    exact Hm1'. }
  rewrite <- (Z.pow_add_r 2 p E1) in H1 by lia.
  assert (H2 : (2 ^ (p + E1) <= 2 ^ ((p - 1) + E2))%Z) by (apply Z.pow_le_mono_r; lia).
  assert (H4 : (2 ^ ((p - 1) + E2) = 2 ^ (p - 1) * 2 ^ E2)%Z) by (apply Z.pow_add_r; lia).
  rewrite H4 in H2.
  assert (H3 : (2 ^ (p - 1) * 2 ^ E2 <= m2 * 2 ^ E2)%Z).
  { apply (proj1 (Z.mul_le_mono_pos_r (2 ^ (p - 1)) m2 (2 ^ E2) Hb2)). exact Hm2. }
  lia.
Qed.

Lemma zmul_pow_pos : forall m E, (0 < m)%Z -> (0 <= E)%Z -> (0 < m * 2 ^ E)%Z.
Proof.
  intros m E Hm HE.
  assert (Hpow : (0 < 2 ^ E)%Z) by (apply zpow_pos; lia).
  assert (H1 : (0 * 2 ^ E < m * 2 ^ E)%Z)
    by (apply (proj1 (Z.mul_lt_mono_pos_r (2 ^ E) 0 m Hpow)); exact Hm).
  rewrite Z.mul_0_l in H1. exact H1.
Qed.

Lemma zopp_pos_eq : forall p : positive, (Z.neg p = - Z.pos p)%Z.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * The IEEE-754 total order and the phi embedding on binary floats *)

Section FloatSpace.
  Variable prec emax : Z.
  Hypothesis Hprec : (0 < prec)%Z.
  Hypothesis Hlt : (prec < emax)%Z.

  Notation emin := (SpecFloat.emin prec emax).

  (** s = true means negative, as in Flocq's cond_Zopp. *)
  Definition sign_Z (s : bool) (m : positive) : Z :=
    if s then Z.neg m else Z.pos m.

  Lemma sign_Z_true : forall m, sign_Z true m = Z.neg m.
  Proof. reflexivity. Qed.

  Lemma sign_Z_false : forall m, sign_Z false m = Z.pos m.
  Proof. reflexivity. Qed.

  Definition phi (x : binary_float prec emax) : Q :=
    match x with
    | B754_nan => Qpower 2 emax + 1
    | B754_infinity true => - Qpower 2 emax
    | B754_infinity false => Qpower 2 emax
    | B754_zero true => - Qpower 2 (emin - 1)
    | B754_zero false => 0
    | B754_finite s m e _ => inject_Z (sign_Z s m) * Qpower 2 e
    end.

  Definition float_dist (x y : binary_float prec emax) : Q :=
    Qabs (phi x - phi y).

  (** The IEEE-754 total order on binary floats (totalOrder), with the
      single NaN as the largest element.  Finite values are ordered by
      their real value (B2R), with -0 < +0. *)
  Definition ieee_le (x y : binary_float prec emax) : Prop :=
    match x with
    | B754_nan => match y with B754_nan => True | _ => False end
    | B754_infinity sx =>
        match y with
        | B754_nan => True
        | B754_infinity sy => (sx = true) \/ (sy = false)
        | _ => (sx = true)
        end
    | B754_zero sx =>
        match y with
        | B754_nan => True
        | B754_infinity sy => (sy = false)
        | B754_zero sy => (sx = true) \/ (sy = false)
        | B754_finite sy _ _ _ => (sy = false)
        end
    | B754_finite sx _ _ _ =>
        match y with
        | B754_nan => True
        | B754_infinity sy => (sy = false)
        | B754_zero sy => (sx = true)
        | B754_finite _ _ _ _ => (B2R x <= B2R y)%R
        end
    end.

  (** ** Bounded (canonical) representations *)

  Lemma bounded_facts : forall m e, SpecFloat.bounded prec emax m e = true ->
    ((Z.pos m < 2 ^ prec)%Z /\ (emin <= e)%Z /\ (e <= emax - prec)%Z /\
     ((emin < e)%Z -> (2 ^ (prec - 1) <= Z.pos m)%Z)).
  Proof.
    intros m e Hb.
    unfold SpecFloat.bounded in Hb.
    apply andb_prop in Hb. destruct Hb as [Hc Hle].
    apply Z.leb_le in Hle.
    unfold SpecFloat.canonical_mantissa in Hc.
    apply Z.eqb_eq in Hc.
    pose proof (Zdigits2_Zdigits (Z.pos m)) as HdEq.
    pose proof (Zdigits_correct radix2 (Z.pos m)) as Hdig.
    assert (Hap : (Z.abs (Z.pos m) = Z.pos m)%Z) by reflexivity.
    rewrite Hap in Hdig.
    rewrite <- HdEq in Hdig.
    assert (Hr : (radix_val radix2 = 2)%Z) by reflexivity.
    rewrite Hr in Hdig.
    (* Zdigits2 (Zpos m) reduces definitionally to Zpos (digits2_pos m) *)
    change (SpecFloat.Zdigits2 (Z.pos m)) with (Z.pos (SpecFloat.digits2_pos m)) in Hdig.
    assert (Hd0 : (0 <= Z.pos (SpecFloat.digits2_pos m))%Z) by lia.
    unfold SpecFloat.fexp in Hc.
    set (d := Z.pos (SpecFloat.digits2_pos m)) in *.
    destruct (Z.max_spec (d + e - prec) emin) as [[Hm1 Hm2]|[Hm1 Hm2]].
    - (* subnormal-or-first-binade: max = emin, so e = emin and d <= prec *)
      rewrite Hm2 in Hc. rewrite <- Hc in Hm1. subst e.
      assert (Hdp : (d <= prec)%Z) by lia.
      assert (H2 : (2 ^ d <= 2 ^ prec)%Z) by (apply Z.pow_le_mono_r; lia).
      repeat split; lia.
    - (* normal: max = d + e - prec, so d = prec *)
      rewrite Hm2 in Hc.
      assert (Hdp : (d = prec)%Z) by lia.
      rewrite Hdp in Hdig, Hm1.
      repeat split; lia.
  Qed.

  (** ** Position of finite values inside (-2^emax, 2^emax) *)

  Lemma phi_finite_abs_lt : forall s m e (H : SpecFloat.bounded prec emax m e = true),
    (Qabs (phi (B754_finite s m e H)) < Qpower 2 emax)%Q.
  Proof.
    intros s m e H.
    pose proof (bounded_facts m e H) as [Hm [He1 [He2 Hn]]].
    cbn [phi].
    assert (Habs : Qabs (inject_Z (sign_Z s m) * Qpower 2 e)
                == inject_Z (Z.pos m) * Qpower 2 e).
    { rewrite Qabs_Qmult, qabs_injZ.
      assert (Hpp : (0 <= Qpower 2 e)%Q) by (apply qpow_nonneg).
      rewrite (Qabs_pos _ Hpp).
      destruct s; reflexivity. }
    rewrite Habs.
    rewrite <- (Qmult_1_l (Qpower 2 emax)).
    apply qalign_lt.
    rewrite Z.mul_1_l.
    apply zmul_pow_lt_pow with (p := prec); [lia | exact Hm | lia | lia | lia | lia].
  Qed.

  (** The magnitude of a finite value is at least the smallest
      subnormal 2^emin. *)
  Lemma phi_finite_abs_ge : forall s m e (H : SpecFloat.bounded prec emax m e = true),
    (Qpower 2 emin <= Qabs (phi (B754_finite s m e H)))%Q.
  Proof.
    intros s m e H.
    pose proof (bounded_facts m e H) as [Hm [He1 [He2 Hn]]].
    cbn [phi].
    assert (Habs : Qabs (inject_Z (sign_Z s m) * Qpower 2 e)
                == inject_Z (Z.pos m) * Qpower 2 e).
    { rewrite Qabs_Qmult, qabs_injZ.
      assert (Hpp : (0 <= Qpower 2 e)%Q) by (apply qpow_nonneg).
      rewrite (Qabs_pos _ Hpp).
      destruct s; reflexivity. }
    rewrite Habs.
    rewrite <- (Qmult_1_l (Qpower 2 emin)).
    apply qalign_le.
    rewrite Z.mul_1_l.
    apply zmul_pow_ge_pow; lia.
  Qed.

  Lemma phi_finite_pos : forall m e (H : SpecFloat.bounded prec emax m e = true),
    (0 < phi (B754_finite false m e H))%Q.
  Proof.
    intros m e H. cbn [phi]. rewrite sign_Z_false.
    apply Qmult_lt_0_compat.
    - change (inject_Z 0 < inject_Z (Z.pos m))%Q. rewrite <- Zlt_Qlt. lia.
    - apply qpow_pos.
  Qed.

  Lemma phi_finite_neg : forall m e (H : SpecFloat.bounded prec emax m e = true),
    (phi (B754_finite true m e H) < 0)%Q.
  Proof.
    intros m e H. cbn [phi]. rewrite sign_Z_true.
    rewrite (zopp_pos_eq m). rewrite inject_Z_opp.
    assert (Hz : (0 < inject_Z (Z.pos m) * Qpower 2 e)%Q).
    { apply Qmult_lt_0_compat.
      - change (inject_Z 0 < inject_Z (Z.pos m))%Q. rewrite <- Zlt_Qlt. lia.
      - apply qpow_pos. }
    lra.
  Qed.

  (** Convenience: the two previous facts as Qabs facts. *)
  Lemma phi_finite_nonpos : forall s m e (H : SpecFloat.bounded prec emax m e = true),
    s = true -> (phi (B754_finite s m e H) <= - Qpower 2 emin)%Q.
  Proof.
    intros s m e H Hs. subst s.
    pose proof (phi_finite_abs_ge true m e H) as Hge.
    pose proof (phi_finite_neg m e H) as Hneg.
    pose proof (Qlt_le_weak _ _ Hneg) as Hneg'.
    rewrite (Qabs_neg _ Hneg') in Hge.
    lra.
  Qed.

  (** ** The order used is the IEEE total order *)

  Lemma Rle_Rcompare_iff : forall u v : R, (u <= v)%R <-> (Rcompare u v <> Gt).
  Proof. intros; split; [apply Rcompare_not_Gt | apply Rcompare_not_Gt_inv]. Qed.

  Lemma compare_cont_eq : forall p q : positive,
    Pos.compare_cont Eq p q = (p ?= q)%positive.
  Proof.
  intros p q. rewrite Pos.compare_cont_spec. unfold Pos.switch_Eq.
  destruct (p ?= q)%positive; reflexivity.
Qed.

  Lemma pos_compare_ne_Gt_iff : forall p q : positive,
    (Pos.compare_cont Eq p q <> Gt) <-> ((Z.pos p <= Z.pos q)%Z).
  Proof.
    intros p q.
    rewrite compare_cont_eq, Pos2Z.inj_compare.
    destruct ((Z.pos p ?= Z.pos q)%Z) eqn:E.
    - apply (proj1 (Z.compare_eq_iff (Z.pos p) (Z.pos q))) in E.
      split; [intros _; lia | intros _; discriminate].
    - apply (proj1 (Z.compare_lt_iff (Z.pos p) (Z.pos q))) in E.
      split; [intros _; lia | intros _; discriminate].
    - apply (proj1 (Z.compare_gt_iff (Z.pos p) (Z.pos q))) in E.
      split.
      + intros Hc. exfalso. apply Hc. reflexivity.
      + intros Hle. exfalso. lia.
  Qed.

  (** The finite-finite case: Bcompare (Flocq's IEEE comparison)
      computes the order lexicographically on (exponent, mantissa), and
      this is equivalent both to the R comparison and to the phi
      comparison. *)
  Lemma finite_finite_iff : forall sx mx ex (Hx : SpecFloat.bounded prec emax mx ex = true)
                                     sy my ey (Hy : SpecFloat.bounded prec emax my ey = true),
    (ieee_le (B754_finite sx mx ex Hx) (B754_finite sy my ey Hy)) <->
    (phi (B754_finite sx mx ex Hx) <= phi (B754_finite sy my ey Hy))%Q.
  Proof.
    intros sx mx ex Hx sy my ey Hy.
    pose proof (bounded_facts mx ex Hx) as [Hm1 [He1 [He2 Hn1]]].
    pose proof (bounded_facts my ey Hy) as [Hm2 [He3 [He4 Hn2]]].
    cbn [ieee_le phi].
    rewrite qalign_le.
    assert (Hbc : Bcompare (B754_finite sx mx ex Hx) (B754_finite sy my ey Hy)
                = Some (Rcompare (B2R (B754_finite sx mx ex Hx))
                                 (B2R (B754_finite sy my ey Hy))))
      by (apply Bcompare_correct; reflexivity).
    assert (Hlex : Bcompare (B754_finite sx mx ex Hx) (B754_finite sy my ey Hy)
                = Some (match sx, sy with
                        | true, false => Lt
                        | false, true => Gt
                        | false, false =>
                            match (ex ?= ey)%Z with
                            | Lt => Lt | Gt => Gt
                            | Eq => Pos.compare_cont Eq mx my
                            end
                        | true, true =>
                            match (ex ?= ey)%Z with
                            | Lt => Gt | Gt => Lt
                            | Eq => CompOpp (Pos.compare_cont Eq mx my)
                            end
                        end)) by reflexivity.
    assert (Hr : Rcompare (B2R (B754_finite sx mx ex Hx)) (B2R (B754_finite sy my ey Hy))
                = match sx, sy with
                  | true, false => Lt
                  | false, true => Gt
                  | false, false =>
                      match (ex ?= ey)%Z with
                      | Lt => Lt | Gt => Gt
                      | Eq => Pos.compare_cont Eq mx my
                      end
                  | true, true =>
                      match (ex ?= ey)%Z with
                      | Lt => Gt | Gt => Lt
                      | Eq => CompOpp (Pos.compare_cont Eq mx my)
                      end
                  end) by congruence.
    rewrite (Rle_Rcompare_iff _ _), Hr.
    clear Hbc Hlex.
    destruct sx, sy.
    - (* x negative, y negative *)
      destruct ((ex ?= ey)%Z) eqn:E.
      + (* ex = ey *)
        apply (proj1 (Z.compare_eq_iff ex ey)) in E. subst ey.
        assert (Hpow : (0 < 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ex))))%Z)
          by (apply zpow_pos; lia).
        split.
        * intros Hc.
          rewrite compare_cont_eq, Pos2Z.inj_compare in Hc.
          destruct ((Z.pos mx ?= Z.pos my)%Z) eqn:E2.
          { apply (proj1 (Z.compare_eq_iff _ _)) in E2.
            rewrite (sign_Z_true mx), (sign_Z_true my), (zopp_pos_eq mx), (zopp_pos_eq my).
            apply (proj1 (Z.mul_le_mono_pos_r (- Z.pos mx) (- Z.pos my)
                     (2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ex)))) Hpow)).
            lia. }
          { exfalso. apply Hc. reflexivity. }
          { apply (proj1 (Z.compare_gt_iff _ _)) in E2.
            rewrite (sign_Z_true mx), (sign_Z_true my), (zopp_pos_eq mx), (zopp_pos_eq my).
            apply (proj1 (Z.mul_le_mono_pos_r (- Z.pos mx) (- Z.pos my)
                     (2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ex)))) Hpow)).
            lia. }
        * intros HR.
          rewrite (sign_Z_true mx), (sign_Z_true my), (zopp_pos_eq mx), (zopp_pos_eq my) in HR.
          apply (proj2 (Z.mul_le_mono_pos_r (- Z.pos mx) (- Z.pos my)
                   (2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ex)))) Hpow)) in HR.
          rewrite compare_cont_eq, Pos2Z.inj_compare.
          destruct ((Z.pos mx ?= Z.pos my)%Z) eqn:E2.
          { discriminate. }
          { exfalso. apply (proj1 (Z.compare_lt_iff _ _)) in E2. lia. }
          { discriminate. }
      + (* ex < ey *)
        apply (proj1 (Z.compare_lt_iff ex ey)) in E.
        split.
        * intros Hc. exfalso. apply Hc. reflexivity.
        * intros HR. exfalso.
          assert (Hch : (Z.pos mx * 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ey)))
                       < Z.pos my * 2 ^ (ey + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z).
          { apply zmul_pow_lt_swap with (p := prec).
            - lia.
            - exact Hm1.
            - lia.
            - apply Hn2; lia.
            - lia.
            - lia.
            - lia. }
          rewrite (sign_Z_true mx), (sign_Z_true my), (zopp_pos_eq mx), (zopp_pos_eq my) in HR. lia.
      + (* ey < ex *)
        apply (proj1 (Z.compare_gt_iff ex ey)) in E.
        split.
        * intros _.
          assert (Hch : (Z.pos my * 2 ^ (ey + (Z.max 0 (- ex) + Z.max 0 (- ey)))
                       < Z.pos mx * 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z).
          { apply zmul_pow_lt_swap with (p := prec).
            - lia.
            - exact Hm2.
            - lia.
            - apply Hn1; lia.
            - lia.
            - lia.
            - lia. }
          rewrite (sign_Z_true mx), (sign_Z_true my), (zopp_pos_eq mx), (zopp_pos_eq my). lia.
        * intros _. discriminate.
    - (* x negative, y positive *)
      split.
      * intros _.
        assert (HP : (0 < Z.pos my * 2 ^ (ey + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z)
          by (apply zmul_pow_pos; lia).
        rewrite (sign_Z_true mx), (sign_Z_false my), (zopp_pos_eq mx). lia.
      * intros _. discriminate.
    - (* x positive, y negative *)
      split.
      * intros Hc. exfalso. apply Hc. reflexivity.
      * intros HR. exfalso.
        assert (HP : (0 < Z.pos mx * 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z)
          by (apply zmul_pow_pos; lia).
        rewrite (sign_Z_false mx), (sign_Z_true my), (zopp_pos_eq my) in HR. lia.
    - (* x positive, y positive *)
      destruct ((ex ?= ey)%Z) eqn:E.
      + (* ex = ey *)
        apply (proj1 (Z.compare_eq_iff ex ey)) in E. subst ey.
        assert (Hpow : (0 < 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ex))))%Z)
          by (apply zpow_pos; lia).
        rewrite pos_compare_ne_Gt_iff.
        rewrite <- (Z.mul_le_mono_pos_r (Z.pos mx) (Z.pos my)
                    (2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ex)))) Hpow).
        reflexivity.
      + (* ex < ey *)
        apply (proj1 (Z.compare_lt_iff ex ey)) in E.
        split.
        * intros _.
          assert (Hch : (Z.pos mx * 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ey)))
                       < Z.pos my * 2 ^ (ey + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z).
          { apply zmul_pow_lt_swap with (p := prec).
            - lia.
            - exact Hm1.
            - lia.
            - apply Hn2; lia.
            - lia.
            - lia.
            - lia. }
          rewrite (sign_Z_false mx), (sign_Z_false my). lia.
        * intros _. discriminate.
      + (* ey < ex *)
        apply (proj1 (Z.compare_gt_iff ex ey)) in E.
        split.
        * intros Hc. exfalso. apply Hc. reflexivity.
        * intros HR. exfalso.
          assert (Hch : (Z.pos my * 2 ^ (ey + (Z.max 0 (- ex) + Z.max 0 (- ey)))
                       < Z.pos mx * 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z).
          { apply zmul_pow_lt_swap with (p := prec).
            - lia.
            - exact Hm2.
            - lia.
            - apply Hn1; lia.
            - lia.
            - lia.
            - lia. }
          rewrite (sign_Z_false mx), (sign_Z_false my) in HR. lia.
  Qed.

  (** Distinctness facts for finite values, used for injectivity. *)

  Lemma phi_finite_neq_zero : forall s m e (H : SpecFloat.bounded prec emax m e = true),
    ~ (phi (B754_finite s m e H) == 0)%Q.
  Proof.
    intros s m e H Heq.
    pose proof (phi_finite_abs_ge s m e H) as Hge.
    assert (Hz : (Qabs (phi (B754_finite s m e H)) == 0)%Q).
    { rewrite Heq. apply Qabs_pos, Qle_refl. }
    assert (H0 : (0 < Qpower 2 emin)%Q) by (apply qpow_pos).
    lra.
  Qed.

  Lemma phi_finite_neq_negmin : forall s m e (H : SpecFloat.bounded prec emax m e = true),
    ~ (phi (B754_finite s m e H) == - Qpower 2 (emin - 1))%Q.
  Proof.
    intros s m e H Heq.
    pose proof (phi_finite_abs_ge s m e H) as Hge.
    assert (Hqmin : (0 < Qpower 2 emin)%Q) by (apply qpow_pos).
    assert (Hqmin1 : (0 < Qpower 2 (emin - 1))%Q) by (apply qpow_pos).
    assert (Hminlt : (Qpower 2 (emin - 1) < Qpower 2 emin)%Q)
      by (apply Qpower_lt_compat_l; [lia | lra]).
    assert (Hz : (Qabs (phi (B754_finite s m e H))
               == Qabs (- Qpower 2 (emin - 1)))%Q)
      by (rewrite Heq; reflexivity).
    assert (Hq2 : (Qabs (- Qpower 2 (emin - 1)) == Qpower 2 (emin - 1))%Q).
    { transitivity (- (- Qpower 2 (emin - 1))).
      - apply Qabs_neg. lra.
      - apply Qopp_involutive. }
    lra.
  Qed.

  Lemma phi_finite_neq_inf : forall b s m e (H : SpecFloat.bounded prec emax m e = true),
    ~ (phi (B754_infinity b) == phi (B754_finite s m e H))%Q.
  Proof.
    intros b s m e H Heq.
    assert (Hqmax : (0 < Qpower 2 emax)%Q) by (apply qpow_pos).
    assert (Hit : (phi (B754_infinity true) == - Qpower 2 emax)%Q) by reflexivity.
    assert (Hif : (phi (B754_infinity false) == Qpower 2 emax)%Q) by reflexivity.
    pose proof (phi_finite_abs_lt s m e H) as Habs.
    pose proof (Qle_Qabs (phi (B754_finite s m e H))) as HleA.
    pose proof (qle_abs_neg (phi (B754_finite s m e H))) as HleA'.
    destruct b; lra.
  Qed.

  (** Injectivity of phi on finite values. *)
  Lemma phi_finite_inj : forall sx mx ex (Hx : SpecFloat.bounded prec emax mx ex = true)
                                 sy my ey (Hy : SpecFloat.bounded prec emax my ey = true),
    phi (B754_finite sx mx ex Hx) == phi (B754_finite sy my ey Hy) ->
    sx = sy /\ mx = my /\ ex = ey.
  Proof.
    intros sx mx ex Hx sy my ey Hy H.
    pose proof (bounded_facts mx ex Hx) as [Hm1 [He1 [He2 Hn1]]].
    pose proof (bounded_facts my ey Hy) as [Hm2 [He3 [He4 Hn2]]].
    cbn [phi] in H.
    apply qalign_eq in H.
    (* the two signs must agree *)
    assert (Hs : sx = sy).
    { destruct sx, sy; try reflexivity.
      - rewrite (sign_Z_true mx), (sign_Z_false my), (zopp_pos_eq mx) in H.
        assert (HA : (0 < Z.pos mx * 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z)
          by (apply zmul_pow_pos; lia).
        assert (HB : (0 < Z.pos my * 2 ^ (ey + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z)
          by (apply zmul_pow_pos; lia).
        lia.
      - rewrite (sign_Z_false mx), (sign_Z_true my), (zopp_pos_eq my) in H.
        assert (HA : (0 < Z.pos mx * 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z)
          by (apply zmul_pow_pos; lia).
        assert (HB : (0 < Z.pos my * 2 ^ (ey + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z)
          by (apply zmul_pow_pos; lia).
        lia. }
    rewrite Hs in H.
    (* the exponents must agree *)
    assert (He : ex = ey).
    { destruct (Z.lt_ge_cases ex ey) as [Hlex|Hgey].
      - exfalso.
        assert (Hnorm : (2 ^ (prec - 1) <= Z.pos my)%Z) by (apply Hn2; lia).
        assert (Hpow : (0 < 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z)
          by (apply zpow_pos; lia).
        assert (Hne : (2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ey))) <> 0)%Z)
          by (apply not_eq_sym; apply Z.lt_neq; exact Hpow).
        assert (Hsplit : (2 ^ (ey + (Z.max 0 (- ex) + Z.max 0 (- ey)))
                        = 2 ^ (ey - ex) * 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z).
        { rewrite <- (Z.pow_add_r 2 (ey - ex) (ex + (Z.max 0 (- ex) + Z.max 0 (- ey))))
            by lia.
          f_equal. lia. }
        rewrite Hsplit, Z.mul_assoc in H.
        assert (Hc : (sign_Z sy mx = sign_Z sy my * 2 ^ (ey - ex))%Z).
        { apply (proj1 (Z.mul_cancel_r (sign_Z sy mx) (sign_Z sy my * 2 ^ (ey - ex)) _ Hne)).
          exact H. }
        assert (Hbig : (2 ^ prec <= Z.pos my * 2 ^ (ey - ex))%Z).
        { assert (H2 : (2 ^ prec = 2 ^ (prec - 1) * 2 ^ 1)%Z).
          { rewrite <- (Z.pow_add_r 2 (prec - 1) 1) by lia. f_equal. lia. }
          assert (H3 : (2 ^ 1 <= 2 ^ (ey - ex))%Z) by (apply Z.pow_le_mono_r; lia).
          assert (H4 : (2 ^ (prec - 1) * 2 ^ 1 <= Z.pos my * 2 ^ (ey - ex))%Z)
            by (apply Z.mul_le_mono_nonneg; lia).
          rewrite <- H2 in H4. exact H4. }
        destruct sy.
        + rewrite (sign_Z_true mx), (sign_Z_true my), (zopp_pos_eq mx), (zopp_pos_eq my) in Hc. lia.
        + rewrite (sign_Z_false mx), (sign_Z_false my) in Hc. lia.
      - destruct (Z.lt_ge_cases ey ex) as [Hley|Hgex].
        + exfalso.
          assert (Hnorm : (2 ^ (prec - 1) <= Z.pos mx)%Z) by (apply Hn1; lia).
          assert (Hpow : (0 < 2 ^ (ey + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z)
            by (apply zpow_pos; lia).
          assert (Hne : (2 ^ (ey + (Z.max 0 (- ex) + Z.max 0 (- ey))) <> 0)%Z)
            by (apply not_eq_sym; apply Z.lt_neq; exact Hpow).
          assert (Hsplit : (2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ey)))
                          = 2 ^ (ex - ey) * 2 ^ (ey + (Z.max 0 (- ex) + Z.max 0 (- ey))))%Z).
          { rewrite <- (Z.pow_add_r 2 (ex - ey) (ey + (Z.max 0 (- ex) + Z.max 0 (- ey))))
              by lia.
            f_equal. lia. }
          rewrite Hsplit, Z.mul_assoc in H.
          assert (Hc : (sign_Z sy my = sign_Z sy mx * 2 ^ (ex - ey))%Z).
          { apply (proj1 (Z.mul_cancel_r (sign_Z sy my) (sign_Z sy mx * 2 ^ (ex - ey)) _ Hne)).
            symmetry. exact H. }
          assert (Hbig : (2 ^ prec <= Z.pos mx * 2 ^ (ex - ey))%Z).
          { assert (H2 : (2 ^ prec = 2 ^ (prec - 1) * 2 ^ 1)%Z).
            { rewrite <- (Z.pow_add_r 2 (prec - 1) 1) by lia. f_equal. lia. }
            assert (H3 : (2 ^ 1 <= 2 ^ (ex - ey))%Z) by (apply Z.pow_le_mono_r; lia).
            assert (H4 : (2 ^ (prec - 1) * 2 ^ 1 <= Z.pos mx * 2 ^ (ex - ey))%Z)
              by (apply Z.mul_le_mono_nonneg; lia).
            rewrite <- H2 in H4. exact H4. }
          destruct sy.
          * rewrite (sign_Z_true mx), (sign_Z_true my), (zopp_pos_eq mx), (zopp_pos_eq my) in Hc. lia.
          * rewrite (sign_Z_false mx), (sign_Z_false my) in Hc. lia.
        + lia. }
    subst ey.
    assert (Hpow : (0 < 2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ex))))%Z)
      by (apply zpow_pos; lia).
    assert (Hne : (2 ^ (ex + (Z.max 0 (- ex) + Z.max 0 (- ex))) <> 0)%Z)
      by (apply not_eq_sym; apply Z.lt_neq; exact Hpow).
    rewrite <- Hs in H.
    assert (Hc : (sign_Z sx mx = sign_Z sx my)%Z).
    { apply (proj1 (Z.mul_cancel_r (sign_Z sx mx) (sign_Z sx my) _ Hne)).
      exact H. }
    assert (Hmx : mx = my).
    { destruct sx.
      - rewrite (sign_Z_true mx), (sign_Z_true my) in Hc.
        injection Hc. intros. subst. reflexivity.
      - rewrite (sign_Z_false mx), (sign_Z_false my) in Hc.
        injection Hc. intros. subst. reflexivity. }
    split; [exact Hs | split; [exact Hmx | reflexivity]].
  Qed.

  (** The main theorem: [ieee_le] is the IEEE total order, and it
      coincides with the order induced by [phi]. *)
  Theorem ieee_le_phi_iff : forall x y : binary_float prec emax,
    ieee_le x y <-> (phi x <= phi y)%Q.
  Proof.
    intros x y.
    assert (Hqmax : (0 < Qpower 2 emax)%Q) by (apply qpow_pos).
    assert (Hqmin1 : (0 < Qpower 2 (emin - 1))%Q) by (apply qpow_pos).
    assert (Hmin1lt : (Qpower 2 (emin - 1) < Qpower 2 emax)%Q)
      by (apply Qpower_lt_compat_l; [unfold SpecFloat.emin; lia | lra]).
    assert (Hnan : (phi B754_nan == Qpower 2 emax + 1)%Q) by reflexivity.
    assert (Hzt : (phi (B754_zero true) == - Qpower 2 (emin - 1))%Q) by reflexivity.
    assert (Hzf : (phi (B754_zero false) == 0)%Q) by reflexivity.
    assert (Hit : (phi (B754_infinity true) == - Qpower 2 emax)%Q) by reflexivity.
    assert (Hif : (phi (B754_infinity false) == Qpower 2 emax)%Q) by reflexivity.
    assert (Hqmin : (0 < Qpower 2 emin)%Q) by (apply qpow_pos).
    assert (Hminlt : (Qpower 2 (emin - 1) < Qpower 2 emin)%Q)
      by (apply Qpower_lt_compat_l; [lia | lra]).
    destruct x as [sx|sx| |sx mx ex Hx], y as [sy|sy| |sy my ey Hy];
      cbn [ieee_le].
    (* zero-zero *)
    - destruct sx, sy.
      + split; [intros _; lra | intros _; left; reflexivity].
      + split; [intros _; lra | intros _; left; reflexivity].
      + split; [intros [H|H]; discriminate H | intros Hle; exfalso; lra].
      + split; [intros _; lra | intros _; right; reflexivity].
    (* zero-inf *)
    - destruct sx, sy.
      + split; [intros H; discriminate H | intros Hle; exfalso; lra].
      + split; [intros _; lra | intros _; reflexivity].
      + split; [intros H; discriminate H | intros Hle; exfalso; lra].
      + split; [intros _; lra | intros _; reflexivity].
    (* zero-nan *)
    - destruct sx; (split; [intros _; lra | intros _; exact I]).
    (* zero-finite *)
    - destruct sy.
      + pose proof (phi_finite_neg my ey Hy) as Hneg.
        assert (Hle : (phi (B754_finite true my ey Hy) <= - Qpower 2 emin)%Q)
          by (apply phi_finite_nonpos; reflexivity).
        destruct sx.
        { split; [intros H; discriminate H | intros Hle2; exfalso; lra]. }
        { split; [intros H; discriminate H | intros Hle2; exfalso; lra]. }
      + pose proof (phi_finite_pos my ey Hy) as Hpos.
        destruct sx.
        { split; [intros _; lra | intros _; reflexivity]. }
        { split; [intros _; lra | intros _; reflexivity]. }
    (* inf-zero *)
    - destruct sx, sy.
      + split; [intros _; lra | intros _; reflexivity].
      + split; [intros _; lra | intros _; reflexivity].
      + split; [intros H; discriminate H | intros Hle; exfalso; lra].
      + split; [intros H; discriminate H | intros Hle; exfalso; lra].
    (* inf-inf *)
    - destruct sx, sy.
      + split; [intros _; lra | intros _; left; reflexivity].
      + split; [intros _; lra | intros _; left; reflexivity].
      + split; [intros [H|H]; discriminate H | intros Hle; exfalso; lra].
      + split; [intros _; lra | intros _; right; reflexivity].
    (* inf-nan *)
    - destruct sx; (split; [intros _; lra | intros _; exact I]).
    (* inf-finite *)
    - pose proof (phi_finite_abs_lt sy my ey Hy) as Habs.
      pose proof (Qle_Qabs (phi (B754_finite sy my ey Hy))) as HleA.
      pose proof (qle_abs_neg (phi (B754_finite sy my ey Hy))) as HleA'.
      destruct sx.
      + split; [intros _; lra | intros _; reflexivity].
      + split; [intros H; discriminate H | intros Hle; exfalso; lra].
    (* nan-zero *)
    - destruct sy; (split; [intros H; destruct H | intros Hle; exfalso; lra]).
    (* nan-inf *)
    - destruct sy; (split; [intros H; destruct H | intros Hle; exfalso; lra]).
    (* nan-nan *)
    - split; [intros _; lra | intros _; exact I].
    (* nan-finite *)
    - pose proof (phi_finite_abs_lt sy my ey Hy) as Habs.
      pose proof (Qle_Qabs (phi (B754_finite sy my ey Hy))) as HleA.
      split; [intros H; destruct H | intros Hle; exfalso; lra].
    (* finite-zero *)
    - destruct sx.
      + pose proof (phi_finite_neg mx ex Hx) as Hneg.
        assert (Hle : (phi (B754_finite true mx ex Hx) <= - Qpower 2 emin)%Q)
          by (apply phi_finite_nonpos; reflexivity).
        destruct sy.
        { split; [intros _; lra | intros _; reflexivity]. }
        { split; [intros _; lra | intros _; reflexivity]. }
      + pose proof (phi_finite_pos mx ex Hx) as Hpos.
        destruct sy.
        { split; [intros H; discriminate H | intros Hle; exfalso; lra]. }
        { split; [intros H; discriminate H | intros Hle; exfalso; lra]. }
    (* finite-inf *)
    - pose proof (phi_finite_abs_lt sx mx ex Hx) as Habs.
      pose proof (Qle_Qabs (phi (B754_finite sx mx ex Hx))) as HleA.
      pose proof (qle_abs_neg (phi (B754_finite sx mx ex Hx))) as HleA'.
      destruct sy.
      + split; [intros H; discriminate H | intros Hle; exfalso; lra].
      + split; [intros _; lra | intros _; reflexivity].
    (* finite-nan *)
    - pose proof (phi_finite_abs_lt sx mx ex Hx) as Habs.
      pose proof (Qle_Qabs (phi (B754_finite sx mx ex Hx))) as HleA.
      split; [intros _; lra | intros _; exact I].
    (* finite-finite *)
    - apply finite_finite_iff.
  Qed.


  (** phi is injective, so |phi x - phi y| has the identity of
      indiscernibles.  All reasoning is done on the cbn-normalized
      (phi-free) forms; the lemmas about phi are transferred by
      conversion (apply). *)
  Theorem phi_inj : forall x y : binary_float prec emax,
    phi x == phi y -> x = y.
  Proof.
    intros x y H.
    assert (Hqmax : (0 < Qpower 2 emax)%Q) by (apply qpow_pos).
    assert (Hqmin1 : (0 < Qpower 2 (emin - 1))%Q) by (apply qpow_pos).
    assert (Hmin1lt : (Qpower 2 (emin - 1) < Qpower 2 emax)%Q)
      by (apply Qpower_lt_compat_l; [unfold SpecFloat.emin; lia | lra]).
    assert (Hqmin : (0 < Qpower 2 emin)%Q) by (apply qpow_pos).
    assert (Hminlt : (Qpower 2 (emin - 1) < Qpower 2 emin)%Q)
      by (apply Qpower_lt_compat_l; [lia | lra]).
    destruct x as [sx|sx| |sx mx ex Hx], y as [sy|sy| |sy my ey Hy].
    (* zero-zero *)
    - destruct sx, sy; try reflexivity; exfalso;
        cbn [phi sign_Z] in H; first [ lra | psatz Q 4 | nra ].
    (* zero-inf *)
    - destruct sx, sy; exfalso; cbn [phi sign_Z] in H; first [ lra | psatz Q 4 | nra ].
    (* zero-nan *)
    - exfalso; destruct sx; cbn [phi sign_Z] in H; first [ lra | psatz Q 4 | nra ].
    (* zero-finite *)
    - exfalso. destruct sx; destruct sy; cbn [phi sign_Z] in H.
      + pose proof (phi_finite_nonpos true my ey Hy (eq_refl true)) as Hle.
        cbn [phi sign_Z] in Hle. first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_pos my ey Hy) as Hpos.
        cbn [phi sign_Z] in Hpos. first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_nonpos true my ey Hy (eq_refl true)) as Hle.
        cbn [phi sign_Z] in Hle. first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_pos my ey Hy) as Hpos.
        cbn [phi sign_Z] in Hpos. first [ lra | psatz Q 4 | nra ].
    (* inf-zero *)
    - destruct sx, sy; exfalso; cbn [phi sign_Z] in H; first [ lra | psatz Q 4 | nra ].
    (* inf-inf *)
    - destruct sx, sy; try reflexivity; exfalso; cbn [phi sign_Z] in H; first [ lra | psatz Q 4 | nra ].
    (* inf-nan *)
    - exfalso; destruct sx; cbn [phi sign_Z] in H; first [ lra | psatz Q 4 | nra ].
    (* inf-finite *)
    - exfalso. destruct sx; destruct sy; cbn [phi sign_Z] in H.
      + pose proof (phi_finite_abs_lt true my ey Hy) as Habs.
        cbn [phi sign_Z] in Habs.
        pose proof (qle_abs_neg (inject_Z (Z.neg my) * Qpower 2 ey)) as Hb.
        first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_pos my ey Hy) as Hpos.
        cbn [phi sign_Z] in Hpos.
        first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_neg my ey Hy) as Hneg.
        cbn [phi sign_Z] in Hneg.
        first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_abs_lt false my ey Hy) as Habs.
        cbn [phi sign_Z] in Habs.
        pose proof (Qle_Qabs (inject_Z (Z.pos my) * Qpower 2 ey)) as Ha.
        first [ lra | psatz Q 4 | nra ].
    (* nan-zero *)
    - exfalso; destruct sy; cbn [phi sign_Z] in H; first [ lra | psatz Q 4 | nra ].
    (* nan-inf *)
    - exfalso; destruct sy; cbn [phi sign_Z] in H; first [ lra | psatz Q 4 | nra ].
    (* nan-nan *)
    - reflexivity.
    (* nan-finite *)
    - exfalso. destruct sy; cbn [phi sign_Z] in H.
      + pose proof (phi_finite_abs_lt true my ey Hy) as Habs.
        cbn [phi sign_Z] in Habs.
        pose proof (Qle_Qabs (inject_Z (Z.neg my) * Qpower 2 ey)) as Ha.
        first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_abs_lt false my ey Hy) as Habs.
        cbn [phi sign_Z] in Habs.
        pose proof (Qle_Qabs (inject_Z (Z.pos my) * Qpower 2 ey)) as Ha.
        first [ lra | psatz Q 4 | nra ].
    (* finite-zero *)
    - exfalso. destruct sx; destruct sy; cbn [phi sign_Z] in H.
      + pose proof (phi_finite_nonpos true mx ex Hx (eq_refl true)) as Hle.
        cbn [phi sign_Z] in Hle. first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_nonpos true mx ex Hx (eq_refl true)) as Hle.
        cbn [phi sign_Z] in Hle. first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_pos mx ex Hx) as Hpos.
        cbn [phi sign_Z] in Hpos. first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_pos mx ex Hx) as Hpos.
        cbn [phi sign_Z] in Hpos. first [ lra | psatz Q 4 | nra ].
    (* finite-inf *)
    - exfalso. destruct sx; destruct sy; cbn [phi sign_Z] in H.
      + pose proof (phi_finite_abs_lt true mx ex Hx) as Habs.
        cbn [phi sign_Z] in Habs.
        pose proof (qle_abs_neg (inject_Z (Z.neg mx) * Qpower 2 ex)) as Hb.
        first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_neg mx ex Hx) as Hneg.
        cbn [phi sign_Z] in Hneg.
        first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_pos mx ex Hx) as Hpos.
        cbn [phi sign_Z] in Hpos.
        first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_abs_lt false mx ex Hx) as Habs.
        cbn [phi sign_Z] in Habs.
        pose proof (Qle_Qabs (inject_Z (Z.pos mx) * Qpower 2 ex)) as Ha.
        first [ lra | psatz Q 4 | nra ].
    (* finite-nan *)
    - exfalso. destruct sx; cbn [phi sign_Z] in H.
      + pose proof (phi_finite_abs_lt true mx ex Hx) as Habs.
        cbn [phi sign_Z] in Habs.
        pose proof (Qle_Qabs (inject_Z (Z.neg mx) * Qpower 2 ex)) as Ha.
        first [ lra | psatz Q 4 | nra ].
      + pose proof (phi_finite_abs_lt false mx ex Hx) as Habs.
        cbn [phi sign_Z] in Habs.
        pose proof (Qle_Qabs (inject_Z (Z.pos mx) * Qpower 2 ex)) as Ha.
        first [ lra | psatz Q 4 | nra ].
    (* finite-finite *)
    - apply phi_finite_inj in H.
      destruct H as [Hs [Hm He]].
      revert Hx Hy. rewrite Hs, Hm, He. intros Hx Hy.
      f_equal. apply eqbool_irrelevance.
  Qed.

  (** The order is total. *)
  Theorem ieee_le_total : forall x y : binary_float prec emax,
    ieee_le x y \/ ieee_le y x.
  Proof.
    intros x y.
    destruct (Qlt_le_dec (phi x) (phi y)) as [H|H].
    - left. apply (proj2 (ieee_le_phi_iff x y)), Qlt_le_weak, H.
    - right. apply (proj2 (ieee_le_phi_iff y x)), H.
  Qed.

  (** The ordered semimetric space of binary floats, with the IEEE
      total order and the phi-induced distance. *)
  Definition float_space : ordered_semimetric_space.
  Proof.
    refine {| space_carrier := binary_float prec emax ;
              space_point := B754_nan ;
              space_le := ieee_le ;
              space_dist := float_dist |}.
    - intros x. apply (proj2 (ieee_le_phi_iff x x)), Qle_refl.
    - intros x y z Hxy Hyz.
      apply (proj2 (ieee_le_phi_iff x z)).
      apply (Qle_trans (phi x) (phi y) (phi z)).
      + apply (proj1 (ieee_le_phi_iff x y)), Hxy.
      + apply (proj1 (ieee_le_phi_iff y z)), Hyz.
    - intros x y Hxy Hyx.
      apply phi_inj, Qle_antisym.
      + apply (proj1 (ieee_le_phi_iff x y)), Hxy.
      + apply (proj1 (ieee_le_phi_iff y x)), Hyx.
    - intros x y. unfold float_dist. apply Qabs_nonneg.
    - intros x y. unfold float_dist. split.
      + intros H. apply phi_inj, qdiff_zero, qabs_zero_iff.
        exact H.
      + intros ->. unfold float_dist.
        assert (Hz : (phi y - phi y == 0)%Q) by ring.
        rewrite Hz. apply Qabs_pos, Qle_refl.
    - intros x y. unfold float_dist. rewrite Qabs_Qminus. reflexivity.
    - intros a b c Hab Hbc. unfold float_dist.
      apply qeq_le. apply qeq_sym'. apply qabs_add_chained.
      + apply (proj1 (ieee_le_phi_iff a b)), Hab.
      + apply (proj1 (ieee_le_phi_iff b c)), Hbc.
  Defined.

  (** On the float space the antitriangle of Definition 9 holds with
      EQUALITY: for a <= b <= c, d(a,c) = d(a,b) + d(b,c).  This
      additivity is what makes the l_infty vector space over floats an
      ordered semimetric space (see the VectorSpace section). *)
  Theorem float_dist_add : forall a b c : binary_float prec emax,
    ieee_le a b -> ieee_le b c ->
    float_dist a b + float_dist b c == float_dist a c.
  Proof.
    intros a b c Hab Hbc. unfold float_dist.
    apply qeq_sym'. apply qabs_add_chained.
    - apply (proj1 (ieee_le_phi_iff a b)), Hab.
    - apply (proj1 (ieee_le_phi_iff b c)), Hbc.
  Qed.

  (** ** A strictly convex example: squaring the phi-difference

      Not every ordered semimetric space realizes the antitriangle of
      Definition 9 with equality.  Squaring the phi-difference,

        d2(x, y) = (phi x - phi y)^2,

      gives another ordered semimetric space on the same carrier and
      the same IEEE-754 total order, and there the antitriangle is a
      STRICT inequality on every chain a < b < c: with
      p = phi b - phi a > 0 and q = phi c - phi b > 0,

        d2(a,c) = (p + q)^2 = p^2 + q^2 + 2 p q > p^2 + q^2,
                = d2(a,b) + d2(b,c).

      The gap 2*p*q vanishes exactly on degenerate chains. *)

  Definition float_sq_dist (x y : binary_float prec emax) : Q :=
    (phi x - phi y) * (phi x - phi y).

  Lemma float_sq_dist_nonneg : forall x y, (0 <= float_sq_dist x y)%Q.
  Proof.
    intros x y. unfold float_sq_dist. apply qsq_nonneg.
  Qed.

  Theorem float_sq_antitriangle :
    forall a b c : binary_float prec emax,
    ieee_le a b -> ieee_le b c ->
    (float_sq_dist a b + float_sq_dist b c <= float_sq_dist a c)%Q.
  Proof.
    intros a b c Hab Hbc.
    apply (proj1 (ieee_le_phi_iff a b)) in Hab.
    apply (proj1 (ieee_le_phi_iff b c)) in Hbc.
    unfold float_sq_dist.
    assert (Hac : (phi a - phi c
                   == (phi a - phi b) + (phi b - phi c))%Q) by ring.
    rewrite Hac.
    apply qsq_antitriangle; lra.
  Qed.

  (** The strict version: on a nondegenerate chain a < b < c the
      antitriangle of Definition 9 is a strict inequality. *)
  Theorem float_sq_antitriangle_strict :
    forall a b c : binary_float prec emax,
    ieee_le a b -> ieee_le b c -> a <> b -> b <> c ->
    (float_sq_dist a b + float_sq_dist b c < float_sq_dist a c)%Q.
  Proof.
    intros a b c Hab Hbc Hab2 Hbc2.
    apply (proj1 (ieee_le_phi_iff a b)) in Hab.
    apply (proj1 (ieee_le_phi_iff b c)) in Hbc.
    assert (Hlt1 : (phi a < phi b)%Q).
    { destruct (Qle_lt_or_eq (phi a) (phi b) Hab) as [H | H].
      - exact H.
      - exfalso. apply Hab2, phi_inj, H. }
    assert (Hlt2 : (phi b < phi c)%Q).
    { destruct (Qle_lt_or_eq (phi b) (phi c) Hbc) as [H | H].
      - exact H.
      - exfalso. apply Hbc2, phi_inj, H. }
    unfold float_sq_dist.
    assert (Hac : (phi a - phi c
                   == (phi a - phi b) + (phi b - phi c))%Q) by ring.
    rewrite Hac.
    apply qsq_antitriangle_strict; lra.
  Qed.

  Lemma float_sq_space : ordered_semimetric_space.
  Proof.
    refine {| space_carrier := binary_float prec emax ;
              space_point := B754_nan ;
              space_le := ieee_le ;
              space_dist := float_sq_dist |}.
    - intros x. apply (proj2 (ieee_le_phi_iff x x)), Qle_refl.
    - intros x y z Hxy Hyz. apply (proj2 (ieee_le_phi_iff x z)).
      apply (Qle_trans (phi x) (phi y) (phi z)).
      + apply (proj1 (ieee_le_phi_iff x y)); exact Hxy.
      + apply (proj1 (ieee_le_phi_iff y z)); exact Hyz.
    - intros x y Hxy Hyx. apply phi_inj, Qle_antisym.
      + apply (proj1 (ieee_le_phi_iff x y)); exact Hxy.
      + apply (proj1 (ieee_le_phi_iff y x)); exact Hyx.
    - intros x y. apply float_sq_dist_nonneg.
    - intros x y. split.
      + intros H. apply phi_inj, qdiff_zero, qsq_zero_iff.
        exact H.
      + intros ->. unfold float_sq_dist. ring.
    - intros x y. unfold float_sq_dist. ring.
    - intros a b c Hab Hbc. apply float_sq_antitriangle; assumption.
  Defined.

End FloatSpace.


(* ------------------------------------------------------------------ *)
(** * Concrete formats: binary64 and binary32 *)

Lemma prec_pos_53 : (0 < 53)%Z. Proof. lia. Qed.
Lemma prec_lt_emax_53_1024 : (53 < 1024)%Z. Proof. lia. Qed.
Lemma prec_pos_24 : (0 < 24)%Z. Proof. lia. Qed.
Lemma prec_lt_emax_24_128 : (24 < 128)%Z. Proof. lia. Qed.

Definition binary64_space : ordered_semimetric_space :=
  float_space 53 1024 prec_pos_53 prec_lt_emax_53_1024.
Definition binary32_space : ordered_semimetric_space :=
  float_space 24 128 prec_pos_24 prec_lt_emax_24_128.

(** The order and distance of the binary64 example, spelled out. *)
Definition binary64_le (x y : binary_float 53 1024) : Prop :=
  ieee_le 53 1024 x y.
Definition binary64_dist (x y : binary_float 53 1024) : Q :=
  float_dist 53 1024 x y.

(** The strictly convex variant on the same carrier and order:
    d2(x, y) = (phi x - phi y)^2.  Same order, same carrier as
    [binary64_space], but the antitriangle of Definition 9 is a
    strict inequality on nondegenerate chains. *)
Definition binary64_sq_space : ordered_semimetric_space :=
  float_sq_space 53 1024 prec_pos_53 prec_lt_emax_53_1024.
Definition binary64_sq_dist (x y : binary_float 53 1024) : Q :=
  float_sq_dist 53 1024 x y.

(** Some sanity checks, verified by computation.  They also document
    how the distance treats non-numeric data and signed zeros. *)

Example binary64_dist_nan_inf :
  binary64_dist B754_nan (B754_infinity false) == 1.
Proof. vm_compute. reflexivity. Qed.

Example binary64_dist_negzero_poszero :
  binary64_dist (B754_zero true) (B754_zero false) == Qpower 2 (-1075).
Proof. vm_compute. reflexivity. Qed.

Example binary64_dist_nan_negmax :
  binary64_dist B754_nan
    (@B754_finite 53 1024 true 9007199254740991%positive 971%Z eq_refl)
  == 2 ^ (1025)%Z - 2 ^ (971)%Z + 1.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Vector spaces over an ordered semimetric space:
       the l_infty- and l_1-like spaces. *)

(** ** Finite sums and maxima over Q *)

Fixpoint qsum (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: t => x + qsum t
  end.

Definition qmax (a b : Q) : Q := if Qle_bool a b then b else a.

Lemma qmax_cases : forall a b, (a <= qmax a b /\ b <= qmax a b)%Q.
Proof.
  intros a b. unfold qmax. destruct (Qle_bool a b) eqn:E.
  - split; [ apply (proj1 (Qle_bool_iff a b)); exact E | apply Qle_refl ].
  - split; [ apply Qle_refl | ].
    destruct (Qlt_le_dec b a) as [H|H].
    + apply Qlt_le_weak, H.
    + rewrite (proj2 (Qle_bool_iff a b) H) in E. discriminate.
Qed.

Lemma qmax_le_l : forall a b, (a <= qmax a b)%Q.
Proof. intros a b. apply (qmax_cases a b). Qed.

Lemma qmax_le_r : forall a b, (b <= qmax a b)%Q.
Proof. intros a b. apply (qmax_cases a b). Qed.

Lemma qmax_le_ub : forall a b c,
  (a <= c)%Q -> (b <= c)%Q -> (qmax a b <= c)%Q.
Proof.
  intros a b c Ha Hb. unfold qmax. destruct (Qle_bool a b) eqn:E.
  - exact Hb.
  - exact Ha.
Qed.

Lemma qmax_zero : forall a b, (a == 0)%Q -> (b == 0)%Q -> (qmax a b == 0)%Q.
Proof.
  intros a b Ha Hb. unfold qmax. destruct (Qle_bool a b).
  - exact Hb.
  - exact Ha.
Qed.

Fixpoint qmaxl (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: t => qmax x (qmaxl t)
  end.

Lemma qmaxl_in : forall l x, In x l -> (x <= qmaxl l)%Q.
Proof.
  induction l as [|a t IH]; simpl; intros x Hx.
  - destruct Hx.
  - destruct Hx as [<-|Hx].
    + apply qmax_le_l.
    + apply (Qle_trans x (qmaxl t)); [apply IH; exact Hx | apply qmax_le_r].
Qed.

Lemma qmaxl_nonneg : forall l,
  (forall x, In x l -> (0 <= x)%Q) -> (0 <= qmaxl l)%Q.
Proof.
  induction l as [|a t IH]; simpl; intros H.
  - apply Qle_refl.
  - unfold qmax. destruct (Qle_bool a (qmaxl t)).
    + apply IH. intros z Hz. apply H. now right.
    + apply H. now left.
Qed.

Lemma qmaxl_le_ub : forall l c, (0 <= c)%Q ->
  (forall x, In x l -> (x <= c)%Q) -> (qmaxl l <= c)%Q.
Proof.
  induction l as [|a t IH]; simpl; intros c Hc H.
  - exact Hc.
  - apply qmax_le_ub.
    + apply H. now left.
    + apply IH.
      * exact Hc.
      * intros z Hz. apply H. now right.
Qed.

Lemma qmaxl_zero : forall l,
  (forall x, In x l -> (x == 0)%Q) -> (qmaxl l == 0)%Q.
Proof.
  induction l as [|a t IH]; simpl; intros H.
  - reflexivity.
  - apply qmax_zero.
    + apply H. now left.
    + apply IH. intros z Hz. apply H. now right.
Qed.

Lemma qmaxl_map_ext_nonneg : forall (f g : nat -> Q) l,
  (forall x, In x (map f l) -> (0 <= x)%Q) ->
  (forall i, In i l -> (f i == g i)%Q) ->
  (qmaxl (map f l) == qmaxl (map g l))%Q.
Proof.
  intros f g l Hnn Hpt.
  assert (Hge : (0 <= qmaxl (map g l))%Q).
  { apply qmaxl_nonneg. intros z Hz.
    apply in_map_iff in Hz. destruct Hz as [i [<- Hi]].
    assert (Hin : In (f i) (map f l))
      by (apply in_map_iff; exists i; split; [reflexivity|exact Hi]).
    pose proof (Hnn (f i) Hin) as Hf.
    apply (Qle_trans 0 (f i)).
    + exact Hf.
    + apply qeq_le. apply (Hpt i Hi). }
  assert (Hle1 : (qmaxl (map f l) <= qmaxl (map g l))%Q).
  { apply qmaxl_le_ub; [exact Hge|].
    intros x Hx. apply in_map_iff in Hx. destruct Hx as [i [<- Hi]].
    apply (Qle_trans (f i) (g i)).
    - apply qeq_le. apply (Hpt i Hi).
    - apply qmaxl_in. apply in_map_iff. exists i.
      split; [reflexivity|exact Hi]. }
  assert (Hle2 : (qmaxl (map g l) <= qmaxl (map f l))%Q).
  { apply qmaxl_le_ub.
    - apply qmaxl_nonneg. exact Hnn.
    - intros x Hx. apply in_map_iff in Hx. destruct Hx as [i [<- Hi]].
      apply (Qle_trans (g i) (f i)).
      + apply qeq_le. apply (qeq_sym' _ _ (Hpt i Hi)).
      + apply qmaxl_in. apply in_map_iff. exists i.
        split; [reflexivity|exact Hi]. }
  apply Qle_antisym; assumption.
Qed.

Lemma qle_add_nonneg : forall x y : Q, (0 <= y)%Q -> (x <= x + y)%Q.
Proof.
  intros x y Hy.
  apply (Qle_trans x (x + 0)).
  - rewrite (Qplus_0_r x). apply Qle_refl.
  - apply (proj2 (Qplus_le_r 0 y x)). exact Hy.
Qed.

Lemma qsum_nonneg : forall l,
  (forall x, In x l -> (0 <= x)%Q) -> (0 <= qsum l)%Q.
Proof.
  induction l as [|a t IH]; simpl; intros H.
  - apply Qle_refl.
  - pose proof (H a (in_eq a t)) as Ha.
    assert (Ht : (0 <= qsum t)%Q) by
      (apply IH; intros z Hz; apply H; now right).
    first [ lra | psatz Q 4 | nra ].
Qed.

Lemma qsum_zero : forall l,
  (forall x, In x l -> (0 <= x)%Q) -> (qsum l == 0)%Q ->
  forall x, In x l -> (x == 0)%Q.
Proof.
  induction l as [|a t IH]; simpl; intros Hn H0 x Hx.
  - destruct Hx.
  - pose proof (Hn a (in_eq a t)) as Ha.
    assert (Ht : (0 <= qsum t)%Q) by
      (apply qsum_nonneg; intros z Hz; apply Hn; now right).
    destruct Hx as [<-|Hx].
    + apply Qle_antisym.
      * first [ lra | psatz Q 4 | nra ].
      * exact Ha.
    + apply IH; auto.
      apply Qle_antisym.
      * first [ lra | psatz Q 4 | nra ].
      * exact Ht.
Qed.

(** If all elements of a NONEMPTY list equal a nonnegative constant c,
    the maximum is c.  (For the empty list qmaxl = 0, so nonnegativity
    of c is needed even on the singleton case: qmaxl [c] = qmax c 0.) *)
Lemma qmaxl_const_nonneg : forall l a c, (0 <= c)%Q ->
  (forall x, In x (a :: l) -> (x == c)%Q) ->
  (qmaxl (a :: l) == c)%Q.
Proof.
  intros l. induction l as [|b t IH]; intros a c Hc H.
  - assert (Ha : (a == c)%Q) by (apply H; now left).
    replace (qmaxl (a :: nil)) with (qmax a 0) by reflexivity.
    unfold qmax. destruct (Qle_bool a 0) eqn:E.
    + apply (proj1 (Qle_bool_iff a 0)) in E.
      apply qeq_sym'. apply Qle_antisym.
      * apply (Qle_trans c a 0).
        -- apply qeq_le. apply qeq_sym'. exact Ha.
        -- exact E.
      * exact Hc.
    + exact Ha.
  - assert (Ha : (a == c)%Q) by (apply H; now left).
    assert (IHc : (qmaxl (b :: t) == c)%Q).
    { apply (IH b c Hc). intros z Hz. apply H. now right. }
    replace (qmaxl (a :: b :: t)) with (qmax a (qmaxl (b :: t)))
      by reflexivity.
    unfold qmax. destruct (Qle_bool a (qmaxl (b :: t))) eqn:E.
    + exact IHc.
    + exact Ha.
Qed.

Lemma qsum_map_zero : forall (f : nat -> Q) l,
  (forall i, In i l -> (f i == 0)%Q) -> (qsum (map f l) == 0)%Q.
Proof.
  induction l as [|a t IH]; simpl; intros H.
  - reflexivity.
  - rewrite (H a (in_eq a t)). rewrite IH.
    + reflexivity.
    + intros z Hz. apply H. now right.
Qed.

Lemma qsum_ext : forall (f g : nat -> Q) l,
  (forall i, In i l -> (f i == g i)%Q) ->
  (qsum (map f l) == qsum (map g l))%Q.
Proof.
  induction l as [|a t IH]; simpl; intros H.
  - reflexivity.
  - rewrite (H a (in_eq a t)). rewrite IH.
    + reflexivity.
    + intros z Hz. apply H. now right.
Qed.

(** l_1 antitriangle: if per component the two legs sum to at most the
    whole (g i + h i <= f i), then the sum of the legs is at most the
    sum of the wholes. *)
Lemma qsum_antitriangle : forall (f g h : nat -> Q) l,
  (forall i, In i l -> (g i + h i <= f i)%Q) ->
  (qsum (map g l) + qsum (map h l) <= qsum (map f l))%Q.
Proof.
  induction l as [|a t IH]; simpl; intros H.
  - apply Qle_refl.
  - pose proof (H a (in_eq a t)) as Hpt.
    assert (IH' : (qsum (map g t) + qsum (map h t)
                   <= qsum (map f t))%Q)
      by (apply IH; intros z Hz; apply H; now right).
    apply (Qle_trans _ ((g a + h a)
                      + (qsum (map g t) + qsum (map h t)))).
    + apply qeq_le. ring.
    + apply Qplus_le_compat; [exact Hpt | exact IH'].
Qed.

(** ** The l_1 and l_infty vector spaces over any ordered semimetric
        space.  Vectors are lists of points of the space.  The order is
        the pointwise order (only equal-length lists are comparable),
        and a length mismatch contributes a +1 penalty to the distance;
        beyond the ends of a list, components are read as the space
        point (which is at distance zero from itself, hence the
        penalty is needed for the identity of indiscernibles). *)

Section VectorSpace.
  Variable V : ordered_semimetric_space.

  Definition vec_le (x y : list (space_carrier V)) : Prop :=
    (length x = length y) /\
    forall i, (i < length x)%nat ->
      space_le V (nth i x (space_point V)) (nth i y (space_point V)).

  Definition vec_penalty (x y : list (space_carrier V)) : Q :=
    if Nat.eqb (length x) (length y) then 0 else 1.

  Definition vec_comps (x y : list (space_carrier V)) : list Q :=
    map (fun i => space_dist V (nth i x (space_point V))
                                 (nth i y (space_point V)))
        (seq 0 (Nat.max (length x) (length y))).

  Definition vec_dist_l1 (x y : list (space_carrier V)) : Q :=
    vec_penalty x y + qsum (vec_comps x y).

  Definition vec_dist_linf (x y : list (space_carrier V)) : Q :=
    vec_penalty x y + qmaxl (vec_comps x y).

  Lemma vec_comps_nonneg : forall x y z, In z (vec_comps x y) -> (0 <= z)%Q.
  Proof.
    intros x y z Hz. unfold vec_comps in Hz.
    apply in_map_iff in Hz. destruct Hz as [i [<- _]].
    apply (space_dist_nonneg V).
  Qed.

  (** Common scaffolding for the two records. *)
  Lemma vec_le_refl : forall x, vec_le x x.
  Proof.
    intros x. split; [reflexivity|].
    intros i _. apply (space_le_refl V).
  Qed.

  Lemma vec_le_trans' : forall x y z, vec_le x y -> vec_le y z -> vec_le x z.
  Proof.
    intros x y z [Hxy Hpwxy] [Hyz Hpwyz].
    split.
    - rewrite Hxy, Hyz. reflexivity.
    - intros i Hi.
      apply (space_le_trans V _ (nth i y (space_point V)) _).
      + apply Hpwxy. exact Hi.
      + apply Hpwyz. rewrite Hxy in Hi. exact Hi.
  Qed.

  Lemma vec_le_antisym' : forall x y, vec_le x y -> vec_le y x -> x = y.
  Proof.
    intros x y [Hxy Hpwxy] [Hyx Hpwyx].
    apply nth_ext with (d := space_point V) (d' := space_point V).
    - exact Hxy.
    - intros i Hi.
      apply (space_le_antisym V).
      + apply Hpwxy. exact Hi.
      + apply Hpwyx. rewrite Hxy in Hi. exact Hi.
  Qed.

  (** The order of the l_infty space.  The pointwise order does NOT
      make the l_infty-like distance an ordered semimetric space: the
      antitriangle of Definition 9 fails for maxima (see the verified
      counterexample binary64_linf_pointwise_antitriangle_fails at the
      end of this file).  What does work is the "synchronized shift"
      order: vectors of equal length that are pointwise ordered AND
      move every component by the same distance.  Along such chains
      the l_infty distance is additive. *)
  Definition vec_le_sync (x y : list (space_carrier V)) : Prop :=
    (length x = length y) /\
    (forall i, (i < length x)%nat ->
       space_le V (nth i x (space_point V))
                  (nth i y (space_point V))) /\
    (forall i j, (i < length x)%nat -> (j < length x)%nat ->
       space_dist V (nth i x (space_point V))
                    (nth i y (space_point V)) ==
       space_dist V (nth j x (space_point V))
                    (nth j y (space_point V))).

  Lemma vec_le_sync_refl : forall x, vec_le_sync x x.
  Proof.
    intros x. split; [reflexivity|]. split.
    - intros i _. apply (space_le_refl V).
    - intros i j _ _.
      transitivity (0:Q).
      + apply (proj2 (space_dist_zero V _ _)). reflexivity.
      + apply qeq_sym'.
        apply (proj2 (space_dist_zero V _ _)). reflexivity.
  Qed.

  Lemma vec_le_sync_antisym : forall x y,
    vec_le_sync x y -> vec_le_sync y x -> x = y.
  Proof.
    intros x y [Hxy [Hpwxy Hsynxy]] [Hyx [Hpwyx Hsynyx]].
    apply nth_ext with (d := space_point V) (d' := space_point V).
    - exact Hxy.
    - intros i Hi.
      apply (space_le_antisym V).
      + apply Hpwxy. exact Hi.
      + apply Hpwyx. rewrite Hxy in Hi. exact Hi.
  Qed.

  (** Transitivity of the synchronized order needs the antitriangle to
      hold with equality (true on the float spaces). *)
  Lemma vec_le_sync_trans : forall x y z,
    (forall u v w, space_le V u v -> space_le V v w ->
       space_dist V u w == space_dist V u v + space_dist V v w) ->
    vec_le_sync x y -> vec_le_sync y z -> vec_le_sync x z.
  Proof.
    intros x y z Hadd [Hxy [Hpwxy Hsynxy]] [Hyz [Hpwyz Hsynyz]].
    split; [rewrite Hxy, Hyz; reflexivity|]. split.
    - intros i Hi.
      apply (space_le_trans V _ (nth i y (space_point V)) _).
      + apply Hpwxy. exact Hi.
      + apply Hpwyz. rewrite Hxy in Hi. exact Hi.
    - intros i j Hi Hj.
      assert (Hiy : (i < length y)%nat) by (rewrite <- Hxy; exact Hi).
      assert (Hjy : (j < length y)%nat) by (rewrite <- Hxy; exact Hj).
      rewrite (Hadd (nth i x (space_point V))
                    (nth i y (space_point V))
                    (nth i z (space_point V))
                    (Hpwxy i Hi) (Hpwyz i Hiy)).
      rewrite (Hadd (nth j x (space_point V))
                    (nth j y (space_point V))
                    (nth j z (space_point V))
                    (Hpwxy j Hj) (Hpwyz j Hjy)).
      rewrite <- (Hsynxy i j Hi Hj).
      rewrite <- (Hsynyz i j Hiy Hjy).
      reflexivity.
  Qed.

  (** If the lengths are equal, the components of [vec_comps] at
      indices below the length are exactly the component distances. *)
  Lemma in_vec_comps : forall x y i,
    (i < length x)%nat -> length x = length y ->
    In (space_dist V (nth i x (space_point V))
                     (nth i y (space_point V))) (vec_comps x y).
  Proof.
    intros x y i Hi Hlen. unfold vec_comps. apply in_map_iff.
    exists i. split; [reflexivity|].
    apply in_seq.
    rewrite Nat.max_l by lia. lia.
  Qed.

  (** Conversely, every element of [vec_comps] is some component
      distance. *)
  Lemma vec_comps_in : forall x y z,
    In z (vec_comps x y) ->
    exists i, (i < Nat.max (length x) (length y))%nat /\
              (z == space_dist V (nth i x (space_point V))
                              (nth i y (space_point V)))%Q.
  Proof.
    intros x y z Hz. unfold vec_comps in Hz.
    apply in_map_iff in Hz. destruct Hz as [i [<- Hi]].
    apply in_seq in Hi.
    exists i. split; [lia | reflexivity].
  Qed.

  (** Each component distance is bounded by the l_infty distance. *)
  Lemma vec_comp_bound : forall x y i, (i < length x)%nat ->
    (space_dist V (nth i x (space_point V)) (nth i y (space_point V))
     <= qmaxl (vec_comps x y))%Q.
  Proof.
    intros x y i Hi. unfold vec_comps.
    apply qmaxl_in. apply in_map_iff. exists i.
    split.
    - reflexivity.
    - apply in_seq. lia.
  Qed.

  (** If all component distances vanish and the lengths agree, the
      vectors are equal. *)
  Lemma vec_comps_zero_to_eq : forall x y,
    length x = length y ->
    (forall z, In z (vec_comps x y) -> (z == 0)%Q) ->
    x = y.
  Proof.
    intros x y Hlen Hall.
    apply (vec_le_antisym' x y).
    - split; [exact Hlen|].
      intros i Hi.
      assert (Hin := in_vec_comps x y i Hi Hlen).
      assert (Hd : (space_dist V (nth i x (space_point V))
                          (nth i y (space_point V)) == 0)%Q)
        by (apply Hall; exact Hin).
      assert (Heq : nth i x (space_point V) = nth i y (space_point V))
        by (apply (proj1 (space_dist_zero V _ _)); exact Hd).
      rewrite Heq. apply (space_le_refl V).
    - split; [rewrite Hlen; reflexivity|].
      intros i Hi.
      assert (Hi' : (i < length x)%nat) by (rewrite Hlen; exact Hi).
      assert (Hin := in_vec_comps x y i Hi' Hlen).
      assert (Hd0 : (space_dist V (nth i x (space_point V))
                           (nth i y (space_point V)) == 0)%Q)
        by (apply Hall; exact Hin).
      assert (Hd : (space_dist V (nth i y (space_point V))
                          (nth i x (space_point V)) == 0)%Q).
      { rewrite (space_dist_sym V (nth i y (space_point V))
                                 (nth i x (space_point V))). exact Hd0. }
      assert (Heq : nth i y (space_point V) = nth i x (space_point V))
        by (apply (proj1 (space_dist_zero V _ _)); exact Hd).
      rewrite Heq. apply (space_le_refl V).
  Qed.

  Definition vec_l1_space : ordered_semimetric_space.
  Proof.
    refine {| space_carrier := list (space_carrier V);
              space_point := nil ;
              space_le := vec_le ;
              space_dist := vec_dist_l1 |}.
    - intros x. apply vec_le_refl.
    - intros x y z. apply vec_le_trans'.
    - intros x y Hxy Hyx. apply (vec_le_antisym' x y Hxy Hyx).
    - (* nonneg *)
      intros x y. unfold vec_dist_l1.
      pose proof (qsum_nonneg (vec_comps x y) (vec_comps_nonneg x y)) as Hs.
      unfold vec_penalty. destruct (Nat.eqb (length x) (length y)).
      first [ lra | psatz Q 4 | nra ].
      first [ lra | psatz Q 4 | nra ].
    - (* zero iff *)
      intros x y. unfold vec_dist_l1. split.
      + intros H.
        pose proof (qsum_nonneg (vec_comps x y) (vec_comps_nonneg x y)) as Hs.
        unfold vec_penalty in H.
        destruct (Nat.eqb (length x) (length y)) eqn:E.
        * apply Nat.eqb_eq in E.
          assert (H0 : (qsum (vec_comps x y) == 0)%Q)
            by first [ lra | psatz Q 4 | nra ].
          assert (Hall : forall z, In z (vec_comps x y) -> (z == 0)%Q)
            by (intros z Hz;
                apply (qsum_zero (vec_comps x y) (vec_comps_nonneg x y) H0 z Hz)).
          exact (vec_comps_zero_to_eq x y E Hall).
        * exfalso. first [ lra | psatz Q 4 | nra ].
      + intros <-. unfold vec_dist_l1, vec_penalty.
        rewrite Nat.eqb_refl.
        assert (H0 : (qsum (vec_comps x x) == 0)%Q).
        { apply qsum_map_zero. intros i _.
          apply (proj2 (space_dist_zero V _ _)). reflexivity. }
        rewrite H0. reflexivity.
    - (* sym *)
      intros x y. unfold vec_dist_l1.
      unfold vec_penalty. assert (Hbc : Nat.eqb (length x) (length y) = Nat.eqb (length y) (length x))
        by (apply Nat.eqb_sym).
      rewrite Hbc.
      assert (Hs : (qsum (vec_comps x y) == qsum (vec_comps y x))%Q).
      { unfold vec_comps. rewrite Nat.max_comm.
        apply qsum_ext. intros i _. apply (space_dist_sym V). }
      rewrite Hs. reflexivity.
    - (* antitriangle of Definition 9 *)
      intros a b c Hab Hbc.
      destruct Hab as [Hab Hpwab]. destruct Hbc as [Hbc Hpwbc].
      unfold vec_dist_l1, vec_penalty, vec_comps.
      rewrite (proj2 (Nat.eqb_eq (length a) (length b)) Hab).
      rewrite (proj2 (Nat.eqb_eq (length b) (length c)) Hbc).
      rewrite (proj2 (Nat.eqb_eq (length a) (length c))
                (Nat.eq_trans Hab Hbc)).
      rewrite <- Hbc, <- Hab.
      rewrite !Nat.max_id.
      assert (Hanti : (qsum (map (fun i => space_dist V
                   (nth i a (space_point V)) (nth i b (space_point V)))
                   (seq 0 (length a)))
                + qsum (map (fun i => space_dist V
                   (nth i b (space_point V)) (nth i c (space_point V)))
                   (seq 0 (length a)))
              <= qsum (map (fun i => space_dist V
                   (nth i a (space_point V)) (nth i c (space_point V)))
                   (seq 0 (length a))))%Q).
      { apply qsum_antitriangle. intros i Hin.
        apply in_seq in Hin.
        assert (Hia : (i < length a)%nat) by lia.
        apply (space_le_antitriangle V).
        - apply Hpwab. exact Hia.
        - apply Hpwbc. lia. }
      first [ lra | psatz Q 4 | nra ].
  Defined.

  (** The l_infty space.  NOTE: the order is [vec_le_sync], NOT the
      pointwise order [vec_le]: with the pointwise order the
      antitriangle of Definition 9 fails (max is not superadditive; see
      binary64_linf_pointwise_antitriangle_fails below).  The
      construction therefore requires the antitriangle of the base
      space to hold with equality (Hadd), which the float spaces
      provide (float_dist_add). *)
  Definition vec_linf_space
    (Hadd : forall u v w, space_le V u v -> space_le V v w ->
       space_dist V u w == space_dist V u v + space_dist V v w)
    : ordered_semimetric_space.
  Proof.
    refine {| space_carrier := list (space_carrier V);
              space_point := nil ;
              space_le := vec_le_sync ;
              space_dist := vec_dist_linf |}.
    - intros x. apply vec_le_sync_refl.
    - intros x y z Hxy Hyz. apply (vec_le_sync_trans x y z Hadd Hxy Hyz).
    - intros x y Hxy Hyx. apply (vec_le_sync_antisym x y Hxy Hyx).
    - (* nonneg *)
      intros x y. unfold vec_dist_linf.
      pose proof (qmaxl_nonneg (vec_comps x y) (vec_comps_nonneg x y)) as Hs.
      unfold vec_penalty. destruct (Nat.eqb (length x) (length y)).
      first [ lra | psatz Q 4 | nra ].
      first [ lra | psatz Q 4 | nra ].
    - (* zero iff *)
      intros x y. unfold vec_dist_linf. split.
      + intros H.
        pose proof (qsum_nonneg (vec_comps x y) (vec_comps_nonneg x y)) as Hs.
        unfold vec_penalty in H.
        destruct (Nat.eqb (length x) (length y)) eqn:E.
        * apply Nat.eqb_eq in E.
          assert (Hall : forall z, In z (vec_comps x y) -> (z == 0)%Q).
          { intros z Hz.
            assert (Hge : (0 <= z)%Q) by (apply (vec_comps_nonneg x y); exact Hz).
            assert (H0 : (qmaxl (vec_comps x y) == 0)%Q)
              by first [ lra | psatz Q 4 | nra ].
            assert (Hz' : (z <= qmaxl (vec_comps x y))%Q)
              by (apply qmaxl_in; exact Hz).
            apply Qle_antisym.
            -- first [ lra | psatz Q 4 | nra ].
            -- exact Hge. }
          exact (vec_comps_zero_to_eq x y E Hall).
        * exfalso.
          pose proof (qmaxl_nonneg (vec_comps x y) (vec_comps_nonneg x y)) as Hs2.
          first [ lra | psatz Q 4 | nra ].
      + intros <-. unfold vec_dist_linf, vec_penalty.
        rewrite Nat.eqb_refl.
        assert (H0 : (qmaxl (vec_comps x x) == 0)%Q).
        { apply qmaxl_zero. intros z Hz.
          unfold vec_comps in Hz. apply in_map_iff in Hz.
          destruct Hz as [i [<- _]].
          apply (proj2 (space_dist_zero V _ _)). reflexivity. }
        rewrite H0. reflexivity.
    - (* sym *)
      intros x y. unfold vec_dist_linf.
      unfold vec_penalty. assert (Hbc : Nat.eqb (length x) (length y) = Nat.eqb (length y) (length x))
        by (apply Nat.eqb_sym).
      rewrite Hbc.
      assert (Hs : (qmaxl (vec_comps x y) == qmaxl (vec_comps y x))%Q).
      { unfold vec_comps. rewrite Nat.max_comm.
        apply qmaxl_map_ext_nonneg.
        - intros z Hz. apply in_map_iff in Hz.
          destruct Hz as [i [<- _]].
          apply (space_dist_nonneg V).
        - intros i _. apply (space_dist_sym V). }
      rewrite Hs. reflexivity.
    - (* antitriangle of Definition 9: along a synchronized chain the
         l_infty distance is exactly additive. *)
      intros a b c Hab Hbc.
      destruct Hab as [Hab [Hpwab Hsynab]].
      destruct Hbc as [Hbc [Hpwbc Hsynbc]].
      unfold vec_dist_linf, vec_penalty.
      rewrite (proj2 (Nat.eqb_eq (length a) (length b)) Hab).
      rewrite (proj2 (Nat.eqb_eq (length b) (length c)) Hbc).
      rewrite (proj2 (Nat.eqb_eq (length a) (length c))
                (Nat.eq_trans Hab Hbc)).
      destruct a as [|a1 ar].
      + (* all three vectors empty *)
        destruct b as [|b1 br]; [| simpl in Hab; discriminate].
        destruct c as [|c1 cr]; [| simpl in Hbc; discriminate].
        unfold vec_comps. simpl.
        first [ lra | psatz Q 4 | nra ].
      + (* nonempty *)
        destruct b as [|b1 br]; [ simpl in Hab; discriminate Hab | ].
        destruct c as [|c1 cr]; [ simpl in Hbc; discriminate Hbc | ].
        assert (Hia : forall i, In i (seq 0 (length (a1 :: ar)))
                      -> (i < length (a1 :: ar))%nat)
          by (intros i Hi; apply in_seq in Hi; lia).
        assert (Hia0 : (0 < length (a1 :: ar))%nat)
          by (simpl; lia).
        assert (Hib0 : (0 < length (b1 :: br))%nat)
          by (simpl; lia).
        set (t := space_dist V (nth 0 (a1 :: ar) (space_point V))
                             (nth 0 (b1 :: br) (space_point V))).
        set (s := space_dist V (nth 0 (b1 :: br) (space_point V))
                             (nth 0 (c1 :: cr) (space_point V))).
        assert (Ht : (0 <= t)%Q) by (apply (space_dist_nonneg V)).
        assert (Hs0 : (0 <= s)%Q) by (apply (space_dist_nonneg V)).
        assert (Htab : (qmaxl (vec_comps (a1 :: ar) (b1 :: br)) == t)%Q).
        { apply qmaxl_const_nonneg; [exact Ht|].
          intros z Hz.
          destruct (vec_comps_in (a1 :: ar) (b1 :: br) z Hz)
            as [i [Hi Hzi]].
          assert (Hia' : (i < length (a1 :: ar))%nat).
          { rewrite Hab in Hi. rewrite Nat.max_id in Hi.
            rewrite Hab. exact Hi. }
          exact (Qeq_trans _ _ _ Hzi (Hsynab i 0%nat Hia' Hia0)). }
        assert (Hsbc : (qmaxl (vec_comps (b1 :: br) (c1 :: cr)) == s)%Q).
        { apply qmaxl_const_nonneg; [exact Hs0|].
          intros z Hz.
          destruct (vec_comps_in (b1 :: br) (c1 :: cr) z Hz)
            as [i [Hi Hzi]].
          assert (Hib' : (i < length (b1 :: br))%nat).
          { rewrite Hbc in Hi. rewrite Nat.max_id in Hi.
            rewrite Hbc. exact Hi. }
          exact (Qeq_trans _ _ _ Hzi (Hsynbc i 0%nat Hib' Hib0)). }
        assert (Htac : (qmaxl (vec_comps (a1 :: ar) (c1 :: cr))
                       == t + s)%Q).
        { apply qmaxl_const_nonneg;
            [first [ lra | psatz Q 4 | nra ]|].
          intros z Hz.
          destruct (vec_comps_in (a1 :: ar) (c1 :: cr) z Hz)
            as [i [Hi Hzi]].
          assert (Hac : length (a1 :: ar) = length (c1 :: cr))
            by (rewrite Hab; exact Hbc).
          assert (Hia' : (i < length (a1 :: ar))%nat).
          { rewrite Hac in Hi. rewrite Nat.max_id in Hi.
            rewrite Hac. exact Hi. }
          assert (Hib' : (i < length (b1 :: br))%nat).
          { rewrite <- Hac in Hi. rewrite Nat.max_id in Hi.
            rewrite <- Hab. exact Hi. }
          assert (Hd : (space_dist V (nth i (a1 :: ar) (space_point V))
                                 (nth i (c1 :: cr) (space_point V))
                        == t + s)%Q).
          { apply (Qeq_trans _ _ _
                     (Hadd (nth i (a1 :: ar) (space_point V))
                           (nth i (b1 :: br) (space_point V))
                           (nth i (c1 :: cr) (space_point V))
                           (Hpwab i Hia') (Hpwbc i Hib'))).
            rewrite (Hsynab i 0%nat Hia' Hia0), (Hsynbc i 0%nat Hib' Hib0).
            reflexivity. }
          exact (Qeq_trans _ _ _ Hzi Hd). }
        rewrite Htab, Hsbc, Htac.
        first [ lra | psatz Q 4 | nra ].
  Defined.

End VectorSpace.

(** ** The binary64 vector examples *)

(** The l_1 vector space: pointwise order, generic construction. *)
Definition binary64_l1_space : ordered_semimetric_space :=
  vec_l1_space binary64_space.

(** On the binary64 space the antitriangle of Definition 9 holds with
    equality (Theorem float_dist_add), which unlocks the l_infty
    vector space (whose order is the synchronized shift). *)
Definition binary64_dist_add :
  forall a b c : binary_float 53 1024,
    binary64_le a b -> binary64_le b c ->
    binary64_dist a c == binary64_dist a b + binary64_dist b c :=
  fun a b c h1 h2 =>
    Qeq_sym _ _
      (float_dist_add 53 1024 prec_pos_53 prec_lt_emax_53_1024 a b c h1 h2).

Definition binary64_linf_space : ordered_semimetric_space :=
  vec_linf_space binary64_space binary64_dist_add.

(** Orders: l_1 uses the pointwise order, l_infty the synchronized
    shift order. *)
Definition binary64_vec_le (x y : list (binary_float 53 1024)) : Prop :=
  vec_le binary64_space x y.
Definition binary64_vec_le_sync
  (x y : list (binary_float 53 1024)) : Prop :=
  vec_le_sync binary64_space x y.
Definition binary64_l1_dist (x y : list (binary_float 53 1024)) : Q :=
  vec_dist_l1 binary64_space x y.
Definition binary64_linf_dist (x y : list (binary_float 53 1024)) : Q :=
  vec_dist_linf binary64_space x y.

(** d([1; -0], [1/2; +0]) = |1-1/2| + 2^(-1075). *)
Example binary64_l1_example :
  binary64_l1_dist
    [ @B754_finite 53 1024 false 4503599627370496%positive (-52)%Z eq_refl
    ; B754_zero true ]
    [ @B754_finite 53 1024 false 4503599627370496%positive (-53)%Z eq_refl
    ; B754_zero false ]
  == (1 # 2) + Qpower 2 (-1075).
Proof. vm_compute. reflexivity. Qed.

(** length mismatch: the +1 penalty *)
Example binary64_l1_penalty_example :
  binary64_l1_dist [ B754_nan ] [ B754_nan; B754_nan ] == 1.
Proof. vm_compute. reflexivity. Qed.

Example binary64_linf_example :
  binary64_linf_dist
    [ @B754_finite 53 1024 false 4503599627370496%positive (-52)%Z eq_refl
    ; B754_zero true ]
    [ @B754_finite 53 1024 false 4503599627370496%positive (-53)%Z eq_refl
    ; B754_zero false ]
  == (1 # 2).
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** * Verified illustrations of the antitriangle of Definition 9

    On the pure-float space the antitriangle holds with equality, and
    on the l_1 vector space it follows componentwise.  For the l_infty
    vector space the natural POINTWISE order provably FAILS: maxima are
    not superadditive.  The following computation is the witness that
    forced the synchronized-shift order for [binary64_linf_space]. *)

(** On pure floats: d(1, 3) = d(1, 2) + d(2, 3) (equality). *)
Example binary64_antitriangle_example :
  binary64_dist
    (@B754_finite 53 1024 false 4503599627370496%positive (-52)%Z eq_refl)
    (@B754_finite 53 1024 false 6755399441055744%positive (-51)%Z eq_refl)
  == binary64_dist
       (@B754_finite 53 1024 false 4503599627370496%positive (-52)%Z eq_refl)
       (@B754_finite 53 1024 false 4503599627370496%positive (-51)%Z eq_refl)
   + binary64_dist
       (@B754_finite 53 1024 false 4503599627370496%positive (-51)%Z eq_refl)
       (@B754_finite 53 1024 false 6755399441055744%positive (-51)%Z eq_refl).
Proof. vm_compute. reflexivity. Qed.

(** Helper: ieee_le on concrete floats by computation of phi. *)
Lemma binary64_le_compute : forall x y : binary_float 53 1024,
  Qle_bool (phi 53 1024 x) (phi 53 1024 y) = true ->
  binary64_le x y.
Proof.
  intros x y H.
  apply (proj2 (ieee_le_phi_iff 53 1024 prec_pos_53
                  prec_lt_emax_53_1024 x y)).
  apply (proj1 (Qle_bool_iff _ _)). exact H.
Qed.

Definition ATv1 : binary_float 53 1024 :=
  @B754_finite 53 1024 false 4503599627370496%positive (-52)%Z eq_refl.
Definition ATv8 : binary_float 53 1024 :=
  @B754_finite 53 1024 false 4503599627370496%positive (-49)%Z eq_refl.
Definition ATv11 : binary_float 53 1024 :=
  @B754_finite 53 1024 false 6192449487634432%positive (-49)%Z eq_refl.

Lemma AT_le_1_11 : binary64_le ATv1 ATv11.
Proof. apply binary64_le_compute. vm_compute. reflexivity. Qed.
Lemma AT_le_1_8 : binary64_le ATv1 ATv8.
Proof. apply binary64_le_compute. vm_compute. reflexivity. Qed.

(** The triple ([1;1] <= [11;1] <= [11;8]) is pointwise ordered ... *)
Example AT_pointwise_1 :
  binary64_vec_le [ATv1; ATv1] [ATv11; ATv1].
Proof.
  split; [reflexivity|].
  intros i Hi.
  destruct i as [|[|[|i]]]; cbn [nth];
    try (apply binary64_le_compute; vm_compute; reflexivity);
    simpl in Hi; exfalso; lia.
Qed.

Example AT_pointwise_2 :
  binary64_vec_le [ATv11; ATv1] [ATv11; ATv8].
Proof.
  split; [reflexivity|].
  intros i Hi.
  destruct i as [|[|[|i]]]; cbn [nth];
    try (apply binary64_le_compute; vm_compute; reflexivity);
    simpl in Hi; exfalso; lia.
Qed.

(** ... but the l_infty antitriangle FAILS on it:
       d_infty([1;1],[11;8]) = 10 < 10 + 7. *)
Example binary64_linf_pointwise_antitriangle_fails :
  (binary64_linf_dist [ATv1; ATv1] [ATv11; ATv8]
   < binary64_linf_dist [ATv1; ATv1] [ATv11; ATv1]
     + binary64_linf_dist [ATv11; ATv1] [ATv11; ATv8])%Q.
Proof.
  apply (proj2 (Qlt_alt _ _)). vm_compute. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * The squared distance: the antitriangle is NECESSARILY an
    inequality

    All examples so far (phi-distance, l_1, l_infty with the
    synchronized order) satisfy the antitriangle of Definition 9 with
    equality.  The strictly convex variant
    [binary64_sq_dist] (same IEEE-754 order!) makes it strict on every
    nondegenerate chain — see [float_sq_antitriangle_strict]. *)

Example binary64_sq_dist_nan_inf :
  binary64_sq_dist B754_nan (B754_infinity false) == 1.
Proof. vm_compute. reflexivity. Qed.

Example binary64_sq_dist_negzero_poszero :
  binary64_sq_dist (B754_zero true) (B754_zero false)
  == Qpower 2 (-2150).
Proof. vm_compute. reflexivity. Qed.

(** d2(1,2) + d2(2,3) = 1 + 1 < 4 = d2(1,3). *)
Example binary64_sq_antitriangle_strict :
  (binary64_sq_dist
     (@B754_finite 53 1024 false 4503599627370496%positive (-52)%Z eq_refl)
     (@B754_finite 53 1024 false 4503599627370496%positive (-51)%Z eq_refl)
   + binary64_sq_dist
       (@B754_finite 53 1024 false 4503599627370496%positive (-51)%Z eq_refl)
       (@B754_finite 53 1024 false 6755399441055744%positive (-51)%Z eq_refl)
   < binary64_sq_dist
       (@B754_finite 53 1024 false 4503599627370496%positive (-52)%Z eq_refl)
       (@B754_finite 53 1024 false 6755399441055744%positive (-51)%Z eq_refl))%Q.
Proof.
  apply (proj2 (Qlt_alt _ _)).
  vm_compute. reflexivity.
Qed.
