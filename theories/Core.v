(** * The language-generic command core

    This is the back half of what used to be [Imp.v], with every mention of
    [Z], [aexp], [aeval] and [{fmap string -> Z}] replaced by a projection of
    the signature [Lang.t].  The command syntax, both semantics, and the
    Kleene-algebra view of [CSTAR] are defined here once; [Imp.v] and the
    Clight instance supply only their expressions, values and stores.

    ** What changed, and why

    Two rules gained a sibling.  [ASSIGN] and [ASSUME] evaluate an
    expression, and evaluation is now partial ([Lang.eval] returns an
    [option], see the header of [Lang.v]).  When it returns [None] the
    command *errors*:

    - [cexec_assign_err]: [eval a s = None] gives [RError s];
    - [cexec_assume_err]: [beval b s = None] gives [RError s].

    Note the asymmetry in [ASSUME], which is deliberate and is the whole
    point of separating "undefined" from "false":

    - [beval b s = Some true]  — the guard passes, execution continues;
    - [beval b s = Some false] — the guard fails, execution *blocks*: there
      is no rule, and no result at all.  This is the [ASSUME] of the original
      development, the KAT test;
    - [beval b s = None]       — the guard is *undefined*, e.g. [if (1/0)],
      and execution errors.  Blocking here would be unsound in the direction
      that matters: it would silently discard a real bug.

    For a language whose evaluation is total — IMP — the [None] rules can
    never fire, and [Imp.v] recovers the original semantics from them (see
    [Imp.cexec_assign_total], [Imp.cexec_assume_total]).

    Everything else is the original development, verbatim modulo the
    generalisation. *)

From Stdlib Require Import Arith ZArith Bool List.
From Stdlib Require Import RelationClasses Morphisms Setoid.
From IncLogic Require Import Sequences RelKleene Lang.

Set Warnings "-notation-for-abbreviation".

(** ** Syntax and semantics

    Everything in this section takes the language [L] as an implicit
    parameter.  The notations come after it, because a [Notation] declared
    inside a [Section] does not survive the [End]. *)

Section DEFS.

Context {L : lang}.

Local Notation ident := (Lang.ident L).
Local Notation value := (Lang.value L).
Local Notation store := (Lang.store L).
Local Notation expr  := (Lang.expr L).
Local Notation bexp  := (Lang.bexp L).

(** Assertions live here, not in [Hoare.v], because a loop may carry one. *)
Definition assertion : Type := store -> Prop.

(** What a loop may be annotated with.  An invariant [AInv I] says "the loop
    reaches exactly [I]"; a *variant* [AVar R] says "after [n] turns the loop
    is in [R n]", from which the invariant is the union [fun s => exists n, R n s].
    The variant form is the more primitive of the two: it carries the
    induction, so nothing has to be proved about coverage. *)
Inductive loopann : Type :=
  | AInv (I: assertion)
  | AVar (R: nat -> assertion).

(** The commands.  Unchanged from [Imp.v] except that the payloads are now
    the signature's [ident], [expr] and [bexp]. *)
Inductive com : Type :=
  | SKIP                         (**r do nothing *)
  | ERROR                        (**r interrupt the program *)
  | ASSIGN (x: ident) (a: expr)  (**r assignment: [x := a] *)
  | NONDET (x: ident)            (**r non-deterministic assignment to [x] *)
  | ASSUME (b: bexp)             (**r assume that [b] holds *)
  | SEQ (c1: com) (c2: com)      (**r sequence: [c1; c2] *)
  | CHOICE (c1: com) (c2: com)   (**r non-deterministic choice: [c1 ⊕ c2] *)
  | CSTAR (ann: option loopann) (c1: com).
      (**r non-deterministic iteration: [c1★], optionally annotated. *)

(** The result type indicates the end value of a program: either a final
    state on the normal path, or the state at the point of error. *)
Inductive result : Type :=
  | RNormal : store -> result
  | RError  : store -> result.

(** *** Small-step semantics *)

Inductive red: com * store -> com * store -> Prop :=
  | red_assign: forall x a s v,
      Lang.eval a s = Some v ->
      red (ASSIGN x a, s) (SKIP, Lang.update x v s)
  | red_assign_err: forall x a s,
      Lang.eval a s = None ->
      red (ASSIGN x a, s) (ERROR, s)
  | red_nondet: forall x s n,
      red (NONDET x, s) (SKIP, Lang.update x n s)
  | red_assume: forall b s,
      Lang.beval b s = Some true ->
      red (ASSUME b, s) (SKIP, s)
  | red_assume_err: forall b s,
      Lang.beval b s = None ->
      red (ASSUME b, s) (ERROR, s)
  | red_seq_done: forall c s,
      red (SEQ SKIP c, s) (c, s)
  | red_seq_error: forall c s,
      red (SEQ ERROR c, s) (ERROR, s)
  | red_seq_step: forall c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) ->
      red (SEQ c1 c, s1) (SEQ c2 c, s2)
  | red_choice_left: forall c1 c2 s,
      red (CHOICE c1 c2, s) (c1, s)
  | red_choice_right: forall c1 c2 s,
      red (CHOICE c1 c2, s) (c2, s)
  | red_cstar_done: forall a c s,
      red (CSTAR a c, s) (SKIP, s)
  | red_cstar_step: forall a c s,
      red (CSTAR a c, s) (SEQ c (CSTAR a c), s).

(** Final configurations for the small-step semantics. *)
Inductive final : com * store -> result -> Prop :=
  | final_skip : forall s,
      final (SKIP, s) (RNormal s)
  | final_error : forall s,
      final (ERROR, s) (RError s).

Definition terminates_result (s: store) (c: com) (r: result) : Prop :=
  exists cs, star red (c, s) cs /\ final cs r.

Definition terminates (s: store) (c: com) (s': store) : Prop :=
  star red (c, s) (SKIP, s').

Definition diverges (s: store) (c: com) : Prop :=
  infseq red (c, s).

(** *** Natural (big-step) semantics *)

Inductive cexec: store -> com -> result -> Prop :=
  | cexec_skip: forall s,
      cexec s SKIP (RNormal s)
  | cexec_error: forall s,
      cexec s ERROR (RError s)
  | cexec_assign: forall s x a v,
      Lang.eval a s = Some v ->
      cexec s (ASSIGN x a) (RNormal (Lang.update x v s))
  | cexec_assign_err: forall s x a,
      Lang.eval a s = None ->
      cexec s (ASSIGN x a) (RError s)
  | cexec_nondet: forall s x n,
      cexec s (NONDET x) (RNormal (Lang.update x n s))
  | cexec_assume: forall s b,
      Lang.beval b s = Some true ->
      cexec s (ASSUME b) (RNormal s)
  | cexec_assume_err: forall s b,
      Lang.beval b s = None ->
      cexec s (ASSUME b) (RError s)
  | cexec_seq: forall c1 c2 s s' s'',
      cexec s  c1 (RNormal s') ->
      cexec s' c2 (RNormal s'') ->
      cexec s  (SEQ c1 c2) (RNormal s'')
  | cexec_seq_error: forall c1 c2 s sf,
      cexec s c1 (RError sf) ->
      cexec s (SEQ c1 c2) (RError sf)
  | cexec_seq_error_right: forall c1 c2 s s' sf,
      cexec s  c1 (RNormal s') ->
      cexec s' c2 (RError sf) ->
      cexec s  (SEQ c1 c2) (RError sf)
  | cexec_choice_left: forall s c1 c2 r,
      cexec s c1 r ->
      cexec s (CHOICE c1 c2) r
  | cexec_choice_right: forall s c1 c2 r,
      cexec s c2 r ->
      cexec s (CHOICE c1 c2) r
  | cexec_cstar_done: forall a c s,
      cexec s (CSTAR a c) (RNormal s)
  | cexec_cstar_step_ok : forall a c s s' s'',
      cexec s  c (RNormal s') ->
      cexec s' (CSTAR a c) (RNormal s'') ->
      cexec s  (CSTAR a c) (RNormal s'')
  | cexec_cstar_step_error : forall a c s sf,
      cexec s c (RError sf) ->
      cexec s (CSTAR a c) (RError sf)
  | cexec_cstar_step_iter_error : forall a c s s' sf,
      cexec s  c (RNormal s') ->
      cexec s' (CSTAR a c) (RError sf) ->
      cexec s  (CSTAR a c) (RError sf).

(** *** Annotations are semantically irrelevant

    No rule of [red] or [cexec] inspects an annotation, so an execution of
    [c] is an execution of [unannot c].  This is what lets a specification be
    stated about the bare program and proved with an annotated copy. *)

Fixpoint unannot (c: com) : com :=
  match c with
  | SKIP => SKIP
  | ERROR => ERROR
  | ASSIGN x a => ASSIGN x a
  | NONDET x => NONDET x
  | ASSUME b => ASSUME b
  | SEQ c1 c2 => SEQ (unannot c1) (unannot c2)
  | CHOICE c1 c2 => CHOICE (unannot c1) (unannot c2)
  | CSTAR _ c => CSTAR None (unannot c)
  end.

(** [step_iter c] is the relation "one successful execution of [c]" on
    stores.  Its reflexive-transitive closure is the Kleene star. *)
Definition step_iter (c: com) (s s': store) : Prop :=
  cexec s c (RNormal s').

End DEFS.

Arguments loopann : clear implicits.
Arguments com : clear implicits.
Arguments result : clear implicits.

(** ** Notations

    Declared outside [Section DEFS] so that they survive it.  [L] is
    implicit in every constructor, so these read exactly as they did when
    the language was fixed. *)

(** [Imp.v] declares a [com] custom entry for its own expression notations;
    the generic layer needs none, and declaring it twice would clash. *)
Declare Scope com_scope.
Delimit Scope com_scope with com.
Local Open Scope com_scope.

Infix ";;" := SEQ (at level 80, right associativity) : com_scope.

Notation "c1 '⊕' c2" := (CHOICE c1 c2)
  (at level 85, right associativity) : com_scope.
Notation "c '★'" := (CSTAR None c)
  (at level 90, right associativity) : com_scope.
Notation "c '★' '⟨' I '⟩'" := (CSTAR (Some (AInv I)) c)
  (at level 90, right associativity) : com_scope.
Notation "c '★' '⟨|' R '|⟩'" := (CSTAR (Some (AVar R)) c)
  (at level 90, right associativity) : com_scope.

Notation "st0 =[ c ]=> st1" := (cexec st0 c st1)
  (at level 40, c at level 99, st1 at level 39).
Notation "s1 =[ c ]=> 'ok' ↑ s2" := (cexec s1 c (RNormal s2))
  (at level 40, c at level 99, s2 at level 39).
Notation "s1 =[ c ]=> 'err' ↑ s2" := (cexec s1 c (RError s2))
  (at level 40, c at level 99, s2 at level 39).

(** The derived control structures.  [Lang.bnot] is what makes these
    statable for any language; see its comment in [Lang.v]. *)

Notation "'WHILE' b 'DO' c 'END'" :=
  (((ASSUME b ;; c) ★) ;; ASSUME (Lang.bnot b))
  (at level 95, right associativity) : com_scope.
Notation "'WHILE' '⟨' I '⟩' b 'DO' c 'END'" :=
  (((ASSUME b ;; c) ★ ⟨ I ⟩) ;; ASSUME (Lang.bnot b))
  (at level 95, right associativity) : com_scope.
Notation "'WHILE' '⟨|' R '|⟩' b 'DO' c 'END'" :=
  (((ASSUME b ;; c) ★ ⟨| R |⟩) ;; ASSUME (Lang.bnot b))
  (at level 95, right associativity) : com_scope.

(** Rocq does not handle an "optional ELSE" well when both notations start
    with exactly the same prefix [IF ... THEN ...], so the no-ELSE form is
    [IF ... THEN ... END] and shares levels with the ELSE form. *)
Notation "'IF' b 'THEN' c1 'ELSE' c2 'END'" :=
  (CHOICE (ASSUME b ;; c1) (ASSUME (Lang.bnot b) ;; c2))
  (at level 89, right associativity,
   b at level 99, c1 at level 89, c2 at level 89) : com_scope.
Notation "'IF' b 'THEN' c1 'END'" :=
  (IF b THEN c1 ELSE SKIP END)
  (at level 89, right associativity,
   b at level 99, c1 at level 89, only parsing) : com_scope.

Notation "'ASSERT' b" :=
  (CHOICE (ASSUME b) (ASSUME (Lang.bnot b) ;; ERROR))
  (at level 100, right associativity) : com_scope.

(** ** Metatheory *)

Section THEORY.

Context {L : lang}.

Local Notation store := (Lang.store L).
Local Notation com := (com L).
Local Notation result := (result L).

Local Open Scope com_scope.

Lemma cexec_unannot:
  forall (s : store) (c : com) (r : result),
  cexec s c r -> cexec s (unannot c) r.
Proof.
  intros s c r H. induction H; cbn [unannot];
    eauto using cexec_skip, cexec_error, cexec_assign, cexec_assign_err,
                cexec_nondet, cexec_assume, cexec_assume_err,
                cexec_seq, cexec_seq_error, cexec_seq_error_right,
                cexec_choice_left, cexec_choice_right, cexec_cstar_done,
                cexec_cstar_step_ok, cexec_cstar_step_error,
                cexec_cstar_step_iter_error.
Qed.

(** *** A sequence of reductions under a [SEQ] *)

(** Stated over whole configurations rather than over a pair of components,
    so that plain [induction] applies.  Going through [dependent induction]
    instead would drag in [Eq_rect_eq]; the development is axiom-free and
    [Assumptions.v] checks that it stays so. *)
Lemma red_seq_steps_gen:
  forall (c2 : com) (cs cs' : com * store),
  star red cs cs' ->
  star red (fst cs ;; c2, snd cs) (fst cs' ;; c2, snd cs').
Proof.
  intros c2 cs cs' H. induction H.
  - apply star_refl.
  - destruct a as [ca sa]; destruct b as [cb sb]; simpl in *.
    eapply star_step; [ apply red_seq_step; exact H | exact IHstar ].
Qed.

Lemma red_seq_steps:
  forall (c2 : com) (s : store) (c : com) (s' : store) (c' : com),
  star red (c, s) (c', s') -> star red ((c ;; c2), s) ((c' ;; c2), s').
Proof.
  intros c2 s c s' c' H. exact (red_seq_steps_gen c2 (c, s) (c', s') H).
Qed.

(** *** Kleene-algebra view of [CSTAR] *)

Lemma cexec_cstar_of_star:
  forall a (c : com) (s s' : store),
  star (step_iter c) s s' -> cexec s (CSTAR a c) (RNormal s').
Proof.
  induction 1.
  - apply cexec_cstar_done.
  - eapply cexec_cstar_step_ok; eauto.
Qed.

(** Both the command and the result are turned into equations so that the
    induction is over fully general indices. *)
Lemma star_of_cexec_cstar_gen:
  forall (s : store) (cc : com) (r : result),
  cexec s cc r ->
  forall a (c : com) (s' : store),
  cc = CSTAR a c -> r = RNormal s' -> star (step_iter c) s s'.
Proof.
  intros s cc r H. induction H; intros a0 c0 s0 Ecc Er;
    try discriminate Ecc; try discriminate Er.
  - (* CSTAR done *)
    injection Ecc as ? ?; subst. injection Er as ?; subst. apply star_refl.
  - (* CSTAR step, body succeeded *)
    injection Ecc as ? ?; subst. injection Er as ?; subst.
    eapply star_step; [ exact H | eapply IHcexec2; reflexivity ].
Qed.

Lemma star_of_cexec_cstar:
  forall a (c : com) (s : store) (r : result),
  cexec s (CSTAR a c) r ->
  forall s', r = RNormal s' -> star (step_iter c) s s'.
Proof.
  intros a c s r H s' Er.
  eapply star_of_cexec_cstar_gen; [ exact H | reflexivity | exact Er ].
Qed.

Theorem cexec_cstar_iff_star:
  forall a (c : com) (s s' : store),
  cexec s (CSTAR a c) (RNormal s') <-> star (step_iter c) s s'.
Proof.
  intros a c s s'. split.
  - intro H. eapply star_of_cexec_cstar; eauto.
  - apply cexec_cstar_of_star.
Qed.

Lemma cexec_cstar_err_to_star_gen:
  forall (s : store) (cc : com) (r : result),
  cexec s cc r ->
  forall a (c : com) (sf : store),
  cc = CSTAR a c -> r = RError sf ->
  exists s', star (step_iter c) s s' /\ cexec s' c (RError sf).
Proof.
  intros s cc r H. induction H; intros a0 c0 sf0 Ecc Er;
    try discriminate Ecc; try discriminate Er.
  - (* body errored on the first turn *)
    injection Ecc as ? ?; subst. injection Er as ?; subst.
    exists s. split; [ apply star_refl | exact H ].
  - (* body succeeded, a later turn errored *)
    injection Ecc as ? ?; subst. injection Er as ?; subst.
    destruct (IHcexec2 a0 c0 sf0 Logic.eq_refl Logic.eq_refl)
      as (sm & STAR & ERR).
    exists sm. split; [ eapply star_step; eauto | exact ERR ].
Qed.

Lemma cexec_cstar_err_to_star:
  forall a (c : com) (s : store) (r : result),
  cexec s (CSTAR a c) r ->
  forall sf', r = RError sf' ->
  exists s', star (step_iter c) s s' /\ cexec s' c (RError sf').
Proof.
  intros a c s r H sf' Er.
  eapply cexec_cstar_err_to_star_gen; [ exact H | reflexivity | exact Er ].
Qed.

Theorem cexec_cstar_err_iff:
  forall a (c : com) (s sf : store),
  cexec s (CSTAR a c) (RError sf) <->
  exists s', star (step_iter c) s s' /\ cexec s' c (RError sf).
Proof.
  intros a c s sf. split.
  - intro H. eapply cexec_cstar_err_to_star; eauto.
  - intros (s' & STAR & ERR). induction STAR.
    + apply cexec_cstar_step_error. exact ERR.
    + eapply cexec_cstar_step_iter_error; eauto.
Qed.

(** *** [step_iter] as a Kleene-algebra homomorphism *)

Lemma step_iter_skip:
  step_iter (@SKIP L) ≡ rid.
Proof.
  intros s s'. unfold step_iter, rid; split.
  - intro H. inversion H; subst. reflexivity.
  - intros ->. apply cexec_skip.
Qed.

(** [ASSUME b] is the KAT-test [\[b\]] — the partial-identity relation that
    holds only on states where [b] is *defined and* true.  The [Some] is the
    visible trace of evaluation being partial. *)
Lemma step_iter_assume:
  forall b (s s' : store),
  step_iter (ASSUME b) s s' <-> s = s' /\ Lang.beval b s = Some true.
Proof.
  intros b s s'. unfold step_iter; split.
  - intro H. inversion H; subst. split; [ reflexivity | assumption ].
  - intros (-> & HB). apply cexec_assume. exact HB.
Qed.

Lemma step_iter_seq:
  forall c1 c2 : com, step_iter (c1 ;; c2) ≡ step_iter c1 ⨟ step_iter c2.
Proof.
  intros c1 c2 s s''. unfold step_iter, rcomp; split.
  - intro H. inversion H; subst. exists s'. split; assumption.
  - intros (s' & H1 & H2). eapply cexec_seq; eauto.
Qed.

Lemma step_iter_choice:
  forall (c1 c2 : com) (s s' : store),
  step_iter (CHOICE c1 c2) s s' <->
  step_iter c1 s s' \/ step_iter c2 s s'.
Proof.
  intros c1 c2 s s'. unfold step_iter; split.
  - intro H. inversion H; subst.
    + left. assumption.
    + right. assumption.
  - intros [H | H].
    + apply cexec_choice_left. assumption.
    + apply cexec_choice_right. assumption.
Qed.

Lemma step_iter_cstar:
  forall a (c : com), step_iter (CSTAR a c) ≡ star (step_iter c).
Proof.
  intros a c s s'. unfold step_iter. apply cexec_cstar_iff_star.
Qed.

Lemma cstar_seq_comm:
  forall a (c : com), step_iter ((CSTAR a c) ;; c) ≡ step_iter (c ;; (CSTAR a c)).
Proof.
  intros a c.
  rewrite !step_iter_seq. rewrite !step_iter_cstar.
  symmetry. apply rcomp_star_shift.
Qed.

(** *** Big-step implies small-step *)

Theorem cexec_to_reds:
  forall (s : store) (c : com) (r : result),
  cexec s c r -> terminates_result s c r.
Proof.
  induction 1.
  - (* SKIP *)
    exists (SKIP, s). split; [ apply star_refl | apply final_skip ].
  - (* ERROR *)
    exists (ERROR, s). split; [ apply star_refl | apply final_error ].
  - (* ASSIGN, defined *)
    exists (SKIP, Lang.update x v s). split.
    + apply star_one. apply red_assign. assumption.
    + apply final_skip.
  - (* ASSIGN, undefined *)
    exists (ERROR, s). split.
    + apply star_one. apply red_assign_err. assumption.
    + apply final_error.
  - (* NONDET *)
    exists (SKIP, Lang.update x n s). split.
    + apply star_one. apply red_nondet.
    + apply final_skip.
  - (* ASSUME, true *)
    exists (SKIP, s). split.
    + apply star_one. apply red_assume. assumption.
    + apply final_skip.
  - (* ASSUME, undefined *)
    exists (ERROR, s). split.
    + apply star_one. apply red_assume_err. assumption.
    + apply final_error.
  - (* SEQ normal *)
    destruct IHcexec1 as (cs1 & STAR1 & FINAL1).
    inversion FINAL1; subst cs1.
    destruct IHcexec2 as (cs2 & STAR2 & FINAL2).
    inversion FINAL2; subst cs2.
    exists (SKIP, s''). split.
    + eapply star_trans.
      * apply red_seq_steps with (c2 := c2) in STAR1. exact STAR1.
      * eapply star_step. apply red_seq_done. subst. exact STAR2.
    + apply final_skip.
  - (* SEQ error (left) *)
    destruct IHcexec as (cs1 & STAR1 & FINAL1).
    inversion FINAL1; subst.
    exists (ERROR, sf). split.
    + eapply star_trans.
      * apply red_seq_steps with (c2 := c2) in STAR1. exact STAR1.
      * apply star_one. apply red_seq_error.
    + apply final_error.
  - (* SEQ error (right) *)
    destruct IHcexec1 as (cs1 & STAR1 & FINAL1).
    inversion FINAL1; subst.
    destruct IHcexec2 as (cs2 & STAR2 & FINAL2).
    inversion FINAL2; subst.
    exists (ERROR, sf). split.
    + eapply star_trans.
      * apply red_seq_steps with (c2 := c2) in STAR1. exact STAR1.
      * eapply star_step; [ apply red_seq_done | exact STAR2 ].
    + apply final_error.
  - (* CHOICE left *)
    destruct IHcexec as (cs & STAR & FINAL').
    exists cs. split.
    + eapply star_step. apply red_choice_left. exact STAR.
    + exact FINAL'.
  - (* CHOICE right *)
    destruct IHcexec as (cs & STAR & FINAL').
    exists cs. split.
    + eapply star_step. apply red_choice_right. exact STAR.
    + exact FINAL'.
  - (* CSTAR done *)
    exists (SKIP, s). split.
    + apply star_one. apply red_cstar_done.
    + apply final_skip.
  - (* CSTAR step ok *)
    destruct IHcexec1 as (cs1 & STAR1 & FINAL1).
    inversion FINAL1; subst cs1.
    destruct IHcexec2 as (cs2 & STAR2 & FINAL2).
    exists cs2. split.
    + eapply star_trans.
      * apply star_one. apply red_cstar_step.
      * eapply star_trans.
        -- apply red_seq_steps with (c2 := CSTAR a c) in STAR1. exact STAR1.
        -- eapply star_step. apply red_seq_done. subst. exact STAR2.
    + exact FINAL2.
  - (* CSTAR step error (body errors immediately) *)
    destruct IHcexec as (cs1 & STAR1 & FINAL1).
    inversion FINAL1; subst.
    exists (ERROR, sf). split.
    + eapply star_trans.
      * apply star_one. apply red_cstar_step.
      * eapply star_trans.
        -- apply red_seq_steps with (c2 := CSTAR a c) in STAR1. exact STAR1.
        -- apply star_one. apply red_seq_error.
    + apply final_error.
  - (* CSTAR step iter error *)
    destruct IHcexec1 as (cs1 & STAR1 & FINAL1).
    inversion FINAL1; subst.
    destruct IHcexec2 as (cs2 & STAR2 & FINAL2).
    inversion FINAL2; subst.
    exists (ERROR, sf). split.
    + eapply star_trans.
      * apply star_one. apply red_cstar_step.
      * eapply star_trans.
        -- apply red_seq_steps with (c2 := CSTAR a c) in STAR1. exact STAR1.
        -- eapply star_step; [ apply red_seq_done | exact STAR2 ].
    + apply final_error.
Qed.

Lemma plus_cstar_iteration:
  forall a (c : com) (s s' : store),
  star red (c, s) (SKIP, s') ->
  plus red (CSTAR a c, s) (CSTAR a c, s').
Proof.
  intros a c s s' STARC.
  eapply plus_left.
  - apply red_cstar_step.
  - eapply star_trans.
    + apply red_seq_steps with (c2 := CSTAR a c) in STARC. exact STARC.
    + apply star_one. apply red_seq_done.
Qed.

Lemma diverges_cstar_via_cexec_cstar_step:
  forall a (c : com) (s : store),
  (forall st, exists st', cexec st c (RNormal st')) ->
  diverges s (CSTAR a c).
Proof.
  intros a c s BODY_TERMINATES.
  unfold diverges.
  eapply (@infseq_coinduction_principle
            (com * store)
            red
            (fun cs => exists st, cs = (CSTAR a c, st))); eauto.
  intros cs (st0 & EQ). subst cs.
  destruct (BODY_TERMINATES st0) as (st1 & EXECc).
  pose proof (cexec_to_reds st0 c (RNormal st1) EXECc) as TERM.
  destruct TERM as (cs1 & STARc & FINALc).
  inversion FINALc; subst cs1.
  exists (CSTAR a c, st1). split.
  + apply plus_cstar_iteration; subst; auto.
  + exists st1. reflexivity.
Qed.

(** *** Small-step implies big-step *)

Lemma red_append_cexec_gen:
  forall (cs cs' : com * store), red cs cs' ->
  forall r, cexec (snd cs') (fst cs') r -> cexec (snd cs) (fst cs) r.
Proof.
  intros cs cs' STEP. induction STEP; simpl; intros r EXEC.
  - (* red_assign *)
    inversion EXEC; subst. apply cexec_assign. assumption.
  - (* red_assign_err *)
    inversion EXEC; subst. apply cexec_assign_err. assumption.
  - (* red_nondet *)
    inversion EXEC; subst. eapply cexec_nondet.
  - (* red_assume *)
    inversion EXEC; subst. eapply cexec_assume; eauto.
  - (* red_assume_err *)
    inversion EXEC; subst. apply cexec_assume_err. assumption.
  - (* red_seq_done *)
    destruct r as [st'|].
    + apply cexec_seq with s. apply cexec_skip. exact EXEC.
    + apply cexec_seq_error_right with s. apply cexec_skip. exact EXEC.
  - (* red_seq_error *)
    inversion EXEC; subst.
    eapply cexec_seq_error. apply cexec_error.
  - (* red_seq_step *)
    simpl in IHSTEP.
    inversion EXEC; subst.
    + eapply cexec_seq.
      * eapply IHSTEP; eauto.
      * eassumption.
    + eapply cexec_seq_error. eapply IHSTEP; eauto.
    + eapply cexec_seq_error_right.
      * eapply IHSTEP; eauto.
      * eassumption.
  - (* red_choice_left *)
    apply cexec_choice_left. exact EXEC.
  - (* red_choice_right *)
    apply cexec_choice_right. exact EXEC.
  - (* red_cstar_done *)
    inversion EXEC; subst. apply cexec_cstar_done.
  - (* red_cstar_step *)
    inversion EXEC; subst.
    + eapply cexec_cstar_step_ok; eauto.
    + eapply cexec_cstar_step_error; eauto.
    + eapply cexec_cstar_step_iter_error; eauto.
Qed.

Lemma red_append_cexec:
  forall (c1 : com) (s1 : store) (c2 : com) (s2 : store),
  red (c1, s1) (c2, s2) ->
  forall r, cexec s2 c2 r -> cexec s1 c1 r.
Proof.
  intros c1 s1 c2 s2 H r EXEC.
  exact (red_append_cexec_gen (c1, s1) (c2, s2) H r EXEC).
Qed.

Lemma reds_to_cexec_gen:
  forall (cs cs' : com * store), star red cs cs' ->
  forall r, final cs' r -> cexec (snd cs) (fst cs) r.
Proof.
  intros cs cs' H. induction H; intros r FIN.
  - inversion FIN; subst; simpl; constructor.
  - eapply red_append_cexec_gen; [ exact H | ]. apply IHstar. exact FIN.
Qed.

Theorem reds_to_cexec:
  forall (s : store) (c : com) (r : result),
  terminates_result s c r -> cexec s c r.
Proof.
  intros s c r (cs & STAR & FINAL).
  exact (reds_to_cexec_gen (c, s) cs STAR r FINAL).
Qed.

Corollary reds_to_cexec_normal:
  forall (s : store) (c : com) (s' : store),
  star red (c, s) (SKIP, s') -> cexec s c (RNormal s').
Proof.
  intros s c s' STAR.
  apply reds_to_cexec. exists (SKIP, s'). split; [exact STAR | constructor].
Qed.

Corollary reds_to_cexec_error:
  forall (s : store) (c : com) (s' : store),
  star red (c, s) (ERROR, s') -> cexec s c (RError s').
Proof.
  intros s c s' STAR.
  apply reds_to_cexec. exists (ERROR, s'). split; [exact STAR | constructor].
Qed.

(** *** The two semantics agree *)

Theorem cexec_iff_reds:
  forall (s : store) (c : com) (r : result),
  cexec s c r <-> terminates_result s c r.
Proof.
  intros. split; [ apply cexec_to_reds | apply reds_to_cexec ].
Qed.

End THEORY.
