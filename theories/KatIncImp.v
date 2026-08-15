(** * Connection: KatInc's KAT-based incorrectness logic ↔ Inc.v's semantic
    IncTriple, in IMP's [com] / [store].

    [prog'] mirrors KatInc's [prog] but with syntactic [aexp]/[bexp], so the
    translation [to_com : prog' → com] (and [to_kat : prog' → prog]) is total.
    We show that KatInc's relational semantics [bstep] coincides with IMP's
    [cexec] on normal results, then lift [Incorrectness] to [IncTriple]. *)

From Stdlib Require Import Program.Equality.
From IncLogic Require Import Imp Sequences Hoare Inc KatInc.
From RelationAlgebra Require Import rel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope com_scope.

(** ** A copy of KatInc's prog using syntactic expressions/tests. *)
Inductive prog' : Type :=
| skp'  : prog'
| aff'  : ident -> aexp -> prog'
| seq'  : prog' -> prog' -> prog'
| ite'  : bexp -> prog' -> prog' -> prog'
| whl'  : bexp -> prog' -> prog'.

(** ** Translation to IMP's [com] (richer language). *)
Fixpoint to_com (p: prog') : com :=
  match p with
  | skp'         => SKIP
  | aff' x a     => ASSIGN x a
  | seq' p q     => to_com p ;; to_com q
  | ite' b p q   => CHOICE (ASSUME b ;; to_com p) (ASSUME (NOT b) ;; to_com q)
  | whl' b p     => (((ASSUME b ;; to_com p) ★) ;; ASSUME (NOT b))
  end.

(** ** Translation to KatInc's [prog], specialised at [store]. *)
Fixpoint to_kat (p: prog') : prog ident store :=
  match p with
  | skp'         => skp ident store
  | aff' x a     => aff ident store x (aeval a)
  | seq' p q     => seq ident store (to_kat p) (to_kat q)
  | ite' b p q   => ite ident store (fun s => beval b s) (to_kat p) (to_kat q)
  | whl' b p     => whl ident store (fun s => beval b s) (to_kat p)
  end.

(** ** KatInc's [bstep] at our chosen instantiation. *)
Definition kat_bstep (p: prog') : hrel store store :=
  bstep ident store Imp.update (to_kat p).

(** ** From KatInc's inductive semantics to IMP's [cexec]. *)

(** Helper: a [whl b body] derivation in [bstep'] produces a Kleene-star
    chain of [(ASSUME b ;; body)] iterations ending in a [b]-false state. *)
Lemma whl_to_star :
  forall (b: bexp) (kbody: prog ident store) (cbody: com),
    (forall s s',
       bstep' ident store Imp.update kbody s s' ->
       cexec s cbody (RNormal s')) ->
    forall s s',
    bstep' ident store Imp.update
      (whl ident store (fun s => beval b s) kbody) s s' ->
    star (step_iter (ASSUME b ;; cbody)) s s' /\ beval b s' = false.
Proof.
  intros b kbody cbody IHbody.
  fix REC 3.
  intros s s' HW.
  inversion HW; subst.
  - (* s_whl_ff *) split; [ apply star_refl | exact H3 ].
  - (* s_whl_tt *)
    inversion H4; subst.
    destruct (REC _ _ H6) as [STAR Hbf].
    split; [| exact Hbf ].
    eapply star_step; [| exact STAR ].
    unfold step_iter.
    eapply cexec_seq;
      [ apply cexec_assume; assumption | apply IHbody; assumption ].
Qed.

Lemma bstep'_to_cexec : forall p' s s',
  bstep' ident store Imp.update (to_kat p') s s' ->
  cexec s (to_com p') (RNormal s').
Proof.
  induction p'; intros s s' H; cbn in *.
  - inversion H; subst; apply cexec_skip.
  - inversion H; subst; apply cexec_assign.
  - inversion H; subst.
    eapply cexec_seq; [ apply IHp'1; eassumption | apply IHp'2; eassumption ].
  - (* ite' *)
    inversion H; subst.
    + apply cexec_choice_right.
      eapply cexec_seq.
      * apply cexec_assume. cbn. now rewrite H5.
      * apply IHp'2; assumption.
    + apply cexec_choice_left.
      eapply cexec_seq.
      * apply cexec_assume; assumption.
      * apply IHp'1; assumption.
  - (* whl' *)
    destruct (whl_to_star _ _ _ IHp' _ _ H) as [STAR Hbfalse].
    apply (cexec_cstar_iff_star None) in STAR.
    eapply cexec_seq.
    + exact STAR.
    + apply cexec_assume. cbn. now rewrite Hbfalse.
Qed.

Lemma kat_bstep_to_cexec : forall p s s',
  kat_bstep p s s' -> cexec s (to_com p) (RNormal s').
Proof.
  intros p s s' H.
  unfold kat_bstep in H.
  apply (bstep_eq ident store Imp.update) in H.
  eapply bstep'_to_cexec; eauto.
Qed.

(** ** The main connection: Incorrectness ⇒ IncTriple.

    We use [Incorrectness_eq] from [KatInc.v] to expose the semantic
    formulation: every [C]-state is reachable from a [B]-state via [bstep]. *)
Theorem Incorrectness_to_IncTriple :
  forall (B C : store -> bool) (p : prog'),
    (forall s', C s' = true ->
                exists2 s, B s = true & kat_bstep p s s') ->
    ⟦⟦ fun s => B s = true ⟧⟧ (to_com p) ⟦⟦ ok ↑ fun s => C s = true ⟧⟧.
Proof.
  intros B C p INC r HC.
  destruct r as [s' | s']; [| exfalso; exact HC ].
  destruct (INC s' HC) as [s HB Hp].
  exists s. split; [ exact HB | ].
  apply kat_bstep_to_cexec. exact Hp.
Qed.