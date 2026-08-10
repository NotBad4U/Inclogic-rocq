From Stdlib Require Import Arith ZArith Psatz Bool String List Program.Equality FunctionalExtensionality.
From mathcomp Require Import ssrbool eqtype choice.
From mathcomp Require Import finmap.
From IncLogic Require Import Imp Sequences.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope com_scope.

Ltac inv H := inversion H; clear H; subst.

Definition swap_xy :=
    ASSIGN "t" (VAR "x");; ASSIGN "x" (VAR "y");; ASSIGN "y" (VAR "t").


Lemma swap_xy_correct:
  forall s, exists s',
  star red (swap_xy, s) (SKIP, s') /\ s' "x" = s "y" /\ s' "y" = s "x".
Proof.
  intros. econstructor; split.
- eapply star_step. apply red_seq_step. apply red_assign.
  eapply star_step. apply red_seq_done.
  eapply star_step. apply red_seq_step. apply red_assign.
  eapply star_step. apply red_seq_done.
  eapply star_step. apply red_assign.
  apply star_refl.
- cbn [aeval]. split.
  + rewrite (update_other "y"); [|intros H; discriminate H].
    rewrite update_same.
    rewrite update_other; [reflexivity | intros H; discriminate H].
  + rewrite update_same.
    rewrite update_other; [|intros H; discriminate H].
    apply update_same.
Qed.


Definition slow_add :=
  WHILE (LESSEQUAL (CONST 1) (VAR "x")) DO
        (ASSIGN "x" (MINUS (VAR "x") (CONST 1)) ;;
         ASSIGN "y" (PLUS  (VAR "y") (CONST 1))) END.

Lemma slow_add_correct:
  forall (s : store),
  s "x" >= 0 ->
  exists s' : store, star red (slow_add, s) (SKIP, s') /\ s' "y" = s "y" + s "x".
Proof.
  (* The loop body, run [n] times, keeps [x + y] constant while driving [x] to
     0.  We reason in the natural semantics ([cexec] / Kleene star) and then
     transfer to a reduction sequence via [cexec_to_reds]. *)
  assert (LOOP: forall n (t: store),
    t "x" = Z.of_nat n ->
    exists s',
      star (step_iter (ASSUME (LESSEQUAL (CONST 1) (VAR "x")) ;;
            (ASSIGN "x" (MINUS (VAR "x") (CONST 1)) ;;
             ASSIGN "y" (PLUS (VAR "y") (CONST 1))))) t s'
      /\ s' "x" = 0 /\ s' "y" = t "y" + t "x").
  { induction n as [|n IH]; intros t Ht.
    - (* zero iterations left: [x = 0] *)
      exists t. split; [ apply star_refl | ].
      split; [ rewrite Ht; reflexivity | rewrite Ht; cbn; lia ].
    - (* one more iteration *)
      set (t2 := update "y" (t "y" + 1) (update "x" (t "x" - 1) t)).
      assert (Htx2 : t2 "x" = t "x" - 1).
      { unfold t2. rewrite update_other by discriminate. apply update_same. }
      assert (Hty2 : t2 "y" = t "y" + 1).
      { unfold t2. apply update_same. }
      assert (Hstep : step_iter (ASSUME (LESSEQUAL (CONST 1) (VAR "x")) ;;
                       (ASSIGN "x" (MINUS (VAR "x") (CONST 1)) ;;
                        ASSIGN "y" (PLUS (VAR "y") (CONST 1)))) t t2).
      { unfold step_iter. eapply cexec_seq.
        - apply cexec_assume. cbn [beval aeval]. apply Z.leb_le.
          rewrite Ht, Nat2Z.inj_succ. lia.
        - eapply cexec_seq.
          + apply cexec_assign.
          + replace t2 with
              (update "y" (aeval (PLUS (VAR "y") (CONST 1))
                            (update "x" (aeval (MINUS (VAR "x") (CONST 1)) t) t))
                          (update "x" (aeval (MINUS (VAR "x") (CONST 1)) t) t)).
            * apply cexec_assign.
            * unfold t2. cbn [aeval]. rewrite update_other by discriminate. reflexivity. }
      assert (Ht2val : t2 "x" = Z.of_nat n).
      { rewrite Htx2, Ht, Nat2Z.inj_succ. lia. }
      destruct (IH t2 Ht2val) as (s' & STAR & Hs'x & Hs'y).
      exists s'. split; [ eapply star_step; [ exact Hstep | exact STAR ] | ].
      split; [ exact Hs'x | ].
      rewrite Hs'y, Hty2, Htx2. lia. }
  intros s Hpos.
  assert (Hid : s "x" = Z.of_nat (Z.to_nat (s "x"))).
  { rewrite Z2Nat.id by lia. reflexivity. }
  destruct (LOOP (Z.to_nat (s "x")) s Hid) as (sm & STAR & Hsmx & Hsmy).
  assert (EXEC : cexec s slow_add (RNormal sm)).
  { unfold slow_add. eapply cexec_seq.
    - apply cexec_cstar_of_star. exact STAR.
    - apply cexec_assume. cbn [beval aeval]. rewrite Hsmx. reflexivity. }
  exists sm. split; [ | exact Hsmy ].
  apply cexec_to_reds in EXEC. destruct EXEC as (cs & STARr & FIN).
  inversion FIN; subst. exact STARr.
Qed.

Definition assertion : Type := store -> Prop.

Definition postassertion : Type := result -> Prop.

Definition aand (P Q: assertion) : assertion :=
  fun s => P s /\ Q s.

Definition aor (P Q: assertion) : assertion :=
  fun s => P s \/ Q s.

(** The assertion "arithmetic expression [a] evaluates to value [v]". *)

Definition aequal (a: aexp) (v: Z) : assertion :=
  fun s => aeval a s = v.

Definition atrue (b: bexp) : assertion :=
  fun s => beval b s = true.

Definition afalse (b: bexp) : assertion :=
  fun s => beval b s = false.

(** The assertion written "[ P[x <- a] ]" in the literature.
    Substituting [a] for [x] in [P] amounts to evaluating [P] in
    stores where the variable [x] is equal to the value of expression [a]. *)

Definition aupdate (x: ident) (a: aexp) (P: assertion) : assertion :=
  fun s => P (update x (aeval a s) s).

Notation "P [ x ↦ a ]" := (aupdate x a P) (at level 10).

Example aupdate_example:
  (aequal (VAR "y") 5 [ "y" ↦ (PLUS (VAR "y") (CONST 2)) ])
  (update "y" 3%Z (finmap.fmap0 : store)).
Proof.
  unfold aupdate, aequal. cbn [aeval]. rewrite !update_same. reflexivity.
Qed.

(** Pointwise implication.  Unlike conjunction and disjunction, this is
    not a predicate over the store, just a Coq proposition. *)

Definition aimp (P Q: assertion) : Prop :=
  forall s, P s -> Q s.

Definition paimp (P Q: postassertion) : Prop :=
  forall r, P r -> Q r.

(** A few notations to improve legibility. *)

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).
Notation "P --* Q" := (paimp P Q) (at level 95, no associativity).
Notation "P //\\ Q" := (aand P Q) (at level 80, right associativity).
Notation "P \\// Q" := (aor P Q) (at level 75, right associativity).

Ltac Tauto :=
  let s := fresh "s" in
  unfold aand, aor, aimp in *;
  intro s;
  repeat (match goal with [ H: (forall (s': store), _) |- _ ] => specialize (H s) end);
  intuition auto.

(** The rules of weak Hoare logic *)

(** Here are the base rules for Hoare logic.
    They define a relation [Hoare P c Q], where
-   [P] is the precondition, assumed to hold "before" executing [c];
-   [c] is the program or program fragment we reason about;
-   [Q] is the postcondition, guaranteed to hold "after" executing [c].

  This is a "weak" logic, meaning that it does not guarantee termination
  of the command [c].  What is guaranteed is that if [c] terminates,
  then its final store satisfies postcondition [Q]. *)

Reserved Notation "⦃ P ⦄ c ⦃ Q ⦄" (at level 90, c at next level).

Definition aforall {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => forall (a: A), P a s.

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => exists (a: A), P a s.

Inductive WeakHoareRes: assertion -> com -> postassertion -> Prop :=
| Hoare_skip_r: forall P,
  (* ------------------ *)
  ⦃ P ⦄ SKIP ⦃ P ⦄
| Hoare_assign_r: forall P x a,
  (* ------------------------------ *)
    ⦃ aupdate x a P ⦄ ASSIGN x a ⦃ P ⦄
| Hoare_nondet: forall x Q,
      ⦃ aforall (fun n => aupdate x (CONST n) Q) ⦄ NONDET x ⦃ Q ⦄
| Hoare_seq_ok: forall P Q R c1 c2,
    ⦃ P ⦄ c1 ⦃ Q ⦄ ->
    ⦃ Q ⦄ c2 ⦃ R ⦄ ->
    (* ------------------ *)
    ⦃ P ⦄ (c1 ;; c2) ⦃ R ⦄
| Hoare_seq_err: forall P c1 c2,
    WeakHoareRes P c1 (fun r => match r with RError _ => True | _ => False end) ->
    (* ------------------ *)
    WeakHoareRes P (c1 ;; c2) (fun r => match r with RError _ => True | _ => False end)
| Hoare_consequence_res: forall P Q P' Q' c,
    ⦃ P ⦄ c ⦃ Q ⦄ ->
    P' -->> P ->
    Q -->> Q' ->
    (* -------------*)
    ⦃ P' ⦄ c ⦃ Q' ⦄
| Hoare_choice_res: forall P Q c1 c2,
    ⦃ P ⦄ c1 ⦃ Q ⦄ ->
    ⦃ P ⦄ c2 ⦃ Q ⦄ ->
    (* ---------------------- *)
    ⦃ P ⦄ (c1 ⊕ c2) ⦃ Q ⦄
| Hoare_cstar_ress: forall INV c,
    ⦃ INV ⦄ c ⦃ INV ⦄ ->
    (* ------------------ *)
    ⦃ INV ⦄ (CSTAR c) ⦃ INV ⦄
| Hoare_assume_r: forall (b: bexp) Q,
    (* [ASSUME b] succeeds without error when the guard holds and otherwise
       blocks; its weakest precondition is "if the guard holds, then [Q]". *)
    ⦃ (fun s => beval b s = true -> Q s) ⦄ ASSUME b ⦃ Q ⦄
| Hoare_error_r: forall Q,
    (* [ERROR] always errors, so a no-error triple is derivable only from the
       empty (unsatisfiable) precondition. *)
    ⦃ (fun _ : store => False) ⦄ ERROR ⦃ Q ⦄
where "⦃ P ⦄ c ⦃ Q ⦄" :=
  (WeakHoareRes P c (fun r => match r with
                          | RNormal s => Q s
                          | RError _ => False
                          end)).

Lemma Hoare_consequence_pre: forall P P' Q c,
      ⦃ P ⦄ c ⦃ Q ⦄ ->
      P' -->> P ->
      ⦃ P' ⦄ c ⦃ Q ⦄.
Proof.
  intros. apply Hoare_consequence_res with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Lemma Hoare_consequence_post: forall P Q Q' c,
      ⦃ P ⦄ c ⦃ Q ⦄ ->
      Q -->> Q' ->
      ⦃ P ⦄ c ⦃ Q' ⦄.
Proof.
  intros. apply Hoare_consequence_res with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Example Hoare_swap_xy: forall m n,
  ⦃ (aequal (VAR "x") m //\\ aequal (VAR "y") n) ⦄ swap_xy ⦃ (aequal (VAR "x") n //\\ aequal (VAR "y") m) ⦄.
Proof.
  intros.
  eapply Hoare_consequence_pre.
- unfold swap_xy. eapply Hoare_seq_ok. apply Hoare_assign_r.
  eapply Hoare_seq_ok. apply Hoare_assign_r. apply Hoare_assign_r.
- unfold aequal, aupdate, aand, aimp; cbn [aeval].
  intros s [Hx Hy].
  rewrite (update_other "y"); [|intros H; discriminate H].
  rewrite update_same. rewrite update_same.
  rewrite update_other; [|intros H; discriminate H].
  rewrite update_other; [|intros H; discriminate H].
  rewrite update_same.
  split; assumption.
Qed.

(** * Soundness of Hoare logic *)

(** We give a semantic interpretation to the statements [Hoare P c Q]
    of Hoare logic.  The interpretation is the relation [triple P c Q]
    defined below in terms of IMP's natural semantics
    (the relation [cexec s c s']). *)

Definition triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s r, cexec s c r -> P s -> (exists s', r = RNormal s' /\ Q s').

Notation "⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄" := (triple P c Q) (at level 90, c at next level).

Lemma triple_skip: forall P,
     ⦃⦃ P ⦄⦄ SKIP ⦃⦃ P ⦄⦄.
Proof.
  unfold triple; intros. exists s. inversion H; subst. auto.
Qed.


Lemma triple_assign: forall P x a,
      ⦃⦃ aupdate x a P ⦄⦄ ASSIGN x a ⦃⦃ P ⦄⦄.
Proof.
  unfold triple, aupdate; intros P x a s r EXEC PRE.
  inversion EXEC; subst.
  eexists. split; [ reflexivity | exact PRE ].
Qed.

Lemma Hoare_nondet_inv: forall x P Q,
  ⦃ P ⦄ NONDET x ⦃ Q ⦄ -> (P -->> aforall (fun n => aupdate x (CONST n) Q)).
Proof.
  intros x P Q H.
  remember (NONDET x) as c eqn:Hc.
  remember (fun r : result => match r with
                              | RNormal s => Q s
                              | RError _ => False
                              end) as Po eqn:HPo.
  revert Q HPo. revert x Hc.
  induction H; intros xg Hc Qg HPo; try discriminate Hc.
  - (* Hoare_nondet *)
    injection Hc as Hxx; subst xg.
    assert (HQeq : Q = Qg).
    { apply functional_extensionality. intros s.
      change (Q s) with ((fun r : result => match r with
                                            | RNormal s => Q s
                                            | RError _ => False
                                            end) (RNormal s)).
      rewrite HPo. reflexivity. }
    subst Q. unfold aimp. auto.
  - (* Hoare_consequence_res *)
    assert (HQeq : Q' = Qg).
    { apply functional_extensionality. intros s.
      change (Q' s) with ((fun r : result => match r with
                                             | RNormal s => Q' s
                                             | RError _ => False
                                             end) (RNormal s)).
      rewrite HPo. reflexivity. }
    subst Q'.
    intros s HP's n.
    apply H1.
    refine (IHWeakHoareRes xg Hc Q _ s _ n).
    + reflexivity.
    + apply H0. exact HP's.
Qed.

Lemma triple_nondet: forall x Q,
    ⦃⦃ aforall (fun n => aupdate x (CONST n) Q) ⦄⦄ NONDET x ⦃⦃ Q ⦄⦄.
Proof.
  unfold triple, aforall, aupdate.
  intros x Q s r EXEC PRE.
  inversion EXEC; subst.
  eexists. split; [ reflexivity | ].
  cbn. apply PRE.
Qed.

Lemma triple_seq: forall P Q R c1 c2,
      ⦃⦃ P ⦄⦄ c1 ⦃⦃ Q ⦄⦄ ->
      ⦃⦃ Q ⦄⦄ c2 ⦃⦃ R ⦄⦄ ->
      ⦃⦃ P ⦄⦄ c1;;c2 ⦃⦃ R ⦄⦄.
Proof.
  unfold triple; intros P Q R c1 c2 H1 H2 s r EXEC PRE.
  inversion EXEC; subst.
  - (* cexec_seq: c1 normal, c2 normal *)
    match goal with
    | E1 : cexec s c1 (RNormal ?s'),
      E2 : cexec ?s' c2 (RNormal ?s'') |- _ =>
      destruct (H1 s (RNormal s') E1 PRE) as (sx & EQ1 & QSx);
      inversion EQ1; subst sx;
      destruct (H2 s' (RNormal s'') E2 QSx) as (sy & EQ2 & RSy);
      inversion EQ2; subst sy;
      exists s''; split; [ reflexivity | exact RSy ]
    end.
  - (* cexec_seq_error: c1 errors *)
    match goal with
    | E1 : cexec s c1 (RError ?se) |- _ =>
      destruct (H1 s (RError se) E1 PRE) as (? & EQ & _); discriminate
    end.
  - (* cexec_seq_error_right: c1 normal, c2 errors *)
    match goal with
    | E1 : cexec s c1 (RNormal ?s'),
      E2 : cexec ?s' c2 (RError ?se) |- _ =>
      destruct (H1 s (RNormal s') E1 PRE) as (sx & EQ1 & QSx);
      inversion EQ1; subst sx;
      destruct (H2 s' (RError se) E2 QSx) as (? & EQ & _); discriminate
    end.
Qed.

Lemma triple_ifthenelse: forall P Q b c1 c2,
      ⦃⦃ atrue b //\\ P ⦄⦄ c1 ⦃⦃ Q ⦄⦄ ->
      ⦃⦃ afalse b //\\ P ⦄⦄ c2 ⦃⦃ Q ⦄⦄ ->
      ⦃⦃ P ⦄⦄ IF b THEN c1 ELSE c2 END ⦃⦃ Q ⦄⦄.
Proof.
  unfold triple, aand, atrue, afalse.
  intros P Q b c1 c2 H1 H2 s r EXEC PRE.
  inversion EXEC; subst.
  - (* choice_left: cexec s (ASSUME b ;; c1) r *)
    match goal with E : cexec s (ASSUME b ;; c1) r |- _ => inversion E; subst end.
    + (* SEQ normal *)
      match goal with EA : cexec s (ASSUME b) _ |- _ => inversion EA; subst end.
      eapply H1; eauto.
    + (* SEQ error left: ASSUME b errors — impossible *)
      match goal with EA : cexec s (ASSUME b) (RError _) |- _ => inversion EA end.
    + (* SEQ error right *)
      match goal with EA : cexec s (ASSUME b) _ |- _ => inversion EA; subst end.
      eapply H1; eauto.
  - (* choice_right: cexec s (ASSUME (NOT b) ;; c2) r *)
    match goal with E : cexec s (ASSUME (NOT b) ;; c2) r |- _ => inversion E; subst end.
    + match goal with EA : cexec s (ASSUME (NOT b)) _ |- _ => inversion EA; subst end.
      eapply H2; eauto.
      split; [ apply Bool.negb_true_iff; assumption | exact PRE ].
    + match goal with EA : cexec s (ASSUME (NOT b)) (RError _) |- _ => inversion EA end.
    + match goal with EA : cexec s (ASSUME (NOT b)) _ |- _ => inversion EA; subst end.
      eapply H2; eauto.
      split; [ apply Bool.negb_true_iff; assumption | exact PRE ].
Qed.

(** Helper: [P] is preserved across any number of iterations of the loop body
    [(ASSUME b ;; c)] when [c] preserves [P] under the [b]-true precondition. *)
Lemma triple_while_invariant: forall P b c s s',
  ⦃⦃ atrue b //\\ P ⦄⦄ c ⦃⦃ P ⦄⦄ ->
  star (step_iter (ASSUME b ;; c)) s s' ->
  P s -> P s'.
Proof.
  intros P b c s s' H STAR PS.
  induction STAR as [ x | x y z STEP STAR' IH ]; [ exact PS | ].
  apply IH. clear IH.
  unfold step_iter in STEP. inversion STEP. subst.
  (* STEP gives:
       H4 : cexec x (ASSUME b) (RNormal s')
       H6 : cexec s' c (RNormal y)         (where s' is the intermediate)
     after inversion of the inner ASSUME we get beval b x = true and s' = x. *)
  match goal with EA : cexec x (ASSUME b) (RNormal ?sm) |- _ => inversion EA; subst sm end.
  match goal with EC : cexec x c (RNormal y) |- _ =>
    destruct (H x (RNormal y) EC) as (sx & EQ & PSx);
      [ split; assumption | inversion EQ; subst sx; exact PSx ]
  end.
Qed.

(** Helper: a [cexec] derivation for a [SEQ] command can be decomposed into
    its three possible shapes. *)
Lemma cexec_seq_inv:
  forall c1 c2 s r,
    cexec s (c1 ;; c2) r ->
    (exists sm sf, cexec s c1 (RNormal sm) /\ cexec sm c2 (RNormal sf) /\ r = RNormal sf)
    \/ (exists sf, cexec s c1 (RError sf) /\ r = RError sf)
    \/ (exists sm sf, cexec s c1 (RNormal sm) /\ cexec sm c2 (RError sf) /\ r = RError sf).
Proof.
  intros c1 c2 s r EXEC.
  inversion EXEC; subst.
  - left. eauto.
  - right. left. eauto.
  - right. right. eauto.
Qed.

Lemma triple_while: forall P b c,
      ⦃⦃ atrue b //\\ P ⦄⦄ c ⦃⦃ P ⦄⦄ ->
      ⦃⦃ P ⦄⦄ WHILE b DO c END ⦃⦃ afalse b //\\ P ⦄⦄.
Proof.
  unfold triple, aand, atrue, afalse.
  intros P b c H s r EXEC PRE.
  (* WHILE b DO c END = ((ASSUME b ;; c) ★) ;; ASSUME (NOT b) *)
  apply cexec_seq_inv in EXEC.
  destruct EXEC as
    [ (sm & sf & EI & EA & ->)
    | [ (sf & EI & ->) | (sm & sf & EI & EA & ->) ] ].
  - (* SEQ normal *)
    apply cexec_cstar_iff_star in EI.
    assert (PSm : P sm) by (eapply triple_while_invariant; eauto).
    (* From EA : cexec sm (ASSUME (NOT b)) (RNormal sf) extract: sm = sf, beval (NOT b) sm = true *)
    inversion EA as [ | | | | ?se ?bv HBeval HEq | | | | | | | | | ]; subst.
    exists sf; split;
      [ reflexivity
      | split; [ apply Bool.negb_true_iff; exact HBeval | exact PSm ] ].
  - (* SEQ error left: iterated body errors *)
    apply cexec_cstar_err_iff in EI.
    destruct EI as (sm & STAR & ERR).
    assert (PSm : P sm) by (eapply triple_while_invariant; eauto).
    apply cexec_seq_inv in ERR.
    destruct ERR as
      [ (sm1 & sf1 & _ & _ & EQbad)
      | [ (sf1 & EA & _) | (sx & sf1 & EA & EC & _) ] ].
    + (* normal yields RNormal, can't equal RError *)
      discriminate EQbad.
    + (* ASSUME b errors: impossible *)
      inversion EA.
    + (* ASSUME b ok, c errors: contradicts H. EA : cexec sm (ASSUME b) (RNormal sx) *)
      inversion EA; subst sx.
      destruct (H sm (RError sf1) EC) as (? & EQc & _);
        [ split; assumption | discriminate ].
  - (* SEQ error right: ASSUME (NOT b) errors. Impossible. *)
    inversion EA.
Qed.

Lemma triple_consequence: forall P Q P' Q' c,
      ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄ ->
      P' -->> P ->
      Q -->> Q' ->
      ⦃⦃ P' ⦄⦄ c ⦃⦃ Q' ⦄⦄.
Proof.
  unfold triple, aimp; intros P Q P' Q' c HT P'P QQ' s r EXEC PRE.
  destruct (HT s r EXEC (P'P s PRE)) as (s' & EQ & QSx).
  exists s'. split; [ exact EQ | apply QQ', QSx ].
Qed.

(** Floyd's forward assignment rule.  With finite-map stores it needs the
    side condition [x ∈ domf s]: otherwise the post-state [update x (aeval a s) s]
    adds [x] to the domain and the original store cannot be recovered by
    re-substituting [x], so the substitution-style postcondition would not be
    valid. *)
Lemma triple_assign_fwd: forall x a P,
  ⦃⦃ (fun s => x \in domf s) //\\ P ⦄⦄
  ASSIGN x a
  ⦃⦃ aexists (fun m => aexists (fun n =>
     aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n))) ⦄⦄.
Proof.
  unfold triple, aand, aexists, aequal, aupdate.
  intros x a P s r EXEC [Hin HP].
  inversion EXEC; subst.
  eexists. split; [ reflexivity | ].
  exists (s x), (aeval a s). split.
  - cbn [aeval]. apply update_same.
  - cbn [aeval]. rewrite update_shadow. rewrite (update_get x s Hin).
    split; [ exact HP | reflexivity ].
Qed.

Fixpoint modified_by (c: com) (x: ident) : Prop :=
  match c with
  | SKIP => False
  | ASSIGN y a => x = y
  | ERROR => False
  | ASSUME b => False
  | NONDET y => x = y
  |  c1 ;; c2 => modified_by c1 x \/ modified_by c2 x
  |  c1 ⊕ c2 => modified_by c1 x \/ modified_by c2 x
  |  c ★ => modified_by c x
  end.

Lemma cexec_modified:
  forall x s1 c s2,
  cexec s1 c s2 -> ~modified_by c x ->
  match s2 with
  | RNormal s => s x = s1 x
  | RError  s => s x = s1 x
  end.
Proof.
  intros x s1 c s2 EXEC.
  induction EXEC; intros NMOD; cbn in NMOD;
    try reflexivity;
    try (apply update_other; intro; apply NMOD; symmetry; assumption);
    try (rewrite IHEXEC2, IHEXEC1; tauto);
    try (apply IHEXEC; tauto).
Qed.

(** "[x] belongs to the (finite) domain of the store [s]."

    Trivially true for every variable under the old function-store model,
    but a real predicate with finmap stores. *)
Definition in_domf (x: ident) : assertion :=
  fun s => x \in domf s.

(** [x] in [domf] is preserved by any [cexec] that does not modify [x]. *)
Lemma dom_update: forall (x y: ident) v (s: store),
  (x \in domf (update y v s)) = ((x == y) || (x \in domf s))%bool.
Proof.
  intros x y v s. unfold update. rewrite dom_setf.
  apply in_fset1U.
Qed.

Lemma cexec_dom_preserved: forall x s1 c s2,
  cexec s1 c s2 -> ~modified_by c x ->
  match s2 with
  | RNormal s => (x \in domf s) = (x \in domf s1)
  | RError  s => (x \in domf s) = (x \in domf s1)
  end.
Proof.
  intros x s1 c s2 EXEC.
  induction EXEC; intros NMOD; cbn in NMOD; try reflexivity.
  - rewrite dom_update.
    assert (Hne : (x == x0) = false).
    { apply (@ssrbool.introF _ ((x == x0)%bool) (@eqP _ _ _)). intro H. apply NMOD, H. }
    rewrite Hne. reflexivity.
  - rewrite dom_update.
    assert (Hne : (x == x0) = false).
    { apply (@ssrbool.introF _ ((x == x0)%bool) (@eqP _ _ _)). intro H. apply NMOD, H. }
    rewrite Hne. reflexivity.
  - apply Decidable.not_or in NMOD. destruct NMOD as [N1 N2].
    specialize (IHEXEC1 N1). specialize (IHEXEC2 N2).
    rewrite IHEXEC2, IHEXEC1. reflexivity.
  - apply Decidable.not_or in NMOD. destruct NMOD as [N1 _].
    apply IHEXEC. exact N1.
  - apply Decidable.not_or in NMOD. destruct NMOD as [N1 N2].
    specialize (IHEXEC1 N1). specialize (IHEXEC2 N2).
    rewrite IHEXEC2, IHEXEC1. reflexivity.
  - apply Decidable.not_or in NMOD. apply IHEXEC, NMOD.
  - apply Decidable.not_or in NMOD. apply IHEXEC, NMOD.
  - specialize (IHEXEC1 NMOD). specialize (IHEXEC2 NMOD).
    rewrite IHEXEC2, IHEXEC1. reflexivity.
  - apply IHEXEC. exact NMOD.
  - specialize (IHEXEC1 NMOD). specialize (IHEXEC2 NMOD).
    rewrite IHEXEC2, IHEXEC1. reflexivity.
Qed.

(** Syntactically, an assertion [P] is independent from a set [vars] of
    variables if none of the variables in [vars] is mentioned in [P].
    With out encoding of assertions as predicates [store -> Prop],
    we cannot state the independence condition like this, since
    the predicates are opaque functions.
    Instead, we will say that the assertion has the same truth value
    in any two stores [s1] and [s2] that differ only on the values of
    the variables in set [vars]. *)
Definition independent_of (P: assertion) (vars: ident -> Prop) : Prop :=
  forall (s1 s2 : store),
  (forall x, ~ vars x -> s1 x = s2 x) ->
  (P s1 <-> P s2).

Lemma triple_frame:
  forall c P Q R,
  ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄ ->
  independent_of R (modified_by c) ->
  ⦃⦃ P //\\ R ⦄⦄ c ⦃⦃ Q //\\ R ⦄⦄.
Proof.
  unfold triple, aand, independent_of.
  intros c P Q R HT INDEP s r EXEC [HPs HRs].
  destruct (HT s r EXEC HPs) as (s' & -> & HQs').
  exists s'. split; [ reflexivity | split; [ exact HQs' | ] ].
  apply (INDEP s s');
    [ intros x NMOD; symmetry;
      exact (cexec_modified x s c (RNormal s') EXEC NMOD)
    | exact HRs ].
Qed.

(** Strong Hoare triples *)
Reserved Notation "⦇ P ⦈ c ⦇ Q ⦈" (at level 90, c at next level).

Definition alessthan (a: aexp) (v: Z) : assertion :=
  fun s => 0 <= aeval a s < v.

Inductive StrongHoareRes: assertion -> com -> postassertion -> Prop :=
| HOARE_skip_r: forall P,
  (* ------------------ *)
  ⦇ P ⦈ SKIP ⦇ P ⦈
| HOARE_assign_r: forall P x a,
  (* ------------------------------ *)
    ⦇ aupdate x a P ⦈ ASSIGN x a ⦇ P ⦈
| HOARE_seq_ok: forall P Q R c1 c2,
    ⦇ P ⦈ c1 ⦇ Q ⦈ ->
    ⦇ Q ⦈ c2 ⦇ R ⦈ ->
    (* ------------------ *)
    ⦇ P ⦈ (c1 ;; c2) ⦇ R ⦈
| HOARE_seq_err: forall P c1 c2,
    StrongHoareRes P c1 (fun r => match r with RError _ => True | _ => False end) ->
    (* ------------------ *)
    StrongHoareRes P (c1 ;; c2) (fun r => match r with RError _ => True | _ => False end)
| HOARE_consequence_res: forall P Q P' Q' c,
    ⦇ P ⦈ c ⦇ Q ⦈ ->
    P' -->> P ->
    Q -->> Q' ->
    (* -------------*)
    ⦇ P' ⦈ c ⦇ Q' ⦈
| HOARE_choice_res: forall P Q c1 c2,
    ⦇ P ⦈ c1 ⦇ Q ⦈ ->
    ⦇ P ⦈ c2 ⦇ Q ⦈ ->
    (* ---------------------- *)
    ⦇ P ⦈ (c1 ⊕ c2) ⦇ Q ⦈
| HOARE_nondet_r: forall x Q,
    (* demonic: the postcondition must hold for *every* nondeterministic value. *)
    ⦇ aforall (fun n => aupdate x (CONST n) Q) ⦈ NONDET x ⦇ Q ⦈
| HOARE_assume_r: forall (b: bexp) Q,
    (* [ASSUME b] must not block, so the guard is required to hold: this is the
       demonic (total-correctness) reading. *)
    ⦇ atrue b //\\ Q ⦈ ASSUME b ⦇ Q ⦈
| HOARE_error_r: forall Q,
    (* [ERROR] always errors; a total triple is derivable only from the empty
       precondition. *)
    ⦇ (fun _ : store => False) ⦈ ERROR ⦇ Q ⦈
| HOARE_cstar_ress: forall (INV: assertion) c (A: Type) (R: A -> A -> Prop) (m: store -> A),
    well_founded R ->
    (forall a, ⦇ INV //\\ (fun s => m s = a) ⦈ c ⦇ INV //\\ (fun s => R (m s) a) ⦈) ->
    (* ------------------ *)
    ⦇ INV ⦈ (CSTAR c) ⦇ INV ⦈
where "⦇ P ⦈ c ⦇ Q ⦈" :=
  (StrongHoareRes P c (fun r => match r with
                          | RNormal s => Q s
                          | RError _ => False
                          end)).




(** Demonic total-correctness ("strong") Hoare triple: from every [P]-state,
    [c] terminates ([exists r]), never errors, and *every* result is a normal
    state satisfying [Q] *)
Definition Triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s, P s ->
    (exists r, cexec s c r) /\
    (forall r, cexec s c r -> exists s', r = RNormal s' /\ Q s').

Notation "⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈" := (Triple P c Q) (at level 90, c at next level).

(** Termination half. *)
Lemma Triple_terminates: forall P c Q s, Triple P c Q -> P s -> exists r, cexec s c r.
Proof. intros P c Q s HT HP. apply (HT s HP). Qed.

(** Safety half is exactly the (error-aware) weak triple. *)
Lemma Triple_safe: forall P c Q, Triple P c Q -> triple P c Q.
Proof. intros P c Q HT s r EXEC HP. destruct (HT s HP) as [_ Hsafe]. exact (Hsafe r EXEC). Qed.

(** Demonic implies angelic: a unique terminating normal run reaching [Q].
    (Under nondeterminism this is strictly stronger than the old definition.) *)
Lemma Triple_func: forall P c Q s,
  Triple P c Q -> P s -> exists s', cexec s c (RNormal s') /\ Q s'.
Proof.
  intros P c Q s HT HP. destruct (HT s HP) as [[r Hr] Hsafe].
  destruct (Hsafe r Hr) as [s' [-> HQ]]. exists s'. split; [ exact Hr | exact HQ ].
Qed.

(** Assemble a demonic triple from termination + the weak (safety) triple. *)
Lemma Triple_intro: forall P c Q,
  (forall s, P s -> exists r, cexec s c r) -> triple P c Q -> Triple P c Q.
Proof.
  intros P c Q Hterm Hsafe s HP.
  split; [ apply Hterm; exact HP | intros r Hr; exact (Hsafe s r Hr HP) ].
Qed.

Lemma Triple_skip: forall P,
  ⦇⦇ P ⦈⦈ SKIP ⦇⦇ P ⦈⦈.
Proof.
  intros P. apply Triple_intro; [ | apply triple_skip ].
  intros s HP. exists (RNormal s). apply cexec_skip.
Qed.

Lemma Triple_assign: forall P x a,
      ⦇⦇ aupdate x a P ⦈⦈ ASSIGN x a ⦇⦇ P ⦈⦈.
Proof.
  intros P x a. apply Triple_intro; [ | apply triple_assign ].
  intros s PRE. exists (RNormal (update x (aeval a s) s)). apply cexec_assign.
Qed.

Lemma Triple_seq: forall P Q R c1 c2,
      ⦇⦇ P ⦈⦈ c1 ⦇⦇ Q ⦈⦈ -> ⦇⦇ Q ⦈⦈ c2 ⦇⦇ R ⦈⦈ ->
      ⦇⦇ P ⦈⦈ c1;;c2 ⦇⦇ R ⦈⦈.
Proof.
  intros P Q R c1 c2 H1 H2. apply Triple_intro.
  - intros s PRE. destruct (Triple_func _ _ _ s H1 PRE) as (sm & E1 & HQ).
    destruct (Triple_terminates _ _ _ sm H2 HQ) as [r2 E2]. destruct r2 as [sf | sf].
    + exists (RNormal sf). eapply cexec_seq; eassumption.
    + exists (RError sf). eapply cexec_seq_error_right; eassumption.
  - eapply triple_seq; [ apply (Triple_safe _ _ _ H1) | apply (Triple_safe _ _ _ H2) ].
Qed.

Lemma Triple_ifthenelse: forall P Q b c1 c2,
      ⦇⦇ atrue b //\\ P ⦈⦈ c1 ⦇⦇ Q ⦈⦈ ->
      ⦇⦇ afalse b //\\ P ⦈⦈ c2 ⦇⦇ Q ⦈⦈ ->
      ⦇⦇ P ⦈⦈ IF b THEN c1 ELSE c2 END ⦇⦇ Q ⦈⦈.
Proof.
  intros P Q b c1 c2 H1 H2. apply Triple_intro.
  - intros s PRE. destruct (beval b s) eqn:Hb.
    + assert (Hpre : (atrue b //\\ P) s) by (split; [ exact Hb | exact PRE ]).
      destruct (Triple_func _ _ _ s H1 Hpre) as (s' & EXEC & _).
      exists (RNormal s'). apply cexec_choice_left.
      apply cexec_seq with s; [ apply cexec_assume; exact Hb | exact EXEC ].
    + assert (Hpre : (afalse b //\\ P) s) by (split; [ exact Hb | exact PRE ]).
      destruct (Triple_func _ _ _ s H2 Hpre) as (s' & EXEC & _).
      exists (RNormal s'). apply cexec_choice_right.
      apply cexec_seq with s;
        [ apply cexec_assume; cbn; rewrite Hb; reflexivity | exact EXEC ].
  - apply triple_ifthenelse; [ apply (Triple_safe _ _ _ H1) | apply (Triple_safe _ _ _ H2) ].
Qed.

Lemma Triple_consequence: forall P Q P' Q' c,
      ⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈ ->
      P' -->> P ->
      Q -->> Q' ->
      ⦇⦇ P' ⦈⦈ c ⦇⦇ Q' ⦈⦈.
Proof.
  intros P Q P' Q' c HT HP'P HQQ'. apply Triple_intro.
  - intros s PRE. apply (Triple_terminates _ _ _ s HT (HP'P s PRE)).
  - eapply triple_consequence; [ apply (Triple_safe _ _ _ HT) | exact HP'P | exact HQQ' ].
Qed.


Lemma Triple_while: forall P variant b c,
  (forall v,
     ⦇⦇ P //\\ atrue b //\\ aequal variant v ⦈⦈
     c
     ⦇⦇ P //\\ alessthan variant v ⦈⦈)
  ->
     ⦇⦇ P ⦈⦈ WHILE b DO c END ⦇⦇ P //\\ afalse b ⦈⦈.
Proof.
  intros P variant b c H. apply Triple_intro.
  - (* Termination: the variant gives a well-founded descent to a [¬b] state.
       Demonic [H] yields a unique decreasing successor via [Triple_func]. *)
    intros s0 PRE0.
    assert (HELP: forall n s,
                0 <= aeval variant s ->
                (Z.to_nat (aeval variant s) <= n)%nat ->
                P s ->
                exists sf,
                  cexec s (CSTAR (ASSUME b ;; c)) (RNormal sf) /\
                  P sf /\ beval b sf = false).
    { induction n as [|n IH]; intros s Hvnn Hn PS.
      - assert (Hzero : aeval variant s = 0).
        { destruct (aeval variant s) as [|p|p]; lia. }
        destruct (beval b s) eqn:Hb.
        + assert (Hpre : (P //\\ atrue b //\\ aequal variant (aeval variant s)) s).
          { split; [ exact PS | split; [ exact Hb | reflexivity ] ]. }
          destruct (Triple_func _ _ _ s (H (aeval variant s)) Hpre)
            as (s1 & _ & (_ & (Hv0 & Hlt))).
          rewrite Hzero in Hlt. lia.
        + exists s. split; [ apply cexec_cstar_done | split; assumption ].
      - destruct (beval b s) eqn:Hb.
        + assert (Hpre : (P //\\ atrue b //\\ aequal variant (aeval variant s)) s).
          { split; [ exact PS | split; [ exact Hb | reflexivity ] ]. }
          destruct (Triple_func _ _ _ s (H (aeval variant s)) Hpre)
            as (s1 & EXEC1 & (PS1 & (Hv0 & Hlt))).
          assert (Hsmaller : (Z.to_nat (aeval variant s1) <= n)%nat).
          { assert ((Z.to_nat (aeval variant s1) < Z.to_nat (aeval variant s))%nat)
              by (apply (proj1 (Z2Nat.inj_lt _ _ Hv0 Hvnn)); exact Hlt).
            lia. }
          destruct (IH s1 Hv0 Hsmaller PS1) as (s2 & EXEC2 & PS2 & Hb2).
          exists s2. split; [ | split; assumption ].
          eapply cexec_cstar_step_ok.
          * apply cexec_seq with s; [ apply cexec_assume; exact Hb | exact EXEC1 ].
          * exact EXEC2.
        + exists s. split; [ apply cexec_cstar_done | split; assumption ].
    }
    destruct (beval b s0) eqn:Hb.
    + assert (Hpre0 : (P //\\ atrue b //\\ aequal variant (aeval variant s0)) s0).
      { split; [ exact PRE0 | split; [ exact Hb | reflexivity ] ]. }
      destruct (Triple_func _ _ _ s0 (H (aeval variant s0)) Hpre0)
        as (s1 & EXEC1 & (PS1 & (Hv0 & _))).
      destruct (HELP (Z.to_nat (aeval variant s1)) s1 Hv0 (le_n _) PS1)
        as (sf & EXEC_LOOP & PSf & Hbf).
      exists (RNormal sf). apply cexec_seq with sf.
      * eapply cexec_cstar_step_ok.
        -- apply cexec_seq with s0;
             [ apply cexec_assume; exact Hb | exact EXEC1 ].
        -- exact EXEC_LOOP.
      * apply cexec_assume; cbn; rewrite Hbf; reflexivity.
    + exists (RNormal s0). apply cexec_seq with s0.
      * apply cexec_cstar_done.
      * apply cexec_assume; cbn; rewrite Hb; reflexivity.
  - (* Safety: the body never errors and preserves [P], so the weak
       partial-correctness [triple_while] applies. *)
    assert (Hbody : ⦃⦃ atrue b //\\ P ⦄⦄ c ⦃⦃ P ⦄⦄).
    { intros s r EXEC Hpre.
      assert (Hpre' : (P //\\ atrue b //\\ aequal variant (aeval variant s)) s).
      { destruct Hpre as [Hbv HPs].
        split; [ exact HPs | split; [ exact Hbv | reflexivity ] ]. }
      destruct (Triple_safe _ _ _ (H (aeval variant s)) s r EXEC Hpre')
        as (s' & EQ & (HP' & _)).
      exists s'. split; [ exact EQ | exact HP' ]. }
    eapply triple_consequence;
      [ apply (triple_while P b c Hbody)
      | intros s HP; exact HP
      | intros s Hpost; destruct Hpost as [Hbf HPs]; split; [ exact HPs | exact Hbf ] ].
Qed.

Module Soundness.

  (** Helper: every (general, postassertion-tagged) weak derivation is sound
      for partial correctness — every execution from a [P]-state lands in a
      result satisfying the postassertion [PQ].  Proved by induction on the
      derivation; mirrors [Strong_partial_correctness] below. *)
  Local Lemma WeakHoareRes_partial: forall P c PQ,
    WeakHoareRes P c PQ ->
    forall s r, cexec s c r -> P s -> PQ r.
  Proof.
    intros P c PQ HW.
    induction HW as [
        P                                  (* skip  *)
      | P x a                              (* assign *)
      | x Q                                (* nondet *)
      | P Q R c1 c2 HW1 IH1 HW2 IH2        (* seq_ok *)
      | P c1 c2 HW IH                      (* seq_err *)
      | P Q P' Q' c HW IH HP'P HQQ'        (* consequence *)
      | P Q c1 c2 HW1 IH1 HW2 IH2          (* choice *)
      | INV c HW IH                        (* cstar *)
      | b Q                                (* assume *)
      | Q                                  (* error *)
    ]; intros sx r EXEC HP.
    - (* skip *)
      inversion EXEC; subst. cbn. exact HP.
    - (* assign *)
      inversion EXEC; subst. cbn. exact HP.
    - (* nondet *)
      inversion EXEC; subst. cbn. apply HP.
    - (* seq_ok *)
      apply cexec_seq_inv in EXEC.
      destruct EXEC as
        [ (sm & sf & H1' & H2' & ->)
        | [ (sf & H1' & ->) | (sm & sf & H1' & H2' & ->) ] ].
      + specialize (IH1 sx (RNormal sm) H1' HP). cbn in IH1.
        specialize (IH2 sm (RNormal sf) H2' IH1). exact IH2.
      + specialize (IH1 sx (RError sf) H1' HP). cbn in IH1. exfalso. exact IH1.
      + specialize (IH1 sx (RNormal sm) H1' HP). cbn in IH1.
        specialize (IH2 sm (RError sf) H2' IH1). exact IH2.
    - (* seq_err *)
      apply cexec_seq_inv in EXEC.
      destruct EXEC as
        [ (sm & sf & H1' & H2' & ->)
        | [ (sf & H1' & ->) | (sm & sf & H1' & H2' & ->) ] ].
      + specialize (IH sx (RNormal sm) H1' HP). cbn in IH. exfalso. exact IH.
      + specialize (IH sx (RError sf) H1' HP). exact IH.
      + specialize (IH sx (RNormal sm) H1' HP). cbn in IH. exfalso. exact IH.
    - (* consequence *)
      apply HP'P in HP.
      specialize (IH sx r EXEC HP).
      destruct r as [s' | s']; cbn in IH |- *.
      + apply HQQ'. exact IH.
      + exact IH.
    - (* choice *)
      inversion EXEC; subst.
      + eapply IH1; eassumption.
      + eapply IH2; eassumption.
    - (* cstar *)
      destruct r as [s' | s'].
      + (* RNormal: induct on the successful-iteration chain, [INV] preserved *)
        apply cexec_cstar_iff_star in EXEC. cbn.
        revert HP. induction EXEC as [|x y z STEP STAR IHSTAR]; intros HP.
        * exact HP.
        * apply IHSTAR. unfold step_iter in STEP.
          specialize (IH x (RNormal y) STEP HP). cbn in IH. exact IH.
      + (* RError: [INV] holds up to the erroring iteration, which the body
           rule forbids *)
        apply cexec_cstar_err_iff in EXEC.
        destruct EXEC as (sm & STAR & ERR).
        assert (HINV_sm : INV sm).
        { clear ERR. revert HP.
          induction STAR as [|x y z STEP STAR' IHSTAR']; intros HP.
          - exact HP.
          - apply IHSTAR'. unfold step_iter in STEP.
            specialize (IH x (RNormal y) STEP HP). cbn in IH. exact IH. }
        specialize (IH sm (RError s') ERR HINV_sm). cbn in IH. exfalso. exact IH.
    - (* assume *)
      inversion EXEC; subst. cbn. apply HP. assumption.
    - (* error *)
      destruct HP.
  Qed.

  Theorem triple_soundness: forall P c Q,
    ⦃ P ⦄ c ⦃ Q ⦄ ->
    ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄.
  Proof.
    unfold triple. intros P c Q HW s r EXEC HP.
    pose proof (WeakHoareRes_partial _ _ _ HW s r EXEC HP) as HQ.
    destruct r as [s' | s']; cbn in HQ.
    - exists s'. split; [ reflexivity | exact HQ ].
    - exfalso. exact HQ.
  Qed.


  (** Helper: a strong syntactic Hoare derivation is sound for partial
    correctness — every execution from a [P]-state lands in a result
    satisfying [Q].  Proved by induction on the derivation. *)
  Local Lemma Strong_partial_correctness: forall P c Q,
    StrongHoareRes P c Q ->
    forall s r, cexec s c r -> P s -> Q r.
  Proof.
    intros P c Q HSH.
    induction HSH as [
        P
      | P x a
      | P Q R c1 c2 HSH1 IH1 HSH2 IH2
      | P c1 c2 HSH IH
      | P Q P' Q' c HSH IH HP'P HQQ'
      | P Q c1 c2 HSH1 IH1 HSH2 IH2
      | x Q
      | b Q
      | Q
      | INV cb A R m Hwf Hbody IHbody
    ]; intros sx r EXEC HP.
    - (* HOARE_skip_r *)
      inversion EXEC; subst. cbn. exact HP.
    - (* HOARE_assign_r *)
      inversion EXEC; subst. cbn. exact HP.
    - (* HOARE_seq_ok *)
      apply cexec_seq_inv in EXEC.
      destruct EXEC as
        [ (sm & sf & H1' & H2' & ->)
        | [ (sf & H1' & ->) | (sm & sf & H1' & H2' & ->) ] ].
      + specialize (IH1 sx (RNormal sm) H1' HP). cbn in IH1.
        specialize (IH2 sm (RNormal sf) H2' IH1). exact IH2.
      + specialize (IH1 sx (RError sf) H1' HP). cbn in IH1. exfalso. exact IH1.
      + specialize (IH1 sx (RNormal sm) H1' HP). cbn in IH1.
        specialize (IH2 sm (RError sf) H2' IH1). exact IH2.
    - (* HOARE_seq_err *)
      apply cexec_seq_inv in EXEC.
      destruct EXEC as
        [ (sm & sf & H1' & H2' & ->)
        | [ (sf & H1' & ->) | (sm & sf & H1' & H2' & ->) ] ].
      + specialize (IH sx (RNormal sm) H1' HP). cbn in IH. exfalso. exact IH.
      + specialize (IH sx (RError sf) H1' HP). exact IH.
      + specialize (IH sx (RNormal sm) H1' HP). cbn in IH. exfalso. exact IH.
    - (* HOARE_consequence_res *)
      apply HP'P in HP.
      specialize (IH sx r EXEC HP).
      destruct r as [s' | s']; cbn in IH |- *.
      + apply HQQ'. exact IH.
      + exact IH.
    - (* HOARE_choice_res *)
      inversion EXEC; subst.
      + eapply IH1; eassumption.
      + eapply IH2; eassumption.
    - (* HOARE_nondet_r *)
      inversion EXEC; subst. cbn. apply HP.
    - (* HOARE_assume_r *)
      inversion EXEC; subst. cbn. exact (proj2 HP).
    - (* HOARE_error_r *)
      destruct HP.
    - (* HOARE_cstar_ress *)
      destruct r as [s' | s'].
      + (* RNormal: induct on the [star (step_iter cb)] chain, [INV] preserved *)
        apply cexec_cstar_iff_star in EXEC. cbn.
        revert HP. induction EXEC as [|x y z STEP STAR IHSTAR]; intros HP.
        * exact HP.
        * apply IHSTAR. unfold step_iter in STEP.
          specialize (IHbody (m x) x (RNormal y) STEP (conj HP (Logic.eq_refl _))).
          cbn in IHbody. destruct IHbody as [HINV_y _]. exact HINV_y.
      + (* RError: same chain up to the erroring iteration, which the body forbids *)
        apply cexec_cstar_err_iff in EXEC.
        destruct EXEC as (sm & STAR & ERR).
        assert (HINV_sm : INV sm).
        { clear ERR. revert HP.
          induction STAR as [|x y z STEP STAR' IHSTAR']; intros HP.
          - exact HP.
          - apply IHSTAR'. unfold step_iter in STEP.
            specialize (IHbody (m x) x (RNormal y) STEP (conj HP (Logic.eq_refl _))).
            cbn in IHbody. destruct IHbody as [HINV_y _]. exact HINV_y. }
        specialize (IHbody (m sm) sm (RError s') ERR (conj HINV_sm (Logic.eq_refl _))).
        cbn in IHbody. exact IHbody.
  Qed.

  Lemma Triple_partial_soundness: forall P c Q,
    ⦇ P ⦈ c ⦇ Q ⦈ ->
    ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄.
  Proof.
    unfold triple. intros P c Q HSH s r EXEC HP.
    pose proof (Strong_partial_correctness _ _ _ HSH s r EXEC HP) as HQ.
    destruct r as [s' | s']; cbn in HQ.
    - exists s'. split; [ reflexivity | exact HQ ].
    - exfalso. exact HQ.
  Qed.


  (** Existence/progress half: from every [P]-state a strong derivation admits
      at least one execution.  Note that the loop case is immediate: [CSTAR c]
      can always stop right away ([cexec_cstar_done]).  The variant in the
      [CSTAR] rule is not needed for this notion of demonic termination, only
      partial correctness ([Strong_partial_correctness]) is used to thread the
      intermediate state through a sequence. *)
  Local Lemma StrongHoareRes_terminates: forall P c PQ,
    StrongHoareRes P c PQ ->
    forall s, P s -> exists r, cexec s c r.
  Proof.
    intros P c PQ HSH.
    induction HSH as [
        P
      | P x a
      | P Q R c1 c2 HSH1 IH1 HSH2 IH2
      | P c1 c2 HSH IH
      | P Q P' Q' c HSH IH HP'P HQQ'
      | P Q c1 c2 HSH1 IH1 HSH2 IH2
      | x Q
      | b Q
      | Q
      | INV cb A R m Hwf Hbody IHbody
    ]; intros sx HP.
    - (* skip *) exists (RNormal sx). apply cexec_skip.
    - (* assign *) eexists. apply cexec_assign.
    - (* seq_ok *)
      destruct (IH1 sx HP) as [r1 E1].
      pose proof (Strong_partial_correctness _ _ _ HSH1 sx r1 E1 HP) as HQ1.
      destruct r1 as [sm | sf]; cbn in HQ1.
      + destruct (IH2 sm HQ1) as [r2 E2]. destruct r2 as [sf2 | sf2].
        * exists (RNormal sf2). eapply cexec_seq; eassumption.
        * exists (RError sf2). eapply cexec_seq_error_right; eassumption.
      + exfalso. exact HQ1.
    - (* seq_err *)
      destruct (IH sx HP) as [r1 E1].
      pose proof (Strong_partial_correctness _ _ _ HSH sx r1 E1 HP) as HQ1.
      destruct r1 as [sm | sf]; cbn in HQ1.
      + exfalso. exact HQ1.
      + exists (RError sf). eapply cexec_seq_error; eassumption.
    - (* consequence *)
      apply HP'P in HP. destruct (IH sx HP) as [r E]. exists r. exact E.
    - (* choice *)
      destruct (IH1 sx HP) as [r1 E1].
      exists r1. apply cexec_choice_left. exact E1.
    - (* nondet: pick any value *)
      exists (RNormal (update x 0 sx)). apply cexec_nondet.
    - (* assume: the guard holds, so [ASSUME b] steps *)
      exists (RNormal sx). apply cexec_assume. exact (proj1 HP).
    - (* error: empty precondition *)
      destruct HP.
    - (* cstar: the loop can stop immediately *)
      exists (RNormal sx). apply cexec_cstar_done.
  Qed.

  Theorem Triple_soundness: forall P c Q,
    ⦇ P ⦈ c ⦇ Q ⦈ ->
    ⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈.
  Proof.
    intros P c Q HSH. apply Triple_intro.
    - exact (StrongHoareRes_terminates _ _ _ HSH).
    - apply Triple_partial_soundness. exact HSH.
  Qed.

End Soundness.

Module Completness.

(** ** Relative completeness of the weak Hoare logic

    We follow the classical "semantic weakest-precondition" recipe: define the
    weakest *liberal* precondition [wlp c Q] semantically (in terms of [cexec]),
    show that the triple [⦃ wlp c Q ⦄ c ⦃ Q ⦄] is *derivable* in the proof
    system, and conclude by the rule of consequence. *)

(** The weakest liberal precondition of [c] for postcondition [Q]: the set of
    states from which *every* execution of [c] terminates normally in a
    [Q]-state — in particular [c] never errors and never blocks into an error. *)
Definition wlp (c: com) (Q: assertion) : assertion :=
  fun s => forall r, cexec s c r -> exists s', r = RNormal s' /\ Q s'.

(** The semantic triple is exactly "[P] entails the weakest liberal
    precondition". *)
Lemma triple_iff_wlp: forall P c Q,
  ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄ <-> (P -->> wlp c Q).
Proof.
  unfold triple, wlp, aimp. split.
  - intros H s HP r EXEC. exact (H s r EXEC HP).
  - intros H s r EXEC HP. exact (H s HP r EXEC).
Qed.

(** *** Pointwise unfolding of [wlp], one per command shape. *)

Lemma wlp_skip: forall Q s, wlp SKIP Q s -> Q s.
Proof.
  intros Q s H. destruct (H (RNormal s) (cexec_skip s)) as (s' & EQ & HQ).
  inversion EQ; subst. exact HQ.
Qed.

Lemma wlp_error: forall Q s, wlp ERROR Q s -> False.
Proof.
  intros Q s H. destruct (H (RError s) (cexec_error s)) as (s' & EQ & _).
  discriminate EQ.
Qed.

Lemma wlp_assign: forall x a Q s, wlp (ASSIGN x a) Q s -> Q (update x (aeval a s) s).
Proof.
  intros x a Q s H.
  destruct (H (RNormal (update x (aeval a s) s)) (cexec_assign s x a))
    as (s' & EQ & HQ).
  inversion EQ; subst. exact HQ.
Qed.

Lemma wlp_nondet: forall x Q s, wlp (NONDET x) Q s -> forall n, Q (update x n s).
Proof.
  intros x Q s H n.
  destruct (H (RNormal (update x n s)) (cexec_nondet s x n)) as (s' & EQ & HQ).
  inversion EQ; subst. exact HQ.
Qed.

Lemma wlp_assume: forall b Q s, wlp (ASSUME b) Q s -> beval b s = true -> Q s.
Proof.
  intros b Q s H Hb.
  destruct (H (RNormal s) (cexec_assume s b Hb)) as (s' & EQ & HQ).
  inversion EQ; subst. exact HQ.
Qed.

Lemma wlp_seq: forall c1 c2 Q s, wlp (SEQ c1 c2) Q s -> wlp c1 (wlp c2 Q) s.
Proof.
  intros c1 c2 Q s H r1 E1. destruct r1 as [sm | sf].
  - exists sm. split; [ reflexivity | ]. intros r2 E2. destruct r2 as [sf2 | sf2].
    + apply (H (RNormal sf2)). eapply cexec_seq; eassumption.
    + apply (H (RError sf2)). eapply cexec_seq_error_right; eassumption.
  - exfalso. destruct (H (RError sf)) as (s' & EQ & _);
      [ eapply cexec_seq_error; eassumption | discriminate EQ ].
Qed.

Lemma wlp_choice_l: forall c1 c2 Q s, wlp (CHOICE c1 c2) Q s -> wlp c1 Q s.
Proof.
  intros c1 c2 Q s H r1 E1. apply (H r1). apply cexec_choice_left. exact E1.
Qed.

Lemma wlp_choice_r: forall c1 c2 Q s, wlp (CHOICE c1 c2) Q s -> wlp c2 Q s.
Proof.
  intros c1 c2 Q s H r1 E1. apply (H r1). apply cexec_choice_right. exact E1.
Qed.

(** The crucial loop lemmas: [wlp (CSTAR c) Q] is *itself* an invariant of [c]
    and it entails [Q] (because the loop may always stop immediately). *)
Lemma wlp_cstar_unfold: forall c Q s,
  wlp (CSTAR c) Q s -> wlp c (wlp (CSTAR c) Q) s.
Proof.
  intros c Q s H r1 E1. destruct r1 as [sm | sf].
  - exists sm. split; [ reflexivity | ]. intros r2 E2. destruct r2 as [sf2 | sf2].
    + apply (H (RNormal sf2)). eapply cexec_cstar_step_ok; eassumption.
    + apply (H (RError sf2)). eapply cexec_cstar_step_iter_error; eassumption.
  - exfalso. destruct (H (RError sf)) as (s' & EQ & _);
      [ eapply cexec_cstar_step_error; eassumption | discriminate EQ ].
Qed.

Lemma wlp_cstar_exit: forall c Q s, wlp (CSTAR c) Q s -> Q s.
Proof.
  intros c Q s H. destruct (H (RNormal s) (cexec_cstar_done c s)) as (s' & EQ & HQ).
  inversion EQ; subst. exact HQ.
Qed.

(** [⦃ wlp c Q ⦄ c ⦃ Q ⦄] is derivable, by structural induction on [c]. *)
Lemma wlp_der: forall c Q, ⦃ wlp c Q ⦄ c ⦃ Q ⦄.
Proof.
  intro c.
  induction c as [ | | x a | x | b | c1 IH1 c2 IH2 | c1 IH1 c2 IH2 | c0 IH0 ];
    intros Q.
  - (* SKIP *)
    eapply Hoare_consequence_pre; [ apply Hoare_skip_r | ].
    intros s H. apply wlp_skip. exact H.
  - (* ERROR *)
    eapply Hoare_consequence_pre; [ apply Hoare_error_r | ].
    intros s H. exact (wlp_error Q s H).
  - (* ASSIGN *)
    eapply Hoare_consequence_pre; [ apply Hoare_assign_r | ].
    intros s H. unfold aupdate. apply wlp_assign. exact H.
  - (* NONDET *)
    eapply Hoare_consequence_pre; [ apply Hoare_nondet | ].
    intros s H n. unfold aupdate. apply wlp_nondet. exact H.
  - (* ASSUME *)
    eapply Hoare_consequence_pre; [ apply Hoare_assume_r | ].
    intros s H. apply wlp_assume. exact H.
  - (* SEQ *)
    eapply Hoare_consequence_pre.
    + eapply Hoare_seq_ok; [ apply (IH1 (wlp c2 Q)) | apply (IH2 Q) ].
    + intros s H. apply wlp_seq. exact H.
  - (* CHOICE *)
    apply Hoare_choice_res.
    + eapply Hoare_consequence_pre; [ apply (IH1 Q) | ].
      intros s H. exact (wlp_choice_l c1 c2 Q s H).
    + eapply Hoare_consequence_pre; [ apply (IH2 Q) | ].
      intros s H. exact (wlp_choice_r c1 c2 Q s H).
  - (* CSTAR *)
    eapply Hoare_consequence_post.
    + apply Hoare_cstar_ress.
      eapply Hoare_consequence_pre; [ apply (IH0 (wlp (CSTAR c0) Q)) | ].
      intros s H. apply wlp_cstar_unfold. exact H.
    + intros s H. exact (wlp_cstar_exit c0 Q s H).
Qed.

(** Relative completeness: every valid semantic triple is derivable. *)
Theorem Hoare_complete: forall P c Q,
  ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄ -> ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  unfold triple. intros P c Q H.
  eapply Hoare_consequence_pre; [ apply wlp_der | ].
  intros s HP r EXEC. exact (H s r EXEC HP).
Qed.

(** Soundness + completeness: the proof system and the semantics agree. *)
Theorem Hoare_adequate: forall P c Q,
  ⦃ P ⦄ c ⦃ Q ⦄ <-> ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄.
Proof.
  intros P c Q. split.
  - apply Soundness.triple_soundness.
  - apply Hoare_complete.
Qed.

End Completness.

Module WP.

(** ** Computing weakest preconditions and verification conditions

    As in the standard backward VC-generator, loops must be annotated with an
    invariant.  Our loop is the unguarded Kleene star [CSTAR]: it may stop
    after any number of iterations, so the annotated invariant must (i) be
    preserved by the body and (ii) directly entail the postcondition. *)

(** Annotated commands: [com] with [CSTAR] decorated by an invariant. *)
Inductive acom : Type :=
  | ASKIP
  | AERROR
  | AASSIGN (x: ident) (a: aexp)
  | ANONDET (x: ident)
  | AASSUME (b: bexp)
  | ASEQ (c1 c2: acom)
  | ACHOICE (c1 c2: acom)
  | ACSTAR (Inv: assertion) (c: acom).

Fixpoint erase (c: acom) : com :=
  match c with
  | ASKIP => SKIP
  | AERROR => ERROR
  | AASSIGN x a => ASSIGN x a
  | ANONDET x => NONDET x
  | AASSUME b => ASSUME b
  | ASEQ c1 c2 => SEQ (erase c1) (erase c2)
  | ACHOICE c1 c2 => CHOICE (erase c1) (erase c2)
  | ACSTAR _ c => CSTAR (erase c)
  end.

(** Syntactic weakest liberal precondition. *)
Fixpoint wlp (c: acom) (Q: assertion) : assertion :=
  match c with
  | ASKIP => Q
  | AERROR => (fun _ => False)
  | AASSIGN x a => aupdate x a Q
  | ANONDET x => aforall (fun n => aupdate x (CONST n) Q)
  | AASSUME b => (fun s => beval b s = true -> Q s)
  | ASEQ c1 c2 => wlp c1 (wlp c2 Q)
  | ACHOICE c1 c2 => wlp c1 Q //\\ wlp c2 Q
  | ACSTAR Inv _ => Inv
  end.

(** Side conditions discharged by [wlp]; the only nontrivial ones come from the
    loop invariants. *)
Fixpoint vcond (c: acom) (Q: assertion) : Prop :=
  match c with
  | ASKIP | AERROR | AASSIGN _ _ | ANONDET _ | AASSUME _ => True
  | ASEQ c1 c2 => vcond c1 (wlp c2 Q) /\ vcond c2 Q
  | ACHOICE c1 c2 => vcond c1 Q /\ vcond c2 Q
  | ACSTAR Inv c =>
      vcond c Inv /\
      (Inv -->> wlp c Inv) /\
      (Inv -->> Q)
  end.

Definition vcgen (P: assertion) (c: acom) (Q: assertion) : Prop :=
  vcond c Q /\ (P -->> wlp c Q).

(** If the verification conditions hold, the [wlp]-triple is derivable. *)
Lemma wlp_sound: forall c Q,
  vcond c Q -> ⦃ wlp c Q ⦄ erase c ⦃ Q ⦄.
Proof.
  induction c as [ | | x a | x | b | c1 IH1 c2 IH2 | c1 IH1 c2 IH2 | Inv c0 IH0 ];
    intros Q VC.
  - apply Hoare_skip_r.
  - apply Hoare_error_r.
  - apply Hoare_assign_r.
  - apply Hoare_nondet.
  - apply Hoare_assume_r.
  - destruct VC as [VC1 VC2].
    eapply Hoare_seq_ok; [ apply IH1; exact VC1 | apply IH2; exact VC2 ].
  - destruct VC as [VC1 VC2].
    apply Hoare_choice_res.
    + eapply Hoare_consequence_pre; [ apply IH1; exact VC1 | intros s [HA _]; exact HA ].
    + eapply Hoare_consequence_pre; [ apply IH2; exact VC2 | intros s [_ HB]; exact HB ].
  - destruct VC as (VC1 & VC2 & VC3).
    eapply Hoare_consequence_post.
    + apply Hoare_cstar_ress.
      eapply Hoare_consequence_pre; [ apply IH0; exact VC1 | exact VC2 ].
    + exact VC3.
Qed.

Theorem vcgen_sound: forall P c Q,
  vcgen P c Q -> ⦃ P ⦄ erase c ⦃ Q ⦄.
Proof.
  intros P c Q [VC1 VC2].
  eapply Hoare_consequence_pre; [ apply wlp_sound; exact VC1 | exact VC2 ].
Qed.

End WP.

Module SP.

(** ** Computing strongest postconditions and verification conditions

    The forward (strongest-postcondition) VC-generator.  For [ASSIGN]/[NONDET]
    we take the exact relational image (the set of reachable states): the purely
    syntactic "Floyd" substitution form is unsound in the over-approximation
    direction with finite-map stores, because when [x ∉ domf s] the pre-state
    cannot be recovered from the post-state by re-substituting [x].  [ACSTAR] is
    annotated with an invariant, and [AERROR] yields the verification condition
    that it be unreachable. *)

Import WP.  (** annotated commands [acom] and [erase] *)

Fixpoint sp (P: assertion) (c: acom) : assertion :=
  match c with
  | ASKIP => P
  | AERROR => (fun _ => False)
  | AASSIGN x a => (fun s' => exists s, P s /\ s' = update x (aeval a s) s)
  | ANONDET x => (fun s' => exists s n, P s /\ s' = update x n s)
  | AASSUME b => atrue b //\\ P
  | ASEQ c1 c2 => sp (sp P c1) c2
  | ACHOICE c1 c2 => sp P c1 \\// sp P c2
  | ACSTAR Inv _ => Inv
  end.

Fixpoint vcond (P: assertion) (c: acom) : Prop :=
  match c with
  | ASKIP | AASSIGN _ _ | ANONDET _ | AASSUME _ => True
  | AERROR => (P -->> (fun _ => False))
  | ASEQ c1 c2 => vcond P c1 /\ vcond (sp P c1) c2
  | ACHOICE c1 c2 => vcond P c1 /\ vcond P c2
  | ACSTAR Inv c =>
      vcond Inv c /\
      (P -->> Inv) /\
      (sp Inv c -->> Inv)
  end.

Definition vcgen (P: assertion) (c: acom) (Q: assertion) : Prop :=
  vcond P c /\ (sp P c -->> Q).

(** If the verification conditions hold, the [sp]-triple is derivable. *)
Lemma sp_sound: forall c P,
  vcond P c -> ⦃ P ⦄ erase c ⦃ sp P c ⦄.
Proof.
  induction c as [ | | x a | x | b | c1 IH1 c2 IH2 | c1 IH1 c2 IH2 | Inv c0 IH0 ];
    intros P VC.
  - (* ASKIP *) apply Hoare_skip_r.
  - (* AERROR *)
    eapply Hoare_consequence_pre; [ apply Hoare_error_r | exact VC ].
  - (* AASSIGN *)
    eapply Hoare_consequence_pre; [ apply Hoare_assign_r | ].
    intros s HP. unfold aupdate. exists s. split; [ exact HP | reflexivity ].
  - (* ANONDET *)
    eapply Hoare_consequence_pre; [ apply Hoare_nondet | ].
    intros s HP n. unfold aupdate. exists s, n. split; [ exact HP | reflexivity ].
  - (* AASSUME *)
    eapply Hoare_consequence_pre; [ apply Hoare_assume_r | ].
    intros s HP Hb. split; [ exact Hb | exact HP ].
  - (* ASEQ *)
    destruct VC as [VC1 VC2].
    eapply Hoare_seq_ok; [ apply (IH1 P VC1) | apply (IH2 (sp P c1) VC2) ].
  - (* ACHOICE *)
    destruct VC as [VC1 VC2].
    apply Hoare_choice_res.
    + eapply Hoare_consequence_post; [ apply (IH1 P VC1) | intros s Hs; left; exact Hs ].
    + eapply Hoare_consequence_post; [ apply (IH2 P VC2) | intros s Hs; right; exact Hs ].
  - (* ACSTAR *)
    destruct VC as (VC1 & VC2 & VC3).
    eapply Hoare_consequence_pre.
    + apply Hoare_cstar_ress.
      eapply Hoare_consequence_post; [ apply (IH0 Inv VC1) | exact VC3 ].
    + exact VC2.
Qed.

Theorem vcgen_sound: forall P c Q,
  vcgen P c Q -> ⦃ P ⦄ erase c ⦃ Q ⦄.
Proof.
  intros P c Q [VC1 VC2].
  eapply Hoare_consequence_post; [ apply sp_sound; exact VC1 | exact VC2 ].
Qed.

End SP.
(** * Genuine demonic total correctness *)

(** The [Triple] above ([⦇⦇ ⦈⦈]) couples *angelic* termination
    ([exists r, cexec s c r]) with demonic safety.  That hybrid is not
    compositional (a [CSTAR] that "stops now" may feed a state on which the
    continuation blocks), so it is not completely axiomatisable by a single loop
    rule.  Here we use a proper *demonic total-correctness* semantics: from a
    [P]-state, [c] must terminate on *every* schedule, never erroring and never
    blocking, in a [Q]-state.  This is captured by an inductive predicate
    [safe], which — being inductive — is well-founded and therefore forces
    termination.  The strong logic [⦇ ⦈] (with the well-founded [CSTAR] variant)
    is sound and complete for it. *)

Module TotalCorrectness.

Inductive safe (Q: assertion) : com -> store -> Prop :=
| safe_skip: forall s,
    Q s ->
    safe Q SKIP s
| safe_step: forall c s,
    c <> SKIP ->
    (exists cs', red (c, s) cs') ->
    (forall c' s', red (c, s) (c', s') -> safe Q c' s') ->
    safe Q c s.

Definition TotalTriple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s, P s -> safe Q c s.

(** *** Closure properties of [safe] used for soundness *)

Lemma safe_post_mono: forall (Q Q': assertion),
  (Q -->> Q') -> forall c s, safe Q c s -> safe Q' c s.
Proof.
  intros Q Q' HQQ' c s H. induction H as [s HQ | c s Hns Hex Hrec IH].
  - apply safe_skip. apply HQQ'. exact HQ.
  - apply safe_step; [ exact Hns | exact Hex | exact IH ].
Qed.

Lemma safe_seq: forall (Qmid Rpost: assertion) c2,
  (forall s, Qmid s -> safe Rpost c2 s) ->
  forall c1 s, safe Qmid c1 s -> safe Rpost (c1 ;; c2) s.
Proof.
  intros Qmid Rpost c2 HQR c1 s H.
  induction H as [s HQ | c1 s Hns Hex Hrec IH].
  - (* c1 = SKIP *)
    apply safe_step.
    + discriminate.
    + exists (c2, s). apply red_seq_done.
    + intros c' s' RED. inversion RED; subst.
      * apply HQR. exact HQ.
      * match goal with Hr : red (SKIP, _) _ |- _ => inversion Hr end.
  - (* c1 steps *)
    apply safe_step.
    + discriminate.
    + destruct Hex as [[c1' s1] RED1]. exists (c1' ;; c2, s1). apply red_seq_step. exact RED1.
    + intros c' s' RED. inversion RED; subst.
      * exfalso. apply Hns. reflexivity.
      * exfalso. destruct Hex as [[ce se] REDe]. inversion REDe.
      * match goal with Hr : red (c1, s) (?cc, ?ss) |- _ => apply (IH cc ss); exact Hr end.
Qed.

(** *** [safe]-validity of each proof rule *)

Lemma TotalTriple_skip: forall P, TotalTriple P SKIP P.
Proof. intros P s HP. apply safe_skip. exact HP. Qed.

Lemma TotalTriple_assign: forall P x a, TotalTriple (aupdate x a P) (ASSIGN x a) P.
Proof.
  intros P x a s HP. apply safe_step.
  - discriminate.
  - exists (SKIP, update x (aeval a s) s). apply red_assign.
  - intros c' s' RED. inversion RED; subst. apply safe_skip. exact HP.
Qed.

Lemma TotalTriple_nondet: forall x Q,
  TotalTriple (aforall (fun n => aupdate x (CONST n) Q)) (NONDET x) Q.
Proof.
  intros x Q s HP. apply safe_step.
  - discriminate.
  - exists (SKIP, update x 0 s). apply red_nondet.
  - intros c' s' RED. inversion RED; subst. apply safe_skip. exact (HP n).
Qed.

Lemma TotalTriple_assume: forall b Q, TotalTriple (atrue b //\\ Q) (ASSUME b) Q.
Proof.
  intros b Q s [Hb HQ]. red in Hb. apply safe_step.
  - discriminate.
  - exists (SKIP, s). apply red_assume. exact Hb.
  - intros c' s' RED. inversion RED; subst. apply safe_skip. exact HQ.
Qed.

Lemma TotalTriple_error: forall Q, TotalTriple (fun _ => False) ERROR Q.
Proof. intros Q s []. Qed.

Lemma TotalTriple_choice: forall P Q c1 c2,
  TotalTriple P c1 Q -> TotalTriple P c2 Q -> TotalTriple P (c1 ⊕ c2) Q.
Proof.
  intros P Q c1 c2 H1 H2 s HP. apply safe_step.
  - discriminate.
  - exists (c1, s). apply red_choice_left.
  - intros c' s' RED. inversion RED; subst.
    + apply H1. exact HP.
    + apply H2. exact HP.
Qed.

Lemma TotalTriple_seq: forall P Q R c1 c2,
  TotalTriple P c1 Q -> TotalTriple Q c2 R -> TotalTriple P (c1 ;; c2) R.
Proof.
  intros P Q R c1 c2 H1 H2 s HP. apply safe_seq with Q.
  - exact H2.
  - apply H1. exact HP.
Qed.

Lemma TotalTriple_consequence: forall P Q P' Q' c,
  TotalTriple P c Q -> P' -->> P -> Q -->> Q' -> TotalTriple P' c Q'.
Proof.
  intros P Q P' Q' c HT HPP' HQQ' s HP'.
  apply (safe_post_mono Q Q' HQQ'). apply HT. apply HPP'. exact HP'.
Qed.

(** The well-founded variant loop rule is [safe]-valid: each iteration strictly
    decreases the measure [m] under the well-founded order [R], so the loop
    cannot iterate forever. *)
Lemma TotalTriple_cstar:
  forall (INV: assertion) c (A: Type) (R: A -> A -> Prop) (m: store -> A),
  well_founded R ->
  (forall a, TotalTriple (INV //\\ (fun s => m s = a)) c (INV //\\ (fun s => R (m s) a))) ->
  TotalTriple INV (CSTAR c) INV.
Proof.
  intros INV c A R m Hwf Hbody.
  assert (KEY: forall a s0, m s0 = a -> INV s0 -> safe INV (CSTAR c) s0).
  { intro a. induction a as [a IHa] using (well_founded_induction Hwf).
    intros s0 Ea HINV0.
    apply safe_step.
    - discriminate.
    - exists (SKIP, s0). apply red_cstar_done.
    - intros c' s' RED. inversion RED; subst.
      + (* stop *) apply safe_skip. exact HINV0.
      + (* one iteration then continue *)
        apply safe_seq with (INV //\\ (fun s => R (m s) (m s'))).
        * intros s'' [HINV'' HR'']. exact (IHa (m s'') HR'' s'' (Logic.eq_refl _) HINV'').
        * apply (Hbody (m s') s'). split; [ exact HINV0 | reflexivity ]. }
  intros s0 HINV0. exact (KEY (m s0) s0 (Logic.eq_refl _) HINV0).
Qed.

(** A command can never be [safe] for the empty postcondition: [safe] forces
    termination, but the final state would have to satisfy [False]. *)
Lemma safe_false_absurd: forall c s, safe (fun _ : store => False) c s -> False.
Proof.
  intros c s H. induction H as [s HQ | c s Hns Hex Hrec IH].
  - exact HQ.
  - destruct Hex as [[c' s'] RED]. exact (IH c' s' RED).
Qed.

(** *** Soundness: the strong logic is sound for demonic total correctness *)

Lemma StrongHoareRes_total: forall P c PQ,
  StrongHoareRes P c PQ -> TotalTriple P c (fun s => PQ (RNormal s)).
Proof.
  intros P c PQ HSH.
  induction HSH as [
      P
    | P x a
    | P Q R c1 c2 HSH1 IH1 HSH2 IH2
    | P c1 c2 HSH IH
    | P Q P' Q' c HSH IH HP'P HQQ'
    | P Q c1 c2 HSH1 IH1 HSH2 IH2
    | x Q
    | b Q
    | Q
    | INV cb A R m Hwf Hbody IHbody
  ]; cbn.
  - apply TotalTriple_skip.
  - apply TotalTriple_assign.
  - eapply TotalTriple_seq; [ exact IH1 | exact IH2 ].
  - (* seq_err: the premise forces the precondition empty *)
    intros s HP. exfalso. exact (safe_false_absurd c1 s (IH s HP)).
  - eapply TotalTriple_consequence; [ exact IH | exact HP'P | exact HQQ' ].
  - apply TotalTriple_choice; [ exact IH1 | exact IH2 ].
  - apply TotalTriple_nondet.
  - apply TotalTriple_assume.
  - apply TotalTriple_error.
  - apply (TotalTriple_cstar INV cb A R m Hwf). exact IHbody.
Qed.

Theorem TotalTriple_soundness: forall P c Q,
  ⦇ P ⦈ c ⦇ Q ⦈ -> TotalTriple P c Q.
Proof.
  intros P c Q HSH. exact (StrongHoareRes_total P c _ HSH).
Qed.


(** *** Completeness: every demonically-totally-correct triple is derivable.

    We use the semantic total weakest precondition [twp c Q = safe Q c] and show
    [⦇ twp c Q ⦈ c ⦇ Q ⦈] is derivable.  The loop case extracts a well-founded
    variant from the [safe] derivation: the relation "one successful iteration of
    the body, among loop-safe states" is well-founded precisely because [safe]
    forbids divergence. *)

Definition twp (c: com) (Q: assertion) : assertion := fun s => safe Q c s.

Lemma Strong_consequence_pre: forall P P' Q c, ⦇ P ⦈ c ⦇ Q ⦈ -> P' -->> P -> ⦇ P' ⦈ c ⦇ Q ⦈.
Proof. intros P P' Q c H HP. eapply HOARE_consequence_res; [ exact H | exact HP | intros s Hs; exact Hs ]. Qed.

Lemma Strong_consequence_post: forall P Q Q' c, ⦇ P ⦈ c ⦇ Q ⦈ -> Q -->> Q' -> ⦇ P ⦈ c ⦇ Q' ⦈.
Proof. intros P Q Q' c H HQ. eapply HOARE_consequence_res; [ exact H | intros s Hs; exact Hs | exact HQ ]. Qed.

(** Pointwise inversions of [safe]. *)

Lemma safe_skip_inv: forall Q s, safe Q SKIP s -> Q s.
Proof. intros Q s H. inversion H; subst; [ assumption | congruence ]. Qed.

Lemma safe_error_inv: forall Q s, safe Q ERROR s -> False.
Proof. intros Q s H. inversion H; subst. destruct H1 as [cs' RED]. inversion RED. Qed.

Lemma safe_assign_inv: forall Q x a s, safe Q (ASSIGN x a) s -> Q (update x (aeval a s) s).
Proof. intros Q x a s H. inversion H; subst. apply safe_skip_inv. apply H2. apply red_assign. Qed.

Lemma safe_nondet_inv: forall Q x s, safe Q (NONDET x) s -> forall n, Q (update x n s).
Proof. intros Q x s H n. inversion H; subst. apply safe_skip_inv. apply (H2 SKIP (update x n s)). apply red_nondet. Qed.

Lemma safe_choice_inv: forall Q c1 c2 s, safe Q (CHOICE c1 c2) s -> safe Q c1 s /\ safe Q c2 s.
Proof.
  intros Q c1 c2 s H. inversion H; subst. split.
  - apply (H2 c1 s). apply red_choice_left.
  - apply (H2 c2 s). apply red_choice_right.
Qed.

Lemma safe_assume_inv: forall Q b s, safe Q (ASSUME b) s -> beval b s = true /\ Q s.
Proof.
  intros Q b s H. inversion H; subst.
  destruct H1 as [[c' s'] RED]. inversion RED; subst. split.
  - assumption.
  - apply safe_skip_inv. exact (H2 SKIP s' RED).
Qed.

(** [safe] is preserved along reductions; hence the post holds at every
    reachable final ([SKIP]) state. *)

Lemma safe_red_preserve: forall P c s c' s', safe P c s -> red (c,s)(c',s') -> safe P c' s'.
Proof.
  intros P c s c' s' H RED. inversion H; subst.
  - inversion RED.
  - apply H2. exact RED.
Qed.

Lemma safe_star_preserve: forall P cfg cfg',
  star red cfg cfg' -> safe P (fst cfg) (snd cfg) -> safe P (fst cfg') (snd cfg').
Proof.
  intros P cfg cfg' STAR. induction STAR as [cfg | cfg cfg1 cfg' Hred STAR1 IH]; intro Hsafe.
  - exact Hsafe.
  - apply IH. destruct cfg as [c s]. destruct cfg1 as [c1 s1]. cbn in *.
    apply (safe_red_preserve P c s c1 s1 Hsafe Hred).
Qed.

Lemma safe_cexec_post: forall P c s x, safe P c s -> cexec s c (RNormal x) -> P x.
Proof.
  intros P c s x H Hexec. apply cexec_to_reds in Hexec.
  destruct Hexec as (cs & STAR & FIN). inversion FIN; subst.
  apply safe_skip_inv. exact (safe_star_preserve P (c,s) (SKIP,x) STAR H).
Qed.

(** Strengthen the post of a [safe] body with "this final state is reachable". *)
Lemma safe_strengthen_reach: forall P c s,
  safe P c s -> safe (fun s' => P s' /\ cexec s c (RNormal s')) c s.
Proof.
  intros P c s H.
  assert (KEY: forall c0 s0, star red (c, s) (c0, s0) -> safe P c0 s0 ->
                safe (fun s' => P s' /\ cexec s c (RNormal s')) c0 s0).
  { intros c0 s0 STAR Hsafe0. revert STAR.
    induction Hsafe0 as [s0 HP | c0 s0 Hns Hex Hrec IH]; intro STAR.
    - apply safe_skip. split; [ exact HP | apply reds_to_cexec_normal; exact STAR ].
    - apply safe_step; [ exact Hns | exact Hex | ].
      intros c' s' RED. apply IH.
      + exact RED.
      + eapply star_trans; [ exact STAR | apply star_one; exact RED ]. }
  apply KEY; [ apply star_refl | exact H ].
Qed.

(** Decompose loop-body safety out of a sequence (the [sem_wp_seq] analogue). *)
Lemma safe_seq_inv: forall Q c2 c1 s,
  safe Q (c1 ;; c2) s -> safe (fun s' => safe Q c2 s') c1 s.
Proof.
  intros Q c2.
  assert (KEY: forall cc s, safe Q cc s ->
                forall c1, cc = (c1 ;; c2) -> safe (fun s' => safe Q c2 s') c1 s).
  { intros cc s H. induction H as [s HQ | cc s Hns Hex Hrec IH]; intros c1 Ecc.
    - discriminate Ecc.
    - subst cc. destruct Hex as [[cc' sc] RED]. inversion RED; subst.
      + apply safe_skip. apply (Hrec cc' sc). apply red_seq_done.
      + exfalso. apply (safe_error_inv Q sc). apply (Hrec ERROR sc). apply red_seq_error.
      + apply safe_step.
        * intro Heq. subst c1. inversion H0.
        * exists (c3, sc). exact H0.
        * intros c'' s'' RED2. apply (IH (c'' ;; c2) s'').
          -- apply red_seq_step. exact RED2.
          -- reflexivity. }
  intros c1 s Hs. exact (KEY (c1 ;; c2) s Hs c1 (Logic.eq_refl _)).
Qed.

(** [safe (CSTAR c)] entails the postcondition (the loop may stop now) and that
    one iteration of the body lands again in a loop-safe state. *)
Lemma safe_cstar_stop: forall Q c s, safe Q (CSTAR c) s -> Q s.
Proof.
  intros Q c s H. apply (safe_skip_inv Q s).
  apply (safe_red_preserve Q (CSTAR c) s SKIP s H). apply red_cstar_done.
Qed.

Lemma safe_cstar_body: forall Q c s,
  safe Q (CSTAR c) s -> safe (fun s' => safe Q (CSTAR c) s') c s.
Proof.
  intros Q c s H. apply (safe_seq_inv Q (CSTAR c) c s).
  apply (safe_red_preserve Q (CSTAR c) s (c ;; CSTAR c) s H). apply red_cstar_step.
Qed.

(** [safe] (being inductive) makes the reduction tree well-founded. *)
Lemma safe_Acc: forall Q c s,
  safe Q c s -> Acc (fun cfg2 cfg1 => red cfg1 cfg2) (c, s).
Proof.
  intros Q c s H. induction H as [s HQ | c s Hns Hex Hrec IH].
  - apply Acc_intro. intros [c' s'] RED. inversion RED.
  - apply Acc_intro. intros [c' s'] RED. exact (IH c' s' RED).
Qed.

Lemma Acc_plus_star: forall b y, star red b y ->
  Acc (fun y x => plus red x y) b -> Acc (fun y x => plus red x y) y.
Proof.
  intros b y Hstar. induction Hstar as [b | b b1 y Hred Hstar1 IH]; intro Hb.
  - exact Hb.
  - apply IH. apply (Acc_inv Hb). apply plus_one. exact Hred.
Qed.

Lemma Acc_red_plus: forall cfg,
  Acc (fun cfg2 cfg1 => red cfg1 cfg2) cfg -> Acc (fun y x => plus red x y) cfg.
Proof.
  intros cfg H. induction H as [cfg H IH].
  apply Acc_intro. intros y Hplus. inversion Hplus; subst.
  apply (Acc_plus_star b y H1). apply IH. exact H0.
Qed.

(** Loop case: derive [⦇ twp (CSTAR c0) Q ⦈ CSTAR c0 ⦇ Q ⦈] using the
    one-iteration relation [RL] as a well-founded variant. *)
Lemma twp_cstar_der: forall c0 Q,
  (forall Q', ⦇ twp c0 Q' ⦈ c0 ⦇ Q' ⦈) ->
  ⦇ twp (CSTAR c0) Q ⦈ CSTAR c0 ⦇ Q ⦈.
Proof.
  intros c0 Q IH0.
  pose (RL := fun x s => safe Q (CSTAR c0) s /\ cexec s c0 (RNormal x)).
  assert (RL_to_plus: forall x s, cexec s c0 (RNormal x) ->
                      plus red (CSTAR c0, s) (CSTAR c0, x)).
  { intros x s Hexec. apply plus_cstar_iteration.
    apply cexec_to_reds in Hexec. destruct Hexec as (cs & STAR & FIN).
    inversion FIN; subst. exact STAR. }
  assert (safe_Acc_RL: forall s, safe Q (CSTAR c0) s -> Acc RL s).
  { assert (GEN: forall cfg, Acc (fun y x => plus red x y) cfg ->
                  forall s, cfg = (CSTAR c0, s) -> safe Q (CSTAR c0) s -> Acc RL s).
    { intros cfg Hacc. induction Hacc as [cfg Hacc IHacc]. intros s Ecfg Hsafe.
      apply Acc_intro. intros x HRL. unfold RL in HRL. destruct HRL as [_ Hexec].
      apply (IHacc (CSTAR c0, x)).
      - subst cfg. apply RL_to_plus. exact Hexec.
      - reflexivity.
      - exact (safe_cexec_post (fun s' => safe Q (CSTAR c0) s') c0 s x
                 (safe_cstar_body Q c0 s Hsafe) Hexec). }
    intros s Hsafe. apply (GEN (CSTAR c0, s)).
    - apply Acc_red_plus. apply (safe_Acc Q (CSTAR c0) s Hsafe).
    - reflexivity.
    - exact Hsafe. }
  assert (RL_wf: well_founded RL).
  { intro s. apply Acc_intro. intros x HRL. unfold RL in HRL. destruct HRL as [Hsafe Hexec].
    exact (Acc_inv (safe_Acc_RL s Hsafe) (conj Hsafe Hexec)). }
  unfold twp.
  eapply Strong_consequence_post.
  - apply (HOARE_cstar_ress (fun s => safe Q (CSTAR c0) s) c0 store RL (fun s => s) RL_wf).
    intro a. eapply Strong_consequence_pre.
    + apply (IH0 ((fun s => safe Q (CSTAR c0) s) //\\ (fun s' => RL s' a))).
    + intros s [Hsafe Heq]. cbn in Heq. subst a. unfold twp.
      eapply safe_post_mono.
      2:{ apply safe_strengthen_reach. apply safe_cstar_body. exact Hsafe. }
      intros s' [HA HB]. split; [ exact HA | ].
      unfold RL. split; [ exact Hsafe | exact HB ].
  - intros s H. exact (safe_cstar_stop Q c0 s H).
Qed.

(** [⦇ twp c Q ⦈ c ⦇ Q ⦈] is derivable, by structural induction on [c]. *)
Lemma twp_der: forall c Q, ⦇ twp c Q ⦈ c ⦇ Q ⦈.
Proof.
  intro c.
  induction c as [ | | x a | x | b | c1 IH1 c2 IH2 | c1 IH1 c2 IH2 | c0 IH0 ]; intros Q.
  - eapply Strong_consequence_pre; [ apply HOARE_skip_r | intros s H; exact (safe_skip_inv Q s H) ].
  - eapply Strong_consequence_pre; [ apply HOARE_error_r | intros s H; exact (safe_error_inv Q s H) ].
  - eapply Strong_consequence_pre; [ apply HOARE_assign_r | intros s H; exact (safe_assign_inv Q x a s H) ].
  - eapply Strong_consequence_pre; [ apply HOARE_nondet_r | intros s H n; exact (safe_nondet_inv Q x s H n) ].
  - eapply Strong_consequence_pre; [ apply HOARE_assume_r | intros s H; exact (safe_assume_inv Q b s H) ].
  - eapply Strong_consequence_pre.
    + eapply HOARE_seq_ok; [ apply (IH1 (twp c2 Q)) | apply (IH2 Q) ].
    + intros s H. exact (safe_seq_inv Q c2 c1 s H).
  - apply HOARE_choice_res.
    + eapply Strong_consequence_pre; [ apply (IH1 Q) | intros s H; exact (proj1 (safe_choice_inv Q c1 c2 s H)) ].
    + eapply Strong_consequence_pre; [ apply (IH2 Q) | intros s H; exact (proj2 (safe_choice_inv Q c1 c2 s H)) ].
  - apply twp_cstar_der. exact IH0.
Qed.

(** Relative completeness and adequacy for demonic total correctness. *)
Theorem TotalTriple_complete: forall P c Q, TotalTriple P c Q -> ⦇ P ⦈ c ⦇ Q ⦈.
Proof.
  intros P c Q H. eapply Strong_consequence_pre; [ apply twp_der | exact H ].
Qed.

Theorem TotalTriple_adequate: forall P c Q, ⦇ P ⦈ c ⦇ Q ⦈ <-> TotalTriple P c Q.
Proof.
  intros P c Q. split; [ apply TotalTriple_soundness | apply TotalTriple_complete ].
Qed.
End TotalCorrectness.
