(** * Encoding examples of Section 6 in O'Hearn's "Incorrectness Logic".

  These encode the four programs of _Figure 5_ (loop0, client0, loop1, loop2)
  and state the Incorrectness Logic triples discussed in §6.1.

  Procedures are modelled as plain [Definition]s and inlined at call sites because we do not support yet a _principle of reuse _.
*)

From Stdlib Require Import Arith ZArith Psatz Bool String List
  Program.Equality FunctionalExtensionality.
From mathcomp Require Import ssrbool eqtype choice.
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import finmap.
Set Warnings "notation-incompatible-prefix".
From IncLogic Require Import Imp Sequences Hoare Inc.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope com_scope.

(** ** loop1 — Fig 5, lines 18-24.

    Two specs in the paper:
      achieves1: [ok: x==0 \/ x==1 \/ x==2 \/ x==3]   (three unrollings)
      achieves2: [ok: x>=0]                            (backwards-variant)

    The [x \in domf s] conjunct in the post is forced by the finmap store
    model: if [x] is unmapped, [s "x"] reads as [0%Z] (sget default), but no
    execution of [loop1] produces a state with [x] unmapped — [ASSIGN "x" ...]
    always adds it.  The paper's spec elides this because its store is a total
    function. *)

Definition loop1_body : com :=
  ASSIGN "x" ("x" + 1).

Definition loop1 : com :=
  ASSIGN "x" 0 ;; (loop1_body ★).

(** Backwards-variant with [P n s := s "x" = Z.of_nat n /\ "x" \in domf s]. *)
Lemma loop1_achieves2 :
  ⟦⟦ ⊤ ⟧⟧
  loop1
  ⟦⟦ ok ↑ ("x" ⩾ 0 ∧ def "x") ⟧⟧.
Proof.
  unfold loop1.
  pose (Pn := fun (n: nat) (s: store) =>
                s "x" = Z.of_nat n /\ "x" \in domf s).
  refine (inc_triple_seq_ok _ (ASSIGN "x" 0) (CSTAR None loop1_body)
                            (Pn 0%nat) _ _ _).
  - (* [true] x := 0 [ok: P 0] *)
    intros r HQ. destruct r as [s' | s']; [ | exfalso; exact HQ ].
    destruct HQ as [Hx0 Hdom]. unfold Pn in *. cbn in Hx0.
    exists s'. split; [ exact I | ].
    replace s' with (update "x" (aeval 0 s') s') at 2.
    + apply cexec_assign.
    + cbn [aeval]. rewrite <- Hx0. apply update_get. exact Hdom.
  - eapply inc_triple_consequence_gen with (P := Pn 0%nat).
    + unfold aimp. intros s HP0. exact HP0.
    + apply inc_triple_ok_cstar with (P := Pn).
      intros n. unfold loop1_body.
      intros r HQ. destruct r as [s' | s']; [ | exfalso; exact HQ ].
      destruct HQ as [Hxv Hdom_s']. unfold Pn in *.
      exists (update "x" (Z.of_nat n) s'). split.
      * split; [ apply update_same | ].
        rewrite dom_update, eqxx. reflexivity.
      * replace s' with
          (update "x" (aeval ("x" + 1) (update "x" (Z.of_nat n) s'))
                       (update "x" (Z.of_nat n) s')) at 2.
        ** apply cexec_assign.
        ** cbn [aeval]. rewrite update_same.
           rewrite update_shadow.
           replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
           rewrite <- Hxv. apply update_get. exact Hdom_s'.
    + intros r HQ. destruct r as [s | s]; [ | exfalso; exact HQ ].
      destruct HQ as [Hxnn Hdom].
      exists (Z.to_nat (s "x")). unfold Pn. split; [ | exact Hdom ].
      rewrite Z2Nat.id; [ reflexivity | exact Hxnn ].
Qed.

(** [achieves1] is a [consequence]-strengthening of [achieves2]: in IL the
    post can be strengthened (smaller set of states to cover) for free, and
    [{0,1,2,3}] is a subset of the nonneg integers.  The paper proves it via
    three unrollings to showcase the unrolling rule, but logically that's
    not needed once [achieves2] is in hand. *)
Lemma loop1_achieves1 :
  ⟦⟦ ⊤ ⟧⟧
  loop1
  ⟦⟦ ok ↑ (("x" ≐ 0 ∨ "x" ≐ 1 ∨ "x" ≐ 2 ∨ "x" ≐ 3) ∧ def "x") ⟧⟧.
Proof.
  eapply inc_triple_consequence_gen with (P := ⊤%A).
  - unfold aimp; auto.
  - exact loop1_achieves2.
  - intros r HQ. destruct r as [s | s]; [ | exfalso; exact HQ ].
    cbn [aeval] in *.
    destruct HQ as [Hcase Hdom]. split; [ | exact Hdom ].
    destruct Hcase as [H | [H | [H | H]]]; rewrite H; lia.
Qed.

(** ** loop2 — Fig 5, lines 32-38.

    The Kleene-star body errors when [x = 2,000,000].  The IL triple captures
    that the error is reachable: [er: x == 2,000,000]. *)

Definition loop2_body : com :=
  (IF (EQUAL "x" 2000000) THEN ERROR END) ;;
  ASSIGN "x" ("x" + 1).

Definition loop2 : com :=
  ASSIGN "x" 0 ;; (loop2_body ★).

(** Body advances [x] by 1 when [x < 2,000,000]. *)
Lemma loop2_body_normal_step:
  forall (s : store),
  s "x" < 2000000 ->
  "x" \in domf s ->
  cexec s loop2_body (RNormal (update "x" (s "x" + 1) s)).
Proof.
  intros s Hlt Hdom.
  unfold loop2_body.
  apply cexec_seq with s.
  - apply cexec_choice_right.
    apply cexec_seq with s.
    + apply cexec_assume. cbn.
      assert (Hne : (s "x" =? 2000000) = false) by (apply Z.eqb_neq; lia).
      rewrite Hne. reflexivity.
    + apply cexec_skip.
  - replace (update "x" (s "x" + 1) s)
      with (update "x" (aeval ("x" + 1) s) s).
    + apply cexec_assign.
    + cbn [aeval]. reflexivity.
Qed.

(** Body errors with state preserved when [x = 2,000,000]. *)
Lemma loop2_body_error_step:
  forall (s : store),
  s "x" = 2000000 ->
  cexec s loop2_body (RError s).
Proof.
  intros s Heq.
  unfold loop2_body.
  apply cexec_seq_error.
  apply cexec_choice_left.
  apply cexec_seq_error_right with s.
  - apply cexec_assume. cbn. rewrite Heq. reflexivity.
  - apply cexec_error.
Qed.

(** From a state with [x = m] in domain, advancing by a nonneg [k : Z] via
    successful body iterations lands at [update "x" (m + k) s], provided
    [m + k ≤ 2,000,000].  Stated over [Z] (not [nat]) to avoid the huge
    [2000000%nat] literal that breaks [lia]. *)
Lemma loop2_iter_Z:
  forall (k : Z),
  0 <= k ->
  forall (s : store),
  "x" \in domf s ->
  s "x" + k <= 2000000 ->
  star (step_iter loop2_body) s (update "x" (s "x" + k) s).
Proof.
  apply (Wf_Z.natlike_ind (fun k => forall (s : store),
           "x" \in domf s -> s "x" + k <= 2000000 ->
           star (step_iter loop2_body) s (update "x" (s "x" + k) s))).
  - (* k = 0 *) intros s Hdom _.
    rewrite Z.add_0_r, update_get; [ apply star_refl | exact Hdom ].
  - (* k = Z.succ k' *) intros k Hk_pos IH s Hdom Hle.
    eapply star_step.
    + unfold step_iter. apply loop2_body_normal_step; [ lia | exact Hdom ].
    + set (s1 := update "x" (s "x" + 1) s).
      assert (Hd1 : "x" \in domf s1)
        by (unfold s1; rewrite dom_update, eqxx; reflexivity).
      assert (Hx1 : s1 "x" = s "x" + 1) by (unfold s1; apply update_same).
      assert (Hreach : star (step_iter loop2_body) s1
                             (update "x" (s1 "x" + k) s1)).
      { apply IH; [ exact Hd1 | rewrite Hx1; lia ]. }
      rewrite Hx1 in Hreach.
      replace (update "x" (s "x" + Z.succ k) s)
        with (update "x" (s "x" + 1 + k) s1)
        by (unfold s1; rewrite update_shadow; f_equal; lia).
      exact Hreach.
Qed.

Lemma loop2_correct :
  ⟦⟦ ⊤ ⟧⟧
  loop2
  ⟦⟦ err ↑ aequal "x" 2000000 ⟧⟧.
Proof.
  unfold loop2.
  intros r HQ.
  destruct r as [s' | s']; [ exfalso; exact HQ | ].
  unfold aequal in HQ. cbn in HQ.
  (* [s' "x" = 2000000] forces ["x" \in domf s'] (sget default is 0). *)
  assert (Hdom : "x" \in domf s').
  { pose proof (fndSome s' "x") as HS.
    unfold sget in HQ.
    destruct (s' .[? "x"]%fmap) as [v | ] eqn:Hf.
    - cbn in HS. symmetry; exact HS.
    - cbn in HQ. lia. }
  exists s'. split; [ exact I | ].
  eapply cexec_seq_error_right.
  - apply cexec_assign.
  - cbn [aeval].
    apply cexec_cstar_err_iff.
    exists s'. split.
    + pose proof (loop2_iter_Z 2000000 ltac:(lia) (update "x" 0 s')) as Hiter.
      assert (Hd0 : "x" \in domf (update "x" 0 s'))
        by (rewrite dom_update, eqxx; reflexivity).
      assert (Hx0 : (update "x" 0 s') "x" = 0) by apply update_same.
      specialize (Hiter Hd0).
      rewrite Hx0 in Hiter. cbn in Hiter.
      specialize (Hiter ltac:(lia)).
      replace s' with (update "x" 2000000 (update "x" 0 s')) at 2;
        [ exact Hiter | ].
      rewrite update_shadow. rewrite <- HQ. apply update_get. exact Hdom.
    + apply loop2_body_error_step. exact HQ.
Qed.

(** ** loop0 — Fig 5, lines 3-10.

    [int n = nondet(); x = 0; while (n > 0) { x = x+n; n = nondet(); }]

    No local-variable scoping in IMP: [n] is just a global identifier.
    The paper's spec [true] loop0 [ok: x>=0] relies on existentially
    quantifying [n] via the local-variable rule, which we don't have.  The
    strongest IL post we can state directly is [x>=0 ∧ n<=0] — the loop exit
    [ASSUME (NOT (n>0))] forces [n <= 0] on every reachable state.  Reached
    by either 0 iterations (when [s' "x" = 0]) or 1 iteration with
    [n_init = s' "x"] (when [s' "x" > 0]). *)

Definition loop0_body : com :=
  ASSIGN "x" ("x" + "n") ;;
  NONDET "n".

Definition loop0 : com :=
  NONDET "n" ;;
  ASSIGN "x" 0 ;;
  WHILE (GREATER "n" 0) DO loop0_body END.

(** Updates on distinct keys commute. *)
Lemma update_swap:
  forall (x y : ident) (u v : Z) (s : store),
  x <> y -> update x u (update y v s) = update y v (update x u s).
Proof.
  intros x y u v s Hxy.
  apply fmapP. intros k.
  unfold update. rewrite !fnd_set.
  destruct ((k == x)%bool) eqn:Ekx; destruct ((k == y)%bool) eqn:Eky;
    try reflexivity.
  exfalso. apply Hxy.
  assert (Hrx : reflect (k = x) (k == x)) by apply string_eqbP.
  assert (Hry : reflect (k = y) (k == y)) by apply string_eqbP.
  rewrite Ekx in Hrx. rewrite Eky in Hry.
  inversion Hrx. inversion Hry. congruence.
Qed.

Lemma loop0_correct :
  ⟦⟦ ⊤ ⟧⟧
  loop0
  ⟦⟦ ok ↑ ("x" ⩾ 0 ∧ "n" ⩽ 0 ∧ def "x" ∧ def "n") ⟧⟧.
Proof.
  unfold loop0.
  intros r HQ. destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [Hxnn [Hnnp [Hdx Hdn]]]. cbn [aeval] in *.
  exists s'. split; [ exact I | ].
  (* Use [s' "n" ≤ 0] for the loop-exit [ASSUME]. *)
  assert (Hexit : beval (NOT (GREATER "n" 0)) s' = true).
  { cbn. assert (Hb : (s' "n" <=? 0) = true)
      by (apply Z.leb_le; exact Hnnp).
    rewrite Hb. reflexivity. }
  destruct (Z.eq_dec (s' "x") 0) as [Hx0 | Hx_ne].
  - (* Case: s' "x" = 0, 0 WHILE iterations *)
    apply cexec_seq with (update "n" (s' "n") s').
    { apply cexec_nondet. }
    apply cexec_seq with (update "x" 0 (update "n" (s' "n") s')).
    { replace (update "x" 0 (update "n" (s' "n") s'))
        with (update "x" (aeval 0 (update "n" (s' "n") s'))
                          (update "n" (s' "n") s'))
        by (cbn [aeval]; reflexivity).
      apply cexec_assign. }
    (* update "x" 0 (update "n" (s' "n") s') = s' *)
    assert (Heq : update "x" 0 (update "n" (s' "n") s') = s').
    { rewrite (update_get "n" s' Hdn).
      rewrite <- Hx0. apply update_get; exact Hdx. }
    rewrite Heq.
    apply cexec_seq with s'.
    { apply cexec_cstar_done. }
    { apply cexec_assume. exact Hexit. }
  - (* Case: s' "x" > 0, 1 WHILE iteration with n_init = s' "x" *)
    assert (Hxpos : 0 < s' "x") by lia.
    apply cexec_seq with (update "n" (s' "x") s').
    { apply cexec_nondet. }
    apply cexec_seq with (update "x" 0 (update "n" (s' "x") s')).
    { replace (update "x" 0 (update "n" (s' "x") s'))
        with (update "x" (aeval 0 (update "n" (s' "x") s'))
                          (update "n" (s' "x") s'))
        by (cbn [aeval]; reflexivity).
      apply cexec_assign. }
    (* Goal: WHILE = ((ASSUME ;; body)★) ;; ASSUME exit, starting from
       update "x" 0 (update "n" (s' "x") s'), reaches s'. *)
    apply cexec_seq with s'.
    + (* CSTAR ((ASSUME (n>0)) ;; body): one iteration to s' *)
      eapply cexec_cstar_step_ok.
      * (* (ASSUME (n>0)) ;; body *)
        eapply cexec_seq.
        ** (* ASSUME (n > 0): n = s' "x" > 0 here *)
           apply cexec_assume.
           cbn.
           assert (Hnval : (update "x" 0 (update "n" (s' "x") s')) "n" = s' "x").
           { rewrite update_other; [ apply update_same | discriminate ]. }
           rewrite Hnval.
           assert (Hb : (s' "x" <=? 0) = false) by (apply Z.leb_gt; exact Hxpos).
           rewrite Hb. reflexivity.
        ** (* body = ASSIGN "x" (x+n) ;; NONDET "n" *)
           eapply cexec_seq.
           *** apply cexec_assign.
           *** apply cexec_nondet with (n := s' "n").
      * (* After one iter, the state needs to be s'; then cexec_cstar_done. *)
        match goal with
        | |- cexec ?st _ _ =>
          assert (Heq : st = s');
          [ | rewrite Heq; apply cexec_cstar_done ]
        end.
        cbn [aeval].
        rewrite update_same.    (* (update "x" 0 (update "n" (s' "x") s')) "x" = 0 *)
        rewrite update_other; [ | discriminate ].   (* read "n" through "x" update *)
        rewrite update_same.    (* (update "n" (s' "x") s') "n" = s' "x" *)
        rewrite Z.add_0_l.      (* 0 + s' "x" = s' "x" *)
        rewrite update_shadow.  (* update "x" v (update "x" 0 ...) = update "x" v ... *)
        rewrite update_swap with (x := "n") (y := "x"); [ | discriminate ].
        rewrite update_shadow.  (* update "n" (s'"n") (update "n" (s'"x") s') = update "n" (s'"n") s' *)
        rewrite (update_get "n" s' Hdn).
        rewrite (update_get "x" s' Hdx).
        reflexivity.
    + apply cexec_assume. exact Hexit.
Qed.

(** ** client0 — Fig 5, lines 12-16.

    [loop0(); if (x==2,000,000) {error();}]

    Inline [loop0] at the call site.  The IL triple says there exists an
    execution that ends in error with [x == 2,000,000]: [loop0] takes one
    iteration with [n_init == 2,000,000], then [n = nondet()] picks
    [n <= 0], the loop exits with [x == 2,000,000], and the conditional
    fires.

    Same caveat as [loop0_correct]: the post must constrain [n] (which is
    a globally visible identifier without the local-variable rule). *)

Definition client0 : com :=
  loop0 ;;
  IF (EQUAL "x" 2000000) THEN ERROR END.

Lemma client0_correct :
  ⟦⟦ ⊤ ⟧⟧
  client0
  ⟦⟦ err ↑ ("x" ≐ 2000000 ∧ "n" ⩽ 0 ∧ def "n") ⟧⟧.
Proof.
  unfold client0.
  intros r HQ. destruct r as [s' | s']; [ exfalso; exact HQ | ].
  destruct HQ as [Hx2M [Hnnp Hdn]]. cbn [aeval] in *.
  (* [s' "x" = 2,000,000 ≠ 0] forces ["x" \in domf s']. *)
  assert (Hdx : "x" \in domf s').
  { pose proof (fndSome s' "x") as HS.
    unfold sget in Hx2M.
    destruct (s' .[? "x"]%fmap) as [v | ] eqn:Hf.
    - cbn in HS. symmetry; exact HS.
    - cbn in Hx2M. lia. }
  (* [loop0_correct] supplies a pre-state and an exec ending at [s']. *)
  destruct (loop0_correct (RNormal s')) as (s_pre & _ & EXEC_loop0).
  { cbn. split; [ lia | split; [ exact Hnnp | split; [ exact Hdx | exact Hdn ] ] ]. }
  exists s_pre. split; [ exact I | ].
  eapply cexec_seq_error_right.
  - exact EXEC_loop0.
  - (* [IF (x==2,000,000) THEN ERROR END] errors at [s']. *)
    apply cexec_choice_left.
    eapply cexec_seq_error_right.
    + apply cexec_assume. cbn. rewrite Hx2M. apply Z.eqb_refl.
    + apply cexec_error.
Qed.
