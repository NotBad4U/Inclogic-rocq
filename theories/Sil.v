From Stdlib Require Import Arith ZArith Psatz Bool String List Program.Equality FunctionalExtensionality.
From mathcomp Require Import ssrbool eqtype choice.
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import finmap.
Set Warnings "notation-incompatible-prefix".
From IncLogic Require Import Imp Sequences Hoare Inc.

(** * Sufficient Incorrectness Logic (SIL)

    SIL (Ascari, Bruni, Gori, Logozzo) is the backward, under-approximating
    logic for Lisbon triples.  Its validity (Def. 1.1 in the paper) is

        ⟪⟪P⟫⟫ c ⟪⟪Q⟫⟫   valid   iff   ⟦⟦←c⟧⟧Q ⊇ P

    where ⟦⟦←c⟧⟧Q is the *largest* set of input states that can reach a state
    in [Q].  Unfolded on a big-step relation [cexec], this is the angelic
    "Lisbon" reading:

        every input satisfying [P] has *at least one* execution reaching [Q].

    Contrast with Incorrectness Logic ([IncTriple] in [Inc.v]), whose validity
    swaps the quantifiers (every *output* in [Q] comes from *some* input in [P]). *)


(** ** The deduction system

    [Q] is a [postassertion] throughout, so a single system uniformly handles
    normal and erroneous outcomes (exactly as in [Inc.v]). *)

(** Level 90, not the level 0 Rocq suggests for closed notations: at level 0 a
    triple is a legal application argument, so [⟪ P ⟫ SKIP ⟪ Q ⟫] re-parses as
    [SKIP] applied to a nested triple.  See the same note in [Inc.v]. *)
Set Warnings "-closed-notation-not-level-0".

Reserved Notation "⟪ P ⟫ c ⟪ 'ok' ↑ Q ⟫" (at level 90, c at next level).

Reserved Notation "⟪ P ⟫ c ⟪ 'ϵ' ↑ Q ⟫" (at level 90, c at next level).

Reserved Notation "⟪ P ⟫ c ⟪ 'err' ↑ Q ⟫" (at level 90, c at next level).

Inductive Sil_triple : assertion -> com -> postassertion -> Prop :=
| Sil_skip : forall Q,
    Sil_triple (fun s => Q (RNormal s)) SKIP Q
| Sil_error : forall Q,
    Sil_triple (fun s => Q (RError s)) ERROR Q
| Sil_assign : forall x a Q,
    Sil_triple (fun s => Q (RNormal (update x (aeval a s) s))) (ASSIGN x a) Q
| Sil_nondet : forall x Q,
    Sil_triple (fun s => exists n, Q (RNormal (update x n s))) (NONDET x) Q
| Sil_assume : forall b Q,
    Sil_triple (fun s => beval b s = true /\ Q (RNormal s)) (ASSUME b) Q
| Sil_seq : forall P R c1 c2 Q,
    Sil_triple R c2 Q ->
    Sil_triple P c1 (fun res => match res with
                                | RNormal s' => R s'
                                | RError sf  => Q (RError sf)
                                end) ->
    (*──────────────────────────*)
    Sil_triple P (SEQ c1 c2) Q
| Sil_choice : forall P1 P2 c1 c2 Q,
    Sil_triple P1 c1 Q ->
    Sil_triple P2 c2 Q ->
    (*──────────────────────────*)
    Sil_triple (P1 \\// P2) (CHOICE c1 c2) Q
| Sil_iter : forall ann c (Q: postassertion) (I: nat -> assertion),
    (* base: from [I 0] the loop may stop in [Q], or error out into [Q]
       on the very next iteration *)
    (forall s, I 0%nat s ->
        Q (RNormal s) \/ (exists sf, cexec s c (RError sf) /\ Q (RError sf))) ->
    (* step: from [I (n+1)] one successful iteration of [c] lands in [I n] *)
    (forall n, Sil_triple (I (S n)) c (fun res => match res with
                                                  | RNormal s' => I n s'
                                                  | RError _   => False
                                                  end)) ->
    (*──────────────────────────*)
    Sil_triple (fun s => exists n, I n s) (CSTAR ann c) Q
| Sil_cons : forall P P' c Q Q',
    (P -->> P') ->
    Sil_triple P' c Q' ->
    (Q' --* Q) ->
    (*──────────────────────────*)
    Sil_triple P c Q
where "⟪ P ⟫ c ⟪ 'ϵ' ↑ Q ⟫" :=
  (Sil_triple P c (fun r => match r with
                            | RNormal s => Q s
                            | RError s => Q s
                            end))
and
 "⟪ P ⟫ c ⟪ 'ok' ↑ Q ⟫" :=
  (Sil_triple P c (fun r => match r with
                            | RNormal s => Q s
                            | RError _ => False
                            end))
and "⟪ P ⟫ c ⟪ 'err' ↑ Q ⟫" :=
  (Sil_triple P c (fun r => match r with
                            | RNormal _ => False
                            | RError s => Q s
                            end)).

(** General (untagged) notation for the syntactic SIL triple, mirroring the
    [⟪⟪ P ⟫⟫ c ⟪⟪ Q ⟫⟫] notation for the semantic one below. *)
Notation "⟪ P ⟫ c ⟪ Q ⟫" := (Sil_triple P c Q) (at level 90, c at next level).


(** ** Semantic SIL triple (angelic)

    [Q] is a [postassertion] (it inspects the [result], so it can speak about
    [ok]/[err] outcomes), exactly as in [IncTriple]. *)
Definition SilTriple (P: assertion) (c: com) (Q: postassertion) : Prop :=
  forall s, P s -> exists r, cexec s c r /\ Q r.

Notation "⟪⟪ P ⟫⟫ c ⟪⟪ 'ϵ' ↑ Q ⟫⟫" :=
  (SilTriple P c (fun r => match r with
                           | RNormal s => Q s
                           | RError s  => Q s
                           end))
  (at level 90, c at next level).

Notation "⟪⟪ P ⟫⟫ c ⟪⟪ 'err' ↑ Q ⟫⟫" :=
  (SilTriple P c (fun r => match r with
                           | RNormal _ => False
                           | RError s  => Q s
                           end))
  (at level 90, c at next level).

Notation "⟪⟪ P ⟫⟫ c ⟪⟪ 'ok' ↑ Q ⟫⟫" :=
  (SilTriple P c (fun r => match r with
                           | RNormal s => Q s
                           | RError _  => False
                           end))
  (at level 90, c at next level).

Notation "⟪⟪ P ⟫⟫ c ⟪⟪ Q ⟫⟫" := (SilTriple P c Q) (at level 90, c at next level).


(** ** Relating SIL to the state-level "strong triple"

    The plain state-level triple
      [ forall s, P s -> exists s', cexec s c (RNormal s') /\ Q s' ]
    is exactly the [ok]-flavoured SIL triple. *)
Definition StrongTriple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s, P s -> exists s', cexec s c (RNormal s') /\ Q s'.

Lemma strong_triple_is_sil_ok : forall P c Q,
    StrongTriple P c Q <-> ⟪⟪ P ⟫⟫ c ⟪⟪ ok ↑ Q ⟫⟫.
Proof.
  intros P c Q. split.
  - intros H s Hs. destruct (H s Hs) as [s' [Hexec HQ]].
    exists (RNormal s'). split; [exact Hexec | exact HQ].
  - intros H s Hs. destruct (H s Hs) as [r [Hexec HQ]].
    destruct r as [s' | s'].
    + exists s'. split; [exact Hexec | exact HQ].
    + contradiction.
Qed.

(** ** Consequence: strengthen the precondition, weaken the postcondition

    The hallmark of SIL — both directions are free, unlike (demonic) total
    Hoare which can only weaken [Q]. *)
Lemma sil_consequence : forall P P' c (Q Q': postassertion),
    (P' -->> P) ->
    ⟪⟪ P ⟫⟫ c ⟪⟪ Q ⟫⟫ ->
    (Q --* Q') ->
    ⟪⟪ P' ⟫⟫ c ⟪⟪ Q' ⟫⟫.
Proof.
  intros P P' c Q Q' HP H HQ s Hs.
  destruct (H s (HP s Hs)) as [r [Hexec HQr]].
  exists r. split; [exact Hexec | apply HQ; exact HQr].
Qed.

(** ** Atomic rules *)

Lemma sil_error : forall P, ⟪⟪ P ⟫⟫ ERROR ⟪⟪ err ↑ P ⟫⟫.
Proof.
  intros P s Hs. exists (RError s). split; [apply cexec_error | exact Hs].
Qed.

Lemma sil_skip : forall P, ⟪⟪ P ⟫⟫ SKIP ⟪⟪ ok ↑ P ⟫⟫.
Proof.
  intros P s Hs. exists (RNormal s). split; [apply cexec_skip | exact Hs].
Qed.

(** ** SIL vs. demonic total Hoare

    The demonic total triple [⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈] (Hoare.v) *always* implies the
    angelic SIL triple: pick any witnessing terminating run, it satisfies [Q].
    Since [Triple] forbids errors and ranges over an [assertion] [Q], the SIL
    side is the [ok]-flavoured triple — which also lifts an [assertion] [Q], so
    the two share the same [Q] (the general [⟪⟪ Q ⟫⟫] would force [Q] to be a
    [postassertion], clashing with [⦇⦇ Q ⦈⦈]). *)
Lemma total_hoare_implies_sil : forall P c Q,
    ⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈ -> ⟪⟪ P ⟫⟫ c ⟪⟪ ok ↑ Q ⟫⟫.
Proof.
  intros P c Q H s Hs. destruct (H s Hs) as [[r Hexec] Hall].
  destruct (Hall r Hexec) as [s' [-> HQ]].
  exists (RNormal s'). split; [exact Hexec | exact HQ].
Qed.

(** The converse needs determinism: with a unique result, "some run reaches Q"
    and "all runs reach Q" coincide. *)
Definition deterministic (c: com) : Prop :=
  forall s r1 r2, cexec s c r1 -> cexec s c r2 -> r1 = r2.

Lemma sil_implies_total_hoare_det : forall P c Q,
    deterministic c ->
    ⟪⟪ P ⟫⟫ c ⟪⟪ ok ↑ Q ⟫⟫ -> ⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈.
Proof.
  intros P c Q Hdet H s Hs. destruct (H s Hs) as [r [Hexec HQ]].
  destruct r as [s' | s']; [ | contradiction ].
  split.
  - exists (RNormal s'). exact Hexec.
  - intros r' Hexec'. rewrite (Hdet s r' (RNormal s') Hexec' Hexec).
    exists s'. split; [ reflexivity | exact HQ ].
Qed.

(** Hence on the deterministic fragment SIL and the strong (demonic) Hoare
    triple coincide — matching §1.3.2 of the paper. *)
Theorem sil_eq_total_hoare_det : forall P c Q,
    deterministic c ->
    (⟪⟪ P ⟫⟫ c ⟪⟪ ok ↑ Q ⟫⟫ <-> ⦇⦇ P ⦈⦈ c ⦇⦇ Q ⦈⦈).
Proof.
  intros P c Q Hdet. split.
  - apply sil_implies_total_hoare_det; exact Hdet.
  - apply total_hoare_implies_sil.
Qed.

(** * The SIL proof system

    We now mirror [Inc.v]: an inductive deduction system [Sil_triple],
    proven sound and complete w.r.t. the semantic triple [SilTriple].
    Where IL is forward (rules track strongest postconditions), SIL is
    backward (rules track weakest preconditions), so the whole development
    is the precise dual of the IL one. *)

Local Open Scope com_scope.

Module Wp.

(** ** Weakest precondition (backward image)

    [wp c Q] is the largest set of input states that can reach [Q], i.e.
    exactly the [⟦⟦←c⟧⟧Q] of the paper.  By construction [SilTriple P c Q]
    is just [P ⊆ wp c Q]. *)
Definition wp (c: com) (Q: postassertion) : assertion :=
  fun s => exists r, cexec s c r /\ Q r.

Lemma SilTriple_wp : forall P c Q, ⟪⟪ P ⟫⟫ c ⟪⟪ Q ⟫⟫ <-> (P -->> wp c Q).
Proof. intros P c Q. split; intros H s Hs; apply H, Hs. Qed.

(** *** [wp] of each command, computed from [cexec] by inversion. *)
Lemma wp_skip : forall Q s, wp SKIP Q s <-> Q (RNormal s).
Proof.
  intros Q s. split.
  - intros [r [H HQ]]. inversion H; subst. exact HQ.
  - intros HQ. exists (RNormal s). split; [ apply cexec_skip | exact HQ ].
Qed.

Lemma wp_error : forall Q s, wp ERROR Q s <-> Q (RError s).
Proof.
  intros Q s. split.
  - intros [r [H HQ]]. inversion H; subst. exact HQ.
  - intros HQ. exists (RError s). split; [ apply cexec_error | exact HQ ].
Qed.

Lemma wp_assign : forall x a Q s,
  wp (ASSIGN x a) Q s <-> Q (RNormal (update x (aeval a s) s)).
Proof.
  intros x a Q s. split.
  - intros [r [H HQ]]. inversion H; subst. exact HQ.
  - intros HQ. exists (RNormal (update x (aeval a s) s)).
    split; [ apply cexec_assign | exact HQ ].
Qed.

Lemma wp_nondet : forall x Q s,
  wp (NONDET x) Q s <-> exists n, Q (RNormal (update x n s)).
Proof.
  intros x Q s. split.
  - intros [r [H HQ]]. inversion H; subst. exists n. exact HQ.
  - intros [n HQ]. exists (RNormal (update x n s)).
    split; [ apply cexec_nondet | exact HQ ].
Qed.

Lemma wp_assume : forall b Q s,
  wp (ASSUME b) Q s <-> beval b s = true /\ Q (RNormal s).
Proof.
  intros b Q s. split.
  - intros [r [H HQ]]. inversion H; subst. split; [ assumption | exact HQ ].
  - intros [Hb HQ]. exists (RNormal s).
    split; [ apply cexec_assume; exact Hb | exact HQ ].
Qed.

(** [wp] of a sequence: run [c1] with the postcondition that says
    "either error out into [Q], or land normally and then satisfy [wp c2 Q]". *)
Lemma wp_seq : forall c1 c2 Q s,
  wp (SEQ c1 c2) Q s
  <-> wp c1 (fun res => match res with
                        | RNormal s' => wp c2 Q s'
                        | RError sf  => Q (RError sf)
                        end) s.
Proof.
  intros c1 c2 Q s. split.
  - intros [r [H HQ]]. inversion H; subst.
    + (* cexec_seq: normal ; normal *)
      exists (RNormal s'). split; [ assumption | ].
      exists (RNormal s''). split; assumption.
    + (* cexec_seq_error: c1 errors *)
      exists (RError sf). split; assumption.
    + (* cexec_seq_error_right: c1 normal, c2 errors *)
      exists (RNormal s'). split; [ assumption | ].
      exists (RError sf). split; assumption.
  - intros [res [H1 Hmid]]. destruct res as [s' | sf].
    + destruct Hmid as [r2 [H2 HQ]]. destruct r2 as [s'' | sf].
      * exists (RNormal s''). split; [ eapply cexec_seq; eassumption | exact HQ ].
      * exists (RError sf). split; [ eapply cexec_seq_error_right; eassumption | exact HQ ].
    + exists (RError sf). split; [ apply cexec_seq_error; exact H1 | exact Hmid ].
Qed.

Lemma wp_choice : forall c1 c2 Q s,
  wp (CHOICE c1 c2) Q s <-> (wp c1 Q s \/ wp c2 Q s).
Proof.
  intros c1 c2 Q s. split.
  - intros [r [H HQ]]. inversion H; subst.
    + left.  exists r. split; assumption.
    + right. exists r. split; assumption.
  - intros [[r [H HQ]] | [r [H HQ]]].
    + exists r. split; [ apply cexec_choice_left; exact H | exact HQ ].
    + exists r. split; [ apply cexec_choice_right; exact H | exact HQ ].
Qed.

End Wp.


Module SilSoundness.

(** ** Soundness *)
Theorem Sil_triple_sound : forall P c Q,
    ⟪ P ⟫ c ⟪ Q ⟫ -> ⟪⟪ P ⟫⟫ c ⟪⟪ Q ⟫⟫.
Proof.
  intros P c Q H. induction H.
  - (* Sil_skip *)
    intros s HQ. exists (RNormal s). split; [ apply cexec_skip | exact HQ ].
  - (* Sil_error *)
    intros s HQ. exists (RError s). split; [ apply cexec_error | exact HQ ].
  - (* Sil_assign *)
    intros s HQ. exists (RNormal (update x (aeval a s) s)).
    split; [ apply cexec_assign | exact HQ ].
  - (* Sil_nondet *)
    intros s [n HQ]. exists (RNormal (update x n s)).
    split; [ apply cexec_nondet | exact HQ ].
  - (* Sil_assume *)
    intros s [Hb HQ]. exists (RNormal s).
    split; [ apply cexec_assume; exact Hb | exact HQ ].
  - (* Sil_seq *)
    intros s HP. destruct (IHSil_triple2 s HP) as [res [H1 Hmid]].
    destruct res as [s' | sf].
    + destruct (IHSil_triple1 s' Hmid) as [r [H2 HQ]]. destruct r as [s'' | sf].
      * exists (RNormal s''). split; [ eapply cexec_seq; eassumption | exact HQ ].
      * exists (RError sf). split; [ eapply cexec_seq_error_right; eassumption | exact HQ ].
    + exists (RError sf). split; [ apply cexec_seq_error; exact H1 | exact Hmid ].
  - (* Sil_choice *)
    intros s [HP1 | HP2].
    + destruct (IHSil_triple1 s HP1) as [r [H1 HQ]].
      exists r. split; [ apply cexec_choice_left; exact H1 | exact HQ ].
    + destruct (IHSil_triple2 s HP2) as [r [H2 HQ]].
      exists r. split; [ apply cexec_choice_right; exact H2 | exact HQ ].
  - (* Sil_iter *)
    rename H into Hbase. rename H0 into Hstep. rename H1 into IHstep.
    intros s [n Hn]. revert s Hn. induction n as [| m IHm]; intros s Hn.
    + (* base *)
      destruct (Hbase s Hn) as [HQ | [sf [Herr HQ]]].
      * exists (RNormal s). split; [ apply cexec_cstar_done | exact HQ ].
      * exists (RError sf). split; [ apply cexec_cstar_step_error; exact Herr | exact HQ ].
    + (* step *)
      destruct (IHstep m s Hn) as [res [Hex Hpost]]. destruct res as [s' | sf].
      * destruct (IHm s' Hpost) as [r [Hr HQ]]. destruct r as [s'' | sf2].
        -- exists (RNormal s'').
           split; [ eapply cexec_cstar_step_ok; eassumption | exact HQ ].
        -- exists (RError sf2).
           split; [ eapply cexec_cstar_step_iter_error; eassumption | exact HQ ].
      * destruct Hpost.
  - (* Sil_cons *)
    intros s HP. destruct (IHSil_triple s (H s HP)) as [r [Hex HQ']].
    exists r. split; [ exact Hex | apply H1; exact HQ' ].
Qed.

End SilSoundness.


Module SilCompleteness.
Import Wp.

(** ** Completeness

    The dual of [Inc.v]'s [sp_der]: the weakest precondition of every command
    is *derivable*.  The loop case uses an explicit backward-reachability
    family. *)

(** Backward-reachability family for [CSTAR c]:
    - [iter_base]: stop in [Q], or error out into [Q] on the next step;
    - [iter_step V]: one successful [c]-step into [V]. *)
Definition iter_base (c: com) (Q: postassertion) : assertion :=
  fun s => Q (RNormal s) \/ (exists sf, cexec s c (RError sf) /\ Q (RError sf)).
Definition iter_step (c: com) (V: assertion) : assertion :=
  fun s => exists s', cexec s c (RNormal s') /\ V s'.
Fixpoint iterI (c: com) (Q: postassertion) (n: nat) : assertion :=
  match n with
  | O   => iter_base c Q
  | S k => iter_step c (iterI c Q k)
  end.

(** Prepending successful [c]-steps stays inside the family. *)
Lemma iterI_prepend : forall c Q s s',
  star (step_iter c) s s' ->
  forall m, iterI c Q m s' -> exists n, iterI c Q n s.
Proof.
  intros c Q s s' Hstar. induction Hstar as [a | a b d Hab Hbd IH]; intros m Hm.
  - exists m. exact Hm.
  - destruct (IH m Hm) as [k Hk]. exists (S k).
    exists b. split; [ exact Hab | exact Hk ].
Qed.

(** Every state in [wp (CSTAR c) Q] is captured by the family. *)
Lemma wp_cstar_to_iterI : forall ann c Q s,
  wp (CSTAR ann c) Q s -> exists n, iterI c Q n s.
Proof.
  intros ann c Q s [r [Hex HQ]]. destruct r as [s'' | sf].
  - apply cexec_cstar_iff_star in Hex.
    eapply iterI_prepend; [ exact Hex | ]. instantiate (1 := O).
    left. exact HQ.
  - apply cexec_cstar_err_iff in Hex. destruct Hex as [s' [Hstar Herr]].
    eapply iterI_prepend; [ exact Hstar | ]. instantiate (1 := O).
    right. exists sf. split; [ exact Herr | exact HQ ].
Qed.

(** The heart of completeness: [wp c Q] is derivable, by induction on [c]. *)
Lemma wp_der : forall c Q, ⟪ wp c Q ⟫ c ⟪ Q ⟫.
Proof.
  induction c; intros Q.
  - (* SKIP *)
    eapply Sil_cons; [ | apply (Sil_skip Q) | intros r Hr; exact Hr ].
    intros s Hs. apply wp_skip. exact Hs.
  - (* ERROR *)
    eapply Sil_cons; [ | apply (Sil_error Q) | intros r Hr; exact Hr ].
    intros s Hs. apply wp_error. exact Hs.
  - (* ASSIGN *)
    eapply Sil_cons; [ | apply (Sil_assign x a Q) | intros r Hr; exact Hr ].
    intros s Hs. apply wp_assign. exact Hs.
  - (* NONDET *)
    eapply Sil_cons; [ | apply (Sil_nondet x Q) | intros r Hr; exact Hr ].
    intros s Hs. apply wp_nondet. exact Hs.
  - (* ASSUME *)
    eapply Sil_cons; [ | apply (Sil_assume b Q) | intros r Hr; exact Hr ].
    intros s Hs. apply wp_assume. exact Hs.
  - (* SEQ *)
    set (Qmid := fun res => match res with
                            | RNormal s' => wp c2 Q s'
                            | RError sf  => Q (RError sf)
                            end).
    assert (Sseq : ⟪ wp c1 Qmid ⟫ (SEQ c1 c2) ⟪ Q ⟫).
    { eapply Sil_seq with (R := wp c2 Q); [ apply IHc2 | apply IHc1 ]. }
    eapply Sil_cons; [ | exact Sseq | intros r Hr; exact Hr ].
    intros s Hs. apply wp_seq. exact Hs.
  - (* CHOICE *)
    assert (Sch : ⟪ wp c1 Q \\// wp c2 Q ⟫ (CHOICE c1 c2) ⟪ Q ⟫).
    { apply Sil_choice; [ apply IHc1 | apply IHc2 ]. }
    eapply Sil_cons; [ | exact Sch | intros r Hr; exact Hr ].
    intros s Hs. apply wp_choice. exact Hs.
  - (* CSTAR *)
    assert (Hiter : ⟪ fun s => exists n, iterI c Q n s ⟫ (CSTAR ann c) ⟪ Q ⟫).
    { apply (Sil_iter ann c Q (iterI c Q)).
      - intros s H. exact H.
      - intro n. eapply Sil_cons; [ | apply (IHc (fun res => match res with
                                                             | RNormal s' => iterI c Q n s'
                                                             | RError _   => False
                                                             end)) | intros r Hr; exact Hr ].
        intros s [s' [Hex HIn]]. exists (RNormal s'). split; [ exact Hex | exact HIn ]. }
    eapply Sil_cons; [ | exact Hiter | intros r Hr; exact Hr ].
    intros s Hs. apply (wp_cstar_to_iterI ann). exact Hs.
Qed.

Theorem Sil_complete : forall P c Q,
    ⟪⟪ P ⟫⟫ c ⟪⟪ Q ⟫⟫ -> ⟪ P ⟫ c ⟪ Q ⟫.
Proof.
  intros P c Q H. eapply Sil_cons.
  - apply SilTriple_wp. exact H.
  - apply wp_der.
  - intros r Hr; exact Hr.
Qed.

End SilCompleteness.

(** [wp] (from [Module Wp]) back in scope for the dual characterizations below. *)
Import Wp.

(** * Connection with Incorrectness Logic

    IL ([IncTriple], from [Inc.v]) and SIL are the two under-approximation
    corners of the taxonomy (Fig. 3 of the paper): both quantify over the same
    relation [cexec], but IL reads it *forward* (every Q-result has a
    P-predecessor) while SIL reads it *backward* (every P-state has a
    Q-successor):

      IncTriple P c Q  :=  forall r, Q r -> exists s, P s /\ cexec s c r
      SilTriple P c Q  :=  forall s, P s -> exists r, cexec s c r /\ Q r

    Note (paper §1.4): unlike HL/NC, IL and SIL are *not* linked by negation,
    and neither implies the other — the dual distribution laws below witness
    their independence. *)

(** The forward image (IL's strongest post, as a [postassertion]); the exact
    dual of [wp]. *)
Definition isp (c: com) (P: assertion) : postassertion :=
  fun r => exists s, P s /\ cexec s c r.

(** The two validity characterizations, side by side:
    IL valid iff [Q ⊆ isp c P]; SIL valid iff [P ⊆ wp c Q]. *)
Lemma IncTriple_isp : forall P c Q, IncTriple P c Q <-> (Q --* isp c P).
Proof. intros P c Q. split; intros H r Hr; apply H, Hr. Qed.

(** A single transition, seen from either side. *)
Lemma cexec_isp_point : forall s c r, cexec s c r <-> isp c (fun x => x = s) r.
Proof.
  intros s c r. split.
  - intros H. exists s. split; [ reflexivity | exact H ].
  - intros [s0 [Hs0 H]]. subst s0. exact H.
Qed.

Lemma cexec_wp_point : forall s c r, cexec s c r <-> wp c (fun y => y = r) s.
Proof.
  intros s c r. split.
  - intros H. exists r. split; [ exact H | reflexivity ].
  - intros [r0 [H Hr0]]. subst r0. exact H.
Qed.

(** ** [sp] and [wp] are the same thing, transposed

    The strongest post [isp] (forward image) and the weakest precondition [wp]
    (backward image) are not literally equal — they have different types
    ([postassertion] vs [assertion]) — but they are the two transposes of the
    one relation [cexec], so they carry exactly the same information.

    Pointwise, on singletons, they *coincide*: both [isp c {s}] at [r] and
    [wp c {r}] at [s] say precisely [cexec s c r]. *)
Lemma sp_wp_point : forall s c r,
  isp c (fun x => x = s) r <-> wp c (fun y => y = r) s.
Proof.
  intros s c r. split.
  - intros [s0 [-> HX]]. exists r. split; [ exact HX | reflexivity ].
  - intros [r0 [HX ->]]. exists s. split; [ reflexivity | exact HX ].
Qed.

(** In general they are *adjoint* (Frobenius reciprocity): the forward image of
    [P] meets [Q] iff [P] meets the backward image of [Q].  Both sides unfold to
    [exists s r, P s /\ cexec s c r /\ Q r] — the witnessing transition, read
    from either end. *)
Theorem sp_wp_adjoint : forall P c Q,
  (exists r, isp c P r /\ Q r) <-> (exists s, P s /\ wp c Q s).
Proof.
  intros P c Q. split.
  - intros [r [[s [HP HX]] HQ]].
    exists s. split; [ exact HP | exists r; split; [ exact HX | exact HQ ] ].
  - intros [s [HP [r [HX HQ]]]].
    exists r. split; [ exists s; split; [ exact HP | exact HX ] | exact HQ ].
Qed.

(** Atomic agreement: on singletons IL and SIL triples coincide — both assert
    exactly that [c] can step from [s] to [r]. This is the shared kernel of the
    two logics. *)
Lemma sil_inc_atomic : forall s c r,
  ⟪⟪ fun x => x = s ⟫⟫ c ⟪⟪ fun y => y = r ⟫⟫
  <-> IncTriple (fun x => x = s) c (fun y => y = r).
Proof.
  intros s c r. split.
  - intros H r' Hr'. subst r'. assert (Hs : s = s) by reflexivity.
    destruct (H s Hs) as [r0 [Hex Heq]]. subst r0.
    exists s. split; [ reflexivity | exact Hex ].
  - intros H s' Hs'. subst s'. assert (Hr : r = r) by reflexivity.
    destruct (H r Hr) as [s0 [Heq Hex]]. subst s0.
    exists r. split; [ exact Hex | reflexivity ].
Qed.

(** ** The dual distribution laws — the leading IL/SIL distinction (paper §1.4, §6.5)

    IL distributes over disjunction in the POSTcondition, whereas SIL
    distributes over disjunction in the PREcondition.  This asymmetry is
    exactly why "IL drops disjuncts in postconditions, SIL in preconditions". *)
Lemma Inc_split_post : forall P c (Q1 Q2: postassertion),
  IncTriple P c (fun r => Q1 r \/ Q2 r) <-> IncTriple P c Q1 /\ IncTriple P c Q2.
Proof.
  intros P c Q1 Q2. split.
  - intros H. split.
    + intros r Hr. apply H. left.  exact Hr.
    + intros r Hr. apply H. right. exact Hr.
  - intros [H1 H2] r [Hr | Hr]; [ apply H1 | apply H2 ]; exact Hr.
Qed.

Lemma Sil_split_pre : forall (P1 P2: assertion) c Q,
  ⟪⟪ P1 \\// P2 ⟫⟫ c ⟪⟪ Q ⟫⟫ <-> ⟪⟪ P1 ⟫⟫ c ⟪⟪ Q ⟫⟫ /\ ⟪⟪ P2 ⟫⟫ c ⟪⟪ Q ⟫⟫.
Proof.
  intros P1 P2 c Q. split.
  - intros H. split.
    + intros s Hs. apply H. left.  exact Hs.
    + intros s Hs. apply H. right. exact Hs.
  - intros [H1 H2] s [Hs | Hs]; [ apply H1 | apply H2 ]; exact Hs.
Qed.
