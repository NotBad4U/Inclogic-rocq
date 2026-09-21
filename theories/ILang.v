(** * IMP as an instance of the language signature

    [CLang.v] shows the signature of [Lang.v] accommodates CompCert's Clight.
    This file shows it accommodates the language the development started
    from, and — the part that actually needs proving — that instantiating the
    generic core at IMP gives back *exactly* the semantics of [Imp.v], not
    merely something that resembles it.

    Without that, [Core.v] would be an unchecked parallel copy of [Imp.v] and
    the word "generalisation" would be doing no work.  The two theorems

    - [cexec_to_core]: every [Imp.cexec] derivation maps to a [Core.cexec] one;
    - [cexec_of_core]: and conversely;

    combine into [cexec_iff], which says the two relations agree up to the
    (structural, bijective) renaming of constructors.

    ** Where the two new rules go

    [Core.cexec] has two constructors [Imp.cexec] does not: [cexec_assign_err]
    and [cexec_assume_err], which fire when [Lang.eval] or [Lang.beval] return
    [None].  For IMP they never fire — [Lang.eval] is [Some ∘ aeval] and
    [Lang.beval] is [Some ∘ beval], both total — and that is visible in the
    proof of [cexec_of_core], where both cases are discharged by
    [discriminate] on [Some _ = None].  [eval_never_undefined] below states it
    directly.

    So the generalisation costs IMP nothing: the extra expressive power sits
    entirely in instances whose evaluation really can fail, which is to say in
    C.

    ** Why this file rather than a rewrite of [Imp.v]

    Rewriting [Imp.v] to *be* this instance is the eventual goal, but it
    forces the two extra constructors through every [inversion] in
    [Hoare.v]/[Inc.v]/[Sil.v] and their examples — some six thousand lines of
    proof.  Establishing the correspondence first makes that migration a
    mechanical rewrite against a theorem, instead of a leap. *)

From Stdlib Require Import Arith ZArith Bool String List.
From HB Require Import structures.
From mathcomp Require Import ssrfun ssrbool eqtype choice.

(** [Import] is not transitive, so requiring [Imp] loads [finmap] without
    activating its notations; the store laws below are stated in terms of
    [.[? _ ]] and [.[_ <- _]], so it has to be imported here too. *)
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import finmap.
Set Warnings "notation-incompatible-prefix".

(** [Imp.v] and [Core.v] declare the same command notations, in the same
    scope, for their respective [com] types.  Importing both is deliberate —
    the instance needs [Imp]'s [finmap] canonical structures to be active —
    and every constructor below is qualified, so the shadowing is harmless. *)
Set Warnings "-notation-overridden".
From IncLogic Require Import Lang Core Imp.

Local Open Scope fmap_scope.

(** ** The instance

    [Lang.get] is the partial [finmap] lookup, not [Imp.sget]: the signature
    wants "no value here" to be representable, and [Imp.sget] hides it behind
    the default [0].  [Imp.sget] remains what [Imp]'s own assertion language
    uses; the two agree wherever the variable is mapped. *)

Definition ImpLang : lang :=
  Lang.Make
    (* ident  *) Imp.ident
    (* value  *) Z
    (* store  *) Imp.store
    (* get    *) (fun s x => s.[? x])
    (* update *) Imp.update
    (* expr   *) Imp.aexp
    (* bexp   *) Imp.bexp
    (* eval   *) (fun a s => Some (Imp.aeval a s))
    (* beval  *) (fun b s => Some (Imp.beval b s))
    (* bnot   *) Imp.NOT.

(** ** The store laws *)

Lemma imp_get_update_same:
  forall (x : Imp.ident) (v : Z) (s : Imp.store),
  (Imp.update x v s).[? x] = Some v.
Proof.
  intros x v s. unfold Imp.update. rewrite fnd_set. rewrite eqxx. reflexivity.
Qed.

Lemma imp_get_update_other:
  forall (x y : Imp.ident) (v : Z) (s : Imp.store),
  y <> x -> (Imp.update x v s).[? y] = s.[? y].
Proof.
  intros x y v s Hne. unfold Imp.update. rewrite fnd_set.
  (* The [==] in the goal sits at [finmap]'s key eqType; writing it out here
     picks a convertible but not syntactically equal instance, so bind it
     from the goal rather than restating it. *)
  match goal with
  | |- context [if ?b then _ else _] =>
      assert (Hb : b = false) by (apply (introF eqP); exact Hne);
      rewrite Hb
  end.
  reflexivity.
Qed.

Lemma imp_store_ext:
  forall s1 s2 : Imp.store,
  (forall x : Imp.ident, s1.[? x] = s2.[? x]) -> s1 = s2.
Proof. intros s1 s2 H. exact (proj1 (fmapP s1 s2) H). Qed.

(** [Imp.NOT] negates and, since [Imp]'s evaluation is total, trivially
    preserves the (never occurring) undefinedness. *)
Lemma imp_beval_bnot:
  forall (b : Imp.bexp) (s : Imp.store),
  Some (Imp.beval (Imp.NOT b) s) = option_map negb (Some (Imp.beval b s)).
Proof. intros. reflexivity. Qed.

Definition ImpLaws : Lang.laws ImpLang :=
  Lang.Laws ImpLang
    string_dec
    imp_get_update_same
    imp_get_update_other
    imp_store_ext
    imp_beval_bnot.

(** ** The frame property

    [Imp.v] has [free_in_aexp] and [aeval_free] already; the boolean side
    needs the corresponding definition, which it lacks. *)

Fixpoint free_in_bexp (x : Imp.ident) (b : Imp.bexp) : Prop :=
  match b with
  | Imp.TRUE | Imp.FALSE => False
  | Imp.EQUAL a1 a2 | Imp.LESSEQUAL a1 a2 =>
      Imp.free_in_aexp x a1 \/ Imp.free_in_aexp x a2
  | Imp.EVEN a1 => Imp.free_in_aexp x a1
  | Imp.NOT b1 => free_in_bexp x b1
  | Imp.AND b1 b2 => free_in_bexp x b1 \/ free_in_bexp x b2
  end.

(** The signature's [fv] takes the expression first; [Imp]'s [free_in_aexp]
    takes the variable first. *)
Definition imp_fv (a : Imp.aexp) (x : Imp.ident) : Prop := Imp.free_in_aexp x a.
Definition imp_fvb (b : Imp.bexp) (x : Imp.ident) : Prop := free_in_bexp x b.

(** Bridges the signature's partial [get] to the total reader [aeval_free]
    is stated with: agreeing on [s.[? x]] implies agreeing on [Imp.sget]. *)
Lemma sget_of_fnd:
  forall (s1 s2 : Imp.store) (x : Imp.ident),
  s1.[? x] = s2.[? x] -> Imp.sget s1 x = Imp.sget s2 x.
Proof. intros s1 s2 x H. unfold Imp.sget. rewrite H. reflexivity. Qed.

Lemma imp_eval_agree:
  forall (a : Imp.aexp) (s1 s2 : Imp.store),
  (forall x : Imp.ident, imp_fv a x -> s1.[? x] = s2.[? x]) ->
  Some (Imp.aeval a s1) = Some (Imp.aeval a s2).
Proof.
  intros a s1 s2 H. f_equal. apply Imp.aeval_free.
  intros x Hx. apply sget_of_fnd. apply H. exact Hx.
Qed.

Lemma imp_beval_agree_aux:
  forall (b : Imp.bexp) (s1 s2 : Imp.store),
  (forall x : Imp.ident, free_in_bexp x b -> s1.[? x] = s2.[? x]) ->
  Imp.beval b s1 = Imp.beval b s2.
Proof.
  induction b; simpl; intros s1 s2 H; try reflexivity.
  - (* EQUAL *)
    rewrite (Imp.aeval_free s1 s2 a1), (Imp.aeval_free s1 s2 a2);
      [ reflexivity | | ];
      intros x Hx; apply sget_of_fnd; apply H; [ right | left ]; exact Hx.
  - (* LESSEQUAL *)
    rewrite (Imp.aeval_free s1 s2 a1), (Imp.aeval_free s1 s2 a2);
      [ reflexivity | | ];
      intros x Hx; apply sget_of_fnd; apply H; [ right | left ]; exact Hx.
  - (* EVEN *)
    rewrite (Imp.aeval_free s1 s2 a1); [ reflexivity | ].
    intros x Hx. apply sget_of_fnd. apply H. exact Hx.
  - (* NOT *) rewrite (IHb s1 s2 H). reflexivity.
  - (* AND *)
    rewrite (IHb1 s1 s2), (IHb2 s1 s2); [ reflexivity | | ];
      intros x Hx; apply H; [ right | left ]; exact Hx.
Qed.

Lemma imp_beval_agree:
  forall (b : Imp.bexp) (s1 s2 : Imp.store),
  (forall x : Imp.ident, imp_fvb b x -> s1.[? x] = s2.[? x]) ->
  Some (Imp.beval b s1) = Some (Imp.beval b s2).
Proof. intros b s1 s2 H. f_equal. apply imp_beval_agree_aux. exact H. Qed.

Definition ImpFrame : Lang.frame ImpLang :=
  Lang.Frame ImpLang imp_fv imp_fvb imp_eval_agree imp_beval_agree.

(** ** Evaluation is total, so the error rules are vacuous *)

Lemma eval_never_undefined:
  forall (a : Lang.expr ImpLang) (s : Lang.store ImpLang),
  Lang.eval a s <> None.
Proof. intros a s. discriminate. Qed.

Lemma beval_never_undefined:
  forall (b : Lang.bexp ImpLang) (s : Lang.store ImpLang),
  Lang.beval b s <> None.
Proof. intros b s. discriminate. Qed.

(** ** Translating the syntax

    [Imp.com] and [Core.com ImpLang] have the same constructors over the same
    payloads; these are the structural renamings between them. *)

Definition to_ann (a : Imp.loopann) : Core.loopann ImpLang :=
  match a with
  (* [I] would be read as the constructor of [True], not as a binder. *)
  | Imp.AInv Inv => @Core.AInv ImpLang Inv
  | Imp.AVar R => @Core.AVar ImpLang R
  end.

Definition of_ann (a : Core.loopann ImpLang) : Imp.loopann :=
  match a with
  | Core.AInv Inv => Imp.AInv Inv
  | Core.AVar R => Imp.AVar R
  end.

Fixpoint to_core (c : Imp.com) : Core.com ImpLang :=
  match c with
  | Imp.SKIP => @Core.SKIP ImpLang
  | Imp.ERROR => @Core.ERROR ImpLang
  | Imp.ASSIGN x a => @Core.ASSIGN ImpLang x a
  | Imp.NONDET x => @Core.NONDET ImpLang x
  | Imp.ASSUME b => @Core.ASSUME ImpLang b
  | Imp.SEQ c1 c2 => @Core.SEQ ImpLang (to_core c1) (to_core c2)
  | Imp.CHOICE c1 c2 => @Core.CHOICE ImpLang (to_core c1) (to_core c2)
  | Imp.CSTAR ann c1 => @Core.CSTAR ImpLang (option_map to_ann ann) (to_core c1)
  end.

Fixpoint of_core (c : Core.com ImpLang) : Imp.com :=
  match c with
  | Core.SKIP => Imp.SKIP
  | Core.ERROR => Imp.ERROR
  | Core.ASSIGN x a => Imp.ASSIGN x a
  | Core.NONDET x => Imp.NONDET x
  | Core.ASSUME b => Imp.ASSUME b
  | Core.SEQ c1 c2 => Imp.SEQ (of_core c1) (of_core c2)
  | Core.CHOICE c1 c2 => Imp.CHOICE (of_core c1) (of_core c2)
  | Core.CSTAR ann c1 => Imp.CSTAR (option_map of_ann ann) (of_core c1)
  end.

Definition to_res (r : Imp.result) : Core.result ImpLang :=
  match r with
  | Imp.RNormal s => @Core.RNormal ImpLang s
  | Imp.RError s => @Core.RError ImpLang s
  end.

Definition of_res (r : Core.result ImpLang) : Imp.result :=
  match r with
  | Core.RNormal s => Imp.RNormal s
  | Core.RError s => Imp.RError s
  end.

Lemma of_ann_to_ann: forall a, of_ann (to_ann a) = a.
Proof. intros [Inv|R]; reflexivity. Qed.

Lemma of_core_to_core: forall c, of_core (to_core c) = c.
Proof.
  induction c; simpl; try reflexivity.
  - rewrite IHc1, IHc2. reflexivity.
  - rewrite IHc1, IHc2. reflexivity.
  - rewrite IHc. destruct ann as [a|]; simpl; [ rewrite of_ann_to_ann | ];
      reflexivity.
Qed.

Lemma of_res_to_res: forall r, of_res (to_res r) = r.
Proof. intros [s|s]; reflexivity. Qed.

(** ** The two semantics agree *)

Theorem cexec_to_core:
  forall s c r, Imp.cexec s c r -> @Core.cexec ImpLang s (to_core c) (to_res r).
Proof.
  intros s c r H. induction H; simpl.
  - apply Core.cexec_skip.
  - apply Core.cexec_error.
  - apply (@Core.cexec_assign ImpLang s x a (Imp.aeval a s)). reflexivity.
  - apply (@Core.cexec_nondet ImpLang s x n).
  - apply Core.cexec_assume. cbn. rewrite H. reflexivity.
  - eapply Core.cexec_seq; eassumption.
  - eapply Core.cexec_seq_error; eassumption.
  - eapply Core.cexec_seq_error_right; eassumption.
  - apply Core.cexec_choice_left. assumption.
  - apply Core.cexec_choice_right. assumption.
  - apply Core.cexec_cstar_done.
  - eapply Core.cexec_cstar_step_ok; eassumption.
  - eapply Core.cexec_cstar_step_error; eassumption.
  - eapply Core.cexec_cstar_step_iter_error; eassumption.
Qed.

Theorem cexec_of_core:
  forall (s : Lang.store ImpLang) (cc : Core.com ImpLang) (r : Core.result ImpLang),
  Core.cexec s cc r -> Imp.cexec s (of_core cc) (of_res r).
Proof.
  intros s cc r H. induction H; simpl.
  - apply Imp.cexec_skip.
  - apply Imp.cexec_error.
  - (* ASSIGN, defined: the witness value is forced to be [aeval a s] *)
    cbn in H. injection H as <-. apply Imp.cexec_assign.
  - (* ASSIGN, undefined: cannot happen for IMP *)
    cbn in H. discriminate H.
  - apply Imp.cexec_nondet.
  - (* ASSUME, true *)
    cbn in H. injection H as H. apply Imp.cexec_assume. exact H.
  - (* ASSUME, undefined: cannot happen for IMP *)
    cbn in H. discriminate H.
  - eapply Imp.cexec_seq; eassumption.
  - eapply Imp.cexec_seq_error; eassumption.
  - eapply Imp.cexec_seq_error_right; eassumption.
  - apply Imp.cexec_choice_left. assumption.
  - apply Imp.cexec_choice_right. assumption.
  - apply Imp.cexec_cstar_done.
  - eapply Imp.cexec_cstar_step_ok; eassumption.
  - eapply Imp.cexec_cstar_step_error; eassumption.
  - eapply Imp.cexec_cstar_step_iter_error; eassumption.
Qed.

(** The headline: instantiating the generic core at IMP is the original IMP
    semantics, neither weaker nor stronger. *)
Theorem cexec_iff:
  forall s c r, Imp.cexec s c r <-> @Core.cexec ImpLang s (to_core c) (to_res r).
Proof.
  intros s c r. split.
  - apply cexec_to_core.
  - intro H. apply cexec_of_core in H.
    rewrite of_core_to_core, of_res_to_res in H. exact H.
Qed.
