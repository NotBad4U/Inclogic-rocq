(** * Executable evaluation of fragment expressions

    [Lang.eval] must be a *function* [expr -> store -> option value], but
    CompCert specifies Clight expression evaluation as an inductive
    *relation*, [Clight.eval_expr].  This file bridges the two, for the
    expressions of the allocation-free fragment of [CFrag.v]:

    - [ceval] computes the value of an expression, or [None];
    - [ceval_sound] says every value it computes is one CompCert's relation
      admits;
    - [ceval_complete] says the converse on the fragment — so on the fragment
      the two agree exactly, and in particular [ceval le a = None] means
      CompCert's relation admits *no* value, i.e. the Clight program is stuck.

    That last reading is the payoff.  A stuck Clight state is how CompCert
    renders undefined behaviour, so "[ceval] returned [None]" is a genuine
    bug report, and it is one an incorrectness logic can chain into a
    reachability proof rather than merely assert.

    The reason a total function exists at all is that CompCert already writes
    the hard parts — [sem_unary_operation], [sem_binary_operation],
    [sem_cast], [bool_val] — as partial *functions* returning [option val].
    Once the memory-touching expression forms are excluded, the only
    remaining relational step is [eval_Elvalue], and the fragment has no
    l-values at all ([eval_lvalue_frag] below).  So the whole relation
    collapses to a fold over those four functions.

    Being executable is also what makes the search of [IncElpi.v] portable to
    C: where the IMP search inverts [aeval] symbolically, here it can simply
    [vm_compute] a [ceval]. *)

From Stdlib Require Import List Bool.
From compcert Require Import lib.Coqlib lib.Maps lib.Integers common.AST
     common.Values common.Memory cfrontend.Ctypes cfrontend.Cop cfrontend.Clight
     export.Ctypesdefs.
From IncLogic Require Import CFrag.

Import ListNotations.
Local Open Scope bool_scope.

Section EVAL.

(** The global environment supplies the composite environment that sizes and
    binary operations consult; the memory is a *parameter*, never part of the
    state.  [CFrag.function_entry2_alloc_free] is what licenses that: in this
    fragment nothing allocates and nothing writes, so [m] is fixed for the
    whole execution. *)

Variable ge : genv.
Variable m : mem.

(** ** The evaluator *)

Fixpoint ceval (le: temp_env) (a: expr) : option val :=
  match a with
  | Econst_int i _ => Some (Vint i)
  | Econst_float f _ => Some (Vfloat f)
  | Econst_single f _ => Some (Vsingle f)
  | Econst_long i _ => Some (Vlong i)
  | Etempvar id _ => le ! id
  | Esizeof ty1 _ => Some (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
  | Ealignof ty1 _ => Some (Vptrofs (Ptrofs.repr (alignof ge ty1)))
  | Eunop op a1 _ =>
      match ceval le a1 with
      | Some v1 => sem_unary_operation op v1 (typeof a1) m
      | None => None
      end
  | Ebinop op a1 a2 _ =>
      match ceval le a1, ceval le a2 with
      | Some v1, Some v2 =>
          sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m
      | _, _ => None
      end
  | Ecast a1 ty =>
      match ceval le a1 with
      | Some v1 => sem_cast v1 (typeof a1) ty m
      | None => None
      end
  (** Outside the fragment: these are the l-value forms, and reading them
      would touch memory. *)
  | Evar _ _ | Ederef _ _ | Eaddrof _ _ | Efield _ _ _ => None
  end.

(** ** No expression of the fragment is an l-value

    This is the lemma that lets [eval_Elvalue] be discarded in every
    inversion below, and hence the reason [ceval] can be a plain fold. *)

Lemma eval_lvalue_frag:
  forall le a l ofs bf,
  expr_frag a = true ->
  ~ eval_lvalue ge empty_env le m a l ofs bf.
Proof.
  intros le a l ofs bf HF H.
  inversion H; subst; simpl in HF; discriminate.
Qed.

(** Discharges the [eval_Elvalue] case of an inversion: the head is not an
    l-value form, so the [eval_lvalue] hypothesis has no constructor. *)
Local Ltac no_lvalue :=
  match goal with
  | H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => solve [ inversion H ]
  end.

(** ** Soundness: what [ceval] computes, CompCert admits

    Note this direction needs no fragment hypothesis — [ceval] returns [None]
    on the out-of-fragment forms, so there is nothing to prove for them. *)

Theorem ceval_sound:
  forall le a v, ceval le a = Some v -> eval_expr ge empty_env le m a v.
Proof.
  intros le a. induction a; simpl; intros v H; try discriminate.
  - (* Econst_int *) injection H as <-. constructor.
  - (* Econst_float *) injection H as <-. constructor.
  - (* Econst_single *) injection H as <-. constructor.
  - (* Econst_long *) injection H as <-. constructor.
  - (* Etempvar *) constructor. exact H.
  - (* Eunop *)
    destruct (ceval le a) as [v1|] eqn:E; [| discriminate].
    econstructor; [ apply IHa; reflexivity | exact H ].
  - (* Ebinop *)
    destruct (ceval le a1) as [v1|] eqn:E1; [| discriminate].
    destruct (ceval le a2) as [v2|] eqn:E2; [| discriminate].
    econstructor; [ apply IHa1; reflexivity | apply IHa2; reflexivity | exact H ].
  - (* Ecast *)
    destruct (ceval le a) as [v1|] eqn:E; [| discriminate].
    econstructor; [ apply IHa; reflexivity | exact H ].
  - (* Esizeof *) injection H as <-. constructor.
  - (* Ealignof *) injection H as <-. constructor.
Qed.

(** ** Completeness: on the fragment, CompCert admits nothing else *)

Theorem ceval_complete:
  forall le a v,
  expr_frag a = true ->
  eval_expr ge empty_env le m a v ->
  ceval le a = Some v.
Proof.
  intros le a. induction a; simpl; intros v HF H; try discriminate.
  - (* Econst_int *) inversion H; subst; [ reflexivity | no_lvalue ].
  - (* Econst_float *) inversion H; subst; [ reflexivity | no_lvalue ].
  - (* Econst_single *) inversion H; subst; [ reflexivity | no_lvalue ].
  - (* Econst_long *) inversion H; subst; [ reflexivity | no_lvalue ].
  - (* Etempvar *) inversion H; subst; [ assumption | no_lvalue ].
  - (* Eunop *)
    inversion H; subst; [| no_lvalue ].
    match goal with
    | Hsub : eval_expr _ _ _ _ a ?v1,
      Hop  : sem_unary_operation _ ?v1 _ _ = Some v |- _ =>
        rewrite (IHa v1 HF Hsub); exact Hop
    end.
  - (* Ebinop *)
    apply andb_prop in HF as [HF1 HF2].
    inversion H; subst; [| no_lvalue ].
    match goal with
    | H1 : eval_expr _ _ _ _ a1 ?v1,
      H2 : eval_expr _ _ _ _ a2 ?v2,
      Hop : sem_binary_operation _ _ ?v1 _ ?v2 _ _ = Some v |- _ =>
        rewrite (IHa1 v1 HF1 H1), (IHa2 v2 HF2 H2); exact Hop
    end.
  - (* Ecast *)
    inversion H; subst; [| no_lvalue ].
    match goal with
    | H1  : eval_expr _ _ _ _ a ?v1,
      Hop : sem_cast ?v1 _ _ _ = Some v |- _ =>
        rewrite (IHa v1 HF H1); exact Hop
    end.
  - (* Esizeof *) inversion H; subst; [ reflexivity | no_lvalue ].
  - (* Ealignof *) inversion H; subst; [ reflexivity | no_lvalue ].
Qed.

(** ** The two consequences that matter

    Determinism, and the reading of [None] as undefined behaviour. *)

Corollary ceval_det:
  forall le a v1 v2,
  expr_frag a = true ->
  eval_expr ge empty_env le m a v1 ->
  eval_expr ge empty_env le m a v2 ->
  v1 = v2.
Proof.
  intros le a v1 v2 HF H1 H2.
  pose proof (ceval_complete le a v1 HF H1) as E1.
  pose proof (ceval_complete le a v2 HF H2) as E2.
  congruence.
Qed.

(** [None] is undefined behaviour: CompCert's relation gives the expression
    no value whatsoever, so a Clight state about to evaluate it is stuck. *)
Corollary ceval_none_stuck:
  forall le a,
  expr_frag a = true ->
  ceval le a = None ->
  forall v, ~ eval_expr ge empty_env le m a v.
Proof.
  intros le a HF Hnone v H.
  rewrite (ceval_complete le a v HF H) in Hnone. discriminate.
Qed.

(** ** Guards

    A Clight conditional evaluates its expression and then coerces the value
    to a boolean with [bool_val], which is itself partial: [bool_val Vundef]
    is [None], and so is the boolean use of a value of a type with no truth
    value.  [cbool] chains the two partialities, which is exactly the
    [Lang.beval] a guard needs. *)

Definition cbool (le: temp_env) (a: expr) : option bool :=
  match ceval le a with
  | Some v => bool_val v (typeof a) m
  | None => None
  end.

(** Negation, as [Lang.bnot] requires it.  [tint] is the type C gives the
    result of [!], and [Onotbool] is CompCert's rendering of it. *)

Definition cnot (a: expr) : expr := Eunop Onotbool a tint.

Lemma expr_frag_cnot:
  forall a, expr_frag a = true -> expr_frag (cnot a) = true.
Proof. intros a H. exact H. Qed.

(** [bool_val] undoes [Val.of_bool] at type [int] — the step that makes the
    round trip through [sem_notbool] give back a plain negated boolean. *)
Lemma bool_val_of_bool:
  forall b, bool_val (Val.of_bool b) tint m = Some b.
Proof. intros [|]; reflexivity. Qed.

Theorem cbool_cnot:
  forall le a, cbool le (cnot a) = option_map negb (cbool le a).
Proof.
  intros le a. unfold cbool, cnot. simpl.
  destruct (ceval le a) as [v|] eqn:E; [| reflexivity].
  unfold sem_unary_operation, sem_notbool.
  destruct (bool_val v (typeof a) m) as [b|] eqn:B; simpl; [| reflexivity].
  apply bool_val_of_bool.
Qed.

End EVAL.
