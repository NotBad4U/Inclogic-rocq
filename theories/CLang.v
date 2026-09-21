(** * Clight as an instance of the language signature

    This is the file the whole Clight effort exists to produce: a term of
    type [Lang.t] whose values are CompCert's [val], whose stores are
    CompCert's [temp_env], and whose expressions are CompCert's
    [Clight.expr].  Feeding it to [Core.v] yields [com], [cexec], and — once
    [Hoare.v]/[Inc.v]/[Sil.v] have been generalised the same way — Hoare
    logic, Incorrectness Logic and SIL over C, with no separate metatheory.

    Nothing here is bespoke.  Each field is discharged by a CompCert lemma:

    | signature field    | discharged by                                  |
    |--------------------|------------------------------------------------|
    | [ident_dec]        | [Coqlib.peq]                                   |
    | [get_update_same]  | [PTree.gss]                                    |
    | [get_update_other] | [PTree.gso]                                    |
    | [store_ext]        | [PTree.extensionality]                         |
    | [beval_bnot]       | [CEval.cbool_cnot], i.e. [Cop.sem_notbool]     |
    | [eval_agree]       | [ceval_agree] below                            |

    ** The two parameters

    [ge] and [m] are parameters of the instance rather than components of the
    state, and that is precisely the content of the fragment restriction: by
    [CFrag.function_entry2_alloc_free] a function with [fn_vars = nil]
    allocates nothing, and by [CFrag.stmt_frag] its body never reads or
    writes memory.  So the memory is fixed for the whole execution and can be
    hoisted out.  Both still have to be *present*, because CompCert threads
    them through [sem_binary_operation], [sem_cast] and [bool_val] — they are
    consulted for pointer comparisons and composite sizes, neither of which
    the fragment can produce, but the signatures demand them anyway.

    ** Guards are expressions

    Clight has no separate syntax of boolean expressions: [Sifthenelse]
    takes an [expr] and coerces its value with [bool_val].  So [Lang.bexp] is
    instantiated to [expr] as well, and [Lang.beval] to [CEval.cbool], which
    is [ceval] followed by [bool_val].  Both partialities — the expression
    having no value, and the value having no truth value — collapse into the
    single [None] that [Core.cexec] reads as [RError]. *)

From Stdlib Require Import List Bool.
From compcert Require Import lib.Coqlib lib.Maps lib.Integers common.AST
     common.Values common.Memory cfrontend.Ctypes cfrontend.Cop cfrontend.Clight
     export.Ctypesdefs.
From IncLogic Require Import Lang Core CFrag CEval.

Set Warnings "-notation-for-abbreviation".

Import ListNotations.

Section INSTANCE.

Variable ge : genv.
Variable m : mem.

(** ** The instance *)

Definition ClightLang : lang :=
  Lang.Make
    (* ident  *) ident
    (* value  *) val
    (* store  *) temp_env
    (* get    *) (fun le x => le ! x)
    (* update *) (fun x v le => PTree.set x v le)
    (* expr   *) expr
    (* bexp   *) expr
    (* eval   *) (fun a le => ceval ge m le a)
    (* beval  *) (fun b le => cbool ge m le b)
    (* bnot   *) cnot.

(** ** The store laws *)

Lemma clight_get_update_same:
  forall (x : ident) (v : val) (le : temp_env),
  (PTree.set x v le) ! x = Some v.
Proof. intros. apply PTree.gss. Qed.

Lemma clight_get_update_other:
  forall (x y : ident) (v : val) (le : temp_env),
  y <> x -> (PTree.set x v le) ! y = le ! y.
Proof. intros x y v le H. apply PTree.gso. exact H. Qed.

Lemma clight_store_ext:
  forall le1 le2 : temp_env,
  (forall x : ident, le1 ! x = le2 ! x) -> le1 = le2.
Proof. intros. apply PTree.extensionality. exact H. Qed.

(** [Lang.beval] takes the expression first and the store second, the
    opposite of [CEval.cbool]; this just flips them. *)
Lemma clight_beval_bnot:
  forall (b : expr) (le : temp_env),
  cbool ge m le (cnot b) = option_map negb (cbool ge m le b).
Proof. intros. apply cbool_cnot. Qed.

Definition ClightLaws : Lang.laws ClightLang :=
  Lang.Laws ClightLang
    peq
    clight_get_update_same
    clight_get_update_other
    clight_store_ext
    clight_beval_bnot.

(** ** The frame property

    [cfv a x] over-approximates "evaluating [a] may read temporary [x]".
    For the fragment it is exact: the only expression form that reads the
    store at all is [Etempvar]. *)

Fixpoint cfv (a: expr) (x: ident) : Prop :=
  match a with
  | Etempvar id _ => id = x
  | Eunop _ a1 _ => cfv a1 x
  | Ebinop _ a1 a2 _ => cfv a1 x \/ cfv a2 x
  | Ecast a1 _ => cfv a1 x
  | _ => False
  end.

(** No fragment hypothesis is needed: on the out-of-fragment forms [ceval]
    is [None] in *both* stores, so the two sides agree vacuously. *)
Lemma ceval_agree:
  forall a le1 le2,
  (forall x, cfv a x -> le1 ! x = le2 ! x) ->
  ceval ge m le1 a = ceval ge m le2 a.
Proof.
  induction a; simpl; intros le1 le2 H; try reflexivity.
  - (* Etempvar *) apply H. reflexivity.
  - (* Eunop *) rewrite (IHa le1 le2 H). reflexivity.
  - (* Ebinop *)
    rewrite (IHa1 le1 le2), (IHa2 le1 le2); [ reflexivity | | ].
    + intros x Hx. apply H. right. exact Hx.
    + intros x Hx. apply H. left. exact Hx.
  - (* Ecast *) rewrite (IHa le1 le2 H). reflexivity.
Qed.

Lemma cbool_agree:
  forall b le1 le2,
  (forall x, cfv b x -> le1 ! x = le2 ! x) ->
  cbool ge m le1 b = cbool ge m le2 b.
Proof.
  intros b le1 le2 H. unfold cbool. rewrite (ceval_agree b le1 le2 H). reflexivity.
Qed.

Definition ClightFrame : Lang.frame ClightLang :=
  Lang.Frame ClightLang cfv cfv ceval_agree cbool_agree.

End INSTANCE.

(** ** Sanity: the core really is available over Clight

    [com (ClightLang ge m)] is the command type, [cexec] its semantics, and
    the derived forms of [Core.v] elaborate — [WHILE] through
    [Lang.bnot = cnot], i.e. through C's own [!]. *)

Section CHECK.

Variable ge : genv.
Variable m : mem.

Local Open Scope com_scope.

Let L := ClightLang ge m.

(** [Lang.expr] and [Lang.bexp] are projections, so unifying [Lang.expr ?L]
    with [Clight.expr] is not something elaboration can solve on its own: the
    instance has to be named.  These two abbreviations do that, and are what
    a surface syntax for writing fragment programs would provide. *)
Local Notation I := (Lang.ident L).
Local Notation E := (Lang.expr L).
Local Notation B := (Lang.bexp L).

(** [x = x / y] guarded by [y != 0] — the shape a fragment [if] elaborates
    to, with the division that [Core.cexec] will send to [RError] whenever
    [ceval] finds it undefined. *)
Definition divide_guarded (x y : I) : com L :=
  IF ((Ebinop One (Etempvar y tint) (Econst_int Int.zero tint) tint) : B) THEN
    ASSIGN x ((Ebinop Odiv (Etempvar x tint) (Etempvar y tint) tint) : E)
  END.

Definition count_down (i : I) : com L :=
  WHILE ((Ebinop Ogt (Etempvar i tint) (Econst_int Int.zero tint) tint) : B) DO
    ASSIGN i ((Ebinop Osub (Etempvar i tint) (Econst_int Int.one tint) tint) : E)
  END.

End CHECK.
