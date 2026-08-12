(** * Towards Automatisation thanks to SP calculus

  We will use the Strongest Post Condition calculus define in [Inc.SP] to
  encode examples of Section 6 in O'Hearn's "Incorrectness Logic" and prove them.

  These encode the four programs of _Figure 5_ (loop0, client0, loop1, loop2) and state their incorrectness.

  ** What changes with respect to [ExampleInc.v]

  [ExampleInc.v] proves the very same statements _semantically_: each proof
  opens the [IncTriple], picks an initial store by hand, and then builds a
  derivation of [cexec] step by step — [cexec_seq], [cexec_cstar_step_ok],
  [cexec_assume], … — with an auxiliary [star]-induction ([loop2_iter_Z]) for
  the loops.  The reasoning is about _executions_.

  Here nothing is built by hand. Each program is written once in the annotated
  language [SP.acom], its loops carrying an invariant, and the whole proof is

<<
      apply (SP.vcgen_valid _ prog_a); [ reflexivity | split ]
>>

  which leaves exactly two goals, both first-order arithmetic over stores:

  - [vcond]: the loop annotations are legal.  Computation reduces this to
    [True] everywhere except at a [CSTAR], where [SP.vcond_cstar_variant]
    turns it into a _forwards variant_ — an assertion family [R n] describing
    the states reachable after [n] turns.
  - [Q --* SP.sp P prog_a]: the wanted post is inside the computed one.
    [SP.slp_ok] / [SP.slp_err] _compute_, so this goal is obtained by [cbn]
    and closed by [lia] plus a handful of store facts.

  No [cexec] constructor is named anywhere below.  That is the point: the
  operational content has been discharged once and for all in [SP.vcgen_sound],
  and what is left is mechanical.

  Proof lines per theorem, the two files stating exactly the same triples:

  ** Summary:
<<
    theorem                     ExampleInc.v   ExampleIncSP.v
    ─────────────────────────────────────────────────────────
    loop1_achieves2                       33                4
    loop1_achieves1                        6                4
    loop2_correct                         28                5
    loop0_correct                         74                5
    client0_correct                       21                6
    ─────────────────────────────────────────────────────────
    total, helper lemmas included         212               81
>>
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

(** ** Automation toolbox *)

Create HintDb sp.

(** A variable is in the domain of a store it has just been written to. *)
Lemma in_domf_update_same: forall (x: ident) (v: Z) (s: store),
  x \in domf (update x v s).
Proof. intros x v s. rewrite dom_update, eqxx. reflexivity. Qed.

(** …and stays in the domain when some (possibly other) variable is written. *)
Lemma in_domf_update: forall (x y: ident) (v: Z) (s: store),
  x \in domf s -> x \in domf (update y v s).
Proof. intros x y v s H. rewrite dom_update, H, orbT. reflexivity. Qed.

(** With finmap stores, reading an unmapped variable yields the [sget] default
    [0]; so a variable observed to hold a nonzero value is necessarily mapped.
    This is what recovers the [x \in domf s] conjuncts that the paper's total
    stores make invisible. *)
Lemma in_domf_of_neq_0: forall (x: ident) (s: store), s x <> 0 -> x \in domf s.
Proof.
  intros x s Hne.
  pose proof (fndSome s x) as HS. unfold sget in Hne.
  destruct (s .[? x]%fmap) as [v | ] eqn:Hf.
  - cbn in HS. symmetry; exact HS.
  - cbn in Hne. exfalso. apply Hne. reflexivity.
Qed.

#[local] Hint Resolve in_domf_update_same in_domf_update : sp.

(** Read the store operations away: every [update] applied to a variable
    reduces, since the two are always concrete strings here. *)
Ltac store_simpl :=
  repeat first
    [ rewrite update_same in *
    | rewrite update_shadow in *
    | rewrite update_other in * by discriminate ].

(** Reduce a goal mentioning the SP transformers to first-order arithmetic over
    stores: compute [slp_ok] / [slp_err] / [vcond], then expand the assertion
    combinators and evaluate the expressions they contain. *)
Ltac sp_compute :=
  try unfold SP.vcgen, SP.sp in *;
  try autounfold with sp in *;
  cbn [SP.slp_ok SP.slp_err SP.vcond SP.iter_slp_ok SP.erase] in *;
  try unfold aimp, paimp, aand, aor, aexists, aforall, aupdate, aequal,
             atrue, afalse, in_domf, ffalse in *;
  cbn [aeval beval GREATER GREATEREQUAL LESS NOTEQUAL OR ODD] in *;
  store_simpl.

(** The [ok]-post of [ASSIGN x e] is
    [x ∈ dom ∧ ∃ m n. x = n ∧ p[m/x] ∧ e[m/x] = n].
    The second witness is always the final value of [x], so only [m] — the
    value [x] held _before_ the assignment — carries information. *)
Ltac sp_assign m :=
  split; [ | exists m; eexists; split; [ reflexivity | split ] ]; store_simpl.

(** Close a computed post.  Such a post is a nest of disjunctions — one branch
    per execution path — most of them the [ffalse] of a command that cannot
    take that exit; its leaves are store-domain facts, [Z] arithmetic and the
    boolean guards left over by [beval].  [sp_solve] searches the nest and
    closes the surviving leaf. *)
Ltac sp_bool :=
  first [ apply Z.eqb_eq | apply Z.eqb_neq | apply Z.leb_le
        | apply Z.leb_gt | apply Z.ltb_lt | apply Z.ltb_ge ].

Ltac sp_solve :=
  rewrite ?Bool.negb_involutive;
  solve [ assumption
        | reflexivity
        | exact I
        | lia
        | auto with sp
        | apply in_domf_of_neq_0; lia
        | sp_bool; lia
        | apply Bool.negb_true_iff; sp_bool; lia
        | apply Bool.negb_false_iff; sp_bool; lia
        | split; sp_solve
        | left; sp_solve
        | right; sp_solve
        (* the pre-value of a [NONDET] is unconstrained when the post does not
           mention it; [0] is as good a witness as any, and a wrong guess just
           backtracks *)
        | exists 0; sp_solve ].

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
  ASSIGN "x" (PLUS (VAR "x") (CONST 1)).

Definition loop1 : com :=
  ASSIGN "x" (CONST 0) ;; (loop1_body ★).

(** The loop annotation: whatever the number of turns, [x] is a nonnegative
    integer.  This is the assertion the paper's backwards variant produces. *)
Definition loop1_inv : assertion :=
  fun s => 0 <= s "x" /\ "x" \in domf s.

(** The same program in the annotated language: identical up to the [⟨ _ ⟩]
    carried by the loop.  [SP.erase] gives [loop1] back — checked below by
    [reflexivity]. *)
Definition loop1_a : SP.acom :=
  (SP.ASSIGN "x" (CONST 0) ;;
   ((SP.ASSIGN "x" (PLUS (VAR "x") (CONST 1))) ★ ⟨ loop1_inv ⟩))%acom.

(** The forwards variant: after [n] turns, [x] holds exactly [n]. *)
Definition loop1_var (n: nat) : assertion :=
  fun s => s "x" = Z.of_nat n /\ "x" \in domf s.

#[local] Hint Unfold loop1_a loop1_inv loop1_var : sp.

(** The loop annotation is legal.  Two obligations, both arithmetic: the
    variant steps ([x = n] becomes [x = n+1]), and it covers the annotation
    (a nonnegative [x] is [Z.to_nat (s "x")] turns in). *)
Lemma loop1_vcond: SP.vcond (fun _ => True) loop1_a.
Proof.
  apply SP.vcond_seq; [ exact I | ].
  apply SP.vcond_cstar_variant with (R := loop1_var).
  - (* entry: [x = 0] is the state right after [x := 0] *)
    intros s [Hx Hdom]. sp_compute. sp_assign 0; sp_solve.
  - (* step: one pass through [x := x+1] *)
    intros n s [Hx Hdom]. sp_compute. sp_assign (Z.of_nat n); sp_solve.
  - (* cover: every nonnegative [x] is reached by some number of turns *)
    intros s [Hnn Hdom]. exists (Z.to_nat (s "x")). sp_compute.
    rewrite Z2Nat.id by exact Hnn. sp_solve.
  - intros m. exact I.
  - exact I.
Qed.

(** Backwards-variant with [P n s := s "x" = Z.of_nat n /\ "x" \in domf s]. *)
Lemma loop1_achieves2 :
  ⟦⟦ fun _ => True ⟧⟧
  loop1
  ⟦⟦ ok ↑ (fun s : store => 0 <= s "x" /\ "x" \in domf s) ⟧⟧.
Proof.
  apply (SP.vcgen_valid _ loop1_a); [ reflexivity | ].
  split; [ exact loop1_vcond | ].
  (* the wanted post *is* the annotation, so the inclusion is an identity *)
  intros r; destruct r as [s | s]; sp_compute; tauto.
Qed.

(** [achieves1] is a [consequence]-strengthening of [achieves2]: in IL the
    post can be strengthened (smaller set of states to cover) for free, and
    [{0,1,2,3}] is a subset of the nonneg integers.  The paper proves it via
    three unrollings to showcase the unrolling rule; here it is the *same*
    verification condition — only the final inclusion changes, and [lia]
    closes it. *)
Lemma loop1_achieves1 :
  ⟦⟦ fun _ => True ⟧⟧
  loop1
  ⟦⟦ ok ↑ (fun s : store => (s "x" = 0 \/ s "x" = 1 \/ s "x" = 2 \/ s "x" = 3)
                            /\ "x" \in domf s) ⟧⟧.
Proof.
  apply (SP.vcgen_valid _ loop1_a); [ reflexivity | ].
  split; [ exact loop1_vcond | ].
  intros r; destruct r as [s | s]; sp_compute; [ | tauto ].
  intros [Hcase Hdom]. sp_solve.
Qed.

(** ** loop2 — Fig 5, lines 32-38.

    The Kleene-star body errors when [x = 2,000,000].  The IL triple captures
    that the error is reachable: [er: x == 2,000,000].

    This is the case that [slp_err] handles through the annotation: the
    [err]-post of [C ★ ⟨ I ⟩] is the [err]-post of [C] run at [I], so the whole
    proof of reachability is carried by the invariant. *)

Definition loop2_body : com :=
  (IF (EQUAL (VAR "x") (CONST 2000000)) THEN ERROR END) ;;
  ASSIGN "x" (PLUS (VAR "x") (CONST 1)).

Definition loop2 : com :=
  ASSIGN "x" (CONST 0) ;; (loop2_body ★).

(** The annotation: the loop counts up from [0] and stops at [2,000,000]. *)
Definition loop2_inv : assertion :=
  fun s => 0 <= s "x" <= 2000000 /\ "x" \in domf s.

Definition loop2_a : SP.acom :=
  (SP.ASSIGN "x" (CONST 0) ;;
   ((((IF (EQUAL (VAR "x") (CONST 2000000)) THEN SP.ERROR END) ;;
       SP.ASSIGN "x" (PLUS (VAR "x") (CONST 1)))) ★ ⟨ loop2_inv ⟩))%acom.

(** The forwards variant.  Indexed over [nat] as [SP.vcond_cstar_variant]
    requires, but every arithmetic fact is stated over [Z] — the huge literal
    [2000000%nat] is what breaks [lia]. *)
Definition loop2_var (n: nat) : assertion :=
  fun s => s "x" = Z.of_nat n /\ s "x" <= 2000000 /\ "x" \in domf s.

#[local] Hint Unfold loop2_a loop2_inv loop2_var : sp.

Lemma loop2_vcond: SP.vcond (fun _ => True) loop2_a.
Proof.
  apply SP.vcond_seq; [ exact I | ].
  apply SP.vcond_cstar_variant with (R := loop2_var).
  - (* entry *)
    intros s [Hx [_ Hdom]]. sp_compute. sp_assign 0; sp_solve.
  - (* step: the guard [x <> 2,000,000] holds because [x] has not reached it *)
    intros n s [Hx [Hle Hdom]]. sp_compute. sp_assign (Z.of_nat n); sp_solve.
  - (* cover *)
    intros s [[Hnn Hle] Hdom]. exists (Z.to_nat (s "x")). sp_compute.
    rewrite Z2Nat.id by exact Hnn. sp_solve.
  - intros m. sp_compute. tauto.
  - sp_compute. tauto.
Qed.

Lemma loop2_correct :
  ⟦⟦ fun _ => True ⟧⟧
  loop2
  ⟦⟦ err ↑ aequal (VAR "x") 2000000 ⟧⟧.
Proof.
  apply (SP.vcgen_valid _ loop2_a); [ reflexivity | ].
  split; [ exact loop2_vcond | ].
  intros r; destruct r as [s | s]; sp_compute; [ tauto | ].
  (* the erroring branch of the body, taken at an invariant state *)
  intros Hx. rewrite Hx. sp_solve.
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
  ASSIGN "x" (PLUS (VAR "x") (VAR "n")) ;;
  NONDET "n".

Definition loop0 : com :=
  NONDET "n" ;;
  ASSIGN "x" (CONST 0) ;;
  WHILE (GREATER (VAR "n") (CONST 0)) DO loop0_body END.

Definition loop0_inv : assertion :=
  fun s => 0 <= s "x" /\ "x" \in domf s /\ "n" \in domf s.

Definition loop0_a : SP.acom :=
  (SP.NONDET "n" ;;
   SP.ASSIGN "x" (CONST 0) ;;
   WHILE ⟨ loop0_inv ⟩ (GREATER (VAR "n") (CONST 0)) DO
     (SP.ASSIGN "x" (PLUS (VAR "x") (VAR "n")) ;; SP.NONDET "n")
   END)%acom.

(** The forwards variant is finite here: [x] is [0] before the loop and, after
    one turn, an arbitrary positive value (the nondeterministic [n] that was
    added to it).  Further turns add nothing, so [R] collapses at [2]. *)
Definition loop0_var (n: nat) : assertion :=
  fun s =>
    match n with
    | 0%nat => s "x" = 0 /\ "x" \in domf s /\ "n" \in domf s
    | 1%nat => 0 < s "x" /\ "x" \in domf s /\ "n" \in domf s
    | _ => False
    end.

#[local] Hint Unfold loop0_a loop0_inv loop0_var : sp.

Lemma loop0_vcond: SP.vcond (fun _ => True) loop0_a.
Proof.
  apply SP.vcond_seq; [ exact I | ].
  apply SP.vcond_seq; [ exact I | ].
  apply SP.vcond_seq; [ | exact I ].
  apply SP.vcond_cstar_variant with (R := loop0_var).
  - (* entry: [n := nondet(); x := 0] *)
    intros s [Hx [Hdx Hdn]]. sp_compute. sp_assign 0; sp_solve.
  - (* step.  Only the first turn is productive, so [R (S (S n))] is [False]. *)
    intros [ | n ] s Hs; [ | destruct Hs ].
    destruct Hs as [Hx [Hdx Hdn]]. sp_compute.
    (* the nondet at the end of the body wrote the value [n] the loop
       consumed, so it can be read back off [x]: [n = x] *)
    split; [ exact Hdn | ]. exists (s "x").
    sp_assign 0; sp_solve.
  - (* cover: either [x = 0] (no turn) or [x > 0] (one turn) *)
    intros s [Hnn [Hdx Hdn]].
    destruct (Z.eq_dec (s "x") 0) as [Hz | Hnz];
      [ exists 0%nat | exists 1%nat ]; sp_compute; sp_solve.
  - intros m. sp_compute. tauto.
  - sp_compute. tauto.
Qed.

Lemma loop0_correct :
  ⟦⟦ fun _ => True ⟧⟧
  loop0
  ⟦⟦ ok ↑ (fun s : store => 0 <= s "x" /\ s "n" <= 0
                            /\ "x" \in domf s /\ "n" \in domf s) ⟧⟧.
Proof.
  apply (SP.vcgen_valid _ loop0_a); [ reflexivity | ].
  split; [ exact loop0_vcond | ].
  intros r; destruct r as [s | s]; sp_compute; [ | tauto ].
  intros [Hnn [Hnp [Hdx Hdn]]]. sp_solve.
Qed.

(** ** client0 — Fig 5, lines 12-16.

    [loop0(); if (x == 2,000,000) {error();}]

    Inline [loop0] at the call site.  The IL triple says there exists an
    execution that ends in error with [x == 2,000,000]: [loop0] takes one
    iteration with [n_init == 2,000,000], then [n = nondet()] picks
    [n <= 0], the loop exits with [x == 2,000,000], and the conditional
    fires.

    Same caveat as [loop0_correct]: the post must constrain [n] (which is
    a globally visible identifier without the local-variable rule).

    Note that the verification condition is [loop0]'s, unchanged: the trailing
    conditional is loop-free, so it contributes nothing to [vcond] and only
    computes in the post. *)

Definition client0 : com :=
  loop0 ;;
  IF (EQUAL (VAR "x") (CONST 2000000)) THEN ERROR END.

Definition client0_a : SP.acom :=
  (loop0_a ;; IF (EQUAL (VAR "x") (CONST 2000000)) THEN SP.ERROR END)%acom.

#[local] Hint Unfold client0_a : sp.

Lemma client0_correct :
  ⟦⟦ fun _ => True ⟧⟧
  client0
  ⟦⟦ err ↑ (fun s : store =>
              s "x" = 2000000 /\ s "n" <= 0 /\ "n" \in domf s) ⟧⟧.
Proof.
  apply (SP.vcgen_valid _ client0_a); [ reflexivity | ].
  split.
  - apply SP.vcond_seq; [ exact loop0_vcond | sp_compute; tauto ].
  - (* the error comes from the trailing conditional, not from inside [loop0] *)
    intros r; destruct r as [s | s]; sp_compute; [ tauto | ].
    intros [Hx [Hnp Hdn]]. rewrite Hx. sp_solve.
Qed.
