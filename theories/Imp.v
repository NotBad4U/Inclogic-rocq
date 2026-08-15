From Stdlib Require Import Arith ZArith Psatz Bool String Ascii List Program.Equality.
From Stdlib Require Import RelationClasses Morphisms Setoid.
From IncLogic Require Import Sequences RelKleene.
From HB Require Import structures.
From mathcomp Require Import ssrfun ssrbool eqtype choice.
(** [finmap] declares its [fset] comprehensions in prefix-incompatible families;
    the warning concerns the library's own notations, not ours, so it is muted
    only across this import and re-enabled straight after. *)
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import finmap.
Set Warnings "notation-incompatible-prefix".

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** * 0.  [Choice]/[Countable] instances for [ascii] and [string]

    Required so that [{fmap string -> Z}] is a well-typed finite map. *)

(** Building the [eqType]/[choiceType]/[countType] stack with HB makes it
    re-register projections mathcomp's own [choice] instances already provide;
    HB reports each as redundant and ignores it, which is harmless here. *)
Set Warnings "-redundant-canonical-projection".

Definition ascii_eqb (a b : ascii) : bool :=
  if ascii_dec a b then true else false.
Lemma ascii_eqbP : Equality.axiom ascii_eqb.
Proof.
  intros a b. unfold ascii_eqb.
  destruct (ascii_dec a b) as [E|N].
  - apply ReflectT, E.
  - apply ReflectF, N.
Qed.
HB.instance Definition _ := hasDecEq.Build ascii ascii_eqbP.
Lemma ascii_pickleK : pcancel nat_of_ascii (fun n => Some (ascii_of_nat n)).
Proof. intro a. rewrite ascii_nat_embedding. reflexivity. Qed.
HB.instance Definition _ := PCanHasChoice ascii_pickleK.
HB.instance Definition _ := PCanIsCountable ascii_pickleK.

Definition string_eqb (s1 s2 : string) : bool :=
  match string_dec s1 s2 with left _ => true | right _ => false end.
Lemma string_eqbP : Equality.axiom string_eqb.
Proof.
  intros s1 s2. unfold string_eqb.
  destruct (string_dec s1 s2) as [E|N]; [left|right]; assumption.
Qed.
HB.instance Definition _ := hasDecEq.Build string string_eqbP.
Lemma string_pickleK :
  pcancel list_ascii_of_string (fun l => Some (string_of_list_ascii l)).
Proof. intro s. rewrite string_of_list_ascii_of_string. reflexivity. Qed.
HB.instance Definition _ := PCanHasChoice string_pickleK.
HB.instance Definition _ := PCanIsCountable string_pickleK.

Set Warnings "redundant-canonical-projection".

(** *  The IMP language *)

(** ** Arithmetic expressions *)

Definition ident := string.

(** The abstract syntax: an arithmetic expression is either... *)

Inductive aexp : Type :=
  | CONST (n: Z)                       (** a constant, or *)
  | VAR (x: string)                    (** a variable, or *)
  | PLUS (a1: aexp) (a2: aexp)         (** a sum of two expressions, or *)
  | MINUS (a1: aexp) (a2: aexp).       (** a difference of two expressions *)

Definition store : Type := {fmap ident -> Z}.
Definition sget (s: store) (x: ident) : Z := odflt 0%Z s.[? x]%fmap.
Coercion sget : store >-> Funclass.

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

(** ** Surface syntax for arithmetic expressions

    [aexp_scope] lets an expression be written the way it is in the program:
    a bare string is the variable, a bare integer the constant.  This is what
    gives assertions a full expression language (see [assn_scope] in
    [Hoare.v]) rather than just "variable compared to constant". *)

Declare Scope aexp_scope.
Delimit Scope aexp_scope with X.
Bind Scope aexp_scope with aexp.

(** [VAR] is declared over [string] rather than [ident] precisely so that it
    can be the coercion: registered over the alias it would not fire on a
    string literal.  Being a constructor and not a wrapper, it needs no
    unfolding — anything matching on [aexp], including the Elpi search in
    [IncElpi.v], sees the ordinary [VAR]. *)
Coercion VAR : string >-> aexp.
Coercion CONST : Z >-> aexp.

Notation "a + b" := (PLUS a b) : aexp_scope.
Notation "a - b" := (MINUS a b) : aexp_scope.

Fixpoint aeval (a: aexp) (s: store) : Z :=
  match a with
  | CONST n => n
  | VAR x => s x
  | PLUS a1 a2 => aeval a1 s + aeval a2 s
  | MINUS a1 a2 => aeval a1 s - aeval a2 s
  end.

(** Unmapped variables read as [0%Z] under [sget]. *)

(** We can prove mathematical properties of a given expression. *)

Lemma aeval_xplus1:
  forall s x, aeval (PLUS (VAR x) (CONST 1)) s > aeval (VAR x) s.
Proof.
  intros. cbn. lia.
Qed.

(** Finally, we can prove "meta-properties" that hold for all expressions.
  For example: the value of an expression depends only on the values of its
  free variables.

  Free variables are defined by this recursive predicate:
*)
Fixpoint free_in_aexp (x: ident) (a: aexp) : Prop :=
  match a with
  | CONST n => False
  | VAR y => y = x
  | PLUS a1 a2 | MINUS a1 a2 => free_in_aexp x a1 \/ free_in_aexp x a2
  end.

Theorem aeval_free:
  forall (s1 s2 : store) a,
  (forall x, free_in_aexp x a -> s1 x = s2 x) ->
  aeval a s1 = aeval a s2.
Proof.
  induction a; cbn; intros SAMEFREE.
- (* Case a = CONST n *)
  auto.
- (* Case a = VAR x *)
  apply SAMEFREE. auto.
- (* Case a = PLUS a1 a2 *)
  f_equal; [apply IHa1 | apply IHa2]; intros; apply SAMEFREE; auto.
- (* Case a = MINUS a1 a2 *)
  f_equal; [apply IHa1 | apply IHa2]; intros; apply SAMEFREE; auto.
Qed.

Definition OPP (a: aexp) : aexp := MINUS (CONST 0) a.

Lemma aeval_OPP: forall s a, aeval (OPP a) s = - (aeval a s).
Proof.
  intros; cbn. lia.
Qed.

(** The IMP language has conditional statements (if/then/else) and
  loops.  They are controlled by expressions that evaluate to Boolean
  values.  Here is the abstract syntax of Boolean expressions. *)

Inductive bexp : Type :=
  | TRUE                              (**r always true *)
  | FALSE                             (**r always false *)
  | EQUAL (a1: aexp) (a2: aexp)       (**r whether [a1 = a2] *)
  | LESSEQUAL (a1: aexp) (a2: aexp)   (**r whether [a1 <= a2] *)
  | EVEN (a1: aexp)                   (**r whether [a1] evaluates to an even integer *)
  | NOT (b1: bexp)                    (**r Boolean negation *)
  | AND (b1: bexp) (b2: bexp).        (**r Boolean conjunction *)

(** Just like arithmetic expressions evaluate to integers,
  Boolean expressions evaluate to Boolean values [true] or [false]. *)

(** ** Surface syntax for boolean expressions

    Same idea as [aexp_scope]: a guard reads like the test it is.  The
    comparison symbols are the ones [assn_scope] uses for assertions — the
    scopes are bound to their types, so [("x" ≐ 9)] is a [bexp] where a [bexp]
    is expected and an [assertion] where an assertion is. *)

Declare Scope bexp_scope.
(** [%Bx], not [%B]: the latter is the standard key for [bool_scope]. *)
Delimit Scope bexp_scope with Bx.
Bind Scope bexp_scope with bexp.

Notation "a ≐ b" := (EQUAL a b) (at level 70, no associativity) : bexp_scope.
Notation "a ≠ b" := (NOT (EQUAL a b)) (at level 70, no associativity) : bexp_scope.
Notation "a ⩽ b" := (LESSEQUAL a b) (at level 70, no associativity) : bexp_scope.
Notation "a ⩾ b" := (LESSEQUAL b a) (at level 70, no associativity) : bexp_scope.
Notation "a ≺ b" := (NOT (LESSEQUAL b a)) (at level 70, no associativity) : bexp_scope.
Notation "a ≻ b" := (NOT (LESSEQUAL a b)) (at level 70, no associativity) : bexp_scope.
Notation "¬ b" := (NOT b) (at level 75, right associativity) : bexp_scope.
Notation "b1 ⋀ b2" := (AND b1 b2) (at level 80, right associativity) : bexp_scope.

Fixpoint beval (b: bexp) (s: store) : bool :=
  match b with
  | TRUE => true
  | FALSE => false
  | EQUAL a1 a2 => aeval a1 s =? aeval a2 s
  | LESSEQUAL a1 a2 => aeval a1 s <=? aeval a2 s
  | EVEN a1 => Z.even (aeval a1 s)
  | NOT b1 => negb (beval b1 s)
  | AND b1 b2 => beval b1 s && beval b2 s
  end.

(** There are many useful derived forms. *)

Definition NOTEQUAL (a1 a2: aexp) : bexp := NOT (EQUAL a1 a2).

Definition GREATEREQUAL (a1 a2: aexp) : bexp := LESSEQUAL a2 a1.

Definition GREATER (a1 a2: aexp) : bexp := NOT (LESSEQUAL a1 a2).

Definition LESS (a1 a2: aexp) : bexp := GREATER a2 a1.

Definition OR (b1 b2: bexp) : bexp := NOT (AND (NOT b1) (NOT b2)).

(** Derived form: evenness test on arithmetic expressions. *)
Definition ODD (a: aexp) : bexp := NOT (EVEN a).

(** ** 1.2 Commands *)
Declare Custom Entry com.
Declare Scope com_scope.
Delimit Scope com_scope with com.
Local Open Scope com_scope.

Notation "x + y" := (PLUS x y) (in custom com at level 50, left associativity).
Notation "x - y" := (MINUS x y) (in custom com at level 50, left associativity).

(**  Commands *)

Inductive com: Type :=
  | SKIP                         (**r do nothing *)
  | ERROR                        (**r interrupt the program *)
  | ASSIGN (x: ident) (a: aexp)  (**r assignment: [v := a] *)
  | NONDET (x: ident)            (**r non-deterministic assignment to [x] *)
  | ASSUME (b: bexp)             (**r assume that [b] holds *)
  | SEQ (c1: com) (c2: com)      (**r sequence: [c1; c2] *)
  | CHOICE (c1: com) (c2: com)   (**r non-deterministic choice: [c1 + c2] *)
  | CSTAR (ann: option loopann) (c1: com).
      (**r non-deterministic iteration: [c1★], optionally annotated with a
          loop invariant.  [None] leaves the loop to whatever the client
          calculus computes for it; [Some I] pins it to [I]. *)

(** We can write [c1 ;; c2] instead of [SEQ c1 c2], it is easier on the eyes. *)

Infix ";;" := SEQ (at level 80, right associativity): com_scope.

Notation "c1 '⊕' c2" := (CHOICE c1 c2)
                         (at level 85, right associativity): com_scope.
Notation "c '★'" := (CSTAR None c)
                         (at level 90, right associativity) : com_scope.

Notation "c '★' '⟨' I '⟩'" := (CSTAR (Some (AInv I)) c)
                         (at level 90, right associativity) : com_scope.

Notation "c '★' '⟨|' R '|⟩'" := (CSTAR (Some (AVar R)) c)
                         (at level 90, right associativity) : com_scope.

(** We can now define the syntax of while-loops in terms of the core IMP commands. *)
Notation "'WHILE' b 'DO' c 'END'" :=
  (((ASSUME b ;; c) ★) ;; ASSUME (NOT b))
    (at level 95, right associativity) : com_scope.

Notation "'WHILE' '⟨' I '⟩' b 'DO' c 'END'" :=
  (((ASSUME b ;; c) ★ ⟨ I ⟩) ;; ASSUME (NOT b))
    (at level 95, right associativity) : com_scope.

Notation "'WHILE' '⟨|' R '|⟩' b 'DO' c 'END'" :=
  (((ASSUME b ;; c) ★ ⟨| R |⟩) ;; ASSUME (NOT b))
    (at level 95, right associativity) : com_scope.

(** Similarly, we can define conditional statements.

    Note: Coq does not handle an “optional ELSE” well when both notations
    start with exactly the same prefix [IF ... THEN ...].

    To keep the convenient no-ELSE syntax, we reserve [IF ... THEN ... END]
    for the no-ELSE form, and introduce a separate keyword [IFELSE] for the
    form with [ELSE]. *)
Notation "'IF' b 'THEN' c1 'ELSE' c2 'END'" :=
  (CHOICE
     (ASSUME b ;; c1)
     (ASSUME (NOT b) ;; c2))
    (at level 89, right associativity,
     b at level 99,
     c1 at level 89,
     c2 at level 89) : com_scope.

(* Same level and argument levels as the [ELSE] form above: the two share the
    prefix [IF _ THEN _], and Rocq requires a common prefix to be parsed at
    identical levels, else only one of the two notations works. *)
Notation "'IF' b 'THEN' c1 'END'" :=
  (IF b THEN c1 ELSE SKIP END)
  (at level 89, right associativity,
   b at level 99,
   c1 at level 89,
   only parsing) : com_scope.

Notation "'ASSERT' b" :=
  (CHOICE
     (ASSUME b)
     (ASSUME (NOT b) ;; ERROR))
    (at level 100, right associativity) : com_scope.

(** Here is an example arithmetic expression: *)

(** Here is an example IMP program that computes the Euclidean division
    of two natural numbers [a] and [b], storing the quotient in variable
    ["q"] and the remainder in variable ["r"].  We assume that [b > 0]. *)

Definition Euclidean_division: com :=
  ASSIGN "r" (VAR "a") ;;
  ASSIGN "q" (CONST 0) ;;
  WHILE (LESSEQUAL (VAR "b") (VAR "r")) DO
    (ASSIGN "r" (MINUS (VAR "r") (VAR "b")) ;;
     ASSIGN "q" (PLUS (VAR "q") (CONST 1)))
  END.

(** Example in section 3.1 *)
Definition Under_approximating_ex: com :=
  IF (EVEN (VAR "x")) THEN
    IF (ODD (VAR "y")) THEN
      ASSIGN "z" (CONST 42)
    ELSE
      SKIP
    END
  END.

(** ** 1.3 Small-step operational semantics *)

(** A useful operation over stores:
    [update x v s] is the store that maps [x] to [v] and is equal to [s] for
    all variables other than [x]. *)

Definition update (x: ident) (v: Z) (s: store) : store :=
  s.[x <- v]%fmap.

Lemma update_same: forall x v s, (update x v s) x = v.
Proof.
  intros x v s. unfold update, sget. rewrite fnd_set, eqxx. reflexivity.
Qed.

Lemma update_other: forall x v s y, x <> y -> (update x v s) y = s y.
Proof.
  intros x v s y Hxy. unfold update, sget. rewrite fnd_set.
  rewrite (@ssrbool.ifF _ ((y == x)%bool) _ _).
  - reflexivity.
  - apply (@ssrbool.introF _ ((y == x)%bool) (@eqP _ _ _)).
    intros Heq. apply Hxy. apply Logic.eq_sym. exact Heq.
Qed.

Lemma update_shadow: forall x m n s, update x n (update x m s) = update x n s.
Proof.
  intros x m n s. unfold update. rewrite finmap.setfC. rewrite eqxx. reflexivity.
Qed.

Lemma update_get: forall x (s: store), x \in domf s -> update x (s x) s = s.
Proof.
  intros x s Hin. unfold update.
  apply fmapP. intro k. rewrite fnd_set.
  destruct ((k == x)%bool) eqn:E.
  - assert (Hk : k = x).
    { generalize (@eqP _ k x). rewrite E. intro H. inversion H. assumption. }
    rewrite Hk.
    destruct (s.[? x]%fmap) eqn:Hsx.
    + f_equal. unfold sget. rewrite Hsx. cbn. reflexivity.
    + exfalso.
      assert (Hnot : (x \in domf s) = false).
      { generalize (fndSome s x). rewrite Hsx. cbn. intro Heq. symmetry. exact Heq. }
      rewrite Hnot in Hin. discriminate.
  - reflexivity.
Qed.

(** The result type indicates the end value of a program: either a final
    state on the normal path, or the state at the point of error. *)
Inductive result : Type :=
| RNormal : store -> result
| RError  : store -> result.

(** The relation [ red (c, s) (c', s') ] defines a basic reduction,
    that is, the first computation step when executing command [c]
    in initial memory state [s].
    [s'] is the memory state "after" this computation step.
    [c'] is a command that represent all the computations that remain
    to be performed later.

    The reduction relation is presented as a Coq inductive predicate,
    with one case (one "constructor") for each reduction rule.
*)

Inductive red: com * store -> com * store -> Prop :=
  | red_assign: forall x a s,
      red (ASSIGN x a, s) (SKIP, update x (aeval a s) s)
  | red_nondet: forall x s n,
    red (NONDET x, s) (SKIP, update x n s)
  | red_assume: forall b s,
    beval b s = true ->
    red (ASSUME b, s) (SKIP, s)
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

(** Final configurations for the small-step semantics, corresponding to [result]. *)
Inductive final : com * store -> result -> Prop :=
  | final_skip : forall s,
    final (SKIP, s) (RNormal s)
  | final_error : forall s,
    final (ERROR, s) (RError s).

  (** Termination for the small-step semantics that returns a [result]. *)
  Definition terminates_result (s: store) (c: com) (r: result) : Prop :=
    exists cs, star red (c, s) cs /\ final cs r.

(** This IMP language is not deterministic due to the nondeterministic choice (+) operator *)
Lemma red_nondeterm :
  exists cs cs1 cs2,
    red cs cs1 /\ red cs cs2 /\ cs1 <> cs2.
Proof.
  exists (CHOICE SKIP (ASSIGN "x" (CONST 1)), [fmap]%fmap : store).
  exists (SKIP, [fmap]%fmap : store).
  exists (ASSIGN "x" (CONST 1), [fmap]%fmap : store).
  split.
  - apply red_choice_left.
  - split.
    + apply red_choice_right.
    + intro. discriminate H.
Qed.

(** We define the semantics of a command by chaining successive reductions.
    The command [c] in initial state [s] terminates with final state [s']
    if we can go from [(c, s)] to [(skip, s')] in a finite number of reductions.
*)

Definition terminates (s: store) (c: com) (s': store) : Prop :=
  star red (c, s) (SKIP, s').

(** The [star] operator is defined in library [Sequences].
    [star R] is the reflexive transitive closure of relation [R].
    On paper it is often written [R*].
    The [star red] relation therefore represents zero, one or several
    reduction steps. *)

(** Likewise, command [c] diverges (fails to terminate) in initial state [s]
    if there exists an infinite sequence of reductions starting with [(c, s)].
    The [infseq] relation operator is defined in library [Sequences].
*)

Definition diverges (s: store) (c: com) : Prop :=
  infseq red (c, s).

(** With guarded [ASSUME], a program can also legitimately *block* (no rule
    fires) when [ASSUME b] is reached in a state where [beval b s = false].
    The previous [red_progress] / [not_goes_wrong] lemmas relied on the fact
    that any non-final configuration could step, which no longer holds here.
    They have been removed. *)

(* * A technical lemma: a sequence of reductions can take place to the left
    of a [SEQ] constructor.  This generalizes rule [red_seq_step]. *)
Lemma red_seq_steps:
  forall c2 s c s' c',
  star red (c, s) (c', s') -> star red ((c ;; c2), s) ((c' ;; c2), s').
Proof.
  intros. dependent induction H.
- apply star_refl.
- destruct b as [c1 st1].
  apply star_step with (c1;;c2, st1). apply red_seq_step. auto. auto.  
Qed.

(** Natural semantics *)

Reserved Notation "st0 =[ c ]=> st1"
  (at level 40, c at level 99, st1 at level 39).

Inductive cexec: store -> com -> result -> Prop :=
  | cexec_skip: forall s,
      s =[ SKIP ]=> RNormal s
  | cexec_error: forall s,
      s =[ ERROR ]=> RError s
  | cexec_assign: forall s x a,
    s =[ ASSIGN x a ]=> RNormal (update x (aeval a s) s)
  | cexec_nondet: forall s x n,
    s =[ NONDET x ]=> RNormal (update x n s)
  | cexec_assume: forall s b,
    beval b s = true ->
    s =[ ASSUME b ]=> RNormal s
  | cexec_seq: forall c1 c2 s s' s'',
    s  =[ c1 ]=> RNormal s' ->
    s' =[ c2 ]=> RNormal s'' ->
    s  =[ SEQ c1 c2 ]=> RNormal s''
  | cexec_seq_error: forall c1 c2 s sf,
    s  =[ c1 ]=> RError sf ->
    s  =[ SEQ c1 c2 ]=> RError sf
  | cexec_seq_error_right: forall c1 c2 s s' sf,
    s  =[ c1 ]=> RNormal s' ->
    s' =[ c2 ]=> RError sf ->
    s  =[ SEQ c1 c2 ]=> RError sf
  | cexec_choice_left: forall s c1 c2 r,
    s =[ c1 ]=> r ->
    s =[ CHOICE c1 c2 ]=> r
  | cexec_choice_right: forall s c1 c2 r,
    s =[ c2 ]=> r ->
    s =[ CHOICE c1 c2 ]=> r
  | cexec_cstar_done: forall a c s,
      s =[ CSTAR a c ]=> RNormal s
  | cexec_cstar_step_ok : forall a c s s' s'',
      s  =[ c ]=> RNormal s' ->
      s' =[ CSTAR a c ]=> RNormal s'' ->
      s  =[ CSTAR a c ]=> RNormal s''
  | cexec_cstar_step_error : forall a c s sf,
      s =[ c ]=> RError sf ->
      s =[ CSTAR a c ]=> RError sf
  | cexec_cstar_step_iter_error : forall a c s s' sf,
      s  =[ c ]=> RNormal s' ->
      s' =[ CSTAR a c ]=> RError sf ->
      s  =[ CSTAR a c ]=> RError sf
  where "st0 =[ c ]=> st1" := (cexec st0 c st1).

Notation "s1 =[ c ]=> 'ok' ↑ s2" := (cexec s1 c (RNormal s2))
  (at level 40, c at level 99, s2 at level 39).

Notation "s1 =[ c ]=> 'err' ↑ s2" := (cexec s1 c (RError s2))
  (at level 40, c at level 99, s2 at level 39).

(** ** Annotations are semantically irrelevant

    No rule of [red] or [cexec] inspects an annotation, so an execution of [c]
    is an execution of [unannot c].  This is what lets a specification be
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

Lemma cexec_unannot: forall s c r, cexec s c r -> cexec s (unannot c) r.
Proof.
  intros s c r H. induction H; cbn [unannot];
    eauto using cexec_skip, cexec_error, cexec_assign, cexec_nondet,
                cexec_assume, cexec_seq, cexec_seq_error, cexec_seq_error_right,
                cexec_choice_left, cexec_choice_right, cexec_cstar_done,
                cexec_cstar_step_ok, cexec_cstar_step_error,
                cexec_cstar_step_iter_error.
Qed.

(** ** Kleene-algebra view of [CSTAR]

    [step_iter c] is the relation "one successful execution of [c]" on stores.
    The reflexive-transitive closure [star (step_iter c)] then captures
    "zero or more successful iterations of [c]" — the Kleene star, which
    lets us reason about [CSTAR c] using the lemmas in [Sequences.v]
    ([star_refl], [star_one], [star_trans], ...). *)

Definition step_iter (c: com) (s s': store) : Prop :=
  s =[ c ]=> RNormal s'.

Lemma cexec_cstar_of_star:
  forall a c s s', star (step_iter c) s s' -> s =[ CSTAR a c ]=> RNormal s'.
Proof.
  induction 1.
  - apply cexec_cstar_done.
  - eapply cexec_cstar_step_ok; eauto.
Qed.

Lemma star_of_cexec_cstar:
  forall a c s r,
    s =[ CSTAR a c ]=> r ->
    forall s', r = RNormal s' -> star (step_iter c) s s'.
Proof.
  intros a c s r H. dependent induction H; intros s0 EQ; try discriminate.
  - inversion EQ; subst. apply star_refl.
  - inversion EQ; subst. eapply star_step; [ exact H | eauto ].
Qed.

Theorem cexec_cstar_iff_star:
  forall a c s s',
    s =[ CSTAR a c ]=> RNormal s' <-> star (step_iter c) s s'.
Proof.
  intros a c s s'. split.
  - intro H. eapply star_of_cexec_cstar; eauto.
  - apply cexec_cstar_of_star.
Qed.

(** Erroring execution of [CSTAR c]: some number of successful iterations
    followed by a body that errors. *)
Lemma cexec_cstar_err_to_star:
  forall a c s r,
    s =[ CSTAR a c ]=> r ->
    forall sf', r = RError sf' ->
    exists s', star (step_iter c) s s' /\ s' =[ c ]=> RError sf'.
Proof.
  intros a c s r H. dependent induction H; intros sf' EQ; try discriminate.
  - injection EQ as ->. exists s. split; [ apply star_refl | exact H ].
  - destruct (IHcexec2 a c Logic.eq_refl sf' EQ) as (sm & STAR & ERR).
    exists sm. split; [ eapply star_step; eauto | exact ERR ].
Qed.

Theorem cexec_cstar_err_iff:
  forall a c s sf,
    s =[ CSTAR a c ]=> RError sf <->
    exists s', star (step_iter c) s s' /\ s' =[ c ]=> RError sf.
Proof.
  intros a c s sf. split.
  - intro H. eapply cexec_cstar_err_to_star; eauto.
  - intros (s' & STAR & ERR). induction STAR.
    + apply cexec_cstar_step_error. exact ERR.
    + eapply cexec_cstar_step_iter_error; eauto.
Qed.

(** ** [step_iter] as a Kleene-algebra homomorphism

    The relation [step_iter] sends program constructors to their
    corresponding Kleene-algebra operators. These equivalences let us
    [rewrite] program structure into relational form and apply the laws
    in [RelKleene.v]. *)

Lemma step_iter_skip:
  step_iter SKIP ≡ rid.
Proof.
  intros s s'. unfold step_iter, rid; split.
  - intro H. inversion H; subst. reflexivity.
  - intros ->. apply cexec_skip.
Qed.

(** [ASSUME b] is the KAT-test [\[b\]] — the partial-identity relation that
    holds only on states where [b] is true. *)
Lemma step_iter_assume:
  forall b s s',
    step_iter (ASSUME b) s s' <-> s = s' /\ beval b s = true.
Proof.
  intros b s s'. unfold step_iter; split.
  - intro H. inversion H; subst. split; [ reflexivity | assumption ].
  - intros (-> & HB). apply cexec_assume. exact HB.
Qed.

Lemma step_iter_seq:
  forall c1 c2, step_iter (SEQ c1 c2) ≡ step_iter c1 ⨟ step_iter c2.
Proof.
  intros c1 c2 s s''. unfold step_iter, rcomp; split.
  - intro H. inversion H; subst. exists s'. split; assumption.
  - intros (s' & H1 & H2). eapply cexec_seq; eauto.
Qed.

Lemma step_iter_choice:
  forall c1 c2 s s',
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
  forall a c, step_iter (CSTAR a c) ≡ star (step_iter c).
Proof.
  intros a c s s'. unfold step_iter. apply cexec_cstar_iff_star.
Qed.

(** [CSTAR c ;; c] and [c ;; CSTAR c] are semantically equivalent: the
    classical Kleene-algebra identity [R* · R = R · R*]. *)
Lemma cstar_seq_comm:
  forall a c, step_iter ((CSTAR a c) ;; c) ≡ step_iter (c ;; (CSTAR a c)).
Proof.
  intros a c.
  rewrite !step_iter_seq. rewrite !step_iter_cstar.
  symmetry. apply rcomp_star_shift.
Qed.

(** We now show an equivalence between evaluations that terminate according
    to the natural semantics
        (existence of a derivation of [cexec s c s'])
    and to the reduction semantics
        (existence of a reduction sequence from [(c,s)] to [(SKIP, s')].

    We start with the natural semantics => reduction sequence direction,
    which is proved by an elegant induction on the derivation of [cexec]. *)

Theorem cexec_to_reds:
  forall s c r, cexec s c r -> terminates_result s c r.
Proof.
  induction 1.
  - (* SKIP *)
    exists (SKIP, s). split.
    + apply star_refl.
    + apply final_skip.
  - (* ERROR *)
    exists (ERROR, s). split.
    + apply star_refl.
    + apply final_error.
  - (* ASSIGN *)
    exists (SKIP, update x (aeval a s) s). split.
    + apply star_one. apply red_assign.
    + apply final_skip.
  - (* NONDET *)
    exists (SKIP, update x n s). split.
    + apply star_one. apply red_nondet.
    + apply final_skip.
  - (* ASSUME *)
    exists (SKIP, s). split.
    + apply star_one. apply red_assume. assumption.
    + apply final_skip.
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
  - (* CSTAR step iter error (body ok, then iteration errors) *)
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

(* * One full body execution yields at least one [red] step from [c★] to [c★]. *)
Lemma plus_cstar_iteration:
  forall a c s s',
    star red (c, s) (SKIP, s') ->
    plus red (CSTAR a c, s) (CSTAR a c, s').
Proof.
  intros a c s s' STARC.
  eapply plus_left.
  - apply red_cstar_step.
  - eapply star_trans.
    + (* reduce the body on the left of the sequence *)
      apply red_seq_steps with (c2 := CSTAR a c) in STARC.
      exact STARC.
    + (* then drop the leading SKIP *)
      apply star_one. apply red_seq_done.
Qed.


(** If the body always terminates (and is not [SKIP]), we can repeat it forever,
    hence there exists an infinite reduction sequence for [c★]. *)
Lemma diverges_cstar_via_cexec_cstar_step:
  forall a c s,
    (forall st, exists st', st =[ c ]=> RNormal st') ->
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

(** The other direction, from a reduction sequence to a [cexec]
    derivation, is more subtle.  Here is the key lemma, showing how a
    reduction step followed by a [cexec] execution can combine into a
    [cexec] execution. *)

Lemma red_append_cexec:
  forall c1 s1 c2 s2, red (c1, s1) (c2, s2) ->
  forall s', s2 =[ c2 ]=> s' -> s1 =[ c1 ]=> s'.
Proof.
  intros until s2; intros STEP. dependent induction STEP; intros s' EXEC.
  - (* red_assign *)
    inversion EXEC; subst. apply cexec_assign.
  - (* red_nondet *)
    inversion EXEC; subst. eapply cexec_nondet.
  - (* red_assume *)
    inversion EXEC; subst. eapply cexec_assume; eauto.
  - (* red_seq_done  *)
    destruct s' as [st'|].
    + apply cexec_seq with s2. apply cexec_skip. exact EXEC.
    + apply cexec_seq_error_right with s2. apply cexec_skip. exact EXEC.
  - (* red_seq_error *)
    inversion EXEC; subst.
    eapply cexec_seq_error. apply cexec_error.
  - (* red_seq_step *)
    inversion EXEC; subst.
    + (* normal *)
      eapply cexec_seq.
      * eapply IHSTEP; eauto.
      * exact H4.
    + (* error left *)
      eapply cexec_seq_error.
      eapply IHSTEP; eauto.
    + (* error right *)
      eapply cexec_seq_error_right.
      * eapply IHSTEP; eauto.
      * exact H4.
  - (* red_choice_left *)
    apply cexec_choice_left. exact EXEC.
  - (* red_choice_right *)
    apply cexec_choice_right. exact EXEC.
  - (* red_cstar_done *)
    inversion EXEC; subst. apply cexec_cstar_done.
  - (* red_cstar_step *)
    inversion EXEC; subst.
    + (* normal *)
      eapply cexec_cstar_step_ok; eauto.
    + (* error left *)
      eapply cexec_cstar_step_error; eauto.
    + (* error right *)
      eapply cexec_cstar_step_iter_error; eauto.
Qed.

(** By induction on the reduction sequence, it follows that a command
    that terminates according to the small-step semantics executes according
    to the natural semantics, with the same [result]. *)
Theorem reds_to_cexec:
  forall s c r,
  terminates_result s c r -> s =[ c ]=> r.
Proof.
  intros s c r (cs & STAR & FINAL).
  dependent induction STAR.
  - inversion FINAL; subst; constructor.
  - destruct b as [c2 s2].
    eapply red_append_cexec; eauto.
Qed.

Corollary reds_to_cexec_normal:
  forall s c s',
    star red (c, s) (SKIP, s') -> s =[ c ]=> RNormal s'.
Proof.
  intros s c s' STAR.
  apply reds_to_cexec.
  exists (SKIP, s'). split; [exact STAR | constructor].
Qed.

Corollary reds_to_cexec_error:
  forall s c s',
    star red (c, s) (ERROR, s') -> s =[ c ]=> RError s'.
Proof.
  intros s c s' STAR.
  apply reds_to_cexec.
  exists (ERROR, s'). split; [exact STAR | constructor].
Qed.