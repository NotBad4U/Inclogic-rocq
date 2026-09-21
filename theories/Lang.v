(** * The language signature

    Everything in this development — the command syntax, the small- and
    big-step semantics, Hoare logic, Incorrectness Logic, SIL — is structural
    in the *command* constructors and indifferent to what a value is, what a
    store is, and how an expression is evaluated.  This file makes that
    indifference official: it packages the parts a client language must
    supply into a record [Lang.t], over which [Core.v] then defines [com] and
    [cexec] once and for all.

    The intended instances are

    - [Imp.ImpLang]: [value = Z], [store = {fmap string -> Z}], expressions
      the [aexp]/[bexp] of [Imp.v];
    - [CLang.ClightLang]: [value = CompCert's val], [store = temp_env =
      PTree.t val], expressions CompCert's [Clight.expr], restricted to the
      allocation-free fragment of [CFrag.v].

    ** Why evaluation is partial

    The one substantive change the C instance forces is that expression
    evaluation returns an [option].  In IMP every [aexp] has a value in every
    store; in C it does not.  [1/0], [1 << 64] and any operation on an
    uninitialised temporary have *no* value, and CompCert models that by
    having [sem_binary_operation] return [None] and the transition relation
    then admit no step at all — the state is stuck, which is CompCert's
    rendering of undefined behaviour.

    That is not an inconvenience to be worked around; it is exactly the thing
    an incorrectness logic is for.  A stuck state is a bug, and [ASSIGN] and
    [ASSUME] therefore each get a second rule in [Core.cexec] taking a [None]
    evaluation to [RError].  For IMP, whose [eval] is [Some ∘ aeval] and hence
    never [None], those rules are vacuous and the original semantics is
    recovered (see [Imp.cexec_assign_total] and friends).

    ** What is *not* in the signature

    [get] is here because assertions and the derived assignment rules need to
    read a store, but no rule of [Core.red] or [Core.cexec] uses it: the
    operational semantics needs only [update], [eval] and [beval].  The laws
    relating [get] and [update] are therefore split off into [Lang.laws], and
    the "an expression only reads the variables it mentions" property into
    [Lang.frame], so that an instance can be used for the metatheory before
    either has been established. *)

From Stdlib Require Import RelationClasses Morphisms Setoid.

(** The [Local Notation]s below abbreviate projections; the 9.2 deprecation
    nudges towards [Abbreviation], which the 9.0/9.1 bundles do not have. *)
Set Warnings "-notation-for-abbreviation".

Module Lang.

(** ** The signature proper

    [get] is partial rather than total-with-a-default.  Both instances want
    it that way: a CompCert [temp_env] genuinely has no value for an
    undeclared temporary — [Clight.eval_Etempvar] requires [le!id = Some v]
    and is stuck otherwise — and making that a default value would be a
    lie that then has to be excluded by a domain invariant carried through
    every proof.  An instance is free to define a total reader of its own on
    top for the benefit of its own assertion language; [Imp.sget] does. *)

Record t : Type := Make {
  ident  : Type;
  value  : Type;
  store  : Type;

  get    : store -> ident -> option value;
  update : ident -> value -> store -> store;

  expr   : Type;
  bexp   : Type;

  (** [None] means "no value in this store", i.e. undefined behaviour. *)
  eval   : expr -> store -> option value;
  beval  : bexp -> store -> option bool;

  (** Negation of a guard.  This is in the signature, rather than being left
      to each instance, because the *derived command forms* need it:
      [WHILE b DO c END] is [(ASSUME b ;; c)★ ;; ASSUME (bnot b)] and
      [IF b THEN c1 ELSE c2 END] is [(ASSUME b ;; c1) ⊕ (ASSUME (bnot b) ;; c2)].
      Without it those notations could not be stated once for every language.
      Both instances have it: [Imp.NOT], and [Eunop Onotbool] for Clight. *)
  bnot   : bexp -> bexp;
}.

Arguments get {_} _ _.
Arguments update {_} _ _ _.
Arguments eval {_} _ _.
Arguments beval {_} _ _.
Arguments bnot {_} _.

(** ** The store laws

    Not a [Prop]-record: [ident_dec] carries computational content, and the
    derived rules of [Inc.v] case on it.  Extensionality is what makes
    [update_shadow] and [update_get] derivable rather than primitive; it
    holds for both instances ([finmap]'s [fmapP], CompCert's
    [PTree.extensionality]). *)

Record laws (L : t) : Type := Laws {
  ident_dec : forall x y : ident L, {x = y} + {x <> y};

  get_update_same :
    forall (x : ident L) (v : value L) (s : store L),
    get (update x v s) x = Some v;
  get_update_other :
    forall (x y : ident L) (v : value L) (s : store L),
    y <> x -> get (update x v s) y = get s y;

  store_ext :
    forall s1 s2 : store L,
    (forall x : ident L, get s1 x = get s2 x) -> s1 = s2;

  (** [bnot] negates, and — this is the part that matters for the error
      semantics — preserves undefinedness: negating a guard that has no
      value still has no value, so [IF] and [WHILE] inherit the [RError]
      behaviour of their guard rather than silently taking a branch. *)
  beval_bnot :
    forall (b : bexp L) (s : store L),
    beval (bnot b) s = option_map negb (beval b s);
}.

Arguments ident_dec {L} _ _ _.
Arguments get_update_same {L} _ _ _ _.
Arguments get_update_other {L} _ _ _ _ _ _.
Arguments store_ext {L} _ _ _ _.
Arguments beval_bnot {L} _ _ _.

(** ** The frame property

    The generalisation of [Imp.aeval_free]: an expression's value depends
    only on the variables it may read.  [fv] is a *may*-read
    over-approximation, so an instance is free to return "every variable" if
    it has nothing better; the lemmas that use it then simply say nothing.
    This is what the framing and independence rules of [Inc.v] need, and it
    is the only thing they need — hence a record of its own, so that an
    instance with no frame reasoning can be built without it. *)

Record frame (L : t) : Type := Frame {
  fv  : expr L -> ident L -> Prop;
  fvb : bexp L -> ident L -> Prop;

  eval_agree :
    forall (a : expr L) (s1 s2 : store L),
    (forall x : ident L, fv a x -> get s1 x = get s2 x) ->
    eval a s1 = eval a s2;
  beval_agree :
    forall (b : bexp L) (s1 s2 : store L),
    (forall x : ident L, fvb b x -> get s1 x = get s2 x) ->
    beval b s1 = beval b s2;
}.

Arguments fv {L} _ _ _.
Arguments fvb {L} _ _ _.
Arguments eval_agree {L} _ _ _ _ _.
Arguments beval_agree {L} _ _ _ _ _.

(** ** Consequences of the laws *)

Section Derived.

Context {L : t} (HL : laws L).

Local Notation store := (store L).
Local Notation ident := (ident L).
Local Notation value := (value L).

(** Writing twice is writing once. *)
Lemma update_shadow :
  forall x (u v : value) (s : store),
  update x v (update x u s) = update x v s.
Proof.
  intros x u v s. apply (store_ext HL). intro y.
  destruct (ident_dec HL y x) as [-> | Hne].
  - rewrite !(get_update_same HL). reflexivity.
  - rewrite !(get_update_other HL) by exact Hne. reflexivity.
Qed.

(** Writing back what is already there changes nothing.  This is the
    generic form of [Imp.update_get], with the [x \in domf s] side condition
    replaced by the [Some] that a partial [get] makes explicit. *)
Lemma update_get :
  forall x (v : value) (s : store),
  get s x = Some v -> update x v s = s.
Proof.
  intros x v s Hget. apply (store_ext HL). intro y.
  destruct (ident_dec HL y x) as [-> | Hne].
  - rewrite (get_update_same HL). symmetry. exact Hget.
  - rewrite (get_update_other HL) by exact Hne. reflexivity.
Qed.

(** Independent writes commute. *)
Lemma update_comm :
  forall x y (u v : value) (s : store),
  x <> y ->
  update x u (update y v s) = update y v (update x u s).
Proof.
  intros x y u v s Hxy. apply (store_ext HL). intro z.
  destruct (ident_dec HL z x) as [-> | Hzx].
  - rewrite (get_update_same HL).
    rewrite (get_update_other HL) by exact Hxy.
    rewrite (get_update_same HL). reflexivity.
  - destruct (ident_dec HL z y) as [-> | Hzy].
    + rewrite (get_update_other HL) by exact Hzx.
      rewrite !(get_update_same HL). reflexivity.
    + rewrite !(get_update_other HL) by assumption. reflexivity.
Qed.

End Derived.

End Lang.

Notation lang := Lang.t.
