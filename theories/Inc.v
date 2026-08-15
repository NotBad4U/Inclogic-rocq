(** * Mechanized Incorrectness Logic

  Implementation of the Incorrectness Logic of O'Hearn [[1]].

  Sound over-approximation methods have been proved effective for guaranteeing the absence of errors, but inevitably they produce false alarms that can hamper the programmers.
  Conversely, under-approximation methods are aimed at bug finding and are free from false alarms.
  The incorrectness logic is a formal system for reasoning about under-approximation, and can be used to prove the presence of bugs in programs.
  It use a use a specification form:

<<  
    [presumption] code [result]
>>

  which says that the post-assertion result be an under-approximation (subset) of the final states that
  can be reached starting from states satisfying the presumption.
  Incorrectness logic adds post-assertions for errors as well as for normal termination, and these assertions describe erroneous states that can be reached by actual program executions

  * Relation to the Hoare triple

  An incorrectness triple is not the negation of a Hoare triple,
  it is its dual: writing [post(c)(P) = { r | ∃ s, P s ∧ cexec s c r }] for the set
  of results reachable from [P], the two forms are the two directions of one inclusion,

<<
    Hoare          ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄    is   post(c)(P) ⊆ Q     (over-approximate)
    Incorrectness  ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧   is   Q ⊆ post(c)(P)     (under-approximate)
>>

  (in [triple] the right-hand side is really the normal results in [Q], since Hoare here
  also rules out errors).  Neither direction implies the other, and neither implies the
  other's negation: an incorrectness triple with [Q = ffalse] is trivially valid whatever
  the program does.  Their conjunction is what pins down [post(c)(P) = Q] exactly.
  Read modally the duality is box against diamond over the reversed relation: Hoare says
  [P ⊆ [c] Q], every execution lands in [Q]; incorrectness says [Q ⊆ ⟨c⁻¹⟩ P], every result
  is witnessed by some execution.  ([Sil.v] takes the remaining corner, the backward
  under-approximate one.)

  Negation appears only when an incorrectness triple is *used* to refute a putative Hoare
  triple, and that needs two further side conditions — the Principle of Denial, [denial]:

<<  
    ⟦ U ⟧ c ⟦ ϵ ↑ U' ⟧  →  U ⇒ O  →  ¬ (U' ⇒ O')  →  ¬(⦃ O ⦄ c ⦃ O' ⦄)
>>

  The under-approximation must sit inside the putative precondition ([U ⇒ O]) and its
  result must escape the putative postcondition ([¬ (U' ⇒ O')]).  Its contrapositive is the
  Principle of Agreement, [agreement] (and [agreement_Triple] for the strong Hoare triple
  [⦇ _ ⦈ _ ⦇ _ ⦈]); the two are logically equivalent.  Because [triple] also demands
  error-freedom, an erroneous post gives a shorter refutation: ⟦ O ⟧ c ⟦ err ↑ E ⟧ with [E]
  satisfiable denies ⦃ O ⦄ c ⦃ O' ⦄ for *every* [O'].

  * Architecture overview:

  - [Inductive Inc_triple] represents the proof system of the incorrectness logic, and is defined by the rules in Fig 2 and Fig 3.
  - [IncTriple] denotes the semantics of the incorrectness logic triple.  It is
    _Definition 1_ (Post and Semantic Triples) read through _Definition 4_ (Interpretation of
    Specifications).
  - [Module IncSoundness] is _Theorem 5_ (Soundness): the semantics validates every axiom
    and inference rule, so every derivable triple is semantically valid.
  - [Module IncCompleteness] is _Theorem 6_ (Completeness): every valid triple is
    derivable.
  - [Module SP] is the strongest-post calculus, computing those posts rather than
    postulating them.  It follows Section 5.2 (Predicate Transformers), where the article gives
    the equations for [post] at choice and iteration, the latter by appeal to a loop invariant.
    Accordingly: functions [slp_ok] and [slp_err] computing the normal and erroneous
    posts syntactically, a side condition [vcond] discharging the loop invariants, and a
    verification-condition generator [vcgen] shown correct by [vcgen_sound].  The invariants
    ride on the commands themselves — [Imp.CSTAR] takes an [option assertion] — so there is
    no separate annotated language.  A loop left unannotated gets the exact post, the union
    of its iterates, which is what makes the search of [IncElpi.v] possible.

  [[1]] Peter W. O'Hearn. 2019. Incorrectness logic. Proc. ACM Program. Lang. 4, POPL,
  Article 10 (January 2020), 32 pages. https://doi.org/10.1145/3371078
*)

From Stdlib Require Import Arith ZArith Psatz Bool String List Program.Equality FunctionalExtensionality.
From mathcomp Require Import ssrbool eqtype choice.
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import finmap.
Set Warnings "notation-incompatible-prefix".
From IncLogic Require Import Imp Sequences Hoare.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope com_scope.

(** Rocq suggests level 0 for closed notations, but these triples must stay at
    level 90.  At level 0 a triple becomes a legal application argument, and
    since the command [c] sits between the brackets it is parsed at a level that
    admits application; [⟦ P ⟧ SKIP ⟦ Q ⟧] then re-parses as [SKIP] applied to a
    nested triple and the following [⟦] is swallowed.  The advice does not apply
    to notations with an interior argument of this kind. *)
Set Warnings "-closed-notation-not-level-0".

Reserved Notation "⟦ P ⟧ c ⟦ 'ok' ↑ Q ⟧" (at level 90, c at next level).

Reserved Notation "⟦ P ⟧ c ⟦ 'ϵ' ↑ Q ⟧" (at level 90, c at next level).

Reserved Notation "⟦ P ⟧ c ⟦ 'err' ↑ Q ⟧" (at level 90, c at next level).

(** The untagged form: [Q] is a raw [postassertion], free to distinguish
    [RNormal] from [RError].  It is the general shape, of which the three
    tagged notations above are instances — not an [ϵ] triple with the tag
    left implicit. *)
Reserved Notation "⟦ P ⟧ c ⟦ Q ⟧" (at level 90, c at next level).

Definition ffalse : assertion := fun _ => False.

(** * Conditions on free and modified variables

- O'Hearn defines Mod(C) syntactically, as "the set of variables modified by
  assignment statements in [C]" (IL §4, p.10:9); [modified_by] (in [Hoare.v]) mirrors this
  directly as a structural recursion over [com].
- Every [Free(-)] side condition, by contrast, is treated semantically,
  following the paper's definition of freeness as invariance under changing
  a variable (§4): [not_free]/[independent_of] plays that role for
  assertions, [aexp_indep] for expressions, and [cexec_indep] for commands.
  A compound condition such as "y ∉ Free(p,C,q)" or
  "(Free(e) ∪ {x}) ∩ Free(C) = ∅" is never computed as an actual variable
  set. It is unfolded argument by argument into a conjunction of these
  predicates, one per object mentioned (e.g. [not_free y P], [not_free y Q]
  and [cexec_indep c y] for "y ∉ Free(p,C,q)"). *)

(** Syntactic substitution [[e/x]] on arithmetic expressions. *)
Fixpoint asubst (x: ident) (e: aexp) (a: aexp) : aexp :=
  match a with
  | CONST n     => CONST n
  | VAR y       => if string_dec x y then e else VAR y
  | PLUS  a1 a2 => PLUS  (asubst x e a1) (asubst x e a2)
  | MINUS a1 a2 => MINUS (asubst x e a1) (asubst x e a2)
  end.

(** [not_free x P] denotes that [P] is invariant under changing [x]:
    "∀ σ v, σ ∈ P ⇔ (σ | x ↦ v) ∈ P" ([1] §4, p.10:7), i.e. [P] is
    independent of [x].

    Unfolded, [not_free x P] is [∀ s1 s2, (∀ z, z <> x -> s1 z = s2 z) ->
    ((λ y. y = x) s1 <-> (λ y. y = x) s2)]: take any two stores that agree on every variable other
    than [x] — [x] itself may or may not differ between them, the hypothesis
    says nothing about it. Whenever that's the case, [P] must give the same
    verdict (true or false) on both. So [P] simply never looks at [x]: no
    matter what value [x] holds, as long as every other variable stays
    fixed, [P]'s truth value can't change.

    "not free" ⇔ "doesn't depend on".
*)
Definition not_free (x: ident) (P: assertion) : Prop :=
  independent_of P (fun y => y = x).

(** [aexp_indep e vars] denotes that [e]'s value is unaffected by changes to the variables in [vars], i.e. Free(e) ∩ vars = ∅. *)
Definition aexp_indep (e: aexp) (vars: ident -> Prop) : Prop :=
  forall (s1 s2 : store), (forall y, ~ vars y -> s1 y = s2 y) -> aeval e s1 = aeval e s2.

(** [cexec_indep c x] denotes that [c]'s execution is invariant under
    changes to [x] i.e. x ∉ Mod(c) and [c] does not read [x]. *)
Definition cexec_indep (c: com) (x: ident) : Prop :=
  forall s v r,
  s =[ c ]=> r ->
  (update x v s) =[ c ]=>
        (match r with
         | RNormal s' => RNormal (update x v s')
         | RError  s' => RError  (update x v s')
         end).

(**
  This inductive type represents the proof system of:
  - _Fig 2_: Generic Proof Rules of Incorrectness Logic
  - and _Fig 3_: Rules for Variables and Mutation
*)
Inductive Inc_triple: assertion -> com -> postassertion -> Prop :=
| Inc_Empty_under_approx: forall P c,
  (*─────────────────── (Empty under-approximates)*)
  ⟦ P ⟧ c ⟦ ϵ ↑ ffalse ⟧
| Inc_consequence_gen: forall P P' c (Q Q': postassertion),
    (P -->> P') ->
    ⟦ P ⟧ c ⟦ Q ⟧ ->
    (Q' --* Q) ->
    (*────────────────── (Consequence) *)
    ⟦ P' ⟧ c ⟦ Q' ⟧
| Inc_disjunc: forall P1 P2 c (Q1 Q2: postassertion),
    ⟦ P1 ⟧ c ⟦ Q1 ⟧ ->
    ⟦ P2 ⟧ c ⟦ Q2 ⟧ ->
    (*─────────────────────────────── (Disjunction) *)
    ⟦ P1 \\// P2 ⟧ c ⟦ fun r => Q1 r \/ Q2 r ⟧
| Inc_triple_skip: forall P,
  (*─────────────────── (Unit) *)
  ⟦ P ⟧ SKIP ⟦ ok ↑ P ⟧
| Inc_err_seq: forall P c1 c2 R,
    ⟦ P ⟧ c1 ⟦ err ↑ R ⟧ ->
    (*──────────── (Sequencing (short-circuit)) *)
    ⟦ P ⟧ (c1 ;; c2) ⟦ err ↑ R ⟧
| Inc_ok_seq: forall P c1 c2 Q1 (Q2: postassertion),
    ⟦ P ⟧ c1 ⟦ ok ↑ Q1 ⟧ ->
    ⟦ Q1 ⟧ c2 ⟦ Q2 ⟧ ->
    (*───────────── (Sequencing (normal)) *)
    ⟦ P ⟧ (c1 ;; c2) ⟦ Q2 ⟧
| Inc_iterate_zero: forall P ann c,
    (*─────────────────── (Iterate zero) *)
    ⟦ P ⟧ CSTAR ann c ⟦ ok ↑ P ⟧
| Inc_iterate_step: forall P ann c (Q: postassertion),
    ⟦ P ⟧ (CSTAR ann c ;; c) ⟦ Q ⟧ ->
    (*───────────────────────────── (Iterate non-zero) *)
    ⟦ P ⟧ (CSTAR ann c) ⟦ Q ⟧
| Inc_backwards_var: forall (P: nat -> assertion) ann c,
    (forall n, ⟦ P n ⟧ c ⟦ ok ↑ P (S n) ⟧) ->
    (*────────────────────────────────────────────────── (Backwards Variant (where n fresh)) *)
    ⟦ P 0%nat ⟧ CSTAR ann c ⟦ ok ↑ (fun s => exists m, P m s) ⟧
| Inc_choice_l: forall P c1 c2 (Q: postassertion),
    ⟦ P ⟧ c1 ⟦ Q ⟧ ->
    (*───────────────────── (Choice i = 1) *)
    ⟦ P ⟧ (c1 ⊕ c2) ⟦ Q ⟧
| Inc_choice_r: forall P c1 c2 (Q: postassertion),
    ⟦ P ⟧ c2 ⟦ Q ⟧ ->
    (*───────────────────── (Choice i = 2) *)
    ⟦ P ⟧ (c1 ⊕ c2) ⟦ Q ⟧
| Inc_error: forall P,
    (*────────────────── (Error) *)
    ⟦ P ⟧ ERROR ⟦ err ↑ P ⟧
| Inc_assume : forall P b,
    (*──────────────────────────────────── (Assume) *)
    ⟦ P ⟧ (ASSUME b) ⟦ ok ↑ atrue b //\\ P ⟧
| Inc_assign_sp: forall x a P,
    (*──────────────────────────────────────────────────────────────────── (Assignment) *)
    ⟦ P ⟧ ASSIGN x a ⟦ ok ↑ (fun s' => exists s, P s /\ s' = update x (aeval a s) s) ⟧
| Inc_nondet_sp: forall x P,
    (*──────────────────────────────────────────────────────────────────── (Nondet Assignment) *)
    ⟦ P ⟧ NONDET x ⟦ ok ↑ (fun s' => exists s n, P s /\ s' = update x n s) ⟧
| Inc_constancy: forall P c Q f,
    ⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧ ->
    independent_of f (modified_by c) -> (* i.e. Mod(C) ∩ Free(f) = ∅ *)
    (*─────────────────────────────── (Constancy) *)
    ⟦ P //\\ f ⟧ c ⟦ ϵ ↑ Q //\\ f ⟧
| Inc_subst_I: forall x e c P Q,
    ⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧ ->
    ~ modified_by c x ->
    cexec_indep c x ->
    aexp_indep e (modified_by c) ->
    (*─────────────────────────────── (Substitution I) *)
    ⟦ P [ x ↦ e ] ⟧ c ⟦ ϵ ↑ Q [ x ↦ e ] //\\ in_domf x ⟧
| Inc_subst_II: forall x y c P Q, (* alpha renaming for logical/ghost variable *)
    x <> y ->
    ⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧ ->
    cexec_indep c x ->
    ~ modified_by c x ->
    ~ modified_by c y ->
    (* The paper's own side condition is just [y ∉ Free(p,C,q)], i.e.
       [not_free y P], [not_free y Q] and [cexec_indep c y]. Our proof
       (see [inc_triple_subst_II]) goes through without ever needing
       those three — [cexec_indep c x] together with the two
       [modified_by] facts already suffice — so they're dropped here. *)
    (*─────────────────────────────── (Substitution II) *)
    ⟦ P [ x ↦ VAR y ] ⟧ c ⟦ ϵ ↑ Q [ x ↦ VAR y ] //\\ in_domf x //\\ in_domf y ⟧
where "⟦ P ⟧ c ⟦ 'ϵ' ↑ Q ⟧" :=
  (Inc_triple P c (fun r => match r with
                            | RNormal s => Q s
                            | RError s => Q s
                            end))
and
 "⟦ P ⟧ c ⟦ 'ok' ↑ Q ⟧" :=
  (Inc_triple P c (fun r => match r with
                            | RNormal s => Q s
                            | RError _ => False
                            end))
and "⟦ P ⟧ c ⟦ 'err' ↑ Q ⟧" :=
  (Inc_triple P c (fun r => match r with
                            | RNormal _ => False
                            | RError s => Q s
                            end))
and "⟦ P ⟧ c ⟦ Q ⟧" := (Inc_triple P c Q).

(** The notation [[p]C[ok: q][er: r]] is a shorthand for [[p]C[ok: q]] and [[p]C[er: r]] taken together. *)
Notation "⟦ P ⟧ c ⟦ 'ok' ↑ Q1 ⟧ ⟦ 'err' ↑ Q2 ⟧" := (⟦ P ⟧ c ⟦ err ↑ Q1 ⟧  /\ ⟦ P ⟧ c ⟦ ok ↑ Q2 ⟧) (at level 90, c at next level).

Lemma eps_to_ok: forall P c Q,
  ⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧ -> ⟦ P ⟧ c ⟦ ok ↑ Q ⟧.
Proof.
  intros P c Q H.
  eapply Inc_consequence_gen; [ intros s Hs; exact Hs | exact H | ].
  intros r; destruct r; cbn; tauto.
Qed.

Lemma eps_to_err: forall P c Q,
  ⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧ -> ⟦ P ⟧ c ⟦ err ↑ Q ⟧.
Proof.
  intros P c Q H.
  eapply Inc_consequence_gen; [ intros s Hs; exact Hs | exact H | ].
  intros r; destruct r; cbn; tauto.
Qed.

(** ** Derivated rules
  Everything inference rules below are proved from the original rules in
  [Inc_triple] above described in the original theory.

  Several of those constructors are stated over a raw [postassertion], because
  their justification never inspects how the command exited.  That is general,
  but inconvenient in practice: the exit condition has to be spelled out at
  every use.  The lemmas below fix a tag (e.g [ϵ = ok]) once and for all.
  - [Inc_post_weaken]: Consequence rule restricted to post
  - [Inc_pre_strengthen]: Consequence rule restricted to pre
  - [Inc_err_cstar]: the erroring iteration rule combining [Inc_iterate_step] and [Inc_ok_seq].
  - [Inc_combine_ok_err]: the rule for combining [[P]c[ok↑A]] and [[P]c[err↑B]] triples into [[P]c[ok↑A][err↑B]].
  - [Inc_ok_ffalse], [Inc_err_ffalse]: the empty post in each tag shape.
  - [Inc_assign_fwd], [Inc_nondet]: O'Hearn's substitution-style forward
    rules.  They are strictly weaker than the relational images
    [Inc_assign_sp] and [Inc_nondet_sp] — they lose the states in which the
    assigned variable was not yet in the store's domain, since no old value
    then reconstructs the pre-store — so they are obtained by post-weakening.
  - [Inc_ok_choice], [Inc_err_choice]: the tag-tracking choice rules, from
    [Inc_choice_l] and [Inc_choice_r] unioned by [Inc_disjunc].
  - [Inc_choice_l_eps], [Inc_choice_r_eps]: the same constructors read at an [ϵ] post.
  - [Inc_consequence]: the [ϵ]-shaped consequence rule, from [Inc_consequence_gen].
  - [Inc_err_seq_split]: an error of a sequence arises either in the first
    command or in the second; this is the form [sp_der] consumes.
  - [Inc_backwards_variant]: the backwards-variant rule of the paper, from
    [Inc_backwards_var]. ([Inc_iterate_zero] is a primitive constructor of
    [Inc_triple], not a derived rule.)
  - [disjunction_ϵ]: post-union at a fixed command and precondition.
*)

(** Post-weakening (consequence keeping the precondition fixed). *)
Lemma Inc_post_weaken: forall P c (Q Q': postassertion),
  ⟦ P ⟧ c ⟦ Q ⟧ -> (Q' --* Q) -> ⟦ P ⟧ c ⟦ Q' ⟧.
Proof.
  intros P c Q Q' H Hsub.
  eapply Inc_consequence_gen; [ intros s Hs; exact Hs | exact H | exact Hsub ].
Qed.


(** Post-strengthening (consequence keeping the postcondition fixed). *)
Lemma Inc_pre_strengthen: forall P P' c Q,
  ⟦ P ⟧ c ⟦ Q ⟧ -> (P -->> P') -> ⟦ P' ⟧ c ⟦ Q ⟧.
Proof.
  intros P P' c Q H Hsub.
  eapply Inc_consequence_gen.
  exact Hsub.
  exact H.
  intros r HQ. refine HQ.
Qed.

(** Erroring iteration: run the star to an intermediate assertion [M], take one
    further iteration of [c] that errors, and fold that extra iteration back
    into the star with [Inc_iterate_step]. *)
Lemma Inc_err_cstar: forall P ann c M R,
    ⟦ P ⟧ CSTAR ann c ⟦ ok ↑ M ⟧ ->
    ⟦ M ⟧ c ⟦ err ↑ R ⟧ ->
    (*──────────────────────────*)
    ⟦ P ⟧ CSTAR ann c ⟦ err ↑ R ⟧.
Proof.
  intros P ann c M R Hok Herr.
  apply Inc_iterate_step.
  exact (Inc_ok_seq P (CSTAR ann c) c M _ Hok Herr).
Qed.

(** Gluing an [ok] and an [err] triple over the same precondition into a single
    result-inspecting post.  This is [Inc_disjunc] read at the postassertion
    level: the disjunction of [ok ↑ A] and [err ↑ B] is [A] on [RNormal] and [B]
    on [RError], up to the vacuous [False] disjunct on each side. *)
Lemma Inc_combine_ok_err: forall P c A B,
    ⟦ P ⟧ c ⟦ ok ↑ A ⟧ ->
    ⟦ P ⟧ c ⟦ err ↑ B ⟧ ->
    (*──────────────────────────*)
    Inc_triple P c (fun r => match r with
                             | RNormal s => A s
                             | RError s => B s
                             end).
Proof.
  intros P c A B Hok Herr.
  eapply Inc_consequence_gen with (P := P \\// P).
  - unfold aor, aimp; intros s [Hs|Hs]; exact Hs.
  - apply (Inc_disjunc P P c _ _ Hok Herr).
  - intros r Hr; destruct r as [s|s]; cbn in Hr |- *; [ left | right ]; exact Hr.
Qed.

(** Specialize Empty under-approximates for ϵ = ok *)
Lemma Inc_ok_ffalse: forall P c, ⟦ P ⟧ c ⟦ ok ↑ ffalse ⟧.
Proof. intros P c. apply eps_to_ok, Inc_Empty_under_approx. Qed.

(** Specialize Empty under-approximates for ϵ = ok *)
Lemma Inc_err_ffalse: forall P c, ⟦ P ⟧ c ⟦ err ↑ ffalse ⟧.
Proof. intros P c. apply eps_to_err, Inc_Empty_under_approx. Qed.


Lemma Inc_assign_fwd: forall x a P,
  ⟦ P ⟧ ASSIGN x a ⟦ ok ↑ (fun s => x \in domf s) //\\ aexists (fun m => aexists (fun n =>
        aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n))) ⟧.
Proof.
  intros x a P.
  eapply Inc_consequence_gen;
    [ intros s Hs; exact Hs | apply (Inc_assign_sp x a P) | ].
  intros r; destruct r as [s'|s']; cbn; [ | tauto ].
  intros [Hdom [m [n [Heqx [HP Heqa]]]]].
  unfold aequal in Heqx, Heqa. cbn in Heqx, Heqa.
  exists (update x m s'). split; [ exact HP | ].
  rewrite Heqa, update_shadow, <- Heqx. symmetry. apply update_get. exact Hdom.
Qed.

Lemma Inc_nondet: forall x P,
  ⟦ P ⟧ NONDET x ⟦ ok ↑ (fun s => x \in domf s)
     //\\ aexists (fun n => aupdate x (CONST n) P) ⟧.
Proof.
  intros x P.
  eapply Inc_consequence_gen;
    [ intros s Hs; exact Hs | apply (Inc_nondet_sp x P) | ].
  intros r; destruct r as [s'|s']; cbn; [ | tauto ].
  intros [Hdom [m HP]].
  exists (update x m s'), (s' x). split; [ exact HP | ].
  rewrite update_shadow. symmetry. apply update_get. exact Hdom.
Qed.

Lemma Inc_ok_choice: forall P c1 c2 Q1 Q2,
    ⟦ P ⟧ c1 ⟦ ok ↑ Q1 ⟧ ->
    ⟦ P ⟧ c2 ⟦ ok ↑ Q2 ⟧ ->
    (*──────────────────────────────────*)
    ⟦ P ⟧ (c1 ⊕ c2) ⟦ ok ↑ (Q1 \\// Q2) ⟧.
Proof.
  intros P c1 c2 Q1 Q2 H1 H2.
  eapply Inc_consequence_gen with (P := P \\// P).
  - unfold aor, aimp; intros s [Hs|Hs]; exact Hs.
  - apply (Inc_disjunc P P (c1 ⊕ c2));
      [ apply Inc_choice_l, H1 | apply Inc_choice_r, H2 ].
  - intros r Hr; destruct r as [s|s]; cbn in Hr |- *;
      [ destruct Hr as [h|h]; [ left | right ]; exact h | destruct Hr ].
Qed.

Lemma Inc_err_choice: forall P c1 c2 R1 R2,
    ⟦ P ⟧ c1 ⟦ err ↑ R1 ⟧ ->
    ⟦ P ⟧ c2 ⟦ err ↑ R2 ⟧ ->
    (*──────────────────────────────────*)
    ⟦ P ⟧ (c1 ⊕ c2) ⟦ err ↑ (R1 \\// R2) ⟧.
Proof.
  intros P c1 c2 R1 R2 H1 H2.
  eapply Inc_consequence_gen with (P := P \\// P).
  - unfold aor, aimp; intros s [Hs|Hs]; exact Hs.
  - apply (Inc_disjunc P P (c1 ⊕ c2));
      [ apply Inc_choice_l, H1 | apply Inc_choice_r, H2 ].
  - intros r Hr; destruct r as [s|s]; cbn in Hr |- *;
      [ destruct Hr | destruct Hr as [h|h]; [ left | right ]; exact h ].
Qed.

Lemma Inc_choice_l_eps: forall P Q c1 c2,
    ⟦ P ⟧ c1 ⟦ ϵ ↑ Q ⟧ -> ⟦ P ⟧ (c1 ⊕ c2) ⟦ ϵ ↑ Q ⟧.
Proof. intros P Q c1 c2 H. apply Inc_choice_l, H. Qed.

Lemma Inc_choice_r_eps: forall P Q c1 c2,
    ⟦ P ⟧ c2 ⟦ ϵ ↑ Q ⟧ -> ⟦ P ⟧ (c1 ⊕ c2) ⟦ ϵ ↑ Q ⟧.
Proof. intros P Q c1 c2 H. apply Inc_choice_r, H. Qed.

(* Administrative lemma *)
Lemma Inc_consequence: forall P P' c Q Q',
    (P -->> P') ->
    ⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧ ->
    (Q' -->> Q) ->
    (*──────────────────*)
    ⟦ P' ⟧ c ⟦ ϵ ↑ Q' ⟧.
Proof.
  intros P P' c Q Q' HP HT HQ.
  eapply Inc_consequence_gen; [ exact HP | exact HT | ].
  intros r Hr; destruct r as [s|s]; apply HQ; exact Hr.
Qed.

(* Administrative lemma *)
Lemma Inc_err_seq_split: forall P c1 c2 Q1 R1 R2,
    ⟦ P ⟧ c1 ⟦ err ↑ R1 ⟧ ->
    ⟦ P ⟧ c1 ⟦ ok ↑ Q1 ⟧ ->
    ⟦ Q1 ⟧ c2 ⟦ err ↑ R2 ⟧ ->
    (*──────────────────────────────────*)
    ⟦ P ⟧ (c1 ;; c2) ⟦ err ↑ (R1 \\// R2) ⟧.
Proof.
  intros P c1 c2 Q1 R1 R2 HR1 HQ1 HR2.
  eapply Inc_consequence_gen with (P := P \\// P).
  - unfold aor, aimp; intros s [Hs|Hs]; exact Hs.
  - apply (Inc_disjunc P P (c1 ;; c2));
      [ apply Inc_err_seq, HR1 | exact (Inc_ok_seq P c1 c2 Q1 _ HQ1 HR2) ].
  - intros r Hr; destruct r as [s|s]; cbn in Hr |- *;
      [ destruct Hr | destruct Hr as [h|h]; [ left | right ]; exact h ].
Qed.

(** The backwards variant rule is [Inc_backwards_var] with [n + 1] in place of
    [S n] and an [ϵ]-shaped premise. *)
Lemma Inc_backwards_variant: forall (P: nat -> assertion) ann c,
    (forall n, ⟦ P n ⟧ c ⟦ ϵ ↑ P (n + 1)%nat ⟧) ->
    (*───────────────────────────────────────────────────────────*)
    ⟦ P 0%nat ⟧ CSTAR ann c ⟦ ok ↑ (fun s => exists (m: nat), P m s) ⟧.
Proof.
  intros P ann c H.
  apply Inc_backwards_var. intros n. specialize (H n).
  rewrite Nat.add_1_r in H. apply eps_to_ok, H.
Qed.

Lemma disjunction_ϵ: forall P c Q1 Q2,
    ⟦ P ⟧ c ⟦ ϵ ↑ Q1 ⟧ ->
    ⟦ P ⟧ c ⟦ ϵ ↑ Q2 ⟧ ->
    ⟦ P ⟧ c ⟦ ϵ ↑ (fun s => Q1 s \/ Q2 s) ⟧.
Proof.
  intros P c Q1 Q2 H1 H2.
  eapply Inc_consequence with (P := P \\// P) (Q := Q1 \\// Q2).
  - unfold aor, aimp; intros s [HP | HP]; exact HP.
  - eapply Inc_consequence_gen;
      [ intros s Hs; exact Hs | apply (Inc_disjunc P P c _ _ H1 H2) | ].
    intros r Hr; destruct r as [s|s]; cbn in Hr |- *;
      destruct Hr as [h|h]; [ left | right | left | right ]; exact h.
  - unfold aor, aimp; auto.
Qed.

(** * Semantics *)

(**
  ** Semantic triple

The post image of a relation [r] is the function [post(r) : assertion -> assertion]
defined by
<<
  post(r) p = {σ' | ∃ σ ∈ p. (σ, σ') ∈ r}
>>

The under-approximate triple is then
<<
  [p] r [q] holds iff post(r) p ⊇ q
>>
Hence the triple can be read semantically as: every state in the postcondition is
reachable from some state in the precondition, that is,
<<
  ∀ σ_q ∈ q. ∃ σ_p ∈ p. (σ_p, σ_q) ∈ r
>>
*)
Definition IncTriple (P: assertion) (c: com) (Q: postassertion) : Prop :=
  forall r, Q r -> exists s, P s /\ cexec s c r.

(** [Imp.cexec_unannot] lifted to triples. *)
Lemma IncTriple_unannot: forall P c Q,
  IncTriple P c Q -> IncTriple P (unannot c) Q.
Proof.
  intros P c Q H r HQ. destruct (H r HQ) as [s [HP HX]].
  exists s. split; [ exact HP | apply cexec_unannot; exact HX ].
Qed.

Notation "⟦⟦ P ⟧⟧ c ⟦⟦ 'ϵ' ↑ Q ⟧⟧" :=
  (IncTriple P%A c (fun r => match r with
                             | RNormal s => Q%A s
                             | RError s  => Q%A s
                             end))
  (at level 90, c at next level).

Notation "⟦⟦ P ⟧⟧ c ⟦⟦ 'err' ↑ Q ⟧⟧" :=
  (IncTriple P%A c (fun r => match r with
                             | RNormal _ => False
                             | RError s  => Q%A s
                             end))
  (at level 90, c at next level).

Notation "⟦⟦ P ⟧⟧ c ⟦⟦ 'ok' ↑ Q ⟧⟧" :=
  (IncTriple P%A c (fun r => match r with
                             | RNormal s => Q%A s
                             | RError _  => False
                             end))
  (at level 90, c at next level).

(* Postassertion-level triple: [Q] is a [postassertion] (it inspects the
   result), as opposed to the [ϵ/ok/err ↑] variants which lift an [assertion]. *)
Notation "⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧" := (IncTriple P c Q) (at level 90, c at next level).

Lemma inc_triple_disjunc: forall P1 P2 c Q1 Q2,
    ⟦⟦ P1 ⟧⟧ c ⟦⟦ ϵ ↑ Q1 ⟧⟧ ->
    ⟦⟦ P2 ⟧⟧ c ⟦⟦ ϵ ↑ Q2 ⟧⟧ ->
    ⟦⟦ P1 \\// P2 ⟧⟧ c ⟦⟦ ϵ ↑ Q1 \\// Q2 ⟧⟧.
Proof.
  unfold aor. intros P1 P2 c Q1 Q2 H1 H2 r HQ.
  destruct r as [s | s]; destruct HQ as [HQ1 | HQ2].
  - destruct (H1 (RNormal s) HQ1) as (s0 & HP & EXEC).
    exists s0. split; [ left; exact HP | exact EXEC ].
  - destruct (H2 (RNormal s) HQ2) as (s0 & HP & EXEC).
    exists s0. split; [ right; exact HP | exact EXEC ].
  - destruct (H1 (RError s) HQ1) as (s0 & HP & EXEC).
    exists s0. split; [ left; exact HP | exact EXEC ].
  - destruct (H2 (RError s) HQ2) as (s0 & HP & EXEC).
    exists s0. split; [ right; exact HP | exact EXEC ].
Qed.

Lemma inc_triple_disjunc_gen: forall P1 P2 c (Q1 Q2: postassertion),
    ⟦⟦ P1 ⟧⟧ c ⟦⟦ Q1 ⟧⟧ ->
    ⟦⟦ P2 ⟧⟧ c ⟦⟦ Q2 ⟧⟧ ->
    ⟦⟦ P1 \\// P2 ⟧⟧ c ⟦⟦ fun r => Q1 r \/ Q2 r ⟧⟧.
Proof.
  unfold aor. intros P1 P2 c Q1 Q2 H1 H2 r [HQ1 | HQ2].
  - destruct (H1 r HQ1) as (s0 & HP & EXEC).
    exists s0. split; [ left; exact HP | exact EXEC ].
  - destruct (H2 r HQ2) as (s0 & HP & EXEC).
    exists s0. split; [ right; exact HP | exact EXEC ].
Qed.

Lemma inc_triple_choice_l_gen: forall P c1 c2 (Q: postassertion),
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ Q ⟧⟧.
Proof.
  intros P c1 c2 Q H r HQ.
  destruct (H r HQ) as (s & HPs & EXEC).
  exists s. split; [ exact HPs | apply cexec_choice_left; exact EXEC ].
Qed.

Lemma inc_triple_choice_r_gen: forall P c1 c2 (Q: postassertion),
    ⟦⟦ P ⟧⟧ c2 ⟦⟦ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ Q ⟧⟧.
Proof.
  intros P c1 c2 Q H r HQ.
  destruct (H r HQ) as (s & HPs & EXEC).
  exists s. split; [ exact HPs | apply cexec_choice_right; exact EXEC ].
Qed.

 (* [p]c[q1] ∧ [p]c[q2] ⇐⇒ [p]c[q1 ∨ q2] *)
Lemma inc_symmetry: forall P c Q1 Q2,
    (⟦ P ⟧ c ⟦ ϵ ↑ Q1 ⟧  /\ ⟦ P ⟧ c ⟦ ϵ ↑ Q2 ⟧)  ->
    ⟦ P ⟧ c ⟦ ϵ ↑ (fun s => Q1 s \/ Q2 s) ⟧.
Proof.
    intros P c Q1 Q2 [h1 h2].
    apply disjunction_ϵ; assumption.
Qed.

Lemma inc_triple_skip: forall P,
    ⟦⟦ P ⟧⟧ SKIP ⟦⟦ ok ↑ P ⟧⟧.
Proof.
    intros P r Hr.
    destruct r.
    - exists s. split; try assumption. apply cexec_skip.
    - exfalso. apply Hr.
Qed.

Lemma inc_triple_empty_under_approx: forall P c,
    ⟦⟦ P ⟧⟧  c ⟦⟦ ϵ ↑ ffalse ⟧⟧.
Proof.
    intros P c r Hr. destruct r; exfalso; apply Hr.
Qed.

Lemma inc_triple_seq_normal: forall P c1 c2 Q1 Q2,
    ⟦⟦ P ⟧⟧  c1 ⟦⟦ ok ↑ Q1 ⟧⟧ ->
    ⟦⟦ Q1 ⟧⟧  c2 ⟦⟦ ϵ ↑ Q2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧  c1 ;; c2 ⟦⟦ ϵ ↑ Q2 ⟧⟧.
Proof.
  intros P c1 c2 Q1 Q2 H1 H2 r HQ2.
  destruct (H2 r HQ2) as (s_mid & HQ1mid & EXEC2).
  destruct (H1 (RNormal s_mid) HQ1mid) as (s_pre & HPpre & EXEC1).
  exists s_pre. split; [ exact HPpre | ].
  destruct r as [s_final | sf].
  - eapply cexec_seq; eauto.
  - eapply cexec_seq_error_right; eauto.
Qed.

(* Generic sequencing on exit tag of Q2 *)
Lemma inc_triple_seq_ok_gen: forall P c1 c2 Q1 (Q2: postassertion),
    ⟦⟦ P ⟧⟧  c1 ⟦⟦ ok ↑ Q1 ⟧⟧ ->
    ⟦⟦ Q1 ⟧⟧ c2 ⟦⟦ Q2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧  (c1 ;; c2) ⟦⟦ Q2 ⟧⟧.
Proof.
  intros P c1 c2 Q1 Q2 H1 H2 r HQ2.
  destruct (H2 r HQ2) as (s_mid & HQ1mid & EXEC2).
  destruct (H1 (RNormal s_mid) HQ1mid) as (s_pre & HPpre & EXEC1).
  exists s_pre. split; [ exact HPpre | ].
  destruct r as [s_final | sf].
  - eapply cexec_seq; eauto.
  - eapply cexec_seq_error_right; eauto.
Qed.

Lemma inc_triple_seq_short_circuit: forall P c1 c2 Q,
    ⟦⟦ P ⟧⟧  c1 ⟦⟦ err ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧  c1 ;; c2 ⟦⟦ err ↑ Q ⟧⟧.
Proof.
  intros P c1 c2 Q H1 r HQ.
  destruct r as [s_final | sf]; [ exfalso; exact HQ | ].
  destruct (H1 (RError sf) HQ) as (s_pre & HPpre & EXEC1).
  exists s_pre. split; [ exact HPpre | ].
  apply cexec_seq_error. exact EXEC1.
Qed.

Lemma inc_triple_iterate_non_zero: forall P ann c (Q: postassertion),
    ⟦⟦ P ⟧⟧  CSTAR ann c ;; c  ⟦⟦ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧  CSTAR ann c ⟦⟦ Q ⟧⟧.
Proof.
  intros P ann c Q H r HQ.
  destruct (H r HQ) as (s & HPs & EXEC).
  inversion EXEC; subst.
  - (* CSTAR normal, then c normal: append one iteration *)
    exists s. split; [ exact HPs | ].
    apply cexec_cstar_iff_star.
    apply cexec_cstar_iff_star in H3.
    eapply star_trans; [ exact H3 | ].
    apply star_one. unfold step_iter. exact H5.
  - (* CSTAR errors directly *)
    exists s. split; [ exact HPs | exact H4 ].
  - (* CSTAR normal, then c errors: append an erroring iteration *)
    exists s. split; [ exact HPs | ].
    apply cexec_cstar_err_iff.
    apply cexec_cstar_iff_star in H3.
    exists s'. split; [ exact H3 | exact H5 ].
Qed.

Lemma inc_triple_iterate_zero: forall P ann c,
    ⟦⟦ P ⟧⟧  CSTAR ann c ⟦⟦ ok ↑ P ⟧⟧.
Proof.
    intros P ann c r Q.
    destruct r as [s | sf].
    - exists s.  split; [ exact Q | ]. constructor.
    - contradiction Q.
Qed.

Lemma inc_triple_consequence: forall P P' c Q Q',
    (P -->> P') ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧ ->
    (Q' -->> Q) ->
    ⟦⟦ P' ⟧⟧ c ⟦⟦ ϵ ↑ Q' ⟧⟧.
Proof.
  intros P P' c Q Q' HPP' H HQ'Q r HQ'r.
  assert (HQr : match r with RNormal s => Q s | RError s => Q s end).
  { destruct r as [s | s]; apply HQ'Q; exact HQ'r. }
  destruct (H r HQr) as (s & HPs & EXEC).
  exists s. split; [ apply HPP'; exact HPs | exact EXEC ].
Qed.

Lemma inc_triple_choice_l: forall P c1 c2 Q,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ϵ ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ ϵ ↑ Q ⟧⟧.
Proof.
  intros P c1 c2 Q H r HQ.
  destruct (H r HQ) as (s & HPs & EXEC).
  exists s. split; [ exact HPs | apply cexec_choice_left; exact EXEC ].
Qed.

Lemma inc_triple_assign_fwd: forall x a P,
  ⟦⟦ P ⟧⟧
  ASSIGN x a
  ⟦⟦ ok ↑ (fun s => x \in domf s) //\\ aexists (fun m => aexists (fun n =>
     aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n))) ⟧⟧.
Proof.
  intros x a P r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [Hdom [m [n [Heq_x [HP Heq_a]]]]].
  cbn in HP, Heq_a, Heq_x.
  unfold aequal in Heq_x, Heq_a. cbn in Heq_x, Heq_a.
  exists (update x m s'). split; [ exact HP | ].
  replace s' with (update x (aeval a (update x m s')) (update x m s')) at 2.
  - apply cexec_assign.
  - rewrite Heq_a, update_shadow, <- Heq_x. apply update_get. exact Hdom.
Qed.

Lemma inc_triple_choice_r: forall P c1 c2 Q,
    ⟦⟦ P ⟧⟧ c2 ⟦⟦ ϵ ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ ϵ ↑ Q ⟧⟧.
Proof.
  intros P c1 c2 Q H r HQ.
  destruct (H r HQ) as (s & HPs & EXEC).
  exists s. split; [ exact HPs | apply cexec_choice_right; exact EXEC ].
Qed.


Lemma inc_triple_backwards_variant: forall (P: nat -> assertion) c,
    (forall n, ⟦⟦ P n ⟧⟧ c ⟦⟦ ϵ ↑ P (n + 1)%nat ⟧⟧) ->
    ⟦⟦ P 0%nat ⟧⟧ c ★ ⟦⟦ ok ↑ (fun s => exists (m: nat), P m s) ⟧⟧.
Proof.
  intros P c H r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [m HPm].
  revert s' HPm.
  induction m as [| k IH]; intros s' HPm.
  - (* m = 0: take s = s' and use cexec_cstar_done *)
    exists s'. split; [ exact HPm | apply cexec_cstar_done ].
  - (* m = S k: chain H k to reach s' from a P k state, then induct *)
    assert (HPk1 : P (k + 1)%nat s') by (rewrite Nat.add_1_r; exact HPm).
    destruct (H k (RNormal s') HPk1) as (s_pre & HPk_pre & EXEC_step).
    destruct (IH s_pre HPk_pre) as (s & HP0s & EXEC_iter).
    exists s. split; [ exact HP0s | ].
    apply cexec_cstar_iff_star.
    apply cexec_cstar_iff_star in EXEC_iter.
    eapply star_trans; [ exact EXEC_iter | ].
    apply star_one. unfold step_iter. exact EXEC_step.
Qed.


Lemma inc_triple_error: forall P, ⟦⟦ P ⟧⟧ ERROR ⟦⟦ err ↑ P ⟧⟧.
Proof.
    intros P r c.
    destruct r as [s | sf].
    - exfalso. apply c.
    - exists sf. split; [ exact c | constructor ].
Qed.


Lemma inc_triple_assume: forall P B,
    ⟦⟦ P ⟧⟧ (ASSUME B) ⟦⟦ ok ↑ atrue B //\\ P ⟧⟧.
Proof.
    intros P B r HQ.
    destruct r as [s | sf].
    destruct HQ as [HB HP].
    - exists s. split.
        +   exact HP.
        + constructor. exact HB.
    - exfalso. apply HQ.
Qed.

(* Substitution I:
            [p] c [ε: q]
    ———————————————————————————————— ((Free(e) ∪ {x}) ∩ Free(C) = ∅)
        [p[e/x]] c [ε: q[e/x]]
*)
Lemma inc_triple_subst_I: forall x e c P Q,
  ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧ ->
  ~ modified_by c x ->
  cexec_indep c x ->
  aexp_indep e (modified_by c) ->
  ⟦⟦ P [ x ↦ e ] ⟧⟧ c ⟦⟦ ϵ ↑ Q [ x ↦ e ] //\\ in_domf x ⟧⟧.
Proof.
  unfold IncTriple, aupdate, aexp_indep, cexec_indep, aand, in_domf.
  intros x e c P Q HT NMOD IND EDEP r HQex.
  destruct r as [s_out | s_out].
  - set (v := aeval e s_out) in *.
    destruct HQex as [HQex Hdom_out].
    destruct (HT (RNormal (update x v s_out)) HQex) as (s_in & HPs_in & EXEC_in).
    pose proof (cexec_modified x s_in c _ EXEC_in NMOD) as Hsx_eq.
    cbn in Hsx_eq.
    assert (Hsx : s_in x = v) by (rewrite <- Hsx_eq; apply update_same).
    pose proof (cexec_dom_preserved x s_in c _ EXEC_in NMOD) as Hdom_in.
    cbn in Hdom_in.
    rewrite dom_update in Hdom_in. rewrite eqxx in Hdom_in. cbn in Hdom_in.
    assert (Hdom_sin : (x \in domf s_in) = true) by (rewrite Hdom_in; reflexivity).
    exists (update x (s_out x) s_in).
    assert (Heval : aeval e (update x (s_out x) s_in) = v).
    { apply EDEP. intros y NM.
      destruct (string_dec x y) as [-> | Hxy]; [ apply update_same | ].
      pose proof (cexec_modified y s_in c _ EXEC_in NM) as MODy.
      cbn in MODy. rewrite update_other; [|exact Hxy].
      rewrite <- MODy. rewrite update_other; [reflexivity|exact Hxy]. }
    split.
    + rewrite Heval.
      rewrite update_shadow. rewrite <- Hsx.
      rewrite update_get; [exact HPs_in | exact Hdom_sin].
    + pose proof (IND s_in (s_out x) _ EXEC_in) as STEP. cbn in STEP.
      rewrite update_shadow in STEP.
      assert (Heq_out : update x (s_out x) s_out = s_out)
        by (apply update_get; exact Hdom_out).
      rewrite Heq_out in STEP. exact STEP.
  - set (v := aeval e s_out) in *.
    destruct HQex as [HQex Hdom_out].
    destruct (HT (RError (update x v s_out)) HQex) as (s_in & HPs_in & EXEC_in).
    pose proof (cexec_modified x s_in c _ EXEC_in NMOD) as Hsx_eq.
    cbn in Hsx_eq.
    assert (Hsx : s_in x = v) by (rewrite <- Hsx_eq; apply update_same).
    pose proof (cexec_dom_preserved x s_in c _ EXEC_in NMOD) as Hdom_in.
    cbn in Hdom_in.
    rewrite dom_update in Hdom_in. rewrite eqxx in Hdom_in. cbn in Hdom_in.
    assert (Hdom_sin : (x \in domf s_in) = true) by (rewrite Hdom_in; reflexivity).
    exists (update x (s_out x) s_in).
    assert (Heval : aeval e (update x (s_out x) s_in) = v).
    { apply EDEP. intros y NM.
      destruct (string_dec x y) as [-> | Hxy]; [ apply update_same | ].
      pose proof (cexec_modified y s_in c _ EXEC_in NM) as MODy.
      cbn in MODy. rewrite update_other; [|exact Hxy].
      rewrite <- MODy. rewrite update_other; [reflexivity|exact Hxy]. }
    split.
    + rewrite Heval.
      rewrite update_shadow. rewrite <- Hsx.
      rewrite update_get; [exact HPs_in | exact Hdom_sin].
    + pose proof (IND s_in (s_out x) _ EXEC_in) as STEP. cbn in STEP.
      rewrite update_shadow in STEP.
      assert (Heq_out : update x (s_out x) s_out = s_out).
      { apply update_get. exact Hdom_out. }
      rewrite Heq_out in STEP. exact STEP.
Qed.

(** Substitution II (alpha renaming for logical/ghost variable):
  consistently rename [x] to a fresh variable [y]
  throughout a whole triple — from [P] c [ϵ: Q] derive
  [P[y/x]] c [ϵ: Q[y/x]]] (same command [c], only the specification
  is renamed).

<<  

        [p] c [ε: q]
  ———————————————————————————————— (y ∉ Free(p, C, q))
      ([p] c [ε: q])(y/x)
>>

  The paper only asks for [y] to be fresh, i.e. unused by [p], [C] and
  [q]. But we need more than that, the conclusion keeps the very same [c]
  — we never rewrite occurrences of [x] to [y] inside [c] itself, only around it, in [P] and [Q].
  So the same [c] is independent on the two variables.
  It's not enough for [c] to be blind to [y]; it must be
  just as blind to [x] — hence [cexec_indep c x] on top of the expected
  [cexec_indep c y] (see below for why even that is finally dropped).

  Concretely, the proof runs backwards: from a final store matching
  [Q[y/x]], it borrows a witness from the original triple by first
  copying [y]'s value into [x] (so the lookup matches [Q]), then has to
  undo that copy on the initial store afterwards, without disturbing
  [c]'s actual run. That undo step is exactly [cexec_indep c x].

  [~modified_by c x] and [~modified_by c y] are needed for a different
  reason: our stores are partial maps ([finmap]), not total functions —
  a variable can be genuinely *absent*, not just zero. If [c] could
  write to [x] or [y], it might add either to the store's domain where
  it wasn't before, breaking the domain bookkeeping ([x ∈ domf s_out],
  [y ∈ domf s_out]) the proof relies on to reconstruct states.

  Given all that, it turns out [not_free y P], [not_free y Q] and
  [cexec_indep c y] — the paper's own side condition, [y ∉ Free(p,C,q)]
  — are never actually needed: [cexec_indep c x] together with the two
  [modified_by] facts already carry the whole proof. So the version
  below drops them; see [Inc_subst_II] for the (shorter) syntactic rule.
*)
Lemma inc_triple_subst_II: forall x y c P Q,
  x <> y ->
  ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧ ->
  cexec_indep c x -> (* (doesn't read it)  *)
  ~ modified_by c x -> (* (doesn't write it) *)
  ~ modified_by c y -> (* (doesn't write the fresh variable) *)
  ⟦⟦ P [ x ↦ VAR y ] ⟧⟧ c
  ⟦⟦ ϵ ↑ Q [ x ↦ VAR y ] //\\ in_domf x //\\ in_domf y ⟧⟧.
Proof.
  unfold IncTriple, aupdate, aand, in_domf, not_free, independent_of.
  intros x y c P Q Hxy HT INDx NMODx NMODy r HQex.
  destruct r as [s_out | s_out].
  - destruct HQex as [HQex [Hdx Hdy]].
    cbn in HQex.
    destruct (HT (RNormal (update x (s_out y) s_out)) HQex)
      as (s_in & HPs_in & EXEC_in).
    cbn in EXEC_in.
    pose proof (cexec_dom_preserved x s_in c _ EXEC_in NMODx) as Hdom_xin.
    cbn in Hdom_xin. rewrite dom_update in Hdom_xin.
    rewrite eqxx in Hdom_xin. cbn in Hdom_xin.
    assert (Hdom_sin_x : (x \in domf s_in) = true)
      by (rewrite Hdom_xin; reflexivity).
    pose proof (cexec_modified x s_in c _ EXEC_in NMODx) as Hsx_eq.
    cbn in Hsx_eq.
    assert (Hsx : s_in x = s_out y) by (rewrite <- Hsx_eq; apply update_same).
    pose proof (cexec_modified y s_in c _ EXEC_in NMODy) as Hsy_eq.
    cbn in Hsy_eq.
    assert (Hsy : s_in y = s_out y).
    { rewrite <- Hsy_eq. rewrite update_other; [reflexivity | exact Hxy]. }
    exists (update x (s_out x) s_in).
    split.
    + cbn [aeval]. rewrite update_other; [|exact Hxy].
      rewrite update_shadow. rewrite Hsy, <- Hsx.
      rewrite update_get; [exact HPs_in | exact Hdom_sin_x].
    + pose proof (INDx s_in (s_out x) _ EXEC_in) as STEP. cbn in STEP.
      rewrite update_shadow in STEP.
      assert (Heq_out : update x (s_out x) s_out = s_out)
        by (apply update_get; exact Hdx).
      rewrite Heq_out in STEP. exact STEP.
  - destruct HQex as [HQex [Hdx Hdy]].
    cbn in HQex.
    destruct (HT (RError (update x (s_out y) s_out)) HQex)
      as (s_in & HPs_in & EXEC_in).
    cbn in EXEC_in.
    pose proof (cexec_dom_preserved x s_in c _ EXEC_in NMODx) as Hdom_xin.
    cbn in Hdom_xin. rewrite dom_update in Hdom_xin.
    rewrite eqxx in Hdom_xin. cbn in Hdom_xin.
    assert (Hdom_sin_x : (x \in domf s_in) = true)
      by (rewrite Hdom_xin; reflexivity).
    pose proof (cexec_modified x s_in c _ EXEC_in NMODx) as Hsx_eq.
    cbn in Hsx_eq.
    assert (Hsx : s_in x = s_out y) by (rewrite <- Hsx_eq; apply update_same).
    pose proof (cexec_modified y s_in c _ EXEC_in NMODy) as Hsy_eq.
    cbn in Hsy_eq.
    assert (Hsy : s_in y = s_out y).
    { rewrite <- Hsy_eq. rewrite update_other; [reflexivity | exact Hxy]. }
    exists (update x (s_out x) s_in).
    split.
    + cbn [aeval]. rewrite update_other; [|exact Hxy].
      rewrite update_shadow. rewrite Hsy, <- Hsx.
      rewrite update_get; [exact HPs_in | exact Hdom_sin_x].
    + pose proof (INDx s_in (s_out x) _ EXEC_in) as STEP. cbn in STEP.
      rewrite update_shadow in STEP.
      assert (Heq_out : update x (s_out x) s_out = s_out)
        by (apply update_get; exact Hdx).
      rewrite Heq_out in STEP. exact STEP.
Qed.

Lemma inc_triple_constancy: forall P c Q f,
    ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧ ->
    independent_of f (modified_by c) ->
    ⟦⟦ P //\\ f ⟧⟧ c ⟦⟦ ϵ ↑ Q //\\ f ⟧⟧.
Proof.
  unfold IncTriple, aand, independent_of.
  intros P c Q f HT INDEP r HQf.
  destruct r as [s_out | s_out]; destruct HQf as [HQs HFs].
  - destruct (HT (RNormal s_out) HQs) as (s & HPs & EXEC).
    exists s. split; [ split; [ exact HPs | ] | exact EXEC ].
    apply (proj1 (INDEP s_out s
      (fun x NMOD => cexec_modified x s c (RNormal s_out) EXEC NMOD))).
    exact HFs.
  - destruct (HT (RError s_out) HQs) as (s & HPs & EXEC).
    exists s. split; [ split; [ exact HPs | ] | exact EXEC ].
    apply (proj1 (INDEP s_out s
      (fun x NMOD => cexec_modified x s c (RError s_out) EXEC NMOD))).
    exact HFs.
Qed.

Lemma inc_triple_nondet: forall x P,
  ⟦⟦ P ⟧⟧ NONDET x
  ⟦⟦ ok ↑ (fun s => x \in domf s)
       //\\ aexists (fun n => aupdate x (CONST n) P) ⟧⟧.
Proof.
  intros x P r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [Hdom [n HPn]].
  cbn in HPn. unfold aupdate in HPn.
  exists (update x n s'). split; [ exact HPn | ].
  replace s' with (update x (s' x) (update x n s')) at 2.
  - apply cexec_nondet.
  - rewrite update_shadow. apply update_get. exact Hdom.
Qed.

(** O'Hearn's _Derived Unrolling Rule_: iteration can execute its
    body [i] times, so a post may be assembled from the finite unrollings. *)

Fixpoint cmd_n (i: nat) c : com :=
  match i with
  | 0%nat => SKIP
  | S n => c ;; cmd_n n c
  end.

(** A finite unrolling [cmd_n i c] is a refinement of [CSTAR c]: every
    execution of the unrolled form is an execution of the iteration.  Proven
    by induction on [i]. *)
Lemma cmd_n_to_cstar: forall i ann c s r,
  cexec s (cmd_n i c) r -> cexec s (CSTAR ann c) r.
Proof.
  induction i as [|n IH]; intros ann c s r EXEC; cbn in EXEC.
  - inversion EXEC; subst. apply cexec_cstar_done.
  - apply cexec_seq_inv in EXEC.
    destruct EXEC as
      [ (sm & sf & H1 & H2 & ->)
      | [ (sf & H1 & ->) | (sm & sf & H1 & H2 & ->) ] ].
    + apply (IH ann c sm (RNormal sf)) in H2.
      eapply cexec_cstar_step_ok; eauto.
    + eapply cexec_cstar_step_error; eauto.
    + apply (IH ann c sm (RError sf)) in H2.
      eapply cexec_cstar_step_iter_error; eauto.
Qed.

(*
  [p] C^i [ϵ: q_i], all i ≤ bound*
  ─────────────────────────────── (Derived Unrolling Rule)
  [p] C⋆ [ϵ: big-∨_(i ≤ bound) q_i]
*)
Lemma inc_triple_derived_unrolling: forall P c (postassert_i: nat -> assertion),
    (forall i, ⟦⟦ P ⟧⟧ (cmd_n i c) ⟦⟦ ϵ ↑ postassert_i i ⟧⟧) ->
    ⟦⟦ P ⟧⟧ c ★ ⟦⟦ ϵ ↑ aexists (fun i => postassert_i i) ⟧⟧.
Proof.
  intros P c postassert_i H r HQ.
  destruct r as [s' | s']; cbn in HQ; destruct HQ as [j Hj].
  - destruct (H j (RNormal s') Hj) as (s & HPs & EXEC).
    exists s. split; [ exact HPs | apply (cmd_n_to_cstar _ None) in EXEC; exact EXEC ].
  - destruct (H j (RError s') Hj) as (s & HPs & EXEC).
    exists s. split; [ exact HPs | apply (cmd_n_to_cstar _ None) in EXEC; exact EXEC ].
Qed.

(*
  [p] C1 [ϵ: q1]    [p] C2 [ϵ: q2]
  ─────────────────────────────── (Derived Rule of Choice)
  [p] C1 + C2 [ϵ: q1 ∨ q2]
*)
Lemma inc_triple_derived_choice: forall P c1 c2 Q1 Q2,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ϵ ↑ Q1 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c2 ⟦⟦ ϵ ↑ Q2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ ϵ ↑ Q1 \\// Q2 ⟧⟧.
Proof.
  intros P c1 c2 Q1 Q2 H1 H2.
  apply inc_triple_choice_l with (c2 := c2) in H1.
  apply inc_triple_choice_r with (c1 := c1) in H2.
  intros r HQ.
  destruct r as [s | s]; destruct HQ as [HQ1 | HQ2].
  - apply (H1 (RNormal s) HQ1).
  - apply (H2 (RNormal s) HQ2).
  - apply (H1 (RError s) HQ1).
  - apply (H2 (RError s) HQ2).
Qed.


(* Postassertion-level consequence: strengthen the precondition, shrink the postassertion. *)
Lemma inc_triple_consequence_gen: forall P P' c (Q Q': postassertion),
    (P -->> P') ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧ ->
    (Q' --* Q) ->
    ⟦⟦ P' ⟧⟧ c ⟦⟦ Q' ⟧⟧.
Proof.
  intros P P' c Q Q' HPP' HT Hsub r HQ'.
  destruct (HT r (Hsub r HQ')) as (s & HPs & EXEC).
  exists s. split; [ apply HPP'; exact HPs | exact EXEC ].
Qed.

(* Strongest normal post of an assignment. *)
Lemma inc_triple_assign_sp: forall x a P,
    ⟦⟦ P ⟧⟧ ASSIGN x a
    ⟦⟦ ok ↑ (fun s' => exists s, P s /\ s' = update x (aeval a s) s) ⟧⟧.
Proof.
  intros x a P r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [s [HP ->]].
  exists s. split; [ exact HP | apply cexec_assign ].
Qed.

(* Strongest normal post of a nondeterministic assignment. *)
Lemma inc_triple_nondet_sp: forall x P,
    ⟦⟦ P ⟧⟧ NONDET x
    ⟦⟦ ok ↑ (fun s' => exists s n, P s /\ s' = update x n s) ⟧⟧.
Proof.
  intros x P r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [s [n [HP ->]]].
  exists s. split; [ exact HP | apply cexec_nondet ].
Qed.

(* Normal sequencing. *)
Lemma inc_triple_seq_ok: forall P c1 c2 Q1 Q2,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ok ↑ Q1 ⟧⟧ ->
    ⟦⟦ Q1 ⟧⟧ c2 ⟦⟦ ok ↑ Q2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ;; c2) ⟦⟦ ok ↑ Q2 ⟧⟧.
Proof.
  intros P c1 c2 Q1 Q2 H1 H2 r HQ2.
  destruct r as [s | s]; [ | exfalso; exact HQ2 ].
  destruct (H2 (RNormal s) HQ2) as (s_mid & HQ1mid & EXEC2).
  destruct (H1 (RNormal s_mid) HQ1mid) as (s_pre & HPpre & EXEC1).
  exists s_pre. split; [ exact HPpre | eapply cexec_seq; eauto ].
Qed.

(* Erroring sequencing: the error arises in [c1], or after [c1] in [c2]. *)
Lemma inc_triple_err_seq: forall P c1 c2 Q1 R1 R2,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ err ↑ R1 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ok ↑ Q1 ⟧⟧ ->
    ⟦⟦ Q1 ⟧⟧ c2 ⟦⟦ err ↑ R2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ;; c2) ⟦⟦ err ↑ (R1 \\// R2) ⟧⟧.
Proof.
  intros P c1 c2 Q1 R1 R2 HR1 HQ1 HR2 r HR.
  destruct r as [s | s]; [ exfalso; exact HR | ].
  destruct HR as [H1 | H2].
  - destruct (HR1 (RError s) H1) as (s_pre & HP & EXEC1).
    exists s_pre. split; [ exact HP | apply cexec_seq_error; exact EXEC1 ].
  - destruct (HR2 (RError s) H2) as (s_mid & HQ1mid & EXEC2).
    destruct (HQ1 (RNormal s_mid) HQ1mid) as (s_pre & HP & EXEC1).
    exists s_pre. split; [ exact HP | eapply cexec_seq_error_right; eauto ].
Qed.

(* Normal choice. *)
Lemma inc_triple_ok_choice: forall P c1 c2 Q1 Q2,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ok ↑ Q1 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c2 ⟦⟦ ok ↑ Q2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ ok ↑ (Q1 \\// Q2) ⟧⟧.
Proof.
  intros P c1 c2 Q1 Q2 H1 H2 r HQ.
  destruct r as [s | s]; [ | exfalso; exact HQ ].
  destruct HQ as [HQ1 | HQ2].
  - destruct (H1 (RNormal s) HQ1) as (s0 & HP & EXEC).
    exists s0. split; [ exact HP | apply cexec_choice_left; exact EXEC ].
  - destruct (H2 (RNormal s) HQ2) as (s0 & HP & EXEC).
    exists s0. split; [ exact HP | apply cexec_choice_right; exact EXEC ].
Qed.

(* Erroring choice. *)
Lemma inc_triple_err_choice: forall P c1 c2 R1 R2,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ err ↑ R1 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c2 ⟦⟦ err ↑ R2 ⟧⟧ ->
    ⟦⟦ P ⟧⟧ (c1 ⊕ c2) ⟦⟦ err ↑ (R1 \\// R2) ⟧⟧.
Proof.
  intros P c1 c2 R1 R2 H1 H2 r HR.
  destruct r as [s | s]; [ exfalso; exact HR | ].
  destruct HR as [HR1 | HR2].
  - destruct (H1 (RError s) HR1) as (s0 & HP & EXEC).
    exists s0. split; [ exact HP | apply cexec_choice_left; exact EXEC ].
  - destruct (H2 (RError s) HR2) as (s0 & HP & EXEC).
    exists s0. split; [ exact HP | apply cexec_choice_right; exact EXEC ].
Qed.

(* Normal iteration: an [ok] invariant family [P n] (one more successful iteration each step) collects into [∃ m, P m]. *)
Lemma inc_triple_ok_cstar: forall (P: nat -> assertion) ann c,
    (forall n, ⟦⟦ P n ⟧⟧ c ⟦⟦ ok ↑ P (S n) ⟧⟧) ->
    ⟦⟦ P 0%nat ⟧⟧ CSTAR ann c ⟦⟦ ok ↑ (fun s => exists m, P m s) ⟧⟧.
Proof.
  intros P ann c H r HQ.
  destruct r as [s' | s']; [ | exfalso; exact HQ ].
  destruct HQ as [m HPm].
  revert s' HPm.
  induction m as [| k IH]; intros s' HPm.
  - exists s'. split; [ exact HPm | apply cexec_cstar_done ].
  - destruct (H k (RNormal s') HPm) as (s_pre & HPk & EXEC_step).
    destruct (IH s_pre HPk) as (s & HP0 & EXEC_iter).
    exists s. split; [ exact HP0 | ].
    apply cexec_cstar_iff_star.
    apply cexec_cstar_iff_star in EXEC_iter.
    eapply star_trans; [ exact EXEC_iter | ].
    apply star_one. unfold step_iter. exact EXEC_step.
Qed.

(* Erroring iteration: reach an intermediate [M] by normal iterations, then error in one more body execution. *)
Lemma inc_triple_err_cstar: forall P ann c M R,
    ⟦⟦ P ⟧⟧ CSTAR ann c ⟦⟦ ok ↑ M ⟧⟧ ->
    ⟦⟦ M ⟧⟧ c ⟦⟦ err ↑ R ⟧⟧ ->
    ⟦⟦ P ⟧⟧ CSTAR ann c ⟦⟦ err ↑ R ⟧⟧.
Proof.
  intros P ann c M R HM HR r HRr.
  destruct r as [s | s]; [ exfalso; exact HRr | ].
  destruct (HR (RError s) HRr) as (s_mid & HMmid & EXEC_c).
  destruct (HM (RNormal s_mid) HMmid) as (s_pre & HP & EXEC_star).
  exists s_pre. split; [ exact HP | ].
  apply cexec_cstar_err_iff.
  apply cexec_cstar_iff_star in EXEC_star.
  exists s_mid. split; [ exact EXEC_star | exact EXEC_c ].
Qed.

Lemma inc_triple_combine_ok_err: forall P c A B,
    ⟦⟦ P ⟧⟧ c ⟦⟦ ok ↑ A ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ err ↑ B ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ fun r => match r with
                          | RNormal s => A s
                          | RError s => B s
                          end ⟧⟧.
Proof.
  intros P c A B Hok Herr r HQ.
  destruct r as [s | s].
  - exact (Hok (RNormal s) HQ).
  - exact (Herr (RError s) HQ).
Qed.

(*
  An [ok] and an [err] reachability post combine into an [ϵ] post over
  their conjunction.  Derived from [inc_triple_combine_ok_err] (which builds
  the tag-distinguishing post) by shrinking that post to [A //\\ B] via
  [inc_triple_consequence_gen].
*)
Lemma inc_triple_ok_err_to_eps: forall P c A B,
    ⟦⟦ P ⟧⟧ c ⟦⟦ ok ↑ A ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ err ↑ B ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ (A //\\ B) ⟧⟧.
Proof.
  intros P c A B HA HB.
  eapply inc_triple_consequence_gen with
    (P := P)
    (Q := fun r => match r with
                   | RNormal s => A s
                   | RError s => B s
                   end).
  - intros s Hs; exact Hs.
  - exact (inc_triple_combine_ok_err P c A B HA HB).
  - intros r HAB; destruct r as [s | s]; destruct HAB as [HAs HBs];
      [ exact HAs | exact HBs ].
Qed.

(** * Soundness *)

Module IncSoundness.

(** O'Hearn, _Theorem 5_ (Soundness): the relational semantics validates every
    axiom and inference rule of Fig 2 and Fig 3.
*)
Theorem Inc_triple_sound_gen: forall P c (Q: postassertion),
    (⟦ P ⟧ c ⟦ Q ⟧) ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧.
Proof.
  intros P c Q H. induction H.
  - (* Inc_Empty_under_approx *) apply inc_triple_empty_under_approx.
  - (* Inc_consequence_gen *) eapply inc_triple_consequence_gen; eassumption.
  - (* Inc_disjunc *) apply inc_triple_disjunc_gen; assumption.
  - (* Inc_triple_skip *) apply inc_triple_skip.
  - (* Inc_err_seq *) apply inc_triple_seq_short_circuit; assumption.
  - (* Inc_ok_seq *) eapply inc_triple_seq_ok_gen; eassumption.
  - (* Inc_iterate_zero *) apply inc_triple_iterate_zero.
  - (* Inc_iterate_step *) apply inc_triple_iterate_non_zero; assumption.
  - (* Inc_backwards_var *) apply inc_triple_ok_cstar; assumption.
  - (* Inc_choice_l *) apply inc_triple_choice_l_gen; assumption.
  - (* Inc_choice_r *) apply inc_triple_choice_r_gen; assumption.
  - (* Inc_error *) apply inc_triple_error.
  - (* Inc_assume *) apply inc_triple_assume.
  - (* Inc_assign_sp *) apply inc_triple_assign_sp.
  - (* Inc_nondet_sp *) apply inc_triple_nondet_sp.
  - (* Inc_constancy *) apply inc_triple_constancy; assumption.
  - (* Inc_subst_I *) apply inc_triple_subst_I; assumption.
  - (* Inc_subst_II *) apply inc_triple_subst_II; assumption.
Qed.

(** The statement as O'Hearn writes it: an [ϵ] triple, i.e. a post that does
    not look at the exit tag. *)
Corollary Inc_triple_sound: forall P c (Q: assertion),
    (⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧) ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧.
Proof.
  intros P c Q H. apply Inc_triple_sound_gen, H.
Qed.

(**
  This section relates the two triples: Hoare's over-approximate ⦃ P ⦄ c ⦃ Q ⦄, from
  [Hoare], and the Incorrectness triple.  Everything below is derived from the soundness theorem above.

  The link itself is made by the Principles of Agreement and Denial ([agreement],
  [agreement_Triple], [denial]).  An incorrectness triple exhibits states that really
  are reachable, so it can *refute* a putative Hoare triple — which is what makes
  incorrectness logic a bug-finding logic rather than a verification one.

  The remaining properties of Fig. 1 live elsewhere in the file: the ∧∨ symmetry is
  [disjunction_ϵ] and [inc_symmetry], and the ⇑⇓ symmetry is [Inc_consequence].

  Fig. 1. Correctness and Incorrectness Principles
  (O'Hearn, "Incorrectness Logic", POPL 2020, p. 10:3)

<<
                        { - } c { - }
               -----------------------> Predicates
              /                             ↑
             /                              | ⊆
            /            post(c)            |
  Predicates -----------------------> Predicates
            \                               |
             \                              | ⊆
              \         [ - ] c [ - ]       ↓
               ----------------------> Predicates

      ∧∨ Symmetry:    [p]c[q1] ∧ [p]c[q2]  <=>  [p]c[q1 ∨ q2]
                      {p}c{q1} ∧ {p}c{q2}  <=>  {p}c{q1 ∧ q2}

      ⇑⇓ Symmetry:    p' <= p ∧ [p]c[q] ∧ q <= q'   =>   [p']c[q']
                      p' => p ∧ {p}c{q} ∧ q => q'   =>   {p'}c{q'}

      Principle of    [u]c[u'] ∧ u => o ∧ {o}c{o'}
        Agreement:      => u' => o'

      Principle of    [u]c[u'] ∧ u => o ∧ ¬(u' => o')
        Denial:         => ¬({o}c{o'})
>>

  To understand the Principle of Agreement, consider the following diagram:

<<
               o                                    o'
        +--------------+                    +--------------+
        |      *       |------------------->|      *       |
        |              |                    |              |
        |  +--------+  |                    |  +-----------+-----+
        |  |   *    |--|------------------->|  |    *      |     |
        |  |        |  |                    |  |           |     |
        |  |   *    |--|------------------->|  |    *      |  *  |  <-- in u',
        |  +--------+  |                    |  +-----------+-----+      not in o'
        |      u       |                    |       u'     |
        +--------------+                    +--------------+
>>

  the regions labelled u and u' represent assertions in an under-approximate triple <<[u] c [u']>> and the
  horizontal lines show the transition relation of the program. We think of the post-condition o'
  as the "test oracle" in a putative Hoare triple {o} c {o'}. If the question "is this a member of o'?"
  fails for a final state obtained by executing the program from a start state satisfying o, then the
  correctness triple is false. Denial says, as in this picture, that if we have an under-approximate
  triple taking a subset u of o to u', and part of u' lies outside of o', then our test oracle will fail on it,
  denying the putative triple; i.e., ¬({o} c {o'}). Agreement gives conditions under which the oracle
  will be happy: the picture would adjust so that u' was contained in o'.

  NOTE: Agreement and Denial are logically equivalent. Traditional program testing corresponds to when u and u' are both singleton sets describing a test run.
  Incorrectness logic uses predicates to describe bigger sets, while remaining under-approximate.
*)

(* Principle of Agreement: [u]c[u'] ∧ (u ⇒ o) ∧ {o} c {o'} ⇒ u' ⇒ o' *)
Lemma agreement: forall U c U' O O',
    ⟦ U ⟧ c ⟦ ϵ ↑ U' ⟧ ->
    U -->> O ->
    ⦃ O ⦄ c ⦃ O' ⦄  ->
    U' -->> O'.
Proof.
  intros U c U' O O' HIL HUO HHO s' HUs'.
  apply Inc_triple_sound in HIL.
  apply Soundness.triple_soundness in HHO.
  destruct (HIL (RNormal s') HUs') as (s & HUs & HEX).
  apply HUO in HUs.
  destruct (HHO s (RNormal s') HEX HUs) as (s'' & EQ & HO').
  inversion EQ; subst. exact HO'.
Qed.


(* Principle of Agreement for strong hoare triples *)
Lemma agreement_Triple: forall U c U' O O',
    ⟦ U ⟧ c ⟦ ϵ ↑ U' ⟧ ->
    U -->> O ->
    ⦇ O ⦈ c ⦇ O' ⦈  ->
    U' -->> O'.
Proof.
  intros U c U' O O' HIL HUO HHO s' HUs'.
  apply Inc_triple_sound in HIL.
  apply Soundness.Triple_partial_soundness in HHO.
  destruct (HIL (RNormal s') HUs') as (s & HUs & HEX).
  apply HUO in HUs.
  destruct (HHO s (RNormal s') HEX HUs) as (s'' & EQ & HO').
  inversion EQ; subst. exact HO'.
Qed.

(** [u] c [u'] ∧ u ⇒ o ∧ ¬ (u' ⇒ o') ⇒ ¬({o} c {o'}) *)
Lemma denial: forall U c U' O O',
    ⟦ U ⟧ c ⟦ ϵ ↑ U' ⟧ ->
    U -->> O ->
    ~ (U' -->> O') ->
    ~ (⦃ O ⦄ c ⦃ O' ⦄).
Proof.
  intros U c U' O O' HIL HUO HnotU'O' Hhoare.
  apply HnotU'O'.
  eapply agreement; eauto.
Qed.

End IncSoundness.

(** * Completeness  *)

Module IncCompleteness.

(** [sem_sp c P] is the post image [post(c)P] of _Definition 1_: the outcomes
    reachable from a [P]-state.  It is the extremal post in both directions —
    see [post_strongest_over_weakest_under] (*Proposition 8*) below. *)
Definition sem_sp (c: com) (P: assertion) : postassertion :=
  fun r => exists s, P s /\ cexec s c r.

Lemma sem_sp_valid: forall P c,
    ⟦⟦ P ⟧⟧ c ⟦⟦ sem_sp c P ⟧⟧.
Proof.
  intros P c r HQ. exact HQ.
Qed.

Lemma sem_sp_strongest: forall P c (Q: postassertion),
    ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧ ->
    Q  --* sem_sp c P.
Proof.
  intros P c Q HT r HQ. exact (HT r HQ).
Qed.

(** ** Weakest precondition, and how it links to the strongest post

    [sem_sp c P : postassertion] is the *image* of [P] under [c] — the outcomes
    reachable from some [P]-state.  Two backward (precondition) transformers are
    its companions:

    - [sem_wp c Q]  — the *existential* preimage: the states from which [c]
      *can* reach an outcome in [Q].  This is the weakest precondition of
      incorrectness / reverse-Hoare logic (angelic, under-approximate).
    - [sem_wlp c Q] — the *universal* preimage: the states from which *every*
      outcome of [c] lands in [Q].  This is the demonic weakest (liberal)
      precondition of Hoare logic.

    [sp] and [wp] are NOT equal — they don't even share a type.  What links them
    is a *Galois adjunction*: [sem_sp c] is the lower adjoint of [sem_wlp c].
    That adjunction is the precise sense in which "sp and wp are equivalent":
    each determines the other. *)

Definition sem_wp (c: com) (Q: postassertion) : assertion :=
  fun s => exists r, cexec s c r /\ Q r.

Definition sem_wlp (c: com) (Q: postassertion) : assertion :=
  fun s => forall r, cexec s c r -> Q r.

(** The adjunction [sem_sp c ⊣ sem_wlp c]: pushing [P] forward and asking that
    it land inside [Q] is the same as asking [P] was already inside the
    (liberal) preimage of [Q].  This Galois connection is the link between the
    strongest post and the (demonic) weakest precondition. *)
Lemma sp_wlp_galois: forall P c (Q: postassertion),
    (sem_sp c P --* Q) <-> (P -->> sem_wlp c Q).
Proof.
  intros P c Q. split.
  - intros H s HP r EXEC. apply H. exists s. split; [ exact HP | exact EXEC ].
  - intros H r (s & HP & EXEC). exact (H s HP r EXEC).
Qed.

(** The forward/backward duality between [sem_sp] and the *existential*
    preimage [sem_wp]: the image of [P] meets [Q] exactly when [P] meets the
    preimage of [Q].  Both sides say "there is a [P]-to-[Q] execution of [c]".
    This is the witness-level link between sp and the (angelic) wp. *)
Lemma sp_wp_meet: forall P c (Q: postassertion),
    (exists r, sem_sp c P r /\ Q r) <-> (exists s, P s /\ sem_wp c Q s).
Proof.
  intros P c Q. split.
  - intros (r & (s & HP & EXEC) & HQ).
    exists s. split; [ exact HP | exists r; split; [ exact EXEC | exact HQ ] ].
  - intros (s & HP & (r & EXEC & HQ)).
    exists r. split; [ exists s; split; [ exact HP | exact EXEC ] | exact HQ ].
Qed.

(** Incorrectness caveat.  An IL triple is the *reverse* inclusion below: every
    [Q]-outcome must have a [P]-predecessor.  Hence its principal transformer is
    the strongest post [sem_sp] (cf. [sem_sp_strongest]), not a weakest
    precondition: enlarging [P] only makes [Q --* sem_sp c P] easier to satisfy,
    so there is no *weakest* valid [P].  [sem_wp] remains the right backward
    operator for IL — but it is the order-*dual* of [sem_sp] (via [sp_wp_meet]),
    not its adjoint (that adjoint, [sem_wlp], characterises the Hoare reading). *)
Lemma il_triple_iff_sp: forall P c (Q: postassertion),
    ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧ <-> (Q --* sem_sp c P).
Proof.
  intros P c Q. split.
  - intros H r HQ. exact (H r HQ).
  - intros H r HQ. exact (H r HQ).
Qed.

(** ** Proposition 8

    O'Hearn's *Definition 7* names two extremal posts of a relation [r] at a
    pre [p]: [StrongestOverPost(r)p] is the least [q] with [{p} r {q}], and
    [WeakestUnderPost(r)p] is the greatest [q] with [[p] r [q]].
    *Proposition 8* is that both coincide with the post image itself:
<<
  StrongestOverPost(r) = WeakestUnderPost(r) = post(r)
>>

    Stating the over-approximate half needs a triple at [postassertion] level:
    [Hoare.triple] fixes the result to be [RNormal], so it only speaks about the
    ok-fragment, whereas [post] ranges over both exits of Fig 4.  [over_triple]
    is that generalisation — Hoare's triple is the [ok ↑] instance of it, see
    [hoare_triple_is_over_triple_ok] below. *)
Definition over_triple (P: assertion) (c: com) (Q: postassertion) : Prop :=
  forall s r, P s -> cexec s c r -> Q r.

(** [over_triple] is just [sem_wlp] read forward, so the over-approximate
    counterpart of [il_triple_iff_sp] is the [sem_sp ⊣ sem_wlp] adjunction. *)
Lemma over_triple_iff_wlp: forall P c (Q: postassertion),
    over_triple P c Q <-> (P -->> sem_wlp c Q).
Proof.
  intros P c Q. split.
  - intros H s HP r EXEC. exact (H s r HP EXEC).
  - intros H s r HP EXEC. exact (H s HP r EXEC).
Qed.

Lemma over_triple_iff_sp: forall P c (Q: postassertion),
    over_triple P c Q <-> (sem_sp c P --* Q).
Proof.
  intros P c Q.
  split; intros H.
  - apply sp_wlp_galois, over_triple_iff_wlp, H.
  - apply over_triple_iff_wlp, sp_wlp_galois, H.
Qed.

(** [post] is a valid over-approximate post, and the least one: it is
    [StrongestOverPost]. *)
Lemma sem_sp_over_valid: forall P c,
    over_triple P c (sem_sp c P).
Proof.
  intros P c. apply over_triple_iff_sp. intros r Hr. exact Hr.
Qed.

Lemma sem_sp_over_strongest: forall P c (Q: postassertion),
    over_triple P c Q ->
    sem_sp c P --* Q.
Proof.
  intros P c Q H. apply over_triple_iff_sp, H.
Qed.

(** Proposition 8, both halves.  Read as: [sem_sp c P] is the least valid
    over-post and, at the same time, the greatest valid under-post — the
    two extremal characterisations pick out the very same predicate, and
    [sem_sp] is [post(c)P] by definition. *)
Proposition post_strongest_over_weakest_under: forall P c,
    (* StrongestOverPost(c)P = post(c)P *)
    (over_triple P c (sem_sp c P) /\ forall Q, over_triple P c Q -> sem_sp c P --* Q)
    /\
    (* WeakestUnderPost(c)P = post(c)P *)
    (⟦⟦ P ⟧⟧ c ⟦⟦ sem_sp c P ⟧⟧ /\ forall Q, ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧ -> Q --* sem_sp c P).
Proof.
  intros P c. split; split.
  - apply sem_sp_over_valid.
  - apply sem_sp_over_strongest.
  - apply sem_sp_valid.
  - apply sem_sp_strongest.
Qed.

(** The two readings meet only at [post] itself: it is the unique
    postassertion that is both a valid over-post and a valid under-post of
    [P] through [c].  This is the sense in which the diagram of Fig. 1 —
    over-approximation above, under-approximation below — is pinched shut at
    the image. *)
Corollary over_and_under_iff_post: forall P c (Q: postassertion),
    (over_triple P c Q /\ ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧)
    <-> (forall r, Q r <-> sem_sp c P r).
Proof.
  intros P c Q. split.
  - intros (Hover & Hunder) r. split.
    + intros HQ. exact (Hunder r HQ).
    + intros Hsp. exact (sem_sp_over_strongest P c Q Hover r Hsp).
  - intros Heq. split.
    + apply over_triple_iff_sp. intros r Hr. apply Heq, Hr.
    + intros r HQ. apply Heq, HQ.
Qed.

(** Relation to Hoare.v.  We do *not* redefine the demonic [wlp] from scratch:
    Hoare.v's weakest liberal precondition [Completness.wlp] is exactly this
    [sem_wlp] specialised to the *ok-fragment* postassertion [ok ↑ Q] — the
    partial-correctness reading in which an error counts as failure.  So
    [sem_wlp] is the postassertion-level generalisation (errors are handled by
    [Q], not hard-wired to [False]) and Hoare's [wlp] is recovered as the
    instance below.  This is why the [sem_sp ⊣ sem_wlp] adjunction needs the
    general [sem_wlp]: [sem_sp c P] emits error outcomes, which Hoare's [wlp]
    would reject outright.

    For [sem_wp] there is nothing in Hoare.v to reuse: Hoare logic is demonic
    and only needs the *universal* preimage; the *existential* preimage is
    proper to incorrectness / reverse-Hoare logic. *)
Lemma hoare_wlp_is_sem_wlp_ok: forall c Q s,
    Completness.wlp c Q s
    <-> sem_wlp c (fun r => match r with RNormal s' => Q s' | RError _ => False end) s.
Proof.
  intros c Q s. unfold Completness.wlp, sem_wlp. split.
  - intros H r EXEC. destruct (H r EXEC) as (s' & -> & HQ). exact HQ.
  - intros H r EXEC. specialize (H r EXEC). destruct r as [s' | s'].
    + exists s'. split; [ reflexivity | exact H ].
    + contradiction.
Qed.

(** Likewise for the triple itself: Hoare's semantic [triple] is [over_triple]
    at the ok-fragment post, where an error counts as failure. *)
Lemma hoare_triple_is_over_triple_ok: forall P c Q,
    (⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄)
    <-> over_triple P c (fun r => match r with RNormal s' => Q s' | RError _ => False end).
Proof.
  intros P c Q. unfold triple, over_triple. split.
  - intros H s r HP EXEC. destruct (H s r EXEC HP) as (s' & -> & HQ). exact HQ.
  - intros H s r EXEC HP. specialize (H s r HP EXEC). destruct r as [s' | s'].
    + exists s'. split; [ reflexivity | exact H ].
    + contradiction.
Qed.

(** ** Syntactic strongest postconditions

[spo c P] / [spe c P] are the strongest normal / erroring postconditions
of [c] from [P], expressed directly through the operational semantics.
They are the two post-images of O'Hearn's _Definition 1_, taken over the
[ok] and [er] relations of Fig 4.  By _Proposition 8_ the post operator is
at once the strongest over-approximate and the weakest under-approximate
post (_Definition 7_), which is why weakening from it suffices below.

<<
  post(r)p = { σ' | ∃σ ∈ p. (σ, σ') ∈ r}
>>
*)

(** Strongest postconditions for normal execution _ok_ exit tag *)
Definition spo (c: com) (P: assertion) : assertion :=
  fun s' => exists s, P s /\ s =[ c ]=> RNormal s'.

(** Strongest postconditions for _error_ exit tag *)
Definition spe (c: com) (P: assertion) : assertion :=
  fun s' => exists s, P s /\ s =[ c ]=> RError s'.

(** [spo_iter c P n]: states reachable from [P] by exactly [n] successful
    iterations of [c]. *)
Fixpoint spo_iter (c: com) (P: assertion) (n: nat) : assertion :=
  match n with
  | 0%nat => P
  | S k => spo c (spo_iter c P k)
  end.


(** An [ok]/[err] triple whose post is empty is vacuously derivable. *)
Lemma Inc_ok_empty: forall P c (A: assertion),
  (forall s, ~ A s) -> ⟦ P ⟧ c ⟦ ok ↑ A ⟧.
Proof.
  intros P c A Hempty.
  eapply Inc_post_weaken; [ apply (Inc_Empty_under_approx P c) | ].
  intros r HA. destruct r as [s|s]; cbn in *; [ exfalso; exact (Hempty s HA) | exact HA ].
Qed.

Lemma Inc_err_empty: forall P c (B: assertion),
  (forall s, ~ B s) -> ⟦ P ⟧ c ⟦ err ↑ B ⟧.
Proof.
  intros P c B Hempty.
  eapply Inc_post_weaken; [ apply (Inc_Empty_under_approx P c) | ].
  intros r HB. destruct r as [s|s]; cbn in *; [ exact HB | exfalso; exact (Hempty s HB) ].
Qed.

(** [spo_iter] shifts: iterating from [spo c P] equals iterating one more from [P]. *)
Lemma spo_iter_shift: forall c P n,
  spo_iter c (spo c P) n = spo_iter c P (S n).
Proof.
  intros c P. induction n as [|k IH]; [ reflexivity | ].
  cbn. cbn in IH. rewrite IH. reflexivity.
Qed.

(** Every state reachable by [star]-iterations is captured by some [spo_iter]. *)
Lemma spo_star_complete: forall c s s',
  star (step_iter c) s s' -> forall P, P s -> exists n, (spo_iter c P n) s'.
Proof.
  intros c s s' HStar. induction HStar as [a | a b d Hab Hbd IH]; intros P HP.
  - exists 0%nat. exact HP.
  - destruct (IH (spo c P)) as [n Hn].
    + exists a. split; [ exact HP | exact Hab ].
    + exists (S n). rewrite <- spo_iter_shift. exact Hn.
Qed.


(** Discharge vacuous cases *)
Ltac sp_empty :=
  solve [ first [ apply Inc_ok_empty | apply Inc_err_empty ];
          intros ? (? & ? & HX); inversion HX ].

(** apply [rule], then show the strongest post is contained in the rule's post by inverting one step of the operational semantics *)
Ltac sp_weaken rule :=
  eapply Inc_post_weaken;
  [ eapply rule
  | intros [?|?]; cbn; try tauto;
    intros (? & ? & HX); inversion HX; subst;
    unfold spo, spe, aor, aand, atrue in *; eauto 8 ].

Lemma spo_cstar_der: forall ann c P,
  (forall P', ⟦ P' ⟧ c ⟦ ok ↑ spo c P' ⟧) ->
  ⟦ P ⟧ CSTAR ann c ⟦ ok ↑ spo (CSTAR ann c) P ⟧.
Proof.
  intros ann c P IH.
  eapply Inc_post_weaken.
  { apply (Inc_backwards_var (spo_iter c P) ann c). intros n. exact (IH _). }
  intros [s|s]; cbn; try tauto.
  intros (s0 & HP & HX). apply cexec_cstar_iff_star in HX.
  eapply spo_star_complete; eauto.
Qed.


(** ** Strongest-post derivability: the heart of completeness.

  For every command [c] and pre [P], the strongest normal post [spo c P]
  and erroring post [spe c P] are *derivable*.  Proven by induction on [c],
  using the tag-tracking rules.
*)
Lemma sp_der: forall c P,
  ⟦ P ⟧ c ⟦ ok ↑ spo c P ⟧ /\ ⟦ P ⟧ c ⟦ err ↑ spe c P ⟧.
Proof.
  induction c; intros P; split; try sp_empty.
  - (* SKIP, ok *)   sp_weaken Inc_triple_skip.
  - (* ERROR, err *) sp_weaken Inc_error.
  - (* ASSIGN, ok *) sp_weaken Inc_assign_sp.
  - (* NONDET, ok *) sp_weaken Inc_nondet_sp.
  - (* ASSUME, ok *) sp_weaken Inc_assume.
  - (* SEQ, ok *)
    destruct (IHc1 P) as [Hok1 _]. destruct (IHc2 (spo c1 P)) as [Hok2 _].
    sp_weaken (Inc_ok_seq _ _ _ _ _ Hok1 Hok2).
  - (* SEQ, err *)
    destruct (IHc1 P) as [Hok1 Herr1]. destruct (IHc2 (spo c1 P)) as [_ Herr2].
    sp_weaken (Inc_err_seq_split _ _ _ _ _ _ Herr1 Hok1 Herr2).
  - (* CHOICE, ok *)
    destruct (IHc1 P) as [Hok1 _]. destruct (IHc2 P) as [Hok2 _].
    sp_weaken (Inc_ok_choice _ _ _ _ _ Hok1 Hok2).
  - (* CHOICE, err *)
    destruct (IHc1 P) as [_ Herr1]. destruct (IHc2 P) as [_ Herr2].
    sp_weaken (Inc_err_choice _ _ _ _ _ Herr1 Herr2).
  - (* CSTAR, ok *)
    apply spo_cstar_der. intros P'. exact (proj1 (IHc P')).
  - (* CSTAR, err *)
    assert (Hok : ⟦ P ⟧ CSTAR ann c ⟦ ok ↑ spo (CSTAR ann c) P ⟧)
      by (apply spo_cstar_der; intros P'; exact (proj1 (IHc P'))).
    destruct (IHc (spo (CSTAR ann c) P)) as [_ Herr].
    eapply Inc_post_weaken; [ exact (Inc_err_cstar _ _ _ _ _ Hok Herr) | ].
    intros [s|s]; cbn; try tauto.
    intros (s0 & HP & HX). apply cexec_cstar_err_iff in HX.
    destruct HX as (s' & HStar & HcErr).
    exists s'. split; [ exists s0; split; [ exact HP | apply cexec_cstar_iff_star; exact HStar ] | exact HcErr ].
Qed.

(** O'Hearn, _Theorem 6_ (Completeness): every true triple is provable.  As in
    the article, the argument runs by induction on the command through the
    strongest posts, using the Backwards Variant rule for iteration. *)
Theorem Inc_complete:
  forall P c Q, ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧ -> ⟦ P ⟧ c ⟦ Q ⟧.
Proof.
  intros P c Q H.
  destruct (sp_der c P) as [Hok Herr].
  eapply Inc_post_weaken;
    [ exact (Inc_combine_ok_err P c (spo c P) (spe c P) Hok Herr) | ].
  intros r Hr; destruct r as [s|s]; exact (H _ Hr).
Qed.

Corollary Inc_complete_ϵ:
  forall P c Q, ⟦⟦ P ⟧⟧ c ⟦⟦ ϵ ↑ Q ⟧⟧ -> ⟦ P ⟧ c ⟦ ϵ ↑ Q ⟧.
Proof. intros P c Q H. exact (Inc_complete P c _ H). Qed.


End IncCompleteness.

(** * Strongest Postconditions Calculus *)

Module SP.
  (**
    Equations:
    <<
    SPₑ(C, p) = post(⟦C⟧ₑ)(p)
    [p] C [ε : q]  ⇔  q ⊆ SPₑ(C, p)

    SPₒₖ(skip, p) = p
    SPₑᵣ(skip, p) = false

    SPₒₖ(error(), p) = false
    SPₑᵣ(error(), p) = p

    SPₒₖ(assume(B), p) = p ∧ B
    SPₑᵣ(assume(B), p) = false

    SPₒₖ(x := e, p) = ∃x′. p[x′/x] ∧ x = e[x′/x]
    SPₑᵣ(x := e, p) = false

    SPₑᵣ(x := nondet(), p) = false
    SPₒₖ(x := nondet(), p) = ∃x′. p[x′/x]


    SPₒₖ(C₁ + C₂, p) = SPₒₖ(C₁, p) ∨ SPₒₖ(C₂, p)
    SPₑᵣ(C₁ + C₂, p) = SPₑᵣ(C₁, p) ∨ SPₑᵣ(C₂, p)

    SPₒₖ(C₁ ; C₂, p) = SPₒₖ(C₂, SPₒₖ(C₁, p))
    SPₑᵣ(C₁ ; C₂, p) = SPₑᵣ(C₁, p) ∨ SPₑᵣ(C₂, SPₒₖ(C₁, p))

    SPₑ(C*, p) = ⋁ₙ≥₀ SPₑ(Cⁿ, p)

    SPₑ(C(y/x), p) = q ⇒ SPₑ(local x.C, p) ⊇ ∃y.q

    SPₒₖ(assert(B), p) = p ∧ B
    SPₑᵣ(assert(B), p) = p ∧ ¬B

    [p] C [ε : q] ⇔ q ⊆ SPₑ(C, p) 
    U ⊆ SPₑ(C, p) ⇒ [p] C [ε : U]
    >>

    <<
    We can derive the SP equations for [WHILE] and [IF] command:
    F(X) = SPₒₖ(C, X ∧ B)
    F⁰(p) = p
    Fⁿ⁺¹(p) = F(Fⁿ(p))

    SPₒₖ(while B do C, p) = ⋁ₙ≥₀ (Fⁿ(p) ∧ ¬B)
    SPₑᵣ(while B do C, p) = ⋁ₙ≥₀ SPₑᵣ(C, Fⁿ(p) ∧ B)

    SPₑ(if B then C₁ else C₂, p) = SPₑ(C₁, p ∧ B) ∨ SPₑ(C₂, p ∧ ¬B)
    SPₒₖ(if B then C₁ else C₂, p) = SPₒₖ(C₁, p ∧ B) ∨ SPₒₖ(C₂, p ∧ ¬B)
    SPₑᵣ(if B then C₁ else C₂, p) = SPₑᵣ(C₁, p ∧ B) ∨ SPₑᵣ(C₂, p ∧ ¬B)
    >>
  *)

  (** Commands already carry their loop annotations ([Imp.CSTAR] takes an
      [option assertion]), so there is no separate annotated syntax and
      nothing to erase.

      The two cases of a loop are the whole point of the optional annotation:

      - [CSTAR (Some Inv) c] is pinned to [Inv], and [vcond] then owes the
        obligation that [Inv] really is reachable;
      - [CSTAR None c] gets the *exact* post, the union of the iterates.
        Under-approximation can afford this because the object is a least
        fixpoint; [Hoare.WP] cannot, its [wlp] being a greatest one, which is
        why annotations are mandatory there. *)

  (* Strongest Liberal Postcondition for normal executions *)

  (**
    The exact reachable post over every result tag at once.
    Strongest [ok]-post: the exact reachable store after _normal_ termination.
  *)
  Fixpoint slp_ok (P: assertion) (c: com) : assertion :=
  match c with
  | SKIP => fun s => P s
  | ERROR => ffalse
  | ASSUME b => atrue b //\\ P
  | ASSIGN x a => in_domf x //\\ aexists (fun (m: Z) => aexists (fun (n: Z) =>
      aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n)))
  | NONDET x => in_domf x //\\ aexists (fun (m: Z) => aupdate x (CONST m) P)
  | CHOICE c1 c2 => slp_ok P c1 \\// slp_ok P c2
  | SEQ c1 c2 => slp_ok (slp_ok P c1) c2
  | CSTAR (Some (AInv Inv)) _ => Inv
  | CSTAR (Some (AVar R)) _ => fun s => exists n, R n s
  | CSTAR None body =>
      (* the union of the iterates.  Spelled as a local fixpoint because
         [iter_slp_ok] below is defined in terms of [slp_ok] itself;
         [slp_ok_cstar_none] identifies the two. *)
      fun s => exists m,
        (fix it (n: nat) : assertion :=
           match n with O => P | S k => slp_ok (it k) body end) m s
  end.

  (** Strongest [err]-post: the exact reachable store after a *faulting* run.
      A loop faults exactly when its body faults at a state the loop can
      reach, uniformly [slp_ok P (CSTAR ann body)]. *)
  Fixpoint slp_err (P: assertion) (c: com) : assertion :=
  match c with
  | SKIP => ffalse
  | ERROR => P
  | ASSUME b => ffalse
  | ASSIGN x a => ffalse
  | NONDET x => ffalse
  | CHOICE c1 c2 => slp_err P c1 \\// slp_err P c2
  | SEQ c1 c2 => slp_err P c1 \\// slp_err (slp_ok P c1) c2
  | CSTAR ann body => slp_err (slp_ok P (CSTAR ann body)) body
  end.

  (** The strongest _postassertion_: it inspects the result tag and returns the
      [ok] post on normal termination and the [err] post on faulting. *)
  Definition sp (P: assertion) (c: com) : postassertion :=
    fun r => match r with
             | RNormal s => slp_ok P c s
             | RError s  => slp_err P c s
             end.

  (** [iter_slp_ok P c n] is the strongest [ok]-post after exactly [n]
      iterations of [c] from [P]. *)
  Fixpoint iter_slp_ok (P: assertion) (c: com) (n: nat) : assertion :=
    match n with
    | O => P
    | S k => slp_ok (iter_slp_ok P c k) c
    end.

  (** [slp_ok] is monotone in the precondition: starting from more states can
      only reach more.  (An annotated loop is degenerate — its post is the
      annotation, which does not mention [P] at all.) *)
  Lemma slp_ok_mono: forall c (P P': assertion),
    (P -->> P') -> (slp_ok P c -->> slp_ok P' c).
  Proof.
    induction c as [ | | x a | x | b | c1 IH1 c2 IH2 | c1 IH1 c2 IH2 | ann body IHb ];
      intros P P' Hsub s H; cbn [slp_ok] in H |- *.
    - (* SKIP *) apply Hsub, H.
    - (* ERROR *) exact H.
    - (* ASSIGN *) destruct H as [Hdom [m [n [Hx [HP Ha]]]]].
      split; [ exact Hdom | ]. exists m, n.
      split; [ exact Hx | split; [ apply Hsub, HP | exact Ha ] ].
    - (* NONDET *) destruct H as [Hdom [m HP]].
      split; [ exact Hdom | ]. exists m. apply Hsub, HP.
    - (* ASSUME *) destruct H as [Hb HP]. split; [ exact Hb | apply Hsub, HP ].
    - (* SEQ *) exact (IH2 _ _ (IH1 _ _ Hsub) s H).
    - (* CHOICE *) destruct H as [H | H];
        [ left; exact (IH1 _ _ Hsub s H) | right; exact (IH2 _ _ Hsub s H) ].
    - (* CSTAR *)
      destruct ann as [Inv | ]; [ exact H | ].
      destruct H as [m Hm]. exists m. revert s Hm.
      induction m as [ | k IHk ]; intros s Hm; cbn in *;
        [ apply Hsub, Hm | exact (IHb _ _ IHk s Hm) ].
  Qed.

  (** The local fixpoint of the [CSTAR None] case is [iter_slp_ok]. *)
  Lemma slp_ok_cstar_none: forall P body s,
    slp_ok P (CSTAR None body) s <-> exists m, iter_slp_ok P body m s.
  Proof.
    intros P body s. cbn [slp_ok]. split; intros [m Hm]; exists m; revert s Hm;
      induction m as [ | k IH ]; intros s Hm; cbn in *; try exact Hm;
      [ exact (slp_ok_mono body _ _ IH s Hm) | exact (slp_ok_mono body _ _ IH s Hm) ].
  Qed.

(** Well-formedness of the loop annotations in [c].  An annotated loop owes
    the obligation that its invariant is actually reached; an unannotated one
    owes nothing beyond its body's own conditions. *)
Fixpoint vcond (P: assertion) (c: com) : Prop :=
  match c with
  | SKIP => True
  | ERROR => True
  | ASSUME _ => True
  | ASSIGN _ _ => True
  | NONDET _ => True
  | CHOICE c1 c2 => vcond P c1 /\ vcond P c2
  | SEQ c1 c2 => vcond P c1 /\ vcond (slp_ok P c1) c2
  | CSTAR (Some (AInv Inv)) body =>
      (Inv -->> (fun s => exists m, iter_slp_ok P body m s))
      /\ (forall m, vcond (iter_slp_ok P body m) body)
      /\ vcond Inv body
  | CSTAR (Some (AVar R)) body =>
      (* no coverage obligation here, unlike [AInv] — see [Imp.loopann] *)
      (R 0%nat -->> P)
      /\ (forall n, R (S n) -->> slp_ok (R n) body)
      /\ (forall m, vcond (iter_slp_ok P body m) body)
      /\ vcond (fun s => exists n, R n s) body
  | CSTAR None body =>
      (forall m, vcond (iter_slp_ok P body m) body)
      /\ vcond (slp_ok P (CSTAR None body)) body
  end.

  Definition vcgen (P: assertion) (c: com) (Q: postassertion) : Prop :=
    vcond P c /\ (Q --* sp P c).

  (** ** Rules for discharging [vcond] *)

  Lemma vcond_seq: forall P c1 c2,
    vcond P c1 -> vcond (slp_ok P c1) c2 -> vcond P (SEQ c1 c2).
  Proof. intros P c1 c2 H1 H2. exact (conj H1 H2). Qed.

  Lemma vcond_choice: forall P c1 c2,
    vcond P c1 -> vcond P c2 -> vcond P (CHOICE c1 c2).
  Proof. intros P c1 c2 H1 H2. exact (conj H1 H2). Qed.

  (** An unannotated loop over a body that is well-formed at every assertion —
      in particular any loop-free body — costs nothing at all. *)
  Lemma vcond_cstar_none: forall P body,
    (forall R, vcond R body) -> vcond P (CSTAR None body).
  Proof. intros P body H. split; [ intros m | ]; apply H. Qed.

  (** A *forwards variant* [R]: [R n] describes the states reachable after
      exactly [n] turns of the loop. *)
  Lemma iter_slp_ok_of_variant: forall (P: assertion) (body: com) (R: nat -> assertion),
    (R 0%nat -->> P) ->
    (forall n, R (S n) -->> slp_ok (R n) body) ->
    forall n, R n -->> iter_slp_ok P body n.
  Proof.
    intros P body R H0 HS n. induction n as [ | k IH ].
    - exact H0.
    - intros s Hs. cbn [iter_slp_ok].
      exact (slp_ok_mono body (R k) (iter_slp_ok P body k) IH s (HS k s Hs)).
  Qed.

  (** A variant annotation is legal as soon as its stages start inside [P]
      and step through the body. *)
  Lemma vcond_cstar_var: forall (P: assertion) (body: com) (R: nat -> assertion),
    (R 0%nat -->> P) ->
    (forall n, R (S n) -->> slp_ok (R n) body) ->
    (forall m, vcond (iter_slp_ok P body m) body) ->
    vcond (fun s => exists n, R n s) body ->
    vcond P (CSTAR (Some (AVar R)) body).
  Proof.
    intros P body R H0 HS Hiter Hbody.
    exact (conj H0 (conj HS (conj Hiter Hbody))).
  Qed.

  (** Hence the annotation rule: an annotation [Inv] is legal as soon as some
      forwards variant covers it. *)
  Lemma vcond_cstar_variant: forall (P Inv: assertion) (body: com) (R: nat -> assertion),
    (R 0%nat -->> P) ->
    (forall n, R (S n) -->> slp_ok (R n) body) ->
    (Inv -->> (fun s => exists n, R n s)) ->
    (forall m, vcond (iter_slp_ok P body m) body) ->
    vcond Inv body ->
    vcond P (CSTAR (Some (AInv Inv)) body).
  Proof.
    intros P Inv body R H0 HS Hcover Hiter Hinv.
    split; [ | exact (conj Hiter Hinv) ].
    intros s Hs. destruct (Hcover s Hs) as [n Hn].
    exists n. exact (iter_slp_ok_of_variant P body R H0 HS n s Hn).
  Qed.

  (* We reuse the semantic strongest posts [spo]/[spe] and the derivability
     result [sp_der] from the completeness development. *)
  Import IncCompleteness.

  (** [spo] is monotone in its precondition. *)
  Lemma spo_mono: forall c (P P': assertion),
    (forall s, P s -> P' s) -> forall s, spo c P s -> spo c P' s.
  Proof.
    intros c P P' Hsub s [s0 [HP HX]]. exists s0. split; [ apply Hsub; exact HP | exact HX ].
  Qed.

  Lemma spo_iter_star: forall c P m s,
    spo_iter c P m s -> exists s0, P s0 /\ star (step_iter c) s0 s.
  Proof.
    intros c P m. induction m as [|k IH]; intros s Hit.
    - exists s. split; [ exact Hit | apply star_refl ].
    - cbn [spo_iter] in Hit. unfold spo in Hit. destruct Hit as [smid [Hk HX]].
      destruct (IH smid Hk) as [s0 [HP HSt]].
      exists s0. split; [ exact HP | ].
      eapply star_trans; [ exact HSt | apply star_one; unfold step_iter; exact HX ].
  Qed.

  Lemma spo_iter_to_cstar: forall ann c P m s,
    spo_iter c P m s -> spo (Imp.CSTAR ann c) P s.
  Proof.
    intros ann c P m s Hit. destruct (spo_iter_star c P m s Hit) as [s0 [HP HSt]].
    unfold spo. exists s0. split; [ exact HP | apply cexec_cstar_of_star; exact HSt ].
  Qed.

  (** The syntactic iterates under-approximate the semantic ones.  Stated
      before [slp_ok_spo] and proved together with it by a nested induction. *)
  Lemma slp_ok_spo_and_iter: forall c P, vcond P c -> forall s, slp_ok P c s -> spo c P s.
  Proof.
    induction c as [ | | x a | x | b | c1 IHc1 c2 IHc2 | c1 IHc1 c2 IHc2 | ann body IHbody ];
      intros P Hv s Hslp.
    - (* SKIP *) cbn [slp_ok] in Hslp. unfold spo. exists s. split; [ exact Hslp | apply cexec_skip ].
    - (* ERROR *) cbn [slp_ok] in Hslp. contradiction.
    - (* ASSIGN x a *) cbn [slp_ok] in Hslp.
      destruct Hslp as [Hdom [m [n [Heq_x [HP Heq_a]]]]].
      unfold aequal in Heq_x, Heq_a. cbn in Heq_x, Heq_a.
      unfold spo. exists (update x m s). split; [ exact HP | ].
      replace s with (update x (aeval a (update x m s)) (update x m s)) at 2.
      + apply cexec_assign.
      + rewrite Heq_a, update_shadow, <- Heq_x. apply update_get. exact Hdom.
    - (* NONDET x *) cbn [slp_ok] in Hslp.
      destruct Hslp as [Hdom [m HQ]].
      unfold spo. exists (update x m s). split.
      + exact HQ.
      + replace s with (update x (s x) (update x m s)) at 2.
        * apply cexec_nondet.
        * rewrite update_shadow. apply update_get. exact Hdom.
    - (* ASSUME b *) cbn [slp_ok] in Hslp.
      destruct Hslp as [Hb HP].
      unfold spo. exists s. split; [ exact HP | apply cexec_assume; exact Hb ].
    - (* SEQ c1 c2 *) cbn [slp_ok] in Hslp. cbn [vcond] in Hv. destruct Hv as [Hv1 Hv2].
      pose proof (IHc2 (slp_ok P c1) Hv2 s Hslp) as Hspo2. unfold spo in Hspo2.
      destruct Hspo2 as [smid [Hmid HX2]].
      pose proof (IHc1 P Hv1 smid Hmid) as Hspo1. unfold spo in Hspo1.
      destruct Hspo1 as [s0 [HP HX1]].
      unfold spo. exists s0. split; [ exact HP | eapply cexec_seq; [ exact HX1 | exact HX2 ] ].
    - (* CHOICE c1 c2 *) cbn [slp_ok] in Hslp. cbn [vcond] in Hv. destruct Hv as [Hv1 Hv2].
      destruct Hslp as [H1 | H2].
      + pose proof (IHc1 P Hv1 s H1) as Hspo. unfold spo in Hspo. destruct Hspo as [s0 [HP HX]].
        unfold spo. exists s0. split; [ exact HP | apply cexec_choice_left; exact HX ].
      + pose proof (IHc2 P Hv2 s H2) as Hspo. unfold spo in Hspo. destruct Hspo as [s0 [HP HX]].
        unfold spo. exists s0. split; [ exact HP | apply cexec_choice_right; exact HX ].
    - (* CSTAR *)
      assert (Hsub: forall (Hiter: forall m, vcond (iter_slp_ok P body m) body) k s',
                iter_slp_ok P body k s' -> spo_iter body P k s').
      { intros Hiter k. induction k as [|j IHj]; intros s' Hk.
        - exact Hk.
        - cbn [iter_slp_ok] in Hk. cbn [spo_iter].
          pose proof (IHbody (iter_slp_ok P body j) (Hiter j) s' Hk) as Hspo.
          eapply spo_mono; [ exact IHj | exact Hspo ]. }
      destruct ann as [[Inv | R] | ].
      + cbn [slp_ok] in Hslp. cbn [vcond] in Hv.
        destruct Hv as [Hinv [Hiter Hinvbody]].
        apply Hinv in Hslp. destruct Hslp as [m Hm].
        apply (spo_iter_to_cstar _ body P m s). apply (Hsub Hiter). exact Hm.
      + cbn [slp_ok] in Hslp. cbn [vcond] in Hv.
        destruct Hv as [H0 [HS [Hiter _]]].
        destruct Hslp as [n Hn].
        apply (spo_iter_to_cstar _ body P n s). apply (Hsub Hiter).
        exact (iter_slp_ok_of_variant P body R H0 HS n s Hn).
      + cbn [vcond] in Hv. destruct Hv as [Hiter _].
        apply slp_ok_cstar_none in Hslp. destruct Hslp as [m Hm].
        apply (spo_iter_to_cstar None body P m s). apply (Hsub Hiter). exact Hm.
  Qed.

  Definition slp_ok_spo := slp_ok_spo_and_iter.

  (** The [Hsub] step above, as a standalone lemma. *)
  Lemma iter_slp_ok_spo_iter: forall body P m s,
    (forall k, vcond (iter_slp_ok P body k) body) ->
    iter_slp_ok P body m s -> spo_iter body P m s.
  Proof.
    intros body P m. induction m as [|j IH]; intros s Hv Hm.
    - exact Hm.
    - cbn [iter_slp_ok] in Hm. cbn [spo_iter].
      pose proof (slp_ok_spo body (iter_slp_ok P body j) (Hv j) s Hm) as Hspo.
      eapply spo_mono; [ | exact Hspo ].
      intros s' Hs'. apply IH; [ exact Hv | exact Hs' ].
  Qed.

  (** The syntactic [err]-post under-approximates the semantic one. *)
  Lemma slp_err_spe: forall c P, vcond P c -> forall s, slp_err P c s -> spe c P s.
  Proof.
    induction c as [ | | x a | x | b | c1 IHc1 c2 IHc2 | c1 IHc1 c2 IHc2 | ann body IHbody ];
      intros P Hv s Hslp.
    - (* SKIP *) cbn [slp_err] in Hslp. contradiction.
    - (* ERROR *) cbn [slp_err] in Hslp. unfold spe. exists s. split; [ exact Hslp | apply cexec_error ].
    - (* ASSIGN *) cbn [slp_err] in Hslp. contradiction.
    - (* NONDET *) cbn [slp_err] in Hslp. contradiction.
    - (* ASSUME *) cbn [slp_err] in Hslp. contradiction.
    - (* SEQ c1 c2 *) cbn [slp_err] in Hslp. cbn [vcond] in Hv. destruct Hv as [Hv1 Hv2].
      destruct Hslp as [H1 | H2].
      + pose proof (IHc1 P Hv1 s H1) as Hspe. unfold spe in Hspe. destruct Hspe as [s0 [HP HX]].
        unfold spe. exists s0. split; [ exact HP | apply cexec_seq_error; exact HX ].
      + pose proof (IHc2 (slp_ok P c1) Hv2 s H2) as Hspe. unfold spe in Hspe.
        destruct Hspe as [smid [Hmid HX2]].
        pose proof (slp_ok_spo c1 P Hv1 smid Hmid) as Hspo. unfold spo in Hspo.
        destruct Hspo as [s0 [HP HX1]].
        unfold spe. exists s0. split; [ exact HP | eapply cexec_seq_error_right; [ exact HX1 | exact HX2 ] ].
    - (* CHOICE c1 c2 *) cbn [slp_err] in Hslp. cbn [vcond] in Hv. destruct Hv as [Hv1 Hv2].
      destruct Hslp as [H1 | H2].
      + pose proof (IHc1 P Hv1 s H1) as Hspe. unfold spe in Hspe. destruct Hspe as [s0 [HP HX]].
        unfold spe. exists s0. split; [ exact HP | apply cexec_choice_left; exact HX ].
      + pose proof (IHc2 P Hv2 s H2) as Hspe. unfold spe in Hspe. destruct Hspe as [s0 [HP HX]].
        unfold spe. exists s0. split; [ exact HP | apply cexec_choice_right; exact HX ].
    - (* CSTAR: the body faults at a state the loop reaches *)
      cbn [slp_err] in Hslp.
      assert (Hbody: vcond (slp_ok P (CSTAR ann body)) body).
      { destruct ann as [[Inv | R] | ]; cbn [vcond] in Hv.
        - destruct Hv as [_ [_ Hib]]. exact Hib.
        - destruct Hv as [_ [_ [_ Hib]]]. exact Hib.
        - destruct Hv as [_ Hib]. exact Hib. }
      pose proof (IHbody _ Hbody s Hslp) as Hspe. unfold spe in Hspe.
      destruct Hspe as [s1 [Hreach HX1]].
      pose proof (slp_ok_spo (CSTAR ann body) P Hv s1 Hreach) as Hspo.
      unfold spo in Hspo. destruct Hspo as [s0 [HP HStar]].
      unfold spe. exists s0. split; [ exact HP | ].
      apply cexec_cstar_err_iff. exists s1.
      split; [ exact (proj1 (cexec_cstar_iff_star ann body s0 s1) HStar) | exact HX1 ].
  Qed.

  (** The [ok]-post is a derivable incorrectness post. *)
  Lemma slp_ok_sound: forall c P, vcond P c -> ⟦ P ⟧ c ⟦ ok ↑ slp_ok P c ⟧.
  Proof.
    intros c P Hv.
    destruct (sp_der c P) as [Hok _].
    eapply Inc_post_weaken; [ exact Hok | ].
    intros r; destruct r as [s|s]; cbn;
      [ intros Hslp; exact (slp_ok_spo c P Hv s Hslp) | tauto ].
  Qed.

  Lemma slp_err_sound: forall c P, vcond P c -> ⟦ P ⟧ c ⟦ err ↑ slp_err P c ⟧.
  Proof.
    intros c P Hv.
    destruct (sp_der c P) as [_ Herr].
    eapply Inc_post_weaken; [ exact Herr | ].
    intros r; destruct r as [s|s]; cbn;
      [ tauto | intros Hslp; exact (slp_err_spe c P Hv s Hslp) ].
  Qed.

  Lemma sp_sound: forall c P,
    vcond P c -> ⟦ P ⟧ c ⟦ sp P c ⟧.
  Proof.
    intros c P Hv.
    exact (Inc_combine_ok_err P c (slp_ok P c) (slp_err P c)
             (slp_ok_sound c P Hv) (slp_err_sound c P Hv)).
  Qed.

  Theorem vcgen_sound: forall P c Q,
  vcgen P c Q -> ⟦ P ⟧ c ⟦ Q ⟧.
  Proof.
    intros P c Q [Hv Himp].
    eapply Inc_post_weaken; [ exact (sp_sound c P Hv) | exact Himp ].
  Qed.

  (** The entry point for verifying a concrete program: what remains is
      [vcgen] — the loop side conditions plus a post inclusion, both pure
      assertion-level goals with no [cexec] reasoning left in them.  There is
      no [erase] premise any more: there is only one syntax. *)
  Corollary vcgen_valid: forall P (c: com) (Q: postassertion),
    vcgen P c Q ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧.
  Proof.
    intros P c Q HV.
    apply IncSoundness.Inc_triple_sound_gen, vcgen_sound, HV.
  Qed.

  (** The same for the bare program.  [unannot c] reduces to it, so [apply]
      sees the two as equal. *)
  Corollary vcgen_valid_unannot: forall P (c: com) (Q: postassertion),
    vcgen P c Q ->
    ⟦⟦ P ⟧⟧ (unannot c) ⟦⟦ Q ⟧⟧.
  Proof.
    intros P c Q HV. apply IncTriple_unannot, vcgen_valid, HV.
  Qed.

End SP.

(** The loop notations — [c ★], [c ★ ⟨ I ⟩], [c ★ ⟨| R |⟩] — are declared once
    in [Imp.v]. *)

