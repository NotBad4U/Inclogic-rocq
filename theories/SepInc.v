From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat.
From mathcomp Require Import ssralg ssrnum monoid order finmap finset.

From IncLogic Require Import State.

Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope imp_scope.
Local Open Scope state_scope.

Notation "x ∈ A" := (x \in A) (at level 70, no associativity).
Notation "x ∉ A" := (x \notin A) (at level 70, no associativity).

Section Vars.
Context {varType : choiceType} {valType : monoidType} {op : Type}.
Context {loc : {fset valType}}.

Abbreviation expr := (expr varType valType op).
Abbreviation com := (com varType valType op).

(* Returns the set of free variables in an expression *)
Fixpoint efv (e : expr) : {fset varType} :=
  match e with
  | Deref e'      => efv e'
  | Binop _ e1 e2 => efv e1 `|` efv e2
  | Var x         => [fset x]
  | Const _       => fset0
  end.

(* Return the free variable of a command *)
Fixpoint cfv (c : com) : {fset varType} :=
  match c with
  | Skip | Error    => fset0
  | AssignStore x e => x |` efv e
  | AssignHeap a e  => efv a `|` efv e
  | Nondet x | Alloc x | Free x => [fset x]
  | Assume e        => efv e
  | Seq c1 c2 | Choice c1 c2 => cfv c1 `|` cfv c2
  | Local x c'      => cfv c' `\ x
  | Star c'         => cfv c'
  end.

(* Returns the set of (program) variables modified by a command C *)
Fixpoint cmod (c : com) : {fset varType} :=
  match c with
  | AssignStore x _ | Nondet x | Alloc x => [fset x]
  | Seq c1 c2 | Choice c1 c2 => cmod c1 `|` cmod c2
  | Local x c'      => cmod c' `\ x
  | Star c'         => cmod c'
  | _               => fset0
  end.


(* Every variable a command modifies is also free in it *)
Lemma cmod_fv c : cmod c `<=` cfv c.
Proof.
  elim: c => /= [|x e|a e|x|e||c1 IH1 c2 IH2|x c IH|c1 IH1 c2 IH2|c IH|x|x].
  all: try exact: fsub0set; try exact: fsubset_refl.
  all: try exact: fsetUSS; try exact: fsetSD; try assumption.
  by rewrite fsub1set fset1U1.
Qed.

Lemma in_cmod_seq x c1 c2 : (x ∈ cmod (Seq c1 c2)) = (x ∈ cmod c1) || (x ∈ cmod c2).
Proof. by rewrite /= in_fsetU. Qed.

Corollary notin_cmod x c : x ∉ cfv c -> x ∉ cmod c.
Proof. by apply: contra; apply/fsubsetP/cmod_fv. Qed.

(** Syntactically, an assertion [p] is independent from a set [vars] of
    variables if none of the variables in [vars] is mentioned in [P]. *)
Definition indep (vars : {fset varType}) (p : sprop varType valType loc) : Prop :=
  forall (s s' : store varType valType) h,
    (forall x, x ∉ vars -> s.[? x] = s'.[? x]) -> p s h -> p s' h.

Lemma indep_sub vars1 vars2 p : vars1 `<=` vars2 -> indep vars2 p -> indep vars1 p.
Proof.
    move=> /fsubsetP XY Hp s s' h E; apply: Hp => x xY; apply: E.
    by apply: contra xY; exact: XY.
Qed.

(*
    Common interface for free variables.

    The paper overload the notation [fv] for expressions, commands and assertions.
    We use the typeclass [Freevar] to also follow the approach of the paper.
 *)
Class Freevar (T : Type) := freevar : {fset varType} -> T -> Prop.

#[global] Instance expr_Fresh : Freevar expr := fun X e => X `&` efv e = fset0.
#[global] Instance com_Fresh : Freevar com := fun X c => X `&` cfv c = fset0.
#[global] Instance sprop_Fresh : Freevar (sprop varType valType loc) := indep.

End Vars.

Notation "'mod' ( c )" := (cmod c) (at level 0, format "'mod' ( c )").

Notation "X ∩ 'fv' t = ∅" := (freevar X t) (at level 70, t at level 9). (* TODO:  should be a more general notation i.e = Y and not just ∅ ? *)
Notation "x ∉ 'fv' t" := (freevar [fset x] t) (at level 70, t at level 9).

Reserved Notation "⟦ P ⟧ c ⟦ ε ↑ Q ⟧" (at level 0, P custom ss at level 99,
  c custom hcom at level 99, ε at level 0, Q custom ss at level 99).

Section Rules.
Context (varType : choiceType) (valType : monoidType) (loc : {fset valType}).
Context (op : Type) {D : Denote op valType}.

Abbreviation expr := (expr varType valType op).
Abbreviation com := (com varType valType op).
Abbreviation state := (state varType valType loc).
Abbreviation result := (result varType valType loc).
Abbreviation assertion := (sprop varType valType loc).
Abbreviation null := (null valType).
Abbreviation pts_any := (pts_any varType valType loc).
Abbreviation etrue := (etrue varType valType loc op).

(* Fig. 5. The ISL proof rules where x and x' are distinct variables *)
Inductive SInc_triple: assertion -> com -> exit -> assertion -> Prop :=
| sinc_skip_ok :
    (*───────────────────────── (Skip) *)
    ⟦ emp ⟧ skip ⟦ ok ↑ emp ⟧
| sinc_assign x x' e :
    x != x' ->
    (*───────────────────────── (Assign) *)
    ⟦ x ≡ x' ⟧ `x := {e}
    ⟦ ok ↑ x ≡ {e.[Var x' // x]} ⟧
| sinc_havoc x x' any :
    x != x' ->
    (*───────────────────────── (Havoc) *)
    ⟦ x ≡ x' ⟧ nondet x
    ⟦ ok ↑ x ≡ {Const any} ⟧
| sinc_assume b :
    (*───────────────────────── (Assume) *)
    ⟦ emp ⟧ assume {b} ⟦ ok ↑ {etrue b} ⟧
| sinc_error :
    (*───────────────────────── (Error) *)
    ⟦ emp ⟧ error ⟦ er ↑ emp ⟧
| sinc_seq1 P Q c1 c2 :
    ⟦ P ⟧ c1 ⟦ er ↑ Q ⟧ ->
    (*───────────────────────── (Seq1) *)
    ⟦ P ⟧ c1 ;; c2 ⟦ er ↑ Q ⟧
| sinc_seq2 P R Q c1 c2 ε :
    ⟦ P ⟧ c1 ⟦ ok ↑ R ⟧ ->
    ⟦ R ⟧ c2 ⟦ ε ↑ Q ⟧ ->
    (*───────────────────────── (Seq2) *)
    ⟦ P ⟧ c1 ;; c2 ⟦ ε ↑ Q ⟧
| sinc_loop1 P c :
    (*───────────────────────── (Loop1) *)
    ⟦ P ⟧ c ★ ⟦ ok ↑ P ⟧
| sinc_loop2 P Q c ε :
    ⟦ P ⟧ c ★ ;; c ⟦ ε ↑ Q ⟧ ->
    (*───────────────────────── (Loop2) *)
    ⟦ P ⟧ c ★ ⟦ ε ↑ Q ⟧
| sinc_choice_l P Q c1 c2 ε :
    ⟦ P ⟧ c1 ⟦ ε ↑ Q ⟧ ->
    (*───────────────────────── (Choice, left) *)
    ⟦ P ⟧ c1 ⊕ c2 ⟦ ε ↑ Q ⟧
| sinc_choice_r P Q c1 c2 ε :
    ⟦ P ⟧ c2 ⟦ ε ↑ Q ⟧ ->
    (*───────────────────────── (Choice, right) *)
    ⟦ P ⟧ c1 ⊕ c2 ⟦ ε ↑ Q ⟧
| sinc_cons P P' Q Q' c ε :
    P' --> P ->
    ⟦ P' ⟧ c ⟦ ε ↑ Q' ⟧ ->
    Q --> Q' ->
    (*───────────────────────── (Cons) *)
    ⟦ P ⟧ c ⟦ ε ↑ Q ⟧
| sinc_disj P1 P2 Q1 Q2 c ε :
    ⟦ P1 ⟧ c ⟦ ε ↑ Q1 ⟧ ->
    ⟦ P2 ⟧ c ⟦ ε ↑ Q2 ⟧ ->
    (*───────────────────────── (Disj) *)
    ⟦ P1 \\// P2 ⟧ c ⟦ ε ↑ Q1 \\// Q2 ⟧
| sinc_subst P Q c ε x y :
    ⟦ P ⟧ c ⟦ ε ↑ Q ⟧ ->
    y ∉ fv P -> y ∉ fv c -> y ∉ fv Q ->
    (*───────────────────────── (Subst) *)
    ⟦ P[y/x] ⟧ c[y/x] ⟦ ε ↑ Q[y/x] ⟧
| sinc_exist x P Q c ε :
    x ∉ fv c ->
    ⟦ P ⟧ c ⟦ ε ↑ Q ⟧ ->
    (*───────────────────────── (Exist) *)
    ⟦ ∃ x, P ⟧ c ⟦ ε ↑ ∃ x, Q ⟧
| sinc_local x P Q c ε :
    ⟦ P ⟧ c ⟦ ε ↑ Q ⟧ ->
    (*───────────────────────── (Local) *)
    ⟦ ∃ x, P ⟧ local x in c ⟦ ε ↑ ∃ x, Q ⟧
| sinc_frame P Q R c ε :
    mod(c) ∩ fv R = ∅ ->
    ⟦ P ⟧ c ⟦ ε ↑ Q ⟧ ->
    (*───────────────────────── (Frame) *)
    ⟦ P ★ R ⟧ c ⟦ ε ↑ Q ★ R ⟧
| sinc_alloc1 x x' :
    x != x' ->
    (*───────────────────────── (Alloc1) *)
    ⟦ x ≡ x' ⟧ alloc x ⟦ ok ↑ x ↦ - ⟧
| sinc_alloc2 x x' y :
    x != x' -> x != y ->
    (*───────────────────────── (Alloc2) *)
    ⟦ x ≡ x' ★ y ↦̸ ⟧ alloc x
    ⟦ ok ↑ x ≡ y ★ y ↦ - ⟧
| sinc_free x y :
    (*───────────────────────── (Free) *)
    ⟦ x ↦ y ⟧ free x ⟦ ok ↑ x ↦̸ ⟧
| sinc_free_er x :
    (*───────────────────────── (FreeEr) *)
    ⟦ x ↦̸ ⟧ free x ⟦ er ↑ x ↦̸ ⟧
| sinc_free_null x :
    (*───────────────────────── (FreeNull) *)
    ⟦ x ≡ {Const null} ⟧ free x
    ⟦ er ↑ x ≡ {Const null} ⟧
| sinc_load x x' y z :
    x != x' -> x != y -> x != z ->
    (*───────────────────────── (Load) *)
    ⟦ x ≡ x' ★ y ↦ z ⟧ `x := [y]
    ⟦ ok ↑ x ≡ z ★ y ↦ z ⟧
| sinc_load_er x y :
    (*───────────────────────── (LoadEr) *)
    ⟦ y ↦̸ ⟧ `x := [y] ⟦ er ↑ y ↦̸ ⟧
| sinc_load_null x y :
    (*───────────────────────── (LoadNull) *)
    ⟦ y ≡ {Const null} ⟧ `x := [y]
    ⟦ er ↑ y ≡ {Const null} ⟧
| sinc_store x y z :
    (*───────────────────────── (Store) *)
    ⟦ x ↦ z ⟧ [x] := y ⟦ ok ↑ x ↦ y ⟧
| sinc_store_er x y :
    (*───────────────────────── (StoreEr) *)
    ⟦ x ↦̸ ⟧ [x] := y ⟦ er ↑ x ↦̸ ⟧
| sinc_store_null x y :
    (*───────────────────────── (StoreNull) *)
    ⟦ x ≡ {Const null} ⟧ [x] := y
    ⟦ er ↑ x ≡ {Const null} ⟧
where "⟦ P ⟧ c ⟦ ε ↑ Q ⟧" := (SInc_triple P c ε Q).

End Rules.

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

Section Semantics.
Context (varType : choiceType) (valType : monoidType) (loc : {fset valType}).
Context (op : Type) {D : Denote op valType}.

(* Locations are values too so we need this hypothesis for rules such as LoadNull *)
Hypothesis null_notin_loc : null valType ∉ loc.

Abbreviation expr := (expr varType valType op).
Abbreviation com := (com varType valType op).
Abbreviation state := (state varType valType loc).
Abbreviation result := (result varType valType loc).
Abbreviation assertion := (sprop varType valType loc).
Abbreviation cexec := (cexec varType valType loc op).
Abbreviation etrue := (etrue varType valType loc op).
Abbreviation null := (null valType).

(* The paper's [⊨ [p] C [ε: q]]: every state in [q] is reached, with exit
   [ε], from some state in [p]. *)
Definition SInc_triple_sem (P: assertion) (c: com) (ε: exit) (Q: assertion) : Prop :=
  forall (σ: state), Q σ.1 σ.2 -> exists (s: state), P s.1 s.2 /\ cexec s c (ε, σ).

Notation "⟦⟦ P ⟧⟧ c ⟦⟦ ε ↑ Q ⟧⟧" := (SInc_triple_sem P c ε Q)
  (at level 0, P custom ss at level 99,
  c custom hcom at level 99, ε at level 0, Q custom ss at level 99).

Lemma sinc_sem_skip : ⟦⟦ emp ⟧⟧ skip ⟦⟦ ok ↑ emp ⟧⟧.
Proof. by move=> σ Q; exists σ; split; last constructor. Qed.

Lemma sinc_sem_assign: forall x x' e,
    x != x' ->
    ⟦⟦ x ≡ x' ⟧⟧ `x := {e}
    ⟦⟦ ok ↑ x ≡ {e.[Var x' // x]} ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_havoc: forall x x' v,
    x != x' ->
    ⟦⟦ x ≡ x' ⟧⟧ nondet x
    ⟦⟦ ok ↑ x ≡ {Const v} ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_assume: forall b,
    ⟦⟦ emp ⟧⟧ assume {b}
    ⟦⟦ ok ↑ {etrue b} ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_error:
    ⟦⟦ emp ⟧⟧ error
    ⟦⟦ er ↑ emp ⟧⟧.
Proof.
Admitted.


Lemma sinc_sem_seq1: forall P c1 c2 Q,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ er ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c1 ;; c2 ⟦⟦ er ↑ Q ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_seq2: forall P c1 c2 R Q ε,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ok ↑ R ⟧⟧ ->
    ⟦⟦ R ⟧⟧ c2 ⟦⟦ ε ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c1 ;; c2 ⟦⟦ ε ↑ Q ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_loop1: forall P c, ⟦⟦ P ⟧⟧ c ★ ⟦⟦ ok ↑ P ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_loop2: forall P Q c ε,
    ⟦⟦ P ⟧⟧ c ★ ;; c ⟦⟦ ε ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c ★ ⟦⟦ ε ↑ Q ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_exist: forall (x: varType) P Q c ε,
    x ∉ fv c ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ ε ↑ Q ⟧⟧ ->
    ⟦⟦ ∃ x, P ⟧⟧ c ⟦⟦ ε ↑ ∃ x, Q ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_choice1: forall P c1 c2 Q ε,
    ⟦⟦ P ⟧⟧ c1 ⟦⟦ ε ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c1 ⊕ c2 ⟦⟦ ε ↑ Q ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_choice2: forall P c1 c2 Q ε,
    ⟦⟦ P ⟧⟧ c2 ⟦⟦ ε ↑ Q ⟧⟧ ->
    ⟦⟦ P ⟧⟧ c1 ⊕ c2 ⟦⟦ ε ↑ Q ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_cons: forall P P' Q Q' c ε,
    P' --> P ->
    ⟦⟦ P' ⟧⟧ c ⟦⟦ ε ↑ Q' ⟧⟧ ->
    Q --> Q' ->
    ⟦⟦ P ⟧⟧ c ⟦⟦ ε ↑ Q ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_disj: forall P1 P2 Q1 Q2 c ε,
    ⟦⟦ P1 ⟧⟧ c ⟦⟦ ε ↑ Q1 ⟧⟧ ->
    ⟦⟦ P2 ⟧⟧ c ⟦⟦ ε ↑ Q2 ⟧⟧ ->
    ⟦⟦ P1 \\// P2 ⟧⟧ c ⟦⟦ ε ↑ Q1 \\// Q2 ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_subst: forall P c Q ε x y,
    ⟦⟦ P ⟧⟧ c ⟦⟦ ε ↑ Q ⟧⟧ ->
    y ∉ fv P -> y ∉ fv c -> y ∉ fv Q ->
    ⟦⟦ P[y/x] ⟧⟧ c[y/x] ⟦⟦ ε ↑ Q[y/x] ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_local: forall x P Q c ε,
    ⟦⟦ P ⟧⟧ c ⟦⟦ ε ↑ Q ⟧⟧ ->
    ⟦⟦ ∃ x, P ⟧⟧ local x in c ⟦⟦ ε ↑ ∃ x, Q ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_frame: forall P Q R c ε,
    ⟦⟦ P ⟧⟧ c ⟦⟦ ε ↑ Q ⟧⟧ ->
    mod(c) ∩ fv R = ∅ ->
    ⟦⟦ P ★ R ⟧⟧ c ⟦⟦ ε ↑ Q ★ R ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_alloc1: forall x x',
    x != x' -> 
    ⟦⟦ x ≡ x' ⟧⟧ alloc x ⟦⟦ ok ↑ x ↦ - ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_alloc2: forall x x' y,
     x != x' -> x != y ->
    ⟦⟦ x ≡ x' ★ y ↦̸ ⟧⟧ alloc x ⟦⟦ ok ↑ x ≡ y ★ y ↦ - ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_free: forall x e,
    ⟦⟦ x ↦ e ⟧⟧ free x ⟦⟦ ok ↑ x ↦̸ ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_freeEr: forall x,
    ⟦⟦ x ↦̸ ⟧⟧ free x ⟦⟦ er ↑ x ↦̸ ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_free_null: forall x,
    ⟦⟦ x ≡ {Const null} ⟧⟧ free x ⟦⟦ er ↑ x ≡ {Const null} ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_load: forall x x' y z,
    x != x' -> x != y -> x != z ->
    ⟦⟦ x ≡ x' ★ y ↦ z ⟧⟧ `x := [y] ⟦⟦ ok ↑ x ≡ z ★ y ↦ z ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_load_err: forall x  y,
    x != y -> 
    ⟦⟦ y ↦̸  ⟧⟧ `x := [y] ⟦⟦ er ↑ y ↦̸  ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_store: forall x y e,
    ⟦⟦ x ↦ e ⟧⟧ [x] := y ⟦⟦ ok ↑ x ↦ y ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_store_err: forall x y,
    ⟦⟦ x ↦̸  ⟧⟧ [x] := y ⟦⟦ er ↑ x ↦̸ ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_load_null: forall x y,
    ⟦⟦ y ≡ {Const null}  ⟧⟧ `x := [y] ⟦⟦ er ↑ y ≡ {Const null} ⟧⟧.
Proof.
Admitted.

Lemma sinc_sem_store_null: forall x y,
    ⟦⟦ x ≡ {Const null}  ⟧⟧ [x] := y ⟦⟦ er ↑ x ≡ {Const null} ⟧⟧.
Proof.
Admitted.

End Semantics.