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

(* Returns the set of free variables in *)
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

Notation "'mod' ( c )" := (cmod c) (at level 0, format "'mod' ( c )").


(* Since the paper combine fv for expr and cmd we define the [Class FreeVars] to unify the interface. *)
Class FreeVars (T : Type) (V : choiceType) := free_vars : T -> {fset V}.

#[global] Instance expr_FreeVars : FreeVars expr varType := efv.

#[global] Instance com_FreeVars : FreeVars com varType := cfv.

Notation "'fv' ( t )" := (free_vars t) (at level 0, format "'fv' ( t )").

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

(* Assertions are Rocq predicates, so their free variables cannot be computed. *)
Definition indep (X : {fset varType}) (p : sprop varType valType loc) : Prop :=
  forall (s s' : store varType valType) h,
    (forall x, x ∉ X -> s.[? x] = s'.[? x]) -> p s h -> p s' h.

Lemma indep_sub X Y p : X `<=` Y -> indep Y p -> indep X p.
Proof.
move=> /fsubsetP XY Hp s s' h E; apply: Hp => x xY; apply: E.
by apply: contra xY; exact: XY.
Qed.

Notation "X # p" := (indep X p) (at level 70, no associativity).

End Vars.
Reserved Notation "⟦ P ⟧ c ⟦ 'ok' ↑ Q ⟧" (at level 0, P custom ss at level 99,
  c custom hcom at level 99, Q custom ss at level 99).

Reserved Notation "⟦ P ⟧ c ⟦ 'err' ↑ Q ⟧" (at level 0, P custom ss at level 99,
  c custom hcom at level 99, Q custom ss at level 99).

Reserved Notation "⟦ P ⟧ c ⟦ 'ϵ' ↑ Q ⟧" (at level 0, P custom ss at level 99,
  c custom hcom at level 99, Q custom ss at level 99).

(* The ISL proof rules (Fig. 5 of the paper). As in [Section Prog] of
   [State.v], the abbreviations fix the parameters of the types from [State],
   so that [state], [result], ... are types again inside the section. *)
Section Rules.
Context (varType : choiceType) (valType : monoidType) (loc : {fset valType}).
Context (op : Type) (denote : op -> valType -> valType -> option valType).

Abbreviation expr := (expr varType valType op).
Abbreviation com := (com varType valType op).
Abbreviation state := (state varType valType loc).
Abbreviation result := (result varType valType loc).
Abbreviation assertion := (sprop varType valType loc).
Abbreviation postassertion := (postassertion varType valType loc).

(* The exit conditions of the paper, lifting an assertion on the final state
   to the [result] monad: [post_ok q] holds of the normal results whose state
   satisfies [q], [post_err q] of the erroneous ones, [post_eps q] of both. *)
Definition post_ok (q : assertion) : postassertion :=
  fun r => if r is RNormal σ then q σ.1 σ.2 else False.
Definition post_err (q : assertion) : postassertion :=
  fun r => if r is RError σ then q σ.1 σ.2 else False.
Definition post_eps (q : assertion) : postassertion :=
  fun r => match r with RNormal σ | RError σ => q σ.1 σ.2 end.

(* The assertion connectives of [State], at the parameters of the section. *)
Abbreviation eval := (eval_expr varType valType loc op denote).
Abbreviation null := (null valType).
Abbreviation pure := (pure varType valType loc).
Abbreviation pts_any := (pts_any varType valType loc).
Abbreviation aexist := (aexist varType valType loc).
Abbreviation aor := (aor varType valType loc).
Abbreviation aimp := (aimp varType valType loc).
Abbreviation pexist := (pexist varType valType loc).
Abbreviation por := (por varType valType loc).
Abbreviation pimp := (pimp varType valType loc).
Abbreviation pstar := (pstar varType valType loc).

(* Fig. 5. The ISL proof rules  *)
Inductive SInc_triple: assertion -> com -> postassertion -> Prop :=
| sinc_skip_ok :
    (*───────────────────────── (Skip) *)
    ⟦ emp ⟧ skip ⟦ ok ↑ emp ⟧
| sinc_assign x x' e :
    x != x' ->
    (*───────────────────────── (Assign) *)
    ⟦ {pure (fun σ => σ.1.[? x] = σ.1.[? x'])} ⟧ `x := {e}
    ⟦ ok ↑ {pure (fun σ => σ.1.[? x] = eval (esubst x (Var x') e) σ)} ⟧
| sinc_havoc x x' v :
    x != x' ->
    (*───────────────────────── (Havoc) *)
    ⟦ {pure (fun σ => σ.1.[? x] = σ.1.[? x'])} ⟧ nondet x
    ⟦ ok ↑ {pure (fun σ => σ.1.[? x] = Some v)} ⟧
| sinc_assume b :
    (*───────────────────────── (Assume) *)
    ⟦ emp ⟧ assume {b} ⟦ ok ↑ {pure (fun σ => eval b σ != Some null)} ⟧
| sinc_error :
    (*───────────────────────── (Error) *)
    ⟦ emp ⟧ error ⟦ err ↑ emp ⟧
| sinc_seq1 P Q c1 c2 :
    ⟦ {P} ⟧ {c1} ⟦ err ↑ {Q} ⟧ ->
    (*───────────────────────── (Seq1) *)
    ⟦ {P} ⟧ {c1} ;; {c2} ⟦ err ↑ {Q} ⟧
| sinc_seq2 P R Q c1 c2 :
    ⟦ {P} ⟧ {c1} ⟦ ok ↑ {R} ⟧ ->
    SInc_triple R c2 Q ->
    (*───────────────────────── (Seq2) *)
    SInc_triple P (Seq c1 c2) Q
| sinc_loop1 P c :
    (*───────────────────────── (Loop1) *)
    ⟦ {P} ⟧ {c} ★ ⟦ ok ↑ {P} ⟧
| sinc_loop2 P Q c :
    SInc_triple P (Seq (Star c) c) Q ->
    (*───────────────────────── (Loop2) *)
    SInc_triple P (Star c) Q
| sinc_choice_l P Q c1 c2 :
    SInc_triple P c1 Q ->
    (*───────────────────────── (Choice, left) *)
    SInc_triple P (Choice c1 c2) Q
| sinc_choice_r P Q c1 c2 :
    SInc_triple P c2 Q ->
    (*───────────────────────── (Choice, right) *)
    SInc_triple P (Choice c1 c2) Q
| sinc_cons P P' Q Q' c :
    aimp P' P ->
    SInc_triple P' c Q' ->
    pimp Q Q' ->
    (*───────────────────────── (Cons) *)
    SInc_triple P c Q
| sinc_disj P1 P2 Q1 Q2 c :
    SInc_triple P1 c Q1 ->
    SInc_triple P2 c Q2 ->
    (*───────────────────────── (Disj) *)
    SInc_triple (aor P1 P2) c (por Q1 Q2)
| sinc_exist x P Q c :
    x ∉ cfv c ->
    SInc_triple P c Q ->
    (*───────────────────────── (Exist) *)
    SInc_triple (aexist x P) c (pexist x Q)
| sinc_local x P Q c :
    SInc_triple P c Q ->
    (*───────────────────────── (Local) *)
    SInc_triple (aexist x P) (Local x c) (pexist x Q)
| sinc_frame P Q R c :
    indep (cmod c) R ->
    SInc_triple P c Q ->
    (*───────────────────────── (Frame) *)
    SInc_triple ⟦ {P} ★ {R} ⟧ c (pstar Q R)
| sinc_alloc1 x x' :
    x != x' ->
    (*───────────────────────── (Alloc1) *)
    ⟦ {pure (fun σ => σ.1.[? x] = σ.1.[? x'])} ⟧ alloc x ⟦ ok ↑ {pts_any x} ⟧
| sinc_alloc2 x x' y :
    x != x' -> x != y ->
    (*───────────────────────── (Alloc2) *)
    ⟦ {pure (fun σ => σ.1.[? x] = σ.1.[? x'])} ★ y ↦̸ ⟧ alloc x
    ⟦ ok ↑ {pure (fun σ => σ.1.[? x] = σ.1.[? y])} ★ {pts_any y} ⟧
| sinc_free x y :
    (*───────────────────────── (Free) *)
    ⟦ x ↦ y ⟧ free x ⟦ ok ↑ x ↦̸ ⟧
| sinc_free_er x :
    (*───────────────────────── (FreeEr) *)
    ⟦ x ↦̸ ⟧ free x ⟦ err ↑ x ↦̸ ⟧
| sinc_free_null x :
    null ∉ loc ->
    (*───────────────────────── (FreeNull) *)
    ⟦ {pure (fun σ => σ.1.[? x] = Some null)} ⟧ free x
    ⟦ err ↑ {pure (fun σ => σ.1.[? x] = Some null)} ⟧
| sinc_load x x' y z :
    x != x' -> x != y -> x != z ->
    (*───────────────────────── (Load) *)
    ⟦ {pure (fun σ => σ.1.[? x] = σ.1.[? x'])} ★ y ↦ z ⟧ `x := [y]
    ⟦ ok ↑ {pure (fun σ => σ.1.[? x] = σ.1.[? z])} ★ y ↦ z ⟧
| sinc_load_er x y :
    (*───────────────────────── (LoadEr) *)
    ⟦ y ↦̸ ⟧ `x := [y] ⟦ err ↑ y ↦̸ ⟧
| sinc_load_null x y :
    null ∉ loc ->
    (*───────────────────────── (LoadNull) *)
    ⟦ {pure (fun σ => σ.1.[? y] = Some null)} ⟧ `x := [y]
    ⟦ err ↑ {pure (fun σ => σ.1.[? y] = Some null)} ⟧
| sinc_store x y z :
    (*───────────────────────── (Store) *)
    ⟦ x ↦ z ⟧ [x] := y ⟦ ok ↑ x ↦ y ⟧
| sinc_store_er x y :
    (*───────────────────────── (StoreEr) *)
    ⟦ x ↦̸ ⟧ [x] := y ⟦ err ↑ x ↦̸ ⟧
| sinc_store_null x y :
    null ∉ loc ->
    (*───────────────────────── (StoreNull) *)
    ⟦ {pure (fun σ => σ.1.[? x] = Some null)} ⟧ [x] := y
    ⟦ err ↑ {pure (fun σ => σ.1.[? x] = Some null)} ⟧
where "⟦ P ⟧ c ⟦ 'ok' ↑ Q ⟧" := (SInc_triple P c (post_ok Q))
and "⟦ P ⟧ c ⟦ 'err' ↑ Q ⟧" := (SInc_triple P c (post_err Q))
and "⟦ P ⟧ c ⟦ 'ϵ' ↑ Q ⟧" := (SInc_triple P c (post_eps Q)).

End Rules.