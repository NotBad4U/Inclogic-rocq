From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat.
From mathcomp Require Import ssralg ssrnum monoid order finmap finset.
From Stdlib Require Import RelationClasses Morphisms Setoid.

Local Open Scope fset_scope.
Local Open Scope fmap_scope.

Notation "'olet' x ':=' e 'in' b" := (obind (fun x => b) e)
  (at level 200, x name, e at level 100, b at level 200, right associativity).

Section State.
Context (varType valType : choiceType).
Context (loc : {fset valType}).

Definition store := {fmap varType -> valType}.
Definition heap := {fmap loc -> valType}.

Definition sprop := store -> heap -> Prop.

Definition encapsulate (p : Prop) : sprop :=
  fun (s : store) (h : heap) => p /\ domf h = fset0.

Definition emp : sprop := encapsulate True.

Definition mapsto (e e' : varType) : sprop :=
  fun s h => exists l v, s.[? e] = Some (val l) /\ s.[? e'] = Some v
                       /\ domf h = [fset l] /\ h.[? l] = Some v.

Definition mapsnot (e : varType) : sprop :=
  fun s h => exists l, s.[? e] = Some (val l) /\ l \notin domf h.

Definition state := (store * heap)%type.

Definition sprod (sh1 sh2 : state) : option state :=
  if (sh1.1 == sh2.1) && [disjoint domf sh1.2 & domf sh2.2]
  then Some (sh1.1, sh1.2 + sh2.2)
  else None.

Definition hprod (p q : sprop) : sprop :=
  fun s h => exists sh1 sh2, sprod sh1 sh2 = Some (s, h) /\ (p s h) /\ (q s h).

End State.

(* The language is parametric in the binary operators [op] and their
   (partial) denotation. The concrete arithmetic is chosen only when the
   language is instantiated; see the [*Ops] sections below. *)
Section Prog.
Context (varType : choiceType) (valType : monoidType) (loc : {fset valType}).
Context (op : Type) (denote : op -> valType -> valType -> option valType).

Abbreviation store := (store varType valType).
Abbreviation heap := (heap valType loc).
Abbreviation sprop := (sprop varType valType loc).
Abbreviation state := (state varType valType loc).

Inductive expr :=
    Deref : expr -> expr
  | Binop : op -> expr -> expr -> expr
  | Var : varType -> expr
  | Const : valType -> expr.

Inductive com :=
    Skip : com
  | AssignStore : varType -> expr -> com
  | AssignHeap : expr -> expr -> com
  | Nondet : varType -> com
  | Assume : expr -> com
  | Error : com
  | Seq : com -> com -> com
  | Local : varType -> com -> com
  | Choice : com -> com -> com
  | Star : com -> com
  | Alloc : varType -> com
  | Free : varType -> com.


(*
  O'Hearn's _Derived Unrolling Rule_: iteration can execute its
  body [i] times, so a post may be assembled from the finite unrollings.

  Star^n :: com
  Star^0 = skip
  Star^i = c ;; c^(i-1)
*)
Definition star_n (n: nat) c : com := iter n (Seq c) Skip.

Fixpoint eval_expr (e : expr) (sh : state) : option valType :=
  match e with
  | Deref e' =>
      olet l := eval_expr e' sh in
      olet l' := insub l in
      sh.2.[? l']
  | Binop o e e' =>
      olet v := eval_expr e sh in
      olet v' := eval_expr e' sh in
      denote o v v'
  | Var x => sh.1.[? x]
  | Const v => Some v
  end.

(* Behave like a Either ADT and satisfy monadic laws *)
Inductive result : Type :=
| RNormal : state -> result
| RError  : state -> result.

Definition ret (s : state) : result := RNormal s.

Definition bind (r : result) (f : state -> result) : result :=
  match r with RNormal s => f s | RError s => RError s end.

Definition fmap (f : state -> state) (r : result) : result :=
  bind r (fun s => ret (f s)).

Lemma ret_bind s f : bind (ret s) f = f s.
Proof. by []. Qed.

Lemma bind_ret r : bind r ret = r.
Proof. by case: r. Qed.

Lemma bindA r f g : bind (bind r f) g = bind r (fun s => bind (f s) g).
Proof. by case: r. Qed.

Reserved Notation "st0 =[ c ]=> st1"
  (at level 40, c at level 99, st1 at level 39).

Definition null : valType := one.

Inductive cexec: state -> com -> result -> Prop :=
| cexec_skip: forall s,
  s =[ Skip ]=> RNormal s
| cexec_error: forall s,
  s =[ Error ]=> RError s
| cexec_assign_store: forall s x a,
  s =[ AssignStore x a ]=>
    if eval_expr a s is Some v then RNormal (s.1.[x <- v], s.2)
    else RError s
| cexec_assign_heap: forall s x y,
  s =[ AssignHeap x y ]=>
    if (olet l  := eval_expr x s in
        olet l' := insub l in
        olet v  := eval_expr y s in
        if l' \in domf s.2 then Some (s.1, s.2.[l' <- v]) else None)
      is Some s' then RNormal s' else RError s
| cexec_nondet: forall s x any,
  s =[ Nondet x ]=> RNormal (s.1.[x <- any], s.2)
| cexec_assume: forall s b,
  s =[ Assume b ]=> if eval_expr b s == Some null then RError s
                   else ret s
| cexec_seq: forall c1 c2 s s' r,
  s  =[ c1 ]=> RNormal s' ->
  s' =[ c2 ]=> r ->
  s  =[ Seq c1 c2 ]=> r
| cexec_seq_error: forall c1 c2 s sf,
  s  =[ c1 ]=> RError sf ->
  s  =[ Seq c1 c2 ]=> RError sf
| cexec_choice_left: forall s c1 c2 r,
  s =[ c1 ]=> r ->
  s =[ Choice c1 c2 ]=> r
| cexec_choice_right: forall s c1 c2 r,
  s =[ c2 ]=> r ->
  s =[ Choice c1 c2 ]=> r
| cexec_local: forall s r x c v, (* FIXME: why need the type on s ?? *)
  s =[ c ]=> r ->
  (s.1.[x <- v], s.2) =[ Local x c ]=> fmap (fun s' => (s'.1.[x <- v], s'.2)) r
(*
  [[C*]] = ⋃_i [[C^i]], with [[C^0]] = Skip and [[C^i+1]] = [[C ; C^i]] 
  It differ from the @Imp.v because IL allow loop to fail but SIL no. 
*)
| cexec_star: forall s c r n,
  s =[ iter n (Seq c) Skip ]=> r ->
  s =[ Star c ]=> r
| cexec_alloc: forall s x l any,
  l \notin domf s.2 ->
  s  =[ Alloc x ]=> RNormal (s.1.[x <- val l], s.2.[l <- any]) (* Following C malloc that put any value *)
| cexec_free: forall (s : state) x,
  s  =[ Free x ]=>
    if (olet v := s.1.[? x] in
        olet l := insub v in
        if l \in domf s.2 then Some (s.1, s.2.[~ l]) else None)
      is Some s' then RNormal s' else RError s
where "st0 =[ c ]=> st1" := (cexec st0 c st1).

(* [Free x] is deterministic: its only outcome is the one of [cexec_free]. *)
Lemma cexec_freeE (s : state) x r :
  s =[ Free x ]=> r ->
  r = if (olet v := s.1.[? x] in
          olet l := insub v in
          if l \in domf s.2 then Some (s.1, s.2.[~ l]) else None)
      is Some s' then RNormal s' else RError s.
Proof. by move=> H; inversion H. Qed.

Lemma free_dangling (s : state) x r :
  (forall v l, s.1.[? x] = Some v -> insub v = Some l -> l \notin domf s.2) ->
  s =[ Free x ]=> r <-> r = RError s.
Proof.
move=> Hd; split=> [/cexec_freeE ->|->]; last first.
  have := cexec_free s x.
  case Ex: s.1.[? x] => [v|] //=; case El: (insub v) => [l|] //=.
  by rewrite (negbTE (Hd _ _ Ex El)).
case Ex: s.1.[? x] => [v|] //=; case El: (insub v) => [l|] //=.
by rewrite (negbTE (Hd _ _ Ex El)).
Qed.

Lemma free_null (s : state) x r :
  null \notin loc -> s.1.[? x] = Some null ->
  s =[ Free x ]=> r <-> r = RError s.
Proof.
move=> Hnull Hx; apply: free_dangling => v l.
by rewrite Hx => -[<-]; rewrite insubN.
Qed.

Lemma free_unallocated_err (s : state) x (l : loc) r :
  s.1.[? x] = Some (val l) -> l \notin domf s.2 ->
  s =[ Free x ]=> r <-> r = RError s.
Proof.
move=> Hx Hl; apply: free_dangling => v l'.
by rewrite Hx => -[<-]; rewrite valK => -[<-].
Qed.

Lemma free_seq_error (s : state) x (l : loc) v c r :
  s.1.[? x] = Some (val l) -> s.2.[? l] = Some v ->
  (forall r', (s.1, s.2.[~ l]) =[ c ]=> r' <-> r' = RError (s.1, s.2.[~ l])) ->
  s =[ Seq (Free x) c ]=> r <-> r = RError (s.1, s.2.[~ l]).
Proof.
move=> Hx Hv H2; have Hl : l \in domf s.2 by rewrite -fndSome Hv.
have H1 : s =[ Free x ]=> RNormal (s.1, s.2.[~ l]).
  by have := cexec_free s x; rewrite Hx /= valK /= Hl.
split=> [H|->]; last by apply: cexec_seq H1 _; apply/H2.
inversion H as [| | | | | |c1 c2 s0 s' r' H1' H2'|c1 c2 s0 sf H1'| | | | | |];
  subst; move/cexec_freeE: H1'; rewrite Hx /= valK /= Hl // => -[Es].
by apply/H2; move: H2'; rewrite Es.
Qed.

Lemma double_free (s : state) x (l : loc) v r :
  s.1.[? x] = Some (val l) -> s.2.[? l] = Some v ->
  s =[ Seq (Free x) (Free x) ]=> r <-> r = RError (s.1, s.2.[~ l]).
Proof.
move=> Hx Hv; apply: (free_seq_error _ _ _ _ _ _ Hx Hv) => r'.
by apply: free_unallocated_err; [exact: Hx | exact/negbT/mem_remfF].
Qed.

Lemma write_unallocated (s : state) a e (l : loc) r :
  eval_expr a s = Some (val l) -> l \notin domf s.2 ->
  s =[ AssignHeap a e ]=> r <-> r = RError s.
Proof.
move=> Ha Hl; split=> [H|->]; [inversion H | have := cexec_assign_heap s a e];
  by rewrite Ha /= valK /=; case: eval_expr => //= v; rewrite (negbTE Hl).
Qed.

Lemma use_after_free (s : state) x (l : loc) v e r :
  s.1.[? x] = Some (val l) -> s.2.[? l] = Some v ->
  s =[ Seq (Free x) (AssignHeap (Var x) e) ]=> r <->
  r = RError (s.1, s.2.[~ l]).
Proof.
move=> Hx Hv; apply: (free_seq_error _ _ _ _ _ _ Hx Hv) => r'.
by apply: write_unallocated; [exact: Hx | exact/negbT/mem_remfF].
Qed.

(* x := malloc(); c, where c fails whenever x points to an allocated cell l,
   raising the error once l has been freed: the heap is then back to its
   initial content and x dangles at l. *)
Lemma alloc_seq_error (s : state) x c r :
  (forall (s' : state) (l : loc) v r', s'.1.[? x] = Some (val l) ->
     s'.2.[? l] = Some v ->
     s' =[ c ]=> r' <-> r' = RError (s'.1, s'.2.[~ l])) ->
  s =[ Seq (Alloc x) c ]=> r <->
  exists l : loc, l \notin domf s.2 /\ r = RError (s.1.[x <- val l], s.2).
Proof.
move=> Hc.
(* Whatever l and any Alloc x picked, the rest of the program errors. *)
have Hrun (l : loc) any r' : l \notin domf s.2 ->
    (s.1.[x <- val l], s.2.[l <- any]) =[ c ]=> r' <->
    r' = RError (s.1.[x <- val l], s.2).
  move=> Hl; rewrite (Hc _ l any).
  - by rewrite /= fnd_set eqxx.
  - by rewrite /= fnd_set eqxx.
  - by rewrite /= remf1_set eqxx remf1_id.
split=> [H|[l [Hl ->]]].
- inversion H as [| | | | | |c1 c2 s0 s' r' Ha H'|c1 c2 s0 sf Ha| | | | | |];
    subst; last by inversion Ha.
  inversion Ha as [| | | | | | | | | | | |? ? l any Hl|]; subst.
  by exists l; split=> //; apply/(Hrun _ any).
- by apply: cexec_seq (cexec_alloc _ _ _ null Hl) _; apply/Hrun.
Qed.

(* Double free: x := malloc(); free(x); free(x) always ends in an error,
   raised by the second free. *)
Corollary double_free_ret_error (s : state) x r :
  s =[ Seq (Alloc x) (Seq (Free x) (Free x)) ]=> r <->
  exists l : loc, l \notin domf s.2 /\ r = RError (s.1.[x <- val l], s.2).
Proof. by apply: alloc_seq_error => s' l v r'; exact: double_free. Qed.

(* Use after free: x := malloc(); free(x); *x := e always ends in an error,
   raised by the write. *)
Corollary use_after_free_ret_error (s : state) x e r :
  s =[ Seq (Alloc x) (Seq (Free x) (AssignHeap (Var x) e)) ]=> r <->
  exists l : loc, l \notin domf s.2 /\ r = RError (s.1.[x <- val l], s.2).
Proof. by apply: alloc_seq_error => s' l v r'; exact: use_after_free. Qed.

(* Programs c1 and c2 agree on the outcome r from the same input state s *)
Definition cmd_equiv (s : state) (c1 c2 : com) (r : result) : Prop :=
  s =[ c1 ]=> r <-> s =[ c2 ]=> r.

Notation "s =[ c1 ~ c2 ]=> r" := (cmd_equiv s c1 c2 r)
  (at level 40, c1 at level 99, c2 at level 99, r at level 39).

(* Two commands are equivalent when, from every state, they have the same
   outcomes, normal and erroneous alike. *)
Definition cequiv (c1 c2 : com) : Prop :=
  forall (s : state) r, s =[ c1 ~ c2 ]=> r.

#[global] Instance cequiv_equiv : Equivalence cequiv.
Proof.
split=> [c|c1 c2 E|c1 c2 c3 E1 E2] s r; rewrite /cmd_equiv //.
- exact: iff_sym (E s r).
- exact: iff_trans (E1 s r) (E2 s r).
Qed.

(* Equivalent commands can be exchanged inside an execution judgement. *)
#[global] Instance cexec_proper : Proper (eq ==> cequiv ==> eq ==> iff) cexec.
Proof. by move=> s _ <- c c' E r _ <-; apply: E. Qed.

#[global] Instance cmd_equiv_proper :
  Proper (eq ==> cequiv ==> cequiv ==> eq ==> iff) cmd_equiv.
Proof. by move=> s _ <- c1 c1' E1 c2 c2' E2 r _ <-; rewrite /cmd_equiv E1 E2. Qed.

Lemma cexec_skipE (s : state) r : s =[ Skip ]=> r <-> r = RNormal s.
Proof. by split=> [H|->]; [inversion H | exact: cexec_skip]. Qed.

Lemma cexec_seqE (s : state) c1 c2 r :
  s =[ Seq c1 c2 ]=> r <->
  (exists s', s =[ c1 ]=> RNormal s' /\ s' =[ c2 ]=> r) \/
  (exists sf, s =[ c1 ]=> RError sf /\ r = RError sf).
Proof.
split=> [H|[[s' [H1 H2]]|[sf [H1 ->]]]]; last 2 first.
- exact: cexec_seq H1 H2.
- exact: cexec_seq_error H1.
inversion H as [| | | | | |? ? ? s' ? H1 H2|? ? ? sf H1| | | | | |]; subst.
- by left; exists s'.
- by right; exists sf.
Qed.

Lemma cexec_choiceE (s : state) c1 c2 r :
  s =[ Choice c1 c2 ]=> r <-> s =[ c1 ]=> r \/ s =[ c2 ]=> r.
Proof.
split=> [H|[H|H]]; last 2 first.
- exact: cexec_choice_left H.
- exact: cexec_choice_right H.
by inversion H as [| | | | | | | |? ? ? ? H'|? ? ? ? H'| | | |]; [left|right].
Qed.

Lemma cexec_starE (s : state) c r :
  s =[ Star c ]=> r <-> exists n, s =[ star_n n c ]=> r.
Proof.
split=> [H|[n]]; last exact: cexec_star.
by inversion H as [| | | | | | | | | | |? ? ? n Hn| |]; exists n.
Qed.

Lemma seq_skipl c : cequiv (Seq Skip c) c.
Proof.
move=> s r; split=> [/cexec_seqE [[s' [/cexec_skipE [->] //]]|]|H].
  by case=> sf [/cexec_skipE].
exact: cexec_seq (cexec_skip s) H.
Qed.

Lemma seq_skipr c : cequiv (Seq c Skip) c.
Proof.
move=> s r; split=> [/cexec_seqE [[s' [H /cexec_skipE ->]]|[sf [H ->]]] //|H].
case: r H => [s'|sf] H; last exact: cexec_seq_error H.
exact: cexec_seq H (cexec_skip s').
Qed.

Lemma seqA c1 c2 c3 : cequiv (Seq (Seq c1 c2) c3) (Seq c1 (Seq c2 c3)).
Proof.
move=> s r; split.
- case/cexec_seqE=> [[s2 [/cexec_seqE [[s1 [H1 H2]]|[? [_ //]]] H3]]|].
    by apply: cexec_seq H1 _; exact: cexec_seq H2 H3.
  case=> sf [/cexec_seqE [[s1 [H1 H2]]|[? [H1 [->]]]] ->].
    by apply: cexec_seq H1 _; exact: cexec_seq_error H2.
  exact: cexec_seq_error H1.
- case/cexec_seqE=> [[s1 [H1 /cexec_seqE [[s2 [H2 H3]]|[sf [H2 ->]]]]]|].
  + by apply: cexec_seq _ H3; exact: cexec_seq H1 H2.
  + by apply: cexec_seq_error; exact: cexec_seq H1 H2.
  case=> sf [H1 ->].
  by apply: cexec_seq_error; exact: cexec_seq_error H1.
Qed.

(* Every command constructor respects [cequiv], so [rewrite] with an
   equivalence works under any program context. *)
#[global] Instance Seq_proper : Proper (cequiv ==> cequiv ==> cequiv) Seq.
Proof.
move=> c1 c1' E1 c2 c2' E2 s r.
split=> /cexec_seqE [[s' [/E1 H1 /E2 H2]]|[sf [/E1 H1 ->]]].
- exact: cexec_seq H1 H2.
- exact: cexec_seq_error H1.
- exact: cexec_seq H1 H2.
- exact: cexec_seq_error H1.
Qed.

#[global] Instance Choice_proper :
  Proper (cequiv ==> cequiv ==> cequiv) Choice.
Proof.
by move=> c1 c1' E1 c2 c2' E2 s r; rewrite /cmd_equiv !cexec_choiceE E1 E2.
Qed.

Lemma iter_congr n c c' :
  cequiv c c' -> cequiv (iter n (Seq c) Skip) (iter n (Seq c') Skip).
Proof. by move=> E; elim: n => //= n IH; rewrite IH E. Qed.

#[global] Instance Star_proper : Proper (cequiv ==> cequiv) Star.
Proof.
move=> c c' E s r.
split=> /cexec_starE [n /(iter_congr n _ _ E) H];
  by apply/cexec_starE; exists n.
Qed.

#[global] Instance Local_proper x : Proper (cequiv ==> cequiv) (Local x).
Proof.
move=> c c' E s r; split=> H;
  inversion H as [| | | | | | | | | |s0 r0 ? ? v Hc| | |]; subst;
  by apply: cexec_local; apply/E.
Qed.

(* c^n; c = c; c^n, where c^n := iter n (Seq c) Skip. *)
Lemma iter_seq_comm c n :
  cequiv (Seq (iter n (Seq c) Skip) c) (Seq c (iter n (Seq c) Skip)).
Proof.
elim: n => [|n IH] /=; first by rewrite seq_skipl seq_skipr.
by rewrite seqA IH.
Qed.

(* Sequencing distributes over the union [Star c] = U_n c^n, on both sides. *)
Lemma seq_starl c c' (s : state) r :
  s =[ Seq (Star c) c' ]=> r <->
  exists n, s =[ Seq (iter n (Seq c) Skip) c' ]=> r.
Proof.
split=> [|[n /cexec_seqE [[s' [H1 H2]]|[sf [H1 ->]]]]].
- case/cexec_seqE=> [[s' [/cexec_starE [n H1] H2]]|].
    by exists n; exact: cexec_seq H1 H2.
  case=> sf [/cexec_starE [n H1] ->].
  by exists n; exact: cexec_seq_error H1.
- by apply: cexec_seq H2; apply/cexec_starE; exists n.
- by apply: cexec_seq_error; apply/cexec_starE; exists n.
Qed.

Lemma seq_starr c c' (s : state) r :
  s =[ Seq c' (Star c) ]=> r <->
  exists n, s =[ Seq c' (iter n (Seq c) Skip) ]=> r.
Proof.
split=> [|[n /cexec_seqE [[s' [H1 H2]]|[sf [H1 ->]]]]].
- case/cexec_seqE=> [[s' [H1 /cexec_starE [n H2]]]|[sf [H1 ->]]].
    by exists n; exact: cexec_seq H1 H2.
  by exists 0; exact: cexec_seq_error H1.
- by apply: cexec_seq H1 _; apply/cexec_starE; exists n.
- exact: cexec_seq_error H1.
Qed.

(* Star c; c = c; Star c, errors included: both are c^+ = U_{n > 0} c^n. *)
Lemma star_seq_comm c (s : state) r :
  s =[ Seq (Star c) c ~ Seq c (Star c) ]=> r.
Proof.
split.
- by case/seq_starl=> n /iter_seq_comm H; apply/seq_starr; exists n.
- by case/seq_starr=> n /iter_seq_comm H; apply/seq_starl; exists n.
Qed.

(* The same law as a [cequiv], so it can be used with [rewrite]. *)
Lemma cequiv_star_seq_comm c : cequiv (Seq (Star c) c) (Seq c (Star c)).
Proof. exact: star_seq_comm. Qed.

End Prog.

(* Operator sets, each at the weakest structure of the mathcomp hierarchy
   that provides them. *)

Section ZmodOps.
Import GRing.Theory.
Local Open Scope ring_scope.
Context (V : zmodType).

Inductive zop := ZAdd | ZSub.

Definition zdenote (o : zop) (a b : V) : option V :=
  Some (match o with ZAdd => a + b | ZSub => a - b end).
End ZmodOps.

Section RingOps.
Import GRing.Theory.
Local Open Scope ring_scope.
Context (V : nzRingType).

Inductive rop := RAdd | RSub | RMul.

Definition rdenote (o : rop) (a b : V) : option V :=
  Some (match o with RAdd => a + b | RSub => a - b | RMul => a * b end).
End RingOps.

Section NumFieldOps.
Import Num.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope order_scope.
Context (V : numFieldType).

Inductive nop := NAdd | NSub | NMul | NDiv | NLe | NLt | NEq.

(* Comparisons are encoded as 0/1; division by zero is undefined. *)
Definition ndenote (o : nop) (a b : V) : option V :=
  match o with
  | NAdd => Some (a + b)
  | NSub => Some (a - b)
  | NMul => Some (a * b)
  | NDiv => if b == 0 then None else Some (a / b)
  | NLe  => Some (if a <= b then 1 else 0)
  | NLt  => Some (if a < b then 1 else 0)
  | NEq  => Some (if a == b then 1 else 0)
  end.
End NumFieldOps.
