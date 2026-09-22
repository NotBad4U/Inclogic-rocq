From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat.
From mathcomp Require Import ssralg ssrnum order finmap finset.

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
Context (varType valType : choiceType) (loc : {fset valType}).
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
  | Assume : sprop -> com
  | Error : com
  | Seq : com -> com -> com
  | Local : varType -> com -> com
  | Choice : com -> com -> com
  | Star : com -> com
  | Alloc : varType -> com
  | Free : varType -> com.

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

Inductive cexec: state -> com -> result -> Prop :=
| cexec_skip: forall s,
  s =[ Skip ]=> RNormal s
| cexec_error: forall s,
  s =[ Error ]=> RError s
| cexec_assign_store: forall (s : state) x a,
  s =[ AssignStore x a ]=>
    if eval_expr a s is Some v then RNormal (s.1.[x <- v], s.2)
    else RError s
| cexec_assign_heap: forall (s : state) x y,
  s =[ AssignHeap x y ]=>
    if (olet l  := eval_expr x s in
        olet l' := insub l in
        olet v  := eval_expr y s in
        if l' \in domf s.2 then Some (s.1, s.2.[l' <- v]) else None)
      is Some s' then RNormal s' else RError s
| cexec_nondet: forall s x any,
  s =[ Nondet x ]=> RNormal (s.1.[x <- any], s.2)
| cexec_assume: forall s b,
  b s.1 s.2 ->
  s =[ Assume b ]=> ret s
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
| cexec_local: forall (s: state) r x c v, (* FIXME: why need the type on s ?? *)
  let restore := fun s' : state =>
    (if s.1.[? x] is Some v0 then s'.1.[x <- v0] else s'.1.[~ x], s'.2)
  in
  (s.1.[x <- v], s.2) =[ c ]=> r ->
  s =[ Local x c ]=> fmap restore r
(*
  [[C*]] = ⋃_i [[C^i]], with [[C^0]] = Skip and [[C^i+1]] = [[C ; C^i]] 
  It differ from the @Imp.v because IL allow loop to fail but SIL no. 
*)
| cexec_star: forall (s : state) c r n,
  s =[ iter n (Seq c) Skip ]=> r ->
  s =[ Star c ]=> r
| cexec_alloc: forall s x l any,
  l \notin domf s.2 ->
  s  =[ Alloc x ]=> RNormal (s.1.[x <- val l], s.2.[l <- any]) (* Following C malloc that put any value *)
| cexec_alloc_error: forall s x l,
  l \in domf s.2 ->
  s  =[ Alloc x ]=> RError s
| cexec_free: forall (s : state) x,
  s  =[ Free x ]=>
    if (olet v := s.1.[? x] in
        olet l := insub v in
        if l \in domf s.2 then Some (s.1, s.2.[~ l]) else None)
      is Some s' then RNormal s' else RError s
where "st0 =[ c ]=> st1" := (cexec st0 c st1).
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
