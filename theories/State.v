From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.
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

Inductive comm :=
    Skip : comm
  | AssignStore : varType -> expr -> comm
  | AssignHeap : expr -> expr -> comm
  | Havoc : varType -> valType -> comm
  | Assume : sprop -> comm
  | Error : comm
  | Seq : comm -> comm -> comm
  | Local : varType -> comm -> comm
  | Choice : comm -> comm -> comm
  | Star : comm -> comm
  | Alloc : varType -> comm
  | Free : varType -> comm.

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

Inductive eval : comm -> 

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
