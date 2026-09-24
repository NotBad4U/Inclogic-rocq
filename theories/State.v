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
Abbreviation mapsnot := (mapsnot varType valType loc).

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

(* Inversion lemmas for [cexec]. *)

Lemma cexec_skipE (s : state) r : s =[ Skip ]=> r <-> r = RNormal s.
Proof. by split=> [H|->]; [inversion H | exact: cexec_skip]. Qed.

Lemma cexec_errorE (s : state) r : s =[ Error ]=> r <-> r = RError s.
Proof. by split=> [H|->]; [inversion H | exact: cexec_error]. Qed.

Lemma cexec_assign_storeE (s : state) x a r :
  s =[ AssignStore x a ]=> r <->
  r = if eval_expr a s is Some v then RNormal (s.1.[x <- v], s.2) else RError s.
Proof. by split=> [H|->]; [inversion H | exact: cexec_assign_store]. Qed.

Lemma cexec_assign_heapE (s : state) a e r :
  s =[ AssignHeap a e ]=> r <->
  r = if (olet l  := eval_expr a s in
          olet l' := insub l in
          olet v  := eval_expr e s in
          if l' \in domf s.2 then Some (s.1, s.2.[l' <- v]) else None)
        is Some s' then RNormal s' else RError s.
Proof. by split=> [H|->]; [inversion H | exact: cexec_assign_heap]. Qed.

Lemma cexec_nondetE (s : state) x r :
  s =[ Nondet x ]=> r <-> exists any, r = RNormal (s.1.[x <- any], s.2).
Proof.
split=> [H|[any ->]]; last exact: cexec_nondet.
by inversion H as [| | | |? ? any| | | | | | | | |]; exists any.
Qed.

Lemma cexec_assumeE (s : state) b r :
  s =[ Assume b ]=> r <->
  r = if eval_expr b s == Some null then RError s else RNormal s.
Proof. by split=> [H|->]; [inversion H | exact: cexec_assume]. Qed.

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

Lemma cexec_allocE (s : state) x r :
  s =[ Alloc x ]=> r <->
  exists (l : loc) any, l \notin domf s.2 /\
    r = RNormal (s.1.[x <- val l], s.2.[l <- any]).
Proof.
split=> [H|[l [any [Hl ->]]]]; last exact: cexec_alloc.
by inversion H as [| | | | | | | | | | | |? ? l any Hl|]; exists l, any.
Qed.

Lemma cexec_freeE (s : state) x r :
  s =[ Free x ]=> r <->
  r = if (olet v := s.1.[? x] in
          olet l := insub v in
          if l \in domf s.2 then Some (s.1, s.2.[~ l]) else None)
        is Some s' then RNormal s' else RError s.
Proof. by split=> [H|->]; [inversion H | exact: cexec_free]. Qed.

Section CmdEquiv.

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

Lemma cequiv_star_seq_comm c : cequiv (Seq (Star c) c) (Seq c (Star c)).
Proof. exact: star_seq_comm. Qed.

End CmdEquiv.

Section MemoryViolation.

(** Faulty commands err in place. *)

(* free(x) errs in place when x is dangling. *)
Lemma free_err x (s : state) r :
  (forall v l, s.1.[? x] = Some v -> insub v = Some l -> l \notin domf s.2) ->
  s =[ Free x ]=> r <-> r = RError s.
Proof.
move=> Hd; rewrite cexec_freeE.
case Ex: s.1.[? x] => [v|] //=; case El: (insub v) => [l|] //=.
by rewrite (negbTE (Hd _ _ Ex El)).
Qed.

Lemma free_null (s : state) x r :
  null \notin loc -> s.1.[? x] = Some null ->
  s =[ Free x ]=> r <-> r = RError s.
Proof.
move=> Hnull Hx; apply: free_err => v l.
by rewrite Hx => -[<-]; rewrite insubN.
Qed.

Lemma mapsnot_dangling x (s : state) :
  mapsnot x s.1 s.2 ->
  forall v l, s.1.[? x] = Some v -> insub v = Some l -> l \notin domf s.2.
Proof. by case=> l [Hx Hl] v l'; rewrite Hx => -[<-]; rewrite valK => -[<-]. Qed.

Lemma free_mapsnot x (s : state) r :
  mapsnot x s.1 s.2 -> s =[ Free x ]=> r <-> r = RError s.
Proof. by move/mapsnot_dangling; exact: free_err. Qed.

Lemma free_allocated (s : state) x (l : loc) r :
  s.1.[? x] = Some (val l) -> l \in domf s.2 ->
  s =[ Free x ]=> r <-> r = RNormal (s.1, s.2.[~ l]).
Proof. by move=> Hx Hl; rewrite cexec_freeE Hx /= valK /= Hl. Qed.

(* free(x) errs in place exactly when x holds no location or x holds an unallocated one. *)
Lemma free_errE (s : state) x :
  (forall r, s =[ Free x ]=> r <-> r = RError s) <->
  (forall v, s.1.[? x] = Some v -> v \notin loc) \/ mapsnot x s.1 s.2.
Proof.
split=> [H|[Hn|Hd] r]; last 2 first.
- by apply: free_err => v l /Hn Hv; rewrite insubN.
- exact: free_mapsnot.
case Ex: s.1.[? x] => [v|]; last by left.
case: (boolP (v \in loc)) => Hv; last by left=> _ [<-].
have Hx : s.1.[? x] = Some (val (Sub v Hv : loc)) by rewrite Ex SubK.
case: (boolP (Sub v Hv \in domf s.2)) => Hdom; last by right; exists (Sub v Hv).
by move/H: ((free_allocated _ _ _ _ Hx Hdom).2 erefl).
Qed.

Lemma write_unallocated (s : state) a e (l : loc) r :
  eval_expr a s = Some (val l) -> l \notin domf s.2 ->
  s =[ AssignHeap a e ]=> r <-> r = RError s.
Proof.
move=> Ha Hl; rewrite cexec_assign_heapE Ha /= valK /=.
by case: eval_expr => //= v; rewrite (negbTE Hl).
Qed.

(* *x := e errs in place on a dangling x. *)
Lemma write_dangling x e (s : state) r :
  (forall v l, s.1.[? x] = Some v -> insub v = Some l -> l \notin domf s.2) ->
  s =[ AssignHeap (Var x) e ]=> r <-> r = RError s.
Proof.
move=> Hd; rewrite cexec_assign_heapE /=.
case Ex: s.1.[? x] => [v|] //=; case El: (insub v) => [l|] //=.
by case: eval_expr => //= w; rewrite (negbTE (Hd _ _ Ex El)).
Qed.

(* y := *x errs in place on a dangling x. *)
Lemma read_dangling x y (s : state) r :
  (forall v l, s.1.[? x] = Some v -> insub v = Some l -> l \notin domf s.2) ->
  s =[ AssignStore y (Deref (Var x)) ]=> r <-> r = RError s.
Proof.
move=> Hd; rewrite cexec_assign_storeE /=.
case Ex: s.1.[? x] => [v|] //=; case El: (insub v) => [l|] //=.
by rewrite (not_fnd (Hd _ _ Ex El)).
Qed.

Lemma free_dangles (s s' : state) x y :
  s.1.[? x] = s.1.[? y] -> s =[ Free y ]=> RNormal s' -> mapsnot x s'.1 s'.2.
Proof.
move=> Hxy /cexec_freeE; rewrite -Hxy.
case Ex: s.1.[? x] => [v|] //=; case: insubP => [l _ Ev|] //=.
by case: ifP => // _ [->]; exists l; rewrite /= Ex Ev mem_remfF.
Qed.

Lemma mapsnot_free x y (s1 s2 : state) :
  mapsnot x s1.1 s1.2 -> s1 =[ Free y ]=> RNormal s2 -> mapsnot x s2.1 s2.2.
Proof.
case=> l [Hx Hl] /cexec_freeE.
case: s1.1.[? y] => [v|] //=; case: (insub v) => [l'|] //=.
by case: ifP => // _ [->]; exists l; rewrite /= Hx mem_remf1 (negbTE Hl) andbF.
Qed.

Lemma mapsnot_assign_store x y a : x != y ->
  forall s1 s2 : state,
  mapsnot x s1.1 s1.2 -> s1 =[ AssignStore y a ]=> RNormal s2 -> mapsnot x s2.1 s2.2.
Proof.
move=> Hxy s1 s2 [l [Hx Hl]] /cexec_assign_storeE.
by case: eval_expr => [v|] //= [->]; exists l; rewrite /= fnd_set (negbTE Hxy) Hx.
Qed.

Lemma mapsnot_assign_heap x a e (s1 s2 : state) :
  mapsnot x s1.1 s1.2 -> s1 =[ AssignHeap a e ]=> RNormal s2 -> mapsnot x s2.1 s2.2.
Proof.
case=> l [Hx Hl] /cexec_assign_heapE.
case: (eval_expr a s1) => [va|] //=; case: (insub va) => [la|] //=.
case: (eval_expr e s1) => [ve|] //=; case: ifP => // Ha [->].
exists l; rewrite mem_setf inE negb_or Hl andbT; split=> //.
by apply: contraNneq Hl => ->.
Qed.

Lemma skip_inv (p : sprop) (s1 s2 : state) :
  p s1.1 s1.2 -> s1 =[ Skip ]=> RNormal s2 -> p s2.1 s2.2.
Proof. by move=> H /cexec_skipE [->]. Qed.

Lemma keep_mapsnot {x P} :
  (forall s1 s2 : state,
    mapsnot x s1.1 s1.2 -> s1 =[ P ]=> RNormal s2 -> mapsnot x s2.1 s2.2) ->
  forall s1 s2 : state, mapsnot x s1.1 s1.2 -> s1 =[ P ]=> RNormal s2 ->
  forall v l, s2.1.[? x] = Some v -> insub v = Some l -> l \notin domf s2.2.
Proof. by move=> K s1 s2 H1 /(K _ _ H1) /mapsnot_dangling. Qed.

Lemma seq_errorE (s : state) P r :
  s =[ Seq P Error ]=> r <->
  exists s', r = RError s' /\ (s =[ P ]=> RNormal s' \/ s =[ P ]=> RError s').
Proof.
rewrite cexec_seqE; split=> [[[s' [H /cexec_errorE ->]]|[sf [H ->]]]|[s' [-> [H|H]]]].
- by exists s'; split=> //; left.
- by exists sf; split=> //; right.
- by left; exists s'; split=> //; exact/cexec_errorE.
- by right; exists s'.
Qed.

Lemma seq_err_in_place (p : sprop) P c (s : state) r :
  (forall s', s =[ P ]=> RNormal s' -> p s'.1 s'.2) ->
  (forall (s' : state) r', p s'.1 s'.2 -> s' =[ c ]=> r' <-> r' = RError s') ->
  s =[ Seq P c ]=> r <-> s =[ Seq P Error ]=> r.
Proof.
move=> HP Hc; rewrite !cexec_seqE.
split=> -[[s' [H1 H2]]|H]; [left | by right | left | by right]; exists s'.
  by split=> //; move/(Hc _ _ (HP _ H1)): H2 => ->; exact: cexec_error.
by split=> //; apply/(Hc _ _ (HP _ H1)); move/cexec_errorE: H2.
Qed.

Lemma free_dangling x P (s : state) r :
  (forall s' : state, s =[ P ]=> RNormal s' ->
    forall v l, s'.1.[? x] = Some v -> insub v = Some l -> l \notin domf s'.2) ->
  s =[ Seq P (Free x) ]=> r <-> s =[ Seq P Error ]=> r.
Proof.
move=> HP; apply: (seq_err_in_place
  (fun st h => forall v l, st.[? x] = Some v -> insub v = Some l -> l \notin domf h)) => //.
exact: free_err.
Qed.

Lemma free_unbound x P (s : state) r :
  (forall v, s.1.[? x] = Some v -> v \notin loc) ->
  (forall s1 s2 : state, (forall v, s1.1.[? x] = Some v -> v \notin loc) ->
    s1 =[ P ]=> RNormal s2 -> forall v, s2.1.[? x] = Some v -> v \notin loc) ->
  s =[ Seq P (Free x) ]=> r <-> s =[ Seq P Error ]=> r.
Proof.
move=> Hx HP; apply: free_dangling => s' /(HP _ _ Hx) Hn v l /Hn Hv.
by rewrite insubN.
Qed.


Section Dangling.
Context {x : varType} {P : com}.

Hypothesis keep_dangling : forall s1 s2 : state, mapsnot x s1.1 s1.2 ->
  s1 =[ P ]=> RNormal s2 ->
  forall v l, s2.1.[? x] = Some v -> insub v = Some l -> l \notin domf s2.2.

Lemma use_after_lifetime (s : state) y c r :
  s.1.[? x] = s.1.[? y] ->
  (forall (s : state) r, (forall v l, s.1.[? x] = Some v -> insub v = Some l ->
     l \notin domf s.2) -> s =[ c ]=> r <-> r = RError s) ->
  s =[ Seq (Free y) (Seq P c) ]=> r <-> s =[ Seq (Free y) (Seq P Error) ]=> r.
Proof.
move=> Hxy Hc; rewrite -!seqA; apply: (seq_err_in_place
  (fun st h => forall v l, st.[? x] = Some v -> insub v = Some l -> l \notin domf h)) => // s'.
case/cexec_seqE=> [[s1 [/(free_dangles _ _ _ _ Hxy) H1 H2]]|[? [_ //]]].
exact: keep_dangling H1 H2.
Qed.

Lemma use_after_free c :
  (forall (s : state) r, (forall v l, s.1.[? x] = Some v -> insub v = Some l ->
     l \notin domf s.2) -> s =[ c ]=> r <-> r = RError s) ->
  cequiv (Seq (Free x) (Seq P c)) (Seq (Free x) (Seq P Error)).
Proof. by move=> Hc s r; exact: use_after_lifetime. Qed.

Lemma double_free :
  cequiv (Seq (Free x) (Seq P (Free x))) (Seq (Free x) (Seq P Error)).
Proof. exact: use_after_free (free_err x). Qed.

Lemma free_unallocated (s : state) r :
  mapsnot x s.1 s.2 -> s =[ Seq P (Free x) ]=> r <-> s =[ Seq P Error ]=> r.
Proof. by move=> Hx; apply: free_dangling => s'; exact: keep_dangling Hx. Qed.

End Dangling.

Lemma use_after_lifetime_reach x y P c (s s1 s2 : state) :
  (forall (s : state) r, (forall v l, s.1.[? x] = Some v -> insub v = Some l ->
     l \notin domf s.2) -> s =[ c ]=> r <-> r = RError s) ->
  s =[ Free y ]=> RNormal s1 -> s1 =[ P ]=> RNormal s2 ->
  (forall v l, s2.1.[? x] = Some v -> insub v = Some l -> l \notin domf s2.2) ->
  s =[ Seq (Free y) (Seq P c) ]=> RError s2.
Proof.
move=> Hc H1 H2 Hx; apply: cexec_seq H1 _; apply: cexec_seq H2 _.
exact/(Hc _ _ Hx).
Qed.

Lemma double_free_reach x P (s s1 s2 : state) :
  s =[ Free x ]=> RNormal s1 -> s1 =[ P ]=> RNormal s2 ->
  (forall v l, s2.1.[? x] = Some v -> insub v = Some l -> l \notin domf s2.2) ->
  s =[ Seq (Free x) (Seq P (Free x)) ]=> RError s2.
Proof. exact: use_after_lifetime_reach (free_err x). Qed.

(** Concrete programs examples, as corollaries. *)

Let seq_det (s s' : state) c1 c2 r :
  (forall r', s =[ c1 ]=> r' <-> r' = RNormal s') ->
  s =[ Seq c1 c2 ]=> r <-> s' =[ c2 ]=> r.
Proof.
move=> H1; split=> [/cexec_seqE [[s0 [/H1 [<-] //]]|[sf [/H1 //]]]|H2].
exact: cexec_seq (proj2 (H1 _) erefl) H2.
Qed.

(* x := malloc(); c runs c from a state where x points to a fresh cell l holding an arbitrary value. *)
Let seq_alloc (s : state) x c r :
  s =[ Seq (Alloc x) c ]=> r <->
  exists (l : loc) any, l \notin domf s.2 /\
    (s.1.[x <- val l], s.2.[l <- any]) =[ c ]=> r.
Proof.
split=> [/cexec_seqE [[s' [/cexec_allocE [l [any [Hl [->]]]] H]]|]|[l [any [Hl H]]]].
- by exists l, any.
- by case=> sf [/cexec_allocE [? [? [_ //]]]].
exact: cexec_seq (cexec_alloc _ _ _ any Hl) H.
Qed.

(*
  free(x)         // x points to the allocated cell l
  free(x)         // ERROR: double free
*)
Example free_free (s : state) x (l : loc) v r :
  s.1.[? x] = Some (val l) -> s.2.[? l] = Some v ->
  s =[ Seq (Free x) (Free x) ]=> r <-> r = RError (s.1, s.2.[~ l]).
Proof.
move=> Hx Hv; have Hl : l \in domf s.2 by rewrite -fndSome Hv.
have E := double_free (keep_mapsnot (skip_inv (mapsnot x))).
rewrite !seq_skipl in E.
rewrite E (seq_det _ (s.1, s.2.[~ l])); first by move=> r'; exact: free_allocated.
exact: cexec_errorE.
Qed.

(*
  free(x)         // x points to the allocated cell l
  y := v          // unrelated store write: x still dangles
  free(x)         // ERROR: double free
*)
Example free_assign_free (s : state) x y v (l : loc) r :
  x != y -> s.1.[? x] = Some (val l) -> l \in domf s.2 ->
  s =[ Seq (Free x) (Seq (AssignStore y (Const v)) (Free x)) ]=> r <->
  r = RError (s.1.[y <- v], s.2.[~ l]).
Proof.
move=> Hxy Hx Hl.
rewrite (double_free (keep_mapsnot (mapsnot_assign_store _ _ (Const v) Hxy))).
rewrite (seq_det _ (s.1, s.2.[~ l])); first by move=> r'; exact: free_allocated.
rewrite (seq_det _ (s.1.[y <- v], s.2.[~ l])); last exact: cexec_errorE.
by move=> r'; rewrite cexec_assign_storeE.
Qed.

(*
  free(x)         // x points to the allocated cell l
  y := alloc()    // may hand l out again: x is valid again
  free(x)         // succeeds
  so the hypothesis on P in [double_free] cannot be dropped; the erroneous
  run is [free_alloc_free_err].
*)
Example free_alloc_free (s : state) x y (l : loc) :
  s.1.[? x] = Some (val l) -> l \in domf s.2 ->
  s =[ Seq (Free x) (Seq (Alloc y) (Free x)) ]=> RNormal (s.1.[y <- val l], s.2.[~ l]).
Proof.
move=> Hx Hl; apply: cexec_seq ((free_allocated _ _ _ _ Hx Hl).2 erefl) _.
have Hl' : l \notin domf s.2.[~ l] by rewrite mem_remfF.
apply: cexec_seq (cexec_alloc (s.1, s.2.[~ l]) y l null Hl') _.
have Hx' : s.1.[y <- val l].[? x] = Some (val l) by rewrite fnd_set Hx if_same.
have Hl'' : l \in domf s.2.[~ l].[l <- null] by rewrite mem_setf inE eqxx.
apply/(free_allocated (s.1.[y <- val l], s.2.[~ l].[l <- null]) x l _ Hx' Hl'').
by rewrite /= remf1_set eqxx (remf1_id Hl').
Qed.

(*
  free(x)         // x points to the allocated cell l
  y := alloc()    // on the run where alloc hands out a cell l' other than l
  free(x)         // ERROR: double free, reached on this run
*)
Example free_alloc_free_err (s : state) x y (l l' : loc) v :
  x != y -> s.1.[? x] = Some (val l) -> l \in domf s.2 -> l' \notin domf s.2 ->
  s =[ Seq (Free x) (Seq (Alloc y) (Free x)) ]=>
    RError (s.1.[y <- val l'], s.2.[~ l].[l' <- v]).
Proof.
move=> Hxy Hx Hl Hl'.
apply: double_free_reach ((free_allocated _ _ _ _ Hx Hl).2 erefl) _ _.
  by apply: cexec_alloc; rewrite mem_remf1 negb_and Hl' orbT.
apply: mapsnot_dangling; exists l.
rewrite fnd_set (negbTE Hxy) Hx mem_setf inE mem_remfF orbF; split=> //.
by apply: contraNneq Hl' => <-.
Qed.

(* Double free: x := malloc(); free(x); free(x) always ends in an error,
   raised by the second free. *)
Example double_free_ret_error (s : state) x r :
  s =[ Seq (Alloc x) (Seq (Free x) (Free x)) ]=> r <->
  exists l : loc, l \notin domf s.2 /\ r = RError (s.1.[x <- val l], s.2).
Proof.
rewrite seq_alloc; split=> [[l [any [Hl]]]|[l [Hl ->]]].
  rewrite (free_free _ _ l any) /= ?fnd_set ?eqxx // remf1_set eqxx remf1_id //.
  by move=> ->; exists l.
exists l, null; rewrite (free_free _ _ l null) /= ?fnd_set ?eqxx //.
by rewrite remf1_set eqxx remf1_id.
Qed.

(*
  free(x)         // x points to the allocated cell l
  *x := e         // ERROR: use after free (write)
*)
Example free_write (s : state) x (l : loc) v e r :
  s.1.[? x] = Some (val l) -> s.2.[? l] = Some v ->
  s =[ Seq (Free x) (AssignHeap (Var x) e) ]=> r <->
  r = RError (s.1, s.2.[~ l]).
Proof.
move=> Hx Hv; have Hl : l \in domf s.2 by rewrite -fndSome Hv.
have E := use_after_free (keep_mapsnot (skip_inv (mapsnot x))) _ (write_dangling x e).
rewrite !seq_skipl in E.
rewrite E (seq_det _ (s.1, s.2.[~ l])); first by move=> r'; exact: free_allocated.
exact: cexec_errorE.
Qed.

(*
  free(x)         // x points to the allocated cell l
  y := *x         // ERROR: use after free (read)
*)
Example free_read (s : state) x y (l : loc) r :
  s.1.[? x] = Some (val l) -> l \in domf s.2 ->
  s =[ Seq (Free x) (AssignStore y (Deref (Var x))) ]=> r <->
  r = RError (s.1, s.2.[~ l]).
Proof.
move=> Hx Hl.
have E := use_after_free (keep_mapsnot (skip_inv (mapsnot x))) _ (read_dangling x y).
rewrite !seq_skipl in E.
rewrite E (seq_det _ (s.1, s.2.[~ l])); first by move=> r'; exact: free_allocated.
exact: cexec_errorE.
Qed.

(* Use after free: x := malloc(); free(x); *x := e always ends in an error,
   raised by the write. *)
Example use_after_free_ret_error (s : state) x e r :
  s =[ Seq (Alloc x) (Seq (Free x) (AssignHeap (Var x) e)) ]=> r <->
  exists l : loc, l \notin domf s.2 /\ r = RError (s.1.[x <- val l], s.2).
Proof.
rewrite seq_alloc; split=> [[l [any [Hl]]]|[l [Hl ->]]].
  rewrite (free_write _ _ l any) /= ?fnd_set ?eqxx // remf1_set eqxx remf1_id //.
  by move=> ->; exists l.
exists l, null; rewrite (free_write _ _ l null) /= ?fnd_set ?eqxx //.
by rewrite remf1_set eqxx remf1_id.
Qed.

(*
  x := alloc(v)   // x points to l, which holds v    (hypotheses Hx, Hv)
  y := x          // y aliases x: y also points to l
  free(y)         // deallocate l
  use(x)          // ERROR: x still points to l, but l has been freed
                  // (use-after-free; here use(x) is *x := e)
*)
Example alias_free_write (s : state) x y (l : loc) v e r :
  s.1.[? x] = Some (val l) -> s.2.[? l] = Some v ->
  s =[ Seq (AssignStore y (Var x)) (Seq (Free y) (AssignHeap (Var x) e)) ]=> r <->
  r = RError (s.1.[y <- val l], s.2.[~ l]).
Proof.
move=> Hx Hv; have Hl : l \in domf s.2 by rewrite -fndSome Hv.
set s' := (s.1.[y <- val l], s.2).
have Hy : s'.1.[? y] = Some (val l) by rewrite fnd_set eqxx.
have Hxy : s'.1.[? x] = s'.1.[? y] by rewrite Hy fnd_set Hx if_same.
rewrite (seq_det _ s'); first by move=> r'; rewrite cexec_assign_storeE /= Hx.
rewrite -(seq_skipl (AssignHeap (Var x) e)).
rewrite (use_after_lifetime (keep_mapsnot (skip_inv (mapsnot x))) _ _ _ _ Hxy
  (write_dangling x e)).
rewrite seq_skipl (seq_det _ (s'.1, s'.2.[~ l])); last exact: cexec_errorE.
by move=> r'; exact: free_allocated.
Qed.

(*
  // x is unbound: it was never allocated
  y := alloc()    // allocating another variable never gives x a location
  free(x)         // ERROR: freeing a non-allocated variable
*)
Example alloc_free_unbound (s : state) x y r :
  x != y -> s.1.[? x] = None ->
  s =[ Seq (Alloc y) (Free x) ]=> r <->
  exists (l : loc) any, l \notin domf s.2 /\
    r = RError (s.1.[y <- val l], s.2.[l <- any]).
Proof.
move=> Hxy Hx; rewrite free_unbound; first by move=> v; rewrite Hx.
  move=> s1 s2 Hn /cexec_allocE [l [any [_ [->]]]] v /=.
  by rewrite fnd_set (negbTE Hxy); exact: Hn.
rewrite seq_alloc; split=> [[l [any [Hl /cexec_errorE ->]]]|[l [any [Hl ->]]]].
  by exists l, any.
by exists l, any; split=> //; exact: cexec_error.
Qed.

(*
  // x dangles: it points to l, which is not allocated
  free(z)         // frees another cell lz: x still dangles
  free(x)         // ERROR: freeing a dangling pointer
*)
Example free_free_dangling (s : state) x z (l lz : loc) r :
  s.1.[? x] = Some (val l) -> l \notin domf s.2 ->
  s.1.[? z] = Some (val lz) -> lz \in domf s.2 ->
  s =[ Seq (Free z) (Free x) ]=> r <-> r = RError (s.1, s.2.[~ lz]).
Proof.
move=> Hx Hl Hz Hlz.
rewrite (free_unallocated (keep_mapsnot (mapsnot_free x z))); first by exists l.
rewrite (seq_det _ (s.1, s.2.[~ lz])); first by move=> r'; exact: free_allocated.
exact: cexec_errorE.
Qed.

End MemoryViolation.

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
