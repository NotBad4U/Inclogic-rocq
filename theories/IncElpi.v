(** * Automated incorrectness proofs by forward SP search, driven by Elpi

  [Inc.SP] turns an incorrectness triple into a verification condition:

<<
      ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧    ⇐    vcond P c  ∧  Q --* sp P c
>>

  [ExampleIncSP.v] annotates every loop by hand to discharge the first
  conjunct.  This file supplies no annotation at all: an unannotated loop
  ([Imp.CSTAR None]) already has the post [Inc.SP] needs, so [vcond] collapses
  to the loop bodies' own side conditions — [True] for a loop-free body.  See
  [SP.vcond_cstar_none].

  ** What is left, and why it is a search

  The whole proof then rests on one goal, [Q --* sp P c], whose loop case reads
  "the target state is reachable in _some_ number of turns".  Two things must
  be found, and neither is determined by unification:

  - the number of turns at each loop — found by iterative deepening;
  - at each [ASSIGN x a], the value [x] held _before_ the assignment — found by
    inverting [a] against the value [x] holds _after_ it.

  That inversion is symbolic manipulation of [aexp] terms with backtracking,
  which is what Elpi is here for.  [NONDET x] picks no value at all, so its
  witness is left as an unknown and fixed later by the linear equation some
  earlier assignment imposes on it (this is what makes [loop0] work).

  ** Scope

  - loop bodies must be loop-free (nested loops are rejected with an error);
  - the search is bounded: [il_auto] tries up to [il_depth] turns per loop, so
    an error reachable only after a large number of iterations (the 2,000,000
    of [loop2]) is out of reach by design and still wants a hand-written
    invariant — see [ExampleIncSP.v].
*)

From Stdlib Require Import Arith ZArith Psatz Bool String List.
From mathcomp Require Import ssrbool eqtype choice.
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import finmap.
Set Warnings "notation-incompatible-prefix".
From elpi Require Import elpi.
From IncLogic Require Import Imp Sequences Hoare Inc.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ** Entry point *)

Lemma il_entry: forall (P: assertion) (c: com) (Q: postassertion),
  SP.vcond P c ->
  (Q --* SP.sp P c) ->
  ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧.
Proof. intros P c Q Hv Hi. exact (SP.vcgen_valid P c Q (conj Hv Hi)). Qed.

(** ** Introduction rules for the strongest post

    [slp_ok] and [slp_err] are [Fixpoint]s, so most of these hold by
    computation; they are stated as lemmas anyway, to give the search one
    named rule per syntactic case and to keep the assignment witness in an
    explicit argument position. *)

Lemma slp_ok_skip: forall (P: assertion) (s: store),
  P s -> SP.slp_ok P SKIP s.
Proof. auto. Qed.

Lemma slp_ok_assume: forall (P: assertion) b (s: store),
  beval b s = true -> P s -> SP.slp_ok P (ASSUME b) s.
Proof. intros P b s Hb HP. exact (conj Hb HP). Qed.

(** [m] is the value [x] held before the assignment. *)
(** The arithmetic premise comes *before* the recursive one: it is what rules
    out a wrong number of loop turns, and checking it first prunes the branch
    before the search descends into it. *)
Lemma slp_ok_assign: forall (P: assertion) x a (s: store) (m: Z),
  x \in domf s ->
  aeval a (update x m s) = s x ->
  P (update x m s) ->
  SP.slp_ok P (ASSIGN x a) s.
Proof.
  intros P x a s m Hd Ha HP. split; [ exact Hd | ].
  exists m, (s x). split; [ reflexivity | exact (conj HP Ha) ].
Qed.

Lemma slp_ok_nondet: forall (P: assertion) x (s: store) (m: Z),
  x \in domf s -> P (update x m s) -> SP.slp_ok P (NONDET x) s.
Proof. intros P x s m Hd HP. split; [ exact Hd | exists m; exact HP ]. Qed.

Lemma slp_ok_seq: forall (P: assertion) c1 c2 (s: store),
  SP.slp_ok (SP.slp_ok P c1) c2 s -> SP.slp_ok P (SEQ c1 c2) s.
Proof. auto. Qed.

Lemma slp_ok_choice_l: forall (P: assertion) c1 c2 (s: store),
  SP.slp_ok P c1 s -> SP.slp_ok P (CHOICE c1 c2) s.
Proof. intros; left; assumption. Qed.

Lemma slp_ok_choice_r: forall (P: assertion) c1 c2 (s: store),
  SP.slp_ok P c2 s -> SP.slp_ok P (CHOICE c1 c2) s.
Proof. intros; right; assumption. Qed.

(** The loop: [k] turns suffice. *)
(** An *annotated* loop hands its post straight over: with [★ ⟨ I ⟩] the post
    is [I], with [★ ⟨| R |⟩] it is some stage of [R].  This is the escape
    hatch — annotate the one loop the search cannot do, leave the rest [None]
    and let [il_auto] handle them. *)
Lemma slp_ok_cstar_inv: forall (P: assertion) Inv body (s: store),
  Inv s -> SP.slp_ok P (CSTAR (Some (AInv Inv)) body) s.
Proof. auto. Qed.

Lemma slp_ok_cstar_var: forall (P: assertion) R body (s: store) (n: nat),
  R n s -> SP.slp_ok P (CSTAR (Some (AVar R)) body) s.
Proof. intros P R body s n H. exists n. exact H. Qed.

(** [k] turns suffice: [slp_ok_cstar_none] read backwards. *)
Lemma slp_ok_cstar: forall (P: assertion) body (s: store) (k: nat),
  SP.iter_slp_ok P body k s -> SP.slp_ok P (CSTAR None body) s.
Proof.
  intros P body s k H. apply SP.slp_ok_cstar_none. exists k. exact H.
Qed.

Lemma iter_slp_ok_O: forall (P: assertion) body (s: store),
  P s -> SP.iter_slp_ok P body 0 s.
Proof. auto. Qed.

Lemma iter_slp_ok_S: forall (P: assertion) body (s: store) (k: nat),
  SP.slp_ok (SP.iter_slp_ok P body k) body s -> SP.iter_slp_ok P body (S k) s.
Proof. auto. Qed.

(** Faulting exits. *)

Lemma slp_err_error: forall (P: assertion) (s: store),
  P s -> SP.slp_err P ERROR s.
Proof. auto. Qed.

Lemma slp_err_seq_l: forall (P: assertion) c1 c2 (s: store),
  SP.slp_err P c1 s -> SP.slp_err P (SEQ c1 c2) s.
Proof. intros; left; assumption. Qed.

Lemma slp_err_seq_r: forall (P: assertion) c1 c2 (s: store),
  SP.slp_err (SP.slp_ok P c1) c2 s -> SP.slp_err P (SEQ c1 c2) s.
Proof. intros; right; assumption. Qed.

Lemma slp_err_choice_l: forall (P: assertion) c1 c2 (s: store),
  SP.slp_err P c1 s -> SP.slp_err P (CHOICE c1 c2) s.
Proof. intros; left; assumption. Qed.

Lemma slp_err_choice_r: forall (P: assertion) c1 c2 (s: store),
  SP.slp_err P c2 s -> SP.slp_err P (CHOICE c1 c2) s.
Proof. intros; right; assumption. Qed.

Lemma slp_err_cstar: forall (P: assertion) ann body (s: store),
  SP.slp_err (SP.slp_ok P (CSTAR ann body)) body s ->
  SP.slp_err P (CSTAR ann body) s.
Proof. auto. Qed.

(** ** Leaf solvers

    Everything the search hands back to Rocq: store-domain facts, boolean
    guards, and linear integer arithmetic. *)

Lemma in_domf_update_same: forall (x: ident) (v: Z) (s: store),
  x \in domf (update x v s).
Proof. intros x v s. rewrite dom_update, eqxx. reflexivity. Qed.

Lemma in_domf_update: forall (x y: ident) (v: Z) (s: store),
  x \in domf s -> x \in domf (update y v s).
Proof. intros x y v s H. rewrite dom_update, H, orbT. reflexivity. Qed.

Lemma in_domf_of_neq_0: forall (x: ident) (s: store), s x <> 0 -> x \in domf s.
Proof.
  intros x s Hne. pose proof (fndSome s x) as HS. unfold sget in Hne.
  destruct (s .[? x]%fmap) as [v | ] eqn:Hf.
  - cbn in HS. symmetry; exact HS.
  - cbn in Hne. exfalso. apply Hne. reflexivity.
Qed.

Create HintDb il.
#[export] Hint Resolve in_domf_update_same in_domf_update : il.

Ltac il_store :=
  repeat first
    [ rewrite update_same in *
    | rewrite update_shadow in *
    | rewrite update_other in * by discriminate ].

(** Reduce every SP transformer and assertion combinator away. *)
Ltac il_cbn :=
  cbn [SP.sp SP.slp_ok SP.slp_err SP.vcond SP.iter_slp_ok] in *;
  unfold aimp, paimp, aand, aor, aexists, aforall, aupdate, aequal,
         atrue, afalse, in_domf, ffalse in *;
  cbn [aeval beval GREATER GREATEREQUAL LESS NOTEQUAL OR ODD] in *;
  il_store.

Ltac il_bool :=
  first [ apply Z.eqb_eq | apply Z.eqb_neq | apply Z.leb_le
        | apply Z.leb_gt | apply Z.ltb_lt | apply Z.ltb_ge ].

(** Close one leaf.  [il_leaf] never splits a goal: the search decides the
    shape, this only discharges what it hands over. *)
Ltac il_leaf :=
  (* GREATER/LESS/NOTEQUAL are Definitions, so [beval] cannot reduce past them
     until they are unfolded *)
  cbn [aeval beval GREATER GREATEREQUAL LESS NOTEQUAL OR ODD] in *;
  il_store;
  rewrite ?Bool.negb_involutive;
  solve [ assumption
        | reflexivity
        | exact I
        | lia
        | auto with il
        | apply in_domf_of_neq_0; lia
        | il_bool; lia
        | apply Bool.negb_true_iff; il_bool; lia
        | apply Bool.negb_false_iff; il_bool; lia
        | cbn [aeval beval] in *; il_store; lia ].

(** The user's precondition, once the search has consumed the whole program.
    [tauto]/[lia] after unfolding is all we can do in general. *)
Ltac il_pre :=
  (* user-supplied invariants are opaque constants; register them with
     [#[local] Hint Unfold my_inv : il.] and they are unfolded here *)
  try autounfold with il in *;
  (* deliberately does NOT unfold SP.slp_ok & co: [slp_ok P (CHOICE c1 c2)]
     mentions P twice, so unfolding under a loop is exponential in the number
     of turns.  Only the assertion combinators are expanded here. *)
  unfold aimp, paimp, aand, aor, aexists, aforall, aupdate, aequal,
         atrue, afalse, in_domf, ffalse in *;
  cbn [aeval beval GREATER GREATEREQUAL LESS NOTEQUAL OR ODD] in *;
  il_store;
  solve [ tauto | lia | il_leaf | intuition (lia || il_leaf) ].

(** [vcond] is syntax-directed and, on unannotated loops, content-free. *)
Ltac il_vcond :=
  repeat first [ exact I
               | simple apply SP.vcond_cstar_none; intro
               | split ].

(** The store is a mathcomp [finmap] over a [choiceType] of strings, so
    computing with [update]/[sget] goes through the [Choice]/[Countable]
    encodings of [Imp.v].  Nothing in the search ever needs that computation —
    the leaf solver reasons with [update_same] and friends, which are lemmas —
    but if conversion is allowed to try, every rule application pays for it.
    Keep them opaque from here on. *)
Strategy opaque [update sget].

(** And the transformers themselves.  [slp_ok P (CHOICE c1 c2)] is
    [slp_ok P c1 \\// slp_ok P c2]: the precondition occurs *twice*, so
    unfolding [iter_slp_ok P body k] for a body containing an [IF] is
    exponential in [k].  The search never needs that unfolding — every rule
    below matches its goal syntactically — but conversion will attempt it
    during typechecking unless told not to. *)
Strategy opaque [SP.slp_ok SP.slp_err SP.iter_slp_ok].

(** ** Setup.  What used to be a term-to-term translation in Elpi is now one
    [apply]: there is nothing to reify. *)

Ltac il_setup := apply il_entry; [ il_vcond | ].


(** Split the post inclusion into its [ok] and [err] halves.  For a one-sided
    spec ([ok ↑ _] / [err ↑ _]) the other half is [False] and closes at once. *)
Ltac il_open :=
  let r := fresh "r" in
  intros r; destruct r as [? | ?]; cbn [SP.sp] in *;
  let h := fresh "Hq" in intros h; try contradiction;
  (* the post is typically a conjunction, and its conjuncts are exactly the
     facts the leaves need: domain membership, guards, arithmetic *)
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Ltac il_close := first [ il_leaf | il_pre ].

(** Rule application goes through Ltac's [apply] rather than coq-elpi's
    [refine.typecheck]: on these goals [apply] unifies the conclusion and
    stops, whereas [refine.typecheck] typechecks the whole application and
    spends seconds on it, growing with search depth.  The witness and the
    loop depth are the only arguments the search has to supply.

    Plain [apply], not [simple apply]: a program is usually a [Definition],
    so matching a rule against the goal has to unfold that constant, which
    [simple apply] declines to do. *)
Ltac il_r_skip      := apply slp_ok_skip.
Ltac il_r_assume    := apply slp_ok_assume.
Ltac il_r_assign m  := apply (slp_ok_assign _ _ _ _ m).
Ltac il_r_nondet m  := apply (slp_ok_nondet _ _ _ m).
Ltac il_r_seq       := apply slp_ok_seq.
Ltac il_r_cstar k   := apply (slp_ok_cstar _ _ _ k).
Ltac il_r_cinv      := apply slp_ok_cstar_inv.
Ltac il_r_cvar n    := apply (slp_ok_cstar_var _ _ _ _ n).
Ltac il_r_choice_l  := apply slp_ok_choice_l.
Ltac il_r_choice_r  := apply slp_ok_choice_r.
Ltac il_r_iterO     := apply iter_slp_ok_O.
Ltac il_r_iterS     := apply iter_slp_ok_S.
Ltac il_r_error     := apply slp_err_error.
Ltac il_r_ecstar    := apply slp_err_cstar.
Ltac il_r_eseq_l    := apply slp_err_seq_l.
Ltac il_r_eseq_r    := apply slp_err_seq_r.
Ltac il_r_echoice_l := apply slp_err_choice_l.
Ltac il_r_echoice_r := apply slp_err_choice_r.

(** ** S2: the search

    One clause per syntactic case of [slp_ok] / [slp_err].  Elpi's own
    backtracking does the searching: the [CHOICE] rules and the loop-depth
    generator have no cut, so a leaf that Rocq cannot close (a guard that does
    not hold, an arithmetic fact that is false) makes the search take the
    next branch.  Deterministic cases are cut.

    The one thing that is computed rather than searched is the [ASSIGN]
    witness: [ainv] inverts the assigned expression against the value the
    variable holds afterwards, which is read off the symbolic store by
    [sval]. *)

Elpi Tactic il_run.
Elpi Accumulate lp:{{

pred pick i:list A, o:A.
pick [X|_] X.
pick [_|Xs] X :- pick Xs X.

% ---- reading the symbolic store -------------------------------------------

% sval Sigma X V : V is the Z-term that X denotes in the store term Sigma
pred sval i:term, i:term, o:term.
sval {{ update lp:Y lp:W lp:S }} X V :- !,
  if (Y = X) (V = W) (sval S X V).
sval S X {{ sget lp:S lp:X }}.

% aval E Sigma V : V is the Z-term that the expression E denotes at Sigma
pred aval i:term, i:term, o:term.
aval {{ CONST lp:N }} _ N :- !.
aval {{ VAR lp:Y }} S V :- !, sval S Y V.
aval {{ PLUS lp:E1 lp:E2 }} S {{ lp:V1 + lp:V2 }} :- !, aval E1 S V1, aval E2 S V2.
aval {{ MINUS lp:E1 lp:E2 }} S {{ lp:V1 - lp:V2 }} :- !, aval E1 S V1, aval E2 S V2.

pred mentions i:term, i:term.
mentions {{ VAR lp:Y }} X :- Y = X.
mentions {{ PLUS lp:E1 lp:E2 }} X :- mentions E1 X ; mentions E2 X.
mentions {{ MINUS lp:E1 lp:E2 }} X :- mentions E1 X ; mentions E2 X.

% ainv E X Sigma Target M :
%   after [X := E] the variable X holds Target; M is what it held before.
%   When E does not read X the assignment forgets it, so M is arbitrary and
%   the obligation [aeval E Sigma = Target] is left for the leaf solver.
pred ainv i:term, i:term, i:term, i:term, o:term.
ainv E X _ _ {{ 0%Z }} :- not (mentions E X), !.
ainv {{ VAR lp:X }} X _ T T :- !.
ainv {{ PLUS lp:E1 lp:E2 }} X S T M :- not (mentions E2 X), !,
  aval E2 S V2, ainv E1 X S {{ lp:T - lp:V2 }} M.
ainv {{ PLUS lp:E1 lp:E2 }} X S T M :- not (mentions E1 X), !,
  aval E1 S V1, ainv E2 X S {{ lp:T - lp:V1 }} M.
ainv {{ MINUS lp:E1 lp:E2 }} X S T M :- not (mentions E2 X), !,
  aval E2 S V2, ainv E1 X S {{ lp:T + lp:V2 }} M.
ainv {{ MINUS lp:E1 lp:E2 }} X S T M :- not (mentions E1 X), !,
  aval E1 S V1, ainv E2 X S {{ lp:V1 - lp:T }} M.

% ---- candidates for a NONDET witness --------------------------------------
% NONDET constrains nothing, so its witness is only fixed by what the rest of
% the program does with it.  Rather than solving for it, offer the values the
% program can talk about and let backtracking choose.

pred idents i:term, o:list term.
idents T [T] :- T = {{ String _ _ }}, !.
idents (app L) R :- !, std.map L idents Ls, std.flatten Ls R.
idents _ [].

pred undup i:list A, o:list A.
undup [] [].
undup [X|Xs] R :- undup Xs R1, if (std.mem R1 X) (R = R1) (R = [X|R1]).

pred cands i:term, i:term, o:list term.
cands Ty S CL :-
  idents Ty IDs, undup IDs IDs1,
  std.map IDs1 (x\ r\ r = {{ sget lp:S lp:x }}) VS,
  std.append [{{ 0%Z }}] VS CL.

% ---- loop depth -----------------------------------------------------------

pred max-depth o:int.
max-depth 4.

pred nat-upto i:int, o:term.
nat-upto _ {{ 0%nat }}.
nat-upto D {{ S lp:K }} :- D > 0, D1 is D - 1, nat-upto D1 K.

% ---- the search -----------------------------------------------------------

pred dispatch i:sealed-goal, o:list sealed-goal.
dispatch SG GL :- coq.ltac.open search SG GL.

pred dispatch-all i:list sealed-goal, o:list sealed-goal.
dispatch-all [] [].
dispatch-all [G|Gs] GL :- dispatch G G1, dispatch-all Gs G2, std.append G1 G2 GL.

pred search i:goal, o:list sealed-goal.
search (goal _ _ {{ SP.slp_ok lp:P lp:A lp:S }} _ _ as G) GL :- !,
  coq.reduction.lazy.whd A A1, sok P A1 S G GL.
search (goal _ _ {{ SP.slp_err lp:P lp:A lp:S }} _ _ as G) GL :- !,
  coq.reduction.lazy.whd A A1, serr P A1 S G GL.
search (goal _ _ {{ SP.iter_slp_ok lp:P lp:A lp:K lp:S }} _ _ as G) GL :- !,
  coq.reduction.lazy.whd K K1, siter P A K1 S G GL.
search G GL :- coq.ltac.call "il_close" [] G [], GL = [].

pred sok i:term, i:term, i:term, i:goal, o:list sealed-goal.

sok _P {{ SKIP }} _S G GL :- !,
  coq.ltac.call "il_r_skip" [] G SGs, dispatch-all SGs GL.
sok _P {{ ASSUME lp:_B }} _S G GL :- !,
  coq.ltac.call "il_r_assume" [] G SGs, dispatch-all SGs GL.
sok _P {{ ASSIGN lp:X lp:E }} S G GL :- !,
  sval S X T, ainv E X S T M,
  coq.ltac.call "il_r_assign" [trm M] G SGs,
  dispatch-all SGs GL.
sok _P {{ NONDET lp:_X }} S (goal _ _ Ty _ _ as G) GL :- !,
  cands Ty S CL, pick CL M,
  coq.ltac.call "il_r_nondet" [trm M] G SGs,
  dispatch-all SGs GL.
sok _P {{ SEQ lp:_C1 lp:_C2 }} _S G GL :- !,
  coq.ltac.call "il_r_seq" [] G SGs, dispatch-all SGs GL.
sok _P {{ CSTAR (Some (AInv lp:_I)) lp:_B }} _S G GL :- !,
  coq.ltac.call "il_r_cinv" [] G SGs, dispatch-all SGs GL.
sok _P {{ CSTAR (Some (AVar lp:_R)) lp:_B }} _S G GL :- !,
  max-depth D, nat-upto D K,
  coq.ltac.call "il_r_cvar" [trm K] G SGs, dispatch-all SGs GL.
sok _P {{ CSTAR None lp:_B }} _S G GL :- !,
  max-depth D, nat-upto D K,
  coq.ltac.call "il_r_cstar" [trm K] G SGs, dispatch-all SGs GL.
% no cut: both branches of a choice are tried
sok _P {{ CHOICE lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_choice_l" [] G SGs, dispatch-all SGs GL.
sok _P {{ CHOICE lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_choice_r" [] G SGs, dispatch-all SGs GL.

pred siter i:term, i:term, i:term, i:term, i:goal, o:list sealed-goal.
siter _P _B {{ 0%nat }} _S G GL :- !,
  coq.ltac.call "il_r_iterO" [] G SGs, dispatch-all SGs GL.
siter _P _B {{ S lp:_K }} _S G GL :- !,
  coq.ltac.call "il_r_iterS" [] G SGs, dispatch-all SGs GL.

pred serr i:term, i:term, i:term, i:goal, o:list sealed-goal.
serr _P {{ ERROR }} _S G GL :- !,
  coq.ltac.call "il_r_error" [] G SGs, dispatch-all SGs GL.
serr _P {{ CSTAR lp:_A lp:_B }} _S G GL :- !,
  coq.ltac.call "il_r_ecstar" [] G SGs, dispatch-all SGs GL.
serr _P {{ SEQ lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_eseq_r" [] G SGs, dispatch-all SGs GL.
serr _P {{ SEQ lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_eseq_l" [] G SGs, dispatch-all SGs GL.
serr _P {{ CHOICE lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_echoice_l" [] G SGs, dispatch-all SGs GL.
serr _P {{ CHOICE lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_echoice_r" [] G SGs, dispatch-all SGs GL.

solve G GL :- search G GL.

}}.

Ltac il_search := elpi il_run.

(** The post half on its own, for proofs that discharge [vcond] by hand
    because some loop carries an annotation. *)
Ltac il_post := il_open; il_search.

(** Everything: discharge [vcond], split the post, search. *)
Ltac il_auto := il_setup; [ il_open; il_search .. ].
