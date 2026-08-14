(** * Automated incorrectness proofs by forward SP search, driven by Elpi

  [Inc.SP] turns an incorrectness triple into a verification condition:

<<
      ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧    ⇐    vcond P a  ∧  Q --* sp P a        (erase a = c)
>>

  where [a] is [c] with every loop annotated.  [ExampleIncSP.v] supplies those
  annotations — an invariant and a forwards variant per loop — by hand.  This
  file removes them.

  ** The canonical annotation

  The obligation on an annotation [Inv] of [c★] is, among others,

<<
      Inv -->> (fun s => exists m, iter_slp_ok P c m s)
>>

  so the _largest_ legal annotation is that union itself.  Taking it
  ([Istar] below) makes the implication an identity and [vcond] collapses to
  the loop bodies' own side conditions — [True], as long as no loop is
  nested inside another.  Nothing has to be invented: see [vcond_Istar].

  ** What is left, and why it is a search

  The whole proof then rests on one goal, [Q --* sp P a], whose loop case reads
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

(** ** The canonical loop annotation *)

Definition Istar (P: assertion) (body: SP.acom) : assertion :=
  fun s => exists m, SP.iter_slp_ok P body m s.

(** With it, a loop contributes nothing to [vcond] beyond its body. *)
Lemma vcond_Istar: forall (P: assertion) (body: SP.acom),
  (forall R, SP.vcond R body) ->
  SP.vcond P (SP.CSTAR (Istar P body) body).
Proof.
  intros P body Hbody. split; [ | split ].
  - intros s Hs. exact Hs.
  - intros m. apply Hbody.
  - apply Hbody.
Qed.

(** Entry point, with the two verification conditions taken apart so that a
    tactic can refine against it. *)
Lemma il_entry: forall (P: assertion) (a: SP.acom) (c: com) (Q: postassertion),
  SP.erase a = c ->
  SP.vcond P a ->
  (Q --* SP.sp P a) ->
  ⟦⟦ P ⟧⟧ c ⟦⟦ Q ⟧⟧.
Proof. intros P a c Q He Hv Hi. exact (SP.vcgen_valid P a c Q He (conj Hv Hi)). Qed.

(** ** Introduction rules for the strongest post

    [slp_ok] and [slp_err] are [Fixpoint]s, so most of these hold by
    computation; they are stated as lemmas anyway, to give the search one
    named rule per syntactic case and to keep the assignment witness in an
    explicit argument position. *)

Lemma slp_ok_skip: forall (P: assertion) (s: store),
  P s -> SP.slp_ok P SP.SKIP s.
Proof. auto. Qed.

Lemma slp_ok_assume: forall (P: assertion) b (s: store),
  beval b s = true -> P s -> SP.slp_ok P (SP.ASSUME b) s.
Proof. intros P b s Hb HP. exact (conj Hb HP). Qed.

(** [m] is the value [x] held before the assignment. *)
(** The arithmetic premise comes *before* the recursive one: it is what rules
    out a wrong number of loop turns, and checking it first prunes the branch
    before the search descends into it. *)
Lemma slp_ok_assign: forall (P: assertion) x a (s: store) (m: Z),
  x \in domf s ->
  aeval a (update x m s) = s x ->
  P (update x m s) ->
  SP.slp_ok P (SP.ASSIGN x a) s.
Proof.
  intros P x a s m Hd Ha HP. split; [ exact Hd | ].
  exists m, (s x). split; [ reflexivity | exact (conj HP Ha) ].
Qed.

Lemma slp_ok_nondet: forall (P: assertion) x (s: store) (m: Z),
  x \in domf s -> P (update x m s) -> SP.slp_ok P (SP.NONDET x) s.
Proof. intros P x s m Hd HP. split; [ exact Hd | exists m; exact HP ]. Qed.

Lemma slp_ok_seq: forall (P: assertion) c1 c2 (s: store),
  SP.slp_ok (SP.slp_ok P c1) c2 s -> SP.slp_ok P (SP.SEQ c1 c2) s.
Proof. auto. Qed.

Lemma slp_ok_choice_l: forall (P: assertion) c1 c2 (s: store),
  SP.slp_ok P c1 s -> SP.slp_ok P (SP.CHOICE c1 c2) s.
Proof. intros; left; assumption. Qed.

Lemma slp_ok_choice_r: forall (P: assertion) c1 c2 (s: store),
  SP.slp_ok P c2 s -> SP.slp_ok P (SP.CHOICE c1 c2) s.
Proof. intros; right; assumption. Qed.

(** The loop: [k] turns suffice. *)
Lemma slp_ok_cstar: forall (P: assertion) body (s: store) (k: nat),
  SP.iter_slp_ok P body k s -> SP.slp_ok P (SP.CSTAR (Istar P body) body) s.
Proof. intros P body s k H. exists k. exact H. Qed.

Lemma iter_slp_ok_O: forall (P: assertion) body (s: store),
  P s -> SP.iter_slp_ok P body 0 s.
Proof. auto. Qed.

Lemma iter_slp_ok_S: forall (P: assertion) body (s: store) (k: nat),
  SP.slp_ok (SP.iter_slp_ok P body k) body s -> SP.iter_slp_ok P body (S k) s.
Proof. auto. Qed.

(** Faulting exits. *)

Lemma slp_err_error: forall (P: assertion) (s: store),
  P s -> SP.slp_err P SP.ERROR s.
Proof. auto. Qed.

Lemma slp_err_seq_l: forall (P: assertion) c1 c2 (s: store),
  SP.slp_err P c1 s -> SP.slp_err P (SP.SEQ c1 c2) s.
Proof. intros; left; assumption. Qed.

Lemma slp_err_seq_r: forall (P: assertion) c1 c2 (s: store),
  SP.slp_err (SP.slp_ok P c1) c2 s -> SP.slp_err P (SP.SEQ c1 c2) s.
Proof. intros; right; assumption. Qed.

Lemma slp_err_choice_l: forall (P: assertion) c1 c2 (s: store),
  SP.slp_err P c1 s -> SP.slp_err P (SP.CHOICE c1 c2) s.
Proof. intros; left; assumption. Qed.

Lemma slp_err_choice_r: forall (P: assertion) c1 c2 (s: store),
  SP.slp_err P c2 s -> SP.slp_err P (SP.CHOICE c1 c2) s.
Proof. intros; right; assumption. Qed.

Lemma slp_err_cstar: forall (P: assertion) body (s: store),
  SP.slp_err (Istar P body) body s ->
  SP.slp_err P (SP.CSTAR (Istar P body) body) s.
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
  cbn [SP.sp SP.slp_ok SP.slp_err SP.vcond SP.iter_slp_ok SP.erase] in *;
  unfold Istar, aimp, paimp, aand, aor, aexists, aforall, aupdate, aequal,
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
  (* deliberately does NOT unfold SP.slp_ok & co: [slp_ok P (CHOICE c1 c2)]
     mentions P twice, so unfolding under a loop is exponential in the number
     of turns.  Only the assertion combinators are expanded here. *)
  unfold aimp, paimp, aand, aor, aexists, aforall, aupdate, aequal,
         atrue, afalse, in_domf, ffalse in *;
  cbn [aeval beval GREATER GREATEREQUAL LESS NOTEQUAL OR ODD] in *;
  il_store;
  solve [ tauto | lia | il_leaf | intuition (lia || il_leaf) ].

(** [vcond] is syntax-directed and, with [Istar] annotations, content-free. *)
Ltac il_vcond :=
  repeat first [ exact I
               | simple apply vcond_Istar; intro
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
Strategy opaque [SP.slp_ok SP.slp_err SP.iter_slp_ok Istar].

(** ** S1: reification

    [com] carries no annotations, [acom] carries one per loop.  Rebuilding the
    former as the latter is a term-to-term translation, which is why it lives
    in Elpi and not in Ltac: the precondition has to be threaded through the
    sequence so that each loop is annotated with [Istar] at the assertion
    reaching it. *)

Elpi Tactic il_setup.
Elpi Accumulate lp:{{

% A loop body must be loop-free: otherwise [vcond_Istar] leaves obligations
% about the inner annotation at every iterate, which we do not synthesise.
pred loop-free i:term.
loop-free C :- coq.reduction.lazy.whd C C1, loop-free1 C1.

pred loop-free1 i:term.
loop-free1 {{ SKIP }}.
loop-free1 {{ ERROR }}.
loop-free1 {{ ASSIGN _ _ }}.
loop-free1 {{ NONDET _ }}.
loop-free1 {{ ASSUME _ }}.
loop-free1 {{ SEQ lp:C1 lp:C2 }} :- loop-free C1, loop-free C2.
loop-free1 {{ CHOICE lp:C1 lp:C2 }} :- loop-free C1, loop-free C2.

% reify Pre Com Acom
pred reify i:term, i:term, o:term.
reify P C A :- coq.reduction.lazy.whd C C1, reify1 P C1 A.

pred reify1 i:term, i:term, o:term.
reify1 _ {{ SKIP }}          {{ SP.SKIP }}.
reify1 _ {{ ERROR }}         {{ SP.ERROR }}.
reify1 _ {{ ASSIGN lp:X lp:E }} {{ SP.ASSIGN lp:X lp:E }}.
reify1 _ {{ NONDET lp:X }}   {{ SP.NONDET lp:X }}.
reify1 _ {{ ASSUME lp:B }}   {{ SP.ASSUME lp:B }}.
reify1 P {{ SEQ lp:C1 lp:C2 }} {{ SP.SEQ lp:A1 lp:A2 }} :-
  reify P C1 A1,
  reify {{ SP.slp_ok lp:P lp:A1 }} C2 A2.
reify1 P {{ CHOICE lp:C1 lp:C2 }} {{ SP.CHOICE lp:A1 lp:A2 }} :-
  reify P C1 A1, reify P C2 A2.
reify1 P {{ CSTAR lp:C }} {{ SP.CSTAR (Istar lp:P lp:A) lp:A }} :-
  if (loop-free C) true
     (coq.error "il_setup: nested loops are not supported;"
                "annotate the inner loop by hand (see ExampleIncSP.v)"),
  reify P C A.

solve (goal _ _ {{ IncTriple lp:P lp:C lp:Q }} _ _ as G) GL :- !,
  reify P C A,
  refine {{ il_entry lp:P lp:A lp:C lp:Q _ _ _ }} G GL.
solve _ _ :- coq.error "il_setup: goal is not an incorrectness triple".

}}.

(** Turn a triple into its two verification conditions, and discharge the
    structural one on the spot. *)
Ltac il_setup := elpi il_setup; [ reflexivity | il_vcond | ].

Lemma Istar_intro: forall (P: assertion) body (s: store) (k: nat),
  SP.iter_slp_ok P body k s -> Istar P body s.
Proof. intros P body s k H. exists k. exact H. Qed.

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
    loop depth are the only arguments the search has to supply. *)
Ltac il_r_skip      := simple apply slp_ok_skip.
Ltac il_r_assume    := simple apply slp_ok_assume.
Ltac il_r_assign m  := simple apply (slp_ok_assign _ _ _ _ m).
Ltac il_r_nondet m  := simple apply (slp_ok_nondet _ _ _ m).
Ltac il_r_seq       := simple apply slp_ok_seq.
Ltac il_r_cstar k   := simple apply (slp_ok_cstar _ _ _ k).
Ltac il_r_choice_l  := simple apply slp_ok_choice_l.
Ltac il_r_choice_r  := simple apply slp_ok_choice_r.
Ltac il_r_iterO     := simple apply iter_slp_ok_O.
Ltac il_r_iterS     := simple apply iter_slp_ok_S.
Ltac il_r_istar k   := simple apply (Istar_intro _ _ _ k).
Ltac il_r_error     := simple apply slp_err_error.
Ltac il_r_ecstar    := simple apply slp_err_cstar.
Ltac il_r_eseq_l    := simple apply slp_err_seq_l.
Ltac il_r_eseq_r    := simple apply slp_err_seq_r.
Ltac il_r_echoice_l := simple apply slp_err_choice_l.
Ltac il_r_echoice_r := simple apply slp_err_choice_r.

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
search (goal _ _ {{ Istar lp:_P lp:_B lp:_S }} _ _ as G) GL :- !,
  max-depth D, nat-upto D K,
  coq.ltac.call "il_r_istar" [trm K] G SGs, dispatch-all SGs GL.
search G GL :- coq.ltac.call "il_close" [] G [], GL = [].

pred sok i:term, i:term, i:term, i:goal, o:list sealed-goal.

sok _P {{ SP.SKIP }} _S G GL :- !,
  coq.ltac.call "il_r_skip" [] G SGs, dispatch-all SGs GL.
sok _P {{ SP.ASSUME lp:_B }} _S G GL :- !,
  coq.ltac.call "il_r_assume" [] G SGs, dispatch-all SGs GL.
sok _P {{ SP.ASSIGN lp:X lp:E }} S G GL :- !,
  sval S X T, ainv E X S T M,
  coq.ltac.call "il_r_assign" [trm M] G SGs,
  dispatch-all SGs GL.
sok _P {{ SP.NONDET lp:_X }} S (goal _ _ Ty _ _ as G) GL :- !,
  cands Ty S CL, pick CL M,
  coq.ltac.call "il_r_nondet" [trm M] G SGs,
  dispatch-all SGs GL.
sok _P {{ SP.SEQ lp:_C1 lp:_C2 }} _S G GL :- !,
  coq.ltac.call "il_r_seq" [] G SGs, dispatch-all SGs GL.
sok P {{ SP.CSTAR (Istar lp:P lp:B) lp:B }} _S G GL :- !,
  max-depth D, nat-upto D K,
  coq.ltac.call "il_r_cstar" [trm K] G SGs, dispatch-all SGs GL.
% no cut: both branches of a choice are tried
sok _P {{ SP.CHOICE lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_choice_l" [] G SGs, dispatch-all SGs GL.
sok _P {{ SP.CHOICE lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_choice_r" [] G SGs, dispatch-all SGs GL.

pred siter i:term, i:term, i:term, i:term, i:goal, o:list sealed-goal.
siter _P _B {{ 0%nat }} _S G GL :- !,
  coq.ltac.call "il_r_iterO" [] G SGs, dispatch-all SGs GL.
siter _P _B {{ S lp:_K }} _S G GL :- !,
  coq.ltac.call "il_r_iterS" [] G SGs, dispatch-all SGs GL.

pred serr i:term, i:term, i:term, i:goal, o:list sealed-goal.
serr _P {{ SP.ERROR }} _S G GL :- !,
  coq.ltac.call "il_r_error" [] G SGs, dispatch-all SGs GL.
serr P {{ SP.CSTAR (Istar lp:P lp:B) lp:B }} _S G GL :- !,
  coq.ltac.call "il_r_ecstar" [] G SGs, dispatch-all SGs GL.
serr _P {{ SP.SEQ lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_eseq_r" [] G SGs, dispatch-all SGs GL.
serr _P {{ SP.SEQ lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_eseq_l" [] G SGs, dispatch-all SGs GL.
serr _P {{ SP.CHOICE lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_echoice_l" [] G SGs, dispatch-all SGs GL.
serr _P {{ SP.CHOICE lp:_C1 lp:_C2 }} _S G GL :-
  coq.ltac.call "il_r_echoice_r" [] G SGs, dispatch-all SGs GL.

solve G GL :- search G GL.

}}.

Ltac il_search := elpi il_run.

(** Everything: reify, discharge [vcond], split the post, search. *)
Ltac il_auto := il_setup; [ il_open; il_search .. ].
