(** * imp: a formalisation of the IMP programming language on top of KAT *)

(* We formalise the IMP language (whose programs are also known as
   "while programs"). We give a big step semantics as an inductive
   predicate, and using KAT, and we show that the two versions
   actually coincide.
   
   We then use the [kat] tactic to prove some simple program
   equivalences, and to derive all rules of corresponding Hoare logic
   for partial correctness. *)

From Stdlib Require Import ZArith.
From RelationAlgebra Require Import kat prop rel comparisons kat_tac relalg.

(** RelationAlgebra's [frel] is fixed to [Set]; we use a [Type]-level graph
    relation so the development can be instantiated at state types living in
    [Type] (e.g. IMP's finite-map [store]). [tfrel f] is the graph [y = f x],
    with the same two lemmas [frel_comp]/[frel_weq] used by the proofs below. *)
Definition tfrel {A B: Type} (f: A -> B) : hrel A B := fun x y => y = f x.

Lemma tfrel_comp {A B C: Type} (f: A -> B) (g: B -> C):
  tfrel f ⋅ tfrel g ≡ tfrel (fun x => g (f x)).
Proof. cbv; firstorder; subst; eauto. Qed.

Lemma tfrel_weq {A B: Type} (f g: A -> B):
  (forall x, f x = g x) -> tfrel f ≡ tfrel g.
Proof. intro Hfg; cbv; firstorder; subst; rewrite ?Hfg; auto. Qed.

Section s.
(** identifiers for memory locations  *)
Variable loc: Set.
(** abstract state (or memory) *)
Variable state: Type.
(** updating the state *)
Variable update: loc -> Z -> state -> state.

(** * Definition of the languague *)

(** programs *)

Inductive prog :=
| skp
| aff (x: loc) (e: state -> Z)
| seq (p q: prog)
| ite (t: dset state) (p q: prog)
| whl (t: dset state) (p: prog).

(** notations *)
Declare Scope imp_scope.
Bind Scope imp_scope with prog.
Delimit Scope imp_scope with imp.
Notation "x  <- y" := (aff x y) (at level 90): imp_scope.
Notation "p  ;; q" := (seq p%imp q%imp) (left associativity, at level 101): imp_scope.
Arguments ite _%_ra _%_imp _%_imp.
Arguments whl _%_ra _%_imp.


(** * Big step semantics *)

(** corresponding functional relation *)
Notation upd x e := (tfrel (fun s => update x (e s) s)).


(** ** using KAT expressions in the model of relations

   the semantics can then be given by induction on the program, using
   a simple fixpoint *)

Fixpoint bstep (p: prog): hrel state state :=
  match p with
    | skp => 1
    | aff x e => upd x e
    | seq p q => bstep p ⋅ bstep q
    | ite b p q => [b] ⋅ bstep p + [!b] ⋅ bstep q
    | whl b p => ([b] ⋅ bstep p)^*  ⋅  [!b]
  end.

(** ** using an inductive predicate, as in standard textbooks *)

Inductive bstep': prog -> hrel state state :=
| s_skp: forall s, bstep' skp s s
| s_aff: forall x e s, bstep' (x <- e) s (update x (e s) s)
| s_seq: forall p q s s' s'', bstep' p s s' -> bstep' q s' s'' -> bstep' (p ;; q) s s''
| s_ite_ff: forall (b: dset state) p q s s', b s = false -> bstep' q s s' -> bstep' (ite b p q) s s'
| s_ite_tt: forall (b: dset state) p q s s', b s = true -> bstep' p s s' -> bstep' (ite b p q) s s'
| s_whl_ff: forall (b: dset state) p s, b s = false -> bstep' (whl b p) s s
| s_whl_tt: forall (b: dset state) p s s', b s = true -> bstep' (p ;; whl b p) s s' -> bstep' (whl b p) s s'.

(** ** equivalence between the two definitions *)

Lemma bstep_eq p: bstep' p ≡ bstep p.
Proof.
  apply antisym. 
  - intros s s'. induction 1. 
     reflexivity. 
     reflexivity. 
     eexists; eassumption. 
     right. eexists. split. reflexivity. simpl; now rewrite H. assumption.
     left. eexists. split. reflexivity. assumption. assumption. 
     exists s. apply (str_refl ([b] ⋅ bstep p)). reflexivity.
      simpl. unfold hrel_inj. simpl. now rewrite H.
     destruct IHbstep' as [t ? [t' ? ?]]. exists t'. 2: assumption. 
     apply (str_cons ([b] ⋅ bstep p)). exists t. 2: assumption.
     eexists; eauto. now split. 
  - induction p; unfold bstep; fold bstep.
     intros ? ? <-. constructor. 
     intros ? ? ->. constructor. 
     intros ? ? [? H1 H2]. econstructor. apply IHp1, H1. apply IHp2, H2.
     intros ? ? [[? [<- H] H']|[? [<- H] H']]. 
      apply s_ite_tt. assumption. apply IHp1, H'. 
      apply s_ite_ff. now apply Bool.negb_true_iff. apply IHp2, H'. 
     apply str_ind_l'.
      intros ? ? [<- H]. apply s_whl_ff. now apply Bool.negb_true_iff.
      rewrite <-dotA. intros s s'' [? [<- H] [s' H' H'']]. apply s_whl_tt. assumption.
      econstructor. apply IHp, H'. assumption.
Qed. 


(** * Some program equivalences *)

(** two programs are said to be equivalent if they have the same semantics *)
(** [≃] rather than [~]: Stdlib's binary-[positive] literals already use [_ ~ 1]
    and [_ ~ 0] at level 7, so a [_ ~ _] notation shares their prefix at an
    incompatible level and one of the two stops parsing. *)
Notation "p ≃ q" := (bstep p ≡ bstep q) (at level 80).

(** ad-hoc simplification tactic *)
Ltac simp := unfold bstep; fold bstep.


(** ** denesting nested loops *)
Lemma two_loops b p: 
  whl b (whl b p)  ≃  whl b p.
Proof. simp. kat. Qed.

(** ** folding a loop *)
Lemma fold_loop b p: 
  whl b (p ;; ite b p skp)  ≃  
  whl b p.
Proof. simp. kat. Qed.

(** ** eliminating deadcode *)
Lemma dead_code b p q r: 
  (whl b p ;; ite b q r)  ≃  
  (whl b p ;; r).
Proof. simp. kat. Qed.

Lemma dead_code' a b p q r: 
  (whl (a ⊔ b) p ;; ite b q r)  ≃ 
  (whl (a ⊔ b) p ;; r).
Proof. simp. kat. Qed.


(** * Reasoning about assignations *)

(** (higher-order style) substitution in formulas and expressions *)
Definition subst x v (A: dset state): dset state := 
  fun s => A (update x (v s) s).
Definition esubst x v (e: state -> Z): state -> Z :=
  fun s => e (update x (v s) s).

(** is [x] fresh in the expression e *)
Definition fresh x (e: state -> Z) := forall v s, e (update x v s) = e s.

Hypothesis update_twice: forall x i j s, update x j (update x i s) = update x j s.
Hypothesis update_comm: forall x y i j s, x<>y -> update x i (update y j s) = update y j (update x i s).


(** ** stacking assignations *)

Lemma aff_stack x e f:
  (x <- e ;; x <- f)  ≃  
  (x <- esubst x e f).
Proof.
  simp. rewrite tfrel_comp.
  apply tfrel_weq; intro s.
  apply update_twice.
Qed.


(** ** removing duplicates *)

Lemma aff_idem x e: fresh x e -> (x <- e ;; x <- e)  ≃  (x <- e). 
Proof. 
  intro. rewrite aff_stack. 
  intros s s'. cbv. rewrite (H (e s)). tauto.
Qed.

(** ** commuting assignations *)

Lemma aff_comm x y e f: x<>y  -> fresh y e ->  
  (x <- e ;; y <- f)  ≃ (y <- esubst x e f ;; x <- e).
Proof.
  intros Hx Hy. simp. rewrite 2tfrel_comp. apply tfrel_weq; intro s.
  rewrite update_comm by congruence. 
  now rewrite (Hy _). 
Qed.

(** ** delaying choices *)

(** in the above example, we cannot exploit KAT since this is just
   about assignations. In the following example, we show how to
   perform a mixed proof: once we assert that the test [t] somehow
   commutes with the assignation [x<-e], [hkat] can make use of this
   assumption to close the goal *)

Lemma aff_ite x e t p q: 
  (x <- e ;; ite t p q)  
  ≃ 
  (ite (subst x e t) (x <- e ;; p) (x <- e ;; q)).
Proof.
  simp. 
  assert (H: upd x e ⋅ [t] ≡ [subst x e t] ⋅ upd x e)
   by (cbv; firstorder; subst; eauto). 
  hkat.
Qed.



(** * Embedding Hoare logic for partial correctness *)

(** Hoare triples for partial correctness can be expressed really
   easily using KAT: *)
Notation Hoare A p B := ([A] ⋅ bstep p ⋅ [!B] ≦ 0).

(** ** correspondence w.r.t. the standard interpretation of Hoare triples  *)
Lemma Hoare_eq A p B: 
  Hoare A p B <-> 
  forall s s', A s -> bstep p s s' -> B s'.
Proof.
  split. 
  - intros H s s' HA Hp. case_eq (B s'). reflexivity. intro HB. 
    destruct (H s s'). exists s'. exists s. 
    now split. assumption. split. reflexivity. simpl. now rewrite HB. 
  - intros H s s' [? [? [<- HA] Hp] [-> HB]]. simpl in HB. 
    rewrite (H _ _ HA Hp) in HB. discriminate. 
Qed.



(** ** deriving Hoare logic rules using the [hkat] tactic *)

(** Hoare triples are encoded as propositions of the shape [x ≦ 0] ;
   therefore, they can always be eliminated by [hkat], so that all
   rules of Hoare logic can be proved automatically (except for the
   assignation rule, of course) 

   This idea come from the following paper:
   Dexter Kozen. On Hoare logic and Kleene algebra with tests. 
   Trans. Computational Logic, 1(1):60-76, July 2000.
   
   The fact that we have an automatic tactic makes it trivial to
   formalise it. *)

Lemma weakening (A A' B B': dset state) p: 
  A' ≦ A -> Hoare A p B -> B ≦ B' -> Hoare A' p B'.
Proof. hkat. Qed.

Lemma rule_skp A: Hoare A skp A.
Proof. simp. kat. Qed.

Lemma rule_seq A B C p q: 
  Hoare A p B -> 
  Hoare B q C -> 
  Hoare A (p;;q) C.
Proof. simp. hkat. Qed.

Lemma rule_ite A B t p q: 
  Hoare (A ⊓ t) p B -> 
  Hoare (A ⊓ !t) q B -> 
  Hoare A (ite t p q) B.
Proof. simp. hkat. Qed.

Lemma rule_whl A t p: 
  Hoare (A ⊓ t) p A -> 
  Hoare A (whl t p) (A ⊓ neg t).
Proof. simp. hkat. Qed.

Lemma rule_aff x v (A: dset state): Hoare (subst x v A) (x <- v) A.
Proof. 
  rewrite Hoare_eq. intros s s' HA H. 
  now inversion_clear H.
Qed.

Lemma wrong_rule_whl A t p: 
  Hoare (A ⊓ !t) p A -> 
  Hoare A (whl t p) (A ⊓ !t).
Proof. simp. Fail hkat. Abort.

Lemma rule_whl' (I A: dset state) t p: 
  Hoare (I ⊓ t) p I -> 
  I ⊓ !t ≦ A -> 
  Hoare I (whl t p) A.
Proof. eauto 3 using weakening, rule_whl. Qed.




(** * Embedding Incorrectness logic for normal termination

   Following Zhang, Azevedo de Amorim and Gaboardi (POPL 2022), the
   incorrectness triple [B] p [C] of O'Hearn (2020) can be encoded
   equationally in Kleene algebra with tests extended with a top
   element ⊤ (Kleene Algebra with Top and Tests, or TopKAT):

       [B] p [C]   ≜   ⊤ ⋅ B ⋅ p  ≥  C

   Intuitively, ⊤ ⋅ x captures the codomain of [x]: in the model of
   binary relations, [⊤ ⋅ x] is the complete relation on the domain
   restricted to [cod(x)]. Hence the encoding above states
   [cod(B; bstep p) ⊇ cod(C)], i.e. every state satisfying [C] is
   reachable from some state satisfying [B] by running [p].

   The current development does not provide a dedicated TopKAT
   abstract structure, but the relational model [hrel state state] is
   already a TopKAT: it inherits a bounded distributive lattice
   structure (level [BDL]), so it has a top element [top: hrel state state]
   which is the complete relation [fun s s' => True].
   The two key facts we use are:
   - [dottx]: [x ≦ ⊤ ⋅ x]   (since [1 ≦ ⊤])
   - [top_nnm]: [⊤ ⋅ ⊤ ≡ ⊤]   (idempotence of ⊤ under composition)
   *)

(** ** Incorrectness triples *)

Notation Incorrectness B p C := ([C] ≦ top ⋅ [B] ⋅ bstep p).

(** ** Correspondence with the standard (relational) interpretation *)

Lemma Incorrectness_eq B p C:
  Incorrectness B p C <->
  forall s', C s' -> exists2 s, B s & bstep p s s'.
Proof.
  split.
  - intros H s' HC.
    destruct (H s' s') as [k Hk Hp].
    { split. reflexivity. simpl. case_eq (C s'). reflexivity.
      intro Hcs'. rewrite Hcs' in HC. discriminate HC. }
    destruct Hk as [j _ Hjk]. simpl in Hjk. destruct Hjk as [Hjk HB].
    subst k. exists j. exact HB. exact Hp.
  - intros H s s' [Hss HC]. subst s'.
    destruct (H s HC) as [s0 HB Hp].
    exists s0.
    + exists s0. exact I. split. reflexivity. exact HB.
    + exact Hp.
Qed.

(** ** Deriving the rules of incorrectness logic

   Unlike the Hoare-logic rules above, these rules cannot be discharged
   by the [kat]/[hkat] tactic, since these tactics ignore the top
   element. They are however straightforward consequences of the
   underlying TopKAT identities. *)

(** An [hkat]-like tactic for IL rules in TopKAT shape.
    The "trick" beyond plain [hkat] is to pose [top_nnm] as a hypothesis
    so [hkat] can use [⊤·⊤ ≡ ⊤] during normalization. *)
Ltac ikat_chain :=
  repeat match goal with
         | H : _ ≦ top ⋅ _ ⋅ bstep _ |- _ => rewrite H
         end.

(** [ikat]: an [hkat]-style wrapper for IL goals in TopKAT shape.
    Handles:
      - empty postcondition (rule_iempty);
      - disjunctive pre/post (rule_idisj);
      - any goal closed by [lattice]/[kat]/[hkat] after [simp] or after
        folding [top·top → top] via [top_nnm].
    Does *not* handle: rules requiring transitivity-chaining through
    [Incorrectness] hypotheses (e.g. rule_iseq), or rules essentially
    proved via the semantic form [Incorrectness_eq] (rule_iskp,
    rule_iite_*, rule_iwhl_*, rule_iaff). *)
Ltac ikat :=
  intros;
  simp;
  first
    [ now (rewrite inj_bot; apply leq_bx)
    | now lattice
    | now hkat
    | now (rewrite top_nnm; hkat)
    | now kat
    | (* disjunctive shape: [A1 ⊔ A2] / [C1 ⊔ C2] *)
      now (rewrite ?inj_cup, ?dotxpls, ?dotplsx;
           apply leq_cupx; ikat_chain; lattice)
    | idtac "ikat: cannot close goal" ].

(** *** Empty *)
Lemma rule_iempty A p: Incorrectness A p bot.
Proof. ikat. Qed.

(** *** Consequence (note the contravariance: in Incorrectness, the
   precondition gets weaker, the postcondition gets stronger) *)
Lemma rule_iconseq (A A' B B': dset state) p:
  A ≦ A' -> Incorrectness A p B -> B' ≦ B -> Incorrectness A' p B'.
Proof.
  intros HA H HB. rewrite HB, H.
  apply dot_leq. 2: reflexivity.
  apply dot_leq. reflexivity.
  apply inj_leq, HA.
Qed.

(** *** Disjunction *)
Lemma rule_idisj (A1 A2 C1 C2: dset state) p:
  Incorrectness A1 p C1 ->
  Incorrectness A2 p C2 ->
  Incorrectness (A1 ⊔ A2) p (C1 ⊔ C2).
Proof. ikat. Qed.

(** *** Identity (skp) *)
Lemma rule_iskp A: Incorrectness A skp A.
Proof.
  rewrite Incorrectness_eq. intros s' HA. exists s'; [ exact HA | reflexivity ].
Qed.

(** *** Composition

   This is the key rule that requires the [⊤·⊤ ≡ ⊤] axiom of TopKAT
   ([top_nnm] in this development). *)
Lemma rule_iseq A B C p q:
  Incorrectness A p B ->
  Incorrectness B q C ->
  Incorrectness A (p;;q) C.
Proof.
  intros Hp Hq. simp.
  transitivity ((top: hrel state state) ⋅ [B] ⋅ bstep q). exact Hq.
  transitivity ((top: hrel state state) ⋅ (top ⋅ [A] ⋅ bstep p) ⋅ bstep q).
  - now rewrite Hp.
  - rewrite <-!dotA. rewrite (dotA (top: hrel state state) top).
    rewrite top_nnm. reflexivity.
Qed.

(** *** Choice for [ite]: incorrectness can be discharged by either branch *)
Lemma rule_iite_t A C t p q:
  Incorrectness (A ⊓ t) p C ->
  Incorrectness A (ite t p q) C.
Proof.
  rewrite !Incorrectness_eq. intros H s' HC.
  destruct (H s' HC) as [s HAt Hp]. simpl in HAt.
  apply Bool.andb_true_iff in HAt as [HA Ht].
  exists s. exact HA.
  simpl. left. exists s. split. reflexivity. simpl. exact Ht. exact Hp.
Qed.

Lemma rule_iite_f A C t p q:
  Incorrectness (A ⊓ !t) q C ->
  Incorrectness A (ite t p q) C.
Proof.
  rewrite !Incorrectness_eq. intros H s' HC.
  destruct (H s' HC) as [s HAt Hp]. simpl in HAt.
  apply Bool.andb_true_iff in HAt as [HA Ht].
  exists s. exact HA.
  simpl. right. exists s. split. reflexivity. simpl. exact Ht. exact Hp.
Qed.

(** *** While: zero iterations
   If we enter the loop with the loop-test already false, [whl t p]
   acts as the identity, so the postcondition can be the precondition
   conjuncted with the negated test. *)
Lemma rule_iwhl_zero A t p:
  Incorrectness (A ⊓ !t) (whl t p) (A ⊓ !t).
Proof.
  rewrite Incorrectness_eq. intros s' HAnt.
  exists s'. exact HAnt.
  simpl. simpl in HAnt. apply Bool.andb_true_iff in HAnt as [_ Hnt].
  exists s'. apply (str_refl ([t] ⋅ bstep p)). reflexivity.
  split. reflexivity. exact Hnt.
Qed.

(** *** While: dependent invariant (Iter-Dependent rule)
   Generalisation of the loop rule, indexed over the number of
   iterations. Given an invariant family [I] such that each iteration
   strengthens the invariant, after [n] iterations of the body we can
   reach a state in [I n]; if additionally the loop test fails there,
   we have exited the loop with postcondition [I n ⊓ !t]. *)

(** Auxiliary fact: we can extend an iteration of length [n] by one
    more step at the end. *)
Lemma iter_extend (r: hrel state state) (n: nat) s0 sn s':
  iter state r n s0 sn -> r sn s' -> iter state r (S n) s0 s'.
Proof.
  revert s0 sn s'. induction n as [|n IHn]; intros s0 sn s' Hiter Hr.
  - simpl in Hiter. subst sn. simpl. exists s'. exact Hr. reflexivity.
  - simpl in Hiter. destruct Hiter as [s1 Hr1 Hiter1].
    simpl. exists s1. exact Hr1. apply (IHn _ _ _ Hiter1 Hr).
Qed.

Lemma rule_iwhl_dep (I: nat -> dset state) t p:
  (forall n, Incorrectness (I n ⊓ t) p (I (S n))) ->
  forall n, Incorrectness (I 0%nat) (whl t p) (I n ⊓ !t).
Proof.
  intros Hp n. rewrite Incorrectness_eq.
  (* Helper: any state in [I n] is reachable from some state in [I 0]
     in exactly [n] iterations of [t]·bstep p. *)
  assert (Hloop: forall k s', I k s' = true ->
            exists2 s0, I 0%nat s0 = true & iter state ([t]⋅bstep p) k s0 s').
  { induction k as [|k IHk]; intros s' HI.
    - exists s'. exact HI. simpl. reflexivity.
    - specialize (Hp k). rewrite Incorrectness_eq in Hp.
      destruct (Hp s' HI) as [sk HIkt Hpk]. simpl in HIkt.
      apply Bool.andb_true_iff in HIkt as [HIk Ht].
      destruct (IHk sk HIk) as [s0 HI0 Hiter].
      exists s0. exact HI0.
      apply (iter_extend _ _ _ sk).
      + exact Hiter.
      + exists sk. split. reflexivity. exact Ht. exact Hpk. }
  intros s' HInt. simpl in HInt.
  apply Bool.andb_true_iff in HInt as [HIn Hnt].
  destruct (Hloop n s' HIn) as [s0 HI0 Hiter].
  exists s0. exact HI0. simpl.
  exists s'. exists n. exact Hiter. split. reflexivity. exact Hnt.
Qed.

(** *** Assignment

   O'Hearn's assignment rule
       [B] x := e [∃ y, B[y/x] ∧ x = e[y/x]]
   uses a fresh syntactic variable [y] to capture the previous value
   of [x]. Like its Hoare counterpart [rule_aff], this rule is
   non-propositional: it goes beyond the equational theory of TopKAT.

   Hoare and Incorrectness are however not symmetric here. For Hoare,
   one can compute the strongest precondition by *backward*
   substitution, which is a function ([subst]), so [rule_aff] is a
   clean schema. For Incorrectness, one needs the strongest
   *postcondition*, i.e. the image of the precondition through
   [x := v], which is intrinsically existential.

   In our semantic setting [dset state = state -> bool] there is no
   way to express such an existential as a test in general. We
   therefore state the rule as a soundness lemma whose hypothesis is
   exactly the image side-condition: every state satisfying the
   postcondition [C] must be exhibited as the result of running
   [x := v] on some state in [B]. *)
Lemma rule_iaff x v (B C: dset state):
  (forall s', C s' = true ->
              exists2 s, B s = true & s' = update x (v s) s) ->
  Incorrectness B (x <- v) C.
Proof.
  rewrite Incorrectness_eq. intros H s' HC.
  destruct (H s' HC) as [s HB Heq].
  exists s. exact HB. simpl. unfold tfrel. now symmetry.
Qed.

End s.

