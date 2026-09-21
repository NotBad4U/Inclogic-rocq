(** * The allocation-free fragment of Clight

    Incorrectness logic is a bug-finding logic: a triple [⟦P⟧ c ⟦err: Q⟧]
    claims that every state in [Q] is genuinely reachable, so every alarm it
    raises is a real one.  To run it on C rather than on the IMP of
    [Imp.v] we need a language whose states are as simple as IMP's store —
    otherwise the strongest-postcondition machinery of [Inc.v], and the
    search of [IncElpi.v] that rests on it, have nothing to compute with.

    CompCert's Clight is almost that language already, provided we cut away
    the memory.  This file defines the cut.

    ** What the fragment is

    A Clight function has three classes of local variable:

    - [fn_params], the parameters;
    - [fn_vars], the locals that live in memory, because their address is
      taken or they are aggregates;
    - [fn_temps], the *temporaries*, which do not reside in memory and whose
      address cannot be taken.

    Under [function_entry2] — the entry semantics of [Clight.semantics2],
    i.e. of Clight as it comes out of CompCert's [SimplLocals] pass —
    parameters are bound to temporaries and *only* [fn_vars] is allocated.
    So

        [fn_vars f = []]

    says exactly that entering [f] performs no allocation, and
    [function_entry2_alloc_free] below turns that syntactic check into the
    semantic statement [m' = m ∧ e = empty_env].

    Add to that the requirement that the body never mentions memory —
    no [Evar] (a global or a stack local), no [Ederef], no [Eaddrof], no
    [Efield], no [Sassign], no [Sbuiltin] — and the memory [m] is not merely
    un-allocated but wholly untouched: it is a parameter of the execution,
    never a part of the state.  The state collapses to the temporary
    environment [temp_env = PTree.t val], the direct counterpart of IMP's
    [store].

    ** Why this is the right fragment for MISRA C / ISO 26262

    The restriction is not an artefact of the mechanisation; it is close to
    what the automotive coding standards already mandate.  MISRA C:2012
    Directive 4.12 bans dynamic memory allocation outright, and ISO 26262-6
    Table 6 lists "no dynamic objects or variables" and "no unconditional
    jumps" among its highly-recommended design principles for ASIL C/D.
    Rule 15.1 ([goto]) and Rule 17.2 (recursion) are likewise reflected here
    as the exclusion of [Sgoto]/[Slabel] and, for now, of [Scall].

    The fit is better than a coincidence: [clightgen] *computes* fragment
    membership for us.  A local whose address is never taken is placed in
    [fn_temps] and the function gets [fn_vars := nil]; a local that violates
    the discipline lands in [fn_vars] and the check fails.  We therefore do
    not have to write — or trust — an address-taken analysis of our own.

    ** What is deliberately left out, and what it costs

    - *Globals.*  Excluded in this first cut, because a global read needs
      [Genv.find_symbol] and [deref_loc], and a global write would put [mem]
      back into the state.  This is the first extension to make: reads from
      a constant memory are cheap, and writes only require the state to
      become a pair.
    - *Calls.*  Excluded for now; non-recursive direct calls to functions
      that are themselves in the fragment are a conservative extension, as
      MISRA Rule 17.2 already forbids the recursive case.
    - *[Sswitch].*  Excluded for now; it is a derived form over
      [Sifthenelse] and adds no memory.
    - *Signed overflow.*  Note that CompCert *defines* signed integer
      overflow as wrap-around rather than leaving it undefined, so a stuck
      Clight state never witnesses an overflow bug.  The undefined behaviours
      this fragment does expose are division and modulo by zero, shifts past
      the word width, and the use of an uninitialised temporary.  Catching
      overflow requires an explicit assertion layer on top; that is a
      deliberate addition, not something the C semantics gives us. *)

From Stdlib Require Import List Bool.
From compcert Require Import lib.Coqlib lib.Maps common.AST common.Values
     common.Memory cfrontend.Ctypes cfrontend.Cop cfrontend.Clight.

Import ListNotations.
Local Open Scope bool_scope.

(** ** Expressions

    Everything that reads or writes memory is rejected.  What remains —
    constants, temporaries, and the pure operators over them — is evaluated
    by [CEval.ceval] as a total function into [option val]. *)

Fixpoint expr_frag (a: expr) : bool :=
  match a with
  | Econst_int _ _ | Econst_float _ _ | Econst_single _ _ | Econst_long _ _ => true
  | Etempvar _ _ => true
  | Esizeof _ _ | Ealignof _ _ => true
  | Eunop _ a1 _ => expr_frag a1
  | Ebinop _ a1 a2 _ => expr_frag a1 && expr_frag a2
  | Ecast a1 _ => expr_frag a1
  (** The four l-value forms, i.e. precisely the expressions that
      [eval_lvalue] relates.  Rejecting them is what makes
      [CEval.eval_lvalue_frag] — "no sub-expression is ever an l-value" —
      provable. *)
  | Evar _ _ | Ederef _ _ | Eaddrof _ _ | Efield _ _ _ => false
  end.

Lemma expr_frag_not_lvalue:
  forall a, expr_frag a = true ->
  match a with
  | Evar _ _ | Ederef _ _ | Efield _ _ _ => False
  | _ => True
  end.
Proof. intros a H. destruct a; simpl in H; try discriminate; exact I. Qed.

(** ** Statements

    [Sassign] writes to memory and [Sbuiltin] may do anything at all, so
    both go.  [Sgoto]/[Slabel] are excluded on MISRA Rule 15.1 grounds
    rather than semantic ones: they would force the proof system to reason
    about [find_label] and so about the whole function body at every jump. *)

Fixpoint stmt_frag (s: statement) : bool :=
  match s with
  | Sskip | Sbreak | Scontinue => true
  | Sset _ a => expr_frag a
  | Sreturn None => true
  | Sreturn (Some a) => expr_frag a
  | Ssequence s1 s2 => stmt_frag s1 && stmt_frag s2
  | Sifthenelse a s1 s2 => expr_frag a && stmt_frag s1 && stmt_frag s2
  | Sloop s1 s2 => stmt_frag s1 && stmt_frag s2
  | Sassign _ _ => false                (**r writes memory *)
  | Scall _ _ _ => false                (**r not yet; see the header *)
  | Sbuiltin _ _ _ _ => false           (**r arbitrary effects, incl. malloc *)
  | Sswitch _ _ => false                (**r not yet; see the header *)
  | Slabel _ _ | Sgoto _ => false       (**r MISRA C:2012 Rule 15.1 *)
  end.

(** The derived C loops stay inside the fragment, which is what makes the
    fragment usable on real [clightgen] output: [Swhile], [Sdowhile] and
    [Sfor] all elaborate to [Sloop] over in-fragment pieces. *)

Lemma stmt_frag_Swhile:
  forall a s, expr_frag a = true -> stmt_frag s = true ->
  stmt_frag (Swhile a s) = true.
Proof. intros a s Ha Hs. simpl. rewrite Ha, Hs. reflexivity. Qed.

Lemma stmt_frag_Sdowhile:
  forall a s, expr_frag a = true -> stmt_frag s = true ->
  stmt_frag (Sdowhile s a) = true.
Proof. intros a s Ha Hs. simpl. rewrite Ha, Hs. reflexivity. Qed.

Lemma stmt_frag_Sfor:
  forall s1 a s2 s3,
  stmt_frag s1 = true -> expr_frag a = true ->
  stmt_frag s2 = true -> stmt_frag s3 = true ->
  stmt_frag (Sfor s1 a s2 s3) = true.
Proof.
  intros s1 a s2 s3 H1 Ha H2 H3. simpl.
  rewrite H1, Ha, H2, H3. reflexivity.
Qed.

(** ** Functions

    The two halves of the discipline: [fn_vars] empty (nothing is
    allocated) and a body that never touches memory. *)

Definition function_frag (f: function) : bool :=
  match fn_vars f with [] => true | _ :: _ => false end
  && stmt_frag (fn_body f).

Lemma function_frag_vars:
  forall f, function_frag f = true -> fn_vars f = [].
Proof.
  intros f H. unfold function_frag in H.
  apply andb_prop in H as [H _].
  destruct (fn_vars f); [reflexivity | discriminate].
Qed.

Lemma function_frag_body:
  forall f, function_frag f = true -> stmt_frag (fn_body f) = true.
Proof.
  intros f H. unfold function_frag in H.
  apply andb_prop in H as [_ H]. exact H.
Qed.

(** ** Allocation-freedom, semantically

    This is the theorem the fragment is named after.  Under the entry
    semantics of [Clight.semantics2], a function with no [fn_vars] neither
    allocates nor installs a non-empty local environment: the memory it
    starts from is the memory it is handed, and every variable it can name
    is a temporary. *)

Theorem function_entry2_alloc_free:
  forall ge f vargs m e le m',
  fn_vars f = [] ->
  function_entry2 ge f vargs m e le m' ->
  e = empty_env /\ m' = m.
Proof.
  intros ge f vargs m e le m' Hvars ENTRY.
  destruct ENTRY as [_ _ _ ALLOC _].
  rewrite Hvars in ALLOC. inv ALLOC. split; reflexivity.
Qed.

(** The temporary environment a call starts in: the parameters bound to the
    incoming arguments, every other temporary undefined.  [Vundef] is not an
    error in CompCert — it propagates until it reaches an operation, which
    then has no defined result.  That is precisely how the use of an
    uninitialised variable turns into a stuck state, i.e. into a bug this
    logic can report. *)

Definition entry_temps (f: function) (vargs: list val) : option temp_env :=
  bind_parameter_temps (fn_params f) vargs (create_undef_temps (fn_temps f)).

Lemma function_entry2_temps:
  forall ge f vargs m e le m',
  function_entry2 ge f vargs m e le m' ->
  entry_temps f vargs = Some le.
Proof. intros. destruct H as [_ _ _ _ BIND]. exact BIND. Qed.
