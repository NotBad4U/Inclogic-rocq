(** * The fragment check, run on real [clightgen] output

    [CFrag.v] claims that membership of the allocation-free fragment is a
    property the C front end already computes for us, rather than an analysis
    we have to write and trust.  This file is the evidence: it takes
    [examples/misra.c] through [clightgen] — the result is
    [theories/ExampleCGen.v], checked in and regenerable with

        clightgen -normalize -o theories/ExampleCGen.v examples/misra.c

    — and decides the fragment predicate on each function by [reflexivity].

    The point of interest is [gcd].  Its body is three writes to locals and a
    loop:

<<
      Swhile (Ebinop One (Etempvar _b tint) (Econst_int (Int.repr 0) tint) tint)
        (Ssequence (Sset _t (Etempvar _b tint))
        (Ssequence (Sset _b (Ebinop Omod (Etempvar _a tint) (Etempvar _b tint) tint))
                   (Sset _a (Etempvar _t tint))))
>>

    Every one of those writes is an [Sset], not an [Sassign], because
    CompCert's [SimplLocals] pass has already placed each non-address-taken
    local in [fn_temps].  And [Sset] is exactly [Core.ASSIGN]: [step_set]
    rewrites [le] to [PTree.set id v le] and leaves [m] alone, which is
    [Lang.update] in [CLang.ClightLang], on the nose.  So writing to a local
    needs nothing beyond the signature as it stands.

    [addr_taken] is here to keep the boundary honest.  Taking [&x] puts [x]
    in [fn_vars], so the function allocates on entry and the write becomes an
    [Sassign] through an l-value; the predicate rejects it. *)

From Stdlib Require Import List.
From compcert Require Import lib.Coqlib lib.Maps common.AST common.Values
     common.Memory cfrontend.Ctypes cfrontend.Clight export.Ctypesdefs.
From IncLogic Require Import CFrag ExampleCGen.

Import ListNotations.

(** ** Inside the fragment *)

Example gcd_in_fragment : function_frag f_gcd = true.
Proof. reflexivity. Qed.

Example safe_div_in_fragment : function_frag f_safe_div = true.
Proof. reflexivity. Qed.

Example sum_in_fragment : function_frag f_sum = true.
Proof. reflexivity. Qed.

(** ** Outside it

    Not a limitation of the *check* but of the fragment: this function really
    does allocate. *)

Example addr_taken_not_in_fragment : function_frag f_addr_taken = false.
Proof. reflexivity. Qed.

Example addr_taken_allocates : fn_vars f_addr_taken = [(_x, tint)].
Proof. reflexivity. Qed.

(** ** What membership buys, semantically

    Not just a boolean: entering [gcd] provably neither allocates nor
    installs a non-empty local environment, so the memory it is handed is the
    memory it runs in.  That is what licenses [CLang.ClightLang] treating [m]
    as a parameter rather than as part of the state. *)

Lemma gcd_entry_alloc_free:
  forall ge vargs m e le m',
  function_entry2 ge f_gcd vargs m e le m' ->
  e = empty_env /\ m' = m.
Proof.
  intros ge vargs m e le m' ENTRY.
  eapply function_entry2_alloc_free; [ | exact ENTRY ].
  apply function_frag_vars. exact gcd_in_fragment.
Qed.

Lemma safe_div_entry_alloc_free:
  forall ge vargs m e le m',
  function_entry2 ge f_safe_div vargs m e le m' ->
  e = empty_env /\ m' = m.
Proof.
  intros ge vargs m e le m' ENTRY.
  eapply function_entry2_alloc_free; [ | exact ENTRY ].
  apply function_frag_vars. exact safe_div_in_fragment.
Qed.
