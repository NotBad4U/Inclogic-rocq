(** * Incorrectness triples proved by automated search

  Same programs as [ExampleInc.v] and [ExampleIncSP.v], but nothing is supplied
  by hand: no annotated copy of the program, no loop invariant, no forwards
  variant, no assignment witness, no iteration count.  Each proof is

<<
      Proof. il_auto. Qed.
>>

  [il_auto] reifies the command into [SP.acom] with the canonical [Istar]
  annotation, discharges [vcond], and searches for the post inclusion.  See
  [IncElpi.v] for how, and for the two facts that make it feasible: the
  annotation nobody has to invent, and applying rules with Ltac [apply].

  ** Coverage

  What follows is the honest boundary, established by measurement:

  - loops whose body is branch-free: fine to the search depth ([loop1]);
  - loops whose body contains an [IF], on both the [ok] and the [err] exit
    ([e1], [loop2s]);
  - [NONDET], whose witness is not determined by the assignment that consumes
    it and is found by backtracking over the values the program mentions
    ([loop0]);
  - a bug reachable only after a large, fixed number of turns — O'Hearn's
    [loop2] errors at 2,000,000 — is out of reach by construction: the search
    unrolls, so it finds bugs at small depth.  That example keeps its
    hand-written invariant in [ExampleIncSP.v].
  - [client0] (an [ERROR] guarded by a test, *after* a loop containing
    [NONDET]) is not currently found; see the note at the end of the file. *)

From Stdlib Require Import Arith ZArith Psatz Bool String List.
From mathcomp Require Import ssrbool eqtype choice.
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import finmap.
Set Warnings "notation-incompatible-prefix".
From IncLogic Require Import Imp Sequences Hoare Inc IncElpi.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope com_scope.

(** ** loop1 — Fig 5, lines 18-24: [x := 0; (x := x+1)*] *)

Definition loop1 : com :=
  ASSIGN "x" (CONST 0) ;; ((ASSIGN "x" (PLUS (VAR "x") (CONST 1))) ★).

(** Zero turns. *)
Lemma loop1_reaches_0 :
  ⟦⟦ fun _ => True ⟧⟧ loop1
  ⟦⟦ ok ↑ (fun s : store => s "x" = 0 /\ "x" \in domf s) ⟧⟧.
Proof. il_auto. Qed.

(** Three turns — the depth is found, not given. *)
Lemma loop1_reaches_3 :
  ⟦⟦ fun _ => True ⟧⟧ loop1
  ⟦⟦ ok ↑ (fun s : store => s "x" = 3 /\ "x" \in domf s) ⟧⟧.
Proof. il_auto. Qed.

(** ** A branching loop body

    [slp_ok P (CHOICE c1 c2)] mentions [P] twice, which is what makes the
    unfolded post exponential in the number of turns; the search never unfolds
    it, so this costs no more than the branch-free case. *)

Definition e1 : com :=
  ASSIGN "x" (CONST 0) ;;
  (((IF (EQUAL (VAR "x") (CONST 9)) THEN ERROR END) ;;
     ASSIGN "x" (PLUS (VAR "x") (CONST 1))) ★).

Lemma e1_reaches_2 :
  ⟦⟦ fun _ => True ⟧⟧ e1 ⟦⟦ ok ↑ (fun s : store => s "x" = 2) ⟧⟧.
Proof. il_auto. Qed.

(** ** An error, found

    Loop-free first: [x := 3; if x = 3 then error]. *)

Definition e0 : com :=
  ASSIGN "x" (CONST 3) ;; (IF (EQUAL (VAR "x") (CONST 3)) THEN ERROR END).

Lemma e0_bug : ⟦⟦ fun _ => True ⟧⟧ e0 ⟦⟦ err ↑ (fun s : store => s "x" = 3) ⟧⟧.
Proof. il_auto. Qed.

(** [loop2] of Fig 5, lines 32-38, with the bound brought within unrolling
    range.  The faulting exit is inside the loop body, so the search has to
    take [slp_err] through the annotation and back into an [ok] search for the
    state at which the body faults. *)

Definition loop2s : com :=
  ASSIGN "x" (CONST 0) ;;
  (((IF (EQUAL (VAR "x") (CONST 3)) THEN ERROR END) ;;
     ASSIGN "x" (PLUS (VAR "x") (CONST 1))) ★).

Lemma loop2s_bug :
  ⟦⟦ fun _ => True ⟧⟧ loop2s ⟦⟦ err ↑ (fun s : store => s "x" = 3) ⟧⟧.
Proof. il_auto. Qed.

(** ** loop0 — Fig 5, lines 3-10, with [NONDET]

    [n := nondet(); x := 0; while n > 0 do x := x + n; n := nondet() done]

    The witness for a [NONDET] is constrained only by what a *later* assignment
    does with it — here [x := x + n] forces the first [n] to be the final [x].
    The search backtracks over the values the program mentions rather than
    solving for it. *)

Definition loop0 : com :=
  NONDET "n" ;; ASSIGN "x" (CONST 0) ;;
  WHILE (GREATER (VAR "n") (CONST 0)) DO
    ASSIGN "x" (PLUS (VAR "x") (VAR "n")) ;; NONDET "n"
  END.

Lemma loop0_reaches_5 :
  ⟦⟦ fun _ => True ⟧⟧ loop0
  ⟦⟦ ok ↑ (fun s : store => s "x" = 5 /\ s "n" <= 0
                            /\ "x" \in domf s /\ "n" \in domf s) ⟧⟧.
Proof. il_auto. Qed.

(** ** Known gap: [client0]

<<
  Definition client0 : com :=
    loop0 ;; IF (EQUAL (VAR "x") (CONST 5)) THEN ERROR END.

  Lemma client0_bug :
    ⟦⟦ fun _ => True ⟧⟧ client0
    ⟦⟦ err ↑ (fun s : store => s "x" = 5 /\ s "n" <= 0 /\ "n" \in domf s) ⟧⟧.
  Proof. il_auto. Qed.   (* fails *)
>>

  Composing the two features above — an [ERROR] guarded by a test, reached
  after a loop containing [NONDET] — is not found.  Logging the leaves the
  search cannot close shows them to be store-domain goals of the shape
  [x \in domf (update y v s)]: the post constrains [n] but says nothing about
  [x], so membership has to be recovered from [s x <> 0] *underneath* the
  [update]s the loop body left behind.

  A domain solver that peels those [update]s does close them, but it also makes
  strictly more branches survive, and the resulting wider search turned
  [e1_reaches_2] from 0.5 s into 8.5 minutes.  Making the search cheap enough
  to afford the stronger leaf solver is the open problem here; [client0] keeps
  its hand-written proof in [ExampleIncSP.v] meanwhile. *)
