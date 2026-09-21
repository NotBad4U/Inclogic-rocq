From IncLogic Require Import Core ILang Hoare Inc Sil.

(* Language-generic core.

   These hold for *every* instance of [Lang.t] at once.  Note that the
   Clight instance ([CLang.v]) is deliberately not checked here: CompCert is
   not axiom-free — its float semantics rest on Flocq's classical reals, so
   [Cop.sem_binary_operation] alone already depends on [Classical_Prop.classic],
   [functional_extensionality_dep] and [ClassicalDedekindReals.*].  Anything
   proved about C inherits those four; the core and the IMP instance do not. *)

Print Assumptions Core.cexec_iff_reds.

Print Assumptions Core.cexec_cstar_iff_star.

Print Assumptions Core.cexec_cstar_err_iff.

Print Assumptions Core.cexec_unannot.

Print Assumptions Core.cstar_seq_comm.

(* The IMP instance, and the proof that instantiating the generic core at it
   gives back exactly the semantics of [Imp.v]. *)

Print Assumptions ILang.cexec_iff.

Print Assumptions ILang.ImpLaws.

Print Assumptions ILang.ImpFrame.



(* Hoare *)

Print Assumptions Hoare.Soundness.triple_soundness.

Print Assumptions Hoare.Soundness.Triple_soundness.

Print Assumptions Hoare.Completness.Hoare_complete.

Print Assumptions Hoare.Completness.Hoare_adequate.

Print Assumptions Hoare.WP.vcgen_sound.

Print Assumptions Hoare.TotalCorrectness.TotalTriple_soundness.

Print Assumptions Hoare.TotalCorrectness.TotalTriple_complete.

Print Assumptions Hoare.TotalCorrectness.TotalTriple_adequate.


(* Incorrectness Logic *)

Print Assumptions Inc.IncSoundness.Inc_triple_sound.

Print Assumptions Inc.IncCompleteness.Inc_complete.

Print Assumptions Inc.IncCompleteness.post_strongest_over_weakest_under.

Print Assumptions Inc.SP.vcgen_sound.


(* Sufficient Incorrectness Logic *)

Print Assumptions Sil.SilSoundness.Sil_triple_sound.

Print Assumptions Sil.SilCompleteness.Sil_complete.

Print Assumptions Sil.sp_wp_adjoint.

Print Assumptions Sil.sil_eq_total_hoare_det.