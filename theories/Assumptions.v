From IncLogic Require Import Hoare Inc Sil.

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