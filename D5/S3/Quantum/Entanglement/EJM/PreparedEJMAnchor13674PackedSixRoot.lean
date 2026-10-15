/- Prepared, uncompiled; no kernel acceptance is asserted.
Actual depth13/code4/index674 only. Source-sized cell bindings and
structural broadcasts preserve all original 20 coordinates, four
values, Int offsets and scale 6987435. No native source premise. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedBucket00
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket01
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket02
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket03
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket04
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket05
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixTables
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixTerminal
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group00
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group01
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group02
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group03
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group04
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group05
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group06
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group07
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group08
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group09
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group10
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group11
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group12
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group13
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group14
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group15
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group16
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group17
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VEGroups
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixRoot
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)

private def group00_normalizationCheck : Bool :=
  all4 (fun x13 => all4 (fun x15 => all4 (fun x16 => decide ((6987435 : ℤ) * (242378067 + TransientEJMAnchor13674VEGroups.table00 x13 x15 x16) = TransientEJMAnchor13674Group02.table x13 x15 x16))))

set_option trace.profiler true in
private theorem group00_normalizationChecked : group00_normalizationCheck = true := by
  decide +kernel

theorem group00_normalization (x13 x15 x16 : Fin 4) :
    (6987435 : ℤ) * (242378067 + TransientEJMAnchor13674VEGroups.table00 x13 x15 x16) = TransientEJMAnchor13674Group02.table x13 x15 x16 := by
  have h0 := group00_normalizationChecked
  unfold group00_normalizationCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x15
  have h3 := all4_sound h2 x16
  exact of_decide_eq_true h3

private def group01_normalizationCheck : Bool :=
  all4 (fun x14 => all4 (fun x17 => decide ((6987435 : ℤ) * (49042984 + TransientEJMAnchor13674VEGroups.table01 x14 x17) = TransientEJMAnchor13674Group11.table x14 x17)))

set_option trace.profiler true in
private theorem group01_normalizationChecked : group01_normalizationCheck = true := by
  decide +kernel

theorem group01_normalization (x14 x17 : Fin 4) :
    (6987435 : ℤ) * (49042984 + TransientEJMAnchor13674VEGroups.table01 x14 x17) = TransientEJMAnchor13674Group11.table x14 x17 := by
  have h0 := group01_normalizationChecked
  unfold group01_normalizationCheck at h0
  have h1 := all4_sound h0 x14
  have h2 := all4_sound h1 x17
  exact of_decide_eq_true h2

private def group02_normalizationCheck : Bool :=
  all4 (fun x13 => all4 (fun x16 => all4 (fun x17 => decide ((6987435 : ℤ) * (864011156 + TransientEJMAnchor13674VEGroups.table02 x13 x16 x17) = TransientEJMAnchor13674Group05.table x13 x16 x17))))

set_option trace.profiler true in
private theorem group02_normalizationChecked : group02_normalizationCheck = true := by
  decide +kernel

theorem group02_normalization (x13 x16 x17 : Fin 4) :
    (6987435 : ℤ) * (864011156 + TransientEJMAnchor13674VEGroups.table02 x13 x16 x17) = TransientEJMAnchor13674Group05.table x13 x16 x17 := by
  have h0 := group02_normalizationChecked
  unfold group02_normalizationCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x16
  have h3 := all4_sound h2 x17
  exact of_decide_eq_true h3

private def group03_normalizationCheck : Bool :=
  all4 (fun x14 => all4 (fun x15 => all4 (fun x16 => all4 (fun x17 => decide ((6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table03 x14 x15 x16 x17) = TransientEJMAnchor13674Group08.table x14 x15 x16 x17)))))

set_option trace.profiler true in
private theorem group03_normalizationChecked : group03_normalizationCheck = true := by
  decide +kernel

theorem group03_normalization (x14 x15 x16 x17 : Fin 4) :
    (6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table03 x14 x15 x16 x17) = TransientEJMAnchor13674Group08.table x14 x15 x16 x17 := by
  have h0 := group03_normalizationChecked
  unfold group03_normalizationCheck at h0
  have h1 := all4_sound h0 x14
  have h2 := all4_sound h1 x15
  have h3 := all4_sound h2 x16
  have h4 := all4_sound h3 x17
  exact of_decide_eq_true h4

private def group04_normalizationCheck : Bool :=
  all4 (fun x13 => all4 (fun x15 => all4 (fun x18 => decide ((6987435 : ℤ) * (242378067 + TransientEJMAnchor13674VEGroups.table04 x13 x15 x18) = TransientEJMAnchor13674Group04.table x13 x15 x18))))

set_option trace.profiler true in
private theorem group04_normalizationChecked : group04_normalizationCheck = true := by
  decide +kernel

theorem group04_normalization (x13 x15 x18 : Fin 4) :
    (6987435 : ℤ) * (242378067 + TransientEJMAnchor13674VEGroups.table04 x13 x15 x18) = TransientEJMAnchor13674Group04.table x13 x15 x18 := by
  have h0 := group04_normalizationChecked
  unfold group04_normalizationCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x15
  have h3 := all4_sound h2 x18
  exact of_decide_eq_true h3

private def group05_normalizationCheck : Bool :=
  all4 (fun x13 => all4 (fun x16 => all4 (fun x18 => decide ((6987435 : ℤ) * (49042984 + TransientEJMAnchor13674VEGroups.table05 x13 x16 x18) = TransientEJMAnchor13674Group06.table x13 x16 x18))))

set_option trace.profiler true in
private theorem group05_normalizationChecked : group05_normalizationCheck = true := by
  decide +kernel

theorem group05_normalization (x13 x16 x18 : Fin 4) :
    (6987435 : ℤ) * (49042984 + TransientEJMAnchor13674VEGroups.table05 x13 x16 x18) = TransientEJMAnchor13674Group06.table x13 x16 x18 := by
  have h0 := group05_normalizationChecked
  unfold group05_normalizationCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x16
  have h3 := all4_sound h2 x18
  exact of_decide_eq_true h3

private def group06_normalizationCheck : Bool :=
  all4 (fun x14 => all4 (fun x16 => all4 (fun x18 => decide ((6987435 : ℤ) * (130781290 + TransientEJMAnchor13674VEGroups.table06 x14 x16 x18) = TransientEJMAnchor13674Group10.table x14 x16 x18))))

set_option trace.profiler true in
private theorem group06_normalizationChecked : group06_normalizationCheck = true := by
  decide +kernel

theorem group06_normalization (x14 x16 x18 : Fin 4) :
    (6987435 : ℤ) * (130781290 + TransientEJMAnchor13674VEGroups.table06 x14 x16 x18) = TransientEJMAnchor13674Group10.table x14 x16 x18 := by
  have h0 := group06_normalizationChecked
  unfold group06_normalizationCheck at h0
  have h1 := all4_sound h0 x14
  have h2 := all4_sound h1 x16
  have h3 := all4_sound h2 x18
  exact of_decide_eq_true h3

private def group07_normalizationCheck : Bool :=
  all4 (fun x15 => all4 (fun x16 => all4 (fun x18 => decide ((6987435 : ℤ) * (49042984 + TransientEJMAnchor13674VEGroups.table07 x15 x16 x18) = TransientEJMAnchor13674Group14.table x15 x16 x18))))

set_option trace.profiler true in
private theorem group07_normalizationChecked : group07_normalizationCheck = true := by
  decide +kernel

theorem group07_normalization (x15 x16 x18 : Fin 4) :
    (6987435 : ℤ) * (49042984 + TransientEJMAnchor13674VEGroups.table07 x15 x16 x18) = TransientEJMAnchor13674Group14.table x15 x16 x18 := by
  have h0 := group07_normalizationChecked
  unfold group07_normalizationCheck at h0
  have h1 := all4_sound h0 x15
  have h2 := all4_sound h1 x16
  have h3 := all4_sound h2 x18
  exact of_decide_eq_true h3

private def group08_normalizationCheck : Bool :=
  all4 (fun x13 => all4 (fun x14 => all4 (fun x17 => all4 (fun x18 => decide ((6987435 : ℤ) * (864011156 + TransientEJMAnchor13674VEGroups.table08 x13 x14 x17 x18) = TransientEJMAnchor13674Group01.table x13 x14 x17 x18)))))

set_option trace.profiler true in
private theorem group08_normalizationChecked : group08_normalizationCheck = true := by
  decide +kernel

theorem group08_normalization (x13 x14 x17 x18 : Fin 4) :
    (6987435 : ℤ) * (864011156 + TransientEJMAnchor13674VEGroups.table08 x13 x14 x17 x18) = TransientEJMAnchor13674Group01.table x13 x14 x17 x18 := by
  have h0 := group08_normalizationChecked
  unfold group08_normalizationCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x14
  have h3 := all4_sound h2 x17
  have h4 := all4_sound h3 x18
  exact of_decide_eq_true h4

private def group09_normalizationCheck : Bool :=
  all4 (fun x15 => all4 (fun x17 => all4 (fun x18 => decide ((6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table09 x15 x17 x18) = TransientEJMAnchor13674Group16.table x15 x17 x18))))

set_option trace.profiler true in
private theorem group09_normalizationChecked : group09_normalizationCheck = true := by
  decide +kernel

theorem group09_normalization (x15 x17 x18 : Fin 4) :
    (6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table09 x15 x17 x18) = TransientEJMAnchor13674Group16.table x15 x17 x18 := by
  have h0 := group09_normalizationChecked
  unfold group09_normalizationCheck at h0
  have h1 := all4_sound h0 x15
  have h2 := all4_sound h1 x17
  have h3 := all4_sound h2 x18
  exact of_decide_eq_true h3

private def group10_normalizationCheck : Bool :=
  all4 (fun x14 => all4 (fun x19 => decide ((6987435 : ℤ) * (49042984 + TransientEJMAnchor13674VEGroups.table10 x14 x19) = TransientEJMAnchor13674Group13.table x14 x19)))

set_option trace.profiler true in
private theorem group10_normalizationChecked : group10_normalizationCheck = true := by
  decide +kernel

theorem group10_normalization (x14 x19 : Fin 4) :
    (6987435 : ℤ) * (49042984 + TransientEJMAnchor13674VEGroups.table10 x14 x19) = TransientEJMAnchor13674Group13.table x14 x19 := by
  have h0 := group10_normalizationChecked
  unfold group10_normalizationCheck at h0
  have h1 := all4_sound h0 x14
  have h2 := all4_sound h1 x19
  exact of_decide_eq_true h2

private def group11_normalizationCheck : Bool :=
  all4 (fun x13 => all4 (fun x14 => all4 (fun x16 => all4 (fun x19 => decide ((6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table11 x13 x14 x16 x19) = TransientEJMAnchor13674Group00.table x13 x14 x16 x19)))))

set_option trace.profiler true in
private theorem group11_normalizationChecked : group11_normalizationCheck = true := by
  decide +kernel

theorem group11_normalization (x13 x14 x16 x19 : Fin 4) :
    (6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table11 x13 x14 x16 x19) = TransientEJMAnchor13674Group00.table x13 x14 x16 x19 := by
  have h0 := group11_normalizationChecked
  unfold group11_normalizationCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x14
  have h3 := all4_sound h2 x16
  have h4 := all4_sound h3 x19
  exact of_decide_eq_true h4

private def group12_normalizationCheck : Bool :=
  all4 (fun x15 => all4 (fun x16 => all4 (fun x19 => decide ((6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table12 x15 x16 x19) = TransientEJMAnchor13674Group15.table x15 x16 x19))))

set_option trace.profiler true in
private theorem group12_normalizationChecked : group12_normalizationCheck = true := by
  decide +kernel

theorem group12_normalization (x15 x16 x19 : Fin 4) :
    (6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table12 x15 x16 x19) = TransientEJMAnchor13674Group15.table x15 x16 x19 := by
  have h0 := group12_normalizationChecked
  unfold group12_normalizationCheck at h0
  have h1 := all4_sound h0 x15
  have h2 := all4_sound h1 x16
  have h3 := all4_sound h2 x19
  exact of_decide_eq_true h3

private def group13_normalizationCheck : Bool :=
  all4 (fun x17 => all4 (fun x19 => decide ((6987435 : ℤ) * (242378067 + TransientEJMAnchor13674VEGroups.table13 x17 x19) = TransientEJMAnchor13674Group17.table x17 x19)))

set_option trace.profiler true in
private theorem group13_normalizationChecked : group13_normalizationCheck = true := by
  decide +kernel

theorem group13_normalization (x17 x19 : Fin 4) :
    (6987435 : ℤ) * (242378067 + TransientEJMAnchor13674VEGroups.table13 x17 x19) = TransientEJMAnchor13674Group17.table x17 x19 := by
  have h0 := group13_normalizationChecked
  unfold group13_normalizationCheck at h0
  have h1 := all4_sound h0 x17
  have h2 := all4_sound h1 x19
  exact of_decide_eq_true h2

private def group14_normalizationCheck : Bool :=
  all4 (fun x14 => all4 (fun x17 => all4 (fun x19 => decide ((6987435 : ℤ) * (242378067 + TransientEJMAnchor13674VEGroups.table14 x14 x17 x19) = TransientEJMAnchor13674Group12.table x14 x17 x19))))

set_option trace.profiler true in
private theorem group14_normalizationChecked : group14_normalizationCheck = true := by
  decide +kernel

theorem group14_normalization (x14 x17 x19 : Fin 4) :
    (6987435 : ℤ) * (242378067 + TransientEJMAnchor13674VEGroups.table14 x14 x17 x19) = TransientEJMAnchor13674Group12.table x14 x17 x19 := by
  have h0 := group14_normalizationChecked
  unfold group14_normalizationCheck at h0
  have h1 := all4_sound h0 x14
  have h2 := all4_sound h1 x17
  have h3 := all4_sound h2 x19
  exact of_decide_eq_true h3

private def group15_normalizationCheck : Bool :=
  all4 (fun x13 => all4 (fun x15 => all4 (fun x17 => all4 (fun x19 => decide ((6987435 : ℤ) * (582842102 + TransientEJMAnchor13674VEGroups.table15 x13 x15 x17 x19) = TransientEJMAnchor13674Group03.table x13 x15 x17 x19)))))

set_option trace.profiler true in
private theorem group15_normalizationChecked : group15_normalizationCheck = true := by
  decide +kernel

theorem group15_normalization (x13 x15 x17 x19 : Fin 4) :
    (6987435 : ℤ) * (582842102 + TransientEJMAnchor13674VEGroups.table15 x13 x15 x17 x19) = TransientEJMAnchor13674Group03.table x13 x15 x17 x19 := by
  have h0 := group15_normalizationChecked
  unfold group15_normalizationCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x15
  have h3 := all4_sound h2 x17
  have h4 := all4_sound h3 x19
  exact of_decide_eq_true h4

private def group16_normalizationCheck : Bool :=
  all4 (fun x13 => all4 (fun x18 => all4 (fun x19 => decide ((6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table16 x13 x18 x19) = TransientEJMAnchor13674Group07.table x13 x18 x19))))

set_option trace.profiler true in
private theorem group16_normalizationChecked : group16_normalizationCheck = true := by
  decide +kernel

theorem group16_normalization (x13 x18 x19 : Fin 4) :
    (6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table16 x13 x18 x19) = TransientEJMAnchor13674Group07.table x13 x18 x19 := by
  have h0 := group16_normalizationChecked
  unfold group16_normalizationCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x18
  have h3 := all4_sound h2 x19
  exact of_decide_eq_true h3

private def group17_normalizationCheck : Bool :=
  all4 (fun x14 => all4 (fun x15 => all4 (fun x18 => all4 (fun x19 => decide ((6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table17 x14 x15 x18 x19) = TransientEJMAnchor13674Group09.table x14 x15 x18 x19)))))

set_option trace.profiler true in
private theorem group17_normalizationChecked : group17_normalizationCheck = true := by
  decide +kernel

theorem group17_normalization (x14 x15 x18 x19 : Fin 4) :
    (6987435 : ℤ) * ((-597676414) + TransientEJMAnchor13674VEGroups.table17 x14 x15 x18 x19) = TransientEJMAnchor13674Group09.table x14 x15 x18 x19 := by
  have h0 := group17_normalizationChecked
  unfold group17_normalizationCheck at h0
  have h1 := all4_sound h0 x14
  have h2 := all4_sound h1 x15
  have h3 := all4_sound h2 x18
  have h4 := all4_sound h3 x19
  exact of_decide_eq_true h4

def value0 (e : Assignment) : ℤ := (6987435 : ℤ) * (21271424 + TransientEJMAnchor13674VEGroups.table00 (e 13) (e 15) (e 16) + TransientEJMAnchor13674VEGroups.table01 (e 14) (e 17) + TransientEJMAnchor13674VEGroups.table02 (e 13) (e 16) (e 17) + TransientEJMAnchor13674VEGroups.table03 (e 14) (e 15) (e 16) (e 17) + TransientEJMAnchor13674VEGroups.table04 (e 13) (e 15) (e 18) + TransientEJMAnchor13674VEGroups.table05 (e 13) (e 16) (e 18) + TransientEJMAnchor13674VEGroups.table06 (e 14) (e 16) (e 18) + TransientEJMAnchor13674VEGroups.table07 (e 15) (e 16) (e 18) + TransientEJMAnchor13674VEGroups.table08 (e 13) (e 14) (e 17) (e 18) + TransientEJMAnchor13674VEGroups.table09 (e 15) (e 17) (e 18) + TransientEJMAnchor13674VEGroups.table10 (e 14) (e 19) + TransientEJMAnchor13674VEGroups.table11 (e 13) (e 14) (e 16) (e 19) + TransientEJMAnchor13674VEGroups.table12 (e 15) (e 16) (e 19) + TransientEJMAnchor13674VEGroups.table13 (e 17) (e 19) + TransientEJMAnchor13674VEGroups.table14 (e 14) (e 17) (e 19) + TransientEJMAnchor13674VEGroups.table15 (e 13) (e 15) (e 17) (e 19) + TransientEJMAnchor13674VEGroups.table16 (e 13) (e 18) (e 19) + TransientEJMAnchor13674VEGroups.table17 (e 14) (e 15) (e 18) (e 19))

def value1 (e : Assignment) : ℤ := (6987435 : ℤ) * (21271424 + TransientEJMAnchor13674VEGroups.table01 (e 14) (e 17) + TransientEJMAnchor13674VEGroups.table03 (e 14) (e 15) (e 16) (e 17) + TransientEJMAnchor13674VEGroups.table06 (e 14) (e 16) (e 18) + TransientEJMAnchor13674VEGroups.table07 (e 15) (e 16) (e 18) + TransientEJMAnchor13674VEGroups.table09 (e 15) (e 17) (e 18) + TransientEJMAnchor13674VEGroups.table10 (e 14) (e 19) + TransientEJMAnchor13674VEGroups.table12 (e 15) (e 16) (e 19) + TransientEJMAnchor13674VEGroups.table13 (e 17) (e 19) + TransientEJMAnchor13674VEGroups.table14 (e 14) (e 17) (e 19) + TransientEJMAnchor13674VEGroups.table17 (e 14) (e 15) (e 18) (e 19) + PreparedEJMAnchor13674PackedOutput.outputTable (e 14) (e 15) (e 16) (e 17) (e 18) (e 19))

def value2 (e : Assignment) : ℤ := (6987435 : ℤ) * (21271424 + TransientEJMAnchor13674VEGroups.table01 (e 14) (e 17) + TransientEJMAnchor13674VEGroups.table09 (e 15) (e 17) (e 18) + TransientEJMAnchor13674VEGroups.table10 (e 14) (e 19) + TransientEJMAnchor13674VEGroups.table13 (e 17) (e 19) + TransientEJMAnchor13674VEGroups.table14 (e 14) (e 17) (e 19) + TransientEJMAnchor13674VEGroups.table17 (e 14) (e 15) (e 18) (e 19) + PreparedEJMAnchor13674PackedSixTables.table19 (e 14) (e 15) (e 17) (e 18) (e 19))

def value3 (e : Assignment) : ℤ := (6987435 : ℤ) * (21271424 + TransientEJMAnchor13674VEGroups.table01 (e 14) (e 17) + TransientEJMAnchor13674VEGroups.table10 (e 14) (e 19) + TransientEJMAnchor13674VEGroups.table13 (e 17) (e 19) + TransientEJMAnchor13674VEGroups.table14 (e 14) (e 17) (e 19) + PreparedEJMAnchor13674PackedSixTables.table20 (e 14) (e 17) (e 18) (e 19))

def value4 (e : Assignment) : ℤ := (6987435 : ℤ) * (21271424 + TransientEJMAnchor13674VEGroups.table01 (e 14) (e 17) + TransientEJMAnchor13674VEGroups.table10 (e 14) (e 19) + TransientEJMAnchor13674VEGroups.table13 (e 17) (e 19) + TransientEJMAnchor13674VEGroups.table14 (e 14) (e 17) (e 19) + PreparedEJMAnchor13674PackedSixTables.table21 (e 14) (e 17) (e 19))

def value5 (e : Assignment) : ℤ := (6987435 : ℤ) * (21271424 + TransientEJMAnchor13674VEGroups.table13 (e 17) (e 19) + PreparedEJMAnchor13674PackedSixTables.table22 (e 17) (e 19))

def value6 (e : Assignment) : ℤ := (6987435 : ℤ) * (21271424 + PreparedEJMAnchor13674PackedSixTables.table23 (e 19))

private theorem initial_lower (e : Assignment)
    (hp : Compatible (prefixPartial 13 4) e) :
    value0 e ≤ TransientEJMAnchor13674Group02.score e + TransientEJMAnchor13674Group11.score e + TransientEJMAnchor13674Group05.score e + TransientEJMAnchor13674Group08.score e + TransientEJMAnchor13674Group04.score e + TransientEJMAnchor13674Group06.score e + TransientEJMAnchor13674Group10.score e + TransientEJMAnchor13674Group14.score e + TransientEJMAnchor13674Group01.score e + TransientEJMAnchor13674Group16.score e + TransientEJMAnchor13674Group13.score e + TransientEJMAnchor13674Group00.score e + TransientEJMAnchor13674Group15.score e + TransientEJMAnchor13674Group17.score e + TransientEJMAnchor13674Group12.score e + TransientEJMAnchor13674Group03.score e + TransientEJMAnchor13674Group07.score e + TransientEJMAnchor13674Group09.score e := by
  have h0 := TransientEJMAnchor13674Group02.bound e hp
  change TransientEJMAnchor13674Group02.table (e 13) (e 15) (e 16) ≤ TransientEJMAnchor13674Group02.score e at h0
  rw [← group00_normalization (e 13) (e 15) (e 16)] at h0
  have h1 := TransientEJMAnchor13674Group11.bound e hp
  change TransientEJMAnchor13674Group11.table (e 14) (e 17) ≤ TransientEJMAnchor13674Group11.score e at h1
  rw [← group01_normalization (e 14) (e 17)] at h1
  have h2 := TransientEJMAnchor13674Group05.bound e hp
  change TransientEJMAnchor13674Group05.table (e 13) (e 16) (e 17) ≤ TransientEJMAnchor13674Group05.score e at h2
  rw [← group02_normalization (e 13) (e 16) (e 17)] at h2
  have h3 := TransientEJMAnchor13674Group08.bound e hp
  change TransientEJMAnchor13674Group08.table (e 14) (e 15) (e 16) (e 17) ≤ TransientEJMAnchor13674Group08.score e at h3
  rw [← group03_normalization (e 14) (e 15) (e 16) (e 17)] at h3
  have h4 := TransientEJMAnchor13674Group04.bound e hp
  change TransientEJMAnchor13674Group04.table (e 13) (e 15) (e 18) ≤ TransientEJMAnchor13674Group04.score e at h4
  rw [← group04_normalization (e 13) (e 15) (e 18)] at h4
  have h5 := TransientEJMAnchor13674Group06.bound e hp
  change TransientEJMAnchor13674Group06.table (e 13) (e 16) (e 18) ≤ TransientEJMAnchor13674Group06.score e at h5
  rw [← group05_normalization (e 13) (e 16) (e 18)] at h5
  have h6 := TransientEJMAnchor13674Group10.bound e hp
  change TransientEJMAnchor13674Group10.table (e 14) (e 16) (e 18) ≤ TransientEJMAnchor13674Group10.score e at h6
  rw [← group06_normalization (e 14) (e 16) (e 18)] at h6
  have h7 := TransientEJMAnchor13674Group14.bound e hp
  change TransientEJMAnchor13674Group14.table (e 15) (e 16) (e 18) ≤ TransientEJMAnchor13674Group14.score e at h7
  rw [← group07_normalization (e 15) (e 16) (e 18)] at h7
  have h8 := TransientEJMAnchor13674Group01.bound e hp
  change TransientEJMAnchor13674Group01.table (e 13) (e 14) (e 17) (e 18) ≤ TransientEJMAnchor13674Group01.score e at h8
  rw [← group08_normalization (e 13) (e 14) (e 17) (e 18)] at h8
  have h9 := TransientEJMAnchor13674Group16.bound e hp
  change TransientEJMAnchor13674Group16.table (e 15) (e 17) (e 18) ≤ TransientEJMAnchor13674Group16.score e at h9
  rw [← group09_normalization (e 15) (e 17) (e 18)] at h9
  have h10 := TransientEJMAnchor13674Group13.bound e hp
  change TransientEJMAnchor13674Group13.table (e 14) (e 19) ≤ TransientEJMAnchor13674Group13.score e at h10
  rw [← group10_normalization (e 14) (e 19)] at h10
  have h11 := TransientEJMAnchor13674Group00.bound e hp
  change TransientEJMAnchor13674Group00.table (e 13) (e 14) (e 16) (e 19) ≤ TransientEJMAnchor13674Group00.score e at h11
  rw [← group11_normalization (e 13) (e 14) (e 16) (e 19)] at h11
  have h12 := TransientEJMAnchor13674Group15.bound e hp
  change TransientEJMAnchor13674Group15.table (e 15) (e 16) (e 19) ≤ TransientEJMAnchor13674Group15.score e at h12
  rw [← group12_normalization (e 15) (e 16) (e 19)] at h12
  have h13 := TransientEJMAnchor13674Group17.bound e hp
  change TransientEJMAnchor13674Group17.table (e 17) (e 19) ≤ TransientEJMAnchor13674Group17.score e at h13
  rw [← group13_normalization (e 17) (e 19)] at h13
  have h14 := TransientEJMAnchor13674Group12.bound e hp
  change TransientEJMAnchor13674Group12.table (e 14) (e 17) (e 19) ≤ TransientEJMAnchor13674Group12.score e at h14
  rw [← group14_normalization (e 14) (e 17) (e 19)] at h14
  have h15 := TransientEJMAnchor13674Group03.bound e hp
  change TransientEJMAnchor13674Group03.table (e 13) (e 15) (e 17) (e 19) ≤ TransientEJMAnchor13674Group03.score e at h15
  rw [← group15_normalization (e 13) (e 15) (e 17) (e 19)] at h15
  have h16 := TransientEJMAnchor13674Group07.bound e hp
  change TransientEJMAnchor13674Group07.table (e 13) (e 18) (e 19) ≤ TransientEJMAnchor13674Group07.score e at h16
  rw [← group16_normalization (e 13) (e 18) (e 19)] at h16
  have h17 := TransientEJMAnchor13674Group09.bound e hp
  change TransientEJMAnchor13674Group09.table (e 14) (e 15) (e 18) (e 19) ≤ TransientEJMAnchor13674Group09.score e at h17
  rw [← group17_normalization (e 14) (e 15) (e 18) (e 19)] at h17
  have combined := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17
  unfold value0
  convert combined using 1 <;> ring

private theorem step0_lower (e : Assignment) : value1 e ≤ value0 e := by
  have h := mul_le_mul_of_nonneg_left (PreparedEJMAnchor13674PackedBucket00.inequality_at e)
    (by decide : (0 : ℤ) ≤ 6987435)
  unfold value1 value0
  linarith only [h]

private theorem step1_lower (e : Assignment) : value2 e ≤ value1 e := by
  have h := mul_le_mul_of_nonneg_left (PreparedEJMAnchor13674PackedSixBucket01.inequality_at e)
    (by decide : (0 : ℤ) ≤ 6987435)
  unfold value2 value1
  linarith only [h]

private theorem step2_lower (e : Assignment) : value3 e ≤ value2 e := by
  have h := mul_le_mul_of_nonneg_left (PreparedEJMAnchor13674PackedSixBucket02.inequality_at e)
    (by decide : (0 : ℤ) ≤ 6987435)
  unfold value3 value2
  linarith only [h]

private theorem step3_lower (e : Assignment) : value4 e ≤ value3 e := by
  have h := mul_le_mul_of_nonneg_left (PreparedEJMAnchor13674PackedSixBucket03.inequality_at e)
    (by decide : (0 : ℤ) ≤ 6987435)
  unfold value4 value3
  linarith only [h]

private theorem step4_lower (e : Assignment) : value5 e ≤ value4 e := by
  have h := mul_le_mul_of_nonneg_left (PreparedEJMAnchor13674PackedSixBucket04.inequality_at e)
    (by decide : (0 : ℤ) ≤ 6987435)
  unfold value5 value4
  linarith only [h]

private theorem step5_lower (e : Assignment) : value6 e ≤ value5 e := by
  have h := mul_le_mul_of_nonneg_left (PreparedEJMAnchor13674PackedSixBucket05.inequality_at e)
    (by decide : (0 : ℤ) ≤ 6987435)
  unfold value6 value5
  linarith only [h]

private theorem final_lower (e : Assignment) :
    (6987435 : ℤ) * 21226312 ≤ value6 e := by
  exact mul_le_mul_of_nonneg_left (PreparedEJMAnchor13674PackedSixTerminal.lower_at e)
    (by decide : (0 : ℤ) ≤ 6987435)

private theorem component_sum (e : Assignment) :
    TransientEJMAnchor13674Group02.score e + TransientEJMAnchor13674Group11.score e + TransientEJMAnchor13674Group05.score e + TransientEJMAnchor13674Group08.score e + TransientEJMAnchor13674Group04.score e + TransientEJMAnchor13674Group06.score e + TransientEJMAnchor13674Group10.score e + TransientEJMAnchor13674Group14.score e + TransientEJMAnchor13674Group01.score e + TransientEJMAnchor13674Group16.score e + TransientEJMAnchor13674Group13.score e + TransientEJMAnchor13674Group00.score e + TransientEJMAnchor13674Group15.score e + TransientEJMAnchor13674Group17.score e + TransientEJMAnchor13674Group12.score e + TransientEJMAnchor13674Group03.score e + TransientEJMAnchor13674Group07.score e + TransientEJMAnchor13674Group09.score e = D5.S3.Quantum.Entanglement.EJMInflationScore.score F1 F2 e := by
  simp only [TransientEJMAnchor13674Factor00.score, TransientEJMAnchor13674Factor01.score, TransientEJMAnchor13674Factor02.score, TransientEJMAnchor13674Factor03.score, TransientEJMAnchor13674Factor04.score, TransientEJMAnchor13674Factor05.score, TransientEJMAnchor13674Factor06.score, TransientEJMAnchor13674Factor07.score, TransientEJMAnchor13674Factor08.score, TransientEJMAnchor13674Factor09.score, TransientEJMAnchor13674Factor10.score, TransientEJMAnchor13674Factor11.score, TransientEJMAnchor13674Factor12.score, TransientEJMAnchor13674Factor13.score, TransientEJMAnchor13674Factor14.score, TransientEJMAnchor13674Factor15.score, TransientEJMAnchor13674Factor16.score, TransientEJMAnchor13674Factor17.score, TransientEJMAnchor13674Factor18.score, TransientEJMAnchor13674Factor19.score, TransientEJMAnchor13674Factor20.score, TransientEJMAnchor13674Factor21.score, TransientEJMAnchor13674Factor22.score, TransientEJMAnchor13674Factor23.score, TransientEJMAnchor13674Factor24.score, TransientEJMAnchor13674Factor25.score, TransientEJMAnchor13674Factor26.score, TransientEJMAnchor13674Factor27.score, TransientEJMAnchor13674Factor28.score, TransientEJMAnchor13674Factor29.score, TransientEJMAnchor13674Factor30.score, TransientEJMAnchor13674Factor31.score, TransientEJMAnchor13674Group00.score, TransientEJMAnchor13674Group01.score, TransientEJMAnchor13674Group02.score, TransientEJMAnchor13674Group03.score, TransientEJMAnchor13674Group04.score, TransientEJMAnchor13674Group05.score, TransientEJMAnchor13674Group06.score, TransientEJMAnchor13674Group07.score, TransientEJMAnchor13674Group08.score, TransientEJMAnchor13674Group09.score, TransientEJMAnchor13674Group10.score, TransientEJMAnchor13674Group11.score, TransientEJMAnchor13674Group12.score, TransientEJMAnchor13674Group13.score, TransientEJMAnchor13674Group14.score, TransientEJMAnchor13674Group15.score, TransientEJMAnchor13674Group16.score, TransientEJMAnchor13674Group17.score,
    D5.S3.Quantum.Entanglement.EJMInflationScore.score, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  ac_rfl

theorem actual_prefix_score_bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 4) e) :
    (6987435 : ℤ) * 21226312 ≤ D5.S3.Quantum.Entanglement.EJMInflationScore.score F1 F2 e := by
  rw [← component_sum e]
  exact (final_lower e).trans ((step5_lower e).trans ((step4_lower e).trans ((step3_lower e).trans ((step2_lower e).trans ((step1_lower e).trans ((step0_lower e).trans (initial_lower e hp)))))))

theorem actual_prefix_score_lower_bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 4) e) :
    (6987435 : ℤ) ≤ D5.S3.Quantum.Entanglement.EJMInflationScore.score F1 F2 e := by
  exact (by decide : (6987435 : ℤ) ≤ 6987435 * 21226312).trans
    (actual_prefix_score_bound e hp)

#print axioms actual_prefix_score_bound
#print axioms actual_prefix_score_lower_bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixRoot
