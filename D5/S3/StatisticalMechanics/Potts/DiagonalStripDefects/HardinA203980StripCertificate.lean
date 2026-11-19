/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.finite_certificate
   digest: Eight boundary classes for five-column diagonal and antidiagonal strips. -/

/-
admission_basis: open-problem-resolution (#31593; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA203980Strip.result)
representative_counts: proof_shape=bind-only; consumers=HardinA203980Strip.result, HardinA229507Strip.counting_bridge
counts: proof_shape=bind-only; consumers=HardinA203980Strip.result, HardinA229507Strip.counting_bridge
initial_counts: proof_shape=bind-only; consumers=HardinA203980Strip.result, HardinA229507Strip.counting_bridge
W: proof_shape=bind-only; consumers=HardinA203980Strip.result, HardinA229507StripCertificate.finite_certificate
powers: proof_shape=bind-only; consumers=HardinA203980Strip.result, HardinA229507StripCertificate.finite_certificate
finite_certificate: proof_shape=bind-only; consumers=HardinA203980Strip.result, HardinA229507StripCertificate.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.DiagonalSymmetry
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
open HardinA203980StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem representative_counts : ∀ i j : Fin 8,
    (∑ r : Row, if bondDefects between (representatives i) r = 0 ∧ boundary r = j
      then (1 : ℤ) else 0) = T i j := by
  intro i
  fin_cases i <;> decide +kernel

/-- Exact zero-bond-cost counts into the eight boundary classes. -/
theorem counts (p : Row) (j : Fin 8) :
    (∑ r : Row, if bondDefects between p r = 0 ∧ boundary r = j
      then (1 : ℤ) else 0) = T (boundary p) j :=
  DiagonalSymmetry.lift_counts 0 T representative_counts p j

/-- The distribution of all three-colour rows over the eight classes. -/
theorem initial_counts : ∀ j : Fin 8,
    (∑ r : Row, if boundary r = j then (1 : ℤ) else 0) = initial j := by
  decide +kernel

def W : Fin 14 → Fin 8 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1],
    ![32, 16, 8, 4, 16, 8, 8, 4],
    ![432, 216, 144, 72, 216, 108, 72, 36],
    ![6048, 2808, 2016, 936, 3024, 1404, 1008, 468],
    ![82656, 38376, 28224, 13104, 41328, 19188, 13104, 6084],
    ![1133568, 522504, 387072, 178416, 566784, 261252, 179712, 82836],
    ![15510528, 7149384, 5308416, 2446848, 7755264, 3574692, 2446848, 1127844],
    ![212300352, 97789032, 72658944, 33467904, 106150176, 48894516, 33491232, 15426612],
    ![2905222464, 1338193224, 994519296, 458091936, 1452611232, 669096612, 458091936, 211004676],
    ![39757770432, 18311855976, 13609928448, 6268536864, 19878885216, 9155927988, 6268956768, 2887391124],
    ![544070872512, 250591201416, 186250938624, 85784497632, 272035436256, 125295600708, 85784497632, 39511103076],
    ![7445438336448, 3429239497128, 2548785367296, 1173926242656, 3722719168224, 1714619748564, 1173933800928, 540693505908],
    ![101888269108416, 46927965947976, 34879324080384, 16064810473824, 50944134554208, 23463982973988, 16064810473824, 7399172500164],
    ![1394306418667968, 642192906173544, 477311724594432, 219841348690656, 697153209333984, 321096453086772, 219841484739552, 101255104396116]]

/-- Powers of the zero-cost transfer on the constant terminal vector. -/
theorem powers (i : Fin 14) : (T ^ i.val).mulVec terminal = W i := by
  exact D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix.tabulatedPowers T 13 W
    (by decide +kernel) (by decide +kernel) i

/-- The eventual fourth-order vector relation. -/
theorem finite_certificate :
    (T ^ 5).mulVec terminal = ∑ j : Fin 4,
      (![324, -270, 0, 15] j : ℤ) • (T ^ (1 + j.val)).mulVec terminal := by
  rw [show 5 = (5 : Fin 14).val from rfl, powers]
  simp_rw [show ∀ j : Fin 4, (T ^ (1 + j.val)).mulVec terminal =
    W ⟨1 + j.val, by omega⟩ from fun j => powers ⟨1 + j.val, by omega⟩]
  decide +kernel

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
