/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripCertificate
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripCertificate.structural_certificate
   digest: Initial, terminal, budget and forward-table certificate for width five. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229583Strip.result)
structural_certificate: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripCertificate
open HardinA229583StripData
open DefectTransfer (bondDefects)

theorem structural_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid (boundary r) (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 14, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 5, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 5 = ∑ j : Fin 4, (![-324, 540, -261, 30] j : ℤ) • W ⟨1 + j.val, by omega⟩ := by
  decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripCertificate
