/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripCertificate
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#30838; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229691Strip.result)
structural_certificate: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData

/-! Exact budget, acceptance, initial and forward-vector identities. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripCertificate
open HardinA229691StripData
open HardinA229583StripData (Row Boundary horizontal antidiagonal boundary cross)
open DefectTransfer (bondDefects)

theorem structural_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 →
      Valid (boundary r) (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 27, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl (boundary r) (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 7, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 7 = ∑ j : Fin 6, (![-5832, 14580, -13122, 4995, -729, 45] j : ℤ) • W ⟨1 + j.val, by omega⟩ := by
  decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripCertificate
