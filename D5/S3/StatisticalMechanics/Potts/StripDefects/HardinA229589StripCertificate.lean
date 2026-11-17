/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripCertificate
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#30838; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229589Strip.result)
structural_certificate: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

/-! Exact budget, acceptance, initial and forward-vector identities. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripCertificate
open HardinA229589StripData
open DefectTransfer (bondDefects)

theorem structural_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid r (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 28, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl r (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 12, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 12 = ∑ j : Fin 6, (![-36, 180, -333, 282, -111, 18] j : ℤ) • W ⟨6 + j.val, by omega⟩ := by
  decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripCertificate
