/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripCertificate
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripCertificate.structural_certificate
   digest: Structural and polynomial certificate for width-6 strips. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229584Strip.result)
tail_bound: proof_shape=bind-only; consumers=structural_certificate
structural_certificate: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripCertificate
open HardinA229584StripData
open DefectTransfer (bondDefects)

private theorem tail_bound (r : Row) :
    (Finset.univ.filter fun z : Fin 4 =>
      boundary r z.castSucc = boundary r z.succ).card ≤ bondDefects horizontal r r := by
  revert r
  decide +kernel

theorem structural_certificate :
    (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid (boundary r) (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 32, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 7, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 7 = ∑ j : Fin 6, (![-6561, 14580, -12150, 4662, -805, 50] j : ℤ) • W ⟨1 + j.val, by omega⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · intro p d hp r hr
    have hd := hp.1
    have ht := tail_bound r
    constructor
    · omega
    · change _ ≤ 1 - (d.val - (cross p r + bondDefects horizontal r r))
      omega
  · intro r hr
    have ht := tail_bound r
    constructor
    · omega
    · change _ ≤ 1 - (1 - bondDefects horizontal r r)
      omega
  · decide +kernel
  · decide +kernel
  · decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripCertificate
