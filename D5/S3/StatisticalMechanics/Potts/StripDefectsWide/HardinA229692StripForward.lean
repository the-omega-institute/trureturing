/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripForward
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripForward
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.finite_certificate
   digest: Exact two-defect width-six HA transfer. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229692Strip.result)
step0: proof_shape=bind-only; consumers=forward_certificate
step1: proof_shape=bind-only; consumers=forward_certificate
step2: proof_shape=bind-only; consumers=forward_certificate
step3: proof_shape=bind-only; consumers=forward_certificate
step4: proof_shape=bind-only; consumers=forward_certificate
step5: proof_shape=bind-only; consumers=forward_certificate
step6: proof_shape=bind-only; consumers=forward_certificate
step7: proof_shape=bind-only; consumers=forward_certificate
step8: proof_shape=bind-only; consumers=forward_certificate
step9: proof_shape=bind-only; consumers=forward_certificate
step10: proof_shape=bind-only; consumers=forward_certificate
forward_certificate: proof_shape=bind-only; consumers=HardinA229692Strip.finite_certificate
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripInherited
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripForward
open HardinA229692StripData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem step0 : W 1 = Matrix.vecMul (W 0) T := by
  exact HardinA229692StripInherited.step 0 (by decide +kernel)


private theorem step1 : W 2 = Matrix.vecMul (W 1) T := by
  exact HardinA229692StripInherited.step 1 (by decide +kernel)


private theorem step2 : W 3 = Matrix.vecMul (W 2) T := by
  exact HardinA229692StripInherited.step 2 (by decide +kernel)


private theorem step3 : W 4 = Matrix.vecMul (W 3) T := by
  exact HardinA229692StripInherited.step 3 (by decide +kernel)


private theorem step4 : W 5 = Matrix.vecMul (W 4) T := by
  exact HardinA229692StripInherited.step 4 (by decide +kernel)


private theorem step5 : W 6 = Matrix.vecMul (W 5) T := by
  exact HardinA229692StripInherited.step 5 (by decide +kernel)


private theorem step6 : W 7 = Matrix.vecMul (W 6) T := by
  exact HardinA229692StripInherited.step 6 (by decide +kernel)


private theorem step7 : W 8 = Matrix.vecMul (W 7) T := by
  exact HardinA229692StripInherited.step 7 (by decide +kernel)


private theorem step8 : W 9 = Matrix.vecMul (W 8) T := by
  exact HardinA229692StripInherited.step 8 (by decide +kernel)


private theorem step9 : W 10 = Matrix.vecMul (W 9) T := by
  exact HardinA229692StripInherited.step 9 (by decide +kernel)


private theorem step10 : W 11 = Matrix.vecMul (W 10) T := by
  exact HardinA229692StripInherited.step 10 (by decide +kernel)



theorem forward_certificate :
    (W 0 = initial ∧ ∀ i : Fin 11, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 11 = ∑ j : Fin 9, (![531441, -1771470, 2460375, -1842183, 803115, -205200, 29368, -2145, 75] j : ℤ) • W ⟨2 + j.val, by omega⟩ := by
  refine ⟨⟨?_, ?_⟩, HardinA229692StripInherited.polynomial (by decide +kernel)⟩
  · change Fin.append
      (D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.W 0)
      (fun j : Fin 36 => initial (j.natAdd 32)) = initial
    simpa only [initial, Fin.append_right] using congrArg (fun w : Fin 32 → ℤ => Fin.append w
        (fun j : Fin 36 => initial (j.natAdd 32)))
      D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripCertificate.structural_certificate.2.2.2.2.1.1
  ·
    intro i
    fin_cases i
    · exact step0
    · exact step1
    · exact step2
    · exact step3
    · exact step4
    · exact step5
    · exact step6
    · exact step7
    · exact step8
    · exact step9
    · exact step10

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripForward
