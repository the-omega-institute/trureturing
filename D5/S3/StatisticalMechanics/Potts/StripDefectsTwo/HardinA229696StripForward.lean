/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripForward
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripForward
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696Strip.finite_certificate
   digest: Block extension for exact two-defect HA strip counts. -/

/-
admission_basis: open-problem-resolution (#31299; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229696Strip.result)
forward_certificate: proof_shape=bind-only; consumers=HardinA229696Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripForward
open HardinA229696StripData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem forward_certificate :
    (W 0 = initial ∧ ∀ i : Fin 10, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 10 = ∑ j : Fin 6, (![-8, 60, -162, 185, -81, 15] j : ℤ) • W ⟨4 + j.val, by omega⟩ := by
  have zero_cut : ∀ j : Fin 10,
      W 0 (j.castAdd 5) = HardinA229588Strip.W 0 j ∧ initial (j.castAdd 5) = HardinA229588Strip.initial j := by
    decide +kernel
  have zero_remaining : ∀ s : Fin 15, 10 ≤ s.val → W 0 s = initial s := by
    decide +kernel
  have step_cut : ∀ (i : Fin 6) (j : Fin 10),
      W (i.succ.castAdd 4) (j.castAdd 5) = HardinA229588Strip.W i.succ j ∧
      Matrix.vecMul (W (i.castSucc.castAdd 4)) T (j.castAdd 5) =
        Matrix.vecMul (HardinA229588Strip.W i.castSucc) HardinA229588Strip.T j := by decide +kernel
  have step_remaining : ∀ (i : Fin 10) (s : Fin 15),
      ¬ (i.val < 6 ∧ s.val < 10) →
      W i.succ s = Matrix.vecMul (W i.castSucc) T s := by decide +kernel
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · funext s
    by_cases hs : s.val < 10
    · let j : Fin 10 := ⟨s.val, hs⟩
      have he : s = j.castAdd 5 := rfl
      rw [he, (zero_cut j).1, (zero_cut j).2]
      exact congrFun HardinA229588Strip.finite_certificate.2.2.2.2.2.1.1 j
    · exact zero_remaining s (by omega)
  · intro i
    funext s
    by_cases hs : i.val < 6 ∧ s.val < 10
    · let k : Fin 6 := ⟨i.val, hs.1⟩
      let j : Fin 10 := ⟨s.val, hs.2⟩
      have he : s = j.castAdd 5 := rfl
      have h0 : i.castSucc = k.castSucc.castAdd 4 := rfl
      have h1 : i.succ = k.succ.castAdd 4 := rfl
      rw [he, h0, h1, (step_cut k j).1, (step_cut k j).2]
      exact congrFun (HardinA229588Strip.finite_certificate.2.2.2.2.2.1.2 k) j
    · exact step_remaining i s hs

end D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripForward
