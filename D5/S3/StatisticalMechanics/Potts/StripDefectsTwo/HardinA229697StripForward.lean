/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripForward
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripForward
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697Strip.finite_certificate
   digest: Block extension for exact two-defect HA strip counts. -/

/-
admission_basis: open-problem-resolution (#31299; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229697Strip.result)
forward_certificate: proof_shape=bind-only; consumers=HardinA229697Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589Strip

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripForward
open HardinA229697StripData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem forward_certificate :
    (W 0 = initial ∧ ∀ i : Fin 17, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 17 = ∑ j : Fin 9, (![216, -1620, 5022, -8343, 8073, -4644, 1557, -288, 27] j : ℤ) • W ⟨8 + j.val, by omega⟩ := by
  have zero_cut : ∀ j : Fin 28,
      W 0 (j.castAdd 14) = HardinA229589StripData.W 0 j ∧ initial (j.castAdd 14) = HardinA229589StripData.initial j := by
    decide +kernel
  have zero_remaining : ∀ s : Fin 42, 28 ≤ s.val → W 0 s = initial s := by
    decide +kernel
  have step_cut : ∀ (i : Fin 12) (j : Fin 28),
      W (i.succ.castAdd 5) (j.castAdd 14) = HardinA229589StripData.W i.succ j ∧
      Matrix.vecMul (W (i.castSucc.castAdd 5)) T (j.castAdd 14) =
        Matrix.vecMul (HardinA229589StripData.W i.castSucc) HardinA229589StripData.T j := by decide +kernel
  have step_remaining : ∀ (i : Fin 17) (s : Fin 42),
      ¬ (i.val < 12 ∧ s.val < 28) →
      W i.succ s = Matrix.vecMul (W i.castSucc) T s := by decide +kernel
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · funext s
    by_cases hs : s.val < 28
    · let j : Fin 28 := ⟨s.val, hs⟩
      have he : s = j.castAdd 14 := rfl
      rw [he, (zero_cut j).1, (zero_cut j).2]
      exact congrFun HardinA229589Strip.finite_certificate.2.2.2.2.2.1.1 j
    · exact zero_remaining s (by omega)
  · intro i
    funext s
    by_cases hs : i.val < 12 ∧ s.val < 28
    · let k : Fin 12 := ⟨i.val, hs.1⟩
      let j : Fin 28 := ⟨s.val, hs.2⟩
      have he : s = j.castAdd 14 := rfl
      have h0 : i.castSucc = k.castSucc.castAdd 5 := rfl
      have h1 : i.succ = k.succ.castAdd 5 := rfl
      rw [he, h0, h1, (step_cut k j).1, (step_cut k j).2]
      exact congrFun (HardinA229589Strip.finite_certificate.2.2.2.2.2.1.2 k) j
    · exact step_remaining i s hs

end D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripForward
