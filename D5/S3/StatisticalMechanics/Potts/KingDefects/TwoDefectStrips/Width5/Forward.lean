/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Forward
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Forward
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229752.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Certificate.transition_counts,D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Forward.structural_certificate
   digest: Width-five exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers on the live path of HardinA229752.result)
structural_certificate: proof_shape=content; consumers=HardinA229752.result
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
/-! Acceptance, initial weights and the forward polynomial relation. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Forward
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem structural_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ s : Fin 43, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 11, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 11 = ∑ j : Fin 6, (![-8, 36, -66, 63, -33, 9] j : ℤ) • W ⟨5+j.val, by omega⟩ := by
  refine ⟨?_, ?_, ⟨rfl, ?_⟩, ?_⟩
  · have h : ∀ a b c e f : Fin 4, ∀ d : Fin 3,
        Valid (![a, b, c, e, f] : Row) d.val →
        terminal (cl (![a, b, c, e, f] : Row) d.val) =
          (if d.val = 0 then 1 else 0) := by
      intro a
      fin_cases a <;> decide +kernel
    intro p
    have he : p = ![p 0, p 1, p 2, p 3, p 4] := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact h (p 0) (p 1) (p 2) (p 3) (p 4)
  · intro s
    fin_cases s <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · funext s
    fin_cases s <;> decide +kernel
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Forward
