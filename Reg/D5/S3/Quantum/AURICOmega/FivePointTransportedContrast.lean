import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.AURICOmega.FivePointTransportedContrast

/-! The squared difference in the five-point criterion for transported readings. -/

namespace Reg.D5.S3.Quantum.AURICOmega.FivePointTransportedContrast

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.FivePointTransportedContrast (exists_transported_readings_iff)
open LeanInformationAudit

set_option autoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ d => d ^ 2) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ d => d ^ 2 + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t d : ℚ) (_ : 0 ≤ t) (_ : t ≤ 1),
    (∃ a b c e r : ℚ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ e ∧ 0 ≤ r ∧ a - b = d ∧
      ∀ x y z w v : ℚ, 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 + v ^ 2 +
        2 * (t * (x * y + z * w + z * v) + a * (x * z + y * v) +
          b * (y * z + x * w) + c * y * w + e * x * v + r * w * v)) ↔
    R.readout () () d ≤ if t ≤ 1 / 2 then (1 - t ^ 2) ^ 2
      else if (t - 1 / 2) ^ 2 ≤ 1 - t ^ 2 then (5 / 4 - t) ^ 2
      else (2 * t - 1) ^ 2 * (1 - t ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have attainable := (exists_transported_readings_iff 1 0 (by norm_num) le_rfl).mpr (by norm_num)
  have bound := (h 1 0 (by norm_num) le_rfl).mp attainable
  change (0 : ℚ) ^ 2 + 1 ≤
    (if (1 : ℚ) ≤ 1 / 2 then (1 - 1 ^ 2) ^ 2
     else if ((1 : ℚ) - 1 / 2) ^ 2 ≤ 1 - 1 ^ 2 then (5 / 4 - 1) ^ 2
     else (2 * 1 - 1) ^ 2 * (1 - 1 ^ 2)) at bound
  norm_num at bound

def family : Registration arena (type_of% @exists_transported_readings_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_transported_readings_iff, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 0, 1, by change (0 : ℚ) ^ 2 ≠ 1 ^ 2; norm_num⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_transported_readings_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.FivePointTransportedContrast.unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.FivePointTransportedContrast.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => d ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.FivePointTransportedContrast
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.FivePointTransportedContrast
