import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.AURICOmega.ThreeReadingContrast

/-! Audit the squared contrast in the rational disk of attainable probe differences. -/

namespace Reg.D5.S3.Quantum.AURICOmega.ThreeReadingContrast

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.ThreeReadingContrast (exists_nonnegative_readings_iff)
open LeanInformationAudit

set_option autoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ c => c ^ 2) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ c => c ^ 2 + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ r d : ℚ,
    (∃ a b : ℚ, 0 ≤ a ∧ 0 ≤ b ∧ a - b = d ∧
      ∀ x y z : ℚ, 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 2 * (r * x * y + a * x * z + b * y * z)) ↔
    r ^ 2 + R.readout () () d ≤ 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have attainable := (exists_nonnegative_readings_iff 1 0).mpr (by norm_num)
  have bound := (h 1 0).mp attainable
  change (1 : ℚ) ^ 2 + (0 ^ 2 + 1) ≤ 1 at bound
  norm_num at bound

def family : Registration arena (type_of% @exists_nonnegative_readings_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_nonnegative_readings_iff, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 0, 1, by change (0 : ℚ) ^ 2 ≠ 1 ^ 2; norm_num⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_nonnegative_readings_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.ThreeReadingContrast.unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.ThreeReadingContrast.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.ThreeReadingContrast
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.ThreeReadingContrast
