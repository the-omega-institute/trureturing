import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations of public statements in the mirrored owner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v
open _root_.D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

open _root_.D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
namespace Reg.D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
/-- Read each squared amplitude in the normalization sum. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => Complex.normSq z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] (φ : ι → ℂ),
    unitVector φ ↔ ∑ x, R.readout () () (φ x) = 1
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h (ι := ULift.{u} Unit) (fun _ => 1)).mp (by
    simp [unitVector, dotProduct])
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @unit_norm_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@unit_norm_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@unit_norm_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.unit
  realizationName := `Reg.D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => Complex.normSq z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print unit_norm_iff
#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
