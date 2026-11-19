import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Constants.Moments.A331474HankelBridge
import Reg.Support.SingleDependentReadout

/-! Source-bound four-slot evidence for the exact coefficient law. -/

namespace Reg.D5.S3.Constants.Moments.A331474HankelBridge
open _root_.D5.S3.Constants.Moments.A331474HankelBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => coeff n F0) (fun e => nomatch e)

def changed : Realization signature :=
  realize signature (fun _ _ n => coeff n F0 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (∀ n, R.readout () () n = b n) ∧
    (∀ n, b (n + 1) = s (n + 1) + s n)

private theorem changed_law : ¬ arena.Law changed := by
  intro h
  have hh := h.1 0
  have ha := source_moments.1 0
  change coeff 0 F0 + 1 = b 0 at hh
  omega

def family : Registration arena (type_of% source_moments) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_moments, changed, changed_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual changed changed_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change coeff 0 F0 ≠ coeff 1 F0
    rw [source_moments.1, source_moments.1]
    norm_num [b]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    source_moments (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Constants.Moments.A331474HankelBridge.auditUnit
  realizationName := `Reg.D5.S3.Constants.Moments.A331474HankelBridge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => coeff n F0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Constants.Moments.A331474HankelBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Constants.Moments.A331474HankelBridge
