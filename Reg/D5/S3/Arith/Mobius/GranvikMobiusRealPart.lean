import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Mobius.GranvikMobiusRealPart
import Reg.Support.SingleDependentReadout

/-! The complete positive-index identity with its real-part observation exposed. -/

namespace Reg.D5.S3.Arith.Mobius.GranvikMobiusRealPart

open _root_.D5.S3.Arith.Mobius.GranvikMobiusRealPart
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ z => z.re + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_ : 0 < n),
    (a n : ℝ) = R.readout () n ((ArithmeticFunction.moebius n : ℂ) * Complex.I ^ n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by decide)
  norm_num [rejected, realize, a] at hbad

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(1 : ℕ), (0 : ℂ), (1 : ℂ), ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `GranvikMobiusRealPart.result.audit
  realizationName := `Reg.D5.S3.Arith.Mobius.GranvikMobiusRealPart.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Mobius.GranvikMobiusRealPart
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Mobius.GranvikMobiusRealPart
