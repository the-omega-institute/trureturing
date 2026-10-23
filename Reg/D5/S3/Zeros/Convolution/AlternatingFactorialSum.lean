import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Convolution.AlternatingFactorialSum
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Zeros.Convolution.AlternatingFactorialSum
open _root_.D5.S3.Zeros.Convolution.AlternatingFactorialSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the real descending factorial at its length coordinate. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n i => (n.descFactorial i : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain both natural parameters and the bound on the descending-factorial length. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n i : ℕ) (_hi : i ≤ n),
    R.readout () n i = (n.factorial : ℝ) / ((n - i).factorial : ℝ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 0 0 (Nat.le_refl 0)
  change (0 : ℝ) = (Nat.factorial 0 : ℝ) / ((0 - 0).factorial : ℝ) at hzero
  norm_num at hzero

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 0, 1, ?_⟩
  change (Nat.descFactorial 2 0 : ℝ) ≠ (Nat.descFactorial 2 1 : ℝ)
  norm_num

def source_registration : Registration arena (type_of% @real_descFactorial) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨real_descFactorial, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@real_descFactorial) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.Convolution.AlternatingFactorialSum.unit
  realizationName := `Reg.D5.S3.Zeros.Convolution.AlternatingFactorialSum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n i => (n.descFactorial i : ℝ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Convolution.AlternatingFactorialSum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Zeros.Convolution.AlternatingFactorialSum
