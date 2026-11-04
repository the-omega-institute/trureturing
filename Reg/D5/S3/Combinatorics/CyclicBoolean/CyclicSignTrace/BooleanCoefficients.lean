import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace.BooleanCoefficients

set_option autoImplicit false
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace.BooleanCoefficients
open _root_.D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev MaskParameter := Σ m : ℕ, Word (2 * m + 1)
abbrev coefficientSignature : Signature := Reg.Support.SingleDependentReadout.signature
  MaskParameter (fun p => Finset (ZMod (2 * p.1 + 1))) (fun _ => ZMod 2)
def coefficientActual : Realization coefficientSignature := realize coefficientSignature
  (fun _ p s => booleanCoeff (fun z => inverseComponent p.1 p.2 (1 + z)) s)
  (fun e => nomatch e)
def coefficientRejected : Realization coefficientSignature := realize coefficientSignature
  (fun _ _ _ => 1) (fun e => nomatch e)

private theorem coefficientDependence :
    ObservationalDependence coefficientSignature coefficientActual := by
  intro role
  let b : Word 3 := Pi.single 0 1
  refine ⟨⟨1, b⟩, topVariables 1 0, topVariables 1 1, ?_⟩
  change booleanCoeff (fun z => inverseComponent 1 b (1 + z)) (topVariables 1 0) ≠
    booleanCoeff (fun z => inverseComponent 1 b (1 + z)) (topVariables 1 1)
  rw [inverse_component_top_coefficient, inverse_component_top_coefficient]
  norm_num [b, Pi.single_apply]

namespace Coefficients
def arena : Arena where
  signature := coefficientSignature
  Law R := ∀ (m : ℕ) (b : Word (2 * m + 1)) (s : Finset (ZMod (2 * m + 1))),
    R.readout () ⟨m, b⟩ s =
      ∑ i, ∑ r ∈ Finset.range (m + 1), b i *
        ((if s = prefixVariables i r then 1 else 0) +
          (if s = insert (i + (2 * r : ℕ)) (prefixVariables i r) then 1 else 0))
private theorem rejected_law : ¬ arena.Law coefficientRejected := by
  intro h
  have he := h 0 0 ∅
  norm_num [coefficientRejected, realize] at he
def familyRegistration : Registration arena
    (type_of% (@inverse_component_boolean_coefficient)) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨inverse_component_boolean_coefficient, coefficientRejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := coefficientDependence
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@inverse_component_boolean_coefficient)
    (type_of% (realize coefficientSignature coefficientActual.readout coefficientActual.anchor))
    (Type → Type) Unit where
  unitName := `D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace.inverse_component_boolean_coefficient.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace.BooleanCoefficients.Coefficients.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature coefficientActual.readout coefficientActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@Finset)
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace.BooleanCoefficients
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end Coefficients


end
end Reg.D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace.BooleanCoefficients
