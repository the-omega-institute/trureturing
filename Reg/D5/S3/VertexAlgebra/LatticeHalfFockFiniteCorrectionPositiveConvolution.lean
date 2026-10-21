import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Faithful dependent-family observations on the complete original source telescope. -/

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.PositiveConvolution

open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ m n => ∑ s ∈ Finset.range (n + 1),
    halfBinomial (m + s) * Ring.choose (1 / 2 : ℂ) (n - s))
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (m n : ℕ), 0 < m →
    readout.readout () m n =
      (m : ℂ) * halfBinomial m * halfBinomial n / ((m : ℂ) + (n : ℂ))

theorem source_bridge :
    (type_of% (@halfBinomial_positive_convolution)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law 1 0 (by decide)
  norm_num [rejected, realize, halfBinomial, Finset.prod_range_succ] at bad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize, halfBinomial, Finset.sum_range_succ,
    Finset.prod_range_succ, Ring.choose_one_right]

def familyRegistration : Registration arena (type_of% (@halfBinomial_positive_convolution)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp halfBinomial_positive_convolution, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@halfBinomial_positive_convolution)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.halfBinomial_positive_convolution "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.PositiveConvolution.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.PositiveConvolution
