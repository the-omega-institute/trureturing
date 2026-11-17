import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
import Reg.Support.SingleDependentReadout

/-! Exact source-family registration of the actual cubic support reconstruction. -/

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open _root_.D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Finset (Q 9)) (fun _ => Finset (Q 9))

def actual : Realization signature :=
  realize signature (fun _ _ C => C) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

/-- The original actual support and all three original hypotheses remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {C : Finset (Q 9)},
    ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 →
    IsBalanced C → C.card = 54 →
    ∃ (g : Q 9 ≃ Q 9) (pi : Fin 9 ≃ Fin 9),
      (∀ x i, g (BalancedCriticalSpectrum.flip x i) =
        BalancedCriticalSpectrum.flip (g x) (pi i)) ∧
      R.readout () () C = (GrayGridComponent.support 3).image g

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : (GrayGridComponent.support 3).card = 54 := by
    simpa using GrayGridComponent.card_support (d := 3) (by decide)
  obtain ⟨g,pi,hg,he⟩ := h (C := GrayGridComponent.support 3)
    (GrayGridComponent.component_regular 3)
    ⟨GrayGridComponent.switching 3,GrayGridComponent.support_isSwitching 3⟩ hc
  have hh := congrArg Finset.card he
  change (∅ : Finset (Q 9)).card = ((GrayGridComponent.support 3).image g).card at hh
  rw [Finset.card_empty,Finset.card_image_of_injective _ g.injective,hc] at hh
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),∅,{fun _ => false},?_⟩
  intro h
  have hh := congrArg Finset.card h
  simp [actual,realize] at hh

def family : Registration arena (type_of% (@gray_reconstruction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gray_reconstruction,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gray_reconstruction) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction.gray_reconstruction.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ C => C) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
