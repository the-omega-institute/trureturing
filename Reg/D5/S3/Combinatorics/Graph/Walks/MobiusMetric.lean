import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.MobiusMetric
import Reg.Support.DependentFamily

set_option autoImplicit false
namespace Reg.D5.S3.Combinatorics.Graph.Walks.MobiusMetric
open _root_.CubicCirculant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Diameter
abbrev signature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ m => (mobius m).diam) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ m : ℕ, R.readout () () m = (m+3)/2

private lemma source_law : arena.Law actual := by
  intro m
  exact mobius_diameter m
private lemma rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  change (0 : ℕ) = 1 at hh
  omega

def registration : Registration arena (type_of% (@_root_.CubicCirculant.mobius_diameter)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_law,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(),0,1,?_⟩
    change (mobius 0).diam ≠ (mobius 1).diam
    rw [mobius_diameter,mobius_diameter]
    omega

def contract : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.CubicCirculant.mobius_diameter)
    (type_of% (realize signature (fun _ _ m => (mobius m).diam) (fun e => nomatch e)))
    Type Unit := {
  unitName := Lean.Name.str (Lean.Name.str `CubicCirculant.mobius_diameter
    "Reg.D5.S3.Combinatorics.Graph.Walks.MobiusMetric/Reg.D5.S3.Combinatorics.Graph.Walks.MobiusMetric.Diameter.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.MobiusMetric.Diameter.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => (mobius m).diam) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.MobiusMetric
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit,value := .bool false }] }
#print axioms registration
#print axioms contract
end Diameter
end
end Reg.D5.S3.Combinatorics.Graph.Walks.MobiusMetric
