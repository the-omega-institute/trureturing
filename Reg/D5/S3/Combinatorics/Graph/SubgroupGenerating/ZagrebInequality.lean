import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.SubgroupGenerating.ZagrebInequality
import Reg.Support.DependentFamily

/-! A whole-family observation of the actual second Zagreb ratio. -/

set_option autoImplicit false
open Finset
open scoped Classical
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.ZagrebInequality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.ZagrebInequality
attribute [local instance]
  _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.subgroupFintype

abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m s => s / (m : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type} [Group G] [Fintype G],
    firstZagreb (sgbGraph G) / (Fintype.card (Vertex G) : ℝ) ≤
      R.readout () ((sgbGraph G).edgeFinset.card) (secondZagreb (sgbGraph G))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h PUnit inferInstance inferInstance
  have hn : (0 : ℝ) ≤
      firstZagreb (sgbGraph PUnit) / (Fintype.card (Vertex PUnit) : ℝ) := by
    apply div_nonneg
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · positivity
  have hb : firstZagreb (sgbGraph PUnit) / (Fintype.card (Vertex PUnit) : ℝ) ≤ -1 := by
    simpa [rejected, realize] using hh
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨1,0,1,by norm_num [actual,realize]⟩

def family : Registration arena (type_of% (@hansen_vukicevic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hansen_vukicevic,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hansen_vukicevic) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.ZagrebInequality.hansen_vukicevic.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.ZagrebInequality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.ZagrebInequality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.ZagrebInequality
