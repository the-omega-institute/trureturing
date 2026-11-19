import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra
import Reg.Support.DependentFamily

/-! Source-bound whole-family observations with explicit open residuals. -/

set_option autoImplicit false
open Finset
open scoped Classical
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra
attribute [local instance] _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.subgroupFintype

namespace edge_countAudit
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => n^2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type} [Group G] [Fintype G],
    (sgbGraph G).edgeFinset.card = R.readout () () (Fintype.card G)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h PUnit inferInstance inferInstance
  rw [edge_count] at hh
  norm_num [rejected,realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(),0,1,by norm_num [actual,realize]⟩
def family : Registration arena (type_of% (@edge_count)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@edge_count,rejected,rejected_law⟩
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
    (@edge_count) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra.edge_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra.edge_countAudit.family
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
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra
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
end edge_countAudit

namespace sgb_spectrumAudit
abbrev signature : Signature where
  Params := MatrixKind
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Multiset ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => starValues n p) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type} [Group G] [Fintype G] (kind : MatrixKind),
    graphSpectrum (sgbGraph G) kind = ∑ H : Subgroup G, R.readout () kind (pairCount H)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h PUnit inferInstance inferInstance .adjacency
  have hm : (1 : ℝ) ∈ graphSpectrum (sgbGraph PUnit) .adjacency := by
    rw [sgb_spectrum]
    apply Multiset.mem_sum.mpr
    exact ⟨⊥,Finset.mem_univ _,by simp [pairCount_bot,starValues]⟩
  rw [hh] at hm
  simpa [rejected,realize] using hm
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨.adjacency,0,1,?_⟩
  intro he
  have hm : (1 : ℝ) ∈ starValues 1 .adjacency := by norm_num [starValues]
  change starValues 0 .adjacency = starValues 1 .adjacency at he
  rw [← he] at hm
  norm_num [starValues] at hm
def family : Registration arena (type_of% (@sgb_spectrum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sgb_spectrum,rejected,rejected_law⟩
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
    (@sgb_spectrum) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra.sgb_spectrum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra.sgb_spectrumAudit.family
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
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body","body","body","body","arg","arg","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sgb_spectrumAudit

end Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra
