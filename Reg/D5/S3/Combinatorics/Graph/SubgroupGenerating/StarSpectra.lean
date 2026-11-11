import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra
import Reg.Support.DependentFamily

/-! Source-bound whole-family observations with explicit open residuals. -/

set_option autoImplicit false
open Matrix
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra

namespace star_matrixAudit
abbrev signature : Signature where
  Params := Σ α : Type, Fintype α × DecidableEq α
  State _ := MatrixKind
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Unit ⊕ p.1) (Unit ⊕ p.1) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p kind => by
    letI := p.2.1
    letI := p.2.2
    exact sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ p.1)) kind) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type} [Fintype α] [DecidableEq α] (kind : MatrixKind),
    R.readout () ⟨α,inferInstance,inferInstance⟩ kind =
      match kind with
      | .adjacency => arrowMatrix 0 0 1
      | .laplacian => arrowMatrix (Fintype.card α) 1 (-1)
      | .signless => arrowMatrix (Fintype.card α) 1 1
      | .commonNeighbour => Matrix.fromBlocks (0 : Matrix Unit Unit ℝ) 0 0
          (Matrix.vecMulVec (fun _ : α => (1 : ℝ)) (fun _ => 1) - Matrix.scalar α 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h Unit inferInstance inferInstance .adjacency
  have he := congrArg (fun M => M (Sum.inl ()) (Sum.inr ())) hh
  change (0 : ℝ) = 1 at he
  norm_num at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Unit,inferInstance,inferInstance⟩,.adjacency,.laplacian,?_⟩
  intro he
  have hh := congrArg (fun M => M (Sum.inl ()) (Sum.inl ())) he
  change sourceMatrix _ .adjacency _ _ = sourceMatrix _ .laplacian _ _ at hh
  rw [star_matrix,star_matrix] at hh
  norm_num [arrowMatrix] at hh
def family : Registration arena (type_of% (@star_matrix)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@star_matrix,rejected,rejected_law⟩
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
    (@star_matrix) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra.star_matrix.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra.star_matrixAudit.family
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
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end star_matrixAudit

namespace star_spectrumAudit
abbrev signature : Signature where
  Params := Σ α : Type, Fintype α × DecidableEq α
  State _ := MatrixKind
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Multiset ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p kind => by
    letI := p.2.1
    letI := p.2.2
    exact graphSpectrum (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ p.1)) kind) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type} [Fintype α] [DecidableEq α] (kind : MatrixKind),
    R.readout () ⟨α,inferInstance,inferInstance⟩ kind =
      starValues (Fintype.card α) kind
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h Empty inferInstance inferInstance .adjacency
  have he := congrArg Multiset.card hh
  norm_num [rejected,realize,starValues] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Unit,inferInstance,inferInstance⟩,.adjacency,.laplacian,?_⟩
  intro he
  change graphSpectrum (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ Unit)) .adjacency =
    graphSpectrum (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ Unit)) .laplacian at he
  rw [star_spectrum,star_spectrum] at he
  have hm : (-1 : ℝ) ∈ starValues (Fintype.card Unit) .adjacency := by norm_num [starValues]
  rw [he] at hm
  norm_num [starValues] at hm
def family : Registration arena (type_of% (@star_spectrum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@star_spectrum,rejected,rejected_law⟩
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
    (@star_spectrum) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra.star_spectrum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra.star_spectrumAudit.family
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
    owner := `D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end star_spectrumAudit

end Reg.D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra
