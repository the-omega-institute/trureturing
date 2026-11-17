import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant
set_option autoImplicit false
set_option maxRecDepth 8192
/-! Exact source bridges for dependent readout audits. -/
noncomputable section
open Classical MvPolynomial Finset Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.SplitQuarticIrreducibility
open _root_.D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant
universe u v w
private abbrev single (P : Type u) (X : P → Type v) (Y : P → Type w) : Signature where
  Params := P
  State := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := Y
  Anchor := Empty
  finiteAnchor := inferInstance

namespace Count
abbrev signature : Signature := single Unit (fun _ => Finset (Finset (Fin 8))) (fun _ => ℕ)
def actual : Realization signature := realize signature (fun _ _ => Finset.card)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () (fourSets.filter (fun I => integerCoefficient I = 0)) = 18
theorem source_bridge : (type_of% (@coefficient_zero_count)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  norm_num [arena, rejected, realize]
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), ∅, {∅}, ?_⟩
  change (∅ : Finset (Finset (Fin 8))).card ≠ ({∅} : Finset (Finset (Fin 8))).card
  simp
private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e
def familyRegistration : Registration arena (type_of% (@coefficient_zero_count)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨coefficient_zero_count, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

/-- Source reconstruction remains unspecified. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coefficient_zero_count)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant.coefficient_zero_count.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant.Count.familyRegistration
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
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Count

end Reg.D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant
