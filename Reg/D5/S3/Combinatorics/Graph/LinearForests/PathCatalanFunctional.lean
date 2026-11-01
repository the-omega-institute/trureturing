import D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
open _root_.D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

local instance : DecidableRel (SimpleGraph.hasse ℕ).Adj := Classical.decRel _

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ v m => phi (SimpleGraph.hasse ℕ) (Finset.range v) m)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ v m : ℕ, v ≤ m → 0 ≤ O.readout () v m

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 (by omega)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 2, ?_⟩
  simp [actual, realize, phi,
    _root_.D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion.configurations,
    SimpleGraph.IsIndepSet, Set.Pairwise, catalan_zero, catalan_two]

def family : Registration arena (type_of% @path_phi_nonnegative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨path_phi_nonnegative, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@path_phi_nonnegative) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional.family
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
    owner := `D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end
end Reg.D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
