import D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The full finite-graph family with its actual signed Catalan functional. -/
namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan
open _root_.D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
open _root_.D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ α : Type u, Σ _ : DecidableEq α, Σ G : SimpleGraph α,
    Σ _ : DecidableRel G.Adj, Finset α
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p m => @phi p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 m)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ {α : Type u} [Fintype α] [d : DecidableEq α]
    (G : SimpleGraph α) [da : DecidableRel G.Adj]
    (_ha : G.IsAcyclic) (_hd : ∀ a, G.degree a ≤ 2) (m : ℕ)
    (_hm : Fintype.card α ≤ m), 0 ≤ O.readout () ⟨α, d, G, da, Finset.univ⟩ m

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} (Fin 0)) inferInstance inferInstance ⊥ inferInstance
    SimpleGraph.isAcyclic_bot (by intro a; exact isEmptyElim a) 0 (by simp)
  change (0 : ℤ) ≤ -1 at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 0), inferInstance, ⊥, inferInstance, ∅⟩, 0, 2, ?_⟩
  simp [actual, realize, phi,
    _root_.D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion.configurations,
    Finset.filter_singleton, SimpleGraph.IsIndepSet, Set.Pairwise, catalan_zero, catalan_two]

def family : Registration arena.{u} (type_of% @finite_forest_phi_nonnegative.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_forest_phi_nonnegative.{u}, rejected, rejected_law⟩
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
      (@finite_forest_phi_nonnegative.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end
end Reg.D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan
