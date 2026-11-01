import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Domination.MinusFourReplication

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReplication

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph
open _root_.D5.S3.Combinatorics.Graph.DominatingSetAverage
open _root_.D5.S3.Combinatorics.Graph.LocalDominatingStemBoundReplication
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourReplication
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe u
noncomputable section
attribute [local instance] Classical.propDecidable

structure Params where
  V : Type u
  finite : Fintype V
  equality : DecidableEq V
  graph : SimpleGraph V
  attachment : Finset V
  copies : ℕ

def signature : DependentFamily.Signature where
  Params := Params.{u}
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def readout (p : Params.{u}) (x : ℤ) : ℤ := by
  letI := p.finite
  letI := p.equality
  exact evaluation (replicated p.graph p.attachment p.copies) x

def rhs (p : Params.{u}) (x : ℤ) : ℤ := by
  letI := p.finite
  letI := p.equality
  exact x * (1 + x) * (∑ S ∈ partialSets p.graph p.attachment, x ^ S.card) ^ p.copies +
    x * (evaluation p.graph x) ^ p.copies

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ p x => readout p x) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ p x, R.readout () p x = rhs p x

abbrev sourceScope := type_of% (@replicated_evaluation.{u})

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h p x
    exact @h p.V p.finite p.equality p.graph p.attachment p.copies x
  · intro h V finite equality graph attachment copies x
    exact h ⟨V, finite, equality, graph, attachment, copies⟩ x

theorem actual_positive : arena.Law actual := source_bridge.mp replicated_evaluation

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (1 : ℤ)) (fun e => nomatch e)

def emptyParams : Params.{u} :=
  ⟨ULift.{u} (Fin 0), inferInstance, inferInstance, ⊥, ∅, 0⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h emptyParams 0
  change (1 : ℤ) = rhs emptyParams 0 at hz
  norm_num [rhs, emptyParams] at hz

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨emptyParams, 0, 1, ?_⟩
    change readout emptyParams 0 ≠ readout emptyParams 1
    have h0 := actual_positive emptyParams 0
    have h1 := actual_positive emptyParams 1
    change readout emptyParams 0 = rhs emptyParams 0 at h0
    change readout emptyParams 1 = rhs emptyParams 1 at h1
    rw [h0, h1]
    norm_num [rhs, emptyParams]

noncomputable def registration :
    Contract.Registration
      (@replicated_evaluation.{u})
      (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Domination.MinusFourReplication.replicated_evaluation.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReplication.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ p x => readout p x) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Domination.MinusFourReplication
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReplication

namespace Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReplication.SupportEvaluation

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph
open _root_.D5.S3.Combinatorics.Graph.DominatingSetAverage
open _root_.D5.S3.Combinatorics.Graph.LocalDominatingStemBoundReplication
open _root_.D5.S3.Combinatorics.Graph.Domination.MinusFourReplication
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe u
noncomputable section
attribute [local instance] Classical.propDecidable

structure Params where
  V : Type u
  finite : Fintype V
  equality : DecidableEq V
  graph : SimpleGraph V
  support : V
  leaf : V
  leafProof : @Leaf V finite graph leaf
  edgeProof : graph.Adj leaf support
  copies : ℕ

def signature : DependentFamily.Signature where
  Params := Params.{u}
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def readout (p : Params.{u}) (x : ℤ) : ℤ := by
  letI := p.finite
  letI := p.equality
  exact evaluation (replicated p.graph {p.support} p.copies) x

def rhs (p : Params.{u}) (x : ℤ) : ℤ := by
  letI := p.finite
  letI := p.equality
  exact x * (x + 2) * (evaluation p.graph x) ^ p.copies

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ p x => readout p x) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ p x, R.readout () p x = rhs p x

abbrev sourceScope := type_of% (@support_replication_evaluation.{u})

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h p x
    exact @h p.V p.finite p.equality p.graph p.support p.leaf p.leafProof p.edgeProof p.copies x
  · intro h V finite equality graph support leaf leafProof edgeProof copies x
    exact h ⟨V, finite, equality, graph, support, leaf, leafProof, edgeProof, copies⟩ x

theorem actual_positive : arena.Law actual := source_bridge.mp support_replication_evaluation

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (1 : ℤ)) (fun e => nomatch e)

def emptyParams : Params.{u} :=
  ⟨ULift.{u} (Fin 2), inferInstance, inferInstance, ⊤, ⟨0⟩, ⟨1⟩,
    by classical; simp [Leaf, SimpleGraph.degree_top], by simp, 0⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h emptyParams 0
  change (1 : ℤ) = rhs emptyParams 0 at hz
  norm_num [rhs, emptyParams] at hz

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨emptyParams, 0, 1, ?_⟩
    change readout emptyParams 0 ≠ readout emptyParams 1
    have h0 := actual_positive emptyParams 0
    have h1 := actual_positive emptyParams 1
    change readout emptyParams 0 = rhs emptyParams 0 at h0
    change readout emptyParams 1 = rhs emptyParams 1 at h1
    rw [h0, h1]
    norm_num [rhs, emptyParams]

noncomputable def registration :
    Contract.Registration
      (@support_replication_evaluation.{u})
      (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Domination.MinusFourReplication.support_replication_evaluation.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReplication.SupportEvaluation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ p x => readout p x) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Domination.MinusFourReplication
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Reg.D5.S3.Combinatorics.Graph.Domination.MinusFourReplication.SupportEvaluation
