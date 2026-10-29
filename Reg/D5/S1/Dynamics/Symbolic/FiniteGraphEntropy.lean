import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing
open _root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
open SymbolicDynamics
open Set Function
open scoped Topology

namespace Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy

noncomputable section
universe u

structure Parameters where
  V : Type u
  fintypeV : Fintype V
  topologyV : TopologicalSpace V
  discreteV : @DiscreteTopology V topologyV

abbrev signature : Signature where
  Params := Parameters.{u}
  State P := P.V → P.V → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set (ℕ → P.V)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ edge => edgeLanguage edge) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ P _ => (∅ : Set (ℕ → P.V))) (fun e => nomatch e)

private def sampleParameters : Parameters.{u} where
  V := ULift.{u} Unit
  fintypeV := inferInstance
  topologyV := inferInstance
  discreteV := inferInstance

private def sampleEdgeTrue : sampleParameters.V → sampleParameters.V → Prop :=
  fun _ _ => True

private def sampleEdgeFalse : sampleParameters.V → sampleParameters.V → Prop :=
  fun _ _ => False

private theorem sampleLanguage_nonempty :
    (edgeLanguage sampleEdgeTrue).Nonempty := by
  refine ⟨fun _ => ULift.up (), ?_⟩
  refine ⟨fun _ => ULift.up (), ?_, ?_⟩
  · intro n
    trivial
  · intro n
    rfl

def compactArena : Arena where
  signature := signature.{u}
  Law r := ∀ (P : Parameters.{u}) (edge : P.V → P.V → Prop),
    letI := P.topologyV
    letI := P.discreteV
    r.readout () P edge = edgeLanguage edge ∧
      IsCompact (r.readout () P edge) ∧ IsClosed (r.readout () P edge)

private theorem compact_actual_law : compactArena.{u}.Law actual := by
  intro P edge
  refine ⟨rfl, ?_⟩
  exact @_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_isCompact_isClosed
    P.V P.fintypeV P.topologyV P.discreteV edge

/- The source declaration quantifies its carrier and instances implicitly.
   Expose the same law through the explicit parameter record used by the
   registration so telescope reconstruction sees the parameter binders in the
   source shape, while the proof still comes from the original theorem. -/
theorem compact_source_statement :
    ∀ (P : Parameters.{u}) (edge : P.V → P.V → Prop),
      letI := P.topologyV
      letI := P.discreteV
      actual.readout () P edge = edgeLanguage edge ∧
        IsCompact (actual.readout () P edge) ∧ IsClosed (actual.readout () P edge) := by
  intro P edge
  refine ⟨rfl, ?_⟩
  exact @_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_isCompact_isClosed
    P.V P.fintypeV P.topologyV P.discreteV edge

private theorem compact_rejected_law : ¬ compactArena.{u}.Law rejected := by
  intro h
  have hzero := (h sampleParameters sampleEdgeTrue).1
  change (∅ : Set (ℕ → sampleParameters.V)) = edgeLanguage sampleEdgeTrue at hzero
  obtain ⟨word, hword⟩ := sampleLanguage_nonempty
  have hmem : word ∈ (∅ : Set (ℕ → sampleParameters.V)) := by
    rw [hzero]
    exact hword
  exact hmem

theorem compact_source_bridge :
    (type_of% (@compact_source_statement.{u})) ↔
      compactArena.{u}.Law actual := by
  constructor
  · intro h P edge
    exact h P edge
  · intro h P edge
    exact h P edge

def compactFamily : Registration compactArena.{u}
    (type_of% (@compact_source_statement.{u})) where
  actual := actual
  bridge := compact_source_bridge
  variation := ⟨compact_actual_law, rejected, compact_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, compact_rejected_law⟩
      intro j hj
      cases j
      exact (hj rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨sampleParameters, sampleEdgeTrue, sampleEdgeFalse, ?_⟩
    intro heq
    change edgeLanguage sampleEdgeTrue = edgeLanguage sampleEdgeFalse at heq
    have hmem : (fun _ : ℕ => (ULift.up () : sampleParameters.V)) ∈
        edgeLanguage sampleEdgeFalse := by
      rw [← heq]
      exact sampleLanguage_nonempty.some_mem
    rcases hmem with ⟨path, hpath, _⟩
    exact hpath 0

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compact_source_statement.{u})
    (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_isCompact_isClosed.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.compactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨compactArena.{u}⟩
  objectArena := .source ⟨compactArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source compactArena.{u} ⟨compactFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ P edge => edgeLanguage edge) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def shiftArena : Arena where
  signature := signature.{u}
  Law r := ∀ (P : Parameters.{u}) (edge : P.V → P.V → Prop),
    letI := P.topologyV
    letI := P.discreteV
    r.readout () P edge = edgeLanguage edge ∧
      MapsTo (FullShift.shift (1 : ℕ)) (r.readout () P edge) (r.readout () P edge)

private theorem shift_actual_law : shiftArena.{u}.Law actual := by
  intro P edge
  refine ⟨rfl, ?_⟩
  exact @_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_shift_invariant
    P.V P.fintypeV P.topologyV P.discreteV edge

theorem shift_source_statement :
    ∀ (P : Parameters.{u}) (edge : P.V → P.V → Prop),
      letI := P.topologyV
      letI := P.discreteV
      actual.readout () P edge = edgeLanguage edge ∧
        MapsTo (FullShift.shift (1 : ℕ)) (actual.readout () P edge) (actual.readout () P edge) := by
  intro P edge
  refine ⟨rfl, ?_⟩
  exact @_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_shift_invariant
    P.V P.fintypeV P.topologyV P.discreteV edge

private theorem shift_rejected_law : ¬ shiftArena.{u}.Law rejected := by
  intro h
  have hzero := (h sampleParameters sampleEdgeTrue).1
  change (∅ : Set (ℕ → sampleParameters.V)) = edgeLanguage sampleEdgeTrue at hzero
  obtain ⟨word, hword⟩ := sampleLanguage_nonempty
  have hmem : word ∈ (∅ : Set (ℕ → sampleParameters.V)) := by
    rw [hzero]
    exact hword
  exact hmem

theorem shift_source_bridge :
    (type_of% (@shift_source_statement.{u})) ↔
      shiftArena.{u}.Law actual := by
  constructor
  · intro h P edge
    exact h P edge
  · intro h P edge
    exact h P edge

def shiftFamily : Registration shiftArena.{u}
    (type_of% (@shift_source_statement.{u})) where
  actual := actual
  bridge := shift_source_bridge
  variation := ⟨shift_actual_law, rejected, shift_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, shift_rejected_law⟩
      intro j hj
      cases j
      exact (hj rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨sampleParameters, sampleEdgeTrue, sampleEdgeFalse, ?_⟩
    intro heq
    change edgeLanguage sampleEdgeTrue = edgeLanguage sampleEdgeFalse at heq
    have hmem : (fun _ : ℕ => (ULift.up () : sampleParameters.V)) ∈
        edgeLanguage sampleEdgeFalse := by
      rw [← heq]
      exact sampleLanguage_nonempty.some_mem
    rcases hmem with ⟨path, hpath, _⟩
    exact hpath 0

noncomputable def registration_2 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@shift_source_statement.{u})
    (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_shift_invariant.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.shiftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨shiftArena.{u}⟩
  objectArena := .source ⟨shiftArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shiftArena.{u} ⟨shiftFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ P edge => edgeLanguage edge) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms compactFamily
#print axioms registration_1
#print axioms shiftFamily
#print axioms registration_2

end
end Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
