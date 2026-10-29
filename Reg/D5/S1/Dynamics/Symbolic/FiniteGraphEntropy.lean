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
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_isCompact_isClosed.{u})) ↔
      compactArena.{u}.Law actual := by
  constructor
  · intro h P edge
    refine ⟨rfl, ?_⟩
    exact @h P.V P.fintypeV P.topologyV P.discreteV edge
  · intro h V fintypeV topologyV discreteV edge
    let P : Parameters.{u} := {
      V := V
      fintypeV := fintypeV
      topologyV := topologyV
      discreteV := discreteV }
    exact (h P edge).2

def compactFamily : Registration compactArena.{u}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_isCompact_isClosed.{u})) where
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
    (@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_isCompact_isClosed.{u})
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
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := none
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
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_shift_invariant.{u})) ↔
      shiftArena.{u}.Law actual := by
  constructor
  · intro h P edge
    refine ⟨rfl, ?_⟩
    exact @h P.V P.fintypeV P.topologyV P.discreteV edge
  · intro h V fintypeV topologyV discreteV edge
    let P : Parameters.{u} := {
      V := V
      fintypeV := fintypeV
      topologyV := topologyV
      discreteV := discreteV }
    exact (h P edge).2

def shiftFamily : Registration shiftArena.{u}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_shift_invariant.{u})) where
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
    (@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_shift_invariant.{u})
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
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms compactFamily
#print axioms registration_1
#print axioms shiftFamily
#print axioms registration_2

end
end Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
