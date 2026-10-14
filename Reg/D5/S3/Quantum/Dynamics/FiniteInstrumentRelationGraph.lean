import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Dynamics.FiniteInstrumentRelationGraph
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Quantum.Recovery.FiniteLocalProtocol
open D5.S3.Quantum.Dynamics.FiniteInstrumentRelationGraph
noncomputable section
namespace Reg.D5.S3.Quantum.Dynamics.FiniteInstrumentRelationGraph

abbrev signature : Signature where
  Params := Type × Type × Type
  State p := List (Terminal p.2.2 p.2.1 p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List (Terminal p.2.2 p.2.1 p.1) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {A R Feedback : Type} [Fintype A] [DecidableEq A] [Fintype R]
    {d : A → ℕ} (T : Tree Feedback d) (X : State R d),
    ∃! φ : Assignment (R := R) T, GraphLaw φ ∧ rootValue φ = X ∧
      r.readout () ⟨A,R,Feedback⟩ (graphLeaves φ) (terminalOutputs T X) ∧
      graphPrefixes φ = coarsePrefixes T X ∧
      ((graphLeaves φ).map (fun z => Matrix.trace z.state)).sum = Matrix.trace X

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let T : Tree Unit (fun _ : Unit => 1) := .leaf ()
  obtain ⟨φ,hφ,_⟩ := h (R := Unit) T 0
  exact hφ.2.2.1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let z : Terminal Unit Unit Unit := ⟨[],(),fun _ => 0,0⟩
  refine ⟨⟨Unit,Unit,Unit⟩,[],[z],?_⟩
  intro h
  have he := congrFun h []
  have hc : [z] = [] := he.mp rfl
  simpa using congrArg List.length hc

def family : Registration arena (type_of% (@relation_graph_protocol_correspondence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@relation_graph_protocol_correspondence,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@relation_graph_protocol_correspondence)
    (type_of% (realize signature (fun _ _ x y => x = y) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.FiniteInstrumentRelationGraph.relation_graph_protocol_correspondence.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FiniteInstrumentRelationGraph.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.FiniteInstrumentRelationGraph
    definition := none
    coordinates := #[0,1,2,7,8]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]}

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Dynamics.FiniteInstrumentRelationGraph
