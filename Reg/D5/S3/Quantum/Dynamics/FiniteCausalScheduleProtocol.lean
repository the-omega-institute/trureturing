import D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol
import Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
open D5.S3.Quantum.Dynamics.FiniteCausalPortGraph
open D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol
open D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
open D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
namespace Reg.D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol

abbrev probabilitySignature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def probabilityActual : Realization probabilitySignature :=
  realize probabilitySignature (fun _ _ x y => x = y) (fun e => nomatch e)
def probabilityRejected : Realization probabilitySignature :=
  realize probabilitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem probabilityDependence : ObservationalDependence probabilitySignature probabilityActual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have hh : (0 : ℂ) = 1 := (congrFun h 1).mpr rfl
  exact zero_ne_one hh

abbrev programArena : Arena where
  signature := probabilitySignature
  Law r := ∀ {I : Interface} (P : Program I) (X : CutState I),
    ∃! φ : Assignment P, GraphLaw φ ∧ rootValue φ = X ∧
      r.readout () () (((leaves φ).map (fun z => Matrix.trace z.state)).sum) (Matrix.trace X)

private theorem program_rejected : ¬ programArena.Law probabilityRejected := by
  intro h
  let I : Interface := ⟨Unit,inferInstance,inferInstance⟩
  obtain ⟨φ,hφ,_⟩ := h (.stop I) 0
  exact hφ.2.2

abbrev scheduleArena : Arena where
  signature := signature.{0}
  Law r := ∀ {E : Type} [PartialOrder E] (G : QuantumPortGraph E) {K L : Set E}
    (l : List E) (hl : Exec K l L) (h : Records G.outcomes) (X : State (G.cut K))
    (hK : IsLowerSet K) (hL : IsLowerSet L) (hfin : L.Finite),
    letI := G.finiteCut K
    ∃! φ : Assignment (compile G l hl (fun d : K => h d)),
      (GraphLaw φ ∧ rootValue φ = X ∧
        ((leaves φ).map (fun z => Matrix.trace z.state)).sum = Matrix.trace X) ∧
      (⟨l.map (fun e => (h e).val),cutInterface G L,pathMap (G.readout h) l hl X⟩ : Terminal) ∈ leaves φ ∧
      (∀ (m : List E) (hm : Exec K m L),
        r.readout () (State (G.cut L)) (pathMap (G.readout h) l hl X) (pathMap (G.readout h) m hm X)) ∧
      (∀ z ∈ leaves φ, z.history.length = (L \ K).ncard)

private theorem schedule_rejected : ¬ scheduleArena.Law rejected := by
  intro h
  let G : QuantumPortGraph Empty := {
    cut := fun _ => Unit
    finiteCut := fun _ => inferInstance
    decidableCut := fun _ => inferInstance
    outcomes := fun e => nomatch e
    hidden := fun e => nomatch e
    kraus := fun {K} {e} _ => nomatch e
    normalized := fun {K} {e} _ _ => nomatch e
    square := fun {K} {a} {b} _ _ => nomatch a }
  obtain ⟨φ,hφ,_⟩ := h G (K := ∅) (L := ∅) [] rfl (fun e => nomatch e) 0
    (by simp [IsLowerSet]) (by simp [IsLowerSet]) Set.finite_empty
  exact hφ.2.2.1 [] rfl

private theorem dependence : ObservationalDependence signature.{0} actual := by
  intro i
  refine ⟨Matrix Unit Unit ℂ,0,1,?_⟩
  intro h
  have hh : (0 : Matrix Unit Unit ℂ) = 1 := (congrFun h 1).mpr rfl
  have hk := congrArg (fun X : Matrix Unit Unit ℂ => X () ()) hh
  simpa using hk

def programFamily : Registration programArena (type_of% (@program_graph_correspondence)) where
  actual := probabilityActual
  bridge := Iff.rfl
  variation := ⟨@program_graph_correspondence,probabilityRejected,program_rejected⟩
  sensitivity := ⟨fun i => ⟨probabilityRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,program_rejected⟩,fun e => nomatch e⟩
  dependence := probabilityDependence

def programRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@program_graph_correspondence)
    (type_of% (realize probabilitySignature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol.program_graph_correspondence.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol.programFamily
  realizationSource := none
  generated := false
  arena := .source ⟨programArena⟩
  objectArena := .source ⟨programArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source programArena ⟨programFamily⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize probabilitySignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","arg","arg","fn","arg","body","arg","arg","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms programFamily
def scheduleFamily : Registration scheduleArena (type_of% (@causal_schedule_realization)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@causal_schedule_realization,rejected,schedule_rejected⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,schedule_rejected⟩,fun e => nomatch e⟩
  dependence := dependence

def scheduleRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@causal_schedule_realization)
    (type_of% (realize signature.{0} (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol.causal_schedule_realization.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol.scheduleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨scheduleArena⟩
  objectArena := .source ⟨scheduleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source scheduleArena ⟨scheduleFamily⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","arg","arg","fn","arg","body","arg","arg","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms scheduleFamily
end Reg.D5.S3.Quantum.Dynamics.FiniteCausalScheduleProtocol
