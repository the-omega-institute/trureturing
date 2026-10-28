import D5.S3.Quantum.Dynamics.FiniteCausalPortGraph
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Quantum.Dynamics.FiniteCausalPortGraph
open D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
open D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
namespace Reg.D5.S3.Quantum.Dynamics.FiniteCausalPortGraph
universe i j o p m n v
abbrev signature : Signature where
  Params := Type v
  State T := T
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ T := T → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature.{v} := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev interchangeArena : Arena where
  signature := signature.{max o p}
  Law r := ∀ {I : Type i} {J : Type j} {O : Type o} {P : Type p} {M : Type m} {N : Type n}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Fintype P] [DecidableEq P] [Fintype M] [Fintype N]
    (A : M → Matrix O I ℂ) (B : N → Matrix P J ℂ) (ρ : State (I × J)),
    r.readout () (State (O × P)) (rightBranch B (leftBranch A ρ)) (leftBranch A (rightBranch B ρ))

private theorem interchangeRejected : ¬ interchangeArena.{i,j,o,p,m,n}.Law rejected := by
  intro h
  exact h (I := ULift.{i} Unit) (J := ULift.{j} Unit)
    (O := ULift.{o} Unit) (P := ULift.{p} Unit)
    (M := ULift.{m} Unit) (N := ULift.{n} Unit) (fun _ => 0) (fun _ => 0) 0

private theorem dependence : ObservationalDependence signature.{v} actual := by
  intro r
  refine ⟨Matrix (ULift.{v} Unit) (ULift.{v} Unit) ℂ,0,1,?_⟩
  intro h
  have he : (0 : Matrix (ULift.{v} Unit) (ULift.{v} Unit) ℂ) = 1 :=
    (congrFun h 1).mpr rfl
  have hh := congrArg (fun X => X (ULift.up ()) (ULift.up ())) he
  simpa using hh

abbrev scheduleArena : Arena where
  signature := signature.{0}
  Law r := ∀ {E : Type} [PartialOrder E] (G : QuantumPortGraph E) (h : Records G.outcomes)
    {I J : Set E}, IsLowerSet I → IsLowerSet J → J.Finite →
    ∀ (l m : List E) (hl : Exec I l J) (hm : Exec I m J) (X : State (G.cut I)),
    r.readout () (State (G.cut J)) (pathMap (G.readout h) l hl X) (pathMap (G.readout h) m hm X)

private theorem scheduleRejected : ¬ scheduleArena.Law rejected := by
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
  exact h G (fun e => nomatch e) (I := ∅) (J := ∅)
    (by simp [IsLowerSet]) (by simp [IsLowerSet]) Set.finite_empty [] [] rfl rfl 0

def interchangeFamily : Registration interchangeArena.{i,j,o,p,m,n} (type_of% (@disjoint_port_interchange.{i,j,o,p,m,n})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@disjoint_port_interchange,rejected,interchangeRejected⟩
  sensitivity := ⟨fun r => ⟨rejected,
    fun q hq => (hq (Subsingleton.elim q r)).elim,rfl,interchangeRejected⟩,fun e => nomatch e⟩
  dependence := dependence

def interchangeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@disjoint_port_interchange.{i,j,o,p,m,n})
    (type_of% (realize signature.{max o p} (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.FiniteCausalPortGraph.disjoint_port_interchange.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FiniteCausalPortGraph.interchangeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨interchangeArena⟩
  objectArena := .source ⟨interchangeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source interchangeArena ⟨interchangeFamily⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.FiniteCausalPortGraph
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms interchangeFamily

def scheduleFamily : Registration scheduleArena (type_of% (@quantum_schedule_independence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quantum_schedule_independence,rejected,scheduleRejected⟩
  sensitivity := ⟨fun r => ⟨rejected,
    fun q hq => (hq (Subsingleton.elim q r)).elim,rfl,scheduleRejected⟩,fun e => nomatch e⟩
  dependence := dependence

def scheduleRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quantum_schedule_independence)
    (type_of% (realize signature.{0} (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.FiniteCausalPortGraph.quantum_schedule_independence.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FiniteCausalPortGraph.scheduleFamily
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
    owner := `D5.S3.Quantum.Dynamics.FiniteCausalPortGraph
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms scheduleFamily
end Reg.D5.S3.Quantum.Dynamics.FiniteCausalPortGraph
