import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Reg.Support.BridgeGraphRelations
import Reg.Support.BridgeGraphOriginalLaws

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open Reg.Support.BridgeGraphRelations
open LeanInformationAudit
open Matrix Module Finset
open scoped BigOperators
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent

@[reducible] def schur_rankArena : Arena where
  signature := natSignature
  Law R := ∀ (A B G D : ℕ) (hB : 0 < B) (hBA : B ≤ A)
    (hD : 0 < D) (hDG : D ≤ G) (κ : ℚ) (hκ : 0 < κ),
    R.readout () () ((schurMap A B G D κ).rank) (min (A * D) (B * G))
theorem schur_rankPositive : schur_rankArena.Law eqActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.schur_rank
theorem schur_rankNegative : ¬ schur_rankArena.Law natRejected := by
  intro h
  exact h 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 (by norm_num)

def schur_rankEvidence : Registration schur_rankArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.schur_rank)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨schur_rankPositive, natRejected, schur_rankNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, schur_rankNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def schur_rankRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.schur_rank)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.schur_rank
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.schur_rankArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.schur_rankEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨schur_rankArena⟩, objectArena := .source ⟨schur_rankArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source schur_rankArena ⟨schur_rankEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.schur_rank
#print axioms schur_rankPositive
#print axioms schur_rankNegative
#print axioms schur_rankEvidence
#print axioms schur_rankRegistration

open Reg.Support.BridgeGraphOriginalLaws
universe u_1 u_2

abbrev inclusionGeneratorSignature : Signature where
  Params := Σ m : Type u_1, Σ n : Type u_2, n → m
  State p := (p.2.1 → p.1) → Matrix p.1 p.2.1 ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.2.1 ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def inclusionGeneratorActual : Realization inclusionGeneratorSignature.{u_1,u_2} :=
  realize inclusionGeneratorSignature (fun _ p f => f p.2.2) (fun e => nomatch e)

def inclusionGeneratorRejected : Realization inclusionGeneratorSignature.{u_1,u_2} :=
  realize inclusionGeneratorSignature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def inclusionGeneratorArena : Arena where
  signature := inclusionGeneratorSignature.{u_1,u_2}
  Law R := ∀ {m : Type u_1} {n : Type u_2} [Fintype n] [DecidableEq m]
    (e : n → m) (he : Function.Injective e),
    Function.Injective (R.readout () ⟨m, ⟨n, e⟩⟩
      (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.inclusion m n ‹DecidableEq m›)).mulVec

theorem inclusionGeneratorPositive :
    inclusionGeneratorArena.{u_1,u_2}.Law inclusionGeneratorActual := by
  intro m n _ _ e he
  exact _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.inclusion_injective e he

theorem inclusionGeneratorNegative :
    ¬ inclusionGeneratorArena.{u_1,u_2}.Law inclusionGeneratorRejected := by
  intro h
  let e : ULift.{u_2} Unit → ULift.{u_1} Unit := fun _ => ⟨()⟩
  have he : Function.Injective e := fun _ _ _ => Subsingleton.elim _ _
  have hinj := h e he
  change Function.Injective (0 : Matrix (ULift.{u_1} Unit) (ULift.{u_2} Unit) ℚ).mulVec at hinj
  have hv := hinj (show (0 : Matrix (ULift.{u_1} Unit) (ULift.{u_2} Unit) ℚ).mulVec
      (fun _ => 0) = (0 : Matrix (ULift.{u_1} Unit) (ULift.{u_2} Unit) ℚ).mulVec
      (fun _ => 1) by simp only [Matrix.zero_mulVec])
  have hq := congrFun hv (⟨()⟩ : ULift.{u_2} Unit)
  norm_num at hq

theorem inclusionGeneratorDependence :
    ObservationalDependence inclusionGeneratorSignature.{u_1,u_2} inclusionGeneratorActual := by
  intro i
  let e : ULift.{u_2} Unit → ULift.{u_1} Unit := fun _ => ⟨()⟩
  let p : inclusionGeneratorSignature.{u_1,u_2}.Params :=
    ⟨ULift.{u_1} Unit, ⟨ULift.{u_2} Unit, e⟩⟩
  let G : inclusionGeneratorSignature.{u_1,u_2}.State p :=
    @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.inclusion
      (ULift.{u_1} Unit) (ULift.{u_2} Unit) inferInstance
  let Z : inclusionGeneratorSignature.{u_1,u_2}.State p := fun _ => 0
  refine ⟨p, G, Z, ?_⟩
  intro h
  have hq := congrFun (congrFun h (⟨()⟩ : ULift.{u_1} Unit))
    (⟨()⟩ : ULift.{u_2} Unit)
  norm_num [inclusionGeneratorActual, realize, p, G, Z, e, inclusion,
    Matrix.submatrix, Matrix.one_apply] at hq

def inclusionGeneratorEvidence : Registration inclusionGeneratorArena.{u_1,u_2}
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.inclusion_injective.{u_1,u_2})) where
  actual := inclusionGeneratorActual
  bridge := Iff.rfl
  variation := ⟨inclusionGeneratorPositive, inclusionGeneratorRejected, inclusionGeneratorNegative⟩
  sensitivity := ⟨fun i => ⟨inclusionGeneratorRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, inclusionGeneratorNegative⟩,
    fun i => nomatch i⟩
  dependence := inclusionGeneratorDependence

noncomputable def inclusion_injectiveRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.inclusion_injective.{u_1,u_2})
    (type_of% (realize inclusionGeneratorSignature.{u_1,u_2}
      (fun _ p f => f p.2.2) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.inclusion_injective
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.inclusionGeneratorArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.inclusionGeneratorEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨inclusionGeneratorArena.{u_1,u_2}⟩,
  objectArena := .source ⟨inclusionGeneratorArena.{u_1,u_2}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source inclusionGeneratorArena.{u_1,u_2} ⟨inclusionGeneratorEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize inclusionGeneratorSignature.{u_1,u_2}
      (fun _ p f => f p.2.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent, definition := none,
    coordinates := #[0, 1, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.inclusion_injective
#print axioms inclusionGeneratorPositive
#print axioms inclusionGeneratorNegative
#print axioms inclusionGeneratorDependence
#print axioms inclusionGeneratorEvidence
#print axioms inclusion_injectiveRegistration

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
