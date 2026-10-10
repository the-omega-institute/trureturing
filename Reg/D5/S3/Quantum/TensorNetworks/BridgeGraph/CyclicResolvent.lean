import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Reg.Support.BridgeGraphRelations

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

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
