import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Reg.Support.BridgeGraphRelations

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open Reg.Support.BridgeGraphRelations
open LeanInformationAudit
open Matrix Module Finset
open scoped BigOperators
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut

@[reducible] def resultArena : Arena where
  signature := natSignature
  Law R := ∀ a b c d : ℕ, 0 < a → a ≤ b → 0 < c → c ≤ d →
    a * a + b * b ≤ 3 * a * b → c * c + d * d ≤ 3 * c * d →
    R.readout () () (QMaxFlow a b c d) (QMinCut a b c d) ∧
      QMinCut a b c d = min (a * d) (b * c)
theorem resultPositive : resultArena.Law eqActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut.result
theorem resultNegative : ¬ resultArena.Law natRejected := by
  intro h
  exact (h 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

def resultEvidence : Registration resultArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut.result)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨resultPositive, natRejected, resultNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, resultNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def resultRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut.result)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut.result
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut.resultArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut.resultEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨resultArena⟩, objectArena := .source ⟨resultArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source resultArena ⟨resultEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut, definition := some { owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut, name := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut.claim, path := #[] },
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut.result
#print axioms resultPositive
#print axioms resultNegative
#print axioms resultEvidence
#print axioms resultRegistration

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowMinCut
