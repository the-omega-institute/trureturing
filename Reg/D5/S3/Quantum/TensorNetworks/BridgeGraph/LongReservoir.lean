import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Reg.Support.BridgeGraphRelations

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open Reg.Support.BridgeGraphRelations
open LeanInformationAudit
open Matrix Module Finset
open scoped BigOperators
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir

@[reducible] def base_witnessArena : Arena where
  signature := witnessPredicateSignature
  Law R := ∀ a b c d : ℕ, 0 < a → a < b → b < 2 * a →
    0 < c → c < d → d < 2 * c → R.readout () () a b c d
theorem base_witnessPositive : base_witnessArena.Law witnessPredicateActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir.base_witness
theorem base_witnessNegative : ¬ base_witnessArena.Law witnessPredicateRejected := by
  intro h
  exact h 2 3 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def base_witnessEvidence : Registration base_witnessArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir.base_witness)) where
  actual := witnessPredicateActual
  bridge := Iff.rfl
  variation := ⟨base_witnessPositive, witnessPredicateRejected, base_witnessNegative⟩
  sensitivity := ⟨fun i => ⟨witnessPredicateRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, base_witnessNegative⟩,
    fun i => nomatch i⟩
  dependence := witnessPredicateDependence

noncomputable def base_witnessRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir.base_witness)
    (type_of% (realize witnessPredicateSignature (fun _ _ a b c d => RationalWitness a b c d) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir.base_witness
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir.base_witnessArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir.base_witnessEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨base_witnessArena⟩, objectArena := .source ⟨base_witnessArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source base_witnessArena ⟨base_witnessEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize witnessPredicateSignature (fun _ _ a b c d => RationalWitness a b c d) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir, definition := some { owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound, name := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.BaseWitness, path := #[] },
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir.base_witness
#print axioms base_witnessPositive
#print axioms base_witnessNegative
#print axioms base_witnessEvidence
#print axioms base_witnessRegistration

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir
