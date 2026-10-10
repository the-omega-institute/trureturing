import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Reg.Support.BridgeGraphRelations

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open Reg.Support.BridgeGraphRelations
open LeanInformationAudit
open Matrix Module Finset
open scoped BigOperators
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit

@[reducible] def castling_provedArena : Arena where
  signature := integerSignature
  Law R := ∀ a b c d : ℕ, a ≤ 3 * b → c ≤ 3 * d →
    R.readout () () ((a * d : ℕ) - (QMaxFlow a b c d : ℤ)) ((b * (3 * d - c) : ℕ) - (QMaxFlow b (3 * b - a) d (3 * d - c) : ℤ))
theorem castling_provedPositive : castling_provedArena.Law integerActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit.castling_proved
theorem castling_provedNegative : ¬ castling_provedArena.Law integerRejected := by
  intro h
  exact h 0 0 0 0 (by omega) (by omega)

def castling_provedEvidence : Registration castling_provedArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit.castling_proved)) where
  actual := integerActual
  bridge := Iff.rfl
  variation := ⟨castling_provedPositive, integerRejected, castling_provedNegative⟩
  sensitivity := ⟨fun i => ⟨integerRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, castling_provedNegative⟩,
    fun i => nomatch i⟩
  dependence := integerDependence

noncomputable def castling_provedRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit.castling_proved)
    (type_of% (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit.castling_proved
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit.castling_provedArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit.castling_provedEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨castling_provedArena⟩, objectArena := .source ⟨castling_provedArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source castling_provedArena ⟨castling_provedEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit, definition := some { owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound, name := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.Castling, path := #[] },
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit.castling_proved
#print axioms castling_provedPositive
#print axioms castling_provedNegative
#print axioms castling_provedEvidence
#print axioms castling_provedRegistration

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit
