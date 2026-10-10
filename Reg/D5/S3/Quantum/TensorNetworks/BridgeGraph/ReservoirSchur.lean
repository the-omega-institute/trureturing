import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Reg.Support.BridgeGraphRelations

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open Reg.Support.BridgeGraphRelations
open LeanInformationAudit
open Matrix Module Finset
open scoped BigOperators
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur

@[reducible] def widthTwo_mulVec_blockArena : Arena where
  signature := rationalSignature
  Law R := ∀ (p q alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength q gamma delta t)) → ℚ)
    (i : (Fin alpha ⊕ Fin beta)) (j : (Fin gamma ⊕ Fin delta))
    (s : Fin (blockLength p alpha beta i)) (t : Fin (blockLength q gamma delta j + 1)),
    R.readout () () ((widthTwoMatrix p q alpha beta gamma delta).mulVec u (⟨i, s⟩, ⟨j, t⟩)) ((pencil (blockLength p alpha beta i) (blockLength q gamma delta j)).mulVec
        (localSource p q alpha beta gamma delta u i j) (s, t))
theorem widthTwo_mulVec_blockPositive : widthTwo_mulVec_blockArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.widthTwo_mulVec_block
theorem widthTwo_mulVec_blockNegative : ¬ widthTwo_mulVec_blockArena.Law rationalRejected := by
  intro h
  exact h 1 1 1 0 1 0 (fun _ => 0) (Sum.inl 0) (Sum.inl 0) ⟨0, by dsimp [blockLength]; omega⟩ ⟨0, by dsimp [blockLength]; omega⟩

def widthTwo_mulVec_blockEvidence : Registration widthTwo_mulVec_blockArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.widthTwo_mulVec_block)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨widthTwo_mulVec_blockPositive, rationalRejected, widthTwo_mulVec_blockNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, widthTwo_mulVec_blockNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def widthTwo_mulVec_blockRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.widthTwo_mulVec_block)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.widthTwo_mulVec_block
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.widthTwo_mulVec_blockArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.widthTwo_mulVec_blockEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨widthTwo_mulVec_blockArena⟩, objectArena := .source ⟨widthTwo_mulVec_blockArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source widthTwo_mulVec_blockArena ⟨widthTwo_mulVec_blockEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.widthTwo_mulVec_block
#print axioms widthTwo_mulVec_blockPositive
#print axioms widthTwo_mulVec_blockNegative
#print axioms widthTwo_mulVec_blockEvidence
#print axioms widthTwo_mulVec_blockRegistration

@[reducible] def cokernel_mulVec_formulaArena : Arena where
  signature := rationalSignature
  Law R := ∀ (p alpha beta gamma delta : ℕ)
    (z : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1)) → ℚ) (k : Fin beta) (j : Fin gamma),
    R.readout () () (((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose).mulVec z (k,j)) (∑ t : Fin (p+1), (-1 : ℚ)^t.val *
        z (⟨Sum.inr k, ⟨p-t.val, by dsimp [blockLength]; omega⟩⟩, ⟨Sum.inl j,t⟩))
theorem cokernel_mulVec_formulaPositive : cokernel_mulVec_formulaArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_mulVec_formula
theorem cokernel_mulVec_formulaNegative : ¬ cokernel_mulVec_formulaArena.Law rationalRejected := by
  intro h
  exact h 0 0 1 1 0 (fun _ => 0) 0 0

def cokernel_mulVec_formulaEvidence : Registration cokernel_mulVec_formulaArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_mulVec_formula)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨cokernel_mulVec_formulaPositive, rationalRejected, cokernel_mulVec_formulaNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cokernel_mulVec_formulaNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def cokernel_mulVec_formulaRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_mulVec_formula)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_mulVec_formula
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_mulVec_formulaArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_mulVec_formulaEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨cokernel_mulVec_formulaArena⟩, objectArena := .source ⟨cokernel_mulVec_formulaArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source cokernel_mulVec_formulaArena ⟨cokernel_mulVec_formulaEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_mulVec_formula
#print axioms cokernel_mulVec_formulaPositive
#print axioms cokernel_mulVec_formulaNegative
#print axioms cokernel_mulVec_formulaEvidence
#print axioms cokernel_mulVec_formulaRegistration

@[reducible] def short_short_witnessArena : Arena where
  signature := witnessPredicateSignature
  Law R := ∀ (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (hB : 0 < beta) (hBA : beta ≤ alpha) (hD : 0 < delta) (hDG : delta ≤ gamma),
    R.readout () () (leftDim p alpha beta) (rightDim p alpha beta) (leftDim p gamma delta) (rightDim p gamma delta)
theorem short_short_witnessPositive : short_short_witnessArena.Law witnessPredicateActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.short_short_witness
theorem short_short_witnessNegative : ¬ short_short_witnessArena.Law witnessPredicateRejected := by
  intro h
  exact h 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def short_short_witnessEvidence : Registration short_short_witnessArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.short_short_witness)) where
  actual := witnessPredicateActual
  bridge := Iff.rfl
  variation := ⟨short_short_witnessPositive, witnessPredicateRejected, short_short_witnessNegative⟩
  sensitivity := ⟨fun i => ⟨witnessPredicateRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, short_short_witnessNegative⟩,
    fun i => nomatch i⟩
  dependence := witnessPredicateDependence

noncomputable def short_short_witnessRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.short_short_witness)
    (type_of% (realize witnessPredicateSignature (fun _ _ a b c d => RationalWitness a b c d) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.short_short_witness
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.short_short_witnessArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.short_short_witnessEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨short_short_witnessArena⟩, objectArena := .source ⟨short_short_witnessArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source short_short_witnessArena ⟨short_short_witnessEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize witnessPredicateSignature (fun _ _ a b c d => RationalWitness a b c d) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.short_short_witness
#print axioms short_short_witnessPositive
#print axioms short_short_witnessNegative
#print axioms short_short_witnessEvidence
#print axioms short_short_witnessRegistration

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur
