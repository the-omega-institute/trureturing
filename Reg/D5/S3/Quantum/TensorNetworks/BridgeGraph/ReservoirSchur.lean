import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Reg.Support.BridgeGraphRelations
import Reg.Support.BridgeGraphOriginalLaws
import Reg.Support.BridgeGraphEqualityFamilies

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

open Reg.Support.BridgeGraphEqualityFamilies
universe u_1 u_2 u_3 u_4

@[reducible] def kernelMatrix_mulVecArena : Arena where
  signature := sourceVectorEqualitySignature
  Law R := ∀ (p alpha beta gamma delta : ℕ) (w : Fin alpha × Fin delta → ℚ),
    R.readout () ⟨p, ⟨alpha, ⟨beta, ⟨gamma, delta⟩⟩⟩⟩
      ((LinearMap.toMatrix' (kernelEmbedding p alpha beta gamma delta)).mulVec w)
      (kernelEmbedding p alpha beta gamma delta w)
theorem kernelMatrix_mulVecPositive : kernelMatrix_mulVecArena.Law sourceVectorEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelMatrix_mulVec
theorem kernelMatrix_mulVecNegative : ¬ kernelMatrix_mulVecArena.Law sourceVectorEqualityRejected := by
  intro h
  exact h 0 0 0 0 0 (fun _ => 0)

def kernelMatrix_mulVecEvidence : Registration kernelMatrix_mulVecArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelMatrix_mulVec)) where
  actual := sourceVectorEqualityActual
  bridge := Iff.rfl
  variation := ⟨kernelMatrix_mulVecPositive, sourceVectorEqualityRejected, kernelMatrix_mulVecNegative⟩
  sensitivity := ⟨fun i => ⟨sourceVectorEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, kernelMatrix_mulVecNegative⟩,
    fun i => nomatch i⟩
  dependence := sourceVectorEqualityDependence

noncomputable def kernelMatrix_mulVecRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelMatrix_mulVec)
    (type_of% (realize sourceVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelMatrix_mulVec
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelMatrix_mulVecArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelMatrix_mulVecEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨kernelMatrix_mulVecArena⟩, objectArena := .source ⟨kernelMatrix_mulVecArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source kernelMatrix_mulVecArena ⟨kernelMatrix_mulVecEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize sourceVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[0, 1, 2, 3, 4], readouts := #[{
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelMatrix_mulVec
#print axioms kernelMatrix_mulVecPositive
#print axioms kernelMatrix_mulVecNegative
#print axioms kernelMatrix_mulVecEvidence
#print axioms kernelMatrix_mulVecRegistration

@[reducible] def cokernelMatrix_mul_widthTwoArena : Arena where
  signature := annihilatorMatrixEqualitySignature
  Law R := ∀ (p alpha beta gamma delta : ℕ),
    R.readout () ⟨p, ⟨alpha, ⟨beta, ⟨gamma, delta⟩⟩⟩⟩
      ((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose *
        widthTwoMatrix p p alpha beta gamma delta) 0
theorem cokernelMatrix_mul_widthTwoPositive : cokernelMatrix_mul_widthTwoArena.Law annihilatorMatrixEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernelMatrix_mul_widthTwo
theorem cokernelMatrix_mul_widthTwoNegative : ¬ cokernelMatrix_mul_widthTwoArena.Law annihilatorMatrixEqualityRejected := by
  intro h
  exact h 0 0 0 0 0

def cokernelMatrix_mul_widthTwoEvidence : Registration cokernelMatrix_mul_widthTwoArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernelMatrix_mul_widthTwo)) where
  actual := annihilatorMatrixEqualityActual
  bridge := Iff.rfl
  variation := ⟨cokernelMatrix_mul_widthTwoPositive, annihilatorMatrixEqualityRejected, cokernelMatrix_mul_widthTwoNegative⟩
  sensitivity := ⟨fun i => ⟨annihilatorMatrixEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cokernelMatrix_mul_widthTwoNegative⟩,
    fun i => nomatch i⟩
  dependence := annihilatorMatrixEqualityDependence

noncomputable def cokernelMatrix_mul_widthTwoRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernelMatrix_mul_widthTwo)
    (type_of% (realize annihilatorMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernelMatrix_mul_widthTwo
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernelMatrix_mul_widthTwoArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernelMatrix_mul_widthTwoEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨cokernelMatrix_mul_widthTwoArena⟩, objectArena := .source ⟨cokernelMatrix_mul_widthTwoArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source cokernelMatrix_mul_widthTwoArena ⟨cokernelMatrix_mul_widthTwoEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize annihilatorMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[0, 1, 2, 3, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"],
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernelMatrix_mul_widthTwo
#print axioms cokernelMatrix_mul_widthTwoPositive
#print axioms cokernelMatrix_mul_widthTwoNegative
#print axioms cokernelMatrix_mul_widthTwoEvidence
#print axioms cokernelMatrix_mul_widthTwoRegistration

@[reducible] def kernel_sample_identityArena : Arena where
  signature := squarePairMatrixEqualitySignature
  Law R := ∀ (p alpha beta gamma delta : ℕ),
    R.readout () ⟨alpha, delta⟩
      ((inclusion (kernelSample p alpha beta gamma delta)).transpose *
        LinearMap.toMatrix' (kernelEmbedding p alpha beta gamma delta)) 1
theorem kernel_sample_identityPositive : kernel_sample_identityArena.Law squarePairMatrixEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_sample_identity
theorem kernel_sample_identityNegative : ¬ kernel_sample_identityArena.Law squarePairMatrixEqualityRejected := by
  intro h
  exact h 0 0 0 0 0

def kernel_sample_identityEvidence : Registration kernel_sample_identityArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_sample_identity)) where
  actual := squarePairMatrixEqualityActual
  bridge := Iff.rfl
  variation := ⟨kernel_sample_identityPositive, squarePairMatrixEqualityRejected, kernel_sample_identityNegative⟩
  sensitivity := ⟨fun i => ⟨squarePairMatrixEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, kernel_sample_identityNegative⟩,
    fun i => nomatch i⟩
  dependence := squarePairMatrixEqualityDependence

noncomputable def kernel_sample_identityRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_sample_identity)
    (type_of% (realize squarePairMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_sample_identity
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_sample_identityArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_sample_identityEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨kernel_sample_identityArena⟩, objectArena := .source ⟨kernel_sample_identityArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source kernel_sample_identityArena ⟨kernel_sample_identityEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize squarePairMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[1, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"],
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_sample_identity
#print axioms kernel_sample_identityPositive
#print axioms kernel_sample_identityNegative
#print axioms kernel_sample_identityEvidence
#print axioms kernel_sample_identityRegistration

@[reducible] def cokernel_sample_identityArena : Arena where
  signature := squarePairMatrixEqualitySignature
  Law R := ∀ (p alpha beta gamma delta : ℕ),
    R.readout () ⟨beta, gamma⟩
      ((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose *
        inclusion (cokernelSample p alpha beta gamma delta)) 1
theorem cokernel_sample_identityPositive : cokernel_sample_identityArena.Law squarePairMatrixEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_sample_identity
theorem cokernel_sample_identityNegative : ¬ cokernel_sample_identityArena.Law squarePairMatrixEqualityRejected := by
  intro h
  exact h 0 0 0 0 0

def cokernel_sample_identityEvidence : Registration cokernel_sample_identityArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_sample_identity)) where
  actual := squarePairMatrixEqualityActual
  bridge := Iff.rfl
  variation := ⟨cokernel_sample_identityPositive, squarePairMatrixEqualityRejected, cokernel_sample_identityNegative⟩
  sensitivity := ⟨fun i => ⟨squarePairMatrixEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cokernel_sample_identityNegative⟩,
    fun i => nomatch i⟩
  dependence := squarePairMatrixEqualityDependence

noncomputable def cokernel_sample_identityRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_sample_identity)
    (type_of% (realize squarePairMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_sample_identity
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_sample_identityArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_sample_identityEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨cokernel_sample_identityArena⟩, objectArena := .source ⟨cokernel_sample_identityArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source cokernel_sample_identityArena ⟨cokernel_sample_identityEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize squarePairMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[2, 3], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"],
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.cokernel_sample_identity
#print axioms cokernel_sample_identityPositive
#print axioms cokernel_sample_identityNegative
#print axioms cokernel_sample_identityEvidence
#print axioms cokernel_sample_identityRegistration

@[reducible] def inclusion_prodArena : Arena where
  signature := inclusionProductEqualitySignature.{u_1,u_2,u_3,u_4}
  Law R := ∀ {m : Type u_1} {n : Type u_2} {r : Type u_3} {s : Type u_4}
    [DecidableEq m] [DecidableEq r] (e : n → m) (f : s → r),
    R.readout () ⟨m, ⟨n, ⟨r, s⟩⟩⟩
      (inclusion (fun k : n × s => (e k.1, f k.2)))
      (kronecker (inclusion e) (inclusion f))
theorem inclusion_prodPositive : inclusion_prodArena.{u_1,u_2,u_3,u_4}.Law inclusionProductEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.inclusion_prod.{u_1,u_2,u_3,u_4}
theorem inclusion_prodNegative : ¬ inclusion_prodArena.{u_1,u_2,u_3,u_4}.Law inclusionProductEqualityRejected := by
  intro h
  exact h (m := ULift.{u_1} Unit) (n := ULift.{u_2} Unit)
    (r := ULift.{u_3} Unit) (s := ULift.{u_4} Unit)
    (fun _ => ⟨()⟩) (fun _ => ⟨()⟩)

def inclusion_prodEvidence : Registration inclusion_prodArena.{u_1,u_2,u_3,u_4}
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.inclusion_prod.{u_1,u_2,u_3,u_4})) where
  actual := inclusionProductEqualityActual
  bridge := Iff.rfl
  variation := ⟨inclusion_prodPositive, inclusionProductEqualityRejected, inclusion_prodNegative⟩
  sensitivity := ⟨fun i => ⟨inclusionProductEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, inclusion_prodNegative⟩,
    fun i => nomatch i⟩
  dependence := inclusionProductEqualityDependence

noncomputable def inclusion_prodRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.inclusion_prod.{u_1,u_2,u_3,u_4})
    (type_of% (realize inclusionProductEqualitySignature.{u_1,u_2,u_3,u_4} (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.inclusion_prod
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.inclusion_prodArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.inclusion_prodEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨inclusion_prodArena.{u_1,u_2,u_3,u_4}⟩, objectArena := .source ⟨inclusion_prodArena.{u_1,u_2,u_3,u_4}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source inclusion_prodArena.{u_1,u_2,u_3,u_4} ⟨inclusion_prodEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize inclusionProductEqualitySignature.{u_1,u_2,u_3,u_4} (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[0, 1, 2, 3], readouts := #[{
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.inclusion_prod
#print axioms inclusion_prodPositive
#print axioms inclusion_prodNegative
#print axioms inclusion_prodEvidence
#print axioms inclusion_prodRegistration

@[reducible] def singleCross_kroneckerArena : Arena where
  signature := crossMatrixEqualitySignature
  Law R := ∀ (p alpha beta gamma delta : ℕ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ),
    R.readout () ⟨p, ⟨alpha, ⟨beta, ⟨gamma, delta⟩⟩⟩⟩
      (singleCross p alpha beta gamma delta BM DM)
      (kronecker (singleThirdLeft p alpha beta BM)
        (singleThirdRight p gamma delta DM))
theorem singleCross_kroneckerPositive : singleCross_kroneckerArena.Law crossMatrixEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.singleCross_kronecker
theorem singleCross_kroneckerNegative : ¬ singleCross_kroneckerArena.Law crossMatrixEqualityRejected := by
  intro h
  exact h 0 0 0 0 0 0 0

def singleCross_kroneckerEvidence : Registration singleCross_kroneckerArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.singleCross_kronecker)) where
  actual := crossMatrixEqualityActual
  bridge := Iff.rfl
  variation := ⟨singleCross_kroneckerPositive, crossMatrixEqualityRejected, singleCross_kroneckerNegative⟩
  sensitivity := ⟨fun i => ⟨crossMatrixEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, singleCross_kroneckerNegative⟩,
    fun i => nomatch i⟩
  dependence := crossMatrixEqualityDependence

noncomputable def singleCross_kroneckerRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.singleCross_kronecker)
    (type_of% (realize crossMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.singleCross_kronecker
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.singleCross_kroneckerArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.singleCross_kroneckerEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨singleCross_kroneckerArena⟩, objectArena := .source ⟨singleCross_kroneckerArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source singleCross_kroneckerArena ⟨singleCross_kroneckerEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize crossMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[0, 1, 2, 3, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.singleCross_kronecker
#print axioms singleCross_kroneckerPositive
#print axioms singleCross_kroneckerNegative
#print axioms singleCross_kroneckerEvidence
#print axioms singleCross_kroneckerRegistration

@[reducible] def slLine_kernelEmbeddingArena : Arena where
  signature := coefficientVectorEqualitySignature
  Law R := ∀ (p alpha beta gamma delta : ℕ)
    (w : Fin alpha × Fin delta → ℚ) (r t : Fin (p + 1)),
    R.readout () ⟨alpha, delta⟩
      (slLine p alpha beta gamma delta (kernelEmbedding p alpha beta gamma delta w) r t)
      (if r.val + t.val = p then (-1 : ℚ) ^ (p-r.val) • w else 0)
theorem slLine_kernelEmbeddingPositive : slLine_kernelEmbeddingArena.Law coefficientVectorEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.slLine_kernelEmbedding
theorem slLine_kernelEmbeddingNegative : ¬ slLine_kernelEmbeddingArena.Law coefficientVectorEqualityRejected := by
  intro h
  exact h 0 0 0 0 0 (fun _ => 0) 0 0

def slLine_kernelEmbeddingEvidence : Registration slLine_kernelEmbeddingArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.slLine_kernelEmbedding)) where
  actual := coefficientVectorEqualityActual
  bridge := Iff.rfl
  variation := ⟨slLine_kernelEmbeddingPositive, coefficientVectorEqualityRejected, slLine_kernelEmbeddingNegative⟩
  sensitivity := ⟨fun i => ⟨coefficientVectorEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, slLine_kernelEmbeddingNegative⟩,
    fun i => nomatch i⟩
  dependence := coefficientVectorEqualityDependence

noncomputable def slLine_kernelEmbeddingRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.slLine_kernelEmbedding)
    (type_of% (realize coefficientVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.slLine_kernelEmbedding
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.slLine_kernelEmbeddingArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.slLine_kernelEmbeddingEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨slLine_kernelEmbeddingArena⟩, objectArena := .source ⟨slLine_kernelEmbeddingArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source slLine_kernelEmbeddingArena ⟨slLine_kernelEmbeddingEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize coefficientVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[1, 4], readouts := #[{
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.slLine_kernelEmbedding
#print axioms slLine_kernelEmbeddingPositive
#print axioms slLine_kernelEmbeddingNegative
#print axioms slLine_kernelEmbeddingEvidence
#print axioms slLine_kernelEmbeddingRegistration

@[reducible] def sourceSL_kernelEmbeddingArena : Arena where
  signature := sourceVectorEqualitySignature
  Law R := ∀ (p alpha beta gamma delta : ℕ) (w : Fin alpha × Fin delta → ℚ),
    R.readout () ⟨p, ⟨alpha, ⟨beta, ⟨gamma, delta⟩⟩⟩⟩
      (sourceSL p alpha beta gamma delta (kernelEmbedding p alpha beta gamma delta w))
      (kernelEmbedding p alpha beta gamma delta w)
theorem sourceSL_kernelEmbeddingPositive : sourceSL_kernelEmbeddingArena.Law sourceVectorEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.sourceSL_kernelEmbedding
theorem sourceSL_kernelEmbeddingNegative : ¬ sourceSL_kernelEmbeddingArena.Law sourceVectorEqualityRejected := by
  intro h
  exact h 0 0 0 0 0 (fun _ => 0)

def sourceSL_kernelEmbeddingEvidence : Registration sourceSL_kernelEmbeddingArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.sourceSL_kernelEmbedding)) where
  actual := sourceVectorEqualityActual
  bridge := Iff.rfl
  variation := ⟨sourceSL_kernelEmbeddingPositive, sourceVectorEqualityRejected, sourceSL_kernelEmbeddingNegative⟩
  sensitivity := ⟨fun i => ⟨sourceVectorEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, sourceSL_kernelEmbeddingNegative⟩,
    fun i => nomatch i⟩
  dependence := sourceVectorEqualityDependence

noncomputable def sourceSL_kernelEmbeddingRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.sourceSL_kernelEmbedding)
    (type_of% (realize sourceVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.sourceSL_kernelEmbedding
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.sourceSL_kernelEmbeddingArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.sourceSL_kernelEmbeddingEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨sourceSL_kernelEmbeddingArena⟩, objectArena := .source ⟨sourceSL_kernelEmbeddingArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source sourceSL_kernelEmbeddingArena ⟨sourceSL_kernelEmbeddingEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize sourceVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[0, 1, 2, 3, 4], readouts := #[{
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.sourceSL_kernelEmbedding
#print axioms sourceSL_kernelEmbeddingPositive
#print axioms sourceSL_kernelEmbeddingNegative
#print axioms sourceSL_kernelEmbeddingEvidence
#print axioms sourceSL_kernelEmbeddingRegistration

open Reg.Support.BridgeGraphOriginalLaws

noncomputable def kernelEmbedding_injectiveRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelEmbedding_injective)
    (type_of% (realize kernelFunctionSignature (fun _ _ f => @Decidable.decide (Function.Injective f)
      (Classical.propDecidable (Function.Injective f))) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelEmbedding_injective
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelEmbedding_injectiveArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelEmbedding_injectiveEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨kernelEmbedding_injectiveArena⟩,
  objectArena := .source ⟨kernelEmbedding_injectiveArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source kernelEmbedding_injectiveArena ⟨kernelEmbedding_injectiveEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize kernelFunctionSignature (fun _ _ f => @Decidable.decide (Function.Injective f)
      (Classical.propDecidable (Function.Injective f))) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[0, 1, 2, 3, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelEmbedding_injective
#print axioms kernelEmbedding_injectivePositive
#print axioms kernelEmbedding_injectiveNegative
#print axioms kernelEmbedding_injectiveEvidence
#print axioms kernelEmbedding_injectiveRegistration

noncomputable def kernel_coordinatesRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_coordinates)
    (type_of% (realize sourceVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_coordinates
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_coordinatesArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_coordinatesEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨kernel_coordinatesArena⟩,
  objectArena := .source ⟨kernel_coordinatesArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source kernel_coordinatesArena ⟨kernel_coordinatesEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize sourceVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur, definition := none,
    coordinates := #[0, 1, 2, 3, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "fn"],
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_coordinates
#print axioms kernel_coordinatesPositive
#print axioms kernel_coordinatesNegative
#print axioms kernel_coordinatesEvidence
#print axioms kernel_coordinatesRegistration

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur
