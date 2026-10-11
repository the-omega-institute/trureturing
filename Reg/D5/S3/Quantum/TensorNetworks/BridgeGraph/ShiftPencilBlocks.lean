import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Reg.Support.BridgeGraphRelations
import Reg.Support.BridgeGraphOriginalLaws
import Reg.Support.BridgeGraphEqualityFamilies

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open Reg.Support.BridgeGraphRelations
open LeanInformationAudit
open Matrix Module Finset
open scoped BigOperators
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
universe u_1 u_2 u_3

@[reducible] def pencil_rank_of_leArena : Arena where
  signature := natSignature
  Law R := ∀ (x y : ℕ) (hxy : x ≤ y),
    R.readout () () ((pencil x y).rank) (x * (y + 1))
theorem pencil_rank_of_lePositive : pencil_rank_of_leArena.Law eqActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_rank_of_le
theorem pencil_rank_of_leNegative : ¬ pencil_rank_of_leArena.Law natRejected := by
  intro h
  exact h 0 0 (by omega)

def pencil_rank_of_leEvidence : Registration pencil_rank_of_leArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_rank_of_le)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨pencil_rank_of_lePositive, natRejected, pencil_rank_of_leNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, pencil_rank_of_leNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def pencil_rank_of_leRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_rank_of_le)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_rank_of_le
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_rank_of_leArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_rank_of_leEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨pencil_rank_of_leArena⟩, objectArena := .source ⟨pencil_rank_of_leArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source pencil_rank_of_leArena ⟨pencil_rank_of_leEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_rank_of_le
#print axioms pencil_rank_of_lePositive
#print axioms pencil_rank_of_leNegative
#print axioms pencil_rank_of_leEvidence
#print axioms pencil_rank_of_leRegistration

@[reducible] def pencil_mulVecArena : Arena where
  signature := rationalSignature
  Law R := ∀ (x y : ℕ) (u : Fin (x + 1) × Fin y → ℚ)
    (r : Fin x × Fin (y + 1)),
    R.readout () () ((pencil x y).mulVec u r) (rectExtend u r.1.val r.2.val +
      if 0 < r.2.val then rectExtend u (r.1.val + 1) (r.2.val - 1) else 0)
theorem pencil_mulVecPositive : pencil_mulVecArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_mulVec
theorem pencil_mulVecNegative : ¬ pencil_mulVecArena.Law rationalRejected := by
  intro h
  exact h 1 0 (fun _ => 0) (0,0)

def pencil_mulVecEvidence : Registration pencil_mulVecArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_mulVec)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨pencil_mulVecPositive, rationalRejected, pencil_mulVecNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, pencil_mulVecNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def pencil_mulVecRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_mulVec)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_mulVec
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_mulVecArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_mulVecEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨pencil_mulVecArena⟩, objectArena := .source ⟨pencil_mulVecArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source pencil_mulVecArena ⟨pencil_mulVecEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.pencil_mulVec
#print axioms pencil_mulVecPositive
#print axioms pencil_mulVecNegative
#print axioms pencil_mulVecEvidence
#print axioms pencil_mulVecRegistration

@[reducible] def block_mulVecArena : Arena where
  signature := rationalSignature
  Law R := ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    {m : ι → Type u_2} {n : ι → Type u_3}
    [∀ i, Fintype (m i)] [∀ i, Fintype (n i)]
    (A : ∀ i, Matrix (m i) (n i) ℚ)
    (z : (Σ i, n i) → ℚ) (i : ι) (j : m i),
    R.readout () () ((blockDiagonal' A).mulVec z ⟨i, j⟩)
      ((A i).mulVec (fun k => z ⟨i, k⟩) j)
theorem block_mulVecPositive : block_mulVecArena.{u_1,u_2,u_3}.Law rationalActual :=
  @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.block_mulVec.{u_1,u_2,u_3}
theorem block_mulVecNegative :
    ¬ block_mulVecArena.{u_1,u_2,u_3}.Law rationalRejected := by
  intro h
  exact h (ι := ULift.{u_1} Unit) (m := fun _ => ULift.{u_2} Unit)
    (n := fun _ => ULift.{u_3} Unit)
    (fun _ => 0) (fun _ => 0) ⟨()⟩ ⟨()⟩

def block_mulVecEvidence :
    Registration block_mulVecArena.{u_1,u_2,u_3}
      (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.block_mulVec.{u_1,u_2,u_3})) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨block_mulVecPositive, rationalRejected, block_mulVecNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, block_mulVecNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def block_mulVecRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.block_mulVec.{u_1,u_2,u_3})
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.block_mulVec
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.block_mulVecArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.block_mulVecEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨block_mulVecArena.{u_1,u_2,u_3}⟩,
  objectArena := .source ⟨block_mulVecArena.{u_1,u_2,u_3}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source block_mulVecArena.{u_1,u_2,u_3} ⟨block_mulVecEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.block_mulVec
#print axioms block_mulVecPositive
#print axioms block_mulVecNegative
#print axioms block_mulVecEvidence
#print axioms block_mulVecRegistration

@[reducible] def rows_cardArena : Arena where
  signature := natSignature
  Law R := ∀ (p alpha beta : ℕ),
    R.readout () () (Fintype.card ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t)))) (leftDim p alpha beta)
theorem rows_cardPositive : rows_cardArena.Law eqActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.rows_card
theorem rows_cardNegative : ¬ rows_cardArena.Law natRejected := by
  intro h
  exact h 0 0 0

def rows_cardEvidence : Registration rows_cardArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.rows_card)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨rows_cardPositive, natRejected, rows_cardNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rows_cardNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def rows_cardRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.rows_card)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.rows_card
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.rows_cardArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.rows_cardEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨rows_cardArena⟩, objectArena := .source ⟨rows_cardArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source rows_cardArena ⟨rows_cardEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.rows_card
#print axioms rows_cardPositive
#print axioms rows_cardNegative
#print axioms rows_cardEvidence
#print axioms rows_cardRegistration

@[reducible] def cols_cardArena : Arena where
  signature := natSignature
  Law R := ∀ (p alpha beta : ℕ),
    R.readout () () (Fintype.card ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)))) (rightDim p alpha beta)
theorem cols_cardPositive : cols_cardArena.Law eqActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.cols_card
theorem cols_cardNegative : ¬ cols_cardArena.Law natRejected := by
  intro h
  exact h 0 0 0

def cols_cardEvidence : Registration cols_cardArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.cols_card)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨cols_cardPositive, natRejected, cols_cardNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cols_cardNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def cols_cardRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.cols_card)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.cols_card
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.cols_cardArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.cols_cardEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨cols_cardArena⟩, objectArena := .source ⟨cols_cardArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source cols_cardArena ⟨cols_cardEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.cols_card
#print axioms cols_cardPositive
#print axioms cols_cardNegative
#print axioms cols_cardEvidence
#print axioms cols_cardRegistration

@[reducible] def same_depth_kernel_dimensionArena : Arena where
  signature := natSignature
  Law R := ∀ (p alpha beta gamma delta : ℕ),
    R.readout () () (finrank ℚ (LinearMap.ker (widthTwoMatrix p p alpha beta gamma delta).mulVecLin)) (alpha * delta)
theorem same_depth_kernel_dimensionPositive : same_depth_kernel_dimensionArena.Law eqActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.same_depth_kernel_dimension
theorem same_depth_kernel_dimensionNegative : ¬ same_depth_kernel_dimensionArena.Law natRejected := by
  intro h
  exact h 0 0 0 0 0

def same_depth_kernel_dimensionEvidence : Registration same_depth_kernel_dimensionArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.same_depth_kernel_dimension)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨same_depth_kernel_dimensionPositive, natRejected, same_depth_kernel_dimensionNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, same_depth_kernel_dimensionNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def same_depth_kernel_dimensionRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.same_depth_kernel_dimension)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.same_depth_kernel_dimension
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.same_depth_kernel_dimensionArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.same_depth_kernel_dimensionEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨same_depth_kernel_dimensionArena⟩, objectArena := .source ⟨same_depth_kernel_dimensionArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source same_depth_kernel_dimensionArena ⟨same_depth_kernel_dimensionEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[], readouts := #[{
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.same_depth_kernel_dimension
#print axioms same_depth_kernel_dimensionPositive
#print axioms same_depth_kernel_dimensionNegative
#print axioms same_depth_kernel_dimensionEvidence
#print axioms same_depth_kernel_dimensionRegistration

@[reducible] def double_fin_pickArena : Arena where
  signature := rationalSignature
  Law R := ∀ (n m r s : ℕ) (a b : ℚ) (u : Fin n × Fin m → ℚ),
    R.readout () () (∑ i : Fin n, ∑ j : Fin m,
      (if i.val = r then a else 0) * (if j.val = s then b else 0) * u (i, j))
      (a * b * rectExtend u r s)
theorem double_fin_pickPositive : double_fin_pickArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.double_fin_pick
theorem double_fin_pickNegative : ¬ double_fin_pickArena.Law rationalRejected := by
  intro h
  exact h 0 0 0 0 0 0 (fun _ => 0)

def double_fin_pickEvidence : Registration double_fin_pickArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.double_fin_pick)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨double_fin_pickPositive, rationalRejected, double_fin_pickNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, double_fin_pickNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def double_fin_pickRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.double_fin_pick)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.double_fin_pick
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.double_fin_pickArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.double_fin_pickEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨double_fin_pickArena⟩, objectArena := .source ⟨double_fin_pickArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source double_fin_pickArena ⟨double_fin_pickEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[], readouts := #[{
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.double_fin_pick
#print axioms double_fin_pickPositive
#print axioms double_fin_pickNegative
#print axioms double_fin_pickEvidence
#print axioms double_fin_pickRegistration

@[reducible] def neg_one_pow_squareArena : Arena where
  signature := rationalSignature
  Law R := ∀ (n : ℕ),
    R.readout () () (((-1 : ℚ) ^ n) * ((-1 : ℚ) ^ n)) (1)
theorem neg_one_pow_squarePositive : neg_one_pow_squareArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.neg_one_pow_square
theorem neg_one_pow_squareNegative : ¬ neg_one_pow_squareArena.Law rationalRejected := by
  intro h
  exact h 0

def neg_one_pow_squareEvidence : Registration neg_one_pow_squareArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.neg_one_pow_square)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨neg_one_pow_squarePositive, rationalRejected, neg_one_pow_squareNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, neg_one_pow_squareNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def neg_one_pow_squareRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.neg_one_pow_square)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.neg_one_pow_square
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.neg_one_pow_squareArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.neg_one_pow_squareEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨neg_one_pow_squareArena⟩, objectArena := .source ⟨neg_one_pow_squareArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source neg_one_pow_squareArena ⟨neg_one_pow_squareEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.neg_one_pow_square
#print axioms neg_one_pow_squarePositive
#print axioms neg_one_pow_squareNegative
#print axioms neg_one_pow_squareEvidence
#print axioms neg_one_pow_squareRegistration

@[reducible] def short_short_cyclic_schur_rankArena : Arena where
  signature := natSignature
  Law R := ∀ (A B G D p : ℕ) (hB : 0 < B) (hBA : B ≤ A)
    (hD : 0 < D) (hDG : D ≤ G) (hp : 0 < p),
    R.readout () () ((((p : ℚ) + 1) • kronecker (rowSelector A B) ((rowSelector G D).transpose) -
      kronecker (rowSelector A B) (forwardHalf G) * (reservoir A G)⁻¹ *
        kronecker (-backward A) ((rowSelector G D).transpose)).rank) (min (A * D) (B * G))
theorem short_short_cyclic_schur_rankPositive : short_short_cyclic_schur_rankArena.Law eqActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.short_short_cyclic_schur_rank
theorem short_short_cyclic_schur_rankNegative : ¬ short_short_cyclic_schur_rankArena.Law natRejected := by
  intro h
  exact h 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def short_short_cyclic_schur_rankEvidence : Registration short_short_cyclic_schur_rankArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.short_short_cyclic_schur_rank)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨short_short_cyclic_schur_rankPositive, natRejected, short_short_cyclic_schur_rankNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, short_short_cyclic_schur_rankNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def short_short_cyclic_schur_rankRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.short_short_cyclic_schur_rank)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.short_short_cyclic_schur_rank
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.short_short_cyclic_schur_rankArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.short_short_cyclic_schur_rankEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨short_short_cyclic_schur_rankArena⟩, objectArena := .source ⟨short_short_cyclic_schur_rankArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source short_short_cyclic_schur_rankArena ⟨short_short_cyclic_schur_rankEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.short_short_cyclic_schur_rank
#print axioms short_short_cyclic_schur_rankPositive
#print axioms short_short_cyclic_schur_rankNegative
#print axioms short_short_cyclic_schur_rankEvidence
#print axioms short_short_cyclic_schur_rankRegistration

@[reducible] def long_long_cyclic_schur_rankArena : Arena where
  signature := natSignature
  Law R := ∀ (A B G D p : ℕ) (hA : 0 < A) (hAB : A ≤ B)
    (hG : 0 < G) (hGD : G ≤ D) (hp : 0 < p),
    R.readout () () ((((p : ℚ) + 1) • kronecker (rowSelector B A).transpose (rowSelector D G) -
      kronecker (-backward B).transpose (rowSelector D G) *
        (1 + kronecker (-backward B).transpose (forwardHalf D).transpose)⁻¹ *
          kronecker (rowSelector B A).transpose (forwardHalf D).transpose).rank) (min (A * D) (B * G))
theorem long_long_cyclic_schur_rankPositive : long_long_cyclic_schur_rankArena.Law eqActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.long_long_cyclic_schur_rank
theorem long_long_cyclic_schur_rankNegative : ¬ long_long_cyclic_schur_rankArena.Law natRejected := by
  intro h
  exact h 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def long_long_cyclic_schur_rankEvidence : Registration long_long_cyclic_schur_rankArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.long_long_cyclic_schur_rank)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨long_long_cyclic_schur_rankPositive, natRejected, long_long_cyclic_schur_rankNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, long_long_cyclic_schur_rankNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def long_long_cyclic_schur_rankRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.long_long_cyclic_schur_rank)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.long_long_cyclic_schur_rank
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.long_long_cyclic_schur_rankArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.long_long_cyclic_schur_rankEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨long_long_cyclic_schur_rankArena⟩, objectArena := .source ⟨long_long_cyclic_schur_rankArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source long_long_cyclic_schur_rankArena ⟨long_long_cyclic_schur_rankEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.long_long_cyclic_schur_rank
#print axioms long_long_cyclic_schur_rankPositive
#print axioms long_long_cyclic_schur_rankNegative
#print axioms long_long_cyclic_schur_rankEvidence
#print axioms long_long_cyclic_schur_rankRegistration

@[reducible] def different_depth_witnessArena : Arena where
  signature := witnessPredicateSignature
  Law R := ∀ (p q alpha beta gamma delta : ℕ) (hpq : p ≠ q),
    R.readout () () (leftDim p alpha beta) (rightDim p alpha beta) (leftDim q gamma delta) (rightDim q gamma delta)
theorem different_depth_witnessPositive : different_depth_witnessArena.Law witnessPredicateActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.different_depth_witness
theorem different_depth_witnessNegative : ¬ different_depth_witnessArena.Law witnessPredicateRejected := by
  intro h
  exact h 0 1 0 0 0 0 (by omega)

def different_depth_witnessEvidence : Registration different_depth_witnessArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.different_depth_witness)) where
  actual := witnessPredicateActual
  bridge := Iff.rfl
  variation := ⟨different_depth_witnessPositive, witnessPredicateRejected, different_depth_witnessNegative⟩
  sensitivity := ⟨fun i => ⟨witnessPredicateRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, different_depth_witnessNegative⟩,
    fun i => nomatch i⟩
  dependence := witnessPredicateDependence

noncomputable def different_depth_witnessRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.different_depth_witness)
    (type_of% (realize witnessPredicateSignature (fun _ _ a b c d => RationalWitness a b c d) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.different_depth_witness
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.different_depth_witnessArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.different_depth_witnessEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨different_depth_witnessArena⟩, objectArena := .source ⟨different_depth_witnessArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source different_depth_witnessArena ⟨different_depth_witnessEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize witnessPredicateSignature (fun _ _ a b c d => RationalWitness a b c d) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.different_depth_witness
#print axioms different_depth_witnessPositive
#print axioms different_depth_witnessNegative
#print axioms different_depth_witnessEvidence
#print axioms different_depth_witnessRegistration

@[reducible] def zero_defect_witnessArena : Arena where
  signature := witnessPredicateSignature
  Law R := ∀ (p alpha beta gamma delta : ℕ)
    (hzero : alpha * delta = 0 ∨ beta * gamma = 0),
    R.readout () () (leftDim p alpha beta) (rightDim p alpha beta) (leftDim p gamma delta) (rightDim p gamma delta)
theorem zero_defect_witnessPositive : zero_defect_witnessArena.Law witnessPredicateActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.zero_defect_witness
theorem zero_defect_witnessNegative : ¬ zero_defect_witnessArena.Law witnessPredicateRejected := by
  intro h
  exact h 0 0 0 0 0 (Or.inl rfl)

def zero_defect_witnessEvidence : Registration zero_defect_witnessArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.zero_defect_witness)) where
  actual := witnessPredicateActual
  bridge := Iff.rfl
  variation := ⟨zero_defect_witnessPositive, witnessPredicateRejected, zero_defect_witnessNegative⟩
  sensitivity := ⟨fun i => ⟨witnessPredicateRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, zero_defect_witnessNegative⟩,
    fun i => nomatch i⟩
  dependence := witnessPredicateDependence

noncomputable def zero_defect_witnessRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.zero_defect_witness)
    (type_of% (realize witnessPredicateSignature (fun _ _ a b c d => RationalWitness a b c d) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.zero_defect_witness
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.zero_defect_witnessArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.zero_defect_witnessEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨zero_defect_witnessArena⟩, objectArena := .source ⟨zero_defect_witnessArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source zero_defect_witnessArena ⟨zero_defect_witnessEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize witnessPredicateSignature (fun _ _ a b c d => RationalWitness a b c d) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn"],
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

#print axioms D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.zero_defect_witness
#print axioms zero_defect_witnessPositive
#print axioms zero_defect_witnessNegative
#print axioms zero_defect_witnessEvidence
#print axioms zero_defect_witnessRegistration

open Reg.Support.BridgeGraphEqualityFamilies

noncomputable def antiDiagonal_kernelRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.antiDiagonal_kernel)
    (type_of% (realize antiDiagonalVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.antiDiagonal_kernel
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.antiDiagonal_kernelArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.antiDiagonal_kernelEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨antiDiagonal_kernelArena⟩, objectArena := .source ⟨antiDiagonal_kernelArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source antiDiagonal_kernelArena ⟨antiDiagonal_kernelEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize antiDiagonalVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "fn", "fn"],
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.antiDiagonal_kernel
#print axioms antiDiagonal_kernelPositive
#print axioms antiDiagonal_kernelNegative
#print axioms antiDiagonal_kernelEvidence
#print axioms antiDiagonal_kernelRegistration

noncomputable def widthTwo_block_decompositionRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.widthTwo_block_decomposition)
    (type_of% (realize widthTwoMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.widthTwo_block_decomposition
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.widthTwo_block_decompositionArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.widthTwo_block_decompositionEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨widthTwo_block_decompositionArena⟩, objectArena := .source ⟨widthTwo_block_decompositionArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source widthTwo_block_decompositionArena ⟨widthTwo_block_decompositionEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize widthTwoMatrixEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[0, 1, 2, 3, 4, 5], readouts := #[{
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.widthTwo_block_decomposition
#print axioms widthTwo_block_decompositionPositive
#print axioms widthTwo_block_decompositionNegative
#print axioms widthTwo_block_decompositionEvidence
#print axioms widthTwo_block_decompositionRegistration

open Reg.Support.BridgeGraphOriginalLaws
universe u_4

noncomputable def witness_of_typed_slicesRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.witness_of_typed_slices.{u_1,u_2,u_3,u_4})
    (type_of% (realize witnessPredicateSignature (fun _ _ a b c d => RationalWitness a b c d) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.witness_of_typed_slices
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.witness_of_typed_slicesArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.witness_of_typed_slicesEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨witness_of_typed_slicesArena.{u_1,u_2,u_3,u_4}⟩,
  objectArena := .source ⟨witness_of_typed_slicesArena.{u_1,u_2,u_3,u_4}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source witness_of_typed_slicesArena.{u_1,u_2,u_3,u_4} ⟨witness_of_typed_slicesEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize witnessPredicateSignature (fun _ _ a b c d => RationalWitness a b c d) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn"],
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.witness_of_typed_slices
#print axioms witness_of_typed_slicesPositive
#print axioms witness_of_typed_slicesNegative
#print axioms witness_of_typed_slicesEvidence
#print axioms witness_of_typed_slicesRegistration

noncomputable def matrix_injective_of_rankRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.matrix_injective_of_rank.{u_1,u_2})
    (type_of% (realize vectorFunctionSignature.{u_1,u_2} (fun _ _ f => @Decidable.decide (Function.Injective f)
      (Classical.propDecidable (Function.Injective f))) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.matrix_injective_of_rank
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.matrix_injective_of_rankArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.matrix_injective_of_rankEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨matrix_injective_of_rankArena.{u_1,u_2}⟩,
  objectArena := .source ⟨matrix_injective_of_rankArena.{u_1,u_2}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source matrix_injective_of_rankArena.{u_1,u_2} ⟨matrix_injective_of_rankEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize vectorFunctionSignature.{u_1,u_2} (fun _ _ f => @Decidable.decide (Function.Injective f)
      (Classical.propDecidable (Function.Injective f))) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body"],
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.matrix_injective_of_rank
#print axioms matrix_injective_of_rankPositive
#print axioms matrix_injective_of_rankNegative
#print axioms matrix_injective_of_rankEvidence
#print axioms matrix_injective_of_rankRegistration

noncomputable def schur_two_equationsRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.schur_two_equations.{u_1,u_2,u_3})
    (type_of% (realize typedVectorEqualitySignature.{u_1} (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.schur_two_equations
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.schur_two_equationsArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.schur_two_equationsEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨schur_two_equationsArena.{u_1,u_2,u_3}⟩,
  objectArena := .source ⟨schur_two_equationsArena.{u_1,u_2,u_3}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source schur_two_equationsArena.{u_1,u_2,u_3} ⟨schur_two_equationsEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize typedVectorEqualitySignature.{u_1} (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"],
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

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.schur_two_equations
#print axioms schur_two_equationsPositive
#print axioms schur_two_equationsNegative
#print axioms schur_two_equationsEvidence
#print axioms schur_two_equationsRegistration

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
