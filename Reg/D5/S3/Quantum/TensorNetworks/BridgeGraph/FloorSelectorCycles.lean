import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Reg.Support.BridgeGraphRelations

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open Reg.Support.BridgeGraphRelations
open LeanInformationAudit
open Matrix Module Finset
open scoped BigOperators
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles

@[reducible] def monodromy_forces_zeroArena : Arena where
  signature := rationalSignature
  Law R := ∀ (μ z : ℚ) (hμ : μ < 1) (hfix : z = μ * z),
    R.readout () () (z) (0)
theorem monodromy_forces_zeroPositive : monodromy_forces_zeroArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.monodromy_forces_zero
theorem monodromy_forces_zeroNegative : ¬ monodromy_forces_zeroArena.Law rationalRejected := by
  intro h
  exact h 0 0 (by norm_num) (by norm_num)

def monodromy_forces_zeroEvidence : Registration monodromy_forces_zeroArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.monodromy_forces_zero)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨monodromy_forces_zeroPositive, rationalRejected, monodromy_forces_zeroNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, monodromy_forces_zeroNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def monodromy_forces_zeroRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.monodromy_forces_zero)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.monodromy_forces_zero
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.monodromy_forces_zeroArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.monodromy_forces_zeroEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨monodromy_forces_zeroArena⟩, objectArena := .source ⟨monodromy_forces_zeroArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source monodromy_forces_zeroArena ⟨monodromy_forces_zeroEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def recurrence_product_boundedArena : Arena where
  signature := rationalSignature
  Law R := ∀ (z f : ℕ → ℚ) (L : ℕ)
    (h : ∀ n < L, z (n + 1) = f n * z n),
    R.readout () () (z L) ((∏ t ∈ range L, f t) * z 0)
theorem recurrence_product_boundedPositive : recurrence_product_boundedArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.recurrence_product_bounded
theorem recurrence_product_boundedNegative : ¬ recurrence_product_boundedArena.Law rationalRejected := by
  intro h
  exact h (fun _ => 0) (fun _ => 0) 0 (by intro n hn; omega)

def recurrence_product_boundedEvidence : Registration recurrence_product_boundedArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.recurrence_product_bounded)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨recurrence_product_boundedPositive, rationalRejected, recurrence_product_boundedNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, recurrence_product_boundedNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def recurrence_product_boundedRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.recurrence_product_bounded)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.recurrence_product_bounded
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.recurrence_product_boundedArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.recurrence_product_boundedEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨recurrence_product_boundedArena⟩, objectArena := .source ⟨recurrence_product_boundedArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source recurrence_product_boundedArena ⟨recurrence_product_boundedEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def balanced_cycle_zeroArena : Arena where
  signature := rationalSignature
  Law R := ∀ (i o : ℤ → ℤ) (z c : ℤ → ℚ)
    (hi : ∀ n, i n = 0 ∨ i n = 1) (ho : ∀ n, o n = 0 ∨ o n = 1)
    (hp : ∀ n, i n = o n → z n = c n * z (n - 1))
    (hc : ∀ n, c n ≠ 0)
    (hk : ∀ n, i n = 0 → o n = 1 → z n = 0 ∧ z (n - 1) = 0)
    (hbal : ∀ a : ℤ, ∀ len : ℕ,
      (∑ t ∈ range len, (i (a + t) - o (a + t))) ≤ 1)
    (L : ℕ) (hL : 0 < L) (hperiod : ∀ n, z (n + L) = z n)
    (hwhole : ∀ a : ℤ, (∑ t ∈ range L, (i (a + t) - o (a + t))) ≤ 0)
    (hproduct : ∀ a : ℤ, (∏ t ∈ range L, c (a + t + 1)) < 1),
    ∀ a, R.readout () () (z a) (0)
theorem balanced_cycle_zeroPositive : balanced_cycle_zeroArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.balanced_cycle_zero
theorem balanced_cycle_zeroNegative : ¬ balanced_cycle_zeroArena.Law rationalRejected := by
  intro h
  exact h (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => (1/2 : ℚ))
    (by intro n; exact Or.inl rfl) (by intro n; exact Or.inl rfl)
    (by intro n hn; norm_num) (by intro n; norm_num)
    (by intro n hi ho; norm_num) (by intro a len; simp)
    1 (by norm_num) (by intro n; rfl) (by intro a; simp)
    (by intro a; norm_num) 0

def balanced_cycle_zeroEvidence : Registration balanced_cycle_zeroArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.balanced_cycle_zero)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨balanced_cycle_zeroPositive, rationalRejected, balanced_cycle_zeroNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, balanced_cycle_zeroNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def balanced_cycle_zeroRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.balanced_cycle_zero)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.balanced_cycle_zero
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.balanced_cycle_zeroArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.balanced_cycle_zeroEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨balanced_cycle_zeroArena⟩, objectArena := .source ⟨balanced_cycle_zeroArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source balanced_cycle_zeroArena ⟨balanced_cycle_zeroEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
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


@[reducible] def backward_applyArena : Arena where
  signature := rationalSignature
  Law R := ∀ (A : ℕ) (i j : Fin A),
    R.readout () () (backward A i j) (if j.val = (i.val + 1) % A then 1 else 0)
theorem backward_applyPositive : backward_applyArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.backward_apply
theorem backward_applyNegative : ¬ backward_applyArena.Law rationalRejected := by
  intro h
  exact h 1 0 0

def backward_applyEvidence : Registration backward_applyArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.backward_apply)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨backward_applyPositive, rationalRejected, backward_applyNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, backward_applyNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def backward_applyRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.backward_apply)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.backward_apply
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.backward_applyArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.backward_applyEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨backward_applyArena⟩, objectArena := .source ⟨backward_applyArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source backward_applyArena ⟨backward_applyEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def forwardHalf_applyArena : Arena where
  signature := rationalSignature
  Law R := ∀ (G : ℕ) (i j : Fin G),
    R.readout () () (forwardHalf G i j) (if j.val = (i.val + G - 1) % G then
      (if i.val = 0 then 1 / 2 else 1) else 0)
theorem forwardHalf_applyPositive : forwardHalf_applyArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.forwardHalf_apply
theorem forwardHalf_applyNegative : ¬ forwardHalf_applyArena.Law rationalRejected := by
  intro h
  exact h 1 0 0

def forwardHalf_applyEvidence : Registration forwardHalf_applyArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.forwardHalf_apply)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨forwardHalf_applyPositive, rationalRejected, forwardHalf_applyNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, forwardHalf_applyNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def forwardHalf_applyRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.forwardHalf_apply)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.forwardHalf_apply
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.forwardHalf_applyArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.forwardHalf_applyEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨forwardHalf_applyArena⟩, objectArena := .source ⟨forwardHalf_applyArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source forwardHalf_applyArena ⟨forwardHalf_applyEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def index_val_intArena : Arena where
  signature := integerSignature
  Law R := ∀ (N : ℕ) (hN : 0 < N) (s : ℤ),
    R.readout () () (((index N hN s).val : ℤ)) (s % N)
theorem index_val_intPositive : index_val_intArena.Law integerActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_val_int
theorem index_val_intNegative : ¬ index_val_intArena.Law integerRejected := by
  intro h
  exact h 1 (by norm_num) 0

def index_val_intEvidence : Registration index_val_intArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_val_int)) where
  actual := integerActual
  bridge := Iff.rfl
  variation := ⟨index_val_intPositive, integerRejected, index_val_intNegative⟩
  sensitivity := ⟨fun i => ⟨integerRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, index_val_intNegative⟩,
    fun i => nomatch i⟩
  dependence := integerDependence

noncomputable def index_val_intRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_val_int)
    (type_of% (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_val_int
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_val_intArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_val_intEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨index_val_intArena⟩, objectArena := .source ⟨index_val_intArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source index_val_intArena ⟨index_val_intEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def index_add_oneArena : Arena where
  signature := natSignature
  Law R := ∀ (N : ℕ) (hN : 0 < N) (s : ℤ),
    R.readout () () ((index N hN (s + 1)).val) (((index N hN s).val + 1) % N)
theorem index_add_onePositive : index_add_oneArena.Law eqActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_add_one
theorem index_add_oneNegative : ¬ index_add_oneArena.Law natRejected := by
  intro h
  exact h 1 (by norm_num) 0

def index_add_oneEvidence : Registration index_add_oneArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_add_one)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨index_add_onePositive, natRejected, index_add_oneNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, index_add_oneNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def index_add_oneRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_add_one)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_add_one
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_add_oneArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_add_oneEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨index_add_oneArena⟩, objectArena := .source ⟨index_add_oneArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source index_add_oneArena ⟨index_add_oneEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def index_sub_oneArena : Arena where
  signature := natSignature
  Law R := ∀ (N : ℕ) (hN : 0 < N) (s : ℤ),
    R.readout () () ((index N hN (s - 1)).val) (((index N hN s).val + N - 1) % N)
theorem index_sub_onePositive : index_sub_oneArena.Law eqActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_sub_one
theorem index_sub_oneNegative : ¬ index_sub_oneArena.Law natRejected := by
  intro h
  exact h 1 (by norm_num) 0

def index_sub_oneEvidence : Registration index_sub_oneArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_sub_one)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨index_sub_onePositive, natRejected, index_sub_oneNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, index_sub_oneNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def index_sub_oneRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_sub_one)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_sub_one
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_sub_oneArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_sub_oneEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨index_sub_oneArena⟩, objectArena := .source ⟨index_sub_oneArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source index_sub_oneArena ⟨index_sub_oneEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def tensor_mulVec_orbitArena : Arena where
  signature := rationalSignature
  Law R := ∀ (A G : ℕ) (hA : 0 < A) (hG : 0 < G)
    (z : Fin A × Fin G → ℚ) (a b s : ℤ),
    R.readout () () ((kronecker (backward A) (forwardHalf G)).mulVec z (orbit A G hA hG a b s)) (edge G hG (b + s) * z (orbit A G hA hG a b (s - 1)))
theorem tensor_mulVec_orbitPositive : tensor_mulVec_orbitArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_mulVec_orbit
theorem tensor_mulVec_orbitNegative : ¬ tensor_mulVec_orbitArena.Law rationalRejected := by
  intro h
  exact h 1 1 (by norm_num) (by norm_num) (fun _ => 0) 0 0 0

def tensor_mulVec_orbitEvidence : Registration tensor_mulVec_orbitArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_mulVec_orbit)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨tensor_mulVec_orbitPositive, rationalRejected, tensor_mulVec_orbitNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, tensor_mulVec_orbitNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def tensor_mulVec_orbitRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_mulVec_orbit)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_mulVec_orbit
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_mulVec_orbitArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_mulVec_orbitEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨tensor_mulVec_orbitArena⟩, objectArena := .source ⟨tensor_mulVec_orbitArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source tensor_mulVec_orbitArena ⟨tensor_mulVec_orbitEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def whole_tensor_excessArena : Arena where
  signature := integerSignature
  Law R := ∀ (A B G D : ℕ) (hA : 0 < A) (hG : 0 < G)
    (phaseI phaseO : ℤ),
    R.readout () () ((∑ t ∈ range (A * G), (jump ((D : ℚ) / G) (phaseI + t) -
      jump ((B : ℚ) / A) (phaseO - t)))) ((A * D : ℕ) - (G * B : ℕ))
theorem whole_tensor_excessPositive : whole_tensor_excessArena.Law integerActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.whole_tensor_excess
theorem whole_tensor_excessNegative : ¬ whole_tensor_excessArena.Law integerRejected := by
  intro h
  exact h 1 0 1 0 (by norm_num) (by norm_num) 0 0

def whole_tensor_excessEvidence : Registration whole_tensor_excessArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.whole_tensor_excess)) where
  actual := integerActual
  bridge := Iff.rfl
  variation := ⟨whole_tensor_excessPositive, integerRejected, whole_tensor_excessNegative⟩
  sensitivity := ⟨fun i => ⟨integerRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, whole_tensor_excessNegative⟩,
    fun i => nomatch i⟩
  dependence := integerDependence

noncomputable def whole_tensor_excessRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.whole_tensor_excess)
    (type_of% (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.whole_tensor_excess
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.whole_tensor_excessArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.whole_tensor_excessEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨whole_tensor_excessArena⟩, objectArena := .source ⟨whole_tensor_excessArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source whole_tensor_excessArena ⟨whole_tensor_excessEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def jump_indexArena : Arena where
  signature := integerSignature
  Law R := ∀ (A B : ℕ) (hA : 0 < A) (s : ℤ),
    R.readout () () (jump ((B : ℚ) / A) (index A hA s).val) (jump ((B : ℚ) / A) s)
theorem jump_indexPositive : jump_indexArena.Law integerActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_index
theorem jump_indexNegative : ¬ jump_indexArena.Law integerRejected := by
  intro h
  exact h 1 0 (by norm_num) 0

def jump_indexEvidence : Registration jump_indexArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_index)) where
  actual := integerActual
  bridge := Iff.rfl
  variation := ⟨jump_indexPositive, integerRejected, jump_indexNegative⟩
  sensitivity := ⟨fun i => ⟨integerRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, jump_indexNegative⟩,
    fun i => nomatch i⟩
  dependence := integerDependence

noncomputable def jump_indexRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_index)
    (type_of% (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_index
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_indexArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_indexEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨jump_indexArena⟩, objectArena := .source ⟨jump_indexArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source jump_indexArena ⟨jump_indexEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def edge_productArena : Arena where
  signature := rationalSignature
  Law R := ∀ (G M : ℕ) (hG : 0 < G) (phase : ℤ),
    R.readout () () ((∏ t ∈ range (M * G), edge G hG (phase + t))) ((1 / 2 : ℚ) ^ M)
theorem edge_productPositive : edge_productArena.Law rationalActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_product
theorem edge_productNegative : ¬ edge_productArena.Law rationalRejected := by
  intro h
  exact h 1 0 (by norm_num) 0

def edge_productEvidence : Registration edge_productArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_product)) where
  actual := rationalActual
  bridge := Iff.rfl
  variation := ⟨edge_productPositive, rationalRejected, edge_productNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, edge_productNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalDependence

noncomputable def edge_productRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_product)
    (type_of% (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_product
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_productArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_productEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨edge_productArena⟩, objectArena := .source ⟨edge_productArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source edge_productArena ⟨edge_productEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def jump_zero_or_oneArena : Arena where
  signature := integerSignature
  Law R := ∀ {ρ : ℚ} (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (n : ℤ), R.readout () () (jump ρ n) 0 ∨ jump ρ n = 1
theorem jump_zero_or_onePositive : jump_zero_or_oneArena.Law integerActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_zero_or_one
theorem jump_zero_or_oneNegative : ¬ jump_zero_or_oneArena.Law integerRejected := by
  intro h
  rcases h (ρ := 0) (by norm_num) (by norm_num) 0 with hf | hf
  · exact hf
  · norm_num [jump] at hf

def jump_zero_or_oneEvidence : Registration jump_zero_or_oneArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_zero_or_one)) where
  actual := integerActual
  bridge := Iff.rfl
  variation := ⟨jump_zero_or_onePositive, integerRejected, jump_zero_or_oneNegative⟩
  sensitivity := ⟨fun i => ⟨integerRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, jump_zero_or_oneNegative⟩,
    fun i => nomatch i⟩
  dependence := integerDependence

noncomputable def jump_zero_or_oneRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_zero_or_one)
    (type_of% (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_zero_or_one
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_zero_or_oneArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_zero_or_oneEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨jump_zero_or_oneArena⟩, objectArena := .source ⟨jump_zero_or_oneArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source jump_zero_or_oneArena ⟨jump_zero_or_oneEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn"],
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


@[reducible] def jump_one_iff_fin_selectorArena : Arena where
  signature := integerSignature
  Law R := ∀ (A B : ℕ) (hB : 0 < B) (hBA : B ≤ A) (n : Fin A), R.readout () () (jump ((B : ℚ) / A) n.val) 1 ↔ ∃ k : Fin B, n.val = k.val * A / B
theorem jump_one_iff_fin_selectorPositive : jump_one_iff_fin_selectorArena.Law integerActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_one_iff_fin_selector
theorem jump_one_iff_fin_selectorNegative : ¬ jump_one_iff_fin_selectorArena.Law integerRejected := by
  intro h
  exact (h 1 1 (by norm_num) (by norm_num) 0).mpr ⟨0, by norm_num⟩

def jump_one_iff_fin_selectorEvidence : Registration jump_one_iff_fin_selectorArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_one_iff_fin_selector)) where
  actual := integerActual
  bridge := Iff.rfl
  variation := ⟨jump_one_iff_fin_selectorPositive, integerRejected, jump_one_iff_fin_selectorNegative⟩
  sensitivity := ⟨fun i => ⟨integerRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, jump_one_iff_fin_selectorNegative⟩,
    fun i => nomatch i⟩
  dependence := integerDependence

noncomputable def jump_one_iff_fin_selectorRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_one_iff_fin_selector)
    (type_of% (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_one_iff_fin_selector
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_one_iff_fin_selectorArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.jump_one_iff_fin_selectorEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨jump_one_iff_fin_selectorArena⟩, objectArena := .source ⟨jump_one_iff_fin_selectorArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source jump_one_iff_fin_selectorArena ⟨jump_one_iff_fin_selectorEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize integerSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"],
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


@[reducible] def opposite_direction_excessArena : Arena where
  signature := integerSignature
  Law R := ∀ {ρI ρO : ℚ} (hρ : ρI ≤ ρO) (phaseI phaseO : ℤ) (len : ℕ), R.readout () () (∑ t ∈ range len, (jump ρI (phaseI + t) - jump ρO (phaseO - t))) 1
theorem opposite_direction_excessPositive : opposite_direction_excessArena.Law integerLeActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.opposite_direction_excess
theorem opposite_direction_excessNegative : ¬ opposite_direction_excessArena.Law integerRejected := by
  intro h
  exact h (ρI := 0) (ρO := 0) (by norm_num) 0 0 0

def opposite_direction_excessEvidence : Registration opposite_direction_excessArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.opposite_direction_excess)) where
  actual := integerLeActual
  bridge := Iff.rfl
  variation := ⟨opposite_direction_excessPositive, integerRejected, opposite_direction_excessNegative⟩
  sensitivity := ⟨fun i => ⟨integerRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, opposite_direction_excessNegative⟩,
    fun i => nomatch i⟩
  dependence := integerLeDependence

noncomputable def opposite_direction_excessRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.opposite_direction_excess)
    (type_of% (realize integerSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.opposite_direction_excess
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.opposite_direction_excessArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.opposite_direction_excessEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨opposite_direction_excessArena⟩, objectArena := .source ⟨opposite_direction_excessArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source opposite_direction_excessArena ⟨opposite_direction_excessEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize integerSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def half_pow_lt_oneArena : Arena where
  signature := rationalSignature
  Law R := ∀ {n : ℕ} (hn : 0 < n), R.readout () () ((1 / 2 : ℚ) ^ n) 1
theorem half_pow_lt_onePositive : half_pow_lt_oneArena.Law rationalLtActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.half_pow_lt_one
theorem half_pow_lt_oneNegative : ¬ half_pow_lt_oneArena.Law rationalRejected := by
  intro h
  exact h (n := 1) (by norm_num)

def half_pow_lt_oneEvidence : Registration half_pow_lt_oneArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.half_pow_lt_one)) where
  actual := rationalLtActual
  bridge := Iff.rfl
  variation := ⟨half_pow_lt_onePositive, rationalRejected, half_pow_lt_oneNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, half_pow_lt_oneNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalLtDependence

noncomputable def half_pow_lt_oneRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.half_pow_lt_one)
    (type_of% (realize rationalSignature (fun _ _ a b => a < b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.half_pow_lt_one
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.half_pow_lt_oneArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.half_pow_lt_oneEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨half_pow_lt_oneArena⟩, objectArena := .source ⟨half_pow_lt_oneArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source half_pow_lt_oneArena ⟨half_pow_lt_oneEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a < b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "fn", "fn"],
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


@[reducible] def common_node_product_boundArena : Arena where
  signature := rationalSignature
  Law R := ∀ (κ : ℚ) (hκ : 0 < κ) (o : ℤ → ℤ) (w : ℤ → ℚ) (hw : ∀ n, 0 < w n) (a : ℤ) (L : ℕ), R.readout () () (∏ t ∈ range L, (if o (a + t + 1) = 1 then κ / (κ + 1) else 1) * w (a + t + 1)) (∏ t ∈ range L, w (a + t + 1))
theorem common_node_product_boundPositive : common_node_product_boundArena.Law rationalLeActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.common_node_product_bound
theorem common_node_product_boundNegative : ¬ common_node_product_boundArena.Law rationalRejected := by
  intro h
  exact h 1 (by norm_num) (fun _ => 0) (fun _ => 1) (by intro n; norm_num) 0 0

def common_node_product_boundEvidence : Registration common_node_product_boundArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.common_node_product_bound)) where
  actual := rationalLeActual
  bridge := Iff.rfl
  variation := ⟨common_node_product_boundPositive, rationalRejected, common_node_product_boundNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, common_node_product_boundNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalLeDependence

noncomputable def common_node_product_boundRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.common_node_product_bound)
    (type_of% (realize rationalSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.common_node_product_bound
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.common_node_product_boundArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.common_node_product_boundEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨common_node_product_boundArena⟩, objectArena := .source ⟨common_node_product_boundArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source common_node_product_boundArena ⟨common_node_product_boundEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def edge_posArena : Arena where
  signature := rationalSignature
  Law R := ∀ (G : ℕ) (hG : 0 < G) (s : ℤ), R.readout () () 0 (edge G hG s)
theorem edge_posPositive : edge_posArena.Law rationalLtActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_pos
theorem edge_posNegative : ¬ edge_posArena.Law rationalRejected := by
  intro h
  exact h 1 (by norm_num) 0

def edge_posEvidence : Registration edge_posArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_pos)) where
  actual := rationalLtActual
  bridge := Iff.rfl
  variation := ⟨edge_posPositive, rationalRejected, edge_posNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, edge_posNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalLtDependence

noncomputable def edge_posRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_pos)
    (type_of% (realize rationalSignature (fun _ _ a b => a < b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_pos
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_posArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.edge_posEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨edge_posArena⟩, objectArena := .source ⟨edge_posArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source edge_posArena ⟨edge_posEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a < b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


@[reducible] def tensor_edge_product_lt_oneArena : Arena where
  signature := rationalSignature
  Law R := ∀ (A G : ℕ) (hA : 0 < A) (hG : 0 < G) (phase : ℤ), R.readout () () (∏ t ∈ range (A * G), edge G hG (phase + t + 1)) 1
theorem tensor_edge_product_lt_onePositive : tensor_edge_product_lt_oneArena.Law rationalLtActual := @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_edge_product_lt_one
theorem tensor_edge_product_lt_oneNegative : ¬ tensor_edge_product_lt_oneArena.Law rationalRejected := by
  intro h
  exact h 1 1 (by norm_num) (by norm_num) 0

def tensor_edge_product_lt_oneEvidence : Registration tensor_edge_product_lt_oneArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_edge_product_lt_one)) where
  actual := rationalLtActual
  bridge := Iff.rfl
  variation := ⟨tensor_edge_product_lt_onePositive, rationalRejected, tensor_edge_product_lt_oneNegative⟩
  sensitivity := ⟨fun i => ⟨rationalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, tensor_edge_product_lt_oneNegative⟩,
    fun i => nomatch i⟩
  dependence := rationalLtDependence

noncomputable def tensor_edge_product_lt_oneRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_edge_product_lt_one)
    (type_of% (realize rationalSignature (fun _ _ a b => a < b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_edge_product_lt_one
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_edge_product_lt_oneArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.tensor_edge_product_lt_oneEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨tensor_edge_product_lt_oneArena⟩, objectArena := .source ⟨tensor_edge_product_lt_oneArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source tensor_edge_product_lt_oneArena ⟨tensor_edge_product_lt_oneEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rationalSignature (fun _ _ a b => a < b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles, definition := none,
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


end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
