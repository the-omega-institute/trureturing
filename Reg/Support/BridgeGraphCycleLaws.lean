import D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.BridgeGraphRelations

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open Reg.Support.BridgeGraphRelations
open LeanInformationAudit
open Matrix Module Finset
open scoped BigOperators

noncomputable section

/- Cycle Laws and their consumed evidence retain the names used by the source mirror. -/
namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles

abbrev finEqualitySignature : Signature where
  Params := ℕ
  State N := Fin N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ N := Fin N → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def finEqualityActual : Realization finEqualitySignature :=
  realize finEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)

def finEqualityRejected : Realization finEqualitySignature :=
  realize finEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem finEqualityDependence : ObservationalDependence finEqualitySignature finEqualityActual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  intro h
  have he := congrFun h (0 : Fin 2)
  change ((0 : Fin 2) = 0) = ((1 : Fin 2) = 0) at he
  have hn : (1 : Fin 2) = 0 := he ▸ rfl
  exact (by decide : ¬ ((1 : Fin 2) = 0)) hn

abbrev orbitEqualitySignature : Signature where
  Params := Σ A : ℕ, ℕ
  State p := Fin p.1 × Fin p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Fin p.1 × Fin p.2) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def orbitEqualityActual : Realization orbitEqualitySignature :=
  realize orbitEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)

def orbitEqualityRejected : Realization orbitEqualitySignature :=
  realize orbitEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem orbitEqualityDependence : ObservationalDependence orbitEqualitySignature orbitEqualityActual := by
  intro i
  refine ⟨⟨2, 1⟩, (0, 0), (1, 0), ?_⟩
  intro h
  have he := congrFun h (0, 0)
  change (((0, 0) : Fin 2 × Fin 1) = (0, 0)) = (((1, 0) : Fin 2 × Fin 1) = (0, 0)) at he
  have hn : ((1, 0) : Fin 2 × Fin 1) = (0, 0) := he ▸ rfl
  exact (by decide : ¬ (((1, 0) : Fin 2 × Fin 1) = (0, 0))) hn

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

@[reducible] def index_natArena : Arena where
  signature := finEqualitySignature
  Law R := ∀ (N : ℕ) (hN : 0 < N) (i : Fin N),
    R.readout () N (index N hN (i.val : ℤ)) i
theorem index_natPositive : index_natArena.Law finEqualityActual :=
  @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_nat
theorem index_natNegative : ¬ index_natArena.Law finEqualityRejected := by
  intro h
  exact h 1 (by norm_num) 0

def index_natEvidence : Registration index_natArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_nat)) where
  actual := finEqualityActual
  bridge := Iff.rfl
  variation := ⟨index_natPositive, finEqualityRejected, index_natNegative⟩
  sensitivity := ⟨fun i => ⟨finEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, index_natNegative⟩,
    fun i => nomatch i⟩
  dependence := finEqualityDependence

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

@[reducible] def index_add_multipleArena : Arena where
  signature := finEqualitySignature
  Law R := ∀ (N : ℕ) (hN : 0 < N) (s k : ℤ),
    R.readout () N (index N hN (s + k * N)) (index N hN s)
theorem index_add_multiplePositive : index_add_multipleArena.Law finEqualityActual :=
  @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_add_multiple
theorem index_add_multipleNegative : ¬ index_add_multipleArena.Law finEqualityRejected := by
  intro h
  exact h 1 (by norm_num) 0 0

def index_add_multipleEvidence : Registration index_add_multipleArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.index_add_multiple)) where
  actual := finEqualityActual
  bridge := Iff.rfl
  variation := ⟨index_add_multiplePositive, finEqualityRejected, index_add_multipleNegative⟩
  sensitivity := ⟨fun i => ⟨finEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, index_add_multipleNegative⟩,
    fun i => nomatch i⟩
  dependence := finEqualityDependence

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

@[reducible] def orbit_periodArena : Arena where
  signature := orbitEqualitySignature
  Law R := ∀ (A G : ℕ) (hA : 0 < A) (hG : 0 < G) (a b s : ℤ),
    R.readout () ⟨A, G⟩ (orbit A G hA hG a b (s + A * G))
      (orbit A G hA hG a b s)
theorem orbit_periodPositive : orbit_periodArena.Law orbitEqualityActual :=
  @D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.orbit_period
theorem orbit_periodNegative : ¬ orbit_periodArena.Law orbitEqualityRejected := by
  intro h
  exact h 1 1 (by norm_num) (by norm_num) 0 0 0

def orbit_periodEvidence : Registration orbit_periodArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles.orbit_period)) where
  actual := orbitEqualityActual
  bridge := Iff.rfl
  variation := ⟨orbit_periodPositive, orbitEqualityRejected, orbit_periodNegative⟩
  sensitivity := ⟨fun i => ⟨orbitEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, orbit_periodNegative⟩,
    fun i => nomatch i⟩
  dependence := orbitEqualityDependence

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

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
