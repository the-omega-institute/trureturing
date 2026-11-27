import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct
import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Source-bound readouts for the contraction and pairing laws of two circuits. -/

namespace Reg.D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct
open _root_.D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition
open _root_.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)
open Reg.Support.UniverseSingleReadout (signature sensitivity)
open Finset Matroid
open scoped Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

private abbrev LoopVertex := ULift.{u} Bool
private def loopFirst : LoopVertex.{u} := ULift.up false
private def loopSecond : LoopVertex.{u} := ULift.up true
private def loopMatroid : Matroid LoopVertex.{u} := loopyOn Set.univ

private theorem loop_circuit (x : LoopVertex.{u}) :
    loopMatroid.IsCircuit (↑({x} : Finset LoopVertex) : Set LoopVertex) := by
  rw [Finset.coe_singleton]
  exact (loopyOn_isLoop_iff.mpr (Set.mem_univ _)).isCircuit

private theorem loop_pair :
    ({loopFirst} : Finset LoopVertex.{u}) ≠ {loopSecond} ∧
      UnionNullityTwo loopMatroid.{u} {loopFirst} {loopSecond} := by
  constructor
  · decide
  · rw [UnionNullityTwo, loopMatroid, eRk_loopyOn]
    have hc : (({loopFirst} : Finset LoopVertex.{u}) ∪ {loopSecond}).card = 2 := by
      decide
    exact (congrArg (fun n : ℕ => (n : ℕ∞)) hc).symm

private theorem loop_contract_empty_base (K : Finset LoopVertex.{u}) :
    (loopMatroid ／ (K : Set LoopVertex)).IsBase ∅ := by
  have h : loopMatroid.IsBasis (↑(∅ : Finset LoopVertex) : Set LoopVertex) (K : Set LoopVertex) :=
    loopyOn_isBasis_iff.mpr ⟨coe_empty, Set.subset_univ _⟩
  have hb := (contract_base_iff (G := ∅) h (by simp)).mpr (by simp [loopMatroid])
  simpa only [coe_empty] using hb

namespace Residual

abbrev Params := Σ V : Type u, Σ _ : LinearOrder V, Finset V

abbrev sig := signature Params.{u}
  (fun p => Finset p.1) (fun p => Finset p.1)

def actual : Realization sig.{u} :=
  realize sig (fun _ ⟨V, ord, C⟩ D => @SDiff.sdiff (Finset V)
    (letI := ord; inferInstance) D C) (fun e => nomatch e)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig.{u}
  Law r := ∀ {V : Type u} [ord : LinearOrder V] {M : Matroid V} {C D : Finset V},
    M.IsCircuit (C : Set V) → M.IsCircuit (D : Set V) →
    UnionNullityTwo M C D →
    (M ／ (C : Set V)).IsCircuit (↑(r.readout () ⟨V, ord, C⟩ D) : Set V) ∧
      (M ／ (D : Set V)).IsCircuit (↑(C \ D) : Set V)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hc := (h (loop_circuit loopFirst) (loop_circuit loopSecond)
    loop_pair.2).1
  exact (loopMatroid ／ (↑({loopFirst} : Finset LoopVertex) : Set LoopVertex)).empty_not_isCircuit
    (by simpa [rejected, realize] using hc)

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  refine ⟨⟨LoopVertex, inferInstance, ∅⟩, {loopFirst}, ∅, ?_⟩
  simp [actual, realize]

def source_registration : Registration arena.{u} (type_of% (@residual_circuits.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@residual_circuits.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity _ actual rejected rejected_law
  dependence := dependence

end Residual

namespace Pairing

abbrev Params :=
  Σ V : Type u, Σ ord : LinearOrder V, Σ fin : Fintype V, Σ M : Matroid V,
    Σ _ : Finset V, Σ D : Finset V, @topCycles V fin ord (M ／ (D : Set V))

abbrev sig := signature Params.{u} (fun p => Chain p.1) (fun _ => ℤ)

def actual : Realization sig.{u} :=
  realize sig (fun _ ⟨V, ord, fin, _, C, D, v⟩ w =>
    @circuitPairing V ord fin C D w v.val) (fun e => nomatch e)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  let C : Finset LoopVertex.{u} := {loopFirst}
  let z : topCycles (loopMatroid ／ (C : Set LoopVertex)) :=
    ⟨simplex ∅, ⟨fun F hF => by
      have hne : F ≠ ∅ := fun h => hF (h.symm ▸ by simpa using loop_contract_empty_base C)
      simp [simplex, hne], fun R => by simp [boundaryOn, simplex]⟩⟩
  have hpos : 0 < circuitPairing C C z.val z.val := by
    unfold circuitPairing
    apply sum_pos' (fun _ _ => mul_self_nonneg _)
    refine ⟨∅, mem_univ _, ?_⟩
    have hboundary : simplexBoundary C ∅ = 1 := by
      simpa [C, insertionSign] using
        (simplexBoundary_erase (C := C) (x := loopFirst) (by simp [C]))
    simp [signedJoin, shuffleSign, hboundary, z, simplex]
  refine ⟨⟨LoopVertex, inferInstance, inferInstance, loopMatroid, C, C, z⟩, z.val, 0, ?_⟩
  change circuitPairing C C z.val z.val ≠ circuitPairing C C 0 z.val
  simpa [circuitPairing, signedJoin] using hpos.ne'

end Pairing

namespace Zero

abbrev arena : Arena where
  signature := Pairing.sig.{u}
  Law r := ∀ {V : Type u} [ord : LinearOrder V] [fin : Fintype V]
    {M : Matroid V} {C D : Finset V},
    M.IsCircuit (C : Set V) → M.IsCircuit (D : Set V) → C ≠ D →
    ¬ UnionNullityTwo M C D →
    ∀ (w : topCycles (M ／ (C : Set V))) (v : topCycles (M ／ (D : Set V))),
      r.readout () ⟨V, ord, fin, M, C, D, v⟩ w.val = 0

private abbrev Four := ULift.{u} (Fin 4)
private def firstPair : Finset Four.{u} := {ULift.up 0, ULift.up 1}
private def secondPair : Finset Four.{u} := {ULift.up 2, ULift.up 3}

private def rankOneModel : IndepMatroid Four.{u} :=
  IndepMatroid.ofFinset Set.univ (fun I => I.card ≤ 1) (by simp)
    (fun _ _ hJ hIJ => (card_le_card hIJ).trans hJ)
    (by
      intro I J _ hJ hIJ
      have hIc : I.card = 0 := by omega
      have hI := card_eq_zero.mp hIc
      subst I
      obtain ⟨x, hx⟩ := card_pos.mp (by simpa using hIJ)
      exact ⟨x, hx, by simp, by simp⟩
    ) (fun _ _ => Set.subset_univ _)

private theorem model_indep (I : Finset Four.{u}) :
    rankOneModel.matroid.Indep (I : Set Four) ↔ I.card ≤ 1 := by
  rw [IndepMatroid.matroid_indep_iff]
  exact IndepMatroid.ofFinset_indep ..

private theorem model_circuit {I : Finset Four.{u}} (hI : I.card = 2) :
    rankOneModel.matroid.IsCircuit (I : Set Four) := by
  rw [isCircuit_iff_dep_forall_sdiff_singleton_indep, dep_iff, model_indep, hI]
  refine ⟨⟨by decide, Set.subset_univ _⟩, fun x hx => ?_⟩
  rw [← coe_erase, model_indep, card_erase_of_mem hx, hI]

private theorem rejected_law : ¬ arena.{u}.Law Pairing.rejected := by
  intro h
  have hrank : rankOneModel.{u}.matroid.eRk (↑(firstPair ∪ secondPair) : Set Four) ≤ 1 := by
    rw [eRk_le_iff]
    intro I _ hI
    have hf : I.Finite := Set.toFinite I
    rw [← hf.coe_toFinset] at hI
    have hc := (model_indep _).mp hI
    rwa [← hf.cast_ncard_eq, Set.ncard_eq_toFinset_card I hf, Nat.cast_le_one]
  have hnull : ¬ UnionNullityTwo rankOneModel.{u}.matroid firstPair secondPair := by
    intro he
    have hc : (firstPair.{u} ∪ secondPair).card = 4 := by decide
    have hb := add_le_add_left hrank (2 : ℕ∞)
    have he' := he.trans (congrArg (fun n : ℕ => (n : ℕ∞)) hc)
    have himpossible := he'.symm.trans_le hb
    norm_num at himpossible
  have hz := h (model_circuit (I := firstPair) (by decide))
    (model_circuit (I := secondPair) (by decide)) (by decide) hnull 0 0
  exact one_ne_zero hz

def source_registration : Registration arena.{u} (type_of% (@circuitPairing_eq_zero.{u})) where
  actual := Pairing.actual
  bridge := Iff.rfl
  variation := ⟨@circuitPairing_eq_zero.{u}, Pairing.rejected, rejected_law⟩
  sensitivity := sensitivity _ Pairing.actual Pairing.rejected rejected_law
  dependence := Pairing.dependence

end Zero

namespace Factor

abbrev arena : Arena where
  signature := Pairing.sig.{u}
  Law r := ∀ {V : Type u} [ord : LinearOrder V] [fin : Fintype V]
    {M : Matroid V} {C D : Finset V},
    M.IsCircuit (C : Set V) → M.IsCircuit (D : Set V) →
    UnionNullityTwo M C D →
    ∀ (w : topCycles (M ／ (C : Set V))) (v : topCycles (M ／ (D : Set V))),
      r.readout () ⟨V, ord, fin, M, C, D, v⟩ w.val =
        pairSign C D * ∑ T : Finset V,
          aggregateRestriction (M ／ (C : Set V)) (D \ C) w.val T *
            aggregateRestriction (M ／ (D : Set V)) (C \ D) v.val T

private theorem rejected_law : ¬ arena.{u}.Law Pairing.rejected := by
  intro h
  have hC := loop_circuit loopFirst
  have hD := loop_circuit loopSecond
  have he := h hC hD loop_pair.2 0 0
  rw [← circuitPairing_factor hC hD loop_pair.2] at he
  simp [Pairing.rejected, realize, circuitPairing, signedJoin] at he

def source_registration : Registration arena.{u} (type_of% (@circuitPairing_factor.{u})) where
  actual := Pairing.actual
  bridge := Iff.rfl
  variation := ⟨@circuitPairing_factor.{u}, Pairing.rejected, rejected_law⟩
  sensitivity := sensitivity _ Pairing.actual Pairing.rejected rejected_law
  dependence := Pairing.dependence

end Factor

namespace Rank

abbrev Params := Σ V : Type u, Σ _ : LinearOrder V, Fintype V

abbrev sig := signature Params.{u}
  (fun p => Matroid p.1) (fun p => Submodule ℚ (Finset p.1 → ℚ))

def actual : Realization sig.{u} :=
  realize sig (fun _ ⟨V, ord, fin⟩ M => @rationalTopCycles V ord fin M)
    (fun e => nomatch e)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig.{u}
  Law r := ∀ {V : Type u} [ord : LinearOrder V] [fin : Fintype V]
    {M : Matroid V} {C D : Finset V},
    M.IsCircuit (C : Set V) → M.IsCircuit (D : Set V) →
    UnionNullityTwo M C D →
    Module.finrank ℚ (LinearMap.range (rationalCircuitPairing M C D)) =
      Module.finrank ℚ (r.readout () ⟨V, ord, fin⟩ (M ／ (↑(C ∪ D) : Set V)))

private def emptyCoordinate (F : Finset LoopVertex.{u}) : ℚ := if F = ∅ then 1 else 0

private theorem emptyCoordinate_mem {M : Matroid LoopVertex.{u}} (hM : M.IsBase ∅) :
    emptyCoordinate ∈ rationalTopCycles M := by
  refine ⟨fun F hF => ?_, fun R => ?_⟩
  · have hn : F ≠ ∅ := by rintro rfl; exact hF (by simpa using hM)
    simp [emptyCoordinate, hn]
  · simp [emptyCoordinate]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let C : Finset LoopVertex.{u} := {loopFirst}
  let D : Finset LoopVertex.{u} := {loopSecond}
  have hC := loop_circuit loopFirst
  have hD := loop_circuit loopSecond
  have he := h hC hD loop_pair.2
  rw [circuitPairing_rank hC hD loop_pair.2] at he
  have hz : 0 < Module.finrank ℚ (rationalTopCycles (loopMatroid ／ (↑(C ∪ D) : Set LoopVertex))) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨emptyCoordinate, emptyCoordinate_mem (loop_contract_empty_base (C ∪ D))⟩,
        fun hzero => by
          have heval := congrArg (fun z => z.val ∅) hzero
          simp [emptyCoordinate] at heval⟩
  change Module.finrank ℚ (rationalTopCycles (loopMatroid ／ (↑(C ∪ D) : Set LoopVertex))) =
    Module.finrank ℚ (⊥ : Submodule ℚ (Finset LoopVertex → ℚ)) at he
  rw [finrank_bot] at he
  exact hz.ne' he

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  refine ⟨⟨LoopVertex, inferInstance, inferInstance⟩, loopMatroid, freeOn Set.univ, ?_⟩
  intro h
  have hz : emptyCoordinate ∈ rationalTopCycles loopMatroid := emptyCoordinate_mem (by simp [loopMatroid])
  change rationalTopCycles loopMatroid = rationalTopCycles (freeOn Set.univ) at h
  rw [h] at hz
  have hbase : ¬ (freeOn (Set.univ : Set LoopVertex)).IsBase ∅ :=
    fun hb => Set.univ_nonempty.ne_empty (freeOn_isBase_iff.mp hb).symm
  have hz' := hz.1 ∅ (by simpa using hbase)
  simp [emptyCoordinate] at hz'

def source_registration : Registration arena.{u} (type_of% (@circuitPairing_rank.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@circuitPairing_rank.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity _ actual rejected rejected_law
  dependence := dependence

end Rank

def residual_circuits_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@residual_circuits.{u}) (Realization Residual.sig.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct.residual_circuits.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct.Residual.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Residual.arena⟩
  objectArena := .source ⟨Residual.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Residual.arena ⟨Residual.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Residual.sig Residual.actual.readout Residual.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def circuitPairing_eq_zero_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@circuitPairing_eq_zero.{u}) (Realization Pairing.sig.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct.circuitPairing_eq_zero.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct.Zero.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Zero.arena⟩
  objectArena := .source ⟨Zero.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Zero.arena ⟨Zero.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Pairing.sig Pairing.actual.readout Pairing.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct
    definition := none
    coordinates := #[0, 3, 4, 5, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def circuitPairing_factor_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@circuitPairing_factor.{u}) (Realization Pairing.sig.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct.circuitPairing_factor.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct.Factor.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Factor.arena⟩
  objectArena := .source ⟨Factor.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Factor.arena ⟨Factor.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Pairing.sig Pairing.actual.readout Pairing.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct
    definition := none
    coordinates := #[0, 3, 4, 5, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def circuitPairing_rank_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@circuitPairing_rank.{u}) (Realization Rank.sig.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct.circuitPairing_rank.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct.Rank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Rank.arena⟩
  objectArena := .source ⟨Rank.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Rank.arena ⟨Rank.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Rank.sig Rank.actual.readout Rank.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct
