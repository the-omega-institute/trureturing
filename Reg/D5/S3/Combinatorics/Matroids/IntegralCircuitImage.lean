import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.IntegralCircuitImage
import Mathlib.Combinatorics.Matroid.Constructions

namespace Reg.D5.S3.Combinatorics.Matroids.IntegralCircuitImage

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
open _root_.D5.S3.Combinatorics.Matroids.IntegralCircuitImage
open _root_.D5.S3.Combinatorics.Matroids.CircuitRestrictionImage (dualClassGcd)
open _root_.D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition (restrictChain restrictionSign)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.UniverseSingleReadout (signature sensitivity)
open Finset Matroid
open scoped Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

abbrev Params := Σ V : Type u, Σ _ : Fintype V, Σ _ : LinearOrder V, Matroid V × Finset V
abbrev sig := signature Params.{u} (fun p => Chain p.1) (fun p => Chain p.1)

def actual : Realization sig.{u} :=
  realize sig (fun _ ⟨V, _, ord, M, K⟩ z => @aggregateRestrict V ord M K z) (fun e => nomatch e)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig.{u}
  Law r := ∀ {V : Type u} [fin : Fintype V] [ord : LinearOrder V]
      {M : Matroid V} {K : Finset V} (_ : M.IsCircuit (K : Set V)) (u : Chain V),
    (∃ z : Chain V, TopCycle M z ∧ r.readout () ⟨V, fin, ord, M, K⟩ z = u) ↔
      ∃ w : Chain V, TopCycle (M ／ (K : Set V)) w ∧ u = (dualClassGcd M K : ℤ) • w

private abbrev Sample := ULift.{u} Bool
private def vertex : Sample.{u} := ULift.up false
private def sample : Matroid Sample.{u} := loopyOn Set.univ
private def circuit : Finset Sample.{u} := {vertex}

private lemma circuit_isCircuit : sample.{u}.IsCircuit (circuit : Set Sample.{u}) := by
  simp [sample, circuit, singleton_isCircuit, loopyOn_isLoop_iff]

private lemma simplex_topCycle : TopCycle sample.{u} (simplex ∅) := by
  refine ⟨fun F hF => ?_, fun R => ?_⟩
  · have hne : F ≠ ∅ := fun h => hF (by simp [h, sample])
    simp [simplex, hne]
  · apply sum_eq_zero
    intro a _
    rw [simplex, ite_eq_right (by simp), mul_zero]

private lemma aggregate_sample :
    aggregateRestrict sample.{u} circuit (simplex ∅) ∅ = 1 := by
  classical
  have hb : (sample.{u} ／ (circuit : Set Sample.{u})).IsBase (↑(∅ : Finset Sample.{u}) : Set Sample.{u}) := by
    apply (contract_base_iff (circuit_erase_basis circuit_isCircuit (mem_singleton_self vertex))
      (by simp)).2
    simp [sample, circuit]
  simp [aggregateRestrict, circuit, restrictChain,
    show (sample.{u} ／ ({vertex} : Set Sample.{u})).IsBase ∅ from by simpa [circuit] using hb,
    restrictionSign, simplex, shuffleSign,
    _root_.D5.S3.HomologicalAlgebra.OrderedFaceSign.insertionSign]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let y := aggregateRestrict sample.{u} circuit (simplex ∅)
  have hr := (exists_topCycle_aggregateRestrict_iff circuit_isCircuit y).1
    ⟨simplex ∅, simplex_topCycle, rfl⟩
  obtain ⟨_, _, hy⟩ := (h circuit_isCircuit y).2 hr
  have he : (0 : Chain Sample.{u}) = y := hy
  have he' := congrFun he ∅
  change (0 : ℤ) = aggregateRestrict sample.{u} circuit (simplex ∅) ∅ at he'
  rw [aggregate_sample] at he'
  exact zero_ne_one he'

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  refine ⟨⟨Sample.{u}, inferInstance, inferInstance, sample, circuit⟩, simplex ∅, 0, ?_⟩
  intro h
  have he := congrFun h ∅
  change aggregateRestrict sample.{u} circuit (simplex ∅) ∅ =
    aggregateRestrict sample.{u} circuit 0 ∅ at he
  rw [aggregate_sample] at he
  simp [aggregateRestrict, restrictChain] at he

def source_registration : Registration arena.{u}
    (type_of% @exists_topCycle_aggregateRestrict_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_topCycle_aggregateRestrict_iff.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity _ actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_topCycle_aggregateRestrict_iff.{u}) (Realization sig.{u}) Type Unit where
  unitName := .str
    `D5.S3.Combinatorics.Matroids.IntegralCircuitImage.exists_topCycle_aggregateRestrict_iff
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.IntegralCircuitImage.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.IntegralCircuitImage
