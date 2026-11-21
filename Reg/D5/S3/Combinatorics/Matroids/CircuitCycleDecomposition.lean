import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition
import Mathlib.Combinatorics.Matroid.Constructions

/-! The signed join summand in the inverse circuit decomposition. -/

namespace Reg.D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition

open LeanInformationAudit
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

abbrev Params :=
  Σ V : Type u, Σ _ : Fintype V, Σ _ : LinearOrder V,
    Σ M : Matroid V, Σ e : V, Σ _ : Finset V, CircuitThrough M e

abbrev sig := signature Params.{u}
  (fun ⟨V, fin, ord, M, _, _, C⟩ => @topCycles V fin ord (M ／ (C.val : Set V)))
  (fun _ => ℤ)

def actual : Realization sig.{u} :=
  realize sig (fun _ ⟨V, _, ord, _, _, F, C⟩ z =>
    @signedJoin V ord C.val (@simplexBoundary V ord C.val) z.val F) (fun e => nomatch e)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ => 1) (fun e => nomatch e)

open scoped Classical in
abbrev arena : Arena where
  signature := sig.{u}
  Law r := ∀ {V : Type u} [fin : Fintype V] [ord : LinearOrder V] (M : Matroid V)
      (e : V) (_ : e ∈ M.E),
    ∃ E : topCycles M ≃ₗ[ℤ] ((C : CircuitThrough M e) → topCycles (M ／ (C.val : Set V))),
      (∀ z C T, (E z C).val T =
        if (M ／ (C.val : Set V)).IsBase (T : Set V) then
          insertionSign (C.val.erase e) e * shuffleSign (C.val.erase e) T *
            z.val (T ∪ C.val.erase e)
        else 0) ∧
      ∀ w F, (E.symm w).val F =
        ∑ C : CircuitThrough M e, r.readout () ⟨V, fin, ord, M, e, F, C⟩ (w C)

private abbrev SampleVertex := ULift.{u} Bool

private def sampleVertex : SampleVertex.{u} := ULift.up false

private def sampleMatroid : Matroid SampleVertex.{u} := loopyOn Set.univ

private def sampleCircuit : CircuitThrough sampleMatroid.{u} sampleVertex.{u} :=
  ⟨{sampleVertex}, by
    constructor
    · rw [Finset.coe_singleton]
      exact (loopyOn_isLoop_iff.mpr (Set.mem_univ _)).isCircuit
    · exact mem_singleton_self _⟩

open scoped Classical in
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨E, _, hinverse⟩ := h sampleMatroid.{u} sampleVertex (Set.mem_univ _)
  have hc : 0 < Fintype.card (CircuitThrough sampleMatroid.{u} sampleVertex) :=
    Fintype.card_pos_iff.mpr ⟨sampleCircuit⟩
  have he := hinverse 0 ∅
  simp only [map_zero, Submodule.coe_zero, Pi.zero_apply] at he
  change (0 : ℤ) = ∑ _ : CircuitThrough sampleMatroid.{u} sampleVertex, (1 : ℤ) at he
  rw [sum_const, card_univ, nsmul_eq_mul, mul_one] at he
  omega

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  let C := sampleCircuit.{u}
  have hbase : (sampleMatroid ／ (C.val : Set SampleVertex)).IsBase
      (↑(∅ : Finset SampleVertex) : Set SampleVertex) := by
    apply (contract_base_iff (circuit_erase_basis C.prop.1 C.prop.2) (by simp)).mpr
    simp [C, sampleCircuit, sampleMatroid]
  let z : topCycles (sampleMatroid ／ (C.val : Set SampleVertex)) :=
    ⟨simplex ∅, ⟨fun F hF => by
      have hne : F ≠ ∅ := fun h => hF (h.symm ▸ hbase)
      simp [simplex, hne], fun R => by simp [boundaryOn, simplex]⟩⟩
  refine ⟨⟨SampleVertex, inferInstance, inferInstance, sampleMatroid,
    sampleVertex, ∅, C⟩, z, 0, ?_⟩
  intro h
  have hboundary : simplexBoundary C.val ∅ = 1 := by
    simpa [C, sampleCircuit, insertionSign] using simplexBoundary_erase C.prop.2
  simp [actual, realize, signedJoin, shuffleSign, hboundary, z, simplex] at h

def source_registration : Registration arena.{u} (type_of% (@circuit_cycle_decomposition.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@circuit_cycle_decomposition.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity _ actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@circuit_cycle_decomposition.{u}) (Realization sig.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition.circuit_cycle_decomposition.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition.source_registration
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
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition
    definition := none
    coordinates := #[0, 3, 4, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition
