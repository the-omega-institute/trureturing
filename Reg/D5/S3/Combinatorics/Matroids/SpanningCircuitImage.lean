import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.SpanningCircuitImage
import Mathlib.Combinatorics.Matroid.Loop

/-! The signed circuit restriction as an observation of a top chain. -/

namespace Reg.D5.S3.Combinatorics.Matroids.SpanningCircuitImage

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
open _root_.D5.S3.Combinatorics.Matroids.CircuitRestrictionImage (signedRestriction dualClassGcd)
open _root_.D5.S3.Combinatorics.Matroids.SpanningCircuitImage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.UniverseSingleReadout (signature sensitivity)
open Finset Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev Params := Σ V : Type u, Σ _ : LinearOrder V, Finset V

abbrev sig := signature Params.{u} (fun p => Chain p.1) (fun _ => ℤ)

def actual : Realization sig.{u} :=
  realize sig (fun _ ⟨V, ord, K⟩ z => @signedRestriction V ord K z) (fun e => nomatch e)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig.{u}
  Law r := ∀ {V : Type u} [ord : LinearOrder V] [Fintype V]
      (M : Matroid V) (K : Finset V)
      (_ : M.IsCircuit (K : Set V)) (_ : M.Spanning (K : Set V)) (n : ℤ),
      (∃ z : Chain V, TopCycle M z ∧ r.readout () ⟨V, ord, K⟩ z = n) ↔
        (dualClassGcd M K : ℤ) ∣ n

private abbrev Sample := ULift.{u} Bool

private def a : Sample.{u} := ULift.up false

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let M := loopyOn ({a} : Set Sample.{u})
  have hK : M.IsCircuit (↑({a} : Finset Sample.{u}) : Set Sample.{u}) := by
    simp [M, singleton_isCircuit, loopyOn_isLoop_iff]
  have hs : M.Spanning (↑({a} : Finset Sample.{u}) : Set Sample.{u}) := by simp [M]
  have hd : (dualClassGcd M ({a} : Finset Sample.{u}) : ℤ) ∣ 1 := by
    simp [dualClassGcd, filter_singleton]
  obtain ⟨_, _, he⟩ := (h M {a} hK hs 1).2 hd
  exact zero_ne_one he

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  refine ⟨⟨Sample.{u}, inferInstance, {a}⟩, fun _ => 1, fun _ => 0, ?_⟩
  change signedRestriction ({a} : Finset Sample.{u}) (fun _ => 1) ≠
    signedRestriction ({a} : Finset Sample.{u}) (fun _ => 0)
  have hboundary : simplexBoundary ({a} : Finset Sample.{u}) ∅ = 1 := by
    simpa [_root_.D5.S3.HomologicalAlgebra.OrderedFaceSign.insertionSign] using
      simplexBoundary_erase (mem_singleton_self a)
  simp [signedRestriction, hboundary]

def source_registration : Registration arena.{u}
    (type_of% (@exists_topCycle_signedRestriction_iff.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_topCycle_signedRestriction_iff.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity _ actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_topCycle_signedRestriction_iff.{u}) (Realization sig.{u}) Type Unit where
  unitName := .str
    `D5.S3.Combinatorics.Matroids.SpanningCircuitImage.exists_topCycle_signedRestriction_iff
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SpanningCircuitImage.source_registration
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
    owner := `D5.S3.Combinatorics.Matroids.SpanningCircuitImage
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.SpanningCircuitImage
