import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
import Mathlib.Combinatorics.Matroid.Constructions

/-! Observations of ordered joins and normalized top-cycle coordinates. -/

namespace Reg.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
open _root_.D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.UniverseSingleReadout (signature sensitivity)
open Finset Matroid
open scoped Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Join

abbrev Params := Σ V : Type u, Σ _ : LinearOrder V, Σ _ : Finset V, Σ _ : Chain V, Chain V

abbrev sig := signature Params.{u} (fun p => Finset p.1) (fun _ => ℤ)

def actual : Realization sig.{u} :=
  realize sig (fun _ ⟨V, ord, C, l, v⟩ F => @signedJoin V ord C l v F) (fun e => nomatch e)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig.{u}
  Law r := ∀ {V : Type u} [ord : LinearOrder V] [Fintype V] (C R : Finset V) (l v : Chain V),
    boundaryOn univ (r.readout () ⟨V, ord, C, l, v⟩) R =
      shuffleSign (R ∩ C) (R \ C) *
        (boundaryOn C l (R ∩ C) * v (R \ C) +
          (-1) ^ (R ∩ C).card * (l (R ∩ C) * boundaryOn (univ \ C) v (R \ C)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let x : ULift.{u} Bool := ULift.up false
  have hh := h {x} ∅ (simplex {x}) (simplex ∅)
  simpa [rejected, realize, boundaryOn, simplex, shuffleSign, insertionSign, x] using hh

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  let x : ULift.{u} Bool := ULift.up false
  refine ⟨⟨ULift.{u} Bool, inferInstance, {x}, simplex {x}, simplex ∅⟩, {x}, ∅, ?_⟩
  intro h
  simp [actual, realize, signedJoin, simplex, shuffleSign, x] at h

def source_registration : Registration arena.{u} (type_of% (@boundaryOn_signedJoin.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundaryOn_signedJoin.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity _ actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@boundaryOn_signedJoin.{u}) (Realization sig.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.OrderedCycleFactorization.boundaryOn_signedJoin.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization.Join.source_registration
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
    owner := `D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
    definition := none
    coordinates := #[0, 3, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Join

namespace Normalization

abbrev Params := Σ V : Type u, Σ _ : LinearOrder V, Σ _ : Fintype V, Matroid V

abbrev sig := signature Params.{u} (fun p => Finset p.1) (fun p => Chain p.1 → Prop)

def actual : Realization sig.{u} :=
  realize sig (fun _ p B => @Normalized p.1 p.2.1 p.2.2.1 p.2.2.2 B) (fun e => nomatch e)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig.{u}
  Law r := ∀ {V : Type u} [ord : LinearOrder V] [fin : Fintype V] (M : Matroid V) (B : Finset V),
    PassiveBase M B →
    (∃! z, r.readout () ⟨V, ord, fin, M⟩ B z) ∧
    (∀ z, Normalized M B z → B = ∅ → z = simplex ∅) ∧
    ∀ e, LeastNonloop M e →
      let C := circuitAt M B e
      let D := B \ C
      PassiveBase (M ／ (C : Set V)) D ∧
      ∀ z w, Normalized M B z → Normalized (M ／ (C : Set V)) D w →
        z = circuitLift C e B w ∧
        (∀ F, F ∈ cycleSupport z ↔
          ∃ x ∈ C, F ∩ C = C.erase x ∧ F \ C ∈ cycleSupport w) ∧
        (cycleSupport z).card = C.card * (cycleSupport w).card

private theorem passive_empty (M : Matroid (ULift.{u} Bool))
    (h : M.IsBase ∅) : PassiveBase M ∅ := by
  exact ⟨by simpa using h, fun _ hx => (notMem_empty _ hx).elim⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let M := loopyOn (Set.univ : Set (ULift.{u} Bool))
  obtain ⟨z, hz, _⟩ := (h M ∅ (passive_empty M (by simp [M]))).1
  exact hz

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  let M := loopyOn (Set.univ : Set (ULift.{u} Bool))
  let x : ULift.{u} Bool := ULift.up false
  have hp := passive_empty M (by simp [M])
  obtain ⟨⟨z, hz, _⟩, _, _⟩ := normalized_factorization M ∅ hp
  refine ⟨⟨ULift.{u} Bool, inferInstance, inferInstance, M⟩, ∅, {x}, ?_⟩
  intro h
  have h' : Normalized M ∅ z = Normalized M {x} z := congrFun h z
  have hw : Normalized M {x} z := h' ▸ hz
  have h0 : z ∅ = 0 := by simpa using hw.coordinate ∅ hp
  have h1 : z ∅ = 1 := by simpa using hz.coordinate ∅ hp
  exact Int.zero_ne_one (h0.symm.trans h1)

def source_registration : Registration arena.{u} (type_of% (@normalized_factorization.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_factorization.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity _ actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@normalized_factorization.{u}) (Realization sig.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.OrderedCycleFactorization.normalized_factorization.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization.Normalization.source_registration
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
    owner := `D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "fn"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Normalization
end
end Reg.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
