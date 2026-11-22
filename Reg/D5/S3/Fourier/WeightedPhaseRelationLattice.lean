import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.WeightedPhaseRelationLattice
import Reg.Support.DependentFamily

/-! Source-bound observations of the actual orbit and its weighted deficit. -/

namespace Reg.D5.S3.Fourier.WeightedPhaseRelationLattice

open _root_.D5.S3.Fourier.WeightedPhaseRelationLattice
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Matrix
open scoped BigOperators Matrix

set_option autoImplicit false
noncomputable section
universe u v

abbrev orbitSignature : Signature where
  Params := Type u
  State J := J → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ J := Set (J → Circle)
  Anchor := Empty
  finiteAnchor := inferInstance

def orbitActual : Realization orbitSignature.{u} :=
  realize orbitSignature (fun _ _ γ => closure (range (fun (t : ℝ) j =>
    Circle.exp (γ j * t)))) (fun e => nomatch e)

def orbitRejected : Realization orbitSignature.{u} :=
  realize orbitSignature (fun _ _ _ => ∅) (fun e => nomatch e)

private theorem singleRoleSensitivity {s : Signature} (law : Realization s → Prop)
    (actual rejected : Realization s) (hs : Subsingleton s.Role) (ha : IsEmpty s.Anchor)
    (h : ¬ law rejected) : Sensitivity ⟨s, law⟩ actual := by
  constructor
  · intro i
    exact ⟨rejected, fun j hj => (hj (hs.allEq j i)).elim,
      funext fun e => (ha.false e).elim, h⟩
  · intro i
    exact (ha.false i).elim

private theorem orbitDependence : ObservationalDependence orbitSignature.{u} orbitActual := by
  intro i
  let J := ULift.{u} Unit
  refine ⟨J, fun _ => 1, fun _ => 0, ?_⟩
  intro h
  change closure (range (fun t : ℝ => fun _ : J => Circle.exp (1 * t))) =
    closure (range (fun t : ℝ => fun _ : J => Circle.exp (0 * t))) at h
  simp only [one_mul, zero_mul, Circle.exp_zero, range_const, closure_singleton] at h
  have hp : (fun _ : J => Circle.exp Real.pi) ∈
      closure (range (fun t : ℝ => fun _ : J => Circle.exp t)) :=
    subset_closure (mem_range_self Real.pi)
  rw [h, mem_singleton_iff] at hp
  exact Circle.exp_pi_ne_one (congrFun hp (ULift.up ()))

abbrev orbitArena : Arena where
  signature := orbitSignature.{u}
  Law r := ∀ {J : Type u} [Fintype J] (γ : J → ℝ),
    r.readout () J γ =
      {p | ∀ k : J → ℤ, (∑ j, (k j : ℝ) * γ j) = 0 → (∏ j, p j ^ k j) = 1}

private theorem orbitRejectedLaw : ¬ orbitArena.{u}.Law orbitRejected := by
  intro law
  have h := law (J := ULift.{u} Unit) (fun _ => 0)
  have hone : (1 : ULift.{u} Unit → Circle) ∈
      {p | ∀ k : ULift.{u} Unit → ℤ, (∑ j, (k j : ℝ) * 0) = 0 → (∏ j, p j ^ k j) = 1} := by
    simp
  rw [← h] at hone
  exact hone

def orbitSource : Registration orbitArena.{u} (type_of% @closure_real_phase_orbit.{u}) where
  actual := orbitActual
  bridge := Iff.rfl
  variation := ⟨@closure_real_phase_orbit.{u}, orbitRejected, orbitRejectedLaw⟩
  sensitivity := singleRoleSensitivity orbitArena.{u}.Law orbitActual orbitRejected
    inferInstance inferInstance orbitRejectedLaw
  dependence := orbitDependence

def orbitAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@closure_real_phase_orbit.{u}) (Realization orbitSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.WeightedPhaseRelationLattice.orbitUnit
  realizationName := `Reg.D5.S3.Fourier.WeightedPhaseRelationLattice.orbitSource
  realizationSource := none
  generated := false
  arena := .source ⟨orbitArena.{u}⟩
  objectArena := .source ⟨orbitArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source orbitArena.{u} ⟨orbitSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize orbitSignature (fun _ _ γ => closure (range (fun (t : ℝ) j =>
    Circle.exp (γ j * t)))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.WeightedPhaseRelationLattice
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev liftArena : Arena where
  signature := orbitSignature.{u}
  Law r := ∀ {J : Type u} {A : Type v} [Fintype J] [Finite A]
    (γ : J → ℝ) (K : Matrix A J ℤ)
    (_hK : ∀ k : J → ℤ, k ∈ Submodule.span ℤ (range K.row) ↔
      (∑ j, (k j : ℝ) * γ j) = 0) (x : J → ℝ),
    (fun j => Circle.exp (x j + Real.pi / 2)) ∈ r.readout () J γ ↔
    ∃ z : A → ℤ, (K.map (Int.cast : ℤ → ℝ)) *ᵥ x =
      fun a => (z a : ℝ) * (2 * Real.pi) -
        (Real.pi / 2) * ((K.map (Int.cast : ℤ → ℝ)) *ᵥ (1 : J → ℝ)) a

private theorem liftRejectedLaw : ¬ liftArena.{u,v}.Law orbitRejected := by
  intro law
  let K : Matrix (ULift.{v} Empty) (ULift.{u} Empty) ℤ := 0
  have hK (k : ULift.{u} Empty → ℤ) :
      k ∈ Submodule.span ℤ (range K.row) ↔ (∑ j, (k j : ℝ) * (0 : ℝ)) = 0 := by
    rw [Subsingleton.elim k 0]
    simp
  have h := (law (fun _ => 0) K hK (fun _ => 0)).mpr
    ⟨0, Subsingleton.elim _ _⟩
  exact h

def liftSource : Registration liftArena.{u,v} (type_of% @centered_lift_iff.{u,v}) where
  actual := orbitActual
  bridge := Iff.rfl
  variation := ⟨@centered_lift_iff.{u,v}, orbitRejected, liftRejectedLaw.{u,v}⟩
  sensitivity := singleRoleSensitivity liftArena.{u,v}.Law orbitActual orbitRejected
    inferInstance inferInstance liftRejectedLaw.{u,v}
  dependence := orbitDependence

def liftAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@centered_lift_iff.{u,v}) (Realization orbitSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.WeightedPhaseRelationLattice.liftUnit
  realizationName := `Reg.D5.S3.Fourier.WeightedPhaseRelationLattice.liftSource
  realizationSource := none
  generated := false
  arena := .source ⟨liftArena.{u,v}⟩
  objectArena := .source ⟨liftArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source liftArena.{u,v} ⟨liftSource.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize orbitSignature (fun _ _ γ => closure (range (fun (t : ℝ) j =>
    Circle.exp (γ j * t)))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.WeightedPhaseRelationLattice
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.WeightedPhaseRelationLattice
