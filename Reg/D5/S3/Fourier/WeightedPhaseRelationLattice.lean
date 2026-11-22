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


abbrev deficitSignature : Signature where
  Params := Σ J : Type u, Fintype J × (J → ℝ)
  State p := p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def deficitActual : Realization deficitSignature.{u} :=
  realize deficitSignature (fun _ p w =>
    let _ : Fintype p.1 := p.2.1
    let γ := p.2.2
    1 - (⨆ t : ℝ, (∑ j, w j * Real.sin (γ j * t)) / (∑ j, w j)))
    (fun e => nomatch e)

def deficitRejected : Realization deficitSignature.{u} :=
  realize deficitSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev deficitArena : Arena where
  signature := deficitSignature.{u}
  Law r := ∀ {J : Type u} {A : Type v} [hJ : Fintype J] [Fintype A]
    [DecidableEq J] [DecidableEq A] (γ w : J → ℝ) (K : Matrix A J ℤ) (_hw : ∀ j, 0 < w j)
    (_hW : 0 < ∑ j, w j)
    (_hK : ∀ k : J → ℤ, k ∈ Submodule.span ℤ (range K.row) ↔
      (∑ j, (k j : ℝ) * γ j) = 0)
    (_hind : LinearIndependent ℝ (K.map (Int.cast : ℤ → ℝ)).row),
    let W := ∑ j, w j
    let R := K.map (Int.cast : ℤ → ℝ)
    let M := diagonal w
    let G := R * M⁻¹ * Rᵀ
    let b (z : A → ℤ) (a : A) :=
      (z a : ℝ) * (2 * Real.pi) - (Real.pi / 2) * (R *ᵥ (1 : J → ℝ)) a
    let E := ⨅ z : A → ℤ, b z ⬝ᵥ (G⁻¹ *ᵥ b z)
    let D := r.readout () ⟨J, hJ, γ⟩ w
    2 * E / (Real.pi ^ 2 * W) ≤ D ∧ D ≤ E / (2 * W) ∧ (IsEmpty A → E = 0)

private theorem deficitRejectedLaw : ¬ deficitArena.{u,v}.Law deficitRejected := by
  intro law
  let J := ULift.{u} Unit
  let K : Matrix (ULift.{v} Empty) J ℤ := 0
  have hK (k : J → ℤ) :
      k ∈ Submodule.span ℤ (range K.row) ↔ (∑ j, (k j : ℝ) * (1 : ℝ)) = 0 := by
    simp only [range_eq_empty, Submodule.span_empty, Submodule.mem_bot, mul_one,
      Fintype.sum_unique, Int.cast_eq_zero]
    exact ⟨fun h => congrFun h default, fun h => funext fun j => (Subsingleton.elim j default) ▸ h⟩
  have h := law (fun _ => 1) (fun _ => 1) K (by simp) (by simp [J]) hK
    linearIndependent_empty_type
  have hup := h.2.1
  norm_num [deficitRejected, realize, dotProduct] at hup

private theorem deficitDependence : ObservationalDependence deficitSignature.{u} deficitActual := by
  intro i
  let J := ULift.{u} Unit
  refine ⟨⟨J, inferInstance, fun _ => 1⟩, fun _ => 0, fun _ => 1, ?_⟩
  intro h
  have heq : 1 = 1 - (⨆ t : ℝ, Real.sin t) := by
    simpa [deficitActual, realize, J] using h
  have hz : (⨆ t : ℝ, Real.sin t) = 0 := by linarith
  have hub : BddAbove (range Real.sin) := ⟨1, by
    rintro _ ⟨t, rfl⟩
    exact Real.sin_le_one t⟩
  have hπ := le_ciSup hub (Real.pi / 2)
  rw [Real.sin_pi_div_two, hz] at hπ
  norm_num at hπ

def deficitSource :
    Registration deficitArena.{u,v} (type_of% @weighted_phase_deficit_bounds.{u,v}) where
  actual := deficitActual
  bridge := Iff.rfl
  variation := ⟨@weighted_phase_deficit_bounds.{u,v}, deficitRejected, deficitRejectedLaw.{u,v}⟩
  sensitivity := singleRoleSensitivity deficitArena.{u,v}.Law deficitActual deficitRejected
    inferInstance inferInstance deficitRejectedLaw.{u,v}
  dependence := deficitDependence

def deficitAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_phase_deficit_bounds.{u,v}) (Realization deficitSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.WeightedPhaseRelationLattice.deficitUnit
  realizationName := `Reg.D5.S3.Fourier.WeightedPhaseRelationLattice.deficitSource
  realizationSource := none
  generated := false
  arena := .source ⟨deficitArena.{u,v}⟩
  objectArena := .source ⟨deficitArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deficitArena.{u,v} ⟨deficitSource.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize deficitSignature (fun _ p w =>
    let _ : Fintype p.1 := p.2.1
    let γ := p.2.2
    1 - (⨆ t : ℝ, (∑ j, w j * Real.sin (γ j * t)) / (∑ j, w j)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.WeightedPhaseRelationLattice
    definition := none
    coordinates := #[0, 6]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms orbitAudit
#print axioms liftAudit
#print axioms deficitAudit

end

end Reg.D5.S3.Fourier.WeightedPhaseRelationLattice
