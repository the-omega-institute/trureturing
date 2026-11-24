import D5.S3.HilbertOperators.OrderThreeOrientationBound
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

/-! The determinant of the orthogonal input is the orientation readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.HilbertOperators.OrderThreeOrientationBound

open _root_.D5.S3.HilbertOperators.OrderThreeOrientationBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

attribute [local instance] InnerProductSpace.complexToReal

universe u v

structure Parameters where
  H : Type u
  [additive : NormedAddCommGroup H]
  [inner : InnerProductSpace ℝ H]

abbrev signature : Signature where
  Params := Parameters.{u}
  State p :=
    letI := p.additive
    letI := p.inner
    p.H →L[ℝ] p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p => by
    letI := p.additive
    letI := p.inner
    exact ContinuousLinearMap.det) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      {ι : Type v} [FiniteDimensional ℝ H] (S : Finset ι)
      (T : ι → H →L[ℝ] H) (U : H →L[ℝ] H),
      (∀ j ∈ S, ∀ x, ‖T j x‖ = ‖x‖) →
      (∀ j ∈ S, T j ^ 3 = 1) →
      (∀ i ∈ S, ∀ j ∈ S, Commute (T i) (T j)) →
      (∀ x, ‖U x‖ = ‖x‖) →
      R.readout () (@Parameters.mk H inferInstance inferInstance) U < 0 →
      (∀ A : H →L[ℝ] H, (∀ j ∈ S, Commute A (T j)) → 0 ≤ A.det) →
      3 ≤ ∑ j ∈ S, commutatorNorm T U j ^ 2

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let H := EuclideanSpace ℝ (ULift.{u} (Fin 0))
  let T : ULift.{v} Unit → H →L[ℝ] H := fun _ => 1
  have hb := h (H := H) (ι := ULift.{v} Unit) ∅ T 1
    (by simp) (by simp) (by simp) (by simp)
    (by norm_num [rejected, realize])
    (fun A _ => by simp [ContinuousLinearMap.det, LinearMap.det_eq_one_of_subsingleton])
  norm_num at hb

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  let H := EuclideanSpace ℝ (ULift.{u} Unit)
  refine ⟨@Parameters.mk H inferInstance inferInstance, 0, 1, ?_⟩
  change (0 : H →L[ℝ] H).det ≠ (1 : H →L[ℝ] H).det
  rw [show (0 : H →L[ℝ] H).det = 0 from
    LinearMap.det_zero' (EuclideanSpace.basisFun (ULift.{u} Unit) ℝ).toBasis]
  change 0 ≠ (1 : H →ₗ[ℝ] H).det
  simp

def evidence : Registration arena.{u,v} (type_of% @sum_sq_commutatorNorm_ge_three.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_sq_commutatorNorm_ge_three.{u,v}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@sum_sq_commutatorNorm_ge_three.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HilbertOperators.OrderThreeOrientationBound.unit
  realizationName := `Reg.D5.S3.HilbertOperators.OrderThreeOrientationBound.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => by
    letI := p.additive
    letI := p.inner
    exact ContinuousLinearMap.det) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HilbertOperators.OrderThreeOrientationBound
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

structure PlaneParameters where
  κ : Type v
  [finite : Fintype κ]

abbrev planeSignature : Signature where
  Params := PlaneParameters.{v}
  State p :=
    letI := p.finite
    EuclideanSpace ℂ p.κ →L[ℝ] EuclideanSpace ℂ p.κ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def planeActual : Realization planeSignature.{v} :=
  realize planeSignature (fun _ p => by
    letI := p.finite
    exact ContinuousLinearMap.det) (fun e => nomatch e)

def planeRejected : Realization planeSignature.{v} :=
  realize planeSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev planeArena : Arena where
  signature := planeSignature.{v}
  Law R :=
    ∀ {ι : Type u} {κ : Type v} [Fintype κ]
      (S : Finset ι) (w : ι → κ → ℂ) (U : EuclideanSpace ℂ κ →L[ℝ] EuclideanSpace ℂ κ),
      (∀ j ∈ S, ∀ k, w j k ^ 3 = 1) →
      (∀ i k, ∃ j ∈ S, w j i ≠ starRingEnd ℂ (w j k)) →
      (∀ x, ‖U x‖ = ‖x‖) →
      R.readout () (@PlaneParameters.mk κ inferInstance) U < 0 →
      (3 ≤ ∑ j ∈ S, commutatorNorm (fun j => characterPlane (w j)) U j ^ 2) ∧
        ∃ j ∈ S, Real.sqrt (3 / (S.card : ℝ)) ≤
          commutatorNorm (fun j => characterPlane (w j)) U j

private theorem plane_rejected_law : ¬ planeArena.{u,v}.Law planeRejected := by
  intro h
  let κ := ULift.{v} (Fin 0)
  have hb := h (ι := ULift.{u} Unit) (κ := κ) ∅ (fun _ _ => 1) 1
    (by simp) (fun i => isEmptyElim i) (by simp)
    (by norm_num [planeRejected, realize])
  have hz := hb.1
  norm_num at hz

private theorem plane_dependence : ObservationalDependence planeSignature.{v} planeActual := by
  intro _
  let κ := ULift.{v} Unit
  refine ⟨@PlaneParameters.mk κ inferInstance, 0, 1, ?_⟩
  let H := EuclideanSpace ℂ κ
  change (0 : H →L[ℝ] H).det ≠ (1 : H →L[ℝ] H).det
  have hzero : (0 : H →L[ℝ] H).det = 0 := by
    change (0 : H →ₗ[ℝ] H).det = 0
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    rw [LinearMap.ker_zero]
    exact top_ne_bot
  rw [hzero]
  change 0 ≠ (1 : H →ₗ[ℝ] H).det
  simp

def planeEvidence :
    Registration planeArena.{u,v} (type_of% @characterPlane_commutator_bounds.{u,v}) where
  actual := planeActual
  bridge := Iff.rfl
  variation := ⟨@characterPlane_commutator_bounds.{u,v}, planeRejected, plane_rejected_law⟩
  sensitivity := ⟨fun i => ⟨planeRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, plane_rejected_law⟩, fun e => nomatch e⟩
  dependence := plane_dependence

def planeRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@characterPlane_commutator_bounds.{u,v}) (Realization planeSignature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.HilbertOperators.OrderThreeOrientationBound.planeUnit
  realizationName := `Reg.D5.S3.HilbertOperators.OrderThreeOrientationBound.planeEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨planeArena⟩
  objectArena := .source ⟨planeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source planeArena ⟨planeEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize planeSignature (fun _ p => by
    letI := p.finite
    exact ContinuousLinearMap.det) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HilbertOperators.OrderThreeOrientationBound
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.HilbertOperators.OrderThreeOrientationBound
