import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.EulerLocalContinuation
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Observation of the original complex function in the extension agreement. -/

open _root_.D5.S3.Analytic.Laplace.EulerLocalContinuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Complex Set Filter Metric
open scoped Topology

namespace Reg.D5.S3.Analytic.Laplace.EulerLocalContinuation
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℂ → ℂ) (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ F z => F z) (fun e => nomatch e)

def rejectedOrdinary : Realization signature :=
  realize signature (fun _ _ z => (z - 1)⁻¹) (fun e => nomatch e)

def rejectedZero : Realization signature :=
  realize signature (fun _ _ z => z⁻¹) (fun e => nomatch e)

/-- A genuine pole cannot agree with a continuous full-disk function on a half disk. -/
private theorem pole_obstruction {c δ : ℝ} (hδ : 0 < δ) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (ball (c : ℂ) δ))
    (hEq : EqOn H (fun z => (z - (c : ℂ))⁻¹) (rightHalfDisk c δ)) : False := by
  have hcont : ContinuousAt H (c : ℂ) :=
    (hH.hasDerivAt (isOpen_ball.mem_nhds (mem_ball_self hδ))).continuousAt
  have hxc : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcenter : Tendsto (fun x : ℝ => (c : ℂ) + (x : ℂ))
      (𝓝[Ioi 0] 0) (𝓝 (c : ℂ)) := by
    simpa using tendsto_const_nhds.add hxc
  have hprod : Tendsto (fun x : ℝ => (x : ℂ) * H ((c : ℂ) + (x : ℂ)))
      (𝓝[Ioi 0] 0) (𝓝 (0 : ℂ)) := by
    simpa using hxc.mul (hcont.tendsto.comp hcenter)
  have heq : (fun x : ℝ => (x : ℂ) * H ((c : ℂ) + (x : ℂ)))
      =ᶠ[𝓝[Ioi 0] 0] fun _ => (1 : ℂ) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with x hx hxδ
    have hxp : 0 < x := hx
    have hz : (c : ℂ) + (x : ℂ) ∈ rightHalfDisk c δ := by
      constructor
      · simpa [mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_of_pos hxp] using hxδ
      · simpa using hxp
    rw [hEq hz]
    simpa using mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hxp.ne')
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds (hprod.congr' heq))

def ordinaryArena : Arena where
  signature := signature
  Law Q := ∀ {c r : ℝ}, c ≠ 0 → 0 < r → ∀ {R F : ℂ → ℂ},
    DifferentiableOn ℂ R (ball (c : ℂ) r) →
    DifferentiableOn ℂ F (rightHalfDisk c r) →
    (∀ z ∈ rightHalfDisk c r,
      z * deriv (deriv F) z + 2 * deriv F z = R z) →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧ ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H (ball (c : ℂ) δ) ∧
        EqOn H (Q.readout () F) (rightHalfDisk c δ)

def zeroArena : Arena where
  signature := signature
  Law Q := ∀ {r : ℝ}, 0 < r → ∀ {R F : ℂ → ℂ} {ell : ℂ},
    DifferentiableOn ℂ R (ball (0 : ℂ) r) →
    DifferentiableOn ℂ F (rightHalfDisk 0 r) →
    (∀ z ∈ rightHalfDisk 0 r,
      z * deriv (deriv F) z + 2 * deriv F z = R z) →
    Tendsto (fun x : ℝ => F (x : ℂ)) (𝓝[Ioi 0] 0) (𝓝 ell) →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧ ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H (ball (0 : ℂ) δ) ∧
        EqOn H (Q.readout () F) (rightHalfDisk 0 δ) ∧ H 0 = ell

private theorem ordinary_rejected : ¬ ordinaryArena.Law rejectedOrdinary := by
  intro h
  obtain ⟨δ, hδ, _, H, hH, he⟩ := h (c := 1) (r := 1) one_ne_zero zero_lt_one
    (R := fun _ => 0) (F := fun _ => 0)
    (differentiable_const (0 : ℂ)).differentiableOn
    (differentiable_const (0 : ℂ)).differentiableOn (by intro z hz; simp)
  exact pole_obstruction (c := 1) hδ hH he

private theorem zero_rejected : ¬ zeroArena.Law rejectedZero := by
  intro h
  obtain ⟨δ, hδ, _, H, hH, he, _⟩ := h (r := 1) zero_lt_one
    (R := fun _ => 0) (F := fun _ => 0) (ell := 0)
    (differentiable_const (0 : ℂ)).differentiableOn
    (differentiable_const (0 : ℂ)).differentiableOn (by intro z hz; simp)
    tendsto_const_nhds
  exact pole_obstruction (c := 0) hδ hH (by simpa [rejectedZero, realize] using he)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨id, 0, 1, zero_ne_one⟩

def ordinaryEvidence : Registration ordinaryArena (type_of% @exists_extension_of_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_extension_of_ne_zero, rejectedOrdinary, ordinary_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    ordinaryArena.Law actual rejectedOrdinary ordinary_rejected
  dependence := actual_dependence

def zeroEvidence : Registration zeroArena (type_of% @exists_extension_at_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_extension_at_zero, rejectedZero, zero_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    zeroArena.Law actual rejectedZero zero_rejected
  dependence := actual_dependence

def ordinaryAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_extension_of_ne_zero) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.EulerLocalContinuation.exists_extension_of_ne_zero.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.EulerLocalContinuation.ordinaryEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨ordinaryArena⟩
  objectArena := .source ⟨ordinaryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ordinaryArena ⟨ordinaryEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ F z => F z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.EulerLocalContinuation
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def zeroAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_extension_at_zero) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.EulerLocalContinuation.exists_extension_at_zero.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.EulerLocalContinuation.zeroEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨zeroArena⟩
  objectArena := .source ⟨zeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zeroArena ⟨zeroEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ F z => F z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.EulerLocalContinuation
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.Laplace.EulerLocalContinuation
