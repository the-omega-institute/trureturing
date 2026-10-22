import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.WallisRemainder.Laplace
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.WallisRemainder.Laplace

open _root_.D5.S3.Analytic.WallisRemainder.Defs
open _root_.D5.S3.Analytic.WallisRemainder.Laplace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory Set
noncomputable section

abbrev logarithmSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def logarithmActual : Realization logarithmSignature :=
  realize logarithmSignature (fun _ _ x => -Real.log (wallisB x)) (fun e => nomatch e)

def logarithmRejected : Realization logarithmSignature :=
  realize logarithmSignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- A positive evaluation used by the rejected-realization certificates. -/
theorem logarithmPositive {x : ℝ} (hx : 0 < x) : 0 < -Real.log (wallisB x) := by
  have hp : ∀ t ∈ Ioi (0 : ℝ), 0 < laplaceKernel x t := by
    intro t ht
    change 0 < t at ht
    unfold laplaceKernel
    apply div_pos
    · apply mul_pos (Real.exp_pos _)
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
    · linarith
  have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ laplaceKernel x t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact (hp t ht).le
  rw [r_eq_laplace hx]
  change 0 < ∫ t in Ioi (0 : ℝ), laplaceKernel x t
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn (integrableOn_laplaceKernel hx)]
  have hs : Function.support (laplaceKernel x) ∩ Ioi 0 = Ioi 0 := by
    ext t
    exact ⟨And.right, fun ht => ⟨(hp t ht).ne', ht⟩⟩
  rw [hs]
  simp

theorem logarithmDependence : ObservationalDependence logarithmSignature logarithmActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change -Real.log (wallisB 0) ≠ -Real.log (wallisB 1)
  rw [show wallisB 0 = 0 by simp [wallisB], Real.log_zero, neg_zero]
  exact (logarithmPositive (x := 1) zero_lt_one).ne

abbrev representationArena : Arena where
  signature := logarithmSignature
  Law R := ∀ {x : ℝ}, 0 < x → R.readout () () x =
    ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * Real.tanh (t / 4) / (2 * t)

private theorem representationRejected : ¬ representationArena.Law logarithmRejected := by
  intro h
  have h0 := h (x := 1) zero_lt_one
  change 0 = _ at h0
  have h1 := r_eq_laplace (x := 1) zero_lt_one
  linarith [logarithmPositive (x := 1) zero_lt_one]

def representationFamily : Registration representationArena (type_of% @r_eq_laplace) where
  actual := logarithmActual
  bridge := Iff.rfl
  variation := ⟨r_eq_laplace, logarithmRejected, representationRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    representationArena.Law logarithmActual logarithmRejected representationRejected
  dependence := logarithmDependence

abbrev kernelSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def kernelActual : Realization kernelSignature :=
  realize kernelSignature (fun _ x t => laplaceKernel x t) (fun e => nomatch e)

def kernelRejected : Realization kernelSignature :=
  realize kernelSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev integrabilityArena : Arena where
  signature := kernelSignature
  Law R := ∀ {x : ℝ}, 0 < x → IntegrableOn (R.readout () x) (Ioi 0)

private theorem integrabilityRejected : ¬ integrabilityArena.Law kernelRejected := by
  intro h
  have hh := h (x := 1) zero_lt_one
  change Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioi 0)) at hh
  have hf := (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp hh
  have hfin := @measure_lt_top ℝ _ (volume.restrict (Ioi 0)) hf univ
  simpa using hfin

private theorem kernelDependence : ObservationalDependence kernelSignature kernelActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change laplaceKernel 1 0 ≠ laplaceKernel 1 1
  rw [show laplaceKernel 1 0 = 0 by simp [laplaceKernel]]
  apply ne_of_lt
  unfold laplaceKernel
  apply div_pos
  · apply mul_pos (Real.exp_pos _)
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _)
  · norm_num

def integrabilityFamily : Registration integrabilityArena (type_of% @integrableOn_laplaceKernel) where
  actual := kernelActual
  bridge := Iff.rfl
  variation := ⟨integrableOn_laplaceKernel, kernelRejected, integrabilityRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integrabilityArena.Law kernelActual kernelRejected integrabilityRejected
  dependence := kernelDependence

def representationAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@r_eq_laplace) (Realization logarithmSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Laplace.representationUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Laplace.representationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨representationArena⟩
  objectArena := .source ⟨representationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source representationArena ⟨representationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize logarithmSignature (fun _ _ x => -Real.log (wallisB x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Laplace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms representationAudit

def integrabilityAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrableOn_laplaceKernel) (Realization kernelSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Laplace.integrabilityUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Laplace.integrabilityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integrabilityArena⟩
  objectArena := .source ⟨integrabilityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integrabilityArena ⟨integrabilityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize kernelSignature (fun _ x t => laplaceKernel x t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Laplace
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms integrabilityAudit

end
end Reg.D5.S3.Analytic.WallisRemainder.Laplace
