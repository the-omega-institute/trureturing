import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.ActualThetaTailLaplace
import Reg.Support.SingleDependentReadout

/-! The complete actual source law with its zero-frequency theta observation. -/

namespace Reg.D5.S3.Weil.Mertens.ActualThetaTailLaplace

open Set MeasureTheory Filter
open scoped Topology
open _root_.D5.S3.Weil.Mertens.ActualThetaTailLaplace
open _root_.D5.S3.Weil.Mertens.ThetaLaplaceContinuation (q Q)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ => q) (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := IntegrableOn (R.readout () ()) (Ioi u₀) ∧ IntegrableOn k (Ioi u₀) ∧
    (∀ U : ℝ, u₀ ≤ U → IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) *
      _root_.D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity t) (Ioi (Real.exp U))) ∧
    (∀ u : ℝ, f u = F (Real.exp u)) ∧
    IntegrableOn f (Ioi u₀) ∧
    (∀ u : ℝ, u₀ ≤ u → ‖f u‖ ≤ ∫ v in Ioi u₀, ‖k v‖) ∧
    Tendsto f atTop (𝓝 0) ∧
    (∀ a b : ℝ, u₀ ≤ a → a ≤ b → AbsolutelyContinuousOnInterval f a b) ∧
    (∀ᵐ u ∂volume.restrict (Ioi u₀), HasDerivAt f (k u) u ∧
      u ^ 2 * deriv f u = (u + 1) * q u) ∧
    (∀ U : ℝ, u₀ ≤ U → AnalyticOnNhd ℂ (L U) {s | 0 < s.re} ∧
      ∀ s : ℂ, 0 < s.re →
        (∀ n : ℕ, IntegrableOn (fun u : ℝ =>
          (u : ℂ) ^ n * Complex.exp (-s * (u : ℂ)) * (f u : ℂ)) (Ioi U)) ∧
        HasDerivAt (L U)
          (-(∫ u in Ioi U, (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (f u : ℂ))) s ∧
        HasDerivAt (deriv (L U))
          (∫ u in Ioi U, (u : ℂ) ^ 2 * Complex.exp (-s * (u : ℂ)) * (f u : ℂ)) s ∧
        s * deriv (deriv (L U)) s + 2 * deriv (L U) s =
          -deriv (Q U) s + Q U s +
            (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-s * (U : ℂ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi u₀) := h.1
  simpa [integrableOn_const_iff, Real.volume_Ioi] using hi

def family : Registration arena (type_of% actual_theta_tail_laplace_ode) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_theta_tail_laplace_ode, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), Real.log 2, ?_⟩
    change q 0 ≠ q (Real.log 2)
    have h0 : q 0 = -1 := by simp [q]
    have h2 : q (Real.log 2) = (Chebyshev.theta 2 - 2) / 2 := by
      rw [q, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    rw [h0, h2]
    have ht := Chebyshev.theta_pos (x := (2 : ℝ)) le_rfl
    linarith

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_theta_tail_laplace_ode) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.ActualThetaTailLaplace.actual_theta_tail_laplace_ode.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.ActualThetaTailLaplace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.ActualThetaTailLaplace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end
end Reg.D5.S3.Weil.Mertens.ActualThetaTailLaplace
