import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ThetaTailRobinWitness
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Robin.ThetaTailRobinWitness
open Set MeasureTheory Real
open _root_.D5.S3.Arith.Robin
open _root_.D5.S3.Arith.Robin.ThetaTailRobinWitness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

private abbrev kernel (t : ℝ) :=
  (Chebyshev.theta t - t) * ActualRobinClockCovariance.activationDensity t

def actual : Realization signature := realize signature (fun _ _ => kernel) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ t => kernel t + 1 / t ^ 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ), 2 ≤ x →
    IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) *
      ActualRobinClockCovariance.activationDensity t) (Ioi x) ∧
    -(∫ t in Ioi x, R.readout () () t) =
      Mertens.E₂p x - (Chebyshev.theta x - x) / (x * log x) ∧
    (10000 ≤ x → 7 / sqrt x < -(∫ t in Ioi x, (Chebyshev.theta t - t) *
      ActualRobinClockCovariance.activationDensity t) →
      let D := Nat.lcmUpto ⌊x⌋₊
      PrimeFiberPropagation.divisorRatio D > exp eulerMascheroniConstant * log (log D) ∧
        5040 < D ∧ log D = Chebyshev.psi x ∧ (D : ℝ) ≤ exp (x * log x))

private theorem reciprocal_square_integrable :
    IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi (2 : ℝ)) := by
  simpa only [Real.rpow_neg, Real.rpow_two, one_div] using
    (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num : (0 : ℝ) < 2))

private theorem reciprocal_square_integral :
    (∫ t in Ioi (2 : ℝ), 1 / t ^ 2) = 1 / 2 := by
  have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num : (0 : ℝ) < 2)
  norm_num [Real.rpow_neg, Real.rpow_two, one_div] at h ⊢
  exact h

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hactual := theta_tail_mertens_robin 2 le_rfl
  have heq := (h 2 le_rfl).2.1
  change -(∫ t in Ioi (2 : ℝ), kernel t + 1 / t ^ 2) =
    Mertens.E₂p 2 - (Chebyshev.theta 2 - 2) / (2 * log 2) at heq
  rw [integral_add hactual.1 reciprocal_square_integrable, reciprocal_square_integral] at heq
  have hidentity : -(∫ t in Ioi (2 : ℝ), kernel t) =
      Mertens.E₂p 2 - (Chebyshev.theta 2 - 2) / (2 * log 2) := hactual.2.1
  linarith

private theorem actual_dependence : kernel (9 / 4) ≠ kernel 16 := by
  have hlog2 : log 2 < 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hl : 0 < log (9 / 4 : ℝ) := log_pos (by norm_num)
  have hlt : log (9 / 4 : ℝ) < 1 := by
    rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, log_pow]
    have h := log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
      (by norm_num : (3 / 2 : ℝ) ≠ 1)
    linarith
  have htheta : Chebyshev.theta (9 / 4) = log 2 := by
    norm_num [Chebyshev.theta, show Finset.Ioc 0 2 = {1, 2} by decide, Finset.sum_filter]
  have hleft : kernel (9 / 4) < -1 / 4 := by
    unfold kernel ActualRobinClockCovariance.activationDensity
    rw [htheta, ← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < (9 / 4 : ℝ) ^ 2 * log (9 / 4 : ℝ) ^ 2)).mpr
    have hm := mul_neg_of_neg_of_pos (sub_neg.mpr hlog2) (by linarith : 0 < log (9 / 4 : ℝ) + 1)
    have hs := mul_pos hl (sub_pos.mpr hlt)
    nlinarith
  have hl16 : 2 < log (16 : ℝ) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]
    linarith [Real.log_two_gt_d9]
  have hright : -1 / 4 < kernel 16 := by
    unfold kernel ActualRobinClockCovariance.activationDensity
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ (by positivity : 0 < (16 : ℝ) ^ 2 * log (16 : ℝ) ^ 2)).mpr
    have hm := mul_nonneg (Chebyshev.theta_nonneg 16)
      (by linarith : 0 ≤ log (16 : ℝ) + 1)
    nlinarith [sq_nonneg (log (16 : ℝ) - 2)]
  linarith

def family : Registration arena (type_of% (@theta_tail_mertens_robin)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨theta_tail_mertens_robin, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 9 / 4, 16, ?_⟩
    exact actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@theta_tail_mertens_robin) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.ThetaTailRobinWitness.theta_tail_mertens_robin.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.ThetaTailRobinWitness.family
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
    owner := `D5.S3.Arith.Robin.ThetaTailRobinWitness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
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
end Reg.D5.S3.Arith.Robin.ThetaTailRobinWitness
