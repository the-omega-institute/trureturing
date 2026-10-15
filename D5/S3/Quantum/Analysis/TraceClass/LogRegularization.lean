/- GID: D5/S3/Quantum/Analysis/TraceClass/LogRegularization
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/LogRegularization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive trace pairing and continuous bounded logarithmic regularizations on genuine trace-class references. -/

import D5.S3.Quantum.Analysis.TraceClass.Pairing
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Bounded logarithmic trace energies

The trace and trace norm are the analytic, basis-independent quantities adopted
from Tom Ole Diem's Apache-2.0 Physlib trace-class development. The logarithm and
its noncommutative monotonicity are Mathlib's real continuous functional calculus.
Only bounded regularizations occur here; no totalized logarithm at a singular
reference is interpreted as an unbounded energy.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace ENNReal

namespace QuantumLogEnergy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The inclusion uses the trace norm on its domain and the operator norm on its range. -/
def operatorCLM : TraceClass H →L[ℂ] (H →L[ℂ] H) :=
  ({ toFun := fun T => T.1
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : TraceClass H →ₗ[ℂ] (H →L[ℂ] H)).mkContinuous 1
    (fun T => by
      change ‖T.1‖ ≤ 1 * ‖T‖
      rw [one_mul, TraceClass.norm_eq_traceNorm]
      exact opNorm_le_traceNorm (TraceClass.isTraceClass_coe T))

/-- Positive trace-class operators have nonnegative real trace. -/
theorem re_trace_nonneg {T : H →L[ℂ] H} (hT : IsTraceClass T) (hpos : 0 ≤ T) :
    0 ≤ (trace T hT).re := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_eq_of_hilbertBasis hT b]
  change 0 ≤ Complex.reCLM (∑' i : w, ⟪b i, T (b i)⟫_ℂ)
  rw [Complex.reCLM.map_tsum (summable_trace_diagonal_of_isTraceClass hT b)]
  exact tsum_nonneg fun i => (T.nonneg_iff_isPositive.mp hpos).re_inner_nonneg_right (b i)

/-- Positivity of the trace pairing requires no commutation between its two arguments.
The cyclicity is applied to the trace-class product `sqrt A * rho`, not to `sqrt rho`. -/
theorem tracePairing_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) : 0 ≤ (TraceClass.tracePairing A rho).re := by
  let R : H →L[ℂ] H := CFC.sqrt A
  have hR : IsSelfAdjoint R := .of_nonneg (CFC.sqrt_nonneg A)
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA
  have hRrho : IsTraceClass (R * rho.1) := TraceClass.isTraceClass_mul_coe R rho
  have hcycle := trace_mul_cycle (A := R) hRrho
  have hconj : 0 ≤ R * rho.1 * R := by
    simpa only [hR.star_eq] using star_left_conjugate_nonneg hrho R
  have heq : R * (R * rho.1) = A * rho.1 := by rw [← mul_assoc, hRR]
  have htrace : TraceClass.tracePairing A rho =
      trace (R * rho.1 * R) (isTraceClass_mul_mul (TraceClass.isTraceClass_coe rho)) := by
    calc
      TraceClass.tracePairing A rho = trace (R * (R * rho.1))
          (isTraceClass_mul_mul (A := R) (B := 1) hRrho) :=
        TraceClass.trace_transport heq.symm _
      _ = _ := hcycle
  rw [htrace]
  exact re_trace_nonneg _ hconj

/-- Positive trace-class operators test the Loewner order, including noncommuting observables. -/
theorem tracePairing_mono {A B : H →L[ℂ] H} (hAB : A ≤ B) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) :
    (TraceClass.tracePairing A rho).re ≤ (TraceClass.tracePairing B rho).re := by
  have h := tracePairing_nonneg (sub_nonneg.mpr hAB) rho hrho
  change 0 ≤ (TraceClass.tracePairingContinuousLinearMap (B - A) rho).re at h
  rw [map_sub, sub_apply, Complex.sub_re] at h
  exact sub_nonneg.mp h

/-- On the positive cone the trace norm is the real trace. -/
theorem traceNorm_eq_re_trace {T : H →L[ℂ] H} (hT : IsTraceClass T) (hpos : 0 ≤ T) :
    traceNorm T hT = (trace T hT).re := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [traceNorm_eq_of_hilbertBasis hT b, CFC.abs_of_nonneg T hpos,
    trace_eq_of_hilbertBasis hT b]
  exact (Complex.reCLM.map_tsum (summable_trace_diagonal_of_isTraceClass hT b)).symm

/-- Normalization and positivity imply the genuine operator inequality `rho ≤ 1`. -/
theorem density_le_one (rho : TraceClass H) (hrho : 0 ≤ rho.1)
    (htrace : (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1) : rho.1 ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg rho.1 hrho).mp
  calc
    ‖rho.1‖ ≤ traceNorm rho.1 (TraceClass.isTraceClass_coe rho) :=
      opNorm_le_traceNorm (TraceClass.isTraceClass_coe rho)
    _ = 1 := (traceNorm_eq_re_trace _ hrho).trans htrace

/-- A positive trace-class contraction, with the topology induced by the genuine trace norm. -/
abbrev Reference (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  {T : TraceClass H // 0 ≤ T.1 ∧ T.1 ≤ 1}

/-- `log(1+epsilon) I - log(T+epsilon I)` is bounded even when `T` has a kernel. -/
def logRegularization (epsilon : ℝ) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  algebraMap ℝ (H →L[ℂ] H) (Real.log (1 + epsilon)) -
    CFC.log (T + algebraMap ℝ (H →L[ℂ] H) epsilon)

private theorem shift_strictlyPositive {epsilon : ℝ} (he : 0 < epsilon)
    {T : H →L[ℂ] H} (hT : 0 ≤ T) :
    IsStrictlyPositive (T + algebraMap ℝ (H →L[ℂ] H) epsilon) :=
  IsStrictlyPositive.nonneg_add hT (isStrictlyPositive_algebraMap he)

/-- The bounded regularization is positive for every positive contraction. -/
theorem logRegularization_nonneg {epsilon : ℝ} (he : 0 < epsilon)
    {T : H →L[ℂ] H} (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ logRegularization epsilon T := by
  apply sub_nonneg.mpr
  have h := CFC.log_le_log (show T + algebraMap ℝ (H →L[ℂ] H) epsilon ≤
      1 + algebraMap ℝ (H →L[ℂ] H) epsilon from add_le_add hT1 le_rfl)
    (shift_strictlyPositive he hT)
  have hid : (1 : H →L[ℂ] H) + algebraMap ℝ (H →L[ℂ] H) epsilon =
      algebraMap ℝ (H →L[ℂ] H) (1 + epsilon) := by simp only [map_add, map_one]
  rw [hid, CFC.log_algebraMap] at h
  exact h

/-- Each bounded regularization reverses the operator order without a commutativity assumption. -/
theorem logRegularization_antitone {epsilon : ℝ} (he : 0 < epsilon)
    {P Q : H →L[ℂ] H} (hP : 0 ≤ P) (hPQ : P ≤ Q) :
    logRegularization epsilon Q ≤ logRegularization epsilon P := by
  unfold logRegularization
  apply sub_le_sub_left
  exact CFC.log_le_log (add_le_add hPQ le_rfl) (shift_strictlyPositive he hP)

/-- The bounded trace energy is paired with an actual trace-class operator. -/
def regularizedEnergy (epsilon : ℝ) (T : H →L[ℂ] H) (rho : TraceClass H) : ℝ :=
  (TraceClass.tracePairing (logRegularization epsilon T) rho).re

/-- Regularized energies are nonnegative, also for singular references. -/
theorem regularizedEnergy_nonneg {epsilon : ℝ} (he : 0 < epsilon)
    (T : Reference H) (rho : TraceClass H) (hrho : 0 ≤ rho.1) :
    0 ≤ regularizedEnergy epsilon T.1.1 rho :=
  tracePairing_nonneg (logRegularization_nonneg he T.2.1 T.2.2) rho hrho

/-- Noncommuting order domination holds at every positive regularization parameter. -/
theorem regularizedEnergy_antitone {epsilon : ℝ} (he : 0 < epsilon)
    {P Q : H →L[ℂ] H} (hP : 0 ≤ P) (hPQ : P ≤ Q)
    (rho : TraceClass H) (hrho : 0 ≤ rho.1) :
    regularizedEnergy epsilon Q rho ≤ regularizedEnergy epsilon P rho :=
  tracePairing_mono (logRegularization_antitone he hP hPQ) rho hrho

/-- The observable inclusion is continuous for the genuine trace norm. -/
private theorem continuous_reference_operator : Continuous (fun T : Reference H => T.1.1) :=
  operatorCLM.continuous.comp continuous_subtype_val

/-- Fixed positive regularization is continuous in the reference's trace norm. -/
theorem continuous_regularizedEnergy {epsilon : ℝ} (he : 0 < epsilon) (rho : TraceClass H) :
    Continuous (fun T : Reference H => regularizedEnergy epsilon T.1.1 rho) := by
  have hshift : Continuous (fun T : Reference H =>
      T.1.1 + algebraMap ℝ (H →L[ℂ] H) epsilon) :=
    continuous_reference_operator.add continuous_const
  have hlog : Continuous (fun T : Reference H =>
      CFC.log (T.1.1 + algebraMap ℝ (H →L[ℂ] H) epsilon)) :=
    CFC.continuousOn_log.comp_continuous hshift fun T =>
      let h := shift_strictlyPositive he T.2.1
      ⟨h.isSelfAdjoint, h.isUnit⟩
  have hreg : Continuous (fun T : Reference H => logRegularization epsilon T.1.1) :=
    continuous_const.sub hlog
  exact Complex.continuous_re.comp
    ((TraceClass.tracePairingContinuousLinearMap.continuous.comp hreg).clm_apply continuous_const)

/-- An auxiliary operator-defined supremum. Its identification with the singular
spectral energy requires a complete spectral basis theorem. -/
def regularizedSupremum (T : Reference H) (rho : TraceClass H) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 rho)

/-- The supremum of actual regularized trace pairings is lower semicontinuous
in the reference's trace norm. This does not yet identify it with a spectral sum. -/
theorem lowerSemicontinuous_regularizedSupremum (rho : TraceClass H) :
    LowerSemicontinuous (fun T : Reference H => regularizedSupremum T rho) := by
  apply lowerSemicontinuous_iSup
  intro n
  exact (ENNReal.continuous_ofReal.comp
    (continuous_regularizedEnergy (by positivity : 0 < ((n : ℝ) + 1)⁻¹) rho)).lowerSemicontinuous

/-- The same operator-defined supremum reverses noncommuting reference order. -/
theorem regularizedSupremum_antitone (P Q : Reference H) (hPQ : P.1.1 ≤ Q.1.1)
    (rho : TraceClass H) (hrho : 0 ≤ rho.1) :
    regularizedSupremum Q rho ≤ regularizedSupremum P rho := by
  apply iSup_mono
  intro n
  exact ENNReal.ofReal_le_ofReal
    (regularizedEnergy_antitone (by positivity : 0 < ((n : ℝ) + 1)⁻¹) P.2.1 hPQ rho hrho)

#print axioms tracePairing_nonneg
#print axioms density_le_one
#print axioms continuous_regularizedEnergy
#print axioms lowerSemicontinuous_regularizedSupremum
#print axioms regularizedSupremum_antitone

end QuantumLogEnergy
