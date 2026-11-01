/- GID: D5/S3/Quantum/Analysis/TraceClass/PowerSeries
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/PowerSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Noncommuting trace power errors and absolutely convergent trace logarithms. -/


import D5.S3.Quantum.Analysis.TraceClass.Pairing
import Mathlib.Analysis.SpecificLimits.Normed

/-! Trace powers use the genuine unconditional trace, with the Physlib ideal suppliers. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open Filter Topology

namespace TraceClassPowerSeries
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def leftMul (A : H →L[ℂ] H) (T : TraceClass H) : TraceClass H :=
  TraceClass.ofOperator (A * T.val) (TraceClass.isTraceClass_mul_coe A T)

private def rightMul (T : TraceClass H) (A : H →L[ℂ] H) : TraceClass H :=
  TraceClass.ofOperator (T.val * A) (by
    simpa using isTraceClass_mul_mul (A := 1) (B := A) T.property)

private theorem leftMul_norm (A : H →L[ℂ] H) (T : TraceClass H) :
    ‖leftMul A T‖ ≤ ‖A‖ * ‖T‖ := by
  have h := traceNorm_mul_mul_le (A := A) (B := 1) T.property
    (TraceClass.isTraceClass_mul_coe A T)
  change traceNorm (A * T.val) _ ≤ ‖A‖ * traceNorm T.val _
  calc
    _ ≤ ‖A‖ * traceNorm T.val T.property * ‖(1 : H →L[ℂ] H)‖ := by simpa using h
    _ ≤ ‖A‖ * traceNorm T.val T.property * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
        (mul_nonneg (norm_nonneg _) (traceNorm_nonneg _ _))
    _ = _ := mul_one _

private theorem rightMul_norm (T : TraceClass H) (A : H →L[ℂ] H) :
    ‖rightMul T A‖ ≤ ‖T‖ * ‖A‖ := by
  have h := traceNorm_mul_mul_le (A := (1 : H →L[ℂ] H)) (B := A) T.property
    (rightMul T A).property
  change traceNorm (T.val * A) _ ≤ traceNorm T.val _ * ‖A‖
  calc
    _ ≤ ‖(1 : H →L[ℂ] H)‖ * traceNorm T.val T.property * ‖A‖ := by simpa using h
    _ ≤ 1 * traceNorm T.val T.property * ‖A‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (show ‖(1 : H →L[ℂ] H)‖ ≤ 1 from ContinuousLinearMap.norm_id_le)
          (traceNorm_nonneg _ _)) (norm_nonneg _)
    _ = _ := by ring

/-- Positive powers are trace class; the zeroth power is never assumed trace class. -/
def positivePower (T : TraceClass H) (m : ℕ) : TraceClass H :=
  leftMul (T.val ^ m) T

private theorem positivePower_coe (T : TraceClass H) (m : ℕ) :
    (positivePower T m).val = T.val ^ (m + 1) := by
  exact (pow_succ T.val m).symm

private theorem op_power_le (T : H →L[ℂ] H) {q : ℝ}
    (hq : 0 ≤ q) (hT : ‖T‖ ≤ q) (m : ℕ) : ‖T ^ m‖ ≤ q ^ m := by
  cases m with
  | zero =>
      change ‖(1 : H →L[ℂ] H)‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
  | succ m => exact (norm_pow_le' T (Nat.succ_pos m)).trans (pow_le_pow_left₀ (norm_nonneg _) hT _)

/-- The original trace of T^(m+1), rather than a finite-cutoff definition. -/
def powerTrace (T : TraceClass H) (m : ℕ) : ℂ :=
  trace (positivePower T m).val (positivePower T m).property

private theorem trace_carrier (T : TraceClass H) :
    TraceClass.tracePairing (1 : H →L[ℂ] H) T = trace T.val T.property := by
  simpa only [TraceClass.tracePairing_apply, one_mul]

private theorem power_norm_le (T : TraceClass H) {q : ℝ}
    (hq : 0 ≤ q) (hT : ‖T.val‖ ≤ q) (m : ℕ) :
    ‖positivePower T m‖ ≤ q ^ m * ‖T‖ :=
  (leftMul_norm _ _).trans
    (mul_le_mul_of_nonneg_right (op_power_le _ hq hT m) (norm_nonneg _))

/-- Inductive noncommuting telescoping in the actual trace-class carrier. -/
theorem power_error_le (T S : TraceClass H) {q : ℝ}
    (hq : 0 ≤ q) (hT : ‖T.val‖ ≤ q) (hS : ‖S.val‖ ≤ q) (m : ℕ) :
    ‖positivePower T m - positivePower S m‖ ≤
      (m + 1 : ℝ) * q ^ m * ‖T - S‖ := by
  induction m with
  | zero =>
      have h (X : TraceClass H) : positivePower X 0 = X :=
        Subtype.ext (by simp [positivePower_coe])
      simp only [h, Nat.cast_zero, zero_add, pow_zero, one_mul]
      exact le_rfl
  | succ m ih =>
      have he : positivePower T (m + 1) - positivePower S (m + 1) =
          leftMul (T.val ^ (m + 1)) (T - S) +
            rightMul (positivePower T m - positivePower S m) S.val := by
        apply Subtype.ext
        change T.val ^ (m + 1) * T.val - S.val ^ (m + 1) * S.val =
          T.val ^ (m + 1) * (T.val - S.val) +
            ((positivePower T m).val - (positivePower S m).val) * S.val
        rw [positivePower_coe, positivePower_coe]
        noncomm_ring
      rw [he]
      calc
        _ ≤ ‖leftMul (T.val ^ (m + 1)) (T - S)‖ +
            ‖rightMul (positivePower T m - positivePower S m) S.val‖ := norm_add_le _ _
        _ ≤ q ^ (m + 1) * ‖T - S‖ +
            ((m + 1 : ℝ) * q ^ m * ‖T - S‖) * q := by
          apply add_le_add
          · exact (leftMul_norm _ _).trans
              (mul_le_mul_of_nonneg_right (op_power_le _ hq hT _) (norm_nonneg _))
          · exact (rightMul_norm _ _).trans
              (mul_le_mul ih hS (norm_nonneg _) (by positivity))
        _ = _ := by push_cast; rw [pow_succ]; ring

/-- Trace differences inherit the noncommuting power error, without division by q. -/
theorem powerTrace_error_le (T S : TraceClass H) {q : ℝ}
    (hq : 0 ≤ q) (hT : ‖T.val‖ ≤ q) (hS : ‖S.val‖ ≤ q) (m : ℕ) :
    ‖powerTrace T m - powerTrace S m‖ ≤
      (m + 1 : ℝ) * q ^ m * ‖T - S‖ := by
  have he : powerTrace T m - powerTrace S m =
      TraceClass.tracePairing (1 : H →L[ℂ] H)
        (positivePower T m - positivePower S m) := by
    simp only [map_sub, trace_carrier, powerTrace]
  rw [he]
  exact ((TraceClass.tracePairing _).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right
      ((TraceClass.norm_tracePairing_le _).trans ContinuousLinearMap.norm_id_le)
      (norm_nonneg _)).trans (by simpa using power_error_le T S hq hT hS m))

private theorem powerTrace_norm_le (T : TraceClass H) {q : ℝ}
    (hq : 0 ≤ q) (hT : ‖T.val‖ ≤ q) (m : ℕ) :
    ‖powerTrace T m‖ ≤ ‖T‖ * q ^ m := by
  exact (TraceClass.norm_trace_le _).trans ((power_norm_le T hq hT m).trans_eq (mul_comm _ _))

/-- The absolutely convergent trace logarithm series, at positive powers only. -/
def logTerm (T : TraceClass H) (m : ℕ) : ℂ := powerTrace T m / (2 * (m + 1 : ℂ))

/-- The trace logarithm uses the original operator's trace at every power. -/
def traceLog (T : TraceClass H) : ℂ := ∑' m, logTerm T m

private theorem logDenom_norm (m : ℕ) :
    ‖(2 : ℂ) * (m + 1 : ℂ)‖ = 2 * (m + 1 : ℝ) := by
  have hm : (m + 1 : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [hm, norm_mul, Complex.norm_natCast]
  norm_num

private theorem logTerm_norm_le (T : TraceClass H) {q : ℝ}
    (hq : 0 ≤ q) (hT : ‖T.val‖ ≤ q) (m : ℕ) :
    ‖logTerm T m‖ ≤ (‖T‖ / 2) * q ^ m := by
  have hm : (1 : ℝ) ≤ m + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  simp only [logTerm, norm_div, logDenom_norm]
  calc
    _ ≤ (‖T‖ * q ^ m) / (2 * (m + 1 : ℝ)) := by
      gcongr
      exact powerTrace_norm_le T hq hT m
    _ ≤ (‖T‖ * q ^ m) / 2 :=
      div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (pow_nonneg hq _))
        (by norm_num) (by linarith)
    _ = _ := by ring

/-- Absolute convergence for every trace-class strict contraction. -/
theorem logTerm_norm_summable (T : TraceClass H) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hT : ‖T.val‖ ≤ q) :
    Summable (fun m => ‖logTerm T m‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (logTerm_norm_le T hq hT)
    ((summable_geometric_of_lt_one hq hq1).mul_left (‖T‖ / 2))

private theorem logTerm_error_le (T S : TraceClass H) {q : ℝ}
    (hq : 0 ≤ q) (hT : ‖T.val‖ ≤ q) (hS : ‖S.val‖ ≤ q) (m : ℕ) :
    ‖logTerm T m - logTerm S m‖ ≤ (‖T - S‖ / 2) * q ^ m := by
  rw [logTerm, logTerm, ← sub_div, norm_div]
  have hm : (0 : ℝ) < m + 1 := by positivity
  rw [logDenom_norm]
  apply (div_le_div_of_nonneg_right (powerTrace_error_le T S hq hT hS m) (by positivity)).trans_eq
  field_simp
  <;> ring

/-- Quantitative absolute trace-log continuity on the closed q contraction ball. -/
theorem traceLog_error_le (T S : TraceClass H) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hT : ‖T.val‖ ≤ q) (hS : ‖S.val‖ ≤ q) :
    ‖traceLog T - traceLog S‖ ≤ ‖T - S‖ / (2 * (1 - q)) := by
  have htn := logTerm_norm_summable T hq hq1 hT
  have hsn := logTerm_norm_summable S hq hq1 hS
  have hg := (summable_geometric_of_lt_one hq hq1).mul_left (‖T - S‖ / 2)
  have hdn := Summable.of_nonneg_of_le (fun m => norm_nonneg (logTerm T m - logTerm S m))
    (logTerm_error_le T S hq hT hS) hg
  rw [traceLog, traceLog, ← htn.of_norm.tsum_sub hsn.of_norm]
  calc
    _ ≤ ∑' m, ‖logTerm T m - logTerm S m‖ := norm_tsum_le_tsum_norm hdn
    _ ≤ ∑' m, (‖T - S‖ / 2) * q ^ m :=
      hdn.tsum_le_tsum (logTerm_error_le T S hq hT hS) hg
    _ = ‖T - S‖ / (2 * (1 - q)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1]
      field_simp
      <;> ring

end TraceClassPowerSeries
