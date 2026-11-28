/- GID: D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation.exists_faithful_qutrit_two_flag_petz_fidelity_failure; premises=D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap.integer_certificate
   digest: The certified qutrit deficit dominates the complementary-flag bound. -/

import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Quantum.Recovery.GibbsOverlap.PetzIntegerQutritOverlap
import D5.S3.Quantum.Recovery.GibbsOverlap.PetzQutritSecondFlag

/-! The two-flag deficit for the qutrit from the integer overlap certificate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.GibbsOverlap.PetzQutritFirstFlag

open scoped BigOperators CStarAlgebra ComplexOrder _root_.Matrix MatrixOrder Matrix.Norms.Operator
open NormedSpace
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Recovery.GibbsOverlap.PetzIntegerQutritOverlap
  (Qutrit A B BInt A_isHermitian B_isHermitian overlap normalized_overlap_bound
    comparison_trace norm_A_le row_sum_le)
open D5.S3.Quantum.Recovery.GibbsOverlap.PetzQutritSecondFlag
open RHLinalg (trace_mul_nonneg_of_posSemidef)

local notation "mat" => CStarMatrix.ofMatrix.symm
local notation "CQ" => CStarMatrix (Fin 3) (Fin 3) ℂ
local notation "Â" => (CStarMatrix.ofMatrix A)
local notation "B̂" => (CStarMatrix.ofMatrix B)

local instance : NormedAlgebra ℚ CQ := .restrictScalars ℚ ℂ _

local instance : ContinuousFunctionalCalculus ℝ CQ IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

local instance : NonUnitalContinuousFunctionalCalculus ℝ CQ IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance : NonnegSpectrumClass ℝ CQ := CStarAlgebra.instNonnegSpectrumClass'

/-- The fixed first-flag weight in the physical qutrit example. -/
private def qutritFlagWeight : ℝ := 1 / 2 ^ (100 : ℕ)

private theorem qutrit_flag_weight_bounds :
    qutritFlagWeight * Real.exp 22 < 1 / 2 ∧
      qutritFlagWeight * Real.exp 44 < Real.exp (-14) / 3 := by
  have hExp (k : ℕ) : Real.exp (k : ℝ) ≤ (3 : ℝ) ^ k := by
    rw [show Real.exp (k : ℝ) = Real.exp 1 ^ k by
      rw [← Real.exp_nat_mul, mul_one]]
    exact pow_le_pow_left₀ (Real.exp_nonneg 1) Real.exp_one_lt_three.le k
  have hε : 0 ≤ qutritFlagWeight := by norm_num [qutritFlagWeight]
  constructor
  · calc
      qutritFlagWeight * Real.exp 22 ≤ qutritFlagWeight * (3 : ℝ) ^ 22 :=
        mul_le_mul_of_nonneg_left (hExp 22) hε
      _ < 1 / 2 := by norm_num [qutritFlagWeight]
  · have h58 : qutritFlagWeight * Real.exp 58 < 1 / 3 :=
      (mul_le_mul_of_nonneg_left (hExp 58) hε).trans_lt (by norm_num [qutritFlagWeight])
    calc
      qutritFlagWeight * Real.exp 44 =
          (qutritFlagWeight * Real.exp 58) * Real.exp (-14) := by
        rw [mul_assoc, ← Real.exp_add]
        norm_num
      _ < (1 / 3) * Real.exp (-14) := mul_lt_mul_of_pos_right h58 (Real.exp_pos _)
      _ = Real.exp (-14) / 3 := by ring

/-- Numerical closure of the two-flag comparison. Here `N` is the qutrit partition
function and `t` is the trace of `Q * M²`. The first-flag input is the quantitative
gap from the integer certificate and the second-flag input is the Hölder bound. -/
private theorem qutrit_flag_deficits_lt_zero {N t f₁ f₂ : ℝ}
    (hN : 0 < N) (hNupper : N ≤ 3 * Real.exp 32) (ht : t ≤ Real.exp 44)
    (hf₁ : f₁ < -(qutritFlagWeight / 2 * (Real.exp 18 / N)))
    (hf₂ : f₂ ≤ qutritFlagWeight ^ 2 * t / 2) :
    f₁ + f₂ < 0 := by
  have hratio : Real.exp (-14) / 3 ≤ Real.exp 18 / N := by
    apply (le_div_iff₀ hN).2
    calc
      Real.exp (-14) / 3 * N ≤ Real.exp (-14) / 3 * (3 * Real.exp 32) :=
        mul_le_mul_of_nonneg_left hNupper (by positivity)
      _ = Real.exp (-14) * Real.exp 32 := by ring
      _ = Real.exp 18 := by rw [← Real.exp_add]; norm_num
  have hsecond : f₂ ≤ qutritFlagWeight ^ 2 * Real.exp 44 / 2 :=
    hf₂.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (sq_nonneg _))
      (by norm_num))
  have hgap := mul_lt_mul_of_pos_left (qutrit_flag_weight_bounds.2.trans_le hratio)
    (show 0 < qutritFlagWeight / 2 by norm_num [qutritFlagWeight])
  have he : qutritFlagWeight / 2 * (qutritFlagWeight * Real.exp 44) =
      qutritFlagWeight ^ 2 * Real.exp 44 / 2 := by ring
  rw [he] at hgap
  linarith only [hf₁, hsecond, hgap]

local notation "ε" => qutritFlagWeight

private theorem weight_pos : 0 < ε := by norm_num [qutritFlagWeight]

private theorem a_selfAdjoint : IsSelfAdjoint Â :=
  congrArg CStarMatrix.ofMatrix A_isHermitian.isSelfAdjoint.star_eq

private theorem b_selfAdjoint : IsSelfAdjoint B̂ :=
  congrArg CStarMatrix.ofMatrix B_isHermitian.isSelfAdjoint.star_eq

private def H : CQ := (2 : ℝ) • Â

private def J : CQ := (2 : ℝ) • B̂

private theorem H_selfAdjoint : IsSelfAdjoint H := (IsSelfAdjoint.all (2 : ℝ)).smul a_selfAdjoint

private theorem J_selfAdjoint : IsSelfAdjoint J := (IsSelfAdjoint.all (2 : ℝ)).smul b_selfAdjoint

private def M : CQ := exp H

private def N : ℝ := partitionFunction J

def Q : DensityState (Fin 3) := gibbsState J J_selfAdjoint

def D₁ : CQ := ε • M

def D₂ : CQ := 1 - D₁

theorem effects_sum : D₁ + D₂ = 1 := by
  rw [D₂]
  abel

def L₁ : CQ := CFC.log Q.1 + CFC.log D₁

def L₂ : CQ := CFC.log Q.1 + CFC.log D₂

private theorem N_pos : 0 < N := partition_function_pos J J_selfAdjoint

theorem Q_posDef : (mat Q.1).PosDef := gibbs_state_posDef J J_selfAdjoint

theorem mat_exp (X : CQ) : mat (exp X) = exp (mat X) :=
  NormedSpace.map_exp CStarMatrix.ofMatrixStarAlgEquiv.symm CStarMatrix.ofMatrixL.symm.continuous X

private theorem exp_add_real_shift (X : CQ) (c : ℝ) :
    exp (X + c • (1 : CQ)) = Real.exp c • exp X := by
  apply CStarMatrix.ofMatrix.symm.injective
  rw [mat_exp]
  change exp (mat X + c • (1 : Qutrit ℂ)) = Real.exp c • mat (exp X)
  simpa only [mat_exp, Complex.coe_smul] using
    PetzIntegerQutritOverlap.exp_add_scalar (mat X) c

theorem D1_strictlyPositive : IsStrictlyPositive D₁ :=
  IsStrictlyPositive.smul weight_pos ((isUnit_exp H).isStrictlyPositive H_selfAdjoint.exp_nonneg)

private theorem log_first_effect : CFC.log D₁ = H + Real.log ε • (1 : CQ) := by
  change CFC.log (ε • exp H) = _
  erw [CFC.log_smul' (A := CQ) (exp H) weight_pos
    ((isUnit_exp H).isStrictlyPositive H_selfAdjoint.exp_nonneg), CFC.log_exp H H_selfAdjoint,
    Algebra.algebraMap_eq_smul_one, add_comm]
  rfl

private theorem log_qutrit_state : CFC.log Q.1 = J - Real.log N • (1 : CQ) :=
  log_gibbs_state J J_selfAdjoint

private theorem exp_first_flag : exp L₁ = (ε / N) • exp ((2 : ℝ) • (Â + B̂)) := by
  have hL : L₁ = (2 : ℝ) • (Â + B̂) + (Real.log ε - Real.log N) • (1 : CQ) := by
    rw [L₁, log_qutrit_state, log_first_effect, sub_smul, smul_add, H, J]
    abel
  rw [hL, exp_add_real_shift, Real.exp_sub, Real.exp_log weight_pos, Real.exp_log N_pos]

private theorem sqrt_scaled_exp_double (X : CQ) (hX : IsSelfAdjoint X) {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • exp ((2 : ℝ) • X)) = Real.sqrt c • exp X := by
  apply CFC.sqrt_unique ?_ (smul_nonneg (Real.sqrt_nonneg c) hX.exp_nonneg)
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_two (Real.sqrt c), Real.sq_sqrt hc,
    two_smul, exp_add_of_commute (Commute.refl X)]

private theorem sqrt_first_effect : CFC.sqrt D₁ = Real.sqrt ε • exp Â :=
  sqrt_scaled_exp_double Â a_selfAdjoint weight_pos.le

private theorem sqrt_qutrit_state : CFC.sqrt Q.1 = Real.sqrt (N⁻¹) • exp B̂ :=
  sqrt_scaled_exp_double B̂ b_selfAdjoint (inv_nonneg.mpr N_pos.le)

private theorem sqrt_first_gibbs : CFC.sqrt (exp L₁) = Real.sqrt (ε / N) • exp (Â + B̂) := by
  rw [exp_first_flag]
  exact sqrt_scaled_exp_double (Â + B̂) (a_selfAdjoint.add b_selfAdjoint)
    (div_nonneg weight_pos.le N_pos.le)

private theorem first_flag_word :
    mat (CFC.sqrt (exp L₁) * CFC.sqrt D₁ * CFC.sqrt Q.1) =
      (ε / N) • (exp (A + B) * exp A * exp B) := by
  rw [sqrt_first_gibbs, sqrt_first_effect, sqrt_qutrit_state]
  change (Real.sqrt (ε / N) • mat (exp (Â + B̂))) * (Real.sqrt ε • mat (exp Â)) *
    (Real.sqrt (N⁻¹) • mat (exp B̂)) = _
  simp only [mat_exp]
  change (Real.sqrt (ε / N) • exp (A + B)) * (Real.sqrt ε • exp A) *
    (Real.sqrt (N⁻¹) • exp B) = _
  have hpair : (Real.sqrt (ε / N) • exp (A + B)) * (Real.sqrt ε • exp A) =
      (Real.sqrt (ε / N) * Real.sqrt ε) • (exp (A + B) * exp A) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hscale : Real.sqrt (ε / N) * Real.sqrt ε * Real.sqrt (N⁻¹) = ε / N := by
    calc
      _ = (Real.sqrt ε) ^ 2 * (Real.sqrt (N⁻¹)) ^ 2 := by
        rw [div_eq_mul_inv, Real.sqrt_mul weight_pos.le]
        ring
      _ = _ := by rw [Real.sq_sqrt weight_pos.le, Real.sq_sqrt (inv_nonneg.mpr N_pos.le),
        div_eq_mul_inv]
  rw [hpair, smul_mul_assoc, mul_smul_comm, smul_smul, hscale]

private theorem first_flag_partition :
    partitionFunction L₁ = (ε / N) * (exp ((2 : ℝ) • (A + B))).trace.re := by
  rw [partitionFunction, exp_first_flag]
  change ((ε / N) • mat (exp ((2 : ℝ) • (Â + B̂)))).trace.re = _
  simp only [mat_exp, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  rfl

private theorem comparison_trace_ge :
    Real.exp 18 ≤ (exp ((2 : ℝ) • (A + B))).trace.re := by
  rw [← Complex.coe_smul, Complex.ofReal_ofNat, comparison_trace]
  linarith only [Real.exp_nonneg (-14), Real.exp_nonneg 2]

private theorem b_entry (i j : Fin 3) : B i j = (BInt i j : ℂ) := rfl

private theorem integer_word_lt_half :
    traceNorm (exp (A + B) * exp A * exp B) < Real.exp 18 / 2 := by
  have h := normalized_overlap_bound
  rw [overlap] at h
  rw [traceNorm_smul_nonneg _ _ (Real.exp_nonneg _)] at h
  apply (mul_lt_mul_iff_right₀ (Real.exp_pos (-18))).mp
  have hscalar : (Real.exp 18 / 2) * Real.exp (-18) = 1 / 2 := by
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    norm_num
  rw [mul_comm (Real.exp (-18)) (Real.exp 18 / 2), hscalar]
  exact h.trans_lt (by norm_num)

private theorem first_flag_gap :
    traceNorm (mat (CFC.sqrt (exp L₁) * CFC.sqrt D₁ * CFC.sqrt Q.1)) -
      partitionFunction L₁ < -(ε / 2 * (Real.exp 18 / N)) := by
  rw [first_flag_word, first_flag_partition]
  have hscaled := traceNorm_smul_nonneg (exp (A + B) * exp A * exp B) (ε / N)
    (div_nonneg weight_pos.le N_pos.le)
  rw [Complex.coe_smul] at hscaled
  rw [hscaled]
  have hnorm := mul_lt_mul_of_pos_left integer_word_lt_half (div_pos weight_pos N_pos)
  have htrace := mul_le_mul_of_nonneg_left comparison_trace_ge (div_nonneg weight_pos.le N_pos.le)
  have hscale : (ε / N) * (Real.exp 18 / 2) = ε / 2 * (Real.exp 18 / N) := by ring
  have hfull : (ε / N) * Real.exp 18 = 2 * (ε / 2 * (Real.exp 18 / N)) := by ring
  rw [hscale] at hnorm
  rw [hfull] at htrace
  calc
    _ < ε / 2 * (Real.exp 18 / N) - (ε / N) * (exp ((2 : ℝ) • (A + B))).trace.re :=
      sub_lt_sub_right hnorm _
    _ ≤ ε / 2 * (Real.exp 18 / N) - 2 * (ε / 2 * (Real.exp 18 / N)) :=
      sub_le_sub_left htrace _
    _ = _ := by ring

private theorem b_row_norm : ‖B‖ ≤ 16 := by
  refine row_sum_le (by norm_num) fun i => ?_
  fin_cases i <;> norm_num [b_entry, BInt, Fin.sum_univ_three, Complex.norm_intCast]

private theorem exp_le_scalar (X : CQ) (hX : IsSelfAdjoint X) {r : ℝ} (hr : ‖mat X‖ ≤ r) :
    exp X ≤ algebraMap ℝ CQ (Real.exp r) := by
  rw [← CFC.real_exp_eq_normedSpace_exp hX]
  apply (cfc_le_algebraMap_iff Real.exp (Real.exp r) X Real.continuous_exp.continuousOn hX).2
  intro x hx
  let e := (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin 3) (A := ℂ)).symm.toAlgEquiv
    |>.restrictScalars ℝ
  have hx' : x ∈ spectrum ℝ (mat X) := by
    change x ∈ spectrum ℝ (e X)
    rwa [AlgEquiv.spectrum_eq e X]
  exact Real.exp_le_exp.mpr
    ((Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx').trans hr))

private theorem mat_smul_norm_le {X : CQ} {r : ℝ} (h : ‖mat X‖ ≤ r) {c : ℝ} (hc : 0 ≤ c) :
    ‖mat (c • X)‖ ≤ c * r := by
  change ‖c • mat X‖ ≤ c * r
  rw [norm_smul, Real.norm_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left h hc

private theorem H_row_norm : ‖mat H‖ ≤ 22 := by
  simpa only [H, show (2 : ℝ) * 11 = 22 by norm_num] using
    (mat_smul_norm_le (X := Â) norm_A_le (show (0 : ℝ) ≤ 2 by norm_num))

private theorem M_le : M ≤ algebraMap ℝ CQ (Real.exp 22) :=
  exp_le_scalar H H_selfAdjoint H_row_norm

private theorem D₁_le_half : D₁ ≤ algebraMap ℝ CQ (1 / 2) := by
  unfold D₁
  calc
    ε • M ≤ ε • algebraMap ℝ CQ (Real.exp 22) :=
      smul_le_smul_of_nonneg_left M_le weight_pos.le
    _ = algebraMap ℝ CQ (ε * Real.exp 22) := by
      simp only [Algebra.algebraMap_eq_smul_one, smul_smul]
    _ ≤ _ := algebraMap_mono CQ qutrit_flag_weight_bounds.1.le

theorem D2_strictlyPositive : IsStrictlyPositive D₂ := by
  have hone : IsStrictlyPositive (1 : CQ) := isUnit_one.isStrictlyPositive zero_le_one
  have hhalf : IsStrictlyPositive (algebraMap ℝ CQ (1 / 2)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact IsStrictlyPositive.smul (by norm_num) hone
  apply hhalf.of_le
  have hid : (1 : CQ) - algebraMap ℝ CQ (1 / 2) = algebraMap ℝ CQ (1 / 2) := by
    rw [← map_one (algebraMap ℝ CQ), ← map_sub]
    norm_num
  rw [← hid, D₂]
  exact sub_le_sub_left D₁_le_half 1

private theorem mat_sub_posSemidef {X Y : CQ} (h : X ≤ Y) : (mat Y - mat X).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (sub_nonneg.mpr h))

private theorem N_le : N ≤ 3 * Real.exp 32 := by
  have hJ : ‖mat J‖ ≤ 32 := by
    simpa only [J, show (2 : ℝ) * 16 = 32 by norm_num] using
      (mat_smul_norm_le (X := B̂) b_row_norm (show (0 : ℝ) ≤ 2 by norm_num))
  have hdiff := mat_sub_posSemidef (exp_le_scalar J J_selfAdjoint hJ)
  have h := (Complex.nonneg_iff.mp hdiff.trace_nonneg).1
  rw [Algebra.algebraMap_eq_smul_one] at h
  change 0 ≤ (Real.exp 32 • (1 : Qutrit ℂ) - mat (exp J)).trace.re at h
  rw [Matrix.trace_sub, Complex.sub_re, Matrix.trace_smul, Complex.smul_re, Matrix.trace_one] at h
  have h' : 0 ≤ Real.exp 32 * 3 - N := by simpa [N, partitionFunction, smul_eq_mul] using h
  simpa only [mul_comm 3 (Real.exp 32)] using (sub_nonneg.mp h')

private theorem M_sq_le : M ^ 2 ≤ algebraMap ℝ CQ (Real.exp 44) := by
  have hs : exp ((2 : ℝ) • H) = M ^ 2 := by
    rw [M, two_smul, exp_add_of_commute (Commute.refl H), pow_two]
  rw [← hs]
  apply exp_le_scalar _ ((IsSelfAdjoint.all (2 : ℝ)).smul H_selfAdjoint)
  simpa only [show (2 : ℝ) * 22 = 44 by norm_num] using
    (mat_smul_norm_le H_row_norm (show (0 : ℝ) ≤ 2 by norm_num))

private theorem weighted_square_trace_le : (mat (Q.1 * M ^ 2)).trace.re ≤ Real.exp 44 := by
  have h : 0 ≤ (mat Q.1 * mat (algebraMap ℝ CQ (Real.exp 44) - M ^ 2)).trace.re :=
    trace_mul_nonneg_of_posSemidef Q_posDef.posSemidef (mat_sub_posSemidef M_sq_le)
  rw [Algebra.algebraMap_eq_smul_one] at h
  change 0 ≤ (mat Q.1 * (Real.exp 44 • (1 : Qutrit ℂ) - mat (M ^ 2))).trace.re at h
  rw [Matrix.mul_sub, mul_smul_comm, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    show (mat Q.1).trace = 1 from Q.2.2] at h
  simp only [Complex.sub_re, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] at h
  exact sub_nonneg.mp h

/-- For these explicit effects the sum of the two ordinary overlap numerators is
strictly below the sum of the unnormalized Gibbs traces. -/
theorem two_flag_overlap_lt_partition :
    traceNorm (mat (CFC.sqrt (exp L₁) * CFC.sqrt D₁ * CFC.sqrt Q.1)) +
      traceNorm (mat (CFC.sqrt (exp L₂) * CFC.sqrt D₂ * CFC.sqrt Q.1)) <
        partitionFunction L₁ + partitionFunction L₂ := by
  have h₂ := second_flag_traceNorm_sub_le Q Q_posDef ε M D1_strictlyPositive.nonneg D₁_le_half
  change traceNorm (mat (CFC.sqrt (exp L₂) * CFC.sqrt D₂ * CFC.sqrt Q.1)) -
    partitionFunction L₂ ≤ ε ^ 2 * (mat (Q.1 * M ^ 2)).trace.re / 2 at h₂
  have hsum := qutrit_flag_deficits_lt_zero N_pos N_le weighted_square_trace_le first_flag_gap h₂
  linarith only [hsum]

end D5.S3.Quantum.Recovery.GibbsOverlap.PetzQutritFirstFlag
