/- GID: D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation
   generality: I
   mirror-B: D5/B/S3/Estimation/TransmissivityBetaPriorProbeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.claim; result=D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.result; claim=D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.claim
   digest: Refute phased in-between-state optimality for beta-prior transmissivity sensing. -/

import D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation

noncomputable abbrev FockSpace := lp (fun _ : ℕ => ℂ) 2
noncomputable def e (n : ℕ) : FockSpace := lp.single 2 n 1
noncomputable def compression {N : ℕ} (H : FockSpace →L[ℂ] FockSpace) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℂ := fun i j => inner ℂ (e i) (H (e j))
private lemma inner_e (n : ℕ) (x : FockSpace) : inner ℂ (e n) x = x n := by
  simp [e, lp.inner_single_left, RCLike.inner_apply]
private lemma compression_isHermitian {N : ℕ} (H : FockSpace →L[ℂ] FockSpace) (hH : IsSelfAdjoint H) :
    (compression (N:=N) H).IsHermitian := by
  ext i j
  simp only [compression, conjTranspose_apply, inner_conj_symm]
  change (starRingEnd ℂ) (inner ℂ (e j) (H (e i))) = _
  rw [inner_conj_symm]
  exact hH.isSymmetric _ _
private lemma gram_le {N : ℕ} (R : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) (hR : R.PosSemidef)
    (x : Fin (N+1) → FockSpace) :
    (∑ k : Fin (N+1), ∑ i, ∑ j, R i j * (star (x j k) * x i k)).re ≤
      (∑ i, ∑ j, R i j * inner ℂ (x j) (x i)).re := by
  let q : ℕ → ℂ := fun k => ∑ i, ∑ j, R i j * (star (x j k) * x i k)
  have hq (k : ℕ) : 0 ≤ (q k).re := by
    have h := hR.dotProduct_mulVec_nonneg (fun i => star (x i k))
    rw [Complex.le_def] at h
    have he : q k = star (fun i => star (x i k)) ⬝ᵥ (R *ᵥ (fun i => star (x i k))) := by
      simp only [q, dotProduct, mulVec, Pi.star_apply, star_star, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact h.1
  have hs : HasSum q (∑ i, ∑ j, R i j * inner ℂ (x j) (x i)) := by
    have hs := hasSum_sum (s:=Finset.univ) (fun i _ =>
      hasSum_sum (s:=Finset.univ) (fun j _ => (lp.hasSum_inner (𝕜:=ℂ) (x j) (x i)).mul_left (R i j)))
    simpa only [q, RCLike.inner_apply, Finset.sum_fn, starRingEnd_apply, mul_comm] using hs
  have hl := sum_le_hasSum (Finset.range (N+1)) (fun k _ => hq k) (Complex.hasSum_re hs)
  simpa only [← Complex.re_sum, ← Fin.sum_univ_eq_sum_range] using hl

private noncomputable def toFock {N : ℕ} (B : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) :
    FockSpace →L[ℂ] FockSpace :=
  ∑ i, ∑ j, B i j • InnerProductSpace.rankOne ℂ (e i) (e j)
private lemma toFock_apply {N : ℕ} (B : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) (x : FockSpace) :
    toFock B x = ∑ i, ∑ j, (B i j * x j) • e i := by
  simp [toFock, _root_.sum_apply, InnerProductSpace.rankOne_apply,
    inner_e, smul_smul]
private lemma toFock_self {N : ℕ} (B : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
    (hB : B.IsHermitian) : IsSelfAdjoint (toFock B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp only [toFock, map_sum, map_smulₛₗ,
    InnerProductSpace.adjoint_rankOne]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show (starRingEnd ℂ) (B j i) = B i j from congrFun (congrFun hB i) j]
private lemma comp_shift {N : ℕ} (H : FockSpace →L[ℂ] FockSpace) (τ : ℝ) :
    compression (N:=N) (H - τ • 1) = compression H - (τ : ℂ) • 1 := by
  ext i j
  simp only [compression, inner_sub_right, inner_smul_right,
    _root_.sub_apply, _root_.smul_apply,
    one_apply_eq_self, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  rw [inner_e]
  simp only [e, lp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · have hv : (i : ℕ) ≠ j := Fin.val_ne_of_ne h
    simp [h, hv, Ne.symm hv, lp.inner_single_left, RCLike.inner_apply, lp.single_apply, Pi.single_apply]

private lemma trace_gram {N : ℕ} (R M : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
    (hM : M.IsHermitian) :
    (R * M ^ 2).trace = ∑ k, ∑ i, ∑ j, R i j * (star (M k j) * M k i) := by
  simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [show star (M k j) = M j k from congrFun (congrFun hM j) k]
private lemma integrand_le {N : ℕ} (R : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
    (hR : R.PosSemidef) (H : FockSpace →L[ℂ] FockSpace) (hH : IsSelfAdjoint H) (τ : ℝ) :
    (R * (compression H - (τ : ℂ) • 1)^2).trace.re ≤
      (∑ i, ∑ j, R i j * inner ℂ (e j) (((H - τ • 1) * (H - τ • 1)) (e i))).re := by
  let T := H - τ • 1
  have hT : IsSelfAdjoint T := hH.sub ((IsSelfAdjoint.all τ).smul (IsSelfAdjoint.one _))
  have hh (i j : Fin (N+1)) :
      inner ℂ (e j) (((H - τ • 1) * (H - τ • 1)) (e i)) =
        inner ℂ (T (e j)) (T (e i)) := by
    exact (hT.isSymmetric (e j) (T (e i))).symm
  simp_rw [hh]
  rw [← comp_shift, trace_gram R _ (compression_isHermitian _ hT)]
  simp only [compression, inner_e]
  exact gram_le R hR (fun i => T (e i))

private lemma toFock_coord {N : ℕ} (B : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
    (x : FockSpace) (k : Fin (N+1)) : toFock B x k = ∑ j, B k j * x j := by
  rw [toFock_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    e, lp.single_apply, Pi.single_apply, smul_eq_mul]
  have hv (i : Fin (N+1)) : (k : ℕ) = i ↔ k = i := Fin.val_inj
  simp only [hv]
  simp
private lemma toFock_square {N : ℕ} (B : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
    (τ : ℝ) (i j : Fin (N+1)) :
    inner ℂ (e j) (((toFock B - τ • 1) * (toFock B - τ • 1)) (e i)) =
      ((B - (τ : ℂ) • 1)^2 : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) j i := by
  have hc (x : FockSpace) (k : Fin (N+1)) : (toFock B - τ • 1) x k =
      ∑ l, (B - (τ : ℂ) • 1) k l * x l := by
    simp only [_root_.sub_apply, _root_.smul_apply,
      one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul,
      Pi.smul_apply, toFock_coord, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, sub_mul, Finset.sum_sub_distrib]
    simp
  rw [inner_e]
  change (toFock B - τ • 1) ((toFock B - τ • 1) (e i)) j = _
  rw [hc]
  simp_rw [hc]
  simp only [e, lp.single_apply, Pi.single_apply]
  have hv (l : Fin (N+1)) : (l : ℕ) = i ↔ l = i := Fin.val_inj
  simp only [hv]
  simp [pow_two, Matrix.mul_apply]

noncomputable def betaDensity (α β τ : ℝ) : ℝ :=
  τ ^ (α - 1) * (1 - τ) ^ (β - 1) /
    (Real.Gamma α * Real.Gamma β / Real.Gamma (α + β))

noncomputable def momentBeta {N : ℕ} (α β : ℝ) (ψ : Fin (N + 1) → ℂ)
    (k : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j => ∫ τ in (0 : ℝ)..1,
    ((betaDensity α β τ * τ ^ k : ℝ) : ℂ) * outputState τ ψ i j

noncomputable def deltaBMatrix {N : ℕ} (α β : ℝ) (ψ : Fin (N + 1) → ℂ)
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, betaDensity α β τ *
    ((outputState τ ψ * (H - (τ : ℂ) • 1) ^ 2).trace).re

noncomputable def deltaB {N : ℕ} (α β : ℝ) (ψ : Fin (N+1) → ℂ)
    (H : FockSpace →L[ℂ] FockSpace) : ℝ :=
  ∫ τ in (0 : ℝ)..1, betaDensity α β τ *
    (∑ i, ∑ j, outputState τ ψ i j *
      inner ℂ (e j) (((H - τ • 1) * (H - τ • 1)) (e i))).re
noncomputable def MMSE {N : ℕ} (α β : ℝ) (ψ : Fin (N + 1) → ℂ) : ℝ :=
  sInf {r : ℝ | ∃ H : FockSpace →L[ℂ] FockSpace,
    IsSelfAdjoint H ∧ r = deltaB α β ψ H}

def claim : Prop :=
  ∀ (α β nbar : ℝ), 0 < α → 0 < β → 0 < nbar →
    ∀ (N : ℕ) (ψ : Fin (N + 1) → ℂ), ‖WithLp.toLp 2 ψ‖ = 1 → meanPhoton ψ = nbar →
      ∃ φ : ℝ, MMSE α β (inBetween nbar φ) ≤ MMSE α β ψ

private lemma outputState_continuous {N : ℕ} (ψ : Fin (N+1) → ℂ) (i j : Fin (N+1)) :
    Continuous (fun τ : ℝ => outputState τ ψ i j) := by
  have hK (l r c : Fin (N+1)) :
      Continuous (fun τ : ℝ => amplitudeKraus l (1-τ) r c) := by
    simp only [amplitudeKraus, Matrix.of_apply]
    split_ifs <;> fun_prop
  unfold outputState
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply]
  fun_prop

theorem deltaBMatrix_eq_moments {N : ℕ} (α β : ℝ) (ψ : Fin (N + 1) → ℂ)
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hp : ContinuousOn (betaDensity α β) (Set.Icc 0 1)) :
    deltaBMatrix α β ψ H = ((H * H * momentBeta α β ψ 0).trace -
      2 * (H * momentBeta α β ψ 1).trace + (momentBeta α β ψ 2).trace).re := by
  classical
  have hrho (i j : Fin (N+1)) := outputState_continuous ψ i j
  have hi (k : ℕ) (i j : Fin (N+1)) : IntervalIntegrable
      (fun τ : ℝ => ((betaDensity α β τ * τ^k : ℝ) : ℂ) * outputState τ ψ i j)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (Complex.continuous_ofReal.comp_continuousOn
      (hp.mul (continuous_id.pow k).continuousOn)).mul (hrho i j).continuousOn
  let f (T : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) (k : ℕ) (τ : ℝ) :=
    ∑ i, ∑ j, T i j * (((betaDensity α β τ * τ^k : ℝ) : ℂ) * outputState τ ψ j i)
  have his (T : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) (k : ℕ) (i : Fin (N+1)) :
      IntervalIntegrable (fun τ : ℝ => ∑ j, T i j *
        (((betaDensity α β τ * τ^k : ℝ) : ℂ) * outputState τ ψ j i)) volume 0 1 := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ
      (fun j _ => (hi k j i).const_mul (T i j))
  have hf (T : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) (k : ℕ) :
      IntervalIntegrable (f T k) volume 0 1 := by
    simpa only [f, Finset.sum_fn] using IntervalIntegrable.sum Finset.univ
      (fun i _ => his T k i)
  have ht (T : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) (k : ℕ) :
      (∫ τ in (0 : ℝ)..1, f T k τ) = (T * momentBeta α β ψ k).trace := by
    unfold f
    rw [intervalIntegral.integral_finsetSum (fun i _ => his T k i)]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hi k j i).const_mul (T i j))]
    simp only [intervalIntegral.integral_const_mul, momentBeta]
  have ftrace (T : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) (k : ℕ) (τ : ℝ) :
      f T k τ = ((betaDensity α β τ * τ^k : ℝ) : ℂ) * (T * outputState τ ψ).trace := by
    simp only [f, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have integrand (τ : ℝ) :
      (betaDensity α β τ : ℂ) * (outputState τ ψ * (H - (τ : ℂ) • 1)^2).trace =
        f (H * H) 0 τ - 2 * f H 1 τ + f 1 2 τ := by
    simp only [ftrace, pow_zero, mul_one, pow_one, Complex.ofReal_mul,
      pow_two, sub_mul, mul_sub, Matrix.mul_smul,
      Matrix.smul_mul, one_mul, mul_one, trace_sub, trace_smul, smul_eq_mul]
    rw [mul_assoc, trace_mul_comm (outputState τ ψ) (H * H),
      trace_mul_comm (outputState τ ψ) H]
    simp only [mul_assoc]
    ring
  unfold deltaBMatrix
  simp_rw [show ∀ τ : ℝ, betaDensity α β τ *
      (outputState τ ψ * (H - (τ : ℂ) • 1)^2).trace.re =
      ((betaDensity α β τ : ℂ) *
        (outputState τ ψ * (H - (τ : ℂ) • 1)^2).trace).re by
    intro τ; simp, integrand]
  change (∫ τ in (0 : ℝ)..1, Complex.reCLM
    (f (H * H) 0 τ - 2 * f H 1 τ + f 1 2 τ)) = _
  rw [Complex.reCLM.intervalIntegral_comp_comm
    (((hf (H * H) 0).sub ((hf H 1).const_mul 2)).add (hf 1 2))]
  rw [intervalIntegral.integral_add ((hf (H * H) 0).sub ((hf H 1).const_mul 2))
    (hf 1 2), intervalIntegral.integral_sub (hf (H * H) 0) ((hf H 1).const_mul 2),
    intervalIntegral.integral_const_mul, ht, ht, ht, one_mul]
  rfl

theorem compression_le {N : ℕ} (α β : ℝ) (ψ : Fin (N+1) → ℂ)
    (H : FockSpace →L[ℂ] FockSpace) (hH : IsSelfAdjoint H)
    (hp : ContinuousOn (betaDensity α β) (Set.Icc 0 1))
    (hn : ∀ τ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ betaDensity α β τ)
    (hρ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (outputState τ ψ).PosSemidef) :
    deltaBMatrix α β ψ (compression H) ≤ deltaB α β ψ H := by
  have hrho (i j : Fin (N+1)) := outputState_continuous ψ i j
  have hc (i j : Fin (N+1)) : Continuous (fun τ : ℝ => inner ℂ (e j)
      (((H - τ • 1) * (H - τ • 1)) (e i))) := by fun_prop
  have hf : ContinuousOn (fun τ => betaDensity α β τ *
      (∑ i, ∑ j, outputState τ ψ i j * inner ℂ (e j)
        (((H - τ • 1) * (H - τ • 1)) (e i))).re) (Set.Icc 0 1) := by
    apply hp.mul
    exact (by fun_prop : Continuous (fun τ : ℝ =>
      (∑ i, ∑ j, outputState τ ψ i j * inner ℂ (e j)
        (((H - τ • 1) * (H - τ • 1)) (e i))).re)).continuousOn
  have hm : ContinuousOn (fun τ => betaDensity α β τ *
      (outputState τ ψ * (compression H - (τ : ℂ) • 1)^2).trace.re) (Set.Icc 0 1) := by
    apply hp.mul
    apply Continuous.continuousOn
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two, Matrix.sub_apply,
      Matrix.smul_apply]
    fun_prop
  unfold deltaBMatrix deltaB
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hm.intervalIntegrable_of_Icc (by norm_num)) (hf.intervalIntegrable_of_Icc (by norm_num))
  intro τ hτ
  exact mul_le_mul_of_nonneg_left (integrand_le _ (hρ τ hτ) H hH τ) (hn τ hτ)
private lemma deltaB_toFock {N : ℕ} (α β : ℝ) (ψ : Fin (N+1) → ℂ)
    (B : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) :
    deltaB α β ψ (toFock B) = deltaBMatrix α β ψ B := by
  unfold deltaB deltaBMatrix
  apply intervalIntegral.integral_congr
  intro τ _
  simp_rw [toFock_square]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]

theorem result : ¬ claim := by
  classical
  have density (τ : ℝ) : betaDensity 3 1 τ = 3 * τ ^ 2 := by
    have g3 : Real.Gamma 3 = 2 := by
      convert Real.Gamma_nat_eq_factorial 2 using 1 <;> norm_num
    have g4 : Real.Gamma 4 = 6 := by
      convert Real.Gamma_nat_eq_factorial 3 using 1 <;> norm_num
    unfold betaDensity
    simp only [show (3 : ℝ) - 1 = 2 by norm_num,
      show (1 : ℝ) - 1 = 0 by norm_num, show (3 : ℝ) + 1 = 4 by norm_num,
      Real.rpow_zero, Real.Gamma_one, g3, g4, mul_one]
    rw [show τ ^ (2 : ℝ) = τ ^ (2 : ℕ) from Real.rpow_natCast τ 2]
    ring
  have hp : ContinuousOn (betaDensity 3 1) (Set.Icc 0 1) := by
    change ContinuousOn (fun τ => betaDensity 3 1 τ) (Set.Icc 0 1)
    simp_rw [density]
    exact (by fun_prop : Continuous (fun τ : ℝ => 3 * τ ^ 2)).continuousOn
  have ipow (n : ℕ) : (∫ τ in (0 : ℝ)..1, (τ : ℂ)^n) = 1 / (n + 1 : ℂ) := by
    simp only [← Complex.ofReal_pow, intervalIntegral.integral_ofReal,
      integral_pow, one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
    push_cast
    rfl
  have cpow (n : ℕ) (a : ℂ) :
      IntervalIntegrable (fun τ : ℝ => a * (τ : ℂ)^n) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have poly (a b c : ℂ) (n : ℕ) :
      (∫ τ in (0 : ℝ)..1,
        a * (τ : ℂ)^(n+2) + b * (τ : ℂ)^(n+3) + c * (τ : ℂ)^(n+4)) =
      a / (n+3 : ℂ) + b / (n+4 : ℂ) + c / (n+5 : ℂ) := by
    rw [intervalIntegral.integral_add ((cpow _ _).add (cpow _ _)) (cpow _ _),
      intervalIntegral.integral_add (cpow _ _) (cpow _ _)]
    simp only [intervalIntegral.integral_const_mul, ipow]
    push_cast
    ring
  have halfpow (n : ℕ) (a : ℂ) :
      (∫ τ in (0 : ℝ)..1, a * (τ : ℂ)^(n+2) * (Real.sqrt τ : ℂ)) =
        a / ((n : ℂ) + 7/2) := by
    have h : (∫ τ in (0 : ℝ)..1, (τ : ℂ)^(n+2) * (Real.sqrt τ : ℂ)) =
        ∫ τ in (0 : ℝ)..1, ((τ ^ ((n : ℝ) + 5/2) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro τ hτ
      have ht : 0 ≤ τ := by simpa using hτ.1
      dsimp only
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Real.sqrt_eq_rpow,
        ← Real.rpow_natCast, ← Real.rpow_add_of_nonneg ht (by positivity) (by norm_num)]
      congr 2
      push_cast
      ring
    simp_rw [mul_assoc a]
    rw [intervalIntegral.integral_const_mul, h, intervalIntegral.integral_ofReal,
      integral_rpow (Or.inl (by linarith [Nat.cast_nonneg (α := ℝ) n] : -1 < (n : ℝ) + 5/2))]
    rw [Real.one_rpow, Real.zero_rpow (by positivity : (n : ℝ) + 5/2 + 1 ≠ 0)]
    push_cast
    ring
  have chi_moments (z : ℂ) (hz : z * star z = 1) (k : ℕ) :
      let χ : Fin 2 → ℂ := ![(Real.sqrt 3 : ℂ)/2, z/2]
      momentBeta 3 1 χ k =
        !![3/(k+3 : ℂ) - 3/(4*(k+4 : ℂ)),
           (3*(Real.sqrt 3 : ℂ)/(4*(k : ℂ)+14)) * star z;
           (3*(Real.sqrt 3 : ℂ)/(4*(k : ℂ)+14)) * z, 3/(4*(k+4 : ℂ))] := by
    dsimp only
    let χ : Fin 2 → ℂ := ![(Real.sqrt 3 : ℂ)/2, z/2]
    have h3 : (Real.sqrt 3 : ℂ)^2 = 3 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have hz₁ : z * (starRingEnd ℂ) z = 1 := hz
    have hz₂ : (starRingEnd ℂ) z * z = 1 := by simpa only [mul_comm] using hz₁
    have rho (τ : ℝ) (hτ : τ ∈ Set.Icc 0 1) : outputState τ χ =
        !![1-(τ : ℂ)/4, (Real.sqrt 3 : ℂ)*(Real.sqrt τ : ℂ)/4 * star z;
           (Real.sqrt 3 : ℂ)*(Real.sqrt τ : ℂ)/4 * z, (τ : ℂ)/4] := by
      have ht : (Real.sqrt τ : ℂ)^2 = (τ : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt hτ.1]
      have htm : (Real.sqrt (1-τ) : ℂ)^2 = 1-(τ : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (sub_nonneg.mpr hτ.2)]
        push_cast
        rfl
      simp only [outputState, sourceKraus _ _ hτ, source_coefficient _ _ _ hτ]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.of_apply, χ, Matrix.mul_apply, Fin.sum_univ_succ,
          vecMulVec_apply, rankOneDensity, conjTranspose_apply, Pi.star_apply,
          RCLike.star_def, Complex.conj_ofReal, map_mul, map_ofNat, map_div₀] <;>
        (try ring_nf) <;> (try simp only [h3, ht, htm]) <;> (try ring_nf) <;>
        (try simp only [mul_assoc (τ : ℂ) z, hz₁, hz₂, mul_one]) <;>
        (first | rfl | ring)
    have diag0 : momentBeta 3 1 χ k 0 0 = 3/(k+3 : ℂ)-3/(4*(k+4 : ℂ)) := by
      unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        3*(τ : ℂ)^(k+2) + (-3/4)*(τ : ℂ)^(k+3) + 0*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> (first | rfl | ring)
      · rw [poly]
        simp only [div_mul_eq_div_div]
        ring
    have diag1 : momentBeta 3 1 χ k 1 1 = 3/(4*(k+4 : ℂ)) := by
      unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        0*(τ : ℂ)^(k+2) + (3/4)*(τ : ℂ)^(k+3) + 0*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> (first | rfl | ring)
      · rw [poly]
        simp only [div_mul_eq_div_div]
        ring
    have off (i j : Fin 2) (w : ℂ)
        (hr : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          outputState τ χ i j = (Real.sqrt 3 : ℂ)*(Real.sqrt τ : ℂ)/4*w) :
        momentBeta 3 1 χ k i j = (3*(Real.sqrt 3 : ℂ)/(4*(k : ℂ)+14))*w := by
      unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (3*(Real.sqrt 3 : ℂ)*w/4) * (τ : ℂ)^(k+2) * (Real.sqrt τ : ℂ)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, hr τ ht]
        push_cast
        simp only [pow_add]
        ring
      · rw [halfpow]
        rw [show 4*(k : ℂ)+14 = 4*((k : ℂ)+7/2) by ring]
        simp only [div_mul_eq_div_div]
        ring
    ext i j
    fin_cases i <;> fin_cases j
    · exact diag0
    · exact off 0 1 (star z) (by intro τ hτ; rw [rho τ hτ]; rfl)
    · exact off 1 0 z (by intro τ hτ; rw [rho τ hτ]; rfl)
    · exact diag1
  have psi_moments (k : ℕ) :
      let ψ : Fin 3 → ℂ := ![(Real.sqrt 14 : ℂ)/4, 0, (Real.sqrt 2 : ℂ)/4]
      momentBeta 3 1 ψ k =
        !![3/(k+3 : ℂ)-3/(4*(k+4 : ℂ))+3/(8*(k+5 : ℂ)), 0,
             3*(Real.sqrt 7 : ℂ)/(8*(k+4 : ℂ));
           0, 3/(4*(k+4 : ℂ))-3/(4*(k+5 : ℂ)), 0;
           3*(Real.sqrt 7 : ℂ)/(8*(k+4 : ℂ)), 0, 3/(8*(k+5 : ℂ))] := by
    dsimp only
    let ψ : Fin 3 → ℂ := ![(Real.sqrt 14 : ℂ)/4, 0, (Real.sqrt 2 : ℂ)/4]
    have h14 : (Real.sqrt 14 : ℂ)^2 = 14 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 14)]
      norm_num
    have h2 : (Real.sqrt 2 : ℂ)^2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hFin12 : (1 : Fin 3) ≤ 2 := by decide
    have h24 : (Real.sqrt 2 : ℂ)^4 = 4 := by
      calc (Real.sqrt 2 : ℂ)^4 = ((Real.sqrt 2 : ℂ)^2)^2 := by ring
           _ = 4 := by rw [h2]; norm_num
    have hprod : (Real.sqrt 14 : ℂ)*(Real.sqrt 2 : ℂ) = 2*(Real.sqrt 7 : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 14),
        show (14 : ℝ)*2 = 4*7 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    have rho (τ : ℝ) (hτ : τ ∈ Set.Icc 0 1) : outputState τ ψ =
        !![1-(τ : ℂ)/4+(τ : ℂ)^2/8, 0, (Real.sqrt 7 : ℂ)*(τ : ℂ)/8;
           0, (τ : ℂ)/4-(τ : ℂ)^2/4, 0;
           (Real.sqrt 7 : ℂ)*(τ : ℂ)/8, 0, (τ : ℂ)^2/8] := by
      have ht : (Real.sqrt τ : ℂ)^2 = (τ : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt hτ.1]
      have htm : (Real.sqrt (1-τ) : ℂ)^2 = 1-(τ : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (sub_nonneg.mpr hτ.2)]
        push_cast
        rfl
      have ht4 : (Real.sqrt τ : ℂ)^4 = (τ : ℂ)^2 := by
        calc (Real.sqrt τ : ℂ)^4 = ((Real.sqrt τ : ℂ)^2)^2 := by ring
             _ = (τ : ℂ)^2 := by rw [ht]
      have htm4 : (Real.sqrt (1-τ) : ℂ)^4 = (1-(τ : ℂ))^2 := by
        calc (Real.sqrt (1-τ) : ℂ)^4 = ((Real.sqrt (1-τ) : ℂ)^2)^2 := by ring
             _ = (1-(τ : ℂ))^2 := by rw [htm]
      simp only [outputState, sourceKraus _ _ hτ, source_coefficient _ _ _ hτ]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.of_apply, ψ, Matrix.mul_apply, Fin.sum_univ_succ,
          vecMulVec_apply, rankOneDensity, conjTranspose_apply, Pi.star_apply,
          RCLike.star_def, Complex.conj_ofReal, map_mul, map_ofNat, map_div₀, hFin12] <;>
        (try ring_nf) <;> (try simp only [h14, h2, h24, ht, htm, ht4, htm4]) <;> (try ring_nf) <;>
        (try ring) <;> linear_combination hprod * ((τ : ℂ)/16)
    ext i j
    fin_cases i <;> fin_cases j
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (3)*(τ : ℂ)^(k+2) + (-3/4)*(τ : ℂ)^(k+3) + (3/8)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (0)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (3*(Real.sqrt 7 : ℂ)/8)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (0)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (3/4)*(τ : ℂ)^(k+3) + (-3/4)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (0)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (3*(Real.sqrt 7 : ℂ)/8)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (0)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (0)*(τ : ℂ)^(k+3) + (3/8)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
  have bounds {N : ℕ} (ψ : Fin (N+1) → ℂ)
      (B : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
      (hA : (momentBeta 3 1 ψ 0).PosSemidef) (hB : B.IsHermitian)
      (hsol : momentBeta 3 1 ψ 0 * B + B * momentBeta 3 1 ψ 0 =
        (2 : ℂ) • momentBeta 3 1 ψ 1) :
      ((momentBeta 3 1 ψ 2).trace - (B * momentBeta 3 1 ψ 1).trace).re ≤
          MMSE 3 1 ψ ∧
        MMSE 3 1 ψ ≤
          ((momentBeta 3 1 ψ 2).trace - (B * momentBeta 3 1 ψ 1).trace).re := by
    let A := momentBeta 3 1 ψ 0
    let C := momentBeta 3 1 ψ 1
    let D := momentBeta 3 1 ψ 2
    let L := (D.trace - (B * C).trace).re
    have hbb : (A * B * B).trace = (B * C).trace := by
      have h := congrArg (fun Z => (B * Z).trace) hsol
      change (B * (A * B + B * A)).trace = (B * ((2 : ℂ) • C)).trace at h
      simp only [mul_add, trace_add, Matrix.mul_smul, trace_smul, smul_eq_mul,
        ← mul_assoc] at h
      rw [trace_mul_cycle B A B, trace_mul_cycle B B A] at h
      linear_combination h / 2
    have hcross (H : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) :
        (A * H * B).trace + (A * B * H).trace = 2 * (H * C).trace := by
      have h := congrArg (fun Z => (H * Z).trace) hsol
      change (H * (A * B + B * A)).trace = (H * ((2 : ℂ) • C)).trace at h
      simp only [mul_add, trace_add, Matrix.mul_smul, trace_smul, smul_eq_mul] at h
      rw [← mul_assoc, ← mul_assoc, trace_mul_cycle H A B,
        trace_mul_cycle B H A, trace_mul_cycle H B A] at h
      simpa only [add_comm] using h
    have bound (H : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) (hH : H.IsHermitian) :
        L ≤ deltaBMatrix 3 1 ψ H := by
      have hS : ((H - B) * (H - B)).PosSemidef := by
        simpa only [(hH.sub hB).eq] using posSemidef_conjTranspose_mul_self (H - B)
      have hn := RHLinalg.trace_mul_nonneg_of_posSemidef hA hS
      have complete : (H * H * A).trace - 2 * (H * C).trace + D.trace -
          (D.trace - (B * C).trace) = (A * ((H - B) * (H - B))).trace := by
        simp only [mul_sub, sub_mul, trace_add, trace_sub, ← mul_assoc]
        rw [trace_mul_cycle H H A]
        linear_combination hcross H - hbb
      rw [deltaBMatrix_eq_moments 3 1 ψ H hp]
      change L ≤ ((H * H * A).trace - 2 * (H * C).trace + D.trace).re
      have h := congrArg Complex.re complete
      change 0 ≤ (A * ((H - B) * (H - B))).trace.re at hn
      dsimp only [L]
      simp only [Complex.sub_re, Complex.add_re] at h ⊢
      linarith
    have attain : deltaBMatrix 3 1 ψ B = L := by
      rw [deltaBMatrix_eq_moments 3 1 ψ B hp]
      change ((B * B * A).trace - 2 * (B * C).trace + D.trace).re = L
      rw [trace_mul_cycle B B A, hbb]
      dsimp only [L]
      congr 1
      ring
    have boundFock (H : FockSpace →L[ℂ] FockSpace) (hH : IsSelfAdjoint H) :
        L ≤ deltaB 3 1 ψ H := by
      apply (bound (compression H) (compression_isHermitian H hH)).trans
      apply compression_le 3 1 ψ H hH hp
      · intro τ _
        rw [density]
        positivity
      · intro τ _
        exact posSemidef_sum _ fun l _ =>
          (posSemidef_vecMulVec_self_star ψ).mul_mul_conjTranspose_same
            (amplitudeKraus l (1-τ))
    have attainFock : deltaB 3 1 ψ (toFock B) = L :=
      (deltaB_toFock 3 1 ψ B).trans attain
    have nonempty : {r : ℝ | ∃ H : FockSpace →L[ℂ] FockSpace,
        IsSelfAdjoint H ∧ r = deltaB 3 1 ψ H}.Nonempty :=
      ⟨deltaB 3 1 ψ (toFock B), toFock B, toFock_self B hB, rfl⟩
    constructor
    · unfold MMSE
      apply le_csInf nonempty
      rintro r ⟨H, hH, rfl⟩
      exact boundFock H hH
    · unfold MMSE
      apply csInf_le
      · refine ⟨L, ?_⟩
        rintro r ⟨H, hH, rfl⟩
        exact boundFock H hH
      · exact ⟨toFock B, toFock_self B hB, attainFock.symm⟩

  have chi_lower (φ : ℝ) : 167/4575 ≤ MMSE 3 1 (inBetween (1/4) φ) := by
    let z := Complex.exp (Complex.I * (φ : ℂ))
    let χ : Fin 2 → ℂ := ![(Real.sqrt 3 : ℂ)/2, z/2]
    let B : Matrix (Fin 2) (Fin 2) ℂ :=
      !![216/305, 7*(Real.sqrt 3 : ℂ)/183 * star z;
         7*(Real.sqrt 3 : ℂ)/183 * z, 204/305]
    have hz : z * star z = 1 := by
      dsimp [z]
      rw [← Complex.exp_conj, ← Complex.exp_add]
      have he : Complex.I * (φ : ℂ) + star (Complex.I * (φ : ℂ)) = 0 := by simp
      simpa [he]
    have hz₁ : z * (starRingEnd ℂ) z = 1 := hz
    have hz₂ : (starRingEnd ℂ) z * z = 1 := by simpa only [mul_comm] using hz₁
    have h3 : (Real.sqrt 3 : ℂ)^2 = 3 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have g0 : momentBeta 3 1 χ 0 =
        !![13/16, 3*(Real.sqrt 3 : ℂ)/14*star z;
           3*(Real.sqrt 3 : ℂ)/14*z, 3/16] := by
      convert chi_moments z hz 0 using 1 <;> norm_num <;> (first | left; ring | ring)
    have g1 : momentBeta 3 1 χ 1 =
        !![3/5, (Real.sqrt 3 : ℂ)/6*star z;
           (Real.sqrt 3 : ℂ)/6*z, 3/20] := by
      convert chi_moments z hz 1 using 1 <;> norm_num <;> (first | left; ring | ring)
    have g2 : momentBeta 3 1 χ 2 =
        !![19/40, 3*(Real.sqrt 3 : ℂ)/22*star z;
           3*(Real.sqrt 3 : ℂ)/22*z, 1/8] := by
      convert chi_moments z hz 2 using 1 <;> norm_num <;> (first | left; ring | ring)
    have hA : (momentBeta 3 1 χ 0).PosSemidef := by
      let v : Fin 2 → ℂ := ![8*(Real.sqrt 3 : ℂ)/7, z]
      have heq : momentBeta 3 1 χ 0 =
          (3/16 : ℂ) • vecMulVec v (star v) + diagonal ![(61/784 : ℂ), 0] := by
        rw [g0]
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [v, Matrix.add_apply, Matrix.smul_apply, diagonal_apply,
            vecMulVec_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal,
            map_mul, map_div₀, map_ofNat] <;>
          (try ring_nf) <;> (try simp only [h3, hz₁, hz₂]) <;> (try ring_nf) <;> (try simp only [hz₁, hz₂]) <;> ring
      rw [heq]
      apply ((posSemidef_vecMulVec_self_star v).smul
        (show (0 : ℂ) ≤ 3/16 by norm_num [Complex.le_def])).add
      apply posSemidef_diagonal_iff.mpr
      intro i
      fin_cases i <;> norm_num [Complex.le_def]
    have hB : B.IsHermitian := by
      change Bᴴ = B
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [B, conjTranspose_apply, RCLike.star_def, Complex.conj_ofReal]
    have hsol : momentBeta 3 1 χ 0 * B + B * momentBeta 3 1 χ 0 =
        (2 : ℂ) • momentBeta 3 1 χ 1 := by
      rw [g0, g1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [B, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.add_apply,
          Matrix.smul_apply] <;> (try ring_nf) <;>
        (try simp only [h3, hz₁, hz₂]) <;> (try ring_nf) <;> (try simp only [hz₁, hz₂]) <;> ring
    have hv : ((momentBeta 3 1 χ 2).trace -
        (B * momentBeta 3 1 χ 1).trace).re = 167/4575 := by
      rw [g1, g2]
      have hc : ((!![19/40, 3*(Real.sqrt 3 : ℂ)/22*star z;
          3*(Real.sqrt 3 : ℂ)/22*z, 1/8] : Matrix (Fin 2) (Fin 2) ℂ).trace -
          (B * !![3/5, (Real.sqrt 3 : ℂ)/6*star z;
            (Real.sqrt 3 : ℂ)/6*z, 3/20]).trace) = (167/4575 : ℂ) := by
        norm_num [B, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
        ring_nf
        (try simp only [h3, hz₁, hz₂]) <;> (try ring_nf) <;> (try simp only [hz₁, hz₂])
        ring
      rw [hc]
      norm_num
    have hl := (bounds χ B hA hB hsol).1
    rw [hv] at hl
    have phase : MMSE 3 1 (inBetween (1/4) φ) = MMSE 3 1 χ := by
      have hc : ⌈(1/4 : ℝ)⌉₊ = 1 := by norm_num
      have hs : (Real.sqrt (1/4))^2 = (1/4 : ℝ) := Real.sq_sqrt (by norm_num)
      unfold inBetween
      rw [hc]
      simp only [Nat.cast_one, Nat.sub_self, sub_self, zero_add, hs]
      apply congrArg (MMSE (N:=1) 3 1)
      ext n
      fin_cases n <;> norm_num [χ, z, Real.sqrt_div] <;> ring
    rw [phase]
    exact hl
  intro h
  let ψ : Fin 3 → ℂ := ![(Real.sqrt 14 : ℂ)/4, 0, (Real.sqrt 2 : ℂ)/4]
  let B : Matrix (Fin 3) (Fin 3) ℂ :=
    !![8/11, 0, 2*(Real.sqrt 7 : ℂ)/77;
       0, 2/3, 0;
       2*(Real.sqrt 7 : ℂ)/77, 0, 20/33]
  have h7 : (Real.sqrt 7 : ℂ)^2 = 7 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
    norm_num
  have g0 : momentBeta 3 1 ψ 0 =
      !![71/80, 0, 3*(Real.sqrt 7 : ℂ)/32;
         0, 3/80, 0;
         3*(Real.sqrt 7 : ℂ)/32, 0, 3/40] := by
    convert psi_moments 0 using 1 <;> norm_num <;> ring
  have g1 : momentBeta 3 1 ψ 1 =
      !![53/80, 0, 3*(Real.sqrt 7 : ℂ)/40;
         0, 1/40, 0;
         3*(Real.sqrt 7 : ℂ)/40, 0, 1/16] := by
    convert psi_moments 1 using 1 <;> norm_num <;> ring
  have g2 : momentBeta 3 1 ψ 2 =
      !![37/70, 0, (Real.sqrt 7 : ℂ)/16;
         0, 1/56, 0;
         (Real.sqrt 7 : ℂ)/16, 0, 3/56] := by
    convert psi_moments 2 using 1 <;> norm_num <;> ring
  have hA : (momentBeta 3 1 ψ 0).PosSemidef := by
    let v : Fin 3 → ℂ := ![5*(Real.sqrt 7 : ℂ)/4, 0, 1]
    have heq : momentBeta 3 1 ψ 0 =
        (3/40 : ℂ) • vecMulVec v (star v) + diagonal ![(43/640 : ℂ), 3/80, 0] := by
      rw [g0]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [v, Matrix.add_apply, Matrix.smul_apply, diagonal_apply,
          vecMulVec_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal,
          map_mul, map_div₀, map_ofNat] <;>
        (try ring_nf) <;> (try simp only [h7]) <;> ring
    rw [heq]
    apply ((posSemidef_vecMulVec_self_star v).smul
      (show (0 : ℂ) ≤ 3/40 by norm_num [Complex.le_def])).add
    apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num [Complex.le_def]
  have hB : B.IsHermitian := by
    change Bᴴ = B
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, conjTranspose_apply, RCLike.star_def, Complex.conj_ofReal]
  have hsol : momentBeta 3 1 ψ 0 * B + B * momentBeta 3 1 ψ 0 =
      (2 : ℂ) • momentBeta 3 1 ψ 1 := by
    rw [g0, g1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.add_apply,
        Matrix.smul_apply] <;> (try ring_nf) <;> (try simp only [h7]) <;> ring
  have hv : ((momentBeta 3 1 ψ 2).trace -
      (B * momentBeta 3 1 ψ 1).trace).re = 2/55 := by
    rw [g1, g2]
    have hc : ((!![37/70, 0, (Real.sqrt 7 : ℂ)/16;
        0, 1/56, 0; (Real.sqrt 7 : ℂ)/16, 0, 3/56] : Matrix (Fin 3) (Fin 3) ℂ).trace -
        (B * !![53/80, 0, 3*(Real.sqrt 7 : ℂ)/40;
          0, 1/40, 0; 3*(Real.sqrt 7 : ℂ)/40, 0, 1/16]).trace) = (2/55 : ℂ) := by
      norm_num [B, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
      ring_nf
      rw [h7]
      norm_num
    rw [hc]
    norm_num
  have hnorm : ‖WithLp.toLp 2 ψ‖ = 1 := by
    have hs : ‖WithLp.toLp 2 ψ‖^2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      norm_num [ψ, Fin.sum_univ_succ, norm_div, Complex.norm_real,
        abs_of_nonneg (Real.sqrt_nonneg 14), abs_of_nonneg (Real.sqrt_nonneg 2)]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 14),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [norm_nonneg (WithLp.toLp 2 ψ)]
  have hmean : meanPhoton ψ = 1/4 := by
    unfold meanPhoton
    norm_num [ψ, Complex.normSq, Fin.sum_univ_succ, Real.sq_sqrt]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  obtain ⟨φ, hle⟩ := h 3 1 (1/4) (by norm_num) (by norm_num) (by norm_num)
    2 ψ hnorm hmean
  have hup := (bounds ψ B hA hB hsol).2
  rw [hv] at hup
  have hlow := chi_lower φ
  linarith

end D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation
