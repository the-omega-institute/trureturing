/- GID: D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/HellingerEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singular noncommuting logarithmic energy controls entropy and the actual trace-norm square. -/

import D5.S3.Quantum.Analysis.TraceClass.SpectralEnergy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

noncomputable section
open scoped ComplexOrder InnerProductSpace ENNReal
open HilbertSchmidt
set_option backward.isDefEq.respectTransparency false
namespace QuantumLogEnergy
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem scalar_hellinger {r s : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ENNReal.ofReal (-r * Real.log r) + ENNReal.ofReal r +
        ENNReal.ofReal ((Real.sqrt r - Real.sqrt s) ^ 2) ≤
      ENNReal.ofReal r * singularLog s + ENNReal.ofReal s := by
  by_cases hr0 : r = 0
  · simp [hr0, Real.sq_sqrt hs]
  by_cases hs0 : s = 0
  · simp [singularLog, hs0, ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne hr (Ne.symm hr0))]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hu := Real.sqrt_pos.mpr hrp
  have hv := Real.sqrt_pos.mpr hsp
  have hl := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne', Real.log_sqrt hs, Real.log_sqrt hr] at hl
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * r by positivity)
  have he : r * (Real.sqrt s / Real.sqrt r) = Real.sqrt r * Real.sqrt s := by
    field_simp
    nlinarith [Real.sq_sqrt hr]
  have hreal : -r * Real.log r + r + (Real.sqrt r - Real.sqrt s) ^ 2 ≤
      r * (-Real.log s) + s := by
    nlinarith [Real.sq_sqrt hr, Real.sq_sqrt hs]
  have hn : 0 ≤ -r * Real.log r :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hr) (Real.log_nonpos hr hr1)
  rw [singularLog, if_neg hs0, ← ENNReal.ofReal_mul hr,
    ← ENNReal.ofReal_add hn hr, ← ENNReal.ofReal_add (add_nonneg hn hr) (sq_nonneg _),
    ← ENNReal.ofReal_add (mul_nonneg hr (neg_nonneg.mpr (Real.log_nonpos hs hs1))) hs]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem summed_scalar_hellinger {ι κ : Type*} (r : ι → ℝ) (s : κ → ℝ)
    (c : ι → κ → ℝ≥0∞) (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hs : ∀ j, 0 ≤ s j) (hs1 : ∀ j, s j ≤ 1) :
    (∑' i, ∑' j, ENNReal.ofReal (-r i * Real.log (r i)) * c i j) +
      (∑' i, ∑' j, ENNReal.ofReal (r i) * c i j) +
      (∑' i, ∑' j, ENNReal.ofReal ((Real.sqrt (r i) - Real.sqrt (s j)) ^ 2) * c i j) ≤
    (∑' i, ∑' j, (ENNReal.ofReal (r i) * singularLog (s j)) * c i j) +
      (∑' i, ∑' j, ENNReal.ofReal (s j) * c i j) := by
  have h := ENNReal.tsum_le_tsum (fun i => ENNReal.tsum_le_tsum (fun j =>
    mul_le_mul_left (scalar_hellinger (hr i) (hr1 i) (hs j) (hs1 j)) (c i j)))
  simpa only [add_mul, ENNReal.tsum_add] using h

private theorem sqrt_eigen (T : Reference H) (d : SpectralResolution T) (i : d.index) :
    CFC.sqrt T.1.1 (d.basis i) = (Real.sqrt (d.values i) : ℂ) • d.basis i := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ _ T.2.1]
  have hfun : (fun x : ℝ => (NNReal.sqrt x.toNNReal : ℝ)) = Real.sqrt := by
    funext x
    rw [Real.sqrt]
  rw [hfun]
  exact cfc_apply_eigenvector T.1.1 (.of_nonneg T.2.1) _ _ (d.eigen i)
    Real.sqrt Real.continuous_sqrt.continuousOn

private theorem sqrt_hs (T : Reference H) : IsHilbertSchmidt (CFC.sqrt T.1.1) := by
  have h := isHilbertSchmidt_sqrt_abs_of_isTraceClass (TraceClass.isTraceClass_coe T.1)
  rwa [CFC.abs_of_nonneg _ T.2.1] at h

private theorem sqrt_square_sum (T : Reference H) {w : Set H} (b : HilbertBasis w ℂ H) :
    (∑' i, ‖CFC.sqrt T.1.1 (b i)‖ ^ 2) = (trace T.1.1 (TraceClass.isTraceClass_coe T.1)).re := by
  have h := tsum_sqrt_abs_norm_sq_eq_traceNorm (TraceClass.isTraceClass_coe T.1) b
  rwa [CFC.abs_of_nonneg _ T.2.1, traceNorm_eq_re_trace _ T.2.1] at h

theorem resolution_diagonal (T : Reference H) (d : SpectralResolution T) (v : H) :
    HasSum (fun i => d.values i * ‖⟪v, d.basis i⟫_ℂ‖ ^ 2)
      (⟪v, T.1.1 v⟫_ℂ).re := by
  let R := CFC.sqrt T.1.1
  have hR : R.IsPositive := R.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)
  have hp := hasSum_norm_sq_inner_basis d.basis (R v)
  have hpoint (i : d.index) : ‖⟪d.basis i, R v⟫_ℂ‖ ^ 2 =
      d.values i * ‖⟪v, d.basis i⟫_ℂ‖ ^ 2 := by
    rw [← hR.inner_left_eq_inner_right, sqrt_eigen T d i, inner_smul_left,
      norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (d.nonneg i), norm_inner_symm]
  have hnorm : ‖R v‖ ^ 2 = (⟪v, T.1.1 v⟫_ℂ).re := by
    have hs : ContinuousLinearMap.adjoint R = R :=
      (ContinuousLinearMap.star_eq_adjoint R).symm.trans
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _))
    rw [← CFC.sqrt_mul_sqrt_self T.1.1 T.2.1, ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.adjoint_inner_left R (R v) v, hs, inner_self_eq_norm_sq_to_K]
    norm_cast
  simpa only [hpoint, hnorm] using hp

private theorem resolution_values_sum (T : Reference H) (d : SpectralResolution T) :
    HasSum d.values (trace T.1.1 (TraceClass.isTraceClass_coe T.1)).re := by
  convert diagonal_hasSum d.basis T.1 using 1
  funext i
  symm
  unfold diagonal
  rw [d.eigen i, inner_smul_right, inner_self_eq_norm_sq_to_K, d.basis.orthonormal.1 i]
  simp

theorem resolution_entropy (T : Reference H) (d : SpectralResolution T) :
    (∑' i, ENNReal.ofReal (-d.values i * Real.log (d.values i))) = spectralEntropy T := by
  rw [← spectralEnergy_self, ← spectralSeries_eq_spectralEnergy T d.basis d.values d.nonneg
    d.eigen T.1 T.2.1]
  unfold spectralSeries
  apply tsum_congr
  intro i
  have hd : diagonal d.basis T.1 i = d.values i := by
    unfold diagonal
    rw [d.eigen i, inner_smul_right, inner_self_eq_norm_sq_to_K, d.basis.orthonormal.1 i]
    simp
  rw [hd]
  by_cases hz : d.values i = 0
  · simp [hz]
  · rw [singularLog, if_neg hz, ← ENNReal.ofReal_mul (d.nonneg i)]
    congr 1
    ring

/-- The full transition-weight double series is the actual singular cross energy.
No normalization, finite energy or support restriction is required. -/
theorem resolution_cross_energy (rho sigma : Reference H)
    (d : SpectralResolution rho) (e : SpectralResolution sigma) :
    (∑' i, ∑' j, (ENNReal.ofReal (d.values i) * singularLog (e.values j)) *
      ENNReal.ofReal (‖⟪e.basis j, d.basis i⟫_ℂ‖ ^ 2)) =
        spectralEnergy sigma rho.1 := by
  let c : d.index → e.index → ℝ≥0∞ := fun i j =>
    ENNReal.ofReal (‖⟪e.basis j, d.basis i⟫_ℂ‖ ^ 2)
  have hdiag (j : e.index) : (∑' i, ENNReal.ofReal (d.values i) * c i j) =
      ENNReal.ofReal (diagonal e.basis rho.1 j) := by
    simp_rw [c, ← ENNReal.ofReal_mul (d.nonneg _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (d.nonneg i) (sq_nonneg _))
      (resolution_diagonal rho d (e.basis j)).summable,
      (resolution_diagonal rho d (e.basis j)).tsum_eq]
    rfl
  have henergy : (∑' i, ∑' j,
      (ENNReal.ofReal (d.values i) * singularLog (e.values j)) * c i j) =
      spectralEnergy sigma rho.1 := by
    calc
      _ = ∑' j, ∑' i, (ENNReal.ofReal (d.values i) * c i j) * singularLog (e.values j) := by
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro j
        apply tsum_congr
        intro i
        ac_rfl
      _ = spectralEnergy sigma rho.1 := by
        simp_rw [ENNReal.tsum_mul_right, hdiag]
        exact spectralSeries_eq_spectralEnergy sigma e.basis e.values e.nonneg e.eigen rho.1 rho.2.1
  exact henergy

set_option maxHeartbeats 1000000 in
-- Full dependent double sums and their kernel-checked transports share this local budget.
private theorem spectral_hellinger (rho sigma : Reference H)
    (d : SpectralResolution rho) (e : SpectralResolution sigma)
    (hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1) :
    spectralEntropy rho + ENNReal.ofReal
      (∑' i, ‖(CFC.sqrt rho.1.1 - CFC.sqrt sigma.1.1) (d.basis i)‖ ^ 2) ≤
      spectralEnergy sigma rho.1 := by
  let c : d.index → e.index → ℝ≥0∞ := fun i j => ENNReal.ofReal (‖⟪e.basis j, d.basis i⟫_ℂ‖ ^ 2)
  have hrow (i : d.index) : (∑' j, c i j) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _)
      (hasSum_norm_sq_inner_basis e.basis (d.basis i)).summable,
      (hasSum_norm_sq_inner_basis e.basis (d.basis i)).tsum_eq, d.basis.orthonormal.1 i]
    norm_num
  have hcol (j : e.index) : (∑' i, c i j) = 1 := by
    have h := hasSum_norm_sq_inner_basis d.basis (e.basis j)
    simp_rw [norm_inner_symm (d.basis _) (e.basis j)] at h
    change (∑' i, ENNReal.ofReal _) = _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h.summable,
      h.tsum_eq, e.basis.orthonormal.1 j]
    norm_num
  have hleft (a : d.index → ℝ≥0∞) : (∑' i, ∑' j, a i * c i j) = ∑' i, a i := by
    simp_rw [ENNReal.tsum_mul_left, hrow, mul_one]
  have hright (a : e.index → ℝ≥0∞) : (∑' i, ∑' j, a j * c i j) = ∑' j, a j := by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, hcol, mul_one]
  have hmass (T : Reference H) (a : SpectralResolution T)
      (ht : (trace T.1.1 (TraceClass.isTraceClass_coe T.1)).re = 1) :
      (∑' i, ENNReal.ofReal (a.values i)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg a.nonneg (resolution_values_sum T a).summable,
      (resolution_values_sum T a).tsum_eq, ht, ENNReal.ofReal_one]
  have henergy := resolution_cross_energy rho sigma d e
  let A := CFC.sqrt rho.1.1 - CFC.sqrt sigma.1.1
  have hA : IsHilbertSchmidt A := isHilbertSchmidt_sub (sqrt_hs rho) (sqrt_hs sigma)
  have hcoord (i : d.index) (j : e.index) :
      ⟪e.basis j, A (d.basis i)⟫_ℂ =
        ((Real.sqrt (d.values i) - Real.sqrt (e.values j) : ℝ) : ℂ) *
          ⟪e.basis j, d.basis i⟫_ℂ := by
    have hp := (CFC.sqrt sigma.1.1).nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)
    dsimp [A]
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, sqrt_eigen rho d i,
      inner_smul_right, ← hp.inner_left_eq_inner_right, sqrt_eigen sigma e j, inner_smul_left]
    simp only [Complex.conj_ofReal, Complex.ofReal_sub]
    ring
  have hnorm (i : d.index) (j : e.index) : ‖⟪e.basis j, A (d.basis i)⟫_ℂ‖ ^ 2 =
      (Real.sqrt (d.values i) - Real.sqrt (e.values j)) ^ 2 *
        ‖⟪e.basis j, d.basis i⟫_ℂ‖ ^ 2 := by
    rw [hcoord, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hdefect : (∑' i, ∑' j,
      ENNReal.ofReal ((Real.sqrt (d.values i) - Real.sqrt (e.values j)) ^ 2) * c i j) =
      ENNReal.ofReal (∑' i, ‖A (d.basis i)‖ ^ 2) := by
    have hp (i : d.index) := hasSum_norm_sq_inner_basis e.basis (A (d.basis i))
    simp_rw [c, ← ENNReal.ofReal_mul (sq_nonneg _), ← hnorm]
    simp_rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) (hp _).summable,
      (hp _).tsum_eq]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
      (summable_norm_sq_apply_of_hilbertBasis d.index d.basis hA)).symm
  have hineq := summed_scalar_hellinger d.values e.values c d.nonneg
    (spectral_value_le_one rho d.basis d.values d.eigen) e.nonneg
    (spectral_value_le_one sigma e.basis e.values e.eigen)
  rw [hleft, hleft, hdefect, henergy, hright, hmass rho d hr, hmass sigma e hs] at hineq
  rw [resolution_entropy rho d] at hineq
  apply ENNReal.le_of_add_le_add_right (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
  change (spectralEntropy rho + ENNReal.ofReal (∑' i, ‖A (d.basis i)‖ ^ 2)) + 1 ≤ _
  convert hineq using 1 <;> ac_rfl

/-- The actual noncommuting singular logarithmic energy bounds entropy with a trace-norm reward.
Both arguments are positive trace-one states; all full zero eigenspaces remain present. -/
theorem spectralEntropy_add_traceNorm_sq_le_energy (rho sigma : Reference H)
    (hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1) :
    spectralEntropy rho + ENNReal.ofReal (‖rho.1 - sigma.1‖ ^ 2 / 4) ≤
      spectralEnergy sigma rho.1 := by
  let R := CFC.sqrt rho.1.1
  let S := CFC.sqrt sigma.1.1
  let A := R - S
  let d := nativeResolution rho
  let D := ∑' i, ‖A (d.basis i)‖ ^ 2
  have hR : IsHilbertSchmidt R := sqrt_hs rho
  have hS : IsHilbertSchmidt S := sqrt_hs sigma
  have hA : IsHilbertSchmidt A := isHilbertSchmidt_sub hR hS
  have hRA : IsTraceClass (R * A) := isTraceClass_mul_of_isHilbertSchmidt hR hA
  have hAS : IsTraceClass (A * S) := isTraceClass_mul_of_isHilbertSchmidt hA hS
  have hRsum : (∑' i, ‖R (d.basis i)‖ ^ 2) = 1 := (sqrt_square_sum rho d.basis).trans hr
  have hSsum : (∑' i, ‖S (d.basis i)‖ ^ 2) = 1 := (sqrt_square_sum sigma d.basis).trans hs
  have hprod1 := traceNorm_mul_le_of_isHilbertSchmidt hR hA hRA d.basis
  have hprod2 := traceNorm_mul_le_of_isHilbertSchmidt hA hS hAS d.basis
  rw [hRsum, Real.sqrt_one, one_mul] at hprod1
  rw [hSsum, Real.sqrt_one, mul_one] at hprod2
  have heq : rho.1.1 - sigma.1.1 = R * A + A * S := by
    have hRR : R * R = rho.1.1 := CFC.sqrt_mul_sqrt_self _ rho.2.1
    have hSS : S * S = sigma.1.1 := CFC.sqrt_mul_sqrt_self _ sigma.2.1
    dsimp [A]
    noncomm_ring [hRR, hSS]
  have hbound : ‖rho.1 - sigma.1‖ ≤ 2 * Real.sqrt D := by
    rw [TraceClass.norm_eq_traceNorm]
    change traceNorm (rho.1.1 - sigma.1.1) _ ≤ _
    rw [_root_.traceNorm_transport heq]
    exact (traceNorm_add_le hRA hAS _).trans (by
      change traceNorm (R * A) hRA + traceNorm (A * S) hAS ≤ _
      linarith)
  have hDn : 0 ≤ D := tsum_nonneg (fun i => sq_nonneg _)
  have hsq : ‖rho.1 - sigma.1‖ ^ 2 ≤ (2 * Real.sqrt D) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbound
  have hreward : ‖rho.1 - sigma.1‖ ^ 2 / 4 ≤ D := by
    nlinarith [Real.sq_sqrt hDn]
  have hweak : spectralEntropy rho + ENNReal.ofReal (‖rho.1 - sigma.1‖ ^ 2 / 4) ≤
      spectralEntropy rho + ENNReal.ofReal D := add_le_add le_rfl (ENNReal.ofReal_le_ofReal hreward)
  exact hweak.trans (spectral_hellinger rho sigma d (nativeResolution sigma) hr hs)

#print axioms spectralEntropy_add_traceNorm_sq_le_energy
end QuantumLogEnergy
