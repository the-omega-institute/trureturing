/- GID: D5/S3/Quantum/Analysis/TraceClass/KernelEnergy
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/KernelEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual kernel projection mass and support obstruction for singular spectral logarithmic energy. -/

import D5.S3.Quantum.Analysis.TraceClass.SpectralEnergy
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
open scoped ComplexOrder InnerProductSpace ENNReal
namespace QuantumLogEnergy
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded orthogonal projection onto the actual closed kernel. -/
def kernelProjection (T : Reference H) : H →L[ℂ] H := T.1.1.ker.starProjection

/-- Actual trace mass of the bounded kernel projection against the first argument. -/
def kernelMass (T : Reference H) (rho : TraceClass H) : ℝ :=
  (TraceClass.tracePairing (kernelProjection T) rho).re

/-- The kernel projection is identity on a zero eigenvector and zero on every nonzero fiber. -/
theorem kernelProjection_eigenvector (T : Reference H) {w : Set H}
    (b : HilbertBasis w ℂ H) (s : w → ℝ)
    (heigen : ∀ i, T.1.1 (b i) = (s i : ℂ) • b i) (i : w) :
    kernelProjection T (b i) = if s i = 0 then b i else 0 := by
  classical
  by_cases hz : s i = 0
  · rw [if_pos hz]
    apply T.1.1.ker.starProjection_eq_self_iff.mpr
    change T.1.1 (b i) = 0
    simp [heigen i, hz]
  · rw [if_neg hz]
    have horth : b i ∈ T.1.1.kerᗮ := by
      apply (Submodule.mem_orthogonal' T.1.1.ker (b i)).mpr
      intro v hv
      have h := (T.1.1.nonneg_iff_isPositive.mp T.2.1).inner_left_eq_inner_right (b i) v
      have hv' : T.1.1 v = 0 := hv
      rw [heigen i, inner_smul_left, hv', inner_zero_right] at h
      simp only [Complex.conj_ofReal] at h
      exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hz)
    change (T.1.1.ker.orthogonalProjectionOnto (b i) : H) = 0
    rw [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal horth]
    rfl

/-- Unconditional trace evaluation identifies projection mass with the full zero-fiber diagonal. -/
theorem kernelMass_hasSum (T : Reference H) {w : Set H}
    (b : HilbertBasis w ℂ H) (s : w → ℝ)
    (heigen : ∀ i, T.1.1 (b i) = (s i : ℂ) • b i) (rho : TraceClass H) :
    HasSum (fun i => if s i = 0 then diagonal b rho i else 0) (kernelMass T rho) := by
  classical
  let K := T.1.1.ker
  let P := kernelProjection T
  have hdiag (i : w) : (⟪b i, (P * rho.1) (b i)⟫_ℂ).re =
      if s i = 0 then diagonal b rho i else 0 := by
    change (⟪b i, K.starProjection (rho.1 (b i))⟫_ℂ).re = _
    rw [← K.inner_starProjection_left_eq_right]
    change (⟪kernelProjection T (b i), rho.1 (b i)⟫_ℂ).re = _
    rw [kernelProjection_eigenvector T b s heigen i]
    split_ifs <;> simp [diagonal]
  have htc := TraceClass.isTraceClass_mul_coe P rho
  have hh := (summable_trace_diagonal_of_isTraceClass htc b).hasSum.mapL Complex.reCLM
  rw [← trace_eq_of_hilbertBasis htc b] at hh
  change HasSum (fun i => (⟪b i, (P * rho.1) (b i)⟫_ℂ).re) (trace (P * rho.1) htc).re at hh
  simpa only [hdiag, kernelMass, TraceClass.tracePairing_apply, P] using hh

private theorem spectralSeries_eq_top_of_zero_weight {w : Set H}
    (b : HilbertBasis w ℂ H) (s : w → ℝ) (rho : TraceClass H)
    (i : w) (hz : s i = 0) (hweight : 0 < diagonal b rho i) :
    spectralSeries b s rho = ∞ := by
  apply top_unique
  have h := ENNReal.le_tsum i (f := fun j => ENNReal.ofReal (diagonal b rho j) * singularLog (s j))
  have hn : ENNReal.ofReal (diagonal b rho i) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hweight)
  have he : ENNReal.ofReal (diagonal b rho i) * singularLog (s i) = ∞ := by
    rw [singularLog, if_pos hz, ENNReal.mul_top hn]
  rw [he] at h
  exact h

/-- A genuinely positive bounded kernel-projection mass forces infinite singular energy. -/
theorem spectralEnergy_eq_top_of_kernelMass_pos (T : Reference H) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) (hmass : 0 < kernelMass T rho) : spectralEnergy T rho = ∞ := by
  classical
  let d := nativeResolution T
  have hsum := kernelMass_hasSum T d.basis d.values d.eigen rho
  have hex : ∃ i, d.values i = 0 ∧ 0 < diagonal d.basis rho i := by
    by_contra h
    have hz : ∀ i, (if d.values i = 0 then diagonal d.basis rho i else 0) = 0 := by
      intro i
      split_ifs with hi
      · exact le_antisymm (not_lt.mp (fun hp => h ⟨i, hi, hp⟩))
          ((rho.1.nonneg_iff_isPositive.mp hrho).re_inner_nonneg_right (d.basis i))
      · rfl
    have hm : kernelMass T rho = 0 := by
      rw [← hsum.tsum_eq]
      simp only [hz, tsum_zero]
    linarith
  obtain ⟨i, hz, hw⟩ := hex
  exact spectralSeries_eq_top_of_zero_weight d.basis d.values rho i hz hw

private theorem positive_kills_of_diagonal_zero (rho : TraceClass H) (hrho : 0 ≤ rho.1)
    (v : H) (hdiag : (⟪v, rho.1 v⟫_ℂ).re = 0) : rho.1 v = 0 := by
  let R := CFC.sqrt rho.1
  have hR : IsSelfAdjoint R := .of_nonneg (CFC.sqrt_nonneg rho.1)
  have hRR : R * R = rho.1 := CFC.sqrt_mul_sqrt_self rho.1 hrho
  have hnorm : ‖R v‖ ^ 2 = 0 := by
    have hinner : ⟪v, rho.1 v⟫_ℂ = ⟪R v, R v⟫_ℂ := by
      have hstar : ContinuousLinearMap.adjoint R = R :=
        (ContinuousLinearMap.star_eq_adjoint R).symm.trans hR
      rw [← hRR, ContinuousLinearMap.mul_apply,
        ← ContinuousLinearMap.adjoint_inner_left R (R v) v, hstar]
    rw [hinner, inner_self_eq_norm_sq_to_K] at hdiag
    exact_mod_cast hdiag
  have hzero : R v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  rw [← hRR, ContinuousLinearMap.mul_apply, hzero, map_zero]

/-- Finite energy forces the actual kernel inclusion. Support inclusion alone is not a finiteness criterion. -/
theorem ker_le_ker_of_spectralEnergy_lt_top (T : Reference H) (rho : TraceClass H)
    (hrho : 0 ≤ rho.1) (hfin : spectralEnergy T rho < ∞) :
    T.1.1.ker ≤ rho.1.ker := by
  classical
  let d := nativeResolution T
  have hkill (i : d.index) (hz : d.values i = 0) : rho.1 (d.basis i) = 0 := by
    apply positive_kills_of_diagonal_zero rho hrho
    change diagonal d.basis rho i = 0
    by_contra hne
    have hp : 0 < diagonal d.basis rho i := lt_of_le_of_ne
      ((rho.1.nonneg_iff_isPositive.mp hrho).re_inner_nonneg_right (d.basis i)) (Ne.symm hne)
    have hinf := spectralSeries_eq_top_of_zero_weight d.basis d.values rho i hz hp
    exact (ne_of_lt hfin) hinf
  have hzero : rho.1 * kernelProjection T = 0 := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr d.basis.dense_span)
    rintro _ ⟨i, rfl⟩
    rw [ContinuousLinearMap.mul_apply, kernelProjection_eigenvector T d.basis d.values d.eigen i]
    split_ifs with hz
    · exact hkill i hz
    · exact map_zero _
  intro v hv
  change rho.1 v = 0
  have hPv : kernelProjection T v = v := T.1.1.ker.starProjection_eq_self_iff.mpr hv
  have heq := congrArg (fun A : H →L[ℂ] H => A v) hzero
  simpa only [ContinuousLinearMap.mul_apply, hPv, ContinuousLinearMap.zero_apply] using heq

end QuantumLogEnergy
