/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedSpectralEntropy
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/BalancedSpectralEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact density-to-reference operator correspondence, the extended spectral half-cap floor, and a half-projection entropy criterion. -/
/-
admission_basis: escape-witness
This mixed Fock application module owns densityReference, the odd-occupation
attenuator entropy bounds and the Fock density half-projection criterion.
Its instance classification includes these physical channel dependencies;
spectral_entropy_lower_of_half still quantifies over every complete complex
Hilbert space and is consumed by balanced_odd_spectral_entropy_lower.
spectral_entropy_lower_of_half uses the actual complete spectral resolution,
trace-one eigenvalue sum and ENNReal termwise comparison. The densityReference
adapter contains exactly the original density operator; no entropy identity
is assumed. density_entropy_eq_log_two_of_square derives its spectral values
from an operator polynomial. utility: none denotes analytic spectral results;
no finite support, rank, energy or entropy premise is added. No equivalence
with FockAttenuator.Entropy.vonNeumannEntropy is asserted.
The balanced one-photon all-density spectral minimum and every-coherent
attainment are attributed to Zixuan He, The energy cost of optical noise,
v1.0, DOI 10.5281/zenodo.23629201, Theorem 2 and Appendix A.2-A.3.
This is formal library integration of that written result; no literature
resolution or priority for the odd-occupation application is claimed.
-/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.BalancedHalfCap
import D5.S3.Quantum.Analysis.TraceClass.SpectralEnergy
import D5.S3.Quantum.Analysis.TraceClass.FiniteBlocks

noncomputable section
open scoped ComplexOrder InnerProductSpace ENNReal
open QuantumLogEnergy
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.BalancedHalfCap
open Bargmann Attenuator

private def fockBasis : HilbertBasis ℕ ℂ Fock := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fock)

private theorem fockBasis_eq (n : ℕ) : fockBasis n = lp.single 2 n (1 : ℂ) := by
  apply fockBasis.repr.injective
  simpa only [fockBasis, LinearIsometryEquiv.coe_refl, id_eq] using fockBasis.repr_self n

private theorem density_nonneg (ρ : DensityOperator) : 0 ≤ ρ.operator :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr ρ.positive

private theorem density_isTraceClass (ρ : DensityOperator) : IsTraceClass ρ.operator := by
  let e := Equiv.ofInjective fockBasis fockBasis.orthonormal.linearIndependent.injective
  refine ⟨Set.range fockBasis, TraceClassFiniteBlocks.setBasis fockBasis, ?_⟩
  rw [CFC.abs_of_nonneg _ (density_nonneg ρ)]
  apply e.summable_iff.mp
  simpa only [Function.comp_def, TraceClassFiniteBlocks.setBasis_apply,
    e, Equiv.ofInjective_apply, fockBasis_eq] using ρ.trace_one.summable

private theorem density_trace (ρ : DensityOperator) :
    (trace ρ.operator (density_isTraceClass ρ)).re = 1 := by
  rw [TraceClassFiniteBlocks.trace_on_basis fockBasis (density_isTraceClass ρ)]
  have hs := summable_trace_diagonal_of_isTraceClass (density_isTraceClass ρ)
    (TraceClassFiniteBlocks.setBasis fockBasis)
  let e := Equiv.ofInjective fockBasis fockBasis.orthonormal.linearIndependent.injective
  have hs' : Summable (fun n : ℕ => ⟪fockBasis n, ρ.operator (fockBasis n)⟫_ℂ) := by
    simpa [Function.comp_def, TraceClassFiniteBlocks.setBasis_apply, e] using
      hs.comp_injective e.injective
  rw [show (∑' n, ⟪fockBasis n, ρ.operator (fockBasis n)⟫_ℂ).re =
      ∑' n, (⟪fockBasis n, ρ.operator (fockBasis n)⟫_ℂ).re from
    Complex.reCLM.map_tsum hs']
  simpa only [fockBasis_eq] using ρ.trace_one.tsum_eq

/-- The native positive trace-class contraction carries exactly the density operator. -/
def densityReference (ρ : DensityOperator) : Reference Fock :=
  ⟨⟨ρ.operator, density_isTraceClass ρ⟩, density_nonneg ρ,
    density_le_one _ (density_nonneg ρ) (density_trace ρ)⟩

/-- All eigenvalues are bounded by the actual scalar operator cap. -/
private theorem eigen_le_cap {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : Reference H) (R : SpectralResolution T) (c : ℝ)
    (hcap : T.1.1 ≤ (c : ℂ) • (1 : H →L[ℂ] H)) (i : R.index) :
    R.values i ≤ c := by
  have h := (ContinuousLinearMap.le_def.mp hcap).re_inner_nonneg_right (R.basis i)
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, R.eigen i,
    inner_smul_right, inner_self_eq_norm_sq_to_K, R.basis.orthonormal.1 i,
    RCLike.ofReal_one, one_pow, mul_one] at h
  change 0 ≤ ((c : ℂ) - (R.values i : ℂ)).re at h
  simpa only [Complex.sub_re, Complex.ofReal_re, sub_nonneg] using h

/-- The same operator's extended spectral entropy has the half-cap floor. -/
theorem spectral_entropy_lower_of_half {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : Reference H)
    (ht : (trace T.1.1 (TraceClass.isTraceClass_coe T.1)).re = 1)
    (hcap : T.1.1 ≤ ((1 / 2 : ℝ) : ℂ) • (1 : H →L[ℂ] H)) :
    ENNReal.ofReal (Real.log 2) ≤ spectralEntropy T := by
  let R := nativeResolution T
  have hdiag (i : R.index) : diagonal R.basis T.1 i = R.values i := by
    unfold diagonal
    rw [R.eigen i, inner_smul_right, inner_self_eq_norm_sq_to_K, R.basis.orthonormal.1 i]
    simp
  have hs : HasSum R.values 1 := by
    have h := diagonal_hasSum R.basis T.1
    rw [ht] at h
    exact h.congr_fun (fun i => (hdiag i).symm)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmass := hs.mul_right (Real.log 2)
  have hnonneg (i : R.index) : 0 ≤ R.values i * Real.log 2 := mul_nonneg (R.nonneg i) hlog
  calc
    ENNReal.ofReal (Real.log 2) = ∑' i, ENNReal.ofReal (R.values i * Real.log 2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hmass.summable, hmass.tsum_eq, one_mul]
    _ ≤ spectralEntropy T := by
      apply ENNReal.tsum_le_tsum
      intro i
      apply ENNReal.ofReal_le_ofReal
      by_cases hz : R.values i = 0
      · change R.values i * Real.log 2 ≤ -R.values i * Real.log (R.values i)
        simp [hz]
      · have h := Real.log_le_log (lt_of_le_of_ne (R.nonneg i) (Ne.symm hz))
          (eigen_le_cap T R (1/2) hcap i)
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub] at h
        change R.values i * Real.log 2 ≤ -R.values i * Real.log (R.values i)
        simpa only [mul_neg, neg_mul, neg_neg] using mul_le_mul_of_nonneg_left (neg_le_neg h) (R.nonneg i)

/-- The lower bound on the original output for every density input and every odd Fock environment. -/
theorem balanced_odd_spectral_entropy_lower (n : ℕ) (hn : Odd n) (ρ : DensityOperator) :
    ENNReal.ofReal (Real.log 2) ≤
      spectralEntropy (densityReference (attenuator (1/2) balanced (pointMassEnvironment n) ρ)) :=
  spectral_entropy_lower_of_half _ (density_trace _) (balanced_odd_attenuator_le_half n hn ρ)

/-- The all-density balanced one-photon lower bound. -/
theorem balanced_one_photon_spectral_entropy_lower (ρ : DensityOperator) :
    ENNReal.ofReal (Real.log 2) ≤
      spectralEntropy (densityReference (attenuator (1/2) balanced (pointMassEnvironment 1) ρ)) :=
  balanced_odd_spectral_entropy_lower 1 (by decide) ρ

/-- A trace-one density whose nonzero eigenvalues all equal one half has exact entropy log 2. -/
theorem density_entropy_eq_log_two_of_square (ρ : DensityOperator)
    (hp : ρ.operator * ρ.operator = ((1/2 : ℝ) : ℂ) • ρ.operator) :
    spectralEntropy (densityReference ρ) = ENNReal.ofReal (Real.log 2) := by
  let T := densityReference ρ
  let R := nativeResolution T
  have hdiag (i : R.index) : diagonal R.basis T.1 i = R.values i := by
    unfold diagonal
    rw [R.eigen i, inner_smul_right, inner_self_eq_norm_sq_to_K, R.basis.orthonormal.1 i]
    simp
  have hs : HasSum R.values 1 := by
    have h := diagonal_hasSum R.basis T.1
    change HasSum _ (trace ρ.operator (density_isTraceClass ρ)).re at h
    rw [density_trace] at h
    exact h.congr_fun (fun i => (hdiag i).symm)
  have hval (i : R.index) : R.values i = 0 ∨ R.values i = 1/2 := by
    have hh := congrArg (fun A : Fock →L[ℂ] Fock => A (R.basis i)) hp
    change T.1.1 (T.1.1 (R.basis i)) = ((1/2 : ℝ) : ℂ) • T.1.1 (R.basis i) at hh
    rw [R.eigen i, map_smul, R.eigen i, smul_smul, smul_smul] at hh
    have hn : R.basis i ≠ 0 := by
      exact norm_ne_zero_iff.mp (by rw [R.basis.orthonormal.1 i]; norm_num)
    have hh' := smul_left_injective ℂ hn hh
    have hr : R.values i * R.values i = (1/2 : ℝ) * R.values i := by exact_mod_cast hh'
    have hzero : R.values i * (R.values i - 1/2) = 0 := by nlinarith only [hr]
    exact (mul_eq_zero.mp hzero).imp id sub_eq_zero.mp
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmass := hs.mul_right (Real.log 2)
  have hnonneg (i : R.index) : 0 ≤ R.values i * Real.log 2 := mul_nonneg (R.nonneg i) hlog
  change (∑' i, ENNReal.ofReal (-R.values i * Real.log (R.values i))) = _
  calc
    _ = ∑' i, ENNReal.ofReal (R.values i * Real.log 2) := by
      apply tsum_congr
      intro i
      rcases hval i with h | h
      · simp [h]
      · rw [h, Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub, neg_mul_neg]
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hmass.summable, hmass.tsum_eq, one_mul]

end D5.S3.Quantum.QuantumChannels.FockAttenuator.BalancedHalfCap
