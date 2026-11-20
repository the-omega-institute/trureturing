import D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget
import D5.S3.Resource.LogDet.PathSpectralClassical
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Finite spectral Jensen for density states with contained support. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix BigOperators CStarAlgebra ComplexOrder MatrixOrder Classical
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Recovery.PetzSpectralCoordinates
open D5.S3.Quantum.Recovery
open D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget (trace_rank_one_product)

namespace PetzPostselectionSpectralJensen

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev stateMatrix (p : DensityState n) : Matrix n n ℂ := CStarMatrix.ofMatrix.symm p.1

private theorem state_pos (p : DensityState n) : (stateMatrix p).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm p.2.1)

def eigenvalue (p : DensityState n) : n → ℝ := (state_pos p).1.eigenvalues

abbrev PositiveMode (p : DensityState n) := {i : n // 0 < eigenvalue p i}

private def eigenvector (p : DensityState n) (i : n) : n → ℂ :=
  fun k => (state_pos p).1.eigenvectorBasis i k

private def overlap (p q : DensityState n) (i j : n) : ℝ :=
  ‖star (eigenvector q j) ⬝ᵥ eigenvector p i‖ ^ 2

/-- The rank-one refinement of the positive-support weight γ Tr(Pγ Qλ). -/
def spectralWeight (p q : DensityState n) (ij : PositiveMode p × PositiveMode q) : ℝ :=
  eigenvalue p ij.1.1 * overlap p q ij.1.1 ij.2.1

theorem spectralWeight_eq_trace (p q : DensityState n)
    (ij : PositiveMode p × PositiveMode q) :
    spectralWeight p q ij =
      eigenvalue p ij.1.1 *
        (Matrix.trace
          (Matrix.vecMulVec (eigenvector p ij.1.1) (star (eigenvector p ij.1.1)) *
            Matrix.vecMulVec (eigenvector q ij.2.1) (star (eigenvector q ij.2.1)))).re := by
  rw [trace_rank_one_product]
  rfl

theorem spectralWeight_nonneg (p q : DensityState n)
    (ij : PositiveMode p × PositiveMode q) : 0 ≤ spectralWeight p q ij :=
  mul_nonneg ij.1.2.le (sq_nonneg _)

omit [DecidableEq n] in
private theorem sum_positive_eq (e f : n → ℝ) (he : ∀ i, 0 ≤ e i)
    (hz : ∀ i, e i = 0 → f i = 0) :
    (∑ i : {i : n // 0 < e i}, f i.1) = ∑ i, f i := by
  classical
  have hzero : (∑ i : {i : n // ¬ 0 < e i}, f i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hz i.1 (le_antisymm (le_of_not_gt i.2) (he i.1))
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < e i) f
  rw [hzero, add_zero] at h
  exact h

private theorem overlap_row (p q : DensityState n) (support : SupportContained p q)
    (i : PositiveMode p) : ∑ j : PositiveMode q, overlap p q i.1 j.1 = 1 := by
  classical
  calc
    _ = ∑ j : n, overlap p q i.1 j := by
      apply sum_positive_eq (eigenvalue q)
      · exact (state_pos q).eigenvalues_nonneg
      · intro j hj
        have hzero : star (eigenvector q j) ⬝ᵥ eigenvector p i.1 = 0 :=
          kernel_eigenvector_overlap_zero
            (stateMatrix p) (stateMatrix q) (state_pos p).1 (state_pos q).1
            (fun _ hv => support hv) j hj i.1 i.2
        simp only [overlap, hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    _ = 1 := by
      have h := (state_pos q).1.eigenvectorBasis.sum_sq_norm_inner_right
        ((state_pos p).1.eigenvectorBasis i.1)
      rw [(state_pos p).1.eigenvectorBasis.orthonormal.1 i.1, one_pow] at h
      convert h using 1
      apply Finset.sum_congr rfl
      intro j _
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      unfold overlap eigenvector
      rw [dotProduct_comm]

private theorem sum_weighted_rows (p q : DensityState n) (support : SupportContained p q)
    (f : n → ℝ) :
    (∑ i : PositiveMode p, ∑ j : PositiveMode q, f i.1 * overlap p q i.1 j.1) =
      ∑ i : PositiveMode p, f i.1 := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, overlap_row p q support i, mul_one]

theorem sum_spectralWeight (p q : DensityState n) (support : SupportContained p q) :
    ∑ ij : PositiveMode p × PositiveMode q, spectralWeight p q ij = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  change (∑ i : PositiveMode p, ∑ j : PositiveMode q,
    eigenvalue p i.1 * overlap p q i.1 j.1) = 1
  rw [sum_weighted_rows p q support, sum_positive_eq (eigenvalue p) (eigenvalue p)
    (state_pos p).eigenvalues_nonneg (fun _ h => h)]
  have h := congrArg Complex.re (state_pos p).1.trace_eq_sum_eigenvalues
  have ht : (stateMatrix p).trace = 1 := p.2.2
  rw [ht] at h
  simpa only [Complex.one_re, Complex.re_sum, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re, eigenvalue] using h.symm

private theorem trace_supported_product (p q : DensityState n) (f g : ℝ → ℝ)
    (hf : f 0 = 0) (hg : g 0 = 0) :
    (cfc f (stateMatrix p) * cfc g (stateMatrix q)).trace.re =
      ∑ i : PositiveMode p, ∑ j : PositiveMode q,
        f (eigenvalue p i.1) * g (eigenvalue q j.1) * overlap p q i.1 j.1 := by
  classical
  rw [cfc_supported_sum (stateMatrix p) (state_pos p) f hf,
    cfc_supported_sum (stateMatrix q) (state_pos q) g hg, Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Matrix.trace_sum,
    Matrix.trace_smul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [trace_rank_one_product]
  unfold eigenvalue overlap eigenvector
  ring

private theorem trace_self_log (p : DensityState n) :
    (stateMatrix p * cfc Real.log (stateMatrix p)).trace.re =
      ∑ i : PositiveMode p, eigenvalue p i.1 * Real.log (eigenvalue p i.1) := by
  let A := stateMatrix p
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A (state_pos p).1.isSelfAdjoint
  calc
    _ = (cfc (fun x : ℝ => x * Real.log x) A).trace.re := by
      rw [cfc_mul (fun x : ℝ => x) Real.log A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _), hid]
    _ = _ := by
      rw [D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum A (state_pos p).1]
      exact (sum_positive_eq (eigenvalue p) (fun i => eigenvalue p i * Real.log (eigenvalue p i))
        (state_pos p).eigenvalues_nonneg (fun i h => by rw [h, zero_mul])).symm

private theorem log_to_state (p : DensityState n) :
    CStarMatrix.ofMatrix (cfc Real.log (stateMatrix p)) = CFC.log p.1 := by
  exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log _
    ((stateMatrix p).finite_real_spectrum.continuousOn _)
    CStarMatrix.ofMatrixL.continuous (state_pos p).1 (by exact (state_pos p).1)

theorem weighted_logRatio_eq_entropy (p q : DensityState n) (support : SupportContained p q) :
    (∑ ij : PositiveMode p × PositiveMode q, spectralWeight p q ij *
      Real.log (eigenvalue p ij.1.1 / eigenvalue q ij.2.1)) =
        finiteTraceLogRelativeEntropy p q := by
  classical
  have hcross := trace_supported_product p q (fun x => x) Real.log rfl Real.log_zero
  rw [cfc_id' ℝ (stateMatrix p) (state_pos p).1.isSelfAdjoint] at hcross
  unfold finiteTraceLogRelativeEntropy
  rw [← log_to_state p, ← log_to_state q]
  change _ = (stateMatrix p *
    (cfc Real.log (stateMatrix p) - cfc Real.log (stateMatrix q))).trace.re
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, trace_self_log, hcross,
    Fintype.sum_prod_type]
  calc
    _ = ∑ i : PositiveMode p, ∑ j : PositiveMode q,
        (eigenvalue p i.1 * Real.log (eigenvalue p i.1) * overlap p q i.1 j.1 -
          eigenvalue p i.1 * Real.log (eigenvalue q j.1) * overlap p q i.1 j.1) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change (eigenvalue p i.1 * overlap p q i.1 j.1) *
        Real.log (eigenvalue p i.1 / eigenvalue q j.1) = _
      rw [Real.log_div i.2.ne' j.2.ne']
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib]
      rw [sum_weighted_rows p q support (fun i => eigenvalue p i * Real.log (eigenvalue p i))]

private theorem threeHalves_eq_mul_sqrt (x : ℝ) (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add_of_nonneg hx zero_le_one (by norm_num), Real.rpow_one]

private theorem trace_threeHalves_inverseSqrt_eq_sum (p q : DensityState n) :
    (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) (stateMatrix p) *
      spectralInverseSqrt (stateMatrix q)).trace.re =
      ∑ ij : PositiveMode p × PositiveMode q, spectralWeight p q ij *
        Real.exp (Real.log (eigenvalue p ij.1.1 / eigenvalue q ij.2.1) / 2) := by
  classical
  unfold spectralInverseSqrt
  rw [trace_supported_product p q (fun x : ℝ => x ^ (3 / 2 : ℝ)) (fun x => (Real.sqrt x)⁻¹)
      (Real.zero_rpow (by norm_num)) (by simp),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change eigenvalue p i.1 ^ (3 / 2 : ℝ) * (Real.sqrt (eigenvalue q j.1))⁻¹ *
    overlap p q i.1 j.1 =
    (eigenvalue p i.1 * overlap p q i.1 j.1) *
      Real.exp (Real.log (eigenvalue p i.1 / eigenvalue q j.1) / 2)
  have hexp : Real.exp (Real.log (eigenvalue p i.1 / eigenvalue q j.1) / 2) =
      Real.sqrt (eigenvalue p i.1 / eigenvalue q j.1) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos i.2 j.2)]
    congr 1
    ring
  rw [hexp, Real.sqrt_div i.2.le, threeHalves_eq_mul_sqrt _ i.2.le, div_eq_mul_inv]
  ring

/-- Jensen on the positive spectral overlaps, with the repository's finite entropy
and the same inverse square root used in ordinary Petz recovery. -/
theorem exp_half_entropy_le_trace_threeHalves_inverseSqrt
    (p q : DensityState n) (support : SupportContained p q) :
    Real.exp (finiteTraceLogRelativeEntropy p q / 2) ≤
      (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) (stateMatrix p) *
        spectralInverseSqrt (stateMatrix q)).trace.re := by
  classical
  have hhalf :
      (∑ ij : PositiveMode p × PositiveMode q, spectralWeight p q ij *
        (Real.log (eigenvalue p ij.1.1 / eigenvalue q ij.2.1) / 2)) =
        finiteTraceLogRelativeEntropy p q / 2 := by
    rw [← weighted_logRatio_eq_entropy p q support, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ij _
    ring
  have hj := ConvexOn.map_sum_le convexOn_exp (t := Finset.univ)
    (w := spectralWeight p q)
    (p := fun ij => Real.log (eigenvalue p ij.1.1 / eigenvalue q ij.2.1) / 2)
    (fun ij _ => spectralWeight_nonneg p q ij) (sum_spectralWeight p q support)
    (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, hhalf, ← trace_threeHalves_inverseSqrt_eq_sum p q] using hj

end PetzPostselectionSpectralJensen
