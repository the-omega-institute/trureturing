/- GID: D5/S3/Quantum/Divergence/SpectralCeilingRelativeEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/SpectralCeilingRelativeEntropy
   mirror-E: none(waiver:actual-matrix-spectral-ceiling)
   anchors: []
   utility: none
   digest: Spectral-ceiling logarithmic gaps on the route to actual matrix entropy gains. -/

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic
import D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget
import D5.S3.Resource.LogDet.PathSpectralClassical

/-! proof_shape: content; admission_basis: escape-witness.
The complete full-spectrum overlap identifies the scalar logarithmic remainder
with the actual noncommuting Hilbert--Schmidt gap, including every kernel mode.
The live application is the entropy gain of the actual P / KPK mixture;
its exact application is checked transiently and explained in the owning Scribe.
No independent scalar-content, physical sharpness, or novelty claim is made. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Recovery.PetzSpectralCoordinates
open D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

namespace D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy

private theorem scalar_log_gap {M x y : ℝ} (hM : 0 < M)
    (hx0 : 0 ≤ x) (hxM : x ≤ M) (hy0 : 0 < y) (hyM : y ≤ M) :
    (x - y) ^ 2 / (2 * M) ≤ x * Real.log x - x * Real.log y - x + y := by
  let f : ℝ → ℝ := fun t =>
    t * Real.log t - t * Real.log y - t + y - (t - y) ^ 2 / (2 * M)
  have hcont : Continuous f := by
    exact (((Real.continuous_mul_log.sub (continuous_id.mul continuous_const)).sub
      continuous_id).add continuous_const).sub
        (((continuous_id.sub continuous_const).pow 2).div_const (2 * M))
  have hd1 (t : ℝ) (ht : 0 < t) :
      HasDerivAt f (Real.log t - Real.log y - (t - y) / M) t := by
    convert ((((Real.hasDerivAt_mul_log ht.ne').sub
      ((hasDerivAt_id t).mul_const (Real.log y))).sub (hasDerivAt_id t)).add_const y).sub
        ((((hasDerivAt_id t).sub_const y).pow 2).div_const (2 * M)) using 1
    all_goals first
      | rfl
      | (dsimp [f]; field_simp [hM.ne']; ring)
  have hd2 (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun s : ℝ => Real.log s - Real.log y - (s - y) / M)
        (1 / t - 1 / M) t := by
    convert ((Real.hasDerivAt_log ht.ne').sub_const (Real.log y)).sub
      (((hasDerivAt_id t).sub_const y).div_const M) using 1
    all_goals first
      | rfl
      | simp [one_div]
  have hconv : ConvexOn ℝ (Icc 0 M) f := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (f := f)
      (f' := fun t => Real.log t - Real.log y - (t - y) / M)
      (f'' := fun t => 1 / t - 1 / M) (convex_Icc 0 M) hcont.continuousOn ?_ ?_ ?_
    · intro t ht
      simp only [interior_Icc, mem_Ioo] at ht
      exact (hd1 t ht.1).hasDerivWithinAt
    · intro t ht
      simp only [interior_Icc, mem_Ioo] at ht
      exact (hd2 t ht.1).hasDerivWithinAt
    · intro t ht
      simp only [interior_Icc, mem_Ioo] at ht
      exact sub_nonneg.mpr (one_div_le_one_div_of_le ht.1 ht.2.le)
  have hdy : HasDerivAt f 0 y := by simpa using hd1 y hy0
  have hfy : f y = 0 := by dsimp [f]; ring
  have hmin : f y ≤ f x := by
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · have hs := hconv.slope_le_of_hasDerivAt ⟨hx0, hxM⟩ ⟨hy0.le, hyM⟩ hxy hdy
      rw [slope_def_field] at hs
      have hh := (div_le_iff₀ (sub_pos.mpr hxy)).mp hs
      linarith
    · exact le_of_eq (congrArg f hxy.symm)
    · have hs := hconv.le_slope_of_hasDerivAt ⟨hy0.le, hyM⟩ ⟨hx0, hxM⟩ hyx hdy
      rw [slope_def_field] at hs
      have hh := (le_div_iff₀ (sub_pos.mpr hyx)).mp hs
      linarith
  rw [hfy] at hmin
  dsimp [f] at hmin
  linarith only [hmin]

private def overlap {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (i j : n) : ℝ :=
  ‖star (fun x => hB.eigenvectorBasis j x) ⬝ᵥ
    (fun x => hA.eigenvectorBasis i x)‖ ^ 2

private theorem overlap_row {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i : n) :
    ∑ j, overlap hA hB i j = 1 := by
  have h := hB.eigenvectorBasis.sum_sq_norm_inner_right (hA.eigenvectorBasis i)
  rw [hA.eigenvectorBasis.orthonormal.1 i, one_pow] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  dsimp [overlap]
  rw [dotProduct_comm]

private theorem overlap_column {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (j : n) :
    ∑ i, overlap hA hB i j = 1 := by
  have h := hA.eigenvectorBasis.sum_sq_norm_inner_left (hB.eigenvectorBasis j)
  rw [hB.eigenvectorBasis.orthonormal.1 j, one_pow] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  dsimp [overlap]
  rw [dotProduct_comm]

private theorem trace_cfc_product {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) :
    (cfc f A * cfc g B).trace.re =
      ∑ i, ∑ j, f (hA.eigenvalues i) * g (hB.eigenvalues j) * overlap hA hB i j := by
  classical
  rw [cfc_spectral_sum A hA f, cfc_spectral_sum B hB g]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Matrix.trace_sum, Matrix.trace_smul, Finset.smul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [trace_rank_one_product]
  dsimp [overlap]
  ring

private theorem overlap_zero_of_support {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (support : ∀ v, B *ᵥ v = 0 → A *ᵥ v = 0)
    (i j : n) (hj : hB.1.eigenvalues j = 0) :
    hA.1.eigenvalues i * overlap hA.1 hB.1 i j = 0 := by
  by_cases hi : hA.1.eigenvalues i = 0
  · rw [hi, zero_mul]
  have hc := D5.S3.Quantum.Divergence.CanonicalChannelDPI.kernel_eigenvector_overlap_zero
    A B hA.1 hB.1 support j hj i (lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hi))
  simp only [overlap, hc, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]

private theorem eigenvalue_le_ceiling {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (M : ℝ)
    (ceiling : A ≤ (M : ℂ) • (1 : Matrix n n ℂ)) (i : n) :
    hA.eigenvalues i ≤ M := by
  let v : n → ℂ := fun x => hA.eigenvectorBasis i x
  have hv : star v ⬝ᵥ v = 1 := by
    calc
      _ = inner ℂ (hA.eigenvectorBasis i) (hA.eigenvectorBasis i) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        exact dotProduct_comm _ _
      _ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1 i]
        simp
  have h := (Complex.nonneg_iff.mp
    ((Matrix.le_iff.mp ceiling).dotProduct_mulVec_nonneg v)).1
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hA.mulVec_eigenvectorBasis i, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, hv] at h
  simpa [Complex.real_smul, smul_eq_mul, sub_nonneg] using h

private theorem trace_self_cfc {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (A * cfc f A).trace.re = ∑ i, hA.eigenvalues i * f (hA.eigenvalues i) := by
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id ℝ A hA
  calc
    _ = (cfc (fun x : ℝ => x) A * cfc f A).trace.re := by rw [hid]
    _ = (cfc (fun x : ℝ => x * f x) A).trace.re := by
      rw [cfc_mul (fun x : ℝ => x) f A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ = _ := D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum A hA _

private theorem overlap_weighted_row {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (f : n → ℝ) :
    ∑ i, ∑ j, f i * overlap hA hB i j = ∑ i, f i := by
  simp_rw [← Finset.mul_sum, overlap_row, mul_one]

private theorem overlap_weighted_column {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (g : n → ℝ) :
    ∑ i, ∑ j, g j * overlap hA hB i j = ∑ j, g j := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, overlap_column, mul_one]

private theorem trace_square_gap {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((A - B)ᴴ * (A - B)).trace.re =
      ∑ i, ∑ j, (hA.eigenvalues i - hB.eigenvalues j) ^ 2 * overlap hA hB i j := by
  have hA2 : (A * A).trace.re = ∑ i, (hA.eigenvalues i) ^ 2 := by
    have hid : cfc (fun x : ℝ => x) A = A := cfc_id ℝ A hA
    have h := trace_self_cfc A hA (fun x => x)
    rw [hid] at h
    simpa only [pow_two] using h
  have hB2 : (B * B).trace.re = ∑ j, (hB.eigenvalues j) ^ 2 := by
    have hid : cfc (fun x : ℝ => x) B = B := cfc_id ℝ B hB
    have h := trace_self_cfc B hB (fun x => x)
    rw [hid] at h
    simpa only [pow_two] using h
  have hAB : (A * B).trace.re =
      ∑ i, ∑ j, hA.eigenvalues i * hB.eigenvalues j * overlap hA hB i j := by
    have hidA : cfc (fun x : ℝ => x) A = A := cfc_id ℝ A hA
    have hidB : cfc (fun x : ℝ => x) B = B := cfc_id ℝ B hB
    have h := trace_cfc_product A B hA hB (fun x => x) (fun x => x)
    rwa [hidA, hidB] at h
  have hexp : ((A - B)ᴴ * (A - B)).trace.re =
      (A * A).trace.re - 2 * (A * B).trace.re + (B * B).trace.re := by
    rw [Matrix.conjTranspose_sub, hA.eq, hB.eq, sub_mul, mul_sub, mul_sub,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
      Complex.sub_re, Complex.sub_re, Complex.sub_re,
      Matrix.trace_mul_comm B A]
    ring
  rw [hexp, hA2, hB2, hAB]
  symm
  have hscale : (∑ i, ∑ j,
      2 * (hA.eigenvalues i * hB.eigenvalues j * overlap hA hB i j)) =
      2 * (∑ i, ∑ j, hA.eigenvalues i * hB.eigenvalues j * overlap hA hB i j) := by
    simp only [Finset.mul_sum]
  calc
    _ = ∑ i, ∑ j, ((hA.eigenvalues i) ^ 2 * overlap hA hB i j -
        2 * (hA.eigenvalues i * hB.eigenvalues j * overlap hA hB i j) +
        (hB.eigenvalues j) ^ 2 * overlap hA hB i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [overlap_weighted_row, overlap_weighted_column, hscale]

set_option maxHeartbeats 1000000 in
/-- A common Loewner spectral ceiling gives the Hilbert--Schmidt remainder in
Klein's inequality for arbitrary positive semidefinite matrices. The support
condition includes every zero eigenspace; commutation and invertibility are
not assumed. The trace correction allows unequal matrix traces. -/
theorem actual_matrix_spectral_ceiling_strong_klein
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (M : ℝ) (hM : 0 < M)
    (ceilingA : A ≤ (M : ℂ) • (1 : Matrix n n ℂ))
    (ceilingB : B ≤ (M : ℂ) • (1 : Matrix n n ℂ))
    (support : ∀ v, B *ᵥ v = 0 → A *ᵥ v = 0) :
    ((A - B)ᴴ * (A - B)).trace.re / (2 * M) ≤
      (A * (cfc Real.log A - cfc Real.log B)).trace.re - A.trace.re + B.trace.re := by
  classical
  have hpair (i j : n) :
      ((hA.1.eigenvalues i - hB.1.eigenvalues j) ^ 2 / (2 * M)) *
          overlap hA.1 hB.1 i j ≤
        (hA.1.eigenvalues i * Real.log (hA.1.eigenvalues i) -
          hA.1.eigenvalues i * Real.log (hB.1.eigenvalues j) -
          hA.1.eigenvalues i + hB.1.eigenvalues j) * overlap hA.1 hB.1 i j := by
    by_cases hj : hB.1.eigenvalues j = 0
    · rcases mul_eq_zero.mp (overlap_zero_of_support A B hA hB support i j hj)
        with hi | hw
      · simp [hi, hj]
      · simp [hw]
    · exact mul_le_mul_of_nonneg_right
        (scalar_log_gap hM (hA.eigenvalues_nonneg i)
          (eigenvalue_le_ceiling hA.1 M ceilingA i)
          (lt_of_le_of_ne (hB.eigenvalues_nonneg j) (Ne.symm hj))
          (eigenvalue_le_ceiling hB.1 M ceilingB j)) (sq_nonneg _)
  have hsummed := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpair i j
  have hleft : (∑ i, ∑ j,
      ((hA.1.eigenvalues i - hB.1.eigenvalues j) ^ 2 / (2 * M)) *
        overlap hA.1 hB.1 i j) = ((A - B)ᴴ * (A - B)).trace.re / (2 * M) := by
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    rw [trace_square_gap A B hA.1 hB.1]
  have hself := trace_self_cfc A hA.1 Real.log
  have hcross : (A * cfc Real.log B).trace.re =
      ∑ i, ∑ j, hA.1.eigenvalues i * Real.log (hB.1.eigenvalues j) *
        overlap hA.1 hB.1 i j := by
    have hid : cfc (fun x : ℝ => x) A = A := cfc_id ℝ A hA.1
    have h := trace_cfc_product A B hA.1 hB.1 (fun x => x) Real.log
    rwa [hid] at h
  have htraceA : A.trace.re = ∑ i, hA.1.eigenvalues i := by
    simpa using congrArg Complex.re hA.1.trace_eq_sum_eigenvalues
  have htraceB : B.trace.re = ∑ j, hB.1.eigenvalues j := by
    simpa using congrArg Complex.re hB.1.trace_eq_sum_eigenvalues
  have hright : (∑ i, ∑ j,
      (hA.1.eigenvalues i * Real.log (hA.1.eigenvalues i) -
        hA.1.eigenvalues i * Real.log (hB.1.eigenvalues j) -
        hA.1.eigenvalues i + hB.1.eigenvalues j) * overlap hA.1 hB.1 i j) =
      (A * (cfc Real.log A - cfc Real.log B)).trace.re - A.trace.re + B.trace.re := by
    rw [mul_sub, Matrix.trace_sub, Complex.sub_re, hself, hcross, htraceA, htraceB]
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      overlap_weighted_row, overlap_weighted_column]
  rw [hleft, hright] at hsummed
  exact hsummed


end D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
