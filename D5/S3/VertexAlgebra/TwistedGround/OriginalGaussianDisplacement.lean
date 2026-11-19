/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDisplacement
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianDisplacement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered finite displacement and its limit on the actual Gaussian carrier. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Frequency multiplication occurs only in finite matrices. -/

set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Topology ENNReal Matrix.Norms.L2Operator
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement

open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianWeightedResolvent
open OriginalGaussianUniformCutoff
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

private def frequency (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => (i.val + 1 : ℂ))

private def finiteWeight (N : ℕ) (r : ℝ) : Fin N → ℂ :=
  fun i => (i.val + 1 : ℂ) * sourceValue r i.val

def finiteSigned (N : ℕ) (σ z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Ring.inverse (1 - σ • finiteSection N z)

private lemma finite_unit (N : ℕ) {σ z : ℂ} (hσ : ‖σ‖ = 1) (hz : ‖z‖ < 1) :
    IsUnit (1 - σ • finiteSection N z) := by
  apply isUnit_one_sub_of_norm_lt_one
  rw [norm_smul, hσ, one_mul]
  exact (finiteSection_opNorm_le N z hz).trans_lt
    (pow_lt_one₀ (norm_nonneg z) hz (by norm_num))

/-- Ordinary transpose symmetry of the original finite section. -/
lemma section_symm (N : ℕ) (z : ℂ) :
    (finiteSection N z).transpose = finiteSection N z := by
  ext i j
  simp only [Matrix.transpose_apply, finiteSection, matrixEntry, pairScalar]
  congr 1
  · congr 1 <;> ring
  · congr 1 <;> omega

private lemma signed_symm (N : ℕ) (σ z : ℂ) :
    (finiteSigned N σ z).transpose = finiteSigned N σ z := by
  simp only [finiteSigned, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, section_symm]

private lemma finite_anticommutator (N : ℕ) (r : ℝ) :
    frequency N * finiteSection N (Real.sqrt r : ℂ) +
      finiteSection N (Real.sqrt r : ℂ) * frequency N =
        Matrix.vecMulVec (finiteWeight N r) (finiteWeight N r) := by
  ext i j
  simp only [frequency, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    finiteSection, Matrix.vecMulVec_apply, finiteWeight]
  linear_combination original_coordinate_anticommutator r i.val j.val

private lemma ordered_first (N : ℕ) {r : ℝ} (hr1 : r < 1) :
    frequency N * finiteSigned N 1 (Real.sqrt r : ℂ) -
      finiteSigned N (-1) (Real.sqrt r : ℂ) * frequency N =
        Matrix.vecMulVec
          ((finiteSigned N (-1) (Real.sqrt r : ℂ)).mulVec (finiteWeight N r))
          ((finiteSigned N 1 (Real.sqrt r : ℂ)).mulVec (finiteWeight N r)) := by
  let K := finiteSection N (Real.sqrt r : ℂ)
  let R := finiteSigned N 1 (Real.sqrt r : ℂ)
  let V := finiteSigned N (-1) (Real.sqrt r : ℂ)
  let H := frequency N
  have hR : (1 - K) * R = 1 := by
    simpa [R, K, finiteSigned] using
      Ring.mul_inverse_cancel _ (finite_unit N (by simp : ‖(1 : ℂ)‖ = 1)
        (radial_norm_lt_one hr1))
  have hV : V * (1 + K) = 1 := by
    simpa [V, K, finiteSigned] using
      Ring.inverse_mul_cancel _ (finite_unit N (by simp : ‖(-1 : ℂ)‖ = 1)
        (radial_norm_lt_one hr1))
  calc
    H * R - V * H = V * ((1 + K) * H - H * (1 - K)) * R := by
      calc
        _ = (V * (1 + K)) * H * R - V * H * ((1 - K) * R) := by rw [hV, hR]; simp
        _ = _ := by noncomm_ring
    _ = V * (H * K + K * H) * R := by congr 2 <;> noncomm_ring
    _ = V * Matrix.vecMulVec (finiteWeight N r) (finiteWeight N r) * R := by
      rw [show H * K + K * H = _ from finite_anticommutator N r]
    _ = _ := by
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose,
        show R.transpose = R from signed_symm N 1 (Real.sqrt r : ℂ)]

private lemma ordered_second (N : ℕ) {r : ℝ} (hr1 : r < 1) :
    frequency N * finiteSigned N (-1) (Real.sqrt r : ℂ) -
      finiteSigned N 1 (Real.sqrt r : ℂ) * frequency N =
        -Matrix.vecMulVec
          ((finiteSigned N 1 (Real.sqrt r : ℂ)).mulVec (finiteWeight N r))
          ((finiteSigned N (-1) (Real.sqrt r : ℂ)).mulVec (finiteWeight N r)) := by
  let K := finiteSection N (Real.sqrt r : ℂ)
  let R := finiteSigned N 1 (Real.sqrt r : ℂ)
  let V := finiteSigned N (-1) (Real.sqrt r : ℂ)
  let H := frequency N
  have hR : R * (1 - K) = 1 := by
    simpa [R, K, finiteSigned] using
      Ring.inverse_mul_cancel _ (finite_unit N (by simp : ‖(1 : ℂ)‖ = 1)
        (radial_norm_lt_one hr1))
  have hV : (1 + K) * V = 1 := by
    simpa [V, K, finiteSigned] using
      Ring.mul_inverse_cancel _ (finite_unit N (by simp : ‖(-1 : ℂ)‖ = 1)
        (radial_norm_lt_one hr1))
  calc
    H * V - R * H = R * ((1 - K) * H - H * (1 + K)) * V := by
      calc
        _ = (R * (1 - K)) * H * V - R * H * ((1 + K) * V) := by rw [hR, hV]; simp
        _ = _ := by noncomm_ring
    _ = -(R * (H * K + K * H) * V) := by noncomm_ring
    _ = -(R * Matrix.vecMulVec (finiteWeight N r) (finiteWeight N r) * V) := by
      rw [show H * K + K * H = _ from finite_anticommutator N r]
    _ = _ := by
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose,
        show V.transpose = V from signed_symm N (-1) (Real.sqrt r : ℂ)]

private lemma section_coordinate (N : ℕ) (z : ℂ) (x : H) (n : ℕ) :
    sectionOp N z x n = if hn : n < N then
      ∑ j : Fin N, matrixEntry z (n + 1) (j.val + 1) * x j.val else 0 := by
  classical
  simp only [sectionOp, ContinuousLinearMap.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  simp_rw [term_apply]
  by_cases hn : n < N
  · rw [dif_pos hn, Finset.sum_eq_single n]
    · simp only [ite_true]
      exact Finset.sum_range _
    · intro i hi hin
      simp [hin]
    · simp [Finset.mem_range, hn]
  · rw [dif_neg hn]
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i ≠ n := by intro h; subst i; exact hn (Finset.mem_range.mp hi)
    simp [hin]

lemma zeroExtend_signed (N : ℕ) {σ z : ℂ} (hσ : ‖σ‖ = 1)
    (hz : ‖z‖ < 1) (x : EuclideanSpace ℂ (Fin N)) :
    sectionSignedResolvent N σ z (zeroExtend N x) =
      zeroExtend N (WithLp.toLp 2 ((finiteSigned N σ z).mulVec x)) := by
  let W := finiteSigned N σ z
  let y : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (W.mulVec x)
  have hfinite : (1 - σ • finiteSection N z).mulVec y = x := by
    change (1 - σ • finiteSection N z).mulVec (W.mulVec x) = x
    rw [Matrix.mulVec_mulVec, show (1 - σ • finiteSection N z) * W = 1 from
      Ring.mul_inverse_cancel _ (finite_unit N hσ hz), Matrix.one_mulVec]
  have he : (1 - σ • sectionOp N z) (zeroExtend N y) = zeroExtend N x := by
    ext n
    change zeroExtend N y n - σ * sectionOp N z (zeroExtend N y) n = _
    rw [section_coordinate, zeroExtend_apply, zeroExtend_apply]
    split_ifs with hn
    · have hf := congrFun hfinite ⟨n, hn⟩
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hf
      simpa only [Matrix.mulVec, dotProduct, finiteSection, zeroExtend_apply,
        dif_pos (Fin.isLt _)] using hf
    · simp
  have hb : ‖σ • sectionOp N z‖ < 1 := by
    rw [norm_smul, hσ, one_mul]
    exact (sectionOp_norm_le N hz).trans_lt
      (pow_lt_one₀ (norm_nonneg z) hz (by norm_num))
  have hi : sectionSignedResolvent N σ z * (1 - σ • sectionOp N z) = 1 :=
    (summable_geometric_of_norm_lt_one hb).tsum_pow_mul_one_sub
  calc
    _ = sectionSignedResolvent N σ z ((1 - σ • sectionOp N z) (zeroExtend N y)) := by
      rw [he]
    _ = zeroExtend N y := congrArg (fun T : H →L[ℂ] H => T (zeroExtend N y)) hi

/-- The actual finite section acts on the included finite coordinates. -/
lemma section_zeroExtend (N : ℕ) (z : ℂ) (x : EuclideanSpace ℂ (Fin N)) :
    sectionOp N z (zeroExtend N x) =
      zeroExtend N (WithLp.toLp 2 ((finiteSection N z).mulVec x)) := by
  ext n
  rw [section_coordinate, zeroExtend_apply]
  split_ifs with hn
  · simp only [Matrix.mulVec, dotProduct, finiteSection, zeroExtend_apply,
      dif_pos (Fin.isLt _), PiLp.toLp_apply]
  · rfl

/-- The infinite square-cutoff inverse agrees with the finite matrix inverse
on zero-extended vectors. Its action outside that subspace is retained. -/
theorem zeroExtend_square_inverse (N : ℕ) {z : ℂ} (hz : ‖z‖ < 1)
    (x : EuclideanSpace ℂ (Fin N)) :
    (∑' k : ℕ, (sectionOp N z ^ 2) ^ k) (zeroExtend N x) =
      zeroExtend N (WithLp.toLp 2 ((Ring.inverse (1 - finiteSection N z ^ 2)).mulVec x)) := by
  let K := finiteSection N z
  let y : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 ((Ring.inverse (1 - K ^ 2)).mulVec x)
  have hk : ‖K‖ < 1 := (finiteSection_opNorm_le N z hz).trans_lt
    (pow_lt_one₀ (norm_nonneg z) hz (by norm_num))
  have hK : IsUnit (1 - K ^ 2) := by
    apply isUnit_one_sub_of_norm_lt_one
    rw [pow_two]
    exact (norm_mul_le _ _).trans_lt
      (by simpa only [pow_two] using pow_lt_one₀ (norm_nonneg K) hk (by norm_num : (2 : ℕ) ≠ 0))
  have hf : (1 - K ^ 2).mulVec y = (x : Fin N → ℂ) := by
    change (1 - K ^ 2).mulVec ((Ring.inverse (1 - K ^ 2)).mulVec x) = (x : Fin N → ℂ)
    rw [Matrix.mulVec_mulVec, Ring.mul_inverse_cancel _ hK, Matrix.one_mulVec]
  have he : ((1 : H →L[ℂ] H) - sectionOp N z ^ 2) (zeroExtend N y) = zeroExtend N x := by
    change zeroExtend N y - sectionOp N z (sectionOp N z (zeroExtend N y)) = _
    rw [section_zeroExtend, section_zeroExtend]
    ext n
    simp only [lp.coeFn_sub, Pi.sub_apply, zeroExtend_apply]
    split_ifs with hn
    · have h := congrFun hf ⟨n, hn⟩
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, pow_two,
        Matrix.mulVec_mulVec] at h
      simpa only [K, Matrix.mulVec_mulVec] using h
    · simp
  have hs : ‖sectionOp N z ^ 2‖ < 1 := by
    apply (norm_pow_le _ _).trans_lt
    exact pow_lt_one₀ (norm_nonneg _) ((sectionOp_norm_le N hz).trans_lt
      (pow_lt_one₀ (norm_nonneg z) hz (by norm_num))) (by norm_num)
  have hi := (summable_geometric_of_norm_lt_one hs).tsum_pow_mul_one_sub
  calc
    _ = (∑' k : ℕ, (sectionOp N z ^ 2) ^ k)
        (((1 : H →L[ℂ] H) - sectionOp N z ^ 2) (zeroExtend N y)) := by rw [he]
    _ = zeroExtend N y := congrArg (fun A : H →L[ℂ] H => A (zeroExtend N y)) hi

private lemma signed_entry (N : ℕ) {σ z : ℂ} (hσ : ‖σ‖ = 1) (hz : ‖z‖ < 1)
    (n m : ℕ) (hn : n < N) (hm : m < N) :
    sectionSignedResolvent N σ z (basis m) n =
      finiteSigned N σ z ⟨n, hn⟩ ⟨m, hm⟩ := by
  classical
  let x : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (Pi.single ⟨m, hm⟩ 1)
  have hx : zeroExtend N x = basis m := by
    ext k
    simp only [zeroExtend_apply, basis, lp.single_apply]
    by_cases hk : k < N
    · simp only [dif_pos hk, x, PiLp.toLp_apply, Pi.single_apply]
      split_ifs <;> simp_all [Fin.ext_iff]
    · simp only [dif_neg hk]
      have hmk : m ≠ k := by intro h; subst k; exact hk hm
      simp [hmk]
  have h := congrArg (fun y : H => y n) (zeroExtend_signed N hσ hz x)
  rw [hx, zeroExtend_apply, dif_pos hn] at h
  simpa [x, Matrix.mulVec, dotProduct, Pi.single_apply] using h

private lemma cutoff_zeroExtend (N : ℕ) (r : ℝ) :
    zeroExtend N (WithLp.toLp 2 (finiteWeight N r)) = weightedCutoff N r := by
  classical
  ext n
  simp only [zeroExtend_apply, weightedCutoff, lp.coeFn_sum, Finset.sum_apply,
    traceWeightedTerm, lp.single_apply, finiteWeight, PiLp.toLp_apply]
  by_cases hn : n < N <;> simp [Finset.mem_range, hn]

private lemma signed_weight_entry (N : ℕ) {σ : ℂ} (hσ : ‖σ‖ = 1)
    {r : ℝ} (hr1 : r < 1) (n : ℕ) (hn : n < N) :
    sectionSignedResolvent N σ (Real.sqrt r : ℂ) (weightedCutoff N r) n =
      (finiteSigned N σ (Real.sqrt r : ℂ)).mulVec (finiteWeight N r) ⟨n, hn⟩ := by
  have h := congrArg (fun y : H => y n)
    (zeroExtend_signed N hσ (radial_norm_lt_one hr1) (WithLp.toLp 2 (finiteWeight N r)))
  simpa only [cutoff_zeroExtend, zeroExtend_apply, dif_pos hn, PiLp.toLp_apply] using h

private lemma signed_tendsto {z σ : ℂ} (hz : ‖z‖ < 1) (hσ : ‖σ‖ = 1) :
    Tendsto (fun N => sectionSignedResolvent N σ z) atTop
      (𝓝 (∑' k : ℕ, (σ • operator z) ^ k)) :=
  (sectionSignedResolvent_tendstoUniformlyOn (norm_nonneg z) hz σ hσ).tendsto_at
    (show z ∈ {w : ℂ | ‖w‖ ≤ ‖z‖} from (show ‖z‖ ≤ ‖z‖ from le_rfl))

/-- The two ordered displacement equations on the original infinite carrier.
Only fixed coordinates survive the finite-frequency limit. -/
theorem signed_resolvent_displacement {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (n m : ℕ) :
    ((n + 1 : ℂ) * resolvent (Real.sqrt r : ℂ) (basis m) n -
      (m + 1 : ℂ) * oppositeResolvent (Real.sqrt r : ℂ) (basis m) n =
        oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr hr1) n *
          resolvent (Real.sqrt r : ℂ) (weightedSource r hr hr1) m) ∧
    ((n + 1 : ℂ) * oppositeResolvent (Real.sqrt r : ℂ) (basis m) n -
      (m + 1 : ℂ) * resolvent (Real.sqrt r : ℂ) (basis m) n =
        -(resolvent (Real.sqrt r : ℂ) (weightedSource r hr hr1) n *
          oppositeResolvent (Real.sqrt r : ℂ) (weightedSource r hr hr1) m)) := by
  have hz := radial_norm_lt_one hr1
  have hR : Tendsto (fun N => sectionSignedResolvent N 1 (Real.sqrt r : ℂ)) atTop
      (𝓝 (resolvent (Real.sqrt r : ℂ))) := by
    simpa only [one_smul, OriginalGaussianResolvent.resolvent] using signed_tendsto hz (by simp : ‖(1 : ℂ)‖ = 1)
  have hV : Tendsto (fun N => sectionSignedResolvent N (-1) (Real.sqrt r : ℂ)) atTop
      (𝓝 (oppositeResolvent (Real.sqrt r : ℂ))) := by
    simpa only [neg_one_smul, oppositeResolvent] using
      signed_tendsto hz (by simp : ‖(-1 : ℂ)‖ = 1)
  have hv : Tendsto (fun N => weightedCutoff N r) atTop (𝓝 (weightedSource r hr hr1)) :=
    (weightedCutoff_tendstoUniformly hr hr1).tendsto_at (⟨r, hr, le_rfl⟩ : Set.Icc 0 r)
  have hRn := ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).continuous.tendsto _).comp
    ((isBoundedBilinearMap_apply.continuous.tendsto _).comp (hR.prodMk_nhds (tendsto_const_nhds (x := basis m))))
  have hVn := ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).continuous.tendsto _).comp
    ((isBoundedBilinearMap_apply.continuous.tendsto _).comp (hV.prodMk_nhds (tendsto_const_nhds (x := basis m))))
  have hpn := ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).continuous.tendsto _).comp ((isBoundedBilinearMap_apply.continuous.tendsto _).comp (hR.prodMk_nhds hv))
  have hpm := ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 m).continuous.tendsto _).comp ((isBoundedBilinearMap_apply.continuous.tendsto _).comp (hR.prodMk_nhds hv))
  have hmn := ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).continuous.tendsto _).comp ((isBoundedBilinearMap_apply.continuous.tendsto _).comp (hV.prodMk_nhds hv))
  have hmm := ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 m).continuous.tendsto _).comp ((isBoundedBilinearMap_apply.continuous.tendsto _).comp (hV.prodMk_nhds hv))
  have he : ∀ᶠ N in atTop,
      ((n + 1 : ℂ) * sectionSignedResolvent N 1 (Real.sqrt r : ℂ) (basis m) n -
        (m + 1 : ℂ) * sectionSignedResolvent N (-1) (Real.sqrt r : ℂ) (basis m) n =
          sectionSignedResolvent N (-1) (Real.sqrt r : ℂ) (weightedCutoff N r) n *
            sectionSignedResolvent N 1 (Real.sqrt r : ℂ) (weightedCutoff N r) m) ∧
      ((n + 1 : ℂ) * sectionSignedResolvent N (-1) (Real.sqrt r : ℂ) (basis m) n -
        (m + 1 : ℂ) * sectionSignedResolvent N 1 (Real.sqrt r : ℂ) (basis m) n =
          -(sectionSignedResolvent N 1 (Real.sqrt r : ℂ) (weightedCutoff N r) n *
            sectionSignedResolvent N (-1) (Real.sqrt r : ℂ) (weightedCutoff N r) m)) := by
    filter_upwards [eventually_gt_atTop (max n m)] with N hN
    have hn : n < N := lt_of_le_of_lt (le_max_left n m) hN
    have hm : m < N := lt_of_le_of_lt (le_max_right n m) hN
    simp only [signed_entry N (by simp : ‖(1 : ℂ)‖ = 1) hz n m hn hm,
      signed_entry N (by simp : ‖(-1 : ℂ)‖ = 1) hz n m hn hm,
      signed_weight_entry N (by simp : ‖(1 : ℂ)‖ = 1) hr1 n hn,
      signed_weight_entry N (by simp : ‖(1 : ℂ)‖ = 1) hr1 m hm,
      signed_weight_entry N (by simp : ‖(-1 : ℂ)‖ = 1) hr1 n hn,
      signed_weight_entry N (by simp : ‖(-1 : ℂ)‖ = 1) hr1 m hm]
    constructor
    · have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M ⟨n, hn⟩ ⟨m, hm⟩)
        (ordered_first N hr1)
      simpa only [Matrix.sub_apply, frequency, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Matrix.vecMulVec_apply, Fin.val_mk, mul_comm] using h
    · have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M ⟨n, hn⟩ ⟨m, hm⟩)
        (ordered_second N hr1)
      simpa only [Matrix.sub_apply, frequency, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Matrix.neg_apply, Matrix.vecMulVec_apply, Fin.val_mk, mul_comm] using h
  constructor
  · exact tendsto_nhds_unique ((tendsto_const_nhds.mul hRn).sub (tendsto_const_nhds.mul hVn))
      ((hmn.mul hpm).congr' (he.mono (fun _ h => h.1.symm)))
  · exact tendsto_nhds_unique ((tendsto_const_nhds.mul hVn).sub (tendsto_const_nhds.mul hRn))
      ((hpn.mul hmm).neg.congr' (he.mono (fun _ h => h.2.symm)))

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDisplacement
