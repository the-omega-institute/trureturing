/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/RankNet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite nets for complex coefficient matrices of bounded rank. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.BallNet
import D5.S3.Quantum.Entanglement.EntanglementBreaking.SchmidtCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open _root_.Matrix
open scoped ComplexOrder
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)

private theorem matrix_finrank_real (m n : ℕ) :
    Module.finrank ℝ (Matrix (Fin m) (Fin n) ℂ) = 2 * m * n := by
  change Module.finrank ℝ (Fin m → Fin n → ℂ) = _
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

section OperatorNorm

open scoped _root_.Matrix.Norms.L2Operator

/-- Rectangular Euclidean operator norm. -/
def rectangularOpNorm {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ‖U‖

end OperatorNorm

private theorem stiefel_mulVec_norm {d k : ℕ} {U : Matrix (Fin d) (Fin k) ℂ}
    (hU : Uᴴ * U = 1) (v : Fin k → ℂ) :
    ‖WithLp.toLp 2 (U *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_toLp_toLp]
  congr 1
  rw [dotProduct_comm (U *ᵥ v), dotProduct_comm v, star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, hU, one_mulVec]

section OperatorNorm

open scoped _root_.Matrix.Norms.L2Operator

private theorem stiefel_opNorm_le_one {d k : ℕ} {U : Matrix (Fin d) (Fin k) ℂ}
    (hU : Uᴴ * U = 1) : rectangularOpNorm U ≤ 1 := by
  rw [rectangularOpNorm, Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖WithLp.toLp 2 (U *ᵥ v.ofLp)‖ ≤ _
  rw [stiefel_mulVec_norm hU, WithLp.toLp_ofLp, one_mul]

theorem exists_stiefel_net {d k : ℕ} :
    ∃ N : Finset (Matrix (Fin d) (Fin k) ℂ),
      N.card ≤ 17 ^ (2 * d * k) ∧
      (∀ U ∈ N, Uᴴ * U = 1) ∧
      ∀ U : Matrix (Fin d) (Fin k) ℂ, Uᴴ * U = 1 →
        ∃ U₀ ∈ N, rectangularOpNorm (U - U₀) ≤ 1 / 8 := by
  let : NormedSpace ℝ (Matrix (Fin d) (Fin k) ℂ) := NormedSpace.restrictScalars ℝ ℂ _
  obtain ⟨N, hN, hcover, hcard⟩ :=
    exists_finset_net_unitBall (S := {U : Matrix (Fin d) (Fin k) ℂ | Uᴴ * U = 1})
      (by
        intro U hU
        rw [Metric.mem_closedBall, dist_zero_right]
        exact stiefel_opNorm_le_one hU)
      (ε := 1 / 8) (by norm_num)
  rw [matrix_finrank_real] at hcard
  norm_num at hcard
  refine ⟨N, by exact_mod_cast hcard, fun U hU => hN hU, ?_⟩
  intro U hU
  obtain ⟨U₀, hU₀, hdist⟩ := hcover U hU
  exact ⟨U₀, hU₀, by rwa [dist_eq_norm] at hdist⟩

private theorem rectangularOpNorm_mulVec {m n : ℕ}
    (U : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    ‖WithLp.toLp 2 (U *ᵥ v)‖ ≤ rectangularOpNorm U * ‖WithLp.toLp 2 v‖ :=
  Matrix.l2_opNorm_mulVec U (WithLp.toLp 2 v)

private theorem rectangularOpNorm_nonneg {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ rectangularOpNorm U := norm_nonneg U

end OperatorNorm

open scoped _root_.Matrix.Norms.Frobenius

theorem exists_frobenius_sphere_net {m n : ℕ} :
    ∃ N : Finset (Matrix (Fin m) (Fin n) ℂ),
      N.card ≤ 17 ^ (2 * m * n) ∧
      (∀ R ∈ N, ‖R‖ = 1) ∧
      ∀ R : Matrix (Fin m) (Fin n) ℂ, ‖R‖ = 1 →
        ∃ R₀ ∈ N, ‖R - R₀‖ ≤ 1 / 8 := by
  obtain ⟨N, hN, hcover, hcard⟩ :=
    exists_finset_net_unitBall (S := {R : Matrix (Fin m) (Fin n) ℂ | ‖R‖ = 1})
      (fun R hR => mem_closedBall_zero_iff.mpr (le_of_eq hR))
      (ε := 1 / 8) (by norm_num)
  rw [matrix_finrank_real] at hcard
  norm_num at hcard
  refine ⟨N, by exact_mod_cast hcard, fun R hR => hN hR, ?_⟩
  intro R hR
  obtain ⟨R₀, hR₀, hdist⟩ := hcover R hR
  exact ⟨R₀, hR₀, by rwa [dist_eq_norm] at hdist⟩

private theorem frobenius_sq_eq_sum_cols {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    ‖A‖ ^ 2 = ∑ j, ‖WithLp.toLp 2 (fun i => A i j)‖ ^ 2 := by
  simp only [Matrix.frobenius_norm_def, Real.rpow_two, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (by positivity : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2),
    EuclideanSpace.norm_sq_eq]
  exact Finset.sum_comm

private theorem frobenius_mul_le {d k n : ℕ} (U : Matrix (Fin d) (Fin k) ℂ)
    (R : Matrix (Fin k) (Fin n) ℂ) :
    ‖U * R‖ ≤ rectangularOpNorm U * ‖R‖ := by
  have hn := rectangularOpNorm_nonneg U
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hn (norm_nonneg _))).mp
  rw [mul_pow, frobenius_sq_eq_sum_cols, frobenius_sq_eq_sum_cols R, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (rectangularOpNorm_mulVec U (fun i => R i j)) 2

private theorem frobenius_stiefel_mul {d k n : ℕ} {U : Matrix (Fin d) (Fin k) ℂ}
    (hU : Uᴴ * U = 1) (R : Matrix (Fin k) (Fin n) ℂ) : ‖U * R‖ = ‖R‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [frobenius_sq_eq_sum_cols]
  exact Finset.sum_congr rfl fun j _ => congrArg (fun t : ℝ => t ^ 2)
    (stiefel_mulVec_norm hU (fun i => R i j))

/-- Use the nonzero eigenspaces of A Aᴴ and fill with zero eigenspaces up to k columns. -/
theorem exists_left_stiefel_factorization {d k : ℕ} (hkd : k ≤ d)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.rank ≤ k) :
    ∃ U : Matrix (Fin d) (Fin k) ℂ, ∃ R : Matrix (Fin k) (Fin d) ℂ,
      Uᴴ * U = 1 ∧ U * R = A ∧ ‖R‖ = ‖A‖ := by
  classical
  let K := A * Aᴴ
  have hK : K.IsHermitian := isHermitian_mul_conjTranspose_self A
  let s := Finset.univ.filter fun i => hK.eigenvalues i ≠ 0
  have hs : s.card ≤ k := by
    have hcard : K.rank = s.card := by
      rw [hK.rank_eq_card_non_zero_eigs]
      simp [s, Fintype.card_subtype]
    rw [← hcard]
    exact (rank_mul_le_left A Aᴴ).trans hA
  obtain ⟨t, hst, ht⟩ := Finset.exists_superset_card_eq hs (by simpa using hkd)
  let e : Fin k ≃ ↥t := Fintype.equivOfCardEq (by simp [ht])
  let f : Fin k → Fin d := fun j => (e j).val
  let V : Matrix (Fin d) (Fin d) ℂ := hK.eigenvectorUnitary
  let U := V.submatrix id f
  let B := Vᴴ * A
  let R := B.submatrix f id
  have hV₁ : Vᴴ * V = 1 := hK.eigenvectorUnitary.2.1
  have hV₂ : V * Vᴴ = 1 := hK.eigenvectorUnitary.2.2
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hU : Uᴴ * U = 1 := by
    dsimp [U]
    rw [conjTranspose_submatrix,
      ← Matrix.submatrix_mul Vᴴ V f id f Function.bijective_id, hV₁, Matrix.submatrix_one f hf]
  have hdiag : B * Bᴴ = diagonal (fun i => (hK.eigenvalues i : ℂ)) := by
    change (Vᴴ * A) * (Vᴴ * A)ᴴ = _
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc A, ← Matrix.mul_assoc Vᴴ]
    change Vᴴ * K * V = _
    have hspec : K = V * diagonal (fun i => (hK.eigenvalues i : ℂ)) * Vᴴ :=
      hK.spectral_theorem
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_assoc, hV₁, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hV₁, Matrix.one_mul]
  have hz (i : Fin d) (hi : i ∉ t) : (fun j => B i j) = 0 := by
    have his : i ∉ s := fun h => hi (hst h)
    have he : hK.eigenvalues i = 0 := by simpa [s] using his
    apply dotProduct_self_star_eq_zero.mp
    have hentry := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i i) hdiag
    simpa [Matrix.mul_apply, dotProduct, diagonal_apply_eq, he, Pi.star_apply] using hentry
  have hVB : V * B = A := by dsimp [B]; rw [← Matrix.mul_assoc, hV₂, Matrix.one_mul]
  have hUR : U * R = A := by
    rw [← hVB]
    ext i j
    let g : Fin d → ℂ := fun l => V i l * B l j
    change (∑ l, g (f l)) = ∑ l, g l
    calc
      (∑ l, g (f l)) = ∑ l : ↥t, g l.val := e.sum_comp (fun l => g l.val)
      _ = ∑ l ∈ t, g l := by simpa using Finset.sum_attach t g
      _ = ∑ l, g l := by
        apply Finset.sum_subset (Finset.subset_univ t)
        intro l _ hl
        have hzero := congrFun (hz l hl) j
        simp [g, hzero]
  exact ⟨U, R, hU, hUR, (frobenius_stiefel_mul hU R).symm.trans (congrArg norm hUR)⟩

/-- The two small errors in a product approximation each have rank at most k. -/
theorem exists_rank_sphere_net (d k : ℕ) (hkd : k ≤ d) :
    ∃ N : Finset (Matrix (Fin d) (Fin d) ℂ),
      N.card ≤ 17 ^ (4 * d * k) ∧
      (∀ A ∈ N, ‖A‖ = 1 ∧ A.rank ≤ k) ∧
      ∀ A : Matrix (Fin d) (Fin d) ℂ, ‖A‖ = 1 → A.rank ≤ k →
        ∃ A₀ ∈ N, ∃ E₁ E₂ : Matrix (Fin d) (Fin d) ℂ,
          A = A₀ + E₁ + E₂ ∧ E₁.rank ≤ k ∧ E₂.rank ≤ k ∧
          ‖E₁‖ ≤ 1 / 8 ∧ ‖E₂‖ ≤ 1 / 8 := by
  classical
  obtain ⟨P, hPcard, hP, hPcover⟩ := exists_stiefel_net (d := d) (k := k)
  obtain ⟨Q, hQcard, hQ, hQcover⟩ := exists_frobenius_sphere_net (m := k) (n := d)
  let N := (P ×ˢ Q).image (fun z => z.1 * z.2)
  have hrank (U : Matrix (Fin d) (Fin k) ℂ) (R : Matrix (Fin k) (Fin d) ℂ) :
      (U * R).rank ≤ k := (rank_mul_le_left _ _).trans U.rank_le_width
  refine ⟨N, ?_, ?_, ?_⟩
  · calc
      N.card ≤ P.card * Q.card := Finset.card_image_le.trans_eq (Finset.card_product _ _)
      _ ≤ 17 ^ (2 * d * k) * 17 ^ (2 * k * d) := Nat.mul_le_mul hPcard hQcard
      _ = 17 ^ (4 * d * k) := by rw [← pow_add]; congr 1; ring
  · intro A hA
    obtain ⟨⟨U, R⟩, hUR, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hU, hR⟩ := Finset.mem_product.mp hUR
    exact ⟨(frobenius_stiefel_mul (hP U hU) R).trans (hQ R hR), hrank U R⟩
  · intro A hAn hAr
    obtain ⟨U, R, hU, hUR, hRn⟩ := exists_left_stiefel_factorization hkd A hAr
    have hR : ‖R‖ = 1 := hRn.trans hAn
    obtain ⟨U₀, hU₀, hdu⟩ := hPcover U hU
    obtain ⟨R₀, hR₀, hdr⟩ := hQcover R hR
    refine ⟨U₀ * R₀, Finset.mem_image.mpr
      ⟨(U₀, R₀), Finset.mem_product.mpr ⟨hU₀, hR₀⟩, rfl⟩,
      (U - U₀) * R, U₀ * (R - R₀), ?_, hrank _ _, hrank _ _, ?_, ?_⟩
    · rw [← hUR, Matrix.sub_mul, Matrix.mul_sub]
      abel
    · simpa only [hR, mul_one] using (frobenius_mul_le (U - U₀) R).trans
        (mul_le_mul_of_nonneg_right hdu (norm_nonneg R))
    · rwa [frobenius_stiefel_mul (hP U₀ hU₀)]

end D5.S3.Quantum.Entanglement.EntanglementBreaking
