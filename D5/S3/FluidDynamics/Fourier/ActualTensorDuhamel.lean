/- GID: D5/S3/FluidDynamics/Fourier/ActualTensorDuhamel
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/ActualTensorDuhamel
   mirror-E: none(waiver:universal-analytic-estimate)
   anchors: []
   utility: none
   digest: Continuous full-frequency tensor paths feed the projected Bochner Duhamel operator. -/

import Mathlib
import D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution
import D5.S3.FluidDynamics.Fourier.BochnerRowHeatPath

open scoped ENNReal BigOperators
open Set MeasureTheory
open D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FluidDynamics.Fourier.ActualTensorDuhamel

set_option maxHeartbeats 4000000 in
-- The full-lattice bilinear construction and its Bochner coefficient identity use this budget.
/-- The actual weighted full-lattice tensor product of two closed-interval paths
is a continuous Hilbert path. Its clamped extension supplies a projected
Bochner Duhamel path with the original coefficient orientation. -/
theorem continuous_weighted_tensor_duhamel (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) :
    let K := ℤ × ℤ
    let V := EuclideanSpace ℂ (Fin 2)
    let TV := EuclideanSpace ℂ (Fin 2 × Fin 2)
    let H := lp (fun _ : K => V) 2
    let G := lp (fun _ : K => TV) 2
    let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
    let κ : K → V := fun k => WithLp.toLp 2 (fun i => (![k.1, k.2] i : ℂ))
    let P := fun k => (ℂ ∙ κ k)ᗮ.starProjection
    ∀ (x y : ℝ → H) (hx : ContinuousOn x (Icc 0 τ))
      (hy : ContinuousOn y (Icc 0 τ)) (Mx My : ℝ)
      (hMx : 0 ≤ Mx) (hMy : 0 ≤ My)
      (hxb : ∀ t ∈ Icc 0 τ, ‖x t‖ ≤ Mx)
      (hyb : ∀ t ∈ Icc 0 τ, ‖y t‖ ≤ My),
    ∃ q : ℝ → G, ContinuousOn q (Icc 0 τ) ∧
      (∀ t ∈ Icc 0 τ, ‖q t‖ ≤ 16 * Mx * My) ∧
      (∀ t ∈ Icc 0 τ, ∀ k : K,
        q t k = weight k • convolution
          (fun l => (weight l)⁻¹ • x t l)
          (fun l => (weight l)⁻¹ • y t l) k) ∧
      (∀ t ∈ Icc 0 τ, ∀ k : K,
        Summable (fun p : K => ‖outer
          ((weight p)⁻¹ • x t p)
          ((weight (k - p))⁻¹ • y t (k - p))‖) ∧
        Summable (fun p : K => outer
          ((weight p)⁻¹ • x t p)
          ((weight (k - p))⁻¹ • y t (k - p))) ∧
        ∀ i j : Fin 2,
          Summable (fun p : K => ‖
            (((weight p)⁻¹ • x t p) i) *
              (((weight (k - p))⁻¹ • y t (k - p)) j)‖)) ∧
      (∀ t ∈ Icc 0 τ, ∀ z w : H, ∀ r : G,
        (∀ k : K, r k = weight k • convolution
          (fun l => (weight l)⁻¹ • z l)
          (fun l => (weight l)⁻¹ • w l) k) →
        ‖q t - r‖ ≤ 16 * ‖x t - z‖ * ‖y t‖ +
          16 * ‖z‖ * ‖y t - w‖) ∧
      (∀ z w : H, ∃ r : G,
        (∀ k : K, r k = weight k • convolution
          (fun l => (weight l)⁻¹ • z l)
          (fun l => (weight l)⁻¹ • w l) k) ∧
        ∀ t ∈ Icc 0 τ,
          ‖q t - r‖ ≤ 16 * ‖x t - z‖ * ‖y t‖ +
            16 * ‖z‖ * ‖y t - w‖) ∧
      ∃ D : ℝ → H, Continuous D ∧ D 0 = 0 ∧
        (∀ t ∈ Icc 0 τ, ‖D t‖ ≤ 32 * Mx * My * Real.sqrt (t / ν)) ∧
        (∀ t ∈ Icc 0 τ, ∀ k : K, P k (D t k) = D t k) ∧
        (∀ t ∈ Icc 0 τ, D t (0 : K) = 0) ∧
        ∀ t ∈ Icc 0 τ, ∀ k : K,
          D t k = ∫ s in (0 : ℝ)..t,
            Real.exp (-ν * (t-s) * ρ k) •
              (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
                ∑ j : Fin 2, κ k j *
                  (weight k • convolution
                    (fun l => (weight l)⁻¹ • x s l)
                    (fun l => (weight l)⁻¹ • y s l) k) (i,j)))) := by
  classical
  intro K V TV H G ρ κ P x y hx hy Mx My hMx hMy hxb hyb
  have hw (k : K) : 0 < weight k := by unfold weight; positivity
  let d : H → K → V := fun z k => (weight k)⁻¹ • z k
  have he (z : H) (k : K) : weight k ^ 2 * ‖d z k‖ ^ 2 = ‖z k‖ ^ 2 := by
    dsimp [d]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hw k))]
    field_simp [(hw k).ne']
  have hs (z : H) : Summable (fun k : K => weight k ^ 2 * ‖d z k‖ ^ 2) := by
    simp_rw [he]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) z).summable
  have hn (z : H) :
      Real.sqrt (∑' k : K, weight k ^ 2 * ‖d z k‖ ^ 2) = ‖z‖ := by
    simp_rw [he]
    have hh : ‖z‖ ^ 2 = ∑' k : K, ‖z k‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) z
    rw [← hh, Real.sqrt_sq (norm_nonneg _)]
  have hp (z w : H) := weighted_tensor_convolution (d z) (d w) (hs z) (hs w)
  let Q (z w : H) : G :=
    ⟨fun k => weight k • convolution (d z) (d w) k,
      memℓp_gen (by
        simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
          ENNReal.toReal_ofNat, Real.rpow_two] using (hp z w).2.1)⟩
  have hQn (z w : H) : ‖Q z w‖ ≤ 16 * ‖z‖ * ‖w‖ := by
    have hh : ‖Q z w‖ ^ 2 =
        ∑' k : K, weight k ^ 2 * ‖convolution (d z) (d w) k‖ ^ 2 := by
      simpa only [Q, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (Q z w)
    have heq : ‖Q z w‖ = Real.sqrt
        (∑' k : K, weight k ^ 2 * ‖convolution (d z) (d w) k‖ ^ 2) := by
      rw [← hh, Real.sqrt_sq (norm_nonneg _)]
    rw [heq]
    have hb := (hp z w).2.2
    change Real.sqrt (∑' k : K, weight k ^ 2 * ‖convolution (d z) (d w) k‖ ^ 2) ≤
      16 * Real.sqrt (∑' k : K, weight k ^ 2 * ‖d z k‖ ^ 2) *
        Real.sqrt (∑' k : K, weight k ^ 2 * ‖d w k‖ ^ 2) at hb
    rw [hn z, hn w] at hb
    exact hb
  have hdadd (z w : H) (k : K) : d (z+w) k = d z k + d w k := by
    simp [d, smul_add]
  have hdsmul (c : ℝ) (z : H) (k : K) : d (c • z) k = c • d z k := by
    change (weight k)⁻¹ • (c • z k) = c • ((weight k)⁻¹ • z k)
    exact smul_comm _ _ _
  have hol (a b c : V) : outer (a+b) c = outer a c + outer b c := by
    ext ij
    change (a ij.1 + b ij.1) * c ij.2 = a ij.1 * c ij.2 + b ij.1 * c ij.2
    ring
  have hor (a b c : V) : outer a (b+c) = outer a b + outer a c := by
    ext ij
    change a ij.1 * (b ij.2 + c ij.2) = a ij.1 * b ij.2 + a ij.1 * c ij.2
    ring
  have hosl (r : ℝ) (a b : V) : outer (r • a) b = r • outer a b := by
    ext ij
    change ((r:ℂ) * a ij.1) * b ij.2 = (r:ℂ) * (a ij.1 * b ij.2)
    ring
  have hosr (r : ℝ) (a b : V) : outer a (r • b) = r • outer a b := by
    ext ij
    change a ij.1 * ((r:ℂ) * b ij.2) = (r:ℂ) * (a ij.1 * b ij.2)
    ring
  have hQal (z w v : H) : Q (z+w) v = Q z v + Q w v := by
    apply lp.ext
    funext k
    change weight k • convolution (d (z+w)) (d v) k =
      weight k • convolution (d z) (d v) k + weight k • convolution (d w) (d v) k
    rw [← smul_add]
    congr 1
    simp only [WeightedTensorConvolution.convolution, hdadd, hol]
    exact ((hp z v).1 k).of_norm.tsum_add ((hp w v).1 k).of_norm
  have hQar (z w v : H) : Q z (w+v) = Q z w + Q z v := by
    apply lp.ext
    funext k
    change weight k • convolution (d z) (d (w+v)) k =
      weight k • convolution (d z) (d w) k + weight k • convolution (d z) (d v) k
    rw [← smul_add]
    congr 1
    simp only [WeightedTensorConvolution.convolution, hdadd, hor]
    exact ((hp z w).1 k).of_norm.tsum_add ((hp z v).1 k).of_norm
  have hQsl (r : ℝ) (z w : H) : Q (r • z) w = r • Q z w := by
    apply lp.ext
    funext k
    change weight k • convolution (d (r • z)) (d w) k =
      r • (weight k • convolution (d z) (d w) k)
    simp only [WeightedTensorConvolution.convolution, hdsmul, hosl,
      tsum_const_smul'', smul_comm (weight k) r]
  have hQsr (r : ℝ) (z w : H) : Q z (r • w) = r • Q z w := by
    apply lp.ext
    funext k
    change weight k • convolution (d z) (d (r • w)) k =
      r • (weight k • convolution (d z) (d w) k)
    simp only [WeightedTensorConvolution.convolution, hdsmul, hosr,
      tsum_const_smul'', smul_comm (weight k) r]
  let QL : H →ₗ[ℝ] H →ₗ[ℝ] G := LinearMap.mk₂ ℝ Q hQal hQsl hQar
    (fun r z w => hQsr r z w)
  let QB : H →L[ℝ] H →L[ℝ] G := QL.mkContinuous₂ 16 hQn
  let q : ℝ → G := fun t => QB (x t) (y t)
  have hqc : ContinuousOn q (Icc 0 τ) :=
    (QB.continuous.comp_continuousOn hx).clm_apply hy
  have hqbound (t : ℝ) (ht : t ∈ Icc 0 τ) : ‖q t‖ ≤ 16 * Mx * My := by
    calc
      ‖q t‖ ≤ 16 * ‖x t‖ * ‖y t‖ := hQn _ _
      _ ≤ 16 * Mx * My := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hxb t ht) (by norm_num))
          (hyb t ht) (norm_nonneg _) (mul_nonneg (by norm_num) hMx)
  have hqcoeff (t : ℝ) (k : K) :
      q t k = weight k • convolution (d (x t)) (d (y t)) k := rfl
  have hQdiff (a b c d' : H) :
      Q a b - Q c d' = Q (a-c) b + Q c (b-d') := by
    have hl : Q (a-c) b = Q a b - Q c b := by
      change QL (a-c) b = QL a b - QL c b
      simp
    have hr : Q c (b-d') = Q c b - Q c d' := by
      change QL c (b-d') = QL c b - QL c d'
      simp
    rw [hl, hr]
    abel
  have hqdiff (t : ℝ) (z w : H) (r : G)
      (hr : ∀ k : K, r k = weight k • convolution (d z) (d w) k) :
      ‖q t - r‖ ≤ 16 * ‖x t - z‖ * ‖y t‖ + 16 * ‖z‖ * ‖y t - w‖ := by
    have hr' : r = Q z w := by
      apply lp.ext
      funext k
      exact hr k
    rw [hr']
    change ‖Q (x t) (y t) - Q z w‖ ≤ _
    rw [hQdiff]
    exact (norm_add_le _ _).trans (add_le_add (hQn _ _) (hQn _ _))
  let qc : C(Icc (0:ℝ) τ, G) :=
    ⟨fun t => q t, continuousOn_iff_continuous_domRestrict.mp hqc⟩
  let qe : ℝ → G := fun t => qc (projIcc 0 τ hτ.le t)
  have hqe : Continuous qe := qc.continuous.comp continuous_projIcc
  have hqeBound (t : ℝ) : ‖qe t‖ ≤ 16 * Mx * My := by
    exact hqbound (projIcc 0 τ hτ.le t).1 (projIcc 0 τ hτ.le t).2
  have hqeEq (t : ℝ) (ht : t ∈ Icc 0 τ) : qe t = q t := by
    dsimp [qe]
    rw [projIcc_of_mem _ ht]
    rfl
  obtain ⟨D, hDc, hD0, hDb, hDk⟩ :=
    D5.S3.FluidDynamics.Fourier.BochnerRowHeatPath.bochner_row_heat_path
      ν τ hν hτ qe hqe (16 * Mx * My)
      (mul_nonneg (mul_nonneg (by norm_num) hMx) hMy) hqeBound
  refine ⟨q, hqc, hqbound, ?_, ?_, ?_, ?_, D, hDc, hD0, ?_, ?_, ?_, ?_⟩
  · intro t ht k
    exact hqcoeff t k
  · intro t ht k
    have hsum := (hp (x t) (y t)).1 k
    refine ⟨?_, ?_, ?_⟩
    · exact hsum
    · exact hsum.of_norm
    · intro i j
      apply hsum.of_nonneg_of_le
      · intro p
        exact norm_nonneg _
      · intro p
        change ‖(outer (d (x t) p) (d (y t) (k - p))) (i,j)‖ ≤
          ‖outer (d (x t) p) (d (y t) (k - p))‖
        exact PiLp.norm_apply_le _ _
  · intro t ht z w r hr
    exact hqdiff t z w r hr
  · intro z w
    refine ⟨Q z w, ?_, ?_⟩
    · intro k
      rfl
    · intro t ht
      exact hqdiff t z w (Q z w) (fun k => rfl)
  · intro t ht
    simpa only [show 2 * (16 * Mx * My) = 32 * Mx * My by ring] using hDb t ht
  · intro t ht k
    rw [hDk t ht k]
    let f : ℝ → V := fun s => Real.exp (-ν * (t-s) * ρ k) •
      (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
        ∑ j : Fin 2, κ k j * qe s k (i,j))))
    have hqek : Continuous (fun s : ℝ => qe s k) :=
      (lp.evalCLM ℝ (fun _ : K => TV) 2 k).continuous.comp hqe
    have hcoord (i j : Fin 2) : Continuous (fun s : ℝ => qe s k (i,j)) :=
      (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 × Fin 2 => ℂ) (i,j)).continuous.comp hqek
    have hrow : Continuous (fun s : ℝ =>
        (WithLp.toLp 2 (fun i : Fin 2 =>
          ∑ j : Fin 2, κ k j * qe s k (i,j)) : V)) := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
      apply continuous_pi
      intro i
      apply continuous_finsetSum
      intro j hj
      exact continuous_const.mul (hcoord i j)
    have hf : Continuous f := by
      dsimp [f]
      exact (Real.continuous_exp.comp (by fun_prop)).smul
        ((continuous_const : Continuous (fun _ : ℝ => (Complex.I : ℂ))).smul
          ((P k).continuous.comp hrow))
    have hp (z : V) : P k (P k z) = P k z :=
      Submodule.starProjection_eq_self_iff.mpr
        ((ℂ ∙ κ k)ᗮ.starProjection_apply_mem z)
    change P k (∫ s in (0:ℝ)..t, f s) = ∫ s in (0:ℝ)..t, f s
    rw [← (P k).intervalIntegral_comp_comm (hf.intervalIntegrable 0 t)]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [f]
    rw [(P k).map_smul_of_tower, (P k).map_smul_of_tower, hp]
  · intro t ht
    rw [hDk t ht (0 : K)]
    have hz (s : ℝ) :
        (WithLp.toLp 2 (fun i : Fin 2 =>
          ∑ j : Fin 2, κ (0 : K) j * qe s (0 : K) (i,j)) : V) = 0 := by
      ext i
      simp [κ]
    change (∫ s in (0:ℝ)..t,
      Real.exp (-ν * (t-s) * ρ (0:K)) •
        (Complex.I • P (0:K) (WithLp.toLp 2 (fun i : Fin 2 =>
          ∑ j : Fin 2, κ (0:K) j * qe s (0:K) (i,j))))) = 0
    simp only [hz, map_zero, smul_zero, intervalIntegral.integral_zero]
  · intro t ht k
    rw [hDk t ht k]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0:ℝ) τ := by
      have hs'' : s ∈ uIcc (0:ℝ) t := hs
      rw [uIcc_of_le ht.1] at hs''
      exact ⟨hs''.1, hs''.2.trans ht.2⟩
    simp only [hqeEq s hs', hqcoeff s k, d, ρ, κ, P]
    rfl

#print axioms continuous_weighted_tensor_duhamel

end D5.S3.FluidDynamics.Fourier.ActualTensorDuhamel
