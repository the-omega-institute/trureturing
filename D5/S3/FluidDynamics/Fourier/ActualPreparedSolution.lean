/- GID: D5/S3/FluidDynamics/Fourier/ActualPreparedSolution
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/ActualPreparedSolution
   mirror-E: none(waiver:universal-analytic-construction)
   anchors: []
   utility: none
   digest: Prepared real mild solutions: uniqueness, stability and smooth velocity. -/

import Mathlib
import D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution
import D5.S3.FluidDynamics.Fourier.BochnerRowHeatPath
import D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis
import D5.S3.FluidDynamics.Fourier.MildPathRegularity
import D5.S3.FluidDynamics.Fourier.JointFourierSynthesis

open scoped ENNReal NNReal BigOperators
open Set MeasureTheory Filter Topology
open D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FluidDynamics.Fourier.ActualPreparedSolution

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 4096 in
/-- The original prepared data, with no evolution cutoff or assumed carrier invariance. -/
theorem prepared_mild_solution (ν A B α β : ℝ)
    (hν : 0 < ν) (hA : 0 < A) (hB : 0 ≤ B)
    (hα : |α| ≤ A) (hβ : |β| ≤ B) :
    let K := ℤ × ℤ
    let V := EuclideanSpace ℂ (Fin 2)
    let TV := EuclideanSpace ℂ (Fin 2 × Fin 2)
    let H := lp (fun _ : K => V) 2
    let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
    let κ : K → V := fun k => WithLp.toLp 2 (fun i => (![k.1, k.2] i : ℂ))
    let P := fun k => (ℂ ∙ κ k)ᗮ.starProjection
    let R := 2 * Real.sqrt (2*A^2 + 9*B^2)
    let τ := ν / (16384 * R^2)
    let a : V := WithLp.toLp 2 ![0, (α : ℂ)]
    let b : V := WithLp.toLp 2 ![(3*β/2 : ℂ), (3*β/2 : ℂ)]
    let X0 : H := lp.single 2 (1,0) a + lp.single 2 (-1,0) a +
      lp.single 2 (-1,1) b + lp.single 2 (1,-1) b
    ∃ u : ℝ → H, ContinuousOn u (Icc 0 τ) ∧ u 0 = X0 ∧
      (∀ t ∈ Icc 0 τ, ‖u t‖ ≤ R) ∧
      (∀ t ∈ Icc 0 τ, u t 0 = 0 ∧
        (∀ k i, u t (-k) i = star (u t k i)) ∧ (∀ k, P k (u t k) = u t k)) ∧
      (∀ v : ℝ → H, ContinuousOn v (Icc 0 τ) →
        (∀ t ∈ Icc 0 τ, ∀ k,
          v t k = Real.exp (-ν*t*ρ k) • X0 k - ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j * (weight k • convolution
                (fun l => (weight l)⁻¹ • v s l)
                (fun l => (weight l)⁻¹ • v s l) k) (i,j))))) →
        ∀ t ∈ Icc 0 τ, v t = u t) ∧
      (∀ (β₂ : ℝ) (v : ℝ → H), ContinuousOn v (Icc 0 τ) →
        (∀ t ∈ Icc 0 τ, ‖v t‖ ≤ R) →
        let b₂ : V := WithLp.toLp 2 ![(3*β₂/2 : ℂ),(3*β₂/2 : ℂ)]
        let X₂ : H := lp.single (E := fun _ : K => V) 2 (1,0) a +
          lp.single (E := fun _ : K => V) 2 (-1,0) a +
          lp.single (E := fun _ : K => V) 2 (-1,1) b₂ +
          lp.single (E := fun _ : K => V) 2 (1,-1) b₂
        (∀ t ∈ Icc 0 τ, ∀ k,
          v t k = Real.exp (-ν*t*ρ k) • X₂ k - ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j * (weight k • convolution
                (fun l => (weight l)⁻¹ • v s l)
                (fun l => (weight l)⁻¹ • v s l) k) (i,j))))) →
        ∀ t ∈ Icc 0 τ, ‖u t-v t‖ ≤ 6*|β-β₂|) ∧
      (∀ x y : ℝ, ∀ i : Fin 2,
        (∑' k : K, ((((weight k)⁻¹:ℝ):ℂ) * X0 k i) *
          D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.character k x y) =
        (D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.realVelocity α β x y i.castSucc : ℂ)) ∧
      ∃ D : ℝ → H, Continuous D ∧ D 0 = 0 ∧
        (∀ t ∈ Icc 0 τ, ‖D t‖ ≤ R/4) ∧
        (∀ t ∈ Icc 0 τ, ∀ k,
          u t k = Real.exp (-ν*t*ρ k) • X0 k - D t k) ∧
        (∀ t ∈ Icc 0 τ, ∀ k,
          D t k = ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j * (weight k • convolution
                (fun l => (weight l)⁻¹ • u s l)
                (fun l => (weight l)⁻¹ • u s l) k) (i,j))))) ∧
        let w : ℕ → K → ℝ := fun m k => (1+ρ k)^((m:ℝ)/2)
        let dec : ℕ → H → K → V := fun m z k => (w m k)⁻¹ • z k
        let aa : ℝ → K → V := fun t k => (1+ρ k)⁻¹ • u t k
        let N : (K → V) → (K → V) → K → V := fun a' b' k =>
          Complex.I • P k (∑' l : K, (∑ j : Fin 2, κ k j*a' l j) • b' (k-l))
        ∃ (U : ℕ → ℝ → H) (L : ℕ → H →L[ℝ] H)
          (B : ℕ → H →L[ℝ] H →L[ℝ] H),
          (∀ m t, t ∈ Icc 0 τ → ∀ k, U m t k = w m k • aa t k) ∧
          (∀ m, ContinuousOn (U m) (Icc 0 τ)) ∧
          (∀ m z k, L m z k = w m k • ((-ν*ρ k) • dec (m+2) z k)) ∧
          (∀ m z z' k, B m z z' k = w m k • N (dec (m+2) z) (dec (m+2) z') k) ∧
          (∀ m t, t ∈ Icc 0 τ → HasDerivWithinAt (U m)
            (L m (U (m+2) t) - B m (U (m+2) t) (U (m+2) t)) (Icc 0 τ) t) ∧
          (∀ m n : ℕ, ContDiffOn ℝ n (U m) (Icc 0 τ)) ∧
          (∀ n : ℕ, ContDiffOn ℝ n
            (fun z : ℝ × (Fin 2 → ℝ) => WithLp.toLp 2 (fun i : Fin 2 =>
              (∑' k : K, Complex.exp (Complex.I *
                ((k.1:ℝ)*z.2 0+(k.2:ℝ)*z.2 1)) • aa z.1 k) i |>.re))
            (Icc 0 τ ×ˢ (Set.univ : Set (Fin 2 → ℝ)))) ∧
          (∀ t ∈ Icc 0 τ, ∀ x : Fin 2 → ℝ,
            Summable (fun k : K => ‖Complex.exp (Complex.I *
              ((k.1:ℝ)*x 0+(k.2:ℝ)*x 1)) • aa t k‖) ∧
            ‖WithLp.toLp 2 (fun i : Fin 2 =>
              (∑' k : K, Complex.exp (Complex.I *
                ((k.1:ℝ)*x 0+(k.2:ℝ)*x 1)) • aa t k) i |>.re)‖ ≤ 4*R) := by
  classical
  have hTensor (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) :
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
  have hDifference (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) :
      let K := ℤ × ℤ
      let V := EuclideanSpace ℂ (Fin 2)
      let TV := EuclideanSpace ℂ (Fin 2 × Fin 2)
      let H := lp (fun _ : K => V) 2
      let G := lp (fun _ : K => TV) 2
      let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
      let κ : K → V := fun k => WithLp.toLp 2 (fun i => (![k.1, k.2] i : ℂ))
      let P := fun k => (ℂ ∙ κ k)ᗮ.starProjection
      ∀ (x y z w : ℝ → H), ContinuousOn x (Icc 0 τ) →
        ContinuousOn y (Icc 0 τ) → ContinuousOn z (Icc 0 τ) →
        ContinuousOn w (Icc 0 τ) →
        ∀ (Mx My Mz Mw Dx Dy : ℝ),
          0 ≤ Mx → 0 ≤ My → 0 ≤ Mz → 0 ≤ Mw → 0 ≤ Dx → 0 ≤ Dy →
          (∀ t ∈ Icc 0 τ, ‖x t‖ ≤ Mx) →
          (∀ t ∈ Icc 0 τ, ‖y t‖ ≤ My) →
          (∀ t ∈ Icc 0 τ, ‖z t‖ ≤ Mz) →
          (∀ t ∈ Icc 0 τ, ‖w t‖ ≤ Mw) →
          (∀ t ∈ Icc 0 τ, ‖x t - z t‖ ≤ Dx) →
          (∀ t ∈ Icc 0 τ, ‖y t - w t‖ ≤ Dy) →
      ∃ Dxy Dzw : ℝ → H, Continuous Dxy ∧ Continuous Dzw ∧
        Dxy 0 = 0 ∧ Dzw 0 = 0 ∧
        (∀ t ∈ Icc 0 τ, ‖Dxy t‖ ≤ 32 * Mx * My * Real.sqrt (t / ν)) ∧
        (∀ t ∈ Icc 0 τ, ‖Dzw t‖ ≤ 32 * Mz * Mw * Real.sqrt (t / ν)) ∧
        (∀ t ∈ Icc 0 τ, ∀ k : K,
          Dxy t k = ∫ s in (0 : ℝ)..t,
            Real.exp (-ν * (t-s) * ρ k) •
              (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
                ∑ j : Fin 2, κ k j *
                  (weight k • convolution
                    (fun l => (weight l)⁻¹ • x s l)
                    (fun l => (weight l)⁻¹ • y s l) k) (i,j))))) ∧
        (∀ t ∈ Icc 0 τ, ∀ k : K,
          Dzw t k = ∫ s in (0 : ℝ)..t,
            Real.exp (-ν * (t-s) * ρ k) •
              (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
                ∑ j : Fin 2, κ k j *
                  (weight k • convolution
                    (fun l => (weight l)⁻¹ • z s l)
                    (fun l => (weight l)⁻¹ • w s l) k) (i,j))))) ∧
        ∀ t ∈ Icc 0 τ,
          ‖Dxy t - Dzw t‖ ≤
            32 * (Dx * My + Mz * Dy) * Real.sqrt (t / ν) := by
    classical
    intro K V TV H G ρ κ P x y z w hx hy hz hw
      Mx My Mz Mw Dx Dy hMx hMy hMz hMw hDx hDy hxb hyb hzb hwb hdiffx hdiffy
    obtain ⟨qxy, hqxyc, hqxyb, hqxyk, -, hqxycmp, -, Dxy, hDxyc, hDxy0,
        hDxyb, -, -, hDxyk⟩ :=
      hTensor
        ν τ hν hτ x y hx hy Mx My hMx hMy hxb hyb
    obtain ⟨qzw, hqzwc, hqzwb, hqzwk, -, -, -, Dzw, hDzwc, hDzw0,
        hDzwb, -, -, hDzwk⟩ :=
      hTensor
        ν τ hν hτ z w hz hw Mz Mw hMz hMw hzb hwb
    let C : ℝ := 16 * Dx * My + 16 * Mz * Dy
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hqdiff (t : ℝ) (ht : t ∈ Icc 0 τ) :
        ‖qxy t - qzw t‖ ≤ C := by
      have h := hqxycmp t ht (z t) (w t) (qzw t) (hqzwk t ht)
      calc
        ‖qxy t - qzw t‖ ≤
            16 * ‖x t - z t‖ * ‖y t‖ + 16 * ‖z t‖ * ‖y t - w t‖ := h
        _ ≤ C := by
          dsimp [C]
          have ha : 16 * ‖x t - z t‖ * ‖y t‖ ≤ 16 * Dx * My :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hdiffx t ht) (by norm_num))
              (hyb t ht) (norm_nonneg _) (mul_nonneg (by norm_num) hDx)
          have hb : 16 * ‖z t‖ * ‖y t - w t‖ ≤ 16 * Mz * Dy :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hzb t ht) (by norm_num))
              (hdiffy t ht) (norm_nonneg _) (mul_nonneg (by norm_num) hMz)
          linarith
    let qc : C(Icc (0:ℝ) τ, G) :=
      ⟨fun t => qxy t - qzw t,
        continuousOn_iff_continuous_domRestrict.mp (hqxyc.sub hqzwc)⟩
    let qe : ℝ → G := fun t => qc (projIcc 0 τ hτ.le t)
    have hqe : Continuous qe := qc.continuous.comp continuous_projIcc
    have hqeb (t : ℝ) : ‖qe t‖ ≤ C :=
      hqdiff (projIcc 0 τ hτ.le t).1 (projIcc 0 τ hτ.le t).2
    obtain ⟨Ddiff, hDdiffc, hDdiff0, hDdiffb, hDdiffk⟩ :=
      D5.S3.FluidDynamics.Fourier.BochnerRowHeatPath.bochner_row_heat_path
        ν τ hν hτ qe hqe C hC hqeb
    have hqxy_ext : Continuous (fun s : ℝ =>
        (⟨fun t : Icc (0:ℝ) τ => qxy t,
          continuousOn_iff_continuous_domRestrict.mp hqxyc⟩ : C(Icc 0 τ,G))
          (projIcc 0 τ hτ.le s)) :=
      (⟨fun t : Icc (0:ℝ) τ => qxy t,
        continuousOn_iff_continuous_domRestrict.mp hqxyc⟩ : C(Icc 0 τ,G)).continuous.comp
          continuous_projIcc
    have hqzw_ext : Continuous (fun s : ℝ =>
        (⟨fun t : Icc (0:ℝ) τ => qzw t,
          continuousOn_iff_continuous_domRestrict.mp hqzwc⟩ : C(Icc 0 τ,G))
          (projIcc 0 τ hτ.le s)) :=
      (⟨fun t : Icc (0:ℝ) τ => qzw t,
        continuousOn_iff_continuous_domRestrict.mp hqzwc⟩ : C(Icc 0 τ,G)).continuous.comp
          continuous_projIcc
    let qxe : ℝ → G := fun s =>
      (⟨fun t : Icc (0:ℝ) τ => qxy t,
        continuousOn_iff_continuous_domRestrict.mp hqxyc⟩ : C(Icc 0 τ,G))
        (projIcc 0 τ hτ.le s)
    let qze : ℝ → G := fun s =>
      (⟨fun t : Icc (0:ℝ) τ => qzw t,
        continuousOn_iff_continuous_domRestrict.mp hqzwc⟩ : C(Icc 0 τ,G))
        (projIcc 0 τ hτ.le s)
    have hqxe_eq (s : ℝ) (hs : s ∈ Icc 0 τ) : qxe s = qxy s := by
      dsimp [qxe]; rw [projIcc_of_mem _ hs]; rfl
    have hqze_eq (s : ℝ) (hs : s ∈ Icc 0 τ) : qze s = qzw s := by
      dsimp [qze]; rw [projIcc_of_mem _ hs]; rfl
    have hqe_sub (s : ℝ) : qe s = qxe s - qze s := by
      dsimp [qe, qxe, qze, qc]
      rfl
    have hrow_cont (q : ℝ → G) (hq : Continuous q) (k : K) :
        Continuous (fun s : ℝ => (WithLp.toLp 2 (fun i : Fin 2 =>
          ∑ j : Fin 2, κ k j * q s k (i,j)) : V)) := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
      apply continuous_pi
      intro i
      apply continuous_finsetSum
      intro j hj
      exact continuous_const.mul
        ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 × Fin 2 => ℂ) (i,j)).continuous.comp
          ((lp.evalCLM ℝ (fun _ : K => TV) 2 k).continuous.comp hq))
    have hkernel_cont (q : ℝ → G) (hq : Continuous q) (t : ℝ) (k : K) :
        Continuous (fun s : ℝ => Real.exp (-ν * (t-s) * ρ k) •
          (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
            ∑ j : Fin 2, κ k j * q s k (i,j))))) := by
      exact (Real.continuous_exp.comp (by fun_prop)).smul
        ((continuous_const : Continuous (fun _ : ℝ => (Complex.I : ℂ))).smul
          ((P k).continuous.comp (hrow_cont q hq k)))
    have hD_eq (t : ℝ) (ht : t ∈ Icc 0 τ) : Dxy t - Dzw t = Ddiff t := by
      apply lp.ext
      funext k
      let f : (ℝ → G) → ℝ → V := fun q s =>
        Real.exp (-ν * (t-s) * ρ k) •
          (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
            ∑ j : Fin 2, κ k j * q s k (i,j))))
      have hfi : IntervalIntegrable (f qxe) volume 0 t :=
        (hkernel_cont qxe hqxy_ext t k).intervalIntegrable 0 t
      have hfj : IntervalIntegrable (f qze) volume 0 t :=
        (hkernel_cont qze hqzw_ext t k).intervalIntegrable 0 t
      have hfx : Dxy t k = ∫ s in (0:ℝ)..t, f qxe s := by
        rw [hDxyk t ht k]
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ Icc 0 τ := by
          rw [uIcc_of_le ht.1] at hs
          exact ⟨hs.1, hs.2.trans ht.2⟩
        dsimp [f]
        rw [hqxe_eq s hs', hqxyk s hs' k]
        rfl
      have hfz : Dzw t k = ∫ s in (0:ℝ)..t, f qze s := by
        rw [hDzwk t ht k]
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ Icc 0 τ := by
          rw [uIcc_of_le ht.1] at hs
          exact ⟨hs.1, hs.2.trans ht.2⟩
        dsimp [f]
        rw [hqze_eq s hs', hqzwk s hs' k]
        rfl
      rw [lp.coeFn_sub, Pi.sub_apply, hfx, hfz, hDdiffk t ht k,
        ← intervalIntegral.integral_sub hfi hfj]
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp [f]
      have hcoord : qe s k = qxe s k - qze s k := by
        rw [hqe_sub]
        rfl
      rw [hcoord]
      let row : G → V := fun q => WithLp.toLp 2 (fun i : Fin 2 =>
        ∑ j : Fin 2, κ k j * q k (i,j))
      have hrow : row (qxe s) - row (qze s) = row (qxe s - qze s) := by
        ext i
        change (∑ j : Fin 2, κ k j * qxe s k (i,j)) -
            (∑ j : Fin 2, κ k j * qze s k (i,j)) =
            ∑ j : Fin 2, κ k j * (qxe s k (i,j) - qze s k (i,j))
        simp only [mul_sub, Finset.sum_sub_distrib]
      change Real.exp (-ν * (t-s) * ρ k) • (Complex.I • P k (row (qxe s))) -
          Real.exp (-ν * (t-s) * ρ k) • (Complex.I • P k (row (qze s))) =
          Real.exp (-ν * (t-s) * ρ k) •
            (Complex.I • P k (row (qxe s - qze s)))
      rw [← smul_sub, ← smul_sub, ← map_sub, hrow]
    refine ⟨Dxy, Dzw, hDxyc, hDzwc, hDxy0, hDzw0,
      hDxyb, hDzwb, hDxyk, hDzwk, ?_⟩
    intro t ht
    rw [hD_eq t ht]
    have h := hDdiffb t ht
    calc
      ‖Ddiff t‖ ≤ 2 * C * Real.sqrt (t / ν) := h
      _ = 32 * (Dx * My + Mz * Dy) * Real.sqrt (t / ν) := by
        dsimp [C]
        ring
  intro K V TV H ρ κ P R τ a b X0
  have hphysical (x y : ℝ) (i : Fin 2) :
      (∑' k : K, ((((weight k)⁻¹:ℝ):ℂ) * X0 k i) *
        D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.character k x y) =
      (D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.realVelocity α β x y i.castSucc : ℂ) := by
    rw [tsum_eq_sum (s := {(1,0),(-1,0),(-1,1),(1,-1)})]
    · have h := D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.synthesis_eq_realVelocity
        α β x y i.castSucc
      have hf0 : D5.S3.FluidDynamics.Fourier.LowModeReversalWitness.frequency (0:Fin 4) = (1,0) := by decide
      have hf1 : D5.S3.FluidDynamics.Fourier.LowModeReversalWitness.frequency (1:Fin 4) = (-1,0) := by decide
      have hf2 : D5.S3.FluidDynamics.Fourier.LowModeReversalWitness.frequency (2:Fin 4) = (-1,1) := by decide
      have hf3 : D5.S3.FluidDynamics.Fourier.LowModeReversalWitness.frequency (3:Fin 4) = (1,-1) := by decide
      convert h using 1
      simp only [D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.synthesis,
        Fin.sum_univ_four, hf0, hf1, hf2, hf3]
      fin_cases i <;>
        norm_num [K, X0, lp.single_apply, a, b, weight,
          D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.synthesis,
          D5.S3.FluidDynamics.Fourier.LowModeReversalWitness.inputAmplitude,
          Fin.sum_univ_four, Fin.ext_iff] <;> ring
    · intro k hk
      have hk' : k ≠ (1,0) ∧ k ≠ (-1,0) ∧ k ≠ (-1,1) ∧ k ≠ (1,-1) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
      simp [X0, lp.single_apply, hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2]
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hτ : 0 < τ := div_pos hν (by positivity)
  let kernel (x : ℝ → H) (t : ℝ) (k : K) (s : ℝ) : V :=
    Real.exp (-ν*(t-s)*ρ k) • (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
      ∑ j : Fin 2, κ k j * (weight k • convolution
        (fun l => (weight l)⁻¹ • x s l) (fun l => (weight l)⁻¹ • x s l) k) (i,j))))
  have hUnrestricted (x y : ℝ → H) (hx : ContinuousOn x (Icc 0 τ))
      (hy : ContinuousOn y (Icc 0 τ))
      (hm : ∀ t ∈ Icc 0 τ, ∀ k,
        x t k - y t k = (∫ s in (0:ℝ)..t, kernel y t k s) -
          ∫ s in (0:ℝ)..t, kernel x t k s) :
      ∀ t ∈ Icc 0 τ, x t = y t := by
    obtain ⟨tx,htx,hmaxx⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hτ.le) hx.norm
    obtain ⟨ty,hty,hmaxy⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hτ.le) hy.norm
    let M : ℝ := ‖x tx‖ + ‖y ty‖ + 1
    have hM : 0 < M := by dsimp [M]; positivity
    have hxb (s : ℝ) (hs : s ∈ Icc 0 τ) : ‖x s‖ ≤ M := by
      have hh : ‖x s‖ ≤ ‖x tx‖ := hmaxx hs
      dsimp [M]; linarith [norm_nonneg (y ty)]
    have hyb (s : ℝ) (hs : s ∈ Icc 0 τ) : ‖y s‖ ≤ M := by
      have hh : ‖y s‖ ≤ ‖y ty‖ := hmaxy hs
      dsimp [M]; linarith [norm_nonneg (x tx)]
    let G := lp (fun _ : K => TV) 2
    obtain ⟨qx,hqxc,_,hqxk,_,_,_,_,_,_,_,_,_,_⟩ :=
      hTensor ν τ hν hτ x x hx hx M M hM.le hM.le hxb hxb
    obtain ⟨qy,hqyc,_,hqyk,_,_,_,_,_,_,_,_,_,_⟩ :=
      hTensor ν τ hν hτ y y hy hy M M hM.le hM.le hyb hyb
    let qe (q : ℝ → G) : ℝ → G := fun s => q (projIcc 0 τ hτ.le s)
    have hqec (q : ℝ → G) (hc : ContinuousOn q (Icc 0 τ)) : Continuous (qe q) :=
      (continuousOn_iff_continuous_domRestrict.mp hc).comp continuous_projIcc
    let FK (q : ℝ → G) (t : ℝ) (k : K) (s : ℝ) : V :=
      Real.exp (-ν*(t-s)*ρ k) • (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
        ∑ j : Fin 2, κ k j * qe q s k (i,j))))
    have hFKc (q : ℝ → G) (hc : ContinuousOn q (Icc 0 τ)) (t : ℝ) (k : K) :
        Continuous (FK q t k) := by
      apply (Real.continuous_exp.comp (by fun_prop)).smul
      apply (continuous_const : Continuous (fun _ : ℝ => (Complex.I:ℂ))).smul
      apply (P k).continuous.comp
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
      apply continuous_pi
      intro i
      apply continuous_finsetSum
      intro j hj
      exact continuous_const.mul
        ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 × Fin 2 => ℂ) (i,j)).continuous.comp
          ((lp.evalCLM ℝ (fun _ : K => TV) 2 k).continuous.comp (hqec q hc)))
    have hFx (t : ℝ) (k : K) (s : ℝ) (hs : s ∈ Icc 0 τ) :
        FK qx t k s = kernel x t k s := by
      dsimp [FK,qe]
      rw [projIcc_of_mem _ hs, hqxk s hs k]
    have hFy (t : ℝ) (k : K) (s : ℝ) (hs : s ∈ Icc 0 τ) :
        FK qy t k s = kernel y t k s := by
      dsimp [FK,qe]
      rw [projIcc_of_mem _ hs, hqyk s hs k]
    have hmF (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        x t k - y t k = ∫ s in (0:ℝ)..t, FK qy t k s - FK qx t k s := by
      rw [intervalIntegral.integral_sub
        ((hFKc qy hqyc t k).intervalIntegrable 0 t)
        ((hFKc qx hqxc t k).intervalIntegrable 0 t), hm t ht k]
      congr 1 <;> apply intervalIntegral.integral_congr <;> intro s hs
      · exact (hFy t k s (by rw [uIcc_of_le ht.1] at hs; exact ⟨hs.1,hs.2.trans ht.2⟩)).symm
      · exact (hFx t k s (by rw [uIcc_of_le ht.1] at hs; exact ⟨hs.1,hs.2.trans ht.2⟩)).symm
    let δ : ℝ := ν/(16384*M^2)
    have hδ : 0 < δ := div_pos hν (by positivity)
    have hδsqrt : Real.sqrt (δ/ν) = 1/(128*M) := by
      rw [show δ/ν = (1/(128*M))^2 by dsimp [δ]; field_simp [hν.ne',hM.ne']; ring]
      exact Real.sqrt_sq (by positivity)
    have hStep (a : ℝ) (ha : 0 ≤ a) (haτ : a < τ)
        (hpast : ∀ s ∈ Icc 0 a, x s = y s) :
        ∀ t ∈ Icc a (min τ (a+δ)), x t = y t := by
      let T : ℝ := min τ (a+δ)-a
      have hT : 0 < T := sub_pos.mpr (lt_min haτ (by linarith))
      have hTδ : T ≤ δ := by dsimp [T]; linarith [min_le_right τ (a+δ)]
      have hsτ (s : ℝ) (hs : s ∈ Icc 0 T) : a+s ∈ Icc 0 τ := by
        dsimp [T] at hs
        constructor
        · linarith [hs.1]
        · linarith [hs.2,min_le_left τ (a+δ)]
      let xx : ℝ → H := fun s => x (a+s)
      let yy : ℝ → H := fun s => y (a+s)
      have hxx : ContinuousOn xx (Icc 0 T) :=
        hx.comp (by fun_prop) hsτ
      have hyy : ContinuousOn yy (Icc 0 T) :=
        hy.comp (by fun_prop) hsτ
      let diff : C(Icc (0:ℝ) T,H) :=
        ⟨fun s => xx s - yy s,
          continuousOn_iff_continuous_domRestrict.mp (hxx.sub hyy)⟩
      have hd (s : ℝ) (hs : s ∈ Icc 0 T) : ‖xx s - yy s‖ ≤ ‖diff‖ :=
        diff.norm_coe_le_norm ⟨s,hs⟩
      obtain ⟨DX,DY,_,_,_,_,_,_,hDX,hDY,hdb⟩ :=
        hDifference ν T hν hT xx xx yy yy hxx hxx hyy hyy
          M M M M ‖diff‖ ‖diff‖ hM.le hM.le hM.le hM.le
          (norm_nonneg _) (norm_nonneg _)
          (fun s hs => hxb _ (hsτ s hs)) (fun s hs => hxb _ (hsτ s hs))
          (fun s hs => hyb _ (hsτ s hs)) (fun s hs => hyb _ (hsτ s hs)) hd hd
      have hlocal (r : ℝ) (hr : r ∈ Icc 0 T) : xx r - yy r = DY r - DX r := by
        apply lp.ext
        funext k
        change x (a+r) k - y (a+r) k = DY r k - DX r k
        rw [hmF (a+r) (hsτ r hr) k, hDX r hr k, hDY r hr k]
        let F : ℝ → V := fun s => FK qy (a+r) k s - FK qx (a+r) k s
        have hFc : Continuous F := (hFKc qy hqyc _ _).sub (hFKc qx hqxc _ _)
        have hp : (∫ s in (0:ℝ)..a, F s) = 0 := by
          rw [← intervalIntegral.integral_zero (a := (0:ℝ)) (b := a) (E := V)]
          apply intervalIntegral.integral_congr
          intro s hs
          have hsa : s ∈ Icc 0 a := by simpa [uIcc_of_le ha] using hs
          have hst : s ∈ Icc 0 τ := ⟨hsa.1,hsa.2.trans haτ.le⟩
          dsimp [F]
          rw [hFy _ _ s hst,hFx _ _ s hst]
          have he : kernel y (a+r) k s = kernel x (a+r) k s := by
            dsimp [kernel]
            rw [hpast s hsa]
          rw [he,sub_self]
        change (∫ s in (0:ℝ)..(a+r), F s) = _
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hFc.intervalIntegrable 0 a) (hFc.intervalIntegrable a (a+r)),hp,zero_add]
        have hshift := intervalIntegral.integral_comp_add_left (a := 0) (b := r) F a
        simp only [add_zero] at hshift
        rw [← hshift]
        have hg : (fun s => F (a+s)) = (fun s => FK qy (a+r) k (a+s) - FK qx (a+r) k (a+s)) := rfl
        have hiy : IntervalIntegrable (fun s : ℝ => FK qy (a+r) k (a+s)) volume 0 r :=
          ((hFKc qy hqyc (a+r) k).comp
            (show Continuous (fun s : ℝ => a+s) from continuous_const.add continuous_id)).intervalIntegrable 0 r
        have hix : IntervalIntegrable (fun s : ℝ => FK qx (a+r) k (a+s)) volume 0 r :=
          ((hFKc qx hqxc (a+r) k).comp
            (show Continuous (fun s : ℝ => a+s) from continuous_const.add continuous_id)).intervalIntegrable 0 r
        rw [hg,intervalIntegral.integral_sub hiy hix]
        congr 1 <;> apply intervalIntegral.integral_congr <;> intro s hs
        · change FK qy (a+r) k (a+s) = kernel yy r k s
          calc
            _ = kernel y (a+r) k (a+s) := hFy (a+r) k (a+s)
              (hsτ s (by rw [uIcc_of_le hr.1] at hs; exact ⟨hs.1,hs.2.trans hr.2⟩))
            _ = _ := by dsimp [kernel,yy]; rw [show a+r-(a+s) = r-s by ring]
        · change FK qx (a+r) k (a+s) = kernel xx r k s
          calc
            _ = kernel x (a+r) k (a+s) := hFx (a+r) k (a+s)
              (hsτ s (by rw [uIcc_of_le hr.1] at hs; exact ⟨hs.1,hs.2.trans hr.2⟩))
            _ = _ := by dsimp [kernel,xx]; rw [show a+r-(a+s) = r-s by ring]
      have hdn : ‖diff‖ ≤ (1/2:ℝ)*‖diff‖ := by
        apply (ContinuousMap.norm_le _ (by positivity)).mpr
        intro r
        change ‖xx r - yy r‖ ≤ _
        rw [hlocal r r.2, norm_sub_rev]
        calc
          ‖DX r - DY r‖ ≤ 32*(‖diff‖*M+M*‖diff‖)*Real.sqrt (r.1/ν) := hdb r r.2
          _ ≤ 32*(‖diff‖*M+M*‖diff‖)*Real.sqrt (δ/ν) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
              (div_le_div_of_nonneg_right (r.2.2.trans hTδ) hν.le)) (by positivity)
          _ = (1/2:ℝ)*‖diff‖ := by rw [hδsqrt]; field_simp; ring
      have hz : ‖diff‖ = 0 := by have hh := norm_nonneg diff; linarith
      intro t ht
      have hr : t-a ∈ Icc 0 T := by dsimp [T]; constructor <;> linarith [ht.1,ht.2]
      have hh := hd (t-a) hr
      rw [hz] at hh
      have he := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
      dsimp [xx,yy] at he
      rw [add_sub_cancel] at he
      exact sub_eq_zero.mp he
    have hblocks (n : ℕ) : ∀ t ∈ Icc 0 (min τ ((n:ℝ)*δ)), x t = y t := by
      induction n with
      | zero =>
        intro t ht
        have ht0 : t = 0 := le_antisymm
          (by simpa only [Nat.cast_zero,zero_mul,min_eq_right hτ.le] using ht.2) ht.1
        subst t
        apply lp.ext
        funext k
        exact sub_eq_zero.mp (by simpa using hm 0 (by simp [hτ.le]) k)
      | succ n ih =>
        by_cases hn : τ ≤ (n:ℝ)*δ
        · intro t ht
          exact ih t ⟨ht.1, by simpa [min_eq_left hn] using ht.2.trans (min_le_left _ _)⟩
        · have hnτ : (n:ℝ)*δ < τ := lt_of_not_ge hn
          intro t ht
          have htop : min τ ((↑(n+1):ℝ)*δ) = min τ ((n:ℝ)*δ+δ) := by congr 1; push_cast; ring
          rw [htop] at ht
          by_cases htn : t ≤ (n:ℝ)*δ
          · exact ih t ⟨ht.1, by simpa [min_eq_right hnτ.le] using htn⟩
          · exact hStep ((n:ℝ)*δ) (by positivity) hnτ
              (fun s hs => ih s ⟨hs.1, by simpa [min_eq_right hnτ.le] using hs.2⟩)
              t ⟨(lt_of_not_ge htn).le,ht.2⟩
    obtain ⟨n,hn⟩ := exists_nat_gt (τ/δ)
    have hcover : τ ≤ (n:ℝ)*δ := by
      have hh := (div_lt_iff₀ hδ).mp hn
      exact hh.le
    intro t ht
    exact hblocks n t ⟨ht.1,by simpa [min_eq_left hcover] using ht.2⟩
  have hρ (k : K) : 0 ≤ ρ k := by dsimp [ρ]; positivity
  have hw (k : K) : 0 < weight k := by dsimp [weight]; positivity
  have hρneg (k : K) : ρ (-k) = ρ k := by
    change ((-k.1:ℤ):ℝ)^2 + ((-k.2:ℤ):ℝ)^2 = _
    simp [ρ]
  have hwneg (k : K) : weight (-k) = weight k := by
    change 1 + ((-k.1:ℤ):ℝ)^2 + ((-k.2:ℤ):ℝ)^2 = _
    simp [weight]
  have hκneg (k : K) : κ (-k) = -κ k := by
    ext i
    fin_cases i
    · change ((-k.1:ℤ) : ℂ) = -(k.1 : ℂ)
      simp
    · change ((-k.2:ℤ) : ℂ) = -(k.2 : ℂ)
      simp
  have hκstar (k : K) (i : Fin 2) : star (κ k i) = κ k i := by
    fin_cases i <;> simp [κ]
  have hκnorm (k : K) : ‖κ k‖^2 = ρ k := by
    simp [V, EuclideanSpace.norm_sq_eq, κ, ρ, Complex.norm_intCast,
      sq_abs, Fin.sum_univ_two]
  let CVL : V →ₗ[ℝ] V :=
    { toFun := fun z => WithLp.toLp 2 (fun i => star (z i))
      map_add' := by
        intro z w
        ext i
        change star (z i + w i) = star (z i) + star (w i)
        exact star_add _ _
      map_smul' := by
        intro r z
        ext i
        change star ((r:ℂ) * z i) = (r:ℂ) * star (z i)
        simp }
  have hCVnorm (z : V) : ‖CVL z‖ = ‖z‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [V, EuclideanSpace.norm_sq_eq, CVL]
  let CV : V →L[ℝ] V := CVL.mkContinuous 1 (by intro z; rw [hCVnorm]; simp)
  have hCV (z : V) (i : Fin 2) : CV z i = star (z i) := rfl
  have hPformula (k : K) (z : V) (i : Fin 2) :
      P k z i = z i - ((∑ j : Fin 2, κ k j * z j) / (ρ k : ℂ)) * κ k i := by
    dsimp [P]
    rw [Submodule.starProjection_orthogonal]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      Submodule.starProjection_singleton, hκnorm]
    change z i - (inner ℂ (κ k) z / (ρ k : ℂ)) * κ k i = _
    congr 2
    simp [V, PiLp.inner_apply, κ, mul_comm]
  have hPeven (k : K) : P (-k) = P k := by
    apply ContinuousLinearMap.ext
    intro z
    ext i
    rw [hPformula, hPformula, hρneg, hκneg]
    change z i - ((∑ j : Fin 2, -κ k j * z j) / (ρ k : ℂ)) * (-κ k i) = _
    simp only [neg_mul, Finset.sum_neg_distrib, neg_div, neg_mul_neg]
    ring
  have hPstar (k : K) (z : V) : P k (CV z) = CV (P k z) := by
    ext i
    rw [hCV (P k z) i, hPformula, hPformula]
    simp only [hCV, star_sub, star_mul, star_div₀, star_sum,
      hκstar, Complex.star_def, Complex.conj_ofReal, mul_comm]
  let S : Submodule ℝ H :=
    { carrier := {z | z 0 = 0 ∧ (∀ k i, z (-k) i = star (z k i)) ∧
        ∀ k, P k (z k) = z k}
      zero_mem' := by simp
      add_mem' := by
        intro z w hz hw'
        refine ⟨by simp [hz.1, hw'.1], ?_, ?_⟩
        · intro k i
          change z (-k) i + w (-k) i = star (z k i + w k i)
          rw [hz.2.1, hw'.2.1, star_add]
        · intro k
          change P k (z k + w k) = z k + w k
          rw [map_add, hz.2.2, hw'.2.2]
      smul_mem' := by
        intro r z hz
        refine ⟨?_, ?_, ?_⟩
        · change r • z 0 = 0
          rw [hz.1, smul_zero]
        · intro k i
          change (r:ℂ) * z (-k) i = star ((r:ℂ) * z k i)
          simp [hz.2.1]
        · intro k
          change P k (r • z k) = r • z k
          rw [(P k).map_smul_of_tower, hz.2.2] }
  have hSclosed : IsClosed (S : Set H) := by
    have hz : IsClosed {z : H | z 0 = 0} :=
      isClosed_eq (lp.evalCLM ℝ (fun _ : K => V) 2 0).continuous continuous_const
    have hc : IsClosed {z : H | ∀ k i, z (-k) i = star (z k i)} := by
      have hc' : IsClosed (⋂ k : K, ⋂ i : Fin 2,
          {z : H | z (-k) i = star (z k i)}) := by
        apply isClosed_iInter
        intro k
        apply isClosed_iInter
        intro i
        let ev (l : K) := (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 => ℂ) i).continuous.comp
          (lp.evalCLM ℝ (fun _ : K => V) 2 l).continuous
        exact isClosed_eq (ev (-k)) (continuous_star.comp (ev k))
      convert hc' using 1
      ext z
      simp
    have hp : IsClosed {z : H | ∀ k, P k (z k) = z k} := by
      have hp' : IsClosed (⋂ k : K, {z : H | P k (z k) = z k}) := by
        apply isClosed_iInter
        intro k
        exact isClosed_eq ((P k).continuous.comp
          (lp.evalCLM ℝ (fun _ : K => V) 2 k).continuous)
          (lp.evalCLM ℝ (fun _ : K => V) 2 k).continuous
      convert hp' using 1
      ext z
      simp
    exact hz.inter (hc.inter hp)
  letI : CompleteSpace S := hSclosed.completeSpace_coe
  let Path := C(Icc (0:ℝ) τ, S)
  let xe (x : Path) (t : ℝ) : H := x (projIcc 0 τ hτ.le t)
  have hxe (x : Path) : Continuous (xe x) :=
    (continuous_subtype_val.comp x.continuous).comp continuous_projIcc
  have hxen (x : Path) (t : ℝ) : ‖xe x t‖ ≤ ‖x‖ :=
    x.norm_coe_le_norm _
  let row (k : K) (Z : TV) : V := WithLp.toLp 2 (fun i : Fin 2 =>
    ∑ j : Fin 2, κ k j * Z (i,j))
  have hDexists (x y : Path) : ∃ d : Path,
      ‖d‖ ≤ 32 * ‖x‖ * ‖y‖ * Real.sqrt (τ/ν) ∧
      d ⟨0, by simp [hτ.le]⟩ = 0 ∧
      ∀ t : Icc (0:ℝ) τ, ∀ k : K,
        (d t : H) k = ∫ s in (0:ℝ)..t.1,
          Real.exp (-ν*(t.1-s)*ρ k) •
            (Complex.I • P k (row k (weight k • convolution
              (fun l => (weight l)⁻¹ • xe x s l)
              (fun l => (weight l)⁻¹ • xe y s l) k))) := by
    obtain ⟨q, hqc, hqn, hqk, hqs, _, _, D, hDc, hD0, hDn, hDP, hDz, hDk⟩ :=
      hTensor ν τ hν hτ (xe x) (xe y) (hxe x).continuousOn (hxe y).continuousOn
        ‖x‖ ‖y‖ (norm_nonneg _) (norm_nonneg _)
        (fun t _ => hxen x t) (fun t _ => hxen y t)
    let dec (z : H) (k : K) := (weight k)⁻¹ • z k
    have hdstar (z : H) (hz : z ∈ S) (k : K) (i : Fin 2) :
        dec z (-k) i = star (dec z k i) := by
      change (((weight (-k))⁻¹:ℝ):ℂ) * z (-k) i =
        star ((((weight k)⁻¹:ℝ):ℂ) * z k i)
      rw [hwneg, hz.2.1]
      simp [mul_comm]
    have hqcoord (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) (i j : Fin 2) :
        q t k (i,j) = (weight k : ℂ) *
          ∑' p : K, dec (xe x t) p i * dec (xe y t) (k-p) j := by
      rw [hqk t ht k]
      change (weight k : ℂ) * (convolution (dec (xe x t)) (dec (xe y t)) k) (i,j) = _
      congr 1
      exact (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 × Fin 2 => ℂ) (i,j)).map_tsum
        (hqs t ht k).2.1
    have hqstar (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) (i j : Fin 2) :
        q t (-k) (i,j) = star (q t k (i,j)) := by
      rw [hqcoord t ht (-k), hqcoord t ht k, star_mul, tsum_star, hwneg]
      simp only [Complex.star_def, Complex.conj_ofReal]
      conv_rhs => rw [mul_comm]
      congr 1
      calc
        (∑' p : K, dec (xe x t) p i * dec (xe y t) (-k-p) j) =
            ∑' p : K, dec (xe x t) (-p) i * dec (xe y t) (-k- -p) j :=
          (tsum_comp_neg _).symm
        _ = _ := by
          apply tsum_congr
          intro p
          rw [show -k- -p = -(k-p) by abel,
            hdstar (xe x t) (x (projIcc 0 τ hτ.le t)).2 p i,
            hdstar (xe y t) (y (projIcc 0 τ hτ.le t)).2 (k-p) j]
          simp
    let qe : ℝ → lp (fun _ : K => TV) 2 := fun s => q (projIcc 0 τ hτ.le s)
    have hqec : Continuous qe :=
      (continuousOn_iff_continuous_domRestrict.mp hqc).comp continuous_projIcc
    have hqeEq (s : ℝ) (hs : s ∈ Icc 0 τ) : qe s = q s := by
      dsimp [qe]
      rw [projIcc_of_mem _ hs]
    have hqeStar (s : ℝ) (k : K) (i j : Fin 2) :
        qe s (-k) (i,j) = star (qe s k (i,j)) :=
      hqstar _ (projIcc 0 τ hτ.le s).2 k i j
    let f (t : ℝ) (k : K) (s : ℝ) : V :=
      Real.exp (-ν*(t-s)*ρ k) • (Complex.I • P k (row k (qe s k)))
    have hfc (t : ℝ) (k : K) : Continuous (f t k) := by
      have hqev : Continuous (fun s => qe s k) :=
        (lp.evalCLM ℝ (fun _ : K => TV) 2 k).continuous.comp hqec
      have hrow : Continuous (fun s => row k (qe s k)) := by
        apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
        apply continuous_pi
        intro i
        apply continuous_finsetSum
        intro j hj
        exact continuous_const.mul
          ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 × Fin 2 => ℂ) (i,j)).continuous.comp hqev)
      exact (Real.continuous_exp.comp (by fun_prop)).smul
        ((continuous_const : Continuous (fun _ : ℝ => (Complex.I:ℂ))).smul
          ((P k).continuous.comp hrow))
    have hDq (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        D t k = ∫ s in (0:ℝ)..t, f t k s := by
      rw [hDk t ht k]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc (0:ℝ) τ := by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      dsimp [f]
      rw [hqeEq s hs', hqk s hs' k]
      rfl
    have hrowStar (s : ℝ) (k : K) : row (-k) (qe s (-k)) = -CV (row k (qe s k)) := by
      ext i
      change (∑ j : Fin 2, κ (-k) j * qe s (-k) (i,j)) =
        -star (∑ j : Fin 2, κ k j * qe s k (i,j))
      rw [hκneg]
      change (∑ j : Fin 2, -κ k j * qe s (-k) (i,j)) = _
      simp only [hqeStar, star_sum, star_mul, hκstar, neg_mul, Finset.sum_neg_distrib]
      simp [mul_comm]
    have hfstar (t s : ℝ) (k : K) : f t (-k) s = CV (f t k s) := by
      dsimp [f]
      rw [hρneg, hPeven, hrowStar, map_neg, hPstar]
      ext i
      change (Real.exp (-ν*(t-s)*ρ k):ℂ) * (Complex.I * (-star (P k (row k (qe s k)) i))) =
        star ((Real.exp (-ν*(t-s)*ρ k):ℂ) * (Complex.I * P k (row k (qe s k)) i))
      simp only [Complex.star_def, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
      ring
    have hDstar (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) : D t (-k) = CV (D t k) := by
      rw [hDq t ht (-k), hDq t ht k,
        ← CV.intervalIntegral_comp_comm ((hfc t k).intervalIntegrable 0 t)]
      apply intervalIntegral.integral_congr
      intro s hs
      exact hfstar t s k
    have hDS (t : ℝ) (ht : t ∈ Icc 0 τ) : D t ∈ S := by
      refine ⟨hDz t ht, ?_, hDP t ht⟩
      intro k i
      rw [hDstar t ht k, hCV]
    let d : Path := ⟨fun t => ⟨D t, hDS t.1 t.2⟩,
      (hDc.comp continuous_subtype_val).subtype_mk _⟩
    refine ⟨d, ?_, ?_, ?_⟩
    · apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro t
      change ‖D t.1‖ ≤ _
      exact (hDn t.1 t.2).trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right t.2.2 hν.le)) (by positivity))
    · apply Subtype.ext
      exact hD0
    · intro t k
      exact hDk t.1 t.2 k
  let A0 : H := lp.single 2 (1,0) a + lp.single 2 (-1,0) a
  let B0 : H := lp.single 2 (-1,1) b + lp.single 2 (1,-1) b
  have hX0 (k : K) : X0 k =
      (if k = (1,0) ∨ k = (-1,0) then a else 0) +
      (if k = (-1,1) ∨ k = (1,-1) then b else 0) := by
    by_cases h1 : k = (1,0)
    · subst k; norm_num [K, X0, lp.single_apply, Prod.mk.injEq]
    by_cases h2 : k = (-1,0)
    · subst k; norm_num [K, X0, lp.single_apply, Prod.mk.injEq]
    by_cases h3 : k = (-1,1)
    · subst k; norm_num [K, X0, lp.single_apply, Prod.mk.injEq]
    by_cases h4 : k = (1,-1)
    · subst k; norm_num [K, X0, lp.single_apply, Prod.mk.injEq]
    simp [X0, lp.single_apply, h1, h2, h3, h4]
  have hX0S : X0 ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · change X0 ((0:ℤ),(0:ℤ)) = 0
      rw [hX0]; norm_num [K, Prod.mk.injEq]
    · intro k i
      have hn1 : (-k = (1,0)) ↔ k = (-1,0) := by
        rw [neg_eq_iff_eq_neg]; rfl
      have hn2 : (-k = (-1,0)) ↔ k = (1,0) := by
        rw [neg_eq_iff_eq_neg]; rfl
      have hn3 : (-k = (-1,1)) ↔ k = (1,-1) := by
        rw [neg_eq_iff_eq_neg]; rfl
      have hn4 : (-k = (1,-1)) ↔ k = (-1,1) := by
        rw [neg_eq_iff_eq_neg]; rfl
      rw [hX0 (-k), hX0 k]
      change ((if -k = (1,0) ∨ -k = (-1,0) then a else 0) i +
        (if -k = (-1,1) ∨ -k = (1,-1) then b else 0) i) =
        star ((if k = (1,0) ∨ k = (-1,0) then a else 0) i +
          (if k = (-1,1) ∨ k = (1,-1) then b else 0) i)
      simp only [hn1, hn2, hn3, hn4, or_comm]
      split_ifs <;> fin_cases i <;> simp [a, b, star_add, K]
    · intro k
      apply Submodule.starProjection_eq_self_iff.mpr
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      by_cases h1 : k = (1,0)
      · subst k; rw [hX0]; norm_num [a, κ, V, PiLp.inner_apply, K, Prod.mk.injEq]
      by_cases h2 : k = (-1,0)
      · subst k; rw [hX0]; norm_num [a, κ, V, PiLp.inner_apply, K, Prod.mk.injEq]
      by_cases h3 : k = (-1,1)
      · subst k; rw [hX0]; norm_num [b, κ, V, PiLp.inner_apply, K, Prod.mk.injEq]
      by_cases h4 : k = (1,-1)
      · subst k; rw [hX0]; norm_num [b, κ, V, PiLp.inner_apply, K, Prod.mk.injEq]
      rw [hX0]; simp [h1, h2, h3, h4]
  have hX0norm : ‖X0‖^2 = 2*α^2 + 9*β^2 := by
    have hh : ‖X0‖^2 = ∑' k : K, ‖X0 k‖^2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) X0
    rw [hh, tsum_eq_sum (s := {(1,0),(-1,0),(-1,1),(1,-1)})]
    · norm_num [X0, lp.single_apply, a, b, V, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      nlinarith [sq_abs β]
    · intro k hk
      have hk' : k ≠ (1,0) ∧ k ≠ (-1,0) ∧ k ≠ (-1,1) ∧ k ≠ (1,-1) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
      rw [hX0]
      simp [hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2]
  have hX0bound : ‖X0‖ ≤ R/2 := by
    have hr2 : R^2 = 4*(2*A^2 + 9*B^2) := by
      dsimp [R]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have ha2 : α^2 ≤ A^2 := by nlinarith [sq_abs α, abs_nonneg α]
    have hb2 : β^2 ≤ B^2 := by nlinarith [sq_abs β, abs_nonneg β]
    nlinarith [norm_nonneg X0, hX0norm]
  let E : ℝ → H := fun t => Real.exp (-ν*t) • A0 + Real.exp (-2*ν*t) • B0
  have hEc : Continuous E :=
    ((Real.continuous_exp.comp (by fun_prop)).smul continuous_const).add
      ((Real.continuous_exp.comp (by fun_prop)).smul continuous_const)
  have hEk (t : ℝ) (k : K) : E t k = Real.exp (-ν*t*ρ k) • X0 k := by
    change Real.exp (-ν*t) • A0 k + Real.exp (-2*ν*t) • B0 k = _
    by_cases h1 : k = (1,0)
    · subst k; norm_num [A0, B0, X0, lp.single_apply, ρ]
    by_cases h2 : k = (-1,0)
    · subst k; norm_num [A0, B0, X0, lp.single_apply, ρ]
    by_cases h3 : k = (-1,1)
    · subst k
      norm_num [A0, B0, X0, lp.single_apply, ρ,
        show -(2*ν*t) = -(ν*t*2) by ring]
    by_cases h4 : k = (1,-1)
    · subst k
      norm_num [A0, B0, X0, lp.single_apply, ρ,
        show -(2*ν*t) = -(ν*t*2) by ring]
    simp [A0, B0, X0, lp.single_apply, h1, h2, h3, h4]
  have hES (t : ℝ) : E t ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hEk, hX0S.1, smul_zero]
    · intro k i
      rw [hEk, hEk, hρneg]
      change (Real.exp (-ν*t*ρ k):ℂ) * X0 (-k) i =
        star ((Real.exp (-ν*t*ρ k):ℂ) * X0 k i)
      rw [hX0S.2.1]
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    · intro k
      rw [hEk, (P k).map_smul_of_tower, hX0S.2.2]
  have hEn (t : ℝ) (ht : 0 ≤ t) : ‖E t‖ ≤ ‖X0‖ := by
    let T (k : K) : V →L[ℂ] V := Real.exp (-ν*t*ρ k) • ContinuousLinearMap.id ℂ V
    have hT (k : K) : ‖T k‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro z
      change ‖Real.exp (-ν*t*ρ k) • z‖ ≤ 1*‖z‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr hν.le) ht) (hρ k))) (norm_nonneg _)
    let M := lp.mapCLM 2 T zero_le_one hT
    have he : M X0 = E t := by
      apply lp.ext
      funext k
      exact (hEk t k).symm
    rw [← he]
    simpa using M.le_of_opNorm_le (lp.norm_mapCLM_le 2 T zero_le_one hT) X0
  let e : Path := ⟨fun t => ⟨E t, hES t⟩,
    (hEc.comp continuous_subtype_val).subtype_mk _⟩
  have hen : ‖e‖ ≤ R/2 := (ContinuousMap.norm_le _ (by positivity)).mpr
    (fun t => (hEn t.1 t.2.1).trans hX0bound)
  have he0 : (e ⟨0, by simp [hτ.le]⟩ : H) = X0 := by
    change E 0 = X0
    simp [E, A0, B0, X0, add_assoc]
  have htime : Real.sqrt (τ/ν) = 1/(128*R) := by
    rw [show τ/ν = (1/(128*R))^2 by
      dsimp [τ]
      field_simp [hν.ne', hR.ne']
      ring]
    exact Real.sqrt_sq (by positivity)
  let D (x y : Path) : Path := Classical.choose (hDexists x y)
  have hDn (x y : Path) : ‖D x y‖ ≤ 32*‖x‖*‖y‖*Real.sqrt (τ/ν) :=
    (Classical.choose_spec (hDexists x y)).1
  have hDzero (x y : Path) : D x y ⟨0, by simp [hτ.le]⟩ = 0 :=
    (Classical.choose_spec (hDexists x y)).2.1
  have hDcoeff (x y : Path) (t : Icc (0:ℝ) τ) (k : K) :
      (D x y t : H) k = ∫ s in (0:ℝ)..t.1,
        Real.exp (-ν*(t.1-s)*ρ k) •
          (Complex.I • P k (row k (weight k • convolution
            (fun l => (weight l)⁻¹ • xe x s l)
            (fun l => (weight l)⁻¹ • xe y s l) k))) :=
    (Classical.choose_spec (hDexists x y)).2.2 t k
  have hDdiff (x y z w : Path) : ‖D x y - D z w‖ ≤
      32 * (‖x-z‖*‖y‖ + ‖z‖*‖y-w‖) * Real.sqrt (τ/ν) := by
    have hxy (t : ℝ) (ht : t ∈ Icc 0 τ) : ‖xe x t - xe z t‖ ≤ ‖x-z‖ :=
      (x-z).norm_coe_le_norm _
    have hyw (t : ℝ) (ht : t ∈ Icc 0 τ) : ‖xe y t - xe w t‖ ≤ ‖y-w‖ :=
      (y-w).norm_coe_le_norm _
    obtain ⟨Dxy, Dzw, _, _, _, _, _, _, hDxyk, hDzwk, hd⟩ :=
      hDifference ν τ hν hτ (xe x) (xe y) (xe z) (xe w)
        (hxe x).continuousOn (hxe y).continuousOn
        (hxe z).continuousOn (hxe w).continuousOn
        ‖x‖ ‖y‖ ‖z‖ ‖w‖ ‖x-z‖ ‖y-w‖
        (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
        (norm_nonneg _) (norm_nonneg _)
        (fun t _ => hxen x t) (fun t _ => hxen y t)
        (fun t _ => hxen z t) (fun t _ => hxen w t) hxy hyw
    have hsame (t : Icc (0:ℝ) τ) : (D x y t : H) = Dxy t.1 ∧
        (D z w t : H) = Dzw t.1 := by
      constructor <;> apply lp.ext <;> funext k
      · exact (hDcoeff x y t k).trans (hDxyk t.1 t.2 k).symm
      · exact (hDcoeff z w t k).trans (hDzwk t.1 t.2 k).symm
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    change ‖(D x y t : H) - (D z w t : H)‖ ≤ _
    rw [(hsame t).1, (hsame t).2]
    exact (hd t.1 t.2).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right t.2.2 hν.le)) (by positivity))
  have hDR (x : Path) (hx : ‖x‖ ≤ R) : ‖D x x‖ ≤ R/4 := by
    calc
      ‖D x x‖ ≤ 32*‖x‖*‖x‖*Real.sqrt (τ/ν) := hDn x x
      _ ≤ 32*R*R*Real.sqrt (τ/ν) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hx (by norm_num)) hx
          (norm_nonneg _) (by positivity)
      _ = R/4 := by rw [htime]; field_simp; ring
  let Φ (x : Path) : Path := e - D x x
  have hΦR (x : Path) (hx : ‖x‖ ≤ R) : ‖Φ x‖ ≤ 3*R/4 :=
    (norm_sub_le _ _).trans (by linarith [hen, hDR x hx])
  have hΦlip (x y : Path) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
      ‖Φ x - Φ y‖ ≤ (1/2:ℝ)*‖x-y‖ := by
    have heq : Φ x - Φ y = -(D x x - D y y) := by dsimp [Φ]; abel
    rw [heq, norm_neg]
    calc
      ‖D x x - D y y‖ ≤ 32*(‖x-y‖*‖x‖+‖y‖*‖x-y‖)*Real.sqrt (τ/ν) :=
        hDdiff x x y y
      _ ≤ 32*(2*R*‖x-y‖)*Real.sqrt (τ/ν) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        nlinarith [norm_nonneg (x-y)]
      _ = (1/2:ℝ)*‖x-y‖ := by rw [htime]; field_simp; ring
  let ball : Set Path := {x | ‖x‖ ≤ R}
  have hball : IsClosed ball := isClosed_le continuous_norm continuous_const
  letI : CompleteSpace ball := hball.completeSpace_coe
  letI : Nonempty ball := ⟨⟨0, by simpa [ball] using hR.le⟩⟩
  let f : ball → ball := fun x => ⟨Φ x, (hΦR x x.2).trans (by linarith)⟩
  have hf : ContractingWith (1/2 : ℝ≥0) f := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (Φ x) (Φ y) ≤ (1/2:ℝ)*dist (x:Path) (y:Path)
    rw [dist_eq_norm, dist_eq_norm]
    exact hΦlip x y x.2 y.2
  let U : ball := hf.fixedPoint f
  have hfix : e - D U U = (U : Path) := congrArg Subtype.val hf.fixedPoint_isFixedPt
  let u : ℝ → H := xe U
  let du : ℝ → H := xe (D U U)
  have hueq (t : Icc (0:ℝ) τ) : (U.val t : H) = (e t : H) - (D U U t : H) :=
    congrArg (fun v : Path => (v t : H)) hfix.symm
  have hdu (t : ℝ) (ht : t ∈ Icc 0 τ) : du t = (D U U ⟨t,ht⟩ : H) := by
    dsimp [du, xe]
    rw [projIcc_of_mem _ ht]
  have hu (t : ℝ) (ht : t ∈ Icc 0 τ) : u t = (U.val ⟨t,ht⟩ : H) := by
    dsimp [u, xe]
    rw [projIcc_of_mem _ ht]
  have humild (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
      u t k = Real.exp (-ν*t*ρ k) • X0 k - ∫ s in (0:ℝ)..t, kernel u t k s := by
    rw [hu t ht,hueq ⟨t,ht⟩]
    change E t k - (D U U ⟨t,ht⟩ : H) k = _
    rw [hEk,hDcoeff]
  have hUnique (v : ℝ → H) (hv : ContinuousOn v (Icc 0 τ))
      (hm : ∀ t ∈ Icc 0 τ, ∀ k,
        v t k = Real.exp (-ν*t*ρ k) • X0 k - ∫ s in (0:ℝ)..t, kernel v t k s) :
      ∀ t ∈ Icc 0 τ, v t = u t := by
    have hh := hUnrestricted u v (hxe U).continuousOn hv (by
      intro t ht k
      rw [humild t ht k,hm t ht k]
      abel)
    exact fun t ht => (hh t ht).symm
  have hStability (β₂ : ℝ) (v : ℝ → H) (hv : ContinuousOn v (Icc 0 τ))
      (hvb : ∀ t ∈ Icc 0 τ, ‖v t‖ ≤ R) :
      let b₂ : V := WithLp.toLp 2 ![(3*β₂/2 : ℂ),(3*β₂/2 : ℂ)]
      let X₂ : H := lp.single 2 (1,0) a + lp.single 2 (-1,0) a +
        lp.single 2 (-1,1) b₂ + lp.single 2 (1,-1) b₂
      (∀ t ∈ Icc 0 τ, ∀ k,
        v t k = Real.exp (-ν*t*ρ k) • X₂ k - ∫ s in (0:ℝ)..t, kernel v t k s) →
      ∀ t ∈ Icc 0 τ, ‖u t-v t‖ ≤ 6*|β-β₂| := by
    intro b₂ X₂ hm
    let bd : V := WithLp.toLp 2 ![((3*(β-β₂)/2:ℝ):ℂ),((3*(β-β₂)/2:ℝ):ℂ)]
    let Z : H := lp.single 2 (-1,1) bd + lp.single 2 (1,-1) bd
    have hinit : X0-X₂ = Z := by
      have hb : b-b₂ = bd := by
        ext i
        fin_cases i <;>
          change 3*(β:ℂ)/2-3*(β₂:ℂ)/2 = ((3*(β-β₂)/2:ℝ):ℂ) <;> push_cast <;> ring
      dsimp [X0,X₂,Z]
      rw [← hb,lp.single_sub,lp.single_sub]
      abel
    have hZn : ‖Z‖ = 3*|β-β₂| := by
      apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
      have hh : ‖Z‖^2 = ∑' k : K, ‖Z k‖^2 := by
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) Z
      rw [hh,tsum_eq_sum (s := {(-1,1),(1,-1)})]
      · norm_num [Z,lp.single_apply,bd,V,EuclideanSpace.norm_sq_eq,
          Fin.sum_univ_two,Complex.norm_real,Real.norm_eq_abs,sq_abs]
        simp only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
        ring
      · intro k hk
        have hk' : k ≠ (-1,1) ∧ k ≠ (1,-1) := by
          simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hk
        simp [Z,lp.single_apply,hk'.1,hk'.2]
    let ez (t : ℝ) : H := Real.exp (-2*ν*t) • Z
    have hezk (t : ℝ) (k : K) : ez t k = Real.exp (-ν*t*ρ k) • (X0-X₂) k := by
      rw [hinit]
      change Real.exp (-2*ν*t) • Z k = Real.exp (-ν*t*ρ k) • Z k
      by_cases hk1 : k = (-1,1)
      · subst k; norm_num [Z,lp.single_apply,ρ,show -(2*ν*t) = -(ν*t*2) by ring]
      by_cases hk2 : k = (1,-1)
      · subst k; norm_num [Z,lp.single_apply,ρ,show -(2*ν*t) = -(ν*t*2) by ring]
      simp [Z,lp.single_apply,hk1,hk2]
    have hezn (t : ℝ) (ht : 0 ≤ t) : ‖ez t‖ ≤ 3*|β-β₂| := by
      dsimp [ez]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-2*ν*t)*‖Z‖ ≤ 1*‖Z‖ := mul_le_mul_of_nonneg_right
          (Real.exp_le_one_iff.mpr (by nlinarith)) (norm_nonneg _)
        _ = _ := by rw [one_mul,hZn]
    let diff : C(Icc (0:ℝ) τ,H) :=
      ⟨fun t => u t-v t,continuousOn_iff_continuous_domRestrict.mp ((hxe U).continuousOn.sub hv)⟩
    have hdb (t : ℝ) (ht : t ∈ Icc 0 τ) : ‖u t-v t‖ ≤ ‖diff‖ := diff.norm_coe_le_norm ⟨t,ht⟩
    obtain ⟨DU,DV,_,_,_,_,_,_,hDU,hDV,hd⟩ :=
      hDifference ν τ hν hτ u u v v (hxe U).continuousOn (hxe U).continuousOn hv hv
        R R R R ‖diff‖ ‖diff‖ hR.le hR.le hR.le hR.le
        (norm_nonneg _) (norm_nonneg _)
        (fun t _ => (hxen U t).trans U.2) (fun t _ => (hxen U t).trans U.2)
        hvb hvb hdb hdb
    have heq (t : ℝ) (ht : t ∈ Icc 0 τ) : u t-v t = ez t-(DU t-DV t) := by
      apply lp.ext
      funext k
      change u t k-v t k = ez t k-(DU t k-DV t k)
      rw [humild t ht k,hm t ht k,hezk,hDU t ht k,hDV t ht k]
      change _ = Real.exp (-ν*t*ρ k) • (X0 k-X₂ k)-_
      rw [smul_sub]
      abel
    have hdn : ‖diff‖ ≤ 3*|β-β₂|+(1/2:ℝ)*‖diff‖ := by
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro t
      change ‖u t-v t‖ ≤ _
      rw [heq t t.2]
      apply (norm_sub_le _ _).trans
      have hh := hd t t.2
      have hs : ‖DU t-DV t‖ ≤ (1/2:ℝ)*‖diff‖ := calc
        ‖DU t-DV t‖ ≤ 32*(‖diff‖*R+R*‖diff‖)*Real.sqrt (t.1/ν) := hh
        _ ≤ 32*(‖diff‖*R+R*‖diff‖)*Real.sqrt (τ/ν) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
            (div_le_div_of_nonneg_right t.2.2 hν.le)) (by positivity)
        _ = _ := by rw [htime]; field_simp; ring
      exact add_le_add (hezn t t.2.1) hs
    intro t ht
    have hh : ‖diff‖ ≤ 6*|β-β₂| := by linarith
    exact (hdb t ht).trans hh
  refine ⟨u, (hxe U).continuousOn, ?_, ?_, ?_, ?_, ?_, ?_, du, hxe (D U U), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu 0 (by simp [hτ.le]), hueq ⟨0,by simp [hτ.le]⟩, he0, hDzero]
    simp
  · intro t ht
    rw [hu t ht]
    exact (U.val.norm_coe_le_norm _).trans U.2
  · intro t ht
    rw [hu t ht]
    exact (U.val ⟨t,ht⟩).2
  · exact hUnique
  · exact hStability
  · exact hphysical
  · rw [hdu 0 (by simp [hτ.le]), hDzero]
    rfl
  · intro t ht
    rw [hdu t ht]
    exact ((D U U).norm_coe_le_norm _).trans (hDR U U.2)
  · intro t ht k
    rw [hu t ht, hdu t ht, hueq ⟨t,ht⟩]
    change E t k - (D U U ⟨t,ht⟩ : H) k = _
    rw [hEk]
  · intro t ht k
    rw [hdu t ht]
    exact hDcoeff U U ⟨t,ht⟩ k

  · intro w dec aa N
    have hweight (k : K) : weight k = 1+ρ k := by dsimp [weight, ρ]; ring
    have hu0 : u 0 = X0 := by
      rw [hu 0 (by simp [hτ.le]), hueq ⟨0,by simp [hτ.le]⟩, he0, hDzero]
      simp
    obtain ⟨q, hqc, _, hqk, hqs, _, _, _, _, _, _, _, _, _⟩ :=
      hTensor ν τ hν hτ u u (hxe U).continuousOn (hxe U).continuousOn
        R R hR.le hR.le
        (fun t _ => (hxen U t).trans U.2) (fun t _ => (hxen U t).trans U.2)
    let RL (k : K) : TV →ₗ[ℂ] V :=
      { toFun := row k
        map_add' := by
          intro z z'
          ext i
          change (∑ j : Fin 2, κ k j * (z (i,j)+z' (i,j))) =
            (∑ j : Fin 2, κ k j*z (i,j)) + ∑ j : Fin 2, κ k j*z' (i,j)
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r z
          ext i
          change (∑ j : Fin 2, κ k j * (r*z (i,j))) = r*∑ j : Fin 2, κ k j*z (i,j)
          simp [Finset.mul_sum, mul_left_comm]
          ring }
    let TL (k : K) : TV →ₗ[ℂ] V :=
      { toFun := fun z => WithLp.toLp 2 (fun i : Fin 2 => ∑ j : Fin 2, κ k j*z (j,i))
        map_add' := by
          intro z z'
          ext i
          change (∑ j : Fin 2, κ k j * (z (j,i)+z' (j,i))) =
            (∑ j : Fin 2, κ k j*z (j,i)) + ∑ j : Fin 2, κ k j*z' (j,i)
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r z
          ext i
          change (∑ j : Fin 2, κ k j * (r*z (j,i))) = r*∑ j : Fin 2, κ k j*z (j,i)
          simp [Finset.mul_sum, mul_left_comm]
          ring }
    let rc (k : K) : TV →L[ℂ] V := (RL k).toContinuousLinearMap
    let tc (k : K) : TV →L[ℂ] V := (TL k).toContinuousLinearMap
    have hsum (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        Summable (fun p : K => outer (aa t p) (aa t (k-p))) := by
      simpa only [aa, ← hweight] using (hqs t ht k).2.1
    have hconvcoord (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) (i j : Fin 2) :
        convolution (aa t) (aa t) k (i,j) = ∑' p : K, aa t p i * aa t (k-p) j :=
      (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 × Fin 2 => ℂ) (i,j)).map_tsum (hsum t ht k)
    have hconvSym (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) (i j : Fin 2) :
        convolution (aa t) (aa t) k (i,j) = convolution (aa t) (aa t) k (j,i) := by
      rw [hconvcoord t ht k i j, hconvcoord t ht k j i]
      let e : K ≃ K :=
        { toFun := fun p => k-p
          invFun := fun p => k-p
          left_inv := by intro p; exact sub_sub_cancel k p
          right_inv := by intro p; exact sub_sub_cancel k p }
      calc
        (∑' p : K, aa t p i * aa t (k-p) j) =
            ∑' p : K, aa t (k-p) i * aa t (k-(k-p)) j := (e.tsum_eq _).symm
        _ = _ := by simp only [sub_sub_cancel]; apply tsum_congr; intro p; ring
    have hNrow (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        N (aa t) (aa t) k = Complex.I • P k (row k (convolution (aa t) (aa t) k)) := by
      have he (p : K) : tc k (outer (aa t p) (aa t (k-p))) =
          (∑ j : Fin 2, κ k j*aa t p j) • aa t (k-p) := by
        ext i
        change (∑ j : Fin 2, κ k j*(aa t p j*aa t (k-p) i)) =
          (∑ j : Fin 2, κ k j*aa t p j) * aa t (k-p) i
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      have hs : tc k (convolution (aa t) (aa t) k) =
          ∑' p : K, (∑ j : Fin 2, κ k j*aa t p j) • aa t (k-p) := by
        change tc k (∑' p : K, outer (aa t p) (aa t (k-p))) = _
        rw [(tc k).map_tsum (hsum t ht k)]
        exact tsum_congr he
      have hr : tc k (convolution (aa t) (aa t) k) =
          row k (convolution (aa t) (aa t) k) := by
        ext i
        change (∑ j : Fin 2, κ k j*convolution (aa t) (aa t) k (j,i)) =
          ∑ j : Fin 2, κ k j*convolution (aa t) (aa t) k (i,j)
        apply Finset.sum_congr rfl
        intro j hj
        rw [hconvSym t ht k j i]
      change Complex.I • P k (∑' p : K, (∑ j : Fin 2, κ k j*aa t p j) • aa t (k-p)) = _
      rw [← hs, hr]
    have hqRow (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        row k (q t k) = weight k • row k (convolution (aa t) (aa t) k) := by
      rw [hqk t ht k]
      simp only [aa, ← hweight]
      let z : TV := convolution (fun l => (weight l)⁻¹ • u t l)
        (fun l => (weight l)⁻¹ • u t l) k
      change row k (weight k • z) = weight k • row k z
      ext i
      change (∑ j : Fin 2, κ k j*((weight k:ℂ)*z (i,j))) =
        (weight k:ℂ)*∑ j : Fin 2, κ k j*z (i,j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hNq (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        (weight k)⁻¹ • (Complex.I • P k (row k (q t k))) = N (aa t) (aa t) k := by
      rw [hqRow t ht k, (P k).map_smul_of_tower,
        smul_comm Complex.I (weight k), inv_smul_smul₀ (hw k).ne']
      exact (hNrow t ht k).symm
    let qe : ℝ → lp (fun _ : K => TV) 2 := fun s => q (projIcc 0 τ hτ.le s)
    have hqec : Continuous qe :=
      (continuousOn_iff_continuous_domRestrict.mp hqc).comp continuous_projIcc
    have hqeEq (s : ℝ) (hs : s ∈ Icc 0 τ) : qe s = q s := by
      dsimp [qe]
      rw [projIcc_of_mem _ hs]
    let g (t : ℝ) (k : K) (s : ℝ) : V := Real.exp (-ν*(t-s)*ρ k) •
      ((weight k)⁻¹ • (Complex.I • P k (row k (qe s k))))
    have hgc (t : ℝ) (k : K) : Continuous (g t k) :=
      (Real.continuous_exp.comp (by fun_prop)).smul
        ((continuous_const : Continuous (fun _ : ℝ => (weight k)⁻¹)).smul
          ((continuous_const : Continuous (fun _ : ℝ => (Complex.I:ℂ))).smul
            ((P k).continuous.comp ((rc k).continuous.comp
              ((lp.evalCLM ℝ (fun _ : K => TV) 2 k).continuous.comp hqec)))))
    have hmild (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        IntervalIntegrable (fun s => Real.exp (-ν*(t-s)*ρ k) • N (aa s) (aa s) k)
          volume 0 t ∧
        aa t k = Real.exp (-ν*t*ρ k) • aa 0 k -
          ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) • N (aa s) (aa s) k := by
      have hsτ (s : ℝ) (hs : s ∈ uIcc (0:ℝ) t) : s ∈ Icc 0 τ := by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      have hnorm (s : ℝ) (hs : s ∈ uIcc (0:ℝ) t) :
          g t k s = Real.exp (-ν*(t-s)*ρ k) • N (aa s) (aa s) k := by
        dsimp [g]
        rw [hqeEq s (hsτ s hs), hNq s (hsτ s hs) k]
      refine ⟨?_, ?_⟩
      · apply ((hgc t k).intervalIntegrable 0 t).congr
        intro s hs
        exact hnorm s (uIoc_subset_uIcc hs)
      · have hDdec : (1+ρ k)⁻¹ • du t k =
            ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) • N (aa s) (aa s) k := by
          rw [hdu t ht, hDcoeff U U ⟨t,ht⟩ k, ← intervalIntegral.integral_smul]
          apply intervalIntegral.integral_congr
          intro s hs
          have hs' := hsτ s hs
          change (1+ρ k)⁻¹ • (Real.exp (-ν*(t-s)*ρ k) •
            (Complex.I • P k (row k (weight k • convolution
              (fun l => (weight l)⁻¹ • u s l) (fun l => (weight l)⁻¹ • u s l) k)))) = _
          rw [← hqk s hs' k, ← hweight, smul_comm ((weight k)⁻¹), hNq s hs' k]
        have huk : u t k = Real.exp (-ν*t*ρ k) • X0 k - du t k := by
          rw [hu t ht, hdu t ht, hueq ⟨t,ht⟩]
          change E t k - (D U U ⟨t,ht⟩ : H) k = _
          rw [hEk]
        change (1+ρ k)⁻¹ • u t k =
          Real.exp (-ν*t*ρ k) • ((1+ρ k)⁻¹ • u 0 k) - _
        rw [huk, smul_sub, smul_comm ((1+ρ k)⁻¹), hu0, hDdec]
    have HG :
    ∃ (U : ℕ → ℝ → H) (L : ℕ → H →L[ℝ] H)
      (B : ℕ → H →L[ℝ] H →L[ℝ] H),
      (∀ m t, t ∈ Icc 0 τ → ∀ k, U m t k = w m k • aa t k) ∧
      (∀ m, ContinuousOn (U m) (Icc 0 τ)) ∧
      (∀ m z k, L m z k = w m k • ((-ν*ρ k) • dec (m+2) z k)) ∧
      (∀ m z z' k, B m z z' k = w m k • N (dec (m+2) z) (dec (m+2) z') k) ∧
      (∀ m t, t ∈ Icc 0 τ → HasDerivWithinAt (U m)
        (L m (U (m+2) t) - B m (U (m+2) t) (U (m+2) t)) (Icc 0 τ) t) := by
      apply D5.S3.FluidDynamics.Fourier.MildPathRegularity.all_grade_regularity_of_mild_path
        ν τ hν hτ u (hxe U).continuousOn
      · intro t ht
        have hs := (U.val ⟨t,ht⟩).2
        rw [← hu t ht] at hs
        refine ⟨?_, ?_, ?_⟩
        · change (1+ρ (0:K))⁻¹ • u t 0 = 0
          rw [hs.1, smul_zero]
        · intro k i
          change (((1+ρ (-k))⁻¹:ℝ):ℂ) * u t (-k) i =
            star ((((1+ρ k)⁻¹:ℝ):ℂ)*u t k i)
          rw [hρneg, hs.2.1]
          simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
          ring
        · intro k
          have hi := Submodule.mem_orthogonal_singleton_iff_inner_right.mp
            (Submodule.starProjection_eq_self_iff.mp (hs.2.2 k))
          have hi' : ∑ j : Fin 2, κ k j*u t k j = 0 := by
            simpa [V, PiLp.inner_apply, κ, mul_comm] using hi
          change (∑ j : Fin 2, κ k j*((((1+ρ k)⁻¹:ℝ):ℂ)*u t k j)) = 0
          simp only [mul_left_comm, ← Finset.mul_sum, hi', mul_zero]
      · intro m
        apply summable_of_ne_finset_zero (s := {(1,0),(-1,0),(-1,1),(1,-1)})
        intro k hk
        have hk' : k ≠ (1,0) ∧ k ≠ (-1,0) ∧ k ≠ (-1,1) ∧ k ≠ (1,-1) := by
          simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
        simp only [hu0, hX0, if_neg (not_or.mpr ⟨hk'.1,hk'.2.1⟩),
          if_neg (not_or.mpr ⟨hk'.2.2.1,hk'.2.2.2⟩), add_zero, smul_zero, norm_zero, zero_pow]
        norm_num
      · exact hmild
    obtain ⟨UU,LL,BB,hUk,hUc,hLk,hBk,hDer⟩ := HG
    have hTime (n m : ℕ) : ContDiffOn ℝ n (UU m) (Icc 0 τ) := by
      induction n generalizing m with
      | zero => exact contDiffOn_zero.mpr (hUc m)
      | succ n ih =>
        rw [show ((n+1:ℕ):WithTop ℕ∞) = (n:WithTop ℕ∞)+1 by simp]
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
          (uniqueDiffOn_Icc hτ)).mpr
        refine ⟨by simp, fun t => ContinuousLinearMap.toSpanSingleton ℝ
          (LL m (UU (m+2) t)-BB m (UU (m+2) t) (UU (m+2) t)), ?_, ?_⟩
        · have hc : ContDiffOn ℝ n (fun t =>
              LL m (UU (m+2) t)-BB m (UU (m+2) t) (UU (m+2) t)) (Icc 0 τ) :=
            ((LL m).contDiff.comp_contDiffOn (ih (m+2))).sub
              (((BB m).contDiff.comp_contDiffOn (ih (m+2))).clm_apply (ih (m+2)))
          exact (ContinuousLinearMap.toSpanSingletonCLE :
            H ≃L[ℝ] (ℝ →L[ℝ] H)).contDiff.comp_contDiffOn hc
        · intro t ht
          exact (hDer m t ht).hasFDerivWithinAt
    have hJoint (n : ℕ) : ContDiffOn ℝ n
        (fun z : ℝ × (Fin 2 → ℝ) => WithLp.toLp 2 (fun i : Fin 2 =>
          (∑' k : K, Complex.exp (Complex.I *
            ((k.1:ℝ)*z.2 0+(k.2:ℝ)*z.2 1)) • aa z.1 k) i |>.re))
        (Icc 0 τ ×ˢ (Set.univ : Set (Fin 2 → ℝ))) := by
      have hc : ContDiffOn ℝ n
          (fun z : ℝ × (Fin 2 → ℝ) => ∑' k : K,
            Complex.exp (Complex.I * ((k.1:ℝ)*z.2 0+(k.2:ℝ)*z.2 1)) • aa z.1 k)
          (Icc 0 τ ×ˢ (Set.univ : Set (Fin 2 → ℝ))) := by
        have hmap : ContDiffOn ℝ n
            (fun z : ℝ × (Fin 2 → ℝ) => (UU (n+2) z.1,z.2))
            (Icc 0 τ ×ˢ (Set.univ : Set (Fin 2 → ℝ))) :=
          ((hTime n (n+2)).comp contDiffOn_fst (prod_subset_preimage_fst _ _)).prodMk contDiffOn_snd
        have hs := (D5.S3.FluidDynamics.Fourier.JointFourierSynthesis.joint_contdiff_fourier_synthesis n).comp_contDiffOn hmap
        apply hs.congr
        intro z hz
        apply tsum_congr
        intro k
        change Complex.exp (Complex.I * ((k.1:ℝ)*z.2 0+(k.2:ℝ)*z.2 1)) • aa z.1 k =
          Complex.exp (Complex.I * ((k.1:ℝ)*z.2 0+(k.2:ℝ)*z.2 1)) •
            ((w (n+2) k)⁻¹ • UU (n+2) z.1 k)
        rw [hUk (n+2) z.1 hz.1 k]
        rw [inv_smul_smul₀ (by dsimp [w]; positivity : w (n+2) k ≠ 0)]
      apply PiLp.contDiff_toLp.comp_contDiffOn
      apply contDiffOn_pi.mpr
      intro i
      exact Complex.reCLM.contDiff.comp_contDiffOn
        (((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 => ℂ) i).restrictScalars ℝ).contDiff.comp_contDiffOn hc)
    let f : ℤ → ℝ := fun n => 1 / (1 + 2 * (n : ℝ) ^ 2)
    have hfpos (n : ℤ) : 0 ≤ f n := by dsimp [f]; positivity
    have hstep (n : ℕ) : f (n + 1) ≤ 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
      dsimp [f]
      push_cast
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      field_simp
      nlinarith
    have hpartial (N : ℕ) :
        ∑ n ∈ Finset.range N, f (n + 1) ≤ 1 - 1 / ((N : ℝ) + 1) := by
      induction N with
      | zero => norm_num
      | succ N ih =>
        rw [Finset.sum_range_succ]
        have hs := hstep N
        push_cast
        have hn : (N : ℝ) + 1 + 1 = (N : ℝ) + 2 := by ring
        rw [hn]
        linarith only [ih, hs]
    have hnat : Summable (fun n : ℕ => f (n + 1)) :=
      summable_of_sum_range_le (fun n => hfpos _) (fun N =>
        (hpartial N).trans (sub_le_self _ (by positivity)))
    have hnatle : (∑' n : ℕ, f (n + 1)) ≤ 1 :=
      hnat.tsum_le_of_sum_range_le (fun N =>
        (hpartial N).trans (sub_le_self _ (by positivity)))
    have hnatzero : Summable (fun n : ℕ => f n) := by
      apply (summable_nat_add_iff 1).mp
      simpa only [Nat.cast_add, Nat.cast_one] using hnat
    have hneg : Summable (fun n : ℕ => f (-(n + 1))) := by
      simpa only [f, Int.cast_neg, even_two, Even.neg_pow] using hnat
    have hf : Summable f := hnatzero.of_nat_of_neg_add_one hneg
    have hfle : (∑' n : ℤ, f n) ≤ 3 := by
      rw [tsum_of_nat_of_neg_add_one hnatzero hneg]
      have hz : 1 + (∑' n : ℕ, f (n + 1)) = ∑' n : ℕ, f n := by
        simpa only [Finset.sum_range_one, show f 0 = 1 by norm_num [f],
          Nat.cast_add, Nat.cast_one, Nat.cast_zero] using hnatzero.sum_add_tsum_nat_add 1
      have heven (n : ℤ) : f (-n) = f n := by simp [f]
      simp only [heven]
      linarith
    have hff := hf.mul_of_nonneg hf hfpos hfpos
    have hffle : (∑' k : ℤ × ℤ, f k.1 * f k.2) ≤ 9 := by
      rw [← hf.tsum_mul_tsum hf hff]
      have h0 : 0 ≤ ∑' n : ℤ, f n := tsum_nonneg hfpos
      nlinarith
    have hInverseMajorant (k : ℤ × ℤ) : (weight k ^ 2)⁻¹ ≤ f k.1 * f k.2 := by
      have hden : (1 + 2 * (k.1 : ℝ) ^ 2) * (1 + 2 * (k.2 : ℝ) ^ 2) ≤
          weight k ^ 2 := by
        dsimp [weight]
        nlinarith [sq_nonneg ((k.1 : ℝ) ^ 2 - (k.2 : ℝ) ^ 2)]
      dsimp [f]
      rw [one_div_mul_one_div, one_div]
      exact inv_anti₀ (by positivity) hden
    have hws : Summable (fun k : ℤ × ℤ => (weight k ^ 2)⁻¹) :=
      hff.of_nonneg_of_le (fun _ => by positivity) hInverseMajorant
    have hwle : (∑' k : ℤ × ℤ, (weight k ^ 2)⁻¹) ≤ 9 :=
      (hws.tsum_le_tsum hInverseMajorant hff).trans hffle
    have hL1 (z : H) : Summable (fun k => ‖(weight k)⁻¹ • z k‖) ∧
        (∑' k : K, ‖(weight k)⁻¹ • z k‖) ≤ 3*‖z‖ := by
      have hi : Summable (fun k : K => ((weight k)⁻¹)^2) := by
        simpa only [inv_pow] using hws
      have hz : Summable (fun k : K => ‖z k‖^2) := by
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
          (lp.hasSum_norm (by norm_num : 0 < (2:ℝ≥0∞).toReal) z).summable
      obtain ⟨hs,hb⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
        Real.HolderConjugate.two_two (fun k => (inv_pos.mpr (hw k)).le)
        (fun k => norm_nonneg (z k))
        (by simpa only [Real.rpow_two] using hi)
        (by simpa only [Real.rpow_two] using hz)
      have he (k : K) : ‖(weight k)⁻¹ • z k‖ = (weight k)⁻¹*‖z k‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hw k))]
      refine ⟨hs.congr (fun k => (he k).symm), ?_⟩
      simp only [← he,Real.rpow_two,← Real.sqrt_eq_rpow] at hb
      have hzn : Real.sqrt (∑' k : K, ‖z k‖^2) = ‖z‖ := by
        have hh : ‖z‖^2 = ∑' k : K, ‖z k‖^2 := by
          simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
            lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) z
        rw [← hh,Real.sqrt_sq (norm_nonneg _)]
      rw [hzn] at hb
      have hiv : Real.sqrt (∑' k : K, ((weight k)⁻¹)^2) ≤ 3 := by
        apply Real.sqrt_le_iff.mpr
        refine ⟨by norm_num, ?_⟩
        simpa only [inv_pow,show (3:ℝ)^2 = 9 by norm_num] using hwle
      exact hb.trans (mul_le_mul_of_nonneg_right hiv (norm_nonneg _))
    let chr (k : K) (x : Fin 2 → ℝ) : ℂ :=
      Complex.exp (Complex.I*((k.1:ℝ)*x 0+(k.2:ℝ)*x 1))
    have hchr (k : K) (x : Fin 2 → ℝ) : ‖chr k x‖ = 1 := by
      dsimp [chr]
      rw [mul_comm]
      convert Complex.norm_exp_ofReal_mul_I ((k.1:ℝ)*x 0+(k.2:ℝ)*x 1) using 1 <;> push_cast <;> rfl
    have hPhys (t : ℝ) (ht : t ∈ Icc 0 τ) (x : Fin 2 → ℝ) :
        Summable (fun k : K => ‖chr k x • aa t k‖) ∧
        ‖WithLp.toLp 2 (fun i : Fin 2 => (∑' k : K, chr k x • aa t k) i |>.re)‖ ≤ 4*R := by
      have hls : Summable (fun k : K => ‖aa t k‖) := by
        simpa only [aa,← hweight] using (hL1 (u t)).1
      have hn (k : K) : ‖chr k x • aa t k‖ = ‖aa t k‖ := by rw [norm_smul,hchr,one_mul]
      have hs : Summable (fun k : K => ‖chr k x • aa t k‖) := hls.congr (fun k => (hn k).symm)
      refine ⟨hs, ?_⟩
      let z : V := ∑' k : K, chr k x • aa t k
      have hr : ‖WithLp.toLp 2 (fun i : Fin 2 => (z i).re)‖ ≤ ‖z‖ := by
        apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg (z i).re)
          (Complex.abs_re_le_norm (z i)) 2
      have hz : ‖z‖ ≤ ∑' k : K, ‖aa t k‖ := by
        have hh := norm_tsum_le_tsum_norm hs
        simpa only [z,hn] using hh
      have hb : (∑' k : K, ‖aa t k‖) ≤ 3*‖u t‖ := by
        simpa only [aa,← hweight] using (hL1 (u t)).2
      exact hr.trans (hz.trans (hb.trans (by nlinarith [(hxen U t).trans U.2])))
    exact ⟨UU,LL,BB,hUk,hUc,hLk,hBk,hDer,fun m n => hTime n m,hJoint,hPhys⟩

set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
#check @prepared_mild_solution
#print axioms prepared_mild_solution

end D5.S3.FluidDynamics.Fourier.ActualPreparedSolution
