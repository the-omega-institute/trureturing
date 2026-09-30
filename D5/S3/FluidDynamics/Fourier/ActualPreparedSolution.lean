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
  intro K V TV H ρ κ P R τ a b X0
  let G := lp (fun _ : K => TV) 2
  have hw (k : K) : 0 < weight k := by unfold weight; positivity
  let d : H → K → V := fun z k => (weight k)⁻¹ • z k
  have he (z : H) (k : K) : weight k ^ 2 * ‖d z k‖ ^ 2 = ‖z k‖ ^ 2 := by
    simp only [d, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [(hw k).ne']
  have hs (z : H) : Summable (fun k : K => weight k ^ 2 * ‖d z k‖ ^ 2) := by
    simp_rw [he]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) z).summable
  have hlpnorm (F : Type) [NormedAddCommGroup F] (z : lp (fun _ : K => F) 2) :
      ‖z‖ = Real.sqrt (∑' k : K, ‖z k‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow] using
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal) z
  have hp (z w : H) := weighted_tensor_convolution (d z) (d w) (hs z) (hs w)
  let Q (z w : H) : G := ⟨fun k => weight k • convolution (d z) (d w) k,
    memℓp_gen (by simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      ENNReal.toReal_ofNat, Real.rpow_two] using (hp z w).2.1)⟩
  have hQn (z w : H) : ‖Q z w‖ ≤ 16 * ‖z‖ * ‖w‖ := by
    rw [hlpnorm TV]
    change Real.sqrt (∑' k : K, ‖weight k • convolution (d z) (d w) k‖^2) ≤ _
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hb := (hp z w).2.2
    change Real.sqrt (∑' k : K, weight k ^ 2 * ‖convolution (d z) (d w) k‖ ^ 2) ≤
      16 * Real.sqrt (∑' k : K, weight k ^ 2 * ‖d z k‖ ^ 2) *
        Real.sqrt (∑' k : K, weight k ^ 2 * ‖d w k‖ ^ 2) at hb
    simpa only [he, ← hlpnorm V z, ← hlpnorm V w] using hb
  let O : V →ₗ[ℝ] V →ₗ[ℝ] TV := LinearMap.mk₂ ℝ outer
    (by intro x y z; ext ij; exact add_mul _ _ _)
    (by intro r x y; ext ij; change ((r:ℂ)*x ij.1)*y ij.2 = (r:ℂ)*(x ij.1*y ij.2); ring)
    (by intro x y z; ext ij; exact mul_add _ _ _)
    (by intro r x y; ext ij; change x ij.1*((r:ℂ)*y ij.2) = (r:ℂ)*(x ij.1*y ij.2); ring)
  let dl (k : K) : H →ₗ[ℝ] V := (weight k)⁻¹ • (lp.evalCLM ℝ (fun _ : K => V) 2 k).toLinearMap
  let QL : H →ₗ[ℝ] H →ₗ[ℝ] G := LinearMap.mk₂ ℝ Q
    (by
      intro x y z; apply lp.ext; funext k
      change weight k • (∑' p, O (dl p (x+y)) (dl (k-p) z)) =
        weight k • (∑' p, outer (d x p) (d z (k-p))) +
          weight k • (∑' p, outer (d y p) (d z (k-p)))
      simp_rw [map_add]
      change weight k • (∑' p : K, (outer (d x p) (d z (k-p)) + outer (d y p) (d z (k-p)))) = _
      rw [Summable.tsum_add ((hp x z).1 k).of_norm ((hp y z).1 k).of_norm, smul_add])
    (by
      intro r x y; apply lp.ext; funext k
      change weight k • (∑' p, O (dl p (r • x)) (dl (k-p) y)) =
        r • (weight k • (∑' p, outer (d x p) (d y (k-p))))
      simp only [map_smul, LinearMap.smul_apply, tsum_const_smul'', smul_comm (weight k) r]
      rfl)
    (by
      intro x y z; apply lp.ext; funext k
      change weight k • (∑' p, O (dl p x) (dl (k-p) (y+z))) =
        weight k • (∑' p, outer (d x p) (d y (k-p))) +
          weight k • (∑' p, outer (d x p) (d z (k-p)))
      simp_rw [map_add]
      change weight k • (∑' p : K, (outer (d x p) (d y (k-p)) + outer (d x p) (d z (k-p)))) = _
      rw [Summable.tsum_add ((hp x y).1 k).of_norm ((hp x z).1 k).of_norm, smul_add])
    (by
      intro r x y; apply lp.ext; funext k
      change weight k • (∑' p, O (dl p x) (dl (k-p) (r • y))) =
        r • (weight k • (∑' p, outer (d x p) (d y (k-p))))
      simp only [map_smul, LinearMap.smul_apply, tsum_const_smul'', smul_comm (weight k) r]
      rfl)
  let QB : H →L[ℝ] H →L[ℝ] G := QL.mkContinuous₂ 16 hQn
  have hQdiff (x y z w : H) : QB x y - QB z w = QB (x-z) y + QB z (y-w) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    rw [sub_add_sub_cancel]
  let rc (k : K) : TV →L[ℂ] V :=
    (((WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ)).symm.toLinearMap.comp
      (LinearMap.pi fun i => ∑ j : Fin 2, κ k j •
        PiLp.projₗ 2 (fun _ : Fin 2 × Fin 2 => ℂ) (i,j))).toContinuousLinearMap).copy
      (fun z => WithLp.toLp 2 (fun i => ∑ j : Fin 2, κ k j*z (i,j))) (by
        funext z; ext i
        simp [LinearMap.pi_apply, LinearMap.sum_apply, PiLp.projₗ, WithLp.linearEquiv_apply]
        rfl)
  let row (k : K) : TV → V := rc k
  let clamp (T : ℝ) (hT : 0 < T) (q : C(Icc (0:ℝ) T,G)) : ℝ → G :=
    fun s => q (projIcc 0 T hT.le s)
  let rowKernel (q : ℝ → G) (t : ℝ) (k : K) (s : ℝ) : V :=
    Real.exp (-ν*(t-s)*ρ k) • (Complex.I • P k (row k (q s k)))
  have hrowKernelc (q : ℝ → G) (hc : Continuous q) (t : ℝ) (k : K) : Continuous (rowKernel q t k) :=
    (Real.continuous_exp.comp (by fun_prop)).smul
      ((continuous_const : Continuous (fun _ : ℝ => (Complex.I:ℂ))).smul
        ((P k).continuous.comp ((rc k).continuous.comp
        ((lp.evalCLM ℝ (fun _ : K => TV) 2 k).continuous.comp hc))))
  have hBexists (T : ℝ) (hT : 0 < T) (q : C(Icc (0:ℝ) T,G)) :=
    D5.S3.FluidDynamics.Fourier.BochnerRowHeatPath.bochner_row_heat_path ν T hν hT
      (clamp T hT q) (q.continuous.comp continuous_projIcc) ‖q‖ (norm_nonneg _)
      (fun s => q.norm_coe_le_norm _)
  let BC (T : ℝ) (hT : 0 < T) (q : C(Icc (0:ℝ) T,G)) := (hBexists T hT q).choose
  have hBC (T : ℝ) (hT : 0 < T) (q : C(Icc (0:ℝ) T,G)) := (hBexists T hT q).choose_spec
  have hBCk (T : ℝ) (hT : 0 < T) (q : C(Icc (0:ℝ) T,G)) (t : ℝ)
      (ht : t ∈ Icc 0 T) (k : K) : BC T hT q t k = ∫ s in (0:ℝ)..t, rowKernel (clamp T hT q) t k s :=
    (hBC T hT q).2.2.2 t ht k
  have hBCsub (T : ℝ) (hT : 0 < T) (q r : C(Icc (0:ℝ) T,G)) (t : ℝ)
      (ht : t ∈ Icc 0 T) : BC T hT q t - BC T hT r t = BC T hT (q-r) t := by
    apply lp.ext; funext k
    rw [lp.coeFn_sub, Pi.sub_apply, hBCk T hT q t ht k, hBCk T hT r t ht k,
      hBCk T hT (q-r) t ht k, ← intervalIntegral.integral_sub
        ((hrowKernelc (clamp T hT q) (q.continuous.comp continuous_projIcc) t k).intervalIntegrable 0 t)
        ((hrowKernelc (clamp T hT r) (r.continuous.comp continuous_projIcc) t k).intervalIntegrable 0 t)]
    apply intervalIntegral.integral_congr; intro s hs
    simp [rowKernel, clamp, row, ← smul_sub, ← map_sub]
  let qp (T : ℝ) (x y : ℝ → H) (hx : ContinuousOn x (Icc 0 T))
      (hy : ContinuousOn y (Icc 0 T)) : C(Icc (0:ℝ) T,G) :=
    ⟨fun t => QB (x t) (y t), continuousOn_iff_continuous_domRestrict.mp
      ((QB.continuous.comp_continuousOn hx).clm_apply hy)⟩
  let dp (T : ℝ) (hT : 0 < T) (x y : ℝ → H) (hx : ContinuousOn x (Icc 0 T))
      (hy : ContinuousOn y (Icc 0 T)) := BC T hT (qp T x y hx hy)
  have hdpk (T : ℝ) (hT : 0 < T) (x y : ℝ → H) (hx hy) (t : ℝ)
      (ht : t ∈ Icc 0 T) (k : K) :
      dp T hT x y hx hy t k = ∫ s in (0:ℝ)..t, rowKernel (fun s => Q (x s) (y s)) t k s := by
    rw [hBCk T hT (qp T x y hx hy) t ht k]
    apply intervalIntegral.integral_congr; intro s hs
    have hs' : s ∈ Icc 0 T := by
      rw [uIcc_of_le ht.1] at hs; exact ⟨hs.1, hs.2.trans ht.2⟩
    simp only [rowKernel, clamp, projIcc_of_mem _ hs', qp]
    rfl
  have hdpn (T : ℝ) (hT : 0 < T) (x y : ℝ → H) (hx hy) (Mx My : ℝ)
      (hMx : 0 ≤ Mx) (hMy : 0 ≤ My)
      (hxb : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ Mx) (hyb : ∀ t ∈ Icc 0 T, ‖y t‖ ≤ My)
      (t : ℝ) (ht : t ∈ Icc 0 T) : ‖dp T hT x y hx hy t‖ ≤ 32*Mx*My*Real.sqrt (t/ν) := by
    have hq : ‖qp T x y hx hy‖ ≤ 16*Mx*My :=
      (ContinuousMap.norm_le _ (by positivity)).mpr (fun s =>
        (hQn _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (hxb s s.2) (by norm_num)) (hyb s s.2)
          (norm_nonneg _) (by positivity)))
    exact ((hBC T hT _).2.2.1 t ht).trans (by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ) ≤ 2))
        (Real.sqrt_nonneg (t/ν))
      convert hh using 1 <;> ring)
  have hdpdiff (T : ℝ) (hT : 0 < T) (x y : ℝ → H) (hx hy)
      (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
      (hxb : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ M) (hyb : ∀ t ∈ Icc 0 T, ‖y t‖ ≤ M)
      (hd : ∀ t ∈ Icc 0 T, ‖x t-y t‖ ≤ C) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖dp T hT x x hx hx t-dp T hT y y hy hy t‖ ≤
        32*(C*M+M*C)*Real.sqrt (t/ν) := by
    rw [show dp T hT x x hx hx t-dp T hT y y hy hy t =
      BC T hT (qp T x x hx hx-qp T y y hy hy) t from hBCsub T hT _ _ t ht]
    have hq : ‖qp T x x hx hx-qp T y y hy hy‖ ≤ 16*(C*M+M*C) := by
      apply (ContinuousMap.norm_le _ (by positivity)).mpr; intro s
      change ‖QB (x s) (x s)-QB (y s) (y s)‖ ≤ _
      rw [hQdiff]
      calc
        _ ≤ 16*‖x s-y s‖*‖x s‖+16*‖y s‖*‖x s-y s‖ :=
          (norm_add_le _ _).trans (add_le_add (hQn _ _) (hQn _ _))
        _ ≤ 16*C*M+16*M*C := by gcongr <;> first | exact hd s s.2 | exact hxb s s.2 | exact hyb s s.2
        _ = _ := by ring
    exact ((hBC T hT _).2.2.1 t ht).trans (by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ) ≤ 2))
        (Real.sqrt_nonneg (t/ν))
      convert hh using 1 <;> ring)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hτ : 0 < τ := div_pos hν (by positivity)
  have hshort (M C t : ℝ) (hM : 0 < M) (hC : 0 ≤ C)
      (ht : t ≤ ν/(16384*M^2)) :
      32*(C*M+M*C)*Real.sqrt (t/ν) ≤ (1/2:ℝ)*C := by
    have hs : Real.sqrt ((ν/(16384*M^2))/ν) = 1/(128*M) := by
      rw [show (ν/(16384*M^2))/ν = (1/(128*M))^2 by
        field_simp [hν.ne', hM.ne']; ring]
      exact Real.sqrt_sq (by positivity)
    calc
      _ ≤ 32*(C*M+M*C)*Real.sqrt ((ν/(16384*M^2))/ν) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
          (div_le_div_of_nonneg_right ht hν.le)) (by positivity)
      _ = _ := by rw [hs]; field_simp; ring
  let kernel (x : ℝ → H) := rowKernel (fun s => Q (x s) (x s))
  have hkernelc (x : ℝ → H) (hx : Continuous x) (t : ℝ) (k : K) :=
    hrowKernelc (fun s => Q (x s) (x s)) ((QB.continuous.comp hx).clm_apply hx) t k
  have hUnrestricted (x y : ℝ → H) (hx : Continuous x) (hy : Continuous y)
      (hm : ∀ t ∈ Icc 0 τ, ∀ k,
        x t k - y t k = (∫ s in (0:ℝ)..t, kernel y t k s) -
          ∫ s in (0:ℝ)..t, kernel x t k s) :
      ∀ t ∈ Icc 0 τ, x t = y t := by
    obtain ⟨tx,htx,hmaxx⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hτ.le) hx.continuousOn.norm
    obtain ⟨ty,hty,hmaxy⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hτ.le) hy.continuousOn.norm
    let M : ℝ := ‖x tx‖ + ‖y ty‖ + 1
    have hM : 0 < M := by dsimp [M]; positivity
    have hxb (s : ℝ) (hs : s ∈ Icc 0 τ) : ‖x s‖ ≤ M := by
      have hh : ‖x s‖ ≤ ‖x tx‖ := hmaxx hs
      dsimp [M]; linarith [norm_nonneg (y ty)]
    have hyb (s : ℝ) (hs : s ∈ Icc 0 τ) : ‖y s‖ ≤ M := by
      have hh : ‖y s‖ ≤ ‖y ty‖ := hmaxy hs
      dsimp [M]; linarith [norm_nonneg (x tx)]
    have hmF (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        x t k - y t k = ∫ s in (0:ℝ)..t, kernel y t k s - kernel x t k s := by
      rw [intervalIntegral.integral_sub
        ((hkernelc y hy t k).intervalIntegrable 0 t)
        ((hkernelc x hx t k).intervalIntegrable 0 t), hm t ht k]
    let δ : ℝ := ν/(16384*M^2)
    have hδ : 0 < δ := div_pos hν (by positivity)
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
      have hxx : Continuous xx := hx.comp (continuous_const.add continuous_id)
      have hyy : Continuous yy := hy.comp (continuous_const.add continuous_id)
      let diff : C(Icc (0:ℝ) T,H) :=
        ⟨fun s => xx s - yy s,
          continuousOn_iff_continuous_domRestrict.mp (hxx.sub hyy).continuousOn⟩
      have hd (s : ℝ) (hs : s ∈ Icc 0 T) : ‖xx s - yy s‖ ≤ ‖diff‖ :=
        diff.norm_coe_le_norm ⟨s,hs⟩
      let DX := dp T hT xx xx hxx.continuousOn hxx.continuousOn
      let DY := dp T hT yy yy hyy.continuousOn hyy.continuousOn
      have hDX := hdpk T hT xx xx hxx.continuousOn hxx.continuousOn
      have hDY := hdpk T hT yy yy hyy.continuousOn hyy.continuousOn
      have hdb := hdpdiff T hT xx yy hxx.continuousOn hyy.continuousOn
        M ‖diff‖ hM.le (norm_nonneg _)
        (fun s hs => hxb _ (hsτ s hs)) (fun s hs => hyb _ (hsτ s hs)) hd
      have hlocal (r : ℝ) (hr : r ∈ Icc 0 T) : xx r - yy r = DY r - DX r := by
        apply lp.ext
        funext k
        change x (a+r) k - y (a+r) k = DY r k - DX r k
        rw [hmF (a+r) (hsτ r hr) k, hDX r hr k, hDY r hr k]
        let F : ℝ → V := fun s => kernel y (a+r) k s - kernel x (a+r) k s
        have hFc : Continuous F := (hkernelc y hy _ _).sub (hkernelc x hx _ _)
        have hp : (∫ s in (0:ℝ)..a, F s) = 0 := by
          rw [← intervalIntegral.integral_zero (a := (0:ℝ)) (b := a) (E := V)]
          apply intervalIntegral.integral_congr
          intro s hs
          have hsa : s ∈ Icc 0 a := by simpa [uIcc_of_le ha] using hs
          dsimp [F, kernel, rowKernel]
          rw [hpast s hsa, sub_self]
        change (∫ s in (0:ℝ)..(a+r), F s) = _
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hFc.intervalIntegrable 0 a) (hFc.intervalIntegrable a (a+r)),hp,zero_add]
        have hshift := intervalIntegral.integral_comp_add_left (a := 0) (b := r) F a
        simp only [add_zero] at hshift
        rw [← hshift]
        rw [← intervalIntegral.integral_sub
          ((hkernelc yy hyy r k).intervalIntegrable 0 r)
          ((hkernelc xx hxx r k).intervalIntegrable 0 r)]
        apply intervalIntegral.integral_congr; intro s hs
        dsimp [F, kernel, rowKernel, xx, yy]
        rw [show a+r-(a+s) = r-s by ring]
      have hdn : ‖diff‖ ≤ (1/2:ℝ)*‖diff‖ := by
        apply (ContinuousMap.norm_le _ (by positivity)).mpr
        intro r
        change ‖xx r - yy r‖ ≤ _
        rw [hlocal r r.2, norm_sub_rev]
        exact (hdb r r.2).trans (hshort M ‖diff‖ r hM (norm_nonneg _)
          (r.2.2.trans hTδ))
      have hz : diff = 0 := norm_eq_zero.mp (by linarith [norm_nonneg diff])
      intro t ht
      have hr : t-a ∈ Icc 0 T := by dsimp [T]; constructor <;> linarith [ht.1,ht.2]
      have he := congrArg (fun z : C(Icc (0:ℝ) T,H) => z ⟨t-a,hr⟩) hz
      change x (a+(t-a))-y (a+(t-a)) = 0 at he
      simpa only [add_sub_cancel, sub_eq_zero] using he
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
    have hcover : τ ≤ (n:ℝ)*δ := ((div_lt_iff₀ hδ).mp hn).le
    intro t ht
    exact hblocks n t ⟨ht.1,by simpa [min_eq_left hcover] using ht.2⟩
  have hρ (k : K) : 0 ≤ ρ k := by dsimp [ρ]; positivity
  have hρneg (k : K) : ρ (-k) = ρ k := by
    change ((-k.1:ℤ):ℝ)^2 + ((-k.2:ℤ):ℝ)^2 = _
    simp [ρ]
  have hwneg (k : K) : weight (-k) = weight k := by
    change 1 + ((-k.1:ℤ):ℝ)^2 + ((-k.2:ℤ):ℝ)^2 = _
    simp [weight]
  have hκneg (k : K) : κ (-k) = -κ k := by
    ext i
    fin_cases i
    · change ((-k.1:ℤ):ℂ) = -(k.1:ℂ); simp
    · change ((-k.2:ℤ):ℂ) = -(k.2:ℂ); simp
  have hκstar (k : K) (i : Fin 2) : star (κ k i) = κ k i := by
    fin_cases i <;> simp [κ]
  have hκnorm (k : K) : ‖κ k‖^2 = ρ k := by
    simp [V, EuclideanSpace.norm_sq_eq, κ, ρ, Complex.norm_intCast,
      sq_abs, Fin.sum_univ_two]
  let CV : V →L[ℝ] V :=
    (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 2 => Complex.conjLIE)).toContinuousLinearEquiv
  have hCV (z : V) (i : Fin 2) : CV z i = star (z i) := rfl
  have hPformula (k : K) (z : V) (i : Fin 2) :
      P k z i = z i - ((∑ j : Fin 2, κ k j * z j) / (ρ k : ℂ)) * κ k i := by
    simp [P, Submodule.starProjection_orthogonal, Submodule.starProjection_singleton,
      hκnorm, V, PiLp.inner_apply, κ, mul_comm]
  have hPeven (k : K) : P (-k) = P k := by
    have he : ℂ ∙ (-κ k) = ℂ ∙ κ k := by
      simpa only [Set.neg_singleton] using (Submodule.span_neg (R := ℂ) {κ k})
    simp only [P, hκneg, he]
  have hPstar (k : K) (z : V) : P k (CV z) = CV (P k z) := by
    ext i
    rw [hCV (P k z) i, hPformula, hPformula]
    simp only [hCV, star_sub, star_mul, star_div₀, star_sum,
      hκstar, Complex.star_def, Complex.conj_ofReal, mul_comm]
  let ev (k : K) := lp.evalCLM ℝ (fun _ : K => V) 2 k
  let SJ : Submodule ℝ H := (ev 0).ker ⊓
    ((⨅ k : K, (ev (-k)).eqLocus (CV.comp (ev k))) ⊓
      ⨅ k : K, (((P k).restrictScalars ℝ).comp (ev k)).eqLocus (ev k))
  let S : Submodule ℝ H := SJ.copy
    {z | z 0 = 0 ∧ (∀ k i, z (-k) i = star (z k i)) ∧ ∀ k, P k (z k) = z k} (by
      ext z
      change (z 0 = 0 ∧ (∀ k i, z (-k) i = star (z k i)) ∧
        ∀ k, P k (z k) = z k) ↔ z ∈ SJ
      simp only [SJ, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.mem_eqLocus, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars, ev]
      change _ ↔ z 0 = 0 ∧ (∀ k, z (-k) = CV (z k)) ∧ ∀ k, P k (z k) = z k
      constructor
      · rintro ⟨hz,hs,hp⟩
        exact ⟨hz, fun k => by ext i; exact hs k i, hp⟩
      · rintro ⟨hz,hs,hp⟩
        exact ⟨hz, fun k i => congrArg (fun v : V => v i) (hs k), hp⟩)
  have hdstar (z : H) (hz : z ∈ S) (k : K) (i : Fin 2) :
      d z (-k) i = star (d z k i) := by
    change (((weight (-k))⁻¹:ℝ):ℂ) * z (-k) i =
      star ((((weight k)⁻¹:ℝ):ℂ) * z k i)
    rw [hwneg, hz.2.1]
    simp [mul_comm]
  have hSclosed : IsClosed (S : Set H) := by
    rw [show S = SJ from Submodule.copy_eq _ _ _]
    simp only [SJ, Submodule.coe_inf, Submodule.coe_iInf]
    exact (ev 0).isClosed_ker.inter ((isClosed_iInter fun k =>
      (ev (-k)).isClosed_eqLocus (CV.comp (ev k))).inter (isClosed_iInter fun k =>
        (((P k).restrictScalars ℝ).comp (ev k)).isClosed_eqLocus (ev k)))
  letI : CompleteSpace S := hSclosed.completeSpace_coe
  let Path := C(Icc (0:ℝ) τ, S)
  let xe (x : Path) (t : ℝ) : H := x (projIcc 0 τ hτ.le t)
  have hxe (x : Path) : Continuous (xe x) :=
    (continuous_subtype_val.comp x.continuous).comp continuous_projIcc
  have hxen (x : Path) (t : ℝ) : ‖xe x t‖ ≤ ‖x‖ :=
    x.norm_coe_le_norm _
  let DP (x y : Path) := dp τ hτ (xe x) (xe y) (hxe x).continuousOn (hxe y).continuousOn
  have hDPc (x y : Path) :=
    (hBC τ hτ (qp τ (xe x) (xe y) (hxe x).continuousOn (hxe y).continuousOn)).1
  have hDPk (x y : Path) := hdpk τ hτ (xe x) (xe y) (hxe x).continuousOn (hxe y).continuousOn
  have hDPmem (x y : Path) : ∀ t ∈ Icc 0 τ, DP x y t ∈ S := by
    let q : ℝ → G := fun s => QB (xe x s) (xe y s)
    have hqc : Continuous q := (QB.continuous.comp (hxe x)).clm_apply (hxe y)
    have hqk (t : ℝ) (k : K) :
        q t k = weight k • convolution (d (xe x t)) (d (xe y t)) k := rfl
    have hqs (t : ℝ) (k : K) := (hp (xe x t) (xe y t)).1 k
    let CT : TV →L[ℝ] TV :=
      (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 2 × Fin 2 => Complex.conjLIE)).toContinuousLinearEquiv
    have hqstar (t : ℝ) (k : K) : q t (-k) = CT (q t k) := by
      rw [hqk, hqk, hwneg, CT.map_smul]
      congr 1
      change (∑' p : K, outer (d (xe x t) p) (d (xe y t) (-k-p))) =
        CT (∑' p : K, outer (d (xe x t) p) (d (xe y t) (k-p)))
      rw [CT.map_tsum (hqs t k).of_norm, ← tsum_comp_neg]
      apply tsum_congr; intro p
      ext ij
      change d (xe x t) (-p) ij.1 * d (xe y t) (-k- -p) ij.2 =
        star (d (xe x t) p ij.1 * d (xe y t) (k-p) ij.2)
      rw [show -k- -p = -(k-p) by abel,
        hdstar (xe x t) (x (projIcc 0 τ hτ.le t)).2 p ij.1,
        hdstar (xe y t) (y (projIcc 0 τ hτ.le t)).2 (k-p) ij.2, star_mul]
      exact mul_comm _ _
    have hqStar (s : ℝ) (k : K) (i j : Fin 2) :
        q s (-k) (i,j) = star (q s k (i,j)) :=
      congrArg (fun z : TV => z (i,j)) (hqstar s k)
    have hrowStar (s : ℝ) (k : K) : row (-k) (q s (-k)) = -CV (row k (q s k)) := by
      ext i
      change (∑ j : Fin 2, κ (-k) j * q s (-k) (i,j)) =
        -star (∑ j : Fin 2, κ k j * q s k (i,j))
      rw [hκneg]
      change (∑ j : Fin 2, -κ k j * q s (-k) (i,j)) = _
      simp only [hqStar, star_sum, star_mul, hκstar, neg_mul, Finset.sum_neg_distrib]
      simp [mul_comm]
    have hfstar (t s : ℝ) (k : K) : rowKernel q t (-k) s = CV (rowKernel q t k s) := by
      dsimp [rowKernel]
      rw [hρneg, hPeven, hrowStar, map_neg, hPstar]
      ext i
      change (Real.exp (-ν*(t-s)*ρ k):ℂ) * (Complex.I * (-star (P k (row k (q s k)) i))) =
        star ((Real.exp (-ν*(t-s)*ρ k):ℂ) * (Complex.I * P k (row k (q s k)) i))
      simp only [Complex.star_def, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
      ring
    have hDq (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        DP x y t k = ∫ s in (0:ℝ)..t, rowKernel q t k s := hDPk x y t ht k
    have hDstar (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) : DP x y t (-k) = CV (DP x y t k) := by
      rw [hDq t ht (-k), hDq t ht k,
        ← CV.intervalIntegral_comp_comm ((hrowKernelc q hqc t k).intervalIntegrable 0 t)]
      apply intervalIntegral.integral_congr
      intro s hs
      exact hfstar t s k
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · rw [hDq t ht 0]
      have hz (s : ℝ) : row 0 (q s 0) = 0 := by
        ext i
        simp [row, rc, κ]
      simp only [rowKernel, hz, map_zero, smul_zero, intervalIntegral.integral_zero]
    · intro k i; rw [hDstar t ht k, hCV]
    · intro k
      rw [hDq t ht k, ← (P k).intervalIntegral_comp_comm ((hrowKernelc q hqc t k).intervalIntegrable 0 t)]
      apply intervalIntegral.integral_congr; intro s hs
      simp only [rowKernel, (P k).map_smul_of_tower]
      rw [Submodule.starProjection_eq_self_iff.mpr
        ((ℂ ∙ κ k)ᗮ.starProjection_apply_mem _)]
  let D (x y : Path) : Path := ⟨fun t => ⟨DP x y t,hDPmem x y t t.2⟩,
    ((hDPc x y).comp continuous_subtype_val).subtype_mk _⟩
  have hDzero (x y : Path) : D x y ⟨0, by simp [hτ.le]⟩ = 0 :=
    Subtype.ext (hBC τ hτ (qp τ (xe x) (xe y) (hxe x).continuousOn (hxe y).continuousOn)).2.1
  have hDcoeff (x y : Path) (t : Icc (0:ℝ) τ) (k : K) :
      (D x y t : H) k = ∫ s in (0:ℝ)..t.1,
        rowKernel (fun s => Q (xe x s) (xe y s)) t.1 k s := hDPk x y t t.2 k
  let A0 : H := lp.single 2 (1,0) a + lp.single 2 (-1,0) a
  let B0 : H := lp.single 2 (-1,1) b + lp.single 2 (1,-1) b
  have hPairS (k : K) (z : V) (hk : k ≠ 0)
      (hz : ∀ i, star (z i) = z i) (hpz : P k z = z) :
      lp.single 2 k z + lp.single 2 (-k) z ∈ S := by
    refine ⟨by simp [lp.single_apply, hk, neg_ne_zero.mpr hk], ?_, ?_⟩
    · intro l i
      change ((Pi.single k z : K → V) (-l)) i + ((Pi.single (-k) z : K → V) (-l)) i =
        star (((Pi.single k z : K → V) l) i + ((Pi.single (-k) z : K → V) l) i)
      have hn₁ : (-l = k) ↔ (l = -k) := neg_eq_iff_eq_neg
      have hn₂ : (-l = -k) ↔ (l = k) := neg_inj
      simp only [Pi.single_apply, hn₁, hn₂, star_add]
      by_cases h₁ : l = k <;> by_cases h₂ : l = -k <;>
        simp only [h₁, h₂, ite_true, ite_false, WithLp.ofLp_zero, Pi.zero_apply, star_zero, hz, add_zero, zero_add]
      all_goals split_ifs <;> simp only [hz, WithLp.ofLp_zero, Pi.zero_apply, star_zero, add_zero, zero_add]
    · intro l
      change P l ((Pi.single k z : K → V) l + (Pi.single (-k) z : K → V) l) =
        (Pi.single k z : K → V) l + (Pi.single (-k) z : K → V) l
      simp only [Pi.single_apply]
      split_ifs <;> subst_vars <;> simp only [map_add, map_zero, hpz, hPeven]
  have hA0S : A0 ∈ S := hPairS (1,0) a (by decide)
    (by intro i; fin_cases i <;> simp [a]) (by
      apply Submodule.starProjection_eq_self_iff.mpr
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      norm_num [a, κ, V, PiLp.inner_apply])
  have hB0S : B0 ∈ S := hPairS (-1,1) b (by decide)
    (by intro i; fin_cases i <;> simp [b]) (by
      apply Submodule.starProjection_eq_self_iff.mpr
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      norm_num [b, κ, V, PiLp.inner_apply])
  let initial (c e : ℝ) : H :=
    lp.single 2 (1,0) (WithLp.toLp 2 ![0,(c:ℂ)]) +
    lp.single 2 (-1,0) (WithLp.toLp 2 ![0,(c:ℂ)]) +
    lp.single 2 (-1,1) (WithLp.toLp 2 ![(3*e/2:ℂ),(3*e/2:ℂ)]) +
    lp.single 2 (1,-1) (WithLp.toLp 2 ![(3*e/2:ℂ),(3*e/2:ℂ)])
  have hInitialSupport (c e : ℝ) (k : K)
      (hk : k ∉ ({(1,0),(-1,0),(-1,1),(1,-1)} : Finset K)) : initial c e k = 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [initial, lp.single_apply, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2]
  have hInitialNorm (c e : ℝ) : ‖initial c e‖^2 = 2*c^2+9*e^2 := by
    rw [show ‖initial c e‖^2 = ∑' k : K, ‖initial c e k‖^2 from by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) (initial c e),
      tsum_eq_sum (s := {(1,0),(-1,0),(-1,1),(1,-1)})]
    · norm_num [initial, lp.single_apply, V, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      nlinarith [sq_abs e]
    · intro k hk; rw [hInitialSupport c e k hk]; norm_num
  have hX0bound : ‖X0‖ ≤ R/2 := by
    have hr2 : R^2 = 4*(2*A^2 + 9*B^2) := by
      dsimp [R]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have ha2 : α^2 ≤ A^2 := by nlinarith [sq_abs α, abs_nonneg α]
    have hb2 : β^2 ≤ B^2 := by nlinarith [sq_abs β, abs_nonneg β]
    nlinarith [norm_nonneg X0, hInitialNorm α β]
  let E : ℝ → H := fun t => Real.exp (-ν*t) • A0 + Real.exp (-2*ν*t) • B0
  have hEc : Continuous E := by dsimp [E]; fun_prop
  have hEk (t : ℝ) (k : K) : E t k = Real.exp (-ν*t*ρ k) • X0 k := by
    change Real.exp (-ν*t) • ((Pi.single (1,0) a : K → V) k + (Pi.single (-1,0) a : K → V) k) +
      Real.exp (-2*ν*t) • ((Pi.single (-1,1) b : K → V) k + (Pi.single (1,-1) b : K → V) k) =
      Real.exp (-ν*t*ρ k) • ((Pi.single (1,0) a : K → V) k + (Pi.single (-1,0) a : K → V) k +
        (Pi.single (-1,1) b : K → V) k + (Pi.single (1,-1) b : K → V) k)
    simp only [Pi.single_apply]
    split_ifs <;> subst_vars <;>
      norm_num [K, ρ, Prod.mk.injEq, show -(2*ν*t) = -(ν*t*2) by ring] at *
  have hES (t : ℝ) : E t ∈ S :=
    S.add_mem (S.smul_mem _ hA0S) (S.smul_mem _ hB0S)
  have hEn (t : ℝ) (ht : 0 ≤ t) : ‖E t‖ ≤ ‖X0‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro k
    rw [hEk, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr
      (by have hp := mul_nonneg (mul_nonneg hν.le ht) (hρ k); nlinarith))
      (norm_nonneg (X0 k))).trans_eq (one_mul _)
  let e : Path := ⟨fun t => ⟨E t, hES t⟩,
    (hEc.comp continuous_subtype_val).subtype_mk _⟩
  have hen : ‖e‖ ≤ R/2 := (ContinuousMap.norm_le _ (by positivity)).mpr
    (fun t => (hEn t.1 t.2.1).trans hX0bound)
  have he0 : (e ⟨0, by simp [hτ.le]⟩ : H) = X0 := by
    change E 0 = X0
    simp [E, A0, B0, X0, add_assoc]
  have hDhalf (x y : Path) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
      ‖D x x - D y y‖ ≤ (1/2:ℝ)*‖x-y‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr; intro t
    change ‖DP x x t - DP y y t‖ ≤ _
    exact (hdpdiff τ hτ (xe x) (xe y) (hxe x).continuousOn (hxe y).continuousOn
      R ‖x-y‖ hR.le (norm_nonneg _)
      (fun s _ => (hxen x s).trans hx) (fun s _ => (hxen y s).trans hy)
      (fun s _ => (x-y).norm_coe_le_norm _) t t.2).trans
        (hshort R ‖x-y‖ t hR (norm_nonneg _) t.2.2)
  have hDR (x : Path) (hx : ‖x‖ ≤ R) : ‖D x x‖ ≤ R/4 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr; intro t
    have hb := hdpn τ hτ (xe x) (xe x) (hxe x).continuousOn (hxe x).continuousOn
      R R hR.le hR.le (fun s _ => (hxen x s).trans hx)
      (fun s _ => (hxen x s).trans hx) t t.2
    have hh := hshort R (R/2) t hR (by positivity) t.2.2
    change ‖DP x x t‖ ≤ R/4
    nlinarith
  let Φ (x : Path) : Path := e - D x x
  have hΦR (x : Path) (hx : ‖x‖ ≤ R) : ‖Φ x‖ ≤ 3*R/4 :=
    (norm_sub_le _ _).trans (by linarith [hen, hDR x hx])
  have hΦlip (x y : Path) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
      ‖Φ x - Φ y‖ ≤ (1/2:ℝ)*‖x-y‖ := by
    have heq : Φ x - Φ y = -(D x x - D y y) := by dsimp [Φ]; rw [sub_sub_sub_cancel_left, neg_sub]
    rw [heq, norm_neg]
    exact hDhalf x y hx hy
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
  have hu (t : ℝ) (ht : t ∈ Icc 0 τ) : u t = (U.val ⟨t,ht⟩ : H) := by
    dsimp [u, xe]; rw [projIcc_of_mem _ ht]
  have hdu (t : ℝ) (ht : t ∈ Icc 0 τ) : du t = (D U U ⟨t,ht⟩ : H) := by
    dsimp [du, xe]; rw [projIcc_of_mem _ ht]
  have humild (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
      u t k = Real.exp (-ν*t*ρ k) • X0 k - ∫ s in (0:ℝ)..t, kernel u t k s := by
    rw [hu t ht,hueq ⟨t,ht⟩]
    change E t k - (D U U ⟨t,ht⟩ : H) k = _
    rw [hEk,hDcoeff]
  have hu0 : u 0 = X0 := by
    rw [hu 0 (by simp [hτ.le]), hueq ⟨0,by simp [hτ.le]⟩, he0, hDzero]
    simp
  refine ⟨u, (hxe U).continuousOn, hu0, ?_, ?_, ?_, ?_, ?_, du, hxe (D U U), ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hu t ht]
    exact (U.val.norm_coe_le_norm _).trans U.2
  · intro t ht
    rw [hu t ht]
    exact (U.val ⟨t,ht⟩).2
  · intro v hv hm
    let vc : C(Icc (0:ℝ) τ,H) :=
      ⟨fun t => v t, continuousOn_iff_continuous_domRestrict.mp hv⟩
    let vv : ℝ → H := fun t => vc (projIcc 0 τ hτ.le t)
    have hvv : Continuous vv := vc.continuous.comp continuous_projIcc
    have he (t : ℝ) (ht : t ∈ Icc 0 τ) : vv t = v t := by
      dsimp [vv]; rw [projIcc_of_mem _ ht]; rfl
    have hh := hUnrestricted u vv (hxe U) hvv (by
      intro t ht k
      rw [he t ht, humild t ht k,hm t ht k]
      have hi : (∫ s in (0:ℝ)..t, kernel vv t k s) = ∫ s in (0:ℝ)..t, kernel v t k s := by
        apply intervalIntegral.integral_congr; intro s hs
        dsimp [kernel, rowKernel]
        rw [he s (by rw [uIcc_of_le ht.1] at hs; exact ⟨hs.1,hs.2.trans ht.2⟩)]
      rw [hi]; exact sub_sub_sub_cancel_left _ _ _)
    exact fun t ht => he t ht ▸ (hh t ht).symm
  · intro β₂ v hv hvb b₂ X₂ hm
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
      have hh := hInitialNorm 0 (β-β₂)
      simpa only [initial, Z, bd, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_div, Complex.ofReal_zero, lp.single_zero, add_zero, zero_add,
        show WithLp.toLp 2 ![(0:ℂ),0] = (0:V) by ext i; fin_cases i <;> rfl,
        zero_pow (by norm_num : 2 ≠ 0), mul_zero, sq_abs, mul_pow,
        show (3:ℝ)^2 = 9 by norm_num] using hh
    let ez (t : ℝ) : H := Real.exp (-2*ν*t) • Z
    have hezk (t : ℝ) (k : K) : ez t k = Real.exp (-ν*t*ρ k) • (X0-X₂) k := by
      rw [hinit]
      change Real.exp (-2*ν*t) • Z k = Real.exp (-ν*t*ρ k) • Z k
      change Real.exp (-2*ν*t) • ((Pi.single (-1,1) bd : K → V) k + (Pi.single (1,-1) bd : K → V) k) =
        Real.exp (-ν*t*ρ k) • ((Pi.single (-1,1) bd : K → V) k + (Pi.single (1,-1) bd : K → V) k)
      simp only [Pi.single_apply]
      split_ifs <;> subst_vars <;>
        norm_num [ρ, show -(2*ν*t) = -(ν*t*2) by ring]
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
    let DU := dp τ hτ u u (hxe U).continuousOn (hxe U).continuousOn
    let DV := dp τ hτ v v hv hv
    have hDU := hdpk τ hτ u u (hxe U).continuousOn (hxe U).continuousOn
    have hDV := hdpk τ hτ v v hv hv
    have hd := hdpdiff τ hτ u v (hxe U).continuousOn hv
      R ‖diff‖ hR.le (norm_nonneg _) (fun t _ => (hxen U t).trans U.2) hvb hdb
    have heq (t : ℝ) (ht : t ∈ Icc 0 τ) : u t-v t = ez t-(DU t-DV t) := by
      apply lp.ext
      funext k
      change u t k-v t k = ez t k-(DU t k-DV t k)
      rw [humild t ht k,hm t ht k,hezk,hDU t ht k,hDV t ht k]
      change _ = Real.exp (-ν*t*ρ k) • (X0 k-X₂ k)-_
      rw [smul_sub]
      change _ = _ - ((∫ s in (0:ℝ)..t, kernel u t k s) - ∫ s in (0:ℝ)..t, kernel v t k s)
      exact sub_sub_sub_comm _ _ _ _
    have hdn : ‖diff‖ ≤ 3*|β-β₂|+(1/2:ℝ)*‖diff‖ := by
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro t
      change ‖u t-v t‖ ≤ _
      rw [heq t t.2]
      apply (norm_sub_le _ _).trans
      exact add_le_add (hezn t t.2.1) ((hd t t.2).trans
        (hshort R ‖diff‖ t hR (norm_nonneg _) t.2.2))
    intro t ht
    have hh : ‖diff‖ ≤ 6*|β-β₂| := by linarith
    exact (hdb t ht).trans hh
  · intro x y i
    rw [tsum_eq_sum (s := {(1,0),(-1,0),(-1,1),(1,-1)})]
    · have h := D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.synthesis_eq_realVelocity
        α β x y i.castSucc
      convert h using 1
      simp only [D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.synthesis,
        Fin.sum_univ_four, D5.S3.FluidDynamics.Fourier.LowModeReversalWitness.frequency,
        Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
      fin_cases i <;>
        norm_num [K, X0, lp.single_apply, a, b, weight,
          D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.synthesis,
          D5.S3.FluidDynamics.Fourier.LowModeReversalWitness.inputAmplitude,
          Fin.sum_univ_four, Fin.ext_iff] <;> ring
    · intro k hk
      have hh : X0 k = 0 := hInitialSupport α β k hk
      simp only [hh, WithLp.ofLp_zero, Pi.zero_apply, mul_zero, zero_mul]
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
    let q : ℝ → G := fun t => QB (u t) (u t)
    have hqc : Continuous q := (QB.continuous.comp (hxe U)).clm_apply (hxe U)
    have hsum (t : ℝ) (k : K) : Summable (fun p : K => outer (aa t p) (aa t (k-p))) := by
      simpa only [aa, ← hweight] using (hp (u t) (u t)).1 k |>.of_norm
    have hNrow (t : ℝ) (k : K) :
        N (aa t) (aa t) k = Complex.I • P k (row k (convolution (aa t) (aa t) k)) := by
      change Complex.I • P k _ = Complex.I • P k _
      congr 2
      rw [show row k (convolution (aa t) (aa t) k) =
        ∑' p : K, rc k (outer (aa t p) (aa t (k-p))) from (rc k).map_tsum (hsum t k)]
      rw [← (Equiv.subLeft k).tsum_eq (fun p : K =>
        (∑ j : Fin 2, κ k j*aa t p j) • aa t (k-p))]
      apply tsum_congr; intro p
      ext i
      change (∑ j : Fin 2, κ k j*aa t (k-p) j)*aa t (k-(k-p)) i =
        ∑ j : Fin 2, κ k j*(aa t p i*aa t (k-p) j)
      rw [sub_sub_cancel, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j hj; ring
    have hNq (t : ℝ) (k : K) :
        (weight k)⁻¹ • (Complex.I • P k (row k (q t k))) = N (aa t) (aa t) k := by
      change (weight k)⁻¹ • (Complex.I • P k
        (rc k (weight k • convolution (d (u t)) (d (u t)) k))) = _
      rw [(rc k).map_smul_of_tower, (P k).map_smul_of_tower,
        smul_comm Complex.I (weight k), inv_smul_smul₀ (hw k).ne']
      simpa only [aa, d, ← hweight] using (hNrow t k).symm
    have hNc (k : K) : Continuous (fun s => N (aa s) (aa s) k) := by
      have hc := (continuous_const : Continuous (fun _ : ℝ => (weight k)⁻¹)).smul
        ((continuous_const : Continuous (fun _ : ℝ => (Complex.I:ℂ))).smul
          ((P k).continuous.comp ((rc k).continuous.comp
          ((lp.evalCLM ℝ (fun _ : K => TV) 2 k).continuous.comp hqc))))
      exact hc.congr (fun s => hNq s k)
    have hmild (t : ℝ) (ht : t ∈ Icc 0 τ) (k : K) :
        IntervalIntegrable (fun s => Real.exp (-ν*(t-s)*ρ k) • N (aa s) (aa s) k) volume 0 t ∧
        aa t k = Real.exp (-ν*t*ρ k) • aa 0 k -
          ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) • N (aa s) (aa s) k := by
      refine ⟨((Real.continuous_exp.comp (by fun_prop)).smul (hNc k)).intervalIntegrable 0 t, ?_⟩
      change (1+ρ k)⁻¹ • u t k = Real.exp (-ν*t*ρ k) • ((1+ρ k)⁻¹ • u 0 k) - _
      rw [humild t ht k, smul_sub, smul_comm ((1+ρ k)⁻¹), hu0,
        ← intervalIntegral.integral_smul]
      congr 1
      apply intervalIntegral.integral_congr; intro s hs
      change (1+ρ k)⁻¹ • (Real.exp (-ν*(t-s)*ρ k) • _) = _
      rw [smul_comm ((1+ρ k)⁻¹)]
      rw [← hweight]
      change Real.exp (-ν*(t-s)*ρ k) • ((weight k)⁻¹ • (Complex.I • P k (row k (q s k)))) = _
      rw [hNq]
    have hgeom : ∀ t ∈ Icc 0 τ, aa t 0 = 0 ∧
        (∀ k i, aa t (-k) i = star (aa t k i)) ∧
        ∀ k, (∑ j : Fin 2, κ k j*aa t k j) = 0 := by
      intro t ht
      have hs := (U.val ⟨t,ht⟩).2
      rw [← hu t ht] at hs
      refine ⟨?_, ?_, ?_⟩
      · change (1+ρ (0:K))⁻¹ • u t 0 = 0
        rw [hs.1, smul_zero]
      · intro k i
        simpa only [aa, ← hweight] using hdstar (u t) hs k i
      · intro k
        have hi := Submodule.mem_orthogonal_singleton_iff_inner_right.mp
          (((ℂ ∙ κ k)ᗮ).smul_mem (((1+ρ k)⁻¹:ℝ):ℂ)
            (Submodule.starProjection_eq_self_iff.mp (hs.2.2 k)))
        simpa [V, PiLp.inner_apply, κ, aa, mul_comm] using hi
    have hinitgrade : ∀ m : ℕ,
        Summable (fun k : K => ‖w m k • aa 0 k‖^2) := by
      intro m
      apply summable_of_ne_finset_zero (s := {(1,0),(-1,0),(-1,1),(1,-1)})
      intro k hk
      have hh : X0 k = 0 := hInitialSupport α β k hk
      simp [aa, hu0, hh]
    obtain ⟨UU,LL,BB,hUk,hUc,hLk,hBk,hDer⟩ :=
      D5.S3.FluidDynamics.Fourier.MildPathRegularity.all_grade_regularity_of_mild_path
        ν τ hν hτ u (hxe U).continuousOn hgeom hinitgrade hmild
    have hTime (n m : ℕ) : ContDiffOn ℝ n (UU m) (Icc 0 τ) := by
      induction n generalizing m with
      | zero => exact contDiffOn_zero.mpr (hUc m)
      | succ n ih =>
        rw [show ((n+1:ℕ):WithTop ℕ∞) = (n:WithTop ℕ∞)+1 by simp]
        apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hτ)).mpr
        refine ⟨fun t ht => (hDer m t ht).differentiableWithinAt, by simp, ?_⟩
        apply (((LL m).contDiff.comp_contDiffOn (ih (m+2))).sub
          (((BB m).contDiff.comp_contDiffOn (ih (m+2))).clm_apply (ih (m+2)))).congr
        intro t ht
        exact (hDer m t ht).derivWithin ((uniqueDiffOn_Icc hτ) t ht)
    let RV : V →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      ((LinearMap.piMap (fun _ : Fin 2 => Complex.reCLM.toLinearMap)).withLpMap 2).toContinuousLinearMap
    refine ⟨UU,LL,BB,hUk,hUc,hLk,hBk,hDer,fun m n => hTime n m, ?_, ?_⟩
    · intro n
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
      exact RV.contDiff.comp_contDiffOn hc
    · intro t ht x
      let f : ℤ → ℝ := fun n => 1 / (1 + 2 * (n : ℝ) ^ 2)
      have hfpos (n : ℤ) : 0 ≤ f n := by dsimp [f]; positivity
      have hzeta : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
      have hzsum : (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^2) = Real.pi^2/6 := by
        have hh := hasSum_zeta_two.summable.sum_add_tsum_nat_add 1
        rw [hasSum_zeta_two.tsum_eq] at hh
        simpa using hh
      have hstep (n : ℕ) : f (n+1) ≤ (1/2:ℝ)*(1/((n:ℝ)+1)^2) := by
        dsimp [f]; push_cast
        have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
        field_simp; nlinarith
      have hnat : Summable (fun n : ℕ => f (n+1)) :=
        (hzeta.mul_left (1/2:ℝ)).of_nonneg_of_le (fun n => hfpos _) hstep
      have hnatle : (∑' n : ℕ, f (n+1)) ≤ 1 := by
        have hh := hnat.tsum_le_tsum hstep (hzeta.mul_left (1/2:ℝ))
        rw [tsum_mul_left, hzsum] at hh
        nlinarith [Real.pi_lt_d2, Real.pi_pos]
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
        rw [← hlpnorm V z] at hb
        have hiv : Real.sqrt (∑' k : K, ((weight k)⁻¹)^2) ≤ 3 :=
          Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa only [inv_pow, show (3:ℝ)^2 = 9 by norm_num] using hwle⟩
        exact hb.trans (mul_le_mul_of_nonneg_right hiv (norm_nonneg _))
      let chr (k : K) (x : Fin 2 → ℝ) : ℂ :=
        Complex.exp (Complex.I*((k.1:ℝ)*x 0+(k.2:ℝ)*x 1))
      have hchr (k : K) (x : Fin 2 → ℝ) : ‖chr k x‖ = 1 := by
        dsimp [chr]
        rw [mul_comm]
        convert Complex.norm_exp_ofReal_mul_I ((k.1:ℝ)*x 0+(k.2:ℝ)*x 1) using 1 <;> push_cast <;> rfl
      have hls : Summable (fun k : K => ‖aa t k‖) := by
        simpa only [aa,← hweight] using (hL1 (u t)).1
      have hn (k : K) : ‖chr k x • aa t k‖ = ‖aa t k‖ := by rw [norm_smul,hchr,one_mul]
      have hs : Summable (fun k : K => ‖chr k x • aa t k‖) := hls.congr (fun k => (hn k).symm)
      refine ⟨hs, ?_⟩
      let z : V := ∑' k : K, chr k x • aa t k
      have hr : ‖RV z‖ ≤ ‖z‖ := by
        rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum (fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (RCLike.norm_re_le_norm (z i)) 2)
      have hz : ‖z‖ ≤ ∑' k : K, ‖aa t k‖ := by
        have hh := norm_tsum_le_tsum_norm hs
        simpa only [z,hn] using hh
      have hb : (∑' k : K, ‖aa t k‖) ≤ 3*‖u t‖ := by
        simpa only [aa,← hweight] using (hL1 (u t)).2
      exact hr.trans (hz.trans (hb.trans (by nlinarith [(hxen U t).trans U.2])))

#print axioms prepared_mild_solution

end D5.S3.FluidDynamics.Fourier.ActualPreparedSolution
