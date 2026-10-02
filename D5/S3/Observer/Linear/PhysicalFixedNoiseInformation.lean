/- GID: D5/S3/Observer/Linear/PhysicalFixedNoiseInformation
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/PhysicalFixedNoiseInformation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compute the second-order fixed-noise information expansion of the actual exponential-trajectory Gramian. -/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ContinuousLinearMap Set Filter Asymptotics
open scoped Topology InnerProductSpace

namespace D5.S3.Observer.Linear.PhysicalFixedNoiseInformation

/-- With fixed positive prior precision and coordinate-noise variance, the physical
exponential-trajectory Gramian gives a log determinant whose first term is the
initial sensor trace and whose error is quadratic in time. -/
theorem physical_fixed_noise_information
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →L[ℝ] V) (C : V →L[ℝ] W)
    (β η : ℝ) (hβ : 0 < β) (hη : 0 < η) :
    let H := C.adjoint.comp C
    let G : ℝ → V →L[ℝ] V := fun T =>
      ∫ t in (0 : ℝ)..T, (C.comp (NormedSpace.exp (t • B))).adjoint.comp
        (C.comp (NormedSpace.exp (t • B)))
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ ∀ T : ℝ, 0 < T → T ≤ δ →
      |(1 / 2 : ℝ) * Real.log ((ContinuousLinearMap.id ℝ V +
          (β * η)⁻¹ • G T).det) -
        T / (2 * β * η) * LinearMap.trace ℝ V H.toLinearMap| ≤ K * T ^ 2 := by
  classical
  intro H G
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  have hfirst :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
    ∀ T : ℝ, 0 < T → T ≤ δ →
    ‖(∫ t in (0 : ℝ)..T,
    (C.comp (NormedSpace.exp (t • B))).adjoint.comp
    (C.comp (NormedSpace.exp (t • B)))) -
    T • C.adjoint.comp C‖ ≤ K * T ^ 2 := by
    let A : ℝ → V →L[ℝ] W := fun t => C.comp (NormedSpace.exp (t • B))
    let f : ℝ → V →L[ℝ] V := fun t => (A t).adjoint.comp (A t)
    let adj : (V →L[ℝ] W) →L[ℝ] (W →L[ℝ] V) :=
      { toFun := fun L => L.adjoint
        map_add' := fun L R => ContinuousLinearMap.adjoint.map_add L R
        map_smul' := by intro r L; simp
        cont := ContinuousLinearMap.adjoint.continuous }
    have he (t : ℝ) : DifferentiableAt ℝ
        (fun s : ℝ => NormedSpace.exp (s • B)) t :=
      (NormedSpace.exp_analytic (𝕂 := ℝ) (t • B)).differentiableAt.comp t
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) B).differentiableAt
    have hA (t : ℝ) : DifferentiableAt ℝ A t :=
      (differentiableAt_const (c := C)).clm_comp (he t)
    have hf (t : ℝ) : DifferentiableAt ℝ f t := by
      exact (adj.differentiableAt.comp t
        (hA t)).clm_comp (hA t)
    have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
    have hzero : f 0 = C.adjoint.comp C := by
      ext x
      simp [f, A, NormedSpace.exp_zero, ContinuousLinearMap.adjoint_one]
    obtain ⟨c, hc⟩ := (hf 0).isBigO_sub.bound
    obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp hc
    let K := max c 0
    refine ⟨K, ε / 2, le_max_right _ _, half_pos hε, ?_⟩
    intro T hT hTδ
    have hTi : IntervalIntegrable f volume 0 T := hfc.intervalIntegrable _ _
    have heq :
        (∫ t in (0 : ℝ)..T, f t) - T • C.adjoint.comp C =
          ∫ t in (0 : ℝ)..T, f t - f 0 := by
      rw [intervalIntegral.integral_sub hTi (intervalIntegrable_const)]
      simp [hzero]
    change ‖(∫ t in (0 : ℝ)..T, f t) - T • C.adjoint.comp C‖ ≤ _
    rw [heq]
    have hn : ‖∫ t in (0 : ℝ)..T, f t - f 0‖ ≤ (K * T) * |T - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (by
        intro t ht
        rw [uIoc_of_le hT.le] at ht
        have ht0 : 0 ≤ t := ht.1.le
        have hdist : dist t 0 < ε := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0]
          linarith [ht.2]
        have h := hbound hdist
        simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht0] at h
        calc
          ‖f t - f 0‖ ≤ c * t := h
          _ ≤ K * t := mul_le_mul_of_nonneg_right (le_max_left _ _) ht0
          _ ≤ K * T := mul_le_mul_of_nonneg_left ht.2 (le_max_right _ _))
    simpa only [sub_zero, abs_of_pos hT, pow_two, mul_assoc] using hn
  obtain ⟨R, δ, hR, hδ, herror⟩ := hfirst
  have hlogdet (L : V →L[ℝ] V) (hL : L.toLinearMap.IsPositive)
      (s : ℝ) (hs : 0 ≤ s) :
      |Real.log ((ContinuousLinearMap.id ℝ V + s • L).det) -
        s * LinearMap.trace ℝ V L.toLinearMap| ≤
        (Module.finrank ℝ V : ℝ) / 2 * s ^ 2 * ‖L‖ ^ 2 := by
    classical
    let n := Module.finrank ℝ V
    let w := hL.isSymmetric.eigenvectorBasis rfl
    let ev : Fin n → ℝ := hL.isSymmetric.eigenvalues rfl
    have hev (i : Fin n) : 0 ≤ ev i := hL.nonneg_eigenvalues rfl i
    have hevnorm (i : Fin n) : ev i ≤ ‖L‖ := by
      have hn := L.le_opNorm (w i)
      have he : L (w i) = ev i • w i := hL.isSymmetric.apply_eigenvectorBasis rfl i
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hev i),
        w.norm_eq_one, mul_one, mul_one] at hn
      exact hn
    have hlog (x : ℝ) (hx : 0 ≤ x) :
        |Real.log (1 + x) - x| ≤ x ^ 2 / 2 := by
      have hu : Real.log (1 + x) ≤ x := by
        simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
      have hl := Real.le_log_one_add_of_nonneg hx
      rw [abs_of_nonpos (sub_nonpos.mpr hu)]
      have hd : 0 < x + 2 := by linarith
      have hr : x - 2 * x / (x + 2) = x ^ 2 / (x + 2) := by
        field_simp
        <;> ring
      calc
        -(Real.log (1 + x) - x) ≤ x - 2 * x / (x + 2) := by linarith
        _ = x ^ 2 / (x + 2) := hr
        _ ≤ x ^ 2 / 2 := div_le_div_of_nonneg_left (sq_nonneg x) (by norm_num) (by linarith)
    have hmat :
        LinearMap.toMatrix w.toBasis w.toBasis
          (ContinuousLinearMap.id ℝ V + s • L).toLinearMap =
          Matrix.diagonal (fun i : Fin n => 1 + s * ev i) := by
      change LinearMap.toMatrix w.toBasis w.toBasis
        (LinearMap.id + s • L.toLinearMap) = _
      rw [map_add, map_smul, LinearMap.toMatrix_id]
      have hmL : LinearMap.toMatrix w.toBasis w.toBasis L.toLinearMap =
          Matrix.diagonal ev := by
        simpa [w, ev, Function.comp_def] using
          hL.isSymmetric.toMatrix_eigenvectorBasis rfl
      rw [hmL]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.diagonal_apply]
      · simp [Matrix.diagonal_apply, Matrix.one_apply, hij, Ne.symm hij]
    have hdet :
        (ContinuousLinearMap.id ℝ V + s • L).det =
          ∏ i : Fin n, (1 + s * ev i) := by
      calc
        _ = (LinearMap.toMatrix w.toBasis w.toBasis
            (ContinuousLinearMap.id ℝ V + s • L).toLinearMap).det :=
          (LinearMap.det_toMatrix w.toBasis _).symm
        _ = _ := by rw [hmat, Matrix.det_diagonal]
    have htrace : LinearMap.trace ℝ V L.toLinearMap = ∑ i : Fin n, ev i :=
      hL.isSymmetric.trace_eq_sum_eigenvalues rfl
    have hpos (i : Fin n) : 0 < 1 + s * ev i :=
      add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hs (hev i))
    rw [hdet, Real.log_prod (fun i _ => ne_of_gt (hpos i)), htrace,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc
      |∑ i : Fin n, (Real.log (1 + s * ev i) - s * ev i)| ≤
          ∑ i : Fin n, |Real.log (1 + s * ev i) - s * ev i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, (s * ev i) ^ 2 / 2 :=
        Finset.sum_le_sum (fun i _ => hlog _ (mul_nonneg hs (hev i)))
      _ ≤ ∑ i : Fin n, (s * ‖L‖) ^ 2 / 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact pow_le_pow_left₀ (mul_nonneg hs (hev i))
          (mul_le_mul_of_nonneg_left (hevnorm i) hs) 2
      _ = (n : ℝ) / 2 * s ^ 2 * ‖L‖ ^ 2 := by
        simp [n, Finset.sum_const, mul_pow]
        <;> ring
  let A : ℝ → V →L[ℝ] W := fun t => C.comp (NormedSpace.exp (t • B))
  have hA : Continuous A := by
    have he : Continuous (fun t : ℝ => NormedSpace.exp (t • B)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact ((NormedSpace.exp_analytic (𝕂 := ℝ) (t • B)).differentiableAt.comp t
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) B).differentiableAt).continuousAt
    exact continuous_const.clm_comp he
  have hg : Continuous (fun t : ℝ => (A t).adjoint.comp (A t)) :=
    (ContinuousLinearMap.adjoint.continuous.comp hA).clm_comp hA
  have hi (T : ℝ) (x y : V) :
      ⟪x, (G T) y⟫_ℝ = ∫ t in (0 : ℝ)..T, ⟪x, (A t).adjoint ((A t) y)⟫_ℝ := by
    let F : (V →L[ℝ] V) →L[ℝ] ℝ :=
      (innerSL ℝ x).comp (ContinuousLinearMap.apply ℝ V y)
    exact (F.intervalIntegral_comp_comm (hg.intervalIntegrable _ _)).symm
  have hsym (T : ℝ) : (G T).toLinearMap.IsSymmetric := by
    intro x y
    change ⟪G T x, y⟫_ℝ = ⟪x, G T y⟫_ℝ
    rw [real_inner_comm, hi, hi]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [adjoint_inner_right, real_inner_comm]
  have hpos (T : ℝ) (hT : 0 < T) : (G T).toLinearMap.IsPositive := by
    refine ⟨hsym T, ?_⟩
    intro x
    change 0 ≤ ⟪G T x, x⟫_ℝ
    rw [real_inner_comm, hi]
    simp only [adjoint_inner_right]
    exact intervalIntegral.integral_nonneg hT.le (fun t _ => real_inner_self_nonneg)
  have htraceNorm (L : V →L[ℝ] V) :
      |LinearMap.trace ℝ V L.toLinearMap| ≤ (Module.finrank ℝ V : ℝ) * ‖L‖ := by
    let w := stdOrthonormalBasis ℝ V
    rw [LinearMap.trace_eq_sum_inner L.toLinearMap w]
    calc
      |∑ i, ⟪w i, L (w i)⟫_ℝ| ≤ ∑ i, |⟪w i, L (w i)⟫_ℝ| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ‖L‖ := by
        apply Finset.sum_le_sum
        intro i _
        calc
          |⟪w i, L (w i)⟫_ℝ| ≤ ‖w i‖ * ‖L (w i)‖ := by
            simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (w i) (L (w i))
          _ ≤ ‖w i‖ * (‖L‖ * ‖w i‖) :=
            mul_le_mul_of_nonneg_left (L.le_opNorm _) (norm_nonneg _)
          _ = ‖L‖ := by rw [w.norm_eq_one]; ring
      _ = _ := by simp
  let s := (β * η)⁻¹
  let n : ℝ := Module.finrank ℝ V
  let F := R + ‖H‖
  let K := n / 4 * s ^ 2 * F ^ 2 + s / 2 * n * R
  have hs : 0 < s := inv_pos.mpr (mul_pos hβ hη)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hF : 0 ≤ F := add_nonneg hR (norm_nonneg _)
  refine ⟨K, min δ 1, by dsimp [K]; positivity, lt_min hδ (by norm_num), ?_⟩
  intro T hT hTδ
  have hTd : T ≤ δ := hTδ.trans (min_le_left _ _)
  have hT1 : T ≤ 1 := hTδ.trans (min_le_right _ _)
  have herr : ‖G T - T • H‖ ≤ R * T ^ 2 := herror T hT hTd
  have hnorm : ‖G T‖ ≤ F * T := by
    calc
      ‖G T‖ = ‖(G T - T • H) + T • H‖ := by rw [sub_add_cancel]
      _ ≤ ‖G T - T • H‖ + ‖T • H‖ := norm_add_le _ _
      _ ≤ R * T ^ 2 + T * ‖H‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT]
        exact add_le_add herr (le_refl _)
      _ ≤ F * T := by dsimp [F]; nlinarith [mul_nonneg hR (mul_nonneg hT.le (sub_nonneg.mpr hT1))]
  have htrerr :
      |LinearMap.trace ℝ V (G T).toLinearMap -
          T * LinearMap.trace ℝ V H.toLinearMap| ≤ n * R * T ^ 2 := by
    have ht := htraceNorm (G T - T • H)
    simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_smul,
      map_sub, map_smul, smul_eq_mul] at ht
    exact ht.trans (by dsimp [n]; nlinarith [mul_le_mul_of_nonneg_left herr hn])
  have hl := hlogdet (G T) (hpos T hT) s hs.le
  have hnormSq : ‖G T‖ ^ 2 ≤ (F * T) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hl' :
      |Real.log ((ContinuousLinearMap.id ℝ V + s • G T).det) -
          s * LinearMap.trace ℝ V (G T).toLinearMap| ≤
        n / 2 * s ^ 2 * (F * T) ^ 2 :=
    hl.trans (mul_le_mul_of_nonneg_left hnormSq (by positivity))
  have heq :
      (1 / 2 : ℝ) * Real.log ((ContinuousLinearMap.id ℝ V + (β * η)⁻¹ • G T).det) -
        T / (2 * β * η) * LinearMap.trace ℝ V H.toLinearMap =
      (1 / 2 : ℝ) * (Real.log ((ContinuousLinearMap.id ℝ V + s • G T).det) -
          s * LinearMap.trace ℝ V (G T).toLinearMap) +
        s / 2 * (LinearMap.trace ℝ V (G T).toLinearMap -
          T * LinearMap.trace ℝ V H.toLinearMap) := by
    dsimp [s]
    field_simp
    <;> ring
  rw [heq]
  calc
    |(1 / 2 : ℝ) * (Real.log ((ContinuousLinearMap.id ℝ V + s • G T).det) -
        s * LinearMap.trace ℝ V (G T).toLinearMap) +
      s / 2 * (LinearMap.trace ℝ V (G T).toLinearMap -
        T * LinearMap.trace ℝ V H.toLinearMap)| ≤
      (1 / 2 : ℝ) * |Real.log ((ContinuousLinearMap.id ℝ V + s • G T).det) -
        s * LinearMap.trace ℝ V (G T).toLinearMap| +
      s / 2 * |LinearMap.trace ℝ V (G T).toLinearMap -
        T * LinearMap.trace ℝ V H.toLinearMap| := by
      simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num),
        abs_of_nonneg (show 0 ≤ s / 2 by positivity)] using
        (abs_add_le ((1 / 2 : ℝ) *
          (Real.log ((ContinuousLinearMap.id ℝ V + s • G T).det) -
            s * LinearMap.trace ℝ V (G T).toLinearMap))
          (s / 2 * (LinearMap.trace ℝ V (G T).toLinearMap -
            T * LinearMap.trace ℝ V H.toLinearMap)))
    _ ≤ (1 / 2 : ℝ) * (n / 2 * s ^ 2 * (F * T) ^ 2) +
        s / 2 * (n * R * T ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hl' (by norm_num))
        (mul_le_mul_of_nonneg_left htrerr (by positivity))
    _ = K * T ^ 2 := by dsimp [K]; ring

end D5.S3.Observer.Linear.PhysicalFixedNoiseInformation
