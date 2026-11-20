import D5.S3.Quantum.Recovery.LikelihoodRationalTailSeparation
import D5.S3.Quantum.Recovery.QuadraticBayesRiskGeometricPetz
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integrating the likelihood Hessian bound for ordinary Petz recovery

The twice-integrated Hessian identity is used on compact subintervals.
At the singular endpoint, dominated convergence is applied to the truncated
score kernels using the integrable squared scores with weight `(1 - t)^2`.
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open LikelihoodRationalTailSeparation

namespace PetzLikelihoodHessianIntegration

variable {ι : Type*} [Fintype ι]

/-- Quadratic risk given nonnegative weights on ordered pairs. -/
def pairwiseRisk (w : ι → ι → ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (c j - c i) ^ 2 * w i j

private theorem continuousOn_mixtureScore {a : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (mixtureScore a) (Ico 0 1) := by
  unfold mixtureScore
  exact continuousOn_const.div (by fun_prop) fun t ht =>
    (add_pos_of_pos_of_nonneg (sub_pos.mpr ht.2) (mul_nonneg ht.1 ha)).ne'

private theorem integral_hessian (δ velocity hessian : ℝ → ℝ) {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) (hδ₀ : δ 0 = 0) (hv₀ : velocity 0 = 0)
    (hδ : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt δ (velocity t) (Ico 0 1) t)
    (hv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt velocity (hessian t) (Ico 0 1) t)
    (hh : ContinuousOn hessian (Icc 0 u)) :
    (∫ t in (0 : ℝ)..u, (u - t) * hessian t) = δ u := by
  have hsub : Icc 0 u ⊆ Ico (0 : ℝ) 1 := fun _ ht => ⟨ht.1, ht.2.trans_lt hu.2⟩
  have hcδ : ContinuousOn δ (Icc 0 u) :=
    fun t ht => ((hδ t (hsub ht)).mono hsub).continuousWithinAt
  have hcv : ContinuousOn velocity (Icc 0 u) :=
    fun t ht => ((hv t (hsub ht)).mono hsub).continuousWithinAt
  have hvInt : IntervalIntegrable velocity volume 0 u :=
    (uIcc_of_le hu.1 ▸ hcv).intervalIntegrable
  have hhInt : IntervalIntegrable hessian volume 0 u :=
    (uIcc_of_le hu.1 ▸ hh).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu.1 hcδ
    (fun t ht => (hδ t ⟨ht.1.le, ht.2.trans hu.2⟩).hasDerivAt
      (mem_of_superset (Ioo_mem_nhds ht.1 (ht.2.trans hu.2)) Ioo_subset_Ico_self)) hvInt
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (u := fun t : ℝ => u - t) (u' := fun _ => (-1 : ℝ))
    (v := velocity) (v' := hessian)
    (fun t _ => ((hasDerivAt_id t).const_sub u).hasDerivWithinAt)
    (fun t ht => (hv t (hsub (uIcc_of_le hu.1 ▸ ht))).mono (uIcc_of_le hu.1 ▸ hsub))
    (by simp) hhInt
  simpa only [sub_self, zero_mul, mul_zero, hv₀, zero_sub, neg_one_mul,
    intervalIntegral.integral_neg, hFTC, hδ₀, sub_zero, neg_neg] using hIBP

/-- Integrating the sampled Hessian bound gives square-root separation at the
endpoint for every finite nonnegative likelihood vector and pair weight.
The two derivatives on `[0, 1)` are interpreted within that interval. -/
theorem pairwiseRisk_sqrt_le_of_hessian
    (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (δ velocity hessian : ℝ → ℝ) (hδ₁ : ContinuousAt δ 1)
    (hδ₀ : δ 0 = 0) (hv₀ : velocity 0 = 0)
    (hδ : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt δ (velocity t) (Ico 0 1) t)
    (hv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt velocity (hessian t) (Ico 0 1) t)
    (hh : ∀ u ∈ Ico (0 : ℝ) 1, ContinuousOn hessian (Icc 0 u))
    (hSample : ∀ t ∈ Ico (0 : ℝ) 1,
      (2 / 3) * ((1 - t) * pairwiseRisk w (fun i => mixtureScore (lam i) t)) ≤ hessian t) :
    (2 / 3) * pairwiseRisk w (fun i => Real.sqrt (lam i)) ≤ δ 1 := by
  let s := Ico (0 : ℝ) 1
  let μ := volume.restrict s
  let K : ℝ → ℝ := fun t => (1 - t) * pairwiseRisk w (fun i => mixtureScore (lam i) t)
  let F : ℝ → ℝ → ℝ := fun u t => max (u - t) 0 * K t
  let G : ℝ → ℝ := fun t => (1 - t) ^ 2 * pairwiseRisk w (fun i => mixtureScore (lam i) t)
  let P : ι → ι → ℝ → ℝ := fun i j t =>
    (1 - t) ^ 2 * (mixtureScore (lam j) t - mixtureScore (lam i) t) ^ 2 * w i j
  have hG : G = fun t => ∑ i, ∑ j, P i j t := by
    funext t
    simp only [G, pairwiseRisk, P, Finset.mul_sum, mul_assoc]
  have hP (i j : ι) : Integrable (P i j) μ :=
    (integrableOn_weighted_score_sub_sq (hlam i) (hlam j)).mul_const (w i j)
  have hInner (i : ι) : Integrable (fun t => ∑ j, P i j t) μ :=
    integrable_finsetSum _ fun j _ => hP i j
  have hGInt : Integrable G μ := by
    rw [hG]
    exact integrable_finsetSum _ fun i _ => hInner i
  have hSep : pairwiseRisk w (fun i => Real.sqrt (lam i)) ≤ ∫ t, G t ∂μ := by
    rw [pairwiseRisk, hG, integral_finsetSum _ (fun i _ => hInner i)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hP i j)]
    refine Finset.sum_le_sum fun j _ => ?_
    dsimp only [P]
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right
      (sq_sqrt_sub_le_integral_weighted_score_sub_sq (hlam i) (hlam j)) (hw i j)
  have hKCont : ContinuousOn K s := by
    have hd (i : ι) : ContinuousOn (mixtureScore (lam i)) s := continuousOn_mixtureScore (hlam i)
    refine (continuousOn_const.sub continuousOn_id).mul ?_
    exact continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      (((hd j).sub (hd i)).pow 2).mul continuousOn_const
  have hKNonneg (t : ℝ) (ht : t ∈ s) : 0 ≤ K t :=
    mul_nonneg (sub_nonneg.mpr ht.2.le) (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hw i j))
  have hGK (t : ℝ) : (1 - t) * K t = G t := by simp only [K, G, pow_two, mul_assoc]
  have hF_lim : Tendsto (fun u => ∫ t, F u t ∂μ) (𝓝[s] 1) (𝓝 (∫ t, G t ∂μ)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence G
    · refine Eventually.of_forall fun u => ?_
      have hCutoff : Continuous (fun t : ℝ => max (u - t) 0) := by fun_prop
      exact (hCutoff.continuousOn.mul hKCont).aestronglyMeasurable measurableSet_Ico
    · filter_upwards [self_mem_nhdsWithin] with u hu
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      have hm : max (u - t) 0 ≤ 1 - t :=
        max_le (sub_le_sub_right hu.2.le _) (sub_nonneg.mpr ht.2.le)
      rw [Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (hKNonneg t ht)), ← hGK]
      exact mul_le_mul_of_nonneg_right hm (hKNonneg t ht)
    · exact hGInt
    · filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      have hc : ContinuousAt (fun u : ℝ => max (u - t) 0 * K t) 1 := by fun_prop
      have hAtOne : F 1 t = G t := by
        simp only [F, max_eq_left (sub_nonneg.mpr ht.2.le), hGK]
      rw [← hAtOne]
      exact hc.continuousWithinAt
  have hCompact (u : ℝ) (hu : u ∈ s) : (2 / 3) * (∫ t, F u t ∂μ) ≤ δ u := by
    have hsub : Icc 0 u ⊆ s := fun _ ht => ⟨ht.1, ht.2.trans_lt hu.2⟩
    have hCut : (∫ t, F u t ∂μ) = ∫ t in (0 : ℝ)..u, (u - t) * K t := by
      calc
        _ = ∫ t in Icc (0 : ℝ) u, F u t :=
          setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ico hsub (fun t ht => by
            have hut : u ≤ t := le_of_not_ge (fun h => ht.2 ⟨ht.1.1, h⟩)
            simp only [F, max_eq_right (sub_nonpos.mpr hut), zero_mul])
        _ = ∫ t in Icc (0 : ℝ) u, (u - t) * K t :=
          setIntegral_congr_fun measurableSet_Icc fun t ht => by
            simp only [F, max_eq_left (sub_nonneg.mpr ht.2)]
        _ = _ := by rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hu.1]
    have hLeft : ContinuousOn (fun t => (u - t) * ((2 / 3) * K t)) (Icc 0 u) :=
      (continuousOn_const.sub continuousOn_id).mul
        (continuousOn_const.mul (hKCont.mono hsub))
    have hRight : ContinuousOn (fun t => (u - t) * hessian t) (Icc 0 u) :=
      (continuousOn_const.sub continuousOn_id).mul (hh u hu)
    rw [hCut, ← intervalIntegral.integral_const_mul, ← integral_hessian δ velocity hessian
      hu hδ₀ hv₀ hδ hv (hh u hu)]
    simp_rw [mul_left_comm (2 / 3 : ℝ)]
    rw [← uIcc_of_le hu.1] at hLeft hRight
    exact intervalIntegral.integral_mono_on hu.1 hLeft.intervalIntegrable hRight.intervalIntegrable
      fun t ht => mul_le_mul_of_nonneg_left (hSample t (hsub ht)) (sub_nonneg.mpr ht.2)
  have : (𝓝[s] (1 : ℝ)).NeBot := right_nhdsWithin_Ico_neBot zero_lt_one
  have hs : ∀ᶠ u in 𝓝[s] (1 : ℝ), u ∈ s := self_mem_nhdsWithin
  exact (mul_le_mul_of_nonneg_left hSep (by norm_num)).trans
    (le_of_tendsto_of_tendsto (hF_lim.const_mul (2 / 3)) hδ₁.continuousWithinAt
      (hs.mono hCompact))

open Matrix QuadraticBayesRiskGeometricPetz
open D5.S3.Divergence.LogDerivTrace (logDeriv)
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Endpoint bound for the actual geometric risk, with pair weights given by the
supported pretty-good measurement. The reference ensemble may be singular. -/
theorem geometricRisk_sqrt_le_of_hessian
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (δ velocity hessian : ℝ → ℝ) (hδ₁ : ContinuousAt δ 1)
    (hδ₀ : δ 0 = 0) (hv₀ : velocity 0 = 0)
    (hδ : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt δ (velocity t) (Ico 0 1) t)
    (hv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt velocity (hessian t) (Ico 0 1) t)
    (hh : ∀ u ∈ Ico (0 : ℝ) 1, ContinuousOn hessian (Icc 0 u))
    (hSample : ∀ t ∈ Ico (0 : ℝ) 1,
      (2 / 3) * ((1 - t) * geometricRisk A (fun i => mixtureScore (lam i) t)) ≤ hessian t) :
    (2 / 3) * geometricRisk A (fun i => Real.sqrt (lam i)) ≤ δ 1 := by
  let w : ι → ι → ℝ := fun i j => (1 / 2) * tracePair (A i) (pgmEffects A (some j))
  have hN := (pgmEffects_isPOVM A hA).1
  have hw (i j : ι) : 0 ≤ w i j :=
    mul_nonneg (by norm_num) (Complex.nonneg_iff.mp ((hA i).trace_mul_nonneg (hN (some j)))).1
  have hEq (c : ι → ℝ) : geometricRisk A c = pairwiseRisk w c := by
    rw [geometricRisk_eq_half_pairwise A c hA, pairwiseRisk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w]
    ring
  simp_rw [hEq] at hSample ⊢
  exact pairwiseRisk_sqrt_le_of_hessian w hw lam hlam δ velocity hessian
    hδ₁ hδ₀ hv₀ hδ hv hh hSample

/-- The score energy lost to the logarithmic Hessian of the retained mass. -/
def bkmDeficit (A : ι → Matrix n n ℂ) (c : ι → ℝ) : ℝ :=
  (∑ i, c i ^ 2 * (trace (A i)).re) -
    tracePair (scoreMoment A c) (logDeriv (∑ i, A i) (scoreMoment A c))

set_option maxHeartbeats 400000 in
/-- The BKM deficit on the actual tilted ensemble bounds the scaled reference
geometric risk. The positive definite mass is on the reference support. -/
theorem tilted_bkmDeficit_geometricRisk
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hQ : (∑ i, A i).PosDef) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    (2 / 3) * ((1 - t) * geometricRisk A (fun i => mixtureScore (lam i) t)) ≤
      bkmDeficit (fun i => (1 - t + t * lam i) • A i) (fun i => mixtureScore (lam i) t) := by
  let A' : ι → Matrix n n ℂ := fun i => (1 - t + t * lam i) • A i
  let d : ι → ℝ := fun i => mixtureScore (lam i) t
  have hr : 0 < 1 - t := sub_pos.mpr ht.2
  have hDom (i : ι) : (1 - t) • A i ≤ A' i := by
    rw [show A' i = (1 - t) • A i + (t * lam i) • A i by simp only [A', add_smul]]
    exact le_add_of_nonneg_right (smul_nonneg (mul_nonneg ht.1 (hlam i)) (hA i).nonneg)
  have hA' (i : ι) : (A' i).PosSemidef :=
    ((smul_nonneg hr.le (hA i).nonneg).trans (hDom i)).posSemidef
  have hExtra : (∑ i, (t * lam i) • A i).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ => (hA i).smul (mul_nonneg ht.1 (hlam i))
  have hQ' : (∑ i, A' i).PosDef := by
    simpa only [A', add_smul, Finset.sum_add_distrib, Finset.smul_sum] using
      (hQ.smul hr).add_posSemidef hExtra
  obtain ⟨L, hL, hSolve, hMinimum, N, hProj, hSum, hRisk⟩ :=
    quadraticRisk_minimum_sld A' d hA' hQ'
  have hN (j : ↥(PetzPositiveTraceFidelity.fidelityEigenvalues hL)) :
      (N j).PosSemidef := (hProj j).1.nonneg.posSemidef
  let E : ℝ := (∑ i, d i ^ 2 * (trace (A' i)).re) - tracePair (scoreMoment A' d) L
  have hTransfer : (1 - t) * geometricRisk A d ≤ E := calc
    _ ≤ (1 - t) * quadraticRisk A d N (fun j => j.val) :=
      mul_le_mul_of_nonneg_left (geometricRisk_le_quadraticRisk A d hA N _ hN hSum) hr.le
    _ ≤ quadraticRisk A' d N (fun j => j.val) :=
      smul_quadraticRisk_le A A' d N _ hN (1 - t) hDom
    _ = E := hRisk
  obtain ⟨hPGM, hPGMSum⟩ := pgmEffects_isPOVM A' hA'
  have hE : E ≤ 2 * geometricRisk A' d :=
    (hMinimum (Option ι) (pgmEffects A') (pgmScores d) hPGM hPGMSum).trans_eq
      (pgm_quadraticRisk_eq A' d hA')
  change (2 / 3) * ((1 - t) * geometricRisk A d) ≤ bkmDeficit A' d
  calc
    _ ≤ (2 / 3) * E := mul_le_mul_of_nonneg_left hTransfer (by norm_num)
    _ = (E + E) / 3 := by ring
    _ ≤ (2 * geometricRisk A' d + E) / 3 :=
      div_le_div_of_nonneg_right (add_le_add hE le_rfl) (by norm_num)
    _ ≤ bkmDeficit A' d := geometricRisk_sldRisk_le_bkm_deficit A' d hA' hQ' L hL hSolve

/-- Endpoint bound when the loss Hessian dominates the BKM deficit of the
tilted ensemble at each sample. Positive definiteness is only required on
the reference support and zero terminal likelihoods are allowed. -/
theorem geometricRisk_sqrt_le_of_bkm_hessian
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hQ : (∑ i, A i).PosDef)
    (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (δ velocity hessian : ℝ → ℝ) (hδ₁ : ContinuousAt δ 1)
    (hδ₀ : δ 0 = 0) (hv₀ : velocity 0 = 0)
    (hδ : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt δ (velocity t) (Ico 0 1) t)
    (hv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt velocity (hessian t) (Ico 0 1) t)
    (hh : ∀ u ∈ Ico (0 : ℝ) 1, ContinuousOn hessian (Icc 0 u))
    (hSample : ∀ t ∈ Ico (0 : ℝ) 1,
      bkmDeficit (fun i => (1 - t + t * lam i) • A i) (fun i => mixtureScore (lam i) t) ≤
        hessian t) :
    (2 / 3) * geometricRisk A (fun i => Real.sqrt (lam i)) ≤ δ 1 :=
  geometricRisk_sqrt_le_of_hessian A hA lam hlam δ velocity hessian hδ₁ hδ₀ hv₀ hδ hv hh
    fun t ht => (tilted_bkmDeficit_geometricRisk A hA hQ lam hlam t ht).trans (hSample t ht)

end PetzLikelihoodHessianIntegration
