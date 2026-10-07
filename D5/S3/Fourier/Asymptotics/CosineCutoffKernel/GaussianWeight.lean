/- GID: D5/S3/Fourier/Asymptotics/CosineCutoffKernel/GaussianWeight
   generality: I
   mirror-B: D5/B/S3/Fourier/Asymptotics/CosineCutoffKernel/GaussianWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian density supplies the L2 integral-kernel factory, onto density isometry, difference-kernel norm identities, and actual convolution conjugacy. -/

import Mathlib.Analysis.Fourier.FourierTransform
import D5.S3.Quantum.Analysis.FourierWindowFiniteRank
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory Set Filter FourierTransform
open scoped FourierTransform ENNReal Topology SchwartzMap
noncomputable section

namespace D5.S3.Fourier.Asymptotics.CosineCutoffKernel.GaussianWeight

theorem weighted_integral_operator (r α : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    let a : ℝ := (1+r)/2
    let b : ℝ := (1-r)/2
    let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
    let κ : ℝ := 1/a + α^2/b
    let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ * x ^ 2 / 2)
    let μρ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
    ∃ T : Lp ℝ 2 (μρ.prod μρ) →L[ℝ] (Lp ℝ 2 μρ →L[ℝ] Lp ℝ 2 μρ),
      (∀ (K : Lp ℝ 2 (μρ.prod μρ)) (f : Lp ℝ 2 μρ),
        (fun x => T K f x) =ᵐ[μρ] (fun x => ∫ y, K (x, y) * f y ∂μρ)) ∧
      (∀ K L, ‖T K - T L‖ ≤ ‖K - L‖) ∧
      (∀ (ι : Type) (l : Filter ι) (Ks : ι → Lp ℝ 2 (μρ.prod μρ))
        (K : Lp ℝ 2 (μρ.prod μρ)), Tendsto Ks l (nhds K) →
        Tendsto (fun i => T (Ks i)) l (nhds (T K))) ∧
      (∀ (K : Lp ℝ 2 (μρ.prod μρ)) (f : Lp ℝ 2 μρ)
        (k : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
        (hk : k =ᵐ[μρ.prod μρ] (K : ℝ × ℝ → ℝ)) (hg : g =ᵐ[μρ] (f : ℝ → ℝ)),
        (∀ᵐ x ∂μρ, Integrable (fun y => k (x,y) * g y) μρ) ∧
        (fun x => ∫ y, k (x,y) * g y ∂μρ) =ᵐ[μρ] (fun x => T K f x)) ∧
      (∀ (ι : Type) (l : Filter ι) (hl : l.NeBot) (Ks : ι → Lp ℝ 2 (μρ.prod μρ))
        (K : Lp ℝ 2 (μρ.prod μρ)) (B : ℝ), Tendsto Ks l (nhds K) →
        (∀ᶠ i in l, ‖T (Ks i)‖ ≤ B) → ‖T K‖ ≤ B) := by
  classical
  let a : ℝ := (1+r)/2
  let b : ℝ := (1-r)/2
  let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
  let κ : ℝ := 1/a + α^2/b
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hκ : 0 < κ := by
    exact add_pos_of_pos_of_nonneg (one_div_pos.mpr ha) (div_nonneg (sq_nonneg α) hb.le)
  dsimp only
  let μ : Measure ℝ := volume.withDensity
    (fun x => ENNReal.ofReal (c0 * Real.exp (-κ * x ^ 2 / 2)))
  change ∃ T : Lp ℝ 2 (μ.prod μ) →L[ℝ] (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ), _
  have hsq (X : Type) [MeasurableSpace X] (ν : Measure X) (f : Lp ℝ 2 ν) :
      ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    funext x
    simp [Real.inner_apply, pow_two]
  have hrow (K : Lp ℝ 2 (μ.prod μ)) :
      ∀ᵐ x ∂μ, MemLp (fun y => K (x,y)) 2 μ := by
    filter_upwards [(Lp.memLp K).aestronglyMeasurable.prodMk_left,
      (Lp.memLp K).integrable_sq.prod_right_ae] with x hm hi
    exact (memLp_two_iff_integrable_sq hm).mpr hi
  have hprod (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      AEStronglyMeasurable (fun z : ℝ × ℝ => K z * f z.2) (μ.prod μ) :=
    (Lp.aestronglyMeasurable K).mul (Lp.aestronglyMeasurable f).comp_snd
  have hbound (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      ∀ᵐ x ∂μ, (∫ y, K (x,y) * f y ∂μ) ^ 2 ≤
        (∫ y, K (x,y) ^ 2 ∂μ) * ‖f‖ ^ 2 := by
    filter_upwards [hrow K] with x hx
    let k := hx.toLp (fun y => K (x,y))
    have hi : (∫ y, K (x,y) * f y ∂μ) = inner ℝ k f := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hx.coeFn_toLp] with y hy
      simp [k, hy, Real.inner_apply, mul_comm]
    have hn : ‖k‖ ^ 2 = ∫ y, K (x,y) ^ 2 ∂μ := by
      rw [hsq ℝ μ k]
      apply integral_congr_ae
      filter_upwards [hx.coeFn_toLp] with y hy
      rw [hy]
    rw [hi, ← hn]
    have hc := norm_inner_le_norm (𝕜 := ℝ) k f
    have hp : 0 ≤ ‖k‖ * ‖f‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hs := mul_self_le_mul_self (norm_nonneg (inner ℝ k f)) hc
    simpa [Real.norm_eq_abs, ← pow_two, sq_abs, mul_pow] using hs
  have hmem (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      MemLp (fun x => ∫ y, K (x,y) * f y ∂μ) 2 μ := by
    have hm := (hprod K f).integral_prod_right'
    apply (memLp_two_iff_integrable_sq hm).mpr
    refine ((Lp.memLp K).integrable_sq.integral_prod_left.mul_const (‖f‖ ^ 2)).mono'
      (hm.pow 2) ?_
    filter_upwards [hbound K f] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (∫ y, K (x,y) * f y ∂μ))] using hx
  let B (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
    (hmem K f).toLp (fun x => ∫ y, K (x,y) * f y ∂μ)
  have hB (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      (B K f : ℝ → ℝ) =ᵐ[μ] (fun x => ∫ y, K (x,y) * f y ∂μ) :=
    (hmem K f).coeFn_toLp
  have hnB (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) : ‖B K f‖ ≤ ‖K‖ * ‖f‖ := by
    have h1 : ‖B K f‖ ^ 2 = ∫ x, (∫ y, K (x,y) * f y ∂μ) ^ 2 ∂μ := by
      rw [hsq ℝ μ (B K f)]
      exact integral_congr_ae ((hB K f).fun_comp (fun z : ℝ => z ^ 2))
    have h2 : ∫ x, (∫ y, K (x,y) ^ 2 ∂μ) * ‖f‖ ^ 2 ∂μ = ‖K‖ ^ 2 * ‖f‖ ^ 2 := by
      rw [integral_mul_const, ← integral_prod (f := fun z : ℝ × ℝ => K z ^ 2)
        (Lp.memLp K).integrable_sq, ← hsq (ℝ × ℝ) (μ.prod μ) K]
    have h3 := integral_mono_ae (hmem K f).integrable_sq
      ((Lp.memLp K).integrable_sq.integral_prod_left.mul_const (‖f‖ ^ 2)) (hbound K f)
    rw [← h1, h2] at h3
    nlinarith [norm_nonneg (B K f), norm_nonneg K, norm_nonneg f,
      mul_nonneg (norm_nonneg K) (norm_nonneg f)]
  have hrowInt (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      ∀ᵐ x ∂μ, Integrable (fun y => K (x,y) * f y) μ := by
    filter_upwards [hrow K] with x hx
    let k := hx.toLp (fun y => K (x,y))
    have hi := L2.integrable_inner (𝕜 := ℝ) k f
    apply hi.congr
    filter_upwards [hx.coeFn_toLp] with y hy
    simp [k, hy, Real.inner_apply, mul_comm]
  have hBaddR (K : Lp ℝ 2 (μ.prod μ)) (f g : Lp ℝ 2 μ) :
      B K (f+g) = B K f + B K g := by
    apply Lp.ext
    filter_upwards [hB K (f+g), hB K f, hB K g, Lp.coeFn_add (B K f) (B K g),
      hrowInt K f, hrowInt K g] with x ha hb hc hd hi hj
    rw [ha, hd]
    simp only [Pi.add_apply]
    rw [hb, hc, ← integral_add hi hj]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy]
    change K (x,y) * (f y + g y) = K (x,y) * f y + K (x,y) * g y
    ring
  have hBsmulR (K : Lp ℝ 2 (μ.prod μ)) (a : ℝ) (f : Lp ℝ 2 μ) :
      B K (a • f) = a • B K f := by
    apply Lp.ext
    filter_upwards [hB K (a • f), hB K f, Lp.coeFn_smul a (B K f)] with x ha hb hc
    rw [ha, hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hb, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul a f] with y hy
    simp only [hy, Pi.smul_apply, smul_eq_mul]
    ring
  have hBaddL (K L : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      B (K+L) f = B K f + B L f := by
    apply Lp.ext
    filter_upwards [hB (K+L) f, hB K f, hB L f, Lp.coeFn_add (B K f) (B L f),
      hrowInt K f, hrowInt L f, Measure.ae_ae_of_ae_prod (Lp.coeFn_add K L)]
      with x ha hb hc hd hi hj he
    rw [ha, hd]
    simp only [Pi.add_apply]
    rw [hb, hc, ← integral_add hi hj]
    apply integral_congr_ae
    filter_upwards [he] with y hy
    rw [hy]
    change (K (x,y) + L (x,y)) * f y = K (x,y) * f y + L (x,y) * f y
    ring
  have hBsmulL (a : ℝ) (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
      B (a • K) f = a • B K f := by
    apply Lp.ext
    filter_upwards [hB (a • K) f, hB K f, Lp.coeFn_smul a (B K f),
      Measure.ae_ae_of_ae_prod (Lp.coeFn_smul a K)] with x ha hb hc hd
    rw [ha, hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hb, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hd] with y hy
    simp only [hy, Pi.smul_apply, smul_eq_mul]
    ring
  let Bₗ : Lp ℝ 2 (μ.prod μ) →ₗ[ℝ] (Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ) :=
    { toFun := fun K =>
        { toFun := B K
          map_add' := hBaddR K
          map_smul' := fun a f => hBsmulR K a f }
      map_add' := fun K L => by
        apply LinearMap.ext
        intro f
        exact hBaddL K L f
      map_smul' := fun a K => by
        apply LinearMap.ext
        intro f
        exact hBsmulL a K f }
  let T := Bₗ.mkContinuous₂ 1 (by
    intro K f
    change ‖B K f‖ ≤ 1 * ‖K‖ * ‖f‖
    simpa only [one_mul] using hnB K f)
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro K f
    exact hB K f
  · intro K L
    rw [← map_sub T]
    exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun f => hnB (K-L) f)
  · intro ι l Ks K hKs
    exact (T.continuous.tendsto K).comp hKs
  · intro K f k g hk hg
    have hke := Measure.ae_ae_of_ae_prod hk
    constructor
    · filter_upwards [hrowInt K f, hke] with x hx he
      apply hx.congr
      filter_upwards [he, hg] with y hy hz
      rw [hy, hz]
    · filter_upwards [hB K f, hke] with x hx he
      change (∫ y, k (x,y) * g y ∂μ) = B K f x
      rw [hx]
      apply integral_congr_ae
      filter_upwards [he, hg] with y hy hz
      rw [hy, hz]
  · intro ι l hl Ks K B hKs hbound
    letI : l.NeBot := hl
    exact le_of_tendsto ((continuous_norm.comp T.continuous).tendsto K |>.comp hKs) hbound


theorem density_unitary (r α : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    let a : ℝ := (1+r)/2
    let b : ℝ := (1-r)/2
    let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
    let κ : ℝ := 1/a + α^2/b
    let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ * x ^ 2 / 2)
    let μρ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
    ∃ U : Lp ℝ 2 μρ ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ),
      (∀ f, (fun x => U f x) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * f x)) ∧
      (∀ h, (fun x => U.symm h x) =ᵐ[μρ] (fun x => h x / Real.sqrt (ρ x))) := by
  classical
  let a : ℝ := (1+r)/2
  let b : ℝ := (1-r)/2
  let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
  let κ : ℝ := 1/a + α^2/b
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hκ : 0 < κ := by
    exact add_pos_of_pos_of_nonneg (one_div_pos.mpr ha) (div_nonneg (sq_nonneg α) hb.le)
  dsimp only
  let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ * x ^ 2 / 2)
  let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
  change ∃ U : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ), _
  have hρ : ∀ x, 0 < ρ x := fun x => mul_pos hc0 (Real.exp_pos _)
  have hρm : Measurable ρ := by dsimp [ρ]; fun_prop
  have hdm : Measurable (fun x => ENNReal.ofReal (ρ x)) := hρm.ennreal_ofReal
  have hd0 : ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (ρ x) ≠ 0 :=
    ae_of_all _ (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (hρ x)))
  have hvol : (volume : Measure ℝ) ≪ μ :=
    withDensity_absolutelyContinuous' hdm.aemeasurable hd0
  have hμ : μ ≪ (volume : Measure ℝ) := withDensity_absolutelyContinuous _ _
  have hs0 : ∀ x, Real.sqrt (ρ x) ≠ 0 := fun x => ne_of_gt (Real.sqrt_pos.mpr (hρ x))
  have hs2 : ∀ x, Real.sqrt (ρ x) ^ 2 = ρ x := fun x => Real.sq_sqrt (hρ x).le
  have hsm : Measurable (fun x => Real.sqrt (ρ x)) := hρm.sqrt
  have hsq (ν : Measure ℝ) (f : Lp ℝ 2 ν) : ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    funext x
    simp [Real.inner_apply, pow_two]
  have hwd (g : ℝ → ℝ) : Integrable g μ ↔ Integrable (fun x => ρ x * g x) volume := by
    have ht := integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
      hdm (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) (g := g)
    simpa [μ, smul_eq_mul, ENNReal.toReal_ofReal (hρ _).le] using ht
  have hwi (g : ℝ → ℝ) : (∫ x, g x ∂μ) = ∫ x, ρ x * g x := by
    have ht := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ))
      hdm (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) g
    simpa [μ, smul_eq_mul, ENNReal.toReal_ofReal (hρ _).le] using ht
  have hfwd (f : Lp ℝ 2 μ) : MemLp (fun x => Real.sqrt (ρ x) * f x) 2 volume := by
    have hm := hsm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).mono_ac hvol)
    apply (memLp_two_iff_integrable_sq hm).mpr
    have hi := (hwd (fun x => f x ^ 2)).mp (Lp.memLp f).integrable_sq
    have he : (fun x => (Real.sqrt (ρ x) * f x) ^ 2) =
        (fun x => ρ x * f x ^ 2) := by
      funext x
      rw [mul_pow, hs2 x]
    change Integrable (fun x => (Real.sqrt (ρ x) * f x) ^ 2) volume
    rw [he]
    exact hi
  have hbwd (h : Lp ℝ 2 (volume : Measure ℝ)) :
      MemLp (fun x => h x / Real.sqrt (ρ x)) 2 μ := by
    have hm : AEStronglyMeasurable (fun x => h x / Real.sqrt (ρ x)) volume :=
      ((Lp.aestronglyMeasurable h).aemeasurable.div hsm.aemeasurable).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq (hm.mono_ac hμ)).mpr
    apply (hwd (fun x => (h x / Real.sqrt (ρ x)) ^ 2)).mpr
    have he : (fun x => ρ x * (h x / Real.sqrt (ρ x)) ^ 2) =
        (fun x => h x ^ 2) := by
      funext x
      rw [div_pow, hs2 x]
      field_simp [(hρ x).ne']
    rw [he]
    exact (Lp.memLp h).integrable_sq
  let V (f : Lp ℝ 2 μ) : Lp ℝ 2 (volume : Measure ℝ) :=
    (hfwd f).toLp (fun x => Real.sqrt (ρ x) * f x)
  have hV (f : Lp ℝ 2 μ) : (V f : ℝ → ℝ) =ᵐ[volume]
      (fun x => Real.sqrt (ρ x) * f x) := (hfwd f).coeFn_toLp
  have hVa (f g : Lp ℝ 2 μ) : V (f+g) = V f + V g := by
    apply Lp.ext
    filter_upwards [hV (f+g), hV f, hV g, Lp.coeFn_add (V f) (V g),
      hvol.ae_eq (Lp.coeFn_add f g)] with x ha hb hc hd he
    simp only [ha, hd, hb, hc, he, Pi.add_apply, mul_add]
  have hVs (a : ℝ) (f : Lp ℝ 2 μ) : V (a • f) = a • V f := by
    apply Lp.ext
    filter_upwards [hV (a • f), hV f, Lp.coeFn_smul a (V f),
      hvol.ae_eq (Lp.coeFn_smul a f)] with x ha hb hc hd
    simp only [ha, hc, hb, hd, Pi.smul_apply, smul_eq_mul]
    ring
  have hVn (f : Lp ℝ 2 μ) : ‖V f‖ = ‖f‖ := by
    have he : ‖V f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [hsq volume (V f), hsq μ f, hwi]
      apply integral_congr_ae
      filter_upwards [hV f] with x hx
      rw [hx, mul_pow, hs2 x]
    nlinarith [norm_nonneg (V f), norm_nonneg f]
  let Vᵢ : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
    { toFun := V, map_add' := hVa, map_smul' := hVs, norm_map' := hVn }
  have hsurj : Function.Surjective Vᵢ := by
    intro h
    let f := (hbwd h).toLp (fun x => h x / Real.sqrt (ρ x))
    refine ⟨f, ?_⟩
    apply Lp.ext
    filter_upwards [hV f, hvol.ae_eq (hbwd h).coeFn_toLp] with x hx hf
    change V f x = h x
    rw [hx, hf]
    field_simp [hs0 x]
  let U := LinearIsometryEquiv.ofSurjective Vᵢ hsurj
  refine ⟨U, ?_, ?_⟩
  · intro f
    exact hV f
  · intro h
    have hf := hμ.ae_eq (hV (U.symm h))
    filter_upwards [hf] with x hx
    change U.symm h x = h x / Real.sqrt (ρ x)
    have he : V (U.symm h) = h := U.apply_symm_apply h
    rw [he] at hx
    apply (eq_div_iff (hs0 x)).mpr
    simpa [mul_comm] using hx.symm


theorem gaussian_weighted_kernel (r α : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    let a : ℝ := (1+r)/2
    let b : ℝ := (1-r)/2
    let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
    let κ : ℝ := 1/a + α^2/b
    let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ*x^2/2)
    let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
    let g0 : ℝ := c0^2 * Real.sqrt (Real.pi/κ)
    (∀ z : ℝ, (∫ x, ρ x * ρ (x-z)) = g0 * Real.exp (-κ*z^2/4)) ∧
    (g0 = ∫ x, ρ x^2) ∧
    (∀ (q : ℝ → ℝ) (hmq : Measurable q) (hq : MemLp q 2 (volume : Measure ℝ)),
      ∃ K : Lp ℝ 2 (μ.prod μ),
        (K : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => q (z.1-z.2)) ∧
        ‖K‖^2 = ∫ z, q z ^ 2 * (g0 * Real.exp (-κ*z^2/4)) ∧
        ‖K‖^2 ≤ g0 * ‖hq.toLp q‖^2) ∧
    (∀ (q p : ℝ → ℝ) (hmq : Measurable q) (hmp : Measurable p)
      (hq : MemLp q 2 (volume : Measure ℝ)) (hp : MemLp p 2 (volume : Measure ℝ))
      (K L : Lp ℝ 2 (μ.prod μ))
      (hK : (K : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => q (z.1-z.2)))
      (hL : (L : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => p (z.1-z.2))),
      ‖K-L‖^2 ≤ g0 * ‖hq.toLp q-hp.toLp p‖^2) ∧
    (∀ (ι : Type) (l : Filter ι) (q : ι → ℝ → ℝ) (p : ℝ → ℝ)
      (hmq : ∀ i, Measurable (q i)) (hmp : Measurable p)
      (hq : ∀ i, MemLp (q i) 2 (volume : Measure ℝ)) (hp : MemLp p 2 (volume : Measure ℝ))
      (Ks : ι → Lp ℝ 2 (μ.prod μ)) (K : Lp ℝ 2 (μ.prod μ))
      (hKs : ∀ i, (Ks i : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => q i (z.1-z.2)))
      (hK : (K : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => p (z.1-z.2))),
      Tendsto (fun i => (hq i).toLp (q i)) l (nhds (hp.toLp p)) → Tendsto Ks l (nhds K)) := by
  classical
  let a : ℝ := (1+r)/2
  let b : ℝ := (1-r)/2
  let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
  let κ : ℝ := 1/a + α^2/b
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hκ : 0 < κ := by
    exact add_pos_of_pos_of_nonneg (one_div_pos.mpr ha) (div_nonneg (sq_nonneg α) hb.le)
  let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ*x^2/2)
  have hG : ∀ z : ℝ, (∫ x, ρ x * ρ (x-z)) =
      c0^2 * Real.sqrt (Real.pi/κ) * Real.exp (-κ*z^2/4) := by
    intro z
    have he (x : ℝ) : ρ x * ρ (x-z) =
        (c0^2 * Real.exp (-κ*z^2/4)) * Real.exp (-κ*(x-z/2)^2) := by
      dsimp [ρ]
      have hp : -κ*x^2/2 + -κ*(x-z)^2/2 = -κ*z^2/4 + -κ*(x-z/2)^2 := by ring
      calc
        (c0 * Real.exp (-κ*x^2/2)) * (c0 * Real.exp (-κ*(x-z)^2/2)) =
            c0^2 * Real.exp (-κ*x^2/2 + -κ*(x-z)^2/2) := by rw [Real.exp_add]; ring
        _ = (c0^2 * Real.exp (-κ*z^2/4)) * Real.exp (-κ*(x-z/2)^2) := by
          rw [hp, Real.exp_add]; ring
    calc
      (∫ x, ρ x * ρ (x-z)) = (c0^2 * Real.exp (-κ*z^2/4)) *
          ∫ x : ℝ, Real.exp (-κ*(x-z/2)^2) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ he)
      _ = c0^2 * Real.sqrt (Real.pi/κ) * Real.exp (-κ*z^2/4) := by
        rw [integral_sub_right_eq_self (fun x : ℝ => Real.exp (-κ*x^2)) (z/2),
          integral_gaussian κ]
        ring
  let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
  let g0 : ℝ := c0^2 * Real.sqrt (Real.pi/κ)
  dsimp only
  change (∀ z : ℝ, (∫ x, ρ x * ρ (x-z)) = g0 * Real.exp (-κ*z^2/4)) ∧ _
  have hBuild : ∀ (q : ℝ → ℝ) (hmq : Measurable q) (hq : MemLp q 2 (volume : Measure ℝ)),
      ∃ K : Lp ℝ 2 (μ.prod μ),
        (K : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => q (z.1-z.2)) ∧
        ‖K‖^2 = ∫ z, q z^2 * (g0 * Real.exp (-κ*z^2/4)) ∧
        ‖K‖^2 ≤ g0 * ‖hq.toLp q‖^2 := by
    intro q hmq hq
    have hρ : ∀ x, 0 < ρ x := fun x => mul_pos hc0 (Real.exp_pos _)
    have hρm : Measurable ρ := by dsimp [ρ]; fun_prop
    have hρb (x : ℝ) : ρ x ≤ c0 := by
      have he : -κ*x^2/2 ≤ 0 := by nlinarith [sq_nonneg x]
      dsimp [ρ]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr he) hc0.le
    have hρi : Integrable ρ (volume : Measure ℝ) := by
      have hi : Integrable (fun x : ℝ => Real.exp (-(κ/2)*x^2)) :=
        integrable_exp_neg_mul_sq_iff.mpr (by positivity)
      convert! hi.const_mul c0 using 1
      funext x
      dsimp [ρ]
      congr 2
      ring
    have hq2 := hq.integrable_sq
    let w : ℝ × ℝ → ℝ := fun z => (ρ z.1 * ρ z.2) * q (z.1-z.2)^2
    let v : ℝ × ℝ → ℝ := fun z => (ρ z.1 * ρ (z.1-z.2)) * q z.2^2
    have hwm : Measurable w := by dsimp [w]; fun_prop
    have hvm : Measurable v := by dsimp [v]; fun_prop
    have hw0 (z : ℝ × ℝ) : 0 ≤ w z := by dsimp [w]; positivity
    have hv0 (z : ℝ × ℝ) : 0 ≤ v z := by dsimp [v]; positivity
    have hwr (x : ℝ) : Integrable (fun y => w (x,y)) := by
      have hi := (hq2.comp_sub_left x).const_mul (c0*ρ x)
      refine hi.mono' (hwm.comp measurable_prodMk_left).aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 (x,y))]
      dsimp [w]
      calc
        ρ x * ρ y * q (x-y)^2 ≤ ρ x * c0 * q (x-y)^2 := by gcongr; exact hρb y
        _ = c0 * ρ x * q (x-y)^2 := by ring
    have hwi : Integrable w ((volume : Measure ℝ).prod volume) := by
      apply (integrable_prod_iff hwm.aestronglyMeasurable).mpr
      refine ⟨ae_of_all _ hwr, ?_⟩
      have hi := (hρi.const_mul c0).mul_const (∫ y, q y^2)
      refine hi.mono' (hwm.aestronglyMeasurable.norm.integral_prod_right') ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun y => norm_nonneg (w (x,y))))]
      calc
        (∫ y, ‖w (x,y)‖) ≤ ∫ y, c0 * ρ x * q (x-y)^2 := by
          apply integral_mono (hwr x).norm ((hq2.comp_sub_left x).const_mul (c0*ρ x))
          intro y
          change ‖w (x,y)‖ ≤ c0 * ρ x * q (x-y)^2
          rw [Real.norm_eq_abs, abs_of_nonneg (hw0 (x,y))]
          dsimp [w]
          calc
            ρ x * ρ y * q (x-y)^2 ≤ ρ x * c0 * q (x-y)^2 := by gcongr; exact hρb y
            _ = c0 * ρ x * q (x-y)^2 := by ring
        _ = c0 * ρ x * ∫ y, q y^2 := by
          rw [integral_const_mul, integral_sub_left_eq_self (fun y : ℝ => q y^2) volume x]
    have hvi : Integrable v ((volume : Measure ℝ).prod volume) := by
      have hi := (hρi.const_mul c0).mul_prod hq2
      refine hi.mono' hvm.aestronglyMeasurable ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (hv0 z)]
      dsimp [v]
      calc
        ρ z.1 * ρ (z.1-z.2) * q z.2^2 ≤ ρ z.1 * c0 * q z.2^2 := by
          gcongr
          exact hρb (z.1-z.2)
        _ = c0 * ρ z.1 * q z.2^2 := by ring
    have hprod : μ.prod μ = ((volume : Measure ℝ).prod volume).withDensity
        (fun z => ENNReal.ofReal (ρ z.1 * ρ z.2)) := by
      dsimp [μ]
      rw [prod_withDensity hρm.ennreal_ofReal hρm.ennreal_ofReal]
      congr 1
      funext z
      exact (ENNReal.ofReal_mul (hρ z.1).le).symm
    have hDm : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (ρ z.1 * ρ z.2)) := by fun_prop
    have hDt (z : ℝ × ℝ) : (ENNReal.ofReal (ρ z.1 * ρ z.2)).toReal = ρ z.1 * ρ z.2 :=
      ENNReal.toReal_ofReal (mul_nonneg (hρ z.1).le (hρ z.2).le)
    have hKmem : MemLp (fun z : ℝ × ℝ => q (z.1-z.2)) 2 (μ.prod μ) := by
      have hm : Measurable (fun z : ℝ × ℝ => q (z.1-z.2)) :=
        hmq.comp (measurable_fst.sub measurable_snd)
      apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
      rw [hprod]
      apply (integrable_withDensity_iff_integrable_smul' hDm
        (ae_of_all _ (fun z => ENNReal.ofReal_lt_top))).mpr
      simpa only [hDt, smul_eq_mul] using hwi
    have hshift (x : ℝ) : (∫ y, w (x,y)) = ∫ z, v (x,z) := by
      have he := integral_sub_left_eq_self (fun z : ℝ => v (x,z)) volume x
      simpa only [v, w, sub_sub_cancel] using he
    have hvinner (z : ℝ) : (∫ x, v (x,z)) = q z^2 * (g0 * Real.exp (-κ*z^2/4)) := by
      dsimp [v]
      rw [integral_mul_const, hG z]
      dsimp [g0]
      ring
    have hI : (∫ z, q (z.1-z.2)^2 ∂μ.prod μ) =
        ∫ z, q z^2 * (g0 * Real.exp (-κ*z^2/4)) := by
      have hd := integral_withDensity_eq_integral_toReal_smul
        (μ := (volume : Measure ℝ).prod volume) hDm
        (ae_of_all _ (fun z => ENNReal.ofReal_lt_top))
        (fun z : ℝ × ℝ => q (z.1-z.2)^2)
      rw [hprod]
      calc
        (∫ z, q (z.1-z.2)^2 ∂((volume : Measure ℝ).prod volume).withDensity
            (fun z => ENNReal.ofReal (ρ z.1 * ρ z.2))) = ∫ z, w z ∂volume.prod volume := by
          simpa only [hDt, smul_eq_mul] using hd
        _ = ∫ x, ∫ y, w (x,y) := integral_prod w hwi
        _ = ∫ x, ∫ z, v (x,z) := by simp_rw [hshift]
        _ = ∫ z, ∫ x, v (x,z) := integral_integral_swap hvi
        _ = ∫ z, q z^2 * (g0 * Real.exp (-κ*z^2/4)) := by simp_rw [hvinner]
    let K : Lp ℝ 2 (μ.prod μ) := hKmem.toLp (fun z : ℝ × ℝ => q (z.1-z.2))
    have hsq (X : Type) [MeasurableSpace X] (ν : Measure X) (f : Lp ℝ 2 ν) :
        ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂ν := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      congr 1
      funext x
      simp [pow_two]
    have hKN : ‖K‖^2 = ∫ z, q z^2 * (g0 * Real.exp (-κ*z^2/4)) := by
      rw [hsq (ℝ × ℝ) (μ.prod μ) K, ← hI]
      exact integral_congr_ae (hKmem.coeFn_toLp.fun_comp (fun a : ℝ => a^2))
    have hQN : ‖hq.toLp q‖^2 = ∫ z, q z^2 := by
      rw [hsq ℝ volume (hq.toLp q)]
      exact integral_congr_ae (hq.coeFn_toLp.fun_comp (fun a : ℝ => a^2))
    refine ⟨K, hKmem.coeFn_toLp, hKN, ?_⟩
    rw [hKN, hQN, ← integral_const_mul]
    apply integral_mono
    · exact hvi.integral_prod_right.congr (ae_of_all _ hvinner)
    · exact hq2.const_mul g0
    · intro z
      have he : Real.exp (-κ*z^2/4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
      have hg0 : 0 ≤ g0 := by dsimp [g0]; positivity
      calc
        q z^2 * (g0 * Real.exp (-κ*z^2/4)) ≤ q z^2 * (g0*1) := by gcongr
        _ = g0 * q z^2 := by ring
  have hPair : ∀ (q p : ℝ → ℝ) (hmq : Measurable q) (hmp : Measurable p)
      (hq : MemLp q 2 (volume : Measure ℝ)) (hp : MemLp p 2 (volume : Measure ℝ))
      (K L : Lp ℝ 2 (μ.prod μ))
      (hK : (K : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => q (z.1-z.2)))
      (hL : (L : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => p (z.1-z.2))),
      ‖K-L‖^2 ≤ g0 * ‖hq.toLp q-hp.toLp p‖^2 := by
    intro q p hmq hmp hq hp K L hK hL
    obtain ⟨D, hD, _, hDn⟩ := hBuild (q-p) (hmq.sub hmp) (hq.sub hp)
    have hKD : K-L = D := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub K L, hK, hL, hD] with z ha hb hc hd
      simp only [ha, Pi.sub_apply, hb, hc, hd]
    have hqp : (hq.sub hp).toLp (q-p) = hq.toLp q-hp.toLp p := by
      apply Lp.ext
      filter_upwards [(hq.sub hp).coeFn_toLp, hq.coeFn_toLp, hp.coeFn_toLp,
        Lp.coeFn_sub (hq.toLp q) (hp.toLp p)] with z ha hb hc hd
      simp only [ha, hd, Pi.sub_apply, hb, hc]
    rw [hKD]
    simpa only [hqp] using hDn
  have hgself : g0 = ∫ x, ρ x^2 := by
    simpa only [g0, sub_zero, pow_two, mul_zero, zero_div, Real.exp_zero, mul_one] using (hG 0).symm
  refine ⟨hG, hgself, hBuild, hPair, ?_⟩
  intro ι l q p hmq hmp hq hp Ks K hKs hK hconv
  have hg0 : 0 ≤ g0 := by dsimp [g0]; positivity
  have hn (i : ι) : ‖Ks i-K‖ ≤ Real.sqrt g0 * ‖(hq i).toLp (q i)-hp.toLp p‖ := by
    have hb := hPair (q i) p (hmq i) hmp (hq i) hp (Ks i) K (hKs i) hK
    have he : (Real.sqrt g0 * ‖(hq i).toLp (q i)-hp.toLp p‖)^2 =
        g0 * ‖(hq i).toLp (q i)-hp.toLp p‖^2 := by
      rw [mul_pow, Real.sq_sqrt hg0]
    nlinarith [norm_nonneg (Ks i-K),
      mul_nonneg (Real.sqrt_nonneg g0) (norm_nonneg ((hq i).toLp (q i)-hp.toLp p))]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun i => norm_nonneg (Ks i-K)) hn
    (by simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hconv)))


theorem cutoff_conjugacy (r α : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    let a : ℝ := (1+r)/2
    let b : ℝ := (1-r)/2
    let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
    let κ : ℝ := 1/a + α^2/b
    let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ * x ^ 2 / 2)
    let μρ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
    ∀ (q : ℝ → ℝ) (hq : MemLp q 2 (volume : Measure ℝ))
      (C : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ))
      (hC : ∀ h, (fun x => C h x) =ᵐ[volume] (fun x => ∫ y, q (x-y) * h y))
      (T : Lp ℝ 2 μρ →L[ℝ] Lp ℝ 2 μρ)
      (hT : ∀ f, (fun x => T f x) =ᵐ[μρ] (fun x => ∫ y, q (x-y) * f y ∂μρ))
      (U : Lp ℝ 2 μρ ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ))
      (hU : ∀ f, (fun x => U f x) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * f x))
      (hUinv : ∀ h, (fun x => U.symm h x) =ᵐ[μρ] (fun x => h x / Real.sqrt (ρ x))),
      ∃ M : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ),
        (∀ h, (fun x => M h x) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * h x)) ∧
        ‖M‖ ≤ Real.sqrt c0 ∧
        U.toLinearIsometry.toContinuousLinearMap.comp (T.comp U.symm.toLinearIsometry.toContinuousLinearMap) =
          M.comp (C.comp M) ∧ ‖T‖ ≤ c0 * ‖C‖ := by
  classical
  let a : ℝ := (1+r)/2
  let b : ℝ := (1-r)/2
  let c0 : ℝ := 1 / (4 * Real.pi * Real.sqrt (a*b))
  let κ : ℝ := 1/a + α^2/b
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hκ : 0 < κ := by
    exact add_pos_of_pos_of_nonneg (one_div_pos.mpr ha) (div_nonneg (sq_nonneg α) hb.le)
  dsimp only
  let ρ : ℝ → ℝ := fun x => c0 * Real.exp (-κ * x ^ 2 / 2)
  let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
  intro q hq C hC T hT U hU hUinv
  have hρ : ∀ x, 0 < ρ x := fun x => mul_pos hc0 (Real.exp_pos _)
  have hρm : Measurable ρ := by dsimp [ρ]; fun_prop
  have hdm : Measurable (fun x => ENNReal.ofReal (ρ x)) := hρm.ennreal_ofReal
  have hd0 : ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (ρ x) ≠ 0 :=
    ae_of_all _ (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (hρ x)))
  have hvol : (volume : Measure ℝ) ≪ μ :=
    withDensity_absolutelyContinuous' hdm.aemeasurable hd0
  have hs2 : ∀ x, Real.sqrt (ρ x) ^ 2 = ρ x := fun x => Real.sq_sqrt (hρ x).le
  have hs0 : ∀ x, Real.sqrt (ρ x) ≠ 0 := fun x => ne_of_gt (Real.sqrt_pos.mpr (hρ x))
  have hwi (g : ℝ → ℝ) : (∫ x, g x ∂μ) = ∫ x, ρ x * g x := by
    have ht := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ))
      hdm (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) g
    simpa [μ, smul_eq_mul, ENNReal.toReal_ofReal (hρ _).le] using ht
  have hρle (x : ℝ) : ρ x ≤ c0 := by
    have he : Real.exp (-κ * x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    exact (mul_le_mul_of_nonneg_left he hc0.le).trans_eq (mul_one c0)
  have hsle (x : ℝ) : Real.sqrt (ρ x) ≤ Real.sqrt c0 := Real.sqrt_le_sqrt (hρle x)
  have hsm : Measurable (fun x => Real.sqrt (ρ x)) := hρm.sqrt
  have hmLp (h : Lp ℝ 2 (volume : Measure ℝ)) :
      MemLp (fun x => Real.sqrt (ρ x) * h x) 2 volume := by
    apply ((Lp.memLp h).const_mul (Real.sqrt c0)).mono
      (hsm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable h))
    filter_upwards with x
    change ‖Real.sqrt (ρ x) * h x‖ ≤ ‖Real.sqrt c0 * h x‖
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hsle x) (abs_nonneg _)
  let V (h : Lp ℝ 2 (volume : Measure ℝ)) : Lp ℝ 2 (volume : Measure ℝ) :=
    (hmLp h).toLp (fun x => Real.sqrt (ρ x) * h x)
  have hV (h : Lp ℝ 2 (volume : Measure ℝ)) :
      (fun x => V h x) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * h x) := (hmLp h).coeFn_toLp
  have hVa (h k : Lp ℝ 2 (volume : Measure ℝ)) : V (h+k) = V h + V k := by
    apply Lp.ext
    filter_upwards [hV (h+k), hV h, hV k, Lp.coeFn_add (V h) (V k), Lp.coeFn_add h k]
      with x ha hb hc hd he
    simp only [ha, hd, hb, hc, he, Pi.add_apply, mul_add]
  have hVs (a : ℝ) (h : Lp ℝ 2 (volume : Measure ℝ)) : V (a • h) = a • V h := by
    apply Lp.ext
    filter_upwards [hV (a • h), hV h, Lp.coeFn_smul a (V h), Lp.coeFn_smul a h]
      with x ha hb hc hd
    simp only [ha, hc, hb, hd, Pi.smul_apply, smul_eq_mul]
    ring
  have hVn (h : Lp ℝ 2 (volume : Measure ℝ)) : ‖V h‖ ≤ Real.sqrt c0 * ‖h‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hV h] with x hx
    rw [hx, norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hsle x) (norm_nonneg _)
  let Vₗ : Lp ℝ 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
    { toFun := V, map_add' := hVa, map_smul' := hVs }
  let M := Vₗ.mkContinuous (Real.sqrt c0) hVn
  have hM (h : Lp ℝ 2 (volume : Measure ℝ)) :
      (fun x => M h x) =ᵐ[volume] (fun x => Real.sqrt (ρ x) * h x) := hV h
  have hMn : ‖M‖ ≤ Real.sqrt c0 :=
    M.opNorm_le_bound (Real.sqrt_nonneg _) hVn
  have hconj : U.toLinearIsometry.toContinuousLinearMap.comp
      (T.comp U.symm.toLinearIsometry.toContinuousLinearMap) = M.comp (C.comp M) := by
    apply ContinuousLinearMap.ext
    intro h
    apply Lp.ext
    change (fun x => U (T (U.symm h)) x) =ᵐ[volume] (fun x => M (C (M h)) x)
    filter_upwards [hU (T (U.symm h)), hvol.ae_eq (hT (U.symm h)),
      hM (C (M h)), hC (M h)] with x hu ht hm hc
    rw [hu, ht, hm, hc]
    congr 1
    rw [hwi]
    apply integral_congr_ae
    filter_upwards [hvol.ae_eq (hUinv h), hM h] with y hi hj
    rw [hi, hj]
    change ρ y * (q (x-y) * (h y / Real.sqrt (ρ y))) =
      q (x-y) * (Real.sqrt (ρ y) * h y)
    have hid : ρ y / Real.sqrt (ρ y) = Real.sqrt (ρ y) := by
      apply (div_eq_iff (hs0 y)).mpr
      simpa only [pow_two] using (hs2 y).symm
    calc
      ρ y * (q (x-y) * (h y / Real.sqrt (ρ y))) =
          q (x-y) * h y * (ρ y / Real.sqrt (ρ y)) := by ring
      _ = q (x-y) * (Real.sqrt (ρ y) * h y) := by rw [hid]; ring
  refine ⟨M, hM, hMn, hconj, ?_⟩
  have hn : ‖U.toLinearIsometry.toContinuousLinearMap.comp
      (T.comp U.symm.toLinearIsometry.toContinuousLinearMap)‖ = ‖T‖ := by
    exact (ContinuousLinearMap.opNorm_linearIsometryEquiv_comp U _).trans
      (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv T U.symm)
  calc
    ‖T‖ = ‖M.comp (C.comp M)‖ := by rw [← hconj, hn]
    _ ≤ ‖M‖ * (‖C‖ * ‖M‖) := (M.opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (C.opNorm_comp_le M) (norm_nonneg _))
    _ ≤ Real.sqrt c0 * (‖C‖ * Real.sqrt c0) :=
      mul_le_mul hMn (mul_le_mul_of_nonneg_left hMn (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _)
    _ = c0 * ‖C‖ := by
      calc
        Real.sqrt c0 * (‖C‖ * Real.sqrt c0) = (Real.sqrt c0)^2 * ‖C‖ := by ring
        _ = c0 * ‖C‖ := by rw [Real.sq_sqrt hc0.le]


end D5.S3.Fourier.Asymptotics.CosineCutoffKernel.GaussianWeight
