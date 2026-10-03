/- GID: D5/S3/Arith/AbsoluteValues/Heights/SliceBound
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/SliceBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The slice-bound condition controls integration along a linear subspace. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import D5.S3.Arith.AbsoluteValues.Heights.PrekopaLeindler

public section

open MeasureTheory Measure Set Metric ENNReal
open scoped Real

/-- The **Gauss density** `exp (-π ‖x‖ ^ 2)`, as an `ℝ≥0∞`-valued function. With `π` in the
exponent it is a probability density for every finite-dimensional real inner product space. -/
@[expose] noncomputable def gaussDensity {E : Type*} [NormedAddCommGroup E] (x : E) :
    ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2))

/-- The radius `ρ` of the ball of volume `1`: Bombieri–Gubler's `ρ(n)`, defined by the
normalization it is used for rather than by its closed form. -/
@[expose] noncomputable def unitVolumeRadius (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : ℝ :=
  (volume (ball (0 : E) 1)).toReal ^ (-(1 / (Module.finrank ℝ E : ℝ)))

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

end

end

public section

open MeasureTheory Set

/-- A function `f : E → ℝ≥0∞` on a real vector space is **log-concave** if
`f x ^ a * f y ^ b ≤ f (a • x + b • y)` for all `x`, `y` and all weights `a, b > 0` summing to
`1`; for positive real-valued `f` this says that `log ∘ f` is concave. -/
@[expose] def LogConcave {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ENNReal) : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 → ∀ x y, f x ^ a * f y ^ b ≤ f (a • x + b • y)

end

public section

open MeasureTheory Measure Set Metric ENNReal Pointwise
open scoped Real

variable {E F : Type*}

/-- `HasSliceBound μ g Q` says that the measure with density `g` of a measurable convex symmetric
set `A` never exceeds `μ (A ∩ Q)`. With `g` the Gauss density and `Q` a product of balls of volume
one this is Bombieri–Gubler's Lemma C.3.7. -/
@[expose] def HasSliceBound [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) (g : E → ℝ≥0∞) (Q : Set E) : Prop :=
  ∀ A : Set E, MeasurableSet A → Convex ℝ A → (∀ x ∈ A, -x ∈ A) →
    ∫⁻ x in A, g x ∂μ ≤ μ (A ∩ Q)

/-- **The slice bound upgrades from sets to even log-concave functions.** Writing `f` as a
superposition of the indicators of its superlevel sets — which are convex because `f` is
log-concave and symmetric because `f` is even — turns the bound for sets into a bound for
integrals. -/
theorem HasSliceBound.lintegral_le [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    {μ : Measure E} [SFinite μ] {g : E → ℝ≥0∞} {Q : Set E}
    (hb : HasSliceBound μ g Q) (hg : Measurable g)
    {f : E → ℝ≥0∞} (hf : Measurable f) (hfe : ∀ x, f (-x) = f x) (hflc : LogConcave f) :
    ∫⁻ x, f x * g x ∂μ ≤ ∫⁻ x in Q, f x ∂μ := by
  let nativeSource9 := (open MeasureTheory Set in (fun {E : Type _} [AddCommGroup E] [Module ℝ E] {f : E → ENNReal}
      (hf : LogConcave f) (c : ENNReal) => (show Convex ℝ {x | c < f x} from by
    classical
    intro x hx y hy a b ha hb hab
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by rw [← hab, ← ha0, zero_add]
      simpa [← ha0, hb1] using hy
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · have ha1 : a = 1 := by rw [← hab, ← hb0, add_zero]
      simpa [← hb0, ha1] using hx
    refine (lt_min hx hy).trans_le (le_trans ?_ (hf a b ha0 hb0 hab x y))
    calc Min.min (f x) (f y) = Min.min (f x) (f y) ^ (a + b) := by rw [hab, ENNReal.rpow_one]
      _ = Min.min (f x) (f y) ^ a * Min.min (f x) (f y) ^ b :=
          ENNReal.rpow_add_of_nonneg a b ha0.le hb0.le
      _ ≤ f x ^ a * f y ^ b :=
          mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) ha0.le)
            (ENNReal.rpow_le_rpow (min_le_right _ _) hb0.le))))
  have hK : ∀ t : ℝ, MeasurableSet {x : E | ENNReal.ofReal t < f x} := fun t =>
    measurableSet_lt measurable_const hf
  calc ∫⁻ x, f x * g x ∂μ = ∫⁻ x, f x ∂(μ.withDensity g) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hg hf]
        exact lintegral_congr fun x => mul_comm _ _
    _ = ∫⁻ t in Ioi (0 : ℝ), (μ.withDensity g) {x | ENNReal.ofReal t < f x} :=
        lintegral_eq_lintegral_measure_ofReal_lt _ hf
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x in {x | ENNReal.ofReal t < f x}, g x ∂μ :=
        lintegral_congr fun t => withDensity_apply g (hK t)
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), μ ({x | ENNReal.ofReal t < f x} ∩ Q) :=
        lintegral_mono fun t => hb _ (hK t) ((nativeSource9 hflc) _)
          (fun x hx => by change ENNReal.ofReal t < f (-x); rw [hfe x]; exact hx)
    _ = ∫⁻ t in Ioi (0 : ℝ), (μ.restrict Q) {x | ENNReal.ofReal t < f x} :=
        lintegral_congr fun t => (Measure.restrict_apply (hK t)).symm
    _ = ∫⁻ x, f x ∂(μ.restrict Q) := (lintegral_eq_lintegral_measure_ofReal_lt _ hf).symm

/-- **The base case of Bombieri–Gubler's Lemma C.3.7**, stated for an arbitrary norm: if the Gauss
density has total mass one and the closed ball of radius `ρ` has measure one, then the Gauss
measure of a measurable convex symmetric set is at most its measure inside that ball. -/
theorem hasSliceBound_closedBall [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {ρ : ℝ} (hρ : 0 < ρ) (hball : μ (closedBall 0 ρ) = 1)
    (hgauss : ∫⁻ x, gaussDensity x ∂μ = 1) :
    HasSliceBound μ gaussDensity (closedBall (0 : E) ρ) := by
  let nativeSource154 := (open MeasureTheory Measure Set Metric ENNReal in (open scoped Real in (fun {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
      (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] (f : E → ℝ≥0∞) => (show ∫⁻ x, f x ∂μ =
        ∫⁻ p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ), f ((p.2 : ℝ) • (p.1 : E))
          ∂(μ.toSphere.prod (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ E - 1))) from by
    classical
    have h1 : ∫⁻ x, f x ∂μ = ∫⁻ x : ({(0 : E)}ᶜ : Set E), f x.1 ∂(μ.comap (↑)) := by
      rw [MeasureTheory.lintegral_subtype_comap (MeasurableSingletonClass.measurableSet_singleton _).compl, MeasureTheory.restrict_compl_singleton]
    rw [h1, ← (μ.measurePreserving_homeomorphUnitSphereProd).lintegral_comp_emb
        (Homeomorph.measurableEmbedding _) (fun p => f ((p.2 : ℝ) • (p.1 : E)))]
    refine MeasureTheory.lintegral_congr fun x => ?_
    have hx : (x : E) ≠ 0 := x.2
    have hn : (0 : ℝ) < ‖(x : E)‖ := by simpa using hx
    rw [homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe, smul_smul,
      mul_inv_cancel₀ hn.ne', one_smul]))))
  let nativeSource155 := (open MeasureTheory Measure Set Metric ENNReal in (open scoped Real in (fun {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
      (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ≥0∞} (hf : Measurable f) => (show ∫⁻ x, f x ∂μ =
        ∫⁻ u : Metric.sphere (0 : E) 1, ∫⁻ r : Set.Ioi (0 : ℝ), f ((r : ℝ) • (u : E))
          ∂(MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere from by
    classical
    rw [nativeSource154 μ f, MeasureTheory.lintegral_prod]
    exact (hf.comp (by fun_prop)).aemeasurable))))
  rcases subsingleton_or_nontrivial E with hE | hE
  · intro A hA _ _
    have hcb : closedBall (0 : E) ρ = univ := by
      ext x; simp [Subsingleton.elim x (0 : E), hρ.le]
    have hg : ∀ x : E, gaussDensity x = 1 := fun x => by
      rw [Subsingleton.elim x (0 : E), show gaussDensity (0 : E) = 1 from by simp [gaussDensity]]
    simp [hg, hcb]
  intro A hA hAconv hAsymm
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  have h0 : (0 : E) ∈ A := by
    have := hAconv ha (hAsymm a ha) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using this
  set n := Module.finrank ℝ E with hn
  set W := Measure.volumeIoiPow (n - 1) with hW
  set c : ℝ≥0∞ := ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-π * (r : ℝ) ^ 2)) ∂W with hcdef
  set d : ℝ≥0∞ := W {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} with hddef
  have hnorm : ∀ (u : sphere (0 : E) 1) (r : Ioi (0 : ℝ)), ‖(r : ℝ) • (u : E)‖ = (r : ℝ) := by
    intro u r
    rw [norm_smul, mem_sphere_zero_iff_norm.mp u.2, mul_one, Real.norm_eq_abs, abs_of_pos r.2]
  have hgsmul : ∀ (u : sphere (0 : E) 1) (r : Ioi (0 : ℝ)),
      gaussDensity ((r : ℝ) • (u : E)) = ENNReal.ofReal (Real.exp (-π * (r : ℝ) ^ 2)) := by
    intro u r; rw [gaussDensity, hnorm]
  have hSne : μ.toSphere univ ≠ 0 := by
    simp only [ne_eq, measure_univ_eq_zero]
    exact Measure.toSphere_ne_zero μ
  have hStop : μ.toSphere univ ≠ ⊤ := measure_ne_top _ _
  have hdmeas : MeasurableSet {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} :=
    measurable_subtype_coe measurableSet_Iic
  have claim1 : μ.toSphere univ * c = 1 := by
    rw [← hgauss, nativeSource155 μ (f := gaussDensity) (by unfold gaussDensity; fun_prop),
      show (fun u : sphere (0 : E) 1 => ∫⁻ r : Ioi (0 : ℝ), gaussDensity ((r : ℝ) • (u : E)) ∂W)
        = fun _ => c from funext fun u => lintegral_congr fun r => hgsmul u r,
      lintegral_const, mul_comm]
  have hcbmem : ∀ (u : sphere (0 : E) 1) (r : Ioi (0 : ℝ)),
      ((r : ℝ) • (u : E) ∈ closedBall (0 : E) ρ) ↔ (r : ℝ) ≤ ρ := by
    intro u r; rw [mem_closedBall, dist_zero_right, hnorm]
  have hd1 : ∀ u : sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ),
      Set.indicator (closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) ((r : ℝ) • (u : E)) ∂W = d := by
    intro u
    have he : (fun r : Ioi (0 : ℝ) =>
        Set.indicator (closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) ((r : ℝ) • (u : E)))
        = Set.indicator {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} (fun _ => (1 : ℝ≥0∞)) := by
      funext r
      by_cases h : (r : ℝ) ≤ ρ
      · rw [Set.indicator_of_mem ((hcbmem u r).mpr h),
          Set.indicator_of_mem (show r ∈ {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} from h)]
      · rw [Set.indicator_of_notMem (fun hm => h ((hcbmem u r).mp hm)),
          Set.indicator_of_notMem (show r ∉ {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} from h)]
    rw [he, lintegral_indicator hdmeas, setLIntegral_one, hddef]
  have claim2 : μ.toSphere univ * d = 1 := by
    rw [← hball]
    have h1 : μ (closedBall (0 : E) ρ)
        = ∫⁻ x, Set.indicator (closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
      rw [lintegral_indicator measurableSet_closedBall, setLIntegral_one]
    rw [h1, nativeSource155 μ
      (f := Set.indicator (closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)))
      (measurable_one.indicator measurableSet_closedBall),
      show (fun u : sphere (0 : E) 1 => ∫⁻ r : Ioi (0 : ℝ),
        Set.indicator (closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) ((r : ℝ) • (u : E)) ∂W)
        = fun _ => d from funext hd1, lintegral_const, mul_comm]
  have hcd : c = d := (ENNReal.mul_right_inj hSne hStop).mp (claim1.trans claim2.symm)
  have key : ∀ u : sphere (0 : E) 1,
      ∫⁻ r : Ioi (0 : ℝ), Set.indicator A gaussDensity ((r : ℝ) • (u : E)) ∂W ≤
      ∫⁻ r : Ioi (0 : ℝ),
        Set.indicator (A ∩ closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) ((r : ℝ) • (u : E)) ∂W := by
    intro u
    by_cases hc : (ρ • (u : E)) ∈ A
    · have hsub : ∀ t : ℝ, 0 < t → t ≤ ρ → (t • (u : E)) ∈ A := by
        intro t ht htρ
        have h1 : (0 : ℝ) ≤ t / ρ := by positivity
        have h2 : (0 : ℝ) ≤ 1 - t / ρ := by
          have : t / ρ ≤ 1 := (div_le_one hρ).mpr htρ
          linarith
        have := hAconv hc h0 h1 h2 (by ring)
        simpa [smul_smul, div_mul_cancel₀ _ hρ.ne'] using this
      have hle : ∫⁻ r : Ioi (0 : ℝ), Set.indicator A gaussDensity ((r : ℝ) • (u : E)) ∂W ≤ c :=
        lintegral_mono fun r => (Set.indicator_le_self _ _ _).trans (hgsmul u r).le
      refine hle.trans ?_
      rw [hcd, hddef, ← setLIntegral_one, ← lintegral_indicator hdmeas]
      refine lintegral_mono fun r => ?_
      by_cases hr : (r : ℝ) ≤ ρ
      · rw [Set.indicator_of_mem (show r ∈ {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} from hr),
          Set.indicator_of_mem (show ((r : ℝ) • (u : E)) ∈ A ∩ closedBall (0 : E) ρ from
            ⟨hsub r r.2 hr, (hcbmem u r).mpr hr⟩)]
      · rw [Set.indicator_of_notMem (show r ∉ {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} from hr)]
        exact zero_le
    · refine lintegral_mono fun r => ?_
      have hr0 : (0 : ℝ) < (r : ℝ) := r.2
      by_cases hmem : ((r : ℝ) • (u : E)) ∈ A
      · have hr : (r : ℝ) ≤ ρ := by
          by_contra hgt
          refine hc ?_
          have hgt' : ρ < (r : ℝ) := not_le.mp hgt
          have h1 : (0 : ℝ) ≤ ρ / (r : ℝ) := le_of_lt (div_pos hρ hr0)
          have h2 : (0 : ℝ) ≤ 1 - ρ / (r : ℝ) := by
            have : ρ / (r : ℝ) ≤ 1 := (div_le_one hr0).mpr hgt'.le
            linarith
          have := hAconv hmem h0 h1 h2 (by ring)
          simpa [smul_smul, div_mul_cancel₀ _ hr0.ne'] using this
        rw [Set.indicator_of_mem hmem,
          Set.indicator_of_mem (show ((r : ℝ) • (u : E)) ∈ A ∩ closedBall (0 : E) ρ from
            ⟨hmem, (hcbmem u r).mpr hr⟩)]
        exact (fun {E : Type _} [instN : NormedAddCommGroup E] (x : E) =>
    (show gaussDensity x ≤ 1 from by
      rw [gaussDensity, ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, sq_nonneg ‖x‖])) _
      · rw [Set.indicator_of_notMem hmem]; exact zero_le
  calc ∫⁻ x in A, gaussDensity x ∂μ
      = ∫⁻ x, Set.indicator A gaussDensity x ∂μ := (lintegral_indicator hA _).symm
    _ = ∫⁻ u : sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ),
          Set.indicator A gaussDensity ((r : ℝ) • (u : E)) ∂W ∂μ.toSphere :=
        nativeSource155 μ ((fun {E : Type _} [instN : NormedAddCommGroup E] [instM : MeasurableSpace E]
      [instO : OpensMeasurableSpace E] =>
    (show Measurable (gaussDensity : E → ℝ≥0∞) from by unfold gaussDensity; fun_prop)).indicator hA)
    _ ≤ ∫⁻ u : sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ),
          Set.indicator (A ∩ closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) ((r : ℝ) • (u : E)) ∂W
          ∂μ.toSphere := lintegral_mono key
    _ = ∫⁻ x, Set.indicator (A ∩ closedBall (0 : E) ρ) (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
        (nativeSource155 μ
          (measurable_one.indicator (hA.inter measurableSet_closedBall))).symm
    _ = μ (A ∩ closedBall (0 : E) ρ) := by
        rw [lintegral_indicator (hA.inter measurableSet_closedBall), setLIntegral_one]

/-- **Bombieri–Gubler's Lemma C.3.7 for a single block**: the Gauss measure of a measurable convex
symmetric set is at most its volume inside the ball of volume one. -/
theorem hasSliceBound_unitVolumeBall [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    HasSliceBound (volume : Measure E) gaussDensity (closedBall (0 : E) (unitVolumeRadius E)) := by
  let nativeSource156 := (open MeasureTheory Measure Set Metric ENNReal in (open scoped Real in (fun (ι : Type _) [Fintype ι] => (show ∫⁻ y : ι → ℝ, ENNReal.ofReal (Real.exp (-π * ∑ i, (y i) ^ 2)) = 1 from by
    classical
    have hprod : ∀ y : ι → ℝ, Real.exp (-π * ∑ i, (y i) ^ 2) = ∏ i, Real.exp (-π * (y i) ^ 2) := by
      intro y
      rw [← Real.exp_sum, Finset.mul_sum]
    have hint : MeasureTheory.Integrable (fun y : ι → ℝ => ∏ i, Real.exp (-π * (y i) ^ 2)) :=
      MeasureTheory.Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq Real.pi_pos)
    have hone : (∫ t : ℝ, Real.exp (-π * t ^ 2)) = 1 := by
      rw [integral_gaussian, div_self Real.pi_ne_zero, Real.sqrt_one]
    have hval : ∫ y : ι → ℝ, ∏ i, Real.exp (-π * (y i) ^ 2) = 1 := by
      rw [MeasureTheory.integral_fintype_prod_volume_eq_pow (fun t : ℝ => Real.exp (-π * t ^ 2)), hone, one_pow]
    calc ∫⁻ y : ι → ℝ, ENNReal.ofReal (Real.exp (-π * ∑ i, (y i) ^ 2))
        = ∫⁻ y : ι → ℝ, ENNReal.ofReal (∏ i, Real.exp (-π * (y i) ^ 2)) :=
          MeasureTheory.lintegral_congr fun y => by rw [hprod]
      _ = ENNReal.ofReal (∫ y : ι → ℝ, ∏ i, Real.exp (-π * (y i) ^ 2)) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (.of_forall fun _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)).symm
      _ = 1 := by rw [hval, ENNReal.ofReal_one]))))
  let nativeSource157 := (open MeasureTheory Measure Set Metric ENNReal in (open scoped Real in (fun (ι : Type _) [Fintype ι] => (show ∫⁻ x : EuclideanSpace ℝ ι, gaussDensity x = 1 from by
    classical
    have hm : Measurable fun y : ι → ℝ => ENNReal.ofReal (Real.exp (-π * ∑ i, (y i) ^ 2)) := by
      fun_prop
    rw [← nativeSource156 ι, ← (PiLp.volume_preserving_ofLp ι).lintegral_comp hm]
    refine MeasureTheory.lintegral_congr fun x => ?_
    rw [gaussDensity, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp))))
  let nativeSource158 := (open MeasureTheory Measure Set Metric ENNReal in (open scoped Real in (show ∫⁻ x : E, gaussDensity x = 1 from by
    classical
    have hm : Measurable (gaussDensity : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ≥0∞) := by
      unfold gaussDensity; fun_prop
    rw [← nativeSource157 (Fin (Module.finrank ℝ E)),
      ← (stdOrthonormalBasis ℝ E).measurePreserving_repr.lintegral_comp hm]
    exact MeasureTheory.lintegral_congr fun x => by
      rw [gaussDensity, gaussDensity, (stdOrthonormalBasis ℝ E).repr.norm_map])))
  let nativeSource160 := (open MeasureTheory Measure Set Metric ENNReal in (open scoped Real in (show MeasureTheory.MeasureSpace.volume (Metric.closedBall (0 : E) (unitVolumeRadius E)) = 1 from by
    classical
    rcases subsingleton_or_nontrivial E with hE | hE
    · have h1 : Metric.closedBall (0 : E) (unitVolumeRadius E) = Set.univ := by
        ext x
        simp only [Metric.mem_closedBall, Set.mem_univ, iff_true]
        rw [hE.elim x (0 : E), dist_self]
        exact (Real.rpow_pos_of_pos (ENNReal.toReal_pos
          (Metric.measure_ball_pos (volume : Measure E) (0 : E) one_pos).ne'
          measure_ball_lt_top.ne) _).le
      have hg : ∀ x : E, gaussDensity x = 1 := fun x => by
        rw [Subsingleton.elim x (0 : E), show gaussDensity (0 : E) = 1 from by simp [gaussDensity]]
      calc MeasureTheory.MeasureSpace.volume (Metric.closedBall (0 : E) (unitVolumeRadius E)) = ∫⁻ _ : E, 1 := by
            rw [MeasureTheory.lintegral_one, h1]
        _ = ∫⁻ x : E, gaussDensity x := MeasureTheory.lintegral_congr fun x => (hg x).symm
        _ = 1 := nativeSource158
    have hv : 0 < (MeasureTheory.MeasureSpace.volume (Metric.ball (0 : E) 1)).toReal := (show 0 < (MeasureTheory.MeasureSpace.volume (Metric.ball (0 : E) 1)).toReal from ENNReal.toReal_pos
        (Metric.measure_ball_pos (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure E) (0 : E) one_pos).ne' measure_ball_lt_top.ne)
    have hn : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
    rw [MeasureTheory.Measure.addHaar_closedBall MeasureTheory.MeasureSpace.volume 0 (show 0 < unitVolumeRadius E from Real.rpow_pos_of_pos (ENNReal.toReal_pos
        (Metric.measure_ball_pos (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure E) (0 : E) one_pos).ne' measure_ball_lt_top.ne) _).le, unitVolumeRadius,
      ← Real.rpow_natCast ((MeasureTheory.MeasureSpace.volume (Metric.ball (0 : E) 1)).toReal ^ (-(1 / (Module.finrank ℝ E : ℝ))))
        (Module.finrank ℝ E),
      ← Real.rpow_mul hv.le,
      show -(1 / (Module.finrank ℝ E : ℝ)) * (Module.finrank ℝ E : ℝ) = -1 by field_simp,
      Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos hv,
      ENNReal.ofReal_toReal measure_ball_lt_top.ne,
      ENNReal.inv_mul_cancel (Metric.measure_ball_pos MeasureTheory.MeasureSpace.volume 0 one_pos).ne' measure_ball_lt_top.ne])))
  exact hasSliceBound_closedBall volume (show 0 < unitVolumeRadius E from Real.rpow_pos_of_pos (ENNReal.toReal_pos
        (measure_ball_pos (volume : Measure E) (0 : E) one_pos).ne' measure_ball_lt_top.ne) _) nativeSource160
      nativeSource158
/-- **The induction step of Bombieri–Gubler's Lemma C.3.7.** If the slice bound holds in each
factor, for densities that are log-concave and even, then it holds for the product measure, the
product density and the product of the two sets. -/
theorem HasSliceBound.prod
    [MeasurableSpace E] [AddCommGroup E] [Module ℝ E] [MeasurableNeg E]
    [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] [MeasurableNeg F]
    {μ : Measure E} {ν : Measure F} [SFinite μ] [SFinite ν]
    [μ.IsNegInvariant] [ν.IsNegInvariant]
    {g : E → ℝ≥0∞} {h : F → ℝ≥0∞} {Q : Set E} {R : Set F}
    (hg : Measurable g) (hge : ∀ x, g (-x) = g x) (hglc : LogConcave g)
    (hh : Measurable h) (hR : MeasurableSet R)
    (hRc : Convex ℝ R) (hRs : ∀ z ∈ R, -z ∈ R)
    (hPLμ : HasPrekopaLeindler μ) (hPLν : HasPrekopaLeindler ν)
    (hE : HasSliceBound μ g Q) (hF : HasSliceBound ν h R) :
    HasSliceBound (μ.prod ν) (fun p => g p.1 * h p.2) (Q ×ˢ R) := by
  let nativeSource9 := (open MeasureTheory Set in (fun {E : Type _} [AddCommGroup E] [Module ℝ E] {f : E → ENNReal}
      (hf : LogConcave f) (c : ENNReal) => (show Convex ℝ {x | c < f x} from by
    classical
    intro x hx y hy a b ha hb hab
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by rw [← hab, ← ha0, zero_add]
      simpa [← ha0, hb1] using hy
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · have ha1 : a = 1 := by rw [← hab, ← hb0, add_zero]
      simpa [← hb0, ha1] using hx
    refine (lt_min hx hy).trans_le (le_trans ?_ (hf a b ha0 hb0 hab x y))
    calc Min.min (f x) (f y) = Min.min (f x) (f y) ^ (a + b) := by rw [hab, ENNReal.rpow_one]
      _ = Min.min (f x) (f y) ^ a * Min.min (f x) (f y) ^ b :=
          ENNReal.rpow_add_of_nonneg a b ha0.le hb0.le
      _ ≤ f x ^ a * f y ^ b :=
          mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) ha0.le)
            (ENNReal.rpow_le_rpow (min_le_right _ _) hb0.le))))
  let nativeSource11 := (open MeasureTheory Set in (fun   
          {ν : MeasureTheory.Measure F}
      (hF : HasPrekopaLeindler ν) {f : E × F → ENNReal} (hf : Measurable f) (hlc : LogConcave f)
      {A : Set F} (hA : MeasurableSet A) (hAc : Convex ℝ A) => (show LogConcave fun x => ∫⁻ y in A, f (x, y) ∂ν from by
    classical
    intro a b ha hb hab x₁ x₂
    have hind : ∀ x : E, (∫⁻ y in A, f (x, y) ∂ν)
        = ∫⁻ y, Set.indicator A (fun y => f (x, y)) y ∂ν :=
      fun x => (MeasureTheory.lintegral_indicator hA _).symm
    have hmeas : ∀ x : E, Measurable (Set.indicator A fun y => f (x, y)) :=
      fun x => (hf.comp measurable_prodMk_left).indicator hA
    simp only [hind]
    refine hF a b ha hb hab _ _ _ (hmeas x₁) (hmeas x₂) (hmeas (a • x₁ + b • x₂)) fun y₁ y₂ => ?_
    by_cases hy₁ : y₁ ∈ A
    · by_cases hy₂ : y₂ ∈ A
      · rw [Set.indicator_of_mem hy₁, Set.indicator_of_mem hy₂,
          Set.indicator_of_mem (hAc hy₁ hy₂ ha.le hb.le hab)]
        exact hlc a b ha hb hab (x₁, y₁) (x₂, y₂)
      · simp [Set.indicator_of_notMem hy₂, ENNReal.zero_rpow_of_pos hb]
    · simp [Set.indicator_of_notMem hy₁, ENNReal.zero_rpow_of_pos ha])))
  let nativeSource11Swap := (open MeasureTheory Set in (fun   
          {ν : MeasureTheory.Measure E}
      (hF : HasPrekopaLeindler ν) {f : F × E → ENNReal} (hf : Measurable f) (hlc : LogConcave f)
      {A : Set E} (hA : MeasurableSet A) (hAc : Convex ℝ A) => (show LogConcave fun x => ∫⁻ y in A, f (x, y) ∂ν from by
    classical
    intro a b ha hb hab x₁ x₂
    have hind : ∀ x : F, (∫⁻ y in A, f (x, y) ∂ν)
        = ∫⁻ y, Set.indicator A (fun y => f (x, y)) y ∂ν :=
      fun x => (MeasureTheory.lintegral_indicator hA _).symm
    have hmeas : ∀ x : F, Measurable (Set.indicator A fun y => f (x, y)) :=
      fun x => (hf.comp measurable_prodMk_left).indicator hA
    simp only [hind]
    refine hF a b ha hb hab _ _ _ (hmeas x₁) (hmeas x₂) (hmeas (a • x₁ + b • x₂)) fun y₁ y₂ => ?_
    by_cases hy₁ : y₁ ∈ A
    · by_cases hy₂ : y₂ ∈ A
      · rw [Set.indicator_of_mem hy₁, Set.indicator_of_mem hy₂,
          Set.indicator_of_mem (hAc hy₁ hy₂ ha.le hb.le hab)]
        exact hlc a b ha hb hab (x₁, y₁) (x₂, y₂)
      · simp [Set.indicator_of_notMem hy₂, ENNReal.zero_rpow_of_pos hb]
    · simp [Set.indicator_of_notMem hy₁, ENNReal.zero_rpow_of_pos ha])))
  let nativeSource159 := (open MeasureTheory Set in (fun {E : Type _} [AddCommGroup E] [Module ℝ E] {s : Set E}
      (hs : Convex ℝ s) (c : ENNReal) => (show LogConcave (Set.indicator s (fun _ => c)) from by
    classical
    intro a b ha hb hab x y
    by_cases hx : x ∈ s
    · by_cases hy : y ∈ s
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
          Set.indicator_of_mem (hs hx hy ha.le hb.le hab),
          ← ENNReal.rpow_add_of_nonneg a b ha.le hb.le, hab, ENNReal.rpow_one]
      · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hb]
    · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ha])))
  intro A hA hAconv hAsymm
  set K : ℝ → Set E := fun s => {y | ENNReal.ofReal s < g y} with hKdef
  have hKmeas : ∀ s, MeasurableSet (K s) := fun s => measurableSet_lt measurable_const hg
  have hKconv : ∀ s, Convex ℝ (K s) := fun s => (nativeSource9 hglc) _
  have hKsymm : ∀ s, ∀ y ∈ K s, -y ∈ K s := fun s y hy => by
    change ENNReal.ofReal s < g (-y); rw [hge y]; exact hy
  have hAsecE : ∀ z : F, MeasurableSet {y : E | (y, z) ∈ A} := fun z => hA.preimage (by fun_prop)
  have hAsecF : ∀ y : E, MeasurableSet {z : F | (y, z) ∈ A} := fun y => hA.preimage (by fun_prop)
  have hnegE : ∀ z : F, {y : E | (y, -z) ∈ A} = -{y : E | (y, z) ∈ A} := fun z => by
    ext y
    simp only [Set.mem_neg, Set.mem_ofPred_eq]
    exact ⟨fun hy => by simpa using hAsymm _ hy, fun hy => by simpa using hAsymm _ hy⟩
  have hnegF : ∀ y : E, {z : F | (-y, z) ∈ A} = -{z : F | (y, z) ∈ A} := fun y => by
    ext z
    simp only [Set.mem_neg, Set.mem_ofPred_eq]
    exact ⟨fun hz => by simpa using hAsymm _ hz, fun hz => by simpa using hAsymm _ hz⟩
  have hRneg : (-R : Set F) = R := by
    ext x
    simp only [Set.mem_neg]
    exact ⟨fun hx ↦ by simpa using hRs _ hx, fun hx ↦ hRs x hx⟩
  have hKneg : ∀ s, (-(K s) : Set E) = K s := fun s ↦ by
    ext x
    simp only [Set.mem_neg]
    exact ⟨fun hx ↦ by simpa using hKsymm s _ hx, fun hx ↦ hKsymm s x hx⟩
  set f : E → ℝ≥0∞ := fun y => (ν.restrict R) {z | (y, z) ∈ A} with hfdef
  set θ : ℝ → F → ℝ≥0∞ := fun s z => (μ.restrict (K s)) {y | (y, z) ∈ A} with hθdef
  have hfmeas : Measurable f := measurable_measure_prodMk_left hA
  have hθmeas : ∀ s, Measurable (θ s) := fun s => measurable_measure_prodMk_right hA
  have hΘmeas : Measurable fun p : F × ℝ => θ p.2 p.1 := by
    have hS : MeasurableSet {q : E × (F × ℝ) |
        ENNReal.ofReal q.2.2 < g q.1 ∧ (q.1, q.2.1) ∈ A} :=
      (measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_snd.comp measurable_snd))
        (hg.comp measurable_fst)).inter (hA.preimage (by fun_prop))
    have heq : (fun p : F × ℝ => θ p.2 p.1)
        = fun p : F × ℝ => μ ((fun y => (y, p)) ⁻¹'
          {q : E × (F × ℝ) | ENNReal.ofReal q.2.2 < g q.1 ∧ (q.1, q.2.1) ∈ A}) := by
      funext p
      rw [hθdef]
      simp only
      rw [Measure.restrict_apply' (hKmeas p.2)]
      congr 1
      ext y
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    rw [heq]
    exact measurable_measure_prodMk_right hS
  have hfeven : ∀ y, f (-y) = f y := fun y => by
    rw [hfdef]
    simp only
    rw [hnegF y, Measure.restrict_apply (hAsecF y).neg, Measure.restrict_apply (hAsecF y),
      show (-{z : F | (y, z) ∈ A} ∩ R) = -({z : F | (y, z) ∈ A} ∩ R) by
        rw [inter_neg, hRneg], measure_neg]
  have hθeven : ∀ s z, θ s (-z) = θ s z := fun s z => by
    rw [hθdef]
    simp only
    rw [hnegE z, Measure.restrict_apply' (hKmeas s), Measure.restrict_apply' (hKmeas s),
      show (-{y : E | (y, z) ∈ A} ∩ K s) = -({y : E | (y, z) ∈ A} ∩ K s) by
        rw [inter_neg, hKneg], measure_neg]
  have hindA : LogConcave (Set.indicator A (fun _ => (1 : ℝ≥0∞))) := nativeSource159 hAconv 1
  have hindAmeas : Measurable (Set.indicator A (fun _ => (1 : ℝ≥0∞))) := measurable_one.indicator hA
  have hfeq : (fun y => ∫⁻ z in R, Set.indicator A (fun _ => (1 : ℝ≥0∞)) (y, z) ∂ν) = f := by
    funext y
    rw [show (fun z => Set.indicator A (fun _ => (1 : ℝ≥0∞)) (y, z))
        = Set.indicator {z | (y, z) ∈ A} (fun _ => (1 : ℝ≥0∞)) from rfl,
      lintegral_indicator (hAsecF y), setLIntegral_one, hfdef]
  have hflc : LogConcave f :=
    hfeq ▸ nativeSource11 hPLν hindAmeas hindA hR hRc
  have hAswapconv : Convex ℝ {q : F × E | (q.2, q.1) ∈ A} :=
    fun _ h1 _ h2 _ _ ha hb hab => hAconv h1 h2 ha hb hab
  have hindA' : LogConcave (Set.indicator {q : F × E | (q.2, q.1) ∈ A} (fun _ => (1 : ℝ≥0∞))) :=
    nativeSource159 hAswapconv 1
  have hindA'meas :
      Measurable (Set.indicator {q : F × E | (q.2, q.1) ∈ A} (fun _ => (1 : ℝ≥0∞))) :=
    measurable_one.indicator (hA.preimage (by fun_prop))
  have hθlc : ∀ s, LogConcave (θ s) := fun s => by
    have heq : (fun z => ∫⁻ y in K s,
        Set.indicator {q : F × E | (q.2, q.1) ∈ A} (fun _ => (1 : ℝ≥0∞)) (z, y) ∂μ) = θ s := by
      funext z
      rw [show (fun y => Set.indicator {q : F × E | (q.2, q.1) ∈ A} (fun _ => (1 : ℝ≥0∞)) (z, y))
          = Set.indicator {y | (y, z) ∈ A} (fun _ => (1 : ℝ≥0∞)) from rfl,
        lintegral_indicator (hAsecE z), setLIntegral_one, hθdef]
    exact heq ▸ nativeSource11Swap hPLμ hindA'meas hindA' (hKmeas s) (hKconv s)
  have hlayer : ∀ S : Set E, MeasurableSet S →
      ∫⁻ y in S, g y ∂μ = ∫⁻ s in Ioi (0 : ℝ), (μ.restrict (K s)) S := by
    intro S _
    rw [lintegral_eq_lintegral_measure_ofReal_lt (μ.restrict S) hg]
    refine lintegral_congr fun s => ?_
    rw [Measure.restrict_apply (hKmeas s), Measure.restrict_apply' (hKmeas s), Set.inter_comm]
  have hW1 : Measurable (Set.indicator A (fun p : E × F => g p.1 * h p.2)) :=
    ((hg.comp measurable_fst).mul (hh.comp measurable_snd)).indicator hA
  have hW2 : Measurable (Set.indicator A (fun p : E × F => g p.1)) :=
    (hg.comp measurable_fst).indicator hA
  have hθs : ∀ z, Measurable fun s => θ s z := fun _ => hΘmeas.comp measurable_prodMk_left
  calc ∫⁻ x in A, g x.1 * h x.2 ∂(μ.prod ν)
      = ∫⁻ z, (∫⁻ y in {y | (y, z) ∈ A}, g y ∂μ) * h z ∂ν := by
        rw [← lintegral_indicator hA, lintegral_prod _ hW1.aemeasurable,
          lintegral_lintegral_swap
            (f := fun (y : E) (z : F) =>
              Set.indicator A (fun p : E × F => g p.1 * h p.2) (y, z)) hW1.aemeasurable]
        refine lintegral_congr fun z => ?_
        rw [show (fun y => Set.indicator A (fun p : E × F => g p.1 * h p.2) (y, z))
            = Set.indicator {y | (y, z) ∈ A} (fun y => g y * h z) from rfl,
          lintegral_indicator (hAsecE z), lintegral_mul_const _ hg]
    _ = ∫⁻ z, (∫⁻ s in Ioi (0 : ℝ), θ s z * h z) ∂ν := by
        refine lintegral_congr fun z => ?_
        rw [hlayer _ (hAsecE z), ← lintegral_mul_const _ (hθs z)]
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ z, θ s z * h z ∂ν :=
        lintegral_lintegral_swap (f := fun (z : F) (s : ℝ) => θ s z * h z)
          (hΘmeas.mul (hh.comp measurable_fst)).aemeasurable
    _ ≤ ∫⁻ s in Ioi (0 : ℝ), ∫⁻ z in R, θ s z ∂ν :=
        lintegral_mono fun s => hF.lintegral_le hh (hθmeas s) (hθeven s) (hθlc s)
    _ = ∫⁻ z in R, (∫⁻ s in Ioi (0 : ℝ), θ s z) ∂ν :=
        lintegral_lintegral_swap (f := fun (s : ℝ) (z : F) => θ s z)
          (hΘmeas.comp measurable_swap).aemeasurable
    _ = ∫⁻ z in R, (∫⁻ y in {y | (y, z) ∈ A}, g y ∂μ) ∂ν :=
        lintegral_congr fun z => (hlayer _ (hAsecE z)).symm
    _ = ∫⁻ y, f y * g y ∂μ := by
        have h1 : ∀ z : F, ∫⁻ y in {y | (y, z) ∈ A}, g y ∂μ
            = ∫⁻ y, Set.indicator A (fun p : E × F => g p.1) (y, z) ∂μ := by
          intro z
          rw [show (fun y => Set.indicator A (fun p : E × F => g p.1) (y, z))
              = Set.indicator {y | (y, z) ∈ A} (fun y => g y) from rfl,
            lintegral_indicator (hAsecE z)]
        simp only [h1]
        rw [lintegral_lintegral_swap (μ := ν.restrict R) (ν := μ)
          (f := fun z y => Set.indicator A (fun p : E × F => g p.1) (y, z))
          (hW2.comp measurable_swap).aemeasurable]
        refine lintegral_congr fun y => ?_
        rw [show (fun z => Set.indicator A (fun p : E × F => g p.1) (y, z))
            = Set.indicator {z | (y, z) ∈ A} (fun _ => g y) from rfl,
          lintegral_indicator (hAsecF y), setLIntegral_const, hfdef, mul_comm]
    _ ≤ ∫⁻ y in Q, f y ∂μ := hE.lintegral_le hg hfmeas hfeven hflc
    _ = (μ.prod ν) (A ∩ (Q ×ˢ R)) := by
        rw [← Measure.restrict_apply hA, ← Measure.prod_restrict, Measure.prod_apply hA]
        rfl

/-- The slice bound transports along a measure-preserving linear equivalence. -/
theorem HasSliceBound.of_measurePreserving [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] {μ : Measure E} {ν : Measure F}
    (e : E ≃ₗ[ℝ] F) (he : MeasurePreserving e μ ν) (hsymm : Measurable e.symm)
    {g : F → ℝ≥0∞} (hg : Measurable g) {Q : Set F} (hQ : MeasurableSet Q)
    (hb : HasSliceBound ν g Q) :
    HasSliceBound μ (fun x => g (e x)) (e ⁻¹' Q) := by
  intro A hA hAconv hAsymm
  have hBA : e ⁻¹' (e.symm ⁻¹' A) = A := by ext x; simp
  have hBmeas : MeasurableSet (e.symm ⁻¹' A) := hsymm hA
  have hBconv : Convex ℝ (e.symm ⁻¹' A) := hAconv.linear_preimage (e.symm : F →ₗ[ℝ] E)
  have hBsymm : ∀ y ∈ e.symm ⁻¹' A, -y ∈ e.symm ⁻¹' A := by
    intro y hy
    have : e.symm (-y) = -(e.symm y) := map_neg _ _
    simpa [Set.mem_preimage, this] using hAsymm _ hy
  have h1 : ∫⁻ x in A, g (e x) ∂μ = ∫⁻ y in e.symm ⁻¹' A, g y ∂ν := by
    rw [← lintegral_indicator hBmeas, ← he.lintegral_comp (hg.indicator hBmeas),
      ← lintegral_indicator hA]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem (show e x ∈ e.symm ⁻¹' A by simpa using hx)]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (show e x ∉ e.symm ⁻¹' A by simpa using hx)]
  have h2 : μ (A ∩ e ⁻¹' Q) = ν (e.symm ⁻¹' A ∩ Q) := by
    have hpre : A ∩ e ⁻¹' Q = e ⁻¹' (e.symm ⁻¹' A ∩ Q) := by rw [Set.preimage_inter, hBA]
    rw [hpre, he.measure_preimage (hBmeas.inter hQ).nullMeasurableSet]
  rw [h1, h2]
  exact hb _ hBmeas hBconv hBsymm
