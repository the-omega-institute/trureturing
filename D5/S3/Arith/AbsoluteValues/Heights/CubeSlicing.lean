/- GID: D5/S3/Arith/AbsoluteValues/Heights/CubeSlicing
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/CubeSlicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Gaussian slice bound gives central sections of a convex symmetric set volume at least one. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.ProductOfBalls
public import Mathlib.Analysis.InnerProductSpace.ProdL2

public section

open MeasureTheory Measure Set ENNReal Pointwise
open scoped Real

section OrthogonalDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The orthogonal decomposition `E ≃ₗ[ℝ] V × Vᗮ`, forgetting the `L²` structure of the target. -/
noncomputable def Submodule.prodOrthogonalEquiv (V : Submodule ℝ E) :
    E ≃ₗ[ℝ] (V × (Vᗮ : Submodule ℝ E)) :=
  V.orthogonalDecomposition.toLinearEquiv ≪≫ₗ WithLp.linearEquiv 2 ℝ (V × (Vᗮ : Submodule ℝ E))

variable [MeasurableSpace E] [BorelSpace E]


end OrthogonalDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


/-- **Bombieri–Gubler, Theorem C.3.8.** If the Gauss measure of every measurable convex symmetric
set is at most its volume inside `Q`, then every central slice of `Q` by a linear subspace has
volume at least one, computed on the subspace. -/
theorem one_le_volume_subtype_mem
    {Q : Set E} (hQm : MeasurableSet Q) (hQc : Convex ℝ Q) (hQs : ∀ x ∈ Q, -x ∈ Q)
    (hQ : HasSliceBound (volume : Measure E) gaussDensity Q) (V : Submodule ℝ E) :
    1 ≤ volume {y : V | (y : E) ∈ Q} := by
  let nativeSource11 := (open MeasureTheory Set in (fun {E F : Type _} [MeasurableSpace E] [AddCommGroup E]
      [Module ℝ E] [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] {ν : MeasureTheory.Measure F}
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
  let nativeSource158 := (open MeasureTheory Measure Set Metric ENNReal in (open scoped Real in (fun {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] => (show ∫⁻ x : E, gaussDensity x = 1 from by
    classical
    have hm : Measurable (gaussDensity : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ≥0∞) := by
      unfold gaussDensity; fun_prop
    rw [← nativeSource157 (Fin (Module.finrank ℝ E)),
      ← (stdOrthonormalBasis ℝ E).measurePreserving_repr.lintegral_comp hm]
    exact MeasureTheory.lintegral_congr fun x => by
      rw [gaussDensity, gaussDensity, (stdOrthonormalBasis ℝ E).repr.norm_map]))))
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
  have hψmeas : Measurable V.prodOrthogonalEquiv :=
    ((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal in (fun {E : Type _} [instE1 : NormedAddCommGroup E] [instE2 : InnerProductSpace ℝ E] [instE3 : FiniteDimensional ℝ E] [instE4 : MeasurableSpace E] [instE5 : BorelSpace E] (V : Submodule ℝ E) => (show MeasurePreserving V.prodOrthogonalEquiv (volume : Measure E)
            ((volume : Measure V).prod (volume : Measure (Vᗮ : Submodule ℝ E))) from by
        have h1 : MeasurePreserving V.orthogonalDecomposition (volume : Measure E) volume :=
          LinearIsometryEquiv.measurePreserving _
        have h2 := WithLp.volume_preserving_ofLp (V : Type _) ((Vᗮ : Submodule ℝ E) : Type _)
        rw [← Measure.volume_eq_prod]
        exact h2.comp h1)))) V).measurable
  have hψsymm : Measurable V.prodOrthogonalEquiv.symm :=
    (LinearMap.continuous_of_finiteDimensional
      (V.prodOrthogonalEquiv.symm : (V × (Vᗮ : Submodule ℝ E)) →ₗ[ℝ] E)).measurable
  let ψm : E ≃ᵐ (V × (Vᗮ : Submodule ℝ E)) :=
    ⟨V.prodOrthogonalEquiv.toEquiv, hψmeas, hψsymm⟩
  have hMPsymm : MeasurePreserving V.prodOrthogonalEquiv.symm
      ((volume : Measure V).prod (volume : Measure (Vᗮ : Submodule ℝ E))) (volume : Measure E) :=
    (((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal in (fun {E : Type _} [instE1 : NormedAddCommGroup E] [instE2 : InnerProductSpace ℝ E] [instE3 : FiniteDimensional ℝ E] [instE4 : MeasurableSpace E] [instE5 : BorelSpace E] (V : Submodule ℝ E) => (show MeasurePreserving V.prodOrthogonalEquiv (volume : Measure E)
            ((volume : Measure V).prod (volume : Measure (Vᗮ : Submodule ℝ E))) from by
        have h1 : MeasurePreserving V.orthogonalDecomposition (volume : Measure E) volume :=
          LinearIsometryEquiv.measurePreserving _
        have h2 := WithLp.volume_preserving_ofLp (V : Type _) ((Vᗮ : Submodule ℝ E) : Type _)
        rw [← Measure.volume_eq_prod]
        exact h2.comp h1)))) V)).symm ψm
  have hQ' := HasSliceBound.of_measurePreserving V.prodOrthogonalEquiv.symm hMPsymm hψmeas
    (show Measurable (gaussDensity : E → ℝ≥0∞) from by
      unfold gaussDensity
      fun_prop) hQm hQ
  set W := (Vᗮ : Submodule ℝ E)
  set QQ : Set (V × W) := V.prodOrthogonalEquiv.symm ⁻¹' Q with hQQdef
  have hQQm : MeasurableSet QQ := hψsymm hQm
  have hQQc : Convex ℝ QQ :=
    hQc.linear_preimage (V.prodOrthogonalEquiv.symm : (V × W) →ₗ[ℝ] E)
  have hQQs : ∀ q ∈ QQ, -q ∈ QQ := by
    intro q hq
    have hneg : V.prodOrthogonalEquiv.symm (-q) = -(V.prodOrthogonalEquiv.symm q) := map_neg _ _
    simpa [hQQdef, Set.mem_preimage, hneg] using hQs _ hq
  -- the marginal of `QQ` in the `V` direction
  set f : W → ℝ≥0∞ := fun z => (volume : Measure V) {y : V | (y, z) ∈ QQ} with hfdef
  have hfmeas : Measurable f := measurable_measure_prodMk_right hQQm
  have hsecm : ∀ z : W, MeasurableSet {y : V | (y, z) ∈ QQ} :=
    fun z => hQQm.preimage (by fun_prop)
  have hfeven : ∀ z, f (-z) = f z := by
    intro z
    have hset : {y : V | (y, -z) ∈ QQ} = -{y : V | (y, z) ∈ QQ} := by
      ext y
      simp only [Set.mem_neg, Set.mem_ofPred_eq]
      exact ⟨fun hy => by simpa using hQQs _ hy, fun hy => by simpa using hQQs _ hy⟩
    rw [hfdef]
    simp only
    rw [hset, measure_neg]
  have hflc : LogConcave f := by
    have hswapc : Convex ℝ {q : W × V | (q.2, q.1) ∈ QQ} :=
      fun _ h1 _ h2 _ _ ha hb hab => hQQc h1 h2 ha hb hab
    have heq : (fun z => ∫⁻ y in (Set.univ : Set V),
        Set.indicator {q : W × V | (q.2, q.1) ∈ QQ} (fun _ => (1 : ℝ≥0∞)) (z, y)
        ∂(volume : Measure V)) = f := by
      funext z
      rw [show (fun y : V =>
          Set.indicator {q : W × V | (q.2, q.1) ∈ QQ} (fun _ => (1 : ℝ≥0∞)) (z, y))
          = Set.indicator {y : V | (y, z) ∈ QQ} (fun _ => (1 : ℝ≥0∞)) from rfl,
        lintegral_indicator (hsecm z), setLIntegral_one, hfdef]
      simp
    have hPLV : HasPrekopaLeindler (volume : Measure V) := by
      let f : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
        (stdOrthonormalBasis ℝ V).repr
      exact HasPrekopaLeindler.of_measurePreserving f.toLinearEquiv f.measurePreserving
        f.symm.continuous.measurable (hasPrekopaLeindler_euclideanSpace _)
    have hswapm : MeasurableSet {q : W × V | (q.2, q.1) ∈ QQ} :=
      hQQm.preimage (measurable_snd.prodMk measurable_fst)
    exact heq ▸ nativeSource11 hPLV
      (measurable_one.indicator hswapm) (nativeSource159 hswapc 1)
      MeasurableSet.univ convex_univ
  have hfle : ∀ z, f z ≤ f 0 := fun z => ((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal in (fun {F : Type _} [AddCommGroup F] [Module ℝ F] {f : F → ℝ≥0∞}
        (hf : LogConcave f) (hfe : ∀ x, f (-x) = f x) (x : F) => (show f x ≤ f 0 from by
      have h := hf (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) x (-x)
      rw [hfe x, show (1/2 : ℝ) • x + (1/2 : ℝ) • (-x) = 0 by module] at h
      calc f x = f x ^ ((1:ℝ)/2) * f x ^ ((1:ℝ)/2) := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
            norm_num
        _ ≤ f 0 := h)))) hflc) hfeven z
  have hf0 : f 0 = volume {y : V | (y : E) ∈ Q} := by
    rw [hfdef]
    simp only
    congr 1
    ext y
    simp [hQQdef, Set.mem_preimage, Submodule.prodOrthogonalEquiv, Submodule.orthogonalDecomposition_symm_apply]
  have hdens : ∀ q : V × W, gaussDensity (V.prodOrthogonalEquiv.symm q)
      = gaussDensity q.1 * gaussDensity q.2 := by
    intro q
    rw [gaussDensity, gaussDensity, gaussDensity,
      show ‖V.prodOrthogonalEquiv.symm q‖ ^ 2 = ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 from by
        change ‖V.orthogonalDecomposition.symm (WithLp.toLp 2 q)‖ ^ 2 = _
        rw [V.orthogonalDecomposition.symm.norm_map, WithLp.prod_norm_sq_eq_of_L2]
        simp, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have key : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal (Real.exp (-π * ε ^ 2)) ≤ f 0 := by
    intro ε hε
    have hSm : MeasurableSet (Metric.closedBall (0 : W) ε) := measurableSet_closedBall
    have hApp := hQ' (Set.univ ×ˢ Metric.closedBall (0 : W) ε)
      (MeasurableSet.univ.prod hSm)
      (convex_univ.prod (convex_closedBall _ _))
      (fun q hq => ⟨Set.mem_univ _, by
        have hn : ‖-q.2‖ ≤ ε := by
          rw [norm_neg]; simpa [Metric.mem_closedBall, dist_zero_right] using hq.2
        simpa [Metric.mem_closedBall, dist_zero_right] using hn⟩)
    have hlhs : ∫⁻ q in Set.univ ×ˢ Metric.closedBall (0 : W) ε,
        gaussDensity (V.prodOrthogonalEquiv.symm q)
        ∂((volume : Measure V).prod (volume : Measure W))
        = (∫⁻ y : V, gaussDensity y) * ∫⁻ z in Metric.closedBall (0 : W) ε, gaussDensity z := by
      rw [← Measure.prod_restrict, Measure.restrict_univ, lintegral_congr hdens]
      exact lintegral_prod_mul (fun {E : Type _} [instN : NormedAddCommGroup E] [instM : MeasurableSpace E]
      [instO : OpensMeasurableSpace E] =>
    (show Measurable (gaussDensity : E → ℝ≥0∞) from by unfold gaussDensity; fun_prop)).aemeasurable
        (fun {E : Type _} [instN : NormedAddCommGroup E] [instM : MeasurableSpace E]
      [instO : OpensMeasurableSpace E] =>
    (show Measurable (gaussDensity : E → ℝ≥0∞) from by unfold gaussDensity; fun_prop)).aemeasurable
    have hlow : ENNReal.ofReal (Real.exp (-π * ε ^ 2)) * volume (Metric.closedBall (0 : W) ε)
        ≤ ∫⁻ z in Metric.closedBall (0 : W) ε, gaussDensity z := by
      rw [← setLIntegral_const]
      refine setLIntegral_mono' hSm fun z hz => ?_
      rw [gaussDensity]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have hznorm : ‖z‖ ≤ ε := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
      have hsq : ‖z‖ ^ 2 ≤ ε ^ 2 := by nlinarith [norm_nonneg z]
      nlinarith [Real.pi_pos]
    have hrhs : ((volume : Measure V).prod (volume : Measure W))
        ((Set.univ ×ˢ Metric.closedBall (0 : W) ε) ∩ QQ)
        ≤ f 0 * volume (Metric.closedBall (0 : W) ε) := by
      rw [Measure.prod_apply_symm ((MeasurableSet.univ.prod hSm).inter hQQm)]
      calc ∫⁻ z : W, (volume : Measure V)
              ((fun y => (y, z)) ⁻¹' ((Set.univ ×ˢ Metric.closedBall (0 : W) ε) ∩ QQ))
          ≤ ∫⁻ z : W, Set.indicator (Metric.closedBall (0 : W) ε) (fun _ => f 0) z := by
            refine lintegral_mono fun z => ?_
            by_cases hz : z ∈ Metric.closedBall (0 : W) ε
            · rw [Set.indicator_of_mem hz]
              refine le_trans (le_of_eq ?_) (hfle z)
              rw [hfdef]
              congr 1
              ext y; simp [hz]
            · rw [Set.indicator_of_notMem hz,
                show ((fun y => (y, z)) ⁻¹'
                    ((Set.univ ×ˢ Metric.closedBall (0 : W) ε) ∩ QQ)) = ∅ by ext y; simp [hz]]
              simp
        _ = f 0 * volume (Metric.closedBall (0 : W) ε) := by
            rw [lintegral_indicator hSm, setLIntegral_const]
    have hvpos : volume (Metric.closedBall (0 : W) ε) ≠ 0 :=
      (Metric.measure_closedBall_pos volume 0 hε).ne'
    have hvtop : volume (Metric.closedBall (0 : W) ε) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hcomb : ENNReal.ofReal (Real.exp (-π * ε ^ 2)) * volume (Metric.closedBall (0 : W) ε)
        ≤ f 0 * volume (Metric.closedBall (0 : W) ε) := by
      calc ENNReal.ofReal (Real.exp (-π * ε ^ 2)) * volume (Metric.closedBall (0 : W) ε)
          ≤ ∫⁻ z in Metric.closedBall (0 : W) ε, gaussDensity z := hlow
        _ = (∫⁻ y : V, gaussDensity y) * ∫⁻ z in Metric.closedBall (0 : W) ε, gaussDensity z := by
              rw [nativeSource158, one_mul]
        _ = ∫⁻ q in Set.univ ×ˢ Metric.closedBall (0 : W) ε,
              gaussDensity (V.prodOrthogonalEquiv.symm q)
              ∂((volume : Measure V).prod (volume : Measure W)) := hlhs.symm
        _ ≤ ((volume : Measure V).prod (volume : Measure W))
              ((Set.univ ×ˢ Metric.closedBall (0 : W) ε) ∩ QQ) := hApp
        _ ≤ f 0 * volume (Metric.closedBall (0 : W) ε) := hrhs
    have hcomb' : volume (Metric.closedBall (0 : W) ε) * ENNReal.ofReal (Real.exp (-π * ε ^ 2))
        ≤ volume (Metric.closedBall (0 : W) ε) * f 0 := by
      rw [mul_comm, mul_comm (volume (Metric.closedBall (0 : W) ε)) (f 0)]; exact hcomb
    exact (ENNReal.mul_le_mul_iff_right hvpos hvtop).mp hcomb'
  rw [← hf0]
  have hcont : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp (-π * ε ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h1 : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp (-π * ε ^ 2)))
        (nhds 0) (nhds (ENNReal.ofReal (Real.exp (-π * (0 : ℝ) ^ 2)))) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).tendsto 0
    simpa using h1.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε

section Milestones

/-- The volume `ω_n` of the unit ball of `EuclideanSpace ℝ (Fin n)`. -/
@[expose] noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal




end Milestones
