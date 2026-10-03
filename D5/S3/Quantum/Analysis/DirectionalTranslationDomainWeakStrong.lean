/- GID: D5/S3/Quantum/Analysis/DirectionalTranslationDomainWeakStrong
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/DirectionalTranslationDomainWeakStrong
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth compact-test weak directional differentiation agrees with strong differentiation of the actual L2 translation orbit in every finite Euclidean dimension. -/

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

open MeasureTheory Filter Set
open DomAddAct
open scoped ENNReal Interval Pointwise

noncomputable section


namespace D5.S3.Quantum.Analysis.DirectionalTranslationDomainWeakStrong
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Weak differentiation against every smooth real compact test is exactly
strong differentiation of translation along a real direction in physical L2.
The dimension and direction may both be zero. -/
theorem directional_translation_domain_iff (b : E) (f h : E → ℂ) (hf : MemLp f 2 (volume : Measure E))
    (hh : MemLp h 2 (volume : Measure E)) :
    ((∀ φ : E → ℝ, ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) φ →
        HasCompactSupport φ →
        (∫ x : E, ((fderiv ℝ φ x b : ℝ) : ℂ) * f x) =
          -∫ x : E, (φ x : ℂ) * h x) ↔
      HasDerivAt (fun t : ℝ => DomAddAct.mk (t • b) +ᵥ hf.toLp f)
        (hh.toLp h) 0) := by
  have hpairing : ∀ (φ : E → ℝ) (hφc : Continuous φ) (hφs : HasCompactSupport φ),
      Continuous (fun x => fderiv ℝ φ x b) → (∀ x, HasFDerivAt φ (fderiv ℝ φ x) x) →
      ∀ (g : E → ℂ), MemLp g 2 (volume : Measure E) →
      HasDerivAt (fun r : ℝ => ∫ x : E, (φ (x - r • b) : ℂ) * g x)
        (∫ x : E, ((-(fderiv ℝ φ x b) : ℝ) : ℂ) * g x) 0 := by
    intro φ hφc hφs hφdc hφd g hg
    let K : Set E := tsupport (fun x => fderiv ℝ φ x b) + Metric.closedBall (0 : E) ‖b‖
    have hKc : IsCompact K := by
      exact ((hφs.fderiv_apply ℝ b).isCompact.add (isCompact_closedBall (0 : E) ‖b‖))
    have hKm : MeasurableSet K := hKc.measurableSet
    have hKtop : volume K ≠ ∞ := hKc.measure_lt_top.ne
    obtain ⟨C, hC⟩ := (hφs.fderiv_apply ℝ b).isCompact.exists_bound_of_continuousOn hφdc.continuousOn
    let C₀ : ℝ := max C 0
    have hC₀ : 0 ≤ C₀ := le_max_right _ _
    have hCglobal : ∀ x, ‖fderiv ℝ φ x b‖ ≤ C₀ := by
      intro x
      by_cases hx : x ∈ tsupport (fun x => fderiv ℝ φ x b)
      · exact (hC x hx).trans (le_max_left _ _)
      · have hz : fderiv ℝ φ x b = 0 := (notMem_tsupport_iff_eventuallyEq.mp hx).self_of_nhds
        rw [hz, norm_zero]
        exact hC₀
    have hbound_mem : MemLp (fun x : E => C₀ * (K.indicator (fun _ : E => (1 : ℝ))) x * ‖g x‖)
        1 (volume : Measure E) := by
      have hi : MemLp (K.indicator (fun _ : E => (1 : ℝ))) 2
          (volume : Measure E) := memLp_indicator_const 2 hKm (1 : ℝ) (Or.inr hKtop)
      have hm : MemLp (fun x : E => (K.indicator (fun _ : E => (1 : ℝ))) x * ‖g x‖)
          1 (volume : Measure E) := MemLp.mul hg.norm hi
      simpa [mul_assoc] using hm.const_mul C₀
    have hFmeas : ∀ r : ℝ, AEStronglyMeasurable
        (fun x : E => (φ (x - r • b) : ℂ) * g x) (volume : Measure E) := by
      intro r
      have hc : Continuous (fun x : E => (φ (x - r • b) : ℂ)) := by fun_prop
      exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
    have hFint : Integrable (fun x : E => (φ x : ℂ) * g x) (volume : Measure E) := by
      have hφlp : MemLp φ 2 (volume : Measure E) := hφc.memLp_of_hasCompactSupport hφs
      have hφlpC : MemLp (fun x : E => (φ x : ℂ)) 2 (volume : Measure E) := by
        have hc : Continuous (fun x : E => (φ x : ℂ)) := by fun_prop
        apply MemLp.of_le_mul (c := 1) hφlp hc.aestronglyMeasurable
        filter_upwards [] with x
        simp
      exact memLp_one_iff_integrable.mp (MemLp.mul hg hφlpC)
    have hF'deriv : ∀ (x : E) (r : ℝ), HasDerivAt
        (fun r : ℝ => (φ (x - r • b) : ℂ) * g x)
        (((-(fderiv ℝ φ (x - r • b) b) : ℝ) : ℂ) * g x) r := by
      intro x r
      have haff : HasDerivAt (fun q : ℝ => x - q • b) (-b) r := by
        simpa using ((hasDerivAt_id r).smul_const b).const_sub x
      have hg := (hφd (x - r • b)).comp_hasDerivAt r haff
      simpa [map_neg, sub_eq_add_neg, mul_assoc, neg_mul] using
        (hg.ofReal_comp.mul_const (g x))
    have hF'meas : AEStronglyMeasurable
        (fun x : E => ((-(fderiv ℝ φ x b) : ℝ) : ℂ) * g x) (volume : Measure E) := by
      have hc : Continuous (fun x : E => ((-(fderiv ℝ φ x b) : ℝ) : ℂ)) := by fun_prop
      exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
    have hbound : ∀ᵐ x : E, ∀ r ∈ Metric.ball (0 : ℝ) 1,
        ‖((-(fderiv ℝ φ (x - r • b) b) : ℝ) : ℂ) * g x‖ ≤
          C₀ * (K.indicator (fun _ : E => (1 : ℝ))) x * ‖g x‖ := by
      filter_upwards [] with x
      intro r hr
      by_cases hx : x ∈ K
      · simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
        exact mul_le_mul_of_nonneg_right (hCglobal (x - r • b)) (norm_nonneg _)
      · have hzero : fderiv ℝ φ (x - r • b) b = 0 := by
          by_contra hn
          have hxm : x - r • b ∈ tsupport (fun x => fderiv ℝ φ x b) := by
            have hsupp : x - r • b ∈ Function.support (fun x => fderiv ℝ φ x b) := by
              simpa [Function.mem_support] using hn
            exact (subset_tsupport (f := fun x => fderiv ℝ φ x b)) hsupp
          have hr0 : ‖r‖ ≤ 1 :=
            (show ‖r‖ < 1 by simpa [Metric.mem_ball] using hr).le
          have hr' : r • b ∈ Metric.closedBall (0 : E) ‖b‖ := by
            simp only [Metric.mem_closedBall, dist_zero_right, norm_smul]
            simpa using mul_le_mul_of_nonneg_right hr0 (norm_nonneg b)
          apply hx
          refine Set.mem_add.2 ⟨x - r • b, hxm, r • b, hr', ?_⟩
          abel
        simp [hzero, hx]
    obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun (r : ℝ) (x : E) => (φ (x - r • b) : ℂ) * g x)
      (F' := fun (r : ℝ) (x : E) => ((-(fderiv ℝ φ (x - r • b) b) : ℝ) : ℂ) * g x)
      (x₀ := (0 : ℝ)) (bound := fun x : E => C₀ * (K.indicator (fun _ : E => (1 : ℝ))) x * ‖g x‖)
      (Metric.ball_mem_nhds 0 one_pos)
      (Filter.Eventually.of_forall hFmeas)
      (by simpa using hFint) (by simpa using hF'meas) hbound
      (memLp_one_iff_integrable.mp hbound_mem)
      (Filter.Eventually.of_forall (fun x r hr => hF'deriv x r))
    simpa using hderiv
  constructor
  · intro hweak
    have hvec : ∀ t : ℝ,
        (DomAddAct.mk (t • b) +ᵥ hf.toLp f) - hf.toLp f =
          ∫ r in (0 : ℝ)..t, DomAddAct.mk (r • b) +ᵥ hh.toLp h := by
      intro t
      let H := Lp ℂ 2 (volume : Measure E)
      let V : ℝ → H → H := fun r u => DomAddAct.mk (r • b) +ᵥ u
      letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
      letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
      have hV (u : H) : Continuous (fun r : ℝ => V r u) := by
        have hmk : Continuous (fun r : ℝ => DomAddAct.mk (r • b)) := DomAddAct.continuous_mk.comp (continuous_id.smul continuous_const)
        have hc : Continuous (fun _ : ℝ => u) := continuous_const
        exact hmk.vadd hc
      let U : H := V t (hf.toLp f) - hf.toLp f
      let W : H := ∫ r in (0 : ℝ)..t, V r (hh.toLp h)
      have hU : LocallyIntegrable (fun x : E => U x) (volume : Measure E) :=
        (Lp.memLp U).locallyIntegrable (by norm_num)
      have hW : LocallyIntegrable (fun x : E => W x) (volume : Measure E) :=
        (Lp.memLp W).locallyIntegrable (by norm_num)
      have hUW : U = W := by
        apply Lp.ext
        apply ae_eq_of_integral_contDiff_smul_eq hU hW
        intro φ hφ hφs
        have hφlp : MemLp φ 2 (volume : Measure E) :=
          hφ.continuous.memLp_of_hasCompactSupport hφs
        have hφlpC : MemLp (fun x : E => (φ x : ℂ)) 2 (volume : Measure E) := by
          have hc : Continuous (fun x : E => (φ x : ℂ)) := by fun_prop
          apply MemLp.of_le_mul (c := 1) hφlp hc.aestronglyMeasurable
          exact ae_of_all _ (fun x => by simp)
        let Φ : H := hφlpC.toLp (fun x : E => (φ x : ℂ))
        let B : H →L[ℂ] ℂ := innerSL ℂ Φ
        have hB : ∀ u : H, B u = ∫ x : E, (φ x : ℂ) * u x := by
          intro u
          dsimp [B, Φ]
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp hφlpC] with x hx
          rw [hx]
          simp [smul_eq_mul, mul_comm]
        have hBv : ∀ r : ℝ, B (V r (hf.toLp f)) =
            ∫ x : E, (φ (x - r • b) : ℂ) * f x := by
          intro r
          dsimp [B, Φ, V]
          rw [L2.inner_def]
          rw [← integral_add_left_eq_self (fun y : E => (φ (y - r • b) : ℂ) *
            f y) (r • b)]
          apply integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp hφlpC,
            (measurePreserving_add_left (volume : Measure E) (r • b)).quasiMeasurePreserving.ae_eq_comp
              hf.coeFn_toLp,
            DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (r • b)) (hf.toLp f)] with x hφx hfx hv
          have hfx' : (hf.toLp f : E → ℂ) (r • b + x) = f (r • b + x) := by
            simpa [Function.comp_def] using hfx
          have hv' : (DomAddAct.mk (r • b) +ᵥ hf.toLp f : H) x =
              (hf.toLp f : E → ℂ) (r • b + x) := by
            simpa using hv
          rw [hφx, hv', hfx']
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_eq_mul, mul_comm]
        have hBf : B (hf.toLp f) = ∫ x : E, (φ x : ℂ) * f x := by
          rw [hB]
          apply integral_congr_ae
          filter_upwards [hf.coeFn_toLp] with x hx
          rw [hx]
        have hBsub : B U = (∫ x : E, (φ (x - t • b) : ℂ) * f x) -
            (∫ x : E, (φ x : ℂ) * f x) := by
          dsimp [U, V]
          rw [map_sub, hBv, hBf]
        have hBh : ∀ r : ℝ, B (V r (hh.toLp h)) =
            ∫ x : E, (φ (x - r • b) : ℂ) * h x := by
          intro r
          dsimp [B, Φ, V]
          rw [L2.inner_def]
          rw [← integral_add_left_eq_self (fun y : E => (φ (y - r • b) : ℂ) *
            h y) (r • b)]
          apply integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp hφlpC,
            (measurePreserving_add_left (volume : Measure E) (r • b)).quasiMeasurePreserving.ae_eq_comp
              hh.coeFn_toLp,
            DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (r • b)) (hh.toLp h)] with x hφx hxh hv
          have hxh' : (hh.toLp h : E → ℂ) (r • b + x) = h (r • b + x) := by
            simpa [Function.comp_def] using hxh
          have hv' : (DomAddAct.mk (r • b) +ᵥ hh.toLp h : H) x =
              (hh.toLp h : E → ℂ) (r • b + x) := by
            simpa using hv
          rw [hφx, hv', hxh']
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_eq_mul, mul_comm]
        have hscalar : ∀ r : ℝ, HasDerivAt
            (fun s : ℝ => ∫ x : E, (φ (x - s • b) : ℂ) * f x)
            (∫ x : E, (φ (x - r • b) : ℂ) * h x) r := by
          intro r
          let ψ : E → ℝ := fun x => φ (x - r • b)
          have hψ : ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) ψ := by
            have haff : ContDiff ℝ (WithTop.some (⊤ : ℕ∞))
                (fun x : E => x - r • b) := by
              exact contDiff_id.sub contDiff_const
            exact hφ.comp haff
          have hψs : HasCompactSupport ψ := by
            dsimp [ψ]
            have heq : (fun x : E => φ (x - r • b)) =
                φ ∘ (Homeomorph.addRight (-(r • b))) := by
              funext x
              change φ (x - r • b) = φ (x + -(r • b))
              rw [sub_eq_add_neg]
            rw [heq]
            exact hφs.comp_homeomorph (Homeomorph.addRight (-(r • b)))
          have hψdc : Continuous (fun x => fderiv ℝ ψ x b) :=
            (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
          have hψd : ∀ x, HasFDerivAt ψ (fderiv ℝ ψ x) x := by
            intro x
            simpa using (hψ.differentiable (by norm_num) x).hasFDerivAt
          have hd0 := hpairing ψ hψ.continuous hψs hψdc hψd f hf
          have hw := hweak ψ hψ hψs
          have hneg : (∫ x : E, ((-(fderiv ℝ ψ x b) : ℝ) : ℂ) * f x) =
              ∫ x : E, (ψ x : ℂ) * h x := by
            rw [← neg_neg (∫ x : E, (ψ x : ℂ) * h x)]
            rw [← hw, ← integral_neg]
            apply integral_congr_ae
            filter_upwards [] with x
            simp [neg_mul]
          have hd0' := hd0.congr_deriv hneg
          have hg : HasDerivAt (fun s : ℝ => s - r) 1 r :=
            (hasDerivAt_id r).sub_const r
          have hd := HasDerivAt.scomp_of_eq r hd0' hg (by simp)
          simpa [ψ, Function.comp_def, sub_smul, add_smul, neg_smul, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hd
        have hG : Continuous (fun r : ℝ => B (V r (hh.toLp h))) :=
          B.continuous.comp (hV (hh.toLp h))
        have hGint : IntervalIntegrable (fun r : ℝ => B (V r (hh.toLp h)))
            (volume : Measure ℝ) 0 t := hG.intervalIntegrable 0 t
        have hGint' : IntervalIntegrable (fun r : ℝ =>
            ∫ x : E, (φ (x - r • b) : ℂ) * h x) (volume : Measure ℝ) 0 t := by
          convert hGint using 1
          funext r
          exact (hBh r).symm
        have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun r : ℝ => ∫ x : E, (φ (x - r • b) : ℂ) * f x)
          (f' := fun r : ℝ => ∫ x : E, (φ (x - r • b) : ℂ) * h x)
          (fun r hr => hscalar r) hGint'
        have hVH : IntervalIntegrable (fun r : ℝ => V r (hh.toLp h))
            (volume : Measure ℝ) 0 t := (hV (hh.toLp h)).intervalIntegrable 0 t
        have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm
          (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := t) B hVH
        have hFTC' : (∫ r in (0 : ℝ)..t, ∫ x : E,
            (φ (x - r • b) : ℂ) * h x) =
            (∫ x : E, (φ (x - t • b) : ℂ) * f x) -
              ∫ x : E, (φ x : ℂ) * f x := by
          simpa using hFTC
        have hpair : B U = B W := by
          calc
            B U = (∫ x : E, (φ (x - t • b) : ℂ) * f x) -
                (∫ x : E, (φ x : ℂ) * f x) := hBsub
            _ = ∫ r in (0 : ℝ)..t, ∫ x : E,
                (φ (x - r • b) : ℂ) * h x := hFTC'.symm
            _ = ∫ r in (0 : ℝ)..t, B (V r (hh.toLp h)) := by
              congr 1
              funext r
              exact (hBh r).symm
            _ = B W := hcomm
        calc
          (∫ x : E, φ x • U x) = ∫ x : E, (φ x : ℂ) * U x := by
            apply integral_congr_ae
            filter_upwards [] with x
            simp [smul_eq_mul]
          _ = B U := (hB U).symm
          _ = B W := hpair
          _ = ∫ x : E, (φ x : ℂ) * W x := hB W
          _ = ∫ x : E, φ x • W x := by
            apply integral_congr_ae
            filter_upwards [] with x
            simp [smul_eq_mul]
      dsimp [U, W, V, H] at hUW ⊢
      exact hUW

    have hforward : HasDerivAt
        (fun t : ℝ => DomAddAct.mk (t • b) +ᵥ hf.toLp f)
        (hh.toLp h) 0 := by
        let H := Lp ℂ 2 (volume : Measure E)
        let V : ℝ → H → H := fun r u => DomAddAct.mk (r • b) +ᵥ u
        letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
        letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
        have hV (u : H) : Continuous (fun r : ℝ => V r u) := by
          have hmk : Continuous (fun r : ℝ => DomAddAct.mk (r • b)) := DomAddAct.continuous_mk.comp (continuous_id.smul continuous_const)
          exact hmk.vadd (continuous_const : Continuous (fun _ : ℝ => u))
        have hI := (hV (hh.toLp h)).integral_hasStrictDerivAt 0 0
        have hI' : HasDerivAt (fun s : ℝ => ∫ r in (0 : ℝ)..s, V r (hh.toLp h))
            (hh.toLp h) 0 := by
          simpa [V] using hI.hasDerivAt
        have hsum := hI'.const_add (hf.toLp f)
        have hfun : (fun s : ℝ => V s (hf.toLp f)) =
            (fun s : ℝ => hf.toLp f + ∫ r in (0 : ℝ)..s, V r (hh.toLp h)) := by
          funext s
          have hs := hvec s
          simpa [V, sub_eq_iff_eq_add, add_comm] using congrArg (fun z => z + hf.toLp f) hs
        have hev : (fun s => V s (hf.toLp f)) =ᶠ[nhds (0 : ℝ)]
            (fun s => hf.toLp f + ∫ r in (0 : ℝ)..s, V r (hh.toLp h)) :=
          Filter.Eventually.of_forall (fun s => congrFun hfun s)
        have hsum' := hsum.congr_of_eventuallyEq hev
        simpa [V, H] using hsum'

    exact hforward
  · intro horbit
    have hreverse : ∀ φ : E → ℝ,
        ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) φ → HasCompactSupport φ →
        (∫ x : E, ((fderiv ℝ φ x b : ℝ) : ℂ) * f x) =
          -∫ x : E, (φ x : ℂ) * h x := by
        let H := Lp ℂ 2 (volume : Measure E)
        let V : ℝ → H → H := fun r u => DomAddAct.mk (r • b) +ᵥ u
        letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
        letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
        intro φ hφ hφs
        have hφdc : Continuous (fun x => fderiv ℝ φ x b) := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
        have hφd : ∀ x, HasFDerivAt φ (fderiv ℝ φ x) x := by
          intro x
          simpa using (hφ.differentiable (by norm_num) x).hasFDerivAt
        have hscalar := hpairing φ hφ.continuous hφs
          hφdc hφd f hf
        have hφlp : MemLp φ 2 (volume : Measure E) :=
          hφ.continuous.memLp_of_hasCompactSupport hφs
        have hφlpC : MemLp (fun x : E => (φ x : ℂ)) 2 (volume : Measure E) := by
          have hc : Continuous (fun x : E => (φ x : ℂ)) := by fun_prop
          apply MemLp.of_le_mul (c := 1) hφlp hc.aestronglyMeasurable
          exact ae_of_all _ (fun x => by simp)
        let Φ : H := hφlpC.toLp (fun x : E => (φ x : ℂ))
        let B : H →L[ℂ] ℂ := innerSL ℂ Φ
        have hB : ∀ u : H, B u = ∫ x : E, (φ x : ℂ) * u x := by
          intro u
          dsimp [B, Φ]
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp hφlpC] with x hx
          rw [hx]
          simp [smul_eq_mul, mul_comm]
        have hBv : ∀ r : ℝ, B (V r (hf.toLp f)) =
            ∫ x : E, (φ (x - r • b) : ℂ) * f x := by
          intro r
          dsimp [B, Φ, V]
          rw [L2.inner_def]
          rw [← integral_add_left_eq_self (fun y : E => (φ (y - r • b) : ℂ) * f y) (r • b)]
          apply integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp hφlpC,
            (measurePreserving_add_left (volume : Measure E) (r • b)).quasiMeasurePreserving.ae_eq_comp
              hf.coeFn_toLp,
            DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (r • b)) (hf.toLp f)] with x hφx hfx hv
          have hfx' : (hf.toLp f : E → ℂ) (r • b + x) = f (r • b + x) := by
            simpa [Function.comp_def] using hfx
          have hv' : (DomAddAct.mk (r • b) +ᵥ hf.toLp f : H) x =
              (hf.toLp f : E → ℂ) (r • b + x) := by
            simpa using hv
          rw [hφx, hv', hfx']
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_eq_mul, mul_comm]
        have hBorbit :
            HasDerivAt (fun r : ℝ => B (V r (hf.toLp f))) (B (hh.toLp h)) 0 := by
          have hi := HasDerivAt.inner ℂ (hasDerivAt_const (x := (0 : ℝ)) Φ) horbit
          simpa [B, V, innerSL_apply_apply] using hi
        have hBorbitscalar : HasDerivAt
            (fun r : ℝ => ∫ x : E, (φ (x-r • b) : ℂ) * f x) (B (hh.toLp h)) 0 := by
          exact hBorbit.congr_of_eventuallyEq
            (Filter.Eventually.of_forall (fun r => (hBv r).symm))
        have heqderiv := HasDerivAt.unique hBorbitscalar hscalar
        have hbh : B (hh.toLp h) = ∫ x : E, (φ x : ℂ) * h x := by
          rw [hB]
          apply integral_congr_ae
          filter_upwards [hh.coeFn_toLp] with x hx
          rw [hx]
        have hmain : (∫ x : E, ((-(fderiv ℝ φ x b) : ℝ) : ℂ) * f x) =
            ∫ x : E, (φ x : ℂ) * h x := by
          rw [← hbh]
          exact heqderiv.symm
        have hnegderiv : (∫ x : E, ((fderiv ℝ φ x b : ℝ) : ℂ) * f x) =
            - (∫ x : E, ((-(fderiv ℝ φ x b) : ℝ) : ℂ) * f x) := by
          rw [← integral_neg]
          apply integral_congr_ae
          filter_upwards [] with x
          simp [neg_mul]
        calc
          (∫ x : E, ((fderiv ℝ φ x b : ℝ) : ℂ) * f x) =
              - (∫ x : E, ((-(fderiv ℝ φ x b) : ℝ) : ℂ) * f x) := hnegderiv
          _ = - (∫ x : E, (φ x : ℂ) * h x) := by rw [hmain]
    exact hreverse



end D5.S3.Quantum.Analysis.DirectionalTranslationDomainWeakStrong
