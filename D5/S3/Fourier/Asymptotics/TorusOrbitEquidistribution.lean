/- GID: D5/S3/Fourier/Asymptotics/TorusOrbitEquidistribution
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/TorusOrbitEquidistribution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous observables on the closed cyclic torus subgroup have Haar orbit averages. -/

import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.UniformSpace.Equicontinuity

noncomputable section

namespace D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution

open Filter MeasureTheory Set TopologicalSpace Topology
open scoped Topology

/-- Powers of an arbitrary finite torus element equidistribute in their own closed subgroup. -/
theorem result {I : Type*} [Fintype I] (g : I → Circle) :
    let G := (Subgroup.zpowers g).topologicalClosure
    letI : CompactSpace G := isCompact_iff_compactSpace.mp
      (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers g)).isCompact
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
    (G : Set (I → Circle)) = closure (range (fun n : ℕ => g ^ n)) ∧
    ∀ f : C(G, ℂ), Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, f ⟨g ^ (n + 1),
        G.pow_mem (subset_closure (Subgroup.mem_zpowers g)) (n + 1)⟩) / (N : ℂ))
      atTop (𝓝 (∫ z : G, f z ∂μ)) := by
  classical
  intro G
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers g)).isCompact
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  have hG : (G : Set (I → Circle)) = closure (range (fun n : ℕ => g ^ n)) := by
    rw [Subgroup.topologicalClosure_coe, Subgroup.coe_zpowers, closure_range_zpow_eq_pow]
  refine ⟨hG, ?_⟩
  let a : G := ⟨g, subset_closure (Subgroup.mem_zpowers g)⟩
  let A (N : ℕ) : C(G, ℂ) →L[ℂ] ℂ :=
    (N : ℂ)⁻¹ • ∑ n ∈ Finset.range N, ContinuousMap.evalCLM ℂ (a ^ (n + 1))
  have hA (N : ℕ) (F : C(G, ℂ)) :
      A N F = (∑ n ∈ Finset.range N, F (a ^ (n + 1))) / (N : ℂ) := by
    simp only [A, smul_apply, sum_apply,
      ContinuousMap.evalCLM_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hbound (N : ℕ) (F : C(G, ℂ)) : ‖A N F‖ ≤ ‖F‖ := by
    rw [hA, norm_div, Complex.norm_natCast]
    by_cases hN : N = 0
    · simp [hN]
    have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    apply (div_le_iff₀ hpos).mpr
    calc
      ‖∑ n ∈ Finset.range N, F (a ^ (n + 1))‖ ≤
          ∑ _n ∈ Finset.range N, ‖F‖ :=
        norm_sum_le_of_le _ (fun n _ => F.norm_coe_le_norm _)
      _ = ‖F‖ * N := by simp [mul_comm]
  let J : C(G, ℂ) →L[ℂ] ℂ :=
    (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)
  have hJ (F : C(G, ℂ)) : J F = ∫ z : G, F z ∂μ := by
    change L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ F) = _
    rw [← L1.integral_eq' ℂ, L1.integral_eq_integral]
    exact integral_congr_ae (ContinuousMap.coeFn_toLp μ F)
  let S : Submodule ℂ C(G, ℂ) :=
    { carrier := {F | Tendsto (fun N => A N F) atTop (𝓝 (J F))}
      zero_mem' := by simp
      add_mem' := by
        intro F H hF hH
        simpa only [Set.mem_ofPred_eq, map_add] using hF.add hH
      smul_mem' := by
        intro c F hF
        simpa only [Set.mem_ofPred_eq, map_smul] using hF.const_smul c }
  have hequi : Equicontinuous (fun N : ℕ => (A N : C(G, ℂ) → ℂ)) := by
    apply (LipschitzWith.uniformEquicontinuous _ 1 _).equicontinuous
    intro N
    apply LipschitzWith.of_dist_le_mul
    intro F H
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub] using hbound N (F - H)
  have hclosed : IsClosed (S : Set C(G, ℂ)) :=
    hequi.isClosed_setOfPred_tendsto J.continuous
  let e : UnitAddTorus I ≃ₜ (I → Circle) :=
    Homeomorph.piCongrRight (fun _ => AddCircle.homeomorphCircle (by norm_num))
  let j : C(G, UnitAddTorus I) := ⟨fun z => e.symm z.val,
    e.symm.continuous.comp continuous_subtype_val⟩
  have hj : IsClosedEmbedding j :=
    e.symm.isClosedEmbedding.comp
      (Subgroup.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal
  let R := ContinuousMap.compCLM ℂ ℂ j
  have hsur : Function.Surjective R := by
    intro F
    obtain ⟨H, hH⟩ := F.exists_extension hj
    exact ⟨H, hH⟩
  have hdense := hsur.denseRange.topologicalClosure_map_submodule
    UnitAddTorus.span_mFourier_closure_eq_top
  have hchar (k : I → ℤ) : R (UnitAddTorus.mFourier k) ∈ S := by
    let χ : (I → Circle) →* Circle :=
      { toFun z := ∏ i, z i ^ k i
        map_one' := by simp
        map_mul' := by intro b c; simp [mul_zpow, Finset.prod_mul_distrib] }
    have hχcont : Continuous χ := by
      change Continuous (fun z : I → Circle => ∏ i, z i ^ k i)
      fun_prop
    have hχ (z : G) : R (UnitAddTorus.mFourier k) z = (χ z.val : ℂ) := by
      have he (b : Circle) : AddCircle.toCircle
          ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm b) = b := by
        rw [← AddCircle.homeomorphCircle_apply one_ne_zero, Homeomorph.apply_symm_apply]
      change (∏ i, fourier (k i)
        ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (z.val i))) = _
      simp only [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow, he]
      exact (map_prod Circle.coeHom (fun i => z.val i ^ k i) Finset.univ).symm
    have hp (n : ℕ) : R (UnitAddTorus.mFourier k) (a ^ n) = (χ g : ℂ) ^ n := by
      rw [hχ]
      change (χ (g ^ n) : ℂ) = _
      simp
    change Tendsto (fun N => A N (R (UnitAddTorus.mFourier k))) atTop
      (𝓝 (J (R (UnitAddTorus.mFourier k))))
    simp only [hA, hp, hJ]
    by_cases hr : χ g = 1
    · have hall (z : G) : χ z.val = 1 := by
        have hz : z.val ∈ closure (range (fun n : ℕ => g ^ n)) := hG ▸ z.property
        apply closure_minimal (t := {b | χ b = 1}) _ (isClosed_eq hχcont continuous_const) hz
        rintro _ ⟨n, rfl⟩
        simp [hr]
      have hconst : (fun z : G => R (UnitAddTorus.mFourier k) z) = fun _ => (1 : ℂ) := by
        funext z
        rw [hχ, hall]
        rfl
      rw [hconst]
      simp only [integral_const, probReal_univ, one_smul]
      refine (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).congr' ?_
      filter_upwards [eventually_ne_atTop 0] with N hN
      simp [hr, hN]
    · have hr' : (χ g : ℂ) ≠ 1 := fun h => hr (Circle.coe_eq_one.mp h)
      have hint : (∫ z : G, R (UnitAddTorus.mFourier k) z ∂μ) = 0 := by
        have hinv := integral_mul_left_eq_self (μ := μ)
          (fun z : G => R (UnitAddTorus.mFourier k) z) a
        have hm (z : G) : R (UnitAddTorus.mFourier k) (a * z) =
            (χ g : ℂ) * R (UnitAddTorus.mFourier k) z := by
          simp only [hχ]
          change (χ (g * z.val) : ℂ) = _
          simp
        simp_rw [hm] at hinv
        rw [integral_const_mul] at hinv
        exact eq_zero_of_mul_eq_self_left hr' hinv
      rw [hint]
      let r : ℂ := χ g
      have hrnorm : ‖r‖ = 1 := Circle.norm_coe _
      have hb (N : ℕ) : ‖∑ n ∈ Finset.range N, r ^ (n + 1)‖ ≤ 2 / ‖r - 1‖ := by
        calc
          ‖∑ n ∈ Finset.range N, r ^ (n + 1)‖ =
              ‖r * ((r ^ N - 1) / (r - 1))‖ := by
            rw [← geom_sum_eq hr']
            congr 1
            simp only [pow_succ, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _
            exact mul_comm _ _
          _ = ‖r ^ N - 1‖ / ‖r - 1‖ := by rw [norm_mul, hrnorm, one_mul, norm_div]
          _ ≤ 2 / ‖r - 1‖ := by
            apply div_le_div_of_nonneg_right _ (norm_nonneg _)
            calc
              ‖r ^ N - 1‖ ≤ ‖r ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
              _ = 2 := by norm_num [norm_pow, hrnorm]
      apply squeeze_zero_norm (fun N => ?_)
        (tendsto_const_div_atTop_nhds_zero_nat (2 / ‖r - 1‖))
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (hb N) (Nat.cast_nonneg N)
  have hspan : (Submodule.span ℂ (range (UnitAddTorus.mFourier (d := I)))).map
      R.toLinearMap ≤ S := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact hchar k
  have htop : (⊤ : Submodule ℂ C(G, ℂ)) ≤ S := by
    rw [← hdense]
    exact Submodule.topologicalClosure_minimal _ hspan hclosed
  intro f
  have hf := htop (Submodule.mem_top : f ∈ (⊤ : Submodule ℂ C(G, ℂ)))
  change Tendsto (fun N => A N f) atTop (𝓝 (J f)) at hf
  have ha (n : ℕ) : a ^ n = ⟨g ^ n, G.pow_mem
      (subset_closure (Subgroup.mem_zpowers g)) n⟩ := Subtype.ext (Subgroup.coe_pow G a n)
  simpa only [hA, hJ, ha, μ] using hf

#print axioms result

end D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution
