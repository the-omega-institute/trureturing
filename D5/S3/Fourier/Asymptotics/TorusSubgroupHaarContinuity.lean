/- GID: D5/S3/Fourier/Asymptotics/TorusSubgroupHaarContinuity
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/TorusSubgroupHaarContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Fourier.AddCircleMulti]
   utility: none
   digest: Hausdorff convergence of closed finite-torus subgroups preserves normalized Haar measures weakly. -/

import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Tactic

namespace D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity

open Set Filter MeasureTheory UnitAddTorus
open scoped Topology BigOperators
noncomputable section

/-- Normalized Haar measure on the closed subgroup, pushed forward by inclusion into the torus. -/
noncomputable def ambientHaar {I : Type*} [Fintype I]
    (H : ClosedSubgroup (I → Circle)) : @ProbabilityMeasure (I → Circle) (borel _) := by
  letI : MeasurableSpace (I → Circle) := borel _
  letI : BorelSpace (I → Circle) := ⟨rfl⟩
  letI : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  letI : MeasurableSpace H := borel H
  letI : BorelSpace H := ⟨rfl⟩
  let μ : Measure H := Measure.haarMeasure ⊤
  letI : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  exact ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure H)
    continuous_subtype_val.measurable.aemeasurable


/-- Hausdorff convergence of closed torus subgroups implies weak convergence of their
ambient normalized Haar probability measures. -/
theorem result {I : Type*} [Fintype I]
    (Hn : ℕ → ClosedSubgroup (I → Circle)) (H : ClosedSubgroup (I → Circle))
    (h : Tendsto (fun n => Metric.hausdorffDist (Hn n : Set (I → Circle))
      (H : Set (I → Circle))) atTop (𝓝 0)) :
    letI : MeasurableSpace (I → Circle) := borel _
    letI : BorelSpace (I → Circle) := ⟨rfl⟩
    Tendsto (fun n => ambientHaar (Hn n)) atTop (𝓝 (ambientHaar H)) := by
  classical
  let : MeasurableSpace (I → Circle) := borel _
  let : BorelSpace (I → Circle) := ⟨rfl⟩
  let (K : ClosedSubgroup (I → Circle)) : MeasurableSpace K := borel K
  let (K : ClosedSubgroup (I → Circle)) : BorelSpace K := ⟨rfl⟩
  let (K : ClosedSubgroup (I → Circle)) : IsTopologicalGroup K :=
    inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let μ (K : ClosedSubgroup (I → Circle)) : Measure K := Measure.haarMeasure ⊤
  let (K : ClosedSubgroup (I → Circle)) : IsProbabilityMeasure (μ K) :=
    ⟨Measure.haarMeasure_self⟩
  have hmap (K : ClosedSubgroup (I → Circle)) (f : C(I → Circle, ℂ)) :
      ∫ x, f x ∂(ambientHaar K : Measure (I → Circle)) = ∫ x : K, f x ∂μ K :=
    integral_map continuous_subtype_val.measurable.aemeasurable
      f.continuous.aestronglyMeasurable
  have hfinite (n : ℕ) : Metric.hausdorffEDist (Hn n : Set (I → Circle))
      (H : Set (I → Circle)) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      ⟨1, (Hn n).one_mem⟩ ⟨1, H.one_mem⟩
      (Hn n).isClosed'.isCompact.isBounded H.isClosed'.isCompact.isBounded
  have hzero (K : ClosedSubgroup (I → Circle)) (χ : (I → Circle) →* ℂ)
      (hx : ∃ x ∈ K, χ x ≠ 1) : (∫ x : K, χ x ∂μ K) = 0 := by
    obtain ⟨x, hx, hχx⟩ := hx
    have ht := integral_mul_left_eq_self (μ := μ K) (fun y : K => χ y) ⟨x, hx⟩
    change (∫ y : K, χ (x * (y : I → Circle)) ∂μ K) = _ at ht
    simp_rw [χ.map_mul] at ht
    rw [integral_const_mul] at ht
    have he : (χ x - 1) * (∫ y : K, χ y ∂μ K) = 0 := by
      rw [sub_mul, one_mul, ht, sub_self]
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hχx)
  have hchar (χ : (I → Circle) →* ℂ) (hc : Continuous χ) :
      Tendsto (fun n => ∫ x : Hn n, χ x ∂μ (Hn n)) atTop
        (𝓝 (∫ x : H, χ x ∂μ H)) := by
    by_cases ht : ∀ x ∈ H, χ x = 1
    · have hv : (∫ x : H, χ x ∂μ H) = 1 :=
        integral_eq_const (Eventually.of_forall fun x => ht x x.property)
      rw [hv]
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      obtain ⟨δ, hδ, hχδ⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hc)
        (ε / 2) (half_pos hε)
      filter_upwards [h.eventually (gt_mem_nhds hδ)] with n hn
      have hclose : ∀ x : Hn n, ‖χ x - 1‖ ≤ ε / 2 := by
        intro x
        obtain ⟨y, hy, hxy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
          x.property hn (hfinite n)
        have hb := hχδ hxy
        rw [ht y hy, dist_eq_norm] at hb
        exact hb.le
      have hint : Integrable (fun x : Hn n => χ x) (μ (Hn n)) :=
        (hc.comp continuous_subtype_val).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hb := norm_integral_le_of_norm_le_const
        (μ := μ (Hn n)) (Eventually.of_forall hclose)
      rw [integral_sub hint (integrable_const (1 : ℂ))] at hb
      simp only [integral_const, probReal_univ, one_smul, mul_one] at hb
      simpa only [dist_eq_norm] using hb.trans_lt (half_lt_self hε)
    · push Not at ht
      obtain ⟨x, hx, hχx⟩ := ht
      rw [hzero H χ ⟨x, hx, hχx⟩]
      apply tendsto_const_nhds.congr'
      have hd : 0 < dist (χ x) 1 := dist_pos.mpr hχx
      obtain ⟨δ, hδ, hχδ⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hc)
        (dist (χ x) 1) hd
      filter_upwards [h.eventually (gt_mem_nhds hδ)] with n hn
      obtain ⟨y, hy, hyx⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt'
        hx hn (hfinite n)
      have hχy : χ y ≠ 1 := by
        intro he
        have hb := hχδ hyx
        rw [he, dist_comm] at hb
        exact (lt_irrefl _ hb)
      exact (hzero (Hn n) χ ⟨y, hy, hχy⟩).symm
  let e : UnitAddTorus I ≃ₜ (I → Circle) :=
    Homeomorph.piCongrRight (fun _ => AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero)
  let A (K : ClosedSubgroup (I → Circle)) (f : C(UnitAddTorus I, ℂ)) : ℂ :=
    ∫ x, f (e.symm x) ∂(ambientHaar K : Measure (I → Circle))
  have hint (K : ClosedSubgroup (I → Circle)) (f : C(UnitAddTorus I, ℂ)) :
      Integrable (fun x => f (e.symm x)) (ambientHaar K : Measure (I → Circle)) :=
    (f.continuous.comp e.symm.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLip (K : ClosedSubgroup (I → Circle)) : LipschitzWith 1 (A K) := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    change dist (∫ x, f (e.symm x) ∂(ambientHaar K : Measure (I → Circle)))
      (∫ x, g (e.symm x) ∂(ambientHaar K : Measure (I → Circle))) ≤ _
    rw [dist_eq_norm, ← integral_sub (hint K f) (hint K g)]
    have hb := norm_integral_le_of_norm_le_const
      (μ := (ambientHaar K : Measure (I → Circle)))
      (Eventually.of_forall fun x => (f - g).norm_coe_le_norm (e.symm x))
    simpa only [ContinuousMap.sub_apply, probReal_univ, mul_one, NNReal.coe_one,
      one_mul, dist_eq_norm] using hb
  let V : Submodule ℂ C(UnitAddTorus I, ℂ) := {
    carrier := {f | Tendsto (fun n => A (Hn n) f) atTop (𝓝 (A H f))}
    zero_mem' := by
      simp only [Set.mem_ofPred_eq, A, ContinuousMap.zero_apply, integral_zero]
      exact tendsto_const_nhds
    add_mem' := by
      intro f g hf hg
      simpa only [Set.mem_ofPred_eq, A, ContinuousMap.add_apply, integral_add (hint _ f) (hint _ g)] using hf.add hg
    smul_mem' := by
      intro c f hf
      simpa only [Set.mem_ofPred_eq, A, ContinuousMap.smul_apply, integral_smul] using hf.const_smul c }
  have hclosed : IsClosed (V : Set C(UnitAddTorus I, ℂ)) :=
    ((LipschitzWith.uniformEquicontinuous (fun n => A (Hn n)) 1
      (fun n => hLip (Hn n))).equicontinuous).isClosed_setOfPred_tendsto (hLip H).continuous
  have hspan : Submodule.span ℂ (range (mFourier (d := I))) ≤ V := by
    apply Submodule.span_le.mpr
    rintro f ⟨k, rfl⟩
    let χ : (I → Circle) →* ℂ := {
      toFun := fun z => ((∏ i, z i ^ k i : Circle) : ℂ)
      map_one' := by simp
      map_mul' := by intro x y; simp [mul_zpow, Finset.prod_mul_distrib] }
    have hc : Continuous χ := by
      change Continuous (fun z : I → Circle => ((∏ i, z i ^ k i : Circle) : ℂ))
      fun_prop
    have he (z : I → Circle) : mFourier k (e.symm z) = χ z := by
      have hz (i : I) : AddCircle.toCircle (e.symm z i) = z i := by
        change AddCircle.toCircle ((AddCircle.homeomorphCircle one_ne_zero).symm (z i)) = z i
        rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
        exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply (z i)
      simp only [mFourier, ContinuousMap.coe_mk, fourier_apply,
        AddCircle.toCircle_zsmul, hz]
      change (∏ i, Circle.coeHom (z i ^ k i)) = Circle.coeHom (∏ i, z i ^ k i)
      exact (map_prod _ _ _).symm
    change Tendsto (fun n => A (Hn n) (mFourier k)) atTop (𝓝 (A H (mFourier k)))
    have hm (K : ClosedSubgroup (I → Circle)) : A K (mFourier k) = ∫ x : K, χ x ∂μ K := by
      change (∫ x, mFourier k (e.symm x) ∂(ambientHaar K : Measure (I → Circle))) = _
      simp_rw [he]
      exact hmap K ⟨χ, hc⟩
    simp_rw [hm]
    exact hchar χ hc
  have hall : ∀ f : C(UnitAddTorus I, ℂ),
      Tendsto (fun n => A (Hn n) f) atTop (𝓝 (A H f)) := by
    have hv := (Submodule.span ℂ (range (mFourier (d := I)))).topologicalClosure_minimal hspan hclosed
    rw [span_mFourier_closure_eq_top] at hv
    exact fun f => hv (Submodule.mem_top)
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  simpa only [A, ContinuousMap.comp_apply, BoundedContinuousFunction.coe_toContinuousMap,
    ContinuousMap.coe_mk, Homeomorph.apply_symm_apply] using hall (f.toContinuousMap.comp ⟨e, e.continuous⟩)

#print axioms ambientHaar
#print axioms result

end

end D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity
