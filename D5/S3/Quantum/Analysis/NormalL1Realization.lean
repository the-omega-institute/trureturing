/- GID: D5/S3/Quantum/Analysis/NormalL1Realization
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NormalL1Realization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive normal realization on the entire complex L1 space. -/

/-
admission_basis: escape-witness
escape_witness: exists_normal_L1_extension
exists_normal_L1_extension: proof_shape: content. The initial continuous norm
bound, positive-cone approximation and sharp disjoint-simple bound occur on
the live route to extension on the entire complex L1 space.
continuous_normal_of_unit consumes the domination theorem; codRestrict and
extendOfNorm consume the complete normalDual target.
All private helper declarations are consumed by this existence theorem.
utility none: an arbitrary-space analytic existence theorem, without a finite
certificate, enumeration, numerical checker or bounded reduction.
-/

import D5.S3.Quantum.Analysis.NormalFunctionals
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Normal realization on all complex L1 inputs -/

noncomputable section

open Set MeasureTheory Filter
open scoped ComplexOrder Topology

namespace D5.S3.Quantum.Analysis.NormalL1Realization

open NormalFunctionals

variable {A K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ν : Measure K) [IsFiniteMeasure ν] [ν.WeaklyRegular]

theorem positive_norm_eq_mass (φ : StrongDual ℂ A)
    (hφ : ∀ a : A, 0 ≤ a → 0 ≤ φ a) : ‖φ‖ = (φ 1).re := by
  let P : A →P[ℂ] ℂ :=
    { φ with monotone' := (monotone_iff_map_nonneg _).mpr hφ }
  exact congrArg Complex.re P.ofReal_opNorm_eq_map_one

private def ofRealMap (u : C(K, ℝ)) : C(K, ℂ) :=
  ⟨fun t => (u t : ℂ), by fun_prop⟩

omit [MeasurableSpace K] [BorelSpace K] in
private theorem continuous_normal_of_unit
    (J : C(K, ℂ) →ₗ[ℂ] StrongDual ℂ A)
    (hpos : ∀ g : C(K, ℂ), (∀ t, 0 ≤ g t) → ∀ a : A, 0 ≤ a → 0 ≤ J g a)
    (hn : IsOrderNormal (J 1)) (g : C(K, ℂ)) : IsOrderNormal (J g) := by
  have hpositive (f : C(K, ℂ)) (hf : ∀ x, 0 ≤ f x) : IsOrderNormal (J f) := by
    apply isOrderNormal_of_domination (J 1) hn ‖f‖ (norm_nonneg _) (J f)
    intro a ha
    refine ⟨hpos f hf a ha, ?_⟩
    have hle (x : K) : f x ≤ (‖f‖ : ℂ) := by
      apply Complex.le_def.mpr
      exact ⟨(Complex.re_le_norm _).trans (f.norm_coe_le_norm x),
        (Complex.nonneg_iff.mp (hf x)).2.symm⟩
    have hnonneg : ∀ x, 0 ≤ ((‖f‖ : ℂ) • (1 : C(K, ℂ)) - f) x := by
      intro x
      simpa using sub_nonneg.mpr (hle x)
    have h := hpos _ hnonneg a ha
    apply sub_nonneg.mp
    simpa only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] using h
  let u : C(K, ℝ) := ⟨fun t => max (g t).re 0, by fun_prop⟩
  let v : C(K, ℝ) := ⟨fun t => max (-(g t).re) 0, by fun_prop⟩
  let s : C(K, ℝ) := ⟨fun t => max (g t).im 0, by fun_prop⟩
  let t : C(K, ℝ) := ⟨fun t => max (-(g t).im) 0, by fun_prop⟩
  have he : ofRealMap u - ofRealMap v + Complex.I • (ofRealMap s - ofRealMap t) = g := by
    ext x
    apply Complex.ext <;>
      simp [ofRealMap, u, v, s, t, max_zero_sub_max_neg_zero_eq_self,
        Complex.mul_re, Complex.mul_im]
  have hnpos (w : C(K, ℝ)) (hw : ∀ x, 0 ≤ w x) :
      J (ofRealMap w) ∈ normalDual (A := A) :=
    hpositive _ (fun x => by change (0 : ℂ) ≤ (w x : ℂ); exact_mod_cast hw x)
  rw [← he, map_add, map_sub, map_smul, map_sub]
  exact (normalDual (A := A)).add_mem
    ((normalDual (A := A)).sub_mem (hnpos u (fun _ => le_max_right _ _))
      (hnpos v (fun _ => le_max_right _ _)))
    ((normalDual (A := A)).smul_mem _ ((normalDual (A := A)).sub_mem
      (hnpos s (fun _ => le_max_right _ _)) (hnpos t (fun _ => le_max_right _ _))))

omit [ν.WeaklyRegular] in
private theorem continuous_integrable (g : C(K, ℂ)) : Integrable g ν :=
  (L1.integrable_coeFn (ContinuousMap.toLp 1 ν ℂ g)).congr
    (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) ν g)

omit [ν.WeaklyRegular] in
private theorem norm_toL1 (g : C(K, ℂ)) :
    ‖ContinuousMap.toLp 1 ν ℂ g‖ = ∫ t, ‖g t‖ ∂ν := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae ((ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) ν g).fun_comp norm)

private theorem continuous_norm_bound
    (J : C(K, ℂ) →ₗ[ℂ] StrongDual ℂ A)
    (hpos : ∀ g : C(K, ℂ), (∀ t, 0 ≤ g t) → ∀ a : A, 0 ≤ a → 0 ≤ J g a)
    (hmass : ∀ g : C(K, ℂ), J g 1 = ∫ t, g t ∂ν)
    (g : C(K, ℂ)) : ‖J g‖ ≤ 2 * ‖ContinuousMap.toLp 1 ν ℂ g‖ := by
  let u : C(K, ℝ) := ⟨fun t => max (g t).re 0, by fun_prop⟩
  let v : C(K, ℝ) := ⟨fun t => max (-(g t).re) 0, by fun_prop⟩
  let s : C(K, ℝ) := ⟨fun t => max (g t).im 0, by fun_prop⟩
  let t : C(K, ℝ) := ⟨fun t => max (-(g t).im) 0, by fun_prop⟩
  have hi (w : C(K, ℝ)) : Integrable w ν :=
    (L1.integrable_coeFn (ContinuousMap.toLp 1 ν ℝ w)).congr
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) ν w)
  have hn (w : C(K, ℝ)) (hw : ∀ x, 0 ≤ w x) :
      ‖J (ofRealMap w)‖ = ∫ x, w x ∂ν := by
    rw [positive_norm_eq_mass _ (hpos _ (fun x => by
      change (0 : ℂ) ≤ (w x : ℂ); exact_mod_cast hw x)), hmass]
    change (∫ x, (w x : ℂ) ∂ν).re = _
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have hu := hn u (fun _ => le_max_right _ _)
  have hv := hn v (fun _ => le_max_right _ _)
  have hs := hn s (fun _ => le_max_right _ _)
  have ht := hn t (fun _ => le_max_right _ _)
  have he : ofRealMap u - ofRealMap v + Complex.I • (ofRealMap s - ofRealMap t) = g := by
    ext x
    apply Complex.ext <;>
      simp [ofRealMap, u, v, s, t, max_zero_sub_max_neg_zero_eq_self,
        Complex.mul_re, Complex.mul_im]
  calc
    ‖J g‖ = ‖J (ofRealMap u) - J (ofRealMap v) +
        Complex.I • (J (ofRealMap s) - J (ofRealMap t))‖ := by
      rw [← he, map_add, map_sub, map_smul, map_sub]
    _ ≤ ‖J (ofRealMap u)‖ + ‖J (ofRealMap v)‖ +
        (‖J (ofRealMap s)‖ + ‖J (ofRealMap t)‖) := by
      calc
        _ ≤ ‖J (ofRealMap u) - J (ofRealMap v)‖ +
            ‖Complex.I • (J (ofRealMap s) - J (ofRealMap t))‖ := norm_add_le _ _
        _ ≤ _ := by simpa only [norm_smul, Complex.norm_I, one_mul] using
            add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ = ∫ x, (u x + v x) + (s x + t x) ∂ν := by
      rw [hu, hv, hs, ht]
      exact ((integral_add ((hi u).add (hi v)) ((hi s).add (hi t))).trans
        (congrArg₂ (· + ·) (integral_add (hi u) (hi v))
          (integral_add (hi s) (hi t)))).symm
    _ ≤ ∫ x, 2 * ‖g x‖ ∂ν := by
      apply integral_mono (((hi u).add (hi v)).add ((hi s).add (hi t)))
        ((continuous_integrable ν g).norm.const_mul 2)
      intro x
      change (max (g x).re 0 + max (-(g x).re) 0) +
        (max (g x).im 0 + max (-(g x).im) 0) ≤ _
      have habs (r : ℝ) : max r 0 + max (-r) 0 = |r| := by
        rcases le_total 0 r with hr | hr <;> simp [hr, abs_of_nonneg, abs_of_nonpos]
      rw [habs, habs]
      linarith [Complex.abs_re_le_norm (g x), Complex.abs_im_le_norm (g x)]
    _ = 2 * ‖ContinuousMap.toLp 1 ν ℂ g‖ := by
      rw [integral_const_mul, norm_toL1 ν]

private theorem positive_projection_dist (z w : ℂ) (hw : 0 ≤ w) :
    ‖((max z.re 0 : ℝ) : ℂ) - w‖ ≤ ‖z - w‖ := by
  have hwi : w.im = 0 := (Complex.nonneg_iff.mp hw).2.symm
  have hwr : 0 ≤ w.re := (Complex.nonneg_iff.mp hw).1
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  have hsq : ‖((max z.re 0 : ℝ) : ℂ) - w‖ ^ 2 ≤ ‖z - w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, hwi, sub_zero]
    by_cases hz : 0 ≤ z.re
    · rw [max_eq_left hz]
      nlinarith [sq_nonneg z.im]
    · rw [max_eq_right (le_of_not_ge hz)]
      nlinarith [sq_nonneg z.im, sq_nonneg z.re]
  simpa only [pow_two] using hsq

private theorem nonneg_mem_closure_continuous (h : K →₁[ν] ℂ)
    (hh : ∀ᵐ t ∂ν, 0 ≤ h t) :
    h ∈ closure {f : K →₁[ν] ℂ | ∃ g : C(K, ℂ),
      (∀ t, 0 ≤ g t) ∧ ContinuousMap.toLp 1 ν ℂ g = f} := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hd := ContinuousMap.toLp_denseRange (E := ℂ) ν ℂ (p := 1) (by simp)
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := Metric.mem_closure_iff.mp (hd h) ε hε
  let p : C(K, ℂ) := ⟨fun t => ((max (g t).re 0 : ℝ) : ℂ), by fun_prop⟩
  refine ⟨ContinuousMap.toLp 1 ν ℂ p, ⟨p, ?_, rfl⟩, ?_⟩
  · intro t
    change (0 : ℂ) ≤ ((max (g t).re 0 : ℝ) : ℂ)
    exact_mod_cast le_max_right (g t).re 0
  · rw [dist_comm, dist_eq_norm]
    rw [dist_comm, dist_eq_norm] at hg
    refine lt_of_le_of_lt (Lp.norm_le_norm_of_ae_le (p := 1) ?_) hg
    filter_upwards [hh, Lp.coeFn_sub (ContinuousMap.toLp 1 ν ℂ p) h,
      Lp.coeFn_sub (ContinuousMap.toLp 1 ν ℂ g) h,
      ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) ν p, ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) ν g] with t ht hp hg hpt hgt
    rw [hp, hg, Pi.sub_apply, Pi.sub_apply, hpt, hgt]
    exact positive_projection_dist (g t) (h t) ht

/-- A positive map on continuous functions with normal values and its scalar mass
measure extends to the entire complex L1 space. No support or nonzero-mass
assumption is imposed. -/
theorem exists_normal_L1_extension
    (J : C(K, ℂ) →ₗ[ℂ] StrongDual ℂ A)
    (hpos : ∀ g : C(K, ℂ), (∀ t, 0 ≤ g t) → ∀ a : A, 0 ≤ a → 0 ≤ J g a)
    (hnormal : IsOrderNormal (J 1))
    (hmass : ∀ g : C(K, ℂ), J g 1 = ∫ t, g t ∂ν) :
    ∃ Γ : (K →₁[ν] ℂ) →L[ℂ] StrongDual ℂ A,
      (∀ g : C(K, ℂ), Γ (ContinuousMap.toLp 1 ν ℂ g) = J g) ∧
      (∀ h : K →₁[ν] ℂ, IsOrderNormal (Γ h)) ∧
      (∀ h : K →₁[ν] ℂ, (∀ᵐ t ∂ν, 0 ≤ h t) →
        ∀ a : A, 0 ≤ a → 0 ≤ Γ h a) ∧
      (∀ h : K →₁[ν] ℂ, Γ h 1 = ∫ t, h t ∂ν) ∧ ‖Γ‖ ≤ 1 := by
  let e := (ContinuousMap.toLp 1 ν ℂ (E := ℂ)).toLinearMap
  have hd : DenseRange e := ContinuousMap.toLp_denseRange ℂ ν ℂ (by simp)
  have hb : ∀ g, ‖J g‖ ≤ 2 * ‖e g‖ := continuous_norm_bound ν J hpos hmass
  let F : C(K, ℂ) →ₗ[ℂ] normalDual (A := A) :=
    J.codRestrict (normalDual (A := A)) (continuous_normal_of_unit J hpos hnormal)
  have hbF : ∀ g, ‖F g‖ ≤ 2 * ‖e g‖ := hb
  let Γ : (K →₁[ν] ℂ) →L[ℂ] StrongDual ℂ A :=
    (normalDual (A := A)).subtypeL.comp (F.extendOfNorm e)
  have he (g : C(K, ℂ)) : Γ (e g) = J g :=
    congrArg Subtype.val (LinearMap.extendOfNorm_eq hd ⟨2, hbF⟩ g)
  have hn (h : K →₁[ν] ℂ) : IsOrderNormal (Γ h) :=
    (F.extendOfNorm e h).property
  have hm (h : K →₁[ν] ℂ) : Γ h 1 = ∫ t, h t ∂ν := by
    refine hd.induction_on h (isClosed_eq (by fun_prop) continuous_integral) ?_
    intro g
    rw [he, hmass]
    exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) ν g).symm
  have hp (h : K →₁[ν] ℂ) (hh : ∀ᵐ t ∂ν, 0 ≤ h t)
      (a : A) (ha : 0 ≤ a) : 0 ≤ Γ h a := by
    have hc : IsClosed {f : K →₁[ν] ℂ | 0 ≤ Γ f a} :=
      isClosed_le continuous_const (by fun_prop)
    apply closure_minimal (s := {f : K →₁[ν] ℂ | ∃ g : C(K, ℂ),
      (∀ t, 0 ≤ g t) ∧ ContinuousMap.toLp 1 ν ℂ g = f}) ?_ hc
      (nonneg_mem_closure_continuous ν h hh)
    rintro f ⟨g, hg, rfl⟩
    change 0 ≤ Γ (e g) a
    rw [he]
    exact hpos g hg a ha
  refine ⟨Γ, he, hn, hp, hm, ?_⟩
  apply Γ.opNorm_le_bound zero_le_one
  intro h
  change ‖Γ h‖ ≤ 1 * ‖h‖
  rw [one_mul]
  refine Lp.induction (p := 1) (by simp) (fun h => ‖Γ h‖ ≤ ‖h‖) ?_ ?_ ?_ h
  · intro c s hs hμs
    change ‖Γ (indicatorConstLp 1 hs hμs.ne c)‖ ≤
      ‖indicatorConstLp 1 hs hμs.ne c‖
    let u := indicatorConstLp 1 hs hμs.ne (1 : ℂ)
    have hu : ∀ᵐ t ∂ν, 0 ≤ u t := by
      filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs.ne) (c := (1 : ℂ))] with t ht
      rw [ht]
      exact indicator_nonneg (fun _ _ => zero_le_one) t
    have hnu : ‖Γ u‖ = (ν s).toReal := by
      rw [positive_norm_eq_mass _ (hp u hu), hm]
      rw [integral_congr_ae (indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs.ne) (c := (1 : ℂ)))]
      simp [hs, measureReal_def]
    have hcu : indicatorConstLp 1 hs hμs.ne c = c • u := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs.ne) (c := c),
        Lp.coeFn_smul c u, indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs.ne) (c := (1 : ℂ))] with t ht hst hut
      rw [ht, hst, Pi.smul_apply, hut]
      by_cases hts : t ∈ s <;> simp [hts]
    rw [hcu, map_smul, norm_smul, hnu]
    simp [norm_smul, norm_indicatorConstLp, u, measureReal_def]
  · intro f g hf hg hfg ihf ihg
    calc
      ‖Γ (hf.toLp f + hg.toLp g)‖ ≤ ‖Γ (hf.toLp f)‖ + ‖Γ (hg.toLp g)‖ := by
        rw [map_add]; exact norm_add_le _ _
      _ ≤ ‖hf.toLp f‖ + ‖hg.toLp g‖ := add_le_add ihf ihg
      _ = ‖hf.toLp f + hg.toLp g‖ := by
        rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm, L1.norm_eq_integral_norm,
          ← integral_add (L1.integrable_coeFn _).norm (L1.integrable_coeFn _).norm]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
          with t hadd hft hgt
        rw [hadd, Pi.add_apply, hft, hgt]
        have hz : f t = 0 ∨ g t = 0 := by
          by_contra! hz
          exact Set.disjoint_left.mp hfg (Function.mem_support.mpr hz.1)
            (Function.mem_support.mpr hz.2)
        rcases hz with hz | hz <;> simp [hz]
  · exact isClosed_le (by fun_prop) continuous_norm

#print axioms exists_normal_L1_extension

end D5.S3.Quantum.Analysis.NormalL1Realization
