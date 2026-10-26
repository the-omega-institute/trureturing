/- GID: D5/S3/Geometry/Metric/MetricACSpeed
   generality: G
   mirror-B: D5/B/S3/Geometry/Metric/MetricACSpeed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Slope]
   utility: none
   digest: Metric speed integrability and exact accumulated-variation identities. -/

import D5.S3.Geometry.Metric.VariationPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace Original172

variable {X : Type*} [MetricSpace X]

/-- Port of TauCeti eVariationOn.le_lintegral_of_edist_le_lintegral at
49035f0ebf0e506dc2f1c078374b2dea4ac9c6dd (Apache-2.0).
Retire when the receiving pinned Mathlib supplies this bound and its consumer
can use that declaration directly. -/
private theorem variation_le_lintegral_of_edist_le_lintegral
    {Y : Type*} [PseudoEMetricSpace Y] {γ : ℝ → Y} {m : ℝ → ℝ≥0∞} {a b : ℝ}
    (h : ∀ s ∈ Icc a b, ∀ u ∈ Icc a b,
      edist (γ s) (γ u) ≤ ∫⁻ t in uIoc s u, m t) :
    eVariationOn γ (Icc a b) ≤ ∫⁻ t in Ioc a b, m t := by
  let L (s u : ℝ) := ∫⁻ t in Ioc s u, m t
  have hadd {s u v : ℝ} (hsu : s ≤ u) (huv : u ≤ v) : L s u + L u v = L s v := by
    dsimp [L]
    rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
      Ioc_union_Ioc_eq_Ioc hsu huv]
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  have hsegment (i : ℕ) : edist (γ (u (i + 1))) (γ (u i)) ≤ L (u i) (u (i + 1)) := by
    rw [edist_comm]
    simpa only [L, uIoc_of_le (hu (Nat.le_succ i))] using h _ (hus i) _ (hus (i + 1))
  have hsum (k : ℕ) : ∑ i ∈ Finset.range k, L (u i) (u (i + 1)) = L (u 0) (u k) := by
    induction k with
    | zero => simp [L]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hadd (hu (Nat.zero_le k)) (hu (Nat.le_succ k))]
  calc
    ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i)) ≤
        ∑ i ∈ Finset.range n, L (u i) (u (i + 1)) := Finset.sum_le_sum fun i _ ↦ hsegment i
    _ = L (u 0) (u n) := hsum n
    _ ≤ ∫⁻ t in Ioc a b, m t := lintegral_mono_set (Ioc_subset_Ioc (hus 0).1 (hus n).2)

private theorem ae_interior_Icc {T : ℝ} (hT : 0 < T) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), t ∈ Ioo (0 : ℝ) T := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (show ∀ᵐ t : ℝ ∂volume, t ≠ 0 from by simp [ae_iff]).filter_mono
      (ae_mono Measure.restrict_le_self),
    (show ∀ᵐ t : ℝ ∂volume, t ≠ T from by simp [ae_iff]).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht h0 h1
  exact ⟨lt_of_le_of_ne ht.1 h0.symm, lt_of_le_of_ne ht.2 h1⟩

/- A pointwise lower estimate for the derivative of accumulated variation. -/
private theorem metric_speed_le_variation_deriv {T t r : ℝ} {z : ℝ → X}
    (hT : 0 < T) (hz : AbsolutelyContinuousOnInterval z 0 T)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hA : DifferentiableAt ℝ (variationOnFromTo z (Icc 0 T) 0) t)
    (hr : Tendsto (fun h : ℝ => dist (z (t+h)) (z t) / |h|)
      (𝓝[≠] (0 : ℝ)) (𝓝 r)) :
    r ≤ deriv (variationOnFromTo z (Icc 0 T) 0) t := by
  let A := variationOnFromTo z (Icc 0 T) 0
  have hlim : Tendsto (fun h : ℝ => (A (t+h) - A t) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (deriv A t)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hA.hasDerivAt.tendsto_slope_zero_right
  have hnear : ∀ᶠ h in 𝓝[>] (0 : ℝ), t+h ∈ Icc (0 : ℝ) T := by
    have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hh : Tendsto (fun h : ℝ => t+h) (𝓝[>] (0 : ℝ)) (𝓝 t) := by
      simpa only [add_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => t)
          (𝓝[>] (0 : ℝ)) (𝓝 t)).add hid
    exact hh.eventually (Icc_mem_nhds ht.1 ht.2)
  have hle : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      dist (z (t+h)) (z t) / |h| ≤ (A (t+h) - A t) / h := by
    filter_upwards [hnear, self_mem_nhdsWithin] with h hh hpos
    change 0 < h at hpos
    have hsub : BoundedVariationOn z (Icc t (t+h)) := by
      have hb := metric_AC_boundedVariationOn (Y := X) (f := z) (a := 0) (b := T) hz
      rw [uIcc_of_le hT.le] at hb
      exact hb.mono (Icc_subset_Icc ht.1.le hh.2)
    have hd := hsub.dist_le (x := t+h) (y := t)
      ⟨by linarith, le_rfl⟩ ⟨le_rfl, by linarith⟩
    have hi := metric_AC_variation_exact_increments (X := X) (z := z) (T := T) hT hz
      ⟨ht.1.le, ht.2.le⟩ hh (by linarith : t ≤ t+h)
    change A (t+h) - A t = _ at hi
    rw [abs_of_pos hpos, hi]
    exact div_le_div_of_nonneg_right hd hpos.le
  exact le_of_tendsto_of_tendsto (hr.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))) hlim hle

/- Every fixed distance coordinate is 1-Lipschitz. Its actual derivative is
   controlled by the metric-speed limit, including at zero speed. -/
private theorem abs_deriv_distance_le_metric_speed {z : ℝ → X} {t r : ℝ}
    (q : X) (hd : DifferentiableAt ℝ (fun u => dist (z u) q) t)
    (hr : Tendsto (fun h : ℝ => dist (z (t+h)) (z t) / |h|)
      (𝓝[≠] (0 : ℝ)) (𝓝 r)) :
    |deriv (fun u => dist (z u) q) t| ≤ r := by
  have hlim := hd.hasDerivAt.tendsto_slope_zero.norm
  have hle : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      ‖h⁻¹ • (dist (z (t+h)) q - dist (z t) q)‖ ≤
        dist (z (t+h)) (z t) / |h| := by
    filter_upwards with h
    have hb := abs_dist_sub_le (z (t+h)) (z t) q
    simpa only [norm_smul, Real.norm_eq_abs, abs_inv, div_eq_inv_mul] using
      mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ |h|⁻¹)
  simpa only [Real.norm_eq_abs] using le_of_tendsto_of_tendsto hlim hr hle

/-- A metric AC curve with a measurable actual metric-speed limit has integrable
speed. Its accumulated-variation derivative equals that speed almost everywhere,
and every subinterval variation is its speed integral. No ambient completeness
or separability and no energy hypothesis occur. -/
theorem metric_AC_speed_variation_bridge {T : ℝ} (hT : 0 < T)
    (z : ℝ → X) (hz : AbsolutelyContinuousOnInterval z 0 T)
    (r : ℝ → ℝ) (hr0 : ∀ t, 0 ≤ r t)
    (hrm : AEStronglyMeasurable r (volume.restrict (Icc (0 : ℝ) T)))
    (hrlim : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      Tendsto (fun h : ℝ => dist (z (t+h)) (z t) / |h|)
        (𝓝[≠] (0 : ℝ)) (𝓝 (r t))) :
    IntervalIntegrable r volume 0 T ∧
    (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      deriv (variationOnFromTo z (Icc 0 T) 0) t = r t) ∧
    (∫⁻ t in Icc (0 : ℝ) T, ENNReal.ofReal (r t)) = eVariationOn z (Icc 0 T) ∧
    (∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b →
      (∫ t in a..b, r t) = (eVariationOn z (Icc a b)).toReal) ∧
    (∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b →
      dist (z a) (z b) ≤ ∫ t in a..b, r t) := by
  classical
  let A := variationOnFromTo z (Icc 0 T) 0
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hA : AbsolutelyContinuousOnInterval A 0 T :=
    metric_AC_implies_AC_variation_primitive (X := X) (z := z) (T := T) hT hz
  have hD : Integrable (deriv A) μ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp
      hA.intervalIntegrable_deriv
  have hdom : ∀ᵐ t ∂μ, r t ≤ deriv A t := by
    filter_upwards [hrlim, ae_interior_Icc hT,
      hA.ae_differentiableAt.filter_mono (ae_mono Measure.restrict_le_self)]
      with t ht hi hd
    apply metric_speed_le_variation_deriv hT hz hi
    · exact hd (by rw [uIcc_of_le hT.le]; exact ⟨hi.1.le, hi.2.le⟩)
    · exact ht
  have hri : Integrable r μ := hD.mono_nonneg hrm
    (Eventually.of_forall hr0) hdom
  have hrint : IntervalIntegrable r volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hri
  have hiab (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) T)
      (hb : b ∈ Icc (0 : ℝ) T) (hab : a ≤ b) :
      IntervalIntegrable r volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact hri.mono_measure (Measure.restrict_mono (Icc_subset_Icc ha.1 hb.2) le_rfl)
  have hchord (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) T)
      (hb : b ∈ Icc (0 : ℝ) T) (hab : a ≤ b) :
      dist (z a) (z b) ≤ ∫ t in a..b, r t := by
    let f : ℝ → ℝ := fun t => dist (z t) (z a)
    have hzab : AbsolutelyContinuousOnInterval z a b := by
      apply hz.mono
      rw [uIcc_of_le hT.le, uIcc_of_le hab]
      exact Icc_subset_Icc ha.1 hb.2
    have hf : AbsolutelyContinuousOnInterval f a b :=
      (LipschitzWith.dist_left (z a)).comp_absolutelyContinuousOnInterval hzab
    have hlimab := hrlim.filter_mono
      (ae_mono (Measure.restrict_mono (Icc_subset_Icc ha.1 hb.2) le_rfl))
    have hle : ∀ᵐ t ∂(volume.restrict (Icc a b)), deriv f t ≤ r t := by
      filter_upwards [hlimab, ae_restrict_mem measurableSet_Icc,
        hf.ae_differentiableAt.filter_mono (ae_mono Measure.restrict_le_self)]
        with t ht hi hd
      have hdf : DifferentiableAt ℝ f t := hd (by rwa [uIcc_of_le hab])
      exact (le_abs_self _).trans (abs_deriv_distance_le_metric_speed (z a) hdf ht)
    have h := intervalIntegral.integral_mono_ae_restrict hab
      hf.intervalIntegrable_deriv (hiab a b ha hb hab) hle
    rw [hf.integral_deriv_eq_sub] at h
    simpa only [f, dist_self, sub_zero, dist_comm] using h
  have hV : eVariationOn z (Icc (0 : ℝ) T) ≠ ⊤ := by
    have h := metric_AC_boundedVariationOn (Y := X) (f := z) (a := 0) (b := T) hz
    rwa [uIcc_of_le hT.le] at h
  have hchordE (a : ℝ) (ha : a ∈ Icc (0 : ℝ) T)
      (b : ℝ) (hb : b ∈ Icc (0 : ℝ) T) :
      edist (z a) (z b) ≤ ∫⁻ t in uIoc a b, ENNReal.ofReal (r t) := by
    wlog hab : a ≤ b generalizing a b
    · rw [edist_comm, uIoc_comm]
      exact this b hb a ha (le_of_not_ge hab)
    rw [uIoc_of_le hab,
      ← ofReal_integral_eq_lintegral_ofReal (hiab a b ha hb hab).1
        (Eventually.of_forall hr0),
      ← intervalIntegral.integral_of_le hab, edist_dist]
    exact ENNReal.ofReal_le_ofReal (hchord a b ha hb hab)
  have hupper : eVariationOn z (Icc (0 : ℝ) T) ≤
      ENNReal.ofReal (∫ t in (0 : ℝ)..T, r t) := by
    have h := variation_le_lintegral_of_edist_le_lintegral hchordE
    rw [← ofReal_integral_eq_lintegral_ofReal hrint.1 (Eventually.of_forall hr0),
      ← intervalIntegral.integral_of_le hT.le] at h
    exact h
  have hincrement : A T - A 0 = (eVariationOn z (Icc (0 : ℝ) T)).toReal :=
    metric_AC_variation_exact_increments (X := X) (z := z) (T := T) hT hz ⟨le_rfl, hT.le⟩
      ⟨hT.le, le_rfl⟩ hT.le
  have hlower : (∫ t in (0 : ℝ)..T, r t) ≤
      (eVariationOn z (Icc (0 : ℝ) T)).toReal := by
    have h := intervalIntegral.integral_mono_ae_restrict hT.le hrint
      hA.intervalIntegrable_deriv hdom
    rwa [hA.integral_deriv_eq_sub, hincrement] at h
  have hreal : (∫ t in (0 : ℝ)..T, r t) =
      (eVariationOn z (Icc (0 : ℝ) T)).toReal := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
    rw [ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg_of_forall (μ := volume) hT.le hr0)] at h
    exact le_antisymm hlower h
  have hdeq : deriv A =ᵐ[μ] r := by
    apply EventuallyEq.symm
    apply (integral_eq_iff_of_ae_le hri hD hdom).mp
    have heq : (∫ t in (0 : ℝ)..T, r t) = ∫ t in (0 : ℝ)..T, deriv A t := by
      rw [hA.integral_deriv_eq_sub, hincrement, hreal]
    simpa only [μ, intervalIntegral.integral_of_le hT.le, integral_Icc_eq_integral_Ioc] using heq
  have hlin : (∫⁻ t in Icc (0 : ℝ) T, ENNReal.ofReal (r t)) =
      eVariationOn z (Icc (0 : ℝ) T) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hri (Eventually.of_forall hr0)]
    change ENNReal.ofReal (∫ t in Icc (0 : ℝ) T, r t) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le,
      hreal, ENNReal.ofReal_toReal hV]
  refine ⟨hrint, hdeq, hlin, ?_, (fun a ha b hb hab => hchord a b ha hb hab)⟩
  intro a ha b hb hab
  have hAab : AbsolutelyContinuousOnInterval A a b := by
    apply hA.mono
    rw [uIcc_of_le hT.le, uIcc_of_le hab]
    exact Icc_subset_Icc ha.1 hb.2
  have hglobal : ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) T → deriv A t = r t :=
    (ae_restrict_iff' measurableSet_Icc).mp hdeq
  calc
    (∫ t in a..b, r t) = ∫ t in a..b, deriv A t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hglobal] with t ht hi
      rw [uIoc_of_le hab] at hi
      exact (ht ⟨ha.1.trans hi.1.le, hi.2.trans hb.2⟩).symm
    _ = A b - A a := hAab.integral_deriv_eq_sub
    _ = _ := metric_AC_variation_exact_increments (X := X) (z := z) (T := T) hT hz ha hb hab

end Original172

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
The partition-integral bound above is adapted from TauCeti, revision
49035f0ebf0e506dc2f1c078374b2dea4ac9c6dd. Full license:
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
