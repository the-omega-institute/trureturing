/- GID: D5/S3/TotalVariation/Asymptotics/StatLeanSignedSmoothing
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/StatLeanSignedSmoothing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier bounds for probability distribution functions against signed integrable densities. -/

/-
Ported from https://github.com/StatLean/Stat-Lean
at immutable revision e1ef06bf52d2a8896439c5b59d982d9aad28a254.
Copyright 2024 Junwei Lu. The upstream LICENSE at this exact revision is
modified Apache-2.0 text, not the standard Apache-2.0 full text. Its complete
original terms and attribution are retained verbatim below.
Upstream LICENSE SHA-256:
  d5945fe0f38866a919940212b0e3b5b0c30629b923c3e26dcce026571a29cd93
The upstream heading identifies Apache License, Version 2.0, but its text differs:
the Contribution definition begins "shall mean, as submitted"; section 4 changes
the paragraph on licensing modifications and additional grants; section 8 uses
"exemplary" instead of "consequential" damages; section 9 changes the warranty
obligations and says exclusions may conflict with this License; and the appendix
says additional terms or conditions may be added. These differences are present
in upstream's LICENSE; they were not introduced by this port. This notice
identifies the source text and does not replace or amend its terms.

Original sources:
  StatLean/HypothesisTesting/ForMathlib/EsseenSmoothing.lean
  StatLean/HypothesisTesting/ForMathlib/BerryEsseen.lean
  StatLean/HypothesisTesting/Bootstrap/Edgeworth.lean
  StatLean/HypothesisTesting/Bootstrap/Consistency.lean

The immutable upstream tree contains LICENSE and no NOTICE file.
Upstream: Lean v4.29.1, Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6.
This repository: Lean v4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
Adaptations preserve original names and statements: retain the live source closure
and consolidate imports. Expose tentC, sqSincC, integrable_sqSincC, gTent,
fourier_gTent, charFunDensity_eq_fourier, abs_pow_le_exp, and
integrable_abs_pow_mul_gauss. Replace Integrable.bdd_mul' by Integrable.bdd_mul;
let Complex.ofRealCLM.hasDerivAt infer its point; use convert! where convert
changed elaboration behavior; supply ha explicitly to field_simp in
integral_linear_mul_cexp. In integrable_stdNormalPDF_mul_pow and
exp_neg_half_sq_mul_abs_pow_le, use the original BerryEsseen declarations
integrable_abs_pow_mul_gauss and abs_pow_le_exp directly in place of the
upstream Edgeworth aliases integrable_abs_pow_mul_exp_neg_half_sq and
abs_pow_le_const_mul_exp_sq_div_four. No new supplier theorem is asserted.
Retirement condition: when this repository's pinned Mathlib contains equivalent
statements, replace the corresponding port by direct imports.
-/

/-
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

      "Work" shall mean the work of authorship made available under
      the License, as indicated by a copyright notice that is included in
      or attached to the work (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean, as submitted to the Licensor for inclusion
      in the Work by the copyright owner or by an individual or Legal Entity
      authorized to submit on behalf of the copyright owner. For the purposes
      of this definition, "submitted" means any form of electronic, verbal,
      or written communication sent to the Licensor or its representatives,
      including but not limited to communication on electronic mailing lists,
      source code control systems, and issue tracking systems that are managed
      by, or on behalf of, the Licensor for the purpose of discussing and
      improving the Work, but excluding communication that is conspicuously
      marked or otherwise designated in writing by the copyright owner as
      "Not a Contribution."

      "Contributor" shall mean Licensor and any Legal Entity on behalf of
      whom a Contribution has been received by the Licensor and subsequently
      incorporated within the Work.

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
      institute patent litigation against any entity (including a cross-claim
      or counterclaim in a lawsuit) alleging that the Work or any
      Contribution embodied within the Work constitutes direct or contributory
      patent infringement, then any patent licenses granted to You under
      this License for that Work shall terminate as of the date such
      litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or Derivative Works
          a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, You must include a readable copy of the attribution
          notices contained within such NOTICE file, in at least one of the
          following places: within a NOTICE text file distributed as part of
          the Derivative Works; within the Source form or documentation, if
          provided along with the Derivative Works; or, within a display
          generated by the Derivative Works, if and wherever such third-party
          notices normally appear. The contents of the NOTICE file are for
          informational purposes only and do not modify the License. You may
          add Your own attribution notices within Derivative Works that You
          distribute, alongside or as an addendum to the NOTICE text from the
          Work, provided that such additional attribution notices cannot be
          construed as modifying the License.

      You may add Your own license statement for Your modifications and
      may provide additional grant of rights to use, copy, modify, merge,
      publish, distribute, sublicense, and/or sell copies of the Work,
      as permitted under this License.

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
      appropriateness of using or reproducing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or exemplary damages of any character arising as a result
      of this License or out of the use or inability to use the Work
      (including but not limited to damages for loss of goodwill, work
      stoppage, computer failure or malfunction, or all other commercial
      damages or losses), even if such Contributor has been advised of the
      possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer, and
      charge a fee for, acceptance of support, warranty, indemnity, or
      other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may offer only
      conditions consistent with this License. You may add additional
      exclusion of warranty clauses, if such exclusions conflict with this
      License, or if required to do so for any reason. You should read all
      applicable laws and regulations before distributing your Work.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format in question. You may also add
      additional terms or conditions for use.

   Copyright 2024 Junwei Lu

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

import D5.S3.TotalVariation.Asymptotics.StatLeanFourierCore

section
open MeasureTheory intervalIntegral
open scoped FourierTransform Real Topology
namespace StatLean.HypothesisTesting
variable {q : ℝ → ℝ}

noncomputable def densityCDF (q : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in Set.Iic x, q y

noncomputable def charFunDensity (q : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * (q y : ℂ)

private lemma integrable_ramp_mul (hq : Integrable q) (u δ : ℝ) :
    Integrable (fun y : ℝ => ramp u δ y * q y) :=
  hq.bdd_mul (c := 1) (continuous_ramp u δ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ramp_nonneg u δ y)]; exact ramp_le_one u δ y)

theorem abs_integral_ramp_mul_sub_densityCDF_le (hq : Integrable q) {δ A : ℝ} (hδ : 0 < δ)
    (hA : ∀ a b : ℝ, a ≤ b → (∫ y in Set.Ioc a b, |q y|) ≤ A * (b - a)) (u : ℝ) :
    |(∫ y : ℝ, ramp u δ y * q y) - densityCDF q u| ≤ A * δ := by
  have h1 : Integrable (fun y : ℝ => ramp u δ y * q y) := integrable_ramp_mul hq u δ
  have h2 : Integrable (Set.indicator (Set.Iic u) q) := hq.indicator measurableSet_Iic
  have hmaj : Integrable (Set.indicator (Set.Ioc u (u + δ)) fun y => |q y|) :=
    hq.abs.indicator measurableSet_Ioc
  have hd : densityCDF q u = ∫ y : ℝ, Set.indicator (Set.Iic u) q y :=
    (MeasureTheory.integral_indicator measurableSet_Iic).symm
  have hpt : ∀ y : ℝ, ‖ramp u δ y * q y - Set.indicator (Set.Iic u) q y‖
      ≤ Set.indicator (Set.Ioc u (u + δ)) (fun y => |q y|) y := by
    intro y
    rcases le_or_gt y u with hy | hy
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy), ramp_eq_one_of_le hδ hy, one_mul, sub_self,
        norm_zero]
      exact Set.indicator_apply_nonneg fun _ => abs_nonneg _
    · rw [Set.indicator_of_notMem (by simpa using hy)]
      rcases le_or_gt y (u + δ) with hy2 | hy2
      · rw [Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hy, hy2⟩), sub_zero, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (ramp_nonneg u δ y)]
        exact mul_le_of_le_one_left (abs_nonneg _) (ramp_le_one u δ y)
      · rw [Set.indicator_of_notMem (by simp [not_le.2 hy2]),
          ramp_eq_zero_of_le hδ hy2.le, zero_mul, sub_zero, norm_zero]
  calc |(∫ y : ℝ, ramp u δ y * q y) - densityCDF q u|
      = ‖∫ y : ℝ, (ramp u δ y * q y - Set.indicator (Set.Iic u) q y)‖ := by
        rw [integral_sub h1 h2, hd, Real.norm_eq_abs]
    _ ≤ ∫ y : ℝ, Set.indicator (Set.Ioc u (u + δ)) (fun y => |q y|) y :=
        norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall hpt)
    _ = ∫ y in Set.Ioc u (u + δ), |q y| := MeasureTheory.integral_indicator measurableSet_Ioc
    _ ≤ A * δ := by simpa using hA u (u + δ) (by linarith)

theorem abs_measure_Iic_sub_densityCDF_le_of_integral_ramp {P : Measure ℝ}
    [IsProbabilityMeasure P] (hq : Integrable q) {δ E A : ℝ} (hδ : 0 < δ)
    (hA : ∀ a b : ℝ, a ≤ b → (∫ y in Set.Ioc a b, |q y|) ≤ A * (b - a))
    (hE : ∀ u : ℝ, |(∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y| ≤ E) (x : ℝ) :
    |(P (Set.Iic x)).toReal - densityCDF q x| ≤ E + 2 * (A * δ) := by
  have hAnn : 0 ≤ A * δ := le_trans (abs_nonneg _)
    (abs_integral_ramp_mul_sub_densityCDF_le hq hδ hA 0)
  have hlip : ∀ a b : ℝ, a ≤ b → |densityCDF q b - densityCDF q a| ≤ A * (b - a) := by
    intro a b hab
    have hunion : (∫ y in Set.Iic b, q y)
        = (∫ y in Set.Iic a, q y) + ∫ y in Set.Ioc a b, q y := by
      rw [← setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        hq.integrableOn hq.integrableOn, Set.Iic_union_Ioc_eq_Iic hab]
    have hsub : densityCDF q b - densityCDF q a = ∫ y in Set.Ioc a b, q y := by
      unfold densityCDF
      rw [hunion]
      ring
    rw [hsub]
    calc |∫ y in Set.Ioc a b, q y| ≤ ∫ y in Set.Ioc a b, |q y| := by
          simpa using MeasureTheory.norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Ioc a b)) q
      _ ≤ A * (b - a) := hA a b hab
  refine abs_le.2 ⟨?_, ?_⟩
  · have h1 : (∫ y, ramp (x - δ) δ y ∂P) ≤ (P (Set.Iic x)).toReal := by
      have := integral_ramp_le_measure_Iic P hδ (x - δ)
      simpa using this
    have h2 := abs_le.1 (abs_integral_ramp_mul_sub_densityCDF_le hq hδ hA (x - δ))
    have h3 := abs_le.1 (hlip (x - δ) x (by linarith))
    have h4 := abs_le.1 (hE (x - δ))
    simp only [sub_sub_cancel] at h3
    linarith [h2.1, h3.1, h4.1]
  · have h1 : (P (Set.Iic x)).toReal ≤ ∫ y, ramp x δ y ∂P :=
      measure_Iic_le_integral_ramp P hδ x
    have h2 := abs_le.1 (abs_integral_ramp_mul_sub_densityCDF_le hq hδ hA x)
    have h4 := abs_le.1 (hE x)
    linarith [h2.2, h4.2]

private lemma tendsto_setIntegral_abs_Iic_atBot (hq : Integrable q) :
    Filter.Tendsto (fun t : ℝ => ∫ y in Set.Iic t, |q y|) Filter.atBot (𝓝 0) := by
  have hinter : (⋂ t : ℝ, Set.Iic (-t)) = (∅ : Set ℝ) := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have := Set.mem_iInter.1 hx (-x + 1)
    simp only [Set.mem_Iic] at this
    linarith
  have hanti : Filter.Tendsto (fun t : ℝ => ∫ y in Set.Iic (-t), |q y|) Filter.atTop
      (𝓝 (∫ y in ⋂ t : ℝ, Set.Iic (-t), |q y|)) :=
    tendsto_setIntegral_of_antitone (fun _ => measurableSet_Iic)
      (fun s t hst => Set.Iic_subset_Iic.2 (by linarith)) ⟨0, hq.abs.integrableOn⟩
  rw [hinter, setIntegral_empty] at hanti
  have := hanti.comp Filter.tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this

private lemma tendsto_integral_ramp_mul_atBot (hq : Integrable q) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun v : ℝ => ∫ y : ℝ, ramp v δ y * q y) Filter.atBot (𝓝 0) := by
  have hbd : ∀ v : ℝ, ‖∫ y : ℝ, ramp v δ y * q y‖ ≤ ∫ y in Set.Iic (v + δ), |q y| := by
    intro v
    have hmaj : Integrable (Set.indicator (Set.Iic (v + δ)) fun y => |q y|) :=
      hq.abs.indicator measurableSet_Iic
    have hpt : ∀ y : ℝ, ‖ramp v δ y * q y‖
        ≤ Set.indicator (Set.Iic (v + δ)) (fun y => |q y|) y := by
      intro y
      rcases le_or_gt y (v + δ) with hy | hy
      · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy), Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (ramp_nonneg v δ y)]
        exact mul_le_of_le_one_left (abs_nonneg _) (ramp_le_one v δ y)
      · rw [Set.indicator_of_notMem (by simpa using hy), ramp_eq_zero_of_le hδ hy.le,
          zero_mul, norm_zero]
    exact (norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall hpt)).trans_eq
      (MeasureTheory.integral_indicator measurableSet_Iic)
  refine squeeze_zero_norm hbd ?_
  exact (tendsto_setIntegral_abs_Iic_atBot hq).comp
    (Filter.tendsto_atBot_add_const_right _ δ Filter.tendsto_id)

theorem abs_integral_ramp_mul_sub_le_of_trapezoid {P : Measure ℝ} [IsProbabilityMeasure P]
    (hq : Integrable q) {u δ E : ℝ} (hδ : 0 < δ)
    (hE : ∀ v : ℝ, v + δ ≤ u →
      |(∫ y, trapezoid v u δ y ∂P) - ∫ y : ℝ, trapezoid v u δ y * q y| ≤ E) :
    |(∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y| ≤ E := by
  have hsplit : ∀ v : ℝ,
      (∫ y, trapezoid v u δ y ∂P) - ∫ y : ℝ, trapezoid v u δ y * q y
        = ((∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y)
          - ((∫ y, ramp v δ y ∂P) - ∫ y : ℝ, ramp v δ y * q y) := by
    intro v
    have hP : (∫ y, trapezoid v u δ y ∂P)
        = (∫ y, ramp u δ y ∂P) - ∫ y, ramp v δ y ∂P := by
      simp only [trapezoid]
      exact integral_sub (integrable_ramp P u δ) (integrable_ramp P v δ)
    have hQ : (∫ y : ℝ, trapezoid v u δ y * q y)
        = (∫ y : ℝ, ramp u δ y * q y) - ∫ y : ℝ, ramp v δ y * q y := by
      rw [← integral_sub (integrable_ramp_mul hq u δ) (integrable_ramp_mul hq v δ)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp only [trapezoid]; ring)
    rw [hP, hQ]
    ring
  have hlim : Filter.Tendsto (fun v : ℝ =>
      |(∫ y, trapezoid v u δ y ∂P) - ∫ y : ℝ, trapezoid v u δ y * q y|) Filter.atBot
      (𝓝 |(∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y|) := by
    simp_rw [hsplit]
    have hmain : Filter.Tendsto (fun v : ℝ =>
        ((∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y)
          - ((∫ y, ramp v δ y ∂P) - ∫ y : ℝ, ramp v δ y * q y)) Filter.atBot
        (𝓝 (((∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y) - (0 - 0))) :=
      tendsto_const_nhds.sub
        ((tendsto_integral_ramp_atBot P hδ).sub (tendsto_integral_ramp_mul_atBot hq hδ))
    simpa using hmain.abs
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_le_atBot (u - δ)] with v hv using hE v (by linarith)

lemma charFunDensity_eq_fourier (q : ℝ → ℝ) (ξ : ℝ) :
    charFunDensity q (-(2 * π * ξ)) = 𝓕 (fun y : ℝ => (q y : ℂ)) ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, charFunDensity]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

theorem integral_fourier_density (hq : Integrable q) {g : ℝ → ℂ} (hg : Integrable g) :
    (∫ x : ℝ, 𝓕 g x * (q x : ℂ)) = ∫ ξ : ℝ, charFunDensity q (-(2 * π * ξ)) * g ξ := by
  have hL : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2 := continuous_inner
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [LinearMap.flip_apply, innerₗ_apply_apply]
    exact real_inner_comm x y
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := innerₗ ℝ) (f := fun y : ℝ => (q y : ℂ)) (g := g)
    Real.continuous_fourierChar hL hq.ofReal hg
  rw [hflip] at key
  have hchar : ∀ ξ : ℝ,
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
          (fun y : ℝ => (q y : ℂ)) ξ
        = charFunDensity q (-(2 * π * ξ)) := fun ξ => (charFunDensity_eq_fourier q ξ).symm
  have hfour : ∀ x : ℝ,
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g x = 𝓕 g x :=
    fun _ => rfl
  simp only [hchar, hfour, smul_eq_mul] at key
  rw [show (∫ x : ℝ, 𝓕 g x * (q x : ℂ)) = ∫ x : ℝ, (q x : ℂ) * 𝓕 g x from
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)]
  exact key.symm

private lemma norm_charFunDensity_le (t : ℝ) :
    ‖charFunDensity q t‖ ≤ ∫ y : ℝ, |q y| := by
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq (integral_congr_ae
    (Filter.Eventually.of_forall fun y => ?_))
  have hone : ‖Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp, show (((t : ℂ) * (y : ℂ) * Complex.I)).re = 0 by simp, Real.exp_zero]
  simp only [norm_mul, hone, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_integral_fourier_sub_density_le {P : Measure ℝ} [IsProbabilityMeasure P]
    (hq : Integrable q) {g : ℝ → ℂ} (hg : Integrable g) :
    ‖(∫ x : ℝ, 𝓕 g x ∂P) - ∫ x : ℝ, 𝓕 g x * (q x : ℂ)‖
      ≤ ∫ ξ : ℝ, ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖ * ‖g ξ‖ := by
  have hsm : Measurable fun ξ : ℝ => -(2 * π * ξ) := by fun_prop
  have hcontq : Continuous fun ξ : ℝ => charFunDensity q (-(2 * π * ξ)) := by
    simp only [charFunDensity_eq_fourier]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hq.ofReal
  have hP : Integrable (fun ξ : ℝ => charFun P (-(2 * π * ξ)) * g ξ) :=
    hg.bdd_mul (measurable_charFun.comp hsm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => norm_charFun_le_one _)
  have hQ : Integrable (fun ξ : ℝ => charFunDensity q (-(2 * π * ξ)) * g ξ) :=
    hg.bdd_mul hcontq.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => norm_charFunDensity_le _)
  rw [integral_fourier_measure hg, integral_fourier_density hq hg, ← integral_sub hP hQ]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq
    (integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_))
  dsimp only
  rw [← sub_mul, norm_mul]

theorem abs_measure_Iic_sub_densityCDF_le_charFun {P : Measure ℝ} [IsProbabilityMeasure P]
    (hq : Integrable q) {δ A : ℝ} (hδ : 0 < δ)
    (hA : ∀ a b : ℝ, a ≤ b → (∫ y in Set.Ioc a b, |q y|) ≤ A * (b - a))
    (hint : Integrable (fun ξ : ℝ =>
      ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖
        * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2))))
    (x : ℝ) :
    |(P (Set.Iic x)).toReal - densityCDF q x|
      ≤ (∫ ξ : ℝ, ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖
          * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2))) + 2 * (A * δ) := by
  refine abs_measure_Iic_sub_densityCDF_le_of_integral_ramp hq hδ hA (fun u => ?_) x
  refine abs_integral_ramp_mul_sub_le_of_trapezoid hq hδ (fun v hvu => ?_)
  obtain ⟨g, hgint, hgfour, hgnorm⟩ := exists_fourier_trapezoid hδ hvu
  have hcastP : (∫ y : ℝ, 𝓕 g y ∂P) = ((∫ y : ℝ, trapezoid v u δ y ∂P : ℝ) : ℂ) := by
    simp_rw [hgfour]
    exact integral_complex_ofReal
  have hcastQ : (∫ y : ℝ, 𝓕 g y * (q y : ℂ))
      = ((∫ y : ℝ, trapezoid v u δ y * q y : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hgfour]
    push_cast
    ring
  have hnormeq : ‖(∫ y : ℝ, 𝓕 g y ∂P) - ∫ y : ℝ, 𝓕 g y * (q y : ℂ)‖
      = |(∫ y : ℝ, trapezoid v u δ y ∂P) - ∫ y : ℝ, trapezoid v u δ y * q y| := by
    rw [hcastP, hcastQ, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hbound : ∀ ξ : ℝ,
      ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖ * ‖g ξ‖
        ≤ ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖
          * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)) :=
    fun ξ => mul_le_mul_of_nonneg_left (hgnorm ξ) (norm_nonneg _)
  have hsm : Measurable fun ξ : ℝ => -(2 * π * ξ) := by fun_prop
  have hcontq : Continuous fun ξ : ℝ => charFunDensity q (-(2 * π * ξ)) := by
    simp only [charFunDensity_eq_fourier]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hq.ofReal
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℝ => ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖ * ‖g ξ‖)
      volume :=
    (((measurable_charFun.comp hsm).aestronglyMeasurable.sub
      hcontq.aestronglyMeasurable).norm).mul hgint.aestronglyMeasurable.norm
  have hLint : Integrable (fun ξ : ℝ =>
      ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖ * ‖g ξ‖) :=
    hint.mono' hmeas (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound ξ)
  rw [← hnormeq]
  exact (norm_integral_fourier_sub_density_le hq hgint).trans
    (integral_mono hLint hint hbound)

end StatLean.HypothesisTesting
end
