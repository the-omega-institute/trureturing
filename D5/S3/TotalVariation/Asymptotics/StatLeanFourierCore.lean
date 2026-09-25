/- GID: D5/S3/TotalVariation/Asymptotics/StatLeanFourierCore
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/StatLeanFourierCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fejer Fourier inversion, ramp approximation, and Fourier representations of trapezoids. -/

/-
Ported from https://github.com/StatLean/Stat-Lean
at immutable revision e1ef06bf52d2a8896439c5b59d982d9aad28a254.
Copyright 2024 Junwei Lu. Licensed under Apache-2.0 (full text below).

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

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

section
open MeasureTheory intervalIntegral
open scoped FourierTransform Real Topology
namespace StatLean.HypothesisTesting
variable {q : ℝ → ℝ}


noncomputable def fejerKernel (T x : ℝ) : ℝ :=
  (T / (2 * π)) * (Real.sin (T * x / 2) / (T * x / 2)) ^ 2

noncomputable def tent (x : ℝ) : ℝ := max 0 (1 - |x|)

lemma tent_zero : tent 0 = 1 := by simp [tent]

lemma tent_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : tent x = 0 := by
  simp [tent, sub_nonpos.2 hx]

lemma tent_of_mem_Icc_zero_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : tent x = 1 - x := by
  have h : |x| = x := abs_of_nonneg hx.1
  simp only [tent, h]
  exact max_eq_right (by linarith [hx.2])

lemma tent_of_mem_Icc_neg_one_zero {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 0) :
    tent x = 1 + x := by
  have h : |x| = -x := abs_of_nonpos hx.2
  simp only [tent, h, sub_neg_eq_add]
  exact max_eq_right (by linarith [hx.1])

lemma continuous_tent : Continuous tent := by
  unfold tent; fun_prop

lemma tent_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) : tent x = 0 := by
  refine tent_of_one_le_abs ?_
  rcases not_and_or.1 (fun h => hx ⟨h.1, h.2⟩) with h | h
  · rw [abs_of_nonpos (by linarith [not_le.1 h])]; linarith [not_le.1 h]
  · rw [abs_of_nonneg (by linarith [not_le.1 h])]; linarith [not_le.1 h]

private lemma integral_linear_mul_cexp {a : ℂ} (ha : a ≠ 0) (c : ℂ) (p q : ℝ) :
    (∫ v in p..q, (c + (v : ℂ)) * Complex.exp (a * v)) =
      ((c + (q : ℂ)) / a - 1 / a ^ 2) * Complex.exp (a * q) -
        ((c + (p : ℂ)) / a - 1 / a ^ 2) * Complex.exp (a * p) := by
  have hderiv : ∀ v : ℝ, HasDerivAt
      (fun w : ℝ => ((c + (w : ℂ)) / a - 1 / a ^ 2) * Complex.exp (a * w))
      ((c + (v : ℂ)) * Complex.exp (a * v)) v := by
    intro v
    have hb : HasDerivAt (fun w : ℝ => (w : ℂ)) 1 v := by
      exact Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun w : ℝ => (c + (w : ℂ)) / a - 1 / a ^ 2) (1 / a) v := by
      simpa using ((hb.const_add c).div_const a).sub_const (1 / a ^ 2)
    have h2 : HasDerivAt (fun w : ℝ => Complex.exp (a * w))
        (Complex.exp (a * v) * a) v := by
      simpa using ((hb.const_mul a).cexp)
    have := h1.mul h2
    convert! this using 1 <;> field_simp [ha] <;> ring
  have hint : IntervalIntegrable (fun v : ℝ => (c + (v : ℂ)) * Complex.exp (a * v))
      MeasureTheory.volume p q := by
    apply Continuous.intervalIntegrable
    fun_prop
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint

noncomputable def tentC (x : ℝ) : ℂ := (tent x : ℂ)

private lemma continuous_tentC : Continuous tentC :=
  Complex.continuous_ofReal.comp continuous_tent

theorem fourier_tentC {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 tentC ξ = ((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  obtain ⟨a, ha_def⟩ : ∃ a : ℂ, a = -2 * (π : ℂ) * (ξ : ℂ) * Complex.I := ⟨_, rfl⟩
  have ha : a ≠ 0 := by
    rw [ha_def]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) Complex.I_ne_zero
    · exact_mod_cast hπ
    · exact_mod_cast hξ
  
  have hstep1 : 𝓕 tentC ξ = ∫ v : ℝ, tentC v * Complex.exp (a * v) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hexp : ((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I = a * (v : ℂ) := by
      rw [ha_def]; push_cast; ring
    dsimp only
    rw [smul_eq_mul, mul_comm, hexp]
  
  have hsupp : ∀ v : ℝ, v ∉ Set.Icc (-1 : ℝ) 1 → tentC v * Complex.exp (a * v) = 0 := by
    intro v hv
    simp [tentC, tent_eq_zero_of_notMem hv]
  have hcont : Continuous fun v : ℝ => tentC v * Complex.exp (a * v) := by
    exact continuous_tentC.mul (by fun_prop)
  have hstep2 : (∫ v : ℝ, tentC v * Complex.exp (a * v))
      = ∫ v in (-1 : ℝ)..1, tentC v * Complex.exp (a * v) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  
  have hsplit : (∫ v in (-1 : ℝ)..1, tentC v * Complex.exp (a * v))
      = (∫ v in (-1 : ℝ)..0, tentC v * Complex.exp (a * v)) +
        ∫ v in (0 : ℝ)..1, tentC v * Complex.exp (a * v) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hleft : (∫ v in (-1 : ℝ)..0, tentC v * Complex.exp (a * v))
      = ∫ v in (-1 : ℝ)..0, ((1 : ℂ) + (v : ℂ)) * Complex.exp (a * v) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hv
    simp [tentC, tent_of_mem_Icc_neg_one_zero hv]
  have hright : (∫ v in (0 : ℝ)..1, tentC v * Complex.exp (a * v))
      = ∫ v in (0 : ℝ)..1, -((((-1 : ℂ)) + (v : ℂ)) * Complex.exp (a * v)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    rw [tentC, tent_of_mem_Icc_zero_one hv]
    push_cast
    ring
  rw [hstep1, hstep2, hsplit, hleft, hright, intervalIntegral.integral_neg,
    integral_linear_mul_cexp ha, integral_linear_mul_cexp ha]
  
  have he0 : Complex.exp (a * ((0 : ℝ) : ℂ)) = 1 := by
    norm_num
  have he1 : Complex.exp (a * ((1 : ℝ) : ℂ)) = Complex.exp a := by
    norm_num
  have hem1 : Complex.exp (a * ((-1 : ℝ) : ℂ)) = Complex.exp (-a) := by
    norm_num
  have hcos : Complex.exp a + Complex.exp (-a) = 2 * Complex.cos (2 * (π : ℂ) * (ξ : ℂ)) := by
    have h1 : a = (-(2 * (π : ℂ) * (ξ : ℂ))) * Complex.I := by rw [ha_def]; ring
    rw [h1, show -(-(2 * (π : ℂ) * (ξ : ℂ)) * Complex.I)
        = (2 * (π : ℂ) * (ξ : ℂ)) * Complex.I by ring,
      Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have ha2 : a ^ 2 = -(4 * (π : ℂ) ^ 2 * (ξ : ℂ) ^ 2) := by
    rw [ha_def]
    rw [mul_pow, mul_pow, mul_pow, Complex.I_sq]
    ring
  have hsin : 2 - 2 * Complex.cos (2 * (π : ℂ) * (ξ : ℂ))
      = 4 * Complex.sin ((π : ℂ) * (ξ : ℂ)) ^ 2 := by
    have : (2 : ℂ) * (π : ℂ) * (ξ : ℂ) = 2 * ((π : ℂ) * (ξ : ℂ)) := by ring
    rw [this, Complex.cos_two_mul', Complex.cos_sq']
    ring
  have hπξ : ((π : ℂ) * (ξ : ℂ)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast hπ
    · exact_mod_cast hξ
  have hsum : Complex.exp a + Complex.exp (-a) - 2
      = -(4 * Complex.sin ((π : ℂ) * (ξ : ℂ)) ^ 2) := by
    rw [hcos]
    linear_combination -hsin
  have hfinal : (Complex.exp a + Complex.exp (-a) - 2) / a ^ 2
      = ((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) := by
    rw [hsum, ha2]
    push_cast
    field_simp
  rw [he0, he1, hem1, ← hfinal]
  field_simp
  push_cast
  ring

private lemma sq_sin_div_le (x : ℝ) : (Real.sin x / x) ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h1 : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  have h2 : Real.sin x ^ 2 ≤ x ^ 2 := Real.sin_sq_le_sq
  rw [div_pow, ← div_eq_mul_inv, div_le_div_iff₀ hx2 hpos]
  rcases le_or_gt (x ^ 2) 1 with h | h
  · nlinarith [sq_nonneg (Real.sin x)]
  · nlinarith [sq_nonneg (Real.sin x)]

theorem integrable_sin_div_sq : Integrable (fun x : ℝ => (Real.sin x / x) ^ 2) := by
  refine Integrable.mono' (g := fun x : ℝ => 2 * (1 + x ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul 2)
    ((Real.continuous_sin.measurable.div measurable_id).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_sin_div_le x

theorem integral_sin_div_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  
  have hscaled : Integrable (fun ξ : ℝ => (Real.sin (π * ξ) / (π * ξ)) ^ 2) :=
    MeasureTheory.Integrable.comp_mul_left' integrable_sin_div_sq hπ
  have hae : 𝓕 tentC =ᵐ[volume] fun ξ : ℝ => (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ) := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with ξ hξ
    exact fourier_tentC (by simpa using hξ)
  have hFint : Integrable (𝓕 tentC) := hscaled.ofReal.congr hae.symm
  
  have hcs : HasCompactSupport tentC :=
    HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => by
      simp [tentC, tent_eq_zero_of_notMem hx]
  have htent : Integrable tentC := continuous_tentC.integrable_of_hasCompactSupport hcs
  have hinv : 𝓕⁻ (𝓕 tentC) (0 : ℝ) = tentC 0 :=
    htent.fourierInv_fourier_eq hFint continuous_tentC.continuousAt
  have h0 : 𝓕⁻ (𝓕 tentC) (0 : ℝ) = ∫ ξ : ℝ, 𝓕 tentC ξ := by
    rw [Real.fourierInv_eq]
    simp
  
  have hone : (∫ ξ : ℝ, (Real.sin (π * ξ) / (π * ξ)) ^ 2) = 1 := by
    have h : (∫ ξ : ℝ, (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ)) = 1 := by
      rw [← integral_congr_ae hae, ← h0, hinv, tentC, tent_zero]
      norm_num
    exact_mod_cast h
  
  have hchange := MeasureTheory.Measure.integral_comp_mul_left
    (fun u : ℝ => (Real.sin u / u) ^ 2) π
  rw [hone, smul_eq_mul, abs_of_pos (inv_pos.2 Real.pi_pos)] at hchange
  have h2 := congrArg (fun z : ℝ => π * z) hchange.symm
  simp only [← mul_assoc, mul_inv_cancel₀ hπ, one_mul, mul_one] at h2
  exact h2

theorem integral_fejerKernel {T : ℝ} (hT : 0 < T) : ∫ x : ℝ, fejerKernel T x = 1 := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h : ∀ x : ℝ,
      fejerKernel T x = (T / (2 * π)) * (Real.sin (T / 2 * x) / (T / 2 * x)) ^ 2 := by
    intro x
    unfold fejerKernel
    rw [show T * x / 2 = T / 2 * x from by ring]
  have hg : (∫ x : ℝ, (Real.sin (T / 2 * x) / (T / 2 * x)) ^ 2)
      = |(T / 2)⁻¹| • ∫ y : ℝ, (Real.sin y / y) ^ 2 :=
    MeasureTheory.Measure.integral_comp_mul_left (fun u : ℝ => (Real.sin u / u) ^ 2) (T / 2)
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, hg, integral_sin_div_sq, smul_eq_mul,
    abs_of_pos (inv_pos.2 (by linarith : (0 : ℝ) < T / 2))]
  field_simp

lemma tent_neg (x : ℝ) : tent (-x) = tent x := by simp [tent]

noncomputable def sqSincC (ξ : ℝ) : ℂ := (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ)

private lemma fourier_tentC_ae : 𝓕 tentC =ᵐ[volume] sqSincC := by
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with ξ hξ
  exact fourier_tentC (by simpa using hξ)

lemma integrable_sqSincC : Integrable sqSincC :=
  (MeasureTheory.Integrable.comp_mul_left' integrable_sin_div_sq Real.pi_ne_zero).ofReal

theorem fourier_sqSincC : 𝓕 sqSincC = tentC := by
  have hcs : HasCompactSupport tentC :=
    HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => by
      simp [tentC, tent_eq_zero_of_notMem hx]
  have htent : Integrable tentC := continuous_tentC.integrable_of_hasCompactSupport hcs
  have hFint : Integrable (𝓕 tentC) := integrable_sqSincC.congr fourier_tentC_ae.symm
  have hinv : 𝓕⁻ (𝓕 tentC) = tentC :=
    continuous_tentC.fourierInv_fourier_eq htent hFint
  funext x
  have h1 : 𝓕 sqSincC x = 𝓕 (𝓕 tentC) x :=
    (Real.fourier_congr_ae fourier_tentC_ae x).symm
  have h2 : 𝓕 (𝓕 tentC) x = 𝓕⁻ (𝓕 tentC) (-x) := by
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  rw [h1, h2, hinv]
  simp [tentC, tent_neg]

noncomputable def gTent (w m : ℝ) (ξ : ℝ) : ℂ :=
  (w : ℂ) * (Complex.exp (((2 * π * m * ξ : ℝ) : ℂ) * Complex.I) * sqSincC (w * ξ))

private lemma integrable_gTent {w : ℝ} (hw : w ≠ 0) (m : ℝ) : Integrable (gTent w m) := by
  have hbase : Integrable (fun ξ : ℝ => sqSincC (w * ξ)) :=
    MeasureTheory.Integrable.comp_mul_left' integrable_sqSincC hw
  have hmod : Integrable
      (fun ξ : ℝ => Complex.exp (((2 * π * m * ξ : ℝ) : ℂ) * Complex.I) * sqSincC (w * ξ)) := by
    refine hbase.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun ξ => ?_)
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · rw [Complex.norm_exp_ofReal_mul_I]
  exact hmod.const_mul _

lemma fourier_gTent {w : ℝ} (hw : 0 < w) (m y : ℝ) :
    𝓕 (gTent w m) y = tentC ((y - m) / w) := by
  have hw' : (w : ℝ) ≠ 0 := ne_of_gt hw
  set z : ℝ := (y - m) / w with hz
  set G : ℝ → ℂ := fun η : ℝ => Complex.exp (((-2 * π * η * z : ℝ) : ℂ) * Complex.I) * sqSincC η
    with hG
  have hkey : ∀ ξ : ℝ,
      Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I) • gTent w m ξ = (w : ℂ) * G (w * ξ) := by
    intro ξ
    have hzw : w * z = y - m := by rw [hz]; field_simp
    have hreal : (-2 * π * (w * ξ) * z : ℝ) = (-2 * π * ξ * y : ℝ) + (2 * π * m * ξ : ℝ) := by
      rw [show (-2 * π * (w * ξ) * z : ℝ) = -2 * π * ξ * (w * z) from by ring, hzw]
      ring
    simp only [hG, smul_eq_mul, gTent]
    rw [hreal]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc (∫ ξ : ℝ, Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I) • gTent w m ξ)
      = ∫ ξ : ℝ, (w : ℂ) * G (w * ξ) := integral_congr_ae (Filter.Eventually.of_forall hkey)
    _ = (w : ℂ) * ∫ ξ : ℝ, G (w * ξ) := MeasureTheory.integral_const_mul _ _
    _ = (w : ℂ) * (|w⁻¹| • ∫ η : ℝ, G η) := by
          congr 1
          exact MeasureTheory.Measure.integral_comp_mul_left G w
    _ = ∫ η : ℝ, G η := by
          rw [abs_of_pos (inv_pos.2 hw), Complex.real_smul, ← mul_assoc]
          push_cast
          rw [mul_inv_cancel₀ (by exact_mod_cast hw' : (w : ℂ) ≠ 0), one_mul]
    _ = tentC z := by
          rw [← fourier_sqSincC]
          rw [Real.fourier_real_eq_integral_exp_smul]
          exact integral_congr_ae (Filter.Eventually.of_forall fun η => rfl)

private lemma min_one_max_zero_div {δ : ℝ} (hδ : 0 < δ) (X : ℝ) :
    min 1 (max 0 (X / δ)) = (1 / δ) * min δ (max 0 X) := by
  have hpos : (0 : ℝ) ≤ 1 / δ := by positivity
  rw [mul_min_of_nonneg _ _ hpos, mul_max_of_nonneg _ _ hpos]
  simp [div_eq_mul_inv, mul_comm, mul_inv_cancel₀ (ne_of_gt hδ)]

private lemma trapezoid_core (w δ s : ℝ) (hw : 0 ≤ w) (hδ : 0 < δ) :
    min δ (max 0 (w + δ - s)) - min δ (max 0 (-w - s))
      = max 0 (w + δ - |s|) - max 0 (w - |s|) := by
  rcases abs_cases s with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rw [hs] <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith

private lemma smul_tent_eq_max {w δ : ℝ} (hw : 0 ≤ w) (hδ : 0 < δ) (t : ℝ) :
    (w / δ) * tent (t / w) = (1 / δ) * max 0 (w - |t|) := by
  rcases hw.lt_or_eq with hw' | hw'
  · have hne : w ≠ 0 := ne_of_gt hw'
    have habs : |t / w| = |t| / w := by rw [abs_div, abs_of_pos hw']
    have hstep : tent (t / w) = max 0 ((w - |t|) / w) := by
      rw [tent, habs]
      congr 1
      field_simp
    rw [hstep, mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ w / δ),
      mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / δ)]
    congr 1
    · ring
    · field_simp
  · subst hw'
    simp [max_eq_left (by simpa using abs_nonneg t : (0 : ℝ) - |t| ≤ 0)]

private lemma integrable_gTent' {w : ℝ} (hw : 0 ≤ w) (m : ℝ) : Integrable (gTent w m) := by
  rcases hw.lt_or_eq with h | h
  · exact integrable_gTent (ne_of_gt h) m
  · have hz : gTent w m = fun _ : ℝ => (0 : ℂ) := by funext ξ; simp [gTent, ← h]
    rw [hz]
    exact integrable_zero _ _ _

private lemma smul_fourier_gTent {w : ℝ} (hw : 0 ≤ w) (δ m y : ℝ) :
    ((w / δ : ℝ) : ℂ) * 𝓕 (gTent w m) y = (((w / δ) * tent ((y - m) / w) : ℝ) : ℂ) := by
  rcases hw.lt_or_eq with h | h
  · rw [fourier_gTent h m y]
    simp [tentC]
  · have hz : gTent w m = fun _ : ℝ => (0 : ℂ) := by funext ξ; simp [gTent, ← h]
    rw [hz, ← h]
    simp [Real.fourier_real_eq_integral_exp_smul]

theorem integral_fourier_measure {P : Measure ℝ} [IsFiniteMeasure P] {g : ℝ → ℂ}
    (hg : Integrable g) :
    ∫ x : ℝ, 𝓕 g x ∂P = ∫ ξ : ℝ, charFun P (-(2 * π * ξ)) * g ξ := by
  have hL : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2 := continuous_inner
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [LinearMap.flip_apply, innerₗ_apply_apply]
    exact real_inner_comm x y
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := P) (ν := (volume : Measure ℝ)) (L := innerₗ ℝ)
    (f := fun _ : ℝ => (1 : ℂ)) (g := g)
    Real.continuous_fourierChar hL (integrable_const 1) hg
  rw [hflip] at key
  have hchar : ∀ ξ : ℝ,
      VectorFourier.fourierIntegral Real.fourierChar P (innerₗ ℝ) (fun _ : ℝ => (1 : ℂ)) ξ
        = charFun P (-(2 * π * ξ)) := by
    intro ξ
    rw [Real.vector_fourierIntegral_eq_integral_exp_smul, charFun_apply_real]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hin : ((innerₗ ℝ) v) ξ = v * ξ := by
      simp only [innerₗ_apply_apply]
      change ξ * v = v * ξ
      ring
    dsimp only
    rw [hin, smul_eq_mul, mul_one]
    congr 1
    push_cast
    ring
  have hfour : ∀ x : ℝ,
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g x = 𝓕 g x :=
    fun _ => rfl
  simp only [hchar, hfour, smul_eq_mul, one_mul] at key
  exact key.symm

noncomputable def ramp (u δ y : ℝ) : ℝ := min 1 (max 0 ((u + δ - y) / δ))

lemma ramp_nonneg (u δ y : ℝ) : 0 ≤ ramp u δ y :=
  le_min zero_le_one (le_max_left _ _)

lemma ramp_le_one (u δ y : ℝ) : ramp u δ y ≤ 1 := min_le_left _ _

lemma continuous_ramp (u δ : ℝ) : Continuous (ramp u δ) := by
  unfold ramp; fun_prop

lemma ramp_eq_one_of_le {u δ y : ℝ} (hδ : 0 < δ) (hy : y ≤ u) : ramp u δ y = 1 := by
  have h : (1 : ℝ) ≤ (u + δ - y) / δ := (one_le_div hδ).2 (by linarith)
  exact min_eq_left (le_max_of_le_right h)

lemma ramp_eq_zero_of_le {u δ y : ℝ} (hδ : 0 < δ) (hy : u + δ ≤ y) : ramp u δ y = 0 := by
  have h : (u + δ - y) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  simp [ramp, max_eq_left h]

lemma integrable_ramp (P : Measure ℝ) [IsFiniteMeasure P] (u δ : ℝ) :
    Integrable (ramp u δ) P :=
  (integrable_const (1 : ℝ)).mono' (continuous_ramp u δ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ramp_nonneg u δ y)]; exact ramp_le_one u δ y)

lemma measure_Iic_le_integral_ramp (P : Measure ℝ) [IsFiniteMeasure P] {δ : ℝ} (hδ : 0 < δ)
    (u : ℝ) : (P (Set.Iic u)).toReal ≤ ∫ y, ramp u δ y ∂P := by
  have hbase : (∫ y, (Set.Iic u).indicator (fun _ => (1 : ℝ)) y ∂P) = (P (Set.Iic u)).toReal := by
    rw [MeasureTheory.integral_indicator_const _ measurableSet_Iic]
    simp [measureReal_def]
  rw [← hbase]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
    (integrable_ramp P u δ) fun y => ?_
  · by_cases hy : y ∈ Set.Iic u
    · rw [Set.indicator_of_mem hy, ramp_eq_one_of_le hδ hy]
    · rw [Set.indicator_of_notMem hy]; exact ramp_nonneg u δ y

lemma integral_ramp_le_measure_Iic (P : Measure ℝ) [IsFiniteMeasure P] {δ : ℝ} (hδ : 0 < δ)
    (u : ℝ) : (∫ y, ramp u δ y ∂P) ≤ (P (Set.Iic (u + δ))).toReal := by
  have hbase : (∫ y, (Set.Iic (u + δ)).indicator (fun _ => (1 : ℝ)) y ∂P)
      = (P (Set.Iic (u + δ))).toReal := by
    rw [MeasureTheory.integral_indicator_const _ measurableSet_Iic]
    simp [measureReal_def]
  rw [← hbase]
  refine integral_mono (integrable_ramp P u δ)
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) fun y => ?_
  · by_cases hy : y ∈ Set.Iic (u + δ)
    · rw [Set.indicator_of_mem hy]; exact ramp_le_one u δ y
    · rw [Set.indicator_of_notMem hy,
        ramp_eq_zero_of_le hδ (le_of_not_ge (by simpa using hy))]

lemma tendsto_measure_Iic_atBot (P : Measure ℝ) [IsProbabilityMeasure P] :
    Filter.Tendsto (fun x : ℝ => (P (Set.Iic x)).toReal) Filter.atBot (𝓝 0) := by
  refine (ProbabilityTheory.tendsto_cdf_atBot P).congr fun x => ?_
  rw [ProbabilityTheory.cdf_eq_real]
  rfl

lemma tendsto_integral_ramp_atBot (P : Measure ℝ) [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun v : ℝ => ∫ y, ramp v δ y ∂P) Filter.atBot (𝓝 0) := by
  refine squeeze_zero (fun v => integral_nonneg fun y => ramp_nonneg v δ y)
    (fun v => integral_ramp_le_measure_Iic P hδ v) ?_
  exact (tendsto_measure_Iic_atBot P).comp
    (Filter.tendsto_atBot_add_const_right _ δ Filter.tendsto_id)

noncomputable def trapezoid (v u δ y : ℝ) : ℝ := ramp u δ y - ramp v δ y

private lemma trapezoid_eq_tent_combination {v u δ : ℝ} (hδ : 0 < δ) (hvu : v + δ ≤ u) (y : ℝ) :
    trapezoid v u δ y
      = ((u - v + δ) / 2 / δ) * tent ((y - (v + u + δ) / 2) / ((u - v + δ) / 2))
        - ((u - v - δ) / 2 / δ) * tent ((y - (v + u + δ) / 2) / ((u - v - δ) / 2)) := by
  have hw2 : (0 : ℝ) ≤ (u - v - δ) / 2 := by linarith
  have hw1 : (u - v + δ) / 2 = (u - v - δ) / 2 + δ := by ring
  have hs1 : u + δ - y = (u - v - δ) / 2 + δ - (y - (v + u + δ) / 2) := by ring
  have hs2 : v + δ - y = -((u - v - δ) / 2) - (y - (v + u + δ) / 2) := by ring
  rw [trapezoid, ramp, ramp, hs1, hs2, min_one_max_zero_div hδ, min_one_max_zero_div hδ,
    ← mul_sub, trapezoid_core _ _ _ hw2 hδ, hw1,
    smul_tent_eq_max hw2 hδ, smul_tent_eq_max (by linarith : (0:ℝ) ≤ (u - v - δ) / 2 + δ) hδ]
  ring

theorem exists_fourier_trapezoid {v u δ : ℝ} (hδ : 0 < δ) (hvu : v + δ ≤ u) :
    ∃ g : ℝ → ℂ, Integrable g ∧
      (∀ y : ℝ, 𝓕 g y = ((trapezoid v u δ y : ℝ) : ℂ)) ∧
      (∀ ξ : ℝ, ‖g ξ‖ ≤ min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2))) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  set w₁ : ℝ := (u - v + δ) / 2 with hw₁
  set w₂ : ℝ := (u - v - δ) / 2 with hw₂
  set m : ℝ := (v + u + δ) / 2 with hm
  have hw₂0 : 0 ≤ w₂ := by rw [hw₂]; linarith
  have hw₁0 : 0 < w₁ := by rw [hw₁]; linarith
  have hdiff : w₁ - w₂ = δ := by rw [hw₁, hw₂]; ring
  refine ⟨fun ξ => ((w₁ / δ : ℝ) : ℂ) * gTent w₁ m ξ - ((w₂ / δ : ℝ) : ℂ) * gTent w₂ m ξ,
    ((integrable_gTent (ne_of_gt hw₁0) m).const_mul _).sub
      ((integrable_gTent' hw₂0 m).const_mul _), fun y => ?_, fun ξ => ?_⟩
  · 
    have hI : ∀ w : ℝ, 0 ≤ w → Integrable (fun ξ : ℝ =>
        Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I) * gTent w m ξ) := by
      intro w hw
      refine (integrable_gTent' hw m).bdd_mul (c := 1) ?_
        (Filter.Eventually.of_forall fun ξ => ?_)
      · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
      · rw [Complex.norm_exp_ofReal_mul_I]
    have hsplit : 𝓕 (fun ξ : ℝ => ((w₁ / δ : ℝ) : ℂ) * gTent w₁ m ξ
          - ((w₂ / δ : ℝ) : ℂ) * gTent w₂ m ξ) y
        = ((w₁ / δ : ℝ) : ℂ) * 𝓕 (gTent w₁ m) y - ((w₂ / δ : ℝ) : ℂ) * 𝓕 (gTent w₂ m) y := by
      have expand : ∀ ξ : ℝ, Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I)
            * (((w₁ / δ : ℝ) : ℂ) * gTent w₁ m ξ - ((w₂ / δ : ℝ) : ℂ) * gTent w₂ m ξ)
          = ((w₁ / δ : ℝ) : ℂ)
              * (Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I) * gTent w₁ m ξ)
            - ((w₂ / δ : ℝ) : ℂ)
              * (Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I) * gTent w₂ m ξ) :=
        fun ξ => by ring
      simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
      have hc : ∀ (c : ℂ) (f : ℝ → ℂ), (∫ a : ℝ, c * f a) = c * ∫ a : ℝ, f a := by
        intro c f
        simpa using MeasureTheory.integral_smul c f
      rw [integral_congr_ae (Filter.Eventually.of_forall expand),
        MeasureTheory.integral_sub ((hI w₁ hw₁0.le).const_mul _) ((hI w₂ hw₂0).const_mul _),
        hc, hc]
    rw [hsplit, smul_fourier_gTent hw₁0.le δ m y, smul_fourier_gTent hw₂0 δ m y,
      trapezoid_eq_tent_combination hδ hvu y, ← hw₁, ← hw₂, ← hm]
    push_cast
    ring
  · 
    dsimp only
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp [gTent, sqSincC]
    have hξa : (0 : ℝ) < |ξ| := abs_pos.2 hξ
    have hval : ∀ w : ℝ,
        (w / δ) * (w * ((Real.sin (π * (w * ξ)) / (π * (w * ξ))) ^ 2))
          = Real.sin (π * (w * ξ)) ^ 2 / (δ * π ^ 2 * ξ ^ 2) := by
      intro w
      rcases eq_or_ne w 0 with rfl | hw
      · simp
      · field_simp
        try ring
    set A : ℝ := Real.sin (π * (w₁ * ξ)) ^ 2 / (δ * π ^ 2 * ξ ^ 2) with hAdef
    set B : ℝ := Real.sin (π * (w₂ * ξ)) ^ 2 / (δ * π ^ 2 * ξ ^ 2) with hBdef
    have hg : ((w₁ / δ : ℝ) : ℂ) * gTent w₁ m ξ - ((w₂ / δ : ℝ) : ℂ) * gTent w₂ m ξ
        = Complex.exp (((2 * π * m * ξ : ℝ) : ℂ) * Complex.I) * ((A - B : ℝ) : ℂ) := by
      have e : ∀ w : ℝ, ((w / δ : ℝ) : ℂ) * gTent w m ξ
          = Complex.exp (((2 * π * m * ξ : ℝ) : ℂ) * Complex.I)
              * (((Real.sin (π * (w * ξ)) ^ 2 / (δ * π ^ 2 * ξ ^ 2) : ℝ)) : ℂ) := by
        intro w
        simp only [gTent, sqSincC]
        rw [← hval w]
        push_cast
        ring
      rw [e w₁, e w₂, hAdef, hBdef]
      push_cast
      ring
    rw [hg, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    
    have hAB : A - B
        = (Real.sin (π * (w₁ * ξ)) ^ 2 - Real.sin (π * (w₂ * ξ)) ^ 2) / (δ * π ^ 2 * ξ ^ 2) := by
      rw [hAdef, hBdef]; ring
    have hsin : Real.sin (π * (w₁ * ξ)) ^ 2 - Real.sin (π * (w₂ * ξ)) ^ 2
        = Real.sin (π * (w₁ * ξ) + π * (w₂ * ξ)) * Real.sin (π * δ * ξ) := by
      have harg : π * (w₁ * ξ) - π * (w₂ * ξ) = π * δ * ξ := by
        rw [← hdiff]; ring
      rw [← harg, Real.sin_add, Real.sin_sub]
      nlinarith [Real.sin_sq_add_cos_sq (π * (w₁ * ξ)), Real.sin_sq_add_cos_sq (π * (w₂ * ξ))]
    have h1 : |Real.sin (π * (w₁ * ξ) + π * (w₂ * ξ))| ≤ 1 := Real.abs_sin_le_one _
    have h2 : |Real.sin (π * δ * ξ)| ≤ π * δ * |ξ| := by
      refine Real.abs_sin_le_abs.trans_eq ?_
      rw [abs_mul, abs_mul, abs_of_pos hπ, abs_of_pos hδ]
    have hprod : |Real.sin (π * (w₁ * ξ) + π * (w₂ * ξ))| * |Real.sin (π * δ * ξ)|
        ≤ π * δ * |ξ| :=
      (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    refine le_min ?_ ?_
    · rw [hAB, hsin, abs_div, abs_of_pos (by positivity : (0 : ℝ) < δ * π ^ 2 * ξ ^ 2), abs_mul,
        show ξ ^ 2 = |ξ| ^ 2 from (sq_abs ξ).symm,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hprod, hξa, hδ, hπ, abs_nonneg (Real.sin (π * δ * ξ))]
    · have hb : |Real.sin (π * (w₁ * ξ)) ^ 2 - Real.sin (π * (w₂ * ξ)) ^ 2| ≤ 1 := by
        rw [abs_le]
        constructor <;>
          nlinarith [Real.sin_sq_le_one (π * (w₁ * ξ)), Real.sin_sq_le_one (π * (w₂ * ξ)),
            sq_nonneg (Real.sin (π * (w₁ * ξ))), sq_nonneg (Real.sin (π * (w₂ * ξ)))]
      rw [hAB, abs_div, abs_of_pos (by positivity : (0 : ℝ) < δ * π ^ 2 * ξ ^ 2),
        div_le_div_iff₀ (by positivity) (by positivity)]
      simpa using mul_le_mul_of_nonneg_right hb
        (by positivity : (0 : ℝ) ≤ δ * π ^ 2 * ξ ^ 2)

end StatLean.HypothesisTesting
end
