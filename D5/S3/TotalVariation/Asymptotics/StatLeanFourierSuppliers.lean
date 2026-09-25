/- GID: D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fejer Fourier inversion and Gaussian Hermite density identities. -/

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

section
open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal Real
namespace StatLean.HypothesisTesting

private noncomputable def cexpGauss (θ u : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * (u : ℂ) * I - (u : ℂ) ^ 2 / 2)

private lemma continuous_cexpGauss (θ : ℝ) : Continuous (cexpGauss θ) := by
  unfold cexpGauss; fun_prop

private lemma norm_cexpGauss (θ u : ℝ) : ‖cexpGauss θ u‖ = Real.exp (-(u ^ 2 / 2)) := by
  have h : ((θ : ℂ) * (u : ℂ) * I - (u : ℂ) ^ 2 / 2)
      = ((-(u ^ 2 / 2) : ℝ) : ℂ) + ((θ * u : ℝ) : ℂ) * I := by push_cast; ring
  rw [cexpGauss, h, Complex.norm_exp, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
    Complex.ofReal_im, neg_zero, add_zero]

private lemma hasDerivAt_cexpGauss (θ u : ℝ) :
    HasDerivAt (cexpGauss θ) (cexpGauss θ u * ((θ : ℂ) * I - (u : ℂ))) u := by
  have hbu : HasDerivAt (fun w : ℝ => (w : ℂ)) 1 u := by
    exact Complex.ofRealCLM.hasDerivAt
  have hg : HasDerivAt (fun w : ℝ => (θ : ℂ) * (w : ℂ) * I - (w : ℂ) ^ 2 / 2)
      ((θ : ℂ) * I - (u : ℂ)) u := by
    have h1 : HasDerivAt (fun w : ℝ => (θ : ℂ) * (w : ℂ) * I) ((θ : ℂ) * I) u := by
      simpa using (hbu.const_mul ((θ : ℂ))).mul_const I
    have h2 : HasDerivAt (fun w : ℝ => (w : ℂ) ^ 2 / 2) ((u : ℂ)) u := by
      have := (hbu.pow 2).div_const 2
      convert! this using 1
      ring
    exact h1.sub h2
  unfold cexpGauss
  exact hg.cexp

lemma abs_pow_le_exp (k : ℕ) (u : ℝ) :
    |u| ^ k ≤ 4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4) := by
  have hfac : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
  have h4 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 4 ^ k * (Nat.factorial k : ℝ) := by positivity
  have hC : (1 : ℝ) ≤ 4 ^ k * (Nat.factorial k : ℝ) := by nlinarith
  have hexp : (1 : ℝ) ≤ Real.exp (u ^ 2 / 4) := by
    linarith [Real.add_one_le_exp (u ^ 2 / 4), sq_nonneg u]
  rcases le_or_gt |u| 1 with h | h
  · calc |u| ^ k ≤ 1 ^ k := pow_le_pow_left₀ (abs_nonneg u) h k
      _ = 1 := one_pow k
      _ ≤ 4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4) := by nlinarith
  · have hkey : (u ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (u ^ 2 / 4) :=
      Real.pow_div_factorial_le_exp (u ^ 2 / 4) (by positivity) k
    have hu2 : (u ^ 2 / 4) ^ k = |u| ^ (2 * k) / 4 ^ k := by
      rw [div_pow, ← sq_abs u, ← pow_mul]
    have hle : |u| ^ k ≤ |u| ^ (2 * k) := pow_le_pow_right₀ h.le (by omega)
    rw [hu2, div_div, div_le_iff₀ hpos] at hkey
    calc |u| ^ k ≤ |u| ^ (2 * k) := hle
      _ ≤ Real.exp (u ^ 2 / 4) * (4 ^ k * (Nat.factorial k : ℝ)) := hkey
      _ = 4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4) := by ring

lemma integrable_abs_pow_mul_gauss (k : ℕ) :
    Integrable (fun u : ℝ => |u| ^ k * Real.exp (-(u ^ 2 / 2))) := by
  have hbase : Integrable (fun u : ℝ => Real.exp (-(1 / 4 : ℝ) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  refine Integrable.mono' (g := fun u : ℝ =>
      4 ^ k * (Nat.factorial k : ℝ) * Real.exp (-(1 / 4 : ℝ) * u ^ 2))
    (hbase.const_mul _) (by fun_prop) (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmul := mul_le_mul_of_nonneg_right (abs_pow_le_exp k u)
    (Real.exp_pos (-(u ^ 2 / 2))).le
  refine hmul.trans_eq ?_
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

private lemma integrable_pow_mul_cexpGauss (θ : ℝ) (k : ℕ) :
    Integrable (fun u : ℝ => (u : ℂ) ^ k * cexpGauss θ u) := by
  have hcont : Continuous fun u : ℝ => (u : ℂ) ^ k * cexpGauss θ u :=
    (Complex.continuous_ofReal.pow k).mul (continuous_cexpGauss θ)
  refine Integrable.mono' (integrable_abs_pow_mul_gauss k) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_cexpGauss]

private lemma integrable_cubic_cexpGauss (θ : ℝ) (α β γ δ : ℂ) :
    Integrable (fun u : ℝ =>
      (α * (u : ℂ) ^ 3 + β * (u : ℂ) ^ 2 + γ * (u : ℂ) + δ) * cexpGauss θ u) := by
  have i0 : Integrable (fun u : ℝ => δ * ((u : ℂ) ^ 0 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 0).const_mul δ
  have i1 : Integrable (fun u : ℝ => γ * ((u : ℂ) ^ 1 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 1).const_mul γ
  have i2 : Integrable (fun u : ℝ => β * ((u : ℂ) ^ 2 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 2).const_mul β
  have i3 : Integrable (fun u : ℝ => α * ((u : ℂ) ^ 3 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 3).const_mul α
  exact (i3.fun_add (i2.fun_add (i1.fun_add i0))).congr
    (Filter.Eventually.of_forall fun u => by ring)

private lemma integral_cubic_cexpGauss (θ : ℝ) (α β γ δ : ℂ) :
    (∫ u : ℝ, (α * (u : ℂ) ^ 3 + β * (u : ℂ) ^ 2 + γ * (u : ℂ) + δ) * cexpGauss θ u)
      = α * (∫ u : ℝ, (u : ℂ) ^ 3 * cexpGauss θ u) + β * (∫ u : ℝ, (u : ℂ) ^ 2 * cexpGauss θ u)
        + γ * (∫ u : ℝ, (u : ℂ) ^ 1 * cexpGauss θ u)
        + δ * (∫ u : ℝ, (u : ℂ) ^ 0 * cexpGauss θ u) := by
  have i0 : Integrable (fun u : ℝ => δ * ((u : ℂ) ^ 0 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 0).const_mul δ
  have i1 : Integrable (fun u : ℝ => γ * ((u : ℂ) ^ 1 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 1).const_mul γ
  have i2 : Integrable (fun u : ℝ => β * ((u : ℂ) ^ 2 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 2).const_mul β
  have i3 : Integrable (fun u : ℝ => α * ((u : ℂ) ^ 3 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 3).const_mul α
  have key : ∀ u : ℝ, (α * (u : ℂ) ^ 3 + β * (u : ℂ) ^ 2 + γ * (u : ℂ) + δ) * cexpGauss θ u
      = α * ((u : ℂ) ^ 3 * cexpGauss θ u) + (β * ((u : ℂ) ^ 2 * cexpGauss θ u)
        + (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u))) :=
    fun u => by ring
  have s3 : (∫ u : ℝ, (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u)))
      = (∫ u : ℝ, γ * ((u : ℂ) ^ 1 * cexpGauss θ u)) + ∫ u : ℝ, δ * ((u : ℂ) ^ 0 * cexpGauss θ u) :=
    integral_add i1 i0
  have s2 : (∫ u : ℝ, (β * ((u : ℂ) ^ 2 * cexpGauss θ u)
        + (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u))))
      = (∫ u : ℝ, β * ((u : ℂ) ^ 2 * cexpGauss θ u))
        + ∫ u : ℝ, (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u)) :=
    integral_add i2 (i1.fun_add i0)
  have s1 : (∫ u : ℝ, (α * ((u : ℂ) ^ 3 * cexpGauss θ u) + (β * ((u : ℂ) ^ 2 * cexpGauss θ u)
        + (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u)))))
      = (∫ u : ℝ, α * ((u : ℂ) ^ 3 * cexpGauss θ u))
        + ∫ u : ℝ, (β * ((u : ℂ) ^ 2 * cexpGauss θ u)
          + (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u))) :=
    integral_add i3 (i2.fun_add (i1.fun_add i0))
  have m3 : (∫ u : ℝ, α * ((u : ℂ) ^ 3 * cexpGauss θ u))
      = α * ∫ u : ℝ, (u : ℂ) ^ 3 * cexpGauss θ u :=
    MeasureTheory.integral_const_mul α _
  have m2 : (∫ u : ℝ, β * ((u : ℂ) ^ 2 * cexpGauss θ u))
      = β * ∫ u : ℝ, (u : ℂ) ^ 2 * cexpGauss θ u :=
    MeasureTheory.integral_const_mul β _
  have m1 : (∫ u : ℝ, γ * ((u : ℂ) ^ 1 * cexpGauss θ u))
      = γ * ∫ u : ℝ, (u : ℂ) ^ 1 * cexpGauss θ u :=
    MeasureTheory.integral_const_mul γ _
  have m0 : (∫ u : ℝ, δ * ((u : ℂ) ^ 0 * cexpGauss θ u))
      = δ * ∫ u : ℝ, (u : ℂ) ^ 0 * cexpGauss θ u :=
    MeasureTheory.integral_const_mul δ _
  rw [integral_congr_ae (Filter.Eventually.of_forall key), s1, s2, s3, m3, m2, m1, m0]
  ring

private lemma integral_poly_cexpGauss_deriv_eq_zero (θ : ℝ) (a b c : ℂ) :
    (∫ u : ℝ, ((2 * a * (u : ℂ) + b)
        + (a * (u : ℂ) ^ 2 + b * (u : ℂ) + c) * ((θ : ℂ) * I - (u : ℂ))) * cexpGauss θ u) = 0 := by
  have hderiv : ∀ u : ℝ,
      HasDerivAt (fun w : ℝ => (a * (w : ℂ) ^ 2 + b * (w : ℂ) + c) * cexpGauss θ w)
      (((2 * a * (u : ℂ) + b)
        + (a * (u : ℂ) ^ 2 + b * (u : ℂ) + c) * ((θ : ℂ) * I - (u : ℂ))) * cexpGauss θ u) u := by
    intro u
    have hbu : HasDerivAt (fun w : ℝ => (w : ℂ)) 1 u := by
      exact Complex.ofRealCLM.hasDerivAt
    have hp : HasDerivAt (fun w : ℝ => a * (w : ℂ) ^ 2 + b * (w : ℂ) + c)
        (2 * a * (u : ℂ) + b) u := by
      have h1 : HasDerivAt (fun w : ℝ => a * (w : ℂ) ^ 2) (a * (2 * (u : ℂ))) u := by
        have := (hbu.pow 2).const_mul a
        convert! this using 1
        ring
      have h2 : HasDerivAt (fun w : ℝ => b * (w : ℂ)) b u := by
        simpa using hbu.const_mul b
      have := (h1.add h2).add_const c
      convert! this using 1
      ring
    have := hp.mul (hasDerivAt_cexpGauss θ u)
    convert! this using 1
    ring
  have hInt : Integrable (fun w : ℝ => (a * (w : ℂ) ^ 2 + b * (w : ℂ) + c) * cexpGauss θ w) :=
    (integrable_cubic_cexpGauss θ 0 a b c).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have hInt' : Integrable (fun u : ℝ => ((2 * a * (u : ℂ) + b)
      + (a * (u : ℂ) ^ 2 + b * (u : ℂ) + c) * ((θ : ℂ) * I - (u : ℂ))) * cexpGauss θ u) :=
    (integrable_cubic_cexpGauss θ (-a) (a * ((θ : ℂ) * I) - b)
      (2 * a + b * ((θ : ℂ) * I) - c) (b + c * ((θ : ℂ) * I))).congr
      (Filter.Eventually.of_forall fun u => by ring)
  exact integral_eq_zero_of_hasDerivAt_of_integrable hderiv hInt' hInt

private lemma poly_cexpGauss_relation (θ : ℝ) (a b c : ℂ) :
    (-a) * (∫ u : ℝ, (u : ℂ) ^ 3 * cexpGauss θ u)
        + (a * ((θ : ℂ) * I) - b) * (∫ u : ℝ, (u : ℂ) ^ 2 * cexpGauss θ u)
      + (2 * a + b * ((θ : ℂ) * I) - c) * (∫ u : ℝ, (u : ℂ) ^ 1 * cexpGauss θ u)
      + (b + c * ((θ : ℂ) * I)) * (∫ u : ℝ, (u : ℂ) ^ 0 * cexpGauss θ u) = 0 := by
  rw [← integral_cubic_cexpGauss θ (-a) (a * ((θ : ℂ) * I) - b) (2 * a + b * ((θ : ℂ) * I) - c)
      (b + c * ((θ : ℂ) * I)), ← integral_poly_cexpGauss_deriv_eq_zero θ a b c]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)

private lemma cexpGauss_eq (θ u : ℝ) :
    cexpGauss θ u = Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2) := by
  rw [cexpGauss, ← Complex.exp_add]
  congr 1
  ring

private lemma integral_cexpGauss (θ : ℝ) :
    (∫ u : ℝ, (u : ℂ) ^ 0 * cexpGauss θ u)
      = ((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2) := by
  have hq := integral_cexp_quadratic (b := -(1 / 2 : ℂ)) (by norm_num) ((θ : ℂ) * I) 0
  have hlhs : (∫ x : ℝ, Complex.exp (-(1 / 2 : ℂ) * (x : ℂ) ^ 2 + (θ : ℂ) * I * (x : ℂ) + 0))
      = ∫ u : ℝ, (u : ℂ) ^ 0 * cexpGauss θ u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [pow_zero, one_mul, cexpGauss]
    congr 1
    ring
  have hcpow : ((π : ℂ) / -(-(1 / 2 : ℂ))) ^ (1 / 2 : ℂ) = ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
    have h2 : ((π : ℂ) / -(-(1 / 2 : ℂ))) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * π)]
    norm_num
  have hexp : Complex.exp ((0 : ℂ) - ((θ : ℂ) * I) ^ 2 / (4 * -(1 / 2 : ℂ)))
      = Complex.exp (-(θ : ℂ) ^ 2 / 2) := by
    congr 1
    rw [mul_pow, Complex.I_sq]
    ring
  rw [← hlhs, hq, hcpow, hexp]

private lemma integral_pow1_cexpGauss (θ : ℝ) :
    (∫ u : ℝ, (u : ℂ) ^ 1 * cexpGauss θ u)
      = ((θ : ℂ) * I) * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2)) := by
  have h := poly_cexpGauss_relation θ 0 0 1
  rw [integral_cexpGauss θ] at h
  linear_combination -h

private lemma integral_pow2_cexpGauss (θ : ℝ) :
    (∫ u : ℝ, (u : ℂ) ^ 2 * cexpGauss θ u)
      = (1 - (θ : ℂ) ^ 2)
          * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2)) := by
  have h := poly_cexpGauss_relation θ 0 1 0
  rw [integral_cexpGauss θ, integral_pow1_cexpGauss θ] at h
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination -h + ((θ : ℂ) ^ 2 * (((Real.sqrt (2 * π) : ℝ) : ℂ)
    * Complex.exp (-(θ : ℂ) ^ 2 / 2))) * hI

private lemma integral_pow3_cexpGauss (θ : ℝ) :
    (∫ u : ℝ, (u : ℂ) ^ 3 * cexpGauss θ u)
      = ((θ : ℂ) * I) * ((1 - (θ : ℂ) ^ 2)
          * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2)))
        + 2 * (((θ : ℂ) * I)
          * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2))) := by
  have h := poly_cexpGauss_relation θ 1 0 0
  rw [integral_pow1_cexpGauss θ, integral_pow2_cexpGauss θ] at h
  linear_combination -h

theorem integral_cexp_mul_gaussian (θ : ℝ) :
    (∫ u : ℝ, Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2))
      = ((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2) := by
  rw [← integral_cexpGauss θ]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun u => by simp only [cexpGauss_eq, pow_zero, one_mul])

theorem integrable_cubic_mul_cexp_mul_gaussian (θ : ℝ) (a b c d : ℂ) :
    Integrable (fun u : ℝ => (a * (u : ℂ) ^ 3 + b * (u : ℂ) ^ 2 + c * (u : ℂ) + d)
      * (Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2))) := by
  refine (integrable_cubic_cexpGauss θ a b c d).congr
    (Filter.Eventually.of_forall fun u => ?_)
  simp only [cexpGauss_eq]

theorem integral_hermite3_mul_cexp_mul_gaussian (θ : ℝ) :
    (∫ u : ℝ, ((u : ℂ) ^ 3 - 3 * (u : ℂ))
        * (Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2)))
      = ((θ : ℂ) * I) ^ 3
          * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2)) := by
  have hsplit : (∫ u : ℝ, ((u : ℂ) ^ 3 - 3 * (u : ℂ)) * cexpGauss θ u)
      = (∫ u : ℝ, (u : ℂ) ^ 3 * cexpGauss θ u) - 3 * ∫ u : ℝ, (u : ℂ) ^ 1 * cexpGauss θ u := by
    have := integral_cubic_cexpGauss θ 1 0 (-3) 0
    rw [show (∫ u : ℝ,
          ((1 : ℂ) * (u : ℂ) ^ 3 + 0 * (u : ℂ) ^ 2 + (-3) * (u : ℂ) + 0) * cexpGauss θ u)
        = ∫ u : ℝ, ((u : ℂ) ^ 3 - 3 * (u : ℂ)) * cexpGauss θ u from
      integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)] at this
    rw [this]
    ring
  have hgoal : (∫ u : ℝ, ((u : ℂ) ^ 3 - 3 * (u : ℂ))
      * (Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2)))
      = ∫ u : ℝ, ((u : ℂ) ^ 3 - 3 * (u : ℂ)) * cexpGauss θ u :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only [cexpGauss_eq])
  rw [hgoal, hsplit, integral_pow3_cexpGauss θ, integral_pow1_cexpGauss θ]
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination (-(θ : ℂ) ^ 3 * I * (((Real.sqrt (2 * π) : ℝ) : ℂ)
    * Complex.exp (-(θ : ℂ) ^ 2 / 2))) * hI

end StatLean.HypothesisTesting
end

section
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology RealInnerProductSpace FourierTransform
namespace StatLean.HypothesisTesting

noncomputable def normalCDF (m : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (gaussianReal m v (Set.Iic x)).toReal

noncomputable def stdNormalCDF (x : ℝ) : ℝ := normalCDF 0 1 x

noncomputable def stdNormalPDF (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)

noncomputable def edgeworthDensity (γ : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  stdNormalPDF u * (1 + γ / 6 * (u ^ 3 - 3 * u) * (Real.sqrt n)⁻¹)

noncomputable def edgeworthCDF (γ : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  stdNormalCDF u - 1 / 6 * γ * stdNormalPDF u * (u ^ 2 - 1) * (Real.sqrt n)⁻¹

noncomputable def hermiteAntideriv (u : ℝ) : ℝ := -(stdNormalPDF u * (u ^ 2 - 1))

lemma stdNormalPDF_eq_gaussianPDFReal (u : ℝ) : stdNormalPDF u = gaussianPDFReal 0 1 u := by
  have hg : gaussianPDFReal 0 1 u
      = (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
        * Real.exp (-(u - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) := rfl
  rw [hg, stdNormalPDF, div_eq_inv_mul]
  norm_num

lemma stdNormalCDF_eq_setIntegral (u : ℝ) :
    stdNormalCDF u = ∫ y in Set.Iic u, stdNormalPDF y := by
  have hnn : 0 ≤ ∫ y in Set.Iic u, gaussianPDFReal 0 1 y :=
    integral_nonneg fun y => gaussianPDFReal_nonneg 0 1 y
  simp_rw [stdNormalPDF_eq_gaussianPDFReal]
  rw [stdNormalCDF, normalCDF, gaussianReal_apply_eq_integral 0 one_ne_zero (Set.Iic u),
    ENNReal.toReal_ofReal hnn]

lemma hasDerivAt_stdNormalPDF (u : ℝ) :
    HasDerivAt stdNormalPDF (-u * stdNormalPDF u) u := by
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-u) u := by
    have := ((hasDerivAt_pow 2 u).neg).div_const 2
    convert! this using 1
    push_cast
    ring
  have h2 := (h1.exp).div_const (Real.sqrt (2 * Real.pi))
  change HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)) _ u
  convert! h2 using 1
  rw [stdNormalPDF]
  ring

lemma hasDerivAt_hermiteAntideriv (u : ℝ) :
    HasDerivAt hermiteAntideriv (stdNormalPDF u * (u ^ 3 - 3 * u)) u := by
  have h := ((hasDerivAt_stdNormalPDF u).mul ((hasDerivAt_pow 2 u).sub_const 1)).neg
  change HasDerivAt (fun x : ℝ => -(stdNormalPDF x * (x ^ 2 - 1))) _ u
  convert! h using 1
  push_cast
  ring

lemma tendsto_hermiteAntideriv_atBot :
    Filter.Tendsto hermiteAntideriv Filter.atBot (𝓝 0) := by
  have hw : Filter.Tendsto (fun u : ℝ => u ^ 2 / 2) Filter.atBot Filter.atTop := by
    have h1 : Filter.Tendsto (fun u : ℝ => |u| ^ 2) Filter.atBot Filter.atTop :=
      (tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_abs_atBot_atTop
    have h2 : Filter.Tendsto (fun u : ℝ => u ^ 2) Filter.atBot Filter.atTop := by
      simpa [sq_abs] using h1
    exact h2.atTop_div_const (by norm_num)
  have h1 : Filter.Tendsto (fun w : ℝ => w ^ 1 * Real.exp (-w)) Filter.atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 : Filter.Tendsto (fun w : ℝ => Real.exp (-w)) Filter.atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have h3 : Filter.Tendsto (fun w : ℝ => (2 * w - 1) * Real.exp (-w)) Filter.atTop (𝓝 0) := by
    have h4 := (h1.const_mul (2 : ℝ)).sub h2
    rw [mul_zero, sub_zero] at h4
    exact h4.congr fun w => by ring
  have hg : Filter.Tendsto
      (fun w : ℝ => -((2 * w - 1) * Real.exp (-w) / Real.sqrt (2 * Real.pi)))
      Filter.atTop (𝓝 0) := by
    have := (h3.div_const (Real.sqrt (2 * Real.pi))).neg
    rw [zero_div, neg_zero] at this
    exact this
  refine (hg.comp hw).congr fun u => ?_
  simp only [Function.comp_apply, hermiteAntideriv, stdNormalPDF]
  rw [neg_div]
  ring_nf

lemma continuous_stdNormalPDF : Continuous stdNormalPDF := by
  change Continuous fun x : ℝ => Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)
  fun_prop

lemma integrable_stdNormalPDF_mul_pow (k : ℕ) :
    Integrable (fun y : ℝ => stdNormalPDF y * y ^ k) := by
  refine Integrable.mono' ((integrable_abs_pow_mul_gauss k).const_mul
      (Real.sqrt (2 * Real.pi))⁻¹)
    (continuous_stdNormalPDF.mul (continuous_pow k)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  refine le_of_eq ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, stdNormalPDF, abs_div,
    abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (Real.sqrt_nonneg _), neg_div]
  ring

lemma integrable_stdNormalPDF : Integrable stdNormalPDF := by
  simpa using integrable_stdNormalPDF_mul_pow 0

lemma integrable_stdNormalPDF_mul_hermite3 :
    Integrable (fun y : ℝ => stdNormalPDF y * (y ^ 3 - 3 * y)) := by
  have h3 := integrable_stdNormalPDF_mul_pow 3
  have h1 := (integrable_stdNormalPDF_mul_pow 1).const_mul (3 : ℝ)
  refine (h3.sub h1).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply]
  ring

lemma integrable_edgeworthDensity (γ : ℝ) (n : ℕ) :
    Integrable (edgeworthDensity γ n) := by
  have hh := integrable_stdNormalPDF_mul_hermite3.const_mul (γ / 6 * (Real.sqrt n)⁻¹)
  refine (integrable_stdNormalPDF.fun_add hh).congr (Filter.Eventually.of_forall fun y => ?_)
  rw [edgeworthDensity]
  ring

lemma setIntegral_Iic_stdNormalPDF_mul_hermite3 (u : ℝ) :
    (∫ y in Set.Iic u, stdNormalPDF y * (y ^ 3 - 3 * y)) = hermiteAntideriv u := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (f := hermiteAntideriv)
    (f' := fun y : ℝ => stdNormalPDF y * (y ^ 3 - 3 * y)) (a := u) (m := 0)
    (fun x _ => hasDerivAt_hermiteAntideriv x)
    integrable_stdNormalPDF_mul_hermite3.integrableOn tendsto_hermiteAntideriv_atBot
  rw [h, sub_zero]

theorem densityCDF_edgeworthDensity (γ : ℝ) (n : ℕ) (u : ℝ) :
    densityCDF (edgeworthDensity γ n) u = edgeworthCDF γ n u := by
  have hsplit : ∀ y : ℝ, edgeworthDensity γ n y
      = stdNormalPDF y + (γ / 6 * (Real.sqrt n)⁻¹) * (stdNormalPDF y * (y ^ 3 - 3 * y)) := by
    intro y
    rw [edgeworthDensity]
    ring
  rw [densityCDF, setIntegral_congr_fun measurableSet_Iic fun y _ => hsplit y,
    integral_add integrable_stdNormalPDF.integrableOn
      (integrable_stdNormalPDF_mul_hermite3.const_mul _).integrableOn,
    MeasureTheory.integral_const_mul, setIntegral_Iic_stdNormalPDF_mul_hermite3,
    ← stdNormalCDF_eq_setIntegral, hermiteAntideriv, edgeworthCDF]
  ring

private lemma exp_neg_half_sq_mul_abs_pow_le (k : ℕ) (u : ℝ) :
    Real.exp (-u ^ 2 / 2) * |u| ^ k ≤ 4 ^ k * (Nat.factorial k : ℝ) := by
  have hmul : Real.exp (-u ^ 2 / 2) * |u| ^ k
      ≤ Real.exp (-u ^ 2 / 2) * (4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4)) :=
    mul_le_mul_of_nonneg_left (abs_pow_le_exp k u) (Real.exp_pos _).le
  have heq : Real.exp (-u ^ 2 / 2) * (4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4))
      = 4 ^ k * (Nat.factorial k : ℝ) * Real.exp (-u ^ 2 / 4) := by
    rw [show Real.exp (-u ^ 2 / 2) * (4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4))
          = 4 ^ k * (Nat.factorial k : ℝ)
            * (Real.exp (-u ^ 2 / 2) * Real.exp (u ^ 2 / 4)) from by ring,
      ← Real.exp_add]
    congr 2
    ring
  have hle1 : Real.exp (-u ^ 2 / 4) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
  have hCnn : (0 : ℝ) ≤ 4 ^ k * (Nat.factorial k : ℝ) := by positivity
  calc Real.exp (-u ^ 2 / 2) * |u| ^ k
      ≤ Real.exp (-u ^ 2 / 2) * (4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4)) := hmul
    _ = 4 ^ k * (Nat.factorial k : ℝ) * Real.exp (-u ^ 2 / 4) := heq
    _ ≤ 4 ^ k * (Nat.factorial k : ℝ) * 1 := by nlinarith
    _ = 4 ^ k * (Nat.factorial k : ℝ) := mul_one _

private lemma stdNormalPDF_mul_abs_pow_le (k : ℕ) {C : ℝ}
    (hC : 4 ^ k * (Nat.factorial k : ℝ) ≤ C) (u : ℝ) :
    stdNormalPDF u * |u| ^ k ≤ (Real.sqrt (2 * Real.pi))⁻¹ * C := by
  have hrw : stdNormalPDF u * |u| ^ k
      = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-u ^ 2 / 2) * |u| ^ k) := by
    rw [stdNormalPDF]; ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_left ((exp_neg_half_sq_mul_abs_pow_le k u).trans hC)
    (by positivity)

theorem abs_edgeworthDensity_le (γ : ℝ) {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    |edgeworthDensity γ n u| ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |γ|) := by
  have hpdfnn : 0 ≤ stdNormalPDF u := by rw [stdNormalPDF]; positivity
  have hsqrt0 : (0 : ℝ) ≤ (Real.sqrt n)⁻¹ := by positivity
  have hsqrt : (Real.sqrt n)⁻¹ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (1 : ℝ) ≤ Real.sqrt n := by
      simpa using Real.sqrt_le_sqrt h1
    exact inv_le_one_of_one_le₀ h2
  have habs3 : |u ^ 3 - 3 * u| ≤ |u| ^ 3 + 3 * |u| := by
    have h := abs_add_le (u ^ 3) (-(3 * u))
    rw [abs_neg] at h
    calc |u ^ 3 - 3 * u| = |u ^ 3 + -(3 * u)| := by rw [sub_eq_add_neg]
      _ ≤ |u ^ 3| + |3 * u| := h
      _ = |u| ^ 3 + 3 * |u| := by
          rw [abs_pow, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have hbracket : |1 + γ / 6 * (u ^ 3 - 3 * u) * (Real.sqrt n)⁻¹|
      ≤ 1 + |γ| / 6 * (|u| ^ 3 + 3 * |u|) := by
    have htri := abs_add_le (1 : ℝ) (γ / 6 * (u ^ 3 - 3 * u) * (Real.sqrt n)⁻¹)
    rw [abs_one] at htri
    have hval : |γ / 6 * (u ^ 3 - 3 * u) * (Real.sqrt n)⁻¹|
        = |γ| / 6 * |u ^ 3 - 3 * u| * (Real.sqrt n)⁻¹ := by
      rw [abs_mul, abs_mul, abs_div, abs_of_nonneg hsqrt0]
      try norm_num
    have hnn : (0 : ℝ) ≤ |γ| / 6 * |u ^ 3 - 3 * u| := by positivity
    have hstep : |γ / 6 * (u ^ 3 - 3 * u) * (Real.sqrt n)⁻¹|
        ≤ |γ| / 6 * (|u| ^ 3 + 3 * |u|) := by
      rw [hval]
      calc |γ| / 6 * |u ^ 3 - 3 * u| * (Real.sqrt n)⁻¹
          ≤ |γ| / 6 * |u ^ 3 - 3 * u| * 1 := mul_le_mul_of_nonneg_left hsqrt hnn
        _ = |γ| / 6 * |u ^ 3 - 3 * u| := mul_one _
        _ ≤ |γ| / 6 * (|u| ^ 3 + 3 * |u|) :=
            mul_le_mul_of_nonneg_left habs3 (by positivity)
    linarith [htri, hstep]
  have hkey : |edgeworthDensity γ n u|
      ≤ stdNormalPDF u * (1 + |γ| / 6 * (|u| ^ 3 + 3 * |u|)) := by
    rw [edgeworthDensity, abs_mul, abs_of_nonneg hpdfnn]
    exact mul_le_mul_of_nonneg_left hbracket hpdfnn
  have hb0 := stdNormalPDF_mul_abs_pow_le 0 (C := 1) (by norm_num) u
  have hb1 := stdNormalPDF_mul_abs_pow_le 1 (C := 4) (by norm_num [Nat.factorial]) u
  have hb3 := stdNormalPDF_mul_abs_pow_le 3 (C := 384) (by norm_num [Nat.factorial]) u
  rw [pow_zero, mul_one, mul_one] at hb0
  rw [pow_one] at hb1
  have e1 := mul_le_mul_of_nonneg_left hb1 (by positivity : (0 : ℝ) ≤ |γ| / 2)
  have e3 := mul_le_mul_of_nonneg_left hb3 (by positivity : (0 : ℝ) ≤ |γ| / 6)
  have hexp : stdNormalPDF u * (1 + |γ| / 6 * (|u| ^ 3 + 3 * |u|))
      = stdNormalPDF u + |γ| / 6 * (stdNormalPDF u * |u| ^ 3)
        + |γ| / 2 * (stdNormalPDF u * |u|) := by ring
  rw [hexp] at hkey
  linarith [hkey, hb0, e1, e3]

theorem charFunDensity_edgeworthDensity (γ : ℝ) (n : ℕ) (t : ℝ) :
    charFunDensity (edgeworthDensity γ n) t
      = Complex.exp (-(t : ℂ) ^ 2 / 2)
        * (1 - Complex.I * (γ : ℂ) * (t : ℂ) ^ 3
            * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) / 6) := by
  have hint1 : Integrable (fun u : ℝ =>
      Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I) * Complex.exp (-(u : ℂ) ^ 2 / 2)) := by
    refine (integrable_cubic_mul_cexp_mul_gaussian t 0 0 0 1).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have hint2 : Integrable (fun u : ℝ => ((u : ℂ) ^ 3 - 3 * (u : ℂ)) *
      (Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I) * Complex.exp (-(u : ℂ) ^ 2 / 2))) := by
    refine (integrable_cubic_mul_cexp_mul_gaussian t 1 0 (-3) 0).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have hcong : ∀ y : ℝ,
      Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * ((edgeworthDensity γ n y : ℝ) : ℂ)
      = (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
          ((((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
              (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
                * Complex.exp (-(y : ℂ) ^ 2 / 2)))
            + Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
                * Complex.exp (-(y : ℂ) ^ 2 / 2)) := by
    intro y
    simp only [edgeworthDensity, stdNormalPDF]
    push_cast
    ring
  have hpull1 : (∫ y : ℝ, (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
        ((((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
            (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
              * Complex.exp (-(y : ℂ) ^ 2 / 2)))
          + Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * Complex.exp (-(y : ℂ) ^ 2 / 2)))
      = (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
        ∫ y : ℝ, ((((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
            (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
              * Complex.exp (-(y : ℂ) ^ 2 / 2)))
          + Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * Complex.exp (-(y : ℂ) ^ 2 / 2)) :=
    MeasureTheory.integral_const_mul _ _
  have hadd : (∫ y : ℝ, ((((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
            (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
              * Complex.exp (-(y : ℂ) ^ 2 / 2)))
          + Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * Complex.exp (-(y : ℂ) ^ 2 / 2)))
      = (∫ y : ℝ, (((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
            (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
              * Complex.exp (-(y : ℂ) ^ 2 / 2))))
        + ∫ y : ℝ, Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
            * Complex.exp (-(y : ℂ) ^ 2 / 2) :=
    integral_add (hint2.const_mul _) hint1
  have hpull2 : (∫ y : ℝ, (((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
        (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * Complex.exp (-(y : ℂ) ^ 2 / 2))))
      = (((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) *
        ∫ y : ℝ, ((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
          (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * Complex.exp (-(y : ℂ) ^ 2 / 2)) :=
    MeasureTheory.integral_const_mul _ _
  rw [charFunDensity, integral_congr_ae (Filter.Eventually.of_forall hcong), hpull1, hadd,
    hpull2, integral_hermite3_mul_cexp_mul_gaussian, integral_cexp_mul_gaussian]
  have hS : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    exact_mod_cast hpos.ne'
  have hcube : ((t : ℂ) * Complex.I) ^ 3 = -(Complex.I * (t : ℂ) ^ 3) := by
    have hI3 : (Complex.I) ^ 3 = -Complex.I := by
      rw [pow_succ, Complex.I_sq]; ring
    rw [mul_pow, hI3]; ring
  rw [hcube]
  push_cast
  field_simp
  ring

end StatLean.HypothesisTesting
end
