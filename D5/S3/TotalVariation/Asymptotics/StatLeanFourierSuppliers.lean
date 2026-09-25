/- GID: D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian Hermite integrals and the signed Edgeworth density and distribution function. -/

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

import D5.S3.TotalVariation.Asymptotics.StatLeanSignedSmoothing

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
