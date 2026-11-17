/- GID: D5/S3/Quantum/Algebra/OriginalCompactActionMetric
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/OriginalCompactActionMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An invariant positive form for original compact-action velocities. -/

module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

/-!
The Gram-operator construction is adapted from TauCeti's compact representation
unitarization at immutable revision 57ab0f657d7fb33d7c9425bf696bec3045b0fd75,
`TauCeti/RepresentationTheory/Compact/Unitarizable.lean`.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0; the full license is reproduced below.
The inverse action permits use of Mathlib's left Haar measure without a
probability-measure normalization. The construction stays on the given W.
Retire the port when the project's own pinned Mathlib supplies an equivalent
compact-action invariant positive form, and directly use that supplier.
-/

@[expose] public section

namespace D5.S3.Quantum.Algebra.OriginalCompactActionMetric

open MeasureTheory
open scoped InnerProductSpace
noncomputable section
universe u
variable {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

abbrev MatrixGroup (W : Type u) [NormedAddCommGroup W] [InnerProductSpace ℝ W] :=
  Subgroup (W →L[ℝ] W)ˣ

variable (G : MatrixGroup W) [CompactSpace G]

local instance : MeasurableSpace G := borel G
local instance : BorelSpace G := ⟨rfl⟩

private def act (g : G) : W →L[ℝ] W := (g.val : W →L[ℝ] W)

omit [FiniteDimensional ℝ W] [CompactSpace G] in
private theorem act_continuous : Continuous (act G) :=
  Units.continuous_val.comp continuous_subtype_val

private def gramFamily (g : G) : W →L[ℝ] W :=
  (act G g⁻¹).adjoint.comp (act G g⁻¹)

omit [CompactSpace G] in
private theorem gramFamily_continuous : Continuous (gramFamily G) := by
  exact (ContinuousLinearMap.compL ℝ W W W).continuous₂.comp
    (((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := W) (F := W)).continuous.comp
      ((act_continuous G).comp continuous_inv)).prodMk
      ((act_continuous G).comp continuous_inv))

private def gram : W →L[ℝ] W :=
  ∫ g : G, gramFamily G g ∂Measure.haar

private theorem gram_inner (v w : W) :
    ⟪v,gram G w⟫_ℝ =
          ∫ g : G, ⟪act G g⁻¹ v,act G g⁻¹ w⟫_ℝ ∂Measure.haar := by
  have hi : Integrable (gramFamily G) (Measure.haar : Measure G) :=
    (gramFamily_continuous G).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ W w)).integral_comp_comm hi
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    innerSL_apply_apply] at h
  change ⟪v,(∫ g : G, gramFamily G g ∂Measure.haar) w⟫_ℝ = _
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g =>
    ContinuousLinearMap.adjoint_inner_right (act G g⁻¹) v (act G g⁻¹ w)

private theorem gram_invariant (g : G) (v w : W) :
    ⟪act G g v,gram G (act G g w)⟫_ℝ = ⟪v,gram G w⟫_ℝ := by
  rw [gram_inner,gram_inner]
  simpa [act,mul_inv_rev] using integral_mul_left_eq_self (μ := (Measure.haar : Measure G))
    (fun h : G => ⟪act G h⁻¹ v,act G h⁻¹ w⟫_ℝ) g⁻¹

private theorem gram_positive (v : W) (hv : v ≠ 0) :
    0 < ⟪v,gram G v⟫_ℝ := by
  rw [gram_inner]
  have hc : Continuous (fun g : G => ⟪act G g⁻¹ v,act G g⁻¹ v⟫_ℝ) := by
    exact (((act_continuous G).comp continuous_inv).clm_apply continuous_const).inner
      (((act_continuous G).comp continuous_inv).clm_apply continuous_const)
  apply integral_pos_of_integrable_nonneg_nonzero (x := (1 : G)) hc
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  · intro g
    exact real_inner_self_nonneg
  · simpa [act] using (inner_self_ne_zero.mpr hv : ⟪v,v⟫_ℝ ≠ 0)

@[instance_reducible] private def invariantCore : InnerProductSpace.Core ℝ W where
  inner v w := ⟪v,gram G w⟫_ℝ
  conj_inner_symm v w := by
    simp only [conj_trivial]
    rw [gram_inner,gram_inner]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => real_inner_comm _ _)
  re_inner_nonneg v := by
    change 0 ≤ ⟪v,gram G v⟫_ℝ
    by_cases hv : v = 0
    · simp [hv]
    · exact (gram_positive G v hv).le
  add_left v w z := inner_add_left _ _ _
  smul_left v w r := by simp [real_inner_smul_left]
  definite v hv := by
    by_contra hn
    exact (ne_of_gt (gram_positive G v hn)) hv

omit [CompactSpace G] in
/-- The original compact action supplies a positive invariant metric, and every
actual original-group curve through the identity has a skew velocity. -/
theorem compact_action_metric (hG : IsCompact (G : Set (W →L[ℝ] W)ˣ)) :
    ∃ B : InnerProductSpace.Core ℝ W,
      (∀ (g : G) (u v : W),
        B.inner ((g.val : W →L[ℝ] W) u) ((g.val : W →L[ℝ] W) v) = B.inner u v) ∧
      ∀ (c : ℝ → G), c 0 = 1 → ∀ K : W →L[ℝ] W,
        HasDerivAt (fun t => (c t).val.val) K 0 →
        ∀ u v : W, B.inner (K u) v = -B.inner u (K v) := by
  letI : CompactSpace G := isCompact_iff_compactSpace.mp hG
  refine ⟨invariantCore G, fun g u v => gram_invariant G g u v, ?_⟩
  intro c hc K hK u v
  have hu := hK.clm_apply (hasDerivAt_const (0 : ℝ) u)
  have hv := hK.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hSv := (hasDerivAt_const (0 : ℝ) (gram G)).clm_apply hv
  have hd := hu.inner ℝ hSv
  have he : (fun t => ⟪(c t).val.val u,gram G ((c t).val.val v)⟫_ℝ) =
      fun _ : ℝ => ⟪u,gram G v⟫_ℝ := by
    funext t
    exact gram_invariant G (c t) u v
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) ⟪u,gram G v⟫_ℝ)
  simp only [hc,OneMemClass.coe_one,Units.val_one,ContinuousLinearMap.one_apply,
    ContinuousLinearMap.zero_apply,add_zero,zero_add] at hz
  change ⟪K u,gram G v⟫_ℝ = -⟪u,gram G (K v)⟫_ℝ
  linarith

end
end D5.S3.Quantum.Algebra.OriginalCompactActionMetric


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
