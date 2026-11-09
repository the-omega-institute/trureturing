/- GID: D5/S3/Quantum/Algebra/TopologicalSchur
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/TopologicalSchur
   mirror-E: none(waiver:upstream-source-reuse)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic]
   utility: none
   digest: Upstream selfadjoint Schur for closed invariant subspaces. -/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-! Selfadjoint Schur's lemma, transplanted from the immutable source below.
Retire this transplant when the pinned mathlib supplies the same closed-subspace theorem. -/

/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Authors: Keisuke Suzuki
Source: kencyke/quantum-system@5d67fe8030eaf1bdaf081e2acfcbe3fbaecfda7c
QuantumSystem/ForMathlib/Analysis/InnerProductSpace/InvariantSubspace.lean
SHA256: 96a1bbcca39cff497d9f703db546646663f72b7b3fc330d37ba7713c56bfdec4
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
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

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

noncomputable section
namespace InnerProductSpace
open scoped InnerProduct ComplexInnerProductSpace ComplexStarModule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "⟪" x ", " y "⟫" => inner ℂ x y
def IsTopologicallyIrreducible (S : Set (H →L[ℂ] H)) : Prop :=
  ∀ K : ClosedSubmodule ℂ H,
    (∀ T ∈ S, K.toSubmodule ∈ Module.End.invtSubmodule (T : Module.End ℂ H)) → K = ⊥ ∨ K = ⊤

omit [CompleteSpace H] in
lemma ker_mem_invtSubmodule_of_commute {G T : H →L[ℂ] H} (h : Commute G T) :
    G.ker ∈ Module.End.invtSubmodule (T : Module.End ℂ H) := by
  refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun x hx => ?_
  have hx' : G x = 0 := hx
  change G (T x) = 0
  rw [← mul_apply_eq_comp, h.eq, mul_apply_eq_comp, hx', map_zero]

/-- If the only closed `S`-invariant subspaces are `⊥` and `⊤`, a self-adjoint operator commuting
with every element of `S` is a real scalar. Two distinct points `r ≠ s` of its spectrum would give,
through the continuous functional calculus, nonzero operators `F`, `G` commuting with `S` with
`G F = 0`; the kernel of `G` would then be a closed invariant subspace that is neither `⊥` (it
contains the range of `F`) nor `⊤` (as `G ≠ 0`). -/
lemma exists_eq_algebraMap_of_isSelfAdjoint_of_commute {S : Set (H →L[ℂ] H)}
    (hS : IsTopologicallyIrreducible S)
    {y : H →L[ℂ] H} (hy : IsSelfAdjoint y) (hcomm : ∀ T ∈ S, Commute y T) :
    ∃ r : ℝ, y = algebraMap ℝ (H →L[ℂ] H) r := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact ⟨0, ContinuousLinearMap.ext fun x => Subsingleton.elim _ _⟩
  obtain ⟨r, hr⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) y hy
  refine ⟨r, CFC.eq_algebraMap_of_spectrum_subset_singleton y r fun s hs => ?_⟩
  by_contra hsr
  rw [Set.mem_singleton_iff] at hsr
  set ε := |s - r| / 2 with hε_def
  have hε : 0 < ε := half_pos (abs_pos.mpr (sub_ne_zero.mpr hsr))
  -- Bumps of height `ε` at `r` and at `s` with disjoint supports.
  set f : ℝ → ℝ := fun t => max 0 (ε - |t - r|) with hf_def
  set g : ℝ → ℝ := fun t => max 0 (ε - |t - s|) with hg_def
  have hgf : (fun t => g t * f t) = (0 : ℝ → ℝ) := by
    funext t
    have htri : |s - r| ≤ |t - r| + |t - s| := by
      calc |s - r| = |(t - r) - (t - s)| := by ring_nf
        _ ≤ |t - r| + |t - s| := abs_sub _ _
    rcases le_total (ε - |t - r|) 0 with h1 | h1
    · simp [f, max_eq_left h1]
    · have h2 : ε - |t - s| ≤ 0 := by linarith
      simp [g, max_eq_left h2]
  have hF : cfc f y ≠ 0 := by
    intro h0
    have := ((cfc_eq_cfc_iff_eqOn (a := y) (f := f) (g := 0)).mp
      (h0.trans (cfc_zero (R := ℝ) (a := y)).symm)) hr
    simp only [f, sub_self, abs_zero, sub_zero, Pi.zero_apply] at this
    linarith [le_of_max_le_right this.le]
  have hG : cfc g y ≠ 0 := by
    intro h0
    have := ((cfc_eq_cfc_iff_eqOn (a := y) (f := g) (g := 0)).mp
      (h0.trans (cfc_zero (R := ℝ) (a := y)).symm)) hs
    simp only [g, sub_self, abs_zero, sub_zero, Pi.zero_apply] at this
    linarith [le_of_max_le_right this.le]
  have hGF : cfc g y * cfc f y = 0 := by rw [← cfc_mul g f y, hgf, cfc_zero]
  rcases hS ⟨(cfc g y).ker, (cfc g y).isClosed_ker⟩
      (fun T hT => ker_mem_invtSubmodule_of_commute ((hcomm T hT).cfc_real g)) with hb | ht
  · refine hF (ContinuousLinearMap.ext fun x => ?_)
    have hx : cfc f y x ∈ (⟨(cfc g y).ker, (cfc g y).isClosed_ker⟩ : ClosedSubmodule ℂ H) := by
      change cfc g y (cfc f y x) = 0
      rw [← mul_apply_eq_comp, hGF, zero_apply]
    rw [hb] at hx
    simpa using hx
  · refine hG (ContinuousLinearMap.ext fun x => ?_)
    have hx : x ∈ (⟨(cfc g y).ker, (cfc g y).isClosed_ker⟩ : ClosedSubmodule ℂ H) := by
      rw [ht]; trivial
    simpa using hx


end InnerProductSpace
