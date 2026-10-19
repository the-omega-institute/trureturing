/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected MCMC finite Perron proof supporting actual weighted graphs. -/
/- Transplanted from or4nge19/MCMC@b901242fd04b6eff425a177e5c9bc6c56257bc62.
Copyright and attribution notices below retained; full license: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean.
Changes: module imports relocated; comment formatting, placement and blank lines adapted for the canonical weighted-graph consumer.
Matteo Cipollina. Changes: unused declarations and branches removed; retained live proof steps preserved; unused local proof terms removed. -/
/- Full upstream Apache-2.0 license, reproduced verbatim.
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
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.Spectrum
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Int.Star
open Filter Set Finset Matrix Topology Convex
theorem eventually_to_open {α : Type*} [TopologicalSpace α] {p : α → Prop} {a : α}
    (h : ∀ᶠ x in 𝓝 a, p x) :
    ∃ (U : Set α), IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, p x := by
  rcases mem_nhds_iff.mp h with ⟨U, hU_open, haU, hU⟩
  simp_all only
  apply Exists.intro
  · apply And.intro
    on_goal 2 => apply And.intro
    on_goal 2 => {exact hU
    }
    · simp_all only
    · intro x a_1
      apply hU_open
      simp_all only
theorem continuousOn_finset_inf' {α β : Type*} [TopologicalSpace α] [LinearOrder β]
    [TopologicalSpace β] [OrderTopology β] {ι : Type*} [Fintype ι]
    {s : Finset ι} {U : Set α} (hs : s.Nonempty) {f : ι → α → β}
    (hf : ∀ i ∈ s, ContinuousOn (f i) U) :
    ContinuousOn (fun x => s.inf' hs (fun i => f i x)) U :=
  ContinuousOn.finset_inf'_apply hs hf
theorem finset_inf'_mono_subset {α β : Type*} [LinearOrder β] {s t : Finset α} (h : s ⊆ t)
    {f : α → β} {hs : s.Nonempty} {ht : t.Nonempty} :
    t.inf' ht f ≤ s.inf' hs f := by
  exact inf'_mono f h hs
theorem mulVec_nonneg {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx : ∀ i, 0 ≤ x i) : ∀ i, 0 ≤ (A *ᵥ x) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j)
theorem exists_pos_of_sum_one_of_nonneg {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ}
    (hsum : ∑ i, x i = 1) (hnonneg : ∀ i, 0 ≤ x i) : ∃ j, 0 < x j := by
  by_contra h
  push_neg at h
  have h_all_zero : ∀ i, x i = 0 := by
    intro i
    exact le_antisymm (h i) (hnonneg i)
  have h_sum_zero : ∑ i, x i = 0 := by
    simp only [h_all_zero, Finset.sum_const_zero]
  have : 1 = 0 := by linarith
  exact absurd this (by norm_num)
lemma Finset.inf'_eq_ciInf {α β} [ConditionallyCompleteLinearOrder β] {s : Finset α}
    (h : s.Nonempty) (f : α → β) :
    s.inf' h f = ⨅ i : s, f i := by
  have : Nonempty s := Finset.Nonempty.to_subtype h
  rw [Finset.inf'_eq_csInf_image]
  congr
  ext x
  simp [Set.mem_image, Set.mem_range]
variable {n : Type*}
lemma exists_pos_of_ne_zero [Fintype n] [DecidableEq n] {v : n → ℝ} (h_nonneg : ∀ i, 0 ≤ v i) (h_ne_zero : v ≠ 0) :
    ∃ i, 0 < v i := by
  by_contra h_all_nonpos
  apply h_ne_zero
  ext i
  exact le_antisymm (by simp_all) (h_nonneg i)
lemma exists_pos_maximal_of_nonneg_ne_zero [Fintype n] [Nonempty n] [DecidableEq n] {v : n → ℝ}
    (h_nonneg : ∀ i, 0 ≤ v i) (h_ne_zero : v ≠ 0) :
    ∃ i, 0 < v i ∧ ∀ j, v j ≤ v i := by
  obtain ⟨i, -, hi_max⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
  obtain ⟨j, hj_pos⟩ := exists_pos_of_ne_zero h_nonneg h_ne_zero
  refine ⟨i, ?_, ?_⟩
  · refine lt_of_lt_of_le hj_pos ?_
    rw [← hi_max]
    exact Finset.le_sup' v (Finset.mem_univ j)
  · intro j
    rw [← hi_max]
    exact Finset.le_sup' v (Finset.mem_univ j)
lemma Set.toFinset_nonempty_iff {α : Type*} [Fintype α] [DecidableEq α] (s : Set α) [Finite s] [Fintype s] :
    s.toFinset.Nonempty ↔ s.Nonempty := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Set.mem_toFinset.mp hx⟩
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Set.mem_toFinset.mpr hx⟩
lemma div_le_iff {a b c : ℝ} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  rw [@le_iff_le_iff_lt_iff_lt]
  exact lt_div_iff₀ hb
lemma Finset.inf'_pos {α : Type*} {s : Finset α} (hs : s.Nonempty)
    {f : α → ℝ} (h_pos : ∀ a ∈ s, 0 < f a) :
    0 < s.inf' hs f := by
  obtain ⟨b, hb_mem, h_fb_is_inf⟩ := s.exists_mem_eq_inf' hs f
  have h_fb_pos : 0 < f b := h_pos b hb_mem
  rw [h_fb_is_inf]
  exact h_fb_pos
lemma ones_norm_mem_simplex [Fintype n] [Nonempty n] :
  (fun _ => (Fintype.card n : ℝ)⁻¹) ∈ stdSimplex ℝ n := by
  dsimp [stdSimplex]; constructor
  · intro i; apply inv_nonneg.2; norm_cast; exact Nat.cast_nonneg _
  · simp [Finset.sum_const, Finset.card_univ];
lemma ne_zero_of_mem_stdSimplex
    {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ}
    (hx : x ∈ stdSimplex ℝ n) :
    x ≠ 0 := by
  intro h_zero
  have h_sum_zero : (∑ i, x i) = 0 := by
    subst h_zero
    simp_all only [Pi.zero_apply, Finset.sum_const_zero]
  have h_sum_one : (∑ i, x i) = 1 := hx.2
  linarith
namespace Matrix
lemma diagonal_mulVec_ones [DecidableEq n][Fintype n] (d : n → ℝ) :
    diagonal d *ᵥ (fun _ => 1) = d := by
  ext i; simp [mulVec_diagonal]
lemma diagonal_inv_mulVec_self [DecidableEq n][Fintype n] {d : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    diagonal (d⁻¹) *ᵥ d = fun _ => 1 := by
  ext i
  simp [mulVec_diagonal]
  simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel]
lemma diagonal_mulVec_diagonal_inv_mulVec [DecidableEq n] [Fintype n]
    {d x : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    diagonal d *ᵥ (diagonal (d⁻¹) *ᵥ x) = x := by
  ext i
  simp [mulVec_diagonal, hd i]
lemma diagonal_mulVec_mono [DecidableEq n] [Fintype n] {d x y : n → ℝ}
    (hd_nonneg : ∀ i, 0 ≤ d i) (hxy : x ≤ y) :
    diagonal d *ᵥ x ≤ diagonal d *ᵥ y := by
  intro i
  rw [mulVec_diagonal, mulVec_diagonal]
  exact mul_le_mul_of_nonneg_left (hxy i) (hd_nonneg i)
end Matrix
variable {α ι : Type*} {f : ι → α} {s : Set ι}
open Set
