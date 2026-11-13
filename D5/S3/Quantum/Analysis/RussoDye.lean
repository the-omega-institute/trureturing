/- GID: D5/S3/Quantum/Analysis/RussoDye
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RussoDye
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unitary convex-hull and finite-mean theorems for complex C-star algebras. -/

/-
admission_basis: escape-witness
escape_witness: exists_unitary_sum_eq_nsmul_add
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27516
Declarations (definition rows carry no proof-shape claim):
exists_mem_unitary_eq_mul_cfcAbs: proof_shape: content; consumers: exists_unitary_add_eq_two_smul_of_isUnit.
exists_unitary_add_eq_two_smul_of_isUnit: proof_shape: content; consumers: exists_unitary_add_eq_add_unitary.
exists_unitary_add_eq_add_unitary: proof_shape: content; consumers: exists_unitary_sum_eq_nsmul_add.
exists_unitary_sum_eq_nsmul_add: proof_shape: content; consumers: exists_unitary_eq_mean_of_norm_lt.
exists_unitary_eq_mean_of_norm_lt: proof_shape: content; consumers: ball_subset_convexHull_unitary.
ball_subset_convexHull_unitary: proof_shape: content; consumers: closedConvexHull_unitary.
closedConvexHull_unitary: proof_shape: content; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital.seminorm_bound_of_unitary_bound.
-/

/-
This file adapts the namespace and visibility of the Apache-2.0 supplier
kencyke/quantum-system, commit 5d67fe8030eaf1bdaf081e2acfcbe3fbaecfda7c,
QuantumSystem/ForMathlib/Analysis/CStarAlgebra/RussoDye.lean.
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

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace D5.S3.Quantum.Analysis.RussoDye

/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
open Metric
open scoped Topology

variable {A : Type*} [CStarAlgebra A]

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

/-- The **polar decomposition** of an invertible element of a unital C⋆-algebra: `z = w |z|` with
`w` unitary, where `|z| = √(z⋆ z)` (`CFC.abs z`). The square `|z| |z| = z⋆ z` is invertible, hence
so is `|z|`; `w = z |z|⁻¹` has `w⋆ w = |z|⁻¹ z⋆ z |z|⁻¹ = 1`, and `w` is invertible, so also
`w w⋆ = 1`. -/
lemma exists_mem_unitary_eq_mul_cfcAbs {z : A} (hz : IsUnit z) :
    ∃ w ∈ unitary A, z = w * CFC.abs z := by
  have hsa : IsSelfAdjoint (CFC.abs z) := (CFC.abs_nonneg z).isSelfAdjoint
  obtain ⟨c, hc⟩ : IsUnit (CFC.abs z) :=
    isUnit_mul_self_iff.mp (CFC.abs_mul_abs z ▸ hz.star.mul hz)
  obtain ⟨W, hW⟩ := hz.mul (c⁻¹).isUnit
  have hzc : z = W * CFC.abs z := by rw [hW, ← hc, mul_assoc, Units.inv_mul, mul_one]
  have hstar : star (W : A) * W = 1 := by
    have h₁ : star ((c⁻¹ : Aˣ) : A) * CFC.abs z = 1 := by
      rw [← hsa.star_eq, ← star_mul, ← hc, Units.mul_inv, star_one]
    calc star (W : A) * W = star ((c⁻¹ : Aˣ) : A) * (star z * z) * (c⁻¹ : Aˣ) := by
          rw [hW, star_mul]; noncomm_ring
      _ = star ((c⁻¹ : Aˣ) : A) * CFC.abs z * (CFC.abs z * (c⁻¹ : Aˣ)) := by
          rw [← CFC.abs_mul_abs z]; noncomm_ring
      _ = 1 := by rw [h₁, ← hc, Units.mul_inv, one_mul]
  refine ⟨W, Unitary.mem_iff.2 ⟨hstar, ?_⟩, hzc⟩
  rw [← Units.inv_eq_of_mul_eq_one_left hstar, Units.mul_inv]

end Ordered

section

/-- An invertible contraction `z` of a unital C⋆-algebra is the mean of two unitaries. With the
polar decomposition `z = w |z|` (`IsUnit.exists_mem_unitary_eq_mul_cfcAbs`), the self-adjoint
contraction `|z|` is the mean of the unitaries `v = |z| + i √(1 - |z|²)` and `v⋆`, so
`2 z = w v + w v⋆`. -/
private lemma exists_unitary_add_eq_two_smul_of_isUnit {z : A} (hz : IsUnit z) (hz₁ : ‖z‖ ≤ 1) :
    ∃ u₁ u₂ : unitary A, (u₁ : A) + u₂ = (2 : ℝ) • z := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  obtain ⟨w, hw, hzw⟩ := exists_mem_unitary_eq_mul_cfcAbs hz
  let s : selfAdjoint A := ⟨CFC.abs z, (CFC.abs_nonneg z).isSelfAdjoint⟩
  have hs : ‖s‖ ≤ 1 := by
    change ‖CFC.abs z‖ ≤ 1
    rwa [CFC.norm_abs]
  let v := selfAdjoint.unitarySelfAddISMul s hs
  let w' : unitary A := ⟨w, hw⟩
  refine ⟨w' * v, w' * star v, ?_⟩
  have hv : (v : A) + (star v : unitary A) = (2 : ℝ) • (s : A) := by
    rw [Unitary.coe_star, selfAdjoint.star_coe_unitarySelfAddISMul,
      selfAdjoint.unitarySelfAddISMul_coe]
    module
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← mul_add, hv, hzw, mul_smul_comm]

/-- If `‖x‖ < 1` and `u` is unitary, then `x + u` is the sum of two unitaries:
`u + x = u (1 + u⋆ x)` is invertible since `‖u⋆ x‖ = ‖x‖ < 1`, and `‖(x + u) / 2‖ ≤ 1`, so
`CStarAlgebra.exists_unitary_add_eq_two_smul_of_isUnit` applies to `(x + u) / 2`. -/
private lemma exists_unitary_add_eq_add_unitary {x : A} (hx : ‖x‖ < 1) (u : unitary A) :
    ∃ u₁ u₂ : unitary A, x + u = u₁ + u₂ := by
  have hux : x + u = u * (1 + star (u : A) * x) := by
    rw [mul_add, mul_one, ← mul_assoc, Unitary.mul_star_self_of_mem u.2, one_mul, add_comm]
  have h₁ : IsUnit (1 + star (u : A) * x) := by
    have h : ‖-(star (u : A) * x)‖ < 1 := by
      rwa [norm_neg, ← Unitary.coe_star, CStarRing.norm_coe_unitary_mul]
    simpa using (Units.oneSub _ h).isUnit
  have hunit : IsUnit ((2⁻¹ : ℝ) • (x + u)) := by
    rw [hux]
    exact (Unitary.isUnit_coe.mul h₁).smul (Units.mk0 (2⁻¹ : ℝ) (by norm_num))
  have hnorm : ‖(2⁻¹ : ℝ) • (x + u)‖ ≤ 1 := by
    have hu : ‖(u : A)‖ ≤ 1 := by
      nontriviality A
      rw [CStarRing.norm_coe_unitary]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    calc 2⁻¹ * ‖x + u‖ ≤ 2⁻¹ * (‖x‖ + ‖(u : A)‖) := by gcongr; exact norm_add_le _ _
      _ ≤ 1 := by linarith
  obtain ⟨u₁, u₂, h⟩ := exists_unitary_add_eq_two_smul_of_isUnit hunit hnorm
  refine ⟨u₁, u₂, ?_⟩
  rw [h, smul_smul]
  norm_num

/-- If `‖x‖ < 1`, then `k x + u` is the sum of `k + 1` unitaries for every unitary `u`: by
induction, `(k + 1) x + u = u₁ + (k x + u₂)` with `x + u = u₁ + u₂`
(`CStarAlgebra.exists_unitary_add_eq_add_unitary`). -/
private lemma exists_unitary_sum_eq_nsmul_add {x : A} (hx : ‖x‖ < 1) (k : ℕ) (u : unitary A) :
    ∃ v : Fin (k + 1) → unitary A, (k : ℝ) • x + u = ∑ i, (v i : A) := by
  induction k generalizing u with
  | zero => exact ⟨fun _ => u, by simp⟩
  | succ k ih =>
    obtain ⟨u₁, u₂, h⟩ := exists_unitary_add_eq_add_unitary hx u
    obtain ⟨v, hv⟩ := ih u₂
    refine ⟨Fin.cons u₁ v, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hv, Nat.cast_succ, add_smul, one_smul, add_assoc, h]
    abel

/-- **Kadison–Pedersen**: in a unital C⋆-algebra, an element with `‖x‖ < 1 - 2 / n` is the mean
`(u₁ + ⋯ + uₙ) / n` of `n` unitaries (Kadison–Pedersen 1985, after Gardner 1984). Together with
`0 < n`, the norm bound forces `n ≥ 3`, since `1 - 2 / n ≤ 0` for `n ∈ {1, 2}`. For
`a = n x / (n - 2)`, `‖a‖ < 1`, and `(n - 2) a + 1` is the sum of `n - 1` unitaries (by
induction, `x + u` being the sum of two unitaries for `‖x‖ < 1` and `u` unitary); adding the
unitary `-1` gives `n x`. -/
private theorem exists_unitary_eq_mean_of_norm_lt {x : A} {n : ℕ} (hn : 0 < n) (hx : ‖x‖ < 1 - 2 / n) :
    ∃ u : Fin n → unitary A, x = (n : ℝ)⁻¹ • ∑ i, (u i : A) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := by
    refine ⟨n - 3, ?_⟩
    by_contra h
    obtain rfl | rfl : n = 1 ∨ n = 2 := by omega
    all_goals norm_num at hx; linarith [norm_nonneg x]
  have hk : (0 : ℝ) < k + 1 := by exact Nat.cast_add_one_pos k
  set a : A := ((k + 3 : ℝ) / (k + 1)) • x with ha_def
  have ha : ‖a‖ < 1 := by
    rw [ha_def, norm_smul, Real.norm_of_nonneg (by positivity)]
    push_cast at hx
    calc (k + 3 : ℝ) / (k + 1) * ‖x‖ < (k + 3) / (k + 1) * (1 - 2 / (k + 3)) := by gcongr
      _ = 1 := by field_simp; ring
  obtain ⟨v, hv⟩ := exists_unitary_sum_eq_nsmul_add ha (k + 1) 1
  have hxa : ((k + 1 : ℕ) : ℝ) • a = ((k + 3 : ℕ) : ℝ) • x := by
    rw [ha_def, smul_smul]
    congr 1
    push_cast
    field_simp
  refine ⟨Fin.cons (-1) v, ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [← hv, hxa, Unitary.coe_neg, OneMemClass.coe_one, neg_add_cancel_comm_assoc, smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]

/-- The open unit ball of a unital C⋆-algebra lies in the convex hull of the unitaries: an element
with `‖x‖ < 1` has `‖x‖ < 1 - 2 / n` for large `n`, and is then the mean of `n` unitaries
(`CStarAlgebra.exists_unitary_eq_mean_of_norm_lt`). -/
private lemma ball_subset_convexHull_unitary : ball (0 : A) 1 ⊆ convexHull ℝ (unitary A : Set A) := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  have h₁ : 0 < 1 - ‖x‖ := sub_pos.2 hx
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / (1 - ‖x‖))
  have hn₀ : (0 : ℝ) < n := (div_pos two_pos h₁).trans hn
  have hxn : ‖x‖ < 1 - 2 / n := by
    rw [div_lt_iff₀ h₁] at hn
    rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ hn₀]
    linarith
  obtain ⟨u, rfl⟩ := exists_unitary_eq_mean_of_norm_lt (Nat.cast_pos.1 hn₀) hxn
  rw [Finset.smul_sum]
  refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by positivity) ?_
    fun i _ => subset_convexHull ℝ _ (u i).2
  simp [hn₀.ne']

/-- The **Russo–Dye theorem** (Russo–Dye 1966): the closed convex hull of the unitaries of a
unital C⋆-algebra is its closed unit ball. Unitaries have norm at most `1`, and the closed ball is
closed and convex; conversely, an `x` with `‖x‖ ≤ 1` is the limit of `t x` as `t → 1⁻`, which lie
in the open unit ball and hence in the convex hull
(`CStarAlgebra.ball_subset_convexHull_unitary`). -/
theorem closedConvexHull_unitary : closedConvexHull ℝ (unitary A : Set A) = closedBall 0 1 := by
  rw [closedConvexHull_eq_closure_convexHull]
  refine subset_antisymm (closure_minimal (convexHull_min ?_ (convex_closedBall 0 1))
    isClosed_closedBall) ?_
  · intro u hu
    rw [mem_closedBall_zero_iff]
    nontriviality A
    rw [CStarRing.norm_of_mem_unitary hu]
  · intro x hx
    rw [mem_closedBall_zero_iff] at hx
    have ht : Filter.Tendsto (fun t : ℝ => t • x) (𝓝[<] 1) (𝓝 x) := by
      simpa using
        ((Filter.tendsto_id (x := 𝓝[<] (1 : ℝ))).mono_right nhdsWithin_le_nhds).smul_const x
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    apply ball_subset_convexHull_unitary
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht.1.le]
    calc t * ‖x‖ ≤ t * 1 := by gcongr; exact ht.1.le
      _ < 1 := by linarith [ht.2]

end

end D5.S3.Quantum.Analysis.RussoDye
