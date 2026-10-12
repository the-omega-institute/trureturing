/- GID: D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Forward differences, derivative bounds, and noninteger power signals. -/

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

noncomputable section

open Set Finset Filter
open scoped Topology
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal

/-- Differentiation commutes with a finite forward difference whenever all its nodes
have the specified derivative. -/
theorem has_deriv_at_fwd_diff_iter (t : ℝ) (n : ℕ) (f f' : ℝ → ℝ) (x : ℝ)
    (hf : ∀ i : ℕ, i ≤ n → HasDerivAt f (f' (x + i * t)) (x + i * t)) :
    HasDerivAt ((fwdDiff t)^[n] f) ((fwdDiff t)^[n] f' x) x := by
  let : NormedSpace ℝ ℝ := NormedAlgebra.toNormedSpace ℝ
  induction n generalizing x with
  | zero => simpa using hf 0 (by omega)
  | succ n ih =>
    have h0 := ih x (fun i hi => hf i (by omega))
    have h1 := ih (x + t) (fun i hi => by
      have he : x + t + i * t = x + (i + 1 : ℕ) * t := by push_cast; ring
      simpa only [he] using hf (i + 1) (by omega))
    convert (h1.comp_add_const x t).fun_sub h0 using 1 <;> first
      | rfl
      | (simp only [Function.iterate_succ_apply', fwdDiff] <;> rfl)

/-- A higher-order mean value formula with every evaluation point in the original
closed forward-difference interval. -/
theorem exists_fwd_diff_iter_eq_iterated_deriv (f : ℝ → ℝ) (R : ℕ) {x t : ℝ}
    (ht : 0 < t)
    (hf : ∀ k : ℕ, k < R → ∀ y ∈ Icc x (x + R * t),
      DifferentiableAt ℝ (iteratedDeriv k f) y) :
    ∃ y ∈ Icc x (x + R * t),
      (fwdDiff t)^[R] f x = t ^ R * iteratedDeriv R f y := by
  induction R generalizing f x with
  | zero => exact ⟨x, by simp, by simp⟩
  | succ R ih =>
    have hd (y : ℝ) (hy : y ∈ Icc x (x + t)) :
        HasDerivAt ((fwdDiff t)^[R] f) ((fwdDiff t)^[R] (deriv f) y) y := by
      apply has_deriv_at_fwd_diff_iter
      intro i hi
      apply (hf 0 (by omega) (y + i * t) ?_).hasDerivAt
      constructor
      · nlinarith [hy.1, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      · have hle : (i : ℝ) ≤ R := by exact_mod_cast hi
        push_cast
        nlinarith [hy.2]
    obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope
      ((fwdDiff t)^[R] f) ((fwdDiff t)^[R] (deriv f)) (show x < x + t by linarith)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => hd y ⟨hy.1.le, hy.2.le⟩)
    obtain ⟨y, hy, hdiff⟩ := ih (deriv f) (x := c) (fun k hk z hz => by
      rw [← iteratedDeriv_succ']
      apply hf (k + 1) (by omega) z
      constructor
      · linarith [hz.1, hc.1]
      · have hr : (0 : ℝ) ≤ R := Nat.cast_nonneg R
        push_cast
        nlinarith [hz.2, hc.2])
    refine ⟨y, ⟨by linarith [hy.1, hc.1], ?_⟩, ?_⟩
    · push_cast
      nlinarith [hy.2, hc.2]
    · rw [Function.iterate_succ_apply', fwdDiff]
      rw [show x + t - x = t by ring] at he
      have he' := (eq_div_iff ht.ne').mp he
      rw [hdiff, ← iteratedDeriv_succ'] at he'
      rw [pow_succ]
      nlinarith [he']

/-- A uniform derivative budget bounds the forward difference, with the sharp
step-size power and the same closed interval. -/
theorem abs_fwd_diff_iter_le (f : ℝ → ℝ) (R : ℕ) {x t D : ℝ}
    (ht : 0 < t)
    (hf : ∀ k : ℕ, k < R → ∀ y ∈ Icc x (x + R * t),
      DifferentiableAt ℝ (iteratedDeriv k f) y)
    (hD : ∀ y ∈ Icc x (x + R * t), |iteratedDeriv R f y| ≤ D) :
    |(fwdDiff t)^[R] f x| ≤ t ^ R * D := by
  obtain ⟨y, hy, he⟩ := exists_fwd_diff_iter_eq_iterated_deriv f R ht hf
  rw [he, abs_mul, abs_of_pos (pow_pos ht R)]
  exact mul_le_mul_of_nonneg_left (hD y hy) (pow_nonneg ht.le R)

/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Authors: Codex
Source: roos-j/lean-spherical,
LeanSpherical/Auto/Spherical/BRSRadial/PlanarResolution.lean,
revision 2b0e2bbf35cdf45ab99d1d77b2dea37b214fe236.
The port is superseded when the repository's pinned Mathlib supplies an equivalent
positive-half-line iterated real-power derivative declaration.
Released under the Apache License, Version 2.0, included below.
-/

/-- On the positive half-line the iterated derivatives of `t ^ p` are the
expected ones. -/
theorem iterated_deriv_rpow_pos (p : ℝ) (n : ℕ) :
    Set.EqOn (iteratedDeriv n fun t : ℝ => t ^ p)
      (fun t : ℝ => (∏ i ∈ Finset.range n, (p - i)) * t ^ (p - n))
      (Ioi (0 : ℝ)) := by
  induction n with
  | zero =>
      intro x hx
      simp
  | succ n ih =>
      intro x hx
      have hxpos : (0 : ℝ) < x := hx
      have hev : (iteratedDeriv n fun t : ℝ => t ^ p) =ᶠ[𝓝 x]
          fun t : ℝ => (∏ i ∈ Finset.range n, (p - i)) * t ^ (p - n) :=
        Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hx) ih
      have hd : HasDerivAt
          (fun t : ℝ => (∏ i ∈ Finset.range n, (p - i)) * t ^ (p - n))
          ((∏ i ∈ Finset.range n, (p - i)) *
            ((p - n) * x ^ (p - n - 1))) x :=
        (Real.hasDerivAt_rpow_const (p := (p - n : ℝ))
          (Or.inl (ne_of_gt hxpos))).const_mul _
      rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv]
      change (∏ i ∈ Finset.range n, (p - i)) * ((p - n) * x ^ (p - n - 1)) =
        (∏ i ∈ Finset.range (n + 1), (p - i)) * x ^ (p - (n + 1 : ℕ))
      rw [Finset.prod_range_succ]
      have hexp : p - ((n : ℝ) + 1) = p - n - 1 := by ring
      push_cast
      rw [hexp]
      ring

/-- A nonintegral real power has a nonzero forward difference on every strictly
positive interval, in every finite order. -/
theorem rpow_fwd_diff_iter_ne_zero (β : ℝ) (R : ℕ) {x t : ℝ}
    (hx : 0 < x) (ht : 0 < t) (hβ : ∀ j : ℕ, β ≠ j) :
    (fwdDiff t)^[R] (fun u : ℝ => u ^ β) x ≠ 0 := by
  have hs (k : ℕ) (y : ℝ) (hy : 0 < y) :
      DifferentiableAt ℝ (iteratedDeriv k (fun u : ℝ => u ^ β)) y := by
    have he : iteratedDeriv k (fun u : ℝ => u ^ β) =ᶠ[𝓝 y]
        (fun u : ℝ => (∏ j ∈ range k, (β - j)) * u ^ (β - k)) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy) (iterated_deriv_rpow_pos β k)
    exact ((Real.hasDerivAt_rpow_const (p := β - k) (Or.inl hy.ne')).const_mul
      (∏ j ∈ range k, (β - j))).congr_of_eventuallyEq he |>.differentiableAt
  obtain ⟨y, hy, he⟩ := exists_fwd_diff_iter_eq_iterated_deriv
    (fun u : ℝ => u ^ β) R ht (fun k _ y hy => hs k y (lt_of_lt_of_le hx hy.1))
  rw [he, iterated_deriv_rpow_pos β R (lt_of_lt_of_le hx hy.1)]
  exact mul_ne_zero (pow_ne_zero _ ht.ne')
    (mul_ne_zero (prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr (hβ j)))
      (Real.rpow_pos_of_pos (lt_of_lt_of_le hx hy.1) _).ne')

/-- The fixed unit-step signal is strictly positive after taking absolute value. -/
theorem unit_signal_pos (β : ℝ) (R : ℕ) (hβ : ∀ j : ℕ, β ≠ j) :
    0 < |(fwdDiff (1 : ℝ))^[R] (fun u : ℝ => u ^ β) 1| :=
  abs_pos.mpr (rpow_fwd_diff_iter_ne_zero β R (by norm_num) (by norm_num) hβ)

/-- Positive dilations preserve the unit-step power signal exactly. -/
theorem rpow_fwd_diff_iter_scale (β : ℝ) (R : ℕ) {t : ℝ} (ht : 0 < t) :
    (fwdDiff t)^[R] (fun u : ℝ => u ^ β) t =
      t ^ β * (fwdDiff (1 : ℝ))^[R] (fun u : ℝ => u ^ β) 1 := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, mul_sum]
  apply sum_congr rfl
  intro i hi
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one]
  rw [show t + (i : ℝ) * t = t * (1 + i) by ring,
    Real.mul_rpow ht.le (by positivity)]
  ring

/-- Every affine contribution vanishes in difference order at least two. -/
theorem affine_fwd_diff_iter_eq_zero (a b t : ℝ) (R : ℕ) (hR : 2 ≤ R) :
    (fwdDiff t)^[R] (fun u : ℝ => a + b * u) = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hR
  have hz : (fwdDiff t)^[2] (fun u : ℝ => a + b * u) = 0 := by
    ext u
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff,
      Pi.zero_apply]
    ring
  rw [hk, add_comm 2 k, Function.iterate_add_apply, hz]
  exact Function.iterate_fixed (by ext u; simp [fwdDiff]) k

/-- An affine target minus a real power has the exact homogeneous difference. -/
theorem affine_power_fwd_diff_iter (a b c β : ℝ) (R : ℕ) (hR : 2 ≤ R)
    {t : ℝ} (ht : 0 < t) :
    (fwdDiff t)^[R] (fun u : ℝ => a + b * u - c * u ^ β) t =
      -c * t ^ β * (fwdDiff (1 : ℝ))^[R] (fun u : ℝ => u ^ β) 1 := by
  have hf : (fun u : ℝ => a + b * u - c * u ^ β) =
      (fun u : ℝ => a + b * u) + (-c) • (fun u : ℝ => u ^ β) := by
    ext u
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hf, fwdDiff_iter_add, affine_fwd_diff_iter_eq_zero a b t R hR,
    fwdDiff_iter_const_smul]
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul]
  rw [rpow_fwd_diff_iter_scale β R ht]
  ring

/-- The signal constant is positive and supplies the exact square-root scale law.
The bound holds for every positive real horizon, hence for every positive integer
horizon used in a dyadic budget. -/
theorem target_signal_scaled (B C β ρ : ℝ) (R : ℕ) (hR : 2 ≤ R)
    (hρ : 0 < ρ) (hβ : ∀ j : ℕ, β ≠ j) :
    0 < ρ ^ β * |(fwdDiff (1 : ℝ))^[R] (fun u : ℝ => u ^ β) 1| / 16 ∧
    ∀ n : ℝ, 0 < n →
      |(fwdDiff (ρ / Real.sqrt n))^[R]
        (fun u : ℝ => (1 - u / C) / (2 * B) - u ^ β / 16) (ρ / Real.sqrt n)| =
      (ρ ^ β * |(fwdDiff (1 : ℝ))^[R] (fun u : ℝ => u ^ β) 1| / 16) *
        n ^ (-(β / 2)) := by
  constructor
  · exact div_pos (mul_pos (Real.rpow_pos_of_pos hρ _) (unit_signal_pos β R hβ))
      (by norm_num)
  · intro n hn
    have ht : 0 < ρ / Real.sqrt n := div_pos hρ (Real.sqrt_pos.mpr hn)
    have hf : (fun u : ℝ => (1 - u / C) / (2 * B) - u ^ β / 16) =
        (fun u : ℝ => 1 / (2 * B) + (-(1 / C / (2 * B))) * u - (1 / 16) * u ^ β) := by
      ext u
      ring
    rw [hf, affine_power_fwd_diff_iter _ _ _ β R hR ht, abs_mul, abs_mul,
      abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16),
      abs_of_pos (Real.rpow_pos_of_pos ht _)]
    rw [Real.div_rpow hρ.le (Real.sqrt_nonneg n), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hn.le]
    simp only [div_eq_mul_inv]
    rw [← Real.rpow_neg hn.le]
    rw [show -(1 * (2 : ℝ)⁻¹ * β) = -(β * 2⁻¹) by ring]
    ring



end D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal

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
