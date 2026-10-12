/- GID: D5/S3/Estimation/TimeArrow/RectangleHypergeometricMoments
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/RectangleHypergeometricMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite hypergeometric moments give a central conditional tail bound. -/

import D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
The falling-factorial convolution and finite moment calculations are adapted
from TauCetiProject/TauCeti, commit 8eecb48e9b51da99ca119f190a64ca43c100795b,
TauCeti/Data/Nat/Choose/Basic.lean (`descFactorial_mul_choose`,
`sum_range_descFactorial_mul_choose_mul_choose`) and
TauCeti/Probability/Distributions/Hypergeometric/Basic.lean
(`sum_hypergeometricWeight_toReal_mul`,
`sum_hypergeometricWeight_toReal_mul_pred`).
The finite real kernel replaces ENNReal-toReal and measure integration.
Copyright (c) 2026 The Tau Ceti contributors. Authors: The Tau Ceti contributors.
Retire these ports when this repository's pinned Mathlib provides equivalent
weighted Vandermonde and finite hypergeometric moment declarations.

Full upstream license:
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

open scoped BigOperators
open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments
noncomputable section

set_option quotPrecheck false in
local notation "H" => fun N K n k : ℕ => if k ≤ n then
  ((K.choose k : ℝ) * ((N - K).choose (n - k) : ℝ)) / (N.choose n : ℝ) else 0

private theorem desc_factorial_mul_choose {m i : ℕ} (hmi : m ≤ i) (A : ℕ) :
    i.descFactorial m * A.choose i = A.descFactorial m * (A - m).choose (i - m) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (i.choose m) (A.choose i), Nat.choose_mul hmi]

/-- **Vandermonde's convolution weighted by a falling factorial of the summation index.**

Weighting the `i`th summand of `∑ i, C(A, i) * C(B, r - i) = C(A + B, r)` by `(i)ₘ` multiplies
the value by `(A)ₘ` and lowers both indices by `m`. After division by `C(A + B, r)`, the cases
`m = 1` and `m = 2` give the first two factorial moments of a hypergeometric law. -/
private theorem factorial_vandermonde {m r : ℕ} (hmr : m ≤ r) (A B : ℕ) :
    ∑ i ∈ range (r + 1), i.descFactorial m * (A.choose i * B.choose (r - i)) =
      A.descFactorial m * (A + B - m).choose (r - m) := by
  have hsub : Ico m (r + 1) ⊆ range (r + 1) := fun i hi => mem_range.2 (mem_Ico.1 hi).2
  have hvanish : ∀ i ∈ range (r + 1), i ∉ Ico m (r + 1) →
      i.descFactorial m * (A.choose i * B.choose (r - i)) = 0 := by
    intro i hi hni
    simp only [mem_range] at hi
    simp only [mem_Ico, not_and, not_lt] at hni
    simp [Nat.descFactorial_eq_zero_iff_lt.2 (by omega : i < m)]
  have key : ∑ i ∈ range (r + 1), i.descFactorial m * (A.choose i * B.choose (r - i)) =
      A.descFactorial m * (A - m + B).choose (r - m) := by
    have hrange : r + 1 - m = r - m + 1 := by omega
    rw [← Finset.sum_subset hsub hvanish, Finset.sum_Ico_eq_sum_range,
      hrange, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j ↦ (A - m).choose i * B.choose j) (r - m), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hri : r - (m + i) = r - m - i := by omega
    rw [hri, ← Nat.mul_assoc, desc_factorial_mul_choose (Nat.le_add_right m i) A,
      Nat.add_sub_cancel_left, Nat.mul_assoc]
  rcases le_or_gt m A with hmA | hmA
  · have hsub_add : A + B - m = A - m + B := by omega
    rwa [hsub_add]
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 hmA] at key ⊢
    simpa using key

private theorem kernel_normalization {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N) :
    (∑ k ∈ range (n + 1), H N K n k) = 1 := by
  have hz : (N.choose n : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hn
  have hv : ∑ k ∈ range (n + 1), K.choose k * (N - K).choose (n - k) = N.choose n := by
    rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => K.choose i * (N - K).choose j) n,
      ← Nat.add_choose_eq, Nat.add_sub_of_le hK]
  calc
    _ = (∑ k ∈ range (n + 1), (K.choose k : ℝ) * ((N - K).choose (n - k) : ℝ)) /
        (N.choose n : ℝ) := by
      rw [sum_div]
      apply sum_congr rfl
      intro k hk
      simp only [if_pos (Nat.lt_succ_iff.mp (mem_range.mp hk))]
    _ = 1 := by
      have hh : (∑ k ∈ range (n + 1), (K.choose k : ℝ) * ((N - K).choose (n - k) : ℝ)) =
          (N.choose n : ℝ) := by exact_mod_cast hv
      rw [hh, div_self hz]

private theorem first_moment {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N) (hN : 0 < N) :
    (∑ k ∈ range (n + 1), H N K n k * (k : ℝ)) = (n : ℝ) * K / N := by
  by_cases hn0 : n = 0
  · subst n; simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hz : (N.choose n : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hn
  have hm : ∑ k ∈ range (n + 1), k * K.choose k * (N - K).choose (n - k) =
      K * (N - 1).choose (n - 1) := by
    have hh := factorial_vandermonde (m := 1) hnpos K (N - K)
    rw [Nat.add_sub_of_le hK] at hh
    simpa [Nat.descFactorial_one, Nat.mul_assoc] using hh
  calc
    _ = ((∑ k ∈ range (n + 1), k * K.choose k * (N - K).choose (n - k) : ℕ) : ℝ) /
        (N.choose n : ℝ) := by
      push_cast
      rw [sum_div]
      apply sum_congr rfl
      intro k hk
      simp only [if_pos (Nat.lt_succ_iff.mp (mem_range.mp hk))]
      ring
    _ = ((K * (N - 1).choose (n - 1) : ℕ) : ℝ) / (N.choose n : ℝ) := by rw [hm]
    _ = _ := by
      have hc : N * (N - 1).choose (n - 1) = N.choose n * n := by
        simpa [Nat.descFactorial_one, Nat.mul_comm] using
          (desc_factorial_mul_choose (m := 1) hnpos N).symm
      have hcR : (N : ℝ) * ((N - 1).choose (n - 1) : ℝ) = (N.choose n : ℝ) * n := by
        exact_mod_cast hc
      push_cast
      field_simp
      linear_combination (K : ℝ) * hcR

private theorem second_factorial_moment {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N)
    (hN : 1 < N) :
    (∑ k ∈ range (n + 1), H N K n k * (k : ℝ) * ((k : ℝ) - 1)) =
      (n : ℝ) * ((n : ℝ) - 1) * K * ((K : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  by_cases hn2 : 2 ≤ n
  · have hz : (N.choose n : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hn
    have hm : ∑ k ∈ range (n + 1), k * (k - 1) * K.choose k * (N - K).choose (n - k) =
        K * (K - 1) * (N - 2).choose (n - 2) := by
      have hh := factorial_vandermonde (m := 2) hn2 K (N - K)
      rw [Nat.add_sub_of_le hK] at hh
      simpa [Nat.descFactorial_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh
    calc
      _ = ((∑ k ∈ range (n + 1), k * (k - 1) * K.choose k * (N - K).choose (n - k) : ℕ) : ℝ) /
          (N.choose n : ℝ) := by
        push_cast
        rw [sum_div]
        apply sum_congr rfl
        intro k hk
        simp only [if_pos (Nat.lt_succ_iff.mp (mem_range.mp hk))]
        cases k with
        | zero => simp
        | succ k => simp only [Nat.cast_succ, Nat.succ_sub_one]; ring
      _ = ((K * (K - 1) * (N - 2).choose (n - 2) : ℕ) : ℝ) / (N.choose n : ℝ) := by rw [hm]
      _ = _ := by
        have hnat : (n - 1) * n * N.choose n = (N - 1) * N * (N - 2).choose (n - 2) := by
          simpa [Nat.descFactorial_succ, Nat.mul_assoc] using
            desc_factorial_mul_choose (m := 2) hn2 N
        have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; norm_num
        have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; norm_num
        have hcR : (N : ℝ) * ((N : ℝ) - 1) * ((N - 2).choose (n - 2) : ℝ) =
            (N.choose n : ℝ) * n * ((n : ℝ) - 1) := by
          rw [← hn1, ← hN1]
          have hnat' : N * (N - 1) * (N - 2).choose (n - 2) =
              N.choose n * n * (n - 1) := by nlinarith [hnat]
          exact_mod_cast hnat'
        have hKpred : (K : ℝ) * ((K - 1 : ℕ) : ℝ) = (K : ℝ) * ((K : ℝ) - 1) := by
          cases K <;> norm_num [Nat.cast_sub]
        have hNR : (1 : ℝ) < N := by exact_mod_cast hN
        have hNm1 : (N : ℝ) - 1 ≠ 0 := by linarith
        push_cast
        rw [hKpred]
        field_simp [hNm1]
        linear_combination (K : ℝ) * ((K : ℝ) - 1) * hcR
  · have hnle : n ≤ 1 := by omega
    interval_cases n <;> norm_num [Finset.sum_range_succ]

/-- Exact second central moment of the same finite rectangle kernel. -/
theorem kernel_second_central_moment {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N) (hN : 1 < N) :
    (∑ k ∈ range (n + 1), H N K n k * ((k : ℝ) - (n : ℝ) * K / N) ^ 2) =
      (n : ℝ) * ((K : ℝ) / N) * (1 - (K : ℝ) / N) * (((N : ℝ) - n) / ((N : ℝ) - 1)) := by
  let m : ℝ := (n : ℝ) * K / N
  have he : (∑ k ∈ range (n + 1), H N K n k * ((k : ℝ) - m) ^ 2) =
      (∑ k ∈ range (n + 1), H N K n k * (k : ℝ) * ((k : ℝ) - 1)) +
        (1 - 2 * m) * (∑ k ∈ range (n + 1), H N K n k * (k : ℝ)) +
          m ^ 2 * (∑ k ∈ range (n + 1), H N K n k) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [he, second_factorial_moment hK hn hN, first_moment hK hn (by omega),
    kernel_normalization hK hn]
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hNz : (N : ℝ) ≠ 0 := by linarith
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by linarith
  dsimp [m]
  field_simp
  ring

/-- The kernel's second central moment is at most the population size over
four, including empty samples. -/
private theorem kernel_variance_le {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N) (hN : 1 < N) :
    (∑ k ∈ range (n + 1), H N K n k * ((k : ℝ) - (n : ℝ) * K / N) ^ 2) ≤ (N : ℝ) / 4 := by
  rw [kernel_second_central_moment hK hn hN]
  by_cases hn0 : n = 0
  · simp [hn0]; positivity
  have hKR : (K : ℝ) ≤ N := by exact_mod_cast hK
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hratio0 : 0 ≤ (K : ℝ) / N := by positivity
  have hratio1 : (K : ℝ) / N ≤ 1 := (div_le_one (by linarith)).mpr hKR
  have hbern : ((K : ℝ) / N) * (1 - (K : ℝ) / N) ≤ 1 / 4 := by
    nlinarith [sq_nonneg ((K : ℝ) / N - 1 / 2)]
  have hpop : (n : ℝ) * (((N : ℝ) - n) / ((N : ℝ) - 1)) ≤ N := by
    rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0 : ℝ) < (N : ℝ) - 1)]
    have hp := mul_le_mul hnR (show (N : ℝ) - n ≤ N - 1 by linarith)
      (show 0 ≤ (N : ℝ) - n by linarith) (show 0 ≤ (N : ℝ) by positivity)
    nlinarith
  have hscale : 0 ≤ (n : ℝ) * (((N : ℝ) - n) / ((N : ℝ) - 1)) := by positivity
  calc
    _ = ((n : ℝ) * (((N : ℝ) - n) / ((N : ℝ) - 1))) *
        (((K : ℝ) / N) * (1 - (K : ℝ) / N)) := by ring
    _ ≤ ((n : ℝ) * (((N : ℝ) - n) / ((N : ℝ) - 1))) * (1 / 4) :=
      mul_le_mul_of_nonneg_left hbern hscale
    _ ≤ (N : ℝ) / 4 := by nlinarith

/-- A finite Chebyshev tail for the exact rectangle kernel; the variance
input is proved from the kernel's own first two factorial moments. -/
theorem kernel_central_tail {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N) (hN : 1 < N)
    (L : ℝ) (hL : 0 < L) :
    (∑ k ∈ (range (n + 1)).filter
      (fun k : ℕ => L * Real.sqrt N < |(k : ℝ) - (n : ℝ) * K / N|), H N K n k) ≤
        1 / (4 * L ^ 2) := by
  classical
  let T := (range (n + 1)).filter
    (fun k : ℕ => L * Real.sqrt N < |(k : ℝ) - (n : ℝ) * K / N|)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hw (k : ℕ) : 0 ≤ H N K n k := by
    dsimp only
    split_ifs <;> positivity
  have ht : L ^ 2 * (N : ℝ) * (∑ k ∈ T, H N K n k) ≤
      ∑ k ∈ T, H N K n k * ((k : ℝ) - (n : ℝ) * K / N) ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    have hb := (mem_filter.mp hk).2
    have hs : (L * Real.sqrt (N : ℝ)) ^ 2 ≤
        ((k : ℝ) - (n : ℝ) * K / N) ^ 2 := by
      nlinarith [sq_abs ((k : ℝ) - (n : ℝ) * K / N),
        mul_nonneg hL.le (Real.sqrt_nonneg (N : ℝ))]
    rw [mul_pow, Real.sq_sqrt hNpos.le] at hs
    nlinarith [mul_nonneg (hw k) (sub_nonneg.mpr hs)]
  have hsub : (∑ k ∈ T, H N K n k * ((k : ℝ) - (n : ℝ) * K / N) ^ 2) ≤
      ∑ k ∈ range (n + 1), H N K n k * ((k : ℝ) - (n : ℝ) * K / N) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => mul_nonneg (hw k) (sq_nonneg _))
  have hb := ht.trans (hsub.trans (kernel_variance_le hK hn hN))
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * L ^ 2)).mpr
  have hc : (0 : ℝ) < N := hNpos
  nlinarith

open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open private
  D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment.native_minimal_four_cell_law
from D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open private
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibration_counts_margins
from D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

/-- The exact original conditional mass is the numerical kernel for every
finite event of the A count. This connects the native law to scalar estimates
without replacing the native history or its conditioning environment. -/
theorem native_kernel_event_mass {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)]
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (k l : ℕ) (z : Fiber S e o) (P : ℕ → Prop) [DecidablePred P] :
    letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
    let V := nativeRectangleRows S e o k l z
    let R := (V.filter fun i => count e z.val i.val 1 = k).card
    let U := (V.filter fun i => count e z.val i.val (-1) = l).card
    let Env := univ.filter fun y : Fiber S e o =>
      nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
    conditionalFiberMass S r e o (Env.filter fun y => P (nativeRectangleACount S e o k l y)) /
      conditionalFiberMass S r e o Env =
        ∑ t ∈ (range (U + 1)).filter P, H V.card R U t := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let Env := univ.filter fun y : Fiber S e o =>
    nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
  let A := nativeRectangleACount S e o k l
  let T := (range (U + 1)).filter P
  have hs (y : Fiber S e o) (hy : y ∈ Env) : A y ≤ U := by
    have he := (native_minimal_readout_eq_iff S e o k l y z).mp (mem_filter.mp hy).2
    have hm := congrArg (fun v => v.2.2.2) he
    change ((nativeRectangleRows S e o k l y).filter
      fun i => count e y.val i.val (-1) = l).card = U at hm
    have hc := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibration_counts_margins
      S e o k l y
    dsimp only at hc
    dsimp only [A]
    omega
  have hE : Env.filter (fun y => P (A y)) = Env.filter (fun y => A y ∈ T) := by
    ext y
    simp only [mem_filter]
    constructor
    · rintro ⟨hy, hp⟩
      exact ⟨hy, mem_filter.mpr ⟨mem_range.mpr (by have hh := hs y hy; omega), hp⟩⟩
    · rintro ⟨hy, ht⟩
      exact ⟨hy, (mem_filter.mp ht).2⟩
  have hsum : conditionalFiberMass S r e o (Env.filter fun y => P (A y)) =
      ∑ t ∈ T, conditionalFiberMass S r e o (Env.filter fun y => A y = t) := by
    simp only [conditionalFiberMass]
    rw [← sum_div, hE]
    congr 1
    exact (sum_fiberwise_eq_sum_filter Env T A (fun y => probability r e S y.val)).symm
  rw [hsum, sum_div]
  apply sum_congr rfl
  intro t ht
  exact D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment.native_minimal_four_cell_law
    S r e o hq hqm hr hr1 ha ha1 k l z t

/-- The native pair/path central tail uses the exact conditional kernel and
its proved variance; no tail assumption or independent surrogate law is used. -/
private theorem native_minimal_central_tail {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)]
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (k l : ℕ) (z : Fiber S e o) (L : ℝ) (hL : 0 < L)
    (hN : 1 < (nativeRectangleRows S e o k l z).card) :
    letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
    let V := nativeRectangleRows S e o k l z
    let R := (V.filter fun i => count e z.val i.val 1 = k).card
    let U := (V.filter fun i => count e z.val i.val (-1) = l).card
    let Env := univ.filter fun y : Fiber S e o =>
      nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
    conditionalFiberMass S r e o (Env.filter fun y => L * Real.sqrt V.card <
      |(nativeRectangleACount S e o k l y : ℝ) - (U : ℝ) * R / V.card|) /
        conditionalFiberMass S r e o Env ≤ 1 / (4 * L ^ 2) ∧
      nativeMinimalRectangleSigma S e o k l = nativeMarginRectangleSigma S e o k l := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  constructor
  · have he := native_kernel_event_mass S r e o hq hqm hr hr1 ha ha1 k l z
      (fun t : ℕ => L * Real.sqrt (nativeRectangleRows S e o k l z).card <
        |(t : ℝ) -
          (((nativeRectangleRows S e o k l z).filter fun i => count e z.val i.val (-1) = l).card : ℝ) *
          ((nativeRectangleRows S e o k l z).filter fun i => count e z.val i.val 1 = k).card /
          (nativeRectangleRows S e o k l z).card|)
    dsimp only at he
    exact he.trans_le (kernel_central_tail (card_filter_le _ _) (card_filter_le _ _) hN L hL)
  · exact native_rectangle_sigma_eq S e o k l


open private
  D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.conditionalFiberMass_eq_card
from D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber

/-- Domination of any native event by a count event retains the exact
native conditioning mass. -/
theorem native_event_mass_le_kernel {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)]
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (k l : ℕ) (z : Fiber S e o) (Q : Fiber S e o → Prop) [DecidablePred Q]
    (P : ℕ → Prop) [DecidablePred P]
    (hpush : ∀ y, nativeMinimalRectangleReadout S e o k l y =
      nativeMinimalRectangleReadout S e o k l z → Q y → P (nativeRectangleACount S e o k l y)) :
    letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
    let V := nativeRectangleRows S e o k l z
    let R := (V.filter fun i => count e z.val i.val 1 = k).card
    let U := (V.filter fun i => count e z.val i.val (-1) = l).card
    let Env := univ.filter fun y : Fiber S e o =>
      nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
    conditionalFiberMass S r e o (Env.filter Q) / conditionalFiberMass S r e o Env ≤
      ∑ t ∈ (range (U + 1)).filter P, H V.card R U t := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  let Env := univ.filter fun y : Fiber S e o =>
    nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
  have hp := ((finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e).2.2.1 S o).1
  have hsub : Env.filter Q ⊆ Env.filter (fun y => P (nativeRectangleACount S e o k l y)) := by
    intro y hy
    have hh := mem_filter.mp hy
    exact mem_filter.mpr ⟨hh.1, hpush y (mem_filter.mp hh.1).2 hh.2⟩
  have hm : conditionalFiberMass S r e o (Env.filter Q) ≤
      conditionalFiberMass S r e o (Env.filter fun y => P (nativeRectangleACount S e o k l y)) := by
    rw [D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.conditionalFiberMass_eq_card S r e o hp,
      D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.conditionalFiberMass_eq_card S r e o hp]
    exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsub) (by positivity)
  have hden : 0 ≤ conditionalFiberMass S r e o Env := by
    rw [D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.conditionalFiberMass_eq_card S r e o hp]
    positivity
  exact (div_le_div_of_nonneg_right hm hden).trans_eq
    (native_kernel_event_mass S r e o hq hqm hr hr1 ha ha1 k l z P)

/-- Balanced margins make all four mean cells large; a single central
A-count deviation controls all four cells at once. -/
private theorem central_four_cells_lower (N R U δ t w : ℝ) (hN : 0 < N) (hδ : 0 ≤ δ)
    (hR : δ * N ≤ R) (hR' : R ≤ (1 - δ) * N)
    (hU : δ * N ≤ U) (hU' : U ≤ (1 - δ) * N)
    (ht : |t - U * R / N| ≤ w) :
    ∀ j, δ ^ 2 * N - w ≤ cellCounts N R U t j := by
  have hδN : 0 ≤ δ * N := mul_nonneg hδ hN.le
  have hR0 : 0 ≤ R := hδN.trans hR
  have hU0 : 0 ≤ U := hδN.trans hU
  have hRc : δ * N ≤ N - R := by nlinarith
  have hUc : δ * N ≤ N - U := by nlinarith
  have hRc0 : 0 ≤ N - R := hδN.trans hRc
  have hUc0 : 0 ≤ N - U := hδN.trans hUc
  have hprod (a b : ℝ) (ha : δ * N ≤ a) (hb : δ * N ≤ b) :
      δ ^ 2 * N ≤ a * b / N := by
    apply (le_div_iff₀ hN).mpr
    have hh := mul_le_mul ha hb hδN (hδN.trans ha)
    nlinarith
  have h0 := hprod U R hU hR
  have h1 := hprod U (N - R) hU hRc
  have h2 := hprod (N - U) R hUc hR
  have h3 := hprod (N - U) (N - R) hUc hRc
  have he1 : U * (N - R) / N = U - U * R / N := by field_simp <;> ring
  have he2 : (N - U) * R / N = R - U * R / N := by field_simp <;> ring
  have he3 : (N - U) * (N - R) / N = N - R - U + U * R / N := by field_simp <;> ring
  rw [he1] at h1
  rw [he2] at h2
  rw [he3] at h3
  intro j
  fin_cases j <;> simp [cellCounts] <;> nlinarith [abs_le.mp ht]

/-- The actual native signal-cell counts agree with the same fixed-margin
real interpolation on a minimal environment. -/
private theorem native_cells_on_minimal_environment {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)] (k l : ℕ) (y z : Fiber S e o)
    (henv : nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z) :
    let V := nativeRectangleRows S e o k l z
    let R := (V.filter fun i => count e z.val i.val 1 = k).card
    let U := (V.filter fun i => count e z.val i.val (-1) = l).card
    ∀ j, ((nativeCalibrationCells S e y.val k l j).card : ℝ) =
      cellCounts V.card R U (nativeRectangleACount S e o k l y) j := by
  classical
  dsimp only
  have he := (native_minimal_readout_eq_iff S e o k l y z).mp henv
  have hV := congrArg (fun v => v.1.card) he
  have hR := congrArg (fun v => v.2.2.1) he
  have hU := congrArg (fun v => v.2.2.2) he
  have hc := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibration_counts_margins S e o k l y
  dsimp only at hc
  change (nativeRectangleRows S e o k l y).card = (nativeRectangleRows S e o k l z).card at hV
  change ((nativeRectangleRows S e o k l y).filter fun i => count e y.val i.val 1 = k).card =
    ((nativeRectangleRows S e o k l z).filter fun i => count e z.val i.val 1 = k).card at hR
  change ((nativeRectangleRows S e o k l y).filter fun i => count e y.val i.val (-1) = l).card =
    ((nativeRectangleRows S e o k l z).filter fun i => count e z.val i.val (-1) = l).card at hU
  rw [hV, hR, hU] at hc
  have hNR := congrArg (fun n : ℕ => (n : ℝ)) hc.1
  have hRR := congrArg (fun n : ℕ => (n : ℝ)) hc.2.1
  have hUR := congrArg (fun n : ℕ => (n : ℝ)) hc.2.2.1
  have hAR := congrArg (fun n : ℕ => (n : ℝ)) hc.2.2.2
  push_cast at hNR hRR hUR
  intro j
  fin_cases j <;> simp [cellCounts] <;> linarith

/-- Conditional simultaneous occupancy of all four original signal cells
follows from the exact native law and its own variance. -/
private theorem native_four_cell_occupancy_tail {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)]
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (k l : ℕ) (z : Fiber S e o) (δ L : ℝ) (hδ : 0 ≤ δ) (hL : 0 < L)
    (hN : 1 < (nativeRectangleRows S e o k l z).card) :
    letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
    let V := nativeRectangleRows S e o k l z
    let R : ℝ := (V.filter fun i => count e z.val i.val 1 = k).card
    let U : ℝ := (V.filter fun i => count e z.val i.val (-1) = l).card
    let Env := univ.filter fun y : Fiber S e o =>
      nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
    δ * V.card ≤ R → R ≤ (1 - δ) * V.card →
    δ * V.card ≤ U → U ≤ (1 - δ) * V.card →
    L * Real.sqrt V.card ≤ δ ^ 2 * V.card / 2 →
    conditionalFiberMass S r e o
      (Env.filter fun y => ∃ j, ((nativeCalibrationCells S e y.val k l j).card : ℝ) <
        δ ^ 2 * V.card / 2) / conditionalFiberMass S r e o Env ≤ 1 / (4 * L ^ 2) := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  intro hR hR' hU hU' hwidth
  let N := (nativeRectangleRows S e o k l z).card
  let R := ((nativeRectangleRows S e o k l z).filter fun i => count e z.val i.val 1 = k).card
  let U := ((nativeRectangleRows S e o k l z).filter fun i => count e z.val i.val (-1) = l).card
  apply (native_event_mass_le_kernel S r e o hq hqm hr hr1 ha ha1 k l z
    (fun y => ∃ j, ((nativeCalibrationCells S e y.val k l j).card : ℝ) < δ ^ 2 * N / 2)
    (fun t : ℕ => L * Real.sqrt N < |(t : ℝ) - (U : ℝ) * R / N|) ?_).trans
  · exact kernel_central_tail (card_filter_le _ _) (card_filter_le _ _) hN L hL
  · intro y hy hbad
    obtain ⟨j, hj⟩ := hbad
    by_contra hh
    have ht : |(nativeRectangleACount S e o k l y : ℝ) - (U : ℝ) * R / N| ≤ L * Real.sqrt N :=
      le_of_not_gt hh
    have hb := central_four_cells_lower N R U δ (nativeRectangleACount S e o k l y)
      (L * Real.sqrt N) (by exact_mod_cast (by omega : 0 < N)) hδ hR hR' hU hU' ht j
    rw [← native_cells_on_minimal_environment S e o k l y z hy j] at hb
    linarith

end
end D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments
