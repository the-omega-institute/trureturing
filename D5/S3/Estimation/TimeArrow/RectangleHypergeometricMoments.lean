/- GID: D5/S3/Estimation/TimeArrow/RectangleHypergeometricMoments
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/RectangleHypergeometricMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite hypergeometric moments give a central conditional tail bound. -/

import D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
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
      rw [if_pos (by omega : k ≤ n)]
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
      rw [if_pos (by omega : k ≤ n)]
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
        rw [if_pos (by omega : k ≤ n)]
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
          exact_mod_cast hnat.symm
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

end
end D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments
