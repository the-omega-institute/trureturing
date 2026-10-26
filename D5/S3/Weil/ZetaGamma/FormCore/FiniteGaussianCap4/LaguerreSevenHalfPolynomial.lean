/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfPolynomial
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:fixed-alpha-laguerre-helper)
   anchors: []
   utility: none
   digest: Real Laguerre polynomials at alpha seven halves and their exact differential identities. -/
/-
Generalized real Laguerre polynomials, adapted 2026-10-26.
SPDX-License-Identifier: Apache-2.0

Modified/adapted proof method from the OAI project, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/MathematicalPhysics/DefocusingNLS/Certificates/LaguerrePolynomial.lean.
That source treats alpha=0 over C. This file changes the coefficients, scalar
field, ODE, and recurrences to alpha=7/2. The full upstream license follows.
-/

/- Full upstream Apache-2.0 license (unmodified text).
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

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped BigOperators

namespace FiniteGaussianCap4.LaguerreSevenHalf

/-- `(9/2)_n`; Gamma(9/2) has been divided out of the moments. -/
def momentWeight (n : ℕ) : ℝ := (ascPochhammer ℝ n).eval (9 / 2)

@[simp] theorem momentWeight_zero : momentWeight 0 = 1 := by
  simp [momentWeight]

theorem momentWeight_succ (n : ℕ) :
    momentWeight (n + 1) = momentWeight n * ((9 / 2 : ℝ) + n) := by
  exact ascPochhammer_succ_eval n (9 / 2 : ℝ)

theorem momentWeight_pos (n : ℕ) : 0 < momentWeight n := by
  exact ascPochhammer_pos n (9 / 2 : ℝ) (by norm_num)

theorem momentWeight_ne_zero (n : ℕ) : momentWeight n ≠ 0 :=
  (momentWeight_pos n).ne'

private theorem factorial_real_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  positivity

/-- Exact generalized Laguerre convention:
`[X^j] L_n^(7/2) = (-1)^j choose(n,j) (9/2)_n / ((9/2)_j n!)`.
The coefficient is zero beyond n. The theorem `coefficient_add` gives the
usual trailing-Pochhammer divided by `j! (n-j)!` form. -/
def coefficient (n j : ℕ) : ℝ :=
  (-1) ^ j * (n.choose j : ℝ) * momentWeight n /
    (momentWeight j * (n.factorial : ℝ))

def laguerre (n : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n + 1), monomial j (coefficient n j)

theorem coefficient_eq_zero (n j : ℕ) (h : n < j) : coefficient n j = 0 := by
  simp [coefficient, Nat.choose_eq_zero_of_lt h]

@[simp] theorem coeff_laguerre (n j : ℕ) :
    (laguerre n).coeff j = coefficient n j := by
  by_cases h : j < n + 1
  · simp [laguerre, Polynomial.coeff_monomial, Finset.mem_range, h]
  · have hnj : n < j := by omega
    simp [laguerre, Polynomial.coeff_monomial, Finset.mem_range, h,
      coefficient_eq_zero n j hnj]

@[simp] theorem coefficient_zero (n : ℕ) :
    coefficient n 0 = momentWeight n / (n.factorial : ℝ) := by
  simp [coefficient]

@[simp] theorem coefficient_self (n : ℕ) :
    coefficient n n = (-1 : ℝ) ^ n / (n.factorial : ℝ) := by
  simp only [coefficient, Nat.choose_self, Nat.cast_one, mul_one]
  field_simp [momentWeight_ne_zero n, factorial_real_ne_zero n]
  <;> ring

@[simp] theorem laguerre_eval_zero (n : ℕ) :
    (laguerre n).eval 0 = momentWeight n / (n.factorial : ℝ) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_laguerre, coefficient_zero]

@[simp] theorem laguerre_zero : laguerre 0 = 1 := by
  ext j
  cases j with
  | zero => simp
  | succ j =>
      simp [Polynomial.coeff_one, coefficient_eq_zero 0 (j + 1) (by omega)]

/-- Explicit finite polynomial expansion, with no basis assumption. -/
theorem laguerre_eval (n : ℕ) (x : ℝ) :
    (laguerre n).eval x =
      ∑ j ∈ Finset.range (n + 1), coefficient n j * x ^ j := by
  simp [laguerre, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Compatibility with the standard coefficient
`(-1)^j (9/2+j)_r / (j! r!)` at degree n=j+r. -/
theorem coefficient_add (j r : ℕ) :
    coefficient (j + r) j =
      (-1 : ℝ) ^ j * (ascPochhammer ℝ r).eval ((9 / 2 : ℝ) + j) /
        ((j.factorial : ℝ) * (r.factorial : ℝ)) := by
  have hw : momentWeight (j + r) =
      momentWeight j * (ascPochhammer ℝ r).eval ((9 / 2 : ℝ) + j) := by
    have h := congrArg (fun p : ℝ[X] => p.eval (9 / 2))
      (ascPochhammer_mul ℝ j r)
    simpa [momentWeight, Polynomial.eval_comp] using h.symm
  have hc : ((j + r).choose j : ℝ) * (j.factorial : ℝ) *
      (r.factorial : ℝ) = ((j + r).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j r)
    simpa only [Nat.add_sub_cancel_left, Nat.cast_mul] using
      congrArg (fun a : ℕ => (a : ℝ)) h
  have hc' : ((j + r).choose j : ℝ) =
      ((j + r).factorial : ℝ) / ((j.factorial : ℝ) * (r.factorial : ℝ)) := by
    apply (eq_div_iff (mul_ne_zero (factorial_real_ne_zero j)
      (factorial_real_ne_zero r))).2
    simpa only [mul_assoc] using hc
  rw [coefficient, hw, hc']
  field_simp [momentWeight_ne_zero j, factorial_real_ne_zero j,
    factorial_real_ne_zero r, factorial_real_ne_zero (j + r)]
  <;> ring

/-- The recurrence which is exactly the coefficient form of the alpha=7/2 ODE. -/
theorem coefficient_recurrence (n j : ℕ) :
    ((j : ℝ) + 1) * ((j : ℝ) + 9 / 2) * coefficient n (j + 1) +
      ((n : ℝ) - j) * coefficient n j = 0 := by
  by_cases hjn : j ≤ n
  · have hc : (n.choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
        (n.choose j : ℝ) * ((n : ℝ) - j) := by
      have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq n j)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hjn] using h
    have hj : (9 / 2 : ℝ) + j ≠ 0 := by positivity
    calc
      _ = ((-1 : ℝ) ^ j * momentWeight n /
          (momentWeight j * (n.factorial : ℝ))) *
          (-(n.choose (j + 1) : ℝ) * ((j : ℝ) + 1) +
            (n.choose j : ℝ) * ((n : ℝ) - j)) := by
        simp only [coefficient, momentWeight_succ, pow_succ]
        field_simp [momentWeight_ne_zero j, factorial_real_ne_zero n, hj]
        <;> ring
      _ = 0 := by rw [neg_mul, hc]; ring
  · have hnj : n < j := by omega
    rw [coefficient_eq_zero n j hnj,
      coefficient_eq_zero n (j + 1) (by omega)]
    ring

/-- `X L'' +(9/2-X)L' + n L = 0`, as an actual polynomial identity. -/
theorem differential_equation (n : ℕ) :
    X * (laguerre n).derivative.derivative +
      (C (9 / 2 : ℝ) - X) * (laguerre n).derivative +
      C (n : ℝ) * laguerre n = 0 := by
  ext j
  cases j with
  | zero =>
      simpa [Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_derivative, sub_mul, Polynomial.coeff_C_mul] using
        coefficient_recurrence n 0
  | succ j =>
      simp only [Polynomial.coeff_add, sub_mul, Polynomial.coeff_sub,
        Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
        Polynomial.coeff_C_mul, coeff_laguerre, Polynomial.coeff_zero]
      have h := coefficient_recurrence n (j + 1)
      push_cast at h ⊢
      linear_combination h

/-- A finite coefficient identity, valid even when j exceeds n. -/
theorem coefficient_derivative_step (n j : ℕ) :
    ((j : ℝ) + 1) * (coefficient (n + 1) (j + 1) -
      coefficient n (j + 1)) = -coefficient n j := by
  have hpas : ((n + 1).choose (j + 1) : ℝ) =
      (n.choose j : ℝ) + (n.choose (j + 1) : ℝ) := by
    exact_mod_cast Nat.choose_succ_succ' n j
  have hmul : ((n : ℝ) + 1) * (n.choose j : ℝ) =
      ((n + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n j
  rw [hpas] at hmul
  have hc : -((j : ℝ) + 1) * ((n : ℝ) + 9 / 2) *
        ((n + 1).choose (j + 1) : ℝ) +
      ((j : ℝ) + 1) * ((n : ℝ) + 1) * (n.choose (j + 1) : ℝ) +
      ((9 / 2 : ℝ) + j) * ((n : ℝ) + 1) * (n.choose j : ℝ) = 0 := by
    rw [hpas]
    linear_combination ((9 / 2 : ℝ) - 1) * hmul
  have hj : (9 / 2 : ℝ) + j ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hz : ((j : ℝ) + 1) * (coefficient (n + 1) (j + 1) -
      coefficient n (j + 1)) + coefficient n j = 0 := by
    calc
      _ = ((-1 : ℝ) ^ j * momentWeight n /
          (momentWeight j * (n.factorial : ℝ) *
            ((n : ℝ) + 1) * ((9 / 2 : ℝ) + j))) *
          (-((j : ℝ) + 1) * ((n : ℝ) + 9 / 2) *
              ((n + 1).choose (j + 1) : ℝ) +
            ((j : ℝ) + 1) * ((n : ℝ) + 1) * (n.choose (j + 1) : ℝ) +
            ((9 / 2 : ℝ) + j) * ((n : ℝ) + 1) * (n.choose j : ℝ)) := by
        simp only [coefficient, momentWeight_succ, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        field_simp [momentWeight_ne_zero j, factorial_real_ne_zero n, hj, hn]
        <;> ring
      _ = 0 := by rw [hc, mul_zero]
  linear_combination hz

/-- The parameter-preserving first derivative step. -/
theorem derivative_step (n : ℕ) :
    (laguerre (n + 1)).derivative = (laguerre n).derivative - laguerre n := by
  ext j
  simp only [Polynomial.coeff_sub, Polynomial.coeff_derivative, coeff_laguerre]
  have h := coefficient_derivative_step n j
  linear_combination h

/-- Lowering identity in coefficient form. -/
theorem coefficient_lowering (n j : ℕ) :
    (j : ℝ) * coefficient (n + 1) j =
      ((n : ℝ) + 1) * coefficient (n + 1) j -
        ((n : ℝ) + 9 / 2) * coefficient n j := by
  by_cases hj : j ≤ n + 1
  · have hc0 : (n.choose j : ℝ) * ((n : ℝ) + 1) =
        ((n + 1).choose j : ℝ) * (((n : ℝ) + 1) - j) := by
      have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_mul_succ_eq n j)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj] using h
    have hc : ((j : ℝ) - ((n : ℝ) + 1)) * ((n + 1).choose j : ℝ) +
        ((n : ℝ) + 1) * (n.choose j : ℝ) = 0 := by
      linear_combination hc0
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hz : (j : ℝ) * coefficient (n + 1) j -
        (((n : ℝ) + 1) * coefficient (n + 1) j -
          ((n : ℝ) + 9 / 2) * coefficient n j) = 0 := by
      calc
        _ = ((-1 : ℝ) ^ j * momentWeight n * ((n : ℝ) + 9 / 2) /
            (momentWeight j * (n.factorial : ℝ) * ((n : ℝ) + 1))) *
            (((j : ℝ) - ((n : ℝ) + 1)) * ((n + 1).choose j : ℝ) +
              ((n : ℝ) + 1) * (n.choose j : ℝ)) := by
          simp only [coefficient, momentWeight_succ, Nat.factorial_succ,
            Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          field_simp [momentWeight_ne_zero j, factorial_real_ne_zero n, hn]
          <;> ring
        _ = 0 := by rw [hc, mul_zero]
    linear_combination hz
  · rw [coefficient_eq_zero (n + 1) j (by omega),
      coefficient_eq_zero n j (by omega)]
    ring

/-- `X L_(n+1)' = (n+1)L_(n+1) -(n+9/2)L_n`. -/
theorem lowering (n : ℕ) :
    X * (laguerre (n + 1)).derivative =
      C ((n : ℝ) + 1) * laguerre (n + 1) -
        C ((n : ℝ) + 9 / 2) * laguerre n := by
  ext j
  cases j with
  | zero =>
      simpa only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_mul_zero, coeff_laguerre, Nat.cast_zero, zero_mul]
        using coefficient_lowering n 0
  | succ j =>
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_mul, Polynomial.coeff_derivative, coeff_laguerre]
      have h := coefficient_lowering n (j + 1)
      push_cast at h ⊢
      linear_combination h

/-- Degree-zero endpoint of the multiplication-by-X recurrence. -/
theorem X_laguerre_zero :
    X * laguerre 0 = C (9 / 2 : ℝ) * laguerre 0 - laguerre 1 := by
  have h := lowering 0
  rw [derivative_step] at h
  simp only [laguerre_zero, Polynomial.derivative_one, zero_sub, mul_neg,
    mul_one, Nat.cast_zero, zero_add, Polynomial.C_1, one_mul] at h ⊢
  linear_combination -h

/-- Three-term recurrence, with the endpoint isolated above; no negative index. -/
theorem X_laguerre_succ (n : ℕ) :
    X * laguerre (n + 1) =
      -C ((n : ℝ) + 2) * laguerre (n + 2) +
        C (2 * (n : ℝ) + 9 / 2 + 2) * laguerre (n + 1) -
        C ((n : ℝ) + 9 / 2) * laguerre n := by
  have h0 := lowering n
  have h1 := lowering (n + 1)
  have hx : X * (laguerre (n + 2)).derivative =
      X * (laguerre (n + 1)).derivative - X * laguerre (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, derivative_step, mul_sub]
  simp only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] at h1
  rw [h1, h0] at hx
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_1, Polynomial.C_ofNat] at hx ⊢
  linear_combination hx

end FiniteGaussianCap4.LaguerreSevenHalf
