/- GID: D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conical two-design concurrence bounds have a uniform ratio ordering. -/

/-
result
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#13873; Proved)
Direct frozen dependencies:
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm
    statement_id: sha256:ec2ace26dd8d3b1f1b18defca9f881e75ab25f3e1a67abd2b14cdc72e2702569;
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_eq_max_re_tr_U
    statement_id: sha256:3487611db943d93cce4a86af60f6499c8a001bc73fe819953d9bfd08a4e811b1;
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
    statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5.
Private proof declarations (consumer -> prerequisite):
  traceNorm_isometry: proof_shape: bind-only; consumers: bound_normal_form,
    dilation_from_completion.
  traceNorm_smul_nonneg: proof_shape: bind-only; consumers: bound_normal_form.
  frame_gram: proof_shape: bind-only; consumers: conical_normalization.
  correlation_factorization: proof_shape: bind-only; consumers: bound_normal_form.
  vI_dot: proof_shape: bind-only; consumers: Q_square.
  Q_positive: proof_shape: bind-only; consumers: Q_hermitian.
  Q_hermitian: proof_shape: bind-only; consumers: conical_normalization, bound_normal_form,
    ratio_monotonicity.
  Q_square: proof_shape: bind-only; consumers: conical_normalization, ratio_monotonicity.
  Q_realigned_trace: proof_shape: bind-only; consumers: ratio_monotonicity.
  M_one: proof_shape: bind-only; consumers: frame_normalization, projection_dilation.
  M_mul: proof_shape: bind-only; consumers: M_square, frame_normalization, projection_dilation,
    normalized_monotonicity.
  M_star: proof_shape: bind-only; consumers: frame_normalization, bound_normal_form,
    projection_dilation.
  M_action: proof_shape: bind-only; consumers: projection_dilation, normalized_monotonicity.
  M_square: proof_shape: bind-only; consumers: conical_normalization, projection_dilation.
  frame_normalization: proof_shape: bind-only; consumers: conical_normalization.
  parameter_pos: proof_shape: bind-only; consumers: conical_normalization, ratio_monotonicity.
  parameter_sq: proof_shape: bind-only; consumers: conical_normalization, bound_normal_form.
  conical_normalization: proof_shape: bind-only; consumers: bound_normal_form.
  bound_normal_form: proof_shape: bind-only; consumers: ratio_monotonicity.
  leftEmbedding_gram: proof_shape: bind-only; consumers: dilation_from_completion.
  leftEmbedding_compress: proof_shape: bind-only; consumers: dilation_from_completion.
  dilation_from_completion: proof_shape: bind-only; consumers: projection_dilation.
  M_action_left: proof_shape: bind-only; consumers: projection_dilation, normalized_monotonicity.
  projection_dilation: proof_shape: bind-only; consumers: normalized_monotonicity.
  normalized_monotonicity: proof_shape: bind-only; consumers: ratio_monotonicity.
  parameter_mono: proof_shape: bind-only; consumers: ratio_monotonicity.
  ratio_monotonicity: proof_shape: bind-only; consumers: result.
Information-escape registration is paused under CLAUDE.md section 3.9.
Utility kind is none: universal matrix identities and estimates, with no finite
certificate, bounded enumeration, checker or numerical-reduction declaration.
-/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Mathlib.Data.Matrix.ColumnRowPartitioned

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteStateChannel
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-
The consumed traceNorm_isometry proof adapts the local hIso in
D5/S3/Quantum/Foundation/FiniteDiamondDistance. The trace norm owner retains
leanprover-community/physlib commit 6a09b2d1761a0d4430083045a247eb121d8da260.
Copyright (c) 2025 Alex Meiburg. All rights reserved. Authors: Alex Meiburg.
The adaptation separates the local isometry fact and generalizes its universes.
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

def swap (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ).submatrix id Prod.swap

structure Design (d m : ℕ) where
  E : Fin m → Matrix (Fin d) (Fin d) ℂ
  alpha : ℝ
  beta : ℝ
  positive : ∀ i, (E i).PosSemidef
  beta_pos : 0 < beta
  beta_le_alpha : beta ≤ alpha
  tensor_identity : ∑ i, Matrix.kronecker (E i) (E i) =
    (alpha : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) + (beta : ℂ) • swap d

def P_E {d m : ℕ} (E : Design d m)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => Matrix.trace (rho * Matrix.kronecker (E.E i) (E.E j))

def c (d : ℕ) : ℝ := Real.sqrt (2 / ((d : ℝ) * ((d : ℝ) - 1)))

def B_E {d m : ℕ} (E : Design d m) (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  c d * (traceNorm (P_E E rho) - E.alpha - E.beta) / E.beta

def claim : Prop := ∀ d : ℕ, 2 ≤ d → ∀ m n : ℕ,
  ∀ (E : Design d m) (G : Design d n),
    (∀ rho : DensityState (Fin d × Fin d),
      B_E E (CStarMatrix.ofMatrix.symm rho.1) ≥ B_E G (CStarMatrix.ofMatrix.symm rho.1)) ∨
    (∀ rho : DensityState (Fin d × Fin d),
      B_E G (CStarMatrix.ofMatrix.symm rho.1) ≥ B_E E (CStarMatrix.ofMatrix.symm rho.1))

private theorem traceNorm_isometry {M N : Type*} [Fintype M] [DecidableEq M]
    [Fintype N] [DecidableEq N]
    (V : Matrix M N ℂ) (hV : Vᴴ * V = 1) (X : Matrix N N ℂ) :
    traceNorm (V * X * Vᴴ) = traceNorm X := by
  let P := CFC.sqrt (Xᴴ * X)
  have hXX : 0 ≤ Xᴴ * X := (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
  have hgram : (V * X * Vᴴ)ᴴ * (V * X * Vᴴ) = V * (Xᴴ * X) * Vᴴ := by
    calc
      _ = V * Xᴴ * (Vᴴ * V) * X * Vᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = _ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hP : 0 ≤ P := CFC.sqrt_nonneg _
  have hsquare : (V * P * Vᴴ) * (V * P * Vᴴ) = V * (Xᴴ * X) * Vᴴ := by
    calc
      _ = V * P * (Vᴴ * V) * P * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * (P * P) * Vᴴ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [show P * P = Xᴴ * X from CFC.sqrt_mul_sqrt_self _ hXX]
  have hpositive : 0 ≤ V * P * Vᴴ :=
    ((Matrix.nonneg_iff_posSemidef.mp hP).mul_mul_conjTranspose_same V).nonneg
  have hsqrt : CFC.sqrt (V * (Xᴴ * X) * Vᴴ) = V * P * Vᴴ :=
    CFC.sqrt_unique hsquare hpositive
  change (CFC.sqrt ((V * X * Vᴴ)ᴴ * (V * X * Vᴴ))).trace.re =
    (CFC.sqrt (Xᴴ * X)).trace.re
  rw [hgram, hsqrt, Matrix.trace_mul_cycle, hV, Matrix.one_mul]

private theorem traceNorm_smul_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (c : ℝ) (hc : 0 ≤ c) :
    traceNorm ((c : ℂ) • X) = c * traceNorm X := by
  have htr (U : unitaryGroup n ℂ) :
      ((U.val * ((c : ℂ) • X)).trace).re = c * ((U.val * X).trace).re := by
    simp [Matrix.trace_smul]
  apply le_antisymm
  · obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U ((c : ℂ) • X)).1
    have h := (traceNorm_eq_max_re_tr_U X).2 ⟨U, rfl⟩
    rw [← hU, htr]
    exact mul_le_mul_of_nonneg_left h hc
  · obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U X).1
    have h := (traceNorm_eq_max_re_tr_U ((c : ℂ) • X)).2 ⟨U, rfl⟩
    rwa [htr, hU] at h

private def frame {d m : ℕ} (E : Design d m) : Matrix (Fin m) (Fin d × Fin d) ℂ :=
  fun i => Matrix.vec (E.E i)

private def realignedFlip {d : ℕ} (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => rho (p.1,q.2) (p.2,q.1)

private theorem frame_gram {d m : ℕ} (E : Design d m) :
    (frame E)ᴴ * frame E = (E.beta : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) +
      (E.alpha : ℂ) • vecMulVec (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ))
        (star (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ))) := by
  ext p q
  have h := congrFun (congrFun E.tensor_identity (p.1,q.2)) (p.2,q.1)
  simp only [Matrix.sum_apply, kroneckerMap_apply, kronecker, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul] at h
  simp only [mul_apply, conjTranspose_apply, frame, Matrix.vec]
  have hherm : ∀ i, star (E.E i p.2 p.1) = E.E i p.1 p.2 := by
    intro i
    exact (E.positive i).1.apply _ _
  simp only [hherm]
  rw [h]
  simp [one_apply, swap, submatrix, Matrix.vec, vecMulVec, Prod.ext_iff, eq_comm]
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;> simp [hp, hq, add_comm]

private theorem correlation_factorization {d m : ℕ} (E : Design d m)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    P_E E rho = frame E * realignedFlip rho * (frame E)ᴴ := by
  ext i j
  change (∑ p : Fin d × Fin d, ∑ q : Fin d × Fin d,
    rho p q * (E.E i q.1 p.1 * E.E j q.2 p.2)) =
    ∑ p : Fin d × Fin d, (∑ q : Fin d × Fin d,
      E.E i q.2 q.1 * rho (q.1,p.2) (q.2,p.1)) * star (E.E j p.2 p.1)
  simp_rw [Finset.sum_mul, (E.positive j).1.apply]
  simp only [Fintype.sum_prod_type]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext b
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  ring

private def Q (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (d : ℂ)⁻¹ • vecMulVec (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ))
    (star (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)))

private lemma vI_dot (d : ℕ) :
    star (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) ⬝ᵥ
      Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ) = (d : ℂ) := by
  simpa using Matrix.star_vec_dotProduct_vec (1 : Matrix (Fin d) (Fin d) ℂ) 1

private lemma Q_positive (d : ℕ) : (Q d).PosSemidef := by
  apply (posSemidef_vecMulVec_self_star ((Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)))).smul
  simp

private lemma Q_hermitian (d : ℕ) : (Q d)ᴴ = Q d := (Q_positive d).1

private lemma Q_square {d : ℕ} (hd : 0 < d) : Q d * Q d = Q d := by
  have hn : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Q, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    vecMulVec_mul_vecMulVec, vI_dot, vecMulVec_smul, smul_smul]
  congr 1
  field_simp

private lemma Q_realigned_trace {d : ℕ} (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (Q d * (Matrix.of (fun p q => rho (p.1,q.2) (p.2,q.1)) :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)).trace =
      (d : ℂ)⁻¹ * rho.trace := by
  simp only [Q, Matrix.smul_mul, trace_smul, smul_eq_mul]
  congr 1
  simp [trace, mul_apply, vecMulVec, Matrix.vec, one_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

private def M (Q : Matrix n n ℂ) (t : ℂ) : Matrix n n ℂ := 1 + (t - 1) • Q

omit [Fintype n] in
private lemma M_one (Q : Matrix n n ℂ) : M Q 1 = 1 := by simp [M]

private lemma M_mul (Q : Matrix n n ℂ) (hQ : Q * Q = Q) (s t : ℂ) :
    M Q s * M Q t = M Q (s * t) := by
  simp only [M, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hQ]
  module

omit [Fintype n] in
private lemma M_star (Q : Matrix n n ℂ) (hQ : Qᴴ = Q) (t : ℝ) :
    (M Q (t : ℂ))ᴴ = M Q (t : ℂ) := by simp [M, hQ]

private lemma M_action (Q : Matrix n n ℂ) (hQ : Q * Q = Q) (t : ℂ) :
    M Q t * Q = t • Q := by
  simp only [M, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hQ]
  module

private lemma M_square (Q : Matrix n n ℂ) (hQ : Q * Q = Q) (t : ℂ) :
    M Q t * M Q t = 1 + (t ^ 2 - 1) • Q := by
  rw [M_mul Q hQ]
  simp only [M, pow_two]

omit [DecidableEq m] in
private theorem frame_normalization (A : Matrix m n ℂ) (Q : Matrix n n ℂ)
    (hQQ : Q * Q = Q) (hQstar : Qᴴ = Q) (b t : ℝ) (hb : 0 < b) (ht : 0 < t)
    (hgram : Aᴴ * A = (b : ℂ) • (M Q (t : ℂ) * M Q (t : ℂ))) :
    ∃ U : Matrix m n ℂ, Uᴴ * U = 1 ∧ A = (Real.sqrt b : ℂ) • (U * M Q (t : ℂ)) := by
  have hn : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hroot : (Real.sqrt b : ℂ) ^ 2 = b := by exact_mod_cast Real.sq_sqrt hb.le
  have hrootpos : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hrn : (Real.sqrt b : ℂ) ≠ 0 := by exact_mod_cast hrootpos.ne'
  let V : Matrix n n ℂ := M Q ((t : ℂ)⁻¹)
  have hvstar : Vᴴ = V := by simpa [V, Complex.ofReal_inv] using M_star Q hQstar t⁻¹
  have hVleft : V * M Q (t : ℂ) = 1 := by simp [V, M_mul Q hQQ, hn, M_one]
  have hVright : M Q (t : ℂ) * V = 1 := by simp [V, M_mul Q hQQ, hn, M_one]
  let U : Matrix m n ℂ := (Real.sqrt b : ℂ)⁻¹ • (A * V)
  refine ⟨U, ?_, ?_⟩
  · simp only [U, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      hvstar, map_inv₀, Complex.star_def, Complex.conj_ofReal]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hmiddle : V * Aᴴ * (A * V) = (b : ℂ) • (1 : Matrix n n ℂ) := by
      rw [Matrix.mul_assoc V Aᴴ, ← Matrix.mul_assoc Aᴴ A, hgram]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc
        _ = (V * M Q (t : ℂ)) * (M Q (t : ℂ) * V) := by
          simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hVleft, hVright, Matrix.one_mul]
    rw [hmiddle, smul_smul]
    have hs : ((Real.sqrt b : ℂ)⁻¹ * (Real.sqrt b : ℂ)⁻¹) * b = 1 := by
      rw [← pow_two, inv_pow, hroot]
      exact inv_mul_cancel₀ (by exact_mod_cast hb.ne')
    rw [hs, one_smul]
  · simp only [U, Matrix.smul_mul, smul_smul]
    rw [mul_inv_cancel₀ hrn, one_smul, Matrix.mul_assoc, hVleft, Matrix.mul_one]

private def parameter {d m : ℕ} (E : Design d m) : ℝ :=
  Real.sqrt (1 + (d : ℝ) * E.alpha / E.beta)

private lemma parameter_pos {d m : ℕ} (E : Design d m) : 0 < parameter E := by
  unfold parameter
  apply Real.sqrt_pos.2
  have hb : 0 < E.beta := E.beta_pos
  have ha : 0 ≤ E.alpha := le_trans E.beta_pos.le E.beta_le_alpha
  positivity

private lemma parameter_sq {d m : ℕ} (E : Design d m) :
    parameter E ^ 2 = 1 + (d : ℝ) * E.alpha / E.beta := by
  apply Real.sq_sqrt
  have hb : 0 < E.beta := E.beta_pos
  have ha : 0 ≤ E.alpha := le_trans E.beta_pos.le E.beta_le_alpha
  positivity

private lemma conical_normalization {d m : ℕ} (hd : 0 < d) (E : Design d m) :
    ∃ U : Matrix (Fin m) (Fin d × Fin d) ℂ,
      Uᴴ * U = 1 ∧ frame E = (Real.sqrt E.beta : ℂ) •
        (U * M (Q d) (parameter E : ℂ)) := by
  apply frame_normalization (frame E) (Q d) (Q_square hd) (Q_hermitian d)
    E.beta (parameter E) E.beta_pos (parameter_pos E)
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hbn : (E.beta : ℂ) ≠ 0 := by exact_mod_cast E.beta_pos.ne'
  have ht : (parameter E : ℂ)^2 = 1 + (d : ℂ) * E.alpha / E.beta := by
    exact_mod_cast parameter_sq E
  rw [frame_gram, M_square (Q d) (Q_square hd)]
  simp only [Q, smul_add, smul_smul]
  change (E.beta : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) +
    (E.alpha : ℂ) • vecMulVec (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ))
      (star (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ))) =
    (E.beta : ℂ) • 1 + ((E.beta : ℂ) * (((parameter E : ℂ)^2 - 1) * (d : ℂ)⁻¹)) •
      vecMulVec (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ))
        (star (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)))
  have hs : (E.beta : ℂ) * (((parameter E : ℂ)^2 - 1) * (d : ℂ)⁻¹) = E.alpha := by
    rw [ht]
    field_simp [hdn, hbn]
    ring
  rw [hs]

private theorem bound_normal_form {d m : ℕ} (hd : 0 < d) (E : Design d m)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    B_E E rho = c d * (traceNorm (M (Q d) (parameter E : ℂ) *
      realignedFlip rho * M (Q d) (parameter E : ℂ)) -
      (parameter E ^ 2 - 1) * (d : ℝ)⁻¹ - 1) := by
  obtain ⟨U, hU, hA⟩ := conical_normalization hd E
  have hroot : (Real.sqrt E.beta : ℂ) * (Real.sqrt E.beta : ℂ) = E.beta := by
    exact_mod_cast Real.mul_self_sqrt E.beta_pos.le
  have hP : P_E E rho = (E.beta : ℂ) • (U *
      (M (Q d) (parameter E : ℂ) * realignedFlip rho * M (Q d) (parameter E : ℂ)) * Uᴴ) := by
    rw [correlation_factorization, hA]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      M_star (Q d) (Q_hermitian d), Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hroot]
    congr 1
    simp only [Matrix.mul_assoc]
  have hn : traceNorm (P_E E rho) = E.beta *
      traceNorm (M (Q d) (parameter E : ℂ) * realignedFlip rho * M (Q d) (parameter E : ℂ)) := by
    rw [hP, traceNorm_smul_nonneg _ E.beta E.beta_pos.le, traceNorm_isometry U hU]
  rw [B_E, hn, parameter_sq]
  have hbn := E.beta_pos.ne'
  have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hbn, hdn]
  ring

private lemma leftEmbedding_gram :
    (Matrix.fromRows (1 : Matrix n n ℂ) (0 : Matrix n n ℂ))ᴴ *
      Matrix.fromRows (1 : Matrix n n ℂ) (0 : Matrix n n ℂ) = 1 := by
  simp only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
    Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_zero, add_zero]

private lemma leftEmbedding_compress (W : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    (Matrix.fromRows (1 : Matrix n n ℂ) (0 : Matrix n n ℂ))ᴴ * W *
      Matrix.fromRows (1 : Matrix n n ℂ) (0 : Matrix n n ℂ) =
        W.submatrix Sum.inl Sum.inl := by
  ext i j
  simp [Matrix.fromRows, mul_apply, conjTranspose_apply, Fintype.sum_sum_type, one_apply]

private theorem dilation_from_completion
    (Y H A K : Matrix n n ℂ)
    (hA : Aᴴ = A) (hK : Kᴴ = K)
    (hAK : A * K = K * A) (hunit : A * A + K * K = 1)
    (hAH : A * H = 1) (hHA : H * A = 1)
    (hgain : H * (K * K) * H = H * H - 1) :
    traceNorm Y + ((H * H - 1) * Y).trace.re ≤ traceNorm (H * Y * H) := by
  obtain ⟨O, hO⟩ := (traceNorm_eq_max_re_tr_U Y).1
  let T : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks A K K (-A)
  have hTstar : Tᴴ = T := by simp [T, fromBlocks_conjTranspose, hA, hK]
  have hTunit : T ∈ unitaryGroup (n ⊕ n) ℂ := by
    rw [mem_unitaryGroup_iff]
    change T * Tᴴ = 1
    rw [hTstar]
    simp [T, fromBlocks_multiply, hunit, hAK,
      show K * K + A * A = 1 from (add_comm _ _).trans hunit, fromBlocks_one]
  let V : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks O.val 0 0 1
  have hVunit : V ∈ unitaryGroup (n ⊕ n) ℂ := by
    rw [mem_unitaryGroup_iff]
    change V * Vᴴ = 1
    have hu : O.val * O.valᴴ = 1 := mem_unitaryGroup_iff.mp O.prop
    simp [V, fromBlocks_conjTranspose, fromBlocks_multiply, hu, fromBlocks_one]
  let U : unitaryGroup (n ⊕ n) ℂ := ⟨T, hTunit⟩ * ⟨V, hVunit⟩ * ⟨T, hTunit⟩
  let J : Matrix (n ⊕ n) n ℂ := Matrix.fromRows (1 : Matrix n n ℂ) (0 : Matrix n n ℂ)
  have hJ : Jᴴ * J = 1 := leftEmbedding_gram
  have hupp := (traceNorm_eq_max_re_tr_U (J * (H * Y * H) * Jᴴ)).2 ⟨U, rfl⟩
  rw [traceNorm_isometry J hJ] at hupp
  have htr : (U.val * (J * (H * Y * H) * Jᴴ)).trace =
      (O.val * Y).trace + ((H * H - 1) * Y).trace := by
    change ((T * V * T) * (J * (H * Y * H) * Jᴴ)).trace = _
    have htop : (T * V * T).submatrix Sum.inl Sum.inl = A * O.val * A + K * K := by
      ext i j
      simp [T, V, fromBlocks_multiply, submatrix]
    calc
      _ = ((Jᴴ * (T * V * T) * J) * (H * Y * H)).trace := by
        calc
          _ = ((T * V * T) * J * (H * Y * H) * Jᴴ).trace := by
            simp only [Matrix.mul_assoc]
          _ = (Jᴴ * ((T * V * T) * J) * (H * Y * H)).trace := trace_mul_cycle _ _ _
          _ = _ := by simp only [Matrix.mul_assoc]
      _ = ((A * O.val * A + K * K) * (H * Y * H)).trace := by
        congr 2
        exact leftEmbedding_compress _ |>.trans htop
      _ = (A * O.val * Y * H).trace + ((K * K) * (H * Y * H)).trace := by
        rw [add_mul, trace_add]
        congr 1
        simp only [← Matrix.mul_assoc]
        rw [Matrix.mul_assoc (A * O.val) A H, hAH, mul_one]
      _ = (O.val * Y).trace + ((H * H - 1) * Y).trace := by
        congr 1
        · rw [trace_mul_cycle]
          simp only [← Matrix.mul_assoc, hHA, one_mul]
        · calc
            _ = (H * (K * K) * H * Y).trace := by
              rw [← Matrix.mul_assoc, trace_mul_cycle]
              simp only [Matrix.mul_assoc]
            _ = _ := by rw [hgain]
  rw [htr, Complex.add_re, hO] at hupp
  exact hupp

private lemma M_action_left (Q : Matrix n n ℂ) (hQ : Q * Q = Q) (t : ℂ) :
    Q * M Q t = t • Q := by
  simp only [M, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hQ]
  module

private theorem projection_dilation (Y Q : Matrix n n ℂ) (hQQ : Q * Q = Q) (hQstar : Qᴴ = Q)
    (h : ℝ) (hh : 1 ≤ h) :
    traceNorm Y + (h ^ 2 - 1) * (Q * Y).trace.re ≤
      traceNorm (M Q (h : ℂ) * Y * M Q (h : ℂ)) := by
  have hp : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hn : (h : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  let A := M Q ((h : ℂ)⁻¹)
  let k := Real.sqrt (1 - h⁻¹ ^ 2)
  let K := (k : ℂ) • Q
  have hi : h⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr hh
  have hiz : 0 ≤ h⁻¹ := inv_nonneg.mpr hp.le
  have hk : k ^ 2 = 1 - h⁻¹ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hkc : (k : ℂ) ^ 2 = 1 - (h : ℂ)⁻¹ ^ 2 := by exact_mod_cast hk
  have hKK : K * K = ((k : ℂ) ^ 2) • Q := by
    simp only [K, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hQQ, pow_two]
  have hunit : A * A + K * K = 1 := by
    rw [hKK]
    change M Q ((h : ℂ)⁻¹) * M Q ((h : ℂ)⁻¹) + ((k : ℂ) ^ 2) • Q = 1
    rw [M_square Q hQQ, hkc]
    module
  have hgain : M Q (h : ℂ) * (K * K) * M Q (h : ℂ) =
      M Q (h : ℂ) * M Q (h : ℂ) - 1 := by
    rw [hKK, M_square Q hQQ]
    simp only [Matrix.mul_smul, Matrix.smul_mul, M_action Q hQQ,
      M_action_left Q hQQ, smul_smul]
    have hs : ((k : ℂ) ^ 2 * (h : ℂ)) * (h : ℂ) = (h : ℂ)^2 - 1 := by
      rw [hkc]
      field_simp [hn]
    rw [hs]
    module
  have hb := dilation_from_completion Y (M Q (h : ℂ)) A K
    (by simpa [A, Complex.ofReal_inv] using M_star Q hQstar h⁻¹)
    (by simp [K, hQstar])
    (by
      simp only [A, K, Matrix.mul_smul, Matrix.smul_mul,
        M_action Q hQQ, M_action_left Q hQQ, smul_smul])
    hunit
    (by simp [A, M_mul Q hQQ, hn, M_one])
    (by simp [A, M_mul Q hQQ, hn, M_one]) hgain
  have htr : ((M Q (h : ℂ) * M Q (h : ℂ) - 1) * Y).trace.re =
      (h ^ 2 - 1) * (Q * Y).trace.re := by
    rw [M_square Q hQQ]
    simp [trace_smul, ← Complex.ofReal_pow]
  rwa [htr] at hb

private theorem normalized_monotonicity (X Q : Matrix n n ℂ) (hQQ : Q * Q = Q)
    (hQstar : Qᴴ = Q) (s t r : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (htrace : (Q * X).trace.re = r) :
    traceNorm (M Q (s : ℂ) * X * M Q (s : ℂ)) - (s^2 - 1) * r ≤
      traceNorm (M Q (t : ℂ) * X * M Q (t : ℂ)) - (t^2 - 1) * r := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hsn : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hh : 1 ≤ t / s := (one_le_div hs).mpr hst
  have hmul : M Q (t / s : ℝ) * M Q (s : ℂ) = M Q (t : ℂ) := by
    rw [M_mul Q hQQ]
    congr 1
    push_cast
    field_simp
  have hmul' : M Q (s : ℂ) * M Q (t / s : ℝ) = M Q (t : ℂ) := by
    rw [M_mul Q hQQ]
    congr 1
    push_cast
    field_simp
  have htr : (Q * (M Q (s : ℂ) * X * M Q (s : ℂ))).trace.re = s^2 * r := by
    calc
      _ = (M Q (s : ℂ) * Q * M Q (s : ℂ) * X).trace.re := by
        congr 1
        calc
          _ = (Q * M Q (s : ℂ) * X * M Q (s : ℂ)).trace := by
            simp only [Matrix.mul_assoc]
          _ = (M Q (s : ℂ) * (Q * M Q (s : ℂ)) * X).trace := trace_mul_cycle _ _ _
          _ = _ := by simp only [Matrix.mul_assoc]
      _ = (((s : ℂ)^2) • (Q * X)).trace.re := by
        rw [M_action Q hQQ, Matrix.smul_mul, M_action_left Q hQQ,
          smul_smul, Matrix.smul_mul]
        simp only [pow_two]
      _ = s^2 * r := by simp [trace_smul, ← Complex.ofReal_pow, htrace]
  have h := projection_dilation (M Q (s : ℂ) * X * M Q (s : ℂ)) Q hQQ hQstar
    (t / s) hh
  rw [htr] at h
  have heq : M Q (t / s : ℝ) * (M Q (s : ℂ) * X * M Q (s : ℂ)) *
      M Q (t / s : ℝ) = M Q (t : ℂ) * X * M Q (t : ℂ) := by
    calc
      _ = (M Q (t / s : ℝ) * M Q (s : ℂ)) * X *
        (M Q (s : ℂ) * M Q (t / s : ℝ)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hmul, hmul']
  rw [heq] at h
  have hscalar : ((t / s)^2 - 1) * (s^2 * r) = (t^2 - s^2) * r := by
    field_simp [hs.ne']
  rw [hscalar] at h
  linarith

private theorem parameter_mono {d m n : ℕ} (E : Design d m) (G : Design d n)
    (h : G.alpha / G.beta ≤ E.alpha / E.beta) : parameter G ≤ parameter E := by
  unfold parameter
  apply Real.sqrt_le_sqrt
  rw [mul_div_assoc, mul_div_assoc]
  exact add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg d))

private theorem ratio_monotonicity {d m n : ℕ} (hd : 2 ≤ d) (E : Design d m) (G : Design d n)
    (h : G.alpha / G.beta ≤ E.alpha / E.beta) (rho : DensityState (Fin d × Fin d)) :
    B_E G (CStarMatrix.ofMatrix.symm rho.1) ≤ B_E E (CStarMatrix.ofMatrix.symm rho.1) := by
  have hdpos : 0 < d := by omega
  have htr : (Q d * realignedFlip (CStarMatrix.ofMatrix.symm rho.1)).trace.re = (d : ℝ)⁻¹ := by
    have h0 := Q_realigned_trace (CStarMatrix.ofMatrix.symm rho.1)
    change (Q d * realignedFlip (CStarMatrix.ofMatrix.symm rho.1)).trace = _ at h0
    have htrace : (CStarMatrix.ofMatrix.symm rho.1).trace = 1 := rho.2.2
    rw [htrace, mul_one] at h0
    rw [h0]
    simp
  have hm := normalized_monotonicity (realignedFlip (CStarMatrix.ofMatrix.symm rho.1))
    (Q d) (Q_square hdpos)
    (Q_hermitian d) (parameter G) (parameter E) ((d : ℝ)⁻¹)
    (parameter_pos G) (parameter_mono E G h) htr
  rw [bound_normal_form hdpos G, bound_normal_form hdpos E]
  exact mul_le_mul_of_nonneg_left (by linarith [hm]) (Real.sqrt_nonneg _)

theorem result : claim := by
  intro d hd m n E G
  rcases le_total (G.alpha / G.beta) (E.alpha / E.beta) with h | h
  · exact Or.inl (fun rho => ratio_monotonicity hd E G h rho)
  · exact Or.inr (fun rho => ratio_monotonicity hd G E h rho)

end D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
