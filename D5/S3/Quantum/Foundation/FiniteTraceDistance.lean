/- GID: D5/S3/Quantum/Foundation/FiniteTraceDistance
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FiniteTraceDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual trace distance and contraction for canonical finite quantum channels. -/

/-
Selected from leanprover-community/physlib commit 6a09b2d1761a0d4430083045a247eb121d8da260:
QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean and its live technical declarations
from Matrix.lean, Isometry.lean, and HermitianMat/Unitary.lean.
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Authors: Alex Meiburg.
Modified by trureturing on 2026-09-08: imports, owner namespace, explicit local names,
private technical closure, and the new canonical state/channel adapter below.
The retained upstream proofs are bind-only source reuse. Their SVD and orthonormal
extension dependencies are live in the triangle inequality, not discarded.
Retirement condition: when this repository's own pinned Mathlib contains equivalent
declarations, replace this retained source with direct imports.
Full Apache-2.0 license follows. The immutable upstream tree contains no NOTICE file.
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

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

noncomputable section
namespace D5.S3.Quantum.Foundation.FiniteTraceDistance
open BigOperators Classical Matrix
open scoped ComplexOrder MatrixOrder

private def isometry {d e R : Type*} [Fintype d] [DecidableEq e]
    [CommRing R] [StarRing R] (A : Matrix d e R) : Prop :=
  A.conjTranspose * A = 1

private theorem mem_unitaryGroup_iff_isometry {d R : Type*} [Fintype d] [DecidableEq d]
    [CommRing R] [StarRing R] (A : Matrix d d R) :
    A ∈ unitaryGroup d R ↔ isometry A ∧ isometry A.conjTranspose := by
  rw [isometry, isometry, conjTranspose_conjTranspose]
  rfl

private theorem re_trace_eq_trace {n R : Type*} [Fintype n] [RCLike R]
    {A : Matrix n n R} (hA : A.IsHermitian) : (RCLike.re A.trace : R) = A.trace := by
  rw [trace, map_sum, RCLike.ofReal_sum, IsHermitian.coe_re_diag hA]

private lemma unitary_row_sum_norm_sq {d : Type*} [Fintype d] [DecidableEq d]
    (C : Matrix d d ℂ) (hC : C * C.conjTranspose = 1) (i : d) :
    ∑ j, ‖C i j‖ ^ 2 = 1 := by
  replace hC := congr($hC i i)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_pow, Matrix.one_apply_eq] at hC
  exact_mod_cast hC

variable {m n R : Type*} [Fintype m] [Fintype n] [RCLike R]
/-- The trace norm of a matrix: Tr[√(A† A)]. -/
def traceNorm (A : Matrix m n R) : ℝ :=
  open MatrixOrder in
  RCLike.re (CFC.sqrt (Aᴴ * A)).trace


/-- The trace norm of the negative is equal to the trace norm. -/
@[simp]
theorem traceNorm_neg (A : Matrix m n R) : traceNorm (-A) = traceNorm A := by
  unfold traceNorm
  congr! 3
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg]
  exact neg_neg _

/-- The trace norm is nonnegative. Property 9.1.1 in Wilde. -/
theorem traceNorm_nonneg (A : Matrix m n R) : 0 ≤ traceNorm A :=
  open MatrixOrder in
  And.left $ RCLike.nonneg_iff.1
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg


variable [DecidableEq n]

omit [Fintype m] [DecidableEq n] in
private lemma inner_A_mulVec_eq (A : Matrix n n ℂ) (v w : n → ℂ) :
    inner ℂ (WithLp.toLp 2 (A.mulVec v)) (WithLp.toLp 2 (A.mulVec w)) =
      star v ⬝ᵥ ((Aᴴ * A).mulVec w) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]

/-- Singular value decomposition for square complex matrices, with singular values expressed as
square roots of the eigenvalues of `Aᴴ * A`. -/
private theorem exists_svd_sqrt_eigenvalues (A : Matrix n n ℂ) :
    let hH : (Aᴴ * A).IsHermitian := by
      simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
    ∃ V W : Matrix.unitaryGroup n ℂ,
      A = V.val * Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)) * W.valᴴ := by
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  let s : n → ℂ := fun i => Real.sqrt (hH.eigenvalues i)
  have hs_ne {i : n} (hi : hH.eigenvalues i ≠ 0) : s i ≠ 0 := by
    dsimp [s]
    exact_mod_cast Real.sqrt_ne_zero'.2
      (lt_of_le_of_ne (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i) (Ne.symm hi))
  let u : n → EuclideanSpace ℂ n := fun i =>
    if hi : hH.eigenvalues i ≠ 0 then
      ((s i)⁻¹ • WithLp.toLp 2 (A.mulVec (hH.eigenvectorBasis i).ofLp))
    else 0
  have hu : Orthonormal ℂ ({i | hH.eigenvalues i ≠ 0}.domRestrict u) := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp [u, s, Set.domRestrict]
    have hi' : hH.eigenvalues i.1 ≠ 0 := i.2
    have hj' : hH.eigenvalues j.1 ≠ 0 := j.2
    simp only [hi', hj', not_false_eq_true, if_true]
    rw [inner_smul_left, inner_smul_right, inner_A_mulVec_eq, hH.mulVec_eigenvectorBasis j.1]
    by_cases hij : i.1 = j.1
    · cases Subtype.ext hij
      simp [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, mul_comm]
      field_simp [show (Real.sqrt (hH.eigenvalues i.1) : ℂ) ≠ 0 by simpa [s] using hs_ne i.2]
      exact_mod_cast (Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i.1)).symm
    · simpa [hij, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
        orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal, mul_comm]
        using (show i ≠ j from fun h => hij (congrArg Subtype.val h))
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℂ) (E := EuclideanSpace ℂ n) (ι := n)
      (by simp [finrank_euclideanSpace]) (v := u)
      (s := {i | hH.eigenvalues i ≠ 0}) hu
  let V : Matrix.unitaryGroup n ℂ := ⟨Matrix.of (fun i j ↦ b j i), by
    simp only [Matrix.mem_unitaryGroup_iff]
    ext i j
    have h1 := b.sum_inner_mul_inner (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simp_all [inner]
    exact h1⟩
  let W : Matrix.unitaryGroup n ℂ := hH.eigenvectorUnitary
  have hAW : A * W.val = V.val * Matrix.diagonal s := by
    ext i j
    have hleft : (A * W.val) i j = A.mulVec (hH.eigenvectorBasis j).ofLp i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, W, Matrix.IsHermitian.eigenvectorUnitary_apply]
    by_cases hj : hH.eigenvalues j = 0
    · have hzero : A.mulVec (hH.eigenvectorBasis j).ofLp = 0 := by
        apply (WithLp.toLp_injective (p := 2))
        exact inner_self_eq_zero.mp (by
          rw [inner_A_mulVec_eq]
          rw [hH.mulVec_eigenvectorBasis j, hj]
          simp)
      rw [hleft, congrFun hzero i]
      simp [Matrix.mul_apply, Matrix.diagonal, V, s, hj]
    · have hbji : b j i = (s j)⁻¹ * A.mulVec (hH.eigenvectorBasis j).ofLp i := by
        simpa [u, hj] using congrArg (fun x : EuclideanSpace ℂ n => x.ofLp i) (hb j hj)
      have hs_mul : s j * b j i = A.mulVec (hH.eigenvectorBasis j).ofLp i := by
        rw [hbji]; field_simp [hs_ne hj]
      rw [hleft, ← hs_mul]; simp [Matrix.mul_apply, Matrix.diagonal, V, s, mul_comm]
  refine ⟨V, W, ?_⟩
  simpa [W, Matrix.IsHermitian.eigenvectorUnitary, Matrix.mul_assoc] using
    congrArg (fun X => X * W.valᴴ) hAW

open scoped MatrixOrder in
private lemma traceNorm_eq_sum_sqrt_eigenvalues (A : Matrix n n ℂ) :
    let hH : (Aᴴ * A).IsHermitian := by
      simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
    traceNorm A = ∑ i, Real.sqrt (hH.eigenvalues i) := by
  intro hH
  unfold traceNorm
  rw [CFC.sqrt_eq_real_sqrt (Aᴴ * A)
    (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self),
    cfcₙ_eq_cfc, Matrix.IsHermitian.cfc_eq hH, Matrix.IsHermitian.cfc]
  simp [Matrix.trace_mul_comm, Matrix.mul_assoc]


/-- For square complex matrices, the trace norm is the maximum of `re (Tr[U * A])`
over unitaries `U`. -/
theorem traceNorm_eq_max_re_tr_U (A : Matrix n n ℂ) :
    IsGreatest {x : ℝ | ∃ U : unitaryGroup n ℂ, Complex.re ((U.val * A).trace) = x} (traceNorm A) := by
  classical
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  obtain ⟨V, W, hA⟩ :
      ∃ V W : Matrix.unitaryGroup n ℂ,
        A = V.val * Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)) * W.valᴴ := by
    simpa [hH] using exists_svd_sqrt_eigenvalues A
  have htraceNorm : traceNorm A = ∑ i, Real.sqrt (hH.eigenvalues i) := by
    simpa [hH] using traceNorm_eq_sum_sqrt_eigenvalues A
  set D : Matrix n n ℂ := Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  have hVu : V.valᴴ * V.val = 1 := (mem_unitaryGroup_iff_isometry V.val).mp V.prop |>.1
  have hWu : W.valᴴ * W.val = 1 := (mem_unitaryGroup_iff_isometry W.val).mp W.prop |>.1
  refine ⟨⟨W * star V, ?_⟩, ?_⟩
  · calc Complex.re (((W * star V).val * A).trace)
        = Complex.re (D.trace) := by
          rw [hA]; congr 1
          change (W.val * V.valᴴ * (V.val * D * W.valᴴ)).trace = D.trace
          simp [Matrix.mul_assoc, hVu, Matrix.trace_mul_comm, hWu]
      _ = traceNorm A := by simp [D, Matrix.trace, htraceNorm]
  · rintro _ ⟨U, rfl⟩
    set C : Matrix.unitaryGroup n ℂ := star W * U * V
    rw [show Complex.re ((U.val * A).trace) =
        ∑ i, Real.sqrt (hH.eigenvalues i) * Complex.re (C.val i i) by
      conv_lhs => rw [hA]
      have h1 : (U.val * (V.val * D * W.valᴴ)).trace = (C.val * D).trace := by
        change _ = (W.valᴴ * U.val * V.val * D).trace
        rw [show (U.val * (V.val * D * W.valᴴ)).trace =
            (((U.val * V.val) * D) * W.valᴴ).trace by simp [Matrix.mul_assoc],
          Matrix.trace_mul_comm _ W.valᴴ]
        simp [Matrix.mul_assoc]
      rw [h1]
      simp [D, Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Complex.mul_re, mul_comm],
      htraceNorm]
    have hdiag_le : ∀ i, Complex.re (C.val i i) ≤ 1 := fun i =>
      (Complex.re_le_norm _).trans (by
        have hsq : ‖C.val i i‖ ^ 2 ≤ 1 := by
          linarith [(Finset.single_le_sum (f := fun j => ‖C.val i j‖ ^ 2)
            (fun j _ => by positivity) (Finset.mem_univ i)).trans_eq
            (unitary_row_sum_norm_sq C.val (Matrix.mem_unitaryGroup_iff.mp C.prop) i)]
        nlinarith [norm_nonneg (C.val i i), hsq])
    exact Finset.sum_le_sum fun i _ => by
      nlinarith [hdiag_le i, Real.sqrt_nonneg (hH.eigenvalues i)]

/-- The trace norm satisfies the triangle inequality for square complex matrices. -/
theorem traceNorm_add_le (A B : Matrix n n ℂ) : traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  obtain ⟨Uab, h₁⟩ := (traceNorm_eq_max_re_tr_U (A + B)).left
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at h₁
  obtain h₂ := (traceNorm_eq_max_re_tr_U A).right
  obtain h₃ := (traceNorm_eq_max_re_tr_U B).right
  simp only [upperBounds, Set.mem_ofPred_eq] at h₂ h₃
  calc _
    _ = RCLike.re ((Uab.1 * A).trace) + RCLike.re ((Uab.1 * B).trace) := h₁.symm
    _ ≤ traceNorm A + RCLike.re ((Uab.1 * B).trace) := by
      simpa [add_comm] using add_le_add_right
        (h₂ (a := RCLike.re ((Uab.1 * A).trace)) ⟨Uab, rfl⟩)
        (RCLike.re ((Uab.1 * B).trace))
    _ ≤ _ := by
      simpa [add_comm] using add_le_add_left
        (h₃ (a := RCLike.re ((Uab.1 * B).trace)) ⟨Uab, rfl⟩) (traceNorm A)

/-- A positive semidefinite matrix has trace norm equal to its trace. -/
theorem traceNorm_of_posSemidef {A : Matrix m m R} (hA : A.PosSemidef) :
    traceNorm A = A.trace := by
  have : Aᴴ * A = A^2 := by rw [hA.1, pow_two]
  open MatrixOrder in
  rw [traceNorm, this, CFC.sqrt_sq A, re_trace_eq_trace hA.1]


open scoped CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel

section Canonical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def act (channel : QuantumChannel ι ι) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix A))

def traceDistance (rho sigma : DensityState ι) : ℝ :=
  traceNorm (CStarMatrix.ofMatrix.symm rho.val - CStarMatrix.ofMatrix.symm sigma.val) / 2

theorem traceDistance_nonneg (rho sigma : DensityState ι) : 0 ≤ traceDistance rho sigma :=
  div_nonneg (traceNorm_nonneg _) (by norm_num)

theorem traceDistance_symm (rho sigma : DensityState ι) :
    traceDistance rho sigma = traceDistance sigma rho := by
  unfold traceDistance
  rw [show CStarMatrix.ofMatrix.symm rho.val - CStarMatrix.ofMatrix.symm sigma.val =
    -(CStarMatrix.ofMatrix.symm sigma.val - CStarMatrix.ofMatrix.symm rho.val) by abel,
    traceNorm_neg]

theorem traceDistance_triangle (rho sigma tau : DensityState ι) :
    traceDistance rho tau ≤ traceDistance rho sigma + traceDistance sigma tau := by
  have h := traceNorm_add_le
    (CStarMatrix.ofMatrix.symm rho.val - CStarMatrix.ofMatrix.symm sigma.val)
    (CStarMatrix.ofMatrix.symm sigma.val - CStarMatrix.ofMatrix.symm tau.val)
  rw [sub_add_sub_cancel] at h
  unfold traceDistance
  linarith

theorem traceDistance_le_one (rho sigma : DensityState ι) : traceDistance rho sigma ≤ 1 := by
  have hn (tau : DensityState ι) : traceNorm (CStarMatrix.ofMatrix.symm tau.val) = 1 := by
    have hp : (CStarMatrix.ofMatrix.symm tau.val).PosSemidef :=
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm tau.prop.1).posSemidef
    have ht := congrArg Complex.re (traceNorm_of_posSemidef hp)
    change traceNorm (CStarMatrix.ofMatrix.symm tau.val) = (Matrix.trace tau.val).re at ht
    simpa [tau.prop.2] using ht
  have h := traceNorm_add_le (CStarMatrix.ofMatrix.symm rho.val)
    (-CStarMatrix.ofMatrix.symm sigma.val)
  rw [traceNorm_neg, hn rho, hn sigma] at h
  unfold traceDistance
  rw [sub_eq_add_neg]
  linarith

private theorem trace_norm_jordan_mass (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    traceNorm A = (Matrix.trace (posPart A)).re + (Matrix.trace (negPart A)).re := by
  have h := congrArg (fun B : Matrix ι ι ℂ => (Matrix.trace B).re)
    (CFC.posPart_add_negPart A hA)
  simpa [Matrix.trace_add, CFC.abs, Matrix.star_eq_conjTranspose, traceNorm] using h.symm

theorem traceDistance_contract (channel : QuantumChannel ι ι) (rho sigma : DensityState ι) :
    traceDistance (channel.mapState rho) (channel.mapState sigma) ≤
      traceDistance rho sigma := by
  let A : Matrix ι ι ℂ := CStarMatrix.ofMatrix.symm rho.val - CStarMatrix.ofMatrix.symm sigma.val
  have hp (tau : DensityState ι) : (CStarMatrix.ofMatrix.symm tau.val).PosSemidef :=
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm tau.prop.1).posSemidef
  have hA : A.IsHermitian := (hp rho).isHermitian.sub (hp sigma).isHermitian
  let P : Matrix ι ι ℂ := posPart A
  let M : Matrix ι ι ℂ := negPart A
  have hP : 0 ≤ P := CFC.posPart_nonneg A
  have hM : 0 ≤ M := CFC.negPart_nonneg A
  have hnorm (B : Matrix ι ι ℂ) (hB : 0 ≤ B) :
      traceNorm (act channel B) = (Matrix.trace B).re := by
    have hout : (act channel B).PosSemidef :=
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
        (map_nonneg channel.toCompletelyPositiveMap
          (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hB))).posSemidef
    have h := congrArg Complex.re (traceNorm_of_posSemidef hout)
    have ht := congrArg Complex.re (channel.trace_preserving (CStarMatrix.ofMatrix B))
    exact h.trans ht
  have hmap : act channel A = act channel P - act channel M := by
    rw [show A = P - M from (CFC.posPart_sub_negPart A hA).symm]
    unfold act
    change CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix P - CStarMatrix.ofMatrix M)) = _
    rw [map_sub]
    rfl
  have hbound : traceNorm (act channel A) ≤ traceNorm A := by
    rw [hmap, sub_eq_add_neg]
    calc
      traceNorm (act channel P + -act channel M) ≤
          traceNorm (act channel P) + traceNorm (-act channel M) := traceNorm_add_le _ _
      _ = traceNorm A := by
        rw [traceNorm_neg, hnorm P hP, hnorm M hM]
        exact (trace_norm_jordan_mass A hA).symm
  have hdiff : CStarMatrix.ofMatrix.symm (channel.mapState rho).val -
      CStarMatrix.ofMatrix.symm (channel.mapState sigma).val = act channel A := by
    unfold act A
    change CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap rho.val) -
      CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap sigma.val) =
      CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap (rho.val - sigma.val))
    rw [map_sub]
    rfl
  unfold traceDistance
  rw [hdiff]
  exact div_le_div_of_nonneg_right hbound (by norm_num)

end Canonical
end D5.S3.Quantum.Foundation.FiniteTraceDistance
