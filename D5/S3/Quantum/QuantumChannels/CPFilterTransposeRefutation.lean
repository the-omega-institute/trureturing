/- GID: D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.claim; result=D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.result; claim=D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.claim
   digest: A unital qutrit channel fails invertible CP-filter transpose equivalence. -/

/-
proof_shape: result: content
escape_witness: form 2 — the public refutation is produced by the non-binding
  CP-inverse congruence construction on its live proof path:
  ∀ L G : MatrixMap (Fin 3) (Fin 3) ℂ, MatrixMap.IsCompletelyPositive L →
    MatrixMap.IsCompletelyPositive G → (∀ X, G (L X) = X) →
    ∃ A : Matrix (Fin 3) (Fin 3) ℂ, IsUnit A ∧ ∀ X, L X = A * X * Aᴴ.
  This proof-local proposition is used to force commutation of the witness range
  and is not definitionally equivalent to ¬ claim.
admission_basis: open-problem-resolution (#13180; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
    statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive
    statement_id: sha256:39e2682fd93035c705a08181bb7fdfb77067eba43afcc98c200c30543b913ed4
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron
    statement_id: sha256:6bbbe42180d7cde8ee171b8a1aeeb16449194862345f2042d95ec7c0b2055471
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron_def
    statement_id: sha256:0a066df1b1de64e4fda175d1ac776d744674a6465abc8a7f13b12f185ce29405
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive
    statement_id: sha256:522daaecff9970808def6ecdd938d4b89107d2820c79bafbf378ab083767f57f
  D5/S3/Quantum/Recovery/KrausLeftInverseNecessity.identity_kraus_scalar
    statement_id: sha256:c8d2f793808fd628ac5bc956a75c99d0677c3daae811b3a29bbe95e9747f5885
  D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCPTP
    statement_id: sha256:1440f7e681ed2017e7c90aedfe54aa0ad218d57311655f9d554863853dd8f53c
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
/-
Selected-source spectral data and proof-local steps: QuantumInfo/Channels/MatrixMap.lean
(choi_matrix_eq_map_proj, exists_kraus_of_choi_PSD, choi_map_inv).
Immutable source: https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260
Adaptation: all-amplification matrix CP and proof-local qutrit Choi/Kraus
construction; no standalone selected-source theorem.
Retirement condition: replace these selected steps by direct applications when
equivalent statements are available in this repository pinned Mathlib;
current pin db584cd6d46c92f209a44c0f1c829460d327499d.
The complete immutable upstream tree contains no NOTICE file.
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

import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Quantum.Recovery.KrausLeftInverseNecessity

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsCPTP)

set_option linter.unusedSimpArgs false
namespace D5.S3.Quantum.QuantumChannels.CPFilterTransposeRefutation

def CPInvertible (F : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  MatrixMap.IsCompletelyPositive F ∧ ∃ G : MatrixMap (Fin 3) (Fin 3) ℂ, MatrixMap.IsCompletelyPositive G ∧ (∀ X, G (F X) = X) ∧ (∀ X, F (G X) = X)

def UnitalChannel (F : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  IsCPTP F ∧ F 1 = 1

def claim : Prop := ∀ F : MatrixMap (Fin 3) (Fin 3) ℂ, UnitalChannel F →
  ∀ (S : Type) [Fintype S] (K : S → Matrix (Fin 3) (Fin 3) ℂ),
    F = MatrixMap.of_kraus K K →
    ∃ L R : MatrixMap (Fin 3) (Fin 3) ℂ, CPInvertible L ∧ CPInvertible R ∧
      MatrixMap.of_kraus (fun i => (K i)ᵀ) (fun i => (K i)ᵀ) = L ∘ₗ F ∘ₗ R

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem result : ¬ claim := by
  classical
  have kraus_transpose_independent {S T : Type} [Fintype S] [Fintype T]
      (K : S → Matrix (Fin 3) (Fin 3) ℂ)
      (K' : T → Matrix (Fin 3) (Fin 3) ℂ)
      (hK : MatrixMap.of_kraus K K = MatrixMap.of_kraus K' K') :
      MatrixMap.of_kraus (fun i => (K i)ᵀ) (fun i => (K i)ᵀ) =
        MatrixMap.of_kraus (fun j => (K' j)ᵀ) (fun j => (K' j)ᵀ) := by
    have duality {U : Type} [Fintype U]
        (H : U → Matrix (Fin 3) (Fin 3) ℂ)
        (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
        Matrix.trace (Y * MatrixMap.of_kraus H H X) =
          Matrix.trace ((∑ i, (H i)ᴴ * Y * H i) * X) := by
      simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
        AddHom.coe_mk, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_cycle' Y (H i * X) (H i)ᴴ
    have dual_eq (Y : Matrix (Fin 3) (Fin 3) ℂ) :
        (∑ i, (K i)ᴴ * Y * K i) = ∑ j, (K' j)ᴴ * Y * K' j := by
      apply Matrix.ext_iff_trace_mul_right.mpr
      intro X
      rw [← duality K X Y, ← duality K' X Y, hK]
    have transpose_dual {U : Type} [Fintype U]
        (H : U → Matrix (Fin 3) (Fin 3) ℂ)
        (X : Matrix (Fin 3) (Fin 3) ℂ) :
        MatrixMap.of_kraus (fun i => (H i)ᵀ) (fun i => (H i)ᵀ) X =
          (∑ i, (H i)ᴴ * Xᵀ * H i)ᵀ := by
      simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
        AddHom.coe_mk, Matrix.transpose_sum, Matrix.transpose_mul,
        Matrix.transpose_transpose,
        Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.mul_assoc]
    apply LinearMap.ext
    intro X
    rw [transpose_dual K X, transpose_dual K' X, dual_eq Xᵀ]
  let choi (f : MatrixMap (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    fun p q => f (Matrix.single p.2 q.2 1) p.1 q.1
  -- Selected-source spectral construction, specialized to the qutrit proof.
  have choi_kraus (f : MatrixMap (Fin 3) (Fin 3) ℂ) (hC : (choi f).PosSemidef) :
      ∃ K : (Fin 3 × Fin 3) → Matrix (Fin 3) (Fin 3) ℂ, f = MatrixMap.of_kraus K K := by
    let K : (Fin 3 × Fin 3) → Matrix (Fin 3) (Fin 3) ℂ := fun k i j =>
      hC.1.eigenvectorUnitary (i,j) k * (Real.sqrt (hC.1.eigenvalues k) : ℂ)
    have spectral (p q : Fin 3 × Fin 3) : choi f p q =
        ∑ k, K k p.1 p.2 * star (K k q.1 q.2) := by
      calc
        choi f p q = ∑ k, hC.1.eigenvectorUnitary p k *
            (hC.1.eigenvalues k : ℂ) * star (hC.1.eigenvectorUnitary q k) := by
          have hentry := congrFun (congrFun hC.1.spectral_theorem p) q
          simpa [Matrix.mul_apply, Matrix.diagonal] using hentry
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k _
          simp only [K, star_mul, Complex.star_def, Complex.conj_ofReal]
          have hs : (Real.sqrt (hC.1.eigenvalues k) : ℂ) *
              (Real.sqrt (hC.1.eigenvalues k) : ℂ) = (hC.1.eigenvalues k : ℂ) := by
            exact_mod_cast Real.mul_self_sqrt (hC.eigenvalues_nonneg k)
          rw [← hs]
          ring
    refine ⟨K, ?_⟩
    ext X b c
    have expand : X = ∑ i, ∑ j, X i j • Matrix.single i j 1 := by
      ext i j
      simp [Matrix.single, Matrix.sum_apply, ite_and]
    conv_lhs => rw [expand]
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    change (∑ i, ∑ j, X i j * choi f (b,i) (c,j)) = _
    simp_rw [spectral]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have cp_exists_kraus (f : MatrixMap (Fin 3) (Fin 3) ℂ) (hCP : MatrixMap.IsCompletelyPositive f) :
      ∃ K : (Fin 3 × Fin 3) → Matrix (Fin 3) (Fin 3) ℂ, f = MatrixMap.of_kraus K K := by
    let v : Fin 3 × Fin 3 → ℂ := fun x => if x.1 = x.2 then 1 else 0
    have proj : choi f = MatrixMap.kron f LinearMap.id (Matrix.vecMulVec v (star v)) := by
      ext ⟨b₁,i₁⟩ ⟨b₂,i₂⟩
      simp [choi, MatrixMap.kron_def, v, Matrix.vecMulVec, Matrix.single, ite_and]
    have hC : (choi f).PosSemidef := by
      rw [proj]
      exact hCP 3 (Matrix.posSemidef_vecMulVec_self_star v)
    exact choi_kraus f hC

  let rho (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
    ![!![(1/2:ℂ),0,0; 0,1/3,0; 0,0,1/6],
      !![(1/6:ℂ),1/12,0; 1/12,1/3,0; 0,0,1/2],
      !![(1/3:ℂ),-1/12,0; -1/12,1/3,0; 0,0,1/3]] j

  let witness : MatrixMap (Fin 3) (Fin 3) ℂ := {
    toFun X := ∑ j, X j j • rho j
    map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
    map_smul' c X := by simp [Matrix.smul_apply, mul_smul, Finset.smul_sum] }

  have diagonal_commute {X Y : Matrix (Fin 3) (Fin 3) ℂ} (hX : X.IsDiag) (hY : Y.IsDiag) : X * Y = Y * X := by
    rw [← hX.diagonal_diag, ← hY.diagonal_diag, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1; funext i; exact mul_comm _ _

  have diagonal_congruence_commute (A P Q : Matrix (Fin 3) (Fin 3) ℂ) (hA : IsUnit A)
      (hI : (A * Aᴴ).IsDiag)
      (hP : (A * P * Aᴴ).IsDiag) (hQ : (A * Q * Aᴴ).IsDiag) : P * Q = Q * P := by
    have hs : IsUnit Aᴴ := hA.star
    have hp : P * (Aᴴ * A) = (Aᴴ * A) * P := by
      apply hA.mul_left_cancel
      apply hs.mul_right_cancel
      simpa only [Matrix.mul_assoc] using diagonal_commute hP hI
    have hq : Q * (Aᴴ * A) = (Aᴴ * A) * Q := by
      apply hA.mul_left_cancel
      apply hs.mul_right_cancel
      simpa only [Matrix.mul_assoc] using diagonal_commute hQ hI
    have hpq : P * (Aᴴ * A) * Q = Q * (Aᴴ * A) * P := by
      apply hA.mul_left_cancel
      apply hs.mul_right_cancel
      simpa only [Matrix.mul_assoc] using diagonal_commute hP hQ
    apply (hs.mul hA).mul_left_cancel
    simpa only [hp, hq, Matrix.mul_assoc] using hpq

  have rho_noncommute : rho 0 * rho 1 ≠ rho 1 * rho 0 := by
    intro h
    have hc := congrArg (fun X : Matrix (Fin 3) (Fin 3) ℂ => X 0 1) h
    norm_num [rho, Matrix.mul_apply, Fin.sum_univ_succ] at hc

  have rho_sum : (∑ j, rho j) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [rho, Matrix.sum_apply, Fin.sum_univ_succ]

  have rho_trace (j : Fin 3) : Matrix.trace (rho j) = 1 := by
    fin_cases j <;> norm_num [rho, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

  have witness_unital : witness 1 = 1 := by
    simpa [witness] using rho_sum

  have witness_trace (X : Matrix (Fin 3) (Fin 3) ℂ) : Matrix.trace (witness X) = Matrix.trace X := by
    change Matrix.trace (∑ j, X j j • rho j) = Matrix.trace X
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, rho_trace, smul_eq_mul, mul_one]
    rfl

  have witness_single (j : Fin 3) : witness (Matrix.single j j 1) = rho j := by
    simp [witness, Matrix.single, Matrix.smul_apply]

  let lower (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
    ![1, !![(1:ℂ),0,0; 1/2,1,0; 0,0,1],
      !![(1:ℂ),0,0; -1/4,1,0; 0,0,1]] j
  let weights (j : Fin 3) : Fin 3 → ℂ :=
    ![![(1/2:ℂ),1/3,1/6], ![(1/6:ℂ),7/24,1/2], ![(1/3:ℂ),5/16,1/3]] j
  have rho_ldl (j : Fin 3) :
      rho j = lower j * Matrix.diagonal (weights j) * (lower j)ᴴ := by
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    ext a b
    fin_cases j <;> fin_cases a <;> fin_cases b <;>
      norm_num [rho, lower, weights, Matrix.mul_apply, Matrix.diagonal,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_two, Fin.isValue, map_ofNat, h02, h12]

  have rho_psd (j : Fin 3) : (rho j).PosSemidef := by
    rw [rho_ldl]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases j <;> fin_cases i <;> norm_num [weights, Complex.nonneg_iff]

  let liftColumn (j : Fin 3) : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
    fun p k => if p.2 = j then (1 : Matrix (Fin 3) (Fin 3) ℂ) p.1 k else 0

  have choi_witness : choi witness =
      ∑ j, liftColumn j * rho j * (liftColumn j)ᴴ := by
    ext ⟨a,b⟩ ⟨c,d⟩
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [choi, witness, liftColumn, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.conjTranspose_apply, Matrix.single, Matrix.one_apply,
      Finset.mul_sum, Finset.sum_mul, Matrix.smul_apply, apply_ite]
    split_ifs with hbd
    · subst d
      simp only [and_self]
      rw [Finset.sum_eq_single b]
      · simp
      · intro x _ hxb
        simp [Ne.symm hxb]
      · simp
    · have hn (j : Fin 3) : ¬(b = j ∧ d = j) := by
        rintro ⟨hb, hd⟩; exact hbd (hb.trans hd.symm)
      simp [hn]

  have witness_choi_psd : (choi witness).PosSemidef := by
    rw [choi_witness]
    apply Matrix.posSemidef_sum
    intro j _
    exact (rho_psd j).mul_mul_conjTranspose_same _
  obtain ⟨wK, hwK⟩ := choi_kraus witness witness_choi_psd
  have witness_cp : MatrixMap.IsCompletelyPositive witness := by
    rw [hwK]
    exact MatrixMap.of_kraus_isCompletelyPositive wK

  have witness_channel : UnitalChannel witness :=
    ⟨⟨witness_cp, witness_trace⟩, witness_unital⟩

  have cp_inverse_weighted_congruence (L G : MatrixMap (Fin 3) (Fin 3) ℂ) (hL : MatrixMap.IsCompletelyPositive L) (hG : MatrixMap.IsCompletelyPositive G)
      (hleft : ∀ X, G (L X) = X) :
      ∃ A : Matrix (Fin 3) (Fin 3) ℂ, IsUnit A ∧ ∃ lam : ℝ, 0 < lam ∧
        ∀ X, L X = (lam : ℂ) • (A * X * Aᴴ) := by
    classical
    obtain ⟨K, hK⟩ := cp_exists_kraus L hL
    obtain ⟨B, hB⟩ := cp_exists_kraus G hG
    have hk (X : Matrix (Fin 3) (Fin 3) ℂ) : L X = ∑ r, K r * X * (K r)ᴴ := by
      rw [hK]
      simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
    have hb (X : Matrix (Fin 3) (Fin 3) ℂ) : G X = ∑ r, B r * X * (B r)ᴴ := by
      rw [hB]
      simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
    let F : ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) → Matrix (Fin 3) (Fin 3) ℂ := fun p => B p.1 * K p.2
    have hf (X : Matrix (Fin 3) (Fin 3) ℂ) : (∑ p, F p * X * (F p)ᴴ) = X := by
      simpa only [F, Fintype.sum_prod_type, Matrix.conjTranspose_mul, Matrix.mul_sum,
        Matrix.sum_mul, Matrix.mul_assoc] using (show
          (∑ s, B s * (∑ r, K r * X * (K r)ᴴ) * (B s)ᴴ) = X by
            rw [← hk, ← hb]; exact hleft X)
    have hs (p) : F p = F p 0 0 • (1 : Matrix (Fin 3) (Fin 3) ℂ) := identity_kraus_scalar F hf 0 p
    have hex : ∃ p, F p 0 0 ≠ 0 := by
      by_contra h
      push Not at h
      have hz (p) : F p = 0 := by rw [hs p, h p, zero_smul]
      have hi := hf 1
      simp only [hz, Matrix.zero_mul, Finset.sum_const_zero] at hi
      have he := congrArg (fun X : Matrix (Fin 3) (Fin 3) ℂ => X 0 0) hi
      norm_num at he
    obtain ⟨⟨s₀,r₀⟩, hc⟩ := hex
    have hprod : IsUnit (B s₀ * K r₀) := by
      change IsUnit (F (s₀,r₀))
      rw [hs]
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ (Matrix (Fin 3) (Fin 3) ℂ))
    have hBu : IsUnit (B s₀) := isUnit_of_mul_isUnit_left hprod
    let A : Matrix (Fin 3) (Fin 3) ℂ := ↑(hBu.unit⁻¹)
    have hAu : IsUnit A := (hBu.unit⁻¹).isUnit
    have hBA : B s₀ * A = 1 := by
      dsimp [A]
      exact hBu.unit.mul_inv_of_eq hBu.unit_spec
    let c : (Fin 3 × Fin 3) → ℂ := fun r => F (s₀,r) 0 0
    have hkr (r) : K r = c r • A := by
      apply hBu.mul_left_cancel
      change F (s₀,r) = B s₀ * (c r • A)
      rw [hs, Matrix.mul_smul, hBA]
    let lam : ℝ := ∑ r, Complex.normSq (c r)
    have hlam : 0 < lam := by
      apply Finset.sum_pos'
      · intro r _; exact Complex.normSq_nonneg _
      · exact ⟨r₀, Finset.mem_univ _, Complex.normSq_pos.mpr hc⟩
    refine ⟨A, hAu, lam, hlam, ?_⟩
    intro X
    rw [hk]
    simp only [hkr, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    have hcoeff : (∑ r, star (c r) * c r) = (lam : ℂ) := by
      dsimp [lam]
      push_cast
      apply Finset.sum_congr rfl
      intro r _
      rw [Complex.normSq_eq_conj_mul_self]
    rw [← Finset.sum_smul, hcoeff]

  have cp_inverse_congruence (L G : MatrixMap (Fin 3) (Fin 3) ℂ) (hL : MatrixMap.IsCompletelyPositive L) (hG : MatrixMap.IsCompletelyPositive G)
      (hleft : ∀ X, G (L X) = X) :
      ∃ A : Matrix (Fin 3) (Fin 3) ℂ, IsUnit A ∧ ∀ X, L X = A * X * Aᴴ := by
    obtain ⟨A, hA, lam, hlam, he⟩ := cp_inverse_weighted_congruence L G hL hG hleft
    let r : ℂ := Real.sqrt lam
    have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hlam).ne'
    have hu : IsUnit (r • (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (isUnit_iff_ne_zero.mpr hr).map (algebraMap ℂ (Matrix (Fin 3) (Fin 3) ℂ))
    have hru : IsUnit (r • A) := by
      simpa only [Matrix.smul_mul, Matrix.one_mul] using hu.mul hA
    have hr2 : star r * r = (lam : ℂ) := by
      dsimp [r]
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hlam)]
    refine ⟨r • A, hru, ?_⟩
    intro X
    rw [he]
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hr2]

  have transpose_diagonal (X : Matrix (Fin 3) (Fin 3) ℂ) :
      ((MatrixMap.of_kraus (fun i => (wK i)ᵀ) (fun i => (wK i)ᵀ)) X).IsDiag := by
    change (∑ k, (wK k)ᵀ * X * (wK k).map star).IsDiag
    intro a b hab
    have hz : witness (Matrix.single a b 1) = 0 := by
      change (∑ j, (Matrix.single a b 1 : Matrix (Fin 3) (Fin 3) ℂ) j j • rho j) = 0
      apply Finset.sum_eq_zero
      intro j _
      have hn : ¬(a = j ∧ b = j) := by rintro ⟨ha, hb⟩; exact hab (ha.trans hb.symm)
      simp [Matrix.single, hn]
    have hc (i j : Fin 3) : (∑ k, wK k i a * star (wK k j b)) = 0 := by
      have he := congrArg (fun Z : Matrix (Fin 3) (Fin 3) ℂ => Z i j) hz
      rw [hwK] at he
      simpa [MatrixMap.of_kraus, LinearMap.sum_apply, Matrix.sum_apply,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
        Matrix.of_apply, ite_and] using he
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    calc
      _ = ∑ j, ∑ i, (∑ k, wK k i a * star (wK k j b)) * X i j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = 0 := by simp only [hc, zero_mul, Finset.sum_const_zero]

  have transpose_witness (X : Matrix (Fin 3) (Fin 3) ℂ) : (MatrixMap.of_kraus (fun i => (wK i)ᵀ) (fun i => (wK i)ᵀ)) X =
      Matrix.diagonal (fun j => Matrix.trace ((rho j)ᵀ * X)) := by
    ext a b
    by_cases hab : a = b
    · subst b
      rw [Matrix.diagonal_apply_eq]
      change (∑ k, ((wK k)ᵀ * X * (wK k).map star) a a) =
        Matrix.trace ((rho a)ᵀ * X)
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.map_apply]
      calc
        _ = ∑ i, ∑ j, (∑ k, wK k i a * star (wK k j a)) * X i j := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          calc
            _ = ∑ k, ∑ i, ∑ j,
                wK k i a * X i j * star (wK k j a) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_comm]
            _ = ∑ i, ∑ k, ∑ j,
                wK k i a * X i j * star (wK k j a) := Finset.sum_comm
            _ = ∑ i, ∑ j, ∑ k,
                wK k i a * X i j * star (wK k j a) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_comm]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ = ∑ i, ∑ j, witness (Matrix.single a a 1) i j * X i j := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          rw [hwK]
          simp [MatrixMap.of_kraus, LinearMap.sum_apply, Matrix.sum_apply,
            Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
            Matrix.of_apply, ite_and]
        _ = Matrix.trace ((rho a)ᵀ * X) := by
          rw [witness_single]
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
          exact Finset.sum_comm
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact transpose_diagonal X hab

  intro h
  obtain ⟨K, hK⟩ := cp_exists_kraus witness witness_cp
  obtain ⟨L, R, hL, hR, heq⟩ :=
    h witness witness_channel (Fin 3 × Fin 3) K hK
  rw [kraus_transpose_independent K wK (hK.symm.trans hwK)] at heq
  have he (X : Matrix (Fin 3) (Fin 3) ℂ) : (MatrixMap.of_kraus (fun i => (wK i)ᵀ) (fun i => (wK i)ᵀ)) X = L (witness (R X)) := by
    have hpoint := congrArg (fun T : MatrixMap (Fin 3) (Fin 3) ℂ => T X) heq
    simpa only [LinearMap.comp_apply] using hpoint
  obtain ⟨G, hG, hl, _⟩ := hL.2
  obtain ⟨A, hA, hLA⟩ := cp_inverse_congruence L G hL.1 hG hl
  obtain ⟨S, _, _, hrs⟩ := hR.2
  have hall (Y : Matrix (Fin 3) (Fin 3) ℂ) : (A * witness Y * Aᴴ).IsDiag := by
    have hd : ((MatrixMap.of_kraus (fun i => (wK i)ᵀ) (fun i => (wK i)ᵀ)) (S Y)).IsDiag := by
      rw [transpose_witness]
      exact Matrix.isDiag_diagonal _
    rw [he, hrs, hLA] at hd
    exact hd
  have hI : (A * Aᴴ).IsDiag := by
    simpa only [witness_unital, Matrix.mul_one] using hall 1
  have h0 : (A * rho 0 * Aᴴ).IsDiag := by
    simpa only [witness_single] using hall (Matrix.single 0 0 1)
  have h1 : (A * rho 1 * Aᴴ).IsDiag := by
    simpa only [witness_single] using hall (Matrix.single 1 1 1)
  exact rho_noncommute (diagonal_congruence_commute A (rho 0) (rho 1) hA hI h0 h1)

#print axioms result
end D5.S3.Quantum.QuantumChannels.CPFilterTransposeRefutation
