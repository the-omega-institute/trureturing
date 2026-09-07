/- GID: D5/S3/Quantum/Foundation/FiniteKrausChannel
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FiniteKrausChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Kraus realizations as canonical completely positive trace-preserving channels. -/

/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Authors: Alex Meiburg

Modified file: the private PhyslibLeaf closure below is selected from
https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260
QuantumInfo/Channels/MatrixMap.lean and QuantumInfo/Channels/Unbundled.lean.
Changes: private namespace, local notation, explicit binders, selected imports.
The canonical CStarMatrix adapter following that closure is local work.
The pinned upstream tree has no NOTICE file. Full upstream license follows.

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

import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.Tactic

/- Exact-reuse audit: source intake precedes D5, pinned Mathlib and Physlib
   searches. The private closure retains the upstream Kraus CP and TP proofs
   under specification A17.2. Retire it when equivalent declarations enter
   this repository's pinned Mathlib. Its live consumer is
   FiniteShiftedRecordChannel.finite_shifted_record_channel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.FiniteKrausChannel

namespace PhyslibLeaf

private abbrev MatrixMap (A B R : Type*) [Semiring R] :=
  Matrix A A R →ₗ[R] Matrix B B R

namespace MatrixMap

variable {A B C D R : Type*} [Fintype A] [DecidableEq A]

section kraus
variable [Star R] [CommSemiring R] {κ : Type*} [Fintype κ]
private def of_kraus (M N : κ → Matrix B A R) : MatrixMap A B R :=
  ∑ k : κ, {
    toFun X := M k * X * (N k).conjTranspose
    map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
    map_smul' r x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
  }

end kraus

section kron
open Kronecker
variable [Fintype B] [Fintype C] [Fintype D] [DecidableEq C]
private noncomputable def kron [CommSemiring R] (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) : MatrixMap (A × C) (B × D) R :=
  let h₁ := (LinearMap.toMatrix (Module.Basis.tensorProduct  (Matrix.stdBasis R A A) (Matrix.stdBasis R C C))
      (Module.Basis.tensorProduct  (Matrix.stdBasis R B B) (Matrix.stdBasis R D D)))
    (TensorProduct.map M₁ M₂);
  let r₁ := Equiv.prodProdProdComm B B D D;
  let r₂ := Equiv.prodProdProdComm A A C C;
  let h₂ := Matrix.reindex r₁ r₂ h₁;
  Matrix.toLin (Matrix.stdBasis R (A × C) (A × C)) (Matrix.stdBasis R (B × D) (B × D)) h₂

local infixl:100 " ⊗ₖₘ " => kron

variable {b₁ b₂ : B} {d₁ d₂ : D}
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 60000 in
/-- The extensional definition of the Kronecker product `MatrixMap.kron`, in terms of the entries of
  its image. -/
private theorem kron_def [CommSemiring R] (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) (M : Matrix (A × C) (A × C) R) :
    (M₁ ⊗ₖₘ M₂) M (b₁, d₁) (b₂, d₂) = ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂,
      (M₁ (Matrix.single a₁ a₂ 1) b₁ b₂) * (M₂ (Matrix.single c₁ c₂ 1) d₁ d₂) * (M (a₁, c₁) (a₂, c₂)) := by
  rw [kron]
  have h_expand : (Matrix.toLin (Matrix.stdBasis R (A × C) (A × C)) (Matrix.stdBasis R (B × D) (B × D))) ((Matrix.reindex (Equiv.prodProdProdComm B B D D) (Equiv.prodProdProdComm A A C C)) ((LinearMap.toMatrix ((Matrix.stdBasis R A A).tensorProduct (Matrix.stdBasis R C C)) ((Matrix.stdBasis R B B).tensorProduct (Matrix.stdBasis R D D))) (TensorProduct.map M₁ M₂))) M = ∑ a₁ : A, ∑ a₂ : A, ∑ c₁ : C, ∑ c₂ : C, M (a₁, c₁) (a₂, c₂) • (Matrix.toLin (Matrix.stdBasis R (A × C) (A × C)) (Matrix.stdBasis R (B × D) (B × D))) ((Matrix.reindex (Equiv.prodProdProdComm B B D D) (Equiv.prodProdProdComm A A C C)) ((LinearMap.toMatrix ((Matrix.stdBasis R A A).tensorProduct (Matrix.stdBasis R C C)) ((Matrix.stdBasis R B B).tensorProduct (Matrix.stdBasis R D D))) (TensorProduct.map M₁ M₂))) (Matrix.single (a₁, c₁) (a₂, c₂) 1) := by
    have h_expand : M = ∑ a₁ : A, ∑ a₂ : A, ∑ c₁ : C, ∑ c₂ : C, M (a₁, c₁) (a₂, c₂) • Matrix.single (a₁, c₁) (a₂, c₂) 1 := by
      ext ⟨a₁, c₁⟩ ⟨a₂, c₂⟩
      simp only [Matrix.single, Matrix.sum_apply]
      rw [Finset.sum_eq_single a₁, Finset.sum_eq_single a₂, Finset.sum_eq_single c₁, Finset.sum_eq_single c₂]
      <;> simp +contextual
    nth_rw 1 [h_expand]
    simp only [map_sum, LinearMap.map_smulₛₗ]
    rfl
  rw [h_expand]
  clear h_expand
  simp only [Matrix.sum_apply]
  congr! 8 with a₁ _ a₂ _ c₁ _ c₂ _
  rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
  congr
  classical
  simp only [Matrix.stdBasis,
    Matrix.reindex_apply, Equiv.prodProdProdComm_symm, Matrix.toLin_apply,
    Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Equiv.prodProdProdComm_apply, LinearMap.toMatrix_apply,
    Module.Basis.tensorProduct_apply, Module.Basis.map_apply, Module.Basis.coe_reindex, Function.comp_apply,
    Equiv.sigmaEquivProd_symm_apply, Pi.basis_apply, Pi.basisFun_apply, Matrix.coe_ofLinearEquiv, TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, Matrix.coe_ofLinearEquiv_symm,
    Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply, Pi.basis_repr, Pi.basisFun_repr, Matrix.of_symm_apply, smul_eq_mul,
    Matrix.of_symm_single, Pi.single_apply, Matrix.smul_of, Matrix.sum_apply, Matrix.of_apply, Pi.smul_apply]
  rw [ Finset.sum_eq_single ( ( b₁, d₁ ), ( b₂, d₂ ) ) ]
  · rw [ Finset.sum_eq_single ( ( a₁, c₁ ), ( a₂, c₂ ) ) ]
    · simp only [↓reduceIte, Pi.single_eq_same, mul_one]
      rw [ mul_comm ]
      congr! 2
      · ext i j
        by_cases hi : i = a₁
        <;> by_cases hj : j = a₂
        <;> simp only [hi, hj, Matrix.of_apply, ne_eq, not_false_eq_true, Pi.single_eq_of_ne,
              Pi.single_eq_same, Pi.zero_apply, Matrix.single]
        <;> grind only
      · ext i j
        by_cases hi : i = c₁
        <;> by_cases hj : j = c₂
        <;> simp only [hi, hj, Matrix.of_apply, ne_eq, not_false_eq_true, Pi.single_eq_of_ne,
              Pi.single_eq_same, Pi.zero_apply, Matrix.single]
        <;> grind only
    · intros
      split
      · grind [Prod.mk.injEq, Pi.single_eq_of_ne, mul_zero]
      · simp
    · simp
  · simp only [Finset.mem_univ, ne_eq, forall_const, Prod.forall, Prod.mk.injEq, not_and, and_imp]
    intro a b c d h
    split_ifs
    · simp_all
    · simp
  · simp

variable [CommSemiring R]
private theorem add_kron (ML₁ ML₂ : MatrixMap A B R) (MR : MatrixMap C D R) : (ML₁ + ML₂) ⊗ₖₘ MR = ML₁ ⊗ₖₘ MR + ML₂ ⊗ₖₘ MR := by
  simp [kron, TensorProduct.map_add_left, Matrix.submatrix_add]

@[simp]
private theorem zero_kron (MR : MatrixMap C D R) : (0 : MatrixMap A B R) ⊗ₖₘ MR = 0 := by
  simp [kron]

end kron

local infixl:100 " ⊗ₖₘ " => kron

section tp
variable [Fintype B] {κ : Type*} [Fintype κ]
private def IsTracePreserving [Semiring R] (M : MatrixMap A B R) : Prop :=
  ∀ x, Matrix.trace (M x) = Matrix.trace x
namespace IsTracePreserving
variable {S : Type*} [CommSemiring S] [Star S]
/-- The channel X ↦ ∑ k : κ, (M k) * X * (N k)ᴴ formed by Kraus operators M, N : κ → Matrix B A R
is trace-preserving if ∑ k : κ, (N k)ᴴ * (M k) = 1 -/
private theorem of_kraus_isTracePreserving
  (M N : κ → Matrix B A S)
  (hTP : (∑ k, (N k).conjTranspose * (M k)) = 1) :
  (MatrixMap.of_kraus M N).IsTracePreserving := by
  intro x
  simp only [of_kraus, LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.trace_sum]
  conv =>
    enter [1,2,i]
    rw [Matrix.trace_mul_cycle (M i) x (N i).conjTranspose]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hTP, one_mul]
end IsTracePreserving
end tp

section cp
variable [Fintype B] [RCLike R]
open scoped ComplexOrder MatrixOrder
open Kronecker

/-- A linear matrix map is *positive* if it maps `PosSemidef` matrices to `PosSemidef`.-/
private def IsPositive (M : MatrixMap A B R) : Prop :=
  ∀⦃x⦄, x.PosSemidef → (M x).PosSemidef

/-- A linear matrix map is *completely positive* if, for any integer n, the tensor product
with `I(n)` is positive. -/
private def IsCompletelyPositive (M : MatrixMap A B R) : Prop :=
  ∀ (n : ℕ), (M ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n) (Fin n) R)).IsPositive

namespace IsCompletelyPositive
/-- Sums of IsCompletelyPositive maps are IsCompletelyPositive. -/
private theorem add {M₁ M₂ : MatrixMap A B R} (h₁ : M₁.IsCompletelyPositive) (h₂ : M₂.IsCompletelyPositive) :
    (M₁ + M₂).IsCompletelyPositive :=
  fun n _ h ↦ by
  simp only [add_kron, LinearMap.add_apply]
  exact Matrix.PosSemidef.add (h₁ n h) (h₂ n h)

variable (A B) in
/-- The zero map `IsCompletelyPositive`. -/
private theorem zero : (0 : MatrixMap A B R).IsCompletelyPositive :=
  fun _ _ _ ↦ by simpa using Matrix.PosSemidef.zero

/-- A finite sum of completely positive maps is completely positive. -/
private theorem finset_sum {ι : Type*} [Fintype ι] {m : ι → MatrixMap A B R} (hm : ∀ i, (m i).IsCompletelyPositive) :
    (∑ i, m i).IsCompletelyPositive :=
  Finset.sum_induction m _ (fun _ _ ↦ add) (.zero A B) (by simpa)
end IsCompletelyPositive

@[simps]
private def conj (y : Matrix B A R) : MatrixMap A B R where
  toFun x := y * x * y.conjTranspose
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The act of conjugating (not necessarily by a unitary, just by any matrix at all) is completely positive. -/
private theorem conj_isCompletelyPositive (M : Matrix B A R) : (conj M).IsCompletelyPositive := by
  --TODO: This is identical to congruence_CP
  intro n m h
  classical
  open ComplexOrder in
  open Kronecker in
  suffices ((M ⊗ₖ 1 : Matrix (B × Fin n) (A × Fin n) R) * m * (M.conjTranspose ⊗ₖ 1)).PosSemidef by
    convert this
    --TODO cleanup. Thanks Aristotle
    ext ⟨ b₁, c₁ ⟩ ⟨ b₂, c₂ ⟩
    rw [ MatrixMap.kron_def ];
    simp [Matrix.mul_apply, Matrix.single];
    have h_split : ∑ x, ∑ x_1, ∑ x_2, ∑ x_3, (if x_2 = c₁ ∧ x_3 = c₂ then (∑ x_4, (∑ x_5, if x = x_5 ∧ x_1 = x_4 then M b₁ x_5 else 0) * (starRingEnd R) (M b₂ x_4)) * m (x, x_2) (x_1, x_3) else 0) = ∑ x, ∑ x_1, (∑ x_4, (∑ x_5, if x = x_5 ∧ x_1 = x_4 then M b₁ x_5 else 0) * (starRingEnd R) (M b₂ x_4)) * m (x, c₁) (x_1, c₂) := by
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      rw [ Finset.sum_eq_single c₁ ]
      · simp_all only [Finset.mem_univ, true_and, Finset.sum_ite_eq', ↓reduceIte]
      · intro b a a_1
        simp_all only [Finset.mem_univ, ne_eq, false_and, ↓reduceIte, Finset.sum_const_zero]
      · intro a
        simp_all only [Finset.mem_univ, not_true_eq_false]
    convert h_split using 1;
    rw [ Matrix.mul_assoc ];
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
      RCLike.star_def, Finset.mul_sum _ _ _, Finset.sum_mul, ite_mul, zero_mul];
    simp [ Matrix.one_apply, Finset.sum_ite, Finset.filter_eq, Finset.filter_and ];
    have h_reindex : ∑ x ∈ {x | c₁ = x.2}, ∑ x_1 ∈ {x | x.2 = c₂}, M b₁ x.1 * (m x x_1 * (starRingEnd R) (M b₂ x_1.1)) = ∑ x ∈ Finset.univ, ∑ x_1 ∈ Finset.univ, M b₁ x * (m (x, c₁) (x_1, c₂) * (starRingEnd R) (M b₂ x_1)) := by
      rw [ show ( Finset.univ.filter fun x : A × Fin n => c₁ = x.2 ) = Finset.image ( fun x : A => ( x, c₁ ) ) Finset.univ from ?_, show ( Finset.univ.filter fun x : A × Fin n => x.2 = c₂ ) = Finset.image ( fun x : A => ( x, c₂ ) ) Finset.univ from ?_ ];
      · simp [Finset.sum_image, Set.InjOn]
      · ext ⟨ x, y ⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq,
          exists_eq_left]
        exact eq_comm;
      · ext ⟨ x, y ⟩
        simp [ eq_comm ];
    have h_inner : ∀ x x_1, ∑ x_2, ∑ x_3 ∈ {x} ∩ if x_1 = x_2 then Finset.univ else ∅, M b₁ x_3 * (starRingEnd R) (M b₂ x_2) * m (x, c₁) (x_1, c₂) = M b₁ x * (starRingEnd R) (M b₂ x_1) * m (x, c₁) (x_1, c₂) := by
      intro x x_1
      rw [ Finset.sum_eq_single x_1 ] <;> simp +contextual;
      simp +contextual [ eq_comm ];
    simp only [ h_inner ];
    simpa only [ mul_assoc, mul_comm, mul_left_comm ] using h_reindex
  obtain ⟨m', rfl⟩ : ∃ B, m = B.conjTranspose * B := by
    classical
    apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    exact Matrix.nonneg_iff_posSemidef.mpr h
  convert Matrix.posSemidef_conjTranspose_mul_self (m' * (M ⊗ₖ 1 : Matrix (B × Fin n) (A × Fin n) R).conjTranspose) using 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  congr
  ext
  simp +contextual only [Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    Matrix.one_apply, apply_ite, mul_one, mul_zero, star_zero, ↓reduceIte, ite_eq_right_iff,
    map_eq_zero, if_true_left]
  tauto

variable {κ : Type*} [Fintype κ]
private theorem of_kraus_isCompletelyPositive (M : κ → Matrix B A R) :
    (of_kraus M M).IsCompletelyPositive := by
  rw [of_kraus]
  exact IsCompletelyPositive.finset_sum (fun i ↦ conj_isCompletelyPositive (M i))
end cp
end MatrixMap
end PhyslibLeaf

open scoped CStarAlgebra ComplexOrder MatrixOrder

private def flattenCStar {a : Type*} [Fintype a] [DecidableEq a] (k : ℕ) :
    CStarMatrix (Fin k) (Fin k) (CStarMatrix a a ℂ) ≃⋆ₐ[ℂ]
      CStarMatrix (a × Fin k) (a × Fin k) ℂ where
  toFun X := CStarMatrix.ofMatrix fun p q => X p.2 q.2 p.1 q.1
  invFun X := CStarMatrix.ofMatrix fun r s =>
    CStarMatrix.ofMatrix fun i j => X (i, r) (j, s)
  left_inv X := rfl
  right_inv X := rfl
  map_add' X Y := rfl
  map_smul' z X := rfl
  map_star' X := rfl
  map_mul' X Y := by
    apply CStarMatrix.ext
    intro ⟨i, r⟩ ⟨j, s⟩
    change (∑ t : Fin k, (CStarMatrix.ofMatrix.symm (X r t) *
      CStarMatrix.ofMatrix.symm (Y t s))) i j =
      ∑ p : a × Fin k, X r p.2 i p.1 * Y p.2 s p.1 j
    simp only [Matrix.sum_apply, Matrix.mul_apply, CStarMatrix.ofMatrix_symm_apply,
      Fintype.sum_prod_type]
    exact Finset.sum_comm

private theorem flatten_intertwines
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (f : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ) (k : ℕ)
    (X : CStarMatrix (Fin k) (Fin k) (CStarMatrix a a ℂ)) :
    flattenCStar k (X.map (fun rho =>
      CStarMatrix.ofMatrix (f (CStarMatrix.ofMatrix.symm rho)))) =
    CStarMatrix.ofMatrix (PhyslibLeaf.MatrixMap.kron f LinearMap.id
      (CStarMatrix.ofMatrix.symm (flattenCStar k X))) := by
  have linear_expansion (M : Matrix a a ℂ) :
      f M = ∑ i, ∑ j, M i j • f (Matrix.single i j 1) := by
    have expand : M = ∑ i, ∑ j, M i j • Matrix.single i j 1 := by
      ext i j
      simp [Matrix.single, Matrix.sum_apply, ite_and]
    conv_lhs => rw [expand]
    simp only [map_sum, map_smul]
  apply CStarMatrix.ext
  intro ⟨i, r⟩ ⟨j, s⟩
  change f (CStarMatrix.ofMatrix.symm (X r s)) i j =
    PhyslibLeaf.MatrixMap.kron f LinearMap.id
      (CStarMatrix.ofMatrix.symm (flattenCStar k X)) (i, r) (j, s)
  rw [linear_expansion, PhyslibLeaf.MatrixMap.kron_def]
  simp [Matrix.sum_apply, Matrix.single, flattenCStar, mul_comm, ite_and]
  rfl

private def canonicalCPOfPhyslib
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (f : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ)
    (hf : PhyslibLeaf.MatrixMap.IsCompletelyPositive f) :
    CompletelyPositiveMap (CStarMatrix a a ℂ) (CStarMatrix b b ℂ) where
  toLinearMap := CStarMatrix.ofMatrixₗ.toLinearMap.comp
    (f.comp CStarMatrix.ofMatrixₗ.symm.toLinearMap)
  map_cstarMatrix_nonneg' k X hX := by
    have hflat : 0 ≤ CStarMatrix.ofMatrix.symm (flattenCStar k X) :=
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
        (map_nonneg (flattenCStar k) hX)
    have hpositive := hf k (Matrix.nonneg_iff_posSemidef.mp hflat)
    have hout : 0 ≤ CStarMatrix.ofMatrix (PhyslibLeaf.MatrixMap.kron f LinearMap.id
        (CStarMatrix.ofMatrix.symm (flattenCStar k X))) :=
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hpositive.nonneg
    rw [← flatten_intertwines] at hout
    exact map_nonneg (flattenCStar k).symm hout

/-- A complete finite Kraus family gives a channel in the canonical all-amplification
interface, with its matrix action equal to the actual Kraus sum. -/
theorem finite_kraus_quantum_channel
    {a b κ : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype κ]
    (K : κ → Matrix b a ℂ)
    (hK : (∑ r, (K r).conjTranspose * K r) = 1) :
    ∃ channel : D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel a b,
      ∀ rho : Matrix a a ℂ,
        CStarMatrix.ofMatrix.symm
          (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
        ∑ r, K r * rho * (K r).conjTranspose := by
  let f := PhyslibLeaf.MatrixMap.of_kraus K K
  let channel : D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel a b :=
    { toCompletelyPositiveMap := canonicalCPOfPhyslib f
        (PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive K)
      trace_preserving := fun rho =>
        PhyslibLeaf.MatrixMap.IsTracePreserving.of_kraus_isTracePreserving K K hK
          (CStarMatrix.ofMatrix.symm rho) }
  refine ⟨channel, ?_⟩
  intro rho
  change PhyslibLeaf.MatrixMap.of_kraus K K rho = _
  simp only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk]

#print axioms finite_kraus_quantum_channel

end D5.S3.Quantum.Foundation.FiniteKrausChannel
