/- GID: D5/S3/Quantum/Foundation/FiniteKrausRepresentation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FiniteKrausRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangular Kraus witnesses for canonical completely positive maps. -/

/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Authors: Alex Meiburg

Selected-source port from
https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260
Source families and retirement conditions are specified below.
Changes: selected declarations, local namespaces and notation, current imports,
and canonical witness constructions. Original selected proof bodies are retained;
rank-one positivity uses the equivalent pinned Mathlib theorem.
The retained pinned upstream tree has no NOTICE file. Full upstream license follows.

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

/- Selected additional Choi/Kraus declarations from QuantumInfo/Channels/Unbundled.lean
at revision 6a09b2d1761a0d4430083045a247eb121d8da260. Existing MatrixMap, kron,
CP predicates and amplification transport are reused from their original owner.
Retire the selected declarations when equivalent declarations exist in this
repository pinned Mathlib (currently db584cd6d46c92f209a44c0f1c829460d327499d).
The rank-one positivity step uses pinned Mathlib directly. -/
import D5.S3.Quantum.Foundation.FiniteKrausChannel

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace D5.S3.Quantum.Foundation.FiniteKrausChannel
namespace PhyslibLeaf
namespace MatrixMap
variable {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [RCLike R]
open scoped MatrixOrder ComplexOrder
local infixl:100 " ⊗ₖₘ " => kron
section


variable (A R) in
/-- Alias of LinearMap.id, but specifically as a MatrixMap. -/
@[reducible]
def id : MatrixMap A A R := LinearMap.id

/-- Choi matrix of a given linear matrix map. Note that this is defined even for things that
  aren't CPTP, it's just rarely talked about in those contexts. This is the inverse of
  `MatrixMap.of_choi_matrix`. Compare with `MatrixMap.toMatrix`, which gives the transfer matrix. -/
def choi_matrix (M : MatrixMap A B R) : Matrix (B × A) (B × A) R :=
  fun (j₁,i₁) (j₂,i₂) ↦ M (Matrix.single i₁ i₂ 1) j₁ j₂

set_option backward.isDefEq.respectTransparency false in
/-- Given the Choi matrix, generate the corresponding R-linear map between matrices as a
MatrixMap. This is the inverse of `MatrixMap.choi_matrix`. -/
def of_choi_matrix (M : Matrix (B × A) (B × A) R) : MatrixMap A B R where
  toFun X := fun b₁ b₂ ↦ ∑ (a₁ : A), ∑ (a₂ : A), X a₁ a₂ * M (b₁, a₁) (b₂, a₂)
  map_add' x y := by funext b₁ b₂; simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    funext b₁ b₂
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Proves that `MatrixMap.choi_matrix` and `MatrixMap.of_choi_matrix` inverses. -/
@[simp]
theorem choi_map_inv (M : MatrixMap A B R) : of_choi_matrix (choi_matrix M) = M := by
  -- By definition of `MatrixMap.of_choi_matrix`, we know that applying it to the Choi matrix of `M`
  -- reconstructs `M`.
  ext X b₁ b₂; simp [MatrixMap.of_choi_matrix, MatrixMap.choi_matrix];
  -- By linearity of $M$, we can distribute $M$ over the sum.
  have h_linear : M X = ∑ x : A, ∑ x_1 : A, X x x_1 • M (Matrix.single x x_1 1) := by
    have h_linear : M X = M (∑ x : A, ∑ x_1 : A, X x x_1 • Matrix.single x x_1 1) := by
      congr with i j ; simp ( config := { decide := Bool.true } ) [ Matrix.sum_apply ];
      simp ( config := { decide := Bool.true } ) [ Matrix.single ];
      rw [ Finset.sum_eq_single i ] <;> aesop;
    simp +decide only [h_linear, map_sum, LinearMap.map_smulₛₗ];
    simp +zetaDelta at *;
  -- By linearity of $M$, we can distribute $M$ over the sum and then apply it to each term.
  simp [h_linear, Matrix.sum_apply]

/-- The correspondence induced by `MatrixMap.of_choi_matrix` is injective. -/
theorem choi_matrix_inj : Function.Injective (@choi_matrix A B R _ _) := by
  intro _ _ h
  simpa only [choi_map_inv] using congrArg of_choi_matrix h

end
section
variable (R)


/-- The `MatrixMap` corresponding to applying a `submatrix` operation on each side. -/
@[simps]
def submatrix (f : B → A) : MatrixMap A B R where
  toFun x := x.submatrix f f
  map_add' := by simp [Matrix.submatrix_add]
  map_smul' := by simp [Matrix.submatrix_smul]


end
namespace IsCompletelyPositive

theorem of_Fintype  {M : MatrixMap A B R} (h : IsCompletelyPositive M)
    (T : Type*) [Fintype T] [DecidableEq T] :
    (M.kron (LinearMap.id : MatrixMap T T R)).IsPositive := by
  obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty (T ≃ Fin n) :=
    Finite.exists_equiv_fin T
  convert h n using 1
  have h_submatrix : (M ⊗ₖₘ (LinearMap.id : MatrixMap T T R)) = (MatrixMap.submatrix R (fun p : B × T => (p.1, e p.2)) ∘ₗ (M ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n) (Fin n) R)) ∘ₗ MatrixMap.submatrix R (fun p : A × Fin n => (p.1, e.symm p.2))) := by
    ext
    simp only [submatrix, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Matrix.submatrix_apply]
    rw [MatrixMap.kron_def, MatrixMap.kron_def]
    simp only [Matrix.single, LinearMap.id_coe, id_eq, Matrix.of_apply, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Matrix.submatrix];
    congr! 4
    rw [← Equiv.sum_comp e]
    congr! 2
    rw [← Equiv.sum_comp e]
    simp only [EmbeddingLike.apply_eq_iff_eq, Equiv.symm_apply_apply]
  constructor
  · intro h₂
    simp [MatrixMap.IsPositive]
    exact h n
  · intro h x hx
    specialize h (hx.submatrix (fun p : A × Fin n => (p.1, e.symm p.2)))
    rw [h_submatrix]
    simp only [LinearMap.coe_comp, Function.comp_apply, submatrix_apply]
    exact h.submatrix _

end IsCompletelyPositive
variable {κ 𝕜 : Type*} [Fintype κ] [RCLike 𝕜]

omit [Fintype B] in
theorem choi_of_kraus (K : κ → Matrix B A 𝕜) :
    (MatrixMap.of_kraus K K).choi_matrix = ∑ k, Matrix.vecMulVec (fun (x : B × A) => K k x.1 x.2) (fun (x : B × A) => star (K k x.1 x.2)) := by
  -- By definition of Choi matrix, we can expand the left-hand side using the linearity of the map and the properties of the Choi matrix.
  ext ⟨b₁, a₁⟩ ⟨b₂, a₂⟩
  simp [MatrixMap.choi_matrix, MatrixMap.of_kraus];
  -- By definition of the sum, the entry (b₁, b₂) of the sum of the Choi matrices of each Kraus operator is the sum of the entries (b₁, b₂) of each individual Choi matrix.
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.single];
  -- Since the inner sum over `x_2` will only contribute when `x_2 = a₁` and `x_1 = a₂`, we can simplify the expression.
  have h_inner : ∀ x : κ, ∑ x_1 : A, (∑ x_2 : A, if a₁ = x_2 ∧ a₂ = x_1 then K x b₁ x_2 else 0) * (starRingEnd 𝕜) (K x b₂ x_1) = (K x b₁ a₁) * (starRingEnd 𝕜) (K x b₂ a₂) := by
    simp [ Finset.sum_ite, Finset.filter_eq, Finset.filter_and ];
    intro x; rw [ Finset.sum_eq_single a₂ ] <;> aesop;
  exact Finset.sum_congr rfl fun _ _ => h_inner _


set_option backward.isDefEq.respectTransparency false in
theorem exists_kraus_of_choi_PSD
    (C : Matrix (B × A) (B × A) 𝕜) (hC : C.PosSemidef) :
    ∃ (K : (B × A) → Matrix B A 𝕜), C = (MatrixMap.of_kraus K K).choi_matrix := by
  classical
  use fun k i j => ( hC.1.eigenvectorUnitary.val : Matrix _ _ 𝕜 ) (i, j) k * ( hC.1.eigenvalues k |> RCLike.ofReal |> Real.sqrt)
  convert Matrix.IsHermitian.spectral_theorem hC.1 using 1;
  ext i j
  simp [choi_of_kraus, Matrix.mul_apply, Matrix.vecMulVec ]
  ring_nf
  simp [ Matrix.sum_apply, Matrix.diagonal ];
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [ ← RCLike.ofReal_pow, Real.sq_sqrt ( hC.eigenvalues_nonneg _ ) ]

/-
The Choi matrix of M is the image of the unnormalized maximally entangled state projector under M ⊗ id.
-/
theorem choi_matrix_eq_map_proj (M : MatrixMap A B R) :
    M.choi_matrix = (M ⊗ₖₘ MatrixMap.id A R) (Matrix.vecMulVec (fun (x : A × A) => if x.1 = x.2 then 1 else 0) (fun (x : A × A) => star (if x.1 = x.2 then 1 else 0))) := by
  have h_choi : ∀ (M : MatrixMap A B R), MatrixMap.kron M (MatrixMap.id A R) (Matrix.vecMulVec (fun (x : A × A) => if x.1 = x.2 then 1 else 0) (fun (x : A × A) => star (if x.1 = x.2 then 1 else 0))) = MatrixMap.choi_matrix M := by
    intro M
    ext ⟨b₁, d₁⟩ ⟨b₂, d₂⟩
    simp [MatrixMap.kron_def, MatrixMap.choi_matrix];
    simp +decide [ Matrix.single, Matrix.vecMulVec ];
    rw [ Finset.sum_eq_single d₁ ] <;> aesop;
  convert h_choi M |> Eq.symm

/-- Choi's theorem on completely positive maps: A map `IsCompletelyPositive` iff its Choi Matrix is PSD. -/
theorem choi_PSD_iff_CP_map (M : MatrixMap A B R) :
    M.IsCompletelyPositive ↔ M.choi_matrix.PosSemidef := by
  constructor
  · intro hcp
    have := MatrixMap.IsCompletelyPositive.of_Fintype hcp A
    rw [ MatrixMap.choi_matrix_eq_map_proj ] at *;
    exact this ( Matrix.posSemidef_vecMulVec_self_star _ )
  · intro h_psd
    obtain ⟨K, hK⟩ := exists_kraus_of_choi_PSD M.choi_matrix h_psd
    rw [choi_matrix_inj hK]
    exact of_kraus_isCompletelyPositive K

theorem IsCompletelyPositive.exists_kraus (Φ : MatrixMap A B R) (hCP : Φ.IsCompletelyPositive) :
    ∃ (M : (B × A) → Matrix B A R), Φ = of_kraus M M := by
  rw [choi_PSD_iff_CP_map] at hCP
  convert exists_kraus_of_choi_PSD Φ.choi_matrix hCP using 1;
  funext
  rw [eq_iff_iff, iff_comm]
  exact MatrixMap.choi_matrix_inj.eq_iff

end MatrixMap
end PhyslibLeaf
open scoped CStarAlgebra ComplexOrder MatrixOrder

/-- A finite rectangular Kraus representation of the canonical CP map, with its all-matrix action. -/
def krausRepresentation
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Φ : CompletelyPositiveMap (CStarMatrix a a ℂ) (CStarMatrix b b ℂ)) :
    {K : (b × a) → Matrix b a ℂ // ∀ M : Matrix a a ℂ,
      CStarMatrix.ofMatrix.symm (Φ (CStarMatrix.ofMatrix M)) =
        ∑ r, K r * M * (K r).conjTranspose} := by
  let matrixOfCanonical : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ :=
    CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      (Φ.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
  have cp : PhyslibLeaf.MatrixMap.IsCompletelyPositive matrixOfCanonical := by
    intro k M hM
    let X := (flattenCStar (a := a) k).symm (CStarMatrix.ofMatrix M)
    have hX : 0 ≤ X := map_nonneg (flattenCStar (a := a) k).symm
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hM.nonneg)
    have hY := Φ.map_cstarMatrix_nonneg X hX
    have hflat := map_nonneg (flattenCStar (a := b) k) hY
    have heq := flatten_intertwines matrixOfCanonical k X
    simp only [X, StarAlgEquiv.apply_symm_apply, Equiv.symm_apply_apply] at heq
    have hout : 0 ≤ CStarMatrix.ofMatrix
        (PhyslibLeaf.MatrixMap.kron matrixOfCanonical LinearMap.id M) := by
      rw [← heq]
      exact hflat
    exact Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hout)
  let witness := PhyslibLeaf.MatrixMap.IsCompletelyPositive.exists_kraus matrixOfCanonical cp
  let K := Classical.choose witness
  have hK := Classical.choose_spec witness
  refine ⟨K, fun M => ?_⟩
  change matrixOfCanonical M = _
  rw [hK]
  simp only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  rfl

end D5.S3.Quantum.Foundation.FiniteKrausChannel
