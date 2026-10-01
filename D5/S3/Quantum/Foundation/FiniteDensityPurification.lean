/- GID: D5/S3/Quantum/Foundation/FiniteDensityPurification
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FiniteDensityPurification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Purification witnesses for canonical finite density states. -/

/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo Soldati

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

/- Selected purification closure: QuantumInfo/ForMathlib/{IsMaximalSelfAdjoint,
HermitianMat/Basic,HermitianMat/Order,HermitianMat/Trace,Matrix}.lean and
QuantumInfo/States/{Pure/Braket,Mixed/MState}.lean at the immutable revision above.
Retire when equivalent statements exist in this repository pinned Mathlib,
currently db584cd6d46c92f209a44c0f1c829460d327499d. No upstream NOTICE was present
in the retained exact archive. -/
import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic
import D5.S3.Quantum.Information.PartialTraceMutualInformation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open BigOperators ComplexConjugate
open scoped Matrix ComplexOrder


-- Source: QuantumInfo/ForMathlib/IsMaximalSelfAdjoint.lean:27-47

class IsMaximalSelfAdjoint (R : outParam Type*) (α : Type*) [Star α] [Star R] [CommSemiring R]
    [Semiring α] [TrivialStar R] [Algebra R α] where
  /-- The additive map sending an element of `α` to its self-adjoint part in `R`. -/
  selfadjMap : α →+ R
  /-- `selfadjMap` pulls scalar multiplication by `R` out of its argument. -/
  selfadj_smul : ∀ (r : R) (a : α), selfadjMap (r • a) = r * (selfadjMap a)
  /-- On self-adjoint elements, `selfadjMap` is a section of `algebraMap R α`. -/
  selfadj_algebra : ∀ {a : α}, IsSelfAdjoint a → algebraMap _ _ (selfadjMap a) = a

/-- Every `TrivialStar` `CommSemiring` is its own maximal self adjoints. -/
instance instTrivialStarIsMaximalSelfAdjoint {R} [Star R] [TrivialStar R] [CommSemiring R] :
    IsMaximalSelfAdjoint R R where
  selfadjMap := AddMonoidHom.id R
  selfadj_smul _ __ := rfl
  selfadj_algebra {_} _ := rfl

/-- ℝ is the maximal self adjoint elements over RCLike -/
instance instRCLikeIsMaximalSelfAdjoint {α : Type*} [RCLike α] : IsMaximalSelfAdjoint ℝ α where
  selfadjMap := RCLike.re
  selfadj_smul := RCLike.smul_re
  selfadj_algebra := RCLike.conj_eq_iff_re.mp

namespace IsMaximalSelfAdjoint

-- Source: QuantumInfo/ForMathlib/IsMaximalSelfAdjoint.lean:60-62

@[simp]
theorem RCLike_selfadjMap {α : Type*} [RCLike α] : (selfadjMap : α →+ ℝ) = RCLike.re := by
  rfl

end IsMaximalSelfAdjoint

-- Source: QuantumInfo/ForMathlib/HermitianMat/Basic.lean:18-20

def HermitianMat (n : Type*) (α : Type*) [AddGroup α] [StarAddMonoid α] :=
  (selfAdjoint (Matrix n n α) : Type (max u_1 u_2))


namespace HermitianMat
variable {α 𝕜 : Type*} {n : Type*} [RCLike 𝕜]
section
variable [AddGroup α] [StarAddMonoid α]

-- Source: QuantumInfo/ForMathlib/HermitianMat/Basic.lean:34-45

@[coe] def mat : HermitianMat n α → Matrix n n α :=
  Subtype.val

instance : Coe (HermitianMat n α) (Matrix n n α) := ⟨mat⟩

@[simp]
theorem val_eq_coe (A : HermitianMat n α) : A.val = A := by
  rfl

@[simp]
theorem mat_mk (x : Matrix n n α) (h) : mat ⟨x, h⟩ = x := by
  rfl

-- Source: QuantumInfo/ForMathlib/HermitianMat/Basic.lean:53-65

theorem H (A : HermitianMat n α) : A.mat.IsHermitian :=
  A.2

@[ext] protected theorem ext {A B : HermitianMat n α} : A.mat = B.mat → A = B :=
  Subtype.ext

instance instFun : FunLike (HermitianMat n α) n (n → α) where
  coe M := (M : Matrix n n α)
  coe_injective _ _ h := HermitianMat.ext h

@[simp]
theorem mat_apply {A : HermitianMat n α} {i j : n} : A.mat i j = A i j := by
  rfl

-- Source: QuantumInfo/ForMathlib/HermitianMat/Basic.lean:72-74

instance : AddGroup (HermitianMat n α) :=
  AddSubgroup.toAddGroup _


end
variable [Fintype n] {A B : HermitianMat n 𝕜}

-- Source: QuantumInfo/ForMathlib/HermitianMat/Order.lean:23-27

open MatrixOrder in
/-- The `MatrixOrder` instance for Matrix (the Loewner order) we keep open for
HermitianMat, always. -/
instance : PartialOrder (HermitianMat n 𝕜) :=
  inferInstanceAs (PartialOrder (selfAdjoint _))

-- Source: QuantumInfo/ForMathlib/HermitianMat/Order.lean:33-39

omit [Fintype n] in
theorem le_iff : A ≤ B ↔ (B - A).mat.PosSemidef := by
  rfl

omit [Fintype n] in
theorem zero_le_iff : 0 ≤ A ↔ A.mat.PosSemidef := by
  rw [le_iff, sub_zero]

section
variable {R : Type*} [Star R] [TrivialStar R] [AddGroup α] [StarAddMonoid α] [CommSemiring R] [Semiring α] [Algebra R α] [IsMaximalSelfAdjoint R α]

-- Source: QuantumInfo/ForMathlib/HermitianMat/Trace.lean:39-40

def trace (A : HermitianMat n α) : R :=
  IsMaximalSelfAdjoint.selfadjMap (A.mat.trace)

end

-- Source: QuantumInfo/ForMathlib/HermitianMat/Trace.lean:120-121

theorem trace_eq_re_trace (A : HermitianMat n 𝕜) : A.trace = RCLike.re A.mat.trace := by
  rfl

-- Source: QuantumInfo/ForMathlib/HermitianMat/Trace.lean:128-132

@[simp]
theorem trace_eq_trace_rc (A : HermitianMat n 𝕜) : A.trace = A.mat.trace := by
  rw [trace, Matrix.trace, map_sum, RCLike.ofReal_sum]
  congr 1
  exact Matrix.IsHermitian.coe_re_diag A.H

end HermitianMat
namespace Matrix
variable {R d d₁ d₂ : Type*} [AddCommMonoid R] [Fintype d]

-- Source: QuantumInfo/ForMathlib/Matrix.lean:602-603

def traceRight (m : Matrix (d₁ × d) (d₂ × d) R) : Matrix d₁ d₂ R :=
  Matrix.of fun i₂ j₂ ↦ ∑ i₁, m (i₂, i₁) (j₂, i₁)

-- Source: QuantumInfo/ForMathlib/Matrix.lean:611-615

variable [Fintype d₁] [Fintype d₂] in
@[simp]
theorem traceRight_trace (A : Matrix (d₁ × d₂) (d₁ × d₂) R) : A.traceRight.trace = A.trace := by
  convert! (Fintype.sum_prod_type _).symm
  rfl

-- Source: QuantumInfo/ForMathlib/Matrix.lean:624-629

variable [StarAddMonoid R] in
theorem IsHermitian.traceRight {A : Matrix (d₁ × d) (d₁ × d) R} (hA : A.IsHermitian) : A.traceRight.IsHermitian := by
  ext
  simp only [Matrix.traceRight, conjTranspose_apply, of_apply, star_sum]
  congr!
  exact congrFun₂ hA _ _

end Matrix
namespace Matrix
variable {𝕜 d₁ d₂ : Type*} [RCLike 𝕜] [Fintype d₁] [Fintype d₂]
variable {A : Matrix (d₁ × d₂) (d₁ × d₂) 𝕜}

-- Source: QuantumInfo/ForMathlib/Matrix.lean:671-679

theorem PosSemidef.traceRight [DecidableEq d₂] (hA : A.PosSemidef) : A.traceRight.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hA ⊢
  constructor
  · exact hA.1.traceRight
  · intro x
    convert Finset.sum_nonneg' (s := .univ) (fun (i : d₂) ↦ hA.2 (fun (j,k) ↦ if i = k then x j else 0))
    simp_rw [Matrix.traceRight, dotProduct_mulVec]
    simpa [dotProduct, vecMul_eq_sum, ite_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
      apply_ite] using Finset.sum_comm_cycle

end Matrix
namespace Matrix
variable {n : Type*} [DecidableEq n]

-- Source: QuantumInfo/ForMathlib/Matrix.lean:1510-1514

theorem unitaryGroup_row_norm [Fintype n] (U : Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, ‖U j i‖^2 = 1 := by
  suffices ∑ j, ‖U j i‖^2 = (1 : ℂ) by exact_mod_cast this
  simpa [Matrix.mul_apply, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    using congr($(U.prop.left) i i)

end Matrix
namespace HermitianMat
variable {m n : Type*} [Fintype m] [Fintype n]

section
variable {α : Type*} [AddCommGroup α] [StarAddMonoid α]

-- Source: QuantumInfo/ForMathlib/HermitianMat/Trace.lean:170-171

def traceRight (A : HermitianMat (m × n) α) : HermitianMat m α :=
  ⟨A.mat.traceRight, A.H.traceRight⟩

variable (A : HermitianMat (m × n) α)

-- Source: QuantumInfo/ForMathlib/HermitianMat/Trace.lean:193-196

@[simp]
theorem traceRight_mat :
    (traceRight A).mat = A.mat.traceRight := by
  rfl

end
variable {𝕜 : Type*} [RCLike 𝕜] (A : HermitianMat (m × n) 𝕜)

-- Source: QuantumInfo/ForMathlib/HermitianMat/Trace.lean:230-232

@[simp]
theorem traceRight_trace : A.traceRight.trace = A.trace := by
  simp [trace_eq_re_trace]

end HermitianMat

-- Source: QuantumInfo/States/Pure/Braket.lean:45-138

section
variable (d : Type*) [Fintype d]

/-- A ket as a vector of unit norm. We follow the convention in `Matrix` of vectors as simple functions
 from a Fintype. Kets are distinctly not a vector space in our notion, as they represent only normalized
 states and so cannot (in general) be added or scaled. -/
structure Ket where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 = 1
  --TODO: change to `vec : EuclideanSpace ℂ d` / `normalized' : ‖vec‖ = 1`

/-- A bra is identical in definition to a `Ket`, but are separate to avoid complex conjugation confusion.
 They can be interconverted with the adjoint: `Ket.to_bra` and `Bra.to_ket` -/
structure Bra where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 =1

end section

namespace Braket

scoped notation:max "〈" ψ:90 "∣" => (ψ : Bra _)

scoped notation:max "∣" ψ:90 "〉" => (ψ : Ket _)

variable {d : Type*} [Fintype d]

instance instFunLikeKet : FunLike (Ket d) d ℂ where
  coe ψ := ψ.vec
  coe_injective _ _ h := by rwa [Ket.mk.injEq]

lemma _root_.Ket.coe_fun_eq (ψ : Ket d) : (ψ : d → ℂ) = ψ.vec := rfl

instance instFunLikeBra : FunLike (Bra d) d ℂ where
  coe ψ := ψ.vec
  coe_injective _ _ h := by rwa [Bra.mk.injEq]

lemma _root_.Bra.coe_fun_eq (ψ : Bra d) : (ψ : d → ℂ) = ψ.vec := rfl

end Braket

section braket
open Braket

variable {d : Type*} [Fintype d]

theorem Ket.apply (ψ : Ket d) (i : d) : ψ i = ψ.vec i :=
  rfl

theorem Bra.apply (ψ : Bra d) (i : d) : ψ i = ψ.vec i :=
  rfl

@[ext]
theorem Ket.ext {ξ ψ : Ket d} (h : ∀ x, ξ x = ψ x) : ξ = ψ :=
  DFunLike.ext ξ ψ h

@[ext]
theorem Bra.ext {ξ ψ : Bra d} (h : ∀ x, ξ x = ψ x) : ξ = ψ :=
  DFunLike.ext ξ ψ h

theorem Ket.normalized (ψ : Ket d) : ∑ x, Complex.normSq (ψ x) = 1 := by
  convert ψ.normalized'
  rw [Complex.normSq_eq_norm_sq]
  rfl

/-- Any Bra can be turned into a Ket by conjugating the elements. -/
@[coe]
def Ket.to_bra (ψ : Ket d) : Bra d :=
  ⟨conj ψ, by simp_all; exact ψ.2⟩

instance instBraOfKet : Coe (Ket d) (Bra d) := ⟨Ket.to_bra⟩


@[simp]
theorem Bra.eq_conj (ψ : Ket d) (x : d) :〈ψ∣ x = conj (∣ψ〉 x) :=
  rfl

end braket
open HermitianMat

-- Source: QuantumInfo/States/Mixed/MState.lean:62-73

@[ext]
structure MState (d : Type*) [Fintype d] [DecidableEq d] where
  M : HermitianMat d ℂ
  nonneg : 0 ≤ M
  tr : M.trace = 1

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]

variable (ψ φ : Ket d)
variable (ρ σ : MState d)

namespace MState

-- Source: QuantumInfo/States/Mixed/MState.lean:77-88

attribute [coe] MState.M
instance instCoe : Coe (MState d) (HermitianMat d ℂ) := ⟨MState.M⟩

attribute [simp] MState.tr

/-- The underlying `Matrix` in an MState. Prefer `MState.M` for the `HermitianMat`. -/
def m (ρ : MState d) : Matrix d d ℂ := ρ.M.mat

@[simp]
theorem mat_M : ρ.M.mat = ρ.m := by
  rfl


-- Source: QuantumInfo/States/Mixed/MState.lean:112-128

theorem psd : ρ.m.PosSemidef :=
  HermitianMat.zero_le_iff.mp ρ.nonneg


/-- Every mixed state is Hermitian. -/
theorem Hermitian : ρ.m.IsHermitian :=
  ρ.M.H

@[simp]
theorem tr' : ρ.m.trace = 1 := by
  rw [MState.m.eq_def, ← HermitianMat.trace_eq_trace_rc, ρ.tr]
  simp

theorem ext_m {ρ₁ ρ₂ : MState d} (h : ρ₁.m = ρ₂.m) : ρ₁ = ρ₂ := by
  rw [MState.mk.injEq]
  ext1
  exact h

-- Source: QuantumInfo/States/Mixed/MState.lean:267-279

set_option backward.isDefEq.respectTransparency false in
/-- A mixed state can be constructed as a pure state arising from a ket. -/
def pure (ψ : Ket d) : MState d where
  M := {
    val := Matrix.vecMulVec ψ (ψ : Bra d)
    property := (Matrix.posSemidef_vecMulVec_self_star ψ).1
  }
  nonneg := HermitianMat.zero_le_iff.mpr (Matrix.posSemidef_vecMulVec_self_star ψ)
  tr := by
    have h₁ (x) : ψ x * conj (ψ x) = Complex.normSq (ψ x) := by
      rw [mul_comm, Complex.normSq_eq_conj_mul_self]
    simp [HermitianMat.trace_eq_re_trace, Matrix.trace, Matrix.vecMulVec_apply, Bra.eq_conj, h₁]
    exact ψ.normalized

-- Source: QuantumInfo/States/Mixed/MState.lean:295-297

@[simp]
theorem pure_apply {i j : d} : (pure ψ).m i j = (ψ i) * conj (ψ j) := by
  rfl

-- Source: QuantumInfo/States/Mixed/MState.lean:586-591

@[simps]
def traceRight (ρ : MState (d₁ × d₂)) : MState d₁ where
  M := ρ.M.traceRight
  nonneg := zero_le_iff.mpr ρ.psd.traceRight
  tr := by simp [trace]


-- Source: QuantumInfo/States/Mixed/MState.lean:1003-1048

/-- The purification of a mixed state. Always uses the full dimension of the Hilbert space (d) to
 purify, so e.g. an existing pure state with d=4 still becomes d=16 in the purification. The defining
 property is `MState.traceRight_of_purify`; see also `MState.purify'` for the bundled version. -/
def purify (ρ : MState d) : Ket (d × d) where
  vec := fun (i,j) ↦
    let ρ2 := ρ.Hermitian.eigenvectorUnitary i j
    ρ2 * (ρ.Hermitian.eigenvalues j).sqrt
  normalized' := by
    have h₁ := fun i ↦ ρ.psd.eigenvalues_nonneg i
    simp only [Complex.norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, h₁, Real.sq_sqrt,
      Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_mul]
    have : ∀ x, ∑ i : d, ‖ρ.Hermitian.eigenvectorUnitary i x‖ ^ 2 = 1 :=
      Matrix.unitaryGroup_row_norm ρ.Hermitian.eigenvectorUnitary
    apply @RCLike.ofReal_injective ℂ
    simp_rw [this, one_mul, RCLike.ofReal_sum, ← Matrix.IsHermitian.trace_eq_sum_eigenvalues]
    exact ρ.tr'

/-- The defining property of purification, that tracing out the purifying system gives the
 original mixed state. -/
@[simp]
theorem purify_spec (ρ : MState d) : (pure ρ.purify).traceRight = ρ := by
  ext i j
  simp_rw [purify, traceRight, HermitianMat.traceRight, Matrix.traceRight]
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply, mat_M, pure_apply,
    mat_mk, Matrix.of_apply]
  simp only [Ket.apply]
  simp only [map_mul]
  simp_rw [mul_assoc, mul_comm, ← mul_assoc (Complex.ofReal _), Complex.mul_conj]
  -- By definition of eigenvectorUnitary and the properties of the unitary matrix and the eigenvalues, we can show that the matrix constructed from the purification is equal to ρ.
  have h_eigenvectorUnitary : ∀ i j, ∑ x, ρ.Hermitian.eigenvectorUnitary i x * ((ρ.Hermitian.eigenvalues x).sqrt ^ 2) * starRingEnd ℂ (ρ.Hermitian.eigenvectorUnitary j x) = ρ.M i j := by
    intro i j
    have h_eigenvectorUnitary : ρ.M = Matrix.of (fun i j => ∑ x, ρ.Hermitian.eigenvectorUnitary i x * ρ.Hermitian.eigenvalues x * starRingEnd ℂ (ρ.Hermitian.eigenvectorUnitary j x)) := by
      have := ρ.Hermitian.spectral_theorem;
      convert! this using 1;
      ext i j; simp [ Matrix.mul_apply, Matrix.diagonal ] ;
    replace h_eigenvectorUnitary := congr_fun ( congr_fun h_eigenvectorUnitary i ) j
    simp_all only [mat_apply, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.of_apply]
    congr! 2;
    norm_num [ Complex.ext_iff, sq ];
    exact Or.inl (Real.mul_self_sqrt (ρ.psd.eigenvalues_nonneg _))
  simp_all [ Complex.normSq, sq ];
  have h1 := h_eigenvectorUnitary i j
  convert! h1 using 1;
  simp [mul_assoc]

end MState

namespace D5.S3.Quantum.Foundation.FiniteDensityPurification
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped MatrixOrder CStarAlgebra
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
def toMState (ρ : DensityState a) : MState a := by
  have hp : (CStarMatrix.ofMatrix.symm ρ.1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)
  refine ⟨⟨CStarMatrix.ofMatrix.symm ρ.1, hp.1⟩,
    HermitianMat.zero_le_iff.mpr hp, ?_⟩
  change Complex.re (Matrix.trace ρ.1) = 1
  rw [ρ.2.2]
  rfl

def toDensity (ρ : MState a) : DensityState a :=
  ⟨CStarMatrix.ofMatrix ρ.m,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv ρ.psd.nonneg, ρ.tr'⟩

/-- Purification of a canonical density state, with exact canonical marginal and matrix. -/
def purification (ρ : DensityState a) :
    {ψ : Ket (a × a) //
      marginalRight (toDensity (MState.pure ψ)) = ρ ∧
      CStarMatrix.ofMatrix.symm (toDensity (MState.pure ψ)).1 =
        Matrix.vecMulVec ψ (fun i => star (ψ i))} := by
  refine ⟨(toMState ρ).purify, ?_, rfl⟩
  have transport (σ : MState (a × a)) :
      toDensity σ.traceRight = marginalRight (toDensity σ) := by
    apply Subtype.ext
    rfl
  rw [← transport, MState.purify_spec]
  apply Subtype.ext
  rfl
end D5.S3.Quantum.Foundation.FiniteDensityPurification
