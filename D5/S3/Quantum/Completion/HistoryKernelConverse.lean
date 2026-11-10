/- GID: D5/S3/Quantum/Completion/HistoryKernelConverse
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/HistoryKernelConverse
   mirror-E: none(waiver:universal-kernel-certification)
   anchors: []
   utility: none
   digest: Singular extensions and finite-cover certification of a fixed history kernel. -/

import D5.S3.Quantum.Completion.HistoryKernelExtension
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Matrix.ColumnRowPartitioned

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The following supplier proofs are adapted from TauCetiProject/TauCeti,
revision 52f9d081237dadaf6d4eae13629281f7faa37d54,
TauCeti/LinearAlgebra/Matrix/PosSemidef.lean and
TauCeti/Analysis/Matrix/PosSemidef/Block.lean.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The Tau Ceti contributors.
Adaptations: complex scalar specialization, local private names, and removal of unused suppliers.
Retire these suppliers when the pinned Mathlib contains equivalent block range constraints. -/
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

namespace D5.S3.Quantum.Completion.HistoryKernelConverse
namespace Suppliers
variable {ι κ : Type*} {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ}
private theorem nullBlock [Fintype ι] [Fintype κ] (hS : S.PosSemidef)
    {x : κ → ℂ} (hx : S.toBlocks₂₂ *ᵥ x = 0) : S.toBlocks₁₂ *ᵥ x = 0 := by
  have hq : star (Sum.elim 0 x) ⬝ᵥ S *ᵥ Sum.elim 0 x = 0 := by
    rw [← fromBlocks_toBlocks S, fromBlocks_mulVec, dotProduct_block]
    simp [Function.star_sumElim, hx]
  have hz := hS.dotProduct_mulVec_zero_iff.mp hq
  rw [← fromBlocks_toBlocks S, fromBlocks_mulVec] at hz
  simpa using congrArg (fun v => v ∘ Sum.inl) hz
private theorem kerBlock [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hS : S.PosSemidef) :
    LinearMap.ker S.toBlocks₂₂.toEuclideanLin ≤ LinearMap.ker S.toBlocks₁₂.toEuclideanLin := by
  intro x hx
  simp only [LinearMap.mem_ker, toEuclideanLin, toLpLin_apply, WithLp.toLp_eq_zero] at hx ⊢
  exact nullBlock hS hx
private theorem rangeBlock₂₁ [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hS : S.PosSemidef) :
    LinearMap.range S.toBlocks₂₁.toEuclideanLin ≤ LinearMap.range S.toBlocks₂₂.toEuclideanLin := by
  have hD : S.toBlocks₂₂.IsHermitian := hS.isHermitian.submatrix Sum.inr
  have hB : S.toBlocks₁₂ᴴ = S.toBlocks₂₁ := by
    ext i j
    exact hS.isHermitian.apply _ _
  simpa only [LinearMap.orthogonal_ker, ← toEuclideanLin_conjTranspose_eq_adjoint,
    hD.eq, hB] using Submodule.orthogonal_le (kerBlock hS)
private theorem rangeBlock₁₂ [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hS : S.PosSemidef) :
    LinearMap.range S.toBlocks₁₂.toEuclideanLin ≤ LinearMap.range S.toBlocks₁₁.toEuclideanLin := by
  have h := rangeBlock₂₁ (hS.submatrix Sum.swap)
  rw [← fromBlocks_toBlocks S, fromBlocks_submatrix_sum_swap_sum_swap,
    toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂] at h
  exact h
-- Adapted from the private support supplier in the same pinned Tau Ceti source.
private theorem ofSupport {X : Type*} (K : X → X → ℂ)
    (hHerm : (Matrix.of K).IsHermitian) (hgram : ∀ x : X →₀ ℂ,
      (Matrix.of fun i j : x.support => K (i : X) (j : X)).PosSemidef) :
    (Matrix.of K).PosSemidef := by
  classical
  refine ⟨hHerm, fun x => ?_⟩
  let y : x.support → ℂ := fun i => x i
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hgram x)).2 y
  have h' : 0 ≤ ∑ i : x.support, ∑ j : x.support,
      star (x (i : X)) * (K (i : X) (j : X) * x (j : X)) := by
    simpa only [y, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
      Finset.mul_sum, mul_assoc] using h
  have h'' : 0 ≤ ∑ i ∈ x.support, ∑ j ∈ x.support,
      star (x i) * (K i j * x j) := by
    convert h' using 1
    rw [Finset.sum_subtype x.support (by intro a; rfl)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_subtype x.support (by intro a; rfl)]
  simpa only [Matrix.of_apply, Finsupp.sum, mul_assoc] using h''

end Suppliers

open D5.S3.Quantum.Completion.HistoryKernelExtension
private theorem blockResidual {I : Type*} [Fintype I]
    (M : Matrix (I ⊕ Unit) (I ⊕ Unit) ℂ) (hM : M.PosSemidef) :
    ∃ (c : Matrix I Unit ℂ) (r : ℂ), M = residualExtension M.toBlocks₁₁ c r := by
  classical
  let b : EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => M (Sum.inl i) (Sum.inr ()))
  have hb : b ∈ LinearMap.range M.toBlocks₁₂.toEuclideanLin := by
    refine ⟨WithLp.toLp 2 (fun _ : Unit => (1 : ℂ)), ?_⟩
    ext i
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, b, Matrix.toBlocks₁₂]
  obtain ⟨v, hv⟩ := Suppliers.rangeBlock₁₂ hM hb
  let c : Matrix I Unit ℂ := fun i _ => v i
  have hc : M.toBlocks₁₂ = M.toBlocks₁₁ * c := by
    ext i j
    have hi := congrArg (fun w : EuclideanSpace ℂ I => w i) hv
    cases j
    change M (Sum.inl i) (Sum.inr ()) = ∑ k, M.toBlocks₁₁ i k * v k
    change (∑ k, M.toBlocks₁₁ i k * v k) = M (Sum.inl i) (Sum.inr ()) at hi
    exact hi.symm
  have hG : M.toBlocks₁₁.IsHermitian := hM.isHermitian.submatrix Sum.inl
  have h21 : M.toBlocks₂₁ = cᴴ * M.toBlocks₁₁ := by
    have h : M.toBlocks₁₂ᴴ = M.toBlocks₂₁ := by
      ext i j
      exact hM.isHermitian.apply _ _
    rw [← h, hc, Matrix.conjTranspose_mul, hG.eq]
  have hres : (M.toBlocks₂₂ - cᴴ * M.toBlocks₁₁ * c).PosSemidef := by
    have hp := hM.conjTranspose_mul_mul_same (Matrix.fromRows (-c) (1 : Matrix Unit Unit ℂ))
    rw [← Matrix.fromBlocks_toBlocks M, hc, h21] at hp
    simpa [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromBlocks_mul_fromRows, Matrix.fromCols_mul_fromRows,
      Matrix.mul_assoc, sub_eq_add_neg, add_comm] using hp
  let δ : ℂ := (M.toBlocks₂₂ - cᴴ * M.toBlocks₁₁ * c) () ()
  have hδ : 0 ≤ δ := hres.diag_nonneg
  let r : ℂ := (Real.sqrt δ.re : ℝ)
  have hr : star r * r = δ := by
    have hre := Complex.eq_re_of_ofReal_le hδ
    rw [hre]
    change star (Real.sqrt δ.re : ℂ) * (Real.sqrt δ.re : ℂ) = (δ.re : ℂ)
    simp only [Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Complex.nonneg_iff.mp hδ).1]
  have hd : M.toBlocks₂₂ = cᴴ * M.toBlocks₁₁ * c + Matrix.of (fun _ _ : Unit => star r * r) := by
    ext i j
    cases i
    cases j
    have hh := hr
    simp only [δ, Matrix.sub_apply] at hh
    simpa only [Matrix.add_apply, Matrix.of_apply] using (eq_add_of_sub_eq hh.symm).trans (add_comm _ _)
  refine ⟨c, r, ?_⟩
  calc M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
      (Matrix.fromBlocks_toBlocks M).symm
       _ = residualExtension M.toBlocks₁₁ c r := by rw [hc, h21, hd]; rfl

private theorem converse {X : Type*} (K : X → X → ℂ)
    (hK : ∀ (n : ℕ) (L : Fin n → X), (finiteGram K L).PosSemidef) :
    KernelExtensionLaw K := by
  intro n L h
  have hp : (finiteGram K (Sum.elim L (fun _ : Unit => h))).PosSemidef := by
    let e := Fintype.equivFin (Fin n ⊕ Unit)
    have ht := hK (Fintype.card (Fin n ⊕ Unit)) (Sum.elim L (fun _ : Unit => h) ∘ e.symm)
    convert ht.submatrix e using 1
    ext i j
    simp [finiteGram, Matrix.submatrix]
  obtain ⟨c, r, heq⟩ := blockResidual _ hp
  exact ⟨c, r, heq⟩

/-- Positivity of all finite ordered tables is equivalent to the primitive law. -/
theorem extensionLaw_iff_finiteGram_posSemidef {X : Type*} (K : X → X → ℂ) :
    KernelExtensionLaw K ↔ ∀ (n : ℕ) (L : Fin n → X), (finiteGram K L).PosSemidef :=
  ⟨extensionLaw_finiteGram_posSemidef K, converse K⟩

/-- The global finitely supported positive form is equivalent to the same-entry law. -/
theorem extensionLaw_iff_kernel_posSemidef {X : Type*} (K : X → X → ℂ) :
    KernelExtensionLaw K ↔ (Matrix.of K).PosSemidef := by
  refine ⟨extensionLaw_kernel_posSemidef K, fun hK => ?_⟩
  exact (extensionLaw_iff_finiteGram_posSemidef K).mpr (fun n L => hK.submatrix L)

/-- A finite table is certified by successive actual square-residual equalities,
starting with the empty table; no positivity is assumed in this predicate. -/
def CertifiedHistory {X : Type*} (K : X → X → ℂ) :
    (n : ℕ) → (Fin n → X) → Prop
  | 0, _ => True
  | n + 1, L =>
      CertifiedHistory K n (fun i => L i.succ) ∧
        ∃ (c : Matrix (Fin n) Unit ℂ) (r : ℂ),
          finiteGram K (Sum.elim (fun i => L i.succ) (fun _ : Unit => L 0)) =
            residualExtension (finiteGram K (fun i => L i.succ)) c r

/-- Every finite set of declared labels occurs in some certified finite history. -/
def CertifiedFiniteCover {X : Type*} (K : X → X → ℂ) : Prop :=
  ∀ s : Finset X, ∃ (n : ℕ) (L : Fin n → X),
    CertifiedHistory K n L ∧ ∀ x ∈ s, ∃ i, L i = x

open private residualExtension_posSemidef
  from D5.S3.Quantum.Completion.HistoryKernelExtension

private theorem certifiedHistory_posSemidef {X : Type*} (K : X → X → ℂ) :
    ∀ (n : ℕ) (L : Fin n → X), CertifiedHistory K n L → (finiteGram K L).PosSemidef := by
  intro n
  induction n with
  | zero =>
      intro L _
      have hz : finiteGram K L = 0 := by ext i; exact Fin.elim0 i
      rw [hz]
      exact Matrix.PosSemidef.zero
  | succ n ih =>
      intro L hL
      obtain ⟨hold, c, r, heq⟩ := hL
      have hp := residualExtension_posSemidef _ c r (ih _ hold)
      rw [← heq] at hp
      have hs := hp.submatrix (Fin.cases (Sum.inr ()) (fun i => Sum.inl i))
      convert hs using 1
      ext i j
      refine Fin.cases ?_ (fun i => ?_) i <;>
        refine Fin.cases ?_ (fun j => ?_) j <;> rfl

/-- Certification need not be globally given as an extension law: a possibly different
certified chain covering each finite label set already implies the full universal law. -/
theorem certifiedFiniteCover_extensionLaw {X : Type*} (K : X → X → ℂ)
    (hcover : CertifiedFiniteCover K) : KernelExtensionLaw K := by
  classical
  apply (extensionLaw_iff_kernel_posSemidef K).mpr
  have hfin : ∀ (n : ℕ) (L : Fin n → X), (finiteGram K L).PosSemidef := by
    intro n L
    obtain ⟨m, V, hV, hinc⟩ := hcover (Finset.univ.image L)
    have hex (i : Fin n) : ∃ j, V j = L i :=
      hinc (L i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    choose e he using hex
    have hp := (certifiedHistory_posSemidef K m V hV).submatrix e
    convert hp using 1
    ext i j
    simp [finiteGram, Matrix.submatrix, he]
  refine Suppliers.ofSupport K ?_ ?_
  · ext x y
    exact (hfin 2 ![x, y]).isHermitian.apply 0 1
  · intro f
    let e := Fintype.equivFin f.support
    have hp := (hfin (Fintype.card f.support) (fun i => (e.symm i).val)).submatrix e
    simpa [finiteGram, Matrix.submatrix] using hp

#print axioms extensionLaw_iff_finiteGram_posSemidef
#print axioms extensionLaw_iff_kernel_posSemidef
#print axioms certifiedFiniteCover_extensionLaw
end D5.S3.Quantum.Completion.HistoryKernelConverse
