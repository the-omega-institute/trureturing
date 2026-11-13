/- GID: D5/S3/HomologicalAlgebra/AcyclicCarrier
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/AcyclicCarrier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Homology.Homotopy, mathlib/module/Mathlib.LinearAlgebra.Basis.Defs]
   utility: none
   digest: Basis-indexed acyclic carriers support homotopies over arbitrary commutative rings. -/

import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Abel

/-!
Source port of AxiomMath/TernaryPoly, immutable revision
28679d7cad438a91a732422d4ab1b184ae17e532,
BoundaryComparison/FacePairingFull/CapCompat/{Carriers,Cells}.lean.
Original attribution: Formalized by Claude Sonnet 5.5.
Modified coefficient/interface statement: arbitrary commutative rings and ordinary
module bases replace rational equivariant cell bases. Boundary nesting is stated
on the finite support of each basis boundary. The carrier primitive and sequence
construction are adapted from the licensed source, rather than re-proving its
rational equivariant theorem.
Retirement condition: replace this port with direct upstream use when this
repository's pinned Mathlib supplies the equivalent full carried statement.
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

   Copyright 2026 Lean FRO, LLC

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

noncomputable section
open CategoryTheory Limits Module
universe u v w x
namespace D5.S3.HomologicalAlgebra.AcyclicCarrier
variable {R : Type u} [CommRing R]
variable {C D : ChainComplex (ModuleCat.{v} R) ℕ}
variable {I : ℕ → Type w} (B : ∀ n, Basis (I n) R (C.X n))

structure CarrierData where
  K : ∀ n, I n → ∀ m, Submodule R (D.X m)
  K_d : ∀ n s m (x : D.X (m + 1)), x ∈ K n s (m + 1) →
    (D.d (m + 1) m).hom x ∈ K n s m
  K_face : ∀ n (s : I (n + 1)) (t : I n),
    (B n).repr ((C.d (n + 1) n).hom (B (n + 1) s)) t ≠ 0 →
    ∀ m, K n t m ≤ K (n + 1) s m

variable {B}

def CarrierData.Carried (𝒦 : CarrierData (D := D) B) {n m : ℕ}
    (g : C.X n ⟶ D.X m) : Prop := ∀ s, g.hom (B n s) ∈ 𝒦.K n s m

theorem CarrierData.Carried.face {𝒦 : CarrierData (D := D) B} {n m : ℕ}
    {g : C.X n ⟶ D.X m} (hg : 𝒦.Carried g) (s : I (n + 1)) :
    g.hom ((C.d (n + 1) n).hom (B (n + 1) s)) ∈ 𝒦.K (n + 1) s m := by
  classical
  let x := (C.d (n + 1) n).hom (B (n + 1) s)
  change g.hom x ∈ _
  rw [← (B n).linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro t ht
  exact Submodule.smul_mem _ _ (𝒦.K_face n s t (Finsupp.mem_support_iff.mp ht) m (hg t))

theorem CarrierData.Carried.sub {𝒦 : CarrierData (D := D) B} {n m : ℕ} {g g' : C.X n ⟶ D.X m}
    (hg : 𝒦.Carried g) (hg' : 𝒦.Carried g') : 𝒦.Carried (g - g') := by
  intro s
  exact Submodule.sub_mem _ (hg s) (hg' s)

/-- Acyclicity of the carriers relative to an augmentation `aug : D.X 0 ⟶ A`. -/
structure CarrierData.Acyclic (𝒦 : CarrierData (D := D) B) {A : Type x} [AddCommGroup A] [Module R A] (aug : D.X 0 →ₗ[R] A) : Prop where
  aug_d : aug.comp (D.d 1 0).hom = 0
  acyc0 : ∀ n (s : I n) (y : D.X 0), y ∈ 𝒦.K n s 0 → aug y = 0 →
    ∃ x ∈ 𝒦.K n s 1, (D.d 1 0).hom x = y
  acyc : ∀ n (s : I n) m (y : D.X (m + 1)), y ∈ 𝒦.K n s (m + 1) → (D.d (m + 1) m).hom y = 0 →
    ∃ x ∈ 𝒦.K n s (m + 2), (D.d (m + 2) (m + 1)).hom x = y

/-- Extend pointwise carrier lifts linearly along an arbitrary, possibly empty basis. -/
theorem basis_exists_lift {n : ℕ} {Y Z : ModuleCat.{v} R}
    (KY : I n → Submodule R Y) (φ : Y ⟶ Z) (Φ : C.X n ⟶ Z)
    (h : ∀ s, Φ.hom (B n s) ∈ (KY s).map φ.hom) :
    ∃ Ψ : C.X n ⟶ Y, (∀ s, Ψ.hom (B n s) ∈ KY s) ∧ Ψ ≫ φ = Φ := by
  classical
  choose y hy hyφ using h
  refine ⟨ModuleCat.ofHom ((B n).constr R y), ?_, ?_⟩
  · intro s
    simpa using hy s
  · apply ModuleCat.hom_ext
    apply (B n).ext
    intro s
    simpa using hyφ s

/-- The primitive step in positive degrees. -/
theorem CarrierData.exists_carried_primitive (𝒦 : CarrierData (D := D) B) {A : Type x} [AddCommGroup A] [Module R A] {aug : D.X 0 →ₗ[R] A}
    (hac : 𝒦.Acyclic aug) {n : ℕ} (m : ℕ) (Φ : C.X n ⟶ D.X (m + 1)) (hΦ : 𝒦.Carried Φ)
    (hcyc : Φ ≫ D.d (m + 1) m = 0) :
    ∃ Ψ : C.X n ⟶ D.X (m + 2), 𝒦.Carried Ψ ∧ Ψ ≫ D.d (m + 2) (m + 1) = Φ := by
  obtain ⟨Ψ, hΨK, hΨ⟩ := basis_exists_lift (B := B) (fun s => 𝒦.K n s (m + 2))
    (D.d (m + 2) (m + 1)) Φ (fun s => by
      obtain ⟨x, hx, hxd⟩ := hac.acyc n s m (Φ.hom (B n s)) (hΦ s) (by
        have := congrArg (fun ψ : C.X n ⟶ D.X m => ψ.hom (B n s)) hcyc
        simpa using this)
      exact ⟨x, hx, hxd⟩)
  exact ⟨Ψ, hΨK, hΨ⟩

/-- The primitive step in degree zero. -/
theorem CarrierData.exists_carried_primitive0 (𝒦 : CarrierData (D := D) B) {A : Type x} [AddCommGroup A] [Module R A] {aug : D.X 0 →ₗ[R] A}
    (hac : 𝒦.Acyclic aug) {n : ℕ} (Φ : C.X n ⟶ D.X 0) (hΦ : 𝒦.Carried Φ) (hcyc : aug.comp Φ.hom = 0) :
    ∃ Ψ : C.X n ⟶ D.X 1, 𝒦.Carried Ψ ∧ Ψ ≫ D.d 1 0 = Φ := by
  obtain ⟨Ψ, hΨK, hΨ⟩ := basis_exists_lift (B := B) (fun s => 𝒦.K n s 1)
    (D.d 1 0) Φ (fun s => by
      obtain ⟨x, hx, hxd⟩ := hac.acyc0 n s (Φ.hom (B n s)) (hΦ s) (by
        have := congrArg (fun ψ : C.X n →ₗ[R] A => ψ (B n s)) hcyc
        simpa using this)
      exact ⟨x, hx, hxd⟩)
  exact ⟨Ψ, hΨK, hΨ⟩

theorem CarrierData.Carried.comp_left {𝒦 : CarrierData (D := D) B} {n m : ℕ} {g : C.X n ⟶ D.X m}
    (hg : 𝒦.Carried g) (ε : ℤ) : 𝒦.Carried (ε • g) := by
  intro s
  have : (ε • g).hom (B n s) = ε • g.hom (B n s) := rfl
  rw [this]
  exact Submodule.smul_of_tower_mem _ ε (hg s)

/-- A carried morphism precomposed with the boundary of the complex `C` is carried (shifted by a degree). -/
theorem CarrierData.Carried.d_comp {𝒦 : CarrierData (D := D) B} {n m : ℕ} {g : C.X n ⟶ D.X m}
    (hg : 𝒦.Carried g) : 𝒦.Carried (C.d (n + 1) n ≫ g) := by
  intro s
  exact hg.face s

theorem exists_sequence (State : ℕ → Type*) (I : State 0 → Prop)
    (R : ∀ m, State m → State (m + 1) → Prop)
    (h0 : ∃ s : State 0, I s) (h : ∀ m (s : State m), ∃ s' : State (m + 1), R m s s') :
    ∃ seq : ∀ m, State m, I (seq 0) ∧ ∀ m, R m (seq m) (seq (m + 1)) := by
  obtain ⟨s0, hs0⟩ := h0
  choose step hstep using h
  let seq : ∀ m, State m := fun m => Nat.rec s0 (fun m s => step m s) m
  exact ⟨seq, hs0, fun m => hstep m (seq m)⟩

/-- **Carried homotopies.**  Two carried twisted chain maps `C.X q ⟶ D.X q` with the same augmentation are
homotopic by a carried homotopy. -/
theorem CarrierData.exists_carried_homotopy (𝒦 : CarrierData (D := D) B) {A : Type x} [AddCommGroup A] [Module R A] {aug : D.X 0 →ₗ[R] A}
    (hac : 𝒦.Acyclic aug) (ε : ℤ) (f g : ∀ q, C.X q ⟶ D.X q)
    (hf : ∀ q, f (q + 1) ≫ D.d (q + 1) q = ε • (C.d (q + 1) q ≫ f q))
    (hg : ∀ q, g (q + 1) ≫ D.d (q + 1) q = ε • (C.d (q + 1) q ≫ g q))
    (hfc : ∀ q, 𝒦.Carried (f q)) (hgc : ∀ q, 𝒦.Carried (g q))
    (haug : aug.comp (f 0).hom = aug.comp (g 0).hom) :
    ∃ h : ∀ q, C.X q ⟶ D.X (q + 1), (∀ q, 𝒦.Carried (h q)) ∧ f 0 - g 0 = h 0 ≫ D.d 1 0 ∧
      ∀ q, f (q + 1) - g (q + 1) = h (q + 1) ≫ D.d (q + 1 + 1) (q + 1) + ε • (C.d (q + 1) q ≫ h q) := by
  let State : ℕ → Type _ := fun q =>
    {h : C.X q ⟶ D.X (q + 1) // 𝒦.Carried h ∧
      C.d (q + 1) q ≫ (f q - g q - h ≫ D.d (q + 1) q) = 0}
  obtain ⟨seq, hseq0, hseq⟩ := exists_sequence State
    (fun s => f 0 - g 0 = s.1 ≫ D.d 1 0)
    (fun q s s' => s'.1 ≫ D.d (q + 1 + 1) (q + 1) = f (q + 1) - g (q + 1) - ε • (C.d (q + 1) q ≫ s.1))
    (by
      obtain ⟨Ψ, hΨc, hΨ⟩ := 𝒦.exists_carried_primitive0 hac (f 0 - g 0) ((hfc 0).sub (hgc 0))
        (by
          ext x
          have hx := congrArg (fun k : C.X 0 →ₗ[R] A => k x) haug
          simpa using sub_eq_zero.mpr hx)
      refine ⟨⟨Ψ, hΨc, ?_⟩, hΨ.symm⟩
      rw [hΨ, sub_self, comp_zero])
    (by
      rintro q ⟨h, hc, hcyc⟩
      have hΦc : 𝒦.Carried (f (q + 1) - g (q + 1) - ε • (C.d (q + 1) q ≫ h)) :=
        ((hfc (q + 1)).sub (hgc (q + 1))).sub (hc.d_comp.comp_left ε)
      have hΦcyc : (f (q + 1) - g (q + 1) - ε • (C.d (q + 1) q ≫ h)) ≫ D.d (q + 1) q = 0 := by
        have h1 : (f (q + 1) - g (q + 1) - ε • (C.d (q + 1) q ≫ h)) ≫ D.d (q + 1) q =
            ε • (C.d (q + 1) q ≫ (f q - g q - h ≫ D.d (q + 1) q)) := by
          simp only [Preadditive.sub_comp, Preadditive.zsmul_comp, Category.assoc, hf, hg,
            Preadditive.comp_sub, smul_sub]
        rw [h1, hcyc, smul_zero]
      obtain ⟨Ψ, hΨc, hΨ⟩ := 𝒦.exists_carried_primitive hac q _ hΦc hΦcyc
      refine ⟨⟨Ψ, hΨc, ?_⟩, hΨ⟩
      have h2 : f (q + 1) - g (q + 1) - Ψ ≫ D.d (q + 1 + 1) (q + 1) = ε • (C.d (q + 1) q ≫ h) := by
        rw [hΨ]; abel
      rw [h2]
      have hdd : C.d ((q + 1) + 1) ((q + 1)) ≫ C.d (q + 1) q = 0 := C.d_comp_d _ _ _
      rw [Preadditive.comp_zsmul, ← Category.assoc, hdd, zero_comp, smul_zero])
  refine ⟨fun q => (seq q).1, fun q => (seq q).2.1, hseq0, fun q => ?_⟩
  have := hseq q
  rw [this]
  abel


/-- The ordinary basis-indexed augmented acyclic-carrier homotopy theorem. -/
theorem exists_homotopy
    (A : ∀ n, I n → ∀ m, Submodule R (D.X m))
    (boundary : ∀ n b m (z : D.X (m + 1)), z ∈ A n b (m + 1) →
      (D.d (m + 1) m).hom z ∈ A n b m)
    (nest : ∀ n (b : I (n + 1)) (c : I n),
      (B n).repr ((C.d (n + 1) n).hom (B (n + 1) b)) c ≠ 0 →
      ∀ m, A n c m ≤ A (n + 1) b m)
    (epsilon : D.X 0 →ₗ[R] R)
    (epsilon_d : epsilon.comp (D.d 1 0).hom = 0)
    (acyc0 : ∀ n b (z : D.X 0), z ∈ A n b 0 → epsilon z = 0 →
      ∃ y ∈ A n b 1, (D.d 1 0).hom y = z)
    (acyc : ∀ n b m (z : D.X (m + 1)), z ∈ A n b (m + 1) →
      (D.d (m + 1) m).hom z = 0 → ∃ y ∈ A n b (m + 2), (D.d (m + 2) (m + 1)).hom y = z)
    (f g : C ⟶ D)
    (augmentation : epsilon.comp (f.f 0).hom = epsilon.comp (g.f 0).hom)
    (fc : ∀ n b, (f.f n).hom (B n b) ∈ A n b n)
    (gc : ∀ n b, (g.f n).hom (B n b) ∈ A n b n) :
    ∃ H : Homotopy f g, ∀ n b, (H.hom n (n + 1)).hom (B n b) ∈ A n b (n + 1) := by
  classical
  let K : CarrierData (D := D) B := ⟨A, boundary, nest⟩
  have hac : K.Acyclic epsilon := ⟨epsilon_d, acyc0, acyc⟩
  obtain ⟨h, hc, hzero, hs⟩ := K.exists_carried_homotopy hac 1 f.f g.f
    (by intro q; simpa using (f.comm (q + 1) q).symm)
    (by intro q; simpa using (g.comm (q + 1) q).symm)
    (by intro q; simpa [CarrierData.Carried, K] using fc q)
    (by intro q; simpa [CarrierData.Carried, K] using gc q)
    (by simpa using augmentation)
  simp only [one_smul] at hc hzero hs
  let H : Homotopy f g :=
    { hom := fun i j => if e : i + 1 = j then h i ≫ eqToHom (congrArg D.X e) else 0
      zero := by
        intro i j hij
        exact dite_eq_right (fun e => hij e)
      comm := by
        intro i
        cases i with
        | zero =>
          simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
            dite_eq_left rfl, eqToHom_refl, Category.comp_id, zero_add]
          exact sub_eq_iff_eq_add.mp hzero
        | succ i =>
          simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
            dite_eq_left rfl, eqToHom_refl, Category.comp_id]
          have hi := hs i
          apply sub_eq_iff_eq_add.mp at hi
          simpa only [add_comm, add_left_comm, add_assoc] using hi }
  refine ⟨H, ?_⟩
  intro n b
  simpa [H] using hc n b

end D5.S3.HomologicalAlgebra.AcyclicCarrier
