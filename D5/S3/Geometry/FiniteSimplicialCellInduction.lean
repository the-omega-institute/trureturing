/- GID: D5/S3/Geometry/FiniteSimplicialCellInduction
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteSimplicialCellInduction
   mirror-E: none(waiver:abstract-finite-simplicial-cell-induction)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex]
   utility: none
   digest: Maximal nondegenerate cells give boundary pushouts and induction on every finite simplicial set. -/
/-
DifferentialGeometry
Copyright 2026 The DifferentialGeometry contributors

Modified Apache-2.0 source port of qinz1yang/differential-geometry,
revision afc0a69081be678c24cb55c5111236af329bfda1:
DifferentialGeometry/Topology/SimplicialSet/MaximalCell.lean and
DifferentialGeometry/Topology/SimplicialSet/FiniteCellInduction.lean.
The module namespace and imports are adapted; the unused reassoc generator is omitted.
The original mathematical statements and proof bodies are preserved.
The full license and upstream NOTICE are reproduced below.

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

Upstream NOTICE:
DifferentialGeometry
Copyright 2026 The DifferentialGeometry contributors

-/
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u

namespace D5.S3.Geometry.FiniteSimplicialCellInduction

variable {X : _root_.SSet.{u}} (s : X.N)


def costar : X.Subcomplex where
  obj m := {x | ¬s.subcomplex ≤ Subfunctor.ofSection x}
  map {m l} f x hx h := hx (h.trans (by
    rw [Subfunctor.ofSection_le_iff]
    exact ⟨f, rfl⟩))






def nondegenerateCellMap : (Δ[s.dim] : _root_.SSet.{u}) ⟶ X :=
  _root_.SSet.yonedaEquiv.symm s.simplex


theorem costar_preimage_cellMap :
    (costar s).preimage (nondegenerateCellMap s) = _root_.SSet.boundary s.dim := by
  ext ⟨⟨m⟩⟩ x
  obtain ⟨f, rfl⟩ := _root_.SSet.stdSimplex.objEquiv.symm.surjective x
  change (¬s.subcomplex ≤ _root_.SSet.Subcomplex.ofSimplex
    (X.map f.op s.simplex)) ↔ ¬Function.Surjective f.toOrderHom
  rw [← SimplexCategory.epi_iff_surjective]
  apply not_congr
  constructor
  · intro h
    rw [_root_.SSet.Subcomplex.ofSimplex_le_iff,
      _root_.SSet.Subcomplex.mem_ofSimplex_obj_iff] at h
    obtain ⟨g, hg⟩ := h
    have hcomp : X.map (g ≫ f).op s.simplex = s.simplex := by
      simpa only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] using hg
    have : Mono (g ≫ f) := X.mono_of_nonDegenerate ⟨_, s.nonDegenerate⟩ _ _ hcomp
    have heq := SimplexCategory.eq_id_of_mono (g ≫ f)
    have : Epi (g ≫ f) := by rw [heq]; infer_instance
    exact epi_of_epi g f
  · intro hf
    rw [_root_.SSet.Subcomplex.ofSimplex_map_of_epi]



theorem costar_sup_cell_eq_top (hs : IsMax s) :
    costar s ⊔ s.subcomplex = ⊤ := by
  apply top_unique
  rw [← _root_.SSet.N.iSup_subcomplex_eq_top X]
  apply iSup_le
  intro t
  by_cases h : s ≤ t
  · have ht : t = s := le_antisymm (hs h) h
    rw [ht]
    exact le_sup_right
  · exact (show t.subcomplex ≤ costar s from
      (Subfunctor.ofSection_le_iff _ _).mpr h).trans le_sup_left


theorem nondegenerateCellMap_injOn_compl_boundary (m : ℕ) :
    Set.InjOn ((nondegenerateCellMap s).app (op ⦋m⦌))
      ((_root_.SSet.boundary s.dim).obj (op ⦋m⦌))ᶜ := by
  intro x hx y hy h
  obtain ⟨f, rfl⟩ := _root_.SSet.stdSimplex.objEquiv.symm.surjective x
  obtain ⟨g, rfl⟩ := _root_.SSet.stdSimplex.objEquiv.symm.surjective y
  have : Epi f := by
    simpa [_root_.SSet.boundary, SimplexCategory.epi_iff_surjective] using! hx
  have h' : X.map f.op s.simplex = X.map g.op s.simplex := h
  have heq := X.unique_nonDegenerate_map _ f ⟨_, s.nonDegenerate⟩ rfl
    g ⟨_, s.nonDegenerate⟩ h'
  rw [heq]

def costarAttachingMap : (_root_.SSet.boundary s.dim : _root_.SSet.{u}) ⟶ costar s :=
  _root_.SSet.Subcomplex.lift ((_root_.SSet.boundary s.dim).ι ≫ nondegenerateCellMap s) (by
    rw [_root_.SSet.Subcomplex.range_comp, _root_.SSet.Subcomplex.image_le_iff,
      costar_preimage_cellMap]
    simp)


theorem costarAttachingMap_inclusion :
    costarAttachingMap s ≫ (costar s).ι =
      (_root_.SSet.boundary s.dim).ι ≫ nondegenerateCellMap s := rfl


theorem costar_cell_isPullback :
    IsPullback (costarAttachingMap s) (_root_.SSet.boundary s.dim).ι
      (costar s).ι (nondegenerateCellMap s) where
  w := costarAttachingMap_inclusion s
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨⟨m⟩⟩ ↦ by
    apply (isLimitMapConePullbackConeEquiv _ _).2
    apply IsPullback.isLimit
    rw [Types.isPullback_iff]
    refine ⟨rfl, ?_, ?_⟩
    · intro x y h
      exact Subtype.ext h.2
    · intro x y h
      change x.val = (nondegenerateCellMap s).app _ y at h
      have hy : y ∈ (_root_.SSet.boundary s.dim).obj (op ⦋m⦌) := by
        rw [← costar_preimage_cellMap s]
        change (nondegenerateCellMap s).app _ y ∈ (costar s).obj _
        rw [← h]
        exact x.prop
      exact ⟨⟨y, hy⟩, Subtype.ext h.symm, rfl⟩)⟩

theorem costar_cell_isPushout (hs : IsMax s) :
    IsPushout (_root_.SSet.boundary s.dim).ι (costarAttachingMap s)
      (nondegenerateCellMap s) (costar s).ι := by
  apply IsPushout.flip
  refine { w := costarAttachingMap_inclusion s, isColimit' := ⟨?_⟩ }
  apply evaluationJointlyReflectsColimits _
  intro ⟨⟨m⟩⟩
  apply (isColimitMapCoconePushoutCoconeEquiv _ _).2
  apply IsPushout.isColimit
  apply Types.isPushout_of_isPullback_of_mono'
  · exact (costar_cell_isPullback s).map ((evaluation _ _).obj _)
  · have hsup := congrArg (fun A : X.Subcomplex ↦ A.obj (op ⦋m⦌))
      (costar_sup_cell_eq_top s hs)
    have hr : _root_.SSet.Subcomplex.range (nondegenerateCellMap s) = s.subcomplex :=
      by simpa [nondegenerateCellMap] using
        _root_.SSet.Subcomplex.range_eq_ofSimplex (nondegenerateCellMap s)
    have hr' := congrArg (fun A : X.Subcomplex ↦ A.obj (op ⦋m⦌)) hr
    change Set.range (fun x : (costar s).obj (op ⦋m⦌) ↦ x.val) ∪
      Set.range ((nondegenerateCellMap s).app (op ⦋m⦌)) = Set.univ
    rw [Subtype.range_coe_subtype]
    change Set.range ((nondegenerateCellMap s).app (op ⦋m⦌)) = _ at hr'
    rw [hr']
    exact hsup
  · intro x y hx hy h
    apply nondegenerateCellMap_injOn_compl_boundary s m
    · exact fun hx' ↦ hx ⟨⟨x, hx'⟩, rfl⟩
    · exact fun hy' ↦ hy ⟨⟨y, hy'⟩, rfl⟩
    · exact h

def costarNondegenerateEquiv :
    (costar s : _root_.SSet).N ≃ {t : X.N // ¬s ≤ t} where
  toFun t := ⟨_root_.SSet.N.mk t.simplex.val
    (((costar s).mem_nonDegenerate_iff t.simplex).mp t.nonDegenerate), t.simplex.prop⟩
  invFun t := _root_.SSet.N.mk ⟨t.val.simplex, t.prop⟩
    (((costar s).mem_nonDegenerate_iff ⟨t.val.simplex, t.prop⟩).mpr t.val.nonDegenerate)
  left_inv t := by cases t; rfl
  right_inv t := by rcases t with ⟨t, ht⟩; cases t; rfl

theorem card_costar_nondegenerate_lt [X.Finite] :
    Nat.card (costar s : _root_.SSet).N < Nat.card X.N := by
  classical
  let := Fintype.ofFinite X.N
  let := Fintype.ofFinite (costar s : _root_.SSet).N
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_not_surjective
    (fun t ↦ (costarNondegenerateEquiv s t).val)
    (Subtype.val_injective.comp (costarNondegenerateEquiv s).injective)
  intro h
  obtain ⟨t, ht⟩ := h s
  exact (costarNondegenerateEquiv s t).prop (le_of_eq ht.symm)

end D5.S3.Geometry.FiniteSimplicialCellInduction


set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial


namespace D5.S3.Geometry.FiniteSimplicialCellInduction


def isInitial_of_isEmpty_nondegenerate (X : _root_.SSet.{u}) [IsEmpty X.N] : IsInitial X := by
  have hbot : (⊥ : X.Subcomplex) = ⊤ := by
    apply le_antisymm bot_le
    rw [_root_.SSet.N.subcomplex_le_iff]
    intro s
    exact isEmptyElim s
  have ht : IsInitial ((⊤ : X.Subcomplex) : _root_.SSet.{u}) := by
    rw [← hbot]
    exact _root_.SSet.Subcomplex.isInitialBot
  exact ht.ofIso (_root_.SSet.Subcomplex.topIso X)

@[elab_as_elim]
theorem finite_cell_induction (P : _root_.SSet.{u} → Prop)
    (hInitial : ∀ X, IsInitial X → P X)
    (hCell : ∀ (n : ℕ) (X Y : _root_.SSet.{u})
      (g : (_root_.SSet.boundary n : _root_.SSet) ⟶ X)
      (r : (Δ[n] : _root_.SSet) ⟶ Y) (b : X ⟶ Y),
      IsPushout (_root_.SSet.boundary n).ι g r b →
      P (_root_.SSet.boundary n) → P X → P Y)
    (X : _root_.SSet.{u}) [X.Finite] : P X := by
  suffices ∀ d : ℕ, ∀ Y : _root_.SSet.{u}, Y.Finite → Y.HasDimensionLT d → P Y by
    obtain ⟨d, hd⟩ := X.hasDimensionLT_of_finite
    exact this d X inferInstance hd
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro Y hY hd
    generalize hn : Nat.card Y.N = n
    induction n using Nat.strong_induction_on generalizing Y with
    | h n ihn =>
      cases isEmpty_or_nonempty Y.N with
      | inl he =>
        have : IsEmpty Y.N := he
        exact hInitial Y (isInitial_of_isEmpty_nondegenerate Y)
      | inr he =>
        have : Nonempty Y.N := he
        obtain ⟨s, hs⟩ := (Set.finite_univ : (Set.univ : Set Y.N).Finite).exists_maximal
          (Set.univ_nonempty)
        have hmax : IsMax s := fun t ht ↦ hs.2 (Set.mem_univ t) ht
        apply hCell s.dim (costar s) Y (costarAttachingMap s) (nondegenerateCellMap s)
          (costar s).ι (costar_cell_isPushout s hmax)
        · exact ih s.dim (Y.dim_lt_of_nonDegenerate ⟨_, s.nonDegenerate⟩ d)
            (_root_.SSet.boundary s.dim) inferInstance inferInstance
        · apply ihn (Nat.card (costar s : _root_.SSet).N)
            (by rw [← hn]; exact card_costar_nondegenerate_lt s) (costar s)
            inferInstance inferInstance rfl

end D5.S3.Geometry.FiniteSimplicialCellInduction
