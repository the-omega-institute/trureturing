/- GID: D5/S3/Combinatorics/Matroids/FiniteIntersection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/FiniteIntersection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common independent set attains a finite matroid rank cut. -/

/-
Source: Peter Nelson, apnelson1/Matroid,
revision 8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b.
https://github.com/apnelson1/Matroid/blob/8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b/Matroid/Intersection.lean
Modified source: native Mathlib imports and names, explicit eRk.toNat and contraction expressions,
and the same-ground statement with its common-independent upper bound.
The consumed source files are Matroid/Intersection.lean, Matroid/Minor/Rank.lean,
Matroid/Rank/Nat.lean, Matroid/Rank/ENat.lean, Matroid/Loop.lean,
Matroid/ForMathlib/Matroid/Basic.lean, and Matroid/ForMathlib/Set.lean:139-140.
Their Apache-2.0 license is reproduced below.
Immutable source locations:
https://github.com/apnelson1/Matroid/blob/8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b/Matroid/Minor/Rank.lean
https://github.com/apnelson1/Matroid/blob/8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b/Matroid/Rank/Nat.lean
https://github.com/apnelson1/Matroid/blob/8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b/Matroid/Rank/ENat.lean
https://github.com/apnelson1/Matroid/blob/8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b/Matroid/Loop.lean
https://github.com/apnelson1/Matroid/blob/8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b/Matroid/ForMathlib/Matroid/Basic.lean
https://github.com/apnelson1/Matroid/blob/8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b/Matroid/ForMathlib/Set.lean#L139-L140
Retire this port when this repository's actual pinned Mathlib supplies an equivalent full
native finite-ground intersection theorem with the accepted standard axiom closure.
-/

module

public import Mathlib.Combinatorics.Matroid.Minor.Contract
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Linarith

/-! # Finite same-ground matroid intersection -/

@[expose] public section

open Set Matroid

namespace D5.S3.Combinatorics.Matroids.FiniteIntersection

variable {α : Type*} {M M₁ M₂ : Matroid α} {I J X Y C : Set α} {e : α}

private lemma basis_extend_inter (hIX : M.IsBasis' I X) (hXY : X ⊆ Y) :
    ∃ J, M.IsBasis' J Y ∧ J ∩ X = I := by
  obtain ⟨J, hJ, rfl⟩ :=
    hIX.isBasis_inter_ground.exists_isBasis_inter_eq_of_superset (inter_subset_inter_left M.E hXY)
  simp_rw [isBasis'_iff_isBasis_inter_ground]
  refine ⟨J, hJ, ?_⟩
  rw [inter_comm X, ← inter_assoc, inter_eq_self_of_subset_left hJ.indep.subset_ground]

private lemma delete_eRk (M : Matroid α) (D X : Set α) :
    (M ＼ D).eRk X = M.eRk (X \ D) := by
  rw [← restrict_compl, restrict_eRk_eq', sdiff_eq, inter_comm M.E, ← inter_assoc, ← sdiff_eq,
    eRk_inter_ground]

private lemma closure_eq_of_union_loops (h : X ∪ M.loops = Y ∪ M.loops) :
    M.closure X = M.closure Y := by
  rw [← closure_union_loops_eq, h, closure_union_loops_eq]

private lemma eRk_eq_of_union_loops (h : X ∪ M.loops = Y ∪ M.loops) : M.eRk X = M.eRk Y := by
  rw [← M.eRk_closure_eq, closure_eq_of_union_loops h, M.eRk_closure_eq]

private lemma contract_eRk_closure_left (M : Matroid α) (X Y : Set α) :
    (M ／ M.closure X).eRk Y = (M ／ X).eRk Y := by
  rw [contract_closure_eq_contract_delete, delete_eRk]
  apply eRk_eq_of_union_loops
  rw [contract_loops_eq, sdiff_union_self]

private lemma contract_eRk_closure_right (M : Matroid α) (X Y : Set α) :
    (M ／ X).eRk (M.closure Y) = (M ／ X).eRk Y := by
  rw [← eRk_closure_eq _ Y, ← eRk_closure_eq, contract_closure_eq,
    contract_closure_eq, closure_union_closure_left_eq]

private lemma contract_eRk_diff (M : Matroid α) (X Y : Set α) :
    (M ／ X).eRk Y = (M ／ X).eRk (Y \ X) := by
  rw [← eRk_closure_eq, contract_closure_eq, eq_comm, ← eRk_closure_eq,
    contract_closure_eq, sdiff_union_self]

private lemma contract_eRk_union (M : Matroid α) (X Y : Set α) :
    (M ／ X).eRk Y = (M ／ X).eRk (Y ∪ X) := by
  rw [eq_comm, contract_eRk_diff, union_sdiff_right, ← contract_eRk_diff]

private lemma basis_contract_eRk (hI : M.IsBasis' I X) (hIJ : M.IsBasis' (I ∪ J) Y)
    (hdj : Disjoint I J) : (M ／ X).eRk Y = J.encard := by
  rw [← contract_eRk_closure_right, ← hIJ.closure_eq_closure, contract_eRk_closure_right,
    ← contract_eRk_closure_left, ← hI.closure_eq_closure, contract_eRk_closure_left,
    contract_eRk_diff, union_sdiff_cancel_left (hdj.inter_eq.subset), Indep.eRk_eq_encard]
  rwa [hI.indep.contract_indep_iff, union_comm, disjoint_comm, and_iff_left hIJ.indep]

private lemma basis_contract_eRk_diff (hI : M.IsBasis' I (X ∪ C))
    (hIC : M.IsBasis' (I ∩ C) C) : (M ／ C).eRk X = (I \ C).encard := by
  rw [contract_eRk_union, basis_contract_eRk hIC (J := I \ C) (by simpa)
    disjoint_sdiff_inter.symm]

private lemma basis_contract_eRk_diff_subset (hI : M.IsBasis' I X) (hCX : C ⊆ X)
    (hIC : M.IsBasis' (I ∩ C) C) : (M ／ C).eRk X = (I \ C).encard := by
  rw [← union_eq_self_of_subset_right hCX] at hI
  exact basis_contract_eRk_diff hI hIC

private lemma contract_eRk_add_of_subset (M : Matroid α) (hXY : X ⊆ Y) :
    (M ／ X).eRk Y + M.eRk X = M.eRk Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, rfl⟩ := basis_extend_inter hI hXY
  rw [basis_contract_eRk_diff_subset hJ hXY hI, ← hI.encard_eq_eRk,
    encard_sdiff_add_encard_inter, hJ.encard_eq_eRk]

private lemma contract_eRk_add (M : Matroid α) (C X : Set α) :
    (M ／ C).eRk X + M.eRk C = M.eRk (X ∪ C) := by
  rw [contract_eRk_union, contract_eRk_add_of_subset]
  exact subset_union_right

@[simp] lemma cast_toNat_eRk (M : Matroid α) [RankFinite M] (X : Set α) :
    ((M.eRk X).toNat : ℕ∞) = M.eRk X :=
  ENat.natCast_toNat (M.isRkFinite_set X).eRk_lt_top.ne

private lemma rank_mono (M : Matroid α) [RankFinite M] (hXY : X ⊆ Y) :
    (M.eRk X).toNat ≤ (M.eRk Y).toNat := by
  rw [← ENat.natCast_le_natCast, cast_toNat_eRk, cast_toNat_eRk]
  exact M.eRk_mono hXY

private lemma indep_rank_eq_ncard (hI : M.Indep I) : (M.eRk I).toNat = I.ncard := by
  rw [hI.eRk_eq_encard, ncard_def]

lemma rank_submod (M : Matroid α) [RankFinite M] (X Y : Set α) :
    (M.eRk (X ∩ Y)).toNat + (M.eRk (X ∪ Y)).toNat ≤
      (M.eRk X).toNat + (M.eRk Y).toNat := by
  rw [← ENat.natCast_le_natCast, Nat.cast_add, Nat.cast_add,
    cast_toNat_eRk, cast_toNat_eRk, cast_toNat_eRk, cast_toNat_eRk]
  exact M.eRk_inter_add_eRk_union_le X Y

private lemma deleteElem_rank (M : Matroid α) (heX : e ∉ X) :
    ((M ＼ {e}).eRk X).toNat = (M.eRk X).toNat := by
  rw [delete_eRk, sdiff_singleton_eq_self heX]

private lemma contract_rank_add (M : Matroid α) [RankFinite M] (C X : Set α) :
    ((M ／ C).eRk X).toNat + (M.eRk C).toNat = (M.eRk (X ∪ C)).toNat := by
  rw [← ENat.natCast_inj, Nat.cast_add, cast_toNat_eRk, cast_toNat_eRk, cast_toNat_eRk,
    contract_eRk_add]

private lemma nonloop_contract_rank_add_one [RankFinite M] (he : M.IsNonloop e) :
    ((M ／ {e}).eRk X).toNat + 1 = (M.eRk (insert e X)).toNat := by
  rw [← union_singleton, ← contract_rank_add, he.eRk_eq]
  rfl

private lemma nonloop_contract_rank_intCast [RankFinite M] (he : M.IsNonloop e) :
    (((M ／ {e}).eRk X).toNat : ℤ) = (M.eRk (insert e X)).toNat - 1 := by
  rw [← nonloop_contract_rank_add_one he]
  exact eq_sub_of_add_eq rfl

private lemma common_indep_upper_bound [RankFinite M₁] [RankFinite M₂]
    (hI₁ : M₁.Indep I) (hI₂ : M₂.Indep I) (A : Set α) :
    I.ncard ≤ (M₁.eRk A).toNat + (M₂.eRk (M₂.E \ A)).toNat := by
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard I A hI₂.finite,
    ← indep_rank_eq_ncard (hI₁.inter_right A), ← indep_rank_eq_ncard (hI₂.sdiff A)]
  exact add_le_add (rank_mono M₁ inter_subset_right)
    (rank_mono M₂ (sdiff_subset_sdiff_left hI₂.subset_ground))

private lemma exists_common_ind_aux (M₁ M₂ : Matroid α) [M₁.Finite] (hE : M₁.E = M₂.E) :
    ∃ I X, X ⊆ M₁.E ∧ M₁.Indep I ∧ M₂.Indep I ∧
      I.ncard = (M₁.eRk X).toNat + (M₂.eRk (M₂.E \ X)).toNat := by
  have _ : M₂.Finite := ⟨hE.symm ▸ M₁.ground_finite⟩
  by_cases hloop : ∀ e ∈ M₁.E, M₁.IsLoop e ∨ M₂.IsLoop e
  · suffices 0 = (M₂.eRk (M₂.E \ M₁.loops)).toNat from
      ⟨∅, M₁.loops, closure_subset_ground _ _, by simpa⟩
    rw [eq_comm, ENat.toNat_eq_zero, or_iff_left (M₂.isRkFinite_set _).eRk_lt_top.ne,
      eRk_eq_zero_iff sdiff_subset, sdiff_subset_iff, ← hE]
    simpa [subset_def]
  push Not at hloop
  obtain ⟨e, he, he₁, he₂⟩ := hloop
  rw [not_isLoop_iff] at he₁ he₂

  have : (M₁ ／ {e}).E.ncard < M₁.E.ncard := ncard_lt_ncard (by simpa) M₁.ground_finite
  have : (M₁ ＼ {e}).E.ncard < M₁.E.ncard := ncard_lt_ncard (by simpa) M₁.ground_finite

  obtain ⟨Id, Xd, hXd, hId₁, hId₂, hId⟩ :=
    exists_common_ind_aux (M₁ ＼ {e}) (M₂ ＼ {e}) (by simp [hE])
  obtain ⟨Ic, Xc, hXc, hIc₁, hIc₂, hIc⟩ :=
    exists_common_ind_aux (M₁ ／ {e}) (M₂ ／ {e}) (by simp [hE])

  rw [he₁.contractElem_indep_iff] at hIc₁
  rw [he₂.contractElem_indep_iff] at hIc₂

  simp only [contract_ground, delete_ground, subset_sdiff,
    disjoint_singleton_right] at hXc hXd

  by_contra! hcon
  replace hcon :=
    show ∀ I X, X ⊆ M₁.E → M₁.Indep I → M₂.Indep I →
      I.ncard + 1 ≤ (M₁.eRk X).toNat + (M₂.eRk (M₂.E \ X)).toNat from
    fun I X hX h h' ↦ Nat.add_one_le_iff.2 <| (common_indep_upper_bound h h' X).lt_of_ne <|
      hcon I X hX h h'

  have hcond := hcon Id (Xc ∩ Xd) (inter_subset_left.trans hXc.1) hId₁.of_delete hId₂.of_delete

  replace hcon := hcon (insert e Ic) (insert e (Xc ∪ Xd))
    (insert_subset he₁.mem_ground (union_subset hXc.1 hXd.1)) hIc₁.2 hIc₂.2
  rw [ncard_insert_of_notMem hIc₁.1 (hIc₁.2.subset (subset_insert _ _)).finite,
    ← insert_union] at hcon

  have hsm := rank_submod M₁ (insert e Xc) Xd
  rw [insert_inter_of_notMem hXd.2] at hsm

  have hsm2 := rank_submod M₂ (M₂.E \ Xc) ((M₂.E \ insert e Xd))
  simp_rw [sdiff_eq, ← inter_inter_distrib_left, ← inter_union_distrib_left, ← compl_inter,
    ← compl_union, union_insert, ← insert_union, inter_comm Xc, insert_inter_of_notMem hXc.2,
    inter_comm Xd, ← sdiff_eq] at hsm2

  zify at hcon hcond hId hIc hsm hsm2

  rw [nonloop_contract_rank_intCast he₂, nonloop_contract_rank_intCast he₁, contract_ground,
    sdiff_sdiff_comm, insert_sdiff_singleton,
      insert_eq_of_mem (show e ∈ M₂.E \ Xc from ⟨he₂.mem_ground, hXc.2⟩)] at hIc
  rw [deleteElem_rank _ hXd.2, deleteElem_rank _ (by simp), delete_ground,
    sdiff_sdiff_comm, sdiff_sdiff, union_singleton] at hId

  linarith
termination_by M₁.E.ncard

/-- A finite same-ground intersection certificate and every common-independent cut bound. -/
theorem finite_matroid_intersection (E : Set α) (hE : E.Finite) (M₁ M₂ : Matroid α)
    (h₁ : M₁.E = E) (h₂ : M₂.E = E) :
    (∃ I X : Set α, I ⊆ E ∧ X ⊆ E ∧ M₁.Indep I ∧ M₂.Indep I ∧
      I.ncard = (M₁.eRk X).toNat + (M₂.eRk (E \ X)).toNat) ∧
    (∀ J Y : Set α, M₁.Indep J → M₂.Indep J →
      J.ncard ≤ (M₁.eRk Y).toNat + (M₂.eRk (E \ Y)).toNat) := by
  have : M₁.Finite := ⟨h₁.symm ▸ hE⟩
  have : M₂.Finite := ⟨h₂.symm ▸ hE⟩
  constructor
  · obtain ⟨I, X, hX, hI₁, hI₂, hc⟩ := exists_common_ind_aux M₁ M₂ (h₁.trans h₂.symm)
    exact ⟨I, X, h₁ ▸ hI₁.subset_ground, h₁ ▸ hX, hI₁, hI₂, h₂ ▸ hc⟩
  · intro J Y hJ₁ hJ₂
    simpa only [h₂] using common_indep_upper_bound hJ₁ hJ₂ Y

#print axioms finite_matroid_intersection

end D5.S3.Combinatorics.Matroids.FiniteIntersection

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
