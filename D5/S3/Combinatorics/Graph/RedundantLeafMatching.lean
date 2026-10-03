/- GID: D5/S3/Combinatorics/Graph/RedundantLeafMatching
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RedundantLeafMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Redundant-leaf fold and inclusion preserve maximal matchings and cardinality. -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Tactic

/-
Source: google-deepmind/formal-conjectures,
revision df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1,
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Matching.lean.
Copyright 2025 The Formal Conjectures Authors (IsEdgeMatching and
IsMaximalEdgeMatching). Their definition bodies and documentation are unchanged.
The maximal-matching transport theorem is additional content.
Retire these definition slices when the pinned dependency provides the same
unordered-edge matching and inclusion-maximality conventions.

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

set_option autoImplicit false

namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite set of edges `M` is a *matching* of `G` if every element of `M` is
an edge of `G` and any two edges of `M` are equal or share no vertex (no vertex
is covered twice). -/
def IsEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ = e₂ ∨ ∀ v : α, ¬ (v ∈ e₁ ∧ v ∈ e₂)

/-- A matching `M` of `G` is *maximal* if no further edge of `G` can be added to
`M` while keeping the matching property. -/
def IsMaximalEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  G.IsEdgeMatching M ∧
    ∀ e ∈ G.edgeSet, e ∉ M → ¬ G.IsEdgeMatching (insert e M)

end SimpleGraph

namespace D5.S3.Combinatorics.Graph.RedundantLeafMatching

universe w

/-- Folding a redundant leaf and including the residual graph preserve maximal
edge matchings and their cardinalities in both directions. -/
theorem redundant_leaf_maximal_matching_transport
    {V : Type w} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v a : V)
    (huv : u ≠ v) (hu : G.degree u = 1) (hv : G.degree v = 1)
    (hua : G.Adj u a) (hva : G.Adj v a) :
    let W := {x : V // x ≠ u}
    let H := G.induce {x : V | x ≠ u}
    let f : V → W := fun x =>
      if h : x = u then ⟨v, Ne.symm huv⟩ else ⟨x, h⟩
    (∀ M : Finset (Sym2 V), G.IsMaximalEdgeMatching M →
      H.IsMaximalEdgeMatching (M.image (Sym2.map f)) ∧
        (M.image (Sym2.map f)).card = M.card) ∧
    (∀ N : Finset (Sym2 W), H.IsMaximalEdgeMatching N →
      G.IsMaximalEdgeMatching (N.image (Sym2.map Subtype.val)) ∧
        (N.image (Sym2.map Subtype.val)).card = N.card) := by
  classical
  let W := {x : V // x ≠ u}
  let H := G.induce {x : V | x ≠ u}
  let f : V → W := fun x =>
    if h : x = u then ⟨v, Ne.symm huv⟩ else ⟨x, h⟩
  change (∀ M, G.IsMaximalEdgeMatching M →
    H.IsMaximalEdgeMatching (M.image (Sym2.map f)) ∧ _) ∧
    (∀ N, H.IsMaximalEdgeMatching N →
    G.IsMaximalEdgeMatching (N.image (Sym2.map Subtype.val)) ∧ _)
  have f_retained (x : W) : f x.val = x := by
    apply Subtype.ext
    simp only [f, dif_neg x.property]
  have unique_neighbor (l : V) (hl : G.degree l = 1) (hla : G.Adj l a)
      (x : V) (hlx : G.Adj l x) : x = a := by
    obtain ⟨b, hb, huniq⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hl
    exact (huniq x hlx).trans (huniq a hla).symm
  have leaf_edge (l : V) (hl : G.degree l = 1) (hla : G.Adj l a)
      (e : Sym2 V) (he : e ∈ G.edgeSet) (hle : l ∈ e) : e = s(l, a) := by
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp hle
    have hx := unique_neighbor l hl hla x (by simpa using he)
    rw [hx]
  have blocked_iff {β : Type w} [DecidableEq β] (K : SimpleGraph β)
      (M : Finset (Sym2 β)) :
      K.IsMaximalEdgeMatching M ↔ K.IsEdgeMatching M ∧
        ∀ e ∈ K.edgeSet, ∃ d ∈ M, ∃ x : β, x ∈ e ∧ x ∈ d := by
    constructor
    · intro hm
      refine ⟨hm.1, ?_⟩
      intro e he
      by_contra hnone
      have hn : ∀ d ∈ M, ∀ x : β, ¬ (x ∈ e ∧ x ∈ d) := by
        intro d hd x hx
        exact hnone ⟨d, hd, x, hx⟩
      have hi : K.IsEdgeMatching (insert e M) := by
        constructor
        · intro d hd
          rcases Finset.mem_insert.mp hd with rfl | hd
          · exact he
          · exact hm.1.1 d hd
        · intro d hd q hq
          rcases Finset.mem_insert.mp hd with hde | hdM
          · subst d
            rcases Finset.mem_insert.mp hq with hqe | hqM
            · exact Or.inl hqe.symm
            · exact Or.inr (hn q hqM)
          · rcases Finset.mem_insert.mp hq with hqe | hqM
            · subst q
              exact Or.inr (fun x hx => hn d hdM x ⟨hx.2, hx.1⟩)
            · exact hm.1.2 d hdM q hqM
      have hem : e ∉ M := by
        intro hem
        induction e using Sym2.inductionOn with
        | _ x y => exact hn s(x, y) hem x ⟨by simp, by simp⟩
      exact hm.2 e he hem hi
    · rintro ⟨hm, hb⟩
      refine ⟨hm, ?_⟩
      intro e he hem hi
      obtain ⟨d, hd, x, hxe, hxd⟩ := hb e he
      rcases hi.2 e (Finset.mem_insert_self _ _) d (Finset.mem_insert_of_mem hd) with h | h
      · exact hem (h ▸ hd)
      · exact h x ⟨hxe, hxd⟩
  have fold_adj (x y : V) (hxy : G.Adj x y) : H.Adj (f x) (f y) := by
    change G.Adj (f x).val (f y).val
    by_cases hx : x = u
    · subst x
      have hy : y = a := unique_neighbor u hu hua y hxy
      subst y
      have hau : a ≠ u := hua.ne.symm
      simpa [f, hau] using hva
    · by_cases hy : y = u
      · subst y
        have hxa : x = a := unique_neighbor u hu hua x hxy.symm
        subst x
        have hau : a ≠ u := hua.ne.symm
        simpa [f, hau] using hva.symm
      · simpa [f, hx, hy] using hxy
  constructor
  · intro M hM
    have collision (e : Sym2 V) (he : e ∈ M) (d : Sym2 V) (hd : d ∈ M)
        (x y : V) (hxe : x ∈ e) (hyd : y ∈ d) (hxy : f x = f y) : e = d := by
      have common (z : V) (hze : z ∈ e) (hzd : z ∈ d) : e = d := by
        rcases hM.1.2 e he d hd with h | h
        · exact h
        · exact False.elim (h z ⟨hze, hzd⟩)
      by_cases hx : x = u
      · subst x
        by_cases hy : y = u
        · subst y
          exact common u hxe hyd
        · have hyv : y = v := by
            have hh := congrArg Subtype.val hxy
            simpa [f, hy] using hh.symm
          subst y
          have heq := leaf_edge u hu hua e (hM.1.1 e he) hxe
          have hdq := leaf_edge v hv hva d (hM.1.1 d hd) hyd
          exact common a (by rw [heq]; simp) (by rw [hdq]; simp)
      · by_cases hy : y = u
        · subst y
          have hxv : x = v := by
            have hh := congrArg Subtype.val hxy
            simpa [f, hx] using hh
          subst x
          have heq := leaf_edge v hv hva e (hM.1.1 e he) hxe
          have hdq := leaf_edge u hu hua d (hM.1.1 d hd) hyd
          exact common a (by rw [heq]; simp) (by rw [hdq]; simp)
        · have h : x = y := by
            have hh := congrArg Subtype.val hxy
            simpa [f, hx, hy] using hh
          subst y
          exact common x hxe hyd
    have him : H.IsEdgeMatching (M.image (Sym2.map f)) := by
      constructor
      · intro e he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
        have hedge := hM.1.1 d hd
        induction d using Sym2.inductionOn with
        | _ x y => exact fold_adj x y (by simpa using hedge)
      · intro e he d hd
        obtain ⟨e0, he0, heq⟩ := Finset.mem_image.mp he
        obtain ⟨d0, hd0, hdq⟩ := Finset.mem_image.mp hd
        subst e d
        by_cases hed : e0 = d0
        · exact Or.inl (congrArg (Sym2.map f) hed)
        · right
          intro z hz
          obtain ⟨x, hxe, hxz⟩ := Sym2.mem_map.mp hz.1
          obtain ⟨y, hyd, hyz⟩ := Sym2.mem_map.mp hz.2
          exact hed (collision e0 he0 d0 hd0 x y hxe hyd (hxz.trans hyz.symm))
    have hmax : H.IsMaximalEdgeMatching (M.image (Sym2.map f)) := by
      apply (blocked_iff H _).mpr
      refine ⟨him, ?_⟩
      intro e he
      induction e using Sym2.inductionOn with
      | _ x y =>
        have hxy : G.Adj x.val y.val := by simpa [H] using he
        obtain ⟨d, hd, z, hz, hzd⟩ :=
          (blocked_iff G M).mp hM |>.2 s(x.val, y.val) (by simpa using hxy)
        refine ⟨Sym2.map f d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, f z, ?_,
          Sym2.mem_map.mpr ⟨z, hzd, rfl⟩⟩
        rcases Sym2.mem_iff.mp hz with hz | hz
        · subst z
          simp [f_retained]
        · subst z
          simp [f_retained]
    have hinj : Set.InjOn (Sym2.map f) (↑M : Set (Sym2 V)) := by
      intro e he d hd hmap
      induction e using Sym2.inductionOn with
      | _ x y =>
        have hx : f x ∈ Sym2.map f d := by rw [← hmap]; simp
        obtain ⟨z, hzd, hz⟩ := Sym2.mem_map.mp hx
        exact collision s(x, y) he d hd x z (by simp) hzd hz.symm
    exact ⟨hmax, Finset.card_image_iff.mpr hinj⟩
  · intro N hN
    have val_inj : Function.Injective (fun x : W => x.val) := Subtype.val_injective
    have emap_inj : Function.Injective (Sym2.map (fun x : W => x.val)) :=
      Sym2.map.injective val_inj
    have him : G.IsEdgeMatching (N.image (Sym2.map Subtype.val)) := by
      constructor
      · intro e he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
        have hedge := hN.1.1 d hd
        induction d using Sym2.inductionOn with
        | _ x y => simpa [H] using hedge
      · intro e he d hd
        obtain ⟨e0, he0, heq⟩ := Finset.mem_image.mp he
        obtain ⟨d0, hd0, hdq⟩ := Finset.mem_image.mp hd
        subst e d
        rcases hN.1.2 e0 he0 d0 hd0 with hed | hed
        · exact Or.inl (congrArg (Sym2.map Subtype.val) hed)
        · right
          intro z hz
          obtain ⟨x, hxe, hxz⟩ := Sym2.mem_map.mp hz.1
          obtain ⟨y, hyd, hyz⟩ := Sym2.mem_map.mp hz.2
          have hxy : x = y := val_inj (hxz.trans hyz.symm)
          exact hed x ⟨hxe, hxy ▸ hyd⟩
    have hau : a ≠ u := hua.ne.symm
    let va : W := ⟨v, Ne.symm huv⟩
    let aa : W := ⟨a, hau⟩
    have haa : ∃ d ∈ N, aa ∈ d := by
      have hvaH : s(va, aa) ∈ H.edgeSet := by simpa [H, va, aa] using hva
      obtain ⟨d, hd, z, hz, hzd⟩ := (blocked_iff H N).mp hN |>.2 s(va, aa) hvaH
      rcases Sym2.mem_iff.mp hz with hz | hz
      · subst z
        have hvd : v ∈ Sym2.map Subtype.val d := Sym2.mem_map.mpr ⟨va, hzd, rfl⟩
        have hedge : Sym2.map Subtype.val d ∈ G.edgeSet :=
          him.1 _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
        have heq := leaf_edge v hv hva (Sym2.map Subtype.val d) hedge hvd
        have ha : a ∈ Sym2.map Subtype.val d := by rw [heq]; simp
        obtain ⟨x, hxd, hxa⟩ := Sym2.mem_map.mp ha
        have hx : x = aa := Subtype.ext hxa
        exact ⟨d, hd, hx ▸ hxd⟩
      · subst z
        exact ⟨d, hd, hzd⟩
    have hmax : G.IsMaximalEdgeMatching (N.image (Sym2.map Subtype.val)) := by
      apply (blocked_iff G _).mpr
      refine ⟨him, ?_⟩
      intro e he
      by_cases hue : u ∈ e
      · have heq := leaf_edge u hu hua e he hue
        obtain ⟨d, hd, had⟩ := haa
        refine ⟨Sym2.map Subtype.val d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, a, ?_,
          Sym2.mem_map.mpr ⟨aa, had, rfl⟩⟩
        rw [heq]
        simp
      · induction e using Sym2.inductionOn with
        | _ x y =>
          have hxu : x ≠ u := by intro h; subst x; exact hue (by simp)
          have hyu : y ≠ u := by intro h; subst y; exact hue (by simp)
          let xx : W := ⟨x, hxu⟩
          let yy : W := ⟨y, hyu⟩
          have hxy : s(xx, yy) ∈ H.edgeSet := by simpa [H, xx, yy] using he
          obtain ⟨d, hd, z, hz, hzd⟩ := (blocked_iff H N).mp hN |>.2 s(xx, yy) hxy
          refine ⟨Sym2.map Subtype.val d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, z.val, ?_,
            Sym2.mem_map.mpr ⟨z, hzd, rfl⟩⟩
          rcases Sym2.mem_iff.mp hz with hz | hz
          · subst z
            simp [xx]
          · subst z
            simp [yy]
    exact ⟨hmax, Finset.card_image_of_injective N emap_inj⟩

end D5.S3.Combinatorics.Graph.RedundantLeafMatching
