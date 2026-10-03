/- GID: D5/S3/Combinatorics/Graph/AdjacentSupportPayment
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/AdjacentSupportPayment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Adjacent nonleaf supports pay for actual induced deletion with retained leaf charges. -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Rat.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-
Source: google-deepmind/formal-conjectures,
revision df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1,
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/HarmonicIndex.lean.
Copyright 2026 The Formal Conjectures Authors (harmonicIndex).
This file adds graph models and a payment theorem to the unchanged harmonicIndex body.
Retire this transplant when this project's pinned Mathlib contains an equivalent
harmonicIndex with the same unordered-edge and degree conventions.

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

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The harmonic index of `G`, defined as `∑_{uv ∈ E(G)} 2 / (deg u + deg v)`,
where `deg` is the degree of a vertex. This is a standard topological index in
chemical graph theory, introduced by Fajtlowicz. -/
def harmonicIndex (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => (2 : ℚ) / ((G.degree u : ℚ) + (G.degree v : ℚ)),
      fun u v => by simp only [add_comm]⟩

end SimpleGraph

namespace D5.S3.Combinatorics.Graph.AdjacentSupportPayment

open Finset SimpleGraph
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The residual uses the retained vertex subtype and recomputes all degrees. -/
abbrev residual (G : SimpleGraph V) (X : Finset V) : SimpleGraph {v : V // v ∉ X} :=
  G.induce {v | v ∉ X}

/-- The defect uses rational subtraction, including when the first degree is smaller. -/
def degreeDefect (d e : ℕ) : ℚ :=
  ((d : ℚ) - (e : ℚ)) ^ 2 / (2 * (d : ℚ) * (e : ℚ) * ((d : ℚ) + (e : ℚ)))

/-- The undirected defect sum uses the degrees of its argument graph. -/
def harmonicDefect (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  ∑ e ∈ G.edgeFinset, e.lift ⟨fun u v => degreeDefect (G.degree u) (G.degree v),
    fun u v => by simp only [degreeDefect]; congr 1 <;> ring⟩

/-- Isolated vertices are excluded from the reciprocal-degree identity. -/
def nonisolatedCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun v => G.degree v ≠ 0)).card


set_option maxHeartbeats 4000000 in
/-- Deleting two adjacent nonleaf supports with original pendant neighbors costs at least 21/20. -/
theorem adjacent_support_harmonic_payment (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hmax : G.maxDegree ≤ 4)
    (hone : ∀ x, (G.neighborFinset x |>.filter fun y => G.degree y = 1).card ≤ 1)
    (a b u_leaf v_leaf : V) (hab : G.Adj a b)
    (ha : 2 ≤ G.degree a) (hb : 2 ≤ G.degree b)
    (hu : G.degree u_leaf = 1) (hau : G.Adj a u_leaf)
    (hv : G.degree v_leaf = 1) (hbv : G.Adj b v_leaf) :
    (21/20 : ℚ) ≤ G.harmonicIndex - (residual G {a,b}).harmonicIndex := by
  classical
  have isolate (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
      (hpos : ∀ v, G.degree v ≠ 0) :
      let Q := residual G X
      let i := (Finset.univ.filter fun v => Q.degree v = 0).card
      G.harmonicIndex - Q.harmonicIndex =
        ((X.card : ℚ)+(i : ℚ))/2 - (harmonicDefect G - harmonicDefect Q) := by
    classical
    dsimp only
    let Q := residual G X
    let I := Finset.univ.filter fun v => Q.degree v = 0
    change G.harmonicIndex - Q.harmonicIndex =
      ((X.card : ℚ)+(I.card : ℚ))/2 - (harmonicDefect G - harmonicDefect Q)
    have accounting {W : Type u} [Fintype W] [DecidableEq W]
        (F : SimpleGraph W) [DecidableRel F.Adj] :
        F.harmonicIndex = (nonisolatedCount F : ℚ)/2 - harmonicDefect F := by
      classical
      have oriented : ∀ (f : W → W → ℚ) (hsym : ∀ v w, f v w = f w v),
          (∑ d : F.Dart, f d.fst d.snd) =
            2 * ∑ e ∈ F.edgeFinset, e.lift ⟨f, hsym⟩ := by
        intro f hsym
        rw [← Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset F.Dart)) (t := F.edgeFinset)
          (g := SimpleGraph.Dart.edge) (fun d _ => F.mem_edgeFinset.mpr d.edge_mem)
          (fun d => f d.fst d.snd)]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        have hf : ∀ d ∈ (Finset.univ.filter fun d : F.Dart => d.edge = e),
            f d.fst d.snd = e.lift ⟨f, hsym⟩ := by
          intro d hd
          have hde := (Finset.mem_filter.mp hd).2
          rw [← hde]
          rfl
        rw [Finset.sum_congr rfl hf, Finset.sum_const, nsmul_eq_mul,
          F.dart_edge_fiber_card e (F.mem_edgeFinset.mp he)]
        norm_num
      have reciprocal : (∑ d : F.Dart, (1 : ℚ) / (F.degree d.fst : ℚ)) =
          (nonisolatedCount F : ℚ) := by
        rw [← Finset.sum_fiberwise' (Finset.univ : Finset F.Dart)
          (fun d => d.fst) (fun v => (1 : ℚ) / (F.degree v : ℚ))]
        simp only [Finset.sum_const, nsmul_eq_mul, F.dart_fst_fiber_card_eq_degree]
        unfold nonisolatedCount
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : F.degree v = 0
        · simp [hv]
        · simp [hv]
      have reciprocal_symm : (∑ d : F.Dart, (1 : ℚ) / (F.degree d.snd : ℚ)) =
          (∑ d : F.Dart, (1 : ℚ) / (F.degree d.fst : ℚ)) := by
        refine Finset.sum_bij (fun d _ => d.symm) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
        · intro d hd e he hde
          exact SimpleGraph.Dart.symm_involutive.injective hde
        · intro d _
          exact ⟨d.symm, Finset.mem_univ _, d.symm_symm⟩
        · intro d _
          rfl
      have pointwise : ∀ d : F.Dart,
          (2 : ℚ) / ((F.degree d.fst : ℚ) + (F.degree d.snd : ℚ)) =
            1 / (2 * (F.degree d.fst : ℚ)) + 1 / (2 * (F.degree d.snd : ℚ)) -
              degreeDefect (F.degree d.fst) (F.degree d.snd) := by
        intro d
        have hv : (F.degree d.fst : ℚ) ≠ 0 := by exact_mod_cast d.adj.degree_pos_left.ne'
        have hw : (F.degree d.snd : ℚ) ≠ 0 := by exact_mod_cast d.adj.degree_pos_right.ne'
        have hs : (F.degree d.fst : ℚ) + (F.degree d.snd : ℚ) ≠ 0 := by
          have hvp : (0 : ℚ) < F.degree d.fst := by exact_mod_cast d.adj.degree_pos_left
          have hwp : (0 : ℚ) < F.degree d.snd := by exact_mod_cast d.adj.degree_pos_right
          linarith
        unfold degreeDefect
        field_simp
        ring
      have hh := oriented (fun v w => (2 : ℚ) / ((F.degree v : ℚ) + (F.degree w : ℚ)))
        (fun v w => by simp only [add_comm])
      have hd := oriented (fun v w => degreeDefect (F.degree v) (F.degree w))
        (fun v w => by simp only [degreeDefect]; congr 1 <;> ring)
      change (∑ d : F.Dart, (2 : ℚ) / ((F.degree d.fst : ℚ) + (F.degree d.snd : ℚ))) =
        2 * F.harmonicIndex at hh
      change (∑ d : F.Dart, degreeDefect (F.degree d.fst) (F.degree d.snd)) =
        2 * harmonicDefect F at hd
      have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset F.Dart)) rfl
        (fun d _ => pointwise d)
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
      have hfirst : (∑ d : F.Dart, (1 : ℚ) / (2 * (F.degree d.fst : ℚ))) =
          (nonisolatedCount F : ℚ) / 2 := by
        calc
          _ = ∑ d : F.Dart, ((1 : ℚ) / (F.degree d.fst : ℚ)) / 2 := by
            apply Finset.sum_congr rfl
            intro d _
            ring
          _ = _ := by rw [← Finset.sum_div, reciprocal]
      have hsecond : (∑ d : F.Dart, (1 : ℚ) / (2 * (F.degree d.snd : ℚ))) =
          (nonisolatedCount F : ℚ) / 2 := by
        calc
          _ = ∑ d : F.Dart, ((1 : ℚ) / (F.degree d.snd : ℚ)) / 2 := by
            apply Finset.sum_congr rfl
            intro d _
            ring
          _ = _ := by rw [← Finset.sum_div, reciprocal_symm, reciprocal]
      linarith [hsum]
    have gnon : nonisolatedCount G = Fintype.card V := by
      unfold nonisolatedCount
      have eq : (Finset.univ.filter fun v => G.degree v ≠ 0) = Finset.univ := by
        ext v
        simp [hpos v]
      rw [eq, Finset.card_univ]
    have qnon : nonisolatedCount Q + I.card = Fintype.card {v : V // v ∉ X} := by
      simpa only [nonisolatedCount,I,not_not,Finset.card_univ] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun v => Q.degree v ≠ 0)
    have qcard : Fintype.card {v : V // v ∉ X} + X.card = Fintype.card V := by
      have h := Fintype.card_subtype_compl (fun v : V => v ∈ X)
      have h' : Fintype.card {v : V // v ∈ X} = X.card := Fintype.card_coe X
      rw [h'] at h
      have hc : X.card ≤ Fintype.card V := by
        simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ X)
      omega
    have a := accounting G
    have b := accounting Q
    rw [gnon] at a
    have hnat : nonisolatedCount Q + I.card + X.card = Fintype.card V := by omega
    have hq : (nonisolatedCount Q : ℚ) + (I.card : ℚ) + (X.card : ℚ) = Fintype.card V := by
      exact_mod_cast hnat
    linarith

  let X : Finset V := {a,b}
  let q (v : V) := (G.neighborFinset v \ X).card
  let r (v : V) := (G.neighborFinset v ∩ X).card
  let t (v : V) := (G.neighborFinset v |>.filter fun w => G.degree w = 1).card
  let m (d k : ℕ) : ℚ := if k = 0 then 0 else if d = 3 then 1/60
    else if d = 4 then if k = 1 then 1/40 else 1/24 else 0
  let c (v : V) : ℚ := if G.degree v = 1 then 0 else
    if G.degree v = 2 then if t v = 0 then 0 else 1/12 else
    if G.degree v = 3 then if t v = 0 then 1/30 else 1/10 else
    if t v = 0 then 3/40 else 13/120
  let K (d : ℕ) : ℚ := if d = 2 then 3/20 else if d = 3 then 4/35 else 1/8
  have symm (d e : ℕ) : degreeDefect d e = degreeDefect e d := by
    simp only [degreeDefect]; congr 1 <;> ring
  have xpos (v : V) (h : v ∈ X) : 2 ≤ G.degree v := by
    simp only [X,Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> assumption
  letI : Nontrivial V := ⟨⟨a,b,hab.ne⟩⟩
  have positive (v : V) : 0 < G.degree v := hc.preconnected.degree_pos_of_nontrivial v
  have maxdeg (v : V) : G.degree v ≤ 4 := (G.degree_le_maxDegree v).trans hmax
  have ds (v : V) : q v + r v = G.degree v := by
    simpa [q,r] using Finset.card_sdiff_add_card_inter (G.neighborFinset v) X
  have rmax (v : V) : r v ≤ 2 := by
    have h := Finset.card_le_card (Finset.inter_subset_right (s₁ := G.neighborFinset v) (s₂ := X))
    have hx : X.card = 2 := by simp [X,hab.ne]
    simpa only [r,hx] using h
  have tmax (v : V) : t v ≤ 1 := hone v
  have leafRetained (v : V) (hv : G.degree v = 1) : v ∉ X := by
    intro hx; have hh := xpos v hx; omega
  have leafq (v w : V) (hadj : G.Adj v w) (hw : G.degree w = 1)
      (hvX : v ∉ X) : q w = 1 := by
    obtain ⟨z,hz,huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hw
    have hn : G.neighborFinset w = {v} := by
      ext x
      simp only [G.mem_neighborFinset,Finset.mem_singleton]
      constructor
      · intro hx; exact (huniq x hx).trans (huniq v hadj.symm).symm
      · rintro rfl; exact hadj.symm
    have he : ({v} : Finset V) \ X = {v} := by
      ext x; simp only [Finset.mem_sdiff,Finset.mem_singleton]; aesop
    simp only [q,hn,he,Finset.card_singleton]
  have leafc (v : V) (hv : G.degree v = 1) : c v = 0 := by simp [c,hv]
  have cpos (v : V) : 0 ≤ c v := by unfold c; split_ifs <;> norm_num
  have mpos (d k : ℕ) : 0 ≤ m d k := by unfold m; split_ifs <;> norm_num
  have tq (v : V) : t v ≤ q v := by
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hwN,hw1⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_sdiff.mpr ⟨hwN,leafRetained w hw1⟩
  have pullback : harmonicDefect (residual G X) =
      ∑ e ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∉ X),
        e.lift ⟨fun v w => degreeDefect (q v) (q w), fun v w => symm _ _⟩ := by
    let Q := residual G X
    let liftEdge := (Function.Embedding.subtype (fun v : V => v ∉ X)).sym2Map
    have edgeMap : Q.edgeFinset.map liftEdge =
        G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∉ X) := by
      calc
        _ = G.edgeFinset ∩ ({v : V | v ∉ X} : Set V).toFinset.sym2 :=
          G.map_edgeFinset_induce (s := {v | v ∉ X})
        _ = _ := by ext e; induction e using Sym2.ind with
                   | _ v w => simp [Finset.mem_sym2_iff]
    have deg (v : {v : V // v ∉ X}) : Q.degree v = q v.val := by
      have hc := congrArg Finset.card (G.map_neighborFinset_induce (s := {v | v ∉ X}) v)
      have hn : G.neighborFinset v.val ∩ ({v : V | v ∉ X} : Set V).toFinset =
          G.neighborFinset v.val \ X := by ext w; simp
      change ((G.induce {v | v ∉ X}).neighborFinset v).card = _
      simpa only [Finset.card_map, hn] using hc
    rw [← edgeMap, Finset.sum_map]
    unfold harmonicDefect
    apply Finset.sum_congr rfl
    intro e _
    induction e using Sym2.ind with
    | _ v w =>
      simp only [liftEdge, Function.Embedding.sym2Map, Sym2.lift_mk]
      change degreeDefect (Q.degree v) (Q.degree w) = _
      rw [deg,deg]
      rfl
  have oriented (f : V → V → ℚ) (hsym : ∀ v w, f v w = f w v) :
      (∑ d : G.Dart, f d.fst d.snd) =
        2 * ∑ e ∈ G.edgeFinset, e.lift ⟨f,hsym⟩ := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset G.Dart)) (t := G.edgeFinset)
      (g := SimpleGraph.Dart.edge) (fun d _ => G.mem_edgeFinset.mpr d.edge_mem)
      (fun d => f d.fst d.snd), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hf : ∀ d ∈ (Finset.univ.filter fun d : G.Dart => d.edge = e),
        f d.fst d.snd = e.lift ⟨f,hsym⟩ := by
      intro d hd; rw [← (Finset.mem_filter.mp hd).2]; rfl
    rw [Finset.sum_congr rfl hf, Finset.sum_const, nsmul_eq_mul,
      G.dart_edge_fiber_card e (G.mem_edgeFinset.mp he)]
    norm_num
  have reindex (f : V → V → ℚ) :
      (∑ d : G.Dart, f d.fst d.snd) = ∑ v, ∑ w ∈ G.neighborFinset v, f v w := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset G.Dart) (fun d => d.fst)]
    apply Finset.sum_congr rfl
    intro v _
    refine Finset.sum_bij (fun d _ => d.snd) ?_ ?_ ?_ ?_
    · intro d hd; exact (G.mem_neighborFinset v d.snd).mpr ((Finset.mem_filter.mp hd).2 ▸ d.adj)
    · intro d hd e he hde
      apply SimpleGraph.Dart.ext
      exact Prod.ext ((Finset.mem_filter.mp hd).2.trans (Finset.mem_filter.mp he).2.symm) hde
    · intro w hw
      let d : G.Dart := ⟨(v,w), (G.mem_neighborFinset v w).mp hw⟩
      exact ⟨d, by simp [d], rfl⟩
    · intro d hd; simp only [(Finset.mem_filter.mp hd).2]
  let A (v w : V) : ℚ := if G.degree v = 1 then 0 else
    if G.degree w = 1 then degreeDefect (G.degree v) 1 - degreeDefect (q v) 1
    else if G.degree w < G.degree v then m (G.degree v) (r v) else 0
  let F (v w : V) : ℚ := if v ∉ X ∧ w ∉ X then degreeDefect (q v) (q w) else 0
  let B (v w : V) : ℚ := if v ∈ X then
    if w ∈ X then degreeDefect (G.degree v) (G.degree w)/2
    else degreeDefect (G.degree v) (G.degree w) + c w
    else if w ∈ X then -c v else A v w
  have Fsym (v w : V) : F v w = F w v := by simp only [F,and_comm,symm]
  have residual_all : harmonicDefect (residual G X) =
      ∑ e ∈ G.edgeFinset, e.lift ⟨F,Fsym⟩ := by
    rw [pullback,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he; induction e using Sym2.ind with
    | _ v w => simp [F]
  have edgeCharge (v w : V) (hadj : G.Adj v w) (hvX : v ∉ X) (hwX : w ∉ X) :
      degreeDefect (G.degree v) (G.degree w) - degreeDefect (q v) (q w) ≤
        A v w + A w v := by
    have qvpos : 0 < q v := Finset.card_pos.mpr
      ⟨w,Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset v w).mpr hadj,hwX⟩⟩
    have qwpos : 0 < q w := Finset.card_pos.mpr
      ⟨v,Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset w v).mpr hadj.symm,hvX⟩⟩
    have dvpos := positive v; have dwpos := positive w
    have dvmax := maxdeg v; have dwmax := maxdeg w
    have dsv := ds v; have dsw := ds w
    have rvm := rmax v; have rwm := rmax w
    by_cases hv1 : G.degree v = 1
    · have hqv := leafq w v hadj.symm hv1 hwX
      by_cases hw1 : G.degree w = 1
      · have hqw := leafq v w hadj hw1 hvX
        simp [A,hv1,hw1,hqv,hqw,degreeDefect]
      · simp [A,hv1,hw1,hqv,symm]
    · by_cases hw1 : G.degree w = 1
      · have hqw := leafq v w hadj hw1 hvX
        simp [A,hw1,hv1,hqw]
      · have phipos (d e : ℕ) : 0 ≤ degreeDefect d e := by
          unfold degreeDefect; positivity
        have scalar (d e k h : ℕ) (hd2 : 2 ≤ d) (hd4 : d ≤ 4)
            (he2 : 2 ≤ e) (he4 : e ≤ 4) (he : e < d)
            (hk : k ≤ 2) (hh : h ≤ 2) (hkd : k < d) (hhe : h < e) :
            degreeDefect d e - degreeDefect (d-k) (e-h) ≤ m d k := by
          interval_cases d <;> interval_cases e <;> first | omega | skip
          all_goals interval_cases k <;> interval_cases h <;>
            first | omega | norm_num [degreeDefect,m]
        have eqv : q v = G.degree v - r v := by omega
        have eqw : q w = G.degree w - r w := by omega
        have dv2 : 2 ≤ G.degree v := by omega
        have dw2 : 2 ≤ G.degree w := by omega
        have rvd : r v < G.degree v := by omega
        have rwd : r w < G.degree w := by omega
        by_cases hlt : G.degree w < G.degree v
        · have hnot : ¬ G.degree v < G.degree w := by omega
          simp only [A,hv1,hw1,if_false,hlt,hnot,if_true,add_zero]
          rw [eqv,eqw]
          exact scalar _ _ _ _ dv2 dvmax dw2 dwmax hlt rvm rwm rvd rwd
        · by_cases hgt : G.degree v < G.degree w
          · simp only [A,hv1,hw1,if_false,hlt,hgt,if_true,zero_add]
            rw [eqv,eqw,symm (G.degree v) (G.degree w),symm (G.degree v-r v) (G.degree w-r w)]
            exact scalar _ _ _ _ dw2 dwmax dv2 dvmax hgt rwm rvm rwd rvd
          · have heq : G.degree v = G.degree w := by omega
            simp only [A,hv1,hw1,hlt,hgt,if_false,add_zero]
            rw [heq]
            have hz : degreeDefect (G.degree w) (G.degree w) = 0 := by simp [degreeDefect]
            rw [hz]
            linarith [phipos (q v) (q w)]
  have eb (v w : V) (hadj : G.Adj v w) :
      degreeDefect (G.degree v) (G.degree w) - F v w ≤ B v w + B w v := by
    by_cases hvX : v ∈ X
    · by_cases hwX : w ∈ X
      · simp [B,F,hvX,hwX,symm]
      · simp [B,F,hvX,hwX,symm]
    · by_cases hwX : w ∈ X
      · simp [B,F,hvX,hwX,symm]
      · simpa [B,F,hvX,hwX] using edgeCharge v w hadj hvX hwX
  have rowCharge (v : V) (hvX : v ∉ X) :
      (∑ w ∈ G.neighborFinset v \ X, A v w) ≤ (r v : ℚ)*c v := by
    by_cases hv1 : G.degree v = 1
    · simp [A,hv1,c]
    · let N := G.neighborFinset v \ X
      let L := N.filter fun w => G.degree w = 1
      let R := N.filter fun w => G.degree w ≠ 1
      have lcard : L.card = t v := by
        congr 1
        ext w
        simp only [L,N,Finset.mem_filter,Finset.mem_sdiff]
        constructor
        · rintro ⟨⟨hn,_⟩,hl⟩; exact ⟨hn,hl⟩
        · rintro ⟨hn,hl⟩; exact ⟨⟨hn,leafRetained w hl⟩,hl⟩
      have rcard : R.card = q v - t v := by
        have h := Finset.card_filter_add_card_filter_not (s := N) (fun w => G.degree w = 1)
        change L.card + R.card = q v at h
        rw [lcard] at h
        omega
      have splitSum : (∑ w ∈ N, A v w) = (∑ w ∈ L, A v w) + ∑ w ∈ R, A v w := by
        simpa only [L,R] using (Finset.sum_filter_add_sum_filter_not N (fun w => G.degree w = 1) (fun w => A v w)).symm
      have leafSum : (∑ w ∈ L, A v w) =
          (t v : ℚ)*(degreeDefect (G.degree v) 1 - degreeDefect (q v) 1) := by
        have point (w : V) (hw : w ∈ L) : A v w = degreeDefect (G.degree v) 1 - degreeDefect (q v) 1 := by
          simp [A,hv1,(Finset.mem_filter.mp hw).2]
        rw [Finset.sum_congr rfl point]
        rw [Finset.sum_const,nsmul_eq_mul,lcard]
      have restSum : (∑ w ∈ R, A v w) ≤ ((q v-t v : ℕ) : ℚ)*m (G.degree v) (r v) := by
        calc
          _ ≤ ∑ _w ∈ R, m (G.degree v) (r v) := by
            apply Finset.sum_le_sum
            intro w hw
            have hw1 := (Finset.mem_filter.mp hw).2
            simp only [A,hv1,if_false,hw1]
            split_ifs <;> first | exact le_refl _ | exact mpos _ _
          _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,rcard]
      have hh : (∑ w ∈ N, A v w) ≤
          (t v : ℚ)*(degreeDefect (G.degree v) 1-degreeDefect (q v) 1) +
            ((q v-t v : ℕ) : ℚ)*m (G.degree v) (r v) := by
        linarith only [splitSum,leafSum,restSum]
      have dvpos := positive v; have dvmax := maxdeg v
      have dsv := ds v; have rvm := rmax v; have tvm := tmax v; have tvq := tq v
      have dv2 : 2 ≤ G.degree v := by omega
      have numeric : (t v : ℚ)*(degreeDefect (G.degree v) 1-degreeDefect (q v) 1) +
          ((q v-t v : ℕ) : ℚ)*m (G.degree v) (r v) ≤ (r v : ℚ)*c v := by
        have eqv : q v = G.degree v - r v := by omega
        dsimp only [c]
        rw [eqv]
        interval_cases G.degree v <;> interval_cases r v <;> interval_cases t v <;>
          first | omega | norm_num [m,degreeDefect]
      exact hh.trans numeric
  have retainedRow (v : V) (hvX : v ∉ X) : ∑ w ∈ G.neighborFinset v, B v w ≤ 0 := by
    have eq : (∑ w ∈ G.neighborFinset v, B v w) =
        (∑ w ∈ G.neighborFinset v \ X, A v w) - (r v : ℚ)*c v := by
      have disj : Disjoint (G.neighborFinset v \ X) (G.neighborFinset v ∩ X) :=
        Finset.disjoint_sdiff_inter _ _
      have split : (G.neighborFinset v \ X) ∪ (G.neighborFinset v ∩ X) = G.neighborFinset v :=
        Finset.sdiff_union_inter _ _
      have h1 : (∑ w ∈ G.neighborFinset v \ X, B v w) = ∑ w ∈ G.neighborFinset v \ X, A v w := by
        apply Finset.sum_congr rfl
        intro w hw; simp [B,hvX,(Finset.mem_sdiff.mp hw).2]
      have h2 : (∑ w ∈ G.neighborFinset v ∩ X, B v w) = -(r v : ℚ)*c v := by
        have point (w : V) (hw : w ∈ G.neighborFinset v ∩ X) : B v w = -c v := by
          simp [B,hvX,(Finset.mem_inter.mp hw).2]
        rw [Finset.sum_congr rfl point]
        simp [r,Finset.sum_const,nsmul_eq_mul]
      calc
        _ = (∑ w ∈ G.neighborFinset v \ X, B v w) + ∑ w ∈ G.neighborFinset v ∩ X, B v w := by
          rw [← Finset.sum_union disj,split]
        _ = _ := by rw [h1,h2]; ring
    rw [eq]; linarith [rowCharge v hvX]
  have cap (d : ℕ) (hd2 : 2 ≤ d) (hd4 : d ≤ 4) (w : V) (hw2 : 2 ≤ G.degree w) :
      degreeDefect d (G.degree w) + c w ≤ K d := by
    have hw4 := maxdeg w; have ht := tmax w
    dsimp only [c]
    interval_cases d <;> interval_cases G.degree w <;> interval_cases t w <;>
      norm_num [degreeDefect,K]
  have deletedRow (v z l : V) (hvX : v ∈ X) (hzX : z ∈ X)
      (hvz : G.Adj v z) (hvl : G.Adj v l) (hl : G.degree l = 1)
      (hx : X = {v,z}) :
      (∑ w ∈ G.neighborFinset v, B v w) ≤
        degreeDefect (G.degree v) 1 + degreeDefect (G.degree v) (G.degree z)/2 +
          ((G.degree v-2 : ℕ) : ℚ)*K (G.degree v) := by
    have vlne : v ≠ l := hvl.ne
    have zlne : z ≠ l := by have hh := xpos z hzX; intro he; rw [he,hl] at hh; omega
    have hzN : z ∈ G.neighborFinset v := (G.mem_neighborFinset v z).mpr hvz
    have hlN : l ∈ G.neighborFinset v := (G.mem_neighborFinset v l).mpr hvl
    let R := G.neighborFinset v \ {z,l}
    have rc : R.card = G.degree v - 2 := by
      have hs : ({z,l} : Finset V) ⊆ G.neighborFinset v := by simp [Finset.insert_subset_iff,hzN,hlN]
      rw [Finset.card_sdiff_of_subset hs]
      simp [zlne,G.card_neighborFinset_eq_degree,R]
    have noleaf (w : V) (hw : w ∈ R) : G.degree w ≠ 1 := by
      intro hw1
      have hn := (Finset.mem_sdiff.mp hw).1
      have hnz := (Finset.mem_sdiff.mp hw).2
      have heq : (G.neighborFinset v |>.filter fun y => G.degree y = 1) = {l} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨by simp [hlN,hl],?_⟩
        intro y hy
        exact Finset.card_le_one.mp (hone v) y hy l (by simp [hlN,hl])
      have he : w = l := by simpa [heq] using (show w ∈ (G.neighborFinset v |>.filter fun y => G.degree y = 1) from by simp [hn,hw1])
      exact hnz (by simp [he])
    have splitN : G.neighborFinset v = insert z (insert l R) := by
      ext w
      simp only [Finset.mem_insert,Finset.mem_sdiff,R]
      constructor
      · intro hw
        by_cases hwz : w = z
        · exact Or.inl hwz
        · by_cases hwl : w = l
          · exact Or.inr (Or.inl hwl)
          · exact Or.inr (Or.inr ⟨hw,by simp [hwz,hwl]⟩)
      · rintro (rfl|rfl|hw)
        · exact hzN
        · exact hlN
        · exact hw.1
    have hzR : z ∉ insert l R := by simp [R,zlne]
    have hlR : l ∉ R := by simp [R]
    rw [splitN,Finset.sum_insert hzR,Finset.sum_insert hlR]
    have zterm : B v z = degreeDefect (G.degree v) (G.degree z)/2 := by simp [B,hvX,hzX]
    have lterm : B v l = degreeDefect (G.degree v) 1 := by simp [B,hvX,leafRetained l hl,leafc l hl,hl]
    rw [zterm,lterm]
    have rest : (∑ w ∈ R, B v w) ≤ ((G.degree v-2 : ℕ) : ℚ)*K (G.degree v) := by
      calc
        _ ≤ ∑ _w ∈ R, K (G.degree v) := by
          apply Finset.sum_le_sum
          intro w hw
          have hwX : w ∉ X := by
            rw [hx]; simp only [Finset.mem_insert,Finset.mem_singleton]
            rintro (he|he)
            · exact ((G.mem_neighborFinset v w).mp (Finset.mem_sdiff.mp hw).1).ne he.symm
            · exact (Finset.mem_sdiff.mp hw).2 (by simp [he])
          have hw2 : 2 ≤ G.degree w := by have hp := positive w; have hh := noleaf w hw; omega
          simpa [B,hvX,hwX] using cap (G.degree v) (xpos v hvX) (maxdeg v) w hw2
        _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,rc]
    linarith
  have wholeBound : harmonicDefect G - harmonicDefect (residual G X) ≤ 19/20 := by
    have summed := Finset.sum_le_sum (s := (Finset.univ : Finset G.Dart))
      (fun d _ => eb d.fst d.snd d.adj)
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib] at summed
    have swap : (∑ d : G.Dart, B d.snd d.fst) = ∑ d : G.Dart, B d.fst d.snd := by
      refine Finset.sum_bij (fun d _ => d.symm) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro d hd e he hde; exact SimpleGraph.Dart.symm_involutive.injective hde
      · intro d _; exact ⟨d.symm,Finset.mem_univ _,d.symm_symm⟩
      · intro d _; rfl
    have ho := oriented (fun v w => degreeDefect (G.degree v) (G.degree w)) (fun v w => symm _ _)
    change (∑ d : G.Dart, degreeDefect (G.degree d.fst) (G.degree d.snd)) = 2*harmonicDefect G at ho
    have hr := oriented F Fsym
    rw [← residual_all] at hr
    rw [ho,hr,swap,reindex] at summed
    have rows : (∑ v, ∑ w ∈ G.neighborFinset v, B v w) ≤
        (∑ w ∈ G.neighborFinset a, B a w) + ∑ w ∈ G.neighborFinset b, B b w := by
      calc
        _ ≤ ∑ v, if v ∈ X then ∑ w ∈ G.neighborFinset v, B v w else 0 := by
          apply Finset.sum_le_sum
          intro v _; by_cases hvX : v ∈ X
          · simp [hvX]
          · simpa [hvX] using retainedRow v hvX
        _ = _ := by
          rw [← Finset.sum_filter]
          have he : (Finset.univ.filter fun v => v ∈ X) = X := by ext v; simp
          rw [he]
          simp [X,hab.ne]
    have ra := deletedRow a b u_leaf (by simp [X]) (by simp [X]) hab hau hu rfl
    have rb := deletedRow b a v_leaf (by simp [X]) (by simp [X]) hab.symm hbv hv (by simp [X,Finset.pair_comm])
    have da4 := maxdeg a; have db4 := maxdeg b
    have num : degreeDefect (G.degree a) 1 + degreeDefect (G.degree b) 1 +
        degreeDefect (G.degree a) (G.degree b) +
        ((G.degree a-2 : ℕ) : ℚ)*K (G.degree a) +
        ((G.degree b-2 : ℕ) : ℚ)*K (G.degree b) ≤ 19/20 := by
      interval_cases G.degree a <;> interval_cases G.degree b <;> norm_num [K,degreeDefect]
    rw [symm (G.degree b) (G.degree a)] at rb
    linarith
  have xcard : X.card = 2 := by simp [X,hab.ne]
  have uvne : u_leaf ≠ v_leaf := by
    intro he
    obtain ⟨z,hz,huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu
    have h := (huniq a hau.symm).trans (huniq b (he ▸ hbv.symm)).symm
    exact hab.ne h
  let Q := residual G X
  let U : {v : V // v ∉ X} := ⟨u_leaf,leafRetained u_leaf hu⟩
  let W : {v : V // v ∉ X} := ⟨v_leaf,leafRetained v_leaf hv⟩
  have iso (l s : V) (hl : G.degree l = 1) (hsl : G.Adj s l) (hsX : s ∈ X) :
      Q.degree ⟨l,leafRetained l hl⟩ = 0 := by
    have hc := congrArg Finset.card (G.map_neighborFinset_induce (s := {v | v ∉ X}) ⟨l,leafRetained l hl⟩)
    have hn : G.neighborFinset l ∩ ({v : V | v ∉ X} : Set V).toFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw'
      obtain ⟨hw,hwn⟩ := Finset.mem_inter.mp hw'
      have hwn' : w ∉ X := by simpa only [Set.mem_toFinset,Set.mem_setOf_eq] using hwn
      obtain ⟨z,hz,huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hl
      have he : w = s := (huniq w ((G.mem_neighborFinset l w).mp hw)).trans (huniq s hsl.symm).symm
      exact hwn' (he.symm ▸ hsX)
    change ((G.induce {v | v ∉ X}).neighborFinset ⟨l,leafRetained l hl⟩).card = 0
    simpa only [Finset.card_map,hn,Finset.card_empty] using hc
  have icard : 2 ≤ (Finset.univ.filter fun v => Q.degree v = 0).card := by
    have hsub : ({U,W} : Finset _) ⊆ (Finset.univ.filter fun v => Q.degree v = 0) := by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨iso u_leaf a hu hau (by simp [X]),iso v_leaf b hv hbv (by simp [X])⟩
    have hn : U ≠ W := by intro h; exact uvne (congrArg Subtype.val h)
    simpa [hn] using Finset.card_le_card hsub
  have ident := isolate G X (fun v => (positive v).ne')
  dsimp only at ident
  rw [xcard] at ident
  have iq : (2 : ℚ) ≤ ((Finset.univ.filter fun v => Q.degree v = 0).card : ℚ) := by exact_mod_cast icard
  change (21/20 : ℚ) ≤ G.harmonicIndex - Q.harmonicIndex
  change harmonicDefect G - harmonicDefect Q ≤ 19/20 at wholeBound
  change G.harmonicIndex - Q.harmonicIndex = _ at ident
  linarith

end D5.S3.Combinatorics.Graph.AdjacentSupportPayment
