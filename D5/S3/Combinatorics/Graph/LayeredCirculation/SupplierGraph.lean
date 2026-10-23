/- GID: D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Finite typed walks retain labeled edges, endpoint flow and finite path potentials. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni

Source: https://github.com/elazarg/multitubes/tree/20d22aa7ca67f9843e5adf9edf173403a2f4033a
Modified upstream source: module layout, pinned API adaptation and retained
consumer closure follow this repository. The original circuit-existence proof is retained.

Original modules: Maths.Graph.EdgeGraph, Maths.Graph.Circulation,
Maths.Multitubes.Additive.Potentials, Maths.Multitubes.FiniteInequality.Basic,
Maths.Multitubes.FiniteInequality.Quantitative, Maths.Multitubes.Additive.Quantitative,
Maths.Multitubes.Additive.Cycles, Maths.Multitubes.Additive.Circuits,
Maths.Multitubes.Additive.CirculationDecomposition.
Retirement: when the mathlib revision pinned by this repository contains equivalent
normalized real circuit decomposition and its consumed prerequisites, replace this
transplant by direct imports and applications of those pinned declarations.

Upstream LICENSE notice:
Copyright Elazar Gershuni

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Apache-2.0 full license:
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

   Copyright 2026 The Omega Institute

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

open scoped BigOperators Matrix
namespace Maths

universe uV uE


structure EdgeGraph (V : Type uV) (E : Type uE) where

  source : E → V

  target : E → V

namespace EdgeGraph

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)
inductive Walk (start : V) : V → Type (max uV uE)
  |
    nil : Walk start start
  |
    concat {finish : V} (walkSoFar : Walk start finish) (edge : E)
      (legal : G.source edge = finish) : Walk start (G.target edge)

namespace Walk

variable {G} {start finish middle : V}


@[simp] def length {start : V} : {finish : V} → G.Walk start finish → ℕ
  | _, .nil => 0
  | _, .concat walkSoFar _ _ => walkSoFar.length + 1


def edges {start : V} : {finish : V} → G.Walk start finish → List E
  | _, .nil => []
  | _, .concat walkSoFar edge _ => walkSoFar.edges ++ [edge]


@[simp] theorem length_concat (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).length = walkSoFar.length + 1 := rfl

@[simp] private theorem edges_nil : (Walk.nil : G.Walk start start).edges = [] := rfl

@[simp] theorem edges_concat (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).edges = walkSoFar.edges ++ [edge] := rfl

@[simp] theorem edges_length (walk : G.Walk start finish) :
    walk.edges.length = walk.length := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih => simp [edges, length, ih]


def visited {start : V} : {finish : V} → G.Walk start finish → List V
  | _, .nil => [start]
  | _, .concat walkSoFar edge _ => walkSoFar.visited ++ [G.target edge]

@[simp] private theorem visited_nil : (Walk.nil : G.Walk start start).visited = [start] := rfl

@[simp] private theorem visited_concat (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).visited = walkSoFar.visited ++ [G.target edge] := rfl

@[simp] theorem length_visited (walk : G.Walk start finish) :
    walk.visited.length = walk.length + 1 := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih => simp [ih]


theorem mem_visited_of_mem_edges (walk : G.Walk start finish)
    {edge : E} (hmem : edge ∈ walk.edges) : G.target edge ∈ walk.visited := by
  induction walk with
  | nil => simp at hmem
  | concat walkSoFar e legal ih =>
      rw [edges_concat, List.mem_append, List.mem_singleton] at hmem
      rw [visited_concat]
      rcases hmem with hmem | rfl
      · exact List.mem_append_left _ (ih hmem)
      · exact List.mem_append_right _ (List.mem_singleton_self _)


theorem edges_nodup_of_visited_nodup (walk : G.Walk start finish)
    (hnd : walk.visited.Nodup) : walk.edges.Nodup := by
  induction walk with
  | nil => simp
  | concat walkSoFar e legal ih =>
      rw [visited_concat, List.nodup_append] at hnd
      obtain ⟨hvisited, -, hdisjoint⟩ := hnd
      rw [edges_concat, List.nodup_append]
      refine ⟨ih hvisited, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      rintro rfl
      exact hdisjoint (G.target a) (walkSoFar.mem_visited_of_mem_edges ha)
        (G.target a) (List.mem_singleton_self _) rfl


theorem exists_split_of_mem_visited (walk : G.Walk start finish)
    {vertex : V} (hmem : vertex ∈ walk.visited) :
    ∃ (before : G.Walk start vertex) (after : G.Walk vertex finish),
      walk.edges = before.edges ++ after.edges := by
  induction walk with
  | nil =>
      rw [visited_nil, List.mem_singleton] at hmem
      subst hmem
      exact ⟨.nil, .nil, by simp⟩
  | concat walkSoFar edge legal ih =>
      rw [visited_concat, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · obtain ⟨before, after, hedges⟩ := ih hmem
        refine ⟨before, after.concat edge legal, ?_⟩
        simp only [edges_concat, hedges, List.append_assoc]
      · subst hmem
        exact ⟨walkSoFar.concat edge legal, .nil, by simp⟩


theorem exists_closedSubwalk_of_not_nodup
    (walk : G.Walk start finish) (hdup : ¬ walk.visited.Nodup) :
    ∃ (vertex : V) (before : G.Walk start vertex) (cycle : G.Walk vertex vertex)
      (after : G.Walk vertex finish),
      0 < cycle.length ∧
        walk.edges = before.edges ++ cycle.edges ++ after.edges := by
  induction walk with
  | nil => exact absurd (List.nodup_singleton start) hdup
  | concat walkSoFar edge legal ih =>
      rw [visited_concat] at hdup
      by_cases hmem : G.target edge ∈ walkSoFar.visited
      · obtain ⟨before, after, hedges⟩ :=
          walkSoFar.exists_split_of_mem_visited hmem
        refine ⟨G.target edge, before, after.concat edge legal, .nil, by simp, ?_⟩
        simp only [edges_concat, edges_nil, hedges,
          List.append_assoc, List.append_nil]
      · have hnodup : ¬ walkSoFar.visited.Nodup := by
          intro hnd
          refine hdup ?_
          rw [List.nodup_append]
          refine ⟨hnd, List.nodup_singleton _, ?_⟩
          intro a ha b hb
          rw [List.mem_singleton] at hb
          subst hb
          rintro rfl
          exact hmem ha
        obtain ⟨vertex, before, cycle, after, hlen, hedges⟩ := ih hnodup
        refine ⟨vertex, before, cycle, after.concat edge legal, hlen, ?_⟩
        simp only [edges_concat, hedges, List.append_assoc]


theorem edges_isChain (walk : G.Walk start finish) :
    walk.edges.IsChain fun first second => G.target first = G.source second := by
  induction walk with
  | nil => exact List.isChain_nil
  | @concat middle walkSoFar edge legal ih =>
      cases walkSoFar with
      | nil => exact List.isChain_singleton edge
      | @concat previous walkBefore finalEdge finalLegal =>
          rw [edges, List.isChain_append]
          refine ⟨ih, List.isChain_singleton edge, ?_⟩
          simp [edges, legal]


private theorem source_of_mem_head? (walk : G.Walk start finish) {edge : E}
    (hhead : walk.edges.head? = some edge) : G.source edge = start := by
  induction walk with
  | nil => simp [edges] at hhead
  | @concat middle walkSoFar finalEdge legal ih =>
      cases walkSoFar with
      | nil =>
          rw [edges_concat, edges_nil, List.nil_append, List.head?_cons,
            Option.some_inj] at hhead
          exact hhead ▸ legal
      | @concat previous walkBefore edge' legal' =>
          have hne : (walkBefore.concat edge' legal').edges ≠ [] := by simp [edges]
          rw [edges_concat, List.head?_append_of_ne_nil _ hne] at hhead
          exact ih hhead


theorem source_head (walk : G.Walk start finish) (hne : walk.edges ≠ []) :
    G.source (walk.edges.head hne) = start :=
  source_of_mem_head? walk (List.head?_eq_some_head hne)


theorem target_getLast (walk : G.Walk start finish) (hne : walk.edges ≠ []) :
    G.target (walk.edges.getLast hne) = finish := by
  cases walk with
  | nil => simp [edges] at hne
  | concat walkSoFar edge legal => simp [edges]


@[simp] def edgeMultiplicity [DecidableEq E] {start : V} :
    {finish : V} → G.Walk start finish → E → ℕ
  | _, .nil => fun _ => 0
  | _, .concat walkSoFar edge _ => fun candidate =>
      walkSoFar.edgeMultiplicity candidate + if candidate = edge then 1 else 0



theorem edgeMultiplicity_pos_iff_mem_edges [DecidableEq E]
    (walk : G.Walk start finish) (edge : E) :
    0 < walk.edgeMultiplicity edge ↔ edge ∈ walk.edges := by
  induction walk with
  | nil => simp [edgeMultiplicity, edges]
  | concat walkSoFar finalEdge legal ih =>
      by_cases h : edge = finalEdge <;> simp [edgeMultiplicity, edges, ih, h]

theorem edgeMultiplicity_eq_count [DecidableEq E]
    (walk : G.Walk start finish) (edge : E) :
    walk.edgeMultiplicity edge = walk.edges.count edge := by
  induction walk with
  | nil => rfl
  | concat walkSoFar finalEdge legal ih =>
      by_cases h : edge = finalEdge
      · subst edge
        simp [edgeMultiplicity, edges, List.count_append, ih]
      · simp [edgeMultiplicity, edges, List.count_append, ih, h, eq_comm]

theorem edgeMultiplicity_eq_one_iff_mem_edges [DecidableEq E]
    (walk : G.Walk start finish) (hnodup : walk.edges.Nodup) (edge : E) :
    walk.edgeMultiplicity edge = 1 ↔ edge ∈ walk.edges := by
  grind [walk.edgeMultiplicity_eq_count]


def castFinish {start finish finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') : G.Walk start finish' :=
  hfinish ▸ walk

@[simp] theorem length_castFinish {start finish finish' : V}
    (walk : G.Walk start finish) (hfinish : finish = finish') :
    (walk.castFinish hfinish).length = walk.length := by
  subst finish'
  rfl

@[simp] theorem edges_castFinish {start finish finish' : V}
    (walk : G.Walk start finish) (hfinish : finish = finish') :
    (walk.castFinish hfinish).edges = walk.edges := by
  subst finish'
  rfl


def castStart {start start' finish : V} (walk : G.Walk start finish)
    (hstart : start = start') : G.Walk start' finish :=
  hstart ▸ walk


@[simp] theorem length_castStart {start start' finish : V}
    (walk : G.Walk start finish) (hstart : start = start') :
    (walk.castStart hstart).length = walk.length := by
  subst start'
  rfl


@[simp] theorem edges_castStart {start start' finish : V}
    (walk : G.Walk start finish) (hstart : start = start') :
    (walk.castStart hstart).edges = walk.edges := by
  subst start'
  rfl


@[simp] def append {start middle : V} (first : G.Walk start middle) :
    {finish : V} → G.Walk middle finish → G.Walk start finish
  | _, .nil => first
  | _, .concat second edge legal => .concat (first.append second) edge legal





@[simp] theorem edges_append (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).edges = first.edges ++ second.edges := by
  induction second with
  | nil => simp
  | concat second edge legal ih => simp [ih, List.append_assoc]

@[simp] theorem length_append (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).length = first.length + second.length := by
  induction second with
  | nil => simp
  | concat second edge legal ih => simp [ih, Nat.add_assoc]


end Walk
end EdgeGraph
end Maths

namespace Maths
namespace EdgeGraph
universe uV uE
variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)

def outgoingMultiplicity [Fintype E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) : ℕ :=
  ∑ edge with G.source edge = vertex, multiplicity edge


def incomingMultiplicity [Fintype E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) : ℕ :=
  ∑ edge with G.target edge = vertex, multiplicity edge


namespace Walk
variable {G} {start finish : V}


private theorem outgoingMultiplicity_edgeMultiplicity_concat
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (vertex : V) :
    G.outgoingMultiplicity (Walk.concat walkSoFar edge legal).edgeMultiplicity vertex =
      G.outgoingMultiplicity walkSoFar.edgeMultiplicity vertex +
        if G.source edge = vertex then 1 else 0 := by
  classical
  simp [outgoingMultiplicity, edgeMultiplicity, Finset.sum_add_distrib]


private theorem incomingMultiplicity_edgeMultiplicity_concat
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (vertex : V) :
    G.incomingMultiplicity (Walk.concat walkSoFar edge legal).edgeMultiplicity vertex =
      G.incomingMultiplicity walkSoFar.edgeMultiplicity vertex +
        if G.target edge = vertex then 1 else 0 := by
  classical
  simp [incomingMultiplicity, edgeMultiplicity, Finset.sum_add_distrib]


private theorem edgeMultiplicity_flow_with_endpoints
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walk : G.Walk start finish) (vertex : V) :
    G.outgoingMultiplicity walk.edgeMultiplicity vertex +
        (if finish = vertex then 1 else 0) =
      G.incomingMultiplicity walk.edgeMultiplicity vertex +
        (if start = vertex then 1 else 0) := by
  induction walk with
  | nil => simp [EdgeGraph.outgoingMultiplicity,EdgeGraph.incomingMultiplicity]
  | @concat middle walkSoFar edge legal ih =>
      rw [outgoingMultiplicity_edgeMultiplicity_concat,
        incomingMultiplicity_edgeMultiplicity_concat, legal]
      omega


theorem edgeMultiplicity_balanced [Fintype E] [DecidableEq E] [DecidableEq V]
    {base : V} (walk : G.Walk base base) (vertex : V) :
    G.outgoingMultiplicity walk.edgeMultiplicity vertex =
      G.incomingMultiplicity walk.edgeMultiplicity vertex := by
  have hflow := walk.edgeMultiplicity_flow_with_endpoints vertex
  omega



end Walk
end EdgeGraph
end Maths

namespace Maths.EdgeGraph.Walk
universe uV uE
variable {V : Type uV} {E : Type uE} {G : Maths.EdgeGraph V E} {start finish : V}

def singleton (edge : E) : G.Walk (G.source edge) (G.target edge) :=
  .concat .nil edge rfl



theorem exists_splitAtEdge (walk : G.Walk start finish) (edge : E) (hmem : edge ∈ walk.edges) :
    ∃ (before : G.Walk start (G.source edge)) (after : G.Walk (G.target edge) finish),
      walk.edges = before.edges ++ edge :: after.edges := by
  induction walk with
  | nil => simp at hmem
  | @concat middle walkSoFar finalEdge legal ih =>
      simp only [edges_concat, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | heq
      · obtain ⟨before, after, hsplit⟩ := ih hmem
        refine ⟨before, after.concat finalEdge legal, ?_⟩
        simp only [edges_concat, hsplit]
        simp [List.append_assoc]
      · subst finalEdge
        exact ⟨walkSoFar.castFinish legal.symm, .nil, by simp⟩

end Maths.EdgeGraph.Walk
