/- GID: D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Finite real flow certificates and directed potential duality supply cycle separation. -/

import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierGraph
import D5.S3.Analytic.Convexity.FarkasAlternative

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

noncomputable section

namespace MaxPlusPotential

universe uV uE

variable {𝕜 : Type*} [AddCommMonoid 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-! ### Weights of walks -/


def walkWeight (weight : E → 𝕜) {start finish : V} (walk : G.Walk start finish) : 𝕜 :=
  (walk.edges.map weight).sum

omit [LinearOrder 𝕜] in
@[simp] theorem walkWeight_concat (weight : E → 𝕜) {start finish : V}
    (walk : G.Walk start finish) (edge : E) (legal : G.source edge = finish) :
    walkWeight weight (walk.concat edge legal) = walkWeight weight walk + weight edge := by
  simp [walkWeight]

omit [LinearOrder 𝕜] in
@[simp] private theorem walkWeight_append (weight : E → 𝕜) {start middle finish : V}
    (first : G.Walk start middle) (second : G.Walk middle finish) :
    walkWeight weight (first.append second)
      = walkWeight weight first + walkWeight weight second := by
  simp [walkWeight]

section AddGroup

variable {𝕜g : Type*} [AddCommGroup 𝕜g]



end AddGroup

omit [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] in
@[simp] theorem walkWeight_castFinish (weight : E → 𝕜) {start finish finish' : V}
    (walk : G.Walk start finish) (hfinish : finish = finish') :
    walkWeight weight (walk.castFinish hfinish) = walkWeight weight walk := by
  simp [walkWeight]

section AddGroup

variable {𝕜g : Type*} [AddCommGroup 𝕜g]


theorem walkWeight_sub_const (weight : E → 𝕜g) (lam : 𝕜g) {start finish : V}
    (walk : G.Walk start finish) :
    walkWeight (fun e => weight e - lam) walk
      = walkWeight weight walk - walk.length • lam := by
  induction walk with
  | nil => simp [Maths.MaxPlusPotential.walkWeight]
  | concat walkSoFar edge legal ih =>
      simp only [walkWeight_concat, ih, EdgeGraph.Walk.length_concat, add_nsmul, one_nsmul]
      abel

end AddGroup

section Potential

variable {𝕜p : Type*} [Add 𝕜p] [LE 𝕜p]


def IsPotential (G : EdgeGraph V E) (weight : E → 𝕜p) (φ : V → 𝕜p) : Prop :=
  ∀ e : E, φ (G.source e) + weight e ≤ φ (G.target e)

end Potential

/-! ### Potentials and their edge defects -/

section AddGroup

variable {𝕜g : Type*} [AddCommGroup 𝕜g] [Preorder 𝕜g] [IsOrderedAddMonoid 𝕜g]


def defect (G : EdgeGraph V E) (weight : E → 𝕜g) (φ : V → 𝕜g) (e : E) : 𝕜g :=
  φ (G.source e) + weight e - φ (G.target e)




end AddGroup

section OrderedMonoid

variable {𝕜o : Type*} [AddCommMonoid 𝕜o] [Preorder 𝕜o] [IsOrderedAddMonoid 𝕜o]


theorem IsPotential.walkWeight_add_le {weight : E → 𝕜o} {φ : V → 𝕜o}
    (hφ : IsPotential G weight φ) {start finish : V} (walk : G.Walk start finish) :
    walkWeight weight walk + φ start ≤ φ finish := by
  induction walk with
  | nil => simp [Maths.MaxPlusPotential.walkWeight]
  | concat walkSoFar edge legal ih =>
      have hedge := hφ edge
      subst legal
      calc
        walkWeight weight (walkSoFar.concat edge rfl) + φ start =
            weight edge + (walkWeight weight walkSoFar + φ start) := by
          simp only [walkWeight_concat]
          ac_rfl
        _ ≤ weight edge + φ (G.source edge) := by
          have h := add_le_add_right ih (weight edge)
          simpa [add_assoc, add_comm, add_left_comm] using h
        _ ≤ φ (G.target edge) := by simpa [add_comm] using hedge

section CancelOrder

variable [IsOrderedCancelAddMonoid 𝕜o]

omit [IsOrderedAddMonoid 𝕜o] in
private theorem IsPotential.closedWalk_nonpos {weight : E → 𝕜o} {φ : V → 𝕜o}
    (hφ : IsPotential G weight φ) {vertex : V} (cycle : G.Walk vertex vertex) :
    walkWeight weight cycle ≤ 0 := by
  have h := hφ.walkWeight_add_le cycle
  have h' : walkWeight weight cycle + φ vertex ≤ 0 + φ vertex := by simpa using h
  exact le_of_add_le_add_right h'

end CancelOrder

end OrderedMonoid

/-! ### The duality

The finite-walk calculus this rests on - the visited-vertex list
`Maths.EdgeGraph.Walk.visited`, the split at a visited vertex, and the
closed-subwalk extraction `Maths.EdgeGraph.Walk.exists_closedSubwalk_of_not_nodup`
- lives in `Maths.EdgeGraph`. -/



def nodupIncomingWeights (G : EdgeGraph V E) (weight : E → 𝕜) (vertex : V) : Set 𝕜 :=
  {r | ∃ (start : V) (walk : G.Walk start vertex),
    walk.edges.Nodup ∧ walkWeight weight walk = r}

omit [LinearOrder 𝕜] in
private theorem zero_mem_nodupIncomingWeights (weight : E → 𝕜) (vertex : V) :
    (0 : 𝕜) ∈ nodupIncomingWeights G weight vertex :=
  ⟨vertex, .nil, by simp, rfl⟩

omit [LinearOrder 𝕜] in
private theorem finite_nodupIncomingWeights [Finite E] (weight : E → 𝕜) (vertex : V) :
    (nodupIncomingWeights G weight vertex).Finite := by
  cases nonempty_fintype E
  refine Set.Finite.subset
    (((List.finite_length_le E (Fintype.card E)).image fun l => (l.map weight).sum)) ?_
  rintro r ⟨start, walk, hnd, rfl⟩
  exact ⟨walk.edges, hnd.length_le_card, rfl⟩


theorem exists_nodup_visited_walkWeight_le {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0) :
    ∀ (bound : ℕ) {start finish : V} (walk : G.Walk start finish), walk.length ≤ bound →
      ∃ pruned : G.Walk start finish,
        pruned.visited.Nodup ∧ walkWeight weight walk ≤ walkWeight weight pruned := by
  intro bound
  induction bound with
  | zero =>
      intro start finish walk hlen
      cases walk with
      | nil => exact ⟨.nil, by simp, le_rfl⟩
      | concat walkSoFar edge legal => simp at hlen
  | succ bound ih =>
      intro start finish walk hlen
      by_cases hnd : walk.visited.Nodup
      · exact ⟨walk, hnd, le_rfl⟩
      · obtain ⟨vertex, before, cycle, after, hcyclen, hedges⟩ :=
          walk.exists_closedSubwalk_of_not_nodup hnd
        have hlengths : walk.length = before.length + (cycle.length + after.length) := by
          have hcongr := congrArg List.length hedges
          simpa [EdgeGraph.Walk.edges_length] using hcongr
        have hshort : (before.append after).length ≤ bound := by
          simp only [EdgeGraph.Walk.length_append]
          omega
        have hweights : walkWeight weight walk
            = walkWeight weight before + walkWeight weight cycle
              + walkWeight weight after := by
          simp only [walkWeight, hedges, List.map_append, List.sum_append]
        obtain ⟨pruned, hpruned, hle⟩ := ih (before.append after) hshort
        refine ⟨pruned, hpruned, le_trans ?_ hle⟩
        have := hcyc vertex cycle
        calc
          walkWeight weight walk = walkWeight weight before + walkWeight weight cycle
              + walkWeight weight after := hweights
          _ ≤ walkWeight weight before + walkWeight weight after := by
            have h := add_le_add_right (add_le_add_right this (walkWeight weight before))
                (walkWeight weight after)
            simpa [add_assoc, add_comm, add_left_comm] using h
          _ ≤ walkWeight weight (before.append after) := by
            rw [walkWeight_append]

section Finite

variable [Finite E]


def maxIncomingWeight (G : EdgeGraph V E) (weight : E → 𝕜) (vertex : V) : 𝕜 :=
  Finset.max' (Set.Finite.toFinset (finite_nodupIncomingWeights (G := G) weight vertex))
    ((Set.Finite.toFinset_nonempty (finite_nodupIncomingWeights (G := G) weight vertex)).2
      ⟨0, zero_mem_nodupIncomingWeights (G := G) weight vertex⟩)

omit [IsOrderedAddMonoid 𝕜] in
private theorem maxIncomingWeight_mem (weight : E → 𝕜) (vertex : V) :
    maxIncomingWeight G weight vertex ∈ nodupIncomingWeights G weight vertex :=
  (Set.Finite.mem_toFinset (finite_nodupIncomingWeights (G := G) weight vertex)).1
    (Finset.max'_mem _ _)

omit [IsOrderedAddMonoid 𝕜] in
private theorem le_maxIncomingWeight {weight : E → 𝕜} {vertex : V} {r : 𝕜}
    (hr : r ∈ nodupIncomingWeights G weight vertex) :
    r ≤ maxIncomingWeight G weight vertex :=
  Finset.le_max' _ _
    ((Set.Finite.mem_toFinset (finite_nodupIncomingWeights (G := G) weight vertex)).2 hr)


private theorem walkWeight_le_maxIncomingWeight {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0)
    {start finish : V} (walk : G.Walk start finish) :
    walkWeight weight walk ≤ maxIncomingWeight G weight finish := by
  obtain ⟨pruned, hnd, hle⟩ := exists_nodup_visited_walkWeight_le hcyc walk.length walk le_rfl
  exact hle.trans (le_maxIncomingWeight ⟨_, pruned, pruned.edges_nodup_of_visited_nodup hnd, rfl⟩)

private theorem maxIncomingWeight_isPotential {weight : E → 𝕜}
    (hcyc : ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0) :
    IsPotential G weight (maxIncomingWeight G weight) := by
  intro e
  obtain ⟨start, walk, -, hwalk⟩ := maxIncomingWeight_mem weight (G.source e)
  have hle := walkWeight_le_maxIncomingWeight hcyc (walk.concat e rfl)
  rwa [walkWeight_concat, hwalk] at hle

section CancelOrder

variable [IsOrderedCancelAddMonoid 𝕜]

omit [IsOrderedAddMonoid 𝕜] in
theorem exists_isPotential_iff_forall_closedWalk_nonpos (weight : E → 𝕜) :
    (∃ φ : V → 𝕜, IsPotential G weight φ) ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkWeight weight cycle ≤ 0 :=
  ⟨fun ⟨_, hφ⟩ _ cycle => hφ.closedWalk_nonpos cycle,
    fun hcyc => ⟨maxIncomingWeight G weight, maxIncomingWeight_isPotential hcyc⟩⟩

end CancelOrder

end Finite

/-! ### The quantitative obstruction -/

end MaxPlusPotential
end
end Maths

namespace Maths
noncomputable section
namespace FiniteInequality
open scoped BigOperators
universe uS uR
variable {State : Type uS} {Row Action : Type uR}

private theorem exists_potential_or_nonnegative_incompatibility
    [Fintype State] [Fintype Action]
    (delta : Action → State → ℝ) (base : Action → ℝ) :
    (∃ potential : State → ℝ, ∀ action, base action ≤ dotProduct (delta action) potential) ∨
    (∃ coefficient : Action → ℝ, (∀ action, 0 ≤ coefficient action) ∧
      (∀ state, ∑ action, coefficient action * delta action state = 0) ∧
      0 < ∑ action, coefficient action * base action) := by
  classical
  let A : Matrix Action (State × Bool) ℝ := fun a s =>
    if s.2 then delta a s.1 else -delta a s.1
  let b : Action → ℝ := fun a => -base a
  have halt := D5.S3.Analytic.Convexity.FarkasAlternative.inequality_farkas A b
  by_cases hp : ∃ x : State × Bool → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b
  · obtain ⟨x, hx, hA⟩ := hp
    left
    refine ⟨fun s => x (s, false) - x (s, true), ?_⟩
    intro a
    have h := hA a
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool,
      A, Bool.false_eq_true, ite_false, ite_true, b] at h
    simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
    simp_rw [neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib] at h
    linarith
  · have hc : ∃ y : Action → ℝ, 0 ≤ y ∧ 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0 := by
      by_contra hn
      exact halt (propext ⟨fun h => (hp h).elim, fun h => (hn h).elim⟩)
    obtain ⟨y, hy, hA, hb⟩ := hc
    right
    refine ⟨y, hy, ?_, ?_⟩
    · intro s
      have hf := hA (s, false)
      have ht := hA (s, true)
      change 0 ≤ ∑ a, (-delta a s) * y a at hf
      change 0 ≤ ∑ a, delta a s * y a at ht
      simp only [neg_mul, Finset.sum_neg_distrib] at hf
      have hzero : ∑ a, delta a s * y a = 0 := le_antisymm (by linarith) ht
      simpa only [mul_comm] using hzero
    · simp only [dotProduct, b, neg_mul, Finset.sum_neg_distrib] at hb
      have hpos : 0 < ∑ a, base a * y a := by linarith
      simpa only [mul_comm] using hpos


private theorem not_nonnegative_incompatibility_of_potential
    [Fintype State] [Fintype Action]
    {delta : Action → State → ℝ} {base : Action → ℝ}
    {potential : State → ℝ}
    (hpotential :
      ∀ action, base action ≤
        dotProduct (delta action) potential)
    {coefficient : Action → ℝ}
    (hnonnegative : ∀ action, 0 ≤ coefficient action)
    (hbalance :
      ∀ state,
        ∑ action, coefficient action * delta action state = 0) :
    ∑ action, coefficient action * base action ≤ 0 := by
  classical
  calc
    ∑ action, coefficient action * base action ≤
        ∑ action, coefficient action *
          dotProduct (delta action) potential := by
            apply Finset.sum_le_sum
            intro action _
            exact mul_le_mul_of_nonneg_left
              (hpotential action) (hnonnegative action)
    _ = ∑ state,
        (∑ action, coefficient action * delta action state) *
          potential state := by
            simp only [dotProduct, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro state _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro action _
            ring
    _ = 0 := by simp [hbalance]

variable [Fintype State] [Fintype Row]

def IsNormalizedCertificate (delta : Row → State → ℝ)
    (coefficient : Row → ℝ) : Prop :=
  (∀ row, 0 ≤ coefficient row) ∧
    (∑ row, coefficient row = 1) ∧
    ∀ state, ∑ row, coefficient row * delta row state = 0


def certificateValue (base : Row → ℝ) (coefficient : Row → ℝ) : ℝ :=
  ∑ row, coefficient row * base row


def WorstResidualAtMost (delta : Row → State → ℝ) (base : Row → ℝ)
    (level : ℝ) : Prop :=
  ∃ potential : State → ℝ,
    ∀ row, base row - dotProduct (delta row) potential ≤ level

private theorem weighted_shiftedBase_eq (base : Row → ℝ)
    (coefficient : Row → ℝ) (level : ℝ) :
    (∑ row, coefficient row * (base row - level)) =
      certificateValue base coefficient -
        level * ∑ row, coefficient row := by
  rw [certificateValue]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

private theorem coefficient_eq_zero_of_sum_eq_zero
    (coefficient : Row → ℝ) (hnonneg : ∀ row, 0 ≤ coefficient row)
    (hsum : ∑ row, coefficient row = 0) :
    ∀ row, coefficient row = 0 := by
  intro row
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (s := Finset.univ) (fun index _ => hnonneg index)).mp hsum
  exact hall row (Finset.mem_univ row)


private theorem certificateValue_le_of_worstResidualAtMost
    {delta : Row → State → ℝ} {base : Row → ℝ} {level : ℝ}
    (hlevel : WorstResidualAtMost delta base level)
    {coefficient : Row → ℝ}
    (hcertificate : IsNormalizedCertificate delta coefficient) :
    certificateValue base coefficient ≤ level := by
  classical
  rcases hlevel with ⟨potential, hpotential⟩
  have hrows (row) : base row - level ≤ dotProduct (delta row) potential := by
    have := hpotential row
    linarith
  have hweak := not_nonnegative_incompatibility_of_potential
    hrows hcertificate.1 hcertificate.2.2
  rw [weighted_shiftedBase_eq, hcertificate.2.1] at hweak
  linarith


theorem worstResidualAtMost_iff_normalizedDual_le
    (delta : Row → State → ℝ) (base : Row → ℝ) (level : ℝ) :
    WorstResidualAtMost delta base level ↔
      ∀ coefficient : Row → ℝ,
        IsNormalizedCertificate delta coefficient →
          certificateValue base coefficient ≤ level := by
  classical
  constructor
  · intro hlevel coefficient hcertificate
    exact certificateValue_le_of_worstResidualAtMost hlevel hcertificate
  · intro hdual
    rcases exists_potential_or_nonnegative_incompatibility delta
      (fun row => base row - level) with
      hpotential | ⟨coefficient, hnonneg, hbalance, hpositive⟩
    · exact ⟨hpotential.choose, fun row => by
        have := hpotential.choose_spec row
        linarith⟩
    · have hmassNonneg : 0 ≤ ∑ row, coefficient row :=
        Finset.sum_nonneg fun row _ => hnonneg row
      have hmassPos : 0 < ∑ row, coefficient row := by
        by_contra hnot
        have hmassZero : ∑ row, coefficient row = 0 :=
          le_antisymm (le_of_not_gt hnot) hmassNonneg
        have hzero := coefficient_eq_zero_of_sum_eq_zero
          coefficient hnonneg hmassZero
        have : ∑ row, coefficient row * (base row - level) = 0 := by
          simp [hzero]
        linarith
      let mass := ∑ row, coefficient row
      let normalized : Row → ℝ := fun row => coefficient row / mass
      have hnormalized : IsNormalizedCertificate delta normalized := by
        refine ⟨fun row => div_nonneg (hnonneg row) hmassNonneg, ?_, ?_⟩
        · dsimp [normalized, mass]
          rw [← Finset.sum_div, div_self hmassPos.ne']
        · intro state
          dsimp [normalized, mass]
          simp only [div_mul_eq_mul_div]
          rw [← Finset.sum_div, hbalance state, zero_div]
      have hvalue : level < certificateValue base normalized := by
        dsimp [certificateValue, normalized, mass]
        simp only [div_mul_eq_mul_div]
        rw [← Finset.sum_div]
        rw [weighted_shiftedBase_eq] at hpositive
        simp only [certificateValue] at hpositive
        rw [lt_div_iff₀ hmassPos]
        nlinarith
      exact (not_lt_of_ge (hdual normalized hnormalized) hvalue).elim

end FiniteInequality
end
end Maths

namespace Maths
noncomputable section
namespace AdditiveTransport

open scoped BigOperators

universe uV uE

variable {V : Type uV} {E : Type uE}

/-! ## One-sided cycle-mean threshold -/


def WorstDirectedResidualAtMost (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ) : Prop :=
  ∃ potential : V → ℝ,
    ∀ edge, MaxPlusPotential.defect G weight potential edge ≤ level


theorem worstDirectedResidualAtMost_iff_closedWalk_le
    [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (level : ℝ) :
    WorstDirectedResidualAtMost G weight level ↔
      ∀ (vertex : V) (cycle : G.Walk vertex vertex),
        MaxPlusPotential.walkWeight weight cycle ≤ cycle.length * level := by
  have hpotential : WorstDirectedResidualAtMost G weight level ↔
      ∃ potential : V → ℝ,
        MaxPlusPotential.IsPotential G (fun edge => weight edge - level) potential := by
    apply exists_congr
    intro potential
    constructor
    · intro h edge
      have := h edge
      change potential (G.source edge) + (weight edge - level) ≤
        potential (G.target edge)
      simp only [MaxPlusPotential.defect] at this
      linarith
    · intro h edge
      have := h edge
      change potential (G.source edge) + (weight edge - level) ≤
        potential (G.target edge) at this
      simp only [MaxPlusPotential.defect]
      linarith
  rw [hpotential,
    MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos]
  apply forall_congr'
  intro vertex
  apply forall_congr'
  intro cycle
  rw [MaxPlusPotential.walkWeight_sub_const, nsmul_eq_mul]
  constructor <;> intro h <;> linarith

/-! ## Symmetric signed-circulation threshold -/


abbrev SignedEdge (E : Type uE) := E × Bool


def signedDelta [DecidableEq V] (G : EdgeGraph V E) : SignedEdge E → V → ℝ
  | (edge, false) => fun vertex =>
      (if vertex = G.target edge then 1 else 0) -
        (if vertex = G.source edge then 1 else 0)
  | (edge, true) => fun vertex =>
      (if vertex = G.source edge then 1 else 0) -
        (if vertex = G.target edge then 1 else 0)



theorem dotProduct_signedDelta_false [Fintype V] [DecidableEq V]
    (G : EdgeGraph V E) (edge : E) (potential : V → ℝ) :
    dotProduct (signedDelta G (edge, false)) potential =
      potential (G.target edge) - potential (G.source edge) := by
  simp [dotProduct, signedDelta, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]

theorem dotProduct_signedDelta_true [Fintype V] [DecidableEq V]
    (G : EdgeGraph V E) (edge : E) (potential : V → ℝ) :
    dotProduct (signedDelta G (edge, true)) potential =
      potential (G.source edge) - potential (G.target edge) := by
  simp [dotProduct, signedDelta, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]


end AdditiveTransport
end
end Maths
