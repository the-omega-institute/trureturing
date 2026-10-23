/- GID: D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Normalized real circulations admit finite convex decompositions into simple circuits. -/

import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Max

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
namespace AdditiveTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}


def IsSimpleCycle {base : V} (cycle : G.Walk base base) : Prop :=
  0 < cycle.length ∧
    ∀ (vertex : V) (before : G.Walk base vertex)
      (inner : G.Walk vertex vertex) (after : G.Walk vertex base),
      cycle.edges = before.edges ++ inner.edges ++ after.edges →
      0 < inner.length → 0 < before.length + after.length → False


def CycleMeanDominates (weight : E → ℝ) {firstBase secondBase : V}
    (first : G.Walk firstBase firstBase)
    (second : G.Walk secondBase secondBase) : Prop :=
  second.length * MaxPlusPotential.walkWeight weight first ≥
    first.length * MaxPlusPotential.walkWeight weight second

private theorem cycle_weight_eq_of_decomposition (weight : E → ℝ)
    {base vertex : V} (cycle : G.Walk base base)
    (before : G.Walk base vertex) (inner : G.Walk vertex vertex)
    (after : G.Walk vertex base)
    (hedges : cycle.edges = before.edges ++ inner.edges ++ after.edges) :
    MaxPlusPotential.walkWeight weight cycle =
      MaxPlusPotential.walkWeight weight inner +
        MaxPlusPotential.walkWeight weight (before.append after) := by
  simp only [MaxPlusPotential.walkWeight, hedges, List.map_append,
    List.sum_append, EdgeGraph.Walk.edges_append]
  ring

private theorem cycle_length_eq_of_decomposition
    {base vertex : V} (cycle : G.Walk base base)
    (before : G.Walk base vertex) (inner : G.Walk vertex vertex)
    (after : G.Walk vertex base)
    (hedges : cycle.edges = before.edges ++ inner.edges ++ after.edges) :
    cycle.length = inner.length + (before.append after).length := by
  rw [← cycle.edges_length, hedges]
  simp [Nat.add_comm, Nat.add_assoc]


theorem exists_simpleCycle_cycleMeanDominates (weight : E → ℝ)
    {base : V} (reference : G.Walk base base) (hne : 0 < reference.length) :
    ∃ (simpleBase : V) (simple : G.Walk simpleBase simpleBase),
      IsSimpleCycle simple ∧ CycleMeanDominates weight simple reference := by
  classical
  let Good : ℕ → Prop := fun length =>
    ∃ (candidateBase : V) (candidate : G.Walk candidateBase candidateBase),
      0 < candidate.length ∧ candidate.length = length ∧
        CycleMeanDominates weight candidate reference
  have hexists : ∃ length, Good length :=
    ⟨reference.length, base, reference, hne, rfl, le_rfl⟩
  let minimum := Nat.find hexists
  obtain ⟨candidateBase, candidate, hcandidateNe, hlength, hdominates⟩ :=
    Nat.find_spec hexists
  refine ⟨candidateBase, candidate, ⟨hcandidateNe, ?_⟩, hdominates⟩
  intro vertex before inner after hedges hinner hremainder
  let remainder : G.Walk candidateBase candidateBase := before.append after
  have hremainder' : 0 < remainder.length := by
    simpa [remainder] using hremainder
  have hweight := cycle_weight_eq_of_decomposition
    weight candidate before inner after hedges
  have hlen := cycle_length_eq_of_decomposition
    candidate before inner after hedges
  have hcomponent :
      CycleMeanDominates weight inner reference ∨
        CycleMeanDominates weight remainder reference := by
    by_contra hnot
    push Not at hnot
    simp only [CycleMeanDominates] at hdominates hnot
    dsimp [remainder] at hnot
    have hinnerLt := lt_of_not_ge hnot.1
    have hremainderLt := lt_of_not_ge hnot.2
    have hlenReal : (candidate.length : ℝ) =
        inner.length + (before.append after).length := by
      exact_mod_cast hlen
    have hcandidateLt :
        reference.length * MaxPlusPotential.walkWeight weight candidate <
          candidate.length * MaxPlusPotential.walkWeight weight reference := by
      rw [hweight, hlenReal]
      nlinarith
    exact (not_lt_of_ge hdominates) hcandidateLt
  have hminimal {length} (hgood : Good length) : minimum ≤ length :=
    Nat.find_min' hexists hgood
  have hminimum : candidate.length = minimum := hlength
  have hafter : 0 < (before.append after).length := by simpa [remainder] using hremainder'
  rcases hcomponent with hinnerDominates | hremainderDominates
  · have := hminimal ⟨vertex, inner, hinner, rfl, hinnerDominates⟩
    omega
  · have := hminimal (length := (before.append after).length)
      ⟨candidateBase, remainder, hremainder', rfl, hremainderDominates⟩
    omega


private theorem exists_simpleCycle_mean_gt_of_closedWalk
    (weight : E → ℝ) (level : ℝ) {base : V}
    (cycle : G.Walk base base)
    (hviolation : cycle.length * level <
      MaxPlusPotential.walkWeight weight cycle) :
    ∃ (simpleBase : V) (simple : G.Walk simpleBase simpleBase),
      IsSimpleCycle simple ∧
        simple.length * level < MaxPlusPotential.walkWeight weight simple := by
  have hne : 0 < cycle.length := by
    by_contra hnot
    have hzero : cycle.length = 0 := Nat.eq_zero_of_not_pos hnot
    have hempty : cycle.edges = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using hzero
    simp [MaxPlusPotential.walkWeight, hzero, hempty] at hviolation
  obtain ⟨simpleBase, simple, hsimple, hdominates⟩ :=
    exists_simpleCycle_cycleMeanDominates weight cycle hne
  refine ⟨simpleBase, simple, hsimple, ?_⟩
  simp only [CycleMeanDominates] at hdominates
  have hsimplePos : (0 : ℝ) < simple.length := by exact_mod_cast hsimple.1
  have hcyclePos : (0 : ℝ) < cycle.length := by exact_mod_cast hne
  have hscaledViolation := mul_lt_mul_of_pos_left hviolation hsimplePos
  by_contra hnot
  have hsimpleLe : MaxPlusPotential.walkWeight weight simple ≤
      simple.length * level := le_of_not_gt hnot
  have hscaledSimple := mul_le_mul_of_nonneg_left hsimpleLe hcyclePos.le
  nlinarith


theorem forall_closedWalk_mean_le_iff_simpleCycle
    (weight : E → ℝ) (level : ℝ) :
    (∀ (base : V) (cycle : G.Walk base base),
      MaxPlusPotential.walkWeight weight cycle ≤ cycle.length * level) ↔
    (∀ (base : V) (cycle : G.Walk base base),
      IsSimpleCycle cycle →
        MaxPlusPotential.walkWeight weight cycle ≤ cycle.length * level) := by
  constructor
  · intro hall base cycle _
    exact hall base cycle
  · intro hsimple base cycle
    by_contra hnot
    have hviolation : cycle.length * level <
        MaxPlusPotential.walkWeight weight cycle := lt_of_not_ge hnot
    obtain ⟨simpleBase, simple, hs, hgt⟩ :=
      exists_simpleCycle_mean_gt_of_closedWalk weight level cycle hviolation
    exact (not_lt_of_ge (hsimple simpleBase simple hs)) hgt


end AdditiveTransport
end
end Maths

namespace Maths
noncomputable section

namespace AdditiveTransport

universe uV uE

variable {V : Type uV} {E : Type uE}


def signedGraph (G : EdgeGraph V E) : EdgeGraph V (SignedEdge E) where
  source
    | (edge, false) => G.source edge
    | (edge, true) => G.target edge
  target
    | (edge, false) => G.target edge
    | (edge, true) => G.source edge








def circuitCoefficient [DecidableEq E] {G : EdgeGraph V E} {base : V}
    (cycle : G.Walk base base) (edge : E) : ℝ :=
  cycle.edgeMultiplicity edge / cycle.length

theorem sum_edgeMultiplicity_eq_length [Fintype E] [DecidableEq E]
    {G : EdgeGraph V E} {start finish : V} (walk : G.Walk start finish) :
    ∑ edge, walk.edgeMultiplicity edge = walk.length := by
  induction walk with
  | nil => simp [Maths.MaxPlusPotential.walkWeight]
  | concat walk edge legal ih =>
      simp only [EdgeGraph.Walk.edgeMultiplicity,
        EdgeGraph.Walk.length_concat, Finset.sum_add_distrib, ih]
      simp





private theorem dotProduct_signedDelta_eq_signedGraph_difference
    [Fintype V] [DecidableEq V] (G : EdgeGraph V E)
    (edge : SignedEdge E) (potential : V → ℝ) :
    dotProduct (signedDelta G edge) potential =
      potential ((signedGraph G).target edge) -
        potential ((signedGraph G).source edge) := by
  rcases edge with ⟨edge, orientation⟩
  cases orientation with
  | false => exact dotProduct_signedDelta_false G edge potential
  | true => exact dotProduct_signedDelta_true G edge potential


private theorem worstDirectedResidualAtMost_signedGraph_iff_finiteInequality
    [Fintype V] [DecidableEq V]
    (G : EdgeGraph V E) (orientedWeight : SignedEdge E → ℝ) (level : ℝ) :
    WorstDirectedResidualAtMost (signedGraph G) orientedWeight level ↔
      FiniteInequality.WorstResidualAtMost
        (signedDelta G) orientedWeight level := by
  apply exists_congr
  intro potential
  apply forall_congr'
  intro edge
  rw [dotProduct_signedDelta_eq_signedGraph_difference]
  simp only [MaxPlusPotential.defect]
  constructor <;> intro h <;> linarith


private theorem normalizedSignedCirculationDual_le_iff_closedWalk_le
    [Fintype V] [DecidableEq V] [Fintype E]
    (G : EdgeGraph V E) (orientedWeight : SignedEdge E → ℝ) (level : ℝ) :
    (∀ coefficient : SignedEdge E → ℝ,
      FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient →
        FiniteInequality.certificateValue orientedWeight coefficient ≤ level) ↔
      ∀ (base : V) (cycle : (signedGraph G).Walk base base),
        MaxPlusPotential.walkWeight orientedWeight cycle ≤
          cycle.length * level := by
  rw [← FiniteInequality.worstResidualAtMost_iff_normalizedDual_le,
    ← worstDirectedResidualAtMost_signedGraph_iff_finiteInequality,
    worstDirectedResidualAtMost_iff_closedWalk_le]


private theorem normalizedSignedCirculationDual_le_iff_simpleCycles_le
    [Fintype V] [DecidableEq V] [Fintype E]
    (G : EdgeGraph V E) (orientedWeight : SignedEdge E → ℝ) (level : ℝ) :
    (∀ coefficient : SignedEdge E → ℝ,
      FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient →
        FiniteInequality.certificateValue orientedWeight coefficient ≤ level) ↔
      ∀ (base : V) (cycle : (signedGraph G).Walk base base),
        IsSimpleCycle cycle →
          MaxPlusPotential.walkWeight orientedWeight cycle ≤
            cycle.length * level := by
  rw [normalizedSignedCirculationDual_le_iff_closedWalk_le,
    forall_closedWalk_mean_le_iff_simpleCycle]


end AdditiveTransport
end
end Maths

namespace Maths
noncomputable section
namespace AdditiveTransport
open scoped BigOperators
universe uV uE
variable {V : Type uV} {E : Type uE}

def edgeListCoefficient [DecidableEq E] (edges : List E) (edge : E) : ℝ :=
  edges.count edge / edges.length

private theorem circuitCoefficient_eq_edgeListCoefficient [DecidableEq E]
    {G : EdgeGraph V E} {base : V} (cycle : G.Walk base base) :
    circuitCoefficient cycle = edgeListCoefficient cycle.edges := by
  funext edge
  simp only [circuitCoefficient, edgeListCoefficient,
    cycle.edgeMultiplicity_eq_count, EdgeGraph.Walk.edges_length]


def simpleSignedCircuitCoefficients [DecidableEq E] (G : EdgeGraph V E) :
    Set (SignedEdge E → ℝ) :=
  {coefficient | ∃ (base : V) (cycle : (signedGraph G).Walk base base),
    IsSimpleCycle cycle ∧ circuitCoefficient cycle = coefficient}


theorem IsSimpleCycle.length_le_card [Fintype V] {G : EdgeGraph V E}
    {base : V} {cycle : G.Walk base base} (hsimple : IsSimpleCycle cycle) :
    cycle.length ≤ Fintype.card V := by
  classical
  by_contra hcard
  cases cycle with
  | nil => exact (Nat.not_lt_zero _ hsimple.1)
  | concat initial edge legal =>
      have hinitialDup : ¬initial.visited.Nodup := by
        intro hnodup
        have hlengthCard := hnodup.length_le_card
        rw [EdgeGraph.Walk.length_visited] at hlengthCard
        simp only [EdgeGraph.Walk.length_concat] at hcard
        exact hcard hlengthCard
      obtain ⟨middle, before, inner, after, hinnerPos, hedges⟩ :=
        initial.exists_closedSubwalk_of_not_nodup hinitialDup
      have hcycleEdges :
          (initial.concat edge legal).edges =
            before.edges ++ inner.edges ++ (after.concat edge legal).edges := by
        simp only [EdgeGraph.Walk.edges_concat, hedges, List.append_assoc]
      exact hsimple.2 middle before inner (after.concat edge legal)
        hcycleEdges hinnerPos (by simp)


private theorem finite_simpleSignedCircuitCoefficients
    [Fintype V] [Fintype E] [DecidableEq E] (G : EdgeGraph V E) :
    (simpleSignedCircuitCoefficients G).Finite := by
  let boundedLists : Set (List (SignedEdge E)) :=
    {edges | edges.length ≤ Fintype.card V}
  have hfinite : boundedLists.Finite := List.finite_length_le _ _
  apply (hfinite.image edgeListCoefficient).subset
  rintro coefficient ⟨base, cycle, hsimple, rfl⟩
  refine ⟨cycle.edges, ?_, ?_⟩
  · change cycle.edges.length ≤ Fintype.card V
    simpa only [EdgeGraph.Walk.edges_length] using hsimple.length_le_card
  · exact (circuitCoefficient_eq_edgeListCoefficient cycle).symm

private theorem continuousLinearMap_eq_certificateValue
    [Fintype E] [DecidableEq E]
    (functional : (SignedEdge E → ℝ) →L[ℝ] ℝ)
    (coefficient : SignedEdge E → ℝ) :
    functional coefficient =
      FiniteInequality.certificateValue
        (fun edge => functional (Pi.single edge 1)) coefficient := by
  calc
    functional coefficient =
        functional (∑ edge, Pi.single edge (coefficient edge)) := by
          rw [LinearMap.sum_single_apply]
    _ = ∑ edge, coefficient edge * functional (Pi.single edge 1) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro edge _
      conv_lhs =>
        rw [show coefficient edge = coefficient edge • (1 : ℝ) by simp,
          Pi.single_smul, map_smul, smul_eq_mul]
    _ = _ := rfl

theorem sum_edgeMultiplicity_mul_eq_walkWeight_general
    [Fintype E] [DecidableEq E] {G : EdgeGraph V E}
    (weight : E → ℝ) {start finish : V} (walk : G.Walk start finish) :
    ∑ edge, (walk.edgeMultiplicity edge : ℝ) * weight edge =
      MaxPlusPotential.walkWeight weight walk := by
  induction walk with
  | nil => simp [Maths.MaxPlusPotential.walkWeight]
  | concat walk edge legal ih =>
      simp only [EdgeGraph.Walk.edgeMultiplicity, Nat.cast_add,
        add_mul, Finset.sum_add_distrib, ih,
        MaxPlusPotential.walkWeight_concat]
      simp

private theorem certificateValue_circuitCoefficient_general
    [Fintype E] [DecidableEq E] {G : EdgeGraph V E}
    (weight : E → ℝ) {base : V} (cycle : G.Walk base base) :
    FiniteInequality.certificateValue weight (circuitCoefficient cycle) =
      MaxPlusPotential.walkWeight weight cycle / cycle.length := by
  simp only [FiniteInequality.certificateValue, circuitCoefficient,
    div_mul_eq_mul_div, ← Finset.sum_div]
  rw [sum_edgeMultiplicity_mul_eq_walkWeight_general]


private theorem normalizedCertificate_mem_convexHull_simpleSignedCircuits
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdgeGraph V E) (coefficient : SignedEdge E → ℝ)
    (hcoefficient :
      FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient) :
    coefficient ∈ convexHull ℝ (simpleSignedCircuitCoefficients G) := by
  by_contra hnot
  let circuits := simpleSignedCircuitCoefficients G
  have hfinite : circuits.Finite := finite_simpleSignedCircuitCoefficients G
  obtain ⟨functional, level, hcircuit, hcoefficientLevel⟩ :=
    geometric_hahn_banach_closed_point
      (convex_convexHull ℝ circuits)
      (hfinite.isClosed_convexHull ℝ) hnot
  let orientedWeight : SignedEdge E → ℝ :=
    fun edge => functional (Pi.single edge 1)
  have hsimple (base : V) (cycle : (signedGraph G).Walk base base)
      (hcycle : IsSimpleCycle cycle) :
      MaxPlusPotential.walkWeight orientedWeight cycle ≤
        cycle.length * level := by
    have hmem : circuitCoefficient cycle ∈ circuits :=
      ⟨base, cycle, hcycle, rfl⟩
    have hstrict := hcircuit _ (subset_convexHull ℝ circuits hmem)
    rw [continuousLinearMap_eq_certificateValue functional,
      certificateValue_circuitCoefficient_general orientedWeight] at hstrict
    have hlength : (0 : ℝ) < cycle.length := by
      exact_mod_cast hcycle.1
    simpa only [mul_comm] using ((div_lt_iff₀ hlength).mp hstrict).le
  have hdual :=
    (normalizedSignedCirculationDual_le_iff_simpleCycles_le
      G orientedWeight level).mpr hsimple coefficient hcoefficient
  rw [← continuousLinearMap_eq_certificateValue functional coefficient] at hdual
  exact (not_lt_of_ge hdual) hcoefficientLevel


theorem exists_simpleSignedCircuit_decomposition
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdgeGraph V E) (coefficient : SignedEdge E → ℝ)
    (hcoefficient :
      FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient) :
    ∃ (ι : Type) (_ : Fintype ι) (convexWeight : ι → ℝ)
      (base : ι → V)
      (cycle : ∀ i, (signedGraph G).Walk (base i) (base i)),
      (∀ i, 0 ≤ convexWeight i) ∧
      (∑ i, convexWeight i) = 1 ∧
      (∀ i, IsSimpleCycle (cycle i)) ∧
      ∀ edge, coefficient edge =
        ∑ i, convexWeight i * circuitCoefficient (cycle i) edge := by
  have hmem :=
    normalizedCertificate_mem_convexHull_simpleSignedCircuits
      G coefficient hcoefficient
  rw [mem_convexHull_iff_exists_fintype] at hmem
  obtain ⟨ι, inst, convexWeight, point, hnonneg, hsum, hpoint, hcoefficientSum⟩ :=
    hmem
  let base : ι → V := fun i => (hpoint i).choose
  let cycle : ∀ i, (signedGraph G).Walk (base i) (base i) :=
    fun i => (hpoint i).choose_spec.choose
  have hcycle (i : ι) : IsSimpleCycle (cycle i) :=
    (hpoint i).choose_spec.choose_spec.1
  have hpointEq (i : ι) : circuitCoefficient (cycle i) = point i :=
    (hpoint i).choose_spec.choose_spec.2
  refine ⟨ι, inst, convexWeight, base, cycle, hnonneg, hsum, hcycle, ?_⟩
  intro edge
  have heq := congrFun hcoefficientSum.symm edge
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hpointEq] using heq

end AdditiveTransport
end
end Maths
