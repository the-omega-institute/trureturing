/- GID: D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerFiniteLabels
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/AdaptiveMarkerFiniteLabels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite compatible labels causally realize every acquired marker prefix. -/

import D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCEvent
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.CompProdEqIff


/-! Finite path compatibility gives causal realization with the original seed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerFiniteLabels

open AdaptiveMarkerStoppingTails

/-- An archive word is chronological; it stores no root or source. -/
abbrev Word := List (Side × Bool)

def actions (w : Word) (k : ℕ) : List Side := (w.take k).map Prod.fst

def replies (w : Word) (k : ℕ) : List Bool := (w.take k).map Prod.snd

def sideTotal (w : Word) (s : Side) : ℕ := (w.map Prod.fst).count s

def occurrences (w : Word) (s : Side) (k : ℕ) : ℕ := (actions w k).count s

private theorem occurrences_le (w : Word) (s : Side) (k : ℕ) :
    occurrences w s k ≤ sideTotal w s := by
  exact ((List.take_sublist k w).map Prod.fst).count_le s

private theorem occurrences_next_le (w : Word) (k : Fin w.length) :
    occurrences w w[k].1 k + 1 ≤ sideTotal w w[k].1 := by
  have h := occurrences_le w w[k].1 (k + 1)
  change ((w.take (k.val + 1)).map Prod.fst).count w[k].1 ≤ sideTotal w w[k].1 at h
  rw [List.take_succ_eq_append_getElem k.isLt, List.map_append, List.count_append] at h
  simpa [occurrences, actions] using h

/-- The first true reply is the final reply, and the word is nonempty. -/
def terminalFirstTrue (w : Word) : Prop :=
  0 < w.length ∧ ∀ k : Fin w.length, w[k].2 = decide (k.val + 1 = w.length)

/-- The original seed selects each action from its reversed acquired prefix. -/
def policyConformity {Seed : Type*} [MeasurableSpace Seed]
    (p : Policy Seed) (u : Seed) (w : Word) : Prop :=
  ∀ k : Fin w.length,
    w[k].1 = p.choose u (actions w k).reverse (replies w k).reverse

/-- Auxiliary finite labels, not part of the archive. The two arms share their
initial label, avoid 11, and produce each acquired reply by their local 00 test. -/
structure Labels (w : Word) where
  bit : (s : Side) → Fin (sideTotal w s + 1) → Bool
  root : bit false ⟨0, Nat.zero_lt_succ _⟩ = bit true ⟨0, Nat.zero_lt_succ _⟩
  no11 : ∀ s i (hi : i < sideTotal w s),
    ¬(bit s ⟨i, by omega⟩ = true ∧ bit s ⟨i + 1, by omega⟩ = true)
  response : ∀ k : Fin w.length,
    w[k].2 = decide
      (bit w[k].1 ⟨occurrences w w[k].1 k, by
          have := occurrences_next_le w k; omega⟩ = false ∧
       bit w[k].1 ⟨occurrences w w[k].1 k + 1, by
          have := occurrences_next_le w k; omega⟩ = false)

/-- Extend each finite label sequence by false beyond its last acquired vertex. -/
def extended {w : Word} (z : Labels w) (s : Side) (i : ℕ) : Bool :=
  if h : i ≤ sideTotal w s then z.bit s ⟨i, by omega⟩ else false

def completion {w : Word} (z : Labels w) : Source :=
  (z.bit false ⟨0, Nat.zero_lt_succ _⟩,
    (fun i => extended z false (i + 1), fun i => extended z true (i + 1)))

private theorem arm_completion {w : Word} (z : Labels w) (s : Side) (i : ℕ) :
    arm (completion z) s i = extended z s (i + 1) := by
  cases s <;> rfl

private theorem endpoint_completion {w : Word} (z : Labels w) (s : Side) (i : ℕ) :
    endpoint (completion z) s i = extended z s i := by
  cases i with
  | zero =>
    cases s
    · simp [endpoint, completion, extended]
    · simpa [endpoint, completion, extended] using z.root
  | succ i => exact arm_completion z s i

private theorem completion_support {w : Word} (z : Labels w) :
    noAdjacentOnes (completion z) := by
  intro s i
  rw [endpoint_completion, arm_completion]
  by_cases hi : i < sideTotal w s
  · simpa [extended, show i ≤ sideTotal w s by omega,
      show i + 1 ≤ sideTotal w s by omega] using z.no11 s i hi
  · simp [extended, show ¬i + 1 ≤ sideTotal w s by omega]

private theorem completion_response {w : Word} (z : Labels w) (k : Fin w.length) :
    markerResponse (completion z) w[k].1 (occurrences w w[k].1 k) = w[k].2 := by
  have hb := occurrences_next_le w k
  rw [markerResponse, endpoint_completion, arm_completion]
  simpa only [extended,
    dite_eq_left (show occurrences w w[k].1 k ≤ sideTotal w w[k].1 by omega),
    dite_eq_left (show occurrences w w[k].1 k + 1 ≤ sideTotal w w[k].1 by omega)] using
      (z.response k).symm

/-- Causal induction: the already reconstructed acquired prefix is the next
policy input. No execution or inverse equation is assumed in Labels. -/
private theorem prefix_realization {Seed : Type*} [MeasurableSpace Seed]
    (p : Policy Seed) (u : Seed) (w : Word)
    (ht : terminalFirstTrue w) (hp : policyConformity p u w) (z : Labels w) :
    ∀ k, k ≤ w.length → actualRun p u (completion z) k =
      ⟨(actions w k).reverse, (replies w k).reverse, decide (k = w.length)⟩ := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [actualRun, actions, replies, Nat.ne_of_lt ht.1]
  | succ k ih =>
    intro hk
    have hklt : k < w.length := by omega
    have hprior := ih (by omega)
    have hne : k ≠ w.length := by omega
    simp only [hne, decide_false] at hprior
    have hpolicy := hp ⟨k, hklt⟩
    have hresponse := completion_response z ⟨k, hklt⟩
    have hterminal := ht.2 ⟨k, hklt⟩
    change w[k].1 = p.choose u (actions w k).reverse (replies w k).reverse at hpolicy
    change markerResponse (completion z) w[k].1 (occurrences w w[k].1 k) = w[k].2
      at hresponse
    change w[k].2 = decide (k + 1 = w.length) at hterminal
    rw [actualRun, hprior]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← hpolicy]
    simp only [sideCount, List.count_reverse]
    change State.mk (w[k].1 :: (actions w k).reverse)
      (markerResponse (completion z) w[k].1 (occurrences w w[k].1 k) ::
        (replies w k).reverse)
      (markerResponse (completion z) w[k].1 (occurrences w w[k].1 k)) = _
    rw [hresponse, hterminal]
    simp only [actions, replies, List.take_succ_eq_append_getElem hklt,
      List.map_append, List.map_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append, hterminal]

/-- Every compatible finite-label witness gives one supported zero-tail source
realizing all acquired prefixes and stopping for the first time at word length. -/
theorem finite_label_realization {Seed : Type*} [MeasurableSpace Seed]
    (p : Policy Seed) (u : Seed) (w : Word)
    (ht : terminalFirstTrue w) (hp : policyConformity p u w) (z : Labels w) :
    noAdjacentOnes (completion z) ∧
    (∀ s (i : Fin (sideTotal w s + 1)),
      endpoint (completion z) s i = z.bit s i) ∧
    (∀ k, k ≤ w.length → actualRun p u (completion z) k =
      ⟨(actions w k).reverse, (replies w k).reverse, decide (k = w.length)⟩) ∧
    actualRun p u (completion z) w.length =
      ⟨(w.map Prod.fst).reverse, (w.map Prod.snd).reverse, true⟩ ∧
    actualQueryCount p u (completion z) w.length = w.length ∧
    stoppingTime p u (completion z) = (w.length : WithTop ℕ) := by
  have hprefix := prefix_realization p u w ht hp z
  have hlast : actualRun p u (completion z) w.length =
      ⟨(w.map Prod.fst).reverse, (w.map Prod.snd).reverse, true⟩ := by
    simpa [actions, replies] using hprefix w.length le_rfl
  refine ⟨completion_support z, ?_, hprefix, hlast, ?_, ?_⟩
  · intro s i
    rw [endpoint_completion]
    simp [extended, show i.val ≤ sideTotal w s by omega]
  · simp [actualQueryCount, hlast]
  · classical
    have hex : ∃ k, (actualRun p u (completion z) k).stopped = true := by
      exact ⟨w.length, by rw [hlast]⟩
    have hfind : Nat.find hex = w.length := by
      apply (Nat.find_eq_iff hex).mpr
      constructor
      · rw [hlast]
      · intro k hk
        rw [hprefix k (by omega)]
        simp [Nat.ne_of_lt hk]
    simp [stoppingTime, hex, hfind]


/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors; simulation source author Codex.
Adaptation of TauCeti at da527980caecf7e72838e069c01f4a7e7633eca3:
TauCeti/Probability/MarkovChain/Simulation.lean and
TauCeti/Probability/Kernel/Randomization.lean.
Source: https://github.com/TauCetiProject/TauCeti/blob/da527980caecf7e72838e069c01f4a7e7633eca3/TauCeti/Probability/MarkovChain/Simulation.lean
Modified for pinned Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679:
independent uniform-noise simulation and its original-source first-record law.
The consumed simulation and first-record proofs supply finite-label realizability.
The pinned upstream Git tree contains no NOTICE file.
Retirement: when the Mathlib revision adopted by this repository supplies an
equivalent simulation theorem, replace this port by its direct application.
The following is the complete upstream Apache-2.0 license.
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

noncomputable section
set_option maxHeartbeats 800000
open Finset MeasureTheory Preorder ProbabilityTheory Function Filter
open scoped ENNReal NNReal BigOperators Topology

namespace Original
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCEvent

namespace Port
variable {α : Type*} [MeasurableSpace α]
private theorem map_prod_eq_compProd_of_map
    {β ξ : Type*} [MeasurableSpace β] [MeasurableSpace ξ]
    {μ : Measure β} [SFinite μ] (κ : Kernel β α)
    [IsMarkovKernel κ] (ρ : Measure ξ) [SFinite ρ] (f : β → ξ → α)
    (hf : Measurable (uncurry f)) (hmap : ∀ b, ρ.map (f b) = κ b) :
    (μ.prod ρ).map (fun p => (p.1, f p.1 p.2)) = μ ⊗ₘ κ := by
  have hF : Measurable (fun p : β × ξ => (p.1, f p.1 p.2)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hs.preimage hF), Measure.compProd_apply hs]
  congr with b
  rw [← hmap b, Measure.map_apply hf.of_uncurry_left (measurable_prodMk_left hs)]
  rfl

private theorem map_prodMk_eq_compProd_of_map
    {β Ω ξ : Type*} [MeasurableSpace β] [MeasurableSpace Ω] [MeasurableSpace ξ]
    {P : Measure Ω} [IsFiniteMeasure P] {W : Ω → β} {U : Ω → ξ}
    (hindep : IndepFun W U P) (hW : AEMeasurable W P)
    {ρ : Measure ξ} (hlaw : HasLaw U ρ P)
    (κ : Kernel β α) [IsMarkovKernel κ] (f : β → ξ → α)
    (hf : Measurable (uncurry f)) (hmap : ∀ w, ρ.map (f w) = κ w) :
    P.map (fun ω => (W ω, f (W ω) (U ω))) = (P.map W) ⊗ₘ κ := by
  have : IsFiniteMeasure ρ := hlaw.isFiniteMeasure_iff.mp inferInstance
  have hpair := hindep.map_prod_eq_prod_map_map hW hlaw.aemeasurable
  rw [hlaw.map_eq] at hpair
  calc
    _ = ((P.map W).prod ρ).map (fun p => (p.1, f p.1 p.2)) := by
      rw [← hpair, AEMeasurable.map_map_of_aemeasurable (by fun_prop)
        (hW.prodMk hlaw.aemeasurable)]
      rfl
    _ = _ := map_prod_eq_compProd_of_map κ ρ f hf hmap

def randomizedChain {ξ : Type*} (g : ξ → α) (f : α → ξ → α) (u : ℕ → ξ) : ℕ → α
  | 0 => g (u 0)
  | n + 1 => f (randomizedChain g f u n) (u (n + 1))
omit [MeasurableSpace α] in
private theorem randomizedChain_congr {ξ : Type*} (g : ξ → α) (f : α → ξ → α)
    {u v : ℕ → ξ} {n : ℕ} (h : ∀ i ≤ n, u i = v i) :
    randomizedChain g f u n = randomizedChain g f v n := by
  induction n with
  | zero => simp [randomizedChain, h 0 le_rfl]
  | succ n ih => simp only [randomizedChain, h (n+1) le_rfl,
      ih (fun i hi => h i (hi.trans (Nat.le_succ n)))]
variable {ξ Ω : Type*} [MeasurableSpace ξ] [MeasurableSpace Ω]
@[fun_prop]
private theorem measurable_randomizedChain {g : ξ → α} {f : α → ξ → α}
    (hg : Measurable g) (hf : Measurable (uncurry f)) :
    Measurable (randomizedChain g f) := by
  apply measurable_pi_iff.mpr
  intro n
  induction n with
  | zero => exact hg.comp (measurable_pi_apply 0)
  | succ n ih => exact hf.comp (ih.prodMk (measurable_pi_apply (n+1)))
private theorem indepFun_randomizedChain_prefix {g : ξ → α} {f : α → ξ → α}
    (hg : Measurable g) (hf : Measurable (uncurry f)) {U : ℕ → Ω → ξ} {P : Measure Ω}
    (hU : ∀ i, Measurable (U i)) (hindep : iIndepFun U P) (n : ℕ) :
    IndepFun (fun ω (i : Fin (n+1)) => randomizedChain g f (fun j => U j ω) i)
      (U (n+1)) P := by
  let extend (v : Set.Iic n → ξ) (j : ℕ) : ξ :=
    if h : j ≤ n then v ⟨j,h⟩ else v ⟨0,Nat.zero_le n⟩
  have hext : Measurable extend := by
    apply measurable_pi_iff.mpr
    intro j
    by_cases h : j ≤ n <;> simp only [extend, h, ↓reduceDIte] <;> fun_prop
  let F (v : Set.Iic n → ξ) (i : Fin (n+1)) := randomizedChain g f (extend v) i
  have hF : Measurable F := measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply (i : ℕ)).comp (measurable_randomizedChain hg hf)).comp hext
  have h := iIndepFun.indepFun_set (Set.Iic n) {n+1}
    (by simp only [Set.disjoint_left, Set.mem_Iic, Set.mem_singleton_iff]; omega) hindep hU
  have h' := h.comp hF (measurable_pi_apply ⟨n+1,rfl⟩)
  convert h' using 1
  · funext ω i
    apply randomizedChain_congr
    intro j hj
    simp [extend, hj.trans (Nat.le_of_lt_succ i.isLt)]
  · rfl
private theorem hasLaw_randomizedChain {g : ξ → α} {f : α → ξ → α}
    (hg : Measurable g) (hf : Measurable (uncurry f))
    {U : ℕ → Ω → ξ} {P : Measure Ω} (hU : ∀ i, Measurable (U i))
    (hindep : iIndepFun U P) {ρ : Measure ξ} (hlaw : ∀ i, HasLaw (U i) ρ P)
    (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ]
    (hg_map : ρ.map g = ν) (hf_map : ∀ x, ρ.map (f x) = κ x) :
    HasLaw (fun ω => randomizedChain g f (fun i => U i ω)) (homogeneousLaw ν κ) P := by
  have := hindep.isProbabilityMeasure
  have : IsProbabilityMeasure ρ := (hlaw 0).isProbabilityMeasure_iff.mp inferInstance
  have : IsProbabilityMeasure ν := hg_map ▸ inferInstanceAs (IsProbabilityMeasure (ρ.map g))
  let X (ω : Ω) := randomizedChain g f (fun i => U i ω)
  have hX : Measurable X := (measurable_randomizedChain hg hf).comp (by fun_prop)
  refine ⟨hX.aemeasurable, measure_eq_of_prefix _ _ ?_⟩
  intro n
  rw [homogeneous_prefix_product, Measure.map_map (by fun_prop) hX]
  change P.map (fun ω (i : Fin (n+1)) => X ω i) = finiteProduct ν κ n
  induction n with
  | zero =>
    rw [finiteProduct, ← hg_map, Measure.map_map (by fun_prop) hg, ← (hlaw 0).map_eq,
      Measure.map_map (by fun_prop) (hU 0)]
    congr 1
    funext ω i
    simp [X, randomizedChain, Fin.fin_one_eq_zero i]
  | succ n ih =>
    let W (ω : Ω) (i : Fin (n+1)) := X ω i
    let η := κ.comap (fun w : Fin (n+1) → α => w (Fin.last n)) (measurable_pi_apply _)
    let F (w : Fin (n+1) → α) (u : ξ) := f (w (Fin.last n)) u
    have hW : Measurable W := by fun_prop
    have hp : P.map (fun ω => (W ω, F (W ω) (U (n+1) ω))) = (P.map W) ⊗ₘ η :=
      map_prodMk_eq_compProd_of_map (indepFun_randomizedChain_prefix hg hf hU hindep n)
        hW.aemeasurable (hlaw (n+1)) η F (by fun_prop) (fun w => hf_map (w (Fin.last n)))
    calc
      _ = (P.map (fun ω => (W ω, F (W ω) (U (n+1) ω)))).map
          (fun p => Fin.snoc p.1 p.2) := by
        rw [Measure.map_map (snoc_measurable n) (by fun_prop)]
        congr 1
        funext ω i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [X, W, F, randomizedChain]
        · simp [W]
      _ = _ := by rw [hp, show P.map W = _ from ih]; rfl
end Port

abbrev ArmNoise := ℕ+ → unitInterval
abbrev Noise := (Bool × ℕ+) → unitInterval
def armNoiseLaw : Measure ArmNoise := Measure.infinitePi fun _ => (volume : Measure unitInterval)
def noiseLaw : Measure Noise := Measure.infinitePi fun _ => (volume : Measure unitInterval)
instance : IsProbabilityMeasure armNoiseLaw := by unfold armNoiseLaw; infer_instance
instance : IsProbabilityMeasure noiseLaw := by unfold noiseLaw; infer_instance
def step (q : unitInterval) (b : Bool) (v : unitInterval) : Bool :=
  if b then false else if v < q then true else false
def Z (q : unitInterval) (x : Bool) (v : ArmNoise) : ℕ → Bool
  | 0 => x
  | n+1 => step q (Z q x v n) (v ⟨n+1,Nat.succ_pos n⟩)
def originalSource (qL qR : unitInterval) (x : Bool) (v : Noise) : Source :=
  (x, (fun n => Z qL x (fun k => v (false,k)) (n+1),
       fun n => Z qR x (fun k => v (true,k)) (n+1)))
def reference (qL qR : unitInterval) (x : Bool) : Measure Source :=
  ((armLaw qL x).prod (armLaw qR x)).map
    (fun p => (x,(fun n => p.1 (n+1), fun n => p.2 (n+1))))
private lemma measurable_step (q : unitInterval) : Measurable (uncurry (step q)) := by
  exact Measurable.ite (measurable_fst (measurableSet_singleton true)) measurable_const
    (Measurable.ite (measurableSet_lt measurable_snd measurable_const) measurable_const measurable_const)
private lemma step_law (q : unitInterval) (b : Bool) :
    (volume : Measure unitInterval).map (step q b) = transition q b := by
  apply Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply (measurable_step q).of_uncurry_left (measurableSet_singleton c)]
  cases b <;> cases c <;> simp [step, transition, bernoulliMeasure_def, Set.preimage]
  · change volume (Set.Ici q) = _
    rw [unitInterval.volume_Ici, ← unitInterval.coe_symm_eq,
      ← unitInterval.coe_toNNReal, ENNReal.ofReal_coe_nnreal]
  · change volume (Set.Iio q) = _
    rw [unitInterval.volume_Iio, ← unitInterval.coe_toNNReal, ENNReal.ofReal_coe_nnreal]
private lemma measurable_Z (q : unitInterval) (x : Bool) : Measurable (Z q x) := by
  apply measurable_pi_iff.mpr
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (measurable_step q).comp (ih.prodMk (measurable_pi_apply _))
private lemma shifted_recursion (q : unitInterval) (x : Bool) (v : ArmNoise) (n : ℕ) :
    Port.randomizedChain (step q x) (step q) (fun j => v ⟨j+1,Nat.succ_pos j⟩) n =
      Z q x v (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Port.randomizedChain, ih, Z]
private lemma tail_law (q : unitInterval) (x : Bool) :
    HasLaw (fun v : ArmNoise => fun n => Z q x v (n+1))
      (homogeneousLaw (transition q x) (transition q)) armNoiseLaw := by
  let U (n : ℕ) (v : ArmNoise) := v ⟨n+1,Nat.succ_pos n⟩
  have hind : iIndepFun U armNoiseLaw := by
    have h := iIndepFun_infinitePi (P := fun _ : ℕ+ => (volume : Measure unitInterval))
      (X := fun _ x => x) (fun _ => measurable_id)
    exact iIndepFun.precomp (g := fun n => (⟨n+1,Nat.succ_pos n⟩ : ℕ+))
      (fun a b h => Nat.succ_injective (congrArg Subtype.val h)) h
  have hlaw (n : ℕ) : HasLaw (U n) (volume : Measure unitInterval) armNoiseLaw :=
    ⟨(measurable_pi_apply _).aemeasurable, Measure.infinitePi_map_eval _ _⟩
  have h := Port.hasLaw_randomizedChain (U := U) (P := armNoiseLaw) (g := step q x)
    (measurable_step q).of_uncurry_left (measurable_step q)
    (fun n => measurable_pi_apply (⟨n+1,Nat.succ_pos n⟩ : ℕ+)) hind hlaw
    (transition q x) (transition q) (step_law q x) (step_law q)
  convert h using 1
  funext v n
  exact (shifted_recursion q x v n).symm
private theorem single_arm_prefix_mass (q : unitInterval) (x : Bool) (l : ℕ) (w : Fin (l+1) → Bool) :
    armNoiseLaw {v | ∀ i, Z q x v i.val = w i} =
      (Measure.dirac x) {w 0} * ∏ i : Fin l, transition q (w i.castSucc) {w i.succ} := by
  classical
  cases l with
  | zero =>
    have he : {v : ArmNoise | ∀ i : Fin 1, Z q x v i.val = w i} =
        if x = w 0 then Set.univ else ∅ := by ext v; simp [Z, Fin.forall_fin_one]
    rw [he]; split_ifs with h <;> simp [h]
  | succ n =>
    by_cases hx : x = w 0
    · have he : {v : ArmNoise | ∀ i : Fin (n+2), Z q x v i.val = w i} =
          {v : ArmNoise | ∀ i : Fin (n+1), Z q x v (i.val+1) = w i.succ} := by
        ext v
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h i; exact h i.succ
        · intro h i; exact Fin.cases hx (fun j => h j) i
      rw [he]
      have hm := (tail_law q x).map_eq
      have heq : armNoiseLaw {v : ArmNoise | ∀ i : Fin (n+1), Z q x v (i.val+1) = w i.succ} =
          ((homogeneousLaw (transition q x) (transition q)).map
            (fun y (i : Fin (n+1)) => y i.val)) {fun i => w i.succ} := by
        rw [← hm, Measure.map_map (by fun_prop) (by
          exact measurable_pi_iff.mpr fun n =>
            (measurable_pi_apply (n+1)).comp (measurable_Z q x))]
        rw [Measure.map_apply (by
          exact measurable_pi_iff.mpr fun i =>
            (measurable_pi_apply (i.val+1)).comp (measurable_Z q x)) (measurableSet_singleton _)]
        congr 1; ext v; simp [funext_iff]
      rw [heq]
      have h := D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
        (transition q x) (transition q) n (fun i => w i.succ)
      change ((homogeneousLaw (transition q x) (transition q)).map
          (fun y (i : Fin (n+1)) => y i.val)) {fun i => w i.succ} = _ at h
      rw [h, Fin.prod_univ_succ]
      simp [← hx]
    · have he : {v : ArmNoise | ∀ i : Fin (n+2), Z q x v i.val = w i} = ∅ := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h; exact hx (h 0)
      rw [he]; simp [hx]
private theorem single_arm_law (q : unitInterval) (x : Bool) :
    armNoiseLaw.map (Z q x) = armLaw q x := by
  apply measure_eq_of_prefix
  intro n
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_map (by fun_prop) (measurable_Z q x),
    Measure.map_apply (by
      exact measurable_pi_iff.mpr fun i => (measurable_pi_apply i.val).comp (measurable_Z q x))
      (measurableSet_singleton w)]
  have he : (fun v : ArmNoise => fun i : Fin (n+1) => Z q x v i.val) ⁻¹' {w} =
      {v | ∀ i, Z q x v i.val = w i} := by ext v; simp [funext_iff]
  change armNoiseLaw ((fun v : ArmNoise => fun i : Fin (n+1) => Z q x v i.val) ⁻¹' {w}) = _
  rw [he, single_arm_prefix_mass]
  exact (D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
    (Measure.dirac x) (transition q) n w).symm
private lemma measurable_originalSource (qL qR : unitInterval) (x : Bool) :
    Measurable (originalSource qL qR x) := by
  apply Measurable.prodMk measurable_const
  exact (measurable_pi_iff.mpr fun n =>
    ((measurable_pi_apply (n+1)).comp (measurable_Z qL x)).comp
      (show Measurable (fun v : Noise => fun k : ℕ+ => v (false,k)) by fun_prop)).prodMk
    (measurable_pi_iff.mpr fun n =>
    ((measurable_pi_apply (n+1)).comp (measurable_Z qR x)).comp
      (show Measurable (fun v : Noise => fun k : ℕ+ => v (true,k)) by fun_prop))
private theorem originalSource_law (qL qR : unitInterval) (x : Bool) :
    noiseLaw.map (originalSource qL qR x) = reference qL qR x := by
  let splitNoise (v : Noise) : ArmNoise × ArmNoise :=
    (fun k => v (false,k), fun k => v (true,k))
  have hs : Measurable splitNoise := by fun_prop
  have hc : noiseLaw.map (MeasurableEquiv.curry Bool ℕ+ unitInterval) =
      Measure.infinitePi (fun _ : Bool => armNoiseLaw) :=
    Measure.infinitePi_map_curry (fun (_ : Bool) (_ : ℕ+) => (volume : Measure unitInterval))
  have hp : noiseLaw.map splitNoise = armNoiseLaw.prod armNoiseLaw := by
    change noiseLaw.map ((fun v : Bool → ArmNoise => (v false,v true)) ∘
      MeasurableEquiv.curry Bool ℕ+ unitInterval) = _
    rw [← Measure.map_map (by fun_prop) (MeasurableEquiv.curry Bool ℕ+ unitInterval).measurable, hc]
    exact Measure.infinitePi_map_eval_prod (by decide : false ≠ true)
  have hpaths : noiseLaw.map (fun v =>
      (Z qL x (fun k => v (false,k)), Z qR x (fun k => v (true,k)))) =
      (armLaw qL x).prod (armLaw qR x) := by
    rw [← single_arm_law qL x, ← single_arm_law qR x,
      Measure.map_prod_map _ _ (measurable_Z qL x) (measurable_Z qR x), ← hp,
      Measure.map_map ((measurable_Z qL x).prodMap (measurable_Z qR x)) hs]
    rfl
  unfold reference
  rw [← hpaths, Measure.map_map (by fun_prop) (by
    exact ((measurable_Z qL x).comp (by fun_prop)).prodMk
      ((measurable_Z qR x).comp (by fun_prop)))]
  rfl

namespace First
def Q (q : unitInterval) : ℝ≥0∞ := unitInterval.toNNReal q
def e (x : Bool) (c : ℕ) : ℕ := if x then c / 2 else (c + 1) / 2
abbrev K := reference
instance (qL qR : unitInterval) (x : Bool) : IsProbabilityMeasure (K qL qR x) := by
  unfold K reference
  infer_instance
private theorem cylinder_mass (qL qR : unitInterval) (x : Bool) (left right : ℕ) :
    K qL qR x (noMarkerCylinder left right) = Q qL ^ e x left * Q qR ^ e x right := by
  classical
  unfold K reference
  rw [Measure.map_apply (by fun_prop) (measurable_set_no_marker_cylinder left right)]
  let A (n : ℕ) : Set Path := {p | ∀ i ≤ n, p i = alternatingBit x i}
  have hs : ∀ᵐ p ∂(armLaw qL x).prod (armLaw qR x),
      (p.1 0 = x ∧ ∀ i, ¬(p.1 i = true ∧ p.1 (i + 1) = true)) ∧
      (p.2 0 = x ∧ ∀ i, ¬(p.2 i = true ∧ p.2 (i + 1) = true)) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [path_support qL x] with p hp
    filter_upwards [path_support qR x] with r hr
    exact ⟨hp, hr⟩
  have he : (fun p : Path × Path =>
      (x, (fun i => p.1 (i + 1), fun i => p.2 (i + 1)))) ⁻¹'
        noMarkerCylinder left right =ᵐ[(armLaw qL x).prod (armLaw qR x)]
        A left ×ˢ A right := by
    filter_upwards [hs] with p hp
    have hL := no_marker_iff_alternating_prefix x p.1 hp.1.1 hp.1.2 left
    have hR := no_marker_iff_alternating_prefix x p.2 hp.2.1 hp.2.2 right
    have hend (side : Bool) (i : ℕ) :
        endpoint (x, (fun j => p.1 (j + 1), fun j => p.2 (j + 1))) side i =
          if side then p.2 i else p.1 i := by
      cases i <;> cases side <;> simp [endpoint, arm, hp.1.1, hp.2.1]
    apply propext
    change ((x, (fun i => p.1 (i + 1), fun i => p.2 (i + 1))) ∈
      noMarkerCylinder left right ↔ p.1 ∈ A left ∧ p.2 ∈ A right)
    simp only [noMarkerCylinder, Set.mem_ofPred_eq, markerResponse, hend, arm,
      Bool.forall_bool, Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not, A]
    exact and_congr hL hR
  rw [measure_congr he, Measure.prod_prod]
  exact congrArg₂ (· * ·) (arm_alternating_mass qL x left) (arm_alternating_mass qR x right)
private theorem prefix_cylinder (actions : List Side) :
    {s | prefixNoMarker s actions} =
      noMarkerCylinder (sideCount actions false) (sideCount actions true) := by
  ext s
  simp only [prefixNoMarker, noMarkerCylinder, Set.mem_ofPred_eq]
  constructor <;> intro h side i hi <;> cases side <;> exact h _ _ hi
private theorem tail_event {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (n : ℕ) :
    {s | (n : WithTop ℕ) < stoppingTime policy seed s} =
      noMarkerCylinder (sideCount (zeroReplay policy seed n) false)
        (sideCount (zeroReplay policy seed n) true) := by
  rw [← prefix_cylinder]
  ext s
  exact (stopped_execution_replay_bridge policy seed s n).1
private theorem first_event {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (n : ℕ) :
    {s | stoppingTime policy seed s = ((n + 1 : ℕ) : WithTop ℕ)} =
      {s | (n : WithTop ℕ) < stoppingTime policy seed s} \
      {s | ((n + 1 : ℕ) : WithTop ℕ) < stoppingTime policy seed s} := by
  ext s
  change stoppingTime policy seed s = ((n + 1 : ℕ) : WithTop ℕ) ↔
    (n : WithTop ℕ) < stoppingTime policy seed s ∧
      ¬((n + 1 : ℕ) : WithTop ℕ) < stoppingTime policy seed s
  generalize stoppingTime policy seed s = t
  rcases eq_or_ne t ⊤ with rfl | ht
  · have hn : ((n + 1 : ℕ) : WithTop ℕ) < ⊤ := WithTop.coe_lt_top (n + 1)
    constructor
    · intro h; exact False.elim ((ne_of_lt hn) h.symm)
    · rintro ⟨_, h⟩; exact False.elim (h hn)
  · obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.mp ht
    constructor
    · intro hk
      have he : k = n + 1 := WithTop.coe_inj.mp hk
      have hn : n < k := by omega
      refine ⟨WithTop.coe_lt_coe.mpr hn, ?_⟩
      intro hn
      have hn' : n + 1 < k := WithTop.coe_lt_coe.mp hn
      omega
    · rintro ⟨h1, h2⟩
      have h1' : n < k := WithTop.coe_lt_coe.mp h1
      have h2' : ¬n + 1 < k := fun h => h2 (WithTop.coe_lt_coe.mpr h)
      have he : k = n + 1 := by omega
      exact congrArg (fun k : ℕ => (k : WithTop ℕ)) he
private theorem exponent_step (x : Bool) (c : ℕ) :
    e x (c + 1) = e x c + (if alternatingBit x c = false then 1 else 0) := by
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;> cases x <;>
    simp [e, alternatingBit, hc] <;> omega
private theorem weight_step (qL qR : unitInterval) (x : Bool) (w : List Side) (j : Side) :
    Q qL ^ e x (sideCount (j :: w) false) * Q qR ^ e x (sideCount (j :: w) true) =
      (Q qL ^ e x (sideCount w false) * Q qR ^ e x (sideCount w true)) *
        (if alternatingBit x (sideCount w j) = false then Q (if j then qR else qL) else 1) := by
  cases j
  · have hL : sideCount (false :: w) false = sideCount w false + 1 := by simp [sideCount]
    have hR : sideCount (false :: w) true = sideCount w true := by simp [sideCount]
    rw [hL, hR, exponent_step]
    split_ifs <;> simp_all [pow_succ]
    all_goals ring
  · have hL : sideCount (true :: w) false = sideCount w false := by simp [sideCount]
    have hR : sideCount (true :: w) true = sideCount w true + 1 := by simp [sideCount]
    rw [hL, hR, exponent_step]
    split_ifs <;> simp_all [pow_succ]
    all_goals ring
private theorem first_mass {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (qL qR : unitInterval) (x : Bool) (n : ℕ) :
    let w := zeroReplay policy seed n
    let j := policy.choose seed w (List.replicate n false)
    K qL qR x {s | stoppingTime policy seed s = ((n + 1 : ℕ) : WithTop ℕ)} =
      if alternatingBit x (sideCount w j) = false then
        Q qL ^ e x (sideCount w false) * Q qR ^ e x (sideCount w true) *
          (1 - Q (if j then qR else qL)) else 0 := by
  classical
  dsimp only
  have hm (k : ℕ) : MeasurableSet
      {s | (k : WithTop ℕ) < stoppingTime policy seed s} := by
    rw [tail_event]
    exact measurable_set_no_marker_cylinder _ _
  have ht (k : ℕ) : K qL qR x {s | (k : WithTop ℕ) < stoppingTime policy seed s} =
      Q qL ^ e x (sideCount (zeroReplay policy seed k) false) *
        Q qR ^ e x (sideCount (zeroReplay policy seed k) true) := by
    rw [tail_event]
    exact cylinder_mass _ _ _ _ _
  have hsub : {s | ((n + 1 : ℕ) : WithTop ℕ) < stoppingTime policy seed s} ⊆
      {s | (n : WithTop ℕ) < stoppingTime policy seed s} := by
    intro s hs
    exact lt_trans (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)) hs
  rw [first_event, measure_sdiff hsub (hm (n + 1)).nullMeasurableSet
    (measure_ne_top (K qL qR x) _), ht n, ht (n + 1)]
  simp only [zeroReplay]
  rw [weight_step]
  by_cases h : alternatingBit x (sideCount (zeroReplay policy seed n)
    (policy.choose seed (zeroReplay policy seed n) (List.replicate n false))) = false
  · simp only [ite_eq_left h]
    have hf : Q qL ^ e x (sideCount (zeroReplay policy seed n) false) *
        Q qR ^ e x (sideCount (zeroReplay policy seed n) true) ≠ ∞ := by
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp [Q]))
        (ENNReal.pow_ne_top (by simp [Q]))
    simpa only [mul_one] using (ENNReal.mul_sub (a := Q qL ^ e x (sideCount (zeroReplay policy seed n) false) *
      Q qR ^ e x (sideCount (zeroReplay policy seed n) true))
      (b := 1) (c := Q (if policy.choose seed (zeroReplay policy seed n)
        (List.replicate n false) then qR else qL)) (by intro _ _; exact hf)).symm
  · simp only [ite_eq_right h, mul_one, tsub_self]

private theorem first_local_iff {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (s : Source) (n : ℕ) :
    stoppingTime policy seed s = ((n + 1 : ℕ) : WithTop ℕ) ↔
      prefixNoMarker s (zeroReplay policy seed n) ∧
        markerResponse s (policy.choose seed (zeroReplay policy seed n) (List.replicate n false))
          (sideCount (zeroReplay policy seed n)
            (policy.choose seed (zeroReplay policy seed n) (List.replicate n false))) = true := by
  have h := Set.ext_iff.mp (first_event policy seed n) s
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff] at h
  rw [(stopped_execution_replay_bridge policy seed s n).1,
    (stopped_execution_replay_bridge policy seed s (n + 1)).1] at h
  rw [zeroReplay, prefix_no_marker_cons] at h
  cases hm : markerResponse s
    (policy.choose seed (zeroReplay policy seed n) (List.replicate n false))
    (sideCount (zeroReplay policy seed n)
      (policy.choose seed (zeroReplay policy seed n) (List.replicate n false))) <;>
    simpa [hm] using h
def decodedState {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (t : ℕ) : State :=
  ⟨zeroReplay policy seed t, true :: List.replicate (t - 1) false, true⟩
def D {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (u : Seed × ℕ) : Seed × List (Side × Bool) :=
  (u.1, ((zeroReplay policy u.1 u.2).zip
    (true :: List.replicate (u.2 - 1) false)).reverse)
def acquiredRecord {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (s : Source) (t : ℕ) : Seed × List (Side × Bool) :=
  (seed, ((actualRun policy seed s t).actions.zip (actualRun policy seed s t).replies).reverse)
private theorem first_state_iff {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (s : Source) (n : ℕ) :
    stoppingTime policy seed s = ((n + 1 : ℕ) : WithTop ℕ) ↔
      actualRun policy seed s (n + 1) = decodedState policy seed (n + 1) := by
  constructor
  · intro ht
    obtain ⟨hp, hm⟩ := (first_local_iff policy seed s n).mp ht
    have hf := (stopped_execution_replay_bridge policy seed s n).2.1.mpr hp
    obtain ⟨ha, hr, _⟩ := (stopped_execution_replay_bridge policy seed s n).2.2.1 hf
    simp [actualRun, hf, ha, hr, decodedState, zeroReplay, hm]
  · intro hs
    have hstop : (actualRun policy seed s (n + 1)).stopped = true := by rw [hs]; rfl
    have hle : stoppingTime policy seed s ≤ ((n + 1 : ℕ) : WithTop ℕ) := by
      apply le_of_not_gt
      intro h
      have hf := (stopped_execution_replay_bridge policy seed s (n + 1)).2.1.mpr
        ((stopped_execution_replay_bridge policy seed s (n + 1)).1.mp h)
      rw [hstop] at hf
      contradiction
    have hc := (stopped_execution_replay_bridge policy seed s (n + 1)).2.2.2.2.2
    have ha : actualQueryCount policy seed s (n + 1) = n + 1 := by
      simp [actualQueryCount, hs, decodedState, zero_replay_length]
    rw [ha, min_eq_right hle] at hc
    exact hc.symm
private theorem first_record_iff {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (s : Source) (n : ℕ) :
    stoppingTime policy seed s = ((n + 1 : ℕ) : WithTop ℕ) ↔
      acquiredRecord policy seed s (n + 1) = D policy (seed, n + 1) := by
  constructor
  · intro ht
    have hs := (first_state_iff policy seed s n).mp ht
    simp [acquiredRecord, D, hs, decodedState]
  · intro hrec
    have hword := congrArg Prod.snd hrec
    change ((actualRun policy seed s (n + 1)).actions.zip
      (actualRun policy seed s (n + 1)).replies).reverse =
      ((zeroReplay policy seed (n + 1)).zip (true :: List.replicate n false)).reverse at hword
    have hz := List.reverse_injective hword
    have hstop : (actualRun policy seed s (n + 1)).stopped = true := by
      cases hb : (actualRun policy seed s (n + 1)).stopped with
      | true => rfl
      | false =>
        obtain ⟨ha, hr, _⟩ := (stopped_execution_replay_bridge policy seed s (n + 1)).2.2.1 hb
        rw [ha, hr] at hz
        simp [zeroReplay, List.replicate_succ] at hz
    have hlen : ((actualRun policy seed s (n + 1)).actions.zip
        (actualRun policy seed s (n + 1)).replies).length = n + 1 := by
      rw [hz]
      simp [List.length_zip, zero_replay_length]
    have hnat : n + 1 ≤ actualQueryCount policy seed s (n + 1) := by
      change n + 1 ≤ (actualRun policy seed s (n + 1)).actions.length
      calc n + 1 = ((actualRun policy seed s (n + 1)).actions.zip
          (actualRun policy seed s (n + 1)).replies).length := hlen.symm
        _ = min (actualRun policy seed s (n + 1)).actions.length
          (actualRun policy seed s (n + 1)).replies.length := List.length_zip
        _ ≤ (actualRun policy seed s (n + 1)).actions.length := Nat.min_le_left _ _
    have hlow : ((n + 1 : ℕ) : WithTop ℕ) ≤ stoppingTime policy seed s := by
      calc ((n + 1 : ℕ) : WithTop ℕ)
          ≤ (actualQueryCount policy seed s (n + 1) : WithTop ℕ) := WithTop.coe_le_coe.mpr hnat
        _ = min ((n + 1 : ℕ) : WithTop ℕ) (stoppingTime policy seed s) :=
          (stopped_execution_replay_bridge policy seed s (n + 1)).2.2.2.2.2
        _ ≤ stoppingTime policy seed s := min_le_right _ _
    have hupp : stoppingTime policy seed s ≤ ((n + 1 : ℕ) : WithTop ℕ) := by
      apply le_of_not_gt
      intro h
      have hf := (stopped_execution_replay_bridge policy seed s (n + 1)).2.1.mpr
        ((stopped_execution_replay_bridge policy seed s (n + 1)).1.mp h)
      rw [hstop] at hf
      contradiction
    exact le_antisymm hupp hlow
private theorem first_record_mass {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (qL qR : unitInterval) (x : Bool) (n : ℕ) :
    let w := zeroReplay policy seed n
    let j := policy.choose seed w (List.replicate n false)
    K qL qR x {s | acquiredRecord policy seed s (n + 1) = D policy (seed, n + 1)} =
      if alternatingBit x (sideCount w j) = false then
        Q qL ^ e x (sideCount w false) * Q qR ^ e x (sideCount w true) *
          (1 - Q (if j then qR else qL)) else 0 := by
  have he : {s | acquiredRecord policy seed s (n + 1) = D policy (seed, n + 1)} =
      {s | stoppingTime policy seed s = ((n + 1 : ℕ) : WithTop ℕ)} := by
    ext s
    exact (first_record_iff policy seed s n).symm
  dsimp only
  rw [he]
  exact first_mass policy seed qL qR x n
private theorem first_record_measurable_set {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (seed : Seed) (n : ℕ) :
    MeasurableSet {s | acquiredRecord policy seed s (n + 1) = D policy (seed, n + 1)} := by
  have he : {s | acquiredRecord policy seed s (n + 1) = D policy (seed, n + 1)} =
      {s | stoppingTime policy seed s = ((n + 1 : ℕ) : WithTop ℕ)} := by
    ext s
    exact (first_record_iff policy seed s n).symm
  rw [he, first_event, tail_event, tail_event]
  exact (measurable_set_no_marker_cylinder _ _).diff (measurable_set_no_marker_cylinder _ _)
end First

abbrev Parameters := unitInterval × unitInterval
variable {Seed : Type*} [MeasurableSpace Seed]
def likelihood (policy : Policy Seed) (u : Seed) (θ : Parameters) (root : Bool) (n : ℕ) : ℝ≥0∞ :=
  let w := zeroReplay policy u n
  let j := policy.choose u w (List.replicate n false)
  if alternatingBit root (sideCount w j) = false then
    First.Q θ.1 ^ First.e root (sideCount w false) *
      First.Q θ.2 ^ First.e root (sideCount w true) *
        (1 - First.Q (if j then θ.2 else θ.1)) else 0

private theorem original_first_record_mass (policy : Policy Seed) (u : Seed)
    (qL qR : unitInterval) (root : Bool) (n : ℕ) :
    noiseLaw {v | First.acquiredRecord policy u (originalSource qL qR root v) (n+1) =
      First.D policy (u,n+1)} = likelihood policy u (qL,qR) root n := by
  calc
    _ = (noiseLaw.map (originalSource qL qR root))
        {s | First.acquiredRecord policy u s (n+1) = First.D policy (u,n+1)} :=
      (Measure.map_apply (measurable_originalSource qL qR root)
        (First.first_record_measurable_set policy u n)).symm
    _ = _ := by
      rw [originalSource_law]
      exact First.first_record_mass policy u qL qR root n


end Original

/-- Every legal finite label replay has strictly positive original-noise mass
at its fixed original seed, fixed common root, and fixed open-square parameters. -/
theorem finite_label_original_realization
    {Seed : Type*} [MeasurableSpace Seed]
    (p : Policy Seed) (u : Seed) (w : Word)
    (ht : terminalFirstTrue w) (hp : policyConformity p u w) (z : Labels w)
    (qL qR : unitInterval)
    (hL : 0 < (qL : ℝ) ∧ (qL : ℝ) < 1)
    (hR : 0 < (qR : ℝ) ∧ (qR : ℝ) < 1) :
    (∀ side : Side,
      0 < Original.First.Q (if side then qR else qL) ∧
      0 < 1 - Original.First.Q (if side then qR else qL)) ∧
    (0 < Original.noiseLaw {v : Original.Noise |
      Original.First.acquiredRecord p u
        (Original.originalSource qL qR (completion z).1 v) w.length = (u, w)}) ∧
    (∃ v : Original.Noise,
      Original.First.acquiredRecord p u
        (Original.originalSource qL qR (completion z).1 v) w.length = (u, w)) := by
  classical
  have factor (q : unitInterval) (hq : 0 < (q : ℝ) ∧ (q : ℝ) < 1) :
      0 < Original.First.Q q ∧ 0 < 1 - Original.First.Q q := by
    have hzero : (0 : ℝ≥0) < unitInterval.toNNReal q := by exact_mod_cast hq.1
    have hone : unitInterval.toNNReal q < (1 : ℝ≥0) := by exact_mod_cast hq.2
    constructor
    · exact ENNReal.coe_pos.mpr hzero
    · apply tsub_pos_iff_lt.mpr
      change (unitInterval.toNNReal q : ℝ≥0∞) < 1
      exact_mod_cast hone
  have factors (side : Side) :
      0 < Original.First.Q (if side then qR else qL) ∧
      0 < 1 - Original.First.Q (if side then qR else qL) := by
    cases side
    · exact factor qL hL
    · exact factor qR hR
  have hr := finite_label_realization p u w ht hp z
  obtain ⟨n, hlen⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.1; omega : w.length ≠ 0)
  change w.length = n + 1 at hlen
  have hstop : stoppingTime p u (completion z) = ((n + 1 : ℕ) : WithTop ℕ) := by
    simpa [hlen] using hr.2.2.2.2.2
  have hrecord : Original.First.acquiredRecord p u (completion z) (n + 1) = (u, w) := by
    unfold Original.First.acquiredRecord
    rw [← hlen, hr.2.2.2.1]
    congr 1
    simp only [← List.map_reverse, List.zip_map', Prod.eta, List.map_id', List.reverse_reverse]
  have hdecoder : Original.First.D p (u, n + 1) = (u, w) :=
    ((Original.First.first_record_iff p u (completion z) n).mp hstop).symm.trans hrecord
  let before := zeroReplay p u n
  let side := p.choose u before (List.replicate n false)
  have hlocal := (Original.First.first_local_iff p u (completion z) n).mp hstop
  have halt : endpoint (completion z) side (sideCount before side) =
      alternatingBit (completion z).1 (sideCount before side) := by
    apply (no_marker_iff_alternating_prefix (completion z).1
      (endpoint (completion z) side) rfl (fun i => hr.1 side i)
      (sideCount before side)).mp ?_ _ le_rfl
    intro i hi
    exact of_decide_eq_false (hlocal.1 side i hi)
  have hbranch : alternatingBit (completion z).1 (sideCount before side) = false :=
    halt.symm.trans (of_decide_eq_true hlocal.2).1
  have hmass := Original.original_first_record_mass p u qL qR (completion z).1 n
  have hpositive : 0 < Original.likelihood p u (qL,qR) (completion z).1 n := by
    change 0 < if alternatingBit (completion z).1 (sideCount before side) = false then
      Original.First.Q qL ^ Original.First.e (completion z).1 (sideCount before false) *
      Original.First.Q qR ^ Original.First.e (completion z).1 (sideCount before true) *
      (1 - Original.First.Q (if side then qR else qL)) else 0
    rw [ite_eq_left hbranch]
    exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.mul_pos_iff.mpr
      ⟨ENNReal.pow_pos (factors false).1 _,
       ENNReal.pow_pos (factors true).1 _⟩, (factors side).2⟩
  rw [hdecoder, ← hlen] at hmass
  have hpos : 0 < Original.noiseLaw {v : Original.Noise |
      Original.First.acquiredRecord p u
        (Original.originalSource qL qR (completion z).1 v) w.length = (u,w)} := by
    rw [hmass]
    exact hpositive
  exact ⟨factors, hpos, nonempty_of_measure_ne_zero hpos.ne'⟩

end

end D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerFiniteLabels
