/- GID: D5/S3/Arith/Additive/Waring/WaringDensity
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringDensity.lean#L1-L198
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import Mathlib.NumberTheory.SumFourSquares

open Finset

namespace Waring

/- Representation predicates from WaringStatement.lean and WaringBound.lean at the same
   revision, consolidated here. No change to their definitions.
   Copyright (c) 2026 The Waring formalization authors. All rights reserved.
   Released under Apache 2.0 license as described below.
   Authors: The Waring formalization authors -/

/-- `n` is a sum of `s` nonnegative `k`-th powers. -/
def IsSumOfKthPowers (k n s : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, n = ∑ i, (f i) ^ k

/-- The full Waring theorem, with an explicit bound `g` depending on `k`. -/
def WaringTheorem : Prop :=
  ∀ k : ℕ, 0 < k → ∃ g : ℕ, ∀ n : ℕ, ∃ s ≤ g, IsSumOfKthPowers k n s

/-- `g` is a Waring bound for exponent `k`: every natural number is a sum of at
most `g` nonnegative `k`-th powers. -/
def IsWaringBound (k g : ℕ) : Prop :=
  ∀ n : ℕ, ∃ s ≤ g, IsSumOfKthPowers k n s

/-- The number of elements of `A` in `[1, n]`. -/
noncomputable def densityCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).filter (fun m => m ∈ A)).card

/-- `A` has Schnirelmann density at least `δ`: every initial segment `[1,n]`
contains at least `δ n` elements of `A`. -/
def HasDensity (A : Set ℕ) (δ : ℚ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → δ * (n : ℚ) ≤ (densityCount A n : ℚ)

theorem hasDensity_le_one {A : Set ℕ} {δ : ℚ} (h : HasDensity A δ) : δ ≤ 1 := by
  have h1 := h 1 le_rfl
  have hc : densityCount A 1 ≤ 1 := by
    classical
    unfold densityCount
    have := Finset.card_le_card (Finset.filter_subset (fun m => m ∈ A) (Finset.Icc 1 1))
    simpa using this
  have : (densityCount A 1 : ℚ) ≤ 1 := by exact_mod_cast hc
  push_cast at h1
  linarith

theorem IsSumOfKthPowers.add {k n m s t : ℕ} (h1 : IsSumOfKthPowers k n s)
    (h2 : IsSumOfKthPowers k m t) : IsSumOfKthPowers k (n + m) (s + t) := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  refine ⟨Fin.append f g, ?_⟩
  rw [Fin.sum_univ_add, hf, hg]
  simp

/-- Two sets whose Schnirelmann densities sum to more than `1` cover `ℕ` by sums. -/
theorem add_eq_univ_of_density {A B : Set ℕ} {α β : ℚ}
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) (hA : HasDensity A α) (hB : HasDensity B β)
    (hαβ : 1 < α + β) : ∀ n : ℕ, ∃ a ∈ A, ∃ b ∈ B, a + b = n := by
  classical
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, hA0, 0, hB0, by simp⟩
  have hn1 : 1 ≤ n := hn
  by_contra hmem
  -- the three counting sets
  set s : Finset ℕ := (Finset.Icc 1 n).filter (fun m => m ∈ A) with hs
  set u : Finset ℕ := (Finset.range n).filter (fun m => m ∈ B) with hu
  set t : Finset ℕ := (Finset.range n).filter (fun m => ¬ m ∈ B) with ht
  have hs_card : (s.card : ℚ) = (densityCount A n : ℚ) := by
    rw [hs]
    simp [densityCount]
  -- `a ↦ n - a` maps `s` into `t`
  have himage : s.image (fun a => n - a) ⊆ t := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨ha1, han⟩, haA⟩ := ha
    rw [ht, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    intro hbB
    exact hmem ⟨a, haA, n - a, hbB, by omega⟩
  have hinj : Set.InjOn (fun a => n - a) ↑s := by
    intro a ha b hb hab
    have hab' : n - a = n - b := hab
    rw [Finset.mem_coe] at ha hb
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at ha hb
    omega
  have hst : s.card ≤ t.card := by
    have h := Finset.card_le_card himage
    rwa [Finset.card_image_of_injOn hinj] at h
  -- `u` and `t` partition `range n`
  have hut : u.card + t.card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.range n) (fun m => m ∈ B)
    rw [← hu, ← ht, Finset.card_range] at h
    omega
  -- `u` contains `0` together with all of `B ∩ [1, n-1]`
  have hinsert : insert 0 ((Finset.Icc 1 (n - 1)).filter (fun m => m ∈ B)) ⊆ u := by
    intro m hm
    rw [Finset.mem_insert] at hm
    rw [hu, Finset.mem_filter, Finset.mem_range]
    rcases hm with rfl | hm
    · exact ⟨by omega, hB0⟩
    · rw [Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hm1, hmn⟩, hmB⟩ := hm
      exact ⟨by omega, hmB⟩
  have h0not : (0 : ℕ) ∉ (Finset.Icc 1 (n - 1)).filter (fun m => m ∈ B) := by
    intro h
    rw [Finset.mem_filter, Finset.mem_Icc] at h
    omega
  have hucard : densityCount B (n - 1) + 1 ≤ u.card := by
    have h := Finset.card_le_card hinsert
    rw [Finset.card_insert_of_notMem h0not] at h
    have hc : ((Finset.Icc 1 (n - 1)).filter (fun m => m ∈ B)).card = densityCount B (n - 1) := by
      simp [densityCount]
    omega
  -- arithmetic
  have hAcard : α * (n : ℚ) ≤ (s.card : ℚ) := by
    rw [hs_card]
    exact hA n hn1
  have hBcard : β * ((n - 1 : ℕ) : ℚ) ≤ ((densityCount B (n - 1) : ℕ) : ℚ) := by
    rcases Nat.eq_or_lt_of_le hn1 with h1 | h1
    · have h0 : n - 1 = 0 := by omega
      rw [h0]
      simp [densityCount]
    · exact hB (n - 1) (by omega)
  have hnat : s.card + (densityCount B (n - 1) + 1) ≤ n := by omega
  have hnatq : (s.card : ℚ) + ((densityCount B (n - 1) : ℕ) : ℚ) + 1 ≤ (n : ℚ) := by
    exact_mod_cast hnat
  have hcast : (n : ℚ) = ((n - 1 : ℕ) : ℚ) + 1 := by
    rw [Nat.cast_sub hn1]
    ring
  have hβle : β ≤ 1 := hasDensity_le_one hB
  nlinarith [hAcard, hBcard, hαβ, hβle, hcast, hnatq]

end Waring

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

   Copyright 2026 The Waring-Lean4 Authors

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
