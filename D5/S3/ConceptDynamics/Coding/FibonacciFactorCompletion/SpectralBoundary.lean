/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual retained weighted path series converges exactly below spectral radius one. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.GCongr

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary

open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open Filter Topology
open scoped ENNReal NNReal Matrix.Norms.Operator

/- The following consumed supplier is transplanted from
LionSR/QICLean, revision c61daa23f385237a4d992a602c94812ca9f909b8,
QICLean/Analysis/SpectralRadiusPowerDecay.lean.
Copyright (c) 2026 TNLean contributors. All rights reserved.
Authors: TNLean contributors.
The supplier is replaced by direct application when the pinned Mathlib contains
geometric_bound_of_spectralRadius_lt with this complete telescope and conclusion.
The Notes notice applies only to Notes and does not cover this Lean source.
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

theorem geometric_bound_supplier
    {A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A]
    (a : A) (rate : ℝ≥0) (ha : spectralRadius ℂ a < (rate : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * (rate : ℝ) ^ n := by
  have hrate_pos : 0 < (rate : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt
      (show (0 : ℝ≥0∞) ≤ spectralRadius ℂ a from bot_le) ha)
  have hev : ∀ᶠ n in Filter.atTop, ‖a ^ n‖₊ < rate ^ n := by
    have gelfand := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
    filter_upwards [gelfand.eventually (eventually_lt_nhds ha),
      Filter.eventually_gt_atTop 0] with n hn hn_pos
    rw [one_div, ENNReal.rpow_inv_lt_iff (Nat.cast_pos.mpr hn_pos)] at hn
    rw [ENNReal.rpow_natCast] at hn
    exact_mod_cast hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  let S : ℝ := Finset.sum (Finset.range N) fun k => ‖a ^ k‖ / (rate : ℝ) ^ k
  let C : ℝ := S + 1
  refine ⟨C, by positivity, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hnorm : ‖a ^ n‖ ≤ (rate : ℝ) ^ n := by
      exact_mod_cast (hN n hn).le
    have hC_ge_one : 1 ≤ C := by
      have hS_nonneg : 0 ≤ S := by
        dsimp [S]
        positivity
      dsimp [C]
      linarith
    calc
      ‖a ^ n‖ ≤ (rate : ℝ) ^ n := hnorm
      _ = 1 * (rate : ℝ) ^ n := by ring
      _ ≤ C * (rate : ℝ) ^ n := by
        gcongr
  · have hn_lt : n < N := Nat.lt_of_not_ge hn
    have hterm : ‖a ^ n‖ / (rate : ℝ) ^ n ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum
        (f := fun k => ‖a ^ k‖ / (rate : ℝ) ^ k)
        (by intro k hk; positivity)
        (Finset.mem_range.mpr hn_lt)
    have hterm' : ‖a ^ n‖ ≤ S * (rate : ℝ) ^ n := by
      exact (div_le_iff₀ (pow_pos hrate_pos n)).1 hterm
    have hS_le_C : S ≤ C := by
      dsimp [C]
      linarith
    calc
      ‖a ^ n‖ ≤ S * (rate : ℝ) ^ n := hterm'
      _ ≤ C * (rate : ℝ) ^ n := by
        gcongr

noncomputable def complexAdjacency (side : MemorySide) (n K : ℕ) (d z : ℝ) :
    Matrix (CoreVertex side n K d) (CoreVertex side n K d) ℂ :=
  (weightedAdjacency side n K d z).map (algebraMap ℝ ℂ)

noncomputable def weightedRadius (side : MemorySide) (n K : ℕ) (d z : ℝ) : ℝ≥0∞ :=
  spectralRadius ℂ (complexAdjacency side n K d z)

noncomputable def pathMass (side : MemorySide) (n K : ℕ) (d z : ℝ) (k : ℕ) : ℝ :=
  ∑ v : CoreVertex side n K d, ∑ t : CoreVertex side n K d,
    (weightedAdjacency side n K d z ^ k) v t

private theorem complex_power (side : MemorySide) (n K : ℕ) (d z : ℝ) (k : ℕ) :
    complexAdjacency side n K d z ^ k =
      (weightedAdjacency side n K d z ^ k).map (algebraMap ℝ ℂ) :=
  (Matrix.map_pow _ (algebraMap ℝ ℂ) k).symm

private theorem power_nonnegative (side : MemorySide) (n K : ℕ) (d z : ℝ)
    (nonnegative : 0 ≤ z) (k : ℕ) :
    ∀ v t, 0 ≤ (weightedAdjacency side n K d z ^ k) v t := by
  classical
  induction k with
  | zero => intro v t; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro v t
    rw [pow_succ,Matrix.mul_apply]
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (ih v j)
    unfold weightedAdjacency
    apply Finset.sum_nonneg
    intro a _
    split_ifs <;> positivity

theorem path_mass_norm_bounds (side : MemorySide) (n K : ℕ) (d z : ℝ)
    (nonnegative : 0 ≤ z) (k : ℕ) :
    0 ≤ pathMass side n K d z k ∧
    ‖complexAdjacency side n K d z ^ k‖ ≤ pathMass side n K d z k ∧
    pathMass side n K d z k ≤
      Fintype.card (CoreVertex side n K d) * ‖complexAdjacency side n K d z ^ k‖ := by
  classical
  let C := CoreVertex side n K d
  let A := complexAdjacency side n K d z
  let M := weightedAdjacency side n K d z
  have entry := power_nonnegative side n K d z nonnegative k
  have row (v : C) : ((∑ t : C, ‖(A^k) v t‖₊ : ℝ≥0) : ℝ) = ∑ t : C, (M^k) v t := by
    simp only [NNReal.coe_sum,coe_nnnorm,A,complex_power,Matrix.map_apply,M]
    apply Finset.sum_congr rfl
    intro t _
    change ‖((weightedAdjacency side n K d z ^ k) v t : ℂ)‖ =
      (weightedAdjacency side n K d z ^ k) v t
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (entry v t)]
  have positive : 0 ≤ pathMass side n K d z k :=
    Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun t _ => entry v t))
  refine ⟨positive,?_,?_⟩
  · rw [Matrix.linfty_opNorm_def]
    have bound : (Finset.univ.sup fun v : C => ∑ t : C, ‖(A^k) v t‖₊) ≤
        Real.toNNReal (pathMass side n K d z k) := by
      apply Finset.sup_le
      intro v hv
      apply NNReal.coe_le_coe.mp
      rw [row,Real.toNNReal_of_nonneg positive]
      exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun t _ => entry j t)) hv
    have b := NNReal.coe_le_coe.mpr bound
    rw [Real.coe_toNNReal _ positive] at b
    exact b
  · have bound (v : C) : (∑ t : C, (M^k) v t) ≤ ‖A^k‖ := by
      rw [← row,Matrix.linfty_opNorm_def]
      exact_mod_cast (Finset.le_sup (f := fun v : C => ∑ t : C, ‖(A^k) v t‖₊)
        (Finset.mem_univ v))
    change (∑ v : C, ∑ t : C, (M^k) v t) ≤ (Fintype.card C : ℝ) * ‖A^k‖
    calc
      _ ≤ ∑ _v : C, ‖A^k‖ := Finset.sum_le_sum (fun v _ => bound v)
      _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

/-- The sum of all actual retained labeled path weights is convergent precisely
when the complex spectral radius of their original weighted adjacency is below
one. At radius one it diverges. No connectivity assumption is imposed. -/
theorem original_weighted_series_boundary (side : MemorySide) (n K : ℕ) (d z : ℝ)
    (nonnegative : 0 ≤ z) :
    (Summable (fun k : ℕ => ∑ v : CoreVertex side n K d,
      ∑ choices : Fin k → CuLetter × CoreVertex side n K d,
        coreMonomial side K d z k v choices)) ↔ weightedRadius side n K d z < 1 := by
  classical
  let C := CoreVertex side n K d
  let A := complexAdjacency side n K d z
  have exact_mass : (fun k : ℕ => ∑ v : C,
      ∑ choices : Fin k → CuLetter × C, coreMonomial side K d z k v choices) =
      pathMass side n K d z := by
    funext k
    unfold pathMass
    apply Finset.sum_congr rfl
    intro v _
    exact ((original_weighted_adjacency_paths side n K d z).2 k v).symm
  rw [exact_mass]
  have bounds := path_mass_norm_bounds side n K d z nonnegative
  constructor
  · intro converges
    rcases isEmpty_or_nonempty C with empty | occupied
    · letI := empty
      exact (spectrum.SpectralRadius.of_subsingleton A).trans_lt (by norm_num)
    · letI := occupied
      have powers : Summable (fun k : ℕ => A^k) :=
        converges.of_norm_bounded (fun k => (bounds k).2.1)
      have small := (powers.tendsto_atTop_zero.norm).eventually (eventually_lt_nhds
        (show ‖(0 : Matrix C C ℂ)‖ < 1 by simp))
      obtain ⟨N,hN⟩ := eventually_atTop.mp small
      have gap : (spectralRadius ℂ A)^(N+1) < 1 :=
        (spectrum.spectralRadius_pow_le A (N+1) (by omega)).trans_lt
          ((spectrum.spectralRadius_le_nnnorm (A^(N+1))).trans_lt (by
            exact_mod_cast hN (N+1) (by omega)))
      exact (pow_lt_one_iff (by omega : N+1≠0)).mp gap
  · intro gap
    obtain ⟨r,above,below⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp gap
    obtain ⟨B,hB,estimate⟩ := geometric_bound_supplier A r above
    have geometric : Summable (fun k : ℕ => (r : ℝ)^k) :=
      summable_geometric_of_lt_one r.coe_nonneg (by exact_mod_cast below)
    apply ((geometric.mul_left B).mul_left (Fintype.card C : ℝ)).of_norm_bounded
    intro k
    rw [Real.norm_eq_abs,abs_of_nonneg (bounds k).1]
    exact (bounds k).2.2.trans (mul_le_mul_of_nonneg_left (estimate k) (by positivity))

/-- A threshold above both actual one-letter seed images disables every c edge
at K=n=1, for either original memory guard convention. -/
noncomputable def oneStepCeiling : ℝ :=
  max (max 0 (aSide .high)) (max (chi * hSide .high) (hSide .high))

private theorem one_step_no_c (side : MemorySide) (d : ℝ) (high : oneStepCeiling < d)
    (v t : MemoryVertex 1) : ¬ MemoryEdge side 1 d v .c t := by
  intro edge
  have guard := edge.2.2 (show memoryRun v .c 1 from ⟨rfl,fun k hk => by omega⟩)
  have c0 : (0 : ℝ) ≤ oneStepCeiling := (le_max_left _ _).trans (le_max_left _ _)
  have au : aSide .high ≤ oneStepCeiling := (le_max_right _ _).trans (le_max_left _ _)
  have ch : chi * hSide .high ≤ oneStepCeiling :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hh : hSide .high ≤ oneStepCeiling :=
    (le_max_right _ _).trans (le_max_right _ _)
  cases side <;> simp only [memoryGuard,Nat.sub_self,pow_zero,one_mul,memoryValue] at guard
  · cases h : v 0 <;> simp only [h,letterMap,mul_zero,add_zero] at guard <;> linarith
  · cases h : v 0 <;> simp only [h,letterMap] at guard
    · linarith
    · have fixed : aSide .high + rho * hSide .high = hSide .high := by
        unfold aSide; ring
      rw [fixed] at guard
      linarith

private theorem all_u_path (side : MemorySide) (K : ℕ) (d : ℝ) :
    BilateralGraphPath side K d (fun _ => (fun _ : Fin 1 => CuLetter.u))
      (fun _ => CuLetter.u) := by
  intro i
  refine ⟨?_,?_,?_⟩
  · funext k
    simp [memoryShift]
  · simp [memoryRun]
  · simp [memoryRun]

private theorem one_step_live_u (side : MemorySide) (d : ℝ)
    (high : oneStepCeiling < d) (v : MemoryVertex 1) (live : LiveVertex side 1 d v) :
    v = fun _ => CuLetter.u := by
  rcases live with ⟨p,ω,path,start⟩
  have letters (i : ℤ) : ω i = .u := by
    cases h : ω i
    · exact False.elim (one_step_no_c side d high (p i) (p (i+1)) (h ▸ path i))
    · rfl
  have recovered := path_memory_reconstruction p ω (fun i => (path i).1)
  rw [recovered] at start
  rw [← start]
  funext k
  exact letters _

private theorem all_u_factor_rate :
    weightedFactorRate ({fun _ : ℤ => CuLetter.u} : Set (ℤ → CuLetter)) = 0 := by
  classical
  let X : Set (ℤ → CuLetter) := {fun _ => CuLetter.u}
  have weight (m : ℕ) : wordWeight (List.replicate m CuLetter.u) = 6*m := by
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ,wordWeight,ih,Nat.mul_add,Nat.add_comm]
  have shape (T : ℕ) (w : FactorDictionary X T) :
      w.val = List.replicate w.val.length CuLetter.u := by
    rcases w.property.1 with ⟨ω,hω,i,letters⟩
    change ω = (fun _ => CuLetter.u) at hω
    subst ω
    apply List.eq_replicate_iff.mpr
    refine ⟨rfl,?_⟩
    intro a ha
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp ha
    have h := letters ⟨j,hj⟩
    simpa only [Fin.getElem_fin,eq] using h.symm
  have bound (T : ℕ) : factorCount X T ≤ 1 := by
    have unique : Subsingleton (FactorDictionary X T) := by
      refine ⟨fun w v => ?_⟩
      apply Subtype.ext
      have ww := w.property.2
      have vv := v.property.2
      rw [shape T w,weight] at ww
      rw [shape T v,weight] at vv
      have len : w.val.length=v.val.length := by omega
      rw [shape T w,shape T v,len]
    let := unique
    have count := Nat.card_le_card_of_injective (fun _ : FactorDictionary X T => ())
      (fun _ _ _ => unique.elim _ _)
    simpa [factorCount] using count
  unfold weightedFactorRate
  have constant : (fun T : ℕ => Real.logb 2 ((max 1 (factorCount X T) : ℕ) : ℝ) /
      (T : ℝ)) = (fun _ : ℕ => (0 : ℝ)) := by
    funext T
    rw [max_eq_left (bound T)]
    simp
  change limsup (fun T : ℕ => Real.logb 2 ((max 1 (factorCount X T) : ℕ) : ℝ) /
      (T : ℝ)) atTop = 0
  rw [constant,limsup_const]

/-- The full positive-K scope includes a closed endpoint: at one-letter memory
and thresholds above the actual seed ceiling, both languages are all-u, their
spectral radius is z^6, and the unique nonnegative radius-one root is one. -/
theorem original_closed_root_boundary (side : MemorySide) (d : ℝ)
    (high : oneStepCeiling < d) :
    (MemoryLanguage side 1 1 d = {fun _ : ℤ => CuLetter.u}) ∧
    (∀ z : ℝ, 0 ≤ z → weightedRadius side 1 1 d z = ENNReal.ofReal (z^6)) ∧
    (∀ z : ℝ, 0 ≤ z → (weightedRadius side 1 1 d z = 1 ↔ z = 1)) ∧
    weightedFactorRate (MemoryLanguage side 1 1 d) = 0 := by
  classical
  let C := CoreVertex side 1 1 d
  have path := all_u_path side 1 d
  let vertex : C := ⟨fun _ => .u,⟨fun _ => (fun _ => .u),fun _ => .u,path,rfl⟩⟩
  let : Nonempty C := ⟨vertex⟩
  have only (v : C) : v.val = fun _ => CuLetter.u := one_step_live_u side d high v.val v.property
  let : Subsingleton C := ⟨fun v t => Subtype.ext ((only v).trans (only t).symm)⟩
  have radius (z : ℝ) (hz : 0 ≤ z) : weightedRadius side 1 1 d z = ENNReal.ofReal (z^6) := by
    have scalar : complexAdjacency side 1 1 d z =
        algebraMap ℂ (Matrix C C ℂ) (z^6 : ℝ) := by
      ext v t
      have eq : v=t := Subsingleton.elim _ _
      subst t
      have uedge : MemoryEdge side 1 d v.val .u v.val := by
        rw [only v]
        refine ⟨?_,?_,?_⟩
        · funext k; simp [memoryShift]
        · simp [memoryRun]
        · simp [memoryRun]
      have univ : (Finset.univ : Finset CuLetter) = {.c,.u} := rfl
      simp [complexAdjacency,weightedAdjacency,univ,one_step_no_c side d high,
        uedge,letterWeight,Algebra.algebraMap_eq_smul_one]
    unfold weightedRadius
    rw [scalar,spectralRadius,spectrum.scalar_eq]
    simp only [Set.mem_singleton_iff,iSup_iSup_eq_left]
    rw [ENNReal.coe_nnreal_eq,coe_nnnorm,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hz 6)]
  have language : MemoryLanguage side 1 1 d = {fun _ : ℤ => CuLetter.u} := by
    ext ω
    rw [Set.mem_singleton_iff,original_memory_graph_correspondence side 1 1 d
      (by decide) (by decide)]
    constructor
    · rintro ⟨p,ωpath,_⟩
      funext i
      cases h : ω i
      · exact False.elim (one_step_no_c side d high (p i) (p (i+1)) (h ▸ ωpath i))
      · rfl
    · intro eq
      subst ω
      refine ⟨fun _ => (fun _ => .u),path,?_⟩
      intro p hp
      exact path_memory_reconstruction p (fun _ => .u) (fun i => (hp i).1)
  refine ⟨language,radius,?_,?_⟩
  · intro z hz
    rw [radius z hz]
    constructor
    · intro eq
      have power : z^6 = 1 := by
        have same := congrArg ENNReal.toReal eq
        simpa [pow_nonneg hz 6] using same
      exact (pow_eq_one_iff_of_nonneg hz (by decide : (6 : ℕ) ≠ 0)).mp power
    · rintro rfl
      norm_num
  · rw [language]
    exact all_u_factor_rate

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
