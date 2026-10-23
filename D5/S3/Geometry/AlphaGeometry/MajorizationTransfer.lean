/- GID: D5/S3/Geometry/AlphaGeometry/MajorizationTransfer
   generality: G
   mirror-B: D5/B/S3/Geometry/AlphaGeometry/MajorizationTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hardy--Littlewood--Polya transfer step for finite vectors. -/

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking, Claude Fable 5, Claude Opus 5.

This transplant is from LeanPool/DavisKahan/ForTauCeti/Analysis/Convex/Majorization.lean
at revision 7498a16d2393e1f02245cb265d67ec4fb2587814:
https://github.com/LeanPool/lean-pool/blob/7498a16d2393e1f02245cb265d67ec4fb2587814/LeanPool/DavisKahan/ForTauCeti/Analysis/Convex/Majorization.lean
The complete Apache-2.0 license and NOTICE chain are retained in
docs/reports/brooks-suppliers/daviskahan-LICENSE.txt and daviskahan-NOTICE.txt.
Retire this transplant when this repository's pinned Mathlib provides an equivalent
transfer lemma, and replace its consumers by direct applications.


admission_basis: escape-witness
escape_witness: FiniteVector.exists_isTTransform_of_not_forall_le
Direct frozen dependencies: none; all prerequisites are pinned Mathlib or this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15483
Per-declaration judgement form (definitions carry no new-content claim):
proof_shape: prefixSum: bind-only; consumer=LogScalarCurvatureMonotone.vector_prefix_eq_list; witness=none
proof_shape: prefixSum_eq_full_sum_of_le: bind-only; consumer=LogScalarCurvatureMonotone.moreMixed_sorted_prefix; witness=none
proof_shape: prefixSum_add: bind-only; consumer=FiniteVector.prefixSum_transfer; witness=none
proof_shape: transfer: bind-only; consumer=FiniteVector.transfer_apply_left; witness=none
proof_shape: IsTTransform: bind-only; consumer=LogScalarCurvatureMonotone.permutation_positive_chain; witness=none
proof_shape: transfer_apply_left: bind-only; consumer=FiniteVector.prefixSum_transfer; witness=none
proof_shape: transfer_apply_right: bind-only; consumer=FiniteVector.prefixSum_transfer; witness=none
proof_shape: transfer_apply_of_ne: bind-only; consumer=FiniteVector.prefixSum_transfer; witness=none
proof_shape: prefixSum_transfer: bind-only; consumer=FiniteVector.exists_isTTransform_of_not_forall_le; witness=none
proof_shape: isTTransform_transfer: bind-only; consumer=FiniteVector.exists_isTTransform_of_not_forall_le; witness=none
proof_shape: exists_isTTransform_of_not_forall_le: content; consumer=PositiveSimplexGeometryAndMixing.positive_sorted_chain; witness=exists_isTTransform_of_not_forall_le
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith


noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.AlphaGeometry.MajorizationTransfer

namespace FiniteVector

variable {n : ℕ}

def prefixSum (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), x i

theorem prefixSum_eq_full_sum_of_le (x : Fin n → ℝ) {k : ℕ} (hk : n ≤ k) :
    prefixSum k x = ∑ i, x i := by
  unfold prefixSum
  have hfilter : Finset.univ.filter (fun i : Fin n => (i : ℕ) < k) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le i.isLt hk
  rw [hfilter]

private theorem prefixSum_add (k : ℕ) (x y : Fin n → ℝ) :
    prefixSum k (x + y) = prefixSum k x + prefixSum k y := by
  simp [prefixSum, Finset.sum_add_distrib]

def transfer (q : Fin n → ℝ) (j l : Fin n) (δ : ℝ) : Fin n → ℝ :=
  Function.update (Function.update q j (q j - δ)) l (q l + δ)

def IsTTransform (y q : Fin n → ℝ) : Prop :=
  ∃ (j l : Fin n) (c : ℝ), 0 ≤ c ∧ c ≤ 1 ∧
    q = (1 - c) • y + c • (y ∘ Equiv.swap j l)

private theorem transfer_apply_left {q : Fin n → ℝ} {j l : Fin n} (hjl : j ≠ l) (δ : ℝ) :
    transfer q j l δ j = q j - δ := by
  rw [transfer, Function.update_of_ne hjl, Function.update_self]

private theorem transfer_apply_right (q : Fin n → ℝ) (j l : Fin n) (δ : ℝ) :
    transfer q j l δ l = q l + δ := by
  rw [transfer, Function.update_self]

private theorem transfer_apply_of_ne {q : Fin n → ℝ} {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l)
    (δ : ℝ) : transfer q j l δ i = q i := by
  rw [transfer, Function.update_of_ne hil, Function.update_of_ne hij]

private theorem prefixSum_transfer {q : Fin n → ℝ} {j l : Fin n} (hjl : j ≠ l) (δ : ℝ) (k : ℕ) :
    prefixSum k (transfer q j l δ) =
      prefixSum k q - (if (j : ℕ) < k then δ else 0) + (if (l : ℕ) < k then δ else 0) := by
  classical
  have hsplit : transfer q j l δ =
      q + ((fun i => if i = j then -δ else 0) + fun i => if i = l then δ else 0) := by
    funext i
    simp only [Pi.add_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [transfer_apply_left hjl, if_pos rfl, if_neg hjl]
      ring
    rcases eq_or_ne i l with rfl | hil
    · rw [transfer_apply_right, if_neg hij, if_pos rfl]
      ring
    · rw [transfer_apply_of_ne hij hil, if_neg hij, if_neg hil]
      ring
  have hj : prefixSum k (fun i : Fin n => if i = j then -δ else 0) =
      if (j : ℕ) < k then -δ else 0 := by
    simp [prefixSum]
  have hl : prefixSum k (fun i : Fin n => if i = l then δ else 0) =
      if (l : ℕ) < k then δ else 0 := by
    simp [prefixSum]
  rw [hsplit, prefixSum_add, prefixSum_add, hj, hl]
  split_ifs <;> ring

private theorem isTTransform_transfer {q : Fin n → ℝ} {j l : Fin n} (hjl : j ≠ l) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ q j - q l) : IsTTransform q (transfer q j l δ) := by
  rcases eq_or_lt_of_le (le_trans hδ0 hδ) with hzero | hpos
  · have h : δ = 0 := le_antisymm (hδ.trans hzero.symm.le) hδ0
    subst h
    refine ⟨j, l, 0, le_rfl, zero_le_one, ?_⟩
    simp [transfer]
  · set c : ℝ := δ / (q j - q l) with hc
    have hcmul : c * (q j - q l) = δ := div_mul_cancel₀ δ (ne_of_gt hpos)
    refine ⟨j, l, c, div_nonneg hδ0 hpos.le, (div_le_one hpos).mpr hδ, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [transfer_apply_left hjl, Equiv.swap_apply_left]
      linear_combination hcmul
    rcases eq_or_ne i l with rfl | hil
    · rw [transfer_apply_right, Equiv.swap_apply_right]
      linear_combination -hcmul
    · rw [transfer_apply_of_ne hij hil, Equiv.swap_apply_of_ne_of_ne hij hil]
      ring

theorem exists_isTTransform_of_not_forall_le {z q : Fin n → ℝ}
    (hz : Antitone z) (hz0 : ∀ i, 0 ≤ z i) (hq0 : ∀ i, 0 ≤ q i)
    (hpre : ∀ k, prefixSum k z ≤ prefixSum k q) (hnot : ¬ ∀ i, z i ≤ q i) :
    ∃ q', IsTTransform q q' ∧ (∀ i, 0 ≤ q' i) ∧
      (∀ k, prefixSum k z ≤ prefixSum k q') ∧
      (Finset.univ.filter fun i => z i ≠ q' i).card <
        (Finset.univ.filter fun i => z i ≠ q i).card := by
  classical
  push Not at hnot
  have hSne : (Finset.univ.filter fun i : Fin n => q i < z i).Nonempty :=
    hnot.imp fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  set l := (Finset.univ.filter fun i : Fin n => q i < z i).min' hSne with hldef
  have hlS : q l < z l :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hSne)).2
  have hlmin : ∀ i, i < l → z i ≤ q i := by
    intro i hil
    by_contra hzq
    push Not at hzq
    exact absurd (Finset.min'_le _ i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzq⟩)) (not_le.mpr hil)
  have hexj : ∃ j, j < l ∧ z j < q j := by
    by_contra hcon
    push Not at hcon
    have heq : ∀ i, i < l → z i = q i := fun i hi =>
      le_antisymm (hlmin i hi) (hcon i hi)
    have hp := hpre ((l : ℕ) + 1)
    have hset : (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ) + 1) =
        insert l (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hi
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq' | hlt
        · exact Or.inl (Fin.ext heq')
        · exact Or.inr hlt
      · rintro (rfl | hi) <;> omega
    have hlnot : l ∉ Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ) := by simp
    rw [prefixSum, prefixSum, hset, Finset.sum_insert hlnot,
      Finset.sum_insert hlnot] at hp
    have hsum_eq :
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < (l : ℕ)), z i =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < (l : ℕ)), q i :=
      Finset.sum_congr rfl fun i hi => heq i (Fin.lt_def.mpr (Finset.mem_filter.mp hi).2)
    rw [hsum_eq] at hp
    linarith
  obtain ⟨j, hjl, hzj⟩ := hexj
  have hjl_ne : j ≠ l := ne_of_lt hjl
  set δ : ℝ := min (q j - z j) (z l - q l) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ₁ : δ ≤ q j - z j := min_le_left _ _
  have hδ₂ : δ ≤ z l - q l := min_le_right _ _
  have hδ₃ : δ ≤ q j - q l := by linarith [hz hjl.le]
  refine ⟨transfer q j l δ, isTTransform_transfer hjl_ne hδpos.le hδ₃, ?_, ?_, ?_⟩
  · intro i
    rcases eq_or_ne i j with rfl | hij
    · rw [transfer_apply_left hjl_ne]
      linarith [hz0 i]
    rcases eq_or_ne i l with rfl | hil
    · rw [transfer_apply_right]
      linarith [hq0 l]
    · rw [transfer_apply_of_ne hij hil]
      exact hq0 i
  · intro k
    rw [prefixSum_transfer hjl_ne]
    rcases lt_or_ge (j : ℕ) k with hjk | hjk
    · rcases lt_or_ge (l : ℕ) k with hlk | hlk
      · rw [if_pos hjk, if_pos hlk]
        linarith [hpre k]
      · rw [if_pos hjk, if_neg (by omega : ¬ (l : ℕ) < k)]
        have hjmem : j ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < k :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩
        have hterm : q j - z j ≤
            ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), (q i - z i) := by
          refine Finset.single_le_sum (f := fun i => q i - z i) (fun i hi => ?_) hjmem
          have hivk : (i : ℕ) < k := (Finset.mem_filter.mp hi).2
          linarith [hlmin i (Fin.lt_def.mpr (by omega : (i : ℕ) < (l : ℕ)))]
        rw [Finset.sum_sub_distrib] at hterm
        simp only [prefixSum]
        linarith
    · rw [if_neg (by omega), if_neg (by omega : ¬ (l : ℕ) < k)]
      linarith [hpre k]
  · refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ?_)
    · intro i hi
      obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => ?_⟩
      have hij : i ≠ j := by rintro rfl; exact absurd heq hzj.ne
      have hil : i ≠ l := by rintro rfl; exact absurd heq hlS.ne'
      exact hine (by rw [transfer_apply_of_ne hij hil]; exact heq)
    · rcases min_choice (q j - z j) (z l - q l) with hmin | hmin
      · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj.ne⟩, ?_⟩
        have h : transfer q j l δ j = z j := by
          rw [transfer_apply_left hjl_ne, hδdef, hmin]
          ring
        simp [h]
      · refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlS.ne'⟩, ?_⟩
        have h : transfer q j l δ l = z l := by
          rw [transfer_apply_right, hδdef, hmin]
          ring
        simp [h]

end FiniteVector
end D5.S3.Geometry.AlphaGeometry.MajorizationTransfer
