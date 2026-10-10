/- GID: D5/S3/Quantum/Petz/MixingIteration
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite prefix majorization reduces to positive pair transfers and permutations by a strictly decreasing discrepancy count. -/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

open Finset

namespace D5.S3.Quantum.Petz.MixingIteration

/-- Sum of the first `k` coordinates, with the cutoff expressed in natural numbers. -/
def prefixSum {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x i

/-- A two-coordinate mixing. Theorems using it require distinct coordinates. -/
def transfer {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) (t : ℝ) : Fin n → ℝ :=
  fun a => if a = i then (1 - t) * x i + t * x j
    else if a = j then t * x i + (1 - t) * x j else x a

private def move {n : ℕ} (x : Fin n → ℝ) (j k : Fin n) (d : ℝ) : Fin n → ℝ :=
  fun a => x a + (if a = k then d else 0) - (if a = j then d else 0)

private theorem prefix_move {n : ℕ} (x : Fin n → ℝ) (j k : Fin n) (d : ℝ)
    (r : ℕ) : prefixSum (move x j k d) r = prefixSum x r +
      (if k.val < r then d else 0) - (if j.val < r then d else 0) := by
  classical
  simp [prefixSum, move, sum_add_distrib, sum_sub_distrib]

private theorem sum_move {n : ℕ} (x : Fin n → ℝ) (j k : Fin n) (d : ℝ) :
    ∑ a, move x j k d a = ∑ a, x a := by
  classical
  simp [move, sum_add_distrib, sum_sub_distrib]

private theorem full_step {n : ℕ} (S : (Fin n → ℝ) → ℝ)
    (hperm : ∀ x (σ : Equiv.Perm (Fin n)), S (x ∘ σ) = S x)
    (hstep : ∀ x, (∀ a, 0 < x a) → ∀ i j, i ≠ j → x i < x j →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → S x ≤ S (transfer x i j t))
    (x : Fin n → ℝ) (hx : ∀ a, 0 < x a) (i j : Fin n) (hij : i ≠ j)
    (horder : x i < x j) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    S x ≤ S (transfer x i j t) := by
  classical
  by_cases hh : t ≤ 1 / 2
  · exact hstep x hx i j hij horder t ht hh
  have heq : transfer x i j (1 - t) = transfer x i j t ∘ Equiv.swap i j := by
    funext a
    by_cases hai : a = i
    · subst a
      simp [transfer, hij.symm]
    by_cases haj : a = j
    · subst a
      simp [transfer, hij.symm]
    simp [transfer, hai, haj, Equiv.swap_apply_of_ne_of_ne hai haj]
  have h := hstep x hx i j hij horder (1 - t) (by linarith) (by linarith)
  rw [heq, hperm] at h
  exact h

private theorem move_step {n : ℕ} (S : (Fin n → ℝ) → ℝ)
    (hperm : ∀ x (σ : Equiv.Perm (Fin n)), S (x ∘ σ) = S x)
    (hstep : ∀ x, (∀ a, 0 < x a) → ∀ i j, i ≠ j → x i < x j →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → S x ≤ S (transfer x i j t))
    (x : Fin n → ℝ) (hx : ∀ a, 0 < x a) (j k : Fin n) (hjk : j ≠ k)
    (hgap : 0 < x j - x k) (d : ℝ) (hd : 0 ≤ d) (hd1 : d ≤ x j - x k) :
    S x ≤ S (move x j k d) := by
  have heq : transfer x k j (d / (x j - x k)) = move x j k d := by
    funext a
    have hmul := div_mul_cancel₀ d hgap.ne.symm
    by_cases haj : a = j
    · subst a
      simp [transfer, move, hjk]
      nlinarith
    by_cases hak : a = k
    · subst a
      simp [transfer, move, hjk.symm]
      nlinarith
    simp [transfer, move, haj, hak]
  rw [← heq]
  exact full_step S hperm hstep x hx k j hjk.symm (by linarith) _
    (div_nonneg hd hgap.le) ((div_le_one hgap).2 hd1)

private theorem choose_coordinates {n : ℕ} (x y : Fin n → ℝ)
    (hsum : ∑ a, x a = ∑ a, y a)
    (hprefix : ∀ r, r ≤ n → prefixSum y r ≤ prefixSum x r) (hne : x ≠ y) :
    ∃ j k : Fin n, j < k ∧ y j < x j ∧ x k < y k ∧
      ∀ a : Fin n, a < k → y a ≤ x a := by
  classical
  have hex : ∃ k, x k < y k := by
    by_contra h
    push Not at h
    have hnepoint : ∃ a, y a < x a := by
      by_contra hlt
      push Not at hlt
      apply hne
      funext a
      exact le_antisymm (hlt a) (h a)
    have hlt := Finset.sum_lt_sum (fun a (_ : a ∈ univ) => h a)
      (by obtain ⟨a, ha⟩ := hnepoint; exact ⟨a, mem_univ a, ha⟩)
    linarith
  let s := univ.filter (fun k => x k < y k)
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := hex
    exact ⟨k, by simp [s, hk]⟩
  let k := s.min' hs
  have hk : x k < y k := (mem_filter.mp (min'_mem s hs)).2
  have hbefore : ∀ a : Fin n, a < k → y a ≤ x a := by
    intro a ha
    by_contra hle
    have ham : a ∈ s := by simp [s, lt_of_not_ge hle]
    have hka := min'_le s a ham
    exact (not_le_of_gt ha) hka
  have hj : ∃ j : Fin n, j < k ∧ y j < x j := by
    by_contra h
    have hall : ∀ j : Fin n, j < k → x j ≤ y j := by
      intro j hj
      by_contra hlt
      exact h ⟨j, hj, lt_of_not_ge hlt⟩
    have hlt : prefixSum x (k.val + 1) < prefixSum y (k.val + 1) := by
      apply Finset.sum_lt_sum
      · intro a ha
        have hav : a.val < k.val + 1 := (mem_filter.mp ha).2
        by_cases hak : a = k
        · simpa [hak] using hk.le
        · exact hall a (by change a.val < k.val; have := Fin.ext_iff.not.mp hak; omega)
      · exact ⟨k, by simp, hk⟩
    have := hprefix (k.val + 1) (by omega)
    linarith
  obtain ⟨j, hjk, hj⟩ := hj
  exact ⟨j, k, hjk, hj, hk, hbefore⟩

private theorem move_prefix {n : ℕ} (x y : Fin n → ℝ) (j k : Fin n)
    (hjk : j < k) (hbefore : ∀ a : Fin n, a < k → y a ≤ x a)
    (hprefix : ∀ r, r ≤ n → prefixSum y r ≤ prefixSum x r)
    (d : ℝ) (hdj : d ≤ x j - y j) :
    ∀ r, r ≤ n → prefixSum y r ≤ prefixSum (move x j k d) r := by
  classical
  intro r hr
  rw [prefix_move]
  by_cases hkr : k.val < r
  · have hjr : j.val < r := lt_trans hjk hkr
    simp only [if_pos hkr, if_pos hjr]
    linarith [hprefix r hr]
  by_cases hjr : j.val < r
  · simp only [if_neg hkr, if_pos hjr]
    have hmargin : x j - y j ≤ prefixSum x r - prefixSum y r := by
      rw [prefixSum, prefixSum, ← sum_sub_distrib]
      exact single_le_sum (fun a ha => sub_nonneg.mpr (hbefore a (by
        have hav := (mem_filter.mp ha).2
        change a.val < k.val
        omega))) (by simp [hjr])
    linarith
  · simp only [if_neg hkr, if_neg hjr, add_zero, sub_zero]
    exact hprefix r hr

/-- Prefix majorization by an antitone target is generated by positive pair mixings.
The initial vector need not remain sorted: the earliest deficit is filled from an earlier
surplus, and each step strictly decreases the number of unequal coordinates. -/
theorem pair_transfer_reduction {n : ℕ} (S : (Fin n → ℝ) → ℝ)
    (hperm : ∀ x (σ : Equiv.Perm (Fin n)), S (x ∘ σ) = S x)
    (hstep : ∀ x, (∀ a, 0 < x a) → ∀ i j, i ≠ j → x i < x j →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → S x ≤ S (transfer x i j t))
    (x y : Fin n → ℝ) (hx : ∀ a, 0 < x a) (hy : ∀ a, 0 < y a)
    (hys : Antitone y) (hsum : ∑ a, x a = ∑ a, y a)
    (hprefix : ∀ r, r ≤ n → prefixSum y r ≤ prefixSum x r) : S x ≤ S y := by
  classical
  generalize hm : (univ.filter (fun a => x a ≠ y a)).card = m
  induction m using Nat.strong_induction_on generalizing x with
  | h m ih =>
    by_cases heq : x = y
    · simp [heq]
    obtain ⟨j, k, hjk, hj, hk, hbefore⟩ := choose_coordinates x y hsum hprefix heq
    let d := min (x j - y j) (y k - x k)
    have hd : 0 < d := lt_min (sub_pos.mpr hj) (sub_pos.mpr hk)
    have hdj : d ≤ x j - y j := min_le_left _ _
    have hdk : d ≤ y k - x k := min_le_right _ _
    have hjkne : j ≠ k := ne_of_lt hjk
    have hykj : y k ≤ y j := hys hjk.le
    have hgap : 0 < x j - x k := by linarith
    have hdgap : d ≤ x j - x k := by linarith
    let z := move x j k d
    have hzj : z j = x j - d := by simp [z, move, hjkne]
    have hzk : z k = x k + d := by simp [z, move, hjkne.symm]
    have hza : ∀ a, a ≠ j → a ≠ k → z a = x a := by
      intro a haj hak
      simp [z, move, haj, hak]
    have hzpos : ∀ a, 0 < z a := by
      intro a
      by_cases haj : a = j
      · subst a; rw [hzj]; linarith [hy j]
      by_cases hak : a = k
      · subst a; rw [hzk]; linarith [hx k]
      rw [hza a haj hak]
      exact hx a
    have hfix : z j = y j ∨ z k = y k := by
      rcases le_total (x j - y j) (y k - x k) with h | h
      · left; rw [hzj]; dsimp [d]; rw [min_eq_left h]; ring
      · right; rw [hzk]; dsimp [d]; rw [min_eq_right h]; ring
    have hsub : univ.filter (fun a => z a ≠ y a) ⊆ univ.filter (fun a => x a ≠ y a) := by
      intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      by_cases haj : a = j
      · subst a; exact hj.ne.symm
      by_cases hak : a = k
      · subst a; exact hk.ne
      rwa [hza a haj hak] at ha
    have hcard : (univ.filter (fun a => z a ≠ y a)).card < m := by
      rw [← hm]
      apply card_lt_card
      apply (ssubset_iff_of_subset hsub).2
      rcases hfix with h | h
      · exact ⟨j, by simp [hj.ne.symm], by simp [h]⟩
      · exact ⟨k, by simp [hk.ne], by simp [h]⟩
    have hzy := ih _ hcard z hzpos (by rw [sum_move]; exact hsum)
      (move_prefix x y j k hjk hbefore hprefix d hdj) rfl
    exact (move_step S hperm hstep x hx j k hjkne hgap d hd.le hdgap).trans hzy

end D5.S3.Quantum.Petz.MixingIteration
