/- GID: D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: For n >= 1, every cyclic matching has at most (n - 1)^2 / 4 blocking pairs. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#12486; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.CyclicStableMarriageBlockingBound

/-- The man's rank in the cyclic profile (1); lower ranks are preferred. -/
def rM {n : ℕ} (g h : Fin n) : ℤ := ((h.val : ℤ) - g.val) % (n : ℤ) + 1

/-- The woman's rank in the cyclic profile (1); lower ranks are preferred. -/
def rW {n : ℕ} (h g : Fin n) : ℤ := (n : ℤ) - ((h.val : ℤ) - g.val) % (n : ℤ)

/-- Both agents strictly prefer this pair to their current partners. -/
def blocks {n : ℕ} (μ : Equiv.Perm (Fin n)) (g h : Fin n) : Prop :=
  rM g h < rM g (μ g) ∧ rW h g < rW h (μ.symm h)

/-- The number of ordered man-woman blocking pairs of a complete matching. -/
noncomputable def B {n : ℕ} (μ : Equiv.Perm (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun gh : Fin n × Fin n => blocks μ gh.1 gh.2)).card

/-- The arc-lemma upper bound, with natural-number division encoding the floor. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ μ : Equiv.Perm (Fin n), B μ ≤ (n - 1)^2 / 4

/-- Ishida's general cyclic-profile upper bound. -/
theorem result : claim := by
  classical
  intro n hn μ
  let bit (P : Prop) : ℕ := if P then 1 else 0
  let offset (g h : Fin n) : ℤ := ((h.val : ℤ) - g.val) % (n : ℤ)
  let Up (μ : Equiv.Perm (Fin n)) (i : Fin n) : Prop := i ≤ μ i

  let Down (μ : Equiv.Perm (Fin n)) (i : Fin n) : Prop := μ i < i

  have offset_cases (g h : Fin n) :
      offset g h = if g ≤ h then (h.val : ℤ) - g.val else (n : ℤ) + h.val - g.val := by
    have hg := g.isLt
    have hh := h.isLt
    unfold offset
    split_ifs with hle
    · apply Int.emod_eq_of_lt <;> omega
    · have hm : ((n : ℤ) + ((h.val : ℤ) - g.val)) % (n : ℤ) =
          (n : ℤ) + ((h.val : ℤ) - g.val) := by
        apply Int.emod_eq_of_lt <;> omega
      simp only [Int.add_emod, Int.emod_self, zero_add, Int.emod_emod] at hm
      omega

  have displacement (μ : Equiv.Perm (Fin n)) (g h : Fin n) :
      blocks μ g h ↔ offset (μ.symm h) h < offset g h ∧ offset g h < offset g (μ g) := by
    have hg := g.isLt
    have hh := h.isLt
    have hm := (μ g).isLt
    have hi := (μ.symm h).isLt
    change (offset g h + 1 < offset g (μ g) + 1 ∧
      (n : ℤ) - offset g h < (n : ℤ) - offset (μ.symm h) h) ↔ _
    omega

  have block_cases (μ : Equiv.Perm (Fin n)) (i j : Fin n) :
      blocks μ i (μ j) ↔
        (Up μ i ∧ Up μ j ∧ i < j ∧ μ j < μ i) ∨
        (Down μ i ∧ Down μ j ∧ i < j ∧ μ j < μ i) ∨
        (Down μ i ∧ Up μ j ∧ (i < j ∨ μ j < μ i)) := by
    rw [displacement, μ.symm_apply_apply]
    simp only [offset_cases, Up, Down]
    have hi := i.isLt
    have hj := j.isLt
    have hpi := (μ i).isLt
    have hpj := (μ j).isLt
    have hinj : i.val = j.val ↔ (μ i).val = (μ j).val := by
      constructor
      · intro h; have : i = j := Fin.ext h; simp [this]
      · intro h; exact congrArg Fin.val (μ.injective (Fin.ext h))
    split_ifs <;> omega

  have B_sum (μ : Equiv.Perm (Fin n)) :
      B μ = ∑ i : Fin n, ∑ j : Fin n, bit (blocks μ i (μ j)) := by
    classical
    unfold B
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [bit] using (Equiv.sum_comp μ (fun h => bit (blocks μ i h))).symm

  have block_bits (μ : Equiv.Perm (Fin n)) (i j : Fin n) :
      bit (blocks μ i (μ j)) =
        bit (Up μ i ∧ Up μ j ∧ i < j ∧ μ j < μ i) +
        bit (Down μ i ∧ Down μ j ∧ i < j ∧ μ j < μ i) +
        bit (Down μ i ∧ Up μ j ∧ (i < j ∨ μ j < μ i)) := by
    classical
    rw [block_cases]
    have hdi : Down μ i ↔ ¬ Up μ i := by unfold Down Up; omega
    have hdj : Down μ j ↔ ¬ Up μ j := by unfold Down Up; omega
    by_cases hi : Up μ i <;> by_cases hj : Up μ j <;>
      simp [bit, hdi, hdj, hi, hj]

  have cut_balance (μ : Equiv.Perm (Fin n)) (t : ℕ) :
      (∑ i : Fin n, bit (i.val < t ∧ t ≤ (μ i).val)) =
      (∑ i : Fin n, bit ((μ i).val < t ∧ t ≤ i.val)) := by
    classical
    have hpoint : ∀ i : Fin n,
        bit (i.val < t) + bit ((μ i).val < t ∧ t ≤ i.val) =
        bit ((μ i).val < t) + bit (i.val < t ∧ t ≤ (μ i).val) := by
      intro i
      unfold bit
      split_ifs <;> omega
    have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
      (fun i _ => hpoint i)
    simp only [Finset.sum_add_distrib] at hs
    have he := Equiv.sum_comp μ (fun i : Fin n => bit (i.val < t))
    omega

  let k (μ : Equiv.Perm (Fin n)) := ∑ i : Fin n, bit (Up μ i)
  let q (μ : Equiv.Perm (Fin n)) := ∑ i : Fin n, bit (Down μ i)

  let AU (μ : Equiv.Perm (Fin n)) :=
    ∑ i : Fin n, ∑ j : Fin n, bit (Up μ i ∧ Up μ j ∧ i < j ∧ μ j < μ i)
  let AW (μ : Equiv.Perm (Fin n)) :=
    ∑ i : Fin n, ∑ j : Fin n, bit (Down μ i ∧ Down μ j ∧ i < j ∧ μ j < μ i)
  let AX (μ : Equiv.Perm (Fin n)) :=
    ∑ w : Fin n, ∑ u : Fin n, bit (Down μ w ∧ Up μ u ∧ (w < u ∨ μ u < μ w))
  let D (μ : Equiv.Perm (Fin n)) :=
    ∑ w : Fin n, ∑ u : Fin n, bit (Down μ w ∧ Up μ u ∧ μ w ≤ μ u ∧ μ u < w)
  let H (μ : Equiv.Perm (Fin n)) :=
    ∑ w : Fin n, ∑ u : Fin n, bit (Down μ w ∧ Up μ u ∧ u < w ∧ w ≤ μ u)

  have B_alignments (μ : Equiv.Perm (Fin n)) :
      B μ = AU μ + AW μ + AX μ := by
    rw [B_sum]
    simp only [AU, AW, AX, block_bits, Finset.sum_add_distrib]

  have upper_nestings (μ : Equiv.Perm (Fin n)) : AU μ ≤ D μ := by
    classical
    unfold AU D
    rw [Finset.sum_comm, Finset.sum_comm (f := fun w u =>
      bit (Down μ w ∧ Up μ u ∧ μ w ≤ μ u ∧ μ u < w))]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : Up μ j
    · calc
        (∑ i : Fin n, bit (Up μ i ∧ Up μ j ∧ i < j ∧ μ j < μ i)) ≤
            ∑ i : Fin n, bit (i.val < (μ j).val + 1 ∧ (μ j).val + 1 ≤ (μ i).val) := by
          apply Finset.sum_le_sum
          intro i _
          unfold bit Up at *
          split_ifs <;> omega
        _ = ∑ w : Fin n, bit ((μ w).val < (μ j).val + 1 ∧ (μ j).val + 1 ≤ w.val) :=
          cut_balance μ ((μ j).val + 1)
        _ = ∑ w : Fin n, bit (Down μ w ∧ Up μ j ∧ μ w ≤ μ j ∧ μ j < w) := by
          apply Finset.sum_congr rfl
          intro w _
          unfold bit Up Down at *
          split_ifs <;> omega
    · simp [hj, bit]

  have lower_nestings (μ : Equiv.Perm (Fin n)) : AW μ + q μ ≤ H μ := by
    classical
    unfold AW q H
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : Down μ w
    · calc
        (∑ j : Fin n, bit (Down μ w ∧ Down μ j ∧ w < j ∧ μ j < μ w)) + bit (Down μ w) =
            ∑ j : Fin n, (bit (Down μ w ∧ Down μ j ∧ w < j ∧ μ j < μ w) + bit (j = w)) := by
          have hsum : (∑ j : Fin n, bit (j = w)) = 1 := by
            rw [Finset.sum_eq_single w]
            · simp [bit]
            · intro j _ hj
              simp [bit, hj]
            · simp
          simp only [Finset.sum_add_distrib, hsum]
          simp [hw, bit]
        _ ≤ ∑ j : Fin n, bit ((μ j).val < w.val ∧ w.val ≤ j.val) := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hjw : j = w
          · subst j
            simp only [bit, hw, lt_self_iff_false,
              and_false, if_false, if_true]
            have hcut : (μ w).val < w.val ∧ w.val ≤ w.val := by
              unfold Down at hw
              exact ⟨hw, le_rfl⟩
            simp [hcut]
          · unfold bit Down at *
            simp only [hjw, if_false, add_zero]
            split_ifs <;> omega
        _ = ∑ u : Fin n, bit (u.val < w.val ∧ w.val ≤ (μ u).val) := (cut_balance μ w.val).symm
        _ = ∑ u : Fin n, bit (Down μ w ∧ Up μ u ∧ u < w ∧ w ≤ μ u) := by
          apply Finset.sum_congr rfl
          intro u _
          unfold bit Down Up at *
          split_ifs <;> omega
    · simp [hw, bit]

  have mixed_partition (μ : Equiv.Perm (Fin n)) :
      D μ + H μ + AX μ = q μ * k μ := by
    classical
    unfold D H AX q k
    rw [Finset.sum_mul_sum]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro u _
    have he : w.val = u.val ↔ (μ w).val = (μ u).val := by
      constructor
      · intro he
        have hw : w = u := Fin.ext he
        simp [hw]
      · intro he
        exact congrArg Fin.val (μ.injective (Fin.ext he))
    unfold bit Up Down
    split_ifs <;> omega

  have blocking_product_bound (μ : Equiv.Perm (Fin n)) :
      B μ + q μ ≤ q μ * k μ := by
    have hU := upper_nestings μ
    have hW := lower_nestings μ
    have hP := mixed_partition μ
    rw [B_alignments]
    omega

  have up_down_card (μ : Equiv.Perm (Fin n)) : k μ + q μ = n := by
    classical
    unfold k q
    rw [← Finset.sum_add_distrib]
    calc
      (∑ i : Fin n, (bit (Up μ i) + bit (Down μ i))) = ∑ _i : Fin n, 1 := by
        apply Finset.sum_congr rfl
        intro i _
        unfold bit Up Down
        split_ifs <;> omega
      _ = n := by simp

  have natural_square_bound (b q k n : ℕ) (hn : 1 ≤ n)
      (hcard : k + q = n) (hb : b + q ≤ q * k) : b ≤ (n - 1)^2 / 4 := by
    have hcardZ : (k : ℤ) + q = n := by exact_mod_cast hcard
    have hbZ : (b : ℤ) + q ≤ (q : ℤ) * k := by exact_mod_cast hb
    have hnmZ : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hsq : 0 ≤ ((k : ℤ) - q - 1)^2 := sq_nonneg _
    have hfourZ : (b : ℤ) * 4 ≤ ((n - 1 : ℕ) : ℤ)^2 := by
      nlinarith
    have hfour : b * 4 ≤ (n - 1)^2 := by exact_mod_cast hfourZ
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr hfour
  exact natural_square_bound (B μ) (q μ) (k μ) n hn
    (up_down_card μ) (blocking_product_bound μ)

end D5.S3.Combinatorics.Graph.CyclicStableMarriageBlockingBound
