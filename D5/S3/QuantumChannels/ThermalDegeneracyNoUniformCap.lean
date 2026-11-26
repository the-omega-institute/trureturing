/- GID: D5/S3/QuantumChannels/ThermalDegeneracyNoUniformCap
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/ThermalDegeneracyNoUniformCap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed qutrit has a thermal operation outside the closed convex hull for each finite bath multiplicity cap. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum

/-! A finite Fibonacci bath beats each multiplicity cap at inverse temperature `log 2`,
on input `diag(0, 2/3, 1/3)`. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.QuantumChannels.ThermalDegeneracyWidthRenewal

open Finset (range)

/-- The multiplicities of the capped Fibonacci bath, starting at level zero. -/
def response (M j : ℕ) : ℕ := min M (Nat.fib (j + 1))

theorem response_le_cap (M j : ℕ) : response M j ≤ M :=
  min_le_left _ _

theorem response_pos {M : ℕ} (hM : 1 ≤ M) (j : ℕ) : 0 < response M j :=
  lt_min (Nat.lt_of_succ_le hM) (Nat.fib_pos.mpr (Nat.succ_pos j))

theorem response_zero {M : ℕ} (hM : 1 ≤ M) : response M 0 = 1 := by
  simp only [response, Nat.zero_add, Nat.fib_one, min_eq_right hM]

theorem response_one {M : ℕ} (hM : 1 ≤ M) : response M 1 = 1 := by
  change min M (Nat.fib 2) = 1
  rw [Nat.fib_two, min_eq_right hM]

private theorem clip_add_le (M a b : ℕ) :
    min M (a + b) ≤ min M a + min M b := by
  by_cases ha : a ≤ M
  · by_cases hb : b ≤ M
    · rw [min_eq_right ha, min_eq_right hb]
      exact min_le_right _ _
    · rw [min_eq_left (le_of_not_ge hb)]
      exact (min_le_left _ _).trans (by omega)
  · rw [min_eq_left (le_of_not_ge ha)]
    exact (min_le_left _ _).trans (by omega)

private theorem clip_sum_le {ι : Type*} (M : ℕ) (s : Finset ι) (f : ι → ℕ) :
    min M (∑ b ∈ s, f b) ≤ ∑ b ∈ s, min M (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact (clip_add_le M _ _).trans (Nat.add_le_add_left ih _)

private theorem clip_mul_le (M d a : ℕ) : min M (d * a) ≤ d * min M a := by
  cases d with
  | zero => simp
  | succ d =>
    by_cases ha : a ≤ M
    · rw [min_eq_right ha]
      exact min_le_right _ _
    · rw [min_eq_left (le_of_not_ge ha)]
      refine (min_le_left _ _).trans ?_
      rw [Nat.succ_mul]
      omega

theorem response_add_two (M j : ℕ) :
    response M (j + 2) = min M (response M (j + 1) + response M j) := by
  have hfib : Nat.fib ((j + 2) + 1) = Nat.fib ((j + 1) + 1) + Nat.fib (j + 1) :=
    (Nat.fib_add_two (n := j + 1)).trans (Nat.add_comm _ _)
  unfold response
  rw [hfib]
  apply le_antisymm
  · exact le_min (min_le_left _ _) (clip_add_le M _ _)
  · exact min_le_min le_rfl (Nat.add_le_add (min_le_right _ _) (min_le_right _ _))

/-- The unmet multiplicity at each level. Predecessors below level zero contribute zero. -/
def deficit (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => g 0
  | 1 => g 1 - g 0
  | j + 2 => g (j + 2) - (g (j + 1) + g j)

noncomputable def convolution (M : ℕ) (d : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ b ∈ range (j + 1), d b * response M (j - b)

/-- Every level of a capped profile is dominated by the deficit convolution. -/
theorem profile_le_convolution {M L : ℕ} {g : ℕ → ℕ} (hM : 1 ≤ M)
    (hcap : ∀ j < L, g j ≤ M) (j : ℕ) (hj : j < L) :
    g j ≤ convolution M (deficit g) j := by
  revert hj
  let d := deficit g
  let C := convolution M d
  change j < L → g j ≤ C j
  induction j using Nat.twoStepInduction with
  | zero =>
    intro _
    simp [C, convolution, d, deficit, Finset.sum_range_succ, response_zero hM]
  | one =>
    intro _
    have hC : C 1 = g 0 + (g 1 - g 0) := by
      simp [C, convolution, d, deficit, Finset.sum_range_succ, response_zero hM,
        response_one hM]
    rw [hC]
    omega
  | more n hn hn1 =>
    intro hj
    have hg₀ : g n ≤ C n := hn (by omega)
    have hg₁ : g (n + 1) ≤ C (n + 1) := hn1 (by omega)
    let T := ∑ b ∈ range (n + 1), d b * (response M (n + 1 - b) + response M (n - b))
    have hprev : C (n + 1) + C n = T + d (n + 1) := by
      change (∑ b ∈ range ((n + 1) + 1), d b * response M (n + 1 - b)) +
        (∑ b ∈ range (n + 1), d b * response M (n - b)) = _
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, response_zero hM, mul_one, T, mul_add, Finset.sum_add_distrib]
      ac_rfl
    have hnext : C (n + 2) =
        (∑ b ∈ range (n + 1), d b * response M (n + 2 - b)) +
          d (n + 1) + d (n + 2) := by
      change (∑ b ∈ range (((n + 1) + 1) + 1), d b * response M (n + 2 - b)) = _
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hedge : n + 2 - (n + 1) = 1 := by omega
      simp only [Nat.sub_self, hedge, response_zero hM, response_one hM, mul_one]
    have hclip : min M T ≤ ∑ b ∈ range (n + 1), d b * response M (n + 2 - b) := by
      dsimp only [T]
      refine (clip_sum_le M _ _).trans (Finset.sum_le_sum ?_)
      intro b hb
      have hbn : b ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hs₁ : n + 1 - b = (n - b) + 1 := by omega
      have hs₂ : n + 2 - b = (n - b) + 2 := by omega
      rw [hs₁, hs₂, response_add_two M (n - b)]
      exact clip_mul_le M _ _
    calc
      g (n + 2) ≤ min M (T + d (n + 1) + d (n + 2)) := by
        apply le_min (hcap (n + 2) hj)
        calc
          g (n + 2) ≤ d (n + 2) + (g (n + 1) + g n) := le_tsub_add
          _ ≤ d (n + 2) + (C (n + 1) + C n) :=
            Nat.add_le_add_left (Nat.add_le_add hg₁ hg₀) _
          _ = _ := by
            rw [hprev]
            ac_rfl
      _ ≤ min M T + d (n + 1) + d (n + 2) := by
        simp only [add_assoc]
        exact (clip_add_le M _ _).trans (Nat.add_le_add_left (min_le_right _ _) _)
      _ ≤ C (n + 2) := by
        rw [hnext]
        exact Nat.add_le_add_right (Nat.add_le_add_right hclip _) _

noncomputable def weightedSum (x : ℝ) (L : ℕ) (g : ℕ → ℕ) : ℝ :=
  ∑ j ∈ range L, x ^ j * (g j : ℝ)

/-- The finite-width renewal bound `Z ≤ K D`. -/
theorem weightedSum_le_response_mul_deficit {M L : ℕ} {x : ℝ} {g : ℕ → ℕ}
    (hM : 1 ≤ M) (hx : 0 ≤ x) (hcap : ∀ j < L, g j ≤ M) :
    weightedSum x L g ≤ weightedSum x L (response M) * weightedSum x L (deficit g) := by
  let d := deficit g
  let a : ℕ → ℝ := fun b => x ^ b * (d b : ℝ)
  let r : ℕ → ℝ := fun k => x ^ k * (response M k : ℝ)
  calc
    weightedSum x L g ≤ ∑ j ∈ range L, x ^ j * (convolution M d j : ℝ) := by
      unfold weightedSum
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (profile_le_convolution hM hcap j (Finset.mem_range.mp hj)))
        (pow_nonneg hx j)
    _ = ∑ j ∈ range L, ∑ b ∈ range (j + 1), a b * r (j - b) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold convolution
      simp only [Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hpow : x ^ j = x ^ b * x ^ (j - b) := by
        calc
          x ^ j = x ^ (b + (j - b)) := congrArg (fun k : ℕ => x ^ k) (by omega)
          _ = x ^ b * x ^ (j - b) := pow_add _ _ _
      dsimp only [a, r]
      rw [hpow]
      ac_rfl
    _ = ∑ b ∈ range L, ∑ k ∈ range (L - b), a b * r k :=
      Finset.sum_range_diag_flip L (fun b k => a b * r k)
    _ ≤ ∑ b ∈ range L, ∑ k ∈ range L, a b * r k := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.sub_le L b))
      intro k _ _
      exact mul_nonneg (mul_nonneg (pow_nonneg hx b) (Nat.cast_nonneg _))
        (mul_nonneg (pow_nonneg hx k) (Nat.cast_nonneg _))
    _ = weightedSum x L (response M) * weightedSum x L (deficit g) := by
      change _ = (∑ k ∈ range L, r k) * (∑ b ∈ range L, a b)
      rw [mul_comm (∑ k ∈ range L, r k), Finset.sum_mul]
      simp only [Finset.mul_sum]

private theorem weightedSum_half_succ (n : ℕ) (g : ℕ → ℕ) :
    weightedSum (1 / 2) (n + 1) g =
      weightedSum (1 / 2) n g + (1 / 2 : ℝ) ^ n * (g n : ℝ) := by
  simp only [weightedSum, Finset.sum_range_succ]

/-- The exact remainder after summing the first `n` weighted Fibonacci multiplicities. -/
theorem four_sub_weightedSum_half_fib (n : ℕ) :
    4 - weightedSum (1 / 2) n (fun j => Nat.fib (j + 1)) =
      4 * (1 / 2 : ℝ) ^ n * (Nat.fib (n + 1) : ℝ) +
        2 * (1 / 2 : ℝ) ^ n * (Nat.fib n : ℝ) := by
  induction n with
  | zero => norm_num [weightedSum, Nat.fib_zero, Nat.fib_one]
  | succ n ih =>
    change 4 - weightedSum (1 / 2) (n + 1) (fun j => Nat.fib (j + 1)) =
      4 * (1 / 2 : ℝ) ^ (n + 1) * (Nat.fib (n + 2) : ℝ) +
        2 * (1 / 2 : ℝ) ^ (n + 1) * (Nat.fib (n + 1) : ℝ)
    rw [weightedSum_half_succ, pow_succ (1 / 2 : ℝ) n,
      Nat.fib_add_two (n := n), Nat.cast_add]
    calc
      _ = (4 - weightedSum (1 / 2) n (fun j => Nat.fib (j + 1))) -
          (1 / 2 : ℝ) ^ n * (Nat.fib (n + 1) : ℝ) := by ring
      _ = _ := by rw [ih]; ring

/-- The Fibonacci prefix plus the geometric cap bound works for every finite length. -/
theorem weightedSum_half_response_le_fib_add_tail (M n L : ℕ) :
    weightedSum (1 / 2) L (response M) ≤
      weightedSum (1 / 2) n (fun j => Nat.fib (j + 1)) +
        2 * (1 / 2 : ℝ) ^ n * (M : ℝ) := by
  have half_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have tail_nonneg (j : ℕ) : 0 ≤ 2 * (1 / 2 : ℝ) ^ j * (M : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg half_nonneg j)) (Nat.cast_nonneg M)
  have prefix_le : weightedSum (1 / 2) n (response M) ≤
      weightedSum (1 / 2) n (fun j => Nat.fib (j + 1)) := by
    unfold weightedSum
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (min_le_right M _))
      (pow_nonneg half_nonneg j)
  rcases le_total L n with hLn | hnL
  · have hprefix : weightedSum (1 / 2) L (response M) ≤
        weightedSum (1 / 2) n (response M) := by
      unfold weightedSum
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hLn)
      intro j _ _
      exact mul_nonneg (pow_nonneg half_nonneg j) (Nat.cast_nonneg _)
    exact (hprefix.trans prefix_le).trans (le_add_of_nonneg_right (tail_nonneg n))
  · obtain ⟨k, rfl : L = n + k⟩ := Nat.exists_eq_add_of_le hnL
    have telescope (k : ℕ) :
        weightedSum (1 / 2) (n + k) (response M) + 2 * (1 / 2 : ℝ) ^ (n + k) * (M : ℝ) ≤
          weightedSum (1 / 2) n (response M) + 2 * (1 / 2 : ℝ) ^ n * (M : ℝ) := by
      induction k with
      | zero => simp only [Nat.add_zero, le_refl]
      | succ k ih =>
        change weightedSum (1 / 2) (n + k + 1) (response M) +
          2 * (1 / 2 : ℝ) ^ (n + k + 1) * (M : ℝ) ≤ _
        have term_le : (1 / 2 : ℝ) ^ (n + k) * (response M (n + k) : ℝ) ≤
            (1 / 2 : ℝ) ^ (n + k) * (M : ℝ) :=
          mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (response_le_cap M (n + k)))
            (pow_nonneg half_nonneg (n + k))
        rw [weightedSum_half_succ, pow_succ (1 / 2 : ℝ) (n + k)]
        calc
          _ ≤ weightedSum (1 / 2) (n + k) (response M) + (1 / 2 : ℝ) ^ (n + k) * (M : ℝ) +
                2 * ((1 / 2 : ℝ) ^ (n + k) * (1 / 2)) * (M : ℝ) := by
            linarith only [term_le]
          _ = weightedSum (1 / 2) (n + k) (response M) +
                2 * (1 / 2 : ℝ) ^ (n + k) * (M : ℝ) := by ring
          _ ≤ _ := ih
    calc
      _ ≤ weightedSum (1 / 2) (n + k) (response M) +
            2 * (1 / 2 : ℝ) ^ (n + k) * (M : ℝ) :=
        le_add_of_nonneg_right (tail_nonneg (n + k))
      _ ≤ weightedSum (1 / 2) n (response M) + 2 * (1 / 2 : ℝ) ^ n * (M : ℝ) :=
        telescope k
      _ ≤ _ := by linarith only [prefix_le]

private theorem fib_add_two_le_three_mul {n : ℕ} (hn : 1 ≤ n) :
    Nat.fib (n + 2) ≤ 3 * Nat.fib n := by
  have hprev : Nat.fib (n - 1) ≤ Nat.fib n := Nat.fib_mono (Nat.sub_le n 1)
  have hnext := Nat.fib_add_one (n := n) (by omega)
  rw [Nat.fib_add_two (n := n), hnext]
  omega

/-- Two more Fibonacci levels reduce the remainder by a factor of at most three quarters. -/
theorem four_sub_weightedSum_half_fib_add_two_le {n : ℕ} (hn : 1 ≤ n) :
    4 - weightedSum (1 / 2) (n + 2) (fun j => Nat.fib (j + 1)) ≤
      (3 / 4 : ℝ) * (4 - weightedSum (1 / 2) n (fun j => Nat.fib (j + 1))) := by
  have fib₂ : (Nat.fib (n + 2) : ℝ) ≤ 3 * (Nat.fib n : ℝ) := by
    exact_mod_cast (fib_add_two_le_three_mul hn)
  have fib₃ : (Nat.fib (n + 2 + 1) : ℝ) ≤ 3 * (Nat.fib (n + 1) : ℝ) := by
    have h : Nat.fib (n + 2 + 1) ≤ 3 * Nat.fib (n + 1) :=
      fib_add_two_le_three_mul (n := n + 1) (by omega)
    exact_mod_cast h
  rw [four_sub_weightedSum_half_fib (n + 2), four_sub_weightedSum_half_fib n,
    pow_add (1 / 2 : ℝ) n 2]
  calc
    _ = (1 / 2 : ℝ) ^ n *
          ((Nat.fib (n + 2 + 1) : ℝ) + (1 / 2) * (Nat.fib (n + 2) : ℝ)) := by ring
    _ ≤ (1 / 2 : ℝ) ^ n * (3 * (Nat.fib (n + 1) : ℝ) + (3 / 2) * (Nat.fib n : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [fib₂, fib₃]) (pow_nonneg (by norm_num) n)
    _ = _ := by ring

/-- Eight more Fibonacci levels suffice to exceed the uniform bound for cap `M`. -/
theorem weightedSum_half_fib_add_tail_lt_fib_add_eight {M n : ℕ}
    (hn : 1 ≤ n) (hMn : M ≤ Nat.fib (n + 1)) :
    weightedSum (1 / 2) n (fun j => Nat.fib (j + 1)) + 2 * (1 / 2 : ℝ) ^ n * (M : ℝ) <
      weightedSum (1 / 2) (n + 8) (fun j => Nat.fib (j + 1)) := by
  let S : ℕ → ℝ := fun k => weightedSum (1 / 2) k (fun j => Nat.fib (j + 1))
  change S n + 2 * (1 / 2 : ℝ) ^ n * (M : ℝ) < S (n + 8)
  have contract₂ : 4 - S (n + 2) ≤ (3 / 4 : ℝ) * (4 - S n) :=
    four_sub_weightedSum_half_fib_add_two_le hn
  have contract₄ : 4 - S (n + 4) ≤ (3 / 4 : ℝ) * (4 - S (n + 2)) :=
    four_sub_weightedSum_half_fib_add_two_le (n := n + 2) (by omega)
  have contract₆ : 4 - S (n + 6) ≤ (3 / 4 : ℝ) * (4 - S (n + 4)) :=
    four_sub_weightedSum_half_fib_add_two_le (n := n + 4) (by omega)
  have contract₈ : 4 - S (n + 8) ≤ (3 / 4 : ℝ) * (4 - S (n + 6)) :=
    four_sub_weightedSum_half_fib_add_two_le (n := n + 6) (by omega)
  have shrink : 4 - S (n + 8) ≤ (81 / 256 : ℝ) * (4 - S n) := by
    linarith only [contract₂, contract₄, contract₆, contract₈]
  have remainder : 4 - S n =
      4 * (1 / 2 : ℝ) ^ n * (Nat.fib (n + 1) : ℝ) +
        2 * (1 / 2 : ℝ) ^ n * (Nat.fib n : ℝ) := four_sub_weightedSum_half_fib n
  have power_pos : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have cap_le : (M : ℝ) ≤ (Nat.fib (n + 1) : ℝ) := Nat.cast_le.mpr hMn
  have fib_le : (Nat.fib n : ℝ) ≤ (Nat.fib (n + 1) : ℝ) :=
    Nat.cast_le.mpr Nat.fib_le_fib_succ
  have fib_pos : 0 < (Nat.fib (n + 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.fib_pos.mpr (Nat.succ_pos n))
  have weighted_cap_le := mul_le_mul_of_nonneg_left cap_le power_pos.le
  have weighted_fib_le := mul_le_mul_of_nonneg_left fib_le power_pos.le
  have weighted_fib_pos := mul_pos power_pos fib_pos
  have weighted_fib_nonneg : 0 ≤ (1 / 2 : ℝ) ^ n * (Nat.fib n : ℝ) :=
    mul_nonneg power_pos.le (Nat.cast_nonneg _)
  have shrink_lt : 4 - S (n + 8) < 2 * (1 / 2 : ℝ) ^ n * (Nat.fib (n + 1) : ℝ) := by
    linarith only [shrink, remainder, weighted_fib_le, weighted_fib_pos]
  linarith only [shrink_lt, remainder, weighted_cap_le, weighted_fib_nonneg]

/-- Cap `Nat.fib L` contains the full Fibonacci profile through length `L`. -/
theorem weightedSum_response_fib_eq (x : ℝ) (L : ℕ) :
    weightedSum x L (response (Nat.fib L)) =
      weightedSum x L (fun j => Nat.fib (j + 1)) := by
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro j hj
  have h : Nat.fib (j + 1) ≤ Nat.fib L :=
    Nat.fib_mono (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
  rw [response, min_eq_right h]

end D5.S3.QuantumChannels.ThermalDegeneracyWidthRenewal

namespace D5.S3.QuantumChannels.ThermalDegeneracyWidthSpectra

open ThermalDegeneracyShellBound (boltzmann)
open ThermalDegeneracyCertificate (deficit)

private def predecessor (g : ℕ → ℕ) (j k : ℕ) : ℕ :=
  if k ≤ j then g (j - k) else 0

private theorem chain_deficit (g : ℕ → ℕ) (j : ℕ) :
    g j - (predecessor g j 1 + predecessor g j 2) =
      ThermalDegeneracyWidthRenewal.deficit g j := by
  rcases j with _ | j
  · simp [predecessor, ThermalDegeneracyWidthRenewal.deficit]
  rcases j with _ | j
  · simp [predecessor, ThermalDegeneracyWidthRenewal.deficit]
  have h1 : 1 ≤ j + 2 := by omega
  have h2 : 2 ≤ j + 2 := by omega
  have h3 : j + 2 - 1 = j + 1 := by omega
  have h4 : j + 2 - 2 = j := by omega
  simp [predecessor, h1, h2, h3, h4, ThermalDegeneracyWidthRenewal.deficit]

private theorem weight_shift (a : ℝ) (j : ℕ) :
    boltzmann (a + j) = boltzmann a * (1 / 2 : ℝ) ^ j := by
  have h : Real.exp (-(Real.log 2)) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  unfold boltzmann
  rw [mul_add, Real.exp_add, mul_comm (-(Real.log 2)) (j : ℝ),
    Real.exp_nat_mul, h]

private theorem eq_min_add_index {a t : ℝ} (hle : a ≤ t)
    (hf : Int.fract a = Int.fract t) :
    t = a + (((⌊t⌋ - ⌊a⌋).toNat : ℕ) : ℝ) := by
  have hn : 0 ≤ ⌊t⌋ - ⌊a⌋ := sub_nonneg.mpr (Int.floor_mono hle)
  have hz : ((⌊t⌋ - ⌊a⌋).toNat : ℤ) = ⌊t⌋ - ⌊a⌋ := Int.toNat_of_nonneg hn
  have hc := congrArg (fun k : ℤ => (k : ℝ)) hz
  push_cast at hc
  simp only [Int.fract] at hf
  linarith

private theorem predecessor_eq {s : Finset ℝ} {g : ℝ → ℕ} {r a : ℝ}
    (hzero : ∀ t ∉ s, g t = 0) (ha : Int.fract a = r)
    (hmin : ∀ t ∈ s, Int.fract t = r → a ≤ t) (j k : ℕ) :
    g (a + (j : ℝ) - k) = predecessor (fun n => g (a + (n : ℝ))) j k := by
  by_cases hjk : k ≤ j
  · rw [predecessor, if_pos hjk]
    congr 1
    rw [Nat.cast_sub hjk]
    ring
  · rw [predecessor, if_neg hjk]
    apply hzero
    intro ht
    have hf : Int.fract (a + (j : ℝ) - k) = r := by
      rw [show (k : ℝ) = ((k : ℤ) : ℝ) by norm_cast,
        Int.fract_sub_intCast, Int.fract_add_natCast, ha]
    have hlt : (j : ℝ) < k := by exact_mod_cast (Nat.lt_of_not_ge hjk)
    linarith [hmin _ ht hf]

private theorem weighted_sum_on_residue {s : Finset ℝ} {r a : ℝ} {N : ℕ}
    (hs : s.filter (fun t => Int.fract t = r) ⊆
      (Finset.range N).image (fun j : ℕ => a + (j : ℝ)))
    (ha : Int.fract a = r) (f : ℝ → ℕ) (hf : ∀ t ∉ s, f t = 0) :
    (∑ t ∈ s.filter (fun t => Int.fract t = r), boltzmann t * (f t : ℝ)) =
      boltzmann a * ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j * (f (a + (j : ℝ)) : ℝ) := by
  classical
  calc
    _ = ∑ t ∈ (Finset.range N).image (fun j : ℕ => a + (j : ℝ)),
        boltzmann t * (f t : ℝ) := by
      apply Finset.sum_subset hs
      intro t ht hnot
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
      have hout : a + (j : ℝ) ∉ s := by
        intro hin
        exact hnot (Finset.mem_filter.mpr ⟨hin, by simpa using ha⟩)
      simp [hf _ hout]
    _ = ∑ j ∈ Finset.range N, boltzmann (a + (j : ℝ)) * (f (a + (j : ℝ)) : ℝ) := by
      apply Finset.sum_image
      intro j _ k _ h
      exact Nat.cast_injective (add_left_cancel h)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [weight_shift, mul_assoc]

open ThermalDegeneracyWidthRenewal (weightedSum response)

private theorem weighted_on_one_residue {s : Finset ℝ} {g : ℝ → ℕ} {M N : ℕ}
    (hzero : ∀ t ∉ s, g t = 0) (hcap : ∀ t, g t ≤ M) (hM : 1 ≤ M)
    (hwidth : ∀ a ∈ s, ∀ t ∈ s, t - a < (N : ℝ))
    {r : ℝ} (hr : r ∈ s.image Int.fract) :
    (∑ t ∈ s.filter (fun t => Int.fract t = r), boltzmann t * (g t : ℝ)) ≤
      weightedSum (1 / 2) N (response M) *
        ∑ t ∈ s.filter (fun t => Int.fract t = r), boltzmann t * (deficit g t : ℝ) := by
  classical
  let c := s.filter (fun t => Int.fract t = r)
  have hc : c.Nonempty := by
    obtain ⟨t, ht, htr⟩ := Finset.mem_image.mp hr
    exact ⟨t, Finset.mem_filter.mpr ⟨ht, htr⟩⟩
  let a := c.min' hc
  have ha : a ∈ c := Finset.min'_mem c hc
  have hfa : Int.fract a = r := (Finset.mem_filter.mp ha).2
  have hmin (t : ℝ) (ht : t ∈ s) (hf : Int.fract t = r) : a ≤ t :=
    Finset.min'_le c t (Finset.mem_filter.mpr ⟨ht, hf⟩)
  let index (t : ℝ) := (⌊t⌋ - ⌊a⌋).toNat
  have hs : c ⊆ (Finset.range N).image (fun j : ℕ => a + (j : ℝ)) := by
    intro t ht
    obtain ⟨hts, htr⟩ := Finset.mem_filter.mp ht
    have hindex : t = a + (index t : ℝ) :=
      eq_min_add_index (hmin t hts htr) (hfa.trans htr.symm)
    refine Finset.mem_image.mpr ⟨index t, Finset.mem_range.mpr ?_, hindex.symm⟩
    have htrange : (index t : ℝ) < (N : ℝ) :=
      by linarith [hwidth a (Finset.mem_filter.mp ha).1 t hts]
    exact_mod_cast htrange
  have hdz (t : ℝ) (ht : t ∉ s) : deficit g t = 0 := by
    simp [deficit, hzero t ht]
  let q (j : ℕ) := g (a + (j : ℝ))
  have hd (j : ℕ) : deficit g (a + (j : ℝ)) = ThermalDegeneracyWidthRenewal.deficit q j := by
    unfold deficit
    rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      predecessor_eq hzero hfa hmin j 1, predecessor_eq hzero hfa hmin j 2]
    exact chain_deficit q j
  rw [weighted_sum_on_residue hs hfa g hzero, weighted_sum_on_residue hs hfa (deficit g) hdz]
  simp_rw [hd]
  rw [mul_left_comm (weightedSum (1 / 2) N (response M))]
  exact mul_le_mul_of_nonneg_left
    (ThermalDegeneracyWidthRenewal.weightedSum_le_response_mul_deficit hM
      (by norm_num) (fun j _ => hcap (a + (j : ℝ)))) (Real.exp_nonneg _)

/-- A cap and a width bound control the partition mass of every finite real spectrum. -/
theorem weighted_deficit {s : Finset ℝ} {g : ℝ → ℕ} {M N : ℕ}
    (hzero : ∀ t ∉ s, g t = 0) (hcap : ∀ t, g t ≤ M) (hM : 1 ≤ M)
    (hwidth : ∀ a ∈ s, ∀ t ∈ s, t - a < (N : ℝ)) :
    (∑ t ∈ s, boltzmann t * (g t : ℝ)) ≤
      weightedSum (1 / 2) N (response M) * ∑ t ∈ s, boltzmann t * (deficit g t : ℝ) := by
  classical
  have hmaps : ∀ t ∈ s, Int.fract t ∈ s.image Int.fract :=
    fun t ht => Finset.mem_image_of_mem Int.fract ht
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun t => boltzmann t * (g t : ℝ)),
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun t => boltzmann t * (deficit g t : ℝ)),
    Finset.mul_sum]
  exact Finset.sum_le_sum fun r hr => weighted_on_one_residue hzero hcap hM hwidth hr

end D5.S3.QuantumChannels.ThermalDegeneracyWidthSpectra

namespace D5.S3.QuantumChannels.ThermalDegeneracyWidthAttainment

open scoped Kronecker Matrix

open ThermalDegeneracyWidthRenewal (response response_zero response_one response_pos
  response_add_two weightedSum)
open ThermalDegeneracyShellBound (levels populations inputState boltzmann partition
  thermalOutput)
open GibbsBathBandwidth (diagonalReal gibbsWeight)
open CoolingMapThermalOperationRefutation (IsEnergyConserving)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)

abbrev Bath (L M : ℕ) := Σ j : Fin L, Fin (response M j.val)

private abbrev Joint (L M : ℕ) := Fin 3 × Bath L M

private abbrev PositiveBath (L M : ℕ) := {b : Bath L M // b.1.val ≠ 0}

def totalLevel {L M : ℕ} (x : Fin 3 × Bath L M) : ℕ := x.1.val + x.2.1.val

private theorem response_le_predecessors {M j : ℕ} (hj : 2 ≤ j) :
    response M j ≤ response M (j - 1) + response M (j - 2) := by
  have h₂ : j - 2 + 2 = j := by omega
  have h₁ : j - 2 + 1 = j - 1 := by omega
  simpa only [h₂, h₁] using
    (response_add_two M (j - 2)).le.trans (min_le_right _ _)

private theorem two_le_of_coordinate_not_lt {L M : ℕ} (hM : 1 ≤ M)
    (b : PositiveBath L M) (h : ¬ b.val.2.val < response M (b.val.1.val - 1)) :
    2 ≤ b.val.1.val := by
  have hj := b.property
  have hi := b.val.2.isLt
  by_contra! h₂
  have hj₁ : b.val.1.val = 1 := by omega
  exact h (by simpa [hj₁, response_one hM, response_zero hM] using hi)

/-- At level `j > 0`, use the level-`j - 1` bath coordinates with qutrit label 1
first, then use the level-`j - 2` coordinates with qutrit label 2. -/
private def partner {L M : ℕ} (hM : 1 ≤ M) (b : PositiveBath L M) : Joint L M := by
  have hj := b.property
  have hL := b.val.1.isLt
  have hi := b.val.2.isLt
  by_cases h : b.val.2.val < response M (b.val.1.val - 1)
  · exact (1, ⟨⟨b.val.1.val - 1, by omega⟩, ⟨b.val.2.val, h⟩⟩)
  · have hj₂ := two_le_of_coordinate_not_lt hM b h
    have hcap := response_le_predecessors (M := M) hj₂
    refine (2, ⟨⟨b.val.1.val - 2, by omega⟩,
      ⟨b.val.2.val - response M (b.val.1.val - 1), ?_⟩⟩)
    change b.val.2.val - response M (b.val.1.val - 1) < response M (b.val.1.val - 2)
    omega

private theorem partner_excited {L M : ℕ} (hM : 1 ≤ M) (b : PositiveBath L M) :
    (partner hM b).1 ≠ 0 := by
  unfold partner
  split
  · exact (by decide : (1 : Fin 3) ≠ 0)
  · exact (by decide : (2 : Fin 3) ≠ 0)

private theorem partner_level {L M : ℕ} (hM : 1 ≤ M) (b : PositiveBath L M) :
    totalLevel (partner hM b) = b.val.1.val := by
  have hj := b.property
  unfold partner
  split
  · change 1 + (b.val.1.val - 1) = b.val.1.val
    omega
  · next h =>
      have hj₂ := two_le_of_coordinate_not_lt hM b h
      change 2 + (b.val.1.val - 2) = b.val.1.val
      omega

private def decodeCoordinate {L M : ℕ} (offset : ℕ) (x : Joint L M) : ℕ :=
  x.2.2.val + if x.1 = 1 then 0 else offset

private theorem partner_coordinate {L M : ℕ} (hM : 1 ≤ M) (b : PositiveBath L M) :
    decodeCoordinate (response M (b.val.1.val - 1)) (partner hM b) = b.val.2.val := by
  unfold partner
  split
  · change b.val.2.val + (if (1 : Fin 3) = 1 then 0 else _) = _
    simp
  · next h =>
      change b.val.2.val - response M (b.val.1.val - 1) +
        (if (2 : Fin 3) = 1 then 0 else response M (b.val.1.val - 1)) = _
      rw [ite_eq_right (by decide)]
      omega

private theorem partner_injective {L M : ℕ} (hM : 1 ≤ M) :
    Function.Injective (partner (L := L) hM) := by
  intro a b h
  have hl := congrArg totalLevel h
  rw [partner_level, partner_level] at hl
  have hc := partner_coordinate hM a
  have hoffset := congrArg (fun j : ℕ => response M (j - 1)) hl
  rw [h, hoffset, partner_coordinate] at hc
  apply Subtype.ext
  exact Sigma.ext (Fin.ext hl) ((Fin.heq_ext_iff (congrArg (response M) hl)).mpr hc.symm)

noncomputable section

open private boltzmann_nat excited_population partition_pos from
  D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation

private def swapPartners {L M : ℕ} (hM : 1 ≤ M) (x : Joint L M) : Joint L M := by
  classical
  exact if h : x.1 = 0 ∧ x.2.1.val ≠ 0 then partner hM ⟨x.2, h.2⟩
    else if h' : ∃ b : PositiveBath L M, partner hM b = x then (0, h'.choose.val)
    else x

private theorem swapPartners_ground {L M : ℕ} (hM : 1 ≤ M) (b : PositiveBath L M) :
    swapPartners hM (0, b.val) = partner hM b := by
  unfold swapPartners
  rw [dite_eq_left ⟨rfl, b.property⟩]

private theorem swapPartners_partner {L M : ℕ} (hM : 1 ≤ M) (b : PositiveBath L M) :
    swapPartners hM (partner hM b) = (0, b.val) := by
  unfold swapPartners
  rw [dite_eq_right (fun h => partner_excited hM b h.1)]
  have hb : ∃ a, partner hM a = partner hM b := ⟨b, rfl⟩
  rw [dite_eq_left hb, partner_injective hM hb.choose_spec]

private theorem swapPartners_fixed {L M : ℕ} (hM : 1 ≤ M) (x : Joint L M)
    (hg : ¬ (x.1 = 0 ∧ x.2.1.val ≠ 0)) (he : ¬ ∃ b, partner hM b = x) :
    swapPartners hM x = x := by
  simp only [swapPartners, dite_eq_right hg, dite_eq_right he]

private theorem swapPartners_involutive {L M : ℕ} (hM : 1 ≤ M) :
    Function.Involutive (swapPartners (L := L) hM) := by
  rintro ⟨s, b⟩
  by_cases hg : s = 0 ∧ b.1.val ≠ 0
  · obtain ⟨rfl, hb⟩ := hg
    rw [swapPartners_ground hM ⟨b, hb⟩, swapPartners_partner]
  · by_cases he : ∃ a, partner hM a = (s, b)
    · obtain ⟨a, ha⟩ := he
      rw [← ha, swapPartners_partner, swapPartners_ground]
    · rw [swapPartners_fixed hM (s, b) hg he, swapPartners_fixed hM (s, b) hg he]

/-- The joint basis involution given by the disjoint same-shell transpositions. -/
def jointPermutation {L M : ℕ} (hM : 1 ≤ M) : Equiv.Perm (Fin 3 × Bath L M) :=
  Function.Involutive.toPerm _ (swapPartners_involutive hM)

theorem jointPermutation_preserves_totalLevel {L M : ℕ} (hM : 1 ≤ M) (x : Fin 3 × Bath L M) :
    totalLevel (jointPermutation hM x) = totalLevel x := by
  obtain ⟨s, b⟩ := x
  change totalLevel (swapPartners hM (s, b)) = totalLevel (s, b)
  by_cases hg : s = 0 ∧ b.1.val ≠ 0
  · obtain ⟨rfl, hb⟩ := hg
    rw [swapPartners_ground hM ⟨b, hb⟩, partner_level]
    simp [totalLevel]
  · by_cases he : ∃ a, partner hM a = (s, b)
    · obtain ⟨a, ha⟩ := he
      rw [← ha, swapPartners_partner, partner_level]
      simp [totalLevel]
    · rw [swapPartners_fixed hM (s, b) hg he]


theorem jointPermutation_ground_zero {L M : ℕ} (hM : 1 ≤ M) (b : Bath L M)
    (hb : b.1.val = 0) : jointPermutation hM (0, b) = (0, b) :=
  swapPartners_fixed hM _ (fun h => h.2 hb) (by
    rintro ⟨a, ha⟩
    exact partner_excited hM a (congrArg Prod.fst ha))

theorem jointPermutation_ground_excited {L M : ℕ} (hM : 1 ≤ M) (b : Bath L M)
    (hb : b.1.val ≠ 0) : (jointPermutation hM (0, b)).1 ≠ 0 := by
  change (swapPartners hM (0, b)).1 ≠ 0
  rw [swapPartners_ground hM ⟨b, hb⟩]
  exact partner_excited hM ⟨b, hb⟩

private theorem bath_eq_of_level_zero {L M : ℕ} (hM : 1 ≤ M) {a b : Bath L M}
    (ha : a.1.val = 0) (hb : b.1.val = 0) : a = b := by
  have h := ha.trans hb.symm
  refine Sigma.ext (Fin.ext h) ((Fin.heq_ext_iff (congrArg (response M) h)).mpr ?_)
  have ha' := (congrArg (response M) ha).trans (response_zero hM)
  have hb' := (congrArg (response M) hb).trans (response_zero hM)
  have hi := a.2.isLt.trans_le ha'.le
  have hk := b.2.isLt.trans_le hb'.le
  omega

abbrev bathDim (L M : ℕ) : ℕ := Fintype.card (Bath L M)

private def bathFin (L M : ℕ) : Bath L M ≃ Fin (bathDim L M) :=
  Fintype.equivFin _

theorem bathDim_pos {L M : ℕ} (hL : 0 < L) (hM : 1 ≤ M) : 0 < bathDim L M :=
  Fintype.card_pos_iff.mpr ⟨⟨⟨0, hL⟩, ⟨0, response_pos hM 0⟩⟩⟩

def bathEnergy {L M : ℕ} (b : Fin (bathDim L M)) : ℝ :=
  ((bathFin L M).symm b).1.val

private def jointFin (L M : ℕ) :
    (Fin 3 × Bath L M) ≃ (Fin 3 × Fin (bathDim L M)) :=
  (Equiv.refl _).prodCongr (bathFin L M)

private def jointPermutationFin {L M : ℕ} (hM : 1 ≤ M) :
    Equiv.Perm (Fin 3 × Fin (bathDim L M)) :=
  ((jointFin L M).symm.trans (jointPermutation hM)).trans (jointFin L M)

private theorem jointPermutationFin_preserves_energy {L M : ℕ} (hM : 1 ≤ M)
    (x : Fin 3 × Fin (bathDim L M)) :
    levels (jointPermutationFin hM x).1 + bathEnergy (jointPermutationFin hM x).2 =
      levels x.1 + bathEnergy x.2 := by
  simpa [jointPermutationFin, jointFin, totalLevel, levels, bathEnergy, Nat.cast_add] using
    congrArg (fun n : ℕ => (n : ℝ))
      (jointPermutation_preserves_totalLevel hM ((jointFin L M).symm x))

def jointUnitary {L M : ℕ} (hM : 1 ≤ M) :
    Matrix.unitaryGroup (Fin 3 × Fin (bathDim L M)) ℂ :=
  ⟨(jointPermutationFin hM).permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff]
    change (jointPermutationFin hM).permMatrix ℂ *
      ((jointPermutationFin hM).permMatrix ℂ)ᴴ = 1
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩

theorem jointUnitary_energyConserving {L M : ℕ} (hM : 1 ≤ M) :
    IsEnergyConserving levels (bathEnergy (L := L) (M := M)) (jointUnitary (L := L) hM) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : j = jointPermutationFin hM i
  · subst j
    rw [jointPermutationFin_preserves_energy, mul_comm]
  · have hzero : (jointUnitary (L := L) hM : Matrix _ _ ℂ) i j = 0 := by
      change (jointPermutationFin hM).toPEquiv.toMatrix i j = (0 : ℂ)
      simp only [PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply, h, ite_false]
    simp only [hzero, zero_mul, mul_zero]

private theorem population_ground : populations 0 = 0 := rfl

theorem partition_bathEnergy (L M : ℕ) :
    partition (bathEnergy (L := L) (M := M)) =
      weightedSum (1 / 2) L (response M) := by
  unfold partition weightedSum
  rw [← (bathFin L M).sum_comp (fun b => boltzmann (bathEnergy b)), Fintype.sum_sigma]
  simp only [bathEnergy, Equiv.symm_apply_apply,
    boltzmann_nat, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simpa only [mul_comm] using
    (Fin.sum_univ_eq_sum_range (fun j => (1 / 2 : ℝ) ^ j * (response M j : ℝ)) L)

private theorem groundOutput_eq_sum {L M : ℕ} (hM : 1 ≤ M) :
    (thermalOutput (bathEnergy (L := L) (M := M)) (jointUnitary (L := L) hM) inputState 0 0).re =
      ∑ b : Fin (bathDim L M),
        populations (jointPermutationFin hM (0, b)).1 *
          gibbsWeight (Real.log 2) bathEnergy (jointPermutationFin hM (0, b)).2 := by
  classical
  let σ := jointPermutationFin (L := L) hM
  let d : Fin 3 × Fin (bathDim L M) → ℂ :=
    fun x => (populations x.1 : ℂ) * (gibbsWeight (Real.log 2) bathEnergy x.2 : ℂ)
  have hconj : σ.permMatrix ℂ * Matrix.diagonal d * (σ.permMatrix ℂ)ᴴ =
      Matrix.diagonal (fun x => d (σ x)) := by
    rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    apply Matrix.ext
    intro i j
    simp [Matrix.submatrix_apply, Matrix.diagonal, Equiv.Perm.inv_def]
  unfold thermalOutput inputState ThermalDegeneracyShellBound.bathState diagonalReal
  rw [Matrix.diagonal_kronecker_diagonal]
  change (partialTraceRight
    (σ.permMatrix ℂ * Matrix.diagonal d * (σ.permMatrix ℂ)ᴴ) 0 0).re = _
  rw [hconj]
  simp only [partialTraceRight, Matrix.diagonal_apply_eq, d, σ, Complex.re_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem groundOutput_term {L M : ℕ} (hM : 1 ≤ M) (b : Fin (bathDim L M)) :
    populations (jointPermutationFin hM (0, b)).1 *
      gibbsWeight (Real.log 2) bathEnergy (jointPermutationFin hM (0, b)).2 =
        if bathEnergy b = 0 then 0
        else ((4 / 3 : ℝ) / partition (bathEnergy (L := L) (M := M))) *
          boltzmann (bathEnergy b) := by
  classical
  let σ := jointPermutationFin (L := L) hM
  have h_energy : levels (σ (0, b)).1 + bathEnergy (σ (0, b)).2 = bathEnergy b := by
    simpa [levels] using jointPermutationFin_preserves_energy hM (0, b)
  have hb : bathEnergy b = 0 ↔ ((bathFin L M).symm b).1.val = 0 := Nat.cast_eq_zero
  by_cases hz : bathEnergy b = 0
  · have h : (σ (0, b)).1 = 0 := by
      simpa [σ, jointPermutationFin, jointFin] using congrArg Prod.fst
        (jointPermutation_ground_zero hM ((bathFin L M).symm b) (hb.mp hz))
    simp only [σ] at h
    rw [h, population_ground, zero_mul, ite_eq_left hz]
  · have h : (σ (0, b)).1 ≠ 0 := by
      simpa [σ, jointPermutationFin, jointFin] using
        jointPermutation_ground_excited hM ((bathFin L M).symm b) (mt hb.mpr hz)
    rw [ite_eq_right hz, excited_population h]
    change (4 / 3 : ℝ) * boltzmann (levels (σ (0, b)).1) *
      (boltzmann (bathEnergy (σ (0, b)).2) / partition bathEnergy) = _
    rw [← h_energy]
    simp only [boltzmann, mul_add, Real.exp_add]
    ring

/-- At inverse temperature `log 2`, the permutation attains the sharp population
`(4/3) * (1 - 1/K_L)` on the diagonal input with populations `(0, 2/3, 1/3)`. -/
theorem attains {L M : ℕ} (hL : 0 < L) (hM : 1 ≤ M) :
    (thermalOutput (bathEnergy (L := L) (M := M)) (jointUnitary (L := L) hM) inputState 0 0).re =
      (4 / 3 : ℝ) * (1 - 1 / weightedSum (1 / 2) L (response M)) := by
  classical
  let e := bathEnergy (L := L) (M := M)
  let b₀ : Fin (bathDim L M) := bathFin L M ⟨⟨0, hL⟩, ⟨0, response_pos hM 0⟩⟩
  have hzero : e b₀ = 0 := by simp [e, b₀, bathEnergy]
  have hpos := partition_pos (bathDim_pos hL hM) e
  have hne (b : Fin (bathDim L M)) (hb : b ≠ b₀) : e b ≠ 0 := by
    intro hz
    apply hb
    apply (bathFin L M).symm.injective
    exact bath_eq_of_level_zero hM (Nat.cast_eq_zero.mp hz) (Nat.cast_eq_zero.mp hzero)
  rw [groundOutput_eq_sum]
  simp_rw [groundOutput_term hM]
  change (∑ b, if e b = 0 then 0 else (4 / 3 : ℝ) / partition e * boltzmann (e b)) = _
  have hsum : (∑ b ∈ Finset.univ.erase b₀, boltzmann (e b)) = partition e - 1 := by
    apply eq_sub_of_add_eq
    have hweight : boltzmann (e b₀) = 1 := by simp [hzero, boltzmann]
    simpa only [partition, hweight] using
      (Finset.sum_erase_add Finset.univ (fun b => boltzmann (e b)) (Finset.mem_univ b₀))
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b₀), ite_eq_left hzero, add_zero]
  calc
    _ = ∑ b ∈ Finset.univ.erase b₀, (4 / 3 : ℝ) / partition e * boltzmann (e b) :=
      Finset.sum_congr rfl fun b hb => ite_eq_right (hne b (Finset.mem_erase.mp hb).1)
    _ = (4 / 3 : ℝ) * (1 - 1 / partition e) := by
      rw [← Finset.mul_sum, hsum]
      field_simp [hpos.ne']
    _ = _ := by rw [show partition e = _ from partition_bathEnergy L M]

end

end D5.S3.QuantumChannels.ThermalDegeneracyWidthAttainment

namespace D5.S3.QuantumChannels.ThermalDegeneracyNoUniformCap

noncomputable section

open ThermalDegeneracyWidthRenewal (weightedSum response response_zero
  weightedSum_half_response_le_fib_add_tail weightedSum_half_fib_add_tail_lt_fib_add_eight
  weightedSum_response_fib_eq)
open CoolingMapThermalOperationRefutation (IsEnergyConserving)
open ThermalOperationDegeneracyRefutation (Mat operation HasCap)
open ThermalDegeneracyShellBound (levels inputState)

private def ground (F : Mat 3 → Mat 3) : ℝ := (F inputState 0 0).re

private def population (K : ℝ) : ℝ := (4 / 3 : ℝ) * (1 - 1 / K)

private theorem population_strictMono : StrictMonoOn population (Set.Ioi (0 : ℝ)) := by
  intro K hK L _ hKL
  unfold population
  exact mul_lt_mul_of_pos_left
    (sub_lt_sub_left (one_div_lt_one_div_of_lt hK hKL) 1) (by norm_num)

private theorem mass_pos {M L : ℕ} (hM : 1 ≤ M) (hL : 0 < L) :
    0 < weightedSum (1 / 2) L (response M) := by
  unfold weightedSum
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)
  · refine ⟨0, Finset.mem_range.mpr hL, ?_⟩
    simp [response_zero hM]

section

open ThermalDegeneracyShellBound (bathEnergies boltzmann partition)
local notation "bathMultiplicity" => ThermalDegeneracyShellBound.multiplicity
open private partition_eq_sum_multiplicity partition_pos ground_population_le_shell_sum
  multiplicity_zero capacityMass from
  D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation

set_option maxHeartbeats 1000000 in
-- The weighted shell sum uses finite-sum congruence and real-to-natural cast normalization.
/-- A width bound gives the finite Fibonacci cooling estimate for real spectra. -/
private theorem ground_le_of_width {m M N : ℕ} (hm : 0 < m) (hM : 1 ≤ M) (hN : 0 < N)
    (e : Fin m → ℝ) (U : Matrix.unitaryGroup (Fin 3 × Fin m) ℂ)
    (hu : IsEnergyConserving levels e U) (hc : HasCap e M)
    (hwidth : ∀ a b : Fin m, e b - e a < (N : ℝ)) :
    (operation (Real.log 2) e U ThermalDegeneracyShellBound.inputState 0 0).re ≤
      (4 / 3 : ℝ) * (1 - 1 / weightedSum (1 / 2) N (response M)) := by
  let K := weightedSum (1 / 2) N (response M)
  let D := ∑ t ∈ bathEnergies e, boltzmann t *
    (ThermalDegeneracyCertificate.deficit (bathMultiplicity e) t : ℝ)
  have hspec : ∀ a ∈ bathEnergies e, ∀ b ∈ bathEnergies e, b - a < (N : ℝ) := by
    intro a ha b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact hwidth i j
  have hKD : partition e ≤ K * D := by
    rw [partition_eq_sum_multiplicity]
    exact ThermalDegeneracyWidthSpectra.weighted_deficit
      (fun _ ht => multiplicity_zero e ht) hc hM hspec
  have hK : 0 < K := mass_pos hM hN
  have hZ := partition_pos hm e
  have hD : 1 / K ≤ D / partition e := by
    apply (div_le_div_iff₀ hK hZ).mpr
    simpa only [one_mul, mul_comm D K] using hKD
  have hCD : capacityMass e + D = partition e := by
    change capacityMass e + (∑ t ∈ bathEnergies e, boltzmann t *
      (ThermalDegeneracyCertificate.deficit (bathMultiplicity e) t : ℝ)) = partition e
    rw [capacityMass, ← Finset.sum_add_distrib,
      partition_eq_sum_multiplicity]
    apply Finset.sum_congr rfl
    intro t _
    rw [← mul_add]
    congr 1
    have h : min (bathMultiplicity e t)
        (bathMultiplicity e (t - 1) + bathMultiplicity e (t - 2)) +
        ThermalDegeneracyCertificate.deficit (bathMultiplicity e) t = bathMultiplicity e t := by
      unfold ThermalDegeneracyCertificate.deficit
      exact (add_comm _ _).trans tsub_add_min
    exact_mod_cast h
  calc
    _ ≤ ((4 / 3 : ℝ) / partition e) * capacityMass e := by
      simpa only [operation, ThermalDegeneracyShellBound.thermalOutput,
        ThermalDegeneracyShellBound.bathState, capacityMass] using
        ground_population_le_shell_sum hm e U hu
    _ = (4 / 3 : ℝ) * (1 - D / partition e) := by
      rw [show capacityMass e = partition e - D by linarith]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_sub_left hD 1) (by norm_num)

end

/-- Finite Gibbs dilations at `log 2` with exactly energy-conserving unitaries
and bath multiplicity at most `M`. Closure uses the pointwise topology on matrix maps. -/
def cappedOperations (M : ℕ) : Set (Mat 3 → Mat 3) :=
  {F | ∃ (m : ℕ) (e : Fin m → ℝ) (U : Matrix.unitaryGroup (Fin 3 × Fin m) ℂ),
    0 < m ∧ HasCap e M ∧ IsEnergyConserving levels e U ∧ F = operation (Real.log 2) e U}

private def capMass (M : ℕ) : ℝ :=
  weightedSum (1 / 2) (M + 1) (fun j => Nat.fib (j + 1)) +
    2 * (1 / 2 : ℝ) ^ (M + 1) * (M : ℝ)

private theorem capMass_pos {M : ℕ} (hM : 1 ≤ M) : 0 < capMass M :=
  (mass_pos hM (Nat.zero_lt_succ 0)).trans_le
    (weightedSum_half_response_le_fib_add_tail M (M + 1) 1)

private theorem width_slot_bound {m : ℕ} (hm : 0 < m) (e : Fin m → ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∀ a b : Fin m, e b - e a < (N : ℝ) := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨n, hn⟩ := exists_nat_gt
    (GibbsBathBandwidth.maxValue e - GibbsBathBandwidth.minValue e)
  refine ⟨n + 1, Nat.zero_lt_succ n, fun a b => ?_⟩
  push_cast
  apply (sub_le_sub (GibbsBathBandwidth.le_maxValue e b)
      (GibbsBathBandwidth.minValue_le e a)).trans_lt
  linarith

private theorem ground_le_capMass {M : ℕ} (hM : 1 ≤ M) {F : Mat 3 → Mat 3}
    (hF : F ∈ cappedOperations M) :
    ground F ≤ population (capMass M) := by
  obtain ⟨m, e, U, hm, hc, hu, rfl⟩ := hF
  obtain ⟨N, hN, hwidth⟩ := width_slot_bound hm e
  apply (ground_le_of_width hm hM hN e U hu hc hwidth).trans
  exact population_strictMono.monotoneOn (mass_pos hM hN) (capMass_pos hM)
    (weightedSum_half_response_le_fib_add_tail M (M + 1) N)

private theorem ground_le_capMass_closedConvexHull {M : ℕ} (hM : 1 ≤ M) {F : Mat 3 → Mat 3}
    (hF : F ∈ closure (convexHull ℝ (cappedOperations M))) :
    ground F ≤ population (capMass M) := by
  have hlinear : IsLinearMap ℝ ground :=
    ⟨fun F G => Complex.add_re (F inputState 0 0) (G inputState 0 0),
      fun r F => Complex.smul_re r (F inputState 0 0)⟩
  have hc : Continuous ground :=
    Complex.continuous_re.comp
      ((continuous_apply 0).comp ((continuous_apply 0).comp (continuous_apply inputState)))
  exact closure_minimal
    (convexHull_min (fun _ h => ground_le_capMass hM h)
      (convex_halfSpace_le hlinear (population (capMass M))))
    (isClosed_le hc continuous_const) hF

/-- For each finite cap, a finite Gibbs operation of the fixed qutrit at `log 2` lies outside
the pointwise closed convex hull of the capped operations. -/
theorem no_uniform_bath_cap {M : ℕ} (hM : 1 ≤ M) :
    ∃ (m : ℕ) (e : Fin m → ℝ) (U : Matrix.unitaryGroup (Fin 3 × Fin m) ℂ),
      0 < m ∧ IsEnergyConserving levels e U ∧
        operation (Real.log 2) e U ∉ closure (convexHull ℝ (cappedOperations M)) := by
  let L := M + 1 + 8
  let K := Nat.fib L
  have hL : 0 < L := by omega
  have hK : 1 ≤ K := Nat.fib_pos.mpr hL
  let e := ThermalDegeneracyWidthAttainment.bathEnergy (L := L) (M := K)
  let U := ThermalDegeneracyWidthAttainment.jointUnitary (L := L) hK
  refine ⟨_, e, U, ThermalDegeneracyWidthAttainment.bathDim_pos hL hK,
    ThermalDegeneracyWidthAttainment.jointUnitary_energyConserving hK, ?_⟩
  intro hc
  have hupper := ground_le_capMass_closedConvexHull hM hc
  change (ThermalDegeneracyShellBound.thermalOutput e U inputState 0 0).re ≤
      population (capMass M) at hupper
  rw [ThermalDegeneracyWidthAttainment.attains hL hK] at hupper
  have hlt : capMass M < weightedSum (1 / 2) L (response K) := by
    unfold capMass K
    rw [weightedSum_response_fib_eq]
    have hfib : M ≤ Nat.fib (M + 1 + 1) := by
      have hpos : 1 ≤ Nat.fib (M + 1) := Nat.fib_pos.mpr (Nat.zero_lt_succ M)
      calc
        M ≤ Nat.fib M + 1 := Nat.le_fib_add_one M
        _ ≤ Nat.fib M + Nat.fib (M + 1) := Nat.add_le_add_left hpos _
        _ = Nat.fib (M + 1 + 1) := (Nat.fib_add_two (n := M)).symm
    exact weightedSum_half_fib_add_tail_lt_fib_add_eight (by omega) hfib
  exact (not_lt_of_ge hupper) (population_strictMono (capMass_pos hM) (mass_pos hK hL) hlt)

end
end D5.S3.QuantumChannels.ThermalDegeneracyNoUniformCap
