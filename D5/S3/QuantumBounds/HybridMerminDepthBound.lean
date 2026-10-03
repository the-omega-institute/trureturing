/- GID: D5/S3/QuantumBounds/HybridMerminDepthBound
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/HybridMerminDepthBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bernards--Gühne hybrid two-cell classical bound for all k,m >= 2. -/
/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#12316; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.CHSH
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.IntervalCases
import Mathlib.InformationTheory.Hamming

namespace D5.S3.QuantumBounds.HybridMerminDepthBound

open scoped BigOperators
open Set

def phase (h : ℕ) : ℤ :=
  (-1 : ℤ) ^ (1 + (h + 1) / 2)

def hybridValue (k m : ℕ)
    (A : (Fin k → Bool) → ℤˣ) (B : (Fin m → Bool) → ℤˣ) : ℤ :=
  ∑ x : Fin k → Bool, ∑ y : Fin m → Bool,
    (((hammingDist x (fun _ => false)) + (hammingDist y (fun _ => false)) : ℕ) : ℤ) *
      phase ((hammingDist x (fun _ => false)) + (hammingDist y (fun _ => false))) *
      (A x : ℤ) * (B y : ℤ)

def claim : Prop :=
  ∀ k m : ℕ, 2 ≤ k → 2 ≤ m →
    IsGreatest
      {v : ℤ | ∃ (A : (Fin k → Bool) → ℤˣ) (B : (Fin m → Bool) → ℤˣ),
        v = hybridValue k m A B}
      (((k + m) * 2 ^ (k + m - 2) : ℕ) : ℤ)

set_option maxHeartbeats 400000 in
theorem result : claim := by
  classical
  have two_cell (r s : ℕ)
      (A : (Fin (r + 1) → Bool) → ℤˣ) (B : (Fin (s + 1) → Bool) → ℤˣ) :
      |∑ x, ∑ y, phase ((hammingDist x (fun _ => false)) + (hammingDist y (fun _ => false)) + 1) *
        (A x : ℤ) * (B y : ℤ)| ≤ (2 : ℤ) ^ (r + s + 1) := by
    classical
    have phase_four (h : ℕ) : phase h = if h % 4 = 0 ∨ h % 4 = 3 then -1 else 1 := by
      unfold phase
      rw [neg_one_pow_eq_pow_mod_two]
      have hh := Nat.mod_lt h (by decide : 0 < 4)
      interval_cases hm : h % 4
      · have he : (1 + (h + 1) / 2) % 2 = 1 := by omega
        norm_num [hm, he]
      · have he : (1 + (h + 1) / 2) % 2 = 0 := by omega
        norm_num [hm, he]
      · have he : (1 + (h + 1) / 2) % 2 = 0 := by omega
        norm_num [hm, he]
      · have he : (1 + (h + 1) / 2) % 2 = 1 := by omega
        norm_num [hm, he]
    have split (n : ℕ) (f : (Fin (n + 1) → Bool) → ℤ) :
        (∑ x, f x) = ∑ u : Fin n → Bool, (f (Fin.cons false u) + f (Fin.cons true u)) := by
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [Fintype.univ_bool, Fin.consEquiv, add_comm]
    have weight (n : ℕ) (b : Bool) (u : Fin n → Bool) :
        (hammingDist (Fin.cons b u) (fun _ => false)) = (if b then 1 else 0) + (hammingDist u (fun _ => false)) := by
      simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter, Bool.not_eq_false, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have block (h : ℕ) (a₀ a₁ b₀ b₁ : ℤˣ) :
        |phase (h+1) * (a₀ : ℤ) * (b₀ : ℤ) +
         phase (h+2) * (a₀ : ℤ) * (b₁ : ℤ) +
         phase (h+2) * (a₁ : ℤ) * (b₀ : ℤ) +
         phase (h+3) * (a₁ : ℤ) * (b₁ : ℤ)| ≤ 2 := by
      have square (u : ℤˣ) : (u : ℤ)^2 = 1 := by
        rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
      have upper (a c b d : ℤˣ) :
          (a : ℤ)*(b : ℤ) + (a : ℤ)*(d : ℤ) + (c : ℤ)*(b : ℤ) - (c : ℤ)*(d : ℤ) ≤ 2 := by
        have square_real (u : ℤˣ) : ((u : ℤ) : ℝ)^2 = 1 := by
          exact_mod_cast square u
        have ht := CHSH_inequality_of_comm
          ((a : ℤ) : ℝ) ((c : ℤ) : ℝ) ((b : ℤ) : ℝ) ((d : ℤ) : ℝ)
          { A₀_inv := square_real a
            A₁_inv := square_real c
            B₀_inv := square_real b
            B₁_inv := square_real d
            A₀_sa := by simp
            A₁_sa := by simp
            B₀_sa := by simp
            B₁_sa := by simp
            A₀B₀_commutes := mul_comm _ _
            A₀B₁_commutes := mul_comm _ _
            A₁B₀_commutes := mul_comm _ _
            A₁B₁_commutes := mul_comm _ _ }
        exact_mod_cast ht
      have bound (a c b d : ℤˣ) :
          |(a : ℤ)*(b : ℤ) + (a : ℤ)*(d : ℤ) + (c : ℤ)*(b : ℤ) - (c : ℤ)*(d : ℤ)| ≤ 2 := by
        refine abs_le.mpr ⟨?_, upper a c b d⟩
        have ht := upper (-a) (-c) b d
        simp only [Units.val_neg, neg_mul] at ht
        linarith only [ht]
      have hh := Nat.mod_lt h (by decide : 0 < 4)
      interval_cases hm : h % 4
      · simpa [phase_four, Nat.add_mod, hm, sub_eq_add_neg] using bound a₀ a₁ b₀ b₁
      · simpa [phase_four, Nat.add_mod, hm, sub_eq_add_neg, add_assoc] using bound a₀ (-a₁) b₀ (-b₁)
      · simpa [phase_four, Nat.add_mod, hm, sub_eq_add_neg, add_assoc] using bound (-a₀) (-a₁) b₀ b₁
      · simpa [phase_four, Nat.add_mod, hm, sub_eq_add_neg, add_assoc] using bound (-a₀) a₁ b₀ (-b₁)
    let term (u : Fin r → Bool) (v : Fin s → Bool) :=
      phase ((hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 1) *
        (A (Fin.cons false u) : ℤ) * (B (Fin.cons false v) : ℤ) +
      phase ((hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 2) *
        (A (Fin.cons false u) : ℤ) * (B (Fin.cons true v) : ℤ) +
      phase ((hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 2) *
        (A (Fin.cons true u) : ℤ) * (B (Fin.cons false v) : ℤ) +
      phase ((hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 3) *
        (A (Fin.cons true u) : ℤ) * (B (Fin.cons true v) : ℤ)
    have hterm (u : Fin r → Bool) (v : Fin s → Bool) : |term u v| ≤ 2 :=
      block ((hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)))
        (A (Fin.cons false u)) (A (Fin.cons true u))
        (B (Fin.cons false v)) (B (Fin.cons true v))
    have hbound : |∑ u, ∑ v, term u v| ≤ (2 : ℤ) ^ (r + s + 1) := by
      calc
        _ ≤ ∑ u, |∑ v, term u v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _u : Fin r → Bool, ∑ _v : Fin s → Bool, (2 : ℤ) := by
          apply Finset.sum_le_sum
          intro u _
          exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun v _ => hterm u v)
        _ = (2 : ℤ) ^ (r + s + 1) := by
          simp [pow_add, pow_succ, mul_comm, mul_left_comm]
    calc
      _ = |∑ u, ∑ v, term u v| := by
        congr 1
        rw [split r]
        apply Finset.sum_congr rfl
        intro u _
        rw [split s, split s, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _
        dsimp only [term]
        simp only [weight, Bool.false_eq_true, ↓reduceIte, zero_add]
        have h₁ : (hammingDist u (fun _ => false)) + (1 + (hammingDist v (fun _ => false))) + 1 =
            (hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 2 := by omega
        have h₂ : 1 + (hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 1 =
            (hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 2 := by omega
        have h₃ : 1 + (hammingDist u (fun _ => false)) + (1 + (hammingDist v (fun _ => false))) + 1 =
            (hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 3 := by omega
        rw [h₁, h₂, h₃]
        simp only [add_assoc]
      _ ≤ _ := hbound
  have coordinate_decomposition (r s : ℕ)
      (A : (Fin (r + 1) → Bool) → ℤˣ) (B : (Fin (s + 1) → Bool) → ℤˣ) :
      hybridValue (r + 1) (s + 1) A B =
        (∑ i : Fin (r + 1), ∑ u : Fin r → Bool, ∑ y : Fin (s + 1) → Bool,
          phase ((hammingDist u (fun _ => false)) + (hammingDist y (fun _ => false)) + 1) *
            (A (i.insertNth true u) : ℤ) * (B y : ℤ)) +
        (∑ j : Fin (s + 1), ∑ x : Fin (r + 1) → Bool, ∑ v : Fin s → Bool,
          phase ((hammingDist x (fun _ => false)) + (hammingDist v (fun _ => false)) + 1) *
            (A x : ℤ) * (B (j.insertNth true v) : ℤ)) := by
    classical
    have weight (n : ℕ) (i : Fin (n + 1)) (b : Bool) (u : Fin n → Bool) :
        (hammingDist (i.insertNth b u) (fun _ => false)) = (if b then 1 else 0) + (hammingDist u (fun _ => false)) := by
      simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter, Bool.not_eq_false]
      rw [Fin.sum_univ_succAbove _ i]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    have split (n : ℕ) (i : Fin (n + 1)) (f : (Fin (n + 1) → Bool) → ℤ) :
        (∑ x, f x) = ∑ u : Fin n → Bool, (f (i.insertNth false u) + f (i.insertNth true u)) := by
      rw [← (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) i).sum_comp]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [Fintype.univ_bool, Fin.insertNthEquiv, add_comm]
    let f (x : Fin (r + 1) → Bool) (y : Fin (s + 1) → Bool) :=
      phase ((hammingDist x (fun _ => false)) + (hammingDist y (fun _ => false))) * (A x : ℤ) * (B y : ℤ)
    have point (x : Fin (r + 1) → Bool) (y : Fin (s + 1) → Bool) :
        (((hammingDist x (fun _ => false)) + (hammingDist y (fun _ => false)) : ℕ) : ℤ) *
          phase ((hammingDist x (fun _ => false)) + (hammingDist y (fun _ => false))) * (A x : ℤ) * (B y : ℤ) =
        (∑ i, if x i then f x y else 0) + (∑ j, if y j then f x y else 0) := by
      simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter, Bool.not_eq_false, Nat.cast_add, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero, add_mul, Finset.sum_mul, ite_mul, one_mul, zero_mul, f]
    have first (i : Fin (r + 1)) :
        (∑ x, ∑ y, if x i then f x y else 0) =
        ∑ u : Fin r → Bool, ∑ y : Fin (s + 1) → Bool,
          phase ((hammingDist u (fun _ => false)) + (hammingDist y (fun _ => false)) + 1) *
            (A (i.insertNth true u) : ℤ) * (B y : ℤ) := by
      rw [split r i]
      simp only [f, Fin.insertNth_apply_same, Bool.false_eq_true, ↓reduceIte,
        Finset.sum_const_zero, zero_add, weight]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro y _
      congr 2
      congr 1
      omega
    have second (j : Fin (s + 1)) :
        (∑ x, ∑ y, if y j then f x y else 0) =
        ∑ x : Fin (r + 1) → Bool, ∑ v : Fin s → Bool,
          phase ((hammingDist x (fun _ => false)) + (hammingDist v (fun _ => false)) + 1) *
            (A x : ℤ) * (B (j.insertNth true v) : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [split s j]
      simp only [f, Fin.insertNth_apply_same, Bool.false_eq_true, ↓reduceIte, zero_add, weight]
      apply Finset.sum_congr rfl
      intro v _
      congr 2
      congr 1
      omega
    unfold hybridValue
    simp_rw [point, Finset.sum_add_distrib]
    congr 1
    · calc
        _ = ∑ x : Fin (r + 1) → Bool, ∑ i : Fin (r + 1), ∑ y : Fin (s + 1) → Bool,
            if x i then f x y else 0 := by
          apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_comm]
        _ = ∑ i : Fin (r + 1), ∑ x : Fin (r + 1) → Bool, ∑ y : Fin (s + 1) → Bool,
            if x i then f x y else 0 := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun i _ => first i
    · calc
        _ = ∑ x : Fin (r + 1) → Bool, ∑ j : Fin (s + 1), ∑ y : Fin (s + 1) → Bool,
            if y j then f x y else 0 := by
          apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_comm]
        _ = ∑ j : Fin (s + 1), ∑ x : Fin (r + 1) → Bool, ∑ y : Fin (s + 1) → Bool,
            if y j then f x y else 0 := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun j _ => second j
  have two_cell_attainment (r s : ℕ) :
      (∑ x : Fin (r + 1) → Bool, ∑ y : Fin (s + 1) → Bool,
        phase ((hammingDist x (fun _ => false)) + (hammingDist y (fun _ => false)) + 1) *
          phase ((hammingDist x (fun _ => false)) + 2) * phase ((hammingDist y (fun _ => false)) + 1)) =
        (2 : ℤ) ^ (r + s + 1) := by
    classical
    have phase_four (h : ℕ) : phase h = if h % 4 = 0 ∨ h % 4 = 3 then -1 else 1 := by
      unfold phase
      rw [neg_one_pow_eq_pow_mod_two]
      have hh := Nat.mod_lt h (by decide : 0 < 4)
      interval_cases hm : h % 4
      · have he : (1 + (h + 1) / 2) % 2 = 1 := by omega
        norm_num [hm, he]
      · have he : (1 + (h + 1) / 2) % 2 = 0 := by omega
        norm_num [hm, he]
      · have he : (1 + (h + 1) / 2) % 2 = 0 := by omega
        norm_num [hm, he]
      · have he : (1 + (h + 1) / 2) % 2 = 1 := by omega
        norm_num [hm, he]
    have split (n : ℕ) (f : (Fin (n + 1) → Bool) → ℤ) :
        (∑ x, f x) = ∑ u : Fin n → Bool, (f (Fin.cons false u) + f (Fin.cons true u)) := by
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [Fintype.univ_bool, Fin.consEquiv, add_comm]
    have weight (n : ℕ) (b : Bool) (u : Fin n → Bool) :
        (hammingDist (Fin.cons b u) (fun _ => false)) = (if b then 1 else 0) + (hammingDist u (fun _ => false)) := by
      simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter, Bool.not_eq_false, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have block (p q : ℕ) :
        phase (p+q+1) * phase (p+2) * phase (q+1) +
        phase (p+q+2) * phase (p+2) * phase (q+2) +
        phase (p+q+2) * phase (p+3) * phase (q+1) +
        phase (p+q+3) * phase (p+3) * phase (q+2) = 2 := by
      have hp := Nat.mod_lt p (by decide : 0 < 4)
      have hq := Nat.mod_lt q (by decide : 0 < 4)
      interval_cases hp' : p % 4 <;> interval_cases hq' : q % 4 <;>
        norm_num [phase_four, Nat.add_mod, hp', hq']
    calc
      _ = ∑ _u : Fin r → Bool, ∑ _v : Fin s → Bool, (2 : ℤ) := by
        rw [split r]
        apply Finset.sum_congr rfl
        intro u _
        rw [split s, split s, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _
        simp only [weight, Bool.false_eq_true, ↓reduceIte, zero_add]
        have h₁ : (hammingDist u (fun _ => false)) + (1 + (hammingDist v (fun _ => false))) + 1 =
            (hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 2 := by omega
        have h₂ : 1 + (hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 1 =
            (hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 2 := by omega
        have h₃ : 1 + (hammingDist u (fun _ => false)) + (1 + (hammingDist v (fun _ => false))) + 1 =
            (hammingDist u (fun _ => false)) + (hammingDist v (fun _ => false)) + 3 := by omega
        have h₄ : 1 + (hammingDist u (fun _ => false)) + 2 = (hammingDist u (fun _ => false)) + 3 := by omega
        have h₅ : 1 + (hammingDist v (fun _ => false)) + 1 = (hammingDist v (fun _ => false)) + 2 := by omega
        rw [h₁, h₂, h₃, h₄, h₅]
        simpa only [add_assoc] using block ((hammingDist u (fun _ => false))) ((hammingDist v (fun _ => false)))
      _ = _ := by
        simp [pow_add, pow_succ, mul_comm, mul_left_comm]

  intro k m hk hm
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 2 := ⟨k - 2, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  let C : ℤ := (2 : ℤ) ^ (r + s + 2)
  have upper (A : (Fin (r + 2) → Bool) → ℤˣ)
      (B : (Fin (s + 2) → Bool) → ℤˣ) :
      hybridValue (r + 2) (s + 2) A B ≤
        (((r + 2 + (s + 2)) * 2 ^ (r + 2 + (s + 2) - 2) : ℕ) : ℤ) := by
    have first (i : Fin (r + 2)) :
        (∑ u : Fin (r + 1) → Bool, ∑ y : Fin (s + 2) → Bool,
          phase ((hammingDist u (fun _ => false)) + (hammingDist y (fun _ => false)) + 1) *
            (A (i.insertNth true u) : ℤ) * (B y : ℤ)) ≤ C := by
      exact le_trans (le_abs_self _) (two_cell r (s + 1) (fun u => A (i.insertNth true u)) B)
    have second (j : Fin (s + 2)) :
        (∑ x : Fin (r + 2) → Bool, ∑ v : Fin (s + 1) → Bool,
          phase ((hammingDist x (fun _ => false)) + (hammingDist v (fun _ => false)) + 1) *
            (A x : ℤ) * (B (j.insertNth true v) : ℤ)) ≤ C := by
      apply le_trans (le_abs_self _)
      simpa only [C, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        two_cell (r + 1) s A (fun v => B (j.insertNth true v))
    rw [coordinate_decomposition (r + 1) (s + 1)]
    calc
      _ ≤ (∑ _i : Fin (r + 2), C) + (∑ _j : Fin (s + 2), C) :=
        add_le_add (Finset.sum_le_sum fun i _ => first i) (Finset.sum_le_sum fun j _ => second j)
      _ = _ := by
        have he : r + 2 + (s + 2) - 2 = r + s + 2 := by omega
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, he, C, Nat.cast_add]
        ring
  let A : (Fin (r + 2) → Bool) → ℤˣ := fun x =>
    (-1) ^ ((hammingDist x (fun _ => false)) / 2)
  let B : (Fin (s + 2) → Bool) → ℤˣ := fun y =>
    (-1) ^ ((hammingDist y (fun _ => false)) / 2)
  have valA (x) : (A x : ℤ) = phase ((hammingDist x (fun _ => false)) + 1) := by
    have he : 1 + (((hammingDist x (fun _ => false)) + 1) + 1) / 2 =
        (hammingDist x (fun _ => false)) / 2 + 2 := by omega
    simp only [A, phase, he, pow_add]
    simp
  have valB (y) : (B y : ℤ) = phase ((hammingDist y (fun _ => false)) + 1) := by
    have he : 1 + (((hammingDist y (fun _ => false)) + 1) + 1) / 2 =
        (hammingDist y (fun _ => false)) / 2 + 2 := by omega
    simp only [B, phase, he, pow_add]
    simp
  have weight (n : ℕ) (i : Fin (n + 1)) (u : Fin n → Bool) :
      (hammingDist (i.insertNth true u) (fun _ => false)) = 1 + (hammingDist u (fun _ => false)) := by
    simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter, Bool.not_eq_false]
    rw [Fin.sum_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, ↓reduceIte]
  have first (i : Fin (r + 2)) :
      (∑ u : Fin (r + 1) → Bool, ∑ y : Fin (s + 2) → Bool,
        phase ((hammingDist u (fun _ => false)) + (hammingDist y (fun _ => false)) + 1) *
          (A (i.insertNth true u) : ℤ) * (B y : ℤ)) = C := by
    simp_rw [valA, valB, weight]
    have he (p : ℕ) : 1 + p + 1 = p + 2 := by omega
    simp only [he]
    exact two_cell_attainment r (s + 1)
  have second (j : Fin (s + 2)) :
      (∑ x : Fin (r + 2) → Bool, ∑ v : Fin (s + 1) → Bool,
        phase ((hammingDist x (fun _ => false)) + (hammingDist v (fun _ => false)) + 1) *
          (A x : ℤ) * (B (j.insertNth true v) : ℤ)) = C := by
    simp_rw [valA, valB, weight]
    have he (p : ℕ) : 1 + p + 1 = p + 2 := by omega
    simp only [he]
    rw [Finset.sum_comm]
    have ht := two_cell_attainment s (r + 1)
    simpa only [C, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using ht
  have attained : hybridValue (r + 2) (s + 2) A B =
      (((r + 2 + (s + 2)) * 2 ^ (r + 2 + (s + 2) - 2) : ℕ) : ℤ) := by
    rw [coordinate_decomposition (r + 1) (s + 1)]
    simp_rw [first, second]
    have he : r + 2 + (s + 2) - 2 = r + s + 2 := by omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, he, C, Nat.cast_add]
    ring
  refine ⟨⟨A, B, attained.symm⟩, ?_⟩
  rintro v ⟨a, b, rfl⟩
  exact upper a b

#print axioms result

end D5.S3.QuantumBounds.HybridMerminDepthBound
