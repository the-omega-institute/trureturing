/- GID: D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Nikolov–Savov Conjecture 3.7: Q_4 is not a maximal renewal minorant. -/

/-
proof_shape: result: content
escape_witness: form (2): the all-n minorant bound in `result`, obtained from
  three initial certificates and strong induction on the renewal recurrence.
admission_basis: open-problem-resolution (#12306; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.RandomWalks.RenewalMinorantMaximalityRefutation

open Finset MvPolynomial

/-- The simplex A_k of equation (2.6), with zero-based coordinates. -/
def Ak (k : ℕ) : Set (Fin (k - 1) → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i ≤ 1}

/-- The masses p_l, with p_k the remaining mass; l is one-based. -/
noncomputable def stepMass {k : ℕ} (p : Fin (k - 1) → ℝ) (l : ℕ) : ℝ :=
  if h : 1 ≤ l ∧ l < k then p ⟨l - 1, by omega⟩
  else if l = k then 1 - ∑ i, p i else 0

/-- Equation (2.2): u_0 = 1 and u_n = sum from l = 1 to min(n,k) of p_l u_(n-l). -/
noncomputable def renewal {k : ℕ} (p : Fin (k - 1) → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∑ l : Fin (min (n + 1) k),
      stepMass p (l.val + 1) * renewal p ((n + 1) - (l.val + 1))
termination_by n => n
decreasing_by have _h := l.isLt; omega

/-- The pointwise ordering P ≺ P' on A_k, as in section 2. -/
def polynomialLE {k : ℕ} (P P' : MvPolynomial (Fin (k - 1)) ℝ) : Prop :=
  ∀ p ∈ Ak k, eval p P ≤ eval p P'

/-- Equation (2.7), interpreting P ≺ m_k as a lower bound at every positive time. -/
def minorantClass (k : ℕ) : Set (MvPolynomial (Fin (k - 1)) ℝ) :=
  {P | P.totalDegree ≤ k - 1 ∧ ∀ p ∈ Ak k, ∀ n : ℕ, 1 ≤ n → eval p P ≤ renewal p n}

/-- Equation (2.5): the product of the first k-1 partial sums. -/
noncomputable def Q (k : ℕ) : MvPolynomial (Fin (k - 1)) ℝ :=
  ∏ j : Fin (k - 1), ∑ l : Fin (k - 1), if l ≤ j then X l else 0

/-- The maximality clause of Nikolov–Savov Conjecture 3.7, with maximal as in (2.8). -/
def claim : Prop :=
  ∀ k : ℕ, 3 ≤ k → Q k ∈ minorantClass k ∧
    ∀ P ∈ minorantClass k, polynomialLE (Q k) P → P = Q k

theorem result : ¬ claim := by
  classical
  let P : MvPolynomial (Fin (4 - 1)) ℝ := X 0 ^ 2 * (X 0 + X 1 + X 2) + X 0 * X 1
  have hQ : Q 4 = X 0 * (X 0 + X 1) * (X 0 + X 1 + X 2) := by
    simp [Q, Fin.prod_univ_succ, Fin.sum_univ_succ]
    ring
  have hdeg : P.totalDegree ≤ 3 := by
    dsimp [P]
    have h01 : (X (0 : Fin 3) + X 1 : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 :=
      (totalDegree_add _ _).trans (by simp)
    have h012 : (X (0 : Fin 3) + X 1 + X 2 : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 :=
      (totalDegree_add _ _).trans (by simpa using h01)
    have hleft : (X (0 : Fin 3) ^ 2 * (X 0 + X 1 + X 2) :
        MvPolynomial (Fin 3) ℝ).totalDegree ≤ 3 := by
      apply (totalDegree_mul _ _).trans
      have hpow := totalDegree_pow (X (0 : Fin 3) : MvPolynomial (Fin 3) ℝ) 2
      simp only [totalDegree_X] at hpow
      omega
    have hright : (X (0 : Fin 3) * X 1 : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 2 :=
      (totalDegree_mul _ _).trans (by simp)
    exact (totalDegree_add _ _).trans (max_le hleft (hright.trans (by omega)))
  have hminor : ∀ p ∈ Ak 4, ∀ n : ℕ, 1 ≤ n → eval p P ≤ renewal p n := by
    intro p hp
    let x := p 0
    let y := p 1
    let z := p 2
    let w := 1 - x - y - z
    let b := x ^ 2 * (x + y + z) + x * y
    have hx : 0 ≤ x := hp.1 0
    have hy : 0 ≤ y := hp.1 1
    have hz : 0 ≤ z := hp.1 2
    have hsum : x + y + z ≤ 1 := by
      simpa [Fin.sum_univ_succ, x, y, z, add_assoc] using hp.2
    have hw : 0 ≤ w := by dsimp [w]; linarith
    have hx1 : x ≤ 1 := by linarith
    have heval : eval p P = b := by simp [P, b, x, y, z]
    have hu0 : renewal p 0 = 1 := by rw [renewal]
    have hu1 : renewal p 1 = x := by
      simp [renewal, stepMass, x]
    have hu2 : renewal p 2 = x ^ 2 + y := by
      rw [renewal]
      change (∑ l : Fin 2, stepMass p (l.val + 1) * renewal p (2 - (l.val + 1))) = _
      simp [Fin.sum_univ_succ, stepMass, hu0, hu1, x, y]
      ring
    have hu3 : renewal p 3 = x ^ 3 + 2 * x * y + z := by
      rw [renewal]
      change (∑ l : Fin 3, stepMass p (l.val + 1) * renewal p (3 - (l.val + 1))) = _
      simp [Fin.sum_univ_succ, stepMass, hu0, hu1, hu2, x, y, z]
      ring
    have hb1 : b ≤ x := by
      have cert : x - b = x * (z + (1 + x) * w) := by dsimp [b, w]; ring
      have := mul_nonneg hx (add_nonneg hz (mul_nonneg (by linarith : 0 ≤ 1 + x) hw))
      linarith
    have hb2 : b ≤ x ^ 2 + y := by
      have cert : x ^ 2 + y - b = x ^ 2 * w + y * (1 - x) := by dsimp [b, w]; ring
      have := add_nonneg (mul_nonneg (sq_nonneg x) hw) (mul_nonneg hy (by linarith : 0 ≤ 1 - x))
      linarith
    have hb3 : b ≤ x ^ 3 + 2 * x * y + z := by
      have cert : x ^ 3 + 2 * x * y + z - b = x * y * (1 - x) + z * (1 - x ^ 2) := by
        dsimp [b]; ring
      have hsq : 0 ≤ 1 - x ^ 2 := by nlinarith
      have := add_nonneg
        (mul_nonneg (mul_nonneg hx hy) (by linarith : 0 ≤ 1 - x)) (mul_nonneg hz hsq)
      linarith
    have alln : ∀ n : ℕ, b ≤ renewal p n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        by_cases h0 : n = 0
        · subst n; rw [hu0]; exact hb1.trans hx1
        by_cases h1 : n = 1
        · subst n; rw [hu1]; exact hb1
        by_cases h2 : n = 2
        · subst n; rw [hu2]; exact hb2
        by_cases h3 : n = 3
        · subst n; rw [hu3]; exact hb3
        have hn : 4 ≤ n := by omega
        have recur : renewal p n = x * renewal p (n - 1) + y * renewal p (n - 2) +
            z * renewal p (n - 3) + w * renewal p (n - 4) := by
          obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
          rw [renewal]
          rw [Nat.min_eq_right hn]
          simp [Fin.sum_univ_succ, stepMass, x, y, z, w]
          ring
        rw [recur]
        have hA := mul_le_mul_of_nonneg_left (ih (n - 1) (by omega)) hx
        have hB := mul_le_mul_of_nonneg_left (ih (n - 2) (by omega)) hy
        have hC := mul_le_mul_of_nonneg_left (ih (n - 3) (by omega)) hz
        have hD := mul_le_mul_of_nonneg_left (ih (n - 4) (by omega)) hw
        have weights : x * b + y * b + z * b + w * b = b := by dsimp [w]; ring
        linarith
    intro n _
    rw [heval]
    exact alln n
  have hle : polynomialLE (Q 4) P := by
    intro p hp
    have hsum : p 0 + p 1 + p 2 ≤ 1 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hp.2
    have cert : eval p P - eval p (Q 4) = p 0 * p 1 * (1 - p 0 - p 1 - p 2) := by
      rw [hQ]
      simp [P]
      ring
    have := mul_nonneg (mul_nonneg (hp.1 0) (hp.1 1))
      (by linarith : 0 ≤ 1 - p 0 - p 1 - p 2)
    linarith
  have hne : P ≠ Q 4 := by
    intro h
    have hv := congrArg (eval (fun _ : Fin 3 => (1 / 4 : ℝ))) h
    rw [hQ] at hv
    norm_num [P] at hv
  intro hc
  exact hne ((hc 4 (by omega)).2 P ⟨hdeg, hminor⟩ hle)

end D5.S3.StatisticalMechanics.RandomWalks.RenewalMinorantMaximalityRefutation
