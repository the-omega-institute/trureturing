/- GID: D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Quesne's Kepler-Coulomb coefficient system has positive closed forms. -/

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients
open scoped BigOperators
noncomputable section

def System (m : ℕ) (Q κ : ℝ) (a : ℕ → ℝ) : Prop :=
  ((m : ℝ) + 1) * a 0 - a 1 = 1 ∧
  (m : ℝ) * Q * a 0 - Q * a 1 -
    (∑ k ∈ Finset.Icc 1 (m / 2), a (2 * k)) = 0 ∧
  (∀ k ∈ Finset.Icc 1 ((m - 1) / 2),
    ((m : ℝ) - 2 * (k : ℝ)) * a (2 * k) -
      Q * a (2 * k + 1) -
      (∑ l ∈ Finset.Icc (k + 1) (m / 2), a (2 * l)) = 0) ∧
  (∀ k ∈ Finset.Icc 1 (m / 2 - 1),
    κ * ((m : ℝ) + 1 - 2 * (k : ℝ)) * a (2 * k - 1) -
      Q * a (2 * k) -
      κ * ((m : ℝ) + 1 - 2 * (k : ℝ)) * a (2 * k + 1) = 0) ∧
  ((1 - (-1 : ℝ) ^ m) / 2) *
      (2 * κ * a (m - 2) - Q * a (m - 1) - 2 * κ * a m) +
    ((1 + (-1 : ℝ) ^ m) / 2) *
      (κ * a (m - 1) - Q * a m) = 0

def series (n : ℕ) (d : ℕ → ℝ) (Q κ : ℝ) : ℝ :=
  Q ^ (2 * n) +
    ∑ j ∈ Finset.Icc 1 n,
      d j * κ ^ j * Q ^ (2 * (n - j))

def delta (μ : ℕ) (b : ℕ → ℝ) (Q κ : ℝ) : ℝ :=
  series μ b Q κ

def OddForm (μ : ℕ) (Q κ : ℝ)
    (b : ℕ → ℝ) (c : ℕ → ℕ → ℝ) (a : ℕ → ℝ) : Prop :=
  a 0 =
    (∏ r ∈ Finset.range μ,
      (Q ^ 2 + 4 * ((r : ℝ) + 1) ^ 2 * κ)) /
      delta μ b Q κ ∧
  (∀ k, 1 ≤ k → k ≤ μ →
    a (2 * k) =
      (((2 * μ + 1).factorial : ℝ) /
        ((2 * μ - 2 * k + 1).factorial : ℝ)) *
      κ ^ k * Q *
      (∏ r ∈ Finset.range (μ - k),
        (Q ^ 2 + 4 * ((r : ℝ) + 1) ^ 2 * κ)) /
      delta μ b Q κ) ∧
  (∀ k, k ≤ μ →
    a (2 * k + 1) =
      (((2 * μ + 1).factorial : ℝ) /
        ((2 * μ - 2 * k).factorial : ℝ)) *
      κ ^ k * series (μ - k) (c k) Q κ /
      delta μ b Q κ)

def EvenForm (μ : ℕ) (Q κ : ℝ)
    (b : ℕ → ℝ) (c : ℕ → ℕ → ℝ) (a : ℕ → ℝ) : Prop :=
  a 0 =
    (∏ r ∈ Finset.range μ,
      (Q ^ 2 + (2 * (r : ℝ) + 1) ^ 2 * κ)) /
      delta μ b Q κ ∧
  (∀ k, 1 ≤ k → k ≤ μ →
    a (2 * k) =
      (((2 * μ).factorial : ℝ) /
        ((2 * μ - 2 * k).factorial : ℝ)) *
      κ ^ k * Q *
      (∏ r ∈ Finset.range (μ - k),
        (Q ^ 2 + (2 * (r : ℝ) + 1) ^ 2 * κ)) /
      delta μ b Q κ) ∧
  (∀ k, k < μ →
    a (2 * k + 1) =
      (((2 * μ).factorial : ℝ) /
        ((2 * μ - 2 * k - 1).factorial : ℝ)) *
      κ ^ k * Q ^ 2 *
      series (μ - k - 1) (c k) Q κ /
      delta μ b Q κ)

def ClosedForms (m : ℕ) (Q κ : ℝ)
    (b : ℕ → ℝ) (c : ℕ → ℕ → ℝ) (a : ℕ → ℝ) : Prop :=
  (m % 2 = 1 → OddForm (m / 2) Q κ b c a) ∧
  (m % 2 = 0 → EvenForm (m / 2) Q κ b c a)

def PositiveConstants (m : ℕ)
    (b : ℕ → ℝ) (c : ℕ → ℕ → ℝ) : Prop :=
  (∀ j ∈ Finset.Icc 1 (m / 2), 0 < b j) ∧
  (∀ k, k ≤ (m - 1) / 2 →
    ∀ j ∈ Finset.Icc 1 ((m - 1) / 2 - k), 0 < c k j)

def claim : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    ∃ b : ℕ → ℝ, ∃ c : ℕ → ℕ → ℝ,
      PositiveConstants m b c ∧
      ∀ Q κ : ℝ, 0 < Q → 0 < κ →
        (∃ a : ℕ → ℝ, System m Q κ a) ∧
        (∀ a : ℕ → ℝ,
          System m Q κ a → ClosedForms m Q κ b c a) ∧
        (∀ a a' : ℕ → ℝ,
          System m Q κ a →
          System m Q κ a' →
          ∀ i : ℕ, i ≤ m → a i = a' i)

private def F (m r : ℕ) : ℝ := (m.descFactorial r : ℝ)
private def t (m k : ℕ) : ℝ := (m : ℝ) - 2 * (k : ℝ) - 1
private def basePoly (m n : ℕ) : Polynomial ℝ :=
  ∏ r ∈ Finset.range n,
    (Polynomial.X + Polynomial.C (((2 * r + 1 + m % 2 : ℕ) : ℝ) ^ 2))
private def P (m k : ℕ) : Polynomial ℝ := basePoly m (m / 2 - k)
private def E (m k : ℕ) : Polynomial ℝ := Polynomial.C (F m (2 * k)) * P m k
private def R (m k : ℕ) : Polynomial ℝ :=
  ∑ l ∈ Finset.Icc (k + 1) (m / 2), Polynomial.C (F m (2 * l - 1)) * P m l
private def H (m k : ℕ) : Polynomial ℝ :=
  Polynomial.C (F m (2 * (m / 2) + 1)) + Polynomial.X * R m k
private def D (m : ℕ) : Polynomial ℝ := ∑ k ∈ Finset.range (m / 2 + 1), E m k
private def B (m k : ℕ) : Polynomial ℝ := if m % 2 = 0 then R m k else H m k
private def bValue (m j : ℕ) : ℝ := (D m).coeff (m / 2 - j)
private def cValue (m k j : ℕ) : ℝ :=
  (B m k).coeff ((m - 1) / 2 - k - j) / F m (2 * k + 1)
private def evenPart (Q : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then a 0 else a (2 * k) / Q
private def oddPart (m : ℕ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  if 2 * k + 1 ≤ m then a (2 * k + 1) else 0
private def Normalized (m : ℕ) (x : ℝ) (e o : ℕ → ℝ) : Prop :=
  ((m : ℝ) + 1) * e 0 - o 0 = 1 ∧
  (∀ k, k ≤ m / 2 → o k = (t m k + 1) * e k -
    ∑ l ∈ Finset.Icc (k + 1) (m / 2), e l) ∧
  (∀ k, k < m / 2 → t m k * (o k - o (k + 1)) = x * e (k + 1))
private def assemble (Q : ℝ) (e o : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then e 0 else if i % 2 = 0 then Q * e (i / 2) else o (i / 2)
private def Shape (p : Polynomial ℝ) (n : ℕ) (L : ℝ) : Prop :=
  (∀ i, n < i → p.coeff i = 0) ∧ p.coeff n = L ∧ (∀ i, i ≤ n → 0 < p.coeff i)

private theorem t_pos {m k : ℕ} (hk : k < m / 2) : 0 < t m k := by
  rw [t.eq_1]
  have h : 2 * k + 2 ≤ m := by omega
  have hc : (2 : ℝ) * k + 2 ≤ m := by exact_mod_cast h
  linarith

private theorem F_succ (m r : ℕ) :
    F m (r + 1) = ((m - r : ℕ) : ℝ) * F m r := by
  simp only [F.eq_1, Nat.descFactorial_succ, Nat.cast_mul]

private theorem F_pos {m r : ℕ} (hr : r ≤ m) : 0 < F m r := by
  rw [F.eq_1]
  exact_mod_cast Nat.descFactorial_pos.mpr hr

private theorem F_ratio {m r : ℕ} (hr : r ≤ m) :
    F m r = (m.factorial : ℝ) / ((m - r).factorial : ℝ) := by
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero (m - r))).mpr
  rw [F.eq_1, mul_comm]
  exact_mod_cast Nat.factorial_mul_descFactorial hr

private theorem sum_head {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (a b : ℕ) (hab : a ≤ b) :
    (∑ j ∈ Finset.Icc a b, f j) = f a + ∑ j ∈ Finset.Icc (a + 1) b, f j := by
  rw [← Finset.sum_insert (by simp)]
  congr 1
  ext j
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

private theorem sum_range_head {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), f j) = f 0 + ∑ j ∈ Finset.Icc 1 n, f j := by
  rw [← sum_head f 0 n (Nat.zero_le n)]
  congr 1
  ext j
  simp only [Finset.mem_range, Finset.mem_Icc]
  omega

private theorem P_step {m k : ℕ} (hk : k < m / 2) :
    P m k = (Polynomial.X + Polynomial.C ((t m k) ^ 2)) * P m (k + 1) := by
  have hn : m / 2 - k = (m / 2 - (k + 1)) + 1 := by omega
  have hc : ((2 * (m / 2 - (k + 1)) + 1 + m % 2 : ℕ) : ℝ) = t m k := by
    have hh : 2 * (m / 2 - (k + 1)) + 1 + m % 2 = m - (2 * k + 1) := by omega
    rw [hh, Nat.cast_sub (by omega), t.eq_1]
    push_cast
    ring
  simp only [P.eq_1, basePoly.eq_1]
  rw [hn, Finset.prod_range_succ, hc, mul_comm]

private theorem terminal_values (m : ℕ) (x : ℝ) :
    (E m (m / 2)).eval x = F m (2 * (m / 2)) ∧
    (H m (m / 2)).eval x = F m (2 * (m / 2) + 1) := by
  simp only [E.eq_1, P.eq_1, basePoly.eq_1, H.eq_1, R.eq_1, Nat.sub_self,
    Finset.range_zero, Finset.prod_empty, mul_one,
    Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self _), Finset.sum_empty, mul_zero, add_zero,
    Polynomial.eval_C]
  exact ⟨trivial, trivial⟩

private theorem E_step {m k : ℕ} (hk : k < m / 2) (x : ℝ) :
    (t m k + 1) * t m k * (E m k).eval x =
      (x + (t m k) ^ 2) * (E m (k + 1)).eval x := by
  have ha : ((m - 2 * k : ℕ) : ℝ) = t m k + 1 := by
    rw [Nat.cast_sub (by omega), t.eq_1]; push_cast; ring
  have hb : ((m - (2 * k + 1) : ℕ) : ℝ) = t m k := by
    rw [Nat.cast_sub (by omega), t.eq_1]; push_cast; ring
  have hf : F m (2 * (k + 1)) = (t m k) * (t m k + 1) * F m (2 * k) := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, F_succ, F_succ, ha, hb]
    ring
  simp only [E.eq_1, Polynomial.eval_mul, Polynomial.eval_C]
  rw [P_step hk, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, hf]
  ring

private theorem H_step {m k : ℕ} (hk : k < m / 2) (x : ℝ) :
    t m k * ((H m k).eval x - (H m (k + 1)).eval x) =
      x * (E m (k + 1)).eval x := by
  have hf : F m (2 * (k + 1)) = t m k * F m (2 * (k + 1) - 1) := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, F_succ]
    rw [show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega,
      Nat.cast_sub (by omega), t.eq_1]
    push_cast; ring
  simp only [H.eq_1, R.eq_1, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_finsetSum]
  rw [sum_head _ (k + 1) (m / 2) (by omega)]
  simp only [E.eq_1, Polynomial.eval_mul, Polynomial.eval_C, hf]
  ring

private theorem E_tail {m k : ℕ} (hk : k ≤ m / 2) (x : ℝ) :
    (t m k + 1) * (E m k).eval x = (H m k).eval x +
      ∑ l ∈ Finset.Icc (k + 1) (m / 2), (E m l).eval x := by
  generalize hn : m / 2 - k = n
  induction n generalizing k with
  | zero =>
    have he : k = m / 2 := by omega
    subst k
    rw [(terminal_values m x).1, (terminal_values m x).2, F_succ]
    simp only [Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self _), Finset.sum_empty, add_zero]
    rw [Nat.cast_sub (by omega), t.eq_1]
    push_cast; ring
  | succ n ih =>
    have hlt : k < m / 2 := by omega
    have hh := ih (k := k + 1) (by omega) (by omega)
    have hs := H_step hlt x
    have he := E_step hlt x
    have ht := t_pos hlt
    have htt : t m (k + 1) = t m k - 2 := by
      simp only [t.eq_1, Nat.cast_add, Nat.cast_one]; ring
    rw [sum_head _ (k + 1) (m / 2) (by omega)]
    rw [htt] at hh
    nlinarith

private theorem first_identity (m : ℕ) (x : ℝ) :
    ((m : ℝ) + 1) * (E m 0).eval x - (H m 0).eval x = (D m).eval x := by
  have h := E_tail (m := m) (k := 0) (Nat.zero_le _) x
  rw [D.eq_1, Polynomial.eval_finsetSum, sum_range_head]
  simp only [t.eq_1, Nat.cast_zero, mul_zero, sub_zero] at h
  linarith

end
end D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients
