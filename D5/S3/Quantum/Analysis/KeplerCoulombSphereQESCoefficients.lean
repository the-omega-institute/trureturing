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
  simpa only [Finset.Icc_add_one_left_eq_Ioc] using
    (Finset.add_sum_Ioc_eq_sum_Icc (f := f) hab).symm

private theorem sum_range_head {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), f j) = f 0 + ∑ j ∈ Finset.Icc 1 n, f j := by
  simpa only [Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc] using
    Finset.sum_range_eq_add_Ico f (Nat.succ_pos n)

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

private theorem coeff_expansion {p : Polynomial ℝ} {n : ℕ}
    (hz : ∀ i, n < i → p.coeff i = 0) :
    p = ∑ i ∈ Finset.range (n + 1), Polynomial.C (p.coeff i) * Polynomial.X ^ i := by
  exact p.as_sum_range_C_mul_X_pow'
    (Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hz))

private theorem shape_nonneg {p : Polynomial ℝ} {n : ℕ} {L : ℝ}
    (h : Shape p n L) (i : ℕ) : 0 ≤ p.coeff i := by
  by_cases hi : i ≤ n
  · exact (h.2.2 i hi).le
  · rw [h.1 i (by omega)]

private theorem shape_const {u : ℝ} (hu : 0 < u) : Shape (Polynomial.C u) 0 u := by
  rw [Shape.eq_1]
  refine ⟨?_, by simp, ?_⟩
  · intro i hi
    simp [Polynomial.coeff_C, show i ≠ 0 by omega]
  · intro i hi
    have : i = 0 := by omega
    simpa [this] using hu

private theorem shape_linear {p : Polynomial ℝ} {n : ℕ} {L u : ℝ}
    (hp : Shape p n L) (hu : 0 < u) :
    Shape ((Polynomial.X + Polynomial.C u) * p) (n + 1) L := by
  rw [Shape.eq_1, add_mul]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
    rw [Polynomial.coeff_X_mul, hp.1 i (by omega), hp.1 (i + 1) (by omega)]
    ring
  · rw [Polynomial.coeff_X_mul, hp.2.1, hp.1 (n + 1) (by omega)]
    ring
  · intro i hi
    cases i with
    | zero => simpa using mul_pos hu (hp.2.2 0 (Nat.zero_le n))
    | succ i =>
      rw [Polynomial.coeff_X_mul]
      exact add_pos_of_pos_of_nonneg (hp.2.2 i (by omega))
        (mul_nonneg hu.le (shape_nonneg hp _))

private theorem shape_shift {p : Polynomial ℝ} {n : ℕ} {L u : ℝ}
    (hp : Shape p n L) (hu : 0 < u) :
    Shape (Polynomial.C u + Polynomial.X * p) (n + 1) L := by
  rw [Shape.eq_1]
  simp only [Polynomial.coeff_add]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
    simp only [Polynomial.coeff_C, Nat.succ_ne_zero, ↓reduceIte, zero_add,
      Polynomial.coeff_X_mul]
    exact hp.1 i (by omega)
  · simpa using hp.2.1
  · intro i hi
    cases i with
    | zero => simpa using hu
    | succ i => simpa using hp.2.2 i (by omega)

private theorem shape_weighted_sum
    (s : Finset ℕ) (p : ℕ → Polynomial ℝ) (d : ℕ → ℕ) (w : ℕ → ℝ) (i : ℕ)
    (hi : i ∈ s) (hp : ∀ j ∈ s, Shape (p j) (d j) 1)
    (hw : ∀ j ∈ s, 0 < w j) (hmax : ∀ j ∈ s, j ≠ i → d j < d i) :
    Shape (∑ j ∈ s, Polynomial.C (w j) * p j) (d i) (w i) := by
  rw [Shape.eq_1]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    apply Finset.sum_eq_zero
    intro j hj
    have hd : d j ≤ d i := by
      by_cases he : j = i
      · subst j; rfl
      · exact (hmax j hj he).le
    rw [(hp j hj).1 r (by omega), mul_zero]
  · rw [Finset.sum_eq_single i]
    · rw [(hp i hi).2.1, mul_one]
    · intro j hj hji
      rw [(hp j hj).1 _ (hmax j hj hji), mul_zero]
    · exact fun hn => (hn hi).elim
  · intro r hr
    exact Finset.sum_pos' (fun j hj => mul_nonneg (hw j hj).le
      (shape_nonneg (hp j hj) r)) ⟨i, hi, mul_pos (hw i hi) ((hp i hi).2.2 r hr)⟩

private theorem base_shape (m n : ℕ) : Shape (basePoly m n) n 1 := by
  induction n with
  | zero => simpa only [basePoly.eq_1, Finset.range_zero, Finset.prod_empty, Polynomial.C_1] using
      (shape_const (u := 1) (by norm_num))
  | succ n ih =>
    rw [basePoly.eq_1, Finset.prod_range_succ, mul_comm]
    exact shape_linear ih (sq_pos_of_pos (by positivity))

private theorem D_shape (m : ℕ) : Shape (D m) (m / 2) 1 := by
  have h := shape_weighted_sum (Finset.range (m / 2 + 1)) (P m)
    (fun k => m / 2 - k) (fun k => F m (2 * k)) 0 (by simp)
    (fun k _ => base_shape m _) (fun k hk => F_pos (by simp only [Finset.mem_range] at hk; omega))
    (fun k hk hne => by simp only [Finset.mem_range] at hk; omega)
  simpa only [D.eq_1, E.eq_1, Nat.sub_zero, mul_zero, F.eq_1,
    Nat.descFactorial_zero, Nat.cast_one] using h

private theorem R_shape {m k : ℕ} (hk : k < m / 2) :
    Shape (R m k) (m / 2 - k - 1) (F m (2 * k + 1)) := by
  have h := shape_weighted_sum (Finset.Icc (k + 1) (m / 2)) (P m)
    (fun l => m / 2 - l) (fun l => F m (2 * l - 1)) (k + 1)
    (by simp; omega) (fun l _ => base_shape m _)
    (fun l hl => F_pos (by simp only [Finset.mem_Icc] at hl; omega))
    (fun l hl hne => by simp only [Finset.mem_Icc] at hl; omega)
  simpa only [R.eq_1, Nat.sub_sub, show 2 * (k + 1) - 1 = 2 * k + 1 by omega] using h

private theorem B_shape {m k : ℕ} (hm : 2 ≤ m) (hk : k ≤ (m - 1) / 2) :
    Shape (B m k) ((m - 1) / 2 - k) (F m (2 * k + 1)) := by
  rw [B.eq_1]
  split_ifs with he
  · convert R_shape (m := m) (k := k) (by omega) using 1
    omega
  · have ho : m % 2 = 1 := by omega
    by_cases ht : k = m / 2
    · subst k
      rw [H.eq_1, R.eq_1]
      simp only [Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self _), Finset.sum_empty,
        mul_zero, add_zero]
      convert shape_const (F_pos (m := m) (r := 2 * (m / 2) + 1) (by omega)) using 1
      omega
    · have hlt : k < m / 2 := by omega
      have hs := shape_shift (R_shape hlt)
        (F_pos (m := m) (r := 2 * (m / 2) + 1) (by omega))
      convert hs using 1 <;> first | rfl | omega

private theorem constants_positive {m : ℕ} (hm : 2 ≤ m) :
    PositiveConstants m (bValue m) (cValue m) := by
  rw [PositiveConstants.eq_1]
  constructor
  · intro j hj
    exact (D_shape m).2.2 _ (Nat.sub_le _ _)
  · intro k hk j hj
    exact div_pos ((B_shape hm hk).2.2 _ (Nat.sub_le _ _)) (F_pos (by omega))

private theorem shape_eval_pos {p : Polynomial ℝ} {n : ℕ} {L x : ℝ}
    (hp : Shape p n L) (hx : 0 ≤ x) : 0 < p.eval x := by
  rw [coeff_expansion hp.1, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (shape_nonneg hp i) (pow_nonneg hx i)
  · exact ⟨0, by simp, by simpa using hp.2.2 0 (Nat.zero_le _)⟩

private theorem D_eval_pos (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 < (D m).eval x :=
  shape_eval_pos (D_shape m) hx

end
end D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients
