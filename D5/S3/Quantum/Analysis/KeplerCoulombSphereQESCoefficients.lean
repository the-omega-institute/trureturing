/- GID: D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Quesne's Kepler-Coulomb coefficient system has positive closed forms. -/

import D5.S3.Constants.NewtonHankelRealRootCriterion
import D5.S3.Zeros.Convolution.AlternatingFactorialSum

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
  rw [F.eq_1]
  exact D5.S3.Zeros.Convolution.AlternatingFactorialSum.real_descFactorial m r hr

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
    rw [bValue.eq_1]
    exact (D_shape m).2.2 _ (Nat.sub_le _ _)
  · intro k hk j hj
    rw [cValue.eq_1]
    exact div_pos ((B_shape hm hk).2.2 _ (Nat.sub_le _ _)) (F_pos (by omega))

private theorem shape_eval_pos {p : Polynomial ℝ} {n : ℕ} {L x : ℝ}
    (hp : Shape p n L) (hx : 0 ≤ x) : 0 < p.eval x := by
  apply D5.S3.Constants.NewtonHankelRealRootCriterion.eval_pos_of_positive_coefficients
    (d := n) ?_ hx
  exact ⟨Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hp.1)
    (ne_of_gt (hp.2.2 n le_rfl)), hp.2.2⟩

private theorem D_eval_pos (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 < (D m).eval x :=
  shape_eval_pos (D_shape m) hx

private theorem parity_power (m : ℕ) :
    (-1 : ℝ) ^ m = if m % 2 = 0 then 1 else -1 := by
  rw [neg_one_pow_eq_pow_mod_two]
  have h : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

private theorem assemble_zero (Q : ℝ) (e o : ℕ → ℝ) : assemble Q e o 0 = e 0 := by
  rw [assemble.eq_1, if_pos rfl]
private theorem assemble_even (Q : ℝ) (e o : ℕ → ℝ) {k : ℕ} (hk : 0 < k) :
    assemble Q e o (2 * k) = Q * e k := by
  rw [assemble.eq_1, if_neg (by omega), if_pos (by omega)]
  congr 2
  omega
private theorem assemble_odd (Q : ℝ) (e o : ℕ → ℝ) (k : ℕ) :
    assemble Q e o (2 * k + 1) = o k := by
  rw [assemble.eq_1, if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

private theorem normalize {m : ℕ} {Q κ : ℝ} {a : ℕ → ℝ}
    (hm : 2 ≤ m) (hQ : Q ≠ 0) (hκ : κ ≠ 0) (ha : System m Q κ a) :
    Normalized m (Q ^ 2 / κ) (evenPart Q a) (oddPart m a) := by
  rw [System.eq_1] at ha
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  have hs (k : ℕ) : (∑ l ∈ Finset.Icc (k + 1) (m / 2), evenPart Q a l) =
      (∑ l ∈ Finset.Icc (k + 1) (m / 2), a (2 * l)) / Q := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l hl
    rw [evenPart.eq_1, if_neg (by simp only [Finset.mem_Icc] at hl; omega)]
  rw [Normalized.eq_1]
  refine ⟨?_, ?_, ?_⟩
  · simpa [evenPart.eq_1, oddPart.eq_1, show 1 ≤ m by omega] using h0
  · intro k hk
    rw [hs]
    by_cases hz : k = 0
    · subst k
      simp only [evenPart.eq_1, oddPart.eq_1, Nat.zero_add, ite_true,
        if_pos (show 1 ≤ m by omega), t.eq_1, Nat.cast_zero, mul_zero, sub_zero]
      field_simp
      nlinarith [h1]
    · rw [evenPart.eq_1, if_neg hz, oddPart.eq_1]
      by_cases ho : 2 * k + 1 ≤ m
      · rw [if_pos ho, t.eq_1]
        have hh := h2 k (by simp only [Finset.mem_Icc]; omega)
        field_simp
        nlinarith [hh]
      · have he : k = m / 2 := by omega
        have hc : (m : ℝ) = 2 * (k : ℝ) := by exact_mod_cast (show m = 2 * k by omega)
        rw [if_neg ho, t.eq_1, hc, sub_self, sub_add_cancel,
          show Finset.Icc (k + 1) (m / 2) = ∅ by subst k; simp]
        simp
  · intro k hk
    have he : k + 1 ≠ 0 := by omega
    rw [evenPart.eq_1, if_neg he, oddPart.eq_1, if_pos (by omega), oddPart.eq_1]
    have hh : κ * t m k *
        (a (2 * k + 1) - if 2 * (k + 1) + 1 ≤ m then a (2 * (k + 1) + 1) else 0) =
        Q * a (2 * (k + 1)) := by
      by_cases ht : k + 1 < m / 2
      · rw [if_pos (by omega), t.eq_1]
        have hh := h3 (k + 1) (by simp only [Finset.mem_Icc]; omega)
        rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hh
        push_cast at hh
        nlinarith [hh]
      · have hlast : k + 1 = m / 2 := by omega
        rw [parity_power] at h4
        by_cases hp : m % 2 = 0
        · have hm' : m = 2 * (k + 1) := by omega
          have hc : (m : ℝ) = 2 * ((k : ℝ) + 1) := by exact_mod_cast hm'
          simp only [hp, ite_true] at h4
          rw [if_neg (by omega), t.eq_1, hc,
            show 2 * k + 1 = m - 1 by omega, show 2 * (k + 1) = m by omega]
          nlinarith [h4]
        · have hm' : m = 2 * (k + 1) + 1 := by omega
          have hc : (m : ℝ) = 2 * ((k : ℝ) + 1) + 1 := by exact_mod_cast hm'
          rw [if_neg hp] at h4
          rw [if_pos (by omega), t.eq_1, hc,
            show 2 * k + 1 = m - 2 by omega, show 2 * (k + 1) + 1 = m by omega,
            show 2 * (k + 1) = m - 1 by omega]
          nlinarith [h4]
    apply (mul_left_cancel₀ hκ)
    field_simp
    nlinarith [hh]

private theorem denormalize {m : ℕ} {Q κ : ℝ} {e o : ℕ → ℝ}
    (hm : 2 ≤ m) (hκ : κ ≠ 0)
    (h : Normalized m (Q ^ 2 / κ) e o) : System m Q κ (assemble Q e o) := by
  rw [Normalized.eq_1] at h
  rcases h with ⟨h0, h1, h2⟩
  have hs (k : ℕ) : (∑ l ∈ Finset.Icc (k + 1) (m / 2), assemble Q e o (2 * l)) =
      Q * ∑ l ∈ Finset.Icc (k + 1) (m / 2), e l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    exact assemble_even Q e o (by simp only [Finset.mem_Icc] at hl; omega)
  rw [System.eq_1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [assemble_zero, assemble_odd Q e o 0]
    exact h0
  · rw [assemble_zero, show 1 = 2 * 0 + 1 from rfl, assemble_odd, hs 0]
    have hh := h1 0 (Nat.zero_le _)
    simp only [t.eq_1, Nat.cast_zero, mul_zero, sub_zero] at hh
    linear_combination -Q * hh
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [assemble_even Q e o (by omega), assemble_odd, hs]
    have hh := h1 k (by omega)
    rw [t.eq_1] at hh
    linear_combination -Q * hh
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [show 2 * k - 1 = 2 * (k - 1) + 1 by omega, assemble_odd,
      assemble_even Q e o (by omega), assemble_odd]
    have hh := h2 (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega, t.eq_1, Nat.cast_sub (by omega)] at hh
    push_cast at hh
    field_simp at hh
    nlinarith [hh]
  · have hmu : 0 < m / 2 := by omega
    have hh := h2 (m / 2 - 1) (by omega)
    rw [show m / 2 - 1 + 1 = m / 2 by omega, t.eq_1,
      Nat.cast_sub (by omega)] at hh
    push_cast at hh
    field_simp at hh
    rw [parity_power]
    by_cases hp : m % 2 = 0
    · have hc : (m : ℝ) = 2 * (m / 2 : ℕ) := by exact_mod_cast (show m = 2 * (m / 2) by omega)
      have hz := h1 (m / 2) (Nat.le_refl _)
      simp only [t.eq_1, hc, sub_self, Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self _),
        Finset.sum_empty] at hz
      have ha : assemble Q e o (m - 1) = o (m / 2 - 1) := by
        exact (congrArg (assemble Q e o) (show m - 1 = 2 * (m / 2 - 1) + 1 by omega)).trans
          (assemble_odd Q e o _)
      have hb : assemble Q e o m = Q * e (m / 2) := by
        exact (congrArg (assemble Q e o) (show m = 2 * (m / 2) by omega)).trans
          (assemble_even Q e o hmu)
      rw [if_pos hp, ha, hb]
      rw [hc] at hh
      norm_num at hz ⊢
      rw [hz] at hh
      nlinarith [hh]
    · have hc : (m : ℝ) = 2 * (m / 2 : ℕ) + 1 := by
        exact_mod_cast (show m = 2 * (m / 2) + 1 by omega)
      have ha : assemble Q e o (m - 2) = o (m / 2 - 1) := by
        exact (congrArg (assemble Q e o) (show m - 2 = 2 * (m / 2 - 1) + 1 by omega)).trans
          (assemble_odd Q e o _)
      have hb : assemble Q e o (m - 1) = Q * e (m / 2) := by
        exact (congrArg (assemble Q e o) (show m - 1 = 2 * (m / 2) by omega)).trans
          (assemble_even Q e o hmu)
      have hd : assemble Q e o m = o (m / 2) := by
        exact (congrArg (assemble Q e o) (show m = 2 * (m / 2) + 1 by omega)).trans
          (assemble_odd Q e o _)
      rw [if_neg hp, ha, hb, hd]
      rw [hc] at hh
      norm_num
      nlinarith [hh]

private theorem normalized_mass {m : ℕ} {x : ℝ} {e o : ℕ → ℝ}
    (h : Normalized m x e o) : (∑ k ∈ Finset.range (m / 2 + 1), e k) = 1 := by
  have hh := h.2.1 0 (Nat.zero_le _)
  rw [sum_range_head]
  simp only [t.eq_1, Nat.cast_zero, mul_zero, sub_zero, Nat.zero_add] at hh
  linarith [h.1]

private theorem normalized_step {m k : ℕ} {x : ℝ} {e o : ℕ → ℝ}
    (h : Normalized m x e o) (hk : k < m / 2) :
    (t m k + 1) * t m k * e k = (x + (t m k) ^ 2) * e (k + 1) := by
  have ha := h.2.1 k hk.le
  have hb := h.2.1 (k + 1) (by omega)
  have hc := h.2.2 k hk
  have ht : t m (k + 1) = t m k - 2 := by
    simp only [t.eq_1, Nat.cast_add, Nat.cast_one]; ring
  rw [sum_head _ (k + 1) (m / 2) (by omega)] at ha
  rw [ht] at hb
  linear_combination -(t m k) * ha + (t m k) * hb + hc

private theorem proportional {m : ℕ} {x : ℝ} {e o : ℕ → ℝ}
    (h : Normalized m x e o) : ∀ k, k ≤ m / 2 →
    e k * F m (2 * (m / 2)) = e (m / 2) * (E m k).eval x := by
  intro k hk
  generalize hn : m / 2 - k = n
  induction n generalizing k with
  | zero =>
    have he : k = m / 2 := by omega
    subst k
    rw [(terminal_values m x).1]
  | succ n ih =>
    have hlt : k < m / 2 := by omega
    have hh := ih (k := k + 1) (by omega) (by omega)
    have hs := normalized_step h hlt
    have he := E_step hlt x
    have ht := t_pos hlt
    apply mul_left_cancel₀ (show (t m k + 1) * t m k ≠ 0 by positivity)
    linear_combination F m (2 * (m / 2)) * hs - e (m / 2) * he +
      (x + (t m k) ^ 2) * hh

private theorem normalized_values {m : ℕ} {x : ℝ} {e o : ℕ → ℝ}
    (hx : 0 < x) (h : Normalized m x e o) : ∀ k, k ≤ m / 2 →
    e k = (E m k).eval x / (D m).eval x ∧ o k = (H m k).eval x / (D m).eval x := by
  have hd := (D_eval_pos m hx.le).ne'
  have hf := (F_pos (m := m) (r := 2 * (m / 2)) (by omega)).ne'
  have hs : F m (2 * (m / 2)) = e (m / 2) * (D m).eval x := by
    calc
      F m (2 * (m / 2)) = (∑ k ∈ Finset.range (m / 2 + 1), e k) * F m (2 * (m / 2)) := by
        rw [normalized_mass h, one_mul]
      _ = ∑ k ∈ Finset.range (m / 2 + 1), e k * F m (2 * (m / 2)) := Finset.sum_mul ..
      _ = ∑ k ∈ Finset.range (m / 2 + 1), e (m / 2) * (E m k).eval x := by
        apply Finset.sum_congr rfl
        intro k hk
        exact proportional h k (by simp only [Finset.mem_range] at hk; omega)
      _ = e (m / 2) * (D m).eval x := by
        rw [D.eq_1, Polynomial.eval_finsetSum, Finset.mul_sum]
  have he (k : ℕ) (hk : k ≤ m / 2) : e k = (E m k).eval x / (D m).eval x := by
    apply (eq_div_iff hd).mpr
    apply mul_right_cancel₀ hf
    linear_combination (D m).eval x * proportional h k hk - (E m k).eval x * hs
  intro k hk
  refine ⟨he k hk, ?_⟩
  rw [h.2.1 k hk, he k hk]
  have ht : (∑ l ∈ Finset.Icc (k + 1) (m / 2), e l) =
      (∑ l ∈ Finset.Icc (k + 1) (m / 2), (E m l).eval x) / (D m).eval x := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l hl
    exact he l (Finset.mem_Icc.mp hl).2
  rw [ht]
  field_simp
  linear_combination E_tail hk x

private theorem normalized_explicit (m : ℕ) {x : ℝ} (hx : 0 < x) :
    Normalized m x (fun k => (E m k).eval x / (D m).eval x)
      (fun k => (H m k).eval x / (D m).eval x) := by
  have hd := (D_eval_pos m hx.le).ne'
  rw [Normalized.eq_1]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination first_identity m x
  · intro k hk
    rw [← Finset.sum_div]
    field_simp
    linear_combination -E_tail hk x
  · intro k hk
    field_simp
    linear_combination H_step hk x

private def answer (m : ℕ) (Q κ : ℝ) : ℕ → ℝ :=
  assemble Q (fun k => (E m k).eval (Q ^ 2 / κ) / (D m).eval (Q ^ 2 / κ))
    (fun k => (H m k).eval (Q ^ 2 / κ) / (D m).eval (Q ^ 2 / κ))

private theorem answer_system {m : ℕ} {Q κ : ℝ}
    (hm : 2 ≤ m) (hQ : 0 < Q) (hκ : 0 < κ) : System m Q κ (answer m Q κ) := by
  rw [answer.eq_1]
  exact denormalize hm hκ.ne' (normalized_explicit m (div_pos (sq_pos_of_pos hQ) hκ))

private theorem solution_values {m : ℕ} {Q κ : ℝ} {a : ℕ → ℝ}
    (hm : 2 ≤ m) (hQ : 0 < Q) (hκ : 0 < κ) (ha : System m Q κ a) :
    a 0 = (E m 0).eval (Q ^ 2 / κ) / (D m).eval (Q ^ 2 / κ) ∧
    (∀ k, 1 ≤ k → k ≤ m / 2 → a (2 * k) =
      Q * (E m k).eval (Q ^ 2 / κ) / (D m).eval (Q ^ 2 / κ)) ∧
    (∀ k, k ≤ (m - 1) / 2 → a (2 * k + 1) =
      (H m k).eval (Q ^ 2 / κ) / (D m).eval (Q ^ 2 / κ)) := by
  have h := normalized_values (div_pos (sq_pos_of_pos hQ) hκ) (normalize hm hQ.ne' hκ.ne' ha)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [evenPart.eq_1, ite_true] using (h 0 (Nat.zero_le _)).1
  · intro k hk hkm
    have hh := (h k hkm).1
    rw [evenPart.eq_1, if_neg (by omega)] at hh
    rw [(div_eq_iff hQ.ne').mp hh]
    ring
  · intro k hk
    have hh := (h k (by omega)).2
    simpa only [oddPart.eq_1, if_pos (show 2 * k + 1 ≤ m by omega)] using hh

private theorem system_unique {m : ℕ} {Q κ : ℝ} {a a' : ℕ → ℝ}
    (hm : 2 ≤ m) (hQ : 0 < Q) (hκ : 0 < κ)
    (ha : System m Q κ a) (ha' : System m Q κ a') : ∀ i, i ≤ m → a i = a' i := by
  have h := solution_values hm hQ hκ ha
  have h' := solution_values hm hQ hκ ha'
  intro i hi
  by_cases hz : i = 0
  · subst i; exact h.1.trans h'.1.symm
  · by_cases he : i % 2 = 0
    · have hh : i = 2 * (i / 2) := by omega
      exact (congrArg a hh).trans ((h.2.1 _ (by omega) (by omega)).trans
        ((h'.2.1 _ (by omega) (by omega)).symm.trans (congrArg a' hh).symm))
    · have hh : i = 2 * (i / 2) + 1 := by omega
      exact (congrArg a hh).trans ((h.2.2 _ (by omega)).trans
        ((h'.2.2 _ (by omega)).symm.trans (congrArg a' hh).symm))

private theorem scale_power {n j : ℕ} {Q κ : ℝ} (hj : j ≤ n) (hκ : κ ≠ 0) :
    κ ^ n * (Q ^ 2 / κ) ^ (n - j) = κ ^ j * Q ^ (2 * (n - j)) := by
  have hp : κ ^ n = κ ^ j * κ ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  rw [div_pow, ← pow_mul, hp]
  calc
    _ = κ ^ j * ((Q ^ (2 * (n - j)) / κ ^ (n - j)) * κ ^ (n - j)) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ (pow_ne_zero _ hκ)]

private theorem series_rescale {p : Polynomial ℝ} {n : ℕ} {L Q κ : ℝ}
    (hp : Shape p n L) (hκ : κ ≠ 0) :
    series n (fun j => p.coeff (n - j) / L) Q κ =
      κ ^ n * p.eval (Q ^ 2 / κ) / L := by
  have hL : L ≠ 0 := by rw [← hp.2.1]; exact (hp.2.2 n (Nat.le_refl _)).ne'
  have he : p.eval (Q ^ 2 / κ) =
      ∑ i ∈ Finset.range (n + 1), p.coeff i * (Q ^ 2 / κ) ^ i := by
    conv_lhs => rw [coeff_expansion hp.1, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hr : (∑ j ∈ Finset.range (n + 1), p.coeff (n - j) * (Q ^ 2 / κ) ^ (n - j)) =
      p.eval (Q ^ 2 / κ) := by
    rw [he]
    simpa only [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (fun i => p.coeff i * (Q ^ 2 / κ) ^ i) (n + 1)
  calc
    series n (fun j => p.coeff (n - j) / L) Q κ =
        ∑ j ∈ Finset.range (n + 1), p.coeff (n - j) / L * κ ^ j * Q ^ (2 * (n - j)) := by
      rw [sum_range_head, series.eq_1]
      simp only [Nat.sub_zero, hp.2.1, div_self hL, pow_zero, one_mul]
    _ = ∑ j ∈ Finset.range (n + 1), κ ^ n *
        (p.coeff (n - j) * (Q ^ 2 / κ) ^ (n - j)) / L := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show κ ^ n * (p.coeff (n - j) * (Q ^ 2 / κ) ^ (n - j)) =
        p.coeff (n - j) * (κ ^ n * (Q ^ 2 / κ) ^ (n - j)) by ring,
        scale_power (by simp only [Finset.mem_range] at hj; omega) hκ]
      ring
    _ = κ ^ n * p.eval (Q ^ 2 / κ) / L := by
      rw [← Finset.sum_div, ← Finset.mul_sum, hr]

private theorem delta_rescale (m : ℕ) {Q κ : ℝ} (hκ : κ ≠ 0) :
    delta (m / 2) (bValue m) Q κ = κ ^ (m / 2) * (D m).eval (Q ^ 2 / κ) := by
  rw [delta.eq_1]
  change series (m / 2) (fun j => (D m).coeff (m / 2 - j)) Q κ = _
  simpa only [div_one] using
    (series_rescale (Q := Q) (D_shape m) hκ)

private theorem P_rescale (m n : ℕ) {Q κ : ℝ} (hκ : κ ≠ 0) :
    κ ^ n * (basePoly m n).eval (Q ^ 2 / κ) =
      ∏ r ∈ Finset.range n, (Q ^ 2 + (((2 * r + 1 + m % 2 : ℕ) : ℝ) ^ 2) * κ) := by
  induction n with
  | zero => simp only [basePoly.eq_1, Finset.range_zero, Finset.prod_empty,
      Polynomial.eval_one, pow_zero, mul_one]
  | succ n ih =>
    rw [basePoly.eq_1, Finset.prod_range_succ, ← basePoly.eq_1, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Finset.prod_range_succ, pow_succ]
    calc
      _ = (κ ^ n * (basePoly m n).eval (Q ^ 2 / κ)) *
          (Q ^ 2 + (((2 * n + 1 + m % 2 : ℕ) : ℝ) ^ 2) * κ) := by
        rw [mul_add, mul_add]
        rw [show κ ^ n * κ * ((basePoly m n).eval (Q ^ 2 / κ) * (Q ^ 2 / κ)) =
          (κ ^ n * (basePoly m n).eval (Q ^ 2 / κ)) * ((Q ^ 2 / κ) * κ) by ring,
          div_mul_cancel₀ _ hκ]
        ring
      _ = _ := by rw [ih]

private theorem E_rescale {m k : ℕ} {Q κ : ℝ} (hk : k ≤ m / 2) (hκ : κ ≠ 0) :
    κ ^ (m / 2) * (E m k).eval (Q ^ 2 / κ) = F m (2 * k) * κ ^ k *
      ∏ r ∈ Finset.range (m / 2 - k),
        (Q ^ 2 + (((2 * r + 1 + m % 2 : ℕ) : ℝ) ^ 2) * κ) := by
  have hp : κ ^ (m / 2) = κ ^ k * κ ^ (m / 2 - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  rw [E.eq_1, Polynomial.eval_C_mul, P.eq_1]
  calc
    _ = F m (2 * k) * κ ^ k * (κ ^ (m / 2 - k) *
        (basePoly m (m / 2 - k)).eval (Q ^ 2 / κ)) := by rw [hp]; ring
    _ = _ := by rw [P_rescale m _ hκ]

private theorem H_rescale {m k : ℕ} {Q κ : ℝ}
    (hm : 2 ≤ m) (hk : k ≤ (m - 1) / 2) (hκ : κ ≠ 0) :
    κ ^ (m / 2) * (H m k).eval (Q ^ 2 / κ) =
      F m (2 * k + 1) * κ ^ k * Q ^ (2 * (1 - m % 2)) *
        series ((m - 1) / 2 - k) (cValue m k) Q κ := by
  have hf := (F_pos (m := m) (r := 2 * k + 1) (by omega)).ne'
  have hs : series ((m - 1) / 2 - k) (cValue m k) Q κ =
      κ ^ ((m - 1) / 2 - k) * (B m k).eval (Q ^ 2 / κ) / F m (2 * k + 1) := by
    change series ((m - 1) / 2 - k)
      (fun j => (B m k).coeff ((m - 1) / 2 - k - j) / F m (2 * k + 1)) Q κ = _
    exact series_rescale (B_shape hm hk) hκ
  rw [hs, B.eq_1]
  by_cases he : m % 2 = 0
  · have hn : (m - 1) / 2 - k = m / 2 - k - 1 := by omega
    have hz : F m (2 * (m / 2) + 1) = 0 := by
      rw [F_succ, show m - 2 * (m / 2) = 0 by omega, Nat.cast_zero, zero_mul]
    have hp : κ ^ (m / 2) = κ ^ k * κ ^ (m / 2 - k - 1) * κ := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    rw [if_pos he, he, hn, H.eq_1, hz, Polynomial.C_0, zero_add,
      Polynomial.eval_mul, Polynomial.eval_X, hp]
    simp only [Nat.sub_zero, mul_one]
    rw [show (κ ^ k * κ ^ (m / 2 - k - 1) * κ) *
      (Q ^ 2 / κ * (R m k).eval (Q ^ 2 / κ)) =
      κ ^ k * κ ^ (m / 2 - k - 1) * ((Q ^ 2 / κ) * κ) *
        (R m k).eval (Q ^ 2 / κ) by ring, div_mul_cancel₀ _ hκ]
    rw [show F m (2 * k + 1) * κ ^ k * Q ^ 2 *
      (κ ^ (m / 2 - k - 1) * (R m k).eval (Q ^ 2 / κ) / F m (2 * k + 1)) =
      κ ^ k * κ ^ (m / 2 - k - 1) * Q ^ 2 * (R m k).eval (Q ^ 2 / κ) *
        (F m (2 * k + 1) / F m (2 * k + 1)) by ring, div_self hf, mul_one]
  · have ho : m % 2 = 1 := by omega
    have hn : (m - 1) / 2 - k = m / 2 - k := by omega
    have hp : κ ^ (m / 2) = κ ^ k * κ ^ (m / 2 - k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [if_neg he, ho, hn, hp]
    simp only [Nat.sub_self, mul_zero, pow_zero, mul_one]
    rw [show F m (2 * k + 1) * κ ^ k *
      (κ ^ (m / 2 - k) * (H m k).eval (Q ^ 2 / κ) / F m (2 * k + 1)) =
      κ ^ k * κ ^ (m / 2 - k) * (H m k).eval (Q ^ 2 / κ) *
        (F m (2 * k + 1) / F m (2 * k + 1)) by ring, div_self hf, mul_one]

private theorem solution_forms {m : ℕ} {Q κ : ℝ} {a : ℕ → ℝ}
    (hm : 2 ≤ m) (hQ : 0 < Q) (hκ : 0 < κ) (ha : System m Q κ a) :
    ClosedForms m Q κ (bValue m) (cValue m) a := by
  have hv := solution_values hm hQ hκ ha
  have hquot (v : ℝ) : v / (D m).eval (Q ^ 2 / κ) =
      (κ ^ (m / 2) * v) / delta (m / 2) (bValue m) Q κ := by
    rw [delta_rescale m hκ.ne']
    exact (mul_div_mul_left v _ (pow_ne_zero _ hκ.ne')).symm
  have hz : a 0 = (∏ r ∈ Finset.range (m / 2),
      (Q ^ 2 + (((2 * r + 1 + m % 2 : ℕ) : ℝ) ^ 2) * κ)) /
      delta (m / 2) (bValue m) Q κ := by
    rw [hv.1, hquot, E_rescale (Nat.zero_le _) hκ.ne']
    simp only [F.eq_1, mul_zero, Nat.descFactorial_zero, Nat.cast_one, pow_zero,
      one_mul, mul_one, Nat.sub_zero]
  have he (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ m / 2) : a (2 * k) =
      F m (2 * k) * κ ^ k * Q * (∏ r ∈ Finset.range (m / 2 - k),
        (Q ^ 2 + (((2 * r + 1 + m % 2 : ℕ) : ℝ) ^ 2) * κ)) /
        delta (m / 2) (bValue m) Q κ := by
    rw [hv.2.1 k hk0 hk, hquot]
    rw [show κ ^ (m / 2) * (Q * (E m k).eval (Q ^ 2 / κ)) =
      Q * (κ ^ (m / 2) * (E m k).eval (Q ^ 2 / κ)) by ring, E_rescale hk hκ.ne']
    ring
  have ho (k : ℕ) (hk : k ≤ (m - 1) / 2) : a (2 * k + 1) =
      F m (2 * k + 1) * κ ^ k * Q ^ (2 * (1 - m % 2)) *
        series ((m - 1) / 2 - k) (cValue m k) Q κ /
        delta (m / 2) (bValue m) Q κ := by
    rw [hv.2.2 k hk, hquot, H_rescale hm hk hκ.ne']
  rw [ClosedForms.eq_1]
  constructor
  · intro hp
    have hm' : m = 2 * (m / 2) + 1 := by omega
    have hprod (n : ℕ) : (∏ r ∈ Finset.range n,
        (Q ^ 2 + (((2 * r + 1 + m % 2 : ℕ) : ℝ) ^ 2) * κ)) =
        ∏ r ∈ Finset.range n, (Q ^ 2 + 4 * ((r : ℝ) + 1) ^ 2 * κ) := by
      apply Finset.prod_congr rfl
      intro r _
      rw [hp]
      push_cast
      ring
    rw [OddForm.eq_1]
    refine ⟨?_, ?_, ?_⟩
    · rw [hz, hprod]
    · intro k hk0 hk
      have hf : F m (2 * k) = ((2 * (m / 2) + 1).factorial : ℝ) /
          ((2 * (m / 2) - 2 * k + 1).factorial : ℝ) := by
        rw [F_ratio (by omega)]
        exact congrArg₂ (fun u v : ℕ => (u.factorial : ℝ) / (v.factorial : ℝ)) hm' (by omega)
      rw [he k hk0 hk, hf, hprod]
    · intro k hk
      have hf : F m (2 * k + 1) = ((2 * (m / 2) + 1).factorial : ℝ) /
          ((2 * (m / 2) - 2 * k).factorial : ℝ) := by
        rw [F_ratio (by omega)]
        exact congrArg₂ (fun u v : ℕ => (u.factorial : ℝ) / (v.factorial : ℝ)) hm' (by omega)
      rw [ho k (by omega), hf, hp, show (m - 1) / 2 - k = m / 2 - k by omega]
      simp only [Nat.sub_self, mul_zero, pow_zero, mul_one]
  · intro hp
    have hm' : m = 2 * (m / 2) := by omega
    have hprod (n : ℕ) : (∏ r ∈ Finset.range n,
        (Q ^ 2 + (((2 * r + 1 + m % 2 : ℕ) : ℝ) ^ 2) * κ)) =
        ∏ r ∈ Finset.range n, (Q ^ 2 + (2 * (r : ℝ) + 1) ^ 2 * κ) := by
      apply Finset.prod_congr rfl
      intro r _
      rw [hp]
      push_cast
      ring
    rw [EvenForm.eq_1]
    refine ⟨?_, ?_, ?_⟩
    · rw [hz, hprod]
    · intro k hk0 hk
      have hf : F m (2 * k) = ((2 * (m / 2)).factorial : ℝ) /
          ((2 * (m / 2) - 2 * k).factorial : ℝ) := by
        rw [F_ratio (by omega)]
        exact congrArg₂ (fun u v : ℕ => (u.factorial : ℝ) / (v.factorial : ℝ)) hm' (by omega)
      rw [he k hk0 hk, hf, hprod]
    · intro k hk
      have hf : F m (2 * k + 1) = ((2 * (m / 2)).factorial : ℝ) /
          ((2 * (m / 2) - 2 * k - 1).factorial : ℝ) := by
        rw [F_ratio (by omega)]
        exact congrArg₂ (fun u v : ℕ => (u.factorial : ℝ) / (v.factorial : ℝ)) hm' (by omega)
      rw [ho k (by omega), hf, hp, show (m - 1) / 2 - k = m / 2 - k - 1 by omega]

theorem result : claim := by
  rw [claim.eq_1]
  intro m hm
  refine ⟨bValue m, cValue m, constants_positive hm, ?_⟩
  intro Q κ hQ hκ
  refine ⟨⟨answer m Q κ, answer_system hm hQ hκ⟩, ?_, ?_⟩
  · intro a ha
    exact solution_forms hm hQ hκ ha
  · intro a a' ha ha'
    exact system_unique hm hQ hκ ha ha'

end
end D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients
