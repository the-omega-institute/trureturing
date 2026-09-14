/- GID: D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral differential states prove eventual periods for every scaled logarithm column. -/

import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Eventual periods of scaled logarithm columns

The entries A383165 and A383166 of Seiichi Manyama give the columns r = 2 and
r = 3 of log(1 + (exp(2X) - 1)/2)^r/r!. Peter Bala conjectures eventual
periodicity modulo every positive integer. See
`Library/ArithSums/bala2026a383165.md` and
`Library/ArithSums/bala2026a383166.md`.

Write H = (1 + exp(2X))/2 and U = H⁻¹. The identities H' = 2H - 1,
U' = U² - 2U and (log H)' = 2 - U give an integral differential system for
B(r,j) = U^j (log H)^r/r!. Induction identifies its integer recurrence with
n! [X^n] B(r,j). In particular numerator extraction in a loses no information.

Modulo m, the recurrence depends on j only through its residue. For fixed r,
the columns indexed by s ≤ r and j < m form a finite deterministic state.
A repeated state therefore gives an eventual period. This proves all columns,
including both conjectures, without asserting any particular or minimal period.
The finite state argument and the scaled differential bridge are used in both
instances. No frozen prerequisite is needed.
-/

open PowerSeries
namespace D5.S1.Recurrence.Periodic.ScaledLogColumnPeriodicity

private noncomputable def H : PowerSeries ℚ :=
  1 + C (1 / 2 : ℚ) * (rescale 2 (exp ℚ) - 1)
private noncomputable def U : PowerSeries ℚ := H⁻¹
private noncomputable def L : PowerSeries ℚ := logOf H
private noncomputable def F (r : ℕ) : PowerSeries ℚ :=
  C (1 / (r.factorial : ℚ)) * L ^ r
private noncomputable def B (r j : ℕ) : PowerSeries ℚ := U ^ j * F r

private theorem H_zero : constantCoeff H = 1 := by
  simp [H, ← coeff_zero_eq_constantCoeff, coeff_rescale]
private theorem U_H : U * H = 1 := PowerSeries.inv_mul_cancel H (by rw [H_zero]; norm_num)
private theorem U_zero : constantCoeff U = 1 := by simp [U, constantCoeff_inv, H_zero]
private theorem L_zero : constantCoeff L = 0 := constantCoeff_logOf H_zero

private theorem H_derivative : derivative ℚ H = 2 * H - 1 := by
  have he : rescale (2 : ℚ) (exp ℚ) = exp ℚ ^ 2 := (exp_pow_eq_rescale_exp 2).symm
  simp only [H, he, map_add, map_sub, Derivation.leibniz, derivative_one,
    derivative_C, derivative_pow, derivative_exp, smul_eq_mul]
  norm_num
  have h : (2 : PowerSeries ℚ) * C (1 / 2 : ℚ) = 1 := by
    rw [show (2 : PowerSeries ℚ) = C (2 : ℚ) by exact (map_ofNat (C (R := ℚ)) 2).symm, ← map_mul]; norm_num
  linear_combination h

private theorem log_derivative_mul : derivative ℚ (log ℚ) * (1 + X) = 1 := by
  have h := congrArg (rescale (-1 : ℚ)) (mk_one_mul_one_sub_eq_one ℚ)
  have he : rescale (-1 : ℚ) (mk 1) = derivative ℚ (log ℚ) := by
    ext n
    simp [deriv_log]
  simpa [he] using h

private theorem L_derivative : derivative ℚ L = 2 - U := by
  have hs : HasSubst (H - 1) := .of_constantCoeff_zero (by change constantCoeff (H - 1) = 0; simp [H_zero])
  have hone : subst (H - 1) (1 : PowerSeries ℚ) = 1 := by
    rw [← coe_substAlgHom hs]; exact map_one _
  have h := congrArg (subst (H - 1)) log_derivative_mul
  have hmul : (derivative ℚ (log ℚ)).subst (H - 1) * H = 1 := by
    simpa only [subst_mul hs, subst_add hs, hone, subst_X hs,
      add_sub_cancel] using h
  have hEq : (derivative ℚ (log ℚ)).subst (H - 1) = U := by
    calc
      _ = ((derivative ℚ (log ℚ)).subst (H - 1) * H) * U := by
        rw [mul_assoc, mul_comm H U, U_H, mul_one]
      _ = U := by rw [hmul, one_mul]
  rw [L, logOf_eq, derivative_subst hs, hEq, map_sub, derivative_one,
    sub_zero, H_derivative]
  linear_combination 2 * U_H

private theorem U_derivative : derivative ℚ U = U ^ 2 - 2 * U := by
  rw [U, derivative_inv', H_derivative]
  change -(U ^ 2) * (2 * H - 1) = U ^ 2 - 2 * U
  linear_combination -2 * U * U_H

private theorem F_zero : F 0 = 1 := by simp [F]
private theorem F_derivative (r : ℕ) :
    derivative ℚ (F (r + 1)) = (2 - U) * F r := by
  have hf : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  have hc : C (1 / ((r + 1).factorial : ℚ)) * (r + 1 : PowerSeries ℚ) =
      C (1 / (r.factorial : ℚ)) := by
    rw [show (r + 1 : PowerSeries ℚ) = C (r + 1 : ℚ) by simp, ← map_mul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  simp only [F, Derivation.leibniz, derivative_C, smul_eq_mul, mul_zero, add_zero,
    derivative_pow, Nat.add_sub_cancel, L_derivative]
  rw [show (↑(r + 1) : PowerSeries ℚ) = r + 1 by simp]
  linear_combination L ^ r * (2 - U) * hc

private theorem U_pow_derivative (j : ℕ) :
    derivative ℚ (U ^ j) = C (j : ℚ) * U ^ (j + 1) - C (2 * j : ℚ) * U ^ j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [derivative_pow, U_derivative]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, map_mul,
      map_ofNat, map_add, map_one, map_natCast]
    simp only [pow_succ]
    ring

private theorem B_derivative (r j : ℕ) :
    derivative ℚ (B r j) = C (j : ℚ) * B r (j + 1) - C (2 * j : ℚ) * B r j +
      if r = 0 then 0 else 2 * B (r - 1) j - B (r - 1) (j + 1) := by
  cases r with
  | zero => simpa only [B, F_zero, mul_one, if_true, add_zero] using U_pow_derivative j
  | succ r =>
    simp only [B, Derivation.leibniz, smul_eq_mul, U_pow_derivative,
      F_derivative, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, pow_succ]
    ring

private theorem B_constant (r j : ℕ) : constantCoeff (B r j) = if r = 0 then 1 else 0 := by
  cases r <;> simp [B, F, U_zero, L_zero]

private def W : ℕ → ℕ → ℕ → ℤ
  | 0, r, _ => if r = 0 then 1 else 0
  | n + 1, r, j => (j : ℤ) * W n r (j + 1) - 2 * j * W n r j +
      if r = 0 then 0 else 2 * W n (r - 1) j - W n (r - 1) (j + 1)

private theorem scaled_derivative (f : PowerSeries ℚ) (n : ℕ) :
    (n.factorial : ℚ) * coeff n (derivative ℚ f) =
      ((n + 1).factorial : ℚ) * coeff (n + 1) f := by
  rw [coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

private theorem scaled_bridge (n r j : ℕ) :
    (W n r j : ℚ) = (n.factorial : ℚ) * coeff n (B r j) := by
  induction n generalizing r j with
  | zero => simpa only [W, Nat.factorial_zero, Nat.cast_one, one_mul,
      coeff_zero_eq_constantCoeff, Int.cast_ite, Int.cast_one, Int.cast_zero]
      using (B_constant r j).symm
  | succ n ih =>
    rw [← scaled_derivative, B_derivative]
    have htwo : (2 : PowerSeries ℚ) = C (2 : ℚ) := (map_ofNat (C (R := ℚ)) 2).symm
    by_cases hr : r = 0
    · simp only [W, hr, if_true, Int.cast_sub, Int.cast_mul,
        Int.cast_natCast, Int.cast_ofNat, add_zero, map_sub, coeff_C_mul]
      rw [ih, ih]
      ring
    · simp only [W, hr, if_false, Int.cast_add, Int.cast_sub, Int.cast_mul,
        Int.cast_natCast, Int.cast_ofNat, map_add, map_sub, htwo, coeff_C_mul]
      rw [ih, ih, ih, ih]
      ring


private theorem W_congr (m n r j k : ℕ) (h : (j : ZMod m) = (k : ZMod m)) :
    (W n r j : ZMod m) = (W n r k : ZMod m) := by
  induction n generalizing r j k with
  | zero => simp [W]
  | succ n ih =>
    have hs : ((j + 1 : ℕ) : ZMod m) = ((k + 1 : ℕ) : ZMod m) := by simpa only [Nat.cast_add, Nat.cast_one] using congrArg (· + 1) h
    simp only [W, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    rw [h, ih r (j + 1) (k + 1) hs, ih r j k h]
    split_ifs <;> simp only [Int.cast_zero, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
      ih (r - 1) j k h, ih (r - 1) (j + 1) (k + 1) hs]

private def state (r m n : ℕ) : Fin (r + 1) → Fin m → ZMod m :=
  fun s j => W n s.val j.val

private theorem state_step (r m n l : ℕ) (hm : 0 < m)
    (h : state r m n = state r m l) : state r m (n + 1) = state r m (l + 1) := by
  have he (s j : ℕ) (hs : s ≤ r) : (W n s j : ZMod m) = (W l s j : ZMod m) := by
    have hj : (j : ZMod m) = ((j % m : ℕ) : ZMod m) := by simp
    calc
      _ = (W n s (j % m) : ZMod m) := W_congr m n s j (j % m) hj
      _ = (W l s (j % m) : ZMod m) := congrFun (congrFun h ⟨s, by omega⟩) ⟨j % m, Nat.mod_lt j hm⟩
      _ = (W l s j : ZMod m) := (W_congr m l s j (j % m) hj).symm
  funext s j
  simp only [state, W, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  rw [he s.val (j.val + 1) (by omega), he s.val j.val (by omega)]
  split_ifs <;> simp only [Int.cast_zero, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
    he (s.val - 1) j.val (by omega), he (s.val - 1) (j.val + 1) (by omega)]

private theorem state_period (r m : ℕ) (hm : 0 < m) :
    ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → state r m (n + p) = state r m n := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨i, j, heq, hne⟩ : ∃ i j, state r m i = state r m j ∧ i ≠ j := by
    simpa [Function.Injective] using not_injective_infinite_finite (state r m)
  have go (i j : ℕ) (hij : i < j) (h : state r m i = state r m j) :
      ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → state r m (n + p) = state r m n := by
    have hk : ∀ k, state r m (i + k) = state r m (j + k) := by
      intro k
      induction k with
      | zero => simpa using h
      | succ k ih => simpa [Nat.add_assoc] using state_step r m (i + k) (j + k) hm ih
    refine ⟨i, j - i, by omega, ?_⟩
    intro n hn
    convert (hk (n - i)).symm using 1 <;> congr 1 <;> omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact go i j hlt heq
  · exact go j i hlt heq.symm

private theorem W_period (r m : ℕ) (hm : 0 < m) :
    ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → (W (n + p) r 0 : ZMod m) = (W n r 0 : ZMod m) := by
  obtain ⟨N, p, hp, h⟩ := state_period r m hm
  refine ⟨N, p, hp, ?_⟩
  intro n hn
  exact congrFun (congrFun (h n hn) ⟨r, by omega⟩) ⟨0, hm⟩

/-- Integer e.g.f. coefficients of log(1 + (exp(2X)-1)/2)^r/r!.
The coefficient bridge proves the rational number inside `num` is integral. -/
noncomputable def a (r n : ℕ) : ℤ :=
  ((n.factorial : ℚ) * coeff n
    (C (1 / (r.factorial : ℚ)) *
      logOf (1 + C (1 / 2 : ℚ) * (rescale 2 (exp ℚ) - 1)) ^ r)).num

private theorem a_eq (r n : ℕ) : a r n = W n r 0 := by
  have h := scaled_bridge n r 0
  simp only [B, pow_zero, one_mul] at h
  change ((n.factorial : ℚ) * coeff n (F r)).num = W n r 0
  rw [← h, Rat.num_intCast]

/-- The integer sequence has exactly the defining e.g.f., for every column. -/
theorem generating_equation (r : ℕ) :
    mk (fun n => (a r n : ℚ) / (n.factorial : ℚ)) =
      C (1 / (r.factorial : ℚ)) *
        logOf (1 + C (1 / 2 : ℚ) * (rescale 2 (exp ℚ) - 1)) ^ r := by
  ext n
  rw [coeff_mk, a_eq, scaled_bridge n r 0]
  simp only [B, pow_zero, one_mul]
  change (n.factorial : ℚ) * coeff n (F r) / (n.factorial : ℚ) = coeff n (F r)
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- Every column is eventually periodic modulo every positive integer.
The onset and positive period are existential; no minimality is asserted. -/
theorem coefficient_periodicity (r m : ℕ) (hm : 0 < m) :
    ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n →
      (a r (n + p) : ZMod m) = (a r n : ZMod m) := by
  simpa only [a_eq] using W_period r m hm

/-- Peter Bala's conjecture on OEIS A383165, the column r = 2. -/
theorem bala_conjecture_a383165 (m : ℕ) (hm : 0 < m) :
    ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n →
      (a 2 (n + p) : ZMod m) = (a 2 n : ZMod m) :=
  coefficient_periodicity 2 m hm

/-- Peter Bala's conjecture on OEIS A383166, the column r = 3. -/
theorem bala_conjecture_a383166 (m : ℕ) (hm : 0 < m) :
    ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n →
      (a 3 (n + p) : ZMod m) = (a 3 n : ZMod m) :=
  coefficient_periodicity 3 m hm

#print axioms a
#print axioms generating_equation
#print axioms coefficient_periodicity
#print axioms bala_conjecture_a383165
#print axioms bala_conjecture_a383166

end D5.S1.Recurrence.Periodic.ScaledLogColumnPeriodicity
