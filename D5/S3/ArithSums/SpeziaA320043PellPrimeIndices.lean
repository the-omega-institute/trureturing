/- GID: D5/S3/ArithSums/SpeziaA320043PellPrimeIndices
   generality: I
   mirror-B: D5/B/S3/ArithSums/SpeziaA320043PellPrimeIndices
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.PellMatiyasevic]
   utility: none
   digest: For a prime p, A320043 a(p-1) is a square iff p is a term of A001075; for p > 2 iff p = x_(2^h), and then p = 7 mod 90. -/

import D5.S3.ArithSums.SpeziaA320043AllRowDivisorFormula
import D5.S3.ArithSums.SpeziaA320043PrimeRowCriterion
import Mathlib.NumberTheory.PellMatiyasevic

/-! Corollary 4 of H. Ma and W. Zhang, OEIS A320043, COMMENTS, revision 43: a square-value
refutation extending Zhu's Pell-prime result (2011): for `a(n) = Σ_{k=1}^n (n+1-k)² k /
gcd(n+1-k, k)³`, whose quotients are exact, and the Pell sequence `r` (A001075: `r 0 = 1`,
`r 1 = 2`, `r (j+2) = 4 r (j+1) - r j`), a prime `p` has `a(p - 1)` a square exactly when `p` is a
term of `r`. With `x 0 = 1`, `x 1 = 7`, `x (t+2) = 14 x (t+1) - x t`, so that `r (2t) = x t`, a
prime `p > 2` has `a(p - 1)` a square exactly when `p = x (2^h)` for some `h`, and every
`x (2^h)` is `7` modulo `90`, hence modulo `30`.

The terms `r j` are Mathlib's Pell solutions `Pell.xn` for `a = 2`, which are all the natural first
coordinates of solutions of `X² - 3Y² = 1` (`Pell.eq_pell`). Combined with the frozen prime-row
criterion (`p² - 12y² = 1`) and the exactness of the quotients from the frozen all-row divisor
formula, this gives the equivalence: odd-index terms are even, and even-index terms pair with an
even second coordinate. Mathlib's `xn_modEq_x2n_add` makes `xn m` divide `xn` at every odd multiple
of `m`, so a prime `x t` needs `t` to be a power of two, and the doubling `r (2k) = 2 r k² - 1`
fixes the residue `7` modulo `90`.

admission_basis: escape-witness. Escape witnesses: xn_odd_even (odd-index terms are even), dvd_odd
(divisibility at odd multiples), square_iff_r (square values at prime rows are the prime terms),
r_prime_iff (prime terms have power-of-two index), x_two_pow_mod (the residue modulo 90). -/

set_option autoImplicit false

namespace D5.S3.ArithSums.SpeziaA320043PellPrimeIndices

open Pell
open D5.S3.ArithSums.SpeziaA320043SquareValuesRefutation

/-- A001075: `r 0 = 1`, `r 1 = 2`, `r (j + 2) = 4 r (j + 1) - r j`. -/
def r : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | j + 2 => 4 * r (j + 1) - r j

/-- `x 0 = 1`, `x 1 = 7`, `x (t + 2) = 14 x (t + 1) - x t`. -/
def x : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | t + 2 => 14 * x (t + 1) - x t

private theorem h12 : 1 < 2 := by norm_num

/-- The Pell identity `xn² - 3 yn² = 1` for `a = 2`. -/
private theorem pell3 (n : ℕ) : (xn h12 n : ℤ) ^ 2 - 3 * (yn h12 n : ℤ) ^ 2 = 1 := by
  have hd := dz_val h12
  simp only [Pell.az] at hd
  norm_num at hd
  have hp := pell_eqz h12 n
  simp only [xz, yz, hd] at hp
  linarith

/-- Every natural solution of `X² - 3Y² = 1` is `(xn n, yn n)` for `a = 2`. -/
private theorem eq_pell3 {X Y : ℕ} (h : X * X - 3 * Y * Y = 1) :
    ∃ n, X = xn h12 n ∧ Y = yn h12 n := by
  apply eq_pell h12
  have hd := dz_val h12
  simp only [Pell.az] at hd
  norm_num at hd
  have hd2 : _ = 3 := Nat.cast_injective (R := ℤ) (hd.trans (by norm_num))
  rw [hd2]; exact h

private theorem r_eq (j : ℕ) : r j = xn h12 j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => simp [r]
    | 1, _ => simp [r]
    | j + 2, ih =>
      have := xz_succ_succ h12 j
      simp only [xz] at this
      rw [r, ih (j + 1) (by omega), ih j (by omega), this]
      norm_num

/-- `xn` at odd indices is even. -/
private theorem xn_odd_even (t : ℕ) : 2 ∣ xn h12 (2 * t + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := xz_succ_succ h12 (2 * t + 1)
    have h' := xz_succ_succ h12 (2 * t)
    simp only [xz] at h h'
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 2 by ring]
    have : (2 : ℤ) ∣ (xn h12 (2 * t + 1 + 2) : ℤ) := by
      rw [h]; norm_num
      exact dvd_sub (dvd_mul_of_dvd_left (by norm_num) _) (by exact_mod_cast ih)
    exact_mod_cast this

/-- `xn m` divides `xn` at every odd multiple of `m`. -/
private theorem dvd_odd (m i : ℕ) : xn h12 m ∣ xn h12 (m * (2 * i + 1)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have := xn_modEq_x2n_add h12 m (m * (2 * i + 1))
    rw [show 2 * m + m * (2 * i + 1) = m * (2 * (i + 1) + 1) by ring] at this
    exact (Nat.dvd_add_right ih).mp (Nat.modEq_zero_iff_dvd.mp this |>.trans (by rw [add_comm]))

private theorem doubling (k : ℕ) : (xn h12 (2 * k) : ℤ) = 2 * (xn h12 k : ℤ) ^ 2 - 1 := by
  have ha := congrArg (fun n : ℕ => (n : ℤ)) (xn_add h12 k k)
  have hp := pell_eqz h12 k
  simp only [Nat.cast_add, Nat.cast_mul] at ha
  simp only [xz, yz, two_mul] at *
  rw [ha]; linarith [hp]

private theorem x_eq (t : ℕ) : x t = r (2 * t) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    match t, ih with
    | 0, _ => simp [x, r]
    | 1, _ => simp [x, r]
    | t + 2, ih =>
      rw [x, ih (t + 1) (by omega), ih t (by omega)]
      have e1 : r (2 * t + 4) = 4 * r (2 * t + 3) - r (2 * t + 2) := by rw [r]
      have e2 : r (2 * t + 3) = 4 * r (2 * t + 2) - r (2 * t + 1) := by rw [r]
      have e3 : r (2 * t + 2) = 4 * r (2 * t + 1) - r (2 * t) := by rw [r]
      rw [show 2 * (t + 2) = 2 * t + 4 by ring, show 2 * (t + 1) = 2 * t + 2 by ring]
      linarith

private theorem x_two_pow_mod (h : ℕ) : x (2 ^ h) % 90 = 7 := by
  induction h with
  | zero => simp [x]
  | succ h ih =>
    rw [x_eq, r_eq, pow_succ, show 2 * (2 ^ h * 2) = 2 * (2 * 2 ^ h) by ring, doubling, ← r_eq,
      ← x_eq]
    obtain ⟨q, hq⟩ : ∃ q, x (2 ^ h) = 90 * q + 7 := ⟨x (2 ^ h) / 90, by omega⟩
    rw [hq, show 2 * (90 * q + 7) ^ 2 - 1 = 7 + 90 * (180 * q ^ 2 + 28 * q + 1) by ring]
    omega

private theorem square_iff_r (p : ℕ) (hp : p.Prime) :
    (∃ m, a (p - 1) = m ^ 2) ↔ ∃ j, (p : ℤ) = r j := by
  simp only [r_eq, Nat.cast_inj]
  have hp2 := hp.two_le
  have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
  rcases (show p = 2 ∨ p = 3 ∨ 5 ≤ p by omega) with rfl | rfl | h5
  · exact ⟨fun _ => ⟨1, by simp⟩, fun _ => ⟨1, by decide⟩⟩
  · constructor
    · rintro ⟨m, hm⟩
      have h6 : a 2 = 6 := by decide
      rw [h6] at hm
      have : m ≤ 3 := by nlinarith
      interval_cases m <;> omega
    · rintro ⟨j, hj⟩
      rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
      · simp at hj
      · simp at hj
      · have := (strictMono_x h12).monotone hj2
        have h7 : xn h12 2 = 7 := by
          have := r_eq 2; simp only [r] at this; omega
        omega
  · rw [(D5.S3.ArithSums.SpeziaA320043PrimeRowCriterion.prime_row_square_iff p hp h5).1]
    constructor
    · rintro ⟨y, -, hy⟩
      have hnat : p * p - 3 * (2 * y) * (2 * y) = 1 := by
        have : p * p = 1 + 3 * (2 * y) * (2 * y) := by
          have : (p : ℤ) * p = 1 + 3 * (2 * y) * (2 * y) := by linarith
          exact_mod_cast this
        omega
      obtain ⟨n, hn, -⟩ := eq_pell3 hnat
      exact ⟨n, hn⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
      · have ht : t ≠ 0 := by rintro rfl; simp at h5
        have hy2 : 2 ∣ yn h12 (2 * t) :=
          (Nat.modEq_zero_iff_dvd.mp ((yn_modEq_two h12 (2 * t)).trans (by simp [Nat.ModEq])))
        obtain ⟨y, hy⟩ := hy2
        have hpos : 0 < yn h12 (2 * t) := by
          have := strictMono_y h12 (show 0 < 2 * t by omega); simpa using this
        refine ⟨y, by omega, ?_⟩
        have := pell3 (2 * t)
        rw [hy] at this
        push_cast at this ⊢
        linarith
      · exfalso
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (xn_odd_even t)
        omega

/-- A prime `p > 2` among the `r j` is `x (2^h)` for some `h`. -/
private theorem r_prime_iff (p : ℕ) (hp : p.Prime) (h2 : 2 < p) :
    (∃ j, (p : ℤ) = r j) ↔ ∃ h, (p : ℤ) = x (2 ^ h) := by
  simp only [x_eq, r_eq, Nat.cast_inj]
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
    · have ht : t ≠ 0 := by rintro rfl; simp at h2
      obtain ⟨h, k, hk, rfl⟩ := Nat.exists_eq_two_pow_mul_odd ht
      obtain ⟨i, rfl⟩ := hk
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact ⟨h, by ring_nf⟩
      · exfalso
        have hd := dvd_odd (2 * 2 ^ h) i
        rw [show 2 * 2 ^ h * (2 * i + 1) = 2 * (2 ^ h * (2 * i + 1)) by ring] at hd
        have hm1 : 2 ≤ xn h12 (2 * 2 ^ h) := by
          have := (strictMono_x h12).monotone
            (show 1 ≤ 2 * 2 ^ h by have := Nat.one_le_two_pow (n := h); omega)
          simpa using this
        have hm2 : xn h12 (2 * 2 ^ h) < xn h12 (2 * (2 ^ h * (2 * i + 1))) := by
          apply strictMono_x h12
          have : 0 < 2 ^ h := by positivity
          nlinarith
        have := hp.eq_one_or_self_of_dvd _ hd
        omega
    · exfalso
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (xn_odd_even t)
      omega
  · rintro ⟨h, hh⟩
    exact ⟨2 * 2 ^ h, hh⟩

/-- Corollary 4 of Ma and Zhang: the quotients defining `a` are exact; `r (2t) = x t`; a prime
`p` has `a (p - 1)` a square exactly when `p` is a term of `r`, and for `p > 2` exactly when
`p = x (2^h)` for some `h`, and then `p ≡ 7 (mod 90)`; every `x (2^h)` is `7` modulo `90`, which
implies the source's residue `7` modulo `30`. -/
theorem result :
    (∀ n k : ℕ, Nat.gcd (n + 1 - k) k ^ 3 ∣ (n + 1 - k) ^ 2 * k) ∧
    (∀ t, r (2 * t) = x t) ∧
    (∀ p : ℕ, p.Prime → ((∃ m, a (p - 1) = m ^ 2) ↔ ∃ j, (p : ℤ) = r j)) ∧
    (∀ p : ℕ, p.Prime → 2 < p → ((∃ m, a (p - 1) = m ^ 2) ↔
      ∃ h, (p : ℤ) = x (2 ^ h) ∧ (p : ℤ) % 90 = 7)) ∧
    (∀ h, x (2 ^ h) % 90 = 7) := by
  refine ⟨D5.S3.ArithSums.SpeziaA320043AllRowDivisorFormula.result.1, fun t => (x_eq t).symm,
    square_iff_r, fun p hp h2 => ?_, x_two_pow_mod⟩
  rw [square_iff_r p hp, r_prime_iff p hp h2]
  constructor
  · rintro ⟨h, hh⟩; exact ⟨h, hh, hh ▸ x_two_pow_mod h⟩
  · rintro ⟨h, hh, -⟩; exact ⟨h, hh⟩

end D5.S3.ArithSums.SpeziaA320043PellPrimeIndices
