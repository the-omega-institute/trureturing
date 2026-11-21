/- GID: D5/S3/ArithSums/SpeziaA320043PellPrimeIndices
   generality: I
   mirror-B: D5/B/S3/ArithSums/SpeziaA320043PellPrimeIndices
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.Pell]
   utility: none
   digest: For a prime p, A320043 a(p-1) is a square iff p is a term of A001075; for p > 2 then p = x_(2^h) and p = 7 mod 30. -/

import D5.S3.ArithSums.SpeziaA320043PrimeRowCriterion
import Mathlib.NumberTheory.Pell

/-! Corollary 4 of H. Ma and W. Zhang, OEIS A320043, COMMENTS, revision 43: a square-value
refutation extending Zhu's Pell-prime result (2011): for `a(n) = Σ_{k=1}^n (n+1-k)² k /
gcd(n+1-k, k)³`, whose quotients are exact, and the Pell sequence `r` (A001075: `r 0 = 1`,
`r 1 = 2`, `r (j+2) = 4 r (j+1) - r j`), a prime `p` has `a(p - 1)` a square exactly when `p` is a
term of `r`. With `x 0 = 1`, `x 1 = 7`, `x (t+2) = 14 x (t+1) - x t`, so that `r (2t) = x t`, a
prime `p > 2` has `a(p - 1)` a square exactly when `p = x (2^h)` for some `h`, and every
`x (2^h)` is `7` modulo `30`.

The terms `r j` are the first coordinates of `(2 + √3)^j`, which are all the positive first
coordinates of solutions of `X² - 3Y² = 1`. Combined with the frozen prime-row criterion
(`p² - 12y² = 1`), this gives the equivalence. The identity
`r (i + 2k) + r i = 2 r (i + k) r k` makes `r m` divide `r` at every odd multiple of `m`, so a prime
`x t` needs `t` to be a power of two, and gives the doubling `r (2k) = 2 r k² - 1`, which fixes the
residue `7` modulo `30`.

admission_basis: escape-witness. Escape witnesses: add_formula (the addition identity), classify
(solutions of `X² - 3Y² = 1` through the fundamental solution), parity and pr_mono, dvd_odd (odd
multiples), doubling, square_iff_r and r_prime_iff. -/

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

/-- The fundamental solution `2 + √3` of `X² - 3Y² = 1`. -/
private def a₁ : Solution₁ 3 := Solution₁.mk 2 1 (by norm_num)

/-- The first coordinate of `(2 + √3)^n`. -/
private def pr (n : ℕ) : ℤ := (a₁ ^ n).x

/-- The second coordinate of `(2 + √3)^n`. -/
private def ps (n : ℕ) : ℤ := (a₁ ^ n).y

private theorem fundamental : IsFundamental a₁ := by
  refine ⟨by simp [a₁], by simp [a₁], fun {b} hb => ?_⟩
  simp only [a₁, Solution₁.x_mk]
  omega

private theorem pr_zero : pr 0 = 1 := by simp [pr]
private theorem pr_one : pr 1 = 2 := by simp [pr, a₁]

/-- `pr (m + k) + pr (m - k) = 2 pr m pr k`, written with `m = i + k`. -/
private theorem add_formula (i k : ℕ) : pr (i + 2 * k) + pr i = 2 * pr (i + k) * pr k := by
  have h1 : a₁ ^ (i + 2 * k) = a₁ ^ (i + k) * a₁ ^ k := by rw [← pow_add]; ring_nf
  have h2 : a₁ ^ i = a₁ ^ (i + k) * (a₁ ^ k)⁻¹ := by
    rw [pow_add, mul_assoc, mul_inv_cancel, mul_one]
  simp only [pr]
  rw [h1, h2, Solution₁.x_mul, Solution₁.x_mul, Solution₁.x_inv, Solution₁.y_inv]
  ring

private theorem pr_rec (n : ℕ) : pr (n + 2) = 4 * pr (n + 1) - pr n := by
  have := add_formula n 1
  rw [pr_one] at this
  linarith

private theorem prop (n : ℕ) : pr n ^ 2 - 3 * ps n ^ 2 = 1 := (a₁ ^ n).prop

/-- Every solution with positive first coordinate has first coordinate `pr n`. -/
private theorem classify (X Y : ℤ) (hX : 0 < X) (h : X ^ 2 - 3 * Y ^ 2 = 1) : ∃ n, X = pr n ∧
    (Y = ps n ∨ Y = -ps n) := by
  rcases le_or_gt 0 Y with hY | hY
  · obtain ⟨n, hn⟩ := fundamental.eq_pow_of_nonneg (a := Solution₁.mk X Y h) (by simpa) (by simpa)
    refine ⟨n, ?_, Or.inl ?_⟩
    · have := congrArg Solution₁.x hn; simpa [pr] using this
    · have := congrArg Solution₁.y hn; simpa [ps] using this
  · obtain ⟨n, hn⟩ := fundamental.eq_pow_of_nonneg (a := (Solution₁.mk X Y h)⁻¹)
      (by simpa) (by simp; linarith)
    refine ⟨n, ?_, Or.inr ?_⟩
    · have := congrArg Solution₁.x hn; simpa [pr] using this
    · have := congrArg Solution₁.y hn; simp [ps] at this ⊢; linarith

private theorem ps_zero : ps 0 = 0 := by simp [ps]
private theorem ps_one : ps 1 = 1 := by simp [ps, a₁]

private theorem ps_rec (n : ℕ) : ps (n + 2) = 4 * ps (n + 1) - ps n := by
  have h1 : a₁ ^ (n + 2) = a₁ ^ (n + 1) * a₁ := by rw [pow_succ]
  have h2 : a₁ ^ n = a₁ ^ (n + 1) * a₁⁻¹ := by
    rw [pow_succ, mul_assoc, mul_inv_cancel, mul_one]
  simp only [ps]
  rw [h1, h2, Solution₁.y_mul, Solution₁.y_mul, Solution₁.x_inv, Solution₁.y_inv]
  simp [a₁]; ring

/-- `1 ≤ pr n < pr (n + 1)`. -/
private theorem pr_mono (n : ℕ) : 1 ≤ pr n ∧ pr n < pr (n + 1) := by
  induction n with
  | zero => simp [pr_zero, pr_one]
  | succ n ih => rw [pr_rec]; constructor <;> linarith

private theorem pr_strictMono : StrictMono pr := strictMono_nat_of_lt_succ fun n => (pr_mono n).2

private theorem ps_pos (n : ℕ) : 0 < ps (n + 1) ∧ ps (n + 1) < ps (n + 2) := by
  induction n with
  | zero => rw [ps_rec, ps_one, ps_zero]; norm_num
  | succ n ih => rw [ps_rec (n + 1)]; constructor <;> linarith

private theorem parity (n : ℕ) :
    (pr (2 * n) % 2 = 1 ∧ ps (2 * n) % 2 = 0) ∧ pr (2 * n + 1) % 2 = 0 := by
  induction n with
  | zero => simp [pr_zero, ps_zero, pr_one]
  | succ n ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := ih
    have e1 : pr (2 * (n + 1)) = 4 * pr (2 * n + 1) - pr (2 * n) := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pr_rec]
    have e2 : ps (2 * (n + 1)) = 4 * ps (2 * n + 1) - ps (2 * n) := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, ps_rec]
    have e3 : pr (2 * (n + 1) + 1) = 4 * pr (2 * (n + 1)) - pr (2 * n + 1) := by
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, pr_rec,
        show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [e1]; omega
    · rw [e2]; omega
    · rw [e3]; omega

/-- `pr m` divides `r` at every odd multiple of `m`. -/
private theorem dvd_odd (m i : ℕ) : pr m ∣ pr (m * (2 * i + 1)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have := add_formula (m * (2 * i + 1)) m
    rw [show m * (2 * i + 1) + 2 * m = m * (2 * (i + 1) + 1) by ring] at this
    have h : pr (m * (2 * (i + 1) + 1)) =
        2 * pr (m * (2 * i + 1) + m) * pr m - pr (m * (2 * i + 1)) := by
      linarith
    rw [h]
    exact dvd_sub (Dvd.intro_left _ rfl) ih

private theorem doubling (k : ℕ) : pr (2 * k) = 2 * pr k ^ 2 - 1 := by
  have := add_formula 0 k
  rw [zero_add, zero_add, pr_zero] at this
  linarith


private theorem x_eq (t : ℕ) : x t = pr (2 * t) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    match t, ih with
    | 0, _ => simp [x, pr_zero]
    | 1, _ => simp [x, pr_rec, pr_one, pr_zero]
    | t + 2, ih =>
      rw [x, ih (t + 1) (by omega), ih t (by omega)]
      have e1 := pr_rec (2 * t + 2)
      have e2 := pr_rec (2 * t + 1)
      have e3 := pr_rec (2 * t)
      rw [show 2 * (t + 2) = 2 * t + 2 + 2 by ring, show 2 * (t + 1) = 2 * t + 2 by ring]
      rw [show 2 * t + 2 + 1 = 2 * t + 3 by ring] at e1
      rw [show 2 * t + 1 + 2 = 2 * t + 3 by ring, show 2 * t + 1 + 1 = 2 * t + 2 by ring] at e2
      rw [show 2 * t + 2 = 2 * t + 2 by ring, show 2 * t + 1 = 2 * t + 1 by ring] at e3
      linarith

private theorem x_two_pow_mod (h : ℕ) : x (2 ^ h) % 30 = 7 := by
  induction h with
  | zero => simp [x]
  | succ h ih =>
    rw [x_eq, pow_succ, show 2 * (2 ^ h * 2) = 2 * (2 * 2 ^ h) by ring, doubling, ← x_eq]
    obtain ⟨q, hq⟩ : ∃ q, x (2 ^ h) = 30 * q + 7 := ⟨x (2 ^ h) / 30, by omega⟩
    rw [hq, show 2 * (30 * q + 7) ^ 2 - 1 = 7 + 30 * (60 * q ^ 2 + 28 * q + 3) by ring]
    omega

/-- For a prime `p`, `a (p - 1)` is a square exactly when `p` is a term of `r`. -/
private theorem square_iff_r (p : ℕ) (hp : p.Prime) :
    (∃ m, a (p - 1) = m ^ 2) ↔ ∃ j, (p : ℤ) = pr j := by
  have hp2 := hp.two_le
  have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
  rcases (show p = 2 ∨ p = 3 ∨ 5 ≤ p by omega) with rfl | rfl | h5
  · exact ⟨fun _ => ⟨1, by simp [pr_one]⟩, fun _ => ⟨1, by decide⟩⟩
  · constructor
    · rintro ⟨m, hm⟩
      have h6 : a 2 = 6 := by decide
      rw [h6] at hm
      have : m ≤ 3 := by nlinarith
      interval_cases m <;> omega
    · rintro ⟨j, hj⟩
      rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
      · rw [pr_zero] at hj; norm_num at hj
      · rw [pr_one] at hj; norm_num at hj
      · have := pr_strictMono.monotone hj2
        rw [show pr 2 = 7 by rw [pr_rec, pr_one, pr_zero]; norm_num] at this
        omega
  · rw [(D5.S3.ArithSums.SpeziaA320043PrimeRowCriterion.prime_row_square_iff p hp h5).1]
    constructor
    · rintro ⟨y, -, hy⟩
      obtain ⟨n, hn, -⟩ := classify p (2 * y) (by positivity) (by linarith)
      exact ⟨n, hn⟩
    · rintro ⟨j, hj⟩
      obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
      · obtain ⟨⟨-, hs⟩, -⟩ := parity t
        have ht : t ≠ 0 := by rintro rfl; rw [pr_zero] at hj; omega
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        have hpos := (ps_pos (2 * t' + 1)).1
        rw [show 2 * t' + 1 + 1 = 2 * (t' + 1) by ring] at hpos
        obtain ⟨y, hy⟩ : ∃ y : ℕ, ps (2 * (t' + 1)) = 2 * y :=
          ⟨(ps (2 * (t' + 1)) / 2).toNat, by omega⟩
        refine ⟨y, by omega, ?_⟩
        have := prop (2 * (t' + 1))
        rw [← hj, hy] at this
        linarith
      · have := (parity t).2
        rw [← hj] at this
        have : 2 ∣ p := by omega
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this
        omega

/-- A prime `p > 2` among the `pr j` is `x (2^h)` for some `h`. -/
private theorem r_prime_iff (p : ℕ) (hp : p.Prime) (h2 : 2 < p) :
    (∃ j, (p : ℤ) = pr j) ↔ ∃ h, (p : ℤ) = x (2 ^ h) := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
    · have ht : t ≠ 0 := by rintro rfl; rw [pr_zero] at hj; omega
      obtain ⟨h, k, hk, rfl⟩ := Nat.exists_eq_two_pow_mul_odd ht
      obtain ⟨i, rfl⟩ := hk
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact ⟨h, by rw [x_eq, hj]; ring_nf⟩
      · exfalso
        have hd := dvd_odd (2 * 2 ^ h) i
        rw [show 2 * 2 ^ h * (2 * i + 1) = 2 * (2 ^ h * (2 * i + 1)) by ring, ← hj] at hd
        have hm1 : 2 ≤ pr (2 * 2 ^ h) := by
          have := pr_strictMono.monotone
            (show 1 ≤ 2 * 2 ^ h by have := Nat.one_le_two_pow (n := h); omega)
          rw [pr_one] at this; exact this
        have hm2 : pr (2 * 2 ^ h) < p := by
          rw [hj]; apply pr_strictMono
          have : 0 < 2 ^ h := by positivity
          nlinarith
        obtain ⟨d, hd'⟩ : ∃ d : ℕ, pr (2 * 2 ^ h) = d := ⟨(pr (2 * 2 ^ h)).toNat, by omega⟩
        rw [hd'] at hd hm1 hm2
        have := (hp.eq_one_or_self_of_dvd d (by exact_mod_cast hd))
        omega
    · have := (parity t).2
      rw [← hj] at this
      have h2p : 2 ∣ p := by omega
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p
      omega
  · rintro ⟨h, hh⟩
    exact ⟨2 * 2 ^ h, by rw [hh, x_eq]⟩


private theorem r_eq (j : ℕ) : r j = pr j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => simp [r, pr_zero]
    | 1, _ => simp [r, pr_one]
    | j + 2, ih => rw [r, pr_rec, ih (j + 1) (by omega), ih j (by omega)]

/-- Corollary 4 of Ma and Zhang: the quotients defining `a` are exact; `r (2t) = x t`; a prime
`p` has `a (p - 1)` a square exactly when `p` is a term of `r`, and for `p > 2` exactly when
`p = x (2^h)` for some `h`; and every `x (2^h)` is `7` modulo `30`. -/
theorem result :
    (∀ n k : ℕ, Nat.gcd (n + 1 - k) k ^ 3 ∣ (n + 1 - k) ^ 2 * k) ∧
    (∀ t, r (2 * t) = x t) ∧
    (∀ p : ℕ, p.Prime → ((∃ m, a (p - 1) = m ^ 2) ↔ ∃ j, (p : ℤ) = r j)) ∧
    (∀ p : ℕ, p.Prime → 2 < p → ((∃ m, a (p - 1) = m ^ 2) ↔ ∃ h, (p : ℤ) = x (2 ^ h))) ∧
    (∀ h, x (2 ^ h) % 30 = 7) := by
  refine ⟨fun n k => ?_, fun t => by rw [r_eq, x_eq], fun p hp => ?_, fun p hp h2 => ?_,
    x_two_pow_mod⟩
  · rw [pow_succ]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left _ _) 2) (Nat.gcd_dvd_right _ _)
  · simp only [r_eq]; exact square_iff_r p hp
  · rw [square_iff_r p hp]; exact r_prime_iff p hp h2

end D5.S3.ArithSums.SpeziaA320043PellPrimeIndices
