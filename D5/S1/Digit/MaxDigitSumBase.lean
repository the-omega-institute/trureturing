/- GID: D5/S1/Digit/MaxDigitSumBase
   generality: G
   mirror-B: D5/B/S1/Digit/MaxDigitSumBase
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Irvine's A394431 conjecture: the least digit-sum-maximizing base is ceiling((n+1)/2). -/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor

/-!
OEIS A394431 asks for the smallest base `b` with `1 < b < n` at which the base-`b` digit sum
of `n` is largest. Sean A. Irvine conjectured on 2026-03-25 that this base is
`ceiling((n+1)/2)` for every `n > 8`.
-/

namespace D5.S1.Digit.MaxDigitSumBase

/-- The sum of the base-`b` digits of `n`. -/
def digitSum (b n : ℕ) : ℕ := (Nat.digits b n).sum

/-- `b` is the smallest base in `1 < b < n` at which the digit sum of `n` is largest. -/
def IsLeastMaxDigitSumBase (n b : ℕ) : Prop :=
  1 < b ∧ b < n ∧
    (∀ c, 1 < c → c < n → digitSum c n ≤ digitSum b n) ∧
    ∀ c, 1 < c → c < b → digitSum c n < digitSum b n

private theorem digitSum_step {b n : ℕ} (hb : 1 < b) :
    digitSum b n = n % b + digitSum b (n / b) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [digitSum]
  · simp [digitSum, Nat.digits_def' hb hn]

private theorem digitSum_le (b n : ℕ) : digitSum b n ≤ n := Nat.digit_sum_le b n

/-- A quotient that is at least the base loses at least `b - 1` to its digit sum. -/
private theorem digitSum_add_le {b q : ℕ} (hb : 1 < b) (hq : b ≤ q) :
    digitSum b q + (b - 1) ≤ q := by
  have hstep := digitSum_step (n := q) hb
  have hle := digitSum_le b (q / b)
  have hdiv := Nat.mod_add_div q b
  have hq1 : 1 ≤ q / b := (Nat.one_le_div_iff (by omega)).2 hq
  have hmul : q / b + (b - 1) ≤ b * (q / b) := by
    obtain ⟨k, hk⟩ : ∃ k, q / b = k + 1 := ⟨q / b - 1, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
    rw [hk, show c + 2 - 1 = c + 1 by omega]; nlinarith
  omega

/-- Below half of `n > 8`, a base gives strictly less than half of `n`. -/
private theorem two_mul_digitSum_lt {b n : ℕ} (hb : 1 < b) (h2b : 2 * b ≤ n) (hn : 8 < n) :
    2 * digitSum b n < n := by
  have hstep := digitSum_step (n := n) hb
  have hdiv := Nat.mod_add_div n b
  have hr := Nat.mod_lt n (show 0 < b by omega)
  have hq2 : 2 ≤ n / b := (Nat.le_div_iff_mul_le (by omega)).2 (by linarith)
  set q := n / b with hqdef
  set r := n % b with hrdef
  by_cases hbq : b ≤ q
  · have h := digitSum_add_le hb hbq
    have : r + 2 * q < b * q + 2 * (b - 1) := by
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
      have : r ≤ c + 1 := by omega
      rw [show c + 2 - 1 = c + 1 by omega]
      nlinarith
    omega
  · have hle := digitSum_le b q
    have hb4 : 4 ≤ b := by
      by_contra hlt
      have hb3 : b = 2 ∨ b = 3 := by omega
      rcases hb3 with rfl | rfl <;> omega
    have : r + 2 * q < b * q := by
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 4 := ⟨b - 4, by omega⟩
      have : r ≤ c + 3 := by omega
      nlinarith
    omega

/-- Above half of `n`, the base-`b` expansion of `n` is the two digits `1, n - b`. -/
private theorem digitSum_of_half_lt {b n : ℕ} (hbn : b < n) (hnb : n < 2 * b) :
    digitSum b n = n - b + 1 := by
  have hb : 1 < b := by omega
  have hq : n / b = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  have hr : n % b = n - b := by
    have := Nat.mod_add_div n b
    rw [hq] at this
    omega
  have h1 : digitSum b 1 = 1 := by
    rw [digitSum_step hb, Nat.mod_eq_of_lt hb, Nat.div_eq_of_lt hb]
    simp [digitSum]
  rw [digitSum_step hb, hq, hr, h1]

private theorem ceil_eq (n : ℕ) : ⌈((n + 1 : ℕ) : ℚ) / 2⌉₊ = n / 2 + 1 := by
  rw [Nat.ceil_eq_iff (by omega)]
  have h := Nat.div_add_mod n 2
  have hm := Nat.mod_lt n (show 0 < 2 by norm_num)
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    have : ((n / 2 + 1 - 1 : ℕ) : ℚ) = (n / 2 : ℕ) := by congr 1
    rw [this]
    have : (n / 2) * 2 < n + 1 := by omega
    exact_mod_cast this
  · rw [div_le_iff₀ (by norm_num)]
    have : n + 1 ≤ (n / 2 + 1) * 2 := by omega
    exact_mod_cast this

/-- Irvine's conjecture for OEIS A394431, as a proposition. -/
def claim : Prop :=
  ∀ n : ℕ, 8 < n → IsLeastMaxDigitSumBase n ⌈((n + 1 : ℕ) : ℚ) / 2⌉₊

/-- **Irvine's conjecture for OEIS A394431.** For every `n > 8` the smallest base in
`1 < b < n` maximizing the digit sum of `n` is `ceiling((n+1)/2)`. -/
theorem result (n : ℕ) (hn : 8 < n) :
    IsLeastMaxDigitSumBase n ⌈((n + 1 : ℕ) : ℚ) / 2⌉₊ := by
  rw [ceil_eq]
  have hv : digitSum (n / 2 + 1) n = n - (n / 2 + 1) + 1 :=
    digitSum_of_half_lt (by omega) (by omega)
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro c hc hcn
    by_cases h2c : 2 * c ≤ n
    · have := two_mul_digitSum_lt hc h2c hn
      omega
    · rw [digitSum_of_half_lt hcn (by omega)]
      omega
  · intro c hc hcb
    have := two_mul_digitSum_lt hc (by omega) hn
    omega

end D5.S1.Digit.MaxDigitSumBase
