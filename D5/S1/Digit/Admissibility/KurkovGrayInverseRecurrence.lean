/- GID: D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/KurkovGrayInverseRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Hanna's inverse Gray code satisfies Kurkov's highest-bit recurrence. -/
import D5.S1.Digit.Admissibility.GrayCodeBinaryRecurrenceClosedForm
import Mathlib.Data.Nat.Log

/-!
# Kurkov's inverse Gray-code recurrence for OEIS A006068

The definition of `a` is Hanna's XOR-prefix formula written as the recursion
`n XOR a(n/2)`, terminating at zero. The first clause of `result` is the OEIS
%N property, "a(n) is Gray-coded into n", using the imported frozen `gray`.
The remaining clauses prove the zero boundary and Kurkov's 2023 recurrence.

For positive inputs, `msb` is A053644; at zero this totalized formula is 1,
whereas A053644(0) is 0. All uses of `msb` in the positive recurrence have
positive arguments. Natural subtraction is truncated and division is floor
division. `complementSecondBit` is A063946, with its two arithmetic %F cases
proved and used locally inside `result`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.Admissibility.KurkovGrayInverseRecurrence

open D5.S1.Digit.Admissibility.GrayCodeBinaryRecurrenceClosedForm (gray)

/-- Hanna's XOR-prefix definition of the inverse Gray-code sequence A006068. -/
def a (n : ℕ) : ℕ :=
  if _h : n = 0 then 0 else n ^^^ a (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _h) (by decide)

/-- Most significant bit A053644 on positive inputs; this formula gives 1 at zero. -/
def msb (n : ℕ) : ℕ := 2 ^ Nat.log 2 n

/-- A063946: complement the second bit from the left, fixing zero and one. -/
def complementSecondBit (n : ℕ) : ℕ :=
  if n < 2 then n else n ^^^ 2 ^ (Nat.log 2 n - 1)

/-- Hanna's inverse property and Kurkov's highest-bit recurrence, with the zero boundary. -/
theorem result :
    (∀ n : ℕ, gray (a n) = n) ∧ a 0 = 0 ∧
    ∀ n : ℕ, 0 < n →
      a n = a (complementSecondBit n - msb (complementSecondBit n)) + msb n := by
  have hzero : a 0 = 0 := by rw [a]; simp
  have hrec (n : ℕ) : a n = n ^^^ a (n / 2) := by
    by_cases hn : n = 0
    · subst n; simp [hzero]
    · rw [a, dif_neg hn]
  have hdiv (n : ℕ) : a n / 2 = a (n / 2) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n; simp [hzero]
      · rw [hrec n, Nat.xor_div_two,
          ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)),
          ← hrec (n / 2)]
  have hright (n : ℕ) : gray (a n) = n := by
    simp only [gray, hdiv]
    rw [hrec n, Nat.xor_xor_cancel_right]
  have hleft (n : ℕ) : a (gray n) = n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n; simpa [gray] using hzero
      · have hg : gray n / 2 = gray (n / 2) := by
          simp only [gray, Nat.xor_div_two]
        rw [hrec (gray n), hg,
          ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
        simp only [gray, Nat.xor_xor_cancel_right]
  have hbound (k n : ℕ) (hn : n < 2 ^ k) : a n < 2 ^ k := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hz : n = 0
      · subst n; simpa [hzero] using Nat.two_pow_pos k
      · rw [hrec n]
        have hd : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide)
        exact Nat.xor_lt_two_pow hn (ih (n / 2) hd (lt_trans hd hn))
  have hxor_add (k x : ℕ) (hx : x < 2 ^ k) : x ^^^ 2 ^ k = x + 2 ^ k := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← Nat.or_two_pow_eq_add_of_lt hx, Nat.testBit_xor, Nat.testBit_or,
      Nat.testBit_two_pow]
    by_cases hi : k = i
    · subst i; simp [Nat.testBit_lt_two_pow hx]
    · simp [hi]
  have htoggle_add (k n : ℕ) (hlo : 2 * 2 ^ k ≤ n) (hhi : n < 3 * 2 ^ k) :
      n ^^^ 2 ^ k = n + 2 ^ k := by
    let r := n - 2 * 2 ^ k
    have hr : r < 2 ^ k := by dsimp [r]; omega
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by simp [pow_succ, Nat.mul_comm]
    have hr' : r < 2 ^ (k + 1) := by rw [hp]; omega
    have heq : n = r + 2 ^ (k + 1) := by dsimp [r]; rw [hp]; omega
    calc
      n ^^^ 2 ^ k = (r ^^^ 2 ^ (k + 1)) ^^^ 2 ^ k := by
        rw [hxor_add (k + 1) r hr', ← heq]
      _ = (r ^^^ 2 ^ k) ^^^ 2 ^ (k + 1) := by ac_rfl
      _ = (r + 2 ^ k) + 2 ^ (k + 1) := by
        rw [hxor_add k r hr, hxor_add (k + 1) (r + 2 ^ k) (by rw [hp]; omega)]
      _ = n + 2 ^ k := by omega
  have hcases (k n : ℕ) :
      (2 * 2 ^ k ≤ n → n < 3 * 2 ^ k → complementSecondBit n = n + 2 ^ k) ∧
      (3 * 2 ^ k ≤ n → n < 4 * 2 ^ k → complementSecondBit n = n - 2 ^ k) := by
    have hp0 : 0 < 2 ^ k := Nat.two_pow_pos k
    have hp2 : 2 ^ (k + 1) = 2 * 2 ^ k := by simp [pow_succ, Nat.mul_comm]
    have hp4 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by rw [pow_succ, hp2]; omega
    have hc (hlo : 2 * 2 ^ k ≤ n) (hhi : n < 4 * 2 ^ k) :
        complementSecondBit n = n ^^^ 2 ^ k := by
      have hlog : Nat.log 2 n = k + 1 :=
        Nat.log_eq_of_pow_le_of_lt_pow (by rw [hp2]; exact hlo)
          (by rw [hp4]; exact hhi)
      simp only [complementSecondBit, if_neg (show ¬n < 2 by omega), hlog,
        Nat.add_sub_cancel]
    constructor
    · intro hlo hhi
      rw [hc hlo (by omega)]
      exact htoggle_add k n hlo hhi
    · intro hlo hhi
      rw [hc (by omega) hhi]
      have ht := htoggle_add k (n - 2 ^ k) (by omega) (by omega)
      have hn : n - 2 ^ k + 2 ^ k = n := by omega
      rw [hn] at ht
      calc
        n ^^^ 2 ^ k = (n - 2 ^ k ^^^ 2 ^ k) ^^^ 2 ^ k :=
          congrArg (fun x => x ^^^ 2 ^ k) ht.symm
        _ = n - 2 ^ k := Nat.xor_xor_cancel_right _ _
  refine ⟨hright, hzero, ?_⟩
  intro n hn
  by_cases hsmall : n < 2
  · have hn1 : n = 1 := by omega
    subst n
    have hone : a 1 = 1 := by rw [hrec]; simp [hzero]
    simp [complementSecondBit, msb, Nat.log_one_right, hzero, hone]
  · let k := Nat.log 2 n - 1
    have hk : Nat.log 2 n = k + 1 := by
      have := Nat.log_pos (by decide : 1 < 2) (show 2 ≤ n by omega)
      dsimp [k]
      omega
    have hp2 : 2 ^ (k + 1) = 2 * 2 ^ k := by simp [pow_succ, Nat.mul_comm]
    have hp4 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by rw [pow_succ, hp2]; omega
    have hlo : 2 * 2 ^ k ≤ n := by
      have h := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
      rwa [hk, hp2] at h
    have hhi : n < 4 * 2 ^ k := by
      have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
      rwa [hk, Nat.succ_eq_add_one, hp4] at h
    let c := complementSecondBit n
    have hc_bounds : 2 * 2 ^ k ≤ c ∧ c < 4 * 2 ^ k := by
      dsimp [c]
      by_cases ht : n < 3 * 2 ^ k
      · rw [(hcases k n).1 hlo ht]
        omega
      · rw [(hcases k n).2 (by omega) hhi]
        omega
    have hclog : Nat.log 2 c = k + 1 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by rw [hp2]; exact hc_bounds.1)
        (by rw [hp4]; exact hc_bounds.2)
    have hm : msb n = 2 ^ (k + 1) := by simp only [msb, hk]
    have hmc : msb c = 2 ^ (k + 1) := by simp only [msb, hclog]
    have hcxor : c = n ^^^ 2 ^ k := by
      dsimp [c]
      simp only [complementSecondBit, if_neg hsmall, hk, Nat.add_sub_cancel]
    let s := c - 2 ^ (k + 1)
    have hs : s < 2 ^ (k + 1) := by dsimp [s]; rw [hp2]; omega
    have hsadd : s + 2 ^ (k + 1) = c := by dsimp [s]; rw [hp2]; omega
    have hpowdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by simp [pow_succ]
    have hg : gray (a s + 2 ^ (k + 1)) = n := by
      calc
        gray (a s + 2 ^ (k + 1)) = gray (a s ^^^ 2 ^ (k + 1)) := by
          rw [hxor_add (k + 1) (a s) (hbound (k + 1) s hs)]
        _ = gray (a s) ^^^ gray (2 ^ (k + 1)) := by
          simp only [gray, Nat.xor_div_two]
          ac_rfl
        _ = s ^^^ (2 ^ (k + 1) ^^^ 2 ^ k) := by
          rw [hright]
          simp only [gray, hpowdiv]
        _ = (s ^^^ 2 ^ (k + 1)) ^^^ 2 ^ k := by rw [Nat.xor_assoc]
        _ = c ^^^ 2 ^ k := by rw [hxor_add (k + 1) s hs, hsadd]
        _ = n := by rw [hcxor, Nat.xor_xor_cancel_right]
    change a n = a (c - msb c) + msb n
    rw [hm, hmc]
    change a n = a s + 2 ^ (k + 1)
    calc
      a n = a (gray (a s + 2 ^ (k + 1))) := congrArg a hg.symm
      _ = a s + 2 ^ (k + 1) := hleft _

#print axioms result

end D5.S1.Digit.Admissibility.KurkovGrayInverseRecurrence
