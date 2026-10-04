/- GID: D5/S3/Combinatorics/Apwenian/GuoHanBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apwenian/GuoHanBlocks
   mirror-E: none(waiver:elementary-block-induction)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Equal actual letters have equal iterated blocks; even parity determines the sequence. -/

import D5.S3.Combinatorics.Apwenian.GuoHanDefs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Apwenian.GuoHan

open GuoHanDefs

/-- Equality of actual letters propagates through every substitution iterate. -/
theorem equal_blocks (p : ℕ) (hp : 0 < p) (σ : ℕ → Fin p → ℕ) (a : ℕ → ℕ)
    (hfix : ∀ n (r : Fin p), a (n * p + r) = σ (a n) r)
    (t n m : ℕ) (hnm : a n = a m) :
    ∀ j < p ^ t, a (n * p ^ t + j) = a (m * p ^ t + j) := by
  induction t generalizing n m with
  | zero =>
      intro j hj
      have : j = 0 := by simpa using hj
      simpa [this] using hnm
  | succ t ih =>
      intro j hj
      have hjq : j / p < p ^ t := by
        apply (Nat.div_lt_iff_lt_mul hp).2
        simpa [pow_succ] using hj
      have hjr : j % p < p := Nat.mod_lt _ hp
      have he := ih n m hnm (j / p) hjq
      have hn : n * p ^ (t + 1) + j =
          (n * p ^ t + j / p) * p + j % p := by
        rw [pow_succ]
        have := Nat.mod_add_div j p
        nlinarith
      have hm : m * p ^ (t + 1) + j =
          (m * p ^ t + j / p) * p + j % p := by
        rw [pow_succ]
        have := Nat.mod_add_div j p
        nlinarith
      rw [hn, hm, hfix _ ⟨j % p, hjr⟩, hfix _ ⟨j % p, hjr⟩, he]

/-- Strong induction identifies an apwenian parity sequence once all even positions are one. -/
theorem identify_parity (b : ℕ → ZMod 2)
    (hrec : ∀ n, b n = b (2 * n + 1) + b (2 * n + 2))
    (heven : ∀ n, b (2 * n) = 1) :
    ∀ n, b n = (periodDoubling n : ZMod 2) := by
  have hbound (n : ℕ) : periodDoubling n ≤ 1 := by
    rw [periodDoubling]
    split_ifs <;> omega
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [periodDoubling]
      split_ifs with hn
      · have haddr : n = 2 * (n / 2) := by omega
        rw [haddr, heven]
        rfl
      · have haddr : n = 2 * (n / 2) + 1 := by omega
        have hchild : 2 * (n / 2) + 2 = 2 * (n / 2 + 1) := by omega
        have hr := hrec (n / 2)
        rw [← haddr, hchild, heven, ih (n / 2) (by omega)] at hr
        have hb := hbound (n / 2)
        interval_cases hv : periodDoubling (n / 2) <;> simp at hr ⊢
        · have hc := eq_neg_of_add_eq_zero_left hr.symm
          exact hc
        · exact hr

end D5.S3.Combinatorics.Apwenian.GuoHan
