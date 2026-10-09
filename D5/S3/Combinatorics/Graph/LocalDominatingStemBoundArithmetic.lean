/- GID: D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Rat.Cast.Order]
   utility: none
   digest: Finite replication bounds force equal counting bases and strict mean inequalities. -/

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LocalDominatingStemBoundArithmetic

/-- The first three binomial terms give a uniform lower bound for positive increments. -/
private theorem quadratic_binomial_bound (x : ℚ) (hx : 0 ≤ x) (r : ℕ) :
    1 + r * x + (r : ℚ) * (r - 1) * x ^ 2 / 2 ≤ (1 + x) ^ r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have hn : 0 ≤ (r : ℚ) * (r - 1) := by
      cases r with
      | zero => norm_num
      | succ k =>
        simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        positivity
    have hm := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1 + x by linarith)
    have hc := mul_nonneg hn (pow_nonneg hx 3)
    calc
      _ ≤ (1 + r * x + (r : ℚ) * (r - 1) * x ^ 2 / 2) * (1 + x) := by
        push_cast
        nlinarith
      _ ≤ (1 + x) ^ r * (1 + x) := hm
      _ = (1 + x) ^ (r + 1) := (pow_succ _ r).symm

/-- The specified replication count already contradicts a linear upper envelope. -/
theorem replication_obstruction (a b h : ℕ) (hb : 0 < b) (hab : b < a) :
    ¬ ((a : ℚ) ^ (4 * h * b ^ 2 + 2) ≤
      (b : ℚ) ^ (4 * h * b ^ 2 + 2) *
        (1 + 2 * (4 * h * b ^ 2 + 2 : ℕ) * h)) := by
  intro hupper
  let r := 4 * h * b ^ 2 + 2
  have hbq : 0 < (b : ℚ) := by exact_mod_cast hb
  have hbne : (b : ℚ) ≠ 0 := ne_of_gt hbq
  have hr : (r : ℚ) = 4 * h * (b : ℚ) ^ 2 + 2 := by
    dsimp [r]
    push_cast
    rfl
  have hrpos : 0 < (r : ℚ) := by rw [hr]; positivity
  have hstep : (b : ℚ) + 1 ≤ a := by exact_mod_cast hab
  have hbase : 1 + 1 / (b : ℚ) ≤ (a : ℚ) / b := by
    apply (le_div_iff₀ hbq).2
    field_simp
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 1 / (b : ℚ)) hbase r
  have hquad := quadratic_binomial_bound (1 / (b : ℚ)) (by positivity) r
  have hquot : ((a : ℚ) / b) ^ r ≤ 1 + 2 * (r : ℚ) * h := by
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos hbq r)).2
    simpa only [r, mul_comm] using hupper
  have hexcess :
      1 + r * (1 / (b : ℚ)) + (r : ℚ) * (r - 1) * (1 / (b : ℚ)) ^ 2 / 2 =
      1 + 2 * (r : ℚ) * h + r / b + r / (2 * (b : ℚ) ^ 2) := by
    rw [hr]
    field_simp
    ring
  have hstrict : 1 + 2 * (r : ℚ) * h <
      1 + r * (1 / (b : ℚ)) + (r : ℚ) * (r - 1) * (1 / (b : ℚ)) ^ 2 / 2 := by
    rw [hexcess]
    have : 0 < (r : ℚ) / b := div_pos hrpos hbq
    have : 0 < (r : ℚ) / (2 * (b : ℚ) ^ 2) := by positivity
    linarith
  exact (not_lt_of_ge (hquad.trans (hp.trans hquot))) hstrict

/-- A counting-base ratio with a linear upper bound at every replication count is at most one. -/
theorem counting_base_le (a b h : ℕ) (hb : 0 < b)
    (hupper : ∀ r : ℕ, (a : ℚ) ^ r ≤ (b : ℚ) ^ r * (1 + 2 * (r : ℚ) * h)) :
    a ≤ b := by
  by_contra hab
  exact replication_obstruction a b h hb (Nat.lt_of_not_ge hab)
    (hupper (4 * h * b ^ 2 + 2))

/-- Replicated global bounds force strictness when the relaxed family is larger. -/
theorem replicated_mean_lt (a b h : ℕ) (α β : ℚ) (hb : 0 < b)
    (hab : b < a) (hβ : 0 ≤ β)
    (hglobal : ∀ r : ℕ,
      (a : ℚ) ^ r * (1 + 6 * (r : ℚ) * (α - 2 * h / 3)) ≤
        (b : ℚ) ^ r * (1 + 3 * (r : ℚ) * (2 * h / 3 - β))) :
    α < 2 * h / 3 := by
  by_contra hα
  have hα' : 2 * (h : ℚ) / 3 ≤ α := le_of_not_gt hα
  have hupper : ∀ r : ℕ,
      (a : ℚ) ^ r ≤ (b : ℚ) ^ r * (1 + 2 * (r : ℚ) * h) := by
    intro r
    have ha : 0 ≤ (a : ℚ) ^ r := by positivity
    have hb' : 0 ≤ (b : ℚ) ^ r := by positivity
    have hl : 0 ≤ 6 * (r : ℚ) * (α - 2 * h / 3) := by positivity
    have hleft := mul_le_mul_of_nonneg_left (show
      (1 : ℚ) ≤ 1 + 6 * (r : ℚ) * (α - 2 * h / 3) by linarith) ha
    have hright := mul_le_mul_of_nonneg_left (show
      1 + 3 * (r : ℚ) * (2 * h / 3 - β) ≤ 1 + 2 * (r : ℚ) * h by
        nlinarith [mul_nonneg (show 0 ≤ (r : ℚ) by positivity) hβ]) hb'
    simpa only [mul_one] using hleft.trans ((hglobal r).trans hright)
  exact (Nat.not_lt_of_ge (counting_base_le a b h hb hupper)) hab

/-- Comparison with the internal dominating family also identifies the counting equality case. -/
theorem relaxed_mean_bound (a b h : ℕ) (α β : ℚ) (hb : 0 < b)
    (hab : b ≤ a) (hβzero : 0 ≤ β) (hβbound : β ≤ 2 * h / 3)
    (hsame : a = b → α = β)
    (hglobal : ∀ r : ℕ,
      (a : ℚ) ^ r * (1 + 6 * (r : ℚ) * (α - 2 * h / 3)) ≤
        (b : ℚ) ^ r * (1 + 3 * (r : ℚ) * (2 * h / 3 - β))) :
    α ≤ 2 * h / 3 ∧ (α = 2 * h / 3 → a = b) := by
  by_cases heq : a = b
  · exact ⟨hsame heq ▸ hβbound, fun _ => heq⟩
  · have hlt := replicated_mean_lt a b h α β hb (lt_of_le_of_ne hab (Ne.symm heq))
      hβzero hglobal
    exact ⟨hlt.le, fun hc => False.elim ((ne_of_lt hlt) hc)⟩

/-- The stem split has the conjectured upper bound, and numerical equality is rigid. -/
theorem stem_split_bound (n l h : ℕ) (α : ℚ) (hsize : n = h + l + 1)
    (hl : 1 ≤ l) (hα : α ≤ 2 * h / 3) :
    1 + (l : ℚ) / 2 + α ≤ (4 * n + 1) / 6 ∧
      (1 + (l : ℚ) / 2 + α = (4 * n + 1) / 6 ↔
        l = 1 ∧ α = 2 * h / 3) := by
  have hlq : (1 : ℚ) ≤ l := by exact_mod_cast hl
  have hn : (n : ℚ) = h + l + 1 := by exact_mod_cast hsize
  refine ⟨by linarith, ?_⟩
  constructor
  · intro heq
    have hlone : (l : ℚ) = 1 := by linarith
    refine ⟨by exact_mod_cast hlone, ?_⟩
    linarith
  · rintro ⟨rfl, heq⟩
    norm_num at hn ⊢
    linarith

end D5.S3.Combinatorics.Graph.LocalDominatingStemBoundArithmetic
