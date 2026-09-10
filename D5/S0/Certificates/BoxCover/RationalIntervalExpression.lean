/- GID: D5/S0/Certificates/BoxCover/RationalIntervalExpression
   generality: G
   mirror-B: D5/B/S0/Certificates/BoxCover/RationalIntervalExpression
   mirror-E: none(waiver:exact-real-enclosure-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S0/Certificates/BoxCover/CheckedRationalBoxCover.checked_forest_covers_sublevel; instance=D5/S0/Certificates/BoxCover/BoxCoverExamples.square_forest_accepted
   digest: A decidable rational endpoint checker entails enclosure of the actual real evaluation of an annotated arithmetic expression. -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
This is the numeric proof layer below FiniteSublevelCover. An untrusted
producer proposes rational endpoints at every expression node. The checker
recomputes all local arithmetic inequalities. Its soundness theorem quantifies
over REAL inputs in the input box, not merely over rational samples.

Bounds are ordinary pairs of rationals. No alternative real, interval-set,
Newton, Hadamard or root carrier is introduced. The expression language has
only the field operations and squaring used by the Cayley residual evaluator.
Division is multiplication by inv; intervals meeting zero fail the inv guard.
The checker permits outward-rounded endpoints and does not trust a producer's
floating-point result, stored PASS, hash, or root-count assertion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.BoxCover.RationalIntervalExpression

/-- Arithmetic syntax carrying proposed rational output endpoints. -/
inductive Expr (n : ℕ) where
  | input (i : Fin n) (lower upper : ℚ)
  | const (q lower upper : ℚ)
  | add (lower upper : ℚ) (left right : Expr n)
  | neg (lower upper : ℚ) (arg : Expr n)
  | mul (lower upper : ℚ) (left right : Expr n)
  | square (lower upper : ℚ) (arg : Expr n)
  | inv (lower upper : ℚ) (arg : Expr n)
  deriving DecidableEq

/-- Proposed output interval; its validity is established only by check. -/
def bounds {n : ℕ} : Expr n → ℚ × ℚ
  | .input _ l u | .const _ l u | .add l u _ _ | .neg l u _
  | .mul l u _ _ | .square l u _ | .inv l u _ => (l, u)

/-- Actual real semantics. Endpoint annotations have no effect on the value. -/
noncomputable def value {n : ℕ} (x : Fin n → ℝ) : Expr n → ℝ
  | .input i _ _ => x i
  | .const q _ _ => q
  | .add _ _ a b => value x a + value x b
  | .neg _ _ a => -value x a
  | .mul _ _ a b => value x a * value x b
  | .square _ _ a => value x a ^ 2
  | .inv _ _ a => 1 / value x a

/-- A purely rational, recursively executable certificate check. All inverse
nodes require strict same-sign denominator endpoints. Every multiplication
checks all four corners; checking only the matching endpoints is unsound. -/
def check {n : ℕ} (box : Fin n → ℚ × ℚ) : Expr n → Bool
  | .input i l u => decide (l ≤ u ∧ l ≤ (box i).1 ∧ (box i).2 ≤ u)
  | .const q l u => decide (l ≤ u ∧ l ≤ q ∧ q ≤ u)
  | .add l u a b => check box a && (check box b &&
      decide (l ≤ u ∧ l ≤ (bounds a).1 + (bounds b).1 ∧
        (bounds a).2 + (bounds b).2 ≤ u))
  | .neg l u a => check box a &&
      decide (l ≤ u ∧ l ≤ -(bounds a).2 ∧ -(bounds a).1 ≤ u)
  | .mul l u a b => check box a && (check box b && decide
      (l ≤ u ∧
       l ≤ (bounds a).1 * (bounds b).1 ∧
       l ≤ (bounds a).1 * (bounds b).2 ∧
       l ≤ (bounds a).2 * (bounds b).1 ∧
       l ≤ (bounds a).2 * (bounds b).2 ∧
       (bounds a).1 * (bounds b).1 ≤ u ∧
       (bounds a).1 * (bounds b).2 ≤ u ∧
       (bounds a).2 * (bounds b).1 ≤ u ∧
       (bounds a).2 * (bounds b).2 ≤ u))
  | .square l u a => check box a && decide
      (l ≤ u ∧
       (l ≤ 0 ∨ (0 ≤ (bounds a).1 ∧ l ≤ (bounds a).1 ^ 2) ∨
         ((bounds a).2 ≤ 0 ∧ l ≤ (bounds a).2 ^ 2)) ∧
       (bounds a).1 ^ 2 ≤ u ∧ (bounds a).2 ^ 2 ≤ u)
  | .inv l u a => check box a && decide
      (l ≤ u ∧ ((bounds a).2 < 0 ∨ 0 < (bounds a).1) ∧
       l ≤ 1 / (bounds a).2 ∧ 1 / (bounds a).1 ≤ u)

private theorem linear_bounds (c a b l u x : ℝ)
    (hx : a ≤ x ∧ x ≤ b)
    (hla : l ≤ c * a) (hlb : l ≤ c * b)
    (hua : c * a ≤ u) (hub : c * b ≤ u) :
    l ≤ c * x ∧ c * x ≤ u := by
  by_cases hc : 0 ≤ c
  · exact ⟨hla.trans (mul_le_mul_of_nonneg_left hx.1 hc),
      (mul_le_mul_of_nonneg_left hx.2 hc).trans hub⟩
  · exact ⟨hlb.trans (mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge hc)),
      (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hc)).trans hua⟩

private theorem product_bounds (a b c d l u x y : ℝ)
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hlac : l ≤ a * c) (hlad : l ≤ a * d)
    (hlbc : l ≤ b * c) (hlbd : l ≤ b * d)
    (huac : a * c ≤ u) (huad : a * d ≤ u)
    (hubc : b * c ≤ u) (hubd : b * d ≤ u) :
    l ≤ x * y ∧ x * y ≤ u := by
  have hc := linear_bounds c a b l u x hx
    (by simpa only [mul_comm] using hlac)
    (by simpa only [mul_comm] using hlbc)
    (by simpa only [mul_comm] using huac)
    (by simpa only [mul_comm] using hubc)
  have hd := linear_bounds d a b l u x hx
    (by simpa only [mul_comm] using hlad)
    (by simpa only [mul_comm] using hlbd)
    (by simpa only [mul_comm] using huad)
    (by simpa only [mul_comm] using hubd)
  apply linear_bounds x c d l u y hy
  · simpa only [mul_comm] using hc.1
  · simpa only [mul_comm] using hd.1
  · simpa only [mul_comm] using hc.2
  · simpa only [mul_comm] using hd.2

private theorem square_bounds (a b l u x : ℝ)
    (hx : a ≤ x ∧ x ≤ b)
    (hl : l ≤ 0 ∨ (0 ≤ a ∧ l ≤ a ^ 2) ∨ (b ≤ 0 ∧ l ≤ b ^ 2))
    (ha : a ^ 2 ≤ u) (hb : b ^ 2 ≤ u) :
    l ≤ x ^ 2 ∧ x ^ 2 ≤ u := by
  constructor
  · rcases hl with hl | ⟨ha0, hl⟩ | ⟨hb0, hl⟩
    · exact hl.trans (sq_nonneg x)
    · have hprod := mul_nonneg (sub_nonneg.mpr hx.1)
        (add_nonneg (ha0.trans hx.1) ha0)
      nlinarith
    · have hfirst : 0 ≤ b - x := sub_nonneg.mpr hx.2
      have hsecond : 0 ≤ -b - x := by linarith
      nlinarith [mul_nonneg hfirst hsecond]
  · by_cases hpos : 0 ≤ x
    · have hb0 : 0 ≤ b := hpos.trans hx.2
      have hprod := mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hb0 hpos)
      nlinarith
    · have hfirst : 0 ≤ x - a := sub_nonneg.mpr hx.1
      have hsecond : 0 ≤ -x - a := by linarith
      nlinarith [mul_nonneg hfirst hsecond]

private theorem reciprocal_bounds (a b x : ℝ)
    (hx : a ≤ x ∧ x ≤ b) (haway : b < 0 ∨ 0 < a) :
    1 / b ≤ 1 / x ∧ 1 / x ≤ 1 / a := by
  rcases haway with hb | ha
  · have hxneg : x < 0 := lt_of_le_of_lt hx.2 hb
    have h1 := one_div_le_one_div_of_le (neg_pos.mpr hb) (neg_le_neg hx.2)
    have h2 := one_div_le_one_div_of_le (neg_pos.mpr hxneg) (neg_le_neg hx.1)
    constructor
    · simpa only [one_div, inv_neg, neg_neg] using neg_le_neg h1
    · simpa only [one_div, inv_neg, neg_neg] using neg_le_neg h2
  · exact ⟨one_div_le_one_div_of_le (lt_of_lt_of_le ha hx.1) hx.2,
      one_div_le_one_div_of_le ha hx.1⟩

/-- Acceptance entails enclosure for every REAL input in the input box.
All local bounds are derived from rational comparisons, never assumed as a
real-valued enclosure oracle. In particular, inv acceptance rules out zero
before using reciprocal monotonicity. This theorem is the numeric premise
supplier for the separate proof-carrying finite coverage-tree owner. -/
theorem checked_expression_encloses {n : ℕ}
    (box : Fin n → ℚ × ℚ) (x : Fin n → ℝ)
    (hx : ∀ i, ((box i).1 : ℝ) ≤ x i ∧ x i ≤ ((box i).2 : ℝ))
    (e : Expr n) (hcheck : check box e = true) :
    ((bounds e).1 : ℝ) ≤ value x e ∧ value x e ≤ ((bounds e).2 : ℝ) := by
  revert hcheck
  induction e with
  | input i l u =>
    intro hcheck
    have h := of_decide_eq_true hcheck
    change (l : ℝ) ≤ x i ∧ x i ≤ (u : ℝ)
    have hl : (l : ℝ) ≤ ((box i).1 : ℝ) := by exact_mod_cast h.2.1
    have hu : ((box i).2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast h.2.2
    exact ⟨hl.trans (hx i).1, (hx i).2.trans hu⟩
  | const q l u =>
    intro hcheck
    have h := of_decide_eq_true hcheck
    change (l : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (u : ℝ)
    constructor
    · exact_mod_cast h.2.1
    · exact_mod_cast h.2.2
  | add l u a b iha ihb =>
    intro hcheck
    have hc := Bool.and_eq_true_iff.mp hcheck
    have hd := Bool.and_eq_true_iff.mp hc.2
    have h := of_decide_eq_true hd.2
    have ha := iha hc.1
    have hb := ihb hd.1
    have hl : (l : ℝ) ≤ ((bounds a).1 : ℝ) + ((bounds b).1 : ℝ) := by
      exact_mod_cast h.2.1
    have hu : ((bounds a).2 : ℝ) + ((bounds b).2 : ℝ) ≤ (u : ℝ) := by
      exact_mod_cast h.2.2
    change (l : ℝ) ≤ value x a + value x b ∧ value x a + value x b ≤ (u : ℝ)
    exact ⟨hl.trans (add_le_add ha.1 hb.1), (add_le_add ha.2 hb.2).trans hu⟩
  | neg l u a iha =>
    intro hcheck
    have hc := Bool.and_eq_true_iff.mp hcheck
    have h := of_decide_eq_true hc.2
    have ha := iha hc.1
    have hl : (l : ℝ) ≤ -((bounds a).2 : ℝ) := by exact_mod_cast h.2.1
    have hu : -((bounds a).1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast h.2.2
    change (l : ℝ) ≤ -value x a ∧ -value x a ≤ (u : ℝ)
    exact ⟨hl.trans (neg_le_neg ha.2), (neg_le_neg ha.1).trans hu⟩
  | mul l u a b iha ihb =>
    intro hcheck
    have hc := Bool.and_eq_true_iff.mp hcheck
    have hd := Bool.and_eq_true_iff.mp hc.2
    rcases of_decide_eq_true hd.2 with
      ⟨_, hll, hlh, hhl, hhh, hll', hlh', hhl', hhh'⟩
    change (l : ℝ) ≤ value x a * value x b ∧ value x a * value x b ≤ (u : ℝ)
    apply product_bounds
      ((bounds a).1 : ℝ) ((bounds a).2 : ℝ)
      ((bounds b).1 : ℝ) ((bounds b).2 : ℝ) (l : ℝ) (u : ℝ)
      (value x a) (value x b) (iha hc.1) (ihb hd.1)
    · exact_mod_cast hll
    · exact_mod_cast hlh
    · exact_mod_cast hhl
    · exact_mod_cast hhh
    · exact_mod_cast hll'
    · exact_mod_cast hlh'
    · exact_mod_cast hhl'
    · exact_mod_cast hhh'
  | square l u a iha =>
    intro hcheck
    have hc := Bool.and_eq_true_iff.mp hcheck
    rcases of_decide_eq_true hc.2 with ⟨_, hl, hla, hua⟩
    change (l : ℝ) ≤ value x a ^ 2 ∧ value x a ^ 2 ≤ (u : ℝ)
    apply square_bounds ((bounds a).1 : ℝ) ((bounds a).2 : ℝ)
      (l : ℝ) (u : ℝ) (value x a) (iha hc.1)
    · rcases hl with hz | ⟨hp, hv⟩ | ⟨hn, hv⟩
      · left; exact_mod_cast hz
      · right; left
        constructor
        · exact_mod_cast hp
        · exact_mod_cast hv
      · right; right
        constructor
        · exact_mod_cast hn
        · exact_mod_cast hv
    · exact_mod_cast hla
    · exact_mod_cast hua
  | inv l u a iha =>
    intro hcheck
    have hc := Bool.and_eq_true_iff.mp hcheck
    rcases of_decide_eq_true hc.2 with ⟨_, hsign, hl, hu⟩
    have hsign' : ((bounds a).2 : ℝ) < 0 ∨ 0 < ((bounds a).1 : ℝ) := by
      rcases hsign with hneg | hpos
      · left; exact_mod_cast hneg
      · right; exact_mod_cast hpos
    have hb := reciprocal_bounds ((bounds a).1 : ℝ) ((bounds a).2 : ℝ)
      (value x a) (iha hc.1) hsign'
    have hl' : (l : ℝ) ≤ 1 / ((bounds a).2 : ℝ) := by exact_mod_cast hl
    have hu' : 1 / ((bounds a).1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
    change (l : ℝ) ≤ 1 / value x a ∧ 1 / value x a ≤ (u : ℝ)
    exact ⟨hl'.trans hb.1, hb.2.trans hu'⟩

#print axioms checked_expression_encloses

end D5.S0.Certificates.BoxCover.RationalIntervalExpression
