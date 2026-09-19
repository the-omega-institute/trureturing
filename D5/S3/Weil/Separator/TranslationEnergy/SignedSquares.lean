/- GID: D5/S3/Weil/Separator/TranslationEnergy/SignedSquares
   generality: G
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/SignedSquares
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Sign-safe rational square bounds accept annotated expressions and contract in width on bounded signed intervals. -/

import D5.S0.Certificates.BoxCover.RationalIntervalExpression
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.TranslationEnergy.SignedSquares

open D5.S0.Certificates.BoxCover.RationalIntervalExpression

/-- The lower endpoint is zero precisely in the genuinely crossing-sign case. -/
def squareBounds (l u : ℚ) : ℚ × ℚ :=
  (if 0 ≤ l then l ^ 2 else if u ≤ 0 then u ^ 2 else 0,
    max (l ^ 2) (u ^ 2))

def squareExpr {n : ℕ} (e : Expr n) : Expr n :=
  .square (squareBounds (bounds e).1 (bounds e).2).1
    (squareBounds (bounds e).1 (bounds e).2).2 e

/-- The exact factory supplies both checker acceptance and actual real enclosure. -/
theorem square_factory_correct {n : ℕ} (box : Fin n → ℚ × ℚ)
    (e : Expr n) (hcheck : check box e = true) :
    0 ≤ (squareBounds (bounds e).1 (bounds e).2).1 ∧
    (squareBounds (bounds e).1 (bounds e).2).1 ≤
      (squareBounds (bounds e).1 (bounds e).2).2 ∧
    check box (squareExpr e) = true ∧
    ∀ (x : Fin n → ℝ),
      (∀ i, ((box i).1 : ℝ) ≤ x i ∧ x i ≤ ((box i).2 : ℝ)) →
      ((squareBounds (bounds e).1 (bounds e).2).1 : ℝ) ≤ value x e ^ 2 ∧
      value x e ^ 2 ≤ ((squareBounds (bounds e).1 (bounds e).2).2 : ℝ) := by
  let l := (bounds e).1
  let u := (bounds e).2
  have hnonneg : 0 ≤ (squareBounds l u).1 := by
    unfold squareBounds
    split_ifs <;> positivity
  have horder : (squareBounds l u).1 ≤ (squareBounds l u).2 := by
    unfold squareBounds
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
    · exact (sq_nonneg l).trans (le_max_left _ _)
  have hguard : (squareBounds l u).1 ≤ 0 ∨
      (0 ≤ l ∧ (squareBounds l u).1 ≤ l ^ 2) ∨
      (u ≤ 0 ∧ (squareBounds l u).1 ≤ u ^ 2) := by
    unfold squareBounds
    split_ifs with hl hu
    · exact Or.inr (Or.inl ⟨hl, le_rfl⟩)
    · exact Or.inr (Or.inr ⟨hu, le_rfl⟩)
    · exact Or.inl le_rfl
  have hc : check box (squareExpr e) = true := by
    change (check box e && decide _) = true
    rw [hcheck, Bool.true_and]
    apply decide_eq_true
    exact ⟨horder, hguard, le_max_left _ _, le_max_right _ _⟩
  refine ⟨hnonneg, horder, hc, ?_⟩
  intro x hx
  exact checked_expression_encloses box x hx (squareExpr e) hc

/-- On a bounded signed interval, squaring has a width bound linear in input width.
The crossing-zero case uses both endpoint distances to zero, not products of
matching endpoints. The same estimate also bounds the output range. -/
theorem square_bounds_width_le (A l u : ℚ) (hA : 0 ≤ A)
    (hl : -A ≤ l) (hlu : l ≤ u) (hu : u ≤ A) :
    0 ≤ (squareBounds l u).1 ∧
    (squareBounds l u).1 ≤ (squareBounds l u).2 ∧
    (squareBounds l u).2 ≤ A ^ 2 ∧
    (squareBounds l u).2 - (squareBounds l u).1 ≤ 2 * A * (u - l) := by
  have hlA : l ≤ A := hlu.trans hu
  have huA : -A ≤ u := hl.trans hlu
  have hl2 := sq_le_sq' hl hlA
  have hu2 := sq_le_sq' huA hu
  have hrange : max (l ^ 2) (u ^ 2) ≤ A ^ 2 := max_le hl2 hu2
  have hw : 0 ≤ u - l := sub_nonneg.mpr hlu
  unfold squareBounds
  by_cases hp : 0 ≤ l
  · rw [if_pos hp]
    have hsq : l ^ 2 ≤ u ^ 2 := (sq_le_sq₀ hp (hp.trans hlu)).2 hlu
    rw [max_eq_right hsq]
    refine ⟨sq_nonneg l, hsq, hu2, ?_⟩
    have ht := mul_nonneg hw (show 0 ≤ 2 * A - (u + l) by linarith)
    nlinarith
  · rw [if_neg hp]
    by_cases hn : u ≤ 0
    · rw [if_pos hn]
      have hsq : u ^ 2 ≤ l ^ 2 := by
        have ht := mul_nonneg hw (show 0 ≤ -l - u by linarith)
        nlinarith
      rw [max_eq_left hsq]
      refine ⟨sq_nonneg u, hsq, hl2, ?_⟩
      have ht := mul_nonneg hw (show 0 ≤ 2 * A + l + u by linarith)
      nlinarith
    · rw [if_neg hn]
      have hl0 : l ≤ 0 := (lt_of_not_ge hp).le
      have hu0 : 0 ≤ u := (lt_of_not_ge hn).le
      have hll := mul_nonneg (show 0 ≤ -l by linarith)
        (show 0 ≤ A + l by linarith)
      have huu := mul_nonneg hu0 (show 0 ≤ A - u by linarith)
      have hau := mul_nonneg hA hu0
      have hal := mul_nonneg hA (show 0 ≤ -l by linarith)
      refine ⟨le_rfl, (sq_nonneg l).trans (le_max_left _ _), hrange, ?_⟩
      rw [sub_zero]
      apply max_le <;> nlinarith

/-- Exact subtraction uses opposite endpoint corners. -/
def differenceBounds (a b : ℚ × ℚ) : ℚ × ℚ :=
  (a.1 - b.2, a.2 - b.1)

/-- A squared difference consumer includes the endpoint algebra in its proof. -/
theorem square_difference_width_le (A a b c d : ℚ) (hA : 0 ≤ A)
    (hab : a ≤ b) (hcd : c ≤ d)
    (ha : -A ≤ a) (hb : b ≤ A) (hc : -A ≤ c) (hd : d ≤ A) :
    let v := differenceBounds (a, b) (c, d)
    0 ≤ (squareBounds v.1 v.2).1 ∧
    (squareBounds v.1 v.2).1 ≤ (squareBounds v.1 v.2).2 ∧
    (squareBounds v.1 v.2).2 ≤ (2 * A) ^ 2 ∧
    (squareBounds v.1 v.2).2 - (squareBounds v.1 v.2).1 ≤
      4 * A * ((b - a) + (d - c)) := by
  dsimp only [differenceBounds]
  have hv := square_bounds_width_le (2 * A) (a - d) (b - c)
    (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨hv.1, hv.2.1, hv.2.2.1, ?_⟩
  nlinarith [hv.2.2.2]

/-- The two square bounds sum to an exact norm-square interval. -/
def normSqBounds (p q : ℚ × ℚ) : ℚ × ℚ :=
  ((squareBounds p.1 p.2).1 + (squareBounds q.1 q.2).1,
    (squareBounds p.1 p.2).2 + (squareBounds q.1 q.2).2)

def differenceExpr {n : ℕ} (a b : Expr n) : Expr n :=
  .add (differenceBounds (bounds a) (bounds b)).1
    (differenceBounds (bounds a) (bounds b)).2 a
    (.neg (-(bounds b).2) (-(bounds b).1) b)

def normSqExpr {n : ℕ} (p q : Expr n) : Expr n :=
  .add (normSqBounds (bounds p) (bounds q)).1
    (normSqBounds (bounds p) (bounds q)).2 (squareExpr p) (squareExpr q)

/-- Two signed difference squares retain a shrinking total width. -/
theorem norm_sq_difference_width_le (Ap Aq a b c d e f g h : ℚ)
    (hAp : 0 ≤ Ap) (hAq : 0 ≤ Aq)
    (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f) (hgh : g ≤ h)
    (ha : -Ap ≤ a) (hb : b ≤ Ap) (hc : -Ap ≤ c) (hd : d ≤ Ap)
    (he : -Aq ≤ e) (hf : f ≤ Aq) (hg : -Aq ≤ g) (hh : h ≤ Aq) :
    let v := normSqBounds (differenceBounds (a, b) (c, d))
      (differenceBounds (e, f) (g, h))
    0 ≤ v.1 ∧ v.1 ≤ v.2 ∧ v.2 ≤ (2 * Ap) ^ 2 + (2 * Aq) ^ 2 ∧
    v.2 - v.1 ≤ 4 * Ap * ((b - a) + (d - c)) +
      4 * Aq * ((f - e) + (h - g)) := by
  have hp := square_difference_width_le Ap a b c d hAp hab hcd ha hb hc hd
  have hq := square_difference_width_le Aq e f g h hAq hef hgh he hf hg hh
  dsimp only [normSqBounds]
  exact ⟨add_nonneg hp.1 hq.1, add_le_add hp.2.1 hq.2.1,
    add_le_add hp.2.2.1 hq.2.2.1, by linarith [hp.2.2.2, hq.2.2.2]⟩

#print axioms square_factory_correct
#print axioms square_bounds_width_le
#print axioms square_difference_width_le
#print axioms norm_sq_difference_width_le

end D5.S3.Weil.Separator.TranslationEnergy.SignedSquares
