/- GID: D5/S3/Weil/Separator/TranslationEnergy/Polynomial/ProductIntervals
   generality: G
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Polynomial/ProductIntervals
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Four signed corners bound the product interval and its width. -/

import D5.S0.Certificates.BoxCover.RationalIntervalExpression
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.TranslationEnergy.Polynomial

def productLower (a b c d : Rat) : Rat :=
  min (min (a * c) (a * d)) (min (b * c) (b * d))

def productUpper (a b c d : Rat) : Rat :=
  max (max (a * c) (a * d)) (max (b * c) (b * d))

theorem product_width (a b c d A B : Rat)
    (hab : a ≤ b) (hcd : c ≤ d)
    (ha : |a| ≤ B) (hb : |b| ≤ B)
    (hc : |c| ≤ A) (hd : |d| ≤ A)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    -B * A ≤ productLower a b c d ∧
    productUpper a b c d ≤ B * A ∧
    productUpper a b c d - productLower a b c d ≤
      B * (d - c) + A * (b - a) := by
  let W : Rat := B * (d - c) + A * (b - a)
  have bound (x y : Rat) (hx : |x| ≤ B) (hy : |y| ≤ A) :
      -B * A ≤ x * y ∧ x * y ≤ B * A := by
    have h := mul_le_mul hx hy (abs_nonneg _) hB
    have hxy : |x * y| ≤ B * A := by
      calc |x * y| = |x| * |y| := abs_mul x y
        _ ≤ B * A := h
    constructor <;> have := abs_le.mp hxy <;> nlinarith
  have h₁ := bound a c ha hc
  have h₂ := bound a d ha hd
  have h₃ := bound b c hb hc
  have h₄ := bound b d hb hd
  have hlower : -B * A ≤ productLower a b c d :=
    le_min (le_min h₁.1 h₂.1) (le_min h₃.1 h₄.1)
  have hupper : productUpper a b c d ≤ B * A :=
    max_le (max_le h₁.2 h₂.2) (max_le h₃.2 h₄.2)
  have pair (x y u v : Rat)
      (hx : x = a ∨ x = b) (hy : y = c ∨ y = d)
      (hu : u = a ∨ u = b) (hv : v = c ∨ v = d) :
      x * y ≤ u * v + W := by
    have hxB : |x| ≤ B := by rcases hx with rfl | rfl <;> assumption
    have hvA : |v| ≤ A := by rcases hv with rfl | rfl <;> assumption
    have hxu : |x - u| ≤ b - a := by
      apply abs_le.mpr
      rcases hx with rfl | rfl <;> rcases hu with rfl | rfl <;>
        constructor <;> linarith
    have hyv : |y - v| ≤ d - c := by
      apply abs_le.mpr
      rcases hy with rfl | rfl <;> rcases hv with rfl | rfl <;>
        constructor <;> linarith
    have hprod₁ : |x| * |y - v| ≤ B * (d - c) :=
      mul_le_mul hxB hyv (abs_nonneg _) hB
    have hprod₂ : |v| * |x - u| ≤ A * (b - a) :=
      mul_le_mul hvA hxu (abs_nonneg _) hA
    have hdiff : x * y - u * v = x * (y - v) + (x - u) * v := by ring
    have hbound : |x * y - u * v| ≤ W := by
      calc
        |x * y - u * v| = |x * (y - v) + (x - u) * v| := congrArg abs hdiff
        _ ≤ |x * (y - v)| + |(x - u) * v| := abs_add_le _ _
        _ = |x| * |y - v| + |v| * |x - u| := by rw [abs_mul, abs_mul]; ring
        _ ≤ W := by dsimp [W]; linarith
    have := (abs_le.mp hbound).2
    linarith
  have spread : productUpper a b c d ≤ productLower a b c d + W := by
    simp only [productUpper, productLower, max_def, min_def]
    split_ifs
    all_goals apply pair <;> simp
  dsimp [W] at spread
  exact ⟨hlower, hupper, by linarith⟩

end D5.S3.Weil.Separator.TranslationEnergy.Polynomial
