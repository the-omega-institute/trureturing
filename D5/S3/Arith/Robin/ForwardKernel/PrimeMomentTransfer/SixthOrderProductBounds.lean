/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderProductBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderProductBounds
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Cubic product perturbations and injective sixth-order sum estimates. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartialPairingPolynomial
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.BigOperators.Ring.Nat

open scoped BigOperators
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Perturbing each factor of a product of three bounded scalars by at most one costs
at most three times the square of the common bound. -/
theorem scalar_prod_diff_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.card = 3) (f g : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, |f i| ≤ B) (hg : ∀ i ∈ s, |g i| ≤ B)
    (hd : ∀ i ∈ s, |f i - g i| ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ 3 * B ^ 2 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  have hm (x y : α) (hx : x ∈ ({a, b, c} : Finset α))
      (hy : y ∈ ({a, b, c} : Finset α)) (F G : α → ℝ)
      (hF : ∀ i ∈ ({a, b, c} : Finset α), |F i| ≤ B)
      (hG : ∀ i ∈ ({a, b, c} : Finset α), |G i| ≤ B) :
      |F x| * |G y| ≤ B ^ 2 := by
    nlinarith [mul_le_mul (hF x hx) (hG y hy) (abs_nonneg (G y)) hB]
  have ha : |(f a - g a) * f b * f c| ≤ B ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ 1 * |f b| * |f c| := by gcongr; exact hd a (by simp)
      _ ≤ B ^ 2 := by simpa using hm b c (by simp) (by simp) f f hf hf
  have hb : |g a * (f b - g b) * f c| ≤ B ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ |g a| * 1 * |f c| := by gcongr; exact hd b (by simp)
      _ ≤ B ^ 2 := by simpa using hm a c (by simp) (by simp) g f hg hf
  have hc : |g a * g b * (f c - g c)| ≤ B ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ |g a| * |g b| * 1 := by gcongr; exact hd c (by simp)
      _ ≤ B ^ 2 := by simpa using hm a b (by simp) (by simp) g g hg hg
  simp only [Finset.prod_insert (show a ∉ ({b, c} : Finset α) by simp [hab, hac]),
    Finset.prod_insert (show b ∉ ({c} : Finset α) by simp [hbc]), Finset.prod_singleton]
  have he : f a * (f b * f c) - g a * (g b * g c) =
      (f a - g a) * f b * f c + g a * (f b - g b) * f c +
        g a * g b * (f c - g c) := by ring
  rw [he]
  calc
    _ ≤ |(f a - g a) * f b * f c + g a * (f b - g b) * f c| +
        |g a * g b * (f c - g c)| := abs_add_le _ _
    _ ≤ (|(f a - g a) * f b * f c| + |g a * (f b - g b) * f c|) +
        |g a * g b * (f c - g c)| := by gcongr; exact abs_add_le _ _
    _ ≤ 3 * B ^ 2 := by linarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
