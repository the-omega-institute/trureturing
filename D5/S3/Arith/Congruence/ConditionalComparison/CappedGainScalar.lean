/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainScalar
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Rational scalar part of the capped-gain lift. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainScalar.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGain
import Mathlib.Analysis.Convex.Function

/-!
# Rational scalar part of the capped-gain lift

The threshold join is proved by exact supporting-line inequalities. No
derivatives, limits, or real-valued probability laws are used.
-/

namespace Erdos7.CappedGain

/-- The part of the lift that varies with the current load, up to a constant. -/
def loadPart (q t A x : ℚ) : ℚ :=
  if x ≤ t then A / (q - x) else (x - t) / (q - t) + A / (q - t)

/-- A supporting slope, including the right-hand slope at the threshold. -/
def loadSlope (q t A x : ℚ) : ℚ :=
  if x ≤ t then A / (q - x) ^ 2 else 1 / (q - t)

theorem reciprocal_support {q t A x y : ℚ} (hqt : t < q) (hA : 0 ≤ A)
    (hx : x ≤ t) (hy : y ≤ t) :
    A / (q - x) + (A / (q - x) ^ 2) * (y - x) ≤ A / (q - y) := by
  have hdx : 0 < q - x := by linarith
  have hdy : 0 < q - y := by linarith
  have hnonneg : 0 ≤ A * (y - x) ^ 2 / ((q - x) ^ 2 * (q - y)) := by positivity
  have hid : A / (q - y) - A / (q - x) - A / (q - x) ^ 2 * (y - x) =
      A * (y - x) ^ 2 / ((q - x) ^ 2 * (q - y)) := by
    field_simp
    <;> ring
  linarith

theorem low_slope_le {q t A x : ℚ} (hqt : t < q) (hA : A ≤ q - t)
    (hx : x ≤ t) : A / (q - x) ^ 2 ≤ 1 / (q - t) := by
  have hc : 0 < q - t := by linarith
  have hd : 0 < q - x := by linarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hc).2
  have h1 := mul_le_mul_of_nonneg_right hA hc.le
  have h2 := mul_self_le_mul_self hc.le (show q - t ≤ q - x by linarith)
  nlinarith

theorem high_line_below_low {q t A y : ℚ} (hqt : t < q) (hA : A ≤ q - t)
    (hy : y ≤ t) : A / (q - t) + (y - t) / (q - t) ≤ A / (q - y) := by
  have hc : 0 < q - t := by linarith
  have hd : 0 < q - y := by linarith
  have h1 : 0 ≤ t - y := by linarith
  have h2 : 0 ≤ q - y - A := by linarith
  have hnonneg : 0 ≤ (t - y) * (q - y - A) / ((q - t) * (q - y)) :=
    div_nonneg (mul_nonneg h1 h2) (mul_pos hc hd).le
  have hid : A / (q - y) - A / (q - t) - (y - t) / (q - t) =
      (t - y) * (q - y - A) / ((q - t) * (q - y)) := by
    field_simp
    <;> ring
  linarith

/-- Every point has an exact global supporting line. -/
theorem loadPart_support {q t A : ℚ} (hqt : t < q) (hA0 : 0 ≤ A)
    (hAc : A ≤ q - t) (x y : ℚ) :
    loadPart q t A x + loadSlope q t A x * (y - x) ≤ loadPart q t A y := by
  by_cases hx : x ≤ t
  · by_cases hy : y ≤ t
    · simpa [loadPart, loadSlope, hx, hy] using reciprocal_support hqt hA0 hx hy
    · have ht : t ≤ y := le_of_not_ge hy
      have h1 := reciprocal_support hqt hA0 hx (le_refl t)
      have h2 := mul_le_mul_of_nonneg_right (low_slope_le hqt hAc hx)
        (show 0 ≤ y - t by linarith)
      simp only [loadPart, loadSlope, hx, hy, if_true, if_false]
      linear_combination h1 + h2
  · by_cases hy : y ≤ t
    · have h := high_line_below_low hqt hAc hy
      simp only [loadPart, loadSlope, hx, hy, if_true, if_false]
      convert h using 1 <;> ring
    · simp only [loadPart, loadSlope, hx, hy, if_true, if_false]
      ring_nf
      exact le_refl _

theorem loadSlope_nonneg {q t A : ℚ} (hqt : t < q) (hA0 : 0 ≤ A) (x : ℚ) :
    0 ≤ loadSlope q t A x := by
  unfold loadSlope
  split_ifs with hx
  · exact div_nonneg hA0 (sq_nonneg _)
  · exact div_nonneg (by norm_num) (by linarith)

theorem loadPart_monotone {q t A : ℚ} (hqt : t < q) (hA0 : 0 ≤ A)
    (hAc : A ≤ q - t) : Monotone (loadPart q t A) := by
  intro x y hxy
  have hs := loadPart_support hqt hA0 hAc x y
  have hm := mul_nonneg (loadSlope_nonneg hqt hA0 x) (sub_nonneg.mpr hxy)
  linarith

theorem loadPart_convex {q t A : ℚ} (hqt : t < q) (hA0 : 0 ≤ A)
    (hAc : A ≤ q - t) : ConvexOn ℚ Set.univ (loadPart q t A) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  let z := a * x + b * y
  have h1 := mul_le_mul_of_nonneg_left (loadPart_support hqt hA0 hAc z x) ha
  have h2 := mul_le_mul_of_nonneg_left (loadPart_support hqt hA0 hAc z y) hb
  have hz : a * (x - z) + b * (y - z) = 0 := by
    calc
      _ = (a * x + b * y) - (a + b) * z := by ring
      _ = 0 := by rw [hab]; dsimp [z]; ring
  have hsum : a * (loadPart q t A z + loadSlope q t A z * (x - z)) +
      b * (loadPart q t A z + loadSlope q t A z * (y - z)) = loadPart q t A z := by
    calc
      _ = (a + b) * loadPart q t A z +
          loadSlope q t A z * (a * (x - z) + b * (y - z)) := by ring
      _ = _ := by rw [hab, hz]; ring
  exact hsum ▸ add_le_add h1 h2

/-- Convexity on the line implies increasing fixed-width increments. -/
theorem convex_increment_mono {f : ℚ → ℚ} (hf : ConvexOn ℚ Set.univ f)
    {x y d : ℚ} (hxy : x ≤ y) (hd : 0 ≤ d) :
    f (x + d) - f x ≤ f (y + d) - f y := by
  by_cases hz : y + d - x = 0
  · have hy : y = x := by linarith
    subst y
    exact le_refl _
  have hden : 0 < y + d - x := lt_of_le_of_ne (by linarith) (Ne.symm hz)
  let a := (y - x) / (y + d - x)
  let b := d / (y + d - x)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hxy) hden.le
  have hb : 0 ≤ b := div_nonneg hd hden.le
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have h1 := hf.2 (Set.mem_univ x) (Set.mem_univ (y + d)) ha hb hab
  have h2 := hf.2 (Set.mem_univ x) (Set.mem_univ (y + d)) hb ha (by linarith)
  have he1 : a * x + b * (y + d) = x + d := by dsimp [a, b]; field_simp; ring
  have he2 : b * x + a * (y + d) = y := by dsimp [a, b]; field_simp; ring
  simp only [smul_eq_mul, he1, he2] at h1 h2
  have h := add_le_add h1 h2
  have he : a * f x + b * f (y + d) + (b * f x + a * f (y + d)) =
      f x + f (y + d) := by
    calc
      _ = (a + b) * (f x + f (y + d)) := by ring
      _ = _ := by rw [hab]; ring
  rw [he] at h
  linarith

theorem loadPart_increment_mono {q t A : ℚ} (hqt : t < q) (hA0 : 0 ≤ A)
    (hAc : A ≤ q - t) {x y d : ℚ} (hxy : x ≤ y) (hd : 0 ≤ d) :
    loadPart q t A (x + d) - loadPart q t A x ≤
      loadPart q t A (y + d) - loadPart q t A y :=
  convex_increment_mono (loadPart_convex hqt hA0 hAc) hxy hd

end Erdos7.CappedGain
