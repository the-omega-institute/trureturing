/- GID: D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Close
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/Lemma43Close
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43Params

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open scoped ENNReal NNReal

/-- **`hgbound_chained`'s constant in `C₁·e^{n²t/8}` form.**  The inner-ball term `ρⁿ/(2n)` is a
constant, not a multiple of the exponential; since `e^{n²t/8} ≥ 1` it may be absorbed into `C₁`. -/
theorem const_normalise {ρ A t : ℝ} {n : ℕ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t) :
    ρ ^ n / (2 * n) + A * Real.exp ((n : ℝ) ^ 2 * t / 8)
      ≤ (ρ ^ n / (2 * n) + A) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  have he : (1 : ℝ) ≤ Real.exp ((n : ℝ) ^ 2 * t / 8) :=
    Real.one_le_exp (by positivity)
  have hX : (0 : ℝ) ≤ ρ ^ n / (2 * n) := by positivity
  nlinarith [hX, he]

/-- The same, in the `ENNReal.ofReal` form `hgbound` is stated in. -/
theorem hgbound_normalised {a₀ α W t K : ℝ} {n : ℕ}
    (hρ : 0 ≤ radiusOf a₀ α (Real.sqrt n / 2) t 0) (ht : 0 ≤ t)
    (h : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
      ≤ ENNReal.ofReal ((radiusOf a₀ α (Real.sqrt n / 2) t 0) ^ n / (2 * n)
        + Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * K * Real.exp ((n : ℝ) ^ 2 * t / 8))) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
      ≤ ENNReal.ofReal
        (((radiusOf a₀ α (Real.sqrt n / 2) t 0) ^ n / (2 * n)
          + Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * K) * Real.exp ((n : ℝ) ^ 2 * t / 8)) :=
  le_trans h (ENNReal.ofReal_le_ofReal (const_normalise hρ ht))

theorem pieces_at_params {t A Y : ℝ} {n : ℕ} (hn : 0 < n) (ht : 0 ≤ t)
    (hts : Real.sqrt t ≤ 1 / 2) (hA1 : 1 ≤ A) (hAY : A ≤ Y)
    (hY : Y * Real.sqrt t ≤ 1 / 2)
    (hb2 : 2 ≤ (n : ℝ) * Real.sqrt t / 2)
    (hLb : (n : ℝ) * Real.sqrt t / 2 / 2 ≤ A)
    (hbA : (n : ℝ) * Real.sqrt t / 2 ≤ 2 * A)
    (hJ2 : ∀ y ∈ Ioc (1 : ℝ) A,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3)
    (hJ3 : ∀ y ∈ Ioc A Y,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3) :
    ((n : ℝ) * Real.sqrt t / 2) *
        ∫ y in Ioc (0 : ℝ) Y, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ (Real.exp 6 + Real.exp 3 * (2 / Real.sqrt (2 * π) + 2) + 2 * Real.exp 3)
        * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  have hs : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hAs : A * Real.sqrt t ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_right hAY hs) hY
  have hone : (0 : ℝ) ≤ 1 := zero_le_one

  have b1 := I1_le (n := n) ht hn hts (integrableOn_pieces (n := n) le_rfl (by simpa using hts))
  have b2 := I2_le (n := n) (J := 3) ht hAs hb2 hLb hJ2
    (integrableOn_pieces (n := n) hone hAs) (integrableOn_rhs (n := n) (J := 3) le_rfl)
  have b3 := I3_le (n := n) (J := 3) ht hA1 hY hbA hJ3
    (integrableOn_pieces (n := n) (le_trans zero_le_one hA1) hY)
    (integrableOn_rhs (n := n) (J := 3) hA1)
  exact pieces_sum_le hA1 hAY hone
    (integrableOn_pieces (n := n) le_rfl (by simpa using hts))
    (integrableOn_pieces (n := n) hone hAs)
    (integrableOn_pieces (n := n) (le_trans zero_le_one hA1) hY)
    b1 b2 b3

end D5.S3.Arith.Lattices.Klartag
