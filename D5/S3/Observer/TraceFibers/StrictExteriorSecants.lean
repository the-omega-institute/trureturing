/- GID: D5/S3/Observer/TraceFibers/StrictExteriorSecants
   generality: I
   mirror-B: D5/B/S3/Observer/TraceFibers/StrictExteriorSecants
   mirror-E: none(waiver:whole-positive-source-estimate)
   anchors: []
   utility: none
   digest: A uniform secant estimate on each strict exterior positive source fiber. -/

import D5.S3.Observer.Linear.GainRayWordGeometry
import D5.S3.Observer.TraceFibers.FixedFiberPairModulus

/-! Uniform inversion on the entire positive calibrated source fiber. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace D5.S3.Observer.TraceFibers.StrictExteriorSecants

open D5.S3.Observer.Linear.GainRay
open FixedFiberPairModulus (maxEntry)

private theorem row_coordinates (P : Mat) (hP : LegalSource P) :
    ∃ x : ℝ, 0 < x ∧ P 1 0 = x * P 0 0 ∧ P 1 1 = x * P 0 1 := by
  obtain ⟨x, r, hx, _, rfl, _, _⟩ := source_chart_exact P hP
  refine ⟨x, hx, ?_, ?_⟩ <;> simp [sourceChart] <;> ring

/-- A single finite constant controls all pairs in the original positive fiber. -/
theorem strict_exterior_uniform_secant (θ : ℚ) (hθ : 0 < θ) (b : ℝ) (hb : 0 < b)
    (hout : b < min (1 / (θ : ℝ)) (1 + (θ : ℝ)) ∨
      max (1 / (θ : ℝ)) (1 + (θ : ℝ)) < b) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ P Q : Mat, LegalSource P → LegalSource Q →
      Matrix.trace (action false * P) = b → Matrix.trace (action false * Q) = b →
      maxEntry (P - Q) ≤ L *
        |(P 1 0 - (θ : ℝ) * P 1 1) - (Q 1 0 - (θ : ℝ) * Q 1 1)| := by
  have hθr : 0 < (θ : ℝ) := by exact_mod_cast hθ
  let B : ℝ := b - 1 - θ
  let C : ℝ := b * θ - 1
  have hsign : (B < 0 ∧ C < 0) ∨ (0 < B ∧ 0 < C) := by
    rcases hout with h | h
    · obtain ⟨ht, hu⟩ := lt_min_iff.mp h
      left
      have hc := (lt_div_iff₀ hθr).mp ht
      dsimp [B, C]
      constructor <;> linarith
    · obtain ⟨ht, hu⟩ := max_lt_iff.mp h
      right
      have hc := (div_lt_iff₀ hθr).mp ht
      dsimp [B, C]
      constructor <;> linarith
  let m := min |B| |C|
  have hm : 0 < m := by
    rcases hsign with ⟨hB, hC⟩ | ⟨hB, hC⟩
    · exact lt_min (abs_pos.mpr (ne_of_lt hB)) (abs_pos.mpr (ne_of_lt hC))
    · exact lt_min (abs_pos.mpr (ne_of_gt hB)) (abs_pos.mpr (ne_of_gt hC))
  let D := b + |b - 1| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let R := D / m
  have hR : 0 ≤ R := (div_pos hD hm).le
  let L := 1 + (1 + (θ : ℝ)) * R
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro P Q hP hQ hPb hQb
  obtain ⟨x, hx, hPv, hPt⟩ := row_coordinates P hP
  obtain ⟨y, hy, hQv, hQt⟩ := row_coordinates Q hQ
  have hPtr : P 0 0 + P 1 1 = 1 := by
    simpa [Matrix.trace_fin_two] using hP.2.2
  have hQtr : Q 0 0 + Q 1 1 = 1 := by
    simpa [Matrix.trace_fin_two] using hQ.2.2
  have hPcal : P 0 1 + P 1 0 + P 1 1 = b := by
    simpa [action_m_shape, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc] using hPb
  have hQcal : Q 0 1 + Q 1 0 + Q 1 1 = b := by
    simpa [action_m_shape, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc] using hQb
  let h := Q 1 1 - P 1 1
  let k := Q 1 0 - P 1 0
  let e := k - (θ : ℝ) * h
  have hdiag : P 0 0 - Q 0 0 = h := by dsimp [h]; linarith
  have hoff : P 0 1 - Q 0 1 = h + k := by dsimp [h, k]; linarith
  have hrowa : (y - x) * P 0 0 = k + y * h := by
    dsimp [k]
    linear_combination hPv - hQv + y * hdiag
  have hrowu : (y - x) * P 0 1 = h + y * (h + k) := by
    dsimp [h, k] at hoff ⊢
    linear_combination hPt - hQt + y * hoff
  have hf : (b - x) * P 0 0 + ((b - 1) * x - 1) * P 0 1 = 0 := by
    linear_combination b * hPtr - hPcal + hPv - (b - 1) * hPt
  let K := (b - 1) * x * y - (x + y) + b
  let A := (B + C) * x * y + B * (x + y) + C
  have hid : h * A + e * K = 0 := by
    dsimp [A, B, C, e, K]
    linear_combination -(b - x) * hrowa - ((b - 1) * x - 1) * hrowu +
      (y - x) * hf
  let W := x * y + (x + y) + 1
  have hW : 0 < W := by dsimp [W]; positivity
  have hxy : 0 ≤ x * y := mul_nonneg hx.le hy.le
  have hsum : 0 ≤ x + y := by positivity
  have hlower : m * W ≤ |A| := by
    have hmB : m ≤ |B| := min_le_left _ _
    have hmC : m ≤ |C| := min_le_right _ _
    rcases hsign with ⟨hB, hC⟩ | ⟨hB, hC⟩
    · rw [abs_of_neg hB] at hmB
      rw [abs_of_neg hC] at hmC
      have hp := mul_nonneg (show 0 ≤ -B - C - m by linarith) hxy
      have hq := mul_nonneg (show 0 ≤ -B - m by linarith) hsum
      have hh : m * W ≤ -A := by dsimp [W, A]; nlinarith only [hp, hq, hmC]
      exact hh.trans (neg_le_abs A)
    · rw [abs_of_pos hB] at hmB
      rw [abs_of_pos hC] at hmC
      have hp := mul_nonneg (show 0 ≤ B + C - m by linarith) hxy
      have hq := mul_nonneg (show 0 ≤ B - m by linarith) hsum
      have hh : m * W ≤ A := by dsimp [W, A]; nlinarith only [hp, hq, hmC]
      exact hh.trans (le_abs_self A)
  have hupper : |K| ≤ D * W := by
    have htri : |K| ≤ |b - 1| * x * y + (x + y) + b := by
      calc
        |K| ≤ |(b - 1) * x * y - (x + y)| + |b| := abs_add_le _ _
        _ ≤ |(b - 1) * x * y| + |x + y| + |b| := by
          gcongr
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le ((b - 1) * x * y) (-(x + y))
        _ = _ := by rw [abs_mul, abs_mul, abs_of_pos hx, abs_of_pos hy,
          abs_of_nonneg hsum, abs_of_pos hb]
    have hp := mul_nonneg (show 0 ≤ D - |b - 1| by dsimp [D]; linarith) hxy
    have hq := mul_nonneg (show 0 ≤ D - 1 by
      dsimp [D]; linarith [abs_nonneg (b - 1)]) hsum
    have hc : b ≤ D := by dsimp [D]; linarith [abs_nonneg (b - 1)]
    have hh : |b - 1| * x * y + (x + y) + b ≤ D * W := by
      dsimp [W]; nlinarith only [hp, hq, hc]
    exact htri.trans hh
  have habs : |h| * |A| = |e| * |K| := by
    have hh : h * A = -(e * K) := by linarith only [hid]
    simpa only [abs_mul, abs_neg] using congrArg abs hh
  have hprod : |h| * (m * W) ≤ |e| * (D * W) := calc
    _ ≤ |h| * |A| := mul_le_mul_of_nonneg_left hlower (abs_nonneg h)
    _ = |e| * |K| := habs
    _ ≤ _ := mul_le_mul_of_nonneg_left hupper (abs_nonneg e)
  have hcancel : |h| * m ≤ |e| * D := by
    apply (mul_le_mul_iff_left₀ hW).mp
    nlinarith only [hprod]
  have hhbound : |h| ≤ R * |e| := by
    calc
      |h| = (|h| * m) / m := by field_simp
      _ ≤ (|e| * D) / m := div_le_div_of_nonneg_right hcancel hm.le
      _ = R * |e| := by dsimp [R]; ring
  have hkbound : |k| ≤ (1 + (θ : ℝ) * R) * |e| := by
    have hke : k = e + (θ : ℝ) * h := by dsimp [e]; ring
    calc
      |k| = |e + (θ : ℝ) * h| := congrArg abs hke
      _ ≤ |e| + (θ : ℝ) * |h| := by
        simpa only [abs_mul, abs_of_pos hθr] using abs_add_le e ((θ : ℝ) * h)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hhbound hθr.le]
  have hhkbound : |h + k| ≤ L * |e| := by
    calc
      |h + k| ≤ |h| + |k| := abs_add_le _ _
      _ ≤ R * |e| + (1 + (θ : ℝ) * R) * |e| := add_le_add hhbound hkbound
      _ = _ := by dsimp [L]; ring
  have hRL : R ≤ L := by dsimp [L]; nlinarith only [mul_nonneg hθr.le hR]
  have hkL : 1 + (θ : ℝ) * R ≤ L := by dsimp [L]; linarith only [hR]
  have hentries : maxEntry (P - Q) ≤ L * |e| := by
    apply max_le
    · apply max_le
      · simpa only [Matrix.sub_apply, hdiag] using
          hhbound.trans (mul_le_mul_of_nonneg_right hRL (abs_nonneg e))
      · simpa only [Matrix.sub_apply, hoff] using hhkbound
    · apply max_le
      · have hv : P 1 0 - Q 1 0 = -k := by dsimp [k]; ring
        simpa only [Matrix.sub_apply, hv, abs_neg] using
          hkbound.trans (mul_le_mul_of_nonneg_right hkL (abs_nonneg e))
      · have ht : P 1 1 - Q 1 1 = -h := by dsimp [h]; ring
        simpa only [Matrix.sub_apply, ht, abs_neg] using
          hhbound.trans (mul_le_mul_of_nonneg_right hRL (abs_nonneg e))
  have he : (P 1 0 - (θ : ℝ) * P 1 1) -
      (Q 1 0 - (θ : ℝ) * Q 1 1) = -e := by dsimp [e, k, h]; ring
  simpa only [he, abs_neg] using hentries

#print axioms strict_exterior_uniform_secant

end D5.S3.Observer.TraceFibers.StrictExteriorSecants
