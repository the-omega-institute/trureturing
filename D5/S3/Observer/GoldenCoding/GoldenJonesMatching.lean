/- GID: D5/S3/Observer/GoldenCoding/GoldenJonesMatching
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenJonesMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden square is the first nonintegral low Jones value and fusion dimension. -/

import D5.S1.FixedPoints.Algebraic.GoldenFixedPoint
import D5.S3.Constants.PentagonCosines
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The target atom remains residual-open with empty `coverage_gids`, and its atom id has no
     formalization receipt. Repository searches for Jones indices, subfactors, the first
     nonintegral cosine-square value, and Fibonacci quantum dimensions found no full theorem.
   * `PentagonCosines.pentagon_golden_cosines` supplies the exact doubled-cosine identity, and
     `GoldenFixedPoint.golden_fixed_point_unique` supplies the unique positive fusion dimension.
     The adjacent `GoldenLorentzUpdate` concerns a different quadratic form; no
     `GoldenBusemannCoordinate` module exists on the pinned base.
   * Pinned Mathlib supplies `Real.cos_pi_div_three`, `Real.cos_pi_div_four`,
     `Real.sq_cos_pi_div_six`, `Real.goldenRatio_sq`, and `Real.goldenRatio_irrational`.
   * A NyxID-proxied GitHub ecosystem search for Lean Jones/subfactor and Fibonacci-fusion
     formalizations returned no matching declaration. No new definition or axiom is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenCoding.GoldenJonesMatching

open D5.S1.FixedPoints.Algebraic.GoldenFixedPoint
open D5.S3.Constants.PentagonCosines

/-- The low Jones cosine-square sequence starts with `1, 2, phi^2, 3`. The golden square is
strictly between the adjacent integers (with a numerical enclosure), the entries before index
five are integral, and the index-five entry is not integral. The final clause records the
decategorified consequence of the Fibonacci fusion law: every positive dimension satisfying
`d^2 = 1 + d` is the golden ratio and has squared dimension `phi^2`. -/
theorem golden_jones_matching :
    let jonesValue := fun n : ℕ =>
      4 * Real.cos (Real.pi / (n : ℝ)) ^ 2
    jonesValue 3 = 1 ∧
      jonesValue 4 = 2 ∧
      jonesValue 5 = Real.goldenRatio ^ 2 ∧
      jonesValue 6 = 3 ∧
      Real.goldenRatio ^ 2 = (3 + Real.sqrt 5) / 2 ∧
      2 < Real.goldenRatio ^ 2 ∧
      Real.goldenRatio ^ 2 < 3 ∧
      2.6 < Real.goldenRatio ^ 2 ∧
      Real.goldenRatio ^ 2 < 2.62 ∧
      (∀ n : ℕ, 3 ≤ n → n < 5 →
        ∃ m : ℤ, jonesValue n = (m : ℝ)) ∧
      (¬∃ m : ℤ, jonesValue 5 = (m : ℝ)) ∧
      ∀ d : ℝ, 0 < d → d ^ 2 = 1 + d →
        d = Real.goldenRatio ∧ d ^ 2 = Real.goldenRatio ^ 2 := by
  dsimp only
  have hThree : 4 * Real.cos (Real.pi / (3 : ℝ)) ^ 2 = 1 := by
    rw [Real.cos_pi_div_three]
    norm_num
  have hFour : 4 * Real.cos (Real.pi / (4 : ℝ)) ^ 2 = 2 := by
    rw [Real.cos_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hFive :
      4 * Real.cos (Real.pi / (5 : ℝ)) ^ 2 = Real.goldenRatio ^ 2 := by
    calc
      4 * Real.cos (Real.pi / (5 : ℝ)) ^ 2 =
          (2 * Real.cos (Real.pi / 5)) ^ 2 := by ring
      _ = Real.goldenRatio ^ 2 := by rw [pentagon_golden_cosines.1]
  have hSix : 4 * Real.cos (Real.pi / (6 : ℝ)) ^ 2 = 3 := by
    rw [Real.sq_cos_pi_div_six]
    norm_num
  have hRadical : Real.goldenRatio ^ 2 = (3 + Real.sqrt 5) / 2 := by
    rw [Real.goldenRatio_sq, Real.goldenRatio]
    ring
  have hSqrtSq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hSqrtNonnegative : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hSqrtLower : (11 / 5 : ℝ) < Real.sqrt 5 := by
    nlinarith
  have hSqrtUpper : Real.sqrt 5 < (56 / 25 : ℝ) := by
    nlinarith
  have hFineLower : (2.6 : ℝ) < Real.goldenRatio ^ 2 := by
    rw [hRadical]
    norm_num at hSqrtLower ⊢
    nlinarith
  have hFineUpper : Real.goldenRatio ^ 2 < (2.62 : ℝ) := by
    rw [hRadical]
    norm_num at hSqrtUpper ⊢
    nlinarith
  have hLower : (2 : ℝ) < Real.goldenRatio ^ 2 := by
    nlinarith
  have hUpper : Real.goldenRatio ^ 2 < (3 : ℝ) := by
    nlinarith
  have hBeforeFive : ∀ n : ℕ, 3 ≤ n → n < 5 →
      ∃ m : ℤ, 4 * Real.cos (Real.pi / (n : ℝ)) ^ 2 = (m : ℝ) := by
    intro n hStart hStop
    have hn : n = 3 ∨ n = 4 := by omega
    rcases hn with rfl | rfl
    · exact ⟨1, hThree.trans (by norm_num)⟩
    · exact ⟨2, hFour.trans (by norm_num)⟩
  have hGoldenSquareIrrational : Irrational (Real.goldenRatio ^ 2) := by
    rw [Real.goldenRatio_sq]
    simpa using Real.goldenRatio_irrational.add_ratCast 1
  have hFiveNotInteger :
      ¬∃ m : ℤ, 4 * Real.cos (Real.pi / (5 : ℝ)) ^ 2 = (m : ℝ) := by
    rintro ⟨m, hm⟩
    exact hGoldenSquareIrrational.ne_int m (hFive.symm.trans hm)
  have hFusionDimension : ∀ d : ℝ, 0 < d → d ^ 2 = 1 + d →
      d = Real.goldenRatio ∧ d ^ 2 = Real.goldenRatio ^ 2 := by
    intro d hd hQuadratic
    have hFixed : goldenReciprocalMap d = d :=
      ((D5.S0.Tower.QuadraticFixedPoint.quadratic_fixed_point_iff d
        (ne_of_gt hd)).1 (by nlinarith [hQuadratic])).symm
    have hGoldenRadical : d = (1 + Real.sqrt 5) / 2 :=
      (golden_fixed_point_unique.2.2 d hd).1 hFixed
    have hGolden : d = Real.goldenRatio := by
      simpa only [Real.goldenRatio] using hGoldenRadical
    exact ⟨hGolden, congrArg (fun x : ℝ => x ^ 2) hGolden⟩
  exact ⟨hThree, hFour, hFive, hSix, hRadical, hLower, hUpper,
    hFineLower, hFineUpper, hBeforeFive, hFiveNotInteger, hFusionDimension⟩

#print axioms golden_jones_matching

end D5.S3.Observer.GoldenCoding.GoldenJonesMatching
