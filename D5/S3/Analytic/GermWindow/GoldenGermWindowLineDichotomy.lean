/- GID: D5/S3/Analytic/GermWindow/GoldenGermWindowLineDichotomy
   generality: I
   mirror-B: D5/B/S3/Analytic/GermWindow/GoldenGermWindowLineDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separate on-line and off-line zeros of the continued golden germ under RH. -/

import D5.S3.Analytic.GermWindow.GoldenGermThirdOrderWindowZeroCriterion
import D5.S3.Analytic.EulerGerm.LocalFactorCriticalLineNonvanishing

/- Library-search audit trail (2026-09-03):
   * The frozen `golden_continued_germ_window_zero_iff_of_rh` supplies the
     complete third-order open-window zero classification under RH.
   * The frozen `germLocalFactor_critical_line_nonzero_of_five_le` excludes
     local-factor zeros at every prime at least five on the pulled-back line.
   * Pinned Mathlib supplies `Nat.Prime.two_le` and the ordered-field
     reciprocal lemmas. No existing declaration gives either dichotomy below. -/

namespace D5.S3.Analytic.GermWindow.GoldenGermWindowLineDichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
open D5.S3.Analytic.EulerGerm.LocalFactorCriticalLineNonvanishing
open D5.S3.Analytic.GermWindow.GoldenGermThirdOrderWindowZeroCriterion

noncomputable section

/-- Under RH, on the pulled-back critical line the continued third-order
golden germ vanishes exactly at a pulled-back zeta zero or at a local-factor
zero for `p = 2` or `p = 3`. -/
theorem golden_continued_germ_line_zero_iff_of_rh
    (hRH : RiemannHypothesis) :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes, Kp s p
    ∀ continuedGerm :
        {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} -> Complex,
      (∀ s, continuedGerm s =
        riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) *
          riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) *
          (riemannZeta
            (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ *
          ((riemannZeta
            (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s.1))⁻¹ *
            riemannZeta
              ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
                Complex) * s.1)) *
            G3 s.1)) ->
      ∀ s, s.1.re = 1 / (2 * Real.goldenRatio ^ 2) ->
        (continuedGerm s = 0 ↔
          (riemannZeta
              (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) = 0 ∨
            germLocalFactor s.1 2 = 0 ∨
            germLocalFactor s.1 3 = 0)) := by
  dsimp only
  intro continuedGerm hformula s hline
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hphi2_lt_phi3 :
      Real.goldenRatio ^ 2 < Real.goldenRatio ^ 3 := by
    calc
      Real.goldenRatio ^ 2 = Real.goldenRatio ^ 2 * 1 := by ring
      _ < Real.goldenRatio ^ 2 * Real.goldenRatio :=
        mul_lt_mul_of_pos_left Real.one_lt_goldenRatio hphi2
      _ = Real.goldenRatio ^ 3 := by ring
  have hlo : 1 / (2 * Real.goldenRatio ^ 3) < s.1.re := by
    rw [hline]
    exact one_div_lt_one_div_of_lt (by positivity)
      (mul_lt_mul_of_pos_left hphi2_lt_phi3 (by norm_num))
  have hhi : s.1.re < 1 / Real.goldenRatio ^ 2 := by
    rw [hline]
    exact one_div_lt_one_div_of_lt hphi2 (by nlinarith)
  have hcriterion :=
    golden_continued_germ_window_zero_iff_of_rh
      hRH continuedGerm hformula s hlo hhi
  have hs_decomp :
      s.1 = (((1 / (2 * Real.goldenRatio ^ 2) : Real) : Complex) +
        Complex.I * (s.1.im : Complex)) := by
    apply Complex.ext_iff.mpr
    constructor
    · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
        one_mul, sub_zero, add_zero] using hline
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
        zero_add]
  constructor
  · intro hzero
    rcases hcriterion.mp hzero with
      ⟨hzeta, _⟩ | ⟨⟨p, hpPrime⟩, hpzero⟩
    · exact Or.inl hzeta
    · by_cases h5 : 5 ≤ p
      · have hnonzero :=
          germLocalFactor_critical_line_nonzero_of_five_le
            hpPrime h5 s.1.im
        rw [hs_decomp] at hpzero
        exact (hnonzero hpzero).elim
      · have hpCases : p = 2 ∨ p = 3 := by
          have hpTwo : 2 ≤ p := hpPrime.two_le
          have hpLt : p < 5 := Nat.lt_of_not_ge h5
          interval_cases p
          · exact Or.inl rfl
          · exact Or.inr rfl
          · norm_num at hpPrime
        rcases hpCases with hpTwo | hpThree
        · exact Or.inr (Or.inl (by simpa [hpTwo] using hpzero))
        · exact Or.inr (Or.inr (by simpa [hpThree] using hpzero))
  · rintro (hzeta | hlocalTwo | hlocalThree)
    · exact hcriterion.mpr (Or.inl ⟨hzeta, hline⟩)
    · exact hcriterion.mpr
        (Or.inr ⟨⟨2, Nat.prime_two⟩, by simpa using hlocalTwo⟩)
    · exact hcriterion.mpr
        (Or.inr ⟨⟨3, Nat.prime_three⟩, by simpa using hlocalThree⟩)

/-- Under RH, away from the pulled-back critical line every zero of the
continued third-order golden germ in the open window is exactly a zero of one
of the canonical local factors. -/
theorem golden_continued_germ_off_line_zero_iff_of_rh
    (hRH : RiemannHypothesis) :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes, Kp s p
    ∀ continuedGerm :
        {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} -> Complex,
      (∀ s, continuedGerm s =
        riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) *
          riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) *
          (riemannZeta
            (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ *
          ((riemannZeta
            (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s.1))⁻¹ *
            riemannZeta
              ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
                Complex) * s.1)) *
            G3 s.1)) ->
      ∀ s, 1 / (2 * Real.goldenRatio ^ 3) < s.1.re ->
        s.1.re < 1 / Real.goldenRatio ^ 2 ->
        s.1.re ≠ 1 / (2 * Real.goldenRatio ^ 2) ->
        (continuedGerm s = 0 ↔
          ∃ p : Nat.Primes, germLocalFactor s.1 p = 0) := by
  dsimp only
  intro continuedGerm hformula s hlo hhi hoffLine
  have hcriterion :=
    golden_continued_germ_window_zero_iff_of_rh
      hRH continuedGerm hformula s hlo hhi
  simpa only [hoffLine, and_false, false_or] using hcriterion

/- These checked examples witness the continuation domain and the frozen
five-zeta premise package. RH remains the explicit conditional input. -/
example : Nonempty {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} := by
  refine ⟨⟨1, ?_⟩⟩
  have hpow : (1 : Real) < Real.goldenRatio ^ 5 :=
    one_lt_pow₀ Real.one_lt_goldenRatio (by norm_num)
  simpa using (inv_lt_one_of_one_lt₀ hpow)

example :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes, Kp s p
    ∃ continuedGerm :
        {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} -> Complex,
      ∀ s, continuedGerm s =
        riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) *
          riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) *
          (riemannZeta
            (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ *
          ((riemannZeta
            (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s.1))⁻¹ *
            riemannZeta
              ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
                Complex) * s.1)) *
            G3 s.1) := by
  have hthird := golden_germ_third_order_factorization
  dsimp only at hthird ⊢
  rcases hthird.2.exists with ⟨continuedGerm, _, hformula⟩
  exact ⟨continuedGerm, hformula⟩

#print axioms golden_continued_germ_line_zero_iff_of_rh
#print axioms golden_continued_germ_off_line_zero_iff_of_rh

end

end D5.S3.Analytic.GermWindow.GoldenGermWindowLineDichotomy
