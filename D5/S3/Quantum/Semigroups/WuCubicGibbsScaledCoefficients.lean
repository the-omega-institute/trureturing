/- GID: D5/S3/Quantum/Semigroups/WuCubicGibbsScaledCoefficients
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicGibbsScaledCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact endpoint Taylor polynomials and middle-gap coefficients for Wu's cubic bound. -/

import D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
import D5.S3.Quantum.Semigroups.WuCubicOccupationTaylor
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! The coefficient identities for the Gibbs-relative form of Wu v1 (3.54).
The endpoint expansions retain the quadratic and cubic terms of the four cut
polynomials and the two adjacent coefficients. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuCubicGibbsScaledCoefficients

open WuCubicAngularCertificate
open WuCubicOccupationTaylor (gibbsLevels)
open private c e bias gamma cutA cutB from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private crossCoeff directedCoeff from D5.S3.Quantum.Semigroups.WuCubicAngularCertificate

/-- The coefficient of the middle gap in the middle cut energy. -/
def middleEnergyScaled (r n q : ℝ) : ℝ := c r * (q - n) * (n + q)

/-- The coefficient of the middle gap in the middle cut bias. -/
def middleBiasScaled (r n q : ℝ) : ℝ :=
  bias r * (n ^ 2 + n * q + q ^ 2) + 2 * e r * (q - n) ^ 2

private def adjacentFactor (r gap sum midGap midSum : ℝ) : ℝ :=
  c r * (sum + midSum) - 3 * e r * (gap + midGap)

/-- The coefficient of the middle gap in the lower adjacent crossing. -/
def lowerCoeffScaled (r m n q : ℝ) : ℝ :=
  (n - m) * adjacentFactor r (n - m) (m + n) (q - n) (n + q)

/-- The coefficient of the middle gap in the upper adjacent crossing. -/
def upperCoeffScaled (r n q : ℝ) : ℝ :=
  (1 - q) * adjacentFactor r (1 - q) (q + 1) (q - n) (n + q)

theorem middle_energy_eq (r m n q : ℝ) :
    cutEnergy r m n q 1 = (q - n) * middleEnergyScaled r n q := by
  simp [cutEnergy, cutA, middleEnergyScaled]
  ring

theorem middle_bias_eq (r m n q : ℝ) :
    cutBias r m n q 1 = (q - n) * middleBiasScaled r n q := by
  simp [cutBias, cutB, middleBiasScaled]
  ring

theorem lower_coeff_eq (r m n q : ℝ) :
    lowerCoeff r m n q = (q - n) * lowerCoeffScaled r m n q := by
  unfold lowerCoeff crossCoeff directedCoeff lowerCoeffScaled adjacentFactor
  ring

theorem upper_coeff_eq (r n q : ℝ) :
    upperCoeff r n q = (q - n) * upperCoeffScaled r n q := by
  unfold upperCoeff crossCoeff directedCoeff upperCoeffScaled adjacentFactor
  ring

theorem long_coeff_eq (r m n q : ℝ) :
    longCoeff r m n q = (n - m) * (1 - q) *
      (c r * (m + n + q + 1) - 3 * e r * ((n - m) + (1 - q) + 2 * (q - n))) := by
  unfold longCoeff crossCoeff directedCoeff
  ring

/-- The coefficient of the middle gap in the matched mixture weight `L₀`. -/
def matchedMixtureScaled (r n q : ℝ) : ℝ :=
  middleBiasScaled r n q / 2 - middleEnergyScaled r n q

/-- The coefficient of the middle gap in the refined mixture weight `L`. -/
def refinedMixtureScaled (r m n q : ℝ) : ℝ :=
  min (lowerCoeffScaled r m n q) (upperCoeffScaled r n q)

/-- The coefficient of the middle gap in the excess weight `ell = L - L₀`. -/
def refinedExcessScaled (r m n q : ℝ) : ℝ :=
  refinedMixtureScaled r m n q - matchedMixtureScaled r n q

/-- The coefficient of the middle gap in `H = E 1 + L`. -/
def refinedHScaled (r m n q : ℝ) : ℝ :=
  middleEnergyScaled r n q + refinedMixtureScaled r m n q

theorem matched_mixture_eq (r m n q : ℝ) :
    matchedMixture (cutEnergy r m n q) (cutBias r m n q) =
      (q - n) * matchedMixtureScaled r n q := by
  rw [matchedMixture, middle_energy_eq, middle_bias_eq, matchedMixtureScaled]
  ring

theorem refined_mixture_eq {r m n q : ℝ} (hnq : n ≤ q) :
    min (lowerCoeff r m n q) (upperCoeff r n q) = (q - n) * refinedMixtureScaled r m n q := by
  rw [lower_coeff_eq, upper_coeff_eq, refinedMixtureScaled,
    mul_min_of_nonneg _ _ (sub_nonneg.mpr hnq)]

theorem refined_excess_eq {r m n q : ℝ} (hnq : n ≤ q) :
    min (lowerCoeff r m n q) (upperCoeff r n q) -
      matchedMixture (cutEnergy r m n q) (cutBias r m n q) =
        (q - n) * refinedExcessScaled r m n q := by
  rw [refined_mixture_eq hnq, matched_mixture_eq, refinedExcessScaled, mul_sub]

theorem refined_H_eq {r m n q : ℝ} (hnq : n ≤ q) :
    cutEnergy r m n q 1 + min (lowerCoeff r m n q) (upperCoeff r n q) =
      (q - n) * refinedHScaled r m n q := by
  rw [middle_energy_eq, refined_mixture_eq hnq, refinedHScaled, mul_add]

/-- The divided matched comparisons imply the actual mixture admissibility,
including at a repeated middle level. -/
theorem matched_mixture_comparisons {r m n q : ℝ} (hnq : n ≤ q)
    (hscaled : n < q → 0 ≤ matchedMixtureScaled r n q ∧ 0 ≤ refinedExcessScaled r m n q) :
    let L₀ := matchedMixture (cutEnergy r m n q) (cutBias r m n q)
    0 ≤ L₀ ∧ L₀ ≤ lowerCoeff r m n q ∧ L₀ ≤ upperCoeff r n q := by
  dsimp only
  rcases eq_or_lt_of_le hnq with heq | hlt
  · subst q
    simp [matched_mixture_eq, lower_coeff_eq, upper_coeff_eq]
  · obtain ⟨hL₀, hell⟩ := hscaled hlt
    have hgap : 0 ≤ q - n := sub_nonneg.mpr hnq
    have hle : matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤
        min (lowerCoeff r m n q) (upperCoeff r n q) :=
      sub_nonneg.mp (by rw [refined_excess_eq hnq]; exact mul_nonneg hgap hell)
    exact ⟨by rw [matched_mixture_eq]; exact mul_nonneg hgap hL₀, le_min_iff.mp hle⟩

/-- The charge comparisons at a tilt threshold `T`, in the form used by
the refined angular minimum. -/
theorem refined_charge_comparisons {r m n q T : ℝ} (hnq : n ≤ q)
    (hsmall : n < q → refinedHScaled r m n q * T / 2 ≤ refinedExcessScaled r m n q)
    (hend : (q - n) * refinedExcessScaled r m n q ≤
      min (cutBias r m n q 0) (cutBias r m n q 2)) :
    let E := cutEnergy r m n q
    let B := cutBias r m n q
    let L := min (lowerCoeff r m n q) (upperCoeff r n q)
    let ell := L - matchedMixture E B
    let H := E 1 + L
    H * T / 2 ≤ ell ∧ ell ≤ min (B 0) (B 2) := by
  dsimp only
  rw [refined_H_eq hnq, refined_excess_eq hnq]
  constructor
  · rcases eq_or_lt_of_le hnq with heq | hlt
    · simp [heq]
    · rw [mul_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hsmall hlt) (sub_nonneg.mpr hnq)
  · exact hend

/-- The refined square loss factors through the same middle gap. Lean's
real division gives the value zero when the denominator vanishes. -/
theorem refined_loss_eq {r m n q : ℝ} (hnq : n ≤ q) :
    let L := min (lowerCoeff r m n q) (upperCoeff r n q)
    L ^ 2 / (4 * (3 * cutEnergy r m n q 1 + L)) =
      (q - n) * ((refinedMixtureScaled r m n q) ^ 2 /
        (4 * (3 * middleEnergyScaled r n q + refinedMixtureScaled r m n q))) := by
  dsimp only
  rw [refined_mixture_eq hnq, middle_energy_eq]
  by_cases hgap : q - n = 0
  · simp [hgap]
  · have hden :
        4 * (3 * ((q - n) * middleEnergyScaled r n q) +
          (q - n) * refinedMixtureScaled r m n q) =
        (q - n) * (4 * (3 * middleEnergyScaled r n q + refinedMixtureScaled r m n q)) := by ring
    rw [hden, mul_pow, pow_two (q - n), mul_assoc, mul_div_assoc,
      mul_div_mul_left _ _ hgap]

/-- The exact quadratic and cubic contribution of an energy cut, after
factoring out `d ^ 2`. The endpoints are `v + d * a` and `w + d * b`. -/
def energyRemainder (r d v w a b : ℝ) : ℝ :=
  let gap := w - v
  let k := b - a
  let l := a + b
  c r * (2 * gap * k * l + k ^ 2 * (v + w + d * l))

/-- The exact quadratic and cubic contribution of half a bias cut, after
factoring out `d ^ 2`. -/
def halfBiasRemainder (r d v w a b : ℝ) : ℝ :=
  let k := b - a
  bias r * (3 * (w * b ^ 2 - v * a ^ 2) + d * (b ^ 3 - a ^ 3)) / 2 +
    e r * (3 * (w - v) * k ^ 2 + d * k ^ 3)

/-- The exact quadratic and cubic contribution of an adjacent coefficient,
after factoring out `d ^ 2`. The middle levels start at `s` and move in
directions `u` and `t`. -/
def adjacentRemainder (r d v w a b s u t : ℝ) : ℝ :=
  let gap := w - v
  let k := b - a
  let midChange := t - u
  let start := adjacentFactor r gap (v + w) 0 (s + s)
  let change := adjacentFactor r k (a + b) midChange (u + t)
  midChange * (k * start + gap * change + d * k * change)

/-- The exact remainder of an endpoint linear cut cost, after factoring
out `d ^ 2`. -/
def endpointRemainder (r d v w a b s u t : ℝ) : ℝ :=
  halfBiasRemainder r d v w a b - energyRemainder r d v w a b -
    adjacentRemainder r d v w a b s u t +
    halfBiasRemainder r d s s u t - energyRemainder r d s s u t

/-- The homogeneous cubic term in the endpoint linear cut cost. -/
def endpointCubic (r a b u t : ℝ) : ℝ :=
  let k := b - a
  let k₁ := t - u
  let l := a + b
  let l₁ := u + t
  bias r * (b ^ 3 - a ^ 3 + t ^ 3 - u ^ 3) / 2 + e r * (k ^ 3 + k₁ ^ 3) -
    c r * (k ^ 2 * l + k₁ ^ 2 * l₁) - k₁ * k * adjacentFactor r k l k₁ l₁

theorem endpoint_remainder_eq (r d v w a b s u t : ℝ) :
    endpointRemainder r d v w a b s u t =
      endpointRemainder r 0 v w a b s u t + d * endpointCubic r a b u t := by
  dsimp [endpointRemainder, endpointCubic, energyRemainder, halfBiasRemainder,
    adjacentRemainder]
  ring

private def endpointSlope (r v w a b s u t : ℝ) : ℝ :=
  let gap := w - v
  let k := b - a
  bias r * (3 * (w ^ 2 * b - v ^ 2 * a)) / 2 + 3 * e r * gap ^ 2 * k -
    c r * (2 * gap * k * (v + w) + gap ^ 2 * (a + b)) -
    (t - u) * gap * adjacentFactor r gap (v + w) 0 (s + s) +
    bias r * (3 * s ^ 2 * (t - u)) / 2

private theorem endpoint_expansion (r d v w a b s u t : ℝ) :
    let X := v + d * a
    let Y := w + d * b
    let N := s + d * u
    let Q := s + d * t
    cutB r X Y / 2 - cutA r X Y -
      (Q - N) * ((Y - X) * adjacentFactor r (Y - X) (X + Y) (Q - N) (N + Q)) +
      (cutB r N Q / 2 - cutA r N Q) =
      (cutB r v w / 2 - cutA r v w) + d * endpointSlope r v w a b s u t +
        d ^ 2 * endpointRemainder r d v w a b s u t := by
  dsimp [cutB, cutA, endpointSlope, endpointRemainder, halfBiasRemainder, energyRemainder,
    adjacentRemainder, adjacentFactor]
  ring

/-- The common scalar `C` in the Gibbs endpoint gradients. -/
def gradientCoefficient (r : ℝ) : ℝ :=
  27 * (r - 1) / (4 * (r ^ 2 - r + 1) * (r ^ 2 + r + 1))

/-- The scaled lower linear cut cost on the Gibbs-relative spectrum. -/
def g0scaled (r d : ℝ) (h : Fin 4 → ℝ) : ℝ :=
  let g := gibbsLevels r
  gradientCoefficient r * (h 0 / r - h 2 / r ^ 2) +
    d * endpointRemainder r d (g 0) (g 1) (h 0) (h 1) (g 1) (h 1) (h 2)

/-- The scaled upper linear cut cost on the Gibbs-relative spectrum. -/
def g2scaled (r d : ℝ) (h : Fin 4 → ℝ) : ℝ :=
  let g := gibbsLevels r
  gradientCoefficient r * r * h 1 +
    d * endpointRemainder r d (g 2) (g 3) (h 2) 0 (g 1) (h 1) (h 2)

private theorem thermal_denominators {r : ℝ} (hr : 0 < r) :
    1 + r ^ 3 ≠ 0 ∧ r ^ 2 - r + 1 ≠ 0 ∧ r ^ 2 + r + 1 ≠ 0 := by
  exact ⟨by positivity, ne_of_gt (by nlinarith only [sq_nonneg (r - 1 / 2)]), by positivity⟩

private theorem endpoint_gibbs_constants {r : ℝ} (hr : 0 < r) :
    let g := gibbsLevels r
    cutB r (g 0) (g 1) / 2 - cutA r (g 0) (g 1) = 0 ∧
    cutB r (g 2) (g 3) / 2 - cutA r (g 2) (g 3) = 0 := by
  obtain ⟨hγ, _, hplus⟩ := thermal_denominators hr
  constructor <;> norm_num [gibbsLevels, cutA, cutB, c, e, bias, gamma] <;>
    field_simp [hr.ne', hγ, hplus] <;> ring

private theorem endpoint_gibbs_gradients {r : ℝ} (hr : 0 < r) (a b t : ℝ) :
    let g := gibbsLevels r
    endpointSlope r (g 0) (g 1) a b (g 1) b t =
      gradientCoefficient r * (a / r - t / r ^ 2) ∧
    endpointSlope r (g 2) (g 3) t 0 (g 1) b t =
      gradientCoefficient r * r * b := by
  obtain ⟨hγ, hminus, hplus⟩ := thermal_denominators hr
  have hC : gradientCoefficient r =
      27 * (r - 1) * (r + 1) / (4 * (1 + r ^ 3) * (r ^ 2 + r + 1)) := by
    unfold gradientCoefficient
    apply (div_eq_div_iff
      (mul_ne_zero (mul_ne_zero (by norm_num) hminus) hplus)
      (mul_ne_zero (mul_ne_zero (by norm_num) hγ) hplus)).2
    rw [show 1 + r ^ 3 = (r + 1) * (r ^ 2 - r + 1) by ring]
    ring
  constructor <;>
    rw [hC] <;>
    norm_num [gibbsLevels, endpointSlope, adjacentFactor, c, e, bias, gamma] <;>
    field_simp [hr.ne', hγ, hplus] <;> ring

theorem gibbs_middle_gap_eq (r d : ℝ) (h : Fin 4 → ℝ) :
    let x := fun i => gibbsLevels r i + d * h i
    x 2 - x 1 = d * (h 2 - h 1) := by
  change r⁻¹ + d * h 2 - (r⁻¹ + d * h 1) = _
  ring

/-- The two exact linear cost identities required by both Gibbs angular
minimum theorems. They hold also at zero displacement. -/
theorem gibbs_endpoint_linear_costs_eq {r : ℝ} (hr : 0 < r)
    (d : ℝ) (h : Fin 4 → ℝ) (hh : h 3 = 0) :
    let x := fun i => gibbsLevels r i + d * h i
    let m := x 0
    let n := x 1
    let q := x 2
    let E := cutEnergy r m n q
    let B := cutBias r m n q
    let L₀ := matchedMixture E B
    let P₀ := (E 0 + lowerCoeff r m n q - L₀) / 2
    let P₂ := (E 2 + upperCoeff r n q - L₀) / 2
    B 0 / 2 - 2 * P₀ = d * g0scaled r d h ∧ B 2 / 2 - 2 * P₂ = d * g2scaled r d h := by
  intro x m n q E B L₀ P₀ P₂
  let g := gibbsLevels r
  obtain ⟨hc₀, hc₂⟩ := endpoint_gibbs_constants hr
  obtain ⟨hs₀, hs₂⟩ := endpoint_gibbs_gradients hr (h 0) (h 1) (h 2)
  have hex₀ := endpoint_expansion r d (g 0) (g 1) (h 0) (h 1) (g 1) (h 1) (h 2)
  have hex₂ := endpoint_expansion r d (g 2) (g 3) (h 2) (h 3) (g 1) (h 1) (h 2)
  have hx3 : g 3 + d * h 3 = 1 := by rw [hh, mul_zero, add_zero]; rfl
  change cutB r m n / 2 - cutA r m n - (q - n) * lowerCoeffScaled r m n q +
    (cutB r n q / 2 - cutA r n q) = _ at hex₀
  dsimp only at hex₂ hc₀ hc₂ hs₀ hs₂
  rw [hx3, hh, hc₂, hs₂] at hex₂
  change cutB r q 1 / 2 - cutA r q 1 - (q - n) * upperCoeffScaled r n q +
    (cutB r n q / 2 - cutA r n q) = _ at hex₂
  rw [hc₀, hs₀] at hex₀
  constructor
  · calc
      B 0 / 2 - 2 * P₀ =
          cutB r m n / 2 - cutA r m n - (q - n) * lowerCoeffScaled r m n q +
            (cutB r n q / 2 - cutA r n q) := by
          simp [P₀, L₀, E, B, matchedMixture, cutEnergy, cutBias, lower_coeff_eq]
          ring
      _ = d * g0scaled r d h := by rw [hex₀]; simp only [g0scaled]; ring
  · calc
      B 2 / 2 - 2 * P₂ =
          cutB r q 1 / 2 - cutA r q 1 - (q - n) * upperCoeffScaled r n q +
            (cutB r n q / 2 - cutA r n q) := by
          simp [P₂, L₀, E, B, matchedMixture, cutEnergy, cutBias, upper_coeff_eq]
          ring
      _ = d * g2scaled r d h := by rw [hex₂]; simp only [g2scaled]; ring

#print axioms gibbs_endpoint_linear_costs_eq
#print axioms matched_mixture_comparisons
#print axioms refined_charge_comparisons
#print axioms refined_loss_eq
#print axioms long_coeff_eq

end D5.S3.Quantum.Semigroups.WuCubicGibbsScaledCoefficients
