/- GID: D5/S3/Quantum/Semigroups/WuCubicGibbsNormalizedJoin
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicGibbsNormalizedJoin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict positivity on Gibbs-normalized spectra from the rational angular tests. -/

import D5.S3.Quantum.Semigroups.WuCubicGibbsAngularMinimum
import D5.S3.Quantum.Semigroups.WuCubicGibbsScaledCoefficients
import OmegaBuild.Commands

/-! The lower and upper near-Gibbs tests for Wu v1 (3.54).
The scaled Schur complement is regular at zero displacement and the refined
charge comparison and square loss use the actual middle-gap coefficients.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicGibbsNormalizedJoin

open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate
open WuCubicOccupationTaylor
open WuCubicGibbsAngularMinimum
open WuCubicGibbsScaledCoefficients

/-- Turn the common-tilt numerator and scaled difference loss into strict
positivity of the true deficit at positive distance from Gibbs. -/
private theorem strict_of_schur_margin {d T p Jbar O g₀ g₂ b δ : ℝ}
    (hd : 0 < d) (hp : 0 < p)
    (hbound : d ^ 2 * (O - (g₀ + g₂) ^ 2 / (4 * p) -
      T * (g₀ - g₂ - b * (g₀ + g₂) / p) ^ 2 / (16 * Jbar)) ≤ δ)
    (hmargin : 0 < (4 * p * O - (g₀ + g₂) ^ 2) / (4 * p) -
      T * (g₀ - g₂ - b * (g₀ + g₂) / p) ^ 2 / (16 * Jbar)) :
    0 < δ := by
  have hcommon :
      (4 * p * O - (g₀ + g₂) ^ 2) / (4 * p) =
        O - (g₀ + g₂) ^ 2 / (4 * p) := by
    field_simp [hp.ne'] <;> ring
  rw [hcommon] at hmargin
  exact (mul_pos (pow_pos hd 2) hmargin).trans_le hbound

/-- The actual refined normalized test from the lower-Gibbs proof. The
hypotheses are spectral and do not divide by the middle gap or displacement.
The same implication holds on either side of the Gibbs wall whenever its
tests pass. In particular it includes the repeated-middle case `n = q`.

The denominator `Jbar` equals `(d*K)*(J-bdiff^2/(4*p))` for the refined
angular quadratic, with its long term `κ/(d*K)`. The coefficient of the
occupation term is the signed Taylor lower bound from WuCubicOccupationTaylor.
-/
theorem refined_normalized_positive {r d K : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hd : 0 < d) (hK : 1 ≤ K)
    (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + d * h i)
    (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i) :
    let x := fun i => gibbsLevels r i + d * h i
    let m := x 0
    let n := x 1
    let q := x 2
    let E := cutEnergy r m n q
    let B := cutBias r m n q
    let Z₀ := lowerCoeff r m n q
    let Z₂ := upperCoeff r n q
    let L₀ := matchedMixture E B
    let κ := longCoeff r m n q / 4
    let P₀ := (E 0 + Z₀ - L₀) / 2
    let P₂ := (E 2 + Z₂ - L₀) / 2
    let p := P₀ + P₂ + B 1 / 2
    let bdiff := P₀ - P₂
    let Lgap := refinedMixtureScaled r m n q
    let ellgap := refinedExcessScaled r m n q
    let loss := (q - n) * (ellgap / 4 +
      Lgap ^ 2 / (4 * (3 * middleEnergyScaled r n q + Lgap)))
    let Jbar := κ + d * K * ((P₀ + P₂) / 4 - loss - bdiff ^ 2 / (4 * p))
    let O := occupationTaylorCoefficient r d h
    let g₀ := g0scaled r d h
    let g₂ := g2scaled r d h
    m ≤ n → n ≤ q → q ≤ 1 →
    0 ≤ matchedMixtureScaled r n q → 0 ≤ ellgap →
    refinedHScaled r m n q * (d * K) / 2 ≤ ellgap →
    (q - n) * ellgap ≤ min (B 0) (B 2) →
    0 < P₀ → 0 < P₂ → 0 < p → L₀ / 4 ≤ κ →
    -2 * min 0 (min g₀ g₂) / min P₀ P₂ ≤ K → 0 < Jbar →
    0 < (4 * p * O - (g₀ + g₂) ^ 2) / (4 * p) -
      d * K * (g₀ - g₂ - bdiff * (g₀ + g₂) / p) ^ 2 / (16 * Jbar) →
    0 < normalizedDeficit r U m n q := by
  intro x m n q E B Z₀ Z₂ L₀ κ P₀ P₂ p bdiff Lgap ellgap loss Jbar O g₀ g₂
    hmn hnq hq1 hLgap hellgap hchargegap hend hP₀ hP₂ hp hκ hlarge hJbar hmargin
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hadm : 0 ≤ L₀ ∧ L₀ ≤ Z₀ ∧ L₀ ≤ Z₂ :=
    matched_mixture_comparisons (r := r) (m := m) hnq (fun _ => ⟨hLgap, hellgap⟩)
  let L := min Z₀ Z₂
  let ell := L - L₀
  let H := E 1 + L
  have hcharge : H * (d * K) / 2 ≤ ell ∧ ell ≤ min (B 0) (B 2) :=
    refined_charge_comparisons (r := r) (m := m) (T := d * K) hnq (fun _ => hchargegap) hend
  have hell : ell = (q - n) * ellgap := refined_excess_eq (r := r) (m := m) hnq
  have hLsq : L ^ 2 / (4 * (3 * E 1 + L)) =
      (q - n) * (Lgap ^ 2 / (4 * (3 * middleEnergyScaled r n q + Lgap))) :=
    refined_loss_eq (r := r) (m := m) hnq
  have hloss : ell / 4 + L ^ 2 / (4 * (3 * E 1 + L)) = loss := by
    rw [hell, hLsq]
    dsimp only [loss]
    ring
  let A := κ + d * K * ((P₀ + P₂) / 4 -
      (ell / 4 + L ^ 2 / (4 * (3 * E 1 + L))) - bdiff ^ 2 / (4 * p))
  have hAeq : A = Jbar := by
    dsimp only [A]
    rw [hloss] <;> rfl
  have hA : 0 < A := by rw [hAeq]; exact hJbar
  obtain ⟨hG₀, hG₂⟩ := gibbs_endpoint_linear_costs_eq (zero_lt_one.trans_le hr) d h hh
  have hbound : d ^ 2 * (O - (g₀ + g₂) ^ 2 / (4 * p) -
      d * K * (g₀ - g₂ - bdiff * (g₀ + g₂) / p) ^ 2 / (16 * A)) ≤
      normalizedDeficit r U m n q :=
    refined_gibbs_angular_minimum (r := r) (d := d) (K := K) (g₀ := g₀) (g₂ := g₂)
      U hr hd hKpos h hh hx hg
      hmn hnq hq1 (fun _ => hadm) (fun _ => hcharge) hP₀ hP₂ hκ hG₀ hG₂ hlarge hA
  rw [hAeq] at hbound
  exact strict_of_schur_margin hd hp hbound hmargin

/-- The matched test from the upper-Gibbs proof, using the same exact scaled
linear costs and the occupation Taylor polynomial, but with no refined
charge or square-loss term. Repeated middle eigenvalues are allowed. -/
theorem matched_normalized_positive {r d K : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hd : 0 < d) (hK : 1 ≤ K)
    (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + d * h i)
    (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i) :
    let x := fun i => gibbsLevels r i + d * h i
    let m := x 0
    let n := x 1
    let q := x 2
    let E := cutEnergy r m n q
    let B := cutBias r m n q
    let Z₀ := lowerCoeff r m n q
    let Z₂ := upperCoeff r n q
    let L₀ := matchedMixture E B
    let κ := longCoeff r m n q / 4
    let P₀ := (E 0 + Z₀ - L₀) / 2
    let P₂ := (E 2 + Z₂ - L₀) / 2
    let p := P₀ + P₂
    let bdiff := P₀ - P₂
    let Jbar := κ + d * K * (p / 4 - L₀ / 4 - bdiff ^ 2 / (4 * p))
    let O := occupationTaylorCoefficient r d h
    let g₀ := g0scaled r d h
    let g₂ := g2scaled r d h
    m ≤ n → n ≤ q → q ≤ 1 →
    0 ≤ matchedMixtureScaled r n q → 0 ≤ refinedExcessScaled r m n q →
    0 < P₀ → 0 < P₂ → L₀ / 4 ≤ κ →
    -2 * min 0 (min g₀ g₂) / min P₀ P₂ ≤ K → 0 < Jbar →
    0 < (4 * p * O - (g₀ + g₂) ^ 2) / (4 * p) -
      d * K * (g₀ - g₂ - bdiff * (g₀ + g₂) / p) ^ 2 / (16 * Jbar) →
    0 < normalizedDeficit r U m n q := by
  intro x m n q E B Z₀ Z₂ L₀ κ P₀ P₂ p bdiff Jbar O g₀ g₂
    hmn hnq hq1 hLgap hellgap hP₀ hP₂ hκ hlarge hJbar hmargin
  have hp : 0 < p := add_pos hP₀ hP₂
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hadm : 0 ≤ L₀ ∧ L₀ ≤ Z₀ ∧ L₀ ≤ Z₂ :=
    matched_mixture_comparisons (r := r) (m := m) hnq (fun _ => ⟨hLgap, hellgap⟩)
  obtain ⟨hG₀, hG₂⟩ := gibbs_endpoint_linear_costs_eq (zero_lt_one.trans_le hr) d h hh
  have hbound : d ^ 2 * (O - (g₀ + g₂) ^ 2 / (4 * p) -
      d * K * (g₀ - g₂ - bdiff * (g₀ + g₂) / p) ^ 2 / (16 * Jbar)) ≤
      normalizedDeficit r U m n q :=
    matched_gibbs_angular_minimum (r := r) (d := d) (K := K) (g₀ := g₀) (g₂ := g₂)
      U hr hd hKpos h hh hx hg
      hmn hnq hq1 (fun _ => hadm) hP₀ hP₂ hκ hG₀ hG₂ hlarge hJbar
  exact strict_of_schur_margin hd hp hbound hmargin

/-- In a normalized sorted pair, an extreme absolute coordinate forces the
lower coordinate to be minus one or the upper coordinate to be one. -/
private theorem middle_faces {a b : ℝ} (hab : a ≤ b) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hn : |a| = 1 ∨ |b| = 1) : a = -1 ∨ b = 1 := by
  obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  rcases hn with ha' | hb'
  · by_cases hpos : 0 ≤ a
    · rw [abs_of_nonneg hpos] at ha'
      right
      linarith
    · rw [abs_of_neg (lt_of_not_ge hpos)] at ha'
      left
      linarith
  · by_cases hpos : 0 ≤ b
    · rw [abs_of_nonneg hpos] at hb'
      exact Or.inr hb'
    · rw [abs_of_neg (lt_of_not_ge hpos)] at hb'
      left
      linarith

/-- The three signed faces exhaust each normalized sorted Gibbs cone. The
sign is minus one on the lower side and plus one on the upper side. -/
theorem signed_normalized_faces (h : Fin 4 → ℝ) {s : ℝ}
    (hs : s = -1 ∨ s = 1) (hside : 0 ≤ s * h 0) (horder : h 1 ≤ h 2)
    (hbound : ∀ i, |h i| ≤ 1)
    (hnorm : |h 0| = 1 ∨ |h 1| = 1 ∨ |h 2| = 1) :
    h 0 = s ∨ h 1 = -1 ∨ h 2 = 1 := by
  rcases hnorm with h₀ | hm
  · left
    rcases hs with hs | hs
    · rw [hs] at hside ⊢
      have hn : h 0 ≤ 0 := by linarith
      rw [abs_of_nonpos hn] at h₀
      linarith
    · rw [hs, one_mul] at hside
      rw [abs_of_nonneg hside] at h₀
      exact h₀.trans hs.symm
  · exact Or.inr (middle_faces horder (hbound 1) (hbound 2) hm)

#print axioms refined_normalized_positive
#print axioms matched_normalized_positive
#print axioms signed_normalized_faces

end D5.S3.Quantum.Semigroups.WuCubicGibbsNormalizedJoin
