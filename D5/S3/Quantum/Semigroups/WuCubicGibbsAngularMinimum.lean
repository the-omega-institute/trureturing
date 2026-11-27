/- GID: D5/S3/Quantum/Semigroups/WuCubicGibbsAngularMinimum
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicGibbsAngularMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gibbs-relative angular elimination for the normalized two-CAR Wu cubic deficit. -/

import D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
import D5.S3.Quantum.Semigroups.WuCubicOccupationTaylor
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! The matched and refined angular minima in the near-Gibbs Wu cubic proof.
The large-tilt bound uses the matched charges in both cases. The small-tilt
bound uses the total tilt and its difference as the two square variables. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicGibbsAngularMinimum

open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate
open WuCubicOccupationTaylor (gibbsLevels occupationTaylorCoefficient occupation_taylor_lower_bound)
open private odd_mass_mem from D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing
open private spectral_coefficients_nonneg crossCoeff directedCoeff from
  D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open private cutA cutB from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

/-- Complete the square in the common tilt, then in the tilt difference.
Here `T = d * K` and `C` is the unscaled constant part of the difference coefficient. -/
private theorem two_squares {d T p b κ C g₀ g₂ S F : ℝ}
    (hT : 0 < T) (hp : 0 < p) :
    let A := κ + T * (C - b ^ 2 / (4 * p))
    0 < A →
    -(d ^ 2 * ((g₀ + g₂) ^ 2 / (4 * p) +
      T * (g₀ - g₂ - b * (g₀ + g₂) / p) ^ 2 / (16 * A))) ≤
    p * S ^ 2 / 4 + d * (g₀ + g₂) * S / 2 +
      (b * S + d * (g₀ - g₂)) * F / 2 + (κ / T + C) * F ^ 2 := by
  intro A hA
  let G := g₀ + g₂
  let V := g₀ - g₂ - b * G / p
  have hscaled : κ / T + C - b ^ 2 / (4 * p) = A / T := by
    dsimp only [A]
    field_simp [hT.ne', hp.ne']
    ring
  have hfirst :
      p * S ^ 2 / 4 + d * G * S / 2 +
        (b * S + d * (g₀ - g₂)) * F / 2 + (κ / T + C) * F ^ 2 =
      p / 4 * (S + (d * G + b * F) / p) ^ 2 -
        d ^ 2 * (G ^ 2 / (4 * p)) + (A / T * F ^ 2 + d * V * F / 2) := by
    rw [← hscaled]
    dsimp only [V]
    field_simp [hp.ne', hT.ne']
    ring
  have hsecond :
      A / T * F ^ 2 + d * V * F / 2 =
      A / T * (F + T * d * V / (4 * A)) ^ 2 -
        d ^ 2 * (T * V ^ 2 / (16 * A)) := by
    field_simp [hA.ne', hT.ne']
    ring
  change -(d ^ 2 * (G ^ 2 / (4 * p) + T * V ^ 2 / (16 * A))) ≤ _
  rw [hfirst, hsecond]
  linarith only [
    mul_nonneg (div_nonneg hp.le (by norm_num : (0 : ℝ) ≤ 4))
      (sq_nonneg (S + (d * G + b * F) / p)),
    mul_nonneg (div_nonneg hA.le hT.le) (sq_nonneg (F + T * d * V / (4 * A)))]

private theorem oddTilt_nonneg (U : unitary Mat) (i : Fin 4) : 0 ≤ oddTilt U i :=
  mul_nonneg (by norm_num) (odd_mass_mem U i).1

private theorem large_tilt_nonneg {d K P₀ P₂ g₀ g₂ a b : ℝ}
    (hd : 0 < d) (hP₀ : 0 < P₀) (hP₂ : 0 < P₂) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hK : -2 * min 0 (min g₀ g₂) / min P₀ P₂ ≤ K) (hS : d * K ≤ a + b) :
    0 ≤ P₀ * a ^ 2 + P₂ * b ^ 2 + d * g₀ * a + d * g₂ * b := by
  let P := min P₀ P₂
  let g := min 0 (min g₀ g₂)
  have hP : 0 < P := lt_min hP₀ hP₂
  have hthreshold := mul_le_mul_of_nonneg_left ((div_le_iff₀ hP).mp hK) hd.le
  change d * (-2 * g) ≤ d * (K * P) at hthreshold
  have hS' := mul_le_mul_of_nonneg_left hS hP.le
  have hslope : 0 ≤ P * (a + b) / 2 + d * g := by
    linarith only [hthreshold, hS']
  have hcommon := mul_nonneg (add_nonneg ha hb) hslope
  have hdiff := mul_nonneg hP.le (sq_nonneg (a - b))
  have hg₀ : g ≤ g₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hg₂ : g ≤ g₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hquad₀ := mul_le_mul_of_nonneg_right (show P ≤ P₀ from min_le_left _ _) (sq_nonneg a)
  have hquad₂ := mul_le_mul_of_nonneg_right (show P ≤ P₂ from min_le_right _ _) (sq_nonneg b)
  have hlin₀ := mul_le_mul_of_nonneg_right hg₀ (mul_nonneg hd.le ha)
  have hlin₂ := mul_le_mul_of_nonneg_right hg₂ (mul_nonneg hd.le hb)
  linarith only [hcommon, hdiff, hquad₀, hquad₂, hlin₀, hlin₂]

private theorem angular_minimum (U : unitary Mat)
    {d K P₀ P₂ g₀ g₂ κ L₀ gain loss O occ δ : ℝ}
    (hd : 0 < d) (hK : 0 < K) (hP₀ : 0 < P₀) (hP₂ : 0 < P₂)
    (hκ : L₀ / 4 ≤ κ) (hL₀ : 0 ≤ L₀) (hgain : 0 ≤ gain)
    (hlarge : -2 * min 0 (min g₀ g₂) / min P₀ P₂ ≤ K) (hO : d ^ 2 * O ≤ occ) :
    let a := oddTilt U 0
    let b := oddTilt U 3
    let S := tiltSum U
    let F := tiltDiff U
    let single := P₀ * a ^ 2 + P₂ * b ^ 2 + d * g₀ * a + d * g₂ * b
    let p := P₀ + P₂ + gain
    let A := κ + d * K * ((P₀ + P₂) / 4 - loss - (P₀ - P₂) ^ 2 / (4 * p))
    0 < A →
    occ + single + (κ * longFactor S - L₀ / 4) * F ^ 2 ≤ δ →
    (S ≤ d * K → occ + single + gain / 4 * S ^ 2 + (κ * longFactor S - loss) * F ^ 2 ≤ δ) →
    d ^ 2 * (O - (g₀ + g₂) ^ 2 / (4 * p) -
      d * K * (g₀ - g₂ - (P₀ - P₂) * (g₀ + g₂) / p) ^ 2 / (16 * A)) ≤ δ := by
  intro a b S F single p A hA hmatched hsmall
  have ha : 0 ≤ a := oddTilt_nonneg U 0
  have hb : 0 ≤ b := oddTilt_nonneg U 3
  have hsum : S = a + b := rfl
  have hdiff : F = a - b := rfl
  have hp : 0 < p := add_pos_of_pos_of_nonneg (add_pos hP₀ hP₂) hgain
  have hκ₀ : 0 ≤ κ := (div_nonneg hL₀ (by norm_num)).trans hκ
  have hT : 0 < d * K := mul_pos hd hK
  have hcommon : 0 ≤ (g₀ + g₂) ^ 2 / (4 * p) := by positivity
  have hdiffLoss : 0 ≤
      d * K * (g₀ - g₂ - (P₀ - P₂) * (g₀ + g₂) / p) ^ 2 / (16 * A) := by positivity
  have hbase : d ^ 2 * (O - (g₀ + g₂) ^ 2 / (4 * p) -
      d * K * (g₀ - g₂ - (P₀ - P₂) * (g₀ + g₂) / p) ^ 2 / (16 * A)) ≤ occ :=
    (mul_le_mul_of_nonneg_left ((sub_le_self _ hdiffLoss).trans (sub_le_self _ hcommon))
      (sq_nonneg d)).trans hO
  by_cases hzero : S = 0
  · have ha₀ : a = 0 := by linarith only [ha, hb, hsum, hzero]
    have hb₀ : b = 0 := by linarith only [ha, hb, hsum, hzero]
    have hF₀ : F = 0 := by rw [hdiff, ha₀, hb₀, sub_self]
    have hsingle₀ : single = 0 := by simp [single, ha₀, hb₀]
    apply hbase.trans
    simpa [hsingle₀, hF₀] using hmatched
  have hS₀ : 0 ≤ S := by rw [hsum]; exact add_nonneg ha hb
  have hS : 0 < S := lt_of_le_of_ne hS₀ (Ne.symm hzero)
  by_cases hbig : d * K ≤ S
  · have hsingle : 0 ≤ single :=
      large_tilt_nonneg hd hP₀ hP₂ ha hb hlarge (by simpa only [hsum] using hbig)
    have hlong : 1 ≤ longFactor S := by simp only [longFactor, ite_eq_right hzero, le_max_left]
    have hpenalty : 0 ≤ (κ * longFactor S - L₀ / 4) * F ^ 2 := by
      have hκlong := mul_le_mul_of_nonneg_left hlong hκ₀
      rw [mul_one] at hκlong
      exact mul_nonneg (sub_nonneg.mpr (hκ.trans hκlong)) (sq_nonneg F)
    exact hbase.trans ((le_add_of_nonneg_right hsingle).trans
      ((le_add_of_nonneg_right hpenalty).trans hmatched))
  · have hST : S ≤ d * K := le_of_lt (lt_of_not_ge hbig)
    have hlong : 1 / (d * K) ≤ longFactor S := by
      rw [longFactor, ite_eq_right hzero]
      exact (one_div_le_one_div_of_le hS hST).trans (le_max_right _ _)
    have hpenalty := mul_le_mul_of_nonneg_right
      (sub_le_sub_right (mul_le_mul_of_nonneg_left hlong hκ₀) loss) (sq_nonneg F)
    have hquad :
        single + gain / 4 * S ^ 2 + (κ / (d * K) - loss) * F ^ 2 =
        p * S ^ 2 / 4 + d * (g₀ + g₂) * S / 2 +
          ((P₀ - P₂) * S + d * (g₀ - g₂)) * F / 2 +
          (κ / (d * K) + ((P₀ + P₂) / 4 - loss)) * F ^ 2 := by
      dsimp only [single, p]
      rw [hsum, hdiff]
      ring
    have hsq := two_squares (d := d) (g₀ := g₀) (g₂ := g₂) (S := S) (F := F)
      (C := (P₀ + P₂) / 4 - loss) (b := P₀ - P₂) hT hp hA
    rw [← hquad] at hsq
    rw [mul_one_div] at hpenalty
    linarith only [hsq, hpenalty, hO, hsmall hST]

private theorem repeated_middle_coefficients (r m n : ℝ) :
    cutEnergy r m n n 1 = 0 ∧ cutBias r m n n 1 = 0 ∧
      lowerCoeff r m n n = 0 ∧ upperCoeff r n n = 0 := by
  exact ⟨by simp [cutEnergy, cutA], by simp [cutBias, cutB],
    by simp [lowerCoeff, crossCoeff, directedCoeff],
    by simp [upperCoeff, crossCoeff, directedCoeff]⟩

private theorem matched_mixture_admissible {r m n q : ℝ} (hnq : n ≤ q) :
    let L₀ := matchedMixture (cutEnergy r m n q) (cutBias r m n q)
    (n < q → 0 ≤ L₀ ∧ L₀ ≤ lowerCoeff r m n q ∧ L₀ ≤ upperCoeff r n q) →
    0 ≤ L₀ ∧ L₀ ≤ lowerCoeff r m n q ∧ L₀ ≤ upperCoeff r n q := by
  intro L₀ h
  rcases eq_or_lt_of_le hnq with hq | hq
  · subst q
    obtain ⟨hA₁, hB₁, hleft, hright⟩ := repeated_middle_coefficients r m n
    simp [L₀, matchedMixture, hA₁, hB₁, hleft, hright]
  · exact h hq

private theorem occupation_taylor_for_cuts {r d : ℝ} (hr : 1 ≤ r) (hd : 0 < d)
    (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + d * h i) (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i) :
    let x := fun i => gibbsLevels r i + d * h i
    d ^ 2 * occupationTaylorCoefficient r d h ≤ occupationDeficit r (x 0) (x 1) (x 2) := by
  intro x
  have hx₀ : 0 ≤ x 0 := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hx 0)
  have hx₁ : 0 ≤ x 1 := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hx 1)
  have hx₂ : 0 ≤ x 2 := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hx 2)
  rw [← occupation_deficit_eq hr hx₀ hx₁ hx₂]
  exact occupation_taylor_lower_bound hr hd.le h hh hx hg

/-- The matched Gibbs-relative lower bound, using the common adjacent mixture
`L₀ = B 1 / 2 - E 1`. All coefficient inequalities are spectral. -/
theorem matched_gibbs_angular_minimum {r d K g₀ g₂ : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hd : 0 < d) (hK : 0 < K)
    (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + d * h i) (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i) :
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
    let A := κ + d * K * (p / 4 - L₀ / 4 - (P₀ - P₂) ^ 2 / (4 * p))
    let O := occupationTaylorCoefficient r d h
    m ≤ n → n ≤ q → q ≤ 1 →
    (n < q → 0 ≤ L₀ ∧ L₀ ≤ Z₀ ∧ L₀ ≤ Z₂) →
    0 < P₀ → 0 < P₂ → L₀ / 4 ≤ κ →
    B 0 / 2 - 2 * P₀ = d * g₀ → B 2 / 2 - 2 * P₂ = d * g₂ →
    -2 * min 0 (min g₀ g₂) / min P₀ P₂ ≤ K → 0 < A →
    d ^ 2 * (O - (g₀ + g₂) ^ 2 / (4 * p) -
      d * K * (g₀ - g₂ - (P₀ - P₂) * (g₀ + g₂) / p) ^ 2 / (16 * A)) ≤
      normalizedDeficit r U m n q := by
  intro x m n q E B Z₀ Z₂ L₀ κ P₀ P₂ p A O hmn hnq hq1 hadm hP₀ hP₂ hκ hG₀ hG₂ hlarge hA
  have hm : 0 ≤ m := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hx 0)
  obtain ⟨hL₀, hleft, hright⟩ := matched_mixture_admissible hnq hadm
  have hmatched := matched_deficit_bound U hr hm hmn hnq hq1 hL₀ hleft hright
  change occupationDeficit r m n q +
    (P₀ * oddTilt U 0 ^ 2 + P₂ * oddTilt U 3 ^ 2 +
      (B 0 / 2 - 2 * P₀) * oddTilt U 0 + (B 2 / 2 - 2 * P₂) * oddTilt U 3) +
    (κ * longFactor (tiltSum U) - L₀ / 4) * tiltDiff U ^ 2 ≤ _ at hmatched
  rw [hG₀, hG₂] at hmatched
  have hO := occupation_taylor_for_cuts hr hd h hh hx hg
  have hAz : 0 < κ + d * K *
      ((P₀ + P₂) / 4 - L₀ / 4 - (P₀ - P₂) ^ 2 / (4 * (P₀ + P₂ + 0))) := by
    simpa only [add_zero] using hA
  simpa only [add_zero] using
    angular_minimum U (gain := 0) (loss := L₀ / 4) hd hK hP₀ hP₂ hκ hL₀ le_rfl hlarge hO
      hAz hmatched (fun _ => by simpa only [zero_div, zero_mul, add_zero] using hmatched)

/-- The refined Gibbs-relative lower bound. The charge test at the tilt
threshold implies admissibility throughout the small-tilt branch. -/
theorem refined_gibbs_angular_minimum {r d K g₀ g₂ : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hd : 0 < d) (hK : 0 < K)
    (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + d * h i) (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i) :
    let x := fun i => gibbsLevels r i + d * h i
    let m := x 0
    let n := x 1
    let q := x 2
    let E := cutEnergy r m n q
    let B := cutBias r m n q
    let Z₀ := lowerCoeff r m n q
    let Z₂ := upperCoeff r n q
    let L₀ := matchedMixture E B
    let L := min Z₀ Z₂
    let ell := L - L₀
    let H := E 1 + L
    let κ := longCoeff r m n q / 4
    let P₀ := (E 0 + Z₀ - L₀) / 2
    let P₂ := (E 2 + Z₂ - L₀) / 2
    let p := P₀ + P₂ + B 1 / 2
    let A := κ + d * K * ((P₀ + P₂) / 4 - (ell / 4 + L ^ 2 / (4 * (3 * E 1 + L))) -
      (P₀ - P₂) ^ 2 / (4 * p))
    let O := occupationTaylorCoefficient r d h
    m ≤ n → n ≤ q → q ≤ 1 →
    (n < q → 0 ≤ L₀ ∧ L₀ ≤ Z₀ ∧ L₀ ≤ Z₂) →
    (n < q → H * (d * K) / 2 ≤ ell ∧ ell ≤ min (B 0) (B 2)) →
    0 < P₀ → 0 < P₂ → L₀ / 4 ≤ κ →
    B 0 / 2 - 2 * P₀ = d * g₀ → B 2 / 2 - 2 * P₂ = d * g₂ →
    -2 * min 0 (min g₀ g₂) / min P₀ P₂ ≤ K → 0 < A →
    d ^ 2 * (O - (g₀ + g₂) ^ 2 / (4 * p) -
      d * K * (g₀ - g₂ - (P₀ - P₂) * (g₀ + g₂) / p) ^ 2 / (16 * A)) ≤
      normalizedDeficit r U m n q := by
  intro x m n q E B Z₀ Z₂ L₀ L ell H κ P₀ P₂ p A O hmn hnq hq1 hadm hcharge
    hP₀ hP₂ hκ hG₀ hG₂ hlarge hA
  have hm : 0 ≤ m := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hx 0)
  obtain ⟨hE, hB, _⟩ := spectral_coefficients_nonneg hr hm hmn hnq hq1
  obtain ⟨hL₀, hleft, hright⟩ := matched_mixture_admissible hnq hadm
  have hL : 0 ≤ L := hL₀.trans (le_min hleft hright)
  have hH : 0 ≤ H := add_nonneg (hE 1) hL
  have hlegal : H * (d * K) / 2 ≤ ell ∧ ell ≤ min (B 0) (B 2) := by
    rcases eq_or_lt_of_le hnq with heq | hlt
    · obtain ⟨hE₁, hB₁, hZ₀, hZ₂⟩ := repeated_middle_coefficients r m n
      have hE' : E 1 = 0 := show cutEnergy r m n q 1 = 0 by rw [← heq]; exact hE₁
      have hB' : B 1 = 0 := show cutBias r m n q 1 = 0 by rw [← heq]; exact hB₁
      have hZ₀' : Z₀ = 0 := show lowerCoeff r m n q = 0 by rw [← heq]; exact hZ₀
      have hZ₂' : Z₂ = 0 := show upperCoeff r n q = 0 by rw [← heq]; exact hZ₂
      simpa [H, ell, L, L₀, matchedMixture, hE', hB', hZ₀', hZ₂'] using le_min (hB 0) (hB 2)
    · exact hcharge hlt
  have hmatched := matched_deficit_bound U hr hm hmn hnq hq1 hL₀ hleft hright
  change occupationDeficit r m n q +
    (P₀ * oddTilt U 0 ^ 2 + P₂ * oddTilt U 3 ^ 2 +
      (B 0 / 2 - 2 * P₀) * oddTilt U 0 + (B 2 / 2 - 2 * P₂) * oddTilt U 3) +
    (κ * longFactor (tiltSum U) - L₀ / 4) * tiltDiff U ^ 2 ≤ _ at hmatched
  rw [hG₀, hG₂] at hmatched
  have hO := occupation_taylor_for_cuts hr hd h hh hx hg
  refine angular_minimum U (gain := B 1 / 2) (loss := ell / 4 + L ^ 2 / (4 * (3 * E 1 + L)))
    hd hK hP₀ hP₂ hκ hL₀ (div_nonneg (hB 1) (by norm_num)) hlarge hO hA hmatched ?_
  intro hS
  have hs := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS hH)
    (by norm_num : (0 : ℝ) ≤ 2)).trans hlegal.1
  have hrefined := refined_deficit_bound U hr hm hmn hnq hq1 hL₀ hleft hright hs hlegal.2
  change occupationDeficit r m n q +
    (P₀ * oddTilt U 0 ^ 2 + P₂ * oddTilt U 3 ^ 2 +
      (B 0 / 2 - 2 * P₀) * oddTilt U 0 + (B 2 / 2 - 2 * P₂) * oddTilt U 3) +
    B 1 / 8 * tiltSum U ^ 2 +
    (κ * longFactor (tiltSum U) - ell / 4 - L ^ 2 / (4 * (3 * E 1 + L))) *
      tiltDiff U ^ 2 ≤ _ at hrefined
  rw [hG₀, hG₂] at hrefined
  dsimp only
  linarith only [hrefined]

#print axioms matched_gibbs_angular_minimum
#print axioms refined_gibbs_angular_minimum

end D5.S3.Quantum.Semigroups.WuCubicGibbsAngularMinimum
