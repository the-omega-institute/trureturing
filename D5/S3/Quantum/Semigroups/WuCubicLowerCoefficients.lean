/- GID: D5/S3/Quantum/Semigroups/WuCubicLowerCoefficients
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicLowerCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Divided coefficient identities for the lower near-Gibbs Wu cubic tests. -/

import D5.S3.Quantum.Semigroups.WuCubicRefinedHellinger
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuCubicLowerCoefficients

open WuCubicAngularCertificate
open WuCubicHellingerMatrix (Vec3 levels lowerWeight upperWeight longCrossing lowerTilt upperTilt)
open WuCubicGibbsScaledCoefficients
open WuCubicOccupationTaylor (gibbsLevels)
open private c e cutB from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private adjacentFactor from D5.S3.Quantum.Semigroups.WuCubicGibbsScaledCoefficients
open private leftGap middleGap rightGap fieldOverGap gap_scaling bias_scaling
  cut_scaling lowerTiltFactor upperTiltFactor lowerTilt_dot upperTilt_dot tilt_scaling
  matchedLower matchedUpper from D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix

def radius : ℚ := 1 / 256

def offsets (y₀ y₁ blend : ℝ) : Vec3 :=
  ![y₀, y₁, y₁ + ((radius : ℝ) - y₁) * blend]

/-- The coefficient left after extracting `(r - 1) * (q - n)` from the middle bias. -/
def biasFactor (r u v s : ℝ) : ℝ :=
  fieldOverGap r * (u ^ 2 + u * v + v ^ 2) + 2 * e r * (r - 1) * s ^ 2

def middleBias (r : ℝ) (y : Vec3) : ℝ :=
  biasFactor r (levels r y 1) (levels r y 2) (middleGap r y)

def mixture (r : ℝ) (y : Vec3) : ℝ :=
  middleBias r y / 2 - c r * middleGap r y * (levels r y 1 + levels r y 2)

def lowerAdjacent (r : ℝ) (y : Vec3) : ℝ :=
  leftGap r y * (c r * (levels r y 0 + 2 * levels r y 1 + levels r y 2) -
    3 * e r * (r - 1) * (leftGap r y + middleGap r y))

def upperAdjacent (r : ℝ) (y : Vec3) : ℝ :=
  rightGap r y * (c r * (levels r y 1 + 2 * levels r y 2 + 1) -
    3 * e r * (r - 1) * (rightGap r y + middleGap r y))

def lowerBias (r : ℝ) (y : Vec3) : ℝ :=
  leftGap r y * biasFactor r (levels r y 0) (levels r y 1) (leftGap r y)

def upperBias (r : ℝ) (y : Vec3) : ℝ :=
  rightGap r y * biasFactor r (levels r y 2) 1 (rightGap r y)

def weight (r : ℝ) (y : Vec3) : ℝ :=
  lowerWeight r y + upperWeight r y + middleGap r y * middleBias r y / 2

def asymmetry (r : ℝ) (y : Vec3) : ℝ :=
  (lowerWeight r y - upperWeight r y) / weight r y

def lowerSlope (r : ℝ) (y : Vec3) : ℝ :=
  lowerTiltFactor r y * ((r * y 0 - y 2) / (r - 1))

def upperSlope (r : ℝ) (y : Vec3) : ℝ :=
  upperTiltFactor r y * (y 1 / (r - 1))

def residual (r : ℝ) (y : Vec3) : ℝ :=
  (1 - asymmetry r y) * lowerSlope r y - (1 + asymmetry r y) * upperSlope r y

def linearPivot (r : ℝ) (y : Vec3) : ℝ :=
  longCrossing r y - asymmetry r y * residual r y

def tests (r : ℝ) (y : Vec3) : Fin 11 → ℝ :=
  let l₀ := mixture r y
  let ell := middleBias r y / 4
  let mix := l₀ + ell
  let s := middleGap r y
  let p₀ := lowerWeight r y
  let p₂ := upperWeight r y
  let qa := (2 / 3) * (p₀ + p₂)
  let qb := lowerSlope r y - upperSlope r y - (4 / 3) * p₂
  let qc := (2 / 3) * p₂ + upperSlope r y
  ![l₀, lowerAdjacent r y - mix, upperAdjacent r y - mix, p₀, p₂,
    lowerBias r y - s * ell, upperBias r y - s * ell, longCrossing r y - s * l₀,
    weight r y * (p₀ + p₂ - s * (ell + mix)) - (p₀ - p₂) ^ 2,
    linearPivot r y, 4 * qa * qc - qb ^ 2]

private theorem cutB_factor (r u v l : ℝ) (h : v - u = (r - 1) * l) :
    cutB r u v = (r - 1) ^ 2 * (l * biasFactor r u v l) := by
  unfold cutB biasFactor
  rw [show v ^ 3 - u ^ 3 = (v - u) * (u ^ 2 + u * v + v ^ 2) by ring,
    h, bias_scaling]
  ring

/-- These factorizations use multiplication by the middle gap. They also hold at `q = n`. -/
theorem cut_factors {r : ℝ} (hr : 1 < r) (y : Vec3) :
    let m := levels r y 0
    let n := levels r y 1
    let q := levels r y 2
    let t := r - 1
    let B := cutBias r m n q
    B 0 = t ^ 2 * lowerBias r y ∧
    B 1 = t ^ 2 * (middleGap r y * middleBias r y) ∧
    B 2 = t ^ 2 * upperBias r y ∧
    matchedMixture (cutEnergy r m n q) B = t ^ 2 * (middleGap r y * mixture r y) ∧
    lowerCoeff r m n q = t ^ 2 * (middleGap r y * lowerAdjacent r y) ∧
    upperCoeff r n q = t ^ 2 * (middleGap r y * upperAdjacent r y) := by
  intro m n q t B
  obtain ⟨hl, hs, hu⟩ := gap_scaling hr y
  change n - m = t * leftGap r y at hl
  change q - n = t * middleGap r y at hs
  change 1 - q = t * rightGap r y at hu
  have hb₀ : B 0 = t ^ 2 * lowerBias r y := cutB_factor r m n _ hl
  have hb₁ : B 1 = t ^ 2 * (middleGap r y * middleBias r y) := cutB_factor r n q _ hs
  have hb₂ : B 2 = t ^ 2 * upperBias r y := cutB_factor r q 1 _ hu
  refine ⟨hb₀, hb₁, hb₂, ?_, ?_, ?_⟩
  · rw [matchedMixture, hb₁, middle_energy_eq, middleEnergyScaled, hs]
    change _ = t ^ 2 * (middleGap r y *
      (middleBias r y / 2 - c r * middleGap r y * (n + q)))
    ring
  · rw [lower_coeff_eq, lowerCoeffScaled, adjacentFactor, hl, hs]
    change _ = t ^ 2 * (middleGap r y * (leftGap r y *
      (c r * (m + 2 * n + q) - 3 * e r * t * (leftGap r y + middleGap r y))))
    ring
  · rw [upper_coeff_eq, upperCoeffScaled, adjacentFactor, hs, hu]
    change _ = t ^ 2 * (middleGap r y * (rightGap r y *
      (c r * (n + 2 * q + 1) - 3 * e r * t * (rightGap r y + middleGap r y))))
    ring

/-- The physical endpoint costs have a common factor `(r - 1)^2`. -/
theorem slope_factors {r : ℝ} (hr : 1 < r) (y : Vec3) :
    let m := levels r y 0
    let n := levels r y 1
    let q := levels r y 2
    cutBias r m n q 0 / 2 - 2 * matchedLower r m n q = (r - 1) ^ 2 * lowerSlope r y ∧
    cutBias r m n q 2 / 2 - 2 * matchedUpper r m n q = (r - 1) ^ 2 * upperSlope r y := by
  intro m n q
  let h : Fin 4 → ℝ := Fin.lastCases 0 y
  have hh : h 3 = 0 := rfl
  have hy : WuCubicHellingerMatrix.displacement 1 h = y := by
    funext i
    simp [WuCubicHellingerMatrix.displacement, h]
  obtain ⟨hg₀, hg₂⟩ := gibbs_endpoint_linear_costs_eq (zero_lt_one.trans hr) 1 h hh
  obtain ⟨ht₀, ht₂⟩ := tilt_scaling hr (d := 1) (by norm_num) h hh
  change cutBias r (levels r (WuCubicHellingerMatrix.displacement 1 h) 0)
      (levels r (WuCubicHellingerMatrix.displacement 1 h) 1)
      (levels r (WuCubicHellingerMatrix.displacement 1 h) 2) 0 / 2 -
    2 * matchedLower r (levels r (WuCubicHellingerMatrix.displacement 1 h) 0)
      (levels r (WuCubicHellingerMatrix.displacement 1 h) 1)
      (levels r (WuCubicHellingerMatrix.displacement 1 h) 2) = 1 * g0scaled r 1 h at hg₀
  change cutBias r (levels r (WuCubicHellingerMatrix.displacement 1 h) 0)
      (levels r (WuCubicHellingerMatrix.displacement 1 h) 1)
      (levels r (WuCubicHellingerMatrix.displacement 1 h) 2) 2 / 2 -
    2 * matchedUpper r (levels r (WuCubicHellingerMatrix.displacement 1 h) 0)
      (levels r (WuCubicHellingerMatrix.displacement 1 h) 1)
      (levels r (WuCubicHellingerMatrix.displacement 1 h) 2) = 1 * g2scaled r 1 h at hg₂
  rw [hy, one_mul] at hg₀ hg₂
  change g0scaled r 1 h = (r - 1) * dotProduct
    (lowerTilt r (WuCubicHellingerMatrix.displacement 1 h)) (WuCubicHellingerMatrix.coordinates h) at ht₀
  change g2scaled r 1 h = (r - 1) * dotProduct
    (upperTilt r (WuCubicHellingerMatrix.displacement 1 h)) (WuCubicHellingerMatrix.coordinates h) at ht₂
  rw [hy, lowerTilt_dot] at ht₀
  rw [hy, upperTilt_dot] at ht₂
  have h₀ : h 0 = y 0 := rfl
  have h₁ : h 1 = y 1 := rfl
  have h₂ : h 2 = y 2 := rfl
  refine ⟨?_, ?_⟩
  · rw [hg₀, ht₀, h₀, h₂, lowerSlope]
    field_simp [sub_ne_zero.mpr hr.ne'] <;> ring
  · rw [hg₂, ht₂, h₁, upperSlope]
    field_simp [sub_ne_zero.mpr hr.ne'] <;> ring

/-- The physical coefficients entering the refined Schur bound. -/
def physicalWeight (r : ℝ) (y : Vec3) : ℝ :=
  let m := levels r y 0
  let n := levels r y 1
  let q := levels r y 2
  matchedLower r m n q + matchedUpper r m n q + cutBias r m n q 1 / 2

def physicalAsymmetry (r : ℝ) (y : Vec3) : ℝ :=
  let m := levels r y 0
  let n := levels r y 1
  let q := levels r y 2
  (matchedLower r m n q - matchedUpper r m n q) / physicalWeight r y

def physicalResidual (r : ℝ) (y : Vec3) : ℝ :=
  let m := levels r y 0
  let n := levels r y 1
  let q := levels r y 2
  let B := cutBias r m n q
  let G₀ := B 0 / 2 - 2 * matchedLower r m n q
  let G₂ := B 2 / 2 - 2 * matchedUpper r m n q
  G₀ - G₂ - physicalAsymmetry r y * (G₀ + G₂)

def physicalPivot (r : ℝ) (y : Vec3) : ℝ :=
  longCoeff r (levels r y 0) (levels r y 1) (levels r y 2) -
    physicalAsymmetry r y * physicalResidual r y

theorem physical_factors {r : ℝ} (hr : 1 < r) (y : Vec3) :
    physicalWeight r y = (r - 1) ^ 2 * weight r y ∧
    physicalAsymmetry r y = asymmetry r y ∧
    physicalResidual r y = (r - 1) ^ 2 * residual r y ∧
    physicalPivot r y = (r - 1) ^ 2 * linearPivot r y := by
  obtain ⟨hp₀, hp₂, hlong⟩ := cut_scaling hr y
  obtain ⟨_, hb, _, _, _, _⟩ := cut_factors hr y
  obtain ⟨hg₀, hg₂⟩ := slope_factors hr y
  have hp : physicalWeight r y = (r - 1) ^ 2 * weight r y := by
    rw [physicalWeight, hp₀, hp₂, hb, weight]
    ring
  have hk : physicalAsymmetry r y = asymmetry r y := by
    rw [physicalAsymmetry, hp, hp₀, hp₂, ← mul_sub, asymmetry,
      mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr hr.ne'))]
  have hres : physicalResidual r y = (r - 1) ^ 2 * residual r y := by
    dsimp only [physicalResidual]
    rw [hg₀, hg₂, hk, residual]
    ring
  refine ⟨hp, hk, hres, ?_⟩
  rw [physicalPivot, hlong, hk, hres, linearPivot]
  ring

theorem signed_row_eq {r : ℝ} (hr : 1 < r) (y : Vec3) :
    WuCubicRefinedHellinger.signedTiltRow r y
      (physicalAsymmetry r y) (physicalResidual r y) (physicalPivot r y) =
    WuCubicRefinedHellinger.signedTiltRow r y
      (asymmetry r y) (residual r y) (linearPivot r y) := by
  obtain ⟨_, hk, hres, hβ⟩ := physical_factors hr y
  rw [hk, hres, hβ]
  funext i
  unfold WuCubicRefinedHellinger.signedTiltRow
  rw [show 2 * ((r - 1) ^ 2 * linearPivot r y) =
      (r - 1) ^ 2 * (2 * linearPivot r y) by ring,
    mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr hr.ne'))]

/-- The eleven finite inequalities imply the physical spectral premises. -/
theorem physical_tests {r : ℝ} (hr : 1 < r) (y : Vec3)
    (hnq : levels r y 1 ≤ levels r y 2) (h : ∀ i, 0 < tests r y i) :
    let m := levels r y 0
    let n := levels r y 1
    let q := levels r y 2
    let A := cutEnergy r m n q
    let B := cutBias r m n q
    let L₀ := matchedMixture A B
    let ell := B 1 / 4
    let L := L₀ + ell
    let P₀ := matchedLower r m n q
    let P₂ := matchedUpper r m n q
    let Q₀ := B 0 / 2 - 2 * P₀
    let Q₂ := B 2 / 2 - 2 * P₂
    0 ≤ L₀ ∧ L ≤ lowerCoeff r m n q ∧ L ≤ upperCoeff r n q ∧
      ell ≤ B 0 ∧ ell ≤ B 2 ∧ 0 < P₀ ∧ 0 < P₂ ∧ L₀ < longCoeff r m n q ∧
      0 ≤ physicalWeight r y * (P₀ + P₂ - ell - L) - (P₀ - P₂) ^ 2 ∧
      0 < physicalPivot r y ∧
      0 ≤ 4 * ((2 / 3) * (P₀ + P₂)) * ((2 / 3) * P₂ + Q₂) -
        (Q₀ - Q₂ - (4 / 3) * P₂) ^ 2 := by
  intro m n q A B L₀ ell L P₀ P₂ Q₀ Q₂
  obtain ⟨_, hs, _⟩ := gap_scaling hr y
  obtain ⟨hb₀, hb₁, hb₂, hm, hz₀, hz₂⟩ := cut_factors hr y
  obtain ⟨hp₀, hp₂, hlong⟩ := cut_scaling hr y
  obtain ⟨hg₀, hg₂⟩ := slope_factors hr y
  obtain ⟨hp, _, _, hβ⟩ := physical_factors hr y
  let t := r - 1
  let s := middleGap r y
  have ht : 0 < t := sub_pos.mpr hr
  have hs₀ : 0 ≤ s := (mul_nonneg_iff_of_pos_left ht).mp (hs ▸ sub_nonneg.mpr hnq)
  have htest (i : Fin 11) : 0 < tests r y i := h i
  have hL₀ : L₀ = t ^ 2 * (s * mixture r y) := hm
  have hell : ell = t ^ 2 * (s * (middleBias r y / 4)) := by
    change cutBias r m n q 1 / 4 = _
    rw [hb₁]
    ring
  have hL : L = t ^ 2 * (s * (mixture r y + middleBias r y / 4)) := by
    change L₀ + ell = _
    rw [hL₀, hell]
    ring
  have hP₀ : P₀ = t ^ 2 * lowerWeight r y := hp₀
  have hP₂ : P₂ = t ^ 2 * upperWeight r y := hp₂
  have hQ₀ : Q₀ = t ^ 2 * lowerSlope r y := hg₀
  have hQ₂ : Q₂ = t ^ 2 * upperSlope r y := hg₂
  have ht₂ : 0 < t ^ 2 := pow_pos ht _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL₀]
    exact mul_nonneg ht₂.le (mul_nonneg hs₀ (htest 0).le)
  · rw [hL, hz₀]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (sub_nonneg.mp (htest 1).le) hs₀) ht₂.le
  · rw [hL, hz₂]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (sub_nonneg.mp (htest 2).le) hs₀) ht₂.le
  · rw [hell]
    change _ ≤ cutBias r m n q 0
    rw [hb₀]
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp (htest 5).le) ht₂.le
  · rw [hell]
    change _ ≤ cutBias r m n q 2
    rw [hb₂]
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp (htest 6).le) ht₂.le
  · rw [hP₀]
    exact mul_pos ht₂ (htest 3)
  · rw [hP₂]
    exact mul_pos ht₂ (htest 4)
  · rw [hL₀, hlong]
    exact mul_lt_mul_of_pos_left (sub_pos.mp (htest 7)) ht₂
  · rw [hp, hP₀, hP₂, hell, hL]
    apply (mul_nonneg (pow_nonneg ht.le 4) (htest 8).le).trans_eq
    symm
    change _ = t ^ 4 * (weight r y * (lowerWeight r y + upperWeight r y -
      s * (middleBias r y / 4 + (mixture r y + middleBias r y / 4))) -
      (lowerWeight r y - upperWeight r y) ^ 2)
    ring
  · rw [hβ]
    exact mul_pos ht₂ (htest 9)
  · rw [hP₀, hP₂, hQ₀, hQ₂]
    apply (mul_nonneg (pow_nonneg ht.le 4) (htest 10).le).trans_eq
    symm
    change _ = t ^ 4 * (4 * ((2 / 3) * (lowerWeight r y + upperWeight r y)) *
      ((2 / 3) * upperWeight r y + upperSlope r y) -
      (lowerSlope r y - upperSlope r y - (4 / 3) * upperWeight r y) ^ 2)
    ring

end D5.S3.Quantum.Semigroups.WuCubicLowerCoefficients
