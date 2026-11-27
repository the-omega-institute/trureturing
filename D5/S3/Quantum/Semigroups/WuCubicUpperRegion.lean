import D5.S3.Quantum.Semigroups.WuCubicGibbsCheckedCoverCompact
import D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix
import D5.S3.Quantum.Semigroups.WuCubicThermalDerivatives
import OmegaBuild.Commands

/-! Physical admissibility and the normalized-deficit bound in the upper Gibbs region. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicUpperRegion

open WuCubicAngularCertificate
open WuCubicDirectedOccupationCap (Mat)
open WuCubicGibbsScaledCoefficients
open WuCubicHellingerMatrix
open WuCubicOccupationTaylor (gibbsLevels)
open WuCubicThermalDerivatives (upperRoot)
open WuCubicGibbsCheckedCoverCompact (InBox)
open private gamma c e bias cutA from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private adjacentFactor from D5.S3.Quantum.Semigroups.WuCubicGibbsScaledCoefficients
open private leftGap middleGap rightGap gap_scaling matchedLower matchedUpper
  from D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix

/-- The four tests on the closed upper root box, in the rational replay coordinates. -/
def UpperRootTests : Prop :=
  ∀ z : Fin 5 → ℝ, InBox (Fin.lastCases (0, 0) upperRoot) z →
    let y := focalOffsets (z 1) (z 2) (z 3)
    0 < longTest (-1) (z 0) y ∧ 0 < longTest 1 (z 0) y ∧
    (signedMatrix (-1) (z 0) y).PosSemidef ∧ (signedMatrix 1 (z 0) y).PosSemidef

private def fieldRatio (r : ℝ) : ℝ :=
  2 * (r ^ 2 + 4 * r + 1) / (3 * (r + 1) * (r ^ 2 + r + 1))

private def directedRatio (r : ℝ) : ℝ := (r - 1) ^ 2 / (r + 1)

private theorem fieldRatio_pos {r : ℝ} (hr : 0 < r) : 0 < fieldRatio r := by
  unfold fieldRatio
  positivity

private theorem fieldRatio_antitone {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    fieldRatio b ≤ fieldRatio a := by
  have ha₀ : 0 < a := zero_lt_one.trans_le ha
  have hb₀ : 0 < b := ha₀.trans_le hab
  let u := a - 1
  let v := b - a
  have hu : 0 ≤ u := sub_nonneg.mpr ha
  have hv : 0 ≤ v := sub_nonneg.mpr hab
  have hpoly : 0 ≤ 6 * v * ((u ^ 2 + 6 * u + 6) * v ^ 2 +
      (2 * u ^ 3 + 18 * u ^ 2 + 39 * u + 24) * v +
      u ^ 4 + 12 * u ^ 3 + 39 * u ^ 2 + 48 * u + 18) := by positivity
  unfold fieldRatio
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  dsimp only [u, v] at hpoly
  nlinarith only [hpoly]

private theorem directedRatio_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    directedRatio a ≤ directedRatio b := by
  have ha₀ : 0 < a := zero_lt_one.trans_le ha
  have hb₀ : 0 < b := ha₀.trans_le hab
  have hpoly : 0 ≤ (b - a) * (((a - 1) + 2) * (b - a) + (a - 1) ^ 2 + 4 * (a - 1)) := by
    have ha' := sub_nonneg.mpr ha
    have hab' := sub_nonneg.mpr hab
    positivity
  unfold directedRatio
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [hpoly]

private theorem coefficient_ratios {r : ℝ} (hr : 1 < r) :
    0 < c r ∧ bias r / 2 = c r * (r - 1) * fieldRatio r ∧
      3 * e r * (r - 1) = c r * directedRatio r := by
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have h₁ : 0 < r + 1 := by positivity
  have h₂ : 0 < r ^ 2 + r + 1 := by positivity
  have hg : 0 < gamma r := by unfold gamma; positivity
  refine ⟨by unfold c; positivity, ?_, ?_⟩
  · unfold bias c fieldRatio
    field_simp
  · unfold e c directedRatio
    field_simp
    ring

/-- The variables are the three successive gaps divided by `r - 1`.
The matched and adjacent coefficients retain the common middle-gap factor. -/
private theorem scaled_coefficients {r m n q l s u : ℝ} (hr : 1 < r)
    (hl : n - m = (r - 1) * l) (hs : q - n = (r - 1) * s)
    (hu : 1 - q = (r - 1) * u) :
    let k := c r * (r - 1) ^ 2
    let f := fieldRatio r
    let w := directedRatio r
    let mix := f * (n ^ 2 + n * q + q ^ 2) + w * s ^ 2 / 3 - s * (n + q)
    let z₀ := l * (m + 2 * n + q - w * (l + s))
    let z₂ := u * (n + 2 * q + 1 - w * (s + u))
    matchedMixture (cutEnergy r m n q) (cutBias r m n q) = k * (s * mix) ∧
    lowerCoeff r m n q = k * (s * z₀) ∧ upperCoeff r n q = k * (s * z₂) ∧
    cutEnergy r m n q 0 = k * (l ^ 2 * (m + n)) ∧
    cutEnergy r m n q 2 = k * (u ^ 2 * (q + 1)) := by
  dsimp only
  obtain ⟨_, hb, he⟩ := coefficient_ratios hr
  have hb' : bias r = 2 * (c r * (r - 1) * fieldRatio r) := by linarith only [hb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [matched_mixture_eq]
    unfold matchedMixtureScaled middleBiasScaled middleEnergyScaled
    rw [hs, hb']
    linear_combination ((r - 1) ^ 2 * s ^ 3 / 3) * he
  · rw [lower_coeff_eq]
    unfold lowerCoeffScaled adjacentFactor
    rw [hl, hs]
    linear_combination (-(r - 1) ^ 2 * s * l * (l + s)) * he
  · rw [upper_coeff_eq]
    unfold upperCoeffScaled adjacentFactor
    rw [hs, hu]
    linear_combination (-(r - 1) ^ 2 * s * u * (s + u)) * he
  · change cutA r m n = _
    rw [cutA, hl]
    ring
  · change cutA r q 1 = _
    rw [cutA, hu]
    ring

/-- Rational bounds following the two thermal slabs of the admissibility verifier.
The last five checks give a single quadratic lower bound for both endpoint terms. -/
private def SlabChecks (a b : ℝ) : Prop :=
  let t := a - 1
  let mMin := (b ^ 2)⁻¹
  let nMin := b⁻¹ - 1 / 128
  let nMax := a⁻¹ + 1 / 128
  let lMin := mMin - (3 / 256) / t
  let lMax := (a ^ 2)⁻¹ + (1 / 128) / t
  let sMax := (1 / 64) / t
  let uMin := b⁻¹ - (1 / 128) / t
  let uMax := a⁻¹ + (1 / 128) / t
  let wMax := directedRatio b
  let fieldMax := fieldRatio a * (3 * nMax ^ 2)
  let mixMax := fieldMax + wMax * sMax ^ 2 / 3
  let lowerMin := mMin + 3 * nMin - wMax * (lMax + sMax)
  let upperMin := 3 * nMin + 1 - wMax * (sMax + uMax)
  let z₀Min := lMin * lowerMin
  let z₂Min := uMin * upperMin
  1 / 2 ≤ mMin ∧ 1 / 2 ≤ nMin ∧ 0 < lMin ∧ 0 < uMin ∧
    0 ≤ lowerMin ∧ 0 ≤ upperMin ∧
    0 ≤ fieldRatio b * (3 * nMin ^ 2) - sMax * (2 * nMax) ∧
    mixMax ≤ z₀Min ∧ mixMax ≤ z₂Min ∧
    1 / 2 ≤ lMin ^ 2 * (mMin + nMin) ∧ 1 / 2 ≤ uMin ^ 2 * (nMin + 1) ∧
    -(7 / 4) ≤ z₀Min - 2 * fieldMax ∧ -(7 / 4) ≤ z₂Min - 2 * fieldMax ∧
    3 ≤ 4 * nMin - 2 * wMax * sMax / 3

private theorem slabChecks_lower : SlabChecks (1049 / 1000) (2249 / 2000) := by
  norm_num [SlabChecks, fieldRatio, directedRatio]

private theorem slabChecks_upper : SlabChecks (2249 / 2000) (6 / 5) := by
  norm_num [SlabChecks, fieldRatio, directedRatio]

private theorem div_cap {a b t₀ t : ℝ} (hb : 0 ≤ b) (ht₀ : 0 < t₀) (ht : t₀ ≤ t)
    (h : a ≤ b) : a / t ≤ b / t₀ :=
  (div_le_div_of_nonneg_right h (ht₀.le.trans ht)).trans
    (div_le_div_of_nonneg_left hb ht₀ ht)

private theorem div_neg_cap {a b t₀ t : ℝ} (hb : 0 ≤ b) (ht₀ : 0 < t₀) (ht : t₀ ≤ t)
    (h : -b ≤ a) : -(b / t₀) ≤ a / t := by
  have h' : -a ≤ b := by linarith only [h]
  simpa only [neg_div, neg_neg] using neg_le_neg (div_cap hb ht₀ ht h')

private structure Admissible (r m n q : ℝ) : Prop where
  lowGibbs : 1 / 2 ≤ (r ^ 2)⁻¹
  midGibbs : 1 / 2 ≤ r⁻¹
  lowLevel : 1 / 2 ≤ m
  midLevel : 1 / 2 ≤ n
  highMiddleLevel : 1 / 2 ≤ q
  lowOrder : m ≤ n
  highOrder : q ≤ 1
  mixtureNonneg : 0 ≤ matchedMixture (cutEnergy r m n q) (cutBias r m n q)
  mixtureLower : matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ lowerCoeff r m n q
  mixtureUpper : matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ upperCoeff r n q
  lowerPos : 0 < matchedLower r m n q
  upperPos : 0 < matchedUpper r m n q
  junctionNonneg : 0 ≤ matchedLower r m n q * matchedUpper r m n q /
    (matchedLower r m n q + matchedUpper r m n q) -
    matchedMixture (cutEnergy r m n q) (cutBias r m n q) / 4

set_option maxHeartbeats 1000000 in
-- The slab comparison normalizes several polynomial bounds in a single proof.
private theorem admissible_on_slab {a b r m n q : ℝ} (ha : 1 < a)
    (har : a ≤ r) (hrb : r ≤ b) (checks : SlabChecks a b)
    (hm₀ : 0 ≤ m - (r ^ 2)⁻¹) (hm₁ : m - (r ^ 2)⁻¹ ≤ 1 / 256)
    (hn₀ : -(1 / 128) ≤ n - r⁻¹) (hnq : n ≤ q) (hq₁ : q - r⁻¹ ≤ 1 / 128) :
    Admissible r m n q := by
  let t := r - 1
  let tMin := a - 1
  let mMin := (b ^ 2)⁻¹
  let nMin := b⁻¹ - 1 / 128
  let nMax := a⁻¹ + 1 / 128
  let lMin := mMin - (3 / 256) / tMin
  let lMax := (a ^ 2)⁻¹ + (1 / 128) / tMin
  let sMax := (1 / 64) / tMin
  let uMin := b⁻¹ - (1 / 128) / tMin
  let uMax := a⁻¹ + (1 / 128) / tMin
  let wMax := directedRatio b
  let fieldMax := fieldRatio a * (3 * nMax ^ 2)
  let mixMax := fieldMax + wMax * sMax ^ 2 / 3
  let lowerMin := mMin + 3 * nMin - wMax * (lMax + sMax)
  let upperMin := 3 * nMin + 1 - wMax * (sMax + uMax)
  let z₀Min := lMin * lowerMin
  let z₂Min := uMin * upperMin
  change 1 / 2 ≤ mMin ∧ 1 / 2 ≤ nMin ∧ 0 < lMin ∧ 0 < uMin ∧
    0 ≤ lowerMin ∧ 0 ≤ upperMin ∧
    0 ≤ fieldRatio b * (3 * nMin ^ 2) - sMax * (2 * nMax) ∧
    mixMax ≤ z₀Min ∧ mixMax ≤ z₂Min ∧
    1 / 2 ≤ lMin ^ 2 * (mMin + nMin) ∧ 1 / 2 ≤ uMin ^ 2 * (nMin + 1) ∧
    -(7 / 4) ≤ z₀Min - 2 * fieldMax ∧ -(7 / 4) ≤ z₂Min - 2 * fieldMax ∧
    3 ≤ 4 * nMin - 2 * wMax * sMax / 3 at checks
  obtain ⟨hmHalf, hnHalf, hlMinPos, huMinPos, hLowerMin, hUpperMin, hMixNonneg,
    hLComp, hUComp, hA₀Min, hA₂Min, hLin₀, hLin₂, hCurv⟩ := checks
  have ha₀ : 0 < a := zero_lt_one.trans ha
  have hr : 1 < r := ha.trans_le har
  have hr₀ : 0 < r := ha₀.trans_le har
  have hb₀ : 0 < b := hr₀.trans_le hrb
  have htMin : 0 < tMin := sub_pos.mpr ha
  have htLe : tMin ≤ t := sub_le_sub_right har 1
  have ht : 0 < t := htMin.trans_le htLe
  have hlowMin : mMin ≤ (r ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 (pow_le_pow_left₀ hr₀.le hrb 2)
  have hlowMax : (r ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 (pow_le_pow_left₀ ha₀.le har 2)
  have hmidMin : b⁻¹ ≤ r⁻¹ := (inv_le_inv₀ hb₀ hr₀).2 hrb
  have hmidMax : r⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hr₀ ha₀).2 har
  have hmMin : mMin ≤ m := hlowMin.trans (sub_nonneg.mp hm₀)
  have hnMin : nMin ≤ n := by dsimp only [nMin]; linarith only [hmidMin, hn₀]
  have hqMax : q ≤ nMax := by dsimp only [nMax]; linarith only [hmidMax, hq₁]
  have hqMin := hnMin.trans hnq
  have hnMax := hnq.trans hqMax
  have hnMinNonneg : 0 ≤ nMin := by linarith only [hnHalf]
  have hmMinNonneg : 0 ≤ mMin := by linarith only [hmHalf]
  have hnNonneg := hnMinNonneg.trans hnMin
  have hqNonneg := hnMinNonneg.trans hqMin
  have hnMaxNonneg := hnNonneg.trans hnMax
  let y : Vec3 := ![m - (r ^ 2)⁻¹, n - r⁻¹, q - r⁻¹]
  have hy₀ : y 0 = m - (r ^ 2)⁻¹ := rfl
  have hy₁ : y 1 = n - r⁻¹ := rfl
  have hy₂ : y 2 = q - r⁻¹ := rfl
  have hmEq : levels r y 0 = m := by
    change (r ^ 2)⁻¹ + y 0 = m
    rw [hy₀]; ring
  have hnEq : levels r y 1 = n := by
    change r⁻¹ + y 1 = n
    rw [hy₁]; ring
  have hqEq : levels r y 2 = q := by
    change r⁻¹ + y 2 = q
    rw [hy₂]; ring
  let l := leftGap r y
  let s := middleGap r y
  let u := rightGap r y
  obtain ⟨hl, hs, hu⟩ := gap_scaling hr y
  rw [hmEq, hnEq] at hl
  rw [hnEq, hqEq] at hs
  rw [hqEq] at hu
  change n - m = t * l at hl
  change q - n = t * s at hs
  change 1 - q = t * u at hu
  have hy₁Lo : -(3 / 256) ≤ y 1 - y 0 := by rw [hy₁, hy₀]; linarith only [hn₀, hm₁]
  have hy₁Hi : y 1 - y 0 ≤ 1 / 128 := by
    rw [hy₁, hy₀]; linarith only [hm₀, hnq, hq₁]
  have hy₂Lo : -(1 / 128) ≤ y 2 := by rw [hy₂]; linarith only [hn₀, hnq]
  have hy₂Hi : y 2 ≤ 1 / 128 := by rwa [hy₂]
  have hlMin : lMin ≤ l := by
    have h := add_le_add hlowMin (div_neg_cap (by norm_num) htMin htLe hy₁Lo)
    simpa only [lMin, l, leftGap, t, sub_eq_add_neg] using h
  have hlMax : l ≤ lMax :=
    add_le_add hlowMax (div_cap (by norm_num) htMin htLe hy₁Hi)
  have hs₀ : 0 ≤ s := by
    change 0 ≤ (y 2 - y 1) / t
    apply div_nonneg _ ht.le
    rw [hy₂, hy₁]
    linarith only [hnq]
  have hsMax : s ≤ sMax := by
    apply div_cap (by norm_num) htMin htLe
    rw [hy₂, hy₁]
    linarith only [hn₀, hq₁]
  have huMin : uMin ≤ u := sub_le_sub hmidMin (div_cap (by norm_num) htMin htLe hy₂Hi)
  have huMax : u ≤ uMax := by
    have h := sub_le_sub hmidMax (div_neg_cap (by norm_num) htMin htLe hy₂Lo)
    simpa only [u, rightGap, t, uMax, sub_neg_eq_add] using h
  have hlPos := hlMinPos.trans_le hlMin
  have huPos := huMinPos.trans_le huMin
  have hsMaxNonneg := hs₀.trans hsMax
  let f := fieldRatio r
  let w := directedRatio r
  have hw₀ : 0 ≤ w := by dsimp only [w, directedRatio]; positivity
  have hwMax : w ≤ wMax := directedRatio_mono hr.le hrb
  have hwMaxNonneg := hw₀.trans hwMax
  have hfMin : fieldRatio b ≤ f := fieldRatio_antitone hr.le hrb
  have hfMax : f ≤ fieldRatio a := fieldRatio_antitone ha.le har
  let mass := n ^ 2 + n * q + q ^ 2
  have hMassMin : 3 * nMin ^ 2 ≤ mass := by
    have hn₂ := pow_le_pow_left₀ hnMinNonneg hnMin 2
    have hq₂ := pow_le_pow_left₀ hnMinNonneg hqMin 2
    have hCross := mul_le_mul hnMin hqMin hnMinNonneg hnNonneg
    dsimp only [mass]
    nlinarith only [hn₂, hq₂, hCross]
  have hMassMax : mass ≤ 3 * nMax ^ 2 := by
    have hn₂ := pow_le_pow_left₀ hnNonneg hnMax 2
    have hq₂ := pow_le_pow_left₀ hqNonneg hqMax 2
    have hCross := mul_le_mul hnMax hqMax hqNonneg hnMaxNonneg
    dsimp only [mass]
    nlinarith only [hn₂, hq₂, hCross]
  have hFieldMin : fieldRatio b * (3 * nMin ^ 2) ≤ f * mass :=
    mul_le_mul hfMin hMassMin (by positivity) (fieldRatio_pos hr₀).le
  have hFieldMax : f * mass ≤ fieldMax :=
    mul_le_mul hfMax hMassMax (by dsimp only [mass]; positivity) (fieldRatio_pos ha₀).le
  have hMidUpper : s * (n + q) ≤ sMax * (2 * nMax) :=
    mul_le_mul hsMax (by linarith only [hnMax, hqMax]) (add_nonneg hnNonneg hqNonneg) hsMaxNonneg
  have hDirectedUpper : w * s ^ 2 ≤ wMax * sMax ^ 2 :=
    mul_le_mul hwMax (pow_le_pow_left₀ hs₀ hsMax 2) (sq_nonneg s) hwMaxNonneg
  let mix := f * mass + w * s ^ 2 / 3 - s * (n + q)
  let z₀ := l * (m + 2 * n + q - w * (l + s))
  let z₂ := u * (n + 2 * q + 1 - w * (s + u))
  have hMix₀ : 0 ≤ mix := by
    dsimp only [mix]
    linarith only [hMixNonneg, hFieldMin, hMidUpper, show 0 ≤ w * s ^ 2 / 3 by positivity]
  have hMixMax : mix ≤ mixMax := by
    dsimp only [mix, mixMax]
    linarith only [hFieldMax, hDirectedUpper, mul_nonneg hs₀ (add_nonneg hnNonneg hqNonneg)]
  have hZ₀ : z₀Min ≤ z₀ := by
    have hProd := mul_le_mul hwMax (add_le_add hlMax hsMax)
      (add_nonneg hlPos.le hs₀) hwMaxNonneg
    apply mul_le_mul hlMin _ hLowerMin hlPos.le
    dsimp only [lowerMin]
    linarith only [hmMin, hnMin, hqMin, hProd]
  have hZ₂ : z₂Min ≤ z₂ := by
    have hProd := mul_le_mul hwMax (add_le_add hsMax huMax)
      (add_nonneg hs₀ huPos.le) hwMaxNonneg
    apply mul_le_mul huMin _ hUpperMin huPos.le
    dsimp only [upperMin]
    linarith only [hnMin, hqMin, hProd]
  have hA₀ : 1 / 2 ≤ l ^ 2 * (m + n) := hA₀Min.trans
    (mul_le_mul (pow_le_pow_left₀ hlMinPos.le hlMin 2) (add_le_add hmMin hnMin)
      (add_nonneg hmMinNonneg hnMinNonneg) (sq_nonneg l))
  have hA₂ : 1 / 2 ≤ u ^ 2 * (q + 1) := hA₂Min.trans
    (mul_le_mul (pow_le_pow_left₀ huMinPos.le huMin 2) (add_le_add hqMin le_rfl)
      (by positivity) (sq_nonneg u))
  have hCurvActual : 3 ≤ 2 * (n + q) - 2 * w * s / 3 := by
    have hProd := mul_le_mul hwMax hsMax hs₀ hwMaxNonneg
    linarith only [hCurv, hnMin, hqMin, hProd]
  have hEndpoint {A Z Zmin : ℝ} (hA : 1 / 2 ≤ A) (hZ : Zmin ≤ Z)
      (hLinear : -(7 / 4) ≤ Zmin - 2 * fieldMax) : 0 < A + s * (Z - 2 * mix) := by
    have hCurvTimes := mul_le_mul_of_nonneg_right hCurvActual hs₀
    have hLinearActual : -(7 / 4) + 3 * s ≤ Z - 2 * mix := by
      dsimp only [mix]
      nlinarith only [hLinear, hZ, hFieldMax, hCurvTimes]
    have hLinearTimes := mul_le_mul_of_nonneg_left hLinearActual hs₀
    nlinarith only [hA, hLinearTimes, sq_nonneg (s - 7 / 24)]
  let k := c r * t ^ 2
  have hc := (coefficient_ratios hr).1
  have hk : 0 < k := mul_pos hc (pow_pos ht 2)
  obtain ⟨hL, hZleft, hZright, hE₀, hE₂⟩ := scaled_coefficients hr hl hs hu
  change matchedMixture (cutEnergy r m n q) (cutBias r m n q) = k * (s * mix) at hL
  change lowerCoeff r m n q = k * (s * z₀) at hZleft
  change upperCoeff r n q = k * (s * z₂) at hZright
  change cutEnergy r m n q 0 = k * (l ^ 2 * (m + n)) at hE₀
  change cutEnergy r m n q 2 = k * (u ^ 2 * (q + 1)) at hE₂
  let L₀ := matchedMixture (cutEnergy r m n q) (cutBias r m n q)
  let P₀ := matchedLower r m n q
  let P₂ := matchedUpper r m n q
  have hL₀ : 0 ≤ L₀ := by
    change 0 ≤ matchedMixture (cutEnergy r m n q) (cutBias r m n q)
    rw [hL]
    exact mul_nonneg hk.le (mul_nonneg hs₀ hMix₀)
  have hLeft : L₀ ≤ lowerCoeff r m n q := by
    change matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ _
    rw [hL, hZleft]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hMixMax.trans (hLComp.trans hZ₀)) hs₀) hk.le
  have hRight : L₀ ≤ upperCoeff r n q := by
    change matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ _
    rw [hL, hZright]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hMixMax.trans (hUComp.trans hZ₂)) hs₀) hk.le
  have hP₀ : L₀ / 2 < P₀ := by
    change _ < (cutEnergy r m n q 0 + lowerCoeff r m n q - L₀) / 2
    have hscaled := mul_pos hk (hEndpoint hA₀ hZ₀ hLin₀)
    dsimp only [L₀]
    rw [hL, hE₀, hZleft]
    nlinarith only [hscaled]
  have hP₂ : L₀ / 2 < P₂ := by
    change _ < (cutEnergy r m n q 2 + upperCoeff r n q - L₀) / 2
    have hscaled := mul_pos hk (hEndpoint hA₂ hZ₂ hLin₂)
    dsimp only [L₀]
    rw [hL, hE₂, hZright]
    nlinarith only [hscaled]
  have hHalf : 0 ≤ L₀ / 2 := div_nonneg hL₀ (by norm_num)
  have hp₀ : 0 < P₀ := hHalf.trans_lt hP₀
  have hp₂ : 0 < P₂ := hHalf.trans_lt hP₂
  have hj : 0 ≤ P₀ * P₂ / (P₀ + P₂) - L₀ / 4 := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ (add_pos hp₀ hp₂)).2
    have h₀ := mul_le_mul_of_nonneg_right hP₀.le hp₂.le
    have h₂ := mul_le_mul_of_nonneg_right hP₂.le hp₀.le
    nlinarith only [h₀, h₂]
  refine ⟨hmHalf.trans hlowMin, ?_, hmHalf.trans hmMin, hnHalf.trans hnMin,
    hnHalf.trans hqMin, ?_, ?_, hL₀, hLeft, hRight, hp₀, hp₂, hj⟩
  · dsimp only [nMin] at hnHalf
    linarith only [hnHalf, hmidMin]
  · exact sub_nonneg.mp (by rw [hl]; exact mul_nonneg ht.le hlPos.le)
  · exact sub_nonneg.mp (by rw [hu]; exact mul_nonneg ht.le huPos.le)

private theorem physical_admissible {r m n q : ℝ}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hm₀ : 0 ≤ m - (r ^ 2)⁻¹) (hm₁ : m - (r ^ 2)⁻¹ ≤ 1 / 256)
    (hn₀ : -(1 / 128) ≤ n - r⁻¹) (hnq : n ≤ q) (hq₁ : q - r⁻¹ ≤ 1 / 128) :
    Admissible r m n q := by
  rcases le_total r (2249 / 2000) with h | h
  · exact admissible_on_slab (by norm_num) hr₀ h slabChecks_lower hm₀ hm₁ hn₀ hnq hq₁
  · exact admissible_on_slab (by norm_num) h hr₁ slabChecks_upper hm₀ hm₁ hn₀ hnq hq₁

private theorem physical_point_in_root {r m n q : ℝ}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hm₀ : 0 ≤ m - (r ^ 2)⁻¹) (hm₁ : m - (r ^ 2)⁻¹ ≤ 1 / 256)
    (hn₀ : -(1 / 128) ≤ n - r⁻¹) (hnq : n ≤ q) (hq₁ : q - r⁻¹ ≤ 1 / 128) :
    ∃ z : Fin 5 → ℝ, InBox (Fin.lastCases (0, 0) upperRoot) z ∧ z 0 = r ∧
      focalOffsets (z 1) (z 2) (z 3) = ![m - (r ^ 2)⁻¹, n - r⁻¹, q - r⁻¹] := by
  let room := 1 / 128 - (n - r⁻¹)
  let blend := if room = 0 then 0 else (q - n) / room
  have hgap : 0 ≤ q - n := sub_nonneg.mpr hnq
  have hfit : q - n ≤ room := by dsimp only [room]; linarith only [hq₁]
  have hblend : (0 ≤ blend ∧ blend ≤ 1) ∧ room * blend = q - n := by
    by_cases hzero : room = 0
    · have hgapZero : q - n = 0 := le_antisymm (hfit.trans_eq hzero) hgap
      simp [blend, hzero, hgapZero]
    · have hpos : 0 < room := lt_of_le_of_ne (hgap.trans hfit) (Ne.symm hzero)
      simp only [blend, ite_eq_right hzero]
      exact ⟨⟨div_nonneg hgap hpos.le, (div_le_one hpos).2 hfit⟩, by field_simp [hzero]⟩
  let z : Fin 5 → ℝ := ![r, m - (r ^ 2)⁻¹, n - r⁻¹, blend, 0]
  refine ⟨z, ?_, rfl, ?_⟩
  · intro i
    fin_cases i
    · change (((1049 / 1000 : ℚ) : ℝ)) ≤ r ∧ r ≤ (((6 / 5 : ℚ) : ℝ))
      simpa only [Rat.cast_div, Rat.cast_ofNat] using And.intro hr₀ hr₁
    · change ((0 : ℚ) : ℝ) ≤ m - (r ^ 2)⁻¹ ∧ m - (r ^ 2)⁻¹ ≤ (((1 / 256 : ℚ) : ℝ))
      simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        And.intro hm₀ hm₁
    · change (((-1 / 128 : ℚ) : ℝ)) ≤ n - r⁻¹ ∧ n - r⁻¹ ≤ (((1 / 128 : ℚ) : ℝ))
      have hn₁ : n - r⁻¹ ≤ 1 / 128 := by linarith only [hnq, hq₁]
      simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div] using
        And.intro hn₀ hn₁
    · change ((0 : ℚ) : ℝ) ≤ blend ∧ blend ≤ ((1 : ℚ) : ℝ)
      simpa only [Rat.cast_zero, Rat.cast_one] using hblend.1
    · change ((0 : ℚ) : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ ((0 : ℚ) : ℝ)
      norm_num
  · funext i
    fin_cases i
    · rfl
    · rfl
    · change (n - r⁻¹) + room * blend = q - r⁻¹
      rw [hblend.2]
      ring

/-- The maximum absolute displacement from the three Gibbs levels. -/
def offsetRadius (r m n q : ℝ) : ℝ :=
  max |m - (r ^ 2)⁻¹| (max |n - r⁻¹| |q - r⁻¹|)

private theorem offsetRadius_pos {r m n q : ℝ}
    (hne : m ≠ (r ^ 2)⁻¹ ∨ n ≠ r⁻¹ ∨ q ≠ r⁻¹) : 0 < offsetRadius r m n q := by
  rcases hne with hm | hn | hq
  · exact (abs_pos.mpr (sub_ne_zero.mpr hm)).trans_le (le_max_left _ _)
  · exact (abs_pos.mpr (sub_ne_zero.mpr hn)).trans_le
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (abs_pos.mpr (sub_ne_zero.mpr hq)).trans_le
      ((le_max_right _ _).trans (le_max_right _ _))

private theorem offsetRadius_attained (r m n q : ℝ) :
    let v : Fin 4 → ℝ := ![m - (r ^ 2)⁻¹, n - r⁻¹, q - r⁻¹, 0]
    ∃ i, |v i| = offsetRadius r m n q := by
  intro v
  change ∃ i, |v i| = max |v 0| (max |v 1| |v 2|)
  rcases le_total (max |v 1| |v 2|) |v 0| with h₀ | h₀
  · exact ⟨0, (max_eq_left h₀).symm⟩
  · rw [max_eq_right h₀]
    rcases le_total |v 2| |v 1| with h₁ | h₁
    · exact ⟨1, (max_eq_left h₁).symm⟩
    · exact ⟨2, (max_eq_right h₁).symm⟩

/-- For every complex unitary frame, the two signed matrices and the two scalar
long tests on the upper root box imply the physical displacement bound. -/
theorem normalized_deficit_ge (hroot : UpperRootTests) (U : unitary Mat) {r m n q : ℝ}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hm₀ : 0 ≤ m - (r ^ 2)⁻¹) (hm₁ : m - (r ^ 2)⁻¹ ≤ 1 / 256)
    (hn₀ : -(1 / 128) ≤ n - r⁻¹) (hnq : n - r⁻¹ ≤ q - r⁻¹) (hq₁ : q - r⁻¹ ≤ 1 / 128)
    (hne : m ≠ (r ^ 2)⁻¹ ∨ n ≠ r⁻¹ ∨ q ≠ r⁻¹) :
    offsetRadius r m n q ^ 2 / 64 ≤ normalizedDeficit r U m n q := by
  have hr : 1 < r := (by norm_num : (1 : ℝ) < 1049 / 1000).trans_le hr₀
  have hnq' : n ≤ q := by linarith only [hnq]
  have ha := physical_admissible hr₀ hr₁ hm₀ hm₁ hn₀ hnq' hq₁
  obtain ⟨z, hz, hz₀, hzOffsets⟩ := physical_point_in_root hr₀ hr₁ hm₀ hm₁ hn₀ hnq' hq₁
  obtain ⟨hLongMinus, hLongPlus, hMatrixMinus, hMatrixPlus⟩ := hroot z hz
  let d := offsetRadius r m n q
  have hd : 0 < d := offsetRadius_pos hne
  let v : Fin 4 → ℝ := ![m - (r ^ 2)⁻¹, n - r⁻¹, q - r⁻¹, 0]
  let h : Fin 4 → ℝ := fun i => v i / d
  have hscale (i : Fin 4) : d * h i = v i := by
    dsimp only [h]
    field_simp [hd.ne']
  have hh : h 3 = 0 := by change 0 / d = 0; exact zero_div d
  have h₀ : 0 ≤ h 0 := div_nonneg hm₀ hd.le
  have h₁₂ : h 1 ≤ h 2 := div_le_div_of_nonneg_right hnq hd.le
  have hnorm : 1 ≤ ∑ i, h i ^ 2 := by
    obtain ⟨i, hi⟩ := offsetRadius_attained r m n q
    change |v i| = d at hi
    have hAbs : |h i| = 1 := by
      change |v i / d| = 1
      rw [abs_div, abs_of_pos hd, hi, div_self hd.ne']
    have hSquare : h i ^ 2 = 1 := by rw [← sq_abs, hAbs, one_pow]
    rw [← hSquare]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (h j)) (Finset.mem_univ i)
  have hx₀ : gibbsLevels r 0 + d * h 0 = m := by
    rw [hscale]
    change (r ^ 2)⁻¹ + (m - (r ^ 2)⁻¹) = m
    ring
  have hx₁ : gibbsLevels r 1 + d * h 1 = n := by
    rw [hscale]
    change r⁻¹ + (n - r⁻¹) = n
    ring
  have hx₂ : gibbsLevels r 2 + d * h 2 = q := by
    rw [hscale]
    change r⁻¹ + (q - r⁻¹) = q
    ring
  have hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + d * h i := by
    intro i
    fin_cases i
    · change 1 / 2 ≤ gibbsLevels r 0 + d * h 0
      rw [hx₀]
      exact ha.lowLevel
    · change 1 / 2 ≤ gibbsLevels r 1 + d * h 1
      rw [hx₁]
      exact ha.midLevel
    · change 1 / 2 ≤ gibbsLevels r 2 + d * h 2
      rw [hx₂]
      exact ha.highMiddleLevel
    · change 1 / 2 ≤ 1 + d * h 3
      rw [hh]
      norm_num
  have hg : ∀ i, 1 / 2 ≤ gibbsLevels r i := by
    intro i
    fin_cases i
    · exact ha.lowGibbs
    · exact ha.midGibbs
    · exact ha.midGibbs
    · change (1 : ℝ) / 2 ≤ 1
      norm_num
  have hy : displacement d h = focalOffsets (z 1) (z 2) (z 3) := by
    rw [hzOffsets]
    funext i
    fin_cases i
    · exact hscale 0
    · exact hscale 1
    · exact hscale 2
  have hlminus : 0 < longTest (-1) r (displacement d h) := by
    simpa only [hy, ← hz₀] using hLongMinus
  have hlplus : 0 < longTest 1 r (displacement d h) := by
    simpa only [hy, ← hz₀] using hLongPlus
  have hmminus : (signedMatrix (-1) r (displacement d h)).PosSemidef := by
    rw [hy, ← hz₀]
    exact hMatrixMinus
  have hmplus : (signedMatrix 1 r (displacement d h)).PosSemidef := by
    rw [hy, ← hz₀]
    exact hMatrixPlus
  have hbound := normalized_deficit_ge_of_matrix_tests U hr hd.le h hh h₀ h₁₂ hx hg
  have hx₀' : levels r (displacement d h) 0 = m := hx₀
  have hx₁' : levels r (displacement d h) 1 = n := hx₁
  have hx₂' : levels r (displacement d h) 2 = q := hx₂
  dsimp only at hbound
  rw [hx₀', hx₁', hx₂'] at hbound
  calc
    d ^ 2 / 64 = (d ^ 2 / 64) * 1 := (mul_one _).symm
    _ ≤ (d ^ 2 / 64) * (∑ i, h i ^ 2) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ normalizedDeficit r U m n q :=
      hbound ha.lowOrder hnq' ha.highOrder ha.mixtureNonneg ha.mixtureLower ha.mixtureUpper
        ha.lowerPos ha.upperPos ha.junctionNonneg hlminus hlplus hmminus hmplus

/-- Under the root-box tests, every non-Gibbs point of the upper physical region
has strictly positive normalized deficit. -/
theorem normalized_deficit_pos (hroot : UpperRootTests) (U : unitary Mat) {r m n q : ℝ}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hm₀ : 0 ≤ m - (r ^ 2)⁻¹) (hm₁ : m - (r ^ 2)⁻¹ ≤ 1 / 256)
    (hn₀ : -(1 / 128) ≤ n - r⁻¹) (hnq : n - r⁻¹ ≤ q - r⁻¹) (hq₁ : q - r⁻¹ ≤ 1 / 128)
    (hne : m ≠ (r ^ 2)⁻¹ ∨ n ≠ r⁻¹ ∨ q ≠ r⁻¹) :
    0 < normalizedDeficit r U m n q := by
  have hd := offsetRadius_pos hne
  have hbound := normalized_deficit_ge hroot U hr₀ hr₁ hm₀ hm₁ hn₀ hnq hq₁ hne
  exact (div_pos (pow_pos hd 2) (by norm_num)).trans_le hbound

/--
info: 'D5.S3.Quantum.Semigroups.WuCubicUpperRegion.normalized_deficit_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms normalized_deficit_ge

/--
info: 'D5.S3.Quantum.Semigroups.WuCubicUpperRegion.normalized_deficit_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms normalized_deficit_pos

end D5.S3.Quantum.Semigroups.WuCubicUpperRegion
