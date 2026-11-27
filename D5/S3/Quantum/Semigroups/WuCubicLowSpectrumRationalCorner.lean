import D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCorner

/-! Rational evaluation of the low-spectrum Wu cubic corner and its physical bound. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrumRationalCorner

open _root_.Matrix
open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate (cutEnergy cutBias lowerCoeff upperCoeff longCoeff normalizedDeficit)
open WuCubicLowSpectrumCorner (thermalCenterLower cornerLower cornerLower_le_normalizedDeficit)
open WuCubicSharpAngularSlice (imbalanceSliceMin squareEdgeMin squareBoundaryMin squareSliceMin)
open private gamma c e bias cutA cutB gibbsLow gibbsHigh from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private crossCoeff directedCoeff from D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open private totalAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private gibbsArgument logCoordinate logSeries logUpper logRatioLower logRatioUpper
  thermalBase thermalFactor from D5.S3.Quantum.Semigroups.WuCubicBoundaryCorner
open private logLower massLogUpper entropyLower from
  D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCorner

private theorem cast_ite_of_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) (a b : ℚ) :
    ((if p then a else b : ℚ) : ℝ) = if q then (a : ℝ) else (b : ℝ) := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left (h.mp hp)]
  · rw [ite_eq_right hp, ite_eq_right (mt h.mpr hp)]

private theorem cast_ite_eq (x y a b : ℚ) :
    ((if x = y then a else b : ℚ) : ℝ) = if (x : ℝ) = y then (a : ℝ) else (b : ℝ) :=
  cast_ite_of_iff Rat.cast_inj.symm a b

private theorem cast_ite_le (x y a b : ℚ) :
    ((if x ≤ y then a else b : ℚ) : ℝ) = if (x : ℝ) ≤ y then (a : ℝ) else (b : ℝ) :=
  cast_ite_of_iff Rat.cast_le.symm a b

private def gammaRat (r : ℚ) : ℚ := 9 / (4 * (1 + r ^ 3))
private def cRat (r : ℚ) : ℚ := gammaRat r * r * (r + 1) / 2
private def eRat (r : ℚ) : ℚ := gammaRat r * r * (r - 1) / 6
private def biasRat (r : ℚ) : ℚ :=
  2 * gammaRat r * r * (r - 1) * (r ^ 2 + 4 * r + 1) / (3 * (r ^ 2 + r + 1))

private def cutARat (r v w : ℚ) : ℚ := cRat r * (w - v) ^ 2 * (w + v)
private def cutBRat (r v w : ℚ) : ℚ := biasRat r * (w ^ 3 - v ^ 3) + 2 * eRat r * (w - v) ^ 3

def cutEnergyRat (r m n q : ℚ) : Fin 3 → ℚ := ![cutARat r m n, cutARat r n q, cutARat r q 1]

def cutBiasRat (r m n q : ℚ) : Fin 3 → ℚ := ![cutBRat r m n, cutBRat r n q, cutBRat r q 1]

private def crossCoeffRat (r v w y z extra : ℚ) : ℚ :=
  cRat r * (w - v) * (z - y) * (w + v + (z + y)) -
    3 * eRat r * (w - v) * (z - y) * ((w - v) + (z - y) + 2 * extra)

def lowerCoeffRat (r m n q : ℚ) : ℚ := crossCoeffRat r m n n q 0
def upperCoeffRat (r n q : ℚ) : ℚ := crossCoeffRat r n q q 1 0
def longCoeffRat (r m n q : ℚ) : ℚ := crossCoeffRat r m n q 1 (q - n)

theorem cutEnergyRat_cast (r m n q : ℚ) (i : Fin 3) :
    (cutEnergyRat r m n q i : ℝ) = cutEnergy r m n q i := by
  fin_cases i <;> simp [cutEnergyRat, cutEnergy, cutARat, cutA, cRat, c, gammaRat, gamma]

theorem cutBiasRat_cast (r m n q : ℚ) (i : Fin 3) :
    (cutBiasRat r m n q i : ℝ) = cutBias r m n q i := by
  fin_cases i <;> simp [cutBiasRat, cutBias, cutBRat, cutB, biasRat, bias, eRat, e, gammaRat, gamma]

private theorem crossCoeffRat_cast (r v w y z extra : ℚ) :
    (crossCoeffRat r v w y z extra : ℝ) = crossCoeff r v w y z extra := by
  simp [crossCoeffRat, crossCoeff, directedCoeff, cRat, c, eRat, e, gammaRat, gamma]

theorem lowerCoeffRat_cast (r m n q : ℚ) :
    (lowerCoeffRat r m n q : ℝ) = lowerCoeff r m n q := by
  simp only [lowerCoeffRat, lowerCoeff, crossCoeffRat_cast, Rat.cast_zero]

theorem upperCoeffRat_cast (r n q : ℚ) :
    (upperCoeffRat r n q : ℝ) = upperCoeff r n q := by
  simp only [upperCoeffRat, upperCoeff, crossCoeffRat_cast, Rat.cast_one, Rat.cast_zero]

theorem longCoeffRat_cast (r m n q : ℚ) :
    (longCoeffRat r m n q : ℝ) = longCoeff r m n q := by
  simp only [longCoeffRat, longCoeff, crossCoeffRat_cast, Rat.cast_one, Rat.cast_sub]

private def logCoordinateRat (x : ℚ) : ℚ := (x - 1) / (x + 1)

private def logSeriesRat : ℕ → ℚ → ℚ
  | 0, _ => 0
  | j + 1, z => logSeriesRat j z + z ^ (2 * j + 1) / (2 * j + 1)

private def logLowerRat (x : ℚ) : ℚ :=
  let z := logCoordinateRat x
  2 * (logSeriesRat 8 z + z ^ 17 / (1 - z ^ 2))

private def logUpperRat (x : ℚ) : ℚ :=
  let z := logCoordinateRat x
  2 * (logSeriesRat 8 z - z ^ 17 / (1 - z ^ 2))

private def massLogUpperRat (x : ℚ) : ℚ := 3 * (x ^ 3 * logUpperRat x)

private def totalAtRat (m n q : ℚ) : ℚ := m ^ 3 + n ^ 3 + q ^ 3 + 1

private def entropyLowerRat (r m n q : ℚ) : ℚ :=
  let T := totalAtRat m n q
  let gibbsLow := 1 / (1 + r ^ 3)
  let gibbsHigh := r ^ 3 * gibbsLow
  T * (logLowerRat (4 * gibbsLow * gibbsHigh) + logLowerRat (T / 4)) -
    massLogUpperRat m - massLogUpperRat n - massLogUpperRat q

/-- The finite log bracket used by the real corner bound. At a zero level the
mass factor is zero. At `r = 1` the entropy coefficient is exactly one half. -/
def thermalCenterLowerRat (r m n q : ℚ) : ℚ :=
  let S := entropyLowerRat r m n q
  gammaRat r * (r - 1) ^ 2 * (r + 1) * totalAtRat m n q +
    if r = 1 then S / 2
    else (3 * (r ^ 2 - 1) / (4 * (r ^ 2 + r + 1))) *
      min (S / (2 * logSeriesRat 5 (logCoordinateRat r))) (S / logLowerRat r)

private theorem logSeriesRat_cast (k : ℕ) (z : ℚ) :
    (logSeriesRat k z : ℝ) = logSeries k z := by
  induction k with
  | zero => simp [logSeriesRat, logSeries]
  | succ k ih =>
    rw [logSeriesRat, logSeries, Finset.sum_range_succ, Rat.cast_add, ih, logSeries]
    push_cast
    rfl

theorem thermalCenterLowerRat_cast (r m n q : ℚ) :
    (thermalCenterLowerRat r m n q : ℝ) = thermalCenterLower r m n q := by
  simp [thermalCenterLowerRat, thermalCenterLower, cast_ite_eq, thermalBase, thermalFactor,
    entropyLowerRat, entropyLower, gammaRat, gamma, totalAtRat, totalAt, gibbsArgument,
    gibbsLow, gibbsHigh, logLowerRat, logLower, logUpperRat, logUpper, logRatioLower,
    logRatioUpper, logSeriesRat_cast, logCoordinateRat, logCoordinate, massLogUpperRat,
    massLogUpper]

/-- The clipped vertex, including either endpoint and the zero weight case. -/
def imbalanceSliceMinRat (weight penalty lo hi : ℚ) : ℚ :=
  if penalty ≤ 2 * weight * lo then weight * lo ^ 2 - penalty * lo
  else if 2 * weight * hi ≤ penalty then weight * hi ^ 2 - penalty * hi
  else -(penalty ^ 2) / (4 * weight)

private theorem imbalanceSliceMinRat_cast (weight penalty lo hi : ℚ) :
    (imbalanceSliceMinRat weight penalty lo hi : ℝ) = imbalanceSliceMin weight penalty lo hi := by
  simp [imbalanceSliceMinRat, imbalanceSliceMin, cast_ite_le]

private def squareEdgeMinRat (weight penalty : ℚ) : ℚ :=
  if 0 ≤ weight then imbalanceSliceMinRat weight penalty (-1) 1 else weight - |penalty|

private theorem squareEdgeMinRat_cast (weight penalty : ℚ) :
    (squareEdgeMinRat weight penalty : ℝ) = squareEdgeMin weight penalty := by
  simp [squareEdgeMinRat, squareEdgeMin, cast_ite_le, imbalanceSliceMinRat_cast]

private def squareBoundaryMinRat (a b c p q : ℚ) : ℚ :=
  min (min (a + p + squareEdgeMinRat b (q + c)) (a - p + squareEdgeMinRat b (q - c)))
      (min (b + q + squareEdgeMinRat a (p + c)) (b - q + squareEdgeMinRat a (p - c)))

private theorem squareBoundaryMinRat_cast (a b c p q : ℚ) :
    (squareBoundaryMinRat a b c p q : ℝ) = squareBoundaryMin a b c p q := by
  simp [squareBoundaryMinRat, squareBoundaryMin, squareEdgeMinRat_cast]

/-- Compare all four edge minima with the stationary value when the Hessian
is positive definite and the stationary point lies in the square. -/
def squareSliceMinRat (a b c p q : ℚ) : ℚ :=
  let det := 4 * a * b - c ^ 2
  let x := (2 * b * p - c * q) / det
  let y := (2 * a * q - c * p) / det
  let edge := squareBoundaryMinRat a b c p q
  if 0 < a ∧ 0 < det ∧ |x| ≤ 1 ∧ |y| ≤ 1 then min edge (-(p * x + q * y) / 2)
  else edge

private theorem squareSliceMinRat_cast (a b c p q : ℚ) :
    (squareSliceMinRat a b c p q : ℝ) = squareSliceMin a b c p q := by
  let det := 4 * a * b - c ^ 2
  let x := (2 * b * p - c * q) / det
  let y := (2 * a * q - c * p) / det
  have feasible :
      (0 < a ∧ 0 < det ∧ |x| ≤ 1 ∧ |y| ≤ 1) ↔
      (0 < (a : ℝ) ∧ 0 < (det : ℝ) ∧ |(x : ℝ)| ≤ 1 ∧ |(y : ℝ)| ≤ 1) := by
    norm_cast
  unfold squareSliceMinRat squareSliceMin
  dsimp only
  rw [cast_ite_of_iff feasible]
  simp [det, x, y, squareBoundaryMinRat_cast]

/-- The exact rational corner expression, with absolute mixture weights and
endpoint charges. The fourth level is normalized to one. -/
def cornerLowerRat (r m n q L R μ₀ μ₂ : ℚ) : ℚ :=
  let A := cutEnergyRat r m n q
  let B := cutBiasRat r m n q
  let Z₀ := lowerCoeffRat r m n q
  let Z₂ := upperCoeffRat r n q
  let κ := longCoeffRat r m n q / 4
  let H := A 1 + (L + R) / 2
  let K := 2 * A 1 + H
  let C := A 1 + (Z₀ + Z₂) / 2 + (3 * (A 0 + A 2) - B 0 - B 2) / 2
  let g := μ₀ - μ₂
  let I := if K = 0 then 0 else 1 / (4 * K)
  let loss := if K = 0 then |g| else I * g ^ 2
  thermalCenterLowerRat r m n q +
    (C - loss + imbalanceSliceMinRat H (B 1 + μ₀ + μ₂) 0 1 +
      squareSliceMinRat ((A 0 + Z₀ - L) / 2 + κ - I * L ^ 2)
        ((A 2 + Z₂ - R) / 2 + κ - I * R ^ 2)
        (2 * (I * L * R - κ)) (B 0 / 2 - μ₀ - 2 * I * L * g)
        (B 2 / 2 - μ₂ + 2 * I * R * g))

theorem cornerLowerRat_cast (r m n q L R μ₀ μ₂ : ℚ) :
    (cornerLowerRat r m n q L R μ₀ μ₂ : ℝ) = cornerLower r m n q L R μ₀ μ₂ := by
  simp [cornerLowerRat, cornerLower, cutEnergyRat_cast, cutBiasRat_cast, lowerCoeffRat_cast,
    upperCoeffRat_cast, longCoeffRat_cast, cast_ite_eq, thermalCenterLowerRat_cast,
    imbalanceSliceMinRat_cast, squareSliceMinRat_cast]

/-- The rational evaluation is a lower bound for every physical complex frame. -/
theorem cornerLowerRat_le_normalizedDeficit {r m n q L R μ₀ μ₂ : ℚ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1)
    (hL : 0 ≤ L ∧ L ≤ lowerCoeffRat r m n q) (hR : 0 ≤ R ∧ R ≤ upperCoeffRat r n q)
    (hμ₀ : 0 ≤ μ₀ ∧ μ₀ ≤ cutBiasRat r m n q 0)
    (hμ₂ : 0 ≤ μ₂ ∧ μ₂ ≤ cutBiasRat r m n q 2) :
    (cornerLowerRat r m n q L R μ₀ μ₂ : ℝ) ≤ normalizedDeficit r U m n q := by
  rw [cornerLowerRat_cast]
  apply cornerLower_le_normalizedDeficit U
  · exact_mod_cast hr
  · exact_mod_cast hm
  · exact_mod_cast hmn
  · exact_mod_cast hnq
  · exact_mod_cast hq1
  · rw [← lowerCoeffRat_cast]
    exact ⟨by exact_mod_cast hL.1, Rat.cast_le.mpr hL.2⟩
  · rw [← upperCoeffRat_cast]
    exact ⟨by exact_mod_cast hR.1, Rat.cast_le.mpr hR.2⟩
  · rw [← cutBiasRat_cast]
    exact ⟨by exact_mod_cast hμ₀.1, Rat.cast_le.mpr hμ₀.2⟩
  · rw [← cutBiasRat_cast]
    exact ⟨by exact_mod_cast hμ₂.1, Rat.cast_le.mpr hμ₂.2⟩

/-- Check the physical parameter ranges and a strict rational deficit margin. -/
def cornerCheck (r m n q L R μ₀ μ₂ margin : ℚ) : Bool :=
  decide (1 ≤ r ∧ 0 ≤ m ∧ m ≤ n ∧ n ≤ q ∧ q ≤ 1 ∧
    (0 ≤ L ∧ L ≤ lowerCoeffRat r m n q) ∧ (0 ≤ R ∧ R ≤ upperCoeffRat r n q) ∧
    (0 ≤ μ₀ ∧ μ₀ ≤ cutBiasRat r m n q 0) ∧ (0 ≤ μ₂ ∧ μ₂ ≤ cutBiasRat r m n q 2) ∧
    margin < cornerLowerRat r m n q L R μ₀ μ₂)

theorem cornerCheck_sound {r m n q L R μ₀ μ₂ margin : ℚ} (U : unitary Mat)
    (h : cornerCheck r m n q L R μ₀ μ₂ margin = true) :
    (margin : ℝ) < normalizedDeficit r U m n q := by
  unfold cornerCheck at h
  obtain ⟨hr, hm, hmn, hnq, hq1, hL, hR, hμ₀, hμ₂, hmargin⟩ := of_decide_eq_true h
  exact (Rat.cast_lt.mpr hmargin).trans_le
    (cornerLowerRat_le_normalizedDeficit U hr hm hmn hnq hq1 hL hR hμ₀ hμ₂)

/-- The known shell corner also passes the executable strict-margin check. -/
theorem shellCorner_check :
    let r : ℚ := 6 / 5
    let m : ℚ := 63 / 100
    let n : ℚ := 3 / 4
    let q : ℚ := 9 / 10
    cornerCheck r m n q (lowerCoeffRat r m n q / 2) (upperCoeffRat r n q / 2) 0 0
      (7 / 1000) = true := by
  decide +kernel

#print axioms cornerLowerRat_cast
#print axioms cornerLowerRat_le_normalizedDeficit
#print axioms cornerCheck_sound
#print axioms shellCorner_check

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrumRationalCorner
