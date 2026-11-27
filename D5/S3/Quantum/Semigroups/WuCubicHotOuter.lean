import D5.S3.Quantum.Semigroups.WuCubicSpectralVariance
import D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
import D5.S3.TotalVariation.Pinsker

/-! Outer hot region of Wu v1 (3.54), for two equal CAR temperatures and s = 3.
The input spectrum is ordered and normalized by its top cube root. The local
estimate at the scalar ray is independent of this argument. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Matrix
open Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicHotOuter

open WuCubicAngularCertificate (normalizedDeficit physicalFrame endCharge thermalCenter)
open WuCubicDirectedOccupationCap
  (Mat frameVector frameWeight oddProbability emptyProbability fullProbability)
open WuCubicCoupledCuts (lowerAdjacentCutWeight upperAdjacentCutWeight)
open WuCubicRankTwoCut (forwardCutWeight reverseCutWeight cutImbalance)
open WuCubicOccupationEnvelope (sym)
open WuCubicSpectralVariance
open WuRepeatedMiddleCubic (alpha)
open private gamma h c e bias gibbsLow gibbsHigh from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private levelsAt totalAt cubic source_centered_at from
  D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private physicalFrame_columns physicalFrame_rows physicalFrame_weight physicalFrame_charge
  cutImbalance_eq_endCharge endCharge_sum from
  D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open private singletonCutWeight_eq adjacentCutWeight_ge_local from
  D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
open private odd_mass_mem from D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing
open private log_four_le alpha_nonneg_and_loss thermalDen_mono from
  D5.S3.Quantum.Semigroups.WuCubicSpectralVariance

noncomputable section

def mass (x : Fin 4 → ℝ) : ℝ := ∑ i, x i ^ 3

def spread (x : Fin 4 → ℝ) : ℝ := x 3 - x 0

def gapFraction (x : Fin 4 → ℝ) (i : Fin 3) : ℝ := spectralGap x i / spread x

def adjacentSum (x : Fin 4 → ℝ) (i : Fin 3) : ℝ := x i.castSucc + x i.succ

def squareEnergy (x : Fin 4 → ℝ) : ℝ :=
  ((x 1 - x 0)^2 * (x 0 + x 1) + (x 2 - x 0)^2 * (x 0 + x 2) +
   (x 3 - x 1)^2 * (x 1 + x 3) + (x 3 - x 2)^2 * (x 2 + x 3)) / 2

def squareDeficit (x : Fin 4 → ℝ) : ℝ :=
  9 / 8 * squareEnergy x - entropyGap (fun i => x i ^ 3) / 2

def edgeGamma (k : ℝ) : ℝ :=
  9 / 4 * ((3 / 4) / (1 + 2 * k^2 / 3) + (1 / 4) / (1 + 2 * k^2)) -
    3 / 8 - k^2 / 25

def edgeFloor (a b : ℝ) : ℝ :=
  (b - a)^4 * edgeGamma ((b - a) / (a + b)) / (4 * (a + b))

def squareFloor (x : Fin 4 → ℝ) : ℝ :=
  edgeFloor (x 0) (x 1) + edgeFloor (x 0) (x 2) +
    edgeFloor (x 1) (x 3) + edgeFloor (x 2) (x 3) +
    4 * (x 0 ^ 3 - (x 1 * x 2)^3)^2 / mass x ^ 3

/-- Section 5 of middle-neck, including the determinant term from entropy
tensorization. The scalar proof appears below. -/
def TracialSquareBound : Prop :=
  ∀ x : Fin 4 → ℝ, Monotone x → 0 ≤ x 0 → x 3 = 1 → squareFloor x ≤ squareDeficit x

private theorem entropy_center {x : Fin 4 → ℝ} (hm : ∀ i, 0 ≤ x i) (hM : 0 < mass x) :
    -entropyGap (fun i => x i ^ 3) =
      mass x * Real.log (mass x / 4) - ∑ i, x i ^ 3 * Real.log (x i ^ 3) := by
  symm
  have hterm (i : Fin 4) :
      x i ^ 3 * Real.log (4 * x i ^ 3 / mass x) =
        x i ^ 3 * Real.log (x i ^ 3) - x i ^ 3 * Real.log (mass x / 4) := by
    rcases (hm i).eq_or_lt with hi | hi
    · simp [← hi]
    rw [show 4 * x i ^ 3 / mass x = x i ^ 3 / (mass x / 4) by ring,
      Real.log_div (pow_ne_zero _ hi.ne') (by positivity)]
    ring
  change _ = -(∑ i, x i ^ 3 * Real.log (4 * x i ^ 3 / mass x))
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change _ = -(_ - mass x * Real.log (mass x / 4))
  ring

private theorem thermal_h (t : ℝ) (ht : 0 ≤ t) :
    h (1 + t) = thermalMassCoefficient t := by
  have hd : 0 < 1 + (1 + t)^3 := by positivity
  have hp : 0 < 1 + t + t^2 := by positivity
  have hfirst : gamma (1 + t) * (1 + t - 1)^2 * (1 + t + 1) =
      9 / (4 * (1 + t + t^2)) * t^2 := by
    unfold gamma
    field_simp [hd.ne', hp.ne'] <;> ring
  have hlog : 4 * gibbsLow (1 + t) * gibbsHigh (1 + t) =
      4 * (1 + t)^3 / (1 + (1 + t)^3)^2 := by
    simp only [gibbsHigh, gibbsLow]
    field_simp [hd.ne']
  simp only [h, thermalMassCoefficient, hfirst, hlog]

private theorem thermal_c (t : ℝ) (ht : 0 ≤ t) :
    c (1 + t) = (9 / 8) * thermalLambda t := by
  have hr : 0 < 1 + t := by positivity
  have hd : 0 < 1 + (1 + t)^3 := by positivity
  have hl : 0 < 1 + t^2 / (1 + t) := by positivity
  unfold c gamma thermalLambda
  field_simp [hr.ne', hd.ne', hl.ne'] <;> ring

private theorem thermal_bounds (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    1 / (1 + T^2) ≤ thermalLambda t ∧ 0 ≤ bias (1 + t) ∧
    bias (1 + t) ≤ (3 / 2) * t ∧ 0 ≤ e (1 + t) ∧ e (1 + t) ≤ (3 / 16) * t := by
  have hr₀ : 0 < 1 + t := by positivity
  have hden : 0 < (1 + t)^2 + (1 + t) + 1 := by positivity
  have hratio : gamma (1 + t) * (1 + t) ≤ 9 / 8 := by
    unfold gamma
    -- Move the positive factor in the numerator before clearing its denominator.
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [ht, sq_nonneg t, pow_nonneg ht 3]
  have hratio₂ : ((1 + t)^2 + 4 * (1 + t) + 1) /
      ((1 + t)^2 + (1 + t) + 1) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith only [sq_nonneg t]
  have hg : 0 ≤ gamma (1 + t) * (1 + t) := by unfold gamma; positivity
  have hb : 0 ≤ bias (1 + t) := by unfold bias gamma; rw [add_sub_cancel_left]; positivity
  have he : 0 ≤ e (1 + t) := by unfold e gamma; rw [add_sub_cancel_left]; positivity
  refine ⟨?_, hb, ?_, he, ?_⟩
  · unfold thermalLambda
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hdiv : t^2 / (1 + t) ≤ t^2 :=
      (div_le_iff₀ hr₀).2 (by nlinarith only [pow_nonneg ht 3])
    linarith only [hdiv, pow_le_pow_left₀ ht htT 2]
  · calc
      bias (1 + t) = (2 / 3) * (gamma (1 + t) * (1 + t)) * t *
          (((1 + t)^2 + 4 * (1 + t) + 1) / ((1 + t)^2 + (1 + t) + 1)) := by
        unfold bias
        field_simp [hden.ne']
        ring
      _ ≤ (2 / 3) * (9 / 8) * t * 2 := by gcongr
      _ = _ := by ring
  · unfold e
    rw [add_sub_cancel_left]
    nlinarith only [mul_le_mul_of_nonneg_right hratio ht]

private def charge (U : unitary Mat) : Fin 3 → ℝ :=
  ![-endCharge U 0, -cutImbalance U, endCharge U 3]

private def symmetricEnergy (U : unitary Mat) (x : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, frameWeight U i j * (x i - x j)^2 * (x i + x j)

private def signedCubic (U : unitary Mat) (x : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, frameWeight U i j * (x i - x j)^3

private theorem cutIndices :
    (0 : Fin 3).castSucc = (0 : Fin 4) ∧ (0 : Fin 3).succ = (1 : Fin 4) ∧
    (1 : Fin 3).castSucc = (1 : Fin 4) ∧ (1 : Fin 3).succ = (2 : Fin 4) ∧
    (2 : Fin 3).castSucc = (2 : Fin 4) ∧ (2 : Fin 3).succ = (3 : Fin 4) := by decide

private theorem charge_eq (U : unitary Mat) (i : Fin 3) :
    spectralCutImbalance (frameWeight U) i = charge U i := by
  rw [spectralCutImbalance_frameWeight]
  have hsum := endCharge_sum U
  unfold endCharge at hsum
  fin_cases i <;>
    simp (config := {decide := true}) [Fin.sum_univ_four, charge, cutImbalance_eq_endCharge,
      endCharge] <;> linarith only [hsum]

set_option maxHeartbeats 1000000 in
private theorem source_split {t m n q : ℝ} (ht : 0 ≤ t) (hm : 0 ≤ m)
    (hmn : m ≤ n) (hnq : n ≤ q) (U : unitary Mat) :
    let x := levelsAt m n q
    let r := 1 + t
    normalizedDeficit r U m n q =
      thermalMassCoefficient t * mass x -
      (alpha r - thermalLambda t / 2) * entropyGap (fun i => x i ^ 3) +
      thermalLambda t * squareDeficit x +
      c r * (symmetricEnergy U x - squareEnergy x) +
      bias r * (∑ i : Fin 3, charge U i * (x i.succ ^ 3 - x i.castSucc ^ 3)) +
      e r * signedCubic U x := by
  intro x r
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hn := hm.trans hmn
  have hq := hn.trans hnq
  have hM : 0 < mass x := by
    simpa [x, mass, levelsAt, Fin.sum_univ_four] using
      (show 0 < m^3 + n^3 + q^3 + 1 by positivity)
  have hx (i : Fin 4) : 0 ≤ x i := by
    fin_cases i <;> simp [x, levelsAt, hm, hm.trans hmn, hm.trans (hmn.trans hnq)]
  have hH := entropy_center hx hM
  have hsum := endCharge_sum U
  unfold normalizedDeficit
  rw [source_centered_at hr _ (physicalFrame_columns U) (physicalFrame_rows U)
    hm (hm.trans hmn) (hm.trans (hmn.trans hnq))]
  change h r * totalAt m n q + _ + _ + _ = _
  have htotal : totalAt m n q = mass x := by simp [mass, x, levelsAt, totalAt, Fin.sum_univ_four]
  have hlog : mass x * Real.log (mass x / 4) - m^3 * Real.log (m^3) -
      n^3 * Real.log (n^3) - q^3 * Real.log (q^3) =
      -entropyGap (fun i => x i ^ 3) := by
    rw [hH]
    simp [x, levelsAt, Fin.sum_univ_four]
    <;> ring
  rw [htotal, ← thermal_h t ht, hlog]
  have hc : c r = 9 / 8 * thermalLambda t := thermal_c t ht
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := cutIndices
  simp only [squareDeficit, squareEnergy, symmetricEnergy, signedCubic, physicalFrame_weight,
    physicalFrame_charge, cubic, Fin.sum_univ_three, Fin.sum_univ_four, x, levelsAt, charge,
    h0, h1, h2, h3, h4, h5, cutImbalance_eq_endCharge,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination bias r * q^3 * hsum +
    (((n - m)^2 * (m + n) + (q - m)^2 * (m + q) +
      (1 - n)^2 * (n + 1) + (1 - q)^2 * (q + 1)) / 2) * hc

/-- Minimum of the quadratic charge cost on the closed interval [0,1].
The zero-weight branch uses the same formula at the origin. -/
def chargeMinimum (w p : ℝ) : ℝ :=
  if 2 * w ≤ p then w - p else -p^2 / (4 * w)

theorem chargeMinimum_le {w p y : ℝ} (hw : 0 ≤ w) (hp : 0 ≤ p)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : chargeMinimum w p ≤ w*y^2 - p*y := by
  unfold chargeMinimum
  split_ifs with h
  · have h₁ := mul_nonneg (sub_nonneg.mpr hy.2) (sub_nonneg.mpr h)
    have h₂ := mul_nonneg hw (sq_nonneg (1-y))
    nlinarith only [h₁, h₂]
  · have hw' : 0 < w := by linarith
    apply (div_le_iff₀ (show 0 < 4*w by positivity)).2
    nlinarith only [sq_nonneg (2*w*y-p)]

private theorem end_charge_lower {D X p R y : ℝ}
    (hD : 0 ≤ D) (hX : 0 ≤ X) (hp : 0 ≤ p)
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) (hR : |R| ≤ (1 + y) / 2) :
    (D - p + chargeMinimum (D+X) p) / 2 ≤
      D / 2 + (D+X) * y^2 / 2 - p * |R| := by
  have hpenalty := mul_le_mul_of_nonneg_left hR hp
  have hq := chargeMinimum_le (add_nonneg hD hX) hp
    (show |y| ∈ Set.Icc (0 : ℝ) 1 from ⟨abs_nonneg _, abs_le.mpr hy⟩)
  rw [sq_abs] at hq
  have hyabs := le_abs_self y
  have hpy := mul_le_mul_of_nonneg_left hyabs hp
  nlinarith only [hq, hpenalty, hpy]

/-- The tracial floor, three diagonal weights, two adjacent weights, three
charge slopes, cubic remainder slope, and positive thermal coefficient are
all frozen by rational endpoints of the spectral box. -/
def cellValue (v d₀ d₁ d₂ l u : ℝ) (p : Fin 3 → ℝ) (j H t : ℝ) : ℝ :=
  v + (d₀ - t*p 0 + chargeMinimum (d₀+l) (t*p 0))/2 +
    chargeMinimum d₁ (t*p 1) +
    (d₂ - t*p 2 + chargeMinimum (d₂+u) (t*p 2))/2 - j*t + H*t^2

/-- The exact residual sign test for a box, quantified over its entire closed thermal interval. -/
def CellInequality (margin lo hi v d₀ d₁ d₂ l u : ℝ) (p : Fin 3 → ℝ) (j H : ℝ) : Prop :=
  ∀ t ∈ Set.Icc lo hi, margin < cellValue v d₀ d₁ d₂ l u p j H t


private def diagonal (x : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  gapFraction x i ^ 2 * adjacentSum x i

private def adjacent (x : Fin 4 → ℝ) (i j : Fin 3) : ℝ :=
  gapFraction x i * gapFraction x j * (adjacentSum x i + adjacentSum x j)

private def chargeSlope (x : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  let z := gapFraction x i
  let a := x i.castSucc
  let b := x i.succ
  (3 / 2) * z * (a^2 + a*b + b^2) / spread x +
    (3 / 16) * spread x * z * (1 + z^2)

private def skewSlope (x : Fin 4 → ℝ) : ℝ :=
  (3 / 16) * spread x *
    ∑ i : Fin 3, spectralCutCap i * gapFraction x i * (1 - gapFraction x i ^ 2)

private theorem fraction_bounds {x : Fin 4 → ℝ} (hx : Monotone x)
    (hs : 0 < spread x) (i : Fin 3) : gapFraction x i ∈ Set.Icc (0 : ℝ) 1 := by
  have hgap : 0 ≤ spectralGap x i := sub_nonneg.mpr (hx Fin.castSucc_lt_succ.le)
  have hspan : spectralGap x i ≤ spread x :=
    sub_le_sub (hx (Fin.le_last i.succ)) (hx (Fin.zero_le i.castSucc))
  exact ⟨div_nonneg hgap hs.le, (div_le_one hs).2 hspan⟩

set_option maxHeartbeats 1000000 in
private theorem angular_excess {x : Fin 4 → ℝ} (hx : Monotone x) (hx₀ : 0 ≤ x 0)
    (hs : 0 < spread x) (U : unitary Mat) (D : Fin 3 → ℝ) (L R c₀ : ℝ)
    (hD : ∀ i, 0 ≤ D i) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hd : ∀ i, D i ≤ c₀ * diagonal x i) (hl : L ≤ c₀ * adjacent x 0 1)
    (hu : R ≤ c₀ * adjacent x 1 2) (hc : 0 ≤ c₀) :
    let y₀ := 1 - 2 * oddProbability (frameVector U 0)
    let y₂ := 1 - 2 * oddProbability (frameVector U 3)
    (D 0 + D 2)/2 + (D 0 + L)*y₀^2/2 + D 1 * |charge U 1|^2 +
      (D 2 + R)*y₂^2/2 ≤ c₀ * (symmetricEnergy U x - squareEnergy x) / spread x ^ 2 := by
  intro y₀ y₂
  let W := sym (frameWeight U)
  let K₀ := W 0 1 + W 0 2 + W 0 3
  let K₁ := forwardCutWeight U + reverseCutWeight U
  let K₂ := W 0 3 + W 1 3 + W 2 3
  obtain ⟨h₀, h₂⟩ := singletonCutWeight_eq U
  obtain ⟨hL₀, hR₀⟩ := adjacentCutWeight_ge_local U
  obtain ⟨h₁, _, _⟩ := WuCubicCoupledCuts.adjacentCutWeight_ge_signed U
  have h₀' : 1 / 2 + y₀^2/2 ≤ K₀ - 1 := by linarith only [h₀]
  have h₂' : 1 / 2 + y₂^2/2 ≤ K₂ - 1 := by linarith only [h₂]
  have hl' : y₀^2/2 ≤ lowerAdjacentCutWeight U - 1/2 := by
    nlinarith only [hL₀]
  have hu' : y₂^2/2 ≤ upperAdjacentCutWeight U - 1/2 := by
    nlinarith only [hR₀]
  have h₁' : |charge U 1|^2 ≤ K₁ - 1 := by
    change |-cutImbalance U|^2 ≤ K₁ - 1
    rw [abs_neg]
    nlinarith only [h₁, sq_nonneg (-WuCubicRankTwoCut.cutEvenOffset U)]
  have heq :
      c₀ * (symmetricEnergy U x - squareEnergy x) / spread x ^ 2 =
        c₀ * diagonal x 0 * (K₀ - 1) + c₀ * diagonal x 1 * (K₁ - 1) +
        c₀ * diagonal x 2 * (K₂ - 1) +
        c₀ * adjacent x 0 1 * (lowerAdjacentCutWeight U - 1/2) +
        c₀ * adjacent x 1 2 * (upperAdjacentCutWeight U - 1/2) +
        c₀ * adjacent x 0 2 * W 0 3 := by
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := cutIndices
    simp only [symmetricEnergy, squareEnergy, diagonal, adjacent, gapFraction, adjacentSum,
      h0, h1, h2, h3, h4, h5, spectralGap, lowerAdjacentCutWeight, upperAdjacentCutWeight, forwardCutWeight,
      reverseCutWeight, K₀, K₁, K₂, W, sym, Fin.sum_univ_four]
    field_simp [hs.ne'] <;> ring
  have hlevels (i : Fin 4) : 0 ≤ x i := hx₀.trans (hx (Fin.zero_le i))
  have hadj (i j : Fin 3) : 0 ≤ adjacent x i j := by
    unfold adjacent adjacentSum
    exact mul_nonneg (mul_nonneg (fraction_bounds hx hs i).1 (fraction_bounds hx hs j).1)
      (add_nonneg (add_nonneg (hlevels _) (hlevels _))
        (add_nonneg (hlevels _) (hlevels _)))
  have hW : 0 ≤ W 0 3 := by
    unfold W sym frameWeight
    exact add_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  have he₀ := (mul_le_mul_of_nonneg_left h₀' (hD 0)).trans
    (mul_le_mul_of_nonneg_right (hd 0) (h₀'.trans' (by positivity)))
  have he₁ := (mul_le_mul_of_nonneg_left h₁' (hD 1)).trans
    (mul_le_mul_of_nonneg_right (hd 1) (h₁'.trans' (sq_nonneg _)))
  have he₂ := (mul_le_mul_of_nonneg_left h₂' (hD 2)).trans
    (mul_le_mul_of_nonneg_right (hd 2) (h₂'.trans' (by positivity)))
  have hle := (mul_le_mul_of_nonneg_left hl' hL).trans
    (mul_le_mul_of_nonneg_right hl (hl'.trans' (by positivity)))
  have hue := (mul_le_mul_of_nonneg_left hu' hR).trans
    (mul_le_mul_of_nonneg_right hu (hu'.trans' (by positivity)))
  rw [heq]
  linarith only [he₀, he₁, he₂, hle, hue, mul_nonneg (mul_nonneg hc (hadj 0 2)) hW]

private theorem angular_charge {x : Fin 4 → ℝ} (hx : Monotone x) (hx₀ : 0 ≤ x 0)
    (hs : 0 < spread x) {t : ℝ} (ht : 0 ≤ t) {T : ℝ} (htT : t ≤ T)
    (U : unitary Mat) (p : Fin 3 → ℝ) (j : ℝ)
    (hp : ∀ i, chargeSlope x i ≤ p i) (hj : skewSlope x ≤ j) :
    -(∑ i : Fin 3, t * p i * |charge U i|) - t*j ≤
       (bias (1+t) * (∑ i : Fin 3, charge U i * (x i.succ^3 - x i.castSucc^3)) +
         e (1+t) * signedCubic U x) / spread x ^ 2 := by
  obtain ⟨_, hb₀, hb, he₀, he⟩ := thermal_bounds t T ht htT
  let s := spread x
  let z := gapFraction x
  let b := bias (1+t)
  let g := e (1+t)
  have hlevels (i : Fin 4) : 0 ≤ x i := hx₀.trans (hx (Fin.zero_le i))
  have hz := fraction_bounds hx hs
  have hcap (i : Fin 3) : 0 ≤ spectralCutCap i := by
    fin_cases i <;> norm_num [spectralCutCap]
  have hsquared (i : Fin 3) : 0 ≤ 1 - z i^2 := by
    have h := pow_le_pow_left₀ (hz i).1 (hz i).2 2
    rw [one_pow] at h
    exact sub_nonneg.mpr h
  have hscale (i : Fin 3) : spectralGap x i = s * z i := by
    dsimp [z, gapFraction, s]
    field_simp [hs.ne'] <;> ring
  have hsk := directional_spectral_cut_cubic_lower_bound U hx
  simp only [charge_eq] at hsk
  change _ ≤ signedCubic U x at hsk
  have hsk' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsk he₀)
    (sq_nonneg s)
  have htotal :
      (∑ i : Fin 3,
        ((b * z i * (x i.castSucc^2 + x i.castSucc * x i.succ + x i.succ^2) / s +
          g * s * z i * (1 + z i^2)) * charge U i -
          g * s * spectralCutCap i * z i * (1 - z i^2))) ≤
      (b * (∑ i : Fin 3, charge U i * (x i.succ^3 - x i.castSucc^3)) +
        g * signedCubic U x) / s^2 := by
    rw [add_div]
    change _ ≤ _ + g * signedCubic U x / s^2
    refine le_trans ?_ (add_le_add_right hsk' _)
    rw [← add_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    have hcube : x i.succ^3 - x i.castSucc^3 =
        spectralGap x i * (x i.castSucc^2 + x i.castSucc * x i.succ + x i.succ^2) := by
      unfold spectralGap
      ring
    rw [hcube, hscale]
    change _ ≤ (_ + g * (s * z i *
      (((s * z i)^2 + s^2) * charge U i - (s^2 - (s * z i)^2) * spectralCutCap i))) / s^2
    apply le_of_eq
    field_simp [show s ≠ 0 from hs.ne'] <;> ring
  refine le_trans ?_ htotal
  rw [← Finset.sum_neg_distrib]
  have hj' := mul_le_mul_of_nonneg_left hj ht
  have hj'' : (∑ i : Fin 3, g * s * spectralCutCap i * z i * (1 - z i^2)) ≤ t*j := by
    refine le_trans ?_ (show t * skewSlope x ≤ t*j from hj')
    simp only [skewSlope, mul_assoc, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hrest : 0 ≤ s * (spectralCutCap i * (z i * (1 - z i^2))) :=
      mul_nonneg hs.le (mul_nonneg (hcap i) (mul_nonneg (hz i).1 (hsquared i)))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right he hrest
  rw [Finset.sum_sub_distrib]
  apply sub_le_sub _ hj''
  apply Finset.sum_le_sum
  intro i _
  let P := b * z i * (x i.castSucc^2 + x i.castSucc * x i.succ + x i.succ^2)/s +
    g * s * z i * (1 + z i^2)
  have hpoly : 0 ≤ x i.castSucc^2 + x i.castSucc * x i.succ + x i.succ^2 :=
    add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (hlevels _) (hlevels _))) (sq_nonneg _)
  have hP : 0 ≤ P := by
    exact add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg hb₀ (hz i).1) hpoly) hs.le)
      (mul_nonneg (mul_nonneg (mul_nonneg he₀ hs.le) (hz i).1) (by positivity))
  have hP' : P ≤ t * p i := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (hp i) ht)
    unfold P
    conv_rhs =>
      simp only [chargeSlope]
      rw [mul_add]
    apply add_le_add
    · have hf : 0 ≤ z i * (x i.castSucc^2 + x i.castSucc * x i.succ + x i.succ^2) / s := by
        exact div_nonneg (mul_nonneg (hz i).1 hpoly) hs.le
      change b ≤ (3 / 2) * t at hb
      convert mul_le_mul_of_nonneg_right hb hf using 1 <;>
        simp only [div_eq_mul_inv] <;> ring
    · have hf : 0 ≤ s * z i * (1 + z i^2) := by
        exact mul_nonneg (mul_nonneg hs.le (hz i).1) (by positivity)
      simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_right he hf
  calc
    -(t * p i * |charge U i|) ≤ -(P * |charge U i|) :=
      neg_le_neg (mul_le_mul_of_nonneg_right hP' (abs_nonneg _))
    _ ≤ P * charge U i := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_abs_le _) hP

private theorem angular_minimum {x : Fin 4 → ℝ} (hx : Monotone x) (hx₀ : 0 ≤ x 0)
    (hs : 0 < spread x) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (U : unitary Mat)
    (D p : Fin 3 → ℝ) (L R j : ℝ) (hD : ∀ i, 0 ≤ D i) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hd : ∀ i, D i ≤ c (1+t) * diagonal x i) (hl : L ≤ c (1+t) * adjacent x 0 1)
    (hu : R ≤ c (1+t) * adjacent x 1 2)
    (hp₀ : ∀ i, 0 ≤ p i) (hp : ∀ i, chargeSlope x i ≤ p i) (hj : skewSlope x ≤ j) :
    cellValue 0 (D 0) (D 1) (D 2) L R p j 0 t ≤
      (c (1+t) * (symmetricEnergy U x - squareEnergy x) +
        bias (1+t) * (∑ i : Fin 3, charge U i * (x i.succ^3 - x i.castSucc^3)) +
        e (1+t) * signedCubic U x) / spread x ^ 2 := by
  have hc : 0 ≤ c (1+t) := by rw [thermal_c t ht]; unfold thermalLambda; positivity
  have hex := angular_excess hx hx₀ hs U D L R _ hD hL hR hd hl hu hc
  have hchg := angular_charge hx hx₀ hs ht htT U p j hp hj
  let y₀ := 1 - 2 * oddProbability (frameVector U 0)
  let y₂ := 1 - 2 * oddProbability (frameVector U 3)
  obtain ⟨ha₀, ha₂⟩ := WuCubicCoupledCuts.endCutCharge_abs_le U
  have hq₀ : |charge U 0| ≤ (1+y₀)/2 := (ha₀.trans (min_le_left _ _))
  have hq₂ : |charge U 2| ≤ (1+y₂)/2 := (ha₂.trans (min_le_left _ _))
  have ho₀ := odd_mass_mem U 0
  have ho₂ := odd_mass_mem U 3
  have hy₀ : y₀ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith only [ho₀.2], by linarith only [ho₀.1]⟩
  have hy₂ : y₂ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith only [ho₂.2], by linarith only [ho₂.1]⟩
  have hq₁ : |charge U 1| ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨abs_nonneg _, ?_⟩
    have hcut := WuCubicCoupledCuts.abs_cutEvenOffset_add_abs_cutImbalance_le_one U
    change |-cutImbalance U| ≤ 1
    rw [abs_neg]
    linarith only [hcut, abs_nonneg (WuCubicRankTwoCut.cutEvenOffset U)]
  have hm₀ := end_charge_lower (hD 0) hL (mul_nonneg ht (hp₀ 0)) hy₀ hq₀
  have hm₂ := end_charge_lower (hD 2) hR (mul_nonneg ht (hp₀ 2)) hy₂ hq₂
  have hm₁ := chargeMinimum_le (hD 1) (mul_nonneg ht (hp₀ 1)) hq₁
  dsimp only at hex
  change (D 0 + D 2)/2 + (D 0 + L)*y₀^2/2 + D 1 * |charge U 1|^2 +
    (D 2 + R)*y₂^2/2 ≤ _ at hex
  rw [Fin.sum_univ_three] at hchg
  rw [add_assoc, add_div]
  unfold cellValue
  linarith only [hex, hchg, hm₀, hm₁, hm₂]

def varianceCoefficient (lo hi : ℝ) (lower upper : Fin 4 → ℝ) : ℝ :=
  9 / (4 * (1 + hi + hi^2)) - 9 / 8 -
    min (7 / 5) (boxVarianceUpper (fun i => lower i ^ 3) (fun i => upper i ^ 3)) *
      thermalEntropyPenalty lo hi

/-- Either reviewed hot interval can retain its uniform mass coefficient
when the variance estimate is weaker near a low-rank face. -/
def uniformCoefficient (hi loss : ℝ) : ℝ :=
  9 / (4 * (1 + hi + hi^2)) - 9 / 8 - (7 / 5) * loss

def firstLimit : ℝ := 7 / 143
def extendedLimit : ℝ := 105241 / 2125200
def firstHeight : ℝ := 7856887 / 32652860
def extendedHeight : ℝ := 1209149759 / 5236664020

theorem first_loss : thermalEntropyPenalty 0 firstLimit ≤ 1 / 2 := by
  norm_num [thermalEntropyPenalty, alphaLossFactor, firstLimit, max_le_iff]

theorem extended_loss : thermalEntropyPenalty 0 extendedLimit ≤ 3 / 7 := by
  norm_num [thermalEntropyPenalty, alphaLossFactor, extendedLimit, max_le_iff]

private theorem thermal_uniform {x : Fin 4 → ℝ} (hx : ∀ i, 0 ≤ x i) (hM : 0 < mass x)
    {t lo hi loss : ℝ} (hlo : 0 ≤ lo) (hlt : lo ≤ t) (hth : t ≤ hi)
    (hloss : thermalEntropyPenalty lo hi ≤ loss) :
    uniformCoefficient hi loss * t^2 * mass x ≤
      thermalMassCoefficient t * mass x -
        (alpha (1+t) - thermalLambda t/2) * entropyGap (fun i => x i^3) := by
  have ht := hlo.trans hlt
  have hp : 0 ≤ loss := (le_max_left _ _).trans hloss
  obtain ⟨hg, hgu⟩ := entropyGap_bounds (fun i => x i ^ 3)
    (fun i => pow_nonneg (hx i) 3) hM
  have hG : entropyGap (fun i => x i^3) ≤ mass x * (7/5) :=
    hgu.trans (mul_le_mul_of_nonneg_left (by simpa using log_four_le) hM.le)
  have ha := (alpha_sub_thermalLambda_half_le hlo hlt hth).trans
    (mul_le_mul_of_nonneg_left hloss (sq_nonneg t))
  have hpen := (mul_le_mul_of_nonneg_right ha hg).trans
    (mul_le_mul_of_nonneg_left hG (mul_nonneg (sq_nonneg t) hp))
  have hrec : 9 / (4 * (1 + hi + hi^2)) ≤ 9 / (4 * (1 + t + t^2)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (thermalDen_mono ht hth) (by norm_num))
  have hmass := mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right (sub_le_sub_right hrec (9/8)) (sq_nonneg t)).trans
      (by simpa only [mul_comm] using thermalMassCoefficient_ge ht)) hM.le
  unfold uniformCoefficient
  linarith only [hmass, hpen]

/-- The maximal coefficient from the two signed thermal estimates. Its sign
is certified at rational endpoints before replacing the actual spectral mass. -/
def cellCoefficient (lo hi loss : ℝ) (lower upper : Fin 4 → ℝ) : ℝ :=
  max (uniformCoefficient hi loss) (varianceCoefficient lo hi lower upper)

/-- Endpoint bounds needed by the analytic reduction. These are purely
algebraic inequalities on physical spectra and are independent of the frame. -/
structure CellBounds (x lower upper : Fin 4 → ℝ) (lo hi T loss v H : ℝ)
    (D p : Fin 3 → ℝ) (L R j : ℝ) : Prop where
  rootsLower : ∀ i, lower i ≤ x i
  rootsUpper : ∀ i, x i ≤ upper i
  massLowerPos : 0 < mass lower
  tracialNonneg : 0 ≤ squareFloor x
  tracialLower : v ≤ squareFloor x / ((1+T^2) * spread x^2)
  thermalLower : H ≤ cellCoefficient lo hi loss lower upper * mass x / spread x^2
  diagonalNonneg : ∀ i, 0 ≤ D i
  lowerAdjacentNonneg : 0 ≤ L
  upperAdjacentNonneg : 0 ≤ R
  diagonalLower : ∀ i, D i ≤ (9/8 / (1+T^2)) * diagonal x i
  lowerAdjacentLower : L ≤ (9/8 / (1+T^2)) * adjacent x 0 1
  upperAdjacentLower : R ≤ (9/8 / (1+T^2)) * adjacent x 1 2
  chargeNonneg : ∀ i, 0 ≤ p i
  chargeUpper : ∀ i, chargeSlope x i ≤ p i
  skewUpper : skewSlope x ≤ j

private theorem sorted_levels {m n q : ℝ} (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1) :
    Monotone (levelsAt m n q) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all (config := {decide := true}) [levelsAt] <;>
    linarith only [hmn, hnq, hq]

/-- The normalized source deficit dominates the real cell lower bound for
every unitary eigenframe of the closed, physically ordered spectral tuple. -/
theorem cellValue_le_normalizedDeficit
    (tracial : TracialSquareBound)
    {t lo hi T loss m n q v H L R j : ℝ} {lower upper : Fin 4 → ℝ} {D p : Fin 3 → ℝ}
    (ht₀ : 0 ≤ lo) (htl : lo ≤ t) (hth : t ≤ hi) (htT : t ≤ T)
    (hloss : thermalEntropyPenalty lo hi ≤ loss)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1) (hs : 0 < 1-m)
    (B : CellBounds (levelsAt m n q) lower upper lo hi T loss v H D p L R j)
    (U : unitary Mat) :
    cellValue v (D 0) (D 1) (D 2) L R p j H t ≤
      normalizedDeficit (1+t) U m n q / (1-m)^2 := by
  let x := levelsAt m n q
  let s := spread x
  have ht := ht₀.trans htl
  have hx := sorted_levels hmn hnq hq
  have hsx : 0 < s := hs
  have hn (i : Fin 4) : 0 ≤ x i := hm.trans (hx (Fin.zero_le i))
  have hM : 0 < mass x := B.massLowerPos.trans_le <| Finset.sum_le_sum fun i _ =>
    (show Monotone (fun a : ℝ => a^3) from
      (show Odd (3 : ℕ) by decide).strictMono_pow.monotone) (B.rootsLower i)
  have hvar := cubic_thermal_lower_bound hn hx B.rootsLower B.rootsUpper
    B.massLowerPos ht₀ htl hth
  have hh₁ := thermal_uniform hn hM ht₀ htl hth hloss
  let Q := thermalMassCoefficient t * mass x -
    (alpha (1+t) - thermalLambda t/2) * entropyGap (fun i => x i^3)
  have hh : cellCoefficient lo hi loss lower upper * t^2 * mass x ≤ Q := by
    unfold cellCoefficient
    rcases le_total (uniformCoefficient hi loss) (varianceCoefficient lo hi lower upper) with h | h
    · rw [max_eq_right h]
      exact hvar
    · rw [max_eq_left h]
      exact hh₁
  have hheat : H*t^2 ≤ Q/s^2 := by
    refine (mul_le_mul_of_nonneg_right B.thermalLower (sq_nonneg t)).trans ?_
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg s)
    linarith only [hh]
  have hlam := (thermal_bounds t T ht htT).1
  have hlam₀ : 0 ≤ thermalLambda t := by unfold thermalLambda; positivity
  have hsq : v ≤ thermalLambda t * squareDeficit x / s^2 := by
    refine B.tracialLower.trans ?_
    rw [← div_div]
    rw [div_eq_inv_mul (squareFloor x)]
    apply div_le_div_of_nonneg_right _ (sq_nonneg s)
    have hmul := mul_le_mul_of_nonneg_right hlam B.tracialNonneg
    rw [one_div] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left (tracial x hx hm rfl) hlam₀)
  have hc : 9/8 / (1+T^2) ≤ c (1+t) := by
    rw [thermal_c t ht, ← mul_one_div]
    exact mul_le_mul_of_nonneg_left hlam (by norm_num)
  have hdiag (i : Fin 3) : 0 ≤ diagonal x i := by
    unfold diagonal adjacentSum
    exact mul_nonneg (sq_nonneg _) (add_nonneg (hn _) (hn _))
  have hadj (i j : Fin 3) : 0 ≤ adjacent x i j := by
    unfold adjacent adjacentSum
    exact mul_nonneg (mul_nonneg (fraction_bounds hx hsx i).1 (fraction_bounds hx hsx j).1)
      (add_nonneg (add_nonneg (hn _) (hn _)) (add_nonneg (hn _) (hn _)))
  have hang := angular_minimum hx hm hsx ht htT U D p L R j B.diagonalNonneg
    B.lowerAdjacentNonneg B.upperAdjacentNonneg
    (fun i => (B.diagonalLower i).trans (mul_le_mul_of_nonneg_right hc (hdiag i)))
    (B.lowerAdjacentLower.trans (mul_le_mul_of_nonneg_right hc (hadj 0 1)))
    (B.upperAdjacentLower.trans (mul_le_mul_of_nonneg_right hc (hadj 1 2)))
    B.chargeNonneg B.chargeUpper B.skewUpper
  rw [source_split ht hm hmn hnq U]
  change cellValue v (D 0) (D 1) (D 2) L R p j H t ≤
    (Q + thermalLambda t * squareDeficit x + c (1+t) * (symmetricEnergy U x - squareEnergy x) +
      bias (1+t) * (∑ i : Fin 3, charge U i * (x i.succ^3 - x i.castSucc^3)) +
      e (1+t) * signedCubic U x) / s^2
  simp only [add_div] at hang ⊢
  unfold cellValue at hang ⊢
  linarith only [hheat, hsq, hang]

/-- Transfer the strict sign of the cell to the original normalized deficit,
retaining its margin in units of spread squared. -/
theorem normalizedDeficit_gt_of_cell
    (tracial : TracialSquareBound)
    {margin t lo hi T loss m n q v H L R j : ℝ} {lower upper : Fin 4 → ℝ} {D p : Fin 3 → ℝ}
    (ht₀ : 0 ≤ lo) (htl : lo ≤ t) (hth : t ≤ hi) (htT : t ≤ T)
    (hloss : thermalEntropyPenalty lo hi ≤ loss)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1) (hs : 0 < 1-m)
    (B : CellBounds (levelsAt m n q) lower upper lo hi T loss v H D p L R j)
    (check : CellInequality margin lo hi v (D 0) (D 1) (D 2) L R p j H)
    (U : unitary Mat) :
    margin * (1-m)^2 < normalizedDeficit (1+t) U m n q :=
  (lt_div_iff₀ (pow_pos hs 2)).mp <|
    (check t ⟨htl, hth⟩).trans_le
      (cellValue_le_normalizedDeficit tracial ht₀ htl hth htT hloss hm hmn hnq hq hs B U)

def shapeLevels (A C s : ℝ) : Fin 4 → ℝ :=
  levelsAt (1-s) (1-(1-A)*s) (1-C*s)

/-- Exact spectral spread predicate after passing to the trace-normalized
physical spectrum. Both adjacent shape faces and the rank-deficient faces
are closed. -/
def PhysicalShape (height A C s : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ C ∧ A+C ≤ 1 ∧ 0 < s ∧ s ≤ 1 ∧
    let f := (2-A+C)/4
    height ≤ s * (max f (1-f) + f*height)

theorem PhysicalShape.ordered {height A C s : ℝ} (hx : PhysicalShape height A C s) :
    0 ≤ 1-s ∧ 1-s ≤ 1-(1-A)*s ∧ 1-(1-A)*s ≤ 1-C*s ∧ 1-C*s ≤ 1 := by
  obtain ⟨hA, hC, hsum, hs, hs₁, _⟩ := hx
  exact ⟨sub_nonneg.mpr hs₁,
    by nlinarith only [mul_nonneg hA hs.le],
    by nlinarith only [mul_nonneg (show 0 ≤ 1-A-C by linarith) hs.le],
    by nlinarith only [mul_nonneg hC hs.le]⟩

private def logLower (w : ℝ) : ℝ := 2 * (w + w^3/3 + w^5/5)

private theorem log_lower {w : ℝ} (hw : 0 ≤ w) (hw₁ : w < 1) :
    logLower w ≤ Real.log ((1+w)/(1-w)) := by
  have h := Real.sum_range_le_log_div hw hw₁ 3
  norm_num [Finset.sum_range_succ] at h
  unfold logLower
  linarith only [h]

private theorem log_upper {w : ℝ} (hw : 0 ≤ w) (hw₁ : w < 1) :
    Real.log ((1+w)/(1-w)) ≤ logLower w + 2*w^7/(1-w^2) := by
  have h := Real.log_div_le_sum_range_add hw hw₁ 3
  norm_num [Finset.sum_range_succ] at h
  unfold logLower
  rw [mul_div_assoc]
  linarith only [h]

private def entropyPart (a : ℝ) : ℝ := a * Real.log a

set_option maxHeartbeats 1000000 in
private theorem shifted_log_upper {k : ℝ} (hk : 0 ≤ k) (hk₁ : k ≤ 1) :
    (1+k)^3 * Real.log (1+k) + (1-k)^3 * Real.log (1-k) ≤
      5*k^2 + k^4/2 + (4/75)*k^6 := by
  rcases hk₁.eq_or_lt with rfl | hlt
  · have hl := log_upper (w := 1/3) (by norm_num) (by norm_num)
    norm_num [logLower] at hl ⊢
    linarith only [hl]
  let p := k/(2+k)
  let m := k/(2-k)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hpd : 0 < 2+k := by positivity
  have hmd : 0 < 2-k := by linarith
  have hm : 0 ≤ m := div_nonneg hk hmd.le
  have hp₁ : p < 1 := (div_lt_one hpd).2 (by linarith)
  have hm₁ : m < 1 := (div_lt_one hmd).2 (by linarith)
  have his : (1+p)/(1-p) = 1+k := by
    apply (div_eq_iff (sub_pos.mpr hp₁).ne').2
    dsimp [p]
    field_simp [hpd.ne'] <;> ring
  have hiy : (1+m)/(1-m) = (1-k)⁻¹ := by
    apply (div_eq_iff (sub_pos.mpr hm₁).ne').2
    dsimp [m]
    field_simp [hmd.ne', (sub_pos.mpr hlt).ne'] <;> ring
  have hlog_pos := log_upper hp hp₁
  have hlog_neg := log_lower hm hm₁
  rw [his] at hlog_pos
  rw [hiy, Real.log_inv] at hlog_neg
  have hlog := add_le_add (mul_le_mul_of_nonneg_left hlog_pos (show 0 ≤ (1+k)^3 by positivity))
    (mul_le_mul_of_nonneg_left (show Real.log (1-k) ≤ -logLower m by linarith only [hlog_neg])
      (pow_nonneg (sub_nonneg.mpr hlt.le) 3))
  refine hlog.trans ?_
  have hpoly :
      5*k^2 + k^4/2 + (4/75)*k^6 -
        ((1+k)^3 * (logLower p + 2*p^7/(1-p^2)) + (1-k)^3 * (-logLower m)) =
        (3072*k^6*(1-k)^10 + 28320*k^7*(1-k)^9 + 112560*k^8*(1-k)^8 +
          253200*k^9*(1-k)^7 + 355320*k^10*(1-k)^6 +
          323154*k^11*(1-k)^5 + 192175*k^12*(1-k)^4 +
          74080*k^13*(1-k)^3 + 17890*k^14*(1-k)^2 + 2310*k^15*(1-k) +
          39*k^16)/(150*(2-k)^5*(2+k)^5) := by
    have hd : (2+k)^2-k^2 ≠ 0 := by nlinarith only [hk]
    dsimp [logLower, p, m]
    rw [show 1 - (k / (2+k))^2 = ((2+k)^2-k^2)/(2+k)^2 by
      field_simp [hpd.ne'] <;> ring]
    field_simp [hpd.ne', hmd.ne', hd] <;> ring
  have hk' : 0 ≤ 1-k := sub_nonneg.mpr hlt.le
  apply sub_nonneg.mp
  rw [hpoly]
  positivity

private theorem phi_lower {z : ℝ} (hz : 0 ≤ z) :
    (9/2)*z^2*((3/4)/(1+2*z/3)+(1/4)/(1+2*z)) ≤
      (1+3*z)*Real.log (1+3*z)-3*z := by
  let w := 3*z/(2+3*z)
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hd : 0 < 2+3*z := by positivity
  have hw₁ : w < 1 := (div_lt_one hd).2 (by linarith)
  have he : (1+w)/(1-w) = 1+3*z := by
    apply (div_eq_iff (sub_pos.mpr hw₁).ne').2
    dsimp [w]
    field_simp [hd.ne'] <;> ring
  have hl := log_lower hw hw₁
  rw [he] at hl
  refine le_trans ?_ (sub_le_sub_right (mul_le_mul_of_nonneg_left hl (by positivity)) _)
  have hp :
    (1+3*z)*logLower w-3*z - (9/2)*z^2*((3/4)/(1+2*z/3)+(1/4)/(1+2*z)) =
    9*z^4*(621*z^4+2169*z^3+1776*z^2+584*z+80)/(10*(2*z+1)*(2*z+3)*(3*z+2)^5) := by
    dsimp [w, logLower]
    field_simp [hd.ne', show 3*z+2 ≠ 0 by positivity,
      show 2*z+1 ≠ 0 by positivity, show 2*z+3 ≠ 0 by positivity,
      show 1+2*z/3 ≠ 0 by positivity, show 1+2*z ≠ 0 by positivity] <;> ring
  apply sub_nonneg.mp
  rw [hp]
  positivity

private def pairEntropy (a b : ℝ) : ℝ :=
  entropyPart (a^3) + entropyPart (b^3) - entropyPart (a^3+b^3) +
    (a^3+b^3)*Real.log 2

private def edgeDeficit (a b : ℝ) : ℝ := 9/16*(b-a)^2*(a+b) - pairEntropy a b/2

private theorem entropyPart_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    entropyPart (a*b) = a*entropyPart b + b*entropyPart a := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [entropyPart]
  rcases hb.eq_or_lt with rfl | hb
  · simp [entropyPart]
  unfold entropyPart
  rw [Real.log_mul ha.ne' hb.ne']
  ring

private theorem pairEntropy_scale {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) :
    pairEntropy (u*a) (u*b) = u^3*pairEntropy a b := by
  have hu' : 0 ≤ u^3 := pow_nonneg hu 3
  have ha' : 0 ≤ a^3 := pow_nonneg ha 3
  have hb' : 0 ≤ b^3 := pow_nonneg hb 3
  simp only [pairEntropy, mul_pow, ← mul_add]
  rw [entropyPart_mul hu' ha', entropyPart_mul hu' hb', entropyPart_mul hu' (add_nonneg ha' hb')]
  ring

private theorem normalized_edge {k : ℝ} (hk : 0 ≤ k) (hk₁ : k ≤ 1) :
    2*k^4*edgeGamma k ≤ edgeDeficit (1-k) (1+k) := by
  have hm : 0 < 1+3*k^2 := by positivity
  have hsum : (1-k)^3 + (1+k)^3 = 2*(1+3*k^2) := by ring
  have hr (a : ℝ) : entropyPart (a^3) = 3*a^3*Real.log a := by
    unfold entropyPart
    rw [Real.log_pow]
    norm_num
    ring
  have heq : edgeDeficit (1-k) (1+k) =
      (15/2)*k^2 - (3/2)*((1+k)^3*Real.log (1+k)+(1-k)^3*Real.log (1-k)) +
        ((1+3*k^2)*Real.log (1+3*k^2)-3*k^2) := by
    unfold edgeDeficit pairEntropy
    rw [hr, hr, hsum, entropyPart_mul (by norm_num : (0 : ℝ) ≤ 2) hm.le]
    unfold entropyPart
    ring
  rw [heq]
  have hphi := phi_lower (sq_nonneg k)
  have hlog := shifted_log_upper hk hk₁
  unfold edgeGamma
  nlinarith only [hphi, hlog]

private theorem edgeFloor_le_edgeDeficit {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    edgeFloor a b ≤ edgeDeficit a b := by
  have hb := ha.trans hab
  by_cases hz : a+b = 0
  · have ha' : a = 0 := by linarith
    have hb' : b = 0 := by linarith
    simp [ha', hb', edgeFloor, edgeDeficit, pairEntropy, entropyPart]
  have hu : 0 < (a+b)/2 := by
    exact half_pos (lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz))
  let u := (a+b)/2
  let k := (b-a)/(a+b)
  have hk : 0 ≤ k := div_nonneg (sub_nonneg.mpr hab) (add_nonneg ha hb)
  have hk₁ : k ≤ 1 := (div_le_one (show 0 < a+b by linarith only [hu])).2
    (by linarith)
  have hₐ : u*(1-k) = a := by
    dsimp [u,k]
    field_simp [hz] <;> ring
  have hᵦ : u*(1+k) = b := by
    dsimp [u,k]
    field_simp [hz] <;> ring
  have he₁ : edgeDeficit a b = u^3*edgeDeficit (1-k) (1+k) := by
    rw [← hₐ, ← hᵦ]
    unfold edgeDeficit
    rw [pairEntropy_scale (sub_nonneg.mpr hk₁) (by positivity) hu.le]
    ring
  have he₂ : edgeFloor a b = u^3*(2*k^4*edgeGamma k) := by
    unfold edgeFloor
    change (b-a)^4*edgeGamma k/(4*(a+b)) = _
    dsimp [u,k]
    field_simp [hz] <;> ring
  rw [he₁, he₂]
  exact mul_le_mul_of_nonneg_left (normalized_edge hk hk₁) (pow_nonneg hu.le 3)

open D5.S3.Divergence.ClassicalDPI (klDivergence)
open D5.S3.TotalVariation.Pinsker (totalVariation pinsker_inequality)

/-- The entropy tensorization surplus of a two-by-two table pays for the
squared determinant. The proof works directly with zero cells. -/
private theorem determinant_bound {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hM : 0 < a+b+c+d) :
    let M := a+b+c+d
    8*(a*d-b*c)^2/M^3 ≤
      entropyPart a + entropyPart b + entropyPart c + entropyPart d -
        (entropyPart (a+b) + entropyPart (c+d) + entropyPart (a+c) + entropyPart (b+d)) +
        entropyPart M := by
  intro M
  change 0 < M at hM
  let m : Fin 4 → ℝ := ![a,b,c,d]
  let row : Fin 4 → ℝ := ![a+b,a+b,c+d,c+d]
  let col : Fin 4 → ℝ := ![a+c,b+d,a+c,b+d]
  let p : Fin 4 → ℝ := fun i => m i/M
  let q : Fin 4 → ℝ := fun i => row i*col i/M^2
  have hm (i : Fin 4) : 0 ≤ m i := by
    fin_cases i <;> simp [m, ha, hb, hc, hd]
  have hr (i : Fin 4) : m i ≤ row i := by
    fin_cases i <;> simp [m, row] <;> linarith only [ha,hb,hc,hd]
  have hc' (i : Fin 4) : m i ≤ col i := by
    fin_cases i <;> simp [m, col] <;> linarith only [ha,hb,hc,hd]
  have hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 := by
    refine ⟨fun i => div_nonneg (hm i) hM.le, ?_⟩
    simp only [p, ← Finset.sum_div]
    rw [show (∑ i, m i) = M by simp [m,M,Fin.sum_univ_four], div_self hM.ne']
  have hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 := by
    refine ⟨fun i => div_nonneg (mul_nonneg ((hm i).trans (hr i)) ((hm i).trans (hc' i)))
      (sq_nonneg M), ?_⟩
    simp only [q, ← Finset.sum_div]
    apply (div_eq_iff (pow_ne_zero _ hM.ne')).2
    simp [row,col,Fin.sum_univ_four,M]
    <;> ring
  have hac (i : Fin 4) (hi : q i = 0) : p i = 0 := by
    rcases (hm i).eq_or_lt with h | h
    · simp [p, ← h]
    have hq' : 0 < q i := div_pos (mul_pos (h.trans_le (hr i)) (h.trans_le (hc' i))) (pow_pos hM 2)
    exact (hq'.ne' hi).elim
  let signs : Fin 4 → ℝ := ![1,-1,-1,1]
  have hdiff (i : Fin 4) : p i-q i = signs i*(a*d-b*c)/M^2 := by
    fin_cases i <;> simp [p,q,m,row,col,signs] <;> field_simp [hM.ne'] <;> dsimp [M] <;> ring
  have hdist (i : Fin 4) : |p i-q i| = |a*d-b*c|/M^2 := by
    have hsign : |signs i| = 1 := by fin_cases i <;> norm_num [signs]
    rw [hdiff, abs_div, abs_mul, hsign, one_mul, abs_of_nonneg (sq_nonneg M)]
  have htv : totalVariation p q = 2*|a*d-b*c|/M^2 := by
    simp only [totalVariation, hdist, Fin.sum_univ_four]
    ring
  have hpin := mul_le_mul_of_nonneg_left (pinsker_inequality p q hp hq hac) hM.le
  rw [htv] at hpin
  have hpin' :
      8*(a*d-b*c)^2/M^3 ≤ M*klDivergence p q := by
    have hh : M*(2*(2*|a*d-b*c|/M^2)^2) = 8*(a*d-b*c)^2/M^3 := by
      rw [div_pow, mul_pow, sq_abs]
      field_simp [hM.ne'] <;> ring
    rwa [hh] at hpin
  have hentry (i : Fin 4) :
      M*(p i*Real.log (p i/q i)) =
        entropyPart (m i) - m i*Real.log (row i) - m i*Real.log (col i) +
          m i*Real.log M := by
    rcases (hm i).eq_or_lt with h | h
    · simp [p, entropyPart, ← h]
    have hri := h.trans_le (hr i)
    have hci := h.trans_le (hc' i)
    have hpq : p i/q i = m i*M/(row i*col i) := by
      unfold p q
      field_simp [hM.ne', hri.ne', hci.ne'] <;> ring
    rw [hpq, Real.log_div (mul_ne_zero h.ne' hM.ne') (mul_ne_zero hri.ne' hci.ne'),
      Real.log_mul h.ne' hM.ne', Real.log_mul hri.ne' hci.ne']
    unfold p entropyPart
    field_simp [hM.ne'] <;> ring
  have heq : M*klDivergence p q =
      entropyPart a + entropyPart b + entropyPart c + entropyPart d -
        (entropyPart (a+b) + entropyPart (c+d) + entropyPart (a+c) + entropyPart (b+d)) +
        entropyPart M := by
    rw [klDivergence, Finset.mul_sum]
    simp only [hentry, m, row, col, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    unfold entropyPart
    dsimp [M]
    ring
  exact hpin'.trans_eq heq

theorem tracialSquare : TracialSquareBound := by
  intro x hx hx₀ hx₃
  have h01 := hx (show (0 : Fin 4) ≤ 1 by decide)
  have h02 := hx (show (0 : Fin 4) ≤ 2 by decide)
  have h13 := hx (show (1 : Fin 4) ≤ 3 by decide)
  have h23 := hx (show (2 : Fin 4) ≤ 3 by decide)
  have h₁ := hx₀.trans h01
  have h₂ := hx₀.trans h02
  have h₃ := h₁.trans h13
  have hm (i : Fin 4) : 0 ≤ x i := hx₀.trans (hx (Fin.zero_le i))
  have hM : 0 < mass x := by
    simp only [mass, Fin.sum_univ_four, hx₃, one_pow]
    positivity
  have hE := entropy_center hm hM
  have hEL : -entropyGap (fun i => x i^3) =
      entropyPart (mass x) - mass x * (2*Real.log 2) -
        (entropyPart (x 0^3) + entropyPart (x 1^3) +
          entropyPart (x 2^3) + entropyPart (x 3^3)) := by
    rw [hE, Real.log_div hM.ne' (by norm_num : (4 : ℝ) ≠ 0),
      show (4 : ℝ) = 2^2 by norm_num, Real.log_pow, Fin.sum_univ_four]
    norm_num [entropyPart]
    <;> ring
  have hD := determinant_bound (pow_nonneg hx₀ 3) (pow_nonneg h₁ 3)
    (pow_nonneg h₂ 3) (pow_nonneg h₃ 3) (by simpa [mass, Fin.sum_univ_four] using hM)
  dsimp only at hD
  rw [show x 0^3+x 1^3+x 2^3+x 3^3 = mass x by simp [mass, Fin.sum_univ_four],
    show x 0^3*x 3^3-x 1^3*x 2^3 = x 0^3-(x 1*x 2)^3 by rw [hx₃]; ring] at hD
  have he₀ := edgeFloor_le_edgeDeficit hx₀ h01
  have he₁ := edgeFloor_le_edgeDeficit hx₀ h02
  have he₂ := edgeFloor_le_edgeDeficit h₁ h13
  have he₃ := edgeFloor_le_edgeDeficit h₂ h23
  unfold squareFloor squareDeficit squareEnergy
  simp only [edgeDeficit, pairEntropy] at he₀ he₁ he₂ he₃
  have hsum : mass x = x 0^3+x 1^3+x 2^3+x 3^3 := by simp [mass,Fin.sum_univ_four]
  linear_combination he₀ + he₁ + he₂ + he₃ + hD/2 - hEL/2 +
    Real.log 2 * hsum

private theorem chargeMinimum_attained {w p : ℝ} (hw : 0 ≤ w) (hp : 0 ≤ p) :
    ∃ y ∈ Set.Icc (0 : ℝ) 1, chargeMinimum w p = w*y^2 - p*y := by
  unfold chargeMinimum
  split_ifs with h
  · exact ⟨1, ⟨by norm_num, le_rfl⟩, by ring⟩
  · have hw' : 0 < w := by linarith
    have hden : 0 < 2*w := by positivity
    refine ⟨p/(2*w), ⟨div_nonneg hp hden.le, (div_le_one hden).2 (le_of_not_ge h)⟩, ?_⟩
    field_simp [hw'.ne'] <;> ring

private theorem chargeMinimum_secant {w p T t : ℝ} (hw : 0 ≤ w) (hp : 0 ≤ p)
    (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) :
    (1-t/T)*chargeMinimum w 0 + (t/T)*chargeMinimum w (T*p) ≤
      chargeMinimum w (t*p) := by
  obtain ⟨y, hy, hmin⟩ := chargeMinimum_attained hw (mul_nonneg ht hp)
  have h₀ := mul_le_mul_of_nonneg_left (chargeMinimum_le hw le_rfl hy)
    (sub_nonneg.mpr ((div_le_one hT).2 htT))
  have h₁ := mul_le_mul_of_nonneg_left
    (chargeMinimum_le hw (mul_nonneg hT.le hp) hy) (div_nonneg ht hT.le)
  rw [hmin]
  have he : (1-t/T)*(w*y^2 - 0*y)+(t/T)*(w*y^2-T*p*y) = w*y^2-t*p*y := by
    field_simp [hT.ne'] <;> ring
  exact (add_le_add h₀ h₁).trans_eq he

/-- A rational lower bound valid for the entire interval [0,T].
The angular cost is concave in thermal displacement because it is the
minimum of affine functions. The quadratic thermal gain stays inside the
minimization, including when the minimizing displacement is interior. -/
def secantFloor (v d₀ d₁ d₂ l u : ℝ) (p : Fin 3 → ℝ) (j H T : ℝ) : ℝ :=
  let base := cellValue v d₀ d₁ d₂ l u p j 0 0
  let penalty := base - cellValue v d₀ d₁ d₂ l u p j 0 T
  base + chargeMinimum (H*T^2) penalty

theorem cellInequality_of_secantFloor
    {margin v d₀ d₁ d₂ l u j H T : ℝ} {p : Fin 3 → ℝ}
    (hT : 0 < T) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hl : 0 ≤ l) (hu : 0 ≤ u) (hp : ∀ i, 0 ≤ p i) (hj : 0 ≤ j) (hH : 0 ≤ H)
    (check : margin < secantFloor v d₀ d₁ d₂ l u p j H T) :
    CellInequality margin 0 T v d₀ d₁ d₂ l u p j H := by
  intro t ht
  let y := t/T
  let base := cellValue v d₀ d₁ d₂ l u p j 0 0
  let penalty := base - cellValue v d₀ d₁ d₂ l u p j 0 T
  have hG0 {w : ℝ} (hw : 0 ≤ w) : chargeMinimum w 0 = 0 := by
    unfold chargeMinimum
    split_ifs with h
    · linarith
    · simp
  have hbase : base = v+(d₀+d₂)/2 := by
    simp [base, cellValue, hG0 (add_nonneg hd₀ hl), hG0 hd₁, hG0 (add_nonneg hd₂ hu)]
    <;> ring
  have hy : y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hT.le, (div_le_one hT).2 ht.2⟩
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hpen : 0 ≤ penalty := by
    have h₀ := chargeMinimum_le (add_nonneg hd₀ hl) (mul_nonneg hT.le (hp 0)) hzero
    have h₁ := chargeMinimum_le hd₁ (mul_nonneg hT.le (hp 1)) hzero
    have h₂ := chargeMinimum_le (add_nonneg hd₂ hu) (mul_nonneg hT.le (hp 2)) hzero
    dsimp [penalty]
    rw [hbase]
    unfold cellValue
    linarith only [h₀,h₁,h₂,mul_nonneg hT.le (hp 0),mul_nonneg hT.le (hp 2),
      mul_nonneg hj hT.le]
  have hmin := chargeMinimum_le (mul_nonneg hH (sq_nonneg T)) hpen hy
  have hsec : base - penalty*y + H*t^2 ≤ cellValue v d₀ d₁ d₂ l u p j H t := by
    have h₀ := chargeMinimum_secant (add_nonneg hd₀ hl) (hp 0) hT ht.1 ht.2
    have h₁ := chargeMinimum_secant hd₁ (hp 1) hT ht.1 ht.2
    have h₂ := chargeMinimum_secant (add_nonneg hd₂ hu) (hp 2) hT ht.1 ht.2
    change (1-y)*chargeMinimum (d₀+l) 0 + y*chargeMinimum (d₀+l) (T*p 0) ≤ _ at h₀
    change (1-y)*chargeMinimum d₁ 0 + y*chargeMinimum d₁ (T*p 1) ≤ _ at h₁
    change (1-y)*chargeMinimum (d₂+u) 0 + y*chargeMinimum (d₂+u) (T*p 2) ≤ _ at h₂
    rw [hG0 (add_nonneg hd₀ hl), mul_zero, zero_add] at h₀
    rw [hG0 hd₁, mul_zero, zero_add] at h₁
    rw [hG0 (add_nonneg hd₂ hu), mul_zero, zero_add] at h₂
    have hyT : y*T = t := div_mul_cancel₀ t hT.ne'
    dsimp [penalty]
    rw [hbase]
    unfold cellValue
    linear_combination h₀ / 2 + h₁ + h₂ / 2 -
      (p 0 / 2 + p 2 / 2 + j) * hyT
  have hheat : H*T^2*y^2 = H*t^2 := by dsimp [y]; field_simp [hT.ne'] <;> ring
  rw [hheat] at hmin
  refine check.trans_le (le_trans ?_ hsec)
  change base + chargeMinimum (H*T^2) penalty ≤ base - penalty*y + H*t^2
  linarith only [hmin]

/-- A complete geometric cover supplies endpoint enclosures and one strict
rational secant test for every surviving spectral cell. -/
def HotCover (margin T height loss : ℝ) : Prop :=
  ∀ A C s : ℝ, PhysicalShape height A C s →
    ∃ (lower upper : Fin 4 → ℝ) (D p : Fin 3 → ℝ) (v H L R j : ℝ),
      CellBounds (shapeLevels A C s) lower upper 0 T T loss v H D p L R j ∧
      0 ≤ H ∧ 0 ≤ j ∧ margin < secantFloor v (D 0) (D 1) (D 2) L R p j H T

/-- Source-level hot outer reduction. A cover at either reviewed set of
parameters gives its original strict margin throughout the closed region. -/
theorem normalizedDeficit_gt_of_hotCover {margin T height loss t A C s : ℝ}
    (hT : 0 < T) (hloss : thermalEntropyPenalty 0 T ≤ loss)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (hshape : PhysicalShape height A C s)
    (cover : HotCover margin T height loss) (U : unitary Mat) :
    margin*s^2 < normalizedDeficit (1+t) U (1-s) (1-(1-A)*s) (1-C*s) := by
  obtain ⟨hm, hmn, hnq, hq⟩ := hshape.ordered
  obtain ⟨lower,upper,D,p,v,H,L,R,j,B,hH,hj,hcheck⟩ := cover A C s hshape
  have hmargin := normalizedDeficit_gt_of_cell tracialSquare le_rfl ht.1 ht.2 ht.2
    hloss hm hmn hnq hq (by linarith only [hshape.2.2.2.1]) B
    (cellInequality_of_secantFloor hT (B.diagonalNonneg 0) (B.diagonalNonneg 1)
      (B.diagonalNonneg 2) B.lowerAdjacentNonneg B.upperAdjacentNonneg B.chargeNonneg
      hj hH hcheck) U
  convert hmargin using 1 <;> ring

theorem first_outer {t A C s : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) firstLimit) (hshape : PhysicalShape firstHeight A C s)
    (cover : HotCover (1/2000) firstLimit firstHeight (1/2)) (U : unitary Mat) :
    s^2/2000 < normalizedDeficit (1+t) U (1-s) (1-(1-A)*s) (1-C*s) := by
  have h := normalizedDeficit_gt_of_hotCover (by norm_num [firstLimit]) first_loss ht hshape cover U
  linarith only [h]

theorem extended_outer {t A C s : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) extendedLimit) (hshape : PhysicalShape extendedHeight A C s)
    (cover : HotCover (1/4000) extendedLimit extendedHeight (3/7)) (U : unitary Mat) :
    s^2/4000 < normalizedDeficit (1+t) U (1-s) (1-(1-A)*s) (1-C*s) := by
  have h := normalizedDeficit_gt_of_hotCover (by norm_num [extendedLimit]) extended_loss ht hshape cover U
  linarith only [h]

/-- Coordinatewise endpoint data after intersecting a box with the shape
triangle and raising its lower spread endpoint. -/
structure SpectralEnclosure (x lower upper : Fin 4 → ℝ) (zlo zhi : Fin 3 → ℝ)
    (slo shi : ℝ) : Prop where
  rootsNonneg : ∀ i, 0 ≤ lower i
  rootsLower : ∀ i, lower i ≤ x i
  rootsUpper : ∀ i, x i ≤ upper i
  massLowerPos : 0 < mass lower
  gapNonneg : ∀ i, 0 ≤ zlo i
  gapLower : ∀ i, zlo i ≤ gapFraction x i
  gapUpper : ∀ i, gapFraction x i ≤ zhi i
  gapAtMostOne : ∀ i, zhi i ≤ 1
  spreadLowerPos : 0 < slo
  spreadLower : slo ≤ spread x
  spreadUpper : spread x ≤ shi

private theorem edgeGamma_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    edgeGamma b ≤ edgeGamma a := by
  have hb := ha.trans hab
  have hs := pow_le_pow_left₀ ha hab 2
  have h₀ : (3/4 : ℝ)/(1+2*b^2/3) ≤ (3/4)/(1+2*a^2/3) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hs])
  have h₁ : (1/4 : ℝ)/(1+2*b^2) ≤ (1/4)/(1+2*a^2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hs])
  unfold edgeGamma
  linarith only [h₀,h₁,hs]

private theorem edgeGamma_nonneg {k : ℝ} (hk : 0 ≤ k) (hk₁ : k ≤ 1) :
    0 ≤ edgeGamma k := by
  refine le_trans ?_ (edgeGamma_antitone hk hk₁)
  norm_num [edgeGamma]

private theorem edgeFloor_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ edgeFloor a b := by
  have hsum := add_nonneg ha (ha.trans hab)
  have hk := div_nonneg (sub_nonneg.mpr hab) hsum
  have hk₁ : (b-a)/(a+b) ≤ 1 := by
    rcases hsum.eq_or_lt with h | h
    · simp [← h]
    · exact (div_le_one h).2 (by linarith)
  unfold edgeFloor
  exact div_nonneg (mul_nonneg (pow_nonneg (sub_nonneg.mpr hab) 4)
    (edgeGamma_nonneg hk hk₁)) (by positivity)

/-- Scaled edge bound evaluated at the endpoints of a spectral cell. -/
def edgeBoxFloor (slo shi llo lhi ulo uhi : ℝ) : ℝ :=
  let k := if ulo = 0 then 1 else min 1 (shi*lhi/ulo)
  slo^2*llo^4*edgeGamma k/(4*uhi)

private theorem edgeBoxFloor_le {a b s slo shi llo lhi ulo uhi : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hslo : 0 < slo) (hs : slo ≤ s) (hshi : s ≤ shi)
    (hllo : 0 ≤ llo) (hl : llo ≤ (b-a)/s) (hlhi : (b-a)/s ≤ lhi)
    (hulo : 0 ≤ ulo) (hul : ulo ≤ a+b) (huh : a+b ≤ uhi) :
    edgeBoxFloor slo shi llo lhi ulo uhi ≤ edgeFloor a b/s^2 := by
  have hs₀ := hslo.trans_le hs
  by_cases hz : a+b = 0
  · have hb : b = a := by linarith only [hz,ha,hab]
    have hz' : llo = 0 := by
      have : llo ≤ 0 := by simpa [hb] using hl
      exact le_antisymm this hllo
    simp [edgeBoxFloor, edgeFloor, hb, hz']
  have hsum : 0 < a+b := lt_of_le_of_ne (by linarith only [ha,hab]) (Ne.symm hz)
  let k := (b-a)/(a+b)
  let K := if ulo = 0 then 1 else min 1 (shi*lhi/ulo)
  have hk₀ : 0 ≤ k := div_nonneg (sub_nonneg.mpr hab) hsum.le
  have hk₁ : k ≤ 1 := (div_le_one hsum).2 (by linarith)
  have hk : k ≤ K := by
    dsimp only [K]
    split_ifs with h
    · exact hk₁
    · have hulo' : 0 < ulo := lt_of_le_of_ne hulo (Ne.symm h)
      apply le_min hk₁
      have hn : b-a ≤ shi*lhi := by
        have h₀ := (div_le_iff₀ hs₀).1 hlhi
        exact h₀.trans (by
          rw [mul_comm lhi s]
          exact mul_le_mul_of_nonneg_right hshi ((hllo.trans hl).trans hlhi))
      exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hulo' hul).trans
        (div_le_div_of_nonneg_right hn hulo'.le)
  have hK : K ≤ 1 := by dsimp only [K]; split_ifs <;> simp
  have hΓ := edgeGamma_antitone hk₀ hk
  have hΓ₀ := edgeGamma_nonneg (hk₀.trans hk) hK
  have heq : edgeFloor a b/s^2 = s^2*((b-a)/s)^4*edgeGamma k/(4*(a+b)) := by
    unfold edgeFloor
    change (b-a)^4*edgeGamma k/(4*(a+b))/s^2 = _
    field_simp [hs₀.ne',hz] <;> ring
  rw [heq]
  change slo^2*llo^4*edgeGamma K/(4*uhi) ≤ _
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left huh (by norm_num : (0 : ℝ) ≤ 4))).trans
    (div_le_div_of_nonneg_right (mul_le_mul
      (mul_le_mul (pow_le_pow_left₀ hslo.le hs 2) (pow_le_pow_left₀ hllo hl 4)
        (pow_nonneg hllo 4) (sq_nonneg s)) hΓ hΓ₀ (by positivity)) (by positivity))

def determinantBoxFloor (lower upper : Fin 4 → ℝ) (shi : ℝ) : ℝ :=
  let Dlo := lower 0^3 - (upper 1*upper 2)^3
  let Dhi := upper 0^3 - (lower 1*lower 2)^3
  4 * (max 0 (max Dlo (-Dhi)))^2 / (shi^2 * mass upper^3)

private theorem determinantBoxFloor_le {x lower upper : Fin 4 → ℝ} {zlo zhi : Fin 3 → ℝ}
    {slo shi : ℝ} (B : SpectralEnclosure x lower upper zlo zhi slo shi) :
    determinantBoxFloor lower upper shi ≤
      (4*(x 0^3-(x 1*x 2)^3)^2/mass x^3)/spread x^2 := by
  have hl := B.rootsNonneg
  have hx (i : Fin 4) := (hl i).trans (B.rootsLower i)
  have hu (i : Fin 4) := (hx i).trans (B.rootsUpper i)
  have hmL : mass lower ≤ mass x := Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (hl i) (B.rootsLower i) 3
  have hmU : mass x ≤ mass upper := Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (hx i) (B.rootsUpper i) 3
  have hm := B.massLowerPos.trans_le hmL
  have hs := B.spreadLowerPos.trans_le B.spreadLower
  have hshi := hs.trans_le B.spreadUpper
  let det := x 0^3-(x 1*x 2)^3
  have h₀ : lower 0^3-(upper 1*upper 2)^3 ≤ det := by
    dsimp [det]
    apply sub_le_sub (pow_le_pow_left₀ (hl 0) (B.rootsLower 0) 3)
    exact pow_le_pow_left₀ (mul_nonneg (hx 1) (hx 2))
      (mul_le_mul (B.rootsUpper 1) (B.rootsUpper 2) (hx 2) (hu 1)) 3
  have h₁ : det ≤ upper 0^3-(lower 1*lower 2)^3 := by
    dsimp [det]
    apply sub_le_sub (pow_le_pow_left₀ (hx 0) (B.rootsUpper 0) 3)
    exact pow_le_pow_left₀ (mul_nonneg (hl 1) (hl 2))
      (mul_le_mul (B.rootsLower 1) (B.rootsLower 2) (hl 2) (hx 1)) 3
  have habs := max_le (abs_nonneg det) (max_le (h₀.trans (le_abs_self det))
    ((neg_le_neg h₁).trans (neg_le_abs det)))
  unfold determinantBoxFloor
  rw [div_div, mul_comm (mass x^3)]
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul (pow_le_pow_left₀ hs.le B.spreadUpper 2)
      (pow_le_pow_left₀ hm.le hmU 3) (pow_nonneg hm.le 3) (sq_nonneg shi))).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsq := pow_le_pow_left₀ (le_max_left _ _) habs 2
  rw [sq_abs] at hsq
  exact mul_le_mul_of_nonneg_left hsq (by norm_num)

def tracialBoxFloor (T slo shi : ℝ) (lower upper : Fin 4 → ℝ) (zlo zhi : Fin 3 → ℝ) : ℝ :=
  (edgeBoxFloor slo shi (zlo 0) (zhi 0) (lower 0+lower 1) (upper 0+upper 1) +
    edgeBoxFloor slo shi (1-zhi 2) (1-zlo 2) (lower 0+lower 2) (upper 0+upper 2) +
    edgeBoxFloor slo shi (1-zhi 0) (1-zlo 0) (lower 1+lower 3) (upper 1+upper 3) +
    edgeBoxFloor slo shi (zlo 2) (zhi 2) (lower 2+lower 3) (upper 2+upper 3) +
    determinantBoxFloor lower upper shi)/(1+T^2)

private theorem tracialBoxFloor_le {x lower upper : Fin 4 → ℝ} {zlo zhi : Fin 3 → ℝ}
    {T slo shi : ℝ} (hx : Monotone x)
    (B : SpectralEnclosure x lower upper zlo zhi slo shi) :
    tracialBoxFloor T slo shi lower upper zlo zhi ≤ squareFloor x/((1+T^2)*spread x^2) := by
  have hs := B.spreadLowerPos.trans_le B.spreadLower
  have hx_nonneg (i : Fin 4) := (B.rootsNonneg i).trans (B.rootsLower i)
  have h₁ : (x 2-x 0)/spread x = 1-gapFraction x 2 := by
    change (x 2-x 0)/spread x = 1-(x 3-x 2)/spread x
    field_simp [hs.ne'] <;> unfold spread <;> ring
  have h₂ : (x 3-x 1)/spread x = 1-gapFraction x 0 := by
    change (x 3-x 1)/spread x = 1-(x 1-x 0)/spread x
    field_simp [hs.ne'] <;> unfold spread <;> ring
  have hEdge (i j : Fin 4) {l u : ℝ} (hij : i ≤ j)
      (h₀ : 0 ≤ l) (hl : l ≤ (x j-x i)/spread x) (hu : (x j-x i)/spread x ≤ u) :=
    edgeBoxFloor_le (hx_nonneg i) (hx hij) B.spreadLowerPos B.spreadLower B.spreadUpper h₀ hl hu
      (add_nonneg (B.rootsNonneg i) (B.rootsNonneg j))
      (add_le_add (B.rootsLower i) (B.rootsLower j)) (add_le_add (B.rootsUpper i) (B.rootsUpper j))
  have he₀ := hEdge 0 1 (by decide) (B.gapNonneg 0) (B.gapLower 0) (B.gapUpper 0)
  have he₁ := hEdge 0 2 (u := 1 - zlo 2) (by decide) (sub_nonneg.mpr (B.gapAtMostOne 2))
    (by rw [h₁]; exact sub_le_sub_left (B.gapUpper 2) 1)
    (by rw [h₁]; exact sub_le_sub_left (B.gapLower 2) 1)
  have he₂ := hEdge 1 3 (u := 1 - zlo 0) (by decide) (sub_nonneg.mpr (B.gapAtMostOne 0))
    (by rw [h₂]; exact sub_le_sub_left (B.gapUpper 0) 1)
    (by rw [h₂]; exact sub_le_sub_left (B.gapLower 0) 1)
  have he₃ := hEdge 2 3 (by decide) (B.gapNonneg 2) (B.gapLower 2) (B.gapUpper 2)
  have he₄ := determinantBoxFloor_le B
  unfold tracialBoxFloor squareFloor
  rw [mul_comm (1+T^2), ← div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simp only [add_div]
  linarith only [he₀, he₁, he₂, he₃, he₄]

def diagonalBox (T : ℝ) (lower : Fin 4 → ℝ) (zlo : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (9/8/(1+T^2))*zlo i^2*adjacentSum lower i

def adjacentBox (T : ℝ) (lower : Fin 4 → ℝ) (zlo : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  (9/8/(1+T^2))*zlo i*zlo j*(adjacentSum lower i+adjacentSum lower j)

def chargeBox (slo shi : ℝ) (upper : Fin 4 → ℝ) (zhi : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  let a := upper i.castSucc
  let b := upper i.succ
  (3/2)*zhi i*(a^2+a*b+b^2)/slo+(3/16)*shi*zhi i*(1+zhi i^2)

def skewBox (shi : ℝ) (zlo zhi : Fin 3 → ℝ) : ℝ :=
  (3/16)*shi*∑ i : Fin 3, spectralCutCap i*zhi i*(1-zlo i^2)

def heatBox (T loss shi : ℝ) (lower upper : Fin 4 → ℝ) : ℝ :=
  cellCoefficient 0 T loss lower upper * mass lower / shi^2

/-- Soundness of the endpoint substitutions in the rational check. -/
theorem cellBounds_of_enclosure {x lower upper : Fin 4 → ℝ} {zlo zhi : Fin 3 → ℝ}
    {T loss slo shi : ℝ} (hx : Monotone x) (hk : 0 ≤ uniformCoefficient T loss)
    (B : SpectralEnclosure x lower upper zlo zhi slo shi) :
    CellBounds x lower upper 0 T T loss (tracialBoxFloor T slo shi lower upper zlo zhi)
      (heatBox T loss shi lower upper) (diagonalBox T lower zlo) (chargeBox slo shi upper zhi)
      (adjacentBox T lower zlo 0 1) (adjacentBox T lower zlo 1 2) (skewBox shi zlo zhi) := by
  have hs := B.spreadLowerPos.trans_le B.spreadLower
  have hshi := hs.trans_le B.spreadUpper
  have hl := B.rootsNonneg
  have hr := B.rootsLower
  have hu := B.rootsUpper
  have hx₀ (i : Fin 4) := (hl i).trans (hr i)
  have hu₀ (i : Fin 4) := (hx₀ i).trans (hu i)
  have hz₀ := B.gapNonneg
  have hzl := B.gapLower
  have hzu := B.gapUpper
  have hz₁ := B.gapAtMostOne
  have hz i := (hz₀ i).trans (hzl i)
  have hzh i := (hz i).trans (hzu i)
  have hcap (i : Fin 3) : 0 ≤ spectralCutCap i := by
    fin_cases i <;> norm_num [spectralCutCap]
  have htr : 0 ≤ squareFloor x := by
    unfold squareFloor
    have h₀ := edgeFloor_nonneg (hx₀ 0) (hx (show (0 : Fin 4) ≤ 1 by decide))
    have h₁ := edgeFloor_nonneg (hx₀ 0) (hx (show (0 : Fin 4) ≤ 2 by decide))
    have h₂ := edgeFloor_nonneg (hx₀ 1) (hx (show (1 : Fin 4) ≤ 3 by decide))
    have h₃ := edgeFloor_nonneg (hx₀ 2) (hx (show (2 : Fin 4) ≤ 3 by decide))
    have hM : 0 ≤ mass x := Finset.sum_nonneg fun i _ => pow_nonneg (hx₀ i) 3
    positivity
  have hK : 0 ≤ cellCoefficient 0 T loss lower upper := hk.trans (le_max_left _ _)
  have hM : mass lower ≤ mass x := Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (hl i) (hr i) 3
  have hdiag (i : Fin 3) : 0 ≤ diagonalBox T lower zlo i := by
    unfold diagonalBox adjacentSum
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (add_nonneg (hl _) (hl _))
  have hadj₀ (i j : Fin 3) : 0 ≤ adjacentBox T lower zlo i j := by
    unfold adjacentBox adjacentSum
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hz₀ i)) (hz₀ j))
      (add_nonneg (add_nonneg (hl _) (hl _)) (add_nonneg (hl _) (hl _)))
  have hadj (i j : Fin 3) : adjacentBox T lower zlo i j ≤
      (9/8/(1+T^2))*adjacent x i j := by
    unfold adjacentBox adjacent adjacentSum
    rw [← mul_assoc, ← mul_assoc]
    gcongr <;> first | positivity | exact hzl _ | exact hr _ | exact hz₀ _ |
      exact add_nonneg (add_nonneg (hl _) (hl _)) (add_nonneg (hl _) (hl _)) |
      exact mul_nonneg (by positivity) (hz _) |
      exact mul_nonneg (mul_nonneg (by positivity) (hz _)) (hz _)
  refine ⟨hr, hu, B.massLowerPos, htr, tracialBoxFloor_le hx B, ?_,
    hdiag, hadj₀ 0 1, hadj₀ 1 2, ?_, hadj 0 1, hadj 1 2, ?_, ?_, ?_⟩
  · unfold heatBox
    exact (div_le_div_of_nonneg_left (mul_nonneg hK B.massLowerPos.le) (pow_pos hs 2)
      (pow_le_pow_left₀ hs.le B.spreadUpper 2)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM hK) (sq_nonneg _))
  · intro i
    unfold diagonalBox diagonal adjacentSum
    rw [← mul_assoc]
    gcongr <;> first | positivity | exact hzl _ | exact hr _ | exact hz₀ _ |
      exact add_nonneg (hl _) (hl _)
  · intro i
    unfold chargeBox
    dsimp only
    exact add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hzh i))
        (add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (hu₀ _) (hu₀ _))) (sq_nonneg _)))
        B.spreadLowerPos.le)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hshi.le) (hzh i)) (by positivity))
  · intro i
    unfold chargeSlope chargeBox
    dsimp only
    have hquad (y : Fin 4 → ℝ) (hy : ∀ k, 0 ≤ y k) :
        0 ≤ y i.castSucc ^ 2 + y i.castSucc * y i.succ + y i.succ ^ 2 :=
      add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (hy _) (hy _))) (sq_nonneg _)
    apply add_le_add
    · apply div_le_div₀ _ _ B.spreadLowerPos B.spreadLower
      · exact mul_nonneg (mul_nonneg (by norm_num) (hzh i)) (hquad upper hu₀)
      · apply mul_le_mul _ _ (hquad x hx₀) (mul_nonneg (by norm_num) (hzh i))
        · exact mul_le_mul_of_nonneg_left (hzu i) (by norm_num)
        · exact add_le_add
            (add_le_add (pow_le_pow_left₀ (hx₀ _) (hu _) 2)
              (mul_le_mul (hu _) (hu _) (hx₀ _) (hu₀ _)))
            (pow_le_pow_left₀ (hx₀ _) (hu _) 2)
    · apply mul_le_mul _ _ (by positivity)
        (mul_nonneg (mul_nonneg (by norm_num) hshi.le) (hzh i))
      · exact mul_le_mul (mul_le_mul_of_nonneg_left B.spreadUpper (by norm_num)) (hzu i)
          (hz i) (mul_nonneg (by norm_num) hshi.le)
      · exact add_le_add_right (pow_le_pow_left₀ (hz i) (hzu i) 2) 1
  · unfold skewSlope skewBox
    have hsq i : 0 ≤ 1-gapFraction x i^2 := by
      have h := pow_le_pow_left₀ (hz i) ((hzu i).trans (hz₁ i)) 2
      rw [one_pow] at h
      exact sub_nonneg.mpr h
    have hq i : 0 ≤ 1-zlo i^2 := by
      have h := pow_le_pow_left₀ (hz₀ i) ((hzl i).trans ((hzu i).trans (hz₁ i))) 2
      rw [one_pow] at h
      exact sub_nonneg.mpr h
    have hsum : (∑ i : Fin 3, spectralCutCap i * gapFraction x i * (1-gapFraction x i^2)) ≤
        ∑ i : Fin 3, spectralCutCap i*zhi i*(1-zlo i^2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hzu i) (hcap i))
        (sub_le_sub_left (pow_le_pow_left₀ (hz₀ i) (hzl i) 2) 1)
        (hsq i) (mul_nonneg (hcap i) (hzh i))
    apply mul_le_mul (mul_le_mul_of_nonneg_left B.spreadUpper (by norm_num)) hsum
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hcap i) (hz i)) (hsq i)
    · positivity

/-- Endpoints of a closed box in the two shape coordinates and the spread. -/
structure ShapeBox where
  aLo : ℝ
  aHi : ℝ
  cLo : ℝ
  cHi : ℝ
  sLo : ℝ
  sHi : ℝ

def ShapeBox.contains (B : ShapeBox) (A C s : ℝ) : Prop :=
  A ∈ Set.Icc B.aLo B.aHi ∧ C ∈ Set.Icc B.cLo B.cHi ∧ s ∈ Set.Icc B.sLo B.sHi

def ShapeBox.aUpper (B : ShapeBox) : ℝ := min B.aHi (1-B.cLo)
def ShapeBox.cUpper (B : ShapeBox) : ℝ := min B.cHi (1-B.aLo)

def shapeDenominator (height f : ℝ) : ℝ := max f (1-f) + f*height

def spreadFloor (height : ℝ) : ℝ := height / ((3/4)*(1+height))

def ShapeBox.sLower (B : ShapeBox) (height : ℝ) : ℝ :=
  let flo := (2-B.aUpper+B.cLo)/4
  let fhi := (2-B.aLo+B.cUpper)/4
  max B.sLo (height / max (shapeDenominator height flo) (shapeDenominator height fhi))

def ShapeBox.lowerRoots (B : ShapeBox) : Fin 4 → ℝ :=
  ![1-B.sHi, 1-(1-B.aLo)*B.sHi, 1-B.cUpper*B.sHi, 1]

def ShapeBox.upperRoots (B : ShapeBox) (height : ℝ) : Fin 4 → ℝ :=
  ![1-B.sLower height, 1-(1-B.aUpper)*B.sLower height, 1-B.cLo*B.sLower height, 1]

def ShapeBox.lowerGaps (B : ShapeBox) : Fin 3 → ℝ :=
  ![B.aLo, max 0 (1-B.aUpper-B.cUpper), B.cLo]

def ShapeBox.upperGaps (B : ShapeBox) : Fin 3 → ℝ :=
  ![B.aUpper, 1-B.aLo-B.cLo, B.cUpper]

theorem PhysicalShape.spreadFloor_le {height A C s : ℝ}
    (hheight : 0 ≤ height) (hx : PhysicalShape height A C s) : spreadFloor height ≤ s := by
  obtain ⟨ha, hc, hac, hs, _, h⟩ := hx
  let f := (2-A+C)/4
  change height ≤ s * shapeDenominator height f at h
  have hf₁ : f ≤ 3/4 := by dsimp [f]; linarith only [ha,hac]
  have hf₀ : 1-f ≤ 3/4 := by dsimp [f]; linarith only [hc,hac]
  have hden : shapeDenominator height f ≤ (3/4)*(1+height) := by
    unfold shapeDenominator
    linarith only [max_le hf₁ hf₀, mul_le_mul_of_nonneg_right hf₁ hheight]
  apply (div_le_iff₀ (show 0 < (3/4)*(1+height) by positivity)).2
  exact h.trans (by simpa only [mul_comm s] using mul_le_mul_of_nonneg_left hden hs.le)

private theorem shape_fractions {A C s : ℝ} (hs : 0 < s) :
    spread (shapeLevels A C s) = s ∧
      gapFraction (shapeLevels A C s) = ![A, 1-A-C, C] := by
  have hspread : spread (shapeLevels A C s) = s := by
    unfold spread shapeLevels levelsAt
    simp
  refine ⟨hspread, ?_⟩
  funext i
  unfold gapFraction
  rw [hspread]
  fin_cases i <;> simp [spectralGap, shapeLevels, levelsAt] <;> field_simp [hs.ne'] <;> ring

theorem ShapeBox.enclosure {B : ShapeBox} {height A C s : ℝ}
    (hheight : 0 ≤ height) (hheight₁ : height ≤ 1) (hx : PhysicalShape height A C s)
    (hB : B.contains A C s) (ha₀ : 0 ≤ B.aLo) (hc₀ : 0 ≤ B.cLo)
    (hs₀ : 0 < B.sLo) (hs₁ : B.sHi ≤ 1) :
    SpectralEnclosure (shapeLevels A C s) B.lowerRoots (B.upperRoots height)
      B.lowerGaps B.upperGaps (B.sLower height) B.sHi := by
  obtain ⟨ha,hc,hac,hs,hs',h⟩ := hx
  obtain ⟨hA,hC,hS⟩ := hB
  have haU : A ≤ B.aUpper :=
    le_min hA.2 (by linarith only [hac,hC.1])
  have hcU : C ≤ B.cUpper :=
    le_min hC.2 (by linarith only [hac,hA.1])
  have haU₁ : B.aUpper ≤ 1 :=
    (min_le_right B.aHi (1-B.cLo)).trans (by linarith)
  have hcU₁ : B.cUpper ≤ 1 :=
    (min_le_right B.cHi (1-B.aLo)).trans (by linarith)
  have haLo₁ : B.aLo ≤ 1 := hA.1.trans (haU.trans haU₁)
  have hcLo₁ : B.cLo ≤ 1 := hC.1.trans (hcU.trans hcU₁)
  let flo := (2-B.aUpper+B.cLo)/4
  let fhi := (2-B.aLo+B.cUpper)/4
  let f := (2-A+C)/4
  have hflo : flo ≤ f := by dsimp [flo,f]; linarith only [haU,hC.1]
  have hfhi : f ≤ fhi := by dsimp [f,fhi]; linarith only [hA.1,hcU]
  have hflo₀ : 0 ≤ flo := by dsimp [flo]; linarith
  have hsD : 0 < max (shapeDenominator height flo) (shapeDenominator height fhi) := by
    have hmax : 0 < max flo (1-flo) := by
      have h₀ := le_max_left flo (1-flo)
      have h₁ := le_max_right flo (1-flo)
      linarith
    have hp : 0 < shapeDenominator height flo := by
      unfold shapeDenominator
      linarith only [hmax,mul_nonneg hflo₀ hheight]
    exact hp.trans_le (le_max_left _ _)
  have hD : shapeDenominator height f ≤
      max (shapeDenominator height flo) (shapeDenominator height fhi) := by
    have he (u : ℝ) : shapeDenominator height u =
        max (1+(height-1)*u) ((1+height)*u) := by
      by_cases hu : u ≤ 1-u
      · have hc : (1+height)*u ≤ 1+(height-1)*u := by
          linarith only [hu]
        rw [shapeDenominator, max_eq_right hu, max_eq_left hc]
        ring
      · have hu' : 1-u ≤ u := le_of_not_ge hu
        have hc : 1+(height-1)*u ≤ (1+height)*u := by
          linarith only [hu']
        rw [shapeDenominator, max_eq_left hu', max_eq_right hc]
        ring
    rw [he f]
    apply max_le
    · apply le_trans _ (le_max_left _ _)
      rw [he flo]
      apply le_trans _ (le_max_left _ _)
      have hneg : height - 1 ≤ 0 := sub_nonpos.mpr hheight₁
      linarith only [mul_le_mul_of_nonpos_left hflo hneg]
    · apply le_trans _ (le_max_right _ _)
      rw [he fhi]
      apply le_trans _ (le_max_right _ _)
      exact mul_le_mul_of_nonneg_left hfhi (by positivity)
  have hsL : B.sLower height ≤ s := by
    unfold ShapeBox.sLower
    apply max_le hS.1
    apply (div_le_iff₀ hsD).2
    change height ≤ s * shapeDenominator height f at h
    simpa only [mul_comm s] using h.trans (mul_le_mul_of_nonneg_left hD hs.le)
  have hsL₀ : 0 < B.sLower height := hs₀.trans_le (le_max_left _ _)
  have hsHi₀ : 0 ≤ B.sHi := hs.le.trans hS.2
  have hlo (i : Fin 4) : 0 ≤ B.lowerRoots i := by
    fin_cases i <;> simp only [ShapeBox.lowerRoots, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    · exact sub_nonneg.mpr hs₁
    · exact sub_nonneg.mpr (by
        have h' := mul_le_mul_of_nonneg_right (show 1-B.aLo ≤ 1 by linarith) hsHi₀
        linarith only [h',hs₁])
    · exact sub_nonneg.mpr (by
        have h' := mul_le_mul_of_nonneg_right hcU₁ hsHi₀
        linarith only [h',hs₁])
    · norm_num
  have hxl (i : Fin 4) : B.lowerRoots i ≤ shapeLevels A C s i := by
    fin_cases i <;> simp only [ShapeBox.lowerRoots, shapeLevels, levelsAt,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    · exact sub_le_sub_left hS.2 1
    · apply sub_le_sub_left
      exact mul_le_mul (sub_le_sub_left hA.1 1) hS.2 hs.le (sub_nonneg.mpr haLo₁)
    · apply sub_le_sub_left
      exact mul_le_mul hcU hS.2 hs.le (hc.trans hcU)
    · rfl
  have hxu (i : Fin 4) : shapeLevels A C s i ≤ B.upperRoots height i := by
    fin_cases i <;> simp only [ShapeBox.upperRoots, shapeLevels, levelsAt,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    · exact sub_le_sub_left hsL 1
    · apply sub_le_sub_left
      exact mul_le_mul (sub_le_sub_left haU 1) hsL hsL₀.le
        (sub_nonneg.mpr (haU.trans haU₁))
    · apply sub_le_sub_left
      exact mul_le_mul hC.1 hsL hsL₀.le hc
    · rfl
  obtain ⟨hsp,hfrac⟩ := shape_fractions (A := A) (C := C) hs
  refine ⟨hlo,hxl,hxu,?_,?_,?_,?_,?_,hsL₀,by simpa [hsp] using hsL,by simpa [hsp] using hS.2⟩
  · have he : B.lowerRoots 3 = 1 := rfl
    unfold mass
    rw [Fin.sum_univ_four,he]
    have h₀ := hlo 0
    have h₁ := hlo 1
    have h₂ := hlo 2
    positivity
  · intro i
    fin_cases i <;> simp [ShapeBox.lowerGaps,ha₀,hc₀]
  · intro i
    rw [hfrac]
    fin_cases i <;> simp only [ShapeBox.lowerGaps, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · exact hA.1
    · change max 0 (1 - B.aUpper - B.cUpper) ≤ 1 - A - C
      exact max_le (by linarith only [hac]) (by linarith only [haU, hcU])
    · exact hC.1
  · intro i
    rw [hfrac]
    fin_cases i <;> simp [ShapeBox.upperGaps]
    · exact haU
    · linarith only [hA.1,hC.1]
    · exact hcU
  · intro i
    fin_cases i <;> simp [ShapeBox.upperGaps]
    · exact haU₁
    · linarith only [ha₀,hc₀]
    · exact hcU₁

def ShapeBox.root (height : ℝ) : ShapeBox := ⟨0,1,0,1,spreadFloor height,1⟩

theorem ShapeBox.root_contains {height A C s : ℝ} (hh : 0 ≤ height)
    (hx : PhysicalShape height A C s) : (ShapeBox.root height).contains A C s := by
  have hf := PhysicalShape.spreadFloor_le hh hx
  obtain ⟨ha,hc,hac,hs,hs₁,_⟩ := hx
  exact ⟨⟨ha, show A ≤ 1 by linarith⟩, ⟨hc, show C ≤ 1 by linarith⟩, ⟨hf, hs₁⟩⟩

theorem ShapeBox.pruned {B : ShapeBox} {height A C s : ℝ}
    (hh : 0 ≤ height) (hh₁ : height ≤ 1) (hx : PhysicalShape height A C s)
    (ha : 0 ≤ B.aLo) (hc : 0 ≤ B.cLo) (hs : 0 < B.sLo) (hs₁ : B.sHi ≤ 1)
    (prune : 1 < B.aLo+B.cLo ∨ B.sHi < B.sLower height) : ¬ B.contains A C s := by
  intro hB
  rcases prune with h | h
  · linarith only [h,hB.1.1,hB.2.1.1,hx.2.2.1]
  · have E := ShapeBox.enclosure (B := B) hh hh₁ hx hB ha hc hs hs₁
    exact (not_lt_of_ge (E.spreadLower.trans E.spreadUpper)) h

def ShapeBox.bisect (B : ShapeBox) (axis : Fin 3) : ShapeBox × ShapeBox :=
  ![({ B with aHi := (B.aLo+B.aHi)/2 }, { B with aLo := (B.aLo+B.aHi)/2 }),
    ({ B with cHi := (B.cLo+B.cHi)/2 }, { B with cLo := (B.cLo+B.cHi)/2 }),
    ({ B with sHi := (B.sLo+B.sHi)/2 }, { B with sLo := (B.sLo+B.sHi)/2 })] axis

theorem ShapeBox.bisect_contains {B : ShapeBox} {A C s : ℝ} (axis : Fin 3)
    (hB : B.contains A C s) :
    (B.bisect axis).1.contains A C s ∨ (B.bisect axis).2.contains A C s := by
  obtain ⟨hA,hC,hs⟩ := hB
  fin_cases axis
  · rcases le_total A ((B.aLo+B.aHi)/2) with h | h
    · exact Or.inl ⟨⟨hA.1,h⟩,hC,hs⟩
    · exact Or.inr ⟨⟨h,hA.2⟩,hC,hs⟩
  · rcases le_total C ((B.cLo+B.cHi)/2) with h | h
    · exact Or.inl ⟨hA,⟨hC.1,h⟩,hs⟩
    · exact Or.inr ⟨hA,⟨h,hC.2⟩,hs⟩
  · rcases le_total s ((B.sLo+B.sHi)/2) with h | h
    · exact Or.inl ⟨hA,hC,⟨hs.1,h⟩⟩
    · exact Or.inr ⟨hA,hC,⟨h,hs.2⟩⟩

/-- Endpoint value checked in exact rational arithmetic on each surviving
leaf. The formulas clip infeasible shape and spread portions before evaluation. -/
def ShapeBox.bound (B : ShapeBox) (T height loss : ℝ) : ℝ :=
  let lower := B.lowerRoots
  let upper := B.upperRoots height
  let slo := B.sLower height
  let D := diagonalBox T lower B.lowerGaps
  secantFloor (tracialBoxFloor T slo B.sHi lower upper B.lowerGaps B.upperGaps)
    (D 0) (D 1) (D 2) (adjacentBox T lower B.lowerGaps 0 1) (adjacentBox T lower B.lowerGaps 1 2)
    (chargeBox slo B.sHi upper B.upperGaps) (skewBox B.sHi B.lowerGaps B.upperGaps)
    (heatBox T loss B.sHi lower upper) T

/-- The remaining finite certificate consists of closed boxes, each with a
strict endpoint test. Membership and coverage are restricted to physical shapes. -/
def CheckedHotBoxes (boxes : List ShapeBox) (margin T height loss : ℝ) : Prop :=
  (∀ A C s : ℝ, PhysicalShape height A C s → ∃ B ∈ boxes, B.contains A C s) ∧
  ∀ B ∈ boxes, 0 ≤ B.aLo ∧ 0 ≤ B.cLo ∧ 0 < B.sLo ∧ B.sHi ≤ 1 ∧ margin < B.bound T height loss

theorem hotCover_of_checkedBoxes {boxes : List ShapeBox} {margin T height loss : ℝ}
    (hheight : 0 ≤ height) (hheight₁ : height ≤ 1)
    (hk : 0 ≤ uniformCoefficient T loss)
    (cover : CheckedHotBoxes boxes margin T height loss) :
    HotCover margin T height loss := by
  intro A C s hx
  obtain ⟨B,hmem,hinside⟩ := cover.1 A C s hx
  obtain ⟨ha,hc,hs,hs₁,hbound⟩ := cover.2 B hmem
  have h := ShapeBox.enclosure (B := B) hheight hheight₁ hx hinside ha hc hs hs₁
  obtain ⟨_,hmn,hnq,hq⟩ := hx.ordered
  have hcell := cellBounds_of_enclosure (sorted_levels hmn hnq hq) hk h
  have hK : 0 ≤ cellCoefficient 0 T loss B.lowerRoots (B.upperRoots height) :=
    hk.trans (le_max_left _ _)
  have hheat : 0 ≤ heatBox T loss B.sHi B.lowerRoots (B.upperRoots height) := by
    unfold heatBox
    exact div_nonneg (mul_nonneg hK h.massLowerPos.le) (sq_nonneg _)
  have hskew : 0 ≤ skewBox B.sHi B.lowerGaps B.upperGaps := by
    have hshi := h.spreadLowerPos.le.trans (h.spreadLower.trans h.spreadUpper)
    unfold skewBox
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i _
    have hcap : 0 ≤ spectralCutCap i := by fin_cases i <;> norm_num [spectralCutCap]
    have hzlo := h.gapNonneg i
    have hzhi := (hzlo.trans (h.gapLower i)).trans (h.gapUpper i)
    have hsq := pow_le_pow_left₀ hzlo
      ((h.gapLower i).trans ((h.gapUpper i).trans (h.gapAtMostOne i))) 2
    rw [one_pow] at hsq
    exact mul_nonneg (mul_nonneg hcap hzhi) (sub_nonneg.mpr hsq)
  exact ⟨_,_,_,_,_,_,_,_,_,hcell,hheat,hskew,hbound⟩

/-- Maximum error against the ordered Gibbs roots, including the fixed
unit top root. -/
def gibbsDistance (r m n q : ℝ) : ℝ :=
  max |m-(r^2)⁻¹| (max |n-r⁻¹| |q-r⁻¹|)

private theorem gibbsDistance_bounds {r m n q : ℝ} (hr : 1 ≤ r)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1) :
    0 ≤ gibbsDistance r m n q ∧ gibbsDistance r m n q ≤ 1 := by
  have hr₂ : 1 ≤ r^2 := by simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hr 2
  have hg₁ : r⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_one (by linarith)).2 hr
  have hg₂ : (r^2)⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_one (by linarith)).2 hr₂
  have hr₀ : 0 ≤ r := by linarith
  have hdiff {a b : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) (hb : 0 ≤ b) (hb₁ : b ≤ 1) :
      |a-b| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  unfold gibbsDistance
  exact ⟨(abs_nonneg _).trans (le_max_left _ _),
    max_le (hdiff hm (hmn.trans (hnq.trans hq)) (by positivity) hg₂)
      (max_le (hdiff (hm.trans hmn) (hnq.trans hq) (by positivity) hg₁)
        (hdiff (hm.trans (hmn.trans hnq)) hq (by positivity) hg₁))⟩

private theorem spectralMargin_of_spreadMargin {T margin s r t m n q δ : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (hr : 1 ≤ r)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1)
    (hs : 1/4 ≤ s) (hmargin : 0 ≤ margin)
    (hconst : (1+T^2)/100000 ≤ margin/16) (hδ : margin*s^2 < δ) :
    (gibbsDistance r m n q ^ 4 + t^2 * gibbsDistance r m n q ^ 2)/100000 < δ := by
  obtain ⟨hd₀,hd₁⟩ := gibbsDistance_bounds hr hm hmn hnq hq
  have h₂ := pow_le_pow_left₀ hd₀ hd₁ 2
  have h₄ := pow_le_pow_left₀ hd₀ hd₁ 4
  have hh := mul_le_mul (pow_le_pow_left₀ ht.1 ht.2 2) h₂
    (pow_nonneg hd₀ 2) (sq_nonneg T)
  have hsp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/4) hs 2) hmargin
  refine lt_of_le_of_lt ?_ hδ
  linarith only [h₄,hh,hconst,hsp]

theorem first_outer_of_checkedBoxes {boxes : List ShapeBox} {t A C s : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) firstLimit) (hx : PhysicalShape firstHeight A C s)
    (cover : CheckedHotBoxes boxes (1/2000) firstLimit firstHeight (1/2)) (U : unitary Mat) :
    s^2/2000 < normalizedDeficit (1+t) U (1-s) (1-(1-A)*s) (1-C*s) :=
  first_outer ht hx (hotCover_of_checkedBoxes (by norm_num [firstHeight])
    (by norm_num [firstHeight]) (by norm_num [uniformCoefficient,firstLimit]) cover) U

theorem extended_outer_of_checkedBoxes {boxes : List ShapeBox} {t A C s : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) extendedLimit) (hx : PhysicalShape extendedHeight A C s)
    (cover : CheckedHotBoxes boxes (1/4000) extendedLimit extendedHeight (3/7)) (U : unitary Mat) :
    s^2/4000 < normalizedDeficit (1+t) U (1-s) (1-(1-A)*s) (1-C*s) :=
  extended_outer ht hx (hotCover_of_checkedBoxes (by norm_num [extendedHeight])
    (by norm_num [extendedHeight]) (by norm_num [uniformCoefficient,extendedLimit]) cover) U

theorem extended_outer_spectral_margin {boxes : List ShapeBox} {t A C s : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) extendedLimit) (hx : PhysicalShape extendedHeight A C s)
    (cover : CheckedHotBoxes boxes (1/4000) extendedLimit extendedHeight (3/7)) (U : unitary Mat) :
    let d := gibbsDistance (1+t) (1-s) (1-(1-A)*s) (1-C*s)
    (d^4+t^2*d^2)/100000 < normalizedDeficit (1+t) U (1-s) (1-(1-A)*s) (1-C*s) := by
  intro d
  obtain ⟨hm,hmn,hnq,hq⟩ := hx.ordered
  have hfloor := PhysicalShape.spreadFloor_le (by norm_num [extendedHeight]) hx
  have hs : 1/4 ≤ s :=
    (show (1 : ℝ)/4 ≤ spreadFloor extendedHeight by norm_num [spreadFloor, extendedHeight]).trans hfloor
  refine spectralMargin_of_spreadMargin ht (by linarith only [ht.1]) hm hmn hnq hq hs
    (show (0 : ℝ) ≤ 1/4000 by norm_num) (by norm_num [extendedLimit]) ?_
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using extended_outer_of_checkedBoxes ht hx cover U

/-- A finite bisection certificate has only endpoint comparisons. Its
coverage of the continuous physical region follows from the bisections. -/
inductive HotBoxTest (margin T height loss : ℝ) : ShapeBox → Prop where
  | leaf {B : ShapeBox}
      (ha : 0 ≤ B.aLo) (hc : 0 ≤ B.cLo) (hs : 0 < B.sLo) (htop : B.sHi ≤ 1)
      (test : margin < B.bound T height loss) : HotBoxTest margin T height loss B
  | prune {B : ShapeBox}
      (ha : 0 ≤ B.aLo) (hc : 0 ≤ B.cLo) (hs : 0 < B.sLo) (htop : B.sHi ≤ 1)
      (test : 1 < B.aLo+B.cLo ∨ B.sHi < B.sLower height) :
      HotBoxTest margin T height loss B
  | split {B : ShapeBox} (axis : Fin 3)
      (left : HotBoxTest margin T height loss (B.bisect axis).1)
      (right : HotBoxTest margin T height loss (B.bisect axis).2) :
      HotBoxTest margin T height loss B

private theorem HotBoxTest.leaves {margin T height loss : ℝ} {B : ShapeBox}
    (hh : 0 ≤ height) (hh₁ : height ≤ 1) (test : HotBoxTest margin T height loss B) :
    ∃ boxes : List ShapeBox,
      (∀ A C s, PhysicalShape height A C s → B.contains A C s →
        ∃ K ∈ boxes, K.contains A C s) ∧
      ∀ K ∈ boxes, 0 ≤ K.aLo ∧ 0 ≤ K.cLo ∧ 0 < K.sLo ∧ K.sHi ≤ 1 ∧
        margin < K.bound T height loss := by
  induction test with
  | @leaf B ha hc hs htop check =>
    refine ⟨[B], fun A C s hx hB => ⟨B, by simp, hB⟩, ?_⟩
    intro K hK
    have he : K = B := by simpa using hK
    subst K
    exact ⟨ha, hc, hs, htop, check⟩
  | prune ha hc hs htop check =>
    refine ⟨[], ?_, by simp⟩
    intro A C s hx hB
    exact (ShapeBox.pruned hh hh₁ hx ha hc hs htop check hB).elim
  | split axis left right ihl ihr =>
    obtain ⟨ls, hls, hlt⟩ := ihl
    obtain ⟨rs, hrs, hrt⟩ := ihr
    refine ⟨ls ++ rs, ?_, ?_⟩
    · intro A C s hx hB
      rcases ShapeBox.bisect_contains axis hB with h | h
      · obtain ⟨K, hK, hi⟩ := hls A C s hx h
        exact ⟨K, List.mem_append.mpr (Or.inl hK), hi⟩
      · obtain ⟨K, hK, hi⟩ := hrs A C s hx h
        exact ⟨K, List.mem_append.mpr (Or.inr hK), hi⟩
    · intro K hK
      rcases List.mem_append.mp hK with h | h
      · exact hlt K h
      · exact hrt K h

theorem HotBoxTest.hotCover {margin T height loss : ℝ}
    (hh : 0 ≤ height) (hh₁ : height ≤ 1) (hk : 0 ≤ uniformCoefficient T loss)
    (test : HotBoxTest margin T height loss (ShapeBox.root height)) :
    HotCover margin T height loss := by
  obtain ⟨boxes, hcover, hleaf⟩ := test.leaves hh hh₁
  exact hotCover_of_checkedBoxes hh hh₁ hk
    (boxes := boxes)
    ⟨fun A C s hx => hcover A C s hx (ShapeBox.root_contains hh hx), hleaf⟩

/-- The outer region written in the original ordered roots. The last
inequality is the mean-normalized spectral spread threshold, cleared of its
positive denominator. -/
def InOuterRegion (height m n q : ℝ) : Prop :=
  let mean := (m+n+q+1)/4
  height*mean ≤ max (1-mean) (mean-m)

private theorem physical_shape_of_roots {height m n q : ℝ} (hh : 0 < height)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1)
    (houter : InOuterRegion height m n q) :
    let s := 1-m
    let A := (n-m)/s
    let C := (1-q)/s
    PhysicalShape height A C s ∧ 1-(1-A)*s = n ∧ 1-C*s = q := by
  dsimp only
  let s := 1-m
  let A := (n-m)/s
  let C := (1-q)/s
  change PhysicalShape height A C s ∧ 1-(1-A)*s = n ∧ 1-C*s = q
  have hs : 0 < s := by
    by_contra! h
    have hm1 : m = 1 := by dsimp [s] at h; linarith
    have hn1 : n = 1 := by linarith
    have hq1 : q = 1 := by linarith
    norm_num [InOuterRegion, hm1, hn1, hq1] at houter
    exact (not_le_of_gt hh) houter
  have hAs : A*s = n-m := div_mul_cancel₀ _ hs.ne'
  have hCs : C*s = 1-q := div_mul_cancel₀ _ hs.ne'
  have hA : 0 ≤ A := div_nonneg (sub_nonneg.mpr hmn) hs.le
  have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr hq) hs.le
  have hsum : A+C ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right _ hs
    rw [add_mul, hAs, hCs, one_mul]
    dsimp [s]
    linarith
  refine ⟨⟨hA, hC, hsum, hs, sub_le_self 1 hm, ?_⟩, ?_, ?_⟩
  · let f := (2-A+C)/4
    let mean := (m+n+q+1)/4
    change height ≤ s*(max f (1-f) + f*height)
    change height*mean ≤ max (1-mean) (mean-m) at houter
    have hf : s*f = 1-mean := by
      dsimp only [f, mean, s] at hAs hCs ⊢
      linear_combination -hAs/4 + hCs/4
    have hrev : s*(1-f) = mean-m := by
      dsimp [s] at hf ⊢
      linear_combination -hf
    have hmax : s*max f (1-f) = max (1-mean) (mean-m) := by
      rw [mul_max_of_nonneg _ _ hs.le, hf, hrev]
    rw [mul_add, ← mul_assoc s f height, hf, hmax]
    linarith only [houter]
  · dsimp [s] at hAs ⊢
    linear_combination hAs
  · linear_combination -hCs

theorem normalizedDeficit_gt_of_outerRegion {margin T height loss r m n q : ℝ}
    (hT : 0 < T) (hh : 0 < height) (hloss : thermalEntropyPenalty 0 T ≤ loss)
    (hr : 1 ≤ r) (hrT : r ≤ 1+T) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1)
    (houter : InOuterRegion height m n q)
    (cover : HotCover margin T height loss) (U : unitary Mat) :
    margin*(1-m)^2 < normalizedDeficit r U m n q := by
  obtain ⟨hshape, hn, hq'⟩ := physical_shape_of_roots hh hm hmn hnq hq houter
  have h := normalizedDeficit_gt_of_hotCover hT hloss
    (t := r-1) ⟨by linarith, by linarith⟩ hshape cover U
  rw [hn, hq', show 1+(r-1) = r by ring, show 1-(1-m) = m by ring] at h
  exact h

/-- The first hot band for every unitary frame in the normalized outer
region, conditional only on the finite rational bisection certificate. -/
theorem first_outer_normalizedDeficit {r m n q : ℝ}
    (test : HotBoxTest (1/2000) firstLimit firstHeight (1/2) (ShapeBox.root firstHeight))
    (hr : 1 ≤ r) (hrT : r ≤ 1+firstLimit)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1)
    (houter : InOuterRegion firstHeight m n q) (U : unitary Mat) :
    (1-m)^2/2000 < normalizedDeficit r U m n q := by
  have h := normalizedDeficit_gt_of_outerRegion (by norm_num [firstLimit])
    (by norm_num [firstHeight]) first_loss hr hrT hm hmn hnq hq houter
    (test.hotCover (by norm_num [firstHeight]) (by norm_num [firstHeight])
      (by norm_num [uniformCoefficient, firstLimit])) U
  linarith only [h]

/-- The extended hot band includes zero and repeated roots and every
unitary frame in the normalized outer region. -/
theorem extended_outer_normalizedDeficit {r m n q : ℝ}
    (test : HotBoxTest (1/4000) extendedLimit extendedHeight (3/7) (ShapeBox.root extendedHeight))
    (hr : 1 ≤ r) (hrT : r ≤ 1+extendedLimit)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1)
    (houter : InOuterRegion extendedHeight m n q) (U : unitary Mat) :
    (1-m)^2/4000 < normalizedDeficit r U m n q := by
  have h := normalizedDeficit_gt_of_outerRegion (by norm_num [extendedLimit])
    (by norm_num [extendedHeight]) extended_loss hr hrT hm hmn hnq hq houter
    (test.hotCover (by norm_num [extendedHeight]) (by norm_num [extendedHeight])
      (by norm_num [uniformCoefficient, extendedLimit])) U
  linarith only [h]

/--
info: 'D5.S3.Quantum.Semigroups.WuCubicHotOuter.first_outer_normalizedDeficit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms first_outer_normalizedDeficit

/--
info: 'D5.S3.Quantum.Semigroups.WuCubicHotOuter.extended_outer_normalizedDeficit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms extended_outer_normalizedDeficit


/-
Exact rational check. Start with [0,1] × [0,1] × [spreadFloor height,1].
Discard a box if aLo+cLo > 1 or sLower height > sHi. Test margin < bound on
the surviving box. If the test fails, bisect its longest side, with ties in
coordinate order A, C, s. Closed children cover the parent.

With fixed spectral endpoints, the three nonpositive charge minima use
penalties linear in t. Their lower secant joins t=0 to t=T. The scalar test
uses the exact closed-interval minimum of H*T^2*y^2 - penalty*y, with
y=t/T. The endpoints, variance, and minimization are rational.

For (firstLimit, firstHeight, 1/2, 1/2000), the exact walk accepted 656
boxes and pruned 39, at maximum accepted depth 16. The minimum bound was
strictly greater than 539252117/10^12.

For (extendedLimit, extendedHeight, 3/7, 1/4000), the exact walk accepted
872 boxes and pruned 53, at maximum accepted depth 17. The minimum bound
was strictly greater than 261530604/10^12.

The height parameters are the exact rational h_Y values in sections 5
and 2 of the middle-neck and residual-spectral-shape proofs respectively.
Those sections give the operator spread comparison leading to PhysicalShape.
-/

end
end D5.S3.Quantum.Semigroups.WuCubicHotOuter
