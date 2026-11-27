/- GID: D5/S3/Quantum/Semigroups/WuCubicOccupationEnvelope
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicOccupationEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar occupation envelope for the ordinary two-mode Wu cubic deficit. -/

import OmegaBuild.Commands
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-!
At cubic exponent three, the exact edge expansion consists of a symmetric
cost, a polarization term, and a nonnegative reverse-edge term. At the
specified spectrum, the canonical anticommutation relations constrain the
edge weights and force a quadratic occupation penalty. The resulting
scalar envelope bounds the ordinary Wu deficit uniformly.
-/

set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope

/-- Sum over the six ascending edges. -/
def edgeSum (F : Fin 4 → Fin 4 → ℝ) : ℝ :=
  F 0 1 + F 0 2 + F 0 3 + F 1 2 + F 1 3 + F 2 3

def sym (w : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) : ℝ := w i j + w j i

def orientationMoment (lam : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  edgeSum (fun i j => (w i j - w j i) * (lam j - lam i))

/-- Here `e i` is the total even occupation probability, and
`m = Tr ρ (N - I)`. The last bound is the triangle inequality for the
difference of the doubly occupied and empty probabilities with unit sums. -/
structure CARConstraints (lam : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ)
    (e : Fin 4 → ℝ) (m : ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ w i j
  combined_marginal : ∀ i, (∑ j, sym w i j) = 2
  pair_le_one : ∀ i j, i < j → sym w i j ≤ 1
  diagonal : ∀ i, w i i = e i * (1 - e i)
  occupation_mem : ∀ i, e i ∈ Set.Icc (0 : ℝ) 1
  occupation_sum : (∑ i, e i) = 2
  moment : orientationMoment lam w = 2 * m
  occupation_bound : ∀ v : ℝ, |m| ≤ ∑ i, e i * |lam i - v|

def spectrumOf (x : Fin 4 → ℝ) (mass : ℝ) (i : Fin 4) : ℝ := (x i) ^ 3 / mass

private def cubicGap (x : Fin 4 → ℝ) (mass : ℝ) (i j : Fin 4) : ℝ := (x j - x i) ^ 3 / mass

/-- The coefficients `C, S, c, s` stand for the cosh and sinh at `h` and `h/3`.
The cube roots of the eigenvalues are the entries of `x` divided by the cube
root of `mass`. -/
def scaledCubicEnergy (C S c s : ℝ) (x : Fin 4 → ℝ) (mass : ℝ)
    (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j *
    ((C + S) / 2 * spectrumOf x mass i + (C - S) / 2 * spectrumOf x mass j -
      (c + s) / 2 * ((x i) ^ 2 * x j / mass) -
      (c - s) / 2 * (x i * (x j) ^ 2 / mass))

private def cubicCost (c s : ℝ) (x : Fin 4 → ℝ) (mass : ℝ) (i j : Fin 4) : ℝ :=
  (c / 2 * (x j - x i) ^ 2 * (x i + x j) - s / 6 * (x j - x i) ^ 3) / mass

/-- The exact cubic reduction, including the reverse-edge term. -/
private theorem scaledCubicEnergy_eq (C S c s : ℝ) (x : Fin 4 → ℝ) (mass m : ℝ)
    (w : Fin 4 → Fin 4 → ℝ) (hlam : (∑ i, spectrumOf x mass i) = 1)
    (hrows : ∀ i, (∑ j, sym w i j) = 2)
    (hm : orientationMoment (spectrumOf x mass) w = 2 * m) :
    scaledCubicEnergy C S c s x mass w =
      C - c - m * (S - s / 3) +
        edgeSum (fun i j => sym w i j * cubicCost c s x mass i j) +
        s / 3 * edgeSum (fun i j => w j i * cubicGap x mass i j) := by
  have h0 := hrows 0
  have h1 := hrows 1
  have h2 := hrows 2
  have h3 := hrows 3
  simp only [scaledCubicEnergy, Fin.sum_univ_four, sym, spectrumOf, cubicCost, cubicGap,
    orientationMoment, edgeSum] at hlam hm h0 h1 h2 h3 ⊢
  linear_combination (C - c) * hlam + (s / 6 - S / 2) * hm +
    ((C - c) / 2 * (x 0 ^ 3 / mass)) * h0 + ((C - c) / 2 * (x 1 ^ 3 / mass)) * h1 +
    ((C - c) / 2 * (x 2 ^ 3 / mass)) * h2 + ((C - c) / 2 * (x 3 ^ 3 / mass)) * h3

private def occupationWeights (P : Fin 4 → Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![2 * P 0 2 - P 1 2, P 1 2, P 1 2, 2 * P 1 3 - P 1 2]

private def referenceCost (P : Fin 4 → Fin 4 → ℝ) : ℝ :=
  P 0 1 + P 2 3 + (P 0 2 + P 1 3) / 2

private def diagonalPenalty (k e : Fin 4 → ℝ) : ℝ :=
  ∑ i, k i * (e i - 1 / 2) ^ 2

/-- Exact symmetric defect. Each of the three edge corrections is retained. -/
private theorem symmetric_defect_eq (P w : Fin 4 → Fin 4 → ℝ) (e : Fin 4 → ℝ)
    (hrows : ∀ i, (∑ j, sym w i j) = 2)
    (hdiag : ∀ i, w i i = e i * (1 - e i)) :
    edgeSum (fun i j => sym w i j * P i j) =
      referenceCost P + diagonalPenalty (occupationWeights P) e +
        (P 0 2 - P 0 1) * (1 - sym w 0 1) +
        (P 1 3 - P 2 3) * (1 - sym w 2 3) +
        (P 0 3 - P 0 2 - P 1 3 + P 1 2) * sym w 0 3 := by
  have h0 := hrows 0
  have h1 := hrows 1
  have h2 := hrows 2
  have h3 := hrows 3
  simp only [edgeSum, referenceCost, diagonalPenalty, Fin.sum_univ_four, sym,
    occupationWeights, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 h3 ⊢
  simp only [hdiag] at h0 h1 h2 h3
  linear_combination ((2 * P 0 2 - P 1 2) / 2) * h0 + (P 1 2 / 2) * h1 +
    (P 1 2 / 2) * h2 + ((2 * P 1 3 - P 1 2) / 2) * h3

private def distance (lam : Fin 4 → ℝ) (v : ℝ) (i : Fin 4) : ℝ := |lam i - v|

private def occupationThreshold (lam : Fin 4 → ℝ) (v : ℝ) : ℝ := (∑ i, distance lam v i) / 2

private def occupationVariance (k a : Fin 4 → ℝ) (center : ℝ) : ℝ :=
  ∑ i, (a i - center) ^ 2 / k i

/-- Weighted Cauchy–Schwarz for every occupation and every choice of center.
A zero weight contributes zero when its centered distance vanishes. The
product form also covers zero total variance. -/
private theorem occupation_cauchy_schwarz (lam k e : Fin 4 → ℝ) (v center m : ℝ)
    (he : (∑ i, e i) = 2) (hm : |m| ≤ ∑ i, e i * distance lam v i)
    (hk : ∀ i, 0 ≤ k i) (hz : ∀ i, k i = 0 → distance lam v i = center) :
    (max 0 (|m| - occupationThreshold lam v)) ^ 2 ≤
      diagonalPenalty k e * occupationVariance k (distance lam v) center := by
  let L := ∑ i, (e i - 1 / 2) * (distance lam v i - center)
  have hL : L + occupationThreshold lam v = ∑ i, e i * distance lam v i := by
    simp only [L, occupationThreshold, Fin.sum_univ_four] at he ⊢
    linear_combination -center * he
  have hdiag : ∀ i : Fin 4, 0 ≤ k i * (e i - 1 / 2) ^ 2 :=
    fun i => mul_nonneg (hk i) (sq_nonneg _)
  have hvar : ∀ i : Fin 4, 0 ≤ (distance lam v i - center) ^ 2 / k i :=
    fun i => div_nonneg (sq_nonneg _) (hk i)
  have hCS : L ^ 2 ≤ diagonalPenalty k e * occupationVariance k (distance lam v) center := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => hdiag i) (fun i _ => hvar i)
    intro i _
    by_cases hi : k i = 0
    · simp [hi, hz i hi]
    · exact le_of_eq (by field_simp [hi])
  by_cases hsmall : |m| ≤ occupationThreshold lam v
  · rw [max_eq_left (sub_nonpos.mpr hsmall), zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact (sq_nonneg L).trans hCS
  · have hpos : 0 < |m| - occupationThreshold lam v := sub_pos.mpr (lt_of_not_ge hsmall)
    have hle : |m| - occupationThreshold lam v ≤ L := by linarith only [hm, hL]
    rw [max_eq_right hpos.le]
    exact (pow_le_pow_left₀ hpos.le hle 2).trans hCS

/-- Completing the square bounds the occupation contribution for every real
polarization. The minimum of the scalar expression is attained at
`m = M + D * b / 2` when `M ≥ 0`. -/
private theorem occupation_penalty_lower {M D b m penalty : ℝ} (hD : 0 < D) (hb : 0 ≤ b)
    (hpenalty : (max 0 (|m| - M)) ^ 2 ≤ penalty * D) :
    -b * M - D * b ^ 2 / 4 ≤ -b * m + penalty := by
  let δ := max 0 (|m| - M)
  have hm : m - M ≤ δ := (sub_le_sub_right (le_abs_self m) M).trans (le_max_right _ _)
  have hlin := mul_le_mul_of_nonneg_left hm hb
  have hdiv : δ ^ 2 / D ≤ penalty := (div_le_iff₀ hD).2 hpenalty
  have hsq : 0 ≤ (δ - D * b / 2) ^ 2 / D := div_nonneg (sq_nonneg _) hD.le
  have hexpand : (δ - D * b / 2) ^ 2 / D = δ ^ 2 / D - b * δ + D * b ^ 2 / 4 := by
    field_simp [hD.ne']
    ring
  rw [hexpand] at hsq
  linarith only [hlin, hdiv, hsq]

/-- The unnormalized cube roots are `64,81,82,101`. -/
def roots : Fin 4 → ℝ := ![64, 81, 82, 101]

def spectrum : Fin 4 → ℝ := spectrumOf roots 2375254

def temperature : ℝ := 3 * Real.log (9 / 8)

def entropyConstant : ℝ :=
  (∑ i, spectrum i * Real.log (4 * spectrum i)) + 2 * Real.log (Real.cosh temperature)

/-- The ordinary-trace entropy against the two-mode Gibbs density. -/
def relativeEntropy (m : ℝ) : ℝ := entropyConstant - 2 * temperature * m

private def thermalFactor : ℝ :=
  (Real.cosh temperature - Real.cosh (temperature / 3)) *
    Real.cosh temperature / Real.sinh temperature

private def normalizedCoefficient : ℝ := thermalFactor / (2 * temperature)

/-- Wu v1 (3.55) at the cubic exponent and log odds `2 * temperature`. -/
def sharpCoefficient : ℝ := 9 / (4 * Real.cosh temperature) * normalizedCoefficient

/-- The ordinary cubic Dirichlet energy, in its directed spectral form. -/
def cubicEnergy (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  9 / (4 * Real.cosh temperature) *
    scaledCubicEnergy (Real.cosh temperature) (Real.sinh temperature)
      (Real.cosh (temperature / 3)) (Real.sinh (temperature / 3)) roots 2375254 w

private theorem exp_temperature : Real.exp temperature = 729 / 512 := by
  unfold temperature
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  norm_num

private theorem exp_third : Real.exp (temperature / 3) = 9 / 8 := by
  rw [show temperature / 3 = Real.log (9 / 8) by unfold temperature; ring]
  exact Real.exp_log (by norm_num)

private theorem cosh_temperature : Real.cosh temperature = 793585 / 746496 := by
  rw [Real.cosh_eq, Real.exp_neg, exp_temperature]
  norm_num

private theorem sinh_temperature : Real.sinh temperature = 269297 / 746496 := by
  rw [Real.sinh_eq, Real.exp_neg, exp_temperature]
  norm_num

private theorem cosh_third : Real.cosh (temperature / 3) = 145 / 144 := by
  rw [Real.cosh_eq, Real.exp_neg, exp_third]
  norm_num

private theorem sinh_third : Real.sinh (temperature / 3) = 17 / 144 := by
  rw [Real.sinh_eq, Real.exp_neg, exp_third]
  norm_num

private theorem thermalFactor_eq : thermalFactor = 1956187025 / 11825243136 := by
  norm_num [thermalFactor, cosh_temperature, sinh_temperature, cosh_third]

private theorem slope_eq :
    Real.sinh temperature - Real.sinh (temperature / 3) / 3 - thermalFactor =
      533681 / 3421656 := by
  norm_num [thermalFactor_eq, sinh_temperature, sinh_third]

private def pointCost : Fin 4 → Fin 4 → ℝ :=
  cubicCost (145 / 144) (17 / 144) roots 2375254

private def midpoint : ℝ := (spectrum 1 + spectrum 2) / 2

private def pointCenter : ℝ :=
  (∑ i, distance spectrum midpoint i / occupationWeights pointCost i) /
    (∑ i, 1 / occupationWeights pointCost i)

private def pointVariance : ℝ :=
  occupationVariance (occupationWeights pointCost) (distance spectrum midpoint) pointCenter

private def slope : ℝ := 533681 / 3421656

private theorem pointWeights_pos (i : Fin 4) : 0 < occupationWeights pointCost i := by
  fin_cases i <;> norm_num [occupationWeights, pointCost, cubicCost, roots]

private theorem pointVariance_pos : 0 < pointVariance := by
  norm_num [pointVariance, pointCenter, occupationVariance, occupationWeights, pointCost,
    cubicCost, roots, distance, midpoint, spectrum, spectrumOf, Fin.sum_univ_four, abs_of_neg,
    abs_of_nonneg]

private theorem point_bound {w : Fin 4 → Fin 4 → ℝ} {e : Fin 4 → ℝ} {m : ℝ}
    (hw : CARConstraints spectrum w e m) :
    (Real.cosh temperature - Real.cosh (temperature / 3)) + referenceCost pointCost -
        slope * occupationThreshold spectrum midpoint - pointVariance * slope ^ 2 / 4 ≤
      scaledCubicEnergy (Real.cosh temperature) (Real.sinh temperature)
        (Real.cosh (temperature / 3)) (Real.sinh (temperature / 3)) roots 2375254 w +
        thermalFactor * m := by
  have hmass : (∑ i, spectrumOf roots 2375254 i) = 1 := by
    norm_num [spectrumOf, roots, Fin.sum_univ_four]
  have henergy := scaledCubicEnergy_eq (Real.cosh temperature) (Real.sinh temperature)
    (Real.cosh (temperature / 3)) (Real.sinh (temperature / 3)) roots 2375254 m w hmass
      hw.combined_marginal hw.moment
  have hdefect := symmetric_defect_eq pointCost w e hw.combined_marginal hw.diagonal
  have hcs := occupation_cauchy_schwarz spectrum (occupationWeights pointCost) e midpoint
    pointCenter m hw.occupation_sum (hw.occupation_bound midpoint)
    (fun i => (pointWeights_pos i).le)
    (fun i hi => ((pointWeights_pos i).ne' hi).elim)
  have hpenalty := occupation_penalty_lower pointVariance_pos (show 0 ≤ slope by norm_num [slope])
    (show (max 0 (|m| - occupationThreshold spectrum midpoint)) ^ 2 ≤
      diagonalPenalty (occupationWeights pointCost) e * pointVariance from hcs)
  have hc01 : 0 ≤ pointCost 0 2 - pointCost 0 1 := by
    norm_num [pointCost, cubicCost, roots]
  have hc23 : 0 ≤ pointCost 1 3 - pointCost 2 3 := by
    norm_num [pointCost, cubicCost, roots]
  have hc03 : 0 ≤ pointCost 0 3 - pointCost 0 2 - pointCost 1 3 + pointCost 1 2 := by
    norm_num [pointCost, cubicCost, roots]
  have h01 := mul_nonneg hc01 (sub_nonneg.mpr (hw.pair_le_one 0 1 (by decide)))
  have h23 := mul_nonneg hc23 (sub_nonneg.mpr (hw.pair_le_one 2 3 (by decide)))
  have h03 : 0 ≤ (pointCost 0 3 - pointCost 0 2 - pointCost 1 3 + pointCost 1 2) * sym w 0 3 :=
    mul_nonneg hc03 (add_nonneg (hw.nonneg 0 3) (hw.nonneg 3 0))
  have hreverse : 0 ≤ (17 / 144 : ℝ) / 3 *
      edgeSum (fun i j => w j i * cubicGap roots 2375254 i j) := by
    refine mul_nonneg (by norm_num) ?_
    unfold edgeSum
    repeat' apply add_nonneg
    all_goals exact mul_nonneg (hw.nonneg _ _) (by norm_num [cubicGap, roots])
  rw [henergy]
  have hslope : Real.sinh temperature - Real.sinh (temperature / 3) / 3 =
      slope + thermalFactor := by
    unfold slope
    linarith only [slope_eq]
  rw [hslope, cosh_third, sinh_third]
  change _ ≤ Real.cosh temperature - 145 / 144 - m * (slope + thermalFactor) +
    edgeSum (fun i j => sym w i j * pointCost i j) +
    (17 / 144) / 3 * edgeSum (fun i j => w j i * cubicGap roots 2375254 i j) +
    thermalFactor * m
  rw [hdefect]
  nlinarith only [hpenalty, h01, h23, h03, hreverse]

-- The eight-term Mathlib remainder bound suffices for the rational comparisons below.
private theorem log_enclosure (z x : ℝ) (hz : |z| < 1) (hx : (1 + z) / (1 - z) = x) :
    |1 / 2 * Real.log x - ∑ j ∈ Finset.range 8, z ^ (2 * j + 1) / (2 * j + 1)| ≤
      |z| ^ 17 / (1 - z ^ 2) := by
  simpa only [hx] using Real.sum_range_sub_log_div_le hz 8

private theorem log_base_lower : (117783 / 1000000 : ℝ) ≤ Real.log (9 / 8) := by
  have h := (abs_le.mp (log_enclosure (1 / 17) (9 / 8) (by norm_num) (by norm_num))).1
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

private theorem entropyConstant_le : entropyConstant ≤ 114539 / 500000 := by
  have h0 := (abs_le.mp
    (log_enclosure (-663339 / 1711915) (524288 / 1187627) (by norm_num) (by norm_num))).2
  have h1 := (abs_le.mp
    (log_enclosure (-124745 / 2250509) (1062882 / 1187627) (by norm_num) (by norm_num))).2
  have h2 := (abs_le.mp
    (log_enclosure (-84891 / 2290363) (1102736 / 1187627) (by norm_num) (by norm_num))).2
  have h3 := (abs_le.mp
    (log_enclosure (872975 / 3248229) (2060602 / 1187627) (by norm_num) (by norm_num))).2
  have hc := (abs_le.mp
    (log_enclosure (47089 / 1540081) (793585 / 746496) (by norm_num) (by norm_num))).2
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 hc
  norm_num [entropyConstant, Fin.sum_univ_four, spectrum, spectrumOf, roots, cosh_temperature]
  linarith only [h0, h1, h2, h3, hc]

private theorem normalizedCoefficient_nonneg : 0 ≤ normalizedCoefficient := by
  apply div_nonneg
  · norm_num [thermalFactor_eq]
  · unfold temperature
    linarith only [log_base_lower]

private theorem normalizedCoefficient_le : normalizedCoefficient ≤ 117041 / 500000 := by
  have hden : (6 * (117783 / 1000000) : ℝ) ≤ 2 * temperature := by
    unfold temperature
    linarith only [log_base_lower]
  unfold normalizedCoefficient
  calc
    _ ≤ thermalFactor / (6 * (117783 / 1000000)) :=
      div_le_div_of_nonneg_left (by norm_num [thermalFactor_eq]) (by norm_num) hden
    _ ≤ _ := by norm_num [thermalFactor_eq]

private theorem rational_margin :
    (1 / 8000 : ℝ) <
      (Real.cosh temperature - Real.cosh (temperature / 3)) + referenceCost pointCost -
        slope * occupationThreshold spectrum midpoint - pointVariance * slope ^ 2 / 4 -
        (117041 / 500000) * (114539 / 500000) := by
  norm_num [cosh_temperature, cosh_third, referenceCost, pointCost, slope,
    occupationThreshold, pointVariance, pointCenter, occupationVariance, occupationWeights,
    cubicCost, roots, distance, midpoint, spectrum, spectrumOf, Fin.sum_univ_four]

/-- At the full-rank ordered spectrum `(262144,531441,551368,1030301)/2375254`
and half log odds `3 log(9/8)`, the normalized ordinary Wu cubic deficit
strictly exceeds `1/8000` for every set of physical CAR witnesses. -/
theorem cubic_deficit_gt {w : Fin 4 → Fin 4 → ℝ} {e : Fin 4 → ℝ} {m : ℝ}
    (hw : CARConstraints spectrum w e m) :
    (1 / 8000 : ℝ) <
      (4 * Real.cosh temperature / 9) * (cubicEnergy w - sharpCoefficient * relativeEntropy m) := by
  have hproduct : normalizedCoefficient * entropyConstant ≤
      (117041 / 500000 : ℝ) * (114539 / 500000) :=
    (mul_le_mul_of_nonneg_left entropyConstant_le normalizedCoefficient_nonneg).trans
      (mul_le_mul_of_nonneg_right normalizedCoefficient_le (by norm_num))
  have hnormalize :
      (4 * Real.cosh temperature / 9) * (cubicEnergy w - sharpCoefficient * relativeEntropy m) =
        scaledCubicEnergy (Real.cosh temperature) (Real.sinh temperature)
          (Real.cosh (temperature / 3)) (Real.sinh (temperature / 3)) roots 2375254 w +
          thermalFactor * m - normalizedCoefficient * entropyConstant := by
    have ht : 0 < temperature := by unfold temperature; linarith only [log_base_lower]
    have hc := (Real.cosh_pos temperature).ne'
    unfold cubicEnergy sharpCoefficient relativeEntropy normalizedCoefficient
    field_simp [hc, ht.ne']
    ring
  rw [hnormalize]
  linarith only [point_bound hw, rational_margin, hproduct]

end D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope
