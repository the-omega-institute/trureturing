/- GID: D5/S3/Quantum/Semigroups/WuCubicAngularCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicAngularCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Matched angular estimates for the ordinary-trace two-CAR Wu cubic deficit. -/

import D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
import D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing
import D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
import D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! Wu v1, Remark 3.15, equal caps and exponent three.
The two adjacent cut estimates use the same absolute mixture weight.
The long crossing and the endpoint charges come from the same complex frame. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicAngularCertificate

open WuCubicDirectedOccupationCap (Mat frameVector frameWeight oddProbability
  emptyProbability fullProbability)
open WuCubicCoupledCuts
open WuCubicRankTwoCut (cutImbalance cutEvenOffset forwardCutWeight reverseCutWeight)
open WuCubicOccupationEnvelope (sym)
open WuCubicSharpLongCrossing (singletonPairWeight_ge_radical singletonPairWeight_ge_product)
open private singletonCutWeight_eq adjacentCutWeight_ge_local from
  D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
open private odd_mass_mem from D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing

/-- Twice the odd occupation of a frame line. -/
def oddTilt (U : unitary Mat) (i : Fin 4) : ℝ := 2 * oddProbability (frameVector U i)

def tiltSum (U : unitary Mat) : ℝ := oddTilt U 0 + oddTilt U 3

def tiltDiff (U : unitary Mat) : ℝ := oddTilt U 0 - oddTilt U 3

def longCrossing (U : unitary Mat) : ℝ := sym (frameWeight U) 0 3

/-- The long-crossing term uses zero at zero total tilt. -/
def longFactor (S : ℝ) : ℝ := if S = 0 then 0 else max 1 (1 / S)

private theorem tiltSum_nonneg (U : unitary Mat) : 0 ≤ tiltSum U := by
  unfold tiltSum oddTilt
  linarith only [(odd_mass_mem U 0).1, (odd_mass_mem U 3).1]

/-- The product form of the complex-frame long-crossing bound. -/
theorem long_crossing_mul (U : unitary Mat) :
    tiltDiff U ^ 2 / 4 ≤ tiltSum U * longCrossing U := by
  have h := singletonPairWeight_ge_product U 0 3
  dsimp only at h
  unfold tiltDiff tiltSum oddTilt longCrossing sym
  linarith only [h]

private theorem radical_unscaled {t s : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (t - s) ^ 2 ≤ (Real.sqrt ((1 - t) * s) - Real.sqrt (t * (1 - s))) ^ 2 := by
  let a := Real.sqrt (1 - t)
  let b := Real.sqrt t
  let c := Real.sqrt (1 - s)
  let d := Real.sqrt s
  have ha : a ^ 2 = 1 - t := Real.sq_sqrt (sub_nonneg.mpr ht.2)
  have hb : b ^ 2 = t := Real.sq_sqrt ht.1
  have hc : c ^ 2 = 1 - s := Real.sq_sqrt (sub_nonneg.mpr hs.2)
  have hd : d ^ 2 = s := Real.sq_sqrt hs.1
  rw [Real.sqrt_mul (sub_nonneg.mpr ht.2), Real.sqrt_mul ht.1]
  change (t - s) ^ 2 ≤ (a * d - b * c) ^ 2
  have hsum : (a * d + b * c) ^ 2 ≤ 1 := by
    have hlagrange : (a * d + b * c) ^ 2 + (a * c - b * d) ^ 2 =
        (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring
    rw [ha, hb, hc, hd] at hlagrange
    nlinarith only [hlagrange, sq_nonneg (a * c - b * d)]
  have hdiff : t - s = (b * c) ^ 2 - (a * d) ^ 2 := by
    simp only [mul_pow, ha, hb, hc, hd]
    ring
  calc
    (t - s) ^ 2 = (a * d - b * c) ^ 2 * (a * d + b * c) ^ 2 := by rw [hdiff]; ring
    _ ≤ (a * d - b * c) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := mul_one _

/-- Equation (1), including zero total tilt. -/
theorem long_crossing_ge (U : unitary Mat) :
    longFactor (tiltSum U) * tiltDiff U ^ 2 / 4 ≤ longCrossing U := by
  have hrad := (radical_unscaled (odd_mass_mem U 0) (odd_mass_mem U 3)).trans
    (singletonPairWeight_ge_radical U 0 3)
  have hbase : tiltDiff U ^ 2 / 4 ≤ longCrossing U := by
    unfold tiltDiff oddTilt longCrossing sym
    linarith only [hrad]
  by_cases hzero : tiltSum U = 0
  · simp only [longFactor, ite_eq_left hzero, zero_mul, zero_div]
    exact (div_nonneg (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)).trans hbase
  · have hpos := lt_of_le_of_ne (tiltSum_nonneg U) (Ne.symm hzero)
    have hproduct := (div_le_iff₀ hpos).2
      (show tiltDiff U ^ 2 / 4 ≤ longCrossing U * tiltSum U by
        simpa only [mul_comm (longCrossing U)] using long_crossing_mul U)
    rw [longFactor, ite_eq_right hzero]
    rcases le_total (1 : ℝ) (1 / tiltSum U) with h | h
    · rw [max_eq_right h]
      calc
        _ = (tiltDiff U ^ 2 / 4) / tiltSum U := by ring
        _ ≤ _ := hproduct
    · simpa only [max_eq_left h, one_mul] using hbase

def endCharge (U : unitary Mat) (i : Fin 4) : ℝ :=
  emptyProbability (frameVector U i) - fullProbability (frameVector U i)

/-- The weighted cuts, retaining the long crossing and the signed charges. -/
def retainedCost (U : unitary Mat) (A B : Fin 3 → ℝ) (Z₀ Z₂ Zlong : ℝ) : ℝ :=
  let W := sym (frameWeight U)
  A 0 * (W 0 1 + W 0 2 + W 0 3) +
  A 1 * (forwardCutWeight U + reverseCutWeight U) +
  A 2 * (W 0 3 + W 1 3 + W 2 3) +
  B 0 * (-endCharge U 0) + B 1 * (-cutImbalance U) + B 2 * endCharge U 3 +
  Z₀ * lowerAdjacentCutWeight U + Z₂ * upperAdjacentCutWeight U + Zlong * longCrossing U

/-- Weighted cost of the cuts in the occupation frame. -/
def occupationCost (A B : Fin 3 → ℝ) (Z₀ Z₂ : ℝ) : ℝ :=
  2 * (A 0 + A 1 + A 2) - (B 0 + B 1 + B 2) + Z₀ + Z₂

def matchedMixture (A B : Fin 3 → ℝ) : ℝ := B 1 / 2 - A 1

/-- The two singleton corrections for a common adjacent mixture weight. -/
def singletonCorrection (U : unitary Mat) (A B : Fin 3 → ℝ) (Z₀ Z₂ L : ℝ) : ℝ :=
  let P₀ := (A 0 + Z₀ - L) / 2
  let P₂ := (A 2 + Z₂ - L) / 2
  P₀ * oddTilt U 0 ^ 2 + P₂ * oddTilt U 3 ^ 2 +
    (B 0 / 2 - 2 * P₀) * oddTilt U 0 + (B 2 / 2 - 2 * P₂) * oddTilt U 3

private theorem weighted_charge {R y v u B μ : ℝ}
    (hR : |R| ≤ min ((1 + y) / 2) (v + (1 - y) / 2 - u))
    (hμ : 0 ≤ μ) (hμB : μ ≤ B) :
    -B * (1 + y) / 2 + μ * (y + u - v) ≤ B * R := by
  have hlocal := mul_le_mul_of_nonneg_left
    (abs_le.mp (hR.trans (min_le_left _ _))).1 (sub_nonneg.mpr hμB)
  have hpartner := mul_le_mul_of_nonneg_left
    (abs_le.mp (hR.trans (min_le_right _ _))).1 hμ
  linarith only [hlocal, hpartner]

/-- The equal adjacent mixtures and equal endpoint charges before completing
the two squares. Multiplication by the absolute weights works at a zero cut. -/
private theorem equal_mixture_quadratic (U : unitary Mat) (A B : Fin 3 → ℝ)
    (Z₀ Z₂ Zlong L μ : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB₁ : 0 ≤ B 1) (hZlong : 0 ≤ Zlong)
    (hL : 0 ≤ L) (hL₀ : L ≤ Z₀) (hL₂ : L ≤ Z₂)
    (hμ : 0 ≤ μ) (hμ₀ : μ ≤ B 0) (hμ₂ : μ ≤ B 2) :
    let u := -cutEvenOffset U
    let w := 1 - |cutImbalance U|
    let H := A 1 + L
    occupationCost A B Z₀ Z₂ + singletonCorrection U A B Z₀ Z₂ L +
      (H * w ^ 2 + (B 1 - 2 * H) * w + μ * (2 * w - tiltSum U)) +
      ((3 * A 1 + L) * u ^ 2 + L * tiltDiff U * u) +
      (Zlong / 4) * longFactor (tiltSum U) * tiltDiff U ^ 2 ≤
    retainedCost U A B Z₀ Z₂ Zlong := by
  let u := -cutEvenOffset U
  let v := |cutImbalance U|
  let a := oddTilt U 0
  let b := oddTilt U 3
  obtain ⟨hD₀, hD₂⟩ := singletonCutWeight_eq U
  obtain ⟨hD₁, hD₀₁, hD₁₂⟩ := adjacentCutWeight_ge_signed U
  obtain ⟨hLocal₀, hLocal₂⟩ := adjacentCutWeight_ge_local U
  obtain ⟨hCharge₀, hCharge₂⟩ := endCutCharge_abs_le U
  change _ = 3 / 2 + (1 - a) ^ 2 / 2 at hD₀
  change _ = 3 / 2 + (1 - b) ^ 2 / 2 at hD₂
  change 1 + v ^ 2 + 3 * u ^ 2 ≤ _ at hD₁
  change (1 + v ^ 2) / 2 + (a - 1) * u + u ^ 2 / 2 ≤ _ at hD₀₁
  change (1 + v ^ 2) / 2 - (b - 1) * u + u ^ 2 / 2 ≤ _ at hD₁₂
  change |-endCharge U 0| ≤ min ((1 + (1 - a)) / 2) (v + (1 - (1 - a)) / 2 - u)
    at hCharge₀
  change |endCharge U 3| ≤ min ((1 + (1 - b)) / 2) (v + (1 - (1 - b)) / 2 + u)
    at hCharge₂
  have hCost₀ := mul_le_mul_of_nonneg_left hD₀.ge (hA 0)
  have hCost₁ := mul_le_mul_of_nonneg_left hD₁ (hA 1)
  have hCost₂ := mul_le_mul_of_nonneg_left hD₂.ge (hA 2)
  have hAdj₀ := mul_le_mul_of_nonneg_left hD₀₁ hL
  have hAdj₂ := mul_le_mul_of_nonneg_left hD₁₂ hL
  have hEnd₀ : (1 + (1 - a) ^ 2) / 2 ≤ lowerAdjacentCutWeight U := by
    dsimp only [a, oddTilt]
    linarith only [hLocal₀]
  have hEnd₂ : (1 + (1 - b) ^ 2) / 2 ≤ upperAdjacentCutWeight U := by
    dsimp only [b, oddTilt]
    linarith only [hLocal₂]
  have hRem₀ := mul_le_mul_of_nonneg_left hEnd₀ (sub_nonneg.mpr hL₀)
  have hRem₂ := mul_le_mul_of_nonneg_left hEnd₂ (sub_nonneg.mpr hL₂)
  have hPenalty₀ := weighted_charge hCharge₀ hμ hμ₀
  have hPenalty₂ := weighted_charge (show |endCharge U 3| ≤
    min ((1 + (1 - b)) / 2) (v + (1 - (1 - b)) / 2 - (-u)) by
      simpa only [sub_neg_eq_add] using hCharge₂) hμ hμ₂
  have hPenalty₁ : B 1 * (-v) ≤ B 1 * (-cutImbalance U) :=
    mul_le_mul_of_nonneg_left (neg_le_neg (le_abs_self _)) hB₁
  have hLong := mul_le_mul_of_nonneg_left (long_crossing_ge U) hZlong
  change Zlong * (longFactor (a + b) * (a - b) ^ 2 / 4) ≤ _ at hLong
  dsimp only [occupationCost, singletonCorrection, retainedCost, tiltSum, tiltDiff]
  change _ + _ + ((A 1 + L) * (1 - v) ^ 2 +
      (B 1 - 2 * (A 1 + L)) * (1 - v) + μ * (2 * (1 - v) - (a + b))) +
      ((3 * A 1 + L) * u ^ 2 + L * (a - b) * u) + _ ≤ _
  linarith only [hCost₀, hCost₁, hCost₂, hAdj₀, hAdj₂, hRem₀, hRem₂,
    hPenalty₀, hPenalty₁, hPenalty₂, hLong]

/-- The matched estimate (2) for the literal weighted costs of any complex CAR frame. -/
theorem matched_cut_bound (U : unitary Mat) (A B : Fin 3 → ℝ) (Z₀ Z₂ Zlong : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (hZlong : 0 ≤ Zlong)
    (hL : 0 ≤ matchedMixture A B) (hL₀ : matchedMixture A B ≤ Z₀)
    (hL₂ : matchedMixture A B ≤ Z₂) :
    let L₀ := matchedMixture A B
    occupationCost A B Z₀ Z₂ + singletonCorrection U A B Z₀ Z₂ L₀ +
      (Zlong / 4 * longFactor (tiltSum U) - L₀ / 4) * tiltDiff U ^ 2 ≤
      retainedCost U A B Z₀ Z₂ Zlong := by
  let L₀ := matchedMixture A B
  have hcost := equal_mixture_quadratic U A B Z₀ Z₂ Zlong L₀ 0 hA (hB 1)
    hZlong hL hL₀ hL₂ (le_refl 0) (hB 0) (hB 2)
  let u := -cutEvenOffset U
  let w := 1 - |cutImbalance U|
  have hH : A 1 + L₀ = B 1 / 2 := by unfold L₀ matchedMixture; ring
  have hw : 0 ≤ (A 1 + L₀) * w ^ 2 := mul_nonneg (add_nonneg (hA 1) hL) (sq_nonneg w)
  have hu : 0 ≤ L₀ * (u + tiltDiff U / 2) ^ 2 := mul_nonneg hL (sq_nonneg _)
  have hmiddle := mul_nonneg (hA 1) (sq_nonneg u)
  dsimp only at hcost ⊢
  change _ + _ + ((A 1 + L₀) * w ^ 2 + (B 1 - 2 * (A 1 + L₀)) * w +
      0 * (2 * w - tiltSum U)) + ((3 * A 1 + L₀) * u ^ 2 + L₀ * tiltDiff U * u) + _ ≤ _
    at hcost
  rw [hH] at hcost hw
  linarith only [hcost, hw, hu, hmiddle]

/-- Charge multiplier used in the refined estimate. -/
def refinedCharge (U : unitary Mat) (A B : Fin 3 → ℝ) (L : ℝ) : ℝ :=
  L - matchedMixture A B - (A 1 + L) * tiltSum U / 2

/-- Sufficient conditions for the same charge multiplier to be legal at both ends. -/
theorem refined_charge_admissible (U : unitary Mat) (A B : Fin 3 → ℝ) (L : ℝ)
    (hA : 0 ≤ A 1) (hL : 0 ≤ L)
    (hsmall : (A 1 + L) * tiltSum U / 2 ≤ L - matchedMixture A B)
    (hend : L - matchedMixture A B ≤ min (B 0) (B 2)) :
    0 ≤ refinedCharge U A B L ∧ refinedCharge U A B L ≤ min (B 0) (B 2) := by
  have hnonneg := mul_nonneg (add_nonneg hA hL) (tiltSum_nonneg U)
  unfold refinedCharge
  constructor <;> linarith only [hsmall, hend, hnonneg]

private theorem middle_square {A L F u : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) :
    -(L ^ 2 / (4 * (3 * A + L))) * F ^ 2 ≤ (3 * A + L) * u ^ 2 + L * F * u := by
  let K := 3 * A + L
  have hK : 0 ≤ K := by unfold K; positivity
  rcases hK.eq_or_lt with hzero | hpos
  · have hLzero : L = 0 := by dsimp only [K] at hzero; linarith only [hA, hL, hzero]
    change -(L ^ 2 / (4 * K)) * F ^ 2 ≤ K * u ^ 2 + L * F * u
    simp [← hzero, hLzero]
  · change -(L ^ 2 / (4 * K)) * F ^ 2 ≤ K * u ^ 2 + L * F * u
    have h := mul_nonneg hpos.le (sq_nonneg (u + L * F / (2 * K)))
    calc
      -(L ^ 2 / (4 * K)) * F ^ 2 =
          K * u ^ 2 + L * F * u - K * (u + L * F / (2 * K)) ^ 2 := by
        field_simp [hpos.ne']
        ring
      _ ≤ _ := sub_le_self _ h

/-- Estimate (3) for the weighted cuts. The middle-square loss is zero
when the common mixture weight is zero, including a repeated middle level. -/
theorem refined_cut_bound (U : unitary Mat) (A B : Fin 3 → ℝ) (Z₀ Z₂ Zlong : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB₁ : 0 ≤ B 1) (hZlong : 0 ≤ Zlong)
    (hL₀ : 0 ≤ matchedMixture A B)
    (hLleft : matchedMixture A B ≤ Z₀) (hLright : matchedMixture A B ≤ Z₂)
    (hsmall : (A 1 + min Z₀ Z₂) * tiltSum U / 2 ≤ min Z₀ Z₂ - matchedMixture A B)
    (hend : min Z₀ Z₂ - matchedMixture A B ≤ min (B 0) (B 2)) :
    let L₀ := matchedMixture A B
    let L := min Z₀ Z₂
    let ell := L - L₀
    occupationCost A B Z₀ Z₂ + singletonCorrection U A B Z₀ Z₂ L₀ +
      B 1 / 8 * tiltSum U ^ 2 +
      (Zlong / 4 * longFactor (tiltSum U) - ell / 4 - L ^ 2 / (4 * (3 * A 1 + L))) *
        tiltDiff U ^ 2 ≤ retainedCost U A B Z₀ Z₂ Zlong := by
  let L₀ := matchedMixture A B
  let L := min Z₀ Z₂
  let ell := L - L₀
  let H := A 1 + L
  let μ := refinedCharge U A B L
  let u := -cutEvenOffset U
  let w := 1 - |cutImbalance U|
  let S := tiltSum U
  let F := tiltDiff U
  have hL : 0 ≤ L := hL₀.trans (le_min hLleft hLright)
  obtain ⟨hμ, hμB⟩ := refined_charge_admissible U A B L (hA 1) hL hsmall hend
  have hcost := equal_mixture_quadratic U A B Z₀ Z₂ Zlong L μ hA hB₁ hZlong hL
    (min_le_left _ _) (min_le_right _ _) hμ (hμB.trans (min_le_left _ _))
    (hμB.trans (min_le_right _ _))
  have hH : H = B 1 / 2 + ell := by unfold H ell L₀ matchedMixture; ring
  have hμeq : μ = ell - H * S / 2 := rfl
  have hw : 0 ≤ H * (w - S / 2) ^ 2 :=
    mul_nonneg (add_nonneg (hA 1) hL) (sq_nonneg _)
  have hu := middle_square (hA 1) hL (F := F) (u := u)
  have hsingle : singletonCorrection U A B Z₀ Z₂ L =
      singletonCorrection U A B Z₀ Z₂ L₀ + ell * S - ell / 4 * (S ^ 2 + F ^ 2) := by
    unfold singletonCorrection ell S F tiltSum tiltDiff
    ring
  dsimp only at hcost ⊢
  change _ + singletonCorrection U A B Z₀ Z₂ L +
    (H * w ^ 2 + (B 1 - 2 * H) * w + μ * (2 * w - S)) +
    ((3 * A 1 + L) * u ^ 2 + L * F * u) + _ ≤ _ at hcost
  rw [hsingle, hμeq, hH] at hcost
  rw [hH] at hw
  change _ + _ + B 1 / 8 * S ^ 2 + (_ - ell / 4 - L ^ 2 / (4 * (3 * A 1 + L))) *
    F ^ 2 ≤ _
  linarith only [hcost, hw, hu]

open WuRepeatedMiddleCubic (Frame alpha weight imbalance)
open WuCubicSignedTransfer (sourceDeficitAt)
open WuCubicDirectedOccupationCap (lowering rowImbalance frameWeight_rowImbalance)
open private occupationBasis lowering_zero lowering_one from
  D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
open private row_mass from D5.S3.Quantum.Semigroups.WuCubicRankTwoCut
open private cutA cutB cut_coefficients c e gamma bias h from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private levelsAt totalAt cubic source_centered_at from
  D5.S3.Quantum.Semigroups.WuCubicSignedTransfer

/-- Relabel a unitary frame by the two-mode occupation pairs. -/
def physicalFrame (U : unitary Mat) : Frame :=
  (U : Mat).submatrix occupationBasis id

private theorem physicalFrame_columns (U : unitary Mat) :
    (physicalFrame U)ᴴ * physicalFrame U = 1 := by
  have hU : (U : Mat)ᴴ * (U : Mat) = 1 := Unitary.coe_star_mul_self U
  change ((U : Mat)ᴴ).submatrix id occupationBasis * (U : Mat).submatrix occupationBasis id = _
  rw [Matrix.submatrix_mul_equiv _ _ _ occupationBasis, hU]
  exact Matrix.submatrix_id_id (1 : Mat)

private theorem physicalFrame_rows (U : unitary Mat) :
    physicalFrame U * (physicalFrame U)ᴴ = 1 := by
  have hU : (U : Mat) * (U : Mat)ᴴ = 1 := Unitary.coe_mul_star_self U
  change (U : Mat).submatrix occupationBasis id * ((U : Mat)ᴴ).submatrix id occupationBasis = _
  rw [← Matrix.submatrix_mul (U : Mat) (U : Mat)ᴴ occupationBasis id occupationBasis
    Function.bijective_id, hU]
  exact Matrix.submatrix_one_equiv occupationBasis

private theorem physicalFrame_weight (U : unitary Mat) (i j : Fin 4) :
    weight (physicalFrame U) i j = frameWeight U i j := by
  unfold weight frameWeight
  apply Finset.sum_congr rfl
  intro k _
  rw [Unitary.conjStarAlgAut_symm_apply]
  have hJ : (lowering k).submatrix occupationBasis occupationBasis =
      TwistedTwoModeOUComparison.modeJump k := by
    ext x y
    simp [lowering, Matrix.reindex_apply]
  have hW :
      (((U : Mat)ᴴ * lowering k) * (U : Mat)).submatrix id id =
        (physicalFrame U)ᴴ * TwistedTwoModeOUComparison.modeJump k * physicalFrame U := by
    rw [← Matrix.submatrix_mul_equiv _ _ id occupationBasis id,
      ← Matrix.submatrix_mul_equiv (U : Mat)ᴴ (lowering k) id occupationBasis occupationBasis, hJ]
    rfl
  exact congrArg (fun M : Mat => Complex.normSq (M i j)) hW.symm

private theorem physicalFrame_charge (U : unitary Mat) (i : Fin 4) :
    imbalance (physicalFrame U) i = endCharge U i := rfl

/-- The normalized ordinary-trace deficit in the spectral frame. -/
def normalizedDeficit (r : ℝ) (U : unitary Mat) (m n q : ℝ) : ℝ :=
  sourceDeficitAt r (physicalFrame U) m n q

open WuCubicOperatorBridge (G GInv D generator)
open private weighted_spectral_energy spectral_entropy_operator spectralEntropy from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

/-- Exact ordinary-trace link for the spectrum (m,n,q,1), using the same
CAR weights and the spectral Gibbs logarithm. -/
theorem normalized_deficit_eq_ordinary_trace {r : ℝ} (hr : 1 ≤ r)
    (U : unitary Mat) (m n q : ℝ) :
    let V := physicalFrame U
    let M := V * diagonal (fun i => (levelsAt m n q i : ℂ)) * Vᴴ
    let X := GInv r * M * GInv r
    normalizedDeficit r U m n q =
      (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re -
        alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
          (M ^ 3).trace.re * Real.log (M ^ 3).trace.re) := by
  dsimp only
  rw [weighted_spectral_energy hr _ (physicalFrame_columns U) (physicalFrame_rows U),
    ← spectral_entropy_operator r _ (physicalFrame_columns U) (physicalFrame_rows U)]
  unfold normalizedDeficit sourceDeficitAt spectralEntropy
  simp [Fin.sum_univ_four, totalAt, levelsAt]

/-- The diagonal weights of the signed spectral cut expansion. -/
def cutEnergy (r m n q : ℝ) : Fin 3 → ℝ := ![cutA r m n, cutA r n q, cutA r q 1]

def cutBias (r m n q : ℝ) : Fin 3 → ℝ := ![cutB r m n, cutB r n q, cutB r q 1]

private def directedCoeff (r v w y z extra : ℝ) : ℝ :=
  3 * e r * (w - v) * (z - y) * ((w - v) + (z - y) + 2 * extra)

private def crossCoeff (r v w y z extra : ℝ) : ℝ :=
  c r * (w - v) * (z - y) * (w + v + (z + y)) - directedCoeff r v w y z extra

def lowerCoeff (r m n q : ℝ) : ℝ := crossCoeff r m n n q 0

def upperCoeff (r n q : ℝ) : ℝ := crossCoeff r n q q 1 0

def longCoeff (r m n q : ℝ) : ℝ := crossCoeff r m n q 1 (q - n)

def thermalCenter (r m n q : ℝ) : ℝ :=
  h r * totalAt m n q +
    alpha r * (totalAt m n q * Real.log (totalAt m n q / 4) -
      m ^ 3 * Real.log (m ^ 3) - n ^ 3 * Real.log (n ^ 3) - q ^ 3 * Real.log (q ^ 3))

def occupationDeficit (r m n q : ℝ) : ℝ :=
  thermalCenter r m n q +
    occupationCost (cutEnergy r m n q) (cutBias r m n q) (lowerCoeff r m n q) (upperCoeff r n q)

/-- The three directed corrections that supplement the retained symmetric cuts. -/
def directedCost (r : ℝ) (U : unitary Mat) (m n q : ℝ) : ℝ :=
  2 * directedCoeff r m n n q 0 * (frameWeight U 2 0 + frameWeight U 3 0) +
  2 * directedCoeff r n q q 1 0 * (frameWeight U 3 0 + frameWeight U 3 1) +
  2 * directedCoeff r m n q 1 (q - n) * frameWeight U 3 0

private theorem cutImbalance_eq_endCharge (U : unitary Mat) :
    cutImbalance U = endCharge U 0 + endCharge U 1 := by
  unfold cutImbalance WuCubicRankTwoCut.cutEmpty WuCubicRankTwoCut.cutFull endCharge
  ring

private theorem endCharge_sum (U : unitary Mat) :
    endCharge U 0 + endCharge U 1 + endCharge U 2 + endCharge U 3 = 0 := by
  have h₀ := row_mass U 0
  have h₃ := row_mass U 3
  simp only [Fin.sum_univ_four] at h₀ h₃
  simp only [endCharge, emptyProbability, fullProbability, frameVector]
  linarith only [h₀, h₃]

/-- Exact signed cut expansion, with the triple-gap term in the long crossing. -/
theorem normalized_deficit_eq_cuts {r : ℝ} (hr : 1 ≤ r) (U : unitary Mat)
    {m n q : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hq : 0 ≤ q) :
    normalizedDeficit r U m n q = thermalCenter r m n q +
      retainedCost U (cutEnergy r m n q) (cutBias r m n q)
        (lowerCoeff r m n q) (upperCoeff r n q) (longCoeff r m n q) +
      directedCost r U m n q := by
  have hrow₀ := frameWeight_rowImbalance U 0
  have hrow₁ := frameWeight_rowImbalance U 1
  have hrow₃ := frameWeight_rowImbalance U 3
  change rowImbalance (frameWeight U) 0 = 2 * endCharge U 0 at hrow₀
  change rowImbalance (frameWeight U) 1 = 2 * endCharge U 1 at hrow₁
  change rowImbalance (frameWeight U) 3 = 2 * endCharge U 3 at hrow₃
  simp only [rowImbalance, Fin.sum_univ_four] at hrow₀ hrow₁ hrow₃
  unfold normalizedDeficit
  rw [source_centered_at hr _ (physicalFrame_columns U) (physicalFrame_rows U) hm hn hq]
  simp only [thermalCenter, physicalFrame_weight, physicalFrame_charge, retainedCost, cutEnergy,
    cutBias, cutA, cutB, lowerCoeff, upperCoeff, longCoeff, crossCoeff, directedCost, directedCoeff,
    lowerAdjacentCutWeight, upperAdjacentCutWeight, longCrossing, sym, forwardCutWeight,
    reverseCutWeight, cutImbalance_eq_endCharge, Fin.sum_univ_four, levelsAt, cubic,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination
    - e r * (n - m) ^ 3 * hrow₀ -
    e r * (q - n) ^ 3 * hrow₀ - e r * (q - n) ^ 3 * hrow₁ +
    e r * (1 - q) ^ 3 * hrow₃ + bias r * q ^ 3 * endCharge_sum U

private theorem e_nonneg {r : ℝ} (hr : 1 ≤ r) : 0 ≤ e r := by
  have hr0 := zero_le_one.trans hr
  have ht := sub_nonneg.mpr hr
  unfold e gamma
  positivity

private theorem three_e_le_c {r : ℝ} (hr : 1 ≤ r) : 3 * e r ≤ c r := by
  have hr0 := zero_le_one.trans hr
  have heq : c r - 3 * e r = gamma r * r := by unfold c e; ring
  have hh : 0 ≤ gamma r * r := by unfold gamma; positivity
  linarith only [heq, hh]

private theorem spectral_coefficients_nonneg {r m n q : ℝ}
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1) :
    (∀ i, 0 ≤ cutEnergy r m n q i) ∧ (∀ i, 0 ≤ cutBias r m n q i) ∧
      0 ≤ longCoeff r m n q := by
  have hn := hm.trans hmn
  have hq := hn.trans hnq
  have h₀ := cut_coefficients hr hm hmn
  have h₁ := cut_coefficients hr hn hnq
  have h₂ := cut_coefficients hr hq hq1
  have hspan : 0 ≤ (n - m) + (1 - q) + 2 * (q - n) := by linarith only [hmn, hnq, hq1]
  have hcompare : (n - m) + (1 - q) + 2 * (q - n) ≤ n + m + (1 + q) := by
    linarith only [hm, hn]
  have hc : 0 ≤ c r := (mul_nonneg (by norm_num) (e_nonneg hr)).trans (three_e_le_c hr)
  have hcoeff : 3 * e r * ((n - m) + (1 - q) + 2 * (q - n)) ≤
      c r * (n + m + (1 + q)) :=
    (mul_le_mul_of_nonneg_right (three_e_le_c hr) hspan).trans
      (mul_le_mul_of_nonneg_left hcompare hc)
  have hlong : 0 ≤ longCoeff r m n q := calc
    0 ≤ (n - m) * (1 - q) *
        (c r * (n + m + (1 + q)) - 3 * e r * ((n - m) + (1 - q) + 2 * (q - n))) :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hmn) (sub_nonneg.mpr hq1)) (sub_nonneg.mpr hcoeff)
    _ = _ := by unfold longCoeff crossCoeff directedCoeff; ring
  refine ⟨?_, ?_, hlong⟩
  · intro i
    fin_cases i
    · exact h₀.1
    · exact h₁.1
    · exact h₂.1
  · intro i
    fin_cases i
    · exact h₀.2
    · exact h₁.2
    · exact h₂.2

private theorem directedCost_nonneg {r m n q : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1) :
    0 ≤ directedCost r U m n q := by
  have he := e_nonneg hr
  have h₀ := sub_nonneg.mpr hmn
  have h₁ := sub_nonneg.mpr hnq
  have h₂ := sub_nonneg.mpr hq1
  have hw (i j : Fin 4) : 0 ≤ frameWeight U i j := by
    unfold frameWeight
    exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hw₂₀ := hw 2 0
  have hw₃₀ := hw 3 0
  have hw₃₁ := hw 3 1
  unfold directedCost directedCoeff
  positivity

private theorem centered_retained_le {r m n q : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1) :
    thermalCenter r m n q + retainedCost U (cutEnergy r m n q) (cutBias r m n q)
      (lowerCoeff r m n q) (upperCoeff r n q) (longCoeff r m n q) ≤
      normalizedDeficit r U m n q := by
  rw [normalized_deficit_eq_cuts hr U hm (hm.trans hmn) (hm.trans (hmn.trans hnq))]
  exact le_add_of_nonneg_right (directedCost_nonneg U hr hmn hnq hq1)

private theorem frameWeight_occupation (i j : Fin 4) :
    frameWeight (1 : unitary Mat) i j =
      if (i = 0 ∧ (j = 1 ∨ j = 2)) ∨ ((i = 1 ∨ i = 2) ∧ j = 3) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [frameWeight, Unitary.conjStarAlgAut_symm_apply, Fin.sum_univ_two,
      lowering_zero, lowering_one]

/-- The scalar reference in the estimates is the deficit of the same spectrum
in the occupation frame. -/
theorem occupation_deficit_eq {r : ℝ} (hr : 1 ≤ r)
    {m n q : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hq : 0 ≤ q) :
    normalizedDeficit r 1 m n q = occupationDeficit r m n q := by
  rw [normalized_deficit_eq_cuts hr 1 hm hn hq]
  norm_num [occupationDeficit, occupationCost, retainedCost, directedCost, frameWeight_occupation,
    lowerAdjacentCutWeight, upperAdjacentCutWeight, forwardCutWeight, reverseCutWeight,
    longCrossing, sym, cutImbalance, WuCubicRankTwoCut.cutEmpty, WuCubicRankTwoCut.cutFull,
    endCharge, emptyProbability, fullProbability, frameVector, Matrix.one_apply]
  ring

/-- Equation (2) for the actual normalized ordinary-trace cubic deficit. -/
theorem matched_deficit_bound {r m n q : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1)
    (hL : 0 ≤ matchedMixture (cutEnergy r m n q) (cutBias r m n q))
    (hleft : matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ lowerCoeff r m n q)
    (hright : matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ upperCoeff r n q) :
    let A := cutEnergy r m n q
    let B := cutBias r m n q
    let L₀ := matchedMixture A B
    occupationDeficit r m n q +
      singletonCorrection U A B (lowerCoeff r m n q) (upperCoeff r n q) L₀ +
      (longCoeff r m n q / 4 * longFactor (tiltSum U) - L₀ / 4) * tiltDiff U ^ 2 ≤
        normalizedDeficit r U m n q := by
  obtain ⟨hA, hB, hlong⟩ := spectral_coefficients_nonneg hr hm hmn hnq hq1
  have hbound := matched_cut_bound U _ _ _ _ _ hA hB hlong hL hleft hright
  have htotal := add_le_add_right hbound (thermalCenter r m n q)
  apply le_trans _ (centered_retained_le U hr hm hmn hnq hq1)
  simpa only [occupationDeficit, add_assoc] using htotal

/-- Equation (3), with the frame-dependent admissibility and the additional
B₁ S²/8 term. -/
theorem refined_deficit_bound {r m n q : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1)
    (hL : 0 ≤ matchedMixture (cutEnergy r m n q) (cutBias r m n q))
    (hleft : matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ lowerCoeff r m n q)
    (hright : matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤ upperCoeff r n q)
    (hsmall : (cutEnergy r m n q 1 + min (lowerCoeff r m n q) (upperCoeff r n q)) *
      tiltSum U / 2 ≤
      min (lowerCoeff r m n q) (upperCoeff r n q) -
        matchedMixture (cutEnergy r m n q) (cutBias r m n q))
    (hend : min (lowerCoeff r m n q) (upperCoeff r n q) -
      matchedMixture (cutEnergy r m n q) (cutBias r m n q) ≤
        min (cutBias r m n q 0) (cutBias r m n q 2)) :
    let A := cutEnergy r m n q
    let B := cutBias r m n q
    let L₀ := matchedMixture A B
    let L := min (lowerCoeff r m n q) (upperCoeff r n q)
    occupationDeficit r m n q +
      singletonCorrection U A B (lowerCoeff r m n q) (upperCoeff r n q) L₀ +
      B 1 / 8 * tiltSum U ^ 2 +
      (longCoeff r m n q / 4 * longFactor (tiltSum U) - (L - L₀) / 4 -
        L ^ 2 / (4 * (3 * A 1 + L))) * tiltDiff U ^ 2 ≤ normalizedDeficit r U m n q := by
  obtain ⟨hA, hB, hlong⟩ := spectral_coefficients_nonneg hr hm hmn hnq hq1
  have hbound := refined_cut_bound U _ _ _ _ _ hA (hB 1) hlong hL hleft hright hsmall hend
  have htotal := add_le_add_right hbound (thermalCenter r m n q)
  apply le_trans _ (centered_retained_le U hr hm hmn hnq hq1)
  simpa only [occupationDeficit, add_assoc] using htotal

/-- At a repeated middle level the matched and refined mixtures and charges
are legal for every frame, and their middle and mixture losses vanish. -/
theorem repeated_middle_angular_bound {r m n : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hn1 : n ≤ 1) :
    occupationDeficit r m n n +
      singletonCorrection U (cutEnergy r m n n) (cutBias r m n n) 0 0 0 +
      longCoeff r m n n / 4 * longFactor (tiltSum U) * tiltDiff U ^ 2 ≤
        normalizedDeficit r U m n n := by
  have hA₁ : cutEnergy r m n n 1 = 0 := by simp [cutEnergy, cutA]
  have hB₁ : cutBias r m n n 1 = 0 := by simp [cutBias, cutB]
  have hL₀ : matchedMixture (cutEnergy r m n n) (cutBias r m n n) = 0 := by
    simp [matchedMixture, hA₁, hB₁]
  have hleft : lowerCoeff r m n n = 0 := by simp [lowerCoeff, crossCoeff, directedCoeff]
  have hright : upperCoeff r n n = 0 := by simp [upperCoeff, crossCoeff, directedCoeff]
  obtain ⟨_, hB, _⟩ := spectral_coefficients_nonneg hr hm hmn (le_refl n) hn1
  have hbound := refined_deficit_bound U hr hm hmn (le_refl n) hn1
    (by simp [hL₀]) (by simp [hL₀, hleft]) (by simp [hL₀, hright])
    (by simp [hA₁, hleft, hright, hL₀])
    (by simpa [hleft, hright, hL₀] using le_min (hB 0) (hB 2))
  simpa [hA₁, hB₁, hL₀, hleft, hright] using hbound

#print axioms long_crossing_ge
#print axioms matched_cut_bound
#print axioms refined_cut_bound
#print axioms normalized_deficit_eq_ordinary_trace
#print axioms normalized_deficit_eq_cuts
#print axioms occupation_deficit_eq
#print axioms matched_deficit_bound
#print axioms refined_deficit_bound
#print axioms repeated_middle_angular_bound

end D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
