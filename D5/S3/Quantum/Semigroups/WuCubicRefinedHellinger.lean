/- GID: D5/S3/Quantum/Semigroups/WuCubicRefinedHellinger
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicRefinedHellinger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The refined Hellinger loss for the ordinary-trace two-CAR Wu cubic deficit. -/

import D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! The lower-region angular certificate for Wu v1 (3.54) at exponent three.
The cut completion uses equal endpoint charges through total tilt 2/3. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicRefinedHellinger

open WuCubicDirectedOccupationCap (Mat)
open WuCubicRankTwoCut (cutEvenOffset cutImbalance)
open WuCubicAngularCertificate
open WuCubicHellingerCut (long_crossing_ge_hellinger)
open private equal_mixture_quadratic middle_square
  spectral_coefficients_nonneg centered_retained_le from
  D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open private matrix_nonneg nonneg_quadratic_lower_bound from
  D5.S3.Quantum.Semigroups.WuCubicHellingerCut
open private odd_mass_mem from D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing

private theorem retainedCost_add_long (U : unitary Mat) (A B : Fin 3 → ℝ)
    (Z₀ Z₂ Zlong : ℝ) :
    retainedCost U A B Z₀ Z₂ Zlong =
      retainedCost U A B Z₀ Z₂ 0 + Zlong * longCrossing U := by
  simp only [retainedCost, zero_mul, add_zero]

/-- The equal-charge cut at L = L₀ + B₁/4, retaining the full long crossing.
Real division assigns zero middle-square loss when L = 0. -/
theorem equal_charge_cut_bound (U : unitary Mat) (A B : Fin 3 → ℝ) (Z₀ Z₂ Zlong : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB₁ : 0 ≤ B 1) (hS : tiltSum U ≤ 2 / 3) :
    let L₀ := matchedMixture A B
    let ell := B 1 / 4
    let L := L₀ + ell
    0 ≤ L₀ → L ≤ Z₀ → L ≤ Z₂ → ell ≤ B 0 → ell ≤ B 2 →
    occupationCost A B Z₀ Z₂ + singletonCorrection U A B Z₀ Z₂ L₀ +
      B 1 / 8 * tiltSum U ^ 2 -
      (ell + L ^ 2 / (3 * A 1 + L)) / 4 * tiltDiff U ^ 2 +
      Zlong * longCrossing U ≤ retainedCost U A B Z₀ Z₂ Zlong := by
  intro L₀ ell L hL₀ hleft hright hend₀ hend₂
  let H := A 1 + L
  let μ := refinedCharge U A B L
  let u := -cutEvenOffset U
  let w := 1 - |cutImbalance U|
  let S := tiltSum U
  let F := tiltDiff U
  have hell : 0 ≤ ell := div_nonneg hB₁ (by norm_num)
  have hL : 0 ≤ L := add_nonneg hL₀ hell
  have hgap : L - L₀ = ell := by dsimp only [L]; ring
  have hH : H = B 1 / 2 + ell := by unfold H L L₀ matchedMixture; ring
  have hHthree : H = 3 * ell := by rw [hH]; dsimp only [ell]; ring
  have hsmall : H * S / 2 ≤ L - L₀ := by
    rw [hgap, hHthree]
    have h := mul_le_mul_of_nonneg_left hS (show 0 ≤ 3 * ell by positivity)
    linarith only [h]
  have hend : L - L₀ ≤ min (B 0) (B 2) := by rw [hgap]; exact le_min hend₀ hend₂
  obtain ⟨hμ, hμB⟩ := refined_charge_admissible U A B L (hA 1) hL hsmall hend
  have hcost := equal_mixture_quadratic U A B Z₀ Z₂ 0 L μ hA hB₁ (le_refl 0) hL
    hleft hright hμ (hμB.trans (min_le_left _ _)) (hμB.trans (min_le_right _ _))
  have hμeq : μ = ell - H * S / 2 := by
    change L - L₀ - H * S / 2 = _
    rw [hgap]
  have hw : 0 ≤ H * (w - S / 2) ^ 2 :=
    mul_nonneg (add_nonneg (hA 1) hL) (sq_nonneg _)
  have hu := middle_square (hA 1) hL (F := F) (u := u)
  have hsingle : singletonCorrection U A B Z₀ Z₂ L =
      singletonCorrection U A B Z₀ Z₂ L₀ + ell * S - ell / 4 * (S ^ 2 + F ^ 2) := by
    unfold singletonCorrection L S F tiltSum tiltDiff
    ring
  dsimp only at hcost
  simp only [zero_div, zero_mul, add_zero] at hcost
  change _ + singletonCorrection U A B Z₀ Z₂ L +
    (H * w ^ 2 + (B 1 - 2 * H) * w + μ * (2 * w - S)) +
    ((3 * A 1 + L) * u ^ 2 + L * F * u) ≤ _ at hcost
  rw [hsingle, hμeq, hH] at hcost
  rw [hH] at hw
  have hloss : L ^ 2 / (4 * (3 * A 1 + L)) = L ^ 2 / (3 * A 1 + L) / 4 := by
    rw [div_div, mul_comm (3 * A 1 + L)]
  rw [hloss] at hu
  rw [retainedCost_add_long]
  linarith only [hcost, hw, hu]

private theorem middle_loss_le_weight {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) :
    L ^ 2 / (3 * A + L) ≤ L := by
  have hden : 0 ≤ 3 * A + L := by positivity
  rcases hden.eq_or_lt with hzero | hpos
  · simpa only [← hzero, div_zero] using hL
  · apply (div_le_iff₀ hpos).mpr
    nlinarith only [mul_nonneg hA hL]

private theorem nonneg_of_discriminant {A B C : ℝ}
    (hA : 0 < A) (hdisc : 0 ≤ 4 * A * C - B ^ 2) (v : ℝ) :
    0 ≤ A * v ^ 2 + B * v + C := by
  have hscale : 0 < 4 * A := by positivity
  apply (mul_nonneg_iff_of_pos_left hscale).mp
  calc
    0 ≤ (2 * A * v + B) ^ 2 + (4 * A * C - B ^ 2) :=
      add_nonneg (sq_nonneg _) hdisc
    _ = _ := by ring

private theorem singleton_nonneg_of_large_tilt {a b P₀ P₂ G₀ G₂ : ℝ}
    (hS : 2 / 3 ≤ a + b) (hP₀ : 0 < P₀) (hP₂ : 0 < P₂) :
    let A := (2 / 3) * (P₀ + P₂)
    let B := G₀ - G₂ - (4 / 3) * P₂
    let C := (2 / 3) * P₂ + G₂
    0 ≤ 4 * A * C - B ^ 2 →
    0 ≤ P₀ * a ^ 2 + P₂ * b ^ 2 + G₀ * a + G₂ * b := by
  intro A B C hdisc
  let S := a + b
  let v := a / S
  have hSpos : 0 < S := (by norm_num : (0 : ℝ) < 2 / 3).trans_le hS
  have hv₀ : S * v = a := by dsimp only [v]; field_simp [hSpos.ne']
  have hv₂ : S * (1 - v) = b := by rw [mul_sub, hv₀, mul_one]; dsimp only [S]; ring
  have hA : 0 < A := mul_pos (by norm_num) (add_pos hP₀ hP₂)
  have hquad : 0 ≤ (2 / 3) * (P₀ * v ^ 2 + P₂ * (1 - v) ^ 2) +
      G₀ * v + G₂ * (1 - v) := by
    have h := nonneg_of_discriminant hA hdisc v
    dsimp only [A, B, C] at h
    linarith only [h]
  have hrad := mul_le_mul_of_nonneg_right hS
    (add_nonneg (mul_nonneg hP₀.le (sq_nonneg v))
      (mul_nonneg hP₂.le (sq_nonneg (1 - v))))
  calc
    0 ≤ S * ((2 / 3) * (P₀ * v ^ 2 + P₂ * (1 - v) ^ 2) + G₀ * v + G₂ * (1 - v)) :=
      mul_nonneg hSpos.le hquad
    _ ≤ S * (S * (P₀ * v ^ 2 + P₂ * (1 - v) ^ 2) + G₀ * v + G₂ * (1 - v)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrad]) hSpos.le
    _ = _ := by rw [← hv₀, ← hv₂]; ring

/-- Refined bound (H) for the physical normalized deficit of the ordered
spectrum (m,n,q,1). The hypotheses are spectral tests independent of the
complex unitary frame. The strong residual test uses L as an upper bound
on the middle-square loss. The large-tilt test is the exact discriminant
of the radial quadratic at total tilt 2/3. -/
theorem refined_hellinger_deficit_bound {r m n q : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1) :
    let A := cutEnergy r m n q
    let B := cutBias r m n q
    let Z₀ := lowerCoeff r m n q
    let Z₂ := upperCoeff r n q
    let Zlong := longCoeff r m n q
    let L₀ := matchedMixture A B
    let ell := B 1 / 4
    let L := L₀ + ell
    let P₀ := (A 0 + Z₀ - L₀) / 2
    let P₂ := (A 2 + Z₂ - L₀) / 2
    let p := P₀ + P₂ + B 1 / 2
    let k := (P₀ - P₂) / p
    let G₀ := B 0 / 2 - 2 * P₀
    let G₂ := B 2 / 2 - 2 * P₂
    let Gs := G₀ + G₂
    let R := G₀ - G₂ - k * Gs
    let β := Zlong - k * R
    let η := R ^ 2 / (4 * β)
    let A₂₃ := (2 / 3) * (P₀ + P₂)
    let B₂₃ := G₀ - G₂ - (4 / 3) * P₂
    let C₂₃ := (2 / 3) * P₂ + G₂
    0 ≤ L₀ → L ≤ Z₀ → L ≤ Z₂ → ell ≤ B 0 → ell ≤ B 2 →
    0 < P₀ → 0 < P₂ → L₀ < Zlong →
    0 ≤ p * (P₀ + P₂ - ell - L) - (P₀ - P₂) ^ 2 →
    0 < β → 0 ≤ 4 * A₂₃ * C₂₃ - B₂₃ ^ 2 →
    occupationDeficit r m n q - (max 0 (2 * η - Gs)) ^ 2 / (4 * p) ≤
      normalizedDeficit r U m n q := by
  intro A B Z₀ Z₂ Zlong L₀ ell L P₀ P₂ p k G₀ G₂ Gs R β η A₂₃ B₂₃ C₂₃
    hL₀ hleft hright hend₀ hend₂ hP₀ hP₂ hlong hstrong hβ hdisc
  obtain ⟨hA, hB, hZlong⟩ := spectral_coefficients_nonneg hr hm hmn hnq hq1
  let κ := Zlong / 4
  let a := oddTilt U 0
  let b := oddTilt U 3
  let S := a + b
  let F := a - b
  let z := S + k * F
  let loss := L ^ 2 / (3 * A 1 + L)
  let j := (P₀ + P₂ - p * k ^ 2 - ell - loss) / 4
  have hB₁ : 0 ≤ B 1 := hB 1
  have hp : 0 < p := add_pos_of_pos_of_nonneg (add_pos hP₀ hP₂) (div_nonneg hB₁ (by norm_num))
  have hcenter := centered_retained_le U hr hm hmn hnq hq1
  change thermalCenter r m n q + retainedCost U A B Z₀ Z₂ Zlong ≤ _ at hcenter
  by_cases hS : S ≤ 2 / 3
  · have hcut := equal_charge_cut_bound U A B Z₀ Z₂ Zlong hA hB₁ hS
      hL₀ hleft hright hend₀ hend₂
    change occupationCost A B Z₀ Z₂ +
      (P₀ * a ^ 2 + P₂ * b ^ 2 + G₀ * a + G₂ * b) + B 1 / 8 * S ^ 2 -
      (ell + loss) / 4 * F ^ 2 + Zlong * longCrossing U ≤ _ at hcut
    have ha : 0 ≤ a := mul_nonneg (by norm_num) (odd_mass_mem U 0).1
    have hb : 0 ≤ b := mul_nonneg (by norm_num) (odd_mass_mem U 3).1
    have hp₀₂ : p = P₀ + P₂ + B 1 / 2 := rfl
    have hk₀ : -1 < k := (lt_div_iff₀ hp).mpr (by linarith only [hp₀₂, hB₁, hP₀])
    have hk₂ : k < 1 := (div_lt_iff₀ hp).mpr (by linarith only [hp₀₂, hB₁, hP₂])
    have hk : 0 ≤ 1 - k ^ 2 := by
      have h := mul_nonneg (sub_nonneg.mpr hk₂.le) (show 0 ≤ 1 + k by linarith only [hk₀])
      nlinarith only [h]
    have hz : 0 ≤ z := calc
      0 ≤ (1 + k) * a + (1 - k) * b :=
        add_nonneg (mul_nonneg (by linarith only [hk₀]) ha) (mul_nonneg (sub_nonneg.mpr hk₂.le) hb)
      _ = z := by dsimp only [z, S, F]; ring
    have hpk : p * k = P₀ - P₂ := by dsimp only [k]; field_simp [hp.ne']
    have hstrong' : 0 ≤ p * (P₀ + P₂ - p * k ^ 2 - ell - L) := calc
      0 ≤ p * (P₀ + P₂ - ell - L) - (P₀ - P₂) ^ 2 := hstrong
      _ = _ := by rw [← hpk]; ring
    have hstrong'' := (mul_nonneg_iff_of_pos_left hp).mp hstrong'
    have hL : 0 ≤ L := add_nonneg hL₀ (div_nonneg hB₁ (by norm_num))
    have hloss : loss ≤ L := middle_loss_le_weight (hA 1) hL
    have hj : 0 ≤ j := div_nonneg (by linarith only [hstrong'', hloss]) (by norm_num)
    have hcollect :
        P₀ * a ^ 2 + P₂ * b ^ 2 + G₀ * a + G₂ * b + B 1 / 8 * S ^ 2 -
          (ell + loss) / 4 * F ^ 2 =
        p * z ^ 2 / 4 + Gs * z / 2 + R * F / 2 + j * F ^ 2 := by
      dsimp only [z, R, Gs, j, S, F]
      linear_combination -((a + b) * (a - b) / 2) * hpk - ((a + b) ^ 2 / 4) * hp₀₂
    have hκ : 0 < κ := div_pos (hL₀.trans_lt hlong) (by norm_num)
    have hη : 0 ≤ η := div_nonneg (sq_nonneg R) (by positivity)
    have hcancel : β * η = R ^ 2 / 4 := by dsimp only [η]; field_simp [hβ.ne']
    have hβeq : 4 * κ - k * R = β := by dsimp only [κ, β]; ring
    have hdet : 0 ≤ (1 - k ^ 2) * η ^ 2 + (4 * κ - k * R) * η - R ^ 2 / 4 := by
      rw [hβeq, hcancel, add_sub_cancel_right]
      exact mul_nonneg hk (sq_nonneg η)
    have hmatrix := matrix_nonneg ha hb hκ hη hdet
    change 0 ≤ R * F / 2 + 2 * κ * (Real.sqrt a - Real.sqrt b) ^ 2 + η * z at hmatrix
    have hcross := mul_le_mul_of_nonneg_left (long_crossing_ge_hellinger U) hZlong
    change Zlong * ((Real.sqrt a - Real.sqrt b) ^ 2 / 2) ≤ _ at hcross
    have hscale : Zlong * ((Real.sqrt a - Real.sqrt b) ^ 2 / 2) =
        2 * κ * (Real.sqrt a - Real.sqrt b) ^ 2 := by dsimp only [κ]; ring
    rw [hscale] at hcross
    have hradial := nonneg_quadratic_lower_bound (v := 2 * η - Gs) hp hz
    change thermalCenter r m n q + occupationCost A B Z₀ Z₂ -
      (max 0 (2 * η - Gs)) ^ 2 / (4 * p) ≤ _
    linarith only [hcenter, hcut, hcollect, mul_nonneg hj (sq_nonneg F),
      hcross, hmatrix, hradial]
  · have hlarge : 2 / 3 ≤ S := (lt_of_not_ge hS).le
    have hsingle := singleton_nonneg_of_large_tilt hlarge hP₀ hP₂ hdisc
    have hbase := matched_cut_bound U A B Z₀ Z₂ Zlong hA hB hZlong hL₀
      ((le_add_of_nonneg_right (div_nonneg hB₁ (by norm_num))).trans hleft)
      ((le_add_of_nonneg_right (div_nonneg hB₁ (by norm_num))).trans hright)
    change occupationCost A B Z₀ Z₂ +
      (P₀ * a ^ 2 + P₂ * b ^ 2 + G₀ * a + G₂ * b) +
      (Zlong / 4 * longFactor S - L₀ / 4) * F ^ 2 ≤ _ at hbase
    have hSpos : 0 < S := (by norm_num : (0 : ℝ) < 2 / 3).trans_le hlarge
    have hfactor : 1 ≤ longFactor S := by
      rw [longFactor, ite_eq_right hSpos.ne']
      exact le_max_left _ _
    have hlong' : 0 ≤ Zlong / 4 * longFactor S - L₀ / 4 := by
      have h := mul_le_mul_of_nonneg_left hfactor (div_nonneg hZlong (by norm_num : (0 : ℝ) ≤ 4))
      linarith only [h, hlong]
    have hdebit : 0 ≤ (max 0 (2 * η - Gs)) ^ 2 / (4 * p) :=
      div_nonneg (sq_nonneg _) (by positivity)
    change thermalCenter r m n q + occupationCost A B Z₀ Z₂ -
      (max 0 (2 * η - Gs)) ^ 2 / (4 * p) ≤ _
    linarith only [hcenter, hbase, hsingle, mul_nonneg hlong' (sq_nonneg F), hdebit]


open scoped BigOperators
open WuCubicHellingerMatrix
  (Vec3 basis coordinates displacement levels quadratic occupationMatrix lowerTilt upperTilt
    occupationTaylorCoefficient_eq_quadratic)
open WuCubicOccupationTaylor (gibbsLevels occupationTaylorCoefficient occupation_taylor_lower_bound)
open WuCubicGibbsScaledCoefficients (g0scaled g2scaled gibbs_endpoint_linear_costs_eq)
open private tilt_scaling from D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix

/-- The signed row of the lower certificate uses the actual residual R. -/
def signedTiltRow (r : ℝ) (y : Vec3) (k R β : ℝ) : Vec3 :=
  fun i => lowerTilt r y i + upperTilt r y i -
    R / (2 * β) * ((1 - k) * lowerTilt r y i - (1 + k) * upperTilt r y i)

/-- The occupation matrix with the 1/1024 margin and the signed Hellinger row. -/
def schurMatrix (r : ℝ) (y : Vec3) (p k R β : ℝ) :
    Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ :=
  let w := signedTiltRow r y k R β
  fromBlocks
    (fun i j => occupationMatrix r y i j - (∑ l, basis l i * basis l j) / 1024)
    (fun i _ => w i / 2) (fun _ j => w j / 2) (fun _ _ => p / (r - 1) ^ 2)

private theorem schur_quadratic (r : ℝ) (y : Vec3) (p k R β : ℝ)
    (h : Fin 4 → ℝ) (hh : h 3 = 0) (s : ℝ)
    (hPSD : (schurMatrix r y p k R β).PosSemidef) :
    0 ≤ quadratic (occupationMatrix r y) (coordinates h) - (∑ i, h i ^ 2) / 1024 +
      dotProduct (signedTiltRow r y k R β) (coordinates h) * s + p / (r - 1) ^ 2 * s ^ 2 := by
  let ξ := coordinates h
  let w := signedTiltRow r y k R β
  have hquad := hPSD.dotProduct_mulVec_nonneg (Sum.elim ξ (fun _ => s))
  have hgram : quadratic (fun i j => ∑ l, basis l i * basis l j) ξ = ∑ i, h i ^ 2 := by
    norm_num [quadratic, ξ, basis, coordinates, dotProduct, Matrix.mulVec,
      Fin.sum_univ_three, Fin.sum_univ_four, hh, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  change 0 ≤ quadratic (occupationMatrix r y) ξ - (∑ i, h i ^ 2) / 1024 +
    dotProduct w ξ * s + p / (r - 1) ^ 2 * s ^ 2
  rw [← hgram]
  simp only [star_trivial, schurMatrix, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one, Fin.sum_univ_three] at hquad
  simp only [fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr] at hquad
  simp only [quadratic, dotProduct, Matrix.mulVec, Fin.sum_univ_three, w]
  linarith only [hquad]

private theorem schur_loss_le {t p v C u : ℝ} (ht : 0 < t) (hp : 0 < p)
    (hu : t * u = v) (hquad : ∀ s : ℝ, 0 ≤ C + u * s + p / t ^ 2 * s ^ 2) :
    v ^ 2 / (4 * p) ≤ C := by
  have hu' : u = v / t := (eq_div_iff ht.ne').mpr (by linarith only [hu])
  let s := -(t * v) / (2 * p)
  have heval : C + u * s + p / t ^ 2 * s ^ 2 = C - v ^ 2 / (4 * p) := by
    rw [hu']
    dsimp only [s]
    field_simp [ht.ne', hp.ne']
    ring
  have h := hquad s
  rwa [heval, sub_nonneg] at h

set_option maxHeartbeats 800000 in
-- Elaborating the Schur evaluation with the physical spectral coefficients needs extra heartbeats.
/-- The lower spectral tests and the signed occupation block imply the
1/1024 squared displacement margin for every physical frame. The offset
vector is the actual displacement from Gibbs, with its fourth entry zero. -/
theorem normalized_deficit_ge_of_schur {r : ℝ} (U : unitary Mat) (hr : 1 < r)
    (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + h i) (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i) :
    let y := displacement 1 h
    let m := levels r y 0
    let n := levels r y 1
    let q := levels r y 2
    let A := cutEnergy r m n q
    let B := cutBias r m n q
    let Z₀ := lowerCoeff r m n q
    let Z₂ := upperCoeff r n q
    let Zlong := longCoeff r m n q
    let L₀ := matchedMixture A B
    let ell := B 1 / 4
    let L := L₀ + ell
    let P₀ := (A 0 + Z₀ - L₀) / 2
    let P₂ := (A 2 + Z₂ - L₀) / 2
    let p := P₀ + P₂ + B 1 / 2
    let k := (P₀ - P₂) / p
    let G₀ := B 0 / 2 - 2 * P₀
    let G₂ := B 2 / 2 - 2 * P₂
    let Gs := G₀ + G₂
    let R := G₀ - G₂ - k * Gs
    let β := Zlong - k * R
    let A₂₃ := (2 / 3) * (P₀ + P₂)
    let B₂₃ := G₀ - G₂ - (4 / 3) * P₂
    let C₂₃ := (2 / 3) * P₂ + G₂
    m ≤ n → n ≤ q → q ≤ 1 →
    0 ≤ L₀ → L ≤ Z₀ → L ≤ Z₂ → ell ≤ B 0 → ell ≤ B 2 →
    0 < P₀ → 0 < P₂ → L₀ < Zlong →
    0 ≤ p * (P₀ + P₂ - ell - L) - (P₀ - P₂) ^ 2 →
    0 < β → 0 ≤ 4 * A₂₃ * C₂₃ - B₂₃ ^ 2 →
    (schurMatrix r y p k R β).PosSemidef →
    (∑ i, h i ^ 2) / 1024 ≤ normalizedDeficit r U m n q := by
  intro y m n q A B Z₀ Z₂ Zlong L₀ ell L P₀ P₂ p k G₀ G₂ Gs R β A₂₃ B₂₃ C₂₃
    hmn hnq hq1 hL₀ hleft hright hend₀ hend₂ hP₀ hP₂ hlong hstrong hβ hdisc hPSD
  let t := r - 1
  let η := R ^ 2 / (4 * β)
  let ξ := coordinates h
  let w := signedTiltRow r y k R β
  have hrpos : 0 < r := zero_lt_one.trans hr
  have ht : 0 < t := sub_pos.mpr hr
  have hx' : ∀ i, 1 / 2 ≤ gibbsLevels r i + 1 * h i := by simpa only [one_mul] using hx
  have hm : 0 ≤ m := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hx' 0)
  obtain ⟨_, hB, _⟩ := spectral_coefficients_nonneg hr.le hm hmn hnq hq1
  have hp : 0 < p := add_pos_of_pos_of_nonneg (add_pos hP₀ hP₂) (div_nonneg (hB 1) (by norm_num))
  have hphysical := refined_hellinger_deficit_bound U hr.le hm hmn hnq hq1
    hL₀ hleft hright hend₀ hend₂ hP₀ hP₂ hlong hstrong hβ hdisc
  change occupationDeficit r m n q - (max 0 (2 * η - Gs)) ^ 2 / (4 * p) ≤ _ at hphysical
  have hocc := occupation_taylor_lower_bound (d := 1) hr.le (by norm_num) h hh hx' hg
  change (1 : ℝ) ^ 2 * occupationTaylorCoefficient r 1 h ≤
    normalizedDeficit r 1 m n q at hocc
  rw [occupation_deficit_eq hr.le hm (hm.trans hmn) (hm.trans (hmn.trans hnq))] at hocc
  simp only [one_pow, one_mul] at hocc
  obtain ⟨hscale₀, hscale₂⟩ := tilt_scaling hr (d := 1) (by norm_num) h hh
  obtain ⟨htilt₀, htilt₂⟩ := gibbs_endpoint_linear_costs_eq hrpos 1 h hh
  change G₀ = 1 * g0scaled r 1 h at htilt₀
  change G₂ = 1 * g2scaled r 1 h at htilt₂
  have hw₀ : G₀ = t * dotProduct (lowerTilt r y) ξ := by rw [htilt₀, one_mul, hscale₀]
  have hw₂ : G₂ = t * dotProduct (upperTilt r y) ξ := by rw [htilt₂, one_mul, hscale₂]
  have hrow : dotProduct w ξ = dotProduct (lowerTilt r y) ξ + dotProduct (upperTilt r y) ξ -
      R / (2 * β) * ((1 - k) * dotProduct (lowerTilt r y) ξ -
        (1 + k) * dotProduct (upperTilt r y) ξ) := by
    simp only [w, signedTiltRow, dotProduct, Fin.sum_univ_three]
    ring
  have hres : (1 - k) * G₀ - (1 + k) * G₂ = R := by dsimp only [R, Gs]; ring
  have hw : t * dotProduct w ξ = Gs - 2 * η := calc
    _ = (t * dotProduct (lowerTilt r y) ξ + t * dotProduct (upperTilt r y) ξ) -
        R / (2 * β) * ((1 - k) * (t * dotProduct (lowerTilt r y) ξ) -
          (1 + k) * (t * dotProduct (upperTilt r y) ξ)) := by rw [hrow]; ring
    _ = _ := by
      rw [← hw₀, ← hw₂, hres]
      change Gs - R / (2 * β) * R = Gs - 2 * η
      dsimp only [η]
      field_simp [hβ.ne']
      ring
  let v := Gs - 2 * η
  have hschur : v ^ 2 / (4 * p) ≤
      occupationTaylorCoefficient r 1 h - (∑ i, h i ^ 2) / 1024 := by
    apply schur_loss_le ht hp hw
    intro s
    rw [occupationTaylorCoefficient_eq_quadratic hrpos 1 h hh]
    exact schur_quadratic r y p k R β h hh s hPSD
  have hv : 2 * η - Gs = -v := by dsimp only [v]; ring
  have hmax : max 0 (2 * η - Gs) ≤ |v| :=
    max_le (abs_nonneg _) (hv.le.trans (neg_le_abs v))
  have hsq := (sq_le_sq₀ (le_max_left 0 (2 * η - Gs)) (abs_nonneg v)).mpr hmax
  rw [sq_abs] at hsq
  have hloss := div_le_div_of_nonneg_right hsq (show 0 ≤ 4 * p by positivity)
  calc
    _ ≤ occupationTaylorCoefficient r 1 h - v ^ 2 / (4 * p) := le_sub_comm.mp hschur
    _ ≤ occupationDeficit r m n q - (max 0 (2 * η - Gs)) ^ 2 / (4 * p) :=
      sub_le_sub hocc hloss
    _ ≤ _ := hphysical

#print axioms equal_charge_cut_bound
#print axioms refined_hellinger_deficit_bound
#print axioms normalized_deficit_ge_of_schur

end D5.S3.Quantum.Semigroups.WuCubicRefinedHellinger
