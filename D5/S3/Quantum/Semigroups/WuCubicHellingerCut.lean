/- GID: D5/S3/Quantum/Semigroups/WuCubicHellingerCut
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicHellingerCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Hellinger bound for the ordinary-trace two-CAR Wu cubic deficit. -/

import D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! Wu v1 (3.54) at equal caps and exponent three. The endpoint odd masses
give a squared Hellinger bound for the long crossing. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicHellingerCut

open WuCubicDirectedOccupationCap (Mat frameVector oddProbability)
open WuCubicAngularCertificate
open WuCubicSharpLongCrossing (singletonPairWeight_ge_radical)
open private odd_mass_mem from D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing
open private spectral_coefficients_nonneg centered_retained_le from
  D5.S3.Quantum.Semigroups.WuCubicAngularCertificate

private theorem hellinger_le_radical {t s : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (Real.sqrt t - Real.sqrt s) ^ 2 ≤
      (Real.sqrt ((1 - t) * s) - Real.sqrt (t * (1 - s))) ^ 2 := by
  let x := Real.sqrt t
  let y := Real.sqrt s
  let P := Real.sqrt ((1 - t) * s)
  let Q := Real.sqrt (t * (1 - s))
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hts := mul_nonneg ht.1 hs.1
  have hP : P ≤ y :=
    Real.sqrt_le_sqrt (show (1 - t) * s ≤ s by nlinarith only [hts])
  have hQ : Q ≤ x :=
    Real.sqrt_le_sqrt (show t * (1 - s) ≤ t by nlinarith only [hts])
  have hsum : (P + Q) ^ 2 ≤ (x + y) ^ 2 :=
    (sq_le_sq₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (add_nonneg hx hy)).2 ((add_le_add hP hQ).trans_eq (add_comm y x))
  have hdiff : P ^ 2 - Q ^ 2 = y ^ 2 - x ^ 2 := by
    dsimp only [P, Q, x, y]
    rw [Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr ht.2) hs.1),
      Real.sq_sqrt (mul_nonneg ht.1 (sub_nonneg.mpr hs.2)),
      Real.sq_sqrt hs.1, Real.sq_sqrt ht.1]
    ring
  have hprod : (x - y) ^ 2 * (x + y) ^ 2 = (P - Q) ^ 2 * (P + Q) ^ 2 := calc
    _ = (y ^ 2 - x ^ 2) ^ 2 := by ring
    _ = (P ^ 2 - Q ^ 2) ^ 2 := by rw [hdiff]
    _ = _ := by ring
  change (x - y) ^ 2 ≤ (P - Q) ^ 2
  by_contra! hlt
  have hpos : 0 < (x + y) ^ 2 := by
    nlinarith only [hlt, sq_nonneg (P - Q), mul_nonneg hx hy]
  have hlt' := mul_lt_mul_of_pos_right hlt hpos
  rw [hprod] at hlt'
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left hsum (sq_nonneg (P - Q)))) hlt'

/-- The squared difference of the endpoint square roots, in odd-tilt units. -/
theorem long_crossing_ge_hellinger (U : unitary Mat) :
    (Real.sqrt (oddTilt U 0) - Real.sqrt (oddTilt U 3)) ^ 2 / 2 ≤ longCrossing U := by
  have h := (hellinger_le_radical (odd_mass_mem U 0) (odd_mass_mem U 3)).trans
    (singletonPairWeight_ge_radical U 0 3)
  change _ ≤ longCrossing U at h
  have ht : (0 : ℝ) ≤ 2 := by norm_num
  simp only [oddTilt, Real.sqrt_mul ht]
  rw [← mul_sub, mul_pow, Real.sq_sqrt ht]
  linarith only [h]

private theorem matrix_nonneg {a b κ k R η : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hdet : 0 ≤ (1 - k ^ 2) * η ^ 2 + (4 * κ - k * R) * η - R ^ 2 / 4) :
    0 ≤ R * (a - b) / 2 + 2 * κ * (Real.sqrt a - Real.sqrt b) ^ 2 +
      η * (a + b + k * (a - b)) := by
  let A := 2 * κ + R / 2 + η * (1 + k)
  let C := 2 * κ - R / 2 + η * (1 - k)
  let x := Real.sqrt a
  let y := Real.sqrt b
  have hdet_eq : A * C - (2 * κ) ^ 2 =
      (1 - k ^ 2) * η ^ 2 + (4 * κ - k * R) * η - R ^ 2 / 4 := by
    dsimp only [A, C]
    ring
  have hdet' : 0 ≤ A * C - (2 * κ) ^ 2 := by rw [hdet_eq]; exact hdet
  have htrace_eq : A + C = 4 * κ + 2 * η := by dsimp only [A, C]; ring
  have htrace : 0 < A + C := by linarith only [htrace_eq, hκ, hη]
  have hA : 0 < A := by
    by_contra! hA
    have hC : 0 ≤ C := by linarith only [htrace, hA]
    have hprod := mul_nonpos_of_nonpos_of_nonneg hA hC
    have hκsq : 0 < (2 * κ) ^ 2 := by positivity
    linarith only [hdet', hprod, hκsq]
  have hscaled : A * (A * x ^ 2 - 4 * κ * x * y + C * y ^ 2) =
      (A * x - 2 * κ * y) ^ 2 + (A * C - (2 * κ) ^ 2) * y ^ 2 := by ring
  have hquad : 0 ≤ A * x ^ 2 - 4 * κ * x * y + C * y ^ 2 :=
    nonneg_of_mul_nonneg_right (by
      rw [hscaled]
      exact add_nonneg (sq_nonneg _) (mul_nonneg hdet' (sq_nonneg _))) hA
  calc
    0 ≤ A * x ^ 2 - 4 * κ * x * y + C * y ^ 2 := hquad
    _ = R * (x ^ 2 - y ^ 2) / 2 + 2 * κ * (x - y) ^ 2 +
        η * (x ^ 2 + y ^ 2 + k * (x ^ 2 - y ^ 2)) := by
      dsimp only [A, C]
      ring
    _ = _ := by
      have hx : x ^ 2 = a := Real.sq_sqrt ha
      have hy : y ^ 2 = b := Real.sq_sqrt hb
      rw [hx, hy]

private theorem nonneg_quadratic_lower_bound {p z v : ℝ} (hp : 0 < p) (hz : 0 ≤ z) :
    -((max 0 v) ^ 2 / (4 * p)) ≤ p * z ^ 2 / 4 - v * z / 2 := by
  let M := max 0 v
  have hlin := mul_le_mul_of_nonneg_right (le_max_right (0 : ℝ) v) hz
  calc
    -(M ^ 2 / (4 * p)) ≤ p * z ^ 2 / 4 - M * z / 2 := by
      rw [← neg_div]
      apply (div_le_iff₀ (show 0 < 4 * p by positivity)).mpr
      nlinarith only [sq_nonneg (p * z - M)]
    _ ≤ _ := by linarith only [hlin]

/-- On the ordered spectrum `(m,n,q,1)`, the endpoint odd masses and the
matched adjacent cuts give the stated loss from the occupation deficit.
`normalized_deficit_eq_ordinary_trace` identifies the right side with the
ordinary-trace expression for every complex unitary frame. -/
theorem hellinger_deficit_bound {r m n q η : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1) :
    let A := cutEnergy r m n q
    let B := cutBias r m n q
    let Z₀ := lowerCoeff r m n q
    let Z₂ := upperCoeff r n q
    let L₀ := matchedMixture A B
    let κ := longCoeff r m n q / 4
    let P₀ := (A 0 + Z₀ - L₀) / 2
    let P₂ := (A 2 + Z₂ - L₀) / 2
    let p := P₀ + P₂
    let k := (P₀ - P₂) / p
    let j := P₀ * P₂ / p - L₀ / 4
    let G₀ := B 0 / 2 - 2 * P₀
    let G₂ := B 2 / 2 - 2 * P₂
    let gs := G₀ + G₂
    let R := G₀ - G₂ - k * gs
    0 ≤ L₀ → L₀ ≤ Z₀ → L₀ ≤ Z₂ →
    0 < P₀ → 0 < P₂ → 0 < κ → 0 ≤ j → 0 ≤ η →
    0 ≤ (1 - k ^ 2) * η ^ 2 + (4 * κ - k * R) * η - R ^ 2 / 4 →
    occupationDeficit r m n q - (max 0 (2 * η - gs)) ^ 2 / (4 * p) ≤
      normalizedDeficit r U m n q := by
  intro A B Z₀ Z₂ L₀ κ P₀ P₂ p k j G₀ G₂ gs R hL hleft hright hP₀ hP₂ hκ hj hη hdet
  let a := oddTilt U 0
  let b := oddTilt U 3
  let F := a - b
  let z := a + b + k * F
  have ha : 0 ≤ a := mul_nonneg (by norm_num) (odd_mass_mem U 0).1
  have hb : 0 ≤ b := mul_nonneg (by norm_num) (odd_mass_mem U 3).1
  have hp : 0 < p := add_pos hP₀ hP₂
  have hpk : p * k = P₀ - P₂ := by
    dsimp only [k]
    field_simp [hp.ne'] <;> ring
  have hpz : p * z = 2 * (P₀ * a + P₂ * b) := calc
    _ = p * (a + b) + (p * k) * F := by dsimp only [z]; ring
    _ = _ := by rw [hpk]; dsimp only [p, F]; ring
  have hpz_nonneg : 0 ≤ p * z := by
    rw [hpz]
    exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hP₀.le ha) (mul_nonneg hP₂.le hb))
  have hz : 0 ≤ z := (mul_nonneg_iff_of_pos_left hp).mp hpz_nonneg
  have hcollect :
      P₀ * a ^ 2 + P₂ * b ^ 2 + G₀ * a + G₂ * b - L₀ / 4 * F ^ 2 =
        p * z ^ 2 / 4 + gs * z / 2 + R * F / 2 + j * F ^ 2 := by
    dsimp only [z, R, gs, j, k, F]
    field_simp [hp.ne'] <;> (dsimp only [p]; ring)
  obtain ⟨hA, hB, hlong⟩ := spectral_coefficients_nonneg hr hm hmn hnq hq1
  have hcut := matched_cut_bound U A B Z₀ Z₂ 0 hA hB (le_refl 0) hL hleft hright
  dsimp only at hcut
  simp only [zero_div, zero_mul, zero_sub, neg_mul, ← sub_eq_add_neg] at hcut
  change occupationCost A B Z₀ Z₂ +
    (P₀ * a ^ 2 + P₂ * b ^ 2 + G₀ * a + G₂ * b) - L₀ / 4 * F ^ 2 ≤ _ at hcut
  have hcenter := centered_retained_le U hr hm hmn hnq hq1
  change thermalCenter r m n q +
    retainedCost U A B Z₀ Z₂ (longCoeff r m n q) ≤ _ at hcenter
  have hretained : retainedCost U A B Z₀ Z₂ (longCoeff r m n q) =
      retainedCost U A B Z₀ Z₂ 0 + longCoeff r m n q * longCrossing U := by
    simp only [retainedCost, zero_mul, add_zero]
  rw [hretained] at hcenter
  have hcross := mul_le_mul_of_nonneg_left (long_crossing_ge_hellinger U) hlong
  change longCoeff r m n q * ((Real.sqrt a - Real.sqrt b) ^ 2 / 2) ≤ _ at hcross
  have hscale : longCoeff r m n q * ((Real.sqrt a - Real.sqrt b) ^ 2 / 2) =
      2 * κ * (Real.sqrt a - Real.sqrt b) ^ 2 := by dsimp only [κ]; ring
  rw [hscale] at hcross
  have hangular : occupationDeficit r m n q +
      (p * z ^ 2 / 4 + gs * z / 2 + R * F / 2 + 2 * κ * (Real.sqrt a - Real.sqrt b) ^ 2) ≤
        normalizedDeficit r U m n q := by
    change thermalCenter r m n q + occupationCost A B Z₀ Z₂ + _ ≤ _
    linarith only [hcenter, hcut, hcross, hcollect, mul_nonneg hj (sq_nonneg F)]
  have hmatrix := matrix_nonneg ha hb hκ hη hdet
  change 0 ≤ R * F / 2 + 2 * κ * (Real.sqrt a - Real.sqrt b) ^ 2 + η * z at hmatrix
  have hradial := nonneg_quadratic_lower_bound (v := 2 * η - gs) hp hz
  calc
    _ ≤ occupationDeficit r m n q + (p * z ^ 2 / 4 - (2 * η - gs) * z / 2) := by
      simpa only [sub_eq_add_neg] using add_le_add_right hradial (occupationDeficit r m n q)
    _ ≤ _ := by linarith only [hangular, hmatrix]

#print axioms long_crossing_ge_hellinger
#print axioms hellinger_deficit_bound

end D5.S3.Quantum.Semigroups.WuCubicHellingerCut
