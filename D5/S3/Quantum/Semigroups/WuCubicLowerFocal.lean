/- GID: D5/S3/Quantum/Semigroups/WuCubicLowerFocal
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicLowerFocal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical spectrum and quadratic deficit margin from the lower focal cover. -/

import D5.S3.Quantum.Semigroups.WuCubicLowerCells
import D5.S3.Quantum.Semigroups.WuCubicLowerPartition

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuCubicLowerFocal

open Matrix
open scoped BigOperators Matrix
open WuCubicAngularCertificate (normalizedDeficit)
open WuCubicDirectedOccupationCap (Mat)
open WuCubicHellingerMatrix (displacement levels)
open WuCubicOccupationTaylor (gibbsLevels)
open WuCubicLowerCoefficients (offsets radius tests)
open WuCubicLowerOccupation (lowerMatrix normalized_deficit_ge_of_lower_matrix)
open WuCubicLowerPartition (root tree)
open WuCubicUpperPartition (InBox)
open private padPoint from D5.S3.Quantum.Semigroups.WuCubicUpperScalarCells

theorem root_tests_of_check (hcheck : tree.check root WuCubicLowerCells.check = true)
    {x : Fin 4 → ℝ} (hx : InBox root x) :
    let y := offsets (x 1) (x 2) (x 3)
    (∀ i, 0 < tests (x 0) y i) ∧ (lowerMatrix (x 0) y).PosSemidef := by
  change (∀ i, 0 < tests (x 0) (WuCubicLowerJets.pointOffsets (padPoint x)) i) ∧
    (lowerMatrix (x 0) (WuCubicLowerJets.pointOffsets (padPoint x))).PosSemidef
  exact tree.check_sound root WuCubicLowerCells.check hcheck
    (fun _ _ hc _ hx' => WuCubicLowerCells.check_sound hc hx') hx

private theorem physical_coordinates {r m n q : ℝ}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hm₀ : -(1 / 256) ≤ m - (r ^ 2)⁻¹) (hm₁ : m - (r ^ 2)⁻¹ ≤ 0)
    (hn₀ : -(1 / 256) ≤ n - r⁻¹) (hnq : n ≤ q) (hq₁ : q - r⁻¹ ≤ 1 / 256) :
    ∃ x : Fin 4 → ℝ, InBox root x ∧ x 0 = r ∧
      offsets (x 1) (x 2) (x 3) = displacement 1 ![m - (r ^ 2)⁻¹, n - r⁻¹, q - r⁻¹, 0] := by
  let a := m - (r ^ 2)⁻¹
  let b := n - r⁻¹
  let c := q - r⁻¹
  let cap : ℝ := 1 / 256
  have hbc : b ≤ c := sub_le_sub_right hnq _
  have hcap : b ≤ cap := hbc.trans hq₁
  let t := (c - b) / (cap - b)
  have ht₀ : 0 ≤ t := div_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hcap)
  have ht₁ : t ≤ 1 := by
    by_cases h : cap - b = 0
    · simp [t, h]
    · exact (div_le_one (lt_of_le_of_ne (sub_nonneg.mpr hcap) (Ne.symm h))).mpr
        (sub_le_sub_right hq₁ _)
  have hex : b + (cap - b) * t = c := by
    by_cases h : cap - b = 0
    · simp only [h, zero_mul, add_zero]
      have hc : c ≤ cap := hq₁
      exact le_antisymm hbc (hc.trans (sub_eq_zero.mp h).le)
    · dsimp only [t]
      field_simp [h]
      ring
  let x : Fin 4 → ℝ := ![r, a, b, t]
  refine ⟨x, ?_, rfl, ?_⟩
  · change ∀ i, ((root i).1 : ℝ) ≤ x i ∧ x i ≤ ((root i).2 : ℝ)
    intro i
    fin_cases i
    · norm_num [root, x]
      exact ⟨hr₀, hr₁⟩
    · norm_num [root, x]
      exact ⟨hm₀, hm₁⟩
    · norm_num [root, x]
      exact ⟨hn₀, hcap⟩
    · norm_num [root, x]
      exact ⟨ht₀, ht₁⟩
  · have hc : (radius : ℝ) = cap := by norm_num [radius, cap]
    funext i
    fin_cases i
    · change a = 1 * a
      rw [one_mul]
    · change b = 1 * b
      rw [one_mul]
    · change b + ((radius : ℝ) - b) * t = 1 * c
      rw [hc, one_mul]
      exact hex

private theorem spectral_domain {r m n q : ℝ}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hm₀ : -(1 / 256) ≤ m - (r ^ 2)⁻¹) (hm₁ : m - (r ^ 2)⁻¹ ≤ 0)
    (hn₀ : -(1 / 256) ≤ n - r⁻¹) (hnq : n ≤ q) (hq₁ : q - r⁻¹ ≤ 1 / 256) :
    let h : Fin 4 → ℝ := ![m - (r ^ 2)⁻¹, n - r⁻¹, q - r⁻¹, 0]
    1 < r ∧ m ≤ n ∧ q ≤ 1 ∧ (∀ i, 1 / 2 ≤ gibbsLevels r i) ∧
      (∀ i, 1 / 2 ≤ gibbsLevels r i + h i) := by
  intro h
  have hr : 1 < r := (by norm_num : (1 : ℝ) < 1049 / 1000).trans_le hr₀
  have hrp : 0 < r := zero_lt_one.trans hr
  have hsq : r ^ 2 ≤ (6 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ hrp.le hr₁ 2
  have hg₀ : ((6 / 5 : ℝ) ^ 2)⁻¹ ≤ (r ^ 2)⁻¹ :=
    (inv_le_inv₀ (by norm_num : 0 < (6 / 5 : ℝ) ^ 2) (pow_pos hrp 2)).mpr hsq
  have hg₁ : (6 / 5 : ℝ)⁻¹ ≤ r⁻¹ :=
    (inv_le_inv₀ (by norm_num : 0 < (6 / 5 : ℝ)) hrp).mpr hr₁
  have hg₁' : r⁻¹ ≤ (1049 / 1000 : ℝ)⁻¹ :=
    (inv_le_inv₀ hrp (by norm_num : 0 < (1049 / 1000 : ℝ))).mpr hr₀
  have hgap : (1 / 256 : ℝ) ≤ r⁻¹ - (r ^ 2)⁻¹ := by
    rw [show r⁻¹ - (r ^ 2)⁻¹ = (r - 1) / r ^ 2 by
      field_simp [hrp.ne'] <;> ring]
    exact (le_div_iff₀ (pow_pos hrp _)).mpr (by nlinarith only [hsq, hr₀])
  norm_num at hg₀ hg₁ hg₁'
  have hm : 1 / 2 ≤ m := by linarith only [hg₀, hm₀]
  have hn : 1 / 2 ≤ n := by nlinarith only [hg₁, hn₀]
  refine ⟨hr, by linarith only [hgap, hm₁, hn₀], by nlinarith only [hg₁', hq₁], ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [gibbsLevels] <;> nlinarith only [hg₀, hg₁]
  · intro i
    fin_cases i
    · change 1 / 2 ≤ (r ^ 2)⁻¹ + (m - (r ^ 2)⁻¹)
      linarith only [hm]
    · change 1 / 2 ≤ r⁻¹ + (n - r⁻¹)
      linarith only [hn]
    · change 1 / 2 ≤ r⁻¹ + (q - r⁻¹)
      linarith only [hn, hnq]
    · norm_num [gibbsLevels, h]

theorem normalized_deficit_ge_of_check (hcheck : tree.check root WuCubicLowerCells.check = true)
    (U : unitary Mat) {r m n q : ℝ}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hm₀ : -(1 / 256) ≤ m - (r ^ 2)⁻¹) (hm₁ : m - (r ^ 2)⁻¹ ≤ 0)
    (hn₀ : -(1 / 256) ≤ n - r⁻¹) (hnq : n ≤ q) (hq₁ : q - r⁻¹ ≤ 1 / 256) :
    ((m - (r ^ 2)⁻¹) ^ 2 + (n - r⁻¹) ^ 2 + (q - r⁻¹) ^ 2) / 1024 ≤
      normalizedDeficit r U m n q := by
  obtain ⟨x, hx, hxr, hxy⟩ := physical_coordinates hr₀ hr₁ hm₀ hm₁ hn₀ hnq hq₁
  obtain ⟨hr, hmn, hq, hg, hlevels⟩ := spectral_domain hr₀ hr₁ hm₀ hm₁ hn₀ hnq hq₁
  let h : Fin 4 → ℝ := ![m - (r ^ 2)⁻¹, n - r⁻¹, q - r⁻¹, 0]
  let y := displacement 1 h
  have hm' : levels r y 0 = m := by
    change (r ^ 2)⁻¹ + 1 * (m - (r ^ 2)⁻¹) = m
    ring
  have hn' : levels r y 1 = n := by
    change r⁻¹ + 1 * (n - r⁻¹) = n
    ring
  have hq' : levels r y 2 = q := by
    change r⁻¹ + 1 * (q - r⁻¹) = q
    ring
  obtain ⟨htests, hmatrix⟩ := root_tests_of_check hcheck hx
  change (∀ i, 0 < tests (x 0) (offsets (x 1) (x 2) (x 3)) i) at htests
  change (lowerMatrix (x 0) (offsets (x 1) (x 2) (x 3))).PosSemidef at hmatrix
  rw [hxr, hxy] at htests hmatrix
  have hh : h 3 = 0 := rfl
  have H := normalized_deficit_ge_of_lower_matrix U hr h hh hlevels hg
  change levels r y 0 ≤ levels r y 1 → levels r y 1 ≤ levels r y 2 → levels r y 2 ≤ 1 →
    (∀ i, 0 < tests r y i) → (lowerMatrix r y).PosSemidef →
    (∑ i, h i ^ 2) / 1024 ≤ normalizedDeficit r U (levels r y 0) (levels r y 1) (levels r y 2) at H
  rw [hm', hn', hq'] at H
  simpa [Fin.sum_univ_four, h] using H hmn hnq hq htests hmatrix

end D5.S3.Quantum.Semigroups.WuCubicLowerFocal
