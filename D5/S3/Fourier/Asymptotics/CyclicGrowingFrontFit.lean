/- GID: D5/S3/Fourier/Asymptotics/CyclicGrowingFrontFit
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicGrowingFrontFit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative comparison between the cyclic front moment matrix and its lattice fit. -/

import D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Instances.Matrix

/-! The two front feature columns have a uniform second-order error in the
scaled mesh. Summing with the mass normalization keeps that rate as the window grows. -/

open Finset Matrix Filter
open scoped Topology
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation

namespace D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit

noncomputable section

set_option autoImplicit false

private theorem scaled_sin_sq_error (x u : ℝ) (hu : u ≠ 0) :
    |(1 - Real.cos (x * u) ^ 2) / u ^ 2 - x ^ 2| ≤ x ^ 4 * u ^ 2 / 3 := by
  let z := x * u
  have hs : |Real.sin z - z| ≤ |z| ^ 3 / 6 :=
    abs_sub_comm z (Real.sin z) ▸ Real.abs_sub_sin_le z
  have ht : |Real.sin z + z| ≤ 2 * |z| := calc
    _ ≤ |Real.sin z| + |z| := abs_add_le _ _
    _ ≤ 2 * |z| := by linarith only [Real.abs_sin_le_abs (x := z)]
  have hd : |Real.sin z ^ 2 - z ^ 2| ≤ |z| ^ 4 / 3 := calc
    _ = |Real.sin z - z| * |Real.sin z + z| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (|z| ^ 3 / 6) * (2 * |z|) :=
      mul_le_mul hs ht (abs_nonneg _) (by positivity)
    _ = _ := by ring
  have he : (1 - Real.cos (x * u) ^ 2) / u ^ 2 - x ^ 2 =
      (Real.sin z ^ 2 - z ^ 2) / u ^ 2 := by
    rw [Real.sin_sq]
    dsimp only [z]
    field_simp
  rw [he, abs_div, abs_of_nonneg (sq_nonneg u)]
  refine (div_le_iff₀ (sq_pos_of_ne_zero hu)).mpr (hd.trans_eq ?_)
  rw [(by decide : Even 4).pow_abs]
  dsimp only [z]
  ring

/-- The normalized mass and second-moment features on the lattice. -/
def latticeFeatures (x : ℝ) : Fin 2 → ℝ := ![1, x ^ 2]

/-- The two front features, with the continuous extension at zero mesh. -/
def frontFeatures (u x : ℝ) : Fin 2 → ℝ :=
  ![(1 + Real.cos (x * u)) / 2,
    if u = 0 then x ^ 2 else (1 - Real.cos (x * u) ^ 2) / u ^ 2]

private theorem latticeFeatures_bounds {x : ℝ} (hx : |x| ≤ 1) (i : Fin 2) :
    0 ≤ latticeFeatures x i ∧ latticeFeatures x i ≤ 1 := by
  have hsq := (sq_le_sq₀ (abs_nonneg x) zero_le_one).mpr hx
  rw [sq_abs, one_pow] at hsq
  fin_cases i <;> simp [latticeFeatures, sq_nonneg, hsq]

private theorem frontFeatures_bounds {u x : ℝ} (hx : |x| ≤ 1) (i : Fin 2) :
    0 ≤ frontFeatures u x i ∧ frontFeatures u x i ≤ 1 := by
  fin_cases i
  · change 0 ≤ (1 + Real.cos (x * u)) / 2 ∧ (1 + Real.cos (x * u)) / 2 ≤ 1
    constructor
    · linarith only [Real.neg_one_le_cos (x * u)]
    · linarith only [Real.cos_le_one (x * u)]
  · by_cases hu : u = 0
    · simpa [frontFeatures, latticeFeatures, hu] using
        latticeFeatures_bounds hx (1 : Fin 2)
    · simp [frontFeatures, hu]
      rw [← Real.sin_sq]
      refine ⟨by positivity, (div_le_iff₀ (sq_pos_of_ne_zero hu)).mpr ?_⟩
      have hsin : |Real.sin (x * u)| ≤ |u| := calc
        _ ≤ |x * u| := Real.abs_sin_le_abs
        _ = |x| * |u| := abs_mul x u
        _ ≤ _ := by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hx (abs_nonneg u)
      have hsq := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg u)).mpr hsin
      simpa only [sq_abs, one_mul] using hsq

private theorem frontFeatures_error {u x : ℝ} (hx : |x| ≤ 1) (i : Fin 2) :
    |frontFeatures u x i - latticeFeatures x i| ≤ u ^ 2 / 3 := by
  have hxsq : x ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg x) zero_le_one).mpr hx
  fin_cases i
  · change |(1 + Real.cos (x * u)) / 2 - 1| ≤ u ^ 2 / 3
    have hcos := Real.cos_le_one (x * u)
    rw [abs_of_nonpos (by linarith only [hcos])]
    have hlow := Real.one_sub_sq_div_two_le_cos (x := x * u)
    nlinarith only [hlow, mul_nonneg (sub_nonneg.mpr hxsq) (sq_nonneg u), sq_nonneg u]
  · by_cases hu : u = 0
    · simp [frontFeatures, latticeFeatures, hu]
    · simp [frontFeatures, latticeFeatures, hu]
      refine (scaled_sin_sq_error x u hu).trans ?_
      have hx4 : x ^ 4 ≤ 1 := by
        simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by decide, one_pow] using
          (sq_le_sq₀ (sq_nonneg x) zero_le_one).mpr hxsq
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx4) (sq_nonneg u)]

private theorem pair_feature_error {u x : ℝ} (hx : |x| ≤ 1) (i j : Fin 2) :
    |frontFeatures u x i * frontFeatures u x j -
      latticeFeatures x i * latticeFeatures x j| ≤ 2 * (u ^ 2 / 3) := by
  obtain ⟨hf0, hf1⟩ := frontFeatures_bounds (u := u) hx j
  obtain ⟨hl0, hl1⟩ := latticeFeatures_bounds hx i
  rw [show frontFeatures u x i * frontFeatures u x j -
        latticeFeatures x i * latticeFeatures x j =
      (frontFeatures u x i - latticeFeatures x i) * frontFeatures u x j +
        latticeFeatures x i * (frontFeatures u x j - latticeFeatures x j) by ring]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ (u ^ 2 / 3) * 1 + 1 * (u ^ 2 / 3) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hf0, abs_of_nonneg hl0]
      exact add_le_add (mul_le_mul (frontFeatures_error hx i) hf1 hf0 (by positivity))
        (mul_le_mul hl1 (frontFeatures_error hx j) (abs_nonneg _) zero_le_one)
    _ = _ := by ring

/-- Squared-feature moments, normalized by the half-width of the front window. -/
def frontGram (n : ℕ) (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  (∑ k ∈ latticeInterval n,
    frontFeatures u ((k : ℝ) / n) i * frontFeatures u ((k : ℝ) / n) j) / n

/-- The per-entry perturbation is uniform in the number of front sites. -/
theorem frontGram_sub_le (n : ℕ) (hn : 0 < n) (u : ℝ) (i j : Fin 2) :
    |frontGram n u i j - frontGram n 0 i j| ≤ 2 * u ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hzero (x : ℝ) : frontFeatures 0 x = latticeFeatures x := by
    funext r
    fin_cases r <;> norm_num [frontFeatures, latticeFeatures]
  simp only [frontGram, hzero, ← sub_div, ← sum_sub_distrib,
    abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑ k ∈ latticeInterval n, |frontFeatures u ((k : ℝ) / n) i *
        frontFeatures u ((k : ℝ) / n) j -
        latticeFeatures ((k : ℝ) / n) i * latticeFeatures ((k : ℝ) / n) j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ latticeInterval n, 2 * (u ^ 2 / 3) := by
      apply sum_le_sum
      intro k hk
      have hsq := (sq_le_iff_mem k n).mpr hk
      have hk' : |(k : ℝ)| ≤ n :=
        (sq_le_sq₀ (abs_nonneg _) hnR.le).mp (by simpa only [sq_abs, one_mul] using hsq)
      have hx : |(k : ℝ) / n| ≤ 1 := by
        simpa only [abs_div, abs_of_pos hnR] using (div_le_one hnR).mpr hk'
      exact pair_feature_error hx i j
    _ = (2 * (n : ℝ) + 1) * (2 * (u ^ 2 / 3)) := by
      rw [sum_const, nsmul_eq_mul, card_latticeInterval]
    _ ≤ 2 * u ^ 2 * n := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hone) (sq_nonneg u)]

private theorem frontGram_zero_card (n : ℕ) (hn : 0 < n) : frontGram n 0 0 0 = 2 + (n : ℝ)⁻¹ := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hz (x : ℝ) : frontFeatures 0 x 0 = 1 := by norm_num [frontFeatures]
  simp only [frontGram, hz, mul_one, sum_const, nsmul_eq_mul, card_latticeInterval]
  field_simp

private theorem frontGram_zero_second (n : ℕ) (hn : 0 < n) : frontGram n 0 0 1 =
    (1 + (n : ℝ)⁻¹) * (2 + (n : ℝ)⁻¹) / 3 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h0 (x : ℝ) : frontFeatures 0 x 0 = 1 := by norm_num [frontFeatures]
  have h1 (x : ℝ) : frontFeatures 0 x 1 = x ^ 2 := by simp [frontFeatures]
  simp only [frontGram, h0, h1, one_mul, div_pow, ← sum_div, sum_lattice_square]
  field_simp

private theorem frontGram_zero_fourth (n : ℕ) (hn : 0 < n) : frontGram n 0 1 1 =
    (1 + (n : ℝ)⁻¹) * (2 + (n : ℝ)⁻¹) *
      (3 + 3 * (n : ℝ)⁻¹ - ((n : ℝ)⁻¹) ^ 2) / 15 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 (x : ℝ) : frontFeatures 0 x 1 = x ^ 2 := by simp [frontFeatures]
  simp only [frontGram, h1]
  simp_rw [show ∀ x : ℝ, x ^ 2 * x ^ 2 = x ^ 4 by intro x; ring,
    div_pow, ← sum_div, sum_lattice_fourth]
  field_simp

private theorem frontGram_zero_symmetric (n : ℕ) : frontGram n 0 1 0 = frontGram n 0 0 1 := by
  unfold frontGram
  simp_rw [mul_comm (frontFeatures 0 _ 1)]

/-- The normalized lattice moments have the uniform-window limit. -/
theorem frontGram_zero_tendsto :
    Tendsto (fun n : ℕ => frontGram n 0) atTop
      (𝓝 !![(2 : ℝ), 2/3; 2/3, 2/5]) := by
  have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have h00 : Tendsto (fun n : ℕ => 2 + (n : ℝ)⁻¹) atTop (𝓝 2) := by
    simpa only [add_zero] using hInv.const_add 2
  have h01 : Tendsto (fun n : ℕ =>
      (1 + (n : ℝ)⁻¹) * (2 + (n : ℝ)⁻¹) / 3) atTop (𝓝 (2 / 3)) := by
    simpa only [add_zero, one_mul] using ((hInv.const_add 1).mul (hInv.const_add 2)).div_const 3
  have h11 : Tendsto (fun n : ℕ =>
      (1 + (n : ℝ)⁻¹) * (2 + (n : ℝ)⁻¹) * (3 + 3 * (n : ℝ)⁻¹ - ((n : ℝ)⁻¹) ^ 2) / 15)
      atTop (𝓝 (2 / 5)) := by
    convert (((hInv.const_add 1).mul (hInv.const_add 2)).mul
      (((hInv.const_mul 3).const_add 3).sub (hInv.pow 2))).div_const 15 using 1 <;> norm_num
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_ge_atTop 1
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  fin_cases i <;> fin_cases j
  · apply h00.congr'
    filter_upwards [hpos] with n hn using (frontGram_zero_card n hn).symm
  · apply h01.congr'
    filter_upwards [hpos] with n hn using (frontGram_zero_second n hn).symm
  · apply h01.congr'
    filter_upwards [hpos] with n hn using (frontGram_zero_symmetric n |>.trans (frontGram_zero_second n hn)).symm
  · apply h11.congr'
    filter_upwards [hpos] with n hn using (frontGram_zero_fourth n hn).symm

/-- The exact lattice fit has the prescribed mass and normalized second moment. -/
theorem frontGram_reference_fit (n : ℕ) (hn : 0 < n) :
    let m := (n : ℝ) * (n + 1) / 5
    let t := (n : ℝ) * (n + 1) - 1 / 2
    let Z := normalizer n t
    frontGram n 0 *ᵥ ![n * t / Z, -(n : ℝ) ^ 3 / Z] = ![1, m / (n : ℝ) ^ 2] := by
  intro m t Z
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrad : (n : ℝ) ^ 2 ≤ t := by dsimp [t]; nlinarith only [hn1]
  have hZ : 0 < Z := normalizer_pos n hn hrad
  have hnorm : Z = (2 * (n : ℝ) + 1) * (2 * (n : ℝ) * (n + 1) / 3 - 1 / 2) := by
    rw [show Z = normalizer n t from rfl, normalizer_formula]
    dsimp [t]
    ring
  funext i
  fin_cases i
  · change (frontGram n 0 *ᵥ ![n * t / Z, -(n : ℝ) ^ 3 / Z]) 0 = 1
    rw [mulVec, dotProduct, Fin.sum_univ_two, frontGram_zero_card n hn, frontGram_zero_second n hn]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp only [t]
    field_simp [hnR.ne', hZ.ne']
    rw [hnorm]
    ring
  · change (frontGram n 0 *ᵥ ![n * t / Z, -(n : ℝ) ^ 3 / Z]) 1 = m / (n : ℝ) ^ 2
    rw [mulVec, dotProduct, Fin.sum_univ_two, frontGram_zero_symmetric n,
      frontGram_zero_second n hn, frontGram_zero_fourth n hn]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp only [t, m]
    field_simp [hnR.ne', hZ.ne']
    rw [hnorm]
    ring

end

end D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
