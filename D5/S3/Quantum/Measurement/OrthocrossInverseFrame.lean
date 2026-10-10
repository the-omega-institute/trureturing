/- GID: D5/S3/Quantum/Measurement/OrthocrossInverseFrame
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/OrthocrossInverseFrame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A geometric closed form for the inverse orthocross frame. -/

import D5.S3.AnalyticClosure.ComplexPowerDifference
import D5.S3.Quantum.Measurement.OrthocrossGramHalfInteger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.OrthocrossInverseFrame

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Measurement.OrthocrossGramHalfInteger

noncomputable def upperEntry : ℂ := (1 - I) / 2
noncomputable def lowerEntry : ℂ := (1 + I) / 2
noncomputable def scale (d : ℕ) : ℂ := (d : ℂ) - upperEntry
noncomputable def ratio (d : ℕ) : ℂ := ((d : ℂ) - lowerEntry) / scale d
noncomputable def denominator (d : ℕ) : ℂ := lowerEntry - upperEntry * ratio d ^ d
noncomputable def upperConstant (d : ℕ) : ℂ :=
  -(I * upperEntry * ratio d ^ ((d : ℤ) - 2)) / (scale d ^ 2 * denominator d)
noncomputable def diagonalConstant (d : ℕ) : ℂ :=
  1 / scale d - I * upperEntry * ratio d ^ ((d : ℤ) - 1) /
    (scale d ^ 2 * denominator d)
noncomputable def candidate (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  of fun j k => if j = k then diagonalConstant d else
    if j < k then upperConstant d * ratio d ^ ((j.val : ℤ) - (k.val : ℤ) + 1) else
      star (upperConstant d * ratio d ^ ((k.val : ℤ) - (j.val : ℤ) + 1))

private theorem upperEntry_ne_zero : upperEntry ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [upperEntry] at this

private theorem lowerEntry_eq : lowerEntry = I * upperEntry := by
  apply Complex.ext <;> norm_num [upperEntry, lowerEntry]

private theorem scale_ne_zero (d : ℕ) : scale d ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  norm_num [scale, upperEntry] at this

private theorem ratio_eq (d : ℕ) : ratio d = star (scale d) / scale d := by
  simp [ratio, scale, upperEntry, lowerEntry]

/-- The geometric ratio is nonzero. -/
theorem ratio_ne_zero (d : ℕ) : ratio d ≠ 0 := by
  rw [ratio_eq]
  exact div_ne_zero (star_ne_zero.mpr (scale_ne_zero d)) (scale_ne_zero d)

/-- The geometric ratio has unit modulus. -/
theorem norm_ratio (d : ℕ) : ‖ratio d‖ = 1 := by
  rw [ratio_eq, norm_div, norm_star, div_self (norm_ne_zero_iff.mpr (scale_ne_zero d))]

/-- Conjugation inverts the geometric ratio. -/
theorem star_ratio (d : ℕ) : star (ratio d) = (ratio d)⁻¹ := by
  rw [ratio_eq, star_div₀, star_star, inv_div]

private theorem ratio_sub_one (d : ℕ) : ratio d - 1 = -I / scale d := by
  dsimp [ratio]
  rw [div_sub_one (scale_ne_zero d)]
  congr 1
  dsimp [scale, upperEntry, lowerEntry]
  ring

private theorem scale_norm_sq (d : ℕ) :
    ‖scale d‖ ^ 2 = (d : ℝ) ^ 2 - d + 1 / 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [scale, upperEntry, Complex.normSq_apply]
  ring

private theorem norm_ratio_pow_sub_one_le (d n : ℕ) :
    ‖ratio d ^ n - 1‖ ≤ (n : ℝ) * ‖ratio d - 1‖ := by
  simpa using D5.S3.AnalyticClosure.ComplexPowerDifference.norm_pow_sub_pow_le
    (ratio d) 1 n 1 (by norm_num) (by simp [norm_ratio]) (by simp)

/-- The denominator in the geometric inverse formula is nonzero in positive dimension. -/
theorem denominator_ne_zero {d : ℕ} (hd : 0 < d) : denominator d ≠ 0 := by
  intro h
  have hp : ratio d ^ d = I := by
    have he : upperEntry * ratio d ^ d = upperEntry * I := by
      rw [mul_comm upperEntry I, ← lowerEntry_eq]
      exact (sub_eq_zero.mp h).symm
    exact mul_left_cancel₀ upperEntry_ne_zero he
  by_cases h1 : d = 1
  · subst d
    have hi := congrArg Complex.im hp
    norm_num [ratio, scale, upperEntry, lowerEntry, Complex.div_im, Complex.normSq_apply] at hi
  · have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    have hb := norm_ratio_pow_sub_one_le d d
    rw [hp, ratio_sub_one, norm_div, norm_neg, norm_I, mul_one_div] at hb
    have hL : 0 < ‖scale d‖ := norm_pos_iff.mpr (scale_ne_zero d)
    have hb' := (le_div_iff₀ hL).mp hb
    have hn : ‖(I - 1 : ℂ)‖ ^ 2 = 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      norm_num [Complex.normSq_apply]
    have hs : (‖(I - 1 : ℂ)‖ * ‖scale d‖) ^ 2 ≤ (d : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hb' 2
    rw [mul_pow, hn, scale_norm_sq] at hs
    nlinarith

/-- The common upper-triangular coefficient is nonzero. -/
theorem upperConstant_ne_zero {d : ℕ} (hd : 0 < d) : upperConstant d ≠ 0 := by
  dsimp [upperConstant]
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero I_ne_zero upperEntry_ne_zero)
    (zpow_ne_zero _ (ratio_ne_zero d))))
    (mul_ne_zero (pow_ne_zero _ (scale_ne_zero d)) (denominator_ne_zero hd))

/-- The geometric ratio is distinct from one. -/
theorem ratio_ne_one (d : ℕ) : ratio d ≠ 1 := by
  intro h
  have hz : -I / scale d = 0 := by rw [← ratio_sub_one, h, sub_self]
  exact (div_ne_zero (neg_ne_zero.mpr I_ne_zero) (scale_ne_zero d)) hz

private theorem ratio_scale (d : ℕ) : (ratio d - 1) * scale d = -I := by
  rw [ratio_sub_one, div_mul_cancel₀ _ (scale_ne_zero d)]

private theorem entries_sum : upperEntry + lowerEntry = 1 := by
  dsimp [upperEntry, lowerEntry]
  ring

private theorem entries_phase (d : ℕ) :
    upperEntry + lowerEntry * ratio d ^ d = -I * denominator d := by
  rw [denominator, lowerEntry_eq]
  have hi : I ^ 2 = -1 := I_sq
  ring_nf
  simp [hi]
  ring

private noncomputable def scaledEntry (d j k : ℕ) : ℂ :=
  ratio d ^ ((j : ℤ) - (k : ℤ) - 1) *
    (if j ≤ k then -lowerEntry * ratio d ^ d else upperEntry) +
    if j = k then scale d * denominator d else 0

private noncomputable def geometricMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  of fun j k => scaledEntry d j.val k.val / (scale d ^ 2 * denominator d)

private theorem sum_powers_le (d k : ℕ) (hk : k < d) :
    (∑ j : Fin d, if j.val ≤ k then ratio d ^ j.val else 0) =
      ∑ j ∈ Finset.range (k + 1), ratio d ^ j := by
  calc
    _ = ∑ j ∈ Finset.range d, if j ≤ k then ratio d ^ j else 0 :=
      Fin.sum_univ_eq_sum_range (fun n : ℕ => if n ≤ k then ratio d ^ n else 0) d
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega

private theorem scaled_column_sum {d : ℕ} (k : Fin d) :
    ∑ j : Fin d, scaledEntry d j.val k.val =
      I * scale d * ratio d ^ ((d : ℤ) - (k.val : ℤ) - 1) := by
  classical
  let q := ratio d
  let L := scale d
  let δ := denominator d
  have hq := ratio_ne_zero d
  have hp (j : ℕ) : q ^ ((j : ℤ) - (k.val : ℤ) - 1) =
      q ^ (-(k.val : ℤ) - 1) * q ^ j := by
    rw [← zpow_natCast, ← zpow_add₀ hq]
    congr 1
    omega
  have he (j : Fin d) : scaledEntry d j.val k.val =
      q ^ (-(k.val : ℤ) - 1) *
        (upperEntry * q ^ j.val - (upperEntry + lowerEntry * q ^ d) *
          (if j.val ≤ k.val then q ^ j.val else 0)) +
        if j = k then L * δ else 0 := by
    simp only [scaledEntry, hp, q, L, δ, Fin.ext_iff]
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_powers_le d k.val k.isLt]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq (ratio_ne_one d), geom_sum_eq (ratio_ne_one d)]
  change q ^ (-(k.val : ℤ) - 1) *
    (upperEntry * ((q ^ d - 1) / (q - 1)) -
      (upperEntry + lowerEntry * q ^ d) * ((q ^ (k.val + 1) - 1) / (q - 1))) + L * δ = _
  have hphase : upperEntry + lowerEntry * q ^ d = -I * δ := entries_phase d
  have hscale : (q - 1) * L = -I := ratio_scale d
  have hpow : q ^ (-(k.val : ℤ) - 1) * q ^ (k.val + 1) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hq]
    norm_num
  have hpowd : q ^ ((d : ℤ) - (k.val : ℤ) - 1) =
      q ^ (-(k.val : ℤ) - 1) * q ^ d := hp d
  rw [hpowd]
  have hfrac : upperEntry * ((q ^ d - 1) / (q - 1)) -
      (upperEntry + lowerEntry * q ^ d) * ((q ^ (k.val + 1) - 1) / (q - 1)) =
      (upperEntry * (q ^ d - 1) -
        (upperEntry + lowerEntry * q ^ d) * (q ^ (k.val + 1) - 1)) / (q - 1) := by ring
  rw [hfrac]
  apply (mul_right_cancel₀ (sub_ne_zero.mpr (ratio_ne_one d)))
  have hqn : q - 1 ≠ 0 := sub_ne_zero.mpr (ratio_ne_one d)
  rw [add_mul, mul_assoc, div_mul_cancel₀ _ hqn]
  have hi : I * I = -1 := I_mul_I
  linear_combination
    -q ^ (-(k.val : ℤ) - 1) * q ^ (k.val + 1) * hphase +
    (δ - I * q ^ (-(k.val : ℤ) - 1) * q ^ d) * hscale +
    δ * I * hpow + q ^ (-(k.val : ℤ) - 1) * q ^ d * entries_sum +
    q ^ (-(k.val : ℤ) - 1) * q ^ d * hi

private theorem scaledEntry_adjacent (d j k : ℕ) :
    ratio d * scaledEntry d j k - scaledEntry d (j + 1) k =
      scale d * denominator d * ((if j = k then 1 else 0) -
        (if j + 1 = k then 1 else 0)) := by
  have hq := ratio_ne_zero d
  have hp : ratio d ^ (((j + 1 : ℕ) : ℤ) - (k : ℤ) - 1) =
      ratio d * ratio d ^ ((j : ℤ) - (k : ℤ) - 1) := by
    calc
      _ = ratio d ^ (1 + ((j : ℤ) - (k : ℤ) - 1)) := by congr 1; omega
      _ = _ := by rw [zpow_add₀ hq, zpow_one]
  have hdiag : ratio d * scale d * denominator d -
      (upperEntry + lowerEntry * ratio d ^ d) = scale d * denominator d := by
    linear_combination denominator d * ratio_scale d - entries_phase d
  by_cases hj : j = k
  · subst k
    simp only [scaledEntry, le_refl, if_true, show ¬j + 1 ≤ j by omega,
      show ¬j + 1 = j by omega, if_false, Int.sub_self, zero_sub,
      Int.reduceNeg, _root_.zpow_neg_one, sub_self, mul_one, sub_zero]
    rw [show (((j + 1 : ℕ) : ℤ) - (j : ℤ) - 1) = 0 by omega, zpow_zero, one_mul]
    calc
      _ = ratio d * scale d * denominator d - (upperEntry + lowerEntry * ratio d ^ d) := by
        field_simp [hq]
        ring
      _ = _ := hdiag
  · by_cases hj' : j + 1 = k
    · have hjle : j ≤ k := by omega
      have hsle : j + 1 ≤ k := by omega
      dsimp only [scaledEntry]
      rw [hp, if_pos hjle, if_neg hj, if_pos hsle, if_pos hj']
      simp only [hj, hj', if_false, if_true]
      ring
    · have hle : (j ≤ k) = (j + 1 ≤ k) := by apply propext; omega
      simp only [scaledEntry, hj, hj', if_false, hp, hle]
      ring

private theorem frame_row_difference {d : ℕ} (N : Matrix (Fin d) (Fin d) ℂ)
    (j : ℕ) (hj : j + 1 < d) (k : Fin d) :
    (frame (1 : Matrix (Fin d) (Fin d) ℂ) * N) ⟨j, by omega⟩ k -
      (frame (1 : Matrix (Fin d) (Fin d) ℂ) * N) ⟨j + 1, hj⟩ k =
      ((d : ℂ) - lowerEntry) * N ⟨j, by omega⟩ k - scale d * N ⟨j + 1, hj⟩ k := by
  classical
  let x : Fin d := ⟨j, by omega⟩
  let y : Fin d := ⟨j + 1, hj⟩
  let F : Matrix (Fin d) (Fin d) ℂ := frame (1 : Matrix (Fin d) (Fin d) ℂ)
  have hxy : x < y := by simp [x, y]
  have he (p : Fin d) : F x p - F y p =
      (if p = x then (d : ℂ) - lowerEntry else 0) -
        if p = y then scale d else 0 := by
    dsimp only [F]
    rw [frame_one]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply, cross, of_apply]
    by_cases hx : p = x
    · subst p
      simp [hxy.ne, hxy.ne', hxy, not_lt_of_gt hxy, lowerEntry]
    · by_cases hy : p = y
      · subst p
        simp [hxy.ne, hxy.ne', hxy, scale, upperEntry]
      · have hl : (x < p) = (y < p) := by
          apply propext
          simp only [Fin.lt_def, x, y, Fin.ext_iff] at *
          constructor <;> intro h <;> omega
        simp [hx, hy, Ne.symm hx, Ne.symm hy, hl]
  change (∑ p, F x p * N p k) - (∑ p, F y p * N p k) = _
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul, he, sub_mul, ite_mul, zero_mul]
  rw [Finset.sum_sub_distrib]
  simp [x, y]
  ring

private theorem geometric_first_row {d : ℕ} (hd : 0 < d) (k : Fin d) :
    (frame (1 : Matrix (Fin d) (Fin d) ℂ) * geometricMatrix d) ⟨0, hd⟩ k =
      (1 : Matrix (Fin d) (Fin d) ℂ) ⟨0, hd⟩ k := by
  classical
  let z : Fin d := ⟨0, hd⟩
  let F : Matrix (Fin d) (Fin d) ℂ := frame (1 : Matrix (Fin d) (Fin d) ℂ)
  have hden : scale d ^ 2 * denominator d ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (scale_ne_zero d)) (denominator_ne_zero hd)
  have hrow (p : Fin d) : F z p = upperEntry + if p = z then scale d else 0 := by
    dsimp only [F]
    rw [frame_one]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply, cross, of_apply]
    by_cases hp : p = z
    · subst p
      simp [scale]
    · have hzp : z < p := by
        simp only [Fin.lt_def, z, Fin.ext_iff] at *
        omega
      simp [hp, Ne.symm hp, hzp, upperEntry]
  change (∑ p, F z p * geometricMatrix d p k) = _
  simp only [geometricMatrix, of_apply, ← mul_div_assoc]
  rw [← Finset.sum_div]
  apply (div_eq_iff hden).mpr
  simp_rw [hrow, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, scaled_column_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hp : ratio d ^ (-(k.val : ℤ) - 1) * ratio d ^ d =
      ratio d ^ ((d : ℤ) - (k.val : ℤ) - 1) := by
    rw [← zpow_natCast, ← zpow_add₀ (ratio_ne_zero d)]
    congr 1
    omega
  simp only [scaledEntry, z, Fin.val_mk, Nat.zero_le, if_true, Int.natCast_zero, zero_sub,
    mul_neg, mul_assoc, hp, lowerEntry_eq, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> linear_combination -(I * upperEntry * scale d) * hp

private theorem frame_mul_geometricMatrix {d : ℕ} (hd : 0 < d) :
    frame (1 : Matrix (Fin d) (Fin d) ℂ) * geometricMatrix d = 1 := by
  classical
  let A : Matrix (Fin d) (Fin d) ℂ := frame (1 : Matrix (Fin d) (Fin d) ℂ) * geometricMatrix d
  have hden : scale d ^ 2 * denominator d ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (scale_ne_zero d)) (denominator_ne_zero hd)
  have hscale : (d : ℂ) - lowerEntry = ratio d * scale d := by
    rw [ratio, div_mul_cancel₀ _ (scale_ne_zero d)]
  have hdiff (j : ℕ) (hj : j + 1 < d) (k : Fin d) :
      A ⟨j, by omega⟩ k - A ⟨j + 1, hj⟩ k =
        (1 : Matrix (Fin d) (Fin d) ℂ) ⟨j, by omega⟩ k -
          (1 : Matrix (Fin d) (Fin d) ℂ) ⟨j + 1, hj⟩ k := by
    change (frame (1 : Matrix (Fin d) (Fin d) ℂ) * geometricMatrix d) _ k -
      (frame (1 : Matrix (Fin d) (Fin d) ℂ) * geometricMatrix d) _ k = _
    rw [frame_row_difference, hscale]
    simp only [geometricMatrix, of_apply, Fin.val_mk]
    calc
      _ = scale d * (ratio d * scaledEntry d j k.val - scaledEntry d (j + 1) k.val) /
          (scale d ^ 2 * denominator d) := by ring
      _ = scale d * (scale d * denominator d * ((if j = k.val then 1 else 0) -
          (if j + 1 = k.val then 1 else 0))) / (scale d ^ 2 * denominator d) := by
            rw [scaledEntry_adjacent]
      _ = (if j = k.val then 1 else 0) - (if j + 1 = k.val then 1 else 0) := by
        rw [show scale d * (scale d * denominator d *
            ((if j = k.val then 1 else 0) - (if j + 1 = k.val then 1 else 0))) =
            (scale d ^ 2 * denominator d) *
            ((if j = k.val then 1 else 0) - (if j + 1 = k.val then 1 else 0)) by ring]
        exact mul_div_cancel_left₀ _ hden
      _ = _ := by simp only [Matrix.one_apply, Fin.ext_iff, Fin.val_mk]
  ext i k
  have hrows : ∀ j (hj : j < d), A ⟨j, hj⟩ k =
      (1 : Matrix (Fin d) (Fin d) ℂ) ⟨j, hj⟩ k := by
    intro j
    induction j with
    | zero => intro hj; exact geometric_first_row hj k
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hstep := hdiff j hj k
      linear_combination hprev - hstep
  exact hrows i.val i.isLt

private theorem geometric_diagonal {d : ℕ} (hd : 0 < d) (j : Fin d) :
    geometricMatrix d j j = diagonalConstant d := by
  have hq := ratio_ne_zero d
  have hp : (ratio d)⁻¹ * ratio d ^ d = ratio d ^ ((d : ℤ) - 1) := by
    rw [← _root_.zpow_neg_one, ← zpow_natCast, ← zpow_add₀ hq]
    congr 1
  have he : (ratio d)⁻¹ * (-lowerEntry * ratio d ^ d) =
      -lowerEntry * ratio d ^ ((d : ℤ) - 1) := by
    calc
      _ = -lowerEntry * ((ratio d)⁻¹ * ratio d ^ d) := by ring
      _ = _ := by rw [hp]
  simp only [geometricMatrix, of_apply, scaledEntry, le_refl, if_true, sub_self,
    zero_sub, _root_.zpow_neg_one, he, diagonalConstant, ← lowerEntry_eq]
  field_simp [scale_ne_zero d, denominator_ne_zero hd]
  ring

private theorem geometric_upper {d : ℕ} (j k : Fin d) (hjk : j < k) :
    geometricMatrix d j k = upperConstant d * ratio d ^ ((j.val : ℤ) - (k.val : ℤ) + 1) := by
  have hq := ratio_ne_zero d
  have hp : ratio d ^ ((j.val : ℤ) - (k.val : ℤ) - 1) * ratio d ^ d =
      ratio d ^ ((d : ℤ) - 2) * ratio d ^ ((j.val : ℤ) - (k.val : ℤ) + 1) := by
    rw [← zpow_natCast, ← zpow_add₀ hq, ← zpow_add₀ hq]
    congr 1
    omega
  simp only [geometricMatrix, of_apply, scaledEntry, show j.val ≤ k.val from hjk.le,
    if_true, show j.val ≠ k.val from (Fin.ne_iff_vne j k).mp hjk.ne, if_false, add_zero,
    upperConstant, ← lowerEntry_eq]
  calc
    _ = -lowerEntry * (ratio d ^ ((j.val : ℤ) - (k.val : ℤ) - 1) * ratio d ^ d) /
      (scale d ^ 2 * denominator d) := by ring
    _ = _ := by rw [hp]; ring

private theorem geometric_eq_candidate {d : ℕ} (hd : 0 < d) :
    geometricMatrix d = candidate d := by
  have hi : (frame (1 : Matrix (Fin d) (Fin d) ℂ))⁻¹ = geometricMatrix d :=
    inv_eq_right_inv (frame_mul_geometricMatrix hd)
  have hh : (geometricMatrix d).IsHermitian := hi ▸ posDef_one.isHermitian.inv
  ext j k
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · simpa only [candidate, of_apply, if_neg hjk.ne, if_pos hjk] using geometric_upper j k hjk
  · simpa [candidate] using geometric_diagonal hd j
  · rw [← hh.apply j k, geometric_upper k j hkj]
    simp [candidate, hkj.ne', not_lt.mpr hkj.le]

/-- The closed geometric candidate is a right inverse of the standard frame. -/
theorem frame_mul_candidate {d : ℕ} (hd : 0 < d) :
    frame (1 : Matrix (Fin d) (Fin d) ℂ) * candidate d = 1 := by
  rw [← geometric_eq_candidate hd]
  exact frame_mul_geometricMatrix hd

/-- The inverse frame has constant diagonal and geometric triangular entries. -/
theorem inverse_frame_eq {d : ℕ} (hd : 0 < d) :
    (frame (1 : Matrix (Fin d) (Fin d) ℂ))⁻¹ = candidate d := by
  exact inv_eq_right_inv (frame_mul_candidate hd)

open scoped ComplexOrder

/-- The diagonal parameter is a strictly positive real number. -/
theorem diagonalConstant_pos {d : ℕ} (hd : 0 < d) : 0 < diagonalConstant d := by
  have hp := (posDef_one (d := d)).inv.diag_pos (i := (⟨0, hd⟩ : Fin d))
  rw [inverse_frame_eq hd] at hp
  simpa [candidate] using hp

private theorem star_entries : star lowerEntry = upperEntry ∧ star upperEntry = lowerEntry := by
  simp [lowerEntry, upperEntry, sub_eq_add_neg]

private theorem star_denominator (d : ℕ) :
    star (denominator d) = -denominator d * ratio d ^ (-(d : ℤ)) := by
  have hp : ratio d ^ d * ratio d ^ (-(d : ℤ)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (ratio_ne_zero d)]
    simp
  rw [denominator, star_sub, star_mul, star_pow, star_entries.1, star_entries.2,
    star_ratio, inv_pow]
  simp only [← zpow_natCast, ← _root_.zpow_neg]
  simp only [zpow_natCast]
  linear_combination -upperEntry * hp

private theorem star_upperConstant_eq (d : ℕ) :
    star (upperConstant d) = upperEntry / (scale d ^ 2 * denominator d) := by
  have hL : star (scale d) = ratio d * scale d := by
    rw [ratio_eq, div_mul_cancel₀ _ (scale_ne_zero d)]
  have hpow : ratio d ^ 2 * ratio d ^ (-(d : ℤ)) = ratio d ^ ((2 : ℤ) - (d : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ (ratio_ne_zero d)]
    congr 1
  have hD : star (scale d ^ 2 * denominator d) =
      -(scale d ^ 2 * denominator d) * ratio d ^ ((2 : ℤ) - (d : ℤ)) := by
    rw [star_mul, star_pow, hL, star_denominator]
    calc
      _ = -(scale d ^ 2 * denominator d) * (ratio d ^ 2 * ratio d ^ (-(d : ℤ))) := by ring
      _ = _ := by rw [hpow]
  have hN : star (-(I * upperEntry * ratio d ^ ((d : ℤ) - 2))) =
      -upperEntry * ratio d ^ ((2 : ℤ) - (d : ℤ)) := by
    rw [← lowerEntry_eq, star_neg, star_mul, star_entries.1, star_zpow₀, star_ratio,
      _root_.inv_zpow, ← _root_.zpow_neg]
    have he : -((d : ℤ) - 2) = (2 : ℤ) - d := by ring
    rw [he]
    ring
  rw [upperConstant, star_div₀, hD, hN, neg_mul, neg_mul, neg_div_neg_eq]
  exact mul_div_mul_right _ _ (zpow_ne_zero _ (ratio_ne_zero d))

/-- The conjugate coefficient differs by the phase i q^(2-d). -/
theorem upperConstant_phase (d : ℕ) :
    star (upperConstant d) = upperConstant d * I * ratio d ^ ((2 : ℤ) - (d : ℤ)) := by
  rw [star_upperConstant_eq d]
  have hp : ratio d ^ ((d : ℤ) - 2) * ratio d ^ ((2 : ℤ) - (d : ℤ)) = 1 := by
    rw [← zpow_add₀ (ratio_ne_zero d)]
    simp
  have hi := I_mul_I
  dsimp only [upperConstant]
  have he : (-(I * upperEntry * ratio d ^ ((d : ℤ) - 2)) /
      (scale d ^ 2 * denominator d)) * I * ratio d ^ ((2 : ℤ) - (d : ℤ)) =
      (-I * I * upperEntry *
        (ratio d ^ ((d : ℤ) - 2) * ratio d ^ ((2 : ℤ) - (d : ℤ)))) /
          (scale d ^ 2 * denominator d) := by ring
  rw [he, hp]
  simp [hi]

/-- The diagonal-to-upper ratio is a quotient of two short Laurent polynomials. -/
theorem diagonal_div_upperConstant {d : ℕ} (hd : 0 < d) :
    diagonalConstant d / upperConstant d =
      (ratio d - I * ratio d ^ ((2 : ℤ) - (d : ℤ))) / (1 - ratio d) := by
  have hq := ratio_ne_zero d
  have hp : ratio d * ratio d ^ ((d : ℤ) - 2) = ratio d ^ ((d : ℤ) - 1) := by
    calc
      _ = ratio d ^ (1 + ((d : ℤ) - 2)) := by rw [zpow_add₀ hq, zpow_one]
      _ = _ := by congr 1; ring
  have ht : diagonalConstant d = 1 / scale d + ratio d * upperConstant d := by
    dsimp only [diagonalConstant, upperConstant]
    calc
      _ = 1 / scale d - I * upperEntry *
          (ratio d * ratio d ^ ((d : ℤ) - 2)) / (scale d ^ 2 * denominator d) := by rw [hp]
      _ = _ := by ring
  have hrec : ratio d * diagonalConstant d - star (upperConstant d) = 1 / scale d := by
    rw [star_upperConstant_eq d]
    dsimp only [diagonalConstant]
    have hp' : ratio d * ratio d ^ ((d : ℤ) - 1) = ratio d ^ d := by
      calc
        _ = ratio d ^ (1 + ((d : ℤ) - 1)) := by rw [zpow_add₀ hq, zpow_one]
        _ = _ := by simp
    apply (mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 (scale_ne_zero d))
      (denominator_ne_zero hd)))
    field_simp [scale_ne_zero d, denominator_ne_zero hd]
    rw [← lowerEntry_eq]
    have he := entries_phase d
    have hs := ratio_scale d
    linear_combination denominator d * hs - he - lowerEntry * hp'
  apply (div_eq_div_iff (upperConstant_ne_zero hd)
    (sub_ne_zero.mpr (Ne.symm (ratio_ne_one d)))).mpr
  rw [mul_sub]
  have hu := upperConstant_phase d
  linear_combination ht - hrec - hu

private def gaussianNumerator (d : ℕ) : GaussianInt := ⟨(d : ℤ) - 1, -(d : ℤ)⟩
private def gaussianDenominator (d : ℕ) : GaussianInt := ⟨(d : ℤ), 1 - (d : ℤ)⟩

private theorem gaussianDenominator_ne_zero (d : ℕ) : gaussianDenominator d ≠ 0 := by
  intro h
  have hr := congrArg Zsqrtd.re h
  have hi := congrArg Zsqrtd.im h
  simp [gaussianDenominator] at hr hi
  omega

private theorem ratio_gaussian (d : ℕ) :
    ratio d = (gaussianNumerator d : ℂ) / (gaussianDenominator d : ℂ) := by
  have hB : (gaussianDenominator d : ℂ) ≠ 0 := by
    exact fun h => gaussianDenominator_ne_zero d (GaussianInt.toComplex_eq_zero.mp h)
  rw [ratio]
  apply (div_eq_div_iff (scale_ne_zero d) hB).mpr
  apply Complex.ext <;>
    simp [gaussianNumerator, gaussianDenominator, GaussianInt.toComplex_def', scale,
      upperEntry, lowerEntry] <;> ring

private theorem gaussian_coprime (d : ℕ) :
    IsCoprime (gaussianNumerator d) (gaussianDenominator d) := by
  let a := gaussianNumerator d
  let b := gaussianDenominator d
  let i : GaussianInt := ⟨0, 1⟩
  let c : GaussianInt := ((d : ℤ) * ((d : ℤ) - 1) : ℤ)
  refine ⟨star a - i * (b - a) * c, i * (b - a) * c, ?_⟩
  ext <;> simp [a, b, i, c, gaussianNumerator, gaussianDenominator] <;> ring

private theorem gaussianDenominator_norm (d : ℕ) :
    (gaussianDenominator d).norm = 2 * (d : ℤ) ^ 2 - 2 * d + 1 := by
  simp [gaussianDenominator, Zsqrtd.norm]
  ring

private theorem denominator_dvd_leadingCoeff (d : ℕ) (p : Polynomial GaussianInt)
    (hr : p.eval₂ GaussianInt.toComplex (ratio d) = 0) :
    gaussianDenominator d ∣ p.leadingCoeff := by
  open Polynomial in
  have hroot : (p.scaleRoots (gaussianDenominator d)).IsRoot (gaussianNumerator d) := by
    apply isRoot_of_eval₂_map_eq_zero GaussianInt.toComplex_injective
    apply scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero GaussianInt.toComplex_injective
    · simpa only [← ratio_gaussian] using hr
    · exact mem_nonZeroDivisors_of_ne_zero (gaussianDenominator_ne_zero d)
  have hdiv := Polynomial.dvd_term_of_isRoot_of_dvd_terms
    (p := gaussianDenominator d) p.natDegree hroot
  have hterms : ∀ j ≠ p.natDegree,
      gaussianDenominator d ∣ (p.scaleRoots (gaussianDenominator d)).coeff j *
        gaussianNumerator d ^ j := by
    intro j hj
    rw [Polynomial.coeff_scaleRoots]
    by_cases hlt : j < p.natDegree
    · apply dvd_mul_of_dvd_left
      apply dvd_mul_of_dvd_right
      exact dvd_pow_self _ (by omega)
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j)]
  have hlead := hdiv hterms
  simp only [Polynomial.coeff_scaleRoots, tsub_self, pow_zero, mul_one,
    Polynomial.coeff_natDegree] at hlead
  exact (gaussian_coprime d).symm.pow_right.dvd_of_dvd_mul_right hlead

/-- A nonzero Gaussian polynomial with small coefficients cannot vanish at q. -/
theorem polynomial_at_ratio_ne_zero (d : ℕ) (p : Polynomial GaussianInt) (hp : p ≠ 0)
    (hcoeff : ∀ n, (p.coeff n).norm < 2 * (d : ℤ) ^ 2 - 2 * d + 1) :
    p.eval₂ GaussianInt.toComplex (ratio d) ≠ 0 := by
  intro hr
  obtain ⟨c, hc⟩ := denominator_dvd_leadingCoeff d p hr
  have hc0 : c ≠ 0 := by
    intro hz
    exact (Polynomial.leadingCoeff_ne_zero.mpr hp) (by simpa [hz] using hc)
  have hn := GaussianInt.norm_pos.mpr hc0
  have hB := GaussianInt.norm_nonneg (gaussianDenominator d)
  have hbound := hcoeff p.natDegree
  rw [Polynomial.coeff_natDegree, hc, Zsqrtd.norm_mul, ← gaussianDenominator_norm] at hbound
  nlinarith

#print axioms ratio_ne_zero
#print axioms ratio_ne_one
#print axioms norm_ratio
#print axioms star_ratio
#print axioms denominator_ne_zero
#print axioms upperConstant_ne_zero
#print axioms frame_mul_candidate
#print axioms inverse_frame_eq
#print axioms diagonalConstant_pos
#print axioms upperConstant_phase
#print axioms diagonal_div_upperConstant
#print axioms polynomial_at_ratio_ne_zero

end D5.S3.Quantum.Measurement.OrthocrossInverseFrame
