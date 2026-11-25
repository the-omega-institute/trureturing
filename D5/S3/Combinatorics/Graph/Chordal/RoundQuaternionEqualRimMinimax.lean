/- GID: D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionEqualRimMinimax
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/RoundQuaternionEqualRimMinimax
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact defect and optimal fit of cyclic equal-rim unit-quaternion gains. -/

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The cyclic rim on four vertices has an exact minimax radius at every angle.
The ratio of this radius to the triangle defect is maximal at the quarter turn. -/

noncomputable section

open Real
open scoped InnerProductSpace Quaternion

namespace RoundQuaternionEqualRimMinimax

/-- The maximum principal angle of a spoke triangle and the cyclic rim triangle. -/
def equalRimDefect (a : ℝ) : ℝ :=
  if a ≤ π / 3 then 3 * a else if a ≤ π / 2 then 2 * π - 3 * a else a

private def rimEigenvalue (a : ℝ) : ℝ := cos (a - 2 * π / 3)

private def optimalScore (a : ℝ) : ℝ :=
  let l := rimEigenvalue a
  let d := l - cos a
  if 0 < d then (-1 + √(1 + 4 * l * d)) / (2 * d) else l

/-- The sharp radius as a function of the common rim angle. -/
def equalRimOptRadius (a : ℝ) : ℝ :=
  if a ≤ π / 3 then a else arccos (optimalScore a)

private theorem defect_eq_max (a : ℝ) (ha : a ∈ Set.Icc 0 π) :
    equalRimDefect a = max a (arccos (cos (3 * a))) := by
  by_cases h₁ : a ≤ π / 3
  · rw [equalRimDefect, if_pos h₁, arccos_cos (by linarith [ha.1]) (by linarith),
      max_eq_right (by linarith [ha.1])]
  rw [equalRimDefect, if_neg h₁]
  by_cases h₂ : a ≤ π / 2
  · rw [if_pos h₂, ← cos_two_pi_sub, arccos_cos (by linarith [pi_pos])
      (by linarith), max_eq_right (by linarith)]
  rw [if_neg h₂]
  apply (max_eq_left _).symm
  rcases le_or_gt a (2 * π / 3) with h₃ | h₃
  · rw [← cos_two_pi_sub, arccos_cos (by linarith) (by linarith [pi_pos])]
    linarith
  · rw [show cos (3 * a) = cos (3 * a - 2 * π) by
        rw [← cos_add_two_pi (3 * a - 2 * π)]
        congr 1 <;> ring,
      arccos_cos (by linarith) (by linarith [ha.2])]
    linarith [ha.2]

private theorem rim_eigenvalue_formula (a : ℝ) :
    rimEigenvalue a = -cos a / 2 + √3 / 2 * sin a := by
  have hc : cos (2 * π / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  have hs : sin (2 * π / 3) = √3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, sin_pi_sub, sin_pi_div_three]
  rw [rimEigenvalue, cos_sub, hc, hs]
  ring

private theorem eigenvalue_gap (a : ℝ) :
    rimEigenvalue a - cos a = √3 * sin (a - π / 3) := by
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  rw [rim_eigenvalue_formula, sin_sub, cos_pi_div_three, sin_pi_div_three]
  nlinarith

private theorem eigenvalue_le_cos {a : ℝ} (ha : 0 ≤ a) (h : a ≤ π / 3) :
    rimEigenvalue a ≤ cos a := by
  have hs : 0 ≤ sin (π / 3 - a) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  rw [show π / 3 - a = -(a - π / 3) by ring, sin_neg] at hs
  linarith [eigenvalue_gap a, mul_nonpos_of_nonneg_of_nonpos
    (sqrt_nonneg 3) (show sin (a - π / 3) ≤ 0 by linarith)]

private theorem cos_lt_eigenvalue {a : ℝ} (h : π / 3 < a) (ha : a ≤ π) :
    cos a < rimEigenvalue a := by
  have hs : 0 < sin (a - π / 3) :=
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  linarith [eigenvalue_gap a, mul_pos (sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)) hs]

private theorem eigenvalue_pos {a : ℝ} (h : π / 3 ≤ a) (ha : a ≤ π) :
    0 < rimEigenvalue a := by
  have hx : |a - 2 * π / 3| ≤ π / 3 := abs_le.2 ⟨by linarith, by linarith⟩
  have hc := cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (a - 2 * π / 3))
    (show π / 3 ≤ π by linarith [pi_pos]) hx
  rw [cos_abs, cos_pi_div_three] at hc
  unfold rimEigenvalue
  linarith

private theorem optimal_score_spec {a : ℝ} (h : π / 3 < a) (ha : a ≤ π) :
    0 < optimalScore a ∧ optimalScore a ≤ 1 ∧
      (rimEigenvalue a - cos a) * optimalScore a ^ 2 + optimalScore a = rimEigenvalue a := by
  let l := rimEigenvalue a
  let d := l - cos a
  let s := √(1 + 4 * l * d)
  have hd : 0 < d := sub_pos.2 (cos_lt_eigenvalue h ha)
  have hl : 0 < l := eigenvalue_pos h.le ha
  have hld := mul_pos hl hd
  have hsq : s ^ 2 = 1 + 4 * l * d := sq_sqrt (by linarith)
  have hs : 1 < s := by
    by_contra! hs
    have hs₀ : 0 ≤ s := sqrt_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.2 hs) (show 0 ≤ s + 1 by linarith)]
  have ht : optimalScore a = (s - 1) / (2 * d) := by
    unfold optimalScore
    dsimp only
    rw [if_pos hd]
    congr 1 <;> ring
  have htpos : 0 < optimalScore a := by rw [ht]; positivity
  have hroot : d * optimalScore a ^ 2 + optimalScore a = l := by
    rw [ht]
    field_simp [ne_of_gt hd]
    nlinarith
  refine ⟨htpos, ?_, hroot⟩
  by_contra! ht
  have hsq₁ : 1 ≤ optimalScore a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ht.le) (show 0 ≤ optimalScore a + 1 by linarith)]
  have hlow := mul_le_mul_of_nonneg_left hsq₁ hd.le
  have hc : cos a ≤ 1 := cos_le_one a
  dsimp [d] at hlow hroot
  linarith

private theorem score_le_optimal {a u : ℝ} (h : π / 3 < a) (ha : a ≤ π)
    (hu : u ≤ rimEigenvalue a - (rimEigenvalue a - cos a) * u ^ 2) :
    u ≤ optimalScore a := by
  obtain ⟨ht, _, hroot⟩ := optimal_score_spec h ha
  by_contra! hlt
  have hsq : optimalScore a ^ 2 ≤ u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hlt.le) (show 0 ≤ u + optimalScore a by linarith)]
  have hd := sub_pos.2 (cos_lt_eigenvalue h ha)
  linarith [mul_le_mul_of_nonneg_left hsq hd.le]

private theorem score_unique {a u : ℝ} (h : π / 3 < a) (ha : a ≤ π) (hu : 0 < u)
    (he : (rimEigenvalue a - cos a) * u ^ 2 + u = rimEigenvalue a) :
    u = optimalScore a := by
  apply le_antisymm (score_le_optimal h ha (by linarith))
  obtain ⟨_, _, hroot⟩ := optimal_score_spec h ha
  by_contra! hlt
  have hsq : u ^ 2 ≤ optimalScore a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hlt.le) (show 0 ≤ u + optimalScore a by linarith)]
  have hd := sub_pos.2 (cos_lt_eigenvalue h ha)
  linarith [mul_le_mul_of_nonneg_left hsq hd.le]

private theorem arccos_cos_mul_convex {q : ℝ} (hq : 0 ≤ q) (hq₁ : q < 1) :
    ConvexOn ℝ (Set.Icc 0 (π / 2)) (fun s => arccos (q * cos s)) := by
  let d : ℝ → ℝ := fun s => 1 - (q * cos s) ^ 2
  let f : ℝ → ℝ := fun s => arccos (q * cos s)
  let f' : ℝ → ℝ := fun s => q * sin s / √(d s)
  have hbound (s : ℝ) : |q * cos s| < 1 := by
    rw [abs_mul, abs_of_nonneg hq]
    exact (mul_le_mul_of_nonneg_left (abs_cos_le_one s) hq).trans_lt (by simpa using hq₁)
  have hpos (s : ℝ) : 0 < d s := by
    have hh := abs_lt.1 (hbound s)
    dsimp [d]
    nlinarith [mul_pos (sub_pos.2 hh.2) (show 0 < 1 + q * cos s by linarith)]
  have hf (s : ℝ) : HasDerivAt f (f' s) s := by
    have hh := abs_lt.1 (hbound s)
    have hh' := (hasDerivAt_cos s).const_mul q
    convert (hasDerivAt_arccos (ne_of_gt hh.1) (ne_of_lt hh.2)).comp s hh' using 1
    dsimp [f', d]
    ring
  have hf' (s : ℝ) :
      HasDerivAt f' (q * (1 - q ^ 2) * cos s / (√(d s)) ^ 3) s := by
    have hcos := (hasDerivAt_cos s).const_mul q
    have hs := ((hcos.pow 2).const_sub 1).sqrt (ne_of_gt (hpos s))
    have hr := ((hasDerivAt_sin s).const_mul q).div hs (ne_of_gt (sqrt_pos.2 (hpos s)))
    convert hr using 1
    have hss : (√(d s)) ^ 2 = d s := sq_sqrt (hpos s).le
    have hsn := sin_sq_add_cos_sq s
    change q * (1 - q ^ 2) * cos s / (√(d s)) ^ 3 =
      (q * cos s * √(d s) -
        q * sin s * ((-(2 * (q * cos s) ^ (2 - 1) * (q * -sin s))) / (2 * √(d s)))) /
        (√(d s)) ^ 2
    field_simp [ne_of_gt (sqrt_pos.2 (hpos s))]
    linear_combination
      q * cos s * (√(d s)) ^ 2 * (hss.trans (show d s = 1 - (q * cos s) ^ 2 from rfl)).symm +
      q ^ 3 * cos s * (√(d s)) ^ 2 * hsn.symm
  have hderiv : deriv f = f' := funext (fun s => (hf s).deriv)
  refine convexOn_of_deriv2_nonneg (convex_Icc 0 _) (by
      exact (continuous_arccos.comp (continuous_const.mul continuous_cos)).continuousOn)
    (fun s _ => (hf s).differentiableAt.differentiableWithinAt) ?_ ?_
  · rw [hderiv]
    exact fun s _ => (hf' s).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [Function.iterate_succ_apply', Function.iterate_one, hderiv, (hf' s).deriv]
    have hs' := interior_subset hs
    have hcos : 0 ≤ cos s := cos_nonneg_of_mem_Icc
      ⟨by linarith [hs'.1, pi_pos], hs'.2⟩
    have hq₂ : 0 ≤ 1 - q ^ 2 := by nlinarith [mul_nonneg hq hq₁.le]
    positivity

private theorem imaginary_unit_sq (I : ℍ[ℝ]) (hI : I.re = 0) (hN : ‖I‖ = 1) :
    I * I = -1 := by
  simpa [pow_two, Quaternion.normSq_eq_norm_mul_self, hN] using
    Quaternion.sq_eq_neg_normSq.mpr hI

private theorem skew_inner (I x y : ℍ[ℝ]) (hI : I.re = 0) (hN : ‖I‖ = 1) :
    ⟪x * I, y⟫_ℝ = -⟪y * I, x⟫_ℝ := by
  let J : ℍ[ℝ] →ₗᵢ[ℝ] ℍ[ℝ] :=
    { toLinearMap := LinearMap.mulRight ℝ I
      norm_map' := fun v => by simp [LinearMap.mulRight_apply, norm_mul, hN] }
  calc
    ⟪x * I, y⟫_ℝ = ⟪(x * I) * I, y * I⟫_ℝ := (J.inner_map_map (x * I) y).symm
    _ = -⟪y * I, x⟫_ℝ := by
      rw [mul_assoc, imaginary_unit_sq I hI hN, mul_neg, mul_one, inner_neg_left, real_inner_comm]

private theorem cyclic_skew (I x y z : ℍ[ℝ]) (hI : I.re = 0) (hN : ‖I‖ = 1) :
    let E := (1 / √2 : ℝ) • (x - y)
    let H := (1 / √6 : ℝ) • (x + y - (2 : ℝ) • z)
    ⟪x * I, y⟫_ℝ + ⟪y * I, z⟫_ℝ + ⟪z * I, x⟫_ℝ = √3 * ⟪E * I, H⟫_ℝ := by
  have hd (v : ℍ[ℝ]) : ⟪v * I, v⟫_ℝ = 0 := by linarith [skew_inner I v v hI hN]
  have hs : √2 * √6 = 2 * √3 := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hcoeff : √3 * (1 / √6 * (1 / √2)) = (1 / 2 : ℝ) := by
    rw [div_mul_div_comm, one_mul, mul_comm (√6), hs]
    field_simp
  dsimp only
  simp only [smul_mul_assoc, sub_mul, real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, ← mul_assoc, mul_assoc (√3), hcoeff]
  simp only [inner_sub_left, inner_sub_right, inner_add_right, real_inner_smul_right, hd,
    skew_inner I y x hI hN, skew_inner I x z hI hN]
  ring

private theorem rim_average (I x y z : ℍ[ℝ]) (a : ℝ) (hI : I.re = 0) (hN : ‖I‖ = 1)
    (ha : a ∈ Set.Icc 0 π) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    let m := (1 / 3 : ℝ) • (x + y + z)
    let A := (cos a : ℍ[ℝ]) + sin a • I
    (⟪x * A, y⟫_ℝ + ⟪y * A, z⟫_ℝ + ⟪z * A, x⟫_ℝ) / 3 ≤
      cos a * ‖m‖ ^ 2 + rimEigenvalue a * (1 - ‖m‖ ^ 2) := by
  let m := (1 / 3 : ℝ) • (x + y + z)
  let E := (1 / √2 : ℝ) • (x - y)
  let H := (1 / √6 : ℝ) • (x + y - (2 : ℝ) • z)
  have hmean :
      ‖m‖ ^ 2 = (3 + 2 * (⟪x, y⟫_ℝ + ⟪y, z⟫_ℝ + ⟪z, x⟫_ℝ)) / 9 := by
    simp only [m, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← real_inner_self_eq_norm_sq,
      inner_add_left, inner_add_right]
    simp only [real_inner_self_eq_norm_sq, hx, hy, hz, one_pow]
    rw [real_inner_comm y x, real_inner_comm x z, real_inner_comm z y]
    ring
  have henergy : ‖E‖ ^ 2 + ‖H‖ ^ 2 = 3 * (1 - ‖m‖ ^ 2) := by
    rw [hmean]
    simp only [E, H, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, one_pow,
      sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_sqrt (by norm_num : (0 : ℝ) ≤ 6),
      ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_self_eq_norm_sq, hx, hy, hz, one_pow]
    rw [real_inner_comm y x, real_inner_comm x z, real_inner_comm z y]
    ring
  have hsym :
      (⟪x, y⟫_ℝ + ⟪y, z⟫_ℝ + ⟪z, x⟫_ℝ) / 3 = ‖m‖ ^ 2 - (1 - ‖m‖ ^ 2) / 2 := by
    linarith
  have hj : ⟪E * I, H⟫_ℝ ≤ ‖E‖ * ‖H‖ := by
    simpa [norm_mul, hN] using real_inner_le_norm (E * I) H
  have hskew : (⟪x * I, y⟫_ℝ + ⟪y * I, z⟫_ℝ + ⟪z * I, x⟫_ℝ) / 3 ≤
      √3 / 2 * (1 - ‖m‖ ^ 2) := by
    rw [cyclic_skew I x y z hI hN]
    have hprod : 2 * ⟪E * I, H⟫_ℝ ≤ ‖E‖ ^ 2 + ‖H‖ ^ 2 :=
      by nlinarith [sq_nonneg (‖E‖ - ‖H‖)]
    have hscaled := mul_le_mul_of_nonneg_left hprod (sqrt_nonneg 3)
    rw [henergy] at hscaled
    linarith
  change _ ≤ cos a * ‖m‖ ^ 2 + _
  have hexpand (u v : ℍ[ℝ]) :
      ⟪u * ((cos a : ℍ[ℝ]) + sin a • I), v⟫_ℝ =
        cos a * ⟪u, v⟫_ℝ + sin a * ⟪u * I, v⟫_ℝ := by
    rw [mul_add, Quaternion.mul_coe_eq_smul, mul_smul_comm,
      inner_add_left, real_inner_smul_left, real_inner_smul_left]
  simp only [hexpand]
  rw [rim_eigenvalue_formula]
  have hb := mul_le_mul_of_nonneg_left hskew (sin_nonneg_of_nonneg_of_le_pi ha.1 ha.2)
  linear_combination hb + cos a * hsym

private def angleQuat (I : ℍ[ℝ]) (a : ℝ) : ℍ[ℝ] := (cos a : ℍ[ℝ]) + sin a • I

private theorem angle_quat_mul (I : ℍ[ℝ]) (hI : I.re = 0) (hN : ‖I‖ = 1) (a b : ℝ) :
    angleQuat I a * angleQuat I b = angleQuat I (a + b) := by
  simp only [angleQuat, add_mul, mul_add, mul_smul_comm, smul_mul_assoc,
    imaginary_unit_sq I hI hN, smul_neg, smul_smul, ← Quaternion.coe_mul_eq_smul,
    ← Quaternion.coe_mul, ← Quaternion.coe_neg, ← Quaternion.coe_add, cos_add, sin_add,
    add_smul]
  rw [Quaternion.coe_mul_eq_smul, Quaternion.mul_coe_eq_smul]
  module

private theorem norm_angle_quat (I : ℍ[ℝ]) (hI : I.re = 0) (hN : ‖I‖ = 1) (a : ℝ) :
    ‖angleQuat I a‖ = 1 := by
  have hl : ⟪(cos a : ℍ[ℝ]), sin a • I⟫_ℝ = 0 := by
    simp [Quaternion.inner_def, Quaternion.re_mul, hI]
  have hsq : ‖angleQuat I a‖ ^ 2 = 1 := by
    simp only [angleQuat, norm_add_sq_real, hl, mul_zero, add_zero, norm_smul,
      Quaternion.norm_coe, hN, mul_one, Real.norm_eq_abs, sq_abs]
    exact cos_sq_add_sin_sq a
  exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num : 0 ≤ (1 : ℝ))).1 (by simpa using hsq)

private def angleGain (I : ℍ[ℝ]) (hI : I.re = 0) (hN : ‖I‖ = 1) (a : ℝ) :
    unitary ℍ[ℝ] :=
  ⟨angleQuat I a, by
    rw [← SetLike.mem_coe, CStarRing.coe_unitary_eq_sphere, mem_sphere_zero_iff_norm]
    exact norm_angle_quat I hI hN a⟩

/-- The cyclic rim has a common forward gain and identity spokes. -/
def equalRimGains (I : ℍ[ℝ]) (hI : I.re = 0) (hN : ‖I‖ = 1) (a : ℝ) :
    Fin 4 → Fin 4 → unitary ℍ[ℝ] :=
  let A := angleGain I hI hN a
  ![![1, 1, 1, 1], ![1, 1, A, A⁻¹], ![1, A⁻¹, 1, A], ![1, A, A⁻¹, 1]]

private def quarterScore : ℝ := 1 / √3

private theorem quarter_score_pos : 0 < quarterScore := by
  unfold quarterScore
  positivity

private theorem quarter_score_sq : quarterScore ^ 2 = 1 / 3 := by
  simp [quarterScore, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem quarter_score_lt_one : quarterScore < 1 := by
  have h := quarter_score_pos
  by_contra! hq
  nlinarith [quarter_score_sq, mul_nonneg (sub_nonneg.2 hq) (show 0 ≤ quarterScore + 1 by linarith)]

private theorem latitude_rim_score (a : ℝ) :
    cos a * quarterScore ^ 2 + rimEigenvalue a * (1 - quarterScore ^ 2) =
      quarterScore * sin a := by
  have hs : √3 / 3 = quarterScore := by
    unfold quarterScore
    field_simp [ne_of_gt (sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [quarter_score_sq, rim_eigenvalue_formula, ← hs]
  ring

private theorem radius_le_fixed_latitude {a : ℝ} (h : π / 3 < a) (ha : a ≤ π) :
    equalRimOptRadius a ≤ arccos (quarterScore * sin a) := by
  have ha₀ : 0 ≤ a := by linarith [pi_pos]
  let u := quarterScore * sin a
  have hu₀ : 0 ≤ u := mul_nonneg quarter_score_pos.le (sin_nonneg_of_nonneg_of_le_pi ha₀ ha)
  have hu₁ : u ≤ quarterScore := by
    simpa [u] using mul_le_mul_of_nonneg_left (sin_le_one a) quarter_score_pos.le
  have hd := (cos_lt_eigenvalue h ha).le
  have hb := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hu₀ quarter_score_pos.le).2 hu₁) (sub_nonneg.2 hd)
  have hu : u ≤ rimEigenvalue a - (rimEigenvalue a - cos a) * u ^ 2 := by
    have he : cos a * quarterScore ^ 2 + rimEigenvalue a * (1 - quarterScore ^ 2) = u :=
      latitude_rim_score a
    linarith
  rw [equalRimOptRadius, if_neg h.not_ge]
  exact arccos_le_arccos (score_le_optimal h ha hu)

private theorem quarter_radius_eq :
    equalRimOptRadius (π / 2) = arccos quarterScore := by
  have ha₁ : π / 3 < π / 2 := by linarith [pi_pos]
  have ha₂ : π / 2 ≤ π := by linarith [pi_pos]
  have hq := latitude_rim_score (π / 2)
  rw [cos_pi_div_two, sin_pi_div_two, zero_mul, zero_add, mul_one] at hq
  have hh := score_unique ha₁ ha₂ quarter_score_pos (by rw [cos_pi_div_two]; linarith)
  rw [equalRimOptRadius, if_neg ha₁.not_ge, ← hh]

private theorem quarter_ratio_gt_half : (1 / 2 : ℝ) < (2 / π) * arccos quarterScore := by
  have hsq : (√2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hlt : quarterScore < √2 / 2 := by
    apply (sq_lt_sq₀ quarter_score_pos.le (by positivity)).1
    rw [quarter_score_sq, hsq]
    norm_num
  have hc : π / 4 < arccos quarterScore := by
    exact lt_of_not_ge (fun h => hlt.not_ge (arccos_le_pi_div_four.mp h))
  rw [div_mul_eq_mul_div, lt_div_iff₀ pi_pos]
  linarith

private theorem fixed_latitude_secant (s : ℝ) (hs : s ∈ Set.Icc 0 (π / 2)) :
    arccos (quarterScore * cos s) ≤ arccos quarterScore +
      (1 - (2 / π) * arccos quarterScore) * s := by
  have hpi : 0 < π / 2 := by positivity
  let b := s / (π / 2)
  have hb : 0 ≤ b := div_nonneg hs.1 hpi.le
  have hb₁ : b ≤ 1 := (div_le_one hpi).2 hs.2
  have hmul : b * (π / 2) = s := div_mul_cancel₀ _ hpi.ne'
  have hc := (arccos_cos_mul_convex quarter_score_pos.le quarter_score_lt_one).2
    (show (0 : ℝ) ∈ Set.Icc 0 (π / 2) from ⟨le_rfl, hpi.le⟩)
    (show π / 2 ∈ Set.Icc 0 (π / 2) from ⟨hpi.le, le_rfl⟩)
    (sub_nonneg.2 hb₁) hb (sub_add_cancel 1 b)
  simp only [smul_eq_mul, mul_zero, zero_add, hmul, cos_zero, mul_one,
    cos_pi_div_two, arccos_zero] at hc
  calc
    _ ≤ (1 - b) * arccos quarterScore + b * (π / 2) := hc
    _ = _ := by dsimp [b]; field_simp [pi_pos.ne']; ring

private theorem strict_ratio_away_from_quarter (a : ℝ) (ha : a ∈ Set.Ioc 0 π)
    (hne : a ≠ π / 2) :
    equalRimOptRadius a / equalRimDefect a < (2 / π) * arccos quarterScore := by
  let c := (2 / π) * arccos quarterScore
  have hc : 1 / 2 < c := quarter_ratio_gt_half
  by_cases h : a ≤ π / 3
  · rw [equalRimDefect, equalRimOptRadius, if_pos h, if_pos h]
    rw [div_lt_iff₀ (by linarith [ha.1] : 0 < 3 * a)]
    change a < c * (3 * a)
    nlinarith [mul_pos (show 0 < 3 * c - 1 by linarith) ha.1]
  let s := |a - π / 2|
  have hs : 0 < s := abs_pos.2 (sub_ne_zero.2 hne)
  have hsπ : s ≤ π / 2 := abs_le.2 ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hdef : π / 2 + s ≤ equalRimDefect a := by
    rw [equalRimDefect, if_neg h]
    by_cases ha₁ : a ≤ π / 2
    · rw [if_pos ha₁, show s = -(a - π / 2) from abs_of_nonpos (sub_nonpos.2 ha₁)]
      linarith
    · rw [if_neg ha₁, show s = a - π / 2 from abs_of_nonneg (sub_nonneg.2 (le_of_not_ge ha₁))]
      linarith
  have hr := radius_le_fixed_latitude (lt_of_not_ge h) ha.2
  rw [← cos_sub_pi_div_two, ← cos_abs] at hr
  have hR := hr.trans (fixed_latitude_secant s ⟨hs.le, hsπ⟩)
  have h₀ : arccos quarterScore = c * (π / 2) := by dsimp [c]; field_simp [pi_pos.ne']; ring
  change equalRimOptRadius a / equalRimDefect a < c
  rw [div_lt_iff₀ (by linarith [pi_pos] : 0 < equalRimDefect a)]
  calc
    _ ≤ arccos quarterScore + (1 - c) * s := hR
    _ < c * (π / 2 + s) := by rw [h₀]; nlinarith [mul_pos (show 0 < 2 * c - 1 by linarith) hs]
    _ ≤ c * equalRimDefect a := mul_le_mul_of_nonneg_left hdef (by linarith)

private theorem ratio_at_quarter :
    equalRimOptRadius (π / 2) / equalRimDefect (π / 2) =
      (2 / π) * arccos quarterScore := by
  rw [quarter_radius_eq, equalRimDefect, if_neg (by linarith [pi_pos]), if_pos le_rfl]
  field_simp [pi_pos.ne']
  ring

end RoundQuaternionEqualRimMinimax
