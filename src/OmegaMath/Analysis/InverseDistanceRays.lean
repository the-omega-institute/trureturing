import OmegaBuild.Commands
import OmegaMath.Analysis.InverseDistanceThree

/-! Omega original.

The inverse-distance gradient along a ray and its leading coefficient at infinity.
-/

compile_only_with_mathlib

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace OmegaMath.InverseDistanceThree

private theorem squareDistance_nonneg (x c : Point) : 0 ≤ squareDistance x c := by
  unfold squareDistance
  positivity

private theorem hasDerivAt_squareDistance_ray (u c : Point) (r : ℝ) :
    HasDerivAt (fun s : ℝ => squareDistance (s • u) c)
      (2 * ∑ j, (r * u j - c j) * u j) r := by
  rw [Finset.mul_sum]
  have h (j : Fin 3) :
      HasDerivAt (fun s : ℝ => (s * u j - c j) ^ 2)
        (2 * ((r * u j - c j) * u j)) r := by
    convert ((((hasDerivAt_id' r).mul_const (u j)).sub_const (c j)).pow 2) using 1
    simp only [Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, one_mul]
    ring
  simpa only [squareDistance, Pi.smul_apply, smul_eq_mul] using
    (HasDerivAt.fun_sum (u := Finset.univ) fun j _ => h j)

theorem hasDerivAt_inverse_ray (u c : Point) {r : ℝ} (hr : r • u ≠ c) :
    HasDerivAt (fun s : ℝ => 1 / radius (s • u) c)
      (-(∑ j, (r * u j - c j) * u j) / radius (r • u) c ^ 3) r := by
  have hpos := radius_pos hr
  have hs : squareDistance (r • u) c ≠ 0 := (Real.sqrt_pos.mp hpos).ne'
  have h := ((hasDerivAt_squareDistance_ray u c r).sqrt hs).inv hpos.ne'
  convert h using 1
  · funext s
    exact one_div _
  · change _ = -((2 * ∑ j, (r * u j - c j) * u j) /
      (2 * radius (r • u) c)) / radius (r • u) c ^ 2
    field_simp [hpos.ne']

private theorem sum_unit_sq {u : Point} (hu : radius u 0 = 1) :
    ∑ j, u j ^ 2 = 1 := by
  have h := Real.sq_sqrt (squareDistance_nonneg u (0 : Point))
  change Real.sqrt (squareDistance u 0) = 1 at hu
  rw [hu, one_pow] at h
  simpa [squareDistance] using h.symm

private theorem tendsto_normalized_component (u c : Point) (j : Fin 3) :
    Tendsto (fun r : ℝ => u j - c j / r) atTop (𝓝 (u j)) := by
  simpa [div_eq_mul_inv] using
    tendsto_const_nhds.sub (tendsto_inv_atTop_zero.const_mul (c j))

private theorem normalized_radius_eq (u c : Point) {r : ℝ} (hr : 0 < r) :
    radius (r • u) c / r = Real.sqrt (∑ j, (u j - c j / r) ^ 2) := by
  have he : squareDistance (r • u) c = r ^ 2 * ∑ j, (u j - c j / r) ^ 2 := by
    rw [squareDistance, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hr.ne']
  rw [radius, he, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le, mul_div_cancel_left₀ _ hr.ne']

theorem tendsto_normalized_radius {u : Point} (hu : radius u 0 = 1) (c : Point) :
    Tendsto (fun r : ℝ => radius (r • u) c / r) atTop (𝓝 1) := by
  have hsum := tendsto_finsetSum (s := Finset.univ)
    fun j _ => (tendsto_normalized_component u c j).pow 2
  have h := (Real.continuous_sqrt.tendsto _).comp hsum
  rw [sum_unit_sq hu, Real.sqrt_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (normalized_radius_eq u c hr).symm

theorem tendsto_scaled_inverse_deriv {u : Point} (hu : radius u 0 = 1) (c : Point) :
    Tendsto (fun r : ℝ => -(r ^ 2) * deriv (fun s : ℝ => 1 / radius (s • u) c) r)
      atTop (𝓝 1) := by
  have hsum := tendsto_finsetSum (s := Finset.univ)
    fun j _ => (tendsto_normalized_component u c j).mul_const (u j)
  have hunit : (∑ j, u j * u j) = 1 := by simpa [pow_two] using sum_unit_sq hu
  rw [hunit] at hsum
  have h := hsum.div ((tendsto_normalized_radius hu c).pow 3) (by norm_num)
  norm_num at h
  refine h.congr' ?_
  have hradius := (tendsto_radius_atTop hu c).eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hradius] with r hr hpos
  change 0 < radius (r • u) c at hpos
  have hne : r • u ≠ c := by
    intro he
    rw [he] at hpos
    simp [radius, squareDistance] at hpos
  change (∑ j, (u j - c j / r) * u j) / (radius (r • u) c / r) ^ 3 = _
  rw [(hasDerivAt_inverse_ray u c hne).deriv]
  have he : (∑ j, (u j - c j / r) * u j) * r =
      ∑ j, (r * u j - c j) * u j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [hr.ne']
  rw [← he]
  generalize (∑ j, (u j - c j / r) * u j) = b
  field_simp [hr.ne', hpos.ne']

end OmegaMath.InverseDistanceThree
