/- GID: D5/S3/Quantum/Analysis/RefinedBMVCoefficients
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The cubic BMV cyclic coefficient identity and the scalar Schur complement bounds. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace RefinedBMV

/-- The sum of the two largest inputs. -/
def pairSum (x y z : ℝ) : ℝ :=
  x + y + z - min x (min y z)

/-- The real kernel at center `z` in the cubic closed-walk decomposition. -/
def kernel (z x y : ℝ) : ℝ :=
  2 * (x + y) + z - 2 * (x - y) ^ 2 / pairSum x y z

/-- The ten monomials of the complete homogeneous cubic, minus ten times `xyz`. -/
def cubicDefect (x y z : ℝ) : ℝ :=
  x ^ 3 + y ^ 3 + z ^ 3 + x ^ 2 * y + x ^ 2 * z + y ^ 2 * x +
    y ^ 2 * z + z ^ 2 * x + z ^ 2 * y - 9 * x * y * z

theorem kernel_symm (z x y : ℝ) : kernel z x y = kernel z y x := by
  unfold kernel pairSum
  rw [show min x (min y z) = min y (min x z) by ac_rfl, add_comm x y,
    show (x - y) ^ 2 = (y - x) ^ 2 by ring]

/-- The rational corrections cancel around a three-step closed walk. -/
theorem cubicDefect_eq_cyclic (x y z : ℝ) :
    cubicDefect x y z =
      (x - z) * (y - z) * kernel z x y +
      (y - x) * (z - x) * kernel x y z +
      (z - y) * (x - y) * kernel y z x := by
  have h₁ : pairSum y z x = pairSum x y z := by
    unfold pairSum
    rw [show min y (min z x) = min x (min y z) by ac_rfl]
    ring
  have h₂ : pairSum z x y = pairSum x y z := by
    unfold pairSum
    rw [show min z (min x y) = min x (min y z) by ac_rfl]
    ring
  simp only [cubicDefect, kernel, h₁, h₂, div_eq_mul_inv]
  ring

theorem kernel_zero (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    kernel 0 x y = 8 * x * y / (x + y) := by
  simp only [kernel, pairSum, min_eq_right hy, min_eq_right hx, add_zero, sub_zero]
  by_cases h : x + y = 0
  · simp [h]
  · field_simp
    ring

/-- The symmetric correction, with its boundary value when a pair sum vanishes. -/
def symmetricCorrection (x y z : ℝ) : ℝ :=
  if (x + y) * (y + z) * (z + x) = 0 then 2 / (x + y + z)
  else 2 * (x * y + y * z + z * x) / ((x + y) * (y + z) * (z + x))

/-- The coefficient kernel for a closed walk centered at `x`. -/
def symmetricKernel (x y z : ℝ) : ℝ :=
  x + 2 * (y + z) - symmetricCorrection x y z * (y - z) ^ 2

private theorem symmetricCorrection_rotate (x y z : ℝ) :
    symmetricCorrection y z x = symmetricCorrection x y z := by
  unfold symmetricCorrection
  rw [show (y + z) * (z + x) * (x + y) = (x + y) * (y + z) * (z + x) by ring,
    show y + z + x = x + y + z by ring,
    show y * z + z * x + x * y = x * y + y * z + z * x by ring]

theorem cubicDefect_eq_cyclic_symmetric (x y z : ℝ) :
    cubicDefect x y z =
      (y - x) * (z - x) * symmetricKernel x y z +
      (z - y) * (x - y) * symmetricKernel y z x +
      (x - z) * (y - z) * symmetricKernel z x y := by
  simp only [cubicDefect, symmetricKernel, symmetricCorrection_rotate y z x,
    symmetricCorrection_rotate x y z]
  ring

private theorem symmetricCorrection_zero (y z : ℝ) :
    symmetricCorrection 0 y z = 2 / (y + z) := by
  simp only [symmetricCorrection, zero_add, add_zero, zero_mul, mul_zero]
  split_ifs with h
  · rfl
  · have hy : y ≠ 0 := fun hy ↦ h (by simp [hy])
    have hz : z ≠ 0 := fun hz ↦ h (by simp [hz])
    have hyz : y + z ≠ 0 := fun hyz ↦ h (by simp [hyz])
    field_simp [hy, hz, hyz]

theorem symmetricKernel_zero (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    symmetricKernel 0 y z = 8 * y * z / (y + z) := by
  rw [← kernel_zero y z hy hz, symmetricKernel, symmetricCorrection_zero]
  simp only [kernel, pairSum, min_eq_right hz, min_eq_right hy, add_zero, zero_add,
    sub_zero, div_eq_mul_inv]
  ring

/-- At a positive center, the kernel splits into a rank-one term and a Cauchy term. -/
theorem symmetricKernel_pos (x y z : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    symmetricKernel x y z =
      x * ((x + 3 * y) / (x + y)) * ((x + 3 * z) / (x + z)) +
        8 * (y ^ 2 / (x + y)) * (z ^ 2 / (x + z)) / (y + z) := by
  by_cases h : y + z = 0
  · have hy0 : y = 0 := by linarith
    have hz0 : z = 0 := by linarith
    simp [hy0, hz0, symmetricKernel, hx.ne']
  · have hxy : x + y ≠ 0 := (add_pos_of_pos_of_nonneg hx hy).ne'
    have hzx : z + x ≠ 0 := (add_pos_of_nonneg_of_pos hz hx).ne'
    rw [symmetricKernel, symmetricCorrection, ite_eq_right (mul_ne_zero (mul_ne_zero hxy h) hzx)]
    rw [add_comm z x] at hzx ⊢
    field_simp [hxy, hzx, h]
    ring

theorem kernel_one_zero (x : ℝ) (hx : 0 ≤ x) :
    kernel 1 0 x = (3 * x + 1) / (x + 1) := by
  have hmin : min 0 (min x 1) = 0 := min_eq_left (le_min hx zero_le_one)
  simp only [kernel, pairSum, hmin, zero_add, sub_zero]
  have hp : 0 < x + 1 := by positivity
  field_simp
  ring

theorem kernel_one_diag (x : ℝ) : kernel 1 x x = 4 * x + 1 := by
  simp only [kernel, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, sub_zero]
  ring

theorem kernel_scale (t z x y : ℝ) (ht : 0 < t) :
    kernel (t * z) (t * x) (t * y) = t * kernel z x y := by
  have hm : pairSum (t * x) (t * y) (t * z) = t * pairSum x y z := by
    simp only [pairSum, ← mul_min_of_nonneg _ _ ht.le]
    ring
  simp only [kernel, hm, ← mul_sub]
  by_cases h : pairSum x y z = 0
  · simp [h]
    ring
  · field_simp [ne_of_gt ht, h]

/-- The scalar Schur complement at a positive pivot of the Cauchy kernel. -/
theorem cauchy_complement (p x y : ℝ) (hp : 0 < p) (hx : 0 < x) (hy : 0 < y) :
    (x + y)⁻¹ - (x + p)⁻¹ * (2 * p) * (p + y)⁻¹ =
      ((x - p) / (x + p)) * (x + y)⁻¹ * ((y - p) / (y + p)) := by
  rw [add_comm p y]
  have hxy : 0 < x + y := by positivity
  have hxp : 0 < x + p := by positivity
  have hyp : 0 < y + p := by positivity
  field_simp
  ring

/-- Off-diagonal entry after pivoting on the zero input and rescaling. -/
def complementEntry (u v : ℝ) : ℝ :=
  ((1 + u) * (1 + v) * kernel 1 u v - (3 * u + 1) * (3 * v + 1)) / 4

private theorem complementEntry_of_le_one (u v : ℝ) (hu : u ≤ 1) (huv : u ≤ v)
    (hv : 0 ≤ v) : complementEntry u v = u ^ 2 * (3 * v - u) / 2 := by
  have hmin : min u (min v 1) = u := min_eq_left (le_min huv hu)
  have hm : pairSum u v 1 = v + 1 := by
    rw [pairSum, hmin]
    ring
  have hp : 0 < v + 1 := by positivity
  simp only [complementEntry, kernel, hm]
  field_simp
  ring

private theorem complementEntry_of_one_le (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) :
    complementEntry u v = (4 * u ^ 2 * v ^ 2 - (u - v) ^ 2) / (2 * (u + v)) := by
  have hv : 1 ≤ v := hu.trans huv
  have hmin : min u (min v 1) = 1 := by rw [min_eq_right hv, min_eq_right hu]
  have hp : 0 < u + v := by linarith
  simp only [complementEntry, kernel, pairSum, hmin, add_sub_cancel_right]
  field_simp
  ring

/-- The determinant of the rescaled two-by-two Schur complement is nonnegative. -/
theorem complementEntry_sq_le (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    complementEntry u v ^ 2 ≤ u ^ 3 * v ^ 3 := by
  have hv : 0 ≤ v := hu.trans huv
  rcases le_total u 1 with h | h
  · rw [complementEntry_of_le_one u v h huv hv, ← sub_nonneg]
    rw [show u ^ 3 * v ^ 3 - (u ^ 2 * (3 * v - u) / 2) ^ 2 =
        u ^ 3 * (v - u) ^ 2 * (4 * v - u) / 4 by ring]
    have : 0 ≤ 4 * v - u := by linarith
    positivity
  · rw [complementEntry_of_one_le u v h huv, div_pow]
    have hp : 0 < u + v := by linarith
    have hden : 0 < (2 * (u + v)) ^ 2 := by positivity
    apply (div_le_iff₀ hden).2
    have hgap : 0 ≤ v - u := sub_nonneg.mpr huv
    have hprod : v ≤ u * v := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right h hv
    have hgap' : v - u ≤ 2 * u * v := by nlinarith
    have hsq := pow_le_pow_left₀ hgap hgap' 2
    have hn : 0 ≤ 4 * u ^ 2 * v ^ 2 - (u - v) ^ 2 := by nlinarith
    have hle : 4 * u ^ 2 * v ^ 2 - (u - v) ^ 2 ≤ 4 * u ^ 2 * v ^ 2 :=
      sub_le_self _ (sq_nonneg _)
    calc
      (4 * u ^ 2 * v ^ 2 - (u - v) ^ 2) ^ 2 ≤ (4 * u ^ 2 * v ^ 2) ^ 2 :=
        pow_le_pow_left₀ hn hle 2
      _ = (u ^ 3 * v ^ 3) * (16 * u * v) := by ring
      _ ≤ (u ^ 3 * v ^ 3) * (2 * (u + v)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [sq_nonneg (u - v)]

#print axioms cubicDefect_eq_cyclic
#print axioms cauchy_complement
#print axioms complementEntry_sq_le

end RefinedBMV
