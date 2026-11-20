/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteAlignedFiber
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteAlignedFiber
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Basic]
   utility: none
   digest: Projective source points and exceptional directions above the five-site special rays. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCoordinates

/-! The special rays lift to two ordinary points each in the trace-aligned source. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteAlignedFiber

open PeriodicMPSFiveSiteCoordinates

noncomputable section

private def a (s : ℂ) : ℂ := 2 - (161 / 36 : ℂ) * s * Complex.I
private def b (s : ℂ) : ℂ := -s * Complex.I / 2
private def root (s : ℂ) : ℂ := (7 / 6 : ℂ) * (1 + s * Complex.I)

/-- The projective representative of either ray in the special marginal fiber. -/
def ray (s : ℂ) : Fin 8 → ℂ := ![a s, b s, 0, 1, 0, 0, 0, 0]

private theorem root_eq (s : ℂ) (hs : s = 1 ∨ s = -1) :
    -(root s) ^ 2 + 3 * root s * b s - b s ^ 2 = a s := by
  rcases hs with rfl | rfl <;>
    apply Complex.ext <;> norm_num [a, b, root, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Complex.normSq_apply,
      pow_two]

/-- Every nonzero scalar representative of a special ray forces the aligned source
into the chart `z ≠ 0` and determines exactly two projective points in that chart. -/
theorem ordinary_lifts (s x y z w gain : ℂ) (hs : s = 1 ∨ s = -1) (hg : gain ≠ 0) :
    aligned x y z w = gain • ray s ↔
      w = 0 ∧ z ^ 2 = gain ∧ y / z = b s ∧
        (x / z = root s ∨ x / z = 3 * b s - root s) := by
  have hroot := root_eq s hs
  constructor
  · intro h
    have hw : w = 0 := sq_eq_zero_iff.mp (by
      simpa [aligned, ray, Pi.smul_apply, smul_eq_mul] using congrFun h 6)
    have hz : z ^ 2 = gain := by
      simpa [aligned, ray, hw, Pi.smul_apply, smul_eq_mul] using congrFun h 3
    have hn : z ≠ 0 := fun hzero => hg (by simpa [hzero] using hz.symm)
    have hy0 : z * y = gain * b s := by
      simpa [aligned, ray, Pi.smul_apply, smul_eq_mul] using congrFun h 1
    have hy : y / z = b s := by
      apply (div_eq_iff hn).2
      rw [← hz, pow_two, mul_assoc] at hy0
      exact (mul_left_cancel₀ hn hy0).trans (mul_comm z (b s))
    have hp0 : -x ^ 2 + 3 * x * y - y ^ 2 = gain * a s := by
      simpa [aligned, ray, Pi.smul_apply, smul_eq_mul] using congrFun h 0
    have hpoly : -(x / z) ^ 2 + 3 * (x / z) * b s - b s ^ 2 = a s := by
      rw [← hy]
      field_simp
      linear_combination hp0 + (a s) * (hz.symm)
    refine ⟨hw, hz, hy, ?_⟩
    have hf : (x / z - root s) * (x / z - (3 * b s - root s)) = 0 := by
      linear_combination hroot - hpoly
    simpa [sub_eq_zero] using mul_eq_zero.mp hf
  · rintro ⟨rfl, hz, hy, hx⟩
    have hn : z ≠ 0 := fun hzero => hg (by simpa [hzero] using hz.symm)
    have hy' := (div_eq_iff hn).1 hy
    have hpoly : -(x / z) ^ 2 + 3 * (x / z) * b s - b s ^ 2 = a s := by
      rcases hx with hx | hx
      · rwa [hx]
      · rw [hx]
        linear_combination hroot
    have hp0 : -x ^ 2 + 3 * x * y - y ^ 2 = gain * a s := by
      rw [← hy] at hpoly
      field_simp at hpoly
      linear_combination hpoly + (a s) * hz
    funext i
    fin_cases i <;> simp [aligned, ray, Pi.smul_apply, smul_eq_mul, hp0, hz]
    rw [hy', ← hz]
    ring

/-- The exceptional image is the linear part of the aligned quadrics at a base
point on the chart `y = 1`. -/
def exceptional (r delta z w : ℂ) : Fin 8 → ℂ :=
  ![(3 - 2 * r) * delta, z, r * w, (1 - r) * w, 0, 0, 0, 0]

/-- A base point has nonzero first coordinate, so its exceptional image cannot
have zero adjacent-pair amplitude and nonzero separated-pair amplitude. -/
theorem exceptional_avoids_ray (s r delta z w gain : ℂ)
    (hr : -r ^ 2 + 3 * r - 1 = 0) (hg : gain ≠ 0) :
    exceptional r delta z w ≠ gain • ray s := by
  intro h
  have hr' : r ≠ 0 := by
    intro he
    norm_num [he] at hr
  have hw : w = 0 := (mul_eq_zero.mp (by
    simpa [exceptional, ray, Pi.smul_apply, smul_eq_mul] using congrFun h 2)).resolve_left hr'
  exact hg (by simpa [exceptional, ray, hw, Pi.smul_apply, smul_eq_mul] using
    (congrFun h 3).symm)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteAlignedFiber
