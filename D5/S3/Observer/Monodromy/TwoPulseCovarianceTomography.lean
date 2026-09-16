/- GID: D5/S3/Observer/Monodromy/TwoPulseCovarianceTomography
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/TwoPulseCovarianceTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two bounded calibrated shear pulses recover a covariance entry with a leaf-coupling-independent variance-error bound. -/

import D5.S3.Observer.Monodromy.TransvectionLieFiltration
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

/-!
# Bounded two-pulse covariance tomography

The actual pulse on natural states is I + t e_i H_i. In the readout coordinates
z = H x, its dual action on an observable coefficient vector is the transpose
row increment of H. We use that actual matrix, not a supplied transport law.

The sign and second strength are chosen from the known couplings. Their
magnitudes are at most one, the second denominator is certified nonzero, and
the second pulse removes the unwanted leaf-leaf coupling from the final ray.
Four actual variances then isolate a covariance entry. The deterministic
error bound has no dependence on the leaf-leaf coupling.

The theorem is valid for every real symmetric bilinear form; in particular it
applies to the symmetrized covariance of quantum quadratures whenever the
specified pulses have the stated unitary realization. It does not define a
finite-dimensional exact CCR representation, prove Gaussian-state existence,
model control errors, or supply a finite-shot concentration theorem.

General Gaussian covariance tomography is established prior art. This module
addresses a specified bounded shear-control architecture; it does not claim
to overturn a no-go theorem for a single fixed autonomous evolution.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.TwoPulseCovarianceTomography

open D5.S3.Observer.Monodromy.TransvectionLieFiltration

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Genuine dual action on the coefficients of the linear quadrature readout. -/
def dualPulse (H : Matrix I I ℝ) (i : I) (t : ℝ) (v : I → ℝ) : I → ℝ :=
  (1 + t • increment H.transpose i).mulVec v

/-- Quadrature variance supplied by an actual bilinear covariance form. -/
def variance (B : LinearMap.BilinForm ℝ (I → ℝ)) (v : I → ℝ) : ℝ := B v v

/-- Align the indirect contribution with the nonzero anchor coupling. -/
def routingSign (H : Matrix I I ℝ) (a i j : I) : ℝ :=
  if 0 ≤ H a j * (H a i * H i j) then 1 else -1

/-- The second strength cancels the known indirect coupling, without amplification. -/
def routingStrength (H : Matrix I I ℝ) (a i j : I) : ℝ :=
  H a j / (H a j + routingSign H a i j * (H a i * H i j))

/-- Construct bounded actual pulse controls, derive their exact covariance
readback, and certify the reconstruction under four independent absolute
variance-error bounds. The theorem assumes neither a precomputed readout ray
nor a noncancellation condition on the leaf-leaf coupling. -/
theorem bounded_two_pulse_covariance_recovery
    (H : Matrix I I ℝ) (a i j : I) (hi : H a i ≠ 0) (hj : H a j ≠ 0) :
    let e : I → (I → ℝ) := fun r => Pi.single r 1
    let s := routingSign H a i j
    let t := routingStrength H a i j
    let vi := dualPulse H i s (e a)
    let vj := dualPulse H j 1 (e a)
    let vij := dualPulse H j t vi
    |s| = 1 ∧ |t| ≤ 1 ∧
      vij = e a + (s * H a i) • e i + (H a j) • e j ∧
      ∀ (B : LinearMap.BilinForm ℝ (I → ℝ)),
        (∀ u v, B u v = B v u) →
        (variance B vij - variance B vi - variance B vj + variance B (e a)) /
            (2 * s * H a i * H a j) = B (e i) (e j) ∧
        ∀ (ε z2 zi zj z0 : ℝ), 0 ≤ ε →
          |z2 - variance B vij| ≤ ε → |zi - variance B vi| ≤ ε →
          |zj - variance B vj| ≤ ε → |z0 - variance B (e a)| ≤ ε →
          |(z2 - zi - zj + z0) / (2 * s * H a i * H a j) - B (e i) (e j)| ≤
            2 * ε / |H a i * H a j| := by
  classical
  let e : I → (I → ℝ) := fun r => Pi.single r 1
  let s := routingSign H a i j
  let t := routingStrength H a i j
  let vi := dualPulse H i s (e a)
  let vj := dualPulse H j 1 (e a)
  let vij := dualPulse H j t vi
  change |s| = 1 ∧ |t| ≤ 1 ∧
    vij = e a + (s * H a i) • e i + (H a j) • e j ∧ _
  have hsabs : |s| = 1 := by
    dsimp [s, routingSign]
    split_ifs <;> norm_num
  have hcross : 0 ≤ H a j * (s * (H a i * H i j)) := by
    dsimp [s, routingSign]
    split_ifs with h <;> nlinarith
  have hbound : |H a j| ≤ |H a j + s * (H a i * H i j)| := by
    nlinarith [sq_abs (H a j), sq_abs (H a j + s * (H a i * H i j)),
      sq_nonneg (s * (H a i * H i j)), abs_nonneg (H a j),
      abs_nonneg (H a j + s * (H a i * H i j))]
  have hden : H a j + s * (H a i * H i j) ≠ 0 :=
    abs_pos.mp (lt_of_lt_of_le (abs_pos.mpr hj) hbound)
  have htbound : |t| ≤ 1 := by
    change |H a j / (H a j + s * (H a i * H i j))| ≤ 1
    rw [abs_div]
    exact (div_le_one (abs_pos.mpr hden)).mpr hbound
  have ht : t * (H a j + s * (H a i * H i j)) = H a j :=
    div_mul_cancel₀ _ hden
  have hstep (r : I) (u : ℝ) (v : I → ℝ) :
      dualPulse H r u v = v + (u * ∑ c, H c r * v c) • e r := by
    ext b
    change (∑ c, ((1 : Matrix I I ℝ) b c +
      u * increment H.transpose r b c) * v c) = _
    simp only [add_mul, Finset.sum_add_distrib]
    have hid : (∑ c, (1 : Matrix I I ℝ) b c * v c) = v b := by
      simp [Matrix.one_apply]
    rw [hid]
    by_cases hb : b = r
    · subst b
      simp [increment, Matrix.transpose_apply, e, Finset.mul_sum, mul_assoc]
    · simp [increment, hb, e, Pi.single_apply, Ne.symm hb]
  have hone (r : I) (u : ℝ) :
      dualPulse H r u (e a) = e a + (u * H a r) • e r := by
    rw [hstep]
    have hsum : (∑ c, H c r * e a c) = H a r := by simp [e]
    rw [hsum]
  have hvi : vi = e a + (s * H a i) • e i := hone i s
  have hvj : vj = e a + (H a j) • e j := by simpa using hone j 1
  have hvij : vij = e a + (s * H a i) • e i + (H a j) • e j := by
    change dualPulse H j t vi = _
    rw [hstep, hvi]
    have hsum : (∑ c, H c j * (e a + (s * H a i) • e i) c) =
        H a j + s * (H a i * H i j) := by
      simp [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
        Finset.sum_add_distrib, mul_ite, ite_mul]
      <;> ring
    rw [hsum, ht]
  refine ⟨hsabs, htbound, hvij, ?_⟩
  intro B hB
  have hpolar : variance B vij - variance B vi - variance B vj + variance B (e a) =
      (2 * s * H a i * H a j) * B (e i) (e j) := by
    rw [hvij, hvi, hvj]
    simp only [variance, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    rw [hB (e j) (e i)]
    ring
  have hs : s ≠ 0 := abs_pos.mp (by rw [hsabs]; norm_num)
  have hd : 2 * s * H a i * H a j ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs) hi) hj
  have hideal :
      (variance B vij - variance B vi - variance B vj + variance B (e a)) /
        (2 * s * H a i * H a j) = B (e i) (e j) := by
    apply (div_eq_iff hd).mpr
    simpa [mul_comm] using hpolar
  refine ⟨hideal, ?_⟩
  intro ε z2 zi zj z0 _hε hz2 hzi hzj hz0
  let E := (z2 - variance B vij) - (zi - variance B vi) -
    (zj - variance B vj) + (z0 - variance B (e a))
  have herror :
      (z2 - zi - zj + z0) / (2 * s * H a i * H a j) - B (e i) (e j) =
        E / (2 * s * H a i * H a j) := by
    calc
      _ = (z2 - zi - zj + z0) / (2 * s * H a i * H a j) -
          (variance B vij - variance B vi - variance B vj + variance B (e a)) /
            (2 * s * H a i * H a j) := by rw [hideal]
      _ = E / (2 * s * H a i * H a j) := by
        dsimp [E]
        ring
  have htriangle (r u : ℝ) : |r - u| ≤ |r| + |u| := by
    simpa using abs_sub_le r 0 u
  have hbudget : |E| ≤ 4 * ε := by
    have h1 := htriangle (z2 - variance B vij) (zi - variance B vi)
    have h2 := htriangle ((z2 - variance B vij) - (zi - variance B vi))
      (zj - variance B vj)
    have h3 := abs_add ((z2 - variance B vij) - (zi - variance B vi) -
      (zj - variance B vj)) (z0 - variance B (e a))
    dsimp [E]
    linarith
  have hdabs : |2 * s * H a i * H a j| = 2 * |H a i * H a j| := by
    simp [abs_mul, hsabs, mul_assoc]
  rw [herror, abs_div, hdabs]
  calc
    |E| / (2 * |H a i * H a j|) ≤ (4 * ε) / (2 * |H a i * H a j|) :=
      div_le_div_of_nonneg_right hbudget (by positivity)
    _ = 2 * ε / |H a i * H a j| := by
      have hab : 0 < |H a i * H a j| := abs_pos.mpr (mul_ne_zero hi hj)
      field_simp [ne_of_gt hab]
      <;> ring

#print axioms bounded_two_pulse_covariance_recovery

end D5.S3.Observer.Monodromy.TwoPulseCovarianceTomography
