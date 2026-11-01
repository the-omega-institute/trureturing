/- GID: D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact factorial Gaussian moments and their finite-mode insertion recurrence. -/

import D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment

open MvPolynomial FactorialFockQuadraticEstimate

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem sub_single_degree (d : I →₀ ℕ) (j : I) (hj : d j ≠ 0) :
    (d - Finsupp.single j 1).degree + 1 = d.degree := by
  have h := congrArg Finsupp.degree (Finsupp.sub_add_single_one_cancel hj)
  simpa only [map_add, Finsupp.degree_single] using h

theorem weight_sub_single (d : I →₀ ℕ) (j : I) (hj : d j ≠ 0) :
    FactorialFockMetric.weight d =
      d j * FactorialFockMetric.weight (d - Finsupp.single j 1) := by
  have h := FactorialFockMetric.weight_add_single (d - Finsupp.single j 1) j
  rw [Finsupp.sub_add_single_one_cancel hj] at h
  simpa only [Finsupp.tsub_apply, Finsupp.single_eq_same,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj)] using h

def nativeMoment (A : Matrix I I ℂ) (d : I →₀ ℕ) : ℂ :=
  (FactorialFockMetric.weight d : ℂ) * gaussianCoefficient A d

theorem nativeMoment_step (A : Matrix I I ℂ)
    (hsym : ∀ i j, A i j = A j i) (r : I →₀ ℕ) (i : I) :
    nativeMoment A (r + Finsupp.single i 1) =
      ∑ j, (r j : ℂ) * A i j * nativeMoment A (r - Finsupp.single j 1) := by
  classical
  by_cases hodd : r.degree % 2 = 1
  · let n := r.degree / 2
    have hr : r.degree = 2 * n + 1 := by dsimp [n]; omega
    have ht : (r + Finsupp.single i 1).degree = 2 * (n + 1) := by
      simp only [map_add, Finsupp.degree_single]; omega
    have hstep := gaussianPiece_coefficient_step A hsym n i r
    rw [← gaussianCoefficient_even A _ (n + 1) ht] at hstep
    have hweight : (FactorialFockMetric.weight (r + Finsupp.single i 1) : ℂ) =
        (r i + 1 : ℂ) * (FactorialFockMetric.weight r : ℂ) := by
      exact_mod_cast FactorialFockMetric.weight_add_single r i
    unfold nativeMoment
    rw [hweight]
    calc
      _ = (FactorialFockMetric.weight r : ℂ) *
          (gaussianCoefficient A (r + Finsupp.single i 1) * (r i + 1 : ℂ)) := by ring
      _ = _ := by
        rw [hstep, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hz : r j = 0
        · simp [coeff_X_mul', Finsupp.mem_support_iff, hz]
        · have hd : (r - Finsupp.single j 1).degree = 2 * n := by
            have := sub_single_degree r j hz; omega
          rw [coeff_X_mul', if_pos (Finsupp.mem_support_iff.mpr hz),
            ← gaussianCoefficient_even A _ n hd]
          have hw : (FactorialFockMetric.weight r : ℂ) =
              (r j : ℂ) * (FactorialFockMetric.weight (r - Finsupp.single j 1) : ℂ) := by
            exact_mod_cast weight_sub_single r j hz
          rw [hw]
          ring
  · have ht : (r + Finsupp.single i 1).degree % 2 = 1 := by
      simp only [map_add, Finsupp.degree_single]
      omega
    rw [nativeMoment, gaussianCoefficient_odd A _ ht, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hz : r j = 0
    · simp [hz]
    · have hd : (r - Finsupp.single j 1).degree % 2 = 1 := by
        have := sub_single_degree r j hz
        omega
      simp [nativeMoment, gaussianCoefficient_odd A _ hd]

theorem occupation_nonzero (d : I →₀ ℕ) (hd : d ≠ 0) :
    ∃ i, d i ≠ 0 := by
  by_contra h
  push_neg at h
  exact hd (Finsupp.ext h)

#print axioms nativeMoment_step

end D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment
