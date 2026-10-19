/- GID: D5/S3/Quantum/Subentropy/UniformValues
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/UniformValues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.result; premises=D5/S3/Quantum/Subentropy/UniformIntegrals.integral_uniformTwo_kernel,D5/S3/Quantum/Subentropy/UniformIntegrals.integral_uniformFour_kernel
   digest: Exact determinant-integral subentropy of the maximally mixed qubit and four-level state. -/

import D5.S3.Quantum.Subentropy.Basic
import D5.S3.Quantum.Subentropy.UniformIntegrals

/-! Explicit kernel expansions evaluate the two uniform states needed in the SSA counterexample. -/
noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped BigOperators
namespace D5.S3.Quantum.Subentropy.UniformValues
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.UniformIntegrals

/-- The maximally mixed two-level state has subentropy log 2 − 1/2. -/
theorem subentropy_uniformTwo {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2) :
    matrixSubentropy (diagonal (fun _ : ι => ((1 / 2 : ℝ) : ℂ))) =
      Real.log 2 - 1 / 2 := by
  unfold matrixSubentropy
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        1 / (t + 1 / 2) - 1 / (t + 1) - 1 / (4 * (t + 1 / 2)^2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [kernel_diagonal _ t (ne_of_gt ht)]
      simp only [Finset.prod_const, Finset.card_univ, hcard]
      have h₀ : t + 1 / 2 ≠ 0 := by linarith [ht.out]
      have h₁ : 1 + t ≠ 0 := by linarith [ht.out]
      have h₂ : t + 1 ≠ 0 := by linarith [ht.out]
      have htpos : 0 < t := ht
      field_simp (disch := positivity)
      <;> ring
    _ = _ := integral_uniformTwo_kernel

/-- The maximally mixed four-level state has subentropy log 4 − 13/12. -/
theorem subentropy_uniformFour {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 4) :
    matrixSubentropy (diagonal (fun _ : ι => ((1 / 4 : ℝ) : ℂ))) =
      Real.log 4 - 13 / 12 := by
  unfold matrixSubentropy
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        1 / (t + 1 / 4) - 1 / (t + 1) - 3 / (8 * (t + 1 / 4)^2) +
          1 / (16 * (t + 1 / 4)^3) - 1 / (256 * (t + 1 / 4)^4) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [kernel_diagonal _ t (ne_of_gt ht)]
      simp only [Finset.prod_const, Finset.card_univ, hcard]
      have h₀ : t + 1 / 4 ≠ 0 := by linarith [ht.out]
      have h₁ : 1 + t ≠ 0 := by linarith [ht.out]
      have h₂ : t + 1 ≠ 0 := by linarith [ht.out]
      have htpos : 0 < t := ht
      field_simp (disch := positivity)
      <;> ring
    _ = _ := integral_uniformFour_kernel

end D5.S3.Quantum.Subentropy.UniformValues
