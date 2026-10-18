/- GID: D5/S3/Zeros/CriticalPoints/TangZhangRealOrder
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/TangZhangRealOrder
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Hadamard]
   utility: none
   digest: The real-order reciprocal critical-point conjecture and its equality boundary. -/

import D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
import D5.S3.Zeros.CriticalPoints.TangZhangRealOrderCounterexample
import D5.S3.Zeros.CriticalPoints.TangZhangConstantRoots
import D5.S3.Zeros.CriticalPoints.SchurMomentInequality

/-! Tang–Zhang Conjecture 1.13, including the failure of its endpoint equality clause. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Zeros.CriticalPoints.TangZhangRealOrder

open TangZhangOrderMinusTwo (P)

def c (n : ℕ) (p : ℝ) : ℝ := (((n : ℝ) + 1) ^ p + n - 1) / n

def claim : Prop :=
    (∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) → ∀ p : ℝ, 1 ≤ p →
       ((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum ≤
         c n p * ∑ j, ‖z j‖ ^ (-p)) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) → ∀ p : ℝ, 1 < p →
       (((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum =
         c n p * ∑ j, ‖z j‖ ^ (-p) ↔ ∀ i j, z i = z j)) ∧
    ¬ (∀ (n : ℕ) (z : Fin n → ℂ), (∀ j, z j ≠ 0) →
       (((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-(1 : ℝ)))).sum =
         c n 1 * ∑ j, ‖z j‖ ^ (-(1 : ℝ)) ↔ ∀ i j, z i = z j))

/-- The real-order inequality, its strict-order equality criterion, and the endpoint refutation. -/
theorem result : claim := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn z hz p hp
    have h := SchurMomentInequality.spectral_bound_and_rigidity (by omega : 0 < n)
      (fun j => (z j)⁻¹) (fun j => inv_ne_zero (hz j)) p hp
    rw [← SchurMomentNormalization.reciprocal_moment z hz p] at h
    simpa only [c, norm_inv, ← Real.rpow_neg_eq_inv_rpow] using h.1
  · intro n hn z hz p hp
    constructor
    · intro heq
      have h := SchurMomentInequality.spectral_bound_and_rigidity (by omega : 0 < n)
        (fun j => (z j)⁻¹) (fun j => inv_ne_zero (hz j)) p hp.le
      rw [← SchurMomentNormalization.reciprocal_moment z hz p] at h
      have he : ((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖ ^ (-p))).sum =
          ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ j, ‖(z j)⁻¹‖ ^ p := by
        simpa only [c, norm_inv, ← Real.rpow_neg_eq_inv_rpow] using heq
      intro i j
      exact inv_injective (h.2 hp he i j)
    · intro heq
      let i₀ : Fin n := ⟨0, by omega⟩
      have hzconst : z = fun _ : Fin n => z i₀ := funext fun j => heq j i₀
      rw [hzconst]
      exact TangZhangConstantRoots.constant_roots_moment n hn (z i₀) (hz i₀) p
  · exact TangZhangRealOrderCounterexample.counterexample

end D5.S3.Zeros.CriticalPoints.TangZhangRealOrder
