/- GID: D5/S3/Fourier/ThreeWaySlotIdentity
   generality: I
   mirror-B: D5/B/S3/Fourier/ThreeWaySlotIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit eighteen-slot three-way encoder is recovered exactly by its stated positive readout. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace D5.S3.Fourier.ThreeWaySlotIdentity

open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-- The two positive coefficients in the three-way refinement table. -/
def slotWeight (s : Fin 2) : ℂ :=
  if s = 0 then (2 / 3 : ℂ) else (1 / 3 : ℂ)

/-- The eighteen-slot encoder from (16.11). -/
def slotEncode (u : ℂ) (x : Fin 3 → ℂ) (k j : Fin 3) (s : Fin 2) : ℂ :=
  slotWeight s * u ^ (k.val * j.val + s.val) * x j

/-- The positive recovery readout from (16.12), written with inverse powers. -/
def slotRecover (u : ℂ) (y : Fin 3 → Fin 3 → Fin 2 → ℂ) (j : Fin 3) : ℂ :=
  (1 / 3 : ℂ) * ∑ k : Fin 3, ∑ s : Fin 2,
    (u⁻¹) ^ (k.val * j.val + s.val) * y k j s

private theorem inv_pow_mul_pow (u : ℂ) (hu : u ≠ 0) (n : ℕ) :
    (u⁻¹) ^ n * u ^ n = 1 := by
  rw [← mul_pow, inv_mul_cancel₀ hu]
  exact one_pow n

/-- The explicit eighteen-slot encoder and recovery satisfy `R₀ D = I₃`. -/
theorem slot_recovery (u : ℂ) (x : Fin 3 → ℂ) (hu : u ≠ 0) :
    ∀ j : Fin 3,
      slotRecover u (slotEncode u x) j = x j := by
  intro j
  unfold slotRecover
  have hterm (k : Fin 3) (s : Fin 2) :
      (u⁻¹) ^ (k.val * j.val + s.val) *
          slotEncode u x k j s = slotWeight s * x j := by
    unfold slotEncode
    calc
      (u⁻¹) ^ (k.val * j.val + s.val) *
          (slotWeight s * u ^ (k.val * j.val + s.val) * x j) =
          slotWeight s * ((u⁻¹) ^ (k.val * j.val + s.val) *
            u ^ (k.val * j.val + s.val)) * x j := by ring
      _ = slotWeight s * x j := by
        rw [inv_pow_mul_pow u hu]
        ring
  simp_rw [hterm]
  simp [slotWeight, Fin.sum_univ_succ]
  ring

end

end D5.S3.Fourier.ThreeWaySlotIdentity
