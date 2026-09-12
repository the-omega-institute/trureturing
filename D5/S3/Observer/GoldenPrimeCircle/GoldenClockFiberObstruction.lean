/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenClockFiberObstruction
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:universal-integer-fiber-proof)
   anchors: []
   digest: Golden multiplication descends to the full integer readout exactly for integer multipliers; every other multiplier separates infinitely many representatives in each fiber. -/

import D5.S0.Carrier.Ring
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenClockFiberObstruction

open D5.S0.Carrier

/-- The entire fiber of an integer readout is an additive coset of the ordinary integers. -/
theorem equal_integer_fiber (x y : GoldenInt) :
    x.b = y.b ↔ ∃ k : ℤ, y = x + (k : GoldenInt) := by
  constructor
  · intro h
    refine ⟨y.a - x.a, ?_⟩
    apply GoldenInt.ext
    · simp only [a_add, a_intCast]
      ring
    · simpa only [b_add, b_intCast, add_zero] using h.symm
  · rintro ⟨k, rfl⟩
    simp

/-- Multiplication is well-defined on the FULL integer quotient exactly for rational-integer
multipliers. An invariant selected section does not imply this full-fiber property. -/
theorem multiplication_descends_iff (u : GoldenInt) :
    (∃ f : ℤ → ℤ, ∀ z : GoldenInt, (u * z).b = f z.b) ↔ u.b = 0 := by
  constructor
  · rintro ⟨f, h⟩
    have hzero := h 0
    have hone := h 1
    simp only [mul_zero, b_zero] at hzero
    simp only [mul_one, b_one] at hone
    exact hone.trans hzero.symm
  · intro hu
    refine ⟨fun n => u.a * n, ?_⟩
    intro z
    simp [b_mul, hu]

/-- For every nonrational multiplier, a single integer fiber has infinitely many distinct
one-step outputs: this explicit integer-indexed output map is injective. -/
theorem fiber_output_injective (u : GoldenInt) (hu : u.b ≠ 0) (n : ℤ) :
    Function.Injective (fun k : ℤ => (u * (⟨k, n⟩ : GoldenInt)).b) := by
  intro k l h
  change u.a * n + u.b * k + u.b * n = u.a * n + u.b * l + u.b * n at h
  apply mul_left_cancel₀ hu
  linarith

end D5.S3.Observer.GoldenPrimeCircle.GoldenClockFiberObstruction
