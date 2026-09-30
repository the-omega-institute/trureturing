/- GID: D5/S3/Geometry/Hyperideal/FibonacciObservation
   generality: G
   mirror-B: none(waiver:finite-observation-obstruction)
   mirror-E: none(waiver:finite-observation-obstruction)
   anchors: []
   digest: The CFMP/Fibonacci return observation has an exact persistent five-phase modular ambiguity. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.FibonacciObservation

/-- Coordinate swap on the two return parameters. -/
def pairSwap (z : ℤ × ℤ) : ℤ × ℤ := (z.2, z.1)

/-- One Fibonacci update on the return parameters. -/
def fibonacciStep (z : ℤ × ℤ) : ℤ × ℤ := (z.2, z.1 + z.2)

/-- The discriminant operator 2θ - 1 in the basis (1, θ). -/
def discriminant (z : ℤ × ℤ) : ℤ × ℤ := (-z.1 + 2 * z.2, 2 * z.1 + z.2)

/-- The cyclic CFMP return observation C = [[2,-1],[1,2]]. -/
def observe (z : ℤ × ℤ) : ℤ × ℤ := (2 * z.1 - z.2, z.1 + 2 * z.2)

/-- Addition in the return-parameter lattice. -/
def pairAdd (x y : ℤ × ℤ) : ℤ × ℤ := (x.1 + y.1, x.2 + y.2)

/-- The phase shift which spans the kernel at modulus 5k. -/
def phaseShift (k t : ℕ) : ℤ × ℤ :=
  ((k * t : ℕ) : ℤ, (2 * (k * t) : ℕ) : ℤ)

/-- Modular equality written as divisibility of the difference. -/
def modEq (m : ℕ) (a b : ℤ) : Prop := (m : ℤ) ∣ b - a

/-- Squaring the discriminant operator multiplies both coordinates by five. -/
theorem discriminant_sq (z : ℤ × ℤ) :
    discriminant (discriminant z) = (5 * z.1, 5 * z.2) := by
  rcases z with ⟨x, y⟩
  simp [discriminant]
  constructor <;> ring

/-- The return observation is the discriminant followed by coordinate swap. -/
theorem observe_eq_discriminant_swap (z : ℤ × ℤ) :
    observe z = discriminant (pairSwap z) := by
  rcases z with ⟨x, y⟩
  simp [observe, discriminant, pairSwap]
  constructor <;> ring

/-- Fibonacci conjugacy: observing after the conjugated Fibonacci step equals
the Fibonacci step after observing. -/
theorem observe_fibonacci_conjugacy (z : ℤ × ℤ) :
    observe (pairSwap (fibonacciStep (pairSwap z))) =
      fibonacciStep (observe z) := by
  rcases z with ⟨x, y⟩
  simp [observe, fibonacciStep, pairSwap]
  constructor <;> ring

theorem observe_phase_first (k t : ℕ) (z : ℤ × ℤ) :
    (observe (pairAdd z (phaseShift k t))).1 = (observe z).1 := by
  rcases z with ⟨x, y⟩
  simp [observe, pairAdd, phaseShift]
  push_cast
  ring

theorem observe_phase_second (k t : ℕ) (z : ℤ × ℤ) :
    (observe (pairAdd z (phaseShift k t))).2 =
      (observe z).2 + 5 * ((k * t : ℕ) : ℤ) := by
  rcases z with ⟨x, y⟩
  simp [observe, pairAdd, phaseShift]
  push_cast
  ring

/-- The five-phase shift is invisible to the return observation modulo 5k.
For every base parameter z and phase t, both observed coordinates are
congruent modulo 5k. -/
theorem observe_phase_indistinguishable (k t : ℕ) (z : ℤ × ℤ) :
    modEq (5 * k) (observe (pairAdd z (phaseShift k t))).1 (observe z).1 ∧
      modEq (5 * k) (observe (pairAdd z (phaseShift k t))).2 (observe z).2 := by
  constructor
  · rw [observe_phase_first]
    simp [modEq]
  · rw [observe_phase_second]
    unfold modEq
    refine ⟨-(t : ℤ), ?_⟩
    push_cast
    ring

end D5.S3.Geometry.Hyperideal.FibonacciObservation
