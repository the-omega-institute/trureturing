/- GID: D5/S3/Geometry/Hyperideal/FibonacciObservation
   generality: G
   mirror-B: none(waiver:finite-observation-obstruction)
   mirror-E: none(waiver:finite-observation-obstruction)
   anchors: []
   utility: none
   digest: The CFMP/Fibonacci return observation has a persistent five-phase modular ambiguity. -/

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
  (((k * t : ℕ) : ℤ), ((2 * (k * t) : ℕ) : ℤ))

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

/-- Exact integer-kernel normal form. If both observed coordinates vanish
modulo 5k, then the input has the form k*(t, 2t+5s). This is the
congruence-level Smith normal form needed for the five-phase obstruction. -/
theorem kernel_phase_characterization (k : ℕ) (hk : 0 < k) (x y : ℤ) :
    (modEq (5 * k) (observe (x, y)).1 0 ∧
      modEq (5 * k) (observe (x, y)).2 0) ↔
      ∃ t s : ℤ,
        x = (k : ℤ) * t ∧
          y = 2 * (k : ℤ) * t + 5 * (k : ℤ) * s := by
  constructor
  · intro h
    have h1 := h.1
    have h2 := h.2
    simp [modEq, observe] at h1 h2
    rcases h1 with ⟨a, ha⟩
    rcases h2 with ⟨b, hb⟩
    refine ⟨-(2 * a + b), a, ?_, ?_⟩
    · push_cast at ha hb ⊢
      nlinarith
    · push_cast at ha hb ⊢
      nlinarith
  · rintro ⟨t, s, rfl, rfl⟩
    constructor
    · simp [modEq, observe]
      refine ⟨s, by ring⟩
    · simp [modEq, observe]
      refine ⟨-(t + 2 * s), by ring⟩

/-- Image characterization. An observed residue pair modulo 5k is realizable
exactly when its linear obstruction 2r+s vanishes modulo five. -/
theorem image_condition (k : ℕ) (hk : 0 < k) (r s : ℤ) :
    (∃ x y : ℤ,
      modEq (5 * k) (observe (x, y)).1 r ∧
        modEq (5 * k) (observe (x, y)).2 s) ↔
      modEq 5 (2 * r + s) 0 := by
  constructor
  · rintro ⟨x, y, h1, h2⟩
    simp [modEq, observe] at h1 h2
    rcases h1 with ⟨a, ha⟩
    rcases h2 with ⟨b, hb⟩
    unfold modEq
    refine ⟨-x - (k : ℤ) * (2 * a + b), ?_⟩
    push_cast at ha hb ⊢
    nlinarith
  · intro h
    simp [modEq] at h
    rcases h with ⟨q, hq⟩
    refine ⟨-(q), 2 * (-(q)) - r, ?_, ?_⟩
    · unfold modEq
      refine ⟨0, ?_⟩
      simp [observe]
    · unfold modEq
      refine ⟨0, ?_⟩
      simp [observe]
      nlinarith [hq]

/-- Specialization at the Robin cutoff modulus 5040 = 5 * 1008. The
phase ambiguity uses only the factor five; the factor seven contributes no
additional state in this observation. -/
theorem observe_phase_indistinguishable_5040 (t : ℕ) (z : ℤ × ℤ) :
    modEq 5040 (observe (pairAdd z (phaseShift 1008 t))).1 (observe z).1 ∧
      modEq 5040 (observe (pairAdd z (phaseShift 1008 t))).2 (observe z).2 := by
  simpa using observe_phase_indistinguishable 1008 t z

end D5.S3.Geometry.Hyperideal.FibonacciObservation
