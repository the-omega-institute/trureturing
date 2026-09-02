/- GID: D5/S3/Observer/AgencyHolonomy/ScalarMemoryBlindness
   generality: I
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/ScalarMemoryBlindness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Scalar Euler behavior forgets every hidden-memory coordinate. -/

import D5.S1.Scale.FibonacciEigen
import D5.S3.Analytic.EulerGerm.GoldenLocalFactor
import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/- Library-search audit trail (2026-09-02):
   * D5 body-shape searches found the canonical `germLocalFactor`,
     `fibonacciSubstitution`, `runWord`, and `completionProjection`, all reused
     below. They found no owner for the three residual factors, their
     triangular memory update, or the resulting scalar-blind completion.
   * Pinned Mathlib searches for finite-word scalar readout equality and
     hidden-memory behavior quotients found no exact theorem.
   * Searches of every installed non-Mathlib Lean package found no theorem
     about controlled scalar behavior or hidden prime memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.ScalarMemoryBlindness

open D5.S1.Scale
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open scoped goldenRatio Matrix

noncomputable section

/-- The source's three residual prime-local factors, indexed by layers zero,
one, and two. -/
noncomputable def layerLocalFactor
    (depth : Fin 3) (s : ℂ) (p : Nat.Primes) : ℂ :=
  if depth = 0 then
    germLocalFactor s p
  else if depth = 1 then
    (1 - (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))) *
      germLocalFactor s p
  else
    ((1 - (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) /
        (1 + (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))) *
      germLocalFactor s p

/-- A prime step applies the Fibonacci substitution to memory, adds the
source channel forcing, and updates the scalar without reading memory. -/
noncomputable def scalarMemoryUpdate
    (depth : Fin 3) (s : ℂ) (channel : Nat.Primes -> Fin 2 -> ℂ)
    (p : Nat.Primes) (state : (Fin 2 -> ℂ) × ℂ) :
    (Fin 2 -> ℂ) × ℂ :=
  let factor := layerLocalFactor depth s p
  ((fibonacciSubstitution.map Complex.ofRealHom) *ᵥ state.1 +
      state.2 • ((factor - 1) • channel p),
    factor * state.2)

/-- Equal initial scalar coordinates have equal scalar readouts after every
finite prime word. Hence the canonical controlled-behavior completion
identifies every pair of states in the full affine memory fiber over `z`. -/
theorem scalar_memory_blindness
    (depth : Fin 3) (s : ℂ) (channel : Nat.Primes -> Fin 2 -> ℂ) :
    ∀ z z' : ℂ, z = z' ->
      (∀ (word : List Nat.Primes) (memory memory' : Fin 2 -> ℂ),
        Prod.snd
            (runWord (scalarMemoryUpdate depth s channel) word (memory, z)) =
          Prod.snd
            (runWord (scalarMemoryUpdate depth s channel) word (memory', z'))) ∧
      (∀ memory memory' : Fin 2 -> ℂ,
        completionProjection (scalarMemoryUpdate depth s channel) Prod.snd
            (memory, z) =
          completionProjection (scalarMemoryUpdate depth s channel) Prod.snd
            (memory', z)) := by
  have blind : ∀ (word : List Nat.Primes) (memory memory' : Fin 2 -> ℂ)
      (z z' : ℂ), z = z' ->
      Prod.snd
          (runWord (scalarMemoryUpdate depth s channel) word (memory, z)) =
        Prod.snd
          (runWord (scalarMemoryUpdate depth s channel) word (memory', z')) := by
    intro word
    induction word with
    | nil =>
        intro memory memory' z z' hz
        simpa [runWord] using hz
    | cons p word ih =>
        intro memory memory' z z' hz
        simp only [runWord]
        apply ih
        simp [hz]
  intro z z' hz
  refine ⟨?_, ?_⟩
  · intro word memory memory'
    exact blind word memory memory' z z' hz
  · intro memory memory'
    apply Quotient.sound
    funext word
    simpa [controlledBehavior] using blind word memory memory' z z rfl

#print axioms layerLocalFactor
#print axioms scalarMemoryUpdate
#print axioms scalar_memory_blindness

end

end D5.S3.Observer.AgencyHolonomy.ScalarMemoryBlindness
