/- GID: D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow
   generality: G
   mirror-B: D5/B/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite-dimensional additive tori carry linear quasiperiodic flows and an integer combination-frequency module. -/

import D5.S3.Dynamics.SpaceTime.CommutingSpaceTimeAction
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Tactic

/-!
# Quasiperiodic torus flow

A finite frequency vector `omega` drives the additive torus by

`theta(t)_j = theta_j + t omega_j mod 1`.

The flow satisfies the exact additive time law and is reversible by negating
time.  Integer mode vectors form a frequency module through the pairing

`n dot omega = sum_j n_j omega_j`.

This finite algebraic layer distinguishes exact resonance, where the pairing
vanishes, from nonresonant and Diophantine estimates.  Density, unique
ergodicity, small-divisor bounds, and spectral convergence require additional
hypotheses and are not asserted here.
-/

/- Library-search audit trail (2026-09-01):
   * Existing golden sampling modules treat one distinguished logarithmic
     frequency scale.
   * `CommutingSpaceTimeAction` owns the abstract joint action law.
   * Repository search found no finite torus flow paired with an integer
     combination-frequency module.
   * Pinned Mathlib supplies `AddCircle`, pointwise finite products, and finite
     sums. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Dynamics.SpaceTime.QuasiperiodicTorusFlow

noncomputable section

universe u

/-- Finite-dimensional unit additive torus. -/
abbrev PhaseTorus (Index : Type u) := Index → AddCircle (1 : ℝ)

variable {Index : Type u}

/-- Linear flow of a real frequency vector on the unit additive torus. -/
def quasiperiodicFlow
    (frequency : Index → ℝ) (time : ℝ)
    (phase : PhaseTorus Index) : PhaseTorus Index :=
  fun index =>
    phase index + (((time * frequency index : ℝ)) : AddCircle (1 : ℝ))

/-- Zero time fixes every torus phase. -/
theorem quasiperiodicFlow_zero
    (frequency : Index → ℝ) (phase : PhaseTorus Index) :
    quasiperiodicFlow frequency 0 phase = phase := by
  funext index
  simp [quasiperiodicFlow]

/-- Additive time parameters compose exactly. -/
theorem quasiperiodicFlow_add
    (frequency : Index → ℝ) (first second : ℝ)
    (phase : PhaseTorus Index) :
    quasiperiodicFlow frequency (first + second) phase =
      quasiperiodicFlow frequency first
        (quasiperiodicFlow frequency second phase) := by
  funext index
  change
    phase index +
        ((((first + second) * frequency index : ℝ)) : AddCircle (1 : ℝ)) =
      (phase index +
          (((second * frequency index : ℝ)) : AddCircle (1 : ℝ))) +
        (((first * frequency index : ℝ)) : AddCircle (1 : ℝ))
  rw [add_mul, AddCircle.coe_add]
  abel

/-- Negating time reverses the torus flow. -/
theorem quasiperiodicFlow_neg_cancel
    (frequency : Index → ℝ) (time : ℝ)
    (phase : PhaseTorus Index) :
    quasiperiodicFlow frequency (-time)
        (quasiperiodicFlow frequency time phase) = phase := by
  rw [← quasiperiodicFlow_add]
  simp [quasiperiodicFlow_zero]

/-- One coordinate evolves by its own circle rotation. -/
theorem quasiperiodicFlow_apply
    (frequency : Index → ℝ) (time : ℝ)
    (phase : PhaseTorus Index) (index : Index) :
    quasiperiodicFlow frequency time phase index =
      phase index +
        (((time * frequency index : ℝ)) : AddCircle (1 : ℝ)) := by
  rfl

section Finite

variable [Fintype Index]

/-- Integer combination frequency paired with a finite frequency vector. -/
def combinationFrequency
    (frequency : Index → ℝ) (mode : Index → ℤ) : ℝ :=
  ∑ index, (mode index : ℝ) * frequency index

/-- The zero mode has zero combination frequency. -/
theorem combinationFrequency_zero
    (frequency : Index → ℝ) :
    combinationFrequency frequency 0 = 0 := by
  simp [combinationFrequency]

/-- Combination frequency is additive in the integer mode. -/
theorem combinationFrequency_add
    (frequency : Index → ℝ) (first second : Index → ℤ) :
    combinationFrequency frequency (first + second) =
      combinationFrequency frequency first +
        combinationFrequency frequency second := by
  simp [combinationFrequency, add_mul, Finset.sum_add_distrib]

/-- Negating a mode negates its combination frequency. -/
theorem combinationFrequency_neg
    (frequency : Index → ℝ) (mode : Index → ℤ) :
    combinationFrequency frequency (-mode) =
      -combinationFrequency frequency mode := by
  simp [combinationFrequency, Finset.sum_neg_distrib]

/-- Exact resonance of an integer mode. -/
def IsResonantMode
    (frequency : Index → ℝ) (mode : Index → ℤ) : Prop :=
  combinationFrequency frequency mode = 0

/-- The zero mode is always resonant. -/
theorem zero_isResonantMode
    (frequency : Index → ℝ) :
    IsResonantMode frequency 0 := by
  exact combinationFrequency_zero frequency

/-- Resonant modes are closed under addition. -/
theorem isResonantMode_add
    (frequency : Index → ℝ) {first second : Index → ℤ}
    (hFirst : IsResonantMode frequency first)
    (hSecond : IsResonantMode frequency second) :
    IsResonantMode frequency (first + second) := by
  rw [IsResonantMode, combinationFrequency_add, hFirst, hSecond, add_zero]

/-- Resonant modes are closed under negation. -/
theorem isResonantMode_neg
    (frequency : Index → ℝ) {mode : Index → ℤ}
    (hMode : IsResonantMode frequency mode) :
    IsResonantMode frequency (-mode) := by
  rw [IsResonantMode, combinationFrequency_neg, hMode, neg_zero]

end Finite

example :
    quasiperiodicFlow (fun _ : Unit => 1) 0 (fun _ => 0) =
      (fun _ => 0) := by
  exact quasiperiodicFlow_zero _ _

#print axioms quasiperiodicFlow_zero
#print axioms quasiperiodicFlow_add
#print axioms quasiperiodicFlow_neg_cancel
#print axioms combinationFrequency_add
#print axioms combinationFrequency_neg
#print axioms isResonantMode_add
#print axioms isResonantMode_neg

end

end D5.S3.Dynamics.SpaceTime.QuasiperiodicTorusFlow
