/- GID: D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fourier characters create unitary log-frequency time flow while scalar products forget order. -/

import D5.S3.Observer.AgencyHolonomy.FiniteHolonomyEnergy
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Prime-frequency Fourier phase flow

The kernel `exp (-i t omega)` is simultaneously an additive character in time
and in frequency. It has unit norm, so a finite family of such channels moves
on a torus. Specializing `omega` to `log p` gives the phase carried by the
prime channel in `p^(-sigma-it)`.

This file also records a sharp boundary between Fourier time and observer
chronology. A scalar ordered product of phase characters collapses to the
character of the summed frequencies. Consequently the scalar Fourier layer
forgets the order of the supplied frequency list. Time is already present as
the variable dual to frequency; order becomes observable only after a
noncommutative or memory-bearing lift.

The finite synthesis theorem gives the exact time-shift law and the standard
triangle bound by the total amplitude norm. No Fourier inversion, Plancherel
theorem, time orientation, irreversibility, prime-zero domination, or zero
location statement is asserted here.
-/

/- Library-search audit trail (2026-08-30):
   * Repository searches for `fourierPhase`, `finiteFourierSynthesis`, and
     `primeFrequencyPhaseFlow` found no existing owner of this exact node.
   * Pinned Mathlib supplies `Complex.exp_add`, `Complex.norm_exp`, finite sums,
     and the triangle inequality used below.
   * The ordered-product collapse and its interpretation as loss of scalar
     sequence order are proved locally rather than imported as a narrative
     claim. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow

noncomputable section

universe u

/-- The unitary Fourier character with angular frequency `frequency`, evaluated
at the real parameter `time`. -/
noncomputable def fourierPhase (frequency time : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (time : ℂ) * (frequency : ℂ))

/-- The logarithmic phase of a natural-number address. Prime addresses recover
`exp (-i t log p)`, the oscillatory part of `p^(-sigma-it)`. -/
noncomputable def logAddressPhase (address : ℕ) (time : ℝ) : ℂ :=
  fourierPhase (Real.log (address : ℝ)) time

/-- Finite Fourier synthesis from complex amplitudes and real frequencies. -/
noncomputable def finiteFourierSynthesis
    {ι : Type u} [Fintype ι]
    (amplitude : ι → ℂ) (frequency : ι → ℝ) (time : ℝ) : ℂ :=
  ∑ p, amplitude p * fourierPhase (frequency p) time

/-- The scalar phase product along a listed sequence of frequencies. -/
noncomputable def orderedPhaseProduct
    (frequencies : List ℝ) (time : ℝ) : ℂ :=
  (frequencies.map fun frequency => fourierPhase frequency time).prod

private theorem fourierPhase_add_time
    (frequency time shift : ℝ) :
    fourierPhase frequency (time + shift) =
      fourierPhase frequency time * fourierPhase frequency shift := by
  unfold fourierPhase
  rw [show
      -Complex.I * ((time + shift : ℝ) : ℂ) * (frequency : ℂ) =
        (-Complex.I * (time : ℂ) * (frequency : ℂ)) +
          (-Complex.I * (shift : ℂ) * (frequency : ℂ)) by
    push_cast
    ring]
  rw [Complex.exp_add]

private theorem fourierPhase_add_frequency
    (frequency other time : ℝ) :
    fourierPhase (frequency + other) time =
      fourierPhase frequency time * fourierPhase other time := by
  unfold fourierPhase
  rw [show
      -Complex.I * (time : ℂ) * ((frequency + other : ℝ) : ℂ) =
        (-Complex.I * (time : ℂ) * (frequency : ℂ)) +
          (-Complex.I * (time : ℂ) * (other : ℂ)) by
    push_cast
    ring]
  rw [Complex.exp_add]

private theorem norm_fourierPhase (frequency time : ℝ) :
    ‖fourierPhase frequency time‖ = 1 := by
  simp [fourierPhase, Complex.norm_exp, Complex.mul_re]

private theorem fourierPhase_time_frequency_symmetry
    (frequency time : ℝ) :
    fourierPhase frequency time = fourierPhase time frequency := by
  unfold fourierPhase
  congr 1
  ring

/--
The Fourier kernel is a unitary additive character in both variables. Time and
frequency enter through the same bilinear pairing, although they retain
different semantic roles in an application.
-/
theorem fourier_phase_character_laws
    (frequency other time shift : ℝ) :
    fourierPhase frequency 0 = 1 ∧
    fourierPhase frequency (time + shift) =
      fourierPhase frequency time * fourierPhase frequency shift ∧
    fourierPhase (frequency + other) time =
      fourierPhase frequency time * fourierPhase other time ∧
    ‖fourierPhase frequency time‖ = 1 ∧
    fourierPhase frequency time = fourierPhase time frequency := by
  constructor
  · simp [fourierPhase]
  constructor
  · exact fourierPhase_add_time frequency time shift
  constructor
  · exact fourierPhase_add_frequency frequency other time
  constructor
  · exact norm_fourierPhase frequency time
  · exact fourierPhase_time_frequency_symmetry frequency time

/--
A scalar product of Fourier phases depends only on the sum of the listed
frequencies. Thus permutation or chronology information is absent from this
commutative scalar layer.
-/
theorem ordered_phase_product_collapse
    (frequencies : List ℝ) (time : ℝ) :
    orderedPhaseProduct frequencies time =
      fourierPhase frequencies.sum time := by
  induction frequencies with
  | nil => simp [orderedPhaseProduct, fourierPhase]
  | cons frequency frequencies inductionHypothesis =>
      calc
        orderedPhaseProduct (frequency :: frequencies) time =
            fourierPhase frequency time *
              orderedPhaseProduct frequencies time := by
          simp [orderedPhaseProduct]
        _ = fourierPhase frequency time *
              fourierPhase frequencies.sum time := by
          rw [inductionHypothesis]
        _ = fourierPhase (frequency + frequencies.sum) time :=
          (fourierPhase_add_frequency
            frequency frequencies.sum time).symm
        _ = fourierPhase (frequency :: frequencies).sum time := by
          rfl

/--
Finite Fourier synthesis obeys the exact time-shift character law and is
bounded in norm by the sum of the amplitude norms.
-/
theorem finite_fourier_synthesis_laws
    {ι : Type u} [Fintype ι]
    (amplitude : ι → ℂ) (frequency : ι → ℝ) (time shift : ℝ) :
    finiteFourierSynthesis amplitude frequency (time + shift) =
      ∑ p,
        (amplitude p * fourierPhase (frequency p) time) *
          fourierPhase (frequency p) shift ∧
    ‖finiteFourierSynthesis amplitude frequency time‖ ≤
      ∑ p, ‖amplitude p‖ := by
  classical
  constructor
  · unfold finiteFourierSynthesis
    apply Finset.sum_congr rfl
    intro p hp
    rw [fourierPhase_add_time]
    ring
  · unfold finiteFourierSynthesis
    calc
      ‖∑ p, amplitude p * fourierPhase (frequency p) time‖ ≤
          ∑ p, ‖amplitude p * fourierPhase (frequency p) time‖ :=
        norm_sum_le _ _
      _ = ∑ p, ‖amplitude p‖ := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [norm_mul, norm_fourierPhase, mul_one]

#print axioms fourier_phase_character_laws
#print axioms ordered_phase_product_collapse
#print axioms finite_fourier_synthesis_laws

end

end D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
