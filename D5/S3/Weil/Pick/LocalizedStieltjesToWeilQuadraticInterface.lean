/- GID: D5/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Isolate the exact-readout condition that transports an active localized Stieltjes orbit into a negative Weil quadratic test. -/

import D5.S3.Weil.Pick.ObserverSignedSupportBarcode
import Mathlib.Tactic

/-!
# Localized Stieltjes to Weil quadratic interface

This module records the precise missing bridge between the finite signed-support
barcode and a Weil quadratic form. A transport consists of test objects and an
exact readout identity equating the Weil value of each realized test with the
corresponding localized atomic weight.

Once that identity is supplied, positive mass and an active orbit force a
strictly negative Weil value. The structure does not construct the realization,
control archimedean or pole terms, or assert that the completed Xi function
provides such a transport.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Pick.LocalizedStieltjesToWeilQuadraticInterface

open D5.S3.Weil.Pick.ObserverSignedSupportBarcode

variable {Orbit Test : Type*}

/-- Exact realization of localized orbit weights by a target Weil quadratic
functional. The realization itself is the remaining analytic obligation. -/
structure ExactLocalizedStieltjesWeilTransport
    (mass delta gamma : Orbit → ℝ) (time : ℝ) where
  test : Orbit → Test
  weilQuadratic : Test → ℝ
  exact_readout : ∀ a,
    weilQuadratic (test a) =
      observerLocalizedWeight (mass a) (delta a) (gamma a) time

/-- An active positive-mass orbit yields a negative target quadratic value. -/
theorem active_orbit_gives_negative_weil_value
    (mass delta gamma : Orbit → ℝ) (time : ℝ)
    (transport : ExactLocalizedStieltjesWeilTransport
      (Test := Test) mass delta gamma time)
    (a : Orbit) (hmass : 0 < mass a)
    (hactive : orbitActiveAt (delta a) (gamma a) time) :
    transport.weilQuadratic (transport.test a) < 0 := by
  rw [transport.exact_readout a]
  exact (observer_localized_weight_neg_iff_active
    (mass a) (delta a) (gamma a) time hmass).2 hactive

/-- If any positive-mass orbit is active, the exact transport produces some
strictly negative Weil test. -/
theorem exists_negative_weil_test_of_active_orbit
    (mass delta gamma : Orbit → ℝ) (time : ℝ)
    (transport : ExactLocalizedStieltjesWeilTransport
      (Test := Test) mass delta gamma time)
    (hmass : ∀ a, 0 < mass a)
    (hactive : ∃ a, orbitActiveAt (delta a) (gamma a) time) :
    ∃ f : Test, transport.weilQuadratic f < 0 := by
  obtain ⟨a, ha⟩ := hactive
  exact ⟨transport.test a,
    active_orbit_gives_negative_weil_value
      mass delta gamma time transport a (hmass a) ha⟩

/-- A nonnegative target quadratic form rules out every active orbit whenever
an exact positive-mass transport exists. -/
theorem no_active_orbit_of_nonnegative_weil_form
    (mass delta gamma : Orbit → ℝ) (time : ℝ)
    (transport : ExactLocalizedStieltjesWeilTransport
      (Test := Test) mass delta gamma time)
    (hmass : ∀ a, 0 < mass a)
    (hweil : ∀ f : Test, 0 ≤ transport.weilQuadratic f) :
    ∀ a, ¬ orbitActiveAt (delta a) (gamma a) time := by
  intro a hactive
  exact (not_lt_of_ge (hweil (transport.test a)))
    (active_orbit_gives_negative_weil_value
      mass delta gamma time transport a (hmass a) hactive)

#print axioms active_orbit_gives_negative_weil_value
#print axioms exists_negative_weil_test_of_active_orbit
#print axioms no_active_orbit_of_nonnegative_weil_form

end D5.S3.Weil.Pick.LocalizedStieltjesToWeilQuadraticInterface
