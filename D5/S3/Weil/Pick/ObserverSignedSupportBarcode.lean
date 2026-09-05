/- GID: D5/S3/Weil/Pick/ObserverSignedSupportBarcode
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/ObserverSignedSupportBarcode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify observer-dependent negative signed support with open orbit intervals and count the resulting negative localized weights under positive masses. -/

import D5.S3.Weil.Pick.LocalizedStieltjesNevanlinnaKernel
import Mathlib.Tactic

/-!
# Observer-dependent signed-support barcode

For an orbit with transverse displacement `delta` and height `gamma`, the
observer at time `t` sees the signed support

`(t - gamma)^2 - delta^2`.

It is negative exactly on the open interval centered at `gamma` with radius
`|delta|`. With positive atomic mass, multiplication by the mass preserves this
sign test. On a finite orbit family, the number of negative localized weights
therefore equals the number of active barcode intervals.

This module counts diagonal localizing weights. It does not identify that count
with the negative index of a sampled Gram matrix; such an equality additionally
needs a full-rank congruence certificate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace D5.S3.Weil.Pick.ObserverSignedSupportBarcode

variable {Orbit : Type*} [Fintype Orbit] [DecidableEq Orbit]

/-- Observer-dependent signed support of one reflected orbit. -/
def observerSignedSupport (delta gamma time : ℝ) : ℝ :=
  (time - gamma) ^ 2 - delta ^ 2

/-- The orbit is active when the observer lies inside its open support interval. -/
def orbitActiveAt (delta gamma time : ℝ) : Prop :=
  |time - gamma| < |delta|

instance (delta gamma time : ℝ) :
    Decidable (orbitActiveAt delta gamma time) :=
  inferInstanceAs (Decidable (|time - gamma| < |delta|))

/-- The first localized diagonal weight: positive mass times signed support. -/
def observerLocalizedWeight
    (mass delta gamma time : ℝ) : ℝ :=
  mass * observerSignedSupport delta gamma time

/-- Number of active orbit intervals at one observation time. -/
def activeOrbitCount
    (delta gamma : Orbit → ℝ) (time : ℝ) : ℕ :=
  ((Finset.univ : Finset Orbit).filter
    (fun a => orbitActiveAt (delta a) (gamma a) time)).card

/-- Number of strictly negative localized atomic weights at one observation time. -/
def negativeLocalizedWeightCount
    (mass delta gamma : Orbit → ℝ) (time : ℝ) : ℕ :=
  ((Finset.univ : Finset Orbit).filter
    (fun a => observerLocalizedWeight
      (mass a) (delta a) (gamma a) time < 0)).card

/-- Signed support is negative exactly inside the corresponding barcode interval. -/
theorem observer_signed_support_neg_iff_active
    (delta gamma time : ℝ) :
    observerSignedSupport delta gamma time < 0 ↔
      orbitActiveAt delta gamma time := by
  unfold observerSignedSupport orbitActiveAt
  rw [sub_neg, sq_lt_sq]

/-- At the orbit center, signed support is the negative transverse square. -/
theorem observer_signed_support_at_center
    (delta gamma : ℝ) :
    observerSignedSupport delta gamma gamma = -(delta ^ 2) := by
  simp [observerSignedSupport]

/-- The center belongs to the active interval exactly for an off-axis orbit. -/
theorem orbit_active_at_center_iff
    (delta gamma : ℝ) :
    orbitActiveAt delta gamma gamma ↔ delta ≠ 0 := by
  simp [orbitActiveAt]

/-- A positive mass leaves the signed-support negativity test unchanged. -/
theorem observer_localized_weight_neg_iff_active
    (mass delta gamma time : ℝ) (hmass : 0 < mass) :
    observerLocalizedWeight mass delta gamma time < 0 ↔
      orbitActiveAt delta gamma time := by
  constructor
  · intro hnegative
    have hsigned : observerSignedSupport delta gamma time < 0 := by
      by_contra hnot
      have hsignedNonneg : 0 ≤ observerSignedSupport delta gamma time :=
        le_of_not_gt hnot
      exact (not_lt_of_ge (mul_nonneg hmass.le hsignedNonneg)) hnegative
    exact (observer_signed_support_neg_iff_active delta gamma time).1 hsigned
  · intro hactive
    exact mul_neg_of_pos_of_neg hmass
      ((observer_signed_support_neg_iff_active delta gamma time).2 hactive)

/-- For positive masses, negative localized weights and active barcode intervals
have exactly the same finite cardinality. -/
theorem negative_localized_weight_count_eq_active_orbit_count
    (mass delta gamma : Orbit → ℝ) (time : ℝ)
    (hmass : ∀ a, 0 < mass a) :
    negativeLocalizedWeightCount mass delta gamma time =
      activeOrbitCount delta gamma time := by
  have hfilter :
      (Finset.univ.filter
        (fun a : Orbit => observerLocalizedWeight
          (mass a) (delta a) (gamma a) time < 0)) =
      (Finset.univ.filter
        (fun a : Orbit => orbitActiveAt (delta a) (gamma a) time)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact observer_localized_weight_neg_iff_active
      (mass a) (delta a) (gamma a) time (hmass a)
  exact congrArg Finset.card hfilter

/-- Under positive masses, an active orbit exists exactly when some localized
atomic weight is negative. -/
theorem exists_active_orbit_iff_exists_negative_localized_weight
    (mass delta gamma : Orbit → ℝ) (time : ℝ)
    (hmass : ∀ a, 0 < mass a) :
    (∃ a, orbitActiveAt (delta a) (gamma a) time) ↔
      ∃ a, observerLocalizedWeight
        (mass a) (delta a) (gamma a) time < 0 := by
  constructor
  · rintro ⟨a, hactive⟩
    exact ⟨a, (observer_localized_weight_neg_iff_active
      (mass a) (delta a) (gamma a) time (hmass a)).2 hactive⟩
  · rintro ⟨a, hnegative⟩
    exact ⟨a, (observer_localized_weight_neg_iff_active
      (mass a) (delta a) (gamma a) time (hmass a)).1 hnegative⟩

#print axioms observer_signed_support_neg_iff_active
#print axioms observer_localized_weight_neg_iff_active
#print axioms negative_localized_weight_count_eq_active_orbit_count
#print axioms exists_active_orbit_iff_exists_negative_localized_weight

end D5.S3.Weil.Pick.ObserverSignedSupportBarcode
