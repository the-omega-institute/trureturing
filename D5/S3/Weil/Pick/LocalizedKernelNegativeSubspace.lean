/- GID: D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/LocalizedKernelNegativeSubspace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct the active-orbit coordinate space, identify its cardinality with the signed-support barcode count, and prove its localized diagonal quadratic form is strictly negative away from zero. -/

import D5.S3.Weil.Pick.ObserverSignedSupportBarcode
import Mathlib.Tactic

/-!
# Localized-kernel negative coordinate subspace

The active observer intervals select a finite coordinate type. Positive masses
make every selected localized weight strictly negative, so the diagonal
quadratic form on this coordinate space is strictly negative away from zero.
The cardinality of the coordinate type is exactly the active-orbit barcode
count.

A target sampled kernel inherits this negative subspace whenever one supplies an
injective linear realization whose quadratic readout is exact. This is the
precise finite condition needed before converting the coordinate count into a
sampled-Gram negative-index statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace D5.S3.Weil.Pick.LocalizedKernelNegativeSubspace

open D5.S3.Weil.Pick.ObserverSignedSupportBarcode

variable {Orbit : Type*} [Fintype Orbit] [DecidableEq Orbit]

/-- Subtype of orbit labels whose signed support is negative at the observation
time. -/
def ActiveOrbit
    (delta gamma : Orbit → ℝ) (time : ℝ) :=
  {a : Orbit // orbitActiveAt (delta a) (gamma a) time}

instance (delta gamma : Orbit → ℝ) (time : ℝ) :
    Fintype (ActiveOrbit delta gamma time) :=
  Subtype.fintype _

/-- Combinatorial negative index of the active diagonal coordinate model. -/
def activeCoordinateNegativeIndex
    (delta gamma : Orbit → ℝ) (time : ℝ) : ℕ :=
  Fintype.card (ActiveOrbit delta gamma time)

/-- The active-orbit subtype is equivalent to the filtered universal finset used
by the barcode count. -/
noncomputable def activeOrbitEquivFiltered
    (delta gamma : Orbit → ℝ) (time : ℝ) :
    ActiveOrbit delta gamma time ≃
      ↥((Finset.univ : Finset Orbit).filter
        (fun a => orbitActiveAt (delta a) (gamma a) time)) where
  toFun a := ⟨a.1, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact a.2⟩
  invFun a := ⟨a.1, by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using a.2⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext rfl

/-- The coordinate-model negative index is exactly the active barcode count. -/
theorem active_coordinate_negative_index_eq_active_orbit_count
    (delta gamma : Orbit → ℝ) (time : ℝ) :
    activeCoordinateNegativeIndex delta gamma time =
      activeOrbitCount delta gamma time := by
  classical
  change Fintype.card (ActiveOrbit delta gamma time) =
    ((Finset.univ : Finset Orbit).filter
      (fun a => orbitActiveAt (delta a) (gamma a) time)).card
  exact Fintype.card_subtype
    (fun a => orbitActiveAt (delta a) (gamma a) time)

/-- Diagonal localized quadratic form on active-orbit coordinates. -/
def activeCoordinateQuadratic
    (mass delta gamma : Orbit → ℝ) (time : ℝ)
    (v : ActiveOrbit delta gamma time → ℝ) : ℝ :=
  ∑ a, observerLocalizedWeight
    (mass a.1) (delta a.1) (gamma a.1) time * (v a) ^ 2

/-- Every active coordinate carries a strictly negative localized weight under
positive masses. -/
theorem active_coordinate_weight_neg
    (mass delta gamma : Orbit → ℝ) (time : ℝ)
    (hmass : ∀ a, 0 < mass a)
    (a : ActiveOrbit delta gamma time) :
    observerLocalizedWeight
      (mass a.1) (delta a.1) (gamma a.1) time < 0 := by
  exact (observer_localized_weight_neg_iff_active
    (mass a.1) (delta a.1) (gamma a.1) time (hmass a.1)).2 a.2

/-- The active-coordinate quadratic form is strictly negative on every nonzero
coordinate vector. -/
theorem active_coordinate_quadratic_neg
    (mass delta gamma : Orbit → ℝ) (time : ℝ)
    (hmass : ∀ a, 0 < mass a)
    (v : ActiveOrbit delta gamma time → ℝ)
    (hv : v ≠ 0) :
    activeCoordinateQuadratic mass delta gamma time v < 0 := by
  classical
  have hexists : ∃ a, v a ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hv
    funext a
    exact hnone a
  obtain ⟨a0, ha0⟩ := hexists
  let term : ActiveOrbit delta gamma time → ℝ := fun a =>
    observerLocalizedWeight
      (mass a.1) (delta a.1) (gamma a.1) time * (v a) ^ 2
  have hnonpos : ∀ a, term a ≤ 0 := by
    intro a
    exact mul_nonpos_of_nonpos_of_nonneg
      (le_of_lt (active_coordinate_weight_neg
        mass delta gamma time hmass a))
      (sq_nonneg (v a))
  have hstrict : term a0 < 0 := by
    exact mul_neg_of_neg_of_pos
      (active_coordinate_weight_neg mass delta gamma time hmass a0)
      (sq_pos_of_ne_zero ha0)
  change (∑ a : ActiveOrbit delta gamma time, term a) < 0
  have hsum :
      (∑ a ∈ (Finset.univ : Finset (ActiveOrbit delta gamma time)), term a) <
        ∑ _a ∈ (Finset.univ : Finset (ActiveOrbit delta gamma time)), (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro a _ha
      exact hnonpos a
    · exact ⟨a0, Finset.mem_univ a0, hstrict⟩
  simpa using hsum

variable {Target : Type*} [AddCommGroup Target] [Module ℝ Target]

/-- Injective exact realization of the active coordinate model inside a target
quadratic domain. Full-rank Cauchy sampling is one possible source of such a
realization. -/
structure ExactActiveCoordinateTransport
    (mass delta gamma : Orbit → ℝ) (time : ℝ) where
  embed : (ActiveOrbit delta gamma time → ℝ) →ₗ[ℝ] Target
  injective : Function.Injective embed
  quadratic : Target → ℝ
  exact_readout : ∀ v,
    quadratic (embed v) =
      activeCoordinateQuadratic mass delta gamma time v

/-- Exact transport carries every nonzero active coordinate vector to a
strictly negative target quadratic value. -/
theorem exact_transport_gives_negative_target_value
    (mass delta gamma : Orbit → ℝ) (time : ℝ)
    (hmass : ∀ a, 0 < mass a)
    (transport : ExactActiveCoordinateTransport
      (Target := Target) mass delta gamma time)
    (v : ActiveOrbit delta gamma time → ℝ)
    (hv : v ≠ 0) :
    transport.quadratic (transport.embed v) < 0 := by
  rw [transport.exact_readout v]
  exact active_coordinate_quadratic_neg
    mass delta gamma time hmass v hv

/-- Injectivity ensures that nonzero active coordinates remain nonzero after
transport into the target space. -/
theorem exact_transport_preserves_nonzero
    (mass delta gamma : Orbit → ℝ) (time : ℝ)
    (transport : ExactActiveCoordinateTransport
      (Target := Target) mass delta gamma time)
    (v : ActiveOrbit delta gamma time → ℝ)
    (hv : v ≠ 0) :
    transport.embed v ≠ 0 := by
  intro hzero
  apply hv
  apply transport.injective
  simpa using hzero

#print axioms active_coordinate_negative_index_eq_active_orbit_count
#print axioms active_coordinate_quadratic_neg
#print axioms exact_transport_gives_negative_target_value
#print axioms exact_transport_preserves_nonzero

end D5.S3.Weil.Pick.LocalizedKernelNegativeSubspace
