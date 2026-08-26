/- GID: D5/S3/ConceptDynamics/ObservationTopology/InvolutionDescent
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/InvolutionDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A transformation descends through a surjective readout exactly when it preserves readout fibers. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib supplies surjections, function extensionality, and involutions.
   * Repository searches found no accepted arbitrary-readout descent theorem with
     existence, uniqueness, involution transport, and fixed-point visibility.
   * The construction uses an explicit chosen section only inside the proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.InvolutionDescent

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- A transformation is stable on readout fibers when equal readouts remain equal
 after applying the transformation. -/
def KernelStable {X Coordinate : Type*}
    (readout : Concept X Coordinate) (transform : X → X) : Prop :=
  ∀ ⦃x y⦄, readout x = readout y →
    readout (transform x) = readout (transform y)

/-- For a surjective readout, kernel stability is exactly the existence of a
 transformation on the quotient coordinates. -/
theorem kernelStable_iff_exists_descended
    {X Coordinate : Type*} (readout : Concept X Coordinate)
    (transform : X → X) (surjective : Function.Surjective readout) :
    KernelStable readout transform ↔
      ∃ descended : Coordinate → Coordinate,
        descended ∘ readout = readout ∘ transform := by
  classical
  constructor
  · intro stable
    let sect : Coordinate → X := fun coordinate =>
      Classical.choose (surjective coordinate)
    have section_spec : ∀ coordinate, readout (sect coordinate) = coordinate :=
      fun coordinate => Classical.choose_spec (surjective coordinate)
    let descended : Coordinate → Coordinate := fun coordinate =>
      readout (transform (sect coordinate))
    refine ⟨descended, ?_⟩
    funext x
    change readout (transform (sect (readout x))) =
      readout (transform x)
    exact stable (section_spec (readout x))
  · rintro ⟨descended, factorization⟩ x y sameReadout
    have atX := congrFun factorization x
    have atY := congrFun factorization y
    change descended (readout x) = readout (transform x) at atX
    change descended (readout y) = readout (transform y) at atY
    calc
      readout (transform x) = descended (readout x) := atX.symm
      _ = descended (readout y) := congrArg descended sameReadout
      _ = readout (transform y) := atY

/-- A descended transformation is unique on a surjective coordinate space. -/
theorem descended_unique
    {X Coordinate : Type*} (readout : Concept X Coordinate)
    (transform : X → X) (surjective : Function.Surjective readout)
    {first second : Coordinate → Coordinate}
    (firstFactors : first ∘ readout = readout ∘ transform)
    (secondFactors : second ∘ readout = readout ∘ transform) :
    first = second := by
  funext coordinate
  rcases surjective coordinate with ⟨x, rfl⟩
  have firstAtX := congrFun firstFactors x
  have secondAtX := congrFun secondFactors x
  exact firstAtX.trans secondAtX.symm

/-- Involutivity descends through a surjective readout. -/
theorem involutive_descends
    {X Coordinate : Type*} (readout : Concept X Coordinate)
    (transform : X → X) (descended : Coordinate → Coordinate)
    (surjective : Function.Surjective readout)
    (transformInvolutive : Function.Involutive transform)
    (factorization : descended ∘ readout = readout ∘ transform) :
    Function.Involutive descended := by
  intro coordinate
  rcases surjective coordinate with ⟨x, rfl⟩
  have atX := congrFun factorization x
  have atTransformX := congrFun factorization (transform x)
  change descended (readout x) = readout (transform x) at atX
  change descended (readout (transform x)) =
    readout (transform (transform x)) at atTransformX
  rw [atX, atTransformX, transformInvolutive x]

/-- A descended fixed point is exactly a collapsed transformation orbit. -/
theorem descended_fixed_iff_orbit_collapsed
    {X Coordinate : Type*} (readout : Concept X Coordinate)
    (transform : X → X) (descended : Coordinate → Coordinate)
    (factorization : descended ∘ readout = readout ∘ transform)
    (x : X) :
    descended (readout x) = readout x ↔
      readout (transform x) = readout x := by
  have atX := congrFun factorization x
  change descended (readout x) = readout (transform x) at atX
  rw [atX]

/-- The descended map is fixed-point free exactly when no source orbit is
 collapsed by the readout. -/
theorem descended_fixedPointFree_iff
    {X Coordinate : Type*} (readout : Concept X Coordinate)
    (transform : X → X) (descended : Coordinate → Coordinate)
    (surjective : Function.Surjective readout)
    (factorization : descended ∘ readout = readout ∘ transform) :
    (∀ coordinate, descended coordinate ≠ coordinate) ↔
      ∀ x, readout (transform x) ≠ readout x := by
  constructor
  · intro descendedFree x collapsed
    exact descendedFree (readout x)
      ((descended_fixed_iff_orbit_collapsed
        readout transform descended factorization x).2 collapsed)
  · intro noCollapsedOrbit coordinate fixed
    rcases surjective coordinate with ⟨x, rfl⟩
    exact noCollapsedOrbit x
      ((descended_fixed_iff_orbit_collapsed
        readout transform descended factorization x).1 fixed)

/-- A bijective observation preserves fixed-point freeness of the descended map. -/
theorem fixedPointFree_descends_through_bijection
    {X Coordinate : Type*} (readout : Concept X Coordinate)
    (transform : X → X) (descended : Coordinate → Coordinate)
    (bijective : Function.Bijective readout)
    (transformFree : ∀ x, transform x ≠ x)
    (factorization : descended ∘ readout = readout ∘ transform) :
    ∀ coordinate, descended coordinate ≠ coordinate := by
  apply (descended_fixedPointFree_iff
    readout transform descended bijective.2 factorization).2
  intro x collapsed
  exact transformFree x (bijective.1 collapsed)

/-- The descended transformation is the identity exactly when the source
 transformation is invisible to the readout. -/
theorem descended_eq_id_iff_invisible
    {X Coordinate : Type*} (readout : Concept X Coordinate)
    (transform : X → X) (descended : Coordinate → Coordinate)
    (surjective : Function.Surjective readout)
    (factorization : descended ∘ readout = readout ∘ transform) :
    descended = id ↔ readout ∘ transform = readout := by
  constructor
  · intro descendedIdentity
    funext x
    have atX := congrFun factorization x
    change descended (readout x) = readout (transform x) at atX
    rw [descendedIdentity] at atX
    exact atX.symm
  · intro invisible
    funext coordinate
    rcases surjective coordinate with ⟨x, rfl⟩
    have atX := congrFun factorization x
    have invisibleAtX := congrFun invisible x
    change descended (readout x) = readout (transform x) at atX
    change readout (transform x) = readout x at invisibleAtX
    exact atX.trans invisibleAtX

#print axioms kernelStable_iff_exists_descended
#print axioms involutive_descends
#print axioms descended_fixedPointFree_iff

end D5.S3.ConceptDynamics.ObservationTopology.InvolutionDescent
