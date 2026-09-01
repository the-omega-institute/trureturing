/- GID: D5/S3/Observer/Sheaf/ObserverGluingObstruction
   generality: G
   mirror-B: D5/B/S3/Observer/Sheaf/ObserverGluingObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: First observer cohomology is the quotient of compatible edge defects by globally correctable coboundaries. -/

import D5.S3.Observer.Sheaf.ObserverSheafLaplacian
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Tactic

/-!
# Finite observer gluing obstruction

A finite observer cochain complex consists of linear maps

`C⁰ --delta0--> C¹ --delta1--> C²`

with `delta1 * delta0 = 0`.  First cocycles are edge mismatch families closed
by `delta1`; first coboundaries are those produced by one global zero-cochain.
The first observer cohomology is the quotient of the cocycle module by the
coboundary module.

A cocycle class vanishes exactly when the mismatch admits a global correction.
A nonzero class is therefore a precise finite gluing obstruction.

This module gives finite linear cohomology.  It does not prove comparison with
Cech or derived sheaf cohomology on an arbitrary site, nor any infinite Hodge
theorem.
-/

/- Library-search audit trail (2026-09-01):
   * `SheafPairwiseEqualizer` owns degree-zero categorical gluing.
   * `FiniteObserverSheaf` owns the finite zero-to-one coboundary and compatible
     sections.
   * `ObserverSheafLaplacian` owns the degree-zero defect energy.
   * Repository search found no first-cohomology quotient for observer
     mismatch classes.
   * Pinned Mathlib supplies linear-map kernels, ranges, submodule quotients,
     and the quotient zero criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Sheaf.ObserverGluingObstruction

universe u v w x

/-- A finite three-term observer cochain complex. -/
structure ObserverCochainComplex
    (R : Type u) (C0 : Type v) (C1 : Type w) (C2 : Type x)
    [CommRing R]
    [AddCommGroup C0] [Module R C0]
    [AddCommGroup C1] [Module R C1]
    [AddCommGroup C2] [Module R C2] where
  delta0 : C0 →ₗ[R] C1
  delta1 : C1 →ₗ[R] C2
  square_zero : delta1.comp delta0 = 0

variable {R : Type u} {C0 : Type v} {C1 : Type w} {C2 : Type x}
variable [CommRing R]
variable [AddCommGroup C0] [Module R C0]
variable [AddCommGroup C1] [Module R C1]
variable [AddCommGroup C2] [Module R C2]

/-- Degree-one cocycle predicate. -/
def IsObserverCocycle
    (complex : ObserverCochainComplex R C0 C1 C2)
    (mismatch : C1) : Prop :=
  complex.delta1 mismatch = 0

/-- Degree-one coboundary predicate. -/
def IsObserverCoboundary
    (complex : ObserverCochainComplex R C0 C1 C2)
    (mismatch : C1) : Prop :=
  ∃ correction : C0, complex.delta0 correction = mismatch

/-- Module of degree-one observer cocycles. -/
def observerCocycles
    (complex : ObserverCochainComplex R C0 C1 C2) : Submodule R C1 :=
  LinearMap.ker complex.delta1

/-- The zero-to-one coboundary regarded as a map into the cocycle module. -/
def coboundaryToCocycles
    (complex : ObserverCochainComplex R C0 C1 C2) :
    C0 →ₗ[R] observerCocycles complex where
  toFun correction :=
    ⟨complex.delta0 correction, by
      change complex.delta1 (complex.delta0 correction) = 0
      have hSquare := LinearMap.congr_fun complex.square_zero correction
      simpa using hSquare⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar correction := by
    apply Subtype.ext
    simp

/-- Coboundaries as a submodule of cocycles. -/
def observerCoboundaries
    (complex : ObserverCochainComplex R C0 C1 C2) :
    Submodule R (observerCocycles complex) :=
  LinearMap.range (coboundaryToCocycles complex)

/-- First finite observer cohomology. -/
abbrev FirstObserverCohomology
    (complex : ObserverCochainComplex R C0 C1 C2) :=
  observerCocycles complex ⧸ observerCoboundaries complex

/-- Cohomology class of a closed observer mismatch. -/
def observerCocycleClass
    (complex : ObserverCochainComplex R C0 C1 C2)
    (mismatch : C1) (hCocycle : IsObserverCocycle complex mismatch) :
    FirstObserverCohomology complex :=
  (observerCoboundaries complex).mkQ ⟨mismatch, hCocycle⟩

/-- Every global coboundary correction produces a cocycle. -/
theorem observer_coboundary_is_cocycle
    (complex : ObserverCochainComplex R C0 C1 C2)
    {mismatch : C1} (hCoboundary : IsObserverCoboundary complex mismatch) :
    IsObserverCocycle complex mismatch := by
  rcases hCoboundary with ⟨correction, rfl⟩
  change complex.delta1 (complex.delta0 correction) = 0
  have hSquare := LinearMap.congr_fun complex.square_zero correction
  simpa using hSquare

/-- A closed mismatch has zero first cohomology class exactly when one global
zero-cochain corrects it. -/
theorem observerCocycleClass_eq_zero_iff
    (complex : ObserverCochainComplex R C0 C1 C2)
    (mismatch : C1) (hCocycle : IsObserverCocycle complex mismatch) :
    observerCocycleClass complex mismatch hCocycle = 0 ↔
      IsObserverCoboundary complex mismatch := by
  unfold observerCocycleClass
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨correction, hCorrection⟩
    refine ⟨correction, ?_⟩
    exact congrArg Subtype.val hCorrection
  · rintro ⟨correction, hCorrection⟩
    refine ⟨correction, ?_⟩
    apply Subtype.ext
    exact hCorrection

/-- A gluing obstruction is a closed mismatch with no global correction. -/
def HasObserverGluingObstruction
    (complex : ObserverCochainComplex R C0 C1 C2)
    (mismatch : C1) : Prop :=
  IsObserverCocycle complex mismatch ∧
    ¬ IsObserverCoboundary complex mismatch

/-- A closed mismatch is obstructed exactly when its first cohomology class is
nonzero. -/
theorem observer_gluing_obstruction_iff_class_ne_zero
    (complex : ObserverCochainComplex R C0 C1 C2)
    (mismatch : C1) (hCocycle : IsObserverCocycle complex mismatch) :
    HasObserverGluingObstruction complex mismatch ↔
      observerCocycleClass complex mismatch hCocycle ≠ 0 := by
  rw [HasObserverGluingObstruction, and_iff_right hCocycle,
    ne_eq, observerCocycleClass_eq_zero_iff]

/-- If every cocycle has a global correction, first observer cohomology has no
nonzero class. -/
theorem every_cocycle_correctable_implies_all_classes_zero
    (complex : ObserverCochainComplex R C0 C1 C2)
    (hCorrectable : ∀ mismatch,
      IsObserverCocycle complex mismatch →
        IsObserverCoboundary complex mismatch) :
    ∀ mismatch hCocycle,
      observerCocycleClass complex mismatch hCocycle = 0 := by
  intro mismatch hCocycle
  rw [observerCocycleClass_eq_zero_iff]
  exact hCorrectable mismatch hCocycle

/-- The trivial three-term complex has no gluing obstruction. -/
theorem zero_complex_no_obstruction
    (mismatch : C1) (hMismatch : mismatch = 0) :
    let complex : ObserverCochainComplex R C0 C1 C2 :=
      { delta0 := 0
        delta1 := 0
        square_zero := by simp }
    ¬ HasObserverGluingObstruction complex mismatch := by
  subst mismatch
  intro complex hObstruction
  exact hObstruction.2 ⟨0, by simp [complex]⟩

#print axioms observer_coboundary_is_cocycle
#print axioms observerCocycleClass_eq_zero_iff
#print axioms observer_gluing_obstruction_iff_class_ne_zero
#print axioms every_cocycle_correctable_implies_all_classes_zero
#print axioms zero_complex_no_obstruction

end D5.S3.Observer.Sheaf.ObserverGluingObstruction
