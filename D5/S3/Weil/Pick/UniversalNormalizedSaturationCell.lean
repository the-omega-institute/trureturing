/- GID: D5/S3/Weil/Pick/UniversalNormalizedSaturationCell
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/UniversalNormalizedSaturationCell
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every normalized unit-phase Pick contact has the same indefinite two-point cell. -/

import D5.S3.Weil.Pick.MinimalRelationalVisibility

/-!
# Universal normalized saturation cell

A family of candidate functions may vary with zero height, offline distance,
multiplicity, completed function, contact phase, and contact point. If every
member is zero at the origin and takes its selected unit phase at its selected
interior point, its standard two-point Pick relation is always the matrix with
rows `(1, 1)` and `(1, 0)`. The phase-one frozen owner supplies the common
non-positivity certificate after unit-phase normalization.
-/

/- Library-search and duplication audit trail (2026-09-03):
   * D5 searches `Pick kernel|pickKernel|normalized saturation|unit modulus|
     relation = !![1,1;1,0]` found the phase-one frozen owner
     `MinimalRelationalVisibility.minimal_relational_visibility`, imported and
     applied below, but no theorem for an arbitrary contact phase or for the
     source-indexed independence family.
   * The body-shape search `(1 - schur z * conj (schur w)) /
     (1 - z * conj w)` found that same frozen owner. Therefore this module
     introduces no global kernel definition; the source kernel remains a
     public local construction in the theorem statement.
   * Pinned Mathlib searches `Pick kernel|unit modulus Pick|phase normalize`
     found complex unit-circle identities and matrix positivity primitives,
     but no exact normalized saturation-cell theorem.
   * GitHub Lean-code searches for `Pick kernel` with `unit modulus` or
     `PosSemidef` returned no exact theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Matrix
open scoped ComplexConjugate ComplexOrder

namespace D5.S3.Weil.Pick.UniversalNormalizedSaturationCell

open D5.S3.Weil.Pick.MinimalRelationalVisibility

/-- Independently of zero height, offline distance, multiplicity, completed
function, contact phase, and interior contact location, normalized unit-phase
contact has the universal indefinite two-point Pick relation. -/
theorem universal_normalized_saturation_cell
    (schurCandidate : Real -> Real -> Nat ->
      (Complex -> Complex) -> Circle -> Complex.UnitDisc -> Complex)
    (contactPoint : Real -> Real -> Nat ->
      (Complex -> Complex) -> Circle -> Complex.UnitDisc)
    (hzero : forall zeroHeight offlineDistance zeroMultiplicity
      completedFunction contactPhase,
      schurCandidate zeroHeight offlineDistance zeroMultiplicity
        completedFunction contactPhase 0 = 0)
    (hcontact : forall zeroHeight offlineDistance zeroMultiplicity
      completedFunction contactPhase,
      schurCandidate zeroHeight offlineDistance zeroMultiplicity
        completedFunction contactPhase
          (contactPoint zeroHeight offlineDistance zeroMultiplicity
            completedFunction contactPhase) = contactPhase) :
    forall zeroHeight offlineDistance zeroMultiplicity completedFunction contactPhase,
      let schur := schurCandidate zeroHeight offlineDistance zeroMultiplicity
        completedFunction contactPhase
      let a := contactPoint zeroHeight offlineDistance zeroMultiplicity
        completedFunction contactPhase
      let pickKernel : Complex.UnitDisc -> Complex.UnitDisc -> Complex := fun z w =>
        (1 - schur z * conj (schur w)) /
          (1 - (z : Complex) * conj (w : Complex))
      let points : Fin 2 -> Complex.UnitDisc := ![(0 : Complex.UnitDisc), a]
      let relation : Matrix (Fin 2) (Fin 2) Complex := fun i j =>
        pickKernel (points i) (points j)
      relation = !![(1 : Complex), 1; 1, 0] /\
        Not relation.PosSemidef := by
  intro zeroHeight offlineDistance zeroMultiplicity completedFunction contactPhase
  dsimp only
  let schur := schurCandidate zeroHeight offlineDistance zeroMultiplicity
    completedFunction contactPhase
  let a := contactPoint zeroHeight offlineDistance zeroMultiplicity
    completedFunction contactPhase
  have hschurZero : schur 0 = 0 := by
    exact hzero zeroHeight offlineDistance zeroMultiplicity completedFunction contactPhase
  have hschurContact : schur a = contactPhase := by
    exact hcontact zeroHeight offlineDistance zeroMultiplicity completedFunction contactPhase
  have hrelation :
      (fun i j : Fin 2 =>
        (1 - schur (![(0 : Complex.UnitDisc), a] i) *
          conj (schur (![(0 : Complex.UnitDisc), a] j))) /
          (1 - ((![(0 : Complex.UnitDisc), a] i : Complex.UnitDisc) : Complex) *
            conj ((![(0 : Complex.UnitDisc), a] j : Complex.UnitDisc) : Complex))) =
        !![(1 : Complex), 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hschurZero, hschurContact, Complex.mul_conj, Circle.normSq_coe]
  let normalized : Complex.UnitDisc -> Complex := fun z =>
    conj (contactPhase : Complex) * schur z
  have hnormalizedZero : normalized 0 = 0 := by
    simp [normalized, hschurZero]
  have hnormalizedContact : normalized a = 1 := by
    simp [normalized, hschurContact, <- Complex.normSq_eq_conj_mul_self]
  let extended : Complex -> Complex :=
    Function.extend ((↑) : Complex.UnitDisc -> Complex) normalized 0
  have hextendedAt (z : Complex.UnitDisc) :
      extended (z : Complex) = normalized z := by
    simpa [extended] using
      Complex.UnitDisc.coe_injective.extend_apply normalized 0 z
  have hextendedZero : extended 0 = 0 := by
    change extended ((0 : Complex.UnitDisc) : Complex) = 0
    rw [hextendedAt, hnormalizedZero]
  have hextendedContact : extended a = 1 := by
    rw [hextendedAt, hnormalizedContact]
  have hvisible := minimal_relational_visibility extended a
    hextendedZero hextendedContact
  have hfibonacciNot :
      Not (Matrix.PosSemidef !![(1 : Complex), 1; 1, 0]) := by
    intro hpositive
    apply hvisible.2.2.2.1
    rw [hvisible.1]
    exact hpositive
  refine And.intro hrelation ?_
  intro hpositive
  apply hfibonacciNot
  rw [<- hrelation]
  exact hpositive

#print axioms universal_normalized_saturation_cell

end D5.S3.Weil.Pick.UniversalNormalizedSaturationCell
