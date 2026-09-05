/- GID: D5/S3/Midline/Cayley/PositiveExactRealizationFiber
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/PositiveExactRealizationFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive exact Cayley realization fibers characterize RH under exhaustive zero data. -/

import D5.S3.Midline.Cayley.ZeroHilbertCayleyUnitarity

/- Library-search and duplication audit (2026-09-05):
   * Searches for positive exact realization fibers, zero-mode defects, Cayley
     eigenmodes, Gram identities, and RH implications found no existing
     realization-fiber declaration in D5 or the active in-flight branches.
   * `ZeroHilbertCayleyUnitarity` is the more general spectral result needed
     here: it identifies RH with the Cayley Gram identity on an exhaustive
     multiplicity-expanded zero space. This module imports and wraps that
     equivalence instead of reproving the critical-line calculation.
   * Pinned Mathlib's `ContinuousLinearMap.isometry_iff_adjoint_comp_self`,
     `Isometry.norm_map_of_map_zero`, and `norm_smul` turn the positive Gram
     identity and a nonzero zero mode into coefficient norm one.
   * The source silently assumes that its zero modes are nonzero and cover all
     nontrivial zeros. Both requirements are explicit below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Midline.Cayley.PositiveExactRealizationFiber

open D5.S3.Midline.Cayley.CayleyUnitarityDefect
open D5.S3.Midline.Cayley.ZeroHilbertCayleyUnitarity
open D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization
open D5.S3.Weil.ZeroSum
open scoped ComplexConjugate ENNReal InnerProduct lp

noncomputable section

/-- A positive exact realization supplies a nonzero mode for every zero
coordinate, realizes the Cayley coefficient on that mode, and has zero
positive metric defect. -/
structure PositiveExactRealization (Z : ZeroData) where
  operator :
    ObserverHilbertSpace (ZeroCoordinate Z) →L[Complex]
      ObserverHilbertSpace (ZeroCoordinate Z)
  psi : ZeroCoordinate Z → ObserverHilbertSpace (ZeroCoordinate Z)
  psi_ne_zero : ∀ v, psi v ≠ 0
  zero_mode : ∀ v,
    operator (psi v) = cayleyCoefficient (Z.zero v.1) • psi v
  gram_identity : star operator * operator = 1

private theorem realization_isometry {Z : ZeroData}
    (realization : PositiveExactRealization Z) :
    Isometry realization.operator := by
  apply realization.operator.isometry_iff_adjoint_comp_self.mpr
  apply ContinuousLinearMap.ext
  intro vector
  have happly := congrArg (fun operator => operator vector)
    realization.gram_identity
  simpa [ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp] using happly

private theorem realization_coefficient_norm {Z : ZeroData}
    (realization : PositiveExactRealization Z)
    (v : ZeroCoordinate Z) :
    ‖cayleyCoefficient (Z.zero v.1)‖ = 1 := by
  have hnorm := (realization_isometry realization).norm_map_of_map_zero
    realization.operator.map_zero (realization.psi v)
  rw [realization.zero_mode, norm_smul] at hnorm
  have hpsi : 0 < ‖realization.psi v‖ :=
    norm_pos_iff.mpr (realization.psi_ne_zero v)
  nlinarith [norm_nonneg (cayleyCoefficient (Z.zero v.1))]

/-- Nonemptiness of the positive exact realization fiber forces RH, provided
the supplied zero data exhausts every nontrivial zeta zero. -/
theorem positive_exact_realization_fiber_nonempty_implies_rh
    (Z : ZeroData)
    (hExhaustive : ∀ rho : Complex,
      riemannZeta rho = 0 →
      (¬ ∃ n : Nat, rho = -2 * (n + 1)) →
      rho ≠ 1 →
      ∃ n, Z.zero n = rho) :
    Nonempty (PositiveExactRealization Z) → RiemannHypothesis := by
  rintro ⟨realization⟩
  have hBridge :=
    cayley_unitarity_defect_formula_on_zero_hilbert_space Z hExhaustive
  exact hBridge.2.1.mpr (realization_coefficient_norm realization)

/-- Under RH, the repository's diagonal zero-space Cayley operator and its
canonical coordinate vectors construct a positive exact realization. -/
def canonicalPositiveExactRealization
    (Z : ZeroData)
    (hExhaustive : ∀ rho : Complex,
      riemannZeta rho = 0 →
      (¬ ∃ n : Nat, rho = -2 * (n + 1)) →
      rho ≠ 1 →
      ∃ n, Z.zero n = rho)
    (hRH : RiemannHypothesis) : PositiveExactRealization Z where
  operator := zeroCayleyOperator Z
  psi := fun v => lp.single 2 v 1
  psi_ne_zero := by
    intro v
    intro hzero
    have happly := congrArg (fun vector => vector v) hzero
    simpa using happly
  zero_mode := by
    intro v
    have hBridge :=
      cayley_unitarity_defect_formula_on_zero_hilbert_space Z hExhaustive
    simpa using (hBridge.1 v).1
  gram_identity := by
    have hBridge :=
      cayley_unitarity_defect_formula_on_zero_hilbert_space Z hExhaustive
    exact hBridge.2.2.1.mp hRH

/-- The positive exact realization fiber is nonempty exactly under RH. This
records both the obstruction and the canonical existence witness. -/
theorem positive_exact_realization_fiber_nonempty_iff_rh
    (Z : ZeroData)
    (hExhaustive : ∀ rho : Complex,
      riemannZeta rho = 0 →
      (¬ ∃ n : Nat, rho = -2 * (n + 1)) →
      rho ≠ 1 →
      ∃ n, Z.zero n = rho) :
    Nonempty (PositiveExactRealization Z) ↔ RiemannHypothesis := by
  constructor
  · exact positive_exact_realization_fiber_nonempty_implies_rh Z hExhaustive
  · intro hRH
    exact ⟨canonicalPositiveExactRealization Z hExhaustive hRH⟩

#print axioms positive_exact_realization_fiber_nonempty_implies_rh
#print axioms positive_exact_realization_fiber_nonempty_iff_rh

end

end D5.S3.Midline.Cayley.PositiveExactRealizationFiber
