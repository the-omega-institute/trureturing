/- GID: D5/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/LosslessReadoutReflexiveGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A lossless readout captures all predicates but no same-state catalog captures them all. -/

import D5.S3.ConceptDynamics.Dialectics.RealizedReadoutCompatibility

/-!
# Lossless Readout Reflexive Gap

This module connects empirical completeness and reflexive incompleteness through
one readout map. An injective readout induces a bijection between Boolean
predicates on its realized empirical image and Boolean predicates on states,
yet every catalogue indexed by those same states misses an explicit predicate
on that image. The diagonal argument itself is classical; the new paper-facing
claim is its transport onto the verified empirical image.
-/

/- Library-search audit trail (2026-09-06):
   * Exact repository hit `realizedReadout_eq_rangeFactorization` identifies the
     existing realized readout with Mathlib's canonical range factorization and
     is used directly; `realizedReadout` is not redeclared.
   * Exact pinned-Mathlib hits `Set.rangeFactorization_bijective` and
     `Function.Bijective.comp_right` respectively characterize losslessness and
     transport bijectivity to Boolean predicate spaces; both are used directly.
   * Repository searches for observable predicate pullbacks and diagonal escape
     on `Set.range` found related generic escape theorems but no theorem joining
     an injective readout, predicate-space bijectivity, and a same-carrier
     catalogue. `Function.cantor_surjective` is a generic prior-art comparator,
     not an exact readout-image transport theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.LosslessReadoutReflexiveGap

open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
open D5.S3.ConceptDynamics.Dialectics.RealizedReadoutCompatibility

/-- Pull an observable Boolean predicate on the realized empirical image back
to a Boolean predicate on states. -/
def observablePullback {A O : Type*} (R : A → O) :
    (Set.range R → Bool) → (A → Bool) :=
  fun q => q ∘ realizedReadout R

/-- An injective readout makes pullback from predicates on its realized image a
bijection onto all Boolean predicates on states. -/
theorem lossless_readout_predicate_equiv
    {A O : Type*} {R : A → O}
    (hR : Function.Injective R) :
    Function.Bijective (observablePullback R) := by
  have hrange : Function.Bijective (realizedReadout R) := by
    rw [realizedReadout_eq_rangeFactorization]
    exact Set.rangeFactorization_bijective.mpr hR
  change Function.Bijective (fun q => q ∘ realizedReadout R)
  exact hrange.comp_right

/-- Every state-indexed catalogue of observable Boolean predicates misses the
predicate obtained by negating its transported diagonal. -/
theorem observable_diagonal_escape
    {A O : Type*} {R : A → O}
    (hR : Function.Injective R)
    (catalog : A → Set.range R → Bool) :
    ∃ q : Set.range R → Bool,
      ∀ a : A, q (realizedReadout R a) ≠
        catalog a (realizedReadout R a) := by
  have hrange : Function.Bijective (realizedReadout R) := by
    rw [realizedReadout_eq_rangeFactorization]
    exact Set.rangeFactorization_bijective.mpr hR
  let e : A ≃ Set.range R := Equiv.ofBijective (realizedReadout R) hrange
  refine ⟨fun o => !(catalog (e.symm o) o), ?_⟩
  intro a
  have hinverse : e.symm (realizedReadout R a) = a := by
    change e.symm (e a) = a
    exact e.symm_apply_apply a
  change Bool.not (catalog (e.symm (realizedReadout R a)) (realizedReadout R a)) ≠
    catalog a (realizedReadout R a)
  rw [hinverse]
  cases catalog a (realizedReadout R a) <;> decide

/-- A lossless readout simultaneously realizes every Boolean state predicate
from its empirical image and rules out surjectivity of every catalogue indexed
by those same states. -/
theorem lossless_observation_strict_reflexive_gap
    {A O : Type*} {R : A → O}
    (hR : Function.Injective R) :
    Function.Bijective (observablePullback R) ∧
      ∀ catalog : A → (Set.range R → Bool),
        ¬ Function.Surjective catalog := by
  refine ⟨lossless_readout_predicate_equiv hR, ?_⟩
  intro catalog hsurjective
  obtain ⟨q, hq⟩ := observable_diagonal_escape hR catalog
  obtain ⟨a, ha⟩ := hsurjective q
  exact hq a (Eq.symm (congrFun ha (realizedReadout R a)))

#print axioms observablePullback
#print axioms lossless_readout_predicate_equiv
#print axioms observable_diagonal_escape
#print axioms lossless_observation_strict_reflexive_gap

end D5.S3.ConceptDynamics.ObservationTopology.LosslessReadoutReflexiveGap
