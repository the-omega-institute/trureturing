/- GID: D5/S3/Observer/ProbabilisticClosure/StrongLumpabilityDescent
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/StrongLumpabilityDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pushed-forward stochastic laws descend exactly when constant on interface fibers. -/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.StrongLumpabilityDescent

open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence

/- Library-search audit trail (2026-08-26):
   * Current-tree searches for strong lumpability, pushed-forward PMF laws, and a
     kernel on the realized image found no exact theorem.
   * `DistributionIndependentClosure` is deterministic: it characterizes point-mass
     kernels and cannot cover arbitrary stochastic rows.
   * Pinned Mathlib supplies `PMF.map` and `Function.surjInv`; no packaged
     fiber-constant descent criterion was found.
   * The body-shape search for an image readout found the canonical
     `DeterministicInterfaceEquivalence.realizedReadout`, which is imported rather
     than redeclared.
-/

set_option autoImplicit false

/-- A Markov row descends to the effective observation image exactly when its
    pushed-forward law is constant on every interface fiber. -/
theorem strong_lumpability_descent_tfae {X B : Type*}
    (q : X → B) (K : X → PMF X) :
    List.TFAE [
      ∃ kernel : Set.range q → PMF (Set.range q),
        ∀ x, PMF.map (realizedReadout q) (K x) = kernel (realizedReadout q x),
      ∀ x y, q x = q y →
        PMF.map (realizedReadout q) (K x) = PMF.map (realizedReadout q) (K y),
      ∀ x y, realizedReadout q x = realizedReadout q y →
        PMF.map (realizedReadout q) (K x) = PMF.map (realizedReadout q) (K y)] := by
  classical
  have hSurjective : Function.Surjective (realizedReadout q) := by
    intro value
    obtain ⟨x, hx⟩ := value.property
    exact ⟨x, Subtype.ext hx⟩
  tfae_have 1 ↔ 2 := by
    constructor
    · rintro ⟨kernel, hkernel⟩ x y hxy
      rw [hkernel x, hkernel y]
      exact congrArg kernel (Subtype.ext hxy)
    · intro hfiber
      let kernel : Set.range q → PMF (Set.range q) := fun value =>
        PMF.map (realizedReadout q) (K (Function.surjInv hSurjective value))
      refine ⟨kernel, ?_⟩
      intro x
      dsimp [kernel]
      apply hfiber x (Function.surjInv hSurjective (realizedReadout q x))
      exact congrArg Subtype.val
        (Function.surjInv_eq hSurjective (realizedReadout q x)).symm
  tfae_have 2 ↔ 3 := by
    constructor
    · intro hfiber x y hxy
      exact hfiber x y (congrArg Subtype.val hxy)
    · intro hfiber x y hxy
      exact hfiber x y (Subtype.ext hxy)
  tfae_finish

#print axioms strong_lumpability_descent_tfae

end D5.S3.Observer.ProbabilisticClosure.StrongLumpabilityDescent
