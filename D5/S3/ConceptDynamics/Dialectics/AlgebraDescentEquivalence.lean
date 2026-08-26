/- GID: D5/S3/ConceptDynamics/Dialectics/AlgebraDescentEquivalence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Dialectics/AlgebraDescentEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Descent is equivalent to pullback-algebra and effective-image observable closure. -/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
import D5.S3.ConceptDynamics.Factor.FactorInvariantObservables

/- Library-search audit trail (2026-08-26):
   * The exact source-shaped descent criterion was searched by theorem name and
     body shape in D5 and Golden/Frozen/accepted; no exact three-clause theorem
     was found.
   * `deterministic_interface_sixfold_equivalence` is the exact frozen source
     for effective descent versus proposition-valued pullback closure.
   * `factor_iff_observable_invariance` is the exact frozen factorization result
     for all effective-image observables; it is applied in both directions.
   * The canonical `realizedReadout` and `EffectiveDescent` primitives are
     imported rather than redeclared.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Dialectics.AlgebraDescentEquivalence

open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
open D5.S3.ConceptDynamics.Factor.FactorInvariantObservables

/-- Effective descent, pullback-algebra closure, and observable closure on the
    canonical effective interface are equivalent. -/
theorem descent_algebra_closure_tfae {X B : Type*}
    (q : X → B) (F : X → X) :
    List.TFAE [
      EffectiveDescent q F,
      PullbackInvariant q F,
      ObservableInvariant (realizedReadout q) F] := by
  tfae_have 1 ↔ 2 :=
    (deterministic_interface_sixfold_equivalence q F).out 0 4
  tfae_have 1 ↔ 3 := by
    constructor
    · rintro ⟨descended, hDescent, hUnique⟩
      apply (factor_iff_observable_invariance (realizedReadout q) F).mp
      refine ⟨descended, Function.semiconj_iff_comp_eq.mpr hDescent⟩
    · intro hObservable
      obtain ⟨descended, hFactor⟩ :=
        (factor_iff_observable_invariance (realizedReadout q) F).mpr hObservable
      have hDescent :
          realizedReadout q ∘ F = descended ∘ realizedReadout q :=
        Function.semiconj_iff_comp_eq.mp hFactor
      have hSurjective : Function.Surjective (realizedReadout q) := by
        intro value
        obtain ⟨x, hx⟩ := value.property
        exact ⟨x, Subtype.ext hx⟩
      refine ⟨descended, hDescent, ?_⟩
      intro other hOther
      funext value
      obtain ⟨x, rfl⟩ := hSurjective value
      exact (congrFun hOther x).symm.trans (congrFun hDescent x)
  tfae_finish

#print axioms descent_algebra_closure_tfae

end D5.S3.ConceptDynamics.Dialectics.AlgebraDescentEquivalence
