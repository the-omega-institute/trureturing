/- GID: D5/S3/Observer/RiemannNamingStabilityReduction
   generality: G
   mirror-B: D5/B/S3/Observer/RiemannNamingStabilityReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: RH naming stability reduces to the missing shifted-response congruence bridge. -/

import D5.S3.Observer.Separation.CongruenceClosureDuality
import Mathlib.NumberTheory.LSeries.RiemannZeta

/- Library-search audit trail (2026-09-02):
   * Exact and symbol-variant searches found the general interior/closure fixed-point
     theorem `dual_congruence_repair_laws`; it is imported and applied directly.
   * Receipt and digest searches found no formalization receipt for the source atom.
     Generalized searches found shifted-xi observation layers, but no complete
     shifted-response state space or reflection-name `Setoid` connecting them to RH.
   * The source theory itself records those analytic bridge obligations as open.
     Accordingly, the theorem below exposes precisely that missing bridge as a
     hypothesis instead of claiming an unconditional shifted-xi instantiation.
   * Pinned Mathlib supplies `RiemannHypothesis`; no Mathlib theorem supplies the
     project-specific shifted-response congruence bridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.RiemannNamingStabilityReduction

open D5.S3.Observer.Separation.CongruenceClosureDuality

universe u

/-- Once the analytic shifted-response model identifies RH with preservation of
the reflection-name relation, the already-proved dual repair theorem gives all
three naming-stability formulations. The bridge hypothesis is exactly the
project-specific obligation not supplied by the abstract repair theory. -/
theorem riemann_naming_stability_reduction
    {State : Type u} (shiftedResponse : State -> State)
    (reflectionName : Setoid State)
    (shiftedXiBridge :
      RiemannHypothesis <->
        IsForwardCongruence shiftedResponse reflectionName) :
    (RiemannHypothesis <->
      congruenceInterior shiftedResponse reflectionName = reflectionName) /\
    (RiemannHypothesis <->
      IsForwardCongruence shiftedResponse reflectionName) /\
    (RiemannHypothesis <->
      congruenceClosure shiftedResponse reflectionName = reflectionName) /\
    (RiemannHypothesis <->
      congruenceInterior shiftedResponse reflectionName = reflectionName /\
        reflectionName = congruenceClosure shiftedResponse reflectionName) := by
  have laws := dual_congruence_repair_laws shiftedResponse
  have interiorFixed :
      congruenceInterior shiftedResponse reflectionName = reflectionName <->
        IsForwardCongruence shiftedResponse reflectionName :=
    laws.2.2.2.2.2.2.1 reflectionName
  have closureFixed :
      IsForwardCongruence shiftedResponse reflectionName <->
        congruenceClosure shiftedResponse reflectionName = reflectionName :=
    laws.2.2.2.2.2.2.2.1 reflectionName
  refine ⟨shiftedXiBridge.trans interiorFixed.symm, shiftedXiBridge,
    shiftedXiBridge.trans closureFixed, ?_⟩
  constructor
  · intro hRH
    have hstable : IsForwardCongruence shiftedResponse reflectionName :=
      shiftedXiBridge.mp hRH
    exact ⟨interiorFixed.mpr hstable, (closureFixed.mp hstable).symm⟩
  · intro hfixed
    exact shiftedXiBridge.mpr (interiorFixed.mp hfixed.1)

#print axioms riemann_naming_stability_reduction

end D5.S3.Observer.RiemannNamingStabilityReduction
