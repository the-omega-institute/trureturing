# Conjugate Unbounded

## Abstract

The conjugate reading of the greedy expansion of one passes every bound.

Every ingredient was already proved and none is restated here. The fourth remainder is past the escape threshold; the greedy digits lie in the range the escape estimate assumes; past the threshold one step cannot return; and the excess above the threshold is multiplied by the conjugate modulus at every step. This module is the composition.

That it needed writing at all is the point. Each of those facts had been landed separately and each was green on its own, but the statement they combine to make existed only in prose. A conjunction of proved things is not proved until someone writes the conjunction down.

**Theorem 1.1 (The conjugate orbit is unbounded).**

$$\forall M \in R,\; \exists n \in N,\; M < \left|\operatorname{conjugateRemainder}\left(n\right)\right|$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisotVerdict/ConjugateUnbounded.the_conjugate_orbit_is_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The other half of the statement is that the orbit never returns below the threshold after the fourth step. Neither half says anything about whether the digits repeat; what they give is the side of the contradiction that any eventual period would have to meet.

## References

- Truth anchor: `D5/S0/Tower/NonPisotVerdict/ConjugateUnbounded.the_conjugate_orbit_is_unbounded`
- Dependency: [D5/S0/Tower/NonPisotFrontier/ConjugateValuation](../NonPisotFrontier/ConjugateValuation.md)
- Dependency: [D5/S0/Tower/NonPisotFrontier/EscapeIteration](../NonPisotFrontier/EscapeIteration.md)
- Dependency: [D5/S0/Tower/NonPisotFrontier/OrbitWitness](../NonPisotFrontier/OrbitWitness.md)
