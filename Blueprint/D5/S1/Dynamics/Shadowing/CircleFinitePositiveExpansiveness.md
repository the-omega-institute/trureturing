# CircleFinitePositiveExpansiveness

## Abstract

Uniform finite positive expansivity implies positive expansivity for every continuous circle selfmap.

Gangloff, Guillon and Oprocha, Various questions around finitely positively expansive dynamical systems, arXiv:2310.17241v1, Question 3.1, page 7, ask for a positively (n+1)-expansive circle map that is not positively n-expansive, for every n>=1. The full-circle theorem below answers negatively: every finite positive-expansivity bound collapses to ordinary positive expansivity, possibly at a new uniform scale. Conversely, positive expansivity supplies the finite bound N=1, so all strict finite levels above one are absent. The known interval obstruction, their Theorem 3.8, is consumed by the proof. The circle argument is repository-derived; this source connection asserts no worldwide novelty, map classification, arbitrary-graph or higher-dimensional extension, or settlement of their other-space questions. The paper's other results remain unaffected.

**Theorem 1.1 (Local injectivity is derived).**

Lean statement: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.isLocallyInjective_of_finitelyPositiveExpansive`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.isLocallyInjective_of_finitelyPositiveExpansive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a continuous selfmap of the entire AddCircle (1 : Real), FinitelyPositiveExpansive implies local injectivity. If local injectivity failed, two distinct lifted turns and the proved two-target crossing would extend every actual coalescing history family. Exact transit and fold pullbacks control every time through T+q+1, including the final application of f, and double the family. The resulting 2^N distinct common-terminal histories contradict the original strict infinite-time Bowen bound. Local injectivity is a conclusion of this argument.

**Theorem 1.2 (The exact circle theorem).**

Lean statement: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.positivelyExpansive_of_finitelyPositiveExpansive`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.positivelyExpansive_of_finitelyPositiveExpansive` (`✓ std3`). ∎

*Resolves.* `Problems/gangloff-guillon-oprocha-circle-finite-positive-expansivity` (refuted) by `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.positivelyExpansive_of_finitelyPositiveExpansive`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gangloff-guillon-oprocha-circle-finite-positive-expansivity","declaration_gid":"D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.positivelyExpansive_of_finitelyPositiveExpansive","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Silvère Gangloff; Pierre Guillon; Piotr Oprocha (2023). *Various questions around finitely positively expansive dynamical systems*. URL: <https://arxiv.org/abs/2310.17241v1>.

*Commentary.*

For every f : AddCircle (1 : Real) -> AddCircle (1 : Real), continuity and FinitelyPositiveExpansive f imply PositivelyExpansive f. The finite hypothesis chooses one epsilon > 0 and one natural N >= 1 uniformly over all centers, bounding the strict forward Bowen set at every natural time including zero. The conclusion supplies its own uniform positive scale c: if dist(f^t(x), f^t(y)) < c for every natural t then x=y. No invertibility, surjectivity, covering, local injectivity, orientation, mixing or expansion hypothesis is imposed. After deriving local injectivity, compactness supplies a uniform injectivity radius. Uniform continuity and the exact short-arc image lemma propagate an endpoint-close short arc at every iterate. If the endpoints differed the entire infinite arc would lie in one original Bowen set, contradicting its finite cardinal bound.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.isLocallyInjective_of_finitelyPositiveExpansive`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.positivelyExpansive_of_finitelyPositiveExpansive`
- Dependency: [D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/CircleOrder](CircleFinitePositiveExpansiveness/CircleOrder.md)
