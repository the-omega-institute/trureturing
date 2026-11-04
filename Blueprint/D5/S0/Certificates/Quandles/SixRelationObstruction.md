# A six-relation obstruction in ordered idempotent magmas

## Abstract

Six relations force two elements to coincide under both strict monotonicity laws.

**Theorem 1.1 (The strict-order cycle forces equality).**

Lean statement: `D5/S0/Certificates/Quandles/SixRelationObstruction.sixRelation_forces_eq`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/SixRelationObstruction.sixRelation_forces_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

For an arbitrary LinearOrder and arbitrary idempotent binary operation strictly increasing in both arguments, d*g=e, g*e=h, f*d=g, d*a=c, a*c=h and f*c=e imply d=g. Under d<g the live proof derives d<e<g, c<d, a<d, a<c, h<c and e<h, yielding h<c<d<e<h. Applying that argument in the dual order rules out g<d. No rack, self-distributivity, inverse action, finiteness or nondegeneracy is assumed. The full presented-quandle refutation consumes this conclusion. This is an attributed implementation of the predecessor ordinary proof; no independent priority or novelty is asserted.

## References

- Truth anchor: `D5/S0/Certificates/Quandles/SixRelationObstruction.sixRelation_forces_eq`
