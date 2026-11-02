# Presented quandles with action and inverse action

## Abstract

A full term presentation of quandles with universal evaluation.

**Definition 1.1 (Unrestricted quandle terms).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedQuandle.Term`

*Formalization.* `D5/S0/Certificates/Quandles/PresentedQuandle.Term` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

Terms contain generators, action and inverse action. Mathlib's action is actor first. The inverse operation prevents the positive-term shelf from being substituted for a quandle.

**Definition 1.2 (Evaluation in any quandle).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedQuandle.eval`

*Formalization.* `D5/S0/Certificates/Quandles/PresentedQuandle.eval` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

An arbitrary generator assignment evaluates every expression in a target quandle using its action and inverse action. The generator type and target can be empty; there is no distinctness assumption.

**Definition 1.3 (The least generated congruence).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedQuandle.Rel`

*Formalization.* `D5/S0/Certificates/Quandles/PresentedQuandle.Rel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

The only constructors are equivalence, congruence for both operations, idempotence, left self-distributivity, the two inverse-action laws and the supplied equations. Every such derivation is respected by evaluation into any model of the equations.

**Definition 1.4 (The full quotient carrier).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedQuandle.Carrier`

*Formalization.* `D5/S0/Certificates/Quandles/PresentedQuandle.Carrier` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

Quotient the term type by this congruence. The actual Quandle instance is built on the quotient: both operations descend, and the quandle laws follow from the corresponding constructors. This is a standard universal-algebra construction; its new implementation is consumed by the eight-crossing specialization, with no claim of mathematical novelty.

**Definition 1.5 (Generators in the quotient).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedQuandle.of`

*Formalization.* `D5/S0/Certificates/Quandles/PresentedQuandle.of` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

Each generator denotes its term class. No injectivity is assumed or generally true.

**Theorem 1.6 (All supplied equations hold).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedQuandle.relation_eq`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/PresentedQuandle.relation_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

Every presentation equation gives an equality of the actual quotient classes. The 8_20 specialization consumes this theorem for the six relations used by its order obstruction.

**Definition 1.7 (Universal evaluation homomorphism).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedQuandle.lift`

*Formalization.* `D5/S0/Certificates/Quandles/PresentedQuandle.lift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

Every assignment satisfying all supplied relations extends by quotient lift to a ShelfHom, the existing Mathlib notion of quandle homomorphism. The homomorphism is defined on every quotient element, not merely the named generators.

**Theorem 1.8 (The extension's generator values).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedQuandle.lift_of`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/PresentedQuandle.lift_of` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

The extension agrees with the assignment on all generators. This reduction is used by the coloring separation.

**Theorem 1.9 (Uniqueness on the full presented quandle).**

Lean statement: `D5/S0/Certificates/Quandles/PresentedQuandle.lift_unique`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/PresentedQuandle.lift_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

Any homomorphism with the specified generator values equals the extension. The proof inducts on expressions and derives inverse-action preservation from rack cancellation. Combined with lift and lift_of, this proves the presentation universal property for arbitrary target quandles. The least-congruence construction imposes no additional relations.

## References

- Truth anchor: `D5/S0/Certificates/Quandles/PresentedQuandle.Carrier`
- Truth anchor: `D5/S0/Certificates/Quandles/PresentedQuandle.Rel`
- Truth anchor: `D5/S0/Certificates/Quandles/PresentedQuandle.Term`
- Truth anchor: `D5/S0/Certificates/Quandles/PresentedQuandle.eval`
- Truth anchor: `D5/S0/Certificates/Quandles/PresentedQuandle.lift`
- Truth anchor: `D5/S0/Certificates/Quandles/PresentedQuandle.lift_of`
- Truth anchor: `D5/S0/Certificates/Quandles/PresentedQuandle.lift_unique`
- Truth anchor: `D5/S0/Certificates/Quandles/PresentedQuandle.of`
- Truth anchor: `D5/S0/Certificates/Quandles/PresentedQuandle.relation_eq`
