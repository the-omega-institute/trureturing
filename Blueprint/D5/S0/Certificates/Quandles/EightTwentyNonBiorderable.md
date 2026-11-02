# The 8_20 presentation: candidate full-domain non-biorderability

## Abstract

The exact eight-relation presented quandle admits no full-domain biorder.

**Definition 1.1 (Eight original arcs).**

Lean statement: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.Arc`

*Formalization.* `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.Arc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

The labels a,b,c,d,e,f,g,h are exactly those of the primary source's oriented Figure fig8_20.

**Definition 1.2 (All eight crossings).**

Lean statement: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.Crossing`

*Formalization.* `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.Crossing` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

The relations are b*e=a, c*g=b, d*g=e, g*e=h, f*d=g, d*a=c, a*c=h, f*c=e. Every paper product x*y is represented as Mathlib Shelf.act y x. Relations 1 and 2 remain in the presentation and are checked by the coloring, though the strict-order obstruction uses only 3 through 8.

**Definition 1.3 (The full presented carrier).**

Lean statement: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.KnotQuandle`

*Formalization.* `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.KnotQuandle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

This is PresentedQuandle.Carrier Crossing, the quotient of unrestricted action and inverse-action terms by exactly the quandle axioms and all crossings. Its universal property is proved in the dependency module. Identifying this algebraic presentation with the fundamental quandle of the oriented knot is an EXTERNAL SOURCE MAP from the original diagram and presentation, not a formal theorem of ambient isotopy or knot recognition. The independent fidelity review remains decisive for that boundary.

**Definition 1.4 (Actual generator classes).**

Lean statement: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.arc`

*Formalization.* `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.arc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

Each arc is its class in the entire quotient. Separation is proved by evaluation rather than imposed as an axiom.

**Definition 1.5 (The paper operation).**

Lean statement: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.op`

*Formalization.* `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.op` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

op x y is Shelf.act y x. The dihedral instance matches 2*y-x directly. Mathlib's group conjugation convention would need inverse action for the paper's group example; no conjugation-group replacement is used.

**Definition 1.6 (The exact mod-nine coloring).**

Lean statement: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.color`

*Formalization.* `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.color` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

The primary paper's tuple is (7,6,5,0,2,8,1,3). Kernel-safe finite reduction checks every original equation. The target is the existing Mathlib dihedral quandle, used only for separation.

**Definition 1.7 (Coloring of the entire presented quandle).**

Lean statement: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.colorHom`

*Formalization.* `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.colorHom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

The universal evaluation property supplies a genuine ShelfHom on every quotient class. Evaluating d and g gives 0 and 1, so their actual classes differ. This assumes neither that the coloring is injective nor that its finite target is ordered.

**Definition 1.8 (One order on the whole carrier).**

Lean statement: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.claim`

*Formalization.* `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

The closed proposition asserts existence of one LinearOrder on the complete presented quandle with both strict translation laws. It does not restrict the quantifiers to generators or terms of bounded length. Every D2 extension would satisfy this order-existence claim, so its negation excludes that author possibility without trusting table exhaustiveness.

**Theorem 1.9 (Closed negation of full-domain biorderability).**

Lean statement: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vaishnavi Gupta; Hitesh Raundal (2025). *Biorderability of knot quandles of knots up to eight crossings*. DOI: [10.48550/arXiv.2505.19573](https://doi.org/10.48550/arXiv.2505.19573). URL: <https://arxiv.org/abs/2505.19573v1>.

*Commentary.*

A hypothetical whole-domain biorder makes the generic six-relation obstruction force d=g. The constructed coloring separates them, giving a contradiction. The result is literally Not claim, with no homomorphism, generator-distinctness or desired conclusion hidden in its hypotheses. This implementation is repo-prior-exposed and a candidate only. Independent source fidelity, current literature status and final review are pending; no solved-original, priority, unique, official-acceptance or KPI claim is made.

## References

- Truth anchor: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.Arc`
- Truth anchor: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.Crossing`
- Truth anchor: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.KnotQuandle`
- Truth anchor: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.arc`
- Truth anchor: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.claim`
- Truth anchor: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.color`
- Truth anchor: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.colorHom`
- Truth anchor: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.op`
- Truth anchor: `D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.result`
- Dependency: [D5/S0/Certificates/Quandles/PresentedQuandle](PresentedQuandle.md)
- Dependency: [D5/S0/Certificates/Quandles/SixRelationObstruction](SixRelationObstruction.md)
