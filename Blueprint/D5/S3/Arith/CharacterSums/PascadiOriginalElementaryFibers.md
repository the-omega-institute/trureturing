# Complete elementary endpoint fibers

## Abstract

The complete original endpoint fiber has at most twice the size of its literal lattice section, plus one. The hyperbola right side may be a nonunit, and repeated endpoints remain included.

Fix a prime p, original alternating units a1,a2, and unit middle letters t,w modulo p cubed. Let F be any finite set of integer points (a,d) in the congruence lattice w*d=t*a modulo p cubed and the physical rectangle |a|<=X, |d|<=Y. Assume 2X<p squared and 2Y<p cubed. Count every ordered pair ((a,d),(b,v)) in F times F for which the original six-letter return word is minus the identity.

**Theorem 1.1 (The full elementary fiber bound).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalElementaryFibers.actual_endpoint_pair_elementary_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalElementaryFibers.actual_endpoint_pair_elementary_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

The number of these actual ordered endpoint pairs is at most 2*|F|+1. No condition is imposed on 1+a1*a2*t*w.

Write k=a1*a2*t. The first original return equation gives (1-k*a)*(1-k*b)=1+k*w. If the first shifted factor is nonzero modulo p squared, cancellation in modulus p cubed determines b modulo p squared; the short first-coordinate interval fixes b as an integer. The unit w and the short second-coordinate interval then recover v. These pairs cost at most |F|. Applying the same argument to the other factor costs at most another |F|.

If both shifted factors vanish modulo p squared, the unit k fixes each first coordinate modulo p squared, and the physical widths again fix both actual endpoints. This remaining class has at most one pair. The three classes cover the entire fiber, including nonunit right sides and repeated endpoints.

This estimate supplies the endpoint cost in the removed unit-chart pieces. Summing the original middle parameters, counting nonunit shortest vectors, and counting nonunit endpoint incidences are separate requirements; the elementary fiber bound alone is not a full six-tuple estimate.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalElementaryFibers.actual_endpoint_pair_elementary_count`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers](PascadiOriginalLinearFibers.md)
