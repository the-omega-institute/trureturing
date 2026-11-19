# Cayley transform and reduction of the norm-one group

## Abstract

Quadratic torus reduction and the cubic character decomposition for a prime-cube word.

**Theorem 1.1 (The cubic word as a product in the norm-one group).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiTorusConductor.cayley_word_eq_one_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiTorusConductor.cayley_word_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

In the quadratic algebra with t squared equal to minus d, the Cayley transform sends x to (1+t*x)/(1-t*x) whenever 1+d*x squared is a unit. The transform has norm one.

When 2 is invertible, the product of three transforms is one exactly when x+y+z=d*x*y*z. Clearing the three unit denominators reduces the equality to the imaginary coordinate of the difference of the two products.

**Theorem 1.2 (The kernel has order p).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiTorusConductor.primeCube_unitary_card_ker`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiTorusConductor.primeCube_unitary_card_ker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For odd prime p the reduction from the quadratic norm-one group over Z/p cubed to the one over Z/p squared is onto. A lift is corrected by a scalar equal to one minus half its norm defect. The defect lies in the square-zero ideal.

In trace-zero coordinates the kernel consists of 1+t*b with b in the additive reduction kernel. Multiplication of these elements adds their b coordinates. The base ring reduction has kernel size p.

**Theorem 1.3 (The exact prime-cube character decomposition).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiTorusConductor.primeCube_wordMass_conductor_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiTorusConductor.primeCube_wordMass_conductor_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

With an arbitrary weight on the prime-cube norm-one group, the product-one mass of ordered triples equals the corresponding mass after reduction divided by p, plus the normalized difference of the two cubic character sums.

Finite abelian character orthogonality gives each of the two cubic moments. Surjective reduction identifies the characters factoring through the square modulus with the pulled-back character family. The signed primitive moment in this identity remains the analytic estimation problem in the six-return application.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiTorusConductor.cayley_word_eq_one_iff`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiTorusConductor.primeCube_unitary_card_ker`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiTorusConductor.primeCube_wordMass_conductor_split`
