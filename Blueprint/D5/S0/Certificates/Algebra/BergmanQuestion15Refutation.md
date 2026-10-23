# Bergman's Question 15 on Contracted Semigroup Algebras

## Abstract

Distinct nonzero sixth powers of three semigroup elements do not prevent a nonzero complex vector in their contracted span from having zero sixth power.

**Definition 1.1 (The contracted vector space).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.Contracted`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.Contracted` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The vector space has the nonzero semigroup elements as a free basis.

**Definition 1.2 (Contracted basis images).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.delta`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The absorbing semigroup zero maps to the zero vector. Every other element maps to its basis vector with coefficient one.

**Definition 1.3 (Bilinear multiplication).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.product`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.product` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Extend the semigroup product bilinearly, sending products equal to the absorbing element to the zero vector. Associativity, commutativity, and distributivity follow from these basis products.

**Definition 1.4 (Positive powers without an identity).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.positivePower`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.positivePower` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Index zero means exponent one. Increasing the index multiplies once more by the same element, so index n means exponent n+1.

**Definition 1.5 (The universal assertion in Question 15).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.claim`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For an arbitrary commutative semigroup with absorbing zero, a finite subset, a positive exponent, and a field of characteristic zero, assume the power map is injective on the subset and preserves nonzero elements. The question asks whether the same nonannihilation holds on the contracted linear span. The closed assertion uses ordinary small carriers, including infinite carriers; the finite counterexample already belongs to those universes.

**Definition 1.6 (The 59 semigroup elements).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.Model`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.Model` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

There are 55 singleton monomials of degrees one through five, three terminal classes of degree six, and the absorbing zero.

**Definition 1.7 (The retained terminal classes).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.label`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.label` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Retain exactly the three classes A, B and C listed in the Route section of Problems/bergman-question15.md from the degree-six monomials; every remaining monomial becomes zero.

**Definition 1.8 (The finite multiplication).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.modelMul`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.modelMul` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Add the exponent triples of singleton classes and take their retained label. Multiplication involving zero or a terminal class gives zero.

**Definition 1.9 (The numeric multiplication table).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.tableMul`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.tableMul` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The numeric table represents the same exponent addition and contraction. Its equality with the monomial rule is checked in the proof.

**Theorem 1.10 (Question 15 has a negative answer).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bergman-question15` (refuted) by `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bergman-question15","declaration_gid":"D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Over the complex numbers take the three degree-one generators and exponent six. Their powers are the distinct nonzero terminal classes A, B and C. With ζ a primitive cube root, the vector delta_x + ζ delta_y + ζ² delta_z has x coefficient one. Its sixth power has coefficient 21(1+ζ+ζ²) in each terminal class and vanishes. Mixed monomials cause cancellation despite the pure powers remaining distinct.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.Contracted`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.Model`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.claim`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.delta`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.label`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.modelMul`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.positivePower`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.product`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.result`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.tableMul`
