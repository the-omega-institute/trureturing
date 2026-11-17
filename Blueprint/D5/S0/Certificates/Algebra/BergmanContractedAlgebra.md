# Contracted semigroup algebras without an identity

## Abstract

The contracted algebra construction also applies to noncommutative semigroups with zero.

**Theorem 1.1 (Products of scalar basis vectors).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.single_mul`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.single_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Let F be any field and S have a multiplication and a distinguished zero. Use exactly the contracted vector space and bilinear product of the Question 15 construction. The product of the scalar basis vectors r delta_a and t delta_b is (rt) delta_(ab). If ab is zero, its image is the zero vector, rather than a new basis vector.

**Definition 1.2 (Scalars and left multiplication).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.contractedSMulCommClass`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.contractedSMulCommClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The field action commutes with multiplication by an algebra element. This is the scalar law a(r b)=r(ab).

**Definition 1.3 (Scalars in the first factor).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.contractedScalarTower`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.contractedScalarTower` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The other scalar law is (r a)b=r(ab). Together these laws express the bilinearity of the original product.

**Theorem 1.4 (Multiplicative basis images).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.delta_mul`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.delta_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every semigroup with absorbing zero, delta_a delta_b=delta_(ab), including when a, b or their product is zero. No commutativity hypothesis is used.

**Definition 1.5 (The nonunital associative ring).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.contractedRing`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.contractedRing` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

If S is a semigroup with absorbing zero, its original contracted vector space over any field is a nonunital associative ring, with the same multiplication. Associativity reduces by linear induction to the semigroup associativity law. Neither an identity nor commutativity is required. For a commutative S the existing commutative structure uses this identical product.

**Definition 1.6 (The induced linear map).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.map`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.map` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Given a function f from S to T, send each nonzero basis element s to delta_(f(s)) and extend linearly over the same field. This construction uses the original nonzero-element basis on each carrier.

**Theorem 1.7 (The image of every semigroup element).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.map_delta`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.map_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

When f sends zero to zero, the induced map sends every delta_s to delta_(f(s)), including s=0. A nonzero element may be sent to zero, as is necessary for a contracted quotient map.

**Theorem 1.8 (Multiplication under the linear extension).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.map_mul`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.map_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Suppose S and T are semigroups with absorbing zero, and f preserves zero and multiplication. For arbitrary contracted vectors a and b, the induced linear map sends ab to the product of their images. The assertion applies to all vectors, rather than only basis vectors or individual powers, and imposes no commutativity hypothesis.

**Definition 1.9 (A nonunital algebra homomorphism).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.mapHom`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.mapHom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The same linear extension is a nonunital algebra homomorphism whenever f preserves zero and multiplication. Its addition and scalar laws come from the linear map, and its product law is the preceding identity. The field needs no characteristic-zero assumption for these structural statements.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.contractedRing`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.contractedSMulCommClass`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.contractedScalarTower`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.delta_mul`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.map`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.mapHom`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.map_delta`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.map_mul`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanContractedAlgebra.single_mul`
- Dependency: [D5/S0/Certificates/Algebra/BergmanQuestion15Refutation](BergmanQuestion15Refutation.md)
