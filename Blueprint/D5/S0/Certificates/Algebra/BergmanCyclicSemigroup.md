# Cyclic terminal monomial semigroups

## Abstract

Cyclic terminal relations give commutative semigroups with a literal xyz-zero quotient.

**Definition 1.1 (The normal forms).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.Model`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.Model` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For a positive integer n, the carrier has an absorbing zero, the distinct monomials of degrees one through n-1, and three distinct terminal elements. The Boolean q specifies whether lower monomials divisible by xyz are also removed. Monomials use the existing bounded multiset representation; no constant monomial or multiplicative identity is added.

**Definition 1.2 (The terminal lists).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.terminalLabel`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.terminalLabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The first terminal class consists of degree-n monomials in x,y with a positive x exponent; the second consists of those in y,z with a positive y exponent; the third consists of those in z,x with a positive z exponent. Degree-n monomials involving all three generators are zero. These are the cyclic lists, rather than the earlier Question-15 partition.

**Theorem 1.3 (Reduction and multiplication).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.normal_mul`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.normal_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every natural n, either Boolean q, and any two positive-degree monomials a,b, the product of their reductions is the reduction of a+b. If a factor has already reached degree n, every further positive-degree multiple is zero. Divisibility by xyz is preserved under multiplication. These facts ensure that reduction is compatible with the full multiplication.

**Definition 1.4 (A commutative semigroup with zero).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.modelSemigroup`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.modelSemigroup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Both bracketings of a triple product reduce the same sum of monomials. The resulting multiplication is associative, and zero absorbs on both sides. Commutativity follows from addition of monomial multisets.

**Theorem 1.5 (Actual generator powers).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.generator_power`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.generator_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The positivePower index k denotes k+1 factors, with no zeroth power. For every generator i, its positivePower at index k is precisely the reduction of k+1 copies of i.

**Theorem 1.6 (Distinct nonzero nth powers).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.terminal_powers`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.terminal_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every positive n and either presentation, generator i raised to the nth power is the terminal constructor with label i. In particular all three terminal powers are nonzero and pairwise distinct. This applies to every positive multiple of six, without a field hypothesis.

**Theorem 1.7 (The generators generate the entire semigroup).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.generated`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.generated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every positive n, the subsemigroup generated by the three degree-one elements is the whole carrier. Every normal form has a positive monomial representative, including zero, represented by n+1 copies of x.

**Theorem 1.8 (Every normal form is attained).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.normal_surjective`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.normal_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every positive n and either value of q, every carrier element is the reduction of a positive monomial. This connects the literal carrier to the generators and the presentation, including its absorbing zero.

**Theorem 1.9 (The quotient homomorphism).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.quotient_mul`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.quotient_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The map from q=false to q=true preserves zero and multiplication. It fixes the three terminals and each lower monomial not divisible by xyz, and sends every lower multiple of xyz to zero. The map is surjective.

**Theorem 1.10 (Every quotient element is attained).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.quotient_surjective`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.quotient_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Each surviving lower monomial and each terminal has the identical normal form as a preimage in the cyclic carrier; zero has zero as a preimage. This is surjectivity of the actual map on the full carriers.

**Theorem 1.11 (The exact fibers).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.quotient_fibers`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.quotient_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Two cyclic normal forms have the same quotient image exactly when they are equal, or both belong to the ideal consisting of zero and the lower monomials divisible by xyz. Every nonzero quotient fiber is a singleton; no terminal powers are identified.

Over any field, applying BergmanContractedAlgebra.mapHom to quotient, its zero-preservation equation and quotient_mul gives a homomorphism between the original contracted nonunital algebras. It sends each basis image to the basis image of its quotient, and sends a collapsed monomial to the zero vector. No characteristic or root-of-unity premise is needed for this structural map. Cancellation and the field criterion require their separate coefficient arguments.

**Theorem 1.12 (Completeness of the written presentation).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.normal_form_complete`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.normal_form_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Start with the free commutative semigroup on x,y,z and an absorbing zero. Take the congruence generated by the cyclic degree-n lists, the degree-n all-three-variable zero relations, the degree-(n+1) zero relations, and optionally the single relation xyz=0. Two words are equivalent under this generated congruence if and only if their normal forms agree. Thus the normal forms impose exactly the stated relations, with neither missing identifications nor additional ones.

The original Question-15 refutation retains its separate 59-element partition. The cyclic presentation and its xyz-zero quotient are the presentations used in the revised examples. At n=6 the positive monomials of degrees at most five number 55, by the existing bounded-multiset cardinality result. Subtraction of one copy of each generator identifies the 10 lower multiples of xyz with the monomials of degree at most two. Thus the cyclic carrier has 55+3+1=59 elements and its quotient has 45+3+1=49 elements. These count the actual normal-form carriers. General cardinalities, coefficient cancellations, field criterion, product-set counts and exact nilpotency indices are separate assertions. No universal conclusion for Question 11, Questions 16-18, or the characteristic-p Eggert conjecture follows from the structural statements here.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.Model`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.generated`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.generator_power`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.modelSemigroup`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.normal_form_complete`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.normal_mul`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.normal_surjective`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.quotient_fibers`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.quotient_mul`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.quotient_surjective`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.terminalLabel`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicSemigroup.terminal_powers`
- Dependency: [D5/S0/Certificates/Algebra/BergmanQuestion23Refutation](BergmanQuestion23Refutation.md)
