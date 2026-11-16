# Sizes and nilpotency of cyclic terminal semigroups

## Abstract

The cyclic terminal semigroups have exact sizes, product sets and nilpotency indices.

**Definition 1.1 (Products without an identity).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.positiveProduct`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanCyclicGrading.positiveProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The index k denotes a right associated product of k+1 arbitrary factors. No identity or empty product is inserted. Associativity makes the choice of bracketing immaterial.

**Definition 1.2 (Degree of a normal form).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.degree`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanCyclicGrading.degree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

A surviving lower monomial retains its total degree. Each terminal has degree n, and zero has degree zero. A nonzero product has the sum of the degrees of its factors. Every nonzero element has positive degree when n is positive, and no normal form has degree greater than n.

**Theorem 1.3 (Exact semigroup and algebra nilpotency).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.nilpotency`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicGrading.nilpotency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every positive n, either presentation and every field F, all products of n+1 semigroup elements vanish. The nth power of the first generator is a nonzero terminal. In the actual contracted algebra, the whole subspace spanned by arbitrary products of n+1 factors is zero, and every such product vanishes. The nth power of the first generator's basis image is nonzero. Thus both nilpotency indices are exactly n+1. The algebra upper bound applies to arbitrary vectors, rather than only to powers of the cancellation vector. The span of the basis images of all semigroup products equals the corresponding mixed-power subspace. This general correspondence transfers the semigroup degree bound to arbitrary algebra vectors. The terminal-partition and noncommutative families consume this same correspondence.

**Theorem 1.4 (Exact carrier sizes and contracted dimensions).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.cardinalities`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicGrading.cardinalities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For n at least two, the cyclic carrier has choose(n+2,3)+3 elements and the xyz-zero quotient has 3n(n-1)/2+4 elements. Over every field their contracted dimensions are choose(n+2,3)+2 and 3n(n-1)/2+3. These conclusions apply in particular to every positive multiple of six. The lower monomials are the existing bounded multisets. Removing one copy of x,y,z is a bijection from the mixed lower monomials to all monomials of degree at most n-4 when n is at least four. In the smaller cases there are no mixed lower monomials. The remaining basis consists of the surviving lower monomials and three terminals; the semigroup zero is excluded from the vector-space basis.

**Definition 1.5 (Actual generator product sets).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.generatorProducts`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanCyclicGrading.generatorProducts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

This is the set of all products of k+1 elements of the actual three generator set. The definition includes any product equal to zero; the counting statements remove zero explicitly.

**Theorem 1.6 (Products and monomials correspond).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.product_sets`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicGrading.product_sets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every n, either presentation and every k, the actual products of k+1 generators are precisely the reductions of all degree-(k+1) monomials. Both inclusions use actual multiplication: a word reduces to the sum of its exponent multiset, and every multiset has a word representative.

**Theorem 1.7 (Counts below the terminal degree).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.lower_product_counts`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicGrading.lower_product_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every degree d with 0<d<n, the nonzero actual generator products number choose(d+2,2) in the cyclic carrier and 3d in its quotient. The correspondence identifies them with all degree-d monomials, or with those not divisible by xyz. Removing xyz from a mixed monomial gives the degree-(d-3) symmetric power when d is at least three; there are no mixed monomials in degrees one and two.

**Theorem 1.8 (Three terminal products and an excluded zero).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.terminal_products`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicGrading.terminal_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For n at least three, the nonzero degree-n generator products are exactly the three distinct terminal normal forms. Each is attained by a pure generator power. The degree-n monomial xyz times x^(n-3) reduces to zero, so the actual product set also contains zero. The nonzero cardinality three explicitly excludes this zero.

At n=6 the sizes are 59 and 49, the dimensions are 58 and 48, and the exact indices are seven. The nonzero generator product counts in degrees one through six are (3,6,10,15,21,3) and (3,6,9,12,15,3). A degree-six word containing x,y,z reduces to zero in both carriers, so zero belongs to the sixth product set and is excluded from these tuples. This establishes the stated Question-11 instance counts; it does not settle the universal question.

These are the cyclic presentation and its xyz-zero quotient. The original Question-15 refutation retains its distinct 59-element partition. The coefficient and field criteria retain their separate hypotheses. No new binomial identity or literature priority is claimed. The n=35 partition is a derived unfolding of von zur Gathen and Roche; their Theorem 4.4 proofs are omitted. The square-zero identity of Almeida, Margolis, Steinberg and Volkov and the binomial identities of Benjamin and Scott remain prior results.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.cardinalities`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.degree`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.generatorProducts`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.lower_product_counts`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.nilpotency`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.positiveProduct`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.product_sets`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicGrading.terminal_products`
- Dependency: [D5/S0/Certificates/Algebra/BergmanCyclicCoefficients](BergmanCyclicCoefficients.md)
