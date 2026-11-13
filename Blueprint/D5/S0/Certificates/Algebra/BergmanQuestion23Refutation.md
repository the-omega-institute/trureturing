# Bergman's Question 23: the monomial model

## Abstract

A coefficient model for the positive ideal of a truncated monomial idealization.

**Definition 1.1 (Mixed product spaces).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.mixedPower`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.mixedPower` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

Index k means exactly k+1 factors from V. The recursion uses the span of the actual bilinear multiplication image of two subspaces, rather than the set of pure powers of individual vectors.

**Definition 1.2 (The relative annihilator).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.relativeAnnihilator`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.relativeAnnihilator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

This is a submodule of V whose elements annihilate every vector of W. The quotient in the question is the quotient of V by this submodule.

**Definition 1.3 (The complete universal question).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.claim`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

For every field and every vector space with an associative commutative bilinear multiplication, every finite dimensional subspace V and every positive exponent, the question asks whether the dimension of the annihilator quotient is at most the dimension of the mixed product space. No identity, finite ambient dimension, nilpotence or characteristic hypothesis is imposed. Ordinary small carriers include all the proposed finite counterexamples.

**Definition 1.4 (Monomial labels).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.Monomial`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.Monomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

A monomial is a multiset on m variables. Its cardinality is its total degree. Multiset addition adds exponents and uses no factorials.

**Definition 1.5 (Positive monomials).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.PositiveIndex`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.PositiveIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

The e labels have degrees from one through t, inclusive.

**Definition 1.6 (Dual monomials).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.DualIndex`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.DualIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

The f labels have underlying monomial degrees from zero through t.

**Definition 1.7 (The finite carrier).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.Model`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.Model` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

The absorbing zero is separate from the e and f families. The contracted algebra has precisely the nonzero labels as its vector space basis.

**Definition 1.8 (The truncated multiplication).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.modelMul`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.modelMul` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

Two e labels multiply by multiset addition when their sum has degree at most t, and give zero otherwise. An e label a times an f label b gives f(b-a) when a is contained in b with multiplicity, and zero otherwise. Two f labels multiply to zero. The symmetric rule is extended bilinearly through the existing contracted algebra construction.

**Definition 1.9 (The positive ideal).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.Ambient`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.Ambient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

Over any field, this is the contracted algebra of the finite carrier. It models the positive ideal, rather than the entire unital Stanley idealization.

**Definition 1.10 (The reversed dual grading).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.labelDegree`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.labelDegree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

An e label has its monomial degree. The degree of an f label b is t+1 minus the degree of b, so every nonzero label has positive degree.

**Definition 1.11 (The actual homogeneous subspaces).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.layer`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.layer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

The degree d subspace consists of the finitely supported coefficient vectors supported on labels of degree d.

**Definition 1.12 (The actual quotient-to-product dimension ratio).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.dimensionRatio`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.dimensionRatio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

Use the real quotient of the actual annihilator quotient dimension by the dimension of the actual n-fold mixed product span of the designated degree-one subspace, in the model with truncation t=n+1.

**Definition 1.13 (The full family specification).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.familyProperties`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.familyProperties` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

Let R be the positive ideal with t=n+1, V its degree-one subspace, W its n-fold mixed product space and A the annihilator of W in V. The specification includes finite dimensional R and W, W equal to the degree-n subspace, A equal to zero, all four dimension formulas, the exact positive dimension deficit, annihilation of every product of n+3 ambient elements and the stated lower bound for the real ratio.

**Theorem 1.14 (The complete parameter family).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.family`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

For every field F and every integer n at least two, every integer m at least three satisfies the full family specification. The actual n-fold mixed product space is exactly the degree-n subspace, with e labels of monomial degree n and f labels of monomial degree two; its relative annihilator in V is zero. R and the product space are finite dimensional.

The dimensions of R, V, W and V/A are respectively two times binomial (m+n+1,n+1) minus one; m plus binomial (m+n,n+1); binomial (m+n-1,n) plus binomial (m+1,2); and the dimension of V. The exact quotient-minus-product deficit is binomial (m+n-1,n+1) minus binomial (m,2), at least binomial (m,3), and the quotient dimension is strictly larger than the product dimension.

Every product of n+3 elements of R is zero. The real dimension ratio is at least (m+n)/(2(n+1)). For each fixed F and n, every real C is exceeded by the actual ratio for some m at least three. The construction is a coefficient presentation of the classical Stanley idealization; see Library/Certificates/stanley1978hilbert.md. The entire unital idealization has one more dimension than R.

**Theorem 1.15 (Question 23 has a negative answer).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bergman-question23` (refuted) by `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bergman-question23","declaration_gid":"D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Acknowledgement.* Richard P. Stanley (1978). *Hilbert Functions of Graded Algebras*. DOI: [10.1016/0001-8708(78)90045-2](https://doi.org/10.1016/0001-8708(78)90045-2). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/30.pdf>.

*Commentary.*

The complete universal assertion is false. Its literal negation follows by taking F rational, n equal to two and m equal to three in the full family. The actual positive ideal has dimension 39, V and its annihilator quotient have dimension 13, and V squared has dimension 12. No extra assumption is added to the original universal claim.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.Ambient`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.DualIndex`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.Model`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.Monomial`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.PositiveIndex`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.claim`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.dimensionRatio`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.family`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.familyProperties`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.labelDegree`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.layer`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.mixedPower`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.modelMul`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.relativeAnnihilator`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.result`
- Dependency: [D5/S0/Certificates/Algebra/BergmanQuestion15Refutation](BergmanQuestion15Refutation.md)
