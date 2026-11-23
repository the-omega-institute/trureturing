# A descent refinement for bounded parking words

## Abstract

An insertion operator on trivariate polynomials gives the recurrence and recovers Alexandersson’s bivariate operator at descent marker one.

**Definition 1.1 (The finite set of bounded parking words).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.literalParking`

*Formalization.* `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.literalParking` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Filter the length-n words on 1 through m by the sorted rank test.

**Theorem 1.2 (Finite-set membership).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.mem_literalParking`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.mem_literalParking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Membership in the finite set is equivalent to the literal bounded parking predicate.

**Definition 1.3 (The weighted enumerator).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.G`

*Formalization.* `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.G` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Sum the literal trivariate weight over the bounded parking words in a commutative semiring.

**Definition 1.4 (The finite maximum-letter fiber).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.topFiber`

*Formalization.* `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.topFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Keep exactly the words in which the upper-bound letter occurs r times.

**Theorem 1.5 (Exactly r copies of the maximum).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.coefficient_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.coefficient_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

For 2 ≤ m ≤ n and 1 ≤ r ≤ n − m + 1, the weight sum on the maximum-letter fiber equals the sum of the degree-r kernel coefficient over shorter words of length n − r and bound m − 1.

**Theorem 1.6 (The bound-one initial condition).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parking_base`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parking_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

There is just the word of n ones at bound one. Its weight is u^(n−1), which also gives equation (3) at v = 1.

**Definition 1.7 (The trivariate polynomial).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parkingPolynomial`

*Formalization.* `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parkingPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The variables at indices zero, one and two mark strict interior peaks, adjacent ties and strict adjacent descents, respectively.

**Definition 1.8 (The polynomial type).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.ParkingPolynomial`

*Formalization.* `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.ParkingPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The natural-coefficient polynomial ring in three variable positions.

**Definition 1.9 (Linear insertion on trivariate polynomials).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertionOperator`

*Formalization.* `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertionOperator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

For retained length ℓ and insertion size r, replace each input monomial by its degree-r kernel coefficient and extend additively with natural multiplicities.

**Theorem 1.10 (The operator on a monomial).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertionOperator_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertionOperator_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The operator on t^p u^k v^d takes the coefficient of z^r in the six-factor kernel with statistics ℓ, p, k and d.

**Theorem 1.11 (The trivariate insertion recurrence).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parkingPolynomial_operator_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parkingPolynomial_operator_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

For 2 ≤ m ≤ n, the terms with no m give the same-length enumerator at bound m − 1. For each r from 1 through n − m + 1, apply the insertion operator to the enumerator at length n − r and bound m − 1.

**Definition 1.12 (The bivariate operator of equation (11)).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.bivariateInsertionOperator`

*Formalization.* `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.bivariateInsertionOperator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

For a bivariate polynomial F, substitute the actual power series B/A² and C/A, multiply by E² A^(ℓ−1), and extract the coefficient of z^r.

**Definition 1.13 (The bivariate polynomial).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.bivariateParkingPolynomial`

*Formalization.* `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.bivariateParkingPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The variables at indices zero and one mark peaks and ties. Each descent contributes the unit weight.

**Theorem 1.14 (Substitute one for the descent marker).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.specialize_descent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.specialize_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The polynomial homomorphism mapping the third variable to one and keeping the first two variables yields the bivariate parking polynomial.

**Definition 1.15 (Equation (11) on the enumerator).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertEq11`

*Formalization.* `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertEq11` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Apply the bivariate insertion operator to the peak-and-tie enumerator of the retained length and bound.

**Theorem 1.16 (The specialized coefficient sum).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertEq11_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertEq11_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

For a positive retained length the bivariate operator is the sum of the specialized degree-r kernel coefficients over the literal retained words.

**Theorem 1.17 (Recover equation (2)).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parking_recurrence_eq11`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parking_recurrence_eq11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

Apply the specialized operator in each positive maximum-letter fiber. The insertion range and the zero-multiplicity term are precisely those of equation (2).

**Theorem 1.18 (Problem 10.3).**

Lean statement: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Per Alexandersson (2026). *Real-rootedness and interlacing for parking functions and Chow polynomials*. DOI: [10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131). URL: <https://arxiv.org/html/2609.05131v2>.

*Commentary.*

The bound-one initial values, arbitrary-length trivariate recurrence, descent-marker substitution, equation (10) factors and equation (2) with its equation (11) operator hold on the bounded parking-word enumerators.

## References

- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.G`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.ParkingPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.bivariateInsertionOperator`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.bivariateParkingPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.coefficient_fiber`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertEq11`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertEq11_coeff`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertionOperator`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertionOperator_monomial`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.literalParking`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.mem_literalParking`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parkingPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parkingPolynomial_operator_recurrence`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parking_base`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.parking_recurrence_eq11`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.result`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.specialize_descent`
- Truth anchor: `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.topFiber`
- Dependency: [D5/S3/Combinatorics/Parking/DescentGapKernel](DescentGapKernel.md)
- Dependency: [D5/S3/Combinatorics/Parking/MaximumLetterGaps](MaximumLetterGaps.md)
