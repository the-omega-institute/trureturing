# McCormack and Zelinsky's Question 44

## Abstract

Strong pseudoperfection is a strong restriction on Euler-form integers.

**Definition 1.1 (Euler forms).**

Lean statement: `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.EulerForm`

*Formalization.* `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.EulerForm` (`✓ std3`).

*Citation.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

An Euler-form integer has a representation q^s*m^2 with q prime, q and s congruent to one modulo four, m positive, and q coprime to m. No oddness condition is imposed on m. The allowed exponents include 1, 5, 9, and every further positive exponent congruent to one modulo four.

**Definition 1.2 (Counting Euler forms).**

Lean statement: `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.eulerCount`

*Formalization.* `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.eulerCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

The count is over integers from 1 to X, so different Euler representations of one integer are counted once.

**Definition 1.3 (Counting strongly pseudoperfect Euler forms).**

Lean statement: `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.eulerSPCount`

*Formalization.* `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.eulerSPCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

The count uses the existing complementary-divisor definition of strongly pseudoperfect positive integers.

**Theorem 1.4 (A strong restriction).**

Lean statement: `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.result` (`✓ std3`). ∎

*Resolves.* `Problems/mccormack-zelinsky-2023-question-44` (proved) by `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mccormack-zelinsky-2023-question-44","declaration_gid":"D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tim McCormack; Joshua Zelinsky (2023). *Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's Function*. DOI: [10.48550/arXiv.2312.11661](https://doi.org/10.48550/arXiv.2312.11661). URL: <https://arxiv.org/abs/2312.11661v4>.

*Commentary.*

The quotient eulerSPCount(X)/eulerCount(X) tends to zero. Thus being strongly pseudoperfect is a strong restriction on the Euler set, answering Question 44. This is a relative density statement; Question 43 concerns density among all integers.

For the exponent-one part q*m^2, the existing prime subset code gives q as a quotient with numerator a divisor subset sum of m^2. Hence q is at most sigma(m^2). Every positive divisor d has a decomposition b^2*a with a squarefree. The implication a*b^2 divides m^2 if and only if a*b divides m requires no coprimality between a and b. Selecting one such decomposition for each divisor injects into the finite set of positive pairs with a*b dividing m.

Interchanging finite sums and counting positive multiples gives a bound by the sum over a of T*(floor(T/a))^2. The inverse-square estimate makes this at most 2*T^3, and therefore at most 3*T^3. With T the integer part of X^(1/4), small square factors contribute at most 3*X^(3/4). Large square factors contribute at most 2*X/(T+1), at most 2*X^(3/4).

Every allowed exponent at least five is 5+4*j; absorbing q^(2*j) into m writes the integer as q^5*a^2. It follows that a*q^2 is at most the integer square root of X. Summing the resulting floor bounds over q at least two contributes at most sqrt(X). These are upper bounds on images of parameter sets, so repeated representations do not require uniqueness.

Consequently eulerSPCount(X) is at most 6*X^(3/4) for X at least sixteen. Every prime congruent to one modulo four is an Euler form with s=m=1. The classical Dirichlet--Mertens estimate used here gives at least exp(-50)*X/log(X) such primes for X at least exp(50). The ratio is bounded by 6*exp(50)*log(X)/X^(1/4), which tends to zero. The integer five also witnesses strict positivity of the denominator for X at least five.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.EulerForm`
- Truth anchor: `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.eulerCount`
- Truth anchor: `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.eulerSPCount`
- Truth anchor: `D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity.result`
- Dependency: [D5/S3/Arith/Abundancy/StrongPseudoperfectDensity](StrongPseudoperfectDensity.md)
- Dependency: [D5/S3/PrimeGaps/ModFourChebyshev](../../PrimeGaps/ModFourChebyshev.md)
