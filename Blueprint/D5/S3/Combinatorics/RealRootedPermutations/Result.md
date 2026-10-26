# All unimodal coefficient orders arise

## Abstract

Exactly the unimodal permutations occur as coefficient orders of products of positive linear factors.

**Theorem 1.1 (Answer to Question 4.6).**

Lean statement: `D5/S3/Combinatorics/RealRootedPermutations/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RealRootedPermutations/Result.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Ball, D. Galvin, C. Hyry, and K. Weingartner (2022). *Independent set and matching permutations*. DOI: [10.1002/jgt.22724](https://doi.org/10.1002/jgt.22724). URL: <https://doi.org/10.1002/jgt.22724>.

*Commentary.*

For every natural n and permutation of Fin(n+1), there are n+1 strictly positive real parameters whose nonconstant product coefficients weakly increase in that permutation order if and only if the permutation is unimodal. Value v denotes coefficient index v+1, so the constant coefficient is omitted. The definitions follow equations (1) and (4) of the cited article, and the conclusion answers Question 4.6 in Section 4 for polynomials of full degree.

LogConcave.unimodal_of_arises gives the necessary condition, including weak orders with a tie at the coefficient maximum. Realization.realize_strict gives the sufficient condition with strictly increasing coefficients, hence also a weak order. The realization uses integer exponent heights and a base larger than the number of subset terms. The classification of unweighted graph matching permutations is a separate question.

## References

- Truth anchor: `D5/S3/Combinatorics/RealRootedPermutations/Result.result`
- Dependency: [D5/S3/Combinatorics/RealRootedPermutations/LogConcave](LogConcave.md)
- Dependency: [D5/S3/Combinatorics/RealRootedPermutations/Realization](Realization.md)
