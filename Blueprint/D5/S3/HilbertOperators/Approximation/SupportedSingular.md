# Approximation from a Complete Supported Singular System

## Abstract

Complete real supported coordinates determine approximation numbers on the entire original input space, including an arbitrary orthogonal kernel.

**Definition 1.1 (All Bounded Finite Rank Competitors).**

Lean statement: `D5/S3/HilbertOperators/Approximation/SupportedSingular.approximationNumber`

*Formalization.* `D5/S3/HilbertOperators/Approximation/SupportedSingular.approximationNumber` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *Approximation numbers of bounded operators and infinite diagonal operators*. URL: <https://github.com/TauCetiProject/TauCeti/blob/b3de655482f7b86c77d8982566e5a73801fd64fa/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean>.

*Commentary.*

For any real bounded linear operator T from E to F and any natural n, approximationNumber(T,n) is the real infimum of norm(T-R) over every bounded real linear R from the same E to the same F whose actual cardinal rank is at most n. The index is zero based. No finite dimension of the ambient codomain, chosen diagonal class of competitors, or choice of singular values enters this definition.

**Theorem 1.2 (Exact Error with the Full Kernel Retained).**

Lean statement: `D5/S3/HilbertOperators/Approximation/SupportedSingular.approximationNumber_eq_supported`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/SupportedSingular.approximationNumber_eq_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E,F,G be real inner product spaces, let K be a subspace of E admitting orthogonal projection, and let k and e be complete Hilbert bases indexed by the natural numbers of K and G. Let T:E to F and A:E to G be bounded real linear operators, and let J:G to F be a linear isometry. Assume T(x)=J(A(x)) for every x. For a nonnegative antitone real sequence d, assume that the e coefficient of A(x) at i equals d(i) times the k coefficient of the orthogonal projection of x onto K, for every x and i. Then, for every natural n, approximationNumber(T,n)=d(n). There is no convergence, strict positivity, injectivity, finite kernel, distinct eigenvalue, or finite ambient rank premise.

The coordinate identity and completeness imply that T vanishes on the orthogonal complement of K and sends k(i) to d(i)J(e(i)). When every d(i) is positive, its kernel is precisely that orthogonal complement. Thus the coefficients belong to the same operator realization and the entire support, rather than an independently chosen scalar sequence. If d tends to zero, the constructed finite rank approximants converge in operator norm.

For the upper bound retain the first n output modes of A and then apply J. The resulting operator has range in the span of n actual ambient output vectors. Parseval and the antitone bound give error at most d(n) on every input, since orthogonal projection onto K is a contraction. For the lower bound, an arbitrary bounded competitor Q of actual rank at most n has linearly dependent images of the first n+1 input modes. A nonzero combination killed by Q has squared input norm equal to the sum of squared coefficients, while its T image has squared norm equal to the sum weighted by d(i) squared. Antitonicity gives error at least d(n). This argument includes n=0 and every repeated coefficient.

Finite rank truncation and the dimension obstruction are classical approximation number methods. The scalar generic diagonal and projection results in Tau Ceti and the Kitware formalization supply related methods; the result here starts from complete supported coordinates on arbitrary real carriers and compares all bounded competitors on the full carrier. It does not assert a new classical approximation theorem or a literature novelty claim.

## References

- Truth anchor: `D5/S3/HilbertOperators/Approximation/SupportedSingular.approximationNumber`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/SupportedSingular.approximationNumber_eq_supported`
