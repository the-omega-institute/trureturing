# The Catalan Power Moment Dictionary

## Abstract

The Jacobi recurrence expresses odd Catalan power coefficients as moments of a monic orthonormal polynomial family.

**Theorem 1.1 (Normalized orthogonality and Catalan moments).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenMoments.moment_dictionary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenMoments.moment_dictionary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

Specialize the boundary-weighted Motzkin orthogonal polynomials to interior weight two and boundary weight one. The resulting rational polynomials satisfy p_0 = 1, p_1 = X-1 and p_{j+2} = (X-2)p_{j+1}-p_j. There exists a rational linear functional L on rational polynomials such that L(p_a p_b) is one when a equals b and zero otherwise, and L(X^t p_k) = C_{2k+1,t-k} for all nonnegative integers t and k. This includes the zero moments when t is less than k. The Jacobi operator acts on sequences by (Jv)_0 = v_0+v_1 and (Jv)_{j+1} = v_j+2v_{j+1}+v_{j+2}; L(f) is the zeroth coordinate of f(J) applied to the zeroth unit vector. Its powers have coordinates binom(2t,t+k)-binom(2t,t+k+1), which satisfy the two-step Pascal recurrence and identify the Catalan coefficients.

## References

- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenMoments.moment_dictionary`
- Dependency: [D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs](CiglerElevenDefs.md)
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal](../MotzkinHankel/CiglerMotzkinHankelOrthogonal.md)
