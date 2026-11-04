# Entire weighted Hankel kernels and exponential polynomials

## Abstract

Finite separation of the entire quadratic weighted Hankel kernel is equivalent to an exponential-polynomial presentation.

**Theorem 1.1 (Finite separation on the whole complex plane).**

Lean statement: `D5/S3/Analytic/Entire/ExponentialPolynomial.finite_weighted_separation_iff_exponential_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/ExponentialPolynomial.finite_weighted_separation_iff_exponential_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quantifier is every entire complex-valued function on Complex. Finite separation means that some natural k and two families of k entire factors represent (z-w)^2*f(z+w) at every complex pair. An exponential polynomial is a finite sum exp(alpha_i*z)*P_i(z), with arbitrary complex exponents and arbitrary complex polynomial coefficients. Repeated exponents and zero polynomials are allowed in this presentation.

Two applications of the difference of the scalar partial derivatives remove the quadratic weight and produce 8*f(z+w). The complete span of all complex translates of f is then finite dimensional. Its product topology is Hausdorff, and finite dimension makes the subspace closed. Pointwise convergence of actual difference quotients proves that scalar differentiation preserves it. No unbounded differentiation operator on a Fock Hilbert space is introduced.

The resulting actual derivative endomorphism decomposes into generalized eigenspaces over Complex. Multiplication by exp(-alpha*z) turns a generalized derivative eigenvector into an entire function with a vanishing iterated derivative. Polynomial primitives and the zero-derivative constant-function theorem reconstruct a genuine polynomial. Conversely, expanding each polynomial at z+w and splitting each exponential gives finitely many entire separated terms.

The statement is about entire functions and finite pointwise separation. Reconstructing actual Hilbert vectors from a completed kernel, proving factorial summability of every polynomial-exponential block, and identifying the existing physical channel are separate modules. The theorem alone does not classify rank three and proves no entropy inequality or all-input elementary-symmetric lower bound.

## References

- Truth anchor: `D5/S3/Analytic/Entire/ExponentialPolynomial.finite_weighted_separation_iff_exponential_polynomial`
- Dependency: [D5/S3/Analytic/Entire/WeightedHankel](WeightedHankel.md)
