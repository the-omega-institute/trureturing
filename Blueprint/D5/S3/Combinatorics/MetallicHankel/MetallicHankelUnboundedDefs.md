# The Large-Shift Metallic Hankel Conjecture

## Abstract

For every positive metallic parameter, each shifted Hankel determinant sequence at shifts at least n+3 is unbounded in absolute value.

**Definition 1.1 (Unboundedness at every large shift).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedDefs.claim`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For every integer n at least one, there exists an integral formal power series Phi with constant coefficient one satisfying q Phi^2 + ((1+q^n)(1-q)-q[n]_q)Phi = 1, where [n]_q = 1+q+...+q^{n-1}. For every such Phi, every integer ell at least n+3 and every nonnegative integer M, there is a nonnegative integer j such that the absolute value of Delta_j^{(ell)} exceeds M. Here Delta_j^{(ell)} is the determinant of the j by j matrix with entry [q^{ell+a+b}]Phi, with row and column indices starting at zero and empty determinant one. This is part 2 of Conjecture E of Han and Pedon, with ell as the varying shift.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedDefs.claim`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs](MetallicHankelDefs.md)
