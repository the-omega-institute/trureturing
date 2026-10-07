# Bounded Strips of Shifted Hankel Determinants

## Abstract

Exponential coefficient growth and bounded determinant rows at two shifts give a bound independent of determinant size at every intermediate shift.

**Theorem 1.1 (A uniform bound between two bounded rows).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedStrip.bounded_strip`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedStrip.bounded_strip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let Phi be an integral formal power series, let a, b and B be nonnegative integers with a at most b, and let M be a positive integer. Suppose that the absolute value of [q^m]Phi is at most B^m for every nonnegative integer m, and that the absolute values of both Delta_j^{(a)} and Delta_j^{(b)} are at most M for every nonnegative integer j. Then for every integer ell between a and b and every nonnegative integer j, the absolute value of Delta_j^{(ell)} is strictly less than 2^{floor(log_2 M)+2(ell-a)(b-ell)+1}. Here Delta_j^{(ell)} is the shifted Hankel determinant of Phi, with empty determinant one. The bound is independent of j and B; B is used only in the coefficient-growth hypothesis. In particular, two bounded rows force all intervening rows to be bounded.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedStrip.bounded_strip`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedJacobi](MetallicHankelUnboundedJacobi.md)
