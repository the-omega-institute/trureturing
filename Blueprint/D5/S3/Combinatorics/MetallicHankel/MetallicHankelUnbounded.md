# Han and Pedon's Metallic Hankel Conjecture, Part 2

## Abstract

For every n at least one, the shifted Hankel determinants of the q-metallic series are unbounded in absolute value at every shift at least n+3.

**Theorem 1.1 (Unboundedness at all shifts at least n+3).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded.result` (`✓ std3`). ∎

*Resolves.* `Problems/han-pedon-metallic-hankel-unbounded` (proved) by `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"han-pedon-metallic-hankel-unbounded","declaration_gid":"D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For every integer n at least one, there exists an integral formal power series Phi with constant coefficient one satisfying q Phi^2 + ((1+q^n)(1-q)-q[n]_q)Phi = 1, where [n]_q = 1+q+...+q^{n-1}. For every such Phi, every integer ell at least n+3 and every nonnegative integer M, some nonnegative integer j satisfies |Delta_j^{(ell)}| > M. Here Delta_j^{(ell)} is the determinant of the j by j matrix with entry [q^{ell+a+b}]Phi, with indices starting at zero and empty determinant one. At shift n+3 there is an explicit subsequence: for every positive integer k, Delta_{Pk-1}^{(n+3)} = (-1)^{nk} 2k lambda, where P = 4 and lambda = 1 when n = 1, and P = 2n(n+1) and lambda = 2n+1 when n is at least two. The cofactor identity and dual-number transfer give this linear growth. The row at shift n+1 is bounded in absolute value by one. Exponential coefficient growth and the bounded-strip theorem then exclude boundedness at every later shift. This establishes part 2 of Conjecture E of Han and Pedon for all positive n.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded.result`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankel](MetallicHankel.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedCofactor](MetallicHankelUnboundedCofactor.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedDefs](MetallicHankelUnboundedDefs.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedGolden](MetallicHankelUnboundedGolden.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedGrowth](MetallicHankelUnboundedGrowth.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedStrip](MetallicHankelUnboundedStrip.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer](MetallicHankelUnboundedTransfer.md)
