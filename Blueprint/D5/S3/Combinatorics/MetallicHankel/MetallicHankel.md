# Han and Pedon's Metallic Hankel Conjecture, Part 1

## Abstract

For every n at least two, the shift n+2 Hankel determinants of the q-metallic series have signed period 2n(n+1) and values in {-2,-1,0,1,2}.

**Theorem 1.1 (Periodicity and values at shift n+2).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankel.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankel.result` (`✓ std3`). ∎

*Resolves.* `Problems/han-pedon-metallic-hankel-shift` (proved) by `D5/S3/Combinatorics/MetallicHankel/MetallicHankel.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"han-pedon-metallic-hankel-shift","declaration_gid":"D5/S3/Combinatorics/MetallicHankel/MetallicHankel.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For every integer n at least two, there exists an integral formal power series Phi with constant coefficient one satisfying q Phi^2 + ((1+q^n)(1-q)-q[n]_q)Phi = 1, where [n]_q = 1+q+...+q^{n-1}. For every such Phi and every nonnegative integer j, define Delta_j^{(ell)} as the determinant of the j by j matrix with entry [q^{ell+a+b}]Phi, using indices starting at zero and empty determinant one. Then Delta_{j+2n(n+1)}^{(n+2)} = (-1)^n Delta_j^{(n+2)}, and Delta_j^{(n+2)} belongs to {-2,-1,0,1,2}. Thus the determinants are periodic when n is even and antiperiodic when n is odd. Integral quadratic tails produce monic moment relations; a two-coordinate transfer bounds their constant terms and a full cycle contributes the sign (-1)^n. The determinant relations extend the conclusion across all zero intervals. These identities establish part 1 of Conjecture E of Han and Pedon; they make no assertion about unboundedness at shifts at least n+3.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankel.result`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelPeriod](MetallicHankelPeriod.md)
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransitions](MetallicHankelTransitions.md)
