# Mathar's recurrence for A068551

## Abstract

The sequence a(n) = 4^n - binomial(2n, n), the total number of returns to the axis in all lattice paths with steps (1,1) and (1,-1) from the origin to (2n, 0), satisfies n a(n) + 2(3 - 4n) a(n - 1) + 8(2n - 3) a(n - 2) = 0 for every n at least 2, as conjectured by R. J. Mathar for OEIS A068551.

**Definition 1.1 (The sequence A068551).**

$$\operatorname{a}\left(n\right) = 4^{n} - \operatorname{choose}\left(2 \cdot n, n\right)$$

*Formalization.* `D5/S3/Combinatorics/LatticeReturnsRecurrence.a` (`✓ std3`).

*Citation.* R. J. Mathar (2012). *OEIS A068551, a(n) = 4^n - binomial(2n, n): recurrence conjecture*. URL: <https://oeis.org/A068551>.

*Commentary.*

a(n) = 4^n - binomial(2n, n), the name of the entry; it counts the returns to the x axis in all lattice paths with steps (1,1) and (1,-1) from the origin to (2n, 0).

**Definition 1.2 (Mathar's conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 2 \le n \Rightarrow (n \cdot \operatorname{a}\left(n\right) + 2 \cdot (3 - 4 \cdot n) \cdot \operatorname{a}\left(n - 1\right) + 8 \cdot (2 \cdot n - 3) \cdot \operatorname{a}\left(n - 2\right) = 0))$$

*Formalization.* `D5/S3/Combinatorics/LatticeReturnsRecurrence.claim` (`✓ std3`).

*Citation.* R. J. Mathar (2012). *OEIS A068551, a(n) = 4^n - binomial(2n, n): recurrence conjecture*. URL: <https://oeis.org/A068551>.

*Commentary.*

For every n at least 2 the three-term recurrence with linear coefficients holds.

**Theorem 1.3 (Proof of the recurrence).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatticeReturnsRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-2012-a068551-recurrence` (proved) by `D5/S3/Combinatorics/LatticeReturnsRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-2012-a068551-recurrence","declaration_gid":"D5/S3/Combinatorics/LatticeReturnsRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar (2012). *OEIS A068551, a(n) = 4^n - binomial(2n, n): recurrence conjecture*. URL: <https://oeis.org/A068551>.

*Commentary.*

Write u(n) = choose(2n, n) and v(n) = 4^n. The central binomial coefficients satisfy n u(n) = 2(2n - 1) u(n - 1), and v(n) = 4 v(n - 1). Substituting a = v - u, the left side of the recurrence equals -R(0) + 4 R(1) + n S(0) - 2(2n - 3) S(1), where R(0) = n u(n) - 2(2n - 1) u(n - 1), R(1) = (n - 1) u(n - 1) - 2(2n - 3) u(n - 2), S(0) = v(n) - 4 v(n - 1) and S(1) = v(n - 1) - 4 v(n - 2) all vanish.

## References

- Truth anchor: `D5/S3/Combinatorics/LatticeReturnsRecurrence.a`
- Truth anchor: `D5/S3/Combinatorics/LatticeReturnsRecurrence.claim`
- Truth anchor: `D5/S3/Combinatorics/LatticeReturnsRecurrence.result`
