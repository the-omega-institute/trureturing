# Richman's congruence for A053871

## Abstract

For the deranged-matching numbers a(n), which are also the central moments of the chi-squared distribution with one degree of freedom, the signed values (-1)^n a(n) are periodic with period q modulo every odd q.

**Definition 1.1 (The sequence A053871).**

$$\operatorname{a}\left(0\right) = 1,\quad\operatorname{a}\left(1\right) = 0,\quad\operatorname{a}\left(n + 2\right) = 2 \cdot (n + 1) \cdot (\operatorname{a}\left(n + 1\right) + \operatorname{a}\left(n\right))$$

*Formalization.* `D5/S3/Combinatorics/DerangedMatchingCongruence.a` (`✓ std3`).

*Citation.* Harry Richman (2023). *OEIS A053871, a(n) = 2*(n-1)*(a(n-1) + a(n-2)), starting a(0) = 1; a(1) = 0; congruence conjecture of Harry Richman*. URL: <https://oeis.org/A053871>.

*Commentary.*

a(0) = 1, a(1) = 0 and a(n + 2) = 2(n + 1)(a(n + 1) + a(n)); a(n) counts the ways to re-pair n couples so that nobody is paired with the original partner.

**Definition 1.2 (Richman's conjecture).**

$$claim \Leftrightarrow (\forall q \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; (\operatorname{Odd}\left(q\right) \land m \equiv n (\mathrm{mod} q)) \Rightarrow ((-1)^{m} \cdot \operatorname{a}\left(m\right) \equiv (-1)^{n} \cdot \operatorname{a}\left(n\right) (\mathrm{mod} q)))$$

*Formalization.* `D5/S3/Combinatorics/DerangedMatchingCongruence.claim` (`✓ std3`).

*Citation.* Harry Richman (2023). *OEIS A053871, a(n) = 2*(n-1)*(a(n-1) + a(n-2)), starting a(0) = 1; a(1) = 0; congruence conjecture of Harry Richman*. URL: <https://oeis.org/A053871>.

*Commentary.*

For every odd q and all m and n that are congruent modulo q, (-1)^m a(m) and (-1)^n a(n) are congruent modulo q.

**Theorem 1.3 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DerangedMatchingCongruence.result` (`✓ std3`). ∎

*Resolves.* `Problems/richman-2023-a053871-signed-congruence` (proved) by `D5/S3/Combinatorics/DerangedMatchingCongruence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"richman-2023-a053871-signed-congruence","declaration_gid":"D5/S3/Combinatorics/DerangedMatchingCongruence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Harry Richman (2023). *OEIS A053871, a(n) = 2*(n-1)*(a(n-1) + a(n-2)), starting a(0) = 1; a(1) = 0; congruence conjecture of Harry Richman*. URL: <https://oeis.org/A053871>.

*Commentary.*

Put b(n) = (-1)^n a(n); the recurrence becomes b(n + 2) = 2(n + 1)(b(n) - b(n + 1)). The alternating sums c(n) of (-1)^k C(n, k) (2k - 1)!! and d(n) of (-1)^k C(n, k) (2k + 1)!! satisfy c(n + 1) = c(n) - d(n) by Pascal's rule and d(n + 1) = c(n + 1) - 2(n + 1) d(n) because (2k + 1)!! = (2k + 1)(2k - 1)!! and k C(n + 1, k) = (n + 1) C(n, k - 1); together they give the same recurrence for c, and c(0) = 1, c(1) = 0, so b = c. For odd q and k at least 1, 2^k C(q, k) (2k - 1)!! equals q(q - 1)...(q - k + 1) C(2k, k), which is divisible by q, and 2 is invertible modulo q, so every term of c(q) past the first is divisible by q and b(q) is 1 = b(0) modulo q. The recurrence gives b(q + 1) = 2q(b(q - 1) - b(q)), which is 0 = b(1) modulo q. Since the coefficient 2(n + 1) has period q modulo q, induction gives b(n + q) congruent to b(n) for every n, and hence the claim.

## References

- Truth anchor: `D5/S3/Combinatorics/DerangedMatchingCongruence.a`
- Truth anchor: `D5/S3/Combinatorics/DerangedMatchingCongruence.claim`
- Truth anchor: `D5/S3/Combinatorics/DerangedMatchingCongruence.result`
