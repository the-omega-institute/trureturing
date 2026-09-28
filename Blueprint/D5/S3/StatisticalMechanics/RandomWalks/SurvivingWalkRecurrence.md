# Mathar's recurrence for surviving walks from height 3

## Abstract

The number a(n) of walks s(0), ..., s(n) on the nonnegative integers with steps of size 1 and s(0) = 3 satisfies (n + 4)(n - 1) a(n) + (n - 1)(n + 1) a(n - 1) - 2(n + 1)(2n + 1) a(n - 2) - 4(n - 1)(n + 1) a(n - 3) = 0 for every n at least 3, as conjectured by R. J. Mathar for OEIS A026023. These walks are the paths of a random walker started at x = 4 that have not been adsorbed at x = 0 by time n.

**Definition 1.1 (Walks on the nonnegative integers).**

$$\operatorname{walks}\left(n, x\right) = \{s \in \operatorname{Fin}\left(n + 1\right) \to \mathbb{N} \mid s\left(0\right) = x \land \left(\forall i \in \operatorname{Fin}\left(n\right),\; (s\left(i + 1\right) = s\left(i\right) + 1 \lor s\left(i + 1\right) + 1 = s\left(i\right))\right)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.walks` (`✓ std3`).

*Citation.* R. J. Mathar (2012). *OEIS A026023, walks on the nonnegative integers from 3: recurrence conjecture*. URL: <https://oeis.org/A026023>.

*Commentary.*

walks(n, x) is the set of sequences s(0), ..., s(n) of nonnegative integers, indexed by Fin (n + 1), with s(0) = x and |s(i + 1) - s(i)| = 1 for every i < n; in Lean the index i ranges over Fin n and s(i + 1), s(i) are s at i.succ and i.castSucc.

**Definition 1.2 (The sequence A026023).**

$$\operatorname{a}\left(n\right) = \operatorname{ncard}\left(\operatorname{walks}\left(n, 3\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.a` (`✓ std3`).

*Citation.* R. J. Mathar (2012). *OEIS A026023, walks on the nonnegative integers from 3: recurrence conjecture*. URL: <https://oeis.org/A026023>.

*Commentary.*

a(n) is the number of such walks of length n starting at 3, the name of the entry.

**Definition 1.3 (Mathar's conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 3 \le n \Rightarrow ((n + 4) \cdot (n - 1) \cdot \operatorname{a}\left(n\right) + (n - 1) \cdot (n + 1) \cdot \operatorname{a}\left(n - 1\right) - 2 \cdot (n + 1) \cdot (2 \cdot n + 1) \cdot \operatorname{a}\left(n - 2\right) - 4 \cdot (n - 1) \cdot (n + 1) \cdot \operatorname{a}\left(n - 3\right) = 0))$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.claim` (`✓ std3`).

*Citation.* R. J. Mathar (2012). *OEIS A026023, walks on the nonnegative integers from 3: recurrence conjecture*. URL: <https://oeis.org/A026023>.

*Commentary.*

For every n at least 3 the four-term recurrence with quadratic coefficients holds, evaluated in the integers.

**Theorem 1.4 (Proof of the recurrence).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-2012-a026023-recurrence` (proved) by `D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-2012-a026023-recurrence","declaration_gid":"D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar (2012). *OEIS A026023, walks on the nonnegative integers from 3: recurrence conjecture*. URL: <https://oeis.org/A026023>.

*Acknowledgement.* Marilena Jianu and Leonard Dăuş (2025). *The number of Dyck-type lattice paths and related sequences*. URL: <https://dmi.utcb.ro/wp-content/uploads/2025/09/proceeeings2025.pdf>.

*Commentary.*

Let W(n, x) be the number of walks of length n from x. Splitting a walk of length n + 1 by its first step gives W(n + 1, x) = W(n, x + 1) + W(n, x - 1), the second term present only for x at least 1, and W(0, x) = 1. The reflection count R(n, x), the sum of binomial(n, d) over the d with n < 2d + x + 2 and 2d at most n + x, satisfies the same recursion by Pascal's rule, so W = R; this is Theorem 2.1 of Jianu and Daus, whose range of d is floor((n - x)/2) to floor((n + x)/2). At x = 3 and n at least 4 the sum has four consecutive terms, and Pascal's rule with the symmetry of binomial coefficients gives a(2m) = c(m) and a(2m + 1) = 2 c(m) with c(m) = binomial(2m + 2, m); the values a(0), ..., a(3) = 1, 2, 4, 8, where the sum has fewer terms, are evaluated directly and fit the same formulas. These satisfy (m + 1)(m + 3) c(m + 1) = 2(m + 2)(2m + 3) c(m). For odd n = 2j + 3 the left side of the recurrence is 12 times this relation at j; for even n = 2j + 4 it is, after multiplication by j + 2, a combination with coefficients 2(2j + 3) and 4(2j + 5) of the relations at j + 1 and j.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.a`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.result`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.walks`
