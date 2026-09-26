# Colliding blocks: where the collision count leaves floor(pi sqrt n), it sets a record

## Abstract

For the number a(n) of elastic collisions between a block of mass n, a block of mass 1 and a wall, every n at which a(n) differs from floor(pi sqrt(n)) is a position of a record of a (OEIS A331859, conjecture of Kagey).

**Definition 1.1 (The collision count of the colliding blocks).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{ceil}\left(\frac{\pi}{\operatorname{arctan}\left(\sqrt{\frac{1}{n}}\right)}\right) - 1$$

*Formalization.* `D5/S3/Constants/Billiards/CollidingBlocksRecords.a` (`✓ std3`).

*Citation.* Peter Kagey (2020). *OEIS A331859, The total number of elastic collisions between a block of mass n, a block of mass 1, and a wall*. URL: <https://oeis.org/A331859>.

*Commentary.*

OEIS A331859, COMMENTS: "Suppose there is a block A of mass n sliding left toward a stationary block B of mass 1, to the left of which is a wall. Assuming the sliding is frictionless and the collisions are elastic, a(n) is the number of collisions between A and B plus the number of collisions between B and the wall." The definition is the entry's FORMULA line "a(n) = ceiling(Pi/arctan(sqrt(1/n))) - 1.", Galperin's count of these collisions, for n at least one.

**Definition 1.2 (The conjecture of OEIS A331859).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow ((\operatorname{a}\left(n\right) \ne \left\lfloor\pi \cdot \sqrt{n}\right\rfloor) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow ((k < n) \Rightarrow (\operatorname{a}\left(k\right) < \operatorname{a}\left(n\right))))))$$

*Formalization.* `D5/S3/Constants/Billiards/CollidingBlocksRecords.claim` (`✓ std3`).

*Citation.* Peter Kagey (2020). *OEIS A331859, The total number of elastic collisions between a block of mass n, a block of mass 1, and a wall*. URL: <https://oeis.org/A331859>.

*Commentary.*

OEIS A331859, COMMENTS: "Conjecture: The values of n for which a(n) != A121854(n) is a subset of A331903." Here A121854(n) = floor(Pi*(sqrt(n))), and A331903, the positions of records in A331859, consists of the n at least one with a(k) < a(n) for all k with 1 <= k < n.

**Theorem 1.3 (Every exceptional n is a record position).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Billiards/CollidingBlocksRecords.result` (`✓ std3`). ∎

*Resolves.* `Problems/kagey-2020-a331859-colliding-blocks-records` (proved) by `D5/S3/Constants/Billiards/CollidingBlocksRecords.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kagey-2020-a331859-colliding-blocks-records","declaration_gid":"D5/S3/Constants/Billiards/CollidingBlocksRecords.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2020). *OEIS A331859, The total number of elastic collisions between a block of mass n, a block of mass 1, and a wall*. URL: <https://oeis.org/A331859>.

*Commentary.*

Write t(m) = arctan(sqrt(1/m)), so that a(m) is the largest integer strictly below pi/t(m). Since t decreases, a is nondecreasing. Since arctan y < y for y > 0 (from y < tan y), t(n) < 1/sqrt(n), so pi/t(n) > pi sqrt(n) and a(n) >= floor(pi sqrt(n)). For n >= 2, sin t(n - 1) = 1/sqrt(n) and sin t < t, so t(n - 1) > 1/sqrt(n) and pi/t(n - 1) < pi sqrt(n). If a(n) differs from floor(pi sqrt(n)), then a(n) >= floor(pi sqrt(n)) + 1 > pi sqrt(n) > pi/t(n - 1) > a(n - 1) >= a(k) for every k < n, so n is a record position; for n = 1 there is no k to compare.

## References

- Truth anchor: `D5/S3/Constants/Billiards/CollidingBlocksRecords.a`
- Truth anchor: `D5/S3/Constants/Billiards/CollidingBlocksRecords.claim`
- Truth anchor: `D5/S3/Constants/Billiards/CollidingBlocksRecords.result`
