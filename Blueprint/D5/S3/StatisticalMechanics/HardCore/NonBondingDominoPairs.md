# Two non-bonding dominoes on a rectangular board

## Abstract

Two dominoes on the r × c board are non-bonding when every square of one is at L1 distance at least 2 from every square of the other, so that they share at most a corner point: hard dimers with nearest-neighbour exclusion. For r, c at least 3 the sets of two non-bonding dominoes number 2c^2r^2 - 2(cr^2 + c^2r) + (r^2 + c^2)/2 - 22cr + (59/2)(c + r) - 30, as conjectured by R. J. Mathar (Conjecture 1 of arXiv:2404.18806).

**Definition 1.1 (Dominoes).**

$$\operatorname{IsDomino}\left(r, c, s\right) \Leftrightarrow (\exists p \in \mathbb{N}\times\mathbb{N},\; \exists q \in \mathbb{N}\times\mathbb{N},\; s = \{p, q\} \land \left(p_{1} < r \land \left(p_{2} < c \land \left(q_{1} < r \land \left(q_{2} < c \land \operatorname{dist}\left(p_{1}, q_{1}\right) + \operatorname{dist}\left(p_{2}, q_{2}\right) = 1\right)\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.IsDomino` (`✓ std3`).

*Citation.* Richard J. Mathar (2024). *Bivariate Generating Functions Enumerating Non-Bonding Dominoes on Rectangular Boards*. URL: <https://arxiv.org/abs/2404.18806v1>.

*Commentary.*

A domino on the r × c board is a set of two squares (p1, p2), (q1, q2) of the board, with p1, q1 < r and p2, q2 < c, at L1 distance 1; dist is the distance of natural numbers, |a - b|.

**Definition 1.2 (Non-bonding dominoes).**

$$\operatorname{NonBonding}\left(s, t\right) \Leftrightarrow (\forall p \in s,\; \forall q \in t,\; 2 \le \operatorname{dist}\left(p_{1}, q_{1}\right) + \operatorname{dist}\left(p_{2}, q_{2}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.NonBonding` (`✓ std3`).

*Citation.* Richard J. Mathar (2024). *Bivariate Generating Functions Enumerating Non-Bonding Dominoes on Rectangular Boards*. URL: <https://arxiv.org/abs/2404.18806v1>.

*Commentary.*

Two dominoes are non-bonding when every square of one has L1 distance at least 2 from every square of the other; this is the criterion of the paper, and it forces them to be disjoint.

**Definition 1.3 (Placements of two dominoes).**

$$\operatorname{D2}\left(r, c\right) = \left|\{P \mid \left|P\right| = 2 \land \left(\left(\forall s \in P,\; \operatorname{IsDomino}\left(r, c, s\right)\right) \land \left(\forall s \in P,\; \forall t \in P,\; s \ne t \Rightarrow (\operatorname{NonBonding}\left(s, t\right))\right)\right)\}\right|$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.D2` (`✓ std3`).

*Citation.* Richard J. Mathar (2024). *Bivariate Generating Functions Enumerating Non-Bonding Dominoes on Rectangular Boards*. URL: <https://arxiv.org/abs/2404.18806v1>.

*Commentary.*

D(r, c, 2) is the number of sets of two dominoes on the board that are non-bonding (Definition 1 of the paper with d = 2).

**Definition 1.4 (Mathar's Conjecture 1).**

$$claim \Leftrightarrow (\forall r \in \mathbb{N},\; \forall c \in \mathbb{N},\; 3 \le r \Rightarrow (3 \le c \Rightarrow (\operatorname{D2}\left(r, c\right) = 2 \cdot c^{2} \cdot r^{2} - 2 \cdot (c \cdot r^{2} + c^{2} \cdot r) + \frac{1}{2} \cdot (r^{2} + c^{2}) - 22 \cdot c \cdot r + \frac{59}{2} \cdot (c + r) - 30)))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.claim` (`✓ std3`).

*Citation.* Richard J. Mathar (2024). *Bivariate Generating Functions Enumerating Non-Bonding Dominoes on Rectangular Boards*. URL: <https://arxiv.org/abs/2404.18806v1>.

*Commentary.*

For all r and c at least 3, D(r, c, 2) is the stated biquadratic polynomial (equation (21) of the paper), read in the rationals.

**Theorem 1.5 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-2024-nonbonding-domino-pairs` (proved) by `D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-2024-nonbonding-domino-pairs","declaration_gid":"D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Richard J. Mathar (2024). *Bivariate Generating Functions Enumerating Non-Bonding Dominoes on Rectangular Boards*. URL: <https://arxiv.org/abs/2404.18806v1>.

*Commentary.*

Every domino is a horizontal one anchored at (i, j) with i < r, j < c - 1 or a vertical one anchored at (i, j) with i < r - 1, j < c, and these anchors determine it. Two dominoes bond (some squares at L1 distance at most 1) exactly when the offset of their anchors lies in a finite list: 11 offsets for two horizontal or two vertical dominoes, the equal one included, and 12 for a horizontal and a vertical one. The ordered anchor pairs with a given offset (a, b) are a product of two interval overlaps, for instance (r - |a|)(c - 1 - |b|) for two horizontal dominoes, and for r, c at least 3 each overlap is linear. Twice D(r, c, 2) is the number of ordered non-bonding pairs, N^2 minus the 46 offset classes with N = r(c - 1) + (r - 1)c the number of dominoes, which sums to the stated polynomial.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.D2`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.IsDomino`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.NonBonding`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.result`
