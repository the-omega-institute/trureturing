# Walks of near-maximal algebraic area on the square lattice

## Abstract

For k < n, the 2n-step walks on the square lattice with algebraic area n^2 - k number twice the coefficient of x^k in phi(x)/f(-x), and the (2n+1)-step walks with area n^2 + n - k number four times the coefficient of x^k in psi(x^2)/f(-x).

**Definition 1.1 (Steps).**

$$\operatorname{Step} = \left\{right, left, up, down\right\}$$

*Formalization.* `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.Step` (`✓ std3`).

*Citation.* Andrei Zabolotskii (2025). *OEIS A385672, Irregular triangle read by rows: T(n, k) is the number of n-step walks on the square lattice having algebraic area k*. URL: <https://oeis.org/A385672>.

*Commentary.*

A walk on the square lattice moves right, left, up or down by one unit at each step.

**Definition 1.2 (Area from a starting height).**

$$\operatorname{areaFrom}\left(y, \operatorname{nil}\right) = 0,\quad\operatorname{areaFrom}\left(y, \operatorname{cons}\left(right, w\right)\right) = y + \operatorname{areaFrom}\left(y, w\right),\quad\operatorname{areaFrom}\left(y, \operatorname{cons}\left(left, w\right)\right) = -y + \operatorname{areaFrom}\left(y, w\right),\quad\operatorname{areaFrom}\left(y, \operatorname{cons}\left(up, w\right)\right) = \operatorname{areaFrom}\left(y + 1, w\right),\quad\operatorname{areaFrom}\left(y, \operatorname{cons}\left(down, w\right)\right) = \operatorname{areaFrom}\left(y - 1, w\right)$$

*Formalization.* `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.areaFrom` (`✓ std3`).

*Citation.* Andrei Zabolotskii (2025). *OEIS A385672, Irregular triangle read by rows: T(n, k) is the number of n-step walks on the square lattice having algebraic area k*. URL: <https://oeis.org/A385672>.

*Commentary.*

The integral of y dx along a walk that starts at height y: a right step adds the current height, a left step subtracts it, and an up or down step changes the height by one.

**Definition 1.3 (Algebraic area).**

$$\operatorname{area}\left(w\right) = \operatorname{areaFrom}\left(0, w\right)$$

*Formalization.* `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.area` (`✓ std3`).

*Citation.* Andrei Zabolotskii (2025). *OEIS A385672, Irregular triangle read by rows: T(n, k) is the number of n-step walks on the square lattice having algebraic area k*. URL: <https://oeis.org/A385672>.

*Commentary.*

The algebraic area of a walk from the origin: the sum of the heights at its right steps minus the sum of the heights at its left steps.

**Definition 1.4 (The triangle A385672).**

$$\operatorname{walkCount}\left(n, k\right) = \left|\{w \in \left(\operatorname{Fin}\left(n\right) \to \operatorname{Step}\right) \mid \operatorname{area}\left(\operatorname{ofFn}\left(w\right)\right) = k\}\right|$$

*Formalization.* `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.walkCount` (`✓ std3`).

*Citation.* Andrei Zabolotskii (2025). *OEIS A385672, Irregular triangle read by rows: T(n, k) is the number of n-step walks on the square lattice having algebraic area k*. URL: <https://oeis.org/A385672>.

*Commentary.*

The number of n-step walks, read as maps from the n positions to the four steps and turned into the list of their values in order (ofFn), whose algebraic area is k.

**Definition 1.5 (Partition numbers).**

$$\operatorname{partitionCount}\left(m\right) = \left|\operatorname{Partition}\left(m\right)\right|$$

*Formalization.* `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.partitionCount` (`✓ std3`).

*Citation.* Andrei Zabolotskii (2025). *OEIS A385672, Irregular triangle read by rows: T(n, k) is the number of n-step walks on the square lattice having algebraic area k*. URL: <https://oeis.org/A385672>.

*Commentary.*

A000041: the number of partitions of m, the coefficients of the reciprocal of f(-x) = the product of (1 - x^i) over i > 0.

**Definition 1.6 (The coefficients A029552).**

$$\operatorname{a029552}\left(k\right) = \operatorname{partitionCount}\left(k\right) + 2 \cdot \sum_{1 \le j, j \le k, j^{2} \le k} \operatorname{partitionCount}\left(k - j^{2}\right)$$

*Formalization.* `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.a029552` (`✓ std3`).

*Citation.* Andrei Zabolotskii (2025). *OEIS A385672, Irregular triangle read by rows: T(n, k) is the number of n-step walks on the square lattice having algebraic area k*. URL: <https://oeis.org/A385672>.

*Commentary.*

The coefficient of x^k in (1 + 2 times the sum of x^(j^2) over j > 0) divided by the product of (1 - x^i) over i > 0.

**Definition 1.7 (The coefficients A098613).**

$$\operatorname{a098613}\left(k\right) = \sum_{1 \le j, j \le k + 1, j^{2} - j \le k} \operatorname{partitionCount}\left(k - (j^{2} - j)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.a098613` (`✓ std3`).

*Citation.* Andrei Zabolotskii (2025). *OEIS A385672, Irregular triangle read by rows: T(n, k) is the number of n-step walks on the square lattice having algebraic area k*. URL: <https://oeis.org/A385672>.

*Commentary.*

The coefficient of x^k in the sum of x^(j^2 - j) over j > 0 divided by the product of (1 - x^i) over i > 0.

**Definition 1.8 (The conjecture of A385672).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (k < n) \Rightarrow (\operatorname{walkCount}\left(2 \cdot n, n^{2} - k\right) = 2 \cdot \operatorname{a029552}\left(k\right) \land \operatorname{walkCount}\left(2 \cdot n + 1, n^{2} + n - k\right) = 4 \cdot \operatorname{a098613}\left(k\right)))$$

*Formalization.* `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.claim` (`✓ std3`).

*Citation.* Andrei Zabolotskii (2025). *OEIS A385672, Irregular triangle read by rows: T(n, k) is the number of n-step walks on the square lattice having algebraic area k*. URL: <https://oeis.org/A385672>.

*Commentary.*

For every k < n the walks of length 2n with area n^2 - k number 2 A029552(k), and the walks of length 2n + 1 with area n^2 + n - k number 4 A098613(k).

**Theorem 1.9 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.result` (`✓ std3`). ∎

*Resolves.* `Problems/zabolotskii-2025-a385672-near-maximal-area-walks` (proved) by `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zabolotskii-2025-a385672-near-maximal-area-walks","declaration_gid":"D5/S3/Combinatorics/LatticeWalkNearMaximalArea.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andrei Zabolotskii (2025). *OEIS A385672, Irregular triangle read by rows: T(n, k) is the number of n-step walks on the square lattice having algebraic area k*. URL: <https://oeis.org/A385672>.

*Commentary.*

Let r, l, u, d count the right, left, up and down steps. At a right step the height is at most u and at a left step at least -d, so the area is at most r u + l d. If the walk uses both a right or up step and a left or down step, then 4(r u + l d) is at most (r + u)^2 + (l + d)^2, which is at most 1 + (L - 1)^2 for the length L, so the area is at most n^2 - n when L = 2n and at most n^2 when L = 2n + 1. Every walk in the stated range therefore uses only right and up steps or only left and down steps, and exchanging right with left and up with down maps the second kind onto the first without changing the area. A word of u up steps and r right steps has area u r minus the number of pairs of a right step followed later by an up step. Splitting at the first step, the words with u up steps and m such pairs satisfy the recurrence N(u, r, m) = N(u - 1, r, m) + N(u, r - 1, m - u), which is also the recurrence of the partitions of m into parts at most u, split by whether the part u occurs; so for r at least m they are the partitions of m into parts at most u, and for u at least m all partitions of m. With u = n + j and r = n - j the number of pairs is k - j^2, at most the smaller of u and r because k < n, and summing over j gives p(k) + 2 times the sum of p(k - j^2) over j > 0. With u = n + 1 + j and r = n - j it is k - j(j + 1), the substitution j to -1 - j pairs the terms, and the sum is twice the sum of p(k - j(j + 1)) over j at least 0.

## References

- Truth anchor: `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.Step`
- Truth anchor: `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.a029552`
- Truth anchor: `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.a098613`
- Truth anchor: `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.area`
- Truth anchor: `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.areaFrom`
- Truth anchor: `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.claim`
- Truth anchor: `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.partitionCount`
- Truth anchor: `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.result`
- Truth anchor: `D5/S3/Combinatorics/LatticeWalkNearMaximalArea.walkCount`
- Dependency: [D5/S1/Digit/Carry/ListInversions](../../S1/Digit/Carry/ListInversions.md)
