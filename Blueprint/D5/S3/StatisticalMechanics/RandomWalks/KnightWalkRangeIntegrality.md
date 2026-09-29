# The normalized expected range of a knight's random walk is an integer

## Abstract

For a knight's random walk on the infinite chessboard, with each of the eight moves chosen uniformly at every step, the expected number E(n) of distinct squares visited in n steps (the start included) satisfies: E(n) 2^(3n-3) is an integer for every n at least one (OEIS A309221).

**Definition 1.1 (The eight knight moves).**

$$\operatorname{move} = [(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)]$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.move` (`✓ std3`).

*Citation.* N. J. A. Sloane (2019). *OEIS A309221, Expected number of distinct squares visited by a knight's random walk on an infinite chessboard after n steps, normalized to give an integer*. URL: <https://oeis.org/A309221>.

*Commentary.*

The eight moves of a knight on the square lattice, listed clockwise from (1, 2); the walk chooses one of them uniformly at each step.

**Definition 1.2 (The position after j steps).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(8\right),\; \forall j \in \mathbb{N},\; \operatorname{position}\left(w, j\right) = \sum_{i \in \operatorname{Fin}\left(n\right), i < j} \operatorname{move}\left(w\left(i\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.position` (`✓ std3`).

*Citation.* N. J. A. Sloane (2019). *OEIS A309221, Expected number of distinct squares visited by a knight's random walk on an infinite chessboard after n steps, normalized to give an integer*. URL: <https://oeis.org/A309221>.

*Commentary.*

The sum of the first j moves of a step sequence w of length n, starting from the origin.

**Definition 1.3 (The visited squares).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(8\right),\; \operatorname{visited}\left(w\right) = \{\operatorname{position}\left(w, j\right) \mid j \in \operatorname{range}\left(n + 1\right)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.visited` (`✓ std3`).

*Citation.* N. J. A. Sloane (2019). *OEIS A309221, Expected number of distinct squares visited by a knight's random walk on an infinite chessboard after n steps, normalized to give an integer*. URL: <https://oeis.org/A309221>.

*Commentary.*

The positions after 0, 1, ..., n steps; OEIS A326954: "The starting square is always considered part of the walk."

**Definition 1.4 (The expected number of distinct visited squares).**

$$\forall n \in \mathbb{N},\; \operatorname{expectedRange}\left(n\right) = \frac{\sum_{w \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(8\right)} \operatorname{card}\left(\operatorname{visited}\left(w\right)\right)}{8^{n}}$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.expectedRange` (`✓ std3`).

*Citation.* N. J. A. Sloane (2019). *OEIS A309221, Expected number of distinct squares visited by a knight's random walk on an infinite chessboard after n steps, normalized to give an integer*. URL: <https://oeis.org/A309221>.

*Commentary.*

OEIS A326954 and A326955: "the expected number of distinct squares visited by a knight's random walk on an infinite chessboard after n steps"; all 8^n step sequences are equally likely.

**Definition 1.5 (The conjecture of OEIS A309221).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\exists m \in \mathbb{Z},\; \operatorname{expectedRange}\left(n\right) \cdot 2^{3 \cdot n - 3} = m))$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.claim` (`✓ std3`).

*Citation.* N. J. A. Sloane (2019). *OEIS A309221, Expected number of distinct squares visited by a knight's random walk on an infinite chessboard after n steps, normalized to give an integer*. URL: <https://oeis.org/A309221>.

*Commentary.*

OEIS A309221, COMMENTS: "a(0)=1; for n>0, a(n) = (A326954(n)/A326955(n))*2^(3*n-3). (It is only a conjecture that this is always an integer)." The claim is the integrality of a(n) for every n at least one.

**Theorem 1.6 (Integrality by the symmetries of the eight moves).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/sloane-2019-a309221-knight-walk-range-integrality` (proved) by `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sloane-2019-a309221-knight-walk-range-integrality","declaration_gid":"D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane (2019). *OEIS A309221, Expected number of distinct squares visited by a knight's random walk on an infinite chessboard after n steps, normalized to give an integer*. URL: <https://oeis.org/A309221>.

*Commentary.*

The eight symmetries of the square lattice permute the eight moves simply transitively: for each move m there is a signed coordinate permutation g of the lattice and a permutation s of the moves with g(move i) = move(s(i)) and s(0) = m. Applying s to every step maps the positions of a walk by g, hence its visited squares by g, and g is injective, so the number of visited squares is unchanged. For n = k + 1, split the step sequences by their first step; applying s maps the walks starting with move 0 bijectively onto those starting with move m, so each of the eight classes has the same total T. The total over all walks is 8T, and E(k + 1) 2^(3k) = 8T / 8^(k+1) 8^k = T is an integer.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.expectedRange`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.move`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.position`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.result`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality.visited`
