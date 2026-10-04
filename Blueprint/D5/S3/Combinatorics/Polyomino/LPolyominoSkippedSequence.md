# L Polyominoes and Skipped Numbers

## Abstract

The minimum size of a polyomino containing N translated L n-ominoes is the Nth term of S(n, 1, 2).

Section 2.1, p. 4 encodes edge-glued unit squares by their integer lower-left corners. The coordinate carrier is Point = Z × Z from OrderedGridMemory.

$$
Point = \mathbb{Z} \times \mathbb{Z}
$$

**Definition 1.1 (The L n-omino).**

$$\forall (n : \mathbb{N}), \operatorname{L}\left(n\right) = \operatorname{image}\left((i : \mathbb{N}) \mapsto ((i : \mathbb{Z}), 0), \operatorname{range}\left(n - 1\right)\right) \cup \left\{(0, 1)\right\}$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.L` (`✓ std3`).

*Citation.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Section 4.4, p. 15: “We define an L n-omino, for n ≥ 3, to be a left-aligned polyomino with two rows that has 1 cell in the top row and n − 1 cells in the bottom row.” The bottom row starts at (0,0); the top cell is (0,1). The image uses the natural-number range 0 ≤ i < n − 1 and casts i to an integer. Natural subtraction is truncated at zero.

**Definition 1.2 (Translation anchors).**

$$\forall (P : \operatorname{Finset}\left(Point\right)), \forall (p : \operatorname{Finset}\left(Point\right)), \operatorname{instances}\left(P, p\right) = \operatorname{filter}\left(\operatorname{biUnion}\left(P, (u : Point) \mapsto \operatorname{image}\left((c : Point) \mapsto u - c, p\right)\right), (v : Point) \mapsto \forall (c : Point), (c \in p) \Rightarrow (c + v \in P)\right)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.instances` (`✓ std3`).

*Citation.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Section 2.1, p. 4: “In this paper, we deal with fixed polyominoes, meaning we consider two polyominoes to be the same shape if they differ by translation only; we call these two instances of that shape.” The displayed expression first lists differences u − c, then retains precisely the anchors v for which every c + v belongs to P. For a nonempty shape this captures every translation anchor. Rotations and reflections are not counted. The expression gives the empty set for an empty shape; every L n-omino in the theorem is nonempty.

Section 1, printed p. 1: “A polyomino is a connected shape made from unit squares, called cells, glued together edge-to-edge.” The relation squareGrid.Adj from SquareGridCoordinates gives the four horizontal and vertical unit edges on Point. All coordinate arithmetic is in the integers.

$$
\forall (c : Point), \forall (b : Point), (\operatorname{squareGrid.Adj}\left(c, b\right)) \Leftrightarrow (((\operatorname{fst}\left(c\right) + 1 = \operatorname{fst}\left(b\right)) \land (\operatorname{snd}\left(c\right) = \operatorname{snd}\left(b\right))) \lor (((\operatorname{fst}\left(b\right) + 1 = \operatorname{fst}\left(c\right)) \land (\operatorname{snd}\left(c\right) = \operatorname{snd}\left(b\right))) \lor (((\operatorname{snd}\left(c\right) + 1 = \operatorname{snd}\left(b\right)) \land (\operatorname{fst}\left(c\right) = \operatorname{fst}\left(b\right))) \lor ((\operatorname{snd}\left(b\right) + 1 = \operatorname{snd}\left(c\right)) \land (\operatorname{fst}\left(c\right) = \operatorname{fst}\left(b\right))))))
$$

**Definition 1.3 (Nonempty connected cell sets).**

$$\forall (P : \operatorname{Finset}\left(Point\right)), (\operatorname{IsPolyomino}\left(P\right)) \Leftrightarrow ((\operatorname{Nonempty}\left(P\right)) \land (\forall (c : Point), (c \in P) \Rightarrow (\forall (b : Point), (b \in P) \Rightarrow (\operatorname{ReflTransGen}\left((u : Point) \mapsto (v : Point) \mapsto (u \in P) \land ((v \in P) \land (\operatorname{squareGrid.Adj}\left(u, v\right))), c, b\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.IsPolyomino` (`✓ std3`).

*Citation.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Section 1, printed p. 1: “A polyomino is a connected shape made from unit squares, called cells, glued together edge-to-edge.” ReflTransGen means a finite path, including the length-zero path. Every vertex of each edge is required to belong to P.

**Definition 1.4 (The instance minimum).**

$$\forall (p : \operatorname{Finset}\left(Point\right)), \forall (N : \mathbb{N}), \operatorname{a}\left(p, N\right) = \operatorname{sInf}\left(\{S : \mathbb{N} \mid \exists (P : \operatorname{Finset}\left(Point\right)), (\operatorname{IsPolyomino}\left(P\right)) \land ((N \le \operatorname{card}\left(\operatorname{instances}\left(P, p\right)\right)) \land (\operatorname{card}\left(P\right) = S))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.a` (`✓ std3`).

*Citation.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Section 1, p. 3: “For N any positive integer, if P is a polyomino of minimum size among those polyominoes containing at least N instances (translated copies) of some polyomino p, we say that P is (p, N)-dense” and “We let a_{p,N} denote the size of a (p, N)-dense polyomino, and we call (a_{p,N})_{N=1}^∞ the instance sequence for p.” The minimum is the natural-number infimum of the displayed set. The proof constructs an eligible polyomino for each n ≥ 3 and N ≥ 1, so the empty-set convention for sInf is never used in the conclusion.

**Definition 1.5 (The sequence's own recursion).**

$$\forall (x : \mathbb{N}), \forall (k : \mathbb{N}), \operatorname{skip}\left(x, k\right) = \operatorname{ite}\left(k \le 1, x, \operatorname{skip}\left(x, k - 1\right) + \operatorname{ite}\left(\exists (i : \mathbb{N}), (1 \le i) \land ((i < k) \land (\operatorname{skip}\left(x, i\right) = k)), 1, 2\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.skip` (`✓ std3`).

*Citation.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Section 6.3, p. 28: “In a recent preprint [Clo25], Benoit Cloitre defines an S(x, y, z) sequence to be an increasing sequence of integers a_k starting with a_1 = x, such that for k > 1, a_k − a_{k−1} = y if k occurs in the sequence before position k, and otherwise a_k − a_{k−1} = z.” Here y = 1 and z = 2. The function ite selects its second argument when its first argument holds and its third otherwise. Index zero is an auxiliary value equal to x; the source sequence starts at index one. Natural subtraction is truncated at zero.

**Definition 1.6 (The general suspicion).**

$$(claim) \Leftrightarrow (\forall (n : \mathbb{N}), \forall (N : \mathbb{N}), (3 \le n) \Rightarrow ((1 \le N) \Rightarrow (\operatorname{a}\left(\operatorname{L}\left(n\right), N\right) = \operatorname{skip}\left(n, N\right))))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.claim` (`✓ std3`).

*Citation.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Section 6.3, p. 28: “We believe S(5, 1, 2) is the same as the instance sequence for [L pentomino], and we suspect that the instance sequence for the L n-omino is S(n, 1, 2) in general.” The bracketed label denotes the source's inline L pentomino diagram. The n ≥ 3 domain comes from Section 4.4 and the N ≥ 1 domain from Section 1. Both independent sides use exactly the definitions above.

**Theorem 1.7 (Identification for every n and N).**

$$\forall (n : \mathbb{N}), \forall (N : \mathbb{N}), (3 \le n) \Rightarrow ((1 \le N) \Rightarrow (\operatorname{a}\left(\operatorname{L}\left(n\right), N\right) = \operatorname{skip}\left(n, N\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.result` (`✓ std3`). ∎

*Resolves.* `Problems/condon-dugan-goldman-williams-2026-l-polyomino-skipped-sequence` (proved) by `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"condon-dugan-goldman-williams-2026-l-polyomino-skipped-sequence","declaration_gid":"D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Put d = n − 2 and weight a cell (x,y) by x + d y. The top and right-most cells of every instance share a level. Injecting anchors into earlier levels and excluding the maximum-x cell at the current level bounds the number I of instances by the sum of floor(i/d) for 0 ≤ i < |P| − I, for every finite cell set P. No connectivity assumption is needed for this lower bound. A trimmed down-set attains the bound and is edge-connected. If K is the least integer with N ≤ sum of floor(i/d) for 0 ≤ i ≤ K, the attained minimum is N + 1 + K. The prefix-sum identity H(K+d) = H(K) + K identifies the jump positions of this minimum with the values absent from its earlier range. Strong induction then identifies it with the independently defined skipped-number recursion. In particular, the believed L pentomino case n = 5 follows.

## References

- Truth anchor: `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.IsPolyomino`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.L`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.a`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.claim`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.instances`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.result`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.skip`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates](../../StatisticalMechanics/HardCore/SquareGridCoordinates.md)
