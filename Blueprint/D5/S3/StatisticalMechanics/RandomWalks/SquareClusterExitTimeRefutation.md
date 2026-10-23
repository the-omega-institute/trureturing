# Squares do not maximize the mean first exit time

## Abstract

A connected lattice disk with 121 vertices has larger mean first exit time than the 11 by 11 square.

**Definition 1.1 (The four lattice directions).**

$$\forall d \in \operatorname{Fin}\left(4\right),\; \operatorname{step}\left(d\right) = \operatorname{ite}\left(d = 0, (1, 0), \operatorname{ite}\left(d = 1, (-1, 0), \operatorname{ite}\left(d = 2, (0, 1), (0, -1)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.step` (`✓ std3`).

*Citation.* Silvia Rognone; Vincenzo Nicosia (2023). *Clusters in randomly-coloured spatial networks*. DOI: [10.1088/2632-072X/aeb36a](https://doi.org/10.1088/2632-072X/aeb36a). URL: <https://arxiv.org/abs/2308.07880v1>.

*Commentary.*

The directions indexed by Fin 4 are the two positive and two negative coordinate steps. Each direction has probability one quarter, as in the source's worked first-step system. The expression ite selects its second argument when its first argument holds and its third otherwise.

**Definition 1.2 (Positions along a direction word).**

$$\begin{aligned}\forall p \in \mathbb{Z}^{2},\; \forall w \in (\operatorname{Fin}\left(0\right) \to \operatorname{Fin}\left(4\right)),\; \forall j \in \mathbb{N},\; \operatorname{position}\left(p, w, j\right) = p\\\forall p \in \mathbb{Z}^{2},\; \forall n \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(4\right)),\; \operatorname{position}\left(p, w, 0\right) = p\\\forall p \in \mathbb{Z}^{2},\; \forall n \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(4\right)),\; \forall j \in \mathbb{N},\; \operatorname{position}\left(p, w, j + 1\right) = \operatorname{position}\left(p + \operatorname{step}\left(w\left(0\right)\right), \operatorname{tail}\left(w\right), j\right)\end{aligned}$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.position` (`✓ std3`).

*Citation.* Silvia Rognone; Vincenzo Nicosia (2023). *Clusters in randomly-coloured spatial networks*. DOI: [10.1088/2632-072X/aeb36a](https://doi.org/10.1088/2632-072X/aeb36a). URL: <https://arxiv.org/abs/2308.07880v1>.

*Commentary.*

A direction word of length n is a function from Fin n to Fin 4. The position starts at p, follows the word in order, and stays at its final vertex after n steps. The function tail removes the first letter of a nonempty word.

**Definition 1.3 (First exit at the last letter).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{Z}^{2}\right),\; \forall p \in \mathbb{Z}^{2},\; \forall n \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(4\right)),\; (\operatorname{exits}\left(S, p, w\right)) \Leftrightarrow ((\forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{position}\left(p, w, \operatorname{val}\left(j\right)\right) \in S) \land (\neg (\operatorname{position}\left(p, w, n\right) \in S)))$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.exits` (`✓ std3`).

*Citation.* Silvia Rognone; Vincenzo Nicosia (2023). *Clusters in randomly-coloured spatial networks*. DOI: [10.1088/2632-072X/aeb36a](https://doi.org/10.1088/2632-072X/aeb36a). URL: <https://arxiv.org/abs/2308.07880v1>.

*Commentary.*

A word exits at time n exactly when all positions with indices less than n belong to S and its final position does not. The map val regards a finite index as a natural number. For n = 0 this says that the starting point is outside S.

**Definition 1.4 (The exit distribution).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{Z}^{2}\right),\; \forall p \in \mathbb{Z}^{2},\; \forall n \in \mathbb{N},\; \operatorname{exitProb}\left(S, p, n\right) = \frac{(\operatorname{card}\left(\{w : (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(4\right)) \mid \operatorname{exits}\left(S, p, w\right)\}\right) : \mathbb{R})}{4^{n}}$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.exitProb` (`✓ std3`).

*Citation.* Silvia Rognone; Vincenzo Nicosia (2023). *Clusters in randomly-coloured spatial networks*. DOI: [10.1088/2632-072X/aeb36a](https://doi.org/10.1088/2632-072X/aeb36a). URL: <https://arxiv.org/abs/2308.07880v1>.

*Commentary.*

All direction words of length n have the same probability, one divided by four to the power n. Counting the words that first exit at their final position gives the first-exit distribution. The notation (a : ℝ) denotes the canonical cast from natural numbers to real numbers.

**Definition 1.5 (Expected first exit time).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{Z}^{2}\right),\; \forall p \in \mathbb{Z}^{2},\; \operatorname{expectedExit}\left(S, p\right) = \sum'_{n : \mathbb{N}} ((n : \mathbb{R}) \cdot \operatorname{exitProb}\left(S, p, n\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.expectedExit` (`✓ std3`).

*Citation.* Silvia Rognone; Vincenzo Nicosia (2023). *Clusters in randomly-coloured spatial networks*. DOI: [10.1088/2632-072X/aeb36a](https://doi.org/10.1088/2632-072X/aeb36a). URL: <https://arxiv.org/abs/2308.07880v1>.

*Commentary.*

The expectation is the sum of time n multiplied by its first-exit probability. The primed sum denotes the real tsum, with value zero if the series is not summable; the rational first-step solutions used below establish summability for the two clusters. This follows the source's prose definition: the first visit to any vertex outside the cluster.

**Definition 1.6 (The mean over starting vertices).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{Z}^{2}\right),\; \operatorname{meanExit}\left(S\right) = \frac{\sum_{p \in S} (\operatorname{expectedExit}\left(S, p\right))}{(\operatorname{card}\left(S\right) : \mathbb{R})}$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.meanExit` (`✓ std3`).

*Citation.* Silvia Rognone; Vincenzo Nicosia (2023). *Clusters in randomly-coloured spatial networks*. DOI: [10.1088/2632-072X/aeb36a](https://doi.org/10.1088/2632-072X/aeb36a). URL: <https://arxiv.org/abs/2308.07880v1>.

*Commentary.*

Average the expected first exit time uniformly over the vertices of S. Real division gives zero for the empty cluster. The source's prose and worked first-step systems use this first-exit interpretation. Its displayed equation eq:eq_tau_c instead averages individual node-to-node hitting times; that different average is not the quantity considered here.

**Definition 1.7 (Nearest-neighbour adjacency within a cluster).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{Z}^{2}\right),\; \forall p \in \mathbb{Z}^{2},\; \forall q \in \mathbb{Z}^{2},\; (\operatorname{adjacent}\left(S, p, q\right)) \Leftrightarrow ((p \in S) \land ((q \in S) \land (\exists d \in \operatorname{Fin}\left(4\right),\; q = p + \operatorname{step}\left(d\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.adjacent` (`✓ std3`).

*Citation.* Silvia Rognone; Vincenzo Nicosia (2023). *Clusters in randomly-coloured spatial networks*. DOI: [10.1088/2632-072X/aeb36a](https://doi.org/10.1088/2632-072X/aeb36a). URL: <https://arxiv.org/abs/2308.07880v1>.

*Commentary.*

Two vertices are adjacent when they both belong to S and one is obtained from the other by a unit coordinate step.

**Definition 1.8 (Connected lattice clusters).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{Z}^{2}\right),\; (\operatorname{connected}\left(S\right)) \Leftrightarrow (\forall p \in \mathbb{Z}^{2},\; (p \in S) \Rightarrow (\forall q \in \mathbb{Z}^{2},\; (q \in S) \Rightarrow (\operatorname{ReflTransGen}\left(\operatorname{adjacent}\left(S\right), p, q\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.connected` (`✓ std3`).

*Citation.* Silvia Rognone; Vincenzo Nicosia (2023). *Clusters in randomly-coloured spatial networks*. DOI: [10.1088/2632-072X/aeb36a](https://doi.org/10.1088/2632-072X/aeb36a). URL: <https://arxiv.org/abs/2308.07880v1>.

*Commentary.*

Every ordered pair of vertices of S is joined by a finite sequence of adjacent vertices in S. ReflTransGen is the reflexive transitive closure, so a path of length zero is allowed. The empty cluster satisfies this predicate vacuously.

**Definition 1.9 (The square of side m).**

$$\forall m \in \mathbb{N},\; \operatorname{square}\left(m\right) = \operatorname{image}\left((\lambda p : (\mathbb{N} \times \mathbb{N}), ((\operatorname{fst}\left(p\right) : \mathbb{Z}), (\operatorname{snd}\left(p\right) : \mathbb{Z}))), (\operatorname{range}\left(m\right) \times \operatorname{range}\left(m\right))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.square` (`✓ std3`).

*Citation.* Silvia Rognone; Vincenzo Nicosia (2023). *Clusters in randomly-coloured spatial networks*. DOI: [10.1088/2632-072X/aeb36a](https://doi.org/10.1088/2632-072X/aeb36a). URL: <https://arxiv.org/abs/2308.07880v1>.

*Commentary.*

Take the Cartesian product of two copies of range(m), the natural numbers from zero to m minus one, and include both coordinates in the integers. The functions fst and snd select the coordinates and (a : ℤ) denotes the canonical cast from natural numbers to integers. For positive m this is the square with m squared vertices; for m = 0 it is empty.

**Definition 1.10 (The square-maximality conjecture).**

$$(claim) \Leftrightarrow (\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow (\forall S \in \operatorname{Finset}\left(\mathbb{Z}^{2}\right),\; (\operatorname{card}\left(S\right) = m^{2}) \Rightarrow ((\operatorname{connected}\left(S\right)) \Rightarrow (\operatorname{meanExit}\left(S\right) \le \operatorname{meanExit}\left(\operatorname{square}\left(m\right)\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.claim` (`✓ std3`).

*Citation.* Silvia Rognone; Vincenzo Nicosia (2023). *Clusters in randomly-coloured spatial networks*. DOI: [10.1088/2632-072X/aeb36a](https://doi.org/10.1088/2632-072X/aeb36a). URL: <https://arxiv.org/abs/2308.07880v1>.

*Commentary.*

Rognone and Nicosia conjecture that the maximal exit time at each fixed number of nodes is obtained for squares. Here the number of nodes is m squared with m at least one, and every finite nearest-neighbour connected subset of the square lattice is compared with the square of side m. The exit time is the uniform mean of first-exit expectations.

**Theorem 1.11 (A disk with larger mean exit time).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/rognone-nicosia-2023-square-cluster-exit-time-refutation` (refuted) by `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rognone-nicosia-2023-square-cluster-exit-time-refutation","declaration_gid":"D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Silvia Rognone; Vincenzo Nicosia (2023). *Clusters in randomly-coloured spatial networks*. DOI: [10.1088/2632-072X/aeb36a](https://doi.org/10.1088/2632-072X/aeb36a). URL: <https://arxiv.org/abs/2308.07880v1>.

*Commentary.*

Let C be the lattice disk $\{(x, y) \in \mathbb{Z}^{2} \mid x^{2} + y^{2} \le 37\}$. It has 121 vertices and is nearest-neighbour connected: reducing the absolute value of a nonzero coordinate preserves membership and gives a path to the origin. Let Q be square(11), the 11 by 11 square.

On C and on Q, rational functions t, extended by zero outside the cluster, satisfy the certificate identity $t = 1 + P\left(t\right)$. Here, for a cluster S and a function f, $P\left(f\right)\left(p\right) = \operatorname{ite}\left(p \in S, \frac{\sum_{d : \operatorname{Fin}\left(4\right)} (f\left(p + \operatorname{step}\left(d\right)\right))}{4}, 0\right)$. The identity holds at every vertex of each cluster. Both functions lie between 1 and 43 there. Positivity of P then bounds its n-th iterate on t by (42/43) to the power n times t. The corresponding remainder terms in the partial sums of the exit distribution tend to zero, identifying t at each starting vertex with expectedExit for that cluster.

The exact means are $\operatorname{meanExit}\left(C\right) = \frac{198008236169}{8338377773}$ and $\operatorname{meanExit}\left(Q\right) = \frac{2811118983}{119333830}$. The first fraction is strictly greater than the second. Since both clusters have 121 vertices, C contradicts the conjectured inequality at m = 11.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.adjacent`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.connected`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.exitProb`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.exits`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.expectedExit`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.meanExit`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.position`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.square`
- Truth anchor: `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.step`
