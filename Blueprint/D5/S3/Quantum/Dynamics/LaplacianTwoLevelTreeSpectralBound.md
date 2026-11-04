# Sharp global spectral bound for root-to-leaf Laplacian transfer on two-level trees

## Abstract

On the homogeneous two-level rooted tree T(k, l) of order n = 1 + k(l + 1) with k >= 2 hubs and l >= 1 leaves per hub, the continuous-time Laplacian propagator from the root to any leaf decomposes across the three eigenvalues 0, a, b of the three-dimensional cell-constant invariant subspace. Its distinct-eigenvalue spectral entry bound equals 2 / (a d), where d = b - a = sqrt((k - l)^2 + 4 l). Scaled by n^(3/2), the squared spectral bound is dominated through an algebraic chord identity and rational square decompositions by the universal constant C_* = 2 + 6 sqrt(5) / 5, with equality on B_{k, l}^2 if and only if (k, l) = (2, 1).

**Definition 1.1 (Order of the two-level rooted tree).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; \operatorname{treeOrder}\left(k, l\right) = 1 + k \cdot \left(l + 1\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.treeOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

For k hubs and l leaves attached to each hub, the total vertex count of T(k, l) is n = 1 + k(l + 1), counting the single root together with k hub-and-branch blocks of size l + 1.

**Definition 1.2 (The homogeneous two-level tree on Fin n).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; \forall u \in \operatorname{Fin}\left(\operatorname{treeOrder}\left(k, l\right)\right),\; \forall v \in \operatorname{Fin}\left(\operatorname{treeOrder}\left(k, l\right)\right),\; (\operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{twoLevelTree}\left(k, l\right), u, v\right)) \Leftrightarrow (\operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{rawTree}\left(k, l\right), \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{vertEquiv}\left(k, l\right)\right)\left(u\right), \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{vertEquiv}\left(k, l\right)\right)\left(v\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.twoLevelTree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The simple graph T(k, l) on Fin(treeOrder k l) is transported along an explicit equivalence from Option(Fin k x Option(Fin l)), where none represents the root, some(i, none) represents the i-th hub adjacent to the root, and some(i, some j) represents the j-th leaf adjacent to the i-th hub. No edges exist within any level or between distinct branches, and twoLevelTreeDecidableRel equips the adjacency relation with decidability.

**Definition 1.3 (The root vertex of T(k, l)).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; \operatorname{rootVertex}\left(k, l\right) = \operatorname{vertEquiv}\left(k, l\right)\left(\operatorname{none}\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.rootVertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The distinguished root r in Fin(treeOrder k l) corresponds under the vertex equivalence to none and has degree k.

**Definition 1.4 (The i-th hub vertex of T(k, l)).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{hubVertex}\left(k, l, i\right) = \operatorname{vertEquiv}\left(k, l\right)\left(\operatorname{some}\left((i, \operatorname{none})\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.hubVertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

For i in Fin k, the hub vertex h_i in Fin(treeOrder k l) corresponds to some(i, none), is adjacent to the root and to its l leaves, and has degree l + 1.

**Definition 1.5 (The (i, j)-th leaf vertex of T(k, l)).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(l\right),\; \operatorname{leafVertex}\left(k, l, i, j\right) = \operatorname{vertEquiv}\left(k, l\right)\left(\operatorname{some}\left((i, \operatorname{some}\left(j\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.leafVertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

For i in Fin k and j in Fin l, the leaf vertex x_{i, j} in Fin(treeOrder k l) corresponds to some(i, some j) and has degree 1 with unique neighbor h_i.

**Definition 1.6 (Continuous-time Laplacian root-to-leaf transfer probability).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(l\right),\; \forall t \in \mathbb{R},\; \operatorname{leafTransferProb}\left(k, l, i, j, t\right) = (\left\lVert \operatorname{lapPropagator}\left(\operatorname{twoLevelTree}\left(k, l\right), t, \operatorname{leafVertex}\left(k, l, i, j\right), \operatorname{rootVertex}\left(k, l\right)\right) \right\rVert)^{2}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.leafTransferProb` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

At real time t, leafTransferProb k l i j t is the squared complex norm |U(t)_{x_{i, j}, r}|^2 of the Laplacian propagator entry exp(i t L)_{x_{i, j}, r} from the root r to the leaf x_{i, j}, defined directly via LaplacianPeakTransferTrees.lapPropagator on twoLevelTree k l at time t.

**Definition 1.7 (Root-to-leaf entry of the Laplacian spectral bounding matrix).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(l\right),\; \operatorname{leafBoundingEntry}\left(k, l, i, j\right) = \operatorname{boundingEntry}\left(\operatorname{twoLevelTree}\left(k, l\right), \operatorname{leafVertex}\left(k, l, i, j\right), \operatorname{rootVertex}\left(k, l\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.leafBoundingEntry` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

Following Section 3 of Coutinho, Guo, and Schmeits (2025), leafBoundingEntry k l i j evaluates LaplacianPeakTransferTrees.boundingEntry on twoLevelTree k l at the pair (x_{i, j}, r), summing the absolute values of the distinct-eigenvalue orthogonal spectral idempotent entries |(E_theta)_{x_{i, j}, r}|.

**Definition 1.8 (Trace parameter of the positive root-supported eigenvalues).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; \operatorname{specS}\left(k, l\right) = (k : \mathbb{R}) + (l : \mathbb{R}) + 2$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.specS` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

On the three-dimensional subspace of vectors constant on the root, on hubs, and on leaves, the nonzero Laplacian eigenvalues satisfy theta^2 - S theta + n = 0 with trace parameter S = k + l + 2 over the reals.

**Definition 1.9 (Spectral discriminant parameter).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; \operatorname{specD}\left(k, l\right) = \sqrt{((k : \mathbb{R}) - (l : \mathbb{R}))^{2} + 4 \cdot (l : \mathbb{R})}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.specD` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The gap between the two positive root-supported eigenvalues is d = sqrt((k - l)^2 + 4 l), computed with real subtraction (k : R) - (l : R) so that S^2 - 4 n = ((k : R) - (l : R))^2 + 4 l = d^2 holds for all k and l.

**Definition 1.10 (Lower positive root-supported Laplacian eigenvalue).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; \operatorname{specA}\left(k, l\right) = \frac{\operatorname{specS}\left(k, l\right) - \operatorname{specD}\left(k, l\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.specA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The smaller positive root of theta^2 - S theta + n = 0 is a = (S - d) / 2. For k >= 2 and l >= 1 one has 1 < a < b and a b = n.

**Definition 1.11 (Upper positive root-supported Laplacian eigenvalue).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; \operatorname{specB}\left(k, l\right) = \frac{\operatorname{specS}\left(k, l\right) + \operatorname{specD}\left(k, l\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.specB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The larger positive root of theta^2 - S theta + n = 0 is b = (S + d) / 2 = a + d.

**Definition 1.12 (Optimal global scaled root-to-leaf transfer constant).**

$$\operatorname{optimalTransferConst} = 2 + \frac{6 \cdot \sqrt{5}}{5}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.optimalTransferConst` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The constant C_* = 2 + 6 sqrt(5) / 5 is the value of the upper-endpoint spectral envelope H(d) at the minimal feasible discriminant d = sqrt(5), attained by the five-vertex tree T(2, 1).

**Definition 1.13 (Upper feasible endpoint for the lower eigenvalue at fixed discriminant).**

$$\forall d \in \mathbb{R},\; \operatorname{upperFeasibleA}\left(d\right) = \frac{d^{2} - 2 \cdot d + 5}{4}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.upperFeasibleA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

At fixed discriminant d, eliminating k and l via 4(A(d) - a) = (k - l - 1)^2 >= 0 confines the lower eigenvalue a to the interval [1, A(d)] where A(d) = (d^2 - 2 d + 5) / 4.

**Definition 1.14 (Lower-endpoint spectral envelope).**

$$\forall d \in \mathbb{R},\; \operatorname{envelopeG}\left(d\right) = \frac{4 \cdot (d + 1)^{\frac{3}{2}}}{d^{2}}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.envelopeG` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

Evaluating the scaled squared spectral bound 4(a + d)^(3/2) / (sqrt(a) d^2) at the left endpoint a = 1 produces G(d) = 4(d + 1)^(3/2) / d^2.

**Definition 1.15 (Upper-endpoint spectral envelope).**

$$\forall d \in \mathbb{R},\; \operatorname{envelopeH}\left(d\right) = \frac{(d^{2} + 2 \cdot d + 5)^{\frac{3}{2}}}{d^{2} \cdot \sqrt{d^{2} - 2 \cdot d + 5}}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.envelopeH` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

Evaluating 4(a + d)^(3/2) / (sqrt(a) d^2) at the right endpoint a = A(d) = (d^2 - 2 d + 5) / 4, where a + d = (d^2 + 2 d + 5) / 4, produces H(d) = (d^2 + 2 d + 5)^(3/2) / (d^2 sqrt(d^2 - 2 d + 5)).

**Theorem 1.16 (Exact root-to-leaf spectral decomposition, symmetry invariance, and closed bound).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; (2 \le k) \Rightarrow ((1 \le l) \Rightarrow (\forall i \in \operatorname{Fin}\left(k\right),\; \forall i2 \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(l\right),\; \forall j2 \in \operatorname{Fin}\left(l\right),\; \forall t \in \mathbb{R},\; (\operatorname{SimpleGraph}.\operatorname{IsTree}\left(\operatorname{twoLevelTree}\left(k, l\right)\right)) \land ((\exists phi \in \operatorname{SimpleGraph}.\operatorname{Iso}\left(\operatorname{twoLevelTree}\left(k, l\right), \operatorname{twoLevelTree}\left(k, l\right)\right),\; (phi\left(\operatorname{rootVertex}\left(k, l\right)\right) = \operatorname{rootVertex}\left(k, l\right)) \land (phi\left(\operatorname{leafVertex}\left(k, l, i, j\right)\right) = \operatorname{leafVertex}\left(k, l, i2, j2\right))) \land ((\operatorname{leafTransferProb}\left(k, l, i, j, t\right) = \operatorname{leafTransferProb}\left(k, l, i2, j2, t\right)) \land ((\operatorname{leafBoundingEntry}\left(k, l, i, j\right) = \operatorname{leafBoundingEntry}\left(k, l, i2, j2\right)) \land ((\operatorname{lapPropagator}\left(\operatorname{twoLevelTree}\left(k, l\right), t, \operatorname{leafVertex}\left(k, l, i, j\right), \operatorname{rootVertex}\left(k, l\right)\right) = \frac{(1 : \mathbb{C})}{(\operatorname{treeOrder}\left(k, l\right) : \mathbb{C})} - \frac{\operatorname{Complex}.\operatorname{exp}\left(\operatorname{Complex}.\operatorname{I} \cdot (\operatorname{specA}\left(k, l\right) : \mathbb{C}) \cdot (t : \mathbb{C})\right)}{(\operatorname{specA}\left(k, l\right) : \mathbb{C}) \cdot (\operatorname{specD}\left(k, l\right) : \mathbb{C})} + \frac{\operatorname{Complex}.\operatorname{exp}\left(\operatorname{Complex}.\operatorname{I} \cdot (\operatorname{specB}\left(k, l\right) : \mathbb{C}) \cdot (t : \mathbb{C})\right)}{(\operatorname{specB}\left(k, l\right) : \mathbb{C}) \cdot (\operatorname{specD}\left(k, l\right) : \mathbb{C})}) \land ((\operatorname{leafBoundingEntry}\left(k, l, i, j\right) = \frac{2}{\operatorname{specA}\left(k, l\right) \cdot \operatorname{specD}\left(k, l\right)}) \land (\operatorname{leafTransferProb}\left(k, l, i, j, t\right) \le (\operatorname{leafBoundingEntry}\left(k, l, i, j\right))^{2}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.twoLevelTree_leaf_dynamics_and_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

For k >= 2 and l >= 1, the graph T(k, l) is a tree (connected and acyclic) whose root has degree k, each hub has degree l + 1, and each leaf has degree 1. Swapping branches and permuting leaves within a branch yield graph automorphisms fixing the root and mapping any leaf x_{i, j} to any other leaf x_{i2, j2}, so both the spectral bounding entry and the transfer probability P_{k, l}(t) are independent of the chosen leaf (i, j). Expanding the root indicator e_r as (1 / n) v_0 + c_a v_a + c_b v_b in explicit cell-constant Laplacian eigenvectors for eigenvalues 0, a, b shows that every other Laplacian eigenspace is orthogonal to e_r, yields the three-frequency formula U(t)_{x_{i, j}, r} = 1 / n - exp(i a t) / (a d) + exp(i b t) / (b d), evaluates the spectral bounding entry to 1 / n + 1 / (a d) + 1 / (b d) = 2 / (a d) because a b = n and b - a = d, and establishes the universal time upper bound P_{k, l}(t) <= B_{k, l}^2.

**Theorem 1.17 (Algebraic envelope decompositions, strict antitonicity, and endpoint domination).**

$$\forall d1 \in \mathbb{R},\; \forall d2 \in \mathbb{R},\; (0 < d1) \Rightarrow ((d1 < d2) \Rightarrow (((\operatorname{envelopeG}\left(d1\right))^{2} = 16 \cdot \left(\frac{1}{d1} + \frac{3}{d1^{2}} + \frac{3}{d1^{3}} + \frac{1}{d1^{4}}\right)) \land (((\operatorname{envelopeH}\left(d1\right))^{2} = 1 + \frac{8}{d1} + \frac{38}{d1^{2}} + \frac{40}{d1^{3}} + \frac{25}{d1^{4}} + \frac{64}{d1 \cdot \left(d1^{2} - 2 \cdot d1 + 5\right)}) \land ((1 < \operatorname{envelopeH}\left(d1\right)) \land ((\operatorname{envelopeG}\left(d2\right) < \operatorname{envelopeG}\left(d1\right)) \land ((\operatorname{envelopeH}\left(d2\right) < \operatorname{envelopeH}\left(d1\right)) \land (\forall a \in \mathbb{R},\; (1 \le a) \Rightarrow ((a \le \operatorname{upperFeasibleA}\left(d1\right)) \Rightarrow (\frac{4 \cdot (a + d1)^{\frac{3}{2}}}{\sqrt{a} \cdot d1^{2}} \le \operatorname{max}\left(\operatorname{envelopeG}\left(d1\right), \operatorname{envelopeH}\left(d1\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.spectral_envelope_and_antitonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

For 0 < d_1 < d_2, squaring G(d_1) yields 16(1 / d_1 + 3 / d_1^2 + 3 / d_1^3 + 1 / d_1^4), and the polynomial identity (d^2 + 2 d + 5)^3 = (d^2 - 2 d + 5)(d^4 + 8 d^3 + 38 d^2 + 40 d + 25) + 64 d^3 yields H(d_1)^2 = 1 + 8 / d_1 + 38 / d_1^2 + 40 / d_1^3 + 25 / d_1^4 + 64 / (d_1(d_1^2 - 2 d_1 + 5)). Because d(d^2 - 2 d + 5) = d((d - 1)^2 + 4) is positive and strictly increasing on (0, infinity) via the factorization d_2(d_2^2 - 2 d_2 + 5) - d_1(d_1^2 - 2 d_1 + 5) = (d_2 - d_1)((d_1 - 1)^2 + (d_2 - 1)^2 + d_1 d_2 + 3) > 0, every term of H(d)^2 exceeding 1 is positive and strictly decreasing, giving 1 < H(d_1), G(d_2) < G(d_1), and H(d_2) < H(d_1). Furthermore, on [1, A(d_1)], the function g(a) = (a + d_1)^3 / a satisfies the chord-difference identity v a(v - a)(1 + d_1)^3 + a(a - 1)(v + d_1)^3 - v(v - 1)(a + d_1)^3 = (v - 1)(a - 1)(v - a)(v a + d_1^3) >= 0 with v = A(d_1), dominating 4(a + d_1)^(3/2) / (sqrt(a) d_1^2) by max(G(d_1), H(d_1)) without calculus.

**Theorem 1.18 (Sharp global O(n^(-3/2)) spectral transfer bound and uniqueness of T(2, 1)).**

$$\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; (2 \le k) \Rightarrow ((1 \le l) \Rightarrow (\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(l\right),\; \forall t \in \mathbb{R},\; (\sqrt{5} \le \operatorname{specD}\left(k, l\right)) \land ((1 < \operatorname{specA}\left(k, l\right)) \land ((\operatorname{specA}\left(k, l\right) \le \operatorname{upperFeasibleA}\left(\operatorname{specD}\left(k, l\right)\right)) \land (((\operatorname{treeOrder}\left(k, l\right) : \mathbb{R}) = \operatorname{specA}\left(k, l\right) \cdot \left(\operatorname{specA}\left(k, l\right) + \operatorname{specD}\left(k, l\right)\right)) \land ((((\operatorname{treeOrder}\left(k, l\right) : \mathbb{R}))^{\frac{3}{2}} \cdot (\operatorname{leafBoundingEntry}\left(k, l, i, j\right))^{2} \le \operatorname{max}\left(\operatorname{envelopeG}\left(\operatorname{specD}\left(k, l\right)\right), \operatorname{envelopeH}\left(\operatorname{specD}\left(k, l\right)\right)\right)) \land ((\operatorname{leafTransferProb}\left(k, l, i, j, t\right) \le (\operatorname{leafBoundingEntry}\left(k, l, i, j\right))^{2}) \land (((\operatorname{leafBoundingEntry}\left(k, l, i, j\right))^{2} \le \operatorname{optimalTransferConst} \cdot ((\operatorname{treeOrder}\left(k, l\right) : \mathbb{R}))^{-\frac{3}{2}}) \land ((((\operatorname{treeOrder}\left(k, l\right) : \mathbb{R}))^{\frac{3}{2}} \cdot (\operatorname{leafBoundingEntry}\left(k, l, i, j\right))^{2} = \operatorname{optimalTransferConst}) \Leftrightarrow ((k = 2) \land (l = 1)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.sharp_global_spectral_transfer_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

For every k >= 2, l >= 1, leaf (i, j), and real time t, the spectral parameters satisfy d >= sqrt(5), 1 < a <= A(d), and n = a(a + d), so n^(3/2) B_{k, l}^2 = 4(a + d)^(3/2) / (sqrt(a) d^2) <= max(G(d), H(d)). At d = sqrt(5), direct algebraic evaluation gives H(sqrt(5)) = C_* and C_*^2 - G(sqrt(5))^2 = 8(3 - sqrt(5)) / 25 > 0, while strict antitonicity of G and H forces max(G(d), H(d)) < C_* whenever d > sqrt(5). Consequently P_{k, l}(t) <= B_{k, l}^2 <= C_* n^(-3/2) everywhere, and the scaled spectral bound n^(3/2) B_{k, l}^2 attains C_* if and only if d = sqrt(5) and a = A(d), which among integers k >= 2 and l >= 1 holds if and only if k = 2 and l = 1.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.envelopeG`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.envelopeH`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.hubVertex`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.leafBoundingEntry`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.leafTransferProb`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.leafVertex`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.optimalTransferConst`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.rootVertex`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.sharp_global_spectral_transfer_bound`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.specA`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.specB`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.specD`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.specS`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.spectral_envelope_and_antitonicity`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.treeOrder`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.twoLevelTree`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.twoLevelTree_leaf_dynamics_and_invariance`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.upperFeasibleA`
- Dependency: [D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees](LaplacianPeakTransferTrees.md)
