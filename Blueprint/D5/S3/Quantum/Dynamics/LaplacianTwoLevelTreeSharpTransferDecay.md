# Non-attained Pell phase supremum and unit asymptotic tail decay for two-level trees

## Abstract

Across all two-level rooted trees T(k, l) with k >= 2 and l >= 1 and all real times t, the scaled root-to-leaf Laplacian transfer probability n^(3/2) P_{k, l}(t) has global supremum C_* = 2 + 6 sqrt(5) / 5, realized already by the time supremum on the single five-vertex tree T(2, 1) along an explicit Pell phase-alignment sequence t_j -> +infinity yet strictly unattained at every finite time because of an integer parity obstruction. Restricting to trees of order n >= N drives both the scaled spectral-bound tail supremum and the scaled transfer-probability tail supremum to 1 as N -> +infinity, yielding uniform (1 + epsilon) n^(-3/2) decay while ruling out O(n^(-beta)) decay for every exponent beta > 3/2 via an infinite even-parameter family attaining peak root-to-leaf transfer at time pi.

**Definition 1.1 (Global set of scaled root-to-leaf transfer probabilities).**

$$\operatorname{scaledTransferSet} = \{y : \mathbb{R} \mid \exists k \in \mathbb{N},\; \exists l \in \mathbb{N},\; (2 \le k) \land ((1 \le l) \land (\exists i \in \operatorname{Fin}\left(k\right),\; \exists j \in \operatorname{Fin}\left(l\right),\; \exists t \in \mathbb{R},\; y = ((\operatorname{treeOrder}\left(k, l\right) : \mathbb{R}))^{\frac{3}{2}} \cdot \operatorname{leafTransferProb}\left(k, l, i, j, t\right)))\}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.scaledTransferSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The set scaledTransferSet collects all real values n^(3/2) P_{k, l}(t) as (k, l) ranges over integers k >= 2 and l >= 1, (i, j) ranges over leaves of T(k, l), and t ranges over all real times, where n = treeOrder k l = 1 + k(l + 1).

**Definition 1.2 (Scaled root-to-leaf transfer set on T(2, 1)).**

$$\forall i \in \operatorname{Fin}\left(2\right),\; \forall j \in \operatorname{Fin}\left(1\right),\; \operatorname{scaledTransferSet21}\left(i, j\right) = \{y : \mathbb{R} \mid \exists t \in \mathbb{R},\; y = (5)^{\frac{3}{2}} \cdot \operatorname{leafTransferProb}\left(2, 1, i, j, t\right)\}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.scaledTransferSet21` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

For a fixed leaf (i, j) of T(2, 1), whose order is n = 5, scaledTransferSet21 i j collects all values 5^(3/2) P_{2, 1}(t) as t ranges over the real line.

**Definition 1.3 (Pell-type integer recurrence approximating sqrt(5)).**

$$(\operatorname{pellPair}\left(0\right) = (2, 1)) \land (\forall j \in \mathbb{N},\; \operatorname{pellPair}\left(j + 1\right) = (9 \cdot \operatorname{Prod}.\operatorname{fst}\left(\operatorname{pellPair}\left(j\right)\right) + 20 \cdot \operatorname{Prod}.\operatorname{snd}\left(\operatorname{pellPair}\left(j\right)\right), 4 \cdot \operatorname{Prod}.\operatorname{fst}\left(\operatorname{pellPair}\left(j\right)\right) + 9 \cdot \operatorname{Prod}.\operatorname{snd}\left(\operatorname{pellPair}\left(j\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.pellPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

Starting from (p_0, m_0) = (2, 1), where 2 - sqrt(5) < 0 has unit norm in Z[sqrt(5)], multiplying repeatedly by the totally positive fundamental square unit 9 + 4 sqrt(5) = (2 + sqrt(5))^2 defines (p_{j + 1}, m_{j + 1}) = (9 p_j + 20 m_j, 4 p_j + 9 m_j).

**Definition 1.4 (Numerator sequence of the Pell phase approximation).**

$$\forall j \in \mathbb{N},\; \operatorname{pellP}\left(j\right) = \operatorname{Prod}.\operatorname{fst}\left(\operatorname{pellPair}\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.pellP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The first coordinate p_j = (pellPair j).1 is even for every j and satisfies p_j - sqrt(5) m_j = (2 - sqrt(5))(9 - 4 sqrt(5))^j -> 0 as j -> +infinity.

**Definition 1.5 (Denominator sequence of the Pell phase approximation).**

$$\forall j \in \mathbb{N},\; \operatorname{pellM}\left(j\right) = \operatorname{Prod}.\operatorname{snd}\left(\operatorname{pellPair}\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.pellM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The second coordinate m_j = (pellPair j).2 is odd, strictly increasing, and bounded below by 9^j, ensuring that 3 m_j - p_j is an odd integer for every j.

**Definition 1.6 (Upper positive root-supported Laplacian eigenvalue on T(2, 1)).**

$$\operatorname{bStar} = \frac{5 + \sqrt{5}}{2}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.bStar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

On T(2, 1) the trace parameter is S = 5 and the discriminant is d = sqrt(5), so the upper positive root-supported eigenvalue is b_* = (5 + sqrt(5)) / 2, while the lower eigenvalue a_* = (5 - sqrt(5)) / 2 satisfies a_* / b_* = (3 - sqrt(5)) / 2.

**Definition 1.7 (Pell phase-alignment times on T(2, 1)).**

$$\forall j \in \mathbb{N},\; \operatorname{approxTime}\left(j\right) = \frac{2 \cdot \pi \cdot (\operatorname{pellM}\left(j\right) : \mathbb{R})}{\operatorname{bStar}}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.approxTime` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

Setting t_j = 2 pi m_j / b_* aligns the upper frequency exactly at exp(i b_* t_j) = exp(2 pi i m_j) = 1 while driving the lower frequency a_* t_j = pi(3 m_j - p_j) + pi(p_j - sqrt(5) m_j) modulo 2 pi toward pi.

**Definition 1.8 (Tail set of scaled squared spectral bounds above threshold N).**

$$\forall N \in \mathbb{R},\; \operatorname{tailBoundingSet}\left(N\right) = \{y : \mathbb{R} \mid \exists k \in \mathbb{N},\; \exists l \in \mathbb{N},\; (2 \le k) \land ((1 \le l) \land ((N \le (\operatorname{treeOrder}\left(k, l\right) : \mathbb{R})) \land (\exists i \in \operatorname{Fin}\left(k\right),\; \exists j \in \operatorname{Fin}\left(l\right),\; y = ((\operatorname{treeOrder}\left(k, l\right) : \mathbb{R}))^{\frac{3}{2}} \cdot (\operatorname{leafBoundingEntry}\left(k, l, i, j\right))^{2})))\}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.tailBoundingSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

For a real order threshold N, tailBoundingSet N collects all scaled squared bounding entries n^(3/2) B_{k, l}^2 over parameters k >= 2, l >= 1 with n = treeOrder k l >= N and leaves (i, j).

**Definition 1.9 (Tail set of scaled root-to-leaf transfer probabilities above threshold N).**

$$\forall N \in \mathbb{R},\; \operatorname{tailTransferSet}\left(N\right) = \{y : \mathbb{R} \mid \exists k \in \mathbb{N},\; \exists l \in \mathbb{N},\; (2 \le k) \land ((1 \le l) \land ((N \le (\operatorname{treeOrder}\left(k, l\right) : \mathbb{R})) \land (\exists i \in \operatorname{Fin}\left(k\right),\; \exists j \in \operatorname{Fin}\left(l\right),\; \exists t \in \mathbb{R},\; y = ((\operatorname{treeOrder}\left(k, l\right) : \mathbb{R}))^{\frac{3}{2}} \cdot \operatorname{leafTransferProb}\left(k, l, i, j, t\right))))\}$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.tailTransferSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

For a real order threshold N, tailTransferSet N collects all scaled transfer probabilities n^(3/2) P_{k, l}(t) over parameters k >= 2, l >= 1 with n = treeOrder k l >= N, leaves (i, j), and real times t.

**Definition 1.10 (Tail supremum of scaled squared spectral bounds).**

$$\forall N \in \mathbb{R},\; \operatorname{tailBoundingSup}\left(N\right) = \operatorname{sSup}\left(\operatorname{tailBoundingSet}\left(N\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.tailBoundingSup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The function tailBoundingSup N = sSup(tailBoundingSet N) records the supremum M_B(N) of n^(3/2) B_{k, l}^2 over all two-level trees of order at least N.

**Definition 1.11 (Tail supremum of scaled root-to-leaf transfer probabilities).**

$$\forall N \in \mathbb{R},\; \operatorname{tailTransferSup}\left(N\right) = \operatorname{sSup}\left(\operatorname{tailTransferSet}\left(N\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.tailTransferSup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The function tailTransferSup N = sSup(tailTransferSet N) records the supremum M_P(N) of n^(3/2) P_{k, l}(t) over all two-level trees of order at least N and all real times t.

**Definition 1.12 (Discriminant lower-bound threshold as a function of tree order).**

$$\forall N \in \mathbb{R},\; \operatorname{tailThresholdD}\left(N\right) = \operatorname{max}\left(\sqrt{5}, \sqrt{4 \cdot \sqrt{N - 1} - 3}\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.tailThresholdD` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

For N >= 4, every two-level tree with k >= 2, l >= 1, and 1 + k(l + 1) >= N satisfies k + l + 1 >= 2 sqrt(N - 1) and (k - l)^2 + 4 l >= 2(k + l + 1) - 3, so its discriminant specD k l is bounded below by D_N = max(sqrt(5), sqrt(4 sqrt(N - 1) - 3)).

**Theorem 1.13 (Global supremum C_*, strict finite-time non-attainment, and Pell convergence).**

$$\forall m \in \mathbb{N},\; (\operatorname{approxTime}\left(m\right) < \operatorname{approxTime}\left(m + 1\right)) \land ((\operatorname{Set}.\operatorname{Nonempty}\left(\operatorname{scaledTransferSet}\right)) \land ((\operatorname{BddAbove}\left(\operatorname{scaledTransferSet}\right)) \land ((\operatorname{IsLUB}\left(\operatorname{scaledTransferSet}, \operatorname{optimalTransferConst}\right)) \land ((\operatorname{sSup}\left(\operatorname{scaledTransferSet}\right) = \operatorname{optimalTransferConst}) \land ((\forall i0 \in \operatorname{Fin}\left(2\right),\; \forall j0 \in \operatorname{Fin}\left(1\right),\; (\operatorname{Set}.\operatorname{Nonempty}\left(\operatorname{scaledTransferSet21}\left(i0, j0\right)\right)) \land ((\operatorname{BddAbove}\left(\operatorname{scaledTransferSet21}\left(i0, j0\right)\right)) \land ((\operatorname{IsLUB}\left(\operatorname{scaledTransferSet21}\left(i0, j0\right), \operatorname{optimalTransferConst}\right)) \land ((\operatorname{sSup}\left(\operatorname{scaledTransferSet}\right) = \operatorname{sSup}\left(\operatorname{scaledTransferSet21}\left(i0, j0\right)\right)) \land (\operatorname{sSup}\left(\operatorname{scaledTransferSet21}\left(i0, j0\right)\right) = \operatorname{optimalTransferConst}))))) \land ((\forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; (2 \le k) \Rightarrow ((1 \le l) \Rightarrow (\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(l\right),\; \forall t \in \mathbb{R},\; ((\operatorname{treeOrder}\left(k, l\right) : \mathbb{R}))^{\frac{3}{2}} \cdot \operatorname{leafTransferProb}\left(k, l, i, j, t\right) < \operatorname{optimalTransferConst}))) \land ((\operatorname{Filter}.\operatorname{Tendsto}\left(\operatorname{approxTime}, \operatorname{Filter}.\operatorname{atTop}, \operatorname{Filter}.\operatorname{atTop}\right)) \land (\forall i0 \in \operatorname{Fin}\left(2\right),\; \forall j0 \in \operatorname{Fin}\left(1\right),\; \operatorname{Filter}.\operatorname{Tendsto}\left(\lambda (j : \mathbb{N}) \mapsto ((5)^{\frac{3}{2}} \cdot \operatorname{leafTransferProb}\left(2, 1, i0, j0, \operatorname{approxTime}\left(j\right)\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(\operatorname{optimalTransferConst}\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.sharp_transfer_supremum_and_pell_approx` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

The approximation times t_m = 2 pi m_m / b_* are strictly increasing and diverge to +infinity. For every k >= 2, l >= 1, leaf (i, j), and real time t, one has the strict inequality n^(3/2) P_{k, l}(t) < C_*: when (k, l) != (2, 1), the uniqueness clause of sharp_global_spectral_transfer_bound gives n^(3/2) B_{k, l}^2 < C_*; when (k, l) = (2, 1), expanding B_{2, 1}^2 - P_{2, 1}(t) as the sum of three nonnegative cosine-gap terms 2 c A_0(1 + cos(a_* t)) + 2 c B_0(1 - cos(b_* t)) + 2 A_0 B_0(1 + cos((a_* - b_*) t)) shows that equality would force a_* t = (2 u + 1) pi and b_* t = 2 v pi for integers u, v, leading to the impossible integer parity equation (4 v - 6 u - 3)^2 = 5(2 u + 1)^2 whose difference is 4(2(2 v^2 - 6 u v - 3 v + 2 u^2 + 2 u) + 1) != 0. Conversely, at t_j on T(2, 1), the odd parity of 3 m_j - p_j yields 5^(3/2) P_{2, 1}(t_j) = (C_* / 2)(1 + cos(pi delta_j)) with delta_j = (2 - sqrt(5))(9 - 4 sqrt(5))^j -> 0, which converges to C_* and establishes nonemptiness, boundedness above, and least-upper-bound equality sSup(scaledTransferSet) = sSup(scaledTransferSet21 i_0 j_0) = C_*.

**Theorem 1.14 (Unit asymptotic tail constant, uniform (1 + epsilon) n^(-3/2) bound, and sharpness).**

$$\forall N \in \mathbb{R},\; (4 \le N) \Rightarrow ((1 \le \operatorname{tailTransferSup}\left(N\right)) \land ((\operatorname{tailTransferSup}\left(N\right) \le \operatorname{tailBoundingSup}\left(N\right)) \land ((\operatorname{tailBoundingSup}\left(N\right) \le \operatorname{max}\left(\operatorname{envelopeG}\left(\operatorname{tailThresholdD}\left(N\right)\right), \operatorname{envelopeH}\left(\operatorname{tailThresholdD}\left(N\right)\right)\right)) \land ((\forall M \in \mathbb{R},\; (\operatorname{Set}.\operatorname{Nonempty}\left(\operatorname{tailBoundingSet}\left(M\right)\right)) \land ((\operatorname{BddAbove}\left(\operatorname{tailBoundingSet}\left(M\right)\right)) \land ((\operatorname{IsLUB}\left(\operatorname{tailBoundingSet}\left(M\right), \operatorname{tailBoundingSup}\left(M\right)\right)) \land ((\operatorname{Set}.\operatorname{Nonempty}\left(\operatorname{tailTransferSet}\left(M\right)\right)) \land ((\operatorname{BddAbove}\left(\operatorname{tailTransferSet}\left(M\right)\right)) \land (\operatorname{IsLUB}\left(\operatorname{tailTransferSet}\left(M\right), \operatorname{tailTransferSup}\left(M\right)\right))))))) \land ((\operatorname{Filter}.\operatorname{Tendsto}\left(\operatorname{tailBoundingSup}, \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left((1 : \mathbb{R})\right)\right)) \land ((\operatorname{Filter}.\operatorname{Tendsto}\left(\operatorname{tailTransferSup}, \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left((1 : \mathbb{R})\right)\right)) \land ((\forall eps \in \mathbb{R},\; (0 < eps) \Rightarrow (\exists N0 \in \mathbb{R},\; \forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; (2 \le k) \Rightarrow ((1 \le l) \Rightarrow ((N0 \le (\operatorname{treeOrder}\left(k, l\right) : \mathbb{R})) \Rightarrow (\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(l\right),\; \forall t \in \mathbb{R},\; (\operatorname{leafTransferProb}\left(k, l, i, j, t\right) \le (\operatorname{leafBoundingEntry}\left(k, l, i, j\right))^{2}) \land ((\operatorname{leafBoundingEntry}\left(k, l, i, j\right))^{2} \le \left(1 + eps\right) \cdot ((\operatorname{treeOrder}\left(k, l\right) : \mathbb{R}))^{-\frac{3}{2}})))))) \land (\forall beta \in \mathbb{R},\; (\frac{3}{2} < beta) \Rightarrow (\neg (\exists C \in \mathbb{R},\; \forall k \in \mathbb{N},\; \forall l \in \mathbb{N},\; (2 \le k) \Rightarrow ((1 \le l) \Rightarrow (\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(l\right),\; \forall t \in \mathbb{R},\; \operatorname{leafTransferProb}\left(k, l, i, j, t\right) \le C \cdot ((\operatorname{treeOrder}\left(k, l\right) : \mathbb{R}))^{-beta}))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.sharp_asymptotic_tail_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Coutinho, Krystal Guo, Vincent Schmeits (2025). *Peak state transfer in continuous quantum walks*. DOI: [10.48550/arXiv.2505.11986](https://doi.org/10.48550/arXiv.2505.11986). URL: <https://arxiv.org/abs/2505.11986v4>.

*Commentary.*

For every positive even integer s = 2(m + 1), choosing l_s = s(s + 1) and k_s = l_s + 1 produces odd lower eigenvalue a_s = s^2 + 1, even upper eigenvalue b_s = (s + 1)^2 + 1, and discriminant d_s = 2 s + 1; at t = pi the phases exp(i pi a_s) = -1 and exp(i pi b_s) = 1 align constructively so that P_{k_s, l_s}(pi) = B_{k_s, l_s}^2 and n_s^(3/2) P_{k_s, l_s}(pi) = H(2 s + 1) > 1. Because n_s >= m can be chosen above any threshold M, both tail sets are nonempty and bounded above by C_*, and 1 <= M_P(N) <= M_B(N) holds for all N >= 4. Conversely, specD k l >= D_N and antitonicity of G and H give M_B(N) <= max(G(D_N), H(D_N)); for d >= 128 one has G(d) <= 1 < H(d) <= 1 + 175 / d, while D_N -> +infinity as N -> +infinity, forcing both M_B(N) -> 1 and M_P(N) -> 1. This yields for every epsilon > 0 a threshold N_0 above which P_{k, l}(t) <= B_{k, l}^2 <= (1 + epsilon) n^(-3/2), whereas for any exponent beta > 3/2 the even-s family satisfies n_s^beta P_{k_s, l_s}(pi) = n_s^(beta - 3/2) H(2 s + 1) > n_s^(beta - 3/2) -> +infinity, refuting every global O(n^(-beta)) upper bound.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.approxTime`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.bStar`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.pellM`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.pellP`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.pellPair`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.scaledTransferSet`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.scaledTransferSet21`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.sharp_asymptotic_tail_decay`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.sharp_transfer_supremum_and_pell_approx`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.tailBoundingSet`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.tailBoundingSup`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.tailThresholdD`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.tailTransferSet`
- Truth anchor: `D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.tailTransferSup`
- Dependency: [D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound](LaplacianTwoLevelTreeSpectralBound.md)
