# The block Bloch state has strictly largest HKNN weight

## Abstract

The block Bloch state has strictly largest HKNN weight

**Definition 1.1 (claim).**

$$\operatorname{claim} \Leftrightarrow (\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow ((\operatorname{bloch}\left(m, \operatorname{block}\left(m\right), \operatorname{fin}\left(m, 2 \cdot m\right)\right) \ne 0) \land (\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; (\operatorname{bloch}\left(m, x, t\right) \ne 0) \Rightarrow ((\neg ((\exists j \in \mathbb{N},\; x = \operatorname{iterate}\left(\operatorname{shift}\left(m\right), j, \operatorname{block}\left(m\right)\right)) \land (\operatorname{val}\left(t\right) = m))) \Rightarrow (\operatorname{weight}\left(m, x, t\right) < \operatorname{weight}\left(m, \operatorname{block}\left(m\right), \operatorname{fin}\left(m, 2 \cdot m\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight.claim` (`✓ std3`).

*Citation.* Zimeng Li; Ning Wu (2026). *Exact momentum-space analysis of small spin-1/2 J1-J2 rings*. DOI: [10.48550/arXiv.2604.23149](https://doi.org/10.48550/arXiv.2604.23149). URL: <https://arxiv.org/abs/2604.23149v1>.

*Commentary.*

Li and Wu, p. 12, after Eq. (47): "Thus, we conjecture that this property holds for arbitrary even number N, i.e., the Bloch state |ξ1,1,...,1(−π)⟩ (there are N/2 − 1 1’s) should have the largest weight in |ψHKNN(N)⟩.". Eq. (6), p. 4: "|ψHKNN⟩ = Σ_{aj<bj and a1<a2<···<aN/2} [a1, b1] · · · [aN/2, bN/2], (6)"; "where the sum is over all partitions of {1, 2, . . . , N} into pairs without regard to order." Singlet, p. 3: "[i, j] ≡ | ↑⟩i | ↓⟩j − | ↓⟩i | ↑⟩j is a singlet state on sites i and j.". Bloch normalization, p. 4, Eq. (7): "|ξ1(k)⟩ = e^{ik/2}/√6 Σ_{j=0}^{5} e^{ikj} T^j |1, 2⟩, |ξ2(k)⟩ = e^{ik}/√6 Σ_{j=0}^{5} e^{ikj} T^j |1, 3⟩, |ξ3(k)⟩ = e^{i3k/2}/√3 Σ_{j=0}^{2} e^{ikj} T^j |1, 4⟩, (7)". N=2m, m>=1; site i corresponds to paper site i+1. The middle index is the Fin (2*m) constructor value with natural value m and the bound m < 2*m supplied by m>=1; fin(m,2*m) displays that value. It carries pi=-pi. The exclusion removes the same block ray up to phase; every other nonzero Bloch state is compared strictly.

**Theorem 1.2 (result).**

$$\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow ((\operatorname{bloch}\left(m, \operatorname{block}\left(m\right), \operatorname{fin}\left(m, 2 \cdot m\right)\right) \ne 0) \land (\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \forall t \in \operatorname{Fin}\left(2 \cdot m\right),\; (\operatorname{bloch}\left(m, x, t\right) \ne 0) \Rightarrow ((\neg ((\exists j \in \mathbb{N},\; x = \operatorname{iterate}\left(\operatorname{shift}\left(m\right), j, \operatorname{block}\left(m\right)\right)) \land (\operatorname{val}\left(t\right) = m))) \Rightarrow (\operatorname{weight}\left(m, x, t\right) < \operatorname{weight}\left(m, \operatorname{block}\left(m\right), \operatorname{fin}\left(m, 2 \cdot m\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The block coefficient attains the crossing-pairing modulus. Every non-arc configuration has a strict deficit because interleaving partners can be swapped to reverse one sign. Translation selects the middle momentum, and the finite support estimate promotes coefficient maximality to strict normalized Bloch weight maximality.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight.result`
- Dependency: [D5/S1/Phase/SeatTowerCombinatorics](../../../S1/Phase/SeatTowerCombinatorics.md)
- Dependency: [D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients](HKNNBlockBlochLargestWeight/PairingCoefficients.md)
- Dependency: [D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison](HKNNBlockBlochLargestWeight/SpectralComparison.md)
