# Signed pairing coefficients and cyclic translation

## Abstract

Signed pairing coefficients and cyclic translation

**Definition 1.1 (s).**

$$\operatorname{s} = a:\operatorname{Bool} \mapsto b:\operatorname{Bool} \mapsto \operatorname{ite}\left((a = \operatorname{false}) \land (b = \operatorname{true}), 1, \operatorname{ite}\left((a = \operatorname{true}) \land (b = \operatorname{false}), -1, 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.s` (`✓ std3`).

*Citation.* Zimeng Li; Ning Wu (2026). *Exact momentum-space analysis of small spin-1/2 J1-J2 rings*. DOI: [10.48550/arXiv.2604.23149](https://doi.org/10.48550/arXiv.2604.23149). URL: <https://arxiv.org/abs/2604.23149v1>.

*Commentary.*

Li and Wu, p. 3, after Eq. (4): "[i, j] ≡ | ↑⟩i | ↓⟩j − | ↓⟩i | ↑⟩j is a singlet state on sites i and j.". The two nonzero integer coefficients are +1 and -1.

**Definition 1.2 (term).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \forall f \in \operatorname{FixedPointFreeInvolution}\left(\operatorname{Fin}\left(2 \cdot m\right)\right),\; \operatorname{term}\left(m, x, f\right) = \prod_{i\in \operatorname{filter}\left(\operatorname{univ}\left(\operatorname{Fin}\left(2 \cdot m\right)\right), i:\operatorname{Fin}\left(2 \cdot m\right) \mapsto i < \operatorname{apply}\left(\operatorname{val}\left(f\right), i\right)\right)} \operatorname{s}\left(\operatorname{apply}\left(x, i\right), \operatorname{apply}\left(x, \operatorname{apply}\left(\operatorname{val}\left(f\right), i\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.term` (`✓ std3`).

*Citation.* Zimeng Li; Ning Wu (2026). *Exact momentum-space analysis of small spin-1/2 J1-J2 rings*. DOI: [10.48550/arXiv.2604.23149](https://doi.org/10.48550/arXiv.2604.23149). URL: <https://arxiv.org/abs/2604.23149v1>.

*Commentary.*

Each unordered edge contributes once, with its smaller endpoint first. The product is the computational-basis coefficient of its tensor product of singlets.

**Definition 1.3 (psi).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \operatorname{psi}\left(m, x\right) = \sum_{f:\operatorname{FixedPointFreeInvolution}\left(\operatorname{Fin}\left(2 \cdot m\right)\right)} \operatorname{term}\left(m, x, f\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.psi` (`✓ std3`).

*Citation.* Zimeng Li; Ning Wu (2026). *Exact momentum-space analysis of small spin-1/2 J1-J2 rings*. DOI: [10.48550/arXiv.2604.23149](https://doi.org/10.48550/arXiv.2604.23149). URL: <https://arxiv.org/abs/2604.23149v1>.

*Commentary.*

Li and Wu, p. 4, Eq. (6): "|ψHKNN⟩ = Σ_{aj<bj and a1<a2<···<aN/2} [a1, b1] · · · [aN/2, bN/2], (6)"; "where the sum is over all partitions of {1, 2, . . . , N} into pairs without regard to order." The existing fixed-point-free involution carrier represents each partition once, with no Pfaffian permutation sign.

**Definition 1.4 (block).**

$$\forall m \in \mathbb{N},\; \operatorname{block}\left(m\right) = i:\operatorname{Fin}\left(2 \cdot m\right) \mapsto \operatorname{decide}\left(\operatorname{val}\left(i\right) < m\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.block` (`✓ std3`).

*Citation.* Zimeng Li; Ning Wu (2026). *Exact momentum-space analysis of small spin-1/2 J1-J2 rings*. DOI: [10.48550/arXiv.2604.23149](https://doi.org/10.48550/arXiv.2604.23149). URL: <https://arxiv.org/abs/2604.23149v1>.

*Commentary.*

The first m sites are down and the other m sites are up. This is the configuration with all successive down-spin separations equal to one.

**Definition 1.5 (balanced).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \operatorname{balanced}\left(m, x\right) = \left(\operatorname{card}\left(\operatorname{filter}\left(\operatorname{univ}\left(\operatorname{Fin}\left(2 \cdot m\right)\right), i:\operatorname{Fin}\left(2 \cdot m\right) \mapsto \operatorname{apply}\left(x, i\right) = \operatorname{true}\right)\right) = m\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.balanced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A configuration is balanced when exactly m sites are down.

**Definition 1.6 (crossing).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \forall f \in \operatorname{FixedPointFreeInvolution}\left(\operatorname{Fin}\left(2 \cdot m\right)\right),\; \operatorname{crossing}\left(x, f\right) = \left(\forall i \in \operatorname{Fin}\left(2 \cdot m\right),\; \operatorname{apply}\left(x, i\right) \ne \operatorname{apply}\left(x, \operatorname{apply}\left(\operatorname{val}\left(f\right), i\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.crossing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every pair has opposite spins.

**Definition 1.7 (Down).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \operatorname{Down}\left(m, x\right) = \{i:\operatorname{Fin}\left(2 \cdot m\right) \mid \operatorname{apply}\left(x, i\right) = \operatorname{true}\}$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.Down` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype of down sites retains its site index.

**Definition 1.8 (Up).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \operatorname{Up}\left(m, x\right) = \{i:\operatorname{Fin}\left(2 \cdot m\right) \mid \operatorname{apply}\left(x, i\right) \ne \operatorname{true}\}$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.Up` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complementary subtype of up sites retains its site index.

**Definition 1.9 (CrossPairings).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \operatorname{CrossPairings}\left(m, x\right) = \{f:\operatorname{FixedPointFreeInvolution}\left(\operatorname{Fin}\left(2 \cdot m\right)\right) \mid \operatorname{crossing}\left(x, f\right)\}$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.CrossPairings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Crossing pairings are precisely the opposite-spin pair partitions.

**Definition 1.10 (K).**

$$\forall m \in \mathbb{N},\; \operatorname{K}\left(m\right) = \operatorname{card}\left(\operatorname{CrossPairings}\left(m, \operatorname{block}\left(m\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K is the number of crossing pair partitions for the block configuration. Its positivity and the equality of balanced-sector counts follow from explicit equivalences.

**Definition 1.11 (shift).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \operatorname{shift}\left(m, x\right) = i:\operatorname{Fin}\left(2 \cdot m\right) \mapsto \operatorname{apply}\left(x, \operatorname{FinIndex}\left(\operatorname{NatMod}\left(\operatorname{val}\left(i\right) + (2 \cdot m - 1), 2 \cdot m\right), \operatorname{Fin}\left(2 \cdot m\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.shift` (`✓ std3`).

*Citation.* Zimeng Li; Ning Wu (2026). *Exact momentum-space analysis of small spin-1/2 J1-J2 rings*. DOI: [10.48550/arXiv.2604.23149](https://doi.org/10.48550/arXiv.2604.23149). URL: <https://arxiv.org/abs/2604.23149v1>.

*Commentary.*

The translation acts on coefficients by the predecessor site modulo 2m. NatMod is natural-number remainder; subtraction on naturals is truncated. Li and Wu define translation by T S_j^- T^{-1} = S_{j+1}^- (p. 2).

**Definition 1.12 (isArc).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \operatorname{isArc}\left(m, x\right) = \left(\exists j \in \mathbb{N},\; x = \operatorname{iterate}\left(\operatorname{shift}\left(m\right), j, \operatorname{block}\left(m\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.isArc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An arc is any cyclic translate of the block configuration.

**Theorem 1.13 (pairing_data).**

$$\forall m \in \mathbb{N},\; (\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \forall f \in \operatorname{FixedPointFreeInvolution}\left(\operatorname{Fin}\left(2 \cdot m\right)\right),\; (\operatorname{crossing}\left(x, f\right)) \Rightarrow (\operatorname{balanced}\left(m, x\right))) \land (((0 < \operatorname{K}\left(m\right)) \land ((\lvert \operatorname{psi}\left(m, \operatorname{block}\left(m\right)\right)\rvert = \operatorname{castInt}\left(\operatorname{K}\left(m\right)\right)) \land ((\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; (\neg (\operatorname{balanced}\left(m, x\right))) \Rightarrow (\operatorname{psi}\left(m, x\right) = 0)) \land (\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \lvert \operatorname{psi}\left(m, x\right)\rvert \le \operatorname{castInt}\left(\operatorname{K}\left(m\right)\right))))) \land ((\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; (\operatorname{balanced}\left(m, x\right)) \Rightarrow (\forall d \in \operatorname{Down}\left(m, x\right),\; \forall e \in \operatorname{Down}\left(m, x\right),\; \forall u \in \operatorname{Up}\left(m, x\right),\; \forall v \in \operatorname{Up}\left(m, x\right),\; (\operatorname{val}\left(d\right) < \operatorname{val}\left(u\right)) \Rightarrow ((\operatorname{val}\left(u\right) < \operatorname{val}\left(e\right)) \Rightarrow ((\operatorname{val}\left(e\right) < \operatorname{val}\left(v\right)) \Rightarrow (\lvert \operatorname{psi}\left(m, x\right)\rvert < \operatorname{castInt}\left(\operatorname{K}\left(m\right)\right)))))) \land (([\operatorname{NeZero}\left(2 \cdot m\right)] (1 \le m) \Rightarrow (\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \operatorname{psi}\left(m, \operatorname{shift}\left(m, x\right)\right) = -\operatorname{psi}\left(m, x\right))) \land ((\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \forall j \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(2 \cdot m\right),\; \operatorname{apply}\left(\operatorname{iterate}\left(\operatorname{shift}\left(m\right), j, x\right), i\right) = \operatorname{apply}\left(x, \operatorname{FinIndex}\left(\operatorname{NatMod}\left(\operatorname{val}\left(i\right) + \left(2 \cdot m - 1\right) \cdot j, 2 \cdot m\right), \operatorname{Fin}\left(2 \cdot m\right)\right)\right)) \land ([\operatorname{NeZero}\left(2 \cdot m\right)] (1 \le m) \Rightarrow (\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; \forall j \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(2 \cdot m\right),\; \operatorname{apply}\left(\operatorname{iterate}\left(\operatorname{shift}\left(m\right), j, x\right), i\right) = \operatorname{apply}\left(x, i - \operatorname{castFin}\left(j, \operatorname{Fin}\left(2 \cdot m\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.pairing_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Crossing involutions give a bijection between down and up sites. The block has one sign on every supported term and K is positive. Transporting down-to-up bijections gives a uniform count. Prescribing two interleaving edges and swapping their partners yields opposite signs and a strict coefficient deficit. Under rotation exactly one pair crosses the cyclic cut, giving a global minus sign. The last two clauses state the site formula for iterated translation.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.CrossPairings`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.Down`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.K`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.Up`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.balanced`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.block`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.crossing`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.isArc`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.pairing_data`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.psi`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.s`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.shift`
- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients.term`
- Dependency: [D5/S1/Phase/SeatTowerCombinatorics](../../../../S1/Phase/SeatTowerCombinatorics.md)
- Dependency: [D5/S3/Zeros/Convolution/PerfectMatchingCount](../../../Zeros/Convolution/PerfectMatchingCount.md)
