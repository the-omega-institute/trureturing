# Complex sparse-probe coercivity

## Abstract

A coordinate basis and one unit vector of full support control the Hilbert--Schmidt distance to scalar matrices.

**Definition 1.1 (hsSq).**

$$\forall d \in \mathbb{N}, M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{hsSq}\left(M\right) = \sum_{i : \operatorname{Fin}\left(d\right)} \sum_{j : \operatorname{Fin}\left(d\right)} \operatorname{normSq}\left(M (i, j)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.hsSq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

hsSq is the sum of the squared complex moduli of all matrix entries.

**Definition 1.2 (offSq).**

$$\forall d \in \mathbb{N}, M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{offSq}\left(M\right) = \sum_{i : \operatorname{Fin}\left(d\right)} \sum_{j : \operatorname{Fin}\left(d\right)} \operatorname{ite}\left(i = j, 0, \operatorname{normSq}\left(M (i, j)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.offSq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

offSq is the corresponding sum over unequal row and column indices.

**Definition 1.3 (survivalLoss).**

$$\forall d \in \mathbb{N}, M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), v \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; \operatorname{survivalLoss}\left(M, v\right) = \sum_{i : \operatorname{Fin}\left(d\right)} \operatorname{normSq}\left(\operatorname{mulVec}\left(M, v\right) (i)\right) - \operatorname{normSq}\left(\sum_{i : \operatorname{Fin}\left(d\right)} \operatorname{conj}\left(v (i)\right) \cdot \operatorname{mulVec}\left(M, v\right) (i)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.survivalLoss` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The survival loss is the squared norm of Cv minus the squared modulus of its inner product with the unit probe v. For a complete Kraus family its sum is the loss of the rank-one survival event.

**Definition 1.4 (probeLoss).**

$$\forall d \in \mathbb{N}, M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), v \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; \operatorname{probeLoss}\left(M, v\right) = \operatorname{offSq}\left(M\right) + \operatorname{survivalLoss}\left(M, v\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.probeLoss` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate losses sum to offSq. The additional probe contributes survivalLoss, so there are d+1 survival events.

**Lemma 1.5 (hs_split).**

$$\forall d \in \mathbb{N}, M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{hsSq}\left(M\right) = \operatorname{offSq}\left(M\right) + \sum_{i : \operatorname{Fin}\left(d\right)} \operatorname{normSq}\left(M (i, i)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.hs_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Separating the diagonal entries gives the Hilbert--Schmidt decomposition.

**Theorem 1.6 (sparse_probe_coercivity).**

$$\forall d \in \mathbb{N}, M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), v \in \operatorname{Fin}\left(d\right) \to \mathbb{C}, mu \in \mathbb{R},\; \left(0 < d \land \left(\sum_{i : \operatorname{Fin}\left(d\right)} \operatorname{normSq}\left(v (i)\right) = 1 \land \left(0 < mu \land \left(\forall i \in \operatorname{Fin}\left(d\right),\; mu \le \operatorname{normSq}\left(v (i)\right)\right)\right)\right)\right) \Rightarrow \frac{mu}{2 + mu} \cdot \left(\operatorname{hsSq}\left(M\right) - \frac{\operatorname{normSq}\left(\operatorname{trace}\left(M\right)\right)}{d}\right) \le \operatorname{probeLoss}\left(M, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.sparse_probe_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c be the complex inner product of v with Cv, and let B be the off-diagonal part of C. The diagonal residual (Cii-c)vi is (Cv-cv)i-(Bv)i. Its squared norm is at most twice the sum of the two squared norms. The unit-vector Cauchy--Schwarz estimate bounds the squared norm of Bv by offSq. Full support bounds the unweighted diagonal residual by its weighted counterpart divided by mu. The trace mean minimizes the unweighted residual, giving the displayed coefficient mu/(2+mu). The argument allows arbitrary complex matrices; no real, Hermitian, or unital condition is present.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.hsSq`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.hs_split`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.offSq`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.probeLoss`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.sparse_probe_coercivity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.survivalLoss`
- Dependency: [D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity](TomiyamaDiagonalKPositivity.md)
