# Operational sparse-probe compression bound

## Abstract

Every finite classical-quantum port incurs a uniform two-setting total-variation error when its quantum block is smaller than the input dimension.

**Definition 1.1 (Port).**

$$\forall d \in \mathbb{N}, q \in \mathbb{N}, F \in \operatorname{FiniteType}\left(\right), a \in \operatorname{FiniteFamily}\left(F\right), b \in \operatorname{FiniteFamily}\left(F\right), P \in \operatorname{Port}\left(d, q, F, a, b\right),\; \sum_{f : F} \sum_{i : a (f)} \operatorname{adjoint}\left(\operatorname{encode}\left(P, f, i\right)\right) \cdot \operatorname{encode}\left(P, f, i\right) = 1 \land \left(\forall f \in F,\; \sum_{j : b (f)} \operatorname{adjoint}\left(\operatorname{decode}\left(P, f, j\right)\right) \cdot \operatorname{decode}\left(P, f, j\right) = 1\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.Port` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FiniteType denotes an arbitrary type equipped with Fintype, FiniteFamily(F) denotes an F-indexed family of such types, and Branch(F,a,b) is the dependent sum of a(f) times b(f). A port has arbitrary finite classical flags F and finite, flag-dependent encoder and decoder Kraus families. Its encoder matrices have size q by d and its decoder matrices have size d by q. Encoder completeness holds after summing all flags. Each decoder is trace preserving on the entire q-dimensional block. The same encoder and decoder are used at both future settings. All input-dependent quantum information passes through the block; the flag is a classical record. This is the measurement-relative compression model of Bluhm, Rauber and Wolf, arXiv:1708.04898v4. Mayer and Knill, arXiv:1805.04491v1, Theorem 1 supplies connected-probe rigidity, with broader nondisturbance structure in Koashi and Imoto, quant-ph/0101144.

**Definition 1.2 (Port.kraus).**

$$\forall d \in \mathbb{N}, q \in \mathbb{N}, F \in \operatorname{FiniteType}\left(\right), a \in \operatorname{FiniteFamily}\left(F\right), b \in \operatorname{FiniteFamily}\left(F\right), P \in \operatorname{Port}\left(d, q, F, a, b\right), x \in \operatorname{Branch}\left(F, a, b\right),\; \operatorname{kraus}\left(P, x\right) = \operatorname{decode}\left(P, \operatorname{flag}\left(x\right), \operatorname{decoderIndex}\left(x\right)\right) \cdot \operatorname{encode}\left(P, \operatorname{flag}\left(x\right), \operatorname{encoderIndex}\left(x\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.kraus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The composite branch is Rfb Bfa, indexed by the actual flag and both finite Kraus indices.

**Definition 1.3 (Port.channel).**

$$\forall d \in \mathbb{N}, q \in \mathbb{N}, F \in \operatorname{FiniteType}\left(\right), a \in \operatorname{FiniteFamily}\left(F\right), b \in \operatorname{FiniteFamily}\left(F\right), P \in \operatorname{Port}\left(d, q, F, a, b\right), M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{channelAction}\left(\operatorname{channel}\left(P\right), M\right) = \sum_{x : \operatorname{Branch}\left(F, a, b\right)} \operatorname{kraus}\left(P, x\right) \cdot M \cdot \operatorname{adjoint}\left(\operatorname{kraus}\left(P, x\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.channel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Completeness gives an actual channel in the canonical completely positive, trace-preserving interface. Its action on every matrix is the sum of composite Kraus conjugations.

**Definition 1.4 (probabilities).**

$$\forall d \in \mathbb{N}, U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), i \in \operatorname{Fin}\left(d\right),\; \operatorname{probabilities}\left(U, rho\right) (i) = \operatorname{re}\left((U \cdot \operatorname{matrix}\left(rho\right) \cdot \operatorname{adjoint}\left(U\right)) (i, i)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.probabilities` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The notation matrix(rho) is CStarMatrix.ofMatrix.symm applied to the underlying density-state matrix. These are the Born probabilities of a complete coordinate readout after the displayed unitary. The input is any complex positive semidefinite density matrix of trace one.

**Definition 1.5 (twoSettingError).**

$$\forall d \in \mathbb{N}, U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), T \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right),\; \operatorname{twoSettingError}\left(U, T\right) = \operatorname{sSup}\left(\left\{\operatorname{max}\left(\operatorname{totalVariation}\left(\operatorname{probabilities}\left(1, rho\right), \operatorname{probabilities}\left(1, \operatorname{mapState}\left(T, rho\right)\right)\right), \operatorname{totalVariation}\left(\operatorname{probabilities}\left(U, rho\right), \operatorname{probabilities}\left(U, \operatorname{mapState}\left(T, rho\right)\right)\right)\right) \mid rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right)\right\}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.twoSettingError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supremum ranges over every density input. Both errors use the same channel. Total variation is one half of the finite sum of absolute probability differences.

**Definition 1.6 (PortEstimate).**

$$\forall d \in \mathbb{N}, q \in \mathbb{N}, F \in \operatorname{FiniteType}\left(\right), a \in \operatorname{FiniteFamily}\left(F\right), b \in \operatorname{FiniteFamily}\left(F\right), P \in \operatorname{Port}\left(d, q, F, a, b\right), U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), v \in \operatorname{Fin}\left(d\right) \to \mathbb{C}, mu \in \mathbb{R},\; \operatorname{PortEstimate}\left(P, U, v, mu\right) \Leftrightarrow \left(\left(\forall x \in \operatorname{Branch}\left(F, a, b\right),\; \operatorname{rank}\left(\operatorname{kraus}\left(P, x\right)\right) \le q\right) \land \left(\sum_{x : \operatorname{Branch}\left(F, a, b\right)} \operatorname{hsSq}\left(\operatorname{kraus}\left(P, x\right)\right) = d \land \left(\sum_{x : \operatorname{Branch}\left(F, a, b\right)} \operatorname{normSq}\left(\operatorname{trace}\left(\operatorname{kraus}\left(P, x\right)\right)\right) \le q \cdot d \land \left(\frac{mu}{2 + mu} \cdot \left(d - q\right) \le \sum_{x : \operatorname{Branch}\left(F, a, b\right)} \operatorname{probeLoss}\left(\operatorname{kraus}\left(P, x\right), v\right) \land \left(\sum_{x : \operatorname{Branch}\left(F, a, b\right)} \operatorname{probeLoss}\left(\operatorname{kraus}\left(P, x\right), v\right) \le \left(d + 1\right) \cdot \operatorname{twoSettingError}\left(U, \operatorname{channel}\left(P\right)\right) \land \frac{mu \cdot \left(d - q\right)}{\left(2 + mu\right) \cdot \left(d + 1\right)} \le \operatorname{twoSettingError}\left(U, \operatorname{channel}\left(P\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.PortEstimate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the composite rank bound, total Hilbert--Schmidt square, trace-square bound, both total-loss estimates, and the actual two-setting error lower bound. Dimension differences and the quantitative bounds use real arithmetic; matrix rank and block dimension use natural numbers.

**Definition 1.7 (portErrors).**

$$\forall d \in \mathbb{N}, q \in \mathbb{N}, U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), e \in \mathbb{R},\; e \in \operatorname{portErrors}\left(d, q, U\right) \Leftrightarrow \left(\exists F \in \operatorname{FiniteType}\left(\right), a \in \operatorname{FiniteFamily}\left(F\right), b \in \operatorname{FiniteFamily}\left(F\right), P \in \operatorname{Port}\left(d, q, F, a, b\right),\; e = \operatorname{twoSettingError}\left(U, \operatorname{channel}\left(P\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.portErrors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The attainable errors allow every finite flag carrier and every finite dependent pair of Kraus-index families, without a bound on the number of flags.

**Theorem 1.8 (sparse_probe_port_bound).**

$$\forall d \in \mathbb{N}, q \in \mathbb{N}, U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), v \in \operatorname{Fin}\left(d\right) \to \mathbb{C}, r \in \operatorname{Fin}\left(d\right), mu \in \mathbb{R},\; \left(0 < d \land \left(0 < q \land \left(\operatorname{adjoint}\left(U\right) \cdot U = 1 \land \left(\sum_{i : \operatorname{Fin}\left(d\right)} \operatorname{normSq}\left(v (i)\right) = 1 \land \left(\left(\forall i \in \operatorname{Fin}\left(d\right),\; U (r, i) = \operatorname{conj}\left(v (i)\right)\right) \land \left(0 < mu \land \left(\forall i \in \operatorname{Fin}\left(d\right),\; mu \le \operatorname{normSq}\left(v (i)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall F \in \operatorname{FiniteType}\left(\right), a \in \operatorname{FiniteFamily}\left(F\right), b \in \operatorname{FiniteFamily}\left(F\right), P \in \operatorname{Port}\left(d, q, F, a, b\right),\; \operatorname{PortEstimate}\left(P, U, v, mu\right)\right) \land \left(\frac{mu \cdot \left(d - q\right)}{\left(2 + mu\right) \cdot \left(d + 1\right)} \le \operatorname{sInf}\left(\operatorname{portErrors}\left(d, q, U\right)\right) \land \operatorname{sInf}\left(\operatorname{portErrors}\left(d, d, U\right)\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.sparse_probe_port_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual composite Kraus matrix, the original factorized trace inequality is applied with U=Rfb adjoint and W=Bfa. Encoder and decoder completeness imply that the total Hilbert--Schmidt square is d and the total trace square is at most qd. The complex coercivity estimate gives total survival loss at least mu(d-q)/(2+mu). Each of the d coordinate inputs and the additional pure input v has an ideal event of probability one, whose loss is bounded by its actual TV error. Summing these d+1 tests yields the pointwise bound. The same non-strict constant passes to the infimum. An identity port attains zero when q=d. This concerns two fixed settings; no lower bound for a larger menu is used. No optimality or novelty assertion is made.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.Port`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.PortEstimate`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.channel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.kraus`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.portErrors`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.probabilities`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.sparse_probe_port_bound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SparseProbePortBound.twoSettingError`
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity](SparseProbeCoercivity.md)
- Dependency: [D5/S3/TotalVariation/Pinsker](../../TotalVariation/Pinsker.md)
