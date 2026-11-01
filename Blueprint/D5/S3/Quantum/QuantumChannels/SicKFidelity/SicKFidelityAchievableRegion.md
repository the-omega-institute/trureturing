# Achievable (k-fidelity, process fidelity) regions and single-fidelity non-identifiability

## Abstract

Exact planar regions of pairs (F_k(Lambda), F(Lambda)) realized by n-qubit completely positive trace-preserving maps across k = 0, 1 <= k <= n - 1, and k >= n, closed-form upper and lower process-fidelity envelopes at prescribed 0-fidelity, unimodal maximizer analysis of the binomial weight kernel, and non-identifiability of F(Lambda) from any single F_k(Lambda) for n >= 2 and k <= n - 1.

**Definition 1.1 (Achievable (k-fidelity, process fidelity) region).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \operatorname{achievableRegion}\left(n, k, r\right) = \left\{p \in \left(\mathbb{R} \times \mathbb{R}\right) \mid \exists L \in \operatorname{QubitMap}\left(n\right),\; \operatorname{IsCompletelyPositive}\left(L\right) \land \left(\operatorname{IsTracePreserving}\left(L\right) \land p = \left(\operatorname{realKFidelity}\left(r, k, L\right), \operatorname{realProcessFidelity}\left(L\right)\right)\right)\right\}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For n qubits and truncation order k, achievableRegion(n, k, rho) is the subset of R^2 consisting of all pairs (realKFidelity(rho, k, Lambda), realProcessFidelity(Lambda)) as Lambda ranges over completely positive trace-preserving n-qubit maps.

**Definition 1.2 (Unsigned Pauli-weight binomial kernel).**

$$\forall k \in \mathbb{N},\; \forall w \in \mathbb{N},\; \operatorname{tailCoeff}\left(k, w\right) = \left(3^{-1}\right)^{w} \cdot \operatorname{choose}\left(w - 1, k\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.tailCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines g_k(w) = 3^{-w} C(w - 1, k) for natural numbers k and w.

**Definition 1.3 (Maximizing Hamming weight w*).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{optWeight}\left(n, k\right) = \operatorname{min}\left(n, \left\lfloor\frac{3 \cdot k}{2}\right\rfloor + 1\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.optWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines w*(n, k) = min(n, floor(3 k / 2) + 1).

**Definition 1.4 (Signed extremal horizontal vertex abscissa).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{extremalAbscissa}\left(n, k\right) = \left(-1\right)^{k} \cdot \operatorname{tailCoeff}\left(k, \operatorname{optWeight}\left(n, k\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.extremalAbscissa` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

Defines x_k(n) = (-1)^k g_k(w*(n, k)), the nonzero horizontal coordinate among vertices on the axis F = 0 for 1 <= k <= n - 1.

**Theorem 1.5 (Exact 0-fidelity achievable triangle, single-qubit segment, and extremal envelopes).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSICProjector}\left(r\left(i\right)\right)\right) \Rightarrow \left(\operatorname{achievableRegion}\left(n, 0, r\right) = \operatorname{convexHull}\left(\mathbb{R}, \left\{\left(1, 1\right), \left(\left(3^{-1}\right)^{n}, 0\right), \left(3^{-1}, 0\right)\right\}\right) \land \left(\left(2 \le n \Rightarrow \left(\forall p \in \left(\mathbb{R} \times \mathbb{R}\right),\; p \in \operatorname{achievableRegion}\left(n, 0, r\right) \Leftrightarrow \left(0 \le \operatorname{snd}\left(p\right) \land \left(1 - \frac{3}{2} \cdot \left(1 - \operatorname{fst}\left(p\right)\right) \le \operatorname{snd}\left(p\right) \land \operatorname{snd}\left(p\right) \le \frac{\operatorname{fst}\left(p\right) - \left(3^{-1}\right)^{n}}{1 - \left(3^{-1}\right)^{n}}\right)\right)\right)\right) \land \left(\left(n = 1 \Rightarrow \left(\forall p \in \left(\mathbb{R} \times \mathbb{R}\right),\; p \in \operatorname{achievableRegion}\left(n, 0, r\right) \Leftrightarrow \left(\operatorname{snd}\left(p\right) = 1 - \frac{3}{2} \cdot \left(1 - \operatorname{fst}\left(p\right)\right) \land \left(3^{-1} \le \operatorname{fst}\left(p\right) \land \operatorname{fst}\left(p\right) \le 1\right)\right)\right)\right) \land \left(\left(\forall t \in \mathbb{R},\; 0 \le t \Rightarrow \left(t \le 1 \Rightarrow \left(\operatorname{IsCompletelyPositive}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = 0, t, \operatorname{ite}\left(g = \left(\lambda i \in \operatorname{Fin}\left(n\right) \mapsto 3\right), 1 - t, 0\right)\right)\right)\right)\right) \land \left(\operatorname{IsTracePreserving}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = 0, t, \operatorname{ite}\left(g = \left(\lambda i \in \operatorname{Fin}\left(n\right) \mapsto 3\right), 1 - t, 0\right)\right)\right)\right)\right) \land \left(\operatorname{realKFidelity}\left(r, 0, \operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = 0, t, \operatorname{ite}\left(g = \left(\lambda i \in \operatorname{Fin}\left(n\right) \mapsto 3\right), 1 - t, 0\right)\right)\right)\right)\right), \operatorname{realProcessFidelity}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = 0, t, \operatorname{ite}\left(g = \left(\lambda i \in \operatorname{Fin}\left(n\right) \mapsto 3\right), 1 - t, 0\right)\right)\right)\right)\right)\right) = \left(t + \left(1 - t\right) \cdot \left(3^{-1}\right)^{n}, t\right)\right)\right)\right)\right) \land \left(\left(\forall b \in \operatorname{PauliLabel}\left(n\right),\; \operatorname{hammingWeight}\left(b\right) = 1 \Rightarrow \left(\forall t \in \mathbb{R},\; 0 \le t \Rightarrow \left(t \le 1 \Rightarrow \left(\operatorname{IsCompletelyPositive}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = 0, t, \operatorname{ite}\left(g = b, 1 - t, 0\right)\right)\right)\right)\right) \land \left(\operatorname{IsTracePreserving}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = 0, t, \operatorname{ite}\left(g = b, 1 - t, 0\right)\right)\right)\right)\right) \land \left(\operatorname{realKFidelity}\left(r, 0, \operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = 0, t, \operatorname{ite}\left(g = b, 1 - t, 0\right)\right)\right)\right)\right), \operatorname{realProcessFidelity}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = 0, t, \operatorname{ite}\left(g = b, 1 - t, 0\right)\right)\right)\right)\right)\right) = \left(t + \left(1 - t\right) \cdot 3^{-1}, t\right)\right)\right)\right)\right)\right) \land \left(2 \le n \Rightarrow \left(\forall x \in \mathbb{R},\; \left(3^{-1}\right)^{n} \le x \Rightarrow \left(x \le 1 \Rightarrow \left(\operatorname{IsGreatest}\left(\left\{y \in \mathbb{R} \mid \left(x, y\right) \in \operatorname{achievableRegion}\left(n, 0, r\right)\right\}, \frac{x - \left(3^{-1}\right)^{n}}{1 - \left(3^{-1}\right)^{n}}\right) \land \left(\left(x < 1 \Rightarrow \frac{x - \left(3^{-1}\right)^{n}}{1 - \left(3^{-1}\right)^{n}} < x\right) \land \left(x - \frac{x - \left(3^{-1}\right)^{n}}{1 - \left(3^{-1}\right)^{n}} = \frac{\left(1 - x\right) \cdot \left(3^{-1}\right)^{n}}{1 - \left(3^{-1}\right)^{n}} \land \operatorname{IsLeast}\left(\left\{y \in \mathbb{R} \mid \left(x, y\right) \in \operatorname{achievableRegion}\left(n, 0, r\right)\right\}, \operatorname{max}\left(0, 1 - \frac{3}{2} \cdot \left(1 - x\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion_zero_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For every n >= 1, R_0 equals the closed convex hull of (1, 1), (3^{-n}, 0), and (1 / 3, 0). When n >= 2, (F_0, F) belongs to R_0 if and only if F >= 0 and 1 - (3 / 2)(1 - F_0) <= F <= (F_0 - 3^{-n}) / (1 - 3^{-n}), with the upper edge attained by mixtures t id + (1 - t) Z^{tensor n} (.) Z^{tensor n} and the lower edge attained by weight-1 Pauli mixtures; at every prescribed F_0 in [3^{-n}, 1], the maximum of F is (F_0 - 3^{-n}) / (1 - 3^{-n}) (strictly below F_0 for F_0 < 1 with gap (1 - F_0) 3^{-n} / (1 - 3^{-n})) and the minimum of F is max(0, 1 - (3 / 2)(1 - F_0)). When n = 1, R_0 collapses to the line segment F = 1 - (3 / 2)(1 - F_0) over 1 / 3 <= F_0 <= 1.

**Theorem 1.6 (Intermediate achievable triangles, unimodal maximizers, and high-order diagonal segment).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSICProjector}\left(r\left(i\right)\right)\right) \Rightarrow \left(\left(\left(1 \le k \land k + 1 \le n\right) \Rightarrow \left(\left(0 < \operatorname{tailCoeff}\left(k, \operatorname{optWeight}\left(n, k\right)\right) \land \operatorname{tailCoeff}\left(k, \operatorname{optWeight}\left(n, k\right)\right) < 1\right) \land \left(\left(\forall w \in \operatorname{Icc}\left(1, n\right),\; \operatorname{tailCoeff}\left(k, w\right) \le \operatorname{tailCoeff}\left(k, \operatorname{optWeight}\left(n, k\right)\right)\right) \land \left(\left\{w \in \operatorname{Icc}\left(1, n\right) \mid \operatorname{tailCoeff}\left(k, w\right) = \operatorname{tailCoeff}\left(k, \operatorname{optWeight}\left(n, k\right)\right)\right\} = \operatorname{ite}\left(\operatorname{Even}\left(k\right) \land \left\lfloor\frac{3 \cdot k}{2}\right\rfloor + 1 \le n, \left\{\left\lfloor\frac{3 \cdot k}{2}\right\rfloor, \left\lfloor\frac{3 \cdot k}{2}\right\rfloor + 1\right\}, \left\{\operatorname{optWeight}\left(n, k\right)\right\}\right) \land \left(\operatorname{achievableRegion}\left(n, k, r\right) = \operatorname{convexHull}\left(\mathbb{R}, \left\{\left(1, 1\right), \left(0, 0\right), \left(\operatorname{extremalAbscissa}\left(n, k\right), 0\right)\right\}\right) \land \left(\left(\operatorname{Odd}\left(k\right) \Rightarrow \left(\forall p \in \left(\mathbb{R} \times \mathbb{R}\right),\; p \in \operatorname{achievableRegion}\left(n, k, r\right) \Leftrightarrow \left(0 \le \operatorname{snd}\left(p\right) \land \left(\operatorname{fst}\left(p\right) \le \operatorname{snd}\left(p\right) \land \operatorname{snd}\left(p\right) \le \frac{\operatorname{fst}\left(p\right) - \operatorname{extremalAbscissa}\left(n, k\right)}{1 - \operatorname{extremalAbscissa}\left(n, k\right)}\right)\right)\right)\right) \land \left(\left(\operatorname{Even}\left(k\right) \Rightarrow \left(\forall p \in \left(\mathbb{R} \times \mathbb{R}\right),\; p \in \operatorname{achievableRegion}\left(n, k, r\right) \Leftrightarrow \left(0 \le \operatorname{snd}\left(p\right) \land \left(\frac{\operatorname{fst}\left(p\right) - \operatorname{extremalAbscissa}\left(n, k\right)}{1 - \operatorname{extremalAbscissa}\left(n, k\right)} \le \operatorname{snd}\left(p\right) \land \operatorname{snd}\left(p\right) \le \operatorname{fst}\left(p\right)\right)\right)\right)\right) \land \left(\left(\forall p \in \left(\mathbb{R} \times \mathbb{R}\right),\; p \in \operatorname{achievableRegion}\left(n, k, r\right) \Rightarrow \left(0 \le \operatorname{snd}\left(p\right) \land \operatorname{snd}\left(p\right) \le 1\right)\right) \land \left(\left(\operatorname{IsCompletelyPositive}\left(\operatorname{id}\right) \land \left(\operatorname{IsTracePreserving}\left(\operatorname{id}\right) \land \left(\operatorname{realKFidelity}\left(r, k, \operatorname{id}\right), \operatorname{realProcessFidelity}\left(\operatorname{id}\right)\right) = \left(1, 1\right)\right)\right) \land \left(\left(\forall b \in \operatorname{PauliLabel}\left(n\right),\; \operatorname{hammingWeight}\left(b\right) = 1 \Rightarrow \left(\operatorname{IsCompletelyPositive}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = b, 1, 0\right)\right)\right)\right) \land \left(\operatorname{IsTracePreserving}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = b, 1, 0\right)\right)\right)\right) \land \left(\operatorname{realKFidelity}\left(r, k, \operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = b, 1, 0\right)\right)\right)\right), \operatorname{realProcessFidelity}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = b, 1, 0\right)\right)\right)\right)\right) = \left(0, 0\right)\right)\right)\right) \land \left(\left(\exists b \in \operatorname{PauliLabel}\left(n\right),\; \operatorname{hammingWeight}\left(b\right) = \operatorname{optWeight}\left(n, k\right)\right) \land \left(\forall b \in \operatorname{PauliLabel}\left(n\right),\; \operatorname{hammingWeight}\left(b\right) = \operatorname{optWeight}\left(n, k\right) \Rightarrow \left(\operatorname{IsCompletelyPositive}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = b, 1, 0\right)\right)\right)\right) \land \left(\operatorname{IsTracePreserving}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = b, 1, 0\right)\right)\right)\right) \land \left(\operatorname{realKFidelity}\left(r, k, \operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = b, 1, 0\right)\right)\right)\right), \operatorname{realProcessFidelity}\left(\operatorname{pauliChannel}\left(\left(\lambda g \in \operatorname{PauliLabel}\left(n\right) \mapsto \operatorname{ite}\left(g = b, 1, 0\right)\right)\right)\right)\right) = \left(\operatorname{extremalAbscissa}\left(n, k\right), 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\left(1 \le n \land n \le k\right) \Rightarrow \left(\operatorname{achievableRegion}\left(n, k, r\right) = \operatorname{convexHull}\left(\mathbb{R}, \left\{\left(0, 0\right), \left(1, 1\right)\right\}\right) \land \operatorname{achievableRegion}\left(n, k, r\right) = \left\{p \in \left(\mathbb{R} \times \mathbb{R}\right) \mid \operatorname{fst}\left(p\right) = \operatorname{snd}\left(p\right) \land \left(0 \le \operatorname{snd}\left(p\right) \land \operatorname{snd}\left(p\right) \le 1\right)\right\}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion_intermediate_and_high_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For 1 <= k <= n - 1, the kernel g_k(w) = 3^{-w} C(w - 1, k) satisfies 0 < g_k(w*) < 1 and attains its maximum over 1 <= w <= n uniquely at w* = min(n, floor(3 k / 2) + 1), except when k is even and 3 k / 2 + 1 <= n where the maximum is attained at {3 k / 2, 3 k / 2 + 1}; the achievable region R_k is the closed triangle conv{(1, 1), (0, 0), (x_k, 0)}, cut out by F >= 0 and F_k <= F <= (F_k - x_k) / (1 - x_k) for odd k and by F >= 0 and (F_k - x_k) / (1 - x_k) <= F <= F_k for even k (implying 0 <= F <= 1), with vertices attained by the identity map, weight-1 Pauli conjugation, and weight-w* Pauli conjugation. For k >= n >= 1, R_k is the diagonal segment {(F_k, F) | F_k = F and 0 <= F <= 1}.

**Theorem 1.7 (Non-identifiability of process fidelity from a single lower-order k-fidelity).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; 2 \le n \Rightarrow \left(k + 1 \le n \Rightarrow \left(\forall r \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \operatorname{QubitMatrix}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSICProjector}\left(r\left(i\right)\right)\right) \Rightarrow \left(\exists L \in \operatorname{QubitMap}\left(n\right),\; \exists M \in \operatorname{QubitMap}\left(n\right),\; \operatorname{IsCompletelyPositive}\left(L\right) \land \left(\operatorname{IsTracePreserving}\left(L\right) \land \left(\operatorname{IsCompletelyPositive}\left(M\right) \land \left(\operatorname{IsTracePreserving}\left(M\right) \land \left(\operatorname{realKFidelity}\left(r, k, L\right) = \operatorname{realKFidelity}\left(r, k, M\right) \land \left(\operatorname{realProcessFidelity}\left(L\right) = 0 \land \left(0 < \operatorname{realProcessFidelity}\left(M\right) \land \operatorname{realProcessFidelity}\left(L\right) \ne \operatorname{realProcessFidelity}\left(M\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.kFidelity_non_identifiability_of_processFidelity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For every n >= 2 and every 0 <= k <= n - 1, there exist two n-qubit completely positive trace-preserving maps with the same k-fidelity F_k, one having zero entanglement process fidelity and one having strictly positive entanglement process fidelity (and hence distinct process fidelities).

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion_intermediate_and_high_characterization`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.achievableRegion_zero_characterization`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.extremalAbscissa`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.kFidelity_non_identifiability_of_processFidelity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.optWeight`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.tailCoeff`
- Dependency: [D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight](SicKFidelityPauliWeight.md)
