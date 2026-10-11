# A reference preserves CCZ magic beyond one third

## Abstract

The noisy CCZ gate preserves magic with a reference at depolarizing strength 1/2.

**Definition 1.1 (Binary quadratic polynomials).**

$$\forall n \in \mathbb{N},\; \forall c \in (\operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)\right)),\; \forall x \in (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)),\; \operatorname{qUpper}\left(c, x\right) = \sum_{i:\operatorname{Fin}\left(n\right)} \sum_{j:\operatorname{Fin}\left(n\right)} (if i \le j then c\left(i, j\right) \cdot x\left(i\right) \cdot x\left(j\right) else 0)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.qUpper` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

Printed page 11, Appendix D, Eq. (D2): "Any pure n-qubit stabilizer state has the form |𝒦,q,𝐛⟩ := (1/√|𝒦|) ∑_{x∈𝒦} i^{𝐛·x}(−1)^{q(x)}|x⟩, where 𝒦 ⊂ 𝔽₂ⁿ is an affine subspace, 𝐛 ∈ 𝔽₂ⁿ, q is a quadratic form, and i = √−1." Computational labels are functions Fin n -> Bool; affine coordinates are functions Fin n -> ZMod 2. The exponent of Complex.I sums integer lifts before exponentiation. Upper-triangular coefficients include diagonal terms, which represent linear monomials over ZMod 2.

**Definition 1.2 (Upper-triangular quadratic representation).**

$$\forall n \in \mathbb{N},\; \forall q \in ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right)),\; \operatorname{IsQuad}\left(q\right) \Leftrightarrow \left(\exists c \in (\operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)\right)),\; q = \operatorname{qUpper}\left(c\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.IsQuad` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

Printed page 11, Appendix D, Eq. (D2): "Any pure n-qubit stabilizer state has the form |𝒦,q,𝐛⟩ := (1/√|𝒦|) ∑_{x∈𝒦} i^{𝐛·x}(−1)^{q(x)}|x⟩, where 𝒦 ⊂ 𝔽₂ⁿ is an affine subspace, 𝐛 ∈ 𝔽₂ⁿ, q is a quadratic form, and i = √−1." Computational labels are functions Fin n -> Bool; affine coordinates are functions Fin n -> ZMod 2. The exponent of Complex.I sums integer lifts before exponentiation. Upper-triangular coefficients include diagonal terms, which represent linear monomials over ZMod 2.

**Definition 1.3 (Stabilizer normal-form amplitudes).**

$$\forall n \in \mathbb{N},\; \forall K \in \operatorname{AffineSubspace}\left(\operatorname{ZMod}\left(2\right), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right))\right),\; \forall q \in ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right)),\; \forall b \in (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)),\; \forall x \in (\operatorname{Fin}\left(n\right) \to Bool),\; let u:(\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) = (fun i : \operatorname{Fin}\left(n\right) \mapsto (if x\left(i\right) then (1:\operatorname{ZMod}\left(2\right)) else 0)); \operatorname{stabVec}\left(n, K, q, b, x\right) = (if u \in K then \operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(((K:\operatorname{Set}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right))\right)).toFinset.card:\mathbb{R})\right)\right)^{-1} \cdot \operatorname{Complex}.\operatorname{I}^{\sum_{i:\operatorname{Fin}\left(n\right)} \operatorname{val}\left(b\left(i\right)\right) \cdot \operatorname{val}\left(u\left(i\right)\right)} \cdot (-1)^{\operatorname{val}\left(q\left(u\right)\right)} else 0)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.stabVec` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

Printed page 11, Appendix D, Eq. (D2): "Any pure n-qubit stabilizer state has the form |𝒦,q,𝐛⟩ := (1/√|𝒦|) ∑_{x∈𝒦} i^{𝐛·x}(−1)^{q(x)}|x⟩, where 𝒦 ⊂ 𝔽₂ⁿ is an affine subspace, 𝐛 ∈ 𝔽₂ⁿ, q is a quadratic form, and i = √−1." Computational labels are functions Fin n -> Bool; affine coordinates are functions Fin n -> ZMod 2. The exponent of Complex.I sums integer lifts before exponentiation. Upper-triangular coefficients include diagonal terms, which represent linear monomials over ZMod 2. The affine support has cardinality (K : Set (Fin n -> ZMod 2)).toFinset.card. Its zero-support expression is defined, while pure stabilizer membership requires nonempty support.

**Definition 1.4 (Pure stabilizer density matrices).**

$$\forall n \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to Bool), (\operatorname{Fin}\left(n\right) \to Bool), \mathbb{C}\right),\; \operatorname{IsPureStab}\left(n, rho\right) \Leftrightarrow \left(\exists K \in \operatorname{AffineSubspace}\left(\operatorname{ZMod}\left(2\right), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right))\right),\; \exists q \in ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right)),\; \exists b \in (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)),\; (K:\operatorname{Set}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right))\right)).Nonempty \land \left(\operatorname{IsQuad}\left(q\right) \land rho = \operatorname{Matrix}.\operatorname{vecMulVec}\left(\operatorname{stabVec}\left(n, K, q, b\right), \operatorname{star}\left(\operatorname{stabVec}\left(n, K, q, b\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.IsPureStab` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

Printed page 11, Appendix D, Eq. (D2): "Any pure n-qubit stabilizer state has the form |𝒦,q,𝐛⟩ := (1/√|𝒦|) ∑_{x∈𝒦} i^{𝐛·x}(−1)^{q(x)}|x⟩, where 𝒦 ⊂ 𝔽₂ⁿ is an affine subspace, 𝐛 ∈ 𝔽₂ⁿ, q is a quadratic form, and i = √−1." Computational labels are functions Fin n -> Bool; affine coordinates are functions Fin n -> ZMod 2. The exponent of Complex.I sums integer lifts before exponentiation. Upper-triangular coefficients include diagonal terms, which represent linear monomials over ZMod 2. Density matrices are Matrix.vecMulVec v (star v); a nonempty affine support and a quadratic phase are required.

**Definition 1.5 (Stabilizer mixtures).**

$$\forall n \in \mathbb{N},\; \operatorname{STAB}\left(n\right) = \operatorname{convexHull}\left(\mathbb{R}, \{rho:\operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to Bool), (\operatorname{Fin}\left(n\right) \to Bool), \mathbb{C}\right) \mid \operatorname{IsPureStab}\left(n, rho\right)\}\right)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.STAB` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

Printed page 2, Section II: "Let STABₙ denote the set of all n-qubit stabilizer states, namely the convex hull of all pure stabilizer states." The convex hull is over the real scalar field.

**Definition 1.6 (Single-qubit depolarizing noise).**

$$\forall lam \in \mathbb{R},\; \forall rho \in \operatorname{Matrix}\left(Bool, Bool, \mathbb{C}\right),\; \operatorname{depol}\left(lam, rho\right) = \operatorname{Matrix}.\operatorname{reindex}\left(finTwoEquiv, finTwoEquiv, \operatorname{D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized}\left(\operatorname{LinearMap}.\operatorname{id}, lam, \operatorname{Matrix}.\operatorname{reindex}\left(\operatorname{Equiv}.\operatorname{symm}\left(finTwoEquiv\right), \operatorname{Equiv}.\operatorname{symm}\left(finTwoEquiv\right), rho\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.depol` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

Printed page 2: "As a standard noise model, we primarily consider the independent depolarizing noise 𝓔_λ^{⊗n} acting on the n-body quantum system, which leaves the qubits it acts on unchanged with probability 1−λ, and replaces them with 𝕀₂/2 with probability λ." The trace factor extends the channel to all matrices. Coordinates 0, 1 and 2 form A; coordinates 3, 4 and 5 form its reference B.

**Definition 1.7 (Depolarization at one coordinate).**

$$\forall lam \in \mathbb{R},\; \forall j \in \operatorname{Fin}\left(6\right),\; \forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(6\right) \to Bool), (\operatorname{Fin}\left(6\right) \to Bool), \mathbb{C}\right),\; \forall x \in (\operatorname{Fin}\left(6\right) \to Bool),\; \forall y \in (\operatorname{Fin}\left(6\right) \to Bool),\; \operatorname{depolAt}\left(lam, j, rho, x, y\right) = \operatorname{depol}\left(lam, (fun u : Bool \mapsto (fun v : Bool \mapsto rho\left(\operatorname{Function}.\operatorname{update}\left(x, j, u\right), \operatorname{Function}.\operatorname{update}\left(y, j, v\right)\right))), x\left(j\right), y\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.depolAt` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

Printed page 2: "As a standard noise model, we primarily consider the independent depolarizing noise 𝓔_λ^{⊗n} acting on the n-body quantum system, which leaves the qubits it acts on unchanged with probability 1−λ, and replaces them with 𝕀₂/2 with probability λ." The trace factor extends the channel to all matrices. Coordinates 0, 1 and 2 form A; coordinates 3, 4 and 5 form its reference B. For each fixed pair of outside labels, apply depol to the two-by-two block obtained with Function.update.

**Definition 1.8 (Noise on the three system qubits).**

$$\forall lam \in \mathbb{R},\; \forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(6\right) \to Bool), (\operatorname{Fin}\left(6\right) \to Bool), \mathbb{C}\right),\; \operatorname{depolA}\left(lam, rho\right) = \operatorname{depolAt}\left(lam, 2, \operatorname{depolAt}\left(lam, 1, \operatorname{depolAt}\left(lam, 0, rho\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.depolA` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

Printed page 2: "As a standard noise model, we primarily consider the independent depolarizing noise 𝓔_λ^{⊗n} acting on the n-body quantum system, which leaves the qubits it acts on unchanged with probability 1−λ, and replaces them with 𝕀₂/2 with probability λ." The trace factor extends the channel to all matrices. Coordinates 0, 1 and 2 form A; coordinates 3, 4 and 5 form its reference B.

**Definition 1.9 (The controlled-controlled-Z gate).**

$$CCZ = \operatorname{Matrix}.\operatorname{diagonal}\left((fun x : (\operatorname{Fin}\left(3\right) \to Bool) \mapsto (if \operatorname{Bool}.\operatorname{and}\left(\operatorname{Bool}.\operatorname{and}\left(x\left(0\right), x\left(1\right)\right), x\left(2\right)\right) then -1 else 1))\right)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.CCZ` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

Printed page 2: "Let Cⁿ⁻¹Z = diag(1, · · · , 1, −1) denote the multi-controlled-Z gate on n-qubits, with C⁰Z = Z." At n = 3, the computational-basis diagonal is -1 at 111 and 1 at every other label; Bool.and is the Boolean conjunction used by the diagonal entries.

**Definition 1.10 (CCZ with an untouched reference).**

$$CCZA = \operatorname{Matrix}.\operatorname{diagonal}\left((fun x : (\operatorname{Fin}\left(6\right) \to Bool) \mapsto \operatorname{CCZ}\left((fun i : \operatorname{Fin}\left(3\right) \mapsto x\left(\operatorname{Fin}.\operatorname{castAdd}\left(3, i\right)\right)), (fun i : \operatorname{Fin}\left(3\right) \mapsto x\left(\operatorname{Fin}.\operatorname{castAdd}\left(3, i\right)\right))\right))\right)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.CCZA` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

CCZA is the diagonal six-qubit matrix obtained from CCZ on the first three bits. Fin.castAdd 3 selects A; the last three coordinates form B.

**Definition 1.11 (Gate followed by local noise).**

$$\forall lam \in \mathbb{R},\; \forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(6\right) \to Bool), (\operatorname{Fin}\left(6\right) \to Bool), \mathbb{C}\right),\; \operatorname{chan}\left(lam, rho\right) = \operatorname{depolA}\left(lam, CCZA \cdot rho \cdot CCZA\right)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.chan` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

Printed page 2: "As a standard noise model, we primarily consider the independent depolarizing noise 𝓔_λ^{⊗n} acting on the n-body quantum system, which leaves the qubits it acts on unchanged with probability 1−λ, and replaces them with 𝕀₂/2 with probability λ." The trace factor extends the channel to all matrices. Coordinates 0, 1 and 2 form A; coordinates 3, 4 and 5 form its reference B. CCZ is real and diagonal, so the displayed two-sided multiplication is its unitary conjugation. The reference is untouched.

**Definition 1.12 (The conjectured magic-capacity threshold).**

$$claim \Leftrightarrow \left(\left(\forall lam \in \mathbb{R},\; lam \in \operatorname{Set}.\operatorname{Icc}\left(\frac{1}{3}, 1\right) \Rightarrow \left(\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(6\right) \to Bool), (\operatorname{Fin}\left(6\right) \to Bool), \mathbb{C}\right),\; \operatorname{IsPureStab}\left(6, rho\right) \Rightarrow \operatorname{chan}\left(lam, rho\right) \in \operatorname{STAB}\left(6\right)\right)\right) \land \left(\forall lam \in \mathbb{R},\; lam \in \operatorname{Set}.\operatorname{Ico}\left(0, \frac{1}{3}\right) \Rightarrow \left(\exists rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(6\right) \to Bool), (\operatorname{Fin}\left(6\right) \to Bool), \mathbb{C}\right),\; \operatorname{IsPureStab}\left(6, rho\right) \land \left(\neg \operatorname{chan}\left(lam, rho\right) \in \operatorname{STAB}\left(6\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.claim` (`✓ std3`).

*Citation.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

Printed page 6, Section VII: "We conjecture that the magic capacity threshold for CCZ under local depolarizing noise is 1/3." Printed page 3: "Define the magic capacity [31] of the Cⁿ⁻¹Z gate as 𝒞(Cⁿ⁻¹Z)=max_{|s⟩}𝓡(Cⁿ⁻¹Z⊗𝕀_{2ⁿ}|s⟩), where the maximum is taken over all 2n-qubit pure stabilizer states |s⟩." Page 2 gives faithfulness: RoM equals 1 exactly on STAB. The first conjunct encodes capacity one for every noise strength in [1/3,1]; the second encodes capacity greater than one below 1/3. Inputs range over pure stabilizer density matrices on six qubits. Only A is noisy, in the noise-after-gate order.

**Theorem 1.13 (The one-third capacity conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.result` (`✓ std3`). ∎

*Resolves.* `Problems/wei-liu-2024-ccz-magic-capacity-threshold` (refuted) by `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wei-liu-2024-ccz-magic-capacity-threshold","declaration_gid":"D5/S3/Quantum/Information/CCZMagicCapacityThreshold.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fuchuan Wei and Zi-Wen Liu (2024). *Noise robustness and threshold of many-body quantum magic*. URL: <https://arxiv.org/abs/2410.21215v1>.

*Commentary.*

At lambda = 1/2, use the pure stabilizer input Omega = 8^(-1/2) sum_x |x,x>. Restricting any stabilizer amplitude to the diagonal produces either zero or a scalar multiple of a three-qubit stabilizer normal form. The binary phase vector becomes b_A + b_B, and the quadratic phase acquires the carry term sum_i b_A(i)b_B(i)x_i^2. The squared overlap with CCZ|+++> is at most 9/16: proper affine supports have at most four points, and the full-support bound follows from the exact finite phase sum. Consequently the separating matrix has nonnegative trace pairing with every stabilizer mixture. Its trace pairing with chan (1/2) applied to the Omega density matrix is exactly -7/1024, contradicting the first conjunct of claim. This proves the refutation at one half; it does not determine the exact threshold.

## References

- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.CCZ`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.CCZA`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.IsPureStab`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.IsQuad`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.STAB`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.chan`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.claim`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.depol`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.depolA`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.depolAt`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.qUpper`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.result`
- Truth anchor: `D5/S3/Quantum/Information/CCZMagicCapacityThreshold.stabVec`
- Dependency: [D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound](../QuantumChannels/TracePreservingEigenvalueBound.md)
