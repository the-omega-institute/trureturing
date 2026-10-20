# OccupationPartialTransposeSpectral

## Abstract

Literal occupation operators and the exact qudit partial-estimation frontier.

**Theorem 1.1 (MatrixBlocks.blockDiagonal_psd).**

$$\forall s \in \operatorname{Type},\; \forall i \in \operatorname{Type},\; [\operatorname{Fintype}\left(s\right)] [\operatorname{DecidableEq}\left(s\right)] [\operatorname{Fintype}\left(i\right)] [\operatorname{DecidableEq}\left(i\right)] \forall B \in s \to \operatorname{Matrix}\left(i, i, \mathbb{C}\right),\; \left(\forall x \in s,\; \operatorname{Matrix}.\operatorname{PosSemidef}\left(B\left(x\right)\right)\right) \Rightarrow \operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{Matrix}.\operatorname{blockDiagonal}\left(B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockDiagonal_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A block diagonal matrix is positive semidefinite whenever every block is positive semidefinite. The blocks and their common matrix indices range over arbitrary finite types.

**Definition 1.2 (occFintype).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{occFintype}\left(N, d\right) = \operatorname{Fintype}.\operatorname{ofEquiv}\left(\operatorname{Sym}\left(\operatorname{Fin}\left(d\right), N\right), \operatorname{Sym}.\operatorname{equivNatSumOfFintype}\left(\operatorname{Fin}\left(d\right), N\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.occFintype` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The symmetric-power equivalence gives the finite occupation carrier.

**Definition 1.3 (symmetricProjector).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{symmetricProjector}\left(N, d\right) = \sum_{t: \{n: \operatorname{Fin}\left(d\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(d\right)}(n\left(i\right)) = N + 1\}}(\operatorname{Matrix}.\operatorname{vecMulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{OccupancyWordSectors}.\operatorname{sectorVector}\left(N + 1, \operatorname{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{Sym}.\operatorname{equivNatSumOfFintype}\left(\operatorname{Fin}\left(d\right), N + 1\right), t\right)\right)\right), \operatorname{star}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{OccupancyWordSectors}.\operatorname{sectorVector}\left(N + 1, \operatorname{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{Sym}.\operatorname{equivNatSumOfFintype}\left(\operatorname{Fin}\left(d\right), N + 1\right), t\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.symmetricProjector` (`✓ std3`).

*Citation.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

Equation (14), p. 3, sums the projectors onto the normalized occupation vectors on the full word space.

**Definition 1.4 (occupationEmbedding).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(N + 1\right) \to \operatorname{Fin}\left(d\right),\; \forall x \in \operatorname{Prod}\left(\{n: \operatorname{Fin}\left(d\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(d\right)}(n\left(i\right)) = N\}, \operatorname{Fin}\left(d\right)\right),\; \operatorname{occupationEmbedding}\left(N, d, w, x\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{OccupancyWordSectors}.\operatorname{sectorVector}\left(N, \operatorname{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{Sym}.\operatorname{equivNatSumOfFintype}\left(\operatorname{Fin}\left(d\right), N\right), x.1\right)\right)\right)\left(\operatorname{Fin}.\operatorname{init}\left(w\right)\right) \cdot \operatorname{if} (w\left(\operatorname{Fin}.\operatorname{last}\left(N\right)\right) = x.2) \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.occupationEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The occupation embedding sends an input occupation and output level to the normalized symmetric input vector times the output coordinate.

**Definition 1.5 (RF).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{RF}\left(N, d\right) = (\operatorname{Inv}.\operatorname{inv}\left((\operatorname{Nat}.\operatorname{choose}\left(N + 1 + d - 1, d - 1\right): \mathbb{C})\right)) \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{occupationEmbedding}\left(N, d\right)\right) \cdot \operatorname{Matrix}.\operatorname{of}\left(\operatorname{fun} (u: \operatorname{Fin}\left(N + 1\right) \to \operatorname{Fin}\left(d\right)) \mapsto \operatorname{fun} (v: \operatorname{Fin}\left(N + 1\right) \to \operatorname{Fin}\left(d\right)) \mapsto \operatorname{symmetricProjector}\left(N, d\right)\left(\operatorname{Fin}.\operatorname{snoc}\left(\operatorname{Fin}.\operatorname{init}\left(v\right), u\left(\operatorname{Fin}.\operatorname{last}\left(N\right)\right)\right), \operatorname{Fin}.\operatorname{snoc}\left(\operatorname{Fin}.\operatorname{init}\left(u\right), v\left(\operatorname{Fin}.\operatorname{last}\left(N\right)\right)\right)\right)\right) \cdot \operatorname{occupationEmbedding}\left(N, d\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.RF` (`✓ std3`).

*Citation.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

RF is R_F of Eq. (12), p. 2: normalized compression of the partially transposed full symmetric projector.

**Definition 1.6 (outputReferenceProjector).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{outputReferenceProjector}\left(N, d\right) = \operatorname{Matrix}.\operatorname{kronecker}\left((1: \operatorname{Matrix}\left(\{n: \operatorname{Fin}\left(d\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(d\right)}(n\left(i\right)) = N\}, \{n: \operatorname{Fin}\left(d\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(d\right)}(n\left(i\right)) = N\}, \mathbb{C}\right)), \operatorname{Matrix}.\operatorname{diagonal}\left(\operatorname{fun} (i: \operatorname{Fin}\left(d\right)) \mapsto \operatorname{if} (\operatorname{val}\left(i\right) = 0) \operatorname{then} (1: \mathbb{C}) \operatorname{else} 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.outputReferenceProjector` (`✓ std3`).

*Citation.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The output reference projector is the input identity tensor the projector onto output level zero, Eq. (10), p. 2.

**Definition 1.7 (RG).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{RG}\left(N, d\right) = \operatorname{Matrix}.\operatorname{kronecker}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{PartialTraceMutualInformation}.\operatorname{partialTraceRight}\left(\operatorname{RF}\left(N, d\right) \cdot \operatorname{outputReferenceProjector}\left(N, d\right)\right), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.RG` (`✓ std3`).

*Citation.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

RG is R_G of Eq. (10), p. 2: partial trace after multiplication by the reference projector, tensor the output identity.

**Definition 1.8 (A).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{A}\left(N, d\right) = ((\operatorname{Nat}.\operatorname{choose}\left(N + d - 1, d - 1\right): \mathbb{C}) \cdot (N + d: \mathbb{C})) \cdot (\operatorname{RF}\left(N, d\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The scaled A operator multiplies the corresponding fidelity operator by D(N,d)(N+d).

**Definition 1.9 (C).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{C}\left(N, d\right) = ((\operatorname{Nat}.\operatorname{choose}\left(N + d - 1, d - 1\right): \mathbb{C}) \cdot (N + d: \mathbb{C})) \cdot (\operatorname{RG}\left(N, d\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.C` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The scaled C operator multiplies the corresponding fidelity operator by D(N,d)(N+d).

**Definition 1.10 (Blocks.blockIndex).**

$$\forall K \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall m \in \{n: \operatorname{Fin}\left(d\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(d\right)}(n\left(i\right)) = K\},\; \forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{blockIndex}\left(m, i\right) = (\langle\operatorname{Function}.\operatorname{update}\left(\operatorname{val}\left(m\right), i, \operatorname{val}\left(m\right)\left(i\right) + 1\right)\rangle, i)$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

A block index pairs the occupation m plus one particle at i with output level i; the subtype proof fixes total occupation K+1.

**Theorem 1.11 (EntryFormula.dimension_pos).**

$$\forall N \in \mathbb{N},\; \forall d \in \mathbb{N},\; 1 \le d \Rightarrow 0 < \operatorname{Nat}.\operatorname{choose}\left(N + d - 1, d - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.dimension_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The binomial dimension is positive for every nonempty alphabet.

**Definition 1.12 (Scalar.blockMaximum).**

$$\forall L \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall a \in \mathbb{R},\; \operatorname{blockMaximum}\left(L, p, a\right) = p + \left(1 - p\right) \cdot a + \frac{p \cdot L + 1 - p + \operatorname{Real}.\operatorname{sqrt}\left(\left(p \cdot L - \left(1 - p\right)\right)^{2} + 4 \cdot p \cdot \left(1 - p\right) \cdot a\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockMaximum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The occupation block maximum consists of its scalar shift and the larger root of its rank-two part.

**Definition 1.13 (Scalar.topRoot).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall c \in \mathbb{R},\; \operatorname{topRoot}\left(a, b, c\right) = \frac{a + c + \operatorname{Real}.\operatorname{sqrt}\left(\left(a - c\right)^{2} + 4 \cdot b^{2}\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The larger root of a real symmetric two by two matrix depends on its diagonal entries and off-diagonal coupling.

**Definition 1.14 (Scalar.bottomRoot).**

$$\forall d \in \mathbb{R},\; \forall s \in \mathbb{R},\; \forall t \in \mathbb{R},\; \operatorname{bottomRoot}\left(d, s, t\right) = \frac{d + t - \operatorname{Real}.\operatorname{sqrt}\left(\left(d - t\right)^{2} + 4 \cdot s^{2}\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.bottomRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The smaller root of a real symmetric two by two matrix is the half-trace minus half the discriminant's square root.

**Theorem 1.15 (Scalar.topRoot_sum).**

$$\forall d \in \mathbb{R},\; \forall s \in \mathbb{R},\; \forall t \in \mathbb{R},\; \operatorname{topRoot}\left(d, s, t\right) + \operatorname{bottomRoot}\left(d, s, t\right) = d + t$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of the two roots equals the trace.

**Theorem 1.16 (Scalar.topRoot_product).**

$$\forall d \in \mathbb{R},\; \forall s \in \mathbb{R},\; \forall t \in \mathbb{R},\; \operatorname{topRoot}\left(d, s, t\right) \cdot \operatorname{bottomRoot}\left(d, s, t\right) = d \cdot t - s^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of the two roots equals the determinant.

**Theorem 1.17 (Scalar.topRoot_bounds).**

$$\forall d \in \mathbb{R},\; \forall s \in \mathbb{R},\; \forall t \in \mathbb{R},\; d \le \operatorname{topRoot}\left(d, s, t\right) \land t \le \operatorname{topRoot}\left(d, s, t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The larger root dominates both diagonal entries.

**Theorem 1.18 (Scalar.topRoot_determinant).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall c \in \mathbb{R},\; \left(\operatorname{topRoot}\left(a, b, c\right) - a\right) \cdot \left(\operatorname{topRoot}\left(a, b, c\right) - c\right) = b^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The spectral gap product equals the square of the off-diagonal coupling.

**Theorem 1.19 (Complex.distinguished_block_identity).**

$$\forall n \in \mathbb{R},\; \forall k \in \mathbb{R},\; \forall p \in \mathbb{R},\; 0 \le n \cdot k \Rightarrow \operatorname{blockMaximum}\left(n + k, p, n\right) = \operatorname{topRoot}\left(n + 1, p \cdot \operatorname{Real}.\operatorname{sqrt}\left(n \cdot k\right), n + p \cdot \left(k + 1 - n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.distinguished_block_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The block supported on the reference occupation has the stated two-dimensional root.

**Theorem 1.20 (BlockSpectral.rankOneQuadratic).**

$$\forall I \in Type,\; [\operatorname{Fintype}\left(I\right)] \forall z \in I \to \mathbb{C},\; \forall psi \in I \to \mathbb{C},\; \operatorname{dotProduct}\left(\operatorname{star}\left(z\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{Matrix}.\operatorname{vecMulVec}\left(psi, \operatorname{star}\left(psi\right)\right), z\right)\right) = (\operatorname{Complex}.\operatorname{normSq}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(z\right), psi\right)\right): \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.rankOneQuadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic form of a rank-one density matrix is the squared modulus of its overlap.

**Definition 1.21 (BlockSpectral.blockOperator).**

$$\forall I \in Type,\; [\operatorname{DecidableEq}\left(I\right)] \forall v \in I \to \mathbb{R},\; \forall i0 \in I,\; \forall a \in \mathbb{R},\; \forall p \in \mathbb{R},\; \operatorname{blockOperator}\left(v, i0, a, p\right) = ((p + \left(1 - p\right) \cdot a: \mathbb{C})) \cdot ((1: \operatorname{Matrix}\left(I, I, \mathbb{C}\right))) + ((p: \mathbb{C})) \cdot (\operatorname{Matrix}.\operatorname{vecMulVec}\left(\operatorname{fun} (i: I) \mapsto (v\left(i\right): \mathbb{C}), \operatorname{fun} (i: I) \mapsto (v\left(i\right): \mathbb{C})\right)) + ((1 - p: \mathbb{C})) \cdot (\operatorname{Matrix}.\operatorname{diagonal}\left(\operatorname{fun} (i: I) \mapsto \operatorname{if} (i = i0) \operatorname{then} 1 \operatorname{else} 0\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockOperator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

Each block is a scalar identity plus a real rank-one matrix and one coordinate projector.

**Theorem 1.22 (BlockSpectral.blockOperator_quadratic).**

$$\forall I \in Type,\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall v \in I \to \mathbb{R},\; \forall i0 \in I,\; \forall a \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall x \in I \to \mathbb{C},\; \operatorname{dotProduct}\left(\operatorname{star}\left(x\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{blockOperator}\left(v, i0, a, p\right), x\right)\right) = (\left(p + \left(1 - p\right) \cdot a\right) \cdot \sum_{i: I}(\operatorname{Complex}.\operatorname{normSq}\left(x\left(i\right)\right)) + p \cdot \operatorname{Complex}.\operatorname{normSq}\left(\sum_{i: I}((v\left(i\right): \mathbb{C}) \cdot x\left(i\right))\right) + \left(1 - p\right) \cdot \operatorname{Complex}.\operatorname{normSq}\left(x\left(i0\right)\right): \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockOperator_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The quadratic form is the sum of its norm, coherent rank-one score and reference-coordinate score.

**Definition 1.23 (BlockMatrices.blockVector).**

$$\forall K \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall m \in \{n: \operatorname{Fin}\left(d\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(d\right)}(n\left(i\right)) = K\},\; \forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{blockVector}\left(m, i\right) = \operatorname{Real}.\operatorname{sqrt}\left((\operatorname{val}\left(m\right)\left(i\right): \mathbb{R}) + 1\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The block vector has entries sqrt(m_i+1).

**Theorem 1.24 (BlockMatrices.weighted_block).**

$$\forall K \in \mathbb{N},\; \forall d \in \mathbb{N},\; 1 \le d \Rightarrow \left(\forall m \in \{n: \operatorname{Fin}\left(d\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(d\right)}(n\left(i\right)) = K\},\; \forall p \in \mathbb{R},\; \operatorname{Matrix}.\operatorname{submatrix}\left(((p: \mathbb{C})) \cdot (\operatorname{A}\left(K + 1, d\right)) + ((1 - p: \mathbb{C})) \cdot (\operatorname{C}\left(K + 1, d\right)), \operatorname{blockIndex}\left(m\right), \operatorname{blockIndex}\left(m\right)\right) = \operatorname{blockOperator}\left(\operatorname{blockVector}\left(m\right), (0: \operatorname{Fin}\left(d\right)), (\operatorname{val}\left(m\right)\left((0: \operatorname{Fin}\left(d\right))\right): \mathbb{R}) + 1, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.weighted_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

Restricting the weighted fidelity operator to an occupation block gives its rank-one-plus-coordinate form.

**Theorem 1.25 (GlobalBound.global_operator_bound).**

$$\forall K \in \mathbb{N},\; \forall k \in \mathbb{N},\; 1 \le k \Rightarrow \left(\forall p \in \mathbb{R},\; 0 \le p \Rightarrow \left(p \le 1 \Rightarrow \operatorname{Matrix}.\operatorname{PosSemidef}\left(((\operatorname{blockMaximum}\left((K: \mathbb{R}) + (k: \mathbb{R}) + 1, p, (K: \mathbb{R}) + 1\right): \mathbb{C})) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Prod}\left(\{n: \operatorname{Fin}\left(k + 1\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(k + 1\right)}(n\left(i\right)) = K + 1\}, \operatorname{Fin}\left(k + 1\right)\right), \operatorname{Prod}\left(\{n: \operatorname{Fin}\left(k + 1\right) \to \mathbb{N} // \sum_{i: \operatorname{Fin}\left(k + 1\right)}(n\left(i\right)) = K + 1\}, \operatorname{Fin}\left(k + 1\right)\right), \mathbb{C}\right))) - \operatorname{AffineMap}.\operatorname{lineMap}\left(\operatorname{C}\left(K + 1, k + 1\right), \operatorname{A}\left(K + 1, k + 1\right), (p: \mathbb{C})\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.global_operator_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ladislav Mišta Jr., Jaromír Fiurášek (2006). *Optimal partial estimation of quantum states from several copies*. DOI: [10.1103/PhysRevA.74.022316](https://doi.org/10.1103/PhysRevA.74.022316). URL: <https://arxiv.org/abs/quant-ph/0606112>.

*Commentary.*

The exhaustive occupation partition and block Rayleigh bound show that the reference block dominates the complete operator, including isolated singletons.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.A`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.C`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.RF`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.RG`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockDiagonal_psd`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockIndex`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockMaximum`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockOperator`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockOperator_quadratic`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.blockVector`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.bottomRoot`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.dimension_pos`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.distinguished_block_identity`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.global_operator_bound`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.occFintype`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.occupationEmbedding`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.outputReferenceProjector`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.rankOneQuadratic`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.symmetricProjector`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_bounds`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_determinant`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_product`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.topRoot_sum`
- Truth anchor: `D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.weighted_block`
- Dependency: [D5/S3/Quantum/Entanglement/SequentialOccupationHistory](../Entanglement/SequentialOccupationHistory.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurement/FiniteDetectionDarkSpace](FiniteDetectionDarkSpace.md)
