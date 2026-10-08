# Quantitative edges of a positive and negative block spike

## Abstract

A rank-one diagonal spike in a Hermitian block matrix admits two-sided spectral-edge estimates. For a unit v, Hermitian S with Sv = 0, L >= 1 and L >= ‖K X S‖, every t >= 96L has an error at most 891L^4/t^3 at each edge, and 1782L^4/t^3 in their sum.

**Definition 1.1 (Top spectral edge).**

$$\forall (\iota : Type), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \forall (M : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), \operatorname{edgeMax}\left(M\right) = \operatorname{sSup}\left(\operatorname{spectrum}\left(\mathbb{R}, M\right)\right)$$

*Formalization.* `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.edgeMax` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real supremum of the real spectrum. Hermitian matrices on nonempty finite types have a nonempty compact real spectrum.

**Definition 1.2 (Bottom spectral edge).**

$$\forall (\iota : Type), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \forall (M : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), \operatorname{edgeMin}\left(M\right) = \operatorname{sInf}\left(\operatorname{spectrum}\left(\mathbb{R}, M\right)\right)$$

*Formalization.* `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.edgeMin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real infimum of the real spectrum, using the same real-spectrum convention as the top edge.

**Definition 1.3 (Hermitian block pencil).**

$$\forall (\iota : Type), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \forall (X : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), \forall (D : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), \operatorname{K}\left(X, D\right) = \operatorname{Matrix}.\operatorname{fromBlocks}\left(D, X, \operatorname{Matrix}.\operatorname{conjTranspose}\left(X\right), -D\right)$$

*Formalization.* `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K X D is Matrix.fromBlocks D X (Matrix.conjTranspose X) (-D); it is Hermitian when D is Hermitian.

**Lemma 1.4 (Upper spectral shift).**

$$\forall (\iota : Type), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \forall (M : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{IsHermitian}\left(M\right)) \Rightarrow (\forall (c : \mathbb{R}), (\operatorname{Matrix}.\operatorname{PosSemidef}\left(c \cdot 1 - M\right)) \Leftrightarrow (\forall (x : \mathbb{R}), (x \in \operatorname{spectrum}\left(\mathbb{R}, M\right)) \Rightarrow (x \le c)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.upper_shift_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A scalar upper spectral bound is exactly positivity of the scalar shift minus the Hermitian matrix.

**Lemma 1.5 (Action of a rank-one matrix).**

$$\forall (\iota : Type), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \forall (v : \operatorname{EuclideanSpace}\left(\mathbb{C}, \iota\right)), \forall (z : \operatorname{EuclideanSpace}\left(\mathbb{C}, \iota\right)), \operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(\operatorname{Matrix}.\operatorname{vecMulVec}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(v\right), \operatorname{star}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(v\right)\right)\right)\right)\left(z\right) = \langle v, z \rangle_{\mathbb{C}} \cdot v$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.outer_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Matrix.vecMulVec and WithLp.ofLp are the actual matrix and vector carriers. The scalar is the complex inner product.

**Lemma 1.6 (Hermitian rank-one matrix).**

$$\forall (\iota : Type), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \forall (v : \operatorname{EuclideanSpace}\left(\mathbb{C}, \iota\right)), \operatorname{Matrix}.\operatorname{IsHermitian}\left(\operatorname{Matrix}.\operatorname{vecMulVec}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(v\right), \operatorname{star}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(v\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.outer_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjugate transpose of the rank-one matrix equals the matrix itself.

**Definition 1.7 (First edge-sum coefficient).**

$$\forall (\iota : Type), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \forall (X : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), \forall (v : \operatorname{EuclideanSpace}\left(\mathbb{C}, \iota\right)), \operatorname{defect1}\left(X, v\right) = \left\lVert \operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(X\right)\right)\left(v\right) \right\rVert^{2} - \left\lVert \operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(X\right)\left(v\right) \right\rVert^{2}$$

*Formalization.* `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.defect1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first coefficient measures the squared norm difference between the adjoint action and the original action.

**Definition 1.8 (Second edge-sum coefficient).**

$$\forall (\iota : Type), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], \forall (X : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), \forall (S : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), \forall (v : \operatorname{EuclideanSpace}\left(\mathbb{C}, \iota\right)), \operatorname{defect2}\left(X, S, v\right) = \operatorname{Complex}.\operatorname{re}\left(\langle \operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(X\right)\left(v\right), \operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(S\right)\left(\operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(X\right)\left(v\right)\right) \rangle_{\mathbb{C}}\right) - \operatorname{Complex}.\operatorname{re}\left(\langle \operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(X\right)\right)\left(v\right), \operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(S\right)\left(\operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(X\right)\right)\left(v\right)\right) \rangle_{\mathbb{C}}\right)$$

*Formalization.* `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.defect2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second coefficient is the difference of the real S-pairings, with the original action first and the adjoint action second.

**Theorem 1.9 (Two-sided positive-edge enclosure).**

$$\forall (\iota : Type), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], [\operatorname{Nonempty}\left(\iota\right)], \forall (X : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), \forall (S : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), \forall (v : \operatorname{EuclideanSpace}\left(\mathbb{C}, \iota\right)), \forall (t : \mathbb{R}), \forall (L : \mathbb{R}), (\left\lVert v \right\rVert = 1) \Rightarrow ((\operatorname{Matrix}.\operatorname{IsHermitian}\left(S\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(S\right)\left(v\right) = 0) \Rightarrow ((1 \le L) \Rightarrow ((\left\lVert \operatorname{K}\left(X, S\right) \right\rVert \le L) \Rightarrow ((96 \cdot L \le t) \Rightarrow (\left|\operatorname{edgeMax}\left(\operatorname{K}\left(X, t \cdot \operatorname{Matrix}.\operatorname{vecMulVec}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(v\right), \operatorname{star}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(v\right)\right)\right) + S\right)\right) - (t + \frac{\left\lVert \operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(X\right)\right)\left(v\right) \right\rVert^{2} - \frac{\left\lVert \langle v, \operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(X\right)\left(v\right) \rangle_{\mathbb{C}} \right\rVert^{2}}{2}}{t} - \frac{\operatorname{Complex}.\operatorname{re}\left(\langle \operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(X\right)\right)\left(v\right), \operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(S\right)\left(\operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(X\right)\right)\left(v\right)\right) \rangle_{\mathbb{C}}\right)}{t^{2}})\right| \le \frac{891 \cdot L^{4}}{t^{3}}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.positive_spike_enclosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized test vector is formed from e + εr₁ + ε²r₂ at ε = 1/t. Its Rayleigh quotient supplies the lower edge bound; the complement gap and residual-energy estimate supply the upper bound. Both estimates hold at every finite t >= 96L.

**Theorem 1.10 (Two-sided edge-sum enclosure).**

$$\forall (\iota : Type), [\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], [\operatorname{Nonempty}\left(\iota\right)], \forall (X : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), \forall (S : \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), \forall (v : \operatorname{EuclideanSpace}\left(\mathbb{C}, \iota\right)), \forall (t : \mathbb{R}), \forall (L : \mathbb{R}), (\left\lVert v \right\rVert = 1) \Rightarrow ((\operatorname{Matrix}.\operatorname{IsHermitian}\left(S\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{toEuclideanCLM}\left(S\right)\left(v\right) = 0) \Rightarrow ((1 \le L) \Rightarrow ((\left\lVert \operatorname{K}\left(X, S\right) \right\rVert \le L) \Rightarrow ((96 \cdot L \le t) \Rightarrow (\left|\operatorname{edgeMax}\left(\operatorname{K}\left(X, t \cdot \operatorname{Matrix}.\operatorname{vecMulVec}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(v\right), \operatorname{star}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(v\right)\right)\right) + S\right)\right) + \operatorname{edgeMin}\left(\operatorname{K}\left(X, t \cdot \operatorname{Matrix}.\operatorname{vecMulVec}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(v\right), \operatorname{star}\left(\operatorname{WithLp}.\operatorname{ofLp}\left(v\right)\right)\right) + S\right)\right) - (\frac{\operatorname{defect1}\left(X, v\right)}{t} + \frac{\operatorname{defect2}\left(X, S, v\right)}{t^{2}})\right| \le \frac{1782 \cdot L^{4}}{t^{3}}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.edge_sum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unitary block reflection transfers the positive-edge estimate to the negative edge. Their leading ±t terms cancel. The sum has the corrected coefficient ‖X* v‖² - ‖X v‖² at order 1/t and the difference of the S-pairings at order 1/t².

## References

- Truth anchor: `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.K`
- Truth anchor: `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.defect1`
- Truth anchor: `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.defect2`
- Truth anchor: `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.edgeMax`
- Truth anchor: `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.edgeMin`
- Truth anchor: `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.edge_sum_bound`
- Truth anchor: `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.outer_action`
- Truth anchor: `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.outer_hermitian`
- Truth anchor: `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.positive_spike_enclosure`
- Truth anchor: `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.upper_shift_iff`
- Dependency: [D5/S3/Weil/GroundMode/ResidualDrivenProjectiveEnergy](../../Weil/GroundMode/ResidualDrivenProjectiveEnergy.md)
