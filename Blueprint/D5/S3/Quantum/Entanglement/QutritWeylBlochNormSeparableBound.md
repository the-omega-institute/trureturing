# The qutrit Weyl--Bloch one-norm

## Abstract

The two-qutrit Weyl--Bloch entrywise one-norm is bounded by 25 on separable states.

**Definition 1.1 (The qutrit Weyl operators).**

$$\forall k \in \operatorname{Fin}\left(3\right),\; \forall l \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \forall c \in \operatorname{Fin}\left(3\right),\; \operatorname{W}\left(k, l, j, c\right) = \operatorname{if}\left(c = j + l, \operatorname{omega}\left(\right)^{\operatorname{val}\left(j\right) \cdot \operatorname{val}\left(k\right)}, 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.W` (`✓ std3`).

*Citation.* Tobias C. Sutter, Christopher Popp and Beatrix C. Hiesmayr (2026). *Group-Theoretic Perspective on the PPT and Realignment Criteria in the Magic Simplex for Bipartite Qutrits*. DOI: [10.1103/z7jn-4try](https://doi.org/10.1103/z7jn-4try). URL: <https://arxiv.org/abs/2508.18393v2>.

*Commentary.*

For row j and column c, W(k,l) has the cubic phase omega to j times k when c equals j+l modulo three, and is zero otherwise. omega denotes D5.S3.QuantumContext.HesseSicCertificate.omega: the complex exponential of two pi times the imaginary unit divided by three.

**Definition 1.2 (The Weyl--Bloch coefficient).**

$$\forall rho \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Complex}\left(\right)\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \forall k \in \operatorname{Fin}\left(3\right),\; \forall l \in \operatorname{Fin}\left(3\right),\; \operatorname{bloch}\left(rho, i, j, k, l\right) = \operatorname{trace}\left(rho \cdot \operatorname{conjTranspose}\left(\operatorname{kronecker}\left(\operatorname{W}\left(i, j\right), \operatorname{W}\left(k, l\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.bloch` (`✓ std3`).

*Citation.* Tobias C. Sutter, Christopher Popp and Beatrix C. Hiesmayr (2026). *Group-Theoretic Perspective on the PPT and Realignment Criteria in the Magic Simplex for Bipartite Qutrits*. DOI: [10.1103/z7jn-4try](https://doi.org/10.1103/z7jn-4try). URL: <https://arxiv.org/abs/2508.18393v2>.

*Commentary.*

The coefficient is the trace pairing with the conjugate transpose of a tensor product of two Weyl operators.

**Definition 1.3 (The entrywise one-norm).**

$$\forall rho \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Complex}\left(\right)\right),\; \operatorname{l1}\left(rho\right) = \sum_{i: \operatorname{Fin}\left(3\right)} (\sum_{j: \operatorname{Fin}\left(3\right)} (\sum_{k: \operatorname{Fin}\left(3\right)} (\sum_{l: \operatorname{Fin}\left(3\right)} (\left|\operatorname{bloch}\left(rho, i, j, k, l\right)\right|))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.l1` (`✓ std3`).

*Citation.* Tobias C. Sutter, Christopher Popp and Beatrix C. Hiesmayr (2026). *Group-Theoretic Perspective on the PPT and Realignment Criteria in the Magic Simplex for Bipartite Qutrits*. DOI: [10.1103/z7jn-4try](https://doi.org/10.1103/z7jn-4try). URL: <https://arxiv.org/abs/2508.18393v2>.

*Commentary.*

The quantity l1 is the sum of the complex norms of all 81 Weyl--Bloch coefficients.

**Definition 1.4 (Finite separable mixtures).**

$$\forall rho \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Complex}\left(\right)\right),\; (\operatorname{IsSeparable}\left(rho\right)) \Leftrightarrow (\exists n \in \operatorname{Nat}\left(\right),\; \exists p \in \operatorname{Fin}\left(n\right) \to \operatorname{Real}\left(\right),\; \exists sigma \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \operatorname{Complex}\left(\right)\right),\; \exists tau \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \operatorname{Complex}\left(\right)\right),\; (\forall t \in \operatorname{Fin}\left(n\right),\; 0 \le p\left(t\right)) \land ((\sum_{t: \operatorname{Fin}\left(n\right)} (p\left(t\right)) = 1) \land ((\forall t \in \operatorname{Fin}\left(n\right),\; (\operatorname{IsDensity}\left(sigma\left(t\right)\right)) \land (\operatorname{IsDensity}\left(tau\left(t\right)\right))) \land (rho = \sum_{t: \operatorname{Fin}\left(n\right)} (\operatorname{smul}\left(\operatorname{ofReal}\left(p\left(t\right)\right), \operatorname{kronecker}\left(sigma\left(t\right), tau\left(t\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.IsSeparable` (`✓ std3`).

*Citation.* Tobias C. Sutter, Christopher Popp and Beatrix C. Hiesmayr (2026). *Group-Theoretic Perspective on the PPT and Realignment Criteria in the Magic Simplex for Bipartite Qutrits*. DOI: [10.1103/z7jn-4try](https://doi.org/10.1103/z7jn-4try). URL: <https://arxiv.org/abs/2508.18393v2>.

*Commentary.*

A separable two-qutrit matrix is a finite convex mixture of tensor products of qutrit density matrices. IsDensity denotes D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity: positive semidefinite with trace one.

**Definition 1.5 (The sharp separable bound and an entangled violation).**

$$(\operatorname{claim}\left(\right)) \Leftrightarrow ((\forall rho \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Complex}\left(\right)\right),\; (\operatorname{IsSeparable}\left(rho\right)) \Rightarrow (\operatorname{l1}\left(rho\right) \le 25)) \land ((\exists rho \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Complex}\left(\right)\right),\; (\operatorname{IsSeparable}\left(rho\right)) \land (\operatorname{l1}\left(rho\right) = 25)) \land (\exists psi \in \operatorname{Prod}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right) \to \operatorname{Complex}\left(\right),\; (\operatorname{dotProduct}\left(\operatorname{star}\left(psi\right), psi\right) = 1) \land (25 < \operatorname{l1}\left(\operatorname{vecMulVec}\left(psi, \operatorname{star}\left(psi\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.claim` (`✓ std3`).

*Citation.* Tobias C. Sutter, Christopher Popp and Beatrix C. Hiesmayr (2026). *Group-Theoretic Perspective on the PPT and Realignment Criteria in the Magic Simplex for Bipartite Qutrits*. DOI: [10.1103/z7jn-4try](https://doi.org/10.1103/z7jn-4try). URL: <https://arxiv.org/abs/2508.18393v2>.

*Commentary.*

Every separable state has l1 at most 25, a separable state attains 25, and a normalized pure two-qutrit vector produces a Weyl--Bloch one-norm strictly above 25.

**Theorem 1.6 (The sharp separable bound).**

$$\operatorname{claim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/sutter-popp-hiesmayr-2025-qutrit-weyl-bloch-norm-bound` (proved) by `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sutter-popp-hiesmayr-2025-qutrit-weyl-bloch-norm-bound","declaration_gid":"D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For every qutrit density matrix, the squared Weyl coefficients sum to at most three. The identity coefficient is one, leaving a squared sum at most two over the other eight coefficients. Cauchy--Schwarz bounds their sum of moduli by four. The local one-norm is therefore at most five.

Weyl coefficients factor on tensor products. The product one-norm is at most twenty-five, and convexity preserves this bound for every finite separable mixture.

The vector (0,1,-1)/sqrt(2) gives a qutrit density matrix with local one-norm five; its tensor square attains twenty-five. The normalized two-qutrit vector (2|00>+|02>+|11>-|20>)/sqrt(7) has one-norm (169+2sqrt(13))/7, which exceeds twenty-five. Thus the separable threshold is sharp and its strict violation detects entanglement.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.IsSeparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.W`
- Truth anchor: `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.bloch`
- Truth anchor: `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.l1`
- Truth anchor: `D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound.result`
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/QuantumContext/HesseSicCertificate](../../QuantumContext/HesseSicCertificate.md)
