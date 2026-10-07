# All gate orderings of an open-boundary transfer-matrix circuit

## Abstract

Every ordering that uses each boundary gate and each nearest-neighbour gate once is a nonzero scalar multiple of a double-row transfer matrix with signed inhomogeneities. Mutual commutation of the transfer matrices implies commutation of the circuit with that family.

**Definition 1.1 (One-site embedding).**

$$\forall Sites \in Type,\; \forall Local \in Type,\;  [\operatorname{DecidableEq}\left(Sites\right)] [\operatorname{Fintype}\left(Local\right)]  \forall i \in Sites,\; \forall B \in \operatorname{Matrix}\left(Local, Local, \mathbb{C}\right),\; \forall f \in \left(Sites \to Local\right) \to \mathbb{C},\; \forall x \in Sites \to Local,\; \operatorname{oneOp}\left(i, B\right)\left(f, x\right) = \sum_{p \in Local} B\left(x\left(i\right), p\right) \cdot f\left(\operatorname{update}\left(x, i, p\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.oneOp` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The matrix acts at site i. The update operation replaces only that coordinate of the configuration; the sum ranges over every local basis label.

**Definition 1.2 (Oriented two-site embedding).**

$$\forall Sites \in Type,\; \forall Local \in Type,\;  [\operatorname{DecidableEq}\left(Sites\right)] [\operatorname{Fintype}\left(Local\right)]  \forall i \in Sites,\; \forall j \in Sites,\; \forall R \in \operatorname{Matrix}\left(Local \times Local, Local \times Local, \mathbb{C}\right),\; \forall f \in \left(Sites \to Local\right) \to \mathbb{C},\; \forall x \in Sites \to Local,\; \operatorname{twoOp}\left(i, j, R\right)\left(f, x\right) = \sum_{p \in Local \times Local} R\left((x\left(i\right), x\left(j\right)), p\right) \cdot f\left(\operatorname{update}\left(\operatorname{update}\left(x, i, \operatorname{fst}\left(p\right)\right), j, \operatorname{snd}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.twoOp` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The first and second components of p replace sites i and j respectively. All other coordinates remain fixed.

**Definition 1.3 (The checked matrix).**

$$\forall Local \in Type,\; [\operatorname{Fintype}\left(Local\right)] [\operatorname{DecidableEq}\left(Local\right)] \forall R \in \operatorname{Matrix}\left(Local \times Local, Local \times Local, \mathbb{C}\right),\; \operatorname{checkedR}\left(R\right) = \operatorname{PEquiv}.\operatorname{toMatrix}\left(\operatorname{Equiv}.\operatorname{toPEquiv}\left(\operatorname{Equiv}.\operatorname{prodComm}\left(Local, Local\right)\right)\right) \cdot R$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.checkedR` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The source defines the checked matrix as P R. Here P is PEquiv.toMatrix applied to Equiv.toPEquiv of Equiv.prodComm, whose entry at (x,y) is one exactly when swapping the two components of x gives y.

**Definition 1.4 (Trace over the auxiliary factor).**

$$\forall Sites \in Type,\; \forall Local \in Type,\; [\operatorname{Fintype}\left(Sites\right)] [\operatorname{DecidableEq}\left(Sites\right)] [\operatorname{Fintype}\left(Local\right)] [\operatorname{DecidableEq}\left(Local\right)] \forall F \in \operatorname{End}\left(\mathbb{C}, \left(\operatorname{Option}\left(Sites\right) \to Local\right) \to \mathbb{C}\right),\; \operatorname{partialTrace}\left(F\right) = (\operatorname{LinearMap}.\operatorname{toMatrixAlgEquiv}').\operatorname{symm}\left(\operatorname{partialTraceLeft}\left(\operatorname{Matrix}.\operatorname{reindex}\left(\operatorname{Equiv}.\operatorname{piOptionEquivProd}\left(Sites, Local\right), \operatorname{Equiv}.\operatorname{piOptionEquivProd}\left(Sites, Local\right), \operatorname{LinearMap}.\operatorname{toMatrixAlgEquiv}'\left(F\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.partialTrace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The auxiliary site is none, and physical sites are some i. Equiv.piOptionEquivProd identifies a configuration on Option Sites with its auxiliary label and physical configuration. LinearMap.toMatrixAlgEquiv' is the forward map over the complex numbers; its .symm is the inverse map. Matrix.reindex uses this configuration equivalence for both indices. partialTraceLeft is the existing matrix trace over the first factor, without normalization.

**Definition 1.5 (The left boundary gate).**

$$\forall Sites \in Type,\; \forall Local \in Type,\; [\operatorname{Fintype}\left(Sites\right)] [\operatorname{DecidableEq}\left(Sites\right)] [\operatorname{Fintype}\left(Local\right)] [\operatorname{DecidableEq}\left(Local\right)] \forall KL \in \operatorname{Matrix}\left(Local, Local, \mathbb{C}\right),\; \forall p \in Sites,\; \forall C \in \operatorname{Matrix}\left(Local \times Local, Local \times Local, \mathbb{C}\right),\; \operatorname{leftGate}\left(KL, p, C\right) = \operatorname{partialTrace}\left(\operatorname{oneOp}\left(none, KL\right) \cdot \operatorname{twoOp}\left(\operatorname{some}\left(p\right), none, \operatorname{checkedR}\left(C\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.leftGate` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The source's left gate is the auxiliary trace of K-a-L times P-a-p R-p-a. Embedding checkedR on the oriented pair (p,a) gives precisely that product because the swap is symmetric.

**Definition 1.6 (The explicit double-row transfer matrix).**

$$\forall N \in \mathbb{N},\; \forall D \in \mathbb{N},\; \forall R \in \mathbb{C} \to \left(\mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right) \times \operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right) \times \operatorname{Fin}\left(D\right), \mathbb{C}\right)\right),\; \forall KR \in \mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right), \mathbb{C}\right),\; \forall KL \in \mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right), \mathbb{C}\right),\; \forall u \in \mathbb{C},\; \forall theta \in \operatorname{Fin}\left(N + 1\right) \to \mathbb{C},\; \operatorname{transfer}\left(N, D, R, KR, KL, u, theta\right) = \operatorname{partialTrace}\left(\operatorname{oneOp}\left(none, KL\left(u\right)\right) \cdot \prod_{i \in \operatorname{reverse}\left(\operatorname{range}\left(N + 1\right)\right)} (\operatorname{twoOp}\left(none, \operatorname{some}\left(\operatorname{ofNat}\left(N + 1, i\right)\right), R\left(u, theta\left(\operatorname{ofNat}\left(N + 1, i\right)\right)\right)\right)) \cdot \operatorname{oneOp}\left(none, KR\left(u\right)\right) \cdot \prod_{i \in \operatorname{range}\left(N + 1\right)} (\operatorname{twoOp}\left(\operatorname{some}\left(\operatorname{ofNat}\left(N + 1, i\right)\right), none, R\left(theta\left(\operatorname{ofNat}\left(N + 1, i\right)\right), -u\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.transfer` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The first product is ordered N down to 0 and the second 0 up to N. The source's chain length is N + 1, and its physical site i + 1 is encoded by i. The products are the explicit R-matrix products, and no inverse monodromy is introduced.

**Definition 1.7 (The bulk and boundary gate family).**

$$\forall N \in \mathbb{N},\; \forall D \in \mathbb{N},\; \forall R \in \mathbb{C} \to \left(\mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right) \times \operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right) \times \operatorname{Fin}\left(D\right), \mathbb{C}\right)\right),\; \forall KR \in \mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right), \mathbb{C}\right),\; \forall KL \in \mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right), \mathbb{C}\right),\; \forall kappa \in \mathbb{C},\; (\operatorname{gate}\left(N, D, R, KR, KL, kappa, 0\right) = \operatorname{oneOp}\left(0, KR\left(kappa\right)\right)) \land (\forall i \in \mathbb{N},\; \operatorname{gate}\left(N, D, R, KR, KL, kappa, i + 1\right) = \operatorname{ite}\left(i = N, \operatorname{leftGate}\left(KL\left(kappa\right), \operatorname{last}\left(N\right), R\left(kappa, -kappa\right)\right), \operatorname{twoOp}\left(\operatorname{ofNat}\left(N + 1, i\right), \operatorname{ofNat}\left(N + 1, i + 1\right), \operatorname{checkedR}\left(R\left(kappa, -kappa\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.gate` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The gate at label zero is the right boundary matrix at physical site zero. Labels 1 through N carry the checked bulk matrix, and label N + 1 is the auxiliary-traced left boundary matrix. Fin.ofNat supplies the site indices; on 0 through N these have their ordinary values.

**Definition 1.8 (A once-per-label ordering).**

$$\forall N \in \mathbb{N},\; \forall D \in \mathbb{N},\; \forall R \in \mathbb{C} \to \left(\mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right) \times \operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right) \times \operatorname{Fin}\left(D\right), \mathbb{C}\right)\right),\; \forall KR \in \mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right), \mathbb{C}\right),\; \forall KL \in \mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right), \mathbb{C}\right),\; \forall kappa \in \mathbb{C},\; \forall pi \in \operatorname{Perm}\left(\operatorname{Fin}\left(N + 2\right)\right),\; \operatorname{circuitProduct}\left(N, D, R, KR, KL, kappa, pi\right) = \prod_{i \in \operatorname{Fin}\left(N + 2\right)} (\operatorname{gate}\left(N, D, R, KR, KL, kappa, \operatorname{val}\left(pi\left(i\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.circuitProduct` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

The permutation runs over all N + 2 labels, including both boundary gates. A product indexed by Fin uses increasing val order, namely List.ofFn followed by List.prod. It follows the permutation's operator-product order. val extracts the natural label of an element of Fin.

**Definition 1.9 (The open-boundary integrability conjecture).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; \forall D \in \mathbb{N},\; \forall R \in \mathbb{C} \to \left(\mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right) \times \operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right) \times \operatorname{Fin}\left(D\right), \mathbb{C}\right)\right),\; \forall KR \in \mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right), \mathbb{C}\right),\; \forall KL \in \mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right), \mathbb{C}\right),\; \forall g \in \mathbb{C} \to \mathbb{C},\; \forall kappa \in \mathbb{C},\; ((1 \le N) \land ((\forall u \in \mathbb{C},\; R\left(u, u\right) = \operatorname{smul}\left(g\left(u\right), \operatorname{PEquiv}.\operatorname{toMatrix}\left(\operatorname{Equiv}.\operatorname{toPEquiv}\left(\operatorname{Equiv}.\operatorname{prodComm}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right)\right)\right)\right)\right)) \land ((g\left(kappa\right) \ne 0) \land (g\left(-kappa\right) \ne 0)))) \Rightarrow (\forall pi \in \operatorname{Perm}\left(\operatorname{Fin}\left(N + 2\right)\right),\; \exists theta \in \operatorname{Fin}\left(N + 1\right) \to \mathbb{C},\; \exists c \in \mathbb{C},\; (\forall i \in \operatorname{Fin}\left(N + 1\right),\; (theta\left(i\right) = kappa) \lor (theta\left(i\right) = -kappa)) \land ((c \ne 0) \land ((\operatorname{circuitProduct}\left(N, D, R, KR, KL, kappa, pi\right) = \operatorname{smul}\left(c, \operatorname{transfer}\left(N, D, R, KR, KL, kappa, theta\right)\right)) \land ((\forall u \in \mathbb{C},\; \forall v \in \mathbb{C},\; \operatorname{Commute}\left(\operatorname{transfer}\left(N, D, R, KR, KL, u, theta\right), \operatorname{transfer}\left(N, D, R, KR, KL, v, theta\right)\right)) \Rightarrow (\forall u \in \mathbb{C},\; \operatorname{Commute}\left(\operatorname{circuitProduct}\left(N, D, R, KR, KL, kappa, pi\right), \operatorname{transfer}\left(N, D, R, KR, KL, u, theta\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.claim` (`✓ std3`).

*Citation.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

Section 3.1.2, p. 15: “For the open-boundary case, similarly to the periodic setting [31], we conjecture that any circuit in which each gate U_{i,i+1} (constructed from an Ř-matrix) appears exactly once per period to every nearest-neighbor pair of spins, and where each boundary gate is constructed from a K-matrix, is integrable.” The encoding uses N + 1 physical sites and N + 2 gates, so 1 <= N is exactly the source's chain length at least two. R, KR and KL are arbitrary matrix-valued spectral functions. Regularity and the two nonzero scalar values suffice for the identity. smul denotes the complex scalar action. Integrability is the conditional commutation statement using the source's standing transfer-commutation property, equation (12); deriving that property from Yang–Baxter and reflection equations is separate.

**Theorem 1.10 (Every ordering has a transfer-matrix realization).**

$$\forall N \in \mathbb{N},\; \forall D \in \mathbb{N},\; \forall R \in \mathbb{C} \to \left(\mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right) \times \operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right) \times \operatorname{Fin}\left(D\right), \mathbb{C}\right)\right),\; \forall KR \in \mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right), \mathbb{C}\right),\; \forall KL \in \mathbb{C} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right), \mathbb{C}\right),\; \forall g \in \mathbb{C} \to \mathbb{C},\; \forall kappa \in \mathbb{C},\; ((1 \le N) \land ((\forall u \in \mathbb{C},\; R\left(u, u\right) = \operatorname{smul}\left(g\left(u\right), \operatorname{PEquiv}.\operatorname{toMatrix}\left(\operatorname{Equiv}.\operatorname{toPEquiv}\left(\operatorname{Equiv}.\operatorname{prodComm}\left(\operatorname{Fin}\left(D\right), \operatorname{Fin}\left(D\right)\right)\right)\right)\right)) \land ((g\left(kappa\right) \ne 0) \land (g\left(-kappa\right) \ne 0)))) \Rightarrow (\forall pi \in \operatorname{Perm}\left(\operatorname{Fin}\left(N + 2\right)\right),\; \exists theta \in \operatorname{Fin}\left(N + 1\right) \to \mathbb{C},\; \exists c \in \mathbb{C},\; (\forall i \in \operatorname{Fin}\left(N + 1\right),\; (theta\left(i\right) = kappa) \lor (theta\left(i\right) = -kappa)) \land ((c \ne 0) \land ((\operatorname{circuitProduct}\left(N, D, R, KR, KL, kappa, pi\right) = \operatorname{smul}\left(c, \operatorname{transfer}\left(N, D, R, KR, KL, kappa, theta\right)\right)) \land ((\forall u \in \mathbb{C},\; \forall v \in \mathbb{C},\; \operatorname{Commute}\left(\operatorname{transfer}\left(N, D, R, KR, KL, u, theta\right), \operatorname{transfer}\left(N, D, R, KR, KL, v, theta\right)\right)) \Rightarrow (\forall u \in \mathbb{C},\; \operatorname{Commute}\left(\operatorname{circuitProduct}\left(N, D, R, KR, KL, kappa, pi\right), \operatorname{transfer}\left(N, D, R, KR, KL, u, theta\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.result` (`✓ std3`). ∎

*Resolves.* `Problems/garcia-fernandez-2026-open-circuit-integrability` (proved) by `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"garcia-fernandez-2026-open-circuit-integrability","declaration_gid":"D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

Assign a negative inhomogeneity at physical site i - 1 exactly when label i precedes label i - 1 in the circuit word. Nonadjacent labels act on disjoint sites and commute. Sorting the labels by the signed key gives the descending negative labels, then zero, then the ascending positive labels, without changing the product. The auxiliary swap train reduces the explicit double-row product to the reversed gate word of circuit, whose time order is fixed by the boundary and bulk gates. The induction uses that same gate word with the terminal KN gate removed; K1 represents label zero and U j represents label j. Each regular checked matrix supplies a scalar identity; their nonzero product accounts for the proportionality constant. Both terminal signs give the same correspondence. Finally a scalar multiple of the transfer matrix at kappa commutes with the transfer family whenever that family mutually commutes.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.checkedR`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.circuitProduct`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.gate`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.leftGate`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.oneOp`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.partialTrace`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.transfer`
- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitIntegrability.twoOp`
- Dependency: [D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation](OpenIntegrableCircuitDepthRefutation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
