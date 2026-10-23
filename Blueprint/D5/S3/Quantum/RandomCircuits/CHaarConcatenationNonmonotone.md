# Concatenation can increase the cHaar moment norm

## Abstract

The second cHaar moment at system and environment dimension two has larger squared Hilbert-Schmidt norm after five concatenations than after four.

**Definition 1.1 (The cHaar channel).**

$$\forall d \in \mathbb{N},\; \forall e \in \mathbb{N},\; [\operatorname{NeZero}\left(e\right)] \forall U \in \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right)), \mathbb{C}\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{cHaarChannel}\left(d, e, U, X\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(U \cdot \operatorname{Matrix.kroneckerMap}\left(fun a \mapsto fun b \mapsto a \cdot b, X, (\operatorname{Matrix.single}\left(0, 0, 1\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(e\right), \operatorname{Fin}\left(e\right), \mathbb{C}\right))\right) \cdot \operatorname{star}\left(U\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.cHaarChannel` (`✓ std3`).

*Citation.* Matthew Duschenes, Diego García-Martín, Zoë Holmes, and M. Cerezo (2026). *Moments of Quantum Channel Ensembles*. DOI: [10.1103/grdp-jph9](https://doi.org/10.1103/grdp-jph9). URL: <https://arxiv.org/abs/2511.12700v2>.

*Commentary.*

Page 5: "Thus the action of any quantum channel is" followed by Lambda(X) = Tr_E[U_Lambda(X tensor nu_E)U_Lambda dagger]. Appendix B, Definition 4, page 25: "Using the Stinespring formalism, we can re-write this average as a twirl with respect to the Haar ensemble of unitaries acting on t copies of a composite space, of a system and environment H ⊗ E of dimensions d,d_E, and a local pure environment state ν_E ∈ B[E]," The system and environment are Fin d and Fin e; Matrix.single 0 0 1 is the fixed pure environment state. The existing partialTraceRight is precisely the sum over the environment coordinate.

**Definition 1.2 (The literal moment operator).**

$$\forall d \in \mathbb{N},\; \forall e \in \mathbb{N},\; \forall t \in \mathbb{N},\; [\operatorname{NeZero}\left(e\right)] \forall r \in ((\operatorname{Fin}\left(t\right) \to \operatorname{Fin}\left(d\right)) \times (\operatorname{Fin}\left(t\right) \to \operatorname{Fin}\left(d\right))),\; \forall c \in ((\operatorname{Fin}\left(t\right) \to \operatorname{Fin}\left(d\right)) \times (\operatorname{Fin}\left(t\right) \to \operatorname{Fin}\left(d\right))),\; \operatorname{momentOp}\left(d, e, t, r, c\right) = \int_{U: \operatorname{Matrix.unitaryGroup}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right)), \mathbb{C}\right)} (\prod_{s: \operatorname{Fin}\left(t\right)} (\operatorname{cHaarChannel}\left(d, e, \operatorname{val}\left(U\right), \operatorname{Matrix.single}\left((c).1\left(s\right), (c).2\left(s\right), 1\right), (r).1\left(s\right), (r).2\left(s\right)\right))) d(\operatorname{Measure.haarMeasure}\left((\operatorname{Top.top}: \operatorname{TopologicalSpace.PositiveCompacts}\left(\operatorname{Matrix.unitaryGroup}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(e\right)), \mathbb{C}\right)\right))\right))$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.momentOp` (`✓ std3`).

*Citation.* Matthew Duschenes, Diego García-Martín, Zoë Holmes, and M. Cerezo (2026). *Moments of Quantum Channel Ensembles*. DOI: [10.1103/grdp-jph9](https://doi.org/10.1103/grdp-jph9). URL: <https://arxiv.org/abs/2511.12700v2>.

*Commentary.*

Page 3: "We can then define the t-th order moment operator as the superoperator of the t-th order twirl," followed by equation (9). The entry at r,c integrates the product of the t channel matrix-unit entries with the same Haar unitary U. This defines every order t, not only the second order.

**Definition 1.3 (The squared Hilbert-Schmidt norm).**

$$\forall i \in Type,\; [\operatorname{Fintype}\left(i\right)] \forall M \in \operatorname{Matrix}\left(i, i, \mathbb{C}\right),\; \operatorname{hsNormSq}\left(M\right) = \sum _{r} \sum _{c} \operatorname{Complex.normSq}\left(M\left(r, c\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.hsNormSq` (`✓ std3`).

*Citation.* Matthew Duschenes, Diego García-Martín, Zoë Holmes, and M. Cerezo (2026). *Moments of Quantum Channel Ensembles*. DOI: [10.1103/grdp-jph9](https://doi.org/10.1103/grdp-jph9). URL: <https://arxiv.org/abs/2511.12700v2>.

*Commentary.*

The squared Hilbert-Schmidt norm is the sum of Complex.normSq over all matrix entries. The concatenation assertion compares this quantity for two powers of the moment operator.

**Definition 1.4 (The concatenation monotonicity assertion).**

$$\operatorname{claim}\left(\right) = \left(\forall d \in \mathbb{N},\; \forall e \in \mathbb{N},\; \forall t \in \mathbb{N},\; [\operatorname{NeZero}\left(e\right)] (1 \le d) \Rightarrow ((1 \le t) \Rightarrow (\forall k \in \mathbb{N},\; \forall j \in \mathbb{N},\; (1 \le k) \Rightarrow ((k \le j) \Rightarrow (\operatorname{hsNormSq}\left((\operatorname{momentOp}\left(d, e, t\right))^{j}\right) \le \operatorname{hsNormSq}\left((\operatorname{momentOp}\left(d, e, t\right))^{k}\right)))))\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.claim` (`✓ std3`).

*Citation.* Matthew Duschenes, Diego García-Martín, Zoë Holmes, and M. Cerezo (2026). *Moments of Quantum Channel Ensembles*. DOI: [10.1103/grdp-jph9](https://doi.org/10.1103/grdp-jph9). URL: <https://arxiv.org/abs/2511.12700v2>.

*Commentary.*

Appendix B, Conjecture 1, page 32: "it is conjectured that such a hierarchy holds for all concatenations k, orders t, and dimensions d,d_E. Further, it is conjectured that the cHaar norm is monotonically non-increasing with environment dimension and concatenations," followed by the displayed concatenation inequality for every k′ ≥ k. Here d,d_E are d,e; the order is t; k and j are positive concatenation counts with k ≤ j. Page 3: "The choice of norm ∥·∥ is task-dependent, and unless noted, we use the Hilbert-Schmidt norm as it is overall the simplest to compute." The squared Hilbert-Schmidt norm of the Liouville matrix is the existing RHLinalg.frobSq, equal to the double sum of Complex.normSq. The environment-dimension clause is a separate assertion.

**Theorem 1.5 (The coordinate swap is Hermitian).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \operatorname{Matrix.IsHermitian}\left(\operatorname{Equiv.Perm.permMatrix}\left(\mathbb{C}, \operatorname{Equiv.prodComm}\left(n, n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.swapHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Matthew Duschenes, Diego García-Martín, Zoë Holmes, and M. Cerezo (2026). *Moments of Quantum Channel Ensembles*. DOI: [10.1103/grdp-jph9](https://doi.org/10.1103/grdp-jph9). URL: <https://arxiv.org/abs/2511.12700v2>.

*Commentary.*

The permutation matrix of the coordinate swap equals its conjugate transpose.

**Theorem 1.6 (The coordinate swap is an involution).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \operatorname{Equiv.Perm.permMatrix}\left(\mathbb{C}, \operatorname{Equiv.prodComm}\left(n, n\right)\right) \cdot \operatorname{Equiv.Perm.permMatrix}\left(\mathbb{C}, \operatorname{Equiv.prodComm}\left(n, n\right)\right) = (1: \operatorname{Matrix}\left((n \times n), (n \times n), \mathbb{C}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.swapSquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Matthew Duschenes, Diego García-Martín, Zoë Holmes, and M. Cerezo (2026). *Moments of Quantum Channel Ensembles*. DOI: [10.1103/grdp-jph9](https://doi.org/10.1103/grdp-jph9). URL: <https://arxiv.org/abs/2511.12700v2>.

*Commentary.*

Applying the coordinate swap twice gives the identity matrix.

**Theorem 1.7 (The concatenation assertion is false).**

$$\neg \operatorname{claim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.result` (`✓ std3`). ∎

*Resolves.* `Problems/duschenes-garciamartin-holmes-cerezo-2026-chaar-concatenation` (refuted) by `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"duschenes-garciamartin-holmes-cerezo-2026-chaar-concatenation","declaration_gid":"D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Matthew Duschenes, Diego García-Martín, Zoë Holmes, and M. Cerezo (2026). *Moments of Quantum Channel Ensembles*. DOI: [10.1103/grdp-jph9](https://doi.org/10.1103/grdp-jph9). URL: <https://arxiv.org/abs/2511.12700v2>.

*Commentary.*

At d = e = t = 2 the fourth power has squared norm 1213852/1171875, and the fifth has squared norm 30362908/29296875. Their difference is 5536/9765625, which is positive. In the rational identity/swap basis, the decaying eigenmode coexists with a growing coefficient towards a non-orthogonal limiting projection.

## References

- Truth anchor: `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.cHaarChannel`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.claim`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.hsNormSq`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.momentOp`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.result`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.swapHermitian`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.swapSquare`
- Dependency: [D5/S3/Quantum/GNSMatrix](../GNSMatrix.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](HaarTwoCopyTwirl.md)
