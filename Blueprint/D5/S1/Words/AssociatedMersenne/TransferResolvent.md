# TransferResolvent

## Abstract

Degree enumeration for labelled circular run-constrained words.

**Definition 1.1 (dMatrix).**

$$\forall (\operatorname{M}: \operatorname{Matrix} (\operatorname{Fin} 2) (\operatorname{Fin} 2) (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \operatorname{dMatrix} \operatorname{M} = (\operatorname{fun} \operatorname{i} \operatorname{j} \mapsto (\operatorname{PowerSeries}.\operatorname{derivative} (\operatorname{Polynomial} \mathbb{Z})) (\operatorname{M} \operatorname{i} \operatorname{j}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferResolvent.dMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Applying the power-series derivative to each matrix entry differentiates the transfer matrix.

**Definition 1.2 (matrixGeom).**

$$\forall (\operatorname{i} \operatorname{j}: \operatorname{Fin} 2), \operatorname{matrixGeom} \operatorname{i} \operatorname{j} = \operatorname{PowerSeries}.\operatorname{mk} (\operatorname{fun} \operatorname{n} \mapsto \sum \operatorname{k} \in \operatorname{Finset}.\operatorname{range} (\operatorname{n} + 1) , \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} ((\operatorname{A}^{\operatorname{k}}) \operatorname{i} \operatorname{j}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferResolvent.matrixGeom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Each coefficient uses only powers k≤n, because A is divisible by PowerSeries.X³. All displayed sums are finite.

**Theorem 1.3 (matrixGeom inverse).**

$$(1 - \operatorname{A}) \cdot \operatorname{matrixGeom} = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferResolvent.matrixGeom_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

At each coefficient only finitely many powers contribute, and the finite geometric-sum identity gives the inverse.

**Definition 1.4 (transferDet).**

$$\operatorname{transferDet} = (\operatorname{Matrix}.\operatorname{det} (1 - \operatorname{A}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferResolvent.transferDet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The determinant of one minus the transfer matrix supplies the cleared transfer denominator.

**Definition 1.5 (transferTrace).**

$$\operatorname{transferTrace} = (\operatorname{Matrix}.\operatorname{trace} (\operatorname{matrixGeom} \cdot \operatorname{dMatrix} \operatorname{A}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferResolvent.transferTrace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Tracing the matrix resolvent times the differentiated transfer matrix records marked cyclic paths.

**Theorem 1.6 (transfer trace cleared).**

$$\operatorname{transferDet} \cdot \operatorname{transferTrace} = - (\operatorname{PowerSeries}.\operatorname{derivative} (\operatorname{Polynomial} \mathbb{Z})) \operatorname{transferDet}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferResolvent.transfer_trace_cleared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Multiplying the resolvent by its determinant gives the adjugate and hence the negative determinant derivative.

**Lemma 1.7 (coeff euler).**

$$\forall (\operatorname{f}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \forall (\operatorname{n}: \operatorname{Nat}), \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} ((\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) \cdot (\operatorname{PowerSeries}.\operatorname{derivative} (\operatorname{Polynomial} \mathbb{Z})) \operatorname{f}) = (\operatorname{n} : (\operatorname{Polynomial} \mathbb{Z})) \cdot \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} \operatorname{f}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferResolvent.coeff_euler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Multiplication by the length variable after differentiation multiplies the nth coefficient by n.

**Theorem 1.8 (trace marked coefficient).**

$$\forall (\operatorname{ell}: \operatorname{Nat}), \forall (\operatorname{n}: \operatorname{Nat}), ((\operatorname{ell} + 1 : (\operatorname{Polynomial} \mathbb{Z})) \cdot \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} ((\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) \cdot \operatorname{Matrix}.\operatorname{trace} (\operatorname{A}^{\operatorname{ell}} \cdot \operatorname{dMatrix} \operatorname{A}))) = (\operatorname{n} : (\operatorname{Polynomial} \mathbb{Z})) \cdot \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} (\operatorname{Matrix}.\operatorname{trace} (\operatorname{A}^{(\operatorname{ell} + 1)}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferResolvent.trace_marked_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Cyclic invariance of trace equates a marked matrix-power coefficient with its length-weighted derivative.

**Theorem 1.9 (coeff euler transferTrace).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} ((\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) \cdot \operatorname{transferTrace}) = \sum \operatorname{ell} \in \operatorname{Finset}.\operatorname{range} (\operatorname{n} + 1) , \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} ((\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) \cdot \operatorname{Matrix}.\operatorname{trace} (\operatorname{A}^{\operatorname{ell}} \cdot \operatorname{dMatrix} \operatorname{A}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferResolvent.coeff_euler_transferTrace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Finite coefficient truncation expresses the marked resolvent trace as the sum of the length-weighted cyclic traces.

## References

- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferResolvent.coeff_euler`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferResolvent.coeff_euler_transferTrace`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferResolvent.dMatrix`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferResolvent.matrixGeom`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferResolvent.matrixGeom_inverse`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferResolvent.trace_marked_coefficient`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferResolvent.transferDet`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferResolvent.transferTrace`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferResolvent.transfer_trace_cleared`
- Dependency: [D5/S1/Words/AssociatedMersenne/TransferTuples](TransferTuples.md)
