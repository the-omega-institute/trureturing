# Qubit Jensen–Shannon order score

## Abstract

The Jensen–Shannon order score for two sharp qubit measurements.

Every square root uses Lean’s total real convention. It is the nonnegative square root of the maximum of zero and its argument, so a negative argument gives zero.

The score formulas use the total real entropy functions in nats. The logarithm is applied to the absolute value of each nonzero entry, and a zero entry contributes zero.

$$
\varphi\left(0\right) = 0 \land \left(\forall x \in \mathbb{R},\; x \ne 0 \Rightarrow \varphi\left(x\right) = -(x) \cdot \operatorname{ln}\left(|x|\right)\right)
$$

$$
\forall p \in Bool \times Bool \to \mathbb{R},\; \operatorname{H}\left(p\right) = \sum_{o \in Bool \times Bool} \varphi\left(\operatorname{p}\left(o\right)\right)
$$

$$
\left(\forall x \in \mathbb{R},\; \operatorname{h}\left(x\right) = \varphi\left(x\right) + \varphi\left(1 - x\right)\right) \land \left(\forall y \in \mathbb{R},\; \operatorname{g}\left(y\right) = \operatorname{ln}\left(2\right) - \operatorname{h}\left(\frac{1 + y}{2}\right)\right)
$$

**Definition 1.1 (Outcome signs).**

$$\forall a \in Bool,\; \operatorname{outcomeSign}\left(a\right) = \operatorname{ite}\left(a, 1, -(1)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.outcomeSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two Boolean outcomes represent the signs −1 and +1.

**Definition 1.2 (Pauli effects).**

$$\forall m \in \mathbb{R},\; \forall k \in \mathbb{R},\; \forall a \in Bool,\; \operatorname{projector}\left(m, k, a\right) = \operatorname{qubitMatrix}\left(\operatorname{outcomeSign}\left(a\right) \cdot k, \operatorname{outcomeSign}\left(a\right) \cdot m\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.projector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the bisector frame the Bloch axis has coordinates (k, 0, m).

**Definition 1.3 (Native state matrix).**

$$\forall r \in \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right),\; \operatorname{nativeMatrix}\left(r\right) = \operatorname{ofMatrixSymm}\left(r.val\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.nativeMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A DensityState on Fin 2 is a positive semidefinite complex operator of trace one. The matrix conversion preserves the operator and its trace.

**Definition 1.4 (Parity parameter).**

$$\forall t \in \mathbb{R},\; \operatorname{sOfT}\left(t\right) = \frac{1 - \sqrt{\operatorname{max}\left(0, 1 - 4 \cdot (t)^{2}\right)}}{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.sOfT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The acute branch selects the smaller parity mass.

**Theorem 1.5 (Parity calibration).**

$$\forall t \in \mathbb{R},\; t \in [0, \frac{1}{2}] \Rightarrow \left(\operatorname{sOfT}\left(t\right) \in [0, \frac{1}{2}] \land \operatorname{sOfT}\left(t\right) \cdot \left(1 - \operatorname{sOfT}\left(t\right)\right) = (t)^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.parameter_calibration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The smaller parity mass lies in the closed half interval and determines the square of the order parameter.

**Definition 1.6 (Forward Lüders record).**

$$\forall A \in Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall B \in Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall r \in \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right),\; \forall o \in Bool \times Bool,\; \operatorname{jointRecord}\left(A, B, r, o\right) = \operatorname{Re}\left(\operatorname{Tr}\left(\operatorname{nativeMatrix}\left(r\right) \cdot \operatorname{A}\left(o.1\right) \cdot \operatorname{B}\left(o.2\right) \cdot \operatorname{A}\left(o.1\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.jointRecord` (`✓ std3`).

*Citation.* Shengjun Wu (2026). *Measurement-order dependence bounds uncertainty, contextuality, steering, and Bell nonlocality*. DOI: [10.48550/arXiv.2611.24604](https://doi.org/10.48550/arXiv.2611.24604). URL: <https://arxiv.org/abs/2611.24604v1>.

*Commentary.*

The first coordinate belongs to the measurement performed first.

**Definition 1.7 (Lüders order score).**

$$\forall A \in Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall B \in Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall r \in \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right),\; \mathrm{let} p = \Lambda (o: Bool \times Bool), \mathrm{let} a = o.1, \mathrm{let} b = o.2, \operatorname{Re}\left(\operatorname{Tr}\left(\operatorname{nativeMatrix}\left(r\right) \cdot \operatorname{A}\left(a\right) \cdot \operatorname{B}\left(b\right) \cdot \operatorname{A}\left(a\right)\right)\right), \mathrm{let} q = \Lambda (o: Bool \times Bool), \mathrm{let} a = o.1, \mathrm{let} b = o.2, \operatorname{Re}\left(\operatorname{Tr}\left(\operatorname{nativeMatrix}\left(r\right) \cdot \operatorname{B}\left(b\right) \cdot \operatorname{A}\left(a\right) \cdot \operatorname{B}\left(b\right)\right)\right), \operatorname{orderScore}\left(A, B, r\right) = \frac{\operatorname{H}\left(\Lambda (o: Bool \times Bool), \frac{\operatorname{p}\left(o\right) + \operatorname{q}\left(o\right)}{2}\right) - \frac{\operatorname{H}\left(p\right) + \operatorname{H}\left(q\right)}{2}}{\operatorname{ln}\left(2\right)}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.orderScore` (`✓ std3`).

*Citation.* Shengjun Wu (2026). *Measurement-order dependence bounds uncertainty, contextuality, steering, and Bell nonlocality*. DOI: [10.48550/arXiv.2611.24604](https://doi.org/10.48550/arXiv.2611.24604). URL: <https://arxiv.org/abs/2611.24604v1>.

*Commentary.*

The two records use the same density state and label entries by the outcome of each measurement. The formula uses the total finite entropy H for arbitrary Boolean-indexed matrices. For the two sharp measurements in Wu’s Definition 1, the records are probability laws and division by ln 2 gives the Jensen–Shannon divergence in bits.

**Definition 1.8 (Bisector-frame score).**

$$\forall t \in \mathbb{R},\; \forall r \in \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right),\; \mathrm{let} s = \operatorname{sOfT}\left(t\right), \mathrm{let} m = \sqrt{\operatorname{max}\left(0, 1 - s\right)}, \mathrm{let} k = \sqrt{\operatorname{max}\left(0, s\right)}, \operatorname{sourceScore}\left(t, r\right) = \operatorname{orderScore}\left(\operatorname{projector}\left(m, k\right), \operatorname{projector}\left(m, -(k)\right), r\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.sourceScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In X, Y, Z order the two sharp Bloch axes are (k, 0, m) and (−k, 0, m).

**Definition 1.9 (Optimized score).**

$$\forall t \in \mathbb{R},\; \operatorname{psi}\left(t\right) = \operatorname{sSup}\left(\operatorname{range}\left(\operatorname{sourceScore}\left(t\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.psi` (`✓ std3`).

*Citation.* Shengjun Wu (2026). *Measurement-order dependence bounds uncertainty, contextuality, steering, and Bell nonlocality*. DOI: [10.48550/arXiv.2611.24604](https://doi.org/10.48550/arXiv.2611.24604). URL: <https://arxiv.org/abs/2611.24604v1>.

*Commentary.*

Section II.C maximizes over all common native qubit inputs. The equality of the supremum with an attained maximum is proved below.

**Definition 1.10 (Closed Bloch disk).**

$$disk = \{d: \mathbb{R} \times \mathbb{R} \mid (d.1)^{2} + (d.2)^{2} \le 1\}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.disk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only the two coordinates in the plane of the measurement axes affect the two records.

**Definition 1.11 (Score in Bloch coordinates).**

$$\forall s \in \mathbb{R},\; \forall d \in \mathbb{R} \times \mathbb{R},\; \mathrm{let} u = \sqrt{\operatorname{max}\left(0, 1 - s\right)} \cdot d.2, \mathrm{let} v = \sqrt{\operatorname{max}\left(0, s\right)} \cdot d.1, \operatorname{diskScore}\left(s, d\right) = \frac{\frac{\operatorname{g}\left(u + v\right) + \operatorname{g}\left(u - v\right)}{2} - \left(1 - s\right) \cdot \operatorname{g}\left(u\right) - s \cdot \operatorname{g}\left(v\right)}{\operatorname{ln}\left(2\right)}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.diskScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The deficit g uses the total binary entropy h. For s in [0,1] and d in the closed Bloch disk, the parity masses are 1−s and s. Grouping by parity cancels the common parity entropy, including when a parity has zero mass.

**Theorem 1.12 (Attainment on the disk and in the native states).**

$$\forall t \in \mathbb{R},\; t \in [0, \frac{1}{2}] \Rightarrow \left(\exists d \in \mathbb{R} \times \mathbb{R},\; d \in disk \land \left(\exists r \in \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right),\; \operatorname{sourceScore}\left(t, r\right) = \operatorname{psi}\left(t\right) \land \left(\operatorname{diskScore}\left(\operatorname{sOfT}\left(t\right), d\right) = \operatorname{psi}\left(t\right) \land \left(\left(\forall x \in \mathbb{R} \times \mathbb{R},\; x \in disk \Rightarrow \operatorname{diskScore}\left(\operatorname{sOfT}\left(t\right), x\right) \le \operatorname{psi}\left(t\right)\right) \land \left(\forall q \in \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right),\; \operatorname{sourceScore}\left(t, q\right) \le \operatorname{psi}\left(t\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.native_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every disk point has a native realization, and a compactness argument attains the common largest score. The existential state and disk point use the same value of the optimization parameter.

**Definition 1.13 (First-quadrant circle).**

$$\forall w \in \mathbb{R},\; \operatorname{circlePoint}\left(w\right) = (\sqrt{\operatorname{max}\left(0, w\right)}, \sqrt{\operatorname{max}\left(0, 1 - w\right)})$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.circlePoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the closed unit interval the point lies on the first-quadrant unit circle, with squared X and Z coordinates w and 1−w, respectively. For every real w the squared coordinates use the maxima below.

$$
\forall w \in \mathbb{R},\; \left((\operatorname{circlePoint}\left(w\right).1)^{2} = \operatorname{max}\left(0, w\right) \land (\operatorname{circlePoint}\left(w\right).2)^{2} = \operatorname{max}\left(0, 1 - w\right)\right) \land \left(w \in [0, 1] \Rightarrow \left((\operatorname{circlePoint}\left(w\right).1)^{2} = w \land (\operatorname{circlePoint}\left(w\right).2)^{2} = 1 - w\right)\right)
$$

**Definition 1.14 (Entropy series weight).**

$$\forall n \in \mathbb{N},\; \operatorname{seriesWeight}\left(n\right) = \frac{1}{\left(2 \cdot \operatorname{realCast}\left(n\right) + 2\right) \cdot \left(2 \cdot \operatorname{realCast}\left(n\right) + 1\right)}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.seriesWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The even entropy series starts with degree two. The index is a natural number and its appearances in the weight are real casts.

**Theorem 1.15 (Positive weights).**

$$\forall n \in \mathbb{N},\; 0 < \operatorname{seriesWeight}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.series_weight_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All degrees have positive weights.

**Definition 1.16 (Even coefficient).**

$$\forall n \in \mathbb{N},\; \forall s \in \mathbb{R},\; \forall u \in \mathbb{R},\; \forall v \in \mathbb{R},\; \operatorname{coeff}\left(n, s, u, v\right) = \frac{(u + v)^{2 \cdot n + 2} + (u - v)^{2 \cdot n + 2}}{2} - \left(1 - s\right) \cdot (u)^{2 \cdot n + 2} - s \cdot (v)^{2 \cdot n + 2}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two original biases are u+v and u−v, and u and v are the parity biases of the mixture.

**Theorem 1.17 (Quadratic coefficient).**

$$\forall s \in \mathbb{R},\; \forall u \in \mathbb{R},\; \forall v \in \mathbb{R},\; \operatorname{coeff}\left(0, s, u, v\right) = s \cdot (u)^{2} + \left(1 - s\right) \cdot (v)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.coeff_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mixed terms cancel at degree two.

**Definition 1.18 (Disk coefficients).**

$$\forall n \in \mathbb{N},\; \forall s \in \mathbb{R},\; \forall d \in \mathbb{R} \times \mathbb{R},\; \operatorname{diskCoeff}\left(n, s, d\right) = \operatorname{coeff}\left(n, s, \sqrt{\operatorname{max}\left(0, 1 - s\right)} \cdot d.2, \sqrt{\operatorname{max}\left(0, s\right)} \cdot d.1\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.diskCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The disk coordinates determine all four biases.

**Theorem 1.19 (Closed-disk entropy series).**

$$\forall s \in \mathbb{R},\; \forall d \in \mathbb{R} \times \mathbb{R},\; \left(s \in [0, 1] \land d \in disk\right) \Rightarrow \operatorname{HasSum}\left(\Lambda (n: \mathbb{N}), \operatorname{seriesWeight}\left(n\right) \cdot \operatorname{diskCoeff}\left(n, s, d\right), \operatorname{diskScore}\left(s, d\right) \cdot \operatorname{ln}\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.disk_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uniform convergence of the scalar entropy series on the closed bias interval allows biases of magnitude one.

**Theorem 1.20 (Coefficientwise comparison).**

$$\forall s \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall d \in \mathbb{R} \times \mathbb{R},\; \forall e \in \mathbb{R} \times \mathbb{R},\; \left(s \in [0, 1] \land \left(t \in [0, 1] \land \left(d \in disk \land e \in disk\right)\right)\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; \operatorname{diskCoeff}\left(n, s, d\right) \le \operatorname{diskCoeff}\left(n, t, e\right)\right) \Rightarrow \operatorname{diskScore}\left(s, d\right) \le \operatorname{diskScore}\left(t, e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.disk_score_le_of_coeff_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A comparison between two disk points at possibly different parity weights lifts to the entropy score.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.circlePoint`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.coeff`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.coeff_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.disk`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.diskCoeff`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.diskScore`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.disk_score_le_of_coeff_le`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.disk_series`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.jointRecord`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.nativeMatrix`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.native_maximum`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.orderScore`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.outcomeSign`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.parameter_calibration`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.projector`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.psi`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.sOfT`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.seriesWeight`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.series_weight_pos`
- Truth anchor: `D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.sourceScore`
- Dependency: [D5/S3/Entropy/MaxEntropy](../../../Entropy/MaxEntropy.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../../Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Information/QubitNormalFormState](../../Information/QubitNormalFormState.md)
