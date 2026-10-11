# TransferTuples

## Abstract

Degree enumeration for labelled circular run-constrained words.

**Definition 1.1 (geom).**

$$\forall (\operatorname{z}: \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})), \operatorname{geom} \operatorname{z} = (\operatorname{PowerSeries}.\operatorname{invOfUnit} (1 - \operatorname{z}) 1)$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.geom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The inverse of one minus a positive-order series supplies its formal geometric series.

**Definition 1.2 (Rser).**

$$\operatorname{Rser} = ((\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))^{3} \cdot (\operatorname{PowerSeries}.\operatorname{C} (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) + (\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))^{5} \cdot (\operatorname{PowerSeries}.\operatorname{C} (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))^{2} \cdot \operatorname{geom} ((\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))^{2}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.Rser` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The run series separates a singleton one-run weight from the geometric tail of longer runs.

**Definition 1.3 (Qser).**

$$\operatorname{Qser} = ((\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) \cdot \operatorname{geom} ((\operatorname{PowerSeries}.\operatorname{C} (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) \cdot (\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.Qser` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The slack series records a compulsory position followed by an arbitrary weighted slack tail.

**Definition 1.4 (A).**

$$\begin{aligned}\operatorname{A} 0 0 = \operatorname{Rser}\\\operatorname{A} 0 1 = \operatorname{Rser} \cdot \operatorname{Qser}\\\operatorname{A} 1 0 = \operatorname{Rser}\\\operatorname{A} 1 1 = \operatorname{Rser} \cdot (\operatorname{PowerSeries}.\operatorname{C} (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})) \cdot \operatorname{Qser}\end{aligned}$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The two slack states determine the transfer entries from run and gap weight factors.

**Lemma 1.5 (det A).**

$$\operatorname{Matrix}.\operatorname{det} (1 - \operatorname{A}) = 1 - \operatorname{Rser} - \operatorname{Rser} \cdot (\operatorname{PowerSeries}.\operatorname{C} (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) \cdot \operatorname{Qser} + \operatorname{Rser}^{2} \cdot ((\operatorname{PowerSeries}.\operatorname{C} (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) - 1) \cdot \operatorname{Qser}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferTuples.det_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Expanding the two-by-two determinant expresses the transfer denominator in run and slack series.

**Lemma 1.6 (geom X2).**

$$(1 - (\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))^{2}) \cdot \operatorname{geom} ((\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))^{2}) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferTuples.geom_X2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Multiplication by one minus the square of the length variable cancels its geometric series.

**Lemma 1.7 (geom YX).**

$$(1 - (\operatorname{PowerSeries}.\operatorname{C} (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) \cdot (\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))) \cdot \operatorname{geom} ((\operatorname{PowerSeries}.\operatorname{C} (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) \cdot (\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferTuples.geom_YX` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Multiplication by one minus the joint length-and-degree variable cancels its geometric series.

**Definition 1.8 (AgreeUpTo).**

$$\forall (\operatorname{N}: \operatorname{Nat}), \forall (\operatorname{f}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \forall (\operatorname{g}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \operatorname{AgreeUpTo} \operatorname{N} \operatorname{f} \operatorname{g} \iff (\forall \operatorname{n} , \operatorname{n} \le \operatorname{N} \to \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} \operatorname{f} = \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} \operatorname{g})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.AgreeUpTo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Agreement of coefficients through a bound records the finite precision needed for enumeration.

**Theorem 1.9 (geom monomial approx).**

$$\forall (\operatorname{m}: \operatorname{Nat}), \forall (\operatorname{d}: \operatorname{Nat}), \forall (\operatorname{N}: \operatorname{Nat}), (0 < \operatorname{m}) \to (\operatorname{AgreeUpTo} \operatorname{N} (\operatorname{geom} (\operatorname{PowerSeries}.\operatorname{monomial} \operatorname{m} ((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{\operatorname{d}}))) (\sum \operatorname{j} \in \operatorname{Finset}.\operatorname{range} (\operatorname{N} + 1) , (\operatorname{PowerSeries}.\operatorname{monomial} \operatorname{m} ((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{\operatorname{d}}))^{\operatorname{j}}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferTuples.geom_monomial_approx` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The finite geometric-sum identity and the positive monomial order remove all omitted low-degree coefficients.

**Definition 1.10 (slackState).**

$$\forall (\operatorname{s}: \operatorname{Nat}), \operatorname{slackState} \operatorname{s} = (\operatorname{if} \operatorname{s} = 0 \operatorname{then} 0 \operatorname{else} 1)$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.slackState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Zero slack selects one transfer state and positive slack selects the other.

**Definition 1.11 (pairLocal).**

$$\forall (\operatorname{b}: \operatorname{Nat} \times \operatorname{Nat}), \operatorname{pairLocal} \operatorname{b} = (\operatorname{min} \operatorname{b}.1 2 + (\operatorname{b}.2 - 1))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.pairLocal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The local weight counts run deletion endpoints and the interior contribution from one gap.

**Definition 1.12 (adjacency).**

$$\forall (\operatorname{i}: \operatorname{Fin} 2), \forall (\operatorname{j}: \operatorname{Fin} 2), \operatorname{adjacency} \operatorname{i} \operatorname{j} = (\operatorname{if} \operatorname{i} = 1 \land \operatorname{j} = 1 \operatorname{then} 1 \operatorname{else} 0)$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.adjacency` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The transition contributes one insertion exactly when both consecutive slack states are positive.

**Definition 1.13 (openDegree).**

$$\begin{aligned}\forall (\operatorname{j}: \operatorname{Fin} 2), \operatorname{openDegree} \operatorname{j} [   ] = 0\\\forall (\operatorname{j}: \operatorname{Fin} 2), \forall (\operatorname{b} : \operatorname{Nat} \times \operatorname{Nat}) , \operatorname{openDegree} \operatorname{j} [ \operatorname{b} ] = \operatorname{pairLocal} \operatorname{b} + \operatorname{adjacency} (\operatorname{slackState} \operatorname{b}.2) \operatorname{j}\\\forall (\operatorname{j}: \operatorname{Fin} 2), \forall (\operatorname{b} \operatorname{c} : \operatorname{Nat} \times \operatorname{Nat}) (\operatorname{t} : \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})) , \operatorname{openDegree} \operatorname{j} (\operatorname{b} :: \operatorname{c} :: \operatorname{t}) = \operatorname{pairLocal} \operatorname{b} + \operatorname{adjacency} (\operatorname{slackState} \operatorname{b}.2) (\operatorname{slackState} \operatorname{c}.2) + \operatorname{openDegree} \operatorname{j} (\operatorname{c} :: \operatorname{t})\end{aligned}$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.openDegree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Accumulating pair-local weights and state transitions gives the weight of an open tuple path.

**Definition 1.14 (provisionalDegree).**

$$\begin{aligned}\operatorname{provisionalDegree} [   ] = 0\\\forall (\operatorname{b} : \operatorname{Nat} \times \operatorname{Nat}) (\operatorname{u} : \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})) , \operatorname{provisionalDegree} (\operatorname{b} :: \operatorname{u}) = \operatorname{openDegree} (\operatorname{slackState} \operatorname{b}.2) (\operatorname{b} :: \operatorname{u})\end{aligned}$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.provisionalDegree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Closing the tuple path adds the final transition back to the initial slack state.

**Theorem 1.15 (trace coefficient tuples).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} (\operatorname{Matrix}.\operatorname{trace} (\operatorname{A}^{(\operatorname{ell} + 1)})) = \sum \operatorname{t} : \operatorname{RunTuples} \operatorname{n} (\operatorname{ell} + 1) , (\operatorname{Polynomial}.\operatorname{X} : (\operatorname{Polynomial} \mathbb{Z}))^{\operatorname{provisionalDegree} \operatorname{t}.\operatorname{val}.\operatorname{val}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferTuples.trace_coefficient_tuples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The matrix trace enumerates ordered tuples at each finite length, with provisionalDegree. No rotations of the word are identified.

**Theorem 1.16 (tuple transfer coefficient).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \operatorname{tuplePolynomial} \operatorname{n} (\operatorname{ell} + 1) = \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} (\operatorname{Matrix}.\operatorname{trace} (\operatorname{A}^{(\operatorname{ell} + 1)})) + \operatorname{if} \operatorname{ell} = 0 \operatorname{then} \operatorname{PowerSeries}.\operatorname{coeff} \operatorname{n} ((\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})) \cdot (1 - (\operatorname{PowerSeries}.\operatorname{C} (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) : \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))) \cdot \operatorname{Rser}) \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferTuples.tuple_transfer_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The correction PowerSeries.X * (1 - PowerSeries.C Polynomial.X) * Rser removes the extra singleton insertion. For [(r,1)], provisionalDegree is min r 2 + 1 and tupleDegree is min r 2.

**Lemma 1.17 (Geometric series inverse).**

$$\forall (\operatorname{z}: \operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z})), \forall (\operatorname{hz}: \operatorname{PowerSeries}.\operatorname{constantCoeff} \operatorname{z} = 0), (1 - \operatorname{z}) \cdot \operatorname{geom} \operatorname{z} = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferTuples.geom_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

A series with zero constant coefficient has geometric series inverse to one minus the series.

**Lemma 1.18 (Agreement under addition).**

$$\forall (\operatorname{N}: \operatorname{Nat}), \forall (\operatorname{f}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \forall (\operatorname{g}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \forall (\operatorname{u}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \forall (\operatorname{v}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \forall (\operatorname{h}: \operatorname{AgreeUpTo} \operatorname{N} \operatorname{f} \operatorname{g}), \forall (\operatorname{k}: \operatorname{AgreeUpTo} \operatorname{N} \operatorname{u} \operatorname{v}), \operatorname{AgreeUpTo} \operatorname{N} (\operatorname{f} + \operatorname{u}) (\operatorname{g} + \operatorname{v})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferTuples.add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Coefficient agreement through a bound is preserved by addition.

**Lemma 1.19 (Agreement under multiplication).**

$$\forall (\operatorname{N}: \operatorname{Nat}), \forall (\operatorname{f}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \forall (\operatorname{g}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \forall (\operatorname{u}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \forall (\operatorname{v}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \forall (\operatorname{h}: \operatorname{AgreeUpTo} \operatorname{N} \operatorname{f} \operatorname{g}), \forall (\operatorname{k}: \operatorname{AgreeUpTo} \operatorname{N} \operatorname{u} \operatorname{v}), \operatorname{AgreeUpTo} \operatorname{N} (\operatorname{f} \cdot \operatorname{u}) (\operatorname{g} \cdot \operatorname{v})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferTuples.mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Coefficient agreement through a bound is preserved by multiplication.

**Lemma 1.20 (Finite geometric identity).**

$$\forall (\operatorname{z}: (\operatorname{PowerSeries} (\operatorname{Polynomial} \mathbb{Z}))), \forall (\operatorname{N}: \operatorname{Nat}), \forall (\operatorname{hz}: \operatorname{PowerSeries}.\operatorname{constantCoeff} \operatorname{z} = 0), \operatorname{geom} \operatorname{z} = (\sum \operatorname{j} \in \operatorname{Finset}.\operatorname{range} (\operatorname{N} + 1) , \operatorname{z}^{\operatorname{j}}) + \operatorname{z}^{(\operatorname{N} + 1)} \cdot \operatorname{geom} \operatorname{z}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferTuples.geom_finite_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The geometric series equals its finite truncation plus the remaining tail.

**Definition 1.21 (Transfer length).**

$$\forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \operatorname{transferLength} \operatorname{t} = (\operatorname{t}.\operatorname{map} \operatorname{pairLength})  .  \operatorname{sum}$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.transferLength` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The transfer length is the sum of the pair lengths in a tuple.

**Definition 1.22 (Alphabet pair).**

$$\forall (\operatorname{N}: \operatorname{Nat}), \forall (\operatorname{b}: \operatorname{Fin} (\operatorname{N} + 2) \times \operatorname{Fin} (\operatorname{N} + 2)), \operatorname{alphabetPair} \operatorname{b} = (\operatorname{b}.1.\operatorname{val} + 1 , \operatorname{b}.2.\operatorname{val})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.alphabetPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

A bounded alphabet pair maps to its natural run and gap lengths.

**Definition 1.23 (Bounded tuple list).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \forall (\operatorname{f}: \operatorname{Fin} \operatorname{ell} \to \operatorname{Fin} (\operatorname{n} + 2) \times \operatorname{Fin} (\operatorname{n} + 2)), \operatorname{boundedList} \operatorname{n} \operatorname{ell} \operatorname{f} = \operatorname{List}.\operatorname{ofFn} (\operatorname{fun} \operatorname{p} \mapsto \operatorname{alphabetPair} (\operatorname{f} \operatorname{p}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/TransferTuples.boundedList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

A bounded function of alphabet pairs is converted to a list of natural pairs.

**Theorem 1.24 (Bounded weight sum).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \forall (\operatorname{g}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat}) \to \operatorname{Polynomial} \mathbb{Z}), (\sum \operatorname{f} : \operatorname{Fin} (\operatorname{ell} + 1) \to \operatorname{Fin} (\operatorname{n} + 2) \times \operatorname{Fin} (\operatorname{n} + 2) , \operatorname{if} \operatorname{transferLength} (\operatorname{boundedList} \operatorname{n} (\operatorname{ell} + 1) \operatorname{f}) = \operatorname{n} \operatorname{then} \operatorname{g} (\operatorname{boundedList} \operatorname{n} (\operatorname{ell} + 1) \operatorname{f}) \operatorname{else} 0) = \sum \operatorname{t} : \operatorname{RunTuples} \operatorname{n} (\operatorname{ell} + 1) , \operatorname{g} \operatorname{t}.\operatorname{val}.\operatorname{val}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/TransferTuples.bounded_weight_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Summing weights over bounded functions equals summing over the corresponding bounded tuples.

## References

- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.A`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.AgreeUpTo`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.Qser`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.Rser`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.add`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.adjacency`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.alphabetPair`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.boundedList`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.bounded_weight_sum`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.det_A`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.geom`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.geom_X2`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.geom_YX`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.geom_finite_identity`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.geom_monomial_approx`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.geom_mul`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.mul`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.openDegree`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.pairLocal`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.provisionalDegree`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.slackState`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.trace_coefficient_tuples`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.transferLength`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/TransferTuples.tuple_transfer_coefficient`
- Dependency: [D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration](MarkedDegreeEnumeration.md)
