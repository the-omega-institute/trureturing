# MarkedDegreeEnumeration

## Abstract

Degree enumeration for labelled circular run-constrained words.

**Definition 1.1 (DegreeTuples).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \forall (\operatorname{k}: \operatorname{Nat}), \operatorname{DegreeTuples} \operatorname{n} \operatorname{ell} \operatorname{k} = (\{ \operatorname{t} : \operatorname{GoodTuple} \operatorname{n} // \operatorname{t}.\operatorname{val}.\operatorname{length} = \operatorname{ell} \land \operatorname{tupleDegree} \operatorname{t}.\operatorname{val} = \operatorname{k} \})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.DegreeTuples` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The subtype fixes the number of tuple pairs and their exact tuple degree.

**Definition 1.2 (instFintypeDegreeTuples).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \forall (\operatorname{k}: \operatorname{Nat}), \operatorname{instFintypeDegreeTuples} \operatorname{n} \operatorname{ell} \operatorname{k} : \operatorname{Fintype} (\operatorname{DegreeTuples} \operatorname{n} \operatorname{ell} \operatorname{k})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.instFintypeDegreeTuples` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

This instance is inferInstanceAs for the subtype of RunTuples n ell whose tupleDegree equals k.

**Theorem 1.3 (marked degree double count).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \forall (\operatorname{k}: \operatorname{Nat}), \operatorname{ell} \cdot \operatorname{Fintype}.\operatorname{card} (\operatorname{DegreeRunWords} \operatorname{n} \operatorname{ell} \operatorname{k}) = \operatorname{n} \cdot \operatorname{Fintype}.\operatorname{card} (\operatorname{DegreeTuples} \operatorname{n} \operatorname{ell} \operatorname{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.marked_degree_double_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The marked word-to-tuple equivalence preserves degree and converts run marks into labelled origins.

**Definition 1.4 (degreePolynomial).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \operatorname{degreePolynomial} \operatorname{n} = (\sum \operatorname{k} \in \operatorname{Finset}.\operatorname{range} (\operatorname{n} + 1) , \operatorname{Polynomial}.\operatorname{C} (\operatorname{N} \operatorname{n} \operatorname{k} : \mathbb{Z}) \cdot \operatorname{Polynomial}.\operatorname{X}^{\operatorname{k}})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.degreePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Summing the histogram with monomials in the degree records all labelled admissible words.

**Definition 1.5 (instFintypeRunTuples).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \operatorname{instFintypeRunTuples} \operatorname{n} \operatorname{ell} : \operatorname{Fintype} (\operatorname{RunTuples} \operatorname{n} \operatorname{ell})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.instFintypeRunTuples` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

This instance is inferInstanceAs for the subtype of GoodTuple n whose underlying list has length ell.

**Lemma 1.6 (runCount le).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \operatorname{runCount} \operatorname{w} \le \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.runCount_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Marked starts form a subset of the labelled positions, bounding the number of runs by the length.

**Definition 1.7 (runPolynomial).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \operatorname{runPolynomial} \operatorname{n} \operatorname{ell} = (\sum \operatorname{k} \in \operatorname{Finset}.\operatorname{range} (\operatorname{n} + 1) , \operatorname{Polynomial}.\operatorname{C} ((\operatorname{Fintype}.\operatorname{card} (\operatorname{DegreeRunWords} \operatorname{n} \operatorname{ell} \operatorname{k})) : \mathbb{Z}) \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{\operatorname{k}})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.runPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Filtering additionally by the number of circular runs gives the degree-refined run polynomial.

**Definition 1.8 (tuplePolynomial).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \operatorname{tuplePolynomial} \operatorname{n} \operatorname{ell} = (\sum \operatorname{k} \in \operatorname{Finset}.\operatorname{range} (\operatorname{n} + 1) , \operatorname{Polynomial}.\operatorname{C} ((\operatorname{Fintype}.\operatorname{card} (\operatorname{DegreeTuples} \operatorname{n} \operatorname{ell} \operatorname{k})) : \mathbb{Z}) \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{\operatorname{k}})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.tuplePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Counting positive tuples by their tuple degree gives the corresponding run-refined weight polynomial.

**Theorem 1.9 (polynomial marked double count).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), (\operatorname{ell} : (\operatorname{Polynomial} \mathbb{Z})) \cdot \operatorname{runPolynomial} \operatorname{n} \operatorname{ell} = (\operatorname{n} : (\operatorname{Polynomial} \mathbb{Z})) \cdot \operatorname{tuplePolynomial} \operatorname{n} \operatorname{ell}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.polynomial_marked_double_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Applying the marked count to each degree coefficient gives the integer polynomial double-count identity.

**Theorem 1.10 (tuplePolynomial eq sum).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{ell}: \operatorname{Nat}), \operatorname{tuplePolynomial} \operatorname{n} \operatorname{ell} = \sum \operatorname{t} : \operatorname{RunTuples} \operatorname{n} \operatorname{ell} , (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{\operatorname{tupleDegree} \operatorname{t}.\operatorname{val}.\operatorname{val}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.tuplePolynomial_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Partitioning the finite tuple set by degree turns the histogram polynomial into a sum of tuple weights.

**Lemma 1.11 (degreePolynomial partition).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \operatorname{degreePolynomial} \operatorname{n} = \sum \operatorname{ell} \in \operatorname{Finset}.\operatorname{range} (\operatorname{n} + 1) , \operatorname{runPolynomial} \operatorname{n} \operatorname{ell}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.degreePolynomial_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Partitioning admissible words by their run count recovers the full degree polynomial.

**Lemma 1.12 (runPolynomial zero).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \operatorname{runPolynomial} \operatorname{n} 0 = (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{(\operatorname{if} \operatorname{n} \le 2 \operatorname{then} 0 \operatorname{else} \operatorname{n})}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.runPolynomial_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

A zero-run admissible word is the zero word, whose degree fixes its single polynomial weight.

**Lemma 1.13 (Zero run count).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{ha}: \operatorname{Admissible} \operatorname{w}), \operatorname{runCount} \operatorname{w} = 0 \iff \operatorname{w} = (\operatorname{Function}.\operatorname{const} (\operatorname{Fin} \operatorname{n}) \operatorname{false})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.runCount_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

For an admissible word, zero run count is equivalent to being the all-false word.

## References

- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.DegreeTuples`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.degreePolynomial`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.degreePolynomial_partition`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.instFintypeDegreeTuples`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.instFintypeRunTuples`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.marked_degree_double_count`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.polynomial_marked_double_count`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.runCount_le`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.runCount_zero_iff`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.runPolynomial`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.runPolynomial_zero`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.tuplePolynomial`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration.tuplePolynomial_eq_sum`
- Dependency: [D5/S1/Words/AssociatedMersenne/MultiRunDegrees](MultiRunDegrees.md)
