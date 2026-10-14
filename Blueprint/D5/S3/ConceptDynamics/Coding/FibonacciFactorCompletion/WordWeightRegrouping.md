# Actual word-weight regrouping and rate abscissa

## Abstract

Actual retained path monomials regroup by original wordWeight, and the original max-one weighted factor rate equals their spectral convergence abscissa.

All paths use the original finite-past memories and both original guard conventions. The c and u labels retain weights twenty and six, including parallel labels with coincident endpoints. Empty walks, empty retained carriers, reducible graphs and walks across transient bridges remain in the quantified scope.

**Theorem 1.1 (core path witness dictionary equiv).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real, T \in Nat,\; \operatorname{Nonempty}\left(\operatorname{Equiv}\left(\operatorname{CorePathWitnessDictionary}\left(side, n, K, d, T\right), \operatorname{RetainedPathDictionary}\left(side, n, K, d, T\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.core_path_witness_dictionary_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recursive constructor rebuilds the actual successive memory vertices of every retained walk. The initial vertex and letter list determine the CorePath choices uniquely. Destructing the dependent sigma and subtype values proves equality without an unchecked cast.

**Theorem 1.2 (core path witness dictionary card).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real, T \in Nat,\; \operatorname{NatCard}\left(\operatorname{CorePathWitnessDictionary}\left(side, n, K, d, T\right)\right) = \operatorname{NatCard}\left(\operatorname{RetainedPathDictionary}\left(side, n, K, d, T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.core_path_witness_dictionary_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two actual dictionaries have equal cardinality. This auxiliary equality is used in the weighted fibre sum.

**Theorem 1.3 (actual weight regrouping).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real, z \in Real, T \in Nat,\; \left(\operatorname{lt}\left(0, K\right) \land \operatorname{le}\left(K, n\right)\right) \Rightarrow \operatorname{tsum}\left(\left(\operatorname{power}\left(z, T\right)\right)_{x \in \operatorname{CorePathWitnessDictionary}\left(side, n, K, d, T\right)}\right) = \operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{NatCard}\left(\operatorname{RetainedPathDictionary}\left(side, n, K, d, T\right)\right)\right), \operatorname{power}\left(z, T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.actual_weight_regrouping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one fixed weight T and any real z, the finite witness dictionary sums the constant z to T. This auxiliary formula supplies each fibre of the whole-series reindexing.

**Theorem 1.4 (actual monomial series regrouping).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real, z \in Real,\; \left(\operatorname{lt}\left(0, K\right) \land \left(\operatorname{le}\left(K, n\right) \land \operatorname{le}\left(0, z\right)\right)\right) \Rightarrow \left(\left(\operatorname{Summable}\left(\left(\operatorname{sum}\left(\left(\operatorname{sum}\left(\left(\operatorname{coreMonomial}\left(side, K, d, z, k, v, choices\right)\right)_{choices \in \operatorname{Fin}\left(k\right) \to \operatorname{Product}\left(CuLetter, \operatorname{CoreVertex}\left(side, n, K, d\right)\right)}\right)\right)_{v \in \operatorname{CoreVertex}\left(side, n, K, d\right)}\right)\right)_{k \in Nat}\right) \Leftrightarrow \operatorname{Summable}\left(\left(\operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{NatCard}\left(\operatorname{RetainedPathDictionary}\left(side, n, K, d, T\right)\right)\right), \operatorname{power}\left(z, T\right)\right)\right)_{T \in Nat}\right)\right) \land \operatorname{tsum}\left(\left(\operatorname{sum}\left(\left(\operatorname{sum}\left(\left(\operatorname{coreMonomial}\left(side, K, d, z, k, v, choices\right)\right)_{choices \in \operatorname{Fin}\left(k\right) \to \operatorname{Product}\left(CuLetter, \operatorname{CoreVertex}\left(side, n, K, d\right)\right)}\right)\right)_{v \in \operatorname{CoreVertex}\left(side, n, K, d\right)}\right)\right)_{k \in Nat}\right) = \operatorname{tsum}\left(\left(\operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{NatCard}\left(\operatorname{RetainedPathDictionary}\left(side, n, K, d, T\right)\right)\right), \operatorname{power}\left(z, T\right)\right)\right)_{T \in Nat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.actual_monomial_series_regrouping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative z, the complete series over letter length k has the same summability and the same real tsum as the series over actual word weight T. Invalid choices contribute zero and are removed by their support. Genuine paths are partitioned by their original total weight; the constructed dictionary equivalence makes each finite fibre sum the retained path count times z to T. The equality includes divergent series, for which both real tsums are zero; summability is stated separately.

**Theorem 1.5 (actual factor path summability).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real, z \in Real,\; \left(\operatorname{lt}\left(0, K\right) \land \left(\operatorname{le}\left(K, n\right) \land \operatorname{le}\left(0, z\right)\right)\right) \Rightarrow \left(\operatorname{Summable}\left(\left(\operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{NatCard}\left(\operatorname{RetainedPathDictionary}\left(side, n, K, d, T\right)\right)\right), \operatorname{power}\left(z, T\right)\right)\right)_{T \in Nat}\right) \Leftrightarrow \operatorname{Summable}\left(\left(\operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{factorCount}\left(\operatorname{MemoryLanguage}\left(side, n, K, d\right), T\right)\right), \operatorname{power}\left(z, T\right)\right)\right)_{T \in Nat}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.actual_factor_path_summability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each actual weight the existing original sandwich bounds the factor count by the path count, and the path count by two to n times the factor count. Nonnegative comparison therefore transfers convergence in both directions with a constant independent of T.

**Theorem 1.6 (original factor series boundary).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real, z \in Real,\; \left(\operatorname{lt}\left(0, K\right) \land \left(\operatorname{le}\left(K, n\right) \land \operatorname{le}\left(0, z\right)\right)\right) \Rightarrow \left(\operatorname{Summable}\left(\left(\operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{factorCount}\left(\operatorname{MemoryLanguage}\left(side, n, K, d\right), T\right)\right), \operatorname{power}\left(z, T\right)\right)\right)_{T \in Nat}\right) \Leftrightarrow \operatorname{lt}\left(\operatorname{weightedRadius}\left(side, n, K, d, z\right), 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.original_factor_series_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original factor power series converges exactly when the original weighted adjacency has spectral radius below one. The result follows through the complete actual path regrouping and the existing spectral path-series supplier, without a supplied growth identity.

**Definition 1.7 (factorLogRate).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right), T \in Nat,\; \operatorname{factorLogRate}\left(X, T\right) = \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{max}\left(1, \operatorname{factorCount}\left(X, T\right)\right)\right)\right), \operatorname{toReal}\left(T\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.factorLogRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The logarithmic quotient uses the max-one count at the original total weight. Its real value at weight zero is zero.

**Theorem 1.8 (factor log rate bounds).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \left(\forall T \in Nat,\; \operatorname{le}\left(0, \operatorname{factorLogRate}\left(X, T\right)\right)\right) \land \operatorname{IsBoundedUnder}\left(le, atTop, \left(\operatorname{factorLogRate}\left(X, T\right)\right)_{T \in Nat}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.factor_log_rate_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every quotient is nonnegative. The finite dictionary bound by three to T plus one bounds the quotients eventually by twice log base two of three, including sparse weights and empty languages.

**Theorem 1.9 (factor rate nonneg).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{le}\left(0, \operatorname{weightedFactorRate}\left(X\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.factor_rate_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every bilateral factor language, the max-one logarithmic rates are nonnegative and bounded above. Their real upper limit is therefore nonnegative, including empty languages and unsupported weights. This bound ensures that rate comparison uses positive convergence exponents.

**Theorem 1.10 (factor rate convergence).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right), s \in Real,\; \operatorname{lt}\left(0, s\right) \Rightarrow \left(\left(\operatorname{lt}\left(\operatorname{weightedFactorRate}\left(X\right), s\right) \Rightarrow \operatorname{Summable}\left(\left(\operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{factorCount}\left(X, T\right)\right), \operatorname{power}\left(\operatorname{power}\left(2, \operatorname{negate}\left(s\right)\right), T\right)\right)\right)_{T \in Nat}\right)\right) \land \left(\operatorname{Summable}\left(\left(\operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{factorCount}\left(X, T\right)\right), \operatorname{power}\left(\operatorname{power}\left(2, \operatorname{negate}\left(s\right)\right), T\right)\right)\right)_{T \in Nat}\right) \Rightarrow \operatorname{le}\left(\operatorname{weightedFactorRate}\left(X\right), s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.factor_rate_convergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every bilateral factor language and every positive real s, the original max-one limsup rate below s implies convergence at z equal to two to minus s, and convergence implies that the rate is at most s. The forward proof uses an eventual geometric majorant strictly between the rate and s. The reverse proof uses terms tending to zero and keeps the max-one convention, so unsupported sparse weights cause no logarithm of zero. No claim about convergence exactly at a generic rate is made.

**Theorem 1.11 (original weighted rate abscissa).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \left(\operatorname{lt}\left(0, K\right) \land \operatorname{le}\left(K, n\right)\right) \Rightarrow \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(side, n, K, d\right)\right) = \operatorname{sInf}\left(\operatorname{setOf}\left(\left(\operatorname{lt}\left(0, s\right) \land \operatorname{lt}\left(\operatorname{weightedRadius}\left(side, n, K, d, \operatorname{power}\left(2, \operatorname{negate}\left(s\right)\right)\right), 1\right)\right)_{s \in Real}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.original_weighted_rate_abscissa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For both actual memory sides and every positive K at most n, the original weightedFactorRate is the infimum of the positive binary exponents whose actual weighted adjacency has radius below one. The set is nonempty and bounded below. This identifies the actual max-one, sparse-weight limsup with the original spectral convergence abscissa.

InteriorRoot identifies this abscissa with the unique interior spectral root for n at least K at least two. It also constructs the lower/upper nesting, closed upper intersection and auxiliary rate sandwich. Graph margins, graph-rate convergence, the full equal-weight auxiliary codebook realization, eventual even allN asymptotics, canonical containing paths, storage/decoder and optimum conclusions require their respective further results.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.actual_factor_path_summability`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.actual_monomial_series_regrouping`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.actual_weight_regrouping`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.core_path_witness_dictionary_card`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.core_path_witness_dictionary_equiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.factorLogRate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.factor_log_rate_bounds`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.factor_rate_convergence`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.factor_rate_nonneg`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.original_factor_series_boundary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.original_weighted_rate_abscissa`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary](SpectralBoundary.md)
