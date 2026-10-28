# Actual subset counts and Howroyd's generating identity

## Abstract

The full original generating identity for all labelled mutual-visibility subsets of the Andrasfai graphs.

For every original n ≥ 1 put m = n - 1. The host has vertex set Z/(3m+2), with u adjacent to v exactly when the canonical representative of v-u is congruent to one modulo three. Thus it is Cay(Z/(3n-1), {1,4,...,3n-2}). A Configuration is any finite labelled vertex subset S such that every distinct pair in S admits a shortest path in this original host whose other vertices avoid S. The empty set and singletons are included. Write c(m) = Andrasfai.count m for the cardinality of this actual Configuration subtype; it is defined independently of any word or matrix.

**Definition 1.1 (Actual configurations and labelled periodic words).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.configurationEquivPeriodicWord`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.configurationEquivPeriodicWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m ≥ 1, configurationEquivPeriodicWord m is an equivalence between Configuration(host m) and the subtype of functions labels : Fin (3m+2) → Bool for which PeriodicAvoidance(List.ofFn labels) holds. It restricts AndrasfaiWords.subsetLabelsEquiv using visible_iff_word_periodic_avoidance. Every vertex label and the origin are retained. PeriodicAvoidance excludes the entire forbidden family from every finite repetition, including factors crossing the labelled boundary.

**Theorem 1.2 (Uniform actual graph counts).**

$$\forall (m : \mathbb{N}), 1 \le m \Rightarrow (\operatorname{count}\left(m\right) : \mathbb{Q}) = \operatorname{trace}\left(M^{3 \cdot m + 2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.count_eq_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here M is AndrasfaiTransfer.transfer, the rational four-state labelled-edge matrix with entry two from state 3 to state 1. Cardinality transport along the actual configuration equivalence and AndrasfaiEnumeration.periodic_word_card_eq_trace give the equation. Its hypotheses hold because 3m+2 is positive and not divisible by three. The trace counts the full Boolean labelling, with the two labels on a shared edge counted separately.

**Definition 1.3 (The series defined from original subset counts).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.generatingSeries`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In Q[[X]], A = generatingSeries is defined as X times PowerSeries.mk(fun m => (Andrasfai.count m : Q)). Consequently its constant coefficient is zero, and for every original n ≥ 1 its coefficient at X^n is c(n-1), the number of all labelled actual visible subsets of the original graph. This is the formal meaning of the sum over n ≥ 1; it introduces no graph of index zero.

**Theorem 1.4 (The original first coefficient).**

$$\operatorname{generatingSeries} = \operatorname{traceSeries} + X$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.generatingSeries_eq_corrected_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficients at all n ≥ 2 agree by count_eq_trace. At n = 1, AndrasfaiWords.count_zero gives four actual subsets of ZMod 2, whereas tr(M^2) is three. Hence exactly X must be added to the uncorrected traceSeries. Both constant coefficients are zero.

**Theorem 1.5 (The full original rational identity).**

$$\operatorname{generatingSeries} = \frac{X \cdot (4 - 19 \cdot X + 33 \cdot X^{2} - 40 \cdot X^{3} + 8 \cdot X^{4})}{1 - 10 \cdot X + 29 \cdot X^{2} - 32 \cdot X^{3} + 8 \cdot X^{4}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a391632-andrasfai-mutual-visibility` (proved) by `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a391632-andrasfai-mutual-visibility","declaration_gid":"D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.result","resolution_kind":"proved"} -->

*Citation.* Andrew Howroyd; Eric W. Weisstein (2026). *OEIS A391632: mutual-visibility subsets of Andrasfai graphs*. URL: <https://oeis.org/A391632/internal>.

*Commentary.*

Substitution into AndrasfaiTransfer.corrected_trace_series gives the entire numerator and denominator, including the original n = 1 coefficient. The denominator has constant coefficient one, and the displayed quotient denotes multiplication by its formal power-series inverse. The identity holds coefficientwise in Q[[X]], without analytic convergence assumptions. It counts all actual labelled existential shortest-path mutual-visibility subsets; it imposes no maximality, independence, or quotient condition.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.configurationEquivPeriodicWord`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.count_eq_trace`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.generatingSeries`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.generatingSeries_eq_corrected_trace`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.result`
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiEnumeration](AndrasfaiEnumeration.md)
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords](AndrasfaiWords.md)
