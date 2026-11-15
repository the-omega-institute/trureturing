# Stationary finite-history entropy envelope

## Abstract

HistoryEnvelope

Let X be a standard Borel measurable space, mu a probability measure, T a measurable map preserving mu, and P a finite measurable partition with index set I. Cells cover X and are pairwise disjoint modulo mu; zero-mass cells are allowed. Write P at time j for its pullback by the jth iterate of T, and B_n for the join of times 0 through n-1, with B_0 the one-cell partition. All entropies use natural logarithms.

**Theorem 1.1 (Every finite history bounds the partition entropy rate).**

$$\forall (X : \operatorname{StandardBorelSpace}), \forall (mu : \operatorname{ProbabilityMeasure} X), \forall (T : X \to X), \operatorname{MeasurePreserving} T mu mu \to \forall (I : \operatorname{FiniteType}), \forall (P : \operatorname{MeasurePartition} mu I), \forall (n : \mathbb{N}), {\operatorname{h}_{mu}}(T,P) \le {\operatorname{H}_{mu}}({P_{n}} \Vert {B_{n}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/HistoryEnvelope.ksEntropyPartition_le_history_conditionalEntropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here h_mu(T,P) is the existing Fekete limit of H_mu(B_m)/m. The finite joint mass w_n(a,b) is mu of the intersection of the B_n cell a with the time-n P cell b, for a in I^{Fin n} and b in I. H_mu(P_n given B_n) denotes conditionalEntropy(w_n), with row mass equal to the actual B_n mass. The conditional row is zero on a zero-mass history, so that history contributes zero. The bound holds for every natural n, including zero, and places no Markov, ergodicity or entropy-limit assumption on the measure.

Set c_n = H_mu(P_n given B_n). Conditioning on B_{n+1} is stronger than conditioning on the shifted B_n. Joint pullback invariance under the same measure-preserving T therefore gives c_{n+1} <= c_n. The existing finite partition chain rule gives H_mu(B_{n+1}) = H_mu(B_n) + c_n. Induction yields H_mu(B_{n+m}) <= H_mu(B_n) + m c_n. Divide by n+m and pass to the existing Fekete limit: the fixed boundary term tends to zero, giving h_mu(T,P) <= c_n. The finite-conditioning bridge identifies this with the displayed finite joint-law conditional entropy.

This is a standard stationary-process entropy-rate relationship. Finite chain rules, conditioning monotonicity, joint pullback invariance and the Fekete limit are reused from the existing KolmogorovSinai modules. The result concerns a partition rate; equating it with the supremum over all finite partitions requires a separate generating-partition theorem. Applying it to a specified symbolic coordinate additionally requires a measurable partition and the exact correspondence between its iterates and that coordinate.

## References

- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/HistoryEnvelope.ksEntropyPartition_le_history_conditionalEntropy`
- Dependency: [D5/S3/Entropy/ConditionalEntropy](../ConditionalEntropy.md)
- Dependency: [D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning](GeneratorConditioning.md)
