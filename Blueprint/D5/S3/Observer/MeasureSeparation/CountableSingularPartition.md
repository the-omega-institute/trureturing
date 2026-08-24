# Countable Pairwise Singular Common Partition

## Abstract

Pairwise singular probability laws have a common measurable partition into full-measure supports.

**Theorem 1.1 (Pairwise singular laws have disjoint full-measure supports).**

$$\forall \alpha: \operatorname{Type}, [\operatorname{MeasurableSpace}\left(\alpha\right)],\\{}P: \mathbb{N} \to \operatorname{Measure}\left(\alpha\right), a: \mathbb{N} \to \operatorname{ENNReal},\\{}(\forall n, \operatorname{ProbabilityMeasure}\left(P_{n}\right)) \land (\forall n, 0 < a_{n}) \land \sum_{n \in \mathbb{N}} a_{n} = 1 \land\\{}(\forall n, m, n \neq m \Rightarrow \operatorname{MutuallySingular}\left(P_{n}, P_{m}\right))\\{}\Rightarrow \operatorname{let} \lambda = \sum_{n \in \mathbb{N}} a_{n} P_{n}, f = (n \mapsto \frac{\mathrm{d}P_{n}}{\mathrm{d}\lambda})\;\\{}(\forall n, m, n \neq m \Rightarrow f_{n} f_{m} = 0 \lambda\text{ almost everywhere}) \land\\{}\exists A: \mathbb{N} \to \operatorname{Set}\left(\alpha\right), (\forall n, \operatorname{Measurable}\left(A_{n}\right)) \land \operatorname{PairwiseDisjoint}\left(A\right) \land\\{}(\forall n, P_{n}(A_{n}) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/CountableSingularPartition.countable_pairwise_singular_common_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P_n be countably many probability laws on one measurable transcript space. Positive normalized weights construct their mixture lambda, and f_n is the Radon--Nikodym derivative of P_n with respect to that mixture.

Pairwise mutual singularity forces f_n f_m to vanish lambda-almost everywhere whenever n and m differ. This is the density form of the separation claim in the source.

The nonzero density supports are measurable and pairwise disjoint up to lambda-null sets. The countable measurable refinement theorem removes those overlaps simultaneously, producing genuinely pairwise disjoint measurable sets A_n. Absolute continuity transfers the refinement equality back to every P_n, so each law assigns its own set mass one.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/CountableSingularPartition.countable_pairwise_singular_common_partition`
