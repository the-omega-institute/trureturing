# Blow-ups and asymptotic graph maxima

## Abstract

Independent-class blow-ups and the limit of normalized graph Ky Fan maxima.

**Definition 1.1 (Independent-class blow-up matrix).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.blowUpMatrix`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.blowUpMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

The matrix replaces each entry of A by a constant square block of order t. For an adjacency matrix, each vertex is replaced by t independent vertices, and each original edge becomes a complete bipartite graph.

**Theorem 1.2 (Blow-up lower bound for a graph).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.kyFan_blowUp_le_xi`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.kyFan_blowUp_le_xi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

For positive t, the maximum at order mt is at least t times the Ky Fan sum of G. Truncate the prefix at the original dimension when necessary. Repeat each coordinate of an attaining signed orthonormal family t times and divide by sqrt(t). Inner products remain unchanged, and the adjacency operator scales its pairing by t.

**Theorem 1.3 (Monotonicity under isolated vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.xi_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.xi_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

For m at most n, the maximum at order m is no larger than that at order n. Embed the graph, add isolated vertices, and extend every vector of an attaining signed family by zero.

**Theorem 1.4 (Blow-up lower bound for the maximum).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.xi_blowUp`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.xi_blowUp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

Taking a graph that attains the finite maximum yields xi(k,mt) at least t times xi(k,m), provided t is positive.

**Definition 1.5 (Normalized supremum).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.normalizedSupremum`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.normalizedSupremum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

The value is the supremum of xi(k,m)/m over all orders m at least k, expressed by the index m+k.

**Theorem 1.6 (Existence and value of the normalized limit).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.tendsto_xi_div`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.tendsto_xi_div` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High (2026). *Formal rectangular singular-value variational bounds*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace>.

*Commentary.*

For every positive k, xi(k,n)/n converges to its supremum over orders at least k. The universal zero-one matrix bound bounds this supremum by (1+sqrt(k))/2. For a fixed order m, use floor(n/m) copies of each vertex and fill the remaining positions with isolated vertices. The resulting lower bound is (1-(n mod m)/n) times xi(k,m)/m. The remainder ratio tends to zero. Taking m with normalized maximum above any chosen lower threshold proves the lower limit bound; the supremum gives the upper bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.blowUpMatrix`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.kyFan_blowUp_le_xi`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.normalizedSupremum`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.tendsto_xi_div`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.xi_blowUp`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/BlowUp.xi_mono`
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/Upper](Upper.md)
