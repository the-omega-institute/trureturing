# Square-Free Source Jets as Cyclic Traces

## Abstract

A square-free source jet is the normalized sum of all ordered cyclic trace words.

**Theorem 1.1 (The full source coefficient is the permutation trace sum).**

$$\begin{gathered}k > 0 \Rightarrow\\{}\operatorname{sourceJetCoefficient}(B) = \frac{1}{k} \sum_{\pi \in S_{k}} \operatorname{Tr}(\prod_{j=1}^{k} B_{\pi(j)}) \land\\{}k \neq 0 \land\\{}squareFreeWord \iff bijection \land\\{}\operatorname{Tr}(ABC) = \operatorname{Tr}(CAB).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/SourceJetCyclicTraces.source_jet_is_closed_cyclic_traces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B_i be a finite family of square matrices and let k be positive. A source word survives the square-zero source rule exactly when every source label occurs at one unique position.

Those surviving words are canonically equivalent to permutations of Fin k. Reindexing the finite sum gives the displayed coefficient with the nonzero 1/k normalization inherited from the kth term of the formal negative log-determinant expansion.

The final clause applies the pinned matrix trace cyclicity theorem, so the ordered traces may also be grouped by cyclic word classes.

## References

- Truth anchor: `D5/S3/Observer/SourceJetCyclicTraces.source_jet_is_closed_cyclic_traces`
