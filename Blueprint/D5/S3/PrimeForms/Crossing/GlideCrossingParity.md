# Glide Crossing Parity

## Abstract

A fixed-point-free glide involution pairs a finite crossing set into two-element orbits.

**Theorem 1.1 (A glide pairing makes the crossing count even).**

$$\forall X,\ [\operatorname{Fintype}(X)],\ \forall g: X \to X,\ (\forall x, g(g(x)) = x) \land (\forall x, g(x) \neq x) \Rightarrow \operatorname{Even}(\operatorname{card}(X)).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/GlideCrossingParity.glide_crossing_count_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be an involution of a finite crossing set with no fixed points. Join each crossing x to g(x). Involutivity makes adjacency symmetric, while the fixed-point-free hypothesis removes loops.

Every vertex in the resulting simple graph has the unique neighbor g(x), so the full graph is a perfect matching. Mathlib's theorem SimpleGraph.Subgraph.IsPerfectMatching.even_card then gives even cardinality without reproving the matching parity theorem.

This closes only the even-crossing assertion in remark 27.479-27.480. It does not formalize the numerical crossing counts, the Pell trace identification, or the rejected multiplicity model.

Repository search found no equivalent D5 declaration. Pinned-Mathlib search found and reused IsPerfectMatching.even_card; no direct fixed-point-free involution parity theorem was found. Loogle had no matching declaration, and GitHub code search required authentication.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/GlideCrossingParity.glide_crossing_count_even`
