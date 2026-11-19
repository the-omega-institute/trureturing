# The static alternating completion law

## Abstract

Mass and conditioning on a fixed extension event in the uniform alternating full-cycle law.

**Theorem 1.1 (Exact mass and conditioning for alternating forest completions).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingCompletionLaw.alternating_completion_law`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/AlternatingCompletionLaw.alternating_completion_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (1989). *Generalized rook polynomials and orthogonal polynomials*. DOI: [10.1007/978-1-4684-0637-5_13](https://doi.org/10.1007/978-1-4684-0637-5_13).

*Commentary.*

The carrier has n labels of each of two colors, with n positive. The prescribed relation is right-unique, left-unique and acyclic, and its edges change color. Its actual tails and heads correspond to the weak components, including isolates. The alternating completions are in bijection with compatible cycles on these components, with the same tail-to-head connector equation as in the classification theorem.

There is a uniform probability mass on the actual alternating full cycles of the original carrier, with mass 1 divided by n! times (n−1)! at each cycle. The event of extending all prescribed edges has outer measure M divided by n! times (n−1)!, where M counts the actual alternating completions. This event has positive mass exactly when a completion exists.

For every support witness of the event, filtering the ambient mass is the pushforward along inclusion of a uniform mass on the completions. Under the same completion mass, the pushforward along the endpoint equivalence gives 1/M to every compatible component cycle.

The specialization of the two-state inventory to opposite target colors counts the ambient cycles. The extension event and the completion subtype have the same underlying permutations. The finite uniform event formula and transport through these equivalences give the stated probabilities.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingCompletionLaw.alternating_completion_law`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/CompatibleCycleInventory](CompatibleCycleInventory.md)
