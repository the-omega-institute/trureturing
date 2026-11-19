# Guessing an available name after a partial observation

## Abstract

Conditional laws for a finite random injective naming.

**Theorem 1.1 (A name hits with probability equal to the remaining density).**

Lean statement: `D5/S3/Combinatorics/Probability/PartialNameAssignment.uniform_remaining_name_hit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/PartialNameAssignment.uniform_remaining_name_hit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an injection uniformly from a finite vertex set into a finite name set. Fix an injective naming on a subset of vertices and an available name set disjoint from those fixed names. Condition on agreement with the fixed naming and on every other vertex receiving an available name. Assume a consistent injection exists.

The conditional law is uniform on consistent injections. For each available name, its mass of being assigned to one of the remaining vertices is the number of remaining vertices divided by the number of available names.

Restricting a consistent injection to the remaining vertices gives a bijection with injections into the available name set. Swapping two available names exchanges the corresponding evaluation fibers. Each remaining vertex therefore has the same probability of taking the given name. Injectivity makes the hit events for different vertices disjoint.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/PartialNameAssignment.uniform_remaining_name_hit`
- Dependency: [D5/S0/Diagonal/Probability/EquivariantEscape](../../../S0/Diagonal/Probability/EquivariantEscape.md)
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletion](../Graph/LinearForests/DirectedForestCompletion.md)
