# Prescribed connectors in compatible cycles

## Abstract

Exact probabilities for a prescribed connection in a compatible labelled cycle.

**Theorem 1.1 (The mass of a specified successor).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingConnectorLaw.connector_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/AlternatingConnectorLaw.connector_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paidi Creed; Mary Cryan (2013). *The number of Euler tours of random directed graphs*. DOI: [10.37236/2377](https://doi.org/10.37236/2377).

*Commentary.*

Each label of a finite set C has a source color s and a destination color d, both Boolean. A compatible cycle is a single-orbit permutation σ on the nonempty set C with d(z) = s(σ(z)) at each label. Let μ be a probability mass function assigning the reciprocal of the number of compatible cycles to each cycle. Fix distinct labels x and y.

The event σ(x) = y has probability zero when s(y) differs from d(x). When the colors agree, remove x, assign source color s(x) to y, and keep the destination colors and the other source colors. Write R for the remaining label set, a and b for the counts of its two source colors, m for its number of false-to-true transitions, and p and q for its false-to-false and true-to-true transition counts.

The event probability is M divided by the original compatible-cycle count. If m is positive then M equals m(a−1)!(b−1)!. If m is zero and p or q is zero then M equals (|R|−1)!. If m is zero and both p and q are positive then M is zero. The theorem expresses the event probability as outer measure on the finite carrier.

Removing x from a cycle with the specified successor redirects the incoming edge of x to y. Inserting x immediately before y reverses this operation. Color compatibility at the redirected edge is exactly the source-color update above. The transition-color counts stay balanced and the existing compatible-cycle inventory theorem supplies M. For an alternating directed forest, s is the color of a component's head and d is the opposite of the color of its tail.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingConnectorLaw.connector_mass`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/CompatibleCycleInventory](CompatibleCycleInventory.md)
