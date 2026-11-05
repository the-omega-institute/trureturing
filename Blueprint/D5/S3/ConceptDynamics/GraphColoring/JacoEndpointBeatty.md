# The recursive Jaco endpoint law

## Abstract

The actual recursively constructed Jaco endpoints are golden Beatty endpoints at every natural index.

**Theorem 1.1 (The source recurrence).**

$$\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\operatorname{jacoRight}\left(n\right) = 2 \cdot n - \operatorname{card}\left(\{i: \mathrm{Nat} \mid (1 \le i) \land ((i < n) \land (n \le \operatorname{jacoRight}\left(i\right)))\}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.endpoint_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every positive n, the endpoint is twice n minus the number of positive earlier endpoints reaching n. Prefix agreement of the existing array construction identifies every stored entry with its original endpoint; this connects the array implementation to the source recurrence.

**Definition 1.2 (The Beatty outdegree candidate).**

Lean statement: `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.beattyOut`

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.beattyOut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural index n, beattyOut n is the natural floor of (n+1) divided by the golden ratio. Its identification with an actual graph quantity is proved through the recursive endpoint law.

**Theorem 1.3 (Positive outdegree bounds).**

$$\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow ((1 \le \operatorname{beattyOut}\left(n\right)) \land (\operatorname{beattyOut}\left(n\right) \le n))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.beatty_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive n, the candidate lies between one and n, using the golden ratio strictly between one and two.

**Theorem 1.4 (Invert the endpoint threshold).**

$$\forall n \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; (n \le i + \operatorname{beattyOut}\left(i\right)) \Leftrightarrow (\operatorname{beattyOut}\left(n\right) \le i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.beatty_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural n and i, the candidate endpoint at i reaches n exactly when i is at least beattyOut n. The golden-ratio floor identity and irrationality account for the strict boundary; no equality case is discarded without proof.

**Theorem 1.5 (The actual all-order endpoint).**

$$\forall n \in \mathrm{Nat},\; \operatorname{jacoRight}\left(n\right) = n + \operatorname{beattyOut}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.endpoint_eq_beatty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction replaces each earlier recursive endpoint by its proved Beatty value. The incoming indices become exactly the interval from beattyOut n through n-1, whose cardinality is n minus beattyOut n. Substituting this count in the source recurrence gives the endpoint law. Index zero remains only the unused table entry.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.beattyOut`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.beatty_bounds`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.beatty_threshold`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.endpoint_eq_beatty`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.endpoint_recurrence`
- Dependency: [D5/S0/Certificates/JacoExponentialDominationRefutation](../../../S0/Certificates/JacoExponentialDominationRefutation.md)
