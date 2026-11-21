# Coupling opposite parity rows

## Abstract

The common true-flag masses for opposite three-bit parity laws form a tetrahedron.

**Theorem 1.1 (Exact region of simultaneous common flag masses).**

$$F(a,b,c) \iff 0 \leq a \land 0 \leq b \land 0 \leq c \land a \leq b + c \land b \leq c + a \land c \leq a + b \land a + b + c \leq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityProfileRegion.attainable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first row is uniform on the four even three-bit profiles. The second is uniform on the four odd profiles. For real masses a, b and c, let F(a,b,c) assert the existence of a nonnegative coupling with these row marginals whose three true-in-both-rows probabilities are a, b and c.

Both marginals are fair in each coordinate, so each agreement probability is twice its true-in-both-rows probability. The difference of the coupled profiles can flip one coordinate or all three. Its four masses are nonnegative and sum to one, which gives the listed inequalities.

Conversely, choose the single-coordinate flips with probabilities b+c-a, c+a-b and a+b-c. Choose the triple flip with the remaining probability 1-a-b-c. Applying the sampled flip to an independent uniform even profile gives a uniform odd profile and the prescribed common masses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityProfileRegion.attainable_iff`
