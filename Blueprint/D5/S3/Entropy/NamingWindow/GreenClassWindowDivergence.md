# Green-Class Window Divergence

## Abstract

Finite naming-window KL divergence is additive across coordinates, identifies the uniform entropy defect, and vanishes exactly at coordinatewise agreement.

**Theorem 1.1 (Window divergence is the sum of coordinate divergences).**

$$\operatorname{KL}(\operatorname{windowLaw}(p), \operatorname{windowLaw}(q)) = \sum_{i} \operatorname{KL}(p_{i}, q_{i}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_windowLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized coordinate laws p_i and strictly positive p_i and q_i, the logarithm of the quotient of the two coordinate products splits into a finite sum. Interchanging the finite sums isolates one KL term per coordinate.

Normalization is required only for p in this additivity theorem. Strict positivity keeps the product logarithm and every coordinate quotient in the elementary real-valued KL regime used by the proof.

**Theorem 1.2 (Uniform coordinates give the uniform window law).**

$$\operatorname{windowLaw}(u) = (w\mapsto \operatorname{card}(W)^{-1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.windowLaw_uniform_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here u is the coordinate law with constant mass one over card O, and W is the finite type of assignments from the coordinate set to O. The coordinate product is therefore the reciprocal of card W at every assignment.

**Theorem 1.3 (Uniform window divergence is the naming entropy defect).**

$$\operatorname{KL}(\operatorname{windowLaw}(p), \operatorname{windowLaw}(u)) = n \times (\operatorname{namingDim}(O) \times \log{2}) - H(\operatorname{windowLaw}(p)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_windowLaw_uniform_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonnegative normalized coordinate family p and a nonempty alphabet O, the product window law is normalized. Divergence from the uniform assignment law is therefore its log-cardinality entropy deficit.

The cardinality of the assignment type is card O raised to the number n of coordinates. Taking its logarithm and using the definition of namingDim gives the displayed defect in nats.

**Theorem 1.4 (Zero window divergence characterizes coordinatewise agreement).**

$$\operatorname{KL}(\operatorname{windowLaw}(p), \operatorname{windowLaw}(q)) = 0 \Leftrightarrow \forall i, p_{i} = q_{i}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_windowLaw_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative normalized and strictly positive coordinate laws p and q, additivity expresses window divergence as a sum of nonnegative coordinate divergences. A zero sum forces every coordinate term to vanish, and Gibbs equality then gives p_i = q_i.

Strict positivity is retained deliberately. Extending the result to coordinate laws with zero support requires a separate support-aware generalization and is outside this module.

**Theorem 1.5 (Green-class window divergence is the coordinate sum).**

$$\operatorname{KL}(\operatorname{windowLaw}(\operatorname{coordLaw}(mu)), \operatorname{windowLaw}(\operatorname{coordLaw}(nu))) = \sum_{i \in S} \operatorname{KL}(\operatorname{coordLaw}(mu, i), \operatorname{coordLaw}(nu, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_greenClass_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two families of probability measures, each finite green-class window is the product of the singleton coordinate masses indexed by S. Under strict positivity, window additivity identifies its KL divergence with the sum of the coordinate divergences over S.

The proof re-establishes two helpers that are private in the frozen GreenClassWindowEntropy module: finite sum-product factorization and normalization of coordinate singleton masses. Their proofs are repeated here because a frozen module cannot be reopened merely to export them.

## References

- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_greenClass_window`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_windowLaw`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_windowLaw_eq_zero_iff`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.klDivergence_windowLaw_uniform_eq`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence.windowLaw_uniform_eq`
- Dependency: [D5/S3/Divergence/StrictGibbs](../../Divergence/StrictGibbs.md)
- Dependency: [D5/S3/Entropy/EntropyDivergenceIdentity](../EntropyDivergenceIdentity.md)
- Dependency: [D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy](GreenClassWindowEntropy.md)
