# Actual Physical Sampling Probability Bridge

## Abstract

Actual uniform iid physical full-recovery probabilities equal factorial times the existing represented spanning polynomial at uniform physical weights.

**Theorem 1.1 (All-Horizon Full-Space Recovery Probability).**

Lean statement: `D5/S3/Resource/SimplexCoverageProbability.uniformSamples_recovered_top`

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SimplexCoverageProbability.uniformSamples_recovered_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural t, the existing MinimumRetrievalTime.uniformSamples measure of the existing recovered columns top t event equals ENNReal.ofReal of t! times spanningPolynomial columns bot t evaluated at the constant real coordinate 1/card Index.

Disjoint measurable finite prefix-word cylinders partition exactly the actual top-recovery event. The infinite product cylinder formula gives each word probability (1/card Index)^t. Evaluating the spanning-filtered word polynomial gives the same finite sum, and the rational factorial identity identifies it with the original reciprocal-factorial spanning polynomial.

The field and ambient module are arbitrary, with no finite-dimensional or spanning premise. All physical indices, including zero, repeated and scalar-parallel columns, remain in the original iid alphabet. The alphabet must be nonempty for the specified uniform measure, and has measurable singletons. Degree zero, zero ambient space and unspanned families are included. No projective pushforward or alternative expected-time definition is introduced.

Projective transport, orbit averaging, zero-column replacement and the all-horizon probability comparison remain separate obligations. The existing retrieval_time_probability_bridge supplies the original tail and expectation transfer after the required comparison and spanning hypotheses are established. The named optimizer remains open.

## References

- Truth anchor: `D5/S3/Resource/SimplexCoverageProbability.uniformSamples_recovered_top`
- Dependency: [D5/S3/Resource/MinimumRetrievalTime](MinimumRetrievalTime.md)
- Dependency: [D5/S3/Resource/SimplexCoverageWords](SimplexCoverageWords.md)
