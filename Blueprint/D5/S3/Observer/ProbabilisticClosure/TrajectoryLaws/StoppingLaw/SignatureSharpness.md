# Exact signature radius and a radius-zero law representative

## Abstract

Exact signature radius and a radius-zero law representative

SignatureRadius(j,k,R) requires a same-signature representative of height at most k for every original tree of height at most k, with every potential address within R of the target. Uniform compression makes the set of such natural radii nonempty before its least member signatureRadius is taken.

**Theorem 1.1 (Exact signature radius with unchanged-seed law equality).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureSharpness.exact_signature_radius_with_law_zero_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureSharpness.exact_signature_radius_with_law_zero_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean target j and natural k at least one, signatureRadius(j,k)=2^(k+1)-1. The complete tree W=completePathTree(not j,k,j+1) has height k and M=2^k-1 potential read occurrences. Every same-signature tree contains an address at distance at least 2^(k+1)-1 from j. The full signature forces a single directed detached path through all M potential occurrences, including those on incompatible branches, before the integer-path separation bound is applied. The tree repeatTargetTree(j,k) has height k and every potential address equals j. For every measurable seed type U, every measure nu and every permitted Bias, realizing this repeated-target tree gives a lawful RawRule with total cap k and actual radius zero, whose full unchanged-seed law equals that of W. Both executions return a_false after exactly k paid reads, so replies can be ignored without erasing the read costs. This radius-zero comparison does not preserve the full signature and gives no exponential lower bound for law-only compression.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureSharpness.exact_signature_radius_with_law_zero_witness`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression](SignatureCompression.md)
