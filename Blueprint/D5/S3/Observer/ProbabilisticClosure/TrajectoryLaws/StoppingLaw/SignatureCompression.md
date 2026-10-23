# Uniform compression with the original seed

## Abstract

Uniform compression with the original seed

For a finite set E of integer edge left endpoints, the occupied vertices are the target q and the endpoints of the specified edges. Connectivity requires each intervening unit edge to belong to E. It does not add an edge merely because two occupied vertices are adjacent. The target component stays fixed; the other interval components are ordered by their original minima and translated according to the shortest prefix reaching the component-count threshold.

**Remark 1.1 (Stopping laws and the universal objective).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.original_rule_stopping_results`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.original_rule_stopping_results` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every permitted Bias, either target, positive budget k and unchanged seed probability space, the stopping witness has minimum law-preserving radius 2k+1. Every lawful capped representative of its full law reads at distance at least 2k+1 with probability at least (1+p^k+(1-p)^k)/2, and the stopping witness attains equality. These stopping-law conclusions combine with uniform compression to give the universal linear lower bound, exponential upper bound and exact values at budgets zero and one. They do not resolve the polynomial-versus-superpolynomial universal radius question.

**Theorem 1.2 (Interval decomposition of specified edges).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.integer_line_component_intervals`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.integer_line_component_intervals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite integer edge set and integer target admit maximal ordered component intervals, an exact partition of the specified edges and the total edge-count identity. The component containing the target is unique; every detached component has strictly positive edge length. These are constructed without supplying a decomposition as a hypothesis.

**Theorem 1.3 (Canonical component translations).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.canonical_target_fixed_packing`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.canonical_target_fixed_packing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every E and q, CanonicalTargetPacking supplies the ordered shortest-prefix split and its displayed component translation formula. Its map is injective on all occupied vertices, fixes the entire target component, acts by translation on every component, preserves each directed queried edge, and places every queried left endpoint between q minus card(E) and q plus card(E). Empty E and zero or one detached component are included.

**Theorem 1.4 (One address tree for both phases).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.bounded_signature_relabeling`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.bounded_signature_relabeling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean j, read tree T and natural k with height(T) at most k, compressedTree(j,T) has the same complete signature and exactly the original height. All its potential addresses lie between j minus 2(2^k-1) and j plus 2(2^k-1)+1. Each node receives one address before execution using its own parity. The tree construction has no Bias parameter. The number of distinct edges in each phase is bounded by the potential occurrence count, which is at most 2^k-1.

**Theorem 1.5 (Formal bounds imply actual bounds).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.normalized_actual_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.normalized_actual_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable seed type, capped RawRule, target j and natural radius, a radius bound on every potential address of every normalized seed tree bounds every address in every actual read prefix. This includes exceptional executions and nonreturns.

**Theorem 1.6 (Full joint-law representatives and least radii).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.completed_rule_uniform_compression`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.completed_rule_uniform_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable seed type U, probability measure nu, permitted Bias, Boolean target j and natural budget k, every completed rule lawful for the original source product and capped on all paths has a lawful RawRule representative on the same seed space. The representative preserves the complete joint law of seed, hidden target, output, return indicator and paid count. It is capped by k on all paths, has actual radius at most 2^(k+1)-1, and has radius zero when k is zero. Every normalized seed tree has height at most k and every potential address lies in the same compression window. No extra random seed or access to the hidden phase is used. UniversalRadius quantifies over all lawful completed inputs; its uniformly sufficient radii are nonempty before rhoLaw is defined by Nat.find. The same conclusion gives rhoLaw(0)=0, rhoLaw(1)=3, the lower bound 2k+1 for k at least one, and the upper bound 2^(k+1)-1. The lower bound reuses stopping-law rigidity. The growth rate between these bounds remains unresolved.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.original_rule_stopping_results`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.bounded_signature_relabeling`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.canonical_target_fixed_packing`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.completed_rule_uniform_compression`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.integer_line_component_intervals`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression.normalized_actual_radius`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw](SeedLaw.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature](WholeTreeSignature.md)
