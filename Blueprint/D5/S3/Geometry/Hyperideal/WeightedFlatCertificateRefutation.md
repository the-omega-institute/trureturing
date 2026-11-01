# Acyclicity and weighted polynomial refutation

## Abstract

Positive flat-candidate gaps rule out dependency cycles and weighted certificates.

A candidate relation C(a,b,c) records a distinguished opposite pair a and the two other pairs b and c. The directed dependency graph sends a to both b and c. A shared positive potential z satisfies z(a) >= 1 + z(b) + z(c) for every candidate, so every dependency edge strictly decreases z.

For a finite family of selected candidates, attach nonnegative weights with at least one positive weight. The weighted gap is the sum of each weight times z(a)-z(b)-z(c). The candidate inequalities and positivity force this gap to be strictly positive. A certificate asserting that the same gap is nonpositive therefore yields a contradiction, while the strict decrease independently excludes every directed cycle.

**Theorem 1.1 (Cycle exclusion and weighted certificate refutation).**

$$\forall Q \in Type,\; \forall Sigma \in Type,\; \forall z \in Function\left(Q, Real\right),\; \forall C \in Function\left(Q, Function\left(Q, Function\left(Q, Prop\right)\right)\right),\; \forall weights \in Function\left(Sigma, Real\right),\; \forall q \in Function\left(Sigma, Q\right),\; \forall q1 \in Function\left(Sigma, Q\right),\; \forall q2 \in Function\left(Sigma, Q\right),\; \left(\left(\forall v \in Q,\; 1 < z\left(v\right)\right) \land \left(\left(\forall a \in Q,\; \forall b \in Q,\; \forall c \in Q,\; C\left(a, b, c\right) \Rightarrow z\left(a\right) \ge 1 + z\left(b\right) + z\left(c\right)\right) \land \left(\left(\forall sigma \in Sigma,\; 0 \le weights\left(sigma\right)\right) \land \left(\left(\exists sigma \in Sigma,\; 0 < weights\left(sigma\right)\right) \land \left(weightedGap\left(weights, z, q, q1, q2\right) \le 0 \land \left(\forall sigma \in Sigma,\; C\left(q\left(sigma\right), q1\left(sigma\right), q2\left(sigma\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(-HasDirectedCycle\left(candidateEdge\left(C\right)\right) \land False\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/WeightedFlatCertificateRefutation.flat_candidate_cycle_and_certificate_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reuses the shared positive-length cycle theorem for the graph conclusion. It then sums the pointwise lower bounds for the weighted gaps; one strictly positive weight makes the sum of weights positive. The nonpositive certificate contradicts that strict lower bound.

The result is an abstract finite certificate criterion. It does not assert that a particular geometric candidate exists, nor does it replace the separate derivation of the candidate inequalities from a realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/WeightedFlatCertificateRefutation.flat_candidate_cycle_and_certificate_refutation`
- Dependency: [D5/S3/Geometry/Hyperideal/FlatCandidateAcyclicity](FlatCandidateAcyclicity.md)
