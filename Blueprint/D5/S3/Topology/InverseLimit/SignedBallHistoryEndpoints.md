# Signed endpoints of the actual ordinal history

## Abstract

All signed analytic endpoints on the actual CH limit, without a supplied history or oscillation premise.

**Theorem 1.1 (Oscillation, the whole signed ball, Grothendieck convergence and point sequences).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedBallHistoryEndpoints.actual_signed_ball_history_endpoints`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedBallHistoryEndpoints.actual_signed_ball_history_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

The only premise is continuum = aleph-one. Every conclusion uses exactly K = (SignedOrdinalRealization.finalPrefix hCH).LimitSpace. For arbitrary regular signed t(n) with totalVariation.real(univ)=1, positive Jordan mass at least one half, and variation carried by pairwise disjoint nonempty clopens W(n), there is one clopen Z with infinitely many evaluations at least one sixth and infinitely many exact zeros.

Countable signed reflection and original whole-birth enumeration capture the entire sequence at one original birth and label. Actual treatment cofinality supplies the same selected successor Result. Exact projection and measure identities transport its arbitrary signed G law without changing labels or natural indices. SignedBallHistoryCapture.signed_clopen_collision applies the same actual RawHistory and proper F laws to obtain two distinct free ultrafilters agreeing under every weak-dual evaluation. SignedBallReduction then excludes an injective continuous map from all of StoneCech Nat into the entire real weak-star dual unit ball.

The remaining clauses quantify over arbitrary dual sequences F(n), a dual limit FInf, and all continuous bidual tests Phi: pointwise convergence on C(K,Real) implies convergence under Phi, with no supplied uniform bound. For every point sequence x(n) converging to p in this same K, eventually x(n)=p. Both follow from the proved full regular signed oscillation through SignedGrothendieckCriterion. The joint construction theorem consumes all four clauses.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedBallHistoryEndpoints.actual_signed_ball_history_endpoints`
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalHistory](SignedOrdinalHistory.md)
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalRealizationEvents](SignedOrdinalRealizationEvents.md)
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalSuccessor](SignedOrdinalSuccessor.md)
- Dependency: [D5/S3/Topology/Measures/SignedBallReduction](../Measures/SignedBallReduction.md)
- Dependency: [D5/S3/Topology/Measures/SignedGrothendieckCriterion](../Measures/SignedGrothendieckCriterion.md)
