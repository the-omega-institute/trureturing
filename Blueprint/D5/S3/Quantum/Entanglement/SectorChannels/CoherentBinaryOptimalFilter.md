# Optimal filters for a coherent binary replacement target

## Abstract

Exact equality in the smaller-Schmidt filter score singles out the largest diagonal-optimal filter.

**Theorem 1.1 (The largest diagonal-optimal filter and its tie).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/CoherentBinaryOptimalFilter.largest_optimal_filter`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SectorChannels/CoherentBinaryOptimalFilter.largest_optimal_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the smaller resource mass q and a smaller positive target weight w. For the matched-diagonal score in the symmetric rank-one filter family there are two clipping thresholds, defined algebraically by w=q(2t1-t1 squared)=q t2 squared. The proof maximizes the literal clipped score, identifies every equality case, and selects the largest such filter. Below the transition 2w=q only t1 is optimal, above it only t2 is optimal, and at the transition both optimize.

The proof uses strict monotonicity outside the two thresholds and an explicit strict chord gap for the intervening convex quadratic. It adds the equality classification and largest-attainer law, not another statement of the previously formalized optimum value.

Paper motivation, not a Lean conclusion: in the fixed pure Schmidt state model with no communication or shared seed, a common filter retains matched coherence of magnitude at most ab times its strength. The paper argument also classifies optimizing CPTP pairs and equality in trace-norm pinching; those steps and the full coherent quantum-channel plateau are not asserted by this scalar theorem.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/CoherentBinaryOptimalFilter.largest_optimal_filter`
