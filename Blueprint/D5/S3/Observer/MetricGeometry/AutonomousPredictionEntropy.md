# Autonomous prediction and observation entropy

## Abstract

Autonomous state complexity and centered observation covers have the same ordered entropy.

**Theorem 1.1 (Exact minima, charged clocks, and the ordered entropy limit).**

Lean statement: `D5/S3/Observer/MetricGeometry/AutonomousPredictionEntropy.autonomous_prediction_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/AutonomousPredictionEntropy.autonomous_prediction_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a nonempty compact metric space, let F be a continuous total autonomous update, and let o be a continuous observation into an arbitrary metric space Y. The response word is the existing futureReadoutWord through the inclusive times 0 through H. Cover centers belong to the response image itself, and balls are closed. The response-cover count is a positive attained finite minimum. The state count is the least feasible budget for the existing HasFiniteHorizonPredictor with Unit actions; it is attained by a nonempty finite carrier of exactly that cardinality, one total update, one readout, and one initialization valid for every initial point and every time through H.

For the lower bound, choose a representative of each nonempty initialization fiber. Every true response in that fiber and its representative response are each within epsilon of the same machine response, so the triangle inequality gives a closed response-centered cover at radius 2 epsilon. Unused machine states do not increase the minimum. For the upper bound, choose a minimum centered cover and give every center a clock coordinate in Fin(H+1), with the clock saturating at H. A finite equivalence labels the centers in Fin(C), keeping the machine carrier in Type even when X and Y lie in higher universes. Initialize once at clock zero. The carrier has exactly (H+1)C states; the clock is part of this count. These arguments include H=0 and require no boundedness or completeness of the ambient output space.

The exact bounds are C_H(2 epsilon) <= S_H(epsilon) <= (H+1)C_H(epsilon). Natural logarithms and H normalization give the fixed-radius growth squeeze between C at 2 epsilon and C at epsilon. The clock has zero exponential growth because log(H+1)/H tends to zero. Each growth rate is antitone in positive radius; its radius-down-to-zero limit is its supremum. Replacing epsilon by epsilon/2 preserves that supremum. Thus the radius limit is taken after the horizon limsup, and the two ordered limits agree in EReal, including positive infinity. The proof does not assert equality of the two rates at every fixed radius.

When o is a topological embedding, the actual pulled-back metric has distance dist(o(x),o(y)) and exactly the original topology. Its positive-radius closed entourages form the metric uniformity basis. The existing coverMincard counts times k<n, so the inclusive response count corresponds to n=H+1. Time monotonicity and (H+1)/H tending to one give the required entropy normalization before applying coverEntropy_eq_iSup_basis. No dynamics on o[X] is assumed for a general nonembedding observation.

This is the formal reception of the paper's autonomous finite-horizon comparison and entropy argument. It reuses the existing prediction predicate and response geometry and mathlib's Bowen-Dinaburg cover minima, extended exponential growth, and uniformity-basis entropy. The content is repo-derived composition; no worldwide novelty or paper-wide verification claim is made. The construction uses a single update. An entire multiple-action response tree has no corresponding linear clock bound.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/AutonomousPredictionEntropy.autonomous_prediction_entropy`
- Dependency: [D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw](BinaryShiftExactBitLaw.md)
- Dependency: [D5/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric](../../ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric.md)
