# Coherent compression of a positive orbit

## Abstract

Coherent compression and density observations for subunital completely positive maps.

**Theorem 1.1 (The corner defect controls the full orbit).**

$$\forall d \in \mathbb{N},\; \forall T \in \operatorname{CompletelyPositiveMap}\left(\operatorname{ComplexEuclideanMatrix}\left(d\right), \operatorname{ComplexEuclideanMatrix}\left(d\right)\right),\; \forall P \in \operatorname{ComplexEuclideanMatrix}\left(d\right),\; \forall X \in \operatorname{ComplexEuclideanMatrix}\left(d\right),\; \forall sigma \in \operatorname{ComplexEuclideanMatrix}\left(d\right),\; \left(\operatorname{apply}\left(T, 1\right) \le 1 \land \left(\operatorname{IsStarProjection}\left(P\right) \land \left(X \le P \land \left(0 \le sigma \land \operatorname{trace}\left(sigma\right) = 1\right)\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \operatorname{iterate}\left(T, n, X\right) \le P + \operatorname{smul}\left(2 \cdot n \cdot \operatorname{sqrt}\left(\left\lVert (1-P) \cdot \operatorname{apply}\left(T, P\right) \cdot (1-P) \right\rVert\right), 1\right) \land \operatorname{re}\left(\operatorname{trace}\left(sigma \cdot \operatorname{iterate}\left(T, n, X\right)\right)\right) \le \operatorname{re}\left(\operatorname{trace}\left(sigma \cdot P\right)\right) + 2 \cdot n \cdot \operatorname{sqrt}\left(\left\lVert (1-P) \cdot \operatorname{apply}\left(T, P\right) \cdot (1-P) \right\rVert\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QuantitativeCPRankHorizon.coherent_compression_trace_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Matrices act on complex Euclidean space, and the norm is its operator norm. T is an arbitrary completely positive linear map with T(I) at most I. P is an orthogonal projection, X is any matrix at most P, and sigma is a positive matrix of trace one. No invertibility of sigma is required. Write Q=I-P and alpha=sqrt(norm(Q T(P) Q)). The same P determines the corner defect, the orbit comparison and the final observation.

For 0 at most Y at most P, put Z=T(Y). Positivity and subunitality give 0 at most Z at most I. Factoring Z through its positive square root bounds norm(Q Z) by alpha, since norm(Q sqrt(Z)) squared equals norm(Q Z Q). The adjoint gives the same bound for Z Q. The identity Z-P Z P=Q Z+P Z Q therefore bounds the full coherent defect by 2 alpha, including both off-diagonal blocks.

Applying this estimate to Y=P gives T(P) at most P+2 alpha I. Induction using positivity of T and T(I) at most I gives T^n(X) at most P+2 n alpha I. Tracing against sigma proves the observation estimate. The result includes n=0, P=0, P=I and zero maps. It does not choose a spectral cutoff or infer the corner defect from a short-word frame.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantitativeCPRankHorizon.coherent_compression_trace_transfer`
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](PositiveFilterTransposeRefutation.md)
