# A quantitative detector-rank horizon

## Abstract

Short-time density observations bound the spectral tail of an effect under an arbitrary complex subunital completely positive map.

**Theorem 1.1 (The universal bound from the original matrices).**

$$\forall D \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall T \in \operatorname{CompletelyPositiveMap}\left(\operatorname{ComplexEuclideanMatrix}\left(D\right), \operatorname{ComplexEuclideanMatrix}\left(D\right)\right),\; \forall B \in \operatorname{ComplexEuclideanMatrix}\left(D\right),\; \forall sigma \in \operatorname{ComplexEuclideanMatrix}\left(D\right),\; \forall epsilon \in \mathbb{R},\; \forall p \in \mathbb{R},\; \left(2 \le D \land \left(2 \le r \land \left(r \le D \land \left(1 \le n \land \left(\operatorname{apply}\left(T, 1\right) \le 1 \land \left(0 \le B \land \left(B \le 1 \land \left(0 \le sigma \land \left(\operatorname{trace}\left(sigma\right) = 1 \land \left(0 \le epsilon \land \left(0 < p \land \left(p \le 1 \land \left(\left(\forall k \in \mathbb{N},\; k \le D - r \Rightarrow \operatorname{re}\left(\operatorname{trace}\left(sigma \cdot \operatorname{iterate}\left(T, k, B\right)\right)\right) \le epsilon\right) \land p \le \operatorname{re}\left(\operatorname{trace}\left(sigma \cdot \operatorname{iterate}\left(T, n, B\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{eigenvalueszero}\left(B, r - 1\right) \le \frac{8 \cdot D}{p^{2}} \cdot \frac{8 \cdot n \cdot D^{\frac{5}{2}}}{p}^{2 \cdot \left(D - r\right)} \cdot epsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/OriginalDataQuantitativeDetectorRankHorizon.detector_rank_horizon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrices act on complex Euclidean space of dimension D. T is completely positive and T(I) is at most I. B is an effect and sigma is a positive matrix of trace one. The eigenvalues of B are ordered decreasingly, with repetitions and zero eigenvalues retained; eigenvalueszero(B,r-1) denotes the r-th eigenvalue. Iteration at zero is the identity. All matrix norms below are Euclidean operator norms.

Put s=lambda_r(B). Nonnegativity settles s=0. For s>0 set t=p s/4, delta=p/(8 n D sqrt(D)), and C=(D/delta)^(D-r). Since s is at most one, t is positive and at most p/4. The threshold delta is positive and less than one. Start with every eigenvector whose eigenvalue is at least t. These vectors form an orthonormal seed of size q at least r. For each seed vector eta, t times its rank-one projection is at most B. Every larger subspace W containing this seed satisfies B at most P_W+t I: on the selected eigenspaces B is at most I, and on the complement every eigenvalue is below t. This construction does not require a spectral gap.

Take the finite Kraus representation of the actual map T, indexed by D squared operators, allowing zero operators. Subunitality makes each Kraus operator a contraction. Apply quantitative_word_orthonormal_extension to this family and the chosen seed. It supplies an orthonormal family e of size m at most D, its projection P, residuals norm((I-P) A_a e_j) at most delta, and expansions of e_j in chronological Kraus words of length at most D-r. The sum of absolute coefficients in each expansion is at most C.

Positivity of individual summands in the same Kraus representation gives t times the rank-one projection onto A_w eta at most T^k(B), where k is the length of w. Trace against sigma and use the early inequalities. The identity Tr(sigma |v><v|)=norm(sqrt(sigma) v) squared yields norm(sqrt(sigma) A_w eta) at most sqrt(epsilon/t). The finite expansions and the triangle inequality then give norm(sqrt(sigma) e_j) at most C sqrt(epsilon/t). Summing over the orthonormal family proves Tr(sigma P) at most D C squared epsilon/t.

Let Q=I-P. Decompose P into its orthonormal rank-one projections and apply the same Kraus representation. Then Q T(P) Q is the sum, over a and j, of rank-one operators on Q A_a e_j. The operator norm of each is at most delta squared. There are at most D cubed terms, so norm(Q T(P) Q) is at most D cubed delta squared. Its square root alpha is therefore at most p/(8 n). This controls the full complex operator, including all off-diagonal coherences.

The spectral cutoff gives X=B-t I at most P. Apply coherent_compression_trace_transfer to T, this P, X and sigma. It gives Re Tr(sigma T^n(X)) at most Tr(sigma P)+2 n alpha. Subunitality implies T^n(I) at most I. Linearity thus gives Re Tr(sigma T^n(B)) at most Tr(sigma P)+2 n alpha+t. The late hypothesis implies p at most D C squared epsilon/t+p/4+p/4. Multiplication by the positive t and substitution t=p s/4 give s at most 8 D C squared epsilon/p squared. Finally D/delta=8 n D^(5/2)/p, giving the displayed constant.

The argument never divides by epsilon and includes epsilon=0. It also includes repeated eigenvalues, singular mixed densities, arbitrary complex coherences, and a late index lying in the early window. No commutation, diagonalizability, conditioning or single-Kraus condition is used. The stronger late-free smallest-eigenvalue endpoint is a separate statement.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/OriginalDataQuantitativeDetectorRankHorizon.detector_rank_horizon`
- Dependency: [D5/S3/Quantum/Algebra/QuantitativeWordOrthonormalExtension](../Algebra/QuantitativeWordOrthonormalExtension.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QuantitativeCPRankHorizon](QuantitativeCPRankHorizon.md)
- Dependency: [D5/S3/SpectralTopology/HermitianEigenvaluePerturbation](../../SpectralTopology/HermitianEigenvaluePerturbation.md)
