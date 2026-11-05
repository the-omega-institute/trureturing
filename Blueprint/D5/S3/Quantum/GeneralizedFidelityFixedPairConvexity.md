# Fixed-Pair Convexity of Generalized Fidelity

## Abstract

For a fixed positive definite qubit reference R and a second input Q of trace one, the squared generalized Bures--Wasserstein quantity is convex in its first density-state input exactly when its Hermitian square-root coefficient is positive semidefinite.

**Definition 1.1 (The full qubit density domain).**

$$densitySet = \{P | \operatorname{PSD}\left(P\right) \land \operatorname{tr}\left(P\right) = 1\}$$

*Formalization.* `D5/S3/Quantum/GeneralizedFidelityFixedPairConvexity.densitySet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The domain consists of all complex two by two positive semidefinite matrices of trace one. It includes every rank-one boundary state and is convex over the real numbers.

**Definition 1.2 (The Hermitian trace coefficient).**

$$\operatorname{coefficient}\left(R, Q\right) = \frac{1}{2}(R^{-1}\operatorname{sqrt}\left(\operatorname{sqrt}\left(R\right)Q\operatorname{sqrt}\left(R\right)\right)+\operatorname{sqrt}\left(\operatorname{sqrt}\left(R\right)Q\operatorname{sqrt}\left(R\right)\right)R^{-1})$$

*Formalization.* `D5/S3/Quantum/GeneralizedFidelityFixedPairConvexity.coefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write S=sqrt(R), D=sqrt(SQS), and C=(R inverse D+D R inverse)/2. When R is positive definite, C is Hermitian. Cyclicity of trace and conjugation give Re fidelity(R,P,Q)=Re tr(C sqrt(SPS)). Every root uses the existing total CFC.sqrt operation. On positive semidefinite arguments this is the positive semidefinite square root; all root arguments are positive semidefinite in the density-state specialization. The inverse is the actual matrix inverse.

**Theorem 1.3 (The exact positivity criterion).**

$$\forall Q,R,\ \operatorname{tr}\left(Q\right) = 1 \land \operatorname{PD}\left(R\right) \Rightarrow (\operatorname{ConvexOn}\left(real, densitySet, {\lambda P,\operatorname{bures}\left(R, P, Q\right)}\right) \iff \operatorname{PSD}\left(\operatorname{coefficient}\left(R, Q\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeneralizedFidelityFixedPairConvexity.fixed_pair_convexity_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex two by two Q of trace one and positive-definite R, convexity of P mapped to bures(R,P,Q) on the entire density domain is equivalent to C being positive semidefinite. In particular, this applies when Q is a density state, including singular Q, and R has trace one. The original real trace term tr(P+Q) becomes two on this domain, so convexity is equivalent to concavity of Re fidelity in P. If C is positive semidefinite, the positive trace functional preserves the operator-concavity inequality for square root. For necessity, diagonalize C=U diag(lambda0,lambda1) U star, set V=S inverse U, alpha=Re (V star V)00 and beta=Re (V star V)11, and use the actual density matrices P(t)=V diag((1-t)/alpha,t/beta) V star for 0<=t<=1. Both normalization constants are strictly positive. The sandwiched matrices have eigenvalues (1-t)/alpha and t/beta, so their actual roots give Re fidelity=lambda0 sqrt(1-t)/sqrt(alpha)+lambda1 sqrt(t)/sqrt(beta). Concavity places this function above its endpoint chord. Substituting t=x squared and letting x decrease to zero forces lambda1>=0; reversing t forces lambda0>=0. This is convexity in P for a fixed pair Q,R and does not assert joint convexity or a data-processing property of channels.

## References

- Truth anchor: `D5/S3/Quantum/GeneralizedFidelityFixedPairConvexity.coefficient`
- Truth anchor: `D5/S3/Quantum/GeneralizedFidelityFixedPairConvexity.densitySet`
- Truth anchor: `D5/S3/Quantum/GeneralizedFidelityFixedPairConvexity.fixed_pair_convexity_iff`
- Dependency: [D5/S3/Quantum/GeneralizedFidelity](GeneralizedFidelity.md)
