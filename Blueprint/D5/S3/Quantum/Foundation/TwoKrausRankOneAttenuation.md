# Nilpotent CAR attenuation

## Abstract

A two-column Gram defect gives quantitative pure-state loss for finite CAR jumps.

Matrices act on the existing complex Euclidean space. opNorm(A) means the norm of Matrix.toEuclideanCLM A, equivalently the L2 operator norm. The index type is arbitrary and finite; no nonempty instance is required. A unit vector itself rules out the empty case. Scalar coefficients in matrix expressions use the real-to-complex embedding.

**Definition 1.1 (No-jump filter).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall J \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall q \in \mathbb{R},\; \operatorname{jumpFilter}\left(J, q\right) = \operatorname{add}\left(\operatorname{sub}\left(1, \operatorname{mul}\left(J, \operatorname{conjTranspose}\left(J\right)\right)\right), \operatorname{smul}\left(\operatorname{ofReal}\left(\operatorname{sqrt}\left(\operatorname{sub}\left(1, q\right)\right)\right), \operatorname{mul}\left(J, \operatorname{conjTranspose}\left(J\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.jumpFilter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F=JJ* is the range projection when J²=0 and JJ*+J*J=I. The filter is I−F+sqrt(1−q)F.

**Definition 1.2 (The canonical finite Kraus map).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall J \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall q \in \mathbb{R},\; \operatorname{jumpMap}\left(J, q\right) = \operatorname{ofKraus}\left(\operatorname{pair}\left(\operatorname{jumpFilter}\left(J, q\right), \operatorname{smul}\left(\operatorname{ofReal}\left(\operatorname{sqrt}\left(q\right)\right), J\right)\right), \operatorname{pair}\left(\operatorname{jumpFilter}\left(J, q\right), \operatorname{smul}\left(\operatorname{ofReal}\left(\operatorname{sqrt}\left(q\right)\right), J\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.jumpMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ofKraus is FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus, with the same ordered pair K=(R,sqrt(q)J) in both slots. This is a linear map on matrices. It is unital under the CAR and interval hypotheses; trace preservation is not asserted. The imported Kraus implementation retains its Physlib source attribution and Apache license.

**Theorem 1.3 (The two actual Kraus sandwiches).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall J \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall q \in \mathbb{R},\; 0 \le q \Rightarrow \left(\forall X \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{jumpMap}\left(J, q, X\right) = \operatorname{add}\left(\operatorname{mul}\left(\operatorname{mul}\left(\operatorname{jumpFilter}\left(J, q\right), X\right), \operatorname{conjTranspose}\left(\operatorname{jumpFilter}\left(J, q\right)\right)\right), \operatorname{smul}\left(\operatorname{ofReal}\left(q\right), \operatorname{mul}\left(\operatorname{mul}\left(J, X\right), \operatorname{conjTranspose}\left(J\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.jumpMap_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For q≥0 the two Kraus summands are RXR* and qJXJ*. The identity uses sqrt(q)²=q.

**Theorem 1.4 (Positivity).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall J \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall q \in \mathbb{R},\; 0 \le q \Rightarrow \left(\forall X \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; 0 \le X \Rightarrow 0 \le \operatorname{jumpMap}\left(J, q, X\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.jumpMap_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each Kraus sandwich preserves positive semidefiniteness. The matrix order is the canonical PSD order.

**Theorem 1.5 (Hermitian contraction).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall J \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall q \in \mathbb{R},\; \operatorname{mul}\left(J, J\right) = 0 \Rightarrow \left(\operatorname{add}\left(\operatorname{mul}\left(J, \operatorname{conjTranspose}\left(J\right)\right), \operatorname{mul}\left(\operatorname{conjTranspose}\left(J\right), J\right)\right) = 1 \Rightarrow \left(0 \le q \Rightarrow \left(q \le 1 \Rightarrow \left(\forall X \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{IsHermitian}\left(X\right) \Rightarrow \operatorname{opNorm}\left(\operatorname{jumpMap}\left(J, q, X\right)\right) \le \operatorname{opNorm}\left(X\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.jumpMap_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CAR gives F²=F, FJ=J, JF=0 and R²=I−qF. Thus H(I)=I. Positivity and linearity transport −norm(X)I≤X≤norm(X)I to the same interval for H(X), proving contraction on every Hermitian input, including indefinite ones.

**Theorem 1.6 (Quantitative rank-one loss).**

$$\forall n \in Type,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall J \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall q \in \mathbb{R},\; \operatorname{mul}\left(J, J\right) = 0 \Rightarrow \left(\operatorname{add}\left(\operatorname{mul}\left(J, \operatorname{conjTranspose}\left(J\right)\right), \operatorname{mul}\left(\operatorname{conjTranspose}\left(J\right), J\right)\right) = 1 \Rightarrow \left(0 \le q \Rightarrow \left(q \le 1 \Rightarrow \left(\forall psi \in \operatorname{EuclideanSpace}\left(\mathbb{C}, n\right),\; \operatorname{norm}\left(psi\right) = 1 \Rightarrow \operatorname{opNorm}\left(\operatorname{jumpMap}\left(J, q, \operatorname{vecMulVec}\left(\operatorname{ofLp}\left(psi\right), \operatorname{star}\left(\operatorname{ofLp}\left(psi\right)\right)\right)\right)\right) \le \operatorname{sub}\left(1, \operatorname{mul}\left(\operatorname{mul}\left(q, \operatorname{sub}\left(1, q\right)\right), \operatorname{sub}\left(\operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{ofLp}\left(psi\right)\right), \operatorname{mulVec}\left(\operatorname{mul}\left(J, \operatorname{conjTranspose}\left(J\right)\right), \operatorname{ofLp}\left(psi\right)\right)\right)\right), \operatorname{normSq}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{ofLp}\left(psi\right)\right), \operatorname{mulVec}\left(J, \operatorname{ofLp}\left(psi\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.nilpotent_jump_rank_one_attenuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write u=ofLp(psi), p=Re(u*Fu), c=u*Ju. The two columns Rpsi and sqrt(q)Jpsi give A with H(P)=AA*. Positivity, P≤I and unitality imply A*A≤I by the rectangular L2 norm identity. The Gram entries are 1−qp, sqrt(q)sqrt(1−q)c and its conjugate, and q(1−p). Its defect determinant is q((1−q)(p−normSq(c))+qp²). Both Gram eigenvalues lie in [0,1]; if their maximum is nu, then norm(H(P))=nu≤1−det(I−A*A). Dropping q²p² gives the stated bound. Both parameter endpoints and arbitrary complex phases are included. This is a pure-state estimate, with no assertion about a low-temperature tube or nonnegativity of an entropy gap.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.jumpFilter`
- Truth anchor: `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.jumpMap`
- Truth anchor: `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.jumpMap_apply`
- Truth anchor: `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.jumpMap_norm_le`
- Truth anchor: `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.jumpMap_positive`
- Truth anchor: `D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.nilpotent_jump_rank_one_attenuation`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](FiniteKrausChannel.md)
