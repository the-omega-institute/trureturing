# Canonical Separable Cone Residual

## Abstract

The separable matrix argmin identifies the canonical negative Moreau residual.

Throughout, m and n are arbitrary natural numbers, including zero. Write I = Fin m x Fin n and Mat = Matrix I I Complex. All optimization, pairing and duality statements range over all complex matrices in Mat. The scalar field for linearity, cones and inner products is Real. No trace-one, rank or positive-dimension assumption is made.

**Definition 1.1 (Standard entry Hilbert space).**

$$H = \operatorname{EuclideanSpace}(\mathbb{C}, I\times I)$$

*Formalization.* `D5/S3/Resource/SeparableConeResidualWitness.EntrySpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H uses the standard complex Euclidean norm and its existing real inner product. It is not the Hermitian subspace and its norm is not the default matrix norm.

**Definition 1.2 (Continuous real linear entry equivalence).**

$$e:Mat \equiv_{\mathbb{R}} H$$

*Formalization.* `D5/S3/Resource/SeparableConeResidualWitness.entryEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map e = entryEquiv and its inverse are continuous and real linear. The theorem entryEquiv_apply states e(A)(i,j) = A(i,j) for every A and every i,j in I.

**Theorem 1.3 (Metric and trace pairing agree).**

$$\forall S \in Mat, W \in Mat,\; \operatorname{innerReal}(\operatorname{e}(S), \operatorname{e}(W)) = \operatorname{pairing}(S, W)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SeparableConeResidualWitness.entry_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing pairing is Re(trace(S.conjTranspose * W)). The theorem pairing_symm gives pairing(S,W) = pairing(W,S) for all matrices. Thus this is a metric identification, beyond continuity or a trace expansion alone.

**Definition 1.4 (Independent matrix objective).**

$$\forall R \in Mat, P \in Mat,\; \operatorname{distanceSq}(R, P) = \operatorname{pairing}(R - P, R - P)$$

*Formalization.* `D5/S3/Resource/SeparableConeResidualWitness.distanceSq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The objective is defined solely from the existing pairing and matrix subtraction.

**Theorem 1.5 (Squared distance in entry coordinates).**

$$\forall R \in Mat, P \in Mat,\; \operatorname{distanceSq}(R, P) = \Vert \operatorname{e}(R - P)\Vert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SeparableConeResidualWitness.distanceSq_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm in this equality is the Euclidean norm on H.

**Definition 1.6 (PSD product generators).**

$$G=\{S \mid \exists A,B, \operatorname{PosSemidef}(A) \land \left(\operatorname{PosSemidef}(B) \land S = \operatorname{kronecker}(A, B)\right)\}$$

*Formalization.* `D5/S3/Resource/SeparableConeResidualWitness.sourceGenerators` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A ranges over Matrix (Fin m) (Fin m) Complex and B over Matrix (Fin n) (Fin n) Complex, independently. G denotes sourceGenerators m n.

**Theorem 1.7 (Closed nonnegative conic hull is SEP).**

$$\operatorname{closure}(\operatorname{nonnegativeConicHull}(G)) = \{S \mid \operatorname{separableCone}(S)\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SeparableConeResidualWitness.closed_conic_hull_eq_separable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hull is PointedCone.hull Real G, so zero and all finite nonnegative real combinations are included. The proof identifies the finite-sum representation and reuses isClosed_separableCone, including empty dimensions.

**Definition 1.8 (The transported proper cone).**

$$K=\{v \in H \mid \operatorname{separableCone}(\operatorname{inverseEntry}(v))\}$$

*Formalization.* `D5/S3/Resource/SeparableConeResidualWitness.separableProperCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K = separableProperCone m n is a ProperCone Real H. mem_separableProperCone gives the displayed membership equivalence, with inverseEntry = e.symm. entry_mem_separableProperCone specializes it to e(S) in K iff separableCone(S). Its closedness is transported through the continuous inverse of e.

**Theorem 1.9 (The concrete nonnegative dual).**

$$\forall W \in Mat,\; \operatorname{e}(W) \in \operatorname{innerDual}(K) \Leftrightarrow \operatorname{blockPositive}(W)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SeparableConeResidualWitness.entry_mem_innerDual_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

innerDual uses innerReal(v,e(W)) >= 0 for every v in K. Block positivity on arbitrary complex matrices does not by itself assert Hermiticity.

**Definition 1.10 (The independent argmin predicate).**

$$\forall R \in Mat, P \in Mat,\; \operatorname{Argmin}(R, P) \Leftrightarrow \operatorname{separableCone}(P) \land \left(\forall Q \in Mat,\; \operatorname{separableCone}(Q) \Rightarrow \operatorname{distanceSq}(R, P) \leq \operatorname{distanceSq}(R, Q)\right)$$

*Formalization.* `D5/S3/Resource/SeparableConeResidualWitness.Argmin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition contains neither projection nor uniqueness nor a witness conclusion.

**Theorem 1.11 (A unique minimizer for every matrix).**

$$\forall R \in Mat,\; \exists! P \in Mat, \operatorname{Argmin}(R, P)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SeparableConeResidualWitness.existsUnique_argmin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

nearestSeparable chooses the point from this independent characterization. nearestSeparable_spec proves Argmin(R,nearestSeparable(R)); nearestSeparable_unique proves P = nearestSeparable(R) for every P satisfying Argmin(R,P). Existence is unconditional.

**Theorem 1.12 (Identification with the generic cone projection).**

$$\forall R \in Mat,\; \operatorname{e}(\operatorname{nearestSeparable}(R)) = \operatorname{coneProjection}(K, \operatorname{e}(R))$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SeparableConeResidualWitness.nearestSeparable_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equality is proved after the independent optimization problem has been solved.

In the following two statements, for each input R set P = nearestSeparable(R), r = R - P and W = P - R. These are dependent abbreviations, not extra hypotheses.

**Theorem 1.13 (Unique orthogonal polar decomposition).**

$$\forall R \in Mat,\; \left(\operatorname{separableCone}(P) \land \left(\operatorname{blockPositive}(-r) \land \left(\operatorname{pairing}(P, r) = 0 \land R = P+r\right)\right)\right) \land \left(\forall Q \in Mat, s \in Mat,\; \left(\operatorname{separableCone}(Q) \land \left(\operatorname{blockPositive}(-s) \land \left(\operatorname{pairing}(Q, s) = 0 \land R = Q+s\right)\right)\right) \Rightarrow \left(Q = P \land s = r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SeparableConeResidualWitness.separable_moreau_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual r lies in the polar cone: its negative lies in the nonnegative dual. The uniqueness follows from the existing moreau_decomposition theorem and applies to this orthogonal decomposition, not to all entanglement witnesses.

**Theorem 1.14 (The canonical negative residual witness).**

$$\forall R \in Mat,\; \operatorname{PosSemidef}(R) \Rightarrow \left(\operatorname{separableCone}(P) \land \left(R = P+r \land \left(\operatorname{IsHermitian}(W) \land \left(\operatorname{blockPositive}(W) \land \left(\operatorname{pairing}(P, r) = 0 \land \left(\left(\forall S \in Mat,\; \operatorname{separableCone}(S) \Rightarrow \left(\operatorname{pairing}(S, r) \leq 0 \land 0 \leq \operatorname{pairing}(S, W)\right)\right) \land \left(\operatorname{pairing}(R, W) = -\operatorname{pairing}(r, r) \land \left(\operatorname{pairing}(R, W) = -\Vert \operatorname{e}(r)\Vert^{2} \land \left(\neg \operatorname{separableCone}(R) \Rightarrow \operatorname{pairing}(R, W)<0\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SeparableConeResidualWitness.separable_cone_residual_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only the physical witness conclusion requires a PSD input R. The separable minimizer P is PSD, hence P and R are Hermitian and W = P - R is Hermitian. W is not asserted PSD. On this source domain the displayed projection and pairing agree with the finite Hermitian/PSD problem because the same entries and trace pairing are used. Strict negativity additionally requires nonseparability; the negative-square identities hold even inside SEP.

**Theorem 1.15 (Zero residual inside the cone).**

$$\forall R \in Mat,\; \operatorname{separableCone}(R) \Rightarrow \left(\operatorname{nearestSeparable}(R) = R \land \left(R - \operatorname{nearestSeparable}(R) = 0 \land \operatorname{nearestSeparable}(R) - R = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SeparableConeResidualWitness.separable_zero_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

nearestSeparable_of_separable also exposes the first equality separately. Zero and any PSD product matrix satisfy this branch.

**Theorem 1.16 (Zero residual characterizes separability).**

$$\forall R \in Mat,\; R - \operatorname{nearestSeparable}(R) = 0 \Leftrightarrow \operatorname{separableCone}(R)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SeparableConeResidualWitness.zero_residual_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This equivalence holds for every matrix and all natural dimensions. No entangled matrix is assumed to exist in each dimension.

This unit supplies only the separable-cone row. The finance row still lacks an independently specified canonical shadow-price residual for the unrestricted market. The Weil row still needs its Hilbert carrier, critical cone and closedness, pairing/Riesz identification, and recovery of the source negative direction. The Nyman row is independent. No whole-atom closure, Riemann-hypothesis result, or general Banach extension is asserted.

## References

- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.Argmin`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.EntrySpace`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.closed_conic_hull_eq_separable`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.distanceSq`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.distanceSq_eq`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.entryEquiv`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.entry_inner`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.entry_mem_innerDual_iff`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.existsUnique_argmin`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.nearestSeparable_projection`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.separableProperCone`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.separable_cone_residual_witness`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.separable_moreau_decomposition`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.separable_zero_residual`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.sourceGenerators`
- Truth anchor: `D5/S3/Resource/SeparableConeResidualWitness.zero_residual_iff`
- Dependency: [D5/S3/Observer/Separation/MoreauDecomposition](../Observer/Separation/MoreauDecomposition.md)
