# Pure White Innovation Directions

## Abstract

Finite contact atoms leave explicit nonzero directions at the white spectral floor.

**Theorem 1.1 (Contact-analysis kernel directions are white-floor eigenvectors).**

$$\begin{aligned}\forall N: \mathbb{N}, M: \mathbb{N}, omega: \mathbb{R},\\z: \operatorname{Fin}(M) \to \operatorname{unitary}(\mathbb{C}),\\q: \operatorname{Fin}(M) \to \{x\in \mathbb{R} \mid 0 < x\},\\M < N+1 \Rightarrow\\\operatorname{let}(A: \operatorname{Matrix}(\operatorname{Fin}(M), \operatorname{Fin}(N+1), \mathbb{C}), \forall r: \operatorname{Fin}(M), j: \operatorname{Fin}(N+1), A_{r,j} = \sqrt{q(r)} {z(r)^{j}}^{*}, T: \operatorname{Matrix}(\operatorname{Fin}(N+1), \operatorname{Fin}(N+1), \mathbb{C}) = omegaI + A^{*}A)\;\\(\forall x: \operatorname{Fin}(N+1) \to \mathbb{C}, x \in \operatorname{ker}(A) \Rightarrow x \in \operatorname{eigenspace}(T, omega)) \land\\\exists x: \operatorname{Fin}(N+1) \to \mathbb{C}, x \neq 0 \land x \in \operatorname{ker}(A).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/PureWhiteInnovationDirection.pure_white_innovation_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The contact points are taken from the unitary subtype of the complex circle, and each contact weight is a strictly positive real. These source objects construct the weighted analysis matrix and the Toeplitz carrier with its scalar white floor.

Every vector annihilated by the contact analysis is an eigenvector of the constructed Toeplitz matrix at the floor value omega. Thus the finite atomic update does not activate that direction.

The strict inequality M < N plus one gives a nonzero analysis-kernel direction by rank-nullity. The public conclusion records both the kernel-to-eigenspace bridge and this nontriviality witness.

The proof uses the adjoint-Gram positivity primitive and finite-dimensional rank-nullity; no arbitrary matrix or auxiliary definition is supplied.

## References

- Truth anchor: `D5/S3/Observer/Tomography/PureWhiteInnovationDirection.pure_white_innovation_direction`
- Dependency: [D5/S3/Observer/Tomography/ToeplitzFlatFloorMultiplicity](ToeplitzFlatFloorMultiplicity.md)
