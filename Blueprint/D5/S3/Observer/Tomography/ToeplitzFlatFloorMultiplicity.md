# Toeplitz Flat-Floor Multiplicity

## Abstract

A contact Gram update has floor omega with the predicted multiplicity.

**Theorem 1.1 (Finite contact rank leaves an exact flat spectral floor).**

$$\begin{aligned}\forall N: \mathbb{N}, M: \mathbb{N}, omega: \mathbb{R},\\z: \operatorname{Fin}(M) \to \operatorname{unitary}(\mathbb{C}),\\q: \operatorname{Fin}(M) \to \{x\in \mathbb{R} \mid 0 < x\},\\M < N+1 \Rightarrow\\\operatorname{let}(A: \operatorname{Matrix}(\operatorname{Fin}(M), \operatorname{Fin}(N+1), \mathbb{C}), \forall r: \operatorname{Fin}(M), j: \operatorname{Fin}(N+1), A_{r,j} = \sqrt{q(r)} {z(r)^{j}}^{*}, T: \operatorname{Matrix}(\operatorname{Fin}(N+1), \operatorname{Fin}(N+1), \mathbb{C}) = omegaI + A^{*}A)\;\\(\forall j: \operatorname{Fin}(N+1), k: \operatorname{Fin}(N+1), T_{jk} = delta_{jk}omega + \sum_{r=1}^{M} q(r) z(r)^{j} {z(r)^{k}}^{*}) \land\\\operatorname{IsLeast}(\operatorname{spectrum}(\mathbb{R}, T), omega) \land\\N+1 - M \leq \operatorname{finrank}(\mathbb{C}, \operatorname{eigenspace}(T, omega)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/ToeplitzFlatFloorMultiplicity.toeplitz_flat_floor_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The contact points live directly in the unitary subtype of the complex unit circle, and every weight lives in the strictly positive real subtype. The weighted analysis matrix is constructed from their contact vectors rather than supplied as an arbitrary matrix.

The first public clause expands the constructed adjoint Gram matrix entry by entry, exposing the scalar white floor and the positive finite contact update on the exact complex Toeplitz carrier.

Adjoint Gram positivity places every real spectral value above omega. Rank-nullity leaves at least N plus one minus M independent kernel directions, and each becomes an omega eigenvector after the scalar floor is added.

The conclusion states the minimum as an IsLeast property of the real spectrum and states the multiplicity as the complex dimension of the omega eigenspace. Hermitian spectral theory identifies this geometric multiplicity with eigenvalue multiplicity.

## References

- Truth anchor: `D5/S3/Observer/Tomography/ToeplitzFlatFloorMultiplicity.toeplitz_flat_floor_multiplicity`
