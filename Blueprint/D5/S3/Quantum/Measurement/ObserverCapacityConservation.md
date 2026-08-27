# Quantum Observer Capacity Conservation

## Abstract

Finite-dimensional quantum observer capacity and invisible residual conserve the traceless Hermitian dimension under information refinement.

**Theorem 1.1 (Capacity and residual conserve dimension under refinement).**

$$\forall d \in Nat,\; d \ne 0 \Rightarrow \left(\left(\forall E \in \operatorname{Set}\left(\operatorname{HermitianSpace}\left(d\right)\right),\; \operatorname{finrank}\left(\mathbb{R}, \operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), E\right)\right)\right) - 1 + \operatorname{finrank}\left(\mathbb{R}, \operatorname{orthogonal}\left(\operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), E\right)\right)\right)\right) = d ^{2} - 1\right) \land \left(\forall E1 \in \operatorname{Set}\left(\operatorname{HermitianSpace}\left(d\right)\right), E2 \in \operatorname{Set}\left(\operatorname{HermitianSpace}\left(d\right)\right),\; E1 \subseteq E2 \Rightarrow \left(\operatorname{finrank}\left(\mathbb{R}, \operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), E1\right)\right)\right) - 1 \le \operatorname{finrank}\left(\mathbb{R}, \operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), E2\right)\right)\right) - 1 \land \operatorname{finrank}\left(\mathbb{R}, \operatorname{orthogonal}\left(\operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), E2\right)\right)\right)\right) \le \operatorname{finrank}\left(\mathbb{R}, \operatorname{orthogonal}\left(\operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), E1\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ObserverCapacityConservation.observer_capacity_conservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An observer effect family generates the real span of the identity and its effects inside the canonical Hermitian matrix carrier. Capacity is that visible dimension minus the identity direction, and the residual is the orthogonal-complement dimension.

The Hermitian carrier has real dimension d squared. Orthogonal dimension splitting and the visible identity line therefore give capacity plus residual equal to d squared minus one.

Including one effect family in another includes their visible spans. Finite-dimensional rank is monotone under that inclusion, while orthogonal complementation reverses it, proving both progress inequalities.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ObserverCapacityConservation.observer_capacity_conservation`
- Dependency: [D5/S3/Quantum/Measurement/JointObserverVisibleResidual](JointObserverVisibleResidual.md)
