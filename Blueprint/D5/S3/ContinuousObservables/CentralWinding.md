# A Central Winding Phase over the Visible Circle

## Abstract

Every finite cyclic winding update is a noncentral unitary whose cardinal power is the nonconstant central visible phase.

**Theorem 1.1 (A finite cyclic winding update has a nonidentity central cardinal power).**

$$\forall M \in \mathbb{N},\ 2 \leq M \Rightarrow U_{M}^{M} = Z_{M} \land U_{M}^{M} \in \operatorname{center}(A_{M}) \land Z_{M} \in \operatorname{center}(A_{M}) \land U_{M} \in \operatorname{unitary}(A_{M}) \land Z_{M} \in \operatorname{unitary}(A_{M}) \land Z_{M} \neq 1 \land \neg (U_{M} \in \operatorname{center}(A_{M})) \land z(0) \neq z(\frac{1}{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/CentralWinding.central_winding_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every M at least two, let A_M be the algebra of continuous complex matrix fields indexed by ZMod M over the visible phase circle. The field U_M cyclically shifts the indices and places the circle coordinate z on its unique wrap edge; Z_M is the scalar field z times the identity. One full circuit crosses that edge exactly once, proving U_M to the M-th power equals Z_M and hence is central.

Pointwise circle norm one proves that U_M and Z_M are unitary. At the half-turn, Z_M is minus the identity, so the central phase is not the identity. At phase zero, U_M fails to commute with a constant diagonal matrix field, proving that the update itself is noncentral.

The certificate also proves z(0) differs from z(1/2). Every constant, winding-free phase configuration takes equal values at those points, so this clause excludes all such configurations. The M = 2 instance is kept explicitly: U_2 is [[0,z],[1,0]] and its square is Z_2. Local library searches checked weighted cyclic shifts, monomial matrices, permutation matrices, AddCircle.toCircle, and Unitary.mem_iff.

## References

- Truth anchor: `D5/S3/ContinuousObservables/CentralWinding.central_winding_certificate`
- Dependency: [D5/S3/ContinuousObservables/PhaseFunctionCenter](PhaseFunctionCenter.md)
