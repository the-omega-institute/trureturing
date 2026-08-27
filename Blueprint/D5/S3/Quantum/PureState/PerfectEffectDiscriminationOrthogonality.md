# Perfect Effect Discrimination Orthogonality

## Abstract

Perfect one-shot effect discrimination forces orthogonality.

**Theorem 1.1 (Perfect effect discrimination forces orthogonality).**

$$\begin{gathered}\forall I: Type, \operatorname{Fintype}(I), \operatorname{DecidableEq}(I),\\{}E: \operatorname{Matrix}(I, I, \mathbb{C}), \psi, \phi: I \to \mathbb{C},\\{}\operatorname{PosSemidefinite}(E) \land \operatorname{PosSemidefinite}(1 - E) \land\\{}\langle \psi, \psi \rangle = 1 \land \langle \psi, \operatorname{mulVec}(E, \psi) \rangle = 1 \land\\{}\langle \phi, \operatorname{mulVec}(E, \phi) \rangle = 0 \Rightarrow\\{}\langle \phi, \psi \rangle = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PerfectEffectDiscriminationOrthogonality.perfect_effect_discrimination_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a finite complex matrix effect: both E and its complement are positive semidefinite. Let psi be normalized, suppose E accepts psi with probability one, and suppose E rejects phi with probability zero.

A positive-semidefinite quadratic value vanishes exactly when the corresponding matrix kills the vector. Applied to the complement at psi and to E at phi, this gives E psi = psi and E phi = 0.

Hermiticity of a positive-semidefinite matrix transfers E between the two slots of the overlap, so the overlap of phi with psi is zero. The theorem is stronger than the pure-state formulation because phi itself need not be normalized.

Repository and pinned-library searches found no exact discrimination theorem. The proof directly applies the pinned positive-matrix quadratic-zero criterion and standard matrix-vector identities.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PerfectEffectDiscriminationOrthogonality.perfect_effect_discrimination_orthogonal`
