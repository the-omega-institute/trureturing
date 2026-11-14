# Uniform density repair

## Abstract

Trace and all-effect lower bounds repair any Hermitian candidate uniformly.

In the formulas, Mat(d) is Matrix(Fin(d), Fin(d), C), Id(d) is its identity, Tr is the complex matrix trace, and complex is the real-to-complex embedding. The expression ite(Q,u,v) means u if Q holds and v otherwise. For a Hermiticity proof h, specMap(h,f) applies the real function f to the real eigenvalues in its orthonormal spectral decomposition; hermNegPart(h) uses f(x)=max(-x,0). The proof h retains the matrix A as its dependent parameter. Dots denote matrix multiplication.

All matrices are actual complex square matrices indexed by Fin d. IsEffect E means positive semidefiniteness of E and of identity minus E. The error parameter eta is nonnegative and d is at least one in the repair theorem.

The negative spectral projector bounds the trace of the negative part by eta. If the positive part has positive trace, division by that trace produces a positive matrix with complex trace one. If that trace is zero, a coordinate density supplies the required matrix. The same single matrix works for every effect, with correction at most 3*eta.

**Definition 1.1 (negativeProjector).**

$$\forall (d: \mathbb{N}), (\forall (A: \operatorname{Mat}(d)), (\forall (h: \operatorname{IsHermitian}(A)), (\operatorname{negativeProjector}(h) = \operatorname{specMap}(h, ((x: \mathbb{R}) \mapsto \operatorname{ite}(x < 0, 1, 0))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityRepair.negativeProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Spectral functional calculus of a Hermitian matrix at the indicator of the negative reals defines its negative spectral projector.

**Theorem 1.2 (negativeProjector effect).**

$$\forall (d: \mathbb{N}), (\forall (A: \operatorname{Mat}(d)), (\forall (h: \operatorname{IsHermitian}(A)), ((\operatorname{PosSemidef}(\operatorname{negativeProjector}(h))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-\operatorname{negativeProjector}(h)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityRepair.negativeProjector_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Hermitian matrix in every natural dimension, its negative spectral projector and the complement of that projector are positive semidefinite.

**Theorem 1.3 (mul negativeProjector).**

$$\forall (d: \mathbb{N}), (\forall (A: \operatorname{Mat}(d)), (\forall (h: \operatorname{IsHermitian}(A)), ((A \cdot \operatorname{negativeProjector}(h)) = -\operatorname{hermNegPart}(h))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityRepair.mul_negativeProjector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying a Hermitian matrix by its negative spectral projector gives the negative of its spectral negative part.

**Theorem 1.4 (psd effect pairing bounds).**

$$\forall (d: \mathbb{N}), (\forall (B: \operatorname{Mat}(d)), (\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(B)) \land ((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E))))) \implies ((0 \leq \Re (\operatorname{Tr}((B \cdot E)))) \land (\Re (\operatorname{Tr}((B \cdot E))) \leq \Re (\operatorname{Tr}(B)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityRepair.psd_effect_pairing_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary positive semidefinite matrix B and every actual effect E, the real part of the complex trace of B*E lies between zero and the real part of the complex trace of B.

**Theorem 1.5 (psd trace real).**

$$\forall (d: \mathbb{N}), (\forall (B: \operatorname{Mat}(d)), ((\operatorname{PosSemidef}(B)) \implies (\operatorname{Tr}(B) = \operatorname{complex}(\Re (\operatorname{Tr}(B))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityRepair.psd_trace_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex trace of every positive semidefinite matrix equals the complex embedding of its real part.

**Theorem 1.6 (uniform density repair).**

$$\forall (d: \mathbb{N}), ((1 \leq d) \implies (\forall (eta: \mathbb{R}), ((0 \leq eta) \implies (\forall (A: \operatorname{Mat}(d)), (((\operatorname{IsHermitian}(A)) \land (\lvert (\Re (\operatorname{Tr}(A))-1) \rvert  \leq eta) \land (\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (-eta \leq \Re (\operatorname{Tr}((A \cdot E))))))) \implies (\exists (\rho: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(\rho)) \land (\operatorname{Tr}(\rho) = 1)) \land (\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (\lvert (\Re (\operatorname{Tr}((\rho \cdot E)))-\Re (\operatorname{Tr}((A \cdot E)))) \rvert  \leq (3 \cdot eta)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityRepair.uniform_density_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d>=1, eta>=0 and actual Hermitian A, an error at most eta in its real trace from one and a lower bound -eta for its real trace pairing with every actual effect imply the existence of one actual positive semidefinite rho with complex trace exactly one, uniformly within 3*eta of A on every actual effect. Both positive-trace and zero-positive-trace branches are included.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityRepair.mul_negativeProjector`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityRepair.negativeProjector`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityRepair.negativeProjector_effect`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityRepair.psd_effect_pairing_bounds`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityRepair.psd_trace_real`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityRepair.uniform_density_repair`
- Dependency: [D5/S3/Quantum/Foundation/EffectAdditivityStability](EffectAdditivityStability.md)
