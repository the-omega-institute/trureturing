# Positive order-norm support

## Abstract

Positive normalized order-norm support on the original carrier.

For every nonzero vector in the original real normed carrier, the closed salient cone with its specified interior unit supplies a real-linear functional nonnegative on the cone, normalized at the unit, bounded by the orderNorm everywhere, and attaining the orderNorm at that vector. The carrier remains arbitrary and possibly incomplete; no finite-dimensionality, completeness, self-duality or prior state-existence premise is introduced.

**Theorem 1.1 (Positive norm support on the entire original carrier).**

$$\forall E \in Types,\; RealNormedVectorSpace\left(E\right) \Rightarrow \left(\forall A \in ConeUnitData\left(E\right),\; \forall a \in E,\; a \ne 0 \Rightarrow \left(\exists beta \in RealLinearReadings\left(E\right),\; \left(\forall x \in cone\left(A\right),\; 0 \le beta\left(x\right)\right) \land \left(beta\left(unit\left(A\right)\right) = 1 \land \left(\left(\forall x \in E,\; abs\left(beta\left(x\right)\right) \le orderNorm\left(A\right)\left(x\right)\right) \land abs\left(beta\left(a\right)\right) = orderNorm\left(A\right)\left(a\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrderNormSupport.positive_norm_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r=orderNorm(a)>0. The two attained cone points r unit-a and r unit+a cannot both be interior, since a common positive decrease would remain a radius. Hahn-Banach support at a noninterior endpoint gives a continuous positive functional with zero endpoint value and positive unit mass; normalize by that mass.

The endpoint equation gives absolute value r at a, and the exposed positive-bound supplier gives the global order-norm bound. This mathematical reading is consumed directly by the original unit-row closed-ball and semidefinite proofs; it constructs no physical preparation. The four-slot audit remains unfinished under issue 28178.

## References

- Truth anchor: `D5/S3/Topology/OrderNormSupport.positive_norm_support`
- Dependency: [D5/S3/Topology/OrderUnitNorm](OrderUnitNorm.md)
