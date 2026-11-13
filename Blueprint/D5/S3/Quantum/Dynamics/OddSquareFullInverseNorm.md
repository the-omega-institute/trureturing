# From an interior odd square to the full inverse

## Abstract

An interior repeated odd block forces Euclidean amplification by the whole finite inverse.

**Theorem 1.1 (A unit vector for the complete open block).**

$$\forall t \in \mathbb{N} \to \mathbb{R},\; \forall n \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall q \in \mathbb{N},\; \left(\forall i \in \mathbb{N},\; 0 < t\left(i\right)\right) \Rightarrow \left(\left(\forall i \in \mathbb{N},\; t\left(i\right) \le 1\right) \Rightarrow \left(1 \le q \Rightarrow \left(a + 2 \cdot q + 1 \le n \Rightarrow \left(\left(\forall i \in \mathbb{N},\; i < 2 \cdot q \Rightarrow t\left(2 \cdot a + i + 2 \cdot q + 1\right) = t\left(2 \cdot a + i\right)\right) \Rightarrow \left(\exists v \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \left\lVert v \right\rVert = 1 \land q \cdot \left(q + 1\right) \le 2 \cdot n \cdot \left\lVert \operatorname{A}\left(t, n\right)\left(v\right) \right\rVert\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/OddSquareFullInverseNorm.full_inverse_unit_amplification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L(t,n) be the sign-conjugated bidiagonal block defined in OddSquareGreenMass, and write A(t,n) for the linear map on EuclideanSpace R (Fin n) induced by its inverse. All vector norms here are Euclidean. The hoppings are positive and at most one. The odd window has length 2q+1, starts at bond 2a, and fits inside the full block: a+2q+1 is at most n. Repetition is required only at the 2q stated bond positions. There is no exterior or closing bond assumption.

The original forward-substitution inverse formula shows that translating both row and column by a transports an entry of the local inverse to the full inverse. Thus both exterior portions of the path remain present. All full inverse entries are nonnegative. The quadratic paired mass from OddSquareGreenMass therefore bounds twice the sum of all entries: each of its two triangular regions embeds injectively in the full matrix. The factor two avoids any need to discard overlap. For the constant vector x with all coordinates one, this entry sum is the Euclidean inner product of x with Ax. Cauchy--Schwarz and the identity norm(x) squared equals n give the displayed inequality for v=x/norm(x). The hypotheses imply n is positive, so v is defined and has norm one.

This estimate concerns the actual inverse of the full finite bidiagonal block. It does not by itself identify an eigenvalue of the full symmetric hopping matrix or prove the all-prefix Tribonacci spectral rate. Those conclusions additionally require the sublattice spectral identification, the actual word-to-hopping substitution, uniform size comparison, and the small prefixes.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/OddSquareFullInverseNorm.full_inverse_unit_amplification`
- Dependency: [D5/S3/Quantum/Dynamics/OddSquareGreenMass](OddSquareGreenMass.md)
