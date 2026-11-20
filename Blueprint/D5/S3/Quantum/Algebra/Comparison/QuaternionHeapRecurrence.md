# Chebyshev formulas for the quaternion heap recurrence

## Abstract

Quaternion heap iterates admit a Chebyshev formula at every index.

**Theorem 1.1 (The cubic recurrence and the Chebyshev formulas).**

$$\forall x \in \mathbb{N} \to \mathbb{H},\; \left(\left\lVert \operatorname{x}\left(0\right) \right\rVert^{2} = 1 \land \left(\left\lVert \operatorname{x}\left(1\right) \right\rVert^{2} = 1 \land \left(\forall j \in \mathbb{N},\; \operatorname{x}\left(j + 2\right) = \operatorname{x}\left(j + 1\right) \cdot \overline{\operatorname{x}\left(j\right)} \cdot \operatorname{x}\left(j + 1\right)\right)\right)\right) \Leftrightarrow \left(\forall n \in \mathbb{N},\; \left\lVert \operatorname{x}\left(n\right) \right\rVert^{2} = 1 \land \left(\operatorname{x}\left(n + 1\right) = U_{n}\left(\operatorname{c}\left(\operatorname{x}\left(0\right), \operatorname{x}\left(1\right)\right)\right) \cdot \operatorname{x}\left(1\right) - U_{n - 1}\left(\operatorname{c}\left(\operatorname{x}\left(0\right), \operatorname{x}\left(1\right)\right)\right) \cdot \operatorname{x}\left(0\right) \land \operatorname{c}\left(\operatorname{x}\left(0\right), \operatorname{x}\left(n\right)\right) = T_{n}\left(\operatorname{c}\left(\operatorname{x}\left(0\right), \operatorname{x}\left(1\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Comparison/QuaternionHeapRecurrence.normSq_and_chebyshev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write c(a,b) for the real inner product and bar for quaternion conjugation. The squared norm is multiplicative, so the cubic recurrence preserves unit norm. For a unit center, reflection has the form twice the projection onto the center minus the original vector. Pairing the reflection with its center preserves the adjacent inner product, which is therefore constant. The resulting linear recurrence has the second-kind Chebyshev solution with the given first two samples. Pairing that solution with the initial sample yields the first-kind Chebyshev polynomial. The formulas use the integer indices of the polynomials, with U at minus one equal to zero and U at minus two equal to minus one. Conversely, the sample formula satisfies the same linear recurrence. Pairing it with a unit sample recovers the constant adjacent comparison, so the reflection formula recovers the cubic recurrence. The sequences (0,1,0,0,...) and (1,0,0,0,...) obey the cubic recurrence and show that each initial unit assumption is necessary. The sequence (1,1,0,0,...) has two unit initial samples and fails the unit conclusion at index two when the recurrence is omitted. These examples follow by direct substitution into the recurrence and squared norm.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Comparison/QuaternionHeapRecurrence.normSq_and_chebyshev`
