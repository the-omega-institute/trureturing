# Normalized observation on derivative layers

## Abstract

Normalized observation on derivative layers

**Theorem 1.1 (Normalized observation on derivative layers).**

$$(\forall x\in U, \sum_{j<n} \pi\left(j, x\right) = x) \land (\exists K \ge 0,\\{}\forall T, s, (0<T \land T\left\lVert b \right\rVert<1 \land 0\le s\le 1) \Rightarrow \left\lVert F\left(T, s\right)-P\left(s\right) \right\rVert\le KT)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/DerivativeLayerNormalizedObservation.derivative_layer_normalized_observation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be an arbitrary finite-dimensional real inner-product space, and W an arbitrary complete real inner-product space. Let B:V→V and C:V→W be arbitrary linear maps. Neither observability of the whole V nor a positive dimension is assumed.

Put n=dim V, N(j)=the intersection of ker(C B^k) for 0≤k<j, U=N(n) orthogonal complement, E(j)=N(j) intersect N(j+1) orthogonal complement for 0≤j<n. Pi(j):V→V is the actual orthogonal projection onto E(j). All n layer indices are retained, even when their layer is zero. Write b and c for the continuous linear maps associated to B and C; i:U→V is the inclusion. All norms are induced Hilbert operator norms.

For each endomorphism X of V put L(j)(X)=c composed with X composed with Pi(j) composed with i. Define F(T,s)=sum over j<n of T^(-j) L(j)(exp(T s b)), and P(s)=sum over j<n of s^j/j! L(j)(b^j). The exponential is the actual normed-algebra exponential.

The projections sum to the inclusion on U. There is a nonnegative K, independent of T and s, for which the displayed estimate holds for every T>0 with T times the norm of b less than one and every s between zero and one.

Orthogonal differences resolve the descending kernel filtration. Every L(j)(b^k) vanishes for k<j. A uniform Taylor-tail bound for the actual exponential, followed by division by T^j and a finite norm sum, gives the linear error.

The finite derivative filtration supplies orthogonal geometry, while the exponential power series and Bochner integral supply the analytic operations.

## References

- Truth anchor: `D5/S3/Observer/Linear/DerivativeLayerNormalizedObservation.derivative_layer_normalized_observation`
