# Finite Realization of Periodic-Point Tables

## Abstract

A finite cyclic action realizes a divisor table exactly when its Mobius data count whole cycles.

**Theorem 1.1 (The finite divisor-table criterion).**

$$\forall a:\mathbb{N}\to \mathbb{N}, M\in \mathbb{N}_{>0}, (\exists \sigma:\operatorname{Perm}\left(\operatorname{Fin}\left(\operatorname{a}\left(M\right)\right)\right), \sigma^{M}=1\land (\forall d\in \mathbb{N}, d\mid M\Rightarrow \operatorname{A}\left(\sigma, d\right)=\operatorname{a}\left(d\right)))\iff (\forall d\in \mathbb{N}, d\mid M\Rightarrow 0\leq \Delta(a,d)\land d\mid \Delta(a,d))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/FiniteRealization.finite_realization_iff` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

Fix a positive natural M and a natural-valued table a. There is a permutation of Fin (a M), with Mth power the identity and fixed count a d for every divisor d of M, exactly when the integer Mobius transform at each such d is nonnegative and divisible by d. In the formula A(sigma,d) is the actual fixedCount, and delta is the integer factor-pair Mobius transform defined in OrbitCounting.

The converse takes delta(a,d) divided by d copies of the cyclic set ZMod d and advances every copy by one. Mobius inversion gives the required fixed counts. At time M every point returns, so the total carrier has cardinality a M and can be relabeled by Fin (a M). This is a finite restriction of the classical exact-realization criterion.

The table's value at zero and its values away from divisors of M are unused. The empty carrier, M equal to one, and singleton cycles are included. The permutation's order divides M; equality of the order with M and transitivity are not asserted. Positive-time fixed counts extend along the greatest common divisor with M, so arbitrary prescribed outside-divisor values cannot be inferred.

## References

- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/FiniteRealization.finite_realization_iff`
- Dependency: [D5/S1/Dynamics/PeriodicOrbits/OrbitCounting](OrbitCounting.md)
