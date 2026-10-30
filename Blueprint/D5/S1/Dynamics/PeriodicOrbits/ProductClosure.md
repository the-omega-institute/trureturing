# Product closure for finite periodic actions

## Abstract

Direct products multiply fixed-point tables and preserve the finite Dold divisibility obstruction.

**Theorem 1.1 (Fixed points of a direct product).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/ProductClosure.fixed_count_prodMap`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/ProductClosure.fixed_count_prodMap` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

For finite carriers X and Y and self-maps f and g, the n-th iterate of the direct product action (f,g) fixes exactly the Cartesian product of the points fixed by f^n and g^n. Hence its fixed-point count is the pointwise product of the two fixed-point counts.

The proof is an explicit equivalence between the fixed-point subtype of Prod.map f g and the product of the two fixed-point subtypes. It uses the actual iterate identity for Prod.map, so it records the group-action product rather than merely multiplying two natural numbers.

**Theorem 1.2 (Dold nonnegativity survives direct products).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/ProductClosure.product_dold_nonneg_dvd`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/ProductClosure.product_dold_nonneg_dvd` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

The pointwise product of the fixed-count sequences of two finite actions again has a nonnegative, period-divisible Mobius transform. This is the arithmetic shadow of the direct-product action: apply the actual orbit-counting Mobius identity to Prod.map f g and use the fixed-count product theorem.

Thus Dold's obstruction is closed under products of finite cyclic actions. The result is stronger than an abstract multiplication identity because it obtains positivity and divisibility from an explicit finite dynamical realization.

**Theorem 1.3 (Divisor-table product consumer).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/ProductClosure.finite_table_product_dold`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/ProductClosure.finite_table_product_dold` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

If two tables are realized on finite cyclic actions through the divisors of a positive exponent M, then their pointwise product satisfies the same nonnegative and divisible Mobius conditions at every divisor of M. The table equalities are transported term by term through the finite divisor antidiagonal, giving a reusable consumer for products of periodic systems.

## References

- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/ProductClosure.finite_table_product_dold`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/ProductClosure.fixed_count_prodMap`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/ProductClosure.product_dold_nonneg_dvd`
- Dependency: [D5/S1/Dynamics/PeriodicOrbits/FiniteRealization](FiniteRealization.md)
