# Cayley Unitarity Defect

## Abstract

The zero-indexed Cayley operator is unitary exactly when every source zero is on the midline.

**Theorem 1.1 (Cayley unitarity defect formula).**

$$\forall n,\ ((C^{*}C-I)e_{n}=delta_{n}e_{n} \land delta_{n}=\Vert c_{n}\Vert^{2}-1 \land delta_{n}=\frac{1-2Re(rho_{n})}{\Vert rho_{n}\Vert^{2}}) \land (AllZerosOnMidline(Z) \iff \forall n,\Vert c_{n}\Vert=1) \land (AllZerosOnMidline(Z) \iff C^{*}C=I) \land (AllZerosOnMidline(Z) \iff \operatorname{Unitary}(C))$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/Cayley/CayleyUnitarityDefect.cayley_unitarity_defect_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Z be the repository's exhaustive duplicate-free enumeration of classical zeta zeros in the open strip. For each indexed zero rho_n, the coefficient c_n is constructed as (rho_n - 1)/rho_n. The operator C is the diagonal operator with these coefficients, its star conjugates them coordinatewise, and e_n is the coordinate basis vector.

On every coordinate, the star-unitarity defect sends e_n to delta_n e_n. The public statement identifies delta_n both as |c_n|^2 - 1 and as (1 - 2 Re(rho_n))/|rho_n|^2. Positivity of the real part in the source carrier makes every denominator nonzero.

Consequently, all enumerated zeros lie on the real-part-one-half midline if and only if every Cayley coefficient has norm one, if and only if C* C is the identity, if and only if C has its coordinatewise star as a two-sided inverse. The statement covers the full countable carrier and does not replace it with a finite matrix or a selected zero.

## References

- Truth anchor: `D5/S3/Midline/Cayley/CayleyUnitarityDefect.cayley_unitarity_defect_formula`
