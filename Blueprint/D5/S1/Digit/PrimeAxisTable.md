# Prime-Axis W-Digit Tables

## Abstract

Finite prime-indexed canonical W digits encode factorization exponents.

**Theorem 1.1 (Finite prime-axis table and product decode).**

$$\forall z \in \operatorname{PrimeAxisTable},\ (\forall p,\ \operatorname{CanonicalRaw}(z.\operatorname{digits}(p))) \land \operatorname{Finite}(\operatorname{support}(z.\operatorname{digits})) \land (\forall p,\ \operatorname{axisExponent}(z,p) = \sum_{k \in \operatorname{support}(z.\operatorname{digits}(p))} z.\operatorname{digits}(p,k)\,w(k)) \land \operatorname{decodePrimeAxisTable}(z) = \prod_{p \in \operatorname{support}(z.\operatorname{digits})} p^{\operatorname{axisExponent}(z,p)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxisTable.prime_axis_table_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An outer finitely supported table assigns canonical binary nonadjacent W digits to prime axes. The theorem exposes finite global support, each W-weighted exponent sum, and the corresponding finite prime-power product decode.

## References

- Truth anchor: `D5/S1/Digit/PrimeAxisTable.prime_axis_table_spec`
- Dependency: [D5/S1/Digit/Raw](Raw.md)
