# Prime-Axis Encoding

## Abstract

Prime-indexed canonical W rows encode positive naturals and transport multiplication to table addition.

**Theorem 1.1 (Prime-axis table equivalence and multiplication).**

$$\forall z,w \in \operatorname{PrimeAxisTable},\ \operatorname{Bijective}(\operatorname{primeAxisEncoding}) \land \operatorname{coe}_{\mathbb{N}}(\operatorname{primeAxisEncoding}(z)) = \operatorname{decodePrimeAxisTable}(z) \land \operatorname{decodePrimeAxisTable}(\operatorname{normalizedTableAdd}(z,w)) = \operatorname{decodePrimeAxisTable}(z)\operatorname{decodePrimeAxisTable}(w)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxisEncoding.prime_axis_encoding_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finitely supported prime axes carrying canonical W rows are equivalent to positive naturals through their factorization exponents. Addition transported through this equivalence decodes exactly as multiplication.
