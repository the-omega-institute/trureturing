# Prime-Axis Encoding

## Abstract

Prime-indexed canonical W rows encode positive naturals and transport multiplication to table addition.

**Definition 1.1 (Prime-axis encoding is the canonical bijection).**

Lean statement: `D5/S1/Digit/PrimeAxisEncoding.primeAxisEncoding`

*Formalization.* `D5/S1/Digit/PrimeAxisEncoding.primeAxisEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Canonical finite-support W rows on every prime axis are equivalent to positive natural numbers. The forward map decodes each axis to its prime exponent and then applies unique factorization.

**Theorem 1.2 (Prime-axis table equivalence and multiplication).**

$$\forall z,w \in \operatorname{PrimeAxisTable},\ \operatorname{Bijective}(\operatorname{primeAxisEncoding}) \land \operatorname{coe}_{\mathbb{N}}(\operatorname{primeAxisEncoding}(z)) = \operatorname{decodePrimeAxisTable}(z) \land \operatorname{decodePrimeAxisTable}(\operatorname{normalizedTableAdd}(z,w)) = \operatorname{decodePrimeAxisTable}(z)\operatorname{decodePrimeAxisTable}(w)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxisEncoding.prime_axis_encoding_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finitely supported prime axes carrying canonical W rows are equivalent to positive naturals through their factorization exponents. Addition transported through this equivalence decodes exactly as multiplication.
