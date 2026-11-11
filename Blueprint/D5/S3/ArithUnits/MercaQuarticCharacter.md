# The Normalized Quartic Character

## Abstract

For every prime r congruent to five modulo eight, the actual complex Dirichlet character of order four with value i at two exists uniquely. It is primitive and odd. Its literal unit kernel has index four and cardinality (r-1)/4.

All moduli are natural numbers; primality is Mathlib's Nat.Prime. Characters are actual DirichletCharacter values on ZMod r with complex coefficients, extended by zero at nonunits. Order is multiplicative order. Odd means chi(-1)=-1, and primitive means that the conductor equals r. The finite character statements include r=5. The historical actual-field class-number formula has the separate restriction r>5.

**Theorem 1.1 (Existence, normalization and uniqueness).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticCharacter.normalized_quartic_exists_unique`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaQuarticCharacter.normalized_quartic_exists_unique` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every prime r with r mod 8 equal to 5, there exists a complex Dirichlet character chi modulo r with order exactly four, chi(2)=i, primitive conductor and odd parity. Every complex Dirichlet character psi modulo r with order four and psi(2)=i equals this chi. Choose an auxiliary generator g of the full finite unit group. Two is nonsquare, so its exponent in g is odd. Construct the character with chi(g)=i and choose it or its cube to orient the value at two. The generator's half-order power is minus one, which proves oddness since (r-1)/2 is 2 modulo 4. An odd exponent is invertible modulo four, proving uniqueness. The nonprincipal character at a prime modulus is primitive. Two need not be a generator.

**Definition 1.2 (The canonical normalized character).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticCharacter.character`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticCharacter.character` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For a prime r and a proof that r mod 8 is 5, character r is a choice of the preceding unique normalized character. Uniqueness removes dependence on the auxiliary generator. The coefficient field is the complex numbers.

**Definition 1.3 (The actual unit kernel).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticCharacter.kernel`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticCharacter.kernel` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Kernel r is the kernel of character r restricted to the actual unit group of ZMod r, with values in the complex unit group. It consists of precisely the units on which the character is one.

**Theorem 1.4 (Kernel cardinality, index and omitted minus one).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticCharacter.kernel_structure`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaQuarticCharacter.kernel_structure` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every prime r congruent to 5 modulo 8, the canonical character has order four, value i at two, primitive conductor, odd parity and the uniqueness property above. Its actual kernel K has cardinality (r-1)/4 and index four, and minus one does not belong to K. The image is exactly the four complex fourth roots of unity: every value is a fourth root, and powers of the unit two realize all four roots. The kernel-index formula gives the cardinality. Oddness excludes minus one.

## References

- Truth anchor: `D5/S3/ArithUnits/MercaQuarticCharacter.character`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticCharacter.kernel`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticCharacter.kernel_structure`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticCharacter.normalized_quartic_exists_unique`
