# Erdos 699 Shared Exponent Caps

## Abstract

Exact 11-23 shared-exponent residues and their four impossible lift rows.

**Theorem 1.1 (Base-two residues and prime-power returns).**

$$\left(\left(\left(\left(2^{8} \bmod 11 = 3 \land 2^{8} \bmod 23 = 3\right) \land 2^{10} \bmod 121 = \left(1 + 5 \cdot 11\right) \bmod 121\right) \land 2^{110} \bmod 121 = 1\right) \land 2^{10} \bmod 11 = 1\right) \land 2^{11} \bmod 23 = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Erdos699/SharedExponentCaps.prime_and_lift_residues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact numeral identities give the residues of 2 at the two endpoint primes, the first lift modulo 121, the return at exponent 110, and the prime periods modulo 11 and 23.

**Theorem 1.2 (No earlier multiple of ten returns modulo 121).**

$$\forall z \in \mathbb{N},\; \left(0 < z \land z < 11\right) \Rightarrow 2^{10 \cdot z} \bmod 121 \ne 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Erdos699/SharedExponentCaps.first_return_mod_121` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive z below 11, the exponent 10z does not return 2 to one modulo 121.

**Theorem 1.3 (The four endpoint lift rows have empty intersections).**

$$\forall N \in \mathbb{N},\; \left(\left(\left(N \bmod 110 \ne 0 \lor N \bmod 11 \ne 1\right) \land \left(N \bmod 110 \ne 22 \lor N \bmod 11 \ne 4\right)\right) \land \left(N \bmod 110 \ne 1 \lor N \bmod 11 \ne 0\right)\right) \land \left(N \bmod 110 \ne 23 \lor N \bmod 11 \ne 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Erdos699/SharedExponentCaps.shared_lift_caps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural exponent, each row excludes at least one of its two required residues. The four rows therefore cannot be realized by one common exponent.

## References

- Truth anchor: `D5/S3/Arith/Erdos699/SharedExponentCaps.first_return_mod_121`
- Truth anchor: `D5/S3/Arith/Erdos699/SharedExponentCaps.prime_and_lift_residues`
- Truth anchor: `D5/S3/Arith/Erdos699/SharedExponentCaps.shared_lift_caps`
