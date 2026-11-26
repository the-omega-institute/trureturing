# Short Frobenius readout for an inert golden cubic probe

## Abstract

The inert cubic branch orientation is recovered from a short norm-one power.

**Theorem 1.1 (One short norm-one power gives the exact inert branch shift).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicInertFrobeniusReadout.native_inert_readout`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicInertFrobeniusReadout.native_inert_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be prime, greater than three and congruent to two modulo three. Work in characteristic q with x fixed by Frobenius, and choose a square root delta of minus three that Frobenius negates. Put B=x squared plus three and assume B is nonzero. The choice x equal to the native Lucas value at index 3^i is fixed by Frobenius because it is an integer residue.

The normalized power of beta=B times (-x+delta) with exponent (q+1)/3, divided by B, equals the usual power with exponent (q squared minus one)/3. This value epsilon is a third root of unity. A cube root of beta labels the actual depressed cubic branches by third roots of unity. Frobenius sends label a to a divided by epsilon rather than to a multiplied by epsilon. The labels are injective and the identity branch is fixed exactly when epsilon equals one.

This proves the finite-field branch formula uniformly, not reciprocity over the native number fields, prime-distribution bounds, or a Wall-Sun-Sun exclusion.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicInertFrobeniusReadout.native_inert_readout`
