# Chinese-remainder identities for finite sieve moments

## Abstract

Chinese-remainder identities for finite sieve moments

**Theorem 1.1 (centered sieve moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCRTMoments.centered_sieve_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCRTMoments.centered_sieve_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural cutoff y and every finite set D of natural shifts, the expectation modulo the primorial of y of the product of the centered sieve variables indexed by D equals the inclusion–exclusion transform of the finite singular series on D. Chinese remaindering counts the simultaneous surviving residues prime by prime; the commutative-ring centered product expansion applied to each sieve variable plus one gives the stated transform.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCRTMoments.centered_sieve_moment`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredProductExpansion](../CentredProductExpansion.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SingularSeriesTail](SingularSeriesTail.md)
