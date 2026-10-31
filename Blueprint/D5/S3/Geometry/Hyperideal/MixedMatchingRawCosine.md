# Mixed matching raw cosine reduction

## Abstract

The symmetric six-variable hyper-ideal cosine reduces to the radial closed form used by mixed matching.

For the symmetric six-variable generalized length vector (r,t,t,o,t,t), the original six-variable cosine formula reduces to the radial expression used in the mixed matching construction.

**Theorem 1.1 (Radial raw cosine formula).**

Lean statement: `D5/S3/Geometry/Hyperideal/MixedMatchingRawCosine.raw_cosine_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/MixedMatchingRawCosine.raw_cosine_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r>1 and t>0, define Q=2*t^2/(r-1). The six-variable cosine at (r,t,t,o,t,t) equals (Q-o)/(Q+1).

The proof factors the numerator and both equal radicands, then cancels the positive common factor and square root.

This is an algebraic raw-formula reduction. It does not assert genuine angle-domain membership or construct a face pairing.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/MixedMatchingRawCosine.raw_cosine_formula`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
