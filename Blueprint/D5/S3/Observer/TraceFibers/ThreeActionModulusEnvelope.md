# Three Action Modulus Envelope

## Abstract

The fixed Fibonacci fiber interface gives the scalar envelopes of the two distinguished three-action continuations, together with the finite word shapes.

**Theorem 1.1 (Three-action scalar envelope).**

Lean statement: `D5/S3/Observer/TraceFibers/ThreeActionModulusEnvelope.three_action_modulus_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/TraceFibers/ThreeActionModulusEnvelope.three_action_modulus_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For words of length at most three in the advance and exchange actions, the pair consisting of the diagonal difference and lower-left entry has the seven listed values.

For a positive rank-one fiber with x=(k+h)r, the frozen fixed-fiber modulus theorem applied to MJM and M^3 gives the scalar suprema with parameters (2-h,1) and (2-2h,2), respectively.

The quadratic separation functions satisfy phi_A(d)-phi_S(d)=d(d/r-h); their common spacing is rh and their common tolerance is 2rh. The threshold values are ordered as 0<2rh<(k+2)x<2(k+1)x.

## References

- Truth anchor: `D5/S3/Observer/TraceFibers/ThreeActionModulusEnvelope.three_action_modulus_envelope`
- Dependency: [D5/S3/Observer/TraceFibers/FixedFiberPairModulus](FixedFiberPairModulus.md)
