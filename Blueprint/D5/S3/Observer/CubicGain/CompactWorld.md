# CompactWorld

## Abstract

The closure equations hold for every actual strict parent, using the same original gain and fixed drift throughout

The closure equations hold for every actual strict parent, using the same original gain and fixed drift throughout. Multiplication by U=1+2b applies uniformly to the entire gain polynomial, and gain_scale expresses the linearity of interpolation and gives its clock-four equation.

Bounded fifth responses already bound ε and the original whole gain. For b≤1, U≤3 gives a bound for every scaled gain sample. For b≥1, U/j≤3, U/n≤3 and U/T≤2 bound scaled samples 1,3,2 respectively. The scaled clock-four reading and the cubic fourth-difference identity then bound sample zero. This establishes a uniform bound on the whole scaled gain, including b→∞.

**Theorem 1.1 (gain scale).**

Lean statement: `D5/S3/Observer/CubicGain/CompactWorld.gain_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/CompactWorld.gain_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sample vector a and real scalars t,s, multiplying all four samples by t multiplies the whole interpolated gain at s by t.

**Theorem 1.2 (closureWorld actual).**

Lean statement: `D5/S3/Observer/CubicGain/CompactWorld.closureWorld_actual`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/CompactWorld.closureWorld_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every strict parent gives a ClosureWorld with its compact source, drift offset, original gain, whole scaled gain and actual fifth and sixth responses.

**Theorem 1.3 (bounded fifth bounds scaled gain).**

Lean statement: `D5/S3/Observer/CubicGain/CompactWorld.bounded_fifth_bounds_scaled_gain`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/CompactWorld.bounded_fifth_bounds_scaled_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real M there are bounds D,G,H such that every strict parent with |P₅|≤M has |ε|≤D, |aᵢ|≤G and |(Ua)ᵢ|≤H for all four original sample indices.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/CompactWorld.bounded_fifth_bounds_scaled_gain`
- Truth anchor: `D5/S3/Observer/CubicGain/CompactWorld.closureWorld_actual`
- Truth anchor: `D5/S3/Observer/CubicGain/CompactWorld.gain_scale`
- Dependency: [D5/S3/Observer/CubicGain/EscapeBarrier](EscapeBarrier.md)
