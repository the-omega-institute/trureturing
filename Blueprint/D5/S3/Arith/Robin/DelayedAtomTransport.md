# DelayedAtomTransport

## Abstract

A later insertion excludes a short closed pulse

**Theorem 1.1 (Price loss is the integrated weight).**

Lean statement: `D5/S3/Arith/Robin/DelayedAtomTransport.curve_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/DelayedAtomTransport.curve_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a price curve on x>1 with derivative minus its continuous positive nonincreasing weight, and 1<a<=b, price(a)-price(b) equals the interval integral of weight over [a,b].

This is a consumed fundamental-calculus helper for the slope estimate, finite pulse accounting, and the original error bound. It is not claimed as new mathematical content.

**Theorem 1.2 (Endpoint bounds for the price loss).**

Lean statement: `D5/S3/Arith/Robin/DelayedAtomTransport.curve_slope_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/DelayedAtomTransport.curve_slope_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same curve and 1<a<=b, (b-a)*weight(b)<=price(a)-price(b)<=(b-a)*weight(a).

The integral identity and the nonincreasing weight give both endpoint bounds. The delayed-atom exclusion consumes the lower and upper estimates.

**Theorem 1.3 (A later insertion excludes a short closed pulse).**

Lean statement: `D5/S3/Arith/Robin/DelayedAtomTransport.delayed_atom_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/DelayedAtomTransport.delayed_atom_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let price have derivative minus weight on x>1, with continuous positive nonincreasing weight. For y<a+1, t>1, h>0 and C>=t, assume h*price(y)<=the integral from C to C+h of price and 2*weight(t)<h*weight(t+h). Then t is outside the closed interval [a,y].

The average price over [t,t+h] loses at least h*weight(t+h)/2 from price(t). Shifting the average to C can only decrease it. Contact would give price(t)-price(y)<weight(t), contradicting the paid density. The original integer specialization proves both insertion compatibility and density; no interpolated integer maximizer is assumed.

The compact reference kernel uses t<z<=B, while the strict actual kernel uses t<=z<=B. Before exclusion, the actual initial atom has weight (price(t)-price(B))/D and the reference initial atom has weight zero. Both terminal weights are zero. These kernels take a price parameter and do not define another original arithmetic price.

## References

- Truth anchor: `D5/S3/Arith/Robin/DelayedAtomTransport.curve_difference`
- Truth anchor: `D5/S3/Arith/Robin/DelayedAtomTransport.curve_slope_bounds`
- Truth anchor: `D5/S3/Arith/Robin/DelayedAtomTransport.delayed_atom_exclusion`
