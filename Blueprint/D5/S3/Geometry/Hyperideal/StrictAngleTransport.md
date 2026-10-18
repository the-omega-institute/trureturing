# Strictifying an actual angle vector by paired-corner transport

## Abstract

A bounded actual transport correction preserves edge sums and makes every corner sum strict.

**Theorem 1.1 (A bounded actual correction preserves M and makes Q strict).**

Lean statement: `D5/S3/Geometry/Hyperideal/StrictAngleTransport.strict_angle_correction`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/StrictAngleTransport.strict_angle_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite T and S, use the actual Pairing, Corner, Occurrence, GlobalEdge, M and Q from ActualCornerTransport. Given corner maps u,v, weights w, a base vector a₀, and real B,m, assume same-component labels, nonnegative weights, component mass at most B, m≤a₀(o) for every occurrence, and Q(a₀,c)≤1 for every corner. Also assume the explicit strict positive divergence sum at every corner, 0<m, and 3B≤m/2.

Then there is a real occurrence vector a such that every a(o)>0, M(a,e)=M(a₀,e) for every actual global edge, Q(a,c)<1 for every actual corner, and |a(o)-a₀(o)|≤3B for every occurrence.

The construction obtains the actual slot paths and lift from ActualCornerTransport.actual_corner_transport, sets a=a₀+lift, and uses finite-sum linearity. The edge identity is the transport zeroM field. The strict corner inequality combines its deficit identity with the supplied positive divergence premise. The occurrence estimate is the actual six-slot bound.

The positive divergence premise is an explicit interface assumption; this theorem does not claim that general CFMP data automatically satisfy it. It does not construct common lengths, a geometric realization, a global gluing, or a complete strictification theorem for arbitrary flat blocks. M sums all actual repeated occurrences, and Q uses the actual local endpoint incidence from the paired tetrahedral slots.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/StrictAngleTransport.strict_angle_correction`
- Dependency: [D5/S3/Geometry/Hyperideal/ActualCornerTransport](ActualCornerTransport.md)
