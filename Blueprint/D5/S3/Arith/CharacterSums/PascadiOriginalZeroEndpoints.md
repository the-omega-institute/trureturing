# The original zero-endpoint contribution

## Abstract

Actual original six-return rows with either physical endpoint equal to zero contribute at most eighteen times the literal area.

**Theorem 1.1 (Zero endpoints are counted by actual middle pairs).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalZeroEndpoints.actual_zero_endpoint_tuple_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalZeroEndpoints.actual_zero_endpoint_tuple_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c be any nonzero modulus. Assume real widths X,Y>=1 and 2X<c, 2Y<c, and fix the two alternating units modulo c. Let T be a finite set of the original integer rows (a,b,w;d,v,t), with every first-row entry bounded in absolute value by X and every second-row entry bounded by Y. Require the existing six-return word, in its unchanged order (a,t,b,d,w,v), to be minus the identity. If every row has either physical endpoint (a,d)=(0,0) or (b,v)=(0,0), then card(T)<=18XY.

A zero endpoint makes the product term in each original row equation vanish, so both original row sums are zero modulo c. Within either fixed zero-endpoint branch, the actual middle pair (w,t) then determines both coordinates of the other endpoint modulo c. The strict box-width inequalities lift those residue equalities to equalities of the original integers. Thus originalMiddle is injective on each branch. Its image lies in the literal integer middle rectangle, whose cardinality is at most (2X+1)(2Y+1)<=9XY. Partition by whether the first endpoint is zero and sum the two branch bounds.

The argument does not assume that the middle entries, the hyperbola right side or a shortest-vector coordinate are units. It needs no reduced basis and no long- or short-chart hypothesis. It counts this removed original-tuple branch only; the nonzero endpoint charts and the full prime-cube assembly remain separate.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalZeroEndpoints.actual_zero_endpoint_tuple_count`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalChartPieces](PascadiOriginalChartPieces.md)
