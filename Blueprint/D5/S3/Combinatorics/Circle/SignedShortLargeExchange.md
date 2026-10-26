# Signed short mass for the complete three-LARGE exchange

## Abstract

Construct an actual signed short-reserve return and consume it in the shared three-LARGE physical exchange.

The source is the actual centered doubling source on physical Fin k labels. This result is conditional on an actual signed short reserve after x; it does not assert universal reserve availability, transport across earlier gates, deeper suffix completion or full C3.1.

**Theorem 1.1 (Constructive signed short-reserve selector).**

Lean statement: `D5/S3/Combinatorics/Circle/SignedShortLargeExchange.signed_short_reserve_select`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/SignedShortLargeExchange.signed_short_reserve_select` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Nodup physical list T, P0 is a physical subpermutation of the entries with 0<f<=B+1 and N0 is a physical subpermutation of the entries with 0<-f<=B+1. Every positive entry of T is at most M, low>0 is supplied by the total positive mass, and the reserve resource is M-B-1 <= mass(P0)+mass(-f,N0).

Remove P0 from the actual positive list and first-cross the remainder at low-Sp. If it undershoots, first-cross P0 at the deficit. If it lands in [low,low+B], retain it. If it overshoots, first-cross N0 with weights -f at u-low-B and append that negative correction. The resulting R is physical, has mass in [low,low+B], and K is the explicit complement with (R++K).Perm T.

The selector uses only the existing PositiveSmallReturnExchange.first_crossing three times. Equal numerical values remain distinct occurrences; no subset-sum oracle or assumed return list is an input.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/SignedShortLargeExchange.signed_short_reserve_select`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeLargePacketExchange](ThreeLargePacketExchange.md)
