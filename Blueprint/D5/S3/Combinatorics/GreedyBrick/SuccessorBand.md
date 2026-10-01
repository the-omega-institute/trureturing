# Successor Band for Exact-Reset Event Histories

## Abstract

Exact-reset chronological event histories satisfy the successor birth band.

**Theorem 1.1 (Chronological predecessor injection bounds the renewal height).**

$$b_{h} \leq H < b_{h+1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GreedyBrick/SuccessorBand.successor_band` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An event history has chronological indices, positive bin labels bounded by nondecreasing heights, total positive-height births with exact strict cuts, brick endpoints whose increments equal event labels, and immediate same-bin predecessors of renewals. Its reset balance states n+h+rho(e)=H+rho(f), where rho counts strictly earlier renewals at higher bins. Under these explicit laws, every renewal f with predecessor e of height h has height H between the actual birth endpoints b_h and b_(h+1).

For a first hypothetical lower-band violation, strong chronological induction puts every earlier renewal's predecessor before birth h. Immediate predecessors pair injectively. Births in that strict cut inject into their distinct labels above the current bin and below h; remaining events are earlier higher-bin renewals. Their combined count contradicts the reset balance. The upper band uses the length h+1 of the next birth event.

This is a conditional event-history component for OEIS A395531. The literal highest-eligible-row process must still supply the rest-event correspondence, first-zero transition, total birth indices, predecessor laws, and reset balance. Future same-bin successor existence, the cut bijection, weighted reciprocity, and the original all-index identity are not delivered here.

## References

- Truth anchor: `D5/S3/Combinatorics/GreedyBrick/SuccessorBand.successor_band`
