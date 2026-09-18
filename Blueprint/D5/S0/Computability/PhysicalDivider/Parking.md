# Parking a Divider Tape

## Abstract

The divider's bit-tape parking loop returns to the fixed origin without enlarging its charged extent.

**Theorem 1.1 (Counted parking with support and visited-position bounds).**

$$T=3n+2, \forall i\le 3n+1, 0\le h_i\le 2n, L_i=0, H_i=H.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PhysicalDivider/Parking.park_preserves_extent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Boolean stack uses two cells per block. The bottom marker is 01, a data block is 1b, and blank cells are zero. The head begins at coordinate twice the number of data blocks below it. Arbitrary already traversed cells may remain above the head. The initial support and head must lie in the charged interval from zero to H.

Parking reads the current marker. At a data block it moves left twice and repeats; at the bottom marker it finishes. For n blocks this requires exactly 3n+1 elementary actions. One additional read executes the finite continuation in the full divider program. All other tapes retain their exact values and positions.

At every intermediate action the head lies between zero and its initial position. The lower and upper charged endpoints remain zero and H, and every nonblank cell stays inside that interval. The upper endpoint is preserved even when it records earlier visits or erased cells. The proof inducts over the blocks, proves the three-action transition to the next block, and lifts each block action to the concrete divider transition.

This theorem concerns the parking phase. Arithmetic refinement, the complete call time bound, and the complete call space bound are separate statements.

## References

- Truth anchor: `D5/S0/Computability/PhysicalDivider/Parking.park_preserves_extent`
