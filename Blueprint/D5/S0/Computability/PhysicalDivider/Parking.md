# Parking a Divider Tape

## Abstract

The divider's bit-tape parking loop returns to the fixed origin without enlarging its charged extent.

Fix an active tape k, a continuation next, a family of tapes t, Boolean lists b and a, and an integer H. Put n = length(b). Assume 2n <= H and Within(stackWithAbove(b,a),(2n,0,H)). Let S be accountedBlockStep extended to optional states by binding, and let P be physicalStep extended in the same way. Powers denote iteration and some denotes a present state.

Let I = ((parkMarker,stackWithAbove(b,a)),(2n,0,H)). Let O be the tape at the origin with empty left list and right list [false,true], followed by [true,v] for each bit v of reverse(b), followed by a. Let E be the block configuration (finished none,O). For a block configuration x, write L(x) = liftBlockCfg(k,next,t,x). Let C be the physical configuration with control continueBlock(next,none) and tape family t updated at k to O. For an accounted state c, c1 and c2 denote its block configuration and extent; low(c), high(c) and head(c) are the fields of c2, and W(c) means Within(c1.tape,c2).

**Theorem 1.1 (Counted parking with support and visited-position bounds).**

$$S^{3n+1}(some(I))=some((E,(0,0,H))) \land P^{3n+2}(some(L(I_1)))=some(C) \land \forall i\in \mathbb{N}, i\le 3n+1 \implies \exists c\in BlockCfg\times Extent, S^i(some(I))=some(c) \land P^i(some(L(I_1)))=some(L(c_1)) \land low(c)=0 \land high(c)=H \land 0\le head(c)\le 2n \land W(c).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PhysicalDivider/Parking.park_preserves_extent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Boolean stack uses two cells per block. The bottom marker is 01, a data block is 1b, and blank cells are zero. The head begins at coordinate twice the number of data blocks below it. Arbitrary already traversed cells may remain above the head. The initial support and head must lie in the charged interval from zero to H.

Parking reads the current marker. At a data block it moves left twice and repeats; at the bottom marker it finishes. For n blocks this requires exactly 3n+1 elementary actions. One additional read executes the finite continuation in the full divider program. All other tapes retain their exact values and positions.

At every intermediate action the head lies between zero and its initial position. The lower and upper charged endpoints remain zero and H, and every nonblank cell stays inside that interval. The upper endpoint is preserved even when it records earlier visits or erased cells. The proof inducts over the blocks, proves the three-action transition to the next block, and lifts each block action to the concrete divider transition.

This theorem concerns the parking phase. Arithmetic refinement, the complete call time bound, and the complete call space bound are separate statements.

## References

- Truth anchor: `D5/S0/Computability/PhysicalDivider/Parking.park_preserves_extent`
