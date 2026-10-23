# Bipartite graceful extension

## Abstract

Uniform bipartite graceful paths and their two-block attachments.

**Theorem 1.1 (Every size at least two has both block orientations).**

Lean statement: `D5/S1/Words/Sequenceability/BipartiteGracefulExtension.exists_two_block_attachment`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/BipartiteGracefulExtension.exists_two_block_attachment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural s at least two, every natural L, and each Boolean orientation flip, there is a list q permuting exactly 0 through 2s+1. It begins at s-1 and ends at 2s. Every adjacent pair crosses the split between s and s+1, so the list alternates between its low and high halves. Its ordinary absolute adjacent differences permute exactly 1 through 2s+1.

In the false orientation, send a low label q to L+q and a high label q to L+s+q. In the true orientation, send a low label q to L+3s+1-q and a high label q to L+(2s+1-q). Append the vertex L+2s in the false orientation, or L+s+1 in the true orientation. The absolute adjacent differences of this appended mapped list permute exactly s through 3s+1, each once. The differences here are linear-path differences; no closing edge or cyclic inventory is asserted.

The auxiliary bases at s=2,3,4,5 are respectively (1,5,0,3,2,4), (2,5,3,4,0,7,1,6), (3,6,4,5,1,9,0,7,2,8), and (4,6,5,8,1,9,3,7,2,11,0,10). To pass from s to s+4, add two to low labels and six to high labels, prefix (s+3,s+6,s+4,s+5), and suffix (0,2s+9,1,2s+8). The old edge lengths increase by four. The prefix and its attachment contribute 3,2,1,4; the suffix attachment and its internal edges contribute 2s+6,2s+9,2s+8,2s+7. These and the shifted old interval partition 1 through 2s+9. Strong induction with the four bases covers every s at least two.

Both block maps increase every crossing edge length by s. The final auxiliary label 2s maps to L+3s in the false orientation, or L+1 in the true orientation. Its edge to the appended vertex therefore has length s. With H=L+3s+1, the blocks are L through L+s and H-s through H. The appended vertex lies between them, at distance one from the nearer endpoint and s from the farther endpoint.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/BipartiteGracefulExtension.exists_two_block_attachment`
