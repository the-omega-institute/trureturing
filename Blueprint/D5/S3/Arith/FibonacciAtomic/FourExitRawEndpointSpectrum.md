# Four-Exit Raw Endpoint Spectrum

## Abstract

Four-exit trees, a zero-to-two raw-cost obstruction, and six local tail costs.

A right comb has k active slots and one compensation slot. Its baseline uses B in every active slot and R0 in the compensation slot. An exceptional member replaces one active block by A, Y, H, or Z and uses the corresponding compensation block.

The endpoint menu contains a vector with one zero and all other coordinates one for the baseline and each Y, H, or Z member. It also contains, for each slot, three vectors with zero at A, two at one of Y, H, or Z, and one elsewhere.

For every slot and every globally correct history-dependent controller, a cost of 8k + 16 on its A member forces a cost of at least 8k + 18 on one of its Y, H, or Z members. Restricting the actual response tree to these four members preserves the original controller's cost lower bound.

An A-leaf query is either common to the four members or gives two sibling members the same nonleaf reply. In the latter case, those two members must subsequently separate. Their shared leaf labels agree, so at least one receives another nonleaf reply before the response tree can reach singleton survivors.

On the five rows (baseline, A, Y, H, Z) at any selected slot, six finite actual response recipes attain the excess vectors (1,1,0,1,1), (1,1,1,0,1), (1,1,1,1,0), (1,0,1,2,1), (1,0,2,1,1), and (1,0,1,1,2). The response-cost core supplies a globally correct strategy for each recipe, with actual costs equal to 8k + 16 plus these coordinates.

**Theorem 1.1 (Structural identities for every right comb).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_foundation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_foundation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural slot count and arbitrary source blocks and tails, the third substitution acts on each block and the tail separately. The comb length is the sum of the block lengths and the tail length. Two combs with the same slot count are equal exactly when their block functions and tails are equal; they are nonconflicting exactly when every pair of corresponding blocks and the two tails are nonconflicting.

**Theorem 1.2 (A Zero Row Forces a Sibling of Excess Two).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.local_two_excess`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.local_two_excess` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, every slot j in Fin(k), and every original Strategy pi, cost(pi,F(k,a_j))=8k+16 implies that some sibling b in Y, H, Z has cost(pi,F(k,b_j)) at least 8k+18.

**Theorem 1.3 (Readout at a comb slot).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_slot_readout`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_slot_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The address consisting of j right steps, one left step, and u reads precisely u in slot j of an arbitrary right comb.

**Theorem 1.4 (Readout in the compensation subtree).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_tail_readout`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_tail_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After k right steps the remaining address reads the compensation subtree of a k-slot right comb.

**Theorem 1.5 (Six Local Tail Costs).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.local_tail_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.local_tail_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every selected slot, on the five rows baseline, A, Y, H, Z, six actual response recipes attain gains (1,1,0,1,1), (1,1,1,0,1), (1,1,1,1,0), (1,0,1,2,1), (1,0,2,1,1), and (1,0,1,1,2). Each recipe has an original globally correct Strategy with costs 8k+16 plus these gains on the five rows.

This module supplies the local obstruction and the six local tails. FourExitScanExtension extends the tails by scanning the other slots, and FourExitRawParetoSpectrum gives the full-family attainment and Pareto classification.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_foundation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_slot_readout`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.comb_tail_readout`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.local_tail_attainment`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.local_two_excess`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation](ActualImageSevenLeafSeparation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore](ActualJointResponseCostCore.md)
