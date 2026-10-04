# Four-Exit Raw Endpoint Spectrum

## Abstract

Four-exit trees, a zero-to-two raw-cost obstruction, and six local tail costs.

A right comb has k active slots and one compensation slot. Its baseline uses B in every active slot and R0 in the compensation slot. An exceptional member replaces one active block by A, Y, H, or Z and uses the corresponding compensation block.

The endpoint menu contains a vector with one zero and all other coordinates one for the baseline and each Y, H, or Z member. It also contains, for each slot, three vectors with zero at A, two at one of Y, H, or Z, and one elsewhere.

For every slot and every globally correct history-dependent controller, a cost of 8k + 16 on its A member forces a cost of at least 8k + 18 on one of its Y, H, or Z members. Restricting the actual response tree to these four members preserves the original controller's cost lower bound.

An A-leaf query is either common to the four members or gives two sibling members the same nonleaf reply. In the latter case, those two members must subsequently separate. Their shared leaf labels agree, so at least one receives another nonleaf reply before the response tree can reach singleton survivors.

On the five rows (baseline, A, Y, H, Z) at any selected slot, six finite actual response recipes attain the excess vectors (1,1,0,1,1), (1,1,1,0,1), (1,1,1,1,0), (1,0,1,2,1), (1,0,2,1,1), and (1,0,1,1,2). The response-cost core supplies a globally correct strategy for each recipe, with actual costs equal to 8k + 16 plus these coordinates.

These local recipes do not establish attainment on the entire family. The scan of other slots, its composition with each tail, global endpoint domination, and the full Pareto classification remain unproved.

## References

- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation](ActualImageSevenLeafSeparation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore](ActualJointResponseCostCore.md)
