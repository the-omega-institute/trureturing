# SingletonCore

## Abstract

Auxiliary cut structure for full mutual-visibility reconfiguration.

All pairs of a connected host are feasible. If two surviving singleton configurations were separated by a cut smaller than the number of host labels, the empty configuration and their pair would be cut. Every other label pays an additional cut in its own local class: either its singleton, or a pair joining it to one of the two endpoints. These disjoint classes contradict the cut size. The empty configuration has precisely one neighbor per host label, so minimum degree is at most host order. These are auxiliary reductions, not a proof of the full maximal-connectivity claim.

## References

- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments](PairPayments.md)
