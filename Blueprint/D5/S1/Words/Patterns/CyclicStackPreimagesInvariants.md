# Cyclic-Stack Gap Invariants

## Abstract

Successful inputs have at most one low per high gap, ordered lows, and constrained high entries.

A gapped word starts with a high entry and places at most one low entry after each high entry. Its high filter, low filter, and optional gap slots reconstruct the original word exactly.

Any permutation whose cyclic-stack output is the layered target is gapped. Its low entries occur in increasing order; permutation preservation therefore identifies the low filter with its consecutive range. The high filter contains the complementary range as a permutation, and equals that range once its increasing order is established. When every gap except possibly the final gap is filled, successful execution forces the highs to increase.

## References

- Dependency: [D5/S1/Words/Patterns/CyclicStackPreimagesCandidates](CyclicStackPreimagesCandidates.md)
