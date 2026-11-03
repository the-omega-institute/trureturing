# Exact paired row bounds and finite row type

## Abstract

Exact paired row bounds and finite row type

FixedRow stores natural x,p,q,h,v,m,M and the actual Bool before. rowBounds is an integer proposition. For each of the first three endpoints it requires the old endpoint in [0,old head-1] and the enlarged endpoint in [0,new head-1]. It also requires 1<=v, 2v<=t, 0<=M and 2M<=y-2.

This module contains only the shared row type and predicate. The small-p tables are defined in SmallTables. The selector therefore returns original simultaneous old and new constraints with their stocks.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits](LowBits.md)
