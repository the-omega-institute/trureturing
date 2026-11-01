# A mask, its xor complement, and the low block

## Abstract

Native shifted supports and physical label partitions

For natural c,s,H with H<=2^c-1, let lambda=2^s, m=(2^c-1)lambda, h=lambdaH, q=m XOR h and low=lambda-1. The internal partition result proves q+h=m and a partition of the bit indices 0 through c+s-1 by h, q and low. Each mask is less than 2^(c+s), their supports are pairwise disjoint, and their union is the full range.

The support argument first proves that multiplying a natural number by 2^s sends each bit index i to s+i, using uniqueness of sums of distinct powers of two. The support of 2^c-1 is the entire c-bit range, so h is a submask of the shifted high block m. Xor supplies its actual complementary support there. The low s-bit block is disjoint from that high block; it is not an interchangeable numerical charge.

The module then transports bit-support disjointness through chamberLabels to disjoint lists of physical occurrences. Under the partition hypotheses, concatenating the three decoded lists is a permutation of the complete interval starting at the chosen offset. Source consumes this physical partition for the W-positive labels, with c+s=b-1. All results here are private implementation components of the Endpoint construction.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Masks](../MaxPlusTwo/Chambers/Masks.md)
