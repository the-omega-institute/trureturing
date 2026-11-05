# Every occurrence, including empty stocks

## Abstract

Original binary supports and exact cuts

Write alpha=d-a, beta=b-d and gamma=c-b. Physical U positives are [0,d-1), V positives [d,d+c-1), W positives [d+c,d+c+b-1) and X positives [d+c+b,k-1), where k=a+b+c+d. Their four terminal labels are d-1,d+c-1,d+c+b-1,k-1. All intervals are half open. Each local bit index is shifted into its original chain, with no cyclic symmetry or surrogate mass.

For I with beta>=2, h has local W bits [0,beta-2) and {beta-1}. If alpha=0, p=h, bank2 has no W bits, and the W complement is {beta-2} followed by [beta,b-1). If alpha>=1, p is the all-ones mask [0,alpha+beta-1); bank2 has {beta-2} followed by [beta,alpha+beta-1), and bank1 has [alpha+beta-1,b-1). Thus popcount(h)=beta-1 and popcount(p XOR h)=alpha. The reserve scalar h=3s/4-1 follows from these very bits.

For II, bank1 W bits are [alpha,b-1), bank2 W bits [1,alpha), and bank3 W bit {0}. They encode r-1, r-2 and 1 as disjoint subsets. In both adjacent branches, bank2 V bit is {gamma-1} with mask q/2 and bank3 V bits are [0,gamma-1) with mask q/2-1. The latter is empty at q=2; the former W stock is empty at r=2. In III, bank1 W bits are [1,b-1), bank2 W is empty, and W bit 0 is retained to the final bank.

MaskOf is the natural sum of distinct dyadic powers. Finset.geomSum_injective identifies the actual native bitIndices with each explicit list support. The full interval permutations prove mask fit, pairwise disjointness, union equal to the full stock, and genuine popcount equal to list length. No assumed feasibility certificate enters the endpoint.

Original bank lengths including terminals are (b,a+1,d,c-1) in I and II and (b,a,a+1,c-1) in III. The exact cut is a+b+1 in I and II, immediately after nW; in III it is b, immediately after nV. The remaining suffix is nonempty, so each cut is strictly less than k. The before/after decomposition proves literal take/drop insertion.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakIntermediateTail/Arithmetic](Arithmetic.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/Banks](../ThirdPeakPaidV/Banks.md)
