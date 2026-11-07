# Original physical banks and the literal insertion

## Abstract

Original physical banks and the literal insertion

Assume 2<=b, 2<=d, b<a and d<a, and let m be a natural mask below 2^(a-1). The positive U,V,W,X chains start at 0,d,d+a,d+a+b and have lengths d-1,a-1,b-1,a-1. Their original terminal labels are d-1,d+a-1,d+a+b-1,a+b+a+d-1. A stock decodes set bits into these actual labels; its complement uses the full all-ones mask XOR the chosen mask. stock_split and canonical_inventory preserve distinct occurrences even when values coincide.

Let n=2^(a-b-1). The raw banks are U(full)++X(m), X(complement of m), W(full)++V(n), and V(complement of n). The early order uses these four banks and terminals k-1,d-1,d+a-1,d+a+b-1. The late order starts with raw banks 2,3,0,1 and terminals d+a-1,d+a+b-1,k-1,d-1. inventory proves that either word is a permutation of List.range k.

The cut is the length of the original prefix ending at terminal k-1. The fresh label k begins bank1 in the early order and bank3 in the late order. word_split, literal_ear and cut_bound identify the enlarged word with take j word ++ [k] ++ drop j word at a legal cut, including empty complementary banks.

raw_masses computes each bank sum in either shared row from the same bit mask. banks_good places every bank label in its positive chain. label_charge proves 2*oldValue-newValue>=0 at every original label, including all four terminals. These occurrence, mass and charge facts give the physical strip construction its exact source interpretation.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/Banks](../ThirdPeakPaidV/Banks.md)
