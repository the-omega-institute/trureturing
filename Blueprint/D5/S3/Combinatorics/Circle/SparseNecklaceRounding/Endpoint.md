# Uniform physical sparse-necklace rounding

## Abstract

Uniform physical sparse-necklace rounding

**Theorem 1.1 (Uniform p minus one physical rounding theorem).**

Lean statement: `D5/S3/Combinatorics/Circle/SparseNecklaceRounding/Endpoint.uniform_sparse_necklace_rounding`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/SparseNecklaceRounding/Endpoint.uniform_sparse_necklace_rounding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural p>=1 and every gaps:Fin(p)->Nat with gaps(j)>=2, the complete PhysicalRounding conclusion holds. This includes p=1, nonprimitive necklaces, repeated gaps and repeated coordinate values. No fractional feasibility, arithmetic certificate or further hypothesis is assumed.

Put k=sum gaps, e=sum_j 2^(sum_{q<j} gaps(q)), N=2^k-1 and H=N/2. The old coordinates are actualSource(k,e); new coordinates are actualSource(k+1,2e). There are two permutations of Fin(k), each giving a literal fresh-first permutation of Fin(k+1), with the fresh label k valued e. The old and new totals are separately zero for both words. For every natural prefix q, plus old/new sums are nonnegative and minus old/new sums are at most H,N, including q=0 and saturated prefixes.

A list of at most p-1 records has distinct prefix lengths and disjoint positive-terminal physical labels, strict native threshold crossings and the exact adjacent positions in both words. Folding the specified literal swaps gives the minus word. Every plus upper-bound failure and every minus lower-bound failure occurs at one recorded position; both error sets over Fin(k+2) have cardinality at most the record count.

The proof identifies every physical positive and terminal label, and proves that their disjoint streams exhaust Fin(k). Native chain masses telescope to the terminal demands, and chain charges telescope to the necklace seed. Threshold separation prevents a positive interval from crossing two successive demands; the final demand is the total positive mass and therefore cannot be a strict split. There are at most p-1 strict splits.

For fractional positive mass x and current next terminal r, put F=x-D(r+1) and Y=e+2F-C, where C is the consumed charge including later terminals. The proof establishes 0<=C<=e. Below the chain boundary x<=D(r+1)+e-h(r+1), the sparse head bound gives Y<=N. Above that boundary, completed later chains force C>=e-z(r+1), and the native margin 2n(r)+z(r+1)<=N gives the same upper bound. This proves every fractional vertex lies in [0,H] times [0,N] from the original gap assumptions.

The simultaneous rounding theorem is then applied to this proved fractional path. Integer-to-rational transport and the literal fresh-first ear word give both separate zero totals and every natural physical prefix bound, including zero and saturated prefixes. Strict cuts give distinct disjoint positive-terminal adjacent swaps and both bad-prefix counts are at most p-1. This is the sparse-necklace rounding theorem; it makes no claim to resolve the remaining full four-gap J problem.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/SparseNecklaceRounding/Endpoint.uniform_sparse_necklace_rounding`
- Dependency: [D5/S3/Combinatorics/Circle/SparseNecklaceRounding/PhysicalStreams](PhysicalStreams.md)
