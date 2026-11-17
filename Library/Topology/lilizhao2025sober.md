---
bibkey: lilizhao2025sober
authors: Xiangrui Li, Qingguo Li, Dongsheng Zhao
year: 2025
title: Sober topologies on a set
doi: null
url: https://arxiv.org/abs/2508.05419v1
claim: Example 3.9 constructs a decreasing sequence of Hausdorff prime-tail topologies on the nonnegative integers whose intersection is T1 and irreducible on the whole space, with no generic point for that whole space.
strata_touched: []
license: citation-only
triage: anchor
---

# Prime-tail topologies and their common opens

Example 3.9 uses the increasing sequence of primes and all residue classes
modulo primes in a tail as a subbasis. The Chinese remainder theorem,
stated immediately before the example, makes every finite prime-residue
cylinder nonempty. Cylinders with disjoint supports intersect.
A sufficiently large prime separates two distinct nonnegative integers,
so every tail topology is Hausdorff.

For two nonempty sets open in every tail, select a finite cylinder in the
first and then select a cylinder in the second from a tail beyond the first
support. Their supports are disjoint. CRT proves that the two opens meet,
so the whole space is irreducible. Singletons stay closed in the intersection
of the tail topologies. The infinite whole space cannot be the closure of
any singleton, proving failure even of quasi-sobriety.

The paper orders topologies by inclusion of open-set collections. Its meet
is their intersection. Mathlib uses the opposite order: its `iSup` has
exactly the sets open in every input topology, by `isOpen_iSup_iff`.
The paper's prime at positive index k corresponds to `primeSeq (k-1)`;
its tail at n+1 corresponds to `tailTopology n`. The cutoff one plus the
sum of a finite support used in Lean serves the same disjointness purpose
as one plus its maximum in the paper, and also handles empty supports.

`finiteCylinder_basis_of_generateOpen` and its open-set specialization
make the finite support, canonical residue bounds, point membership and
set containment explicit. This is a repository proof of the basis
extraction used in the example, with no originality claim. The source's
separate Remark 3.10 about the cofinite topology is outside this unit.

## Verified locator

https://arxiv.org/abs/2508.05419v1

Full text: https://arxiv.org/html/2508.05419v1, Example 3.9 and the
Chinese remainder statement immediately preceding it. The order convention
is specified in the introduction. This note cites and paraphrases the
source; it redistributes no article text or assets.
