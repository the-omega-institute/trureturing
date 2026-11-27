---
slug: rossi-2026-prefix-hamming-dimension
bibkey: rossi2026permutohedron
doi: 10.48550/arXiv.2611.25741
url: https://arxiv.org/abs/2611.25741v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.minimum_hamming_dimension
---

# Rossi’s minimum binary Hamming dimension

## Problem

Giovanni Rossi, *Beyond geometric lattices: pseudo-atoms and redundant join representations in the
face lattice of the permutohedron*, arXiv:2611.25741v1, §10.3 item 8, p. 26, asks:

> Embeddings in the hypercube. The distance δ on atoms is half the Hamming distance between the incidence vectors of the cut sets, so (Sₙ, δ) embeds isometrically, up to the factor 2, in a cube of dimension 2ⁿ − 2. What is the smallest dimension of such an embedding?

By the standing convention n ≥ 3. For each such n, take all permutations and the fixed scale
2δ, where δ counts unequal proper unordered prefixes by Definition 5.9. Theorem 5.10(1)
identifies 2δ with the cut-family symmetric-difference distance. Each target coordinate is
Boolean and contributes one to Hamming distance when it differs.
[Primary edition, p. 26](https://arxiv.org/pdf/2611.25741v1#page=26)

## Motivation

The incidence map uses one coordinate per nonempty proper subset. A minimum dimension must also
exclude arbitrary embeddings that share coordinates between ranks or use a different
representation of the same distances.

## Gap

The bounded prior-resolution search found no equivalent settled minimum at the stated scale.
The named related results address graph distances, split decompositions and single equilateral
codes. The search scope and index limits are recorded in the
[Library note](../Library/FiniteGeometry/rossi2026permutohedron.md).
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/32776)

## Route

Adjacent exchanges and paths realize every signed difference of prefix-incidence basis vectors
within a rank. Polarization transfers their pairings to sums of differences in any binary
realization. The integral squared-norm-two vectors at a rank have distinct pairwise intersecting
two-coordinate supports. A star uses one common coordinate and one distinct coordinate per
vector. A triangle fits three such supports into three coordinates. A shared coordinate between
ranks would violate their pairings or the distinctness of the supports, so the rank bounds add.

One-hot words attain the bound for every rank except those with four possible prefixes.
The four even-parity triples attain the bound for those ranks. At n = 4 the three rank
sizes are 4, 6 and 4, so the dimension is 3 + 6 + 3 = 12. For other n ≥ 3 the sum of the rank
sizes is 2ⁿ − 2. Extra zero coordinates give every feasible larger dimension.

## Falsifier

A map preserving all pairwise distances at dimension below the threshold would contradict the
lower bound. Failure to attain the threshold for any n ≥ 3 would contradict the upper bound.
Both tests use the same fixed scale and the complete permutation domain.

## Evidence

Rossi's Theorem 5.10(1) identifies twice the proper-rank mismatch count with the
cut-family symmetric-difference distance. Ordering the cuts by size recovers the prefix
chain and hence the permutation, so preserving this distance implies injectivity.

`D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.minimum_hamming_dimension`
proves the full equivalence between existence of the distance-preserving map and the dimension
bound for every n ≥ 3 and every d. Its axiom closure is `Classical.choice`, `Quot.sound`
and `propext`.

## Triage

`theorem`. The result answers the first-tier published question at its specified scale.

### What the settlement shows

**Proved** by `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.minimum_hamming_dimension`.

The signed-support argument gives the sharp lower bound even for embeddings whose coordinates
have no prescribed interpretation. The only saving over the incidence cube occurs at n = 4,
where each outer rank saves one coordinate. This sharpens the dimension assertion following
Theorem 5.10(1). The source's other atom-distance identities are unaffected.

**Questions beyond this settlement.** Minimum coordinate counts with arbitrary coordinate weights
or at other scales require separate statements. Section 10.3's extensions to other Coxeter types,
its other face-lattice questions and the q-analogue remain open here.

## ASSUMED-UNVERIFIED

Priority beyond the bounded literature and citation search is unverified. There is no claim
here about dimensions for alternative distances or weight conventions.
