---
slug: bajnok-2022-perfect-restricted-bases-conjecture-22-golay
bibkey: bajnok2022walkadditivecombinatorics
doi: 10.48550/arXiv.2211.01893
url: https://arxiv.org/abs/2211.01893v1
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.result
---

# A Golay quotient and the perfect restricted basis classification

## Problem

Bela Bajnok, *A Walk Through Some Newer Parts of Additive Combinatorics*,
arXiv:2211.01893v1, Section 3, Conjecture 22, PDF page 10, states:

> For integers $m \geq 2$ and $s \geq 2$, perfect restricted $s$-bases of size
> $m$ exist if, and only if, $G$ has order $2^m$ or is isomorphic to
> $\mathbb{Z}_{2^{s+1}-1}$, $\mathbb{Z}_2^{2s}$, or to
> $\mathbb{Z}^{2s-2} \times \mathbb{Z}_4$.

The ambient groups are finite abelian groups. The final family is literally
printed with integers. The companion paper intends the finite group
$\mathbb Z_2^{2s-2}\times\mathbb Z_4$. The same example excludes both.
The refutation uses the necessary direction at $s=3,m=23$, and does not
exploit the missing subscript or an omitted range in the existence direction.

| Source clause | Lean counterpart |
| --- | --- |
| Finite abelian $G$ | `G : Type`, `AddCommGroup G`, `Fintype G` |
| $m,s\ge2$ | Natural parameters with `2 ≤ m`, `2 ≤ s` |
| A basis of size $m$ | `∃ A : Finset G, A.card = m ∧ IsPerfectRestrictedBasis s A` |
| Unique sums of at most $s$ distinct elements | The original predicate from `BajnokBersonJustPerfectRestrictedBasis`, including the empty sum |
| Full equivalence | `claim` contains `↔`, not just the direction used in the proof |
| Order $2^m$ | `Nat.card G = 2 ^ m` |
| Cyclic family | `Nonempty (G ≃+ ZMod (2 ^ (s + 1) - 1))` |
| Binary family | `Nonempty (G ≃+ (Fin (2 * s) → ZMod 2))` |
| Literal last family | `ListedFamily G s m ℤ` uses `(Fin (2*s-2) → ℤ) × ZMod 4` |
| Intended last family | The same construction also disproves `ListedFamily GolayGroup 3 23 (ZMod 2)` |
| Finite-set equality | `DecidableEq G`, available classically for each group |
| Refutation | The closed `claim : Prop` and literal `result : Not claim` |

## Motivation

The independently posed companion Question 11 in Bajnok--Berson--Just,
*On Perfect Bases in Finite Abelian Groups*, DOI 10.2140/involve.2022.15.525,
arXiv:2211.13675v1, Section 4, asks:

> Are there any groups that have a perfect restricted $s$-basis of size $m$
> with $m \geq 2s + 2$?

The same $s=3,m=23$ construction answers this question affirmatively.
These are two consequences of one Golay quotient, not two independent
research constructions. The prior registration is
[#30733](https://github.com/the-omega-institute/trureturing/issues/30733).

## Gap

The existing Golay encoder supplies the actual code and its minimum weight.
The missing inference identifies correctable error supports with all bounded
subset sums in the additive quotient, and then with the source's basis predicate.

## Route

Puncture the existing binary extended Golay encoder at its parity coordinate.
The parity identity retains injectivity, giving a length-23 code with 4096
elements. Its nonzero words have weight at least seven. The quotient of
$\mathbb F_2^{23}$ by this code has order 2048. Two subsets of at most three
coordinate classes with the same sum give a codeword supported in their
union, of size at most six; the minimum weight forces equal subsets.
Singleton subsets show that the 23 coordinate classes are distinct.

There are exactly
$1+23+\binom{23}{2}+\binom{23}{3}=2048$ admissible subsets.
Injection and equality of finite cardinalities give surjection. Pulling an
arbitrary subset of the coordinate-class image back to its full coordinate
preimage proves uniqueness for every competing subset of the basis.

The proposed finite orders at these parameters are $2^{23}$, 15 and 64;
none is 2048. The printed integer-power final family is infinite, and its
intended binary version has order 64.

## Falsifier

Changing to exactly three summands, ordered tuples, only injectivity, a
conditional uninstantiated code, or a restricted family of competing subsets
would not answer the source problem. The actual finite group and the full
original predicate are required.

## Evidence

The exact settling declaration is
`D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.result`.
The abstract bridge is `BinaryCodePerfectRestrictedBasis.basis_of_minimum_weight`.
The Golay weight enumeration is reused from `GolayEncoder.minimum_weight`;
it is not repeated or replaced by a coding hypothesis.

The public helper four-slot audits are unfinished under
[#30740](https://github.com/the-omega-institute/trureturing/issues/30740).
No validated registration is claimed. The designated refutation result is exempt.

## Triage

The construction refutes the stated classification and answers the companion
Question 11 affirmatively. These are consequences of the same construction.
The formal result does not establish literature priority.

## ASSUMED-UNVERIFIED

A bounded literature search recorded in #30733 found no exact-context
settlement. Both official arXiv pages list v1. The complete Greene--Higgins
TeX does not discuss this Golay connection. The Hang Yu material named
without a title in the older Question 6 dossier remains unidentified, and
the forward-citation inventory is incomplete. These limits are
`ASSUMED-UNVERIFIED`; no worldwide novelty or mathematical-priority claim follows.
