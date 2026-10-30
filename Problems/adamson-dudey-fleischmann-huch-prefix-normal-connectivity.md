---
slug: adamson-dudey-fleischmann-huch-prefix-normal-connectivity
bibkey: adamsondudeyfleischmannhuch2025prefixnormal
doi: 10.1007/978-3-032-09524-4_5
url: https://arxiv.org/abs/2508.19619v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.result
---

# Connectivity of prefix normal generators

## Problem

Duncan Adamson, Moritz Dudey, Pamela Fleischmann and Annika Huch,
*Word Chain Generators for Prefix Normal Words*, arXiv:2508.19619v1,
Conclusion, pp. 17–18, ask:

> Is there a path from any prefix normal generator to all others, just by swapping neighbouring numbers?

The institutional 18-page accepted author manuscript (AAM) poses the same
question. For every positive n, the vertices are permutations of 1,...,n
whose complete flip-to-zero chains are prefix normal. Starting at the
all-one word, each entry names the position to flip. All n+1 states,
including both endpoints, must satisfy the comparison of every contiguous
factor with the prefix of the same length. A move exchanges entries at
adjacent positions; their distinct values can be arbitrary. Every
intermediate permutation must remain a valid generator. The requested
path is finite and may have zero moves. No shortest-path, direction or
complexity requirement is imposed.

## Motivation

The frozen declaration
`D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.result`
connects all pairs. Published Lemma 17 supplies ascent-exchange preservation;
the global argument applies it through actual contextual swaps to a common
descending normal form. This is an elementary constructive application to
the question in the two read manuscripts.

## Gap

The local preservation statement must yield a finite path with valid
intermediate vertices. The result quantifies over all natural n and both
endpoint lists, with precisely their direct flip-chain validity as
hypotheses. Each edge requires two valid endpoints and a common prefix
and suffix around the exchanged pair. The n=0 case is a proved repository
extension; all source positive-length cases remain included.

Lean positions and values are 0,...,n−1. Adding one gives the source
convention and preserves adjacency and flip order. After t flips, the
occupied set is range(n) minus the first t entries. Permutation membership
and take/drop disjointness identify it with the suffix set; this equality
is used at both endpoints and every transported edge.

The mathematical reading includes zero counts, empty factors, same-length
prefix/factor comparisons and all n+1 states, accounting for the source's
printed count-codomain, factor-comparison and finite-chain quantifier
defects. With a prefix of length q followed by a,b, the changed state is
Lean time q+1 and source component q+2, as given by the recurrence and
Figure 5. The q+1 component references in Lemma 17's prose do not override
that recurrence. The Library note retains the source and indexing limits.

## Route

Exchanging an adjacent ascent a<b changes only the state after the first
of the two flips. The deletion-count comparison proves prefix normality
of that state; every other occupied set is unchanged. Contextual induction
over insertion and then over the list constructs a finite valid path to
descending order. Sorted-permutation uniqueness identifies the two final
lists. Edge symmetry reverses the second path, and concatenation gives
the required all-pairs path.

## Falsifier

Two valid generators of the same positive length in different components
would refute the assertion. Omitting a factor, a chain state, a positive
length or an intermediate validity condition would fail correspondence.
An earlier exact whole-answer supplier would change the literature account
without changing the kernel-checked mathematical statement.

## Evidence

The Library note identifies the read v1 source material and PDF SHA-256
`5dd21ff6f2ee3a9cdc115118cd579d364f66433393f5c8f406d490258b967ae5`.
The AAM is institutionally identified at
<https://research-repository.st-andrews.ac.uk/handle/10023/33532>.
Its full 18-page extracted text was independently read; its PDF SHA-256 is
`b46bc44a3b2103eed027ebf25446c632aade08e31124aa33370b0afbb11f6a2f`.
This scope excludes page-image inspection and independent verification of
the source proofs. The institution attests CC BY for the AAM; arXiv v1 is
CC BY-NC-ND 4.0. The repository retains citation and mathematical exposition
only, not either article body.

The Library note's bounded literature scope identified no exact whole-answer
supplier. Published local ascent preservation is supply; the elementary
constructive path is the retained global application. The Lean theorem uses
Classical.choice, Quot.sound and propext.

## Triage

`theorem` classifies the unbounded structural question. The decisive
mechanism is a common valid descending normal form reached by actual
contextual adjacent swaps. The proof extends to n=0. No complexity bound,
shortest-path theorem or prescribed directed all-pairs result is supplied.

The source-qualified consequence is an affirmative connectivity answer for
arXiv v1 and the institutional AAM. The source's other Conclusion questions
remain unaddressed here. Counting, efficient enumeration, shortest paths
and directed variants require separate statements and proofs; this result
claims no settlement of those neighbouring questions.

## ASSUMED-UNVERIFIED

The final Springer body, DOI 10.1007/978-3-032-09524-4_5, LNCS 16230,
pp. 68–82, has 15 pages and publisher citation year 2026. It has not been
read. Agreement of its definitions, indexing, Conclusion and answer status
with the read manuscripts remains ASSUMED-UNVERIFIED. Bounded literature
non-detection establishes no worldwide openness, exhaustive absence or
priority. No new deep breakthrough is claimed.
