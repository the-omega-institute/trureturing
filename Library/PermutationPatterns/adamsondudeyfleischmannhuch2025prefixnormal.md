---
bibkey: adamsondudeyfleischmannhuch2025prefixnormal
authors: Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch
year: 2025
title: Word Chain Generators for Prefix Normal Words
doi: 10.1007/978-3-032-09524-4_5
url: https://arxiv.org/abs/2508.19619v1
claim: The v1 Conclusion asks whether every prefix normal generator is reachable from every other by swapping neighbouring entries; Lemma 17 supplies preservation when an adjacent ascent is exchanged.
strata_touched:
  - D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity
license: citation-only
triage: anchor
---

## Verified locator

The source used is https://arxiv.org/abs/2508.19619v1, submitted 27 August
2025, with PDF https://arxiv.org/pdf/2508.19619v1. Its authors are Duncan
Adamson, Moritz Dudey, Pamela Fleischmann and Annika Huch. The arXiv metadata
and license link identify the article license as CC BY-NC-ND 4.0
(https://creativecommons.org/licenses/by-nc-nd/4.0/). This note contains
bibliographic citation and mathematical exposition, not a copied article body.
PDF SHA-256: `5dd21ff6f2ee3a9cdc115118cd579d364f66433393f5c8f406d490258b967ae5`.

The later Springer chapter locator is DOI 10.1007/978-3-032-09524-4_5,
https://link.springer.com/chapter/10.1007/978-3-032-09524-4_5,
RP 2025, LNCS 16230, pp. 68–82. The publisher citation year is 2026;
the arXiv version cited here is 2025. The final chapter body is inaccessible
in the supplied source verification and has not been compared with v1.
Agreement of its definitions, lemmas, conclusion or answer status with v1 is
ASSUMED-UNVERIFIED.

## Read scope and question

The v1 title, Definitions 1–4 and 6, chain recurrence, adjacent-position
setup, complete Lemma 17 and Figure 5, the relevant Lemma 18 and Theorem 20
interfaces, and the complete Conclusion on pp. 17–18 were read. The
Conclusion asks: “Is there a path from any prefix normal generator to all
others, just by swapping neighbouring numbers?” Here neighbouring means
adjacent positions in the displayed permutation, without requiring consecutive
numerical values. Each vertex must have all n+1 prefix-normal chain states.
There is no shortest-path, direction, complexity or prescribed-sorting clause.

Lemma 17 is published supply for the ascent exchange, not a newly posed
question. Its proof is checked independently in the owning Lean module.
Lemma 18 and Theorem 20 give local descending-exchange criteria, not a global
path supplier. The global argument applies elementary insertion sorting to
valid ascent exchanges and reverses one of the two paths to a common endpoint.
This is one application to the v1 question; its sorting helper is not a
separate external result.

## Indexing and evidence limits

Source positions and values run from 1 to n. Lean positions and values run
from 0 to n−1; adding one to every value and position preserves the flip
order and adjacency. After t flips, Lean's undeleted set is range(n) minus
the first t entries, corresponding to source component t+1. For a prefix
of length q followed by entries a,b, the changed intermediate state has
Lean time q+1 and source component q+2. The Lemma 17 prose uses q+1 for
that component, whereas its recurrence and Figure 5 give q+2. The Lean
proof uses the recurrence consistently. Zero counts, empty factors and both
endpoint states are included despite the printed count-codomain and finite
component-quantifier defects in Definitions 1, 2 and 6.

The supplied bounded literature and source verification found no exact
whole-answer supplier in its searched scope. This does not certify exhaustive
absence, current open status, originality or worldwide priority. In particular,
the inaccessible final Springer body remains outside the verified scope.
The Library note and Stage A collection make no resolution, delivery or KPI
claim.
