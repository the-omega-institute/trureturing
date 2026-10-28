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

The cited preprint is https://arxiv.org/abs/2508.19619v1, submitted 27 August
2025, with PDF https://arxiv.org/pdf/2508.19619v1. Its authors are Duncan
Adamson, Moritz Dudey, Pamela Fleischmann and Annika Huch. The arXiv metadata
and license link identify the preprint license as CC BY-NC-ND 4.0
(https://creativecommons.org/licenses/by-nc-nd/4.0/).
PDF SHA-256: `5dd21ff6f2ee3a9cdc115118cd579d364f66433393f5c8f406d490258b967ae5`.

An institutional accepted author manuscript (AAM) is available from the
University of St Andrews repository:
https://research-repository.st-andrews.ac.uk/handle/10023/33532,
with full metadata at
https://research-repository.st-andrews.ac.uk/handle/10023/33532?show=full
and PDF at
https://research-repository.st-andrews.ac.uk/bitstream/handle/10023/33532/main.pdf?sequence=1&isAllowed=y.
The repository rights statement identifies an accepted manuscript under CC BY;
the institutional portal,
https://research-portal.st-andrews.ac.uk/en/publications/word-chain-generators-forprefix-normal-words/,
labels it Accepted author manuscript. Both records identify the same four
authors, DOI, LNCS volume and page range. The downloaded AAM has 18 pages,
594,669 bytes and SHA-256
`b46bc44a3b2103eed027ebf25446c632aade08e31124aa33370b0afbb11f6a2f`.
It prints no version number and is byte-distinct from arXiv v1. This note
retains citation and mathematical exposition only, not either article body;
its citation-only classification is distinct from the licences of the two
source manuscripts.

The Springer chapter locator is DOI 10.1007/978-3-032-09524-4_5,
https://link.springer.com/chapter/10.1007/978-3-032-09524-4_5,
Reachability Problems, RP 2025, LNCS 16230, pp. 68–82. The publisher
print/citation year is 2026, while the institutional citation year is 2025.
Crossref records first online publication on 5 November 2025; the institution
records publication on 6 November 2025. The 15-page published chapter and
18-page AAM are distinct version scopes. The final publisher body has not
been acquired or read. Agreement of its definitions, lemmas, indexing,
Conclusion or answer status with either read manuscript is ASSUMED-UNVERIFIED.

## Read scope and question

The v1 title, Definitions 1–4 and 6, chain recurrence, adjacent-position
setup, complete Lemma 17 and Figure 5, the relevant Lemma 18 and Theorem 20
interfaces, and the complete Conclusion on pp. 17–18 were read. All extracted
text from all 18 AAM pages was read, including statements, proofs, figures as
text, Conclusion and References; this scope excludes page-image inspection
and independent verification of the paper's proofs. Direct whole-document
text comparison found differences in citation placeholders, the arXiv margin
stamp and line wrapping or hyphenation. Definitions 1, 3 and 6 and the
adjacent-position setup with Lemma 17 have identical extracted text. The
Conclusions agree after citation-marker replacement and whitespace removal.
These comparisons establish neither PDF byte equality nor publisher-body
identity.

Both manuscripts explicitly ask in the Conclusion on pp. 17–18: “Is there a
path from any prefix normal generator to all others, just by swapping
neighbouring numbers?” Here neighbouring means adjacent positions in the
displayed permutation, without requiring consecutive numerical values. Each
vertex must have all n+1 prefix-normal chain states. There is no shortest-path,
direction, complexity or prescribed-sorting clause.

Lemma 17 supplies preservation when an adjacent ascent is exchanged. Lemma 18
and Theorem 20 state local descending-exchange criteria. No explicit global
all-pairs connectivity theorem or complete global path construction was
identified in the read AAM; this does not assert that its local results cannot
imply an answer. The bounded literature and source verification identified no
exact whole-answer supplier in its examined source bodies and search scope.
This is bounded non-detection, not evidence of exhaustive absence, worldwide
current openness, originality or priority. The source-qualified correspondence
is to the question explicitly posed in arXiv v1 and the institutional AAM;
the unread final chapter remains outside that qualification.

The owning Lean module independently proves ascent-exchange preservation.
Its global argument applies elementary insertion sorting to valid ascent
exchanges and reverses one of the two paths to a common endpoint. This is one
application to the question in the two read manuscripts; its sorting helper
is not a separate external result.

## Indexing and evidence limits

Source positions and values run from 1 to n. Lean positions and values run
from 0 to n−1; adding one to every value and position preserves the flip
order and adjacency. After t flips, Lean's undeleted set is range(n) minus
the first t entries, corresponding to source component t+1. For a prefix
of length q followed by entries a,b, the changed intermediate state has
Lean time q+1 and source component q+2. In both read manuscripts, the Lemma 17
prose uses q+1 for that component, whereas its recurrence and Figure 5 give
q+2. The Lean proof uses the recurrence consistently. Zero counts, empty
factors and both endpoint states are included despite the printed
count-codomain and finite component-quantifier defects in Definitions 1, 2
and 6, which remain unchanged in the AAM. The source uses positive word
lengths; no empty-length claim is attributed to either manuscript.
