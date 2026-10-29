---
bibkey: gangloff2019dominating
authors: Silvere Gangloff; Alexandre Talon
year: 2019
title: "Asymptotic growth rate of square grids dominating sets: a symbolic dynamics approach"
doi: 10.48550/arXiv.1906.10779
url: https://arxiv.org/abs/1906.10779
claim: "Proposition 1 characterizes a dominating set as inclusion-minimal exactly when each selected vertex is isolated within the set or has an outside private neighbour."
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.1906.10779

Source: https://arxiv.org/abs/1906.10779

The locator and page references use arXiv:1906.10779v2, Definitions 2, 4 and 5
and Proposition 1, pp. 2–3. The arXiv version listing contains v1 and v2.
The journal publication has DOI 10.1016/j.tcs.2020.03.006; its full text is not
used as a checked substitute for v2.

## Characterization and correspondence

The domination premise is essential. For a dominating set, every selected
vertex must either have no selected neighbour or possess an outside neighbour
whose unique selected neighbour is that vertex. A closed private witness combines
these alternatives: an isolated selected vertex witnesses itself, while an
outside private neighbour supplies the other alternative.
`BarkerMinimalGridEncoding.minimal_iff_closed_private` expresses this
characterization for finite simple graphs and finite vertex subsets. Witness
existence is propositional and contributes no counting multiplicity.

The paper also gives symbolic-dynamics and fixed-width recoding background.
Those passages do not establish the complete OEIS A286848 numerator, denominator
or all-width actual-subset identity.

## License

The arXiv record uses the nonexclusive distribution license. This note cites
and paraphrases the mathematical result; it copies no proof code and infers no
permissive code or prose-copy license from arXiv availability.
