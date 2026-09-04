---
bibkey: wang2026port
authors: Han Wang
year: 2026
title: Port Fillings for Primary Pseudoperfect Numbers
doi: 10.48550/arXiv.2605.21518
claim: Lemma 6.2 states both orientations of the port-composition law for coprime squarefree integers.
strata_touched:
  - D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition
license: citation-only
triage: anchor
---

# Port Fillings for Primary Pseudoperfect Numbers

Han Wang introduces the port residual
`Delta_(R,c)(B) = cB - R partial(B)` for squarefree positive integers and uses
it to organize extensions of primary pseudoperfect numbers. Lemma 6.2 states
that for coprime squarefree integers `A` and `B`,
`Delta_(R,c)(AB) = Delta_(RA,Delta_(R,c)(A))(B)`, together with the symmetric
formula obtained by interchanging `A` and `B`.

The repository theorem
`D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.portDelta_mul` is not
classified as literature-attested verbatim. It works over natural numbers,
drops Wang's squarefreeness hypotheses, and records one orientation. The note
therefore supplies contextual credit through `repo-derived` provenance rather
than claiming an exact literature statement.

## Search log

- 2026-09-05: Queried the arXiv Atom API for `id_list=2605.21518`. HTTP 200
  returned exactly one entry, `http://arxiv.org/abs/2605.21518v1`, titled
  *Port Fillings for Primary Pseudoperfect Numbers*, authored by Han Wang,
  published 2026-05-18 in `math.NT`.
- 2026-09-05: Downloaded arXiv PDF version 1 and read Definition 6.1 and Lemma
  6.2. The lemma states both composition orientations and explicitly assumes
  that `A` and `B` are coprime squarefree integers.
- 2026-09-05: Issued `HEAD` for
  `https://doi.org/10.48550/arXiv.2605.21518`; it returned HTTP 302 to the
  arXiv abstract, followed by HTTP 200.

## Verified locator

- arXiv: https://arxiv.org/abs/2605.21518
- DOI: https://doi.org/10.48550/arXiv.2605.21518
