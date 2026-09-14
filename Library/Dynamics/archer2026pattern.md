---
bibkey: archer2026pattern
authors: Kassie Archer, Noel Bourne
year: 2026
title: Pattern avoidance in compositions and powers of permutations
doi: 10.46298/dmtcs.17199
claim: Section 5 conjectures a counting equality for permutations avoiding 312 and 321 whose cubes avoid 2143 and compositions with at most one part outside 1 and 3.
strata_touched:
  - D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance
  - D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition
license: citation-only
triage: anchor
---

# Pattern avoidance in compositions and powers of permutations

This note anchors Lemma 3.1 and its resulting bijection, as well as the
unnumbered cube-counting conjecture in Section 5, "Further directions and
open questions", page 13 of arXiv:2505.05218v3. The following is the worker's
verbatim transcription of the conjecture, with line wrapping removed and
mathematical glyphs represented in inline LaTeX:

> For example, based on the ideas similar to the ones in this paper, we conjecture
> that the number of permutations that avoid the chain $(312,321 : \varnothing : 2143)$
> (i.e, those with the property that $\pi$ avoids $\{312,321\}$ and $\pi^3$
> avoids $2143$) is equal to the number of compositions $d = (d_1,d_2,\ldots,d_m)$
> of $n$ so that all $d_i$ are 1 or 3, except for at most one.

The surrounding request for other patterns and higher powers is outside this
anchor. In the same PDF, Section 3 defines `epsilon_1 = 1`, `epsilon_2 = 21`,
and `epsilon_d = 234...d1` for `d >= 3`. Lemma 3.1 on page 4 proves, for
`n >= 1`, that a permutation avoids 312 and 321 if and only if it is the
direct sum of these rotations for some composition of `n`. The first
paragraph on page 5 explicitly identifies the resulting bijection with
compositions. These are already-proved source results.

The frozen modules
`D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance`
and `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition`
formalize this route. The former proves the criterion for a specified list
of positive block sizes:
`rotationSumPerm_pow_avoids_2143_iff` allows at most one block size not
dividing the exponent, and `rotationSumPerm_cube_avoids_2143_iff` specializes
this to at most one part outside `{1,3}`. The latter formalizes Lemma 3.1 and
the bijection using the repository's generic pattern-containment predicate
and Mathlib compositions, then combines them with the cube criterion to prove
the counting equality. Lemma 3.1 and the bijection retain literature
provenance; the final counting theorem is repository-derived and carries the
problem's `Proved` resolution claim.

## Search log

- Caller-supplied reading, 2026-09-07: queried
  `https://export.arxiv.org/api/query?id_list=2505.05218`, HTTP 200,
  `totalResults=1`. The entry is arXiv:2505.05218v3 with the title and authors
  above, first published `2025-05-08T13:10:36Z`, updated
  `2026-05-13T12:55:31Z`, primary category `math.CO`. The API supplied
  `arxiv:doi` as `10.46298/dmtcs.17199` and `arxiv:journal_ref` as
  "Discrete Mathematics & Theoretical Computer Science, vol. 28:1,
  Permutation Patterns 2025, Special issues (May 19, 2026) dmtcs:17199".
  API response byte count was not supplied. The journal DOI is the bound
  identity; an arXiv DOI is not substituted for it.
- Caller-supplied reading, 2026-09-07:
  `HEAD https://doi.org/10.46298/dmtcs.17199` returned HTTP 302 to
  `https://dmtcs.episciences.org/17199`; no response byte count was supplied.
- Worker reading, 2026-09-07: fetched
  `https://arxiv.org/pdf/2505.05218v3` using `curl --location --fail`.
  HTTP 200, 374413 bytes, SHA-256
  `daec95fcbbf9b2c439b1a3680af97c01fe4912c1889fd312a0a8044ab6a497c9`.
  `pypdf.PdfReader` reported 15 pages. Extracted Section 5 and the sentence
  quoted above on printed/PDF page 13, Lemma 3.1 and its proof on page 4,
  and the explicit bijection statement on page 5. Also read the local Lean
  criterion statements and the frozen-state receipt. The API and DOI HEAD
  readings above were not repeated.

No literature search for a later resolution of the conjecture was performed.
This note records only that arXiv:2505.05218v3 presents the statement as a
conjecture; it does not assess the subsequent literature.

**ASSUMED-UNVERIFIED:** no repository machine verifies equivalence between the
paper's natural-language proposition and a Lean statement. The correspondence
of the paper's rotations and avoidance convention with the frozen criterion
is a reading comparison; the frozen counting theorem proves the corresponding
formal statement.

## Verified locator

- arXiv: https://arxiv.org/abs/2505.05218v3 (caller-supplied metadata).
- DOI: https://doi.org/10.46298/dmtcs.17199 (caller-supplied HTTP 302).
- Journal: https://dmtcs.episciences.org/17199 (caller-supplied redirect target).
- PDF: https://arxiv.org/pdf/2505.05218v3 (worker HTTP 200; Section 5, page 13;
  Lemma 3.1, page 4; bijection, page 5).
