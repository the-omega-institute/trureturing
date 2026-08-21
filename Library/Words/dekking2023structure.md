---
bibkey: dekking2023structure
authors: F. Michel Dekking
year: 2023
title: The structure of base phi expansions
doi: 10.48550/arXiv.2305.08349
claim: Occurrence sequences of negative-position digit prefixes in base-phi expansions are conjecturally Lucas-parameterized sequences drawn from three Sturmian families.
strata_touched:
  - D5/X_Frontier/BasePhiNegativePrefixTrident
  - D5/S1/Words/ZeckendorfOrder
  - D5/S1/Words/ZeckendorfBeattyBridge
  - D5/S1/Words/ReturnWords/GoldenReturnWords
  - D5/S1/Deficit/ZeckendorfDisplacementReading
license: citation-only
triage: anchor
---

# The structure of base phi expansions

Dekking studies the two-sided base-phi expansion `beta(N) = beta^+(N) . beta^-(N)`
and the sequences `R_{.w}` of natural numbers whose first `m` negative-position
digits equal a fixed word `w`. The paper introduces three families `V_F, V_G, V_H`
built from first-difference words of three Sturmian morphisms, and conjectures
that every such occurrence sequence is one of those families, or a union of three
of them, with Lucas-number parameters. It records that the obstruction is the
failure of `beta^-(N)` words to appear in lexicographic order, unlike the
positive side.

This note is the literature anchor for the problem candidate
`Problems/base-phi-negative-prefix-trident.md`.

The paper locates the phenomenon the formalization needs: Section 7.1 defines
the singleton/trident dichotomy of equal complete negative tails, and
Theorem 7.5 states the recursion the paper uses to prove it. The repository
formalization does **not** derive Theorem 7.5's recursion; it proves the
singleton/trident fiber shape directly with repo-native Beatty floor
coordinate arguments. The paper reference is provenance for the statement,
not for the proof route. On PDF page 16, Theorem 7.5 gives the
`gamma^-` recursion: its odd branches append `10`, `0010`, and `00` in
Equations (15a-c), while its even branches append `00`, `01`, and `01` in
Equations (16a-c). Section 7.1 defines equal complete negative tails as either
singletons or three consecutive inputs ("tridents"); Lemma 7.1 proves the
boundary trident splitting by induction from Theorem 3.3. Section 7.2 then
starts the conjectural classification of arbitrary finite negative prefixes,
which is strictly stronger and is not claimed by the present formalization.

The Lean proof takes only the cropped algebraic consequence needed by the
frontier: split a canonical expansion at exponent zero, identify its
nonnegative GoldenInt coordinate through the pinned Zeckendorf/Beatty bridge,
bound the nonempty negative tail on the two sides of `phi^-1`, classify the
corresponding floor fiber, and use the canonical seam digit to reduce the
upper-side two-coordinate fiber to a singleton. On the lower side, canonical
tail gluing realizes all three consecutive coordinates. This is equivalent to
the singleton/trident consequence of the recursive append structure; it does
not formalize the paper's full interval recursion or prefix-family panorama.

## Search log

- 2026-08-18: Queried the arXiv Atom API for `id_list=2305.08349`. HTTP 200 with
  `totalResults=1`; the entry resolved to `http://arxiv.org/abs/2305.08349v1`,
  title *The structure of base phi expansions*, sole author F. Michel Dekking,
  published 2023-05-15, primary category `math.NT`. The API reported no
  `arxiv:doi` and no `arxiv:journal_ref`, so the arXiv-assigned DOI is used.
- 2026-08-18: Issued `HEAD https://doi.org/10.48550/arXiv.2305.08349`, which
  returned HTTP 302 redirecting to `https://arxiv.org/abs/2305.08349`.
- 2026-08-22: Searched arXiv for `2305.08349`, fetched
  `https://arxiv.org/pdf/2305.08349v1`, and extracted the theorem text. The
  PDF fetch and arXiv API query both returned HTTP 200. Located Theorem 7.5 on
  PDF page 16, Lemma 7.1 on page 15, and the conjectural finite-prefix program
  at the start of Section 7.2 on page 20.

No literature search for a later resolution of the conjecture was performed; the
open status recorded in the problem candidate is the status stated in this
arXiv version, not an assessment of the subsequent literature.

## Verified locator

- arXiv: https://arxiv.org/abs/2305.08349
- DOI: https://doi.org/10.48550/arXiv.2305.08349
