---
slug: archer-bourne-cube-2143-count
bibkey: archer2026pattern
doi: 10.46298/dmtcs.17199
triage: window
motivation_gids:
  - D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance
  - D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition
---

# Archer-Bourne cube-avoidance counting equality

## Problem

This dossier deliberately anchors only the unnumbered counting conjecture
in Section 5, "Further directions and open questions", page 13 of
arXiv:2505.05218v3. The worker extracted this sentence from the PDF; line
wrapping is removed and mathematical glyphs are transcribed into inline LaTeX:

> For example, based on the ideas similar to the ones in this paper, we conjecture
> that the number of permutations that avoid the chain $(312,321 : \varnothing : 2143)$
> (i.e, those with the property that $\pi$ avoids $\{312,321\}$ and $\pi^3$
> avoids $2143$) is equal to the number of compositions $d = (d_1,d_2,\ldots,d_m)$
> of $n$ so that all $d_i$ are 1 or 3, except for at most one.

Thus, for each positive `n`, count permutations of `n` avoiding 312 and 321
whose cubes avoid 2143, and compare with ordered compositions of `n` having
at most one part outside `{1,3}`. The paper's broader questions about other
patterns and higher powers are deliberately out of scope.

## Motivation

The frozen motivation module supplies an exact avoidance criterion for
powers of direct sums of cyclic rotations. Its cube specialization provides
the composition-side condition in the quoted conjecture. This is a concrete
formal input to the counting bridge.

## Gap

The formalization route is complete. Candidate theorem 6.222 supplies the
decomposition, uniqueness of the indexing composition, and the restricted
cardinality bijection needed to combine the earlier cube criterion with the
published source results.

## Route

The frozen half is `rotationSumPerm_pow_avoids_2143_iff`: for positive block
sizes, the `r`th power of `pi_d` avoids 2143 exactly when at most one block
size fails to divide `r`. Its frozen cube specialization,
`rotationSumPerm_cube_avoids_2143_iff`, makes the exceptional sizes precisely
those outside `{1,3}`.

The completed formal half is the decomposition of every 312/321-avoiding
permutation as a direct sum of cyclic rotations, its bijectivity with
compositions of `n`, and the restriction of that bijection to transport
cardinalities using the cube criterion. Archer and Bourne already prove the
decomposition in Lemma 3.1 on page 4 and identify the bijection on page 5;
this part is formalization of a published result, not new
mathematics. The worker read both passages in the fetched PDF.

`card_avoids_312_321_cube_2143_eq_compositions` combines the formalized
bijection with the frozen criterion and proves the conjectured equality. Its
Scribe declaration carries this problem's `Proved` resolution claim. The
decomposition and bijection retain literature provenance, while this final
counting theorem is repository-derived.

## Falsifier

A positive `n` with unequal exact counts on the two sides would refute the
anchored conjecture. To validate a proposed enumeration, it must range over
all permutations and all compositions of that `n` using the paper's
avoidance and composition conventions. No new enumeration was performed
here. A formal bridge must preserve total size and prove both directions
and uniqueness; the criterion for an already-given `pi_d` alone cannot
certify those properties.

## Evidence

- Frozen module:
  `D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance.lean`.
- Public criterion theorems: `rotationSumPerm_pow_avoids_2143_iff` and
  `rotationSumPerm_cube_avoids_2143_iff`.
- Frozen bridge module:
  `D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition.lean`.
- Public bridge and counting theorems:
  `avoids_312_321_iff_exists_rotationSumComposition`,
  `rotationSumComposition_injective`, and
  `card_avoids_312_321_cube_2143_eq_compositions`.
- Machine-checkable frozen-state receipt:
  `Golden/Frozen/state/D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance.lean.json`.
  The worker's `test -f` exited 0 on 2026-09-07.
- `Library/Dynamics/archer2026pattern.md` records the worker's PDF fetch:
  HTTP 200, 374413 bytes, SHA-256
  `daec95fcbbf9b2c439b1a3680af97c01fe4912c1889fd312a0a8044ab6a497c9`.
  The conjecture is on page 13; the published decomposition and bijection
  are on pages 4 and 5. Candidate 6.221 records the criterion, while 6.222
  records the completed repository bridge; these numbers are provenance.

## Triage

`window`. The repository route is complete: the decomposition and injectivity
formalize the paper's source results, and the final restricted cardinality
bijection proves the anchored counting proposition. The final theorem carries
the problem's `Proved` resolution claim.

## ASSUMED-UNVERIFIED

- No repository machine verifies that a Lean statement is equivalent to the
  paper's natural-language proposition. This worker's comparison of the
  extracted source with the Lean criterion, including rotations and
  avoidance conventions, is human reading evidence, not a proof of
  source-to-Lean equivalence.
- The decomposition and bijection are source results formalized in the
  repository. Their identification with the paper's prose remains a reading
  comparison rather than a machine-verified translation.
- The API metadata and journal DOI redirect are caller-supplied readings
  dated 2026-09-07. The worker independently fetched and extracted the v3
  PDF, but did not repeat those metadata requests.
- No literature search for a later resolution of the conjecture was performed.
  This dossier records only that arXiv:2505.05218v3 presents the statement as
  a conjecture; it does not assess the subsequent literature.
