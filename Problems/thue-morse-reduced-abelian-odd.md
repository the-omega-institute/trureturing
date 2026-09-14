---
slug: thue-morse-reduced-abelian-odd
bibkey: campbell2025reduced
doi: 10.48550/arXiv.2509.16034
triage: theorem
motivation_gids:
  - D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
---

# Odd-index reduced abelian complexity of the Thue-Morse word

## Problem

This dossier deliberately anchors only the equality
`rho^{ab,red}_t(2n+1) = rho^{ab,red}_t(n+1)` for every nonnegative integer
`n`, proposed in Section 3 (Conclusion), page 15 of arXiv:2509.16034v1 and
printed page 14 of the verified journal version. The shared Library note
records the journal citation. The source sentence is:

> Although it appears that rho^{ab,red}_t(2n+1) = rho^{ab,red}_t(n+1) for
> nonnegative integers n, the problem of determining a full recursion for
> rho^{ab,red}_t(n) seems to be challenging.

`red(w)` collapses every maximal constant run; reduced abelian complexity
counts all length-`n` factors up to rearrangement of their reduced words
with equal reduced length. The full recursion and four further questions
in the source paragraph, namely the nonzero sign of `rho(4n+2)-rho(4n)`, a
recursion for `rho(4n)`, equation (11), and non-k-automaticity of sequence
(10), are deliberately out of scope.

## Motivation

The frozen motivation module defines factors at every natural start and
counts their reduced Parikh vectors. It provides the exact odd recurrence
needed for this external proposition, making the all-start interpretation
explicit rather than depending on a finite sampled prefix.

## Gap

The paper does not prove this odd equality. Its formal counterpart is
already frozen; the missing item addressed here is
the literature-backed pool entry. No assertion about a full recursion or
any of the other four source questions follows from this dossier's odd
recurrence anchor.

## Route

Use `reducedAbelianComplexity_odd (n : Nat)`. The formal `thueMorse` is
zero-indexed binary digit parity; `factor length start` ranges over every
natural `start`, `runCompress` uses `List.destutter`, and `R length` counts
the resulting reduced Parikh classes. Equal Parikh vectors force equal
reduced length and identical character multiplicities, matching the paper's
equivalence relation according to the caller's reading.

The frozen proof transfers a bijection on reduced class codes back to these
all-start Parikh classes. No prefix-only count is substituted. The
`R (2^k+1) = 3` corollary is supporting evidence only; the sole problem
anchor remains the odd recurrence. Claim binding is a later Scribe layer.

## Falsifier

A nonnegative `n` for which the two exact all-start reduced complexity
counts differ would refute the proposition. A discrepancy in a finite
sample of starting positions is insufficient without a proof that the
sample exhausts every reduced class at both lengths. No fresh numerical
search or exhaustive factor computation was performed here.

## Evidence

- Frozen module: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.lean`.
- Public theorem: `reducedAbelianComplexity_odd`, stating
  `R (2*n+1) = R (n+1)` for every natural `n`.
- Companion public theorem: `reducedAbelianComplexity_two_pow_add_one`,
  stating `R (2^k+1) = 3`; it is not another anchored open problem.
- Machine-checkable frozen-state receipt:
  `Golden/Frozen/state/D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.lean.json`.
- Literature reading and locators: `Library/Words/campbell2025reduced.md`.
  Theory candidates 6.223 and 6.224 supply provenance context only.
- The journal venue, February 20, 2026 publication date and printed DOI
  `10.5281/zenodo.18714474` are verified from the journal PDF, as documented
  in the Library note. The front matter retains the original arXiv DOI and
  bibkey; journal publication is not an arXiv v2.

## Triage

`theorem`. The exact odd recurrence for the all-start definition has a frozen
kernel-verified proof, subject to the source correspondence limitation below.
This classification neither covers the paper's other questions nor binds a
resolution claim.

For the related question about sequence (10), the shared Library note and
the `ThueMorseReducedAbelianEven` Scribe mirror give an expository consequence
of the existing extrema recurrences and weighted interval count: `R` is
unbounded on positive lengths and therefore non-k-automatic in every integer
base `k >= 2`. This is compatible with `R(2^k+1) = 3`; unboundedness does not
mean convergence to infinity. No separately kernel-checked nonautomaticity
endpoint or typed resolution claim is supplied, and the sole anchor of this
dossier remains the odd recurrence.

## ASSUMED-UNVERIFIED

- No repository machine verifies that the Lean statement is equivalent to the
  paper's natural-language proposition. The comparison of the all-start
  definitions is a reading of the source, not a machine proof of equivalence
  between the source text and Lean.
- First-publication priority for the odd recurrence is not established.
  The source's unproved wording describes that publication. The Library
  note's targeted later-literature search concerns nonautomaticity and is
  limited to the searched scope, not a worldwide absence certification.
