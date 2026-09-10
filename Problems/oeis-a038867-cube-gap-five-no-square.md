---
slug: oeis-a038867-cube-gap-five-no-square
bibkey: oeis2026a038867
doi: null
url: https://oeis.org/A038867
triage: theorem
motivation_gids:
  - D5/S3/Factorization/CubeGapFiveNoSquare
---

# The A038867 no-square conjecture

## Problem

Take the difference between two cubes whose bases are five apart. Klaus
Purath conjectured on May 15, 2026 that no such difference is a perfect
square, noting verification through one hundred thousand indices.

## Motivation

This is a first-tier recent OEIS conjecture. Direct inspection on September 9,
2026 found the statement still labelled Conjecture, with the page carrying
only the polynomial expansion and the numerical verification.

## Gap

The searched public indexes returned no proof. The polynomial expansion
already on the page names the terms but says nothing about squares; the
residue argument that settles it is not stated there or in the sole
cross-referenced entry.

## Route

The difference expands to five times a quadratic whose constant term is
twenty-five and whose other terms carry a factor of three. So the whole
expression is two modulo three, for every index. A square is zero or one
modulo three, never two, so the two residue sets are disjoint and no term can
be a square.

Subtraction of naturals truncates, so the module states the expanded form as
the definition and recovers the difference of cubes separately, where the
identity shows the subtraction is not truncating.

## Falsifier

An index whose cube difference at gap five is a perfect square would
contradict the theorem about the defined quantity.

## Evidence

- Module: `D5/S3/Factorization/CubeGapFiveNoSquare.lean`.
- Main theorems: `cube_gap_five_ne_sq` and `cube_gap_five_ne_sq_sub`, the second
  in the source's own subtraction form.
- Supporting results: `gap_eq_cube_sub`, `gap_mod_three`,
  `sq_mod_three_ne_two`.
- All four public results depend only on propositional extensionality and
  quotient soundness; no choice principle is used.
- There is no finite cutoff in any public statement.

The caller verified before implementing. The polynomial identity held for
every index below two hundred with no mismatch. The residues of the
difference formed the single-element set containing two, over five hundred
indices. The residues of squares formed the set containing zero and one, over
five hundred candidates. The two sets are disjoint. A direct search over three
hundred thousand indices found no square.

## Triage

`theorem`. The statement is proved for every index. Nothing is asserted about
cube differences at other gaps, where the residue argument does not apply.

## ASSUMED-UNVERIFIED

First-publication priority is not established. The searches do not exclude
private or unindexed proofs. The identification with the OEIS entry is
documentary; the kernel verifies the explicitly defined quantity.
