---
bibkey: morsehedlund1940symbolic
authors: Marston Morse and Gustav A. Hedlund
year: 1940
title: Symbolic Dynamics II. Sturmian Trajectories
doi: 10.2307/2371431
claim: A one-sided infinite word with at most n factors of some length n is eventually periodic.
strata_touched:
  - D5/S1/Words/Complexity/MorseHedlund
license: citation-only
triage: anchor
---

# Symbolic Dynamics II. Sturmian Trajectories

Morse and Hedlund establish the factor-complexity threshold now bearing their
names. In the one-sided form used here, an infinite word over a finite alphabet
is eventually periodic when its number of factors of some length `n` is at most
`n`. Equivalently, a word that is not eventually periodic has at least `n + 1`
factors of every length.

The repository formalization fixes natural starting indices and concludes only
eventual periodicity, so a finite nonperiodic prefix is allowed. It does not
claim recurrence, balance, a bi-infinite classification, or the converse
description of every Sturmian word. The literature attests the classical
theorem statement; the Lean proof is a direct repository implementation using
finite factor sets, unique right extension, and pigeonhole.

## Search log

- 2026-08-13: The accepted GOLD-34 design supplied the classical theorem and
  the repository spec supplied the canonical bibkey `morsehedlund1940symbolic`.
- 2026-08-13: Searched the repository, pinned Mathlib checkout, and git history
  for Morse-Hedlund names, generic word-factor complexity, and eventual-word
  periodicity. No reusable generic theorem was found.
- 2026-08-13: The lean4 skill's local smart search for `Morse Hedlund factor
  complexity eventually periodic word` returned no declaration match.
- 2026-08-13: No online metadata query was run because network capability was
  unavailable in the implementation environment. The DOI, authors, year, and
  title were not independently verified in this turn and must be checked by the
  repository's normal literature-observation lane.

## Locator

- DOI: https://doi.org/10.2307/2371431
