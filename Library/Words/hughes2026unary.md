---
bibkey: hughes2026unary
authors: Charles E. Hughes
year: 2026
title: "Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations"
doi: null
url: https://arxiv.org/abs/2608.27755v2
claim: "Section 11, Theorem 9 identifies the inserted-unary singleton insertion-degree spectrum by occupied gaps."
strata_touched:
  - D5/S1/Words/HughesUnaryInsertion
license: citation-only
triage: anchor
---

# Inserted-unary gap argument

Section 2 fixes a finite alphabet. Section 11, Theorem 9 states that for
an inserted word a^m and a base word with s non-a occurrences, the spectrum
is the integers from 1 through min(m,s+1) when m is positive. Its proof
identifies the degree of each output with the number of gaps receiving
positive inserted mass. Indexed non-a occurrences can carry repeated letters.

The theorem also assigns degree 1 when m is zero. Native positional masks
count nonempty inserted runs, giving degree 0 for an empty inserted source.
These conventions agree when the inserted source is nonempty. The native
formalization uses arbitrary alphabets; finiteness is not required by the
gap argument. Reverse-unary formulas and universal minimum-mask exchange
claims are separate arguments, not claims attributed to this theorem.

The source is https://arxiv.org/abs/2608.27755v2, Section 11, page 9.
PDF SHA-256: `5214003a97cdb9b9ef301a912e2a52552105eab34e61acead82929b7a609a3d6`.
