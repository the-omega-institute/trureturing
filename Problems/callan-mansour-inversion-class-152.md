---
slug: callan-mansour-inversion-class-152
bibkey: callan2023inversion
doi: 10.5281/zenodo.8399694
url: https://math.colgate.edu/~integers/x78/x78.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/InversionSeq/InversionSeqClass152.result
---

# Inversion Sequences Avoiding {010, 100, 102, 210} and {011, 201, 210}

## Problem

David Callan and Toufik Mansour, *Inversion Sequences Avoiding Quadruple Length-3 Patterns*,
Integers 23 (2023), #A78, Section 1, Conjecture 1:

> Class 152: {010, 100, 102, 210} ∼_I {011, 201, 210}

Here ∼_I means that, for every n, equally many inversion sequences of length n avoid each set. The authors
checked the conjecture up to n = 13 and list the comparison as "still open" in Table 1.

## Motivation

The theorem `D5/S3/Combinatorics/InversionSeq/InversionSeqClass152.result` establishes the equality for
every n; both classes have (1 + Σ_{j<n} binom(2j, j))/2 elements of length n ≥ 1.

## Gap

Pre-registration issue 11762 records the literature screen: Class 166 of the same conjecture was settled by
Asinowski and Polley, while none of the located later papers treats Class 152. This is a bounded negative
finding.

## Route

1. In the left class a value that occurs after a larger value occurs only once, and every adjacent descent
   starts at the global maximum; the sequence is cut at its first adjacent descent into a weakly increasing
   prefix and a suffix of interleaved maxima and singleton values.
2. In the right class 011 forces distinct positive entries; the sequence is cut at its last zero into a
   Catalan prefix and a unique decomposition into rotation blocks.
3. Weakly increasing inversion sequences are Dyck paths; factorizations of Dyck paths at the first ascent,
   a marked interior descent and the penultimate descent give the generating functions of both sides,
   which coincide.

## Falsifier

The statement would fail if either decomposition missed a sequence or produced one twice, or if the two
generating functions differed in some coefficient.

## Evidence

Every structural lemma and both decompositions were checked on all inversion sequences of length at most
11; the two counts agree through n = 11.

## Triage

`theorem`; the statement is Class 152 of Conjecture 1 in Callan and Mansour's paper and is quantified over
every n.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation and full-text searches, the OEIS entries and the GitHub
and repository checks recorded above.
