---
bibkey: britnellwildon2017bellnumbers
authors: John R. Britnell, Mark Wildon
year: 2017
title: "Bell numbers, partition moves and the eigenvalues of the random-to-top shuffle in Dynkin Types A, B and D"
doi: 10.1016/j.jcta.2016.12.003
url: https://arxiv.org/abs/1507.04803
claim: "For the numbers of set partitions with marked blocks defined in the paper, equation (9) gives the closed form whose second column is 2^(t-2)(2^(t-1)+1) (OEIS A007582), and Proposition 8.1 identifies the number of one-row colourings by n unlabelled colour pairs with a Type B Bell number."
strata_touched:
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.path_result
license: citation-only
triage: anchor
---

# Paired colourings of a row and Type B Bell numbers

## Verified locator

Source: [arXiv:1507.04803v1](https://arxiv.org/abs/1507.04803v1), Section 6.5,
equation (9), with the sentence after it naming OEIS A000079 and A007582;
Section 8, the definition of Q_{s,t}(n) and Proposition 8.1. Published version:
J. Combin. Theory Ser. A 148 (2017) 116–144, DOI 10.1016/j.jcta.2016.12.003
(Crossref metadata). The equation and proposition numbers are those of arXiv v1.
The title and author names follow the arXiv and Crossref metadata.

## Source statement

Equation (9) states, for the marked-partition numbers {t n}†,
{t n}† = (1/(2^n n!)) Σ_{k=0}^{n} (−1)^k C(n,k) (2(n−k))^t,
and the text derives {t 1}† = 2^(t−1) and {t 2}† = 2^(t−2)(2^(t−1)+1),
"giving sequences A000079 and A007582 respectively".

Proposition 8.1 states Q_{1,t}(n) = B†_{t−1}(n−1) for all t ≥ 1, where Q_{s,t}(n)
counts colourings of an s × t array of boxes by a set of 2n unlabelled colours
arranged into n pairs "so that no two horizontally or vertically adjacent boxes
receive colours from the same pair"; colourings that differ by a permutation of
the n pairs, or by swapping colours within a pair, are regarded as the same.

## Use in this repository

`HardinThinGraphTransport.path_result` states the one-row case of the
paired-colouring count in the A007582 form; this note is its prior-result
attribution. The repository's two-dimensional strip statements are not claimed
by the source.
