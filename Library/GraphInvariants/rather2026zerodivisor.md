---
bibkey: rather2026zerodivisor
authors: Bilal Ahmad Rather
year: 2026
title: Combinatorial and analytic aspects of independence polynomials of zero divisor graphs
doi: 10.48550/arXiv.2606.04789
url: https://arxiv.org/abs/2606.04789v1
claim: "Theorem 4.1 counts independent subsets of the three-prime zero divisor graph; Problem 1 asks for unimodality and log concavity for every prime triple p<q<r."
strata_touched:
  - D5/S3/Combinatorics/Graph/ZeroDivisor/Support
  - D5/S3/Combinatorics/Graph/ZeroDivisor/NativeCoefficients
license: citation-only
triage: anchor
---

# Three-prime zero divisor independence polynomials

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2606.04789

Version 1: https://arxiv.org/abs/2606.04789v1

Full text: https://arxiv.org/html/2606.04789v1

## Native graph and counting formula

The graph has the actual nonzero zero divisors of the residue ring as its
vertices. Distinct vertices are adjacent exactly when their ring product
is zero. For primes p<q<r, Theorem 4.1, printed pages 18–20, gives the
independent-subset formula obtained by the singleton and two-coordinate
support cells under the Chinese remainder equivalence. The support
multiplicities are p-1, q-1, r-1 and their pairwise products.

The repository's `Support` module uses these actual vertices and the native
independent-configuration polynomial. The polynomial identity follows from
four disjoint families of all independent subsets.

## Original question

Problem 1 on printed page 24 asks whether the independence polynomial of
the zero divisor graph of ZMod(p*q*r), for primes p<q<r, is unimodal and
log-concave. The prime two belongs to the quantified family. This question
has no finite upper bound on the primes or on the coefficient index.

The proposed coefficient route uses a=p-1, b=q-1, c=r-1 and the support
endpoint max(ab+ac+bc,c+ac+bc). Setting the endpoint to ab+ac+bc for every
prime triple would omit a larger singleton family in some cases.
