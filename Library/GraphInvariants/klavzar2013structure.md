---
bibkey: klavzar2013structure
authors: Sandi Klavzar
year: 2013
title: "Structure of Fibonacci cubes: a survey"
doi: 10.1007/s10878-011-9433-z
url: https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf
claim: "Fibonacci cube edges are the Hamming-one pairs of binary words without consecutive ones; their count is the sum of the sizes of the legal supports, equivalently the size-weighted sum of the actual support counts."
strata_touched:
  - D5/S3/Combinatorics/Graph/LegalWords/EdgeCount
license: citation-only
triage: anchor
---

# Fibonacci cube edges and legal supports

## Locator

DOI: 10.1007/s10878-011-9433-z

URL: https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf

Section 1 defines the Fibonacci cube by restricting the Boolean hypercube
to strings without consecutive ones. Section 4.2 and Theorem 4.4 give its
cube polynomial; the coefficient of degree one counts its edges.

## Counting interpretation

Identify a binary word of length n with its occupied subset of positions
1 through n. A legal support has no consecutive elements. Each occupied
position gives an edge by deletion, and every edge has exactly one larger
support and one deleted position. Thus the unordered edge count is the
sum of support sizes. Grouping those supports by their size gives the sum
of k times the actual number of size-k legal supports. The largest possible
size is the integer quotient of n+1 by two. The empty word has no edges.

The formal statement uses the existing legal-word graph and occupation
count. It does not assert a binomial closed form, the dimensions of an
observation kernel, or any exact-sequence comparison. These are separate
mathematical assertions. This counting identity is classical; its proof
in the native legal-word realization makes no claim of mathematical novelty.
