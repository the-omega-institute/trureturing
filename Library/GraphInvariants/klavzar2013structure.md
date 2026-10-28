---
bibkey: klavzar2013structure
authors: Sandi Klavzar
year: 2013
title: "Structure of Fibonacci cubes: a survey"
doi: 10.1007/s10878-011-9433-z
url: https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf
claim: "Fibonacci cube edges are the Hamming-one pairs of binary words without consecutive ones; their count is the sum of the sizes of the legal supports, equivalently the size-weighted sum of the actual support counts. Related majority, clique-complex and metric-median characterizations are attributed to Betre, Zhang and Edmond and to Xie and Xu below."
strata_touched:
  - D5/S3/Combinatorics/Graph/LegalWords/EdgeCount
  - D5/S3/Combinatorics/Graph/HereditaryFlip/Majority
  - D5/S3/Combinatorics/Graph/HereditaryFlip/Median
license: citation-only
triage: anchor
---

# Fibonacci cubes, legal supports and majority geometry

## Fibonacci-cube source and locator

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

## Majority and clique complexes

Kassahun H Betre, Yan X Zhang and Carter Edmond, "Pure Simplicial and Clique
Complexes with a Fixed Number of Facets" (2024),
DOI: 10.48550/arXiv.2411.12945,
URL: https://arxiv.org/html/2411.12945v1.
This is the source of the facet criterion below; the front-matter citation
identifies Klavzar's Fibonacci-cube survey.

Theorem 3.1 of arXiv:2411.12945v1 states that a simplicial complex with
facets F1,...,Fn is a clique complex if and only if
(Fi intersection Fj) union (Fi intersection Fk) union (Fj intersection Fk)
is a face for each three-element subset of facet indices. The complex
contains the empty face. Heredity transfers the condition from facets to
arbitrary faces; repeated inputs have a majority contained in an input.
Clique complexes are determined by their singleton and pair faces.

Yan-Ting Xie and Shou-Jun Xu, "Characterizing simplex graphs" (2025),
arXiv:2503.17160v1, Theorem 1.5, also identify finite clique or independence
complexes by the Median Property. Its surrounding discussion explicitly
relates that property to the earlier facet criterion.
URL: https://arxiv.org/abs/2503.17160v1.

## Finite-support scope and metric medians

The formal finite-support statement uses an arbitrary ambient type with
decidable equality. It includes empty and singleton constraints, so it
also allows absent vertices and the empty family. The universal least
majority-closed extension follows by induction on support cardinality and
does not assume heredity of competing extensions. These are classical
combinatorial statements and their consequences; no novelty is claimed.
The Majority module contains no graph metric or metric median theorem.
The Median module uses the native shortest-walk distance and the three
pairwise distance intervals. Their unique common vertex has exactly the
majority support. For a hereditary family, its flip graph is connected
and has a unique metric median for every triple if and only if the family
contains the empty face and is flag. The empty-face condition is explicit
because connectedness requires a vertex. This is the finite-support
form of the classical characterization discussed by Xie and Xu; it also
permits infinite ambient types and families, with finite individual faces.
