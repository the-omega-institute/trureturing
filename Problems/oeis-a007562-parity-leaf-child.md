---
slug: oeis-a007562-parity-leaf-child
bibkey: wiseman2025a007562
doi: null
url: https://oeis.org/wiki/User:Gus_Wiseman?oldid=1666467#Open_Problems
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/UnorderedTrees/A007562.result
---

# Wiseman's A007562 rooted-tree counts

## Problem

> Let a(n) be the number of planted trees where non-root, non-leaf nodes an even distance from root are of degree 2. Let b(n) be the number of unlabeled rooted trees with n nodes in which every non-leaf node has at least one leaf. Is a(n) = b(n) for all n?

In the normalized sequence at size one the planted side uses the OEIS value one.
The literal planted class has size zero there, and the leaf-child class has size one.
[Wiseman's question](https://oeis.org/wiki/User:Gus_Wiseman?oldid=1666467#Open_Problems) · [A007562](https://oeis.org/A007562/internal) · [b-file](https://oeis.org/A007562/b007562.txt)

## Motivation

The question compares finite unordered rooted-tree classes up to root-preserving isomorphism.
The plant counts as a vertex, depth is measured in edges, and the leaf at each internal vertex
is an immediate child.
[Research issue #34784](https://github.com/the-omega-institute/trureturing/issues/34784)

## Gap

A143363 gives the ordered leaf-child condition using edge indexing and lists A007562 as its unordered version.
Bernstein and Sloane's table gives the Euler-transform characterization. These locators present sequence
relationships. The scope of the prior-proof screen is recorded in the research issue.
[A143363](https://oeis.org/A143363/internal) · [Bernstein–Sloane](https://arxiv.org/abs/math/0205301) · [Source screen](https://github.com/the-omega-institute/trureturing/issues/34784)

## Route

Keep the parent of each odd-depth vertex and use the grandparent for each nonroot even-depth vertex.
The inverse marks one immediate leaf at each internal vertex and moves the other children under that leaf.
The two depth formulas certify descent. Swapping two marker choices in their actual child set gives an
isomorphism of the inverse images. Transport of markers along rooted isomorphisms and the exact inverse
laws give bijectivity on the actual unordered quotient.

## Falsifier

Two nonisomorphic normalized parity trees with isomorphic forward images, or a leaf-child tree with
no forward preimage, would falsify the proposed class equivalence.

## Evidence

The Lean result has distinct clauses for literal equality at sizes at least two, the three singleton
values, and normalized equality at every positive size. The equivalence preserves every original vertex.
[D5/S3/Combinatorics/UnorderedTrees/A007562.result](../D5/S3/Combinatorics/UnorderedTrees/A007562.lean)

## Triage

Tier 1 with open-problem-resolution admission.

### What the settlement shows

Proved by `D5/S3/Combinatorics/UnorderedTrees/A007562.result`. The same-vertex equivalence
transfers the normalized count at every positive size, including examples with repeated isomorphic siblings.
The literal equality holds from size two onward. The differing literal singleton counts delimit that equality.

## ASSUMED-UNVERIFIED

Full texts of the Bernstein–Sloane erratum and the Cheon–Shapiro article were unavailable in the
preregistered screen. Publication priority beyond the inspected scope is unverified.
