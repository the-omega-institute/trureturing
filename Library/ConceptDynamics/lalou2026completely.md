---
bibkey: lalou2026completely
authors: Mohammed Lalou; Nader Mbarek; Abdallah Skender; Olivier Togni
year: 2026
title: "Completely Independent Spanning Trees in Split Graphs: Structural Properties and Complexity"
doi: 10.48550/arXiv.2512.15486
url: https://arxiv.org/abs/2512.15486v2
claim: "Conjecture 1 asserts that every hypergraph satisfies chi_p^2(H) = chi_p(H) - ceil(alpha_{chi_p(H)}(H)/2)."
strata_touched:
  - D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation
license: CC-BY-4.0
triage: anchor
---

<!-- GID: D5/L/ConceptDynamics/lalou2026completely -->

# Panchromatic and bipanchromatic coloring conjecture

Version 2 of the source was checked at the stable arXiv locator below. Section 2
defines a panchromatic k-coloring by requiring every hyperedge to contain every
color. A unique color occurs once in the whole hypergraph. A bipanchromatic
coloring is panchromatic and has no unique color, equivalently every global
color class has at least two vertices. The panchromatic and bipanchromatic
numbers are maxima over feasible color counts.

Section 3.2 defines alpha_k as the minimum number of unique colors among all
panchromatic k-colorings. Section 5, Equation (5.1), and Conjecture 1 state:

> Every hypergraph H satisfies
> chi_p^2(H) = chi_p(H) - ceil(alpha_{chi_p(H)}(H)/2).

The source reports positive integer-programming tests before proposing the
conjecture. It does not contain or attest the repository's six-vertex
counterexample. The repository result is therefore recorded as repo-derived,
with no world-priority claim.

The supplied bounded status and library intake found no existing proof or
refutation of the complete conjecture in the inspected repository, pinned
Mathlib, or stated literature surfaces. This implementation worker did not
repeat that generic novelty search; exhaustive publication coverage remains
unverified.

## Verified locator

- DOI: 10.48550/arXiv.2512.15486
- URL: https://arxiv.org/abs/2512.15486v2
- Checked text: https://arxiv.org/html/2512.15486v2, dated 28 July 2026,
  especially Section 2 paragraphs 2--3, Section 3.2's definition of alpha_k,
  and Section 5 Conjecture 1. The checked local HTML has SHA-256
`822afac3cd61ccc97ca2f75cf8ba236538793e54c8b3b21cc7b3e81acb0c776a`.
