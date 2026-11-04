---
bibkey: benyihajnal2016relatives
authors: Beáta Bényi and Péter Hajnal
year: 2016
title: "Combinatorial properties of poly-Bernoulli relatives"
doi: null
url: https://arxiv.org/abs/1602.08684v1
claim: "Section 3.2 Theorem 12(ii) counts permutations with strict excedance-position set [k] by C(n,k), allowing fixed points."
strata_touched:
  - D5/S3/Combinatorics/PriorityLattice/TestartTreeCode
  - D5/S3/Combinatorics/PriorityLattice/TestartTraversal
license: citation-only
triage: anchor
---

## Published interpretation

Source: https://arxiv.org/html/1602.08684v1 , Section 3.2,
Theorem 12(ii), printed pages 11–12. The source distinguishes the strict
excedance set E(pi)={i : pi(i)>i} from the weak excedance set.
Its singly starred family consists of permutations of [n+k] whose strict
excedance-position set is [k]. Theorem 12(ii) gives its cardinality C(n,k).
The doubly starred family additionally forbids fixed points and is a
different family.

The substitution n=a and k=b-1 gives permutations of [a+b-1] with strict
excedance-position set [b-1]. Fixed points remain allowed. This published
count is bibliographic context; the Lean implementation targets the
actual permutation class and does not assume a tree correspondence or
import a literature theorem as a Lean axiom.

The arXiv HTML identifies its distribution license as arXiv's perpetual
non-exclusive license. This repository imports no article code, figures
or full text; this bibliographic note is `citation-only` and grants no
rights over the original article. Imported mathlib code retains its
upstream Apache-2.0 attribution and is called through imports.

## Verified locator

https://arxiv.org/abs/1602.08684v1
