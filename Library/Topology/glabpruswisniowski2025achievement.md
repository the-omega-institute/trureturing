---
bibkey: glabpruswisniowski2025achievement
authors: Szymon Głąb and Franciszek Prus-Wiśniowski
year: 2025
title: Achievement sets — current results and open problems
doi: null
url: https://arxiv.org/abs/2512.17285v1
claim: Section 2 Problem 9 asks the unnormalized positive-measure residue converse for indexed multigeometric achievement sets; it is the same question as Section 5.1 Problem 1 of arXiv 2508.19454v1.
strata_touched:
  - D5/S3/Topology/Measures
license: citation-only
triage: anchor
---

# Multigeometric achievement sets and the residue converse

The fixed arXiv v1 source defines a multigeometric sequence using
positive weakly decreasing coefficients $k_1\geq\cdots\geq k_m>0$.
With ratio $1/n$, its first block is $k_i/n$, not $k_i$.
The Boolean sum set is

$$
\Sigma=\left\{\sum_{i=1}^{m}\varepsilon_i k_i:
\varepsilon_i\in\{0,1\}\right\}.
$$

Repeated coefficient positions are independent choices; only equal sum
values are identified in this set. Section 2, Problem 9 asks whether,
when $n=|\Sigma|$, no $k_i$ is divisible by $n$, and the actual infinite
achievement set has positive Lebesgue measure, the remainders of
$\Sigma$ modulo $n$ must be all of $\{0,\ldots,n-1\}$.
It imposes no greatest-common-divisor-one condition. This is the same
target as [Section 5.1, Problem 1 of Kenyon theorem revisited](glabkula2025kenyon.md).

`D5.S3.Topology.Measures.AchievementResidueConverseRefutation` models the
entire universal implication, retaining the coefficient indexing and
the denominator exponent one. Its closed theorem `result : ¬ claim`
uses $(9,3,3)$ and $n=6$. The block sums are
$\{0,3,6,9,12,15\}$, their residue set is $\{0,3\}$, and the actual
achievement set is $[0,3]$. The proof establishes convergence and both
directions of this interval equality through genuine `HasSum` and the
pinned Mathlib base-six digit expansion, before applying Lebesgue measure.
This describes the Lean assertion; it asserts no publication priority,
official acceptance or exhaustive current-openness clearance.

## Source and scope limits

The complete fixed-v1 TeX source is available. The definition, Boolean
sum formula, surrounding Nitecki theorem and Problem 9 are the passages
used here. The printed Nitecki interval endpoint has a scale mismatch
with the exponent-one sequence convention; that endpoint is not used
as an assumption. The survey's prime-cardinality remark is not used
as a theorem about these unnormalized coefficients.

The source's references to original journal articles are not a claim
that those articles have all been read. The supplied bounded literature
qualification does not establish exhaustive novelty or current openness.
Primitive and normalized coefficient variants remain outside this result.
The note paraphrases the source and reproduces no source files.

## Verified locator

- Fixed primary source: https://arxiv.org/abs/2512.17285v1
- Fixed source archive: https://arxiv.org/src/2512.17285v1
- Fixed PDF: https://arxiv.org/pdf/2512.17285v1
