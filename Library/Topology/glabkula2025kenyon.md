---
bibkey: glabkula2025kenyon
authors: Szymon Głąb and Mateusz Kula
year: 2025
title: Kenyon theorem revisited
doi: null
url: https://arxiv.org/abs/2508.19454v1
claim: Section 5.1 Problem 1 asks whether positive measure forces every residue modulo the cardinality of the Boolean block-sum set when no indexed coefficient is divisible by that cardinality; this is the alias of arXiv 2512.17285v1 Section 2 Problem 9.
strata_touched:
  - D5/S3/Topology/Measures
license: citation-only
triage: anchor
---

# The unnormalized residue question

Section 5.1, Problem 1 of the fixed arXiv v1 source asks about a
multigeometric sequence $(k_1,\ldots,k_m;1/n)$ with positive natural
coefficients. Let

$$
\Sigma=\left\{\sum_{i=1}^{m}\varepsilon_i k_i:
\varepsilon_i\in\{0,1\}\right\},\qquad |\Sigma|=n.
$$

Assuming no $k_i$ is divisible by $n$ and the infinite achievement set
has positive Lebesgue measure, must $\Sigma$ have every remainder modulo
$n$? No primitive-coefficient or gcd-one condition appears in this
question. Its later appearance as
[Section 2, Problem 9 of the achievement-set survey](glabpruswisniowski2025achievement.md)
is one target, not a second problem.

The module
`D5.S3.Topology.Measures.AchievementResidueConverseRefutation` retains
the entire unnormalized universal claim with weakly decreasing indexed
coefficients and independent repeated positions. For $(9,3,3)$ and
$n=6$, the six distinct block sums are $\{0,3,6,9,12,15\}$ and the
residues are only $\{0,3\}$. The genuine achievement set, starting at
denominator exponent one, is $[0,3]$. Summability, regrouping and the
selection of every base-six digit sequence are proved on the original
indices, using Mathlib's infinite digit expansion. The conclusion is
the literal closed negation `result : ¬ claim`.

## Source and scope limits

The complete fixed-v1 TeX source is available; the passages used here
are the multigeometric convention and Section 5.1's definition,
example and question. The paper's normalized prime-case theorem
involves a translation and scaling by a common divisor; it is not a
substitute for the unnormalized question. Dividing $(9,3,3)$ by three
changes the residue conclusion and is not performed in the Lean model.

The supplied literature check was bounded. Original journal sources
cited by these papers have not all been read, and exhaustive novelty,
current-openness clearance and official acceptance are not asserted.
The result makes no claim about primitive or normalized variants, nor
about the other open questions or main theorems of this paper. This
note is citation and paraphrase only.

## Verified locator

- Fixed primary source: https://arxiv.org/abs/2508.19454v1
- Fixed source archive: https://arxiv.org/src/2508.19454v1
- Fixed PDF: https://arxiv.org/pdf/2508.19454v1
