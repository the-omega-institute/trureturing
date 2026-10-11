---
bibkey: teimoorifaal2026brestricted
authors: H. Teimoori Faal
year: 2026
title: "A Bivariate B-Restricted Clique Polynomial: From Local Neighborhoods to Global Expansion"
doi: null
url: https://arxiv.org/abs/2602.24151v1
claim: "Open Problem 1 asks whether an r-connected K_{r+3}-free non-chordal graph can have a B-restricted clique polynomial that fails to be real-stable."
strata_touched:
  - D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2602.24151v1

H. Teimoori Faal, arXiv:2602.24151v1. Page numbers refer to the numbered PDF pages.

- Definition 2.1, page 4: “For G=(V,E) and B ⊆ V, define”
  \(C_B(G;x,y) := \sum_{K \subseteq V,\ K\text{ clique}} x^{|K|} y^{|K\cap B|}\).
  The empty clique contributes 1; Example 2.3 uses this convention.
- Definition 2.4, page 4: “A polynomial \(f(x,y) \in \mathbb{R}[x,y]\) is real stable if it is not identically zero and”
  \(f(x,y) \neq 0\) “for all \((x,y) \in \mathbb{C}^2\) such that \(\operatorname{Im}(x) > 0\) and \(\operatorname{Im}(y) > 0\).”
- Definition 4.2, page 7: “A graph is r-connected if removal of fewer than r vertices leaves it connected.”
- Definition 4.3, page 7: “A graph is chordal if every induced cycle has length 3.”
- Theorem 4.8, page 8: “Let r≥1. If G is r-connected, K_{r+3}-free, and chordal, then” \(C_B(G;x,y)\) “is real-stable.”
- Section 7, Open Problems, item 1, page 18: “Necessity of Conditions: Are the conditions of r-connectivity and chordality also necessary? Is there an r-connected K_{r+3}-free non-chordal graph for which C_B(G;x,y) fails to be real-stable?”

Crossref title search returned no matching work or DOI. The arXiv version is the verified locator; no publisher DOI is asserted.

## Scope

The second question of Open Problem 1 has a positive answer for every integer r≥1. Put a=max(r−2,0), take the join K_a ∨ C₄, and mark one cycle vertex. Its polynomial is
\((1+x)^a(1+2x)(1+x+xy)\), which vanishes at \((x,y)=(i,-1+i)\) in the product of the upper half-planes. The family is r-connected, K_{r+3}-free and non-chordal. For r=1 it is C₄, which is 2-connected; no exact-connectivity assertion is made.

Theorem 4.8 is a source assertion, not a premise of this settlement. Its complete-graph counterexample and the question of which marked sets preserve stability are separate questions.
