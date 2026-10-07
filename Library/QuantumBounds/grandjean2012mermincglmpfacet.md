---
bibkey: grandjean2012mermincglmpfacet
authors: B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin
year: 2012
title: "Bell inequalities for three systems and arbitrarily many measurement outcomes"
doi: 10.48550/arXiv.1204.3829
url: https://arxiv.org/abs/1204.3829v2
claim: "The inequality (1), Mermin-CGLMP, defines a facet of the full local polytope for every K >= 2."
strata_touched:
  - D5/S3/QuantumBounds/MerminCglmpFacet
  - D5/S3/QuantumBounds/CglmpFacetRigidity
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.1204.3829

Source: https://arxiv.org/abs/1204.3829v2

Archive DOI URL: https://doi.org/10.48550/arXiv.1204.3829

Journal: Phys. Rev. A 85, 052113. Journal DOI URL:
https://doi.org/10.1103/PhysRevA.85.052113

# The Mermin-CGLMP facet conjecture

Section II, PDF p. 1, states:

> We consider a scenario involving three spatially separated parties (henceforth referred as Alice, Bob and Charlie), and with each of them performing 2 alternative K-outcome measurements.

The full joint probabilities have two inputs and K outputs per party. Input
0 in Lean is source setting 1; input 1 is source setting 2. A deterministic
behaviour assigns both outputs of each party in advance, and the local
polytope is the convex hull of all these behaviours.

Equation (1), PDF p. 1, is

$$
\begin{aligned}
S^{(K)}={}&\langle[A_2-B_1+C_1]_K\rangle
+\langle[A_1+B_2-C_1]_K\rangle\\
&+\langle[-A_1+B_1+C_2]_K\rangle
+\langle[-A_2-B_2-C_2-1]_K\rangle\ge K-1.
\end{aligned}
$$

The same page states:

> where [X]_K stands for X modulo K

Equation (2) defines the bracket expectation as

$$
\langle[X]_K\rangle=\sum_{j=0}^{K-1}j\,P(X=j\,\mathrm{mod}\,K).
$$

Section II, PDF p. 2, states:

> It suffices to consider deterministic classical strategies for determining the minimal value of S^(K) allowed in a local theory

The conjecture sentence, Section II, PDF p. 2, is:

> We conjecture that inequality (1) is indeed facet-defining for all K ≥ 2.

The paper verifies the facet property through K=8. The Lean statement
`MerminCglmpFacet.claim` includes validity and says that the affine dimension
of its saturating face plus one equals the affine dimension of the full
local polytope, for every K ≥ 2. Its `result` proves that statement.

The decisive mechanism is a family of relabelled CGLMP slices indexed by
Charlie's two outputs. Bipartite rigidity gives a multiplier on each slice;
the rectangular identity forces the multiplier to be constant. The general
`FacetRigidityBridge.rigidity_facet_bridge` turns this rigidity into the
affine-dimension equation. The proof uses a short-arc derivation of
Masanes's bipartite facet result, cited separately as
`masanes2003tightbell`.

The facet clause of Appendix B inequality (B1), the fully symmetric
generalisation, and extension to more parties are separate questions.
The local-bound clause of (B1) belongs to
`grandjean2012threesystems`; this note concerns inequality (1).
