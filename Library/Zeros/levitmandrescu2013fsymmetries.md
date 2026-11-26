---
bibkey: levitmandrescu2013fsymmetries
authors: Vadim E. Levit; Eugen Mandrescu
year: 2013
title: On f-Symmetries of the Independence Polynomial
doi: 10.48550/arXiv.1303.2564
url: https://arxiv.org/abs/1303.2564v1
claim: "Theorem 1.2 gives Gutman's corona identity I(G ◦ H; x) = I(H; x)^|V(G)| I(G; x/I(H; x))."
strata_touched:
  - D5/S3/StatisticalMechanics/HardCore/IndependenceRootMultiplicity
license: citation-only
triage: anchor
---

# Gutman's formula for the independence polynomial of a corona

Levit and Mandrescu, Theorem 1.2 on page 3, state the corona identity
$$
I(G\circ H;x)=I(H;x)^{|V(G)|}I\bigl(G;x/I(H;x)\bigr).
$$
They attribute it to Ivan Gutman, *Independence vertex sets in some
compound graphs*, Publications de l'Institut Mathématique 52 (1992),
5–9, reference [9]. The product is understood after clearing the
substitution denominators.

For $G=K_t$ and $H$ the edgeless graph on $k$ vertices, the two input
polynomials are $1+tx$ and $(1+x)^k$. For $t>0$ this gives
$(1+x)^{(t-1)k}((1+x)^k+tx)$. When also $k>0$, evaluating the residual
at −1 gives $-t$, so the multiplicity is $(t-1)k$. This known identity
is the algebraic input to the application to Bhardwaj et al., Question 5.8.

## Verified locator

- arXiv v1, Theorem 1.2 (Gutman’s corona identity), p. 3, and bibliography reference [9], p. 9. [Theorem](https://arxiv.org/pdf/1303.2564v1#page=3) · [Version record](https://arxiv.org/abs/1303.2564v1) · [DOI](https://doi.org/10.48550/arXiv.1303.2564)
