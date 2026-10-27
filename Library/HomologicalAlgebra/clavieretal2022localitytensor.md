---
bibkey: clavieretal2022localitytensor
authors: Pierre J. Clavier; Loic Foissy; Diego A. López; Sylvie Paycha
year: 2022
title: "Tensor products and the Milnor-Moore theorem in the locality setup"
doi: 10.1007/s40879-025-00822-z
url: https://arxiv.org/abs/2205.14616v1
claim: "The paper develops locality vector spaces and locality tensor products V⊗_⊤W = K(V×_⊤W)/(I_bil ∩ K(V×_⊤W)), and states as Conjectural statement 6.16 that I_bil(V1,V2) ∩ K(V1×_⊤V2) is locality compatible with the relation ⊤_{V1×_⊤V2}, a condition under which the locality tensor product is a locality vector space."
strata_touched:
  - D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation
license: citation-only
triage: anchor
---

# Tensor products and the Milnor-Moore theorem in the locality setup

P. J. Clavier, L. Foissy, D. A. López and S. Paycha, arXiv:2205.14616v1 [math.RA, math-ph, math.QA]; European Journal of Mathematics 11 (2025), article 41. Quotations are from the v1 TeX source.

Locality vector spaces (Definition 1.1):

> A {\bf locality $\K$-vector space} or simply {\bf locality vector space} is a  pre-locality $\K$-vector space $(V,\top)$ such that the polar set $U^\top=\{x\in V: (\forall u\in U),\, u\top x\}$ of   any  subset $U\subset V$ is a linear subspace of $V$.

Locality compatibility (Definition 6.7):

> Let $(V,\top)$ be a locality vector space and $W\subset V$ a linear subspace. We say that {\bf $W$ is locality compatible with $\top$} if $\forall (x,y,z)\in V^3,~\forall w\in W,~$ $(x,y)\in\top\, \wedge (x+w,z)\in \top\Longrightarrow(\exists w'\in W): (x+w',y)\in\top\,\wedge (x+w',z)\in \top.$

Conjectural statement 6.16:

> Given a locality vector space $( {E},\top)$ and $V_1$, $V_2$ two of its subspaces, the subspace $I_{\rm bil} {(V_1, V_2)} {\cap\K(V_1\times_\top V_2)}\subset \K(V_1\times_\top V_2)$ is locality compatible with $\top_{V_1\times_\top V_2}$.

## Verified locator

Source: https://arxiv.org/abs/2205.14616v1
- URL: https://arxiv.org/abs/2205.14616v1 (source `Clavier_Foissy_Lopez_Paycha_arxiv.tex`, md5 `1f6041a82cd80114573aa776694ccf20`, 2896 lines):
  - locality sets and locality vector spaces, Definition `defn:basic_loc_defn`, l. 340–359;
  - the locality Cartesian product, l. 387–394;
  - the bilinear relations $I_{\rm bil}$, l. 422–430, and the relation $\top_{V\times_\top W}$, Eq. `eq:locreltoptimes`, l. 447–449;
  - the locality tensor product, Definition `defn:loctensprod1`, l. 556–562;
  - the relation on a free span, Eq. `eq:locrelonthefreespan`, l. 755–769;
  - locality compatibility, Definition `defn:loccompatible`, l. 1880–1886;
  - the Remark identifying $\top_{V\times_\top W}$ with $V^{\times_\top4}$ when $V=W$, l. 1972–1975;
  - compatibility implies that the quotient is a locality vector space, Theorem `thm:quotientlocality-vs`, l. 1935;
  - Conjectural statement `conj:main1`, l. 1984–1987.
- DOI: 10.1007/s40879-025-00822-z (https://doi.org/10.1007/s40879-025-00822-z; Crossref lists European Journal of Mathematics, volume 11, article 41, published 16 June 2025). The journal text was not read (subscription); its abstract lists the question whether the locality tensor product of two locality vector spaces is a locality vector space as open.
