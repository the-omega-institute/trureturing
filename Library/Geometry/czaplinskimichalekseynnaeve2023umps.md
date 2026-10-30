---
bibkey: czaplinskimichalekseynnaeve2023umps
authors: Adam Czapliński; Mateusz Michałek; Tim Seynnaeve
year: 2023
title: "Uniform matrix product states from an algebraic geometer's point of view"
doi: 10.1016/j.aam.2022.102417
url: https://arxiv.org/abs/1904.07563v1
claim: "The set uMPS(D,d,N) of uniform (translation-invariant) matrix product states with bond dimension D, physical dimension d and N sites is the image of the trace-word map; its closure has dimension at most min{(d−1)D²+1, dim Cyc^N(C^d)}, and Conjecture 2.14 states that equality holds for every (D,d,N)."
strata_touched:
  - D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation
license: citation-only
triage: anchor
---

# Czapliński, Michałek and Seynnaeve, Uniform matrix product states from an algebraic geometer's point of view

A. Czapliński, M. Michałek and T. Seynnaeve, Adv. Appl. Math. 142 (2023) 102417; arXiv:1904.07563v1. Quotations are from the v1 TeX source, with the source's macro `\IMPS` (typeset uMPS) kept as written.

For $D,d,N\ge1$ and matrices $M_0,\dots,M_{d-1}\in\mathbb C^{D\times D}$, the tensor $T_N(M_0,\dots,M_{d-1})=\sum\operatorname{tr}(M_{i_1}\cdots M_{i_N})\,e_{i_1}\otimes\dots\otimes e_{i_N}$ is a uniform $D$-matrix product state, and $\mathrm{uMPS}(D,d,N)$ is the image of $T_N$. It lies in the space $\mathrm{Cyc}^N(\mathbb C^d)$ of cyclically symmetric tensors. For $N=2$ it consists of the symmetric $d\times d$ matrices of rank at most $D^2$. The dimension of its closure is at most $\min\{(d-1)D^2+1,\dim\mathrm{Cyc}^N(\mathbb C^d)\}$, and the set has expected dimension when equality holds. Section 2 states:

> For every choice of $(D,d,N)$, $\IMPS(D,d,N)$ has expected dimension.

## Verified locator

Source: https://arxiv.org/abs/1904.07563v1
- DOI: https://doi.org/10.1016/j.aam.2022.102417 (Advances in Applied Mathematics 142, article 102417; title, authors, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/1904.07563v1. The e-print member `uMPS-final.tex` has 1034 lines and md5 `8f2a97c8c4c32b15d5873cfca15595b2`. Locations:
  - the definition of $T_N$ and uMPS, l. 180–193; $\mathrm{Cyc}^N$, l. 209;
  - the trivial cases including $N=2$, l. 243–253; the dimension bound, l. 272–275;
  - $\dim\mathrm{Cyc}^N$, l. 279–293; expected dimension, l. 299–305;
  - Conjecture 2.14, l. 311–313.
