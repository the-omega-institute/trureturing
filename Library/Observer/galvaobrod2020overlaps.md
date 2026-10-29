---
bibkey: galvaobrod2020overlaps
authors: Ernesto F. Galvão; Daniel J. Brod
year: 2020
title: "Quantum and classical bounds for two-state overlaps"
doi: 10.1103/PhysRevA.101.062110
url: https://arxiv.org/abs/1902.11039v3
claim: "For three pure states with known overlaps r_AB and r_AC, the unknown overlap r_BC lies between explicit tight bounds r_- (or 0) and r_+; for a connected graph of known overlaps the paper propagates these three-state intervals by intersecting over common neighbours, and leaves open whether this procedure is optimal."
strata_touched:
  - D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation
license: citation-only
triage: anchor
---

# Galvão and Brod, Quantum and classical bounds for two-state overlaps

E. F. Galvão and D. J. Brod, Phys. Rev. A 101, 062110 (2020); arXiv:1902.11039v3. Quotations are from the v3 TeX source.

For pure states the overlap is $r_{ij}=|\langle i|j\rangle|^2$. For the chain $B-A-C$ with known $r_{AB},r_{AC}$, put $r_\pm=\bigl(\sqrt{r_{AB}r_{AC}}\pm\sqrt{(1-r_{AB})(1-r_{AC})}\bigr)^2$. Then $r_{BC}\le r_+$, and $r_{BC}\ge r_-$ if $r_{AB}+r_{AC}>1$, otherwise $r_{BC}\ge0$; the bounds are attained for pure states of any dimension. For a connected graph of known overlaps, the procedure cycles $A$ over all common neighbours of $B,C$, intersects the inferred ranges for $r_{BC}$, adds the edge and repeats until the graph is complete. Section II.B continues:

> We leave it as an open question whether this procedure is optimal, but emphasize that even the initial iteration that produces a complete graph already provides bounds for every pair of vertices, which may be useful even if not tight.

## Verified locator

Source: https://arxiv.org/abs/1902.11039v3
- DOI: https://doi.org/10.1103/PhysRevA.101.062110 (Physical Review A 101(6), article 062110; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/1902.11039v3. The e-print member `overlap_pra_v3.tex` has 674 lines and md5 `52c4a57f4ae9ae3536a2134c036dc28d`. Locations:
  - overlaps and $r_\pm$, l. 96–119; the three-state bounds, l. 121–131;
  - the propagation procedure, l. 150–156; the open question, l. 165.
