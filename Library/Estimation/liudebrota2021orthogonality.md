---
bibkey: liudebrota2021orthogonality
authors: Yizhou Liu; John B. DeBrota
year: 2021
title: "Relating measurement disturbance, information, and orthogonality"
doi: 10.1103/PhysRevA.104.052216
url: "https://arxiv.org/abs/2105.02074v2"
claim: "The paper defines the disturbance, measurement strength and orthogonality of a POVM with Lüders updating, proves an information-disturbance trade-off relation in which orthogonality plays a role, identifies SICs as the measurements closest to a nondisturbing ideal, and conjectures that a specific block-diagonal projective POVM minimizes the orthogonality when there are fewer effects than the dimension."
strata_touched:
  - D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation
license: citation-only
triage: anchor
---

# Liu and DeBrota, Relating measurement disturbance, information, and orthogonality

Y. Liu and J. B. DeBrota, Physical Review A 104(5) (2021) 052216, DOI 10.1103/PhysRevA.104.052216; arXiv:2105.02074v2 (titled "Relating measurement disturbance, information and orthogonality"). Quotations are from the arXiv v2 TeX source.

For a POVM $\{E_i\}_{i=1}^n$ on $\mathbb C^d$ the paper sets $[S]_{ij}=\operatorname{tr}(\sqrt{E_i}\sqrt{E_j})$ and defines the orthogonality $O=\|S-\mathbb 1\|_F^2$. For $n<d$, with $d=an+b$ and $0\le b<n$, it constructs the projective POVM of diagonal $0/1$ effects on disjoint blocks with $a$ ones in each of the first $n-1$ effects and $a+b$ in the last, so $S=\operatorname{diag}(a,\dots,a,a+b)$, and states:

> The above constructed POVM has minimal orthogonality $O$ among POVMs having $n(n<d)$ nonvanishing effects.

## Verified locator

Source: https://arxiv.org/abs/2105.02074v2
- DOI: https://doi.org/10.1103/PhysRevA.104.052216 (journal version; title, authors, journal, volume, issue and article number from Crossref; the journal text was not read).
- URL: https://arxiv.org/abs/2105.02074v2. The e-print member `apssamp.tex` has 864 lines and md5 `527db32de2aed1b45dd0a3b1d4a2412d`. Locations:
  - the matrix $S$ and the orthogonality $O$, l. 400–420;
  - the construction for $n<d$ and its $S$ and $O$, Appendix "Fewer effects", l. 761–792;
  - the conjecture, l. 795–797.
