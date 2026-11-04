---
bibkey: chen2017movingparticle
authors: Joe P. Chen
year: 2017
title: "The moving particle lemma for the exclusion process on a weighted graph"
doi: 10.1214/17-ECP82
url: "https://arxiv.org/abs/1606.01577v4"
claim: "For the symmetric exclusion process on a finite weighted graph and every density α∈[0,1], the cost ½ν_α[(∇_{xy}f)²] of exchanging the occupations at x and y is at most the effective resistance R_eff(x,y) times the exclusion Dirichlet energy; the paper conjectures that this moving particle lemma is optimal on any finite weighted graph."
strata_touched:
  - D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality
license: citation-only
triage: anchor
---

# Chen, The moving particle lemma for the exclusion process on a weighted graph

J. P. Chen, Electron. Commun. Probab. 22 (2017), no. 47, 1–13; arXiv:1606.01577v4. Quotations are from the v4 TeX source.

On a finite connected weighted graph $(G,\mathbf c)$ with nonnegative conductances, the symmetric exclusion process is reversible with respect to the product Bernoulli measures $\nu_\alpha$ on $\{0,1\}^V$, and its Dirichlet energy is $\mathcal E^{\rm EX}_{\nu_\alpha}(f)=\tfrac12\sum_{xy\in E}c_{xy}\,\nu_\alpha[(\nabla_{xy}f)^2]$ with $(\nabla_{xy}f)(\zeta)=f(\zeta^{xy})-f(\zeta)$. Theorem 1 states $\tfrac12\nu_\alpha[(\nabla_{xy}f)^2]\le R_{\rm eff}(x,y)\,\mathcal E^{\rm EX}_{\nu_\alpha}(f)$ for every $\alpha\in[0,1]$, $x,y\in V$ and $f:\{0,1\}^V\to\mathbb R$, where $[R_{\rm eff}(x,y)]^{-1}=\inf\{\sum_{zw\in E}c_{zw}[h(z)-h(w)]^2:h(x)=1,\ h(y)=0\}$. The proof uses the octopus inequality of Caputo, Liggett and Richthammer. After noting that Theorem 1 gives $R_{\rm eff}(x,y)\ge(\inf_f\mathcal J^{x,y}(f))^{-1}$ (1.9), the paper states:

> However, it is unclear in general when (1.9) becomes an equality. That being said, we conjecture that Theorem 1 is optimal on any finite weighted graph, and more generally, on resistance spaces [24], in light of the connection between the moving particle lemma and the spectral gap of an interacting particle system [22,33,34].

## Verified locator

Source: https://arxiv.org/abs/1606.01577v4
- DOI: https://doi.org/10.1214/17-ECP82 (Electronic Communications in Probability 22, pages 1–13, 2017, title and author from Crossref; article number 47 from the arXiv journal reference).
- URL: https://arxiv.org/abs/1606.01577v4. The e-print member `OctopusMoving_v3.tex` has 1061 lines and md5 `39f69aeb26c41617f292bc17b1771bca`. Locations:
  - the exclusion generator, the exchange $\zeta^{xy}$ and $\nu_\alpha$, l. 110–124;
  - the Dirichlet energy, l. 125–128;
  - Theorem 1 and the effective resistance, l. 131–145;
  - the functional $\mathcal J^{x,y}$, (1.9) and the conjecture, l. 168–179.
