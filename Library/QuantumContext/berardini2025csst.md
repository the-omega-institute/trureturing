---
bibkey: berardini2025csst
authors: Elena Berardini; Reza Dastbasteh; Josu Etxezarreta Martinez; Shreyas Jain; Olatz Sanz Larrarte
year: 2025
title: "Asymptotically Good CSS-T Codes and a New Construction of Triorthogonal Codes"
doi: 10.1109/JSAIT.2025.3582156
url: https://arxiv.org/abs/2412.08586v2
claim: "From a binary CSS code (C1, C2) and a linear map φ on C1 satisfying a triple-product parity condition, the paper builds the CSS-T code (C1^{Nφ}, C2^{Nφ}) with C^{Nφ} = {(x, φ(x))}, proves that φ = I gives a [[2n, k, ≥ d]] CSS-T code, and asks for maps φ giving better parameters than the identity or a permutation."
strata_touched:
  - D5/S3/Quantum/Codes/CssTDoublingMapImprovement
license: citation-only
triage: anchor
---

# Asymptotically Good CSS-T Codes and a New Construction of Triorthogonal Codes

E. Berardini, R. Dastbasteh, J. Etxezarreta Martinez, S. Jain and O. Sanz Larrarte, arXiv:2412.08586v2 (v1 2024-12-11); IEEE J. Sel. Areas Inf. Theory 6 (2025) 189–198. Quotations are from the v2 TeX source.

CSS parameters (Theorem 1):

> Let $C_2,C_1 \subseteq \mathbb{F}_2^n$  be two linear codes such that $C_2 \subseteq C_1$. Then, there exists an $[\![n,k,d]\!]$ quantum code, called CSS and denoted by $(C_1,C_2)_\mathrm{CSS}$, where $k=\dim(C_1)-\dim(C_2)$ and $d=\min\{\wt(C_1\setminus C_2),\wt(C_2^\perp\setminus C_1^\perp)\}$.

The construction (Definition 3):

> Let $C\subseteq\F_2^n$ be a linear code. Let $\phi:C\to\F_2^n$ be a map. We define $$C^{N_\phi} \defeq \left\{(x,\phi(x)) \mid x\in C\right\}.$$

The admissibility condition (Proposition 1):

> Then $\left(C_1^{N_\phi}, C_2^{N_\phi}\right)$ forms a CSS-T code if and only if $\phi : C_1 \rightarrow \F_2^n$ is a linear map such that for each $x,y \in C_1$ and $z \in C_2$ we have $$\wt(x \star y \star z) + \wt(\phi (x) \star \phi (y) \star \phi (z))\equiv 0 \mod{2}.$$

The open question (Remark 1):

> Finding maps $\phi$ giving CSS-T codes with better parameters than the choice $\phi=I$ or a permutation is an interesting open question.

## Verified locator

- URL: https://arxiv.org/abs/2412.08586v2 (source `CSST-JSAIT-final.tex`, md5 `0a12219774df7122726d3bd6783a16f0`):
  - Theorem 1, l. 199–201;
  - Definition 3, l. 275–279;
  - Proposition 1, l. 282–285;
  - Proposition 3, l. 306–321;
  - Remark 1, l. 330–332;
  - the conclusion, l. 695.
- DOI: https://doi.org/10.1109/JSAIT.2025.3582156.
