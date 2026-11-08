---
bibkey: mghirbi2026renyi
authors: Nidhal Mghirbi and Seth Douglas
year: 2026
title: "The Lovasz number is not alone: a continuum of Renyi points in the entanglement-assisted spectrum of graphs"
doi: 10.48550/arXiv.2610.20775
url: https://arxiv.org/abs/2610.20775v1
claim: "Power-compression projection formula for Petz Renyi graph radii, monotonicity, flat witnesses, and the pentagon plateau on [1/2,2]."
strata_touched:
  - D5/S3/Quantum/Matrix/PentagonQuarticTrace
  - D5/S3/Quantum/Matrix/PentagonQuinticTrace
license: citation-only
triage: anchor
---

# Renyi graph radii and the pentagon

## Verified locator

DOI: 10.48550/arXiv.2610.20775

Source: https://arxiv.org/abs/2610.20775v1

The retained primary TeX is version 1.2.1, source commit
`fed3e8013f75998145cf5240b92821dd70cd4f79`, SHA-256
`213fba00a67a0e605e3ed1ce58ff4a927a5624d02c67a67693f12a4d518f881c`.
The title and authors agree with its title block. The locators below are
literal TeX labels in that source.

For a faithful state $\sigma$, an orthogonal projection $P$ and nonzero
$s\in[-1,1]$, the power-compression definition preceding
`prop:supported` is

$$
K_s(\sigma,P)=(P\sigma^sP)^{1/s},\qquad
Z_s(\sigma,P)=\operatorname{Tr}K_s(\sigma,P),
$$

on the range of $P$, extended by zero on its orthogonal complement.
At $s=0$, use $K_0=\exp(P(\ln\sigma)P)$ on that range.
The projection formula `eq:projection-formula` is

$$
\frac1{\vartheta_\alpha(G)}
=\sup_{(P_x),\sigma}\min_{x\in V(G)}Z_{1-\alpha}(\sigma,P_x),
$$

where the projections form a representation of $G$ and the state is
faithful on the same finite-dimensional space. On $C_5$, the support
relations are $P_iP_{i+2}=0$, with indices modulo five.

`prop:endpoints`(ii) states that $\vartheta_\alpha(G)$ is nondecreasing
on $[0,2]$. The flat-witness lemma `lem:flat` gives the radius
$-\log\operatorname{Tr}(\Pi\sigma)$ at every order for
$\rho=\Pi\sigma/\operatorname{Tr}(\Pi\sigma)$ when $\Pi$ commutes with
$\sigma$. Theorem `thm:pentagon-half` proves
$\vartheta_\alpha(C_5)=5/2$ for $1/2\le\alpha\le2$.
Its flat representation has $P_i$ projecting onto
$\operatorname{span}(e_i,e_{i+1})$ and $\sigma=I/5$.

The source also discusses the Lovasz umbrella, faithful limiting centers,
and explicit optimized-center witnesses. These constructions are primary
source material. The open question in the paragraph "The pentagon curve"
asks for the exact values at $0<\alpha<1/2$; the source does not state the
sharp universal PSD fifth-moment inequality.

## Integer-moment application and limits

The repository's quartic and quintic modules concern actual complex
matrices of every finite dimension, including the empty dimension. The
quintic certificate gives

$$
\operatorname{Tr}\Bigl(\sum_i A_i\Bigr)^5
\le16\sum_i\operatorname{Tr}(A_i^5),\qquad
A_i\succeq0,\quad A_iA_{i+2}=0.
$$

This fifth-degree certificate is attributed to the supplied mathematical
source `pentagon-quintic-joint-source/proof.txt`, SHA-256
`9ecd6884c7788722176850d88a786d0306243f9373e333ed25ff6b557faf101a`.
It is not a theorem attributed to Mghirbi and Douglas. The owning Blueprint
explains the analytical positive Schatten duality at $p=5/4$ and its graph
consequence using the projection formula above. Those fractional-power
and graph steps are outside the integer-moment Lean statement. The full
curve and literature priority remain unresolved; the quintic consequence
is not a claim about the best available analytical plateau.
