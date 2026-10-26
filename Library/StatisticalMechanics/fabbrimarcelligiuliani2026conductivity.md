---
bibkey: fabbrimarcelligiuliani2026conductivity
authors: Simone Fabbri; Giovanna Marcelli; Alessandro Giuliani
year: 2026
title: "The conductivity matrix at the topological phase transition"
doi: null
url: https://arxiv.org/abs/2609.03832v1
claim: "The paper studies the conductivity matrix of two-dimensional lattice fermion models at a topological phase transition, under a gap assumption on the Bloch bands for nonzero mass; for its pi/2-flux Hofstadter example it supports the gap assumption only numerically, stating that for every m in [-2,2] minus {0} the fourth band stays above and the third band below the Fermi energy over the Brillouin zone, and expects an analytic proof."
strata_touched:
  - D5/S3/SpectralTopology/HalfFluxHofstadterMassGap
license: citation-only
triage: anchor
---

# Fabbri, Marcelli and Giuliani, the conductivity matrix at the topological phase transition

S. Fabbri, G. Marcelli and A. Giuliani, arXiv:2609.03832v1 [math-ph] (3 September 2026). Quotations are from the v1 TeX source, with the macros `\v{k}`, `\l`, `\mbb{B}` written as $\vec k$, $\lambda$, $\mathbb B$ and cross-references omitted.

The bands:

> we denote by $\lambda_1(\vec k;m)\le \ldots \le \lambda_M(\vec k;m)$ the eigenvalues of $\hat{H}^0(\vec k;m)$ (i.e., its *energy bands*), repeated according to multiplicity.

The gap assumption (item 1 of the second assumption): for an index $n$ with $\lambda_\pm=\lambda_{n+1},\lambda_n$ and $\mu_\pm(m)$ the minimum and maximum of $\lambda_\pm(\cdot;m)$ over $\mathbb B$,

> $\mu_+(m)>\mu_+(0)=\mu_-(0)>\mu_-(m) \quad \forall \, m\in[-m_0,m_0]\setminus\{0\}$

The $\pi/2$-flux Hofstadter example, with $d\in\mathbb R$:

$$\hat{H}^0(\vec k)= -\begin{pmatrix}
d & 1-i e^{2ik_1} & 1-ie^{2ik_2} & 0 \\
1+i e^{-2ik_1}& 0& 0 & -i+ e^{2ik_2}\\
1+ i e^{-2ik_2} & 0 & 0 & 1+i e^{2ik_1}\\
0 & i+ e^{-2ik_2} & 1- i e^{-2i k_1} & -d
\end{pmatrix},$$

with $\vec k_F:=(\frac{\pi}{4},\frac{\pi}{4})$ and

> Letting the mass parameter be $m:= d-2$ and $\hat H^0(\vec k;m):=\hat H^0(\vec k)\big|_{d=2+m}$, we then set the Fermi energy $\mu=\lambda_3(\vec k_F;m)\big|_{m=0}= \lambda_4(\vec k_F;m)\big|_{m=0}$.

> In the `MathematicaNotebook1.nb` sheet we provide numerical evidence of the validity of Assumption 2.1, and specifically of the fact that for all $m\in[-2,2]\setminus\{0\}$, $\min_{\vec{k}\in\mathbb{B}}(\lambda_4(\vec{k};m)-\mu)>0$ and $\max_{\vec{k}\in\mathbb{B}}(\lambda_3(\vec{k};m)-\mu)<0$. We expect that, with some additional technical effort, this can be fully proved analytically, but we prefer not to belabor the details of such a proof here.

## Verified locator

Source: https://arxiv.org/abs/2609.03832v1
- URL: https://arxiv.org/abs/2609.03832v1 (the e-print is a gzipped tar archive; member `FMG_v1.tex`, 2259 lines, md5 `8e03f8b9d7f104d07ebd07e00baad267`):
  - the Brillouin zone, Eq. `def:Brillouin`, l. 328–332;
  - the bands, l. 354;
  - the gap assumption, Assumption `assum:H`, l. 356–392, inequality `eqn:54` at l. 364;
  - the Bloch matrix, Eq. `eqn:Hofst_Hamiltonian`, l. 663–671;
  - the Fermi point, l. 674;
  - the Fermi energy and the numerical expectation, l. 686–690.
- The author list and the date are from the arXiv metadata; Crossref lists no journal version.
