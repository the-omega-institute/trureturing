---
bibkey: kulhandjian2026singer
authors: M. Kulhandjian; L. Hanzo
year: 2026
title: "Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance"
doi: 10.48550/arXiv.2610.02392
url: https://arxiv.org/abs/2610.02392v1
claim: "Conjecture 24 asserts that Proposition 23 holds for every d >= 2: for q = 2 the cross-correlation u = M_Q tau_H of the code Q(2,d) is the all-ones vector, every Z_i Z_j is a non-stabilizer element of the centralizer, and the minimum distance is 2."
strata_touched:
  - D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling
  - D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound
license: citation-only
triage: anchor
---

# Singer-difference-set qudit stabilizer codes

M. Kulhandjian and L. Hanzo, arXiv:2610.02392v1 (2026-10-01), quant-ph and cs.IT;
comment: accepted for publication in IEEE Open Journal of the Communications Society.
Source file `Paper_OJCOMS.tex`. Proposition 23 and Conjecture 24 are in Section VII.E;
the construction is the Algorithm of Section V and Appendix A.

The source sentences are quoted verbatim below.

> \begin{proposition}[$q=2$ distance ceiling; original, numerical]\label{prop:q2-ceiling} For every $d\in\{2,3,4,5,6\}$, the cross-correlation $u=M_{Q}\boldsymbol\tau_{H}\in\F 2^{n}$ of $\mathcal Q(2,d)$ satisfies $u\equiv\mathbf 1\pmod 2$ (verified by \texttt{verify\_q2\_ceiling.py}). Hence $H_{x}=\mathrm{circ}(u)$ is the all-ones circulant mod 2, and for any pair of distinct positions $\{i,j\}$ the Pauli $\mathbf a=e_{i}+e_{j}$ satisfies $\mathbf a\,H_{x}^{\top}=u_{i}+u_{j}=0\pmod 2$, putting $Z_{i}Z_{j}$ in the centralizer of $\mathcal Q(2,d)$. At $(2,2),(2,3),(2,4)$ exhaustive search certifies that $Z_{0}Z_{1}$ is \emph{not} in $\mathrm{rowspan}(H)$, so it is a non-stabilizer weight-$2$ logical and $d_{\min}(\mathcal Q(2,d))=2$ exactly. \end{proposition}

> \begin{conjecture}[General-$d$ $q=2$ ceiling]\label{conj:q2-ceiling-general} Proposition~\ref{prop:q2-ceiling} holds for every $d\ge 2$. \end{conjecture}

The list of open problems in the conclusions repeats it:

> \item \emph{General-$d$ $q=2$ ceiling.} Settle Conjecture~\ref{conj:q2-ceiling-general} analytically; numerically confirmed at $d\le 6$.

The construction at $q=2$ (Appendix A, Steps 2–4, and the Algorithm output), verbatim:

> Define $\boldsymbol\tau_{H}\in\F q^{n}$ by $(\boldsymbol\tau_{H})_{i}=1$ if $T[i]=0$, else $0$, for $i=0,\dots,n-1$.

> Set $\xi=q+1$ if $q$ is even, $\xi=2$ if $q$ is odd. Define $\boldsymbol\tau_{Q}\in\F q^{n}$ by $(\boldsymbol\tau_{Q})_{i}=1$ if $T[(\xi i)\bmod(q^{d+1}-1)]=0$, else $0$.

> $M_{Q}=\mathrm{circ}(\boldsymbol\tau_{Q})$, the $n\times n$ circulant matrix with first column $\boldsymbol\tau_{Q}$ and subsequent columns cyclic-shifts thereof: $(M_{Q})_{i,j}=(\boldsymbol\tau_{Q})_{(i-j)\bmod n}$.

> Compute the centralizer $\mathcal C=\{(\mathbf a,\mathbf b)\in\F q^{2n}\colon \mathbf a H_{x}^{\top}=\mathbf b H_{z}^{\top}\}$

> $d_{\min}=\min\{\wt(\mathbf v)\colon \mathbf v\in \mathcal C\setminus\mathcal S\}$.

Here $T[i]=\Tr_{K/F}(\alpha^i)$ for a primitive $\alpha\in\mathbb F_{q^{d+1}}$, $n=(q^{d+1}-1)/(q-1)$,
$A=\mathrm{circ}(\boldsymbol\tau_H)$ is the Singer incidence matrix, $H=(H_z\mid H_x)=(A\mid M_QA)$ and
$\mathcal S$ is the row space of $H$.

## Verified locator

DOI: `10.48550/arXiv.2610.02392`. Canonical source URL: `https://arxiv.org/abs/2610.02392v1`.
Proposition 23 (`prop:q2-ceiling`) and Conjecture 24 (`conj:q2-ceiling-general`) are in
Section VII.E; the open-problem list is in Section X; the construction is in Appendix A.


Conjecture 25, Section VII, page 19 (verbatim source TeX):

> For prime $p$ odd, $d_{\min}(\mathcal Q(p,2))\le p+1$.

The trace-plane definition, Section III, page 7 (verbatim source TeX):

> Its first column $\boldsymbol\tau_H$ has $(\boldsymbol\tau_H)_i=1$ iff $\Tr_{K/F}(\alpha^i)=0$.

The odd-prime construction takes $K=\mathbb F_{p^3}$ and $n=p^2+p+1$,
with $\tau_H(i)=[\operatorname{Tr}(\alpha^i)=0]$ and
$\tau_Q(i)=[\operatorname{Tr}(\alpha^{2i})=0]$. The trace-plane description
is on page 7 and the algorithm in Appendix A on pages 27–28.

The Appendix A worked example at $p=3$, using $X^3+2X^2+X+1$ and $\alpha=X$,
prints $D=\{2,3,6,8\}$ and $Q=\{0,7,8,11\}$.
The defining trace formulas instead give $D=\{0,7,8,11\}$ and
$Q=\{0,4,10,12\}$, with $Q=2^{-1}D$ modulo 13.
These corrected supports are obtained by exact arithmetic in the stated cubic
polynomial quotient; the proof uses the defining trace formulas.
