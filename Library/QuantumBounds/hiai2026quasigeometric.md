---
bibkey: hiai2026quasigeometric
authors: Fumio Hiai
year: 2026
title: Log-majorizations between quasi-geometric type means for matrices
doi: null
url: https://arxiv.org/abs/2510.04691v3
claim: The tilde spectral trace uses a base-first weighted geometric mean; Problem 5.20 asks for its joint concavity parameter range.
strata_touched:
  - D5/S3/Quantum/Hiai
license: citation-only
triage: anchor
---

# Tilde spectral trace and its concavity classification

Hiai's equations (2.1), (2.5), and (2.6), printed page 4, define

$$
X\#_\alpha Y=X^{1/2}(X^{-1/2}YX^{-1/2})^\alpha X^{1/2},
\qquad K=A^{-p}\#_\alpha B^p,
$$
$$
T_{\alpha,p}(A,B)=\operatorname{Re}\operatorname{Tr}
\left(K^{1/2}A^{2p(1-\alpha)}K^{1/2}\right)^{1/p}.
$$

All powers are spectral functional calculus. The first geometric-mean argument
is its base. Proposition 5.19(1), printed page 33, gives $p\le1$ as a necessary
condition for joint concavity. Problem 5.20 asks for sufficient conditions away
from the known midpoint $\alpha=1/2$.

The project classification on positive definite complex matrix pairs is

$$
0<\alpha<1,\quad p>0
\quad\Longrightarrow\quad
\Bigl(
\bigl[\text{$T_{\alpha,p}$ is jointly concave in every finite dimension}\bigr]
\iff \bigl[\alpha=1/2\ \text{and}\ p\le1\bigr]
\Bigr).
$$

The all-dimension quantifier lies inside the left side of this single
equivalence. The necessary direction uses dimension two; the equivalence is
not asserted separately in the degenerate zero and one dimensions. The Lean
functional uses `CFC.rpow` for every matrix power.

## Off-midpoint construction

Put $r=1-\alpha$, $\gamma=(3/2)^r$, $\eta=4^r$,
$\delta=(\gamma-1)/(2(\eta-\gamma))$, $q=\delta^{1/(2r-1)}$,
and $w=1/(1+q)$. These quantities are positive when $\alpha\ne1/2$.
For the normalized rank-one projector

$$
P=\begin{pmatrix}w&\sqrt{w(1-w)}\\\sqrt{w(1-w)}&1-w\end{pmatrix}
$$

and $A_x=\operatorname{diag}(x,1)$, $x>0$, normalized rank-one compression gives

$$
\mu=1-w+wx^p,\qquad \nu=1-w+wx^{2pr},\qquad
A_x^{-p}\#_\alpha P=\mu^{-r}P,
\qquad T_{\alpha,p}(A_x,P)=(\mu^{-r}\nu)^{1/p}.
$$

At $a=q^{1/p}$ and $b=(2q)^{1/p}$ the exact difference of the scalar cores is

$$
h(a)^p-h(b)^p=\frac{(1-w)^\alpha(\gamma-1)}{2\,3^r}>0.
$$

The positive-base power identities hold for both signs of $2r-1$.
Taking $\theta=(h(a)-h(b))/(2h(a))$ and
$c=a+(b-a)/\theta$ gives $b=(1-\theta)a+\theta c$ and a strict Jensen gap.
Continuity of positive matrix powers preserves that gap at the three fixed
SPD first inputs for one common $B=P+\varepsilon I$, $\varepsilon>0$.
No negative power is taken at the singular projector.

## Midpoint assembly and the power boundary

For SPD $A,B$, set $C=A^{p/2}B^pA^{p/2}$ and
$L=A^{-p}\#_{1/2}B^p$. CFC cancellation proves
$A^{p/2}LA^{p/2}=C^{1/2}$. Equality of the spectral trace powers of the two
Gram matrices of $A^{p/2}L^{1/2}$ gives the actual identity

$$
T_{1/2,p}(A,B)=F_p(A,B)=\operatorname{Re}\operatorname{Tr}C^{1/(2p)}.
$$

For invertible $Z$, let $E_A(Z)=\operatorname{Re}\operatorname{Tr}
(Z^*A^pZ)^{1/p}$. The $\theta=0$ endpoint of the existing
`PsiMeanTraceConcavity.psi_jointly_concave` supplies fixed-congruence Epstein
concavity for $0<p\le1$. Existing Schatten Hölder and Gram calculations give

$$
F_p(A,B)\le\frac{E_A(Z)+E_B((Z^{-1})^*)}{2}.
$$

The invertible optimizer $Z=A^{-p/2}C^{1/4}$ makes both Grams equal $C^{1/2}$.
Choose this optimizer at the SPD mixed pair, apply the two fixed-$Z$ concavity
inequalities, and use the universal upper bound at each endpoint. This proves
the sufficient direction in arbitrary finite dimension, without a new
Epstein axiom or an assumed midpoint identity.

For $p>1$, put $Q=\operatorname{diag}(1,0)$ and
$P=(1/2)\left(\begin{smallmatrix}1&1\\1&1\end{smallmatrix}\right)$.
The positive-power Gram functional has
$F_p(Q,P)=F_p(I-Q,P)=2^{-1/(2p)}$ and $F_p(I/2,P)=2^{-1/2}$.
The strict deficit persists for one common small $s\in(0,1/2)$ with
$A_0=\operatorname{diag}(1-s,s)$, $A_1=\operatorname{diag}(s,1-s)$,
and $B=(1-s)P+s(I-P)$. Their mixture is $I/2$, and its exact value is
$2^{-1/2}(\sqrt{1-s}+\sqrt{s})$. Only the SPD identity connects this
positive-power boundary argument to TILDE.

## Attribution and scope

The midpoint sufficient direction is classical, including Zhang,
https://arxiv.org/abs/1811.01205v2. The project contribution is the consumed
formal assembly and all-off-midpoint construction for this exact functional.
Hiai supplies the object, necessary boundary and question. The comparison is
bounded to inspected primary manuscript versions and pinned repository
libraries; unread journal theorem bodies are not excluded by metadata.
Supported-PSD extensions, the UNTILDE family and Problem 5.18 are separate
obligations.

Jeong, Kim, and Tam, *New Weighted Spectral Geometric Mean and Quantum
Divergence*, https://arxiv.org/abs/2501.00287v1, Theorem 4.3, prove strict
concavity in the second variable for the $p=1$ tilde operator; Remark 4.4
distinguishes the first variable. This is not an all-$p$ joint-concavity
supplier. The inspected Vuong–Dinh author manuscript for DOI
10.1016/j.laa.2026.08.033 likewise gives fixed-first-input trace concavity at
$p=1$. The Heron manuscript https://arxiv.org/abs/2605.26141v1 concerns
midpoint quadratic majorization, not the affine joint Jensen inequality.

Vuong, Shudo, and Osaka, *Alternative-Mean Trace Divergences: Geometry, Data
Processing, and Barycenters*, https://arxiv.org/abs/2609.00034v1, classify a
different operator based on an unweighted transition. At a power function,
its specialization is the UNTILDE $p=1$ family and cannot be substituted for
TILDE without an additional identity.

## Verified locator

https://arxiv.org/abs/2510.04691v3

The cached v3 PDF has SHA256
517793e372e0d145619e517e7be0772e4852536ce65821cd5142e714e19e1a4b.
