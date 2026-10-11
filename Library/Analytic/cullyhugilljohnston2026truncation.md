---
bibkey: cullyhugilljohnston2026truncation
authors: Michaela Cully-Hugill and Daniel R. Johnston
year: 2026
title: On the error term in the explicit formula of Riemann-von Mangoldt II
doi: null
url: https://arxiv.org/abs/2402.04272v3
claim: The primary selected-height theorem supplies an explicit complete signed degree-one tail allowance at each actual source; its cutoff selection does not control the corresponding joint Robin finite head.
strata_touched: []
license: citation-only
triage: anchor
---

# Selected-height explicit formula and the original signed suffix

The primary is Cully-Hugill--Johnston,
[arXiv:2402.04272v3](https://arxiv.org/pdf/2402.04272v3), Theorem 1.2
on printed p.2 and Table 1 on printed p.3. The versioned PDF has
19 pages and SHA-256
`9bf784f264970a5bb82e54547c2dbd68b1a4cc6a69ee679b8fc2159d006a565c`.
The inspected statement and numerical row are literature suppliers;
the full proof and the table-generating computations are not
independently reproduced here. No Lean verification is claimed.

## Exact supplier contract

The source uses the weak prime-power function
$\psi(x)=\sum_{n\le x}\Lambda(n)$, with every nontrivial zero counted
with multiplicity. For fixed $0<\alpha\le1/2$ and $0\le\omega\le1$,
Theorem 1.2 supplies constants $M,x_M$ such that for every $x\ge x_M$
and

$$
\max\{51,\log^2x\}<Y<\frac{x^\alpha-2}{4},
$$

there exists $T^*\in[Y,2Y]$ with

$$
\psi(x)=x-\sum_{|\operatorname{Im}\rho|\le T^*}
m_\rho\frac{x^\rho}{\rho}+e(x,T^*),
\qquad
|e(x,T^*)|\le\frac{Mx(\log x)^{1-\omega}}Y.
$$

The Table 1 row used for the original-source application is
$\alpha=1/2$, $\omega=1$, $\log x_M=10^{13}$ and $M=19.81$.
Thus its source threshold is $x\ge\exp(10^{13})$, not $x\ge10^{13}$.
This row is attributed to the authors; quoting it is not an independent
certificate of their computations.

The height is selected by the theorem for each actual $x$. The
contract does not apply to every prescribed height in $[Y,2Y]$, and
separate pointwise applications do not select a common height for
different sources. The source's Theorem 1.3 and Corollary 3.3 provide
a distinct common-height interval formulation; they are not silently
substituted into the pointwise application.

## Preserve the complete conjugate-pair endpoint

Let $P_x(T)=2\operatorname{Re}\sum_{0<\operatorname{Im}\rho\le T}
m_\rho x^\rho/\rho$ and
$q(x)=\log(2\pi)+\tfrac12\log(1-x^{-2})$.
Let $\Lambda_{\mathbb R}(x)$ equal $\log p$ at an actual integer prime
power $x=p^k$, and zero otherwise. The classical complete explicit
formula with symmetric height ordering gives

$$
P_x(\infty)=x-\psi(x)-q(x)+\frac12\Lambda_{\mathbb R}(x).
$$

The source's selected-height statement therefore directly supplies
the complete real paired tail $H_x(T^*)=P_x(\infty)-P_x(T^*)$:

$$
\left|H_x(T^*)+q(x)-\frac12\Lambda_{\mathbb R}(x)\right|
\le\frac{Mx(\log x)^{1-\omega}}Y.
$$

The half-prime-power atom matches weak $\psi$ to the symmetric
endpoint. Actual zero real parts and multiplicities remain in
$x^\rho/\rho$; no critical-line replacement is made. The statement
concerns the real conjugate-pair tail, not ordinary convergence of
the complex positive-ordinate half-sum at a prime power. No separation
from prime powers is assumed: the full weak-$\psi$ error is paid by
the primary theorem in its stated domain.

## Consumer and remaining boundary

The [original-core application](../Estimation/trureturing2026pricegapconvexity.md)
uses $x=A=\log N$, while retaining the original integrated response
at $B=\log u$ with $N=pu$. Choosing
$Y=(\sqrt A-4)/4$ satisfies the supplier's strict domain after its
threshold and selects $T^*\asymp\sqrt A$. Combining this direct
degree-one supplier with the [existing complete degree-two suffix
contract J1--J6](../ArithSums/nicolas2025comparison.md#a-signed-infinite-height-allowance-from-the-existing-landau-formula)
pays the actual signed compensated suffix at those same selected
cutoffs. It does not reproduce J1--J6 as a new theorem or estimate
each zero of the degree-one infinite tail by absolute value.

The pointwise theorem supplies no favorable sign for the corresponding
joint finite head, no free payment of $K(A)-\psi(A)$, and no common
cutoff chosen independently of the sources. The original actual
complete-head condition CR23, PG15/J and RH remain unproved. The
application is supplier-relative, without a literature-originality
claim or a new generic explicit-formula theorem.
