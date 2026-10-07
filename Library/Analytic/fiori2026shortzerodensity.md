---
bibkey: fiori2026shortzerodensity
authors: Andrew Fiori
year: 2026
title: Zero Density Theorems for Short Intervals
doi: null
url: https://arxiv.org/abs/2609.22624v1
claim: The preprint bounds the proportion of zeros near the strip edge in every eligible short ordinate interval; its local count refines an absolute block allowance for the actual Robin tail but supplies no signed critical-source estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Short-interval zero counts and the actual signed-tail budget

The primary is [arXiv:2609.22624v1](https://arxiv.org/pdf/2609.22624v1),
submitted 18 September 2026. The inspected PDF has 36 pages and SHA-256
`27d5a533d537de38f87029de5184597c2cb860d1a57cd2ab72be5ac24dbeb84f`.
Corollary 1 and Table 1, printed pp.1–2, Theorems 2–3, p.3, and
Corollaries 4–5, p.4, were checked in that primary. These are preprint
statements; their complete proofs and table-generating computations have
not been independently verified here. No Lean verification or originality
claim is made.

## The count, interval and quantifiers

Write $N(T)$ for the number of nontrivial zeta zeros with ordinates
$0<\gamma\le T$, and $N(T_1,T_2,\alpha)$ for the count in
$T_1\le\gamma\le T_2$, $\beta>1-\alpha$.
The source counts multiplicities and assigns half multiplicity on a
boundary. Retain those conventions rather than replacing the counts by
distinct ordinates or zero locations without multiplicity.

For $0<\alpha<1/6$, Corollaries 4–5 give explicit upper ratios

$$
\frac{N(t-h,t+h,\alpha)}{N(t+h)-N(t-h)}
<C_2(\alpha,r,h_0,t_0)
\qquad(t>t_0,\quad h_0<h<t^{2/3}).
$$

Each mechanism has its own displayed $C_2$, parameter restrictions and
positive-denominator condition. This is a bound in every eligible
interval, not an assertion only for almost all intervals. It supplies no
claim for an arbitrary smaller $h$ or a lower starting height.

Corollary 1 combines the ratio with the functional-equation reflection.
For example, Table 1 gives $\alpha=1/16$, $h_0=100$, $t_0=10^{100}$
and the rounded-down central proportion $0.1374$. Consequently that
source statement supplies

$$
N(t-h,t+h,1/16)<0.4313\,[N(t+h)-N(t-h)]
\qquad(t>10^{100},\quad100<h<t^{2/3}).
\tag{1}
$$

The constant is $(1-0.1374)/2$ from the source's
$1-2N(t-h,t+h,\alpha)/[N(t+h)-N(t-h)]$ comparison.
This application consumes the published table value; it does not
recompute or independently certify its optimization.

## A count allowance for the actual Robin kernel

Reuse the [published signed formula](../ArithSums/nicolas2025comparison.md)
from Broadbent–Fiori–Kadiri–Ng–Wilk, Proposition 13(i), rather than
replacing the original tail by a cosine sum. For a real cutoff $A\ge2$
and an actual zero $\rho=\beta+i\gamma$, its individual response is

$$
K_A(\rho)=-\frac1\rho\int_A^\infty
u^{\rho-2}\frac{1+\log u}{\log^2u}\,du.
\tag{2}
$$

Keep $L=\log A$ and $g(v)=(1+v)/v^2$ for $v>0$.
The same integration-by-parts kernel estimate used in that published
formula gives the elementary allowance

$$
|K_A(\rho)|\le
\frac{2A^{\beta-1}g(L)}{|\rho|\,|1-\rho|}.
\tag{3}
$$

Indeed, substitution $u=e^v$ gives the integral of
$e^{-(1-\rho)v}g(v)$ over $[L,\infty)$.
Integration by parts gives a boundary term and a term with $g'$,
both divided by $1-\rho$. Since $g$ decreases to zero and
$\int_L^\infty|g'(v)|dv=g(L)$, their absolute values sum to at most
$2A^{\beta-1}g(L)/|1-\rho|$. This is an application of the existing
kernel formula and elementary absolute estimates, not a new signed
estimate or prime-distribution theorem.

Let $\mathcal R(t,h)$ be the actual positive-height zero multiset in
$[t-h,t+h]$, including multiplicity. Assign each occurrence weight
$w_\rho=1$ in the open interval and $1/2$ at either ordinate endpoint.
Then

$$
Z(t,h)=\sum_{\rho\in\mathcal R(t,h)}w_\rho
=N(t+h)-N(t-h).
$$

For the parameters in (1), the weighted count with $\beta>15/16$ is
at most $\kappa Z(t,h)$, where $\kappa=0.4313$. Any additional
half-weight on the real boundary in the source's rectangular count
only increases that upper count. For every other zero,
$A^{\beta-1}\le A^{-1/16}$. Hence the count and the response refer
to the same actual multiset, and

$$
\sum_{\rho\in\mathcal R(t,h)}w_\rho A^{\beta-1}
\le Z(t,h)\left[\kappa+(1-\kappa)A^{-1/16}\right].
\tag{4}
$$

The conjugate-paired contribution of this block to (2) is
$\mathcal C_A(t,h)=2\Re\sum_{\rho\in\mathcal R(t,h)}w_\rho K_A(\rho)$.
Both $|\rho|$ and $|1-\rho|$ are at least $t-h>0$.
Combining (3)–(4), with the conjugate factor retained, gives

$$
|\mathcal C_A(t,h)|\le
\frac{4g(L)Z(t,h)}{(t-h)^2}
\left[\kappa+(1-\kappa)A^{-1/16}\right].
\tag{5}
$$

On the original Robin normalization the corresponding allowance is

$$
\sqrt A\log A\,|\mathcal C_A(t,h)|\le
\frac{4\sqrt A(1+1/L)Z(t,h)}{(t-h)^2}
\left[\kappa+(1-\kappa)A^{-1/16}\right].
\tag{6}
$$

The bracket improves the allowance obtained from (3) by only using
$\beta<1$ and the same block count. This is a count-based refinement
of that particular absolute estimate; no improvement over every other
density estimate or over the previously indexed cumulative-response
bounds is asserted. It holds for every real $A\ge2$ with the stated
ordinate-window premises, including $A=\log N$ at an authenticated
critical source. The source's large ordinate threshold is retained;
it is not a threshold on $N$, $A$ or the prime-input clock.

## What the source does not identify

The central region in this example is $[1/16,15/16]$, not the critical
line. A positive proportion in that region neither excludes an off-line
zero nor determines the phases of the zeros' arithmetic responses.
The ordinate interval $[t-h,t+h]$ is not an interval of prime inputs or
of integers tested by Robin.

The [selected critical-source application](polak2026finiterobinca.md)
keeps $A=\log N$ and the original signed integral $I_\psi(A)$.
No theorem here identifies the FIB five-pattern count with a zero count,
places that source on an ordinate interval, or gives a lower bound for
its full signed integral. The local ratio can instead be used as a
counting input for a specified part of the actual explicit formula.

Equations (5)–(6) keep both signs possible and bound only one frequency
block. To cover several blocks, their weights must form a partition
without duplicate zeros; the remaining zeros and the elementary terms
of the signed formula are still required. Every fixed off-line zero
eventually lies below a moving high-frequency cutoff, and its response
is not removed by controlling the blocks above that cutoff.
The allowance therefore supplies no finite global lower budget for
$\sqrt A\log A\,I_\psi(A)$ and does not pay the selected source's
condition $I_\psi(A)>-D^*(A)$. No new Robin verification range,
bound for the full normalized signed tail, or proof of RH is established.
