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
