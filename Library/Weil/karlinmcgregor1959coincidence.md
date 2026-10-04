---
bibkey: karlinmcgregor1959coincidence
authors: Samuel Karlin and James L. McGregor
year: 1959
title: Coincidence probabilities
doi: 10.2140/pjm.1959.9.1141
url: https://msp.org/pjm/1959/9-4/pjm-v9-n4-p13-s.pdf
claim: The source relates ordered transition determinants to noncrossing paths and gives a local-character consequence of order-two positivity. The original even theta jump form fails that all-times ordered determinant hypothesis; no sharp spectral gap follows from this route.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Ordered semigroups and the original theta jumps

## Published determinant interface

The journal reference is *Pacific Journal of Mathematics* 9 (1959),
1141–1164. The inspected [publisher PDF](https://msp.org/pjm/1959/9-4/pjm-v9-n4-p13-s.pdf)
has SHA-256
`e198ad4388e3744ff670ab58472d192feabee7538edb53a41ed47ac1ae91bf4a`.
Only bibliographic information and the following source applications are
retained; no third-party implementation or PDF is copied into the project.

Introduction (C), printed pp.1142–1143, relates ordered transition
probability determinants to noncoincidence for a one-dimensional strong
Markov process with continuous paths. Continuity prevents two ordered
particles from exchanging positions without meeting. A jump process is
not assigned this hypothesis merely because its state space is a line.

Section8, Theorem5, printed pp.1157–1158, assumes stationary transition
probabilities on the real line, convergence to1 on a neighborhood of
the starting point as time tends to zero, order-two positivity of the
ordered transition determinants, and an exponent $a>0$ such that

$$
P(t,x,\{y:|y-x|\ge\delta\})=o(t^a)
\quad(t\downarrow0)
$$

for every $x$ and $\delta>0$. Its conclusion is a bound $Mt^\beta$,
uniform on each fixed compact set of starting points, for every fixed
$\beta,\delta>0$. The first inequality in its proof places a middle
neighborhood between the starting point and the distant destination:
order-two positivity bounds a direct crossing by the product of the
two intermediate transitions.

Section9, Theorem6, printed pp.1159–1160, classifies homogeneous
processes with totally positive transition functions as deterministic
drift or Wiener processes, with possible exponential killing. The
original theta process is not homogeneous. That classification is not
used as a theorem about it. Nor are the pointwise transition hypotheses
of Theorem5 asserted without verification; the model check below uses
its ordered-determinant mechanism directly on the known closed form.

## Test the unchanged even form before borrowing oscillation theory

Retain the [original minimal realization](fukushima2011dirichlet.md),
$D=E_\Gamma+E_{\rm prime}$ in $L^2_{\rm even}(\nu)$, with
$d\nu=\rho\,dx=2\Phi\cosh(x/2)dx$. Let $A\ge0$ be its energy operator
and $P_t=e^{-tA}$. Reflection reduces both. On the positive half-line
the even space has radial measure $d\nu_{\rm rad}(r)=2\rho(r)dr$.
The full symmetric conductance is $J=J_\Gamma+J_p$, where

$$
J_\Gamma(dx,dy)=\Phi(x)\Phi(y)\psi(|x-y|)dxdy,
\qquad \psi(u)=\frac{e^{-u/2}}{1-e^{-2u}}>0\quad(u>0).
$$

Every prime-power graph remains in the nonnegative $J_p$. In the
nonnegative-generator convention the real polarized form is

$$
D(f,g)=\tfrac12\iint(f(y)-f(x))(g(y)-g(x))J(dx,dy).
$$

Choose three nonzero nonnegative even compact smooth functions
$f_L,f_M,f_R$, supported in the reflections of strictly separated
positive intervals $I_L<I_M<I_R$. They belong to the original even
core and have pairwise zero $L^2(\nu)$ overlap. Symmetry and disjointness
give, for distinct indices,

$$
D(f_i,f_j)=-\iint f_i(x)f_j(y)J(dx,dy)<0. \tag{O1}
$$

The conductance integral is finite by the form bound. Its Gamma part
is strictly positive before the minus sign; prime terms cannot cancel
it. Thus this test uses every actual long edge and no numerical cutoff.

The existing closed-form/semigroup correspondence gives, for
$f,g\in D[D]$,

$$
\langle f,P_tg\rangle_\nu
=\langle f,g\rangle_\nu-tD(f,g)+o(t). \tag{O2}
$$

Operator-domain membership is unnecessary. In the spectral calculus,
write $f=(A+1)^{-1/2}F$ and $g=(A+1)^{-1/2}G$. The multipliers
$(1-e^{-t\lambda})/[t(1+\lambda)]$ are bounded by1 and converge to
$\lambda/(1+\lambda)$, which verifies the form limit in (O2).

Put $a_{ij}(t)=\langle f_i,P_tf_j\rangle_\nu$,
$m=\|f_M\|_\nu^2>0$ and $c_{LR}=-D(f_L,f_R)>0$. The ordered rows
$(L,M)$ and columns $(M,R)$ have determinant

$$
\begin{aligned}
\Delta(t)&=a_{LM}(t)a_{MR}(t)-a_{LR}(t)a_{MM}(t)\\
&=-mc_{LR}t+o(t)<0
\quad\hbox{for all sufficiently small }t>0. \tag{O3}
\end{aligned}
$$

Both factors in the first product are $O(t)$; the second product has
$a_{LR}=tc_{LR}+o(t)$ and $a_{MM}=m+O(t)$. An order-two positive radial
transition kernel would give a nonnegative determinant after integration
against these ordered nonnegative source and destination weights.
Equivalently that integrated condition can itself be stated without
assuming a transition density. Equation(O3) violates it.

Consequently the original even theta semigroup cannot supply the
all-times order-two positivity required by this proposed oscillation
route. Positivity preservation of the Dirichlet semigroup remains true;
it does not impose signs on these ordered two-by-two minors. The
continuous Gamma conductance already causes the obstruction, so deleting
prime atoms would not restore this particular condition.

## What is still needed at the critical threshold

The [known critical family](lagarias2004li.md#the-full-derivative-family-and-the-remaining-estimate)
satisfies $Ah_k=h_k/2$, but that equation alone does not locate every
other nonzero eigenvalue above it. A nodal-domain upper bound cannot
be reversed into such an ordering. This note neither counts the nodal
domains of $h_1$ nor identifies a subthreshold eigenvalue.

The original remainder still requires $D(r)\ge\|r\|_\nu^2/2$.
Equations(O1)–(O3) exclude the stated all-times ordered-semigroup
hypothesis. They do not exclude a weaker resolvent or fixed-time
oscillation theorem, a different justified comparison, or the sharp
Poincare bound itself. A FIB boundary description must preserve the
long jump pairings before borrowing a theorem based on ordered paths.
Branch order alone does not supply that theorem's conditions.

The short-time determinant mechanism is reused from the inspected
classical source. Its application to the original minimal even form
is paper mathematics, without a new general-method, priority, numerical
certificate or Lean claim. Weaker spectral-ordering hypotheses remain
unverified for this operator; no exhaustive absence claim is made. RH
and the full Robin inequality remain unresolved.
