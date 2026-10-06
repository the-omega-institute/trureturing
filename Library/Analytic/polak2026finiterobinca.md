---
bibkey: polak2026finiterobinca
authors: Robert Polak
year: 2026
title: A Finite Computer-Assisted Verification of Robin's Inequality via Colossally Abundant Profiles, with Exact Prime-Power Residual Dynamics
doi: 10.5281/zenodo.21808589
url: https://doi.org/10.5281/zenodo.21808589
claim: The preprint reports a finite Robin verification and an effective positive full-support core; the core applies at the selected critical source's own logarithmic clock, but does not bound its signed prime-error tail or prove RH.
strata_touched: []
license: citation-only
triage: anchor
---

# Finite CA-profile verification and the signed residual

The source is Robert Polak, Zenodo preprint, record
[21808589](https://doi.org/10.5281/zenodo.21808589), version 1.0.0, published
5 August 2026. The retrieved PDF has 37 pages and SHA-256
`9a118f1f0247872458fc9dfbc91dfe067df7bbeb162f46fc1ad11e64f7913b2d`.
The locators below use printed pages. The full-support identity,
Lemma 7, and Proposition 10 with its argument on pp.3–8, and the
residual and event interfaces in §8.2–8.8 on pp.18–28 were inspected.
This is a primary-source applicability check, not a whole-paper proof audit,
independent rerun of its certificates, peer-review claim, or Lean verification.

## Finite theorem and residual interface

The preprint claims Robin's strict inequality for every

$$
5041\le n\le 10^{7.1\times10^{22}}.
$$

Its certificate exhausts 3,341,978 colossally abundant exponent profiles, uses an analytic prime-power reduction and a finite-height zero verification, and transfers certified CA endpoints to intervening integers by Robin's convexity proposition. The stated CA support computation reaches $1.64967\times10^{23}$.

After the finite theorem, the source derives exact prime-power cell and signed-triangular identities. Its exploratory event scan is explicitly separated from the finite proof: the universal eventwise target needed for an infinite Robin proof remains unproved.

## Directly reusable effective core

For a real $x\ge2$ and a full-support integer
$n=\prod_{p\le x}p^{a_p}$ with every $a_p\ge1$, write

$$
\begin{aligned}
\Delta(n)&=\gamma+\log\log\log n-\log\frac{\sigma(n)}n,\\
I_\psi(x)&=\int_x^\infty(\psi(t)-t)
              \frac{1+\log t}{t^2\log^2t}\,dt,\\
z(n,x)&=\frac{\log n-x}{x},\\
B_2(n,x)&=\log\left(1+\frac{\log(1+z(n,x))}{\log x}\right)
             -\frac{z(n,x)}{\log x},\\
R_{\rm core}(n,x)&=\frac{\log n-\vartheta(x)}{x\log x}
                   -\sum_{p\le x}\log(1-p^{-(a_p+1)}),\\
C_{\rm pp}(x)&=\frac{\psi(x)-\vartheta(x)}{x\log x}
             +\sum_{\substack{p\le x,\ m\ge2\\p^m>x}}\frac1{mp^m}.
\end{aligned}
$$

The logarithmic margin is defined when $n>e$; the critical-source
application below is entirely above 5040. Proposition 6, p.5, gives

$$
\Delta(n)=I_\psi(x)+B_2(n,x)+R_{\rm core}(n,x)-C_{\rm pp}(x).
$$

This is the same $I_\psi$ and positive kernel used in the
[Nicolas comparison](../ArithSums/nicolas2025comparison.md).
The paper denotes the margin by $\mathcal G(n)$; it is not the Gronwall
quotient $G(n)=\sigma(n)/(n\log\log n)$ used in the other source notes.

Define the paper's independent full-support minimum by

$$
\begin{aligned}
\Phi_{p,x}(a)&=(a-1)\frac{\log p}{x\log x}
                       -\log(1-p^{-(a+1)}),\\
D^*(x)&=\sum_{p\le x}\min_{a\in\mathbb Z_{\ge1}}\Phi_{p,x}(a)-C_{\rm pp}(x).
\end{aligned}
$$

Lemma 7 and Corollary 8, pp.6–7, give
$R_{\rm core}(n,x)-C_{\rm pp}(x)\ge D^*(x)>0$ without a CA,
GA1, GA2, or self-tangency premise. The minimization retains full support;
its activation rule is not the paper's CA-family activation rule.
Proposition 10, p.8, gives the effective, unbounded continuation

$$
\sqrt x\log x\,D^*(x)>D_{\rm lb}(x)>\frac12
\qquad(x\ge56\,048\,351).
$$

The full envelope is explicitly defined on p.7. Put

$$
\begin{aligned}
L_x&=\log x,& \ell_x&=\frac{L_x+\log2}{2},&
\epsilon_x&=\frac{3.965}{\ell_x^2},& q_x&=1-\sqrt{\frac2x},\\
a_x&=\frac{L_x}{\sqrt2\,\ell_x},&
j_x&=\frac{L_x}{\sqrt2}
       \left(\frac{q_x}{\ell_x}-\frac1{\ell_x^2}\right),\\
s_x&=(1-\epsilon_x)j_x-2\epsilon_xa_x-\frac1{\sqrt x},\\
D_{\rm lb}(x)&=\left(\frac12-\frac1{3\sqrt{2x}}\right)s_x.
\end{aligned}
$$

Here $a_x,j_x,s_x$ are the paper's $A(L),J(L),S(L)$ at $L=\log x$;
$A=\log N$ below is the source clock. Proposition 10 also states that
$D_{\rm lb}$ is increasing on this range. Retaining this published
function avoids discarding its effective surplus above $1/2$.

That continuation uses the cited Dusart theta bound and the explicit
positive contributions from $\sqrt{2x}<p\le x$. It is separate from
the finite all-integer Robin theorem and needs no finite-height RH input
in the inspected argument. Its cited theta theorem is an external
premise; its original proof was not independently audited here.
The finite support sweep and the analytic continuation are reused,
not repeated computations or new reserve estimates.

## Application at the same critical source and clock

Under a Robin counterexample, select the least global maximizer $N>5040$
by the [Caveney–Nicolas–Sondow reduction](../Arith/caveney2012sacaga.md).
Write $A=\log N$, $P=P^+(N)=p_k$, and let $P^+$ be the next prime.
This source is CA with initial prime support and belongs to $U_1$.
The existing [seven-smooth exclusion](../../Blueprint/D5/S3/Arith/Robin/SevenSmooth.md)
rules out $k\le4$. Hence the
[Kalyabin endpoint conditions](kalyabin2026maximalgronwall.md) apply
and give $P<A<P^+$ at this same integer.

There is no prime between $P$ and $A$, so the full-support products and
sums above contain exactly the actual primes of $N$ when **$x=A$**.
The same source also attains the full-support core minimum. Its proper
GA1 condition gives deletion comparisons in the range $N/p>e$, and GA2
gives every one-prime insertion comparison. The existing archived
[direct tangent-CA bridge](mantovanelli2026primeworkload.md), source §4,
`thm:direct-bridge`, therefore identifies this very $N$ as the regular CA
optimizer at

$$
\varepsilon_A=\frac1{A\log A}.
$$

This is precisely the price in Polak's full-support minimization.
Put $Z(m)=\sigma(m)/m$. For each actual $p\le A$, the local price
objective and $\Phi_{p,A}$ differ by an additive constant and a sign.
Equivalently, the source's
minimizer calculation on p.6 gives

$$
\Phi_{p,A}(a+1)-\Phi_{p,A}(a)
=\varepsilon_A\log p
 -\log\frac{Z(p^{a+1})}{Z(p^a)}.
$$

Thus the actual $a_p=v_p(N)$ attains
$\min_{a\ge1}\Phi_{p,A}(a)$. Regularity excludes a tied layer.
The correspondence uses the clock price $\varepsilon_A$, rather than
identifying it with the support-parametrized CA-family price discussed
at the end of Polak's p.6. Initial support and $P<A<P^+$ keep exactly
the same prime set in both minimizations. Consequently

$$
R_{\rm core}(N,A)-C_{\rm pp}(A)=D^*(A).
$$

Moreover $z(N,A)=0$ and $B_2(N,A)=0$ exactly. Proposition 6 now gives
the paper-level identity

$$
\Delta(N)=I_\psi(A)+R_{\rm core}(N,A)-C_{\rm pp}(A)
          =I_\psi(A)+D^*(A).
$$

The core optimization slack is zero at this selected source. Its exact
strict Robin condition is $I_\psi(A)>-D^*(A)$; equality yields
$\Delta(N)=0$ and does not satisfy strict Robin. This application
identifies the actual minimizer and pays no new signed estimate.

The numerical threshold also has an existing supplier.
[Axler's finite stop](../notes/axler2023robin.md), author version
[2110.13478v3](https://arxiv.org/pdf/2110.13478v3), Lemma 2.3, p.3,
cites strict Robin for $5041\le n\le N_K$, where
$K=999\,999\,476\,056$ and $N_K$ is the $K$th primorial.
Therefore the counterexample-level source has $N>N_K$, and simply

$$
A>\log N_K\ge K\log2>\frac K2>56\,048\,351.
$$

This consumes the cited finite verification; it neither reruns nor extends
it, and uses no theta estimate to compare these thresholds.
Proposition 10 thus gives at this fixed source

$$
\boxed{\displaystyle
\Delta(N)>I_\psi(A)+\frac{1}{2\sqrt A\log A}.}
$$

In particular a hypothetical selected counterexample must satisfy
$\sqrt A\log A\,I_\psi(A)<-1/2$. A source-specific lower bound
$\sqrt A\log A\,I_\psi(A)\ge-1/2$ would suffice to exclude it.

The same application retains the complete envelope and gives

$$
\sqrt A\log A\,\Delta(N)
>\sqrt A\log A\,I_\psi(A)+D_{\rm lb}(A).
$$

Thus it is enough to prove the weaker source-specific condition

$$
\boxed{\sqrt A\log A\,I_\psi(A)\ge-D_{\rm lb}(A).}
$$

It is weaker than the half-unit condition because $D_{\rm lb}(A)>1/2$.
Conversely, a hypothetical selected counterexample must satisfy the
stronger necessary condition
$\sqrt A\log A\,I_\psi(A)<-D_{\rm lb}(A)$.
The strict inequality in Proposition 10 supplies strict Robin even
if the sufficient tail condition is attained with equality.
The signed condition remains unproved. Its explicit core envelope and
cutoff are paid at this same finite source, without an unbounded
critical-source sequence or Kalyabin's existential $K_\varepsilon$.
This does not make that separate asymptotic cutoff effective.

This is reuse of Polak's core estimate on the endpoint-restricted source,
including its full published envelope, not a new reserve theorem,
numerical evaluation, or signed Robin estimate. Positivity of $D^*$
does not assert positivity of $\Delta$; the unknown signed $I_\psi(A)$
has been retained. Neither the complete divisor-deletion comparisons
nor the all-multiplier GA2 comparisons have yet supplied its needed bound.
The application adds no Lean declaration or formal certification of the
external analytic or finite-verification premises.

## Published event dynamics and the unpaid prime-state work

The same manuscript already supplies a continuous-flow and prime-power
event program. Reuse this published construction rather than treating
an affine recurrence, a cone, or a quadratic energy as a new FIB estimate.
The source's auxiliary buffer is

$$
B(t)=\sum_\rho\frac{e^{(\rho-1/2)t}}{\rho(1-\rho)},
\qquad C=B(0)=2+\gamma-\log(4\pi),
$$

with the complete nontrivial-zero multiset. Theorem 15, pp.19–20, makes
eventual nonnegativity of $\mathcal P(t):=C-B(t)$ equivalent to RH.
Here $\mathcal P$ is the paper's $P(t)$, not the support prime $P$ above.
It is not $\Delta(N)$ or the normalized $I_\psi(A)$.

Equation (8.24), p.22, identifies the regularized buffer exactly with the
[classical Chebyshev primitive](lay2015mertenssignchanges.md):

$$
\widehat B(\log x)
=-\sqrt x\int_x^\infty\frac{\psi(u)-u}{u^2}\,du
 -\frac{\log(2\pi)}{\sqrt x},\qquad x>1.
$$

The explicit trivial-zero correction is
$B(t)-\widehat B(t)=\sum_{j\ge1}e^{-(2j+1/2)t}/(2j(2j+1))$ for $t>0$.
This reuses the existing primitive interface; the additional
$(1+\log u)/\log^2u$ weight in $I_\psi$ remains distinct.

For $q=p^m$, put $\tau_q=\log q$ and $J_q=\Lambda(q)/\sqrt q$.
Equations (8.26)–(8.30), pp.23–24, define, for $t\ge\log2$
and $\mathcal P(t)>0$,

$$
\begin{aligned}
g(t)&=e^{t/2}\left(1-\frac{e^{-3t}}{1-e^{-2t}}\right),&
k(t)&=g(t)-C/4,\\
Q(t)&=\sqrt{\mathcal P(t)^2/4+2k(t)\mathcal P(t)},&
E_B(t)&=\mathcal P'(t)^2-Q(t)^2.
\end{aligned}
$$

On an open prime-power cell $E_B'=-2k'\mathcal P$; at an event,
$\Delta\mathcal P'=-J_q$ and
$\Delta E_B=J_q^2-2J_q\mathcal P'(\tau_q^-)$. Lemma 18 supplies
the initial positive cone at $q=2$. Theorem 19 preserves it, and concludes
RH, **provided that every next actual event with the inherited cone obeys**

$$
Q(\tau_q)+\mathcal P'(\tau_q^-)>J_q.
$$

This universal event premise remains unpaid. Propositions 20–21,
p.25, give its exact signed triangular-window form; they do not bound
the signed window. Proposition 22, p.26, gives the central-secant estimate
$|\mathcal P(t+h)-\mathcal P(t-h)|^2\le4\mathcal P(t)\mathcal P(2h)$
**assuming RH**. It cannot be imported as an unconditional local estimate
in a proof of RH. The source's adaptive window has additive scale
$\sqrt q\log q$, rather than an independently chosen coarse interval.

The separate energy audit makes the missing joint quantity explicit.
For $r\ge0$, $\epsilon_r=(1+t)^{-r}$ and
$E_r=(1-\epsilon_r/2)\widehat B^2+2\epsilon_r\widehat B'^2$,
equation (8.52), p.27, gives

$$
\Delta E_r
=4\epsilon_r(\tau_q)J_q\widehat B'(\tau_q^-)
 +2\epsilon_r(\tau_q)J_q^2.
$$

Proposition 23, p.28, supplies
$\sum_q(1+\log q)^{-r}\Lambda(q)^2/q<\infty$ exactly when $r>2$.
It pays the square-kick budget, not the signed state-prime work in the
first term. The source also excludes a fixed positive-definite quadratic
form decreasing for every homogeneous cell state, and shows that a
positive semidefinite quadratic form invariant under every common
translation of its two characteristic coordinates must annihilate
$(1,1)$. This restriction concerns universal state-independent energies;
it does not exclude an estimate adapted to the actual arithmetic orbit.

These source results identify the required joint estimate and prevent
repeating the generic flow, cone, or square-budget work. No bound for the
actual signed work, proof of the universal kick premise, or map from
the selected CA source or FIB addresses supplying that premise is
established here. The selected-source condition
$I_\psi(A)>-D^*(A)$ therefore remains unchanged and unproved.

The cited Ford–Soundararajan–Zaharescu sequel and its original
[fixed smooth-test supplier](../Weil/fordzaharescu2005zerophases.md)
do identify $-J_q/(2\pi)$ in the ordinate-phase average for each fixed
integer $q>1$. Their fixed-scale expansion does not bound the actual
weighted buffer or the signed state-prime work above. The golden
eigen-scale has no correction density in that theorem; this is a
parameter application, not an FIB-to-Robin estimate.

## Boundary for FIB

The finite certificate is organized by CA exponent profiles and
consecutive-CA interpolation, whereas a FIB family is specified by additive
Zeckendorf windows or congruence classes. A FIB address alone does not
certify the initial prime support or the endpoints used above. Those
conditions are supplied here for the selected critical source by the cited
arithmetic results. The source supplies no estimate for its remaining
signed residual, or for the pointwise signed term in FIB §250. Its finite
verification range remains an external boundary check; repeating that
computation would not advance RH.
