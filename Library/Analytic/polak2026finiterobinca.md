---
bibkey: polak2026finiterobinca
authors: Robert Polak
year: 2026
title: A Finite Computer-Assisted Verification of Robin's Inequality via Colossally Abundant Profiles, with Exact Prime-Power Residual Dynamics
doi: 10.5281/zenodo.21808589
url: https://doi.org/10.5281/zenodo.21808589
claim: The preprint reports a finite Robin verification and an effective positive full-support core; the core applies at the selected critical clock and, with positive extra-support costs, at arbitrary large GA2 clocks, but does not bound their signed prime-error tails or prove RH.
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

The [effective Nicolas–GA2 application](../ArithSums/nicolas2025comparison.md#an-effective-core-bound-at-the-selected-ga2-source)
retains this same source, minimizer, and clock and supplies

$$
\sqrt A\log A\,D^*(A)>\mathcal E(\log A)
>D_{\rm lb}(A)+0.01.
$$

Its explicit function $\mathcal E$ and uniform comparison use Nicolas's
effective envelope ratio, cancellation of the absent-prime suffix by
the source's GA2 comparisons, and Dusart's published prime-power bound.
All thresholds are paid by the Axler finite stop already used here.
Thus the weaker source-specific condition
$\sqrt A\log A\,I_\psi(A)\ge-\mathcal E(\log A)$ suffices for strict Robin.
That signed condition is unproved. This is a paper-level application,
without a new finite verification, originality claim, or Lean result.

## Application to arbitrary GA2 sources, including extra prime support

The full-support core can also be used at a GA2 integer that is not
known to be GA1, CA, or a global maximizer. Let $N$ be GA2 and put
$A=\log N\ge3$. This application uses its own clock and actual
exponents $a_p=v_p(N)$ throughout.

First, GA2 forces every prime $p\le A$ to divide $N$. Indeed, if such
a prime were absent, multiplicativity would give

$$
\frac{G(Np)}{G(N)}
=\left(1+\frac1p\right)\frac{\log A}{\log(A+\log p)}>1,
$$

because

$$
\log(A+\log p)<\log A+\frac{\log p}{A}
\le\left(1+\frac1p\right)\log A.
$$

The last comparison follows from $p\log p\le A\log A$. This
contradicts GA2. This support argument needs only $A>1$; the stronger
$A\ge3$ ensures that the full-support factor

$$
n_0=\prod_{p\le A}p^{a_p}
$$

contains both 2 and 3 and hence is at least $6>e$, as required for
its logarithmic margin. No assertion that $N$ has no primes above $A$
is needed.

For an occupied prime $p>A$, define its extra-support cost by

$$
\Xi_{p,A}(a)=a\frac{\log p}{A\log A}-\log Z(p^a),
\qquad Z(m)=\frac{\sigma(m)}m,\qquad a\ge1.
$$

These costs are strictly positive. The binomial expansion gives
$Z(p^a)=\sum_{j=0}^ap^{-j}\le(1+1/p)^a$, so

$$
\log Z(p^a)\le a\log(1+1/p)<\frac ap
<a\frac{\log p}{A\log A}.
$$

The final strict comparison uses $p\log p>A\log A$.

Apply Proposition 6 to $n_0$ at $x=A$. Put $A_0=\log n_0$. The
budget transport to the same original $N$ is exactly

$$
\Delta(N)-\Delta(n_0)
=\log\frac{\log A}{\log A_0}
 -\sum_{\substack{p>A\\p\mid N}}\log Z(p^{a_p}),
$$

whereas

$$
B_2(n_0,A)
=\log\frac{\log A_0}{\log A}-\frac{A_0-A}{A\log A}.
$$

Their logarithmic terms cancel, and
$A-A_0=\sum_{p>A,\,p\mid N}a_p\log p$. Thus the transported identity is

$$
\boxed{\displaystyle
\Delta(N)=I_\psi(A)
 +\sum_{p\le A}\Phi_{p,A}(a_p)-C_{\rm pp}(A)
 +\sum_{\substack{p>A\\p\mid N}}\Xi_{p,A}(a_p).}
$$

Taking the existing full-support minimum gives

$$
\Delta(N)\ge I_\psi(A)+D^*(A)
 +\sum_{\substack{p>A\\p\mid N}}\Xi_{p,A}(a_p)
\ge I_\psi(A)+D^*(A).
$$

This is an inequality at arbitrary GA2 sources. Their actual exponents
are not asserted to attain the core minimum. Proper-GA1 deletion
conditions and the selected CA source's equality have not been
transported to this larger class. The stronger Nicolas allowance
requires the separate actual-core argument linked below.

For $A\ge56\,048\,351$, the same Proposition 10 gives
$\sqrt A\log A\,D^*(A)>D_{\rm lb}(A)>1/2$. Caveney–Nicolas–Sondow's
Fact 2 gives $G(N)\ge e^\gamma$, hence $\Delta(N)\le0$. Consequently
every such GA2 source must satisfy

$$
\boxed{\sqrt A\log A\,I_\psi(A)<-D_{\rm lb}(A)<-\frac12.}
$$

The [Nicolas envelope on actual GA2 cores](../ArithSums/nicolas2025comparison.md#the-same-effective-allowance-on-actual-ga2-cores)
uses $Z(N)\le\Sigma(N)$ without CA equality and pays the primorial
suffix even when its primes already divide $N$. For $N\ge N^{(0)}$
and $\log A\ge26$, it strengthens the necessary signed condition to
$\sqrt A\log A\,I_\psi(A)<-\mathcal E(\log A)$. Its bound is on the
whole actual core in the displayed identity, not on $D^*(A)$.

The [published conditional GA2 family](../Arith/caveney2012sacaga.md#the-published-unbounded-ga2-supplier-under-rh-failure)
has $N_i\to\infty$ under RH failure. Therefore an eventual lower bound
$\sqrt A\log A\,I_\psi(A)\ge-\mathcal E(\log A)$ valid at every
sufficiently large GA2 clock would contradict that existing family.
This route would need no effective starting point for the eventual
bound. It does need a proof of the signed bound on these actual clocks;
an arbitrary sequence of favorable real cutoffs is insufficient.

The application reuses the published full-support identity, minimum,
effective core, and conditional infinitude. It supplies the missing
extra-support accounting needed to use that core on the larger source
class. It is a paper-level interface assessment, not a new core estimate,
RH criterion, signed-tail bound, originality claim, or Lean result.
The fixed global source above retains its stronger structural inputs;
this unbounded-source route retains the same unpaid signed tail.

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

For the exact target, take the same actual event $t=\tau_q$ and
$0<h<t$. Let $T_\triangle(t,h)$ be the signed odd-triangular
sum minus smooth forcing defined in (8.35), with
$F=\mathcal P/4+k$. The central event is excluded and endpoint
events have zero weight. Proposition 21, (8.38), pp.25–26, states
that, under the inherited cone
$\mathcal P(t)>0$, $|\mathcal P'(t^-)|<Q(t)$, the post-event
cone condition is equivalent to

$$
\mathcal P(t+h)-\mathcal P(t-h)+T_\triangle(t,h)
                  +2hQ(t)-hJ_q>0.
$$

The secant and signed discrepancy must be controlled jointly.
The source's (8.48)–(8.49), p.27, exhibits the obstruction to
using a small triangular discrepancy alone: for a fixed nonzero
exponential mode $f_\mu(t)=e^{\mu t}$,

$$
T_\mu(t,h)=2e^{\mu t}(\mu h-\sinh(\mu h)),\qquad
\frac{T_\mu(t,h)}{2hf'_\mu(t)}=O_\mu(h^2)\longrightarrow0
\quad(h\to0),
$$

including when $\operatorname{Re}\mu>0$. This is a source-given
mode obstruction, not an actual arithmetic counterexample or an
RH disproof. Relative decay of the triangular remainder leaves
the growing secant uncontrolled. Proving that decay, or first
assuming Proposition 22's RH-conditional secant bound, does not
supply the combined unconditional event inequality.

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

## Exact FIB coordinates for the published forced flow

The source's equation (8.17), p.22, already gives the regularized dynamics

$$
\widehat B''-\frac14\widehat B
=-e^{t/2}+\sum_{q=p^m}J_q\delta(t-\log q),\qquad t>0.
$$

Reuse this equation and its finite right-limit initial data. The following
is a linear coordinate and clock application, not a new event system or
estimate. The existing [FIB composition frame](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
§§3 and 149, has $M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$,
$S=M^3$ and $C=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$.
Here its coordinates are extended to $\mathbb R^2$; a real state in these
coordinates is not thereby the composition of a finite FIB tree.

Remove the known resonant drift, including its derivative:

$$
Y(t)=\widehat B(t)+te^{t/2},\qquad
Y'(t)=\widehat B'(t)+(1+t/2)e^{t/2}.
$$

Then $Y''-Y/4=\sum_qJ_q\delta(t-\log q)$.
Define the simultaneous state transport by

$$
\begin{pmatrix}Y\\Y'\end{pmatrix}
=T\begin{pmatrix}a\\b\end{pmatrix},\qquad
T=\begin{pmatrix}2&1\\0&\sqrt5/2\end{pmatrix},\qquad
a=\frac Y2-\frac{Y'}{\sqrt5},\quad b=\frac{2Y'}{\sqrt5}.
$$

On each open event cell the homogeneous propagator in this frame is

$$
\Phi(s)=\cosh(s/2)I+\frac{2M-I}{\sqrt5}\sinh(s/2).
$$

Its generator is $(2M-I)/(2\sqrt5)$ and its eigenvalues are
$e^{s/2},e^{-s/2}$. For $h=4\log\varphi$,

$$
\Phi(h)=M^2,\qquad \Phi(3h)=M^6=S^2,\qquad
C\Phi(s)C^{-1}=\Phi(-s).
$$

These are substitutions into the existing hyperbolic flow and FIB matrix
identities. $M$ and the single three-position step $S$ have determinant
$-1$, whereas this homogeneous propagator has determinant $1$.
Thus the even steps above match the continuous flow; an odd FIB step
would require an additional orientation reversal. Evaluating $\Phi(h)$
does not assert that an actual event-free cell has length $h$.

The original readout must be transported too:

$$
\widehat B(t)=2a(t)+b(t)-te^{t/2},\qquad
\widehat B'(t)=\frac{\sqrt5}{2}b(t)-(1+t/2)e^{t/2}.
$$

Neither readout is the original FIB quantity $q(a,b)=2a+3b$.
For a passive frame $\mathbf z_k=C^k\mathbf z$, transport the input vector
by $C^k$, the propagator by $C^k\Phi C^{-k}$, and each linear readout row
$\ell$ by $\ell C^{-k}$. The clock and the explicit drift terms are retained.
An active rotation of the state alone changes the forcing direction and
is not an invariance of the given prime trajectory.

### Retain the actual prime inputs in every step

At $\tau_q=\log q$, continuity of $Y$ and the derivative jump $J_q$ give

$$
\Delta\mathbf z_q=\frac{J_q}{\sqrt5}\begin{pmatrix}-1\\2\end{pmatrix},
\qquad \mathbf z=(a,b)^{\mathsf T}.
$$

Taking the initial and final states on the right, the actual fixed-time
update is therefore

$$
\mathbf z(t+h)=M^2\mathbf z(t)+
\sum_{t<\tau_q\le t+h}
\Phi(t+h-\tau_q)\frac{J_q}{\sqrt5}\begin{pmatrix}-1\\2\end{pmatrix}.
$$

For two three-position windows, replace $h$ by $3h$ and $M^2$ by $M^6$;
the entire corresponding event sum remains. This is the finite forced
propagator formula, with every actual prime power and its timing included.
The input term is determined by the prime measure, rather than one of
the five fixed integer translations $0,(1,0),(0,1),(2,1),(1,1)$.

Already the event $q=2$ has first component
$-\log2/\sqrt{10}\in(-1,0)$. Thus this kick is outside $\mathbb Z^2$
in the transported frame. An integral unimodular frame change generated
by $M,J,C$ cannot turn it into an integer vector: its inverse preserves
$\mathbb Z^2$. This obstructs identifying these event maps with the
original integer-coordinate five-pattern translations. A response
computed from a full FIB address can still reconstruct $q$, its event
time and $\Lambda(q)$; that is an additional arithmetic response map,
whose weights and estimates must be retained.

### Read Robin's actual residual at the same clock

For the tail target, retain the existing prime-power cutoff as a scalar
accumulator of this same event history:

$$
\mathcal P_\Pi(t)=\Pi_r(e^t)
=\sum_{p^m\le e^t}\frac1{mp^m},\qquad
\Delta\mathcal P_\Pi(\tau_q)
=\frac{J_qe^{-\tau_q/2}}{\tau_q}.
$$

It is constant between events. The
[existing cross-family signed-tail identity](bhattacharyamartinsimpson2026weightedprimeerrors.md)
and the source's characteristic coordinates give, for $t>0$,

$$
\begin{aligned}
\psi(e^t)&=e^{t/2}[-a(t)+(\varphi-1)b(t)]-\log(2\pi),\\
I_\psi(e^t)&=\frac{\psi(e^t)-e^t}{e^t t}
             -\mathcal P_\Pi(t)+\log t+\gamma.
\end{aligned}
$$

These are transported readouts of already established paper identities,
not a new tail formula. The accumulator keeps the distinct $1/\log q$
factor in the event weight; it can also be computed from the complete
forced history. It is not replaced by the golden quadratic invariant.

At the selected critical source above, under its cited premises, put
$A=\log N$ and **$t=\log A$**, not $t=\log N$.
The exact core application then reads the original Robin margin as

$$
\Delta(N)=\frac{\psi(A)-A}{A\log A}
 -\Pi_r(A)+\log\log A+\gamma+D^*(A).
$$

This retains the same integer, cutoff, prime events and complete weights.
The fixed $h$ grid is a grid of real cutoffs; it constructs no successor
critical integer and supplies no coverage of critical sources by its nodes.
The homogeneous matrix correspondence supplies no sign for this centered
combination; its required lower bound remains the original signed-tail
obligation.

### The transported conservation law retains the centering problem

The existing golden form becomes

$$
Q_F(a,b)=a^2+ab-b^2=\frac{Y^2}{4}-Y'^2.
$$

It is constant during homogeneous propagation, while an event changes it
by $-2J_qY'(\tau_q^-)-J_q^2$. Equations (8.19)–(8.21) identify its actual
value without new spectral assumptions. With $c=\log(2\pi)$ and
$\psi_r(x)=\sum_{q\le x}\Lambda(q)/q$ they give

$$
\begin{aligned}
Y(t)&=e^{t/2}[\psi_r(e^t)+\gamma+1]
       -e^{-t/2}[\psi(e^t)+c],\\
Y'(t)&=\frac12e^{t/2}[\psi_r(e^t)+\gamma+1]
       +\frac12e^{-t/2}[\psi(e^t)+c],\\
Q_F(\mathbf z(t))&=-[\psi_r(e^t)+\gamma+1][\psi(e^t)+c].
\end{aligned}
$$

The factors are positive and nondecreasing, so this actual product is
constant between events and decreases at each event. This is a product
law for the counts, not a positive norm bound for the centered buffer.
At any fixed time, a fixed negative $Q_F$ allows arbitrarily large $|Y|$
on its real level set; subtracting $te^{t/2}$ does not change that fact.
This states the limitation of this scalar invariant on the real carrier,
not a no-go for additional constraints on the actual arithmetic orbit.
In particular Polak's retained energy jump still involves the original
$\widehat B'$ and its signed state-prime work, not just this product.

This coordinate interface exhibits the common expanding and contracting
directions and transports the actual forcing and observer. It supplies
no estimate for the retained input sum or the centered cancellation,
no cone-kick bound, and no proof of $I_\psi(A)>-D^*(A)$ or RH.
It is a paper application with no new Lean declaration or originality
claim.

The [short-interval zero-count supplier](fiori2026shortzerodensity.md)
refines a specified absolute frequency-block allowance in the actual
$I_\psi$ formula, with the source's ordinate thresholds and multiplicities
retained. It supplies no sign for the complete response, does not control
the remaining zeros, and leaves the same critical-source estimate unpaid.

## Earlier support-harmonic route: the envelope is still a target

The author's *Derived Prime-Harmonic Envelope on CA Support*, dated
4 June 2026, is a ten-page
[primary supplement](https://github.com/robopol/Riemann-hypothesis/blob/e61ed0c0707e499f6748efb916bd4bdfbccaa445/papers/Derived_Prime_Harmonic_Envelope_on_CA_Support_en.pdf),
with PDF SHA-256
`6a65507bde32150569791b632866485fe99d86533ffe77104ab1c823408d2a21`.
Its abstract, §§2–8 and Analytic Target 1 on p.9 were inspected.
The [author's scope statement](https://github.com/robopol/Riemann-hypothesis/blob/e61ed0c0707e499f6748efb916bd4bdfbccaa445/README.md)
identifies it as an earlier corrected-status paper, rather than a later
completion of the finite-verification manuscript. It explicitly derives
a required prime-harmonic envelope without proving its infinite-range
validity. Its cited estimates and numerical tables are not independently
audited or rerun here; no Lean verification is claimed.

To keep the support variable distinct from the current $A=\log N$, write

$$
\mathcal A_p(x)=\sum_{p\le x}\frac1p-\log\log x,
$$

and let $B_1$ be the Meissel–Mertens prime constant. On one actual sampled
CA-support block $1<Y<x$, with $\nu=\pi(x)-\pi(Y)>0$, put

$$
\begin{aligned}
H&=\log\frac{\log x}{\log Y},\qquad \mu=H/\nu,\\
C_2(Y,x)&=\sum_{Y<p\le x}\frac1{p(p-1)},\\
D_{\rm br}(Y,x)&=\nu[1-(1+\mu)e^{-\mu}].
\end{aligned}
$$

The source uses a certified lower divisor-deficit envelope to form the
reserve $R^\Theta(x)$, and retains the incoming certified upper ledger
$U(Y)$. Its equations (11)–(16), pp.6–7, already show that the sufficient
first-moment block gate $M_1(Y,x)\le R^\Theta(x)-U(Y)$ is equivalent to

$$
\mathcal A_p(x)\le\mathcal A^\Theta_{\rm req}(Y,x)
:=\mathcal A_p(Y)-C_2(Y,x)
  +e^\mu[R^\Theta(x)-U(Y)+D_{\rm br}(Y,x)].
$$

Equations (19)–(22) therefore express the required upper envelope as

$$
\mathcal A_p(x)-B_1\le
\frac{C^\Theta_{\rm req}(x)}{\sqrt x\log x},\qquad
C^\Theta_{\rm req}(x)
=[\mathcal A^\Theta_{\rm req}(Y,x)-B_1]\sqrt x\log x.
$$

This is the author's existing gate and target, not an unconditional
prime estimate or a newly derived Robin criterion. The required constant
depends on the same block's incoming ledger, prime count, harmonic
remainder and reserve. No fixed lower bound for that constant or
infinite-range certification of the gate is supplied. Replacing the
actual deficit by its smaller analytic lower envelope reduces the
admissible budget, as source equation (20) records. The sampled table
does not establish coverage of all critical sources. Closing a
non-strict block gate also does not by itself certify the final strict
Robin margin; the ledger's transfer and strictness obligations remain.

At the currently selected integer, the support endpoint is
$x=P^+(N)$, whereas the retained signed-tail estimate uses $A=\log N$.
The already-paid condition $P^+(N)<A<P^+_{\rm next}(N)$ does not identify
these cutoffs. Applying this earlier route would require a certified
incoming ledger and block coverage at that same source, together with
the still-missing upper envelope. It does not supply
$I_\psi(A)>-D^*(A)$ by renaming the cutoff. The supplement's $\beta(x)$
is the Euler product $\prod_{p\le x}p/(p-1)$, not the FIB atom
$\beta=\rho(\alpha)$; equality of the symbol supplies no bridge.

## Boundary for FIB

The [golden-field Mertens source](hathi2025numberfieldmertens.md) uses
prime-ideal norms, retains a separate $L(s,\chi_5)$ response and
identifies unit multiples under the ideal observation. Its hypotheses
and cutoff accounting do not supply this ordinary same-source tail bound.

The finite certificate is organized by CA exponent profiles and
consecutive-CA interpolation, whereas a FIB family is specified by additive
Zeckendorf windows or congruence classes. A FIB address alone does not
certify the initial prime support or the endpoints used above. Those
conditions are supplied here for the selected critical source by the cited
arithmetic results. The source supplies no estimate for its remaining
signed residual, or for the pointwise signed term in FIB §250. Its finite
verification range remains an external boundary check; repeating that
computation would not advance RH.

## For sufficiently large supports, the native clock is outside the negative critical-damping regime

The repository's [prime-prefix continuation](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_PRIME_PREFIX.md)
§§441–445 studies a complete normalized first integral, rather than the
complete Robin response. Its existing unique-zero and sign results can be
applied to the clock supplied above; this application is not a new
prime-error estimate or a Lean verification.

Put $z=P$, let $p=P^+$ be the next prime, and use the insertion clock
$L=\log p$. With the notation of §441,

$$
E_P(s)=\prod_{q\le P}(1-q^{-s}),\qquad
C_P=E_P(1)^{-1},\qquad F_P(v)=C_PE_P(1+v/L),
$$

$$
H_P(v)=F_P(v)(1-e^{-v})-v,\qquad
J_P(\sigma)=\int_0^\infty e^{-\sigma v}\frac{H_P(v)}{v^2}\,dv.
$$

The zero-displacement first integral at the actual clock $x=A$ uses
$\sigma_A=\log A/L$: the Laplace change of variable $v=L u$ sends
$e^{-u\log A}$ to $e^{-\sigma_Av}$. Both prefixes in the insertion
comparison retain this same $L$, $A$, and zero displacement.
The already supplied $P<A<p$ and Bertrand's theorem give

$$
1-\frac{\log2}{L}\le\frac{\log P}{\log p}
<\sigma_A<1.
$$

Thus $\sigma_A\to1$ uniformly over $A\in(P,p)$ as $P\to\infty$.
In contrast, §§441 and 445 locate the eventual unique damping zero at
$\sigma_P\sim t_*L^{-C}$, where $C=e^{\gamma_E}>1$ and $t_*>0$.
The existing sign on the upper side of this zero therefore yields,
for all sufficiently large prime supports and every such $A$,

$$
J_P(\sigma_A)>0,\qquad
I_p(\sigma_A)-I_P(\sigma_A)=\frac{J_P(\sigma_A)}{p-1}>0.
$$

This is an eventual statement over eligible parameters. No effective
threshold for the one selected critical integer is supplied here, and
no unbounded sequence of critical maximizers is assumed.

The negative correction in §445 is evaluated at
$\sigma=t_*L^{-C}$. In the same native-clock substitution this corresponds
to $x=\exp(t_*L^{1-C})\to1$, rather than $x=A\in(P,p)\to\infty$.
It therefore cannot be inserted at the actual source by identifying the
two damping parameters.

The normalized $J_P(\sigma)$ here is not the integer-row kernel
$J_A^{\eta_P}(n)$ in the original volume. Insertion changes the Euler
normalization; the other density terms, actual rough Möbius weights,
all integer rows and the complete complement are still required.
Neither insertion sign supplies the sign of
$I_\psi(A)+D^*(A)$ or the missing same-source signed-tail bound.

## Finite-height residual bounds at the actual critical clock

The effective core application above can pay the complete signed residual
on an explicit finite interval. This strengthens a restriction on the
selected global maximizer, not Robin's inequality for every integer in a
larger interval. No zero verification or CA-profile enumeration is repeated.

Keep the same selected source $N$, $A=\log N$, $L=\log A$, and
$T_A=\sqrt A L$. In this paragraph the verified zero height is denoted
$H_0=3\cdot10^{12}$, to distinguish it from $T_A$.
Theorem 1 of Platt–Trudgian,
[arXiv:2004.09765v1](https://arxiv.org/pdf/2004.09765v1), printed p.2,
verifies the stronger height $3000175332800$, and hence that all zeros
with $0<\Im\rho\le H_0$ have real part $1/2$.
The published version is *Bulletin of the London Mathematical Society*
53 (2021), 792–797, DOI [10.1112/blms.12460](https://doi.org/10.1112/blms.12460).
This existing finite-height theorem is an external input; no global RH
premise or verification beyond $H_0$ is added.

### Reusing the complete residual envelope

Polak's §5.3–5.5, printed pp.10–12, equations (5.8), (5.11) and (5.14),
give at any real $A>1$

$$
T_A I_\psi(A)\ge-C_{\rm low}(A)-C_{\rm high}(A),
\tag{F1}
$$

where, putting $c_0=2+\gamma-\log(4\pi)$,

$$
C_{\rm low}(A)=c_0(1+3/L+4/L^2)+\frac{\log(2\pi)}{\sqrt A},
$$

$$
C_{\rm high}(A)\le\sqrt A(1+A^{-1})
\left[(1+1/L)S_2(H_0)+2(1/L+2/L^2)S_3(H_0)\right].
\tag{F2}
$$

Here $S_j(H_0)=\sum_{\Im\rho>H_0}(\Im\rho)^{-j}$ counts positive
ordinates with multiplicity. The source's (5.13), using the published
Hasanalizade–Shen–Wong zero-count bound, supplies the coarser constants

$$
S_2(H_0)<1.48\cdot10^{-12},\qquad
S_3(H_0)<5\cdot10^{-25}.
\tag{F3}
$$

These constants weaken the source's displayed directed enclosures; the
underlying zero-count proof and scalar evaluations are not independently
rerun here. Its functional-equation pairing allows off-line quartets and
all multiplicities in the unverified high part. The positive trivial-zero
contribution is discarded only in the permitted lower-bound direction.
Thus (F1) bounds the entire integral over $[A,\infty)$, including its
unverified-zero contribution. No tail beyond a finite endpoint is omitted.

The original CA-support certificate also needs its nonlinear bridge loss
$C_{B_2}$. At this actual source clock, the already established
$B_2(N,A)=0$ exactly, so that term is absent. Equations (F1)–(F3) do not
use Büthe's support-to-size estimate or assume the source's segmented
monotonicity checks outside their certified range.

### A uniform finite exclusion

Put

$$
X=21\cdot10^{22}.
$$

The Axler finite stop already used above gives $A>K/2>e^{26}$.
The elementary constant bounds $0<c_0<0.05$ and $\log(2\pi)<2$
may be used throughout. For example, $\gamma<0.58$ and
$\log(4\pi)>2.53$ give the upper bound on $c_0$.
The published core application supplies
$T_A D^*(A)>\mathcal E(L)$, with $\mathcal E$ increasing for $L\ge26$
and $\mathcal E(26)>0.65$.
It also gives $\mathcal E(50)>0.75$. An entirely rational lower comparison is

$$
\mathcal E(50)>
2.828-\frac{2.70\cdot1.415}{50}+\frac{6.78}{2500}
-2.00014-\frac{2.67}{4000}-\frac{101}{6\cdot10^{10}}>0.75.
\tag{F4}
$$

For its exponential bounds, the same positive-series inequalities used
above give $e^{25/3}>54^2(25/18)>4000$ and
$e^{25}>54^6(8/3)>6\cdot10^{10}$.
Also $e^{25}<(11/4)^{25}<10^{11}$.

Apply (F2) uniformly on two overlapping clock ranges. On
$e^{26}<A\le e^{50}$, use $L>26$, $\sqrt A<10^{11}$ and
$1+A^{-1}<1.0001$. On $e^{50}\le A\le X$, use $L\ge50$,
$\sqrt A<4.6\cdot10^{11}$ and the same last factor.
The square-root upper bound follows from
$(4.6\cdot10^{11})^2>X$. Equations (F2)–(F3), with
$2(1/26+2/26^2)<0.1$ and $2(1/50+2/50^2)<0.05$, then give

| Actual clock range | $C_{\rm low}(A)$ | $C_{\rm high}(A)$ | Core allowance |
|---|---:|---:|---:|
| $e^{26}<A\le e^{50}$ | $<0.057$ | $<0.155$ | $\mathcal E(L)>0.65$ |
| $e^{50}\le A\le X$ | $<0.054$ | $<0.695$ | $\mathcal E(L)>0.75$ |

For the first low-zero bound, $e^{13}>400000$ bounds its constant term.
For the second, $e^{25}>6\cdot10^{10}$ does so. The high-zero comparisons
are the exact rational inequalities

$$
10^{11}(1.0001)
\left[\frac{27}{26}(1.48\cdot10^{-12})+0.1(5\cdot10^{-25})\right]<0.155,
$$

$$
(4.6\cdot10^{11})(1.0001)
\left[1.02(1.48\cdot10^{-12})+0.05(5\cdot10^{-25})\right]<0.695.
$$

The table therefore covers the entire possible interval
$K/2<A\le X$, not a selection of endpoints. Combining (F1) with the exact
same-source identity $\Delta(N)=I_\psi(A)+D^*(A)$ gives

$$
\boxed{\sqrt A\log A\,\Delta(N)>0.001\qquad(K/2<A\le X).}
\tag{F5}
$$

Such a source would satisfy strict Robin and could not be the selected
counterexample-level global maximizer. Conditional on the cited source
reduction, analytic bounds and finite-verification inputs, a failure of RH
must therefore have its selected least global maximizer at

$$
\boxed{\log N>21\cdot10^{22}.}
\tag{F6}
$$

This bound is on the selected maximizer. It does not bound the least
counterexample, certify every integer below $e^X$, or extend Polak's
all-integer finite theorem. The source's existing all-integer range
already forces this maximizer past $7.1\cdot10^{22}\log10$;
(F6) is a larger source-clock restriction, since $\log10<5/2$.
The derivation of (F5) itself uses the earlier Axler stop, not that stronger
all-integer certificate.

At fixed $H_0$, the available high-zero allowance grows proportionally to
$\sqrt A$; the core allowance tends to a finite constant. Thus this finite
application supplies no unbounded signed-tail estimate or RH proof.
It adds no Lean result and does not certify the cited papers' proofs or
computations.

## Combining finite zero verification with the classical zero-free region

Keep the same selected Robin source, clock $A=\log N$, $L=\log A$,
normalization $T_A=\sqrt A L$, effective core and verified height
$H_0=3\cdot10^{12}$. This application controls the complete unverified
zero contribution with two disjoint height ranges. It uses published
inputs and symbolic outward comparisons; no zero or CA-profile
computation is repeated, and no originality or Lean result is claimed.

### The additional published input

[Johnston–Yang, arXiv:2204.01980v2](https://arxiv.org/pdf/2204.01980v2),
Lemma 2.7, printed p.5, states that for $|t|\ge2$ there are no zeta
zeros in

$$
\beta\ge1-\frac1{R_0\log|t|},\qquad R_0=5.5666305.
\tag{Z1}
$$

Its footnote attributes the classical region to Mossinghoff–Trudgian
and the improved constant to the higher verified height. The versioned
PDF is the one identified in the [existing supplier note](../Weil/johnstonyang2022pnt.md),
SHA-256 `565993a6def48b237a68a92acba604f2c42f99165e0e71e390f8e21a313b74b2`.
The additional lemma and footnote were directly inspected; the external
zero-free proof is not independently certified here. The existing
Platt–Trudgian input supplies the finite verification, rather than a
global RH assumption.

Set $U=10^{16}$. For every actual zero with
$H_0<\gamma\le U$, (Z1), $R_0<6$, $\log U<40$, and the
multiplicity-preserving functional-equation reflection give

$$
\frac1{240}<\beta<1-\frac1{240}.
$$

For $A>1$, convexity on this interval therefore gives

$$
A^{\beta-1}+A^{-\beta}
\le A^{-1/240}+A^{-239/240}=:B(A).
\tag{Z2}
$$

Apply this to the same reflected pairs in Polak's (5.12)–(5.14).
The middle range keeps the improved factor $B(A)$; the range
$\gamma>U$ keeps the original $1+A^{-1}$ factor. Zeros on the
critical line, off-line quartets and every multiplicity are included.
With the same positive-ordinate tails $S_j$, the complete high-zero
allowance satisfies

$$
\begin{aligned}
C_{\rm high}(A)&\le C_{\rm mid}(A)+C_{>U}(A),\\
C_{\rm mid}(A)&\le\sqrt A\,B(A)
\left[(1+1/L)S_2(H_0)+2(1/L+2/L^2)S_3(H_0)\right],\\
C_{>U}(A)&\le\sqrt A(1+A^{-1})
\left[(1+1/L)S_2(U)+2(1/L+2/L^2)S_3(U)\right].
\end{aligned}
\tag{Z3}
$$

The actual ranges in (Z3) are disjoint. The middle-range upper bound
uses the larger full tail $S_j(H_0)$ as a positive envelope; this does
not omit any zero or identify that envelope with the middle-range sum.
Conjugation and reflection carry exactly the same factors as (F2).

### Pay the entire range above the second height

Reuse the full parameter formula in Polak's (5.13), obtained from the
Hasanalizade–Shen–Wong zero-count bound. With
$(a,b,c)=(0.1038,0.2573,9.3675)$, it gives at $U$

$$
S_2(U)\le\frac{\log(U/(2\pi))+1}{2\pi U}
+\frac{2a\log U+a/2+2b\log\log U+b/(2\log U)+2c}{U^2}.
\tag{Z4}
$$

The elementary bounds $2\pi>6$, $32<\log U<40$,
$\log\log U<4$, $a<1/9$, $b<1/3$ and $c<10$ give

$$
S_2(U)<\frac{41}{6U}+\frac{32}{U^2}<7\cdot10^{-16},
\qquad
S_3(U)\le S_2(U)/U<7\cdot10^{-32}.
\tag{Z5}
$$

Here $2<\log10<5/2$ supplies the logarithmic interval, and $e^4>54$
supplies the iterated-logarithm bound. These are scalar outward
comparisons of the published formula, not a new zero count or a
numerical reconstruction of the source's directed constants.

### The complete signed target on a larger source-clock interval

Consider every selected source with

$$
e^{50}\le A\le X_1:=3\cdot10^{23}.
$$

Then $\sqrt A<5.5\cdot10^{11}$, $L\ge50$ and
$1+A^{-1}<1.0001$. The existing positive-series bound
$e^{25}>6\cdot10^{10}$, and $e^t\ge1+t$ for $t\ge0$, give

$$
B(A)\le\frac{24}{29}+e^{-L/2}
<\frac{24}{29}(1.0001).
\tag{Z6}
$$

Use (F3) at $H_0$, (Z5) at $U$, $1+1/L\le1.02$ and
$2(1/L+2/L^2)<0.05$. The two rational comparisons are

$$
(5.5\cdot10^{11})\frac{24}{29}(1.0001)
\left[1.02(1.48\cdot10^{-12})+0.05(5\cdot10^{-25})\right]<0.688,
$$

$$
(5.5\cdot10^{11})(1.0001)
\left[1.02(7\cdot10^{-16})+0.05(7\cdot10^{-32})\right]<0.0004.
$$

Consequently $C_{\rm high}(A)<0.6884$ on the entire stated interval.
The existing $C_{\rm low}(A)<0.054$ and $\mathcal E(L)>0.75$ then
pay the full signed Robin condition, with the exact same-source identity:

$$
\boxed{T_A\Delta(N)>0.75-0.054-0.6884=0.0076>0.007
\qquad(e^{50}\le A\le X_1).}
\tag{Z7}
$$

The lower clock interval $K/2<A\le e^{50}$ was already paid in (F5)
and is reused. Thus, conditional on the same cited source reduction,
core, zero-free region and finite-verification inputs, a failure of RH
must have its selected least global maximizer at

$$
\boxed{\log N>3\cdot10^{23}.}
\tag{Z8}
$$

This improves the existing selected-source restriction
$\log N>21\cdot10^{22}$. It does not constrain the least
counterexample, establish Robin for every integer below $e^{X_1}$,
or extend Polak's all-integer finite theorem. The original height
$H_0$ is still the only verified height; $U$ is only a partition of the
complete unverified-zero contribution.

The unbounded target remains
$T_A I_\psi(A)\ge-\mathcal E(\log A)$ at the same selected source.
For fixed $H_0,U$, (Z3) still permits a high-zero allowance growing as
$A^{1/2-1/240}$, and the part above $U$ retains its $\sqrt A$ factor.
Hence (Z7) supplies no unbounded signed estimate or RH proof. The
separate divisor-order decomposition of the same integral is not
added to this spectral allowance; each representation keeps its own
complete remainder.

## An explicit real-part density allowance for the complete high tail

Keep the conditionally selected least integer $N>5040$ attaining the
global maximum of the Robin ratio, its clock $A=\log N$, $L=\log A$,
and $T_A=\sqrt A L$. This application uses an existing explicit
zero-density estimate to sharpen the entire high-zero allowance at that
same source. It is a paper application, not a new density theorem,
zero verification, all-integer finite Robin theorem or Lean result.
The original unbounded signed target remains unchanged.

### The existing density input at one tabulated real part

[Johnston–Yang, arXiv:2204.01980v2](https://arxiv.org/pdf/2204.01980v2),
Lemma 2.6, equation (2.2), printed p.5, and Appendix B, Table 3,
printed p.20, give at $\sigma_*=0.98=49/50$

$$
N(\sigma_*,t)
\le16.281\,t^{4/75}(\log t)^{76/25}
 +2.231(\log t)^2.
\tag{D1}
$$

Here $N(\sigma,t)$ counts actual zeros with $\sigma<\Re\rho<1$
and $0<\Im\rho<t$, with multiplicity. This is a count in real part,
not the total ordinate count. Use only this tabulated row; no
interpolation or constants at unlisted real parts are assumed.
The versioned PDF and SHA-256 are identified in the
[existing supplier note](../Weil/johnstonyang2022pnt.md).

The paragraph before Lemma 2.6 explicitly replaces the unreliable
critical-line bound used in the older Kadiri–Lumley–Ng calculation and
recomputes the constants. The older constants are not substituted.
Table 3 uses the verified height $H_1=3000175332800$, already cited
above. Keep the weaker cut $H=3\cdot10^{12}$. For $H\le t\le H_1$
the count in (D1) is zero by that same finite-height input; above $H_1$
the density estimate supplies the bound. Its external analytic proof
and table calculation are cited, not independently rerun here.

Since $t\ge H>e$, the outward bounds $16.281<17$, $2.231<3$,
$4/75<1/10$ and $76/25<4$ give the convenient allowance

$$
N(\sigma_*,t)<20t^{1/10}(\log t)^4\qquad(t\ge H).
\tag{D2}
$$

### Pay every zero far from the critical line

Partition the actual positive-ordinate high zeros into two disjoint,
reflection-invariant sets:

$$
\mathcal Z_{\rm bulk}=\{\rho:\Im\rho>H,\ 1/50\le\Re\rho\le49/50\},
\qquad
\mathcal Z_{\rm far}=\{\rho:\Im\rho>H,\
\Re\rho<1/50\text{ or }\Re\rho>49/50\}.
$$

Reflection $\rho\mapsto1-\overline\rho$ preserves ordinate and
multiplicity. Thus the far set has twice the right-hand count in
(D1). For $S_j^{\rm far}=\sum_{\rho\in\mathcal Z_{\rm far}}(\Im\rho)^{-j}$,
Tonelli applied to the positive counting sum gives

$$
S_2^{\rm far}
=4\int_H^\infty\frac{N(\sigma_*,t)}{t^3}\,dt
<80\int_H^\infty t^{-29/10}(\log t)^4\,dt.
\tag{D3}
$$

There are no far zeros at or below $H$, so no starting-endpoint term
is lost. The integral includes the complete infinite height range.
Put $h=\log H$ and $a=19/10>1$. The elementary integral equals

$$
H^{-19/10}
\left(\frac{h^4}{a}+\frac{4h^3}{a^2}+\frac{12h^2}{a^3}
 +\frac{24h}{a^4}+\frac{24}{a^5}\right).
$$

The existing scalar bounds $e^{25}>6\cdot10^{10}$ and $e>8/3$
give $e^{30}>H$, hence $h<30$. The bracket is therefore less than
$30^4+4\cdot30^3+12\cdot30^2+24\cdot30+24=929544<10^6$.
Also $H^{1/10}<20$, since $H<20^{10}$. Consequently

$$
S_2^{\rm far}<\frac{80\cdot10^6\cdot20}{H^2}
<2\cdot10^{-16},\qquad
S_3^{\rm far}\le S_2^{\rm far}/H<7\cdot10^{-29}.
\tag{D4}
$$

These are symbolic outward comparisons of the published density bound,
not a new zero count or numerical certificate.

### Pay the remaining bulk at its own real-part range

For every $A>1$, convexity and functional-equation pairing on the bulk
give

$$
A^{\beta-1}+A^{-\beta}
\le A^{-1/50}+A^{-49/50}=:B_*(A).
$$

Apply the same coefficient-preserving estimate as (F2) separately to
the two reflection-invariant sets. Their complete high allowance obeys

$$
\begin{aligned}
C_{\rm bulk}(A)&\le\sqrt A B_*(A)
 \left[(1+1/L)S_2(H)+2(1/L+2/L^2)S_3(H)\right],\\
C_{\rm far}(A)&\le\sqrt A(1+A^{-1})
 \left[(1+1/L)S_2^{\rm far}+2(1/L+2/L^2)S_3^{\rm far}\right],\\
C_{\rm high}(A)&\le C_{\rm bulk}(A)+C_{\rm far}(A).
\end{aligned}
\tag{D5}
$$

The bulk uses the larger total-ordinate envelopes (F3); the far set
uses (D4). The underlying sets are disjoint, so no contribution is
omitted or counted as an independently realized favorable extremum.
Critical-line zeros above $H$, boundary real parts, conjugates and all
multiplicities remain included. The low allowance is still (F1).

### A stronger restriction on the same selected source

For $3\cdot10^{23}<A\le10^{24}$, the earlier scalar bounds give
$L>50$, $\sqrt A\le10^{12}$ and $1+A^{-1}<1.0001$. Also

$$
B_*(A)<e^{-1}+e^{-49}
<\frac38+\frac1{6\cdot10^{10}}<\frac38(1.0001).
$$

Equations (F3), (D4) and (D5), with $1+1/L<1.02$ and
$2(1/L+2/L^2)<0.05$, give the rational comparisons

$$
C_{\rm bulk}(A)
<10^{12}\frac38(1.0001)
 \left[1.02(1.48\cdot10^{-12})+0.05(5\cdot10^{-25})\right]<0.5662,
$$

$$
C_{\rm far}(A)
<10^{12}(1.0001)
 \left[1.02(2\cdot10^{-16})+0.05(7\cdot10^{-29})\right]<0.000205.
$$

Reuse the same-source core $T_A D^*(A)>\mathcal E(L)>0.75$ and
$C_{\rm low}(A)<0.054$ on $L\ge50$. The complete signed integral
therefore pays the target, with the original exact margin identity:

$$
\boxed{T_A\Delta(N)>0.75-0.054-0.5662-0.000205
=0.129595>0.129\quad(3\cdot10^{23}<A\le10^{24}).}
\tag{D6}
$$

Together with the already paid lower range (Z8), this implies,
conditional on the cited source reduction, core, density and
finite-verification inputs, that a failure of RH must have its selected
least global Robin maximizer at

$$
\boxed{\log N>10^{24}.}
\tag{D7}
$$

This improves (Z8) at the same source. It is not a bound on the least
Robin counterexample or verification for all integers below $e^{10^{24}}$.
The verified height is unchanged. The gain comes from the existing
real-part population bound, not from optimizing the earlier height
handoff or assuming cancellation of the actual error.
For fixed $H$ and this density row, the bulk allowance retains
$A^{12/25}$ growth and the far allowance a $\sqrt A$ factor. Thus
(D6) does not supply the original unbounded signed estimate or prove RH.

## An intermediate-real-part density input extends the same source bound

Retain the same conditionally selected least global Robin maximizer
$N>5040$, $A=\log N$, $L=\log A$, and $T_A=\sqrt A L$.
The original target $T_A I_\psi(A)\ge-\mathcal E(L)$ at every surviving
source clock is unchanged. This application consumes a published
explicit density estimate at $7/8$, a real part not supplied by the
preceding Johnston–Yang table. It improves a finite source-clock
exclusion; it is not a new density theorem, an all-integer Robin
verification, a bound on the least counterexample, or a Lean proof.

### Reuse the published Ingham estimate at its tabulated endpoint

Chourasiya–Simonič, *An explicit form of Ingham's zero density estimate*,
[arXiv:2507.15184v2](https://arxiv.org/pdf/2507.15184v2), revised
30 September 2025, Corollary 1 and Table 1, printed p.2, give

$$
N(\sigma,t)\le B_1t^{3(1-\sigma)/(2-\sigma)}
 (\log t)^{(7-5\sigma)/(2-\sigma)}
 +B_2(\log t)^2+B_3\log t\qquad(t\ge3\cdot10^{12}).
$$

Use only the row $[\sigma_1,\sigma_2]=[27/32,7/8]$, whose
$(B_1,B_2,B_3)$ are $(21.77,6.240,110.7)$. At its included upper
endpoint, and with the existing cut $H=3\cdot10^{12}$, this is

$$
N(7/8,t)\le21.77t^{1/3}(\log t)^{7/3}
 +6.240(\log t)^2+110.7\log t
<22t^{1/3}(\log t)^{7/3}+7(\log t)^2+111\log t.
\tag{E1}
$$

Here the source counts zeros with $\Re\rho\ge\sigma$ and
$0<\Im\rho\le t$, including multiplicities. The verified-height input
is the same $H$ already consumed above. The theorem does not assume
global RH. No constants from its separate Appendix Table 4 or the older
Kadiri–Lumley–Ng tables, and no interpolation in $\sigma$, are used.
The inspected version has 33 pages and PDF SHA-256
`11ebae58b467d14a20835eb732130c2c084f9440ef5e2fdbe38d697ba1e0d261`.
The cited density theorem and its table computation are external inputs;
they are not independently reproved or rerun here.

### Include the entire reflected far tail

Partition the actual positive-ordinate zeros above $H$ into

$$
\mathcal Z_{\rm mid}=\{\rho:\Im\rho>H,\ 1/8<\Re\rho<7/8\},
\qquad
\mathcal Z_{\rm edge}=\{\rho:\Im\rho>H,\
 \Re\rho\le1/8\text{ or }\Re\rho\ge7/8\}.
$$

These are disjoint, reflection-invariant multisets and include the
real-part endpoints in the edge set. Reflection preserves ordinate and
multiplicity. The number of edge zeros up to $t$ is therefore
$2N(7/8,t)$; there are none at or below $H$ by the reused finite-height
verification. Thus, for $S_j^{\rm edge}=\sum_{\mathcal Z_{\rm edge}}
(\Im\rho)^{-j}$, the same positive counting integral as (D3) gives

$$
S_2^{\rm edge}=4\int_H^\infty N(7/8,t)t^{-3}\,dt.
\tag{E2}
$$

All heights to infinity and all multiplicities are retained. The factor
four is the reflection factor followed by the counting-integral factor;
conjugation remains in the coefficient-preserving response estimate.

For the following symbolic outward comparisons, reuse $1<h=\log H<30$.
With $a=5/3$, successive integration by parts, followed by
$u^{-2/3}\le h^{-2/3}$ for $u\ge h$, gives

$$
\begin{aligned}
\int_H^\infty t^{-8/3}(\log t)^{7/3}\,dt
\le H^{-5/3}\left[
\frac{h^{7/3}}a+\frac{7h^{4/3}}{3a^2}
 +\frac{28h^{1/3}}{9a^3}+\frac{28h^{-2/3}}{27a^4}\right]
<2300H^{-5/3}.
\end{aligned}
$$

Indeed $h^{1/3}<4$, $h^{7/3}<3600$, $h^{4/3}<120$ and
$h^{-2/3}<1$ bound the bracket by
$2160+100.8+2.688+0.1344<2300$.
The remaining elementary integrals are

$$
\int_H^\infty t^{-3}(\log t)^2dt
=H^{-2}(h^2/2+h/2+1/4)<466H^{-2},
$$

$$
\int_H^\infty t^{-3}\log t\,dt
=H^{-2}(h/2+1/4)<16H^{-2}.
$$

Since $H^{5/3}>6\cdot10^{20}$, as $3^5>6^3$, equations (E1)–(E2)
therefore give

$$
\begin{aligned}
S_2^{\rm edge}
&<88\cdot2300H^{-5/3}+(28\cdot466+444\cdot16)H^{-2}\\
&<\frac{202400}{6\cdot10^{20}}+\frac{20152}{9\cdot10^{24}}
<3.38\cdot10^{-16},\\
S_3^{\rm edge}&\le S_2^{\rm edge}/H<1.13\cdot10^{-28}.
\end{aligned}
\tag{E3}
$$

These comparisons apply the published bound; no zeros or arithmetic
configurations are newly enumerated.

### Pay the complete response on a larger finite clock interval

The existing coefficient-preserving pairing in (F2) and (D5) applies
separately to these two actual multisets. Convexity gives the midpoint
allowance $A^{-1/8}+A^{-7/8}$ on $\mathcal Z_{\rm mid}$. Retain (F3)
for its total-ordinate reciprocal sums; retain (E3) for the edge set.
Consequently

$$
\begin{aligned}
C_{\rm mid}(A)&\le (A^{3/8}+A^{-3/8})
 [(1+1/L)S_2(H)+2(1/L+2/L^2)S_3(H)],\\
C_{\rm edge}(A)&\le\sqrt A(1+A^{-1})
 [(1+1/L)S_2^{\rm edge}+2(1/L+2/L^2)S_3^{\rm edge}],\\
C_{\rm high}(A)&\le C_{\rm mid}(A)+C_{\rm edge}(A).
\end{aligned}
\tag{E4}
$$

For $10^{24}<A\le10^{30}$, reuse $L>50$,
$1+1/L<1.02$, and $2(1/L+2/L^2)<0.05$.
Here $\sqrt A\le10^{15}$, $1+A^{-1}<1.0001$, and

$$
A^{3/8}+A^{-3/8}<2.0001\cdot10^{11}.
$$

The last comparison uses $A^{3/8}\le10^{45/4}<2\cdot10^{11}$
from $10^{1/4}<2$, and $A^{-3/8}<1$.
Using the same (F3) constants gives

$$
C_{\rm mid}(A)
<2.0001\cdot10^{11}
 [1.02(1.48\cdot10^{-12})+0.05(5\cdot10^{-25})]<0.302,
$$

$$
C_{\rm edge}(A)
<10^{15}(1.0001)
 [1.02(3.38\cdot10^{-16})+0.05(1.13\cdot10^{-28})]<0.345.
\tag{E5}
$$

Reuse the unchanged low allowance $C_{\rm low}(A)<0.054$ and
same-source core $T_AD^*(A)>\mathcal E(L)>0.75$ for $L\ge50$.
The original signed margin, with its complete infinite high tail, satisfies

$$
\boxed{T_A\Delta(N)>0.75-0.054-0.302-0.345=0.049
\quad(10^{24}<A\le10^{30}).}
\tag{E6}
$$

Together with the already paid lower clocks (D7), this implies,
conditional on the cited source reduction, core, density and
finite-verification inputs, that RH failure must place the same least
integer attaining the global Robin-ratio maximum over $n>5040$ at

$$
\boxed{\log N>10^{30}.}
\tag{E7}
$$

The clock bound is a factor $10^6$ above (D7), with no increase in the
verified zero height. It is not a least-counterexample bound or an
all-integer verification below $e^{10^{30}}$. The gain uses a published
intermediate-real-part density theorem, rather than a finer rounding of
(D6). For this fixed cut, (E4) still retains $A^{3/8}$ and $\sqrt A$
growth. The original unbounded same-source signed target, the all-size
FIB matrix positivity claim and RH remain unproved. This application is
paper-level and makes no mathematical originality or Lean-certification
claim.

## Keeping the real-part weights in the complete high-zero tail

Keep the same conditionally selected least integer $N>5040$ attaining the
global Robin-ratio maximum, its actual clock $A=\log N$, $L=\log A$,
and $T_A=\sqrt A L$. The preceding density application retains only a
single horizontal cutoff. The following application integrates the
published density bound against the actual real-part weight instead.
It consumes the same finite-height verification and Corollary 1 of
Chourasiya–Simonič, rather than a new density theorem or zero computation.
The original unbounded signed-tail target remains unchanged.

### A uniform supplier on the needed real parts

Corollary 1 and Table 1 of the already identified
[arXiv:2507.15184v2](https://arxiv.org/pdf/2507.15184v2), printed p.2,
apply on each of their **closed** intervals $[\sigma_1,\sigma_2]$.
Their rows covering $3/4\le\sigma\le1$ have
$B_1<47$, $B_2<10$, and $B_3<168$. Taking these larger constants is
therefore a uniform consequence of the finitely many published rows;
it does not interpolate constants from pointwise asymptotic estimates.
For $t\ge H:=3\cdot10^{12}$, put

$$
d(\sigma)=\frac{3(1-\sigma)}{2-\sigma},\qquad
q(\sigma)=\frac{7-5\sigma}{2-\sigma}=2+d(\sigma),\qquad
a(\sigma)=2-d(\sigma)=\frac{1+\sigma}{2-\sigma}.
$$

The supplied count, with actual multiplicities and the source's
$\beta\ge\sigma$, $0<\gamma\le t$ convention, obeys

$$
N(\sigma,t)<47t^{d(\sigma)}(\log t)^{q(\sigma)}
                 +10(\log t)^2+168\log t
\quad(3/4\le\sigma<1).
\tag{W1}
$$

The cited density proof and table are external premises, not independently
rerun or kernel-certified. Their finite-height premise is exactly the
one already used above, not RH at unbounded height.

### A count for each reflected far tail

Define the actual positive-ordinate multiset

$$
\mathcal F_\sigma=\{\rho=\beta+i\gamma:\gamma>H,
                       \ \beta\ge\sigma\text{ or }\beta\le1-\sigma\},
\qquad
F_2(\sigma)=\sum_{\rho\in\mathcal F_\sigma}\gamma^{-2}.
$$

For $\sigma\ge3/4$ the two real-part conditions are disjoint.
Reflection preserves ordinate and multiplicity; there are no members
at or below $H$. The same counting-integral identity used in (E2) gives

$$
F_2(\sigma)=4\int_H^\infty N(\sigma,t)t^{-3}\,dt.
\tag{W2}
$$

Set $h=\log H<30$. On this range $7/5\le a(\sigma)\le2$
and $2\le q(\sigma)\le13/5$. Three integrations by parts, with
$u^{q-3}\le h^{q-3}$ for $u\ge h>1$, give

$$
\begin{aligned}
\int_H^\infty t^{d-3}(\log t)^q\,dt
&\le H^{-a}\left[
\frac{h^q}{a}+\frac{qh^{q-1}}{a^2}
 +\frac{q(q-1)h^{q-2}}{a^3}
 +\frac{q(q-1)(q-2)h^{q-3}}{a^4}\right]\\
&<5500H^{-a}.
\end{aligned}
\tag{W3}
$$

For the last comparison use $30^{3/5}<8$ and hence
$h^q<7200$, $h^{q-1}<240$, $h^{q-2}<8$, and $h^{q-3}<1$.
The bracket is bounded by

$$
\frac{7200}{7/5}+\frac{(13/5)240}{(7/5)^2}
 +\frac{(104/25)8}{(7/5)^3}
 +\frac{312/125}{(7/5)^4}<5500.
$$

Reuse the earlier integrals
$\int_H^\infty t^{-3}(\log t)^2dt<466H^{-2}$ and
$\int_H^\infty t^{-3}\log t\,dt<16H^{-2}$.
Equations (W1)–(W3) give the complete, uniform allowance

$$
F_2(\sigma)<1040000H^{-a(\sigma)}+30000H^{-2}.
\tag{W4}
$$

Every height to infinity is included in (W2)–(W4).

### Integrate the actual weight rather than its worst endpoint

Put

$$
Q_A(\sigma)=A^{\sigma-1/2}+A^{1/2-\sigma},\qquad
B_j(A)=\sum_{\gamma>H}
 \frac{A^{\beta-1/2}+A^{1/2-\beta}}{\gamma^j}\quad(j=2,3).
$$

These sums contain every actual positive-ordinate zero with multiplicity.
For each zero, layer integration of the increasing function
$Q_A(1/2+|\beta-1/2|)$, clipped below at $3/4$, gives

$$
B_2(A)\le Q_A(3/4)S_2(H)
                  +\int_{3/4}^1 Q_A'(\sigma)F_2(\sigma)\,d\sigma.
\tag{W5}
$$

Tonelli applies to the nonnegative integrand. Its endpoint convention
agrees with (W2); individual real-part endpoints do not change the
integral. This keeps the same zeros in the density count and in the
response. Reflection and conjugation are not counted as independent
favorable configurations.

Since $Q_A'(\sigma)\le LA^{\sigma-1/2}$, (W4)–(W5) yield

$$
B_2(A)<2A^{1/4}S_2(H)
 +1040000L\int_{3/4}^1 A^{\sigma-1/2}H^{-a(\sigma)}\,d\sigma
 +30000H^{-2}(\sqrt A-A^{1/4}).
\tag{W6}
$$

The coefficient-preserving estimate (5.12) in Polak's source, before
its worst-real-part convexity bound, and multiplicity-preserving
reflection give

$$
C_{\rm high}(A)\le(1+1/L)B_2(A)
                  +2(1/L+2/L^2)B_3(A).
\tag{W7}
$$

The factor from conjugation is already present in $B_j$: summing the
two reflected weights equals twice the sum of $A^{\beta-1/2}$ over
positive ordinates. Also $B_3(A)\le B_2(A)/H$. Thus (W7) bounds the
same complete high part of (F1), rather than an extra reserve added
to that part.

### A larger finite source-clock exclusion

Consider $10^{30}<A\le10^{34}$. Elementary logarithm bounds
$2.302<\log10<2.303$ and $1.098<\log3<1.099$ give

$$
50<L<78.4,\qquad 28.7<h<30.
$$

For $r=2-\sigma>0$, arithmetic–geometric mean gives

$$
\begin{aligned}
\log\left(A^{\sigma-1/2}H^{-a(\sigma)}\right)
&=\tfrac32L+h-Lr-3h/r\\
&\le\tfrac32L+h-2\sqrt{3Lh}<-18.
\end{aligned}
\tag{W8}
$$

For the strict scalar comparison, $\tfrac32L+h-2\sqrt{3Lh}$ is
increasing in $L$ and decreasing in $h$ on the stated rectangle.
At $(L,h)=(78.4,28.7)$ it is less than $-18$, since
$82.15^2=6748.6225<6750.24=3(78.4)(28.7)$.
The logarithm bounds can be obtained by the positive series
$\log v=2\sum_{k\ge0}z^{2k+1}/(2k+1)$, $z=(v-1)/(v+1)$,
with its geometric remainder bound; no prime or zero data are used.

Reuse $S_2(H)<1.48\cdot10^{-12}$.
Here $A^{1/4}<4\cdot10^8$, $\sqrt A\le10^{17}$, and
$e^{18}>20^6=64000000$: the last inequality follows already from
$\sum_{k=0}^{8}3^k/k!>20$. Consequently (W6) gives

$$
\begin{aligned}
B_2(A)
&<2(4\cdot10^8)(1.48\cdot10^{-12})
 +\frac{1040000(78.4)}{4(64000000)}
 +\frac{30000\cdot10^{17}}{9\cdot10^{24}}\\
&<0.321.
\end{aligned}
\tag{W9}
$$

Equations (W7) and $B_3\le B_2/H$ give
$C_{\rm high}(A)<1.021(0.321)<0.33$.
Reuse the unchanged $C_{\rm low}(A)<0.054$, strict core
$T_AD^*(A)>\mathcal E(L)>0.75$, and exact same-source margin.
The complete signed integral therefore yields

$$
\boxed{T_A\Delta(N)>0.75-0.054-0.33=0.366>0.36
\qquad(10^{30}<A\le10^{34}).}
\tag{W10}
$$

Together with the previously paid lower clocks (E7), and conditional
on the same cited source reduction, core, density and finite-verification
inputs, RH failure must place the selected least global Robin maximizer at

$$
\boxed{\log N>10^{34}.}
\tag{W11}
$$

This is a $10^4$ extension of the selected-source clock restriction;
it is not a least-counterexample bound or an all-integer verification
below $e^{10^{34}}$. The verified zero height is unchanged.
The gain keeps the real-part dependence of the existing density estimate
through (W5), rather than using one worst real-part weight for a whole
far set. It does not assume cancellation or infer the actual signed
error from a lower bound on its magnitude.

For fixed $H$, the upper allowance in (W6) is not bounded as
$A\to\infty$; its displayed last term alone grows as $\sqrt A$.
This is growth of the available allowance, not a lower bound on the
actual high-zero contribution. The original same-source signed target,
all-size FIB matrix positivity, and RH remain unproved.
This is a paper-level application of existing results, without a
mathematical originality claim, new zero computation, or Lean certification.


## Keep the coupled logarithmic exponent in the complete density tail

Retain the same actual zero multisets, source clock $A=\log N$,
$L=\log A$, verified height $H=3\cdot10^{12}$ and
$h=\log H$ as in (W1)–(W7). The published density estimate has the
exact relation

$$
q(\sigma)=4-a(\sigma),\qquad
\frac75\le a(\sigma)\le2,\qquad
2\le q(\sigma)\le\frac{13}5
\quad(3/4\le\sigma<1).
$$

Keeping this relation in the already established integral (W3) gives
a smaller complete high-zero allowance. This is an application of the
same published density rows and finite-height verification, not a new
density theorem, a repetition of their proofs or a new zero computation.
The density and verification inputs remain external premises; no
mathematical originality or Lean certification is asserted.

### A reciprocal-square bound retaining both exponents

Factor the bracket in the first inequality of (W3) as

$$
\frac{h^q}{a}
\left[1+\frac q{ah}+\frac{q(q-1)}{a^2h^2}
 +\frac{q(q-1)(q-2)}{a^3h^3}\right].
$$

Since $h>28$, its square bracket is less than

$$
1+\frac{13}{196}+\frac{104}{38416}
 +\frac{312}{7529536}<1.07.
$$

Thus the leading term of the same reflected count integral (W2) is
at most $4(47)(1.07)H^{-a}h^q/a$, and
$4(47)(1.07)/(7/5)<144$. Reuse the unchanged logarithmic-error
integrals in (W3)–(W4). They give

$$
\boxed{
F_2(\sigma)<144H^{-a(\sigma)}h^{q(\sigma)}+30000H^{-2}
=144h^4(Hh)^{-a(\sigma)}+30000H^{-2}.}
\tag{X1}
$$

All ordinates above $H$ through infinity are included, with the same
analytic multiplicities and reflection convention. The equality on
the right uses the joint identity $q=4-a$, rather than combining
independently attained exponent endpoints.

Insert (X1) in the existing actual-weight layer integral (W5), with
$Q_A'(\sigma)\le LA^{\sigma-1/2}$. Then

$$
\boxed{
\begin{aligned}
B_2(A)<{}&2A^{1/4}S_2(H)
 +144Lh^4\int_{3/4}^1
    A^{\sigma-1/2}(Hh)^{-a(\sigma)}\,d\sigma\\
&+30000H^{-2}(\sqrt A-A^{1/4}).
\end{aligned}}
\tag{X2}
$$

The source's coefficient estimate remains precisely (W7), including
$B_3\le B_2/H$. No response is discarded or counted as an additional
reserve. Compared with (W6), (X2) retains the logarithmic exponent of
each real-part layer rather than paying its worst value throughout
the strip. This changes the allowance, not the actual signed sum.

For fixed $H$, (X2) still has an allowance growing with $A$; its last
term alone grows like $\sqrt A$. That is not a lower bound on the
actual response. The complete unbounded same-source Robin condition
and RH remain unproved.


### A further finite restriction of the same selected Robin source

Assume RH fails and the same cited source-reduction, strict-core,
density and finite-verification inputs hold. Let $N>5040$ be the
least integer attaining the global Robin-ratio maximum. Consider

$$
10^{34}<A=\log N\le10^{36},\qquad L=\log A.
$$

The existing logarithm bounds $2.302<\log10<2.303$ and
$1.098<\log3<1.099$ give

$$
78<L<83,\qquad 28<h<30.
$$

Put $s=h+\log h$. In fact
$h>12(2.302)+1.098=28.722>27$, so

$$
s>12(2.302)+4(1.098)=32.016>32.
$$

Also $s<34$, since $h<30$ and $\log30<4$; the latter follows
from the already used $e^4>54$.

For $r=2-\sigma>0$, the same arithmetic–geometric mean comparison
as (W8), now with the coupled logarithmic factor, gives

$$
\begin{aligned}
\log\left(A^{\sigma-1/2}(Hh)^{-a(\sigma)}\right)
&=\tfrac32L+s-Lr-3s/r\\
&\le\tfrac32L+s-2\sqrt{3Ls}<-22.
\end{aligned}
\tag{X3}
$$

The expression after the inequality increases in $L$ and decreases
in $s$ on $78<L<83$, $32<s<34$. At $(L,s)=(83,32)$ it is
$156.5-2\sqrt{7968}<-22$, because
$89.25^2=7965.5625<7968$. Thus (X3) holds uniformly over the
whole real-part integral, rather than only at a chosen layer.

Reuse $S_2(H)<1.48\cdot10^{-12}$, $e^{18}>64000000$ from (W9),
and $e^4>54$ from the Nicolas core comparison. These give
$e^{22}>3456000000$. Also $A^{1/4}\le10^9$ and
$\sqrt A\le10^{18}$. Equation (X2) now supplies

$$
\begin{aligned}
B_2(A)
&<2(10^9)(1.48\cdot10^{-12})
 +\frac{144(83)(30^4)}{4(3456000000)}
 +\frac{30000\cdot10^{18}}{9\cdot10^{24}}\\
&=0.00296+0.7003125+\frac1{300}<0.707.
\end{aligned}
\tag{X4}
$$

All comparisons are elementary rational bounds applied to the existing
complete density integral. No primes, CA profiles or zero ordinates
are newly enumerated or verified.

### Pay the full signed margin with the same strict core

The explicit Nicolas allowance $\mathcal E(L)$ in (G7) of the
[comparison note](../ArithSums/nicolas2025comparison.md) has a sufficient
strict bound on this range. Reuse $1.414<\sqrt2<1.415$,
$\log2<0.70$, $e^{13}>400000$, and the decreasing exponential
error terms already used there. For $L\ge78$, discard only the
positive $6.78/L^2$ term to obtain

$$
\mathcal E(L)>
2.828-\frac{2.7(1.415)}{78}-2.00014
 -\frac{2.67}{400000}-\frac{157}{400000^3}>0.778.
\tag{X5}
$$

The last denominator uses $e^{39}>(400000)^3$, and
$156+5/78<157$. The actual strict core remains
$T_AD^*(A)>\mathcal E(L)$, with $T_A=\sqrt A L$, at this
same integer, optimizer and clock.

Reuse (W7), $B_3\le B_2/H$, and its previously paid factor $1.021$.
Equation (X4) gives

$$
C_{\rm high}(A)<1.021(0.707)<0.722.
$$

The unchanged complete low allowance is $C_{\rm low}(A)<0.054$;
it retains the verified head and the elementary terms of the original
signed formula (F1). Consequently the original integral obeys
$T_AI_\psi(A)>-0.776> -\mathcal E(L)$ on this selected-source
range. Together with the strict core, it gives

$$
\boxed{
T_A\Delta(N)>0.778-0.054-0.722=0.002
\qquad(10^{34}<A\le10^{36}).}
\tag{X6}
$$

This pays the original sufficient signed-tail condition on the stated
finite clock interval. It includes every zero above $H$ through
infinity; reflection, conjugation and real-part weights keep their
original multiplicities. The high allowance is used once, on the
same actual zero multiset as the margin, rather than added to a
separately optimized reserve.

Together with (W11), and conditional on the same cited source
reduction, strict core, density and finite-verification inputs, RH
failure must place the selected least global Robin maximizer at

$$
\boxed{\log N>10^{36}.}
\tag{X7}
$$

This strengthens the selected-source clock restriction by a factor
of $100$. It is not a least-counterexample bound or an all-integer
Robin verification below $e^{10^{36}}$. The verified zero height,
external density theorem and source-selection hypotheses are unchanged.
The gain comes from retaining $q=4-a$ inside the density integral,
not from a new zero-density theorem or an assumption of cancellation.

The full unbounded signed-tail condition at the selected source and
RH remain unproved. In particular the growing fixed-$H$ allowance
in (X2) is still present; the finite interval cannot be extrapolated
to all clocks. This is a paper-level application of existing results,
without a mathematical originality claim or Lean certification.

## A uniform obstruction for adaptive positive-law absolute budgets

The [GAK/GAD whole-law transport](../ArithSums/nicolas2025comparison.md#project-application-density-weighted-order-nine-transport-reaches-3e47)
explains why a fixed positive-variance law has a growing transport
allowance. The following application also covers arbitrary laws chosen
anew at each clock. It concerns the existing certificate that multiplies
one common tail-damping bound by a whole zero-mass allowance, then adds
a nonnegative variance allowance. It does not lower-bound the actual
signed response or the actual transport.

The suppliers are the classical convexity and logarithm bounds, the
global cosine inequality, the existing FV4 actual-zero count and the
GAK23/GAD2 certificate. The cosine inequality is already available as
[`Real.one_sub_sq_div_two_le_cos`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean).
Their proofs are not reconstructed as new general theorems. This is an
ordinary application of those results, without a literature-priority
claim or Lean certification of the application.

### One fixed actual zero constrains every admissible positive law

Keep $H=3\cdot10^{12}$ and put $a_0=99/100$, $b_0=101/100$.
For each $A$, allow any positive probability law $\mu_A$ with
$a_0\le C\le b_0$ and $\mathbb E C=1$. Write

$$
V_A=\mathbb E(C-1)^2,\qquad
H_{\mu_A}(s)=\mathbb E C^{s-1},\qquad
q_A\ge\sup_{\substack{\rho\text{ actual}\\|\Im\rho|>H}}
                   |H_{\mu_A}(\rho)|.
\tag{VDB1}
$$

All actual nontrivial zeros are retained, with their original real
parts. No regularity of $A\mapsto\mu_A$ or $A\mapsto q_A$ is needed.
In particular $q_A$ need only dominate the actual discrete zero set;
no continuum of fictitious zero locations is substituted for it.

To choose one fixed member of that set, reuse
[FV3–FV4's existing zero-count application](../Zeros/lagarias2007li.md#an-explicit-positive-budget-above-c).
Take the least Fibonacci number $c>H$. Its predecessor is at most $H$,
so $c\le2H$, and $c$ is the sum of two adjacent positive Fibonacci
numbers. Thus the original Fibonacci-cut hypotheses are preserved.
FV4 supplies $N_+(2c)-N_+(c)>0$, hence an actual nontrivial zero
$\rho_*=\beta_*+i\gamma_*$ with

$$
H<c<\gamma_*\le2c\le4H,\qquad 0<\beta_*<1.
\tag{VDB2}
$$

This uses the same Hasanalizade–Shen–Wong counting premise, not a new
zero computation. The zero is fixed before choosing any of the laws;
no assumption that it is off the critical line is made.

Convexity and the exact mean give $\mathbb E C^{\beta_*-1}\ge1$.
On the full support,
$|\log C|\le|C-1|/a_0$ and $C^{\beta_*-1}\le a_0^{-1}$.
Apply $\cos x\ge1-x^2/2$ inside this same expectation:

$$
\begin{aligned}
\Re H_{\mu_A}(\rho_*)
&\ge\mathbb E C^{\beta_*-1}
 -\frac{\gamma_*^2}{2}
       \mathbb E[C^{\beta_*-1}(\log C)^2]\\
&\ge1-\frac{\gamma_*^2}{2a_0^3}V_A.
\end{aligned}
$$

Every integral exists on the compact positive support. Norm
nonnegativity and (VDB1) therefore imply

$$
q_A\ge(1-K_*V_A)_+,\qquad
K_*:=\frac{\gamma_*^2}{2a_0^3}>0.
\tag{VDB3}
$$

The same positive law supplies both its variance and its response at
this actual zero. Multiplicity does not alter this pointwise constraint.

### Minimize the complete certificate jointly in damping and variance

Let $\mathcal M(A)\ge0$ be the retained whole-tail mass allowance.
Suppose the sufficient certificate keeps the GAK23 nonnegative costs,
so in particular its numerical upper allowance obeys

$$
\mathcal U_A(\mu_A,q_A)
\ge\mathcal M(A)q_A+\frac{13}{25}\sqrt A\,V_A.
\tag{VDB4}
$$

The coefficient $13/25$ is the existing $.52$ transport coefficient;
its additional $2\eta_0(A)$, the head, coefficient-remainder factors
and elementary allowances are nonnegative. They may be retained or
increased without weakening this lower bound on the certificate.

Put $z=K_*V_A$ and $D_A=(13/25)\sqrt A/K_*$. For $0\le z\le1$,
the right side of (VDB4) is at least
$\mathcal M(A)(1-z)+D_Az$, a convex combination of its two endpoints.
For $z\ge1$ it is at least $D_Az\ge D_A$. Hence, for every law and
every certified $q_A$ simultaneously,

$$
\mathcal U_A(\mu_A,q_A)
\ge\min\left\{\mathcal M(A),
          \frac{26a_0^3}{25\gamma_*^2}\sqrt A\right\}
\ge\min\left\{\mathcal M(A),
          \frac{13a_0^3}{200H^2}\sqrt A\right\}.
\tag{VDB5}
$$

Thus whenever the fixed-$H$ mass allowance $\mathcal M(A)$ tends
to infinity, the infimum of this complete certificate over all the
admissible positive laws also tends to infinity. This includes laws
whose variance tends to zero and laws whose certified damping changes
with $A$; it is not only a statement about a fixed convolution order.

### An explicit restriction for the rationalized GAD allowance

For a concrete consumer take the rationalized GAD2 supplier, with
$L=\log A$, $h=\log H$ and $\alpha(\sigma)=(1+\sigma)/(2-\sigma)$:

$$
\begin{aligned}
\mathcal M_H(A)={}&
2\frac{37}{25\cdot10^{12}}A^{1/4}
 +144Lh^4\int_{3/4}^{1}
       A^{\sigma-1/2}(Hh)^{-\alpha(\sigma)}\,d\sigma\\
&+30000H^{-2}(\sqrt A-A^{1/4}).
\end{aligned}
\tag{VDB6}
$$

This is the existing full density upper envelope after replacing
$S_2(H)$ by its cited rational upper bound. Its explicit positive
baseline is part of the chosen allowance, not a lower bound for the
actual mass $B_2(A)$. The original (W5) baseline instead uses
$Q_A(3/4)S_2(H)$; it is not assigned this rational numerical floor.

For $A\ge256H^4=20736\cdot10^{48}$, all terms in (VDB6) are
nonnegative and

$$
\mathcal M_H(A)\ge\frac{888}{25},\qquad
\frac{13a_0^3}{200H^2}\sqrt A
\ge\frac{26}{25}\left(\frac{99}{100}\right)^3
=\frac{12613887}{12500000}>1.
$$

Consequently every certificate satisfying this specified contract has

$$
\mathcal U_A(\mu_A,q_A)>1>Q_R
\qquad(A\ge256H^4),
\tag{VDB7}
$$

where $Q_R$ is the unchanged GAK37 common reserve. Arbitrarily changing
the narrow positive law cannot make the sufficient test
$\mathcal U_A<Q_R$ hold on an unbounded range under this contract.

This conclusion does not reverse GAK23's directed transport inequality.
It lower-bounds the retained upper-allowance expression, not the actual
transport, signed zero sum or Robin margin. It does not restrict a
sharper mass supplier, a changing height, frequency-dependent joint
weights, a signed or broad-support law, or an estimate coupled to the
same integer's actual defect. The already paid GPP higher-power transport
and BPY xi-law constructions remain available. The unpaid root-scale
same-source signed estimate and RH remain open.

## A finite log-free density row lowers the complete upper envelope

Chiara Bellotti, *An explicit log-free zero density estimate for the
Riemann zeta-function*,
[arXiv:2405.12545v2](https://arxiv.org/pdf/2405.12545v2), Theorem 1.1
on printed pp.2–3 and Table 2 on printed p.28, supplies

$$
N_>(\sigma,t)\le C t^{B(1-\sigma)},\qquad
C=6.23\cdot10^6,\quad B=2.152,
\quad 0.985\le\sigma<1,\quad e^{500}<t\le e^{1000}.
\tag{Y1}
$$

Here $N_>$ uses the source's strict conditions $\beta>\sigma$ and
$0<\gamma<t$, with the zero-count multiplicities. Its analytic proof
and table computation remain external inputs. The publication locator
is [J. Number Theory 269 (2025), 37–77](https://doi.org/10.1016/j.jnt.2024.10.001);
the cited interface is the pinned preprint, without an assertion that
its text equals the published version. Only this table row is used.

Let $D_I(\sigma,t)$ denote the existing right side of (W1), and put
$\alpha=197/200$, $u=e^{500}$, $v=e^{1000}$. Define

$$
M(\sigma,t)=
\begin{cases}
\min\{D_I(\sigma,t),Ct^{B(1-\sigma)}\},
 &\alpha\le\sigma<1,\ u<t\le v,\\
D_I(\sigma,t),&\text{otherwise}.
\end{cases}
\tag{Y2}
$$

Both inputs bound the same actual strict count, so $N_>\le M$
on the whole original domain. For the strict reflected sum, (W2)
gives $F_2^>(\sigma)\le4\int_H^\infty M(\sigma,t)t^{-3}\,dt$.
The strict height endpoints do not change this counting integral.
Strict real-part endpoints do not change (W5)'s layer integral;
zeros on $\beta=\alpha$ retain their layers below $\alpha$.
Reflection and every multiplicity keep the original factor $4$.

On the rectangle in (Y1),
$B<3/(2-\sigma)$, $q(\sigma)\ge2$, and
$C<47\cdot500^2=11.75\cdot10^6$ imply
$Ct^{B(1-\sigma)}<D_I(\sigma,t)$.
For $A>1$, reuse $Q_A$ and $S_2(H)$ from (W5) and define

$$
U_M(A)=Q_A(3/4)S_2(H)
 +4\int_{3/4}^1 Q_A'(\sigma)
       \int_H^\infty M(\sigma,t)t^{-3}\,dt\,d\sigma.
\tag{Y3}
$$

Let $U_I$ be the same expression with $D_I$ in place of $M$.
These envelopes are finite at each $A>1$, and (W5) gives
$B_2(A)\le U_M(A)$. Their exact difference is

$$
U_I(A)-U_M(A)
=4\int_\alpha^1 Q_A'(\sigma)
       \int_u^v\bigl[D_I(\sigma,t)-Ct^{B(1-\sigma)}\bigr]
                    t^{-3}\,dt\,d\sigma>0.
\tag{Y4}
$$

Finally, (W7) and $B_3\le B_2/H$ preserve the original coefficient
factors and give, with $L=\log A$,

$$
C_{\rm high}(A)\le
\left[1+\frac1L+\frac2H\left(\frac1L+\frac2{L^2}\right)\right]U_M(A).
\tag{Y5}
$$

Outside the finite rectangle, the original Ingham envelope still
extends to infinity. Thus this is a complete high-part allowance,
with no discarded heights, real parts or multiplicities. The low
and elementary contributions, selected integer, its clock and the
strict core are unchanged. Equation (Y4) improves explicit upper
envelopes; it supplies no cancellation theorem, certified numerical
Robin margin, new source-clock exclusion or uniform bound as
$A\to\infty$. The complete selected-source signed target and RH
remain unproved. This reuses Bellotti and (W2), (W5), (W7), without
reproving a density theorem or claiming Lean verification.

## A seven-eighths ceiling in the complete positive-law Robin transport

The [Nicolas comparison's GAD application](../ArithSums/nicolas2025comparison.md#project-application-density-weighted-order-nine-transport-reaches-3e47)
already pays the complete signed response on
$8\cdot10^{46}<A\le3\cdot10^{47}$. Its density integral extends to
real part one. The following application adds the separately recorded
[ASC1 seven-eighths ceiling](../ArithSums/nicolas2025comparison.md#project-application-a-seven-eighths-ceiling-lowers-the-actual-sample-cut)
to that whole-law transport. The changed input removes real-part layers
above $7/8$, permitting a lower-variance order-seven law. Under these
inputs the new all-integer slab is

$$
3\cdot10^{47}<A=\log n\le6\cdot10^{47}.
\tag{CDR1}
$$

The premises are all five primary analytic inputs in
[GAK section 1](../ArithSums/nicolas2025comparison.md#1-exact-theorem-and-premises),
the same unrestricted reserve and response identities GAK36–GAK39,
the Chourasiya–Simonič density rows supplying (W1), and the additional
condition

$$
\beta\le7/8\qquad\text{for every actual nontrivial zeta zero}.
\tag{CDR2}
$$

The pinned supplier for (CDR2) is
[`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean).
It is an external analytic premise: its complete transitive proof closure
has not been compiled or independently certified here. The project and
upstream Lean toolchains remain distinct. GAK's five primary inputs and
the density bound alone do not supply (CDR2). No primary proof, finite
zero computation or density theorem is repeated. This is a source-
conditional ordinary application, without Lean certification or a
literature-priority claim.

### Truncate the actual real-part population before bounding it

Keep $H=3\cdot10^{12}$, $h=\log H$, $s=\log(Hh)$, $L=\log A$,
$\alpha(\sigma)=(1+\sigma)/(2-\sigma)$ and the same positive-
ordinate mass $B_2(A)$ from (W5), including analytic multiplicities.
Reflection gives $\beta\ge1/8$ from (CDR2). Hence the actual reflected
count $F_2(\sigma)$ in (W2) is zero for $\sigma>7/8$.
Zeros on $\beta=7/8$ or $1/8$ remain included: their layers below the
endpoint are retained, and a single integration endpoint has zero
measure. Tonelli's existing nonnegative layer identity (W5), followed
by (X1), therefore gives

$$
\begin{aligned}
B_2(A)<{}&2A^{1/4}S_2(H)
 +144Lh^4\int_{3/4}^{7/8}
    A^{\sigma-1/2}(Hh)^{-\alpha(\sigma)}\,d\sigma\\
&+30000H^{-2}(A^{3/8}-A^{1/4}).
\end{aligned}
\tag{CDR3}
$$

The last term is truncated along with the principal density term.
This uses the same actual zero population at all heights above $H$;
it does not extend the finite-height critical-line verification.

For $f(\sigma)=L(\sigma-1/2)-s\alpha(\sigma)$,

$$
f'(\sigma)=L-\frac{3s}{(2-\sigma)^2}
 \ge L-\frac{64}{27}s>0\qquad(3/4\le\sigma\le7/8).
$$

Reuse GAD's rational logarithm bounds $L>107$, $28<h<29$ and
$s<32.1$; the larger lower endpoint in (CDR1) preserves them. Integrating
the derivative bound toward $7/8$ gives

$$
\int_{3/4}^{7/8}e^{f(\sigma)}d\sigma
 <\frac{A^{3/8}(Hh)^{-5/3}}{L-(64/27)s},\qquad
\frac{L}{L-(64/27)s}<\frac{45}{13}<\frac72.
\tag{CDR4}
$$

For uniform rational enclosures put $r=8\cdot10^{23}$. Then
$r^2>6\cdot10^{47}$ and $A^{1/4}<10^{12}$. The exact power
comparisons

$$
r^3<(8.5\cdot10^{17})^4,\qquad
(84\cdot10^{12})^5>(1.6\cdot10^{23})^3
$$

give $A^{3/8}<8.5\cdot10^{17}$ and
$(Hh)^{5/3}>1.6\cdot10^{23}$. Inserting these and the reused
$S_2(H)<37/(25\cdot10^{12})$ into (CDR3) yields

$$
\begin{aligned}
B_2(A)&<\frac{74}{25}
 +144\frac72\,29^4\frac{8.5\cdot10^{17}}{1.6\cdot10^{23}}
 +\frac{30000(8.5\cdot10^{17})}{H^2}\\
&=\frac{2276049253}{1200000}<1900.
\end{aligned}
\tag{CDR5}
$$

The GAD5 reflection/conjugation identity is unchanged:
$B_2(A)=\sum_{|\gamma|>H}m_\rho A^{\beta-1/2}/\gamma^2$.
It already pays both ordinate signs. There is no further factor of two.

### Consume the smaller mass with the complete order-seven law

Use the existing GAK finite equal-width log-uniform construction with
$k=7$ and width $\delta=51/(20H)$, keeping its exact whole-law
normalization $\mathbb EC=1$. Put

$$
x=\delta^2,\qquad M_*=(1-14x)^{-1},\qquad
V_*=\frac{7x}{3-10x},\qquad q=\frac{219}{1000}.
\tag{CDR6}
$$

GAK3–GAK6 give positive denominators, full support in $(.99,1.01)$,
$\mathbb EC^{-1}\le M_*$ and $\operatorname{Var}C\le V_*$.
GAK41/GAK47's normalized scalar base is independent of $k$:

$$
q_*:=\frac{7/32+(20/51)\delta/(1-x)}{1-x}<q.
$$

Consequently the actual complex response satisfies
$|H_C(\rho)|<q^7$ throughout $|\gamma|>H$, for all actual real
parts. The head retains its bound $M_*$. The full integrated
coefficient $F_A$, its GAK12 remainder and the absolute exchange
in GAK15 are retained. In particular the tail needs no extra $M_*$.

The complete allowances, using the same remainder factors as GAD6, are

$$
\begin{aligned}
U_h&=\frac{108}{107}\frac{527}{500}\frac1{20}M_*,\\
U_t&=\frac{108}{107}\frac{10001}{10000}q^7(1900),\\
U_v&=\frac{260001}{500000}rV_*,\qquad
U_e=\frac{5M_*}{10^{23}}.
\end{aligned}
\tag{CDR7}
$$

The GAK26 estimate $\eta_0(A)<10^{-6}$ and $\sqrt A>10^{23}$
hold on the entire slab. Thus GAK23 gives the original signed integral,
with its cutoff atoms, directed transport and full elementary response,

$$
-T_AI_\psi(A)<U_h+U_t+U_v+U_e<\frac{161}{200},
\qquad T_A=\sqrt A L.
\tag{CDR8}
$$

Sufficient exact rational comparisons are
$U_h<.0532$, $U_t<.0464$, $U_v<.7014$ and
$U_e<6\cdot10^{-23}$; their sum is less than $161/200$.
The gain in high-zero mass is used to reduce smoothing order and hence
variance cost. No zero-phase cancellation or favorable sample is assumed.

### Keep the unrestricted reserve and each integer's own defect

For every integer in (CDR1), take its own $A=\log n$ and
$\lambda=1/(AL)$. Reuse exactly GAK37 and GAK39, including its
nonnegative unrestricted-price defect $d_A(n)$ and
$Q_R=67838284064811/83593750000000$. Since
$Q_R-161/200>1/200$, (CDR8) implies, under all stated premises,

$$
T_A\left[\gamma+\log L-\log\frac{\sigma(n)}n\right]
 >\frac1{200}+\frac{L}{(L+2)^3}+T_Ad_A(n)>0.
\tag{CDR9}
$$

Here $\gamma$ denotes Euler's constant, not a zero ordinate. This is
the strict Robin inequality for each integer in the slab. No CA or
maximizer selection is required and no defect is set to zero. The earlier
GAD slab is reused at its original scope; (CDR9) does not establish Robin
for every smaller integer or give a least-counterexample bound.

For this fixed $H$ and positive-variance law, the transport allowance
still grows with $\sqrt A$. The additional strip premise therefore
does not close the unbounded signed estimate or prove RH.

The [existing rational certificate, extended with the capped scenario](https://github.com/the-omega-institute/trureturing-experiments/tree/a0f4aeb56177d88284985f07f51cf4c32d2f19b3/experiments/robin-density-transport-3e47)
checks the logarithm and power enclosures, support, normalization and
complete numerical allowances. Its baseline numerical result is preserved.
These finite checks do not certify the external analytic premises or the
complete inference in Lean.


## Fixed-degree transport retains a positive complete first-layer budget

The named inputs XLR, GPC, KTO, HLD, GMW and CPW below refer to
the existing [Nicolas comparison card](../ArithSums/nicolas2025comparison.md)
and its response, transport and localization applications.

This application keeps the single degree $k=1$ in GPC, KTO and HLD.
It reuses their full-response and root-tail estimates before their
moving-degree limits. The delivered consumer retains the nonzero
higher-layer term and the same original integer. No new xi-law,
prime-distribution theorem, literature priority or Lean certification
is claimed.

Keep $A=\log n$, $L=\log A$, $T_A=\sqrt A L$ and the BPY law $\mu$
from XLR1. Write

$$
m=\pi/3,\qquad h(s)=2m^{1-s}\xi(s),\qquad
Q(z)=(1-z)(1-z/m),
$$

$$
\nu_*=(1+1/m)\mu-\mu^{*2}/m,\qquad
b=h(1/2),\qquad q_*=Q(b),\qquad H_*=1-q_*.
\tag{FDW1}
$$

This is exactly GPC1 at $k=1$. Its mass, first clock moment and
inverse first moment are one, and its Mellin transform vanishes at
every actual nontrivial zero. Every fixed real absolute moment is
finite by GPC2. Keep the same clamp, two correction atoms and KTO
observation kernel:

$$
\chi_A(c)=\max\{c,e/A\},\qquad
\delta_A=\int c^{-1}\,d(\chi_A)_\#\nu_*(c)-1,
$$

$$
\eta_A=(\chi_A)_\#\nu_*-2\delta_A(\delta_1-\delta_2),\qquad
\omega_A(E)=\int\kappa_{A,c}(E)\,d\eta_A(c).
\tag{FDW2}
$$

For large $A$, KTO3 gives $\delta_A=O(A^{-3})$. KTO7--KTO8
therefore retain exact mass and exact price mean
$\int\lambda(Av)d\omega_A=\lambda(A)$, where
$\lambda(x)=1/(x\log x)$. GPC5 applies to this fixed degree, since
its first assertion is uniform over $1\le k\le\kappa\log A$.
The finite-cutoff estimates in its proof, with fixed moments, give
$T_A|J_{\nu_*}^\psi(A)|=O(A^{-1/2})$; the bounded responses at the
two correction atoms cost $O(A^{-5/2}L)$. Thus the complete transported
$\psi$ response is $o(1/T_A)$, with no zero-height or clock tail omitted.

The quantitative transport in KTO9--KTO10 and HLD5 now has bounded
weighted logarithmic moments. Their $O(L^{-3/4})$ allowances become
$O(L^{-1})$: on $c\ge A^{-1/2}$ the error is the same
$L^{-1}c^{-1/2}(1+|\log c|)$ times a fixed absolute moment; below
that cut the full bounded, clamped integrand costs $O(A^{-3/2}L)$
after root normalization. Consequently, before discarding any term,

$$
T_A\int R(Av)\,d\omega_A(v)=c_RH_*+O(L^{-1}),\qquad
c_R=2(\sqrt2-1),
$$

$$
T_A\mathcal J_2(A)=2\sqrt2q_*+O(L^{-1}).
\tag{FDW3}
$$

Here $\mathcal J_2$ is HLD6's complete actual higher-pressure gap.
It is not $o(1/T_A)$ for a fixed degree when $q_*\ne0$.
Absolute integration and the entire kernel tail are the same as in
KTO and HLD; no positive-power moment is assigned to $\omega_A$.

Let $D_{1,A}(n)$ be the $\omega_A$ average of the complete actual
first-layer defect, including occupied and absent primes at all primes.
Let $G_{2,A}(n)=d_2(n,\lambda(A))\ge0$ be the original integer's
complete higher-layer defect at its own price, as in HLD7.
Exact mass and price give $D_{2,A}(n)=G_{2,A}(n)+\mathcal J_2(A)$.
KTO's same-integer account, with FDW3 retained, yields

$$
\boxed{\displaystyle
T_A\Delta(n)=T_A[D_{1,A}(n)+G_{2,A}(n)]
+c_*+O(L^{-1}),\qquad c_*=c_R+2q_*.}
\tag{FDW4}
$$

The remainder is uniform over original integers at their own $A$.
The coefficient $2q_*$ combines the higher-layer gap with the
transported reserve: $c_R(1-q_*)+2\sqrt2q_*=c_R+2q_*$.
It would be incorrect to retain the reserve gain while deleting the
higher-layer contribution.

XLR2 gives $1\le b\le\sqrt m$. The elementary quadratic minimum
and $1<m<22/21$ give

$$
-\frac1{1848}<q_*\le0,\qquad
c_*>\frac{207}{250}-\frac1{924}>\frac{33}{40}>0.
\tag{FDW5}
$$

The rational square comparison $(707/500)^2<2$ pays the bound on
$\sqrt2$. This positive constant is a complete fixed-degree budget,
not a lower bound for the signed first-layer defect in FDW4.


### A polylogarithmic window for the unpaid first-prime account

Use the uniform real-order constant $C_m\ge1$ already supplied by
GMW1, and put, for sufficiently large $A$,

$$
B_*=8(C_m+1),\qquad
Y_A=\frac{A}{(L+2)^{B_*}},\qquad
P_A=A(\log L+2)^{B_*}.
\tag{FDW6}
$$

These are exactly CPW1 and GMW2 with the fixed degree $k=1$.
The source, clamp and observer remain FDW1--FDW2. Define
$G_{\mathrm{low},A}(n)$ by CPW7 at the new $Y_A$; it is the
nonnegative own-price cost of the same integer's missing primes
$p\le Y_A$. Define $C_A(n)$ and $D_{\mathrm{far},A}(n)$ by
averaging the complete actual first-layer defect on, respectively,
$Y_A<p\le P_A$ and $p>P_A$. Both occupied and absent primes are
included, with the original occupation pattern.

The order-$L$ negative-moment calculation CPW3--CPW6 gives

$$
D_{\mathrm{low},A}(n)=G_{\mathrm{low},A}(n)+O(\rho_A),\qquad
\rho_A=4e^{-(3C_m+4)L\log(L+2)},\qquad
T_A\rho_A=o(L^{-1}).
\tag{FDW7}
$$

All low primes lie above their original-price activation, by CPW4.
For source clocks below $2Y_A/A$, CPW5 pays the inverse-price factor;
for every other source clock the entire low-prime hinge integral is
zero. Thus this estimate includes the clamped clocks and the complete
infinite observation-kernel tail, not just a source mass bound.

For the upper cut, use GMW3 at the growing real order $t=\log L$.
Its whole weighted clock-tail allowance, including GMW5's
additional factor, is
$O((1+\log L)\exp[-(C_m+2)(\log L)\log(\log L+2)])
=o(L^{-1})$.
The actual activation formula JPT5 and the complete prime-tail
calculation GMW4--GMW8 therefore give

$$
U_A:=\int\sum_{p>P_A}\log p\,(r_p-\lambda(Av))_+
       \,d\omega_A(v)
=\frac{\beta_1}{L}(1+o(1))>0,
\qquad r_p=\frac{\log(1+1/p)}{\log p}.
\tag{FDW8}
$$

Here $\beta_1>0$ is ACP3's fixed node-$1$ slope. The Gamma comparison
uses $k=1$, $Z=\log P_A=L+O(\log\log L)$ and $\Gamma(1)=1$.
The effective-PNT and activation errors are $o(L^{-1})$; no claim
that this far-sector error is root-small is made.
The scalar hinge identity and exact mass and price keep the actual
occupied-prime correction:

$$
D_{\mathrm{far},A}(n)=U_A+
 \sum_{\substack{p>P_A\\p\mid n}}(\lambda(A)-r_p)\log p
\ge U_A.
\tag{FDW9}
$$

Each correction is nonnegative because $p>P_A>A$ and
$r_p<\lambda(p)<\lambda(A)$. All infinite prime sums after
observation are absolutely integrable by JPT3's complete-pressure
majorant; the same proof uses only fixed source moments here.

Substitute the exact disjoint decomposition
$D_{1,A}=D_{\mathrm{low},A}+C_A+D_{\mathrm{far},A}$ into FDW4.
The resulting full original-integer account is

$$
\boxed{\begin{aligned}
T_A\Delta(n)={}&T_A\bigl[C_A(n)+D_{\mathrm{far},A}(n)
 +G_{\mathrm{low},A}(n)+G_{2,A}(n)\bigr]\\
&+c_*+O(L^{-1}).
\end{aligned}}
\tag{FDW10}
$$

No actual higher layer, low-prime baseline or occupied far prime is
omitted. The undecided first-prime window has endpoints
$A/(\log A+2)^{B_*}$ and $A(\log\log A+2)^{B_*}$, with a fixed
exponent $B_*$. This is narrower than the growing-degree window;
it does not assert that either endpoint divided by $A$ tends to one.
There is no numerical common threshold because $C_m$ and the reused
asymptotic inputs have not been made jointly effective here.

A sufficient still-unproved joint estimate is
$T_A[C_A(n)+D_{\mathrm{far},A}(n)]\ge-33/40$ eventually for all
original integers. FDW5, FDW10 and the two nonnegative baselines would
then give strict eventual Robin; lower finite scales would still need
their own coverage. The exact far account in this condition cannot be
replaced by its leading term with an $o(L^{-1})$ error: that allowance
is larger than the required root scale. ACC's actual-integer
cancellation obstruction must still be respected.

For any actual own-price zero-defect source, all scalar nonnegative
baseline defects vanish. Combining FDW10 with the original
$\Delta(n)=I_\psi(A)+R(A)$ then gives

$$
T_A[C_A(n)+D_{\mathrm{far},A}(n)]
=T_AI_\psi(A)-2q_*+O(L^{-1}).
\tag{FDW11}
$$

Thus the changed root constant is compensated in the same signed
first-layer account. It is not an additional physical reserve or a
proved bound for that account. A FIB address may supply this same
integer and its verified arithmetic data; the address alone supplies
no sign in FDW10. The complete joint comparison and RH remain open.

## Actual strict CA sources have a root-small own-price higher baseline

This application continues the fixed-degree account FDW1--FDW11 on
one specified actual integer family. It reuses the complete higher
inventory and defect in [HLD1--HLD8](../ArithSums/nicolas2025comparison.md#a-root-small-debit-for-the-complete-actual-higher-layer-defect),
the actual strict products in ACC, and their unconditional own-clock
comparison [NP0](../ArithSums/erdosnicolas1975repartition.md#actual-strict-ca-products-at-their-own-size-price).
The added consumer bounds this family's nonnegative higher baseline,
which FDW10 retained without an upper estimate. No new prime theorem,
literature priority, Lean certification or Robin sign is claimed.

For sufficiently large real $x$, keep the actual strict product

$$
N_x=\prod_p p^{a_p(x)},\qquad
 a_p(x)=\#\{j\ge1:r_{p,j}>\lambda(x)\},\qquad
A=\log N_x,\quad L=\log A,\quad T_A=\sqrt A L,
$$

$$
\lambda(u)=\frac1{u\log u},\qquad
K(u)=-\lambda'(u),\qquad
\varepsilon_x=\frac{|A-x|}{x}
=O(e^{-a\sqrt{\log x}})=o(1)
\tag{HCB1}
$$

for the same positive constant $a$ as NP0. Every layer and every
simultaneous activation is retained; equality layers are excluded in
$N_x$. In particular $A\in[x/2,2x]$ eventually. No CA optimizer is
substituted for an arbitrary integer: this paragraph concerns the
literal family $n=N_x$.

Write $\mathcal A_2(u)$ for HLD1's complete active mass over $j\ge2$.
HLD3 and its actual second-cutoff input give
$\mathcal A_2(u)=O(\sqrt x)$ uniformly on $u\in[x/2,2x]$.
The higher layers of $N_x$ already optimize the higher pressure at
$\lambda(x)$, including the zero cost of any equality layer. Thus
$d_2(N_x,\lambda(x))=0$ and $L_2(N_x)=\mathcal A_2(x)$ in HLD7.

On this compact price interval only finitely many actual layers can
activate. Apply the finite pressure differentiation already used in
[NPC5](../ArithSums/erdosnicolas1975repartition.md#keep-the-exact-inventory-between-both-prices)
to HLD1's higher pressure. It gives, in either endpoint ordering,

$$
\begin{aligned}
G_{2,A}(N_x)&=d_2(N_x,\lambda(A))\\
 &=\int_x^A[\mathcal A_2(u)-\mathcal A_2(x)]K(u)\,du\\
 &=\int_{\min(x,A)}^{\max(x,A)}
       |\mathcal A_2(u)-\mathcal A_2(x)|K(u)\,du\ge0.
\end{aligned}
\tag{HCB2}
$$

The strict endpoint convention changes neither the pressure integral
nor a layer's zero benefit at equality. Monotonicity of the complete
inventory justifies the absolute-value expression. Its integrand
contains all higher exponent layers, rather than only the square layer.
The uniform inventory bound and
$K(u)=O(1/(x^2\log x))$ on this interval imply

$$
0\le G_{2,A}(N_x)\le
\frac{C|A-x|}{x^{3/2}\log x},\qquad
\boxed{\quad 0\le T_AG_{2,A}(N_x)\le C'\varepsilon_x=o(1).\quad}
\tag{HCB3}
$$

These constants are uniform over all sufficiently large real $x$,
including activation events. The conclusion requires only $A\sim x$,
not NPC2's stronger $|A-x|=o(x^{3/4})$. It does not bound the
complete own-price defect, whose first-layer part can remain larger.

Retain precisely the fixed source and observation FDW1--FDW2.
FDW3 and exact mass and price give the actual observed higher part

$$
T_AD_{2,A}(N_x)=2\sqrt2q_*+
 O(L^{-1}+\varepsilon_x).
\tag{HCB4}
$$

The nonzero signed higher-pressure term is still present. HCB3
controls the original nonnegative baseline; it does not make the
signed observer positive or turn HCB4 into an $o(1)$ assertion.

The BPY law is nondegenerate: its mean is one and its inverse first moment
is $m>1$. Strict convexity therefore gives
$b=\mathbb E C^{-1/2}>1$, while XLR2 gives $b\le\sqrt m<m$.
Consequently $q_*=(1-b)(1-b/m)<0$, and HCB4 implies
$T_AD_{2,A}(N_x)\to2\sqrt2q_*<0$ over the whole strict CA family.
This is a negative signed average of the actual nonnegative
higher-defect integrands. It determines neither the full signed
defect nor the Robin margin.

### The generating-price account retains the complete tangent compensation

Use the unchanged FDW6 cuts at the original source's own $A=\log N_x$.
Since $A\sim x$, eventually $2Y_A<x<P_A$.
CPW4's actual activation inequality puts every $p\le Y_A$ in $N_x$.
Every prime factor of $N_x$ is less than $x$, by ACC's first-layer
activation bracket. Hence, for this same integer and observer,

$$
G_{\mathrm{low},A}(N_x)=0,\qquad
D_{\mathrm{far},A}(N_x)=U_A.
\tag{HCB5}
$$

The second equality retains FDW8's exact infinite pressure integral;
its occupied-prime correction is zero because $P_A>x$.
Combining FDW10, HCB3 and HCB5 gives the full central-plus-far account

$$
T_A\Delta(N_x)=T_A[C_A(N_x)+U_A]+c_*+
 O(L^{-1}+\varepsilon_x),\qquad c_*=c_R+2q_*.
\tag{HCB6}
$$

This is a consequence for the whole unconditional strict CA family,
not merely for the own-price zero-defect sources of FDW11.
No low baseline, occupied far prime or actual higher layer is left
unaccounted for.

The [existing generating-price identity](../ArithSums/nicolas2025comparison.md#project-application-actual-monotone-layers-at-a-shorter-successor)
uses the nonnegative tangent loss

$$
\Gamma_x(A)=\log\log x+\lambda(x)(A-x)-\log\log A\ge0,
$$

$$
\Delta(N_x)=I_\psi(x)+R(x)-\Gamma_x(A).
\tag{HCB7}
$$

This is the same concavity term as
[TC.4](../ArithSums/erdosnicolas1975repartition.md#an-explicit-thin-layer-capacity-for-the-same-arbitrary-host),
with opposite sign to its $\kappa_x(A)$; it is not a new pressure
identity. Keep it exact even when its root normalization is large.
KTO1 and $A/x=1+O(\varepsilon_x)$ give
$T_AR(x)=c_R+O(L^{-1}+\varepsilon_x)$.
Consequently HCB6--HCB7 imply

$$
\boxed{\displaystyle
T_A[C_A(N_x)+U_A]
=T_A[I_\psi(x)-\Gamma_x(A)]-2q_*
 +O(L^{-1}+\varepsilon_x).}
\tag{HCB8}
$$

In particular the changed fixed-degree constant is compensated on
all these actual integers, even when their own-price defects do not
vanish. The far integral cannot be replaced here by
$\beta_1/L(1+o(1))$: that relative error is not root-small.
The signed prime integral and the exact tangent loss still need a
joint estimate.

For the root-scale comparison, suppose on a specified unbounded
family that $|A-x|/x^{3/4}\to\ell<\infty$.
The existing curvature of $\log\log x$ in TC.4 gives
$T_A\Gamma_x(A)\to\ell^2/2$.
Together with the owned own-price coefficient NPC9--NPC11,
$T_A d_A(N_x)\to\ell^2/2$, the exact two margin accounts yield

$$
\begin{aligned}
T_A[I_\psi(A)-I_\psi(x)]&=-\ell^2+o(1),\\
T_A\Delta(N_x)&=T_AI_\psi(x)+c_R-\ell^2/2+o(1),\\
T_A[C_A(N_x)+U_A]&=T_AI_\psi(x)-\ell^2/2-2q_*+o(1).
\end{aligned}
\tag{HCB9}
$$

Indeed subtract the accounts at $A$ and $x$; the difference of their
root-normalized reserves tends to zero. The positive own-price
coefficient and the negative generating-price coefficient therefore
belong to compatible observations of the same source. Keeping the
positive defect while leaving the prime integral unchanged would
miss the full $-\ell^2$ transport.

A sufficient signed premise on this specified family is
$\liminf T_AI_\psi(x)>-c_R+\ell^2/2$; it would imply eventual
strict Robin there. Neither that premise, a uniform full-family
root bound, nor the central-plus-exact-far lower bound is supplied.
The formula with finite $\ell$ does not cover larger displacements;
HCB8 retains their exact tangent loss. RH and strict Robin for every
integer above 5040 remain unresolved. These are paper applications
of the cited inventory, pressure, curvature and prime-count inputs,
with no Lean certification or literature-priority claim.


## A truncated Fourier law in the same complete finite consumer

The [truncated Fourier-law application](../Estimation/trureturing2026bandlimitedrobin.md),
BFR1--BFR10, reuses GAK's original five analytic premises and unrestricted
reserve. Its positive mean-normalized law has a second-moment allowance
near $10/H^2$ and complete complex tail response below $10^{-26}$ at
$H=3\cdot10^{12}$. The same full transport then pays strict Robin for
each integer in $8\cdot10^{46}<\log n\le17\cdot10^{47}$, retaining its
own nonnegative price defect. This extends the finite slab without
CDR2's additional $7/8$ ceiling or a new density premise. It is a
paper-level conditional application, not a new zero verification,
Lean certification, least-counterexample bound or unbounded RH estimate.
