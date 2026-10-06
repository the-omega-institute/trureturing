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
