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
