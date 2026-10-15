# Recursive relational observation: stability of the original-control instrument

This volume studies approximation for exactly the canonical optimal
double-wall instrument (OC.19)–(OC.19b) in
[Original-Control Instrument Boundaries](https://github.com/the-omega-institute/trureturing/blob/17ef08588473220560adc4a7fb0775a5f7f238a1/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md#52-ideal-all-prefix-limit).
That immutable supplier owns the instrument, its optimality and chronological
completion. The results here concern a conditional inverse estimate and two
explicit stability obstructions. They are ordinary mathematical proofs,
without new Lean verification or a physical implementation claim.

The same prescribed operation, positive source, clock and initial input are
compared throughout. A whole marked probability law, a complete quantum
instrument and one acquired stopped record are different data. None of the
estimates supplies access to a whole law. This source does not classify
terminal instruments or propose a minimum observer memory.

## 1. Source, controls and complete output metrics

**Definition 1.1 (fixed original source).** Fix $0<Z<1$, $r=1-Z$,
$c=r/2$ and $a\in(0,c)$. This is the double wall $b=(c,c,Z)$ of
`FiniteRectangleTransport.ValidBase`. Modes are ordered $(0,1,2,3,13)$;
index $4$ means mode $13$. The probabilities and signed weights are

$$
p(k)=(k,c-k,Z,c-k,k),\qquad
w(k)=\tfrac12(1,0,0,0,1)-\frac{k}{r}(1,1,0,1,1).
\tag{IS.1}
$$

For fixed finite $T\geq0$, a control $\gamma=(k,\chi)$ means precisely
an original control with $k(0)=a$: both real coordinates are continuous,
$0<k(t)<c$, $\chi$ has finite variation, and either both coordinates are
absolutely continuous or they have the supplied finite-piecewise-$C^1$
regularity with continuous rates on each closed piece. The latter alternative
also implies absolute continuity by integration and finite telescoping.
There is no common partition-size, speed or variation bound unless stated.
Each individual path has a positive compact support margin.

Let $\xi(t)=\chi(t)-\chi(0)$ and

$$
H_i(t)=\int_0^t w_i(k(u))\chi'(u)\,du,\qquad
\lambda(t)=\frac{(k'(t))_+}{k(t)}
             +\frac{(-k'(t))_+}{c-k(t)},\qquad
S(t)=\exp\left(-\int_0^t\lambda(u)\,du\right).
\tag{IS.2}
$$

All these integrals exist. In particular $S(t)>0$ and $S$ is nonincreasing.
The source retains the real lift: $\xi=2(H_0-H_1)$ and $H_2=0$.
For a based loop $\xi(T)=2\pi m$, $m$ is an arbitrary signed integer.
The theorems allow the entire original class; the counterexamples select
zero-phase, zero-winding members without deleting other sectors.

**Definition 1.2 (the specified completion).** Use only the supplier's
instrument with live space $\mathbb C^5$ and absorbing state $f$:

$$
\begin{aligned}
K_t&=\sqrt{S(t)}\operatorname{diag}_i
       \left(\sqrt{\frac{p_i(k(t))}{p_i(a)}}e^{-iH_i(t)}\right),\\
g_i(t)&=\lambda(t)-(\log p_i(k(t)))',\\
J_i(t)&=\sqrt{g_i(t)}\,|f\rangle\langle i|K_t.
\end{aligned}
\tag{IS.3}
$$

Here $g_i\geq0$ almost everywhere. The terminal output retains either
success with unnormalized live state $K_T\rho K_T^*$, or exact first
failure time $t$, original mode $i$, and absorbing successor, with CP
density $J_i(t)\rho J_i(t)^*$. Every Borel time event is retained.
Failure has only its supplied stopped continuation. No hidden environment
port, phase read, old-prefix quantum read or programme-identity register is
adjoined to this output. If another task retains such fields, they remain
additional fields and the comparisons here do not erase them.

The full control indexes a prescribed mathematical instrument programme.
An executed run that fails has only its live prefix and then $f$; its
unvisited live tail is not executed. The law-level height inverse below
identifies the programme's time function, not the unexecuted tail of a
single acquired stopped trajectory.

The supplier's full unknown initial family has diagonal $p(a)$:

$$
\Psi_{a,\beta,m}=\sqrt Z\,e_2+e^{-i\beta}
 \left(\sqrt{2a}\,U_++(-1)^m\sqrt{2(c-a)}\,U_-\right),
\quad \beta\in\mathbb R,\ m\in\mathbb Z,
\tag{IS.4}
$$

where $U_+=(e^{-i\theta_0}e_0+e^{-i\theta_4}e_4)/\sqrt2$ and
$U_-=(e^{-i\theta_1}e_1+e^{-i\theta_3}e_3)/\sqrt2$, with common fixed
initial phases and middle phase zero. Unknown $\beta,m$ are not controller
inputs. A matched comparison uses the same actual input on both sides,
including any unchanged reference. Relabeling two independently unknown
initial inputs is a different identification problem.

**Definition 1.3 (complete marked-law metric).** On the common measurable
record space

$$
\Omega_T=\{\mathsf s\}\ \sqcup\ ((0,T]\times\{0,1,2,3,4\}),
\tag{IS.5}
$$

let $\mu_\gamma$ be the joint probability law from any fixed member of
(IS.4). The success symbol means no failure through $T$. Set

$$
\begin{aligned}
F_i(t)&=\mu_\gamma((0,t]\times\{i\}),\\
d_{\mathrm{mark}}(\gamma,\widetilde\gamma)
 &=\sup_{E\subseteq\Omega_T\ \mathrm{measurable}}
          |\mu_\gamma(E)-\mu_{\widetilde\gamma}(E)|.
\end{aligned}
\tag{IS.6}
$$

This is total variation in the probability convention, equal to half the
$L^1$ distance of densities with respect to any common dominating measure.
It retains all modes, their joint time labels and terminal success. It is a
metric on these probability laws, a pseudometric on controls, and does not
include the live quantum state. It is neither a distance between normalized
conditional failure laws nor a distance between unmarked time marginals.

**Definition 1.4 (complete quantum operational metric).** For any common
normalized input $\rho$ on the live space and an arbitrary unchanged reference
$R$, let $\omega_{\gamma,\mathsf s}(\rho)$ be its unnormalized successful
output and $\omega_{\gamma,i}(t;\rho)$ its failure output density, applying
the maps in (IS.3) tensored with $\operatorname{id}_R$. Define

$$
\begin{aligned}
D_\rho(\gamma,\widetilde\gamma)=\frac12\bigg(&
 \|\omega_{\gamma,\mathsf s}(\rho)
       -\omega_{\widetilde\gamma,\mathsf s}(\rho)\|_1\\
 &+\sum_{i=0}^4\int_0^T
   \|\omega_{\gamma,i}(t;\rho)
       -\omega_{\widetilde\gamma,i}(t;\rho)\|_1\,dt\bigg),\\
d_{\mathrm{op}}(\gamma,\widetilde\gamma)&=\sup_{R,\rho}D_\rho(\gamma,\widetilde\gamma).
\end{aligned}
\tag{IS.7}
$$

These are trace distances on the full classical–quantum output, with exact
time treated as a measurable classical variable, not a finite register.
The definition applies also to trace-class states on an infinite-dimensional
reference. The classical output norm is the displayed integral norm; no
uncountable orthonormal time basis is assumed. Operational distinguishability
here allows arbitrary tests of this declared output, not access to the control
description. It supplies no such laboratory tests.

For a source-family input, tracing out the quantum output gives (IS.6), so

$$
d_{\mathrm{mark}}\leq D_\rho\leq d_{\mathrm{op}}.
\tag{IS.8}
$$

Indeed the absolute trace of each Hermitian output difference is bounded by
its trace norm; summing the classical blocks proves the first inequality.
No converse metric substitution is made. Exact equality of these metrics
will be proved only for the particular counterexamples below.

## 2. Conditional inverse stability and its constants

**Lemma 2.1 (loss balance needed for stability).** For every control of
Definition 1.1, every source-family input, every mode and every $t$,

$$
F_i(t)=p_i(a)-S(t)p_i(k(t)).
\tag{IS.9}
$$

Consequently

$$
S(t)=1-F_2(t)/Z,\qquad
k(t)=\frac{a-F_0(t)}{S(t)},\qquad
F_0(t)+F_4(t)=2a-2S(t)k(t).
\tag{IS.10}
$$

Proof. Write $q_i=S p_i(k)$. The absolutely continuous product rule gives
$q_i'=-g_iq_i$. In (IS.3), $J_i\rho J_i^*$ depends on the live input only
through its $ii$ entry; the phase cancels. That entry is $p_i(a)$ on
(IS.4), so the failure density is $g_iS p_i(k)=-q_i'$. Integrating from
zero, where $S(0)=1$ and $k(0)=a$, proves (IS.9) at every time. The
middle probability is $Z$ and the two plus probabilities equal $k$,
giving (IS.10). These calculations use the credited instrument; they do
not assert its acquisition or a new instrument classification. $\square$

**Theorem 2.2 (two-CDF inverse estimate).** Compare two controls with the
same $b,a,T$ and input contract. Suppose

$$
S(T),\widetilde S(T)\geq\sigma>0,\qquad
\|F_0-\widetilde F_0\|_\infty\leq\varepsilon_0,\qquad
\|F_2-\widetilde F_2\|_\infty\leq\varepsilon_2.
$$

Then

$$
\|k-\widetilde k\|_\infty
\leq\frac{\varepsilon_0+(c/Z)\varepsilon_2}{\sigma}.
\tag{IS.11}
$$

Proof. Terminal floors imply the same floors at all earlier times. By
(IS.10), $|S-\widetilde S|\leq\varepsilon_2/Z$, and

$$
S(k-\widetilde k)=\widetilde F_0-F_0
                         +\widetilde k(\widetilde S-S).
$$

Use $0<\widetilde k<c$ and divide by $S\geq\sigma$.
Taking the supremum proves the estimate, including $T=0$. $\square$

**Theorem 2.3 (stronger complete marked-law-TV inverse estimate).** Under
the same fixed source, time and matched-input hypotheses and terminal
survival floors, if $d_{\mathrm{mark}}\leq\varepsilon$, then

$$
\|k-\widetilde k\|_\infty\leq\frac{\varepsilon}{2\sigma}.
\tag{IS.12}
$$

In particular this holds with $\varepsilon=d_{\mathrm{op}}$, or with
$\varepsilon=D_\rho$ for any matched source-family input, by (IS.8).
It is a height estimate, not an approximate phase-lifting theorem.

Proof. Fix $t$ and put $x=\widetilde k(t)$. In the *same* record space
$\Omega_T$ define disjoint events

$$
\begin{aligned}
A_t&=(0,t]\times\{0,4\},\\
B_t&=\{\mathsf s\}\sqcup((t,T]\times\{0,1,2,3,4\}).
\end{aligned}
$$

Thus $\mu(A_t)=2a-2S(t)k(t)$ and $\mu(B_t)=S(t)$.
The bounded function $h_t=\frac12\mathbf1_{A_t}+x\mathbf1_{B_t}$ takes
values in $[0,1/2]$, because $0<x<c<1/2$. For two probability laws,

$$
\left|\int h\,d(\mu-\widetilde\mu)\right|
\leq (\sup h-\inf h)\,\sup_E|\mu(E)-\widetilde\mu(E)|.
\tag{IS.13}
$$

For completeness, subtract $\inf h$ since the signed measure has total mass
zero, and integrate its level sets; each level-set difference is bounded by
the event supremum. Apply this to $h_t$. Substitution from (IS.10) gives

$$
S(t)(k(t)-x)=-\int h_t\,d(\mu_\gamma-\mu_{\widetilde\gamma}),
$$

whose absolute value is at most $\varepsilon/2$. Divide by the floor and
take the supremum. The events contain actual retained failure labels and
survival beyond the cut; no independent marginal laws were combined.
$\square$

The constants in (IS.11) are $1$ and $c/Z$ before division by $\sigma$;
the constant in (IS.12) is $1/2$. These are the proved constants, without a
claim of optimal minimax constants. If only a common marked-TV error
$\varepsilon$ is known, it implies each CDF error is at most $\varepsilon$;
using (IS.11) then gives $(1+c/Z)\varepsilon/\sigma$, whereas (IS.12)
uses the joint law to give $\varepsilon/(2\sigma)$. Two supplied CDF error
bounds do not themselves certify marked TV or quantum operational distance.
Uniform CDF error controls intervals, whereas TV tests all measurable time
sets. Thus the stronger estimate requires stronger error data.

**Corollary 2.4 (an explicit resource route to the floor).** Fix
$0<\eta\leq c/2$. If both paths obey
$\eta\leq k,\widetilde k\leq c-\eta$ and
$\operatorname{TV}(k),\operatorname{TV}(\widetilde k)\leq V$, then one
may take $\sigma=e^{-V/\eta}$. A common height-speed bound $v_k$ and
duration bound $T_*$ give the choice $V=v_kT_*$.

Proof. Pointwise $\lambda\leq |k'|/\eta$; integrate and exponentiate.
Absolute continuity identifies height variation with $\int|k'|$.
$\square$

This floor is sufficient and conservative. Positive support of each
individual path supplies no common numerical $\eta$ or $V$ over the full
original class. The theorems use the known preparation diagonal; they do
not identify an unknown initial phase, winding, reference or preparation
from an unlabelled collection of outputs.

## 3. A bounded-speed forward discontinuity

**Definition 3.1 (the signed loss curve used in this example).** Write
$C=F_0-F_1$ and $V_C(t)=\operatorname{TV}_{[0,t]}(C)$.
For this canonical optimal instrument, direct differentiation of (IS.9)
shows the following alternatives almost everywhere:

$$
\begin{array}{c|ccc}
 &F_0'&F_1'&F_2'\\ \hline
k'>0&0&cS\lambda&ZS\lambda\\
k'<0&cS\lambda&0&ZS\lambda\\
k'=0&0&0&0
\end{array}
\tag{IS.14}
$$

The paired modes have $F_4'=F_0'$ and $F_3'=F_1'$. Consequently
$|C'|=cS\lambda=-cS'$ and

$$
V_C(t)=c(1-S(t)).
\tag{IS.15}
$$

Only this balance identity is needed here. It does not assert a general
range theorem, minimum coordinate theorem or new finite-storage result.

**Theorem 3.2 (uniform convergence with bounded resources does not control
survival).** Fix $c\in(0,1/2)$, $Z=1-2c$, $a=c/2$, duration $T=1$ and
constant real phase. Set $v=c/2$. For each integer $n\geq1$, define the
triangular function on the $j$th cycle, $0\leq j<n$, by

$$
C_n(t)=
\begin{cases}
v(t-j/n),& j/n\leq t\leq(j+1/2)/n,\\
v((j+1)/n-t),&(j+1/2)/n\leq t\leq(j+1)/n.
\end{cases}
\tag{IS.16}
$$

The actual original height control is

$$
S_*(t)=1-t/2,\qquad
k_n(t)=\frac c2-\frac{C_n(t)}{2S_*(t)},\qquad \chi_n(t)=\chi_0.
\tag{IS.17}
$$

These controls belong to both original regularity alternatives and have
the following common bounds, in the acquisition supplier's chosen coordinate
units:

$$
\begin{aligned}
&k_n(0)=k_n(1)=a,\qquad c/4\leq k_n\leq c/2,\\
&\min_i p_i(k_n(t))\geq\min(c/4,Z)>0,\qquad |k_n'|\leq3c/4,\\
&\chi_n'=0,\quad \operatorname{TV}(\chi_n)=0,\quad
  \operatorname{TV}(k_n)=\mathcal L_n\leq3c/4,\quad
  \mathcal Q_n\leq9c^2/16.
\end{aligned}
\tag{IS.18}
$$

Here $\mathcal L=\int\sqrt{k'^2+\chi'^2}$ and
$\mathcal Q=\int(k'^2+\chi'^2)$ are mathematical coordinate costs,
not calibrated physical energy. Both $k_n\to a$ and the instrument's
actual signed loss curves $C_n\to0$ uniformly, with bounds $c/(4n)$.
Nevertheless the actual survival is $S_n(t)=1-t/2$, and hence

$$
S_n(1)=\tfrac12\neq1=S_{\mathrm{wait}}(1),\qquad
d_{\mathrm{mark}}(\gamma_n,\mathrm{wait})
=D_\rho(\gamma_n,\mathrm{wait})
=d_{\mathrm{op}}(\gamma_n,\mathrm{wait})=\tfrac12
\tag{IS.19}
$$

for every normalized live input with any reference in the $D_\rho$ equality.

Proof. The functions in (IS.17) are continuous and smooth on each of the
finitely many triangular legs, with denominators at least $1/2$. Their
derivatives extend continuously to each closed leg. They therefore satisfy
the finite-piecewise-$C^1$ condition and are absolutely continuous.
The bounds $0\leq C_n\leq c/(4n)$ and $S_*\geq1/2$ give the height,
margin and uniform-error bounds. Differentiation on a leg gives

$$
k_n'=-\frac{C_n'}{2S_*}-\frac{C_n}{4S_*^2}.
\tag{IS.20}
$$

On rising legs $C_n'=v$ and this equals
$-(c-k_n)/(2S_*)<0$. On falling legs $C_n'=-v$ and it equals
$k_n/(2S_*)>0$. Thus the *actual* hazard from (IS.2) is
$\lambda_n=1/(2S_*)$. Since $S_*'=-1/2$ and $S_*(0)=1$, it solves
$S_*'=-\lambda_nS_*$ and is the actual survival. By (IS.14) the actual
derivative of $F_0-F_1$ is $+v$ on the rising legs and $-v$ on the
falling legs. It starts at zero, so the actual curve is precisely (IS.16).
This verifies the family directly from the original hazard and jump law,
without assuming any curve-realization theorem.

From (IS.20),
$|k_n'|\leq v+c/(4n)\leq3c/4$. Integrating this speed and its square
over the unit interval proves the variation, length and quadratic bounds.
The transported phase is zero, and the height returns to $a$, so
$K^{(n)}_1=I_5/\sqrt2$. Completeness makes the total failure effect
$I_5/2$. Waiting has successful operator $I_5$ and no failure output.
For any normalized input with reference the success difference has trace
norm $1/2$; the positive failure blocks together have trace $1/2$.
Their half-sum in (IS.7) is $1/2$. The classical failure event gives the
same distance for (IS.6). Taking the supremum changes nothing. $\square$

**Corollary 3.3 (the precise insufficient regularity boundary).** Uniform
height error, even together with a common positive support margin, common
finite duration, common Lipschitz bound, common height-variation upper bound,
zero phase variation and common upper bounds on $\mathcal L,\mathcal Q$,
does not imply convergence of survival or complete stopped instruments.
Uniform error in the signed curve is likewise insufficient, even when
$|C_n'|=c/2$ almost everywhere and $\operatorname{TV}(C_n)=c/2$ for all $n$.

Proof. Theorem 3.2 supplies all the stated bounds and nonconvergence.
For each $t$, $V_{C_n}(t)=vt$, whereas the zero curve has variation zero;
thus uniform convergence of curves has lost their accumulated variation.
There is no contradiction with a theorem requiring *convergence* of
variation, or convergence of derivatives in $L^1$. The height derivatives
also fail to converge to zero in $L^1$: their exact variation is

$$
\operatorname{TV}(k_n)
=c\sum_{j=0}^{n-1}\frac1{4n-2j-1}>c/4.
\tag{IS.21}
$$

Each cycle has one minimum at $(j+1/2)/n$, of depth
$c/[2(4n-2j-1)]$ below $a$; summing twice these depths proves the formula.
The family has no common bound on its number of monotonic pieces. Equal
upper resource bounds are not equality of resource totals with waiting.
$\square$

## 4. Low-survival inverse nonuniformity with exact operational distance

**Theorem 4.1 (repeated-prefix early/late pair).** Fix $0<a<b<c<1/2$,
$Z=1-2c$, $d=b-a$ and

$$
q=\frac ab\frac{c-b}{c-a}\in(0,1).
\tag{IS.22}
$$

For each integer $n\geq1$, construct two controls of duration $2$ with
constant real phase. They have a common literal prefix on $[0,1]$:
on each $[j/n,(j+1)/n]$, $0\leq j<n$, move affinely from $a$ to $b$
on its first half and affinely back to $a$ on its second half.
The early suffix is

$$
k_{n,E}(t)=
\begin{cases}
a+4d(t-1),&1\leq t\leq5/4,\\
b-4d(t-5/4),&5/4\leq t\leq3/2,\\
a,&3/2\leq t\leq2;
\end{cases}
\tag{IS.23}
$$

the late suffix waits at $a$ on $[1,3/2]$ and then uses the same excursion
shifted by $1/2$. The two controls satisfy both regularity alternatives,
share support margin $\min(a,c-b,Z)$ and have exactly equal resource tuples

$$
\begin{aligned}
T&=2,&\operatorname{TV}(k)&=\mathcal L=2(n+1)d,\\
\operatorname{TV}(\chi)&=0,&\mathcal Q&=(4n^2+8)d^2,\\
\|k'\|_{L^\infty}&=\max(2n,4)d,&\|\chi'\|_{L^\infty}&=0.
\end{aligned}
\tag{IS.24}
$$

Their height distance is fixed, while their complete instruments satisfy

$$
\begin{aligned}
\|k_{n,E}-k_{n,L}\|_\infty&=d,\\
d_{\mathrm{mark}}(\gamma_{n,E},\gamma_{n,L})
 &=D_\rho(\gamma_{n,E},\gamma_{n,L})
  =d_{\mathrm{op}}(\gamma_{n,E},\gamma_{n,L})
  =q^n(1-q).
\end{aligned}
\tag{IS.25}
$$

The $D_\rho$ equality holds for **every** common normalized five-dimensional
live input with **any** unchanged reference, including entanglement with
the live input. Thus the exponential indistinguishability is not a
source-family-only or reference-free assertion.

Proof. Every finite piece is affine or constant with matching endpoints,
and $[a,b]\subset(0,c)$, so the controls are original controls with the
claimed margin and zero phase. A monotone upward leg $a\to b$ has survival
$a/b$ by integrating $k'/k$; its downward return has survival
$(c-b)/(c-a)$. A whole loop therefore has survival $q$ and, because its
endpoint height and phase are unchanged, successful Kraus $\sqrt q I_5$.
The common prefix has successful Kraus $q^{n/2}I_5$. Its entire failure
CP measure, including its correlations with the reference, is identical
for the two histories, since their controls coincide on that full prefix.

Each suffix has successful Kraus $\sqrt q I_5$, so both total success
operators are $q^{(n+1)/2}I_5$. The total suffix failure effect is
$(1-q)I_5$. After the common prefix it is $q^n(1-q)I_5$.
For arbitrary joint $\rho$ the total suffix failure trace is consequently
$q^n(1-q)$ in each experiment. These are positive operator-valued output
measures on the reference and absorbing state. Their time supports are
respectively $(1,3/2)$ and $(3/2,2)$, disjoint up to endpoints of Lebesgue
measure zero. There are no failure atoms at the endpoints. Thus on the
early support the output difference is positive; on the late support it
is negative. Their integrated trace norms add to $2q^n(1-q)$.
The common-prefix differences and terminal-success difference vanish.
Equation (IS.7) now gives exactly $q^n(1-q)$, without discarding any
mode or reference correlation. The event of a failure in the early time
window attains this distance already in the marked law, proving every
equality in (IS.25).

At time $5/4$ the early height is $b$ and the late height is $a$;
all heights are in $[a,b]$. This proves the sup gap $d$.
There are $n$ prefix round trips at speed $2nd$ and one suffix round trip
at speed $4d$ occupying half a unit. Summing their variations and squared
speeds proves (IS.24). $\square$

The same supremum distance holds for the supplier's common six-dimensional
absorbing extension: an initially stopped component creates no additional
difference, and live–stopped coherences have identical terminal successful
operators. The differing failure mass for a general such input is
$q^n(1-q)$ times its initial live weight. A fully live input attains the
supremum in (IS.25).

**Corollary 4.2 (what uniform inverse statement is false).** On original
controls with fixed duration $2$ and the common support band $[a,b]$, there
is no function $\omega(\varepsilon)\to0$ as $\varepsilon\downarrow0$
such that $\|k-\widetilde k\|_\infty\leq
\omega(d_{\mathrm{op}}(\gamma,\widetilde\gamma))$ for all pairs in that
class. The same negative conclusion holds with $d_{\mathrm{mark}}$.

Proof. Apply (IS.25) and let $n\to\infty$. $\square$

This statement also survives requiring equality of the listed aggregate
resources *within each compared pair*. Their common values in (IS.24)
grow with $n$. It supplies no counterexample on a class with a common
speed cap or common height-variation cap. Total survival is
$q^{n+1}\to0$, so no common positive survival floor is present.
For example $c=2/5$, $Z=1/5$, $a=1/5$, $b=3/10$ gives
$q=1/3$, height gap $1/10$ and distance $2/3^{n+1}$.

The constructions are actual legal mathematical controls, not pre-run
recorded occurrences or laboratory incidents. Their mathematical
instrument programmes are different. A separately retained programme name
or waveform archive would distinguish the richer outputs and is not an
input to the distances defined here.

## 5. Reconciliation and the stronger hypotheses actually used

Theorem 3.2 is a discontinuity from **uniform control or signed-curve
topology to output law**. It already has survival at least $1/2$ and
uniform speed, variation and support bounds. Its complete marked laws
stay distance $1/2$ from waiting, so it does not meet a small-output-error
hypothesis of Theorem 2.3. Theorem 4.1 is an obstruction in the opposite
direction, from **small output distance to uniform height recovery** over
a class without a common survival floor. It does not have uniformly bounded
speed or variation. Neither construction refutes (IS.11) or (IS.12).

For (IS.12), both a bound on the *joint marked-law error* and a certified
floor are sufficient data. A common support margin and height-variation
bound supply the floor by Corollary 2.4, but do not themselves supply
small marked-law error. Given only the two CDF errors, use (IS.11).
Replacing these hypotheses with a failure-time marginal, a conditional
survival probability, a uniform error in $C$, a terminal holonomy error,
or a finite number of acquired events is unsupported.

**Proposition 5.1 (one stronger forward control condition for survival).**
Fix $0<\eta\leq c/2$ and suppose both heights stay in $[\eta,c-\eta]$. Put
$\delta=\|k-\widetilde k\|_\infty$,
$e=\|k'-\widetilde k'\|_{L^1}$, and
$M=\operatorname{TV}(\widetilde k)$. Then

$$
\|\lambda-\widetilde\lambda\|_{L^1}
\leq B:=e/\eta+M\delta/\eta^2,\qquad
\|S-\widetilde S\|_\infty\leq B.
\tag{IS.26}
$$

Proof. For fixed height, the hazard as a function of velocity is continuous
piecewise linear with slopes bounded in modulus by $1/\eta$. Changing
height with velocity fixed changes it by at most
$|\widetilde k'|\delta/\eta^2$. Integrate the two differences.
For nonnegative charges $x,y$, $|e^{-x}-e^{-y}|\leq|x-y|$;
apply this to each prefix integral. $\square$

Thus strong derivative control, or a separate certificate of accumulated
loss variation in (IS.15), addresses the oscillation obstruction for
survival. A bound on variation without an error bound on its accumulation
does not. Survival convergence alone is still weaker than convergence of
all retained quantum outputs and time/mode measures.

**Proposition 5.2 (sufficient complete-output error data).** Write
$f_i=F_i'$ for source-family loss densities and define

$$
\kappa=\|K_T-\widetilde K_T\|_{\mathrm{op}},\qquad
b_i=\frac1{p_i(a)}\int_0^T|f_i-\widetilde f_i|\,dt.
$$

For the fixed canonical instruments on all live inputs and arbitrary
reference,

$$
d_{\mathrm{op}}\leq\kappa+\tfrac12\max_i b_i.
\tag{IS.27}
$$

Proof. From (IS.3) and (IS.9), the failure density on a joint input is
$(f_i/p_i(a))|f\rangle\langle f|\otimes\rho_{ii}^R$, where
$\rho_{ii}^R\geq0$ and $\sum_i\operatorname{tr}\rho_{ii}^R=1$.
Its integrated difference norm is
$\sum_i b_i\operatorname{tr}\rho_{ii}^R\leq\max_i b_i$.
For contractions $K,L$, adding and subtracting $L\rho K^*$ bounds
$\|K\rho K^*-L\rho L^*\|_1$ by $2\|K-L\|_{\mathrm{op}}$, also
after tensoring with the identity. Combine these estimates in (IS.7).
$\square$

The inputs in (IS.27) require certified $L^1$ loss-density error, including
time/mode calibration, and terminal Kraus error, including terminal phase
characters. Uniform CDF or signed-curve error cannot be substituted for
these stronger data. For clarity, (IS.26) does provide a concrete route
to loss-density convergence: with $D=\operatorname{TV}(k)\leq M+e$,
product differentiation of $f_i=-(S p_i(k))'$ gives

$$
\int|f_i-\widetilde f_i|
\leq(1+M/\eta+D)B+\delta+e.
\tag{IS.28}
$$

Indeed $\int|S'-\widetilde S'|\leq(1+M/\eta)B$ follows from
$S'=-\lambda S$, and $\int|\widetilde S'|\leq1$.
The remaining product terms are bounded by $\delta$, $DB$ and $e$,
using $p_i\leq1$ and $|p_i(k)-p_i(\widetilde k)|\leq\delta$.
Hence a uniform margin, bounded $M$, strong $W^{1,1}$ height convergence
and separately controlled terminal phase characters suffice for
complete-output convergence through (IS.27). Explicitly, set
$z_i=e^{-iH_i(T)}$ and
$e_z=\max_i|z_i-\widetilde z_i|$. Since
$|S p_i(k)-\widetilde S p_i(\widetilde k)|\leq B+\delta$ and
$|\sqrt x-\sqrt y|\leq\sqrt{|x-y|}$ for nonnegative $x,y$,

$$
\kappa\leq\max_i\sqrt{\frac{B+\delta}{p_i(a)}}+e_z.
\tag{IS.29}
$$

The phase term uses that every diagonal entry of $\widetilde K_T$ has
modulus at most one. This is an explicit sufficient condition, not a claim
that derivative convergence is necessary or that $e_z$ has been acquired.

No relative phase waveform is recovered from the height estimate.
Recovering it would need additional same-input phase-sensitive data at
intermediate cuts and a declared real-lift anchor. A finite noisy version
would additionally need certified sampling, clock/reference alignment and
an anti-alias condition, such as a known bound keeping real phase increments
between consecutive reads strictly within a selected unwrapping interval,
with noise slack. Those data and their acquisition are absent here; no
approximate phase-unwrapping theorem is asserted. Unknown past $\beta,m$
remain unknown and are never passed to a controller.

The common future original menu, when separately permitted, consists of
prescribed original controls at the same base and matching current height,
of any finite duration including zero, with both regularity alternatives
and all signed winding sectors. `concatenate_original` supplies the literal
prefix and the relatively translated real-phase tail. It supplies no
post-failure positive-carrier restart. A common legal downstream quantum
protocol on the retained joint output cannot increase its trace distance;
such a protocol must use the same acquired-record policy, references,
permissions and external inputs in both experiments. This observation does
not allow access to omitted old programme fields, different legality guards
or earlier quantum cuts. An acquisition service or complete internal
observer still needs its own joint legality, failure and update proof.

## 6. Sources, exact checks and recovery boundary

All repository citations in this volume select the immutable public revision
`17ef08588473220560adc4a7fb0775a5f7f238a1`.

| Supplier | Exact use and boundary |
| --- | --- |
| [FiniteRectangleTransport Lean](https://github.com/the-omega-institute/trureturing/blob/17ef08588473220560adc4a7fb0775a5f7f238a1/D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean), `ValidBase`, `probability`, `phaseWeight`, `weight_compatible`, and [Blueprint](https://github.com/the-omega-institute/trureturing/blob/17ef08588473220560adc4a7fb0775a5f7f238a1/Blueprint/D5/S3/Quantum/Fibers/FiniteRectangleTransport.md) | Strict positive source, original signed transport, middle gauge, real lifts and all signed sectors. The controls here obey that exact law; no physical actuator or sensor follows from the source. |
| [OriginalControlComposition Lean](https://github.com/the-omega-institute/trureturing/blob/17ef08588473220560adc4a7fb0775a5f7f238a1/D5/S3/Quantum/Fibers/OriginalControlComposition.lean), `OriginalControl`, `FiniteC1Control`, `concatenate_original`, and [Blueprint](https://github.com/the-omega-institute/trureturing/blob/17ef08588473220560adc4a7fb0775a5f7f238a1/Blueprint/D5/S3/Quantum/Fibers/OriginalControlComposition.md) | Both regularity alternatives, matching interfaces, arbitrary finite and zero durations, unchanged prefix, translated relative tail and exact scalar-integral composition. No unknown past input is granted to the controller. |
| [Instrument Boundaries](https://github.com/the-omega-institute/trureturing/blob/17ef08588473220560adc4a7fb0775a5f7f238a1/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md), §§4–5.2, especially OC.19b | Entire canonical optimal instrument, full unknown-input family, sharp filters, blind success records, survival optimum and absorbing completion are credited inputs. This volume studies stability for that completion only, not every optimal instrument or every valid base. |
| [Record Acquisition](https://github.com/the-omega-institute/trureturing/blob/17ef08588473220560adc4a7fb0775a5f7f238a1/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_RECORD_ACQUISITION.md), §§2, 5–9, 11 | Chosen coordinate costs, finite point-query limitations and conditional calibrated area/winding certificates. Those endpoint-response certificates do not certify the complete law metric here. No duplicate sampling lower bound is proposed. |
| [Transport-Memory Completion](https://github.com/the-omega-institute/trureturing/blob/17ef08588473220560adc4a7fb0775a5f7f238a1/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §§2.9–2.12/2.18; [Process Geometry](https://github.com/the-omega-institute/trureturing/blob/17ef08588473220560adc4a7fb0775a5f7f238a1/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §34; [Atlas Stable Core](https://github.com/the-omega-institute/trureturing/blob/17ef08588473220560adc4a7fb0775a5f7f238a1/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md), §§1–3 | Actual coherent source/common port, known nonzero amplitudes and record overlap, aligned acquired records, actual domains/routes, references, permissions, failure successors and selection/update inputs remain separate requirements. A whole-law inverse does not fulfill them. |
| Dobler and Pauly, [*Approximative Tests for the Equality of Two Cumulative Incidence Functions of a Competing Risk*, arXiv:1402.2209v3](https://arxiv.org/html/1402.2209v3), §2, Eq. (2.1) and following sampling model | `literature-attested`: cause-marked cumulative incidence is survival integrated against a cause intensity; their estimators use independent observed copies and a stated censoring/truncation model. The loss balance here is derived directly from OC.19b; their copies and estimation model are not supplied for this source. |
| Chiribella, D'Ariano and Perinotti, [*Theoretical framework for quantum networks*, arXiv:0904.4483v2](https://arxiv.org/html/0904.4483v2), Theorem 3, Definition 10/Theorem 10 and Definition 11 | `literature-attested`: causal normalization, generalized instruments and testers describe specified quantum networks and accessible operations; Definition 10 states a finite-outcome presentation and discusses extension to arbitrary outcomes. No continuous-monitor implementation, allowed tester family, waveform sensor or same-history archive is imported. The continuous-time measure and all distances here are defined explicitly by the supplier and (IS.5)–(IS.7). |

Calculus for absolutely continuous functions, total-variation duality and
trace-norm inequalities are mature ingredients. The source-specific new
content is the conditional metric comparison in Theorems 2.2–2.3, the actual
bounded-resource forward counterfamily in Theorem 3.2, the exact
reference-preserving distance of Theorem 4.1, and the explicitly scoped
sufficient stability conditions in §5. These are `repo-derived` ordinary
deductions, not a worldwide originality claim. No compression or
asymptotic-rate theorem from a different quantum model is used.

Bounded exact in-memory rational calculations check (IS.17)–(IS.20) on
816 interior leg points: $c\in\{1/5,2/5,1/3\}$,
$n\in\{1,2,3,4,8,16\}$, every leg, at local fractions
$1/8,1/3,1/2,7/8$. The checks include the original hazard, nonnegative
five-mode loss density, actual signed loss derivative, uniform margins and
speed bounds. Another 120 exact checks use three rational triples
$(c,a,b)=(2/5,1/5,3/10),(2/5,1/10,1/5),(1/3,1/12,1/4)$,
$1\leq n\leq8$ and all five initial mode inputs, verifying the scalar
loop effect, repeated survival and disjoint-tail half-$L^1$ distance.
Eighteen exact checks on the same $c,n$ lists verify (IS.21) and its
positive lower bound on height variation.
For the first triple the first two distances are $2/9$ and $2/27$.
The all-parameter and arbitrary-reference claims rest on the ordinary
proofs, not on these finite calculations. No experiment files are retained.

The recovery delta is precise: under a certified survival floor, small
error in the complete marked law controls the entire parameterized height;
uniform waveform accuracy alone fails to control that law; without a
floor, even complete quantum output distance can hide a fixed late height
distinction. These results do not identify the full real phase history,
construct an acquired observer boundary, replace the live quantum specimen
by a classical label, or give finite memory for a real-time law.

An actual acquisition implementation would have to justify calibrated
time/mode and phase-sensitive readings, source/input matching, joint error
events, preparation/reference transport, any repeated same-history trials,
disturbance, storage and arithmetic, and every legal update/failure
successor. None is supplied by taking the inverse of a probability law.
Exact timestamps and whole cumulative functions are not finite-bit data.
The native $\alpha/\beta$ late-target rate/cofinality problem, the distinct
fixed-Hamiltonian quantum minimax problem, common-port acquisition and
space/time/boundary/memory mutual recovery remain unresolved under their
original contracts. No full-programme completion, physical realization or
Lean certification is claimed.

## 追加锚（本行以下为增补区）
