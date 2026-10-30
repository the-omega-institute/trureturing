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

## 7. The native spatial form and the actual command-time trace

**Definition 7.1 (fixed native source and spatial topology).** Write G for
[Native variable-coefficient Green stability](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md)
and O for [Native point-source occupation and finite-command cap limits](FIB_NATIVE_SINGULAR_OCCUPATION_AND_COMMAND_CAP_LIMITS.md).
Fix any model of G, Definition 29.1, equivalently O, Definition 1.1.
Thus $0<Z<1$, $r=1-Z$, $H=r/2$, the original means satisfy $X=Y=H$,
$I=(l,u)\Subset(0,H)$, and $\Omega=I\times\mathbb T^2$.
Preparations, their phase rotations and the interior source
$o=(k_o,\alpha_o,\beta_o)$ are fixed. Both actual phase periods are
$2\pi$. Fix arbitrary smooth positive raw density $\rho$ and smooth real
symmetric positive definite $A=(a^{ij})$ on a neighbourhood of the closed
cylinder. Retain exactly

$$
\begin{gathered}
X_1=P=\partial_k,\qquad
X_2=Q=\tfrac12\partial_\alpha+(\tfrac12-k/r)\partial_\beta,
\qquad d\mu=\rho\,dk\,d\alpha\,d\beta,\\
T_A[f]=\int_\Omega\sum_{i,j=1}^2
 a^{ij}(X_jf)\overline{X_if}\,d\mu,\qquad
\|f\|_{\mathcal F}^2=\|f\|_{L^2(\mu)}^2+T_A[f],\\
\mathcal F_A=\overline{C_c^\infty(\Omega)}^{\,\|\cdot\|_{\mathcal F}}.
\end{gathered}
\tag{NT.1}
$$

The spatial object is an amplitude modulo $\mu$-almost-everywhere equality,
with this original form topology. Smooth amplitudes have unique smooth
representatives: a smooth function vanishing $\mu$-almost everywhere
vanishes everywhere, since $\rho$ is positive. The represented free
operator $L_A$ has both height faces killed and phases periodic. Its clock
is $e^{-tL_A}$, with control covariance $2A\,dt$. Its full unit-source
Green field and the diffusion occupation measure are

$$
\Gamma(q)=\int_0^\infty p_t^\Omega(o,q)\,dt,
\qquad \nu(dq)=\Gamma(q)\,d\mu(q).
\tag{NT.2}
$$

The source is not averaged, the angular measure is not normalized, and
$\int\Gamma L_A\varphi\,d\mu=\varphi(o)$. The suppliers give
$\Gamma\in L^1(\mu)$, positive and smooth off $o$, and
$\Gamma(o)=+\infty$. Its value at this $\mu$-null point does not change
$\nu$. This is the free killed operator, without an attractive potential
or ground conditioning. The spatial probes below do not change the
actual initial source or assert preparation of a new physical state.

**Definition 7.2 (unchanged command law and complete lifetime).** Put

$$
\delta_n=n^{-2},\quad m_n=n^3,\quad S_n=n,\quad T_n=n+\delta_n,
\quad \Sigma=A^{1/2},\qquad
d^j=\rho^{-1}\sum_iX_i(\rho a^{ij}).
\tag{NT.3}
$$

Let $\Xi_n=(\{-1,1\}^2)^{m_n}$ with its uniform product probability
$\pi_n$. At each alive node execute exactly G, Definition 29.2:

$$
\begin{gathered}
v_i=d(q_i)\delta_n+\sqrt{2\delta_n}\Sigma(q_i)\xi_i,\qquad
\theta=(t-i\delta_n)/\delta_n,\\
(a,b,j)(t)=
\left(a_i+\theta v_i^1,\ b_i+\theta v_i^2,
 j_i+\theta a_i v_i^2+\tfrac12\theta^2v_i^1v_i^2\right),\\
q(t)=\Phi_o(a,b,j)=
\left(k_o+a,\ [\alpha_o+b/2],
 [\beta_o+(\tfrac12-k_o/r)b-j/r]\right).
\end{gathered}
\tag{NT.4}
$$

Controls start at zero, and $j=\int a\,db$ is the actual chronological
integral at every prefix. Cut a chord at its first hit of either $l$ or
$u$, and hold thereafter. If every random cell survives, retain the
original last interval $[S_n,T_n]$: height moves linearly from its current
value to $u$ with $b$ and $j$ constant. Write $\bar q_{n,\omega}$ for
the resulting held trajectory and $\zeta_{n,\omega}$ for its actual
first hit. Then $0<\zeta_{n,\omega}\le T_n$. Unused signs are not
rejected or reweighted. All native prefix guards remain in force.
Only $0\le t<\zeta_{n,\omega}$ contributes to an alive observation;
the post-hit hold and any later constant continuation contribute nothing.
Stationary random cells before death, including a possible source hold
at a coarse mesh, do contribute their entire duration.

**Definition 7.3 (trace space, expected measure and supplied limit).** The
actual run-time measure space is the finite disjoint union

$$
\mathscr D_n=\coprod_{\omega\in\Xi_n}
 \{\omega\}\times[0,\zeta_{n,\omega}),\qquad
 d\vartheta_n(\omega,t)=\pi_n(\omega)\,dt.
\tag{NT.5}
$$

Define the expected spatial occupation measure $\nu_n$ and the linear
smooth-core trace by

$$
\begin{aligned}
\nu_n(B)&=\sum_{\omega\in\Xi_n}\pi_n(\omega)
 \int_0^{\zeta_{n,\omega}}{\bf1}_B(\bar q_{n,\omega}(t))\,dt,\\
\mathscr R_n:C_c^\infty(\Omega)\subset\mathcal F_A
 &\longrightarrow L^2(\mathscr D_n,\vartheta_n),\qquad
 (\mathscr R_nf)(\omega,t)=f(\bar q_{n,\omega}(t)).
\end{aligned}
\tag{NT.6}
$$

The target records functions of the actual executed time and sign word;
it is not an acquired sensor record. Its norm satisfies
$\|\mathscr R_nf\|^2=\nu_n(|f|^2)$. Equivalently, restriction first
lands in $L^2(\nu_n)$ and then pulls back isometrically into this run-time
space. The latter isometry need not be onto: an arbitrary time function
need not depend only on the visited state. Thus no independent run-time
information is silently identified with a spatial value.

For the same-source free diffusion $Q_t$ of G, (29.6)–(29.7), killed at
$\tau$, Tonelli gives, for every nonnegative Borel $W$,

$$
\nu(W)=\mathbb E_o\int_0^\tau W(Q_t)\,dt.
\tag{NT.7}
$$

G, Theorem 29.6, supplies the complete-lifetime fixed-test bridge

$$
\nu_n(f)\longrightarrow\nu(f)
\qquad(f\in C(\overline\Omega)),\qquad
\nu_n(1)\longrightarrow\nu(1)=\mathbb E_o\tau\in(0,\infty).
\tag{NT.8}
$$

Its lifetime estimate and original termination rule are part of that
supplier. No limit on an initial cell is substituted for (NT.8).

## 8. Nonclosability for every original mesh

**Theorem 8.1 (arbitrarily small native-form representatives of a fixed
smooth command trace).** For every fixed model of Definition 7.1, every
integer $n\ge1$, every $f\in C_c^\infty(\Omega;\mathbb C)$ and every
$\varepsilon>0$, there exists $\chi\in C_c^\infty(\Omega;\mathbb R)$,
$0\le\chi\le1$, such that $u=f\chi$ satisfies

$$
\operatorname{supp}u\subseteq\operatorname{supp}f,\qquad
|u|\le|f|,\qquad \|u\|_{\mathcal F}\le\varepsilon,\qquad
u(\bar q_{n,\omega}(t))=f(\bar q_{n,\omega}(t))
\quad(\omega\in\Xi_n,\ 0\le t<\zeta_{n,\omega}).
\tag{NT.9}
$$

The cutoff $\chi$ can be supported in any
prescribed open neighbourhood of $\operatorname{supp}f$ inside $\Omega$.
In particular $\mathscr R_n$ is not closable from the Hilbert space
$\mathcal F_A$ into the actual run-time $L^2$ space, for every $n\ge1$.
The same holds for the equivalent core restriction into $L^2(\nu_n)$.
The scalar core map $f\mapsto\nu_n(|f|^2)$ has no continuous extension
in the original form norm.

Proof. For a fixed sign word, all alive nodes are determined recursively
by (NT.4). Each nonzero chord is a smooth immersed arc: its lifted height
and $\alpha$ derivatives are respectively $v_i^1/\delta_n$ and
$v_i^2/(2\delta_n)$, which cannot both vanish. A zero increment gives a
stationary point. Phase reduction preserves local smoothness, even through
windings. An immersed compact arc has a finite cover by embedded arc
charts; no global injectivity is needed. A cut chord is a subarc of the
same curve. The terminal height leg is another regular arc, since on
survival its starting height is strictly below $u$. Corners are covered
one adjoining arc at a time.

Let

$$
C_n=\bigcup_{\omega\in\Xi_n}
 \bar q_{n,\omega}([0,\zeta_{n,\omega}])
 \subseteq\overline\Omega,\qquad K=C_n\cap\operatorname{supp}f.
\tag{NT.10}
$$

If $K$ is empty, take $\chi=0$. Otherwise $C_n$ is a finite union
of compact curve images and points, with at most
$4^{m_n}$ paths, each of at most $m_n+1$ executed pieces. Hence $K$ is
compact and contained in the interior. Its preimages in the finitely many
parameter intervals are compact. Cover those preimages by finitely many
intervals on which each nonstationary curve is embedded, extending a piece
locally past an interior endpoint if necessary. This gives finitely many
interior arc charts covering $K$, together with finitely many point
charts. All charts can lie in the prescribed open neighbourhood. Self
intersections and joins cause no additional requirement.

The needed small-cutoff calculation is the classical logarithmic
codimension-two capacity mechanism. In a straightened arc chart use
coordinates $(s,y)\in\mathbb R\times\mathbb R^2$, with arc $y=0$.
Choose a smooth longitudinal cutoff $a(s)$ with $0\le a\le1$, equal
to one near the compact subarc and supported inside the chart. For $0<e<1/2$ put $L=\log(1/e)$
and choose a fixed smooth $\psi:\mathbb R\to[0,1]$ equal to one on
$(-\infty,0]$ and zero on $[1,\infty)$. Define

$$
 h_e(y)=\psi\left(\frac{\log(|y|/e^2)}{L}\right)\ (y\ne0),
 \qquad h_e(0)=1.
\tag{NT.11}
$$

It is smooth, constant near zero, supported in $|y|\le e$, and
$|\nabla h_e(y)|\le C/(|y|L)$ on $e^2<|y|<e$. In these two normal
directions polar integration gives

$$
\int |h_e|^2dy\le Ce^2,\qquad
\int|\nabla h_e|^2dy
 \le\frac{C}{L^2}\int_{e^2}^{e}\frac{dr}{r}
 =\frac{C}{L}.
\tag{NT.12}
$$

The longitudinal derivative of $a(s)h_e(y)$ costs $O(e^2)$.
Chart Jacobians and inverse derivatives are bounded on the chosen compact
supports. Thus the local ordinary $H^1$ norm squared is at most
$C(e^2+L^{-1})$. For a stationary point, an ordinary ball cutoff of
radius $e$, equal to one on the half-radius ball, has squared $L^2$ cost
$O(e^3)$ and squared gradient cost $O(e)$. This includes a positive-time
hold at $o$. These cutoffs are used only to estimate the given native form;
no Euclidean operator replaces it.

Extend the finitely many chart cutoffs $\chi_i$ by zero and combine them
as $\chi=1-\prod_{i=1}^N(1-\chi_i)$. Then $\chi=1$ near $K$,
$0\le\chi\le1$, and $\chi$ is smooth with compact support in the chosen
neighbourhood. The inequalities $\chi\le\sum_i\chi_i$ and
$|\nabla\chi|^2\le N\sum_i|\nabla\chi_i|^2$ in local coordinates
show that its ordinary local $H^1$ costs tend to zero. The number $N$
and constants may depend on this fixed $n$ and $f$.

For completeness, boundedness of $A,\rho$ and the coordinate coefficients
of $P,Q$ on this compact chart collection gives

$$
\|f\chi\|_{\mathcal F}^2
 \le C_{n,f}\sum_i
   \int\bigl(|\chi_i|^2+|\nabla\chi_i|^2\bigr)\,dq
 \longrightarrow0.
\tag{NT.13}
$$

Indeed $X_j(f\chi)=\chi X_jf+fX_j\chi$; both $f$ and its first
horizontal derivatives are bounded. The coordinate gradient bounds each
$X_j\chi$, which proves (NT.13) by the product rule and finite sums.
This is an upper estimate for exactly (NT.1); its closure domain and
homogeneous volume exponent have not been changed. Choose the finitely
many radii sufficiently small to make the norm at most $\varepsilon$.
On a visited point where $f\ne0$, that point lies in $K$ and $\chi=1$.
Where $f=0$, equality in (NT.9) holds automatically. This proves every
pointwise assertion, including all returns and the complete terminal leg.

To prove nonclosability, take real $0\le\varphi\le1$ in
$C_c^\infty(\Omega)$, equal to one near $o$. Every path has positive
lifetime and starts continuously at $o$. Consequently
$c_n=\nu_n(\varphi^2)>0$, with no fine-mesh qualification, and $c_n<\infty$
by $\zeta_n\le T_n$. At this fixed $n$ use (NT.9) with
$f=\varphi$ and $\varepsilon=1/j$ to obtain $u_j\to0$ in $\mathcal F_A$
while $\mathscr R_nu_j=\mathscr R_n\varphi$ for all $j$. These images
converge to a nonzero vector of squared norm $c_n$. A closable linear
operator cannot have graph closure containing $(0,v)$ with $v\ne0$.
The isometric $L^2(\nu_n)$ formulation gives the same contradiction.
Continuity of an extension of $f\mapsto\nu_n(|f|^2)$ at zero would
require $\nu_n(|u_j|^2)\to0$, whereas it equals the fixed $c_n>0$.
$\square$

## 9. Bounded smooth changing observations over the complete lifetime

**Theorem 9.1 (a positive command/diffusion gap at vanishing native form
norm).** Fix the model of Definition 7.1. For every nonzero real
$\varphi\in C_c^\infty(\Omega)$ with $0\le\varphi\le1$, and every
positive sequence $\varepsilon_n\to0$, there exist real
$h_n\in C_c^\infty(\Omega)$ with

$$
\begin{gathered}
0\le h_n\le\varphi\le1,\qquad
\operatorname{supp}h_n\subseteq\operatorname{supp}\varphi,
\qquad \|h_n\|_{\mathcal F}\le\varepsilon_n,\\
h_n(\bar q_{n,\omega}(t))=\varphi(\bar q_{n,\omega}(t))
\quad(\omega\in\Xi_n,\ 0\le t<\zeta_{n,\omega}),\\
\nu_n(h_n^2)=\nu_n(\varphi^2)\longrightarrow
 c:=\nu(\varphi^2)>0,\qquad
\nu(h_n^2)=\mathbb E_o\int_0^\tau h_n(Q_t)^2dt\longrightarrow0.
\end{gathered}
\tag{NT.14}
$$

In particular the difference of the two expected complete occupations of
the bounded smooth observable $W_n=h_n^2$ tends to $c>0$.
One may require all supports to lie in any fixed nonempty open
$U\Subset\Omega\setminus\{o\}$ by choosing $\varphi\in C_c^\infty(U)$.

Proof. Apply Theorem 8.1 with $f=\varphi$ at each $n$. Equality of
restrictions proves the exact command identity, on each actual run before
averaging. The single fixed test $\varphi^2$, extended by zero to the
closed cylinder, satisfies (NT.8). Positivity of $\Gamma$ off $o$ and
nonzero smoothness of $\varphi$ give $c>0$.

To prove the diffusion limit even when $\operatorname{supp}\varphi$
contains $o$, for every $M>0$ use $h_n^2\le1$ and write

$$
0\le\nu(h_n^2)
\le M\|h_n\|_{L^2(\mu)}^2
       +\int_{\{\Gamma>M\}}\Gamma\,d\mu.
\tag{NT.15}
$$

First let $n\to\infty$, then $M\to\infty$. Integrability of the
original full Green field makes the latter term vanish. Equation (NT.7)
identifies the expectation. In the source-free case there is the simpler
bound $\nu(h_n^2)\le(\sup_{\operatorname{supp}\varphi}\Gamma)
\|h_n\|_2^2\to0$. Cutoffs in Theorem 8.1 can lie in $U$, and
$h_n=\varphi\chi_n$ already has support in its fixed compact subset.
No control of only the first cell is used. $\square$

## 10. Normalized smooth probes on a fixed source-free region

**Theorem 10.1 (normalized, uniformly bounded form-convergent
counterfamily).** Fix any nonempty open $U\Subset\Omega\setminus\{o\}$
and any real nonnegative $u_0\in C_c^\infty(U)$ with
$\|u_0\|_{L^2(\mu)}=1$. Put

$$
B=\|u_0\|_\infty,\qquad \lambda=(1+B)^{-1}>0,
\qquad J=\nu(u_0^2)\in(0,\infty).
\tag{NT.16}
$$

For every positive $\varepsilon_n\to0$ there are nonnegative
$u_n\in C_c^\infty(U)$ of $L^2(\mu)$ norm one, supported in the same
compact $\operatorname{supp}u_0$, with

$$
\begin{gathered}
\|u_n\|_\infty\le B+1,\qquad
\|u_n-u_0\|_{\mathcal F}
 \le(1+\|u_0\|_{\mathcal F})\varepsilon_n\longrightarrow0,\\
\nu(u_n^2)\longrightarrow J,\qquad
\nu_n(u_n^2)\longrightarrow(1+\lambda)^2J,\\
\nu_n(u_n^2)-\nu(u_n^2)\longrightarrow
 (2\lambda+\lambda^2)J>0,\\
\nu_n(u_n^2)-\nu_n(u_0^2)\longrightarrow
 (2\lambda+\lambda^2)J,
\qquad \nu(u_n^2)-\nu(u_0^2)\longrightarrow0.
\end{gathered}
\tag{NT.17}
$$

Thus, even for this fixed source-free support and a uniformly bounded
normalized smooth class, no modulus $\omega(s)\to0$ as $s\downarrow0$
can bound $|\nu_n(v^2)-\nu_n(w^2)|$ by
$\omega(\|v-w\|_{\mathcal F})$ for every sufficiently large $n$ and all
members of that class. Here normalized amplitudes converge to a normalized
$u_0$; it is their difference, not their unit-norm amplitudes, that tends
to zero in the form norm.

Proof. Apply Theorem 8.1 to $f=\lambda u_0$ at mesh $n$, choosing the
cutoff inside $U$, and denote its product by $g_n$. Then
$0\le g_n\le\lambda u_0\le1$, $\|g_n\|_{\mathcal F}\le\varepsilon_n$,
and its actual trace is exactly $\lambda$ times the trace of $u_0$.
Set

$$
N_n=\|u_0+g_n\|_{L^2(\mu)},\qquad
u_n=\frac{u_0+g_n}{N_n}.
\tag{NT.18}
$$

Nonnegativity and the triangle inequality give
$1\le N_n\le1+\|g_n\|_2\le1+\varepsilon_n$.
Consequently $\|u_n\|_\infty\le B+1$, and

$$
\|u_n-u_0\|_{\mathcal F}
\le N_n^{-1}\|g_n\|_{\mathcal F}
  +|N_n^{-1}-1|\,\|u_0\|_{\mathcal F}
\le(1+\|u_0\|_{\mathcal F})\varepsilon_n.
\tag{NT.19}
$$

On every actual alive path, including terminal legs and stationary cells,
there is the exact pointwise identity

$$
u_n(\bar q_{n,\omega}(t))
 =\frac{1+\lambda}{N_n}u_0(\bar q_{n,\omega}(t)),
\qquad
\nu_n(u_n^2)=\frac{(1+\lambda)^2}{N_n^2}\nu_n(u_0^2).
\tag{NT.20}
$$

Since $N_n\to1$, (NT.8) at the fixed continuous test $u_0^2$ gives the
command limit in (NT.17). This identity does not require every coarse
mesh to visit $U$: if no path visits its support, both sides of the
corresponding command equality are zero.

On the fixed compact source-free support $K_0=\operatorname{supp}u_0$,
$\Gamma$ is bounded. Cauchy–Schwarz gives

$$
|\nu(u_n^2)-\nu(u_0^2)|
\le(\sup_{K_0}\Gamma)\|u_n-u_0\|_2
 (\|u_n\|_2+\|u_0\|_2)\longrightarrow0.
\tag{NT.21}
$$

Positivity gives $J>0$; boundedness gives $J<\infty$. All remaining
limits in (NT.17) follow by subtraction. A proposed uniform modulus,
applied to $v=u_n,w=u_0$, would tend to zero by (NT.19), contradicting
the positive last command limit. $\square$

## 11. Correspondence, suppliers and the scope of recovery

**Definition 11.1 (independent observations and the failed direction).**
The spatial information is the independently defined form element and
norm (NT.1). Command time is the ordered, actually executed clock,
controls, area and state path of (NT.3)–(NT.5), stopped at its first hit.
Boundary information is its first-hit time and height face, with the
held boundary point or cemetery convention supplied by G. None of these
is defined by an inverse of another observation. The boundary is fixed
throughout Theorems 8.1–10.1; their compactly supported probes introduce
no extra boundary condition. A retained record would instead require
actual stored outcomes, bindings and permitted later calls. No such
memory object is constructed by these mathematical traces or measures.

The precise failed direction is completion of smooth spatial data in the
original form norm followed by their restriction to these actual finite
commands. Theorem 8.1 rules out even a closable linear trace agreeing
with all smooth restrictions; Theorem 10.1 rules out a mesh-uniform
continuity modulus on the displayed normalized bounded class. On arbitrary
Borel representatives even spatial almost-everywhere equivalence is too
coarse: $E_n=C_n\cap\Omega$ has $\mu(E_n)=\nu(E_n)=0$, while
$\nu_n(E_n)=\nu_n(1)>0$. Indeed a finite smooth curve image has zero
three-dimensional chart volume, stationary points do too, and $\nu\ll\mu$.
The countable union $E=\bigcup_{n\ge1}E_n$ is a single Borel null
carrier for all $\nu_n$. This generic measure singularity is an
intermediate observation, not an additional separator theorem or an
acquired detector. The bounded smooth counterfamilies are the stronger
conclusion.

A specified smooth pointwise function remains evaluable along a specified
path. Stronger supplied data can control a trace: for example, for
$f,g\in C_c^\infty(\Omega)$ with their smooth representatives,

$$
\|\mathscr R_n(f-g)\|^2
 \le\nu_n(1)\|f-g\|_\infty^2.
\tag{NT.22}
$$

This follows by integrating the pointwise bound, and (NT.8) makes its
constant bounded over $n$ (convergence bounds the tail, and there are only
finitely many initial meshes). Such uniform spatial control, a separate
trace certificate, a changed sampling law or a field-evaluation service
is extra input beyond form distance. The inequality installs none of
them. No inverse from time or boundary back to a spatial amplitude, route
agreement for four views, dynamics conjugacy or universal physical
impossibility is inferred.

**Definition 11.2 (suppliers and the additional mathematical content).**
G, Definitions 29.1–29.2, Lemmas 29.3–29.5 and Theorem 29.6, supply the
original law, actual chronological realization, killing, resources and
complete fixed-test convergence. O, Theorems 2.1–5.1, supply the original
singular-amplitude witness and its form domain, integrability thresholds,
caps and cap-order conclusions. In particular O, Theorems 7.1–8.1,
already supply the uniform source-ball bound and the uncapped expected
bridge for the fixed observable $\Gamma^p$, $0<p<1/2$, over the complete
original lifetime. Those conclusions retain their original scope. The
changing fields of (NT.14) and (NT.17) are not a fixed test, and neither
contradict those suppliers nor prove any additional cap rate, complete
singular tail or acquisition theorem from first-cell behaviour.

Null-image facts, singular-measure separation, the logarithmic tubular
capacity calculation, the graph criterion for closability and the
integrability truncation argument are classical ingredients. Generic
singular separation is already represented by
`D5/S3/Observer/MeasureSeparation/SingularProbabilityPerfectSeparator.lean`
and its owning Blueprint Scribe, and by pinned Mathlib's
`MeasureTheory.Measure.MutuallySingular` API. The separate
`FormCorePositivityTransfer` Lean/Scribe pair requires continuity of its
form map as a premise; it cannot supply that missing premise for (NT.6).
Pinned Mathlib's Hausdorff-dimension and null-image results likewise
supply generic nullity, not this native command/form correspondence.
The additional `repo-derived` content is (NT.9), (NT.14) and (NT.17),
with the original fields, arbitrary fixed coefficients, all actual command
pieces and the full fixed-test bridge on the same source. No assertion
of worldwide priority is made.

The general trace/capacity literature includes Bahouri–Chemin–Xu,
[*Trace theorem on the Heisenberg group*](https://doi.org/10.5802/aif.2437),
§1, and Danielli–Garofalo–Nhieu,
[*Trace inequalities for Carnot–Caratheodory spaces and applications*](https://www.numdam.org/item/ASNSP_1998_4_27_2_195_0/),
§§1–2. No exact theorem from either paper is applied to (NT.6); the
cutoff estimates needed here are displayed in the proof. Altmeyer,
[*Approximation of occupation time functionals*, arXiv:1706.03418v4](https://arxiv.org/abs/1706.03418v4),
§2, explicitly distinguishes a measurable representative from its $L^2$
class. Its §2 density estimates and §3.2 heat-kernel assumptions concern
observations and Riemann estimators of the specified process itself.
At a fixed native mesh and time the law has finite support, and its
occupation is carried by $E_n$; those density premises cannot be supplied
by the density of the limiting diffusion. Thus these approximation
results are not transferred to the finite-sign producer.

The original actual-tree results of
[Native Structural Storage Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md),
§§1, 7, and [Native Paid View Conversion](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md),
§§1, 7, retain their independently declared source, acquisition and
continuation domains. Their view correspondences, the ideal response
and acquisition boundary of [Future-response sufficiency, §57](RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md),
and the common-source and legality conditions of
[Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)
and [Atlas Stable Core](RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md)
are not replaced by a cylinder trace. In particular the normalized probes
in §10 are not new acquired states of those sources. The earlier
instrument metrics and recovery results of §§1–6 keep their different
specified readouts; no identity between that quantum instrument and
(NT.6) is asserted.

**Definition 11.3 (operational and resource domain).** At mesh $n$ the
original full-word sampler requests exactly $m_n=n^3$ fair sign pairs,
hence $2n^3$ sign bits. On a realized execution at most $n^3$ alive-node
increment evaluations occur; each invokes the supplied $\Sigma,d$
evaluations, with $d$ requiring the stated coefficient derivatives.
There are at most $n^3$ random chords and one terminal height leg,
$0<\zeta_n\le n+n^{-2}$, and at most one killed partial random chord.
The finite-word description can include an unexecuted suffix. These
counts and G's variation/coordinate-energy estimates price neither exact
real arithmetic nor the source/coefficient access premises. They give
no common finite variation or energy budget as $n\to\infty$.

The finite-support description used in the cutoff existence proof ranges
over at most $4^{n^3}$ words and $(n^3+1)4^{n^3}$ curve pieces before
identical pieces are identified. It is a mathematical union, not an
executed all-branch selector on a single run. Its chart constants and
required tube radii depend on the fixed coefficients, $n$ and the desired
norm error. The proof supplies no efficient construction, certified
finite-precision radius, unknown-source oracle or installed field
evaluator. Finite formulas and exact-real coordinates do not entail
bounded bit memory. Evaluating a continuum of path values, acquiring an
expectation, and retaining callable observations require their own
measurement, reference, rights, disturbance, storage and error contracts.
There is no added hidden history, copied full trajectory or post-death
restart. Source-uniform acquisition, actual retention and later lawful
use, all four-view recovery routes and an actual alpha/beta-to-cylinder
realization remain separate obligations of the broader relational
programme. Theorems 8.1–10.1 establish the bounded analytic obstruction
without assuming those missing bridges or completing that programme.

## 追加锚（本行以下为增补区）


## 12. Scalar triangular controls and survival

**Theorem 12.1 (uniform scalar resource bounds and survival discontinuity).**
Fix real numbers $0<c<1/2$ and $\phi\in\mathbb R$, put
$a=c/2$, $Z=1-2c$, $b=(c,c,Z)$ and $I=[0,1]$, and retain the original
control class of Definition 1.1. For $n\in\mathbb N$, $n\ge1$,
$j\in\mathbb N$ and $t\in\mathbb R$, define

$$
\begin{aligned}
\tau_{n,j}(t)&=\max\bigl(0,\min(t-j/n,(j+1)/n-t)\bigr),\\
C_n(t)&=\frac c2\sum_{j=0}^{n-1}\tau_{n,j}(t),\\
k_n(t)&=\frac c2-\frac{C_n(t)}{2-t}\quad(t\ne2),
\qquad k_n(2)=\frac c2,\qquad q(t)=\phi.
\end{aligned}
\tag{ST.1}
$$

The value at $2$ specifies a total real function and does not affect its
restriction to $I$. For a real function $k$, let $k'(t)$ mean its ordinary
real derivative when it exists, with value zero otherwise, and set

$$
\begin{aligned}
h_c[k](t)&=\frac{\max(k'(t),0)}{k(t)}
            +\frac{\max(-k'(t),0)}{c-k(t)},\\
S_c[k](t)&=\exp\left(-\int_0^t h_c[k](u)\,du\right),\\
L(k,q)&=\int_0^1\sqrt{k'(t)^2+q'(t)^2}\,dt,\qquad
Q(k,q)=\int_0^1\bigl(k'(t)^2+q'(t)^2\bigr)\,dt.
\end{aligned}
\tag{ST.2}
$$

Division by zero in the total hazard formula is assigned value zero.
All integrals are real interval integrals with Lebesgue measure; an
integral with reversed endpoints has the opposite sign, and a nonintegrable
integrand is assigned integral zero. Write $V_I(f)$
for the extended nonnegative total variation of $f$ on $I$; finite real
upper bounds below are included in the extended nonnegative reals.

For every $n\ge1$ the following assertions hold simultaneously.

1. The base $b$ is valid, and $(k_n,q)$ is an original control of duration
   one. It has a finite piecewise-$C^1$ partition with continuous derivative
   rates on each closed piece, and both coordinates are absolutely
   continuous on $I$. Its endpoints satisfy $k_n(0)=k_n(1)=a$.
   For every natural $j<n$, including all endpoints of the displayed legs,

   $$
   \begin{aligned}
   C_n(t)&=\frac c2(t-j/n)
     &&\left(j/n\le t\le(j+1/2)/n\right),\\
   C_n(t)&=\frac c2((j+1)/n-t)
     &&\left((j+1/2)/n\le t\le(j+1)/n\right).
   \end{aligned}
   \tag{ST.3}
   $$

2. For every $t\in I$,

   $$
   \frac c4\le k_n(t)\le\frac c2,\qquad
   |k_n(t)-a|\le\frac{c}{4n},\qquad
   0<m:=\min(c/4,1-2c)\le p_i(k_n(t))
   \quad(i\in\{0,1,2,3,13\}).
   \tag{ST.4}
   $$

   The function $k_n$ is Lipschitz on $I$ with constant $3c/4$, and

   $$
   \begin{gathered}
   V_I(q)=0,\qquad V_I(k_n)\le3c/4,\qquad
   q'(t)=0\quad(t\in\mathbb R),\\
   L(k_n,q)\le3c/4,\qquad Q(k_n,q)\le9c^2/16.
   \end{gathered}
   \tag{ST.5}
   $$

   Both integrands defining $L(k_n,q)$ and $Q(k_n,q)$ are interval
   integrable on $[0,1]$. For Lebesgue-almost every real $t$, membership
   $t\in I$ implies

   $$
   h_c[k_n](t)=\frac1{2-t},\qquad |k_n'(t)|\le3c/4.
   \tag{ST.6}
   $$

3. For every $t\in I$, the hazard is interval integrable from $0$ to $t$
   and $S_c[k_n](t)=1-t/2$. The waiting pair $(t\mapsto a,q)$ is an
   original control on the same base and duration, and, for every real $t$,
   its hazard is zero and its survival is one.

Moreover, for every real $\varepsilon>0$ there is a natural $N\ge1$ such
that every natural $n\ge N$ is an original control as above and satisfies
$|k_n(t)-a|<\varepsilon$ for every $t\in I$. Nevertheless, for every
natural $n\ge1$,

$$
\left|S_c[k_n](1)-S_c[t\mapsto a](1)\right|=\frac12,
\qquad
\bigl(S_c[k_{n+1}](1)\bigr)_{n\in\mathbb N}
\not\longrightarrow S_c[t\mapsto a](1).
\tag{ST.7}
$$

These assertions concern the scalar hazard and the coordinate costs in
(ST.2). They impose no common upper bound on the number of pieces.

Proof. At any $t\in[j/n,(j+1)/n]$ all tents except the $j$th vanish;
neighboring tents are also zero at a shared endpoint. The remaining tent
is the smaller of the two distances to the cycle endpoints. Splitting at
the midpoint gives (ST.3), continuity of $C_n$, $C_n(0)=C_n(1)=0$, and
$0\le C_n(t)\le c/(4n)$ on $I$. Since $2-t\ge1$ and $n\ge1$, (ST.1)
gives the height bounds and error estimate in (ST.4). The five probabilities
are $(k_n,c-k_n,Z,c-k_n,k_n)$; each is at least $m>0$. The equal base
coordinates are positive, $Z>0$, and $2c+Z=1$, so the base is valid.

On every open rising leg $C_n'=c/2$, and on every open falling leg
$C_n'=-c/2$. Differentiating (ST.1) gives

$$
k_n'=-\frac{C_n'}{2-t}-\frac{C_n}{(2-t)^2}
 =\begin{cases}
 -(c-k_n)/(2-t),&\text{on rising legs},\\
 k_n/(2-t),&\text{on falling legs}.
 \end{cases}
\tag{ST.8}
$$

The expressions extend continuously to each closed leg. Together with the
constant phase they supply a finite piecewise-$C^1$ partition at the times
$j/(2n)$, $0\le j\le2n$. Integrating the continuous rates on each piece
and telescoping, including a partition truncated at any point of $I$,
expresses each coordinate as its initial value plus an integral of an
integrable derivative. Thus both coordinates are absolutely continuous.
The constant phase has finite variation, and the strict probability
bounds give the remaining original-control conditions. Formula (ST.1)
at the endpoints gives $k_n(0)=k_n(1)=a$.

The derivative formula before the case split and the bounds on $C_n$
give $|k_n'|\le c/2+c/(4n)\le3c/4$ off the finite corner set.
Absolute continuity and the fundamental theorem on every subinterval
then give $|k_n(y)-k_n(x)|\le(3c/4)|y-x|$ for $x,y\in I$.
Summing over partitions proves the variation bound. The phase derivative
and variation are zero. Its length integrand is therefore $|k_n'|$,
which is integrable by absolute continuity. The squared derivative is
measurable and dominated almost everywhere by $9c^2/16$ on the unit
interval, hence integrable. Integrating these two bounds proves (ST.5).

The height lies strictly between $0$ and $c$. In (ST.8) the rising-leg
derivative is negative and the falling-leg derivative positive.
Substitution into (ST.2) gives $h_c[k_n](t)=1/(2-t)$ away from the finite
corner set, proving (ST.6). The latter function is continuous on $I$, so
the actual hazard is interval integrable from $0$ to every $t\in I$.
Its integral is $-\log(1-t/2)$, as follows by differentiating this
primitive and evaluating at zero. Exponentiation proves
$S_c[k_n](t)=1-t/2$. For waiting, both coordinates are constant, their
probability coordinates are strictly positive, and their derivatives
vanish on all of $\mathbb R$. Thus waiting is an original control and
has zero hazard and survival one at every real time.

Given $\varepsilon>0$, choose a natural $M>c/(4\varepsilon)$ and set
$N=M+1$. For every $n\ge N$, (ST.4) gives
$|k_n(t)-a|\le c/(4n)<\varepsilon$ on $I$, while all the original-control
and resource conclusions remain valid. At time one the actual survival
is $1/2$ for every $n\ge1$, whereas waiting has survival one. This proves
the discrepancy in (ST.7). The sequence indexed by $n+1$ is constantly
$1/2$; uniqueness of real limits excludes convergence to one. $\square$
