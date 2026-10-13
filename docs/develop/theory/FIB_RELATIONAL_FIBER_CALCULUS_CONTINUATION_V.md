# FIB Relational Fiber Calculus · Continuation V
## —Source-specific old-curve precision and future root readout

> **Machine contract.** This is a `generic-v1` theory reference volume. The
> definitions and results below are ordinary mathematical prose, not Lean
> declarations, and make no kernel-verification claim. Published batches are
> append-only; the volume ends with an append anchor.

**来源。** AI-authored theory by a Codex implementation worker. This volume
is a repository-derived mathematical exposition, with prior methods cited
below; it is not user-provided original theory.

The source-specific deduction in §59 concerns the original ordered
substitution sources $T_n=\rho^n(\alpha)$, all occurrence vertices, and
centered unit counting-norm preparations. It uses the exact old root-neighbor
residual and fixed-positive-time successor root gap of
[Holographic IV, §§109--110](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md#109-a-persistent-centered-defect-for-actual-ancestry-transport).
Smoothing the two actual residual sites yields an $O(n/N_n)$ separation
bound for the entire old passive root curve after a fixed cutoff $a_0>0$.
Combined with the cited classical two-consistent-input recovery argument,
this gives a necessary absolute-error precision boundary for predicting the
specified ancestry-then-heat future on those two preparations.

The conclusion is conditional on the common full closed report-ball
contract in Definition 59.2. The comparison grants the source index to an
arbitrary decoder and supplies neither a native acquisition procedure nor
an optimal precision exponent. Section 58 records the separate obligations
for any proposed extension to a native action, controller, resource, or
randomized-record interface; those extensions are not supplied by §59.

## 58. Scope and assumptions for a native bridge

All Relational IV references in this section denote the
[immutable published edition, §§46--50](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md#46-execution-boundary-corrections).
Its corrected finite-profile and source-total contracts are the resource
supplier. The following definitions and assumptions specify what an
additional bridge would have to retain. No general signed-fiber bridge,
controller synthesis, or quotient-minimality result is asserted here.

**Definition 58.1 (complete tagged action boundary).** A complete semantic
state $q\in Q$ retains the original source, current source state, controller
position and memory, authenticated epoch, ordered history, guards and
permissions, contracted resource accumulators, and immutable target row.
Its status distinguishes pending, halt, deadlock, illegal, and undefined
cases. A halt carries the complete terminal output; non-halts have a
distinguished absent output. Halt is absorbing and deadlock permits no
progress. For every primitive action the interface records legality and
definedness separately, and, on a legal defined action, its actual visible
response, contracted event fields, and successor. A silent action has an
explicit response $\bot$. Illegal and undefined cases have distinct tags
and absent response, cost, and successor fields; a legal but undefined
operation is a contract failure. Silence, absence, failure, and termination
are separate labels.

The underlying same-source boundary and all-action response factorization
are supplied by
[Relational IV, Definitions 41.2--41.3 and 46.1, with §47's history-state correction](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md#47-uniform-finite-profile-and-history-state-correction).
The full tagging above is an explicit requirement on a proposed extension,
including cases that are not successful runs. Source/chart coordinates
remain semantic descriptions, not online source-identity inputs.

**Assumption 58.2 (observable initialization, action, update, and fixed-policy representation).**
For a proposed summary $\eta:Q\to M$, use its image as the summary space.
Require every compared status, terminal row, legality, definedness, response,
and resource label to factor through $\eta$. For each legal defined action
require one summary successor satisfying

$$
\overline T_a(\eta(q))=\eta(\operatorname{Next}(q,a)).
$$

Prediction of equal labelled futures alone is not a supplied successor
factorization. To use a quotient class as actual controller memory, require
its initialization from the available visible boundary and a
source-independent update from the current visible memory, selected action,
and received response. More generally, a policy may use a semantic summary
only when its chosen action and every required memory update factor through
the available visible history across all compatible source states. These
are additional observability assumptions, not access to a hidden class.
The all-action requirement, including silent actions, uses
[Relational IV, Definition 46.1](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md#46-execution-boundary-corrections).

For comparison of one fixed deterministic policy, declare a common response
alphabet $V$ including silence, and a total completed continuation carrier
$V^*$. At each controller state $k$, let $D_k^\pi\subseteq V^*$ be its
complete prefix-closed admitted domain, including the empty word. Let
$F_k^\pi$ record the state and edge labels along every completed word,
including selected actions, all status/failure tags, complete outputs, and
all contracted initial, event, and final resource fields. Missing or
post-terminal continuations are padded by distinct absorbing failure sinks;
this is semantic completion, not an additional legal action or charged
actual event. Equality of the residuals

$$
\mathcal R_k^\pi=(D_k^\pi,F_k^\pi)
$$

means equality of domains and full completed functions on the common
carrier, never agreement only on intersecting compatible-source domains.
Every admitted response-indexed successor must agree with the actual next
controller state on every compatible source. Compared fields must either
factor through this boundary or retain their entire same-source semantic
field, with its domain and absent cases; the latter is not online access to
source identity.

A finite completed state presentation or finite residual index is an
additional assumption for a finite fixed-policy representation. Effective
residual equality or a certified effective finite quotient is a further
assumption. Comparison across policies also requires an effectively
presented candidate family and a success decision; any claim covering a
larger controller class requires a separately proved complete enumeration.
Finite action/reply alphabets and finite chart types supply none of these
memory or effectiveness assumptions. Task-relative choices need not have
one coarsest safe partition; the existing destructive calibration example
is supplied directly by
[Relational II, §§25.2--25.4](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md#定理-252单个和任意两个历史都一步可解).
Finite-policy representation and its effective construction remain separate
from the two-preparation comparison of §59.

**Assumption 58.3 (same-source aggregation and uniformly finite profiles).**
A resource bridge declares the charged fields, units and domains, initial
accumulator, ordered aggregation $G_\Gamma$, terminal evaluation, and source
domain. For each original source $s$, it uses one actual trace $\tau_C(s)$
and defines $c_C(s)=G_\Gamma(\tau_C(s))$. A recursive aggregation retains
its initialization, all update state and inputs, and final rule; a
nonrecursive aggregation retains its whole contracted input trace.
Encoding, acquisition, address, preparation, update, arithmetic, memory,
and output costs remain separate declared fields. Sourcewise bounds and
weighted costs use these same-source values; coordinate maxima or policy
minima taken at different witnesses are not spliced into one run. The
same-run weighted objective and its distinction from coordinatewise maxima
are supplied by
[Relational IV, §§44.3--44.5, with §50's restriction](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md#50-weighted-thresholds-inherit-the-finite-profile-boundary).

For integer vector costs on a nonempty domain $D$, the resource supplier uses
$b(C)=\sup_{s\in D}c_C(s)\in(\mathbb N\cup\{\infty\})^d$ and restricts
finite-frontier witnesses to $b(C)\in\mathbb N^d$. A mixed budget still
requires one finite vector bounding every coordinate uniformly over all
sources, including coordinates unconstrained by that budget. Use the
[finite-profile alias of Relational IV, §49](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md#49-explicit-finite-feasibility-alias),
with the bounded-profile and uniform-history or exact-acceleration
certificates of
[§47](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md#47-uniform-finite-profile-and-history-state-correction)
and the exact all-infinite decision required by
[§48](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md#48-supersession-and-the-all-infinite-query).
Weighted thresholds inherit the same finite-profile restriction in
[§50](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md#50-weighted-thresholds-inherit-the-finite-profile-boundary).

Any proposed effective implementation must separately supply an exact
finite controller enumeration, source-total success and complete-row
coverage, uniform raw-event horizons or certified exact acceleration, and
uniform boundedness decisions and finite-bound extraction in every
coordinate. A per-source terminating rank or response-phase count is not
that certificate. A budget-specific horizon is not a supplied
budget-independent family horizon or boundedness decision. The resource
supplier's finite enumeration, Presburger and Dickson arguments are cited
there; they are not additional results of this volume and are not used in
§59's absolute-error-radius deduction.

**Assumption 58.4 (full-record measurability and field factorization).**
A randomized bridge first declares one seed probability space
$(U,\mathcal U,\mu)$ and one deterministic visible-response rule after
fixing the seed. For each original source $s$, require a measurable
termination time $T_s:U\to\mathbb N\cup\{\infty\}$ and a measurable
complete record $X_s$ on $\{T_s<\infty\}$ into one declared measurable
carrier. The compared record specifies its selected actions, ordered
addresses and epochs, status, output, and all contracted resource fields.
Measurability of the full record is an additional assumption, separate from
measurable wrong-return/divergence events or a measurable extended cost.

A probability law on finite complete records additionally requires
almost-sure finite termination for each source. Otherwise declare the
finite-termination subprobability law, or extend the carrier by a measurable
divergence record, specifying which divergent fields are retained or
discarded without assigning a finite completed cost to an infinite trace.
Almost-sure termination is not a uniform horizon or an expected-cost bound.

For comparison on a measurable seed event, require finite termination at
both sources and matched complete visible histories, including stopping
and status. Separately require every compared record field to be the same
measurable function of seed and that history, or supply its own
almost-everywhere equality there. A source-dependent cost, for example,
is not determined merely by a common visible reply. Equality of a declared
projection is only a comparison of that projection; it is not equality of
full records. Abstract marginal-law comparisons do not supply an agreement
event in the specified seed coupling. Section 59 uses an adversarial report
channel with no probability law over sources or preparations.

**Convention 58.5 (action order and the scope of the supplier).**
[Holographic IV, §107](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md#107-root-readout-action-closure-and-future-memory)
uses $C_\ell A^jT_w$: intervention word first, passive evolution next,
readout last. For arbitrary allowed passive/intervention interleavings,
the supplier is
[Relational II, §§44.5--44.7](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md#44-固定原生菜单的边界因子化与交错动作修正).
A native bridge must retain its own allowed ordered words, legality,
same-source branch support, resources, and absorbing Stop. Neither linear
supplier supplies those resource or full-record assumptions for a new bridge.

The chronological target of §59 is actual ancestry comparison, successor
heat, then normalized successor root readout, using
[Holographic IV, §§109--110](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md#110-root-visible-ancestry-memory-of-homogeneous-occurrence-states).
It is a signed homogeneous-state comparison, not a native original-reply
protocol. Constructing and effectively presenting a general signed FIB
interface satisfying the preceding bridge assumptions remains unproved.

## 59. Future root prediction from noisy old passive curves

**Definition 59.1 (the original source and the two comparison preparations).**
In this section Holographic IV denotes the
[immutable supplier text, §§109--110](https://github.com/the-omega-institute/trureturing/blob/0cd2d8e87296269efebb3d308ff59318aab0a10a/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md#109-a-persistent-centered-defect-for-actual-ancestry-transport).
Use the original ordered substitution sources $T_n=\rho^n(\alpha)$ and all
occurrence vertices of each source, with

$$
N_n=|V_{T_n}|=2F_{n+1}-1,\qquad
F_0=0,\quad F_1=1,\quad F_{j+2}=F_{j+1}+F_j.
$$

On the real counting space $\mathcal V_n=\ell^2(V_{T_n})$, let $L_n$ be the
closed unit-edge Laplacian, without a root killing term, and let $P_n$ be
orthogonal projection onto the zero-counting-mean subspace. Retain precisely
the actual ancestry pullback $J_n$ of Holographic IV, Definitions 109.1
and 110.1, which fixes old vertices and copies each old beta parent's value
to both its new children. Write

$$
S_n(a)=e^{-N_naL_n},\qquad
\mathcal C_nf=\sqrt{N_n}\,f(r),\qquad
\mathcal A_n=\sqrt{\frac{N_n}{N_{n+1}}}\,P_{n+1}J_nP_n.
$$

The operators and norms use every occurrence and counting measure. In
particular $\mathcal C_n$ and $\mathcal A_n$ are the normalized port and
ancestry comparison map, not the scalar finite-part quantities of
Holographic IV §92. Every root or root-neighbor smoothing norm below
restricts its input to $P_n\mathcal V_n$; the full closed counting
Laplacian and all occurrence vertices are retained.
Let $x_n\in P_n\mathcal V_n$, $n\ge2$, be the centered
unit vectors supplied by its Definition 110.1. The two preparations in this
section are $0$ and $x_n$ on the **same** deterministic old source $T_n$;
there is no probability law or mixture over sources or preparations.

Fix $a_0>0$. The optimistic old observation is the entire passive root curve

$$
\eta_n(f)(a)=\mathcal C_nS_n(a)f\quad(a\ge a_0),\qquad
\eta_n(f)\in\mathscr Y:=C_b([a_0,\infty),\mathbb R),
\quad \|y\|_\infty=\sup_{a\ge a_0}|y(a)|.
$$

Continuity follows from the finite-dimensional heat semigroup; boundedness
follows from contraction and the positive-time root smoothing bound of
Holographic IV (110.11). A supplied finite bank at declared times
$a_1,\ldots,a_m\ge a_0$ is the projection
$y\mapsto(y(a_1),\ldots,y(a_m))$, with maximum norm. Giving the entire curve
is a stronger comparison observation than giving this bank; it asserts no
native acquisition of either one.

Choose one fixed $s$ in the positive window $[s_*/2,s_*]$ of Holographic IV
Theorem 110.3, independently of $n$, and put

$$
g_{n,s}(f)=\mathcal C_{n+1}S_{n+1}(s)\mathcal A_nf,\qquad
q_n=|g_{n,s}(x_n)-g_{n,s}(0)|=|g_{n,s}(x_n)|.
$$

The actual chronological order of this target is ancestry comparison,
successor heat, then successor root readout. The supplier proves

$$
g_{n,s}(x_n)\longrightarrow D(s)\ne0,\qquad
q_n\longrightarrow |D(s)|>0,\qquad g_{n,s}(0)=0.
$$

The choice of the fixed window is essential: nonvanishing is not asserted
at every positive $s$, at a particular numerical time, or through $s=0$.

**Definition 59.2 (one common adversarial report contract).** Define the old
curve separation, a distance rather than a time, by

$$
a_n=\|\eta_n(x_n)-\eta_n(0)\|_\infty.
$$

At a prescribed radius $E\ge0$, every $y\in\mathscr Y$ with
$\|y-\eta_n(f)\|_\infty\le E$ is an allowed report for preparation $f$.
Both preparations use this same report channel. The report is the only
state-dependent datum: stopping, timing, and class tags cannot distinguish
preparations with the same report. For arbitrary predictor maps
$\widehat g_n:\mathscr Y\to\mathbb R$, define

$$
R_n(E)=\inf_{\widehat g_n}\;
 \max_{f\in\{0,x_n\}}\;
 \sup_{\substack{y\in\mathscr Y\\
                 \|y-\eta_n(f)\|_\infty\le E}}
 |\widehat g_n(y)-g_{n,s}(f)|.
$$

A predictor may depend on $n$, $a_0$, and $s$, and need not be linear,
continuous, measurable, or effectively computable. This grants the source
comparison metadata to strengthen the impossibility statement; it does not
make $n$ or $N_n$ a freely acquired native observation. The channel contract
is adversarial absolute error, not a stochastic noise model.

**Theorem 59.3 (the FIB future-readout noise and precision transfer).**
For the preparations, fixed times, normalization, and common report channel
of Definitions 59.1--59.2, there are $K_{\rm sharp}>0$ and $n_0\ge3$,
independent of $n$, such that

$$
a_n\le\frac{K_{\rm sharp}n}{N_n}\quad(n\ge n_0).
\tag{59.1}
$$

For every $n\ge2$ and $E\ge0$, the exact risk on these two preparations is

$$
R_n(E)=
\begin{cases}
0,&2E<a_n,\\
q_n/2,&2E\ge a_n.
\end{cases}
\tag{59.2}
$$

Consequently, the vanishing choice $E_n=a_n/2$ satisfies

$$
E_n\longrightarrow0,\qquad
R_n(E_n)\longrightarrow\frac{|D(s)|}{2}>0.
\tag{59.3}
$$

Every radius sequence with $E_n\ge K_{\rm sharp}n/(2N_n)$ for all
sufficiently large $n$ has the same limiting risk.

If $0\le\delta<|D(s)|/2$, any family of predictors guaranteeing worst error
at most $\delta$ on both preparations and every allowed report for all
sufficiently large $n$ must satisfy, eventually,

$$
2E_n<a_n\le\frac{K_{\rm sharp}n}{N_n}.
\tag{59.4}
$$

In particular, for the dyadic absolute-error radius $E_n=2^{-p_n}$,

$$
p_n>\log_2N_n-\log_2n+1-\log_2K_{\rm sharp},\qquad
\liminf_{n\to\infty}\frac{p_n}{n}\ge\log_2\varphi,
\quad \varphi=\frac{1+\sqrt5}{2}.
\tag{59.5}
$$

The overlap bounds also hold for any supplied finite bank in Definition
59.1 under its common maximum-norm error contract, since the bank separation
is no greater than $a_n$. Thus (59.5) remains a necessary condition for such
a bank to give the same guarantee; the bank can require still finer error
or have zero separation and prevent the guarantee even at zero radius.

Proof. Retain the exact old-field identity of Holographic IV (109.9),
with the witness normalization (109.7)--(109.8) and (110.2). For all
sufficiently large $n\ge3$, it says

$$
\begin{aligned}
x_n&=\frac{L_nH_n+P_nR_n^{\rm old}}{d_n},\\
R_n^{\rm old}
 &=u_{n,L}\delta_{v_{n,L}}+u_{n,R}\delta_{v_{n,R}},\\
\|H_n\|&\le h n\sqrt{N_n},\qquad
d_n\ge d_*\sqrt{N_n},\qquad
|u_{n,L}|+|u_{n,R}|\le U,
\end{aligned}
$$

for constants $h,d_*,U>0$ independent of $n$. Here $v_{n,L}$ and
$v_{n,R}$ are the two actual old root neighbors, and their deltas are
**node** point masses, not edge coordinates or successor vertices.
In the supplier's notation the coefficients are
$u_{n,L}=\alpha_nQ_{n-1}$ and $u_{n,R}=\beta_nQ_{n-2}$, where $Q_k$
denotes its block beta-charge sum $q_k$ from (108.10), with $|Q_k|\le2$;
this $Q_k$ is distinct from the future target gap $q_n$ here.
The contrast constants $\alpha_n,\beta_n$ are bounded by (109.5), and
$d_n/\sqrt{N_n}\to\sqrt{\kappa}>0$ by (109.8), where
$\kappa=c(2-c)$ and $c=\varphi^{-1}$. The corrector is zero
at the global root and both old subtree roots, so the two exterior root
seams contribute zero. Thus the two-neighbor support is an exact identity
on the old source, available eventually with $n_0\ge3$.
Choose $n_0$ so that all displayed bounds hold for every $n\ge n_0$.
Applying $P_n$ to (109.9) retains $P_nR_n^{\rm old}$ and uses
$P_nL_n=L_n$; the raw residual need not be centered.

Set $t=a_0/2$. The root port bound (110.11) gives

$$
\|\mathcal C_nS_n(t)\|\le B_t=\frac{V}{\sqrt{2et}},\qquad
V=\sup_j\|v_j^{\mathrm e}\|<\infty\quad(t>0),
$$

where $v_j^{\mathrm e}$ is the supplier's common-edge-carrier vector.
For either actual root neighbor $v$, write
$\mathcal C_{n,v}u=\sqrt{N_n}\,u(v)$ on $P_n\mathcal V_n$.
The unit-edge energy identity $L_n=D_n^*D_n$ of (103.1) gives, for
every centered $u$,

$$
|u(v)-u(r)|^2
 \le\sum_{\{w,w'\}\in E(T_n)}|u(w)-u(w')|^2
 =\|L_n^{1/2}u\|^2.
$$

Finite spectral calculus, on this same counting space, gives

$$
\sqrt{N_n}\,\|L_n^{1/2}S_n(t)\|
 \le\sqrt{N_n}\sup_{\lambda\ge0}
           \sqrt\lambda\,e^{-N_nt\lambda}
 =\frac1{\sqrt{2et}}.
$$

Consequently both neighbor ports satisfy

$$
\|\mathcal C_{n,v}S_n(t)\|
 \le B_t+\frac1{\sqrt{2et}}
 =\frac{V+1}{\sqrt{2et}}=:J_t.
$$

The representing vector of $\mathcal C_{n,v}$ on the centered subspace
is $\sqrt{N_n}P_n\delta_v$. Self-adjointness of $S_n(t)$ on that
subspace therefore yields

$$
\|S_n(t)P_n\delta_v\|
 =\frac{\|\mathcal C_{n,v}S_n(t)\|}{\sqrt{N_n}}
 \le\frac{J_t}{\sqrt{N_n}},\qquad
\|S_n(t)P_nR_n^{\rm old}\|
 \le\frac{UJ_t}{\sqrt{N_n}}.
$$

Keeping the support before smoothing supplies this extra
$N_n^{-1/2}$ factor. Bounding only $\|R_n^{\rm old}\|$ as in (109.10)
loses it. With $\|L_nS_n(t)\|\le1/(eN_nt)$, the exact field identity
now gives

$$
\|S_n(t)x_n\|
 \le\frac{\|L_nS_n(t)H_n\|
             +\|S_n(t)P_nR_n^{\rm old}\|}{d_n}
 \le\frac1{d_*N_n}
           \left(\frac{hn}{et}+UJ_t\right)
 \quad(n\ge n_0).
\tag{59.6}
$$

The positive semidefinite closed Laplacian makes $S_n$ a contraction
on the centered counting space. For every $a\ge a_0=2t$, split the heat:

$$
\begin{aligned}
|\mathcal C_nS_n(a)x_n|
 &\le\|\mathcal C_nS_n(t)\|\,\|S_n(a-t)x_n\|\\
 &\le B_t\,\|S_n(t)x_n\|\\
 &\le\frac{B_t}{d_*N_n}
          \left(\frac{hn}{et}+UJ_t\right)
 \le\frac{K_{\rm sharp}n}{N_n}.
\end{aligned}
\tag{59.7}
$$

The second inequality uses
$S_n(a-t)=S_n(a-2t)S_n(t)$ and $a-2t\ge0$.
It therefore covers the entire unbounded interval $[a_0,\infty)$, without
assuming that the supplier's compact-interval convergence is already
uniform there. Choose any positive

$$
K_{\rm sharp}\ge\frac{B_t}{d_*}
              \left(\frac h{et}+\frac{UJ_t}{n_0}\right).
$$

Taking the supremum in (59.7) proves (59.1), since $\eta_n(0)=0$.
The constants depend on $a_0$ and the fixed supplier family, not on $n$.
These root and neighbor smoothing bounds do not hold on the full space:
$S_n(t)$ fixes the constant mode, and the normalized ports take value $1$
on $N_n^{-1/2}\mathbf1$. Their full-space norms are therefore at least
$1$ for every $t$, whereas $B_t,J_t\to0$ as $t\to\infty$.
The projection $P_n$ and centered operator domains are essential.

For the noise step, the bounded continuous midpoint curve

$$
y_n^*=\frac{\eta_n(x_n)+\eta_n(0)}2
$$

has distance exactly $a_n/2$ from both true curves. When $2E\ge a_n$ it
is an allowed report for both preparations. Any predictor therefore assigns
the same number $z=\widehat g_n(y_n^*)$ to two targets separated by $q_n$.
The triangle inequality gives

$$
q_n\le |z-g_{n,s}(0)|+|z-g_{n,s}(x_n)|
 \le 2\max_{f\in\{0,x_n\}}|z-g_{n,s}(f)|.
$$

Taking the allowed-report supremum and then the infimum over predictor maps
proves $R_n(E)\ge q_n/2$ whenever $2E\ge a_n$.
The constant target-midpoint predictor
$\widehat g_n(y)=[g_{n,s}(0)+g_{n,s}(x_n)]/2$ has error exactly
$q_n/2$ on both preparations for every report, proving equality in this
branch. When $2E<a_n$, the two full closed report balls are disjoint:
a point in their intersection would give $a_n\le2E$ by the triangle
inequality. On their union, assign to each report the target of its unique
compatible preparation, and assign any value outside the union. This
arbitrary predictor has zero error. These two branches prove (59.2)
as an elementary classical intermediate for this source comparison;
the decoder is not claimed measurable or effective.
The shared-report midpoint/radius-of-information step is a classical
optimal-recovery ingredient; see Micchelli and Rivlin, *A Survey of Optimal
Recovery*, in *Optimal Estimation in Approximation Theory*,
[doi:10.1007/978-1-4684-2388-4_1](https://doi.org/10.1007/978-1-4684-2388-4_1),
and the bounded-error optimal-recovery setting of Foucart and Liao,
*Optimal Recovery from Inaccurate Data in Hilbert Spaces: Regularize, But
What of the Parameter?*,
[doi:10.1007/s00365-022-09590-5](https://doi.org/10.1007/s00365-022-09590-5).
The same two-consistent-input triangle-inequality step appears explicitly in
the proof of Theorem 1 of Foucart, *Learning the maximum of a Hölder function
from inexact data*,
[doi:10.1090/proc/17456](https://doi.org/10.1090/proc/17456).
Only that lower-bound ingredient is used: no sufficient recovery theorem,
Hilbert-space regularization rule, or Hölder-model hypothesis is transferred
to the curve carrier. The displayed argument proves the needed step directly.

Binet's formula and $N_n=2F_{n+1}-1$ give

$$
\frac n{N_n}\longrightarrow0,\qquad
\frac{\log_2N_n}{n}\longrightarrow\log_2\varphi,\qquad
\frac{\log_2n}{n}\longrightarrow0.
$$

Thus (59.1) implies $a_n\to0$, whereas the supplier's fixed-$s$ limit
gives $q_n\to|D(s)|>0$. By (59.2), substituting $E_n=a_n/2$ gives
$R_n(E_n)=q_n/2$, proving (59.3).
If $E_n\ge K_{\rm sharp}n/(2N_n)$, (59.1) also implies $2E_n\ge a_n$,
so the same exact risk and limit hold eventually.
For a fixed $\delta<|D(s)|/2$, eventually $q_n>2\delta$.
Then overlapping report balls would contradict a worst-error guarantee of
$\delta$ by (59.2), proving (59.4). With $E_n=2^{-p_n}$, (59.4) gives
$2^{1-p_n}<K_{\rm sharp}n/N_n$. Taking logarithms of these positive
quantities and using the displayed growth limits proves (59.5).
For a finite bank its projected midpoint is again allowed at both
preparations, and its separation is bounded by the full-curve separation;
the same argument applies. $\square$

**Convention 59.4 (scope, degeneracies, and provenance).** If $a_n=0$ at
some finite $n$ with $q_n>0$, even the zero-radius report is shared and
$R_n(0)=q_n/2$. If $a_n>0$, however, $E_n=a_n/4$ gives zero two-state
risk by (59.2); along indices with positive separation these radii also
tend to zero. In particular, if $a_n>0$ eventually, this is a vanishing
noise sequence with eventually zero risk, so vanishing noise alone does
not force failure under that condition.
The theorem takes no logarithm of $a_n$ and presumes no strictly positive
finite-$n$ old curve gap. Its arbitrary two-point decoder supplies neither
recovery on the entire original source or field domain nor a finite
actual-history acquisition procedure.

The exponent in (59.5) is necessary for the declared dyadic **absolute-error
radius** under this common channel. No matching lower bound on $a_n$ or
general-domain recovery upper bound is supplied, so this exponent is not
claimed optimal. It is not a sufficient precision algorithm or a storage
optimum: it counts neither representations of an entire curve nor acquired
index metadata. It supplies no physical energy or
duration law. The observation cutoff $a_0$ and successor readout time $s$
are fixed positive comparison times; the proof supplies no uniform bound
as $a_0\downarrow0$, and no conclusion is drawn for observation times tending
to zero with $n$.

Normalization is part of the target. With ordinary unnormalized successor
root evaluation on the same unit counting-norm inputs and map $\mathcal A_n$,
$g_{n,s}(x_n)$ is divided by $\sqrt{N_{n+1}}$ and tends to zero, as in
Holographic IV §110.5. That target does not have the fixed positive gap used
in (59.3)--(59.5). Changing instead to the pointwise fields
$\sqrt{N_n}x_n$ changes the input scale and its noise contract; it is not
an unchanged precision claim.

This is `repo-derived` source-specific composition of Holographic IV
(109.7)--(109.10) and §§110.1--110.5, using its unit-edge identity (103.1),
with the cited `literature-attested` optimal-recovery ingredient;
no claim of originality is made for the composition. The
uncertainty here is between signed homogeneous preparations, not between
two native root-query replies or two separate source-size experiments.
Native preparation of these signed fields and realization of heat, both
centering projections, ancestry transfer, and real root ports through $\mathsf{Read}$ and
$\mathsf{ApplyRho}$ remain unproved. A bridge would have to preserve the
same actual source and joint action history, immutable target, epoch and
presence guards, permissions and refusals, absorbing Stop, and every
declared preparation, acquisition, address, update, arithmetic, memory, and
output cost required by Holographic IV §110.5. Comparison time remains
separate from physical duration until that correspondence is proved.
These are ordinary paper statements, without a Lean/kernel-verification
claim.

## 追加锚（本行以下为增补区）
