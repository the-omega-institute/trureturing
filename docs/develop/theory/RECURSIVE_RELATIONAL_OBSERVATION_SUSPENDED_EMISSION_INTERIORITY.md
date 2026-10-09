# Suspended-emission interiority for common complete-tail configuration risks

## 1. One source-specific compatibility statement

**Mathematical status.** The new results in this volume have ordinary mathematical proofs. They have no Lean kernel verification or frozen formal status; their formal claims remain open in this repository. The source-specific argument, rather than a finite enumeration or numerical optimization, bears the universal quantifiers below.

**Definition 1.1 (source parameters and radii).** Put

$$
a=1/3,
\qquad b=2/5,
\qquad d_p=1116529/11390625,
\qquad d_\beta=239/3375,
\qquad \rho_s=d_s/2.
$$

The actual source is the original stopped Fibonacci source of [ST], [CLIP] and [PAID]. Its installed finite or countable depth prior has positive mass at depths 1 and 2 and at at least one depth $k\ge3$. Define the supplied positive interior excursion

$$
\eta=\frac{14219478376}{318644812890625}.
\tag{1.1}
$$

The source, observer, full-tail risks and marginalized conditioning defect are specified in Section 2.

**Definition 1.2 (interior suspended emission mass).** For an allowed observer $M$, let $v_y$ be its next synthetic alpha probability at a suspended configuration $y$. At a positive actual suspended history $h$, let $\rho_h$ be its actual conditional configuration row. Set

$$
\psi(t)=\min\{(t-a)_+,(b-t)_+\},
\qquad
\mathcal I_h(M)=\sum_y\rho_h(y)\psi(v_y),
\qquad
\mathcal I(M)=\sup_{h\in\mathcal H_\beta}\mathcal I_h(M).
\tag{1.2}
$$

Here $(t)_+=\max(t,0)$. The tent function $\psi$ vanishes outside $(a,b)$ and equals the distance to the nearer endpoint inside $[a,b]$. The row is an analysis object. It is not a runtime probability-vector input. This statistic is neither an alpha-edge change nor complete-return motion: it concerns the present suspended emission itself.

Write

$$
e(M)=\max\{R_{\mathrm{conf},p}(M)-\rho_p,
                 R_{\mathrm{conf},\beta}(M)-\rho_\beta\}.
\tag{1.3}
$$

**Theorem 1.3 (necessary suspended emission interiority).** Every finite COMPLETE observer on every prior of Definition 1.1 satisfies

$$
61e(M)+15\mathcal I(M)
>\frac{11\eta}{300000}>0.
\tag{1.4}
$$

In particular, in the entire class with no reachable suspended emission strictly between $a$ and $b$,

$$
\inf_M e(M)\ge\frac{11\eta}{18300000}.
\tag{1.5}
$$

Exact common conf/conf attainment requires

$$
\mathcal I(M)>\frac{11\eta}{4500000}.
\tag{1.6}
$$

If a sequence has both configuration excesses tending to zero, then

$$
\liminf_n\mathcal I(M_n)\ge\frac{11\eta}{4500000}.
\tag{1.7}
$$

State counts, kernels and supported priors may vary along this sequence, provided each member obeys the same source contract and has a supported nonendpoint.

The new ingredient is the short-word forcing and stationary balance proved in Sections 3–5. The two suspended coordinates $\alpha w_{1,1}$ and $\alpha w_{2,1}$ have the opposite endpoint order from their p residual coordinates. When the suspended emission equals an endpoint, this forces its actual alpha successors toward the corresponding p endpoint coordinates. Both unweighted acquired flows then give a switching balance incompatible with simultaneous endpoint event calibration, unless the full p laws approach the fair native endpoint tags. The supplied interior loss rules out that last possibility.

The new inequality is specific to conf/conf. No analogous new restriction is proved for law/law, law/conf or conf/law; their supplied attainments [MIXED; SWITCH] retain their original scopes. The proof requires both configuration-before-TV bounds.

The theorem gives no unrestricted positive gap: $\mathcal I$ is free in the original model class. It constructs no exact common attainer or vanishing-excess family, and gives no fixed-resource optimum.

## 2. The unchanged source and complete finite observers

**Definition 2.1 (actual source and original execution).** Fix $m=2,d=1,\ell=2,n=4$, with $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$. Before the first actual Read draw one $K$ from one installed finite or countable prior $\mu$. Conditional on that same $K=k$, every seed and payload Read is independent, with alpha probability

$$
r_k=F_{k+1}/F_{k+3},
\qquad r_1=a,
\qquad r_2=b,
\qquad r_k\in I_0=[3/8,5/13]\quad(k\ge3).
$$

Equal seed pairs are paid rejections. Alpha-beta accepts seed 0 and beta-alpha accepts seed 1. In payload phase p, alpha completes marker 0 and beta suspends. At suspension, alpha returns to p and beta completes marker 1. The first three completions advance segments. The third record is written before its latch. Fourth completion enters the matching pendingStop; its unique original Stop enters deliveredStop. Neither terminal admits Read.

Retain the full original finite control $C_0$: both seeds, parser, selectors, bare fields, full marker tree, held $B,Q^+,Z$ records, write/latch flags, permissions, completion and Stop delivery. Both seeds, all marker triples and all positive finite rejection and return histories stay in the domain. There is no source reset, fresh depth, future-event conditioning, additional actual observation, controller port or post-Stop operation.

$\mathcal H_3$ is the first fourth-segment p cut after the third latch. $\mathcal H_p$ and $\mathcal H_\beta$ contain all positive finite fourth-segment p and suspended histories, including arbitrary finite returns. The proof uses the full $\mathcal H_p$, not just $\mathcal H_3$.

**Definition 2.2 (complete residual law).** Put $a_r=r(1-r)$ and

$$
w_{j,0}=(\beta\alpha)^j\alpha,
\qquad
w_{j,1}=(\beta\alpha)^j\beta\beta,
\qquad j\ge0.
$$

The p carrier consists of these finite words and its unique infinite noncompletion word. The suspended carrier consists of beta, $\alpha w_{j,c}$ and its infinite noncompletion word. The already acquired suspended beta is not a future Read. Fixed-parameter masses are

$$
P_{p,r}(w_{j,0})=ra_r^j,
\qquad P_{p,r}(w_{j,1})=(1-r)^2a_r^j,
$$

$$
P_{\beta,r}(\beta)=1-r,
\qquad
P_{\beta,r}(\alpha w_{j,0})=r^2a_r^j,
\qquad
P_{\beta,r}(\alpha w_{j,1})=r(1-r)^2a_r^j.
\tag{2.1}
$$

Both infinite-word masses are zero. The current-record renderer $I_c$ retains every future Read and inserts its original event blocks, held records, permissions, completion and Stop. Reading back the letters is its inverse. This measurable bijection preserves TV and commutes with deleting the next original operation and its block [ST, Section 2.1].

At a positive acquired history $h$, including every paid rejection and partial parse in its letter counts,

$$
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
 {\sum_j\mu(j)r_j^{A(h)}(1-r_j)^{B(h)}},
\qquad
T_h^\mu=(I_{C_0(h)})_*\sum_k\nu_h(k)P_{s,r_k}.
\tag{2.2}
$$

The denominator is positive. The same actual $K$ supplies all acquired and unread letters. Counts and posterior probabilities are analysis quantities only.

**Definition 2.3 (observer, exact generation and risks).** An observer has one fixed finite COMPLETE configuration set, source-independent initialization and fixed time-homogeneous source-independent acquired-letter stochastic kernels. COMPLETE includes the original control, records, permissions, program/table selectors, workspace, addresses, output indices and all persistent randomness. Runtime reads its actual configuration only. It receives no continuous register, readable state-distribution or posterior vector, uncounted tape, correlated source seed, clock, archive or advice.

Every configuration's decoder is the complete law generated by its synthetic emissions and these same acquired-letter kernels. For a legal next operation $o$ and residual event $E$,

$$
D_z(oE)=q_z(o)\sum_{z'}P_o(z,z')D_{z'}(E).
\tag{2.3}
$$

The cylinder includes the entire original event block. This identity remains valid when $q_z(o)=0$; the actual kernel still exists. Synthetic generation never queries the actual source. A decoder describes a finite installed generator and current configuration, not an infinite probability table or an exact-real physical oracle.

With actual conditional configuration row $\rho_h$, define

$$
\overline D_h=\sum_z\rho_h(z)D_z,
\qquad
e_{\mathrm{law}}(h)=\operatorname{TV}(\overline D_h,T_h^\mu),
$$

$$
e_{\mathrm{conf}}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu),
\qquad
R_{j,s}=\sup_{h\in\mathcal H_s}e_j(h).
\tag{2.4}
$$

TV is the event-supremum convention, equivalently half the countable $\ell^1$ distance on these fourth-segment carriers. Configuration-before-TV, marginal-law TV and actual-history-average loss are different quantities. The supplied terminal-projection minima are $13/266$ and $9/266$ [ST, Theorems 2.1 and 3.1]. The present full-tail radii are $1116529/22781250$ and $239/6750$; the original finite positive-history lower witnesses are supplied by [ST, Sections 2.3 and 3.1–3.3].

For a positive actual history and legal next operation $o$ with predicted probability $q_h(o)>0$, let $\operatorname{res}_o\overline D_h$ be its conditional law after deleting $o$ and its original block. Retain the original marginalized defect

$$
\delta(h,o)=\operatorname{TV}(\operatorname{res}_o\overline D_h,\overline D_{ho}).
$$

Here $q_h(o)=\overline D_h([o])$. At $q_h(o)=0$ set the defect to zero without creating a conditional law. The actual successor and its risk remain in the domain. Zero defect means exactly these conditional equalities on positive predicted operation cylinders; it does not relax (2.3). $\Delta_4$ and $\Delta_{\mathrm{all}}$ take the fourth-segment and full original-operation suprema. PendingStop has zero defect and deliveredStop has empty supremum zero. Only marginalized conditioning/update coherence is relaxed; (2.3) stays exact.

Theorem 1.3 imposes no defect budget and therefore includes the subclass with exact zero marginalized defect. It supplies no recovery construction when a defect bound tends to zero. Achievable coordinates are the tuples of all four phase risks, both defects and counted resources produced by one allowed observer on one installed source/prior. Neither independent phase minima nor proof-comparison tables supply a joint attaining tuple for the original observer.

**Mathematical citation 2.4 (reused stationary comparison).** [MIXSEP, Lemma 2.1], [PAID, Lemma 14.1] and [CLIP, Theorem 3.1] supply the following common-object comparison. From any allowed observer extract one original held-record fibre, finite sets $X,Y$, its original acquired kernels $B:X\to Y$, $A:Y\to X$, copied raw complete laws and rows

$$
\pi B=\tau,
\qquad \tau A=\pi.
\tag{2.5}
$$

For every supported depth, both configuration losses on these rows are no greater than the original phase risks. Every bounded nonnegative suspended-state statistic is bounded on $\tau$ by its worst-positive-history expectation. These are common paid-history limits and stationary analysis rows, not new actual observations or runtime inputs.

Delete zero-row labels first; the nonnegative flow equations forbid transitions from positive-row labels into them. Clipping both emissions to $[a,b]$, retaining the restricted $B,A,\pi,\tau$ and regenerating the complete laws, gives a finite regular stationary table with

$$
\widehat\varepsilon_p\le(41\varepsilon_p+20\varepsilon_\beta)/11,
\qquad
\widehat\varepsilon_\beta\le(12\varepsilon_p+41\varepsilon_\beta)/11.
\tag{2.6}
$$

Thus its maximal configuration excess is at most $61e/11$. The supplied clipping coupling covers arbitrary original emissions, including zero or one and possible original noncompletion mass. For a regular stationary table, all-positive-history risks equal the supported pure-target suprema [CLIP, Proposition 2.3]. These comparisons preserve neither a hard defect budget nor a fixed COMPLETE resource budget.

The original paid-history extraction fixes the suffix $\beta\alpha\mid\beta\beta\alpha\alpha$, accepting seed 1 and markers 100 before the third write and latch. Equal-pair matrix powers converge along recurrent periods; rejection proportions expose each supported depth while the observer row converges to one common row. Competing likelihood ratios decay by the Bernoulli KL divergence. The bounded rounding errors and summable prior masses permit dominated convergence for the entire countable posterior. Appending each finite return and taking a Cesaro row gives (2.5). This source mechanism is reused rather than asserted for a changed experiment.

## 3. Opposite word orders force conditional successors

**Definition 3.1 (regular stationary table).** For the rest of Sections 3–5, $\pi,\tau$ are finite probability rows, $B,A$ are row-stochastic kernels satisfying (2.5), and $u_x,v_y\in[a,b]$. From each row the exact complete raw laws satisfy

$$
Q_x=u_x\delta_\alpha+(1-u_x)\beta\sum_yB_{xy}W_y,
$$

$$
W_y=(1-v_y)\delta_\beta+v_y\alpha\sum_xA_{yx}Q_x.
\tag{3.1}
$$

Use the original product realization: fair synthetic letters before the third latch, an independent $\pi$ sample after the third write and latch in that same update, $B$ on p-beta, $A$ on suspended-alpha and original terminal updates on completing letters. All original fibres retain their own records. Every return has synthetic survival at most $\lambda=4/15$, so the full laws normalize without conditioning on completion. Legal infinite outcomes remain and have zero mass.

Put

$$
\varepsilon_s=R_{\mathrm{conf},s}-\rho_s\ge0,
\qquad e=\max(\varepsilon_p,\varepsilon_\beta).
$$

**Mathematical citation 3.2 (endpoint box slack).** The supplied coordinate triangle identity [CLIP, equation (3.6)] gives

$$
\sum_x\pi_x\sum_w
\operatorname{dist}\bigl(Q_x(w),[P_{p,a}(w)\wedge P_{p,b}(w),
                                    P_{p,a}(w)\vee P_{p,b}(w)]\bigr)
\le2\varepsilon_p.
\tag{3.2}
$$

The suspended analogue has bound $2\varepsilon_\beta$. Include the infinite outcome in both sums. This is a consequence of the two configuration losses, not an assumption of pointwise preservation.

The positive-difference events and their endpoint masses are supplied:

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},
\quad
P_{p,a}(E_p)=412/729,
\quad P_{p,b}(E_p)=7299/15625,
$$

$$
E_\beta=\{\beta,\alpha w_{0,1}\},
\quad
P_{\beta,a}(E_\beta)=22/27,
\quad P_{\beta,b}(E_\beta)=93/125.
$$

If $C_s$ is the midpoint of these two masses, the endpoint configuration bounds imply

$$
|\pi Q(E_p)-C_p|\le\varepsilon_p,
\qquad |\tau W(E_\beta)-C_\beta|\le\varepsilon_\beta.
\tag{3.3}
$$

Indeed projection to the event contracts TV, and averaging before the event difference can only decrease configuration loss.

**Definition 3.3 (two early complete-word coordinates).** Set

$$
g_x=Q_x(w_{0,1}),
\qquad f_x=Q_x(w_{1,1}),
\qquad t_x=Q_x(w_{2,1}).
$$

For $r\in\{a,b\}$ put

$$
G_r=(1-r)^2,
\qquad F_r=r(1-r)^3,
\qquad T_r=r^2(1-r)^4,
\qquad c_r=rF_r.
$$

Their values are

| $r$ | $G_r$ | $F_r$ | $T_r$ | $c_r$ |
| --- | --- | --- | --- | --- |
| $a$ | $4/9$ | $8/81$ | $16/729$ | $8/243$ |
| $b$ | $9/25$ | $54/625$ | $324/15625$ | $108/3125$ |

In particular

$$
F_a>F_b,
\quad T_a>T_b,
\quad aF_a<bF_b,
\quad aT_a<bT_b.
\tag{3.4}
$$

The last two inequalities are the reversed order at suspension.

**Lemma 3.4 (conditional endpoint forcing).** Suppose every $v_y\in\{a,b\}$. Define a probability row on the finite analysis pairs $(r,x)$ by

$$
\zeta(r,x)=\sum_{y:v_y=r}\tau_yA_{yx}.
\tag{3.5}
$$

Its $x$ marginal is $\pi$. With

$$
\delta=4\varepsilon_p+6\varepsilon_\beta,
$$

one has

$$
\mathbb E_\zeta|f_x-F_r|\le\delta,
\qquad
\mathbb E_\zeta|t_x-T_r|\le\delta.
\tag{3.6}
$$

The analysis mark $r$ is a predecessor emission, not a new source parameter or runtime posterior port.

**Proof.** Treat either coordinate $q_x=f_x$ or $q_x=t_x$, writing its endpoint values as $q_a>q_b$. The corresponding suspended word has endpoint interval $[aq_a,bq_b]$ by (3.4), and its row probability is $v_y(Aq)_y$ by exact own generation.

For $v_y=a$, the elementary absolute-value identity gives

$$
\sum_xA_{yx}|q_x-q_a|
=q_a-(Aq)_y+2\sum_xA_{yx}(q_x-q_a)_+
$$

$$
\le \frac{(aq_a-a(Aq)_y)_+}{a}
       +2\sum_xA_{yx}\operatorname{dist}(q_x,[q_b,q_a]).
$$

For $v_y=b$ the analogous identity gives

$$
\sum_xA_{yx}|q_x-q_b|
\le \frac{(b(Aq)_y-bq_b)_+}{b}
       +2\sum_xA_{yx}\operatorname{dist}(q_x,[q_b,q_a]).
$$

Multiply by $\tau_y$ and sum over the two groups. The selected suspended outside-box violations have total at most $2\varepsilon_\beta$ by (3.2). Their divisors are at least $a=1/3$. The p violations have total at most $2\varepsilon_p$, since $\tau A=\pi$. Thus the sum is at most $6\varepsilon_\beta+4\varepsilon_p$. This proves both inequalities. No successor is presampled into the original decoder, and no configuration risk is replaced by a mean risk. $\square$

## 4. Both acquired flows impose an incompatible switching balance

**Definition 4.1 (analysis transitions and ideal zero-slack coordinates).** On (3.5), the original acquired return induces

$$
K((r,x),(r',x'))=
\sum_{y:v_y=r'}B_{xy}A_{yx'}.
\tag{4.1}
$$

The row $\zeta$ is stationary for $K$: sum over the old mark and $x$, use $\pi B=\tau$, and recover (3.5). This extends only an analysis coupling; the copied decoded law remains $Q_x$.

Put

$$
\theta_x=\sum_{y:v_y=b}B_{xy},
\qquad c_x=c_a+(c_b-c_a)\theta_x,
\qquad d_x=(1-a)-(b-a)\theta_x,
$$

$$
u^*_{r,x}=1-T_r/c_x,
\qquad g^*_{r,x}=T_rd_x/c_x.
\tag{4.2}
$$

These are auxiliary rational functions with positive denominator $c_x\ge c_a$. They are not installed forecasts. The denominator $c_x$ increases with $\theta_x$, so $1-T_r/c_x$ increases as well. For $r=a$ its endpoint values are $a$ and $7183/19683$; for $r=b$ they are $11567/31250$ and $b$. All four belong to $[a,b]$, proving $u^*_{r,x}\in[a,b]$ for every $\theta_x\in[0,1]$.

**Lemma 4.2 (coordinate errors).** In the endpoint-suspended table,

$$
\mathbb E_\zeta|g_x-g^*_{r,x}|\le\frac{513}{20}\delta,
\qquad
\mathbb E_\zeta|u_x-u^*_{r,x}|\le\frac{1539}{40}\delta.
\tag{4.3}
$$

**Proof.** From (3.1),

$$
g_x=(1-u_x)d_x,
\qquad
t_x=(1-u_x)\sum_yB_{xy}v_y\sum_{x'}A_{yx'}f_{x'}.
$$

Replacing $f_{x'}$ by $F_{v_y}$ in the second formula changes its $\pi$-average absolute value by at most

$$
\frac23\frac25\sum_{y,x'}\tau_yA_{yx'}|f_{x'}-F_{v_y}|
\le\frac4{15}\delta.
$$

Together with (3.6) this yields

$$
\mathbb E_\zeta|(1-u_x)c_x-T_r|\le\frac{19}{15}\delta.
\tag{4.4}
$$

Multiply this residual by $d_x/c_x\le(2/3)/c_a=81/4$ for the first bound, and by $1/c_x\le1/c_a=243/8$ for the second. The resulting factors are $513/20$ and $1539/40$. $\square$

**Definition 4.3 (switching mass and deficits).** Set $w=\zeta\{r=a\}$ and

$$
J=\mathbb E_\zeta[\mathbf1_{r=a}\theta_x]
 =\mathbb E_\zeta[\mathbf1_{r=b}(1-\theta_x)].
\tag{4.5}
$$

The equality follows from stationarity of the mark: its next high-mark probability is $\pi\theta=\tau\{v=b\}=1-w$. Hence the low-to-high and high-to-low masses balance.

Put

$$
L=\mathbb E_\zeta[\mathbf1_{r=a}(G_a-g^*_{a,x})],
\qquad
H=\mathbb E_\zeta[\mathbf1_{r=b}(g^*_{b,x}-G_b)]
$$

and

$$
k_a=G_a(c_b-c_a)+T_a(b-a)=1664/759375,
$$

$$
k_b=G_b(c_b-c_a)+T_b(b-a)=832/421875.
$$

Subtraction in (4.2) gives

$$
G_a-g^*_{a,x}=k_a\theta_x/c_x,
\qquad
g^*_{b,x}-G_b=k_b(1-\theta_x)/c_x.
\tag{4.6}
$$

Thus $L,H\ge0$, and the common switching mass in (4.5) implies

$$
H\le R L,
\qquad
J\le(c_b/k_a)L,
\qquad
R=\frac{k_bc_b}{k_ac_a}=\frac{59049}{62500}<\frac{19}{20},
\qquad c_b/k_a=6561/416<16.
\tag{4.7}
$$

**Lemma 4.4 (two endpoint calibrations bound switching).** Define

$$
S_p=\varepsilon_p+\frac{553}{20}\delta,
\qquad
S_\beta=\varepsilon_\beta+\frac{513}{50}\delta.
$$

Then

$$
|d_p(w-1/2)-L+H|\le S_p,
$$

$$
|d_\beta(w-1/2)-aL+bH|\le S_\beta.
\tag{4.8}
$$

Consequently

$$
L\le4100e,
\qquad H\le L,
\qquad d_p|w-1/2|\le L+281e.
\tag{4.9}
$$

**Proof.** The actual mean p event mass is $\pi(g+f+t)$. Replacing its three coordinates by $g^*_{r,x},F_r,T_r$ changes it by at most $(513/20+2)\delta=553\delta/20$. The replacement mean is

$$
w\varphi_p(a)+(1-w)\varphi_p(b)-L+H,
\qquad \varphi_p(r)=(1-r)^2(1+a_r+a_r^2).
$$

Use (3.3) to get the first inequality in (4.8).

The actual mean suspended event mass is

$$
\tau(1-v+vAg)=\mathbb E_\zeta[1-r+rg_x].
$$

Replacing $g_x$ by $g^*_{r,x}$ changes this by at most $(2/5)(513/20)\delta=513\delta/50$. Its replacement mean is

$$
w\varphi_\beta(a)+(1-w)\varphi_\beta(b)-aL+bH,
\qquad \varphi_\beta(r)=1-r+r(1-r)^2.
$$

Again (3.3) gives the second inequality. Both comparisons use the same $w,L,H$ and actual circulation.

Put $q=d_\beta/d_p=806625/1116529<3/4$. Eliminate $w-1/2$ in (4.8), and use (4.7):

$$
[(q-a)-(q-b)R]L\le qS_p+S_\beta.
\tag{4.10}
$$

Here

$$
(q-a)-(q-b)R
=\frac{3048936419}{36094687500}>2/25.
$$

Since $\delta\le10e$, one has $S_p\le281e$ and $S_\beta\le111e$. Thus

$$
L\le\frac{25}{2}\left(\frac34\,281+111\right)e<4100e
$$

when $e>0$; the non-strict bound also holds at $e=0$. Finally (4.7) gives $H\le L$, and the first inequality of (4.8) gives $d_p|w-1/2|\le|L-H|+S_p\le L+281e$. $\square$

## 5. The full-tail and supported-interior implication

**Lemma 5.1 (one full-law comparison).** Define

$$
D_0=\mathbb E_\zeta\operatorname{TV}(Q_x,P_{p,r}).
$$

Then

$$
D_0\le600e+31L.
\tag{5.1}
$$

**Proof.** The same subtraction used in (4.6) gives

$$
u^*_{a,x}-a=U(G_a-g^*_{a,x}),
\qquad
b-u^*_{b,x}=U(g^*_{b,x}-G_b),
\qquad U=311/624<1/2.
$$

With (4.3),

$$
\mathbb E_\zeta|u_x-r|
\le\frac{1539}{40}\delta+U(L+H)
\le390e+L.
\tag{5.2}
$$

Couple the complete generator from the analysis pair $(r,x)$ to the native fixed-parameter source with parameter $r$, holding that reference parameter fixed for its entire future. Couple the first p emission maximally. Its mismatch probability is $|u_x-r|$. After a matched beta, use the original $B$ row. If its suspended emission mark differs from the current reference mark, declare this coupling unsuccessful; otherwise the suspended emissions agree exactly. A matched alpha uses the original $A$ row and continues with the same mark.

The two types of acquired mark changes have total stationary probability $2J$, so the declared-failure term is at most $(2/3)2J$. The successful continuation subrow is bounded entrywise by $\lambda K$, with $\lambda=4/15$, and $\zeta K=\zeta$. Therefore the configuration-average full-law comparison satisfies

$$
D_0\le\mathbb E_\zeta|u_x-r|+\frac43J+\frac4{15}D_0.
\tag{5.3}
$$

This follows either from the complete-law coupling or by applying its cylinder recursion to finite future partitions and passing to their increasing refinement. Both generators complete almost surely by the regular survival bound, and the unique infinite outcomes remain in the carrier with zero mass. No finite-word approximation is treated as the complete law.

Use $J\le16L$ from (4.7), (5.2), and divide by $1-4/15$:

$$
D_0\le\frac{15}{11}\left(390e+\frac{67}{3}L\right)
\le600e+31L.
$$

The mark is used only to choose a reference law in this proof. The original decoder still reads $x$ and has complete law $Q_x$. $\square$

**Theorem 5.2 (evaluated gap for every endpoint-suspended shape).** Every finite regular stationary table with $v_y\in\{a,b\}$ and a supported nonendpoint satisfies

$$
e>\eta/300000.
\tag{5.4}
$$

**Proof.** Reuse the supplied source-specific excursion [DIRECTION, Section 5]: for every $r\in I_0$,

$$
P_{p,r}(w_{3,1})-\max\{P_{p,a}(w_{3,1}),P_{p,b}(w_{3,1})\}\ge\eta.
$$

It follows by the coordinate triangle identity that

$$
\frac{\operatorname{TV}(P_{p,a},P_{p,r})+
       \operatorname{TV}(P_{p,b},P_{p,r})}{2}
\ge\rho_p+\eta/2.
\tag{5.5}
$$

Changing the fair tag weights to $(w,1-w)$ changes this average by at most $d_p|w-1/2|$, since the two distances differ by at most $d_p$. The $x$ marginal of $\zeta$ is $\pi$, so reverse triangle and (5.1) give, for the same supported $r$,

$$
\pi\operatorname{TV}(Q_x,P_{p,r})
\ge\rho_p+\eta/2-d_p|w-1/2|-D_0.
$$

The left side is at most $\rho_p+\varepsilon_p$. Thus (4.9) and (5.1) imply

$$
\eta/2\le\varepsilon_p+L+281e+600e+31L
\le132082e.
$$

In particular $e>0$, and $264164<300000$ gives (5.4). This conclusion is uniform in all finite label counts and all stochastic kernel entries. A supported interior depth is consumed as an actual full configuration-loss target; it is not an arbitrary diagnostic target or a replacement mean loss. $\square$

## 6. Rounding one emission vector and returning to arbitrary observers

**Lemma 6.1 (rounding comparison on the same actual flow).** In any regular stationary table, put

$$
I=\sum_y\tau_y\min\{v_y-a,b-v_y\}.
$$

Round $v_y$ to its nearer endpoint, choosing $a$ at a tie. Retain $u,B,A,\pi,\tau$ and regenerate both complete laws using these same updates. The new table has endpoint suspended emissions and maximal configuration excess at most

$$
e+15I/11.
\tag{6.1}
$$

**Proof.** The actual rows and both acquired flows are unchanged. Let $d_p'$ and $d_\beta'$ be the row-averaged complete-law TV changes. Couple only the changed suspended emissions, using identical acquired update rows after a matched letter. Convexity, regular emissions and stationarity give

$$
d_p'\le\frac23d_\beta',
\qquad
d_\beta'\le I+\frac25d_p'.
$$

Consequently $d_p'\le10I/11$ and $d_\beta'\le15I/11$. The full coupling includes every return and the infinite outcome; both programs have geometric survival bounded by $4/15$ per return. At each same actual history the source target and acquired rows are identical in the two models. Applying the TV triangle inequality configuration by configuration gives (6.1); convexity gives the analogous same-model law-order comparisons. No hard defect or total-resource budget is preserved. $\square$

**Proof of Theorem 1.3.** Use the common paid-history extraction in Citation 2.4 on the original observer. Retain the bounded nonnegative suspended-state function

$$
y\longmapsto\psi(v_y).
$$

Its extracted expectation is at most $\mathcal I(M)$: every positive p history has its positive suspended beta successor, and its unweighted acquired row is $\rho_hB$. The bound survives the paid-history row limits and Cesaro averaging exactly as other bounded state statistics in [MIXSEP, Lemma 2.1].

Clip both emission vectors to $[a,b]$ as in (2.6). Projection to this interval leaves $\psi$ unchanged. Thus the clipped table has maximal excess at most $61e(M)/11$ and suspended endpoint distance at most $\mathcal I(M)$.

Apply Lemma 6.1, without changing either acquired kernel or row. The rounded table is a finite regular stationary table with endpoint suspended emissions, on the same installed source and full original history domain. Its maximal configuration excess $e'$ satisfies

$$
11e'\le61e(M)+15\mathcal I(M).
$$

Theorem 5.2 gives $11e'>11\eta/300000$, proving (1.4). Setting $\mathcal I=0$, $e=0$, or taking a liminf gives (1.5)–(1.7), respectively. Infimum and limit statements remain distinct from an attained finite optimizer. $\square$

## 7. Correspondence, excluded classes and semantic whitebox information

**Proposition 7.1 (endpoint suspended emissions permit the previously necessary changes).** There is a lawful finite regular stationary table with $\mathcal I=0$, positive absolute alpha-edge change, positive decrease on acquired alpha edges and positive complete-return motion. Neither acquired kernel is a complete redraw.

**Proof.** Take two labels in each phase, fair rows, $B$ equal to the identity and $A$ the transposition, and

$$
u_0=u_1=9/25,
\qquad v_0=a,
\qquad v_1=b.
$$

Both unweighted flows are fair. Install the original product realization of Definition 3.1 on every original record fibre. Its suspended endpoint distance is zero. The acquired alpha update from suspended label 1 to p label 0 has decrease $b-9/25=1/25$, with actual row weight $1/2$; thus expected decrease is $1/50>0$. The other alpha edge has nonzero increase, so absolute alpha change is positive as well.

Its immediate p beta-beta probabilities are

$$
g_0=(16/25)(2/3)=32/75,
\qquad g_1=(16/25)(3/5)=48/125.
$$

They differ by $16/375$. The actual return transposes the labels, so the complete-return motion is at least $16/375>0$, by projection to this complete word. Its successor complete-law dispersions and both phase law diameters are positive: the p laws differ on beta-beta and the suspended laws differ on immediate beta. Both private kernels are deterministic bijections with different rows, not row-independent redraws.

Its p law $Q_0$ is also outside the Borel constant-parameter stopped-p mixture family on $[a,b]$. Put $s=9/25$, $h_a=(16/25)a$, $h_b=(16/25)b$ and $q_j=Q_0(w_{j,0})$. Exact own generation gives

$$
q_1=sh_a,\qquad q_2=sh_ah_b,\qquad q_3=sh_a^2h_b,
\qquad q_2^2-q_1q_3=s^2h_a^2h_b(h_b-h_a)>0.
$$

For a Borel stopped-p mixture with measure $\kappa$, the same coordinates would be $q_j=\int r[r(1-r)]^j\,d\kappa(r)$; Cauchy applied to this positive moment measure gives $q_2^2\le q_1q_3$, a contradiction. This uses a mature moment inequality only to distinguish this explicit lawful example from the supplied native-mixture class [NATIVE; MIXSEP]. The table is not claimed near-optimal; Theorem 1.3 bounds its joint risk away from the endpoint. $\square$

This proposition distinguishes the newly excluded endpoint-emission class from the zero-motion class of MOTION, the alpha-conserving class of ALPHA, the nondecreasing-alpha class of DIRECTION and the complete-redraw classes of PAID. The new proof does not assume native-mixture membership, reversibility, irreducibility or a chosen finite shape. It uses the per-configuration complete-law boxes that mean-law comparisons alone would lose.

**Proposition 7.2 (source and resource correspondence).** Every realized comparison table used in the proof preserves all original operations, histories, held records and exact own-configuration generation. It supplies no runtime predecessor tag, posterior, count or new actual observation, and no equality of its resource budget with the original observer's budget is asserted.

**Proof.** Extraction uses the same actual $B,A$ and copied complete laws on one original held-record fibre. Its rows and the pair mark (3.5) are analysis objects. Clipping and rounding change only synthetic emissions. They retain both actual kernels, the original source and the installed prior. The product construction keeps $C_0$, uses its original event blocks, performs the third write before its latch, clears only private labels on completion, and enables only the original matching Stop. Induction over original operations preserves every record and permission on both seeds, all marker fibres, rejections and returns. The decoder is defined as the complete law of the changed finite program, using those same actual kernels, so (2.3) holds from every configuration.

The mark in Sections 3–5 is never installed in a comparison table or exposed to runtime. It couples the predecessor emission with the original successor configuration on the same acquired edge. Its $x$ marginal remains exactly $\pi$, so all p configuration losses in the proof are the original losses.

Arbitrary public real entries specify mathematical stochastic rules only. For rational represented tables the unchanged kernels and rounded endpoint probabilities admit finite exact categorical samplers, with every candidate, cursor, program selector, threshold, workspace and persistent label charged as part of COMPLETE [PAID, Proposition 11.3]. Rejection uses fresh independent bits and reuses finite workspace. Actual source Reads, sampler bits and work, installed model/table size, held records, synthesis/output and physical source preparation remain separate accounts. Arbitrarily long positive return histories and rejection attempts preclude a finite worst-case total time or output bound. No exact-real device, state-distribution vector or free source-query capability follows. $\square$

**Corollary 7.3 (task-relative semantic whitebox constraint).** Suppose a finite predictive model is assigned the source, legal operations, COMPLETE resource class and exact own-generation semantics of Section 2. If both original complete-tail configuration excesses vanish, its observable configuration semantics cannot use only the two source-endpoint probabilities at suspension. More quantitatively, its same-history expected interior tent mass must satisfy (1.6); in particular some reachable suspended configurations have emissions in $(a,b)$.

**Proof.** Apply Theorem 1.3 to this assignment. The statistical objects are per-configuration decoded laws and the original acquired flow; they are not an identification of the internal implementation. Internal labels, network architecture and a FIB five-window classification are not hypotheses or conclusions of the theorem. $\square$

**Proposition 7.4 (the supported-interior hypothesis cannot be omitted).** On the allowed source with prior supported exactly on depths 1 and 2, the supplied fair persistent endpoint-tag generator has $e=0$ and $\mathcal I=0$.

**Proof.** Use [ST, Theorem 2.1]: retain a fair source-independent endpoint label, set $u=v$ to its endpoint and preserve the label under both noncompleting updates. Its actual fair rows and exact complete laws attain all four phase combinations on this two-depth source. Both suspended emissions are endpoints. This is the existing two-depth attainer, not a new construction. $\square$

## 8. Mathematical attribution and remaining frontier

**Mathematical citation 8.1 (existing and external statements).** The source laws, exact phase radii, paid-history extraction, interval clipping, stationary original-domain realization, full-law survival bound, endpoint box identity and interior excursion are supplied by [ST], [CLIP], [PAID], [MIXSEP] and [DIRECTION]. They are reused, not new minimax or coherence results.

The newly derived relation is (3.6)–(4.10), with its full-law consequence (5.4). It exploits the actual reversed endpoint order of two suspended complete words and the switching equality from both original unweighted flows. The interior tent mass in (1.2) is distinct from ALPHA's absolute acquired-edge change and DIRECTION's signed decrease. The result does not sharpen either relation's coefficient or reproduce a generic energy theorem.

Picci and van Schuppen's primary texts [PS83, Section 2 and Proposition 3.2] and [PS84, Section 3] concern weak realization of a stationary finite-valued process and a static positive factorization of its past/future law. Their weak output-law equality does not impose the present unweighted actual-flow stationarity, each row's common same-update future generation or the two private-loss bounds. Static positive factorization and ordinary matrix rank supply no substitute for these constraints.

Backhoff, Beiglböck, Lin and Zalashko [CT, Theorem 2.6] give causal transport duality and attainment for fixed finite-horizon marginals and a lower semicontinuous bounded-below cost, under their successive weak continuity assumption. Their Theorem 2.7 adds a Markov source and a semiseparable cost for its dynamic programming principle. These are mature tools on specified transport problems, not an attainment theorem for arbitrary finite same-update observers. On the present source, conditional independence given the one hidden depth does not make the observed letter/control process Markov. For example $S=\beta\alpha\mid\beta\beta\alpha\alpha$ and $\alpha\alpha S$ end at the same original record/control fibre. Formula (2.2) reweights the latter posterior by $r_k^2$, strictly raising its next-alpha mean: if $R$ has the former posterior and $R'$ is an independent copy, then

$$
\frac{\mathbb E R^3}{\mathbb E R^2}-\mathbb E R
=\frac{\mathbb E[(R-R')(R^2-(R')^2)]}{2\mathbb E R^2}>0,
$$

since the two supported endpoint rates remain distinct and positive under every finite history. Thus that visible control and the last letter do not determine the next-letter law. An analysis Markovization by history or hidden depth does not grant runtime access to either. Furthermore the shared own-law constraints (3.1), unbounded positive histories and configuration-before-TV loss are additional obligations, not consequences of transport causality.

Chen and Kiefer [CK, Theorem 7 and Corollary 8] give convergent TV approximation for a specified pair of finite labelled Markov chains. A fixed rational observer row and fixed depth target can be put in that framework, retaining original events and padding after Stop. Pairwise law evaluation supplies no lower bound over every finite shape and no risk-preserving realization of two separately optimized phase reports. [PAID, Sections 9–10] already supplies the appropriate original-source finite-partition/all-shape comparison; none is reproved here.

The rational two-label upper witness [PAID, Section 11] has suspended emissions strictly inside $(a,b)$ and interior tent mass $9899/600000000$. Both of its configuration excesses are below $11/10^8$, while its own p excess is above $109467/10^{12}$. These are an unrestricted upper witness and a witness-specific lower bound, respectively, and are compatible with (1.4). The actual three-depth counterexample [ST, Section 3.3] uses prior $(1/10000,1/10000,4999/5000)$ on $\{1,2,3\}$ and history $\beta\alpha\mid\beta\beta\alpha\alpha$: the fair endpoint-tag generator violates its p configuration benchmark on $w_{3,1}$. That is a failure of this generator, not a universal sharper lower bound or a marginalized-risk violation. Here the supplied excursion becomes an all-shape conclusion only after Sections 3–5 control the same original generator. The native-mixture exclusions, existing return-motion and directional relations, and all four risk-order supplies retain their stated scopes.

The primary statements just named do not directly supply (3.6)–(5.4). This is a bounded source correspondence and literature assessment, not an exhaustive global priority claim.

**Mathematical citation 8.2 (other public source contracts).** [RECOVERY] identifies the original phase and countable posterior from an entire exact remaining-length distribution and recovers its permitted projected transcript law. That projected transcript omits held registers; the present full-law comparison retains them through the fixed current-record map $I_c$. At a fixed held-record fibre the Read-preserving renderer supplies this correspondence, but an entire exact distribution is not a single-run source observation or a finite runtime posterior service. Its identifiability statement supplies neither the conditional inequalities (3.6) nor a finite common private-risk attainer.

[JOINT] optimizes historical source rows jointly with a prefix code under depth budgets. Its source family permits arbitrary history-dependent rows, while this source fixes one hidden depth before all Reads. Optimizing those rows or permuting their heavy children would change the actual stopped source or its word labels. Deterministic KBonacci INITIAL block fees, prescribed-area joint moment injection and affine command-fee optima likewise have different observations, targets and resource contracts. No stochastic stopped-risk transfer is used from these sources.

**Mathematical citation 8.3 (other public correspondence boundaries).** [CUBE, Sections 1–12] concerns immutable ordered-tree bracket defects, four-valued literal-address replies, retained raw evidence and hard query budgets. It expressly labels its ordinary arguments as open reference claims. The stopped source here instead emits letters from one pre-drawn hidden depth; its original interface supplies no address query, bracket intervention or coherent oracle. Equal leaf words and small normalized ancestor distances therefore furnish neither the two configuration-risk boxes nor (3.6). No result from that source is a premise here.

[KB26, Section 26] gives an exact adaptive/GLOBAL complete-block fee separation for its specified dyadic INITIAL target family. Its controller chooses literal input blocks and observes their completed endpoints. Here acquired Read letters are random replies from the unchanged source, not chosen blocks, and the objective is full-tail configuration TV rather than INITIAL target identification. There is no supplied source/action/observation/loss/resource-preserving map, so those exact fees are not transferred.

[FUTURE, Sections 34–37] gives integer-kernel and exact-response recovery statements on the original acquired-history image, with its stated support, precision and representation conditions. Such a response can mathematically determine live counts without recovering chronology, a held selected-count bank or the sampled hidden depth. Section 35 requires a supplied exact rational response for its effective inverse; Section 36 separates held records and terminal permissions. This volume retains all original held fields via $I_c$ and grants no such response as a runtime observation. Those recovery statements do not construct a fixed finite same-update generator or control either private configuration loss, and no recovery or fee bound from them is used in (1.4).

**Open question 8.4 (remaining joint realization).** Can a finite complete observer simultaneously satisfy both endpoint full-law boxes, every supported interior configuration loss, the required positive return motion, the required private alpha decreases and the positive suspended interior mass in (1.6), with both original acquired flows and exact per-configuration generation?

This theorem excludes a neighborhood of the no-interior-emission class measured by $\mathcal I$ through (1.4). It gives no upper constraint forcing $\mathcal I$ to be small in the unrestricted class. Exact attainment, an unattained zero infimum, a strictly positive unrestricted gap and optima under fixed resources therefore remain separate unresolved alternatives. A concrete next theoretical obligation is to constrain the shared conditional residual coordinates for genuinely interior $v_y$, where the endpoint forcing of Lemma 3.4 no longer identifies one native tag. A construction must certify the entire complete-law and original-history contract; a universal obstruction must retain every finite shape and all supported configuration losses.

## 9. References

- **ST:** [Randomized stopped-tail minimax](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md), Sections 1–3.
- **CLIP:** [Risk-controlled emission moment feasibility](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md), Sections 2–5.
- **PAID:** [Effective paid-history certificates](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md), Sections 2, 9–15.
- **MIXSEP:** [Uniform mixture separation](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_MIXTURE_SEPARATION.md), Lemma 2.1.
- **ALPHA:** [Acquired alpha calibration compatibility](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/docs/develop/theory/AURIC_FIB_ATOM_ACQUIRED_ALPHA_CALIBRATION_COMPATIBILITY.md).
- **DIRECTION:** [Directional alpha calibration](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/docs/develop/theory/AURIC_FIB_ATOM_DIRECTIONAL_ALPHA_CALIBRATION.md), Sections 2, 5–6.
- **MOTION:** [Actual-return forecast motion](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_RETURN_FORECAST_MOTION.md).
- **MIXED:** [Mixed-phase defect attainment](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MIXED_PHASE_DEFECT_ATTAINMENT.md), its supplied law/law and law/conf scopes.
- **SWITCH:** [Configuration/law switch attainment](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONFIGURATION_LAW_SWITCH_ATTAINMENT.md), its supplied conf/law scope.
- **NATIVE:** [Native-mixture recurrence obstruction](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md), its stated native-mixture class.
- **PS83:** G. Picci and J. H. van Schuppen, *On the Weak Finite Stochastic Realization Problem*, BW 184/83, [primary preprint](https://ir.cwi.nl/pub/6613/6613D.pdf).
- **PS84:** G. Picci and J. H. van Schuppen, *On the Weak Finite Stochastic Realization Problem*, [primary published chapter](https://ir.cwi.nl/pub/2049/2049D.pdf).
- **CT:** J. Backhoff, M. Beiglböck, Y. Lin and A. Zalashko, *Causal Transport in Discrete Time and Applications*, [arXiv:1606.04062v2](https://arxiv.org/html/1606.04062v2), DOI [10.1137/16M1080197](https://doi.org/10.1137/16M1080197).
- **CK:** T. Chen and S. Kiefer, *On the Total Variation Distance of Labelled Markov Chains*, [arXiv:1405.2852](https://arxiv.org/html/1405.2852), DOI [10.1145/2603088.2603099](https://doi.org/10.1145/2603088.2603099).
- **RECOVERY:** [Fourth-segment residual laws and depth recovery](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.md), and its [native conditional-control supplier](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeConditionalControl.md).
- **JOINT:** [Historical processes and depth-budget joint extrema](https://github.com/the-omega-institute/trureturing/blob/4a5ef983220fb11060817d7a36dc1dfc10ce6016/Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HistoricalDepthBudgetJointExtremum.md).
- **CUBE:** [Ancestry cube and acquisition cost](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/AURIC_FIB_ATOM_ANCESTRY_CUBE_AND_ACQUISITION_COST.md), Sections 1–12, with its stated open-reference status.
- **KB26:** [KBonacci self-calibrating boundaries](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/KBONACCI_SELF_CALIBRATING_BOUNDARIES.md), Section 26.
- **FUTURE:** [Future response sufficiency](https://github.com/the-omega-institute/trureturing/blob/3a56aa49697ab7641b7dbe616e0424327c69d2ca/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md), Sections 34–37.

## 追加锚（本行以下为增补区）
