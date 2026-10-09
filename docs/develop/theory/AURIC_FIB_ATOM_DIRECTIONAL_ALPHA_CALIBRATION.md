# Directional acquired-alpha calibration against a rising source posterior

## 1. The uncovered direction

The original common-model question asks for one finite same-update generator attaining the p and suspended complete-tail configuration-risk minima. The published ALPHA result requires positive absolute next-alpha change on actual suspended-alpha updates; MOTION requires positive complete-law change on an actual return. Neither condition specifies the direction of the alpha change. This article proves that direction matters: near common optimality requires a positive amount of **decrease** of the next-alpha forecast on some actual alpha updates.

At every positive suspended cut, the true source next-alpha probability increases after the acquired alpha. The necessary decrease concerns the predictor's individual random configurations, not its mean forecast and not the source posterior. This difference is a source-specific constraint on causal minimax calibration.

Write

$$
d_p=\frac{1116529}{11390625},\qquad
 d_\beta=\frac{239}{3375},\qquad \rho_s=d_s/2,
$$

$$
\eta=\frac{14219478376}{318644812890625},\qquad
\kappa=\eta^2/64.
\tag{1.1}
$$

At a positive actual suspended history h, let its conditional configuration row be $\rho_h(y)$, its actual alpha-update kernel be $A_h(y,x)$, and its current and successor next-alpha emission probabilities be $v_y,u_x$. Set

$$
\mathcal D_h(M)=\sum_{y,x}\rho_h(y)A_h(y,x)(v_y-u_x)_+,
\qquad \mathcal D(M)=\sup_{h\in\mathcal H_\beta}\mathcal D_h(M).
\tag{1.2}
$$

Here $(t)_+=\max(t,0)$. The weights are the unweighted acquired-alpha edge law. The row is an analysis object, never a runtime input. Let

$$
e(M)=\max_s\{R_{\mathrm{conf},s}(M)-\rho_s\}.
$$

**Theorem 1.1.** On every allowed fixed finite or countable prior with positive endpoint masses and a supported nonendpoint, every allowed finite COMPLETE observer satisfies

$$
240e(M)+30\mathcal D(M)>\kappa>0.
\tag{1.3}
$$

Consequently exact common conf/conf attainment requires $\mathcal D>\kappa/30$. Any sequence with both excesses tending to zero has $\liminf\mathcal D\ge\kappa/30$. In the entire class whose every reachable actual alpha edge obeys $u_x\ge v_y$, the joint excess infimum is at least $\kappa/240$. This class can have positive absolute alpha change, positive complete-return motion, nonnative decoders and noncollapsed successor laws.

The new ingredient is the directional stationary calibration relation in Theorem 3.1, including its positive cost for forecast increases. Equation (1.3) is its full-observer consequence. The numerical constants deliberately retain conservative supplied scales; the contribution is the direction restriction, not an improved coefficient.

No finite exact common attainer, vanishing-excess family or positive unrestricted gap is asserted. The free statistic $\mathcal D$ remains unconstrained in the original question.

The theorem concerns conf/conf. The supplied law/law and law/conf attainments [MIXED] and conf/law attainment [SWITCH] keep their stated unchanged-source scopes. No corresponding new direction obstruction is proved for those three combinations: Section 5 needs p configuration risk, and arbitrary-emission clipping in Section 6 uses both configuration risks. Marginalized loss, configuration loss, averaged-history loss and worst-positive-history loss are never exchanged.

## 2. Source, legal execution, complete laws and resources

Fix $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$ and $m=2,d=1,\ell=2,n=4$. Before the first actual Read draw one K from one installed finite or countable prior $\mu$, with $\mu(1),\mu(2)>0$. Given this same K=k, all seed and payload Reads are independent, with alpha probability

$$
r_k=F_{k+1}/F_{k+3},\quad r_1=1/3,\quad r_2=2/5,
\quad r_k\in I_0=[3/8,5/13]\quad(k\ge3).
$$

The source parameter is never reset. Equal seed pairs are rejected and both Reads are paid; alpha-beta accepts seed 0 and beta-alpha accepts seed 1. Payload p emits a completed marker 0 after alpha and suspends after beta. Suspension returns to p after alpha and completes marker 1 after beta. The first three completions advance segments. The third record write precedes its latch. Fourth completion enters the matching original pendingStop; its unique Stop delivers once. Pending and delivered states admit no Read.

Retain the complete original finite control $C_0$: both seeds, selectors, bare fields, parser, full marker tree, held $B,Q^+,Z$ records, write/latch flags, permissions, completion and delivery. The full-tree relation writer uses the old completed-marker count t and old one-count j. Its first and second zeros are events a,c; its first and second ones are b,d. For old t<3 it appends each recognized event to containing scopes $S_1^+=\{a,c,d\}$, $S_2^+=\{b,c\}$. It writes Z only at the first marker. Unmatched ordinal events, seed retries, returns, partial parses and later completions hold these fields. At old t=2 it completes the third write before latching B; afterward the held fields remain while the fourth parser and Stop continue. Both seeds, all 16 marker words and their prefixes, every finite paid rejection history and every finite return history remain in the domain. There is no future-E1 conditioning, controller port, clock, source copy or extra observation [ST, E1, PAID].

Let $\mathcal H_3$ contain the first p cut after that latch. Let $\mathcal H_p,\mathcal H_\beta$ contain all positive finite fourth-segment p and suspended histories, including arbitrary returns. These domains are distinct. Put

$$
a_r=r(1-r),\qquad w_{j,0}=(\beta\alpha)^j\alpha,
\qquad w_{j,1}=(\beta\alpha)^j\beta\beta.
$$

The complete raw p carrier consists of these words and its unique infinite noncompletion word. The suspended carrier consists of beta, $\alpha w_{j,b}$, and its infinite noncompletion word. Their source laws are

$$
P_{p,r}(w_{j,0})=ra_r^j,\quad P_{p,r}(w_{j,1})=(1-r)^2a_r^j,
$$

$$
P_{\beta,r}(\beta)=1-r,\quad
P_{\beta,r}(\alpha w_{j,0})=r^2a_r^j,\quad
P_{\beta,r}(\alpha w_{j,1})=r(1-r)^2a_r^j.
\tag{2.1}
$$

The infinite-word masses are zero. The original measurable bijection $I_c$ retains each future Read and inserts its complete deterministic original event block, records, permissions, completion and Stop. Its inverse reads the letters back. It preserves TV and commutes with removal of the next operation and its original block. The already acquired suspended beta is not another future Read.

A legal acquired operation list, with only Stop deleted, is exactly its ordered raw-prefix cylinder. Induction proves this: each Read consumes the next raw letter and applies the original deterministic block; Stop consumes no letter and delivery ends execution. Rejections, accepted seed letters, early payloads, returns and partial pairs are all retained. Thus, with counts over **all** acquired Reads,

$$
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
 {\sum_i\mu(i)r_i^{A(h)}(1-r_i)^{B(h)}},\qquad
T_h^\mu=(I_{C_0(h)})_*\sum_k\nu_h(k)P_{s,r_k}.
\tag{2.2}
$$

The denominator is strictly positive; the countable sums are dominated by the summable prior masses. Conditional on each supported K, the unread tail remains independent with the same parameter. No completion condition enters (2.2). Counts and posterior rows are analysis quantities.

An observer has one fixed finite COMPLETE carrier, source-independent initialization, fixed time-homogeneous source-independent acquired-letter stochastic updates, and a decoder reading one actual configuration. COMPLETE includes $C_0$, private labels, installed constants and tables, program selectors, workspace, addresses, output indices and persistent randomness. It has no uncounted tape, continuous register, correlated source seed, readable distribution vector, clock, archive or advice. Each decoder is exactly the complete law of its own synthetic generator, using its synthetic emissions and these **same** acquired-letter kernels. A finite law description, such as the installed generator and current configuration index, is the output contract; an infinite table or exact posterior service is not supplied.

More precisely, let $P_o(z,z')$ be the installed acquired-operation kernel. For every future event E after removal of o and its prescribed block, exact own-configuration generation means

$$
D_z(oE)=q_z(o)\sum_{z'}P_o(z,z')D_{z'}(E).
\tag{2.5}
$$

The prefix oE includes that entire original block. This identity uses the same $P_o$ on acquired and synthetic execution. It remains valid when $q_z(o)=0$; the actual kernel is still defined. It is an individual cylinder identity, stronger than any assertion about a marginalized report.

At the same actual history put

$$
Q_h=\sum_z\rho_h(z)D_z,\quad
e_{\rm law}(h)=\operatorname{TV}(Q_h,T_h^\mu),\quad
e_{\rm conf}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu).
\tag{2.3}
$$

TV is the supremum of the absolute event-probability difference. On the fourth-segment carriers it is half the countable $\ell^1$ distance, including the infinite outcome. Each $R_{j,s}$ is the supremum over all positive histories in $\mathcal H_s$. Actual-history-average loss is different. The supplied separate full-tail minimax radii are $\rho_p=1116529/22781250$, $\rho_\beta=239/6750$; the terminal values $13/266,9/266$ do not replace them.

For a positive actual legal history h and one of its legal next operations o, let $[o]$ be the corresponding complete-future cylinder and $q_h(o)=Q_h([o])$. When $q_h(o)>0$, let $\operatorname{res}_o Q_h$ be the conditional law on that cylinder pushed forward by deletion of o and its original event block. The retained marginalized conditioning/update defect is

$$
\delta(h,o)=
\begin{cases}
\operatorname{TV}(\operatorname{res}_o Q_h,Q_{ho}),&q_h(o)>0,\\
0,&q_h(o)=0.
\end{cases}
\tag{2.4}
$$

The second case defines no conditional law. It does not remove the positive actual successor or its risk. Let $\Delta_4$ be the supremum over legal operations at positive fourth-segment active or pending cuts, and $\Delta_{\rm all}$ the supremum over legal operations at all positive original cuts, including seed rejection and early payload parsing. PendingStop has zero defect; the delivered empty supremum is zero. Individual same-update generation remains exact. No defect budget or zero-defect recovery is imposed; the relaxation concerns only these marginalized comparisons. For a fixed installed prior, the achievable set consists of the tuples $(R_{\rm law,p},R_{\rm conf,p},R_{\rm law,\beta},R_{\rm conf,\beta},\Delta_4,\Delta_{\rm all})$ produced by one allowed observer, with its one counted resource allocation. A comparison must be witnessed by one such tuple, or by the explicit comparison construction in its stated resource class. Separate attainable coordinates do not assert an attainable joint tuple.

The supplied finite-history lower witnesses [ST, Theorem 2.1] remain applicable. In the two-depth source, for every fixed finite competitor and $0<\epsilon<1$, $0<\zeta<1/2$, positive paid histories on the same original control fibre have configuration-row TV at most $\epsilon$ and opposite endpoint posterior errors at most $\zeta$; their phase configuration-loss maximum is at least $((1-2\zeta)d_s-\epsilon)/2$. Its explicit paid-length bound is retained as follows. If $S_M$ is the complete competitor size, put $a_*=36/25$, $b_*=81/100$, $c_p=(\mu(2)/\mu(1))(19683/15625)$, $c_\beta=9c_p/10$, and for the chosen phase $c=c_s$ set

$$
\begin{aligned}
q_g&=\lceil S_M/(2\epsilon)\rceil,&N_g&=(q_g+1)^{S_M},\\
D_g&=\left\lceil\frac{2\log((1-\zeta)/\zeta)+|\log b_*|}{\log a_*}\right\rceil,
&i_0&=\max\{0,\lceil-\log c/\log a_*\rceil\},\\
J_g&=i_0+N_gD_g,&T_g&=\left\lceil\frac{\log c+J_g\log a_*}{|\log b_*|}\right\rceil.
\end{aligned}
$$

Those p witnesses have at most $2J_g+2T_g+6$ paid Reads; suspension adds one. This is a finite certificate length, not an execution deadline or minimum resource price. Full-posterior endpoint exposure with additional finite or countable depths gives $(d_s-2\zeta-\epsilon)/2$ [ST, Section 3.3]. These are actual-history lower witnesses, not reset experiments. They justify the endpoint radii and nonnegative excesses used below.

Finally, source and observer likelihoods factor along a fixed acquired word. At a suspended cut,

$$
\Pr(K=k,Y_h=y,\text{next actual alpha},X_{h\alpha}=x\mid h)
=\nu_h(k)\rho_h(y)r_kA_h(y,x).
$$

Dividing the sum over k by $\sum_k\nu_h(k)r_k>0$ gives precisely the edge weights in (1.2), without synthetic-emission tilting.

## 3. A directional calibration cone on both acquired flows

Take finite p and suspended label sets X,Y with positive probability rows $\pi,\tau$, row-stochastic actual kernels $B:X\to Y,A:Y\to X$, and emissions $u_x,v_y\in[1/3,2/5]$. Require both unweighted acquired flows

$$
\pi B=\tau,\qquad \tau A=\pi,\qquad C=BA.
\tag{3.1}
$$

Their product realization retains the full original $C_0$, uses fair synthesis before the third latch, and samples $\pi$ source-independently after the third write and latch in that same update. B acts on p-beta, A on suspended-alpha; completing letters clear private labels and retain the matching original Stop. All original record fibres use this same rule, retaining their own records. Projection to $C_0$ preserves every event and enabled menu by induction. All labels and samplers are charged. The $\pi$-initializer is part of the installed table, with a finite exact sampler when its entries are rational; arbitrary real rows here describe abstract stochastic rules only. Actual fourth rows are $\pi,\tau$ after every history, since actual letters do not tilt the private rows by synthetic probabilities [PAID, Lemma 2.1.1].

The exact individual raw decoder laws satisfy

$$
Q_x=u_x\delta_\alpha+(1-u_x)\beta\sum_yB_{xy}W_y,
\qquad W_y=(1-v_y)\delta_\beta+v_y\alpha\sum_zA_{yz}Q_z.
\tag{3.2}
$$

A return has synthetic survival at most $\lambda=4/15$. Finite-word expansion and vanishing residual mass determine normalized complete laws. Infinite outcomes remain with zero mass; no law is conditioned on completion. Earlier seed and payload survivals are geometric as well. Pending and delivered laws are the original unique Stop and empty future.

The all-positive-history risks equal the supported pure-target suprema on these fixed rows [CLIP, Proposition 2.3]. For the upper direction use countable target convexity in (2.2). For the lower direction, positive paid rejection histories expose each supported depth while the installed row stays fixed; the target converges in TV. This correspondence concerns full $\mathcal H_s$, not only $\mathcal H_3$.

Define

$$
J_+=\sum_{y,z}\tau_yA_{yz}(v_y-u_z)_+,
\quad J_-=\sum_{y,z}\tau_yA_{yz}(u_z-v_y)_+,
$$

$$
Z_x=15u_x-5,\qquad
\mathcal E_C=\frac12\sum_{x,z}\pi_xC_{xz}(u_x-u_z)^2.
\tag{3.3}
$$

$J_+$ measures decreases on the alpha update; $J_-$ measures increases. Set

$$
h=\frac{1586793150}{266850431},\quad
K=\frac{7613443125}{266850431},\quad
c=\frac{502947375}{266850431}>0.
\tag{3.4}
$$

**Theorem 3.1.** For every such table, on every allowed installed prior, with $\varepsilon_s=R_{\rm conf,s}-\rho_s$,

$$
\frac{\mathbb E_\pi[Z(1-Z)]}{16}+h\mathcal E_C+cJ_-
\le\frac{\varepsilon_p}{d_p}+\frac{\varepsilon_\beta}{d_\beta}+KJ_+.
\tag{3.5}
$$

Only positive endpoint masses are needed for (3.5). A supported nonendpoint will enter in Section 5. The new term $cJ_-$ gives a positive calibration cost to the opposite direction, rather than charging both directions identically.

Use the supplied endpoint-positive complete events

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\}.
$$

Their endpoint probabilities are $412/729,7299/15625$ and $22/27,93/125$, with midpoints $C_p=11758471/22781250$, $C_\beta=5261/6750$. If $a=\pi Q(E_p),b=\tau W(E_\beta)$, the endpoint configuration-risk bounds, projected to these events, give

$$
|a-C_p|\le\varepsilon_p,\quad |b-C_\beta|\le\varepsilon_\beta,
\quad D:=\frac{412/729-a}{d_p}-\frac{22/27-b}{d_\beta}
\le\frac{\varepsilon_p}{d_p}+\frac{\varepsilon_\beta}{d_\beta}.
\tag{3.6}
$$

This uses a necessary event consequence of the configuration losses; it does not replace them by law-order losses.

We use one explicit published input. For the **paired** table with p and suspended labels X, row $\pi$ in both phases, beta kernel C, alpha kernel identity, and both emissions u, denote its event means by $a^*,b^*$. The supplied stationary calibration-energy inequality [ALPHA, Section 5] states

$$
D^*:=\frac{412/729-a^*}{d_p}-\frac{22/27-b^*}{d_\beta}
\ge\mathbb E_\pi[Z(1-Z)]/16+h\mathcal E_C.
\tag{3.7}
$$

Its hypotheses are exactly finite stationarity and regular emissions; neither reversibility, irreducibility nor a native-mixture premise is required. This is a reused result, not a new energy theorem. The new proof must relate D to D* directionally; the absolute comparison in ALPHA does not do that.

## 4. Directional comparison: the live missing argument

**Lemma 4.1 (remove only forecast decreases).** There is a finite stationary regular comparison table whose alpha emissions are no larger than their predetermined p successors. If its event score is D0, then

$$
D+KJ_+\ge D_0.
\tag{4.1}
$$

Its p laws and suspended **mean** law are compared to the original ones; no suspended configuration-risk domination is asserted.

**Proof.** Split a suspended label into pairs $(y,z)$ with $A_{yz}>0$. Give it row $\tau'_{yz}=\tau_yA_{yz}$, beta kernel $B'_{x,(y,z)}=B_{xy}A_{yz}$, and deterministic alpha successor z. Then $\pi B'=\tau'$, $\tau'A'=\pi$, and $B'A'=C$. Presampling the private successor after beta is causal, source-independent and finite; it is not a source observation. The split index and all sampler states are charged. If its emission remains $v_y$, its p laws are exactly Q, and its suspended mean is exactly $\tau W$, by (3.2). Individual suspended laws can differ because the private successor was sampled earlier.

Now use $v^0_{yz}=\min(v_y,u_z)$. All emissions remain regular and both acquired flows remain exact. Generate the new laws Q0,W0 from these same installed updates; do not assign a centroid decoder. Let $d=\sum_x\pi_x\operatorname{TV}(Q_x,Q_x^0)$. Couple the synthetic suspended emissions, conditional on the presampled pair. Their discrepancy probability is $(v_y-u_z)_+$; a matched alpha continues at z. The p emissions agree. Averaging the complete-law coupling and using (3.1) gives

$$
d\le\tfrac23J_++\tfrac4{15}d,
\qquad d\le\tfrac{10}{11}J_+.
$$

The suspended mean-law distance is at most $J_++(2/5)d\le15J_+/11$. Both bounds concern whole stopped laws; the regular survival bound includes all returns and the infinite outcome. Thus $|a-a_0|\le10J_+/11$, $|b-b_0|\le15J_+/11$. Since $K=10/(11d_p)+15/(11d_\beta)$, (4.1) follows. The comparison preserves no hard defect or COMPLETE budget. ∎

**Lemma 4.2 (forecast increases have a positive signed cost).** For the comparison of Lemma 4.1 and the paired table of (3.7),

$$
D_0\ge D^*+cJ_-.
\tag{4.2}
$$

**Proof.** Work in the split table and write $U=\operatorname{diag}(1-u)$. Let

$$
F_0=B'\operatorname{diag}(v^0)A',\quad
F_*=C\operatorname{diag}(u),\quad
H_0=UF_0,\quad H_*=UF_*,\quad R=H_*-H_0\ge0.
$$

The inequality is entrywise, since each split alpha edge has $v^0_{yz}\le u_z$. Let $g_0=U\mathbf1-H_0\mathbf1$, $g_*=U\mathbf1-H_*\mathbf1$. These are the immediate marker-1 word probabilities. Then $g_0-g_*=R\mathbf1$. Set $t=J_-$. The total expected difference between successor and suspended emissions in the split table is exactly t; edges with original $v_y>u_z$ were set to equality.

Let $f_n=g_0+H_0g_0+\cdots+H_0^ng_0$ and define $f_n^*$ similarly; put $f_{-1}=f_{-1}^*=0$. These are probabilities of marker 1 completed within n returns, so each lies in [0,1]. Subtracting their recursions gives

$$
f_n-f_n^*=H_0(f_{n-1}-f_{n-1}^*)+R(\mathbf1-f_{n-1}^*).
$$

Induction yields $0\le f_2-f_2^*\le\sum_{j=0}^2H_0^jR\mathbf1$. Since $H_0\le\lambda C$, $\pi C=\pi$ and $\pi R\mathbf1\le(2/3)t$,

$$
0\le a_0-a^*\le\tfrac23(1+\lambda+\lambda^2)t=\tfrac{602}{675}t.
\tag{4.3}
$$

For the suspended event define the nonnegative row

$$
r_z=\sum_y\tau_yA_{yz}(u_z-v^0_{yz}),\qquad \sum_zr_z=t.
$$

The alpha-weighted successor row is $\pi\operatorname{diag}(u)-r$. Therefore

$$
b_0-b^*=r(\mathbf1-g_0)+\sum_x\pi_xu_x(g_0-g_*)_x.
\tag{4.4}
$$

Every $(g_0)_x\le(2/3)^2=4/9$, so the first term is at least 5t/9. For the second, $u_x(1-u_x)\ge2/9$, and summing its beta-edge flow gives at least 2t/9. Hence

$$
b_0-b^*\ge7t/9.
\tag{4.5}
$$

Equations (4.3)–(4.5), in the **same** table, imply

$$
D_0-D^*\ge\left(\frac7{9d_\beta}-\frac{602}{675d_p}\right)t
=\frac{502947375}{266850431}t=ct.
$$

This sign uses the original two events, their distinct full-tail endpoint distances, and the common actual circulation. It is not a marginal covariance substitution or an arbitrary-task monotonicity claim. ∎

**Proof of Theorem 3.1.** Combine (3.6), Lemmas 4.1–4.2 and the supplied paired inequality (3.7). No individual conditional-law calibration or zero marginalized defect was assumed. ∎

## 5. Consuming the supported interior loss

Let

$$
G_+=\varepsilon_p/d_p+\varepsilon_\beta/d_\beta+KJ_+.
$$

**Proposition 5.1.** With a supported nonendpoint, $G_+>\kappa$, and consequently

$$
25\max(\varepsilon_p,\varepsilon_\beta)+30J_+>\kappa.
\tag{5.1}
$$

**Proof.** Theorem 3.1 gives $\mathcal E_C\le G_+/h$, $\mathbb E Z(1-Z)\le16G_+$, $J_-\le G_+/c$, while $J_+\le G_+/K$.

We spell out the needed complete-law comparisons. Comparing the original generator with the paired generator, the suspended emission discrepancy on a presampled edge is $|v_y-u_z|$. The coupling used in Lemma 4.1 now gives

$$
\sum_x\pi_x\operatorname{TV}(Q_x,Q_x^*)\le\tfrac{10}{11}(J_++J_-).
\tag{5.2}
$$

The supplied source-law bound is $\operatorname{TV}(P_{p,u},P_{p,t})\le L_p|u-t|$, $L_p=125/57$. Its coupling follows the two iid letter generators until the first discrepancy, through the original parser; the expected p Read count is $(2-u)/(1-u(1-u))\le L_p$. Summing discrepancy hazards proves the full-law bound, with both legal infinite outcomes retained.

Put $d_x'=\operatorname{TV}(Q_x^*,P_{p,u_x})$. Couple the paired suspended emission $u_z$ with the constant source emission $u_x$, and use that Lipschitz bound after a matched return. Then

$$
d_x'\le(1-u_x)\sum_zC_{xz}
 \{(1+u_zL_p)|u_z-u_x|+u_zd_z'\}.
$$

Averaging and using stationarity yields

$$
\pi d'\le k\sqrt{2\mathcal E_C},\qquad k=1070/627.
\tag{5.3}
$$

Indeed the continuation coefficient is at most $\lambda=4/15$, the discrepancy coefficient after division by $1-\lambda$ is $(10/11)(1+(2/5)L_p)=k$, and Cauchy bounds $\sum\pi_xC_{xz}|u_x-u_z|$ by $\sqrt{2\mathcal E_C}$.

Round u to its nearer endpoint $t_x\in\{1/3,2/5\}$, taking the lower on ties. Since $|u_x-t_x|\le(2/15)Z_x(1-Z_x)$, (5.2)–(5.3) give

$$
d_0:=\sum_x\pi_x\operatorname{TV}(Q_x,P_{p,t_x})
\le\tfrac{10}{11}(J_++J_-)+k\sqrt{2\mathcal E_C}+\tfrac{800}{171}G_+.
\tag{5.4}
$$

These endpoint laws are proof comparisons, not replacement decoders. If $w=\pi\{t_x=1/3\}$, endpoint event calibration gives $d_p|w-1/2|\le\varepsilon_p+d_0$.

For every $r\in I_0$, the complete word $w_{3,1}$ has source mass $r^3(1-r)^5$, exceeding both endpoint masses by at least eta. Its derivative has sign $3-8r$, so its smallest value on $I_0$ is at 5/13; subtracting the larger endpoint value gives (1.1). The supplied coordinate triangle identity, including the infinite atom, gives

$$
\frac{\operatorname{TV}(P_{p,1/3},P_{p,r})+
\operatorname{TV}(P_{p,2/5},P_{p,r})}{2}\ge\rho_p+\eta/2.
$$

For completeness that identity is the sum, divided by two, of
$|d-a|+|d-b|-|a-b|=2\operatorname{dist}(d,[a\wedge b,a\vee b])$ over the countable carrier. The word outside the endpoint interval contributes at least eta. Reverse triangle bounds the change from fair endpoint weights by $d_p|w-1/2|$. Therefore, on the same row,

$$
\sum_x\pi_x\operatorname{TV}(Q_x,P_{p,r})
\ge\rho_p+\eta/2-\varepsilon_p-2d_0.
$$

Choose one supported nonendpoint, whose pure-target configuration loss is at most $\rho_p+\varepsilon_p$. Comparing these two inequalities yields

$$
\eta/4\le\varepsilon_p+d_0.
\tag{5.5}
$$

All losses here use this one table, row, prior and target. This is precisely where configuration-before-TV is essential.

Since $\varepsilon_p\le d_pG_+$, substitution in (5.4)–(5.5) gives

$$
\eta/4\le A_+G_++B_0\sqrt{G_+},\quad
A_+=d_p+800/171+\tfrac{10}{11}(1/K+1/c)<6,
$$

$$
B_0^2=2k^2/h=\frac{12220682338076}{12476288085327}<1.
$$

The exact value of $A_+$ is $2540417332337410742197/480176818797590578125$. If $G_+\le\eta^2/64$, the right side is strictly below $6\eta^2/64+\eta/8<\eta/4$, since $0<\eta<4/3$. This contradicts (5.5). Finally $1/d_p+1/d_\beta<25$ and K<30 give (5.1). ∎

## 6. Arbitrary finite observers, countable priors and original histories

**Proof of Theorem 1.1.** Reuse the common paid-history extraction [MIXSEP, Lemma 2.1; PAID, Lemma 14.1], retaining both configuration-risk bounds. It gives one held-record fibre, the observer's original B,A and copied complete laws, and rows $\pi B=\tau,\tau A=\pi$, with simultaneous pure-target configuration losses bounded by the original phase risks for every supported depth.

The source/history mechanism of this supplied extraction is explicit. Use $S=\beta\alpha\mid\beta\beta\alpha\alpha$, accepting seed 1 and writing markers 100 before the third latch. At the seed-pair boundary, finite-chain powers of the two equal-pair update matrices converge along multiples of their recurrent periods. With rejection counts approaching proportions r and 1-r for a chosen supported r, the acquired row tends to the same row independently of r. Competing-depth likelihood ratios are $\exp[-2n\operatorname{KL}(\operatorname{Ber}(r)\Vert\operatorname{Ber}(r_i))+O(1)]$. The rounding error and fixed-suffix likelihood ratio are uniformly bounded on $[1/3,2/5]$. The distinct Fibonacci parameters and summable prior give dominated convergence of the entire other-depth posterior mass, including countable priors. Appending each fixed finite return preserves it. A Cesaro limit of the returned rows is stationary and retains all supported loss bounds on that same row. Positive stationary coordinates occur after finite positive original histories. These are analysis limits, not installed posterior registers or new source runs.

The same finite-row limits also retain any bounded linear statistic. Apply this observation to

$$
f_B(x)=\sum_yB_{xy}\sum_zA_{yz}(v_y-u_z)_+.
$$

At each positive actual p history on the fibre, its positive suspended successor has row $\rho_hB$. Hence $\rho_hf_B=\mathcal D_{h\beta}(M)\le\mathcal D(M)$. This bound survives each finite-row limit, Cesaro average and its limit, giving $J_+^0=\pi f_B\le\mathcal D(M)$. Both flows and the statistic use actual unweighted letters, including original kernels with zero synthetic probabilities.

Delete zero-row labels; nonnegative flow identities forbid transitions into them from positive labels. Clip both emission vectors to $[1/3,2/5]$ and regenerate their own complete laws, retaining the two kernels and rows. The supplied risk-controlled clipping [CLIP, Theorem 3.1] gives

$$
\widehat\varepsilon_p\le(41\varepsilon_p+20\varepsilon_\beta)/11,
\qquad
\widehat\varepsilon_\beta\le(12\varepsilon_p+41\varepsilon_\beta)/11.
\tag{6.1}
$$

Its full-law coupling includes original positive noncompletion mass and zero or unit emissions; no original regularity is assumed. The common interval projection is monotone and 1-Lipschitz, so pointwise

$$
([v]_{[1/3,2/5]}-[u]_{[1/3,2/5]})_+\le(v-u)_+.
$$

Thus $\widehat J_+\le J_+^0\le\mathcal D(M)$. Install the resulting finite stationary comparison by the original product realization. Countable target convexity supplies its all-history risk bounds. No hard defect or resource budget is preserved.

Proposition 5.1 applied to this one table yields $\widehat G_+>\kappa$. With $e=\max(\varepsilon_p,\varepsilon_\beta)$,

$$
\widehat G_+\le
\left(\frac{61}{11d_p}+\frac{53}{11d_\beta}\right)e+K\mathcal D(M)
\le240e+30\mathcal D(M).
$$

The displayed coefficient of e is $33253004250/266850431<240$. This proves (1.3). The endpoint lower bounds give nonnegative excesses. Exact and liminf consequences follow, including when finite shapes or installed priors vary while retaining the hypotheses. ∎

## 7. A rising true posterior and a necessary opposing private response

The posterior-increase identity in [SIMPLEX, Section 9] is a covered source ingredient. At any positive suspended history let $m_h=\sum_k\nu_h(k)r_k$. Bayes conditioning on that same acquired alpha gives $\nu_{h\alpha}(k)=\nu_h(k)r_k/m_h$, and hence

$$
m_{h\alpha}-m_h=
\frac{\sum_k\nu_h(k)r_k^2}{m_h}-m_h
=\frac{\operatorname{Var}_{\nu_h}(r)}{m_h}>0.
\tag{7.1}
$$

Both endpoint posterior masses remain positive after every finite history, so the variance is strictly positive. All sums are bounded and countable. Equation (7.1) describes the same acquired alpha as (1.2), not a synthetic sample or an added observation.

When $240e<\kappa$, Theorem 1.1 gives $\mathcal D>(\kappa-240e)/30>0$. Some finite positive suspended history therefore has positive acquired edge mass with $v_y>u_x$, even though (7.1) holds there. Exact attainment, if it exists, has such a history with $\mathcal D_h>\kappa/30$. This does **not** require the predictor's marginalized emission mean to fall: increases on other private outcomes may dominate. It does not claim that every actual alpha, every history or the one realized source run exhibits a decrease. No uniform paid length or occurrence probability is supplied.

The excluded direction class is nonempty beyond ALPHA's emission-conserving class. Use X=Y={0,1}, fair rows, $A=I$, B the swap, $u=(1/3,2/5)$, $v=(1/3,1/3)$. Install this rational product observer on, for example, the original prior $\mu(1)=\mu(2)=\mu(3)=1/3$. Both acquired flows hold, all original histories and records remain, and the same-update laws are normalized by regular survival. Here $J_+=0$, $J_-=1/30$. Absolute alpha change is positive. The actual return swaps p labels, whose immediate-alpha coordinates differ by 1/15, so complete-return motion is at least 1/15. Neither interface is a complete redraw. Both phase law diameters are positive; their lower bounds are 1/15 and 1/45. Positive emissions, irreducible actual return and distinct p laws also place this example outside the all-native-mixture class by the supplied NATIVE rigidity. This is a lawful example of the excluded update direction, not a near-optimal witness.

For task-relative whitebox quality $W_s=1-R_{\rm conf,s}$, simultaneous $W_s\ge1-\rho_s-e$ forces $\mathcal D\ge(\kappa-240e)_+/30$, with strictness for a positive right side. This constrains a semantic forecast and its actual causal update jointly. It identifies neither an internal implementation nor a classification of arbitrary trained networks by FIB windows.

## 8. Mathematical correspondences and finite realization boundary

The uncovered relation is the signed comparison (4.2), combined with removal of only decreases in (4.1) and the resulting cone (3.5). It extends the excluded class from emission-conserving alpha updates to all nondecreasing alpha updates, allowing arbitrary finite nonreversible beta dynamics. The first-three-marker influence bound and suspended-event lower bound use both acquired flows and the unequal original endpoint distances. Positive realization, coupling, convexity, triangle inequalities and stationarity are mature ingredients.

ALPHA supplies the paired energy inequality (3.7), the absolute comparison used in (5.2), and the supported-interior consumption. Its absolute statistic treats both signs alike. MOTION requires complete-return motion without prescribing its emission direction. MIXSEP and NATIVE restrict source-mixture representations, whereas the direction class here permits nonnative generated laws. PAID Sections 9–11 supplies label aggregation, both acquired flows, all-shape risk/defect approximation, corrected unrestricted certificates and the rational two-label upper witness. That witness has positive alpha decreases and positive excess; neither is a positive unrestricted gap. PAID Sections 12–15 supplies either-interface redraw exclusion, complete successor-law dispersion and held-fibre diameter noncollapse. Those restrictions do not specify the two signs in (3.3). All these results are used within their published scopes.

The actual three-depth endpoint-tag counterexample retains its scope: at $\mu=(1/10000,1/10000,4999/5000)$ and $h_0=\beta\alpha\mid\beta\beta\alpha\alpha$, the fair persistent endpoint-tag generator exceeds the p configuration benchmark because of $w_{3,1}$ [ST, Section 3.3]. It is a method-specific configuration-risk failure, not a marginalized-risk violation or a universal positive gap. Section 5 consumes its supplied interior excursion only after the directional relation controls closeness to endpoint tags.

SIMPLEX supplies (7.1), together with its five-mode Bayes-plausible record and higher-moment examples. Its source-posterior formula applies here by the identical shared-depth prior, parameter $r_k$, finite actual word and acquired alpha likelihood. This correspondence concerns the true posterior only. It installs no posterior row, gives no configuration-risk replacement, and contains no signed relation between both acquired kernels and complete-law risks. The opposing private response is the consequence of Sections 4–6, not a new posterior identity.

JM Sections 49–51 concerns actual immutable ordered trees under the substitution $\rho$, their depth/ray flag, construction-context quotient and one local rotation preserving the leaf word while causing unbounded intrinsic-depth loss. Its contexts are mathematical constructions, not granted source operations. Its raw objects, replies and metrics are different from the same-depth iid paid Read source and the two acquired stochastic flows here. RT Section 41 concerns finite Abelian controlled shifts, character annihilation and a minimum random support under full multi-coordinate Fourier conditions. Its channel and diamond-norm contract likewise gives no stopped-source TV or paid-history correspondence. No result is transferred from either contract.

TREE uses a bounded immutable tree, a truthful hit-or-append cache, payment for distinct queried addresses, correct yes/no termination, and nominal carrier lower bounds. Repeating an address there repeats one immutable reply. Repeating Read here yields another iid letter conditional on the same K and pays again. Since both letters have positive probability, a repeat-address interpretation fails to preserve the source law. Its cache cannot supply a free original history archive or the two required acquired flows.

KB22 concerns deterministic matched mod-two complete blocks, immutable INITIAL phase and the exact $2r$ phase fee on its stated dyadic family. KB-TRACE and KB-EXEC preserve the same original scanner, chronological own endpoints and paid complete-word execution. KB-PHYSICAL, on odd $m\ge3$, $k=m+1$, a successful positive parent, full surviving phase support and the specified per-phase INITIAL-label factorization, supplies a donor-compensated complete suffix and a final own-archive decoder. Its regular and exceptional seams are part of that deterministic source contract. None identifies its literal block, scalar endpoint, retained archive, INITIAL target or block fee with a stochastic stopped Read, complete-law TV loss or finite private configuration here. A paid suffix attainment is not a stochastic minimax optimum. No archive, input choice, clock or price transport is assumed.

KIM concerns row incidence of natural floors of golden powers and Lucas thresholds. LOCAL concerns adjacent-exclusion position laws, with its stated interior, Markov or activity hypotheses. For either nonconstant binary identification of occupation with alpha/beta, its forbidden adjacent occupied pair conflicts with an original positive equal-pair rejection. TRI concerns static quadratic response and its explicitly added continuous internal dynamics; OBS supplies observation/response identities under its own declared laws. Neither semantic response nor shared Fibonacci terminology identifies the present source, legal operations, risk order, decoder generation or runtime. The proof uses the original stopped source directly and classifies no arbitrary trained network by five windows.

CK compares two supplied labelled Markov-chain laws in TV; its approximation and maximizing-event conclusions do not impose a joint acquired-flow configuration-risk calibration. TS and CJM construct positive realizations of supplied transfer functions, with their stated pole and positivity hypotheses. MW characterizes quotients and positive or completely positive realizations of a given stochastic process. These mature realization and comparison results do not supply the original paid posterior exposure or the signed event comparison (4.2). This attribution makes no exhaustive priority claim.

For a counted rational realization, put $N=|X|$, $L=|Y|$ and $c_0=|C_0|$. The original table has at most $c_0(1+N+L)$ semantic operation-cut configurations. The split has at most $NL$ suspended labels, and each split or paired comparison has the uniform semantic bound

$$
S=c_0(1+N+NL).
\tag{8.1}
$$

The one extra private value is the cleared value. Taking a product over control and labels overcounts invalid combinations, so remains an upper bound. Full original record, parser, permission, latch, pending and delivered fields are in $C_0$. This construction is finite and need not preserve a competitor's resource budget.

For rational $\pi,\tau,B,A,u,v$, choose a common positive denominator $q_0$ for those entries and the early fair emission, and put $q=q_0^2$, $b=\lceil\log_2q\rceil$. Every entry of $B'$, $C$, $\tau'$, the original and clipped emissions and each initializer has denominator dividing q. Minima preserve rationality. Acquired kernels are sampled as installed rows. Synthetic emissions and their conditional update rows are sampled successively, so no additional product denominator is needed. The program never samples a source posterior.

To sample a row with denominator q, retain b fresh fair bits as an integer $j\in\{0,\ldots,2^b-1\}$. Reject $j\ge q$; otherwise select the unique half-open cumulative-threshold interval containing j. Accepted j is exactly uniform on $\{0,\ldots,q-1\}$, hence this gives the installed row exactly. The acceptance probability is $q/2^b>1/2$, except that a power-of-two denominator accepts surely. Retries overwrite the same candidate and cursor without a persistent retry count. The expected fresh-bit cost per categorical draw is $b2^b/q<2b$; no finite worst-case draw time is asserted.

Here is a conservative bound counting the remaining fields. Let R be the number of installed categorical rows, each padded to at most S successors. Cumulative thresholds, including their end values, require at most $T=R(S+1)(b+1)$ bits. Let P be the bit length of the fixed finite program, model identifier, control/event/output tables and finite law-description constants; let w be the additional reusable workspace in bits, including any report buffer. Let J be its number of program-counter values. Let E be the maximum original event-block length, including the third write and latch in their original order, and let O be the maximum length of an encoded finite law report. Both lengths are counted installation parameters. Set $a=P+T+w+b+1$, counting addresses in the program/table and reusable workspace/candidate buffers, together with a null value. Cursor and selector fields are fixed registers named by the program. Candidate, cursor, row/threshold selectors, address, result index and separate event/report cursors then give

$$
|\mathcal C_{\rm complete}|
\le S\,2^{P+T+w}\,J\,2^b(b+1)(R+1)(S+1)^2a(E+1)(O+1).
\tag{8.2}
$$

The two $(S+1)$ factors separately count threshold scanning and the selected successor index. The $2^{P+T+w}$ factor even counts all possible bit patterns in allocated program/table/workspace storage; fixed installed contents occupy a subset. Thus installation length is explicitly charged despite being constant during a run. Finite tables allow finite J and w: integer comparisons and threshold scans need only fixed-width buffers. The four-marker controller has finite event blocks, and every report has a fixed finite field encoding, so E and O are finite as well. Every persistent random bit is in these counted fields. The output is the finite installed-law identifier and encoded current complete configuration index, not an infinite probability table.

Internal categorical service has no external Read, reset, wait command or observation and introduces no additional source-query cut or permission. The risk cuts remain the original returned-operation cuts. Its returned kernel is exactly the installed row by the uniform-integer argument. The synthetic generator uses the same service for the same acquired-letter rows, and the decoder from every service configuration is that program's remaining complete-future law. Projection of each returned operation to $C_0$ performs precisely its original event block, enabled menu and matching Stop. This proves same-update causal generation for the rational product and comparisons, including all held fibres and all positive finite histories, without replacing a configuration law by a mean law.

Arbitrary real entries remain abstract finite indexed stochastic rules, not physical exact-real sampling oracles. The universal inequalities do not require rational entries. Original paid Reads, source provision, program and table length, numerical representation, retained memory, synthesis, fresh randomness, output, work, energy and physical realization are separate resource accounts. Arbitrarily long legal rejection and return histories and the exact rational sampler's possible retries rule out a finite worst-case total-work or output-length conclusion. The finite-state bounds do not assert a fixed-resource optimum.

## 9. Remaining common-model frontier

The required private decreases narrow the original common-model frontier while the true posterior rises on the identical acquired edge. Whether those decreases can coexist with every endpoint word box, supported interior configuration loss and necessary positive return motion in one exact finite generator remains open. A concrete next problem is a nonnative realization satisfying (3.5), both acquired flows and the complete endpoint conditional boxes with each alpha-edge sign retained. A positive unrestricted gap still needs an upper restriction on available decreases or an evaluated corrected all-shape certificate. A zero-infimum statement needs a lawful quantified vanishing family; exact attainment needs one finite complete table. Nonattainment alone gives neither. Fixed-resource optima and hard-defect feasibility are separate questions. No complete unrestricted frontier claim follows from the present signed relation.

## 10. References

- **ST.** [Randomized stopped-tail minimax](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md), Sections 1–3.
- **E1.** [Full E1 scope extension](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FULL_E1_SCOPE_EXTENSION.md), Section 2.
- **CLIP.** [Risk-controlled emission moment feasibility](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md), Sections 2–5.
- **ALPHA.** [Acquired-alpha calibration compatibility](https://github.com/the-omega-institute/trureturing/blob/dea8221f73f9fa9dc9044789e16b2cd93c6a45c5/docs/develop/theory/AURIC_FIB_ATOM_ACQUIRED_ALPHA_CALIBRATION_COMPATIBILITY.md), Sections 3–7; body SHA256 `d8813ebb99918872072e9e37b29bd2954dedc3c13318b94d8b206c958777062a`.
- **MOTION.** [Actual-return forecast motion](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_RETURN_FORECAST_MOTION.md), Sections 1–8; body SHA256 `81a2612f0bff1141b4e335cd4a06885ea63ff9bfaaffe06aea140e960f7be0aa`.
- **MIXSEP.** [Uniform mixture separation](https://github.com/the-omega-institute/trureturing/blob/37453819032a4873639381066b0f43946b7deed0/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_MIXTURE_SEPARATION.md), Sections 2–6.
- **MIXED.** [Mixed-phase defect attainment](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MIXED_PHASE_DEFECT_ATTAINMENT.md), stated law/law and law/conf attainments.
- **SWITCH.** [Configuration/law switch attainment](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONFIGURATION_LAW_SWITCH_ATTAINMENT.md), stated conf/law attainment.
- **NATIVE.** [Native-mixture recurrence obstruction](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md), Sections 3–7.
- **PAID.** [Effective paid-history certificates](https://github.com/the-omega-institute/trureturing/blob/31513930de85c7ab973bdf58c2a3c821903db164/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md), especially Sections 2, 9–15; body SHA256 `ed9697ab2f9d7bd05b136d26dff537001868934e39c2e9393236de01b9cf3289`.
- **KB.** [KBonacci self-calibrating boundaries](https://github.com/the-omega-institute/trureturing/blob/dea8221f73f9fa9dc9044789e16b2cd93c6a45c5/docs/develop/theory/KBONACCI_SELF_CALIBRATING_BOUNDARIES.md), Sections 16–22.
- **KIM.** [Kimberling array first occurrence](https://github.com/the-omega-institute/trureturing/blob/dea8221f73f9fa9dc9044789e16b2cd93c6a45c5/Blueprint/D5/S1/Recurrence/KimberlingArrayFirstOccurrence.md) and [Row pairs](https://github.com/the-omega-institute/trureturing/blob/dea8221f73f9fa9dc9044789e16b2cd93c6a45c5/Blueprint/D5/S1/Recurrence/KimberlingArrayRowPairs.md).
- **LOCAL.** [Local reconstruction and loop correction](https://github.com/the-omega-institute/trureturing/blob/dea8221f73f9fa9dc9044789e16b2cd93c6a45c5/docs/develop/theory/AURIC_FIB_ATOM_LOCAL_RECONSTRUCTION_AND_LOOP_CORRECTION.md), Sections 1–6.
- **OBS.** [Observation update and return prediction](https://github.com/the-omega-institute/trureturing/blob/dea8221f73f9fa9dc9044789e16b2cd93c6a45c5/docs/develop/theory/AURIC_FIB_ATOM_OBSERVATION_UPDATE_AND_RETURN_PREDICTION.md), Sections 6–10.
- **TRI.** [Response triangle and internal memory](https://github.com/the-omega-institute/trureturing/blob/dea8221f73f9fa9dc9044789e16b2cd93c6a45c5/docs/develop/theory/AURIC_FIB_ATOM_RESPONSE_TRIANGLE_AND_INTERNAL_MEMORY.md), Sections 1–11.
- **CK.** Taolue Chen and Stefan Kiefer, [On the Total Variation Distance of Labelled Markov Chains](https://arxiv.org/html/1405.2852v1), Theorem 7, Corollary 8 and Proposition 12.
- **TS.** Hamed Taghavian and Jens Sjolund, [Minimal positive Markov realizations](https://arxiv.org/html/2502.21102v3), Sections III–V.
- **CJM.** Wojciech Czaja, Philippe Jaming and Mate Matolcsi, [An efficient algorithm for positive realizations](https://arxiv.org/html/math/0612551v2), Sections 2–4.
- **MW.** Alex Monras and Andreas Winter, [Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem](https://arxiv.org/html/1412.3634v1), Sections 2, 4 and 7.
- **SIMPLEX.** [Record simplex and higher-order compatibility](https://github.com/the-omega-institute/trureturing/blob/dda430bbcb110d3fea2c085a21d09577fba5f735/docs/develop/theory/AURIC_FIB_ATOM_RECORD_SIMPLEX_AND_HIGHER_ORDER_COMPATIBILITY.md), Section 9, the posterior-increase identity; Sections 1–8, their stated five-mode record contracts.
- **JM.** [Joint moment fibres](https://github.com/the-omega-institute/trureturing/blob/dda430bbcb110d3fea2c085a21d09577fba5f735/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md), Sections 49–51.
- **RT.** [Arithmetic holographic RT](https://github.com/the-omega-institute/trureturing/blob/dda430bbcb110d3fea2c085a21d09577fba5f735/docs/develop/theory/ARITHMETIC_HOLOGRAPHIC_RT.md), Section 41.
- **TREE.** [Actual observer bounded lower bounds](https://github.com/the-omega-institute/trureturing/blob/dda430bbcb110d3fea2c085a21d09577fba5f735/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.md), immutable-tree, truthful-cache and nominal-carrier contract.
- **KB-TRACE.** [Original acquired trace](https://github.com/the-omega-institute/trureturing/blob/dda430bbcb110d3fea2c085a21d09577fba5f735/Blueprint/D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.md), same original archive, actual phase and paid execution contract.
- **KB-EXEC.** [Original execution bridge](https://github.com/the-omega-institute/trureturing/blob/dda430bbcb110d3fea2c085a21d09577fba5f735/Blueprint/D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.md), original/native record and fee correspondence.
- **KB-PHYSICAL.** [Physical window decoder](https://github.com/the-omega-institute/trureturing/blob/dda430bbcb110d3fea2c085a21d09577fba5f735/Blueprint/D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.md), original physical INITIAL decoder and its hypotheses.

## 追加锚（本行以下为增补区）
