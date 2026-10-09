# Certified small risk does not effectively localize acquired history

## 1. Mathematical setting and reused results

**Convention 1.1 (original source and representation).** Fix the common-depth paid Read/Stop source and full original records of PH1.2–1.5. The representation category is exactly PH37.1–37.2's COMPLETE sequential bit machine with source-independent fair-bit microsteps, finite resident code/data, every persistent private phase and a uniformly bounded peak snapshot. Services return almost surely at every allowed entrance. Both original compatibility equations are required. The source/prior is installed once; none of the constructions below changes its operations or supplies a runtime posterior. A finite digital description and executable full-law consumer are distinct from a semantic real-coordinate law.

**Mathematical reference 1.2 (suppliers and scope).** PH denotes [Phase-coherent full-tail minimax](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md), EF denotes [Endpoint-floor history localization](RECURSIVE_RELATIONAL_OBSERVATION_ENDPOINT_FLOOR_HISTORY_LOCALIZATION.md), ST denotes [Randomized stopped-tail minimax](RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md), and EA denotes [Effective acquisition horizon](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_ACQUISITION_HORIZON.md). Project statements are taken at the common published snapshot [e23df943779556edf1d488df6c29bf6483b0a818](https://github.com/the-omega-institute/trureturing/tree/e23df943779556edf1d488df6c29bf6483b0a818).

PH14–17 supplies the rational near-optimal arc, isolated optimum and baseline unbounded-tail bounds. EF8.2 supplies uniform finite existence at each fixed complete description budget; PH42/45/46 supplies a computable acquired endpoint lower witness. EA7.1–7.2 supplies the strict-cutpoint premise and finite simple separated-value amplifier; EA8.1 supplies a fully charged finite graph serialization and interpreter. Those proofs are reused with explicit parameter correspondence below. EA9.1's high-risk counterfamily alone does not settle the promised class here. The new bridge is the strict positive affine perturbation in §§3–6, which keeps both compatibilities and an arbitrarily small prescribed excess over the optimum, while the original acquired-word supremum remains non-effective at a fixed positive precision.

## 2. Original source, full records and four objectives

**Definition 2.1 (fixed installed source).** Fix a finite depth menu $S$ containing 1 and 2 and a feasible rational every-mass floor $b_{\rm src}>0$, so $|S|b_{\rm src}\le1$. Write

$$
\mathcal P_{S,b_{\rm src}}=\{\mu:\operatorname{supp}\mu=S,\ \mu(k)\ge b_{\rm src},\ \sum_{k\in S}\mu(k)=1\}.
$$

A source is installed once. Before the first actual Read it draws one common $K\sim\mu$; every actual paid Read, including rejected seed pairs and payload returns, uses this same $K$. Conditional on $K=k$, fresh Read letters have probabilities $r_k=F_{k+1}/F_{k+3}$ for $\alpha$ and $1-r_k$ for $\beta$. Here $r_1=1/3$, $r_2=2/5$ and $3/8\le r_k\le5/13$ for $k\ge3$. Nothing below chooses, copies or resamples this source.

Retain the entire PH1.2 original transition table $\delta_0$ and original configuration $C_0$: both seeds, bare fields, selector, all tree records $B,Q^+,Z$, ordered writes and latch, parser, permissions, completion and delivery. The seed parser rejects equal pairs, accepts $\alpha\beta$ as seed 0 and $\beta\alpha$ as seed 1. In each payload phase $p_i$, $\alpha$ completes marker 0 and $\beta$ enters the suspended phase; there $\alpha$ returns to $p_i$ and $\beta$ completes marker 1. The third write finishes before latch. The same history's latched record is held through segment four, its completion, the sole original Stop and delivery. Pending permits only that Stop; delivered has empty residual; neither permits Read. The monitor added below never changes a record, original event, permission or source probability.

For a history $h$, let $A(h),B(h)$ count all acquired letters and let $\ell(h)=A(h)+B(h)$ count paid Reads. The complete actual target, at an active fourth-segment cut with original configuration $c$, is

$$
T_h^\mu=(I_c)_*\sum_{k\in S}\nu_h(k)P_{s,r_k},\qquad
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}{\sum_i\mu(i)r_i^{A(h)}(1-r_i)^{B(h)}}.
\tag{2.1}
$$

This is the common-source posterior, with strictly positive denominator. The posterior, acquired counts and probability rows below are analysis objects, never runtime inputs. The full legal raw carrier at $p_4$ consists of $u_{j,0}=(\beta\alpha)^j\alpha$, $u_{j,1}=(\beta\alpha)^j\beta\beta$ for $j\ge0$, and the legal infinite noncompletion outcome. At the suspended cut it consists of $\beta$ or $\alpha u_{j,z}$ and its infinite outcome. The already acquired suspended $\beta$ is absent from future letters. With $a_r=r(1-r)$,

$$
\begin{aligned}
P_{p,r}(u_{j,0})&=r a_r^j,&P_{p,r}(u_{j,1})&=(1-r)^2a_r^j,\\
P_{\beta,r}(\beta)&=1-r,&P_{\beta,r}(\alpha u_{j,0})&=r^2a_r^j,&
P_{\beta,r}(\alpha u_{j,1})&=r(1-r)^2a_r^j.
\end{aligned}
\tag{2.2}
$$

PH/ST supplies the same-history transcript map $I_c$: each raw word executes the original ordered event blocks, held-record actions, completion, Stop and delivery from this $c$. Reading back letters gives its inverse on the image. It preserves TV, including the noncompletion outcome, rather than discarding records or comparing records from different histories. The pinned formal source `FourthSegmentStoppedLaw.lean` supplies `legalRead`, `legalStop`, `first_completion_normal_form`, `noncompletion_fiber`, `actual_noncompletion_mass_zero` and `actual_fourth_segment_stopped_word_law`, with $\alpha=0,\beta=1$. The common-$K$, Bayes and full-record bridges are the separate PH/ST contracts. Mathematical `totalRead` grants no terminal Read.

**Definition 2.2 (original full-history consumer).** A randomized observer has a source-independent actual row $\rho_h=\eta P_h$ over complete ready configurations, and an executable full residual decoder $D_z$ for each configuration. Define

$$
e_{\rm law}(h)=\operatorname{TV}\!\left(\sum_z\rho_h(z)D_z,T_h^\mu\right),\qquad
e_{\rm conf}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu).
$$

Let $\mathcal H_p,\mathcal H_\beta$ be all original positive finite histories after the third latch at their respective fourth-segment phases, retaining every seed, record and finite rejection/return word. For $H\ge7$, put

$$
\Phi_H^{j_p,j_\beta}=
\max\left\{\sup_{h\in\mathcal H_p,\ell(h)\le H}e_{j_p}(h)-\rho_p,
\sup_{h\in\mathcal H_\beta,\ell(h)\le H}e_{j_\beta}(h)-\rho_\beta\right\},
\tag{2.3}
$$

where $\rho_p=1116529/22781250$, $\rho_\beta=239/6750$ and $(j_p,j_\beta)$ independently ranges over the four law/conf choices. The uncapped version is $\Phi_\infty$. Every error still uses the full unbounded future transcript. $H$ limits only acquired history. Pending/delivered errors are zero. The representation is nonlinear normalized sequential generation; matrix coordinates do not supply linear-response memory bounds or finite bits from real-coordinate count.

## 3. Effective constants and the infinite-tail affine neighborhood

**Definition 3.1 (arc and strict rational certificate).** Reuse PH14–17's constants and functions, distinguishing the arc coefficient $g$ from the source floor:

$$
\begin{aligned}
c&=11758471/22781250,&C&=1944/390625,&d_0&=5261/6750,&N&=2c+C,\\
S_a&=1+a+a^2,&H_a&=2S_a+a^3,&g&=N/H_a,\\
u&=1-a-g,&v&=a/(a+g),&
e&=(ga^3-C)/2,&f&=g(1+a)/(a+g)-d_0.
\end{aligned}
\tag{3.1}
$$

Let $a_*$ be PH17's isolated algebraic root $e=f$, $t_*=e(a_*)$, and $a_1$ the arc endpoint $f=0$. Fix a rational requested near-optimal tolerance $\tau>0$ and write $\zeta=\min\{\tau,1/1000\}$. Rational bisection using the strictly decreasing $f-e$ chooses a root bracket $a_-<a_*<a<a_1$ with

$$
0<f<e,\qquad e(a)-e(a_-)<\zeta/4.
\tag{3.2}
$$

All comparisons are finite rational comparisons, including the signs at the two bracket endpoints; hence $0<e-t_*<\zeta/4$. Existence and termination use the published monotonicity, root isolation and continuity, not a risk oracle. Define $l=1-u$, $k=(1-v)S_a>0$ and $k_2=(1-v)(S_a+a^3)>0$. Choose $\lambda$ to be one half the minimum of

$$
\begin{gathered}
2/5-u,\quad l\left(1-\frac{2/27}{ua}\right),\quad
l\left(1-\frac{32/6561}{ga^3}\right),\quad
l\left(1-\frac{C}{ga^3}\right),\quad
\rho_p-4/125,\quad \frac{\zeta}{4k}.
\end{gathered}
\tag{3.3}
$$

These rationals are strictly positive: PH15 gives $u<2/5$, $ua>2/27$, $ga^3>C>32/6561$ and $\rho_p>4/125$. Thus $\lambda>0$ is computable independently of the automaton, prior and history. Set

$$
\Delta=k\lambda>0,\qquad \epsilon_0=\Delta/8.
\tag{3.4}
$$

The rational certificate comprises the bracket signs, stochastic parameter ranges and the finite inequalities (3.2)–(3.3). Its production, serialization and checking are separately paid offline work.

**Lemma 3.2 (complete affine risk, every future word).** Let $Q,V$ be PH15's ordinary $p,\beta$ laws of $G(a)$. For $0\le x\le\lambda$ let

$$
Q^x=(u+x)\delta_{[\alpha]}+(l-x)(\beta V).
\tag{3.5}
$$

Completion and Stop are included by $I_c$. Its exact full-tail distances are

$$
\operatorname{TV}(Q^x,P_{p,r_1})=\rho_p+e+kx,\qquad
\operatorname{TV}(Q^x,P_{p,r_2})=\rho_p+e-k_2x.
\tag{3.6}
$$

For every $k\ge3$, $\operatorname{TV}(Q^x,P_{p,r_k})<\rho_p$. All laws retain the legal infinite outcome with zero mass.

**Proof.** Write $t=1-x/l$. Expansion of (3.5), using $a=lv$ and $g=l(1-v)$, gives

$$
Q^x(u_{0,0})=u+x,\quad Q^x(u_{j,0})=tu a^j\ (j\ge1),\quad
Q^x(u_{j,1})=tg a^j\ (j\ge0).
\tag{3.7}
$$

The ordinary laws complete with geometric factor $a<6/25$; (3.5) completes almost surely and its masses sum to one. Put $a^{\rm src}_1=2/9$, $a^{\rm src}_2=6/25$. For the zero words, $1/3<u+x<2/5$. At $j=1$, (3.3) gives $tu a>2/27$, while $tu a\le ua<(2/5)(6/25)$ by PH15. Ratios to endpoint 1 increase with $j$ since $a>2/9$; ratios to endpoint 2 decrease since $a<6/25$. Both comparisons therefore hold for every $j\ge1$.

For one words at $j=0,1,2$, PH15 has $ga^j<(4/9)(2/9)^j$; decreasing their masses preserves this inequality. At $j=3$, (3.3) gives $tga^3>32/6561$ and $tga^3>C=(9/25)(6/25)^3$. The first ratio increases thereafter, so all $j\ge3$ exceed endpoint 1. The second ratio decreases, so all $j\le3$ exceed endpoint 2. At $j=4$, PH15 has $ga^4<(9/25)(6/25)^4$; reducing it and propagating the decreasing ratio gives this comparison for every $j\ge4$. These finite gates and geometric ratios prove the entire infinite sign partition.

Consequently the positive coordinates of $P_{p,r_1}-Q^x$ are exactly $E=\{u_{0,1},u_{1,1},u_{2,1}\}$, and those of $Q^x-P_{p,r_2}$ are exactly $F=E\cup\{u_{3,1}\}$. For normalized countable laws TV equals the sum of positive differences. PH14–15 gives $P_{p,r_1}(E)=\rho_p+c$ and $P_{p,r_2}(F)=c-\rho_p+C$, while $Q^x(E)=gS_a-kx$ and $Q^x(F)=g(S_a+a^3)-k_2x$. The arc identity $gH_a=2c+C$ gives (3.6).

The two first-letter branches in (3.5) are disjoint, so $\operatorname{TV}(Q^x,Q)=x$. PH15.10's complete geometric bound for every nonendpoint parameter is $\operatorname{TV}(Q,P_{p,r_k})<4/125$. Triangle inequality and (3.3) give $4/125+x<\rho_p$. This controls the entire interval of nonendpoint parameters, not a checked finite list of depths. Pushforward through the same $I_c$ proves the identical statements for full original transcripts. No future-tail truncation or first-letter surrogate loss was used. $\square$

## 4. Paid history monitor and two separate compatibilities

**Definition 4.1 (finite acquired-word monitor).** Let $\mathcal A$ be any finite rational probabilistic automaton with a finite nonempty alphabet $\Gamma$, rational initial row $\eta_{\mathcal A}$, rational row-stochastic matrices $T_i$, and accepting states $F_{\mathcal A}$. Write $p_{\mathcal A}(w)=\eta_{\mathcal A}T_w\mathbf1_F$ and $V_{\mathcal A}=\sup_{w\in\Gamma^*}p_{\mathcal A}(w)$. Runtime holds one sampled automaton state; it never holds this probability row.

Set $X=\alpha\alpha$, $Y=\beta\beta$. Choose $d=\max\{1,\lceil\log_2(|\Gamma|+1)\rceil\}$ by integer comparison. Assign the $|\Gamma|$ data letters codes $0,\ldots,|\Gamma|-1$ and the monitor delimiter $\diamond$ code $|\Gamma|$, all at width $d$ over pair tokens $X,Y$. Unassigned codes invalidate the monitor. At completed data blocks, sample the corresponding $T_i$ transition with fresh source-independent fair bits. At the completed delimiter freeze the sampled state. Thereafter only $Y$ rejections are allowed by the monitor, and they leave that state unchanged; any $X$ invalidates it. An accepted unequal pair before delimiter, an incomplete block, or a seed other than 1 invalidates it. Invalidity is absorbing for private monitoring only; it never suppresses an actual original history.

After valid delimiter and any number of $Y$ pairs, the monitor recognizes exactly the original six-letter suffix

$$
S_0=\beta\alpha\mid\beta\beta\alpha\alpha.
$$

The accepted seed is 1 and the first three markers are 100 with no payload returns. Monitor suffix states are a bounded literal prefix matcher, executed after each unchanged original update and its entire ordered event block. Only the final suffix state, reached after the third write and latch, is a special gate. Every other seed, record, return and malformed word uses the baseline. At the first fourth-segment Read the sampled automaton label and gate are cleared to a fixed baseline tag, for either letter. This is an internal holding update at an existing Read, not an additional operation.

Earlier than the third latch, every synthetic next-letter probability is $1/2$, independently of private state. At a special gate in $p_4$, emit synthetic $\alpha$ with probability $u+\lambda\mathbf1_F(q)$. All other $p_4$ cuts use $u$ and all suspended fourth cuts use $v$. The same source-independent monitor update is used after an actual or synthetic letter. Pending generates only the original Stop and delivery; delivered has empty residual. $D_z$ is the executable full law of this program, rendered from that configuration's own original record.

**Lemma 4.2 (all source, event and permission fibers).** This construction leaves the original source and every positive finite original history unchanged. At a fourth-segment gate the history is exactly

$$
h(w,n)=\operatorname{enc}(w)\operatorname{enc}(\diamond)Y^nS_0,
\qquad w\in\Gamma^*,\ n\ge0,
\tag{4.1}
$$

with paid length $2d(|w|+1)+2n+6$. The probability of its retained accepting label is exactly $p_{\mathcal A}(w)$, including $w$ empty. All other fourth-segment histories have baseline reports. Both exact compatibilities hold independently at every original history and every legal positive-prediction continuation, from initialization to delivery.

**Proof.** Before seed acceptance every completed $X$ or $Y$ is an original paid rejection. The fixed-width parser recognizes a sequence of complete data blocks followed by its first delimiter, then only $Y$ pairs. Its finite suffix matcher recognizes seed 1 followed by the exact four-letter payload suffix, and nothing else. Incomplete/unassigned codes or any mismatch are private dead tags. Induction at pair/block boundaries proves this grammar; no input history is removed. The suffix contains two seed Reads and four payload Reads, completing exactly markers 100. Its last $\alpha$ triggers the original third write and then latch, before the monitor gate is set. Reading any fourth letter clears the gate, so it cannot reappear. Both seeds and all eight marker triples continue through the unchanged original table. Writes, event ordering and original menus are unaltered on each such fiber, including partial prefixes, payload returns, completion and terminal cuts.

The automaton's initial sample and letter updates are private and source-independent. Induction over complete data blocks gives exactly the row $\eta_{\mathcal A}T_w$ conditional on the actual source word. Neither delimiter, padding nor suffix changes the sampled label. Hence (4.1) has acceptance probability $p_{\mathcal A}(w)$. This is a conditional distribution of actual charged states. The runtime initial sample is its source-independent finite private automaton state; no source-prior sample or posterior is supplied to a report.

First consider per-configuration generation. The program samples a synthetic letter with declared probability $q_z(x)$, using fresh bits, and then executes exactly the actual holding kernel $P_x$, with independent fresh bits for a possible automaton transition. For its full original event block $E(c,x)$ and residual measurable event $A$,

$$
D_z((x,E(c,x))A)=q_z(x)\sum_{z'}P_x(z,z')D_{z'}(A).
\tag{4.2}
$$

Thus its joint effective kernel is $q_z(x)P_x(z,z')$. The entire original record and deterministic event block are part of this identity. Finite cylinders and almost-sure service return define the full decoder, including zero-mass noncompletion. Earlier fair synthesis has seed success probability $1/2$ and payload return factor $1/4$; after latch there is at most one altered letter followed by the geometric $G(a)$. Hence synthesis completes almost surely, from every reachable allowed entrance, without adding a nonreturning internal outcome. This proves the first compatibility.

For actual-history marginalized compatibility, let $\rho_h$ be the actual row in the common original $c$ fiber. Conditioning (4.2) on a predicted $x$ yields the weighted successor mixture

$$
\frac{\sum_z\rho_h(z)q_z(x)\sum_{z'}P_x(z,z')D_{z'}}{\sum_z\rho_h(z)q_z(x)}.
\tag{4.3}
$$

The next actual report is the unweighted successor mixture $\sum_{z'}(\rho_hP_x)(z')D_{z'}$. Before the special cut $q_z(x)$ is constant over the entire reachable private-state fiber of a fixed actual history, even though its future decoder may depend on the label. This cancels the weight in (4.3). At a special cut the letter probabilities can differ, but for each fixed $x$ every predecessor label has the same successor decoder: for $\alpha$ it is the deterministic original completion/Stop residual; for $\beta$ it is $V$ at the common original suspended successor and record. Label erasure therefore makes both mixtures equal. Afterward every report is baseline; deterministic original holding and the same kernel identity give equality. Terminal Stop has probability one; delivered has no next operation. All declared active letter probabilities are strictly positive. Induction proves the second compatibility for every finite legal positive continuation, separately from (4.2). Keeping unequal successor laws at a variable-probability step would invalidate (4.3); no general randomized-mixture principle is presumed. $\square$

## 5. Complete digital realization and effective promise certificates

**Proposition 5.1 (effective rational-service extension of the published compiler).** Definition 4.1 has a total finite compilation into the exact PH37 COMPLETE category, with a computable sufficient integer budget $B_{\mathcal A,\tau}$. It uses EA8.1's fixed graph-row presentation and charged sequential-bit interpreter. The changes are its finite monitor and rational, almost-surely returning sampler graphs; the published graph layout, addressing and installer bound apply unchanged to the resulting enlarged finite graph.

**Proof.** For each rational initial/transition row, convert its entries to nonnegative integer weights $a_1,\ldots,a_q$ with common denominator $D=\sum_i a_i\ge1$. For that row put $j_D=\lceil\log_2D\rceil$, computed by integer powers; if $D=1$ use a deterministic transition. Otherwise draw exactly $j_D$ fresh fair bits into a finite prefix state. Reject candidate integers $t\ge D$, returning to the same row's empty prefix state, and assign $t<D$ to the unique half-open cumulative interval for its destination. The probability of any destination $i$, after summing the geometric repetitions, is

$$
\sum_{n\ge0}(1-D/2^{j_D})^n\,a_i/2^{j_D}=a_i/D.
\tag{5.1}
$$

Each draw succeeds with probability $D/2^{j_D}>1/2$, or one when $D$ is a power of two. A width based on the largest denominator is an allocation bound, not the number of bits drawn for every row. The probability of $n$ consecutive rejections is $(1-D/2^{j_D})^n\to0$. No retry counter or random tape is retained. Apply the same construction to $u,v,u+\lambda$ and the finite initialization row. Letter-choice bits and any automaton-update bits are disjoint fresh calls, so the effective joint kernel is precisely $q_z(x)P_x(z,z')$.

For clarity, each sampler is an explicit finite graph: its nodes are the bit prefixes of lengths $0,\ldots,j_D$, terminal integers branch to a fixed destination or back to the empty prefix. Rational weights and cumulative intervals are computed offline. Comparison may be enumerated into deterministic nodes; alternatively finite bit comparisons expand into the same finite graph. Row indices, prefix values, return labels and the selected sampled state are all nodes or charged fields. Take its product with the finite pair/block/suffix parser, validity/frozen/gate flags, the one sampled automaton state and the entire original $C_0$. Expand each unchanged original lookup, event block and record rendering into bounded deterministic graph nodes. The original block executes completely, including write-before-latch, before the private update. All ready returns normalize sampler prefixes and transient cursors; only the declared finite original and private holding state remains. No acquired count, old word, posterior or probability row is present. This constructs a finite logical graph $G$ by terminating enumeration of finite sets, including all low-probability sampler phases and every legal original entrance. Rejection edges are cycles in $G$; they do not enlarge its state set.

Now apply the *serialization and interpreter construction* of EA8.1, not its particular dyadic sampler or balanced monitor. In its notation, set $N=|G|$, $N_0=|C_0|$, $A_E$ equal to this graph's full finite output/event alphabet, $w=\max\{1,\lceil\log_2N\rceil\}$, $\sigma=\max\{1,\lceil\log_2A_E\rceil\}$. Its $T_0$ is the same entire original table and rendering dictionary, retained even when redundant in $G$; $H_{\mathcal A}$ is its self-delimited graph/data metadata. Any retained literal automaton rows, rational denominators/thresholds, emission constants and codebook are serialized in this charged data segment, even when the graph already compiles their effect. With the fixed interpreter and loader of length $I$, the published rule gives

$$
\begin{aligned}
T_{\mathcal A}&=H_{\mathcal A}+N(6+3w+\sigma)+T_0,\\
S_{\mathcal A}&=T_{\mathcal A}+I+N+N_0+A_E+1,\\
R_{\mathcal A}&=\left\lceil\log_2\bigl(256(S_{\mathcal A}+1)^2+1\bigr)\right\rceil,\\
B_{\mathcal A,\tau}&=2(T_{\mathcal A}+I+J_{\mathcal A})+32R_{\mathcal A}+64.
\end{aligned}
\tag{5.2}
$$

Here $J_{\mathcal A}$ is exactly EA8.1's allocation-header length. Its thirty-two integer slots include actual and synthetic graph nodes, original control copies, PCs, all heads/addresses, loop and field cursors, event/render positions, operands and scratch; its 64 Boolean slots include modes, carries, fair/input/output bits, finite provider and handshake flags. Sampler prefixes and any retained random phase are already part of $G$ and its current-node field. Thus they are charged even when also covered redundantly by a reserved slot. Static tables, code, constants, codebook and layout metadata are in $T_{\mathcal A}+I+J_{\mathcal A}$; both actual and synthetic state exist simultaneously. The leading factor two includes the whole incoming installation image as well as the resident copy. EA8.1's inequalities (8.2)–(8.4), with these exact values, cover every code/data/RAM/installation address and intermediate, without circular field widths or free pointers. The row interpreter and addressing proof use only finiteness of $G$, its deterministic/fair-bit nodes and finite row alphabet. They do not require the absence of sampler cycles. This proves a total computable sufficient COMPLETE charge, rather than a coordinate-count argument or measured minimum.

Initialization makes no actual Read. A legal actual update uses bounded original event work and at most one almost-surely returning row service. A synthetic next-letter service uses one almost-surely returning letter service followed by the same update. The finitely many deterministic operations between draws terminate, so every allowed service returns almost surely; a rejected draw has no report/query cut. The finite-width PC, heads and sampler scratch persist during each such service and are included in (5.2). All microsteps have probabilities $0,1/2,1$. Deterministic baseline behavior can fill unused ready encodings, and proof-only terminal matrix totalization grants no terminal Read. Lemma 4.2, rather than compilation alone, supplies both compatibility obligations.

The resident report is the executable finite generator identity with its current charged configuration, or a serial consumption of the same full law on the synthetic track. It does not use actual source Read. Output, buffer and receiver archive accounts remain those of EA8.1/PH37.2; a growing receiver archive is not fed back into holding. Offline graph construction, rational arithmetic and certificate checking have their own paid computation, stored tables and output. If such work is part of online installation, apply EA8.1's explicit compiler-peak convention: run the terminating deterministic bit compiler, record its finite maximum occupied tape and control, and add its code/data/peak address allocation to (5.2). Any additional online provider or buffer must likewise enter COMPLETE. There is no value or semantic-admissibility query.

For the fixed negative source $S=\{1,2\},\mu=(1/2,1/2)$, reuse EA8.1's source-provider construction verbatim: one fair-bit choice of the common $K$, then fresh finite rejection sampling of $1/3$ or $2/5$ at each paid Read. Its fixed charged code, depth latch, PCs, candidate/cursor/buffer and installation peak form a separate constant $B_{\rm src}$. If source-provider storage is included in a horizon budget, use $B_{\mathcal A,\tau}+B_{\rm src}$; the computable fixed addition does not affect the contradiction. Any other fixed rational finite prior has the same finite-row source realization and separate computable charge. The uniform mathematical bounds over real priors below do not claim a finite digital source implementation for arbitrary real masses. $\square$

**Proposition 5.2 (effective simultaneous risk promise).** Every compiled member, on every $\mu\in\mathcal P_{S,b_{\rm src}}$, satisfies both phase risks in both orders strictly below $1/12=1/3-1/4$, and all four objectives satisfy $t_*<\Phi_\infty<t_*+\tau$. A finite structural certificate for these assertions is computably produced from the automaton table, without a value, full-risk or admissibility oracle.

**Proof.** The exact correspondence proved in §6 is $\Phi_\infty=e+\Delta V_{\mathcal A}$. Stochastic rows and a normalized initial row give $0\le V_{\mathcal A}\le1$, without solving its value problem. Thus $0<\Phi_\infty-t_*<\zeta/4+\zeta/8=3\zeta/8<\tau$. The phase bounds in §6, $R_{j,p}\le\rho_p+e+\Delta$ and $R_{j,\beta}=\rho_\beta+f$, are below $\rho_p+1/10000+3/8000<1/12$ and $\rho_\beta+1/10000+1/4000<1/12$ respectively, using PH17's $t_*<1/10000$ and $f<e$. All comparisons are strict rational upper certificates. Include row nonnegativity/sums, normalization, root bracket, finite gates, literal field/compiler layout and Lemmas 3.2/4.2/6.1's proof schema instantiated with the supplied finite tables. This certificate controls the entire family uniformly through stochasticity. The producer computes none of $V_{\mathcal A},\Phi_\infty$ or arbitrary-code semantic membership. General promise recognition is a different problem. Certificate material is not an acquired runtime input. $\square$

## 6. Exact original full-risk value and reachable lower witnesses

**Theorem 6.1 (all four original objectives, fixed source).** For the constructed observer and every installed $\mu\in\mathcal P_{S,b_{\rm src}}$,

$$
\begin{aligned}
R_{\rm law,p}=R_{\rm conf,p}&=\rho_p+e+\Delta V_{\mathcal A},\\
R_{\rm law,\beta}=R_{\rm conf,\beta}&=\rho_\beta+f,\\
\Phi_\infty^{j_p,j_\beta}&=e+\Delta V_{\mathcal A}
\quad\text{for each of the four pairs}.
\end{aligned}
\tag{6.1}
$$

These equalities compare suprema; they do not assert law/conf equality at every finite mixed-posterior history or attainment at one finite history. For every fixed finite automaton word $w$, the positive actual histories (4.1), within this same source, have accepting probability $p_{\mathcal A}(w)$ and their two complete errors tend to $\rho_p+e+\Delta p_{\mathcal A}(w)$ as $n\to\infty$.

**Proof.** At a gate history decoding $w$, write $\theta=p_{\mathcal A}(w)$. Per-label reports are $Q^0$ and $Q^\lambda$, so the law report is $Q^{\lambda\theta}$ by (3.5)'s affine formula. Convexity against the actual posterior in (2.1), then Lemma 3.2, gives

$$
e_{\rm law}(h)\le\rho_p+e+\Delta\theta.
\tag{6.2}
$$

For conf first bound each label's distance to that same actual target by the posterior-weighted pure-source distances, obtaining bounds $\rho_p+e$ and $\rho_p+e+\Delta$; average with weights $1-\theta,\theta$ to obtain exactly the same upper bound. At every other $p$ cut the report is $Q$, and PH15 gives $e_j\le\rho_p+e$. Every suspended cut has report $V$ and PH15 gives $e_j\le\rho_\beta+f$. This covers all actual seeds, tree-record fibers and arbitrary returns, not just the witness grammar. Terminal errors vanish.

For the reverse $p$ bound, fix $w$ first. Write $A_0,B_0$ for the fixed counts in $\operatorname{enc}(w)\operatorname{enc}(\diamond)S_0$. At (4.1) the entire common-source posterior has odds

$$
\frac{\nu_{h(w,n)}(k)}{\nu_{h(w,n)}(1)}=
\frac{\mu(k)r_k^{A_0}(1-r_k)^{B_0}}{\mu(1)r_1^{A_0}(1-r_1)^{B_0}}
\left(\frac{1-r_k}{2/3}\right)^{2n}.
\tag{6.3}
$$

For every $k\ne1$ in $S$, $r_k>1/3$, so the final factor tends to zero. The finite sum of all these odds tends to zero, yielding $\nu(1)\to1$ for the entire posterior. In fact the other factors are at most $(15/16)^{2n}$, times a finite constant depending on the fixed word and installed prior. Formula (2.1) then gives TV distance to $P_{p,r_1}$ at most $1-\nu(1)\to0$. There was no selection of a free posterior or change of prior.

The retained accepting probability stays exactly $\theta$, independent of $n$. TV is 1-Lipschitz in its target. For law, (3.6) at $x=\lambda\theta$ therefore gives the stated error limit. For conf apply the same Lipschitz estimate to $Q^0,Q^\lambda$ separately, then average: (3.6) gives the identical limit. For any positive accuracy choose a finite $n$ making the target discrepancy smaller; this is a finite actual positive history, not an infinite acquired input. Supremizing first over $n$ for each fixed $w$, then over finite $w$, gives the lower $p$ equality in (6.1). Every word is positive under every supported $k$ because all letter probabilities are strictly between zero and one.

For the suspended phase, its reports are baseline for every actual history. PH15.12's legal endpoint-2 training histories followed by one fourth $\beta$ have true complete suspended law tending to $P_{\beta,r_2}$, and their reports are $V$ because that first fourth Read clears any gate. Reusing PH15.9 and its reachable-history bridge supplies the reverse equality $\rho_\beta+f$ for both orders. The domain is the same original fixed source and records; no new endpoint input is installed. Since $f<e$ and $\Delta V_{\mathcal A}\ge0$, subtracting the two respective radii and taking the original maximum proves the last line. $\square$

**Corollary 6.2 (finite-cap upper consumer).** For $H\ge7$ let

$$
v_H(\mathcal A)=\max_{w\in\Gamma^*,\ |w|\le H}p_{\mathcal A}(w).
$$

This is a terminating exact rational calculation, and all four original objectives obey

$$
\Phi_H\le e+\Delta v_H(\mathcal A).
\tag{6.4}
$$

**Proof.** Enumerate the finite words up to $H$, multiply finite rational matrices and compare rational acceptances. A gate with paid length at most $H$ decodes at most $H$ data letters, by (4.1); every other cut has baseline phase score at most $e$ or $f<e$. Apply (6.2) for the chosen risk order in each phase and take the finite original supremum. This does not evaluate or approximate the future loss by a first-letter loss: (6.2) already proves the full unbounded-tail bound. It needs no exact-TV or semantic-admissibility oracle. $\square$

**Lemma 6.3 (certified finite-cap full-future calculation for this family).** For a constructed member, fixed rational installed prior and finite $H\ge7$, all four $\Phi_H$ values are computably approximable with an explicit absolute error bound. For each chosen order separately, retaining the complete words of indices $j<J$ gives its rational lower value $L_H$ with

$$
L_H\le\Phi_H\le L_H+4^{-J}\qquad(J\ge1).
\tag{6.5}
$$

The calculation is external, terminating finite rational work, with no runtime posterior or full-TV oracle.

**Proof.** Enumerate the finitely many original binary source words of at most $H$ Reads and run the unchanged original finite parser/table to select active legal cuts; deterministic event and permission fibers are determined by that word. All supported depths give each such source word positive probability. Compute its rational posterior using (2.1), and its private accepting probability by rational automaton products only if it is a gate. Other cuts have one baseline decoder. Thus law uses $Q^{\lambda\theta}$ at a gate, conf averages $Q^0,Q^\lambda$ with weights $1-\theta,\theta$, and beta uses $V$.

For a $p$ report $Q^x$, (3.7)'s omitted mass at indices $j\ge J$ is $(1-x/l)a^J$. For $V$ it is $va^J$; its separate single-word $\beta$ atom is always included. The actual omitted masses are respectively $\sum_k\nu_h(k)a_{r_k}^J$ and $\sum_k\nu_h(k)r_k a_{r_k}^J$. All are at most $4^{-J}$ since $a<1/4$ and $a_{r_k}\le6/25<1/4$. Both infinite outcomes have zero mass. For any two such normalized laws the finite half-sum of absolute coordinate differences is a lower TV value; the omitted half-sum is bounded by one half the sum of their omitted masses, hence by $4^{-J}$. For conf apply this bound to each decoder and average with the same actual row; the bound is unchanged. For law compute the mixture's finite coordinates first. Pushforward through this cut's own $I_c$ preserves these statements on complete records, event blocks, Stop and delivery. Taking maxima over the finite original histories and subtracting the exact phase radii preserves the same two-sided enclosure, proving (6.5). Choose a finite $J$ by integer powers until $4^{-J}$ is below any requested rational error. Table enumeration, matrix/posterior arithmetic, work, storage and output remain paid offline. This elementary geometric bound concerns this particular constructed family; it supplies no general semantic membership test or arbitrary-chain full-TV service. $\square$

## 7. Primary strict premise, separated values and non-effectivity

**Mathematical reference 7.1 (strict primary premise).** Reuse EA7.1's attested Gimbert–Oualhadj premise: strict emptiness at cutpoint $1/2$ is undecidable for finite simple probabilistic automata, with finite state/alphabet, point initial state and stochastic transition entries in $\{0,1/2,1\}$. The original primary is *Probabilistic Automata on Finite Words: Decidable and Undecidable Problems*, ICALP author full version, [HAL v3](https://hal.science/hal-00456538v3), Definition 1, §2.1 Definition 2 and Theorem 1. Its problem is existence of a finite word with acceptance strictly greater than $1/2$, not equality of the supremum to one. No value oracle follows from this premise.

**Lemma 7.2 (exact reuse of the separated-value amplifier).** Given any primary simple instance $\mathcal B$, apply EA7.2 with its $A_0=\mathcal B$ and output $A=\mathcal A$. Its output is a finite simple automaton with point initialization and

$$
\begin{cases}
V_{\mathcal A}\le1/2,&\text{if every }p_{\mathcal B}(w)\le1/2,\\
V_{\mathcal A}=1,&\text{if some }p_{\mathcal B}(w)>1/2.
\end{cases}
\tag{7.1}
$$

**Proof by exact correspondence.** The alphabet $\Gamma$ in Definition 4.1 is the complete output alphabet of EA7.2, including its disjoint trial/round punctuation. Its accepting set and initialization are unchanged; its rational tables are the simple stochastic tables supplied there. Every finite $\Gamma$ word, including unfinished or malformed rounds, is encoded as data before our separate monitor delimiter $\diamond$. EA7.2's all-word proof therefore bounds precisely the $V_{\mathcal A}$ consumed by Theorem 6.1 and Corollary 6.2; it does not restrict the supremum to well-formed rounds. Its positive-case value one is a supremum approached by finite words, not an asserted attained word. Every punctuation transition acts only on the private sampled automaton state at an existing paid code completion. It neither initializes a second common source nor creates a reset/copy, experiment, clock or post-Stop operation. The monitor's fixed-width code and beta-rejection padding replace EA3.2's balanced code; no balanced-count or endpoint-2 posterior formula from EA6 is used. Our independent endpoint-1 likelihood proof is (6.3). These identifications satisfy all premises of the reused lemma, yielding (7.1) without a second amplifier construction. $\square$

**Theorem 7.3 (certified promised-class obstruction).** Fix any finite $S\supseteq\{1,2\}$, any feasible rational every-mass floor $b_{\rm src}>0$, any one rational prior $\mu\in\mathcal P_{S,b_{\rm src}}$, and any rational tolerance $\tau>0$. The effectively compiled family of §§3–5, already certified with margin $1/4$ below $1/3$ in both phase risks and both orders and with $t_*<\Phi_\infty<t_*+\tau$ for all four objectives, admits no total computable acquisition-horizon function across its COMPLETE budgets. A correct returned cap means an integer $H\ge7$ with $0\le\Phi_\infty^{j_p,j_\beta}-\Phi_H^{j_p,j_\beta}\le\epsilon_0$ for the chosen order. Failure already holds at the single positive rational accuracy $\epsilon_0=\Delta/8$ of (3.4), independent of the automaton. More strongly, no algorithm guaranteed to return a correct cap and terminate on every constructed description-plus-certificate input exists, for any one of the four original objectives. In particular this holds for the one fixed source $S=\{1,2\}$, $\mu=(1/2,1/2)$, every-mass floor $1/2$.

**Proof.** Suppose such a horizon algorithm exists, for any chosen objective. Given a strict-emptiness instance $\mathcal B$, construct Lemma 7.2's $\mathcal A$, then the fully certified observer and computable budget. Supply the same fixed prior/floor and fixed $\epsilon_0$. All algorithm inputs are genuinely in the promised family; no membership oracle is invoked. Let $H$ be its finite returned cap, increased to at least 7. Monotonicity preserves correctness. The promised inequality, Theorem 6.1 and Corollary 6.2 imply

$$
e+\Delta V_{\mathcal A}-\epsilon_0\le\Phi_H
\le e+\Delta v_H(\mathcal A),\qquad
v_H(\mathcal A)\ge V_{\mathcal A}-1/8.
\tag{7.3}
$$

Compute $v_H$ exactly by finite rational products. In the yes case it is at least $7/8$; in the no case it is at most $1/2$. Comparison with $3/4$ separates these with strict respective slacks $1/8$ and $1/4$. This terminating finite-cap decision contradicts the verified primary strict-emptiness theorem. It does not require calculation of $\Phi_H$, arbitrary full-TV, the unknown value, admissibility of arbitrary programs, or a numerical test of equality to one. External enumeration may be extremely expensive; its computation, storage and output are paid separately. Description-plus-certificate termination only on the constructed family already suffices for the contradiction; the algorithm need not terminate elsewhere. A budget-only total function would be a special case. Every step uses the same actual source/prior, with only the finite installed observer and its charged budget varying. Since (6.1)/(6.4) hold for every objective choice, the argument applies separately to all four. $\square$

**Corollary 7.4 (quantitative margin range actually supported).** The preceding construction also works for any fixed rational margin $m$ with $0<m<1/3-\rho_p-t_*$, keeping any prescribed rational $\tau>0$. Constants and $\epsilon_0$ may depend on $(m,\tau)$, never on the automaton value or history. Its risk promises become $R_{j,s}<1/3-m$.

**Proof.** During root bisection additionally require $\rho_p+e(a)<1/3-m$, and retain (3.2); continuity and the strict hypothesis guarantee termination. Add the positive rational $(1/3-m-\rho_p-e)/k$ to (3.3)'s minimum. Then $\Delta<1/3-m-\rho_p-e$, and all previous gates and near-optimal bounds remain. The beta risk satisfies $\rho_\beta+f<\rho_p+e$ since $\rho_\beta<\rho_p$ and $f<e$. Lemmas 3.2–7.3 are unchanged, with fixed positive amplitude. The margin hypothesis is a computably checkable strict comparison with an isolated algebraic number, or can be supplied with a finite strict bracket. No conclusion is inferred for tighter margins or for further constrained observer subclasses. $\square$

**Domain note 7.5 (numerical input and positive real tolerance).** The effective constructors and algorithms take rational tolerance/margin certificates. Given any strictly positive real desired tolerance, fix a strictly positive rational sub-tolerance below it and apply Theorem 7.3; the resulting family also satisfies the desired real promise. No algorithm for reading an arbitrary opaque real number is required or claimed. For every fixed menu and floor the same construction and certificate are prior-independent and their risk bounds hold on the entire real simplex. The non-effectivity contradiction already fixes one rational prior in that simplex, rather than varying posterior mixtures or prior descriptions.

## 8. Reused finite existence and the coarse positive boundary

**Corollary 8.1 (fixed-tuple existence is retained).** For every fixed $(B,S,b_{\rm src},\epsilon)$ with $\epsilon>0$, there exists a finite horizon uniformly over all admissible at-most-$B$ observers, priors in $\mathcal P_{S,b_{\rm src}}$ and all four original objectives. This remains true upon restricting to the promised family.

**Proof by exact application.** Apply EF8.2 with its tuple $(B,S,b,\epsilon)=(B,S,b_{\rm src},\epsilon)$ and its $\mathfrak D_\mu(B)$ equal to PH37.1–37.2's category of Convention 1.1. Its acquired length is $\ell(h)$ from Definition 2.1, including all seed rejections and payload returns. Its two phase radii and law/conf objective pairs are exactly (2.3); its target is (2.1) on each history's own full original $I_c$ fiber. The observer initialization, update kernels and decoder are unchanged when varying the prior, so EF's fixed-observer comparison applies. Restriction to the promised subclass preserves its bound. No compactness proof or algorithm is inferred. Theorem 7.3 concerns a total computable choice as the budgets vary, so it is consistent with this finite existence. If $|S|b_{\rm src}>1$ the simplex is empty and the statement is vacuous. $\square$

**Corollary 8.2 (exact full-risk upper-minus-lower transfer).** For any original PH37 observer of feasible budget $B\ge1$ on one fixed finite or countable prior $\mu$, a certified rational $0<a_{\rm src}\le\min\{\mu(1),\mu(2)\}$, and a supplied mathematical upper promise $\Phi_\infty^{j_p,j_\beta}\le t_*+\tau$ with rational $\tau\ge0$, define $\gamma_B=2^{-2^{4B+13}}$. A total computable cap for that original full-risk gap follows from PH42/45/46 at rational precision $\epsilon>0$ whenever

$$
\epsilon>\tau-\gamma_B.
\tag{8.1}
$$

In particular every $\epsilon\ge\tau$ is covered. Nonempty promised classes necessarily have $\tau>\gamma_B$; the exact-optimum digital promise $\tau=0$ is empty at every finite COMPLETE budget.

**Proof.** PH42.1 supplies $\Psi^{\rm end}>t_*+\gamma_B$ and $\Phi_\infty\ge\Psi^{\rm end}$. Choose a rational $\delta$ strictly between $\max\{0,\tau-\epsilon\}$ and $\gamma_B$, possible exactly under (8.1), and set $\xi=(\gamma_B-\delta)/2$. PH46.2 with PH45.2's explicit integer cap $H(B,a_{\rm src},\xi)$ gives $\Phi_H>t_*+\delta$ for each original order choice. Therefore the exact original numerical gap satisfies

$$
0\le\Phi_\infty-\Phi_H<\tau-\delta<\epsilon.
\tag{8.2}
$$

This is a full-history/full-future result: the independent upper promise closes the gap from the acquired endpoint lower witness. It does not reverse $\Psi^{\rm end}\le\Phi_\infty$. Nonemptiness follows from $t_*+\gamma_B<\Phi_\infty\le t_*+\tau$; PH42 also excludes exact optimum. The displayed $(\gamma_B,\xi,H)$ are mathematical certificate objects, whose computation and storage have external costs and are not acquired runtime registers. For the family of Theorem 7.3, Proposition 9.1 gives $\Psi^{\rm end}=e$, so PH42 gives $\gamma_B<e-t_*<\zeta/4$. Hence $\tau-\gamma_B>3\tau/4$, whereas $\epsilon_0=\Delta/8\le\zeta/64\le\tau/64$. Its fixed fine accuracy lies strictly outside this coarse window. No contradiction exists between (8.2) and the obstruction. $\square$

## 9. Original observer, extracted cycle and unrecovered chronology

**Proposition 9.1 (small amplitude retains original dependence).** For the constructed observer, the PH21/39 extracted endpoint rows after the fourth-segment return limit report only the baseline $Q,V$, and have $\Psi^{\rm end}=e$, independent of $\mathcal A$. The original full-history objective is $e+\Delta V_{\mathcal A}$. Thus low-risk domination or endpoint extraction does not recover the original transient reports, their acquired localization costs or the acquired-word dependence, however small the fixed positive $\Delta$.

**Proof.** The first fourth Read clears the private label and gate on both branches; a fourth return pair therefore leaves only baseline decoder state, regardless of the training row. Every subsequent return also reports baseline. The PH21/39 return-power limit is supported on that cleared original record fiber; its $p,\beta$ decoders are $Q,V$ at every residue. PH15 gives endpoint scores $e,f$, whose maximum is $e$. Before clearing, Theorem 6.1 gives the full-history score $e+\Delta V_{\mathcal A}$. Always-reject and always-accept automata give the two values $e$ and $e+\Delta$ while their extracted reports agree. PH21's theorem is risk domination by a replacement; it promises neither original per-history report equality nor original-cost-preserving compilation. PH24's recovery theorem is restricted to positive single-mode generators. This finite private-word transient is not put in that smaller category by its risk magnitude. $\square$

**Proposition 9.2 (actual chronology and target remain separate).** Fix an encoded word $w$. The observer's complete ready boundary distribution and decoder along $h(w,n)$ are independent of $n$, although paid lengths are $2d(|w|+1)+2n+6$ and true posteriors vary with $n$. The source provider's opaque depth latch is not an acquired observer field. Thus no function of that retained boundary distribution or decoder recovers the erased padding count, actual posterior or paid age. Ordered word dependence can also survive when true posteriors agree.

**Proof.** Padding leaves the sampled label unchanged; the suffix resets its finite matcher to the same gate and yields the same original $c_*$ with the third write completed. No field records $n$. Equation (6.3) has strictly positive unequal endpoint odds at each finite $n$, which change with $n$ because $r_2\ne r_1$. The actual posterior is therefore not determined by this identical boundary distribution. With independent coupling of the private samples along these analysis histories, the same individual ready labels can occur for all $n$ with the same positive probabilities; an individual-state inverse cannot repair the missing count either.

For a concrete order example, let a two-state automaton start in state 0 and accept state 1. On input 0 use $T_0=((1/2,1/2),(0,1))$ and on 1 use $T_1=((1,0),(1/2,1/2))$. Then $p(01)=1/4$ and $p(10)=1/2$. Fixed-width encoding permutes the same blocks, so $h(01,n)$ and $h(10,n)$ have identical acquired counts, original seed/record and true posterior. Their marginalized first-letter perturbations, hence declared full laws, differ by $\lambda/4$ in TV. The monitor retains a paid relation to order while the original record/posterior erases it. This does not reconstruct the past from one sampled future or supply an archive. A further actually acquired, charged sufficient relation would need its own factorization and inverse theorem. $\square$

**Proposition 9.3 (separate total resource accounts).** The history witnesses are positive finite possibilities, not forced inputs or a waiting-time bound. Source installation, paid acquisition, private microstep work, COMPLETE peak memory, report output and receiver archive remain separate charges.

**Proof.** Conditional on any supported $K$, the probability of a designated source word is $r_K^{A(h)}(1-r_K)^{B(h)}>0$, and its prior average is positive. Every letter probability is at least $1/3$, so a source word of length $L$ has probability at least $3^{-L}$. Its complement can have positive probability; one original run may finish and Stop without ever obtaining that exact prefix. With no reset/copy/retrial port, inverse probability is no encounter-time guarantee. PH49.1 gives an infinite encounter-time expectation if failure to reach the exact prefix is assigned infinite time. The monitor's private sampling cannot choose actual letters or change source occurrence.

Each actual Read and rejected pair, original write, hold, completion, Stop and delivery has its original account. The fixed rational source pays its prior description, installing and sampling its unique $K$; these charges are constant across this counterfamily, not zero. Private row/letter rejection sampling has finite expected attempts but unbounded worst-case attempts and fair bits. Its scratch and all retained phases are included in (5.2). PH49's finite-micrograph service estimate applies once that full budget is supplied; no uniform finite worst-case work follows. The full generated tail has positive arbitrarily long finite words, despite geometric completion and finite expected letter count in this particular family. Serial rendering, the output channel's buffers, original Stop/delivery work and the receiver's archive all cost resources. An output archive is not fed back into observer holding. External matrix enumeration, root isolation, certificates, search and the hypothetical horizon consumer have their own paid computation/storage/output; if they participate online their providers must join COMPLETE. The construction proves no joint resource optimum. $\square$

## 10. Mathematical correspondence and remaining inverse questions

**Mathematical reference 10.1 (precise reuse boundaries).**

| Supplier | Mathematical input and domain |
| --- | --- |
| PH1–2; ST1–3 | One common source, acquired filtration, raw stopped carrier, Bayes law, original record/Stop isometry, phase radii and two separate compatibilities. |
| PH14–17 | Rational arc, root isolation, all-tail baseline signs and reachable endpoint training. Lemma 3.2 supplies the new perturbation signs. |
| PH21–24,39 | Low-risk extracted cycles and endpoint rows; positive single-mode recovery has its stated narrower category. Proposition 9.1 concerns the original observer's extra transient. |
| PH25–26,30,37 | Entire original table/dictionary and the complete binary architecture; no runtime probability row or real register. |
| PH42,45,46 | Strict endpoint digital gap and an effective paid endpoint witness, consumed by the exact original upper-minus-lower argument in §8. |
| PH48–50 | Transient versus endpoint domains and the separate acquisition, occurrence, microstep, installation, output and chronology accounts. |
| EF7.2,8.2; EA2.3–2.4 | Relative-prior stability and finite uniform existence at fixed $(B,S,b_{\rm src},\epsilon)$, with the same observer and actual histories. No total computable cap is inferred. |
| EA7.1–7.2,8.1 | Strict primary premise, finite simple all-word value-gap amplifier and complete finite-graph serializer/interpreter. Proposition 5.1 changes only finite graph ingredients and proves the rational services' almost-sure return. |
| [FourthSegmentStoppedLaw](../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.lean) and [its Blueprint](../../../Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.md) | Fixed-$r$ raw fourth-segment legal Read/Stop, first-completion normal form, infinite noncompletion fiber, zero noncompletion mass and explicit stopped-word law, with $\alpha=0,\beta=1$. Common-source Bayes and full records are the PH/ST bridges. |
| Gimbert–Oualhadj, cited in §7 | `literature-attested`: strict-cutpoint undecidability for simple finite automata. The source-specific promised-class transfer is the ordinary argument of §§3–7. |
| This volume §§3–9 | `repo-derived`: nonzero small-risk calibration, actual fixed-source witnesses, promise certificates, finite-cap calculation and original-consumer transfer; no external priority claim. |

The five-mode laws in [finite-start predictive memory](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_START_PREDICTIVE_MEMORY.md), [native-mixture obstruction](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md), [approximate coherence price](RECURSIVE_RELATIONAL_OBSERVATION_APPROXIMATE_COHERENCE_PRICE.md), [mixed-phase defect attainment](RECURSIVE_RELATIONAL_OBSERVATION_MIXED_PHASE_DEFECT_ATTAINMENT.md), and the Auric/Fib geometrical continuations retain their own source and representation conditions. Their semantic coordinates are not PH37 runtime inputs. In particular [foundational formulas and relations](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) starts from free ordered trees, legal five-mode windows and native readers; its affine law inverses require the specified extra joint coordinates. [Full-positive-window logarithmic prices](KBONACCI_FULL_POSITIVE_WINDOW_LOGARITHMIC_PRICE.md), beginning at Definition 73.1, fixes integer KBonacci block control, an actually acquired chronological window and immutable INITIAL labels. Its continuation prices require their specified seams and endpoints. Neither source is the common-depth PH paid-letter process, and neither supplies an acquired count/posterior oracle or a low-risk all-history localization theorem for this fixed source.

**Corollary 10.2 (relative-prior stability of the same consumer).** Keep one compiled observer's actual kernels, initialization and full decoder fixed. If two positive priors on the same finite support satisfy $1-\eta\le\widetilde\mu(k)/\mu(k)\le1+\eta$ for every $k$, where $0<\eta<1$, then every original fixed-history law/conf error, every capped phase risk and its uncapped counterpart differ by at most $2\eta/(1-\eta)$. The same bound holds for each joint objective.

**Proof by exact application.** Apply EF7.2, or equivalently EA2.4, to this unchanged observer. The likelihood is exactly $r_k^{A(h)}(1-r_k)^{B(h)}$ with all paid Reads counted; the original deterministic records add no likelihood factor. Thus the actual history domain and private row $\eta_{\mathcal A}P_h$ are common to both prior installations, while the full target is their respective normalized common-source mixture pushed through the same $I_c$. Both risk orders, phase radii and maxima are those of Definition 2.2. No retraining, runtime prior input or posterior acquisition is supplied by this analytical comparison. $\square$

**Open question 10.3 (acquired boundary and inverse scope).** The exact declared law, its actual acquisition, certified finite precision, stability under supplied prior information, finite complete digital holding and loss of the actual full target are different recovery problems. In this family the declared gate law semantically determines its first-letter probability $u+\lambda\theta$; because $\lambda>0$, exact law access determines $\theta$. This semantic inverse does not recover the actual hidden $K$, posterior, erased padding or a word archive, by Proposition 9.2. It also grants no zero-error measurement of a law probability from finitely many generated samples.

Theorem 7.3 rules out one effective acquired-history upper certificate across the stated promised class, while §8 retains a coarser original-risk certificate and fixed-tuple existence. A stricter subclass excluding the finite private-word monitors needs its own theorem. Recovering chronology or an actual posterior from a further acquired, charged boundary relation requires an explicit source-faithful factorization and inverse; no such relation is supplied here. Global minimality of a relation structure, physical spacetime recovery and joint total-resource optimality remain outside these local results. The persistent mutual-recovery objective is unresolved.

## 追加锚（本行以下为增补区）
