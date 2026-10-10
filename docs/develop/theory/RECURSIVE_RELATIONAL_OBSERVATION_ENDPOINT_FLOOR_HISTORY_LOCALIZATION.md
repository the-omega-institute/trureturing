# Endpoint mass floors do not localize arbitrary acquired-history risk

## 1. The full-history localization question

This volume keeps PH20.1's numerical objective: approximate a supremum over all positive finite acquired histories while measuring each history's error on the entire unbounded future stopped transcript. PH37–44 supplies the complete digital category and its endpoint-row certificate; PH45–46 supplies paid acquisition for a certified endpoint margin. PH47's counterexamples let endpoint absolute masses shrink, and PH48 separates transient full-history margins from endpoint margins. The remaining question addressed here is whether a fixed positive floor on both endpoint masses localizes an arbitrary specified full-history gap.

One fixed complete digital observer and priors on three actual depths answer that question negatively, for each of the four original law/conf objectives. Additional quantitative information about the same installed prior repairs the original numerical gap for this observer and family. A floor on every mass of a fixed finite depth menu gives uniform finite existence for the whole bounded digital category; effective computation of that general horizon remains a separate question.

References PH, ST, ACP, MP, FSP and NM denote the mathematical suppliers in §10 at revision `46fa8e9917031263e7911c34d39ddbfb5516cbc5`. All results here are ordinary mathematical proofs relative to those contracts, not new Lean certification. The reference volume is append-only after publication; subsequent mathematical additions belong after its final append anchor.

## 2. The unchanged source and all four consumers

**Definition 2.1 (installed common source).** Retain PH1.2–1.5 in full. Before the first actual Read, draw a single $K$ from the installed finite or countable prior $\mu$. Every paid rejection, accepted seed pair and all four payload segments use this same $K$. Given $K=k$, actual Read letters are fresh conditionally independent, with

$$
r_k=F_{k+1}/F_{k+3},\qquad r_1=1/3,\quad r_2=2/5,\quad r_3=3/8,
\qquad 1/3\le r_k\le2/5.
$$

The seed parser accepts $\alpha\beta$ as seed 0 and $\beta\alpha$ as seed 1, rejecting equal pairs with their original paid Reads. In payload phase $p_i$, $\alpha$ completes marker 0 and $\beta$ enters $q_{\beta,i}$; there, $\alpha$ returns to $p_i$ and $\beta$ completes marker 1. After marker 3, the original record write finishes before latch. The held record persists through segment 4, its completion, the sole original Stop and delivery. Pending and delivered permit no Read.

The full finite original configuration $C_0$ includes both seeds, bare fields, selector, tree records $B,Q^+,Z$, writes, latch, permissions, parser, completion and delivery. Its original table is denoted $\delta_0$. The domains $\mathcal H_p,\mathcal H_\beta$ are all positive finite actual histories after the third latch in the respective fourth-segment phases. They retain all seeds, records, finite rejections and returns. They are not replaced by the latch-only domain $\mathcal H_3$, or conditioned on a future event.

For $a_r=r(1-r)$ the complete raw stopped words and laws are

$$
\begin{aligned}
u_{j,0}&=(\beta\alpha)^j\alpha,&u_{j,1}&=(\beta\alpha)^j\beta\beta,\\
P_{p,r}(u_{j,0})&=r a_r^j,&P_{p,r}(u_{j,1})&=(1-r)^2a_r^j,\\
P_{\beta,r}(\beta)&=1-r,&P_{\beta,r}(\alpha u_{j,0})&=r^2a_r^j,\\
&&P_{\beta,r}(\alpha u_{j,1})&=r(1-r)^2a_r^j\quad(j\ge0).
\end{aligned}
\tag{2.1}
$$

The raw carrier also contains the legal infinite noncompletion outcome; it has zero actual mass. The already acquired suspended $\beta$ is absent from the future word. PH2.1 and ST2.1 give the original transcript map $I_c$: start with this history's own $c=C_0(h)$, retain every future Read letter and produce its original ordered control, held-record, completion, Stop and delivery events. Reading back the letters is its inverse on the image. On the fourth-segment countable carrier it preserves TV. The formal source `FourthSegmentStoppedLaw` supplies the actual first-completion language and fixed-parameter raw law; conditional freshness, Bayes conditioning and full-record correspondence remain the separate PH/ST bridges.

With $A(h),B(h)$ counting every actually acquired letter, including rejected pairs, the actual conditional law is

$$
T_h^\mu=(I_{C_0(h)})_*\sum_k\nu_h^\mu(k)P_{s,r_k},\qquad
\nu_h^\mu(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
{\sum_i\mu(i)r_i^{A(h)}(1-r_i)^{B(h)}}.
\tag{2.2}
$$

The denominator is positive. Counts and posterior are proof coordinates; neither is an observer input.

**Definition 2.2 (original numerical objectives).** For a source-independent finite observer with actual configuration row $\rho_h$ and complete decoders $D_z$, retain

$$
e_{\rm law}(h)=\operatorname{TV}\!\left(\sum_z\rho_h(z)D_z,T_h^\mu\right),\qquad
e_{\rm conf}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu).
$$

Let $\ell(h)$ count original paid actual Reads. With the convention that an empty error supremum is zero, define

$$
\begin{aligned}
R_{s,H}^{j}(M,\mu)&=\sup_{h\in\mathcal H_s,\ \ell(h)\le H}e_j(h),\\
\Phi_H^{j_p,j_\beta}(M,\mu)&=
\max\{R_{p,H}^{j_p}-\rho_p,R_{\beta,H}^{j_\beta}-\rho_\beta\},\\
\rho_p&=1116529/22781250,\qquad \rho_\beta=239/6750.
\end{aligned}
\tag{2.3}
$$

Here $(j_p,j_\beta)$ runs separately over $(\mathrm{law},\mathrm{law})$, $(\mathrm{law},\mathrm{conf})$, $(\mathrm{conf},\mathrm{law})$, $(\mathrm{conf},\mathrm{conf})$. The symbol $\Phi_\infty$ means PH20.1's original unrestricted finite-history objective. Both $\Phi_H$ and $\Phi_\infty$ use the full future law; $H$ restricts acquired history, not future-tail length. Pending and delivered have exact deterministic residuals and add zero error.

For every fixed observer/prior and positive $\epsilon$, $\Phi_H\uparrow\Phi_\infty$, and some finite individual $H$ has gap at most $\epsilon$. Indeed every finite actual history belongs to some cap, so each uncapped risk is the increasing limit of the capped suprema; maximum of the two limits commutes with this increasing limit. This is an existence statement, not an algorithm or a family-uniform modulus.

## 3. One explicitly charged complete digital observer

**Definition 3.1 (one realization in the published COMPLETE category).** The ambient class is exactly PH37.1–37.2's $\mathfrak D_\mu(B)$: the fixed finite-alphabet sequential bit architecture, source-independent fair-bit microsteps, almost-sure return at every allowed service entry, the original ready query cuts, and both exact compatibilities. For this particular realization, fix once a finite Boolean bit instruction set with conditional and unconditional fixed-label jumps, fresh source-independent fair bits, original Read/Stop requests, serial output and return. Encode each instruction with a four-bit opcode and two operands encoded by Elias gamma of the operand plus one. Fix its finite bit interpreter and include its code. Code, constants, metadata, field layouts and all length/boundary descriptors, original transition/menu table and rendering dictionary are resident binary data. Each macroinstruction expands into deterministic bit microsteps and single fresh fair-bit steps; each microstep transition has probability $0,1/2$ or $1$. Charge maximum simultaneously allocated RAM, including program counter, operands, addresses, all original fields, persistent phases, private microstates, working and output cursors, sampler scratch and any handshake buffer actually used. The source ports are exactly the original ones. Internal computation is serial and does not call the source while consuming a report.

Use PH25.1's lossless numbering of $C_0$, original table/dictionary format and constants $N_0,s_0,T_0,A_0,h_0,d_0^{\rm enc},\sigma_0$. A fixed program realizing the algorithm in Definition 3.2 is obtained by literal table lookup, bounded-field copying, comparison, output and fixed-label loops in this instruction set. All lookup and rendering work is executed, rather than delegated to an oracle. Choose one such finite compilation once; denote its fully serialized program/interpreter length by $P_M$. Allocate two $s_0$-bit original-configuration fields and two five-bit matcher fields. Install a padded $32\times3\times5=480$-bit matcher successor table. Allocate a three-bit sampling candidate and two-bit position; sampler fields are cleared at commits. Allocate separate finite cursors covering every program/ROM address, dictionary symbol, event within an update, output bit, decoded operand, selected action and mode, with widths equal to the ceiling log of their finite ranges, at least one bit. Their sum, including all bit latches and temporary bounded copy/lookup fields used by the chosen compiler, is $f_M$. No call stack or unbounded index is used: loops jump to fixed labels and rendering resets its finite cursor after each event. A serial installer writes these fixed resident bits using the same bounded address/copy fields; its input buffer, installation mode and cursor are included in $f_M$. Offline compilation is not an online computation provider. If a compiler or a host instead participates in online installation or generation, its resident code and peak workspace must also be charged, increasing this fixed constant.

Thus one sufficient fixed budget is the specific integer

$$
B_0=T_0+P_M+480+2s_0+10+3+2+f_M.
\tag{3.1}
$$

Equivalently, (3.1) is the complete code/data length plus the sum of the compiler's allocated field widths, not the number of nonzero bits. This specifies a finite encoding and a particular finite compilation of a fully stated finite algorithm. The existential choice of its fixed code contributes to $B_0$; no unmeasured numerical executable size or minimum is asserted. Nothing in this definition depends on $\mu$, $H$ or a posterior. A larger at-most-$B$ budget includes it. Changing encoding or adding a host buffer changes the charged constant.

The ambient PH37 category permits retained random phases, reducibility, transients, zero effective transitions and legal infinite noncompletion outcomes. It does not require a literal dyadic probability table, a cyclic kernel, native-mixture reports, or clearing all private phases on service return. Our particular machine uses deterministic actual holding, clears scratch, and completes its synthetic tail almost surely; these are its properties, not restrictions on competitors. PH37.2 charges every output-computation provider and installation peak, so complete bounded binary descriptions are finite in number for each $B$. This is a nonlinear normalized sequential generative representation, not a linear response space or an inference from real-coordinate count to bits.

**Definition 3.2 (matcher and generator).** Write

$$
W=\alpha^6\beta^{10}=(\alpha\alpha)^3(\beta\beta)^5,
\qquad S=\beta\alpha\mid\beta\beta\alpha\alpha,
\qquad h_n=W^nS\quad(n\ge0).
\tag{3.2}
$$

The vertical bar is punctuation, not an operation. Use matcher states $q_0,\ldots,q_{15},t_1,\ldots,t_6,\mathrm{dead}$, initially $q_0$. From $q_0$, $\alpha$ goes to $q_1$ and $\beta$ to $t_1$. For $1\le i\le5$, $\alpha$ takes $q_i$ to $q_{i+1}$; for $6\le i\le14$, $\beta$ takes $q_i$ to $q_{i+1}$; $\beta$ takes $q_{15}$ to $q_0$. The suffix transitions are

$$
t_1\xrightarrow\alpha t_2\xrightarrow\beta t_3\xrightarrow\beta t_4
\xrightarrow\alpha t_5\xrightarrow\alpha t_6.
$$

Every unspecified letter transition goes to dead; dead is absorbing; either letter from $t_6$ goes to dead. Stop also sends the matcher to dead. Unused padded table rows are dead. In every actual operation, execute the original $\delta_0$ and its ordered event block, then the matcher update. The matcher changes no original field, record, permission or source behavior.

At every active synthetic configuration, choose $\alpha$ with probability $1/3$, except at $p_4$ with matcher $t_6$, where choose it with probability $5/8$. Use the same combined deterministic letter update as actual holding. Pending emits only the unique original Stop and delivery, then delivered has empty residual. Define $D_z$ as this generator's complete legal transcript law. A finite descriptor is its charged program and current configuration; no infinite probability table is stored.

Sample $1/3$ with two fresh fair bits: reject candidate 3, emit $\alpha$ for 0 and $\beta$ for 1 or 2. Sample $5/8$ with three fresh fair bits and emit $\alpha$ for candidates below 5. Clear scratch before letter commit and normalize synthetic fields, cursors and PC before returning. The actual configuration remains held during report consumption. Only the already acquired finite configuration is copied into the separately charged synthetic cursor; the source and its $K$ are not copied.

**Lemma 3.3 (source correspondence and exact compatibilities).** This observer is in the published $\mathfrak D_\mu(B_0)$ of PH37.1–37.2 on every PH prior with positive endpoints, from initialization to delivery. All original finite histories and records remain in the actual domain. At query cuts actual retention is deterministic, and both exact compatibilities hold separately.

**Proof.** $W$ comprises eight legal rejected equal pairs. $S$ accepts seed 1, then completes markers 100 without returns. Its last $\alpha$ completes the third original write and only then latches. Thus every $h_n$ is a positive actual history, with the same original held $c_*$, in $\mathcal H_3\subset\mathcal H_p$, and

$$
A(h_n)=6n+3,\quad B(h_n)=10n+3,\quad \ell(h_n)=16n+6.
\tag{3.3}
$$

The matcher recognizes $W^*S$ exactly: every cycle from $q_0$ consumes one complete $W$; the alternative starts the six-letter suffix, whose terminal has no nondead outgoing letters. All proper nondead prefixes occur before the original third latch. Therefore at any reachable fourth-segment query the matcher is $t_6$ exactly on $h_n$, and is dead on every other history. The first fourth-segment Read after $h_n$ consumes this special phase permanently. Both seeds, all other original tree records and all rejected and return words still execute unchanged $\delta_0$. No history is screened out by the matcher.

Sampling $1/3$ succeeds per trial with probability $3/4$, so it returns almost surely with finite expected work and fixed workspace; $5/8$ uses three bits. After its one exceptional step, every synthetic path uses the ordinary $1/3$ generator. Ordinary seed acceptance per pair is $4/9$ and payload return factor is $2/9$. Consequently the complete synthetic process terminates almost surely from every reachable original cut. The noncompletion carrier is retained with zero synthetic mass, rather than discarded by conditional normalization.

Let $\Delta$ be the combined deterministic update and $E(c,x)$ the complete original event block for operation $x$. Fresh sampling and the program imply, for every residual measurable event $A$,

$$
D_z((x,E(c,x))A)=q_z(x)D_{\Delta(z,x)}(A).
\tag{3.4}
$$

Legal Stop has probability one. Finite cylinders determine the complete law; almost-sure termination and the retained zero noncompletion mass give the same equality on the full stopped carrier. This first proves per-configuration same-update generation. For the other obligation, $\rho_h$ is the point mass at the actual canonical configuration $z(h)$, and $z(hx)=\Delta(z(h),x)$. All active synthetic letter probabilities are strictly positive. Divide (3.4) by $q_z(x)$ and delete the operation and its event block: $\operatorname{res}_x\overline D_h=\overline D_{hx}$. Iterate for every finite legal continuation. Delivered has no next operation. This independently proves actual-history marginalized update compatibility, without using the actual posterior as a runtime state.

All original writes and events precede the extra matcher update; third write precedes latch, and the same history's record is held through fourth completion and delivery. At each query comparison use its own $I_{C_0(h)}$, never records assembled from different histories. No actual random tag survives synthesis, no clock or history archive is added, no reset, resampling, test or post-Stop Read is available. Every internal microstate and finite output provider is charged by (3.1), even though internal execution is not a new original query cut. The effective actual kernels are $0/1$, the effective synthetic probabilities rational, and initialization source independent. Initialization and actual updates are finite deterministic services; the sampler services return almost surely at every allowed entry, including generated-only entries. The fixed-width encoding contains the installer, complete original controls, both cursors, matcher and all microstates. Its joint effective generation is $q_z(x)P_x(z,z')$ with $P_x$ the deterministic combined update. These facts verify every PH37.1–37.2 restriction, in addition to PH1.4, both PH1.5 contracts and PH21.1. The low-risk hypotheses of PH21.2, when used, are supplied separately by (5.3), not inferred from membership. $\square$

## 4. Full unbounded-tail risk on every history

**Lemma 4.1 (exact special law).** At $h_n$ the raw report $Q$ has

$$
\begin{aligned}
Q(u_{0,0})&=5/8,&Q(u_{0,1})&=1/4,\\
Q(u_{j+1,0})&=(1/24)(2/9)^j,&Q(u_{j+1,1})&=(1/18)(2/9)^j\quad(j\ge0).
\end{aligned}
\tag{4.1}
$$

For every finite/countable posterior on PH parameters, writing $m=\sum_k\nu(k)r_k$,

$$
\operatorname{TV}\!\left(Q,\sum_k\nu(k)P_{p,r_k}\right)=5/8-m.
\tag{4.2}
$$

**Proof.** The exceptional first $\alpha$ completes immediately. After first $\beta$ (probability $3/8$), synthesis uses iid $r_1$: the immediate second $\beta$ gives $(3/8)(2/3)=1/4$; first $\alpha$ returns to ordinary p with factor $(3/8)(1/3)=1/8$, giving the two later families in (4.1). Their geometric sum plus the two immediate terms is one.

For $r\in[1/3,2/5]$, $a_r\ge2/9$. The true immediate $\beta\beta$ mass is at least $9/25>1/4$. For every $j\ge0$,

$$
r a_r^{j+1}\ge(2/27)(2/9)^j>(1/24)(2/9)^j,
$$
$$
(1-r)^2a_r^{j+1}\ge(2/25)(2/9)^j>(1/18)(2/9)^j.
$$

Conversely $Q(\alpha)=5/8>r$. Thus the only positive coordinate of $Q-P_{p,r}$ is $\alpha$, for every $j$, not merely a finite set of words. These signs survive any actual posterior mixture. Both laws give zero to noncompletion. For normalized laws, the sum of the positive coordinate differences is TV, proving (4.2). The same $I_c$ preserves this equality on the complete record/control/Stop transcript. It is a full-tail TV formula whose maximizing event happens to be one letter, not a substitution of a one-step loss for the original consumer. $\square$

**Lemma 4.2 (ordinary queries).** At every other reachable fourth-segment query the report is $(I_c)_*P_{s,r_1}$. For every installed PH prior and every such actual history,

$$
e_{\rm law}(h)=e_{\rm conf}(h)\le
\begin{cases}1/7,&s=p,\\4/35,&s=\beta.\end{cases}
\tag{4.3}
$$

**Proof.** The matcher is dead and cannot revive. Reuse ACP4's full-stopped-word first-disagreement coupling, with the reference process at $r_1$. The expected future Read counts solve $L_p=1+(1-r_1)(1+r_1L_p)$, $L_\beta=1+r_1L_p$, giving $15/7$ and $12/7$. Before a first disagreement the reference process has the same parser and events as the comparison. A per-letter mismatch is at most $|r-r_1|\le1/15$. Summing active-step mismatch probabilities bounds full-transcript TV by $1/7$ and $4/35$. Convexity gives the same bounds for the actual posterior mixture. This is a mathematical coupling of laws, not a source copy or an experiment. Deterministic actual holding makes law and conf identical at each query. Pending and delivered residuals are exact. $\square$

## 5. Fixed positive endpoint floor and no uniform horizon

**Theorem 5.1 (one observer, all four quantified failures).** Fix the observer $M$ and $B_0$ above. Set $a=1/4$, $\epsilon_0=1/1000$. For every integer $N\ge7$, install the rational prior

$$
\mu_{\delta_N}=(1/4,3/4-\delta_N,\delta_N)\text{ on }\{1,2,3\},
\qquad \delta_N=(1/8)(8/9)^N.
\tag{5.1}
$$

Both endpoint masses are at least $a$. For each of the four original objective pairs separately,

$$
\Phi_\infty^{j_p,j_\beta}(M,\mu_{\delta_N})-
\Phi_N^{j_p,j_\beta}(M,\mu_{\delta_N})
\ge\frac{39973}{13197840}>\epsilon_0.
\tag{5.2}
$$

In fact, throughout $0<\delta\le1/4$,

$$
\Phi_\infty(M,\mu_\delta)=L:=1/4-\rho_p
=9157567/45562500,
\qquad R_p=1/4<1/3,\quad R_\beta\le4/35<1/3.
\tag{5.3}
$$

**Proof.** Put $b_i=[r_i(1-r_i)]^3$ and $f_i=r_i^6(1-r_i)^{10}$. Actual likelihood at $h_n$ is $b_if_i^n$. No parser or record factor is added to (2.2). The endpoint-conditional depth-2/depth-1 odds are at least

$$
2(b_2/b_1)(f_2/f_1)^n,
\quad b_2/b_1=19683/15625,
\quad f_2/f_1=2541865828329/2441406250000>1.
$$

Hence the endpoint-conditional mean $m_E(n)$ obeys

$$
m_E(n)\ge m_{\min}:=\frac{r_1b_1+2r_2b_2}{b_1+2b_2}
=314321/824865=3/8+g,
\quad g=39973/6598920>0.
\tag{5.4}
$$

The log derivative of $f(r)=r^6(1-r)^{10}$ is $(6-16r)/(r(1-r))$. Its unique maximum on this interval is at $r_3=3/8$, and $f_3>f_2>f_1$. For every fixed positive $\delta$,

$$
\frac{1-\nu_{h_n}(3)}{\nu_{h_n}(3)}
=\sum_{i=1,2}\frac{\mu_\delta(i)b_i}{\delta b_3}(f_i/f_3)^n\longrightarrow0.
\tag{5.5}
$$

This conditions the one installed common source on actual positive finite words. It does not assign posterior mixtures arbitrarily. Their source probabilities are $\sum_i\mu_\delta(i)b_if_i^n>0$. By (5.4), $m(h_n)=(1-\nu_{h_n}(3))m_E(n)+\nu_{h_n}(3)(3/8)\ge3/8$, and it tends to $3/8$. Lemma 4.1 therefore gives special-history errors bounded by $1/4$ and converging to $1/4$. All ordinary p errors are at most $1/7$, so $R_p=1/4$; all beta errors are at most $4/35$. The rational inequality $4/35-\rho_\beta<1/4-\rho_p$ proves (5.3). No finite $h_n$ attains the displayed p supremum: its endpoint masses remain positive, so its mean is strictly greater than $3/8$.

For any actual word of $t$ Reads, use the depth-1 term alone in the Bayes denominator:

$$
\nu_h(3)\le4\delta(9/8)^{A(h)}(15/16)^{B(h)}
\le4\delta(9/8)^t.
\tag{5.6}
$$

With $\delta=\delta_N$ and $t\le N$, this is at most $1/2$. At any special history under that cap, (5.4) implies $m(h_n)\ge3/8+g/2$ and its full error is at most $1/4-g/2$. At every other capped history use Lemma 4.2, including all seeds and records. The exact comparisons

$$
1/7<1/4-g/2,\qquad
4/35-\rho_\beta<1/4-g/2-\rho_p
$$

give $\Phi_N\le L-g/2$. This is an upper bound on every actual history below the cap, with full future loss. Subtract from (5.3) to obtain (5.2). Since $\rho_h$ is always a point mass, each use of law and conf agrees pointwise; the argument proves law/law, law/conf, conf/law and conf/conf for this same observer and prior, rather than importing one order's result into another random model. $\square$

**Corollary 5.2 (failure of finite uniform existence).** No finite-valued horizon depending only on $(B,a,\epsilon)$ can guarantee $\Phi_\infty-\Phi_H\le\epsilon$ over the original priors and complete digital observers. In particular no total computable such function exists.

**Proof.** Evaluate any proposed horizon at $(B_0,1/4,1/1000)$, call the result $H$, and take $N=\max\{H,7\}$. The one fixed observer is allowed, its prior (5.1) obeys the positive endpoint floor, and monotonicity gives $\Phi_H\le\Phi_N<L-\epsilon_0$. The same contradiction applies for any larger at-most budget. It settles no smaller budget that excludes this machine. For this particular prior family every fixed positive $\delta$ still has finite individual witnesses by (5.5). No generic automata undecidability, absent individual horizons or failure of PH's scoped endpoint transfers is inferred. $\square$

## 6. The same numerical gap and threshold witnesses

**Proposition 6.1 (strict threshold formulation).** Fix a machine, prior, objective pair, cap $H$ and $\epsilon\ge0$. The numerical inequality $\Phi_\infty-\Phi_H\le\epsilon$ is equivalent to the following implication for every real $\tau$, with this same $H$: if $\Phi_\infty>\tau+\epsilon$, then an actual history in one of the two queried phases, with at most $H$ paid Reads, has phase score $e_{j_s}(h)-\rho_s>\tau$. Take $H\ge7$, so both queried domains are nonempty and the empty-supremum convention creates no artificial score. The counterexample uses $H\ge7$ and meets this condition.

**Proof.** Approximation gives $\Phi_H\ge\Phi_\infty-\epsilon>\tau$. The capped domains contain finitely many words, so a phase score above $\tau$ exists. Conversely, if the numerical gap exceeds $\epsilon$, choose $\tau$ strictly between $\Phi_H$ and $\Phi_\infty-\epsilon$. The implication would produce a capped score greater than $\Phi_H$, a contradiction. Strictness matters: a supremum equal to $\tau+\epsilon$ does not supply a score strictly above $\tau+\epsilon$. For any strict inequality $\Phi_\infty>\tau+\epsilon$, the definition of supremum supplies some finite actual history above that threshold, even when the supremum is unattained. This statement never promises a maximizing history. $\square$

**Corollary 6.2 (one fixed threshold also fails uniformly).** Set $\tau=199/1000$, $\epsilon=1/1000$. For every $N\ge7$, the prior (5.1) has $\Phi_\infty>\tau+\epsilon$ but $\Phi_N<\tau$, for all four objective pairs. Thus even a horizon also allowed to depend on this fixed threshold and slack cannot be uniform over the stated family.

**Proof.** The exact rational comparisons are $L>1/5$ and $L-g/2<199/1000$. Theorem 5.1 applies. For each fixed prior the sequence $h_n$ eventually has score above $\tau+\epsilon$ by its strict limiting margin, so actual finite longer histories supply the uncapped inequality. None under the chosen cap does. $\square$

The PH optimum-relative consumer can also be left numerically unchanged. PH17/20 supply $0<t_*<1/10000$. With the fixed requested gap $\gamma=99/500$, this family satisfies

$$
\Phi_\infty>t_*+\gamma+1/1000,\qquad
\Phi_N<\gamma<t_*+\gamma.
\tag{6.1}
$$

These follow from $L>\gamma+1/1000+1/10000$ and $L-g/2<\gamma$. Thus the obstruction is a specified original gap with its original slack, rather than an endpoint certificate of a smaller numerical value. The ordinary counterexample proof does not use PH's optimal-generator construction or its implementation as a supplier.

**Proposition 6.3 (necessary paid length).** In the three-depth family, let $0<\epsilon<g$. Any history with phase score greater than $L-\epsilon$ must be one of the special $h_n$, and must satisfy

$$
4\delta(9/8)^{\ell(h_n)}>1-\epsilon/g.
\tag{6.2}
$$

Consequently, whenever the numerator ratio below exceeds one,

$$
\ell(h_n)>\frac{\log((1-\epsilon/g)/(4\delta))}{\log(9/8)}.
\tag{6.3}
$$

**Proof.** Both ordinary phase-score bounds are smaller than $L-g$. The score is special, and (4.2),(5.4) give $L-(e(h_n)-\rho_p)=m(h_n)-3/8\ge g(1-\nu_{h_n}(3))$. A score greater than $L-\epsilon$ therefore needs $\nu_{h_n}(3)>1-\epsilon/g$. Apply (5.6) and take logarithms. This is necessary length of a possible paid witness, not a probability, waiting time or internal computational duration. $\square$

**Proposition 6.4 (the published endpoint consumer remains valid).** For this same machine, every prior of Theorem 5.1 and every legal PH21/PH39 period choice have

$$
Q_i=P_{p,r_1},\qquad V_i=P_{\beta,r_1},\qquad
A_p^{\rm end}=2\rho_p,\qquad A_\beta^{\rm end}=2\rho_\beta,
\qquad \Psi^{\rm end}(M)=\rho_p.
\tag{6.4}
$$

Thus PH45.2 applies with the already certified endpoint floor $a=1/4$, and PH46.1 transfers every certified endpoint margin $g_{\rm end}$ with $t_*+g_{\rm end}\le\rho_p$ to its specified smaller requested margin. Neither that transfer nor PH46.2's budget margin supplies the full numerical approximation of §5 or the larger full-history threshold in (6.1).

**Proof.** The original PH21 training words are $(\alpha\alpha)^m(\beta\beta)^lS_0$, where $S_0=S$ and both exponents tend to infinity in their prescribed residue classes. Once $m\ge4$, the seventh consecutive $\alpha$ sends the matcher to dead; later letters cannot revive it. The original rejected pairs still return to the same seed-parser cut, and $S_0$ produces exactly the same $c_*$. Hence the PH21 row $\Lambda$ is the point mass on $(c_*,\mathrm{dead})$ with its canonical charged idle fields. Every further fourth-segment return $\beta\alpha$ preserves that matcher and original $c_*$; all PH39 rows $\lambda_i$ coincide. Their raw decoders are precisely the ordinary $r_1$ laws, and the suspended row is their deterministic $\beta$ successor. This establishes the first two identities for any legal period choice without replacing the published endpoint domain by arbitrary posterior inputs. Reuse ST2.2/PH2.2's exact endpoint distances to get the last three identities; $\rho_p>\rho_\beta$.

All PH45 hypotheses hold by Lemma 3.3 and the endpoint certificate, so its endpoint-row approximation theorem and PH46's margin consumers apply unchanged. However $\rho_p<t_*+99/500$, while (6.1) has full-history value above $t_*+99/500+1/1000$. The histories carrying that larger gap retain $t_6$ and concentrate the actual posterior on depth 3. The endpoint-training limit has erased $t_6$ instead. Thus this machine specifies which actual full-history stratum is missed by endpoint rows; it is not a counterexample to their scoped transfer. PH48.1 already proves the general direction cannot be reversed; the new point here is the absence of any uniform horizon for the larger consumer even after both endpoint masses are bounded away from zero. $\square$

## 7. Additional prior information repairs the same consumer

**Theorem 7.1 (effective same-family numerical transfer).** Keep exactly $M$, the original source and $\mu_\delta=(1/4,3/4-\delta,\delta)$ for $0<\delta\le1/4$. Supply a rational certificate $0<b\le\delta$ and a rational accuracy $\epsilon>0$ as data for mathematical witness construction, not as runtime observer inputs. Put

$$
\Gamma=f_2/f_3=\frac{1459166279268040704}{1490116119384765625}<1,
\qquad C=b_2/b_3=2097152/1953125.
\tag{7.1}
$$

Choose by exact rational multiplication the first integer $n\ge1$ such that $C\Gamma^n\le40b\epsilon$, and let $H=16n+6$. This procedure terminates and, simultaneously for all four objective pairs and every member of this family with $\delta\ge b$,

$$
0\le\Phi_\infty(M,\mu_\delta)-\Phi_H(M,\mu_\delta)\le\epsilon.
\tag{7.2}
$$

**Proof.** $b_1<b_2$, $f_1<f_2<f_3$ and $\mu_\delta(1)+\mu_\delta(2)\le1$. Equation (5.5) bounds the actual endpoint posterior odds by $(C/b)\Gamma^n$, so $1-\nu_{h_n}(3)\le(C/b)\Gamma^n$. The endpoint mean lies in $[3/8,r_2]$, whence

$$
0\le m(h_n)-3/8\le(r_2-3/8)(1-\nu_{h_n}(3))
\le C\Gamma^n/(40b)\le\epsilon.
$$

The special score is exactly $L-(m(h_n)-3/8)$. It is a member of the original capped domain at $16n+6$ Reads. Equation (5.3), rather than merely a lower bound for a different limiting row, now proves (7.2). Since $0<\Gamma<1$, exact rational iteration terminates for every positive rational $b,\epsilon$. Its rational arithmetic storage, iteration counter, output length and computation time must be charged to the external witness-construction procedure. The observer retains none of these values. $\square$

An endpoint floor does not supply this $b$. The floor, fixed support cardinality, maximum depth and bounded depth moments or entropy all hold in this three-depth family while the interior mass tends to zero. Any prior-data repair admitting the family must quantitatively exclude or resolve that behavior. Theorem 7.1 proves sufficiency for this same observer and family; a floor at depth 3 is not asserted sufficient for every observer or every countable prior. More generally the relevant data would be a mass/likelihood-domination certificate for the components selected by the observer's reachable history strata.

**Theorem 7.2 (relative-prior consumer stability, including countable support).** Fix one source-independent observer and two finite/countable PH priors $\mu,\widetilde\mu$. Suppose, for every depth,

$$
(1-\zeta)\mu(k)\le\widetilde\mu(k)\le(1+\zeta)\mu(k),
\qquad 0\le\zeta<1.
\tag{7.3}
$$

Let $\kappa=\zeta/(1-\zeta)$. At every actual finite history, the full true laws differ by at most $\kappa$ in TV. Both error orders, each capped and uncapped phase risk, and each capped and uncapped $\Phi$ differ by at most $\kappa$. A witness transfers on the identical actual word with score allowance $\kappa$. A bound $\Phi_\infty^\mu-\Phi_H^\mu\le\epsilon$ transfers as

$$
\Phi_\infty^{\widetilde\mu}-\Phi_H^{\widetilde\mu}\le\epsilon+2\kappa.
\tag{7.4}
$$

**Proof.** The supports coincide, including common zero masses. On support write $a(k)=\widetilde\mu(k)/\mu(k)\in[1-\zeta,1+\zeta]$. Multiply the same actual likelihoods, then normalize (2.2), to obtain $\widetilde\nu_h(k)=\nu_h(k)a(k)/\bar a_h$, where $\bar a_h=\sum_k\nu_h(k)a(k)\ge1-\zeta$. Hence

$$
\operatorname{TV}(\nu_h,\widetilde\nu_h)
=\frac{\sum_k\nu_h(k)|a(k)-\bar a_h|}{2\bar a_h}
\le\frac{\zeta}{1-\zeta}.
$$

All countable sums are absolutely convergent: the integrands are bounded and $\nu_h$ is a probability. Mixing the same complete depth laws and pushing through the same $I_c$ contracts TV. The source-independent initialization and actual update matrices make $\rho_h$ identical for the two priors on the same actual word. Thus the triangle inequality bounds the change of law error by the true-law TV; for conf apply it per decoder and average with the same $\rho_h$. Supremum and the maximum in (2.3) preserve the bound. All finite legal words are positive under both priors, so the actual domains coincide. Applying the bound at both $\infty$ and $H$ yields (7.4). Exact compatibility, when required, remains the same because reports, rows, legal histories and predicted prefixes are unchanged. $\square$

This relative certificate is stronger than small additive prior TV. The family $\mu_\delta\to\mu_0$ in prior TV but admits no such certificate at the atom whose mass disappears. PH47.3 supplies the corresponding acquisition boundary: finite original Reads cannot zero-error certify an unknown prior mass floor. A certified installation description may supply a floor through separately charged computation. Neither this certificate nor a proof posterior is an observer input or a free runtime oracle.

## 8. Compactness, continuity and the precise existence boundary

**Theorem 8.1 (finite-horizon continuity, full-risk discontinuity).** Adjoin the valid endpoint prior $\mu_0=(1/4,3/4,0)$ to the line $0\le\delta\le1/4$. This is compact even in prior TV. Every fixed $\Phi_H(M,\mu_\delta)$ is continuous on it. Nevertheless,

$$
\Phi_\infty(M,\mu_0)=5/8-m_0-\rho_p,
\qquad m_0=432419/1120110,
\tag{8.1}
$$

whereas every $\delta>0$ has $\Phi_\infty=L$. The upward limit jump at zero is

$$
L-\Phi_\infty(M,\mu_0)=m_0-3/8=49511/4480440>0.
\tag{8.2}
$$

**Proof.** There are finitely many legal acquired words of at most $H$ Reads, and any optional Stop positions are determined by the original parser. Every word's likelihood denominator in (2.2) stays positive at every $\delta$, including zero. Its posterior weights vary continuously, and mixtures of fixed full residual laws vary continuously in TV, since their TV difference is at most the TV of their weights. Each error is therefore continuous; so is the finite maximum defining $\Phi_H$.

At zero the endpoint odds on $h_n$ are $3(b_2/b_1)(f_2/f_1)^n$, strictly increasing in $n$. The posterior mean is minimized at $n=0$, with value $m_0$ in (8.1). The maximum special error is $5/8-m_0$ and is attained at $h_0$. The ordinary p bound and beta phase-score bound are strictly smaller than its corresponding p score. Thus (8.1) is exact. Theorem 5.1 supplies the exact value for every positive $\delta$, and rational subtraction gives (8.2).

A uniform limit of the continuous $\Phi_H$ would be continuous: choose one $H$ making both function-value approximation errors less than one third of the requested continuity tolerance and use continuity of that $\Phi_H$ for the remaining third. The nonzero jump contradicts such a limit. Hence compact prior space and finitely many bounded programs alone cannot force a uniform acquisition modulus. The missing hypothesis in that compactness argument is continuity/equicontinuity of the full-history supremum; a supremum of continuous functions is only lower semicontinuous in general. The exhibited direction of the jump agrees with that fact. $\square$

**Theorem 8.2 (fixed finite menu and a floor on every supported mass give uniform existence).** Fix the entire published PH37.1–37.2 category $\mathfrak D_\mu(B)$ on its fixed binary architecture, an integer budget $B$, a finite depth menu $S$ containing 1 and 2, and $b>0$. On the compact simplex

$$
\mathcal P_{S,b}=\{\mu:\operatorname{supp}\mu=S,\ \mu(k)\ge b\ (k\in S),\ \sum_{k\in S}\mu(k)=1\},
$$

for every $\epsilon>0$ there is some finite uniform acquired-history cap $H$ such that $\Phi_\infty-\Phi_H\le\epsilon$ for every admissible at-most-$B$ observer, every prior in this simplex and all four objectives. This assertion is finite existence, not total computability of $H$ from $(B,S,b,\epsilon)$.

**Proof.** If the simplex is empty the claim is vacuous. Otherwise take two priors in it and any positive actual likelihood vector $L_k$. Write $d=\|\mu-\widetilde\mu\|_\infty$ and $Z=\sum_k\mu(k)L_k\ge b\sum_kL_k$. Expanding both normalizations and using $|Z-\widetilde Z|\le\sum_k|\mu(k)-\widetilde\mu(k)|L_k$ gives

$$
\begin{aligned}
2\operatorname{TV}(\nu_h^\mu,\nu_h^{\widetilde\mu})
&\le\frac{\sum_k|\mu(k)-\widetilde\mu(k)|L_k}{Z}
+\frac{|Z-\widetilde Z|}{Z}\\
&\le2d/b.
\end{aligned}
\tag{8.3}
$$

This bound is uniform over every finite acquired word and its length. The same contraction and fixed-row argument as Theorem 7.2 makes both history errors and all capped/uncapped objectives $1/b$-Lipschitz in this norm. That holds for randomized holding as well as this construction. The laws remain the full residual laws.

Take a finite prior net of radius $b\epsilon/4$ in the compact simplex. Fix one bounded program and one of the four objectives. At each net point, Definition 2.2's pointwise increasing convergence supplies a finite cap with gap at most $\epsilon/2$. Take the maximum of these caps over the finite net, the four objective pairs, and the finite set of complete program/data descriptions of budget at most $B$. Monotonicity preserves each net-point inequality. Moving to an arbitrary prior changes the uncapped and capped value by at most $\epsilon/4$ each, proving the claimed $\epsilon$ gap.

The pool may be restricted to admissible descriptions. Their exact compatibilities concern source-independent rows, reports, common legal histories and predicted prefixes, so are prior-independent on this domain. Even if a separately declared class additionally restricts the risk of an input at a particular prior, the proof can cover the larger finite pool of well-defined original-interface programs before applying that extra restriction. It does not assume that such semantic admissibility can be decided. Finiteness uses the charge for code, constants and all output providers: allowing an uncharged prior-specific decoder or real constant would invalidate this step. $\square$

**Open question 8.3 (effective upper certificate remains separate).** The preceding proof supplies neither an algorithm for the net-point suprema nor a certificate that a searched horizon approximates them. An explicit additional condition sufficient for turning this proof into a total procedure is a uniform effective upper certificate: given a bounded admissible description, a net prior and positive precision, produce a rational upper bound on its original full-history $\Phi_\infty$ and a computed capped lower value with certified gap below that precision; alternatively supply a uniformly effective convergence modulus directly. Finite prior nets, computable fixed-history likelihoods and pointwise full-future TV evaluation alone do not certify the supremum over arbitrary acquired histories. The decidability of semantic admissibility may be another implementation obligation if an algorithm filters codes. PH45 gives effective bounds for its certified endpoint domain; Chen–Kiefer, Theorem 7, gives convergence of full future-trace TV approximations for finite labelled chains. Neither result gives the upper certificates for the supremum over all acquired histories required here. Proposition 12 in the latter source also prevents replacing full TV by an assumed rational-risk oracle. Total computability for the stronger finite-menu/all-masses-floor hypothesis remains open in this volume.

## 9. Paid chronology, occurrence and complete resource accounts

**Proposition 9.1 (fixed memory does not recover paid chronology).** All $h_n$ have the same canonical retained boundary $(c_*,t_6)$ and the same report $Q$, with different paid lengths $16n+6$. For each fixed positive $\delta$, their true conditional laws vary with $n$ and tend to the depth-3 law; their special errors are strictly below $1/4$ at every finite $n$ and tend to $1/4$. Thus the observer boundary/report does not recover the erased repetition count, actual posterior or paid chronology. It does determine its own legal future generator with both exact compatibilities.

**Proof.** After every $W$ the matcher returns to $q_0$ and the seed parser to its original empty-pair state; the same $S$ then produces the same seed and record $c_*$. Neither state stores the number of rejected blocks. Equations (5.4)–(5.5) give positive endpoint posterior mass at every finite $n$ and the limiting depth-3 concentration, so these posterior coordinates cannot be recovered from the common state. The lengths differ by 16 and are unbounded, precluding even a bounded absolute-error age estimate from this one state. Definition 3.2 and Lemma 3.3 determine and condition its legal full future generation. Legal completion guarantees and exact update semantics therefore coexist with a missing actual-target and chronology inverse. $\square$

Exact semantic law recovery, actual acquisition, representation precision, complete finite memory and loss of the true target are different statements here. Our finite rational sampler implements its declared law exactly; that law still has the nonzero target risk (5.3). Inverting a law object is a mathematical operation with its own representation cost, not recovery from one sampled future. This boundary is source-specific and does not import FSP's different five-mode source or its memory minima.

**Proposition 9.2 (possible witness length is not waiting time).** Each $h_n$ has positive probability in one original run but need not occur in that run. The original source's expected total number of actual Reads until fourth completion is uniformly bounded by $183/14$ over all PH priors. There is nevertheless no uniform finite worst-case acquisition length, and the high-risk witnesses of Theorem 5.1 have diverging necessary length as $\delta\downarrow0$.

**Proof.** Their positive probability was computed after (5.5). At fixed $r$, a seed trial costs two Reads and succeeds with probability $2a_r$, so the expected seed cost is $1/a_r\le9/2$. Each segment has expected length $(2-r)/(1-a_r)\le15/7$, by the same parser recurrence and ACP4 derivative bound. Sum four segment expectations conditional on the common $K$, then average over the installed prior: at most $9/2+60/7=183/14$. Independence between segment lengths is unnecessary for this sum. The original Stop and delivery account remains separate and unchanged. Arbitrarily many equal rejections have positive probability, so no finite worst-case Read bound exists. Equation (6.3) concerns the length of a possible score witness, while the expectation concerns terminating the ordinary run. No reset or repetition interface permits turning witness probability into a waiting-time guarantee. $\square$

The source installer pays for the rational prior description, its precision, installing it and realizing the single common-$K$ choice. For (5.1), writing numerator and denominator directly uses $O(N)$ bits; a compressed description still pays its program, argument and evaluation work. These costs are outside the fixed prior-independent observer budget, and are not free or assumed bounded. Also bounding source-prior description would change the quantified class. The certificate $b$ and exact-rational witness search of Theorem 7.1 have separate external data/computation accounts.

The observer pays (3.1) for code/interpreter, original table/dictionary and metadata, both actual and synthetic complete control/record fields, matcher phases, all sampler candidates and positions, every PC, operand, address and output/event/rendering cursor, and peak workspace. Source-independent fair bits are an explicit logical supplier: producing them has its own charged random-bit/work account, not a physical-law conclusion. Sampling $1/3$ uses $8/3$ fair bits in expectation and has no finite worst-case bit/time bound; $5/8$ uses three. Synthetic seed/segment output length is unbounded, though expectations are finite. The receiver's storage of a full streamed transcript and any host output buffers are additional costs; no output archive is fed back into holding. There is no complete-state omission obtained by naming only 23 matcher states, no state-count optimum and no total-resource optimum.

## 10. Mathematical suppliers and recovery boundaries

**Mathematical citation 10.1 (source-specific overlap).** The mathematical suppliers below are read at revision `46fa8e9917031263e7911c34d39ddbfb5516cbc5`. Their conclusions retain their own hypotheses. All new conclusions of this volume are `repo-derived` ordinary mathematics; Bayes normalization, TV contraction/coupling and finite-dimensional compactness are intermediate tools, not separate claims of novelty.

| Supplier | Reused contract and scope of the new bridge |
| --- | --- |
| [PH](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md), §§1–2, 20–23, 25–26, 33–34, 37–50 | PH1 gives the one common source, same-history posterior and two distinct exact compatibilities. PH20.1 gives the original four numerical objectives; PH25 gives full original table/dictionary encoding. PH37 gives the entire COMPLETE class; §§38–44 supply its endpoint-row certificate, not an all-history cover. PH45–46 supplies certified endpoint-margin acquisition. PH47 lets endpoint absolute masses shrink, whereas (5.1) fixes their floor at $1/4$ and lets only depth-3 mass vanish. PH48 shows transient loss need not survive endpoint extraction, whereas §5 additionally proves absence of every finite uniform full-gap horizon. Proposition 6.4 and Theorem 7.1 respectively retain the endpoint contract and repair the original numerical consumer in this constructed family. No arithmetic separation, digital storage necessity, or predecessor acquisition proof is repeated. |
| [ST](RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md), §§1–3 | All original seeds, complete stopped-word/record isometry, positive finite history domains, distinct law/conf orders and exact endpoint TV distances. Endpoint-extraction witnesses do not bound the arbitrary-history numerical supremum. |
| [ACP](RECURSIVE_RELATIONAL_OBSERVATION_APPROXIMATE_COHERENCE_PRICE.md), §§1–2, 4 | The full-transcript metric, separate compatibility obligations and full-stopped-word coupling used in Lemma 4.2. Our deterministic actual holding has zero defect over the whole original domain; its target error is nevertheless nonzero. |
| [MP](RECURSIVE_RELATIONAL_OBSERVATION_MIXED_PHASE_DEFECT_ATTAINMENT.md), §§1, 3–5 | Its randomized four-tag law/conf and nonzero-defect conclusions keep their stated scope. They do not supply this deterministic-retention machine's cap bounds. |
| [NM](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md), §§2, 4–9 | NM's native source-mixture and positive suspended-emission conditions are subclass conditions. Here $Q(\alpha)=5/8$ exceeds every original $r_k$ and is outside its source-mixture subclass. No common optimal conf attainment is claimed. |
| [FSP](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_START_PREDICTIVE_MEMORY.md), §§7–11 | Finite-start acquisition, future-law recovery, chronology and represented costs are different tasks. Its five-mode source and memory minima do not transfer to the PH Read/Stop interface. |
| [Joint-coordinate source](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md), §§12.1–12.2 | Exact supplied joint statistics can recover a law in its own affine real-coordinate category. It provides neither a prior-mass certificate nor a Read instrument; real-coordinate count is not the COMPLETE budget or a finite-bit conclusion. |
| [Formal source](../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.lean), `legalRead`, `legalStop`, `parses_normal_form`, `first_completion_normal_form`, `stopped_word_fiber`, `noncompletion_fiber`, `actual_noncompletion_mass_zero`, `actual_fourth_segment_stopped_word_law` | These statements describe the actual fourth-segment raw completion law at fixed $r$, with $\alpha=0,\beta=1$. Mathematical `totalRead` totalization grants no post-terminal Read. The common-$K$ posterior and full original record/filtration correspondence are the separate PH/ST contracts used in §§2–3; reading formal source is not fresh kernel verification. |
| [Blueprint](../../../Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.md), Theorems 1.1–1.7 | Explicit scope of that fixed-parameter law and the separate conditional freshness, shared-depth posterior and same-record transcript obligations. |

**Mathematical citation 10.2 (future TV is a separate effective problem).** Taolue Chen and Stefan Kiefer, [*On the Total Variation Distance of Labelled Markov Chains*, arXiv:1405.2852v1](https://arxiv.org/pdf/1405.2852v1), Theorem 7 and Proposition 12, is `literature-attested` for convergent lower/upper future-trace TV approximations and an irrational TV value for rational labelled chains. These are intermediate boundaries for Open question 8.3, not new results of this volume. A finite future-trace approximation, or even computable fixed-history full TV, does not itself certify a supremum over arbitrary acquired PH histories.

**Proposition 10.3 (the recovered relation and its missing inverse).** For this construction, a charged finite boundary determines a legal executable future law and that law's conditional continuations, while losing the repetition count, true posterior and paid chronology of the original common source. Restoring a numerical full-risk witness requires additional quantitative prior information. In the whole COMPLETE category, fixed finite support with a positive floor at every supported atom restores uniform finite existence but does not by the compactness proof alone supply a computable uniform horizon.

**Proof.** Lemma 3.3 gives legal generation and both exact compatibility identities; Proposition 9.1 gives different original positive histories at the same retained boundary. Theorems 5.1 and 7.1 prove the obstruction and same-consumer repair, and Theorems 8.1–8.2 distinguish compact endpoint-floor families from the all-supported-masses-floor family. Every posterior in those arguments comes from the installed prior and the likelihood of one actual common-$K$ history. Finite memory, exact declared-law representation, actual acquisition, full-target loss, receiver archives, output work and source installation remain distinct accounts by §9 and PH37.2/PH49. No joint-cost optimum, physical spacetime reconstruction or global mutual-recovery completion follows. $\square$

## 追加锚（本行以下为增补区）
