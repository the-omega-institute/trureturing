# Effective paid-history certificates for the common-model configuration-risk frontier

## 1. The unchanged question and its finite observers

The question is whether one finite observer, on one common-depth source and one installed prior, can simultaneously attain the two complete-tail configuration-risk minima. With a supplied period bound and a finite neighborhood-exposure certificate for the prior, finitely many **actual possible histories** approximate all four risk coordinates uniformly over the arbitrary finite kernels of Definition 2.1. The certificate also covers countable priors, using mass near a finite parameter cover rather than a lower bound on every supported depth mass. It does not decide existence of a finite common optimizer or the sign of the unrestricted excess infimum.

A state-count-independent computable acquisition cap for finite priors, all supported mass floors and a certified privately contracting, exactly coherent digital observer class is supplied by [CF, Theorem 6.2]. That qualitative cap is reused. The source-specific increment here is the neighborhood-exposure certificate over all regular actual-flow kernels without a private-contraction assumption, together with the risk-only stationary replacement and the all-shape frontier comparison in Lemma 2.2 and Corollary 5.3.

**Definition 1.1 (one source and its original operations).** Let $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$, and install a finite or countable prior $\mu$ on positive integers with $\mu(1),\mu(2)>0$. Before any Read draw one $K$. Conditional on this same $K=k$, every paid seed Read and every payload Read is independent, with probabilities $r_k,1-r_k$ for $\alpha,\beta$, where

$$
r_k=F_{k+1}/F_{k+3},\qquad r_1=1/3,\quad r_2=2/5,\quad
r_k\in[3/8,5/13]\quad(k\ge3).
\tag{1.1}
$$

Keep $m=2,d=1,\ell=2,n=4$ and the entire original finite control $C_0$ and update table of [PH, Definitions 1.2–1.5 and 25.1]. Equal seed pairs are rejected and both Reads remain paid; $\alpha\beta$ accepts seed 0 and $\beta\alpha$ accepts seed 1. In payload phase p, $\alpha$ completes marker 0 and $\beta$ suspends. At suspension, $\alpha$ returns to p and $\beta$ completes marker 1. The first three completions advance segments. The third update writes its full record before latching it. Fourth completion enables only its original matching Stop, whose delivery is unique. Pending and delivered states admit no Read.

The finite control includes both seeds, selectors, the complete marker tree, bare fields, held records $B,Q^+,Z$, parser, write/latch flags, permissions, completion and Stop delivery. Every seed, marker triple, finite rejection word and finite payload-return history stays in the original domain. There is no source reset, fresh depth, extra actual observation or controller port, post-Stop Read, or conditioning on a future completion event.

Write $\mathcal H_p,\mathcal H_\beta$ for all positive finite actual fourth-segment histories at p and suspension. Write $\mathcal H_3\subset\mathcal H_p$ for the first fourth-segment cut only. The two domains are not identified. $N_R(h)$ counts every paid acquired Read, including seed rejections and partial pairs.

**Definition 1.2 (the complete future and its actual law).** Put $a_r=r(1-r)$ and $w_{j,0}=(\beta\alpha)^j\alpha$, $w_{j,1}=(\beta\alpha)^j\beta\beta$, $j\ge0$. The p carrier contains these completed raw words and its infinite noncompletion word. The suspended carrier contains $\beta$, $\alpha w_{j,b}$ and its infinite noncompletion word. The supplied stopped laws [ST, §2.1] are

$$
\begin{aligned}
P_{p,r}(w_{j,0})&=r a_r^j,&P_{p,r}(w_{j,1})&=(1-r)^2a_r^j,\\
P_{\beta,r}(\beta)&=1-r,&P_{\beta,r}(\alpha w_{j,0})&=r^2a_r^j,&
P_{\beta,r}(\alpha w_{j,1})&=r(1-r)^2a_r^j.
\end{aligned}
\tag{1.2}
$$

Their noncompletion masses are zero. The supplied measurable bijection $I_c$ [FLOW, Definition 2.4] retains every Read letter and inserts its original control, record, permission, completion, Stop and delivery events on the current actual record fiber $c$. Its inverse reads back the letters; it preserves TV and commutes with deleting the next operation and its deterministic event block. The already acquired suspended $\beta$ is not a future Read.

For an actual finite history $h$, its full target is

$$
T_h^\mu=(I_{C_0(h)})_*\sum_k\nu_h(k)P_{s,r_k},\qquad
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
{\sum_t\mu(t)r_t^{A(h)}(1-r_t)^{B(h)}}.
\tag{1.3}
$$

Both counts include all acquired Reads. The posterior and probability rows below are analysis quantities, never runtime inputs.

**Definition 1.3 (finite same-update observer, orders and defect).** The observer has a fixed finite COMPLETE configuration carrier, source-independent initialization, fixed time-homogeneous source-independent letter updates, and a decoder reading one actual configuration. COMPLETE counts $C_0$, program and table selectors, installed description, workspace, addresses, output indices, permissions, and all persistent randomness. It has no free clock, tape, archive, advice, correlated source seed, continuous register or readable probability-distribution vector.

From each configuration $z$, synthetic letter probabilities followed by the **same** acquired-letter update kernels generate its decoded full law $D_z$. This obligation is exact. Synthetic generation makes no actual source call. Abstract real entries specify finite stochastic rules; an effective sampler is asserted only for a separately represented effective table.

At the same actual history let $\rho_h$ be the conditional configuration row and put

$$
Q_h=\sum_z\rho_h(z)D_z,\quad
e_{\rm law}(h)=\operatorname{TV}(Q_h,T_h^\mu),\quad
e_{\rm conf}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu).
\tag{1.4}
$$

TV uses $\sup_E|P(E)-Q(E)|$, hence half the $\ell^1$ distance on the fourth-tail carrier. Set $R_{j,s}=\sup_{h\in\mathcal H_s}e_j(h)$ and $R_{j,s,H}=\sup_{h\in\mathcal H_s,N_R(h)\le H}e_j(h)$. Actual-history-average risk is a different consumer. Reuse the separate complete-tail minima

$$
\rho_p=1116529/22781250,\qquad \rho_\beta=239/6750.
\tag{1.5}
$$

The terminal projection has the separate supplied minima $13/266,9/266$; it does not replace (1.5). The published general-prior common law/law, law/conf and conf/law attainments, and the two-depth all-orders attainment, remain supplied results [CLIP, Citation 1.5].

Write $q_z(x)$ for the individual decoder's next-operation probability and $q_h(x)=\sum_z\rho_h(z)q_z(x)$. For a legal next operation $x$ with $q_h(x)>0$, define

$$
\delta(h,x)=\operatorname{TV}(\operatorname{res}_xQ_h,Q_{hx}).
\tag{1.6}
$$

Here the residual deletes that operation and its original event block after conditioning. At $q_h(x)=0$ set the defect to zero without defining a conditional law; the actual successor and its risk remain in the domain. $\Delta_4$ takes the fourth-segment supremum and $\Delta_{\rm all}$ takes the entire original-operation supremum. PendingStop has its deterministic zero-defect successor; deliveredStop has empty supremum zero. Only marginalized conditioning/update coherence is relaxed.

## 2. Actual-flow tables and a risk-only stationary realization

**Definition 2.1 (regular periodic table).** Its observer period $d$ is distinct from the fixed source parameter $d=1$. A table has finite nonempty sets $X_i,Y_i$, $i$ modulo a positive integer $d$, probability rows $\pi_i,\tau_i$, row-stochastic acquired-letter kernels $B_i:X_i\to Y_i$, $A_i:Y_i\to X_{i+1}$, and synthetic $\alpha$ probability vectors $u_i=(u_i(x))_{x\in X_i}$ and $v_i=(v_i(y))_{y\in Y_i}$. The entries of $\pi_i,\tau_i,B_i,A_i$ lie in $[0,1]$; each probability row and each row of either kernel sums to one, with zero and unit entries allowed. Only the emission vectors are restricted entrywise: $u_i(x),v_i(y)\in[1/3,2/5]$. This is the regular domain of [CLIP, Definitions 2.1 and 4.1]. Require

$$
\pi_iB_i=\tau_i,\qquad \tau_iA_i=\pi_{i+1}.
\tag{2.1}
$$

Before the latch, the observer retains only original control and synthesizes fair letters. In the same original update that writes the third record and then latches it, sample an $X_0$ label with the same fixed row $\pi_0$ on every original seed/record fiber, independently of the source and acquired word. No pre-latch private word state selects this row. Use $B_i$ after p-$\beta$, $A_i$ after suspended-$\alpha$, advancing the finite mode on that return only. Completing letters clear the labels and perform the original pendingStop transition. Every original record fiber uses this rule while retaining its own actual records. Mode, sampled labels, samplers, tables and all control are charged. The rows in (2.1) are not read by an online posterior service.

Let $Q_{i,x},W_{i,y}$ be the complete raw decoded laws from these labels. They are generated by these emissions and these same kernels. Conditional on every actual fourth-segment history with $i$ completed returns modulo $d$, its label row is exactly $\pi_i$ or $\tau_i$. This follows by induction from (2.1), since conditioning on a source word does not reweight the independent observer randomness by synthetic probabilities.

For $j\in\{\mathrm{conf},\mathrm{law}\}$ define

$$
\begin{aligned}
F_{{\rm conf},p,i}(r)&=\sum_x\pi_i(x)\operatorname{TV}(Q_{i,x},P_{p,r}),\\
F_{{\rm law},p,i}(r)&=\operatorname{TV}(\sum_x\pi_i(x)Q_{i,x},P_{p,r}),
\end{aligned}
\tag{2.2}
$$

and use $\tau_i,W_{i,y}$ at suspension. [CLIP, Proposition 2.3] supplies

$$
R_{j,s}=\sup_{i,k:\mu(k)>0}F_{j,s,i}(r_k).
\tag{2.3}
$$

These four coordinates belong to one installed table. The formula concerns full $\mathcal H_s$, not only $\mathcal H_3$. [CLIP, Proposition 5.3] also supplies

$$
|F_{j,s,i}(r)-F_{j,s,i}(t)|\le L_s|r-t|,\qquad
L_p=125/57,\quad L_\beta=107/57.
\tag{2.4}
$$

Its transcript correspondence includes the complete held records and Stop.

**Lemma 2.1.1 (full original-domain realization).** A table of Definition 2.1 defines one finite observer preserving the entire original source/control contract on every original positive finite history. Its individual decoder generation is exact from every retained operation cut, and its complete future includes the original infinite noncompletion outcomes.

**Proof.** Its actual update is the product of the original update on the full $C_0$ component and the specified private finite update. On every letter its projection to $C_0$ is the original update, with precisely that update’s entire event block. The private latch sampling is placed after the third record write and latch in that same update. Induction over original operations therefore preserves every field, record, permission and event on the same history. In particular equal pairs remain paid rejections, both unequal seeds remain accepted, every marker triple writes and holds its own records, every finite fourth return remains legal, and fourth completion enables only its matching original Stop. The private labels never change the enabled menu; completion clears them without changing held records or delivery.

From each configuration define the decoder as the probability law of this installed finite generator: synthetic letters use its emissions and then the identical acquired-letter transition and original event block. For a next-letter continuation $xE$ its defining cylinder identity is

$$
D_z(xE)=q_z(x)\sum_{z'}P_x(z,z')D_{z'}(E).
$$

This is individual generation, not an inference from a marginalized risk or defect. Before the latch, seed-pair survival has probability $1/2$ per rejected synthetic pair and early payload survival has probability $1/4$ per return. After the latch, a fourth return survives with probability at most $4/15$, from every label and at every mode. Thus synthetic completion and its sole Stop occur almost surely. Legal infinite noncompletion words remain in the full path carrier with zero mass; no completion event is used for renormalization. At each actual depth seed-pair survival is $1-2a_r\le5/9$, and each early payload return survives with $a_r\le6/25$; (1.2) gives the fourth-stage zero noncompletion mass. Thus original actual noncompletion has zero mass at each depth, and hence under the common prior as well. Pending and delivered decoder residuals are exactly the original deterministic Stop/delivery or empty law. The entire current-record rendering is through $I_c$, not just a terminal marker.

For a represented finite sampler, internal states carry the conditional continuation of that same finite service program and are included in COMPLETE. They introduce no extra source-query cuts or permissions. At the original returned cuts the effective synthetic joint transition is exactly $q_z(x)P_x(z,z')$, using fresh independent emission and update bits where the represented program needs them. ∎

**Lemma 2.2 (finite stationary realization for risk comparison).** From any table of Definition 2.1 construct one regular table with period one and finite label sets $X=\bigsqcup_iX_i$, $Y=\bigsqcup_iY_i$, such that all four risks are no greater. Each active p or suspended labeled configuration retains its complete decoded law. Pre-latch laws use the new latch sampler, with exact individual same-update generation throughout. The construction does not preserve a prescribed hard defect bound; instead

$$
\Delta_{\rm all}^{\rm new}\le\min\{1,\Delta_{\rm all}^{\rm old}+1/10\}.
\tag{2.5}
$$

**Proof.** Install the same labeled transitions: $B$ sends $X_i$ to $Y_i$ by $B_i$, and $A$ sends $Y_i$ to $X_{i+1}$ by $A_i$. Keep the same emissions. Initialize the active label at the third latch with $\pi(i,x)=\pi_i(x)/d$. Set $\tau(i,y)=\tau_i(y)/d$. The new rows sum to one, and the disjoint-union kernels are row-stochastic, with zeros outside their indicated blocks. All emissions retain their values in $[1/3,2/5]$, so this is a table of Definition 2.1. Then $\pi B=\tau$ and $\tau A=\pi$. Thus the acquired p and suspended rows are stationary. No source or original control is restarted: only the source-independent private latch sampler changes. From a particular active labeled configuration the entire subsequent synthetic program is unchanged, so its complete decoded law is unchanged. Before the latch the program uses the new sampler, and its decoded laws are defined by that changed same-update program.

For conf, its pure-target error is the average of the old mode errors. For law, TV convexity bounds the distance of its averaged mode forecast by that same average of old law errors. Each is at most the corresponding old supremum in (2.3). This proves simultaneous risk domination, using the same actual prior and history domain.

For the p-$\beta$ defect put $q_i=\pi_i(1-u_i)$. In the new conditional residual, the mode weight is $\theta_i=q_i/\sum_tq_t$, whereas the actual successor mode weight is $1/d$. The old conditional residual in each mode is within $\Delta_{\rm all}^{\rm old}$ of its old successor forecast. Convexity and the triangle inequality give an additional error at most $\operatorname{TV}(\theta,\mathrm{Unif})$. If $q_i\in[a,b]$, then

$$
\operatorname{TV}(\theta,\mathrm{Unif})
=\frac{d^{-1}\sum_i|q_i-\bar q|}{2\bar q}\le\frac{b-a}{2a}.
$$

Here $[a,b]=[3/5,2/3]$, giving $1/18$. At suspended-$\alpha$, the weights use $\tau_i v_i\in[1/3,2/5]$, giving $1/10$. Completing residuals are the same deterministic terminal laws. Earlier emissions are fair and the new latch sampler is used in both acquired and synthetic updates, so those defects remain zero. Pending and delivered laws are unchanged. Taking the maximum proves (2.5). All active predicted letters have positive probabilities. This proof does not infer marginalized coherence from unchanged individual generation. ∎

**Corollary 2.3 (remaining risk-only frontier in stationary tables).** Let $\mathfrak M_\mu$ be the entire finite observer class of Definition 1.3, $\mathfrak E_\mu$ its regular periodic tables, and $\mathfrak S_\mu$ the regular period-one tables. Define

$$
J(\mathfrak A)=\inf_{M\in\mathfrak A}
\max\{R_{{\rm conf},p}(M)-\rho_p,R_{{\rm conf},\beta}(M)-\rho_\beta\}.
$$

Then

$$
J(\mathfrak S_\mu)=J(\mathfrak E_\mu),\qquad
J(\mathfrak M_\mu)\le J(\mathfrak S_\mu)\le(61/11)J(\mathfrak M_\mu).
\tag{2.6}
$$

A finite common endpoint model exists in $\mathfrak M_\mu$ if and only if one exists in $\mathfrak S_\mu$. Zero excess infimum and a strictly positive unrestricted gap are likewise equivalent between these two classes. These statements impose no hard defect budget and preserve no original state or total-cost budget.

**Proof.** Lemma 2.2 and inclusion give equality of the two regular infima. Apply [CLIP, Theorem 4.2] to the original common source, complete tails and both configuration-risk orders of Definition 1.3; its factor and exact-endpoint assertion give (2.6) and existence. Fold its exact regular endpoint table by Lemma 2.2. Separate minima (1.5) make the dominated endpoint bounds equalities. The defect qualification is necessary because the phase weights change after synthetic conditioning. In particular an old zero defect gives only the bound $\Delta_{\rm all}^{\rm new}\le1/10$ from Lemma 2.2, not zero-defect recovery. ∎

## 3. A finite exposure certificate for the installed prior

Put $I=[1/3,2/5]$, $w=|I|=1/15$, and let $S_\mu=\overline{\{r_k:\mu(k)>0\}}\subset I$.

**Definition 3.1 (neighborhood exposure).** A certificate consists of rational numbers $0<\delta\le1/15$, $0<\eta<1$, $0<b\le1$, and a finite nonempty rational set $T=\{t_1,\ldots,t_m\}\subset I$, satisfying

$$
S_\mu\subset\bigcup_{t\in T}[t-\delta,t+\delta],\qquad
\sum_{k:|r_k-t|\le\delta/4}\mu(k)\ge b\quad(t\in T).
\tag{3.1}
$$

The first condition is a support cover; the second is mass in a smaller neighborhood. Centers need not be actual depths. The certificate is mathematical data about the same installed prior, not an observation port or runtime probability register. Supplying, verifying and representing it have separate costs.

**Lemma 3.2 (availability and its limits).** Every fixed allowed finite or countable prior admits such a certificate for every rational $0<\delta\le1/15$ and any chosen $0<\eta<1$. Existence does not provide a uniform algorithm extracting it from an opaque prior. For a finite support, a certificate can use its actual rational parameters as centers and any certified lower bound on its positive masses. An infinite support need not have a positive lower bound on every atom.

**Proof.** The actual supported parameters are dense in their compact closure. Their open $\delta$-balls cover that closure: at a closure point choose a supported parameter at distance less than $\delta$. Take a finite subcover, retaining actual supported parameters as centers. Each center has positive prior mass and belongs to its own inner neighborhood. Choose a positive rational $b$ below the minimum of those finitely many masses. The closed cover and the mass inequalities follow. No computability premise about support or masses entered this existence proof. The finite-support assertion is direct. ∎

**Lemma 3.3 (likelihood separation of neighborhoods).** For $t,r\in I$ let

$$
D(t\Vert r)=t\log(t/r)+(1-t)\log((1-t)/(1-r)).
$$

Then

$$
2(t-r)^2\le D(t\Vert r)\le(9/4)(t-r)^2.
\tag{3.2}
$$

Consequently $|r-t|>\delta$ and $|v-t|\le\delta/4$ imply $D(t\Vert r)-D(t\Vert v)\ge\delta^2$.

**Proof.** As a function of its first argument $x$, $D(x\Vert r)$ has value and first derivative zero at $x=r$, and second derivative $1/(x(1-x))$. On the interval between $t$ and $r$, this derivative lies in $[4,9/2]$. Twice integrating gives (3.2). The difference is at least $(2-9/64)\delta^2>\delta^2$. This is ordinary Bernoulli likelihood calculus; the new source use is in the following paid-history bound. ∎

## 4. One finite actual-history family for arbitrary kernels

**Theorem 4.1 (uniform paid-history certificate).** Fix a certificate (3.1) and a positive integer $D_0$ bounding the table period. Let $a$ be a common positive denominator of all $t\in T$, and define by rational and integer comparisons

$$
C_{D_0}=(27/25)^{D_0+2}(10/9),\qquad
q=\min\{z\in\mathbb N:2^z\ge C_{D_0}/(b\eta)\},
$$

$$
n=a\left\lceil\frac{q}{2a\delta^2}\right\rceil,\qquad
H=2n+2D_0+5.
\tag{4.1}
$$

For $t\in T$, $0\le i<D_0$ and $e\in\{0,1\}$, use the original acquired words

$$
h_{t,i,e}=(\alpha\alpha)^{nt}(\beta\beta)^{n(1-t)}
\beta\alpha\mid\beta\beta\alpha\alpha\,(\beta\alpha)^i\beta^e.
\tag{4.2}
$$

The bar marks a boundary and is not a source symbol. $e=0$ is a p query and $e=1$ a suspended query. Denote the finite respective sets by $\mathcal W_p,\mathcal W_\beta$. They depend on the certificate and period bound, not on the number of labels, entries, mixing rate or emissions of a table.

For **every** regular periodic table of period $d\le D_0$, all its arbitrary finite kernels, both risk orders and the same installed prior satisfy

$$
0\le R_{j,s}-\max_{h\in\mathcal W_s}e_j(h)
\le E_s:=L_s(2\delta+w\eta),
\tag{4.3}
$$

and hence

$$
0\le R_{j,s}-R_{j,s,H}\le E_s.
\tag{4.4}
$$

Every displayed word is positive and legal, has at most $H$ paid Reads, and has source probability at least $3^{-H}$. The bounds concern complete unbounded futures. They assert possible witnesses, not the ability to force a source word, restart a run or encounter a specified witness with certainty.

**Proof.** Each initial equal pair is an original paid seed rejection. The suffix $\beta\alpha$ accepts seed 1; $\beta\beta,\alpha,\alpha$ completes the first three markers as 100, with the original third write and then latch. Each following $\beta\alpha$ is one legal fourth-segment return. The final $\beta$ suspends when $e=1$. Thus (4.2) is an original positive history with the same actual record, independently of $t,n,i$. Its paid length is $2n+6+2i+e\le H$. Each actual letter has probability at least $1/3$ at every supported depth; mixing the positive likelihoods gives the stated occurrence bound. No rejected or accepted operation is added or removed.

The acquired counts are

$$
A=2nt+3+i,\qquad B=2n(1-t)+3+i+e.
\tag{4.5}
$$

For parameter $r$, its likelihood is

$$
\exp\{2n[t\log t+(1-t)\log(1-t)]-2nD(t\Vert r)\}
\,a_r^{3+i}(1-r)^e.
\tag{4.6}
$$

For $r\in I$ outside the $\delta$-neighborhood and $v\in I$ in the $\delta/4$-neighborhood, Lemma 3.3 bounds the rejection-block likelihood ratio by $e^{-2n\delta^2}$. Moreover $a_r\in[2/9,6/25]$ and $1-r\in[3/5,2/3]$. The suffix ratio is at most

$$
(27/25)^{3+i}(10/9)^e\le C_{D_0}.
$$

For each outside parameter this comparison holds against every inside parameter. Integrate the denominator over the inside prior mass, at least $b$, and the numerator over the outside mass, at most one. The same acquired posterior therefore obeys

$$
\nu_{h_{t,i,e}}\{|r_K-t|>\delta\}
\le(C_{D_0}/b)e^{-2n\delta^2}
\le(C_{D_0}/b)2^{-q}\le\eta.
\tag{4.7}
$$

The summation is valid for countably many depths; no atom separation, smallest positive mass or tail oracle is used. Since every parameter lies in $I$, (4.7) gives

$$
\sum_k\nu_{h_{t,i,e}}(k)|r_k-t|\le\delta+w\eta.
$$

Using the full-law bound underlying (2.4), convexity and the same current $I_c$,

$$
\operatorname{TV}(T_{h_{t,i,e}}^\mu,(I_c)_*P_{s,t})
\le L_s(\delta+w\eta).
\tag{4.8}
$$

At this actual history the table row is exactly $\pi_{i\bmod d}$ or $\tau_{i\bmod d}$. There is no limit of observer kernels to estimate. Triangle inequalities before configuration averaging, or after forecast marginalization, yield

$$
|e_j(h_{t,i,e})-F_{j,s,i\bmod d}(t)|
\le L_s(\delta+w\eta).
\tag{4.9}
$$

For every supported parameter $r$, the cover supplies $t$ within $\delta$. Thus (2.4) and (4.9) imply

$$
F_{j,s,i}(r)\le e_j(h_{t,i,e})+L_s(2\delta+w\eta),
$$

choosing $0\le i<d\le D_0$ in (4.2). Take the supremum using (2.3). The reverse inequality holds because every witness is an actual history in the original domain. This proves (4.3), and inclusion in the acquired cap proves (4.4). Both orders use the same row and actual posterior throughout. ∎

**Corollary 4.2 (a total regular-subclass horizon under finite source data).** Fix a finite depth menu $S$ containing 1 and 2, a feasible rational mass floor $b>0$ with $|S|b\le1$, and a period bound $D_0$. Over all priors with exact support $S$ and every mass at least $b$, there is a total computable cap approximating every regular table's four phase risks to any rational positive accuracy. The cap has no label-count or table-entry dependence, and applies to its exactly marginalized-coherent subclass as well.

**Proof.** Use $T=\{r_k:k\in S\}$. For any rational $0<\epsilon\le1/4$, take $L=125/57$, $\delta=\epsilon/(4L)$ and $\eta=\epsilon/(2Lw)$. These satisfy Definition 3.1 and $E_s\le\epsilon$. Formula (4.1) is terminating rational arithmetic. For larger accuracy use $\min\{\epsilon,1/4\}$. Marginal exactness only restricts the tables covered by Theorem 4.1. ∎

The installed table may still have abstract real entries; the cap's integer computation does not evaluate them. Effective evaluation of an individual table additionally needs an effective represented table and prior. An infinite prior can use Theorem 4.1 whenever a finite exposure certificate is supplied. Lemma 3.2 does not supply its effective acquisition from an arbitrary prior description.

**Representation convention 4.3 (cap versus evaluated risk).** Formula (4.1) computes an integer cap from the supplied rational exposure data and period bound, without evaluating the table or prior. Evaluating the finite-history loss functionals additionally requires their numerical entries. With a finite rational prior and rational table, every level-$L$ partition probability is rational and calculable by finite matrix products and Bayes normalization. For a countable prior, a sufficient external representation supplies computable masses and an effective tail-mass bound: all summands in the likelihood and partition numerators are bounded by the prior masses, and for a word of length at most $H$ the Bayes denominator is at least $3^{-H}$. These bounds give certified approximations of the normalized finite partition probabilities. Rational table entries again suffice for its synthetic coordinates. An opaque prior together with (3.1) alone supplies neither those numerical evaluations nor an algorithm for finding the exposure data. The semantic inequalities below still hold for such a prior. All certificate and evaluation work has its own costs and is absent from runtime state.

## 5. Complete-tail and defect certificates on the same histories

**Definition 5.1 (finite future partition).** At p distinguish all complete $w_{j,b}$ for $0\le j<L$ and put all other outcomes, including infinite noncompletion, in one residual cell. At suspension distinguish $\beta$ and $\alpha w_{j,b}$ for $j<L$, with one residual cell. Let $e_{j,L}(h)$ be the respective TV error with both laws pushed to this partition, retaining configuration-before-TV or configuration-after-TV in its indicated order. Put $A_{j,s,L}=\max_{h\in\mathcal W_s}e_{j,L}(h)$.

**Theorem 5.2 (one common finite semantic certificate).** For the same table, prior and actual witness family of Theorem 4.1,

$$
0\le R_{j,p}-A_{j,p,L}\le E_p+(6/25)^L,
$$

$$
0\le R_{j,\beta}-A_{j,\beta,L}\le E_\beta+(2/5)(6/25)^L.
\tag{5.1}
$$

The two noncompleting edges from these histories also cover every fourth-segment defect mode. Let $D_L$ be their maximum defect with the residual laws pushed to the corresponding level-$L$ future partition. Then

$$
0\le\Delta_{\rm all}-D_L=\Delta_4-D_L\le(4/15)^L.
\tag{5.2}
$$

These are simultaneous coordinates of one model. No per-configuration generation defect is introduced.

**Proof.** Refining a residual cell with masses $a,c$ increases TV by at most $\min(a,c)$, since its extra half-$\ell^1$ contribution is at most $[(a+c)-|a-c|]/2$. The actual target's residual mass is at most $(6/25)^L$ at p and $(2/5)(6/25)^L$ at suspension, uniformly over the actual posterior. Apply this inequality to each configuration, then average for conf; apply it directly after averaging for law. Combine the resulting finite-witness bound with (4.3) to obtain (5.1). The carrier has never been conditioned on completion.

For clarity the actual and predicted successor rows differ. At mode $i$ set $U_i=\operatorname{diag}(1-u_i)$, $V_i=\operatorname{diag}(v_i)$ and

$$
q_i=\pi_i(1-u_i)\ge3/5,\quad
\gamma_i=\pi_iU_iB_i/q_i,\quad
\ell_i=\tau_i v_i\ge1/3,\quad
\zeta_i=\tau_iV_iA_i/\ell_i.
$$

The p-$\beta$ defect compares $\sum_y\gamma_i(y)W_{i,y}$ to $\sum_y\tau_i(y)W_{i,y}$. The suspended-$\alpha$ defect compares $\sum_x\zeta_i(x)Q_{i+1,x}$ to $\sum_x\pi_{i+1}(x)Q_{i+1,x}$. These equations depend only on the table row, not the actual source posterior. The displayed witness histories hit every mode. Their legal actual successors execute precisely these same original events and acquired kernels, even when that successor is not itself a chosen witness word.

For synthetic generation, each p return has survival probability at most $(2/3)(2/5)=4/15$, irrespective of intermediate sampled labels. After $L$ returns every p law has residual mass at most $(4/15)^L$, and every suspended law at most $(2/5)(4/15)^L$. The residual-cell inequality therefore bounds the difference between each full defect and its partition defect by at most $(4/15)^L$. Completing edges have the identical deterministic terminal residual, early fair-emission updates have zero defect, and pending/delivered laws have zero defect. This proves (5.2). Active predicted letters are positive; the zero-event convention remains that of Definition 1.3. Infinite noncompletion stays a legal outcome and has zero mass under these regular laws, by the same survival estimate. ∎

**Corollary 5.3 (uniform finite-history bridge across all stationary shapes).** Fix one installed prior. Choose a sequence of exposure certificates with $\delta_n,\eta_n\to0$, and future levels $L_n\to\infty$. Use period bound $D_0=1$. Over **all finite stationary regular shapes**, let

$$
K_n=\inf_M\max\{A_{{\rm conf},p,L_n}(M)-\rho_p,
A_{{\rm conf},\beta,L_n}(M)-\rho_\beta\}.
$$

Then, with $J_S=J(\mathfrak S_\mu)$,

$$
0\le J_S-K_n\le
\max_s E_{s,n}+(6/25)^{L_n}\longrightarrow0.
\tag{5.3}
$$

Consequently a strictly positive unrestricted conf/conf gap exists if and only if some $K_n>0$. A proved positive all-shape lower bound $K_n\ge c>0$ implies $J(\mathfrak M_\mu)\ge11c/61$. No algorithm for $K_n$, finite-state optimizer bound, or positive value is asserted.

**Proof.** The errors in Theorem 5.2 are uniform in the entire finite shape and all its kernel entries. Taking the two-phase maximum and then the infimum preserves the same error bound. This proves (5.3), without compactness over the unbounded union of shapes. If $J(\mathfrak M_\mu)>0$, (2.6) gives $J_S>0$, so sufficiently small error in (5.3) gives $K_n>0$. Conversely $K_n>0$ implies $J_S\ge K_n>0$, and (2.6) gives the stated lower bound. ∎

The finite infimum in this corollary still ranges over every finite number of labels. A finite grid cannot establish its positive lower bound. For endpoint existence one still needs **one finite shape and one table** satisfying all full-tail conditions; different shapes at successive levels do not supply an optimizer. The corollary controls the acquired-history quantifier uniformly after a risk-only stationary realization, without interchanging those existence quantifiers or preserving a prescribed hard defect budget.

## 6. Endpoint mass floors do not suffice even for one stationary regular observer

The supplied three-depth endpoint-tag counterexample [ST, equations (3.17)–(3.21); CLIP, Citation 1.5] concerns the complete atom $w_{3,1}$. Its interior excursion is reused here, not a new phase-radius computation or arbitrary-law obstruction.

**Proposition 6.1 (one bounded table, failure of every endpoint-floor-only cap).** There is one fixed rational regular period-one table with two p labels and two suspended labels, exact individual same-update generation and a fixed positive marginalized defect, for which no finite cap uniform over all three-depth priors with endpoint masses at least $1/4$ can approximate conf/conf full-history excess to one fixed positive accuracy.

**Proof.** At the third latch sample a fair persistent tag $J\in\{1,2\}$. Acquired noncompleting updates preserve the tag; synthetic emissions use $r_J$ at both phases. Completing updates clear it and execute the original Stop. Thus its individual decoded laws are exactly $P_{p,r_J},P_{\beta,r_J}$, with their own actual current records. This is a regular period-one table with $B=A=I$ and $\pi=\tau=(1/2,1/2)$. The fair tag, original controls, table and sampler workspace are finite and charged. Both seeds, every triple and every return history remain available.

Let $r_3=3/8$, $w_*=(\beta\alpha)^3\beta\beta$, and put

$$
\chi=P_{p,r_3}(w_*)-\max\{P_{p,r_1}(w_*),P_{p,r_2}(w_*)\}
=\frac{84375}{16777216}-\frac{1944}{390625}>0,\qquad g=\chi/2.
\tag{6.1}
$$

The endpoint masses are $32/6561$ and $1944/390625$, with the latter larger; its difference from $84375/16777216$ is positive by cross multiplication. For any three probability laws on the countable carrier, the coordinate triangle identity gives

$$
\frac12\operatorname{TV}(P_1,T)+\frac12\operatorname{TV}(P_2,T)
-\frac12\operatorname{TV}(P_1,P_2)
=\frac12\sum_w\operatorname{dist}\bigl(T(w),[\min(P_1(w),P_2(w)),\max(P_1(w),P_2(w))]\bigr).
\tag{6.2}
$$

Include the infinite outcome in that sum. The one reused atom (6.1) and $\operatorname{TV}(P_{p,r_1},P_{p,r_2})=2\rho_p$ imply the pure-depth-3 p-conf risk is at least $\rho_p+g$. Formula (2.3) therefore gives $\Phi_\infty^{\rm conf,conf}\ge g$ for every positive prior on $\{1,2,3\}$, where $\Phi_H=\max_s(R_{{\rm conf},s,H}-\rho_s)$. It uses the same fixed installed tag observer. Equivalently, original rejection words with limiting acquired $\alpha$ frequency $3/8$ concentrate their actual posterior at depth 3; their tag row remains fair. They are finite positive histories of that one prior.

Now install $\mu_z=(1/4,3/4-z,z)$, $0<z\le1/4$. For any acquired history with $A+B\le H$, its actual depth-3 posterior satisfies

$$
\nu_h(3)\le\frac{z}{1/4}
\left(\frac{r_3}{r_1}\right)^A
\left(\frac{1-r_3}{1-r_1}\right)^B
=4z(9/8)^A(15/16)^B\le4z(9/8)^H.
\tag{6.3}
$$

Remove its depth-3 mass and normalize its endpoint posterior to obtain $T_h^0$. Every coordinate of $T_h^0$ lies between the two endpoint coordinates. Equation (6.2) hence gives fair-tag conf error exactly $\rho_s$ at either phase. The original $T_h^{\mu_z}$ is at TV distance at most $\nu_h(3)$ from this same-history endpoint mixture. Consequently

$$
\Phi_H^{\rm conf,conf}(M,\mu_z)\le4z(9/8)^H.
\tag{6.4}
$$

For any integer $N\ge7$ choose the positive rational $z_N=(g/16)(8/9)^N<1/4$. Then both endpoint masses have the stated floor, $\Phi_N\le g/4$ and $\Phi_\infty\ge g$. The gap is at least $3g/4$. An accuracy $g/2$ therefore admits no finite uniform cap, even for this fixed table, fixed three-depth menu and fixed endpoint floor.

This table's marginalized defect is positive: conditioning a predicted p-$\beta$ changes the tag weight from $1/2$ to $10/19$, and the two suspended laws differ. Conditioning suspended-$\alpha$ changes that weight to $5/11$, and the two p laws differ. These are exact same-update conditional laws, not generation errors. Thus this proposition imposes no zero-defect membership in PH37. It gives neither a universal conf/conf obstruction nor a positive unrestricted joint infimum. ∎

The contrast with Corollary 4.2 is precise. Every depth mass has a floor in that corollary; here the depth-3 mass tends to zero. More generally Theorem 4.1 permits small unrepresented atoms when they lie near exposed representative neighborhoods. Endpoint floors alone do not expose a separated supported interior target. The necessary accuracy and source-family assumptions cannot be inferred from a state count or a Fibonacci name.

## 7. Resource, effectiveness and task-relative whitebox consequences

**Proposition 7.1 (complete causal accounting).** The proofs add no online acquired count, posterior, probability row, history-selection service or source-query capability. A periodic table uses at most the generous returned-cut allocation $|C_0|(1+\sum_i(|X_i|+|Y_i|))$ before numerical sampler/workspace expansion. Lemma 2.2 uses the same union of labels with a changed finite latch distribution, not an uncounted external phase. No original state or total-resource budget is preserved by the supplied comparison from $\mathfrak M_\mu$.

For a rational represented table, exact finite categorical sampling can be realized with charged finite candidate bits, bit cursor, current row/label indices, PC, addresses, threshold data, event/output cursor, original records and every sampler microstate. All installed code/data and installation workspace count. Acquired Reads, fresh random bits, internal work, output length, offline certificate work and source-provider storage are separate accounts. There is no finite worst-case total return-word, random-bit or output-length bound.

**Proof.** The active runtime state is one sampled finite label and its current original $C_0$. The rows describe the probabilities of those states but are not retained as numerical registers. A common-denominator rational row is sampled by drawing a fixed-width integer, rejecting integers beyond its denominator and selecting among finite cumulative thresholds. Candidate storage and the cursor are finite; retries reuse that same storage and require no retained retry counter. The threshold table, row selector and sequential lookup program are finite installed data. Rejection sampling returns almost surely and has unbounded possible work, all of which is charged when used. Clearing scratch at service return leaves a finite COMPLETE carrier; synthetic and acquired updates use the same row sampler. The original event blocks and record rendering have finite cursors included in $C_0$ and its charged program workspace. Synthesis carries its own paid cursor and makes no actual Read.

The certificate (3.1), integer computation (4.1), displayed words, likelihood comparisons and partition calculations are external mathematical data and computations. If computed, retained or output by an implementation, their program, integer width, memory and work must be charged; if fed online to a predictor, they belong to its COMPLETE accounting and would be additional supplied inputs. The theorems merely certify possible original histories. Abstract real tables supply no exact-real sampling implementation. The original source provider keeps its one inaccessible common $K$ and installed prior in its separate account; no proof row gives the observer access to them. ∎

**Corollary 7.2 (quality on the same common source).** Let $W_{j,s}=1-R_{j,s}$. A certificate for one table consisting of its complete finite generative description, (3.1), the original acquired words (4.2), and its level-$L$ same-model partition comparisons yields

$$
1-A_{j,s,L}-E_s-c_s(6/25)^L\le W_{j,s}\le1-A_{j,s,L},
\qquad c_p=1,\quad c_\beta=2/5,
\tag{7.1}
$$

and $D_L\le\Delta_{\rm all}\le D_L+(4/15)^L$. This certifies task-relative semantic quality and marginalized coherence of one model, with individual generation already supplied by its program. It does not recover that program from the semantic coordinates or classify trained networks.

**Proof.** Subtract the common-model bounds (5.1) from one and apply (5.2). ∎

**Mathematical correspondence 7.3 (scope of external suppliers).** Gimbert and Oualhadj, *Probabilistic Automata on Finite Words: Decidable and Undecidable Problems*, author full version [GO, Definition 2 and Theorem 1 (Paz)], gives undecidability of strict emptiness for finite probabilistic automata with entries $0,1/2,1$ at cutpoint $1/2$. [EA, §§3–9] transports that problem through private labels retained over arbitrary paid seed-rejection words to the whole PH37 exact-marginal-coherence program class. That construction does not have Definition 2.1's source-independent fresh latch row and periodic fourth-segment actual-flow certificate. Theorem 4.1 gives a total acquired-cap computation when these additional premises and finite exposure data are present, including any exact-coherence tables within this subclass. Thus the published whole-program noncomputability theorem supplies no impossibility for this computation or for stationary-table endpoint feasibility. Its reduction cannot transfer while silently replacing its program/historical-state quantifiers.

[PR, Convention 1.1, Definition 2.1 and Theorem 7.3] strengthens the whole-program obstruction. Fix a rational $\tau>0$, one rational prior on a finite support containing 1 and 2, and a positive floor at **every** supported depth. It gives a digitally represented family satisfying both exact compatibilities and $t_*<\Phi_\infty<t_*+\tau$ for all four objectives, where $t_*$ is its supplied isolated algebraic optimum. At one rational accuracy $\epsilon_0(\tau)>0$, independent of its private automaton, no algorithm guaranteed to terminate with a correct acquired cap on every constructed description-plus-certificate exists; a total budget-based cap is therefore also excluded. This is stronger than a counterfamily with vanishing interior prior mass. Its private automaton label depends on the paid rejection word and survives to a special first fourth-segment gate; the first fourth Read then erases it. The fixed fresh latch row and periodic actual-flow identities of Definition 2.1 are additional hypotheses absent from that family. In particular its pre-erasure gate row is not made stationary by its small risk or exact compatibilities. [PR, Proposition 9.1] explicitly separates original transient reports from the extracted baseline cycle. Corollary 4.2 therefore applies to a narrower class on the same finite-prior menu and all-mass floors; its computable cap is not a whole-PH37 claim. Corollary 2.3 compares risks of replacement models without preserving original transient reports, acquired localization costs, a hard defect bound or a COMPLETE budget. It provides no horizon for the original promised-risk observer and no all-shape optimizer or positive gap. Proposition 6.1 has a different failure mechanism: it fixes one regular observer with positive marginalized defect and varies a prior family without an interior mass floor.

[CF, Convention 2.1, Definition 3.1 and Theorem 6.2] supplies a different sufficient history certificate on the same original common-$K$, paid-Read, full-record and complete-tail consumer. It fixes a finite exact depth menu $S\supset\{1,2\}$ and a positive rational floor $b$ on **every** supported mass. Its observer is a finite sequential-bit COMPLETE program with source-independent initialization and rational effective acquired kernels $P_x(c)$, bound to that program and its full ready-state fibers $X_c$. Both individual same-update generation and actual-history marginalized conditioning/update coherence must be exact. Its certificate gives an integer $\tau\ge1$ and rational $0\le\theta<1$ such that every legal length-$\tau$ Read block $v$, from every original active cut $c$, satisfies

$$
\max_{z,z'\in X_c}\operatorname{TV}\bigl(P_v(c)(z,\cdot),P_v(c)(z',\cdot)\bigr)\le\theta.
$$

This quantifies over all private rows on the same **complete** original fiber, including the seed parser, half-pairs, early segments, latch and fourth segment; it is not merely a statement about the one row reached from an initializer. The supplied total computable $H(S,b,\epsilon,\tau,\theta;\delta_0)$ is independent of private state count and decoded laws. Every actual fourth-phase history has a positive history of length at most $H$ with the same complete control, phase and records and with both losses uniformly close. Thus its four phase risks and all four law/conf combinations have acquired-cap error at most $\epsilon$. Its semantic theorem permits real prior masses; numerical risk intervals additionally require effective program and prior representations [CF, Corollary 7.1]. Its program, all sampler microstates, peak workspace, paid Reads, randomness, synthesis, output, source and external certificate/evaluation work remain separately charged. Private contraction does not erase the common-depth posterior, reconstruct actual age or force a witness on the sole source run [CF, Propositions 11.1–11.2 and Account 11.3]. These distinctions and the qualitative cap on the overlapping finite-prior, all-mass-floor, rational, exactly coherent tables sharing a contraction certificate are supplied results, not additional content of Corollary 4.2.

Theorem 4.1 uses different hypotheses. Its actual rows are fixed by a fresh source-independent latch and the flow identities (2.1), rather than controlled by decay between arbitrary private starting rows. Its cap depends on the finite exposure data and period bound, with no contraction rate, private state count or kernel-entry input. A lower mass bound is needed only in the inner neighborhoods of the finite cover, so countable priors are included. Arbitrary real table entries specify mathematical stochastic rules, not a digital sampling implementation; marginalized defects can be positive. Conversely, [CF, Theorem 6.2] does not require these fresh-latch and periodic-flow identities and compares each original history on its own full record fiber. The two sufficient classes are therefore not identified. None of these source-correspondence statements adds a premise to Theorems 4.1 or 5.2.

The persistent-tag table of Proposition 6.1 makes the missing contraction implication explicit. Both tags have positive conditional probability on one actual latched history. For every integer $\tau\ge1$, the length-$\tau$ prefix of $\beta\alpha\beta\alpha\cdots$ is legal from p and never completes the fourth segment. Since $B=A=I$, its two starting tags end in disjoint tag states on the same final original fiber; their acquired-row TV is exactly 1. It therefore has no [CF, Definition 3.1] certificate with $\theta<1$, despite its stationary fair actual row. Forgetting the tag also fails the complete-decoder equality required by [CF, Proposition 7.2]: its two p laws assign probabilities $1/3$ and $2/5$ to the future word $\alpha$, and its suspended laws assign $2/3$ and $3/5$ to $\beta$. This check concerns that specified table; it does not say that every regular table fails contraction. The example's positive marginalized defect separately prevents treating it as a member of the supplier's exactly coherent class.

[CF, Proposition 7.2] preserves both losses under a strong-lumpability quotient whose merged configurations have identical complete decoded measures. Lemma 2.2 instead keeps all active labels, changes the latch distribution and dominates the four risks; it changes pre-latch laws and supplies only (2.5) for marginalized coherence. It supplies neither private contraction nor a hard-defect or COMPLETE-budget preservation. The supplier's uniform cap fixes $S,b,\tau,\theta$ and its program/coherence hypotheses; it does not cover the union of all stationary regular shapes in Corollary 5.3. No uniformly certified contracting replacement for that entire union, or equality of its risk infimum with the supplier's certified-subclass infimum, is assumed or supplied by these results. The infimum comparison itself is elementary; its source-specific input here is the actual-history approximation uniform over that full union. Neither certificate decides common endpoint attainment, an unattained zero excess infimum or a positive unrestricted gap.

Chen and Kiefer, *On the Total Variation Distance of Labelled Markov Chains* [CK, Theorem 7 and Corollary 8], give convergent computable TV intervals for a supplied pair of finite rational labeled Markov chains and their specified initial distributions. It concerns one fixed future-law comparison, rather than the supremum over arbitrary acquired words. Here (4.7) supplies an explicit finite acquisition bridge, while (5.1) supplies a complete stopped-tail bound. These are distinct uses of history and future length; no rational-valued TV oracle is assumed. [CK, Proposition 12] explicitly permits irrational distances for rational chains.

The FIB five-window moment and seam results [FIB-H, §§6–7; FIB-I, §§20 and 31] use supplied exact model statistics, ordered numerical replies, current composition and guarded continuation. Their same-source joint-state/cost requirement is retained; their five semantic modes are not the p/suspended configuration carrier. [KB, Definition 89.1 and Theorem 89.2] uses $(k,m,T,g)=(16,14,17,1)$, one triple joined label class, complete emitted fourteen-bit blocks and own completed scalar endpoints; its fixed-stream fees $4,5$ have that different operation and source contract. None supplies (1.3), a paid rejection-word exposure certificate, a same-update decoder, or a conf-risk transfer here. A transfer would have to preserve the common source law, joint reply/successor kernel, permissions, current actual record, every individual decoded law, full-tail TV and the separate costs; matching numbers or spectra do not establish those conditions.

[A39, Propositions 39.1–39.3] fixes one real nonnegative unit-mass $L^1(\mathbb R)$ density $\rho$ and its actual Fourier difference Gram. It proves $\Re K_\rho(t_n)\to1$ if and only if $t_n\to0$; hence convergence to its specified singular target forces a collision of the first pair. A finite nonzero zero $K_\rho(T)=0$ additionally gives bounded distinct nodes whose strictly positive definite Grams tend to that same singular target, with such a zero supplied by the uniform density. These conclusions distinguish pointwise strictness from a uniform quantitative margin. They neither identify that Gram with the actual-flow table nor give a paid-history or full-tail TV comparison for this source. Here the uniform quantitative inputs are the declared exposure data (3.1) and emission bounds, while the unrestricted risk infimum remains undecided. A cross-source use of those Gram conclusions would require an explicit same-object observation map, appropriate metric bounds and the source/operation/resource correspondence above; none is assumed.

## 8. The remaining original boundary

**Boundary 8.1 (what the reduction settles).** Theorems 4.1 and 5.2 give uniform paid-history certification over arbitrary finite actual-flow tables under quantified neighborhood exposure. It applies to the original common model, actual prior and unbounded future, and after a risk-only stationary realization removes label count and period from the certificate's acquisition bound. Proposition 6.1 also identifies a missing source condition inside a fixed stationary regular example: endpoint floors do not expose an arbitrarily small separated interior mass.

**Open question 8.2 (common attainment and joint infimum).** The conf/conf alternatives remain distinct: a finite exact common optimizer; an unattained zero excess infimum; a strictly positive unrestricted gap; and minima under fixed COMPLETE, time, sampler, program or other budgets. No alternative is selected here. A next source-specific route is to prove an all-shape lower bound for one of the actual finite-query functionals $K_n$, or to supply one finite stationary same-update table with a complete all-positive-history endpoint certificate. Corollary 5.3 explains the consequence of such a lower bound but does not produce it. Under a prescribed hard defect budget one must additionally control phase-conditioning weights; Lemma 2.2 cannot discard that obligation. The existence of different feasible finite tables at arbitrarily fine certificate levels still does not give one finite shape at all levels.

[ST]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md
[PH]: https://github.com/the-omega-institute/trureturing/blob/720df794e9458ea3f6aa6319a2d7fe67d53c1a27/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md
[FLOW]: https://github.com/the-omega-institute/trureturing/blob/f165cf2ce07205f272210bc7d0b7c0669a6c2782/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FLOW_PRESERVING_RATIONAL_FRONTIER.md
[CLIP]: https://github.com/the-omega-institute/trureturing/blob/720df794e9458ea3f6aa6319a2d7fe67d53c1a27/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md
[EA]: https://github.com/the-omega-institute/trureturing/blob/720df794e9458ea3f6aa6319a2d7fe67d53c1a27/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_ACQUISITION_HORIZON.md
[FIB-H]: https://github.com/the-omega-institute/trureturing/blob/720df794e9458ea3f6aa6319a2d7fe67d53c1a27/docs/develop/theory/AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md
[FIB-I]: https://github.com/the-omega-institute/trureturing/blob/720df794e9458ea3f6aa6319a2d7fe67d53c1a27/docs/develop/theory/AURIC_FIB_ATOM_INTRINSIC_CLASSIFICATION_AND_POLYGON_GEOMETRY.md
[KB]: https://github.com/the-omega-institute/trureturing/blob/720df794e9458ea3f6aa6319a2d7fe67d53c1a27/docs/develop/theory/KBONACCI_FULL_POSITIVE_WINDOW_LOGARITHMIC_PRICE.md
[PR]: https://github.com/the-omega-institute/trureturing/blob/99c08e6f10d17be91e94ba53829b5cdcec75570f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROMISED_RISK_HISTORY_LOCALIZATION.md
[A39]: https://github.com/the-omega-institute/trureturing/blob/bce8d6d3d3f597f6ab9d70c06821cfab552aae69/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md
[CF]: https://github.com/the-omega-institute/trureturing/blob/3031ca0f03784e99dcd0ca57c5b13d8840955d4d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CERTIFIED_FADING_MEMORY_ACQUISITION.md
[GO]: https://hal.science/hal-00456538v3/document
[CK]: https://arxiv.org/pdf/1405.2852v1

## 追加锚（本行以下为增补区）
