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

## 9. Positive-tolerance aggregation of one stationary actual circulation

**Definition 9.1 (cells, centroids and the tolerance shape).** Work with one period-one regular table of Definition 2.1 on the source and full original operation contract of Definitions 1.1–1.3. Write its positive-row labels as $X,Y$, its rows as $\pi,\tau$, and its complete raw laws as $Q_x,W_y$. Zero-row labels can be deleted: $\pi B=\tau$ and $\tau A=\pi$, with nonnegative entries, exclude transitions from a positive-row label into a zero-row label.

For a rational $0<t\le1$, put

$$
\lambda=4/15,\qquad
L=\min\{\ell\ge1:\lambda^\ell\le t/2\},\qquad
G=\left\lceil\frac{2L+2}{t}\right\rceil,\qquad \xi=1/G,
\tag{9.1}
$$

$$
N_p(t)=(G+1)^{2L+1},\qquad
N_\beta(t)=(G+1)^{2L+2}.
\tag{9.2}
$$

The level-$L$ vectors of Definition 5.1 have $2L+1$ p coordinates and $2L+2$ suspended coordinates, including their residual cell. Partition $X$ into cells $C$ by equality of the coordinatewise vector $\lfloor Gz_x^{p,L}\rfloor$, and partition $Y$ into cells $D$ using $\lfloor Gz_y^{\beta,L}\rfloor$. Let $\mathcal C,\mathcal D$ be the occupied cells. Define their positive weights and analysis-only centroids by

$$
\bar\pi_C=\sum_{x\in C}\pi_x,\quad
\bar\tau_D=\sum_{y\in D}\tau_y,\quad
\bar Q_C=\sum_{x\in C}\frac{\pi_x}{\bar\pi_C}Q_x,\quad
\bar W_D=\sum_{y\in D}\frac{\tau_y}{\bar\tau_D}W_y.
\tag{9.3}
$$

These centroids are not assigned as decoders of a replacement observer. All vectors, bins and rows in this definition are mathematical construction data.

**Theorem 9.2 (uniform label cap with exact acquired flow and generated decoders).** For every allowed installed finite or countable prior, every finite stationary regular table $M$, and every $t$ of Definition 9.1, there is one stationary regular table $\widehat M$ with at most $N_p(t),N_\beta(t)$ labels. It uses the same original source, histories, complete control, records, permissions and event rendering. Its acquired rows satisfy both flow identities exactly; every individual decoder is generated by its own emissions and the same acquired-letter kernels. Put

$$
a_p(t)=\frac{14}{11}t+\frac{25}{44}\xi,\qquad
a_\beta(t)=\frac{10}{11}t+\frac{21}{44}\xi,\qquad a(t)=a_p(t).
\tag{9.4}
$$

Writing $\widehat Q_C,\widehat W_D$ for its generated complete raw laws,

$$
\max_C\operatorname{TV}(\widehat Q_C,\bar Q_C)\le a_p(t),\qquad
\max_D\operatorname{TV}(\widehat W_D,\bar W_D)\le a_\beta(t).
\tag{9.5}
$$

At every original positive history $h\in\mathcal H_s$, the same two installed tables obey

$$
|e_{\rm law}(h;\widehat M)-e_{\rm law}(h;M)|\le a_s(t),
\tag{9.6}
$$

$$
-(t+a_s(t))\le
 e_{\rm conf}(h;\widehat M)-e_{\rm conf}(h;M)
 \le a_s(t).
\tag{9.7}
$$

These bounds also hold when both measures in every TV are pushed to any common finite future partition. In particular all four complete phase risks are compared simultaneously; each new configuration risk increases by at most $a_s(t)$. No marginalized-coherence constraint is imposed.

Since $\xi\le t/4$, one has $a(t)\le249t/176$ and $t+a(t)\le425t/176$. Thus for any rational desired accuracy $\epsilon>0$, choosing $t=\min\{1,176\epsilon/425\}$ supplies one table comparing all four per-history losses within $\epsilon$. Choosing $t=\min\{1,176\epsilon/249\}$ bounds their one-sided increase and the infimum correction below by $\epsilon$.

Proof. First establish the cell diameters on the complete carriers. Every vector coordinate is in $[0,1]$, so there are at most $G+1$ bins per coordinate. Two vectors in the same cell differ by at most $\xi$ in each coordinate. Their partition TV is at most $(L+1/2)\xi$ at p and $(L+1)\xi$ at suspension. Both are at most $t/2$ by (9.1). From every old label the residual masses are at most $\lambda^L$ and $(2/5)\lambda^L$, respectively, by the regular survival bound in Theorem 5.2. Refining the residual cell increases TV by at most the smaller residual mass. Hence the complete-law diameter of every cell is at most $t$. Convexity gives

$$
\operatorname{TV}(Q_x,\bar Q_C)\le t\ (x\in C),\qquad
\operatorname{TV}(W_y,\bar W_D)\le t\ (y\in D).
\tag{9.8}
$$

The p coordinate of the completed word $\alpha$ is exactly $u_x$. The suspended coordinate of the completed word $\beta$ is exactly $1-v_y$. Thus the emission range inside each cell has width at most $\xi$.

Average the two actual edge flows, separately and without synthetic likelihood weights:

$$
\widehat B_{CD}=
\frac{\sum_{x\in C,y\in D}\pi_xB_{xy}}{\bar\pi_C},\qquad
\widehat A_{DC}=
\frac{\sum_{y\in D,x\in C}\tau_yA_{yx}}{\bar\tau_D},
\tag{9.9}
$$

$$
\bar u_C=\frac{\sum_{x\in C}\pi_xu_x}{\bar\pi_C},\qquad
\bar v_D=\frac{\sum_{y\in D}\tau_yv_y}{\bar\tau_D}.
\tag{9.10}
$$

Both kernels are row-stochastic and both emission vectors remain in $[1/3,2/5]$. Their column sums, weighted by the corresponding row, are

$$
(\bar\pi\widehat B)_D
=\sum_{y\in D}(\pi B)_y=\bar\tau_D,\qquad
(\bar\tau\widehat A)_C
=\sum_{x\in C}(\tau A)_x=\bar\pi_C.
\tag{9.11}
$$

This is one common acquired circulation, not two independently chosen phase witnesses.

Install $\bar\pi$ as the source-independent private sampling row in the same third-completion update, after the original record write and latch. Before that update keep the original control and fair synthesis; thereafter use $\widehat B$ after p-$\beta$ and $\widehat A$ after suspended-$\alpha$, with emissions $\bar u,\bar v$. Completing letters clear the labels and perform the original pendingStop transition. Definition 2.1 and Lemma 2.1.1 then give the full-domain observer. More explicitly, its update is the product of the original $C_0$ update and this finite private update, so projection preserves each original event block and enabled menu. All rejected seed pairs remain paid, both accepted seeds and every marker triple remain, and every record is written, held and delivered by its original rule. No source depth is redrawn.

Define $\widehat Q,\widehat W$ as the complete laws generated by this installed table. For a probability law $H$, let $\alpha H,\beta H$ denote prefixing the indicated next Read and let $\delta_w$ be point mass at a complete raw word. The old and new generators satisfy

$$
Q_x=u_x\delta_\alpha+(1-u_x)\beta\sum_yB_{xy}W_y,
\quad
W_y=(1-v_y)\delta_\beta+v_y\alpha\sum_xA_{yx}Q_x,
\tag{9.12}
$$

$$
\widehat Q_C=\bar u_C\delta_\alpha+
 (1-\bar u_C)\beta\sum_D\widehat B_{CD}\widehat W_D,
\quad
\widehat W_D=(1-\bar v_D)\delta_\beta+
 \bar v_D\alpha\sum_C\widehat A_{DC}\widehat Q_C.
\tag{9.13}
$$

Each p return has survival probability at most $\lambda$, in both generators and irrespective of sampled labels. Therefore all their legal infinite noncompletion outcomes have zero mass. The carriers still include these outcomes; no law has been conditioned on eventual completion. Finite-word expansion and this vanishing residual mass determine the complete generated laws. On every full record fiber $c$, rendering by $I_c$ preserves TV and the next-operation identities, including the matching Stop and unique delivery. At all retained operation cuts the exact identity is $D_z(xE)=q_z(x)\sum_{z'}P_x(z,z')D_{z'}(E)$, with the installed acquired kernel $P_x$ itself.

The centroids need not satisfy (9.13). The following estimate controls the missing covariance rather than discarding it. For weights $w_i$ summing to one, probabilities $e_i$ of range width at most $\xi$, their mean $\bar e$, and arbitrary probability laws $H_i$, the signed measure has total mass zero and

$$
\left\|\sum_iw_i(e_i-\bar e)H_i\right\|_{\rm TV}
\le\frac12\sum_iw_i|e_i-\bar e|\le\frac\xi4.
\tag{9.14}
$$

Here $\|\sigma\|_{\rm TV}=\frac12\sum_\omega|\sigma(\omega)|$ for a zero-mass signed measure on the complete countable carrier. The first inequality is the triangle inequality. For the second, if $e_i\in[b,c]$ with mean $m$, convexity of $|e-m|$ bounds its expectation by $2(m-b)(c-m)/(c-b)\le(c-b)/2$; the zero-width case is zero.

In the $\pi$-conditional average of the first equation of (9.12), replace $W_y$ by $\bar W_{D(y)}$. By (9.8) this costs at most $(2/3)t$. The resulting successor law for label $x$ is $H_x=\sum_yB_{xy}\bar W_{D(y)}$. Replacing its factor $1-u_x$ by $1-\bar u_C$ costs at most $\xi/4$ by (9.14). The remaining unweighted conditional average of $H_x$ is exactly $\sum_D\widehat B_{CD}\bar W_D$ by (9.9). Consequently

$$
\operatorname{TV}\left(\bar Q_C,
 \bar u_C\delta_\alpha+(1-\bar u_C)\beta
 \sum_D\widehat B_{CD}\bar W_D\right)
\le\frac23t+\frac\xi4.
\tag{9.15}
$$

In the $\tau$-conditional average of the second equation of (9.12), replacing $Q_x$ by $\bar Q_{C(x)}$ costs at most $(2/5)t$. Replacing $v_y$ by $\bar v_D$ costs at most $\xi/4$, again using (9.14); its unweighted successor average is $\sum_C\widehat A_{DC}\bar Q_C$. Thus

$$
\operatorname{TV}\left(\bar W_D,
 (1-\bar v_D)\delta_\beta+\bar v_D\alpha
 \sum_C\widehat A_{DC}\bar Q_C\right)
\le\frac25t+\frac\xi4.
\tag{9.16}
$$

Let $d_p,d_\beta$ be the two maxima in (9.5). Prefixing is an isometry on measures and mixture formation contracts TV. Subtracting (9.13) from (9.15)–(9.16) yields

$$
d_p\le\frac23t+\frac\xi4+\frac23d_\beta,
\qquad
d_\beta\le\frac25t+\frac\xi4+\frac25d_p.
\tag{9.17}
$$

Substitution leaves $1-(2/3)(2/5)=11/15>0$ and gives precisely $d_p\le a_p(t),d_\beta\le a_\beta(t)$. This proves (9.5) for the new own-generated laws.

Conditional on any original acquired fourth-segment word, the old private row is $\pi$ or $\tau$ and the new one is $\bar\pi$ or $\bar\tau$. At the first p cut this is the independent latch rule. At every subsequent suspended or returned p cut it follows by induction from the respective flow identities (2.1) and (9.11). Acquired letters do not reweight private rows by synthetic emissions. The source posterior, all paid counts and the full current $C_0(h)$ are therefore the same in the two models; no posterior is installed in either. The original target $T_h^\mu$ is identical.

For any target law $T$ on the current raw phase carrier, the old marginal law equals $\sum_C\bar\pi_C\bar Q_C$, and its new counterpart is $\sum_C\bar\pi_C\widehat Q_C$. Their TV is at most $a_p(t)$, proving (9.6) at p. For the configuration order, convexity before taking the configuration average gives

$$
\sum_C\bar\pi_C\operatorname{TV}(\widehat Q_C,T)
\le\sum_x\pi_x\operatorname{TV}(Q_x,T)+a_p(t).
\tag{9.18}
$$

Conversely (9.8) and (9.5) give $\operatorname{TV}(Q_x,\widehat Q_{C(x)})\le t+a_p(t)$; averaging the triangle inequality proves the other side of (9.7). Replacing $\pi,Q$ by $\tau,W$ gives the suspended assertions with $a_\beta(t)$. These arguments hold for every $T$, in particular the unchanged posterior target at every original positive history. They also hold after any common finite partition, by contraction of TV. Applying $I_{C_0(h)}$ preserves them on the complete transcript. Taking phase suprema completes the risk assertions. ∎

**Proposition 9.3 (soft marginalized-defect control).** The tables of Theorem 9.2 satisfy

$$
|\Delta_{\rm all}(\widehat M)-\Delta_{\rm all}(M)|
\le4t+2\xi.
\tag{9.19}
$$

This permits positive defect in both tables and does not preserve a prescribed closed hard-defect budget.

Proof. The global p-$\beta$ probability $q=\pi(1-u)=\bar\pi(1-\bar u)\ge3/5$ and suspended-$\alpha$ probability $b=\tau v=\bar\tau\bar v\ge1/3$ are unchanged exactly. The two p forecasts have identical mass on the completing word $\alpha$; their TV is $q$ times the TV between their p-$\beta$ residuals. By (9.5) that residual comparison is at most $(5/3)a_p$. Their actual successor forecasts differ by at most $a_\beta$. The difference between the two p-$\beta$ defects is therefore at most $(5/3)a_p+a_\beta$. The suspended forecasts have identical mass on the completing word $\beta$, so the analogous defect difference is at most $3a_\beta+a_p$. These are the only potentially nonzero defects: earlier synthesis is fair with its own latch sampler, and completing, pending and delivered transitions have the identical deterministic residuals, as in Theorem 5.2. Both models have stationary rows at every active history. The maximum of the two differences bounds the difference of their defect suprema. Substitution from (9.4) gives

$$
\frac53a_p+a_\beta=\frac{100}{33}t+\frac{47}{33}\xi,
\qquad 3a_\beta+a_p=4t+2\xi,
$$

with the second no smaller. No emission–successor independence or covariance equality has been assumed. ∎

## 10. Error-corrected bounded-shape certificates for the unrestricted infimum

**Definition 10.1 (one padded tolerance shape).** Let $\mathfrak S_{\mu,t}$ be the period-one regular tables with exactly $N_p(t),N_\beta(t)$ labels, allowing zero actual weights, on the same installed prior and original contract. Every smaller table pads to this single shape by adding labels of zero row weight, placing no transition from an active label into them, and choosing arbitrary stochastic rows and regular emissions for the new inactive labels. The padding changes no actual positive-history risk. It defines own-generated decoders on the inactive labels as well. Write

$$
J_t=\min_{M\in\mathfrak S_{\mu,t}}
 \max\{R_{{\rm conf},p}(M)-\rho_p,
        R_{{\rm conf},\beta}(M)-\rho_\beta\}.
\tag{10.1}
$$

The minimum exists by the fixed-shape continuity and compactness in [CLIP, Proposition 6.3], with no defect restriction or optional exact-endpoint constraints. As in Corollary 5.3, $J_S$ denotes the infimum over all finite stationary shapes.

**Corollary 10.2 (a bounded shape with the necessary correction).** For every allowed prior and every rational $0<t\le1$,

$$
0\le J_t-J_S\le a(t),\qquad
\max\{0,J_t-a(t)\}\le J_S\le J_t.
\tag{10.2}
$$

For the exposure certificates, original actual witness families and future levels of Corollary 5.3, set $c_n=\max_sE_{s,n}+(6/25)^{L_n}$ and let

$$
k_{n,t}=\min_{M\in\mathfrak S_{\mu,t}}
 \max\{A_{{\rm conf},p,L_n}(M)-\rho_p,
        A_{{\rm conf},\beta,L_n}(M)-\rho_\beta\}.
\tag{10.3}
$$

This is the same finite-query functional defining $K_n$, restricted to the padded tolerance shape. Then

$$
K_n\le k_{n,t}\le K_n+a(t),\qquad
\max\{0,k_{n,t}-a(t)\}\le J_S\le k_{n,t}+c_n,
\tag{10.4}
$$

and its transfer to the original full observer class is

$$
\frac{11}{61}\max\{0,k_{n,t}-a(t)\}
\le J(\mathfrak M_\mu)\le k_{n,t}+c_n.
\tag{10.5}
$$

In particular a rigorous bounded-shape certificate $k_{n,t}\ge a(t)+c$, $c>0$, proves the unrestricted full-class gap $J(\mathfrak M_\mu)\ge11c/61$. No positive certificate value is supplied by these inequalities alone.

Proof. The padded-shape class is contained in the union of all finite stationary shapes, so $J_S\le J_t$. For any stationary table, Theorem 9.2 bounds the increase of its two configuration risks by $a(t)$, and padding does not change them. Taking its infimum proves $J_t\le J_S+a(t)$, without assuming attainment of $J_S$. The separate phase minima give $J_S\ge0$.

For (10.4), inclusion gives $K_n\le k_{n,t}$. The finite-partition assertion of Theorem 9.2 applies to every history in the same $\mathcal W_p,\mathcal W_\beta$ used in $K_n$, with the same actual target. Its one-sided configuration error bounds the increase of this functional by $a(t)$. Taking the unrestricted shape infimum gives $k_{n,t}\le K_n+a(t)$. Corollary 5.3 gives $K_n\le J_S\le K_n+c_n$, yielding both corrected bounds. The fixed finite-history functional is continuous on the compact padded-shape table space, so its stated minimum exists. Finally (2.6) gives $(11/61)J_S\le J(\mathfrak M_\mu)\le J_S$, proving (10.5). The lower certificate subtracts the shape-aggregation error before applying the full-class comparison factor. ∎

**Corollary 10.3 (finite polynomial certificates and their positive-gap completeness).** On the padded shape of Definition 10.1, let $j_{t,T}$ be the finite pure-target partition minimum of [CLIP, Proposition 6.3], with future level $T$ independent of the aggregation level $L$. Use the whole supported parameter set for finite support. For infinite support use its finite set $S_T$ including the limiting parameter, as in [CLIP, Proposition 5.3]. With $b_0=6/25$, put

$$
e_T=\max\{b_0^T+\zeta_{p,T},(2/5)b_0^T+\zeta_{\beta,T}\},
\tag{10.6}
$$

where $\zeta_{s,T}=0$ for finite support and the supplied support-net errors apply otherwise. Omitting all defect restrictions and optional exact-endpoint constraints, one has

$$
\max\{0,j_{t,T}-a(t)\}\le J_S\le j_{t,T}+e_T,
\tag{10.7}
$$

$$
\frac{11}{61}\max\{0,j_{t,T}-a(t)\}
\le J(\mathfrak M_\mu)\le j_{t,T}+e_T.
\tag{10.8}
$$

A strictly positive full-class gap exists if and only if some $t,T$ satisfy $j_{t,T}>a(t)$. The same equivalence holds with $k_{n,t}>a(t)$ for some $n,t$ and the certificate sequence of Corollary 5.3. For a supplied finite exact support, finite polynomial minima and these brackets give a computable stationary infimum $J_S$, and a semidecision of a positive full-class gap. They give no decision between finite endpoint attainment and an unattained zero infimum.

Proof. The fixed-shape supplier gives $0\le J_t-j_{t,T}\le e_T$. Combining this with (10.2) proves (10.7), and (2.6) proves (10.8). Because $G\ge(2L+2)/t$, $\xi\le t/(2L+2)\le t/4$; hence $a(t)\to0$ as $t\downarrow0$. If $J(\mathfrak M_\mu)>0$, (2.6) gives $J_S>0$. Choose $t$ with $a(t)<J_S/3$ and then $T$ with $e_T<J_S/3$. The supplier implies $j_{t,T}\ge J_t-e_T\ge J_S-e_T>a(t)$. Conversely $j_{t,T}>a(t)$ gives a positive lower bound in (10.8). Replacing $e_T,j_{t,T}$ by $c_n,k_{n,t}$ and using $k_{n,t}\ge K_n\ge J_S-c_n$ proves the second equivalence.

For a finite supplied support the target parameters are rational Fibonacci ratios. Each table's finite-word probabilities are finite products of the same flow and emission variables. Absolute values in the finite configuration losses can be represented by bounded auxiliary variables, so the compact minimization is a finite semialgebraic problem with rational coefficients, exactly as in [CLIP, Definition 6.1 and Proposition 6.3]. Decision and elimination over real closed fields give rational enclosures for its minimum to any prescribed accuracy. Choosing $a(t)+e_T$ below that accuracy makes (10.7) an approximation of $J_S$. The enumeration of positive rational tolerances, future levels and increasingly precise enclosures detects a positive full-class gap by the proved equivalence. Positive masses at all supplied support points suffice; their numerical values are not used in this pure-target functional, by (2.3). For an opaque countable support, the semantic inequalities remain valid, but numerical use requires effective certified support nets or the represented actual-history targets of (10.3). Neither is supplied by an unspecified prior. This is not a practical running-time bound, nor an effective sampler assertion for arbitrary real minimizing entries. ∎

**Proposition 10.4 (scope of semantic compression and resource separation).** The bound (9.2) controls the number of private labels at the original returned p and suspended cuts. A generous bound before sampler expansion is $|C_0|(1+N_p(t)+N_\beta(t))$ returned-cut configurations. It is not a bound on COMPLETE after all represented service microstates, on installed numerical precision, program size, workspace, acquisition length, random-bit supply, synthetic output length or total work. No original fixed resource budget is preserved. The family of tolerance bounds supplies neither one finite exact endpoint table nor a zero-excess family, unless the corresponding remaining mathematical obligations are proved separately.

Proof. The construction retains only a sampled cell label and the complete original $C_0$ at an operation cut. It retains no acquired count, history, source posterior, analysis row, binning vector, centroid or external clock. All original acquired Reads, seed rejections, records and legal return words remain. The original source provider and its one common-depth draw have their own resources. Synthetic generation uses the same finite private kernels without an actual Read or a post-Stop operation.

For a represented rational input table, finite-word vectors and the cell construction use exact rational arithmetic, and (9.9)–(9.10) give rational replacement entries. A rational categorical row admits a finite candidate-bit and cursor sampler with rejection, finite installed thresholds and finite reuse of workspace. Every candidate, cursor, row selector, PC, address, threshold, event cursor, original record and service microstate belongs to its charged program/carrier; installation, offline aggregation and certificate evaluation have their own costs. Rejection may use unboundedly many fresh bits and microsteps, with all actual use charged. The same represented sampler is used in acquired and synthetic updates. Legal arbitrarily long return words and synthesis outputs exclude a finite worst-case total length or work bound. Arbitrary real tables assert only abstract stochastic rules; the label cap supplies no digital representation for their constants.

Finally $N_p(t),N_\beta(t)$ are tolerance-dependent bounds. The quantifier proved is $\forall t>0\,\forall M\,\exists\widehat M_t$ with the stated approximation, not $\exists$ one bounded shape realizing all tolerances or the exact endpoint. Corollaries 10.2–10.3 supply corrected certificate implications but no evaluated positive margin or table attaining either endpoint. The finite endpoint, unattained zero infimum, positive gap and fixed-budget alternatives of Open question 8.2 therefore remain distinct. No physical spacetime, exact posterior or chronology recovery follows from a TV approximation of these phase laws. ∎

**Mathematical correspondence 10.5 (source-specific increment).** Theorem 9.2 and the corrected all-shape certificate consequences are repo-derived. The stopped laws, complete record rendering, regular survival estimate, stationary risk reduction and fixed-shape polynomial minima are the suppliers in Definitions 1.1–2.1, Corollary 2.3, Theorem 5.2 and [CLIP, §§5–6]. Their content is reused rather than counted as a new phase optimum. The elementary convexity and contraction estimates occur inside the new joint proof.

The exact quotient in [CF, Proposition 7.2] assumes identical complete decoded measures and strong lumpability to preserve arbitrary acquired rows. Theorem 9.2 uses stationary-weighted actual edge flows, allows unequal laws and nonlumpable rows, and explicitly bounds the covariance in the new generated laws. It proves the comparison for the installed stationary rows on every original positive history; it is not a pathwise quotient for arbitrary private initial rows. [FLOW] rationalizes a supplied finite shape and [CLIP, Proposition 6.3] certifies one fixed shape. The additional bridge here bounds the replacement shape solely by positive accuracy before those certificates are transferred to the unbounded union. [CK, Theorem 7 and Corollary 8] supplies approximation for a fixed pair of represented labeled Markov chains, not this label cap or an all-shape lower bound. The actual-history-average consumer likewise does not replace the phase suprema in (10.1)–(10.3). These correspondences establish the scope of the derivation, not a claim of global literature priority.

## 追加锚（本行以下为增补区）

## 11. One rational common table with uniformly small positive excess

**Definition 11.1 (the common two-label table).** On the original source, control and complete future of Definitions 1.1–1.3, use a period-one table with $X=Y=\{0,1\}$ and

$$
\begin{gathered}
D=300000000,\qquad b=\frac{22306}{D},\qquad
\pi=\tau=(1/2,1/2),\\
B=\begin{pmatrix}1-b&b\\b&1-b\end{pmatrix},\qquad
A=\begin{pmatrix}1&0\\0&1\end{pmatrix},\\
u=\frac1D\begin{pmatrix}100003966\\119995354\end{pmatrix},\qquad
v=\frac1D\begin{pmatrix}100005451\\119995552\end{pmatrix}.
\end{gathered}
\tag{11.1}
$$

Before the third latch retain the full original $C_0$ and use fair synthetic letters. The original third-completion update first writes the whole record and latches it, then independently samples the fair private label. After an acquired p-$\beta$ apply $B$; after an acquired suspended-$\alpha$ apply $A$. Synthetic generation uses the same two update kernels with the emissions $u,v$. Completing letters clear the private label and retain the original pendingStop and all held records. Only the original matching Stop and delivery follow. The table is fixed independently of the prior, source depth, acquired word, seed and record fiber.

Put $U=\operatorname{diag}(1-u)$, $V=\operatorname{diag}(v)$,

$$
H=UBV,\qquad g=UB(\mathbf1-v).
\tag{11.2}
$$

For $j\ge0$ the raw complete decoded laws are

$$
\begin{aligned}
Q_i(w_{j,0})&=(H^ju)_i,& Q_i(w_{j,1})&=(H^jg)_i,\\
W_i(\beta)&=1-v_i,& W_i(\alpha w_{j,c})&=v_iQ_i(w_{j,c}).
\end{aligned}
\tag{11.3}
$$

Both carriers retain their legal infinite noncompletion outcome. Each full configuration uses its own current-record map $I_c$ to insert the complete original event blocks. No acquired suspended letter is inserted a second time into its future.

**Theorem 11.2 (uniform conf/conf certificate and witness nonattainment).** For every finite or countable installed prior with $\mu(1),\mu(2)>0$, Definition 11.1 gives one finite rational same-update observer $M_\mu$ such that, on all the original positive acquired histories in both fourth phases,

$$
R_{{\rm conf},s}(M_\mu)-\rho_s
<\frac{109986166}{10^{15}}<\frac{11}{100000000},
\qquad s=p,\beta.
\tag{11.4}
$$

The law-order risks of this same observer obey the corresponding upper bounds. In the notation of Corollary 2.3,

$$
0\le J(\mathfrak M_\mu)\le J(\mathfrak S_\mu)
\le \max_s\{R_{{\rm conf},s}(M_\mu)-\rho_s\}
<\frac{11}{100000000}.
\tag{11.5}
$$

This particular witness does not attain the two minima:

$$
R_{{\rm conf},p}(M_\mu)-\rho_p
>\frac{109467}{10^{12}}>\frac1{10000000}.
\tag{11.6}
$$

Its individual same-update generation is exact, while its marginalized suspended-$\alpha$ defect is strictly greater than $3/1000$. No hard defect bound or fixed COMPLETE resource budget is a premise of (11.4).

Proof. All four emissions lie in $[1/3,2/5]$. The matrix $B$ is doubly stochastic and $A$ is the identity, so

$$
\pi B=\tau,\qquad \tau A=\pi.
\tag{11.7}
$$

The independent latch row and induction over the actual noncompleting letters keep the acquired private row exactly fair at every original p and suspended history. Actual acquired letters come from the same installed $K$, independently of the private random choices. Thus this induction uses the unweighted actual kernels $B,A$, without reweighting by the synthetic emissions. It holds on every seed and complete-record fiber and after every finite number of returns.

For synthetic generation, the two phase equations are instead

$$
\begin{aligned}
Q_i&=u_i\delta_\alpha+(1-u_i)\,\beta\sum_tB_{it}W_t,\\
W_i&=(1-v_i)\delta_\beta+v_i\,\alpha Q_i.
\end{aligned}
\tag{11.8}
$$

Here prefixing denotes prefixing the raw word, with its original events subsequently supplied by $I_c$. Expanding (11.8) gives precisely (11.2)–(11.3). In particular both laws are produced by this same installed table, rather than assigned separately to the phases. The identity

$$
u+g+H\mathbf1=\mathbf1,
\qquad H\mathbf1\le\frac4{15}\mathbf1
\tag{11.9}
$$

shows that the total p mass completed before $L$ returns is $\mathbf1-H^L\mathbf1$. The residual tends to zero geometrically, so every $Q_i$ is normalized. Equation (11.8) then normalizes $W_i$. Infinite noncompletion remains an outcome of mass zero; neither law is conditioned on completion. Before the latch, fair seed-pair rejection and payload-return survival also decay geometrically, as in Lemma 2.1.1. Pending and delivered configurations have the original deterministic Stop/delivery and empty future. This establishes individual generation on the entire original retained carrier.

It remains to bound the two pure-target configuration errors, using the actual fair rows. Set $L=16$. On the complete-word partitions of Definition 5.1 let

$$
\begin{aligned}
q_i&=\bigl((H^ju)_i,(H^jg)_i\ (0\le j<16);\ (H^{16}\mathbf1)_i\bigr),\\
w_i&=\bigl(1-v_i;\ v_iq_i\bigr),\\
t_p(r)&=\bigl(ra_r^j,(1-r)^2a_r^j\ (0\le j<16);\ a_r^{16}\bigr),\\
t_\beta(r)&=\bigl(1-r;\ rt_p(r)\bigr).
\end{aligned}
\tag{11.10}
$$

Each vector is normalized, including its single residual cell. Denote their finite configuration errors by

$$
F_{p,16}(r)=\frac14\sum_{i=0}^1\|q_i-t_p(r)\|_1,
\qquad
F_{\beta,16}(r)=\frac14\sum_{i=0}^1\|w_i-t_\beta(r)\|_1.
\tag{11.11}
$$

The factors retain configuration averaging outside TV.

The following integer expressions specify the finite rational certificate. Write $\widehat u=D u$, $\widehat v=D v$, $\widehat B=DB$, and define the integer matrix $\mathsf H$ and column $\mathsf g$ by

$$
\mathsf H_{it}=(D-\widehat u_i)\widehat B_{it}\widehat v_t,\qquad
\mathsf g_i=(D-\widehat u_i)\sum_t\widehat B_{it}(D-\widehat v_t).
\tag{11.12}
$$

Thus $H=\mathsf H/D^3$, $g=\mathsf g/D^3$, and the decoder coordinates in (11.10) are exactly

$$
q_i(w_{j,0})=\frac{(\mathsf H^j\widehat u)_i}{D^{3j+1}},\qquad
q_i(w_{j,1})=\frac{(\mathsf H^j\mathsf g)_i}{D^{3j+3}},\qquad
q_i(*)=\frac{(\mathsf H^{16}\mathbf1)_i}{D^{48}}.
\tag{11.13}
$$

Here $*$ is the residual cell. The integer numerators in (11.12) are

$$
\mathsf H=\begin{pmatrix}
5999761938043440825963796&535313541104374971008\\
401540250133587167876&6479445253623873282590848
\end{pmatrix},\qquad
\mathsf g=\begin{pmatrix}
11999345808415454799065196\\9720571346125993130241276
\end{pmatrix}.
\tag{11.14}
$$

Powers can equivalently be expressed by $\mathsf H^0=I$ and $\mathsf H^{j+1}=\mathsf H^j\mathsf H$. For $r=e/f$, the two target p coordinates are the integers $e^{j+1}(f-e)^j$ and $e^j(f-e)^{j+2}$ divided by $f^{2j+1}$ and $f^{2j+2}$ respectively; the residual is $[e(f-e)]^{16}/f^{32}$. The suspended coordinates follow by multiplying by $e/f$ and adjoining $1-e/f$. All denominators are positive.

Put $I_0=[3/8,5/13]$, $E_p=\{w_{0,1},w_{1,1},w_{2,1}\}$ and $E_\beta=\{\beta,\alpha w_{0,1}\}$. Substitution in (11.13) at each of the two rational boundaries of $I_0$ gives the following strict chains; every adjacent gap in these chains exceeds $11/10^{12}$:

| Phase and cell | Chain at $r=3/8$ and at $r=5/13$ |
| --- | --- |
| p, $z\in E_p$ | $q_0(z)>t_p(r)(z)>q_1(z)$ |
| p, $z=w_{3,1}$ | $t_p(r)(z)>q_1(z)>q_0(z)$ |
| p, every other distinguished cell and $*$ | $q_0(z)<t_p(r)(z)<q_1(z)$ |
| suspended, $z\in E_\beta$ | $w_0(z)>t_\beta(r)(z)>w_1(z)$ |
| suspended, every other distinguished cell and $*$ | $w_0(z)<t_\beta(r)(z)<w_1(z)$ |

These are 134 finite cell chains with explicit integer expressions (11.12)–(11.14), comprising 268 positive differences. Each inequality is a positive-denominator integer comparison, including the residual cells.

To pass from the two rational boundaries to every $r\in I_0$, a target coordinate of the form $r^a(1-r)^c$ has derivative with sign $a-(a+c)r$. For the p branch 0, $(a,c)=(j+1,j)$ and the derivative is positive throughout $I_0$. For the p branch 1, $(a,c)=(j,j+2)$; it is nonpositive for $j\le3$ and positive for $j\ge4$. Its only boundary turning point is $3/8$ at $j=3$; the next turning point is $2/5>5/13$. At suspension the initial $1-r$ decreases, branch 0 has $(a,c)=(j+2,j)$ and increases, and branch 1 has $(a,c)=(j+1,j+2)$, decreasing at $j=0$ and increasing for $j\ge1$. Both residuals, $a_r^{16}$ and $r a_r^{16}$, increase. Consequently every target coordinate lies between its two boundary values, and all the displayed chains hold throughout $I_0$.

For any normalized finite vectors $a,b,t$, the coordinate absolute-value identity gives

$$
\frac{\operatorname{TV}(a,t)+\operatorname{TV}(b,t)}2
=\frac{\operatorname{TV}(a,b)}2
+\frac12\sum_z\operatorname{dist}
\bigl(t_z,[\min(a_z,b_z),\max(a_z,b_z)]\bigr).
\tag{11.15}
$$

Indeed $|a_z-t_z|+|b_z-t_z|=|a_z-b_z|+2\operatorname{dist}(t_z,[\min(a_z,b_z),\max(a_z,b_z)])$ for each coordinate; summing and dividing by four proves (11.15). Applying the chains yields, throughout $I_0$,

$$
\begin{aligned}
F_{p,16}(r)&=\frac12\operatorname{TV}(q_0,q_1)
+\frac12\left[r^3(1-r)^5-q_1(w_{3,1})\right],\\
F_{\beta,16}(r)&=\frac12\operatorname{TV}(w_0,w_1).
\end{aligned}
\tag{11.16}
$$

The derivative of the variable term is $r^2(1-r)^4(3-8r)\le0$ on $I_0$. Hence the p expression is maximized at $3/8$, and the suspended expression is constant. This bounds every original depth $k\ge3$, without replacing countable support by a finite diagnostic support.

For the two original endpoints and this interval maximum, (11.10)–(11.14) give the following strict rational enclosures. Each displayed pair $(l,h)$ means $l/10^{12}<F_{s,16}(r)-\rho_s<h/10^{12}$.

| $r$ | p enclosure $(l,h)$ | suspended enclosure $(l,h)$ |
| --- | --- | --- |
| $1/3$ | $(109467,109468)$ | $(109092,109093)$ |
| $2/5$ | $(108109,108110)$ | $(108551,108552)$ |
| $3/8$ | $(109864,109865)$ | $(-18062232,-18062231)$ |

Together with (11.16), these positive-denominator comparisons prove

$$
\sup_{k\ge1}\{F_{s,16}(r_k)-\rho_s\}
<\frac{109865}{10^{12}},\qquad s=p,\beta.
\tag{11.17}
$$

The full-tail correction does not require extending these finite signs to unbounded $j$. Refining a residual cell with decoder and target masses $a,c$ increases TV by at most $[(a+c)-|a-c|]/2=\min(a,c)$. The target residual is $a_r^{16}\le(6/25)^{16}$ at p and $r a_r^{16}\le(2/5)(6/25)^{16}$ at suspension. Apply the inequality to each configuration and average. This is the residual argument of Theorem 5.2 and [CLIP, Theorem 5.2], with the infinite outcome included. Exactly,

$$
\left(\frac6{25}\right)^{16}<\frac{121166}{10^{15}},\qquad
\frac{109865}{10^{12}}+\frac{121166}{10^{15}}
=\frac{109986166}{10^{15}}<\frac{11}{10^8}.
\tag{11.18}
$$

For example the first comparison follows by cross multiplication of $6^{16}/25^{16}$ with its displayed rational upper bound. Equations (11.17)–(11.18) now bound both full pure-target configuration losses uniformly over all original supported depths.

At an arbitrary original positive acquired history the target is the posterior mixture (1.3), while the acquired row is still fair by (11.7). Countable target convexity gives

$$
\frac12\sum_{i=0}^1
\operatorname{TV}\left(Q_i,\sum_k\nu_h(k)P_{p,r_k}\right)
\le\sum_k\nu_h(k)\frac12\sum_{i=0}^1
\operatorname{TV}(Q_i,P_{p,r_k}),
\tag{11.19}
$$

and the suspended inequality uses $W_i$. The original current-record map $I_c$ preserves these TV comparisons and the complete next-operation event blocks. The common strict upper margin in (11.17)–(11.18) therefore bounds the suprema on all $\mathcal H_p,\mathcal H_\beta$, proving (11.4). Convexity in the decoder gives law $\le$ conf for this same model. Its membership in $\mathfrak S_\mu$, inclusion and the separate phase lower bounds prove (11.5).

For nonattainment, partitioning never increases TV, and the first p enclosure gives $F_p(1/3)-\rho_p>109467/10^{12}$. This endpoint is supported. The pure-target exposure equality (2.3), supplied by [CLIP, Proposition 2.3], thus proves (11.6). In particular its limiting endpoint error is approached by positive finite paid rejection histories of the same installed prior; it is not an error on an inaccessible reset source. No model-independent positive lower bound follows from this one-model calculation.

Finally, at a suspended cut the actual successor row after $\alpha$ is fair, but conditioning the synthetic report on $\alpha$ gives the row

$$
\eta=\frac{(v_0,v_1)}{v_0+v_1}.
$$

The two successor laws are $Q_0,Q_1$. Homogeneity of TV for their signed difference, followed by the event consisting of the immediate p completion $\alpha$, gives

$$
\begin{aligned}
\delta(h,\alpha)
&=\frac{v_1-v_0}{2(v_0+v_1)}\operatorname{TV}(Q_0,Q_1)\\
&\ge\frac{(v_1-v_0)(u_1-u_0)}{2(v_0+v_1)}
=\frac{33302488770849}{11000050150000000}>\frac3{1000}.
\end{aligned}
\tag{11.20}
$$

Thus exact individual generation has not been confused with zero marginalized defect. Also $BA=B$ is irreducible, every $v_i$ is positive, and $Q_0(\alpha)=u_0\ne u_1=Q_1(\alpha)$. The supplied native-mixture rigidity [NATIVE11, Theorem 5.1] implies that the two p laws cannot both be mixtures of the original native depth laws. That result is consumed only to locate this particular witness relative to its native-mixture subclass. ∎

**Proposition 11.3 (finite represented resources and the remaining alternatives).** The same table admits finite exact rational sampling with all original records and controls retained and all service microstates charged under COMPLETE. Its two private labels per phase are not its total COMPLETE state count. The bound (11.5) is an upper bound for the unrestricted common-model infimum, while (11.6) is a lower bound only for this witness. These conclusions select none of the finite-endpoint, unattained-zero-infimum or strictly-positive-infimum alternatives in Open question 8.2.

Proof. Every primitive probability in (11.1), including the fair latch and pre-latch emissions, has denominator $D$; deterministic updates need no random selection. Since $D<2^{29}$, a rational sampler may draw a 29-bit candidate, reject values at least $D$, and compare an accepted candidate to its finite integer thresholds. Its candidate, bit cursor, current row and label, program counter, addresses, table data, event and output cursors, and original record/control fields form finite charged storage. Repeated attempts reuse this storage and retain no unbounded retry counter. Fresh independent bits give the exact row probabilities and almost-sure return. Acquired and synthetic execution use this same represented update sampler; synthetic emission sampling makes no actual source call.

The original $C_0$ remains present before and after the latch. Both accepted seeds, every paid rejection word, the complete marker tree, every record write before its latch, held records, permissions and delivery are preserved by the product update of Lemma 2.1.1. All original positive payload-return histories and legal noncompletion futures remain. The observer keeps no additional acquired-history register, Read count, posterior, readable analysis row, external clock, source-reset service or continuous register, and pending/delivered states have no Read. Installation description and workspace, actual Reads, fresh bits, internal work, synthesis and output length, offline certificate arithmetic and the source provider's single common-depth resources are separate accounts. Random rejection and arbitrarily long legal return words preclude a finite worst-case total-bit, time or output bound. No total-resource optimum or preservation of a previously prescribed budget is inferred from the private label count.

There is one fixed positive upper witness, with a strictly positive own excess. A vanishing-excess family would require another quantified construction, a finite exact endpoint another table or proof, and a positive unrestricted gap an inequality valid over all finite shapes. None follows from an upper witness and its own lower bound. The result supplies no exact posterior or chronology recovery, physical-spacetime consequence or global completion. ∎

The table and the uniform source-specific certificate in Theorem 11.2 are repo-derived. The stopped-word laws, actual-history interpretation, stationary row condition, full record rendering, phase minima and residual-cell estimate are reused from Definitions 1.1–2.1, (2.3), Theorem 5.2 and [CLIP, §§2 and 5]. The coordinate triangle identity is the elementary intermediate step (11.15), not a separate new theorem. [CK, Theorem 7 and Corollary 8] approximates TV for a supplied pair of labeled Markov chains; it supplies neither (11.1) nor simultaneous unweighted acquired circulation and configuration-before-TV bounds on this source. The conf/law construction [SWITCH11, §3] uses suspended emissions $0,1/2$, and [MIXED11, Theorem 3.1] supplies different risk orders. Their stated attainments do not supply the regular-emission conf/conf certificate (11.4). These are bounded mathematical correspondences, without a global literature-priority or optimality claim.

[NATIVE11]: https://github.com/the-omega-institute/trureturing/blob/54dc9a9bd356fe584703022a3a4c0b0978f557de/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md
[SWITCH11]: https://github.com/the-omega-institute/trureturing/blob/54dc9a9bd356fe584703022a3a4c0b0978f557de/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONFIGURATION_LAW_SWITCH_ATTAINMENT.md
[MIXED11]: https://github.com/the-omega-institute/trureturing/blob/54dc9a9bd356fe584703022a3a4c0b0978f557de/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MIXED_PHASE_DEFECT_ATTAINMENT.md

## 追加锚（本行以下为增补区）
## 12. Either-interface complete-redraw obstruction

The next result isolates the relation that is lost when a private successor law is redrawn from a row independent of the current phase label. It uses the same complete stopped carriers and the same actual-flow table as Definitions 1.1–2.1. A redraw below is a change to the observer's finite private update kernel; it is not a reset of the source draw, the original control, a held record, or a paid history.

For a period-one table write

$$
\bar Q=\sum_x\pi_xQ_x,\qquad \bar W=\sum_y\tau_yW_y,
$$

and put

$$
L_x=\sum_yB_{xy}W_y,\qquad J_y=\sum_xA_{yx}Q_x.
$$

The complete-word events used below are

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\}.
$$

Direct substitution in the stopped laws gives

$$
\begin{aligned}
P_{p,1}(E_p)&=\frac{412}{729},&
P_{p,2}(E_p)&=\frac{7299}{15625},&
C&:=\frac{P_{p,1}(E_p)+P_{p,2}(E_p)}2=\frac{11758471}{22781250},\\
P_{\beta,1}(E_\beta)&=\frac{22}{27},&
P_{\beta,2}(E_\beta)&=\frac{93}{125},&
H&:=\frac{P_{\beta,1}(E_\beta)+P_{\beta,2}(E_\beta)}2=\frac{5261}{6750}.
\end{aligned}
$$

The half-distances of the two endpoint laws are the supplied
$\rho_p=1116529/22781250$ and $\rho_\beta=239/6750$. Also set

$$
U:=P_{p,2}(w_{3,1})=\frac{1944}{390625},\qquad
S(t):=1+t+t^2,\qquad \eta:=\frac1{100000}.
$$

**Theorem 12.1 (either-interface complete-redraw obstruction).** Let a finite period-one regular table have positive stationary rows, $\pi B=\tau$, $\tau A=\pi$, and all emissions in $[1/3,2/5]$. If either

$$
A_{yx}=\pi_x\quad\text{for every retained }y
\tag{12.1}
$$

or

$$
B_{xy}=\tau_y\quad\text{for every retained }x,
\tag{12.2}
$$

then

$$
\max\{R_{\rm law,p}-\rho_p,
       R_{\rm law,\beta}-\rho_\beta\}>\eta.
\tag{12.3}
$$

Consequently the same strict bound holds with the two configuration risks in place of the law risks. The assertion is uniform in the finite numbers of labels, in the installed finite or countable prior with $\mu(1),\mu(2)>0$, and in all positive paid histories. All complete noncompletion outcomes remain in the carrier.

**Proof.** Suppose both law excesses are at most $\eta$. The endpoint histories are included in the stationary risk formulas, so

$$
|\bar Q(E_p)-C|\le\eta,\qquad
|\bar W(E_\beta)-H|\le\eta.
\tag{12.4}
$$

For any complete law $D$ and endpoint laws $P_1,P_2$ whose distance is $2\rho$, the coordinate identity

$$
\operatorname{TV}(D,P_1)+\operatorname{TV}(D,P_2)-2\rho
 =\sum_z\operatorname{dist}\!\left(D(z),[P_1(z)\wedge P_2(z),P_1(z)\vee P_2(z)]\right)
\tag{12.5}
$$

holds, including the infinite noncompletion atom. Applying it to $\bar Q$ and the p endpoints shows

$$
\bar Q(w_{3,1})\le U+2\eta.
\tag{12.6}
$$

Assume first (12.1). Put

$$
q=\sum_x\pi_xu_x,\qquad \bar v=\sum_y\tau_yv_y,
$$

$$
t=\sum_{x,y}\pi_x(1-u_x)B_{xy}v_y,\qquad g=1-q-t.
$$

The individual same-update equations and the row-independent $A$ give the complete-law identities

$$
\bar Q=q\,\delta_\alpha+g\,\delta_{\beta\beta}
       +t\,\beta\alpha\,\bar Q,
\qquad
\bar W=(1-\bar v)\,\delta_\beta+\bar v\,\alpha\bar Q.
\tag{12.7}
$$

Thus $\bar Q(E_p)=gS(t)$ and

$$
\bar W(E_\beta)=1-\bar v+\bar vg=1-\widetilde d,
\qquad \widetilde d:=\bar v(1-g).
\tag{12.8}
$$

The actual edge law $\pi_xB_{xy}$ has marginals $\pi$ and $\tau$. Hence

$$
t=(1-q)\bar v-\operatorname{Cov}(u(X),v(Y)),
\tag{12.9}
$$

where the covariance is under that unweighted edge law. Since $1-q=g+t$,

$$
\operatorname{Cov}(u(X),v(Y))
 =\frac{(g+t)\widetilde d}{1-g}-t.
\tag{12.10}
$$

Now define $g_0(t)=C/S(t)$ and $f(t)=Ct^3/S(t)$. Equations (12.4), (12.7) and (12.8) give
$|g-g_0(t)|\le\eta$ and $\widetilde d$ differs from $d:=1-H$ by at most $\eta$. Since $0\le t\le(2/3)(2/5)=4/15$, (12.6) gives $f(t)\le U+3\eta$. The function $f$ is strictly increasing, and the exact comparison at $t_0=23191/100000$ is

$$
f(t_0)-U
 =\frac{895013545004856241}{29289676527028125000000}>3\eta.
\tag{12.11}
$$

Therefore $t<t_0$. Set

$$
D_A(t)=d\,\frac{g_0(t)+t}{1-g_0(t)}-t.
$$

On $[0,4/15]$, $g_0(t)\le C$, with equality at $t=0$ and strict inequality for $t>0$. Because $g_0'(t)<0$ and $d<1-C\le1-g_0(t)$, $D_A$ is strictly decreasing on this entire interval. The exact margin is

$$
D_A(t_0)-\frac1{900}
 =\frac{1529494301962866701}{3786740393838075000000}>3\eta.
\tag{12.12}
$$

On the interval forced by (12.4), all of $g,g_0$ are below $521/1000$ and all of $\widetilde d,d$ are below $221/1000$. Direct differentiation of the right side of (12.10) bounds the sum of the absolute partial derivatives in $g$ and $\widetilde d$ by
$1971677/688323<3$. Thus its value differs from $D_A(t)$ by less than $3\eta$, and (12.12) gives
$|\operatorname{Cov}(u(X),v(Y))|>1/900$.

For a random variable $Z\in[a,b]$, $\mathbb E[(Z-a)(b-Z)]\ge0$ gives
$\operatorname{Var}(Z)\le(b-a)^2/4$. Cauchy–Schwarz therefore gives

$$
|\operatorname{Cov}(u(X),v(Y))|\le\frac1{900},
\tag{12.13}
$$

because both emission intervals have width $1/15$. This contradiction rules out (12.1).

For (12.2), put

$$
t=\sum_{y,x}\tau_yv_yA_{yx}(1-u_x),\qquad
g=(1-q)(1-\bar v).
$$

The averaged equations are now

$$
\bar Q=q\,\delta_\alpha+(1-q)\,\beta\bar W,
\qquad
\bar W=(1-\bar v)\,\delta_\beta+(\bar v-t)\,\alpha\alpha
       +t\,\alpha\beta\,\bar W.
\tag{12.14}
$$

Consequently $\bar Q(E_p)=gS(t)$ and
$\bar W(E_\beta)=(1-\bar v)(1+t)$. Writing the latter probability as $h$, the unweighted edge law $\tau_yA_{yx}$ gives

$$
\operatorname{Cov}(v(Y),u(X))
 =g\,\frac{1+t-h}{h}-t.
\tag{12.15}
$$

The same event bounds imply $|h-H|\le\eta$ and again $t<t_0$. Define

$$
D_B(t)=g_0(t)\frac{1+t-H}{H}-t.
$$

It is strictly decreasing because $g_0'<0$ and $C/H<1$, while exact arithmetic gives

$$
D_B(t_0)-\frac1{900}
 =\frac{258121825473795701}{4930975622678238900000}>2\eta.
\tag{12.16}
$$

Here $h,H>779/1000$, and the sum of the absolute partial derivatives in $g$ and $h$ is at most $164183/95817<2$. The true expression in (12.15) therefore differs from $D_B(t)$ by less than $2\eta$. This again contradicts (12.13), and proves (12.3). The endpoint bounds used only complete events and the full coordinate identity; no tail truncation, completion conditioning, or finite prior-support reduction entered the argument. ∎

The three exact margins in (12.11), (12.12), and (12.16) are the rational certificate. They are strict after cross multiplication; no floating-point inequality is used. The endpoint cells and their midpoint coordinates agree with the full-tail separation calculation in [UNIF, §§3–5]. That source separates a larger constant-parameter mixture family from the endpoint minima. The present theorem concerns a different failure mode: a complete redraw can collapse the continuation relation even when the decoded laws are arbitrary, so it does not republish the mixture-family exclusion.

## 13. Full successor-law continuation dispersion

For a finite period-one regular stationary table (the stationary class used after the existing period reduction), define the actual-flow successor dispersions

$$
b_p:=\sum_x\pi_x\operatorname{TV}(L_x,\bar W),\qquad
b_\beta:=\sum_y\tau_y\operatorname{TV}(J_y,\bar Q).
\tag{13.1}
$$

These are TV distances between complete successor laws, including the infinite noncompletion outcome. They are weighted by the unweighted acquired flow. They are neither marginalized conditioning defects nor distances between label distributions. Splitting a label into copies with the same decoded law and proportionally split flow leaves them unchanged.

**Theorem 13.1 (quantitative continuation dispersion).** For every finite period-one regular stationary table, put

$$
e=\max\{R_{\rm conf,p}-\rho_p,
         R_{\rm conf,\beta}-\rho_\beta\}.
$$

Then

$$
e+\frac{10}{11}b_p>\eta,
\qquad
e+\frac{6}{11}b_\beta>\eta.
\tag{13.2}
$$

Consequently, for any sequence of such tables with $e_n\to0$,

$$
\liminf_n b_{p,n}\ge\frac{11}{1000000},\qquad
\liminf_n b_{\beta,n}\ge\frac{11}{600000}.
\tag{13.3}
$$

Thus a zero-excess sequence cannot erase complete-law continuation dependence at either phase interface. The conclusion permits positive marginalized defect and imposes no defect budget.

**Proof.** Replace $A$ by the row-independent kernel $A^0_{yx}=\pi_x$, keeping $B,\pi,\tau,u,v$ fixed. This preserves $\pi B=\tau$ and $\tau A^0=\pi$. Let $Q_x^0,W_y^0$ be the complete laws generated by the replacement and set

$$
d_p=\sum_x\pi_x\operatorname{TV}(Q_x,Q_x^0),\qquad
d_\beta=\sum_y\tau_y\operatorname{TV}(W_y,W_y^0).
$$

Prefixing and deleting deterministic original event blocks are TV isometries. The p equations and convexity give

$$
d_p\le\frac23d_\beta.
$$

For the suspended laws, insert the old $\bar Q$ between $J_y$ and the new $\bar Q^0$:

$$
d_\beta\le\frac25(b_\beta+d_p).
$$

Solving yields

$$
d_p\le\frac4{11}b_\beta,\qquad d_\beta\le\frac6{11}b_\beta.
\tag{13.4}
$$

At every original history the replacement has the same acquired stationary rows and the same source target. Therefore its p and suspended law risks are bounded by the old configuration risks plus $d_p$ and $d_\beta$, respectively. The maximum replacement law excess is at most $e+6b_\beta/11$. Theorem 12.1 applies to the replacement, so (13.2)'s second inequality follows.

Now replace $B$ by $B^0_{xy}=\tau_y$ and keep $A$ fixed. The same argument gives

$$
d_\beta\le\frac25d_p,\qquad
d_p\le\frac23(b_p+d_\beta),
$$

and hence

$$
d_p\le\frac{10}{11}b_p,\qquad d_\beta\le\frac4{11}b_p.
\tag{13.5}
$$

Theorem 12.1 applied to this replacement gives the first inequality in (13.2). All comparisons are between complete laws of one table and its one-kernel replacement; no two histories, phases, or independently optimized tables are combined. ∎

The replacement argument is a continuation certificate, not a claim that the original table itself has a positive risk gap. A table may have small $e$ while retaining the lower bounds in (13.3) through dispersed successor laws. Conversely, a bound on a next-letter cylinder alone would not imply (13.1), because (13.1) is a full-tail law distance.

## 14. Full-observer law-diameter noncollapse on a held-record fibre

Fix the positive paid suffix

$$
S=\beta\alpha\mid\beta\beta\alpha\alpha.
\tag{14.1}
$$

It accepts seed 1, writes the marker triple $100$, and reaches the third write-before-latch with one fixed held-record fibre. For an arbitrary finite observer $M$, let $\mathcal Z_p^*(M)$ and $\mathcal Z_\beta^*(M)$ be the unions of configurations having positive probability after some positive finite original history on this fibre, at the p and suspended cuts respectively. Pull every complete decoder back through its own current $I_c$ to the common raw carrier, so that the current deterministic record, permission, completion, Stop and delivery block is removed from the comparison. Define

$$
D_s(M)=\sup\{\operatorname{TV}(D,D'):
 D,D'\text{ are pulled-back laws from }\mathcal Z_s^*(M)\},
\qquad s\in\{p,\beta\}.
\tag{14.2}
$$

The supremum is over the union of reachable configurations across all positive finite histories on this one held-record fibre. It is not a claim that all those configurations coexist after one history.

**Lemma 14.1 (common row and held-record reachability).** All source parameters lie in the compact range $I=[1/3,2/5]$. On the fibre (14.1), every finite observer $M$ has actual kernels $B:X\to Y$, $A:Y\to X$ and probability rows $\pi,\tau$ satisfying $\pi B=\tau$, $\tau A=\pi$. For every supported depth $k$ the same two rows satisfy

$$
\sum_x\pi_x\operatorname{TV}(Q_x,P_{p,r_k})\le R_{\rm conf,p}(M),\qquad
\sum_y\tau_y\operatorname{TV}(W_y,P_{\beta,r_k})\le R_{\rm conf,\beta}(M).
\tag{14.3}
$$

Every positive-row label is an actual reachable configuration on this held-record fibre, and its $Q_x$ or $W_y$ is exactly its original pulled-back complete decoder. The emissions may lie anywhere in $[0,1]$, and the copied decoders may have positive noncompletion mass. A single support-closed stationary table can use these rows and kernels without changing any copied complete law.

**Proof.** This is the paid-history/common-row construction of [FLOW, §3], with the fixed-fibre reachability statement also made explicit in [UNIF, Lemma 2.1]. The all-four risk-order bounds are the two configuration and two law comparisons in [FLOW, §3]. Let $\eta_0$ be the source-independent initial configuration row at the original seed-pair boundary, after initialization and before the first paid seed Read. At that boundary let $R_\alpha,R_\beta$ be the stochastic updates for the two equal rejected pairs, and let $P_S$ be the acquired suffix-update product along the six Read letters of $S$, including their original control, record-write and latch updates. Finite-chain decomposition gives positive integers $d_\alpha,d_\beta$ such that $R_\alpha^{d_\alpha n}\to E_\alpha$ and $R_\beta^{d_\beta n}\to E_\beta$. For each supported $r=r_k$, the paid positive histories

$$
(\alpha\alpha)^{m_n}(\beta\beta)^{t_n}S,\qquad
m_n=d_\alpha\left\lfloor\frac{nr}{d_\alpha}\right\rfloor,\qquad
 t_n=d_\beta\left\lfloor\frac{n(1-r)}{d_\beta}\right\rfloor
$$

have configuration rows tending to the same $\lambda=\eta_0E_\alpha E_\beta P_S$, independently of $r$. Write these histories as $h_n(r)$ and set $\ell_S(t)=t^3(1-t)^3$, the fixed suffix's positive likelihood. Relative to the chosen supported depth $k$, the full paid-history likelihood ratios satisfy

$$
L_{n,i}:=\frac{\Pr(h_n(r)\mid K=i)}{\Pr(h_n(r)\mid K=k)}
=\frac{\ell_S(r_i)}{\ell_S(r)}
\exp\!\left[-2n\operatorname{KL}(\operatorname{Ber}(r)\Vert\operatorname{Ber}(r_i))+\varepsilon_{n,i}\right],
$$

$$
|\varepsilon_{n,i}|\le C_{\rm round}
:=2d_\alpha\log(6/5)+2d_\beta\log(10/9).
$$

Since $t(1-t)\in[2/9,6/25]$ on $I$ and KL is nonnegative, the bound

$$
0\le L_{n,i}\le C_*:=e^{C_{\rm round}}(27/25)^3,
\qquad
0\le\frac{\mu(i)}{\mu(k)}L_{n,i}
\le\frac{C_*}{\mu(k)}\mu(i)
$$

holds uniformly in $n$ and competing depths $i$. The dominating sequence is summable because $\mu$ is a probability prior and $\mu(k)>0$. The source parameters are distinct, so $L_{n,i}\to0$ for each $i\ne k$. Dominated convergence therefore gives

$$
\sum_{i\ne k}\frac{\mu(i)}{\mu(k)}L_{n,i}\to0,
\qquad
\nu_{h_n(r)}(k)
=\left(1+\sum_{i\ne k}\frac{\mu(i)}{\mu(k)}L_{n,i}\right)^{-1}\to1,
$$

including for countable priors. Every approximant is a finite positive history of this one installed source, with the same seed, marker records and permissions. Each fixed fourth-segment prefix also has positive likelihood throughout $I$ and bounded likelihood ratios there, so appending it preserves this summable domination and posterior concentration.

Appending any fixed number $j$ of returns, with or without one further $\beta$, gives limiting rows $\lambda(BA)^j$ and $\lambda(BA)^jB$ and the corresponding pure targets. Configuration loss is linear in the row and 1-Lipschitz in the target; law loss is continuous in the finite row and target. Hence both risk orders on each of these limiting rows are bounded by the original phase suprema, simultaneously for every supported $k$.

Take a convergent subsequence of the Cesàro rows
$\pi_N=N^{-1}\sum_{j<N}\lambda(BA)^j$. The identity
$\pi_NBA-\pi_N=[\lambda(BA)^N-\lambda]/N$ gives $\pi BA=\pi$. Put $\tau=\pi B$. Averaging preserves the configuration bounds by linearity and the law bounds by convexity, and taking the finite-row limit proves (14.3) and its law counterparts.

If $\pi_x>0$, then $(\lambda(BA)^j)_x>0$ for some finite $j$; otherwise all Cesàro coordinates would vanish. A sufficiently late finite paid-history approximant also has positive $x$ coordinate. The same argument applied to $\tau=\pi B$ proves suspended reachability. Thus positive stationary coordinates are original reachable configurations, with their own complete original decoders. Conversely, the lemma asserts no coverage of every reachable original configuration by the stationary support; transient labels can disappear. Only this inclusion is required in (14.2).

Delete zero-row labels. The flow equations show that retained labels cannot move under $B$ or $A$ to deleted labels, because all flows are nonnegative. On this support, keep the original emissions and transitions. Its synthetic program is the original program from each such configuration up to completion, with the same original event blocks, and so keeps its complete law, including any noncompletion mass. If a comparison observer is desired on other record fibres, the product update and source-independent latch construction of Lemma 2.1.1 applies with these arbitrary emissions; normalization now follows from the copied complete laws rather than a regular survival bound. Original targets are the same posterior mixtures, so countable TV convexity gives risk domination on all original fibres. The construction supplies no defect or resource preservation. ∎

**Theorem 14.2 (full finite-observer law-diameter noncollapse).** For every finite observer $M$ of the original source and every allowed installed prior,

$$
e(M)+\frac{18}{11}D_p(M)>\eta,
\qquad
e(M)+\frac{20}{11}D_\beta(M)>\eta,
\tag{14.4}
$$

where

$$
e(M)=\max\{R_{\rm conf,p}(M)-\rho_p,
            R_{\rm conf,\beta}(M)-\rho_\beta\}.
$$

In particular, if $e(M_n)\to0$ along finite observers, then

$$
\liminf_nD_p(M_n)\ge\frac{11}{1800000},\qquad
\liminf_nD_\beta(M_n)\ge\frac{11}{2000000}.
\tag{14.5}
$$

If either held-fibre diameter is zero, then $e(M)>\eta$. This conclusion uses no zero-defect assumption and makes no claim about a fixed COMPLETE budget.

**Proof.** Use Lemma 14.1 and write the common stationary rows and copied laws as $\pi,\tau,Q_x,W_y$, with means

$$
\bar u=\sum_x\pi_xu_x,\qquad \bar v=\sum_y\tau_yv_y,
\qquad \bar Q=\sum_x\pi_xQ_x,\qquad \bar W=\sum_y\tau_yW_y.
$$

Let

$$
d_p=\sum_x\pi_x\operatorname{TV}(Q_x,\bar Q),\qquad
d_\beta=\sum_y\tau_y\operatorname{TV}(W_y,\bar W).
$$

Because every positive table label is reachable on the held fibre, convexity gives

$$
d_p\le D_p(M),\qquad d_\beta\le D_\beta(M).
\tag{14.6}
$$

If $e(M)>\eta$, both inequalities are immediate. Assume $e(M)\le\eta$. The endpoint cylinders give

$$
\frac25-\rho_p-e(M)\le\bar u\le\frac13+\rho_p+e(M),
$$

$$
\frac25-\rho_\beta-e(M)\le\bar v\le\frac13+\rho_\beta+e(M),
\tag{14.7}
$$

Under $e(M)\le\eta$, the intervals in (14.7) are contained, respectively, in the enclosing intervals with bounds
$127931891/364500000$ and $139368109/364500000$, and
$984373/2700000$ and $995627/2700000$.
These bounds are obtained by substituting $\eta=1/100000$ for $e(M)$; they imply $\bar u,\bar v\in[1/3,2/5]$ without asserting attainable extrema for arbitrary $e(M)$.

Construct an auxiliary singleton table with emissions $\bar u,\bar v$ and identity acquired kernels. Its complete laws $Q^0,W^0$ obey

$$
Q^0=\bar u\,\delta_\alpha+(1-\bar u)\,\beta W^0,\qquad
W^0=(1-\bar v)\,\delta_\beta+\bar v\,\alpha Q^0.
\tag{14.8}
$$

The return mass is at most $(2/3)(2/5)=4/15$, so these complete laws are normalized on the unbounded legal carrier and retain its infinite noncompletion outcome with mass zero. No real-valued row is supplied to the running observer; this singleton is an analysis comparison.

Define the pooled residuals

$$
c_p=\operatorname{TV}\bigl(\bar Q,\bar u\delta_\alpha+(1-\bar u)\beta\bar W\bigr),
$$

$$
c_\beta=\operatorname{TV}\bigl(\bar W,(1-\bar v)\delta_\beta+\bar v\alpha\bar Q\bigr).
$$

The individual equations, $\pi B=\tau$, $\tau A=\pi$, and the facts
$u_x=Q_x(\{\alpha\})$ and $1-v_y=W_y(\{\beta\})$ give the four estimates

$$
c_p\le\frac12d_p,\qquad c_\beta\le d_p,
\qquad c_p\le d_\beta,\qquad c_\beta\le\frac12d_\beta.
\tag{14.9}
$$

For example, the first residual is the zero-mass signed mixture
$\sum_x\pi_x(\bar u-u_x)L_x$, whose positive and negative masses are at most
$\frac12\sum_x\pi_x|u_x-\bar u|\le d_p/2$. For the second estimate in the first pair, convexity gives
$\operatorname{TV}(J_y,\bar Q)\le\sum_xA_{yx}\operatorname{TV}(Q_x,\bar Q)$ and then $\tau A=\pi$; the other pair is dual.

Let $a=\operatorname{TV}(\bar Q,Q^0)$ and $b=\operatorname{TV}(\bar W,W^0)$. From (14.8),

$$
a\le c_p+\frac23b,\qquad b\le c_\beta+\frac25a,
$$

so

$$
a\le\frac{15c_p+10c_\beta}{11},\qquad
b\le\frac{6c_p+15c_\beta}{11}.
\tag{14.10}
$$

Using the first pair in (14.9) gives $\max\{a,b\}\le18d_p/11$; using the second gives $\max\{a,b\}\le20d_\beta/11$. For every supported depth, the singleton's two law distances are at most the corresponding common-row distances plus $a$ or $b$. Those distances are at most the original configuration risks by Lemma 14.1 and convexity. The singleton's full actual-history risks are the suprema of these pure-depth distances by (2.3). Thus its maximal law excess is at most

$$
e(M)+\frac{18}{11}d_p
\quad\text{and also at most}\quad
e(M)+\frac{20}{11}d_\beta.
$$

The singleton is regular and both of its acquired kernels are complete redraws. Theorem 12.1 therefore makes each displayed quantity strictly larger than $\eta$. Finally use (14.6). Taking liminf proves (14.5). ∎

## 15. Correspondence, exact scope and the remaining alternatives

The common event cells, midpoint values and complete-tail endpoint geometry are supplied by [ST], [CLIP] and the published mixture separation [UNIF]. [UNIF] permits arbitrary complete decoder laws and compares them with a larger constant-parameter mixture family. The present Sections 12–14 instead track the actual unweighted successor kernels and show that collapsing either interface to one complete future law is impossible below the same rational tolerance. The law-diameter theorem then transfers that obstruction to the entire finite-observer class through the support inclusion and exact decoder correspondence on the held-record fibre in Lemma 14.1. No representation-family exclusion is counted twice.

The source correspondence is literal. The common depth is drawn once before all Reads; paid seed rejections, both seeds, all marker records, write-before-latch, held fields, permissions, matching Stop and delivery remain in the original control. The same acquired-letter kernels are used by each decoder. All finite fourth returns and the legal infinite noncompletion words remain in the complete carriers. The rows $\pi,\tau$, the successor laws, the diameters, and the auxiliary singleton are analysis objects, not posterior input, a continuous register, a free clock, a source reset, or an added Read. Rational entries can use the existing charged finite exact sampling convention; arbitrary real entries specify mathematical stochastic rules only.

The result is a source-specific obstruction and a necessary continuation-dispersion condition. It does not prove a finite exact common endpoint, a family with configuration excess tending to zero, a strictly positive unrestricted conf/conf infimum, or any fixed-budget optimum. Positive successor-law diameter is compatible with very small configuration excess, and the inequalities do not determine whether such a noncollapsed family exists. Marginalized defect may be nonzero and is not bounded here. Exact posterior or chronology recovery, physical-spacetime interpretation, global completion, total-resource optimality, remain outside these mathematical conclusions.

[UNIF]: https://github.com/the-omega-institute/trureturing/blob/37453819032a4873639381066b0f43946b7deed0/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_MIXTURE_SEPARATION.md


## 追加锚（本行以下为增补区）

## 16. Compact complete-law circulation and finite own-law regeneration

Fix the original once-$K$ source of Definitions 1.1–1.3, with one installed finite or countable prior $\mu$, positive endpoint masses, and at least one supported depth $k\ge3$. All supported interior depths are retained. Write

$$
R_\mu=\overline{\{r_k:\mu(k)>0\}}\subset[1/3,2/5].
$$

This is the parameter support closure; $\mathfrak S_\mu$ continues to denote the class of finite regular stationary tables in Corollary 2.3. The objective uses configuration-before-TV on the complete carrier, with the supremum over all original positive paid histories; law-order comparisons are auxiliary. The raw-law notation removes only the deterministic current-record rendering $I_c$; it does not remove Reads, records, permissions, completion, matching Stop or delivery. The stationary realization, parameter continuity, finite cells and two-phase contraction of §§2, 5 and 9 are reused. The additional bridge is from arbitrary feasible complete-law edge measures to actual finite tables.

**Definition 16.1 (complete law spaces and the two actual edges).** Let $\Omega_p,\Omega_\beta$ be the two complete countable raw carriers of Definition 1.2, including their respective infinite noncompletion outcomes $\infty_p,\infty_\beta$. Prefixing $\beta:\Omega_\beta\to\Omega_p\setminus\{\alpha\}$ and $\alpha:\Omega_p\to\Omega_\beta\setminus\{\beta\}$ includes these outcomes. Put $\lambda=4/15$, and for integers $L\ge0$ set

$$
\begin{aligned}
T_{p,L}&=\{w_{j,b}:j\ge L,\ b=0,1\}\cup\{\infty_p\},\\
T_{\beta,L}&=\{\alpha w_{j,b}:j\ge L,\ b=0,1\}\cup\{\infty_\beta\}.
\end{aligned}
\tag{16.1}
$$

Define spaces of normalized probability laws, with the full TV metric, by

$$
\begin{aligned}
\mathcal K_p&=\{q:u(q):=q(\alpha)\in[1/3,2/5],\quad
                  q(T_{p,L})\le\lambda^L\ (L\ge0)\},\\
\mathcal K_\beta&=\{w:v(w):=1-w(\beta)\in[1/3,2/5],\quad
                  w(T_{\beta,L})\le(2/5)\lambda^L\ (L\ge0)\}.
\end{aligned}
\tag{16.2}
$$

The infinite atoms are present, although these bounds force their mass to zero. Let $\mathcal K=\mathcal K_p\times\mathcal K_\beta$. Use two separately normalized Borel probability measures $\gamma,\zeta$ on $\mathcal K$, with shared marginals

$$
\gamma_p=\zeta_p=\sigma_p,\qquad
\gamma_\beta=\zeta_\beta=\sigma_\beta.
\tag{16.3}
$$

The coordinates of $\gamma$ are the current p law and successor suspended law on the acquired p-$\beta$ edge. The coordinates of $\zeta$ are the successor p law and current suspended law on the acquired suspended-$\alpha$ edge. Their coordinate order is the same, but their conditional equations condition on different coordinates. Neither edge is weighted by a synthetic emission probability. Define

$$
\begin{aligned}
\mathcal E_{B,z}(q,w)&=q(\beta z)-(1-u(q))w(z),&&z\in\Omega_\beta,\\
\mathcal E_{A,t}(q,w)&=w(\alpha t)-v(w)q(t),&&t\in\Omega_p.
\end{aligned}
\tag{16.4}
$$

A pair is feasible when (16.3) holds and, for every indicated complete outcome and every real continuous state test,

$$
\int f(q)\mathcal E_{B,z}(q,w)\,d\gamma=0
\quad(f\in C(\mathcal K_p)),\qquad
\int g(w)\mathcal E_{A,t}(q,w)\,d\zeta=0
\quad(g\in C(\mathcal K_\beta)).
\tag{16.5}
$$

Write $\mathcal F$ for these pairs. Their configuration losses and value are

$$
\begin{aligned}
\Phi_\mu(\gamma,\zeta)
 &=\max\left\{\sup_{r\in R_\mu}\left[\int\operatorname{TV}(q,P_{p,r})\,d\sigma_p-\rho_p\right],
 \sup_{r\in R_\mu}\left[\int\operatorname{TV}(w,P_{\beta,r})\,d\sigma_\beta-\rho_\beta\right]\right\},\\
V_\mu&=\min_{(\gamma,\zeta)\in\mathcal F}\Phi_\mu(\gamma,\zeta).
\end{aligned}
\tag{16.6}
$$

The minimum notation is justified next. These measures are analysis objects, not an installed infinite configuration carrier or an online probability register. In particular (16.5) is a family of conditional complete-measure constraints, not merely an equality of the two marginalized forecasts.

**Lemma 16.2 (compactness and attained complete-law value).** The spaces $\mathcal K_p,\mathcal K_\beta$ are nonempty compact convex spaces in full TV and contain the individual complete laws of every regular stationary table. The feasible set $\mathcal F$ is nonempty, compact and convex in the weak topology of the two edge probability measures. Its objective is continuous and convex, has nonnegative value, and attains the minimum (16.6). No compactness in TV of the edge probability measures is asserted.

Proof. Normalization, nonnegativity, the emission intervals and each tail bound in (16.2) are closed convex conditions in the countable $\ell^1$ probability simplex. That simplex is complete in TV. Collapse $T_{s,L}$ onto one fixed finite outcome at level $L$, keeping every earlier complete outcome. The resulting laws lie in a finite-dimensional simplex, and the full TV displacement is at most $\lambda^L$ at p and $(2/5)\lambda^L$ at suspension. These bounds tend uniformly to zero. Finite-dimensional total boundedness therefore gives total boundedness of each $\mathcal K_s$. Closedness and completeness give compactness. The tails decrease to the infinite atom; continuity from above gives zero mass there without conditioning on completion.

For a finite regular table the p return matrix is
$\operatorname{diag}(1-u)B\operatorname{diag}(v)A\le\lambda BA$ entrywise. Thus survival of $L$ returns from each label is at most $\lambda^L$. A suspended law first returns with probability at most $2/5$. These are exactly (16.2), with the infinite outcomes retained. The endpoint native laws in (1.2) are examples, since $a_r\le6/25<\lambda$ and $r\le2/5$.

Borel probability measures on a compact metric space form a compact space for weak convergence; this is the compact-space case of Prokhorov's theorem [BILL16, §5]. Hence $\operatorname{Prob}(\mathcal K)^2$ is compact. Each integrand in (16.5) is bounded continuous: individual atom coordinates and $u,v$ are continuous in full TV. Marginal agreement can be expressed by integrals of all continuous functions of each coordinate, so it too is a closed affine condition. The intersection is compact and convex. For nonemptiness take

$$
\gamma=\zeta=\tfrac12\delta_{(P_{p,r_1},P_{\beta,r_1})}
                    +\tfrac12\delta_{(P_{p,r_2},P_{\beta,r_2})}.
\tag{16.7}
$$

Both source-law generator identities hold at each of its points, so this is equality-feasible. It is not asserted to meet the interior risk bounds.

For a fixed $r$, the configuration loss is an integral of a continuous function, and is continuous in the weak marginal. The supplied parameter estimate (2.4) gives, uniformly in a candidate law,

$$
|\operatorname{TV}(D,P_{s,r})-\operatorname{TV}(D,P_{s,t})|
\le L_s|r-t|.
$$

Given weak convergence of marginals, a finite parameter net in compact $R_\mu$ reduces uniform convergence of the losses to convergence at finitely many parameters, with a uniformly vanishing net error. Consequently their suprema are continuous. Each fixed-parameter loss is affine in its marginal, so its supremum, and then the maximum of the two suprema, is convex. Continuity also shows that the supremum over the actual supported parameters equals that over $R_\mu$, including for a countable prior. In each phase the two endpoint losses have sum at least $\operatorname{TV}(P_{s,r_1},P_{s,r_2})=2\rho_s$; their maximum is at least $\rho_s$. Thus $\Phi_\mu\ge0$. Compactness and continuity now prove attainment. ∎

**Theorem 16.3 (Borel-cell regeneration and the exact regular value).** For every feasible pair and every rational $0<t\le1$, there is one actual finite regular stationary table with at most $N_p(t),N_\beta(t)$ labels of (9.2). It has both acquired flows exactly, and its individual complete laws are generated by its own installed emissions and acquired kernels. With $a_s(t)$ as in (9.4), its losses against every complete target $T$ satisfy

$$
\begin{aligned}
-(t+a_s(t))&\le \widehat L_{{\rm conf},s}(T)-L_{{\rm conf},s}(T)\le a_s(t),\\
|\widehat L_{{\rm law},s}(T)-L_{{\rm law},s}(T)|&\le a_s(t),
\end{aligned}
\tag{16.8}
$$

where $L_{{\rm conf},p}(T)=\int\operatorname{TV}(q,T)\,d\sigma_p$ and
$L_{{\rm law},p}(T)=\operatorname{TV}(\int q\,d\sigma_p,T)$, with the suspended analogues. Hats denote the finite table with its actual stationary row. The same inequalities hold after any common finite future partition. In particular,

$$
V_\mu=J(\mathfrak S_\mu)=J(\mathfrak E_\mu),\qquad
\frac{11}{61}V_\mu\le J(\mathfrak M_\mu)\le V_\mu.
\tag{16.9}
$$

For general marginal support the construction is finite approximation. Separately, when both marginals are finitely supported, singleton law cells give exact finite realization with one label per distinct marginal law; that exact realization has no asserted tolerance-dependent label bound. No equality with the original arbitrary-observer value, finite optimizer, effective sampler or resource-preserving replacement is claimed.

Proof. First extend (16.5) to every Borel state cell. For $z\in\Omega_\beta$ define a finite signed Borel measure on $\mathcal K_p$ by

$$
\nu_z(E)=\int_{E\times\mathcal K_\beta}\mathcal E_{B,z}(q,w)\,d\gamma.
\tag{16.10}
$$

Its density is bounded, so its variation is finite. Equation (16.5) says $\int f\,d\nu_z=0$ for all continuous $f$. To see explicitly that this determines every Borel set, for a closed set $F$ use the continuous functions
$f_n(q)=\max\{0,1-n\operatorname{dist}(q,F)\}$, with the empty-set case zero. They converge pointwise to $1_F$ and are bounded by one. Dominated convergence against $|\nu_z|$ gives $\nu_z(F)=0$. The class of sets on which $\nu_z$ vanishes contains the whole space, is closed under complements and countable disjoint unions, and contains the closed sets, which form a generating intersection-closed family. The pi-lambda theorem therefore gives $\nu_z(E)=0$ for every Borel $E$. Apply the same argument on $\mathcal K_\beta$ to
$\int_{\mathcal K_p\times E}\mathcal E_{A,t}\,d\zeta$. This is the continuous-test uniqueness principle for finite signed measures (Rudin, *Real and Complex Analysis*, Chapters 2 and 6), applied separately to both edges and every complete outcome.

All law integrals used here exist in $\ell^1$: the coordinate maps are measurable, the carriers are countable and every integrand law has norm one. Tonelli gives normalization of their integrals, and bounded coefficients give absolutely summable signed integrals. Thus equality of every complete atom coordinate, including infinity, is equality of the whole signed measure. There is no finite-word proxy at this step.

Use the finite level-$L$ floor bins of Definition 9.1 on the law spaces themselves, with $L,G,\xi$ as in (9.1). They are Borel cells. Two p partition vectors in one cell have TV at most $(L+1/2)\xi$, and two suspended vectors at most $(L+1)\xi$. Refining their residual cell increases TV by at most its smaller mass. The uniform residual bounds (16.2), $\lambda^L\le t/2$ and $G\ge(2L+2)/t$ therefore give full-law diameter at most $t$ in either phase. There are at most the numbers of cells in (9.2). The emission coordinate $q(\alpha)$, or $w(\beta)$, is among the binned coordinates, so the emission range in each cell has width at most $\xi$.

Retain only cells $C,D$ with positive marginal weight, and define

$$
\begin{aligned}
\pi_C&=\sigma_p(C),&\tau_D&=\sigma_\beta(D),\\
B_{CD}&=\gamma(C\times D)/\pi_C,&
A_{DC}&=\zeta(C\times D)/\tau_D,\\
\bar q_C&=\pi_C^{-1}\int_Cq\,d\sigma_p,&
\bar w_D&=\tau_D^{-1}\int_Dw\,d\sigma_\beta,\\
\bar u_C&=\pi_C^{-1}\int_Cu(q)\,d\sigma_p,&
\bar v_D&=\tau_D^{-1}\int_Dv(w)\,d\sigma_\beta.
\end{aligned}
\tag{16.11}
$$

Zero-marginal cells have zero incident mass in both nonnegative edge measures. Separate normalization and shared marginals give stochastic rows and, exactly,

$$
\sum_C\pi_CB_{CD}=\tau_D,\qquad
\sum_D\tau_DA_{DC}=\pi_C.
\tag{16.12}
$$

The averaged emissions remain regular. Each member law is within $t$ of its own cell centroid by convexity. The Borel identities proved above give the complete centroid equations

$$
\begin{aligned}
\bar q_C&=\bar u_C\delta_\alpha+
 \beta\,\pi_C^{-1}\int_{C\times\mathcal K_\beta}(1-u(q))w\,d\gamma,\\
\bar w_D&=(1-\bar v_D)\delta_\beta+
 \alpha\,\tau_D^{-1}\int_{\mathcal K_p\times D}v(w)q\,d\zeta.
\end{aligned}
\tag{16.13}
$$

These are analysis identities; the centroids are not installed as decoders.

For the first equation replace the successor $w$ by $\bar w_{D(w)}$. This costs at most $(2/3)t$ in TV. Under the conditional edge probability $\gamma|_{C\times\mathcal K_\beta}/\pi_C$, the mean of $e=1-u(q)$ is $1-\bar u_C$. For any joint distribution of a scalar $e$ of range width at most $\xi$ and a probability law $H$, without independence,

$$
\left\|\mathbb E[(e-\mathbb Ee)H]\right\|_{\rm TV}
\le\tfrac12\mathbb E|e-\mathbb Ee|\le\xi/4.
\tag{16.14}
$$

The signed measure has total mass zero; its half-$\ell^1$ norm is bounded by the first expression. The mean absolute deviation bound is the interval calculation in (9.14). Taking $H=\bar w_{D(w)}$ accounts for the emission–successor covariance. Its unweighted mean is exactly $\sum_DB_{CD}\bar w_D$. The first centroid has generator residual at most $(2/3)t+\xi/4$. On the second edge, replace $q$ by $\bar q_{C(q)}$ and take $e=v(w)$ under $\zeta|_{\mathcal K_p\times D}/\tau_D$. Its mean is $\bar v_D$, its unweighted successor mean is $\sum_CA_{DC}\bar q_C$, and the residual is at most $(2/5)t+\xi/4$.

Install the finite table (16.11), and denote its own generated complete laws by $\widehat q_C,\widehat w_D$. Regular return survival gives normalized laws, zero infinite mass, and uniqueness: agreement of the generator equations determines every complete finite word, while a remainder after $L$ returns has mass tending uniformly to zero. Equivalently, the two-phase generator map contracts after a full return by $\lambda<1$. Put
$d_p=\max_C\operatorname{TV}(\widehat q_C,\bar q_C)$ and
$d_\beta=\max_D\operatorname{TV}(\widehat w_D,\bar w_D)$. Prefixing is a TV isometry and mixing contracts it, so

$$
d_p\le\tfrac23t+\xi/4+\tfrac23d_\beta,\qquad
d_\beta\le\tfrac25t+\xi/4+\tfrac25d_p.
\tag{16.15}
$$

Solving, with $1-(2/3)(2/5)=11/15$, gives $d_p\le a_p(t)$ and $d_\beta\le a_\beta(t)$, the existing constants (9.4). Jensen bounds the centroid configuration loss by the original marginal configuration loss. The regenerated centroid comparison therefore increases that loss by at most $a_s(t)$. Conversely every member law is within $t+a_s(t)$ of the regenerated law of its cell, which bounds the decrease by $t+a_s(t)$. The marginal barycenter changes by at most $a_s(t)$, giving the law-order estimate. Pushing every law to a common finite partition preserves all these bounds. This proves (16.8).

The installation is precisely Lemma 2.1.1: retain the entire original $C_0$, synthesize fair letters before the latch, and sample $\pi$ independently after the original third record write and latch within that same update. Use $B$ on acquired p-$\beta$ and $A$ on acquired suspended-$\alpha$, with those identical kernels in synthesis. Completing letters clear private labels and enable only the matching original Stop. Both seeds, all paid equal-pair rejections, marker triples, records, permissions, finite returns and delivery remain. Induction from (16.12) keeps the actual private row $\pi$ or $\tau$ at every fourth history; acquired letters are not reweighted by synthetic emissions. Every current-record law is rendered through its own $I_c$.

At an original positive history the unchanged target is the countable posterior mixture (1.3). TV convexity, with the stationary private row, carries a uniform supported-pure-target bound to that mixture. The reverse supremum equality is the paid rejection-history exposure in (2.3), not a reset experiment or a restriction to the first fourth cut. Thus applying (16.8) to each pure target and taking the full phase suprema gives a table of excess at most $\Phi_\mu(\gamma,\zeta)+a_p(t)$.

In the other value direction, any finite stationary regular table pushes its two actual edge arrays forward as

$$
\gamma=\sum_{x,y}\pi_xB_{xy}\delta_{(Q_x,W_y)},\qquad
\zeta=\sum_{y,x}\tau_yA_{yx}\delta_{(Q_x,W_y)}.
\tag{16.16}
$$

Their masses are separately one, and (2.1) gives both shared marginals. Multiplying each individual complete generator equation by $f(Q_x)$ or $g(W_y)$ and summing its own outgoing edges gives (16.5). Duplicate law values just add their masses; their emissions are determined by the law and their conditional equations still hold. Configuration loss pushes forward exactly, so $V_\mu\le J(\mathfrak S_\mu)$. Apply the finite regeneration to a minimizer and let $t\downarrow0$. Since $\xi\le t/4$, $a_p(t)\to0$, giving $J(\mathfrak S_\mu)\le V_\mu$. Corollary 2.3 supplies the remaining assertions (16.9), including its risk-only original-class factor and the periodic-to-stationary equality. Original zero/unit emissions and positive noncompletion mass are handled by that supplied extraction and clipping comparison, not by membership in (16.2).

Finally, when both marginals have finite support, both edges are supported on their finite Cartesian product. Use the Borel identities with singleton law cells. Equations (16.11)–(16.13) then have no cell diameter or covariance error: emissions are constant in each conditioning cell. The given laws satisfy the exact finite generator equations and regular uniqueness identifies them with the generated laws. This proves exact realization in this case. General compact minimizers need not have finite marginal support. ∎

## 17. Complete endpoint projection and the zero-value alternatives

**Theorem 17.1 (complete endpoint boxes and necessary near-zero rates).** For either phase let $P_1=P_{s,r_1},P_2=P_{s,r_2}$ on its entire countable carrier, and define

$$
\begin{aligned}
l(z)&=\min\{P_1(z),P_2(z)\},&h(z)&=\max\{P_1(z),P_2(z)\},\\
\mathcal B_s&=\{D':D'\text{ is a normalized law},\ l\le D'\le h\},\\
a(D)&=\sum_z(l(z)-D(z))_+,&b(D)&=\sum_z(D(z)-h(z))_+.
\end{aligned}
\tag{17.1}
$$

The infinite noncompletion coordinate is included. For every normalized complete law $D$,

$$
\min_{D'\in\mathcal B_s}\operatorname{TV}(D,D')=\max\{a(D),b(D)\},
\tag{17.2}
$$

and a normalized minimizer exists. Now let $M$ be one finite regular stationary table and put $e=\max_s\{R_{{\rm conf},s}(M)-\rho_s\}$. Project each of its complete laws $Q_x,W_y$ to minimizers $Q'_x,W'_y$ in the two boxes. Retain its original $\pi,\tau,B,A$. Then

$$
E_p:=\sum_x\pi_x\operatorname{TV}(Q_x,Q'_x)\le2e,\qquad
E_\beta:=\sum_y\tau_y\operatorname{TV}(W_y,W'_y)\le2e.
\tag{17.3}
$$

Their two full residual barycenter errors, with the unchanged actual flow, obey

$$
\begin{aligned}
d'_B&:=\sum_x\pi_x\operatorname{TV}\left(\operatorname{res}_\beta Q'_x,
                                     \sum_yB_{xy}W'_y\right)
       \le\tfrac53E_p+E_\beta\le16e/3,\\
d'_A&:=\sum_y\tau_y\operatorname{TV}\left(\operatorname{res}_\alpha W'_y,
                                     \sum_xA_{yx}Q'_x\right)
       \le3E_\beta+E_p\le8e.
\end{aligned}
\tag{17.4}
$$

The residual deletes the indicated future operation and its original event block. These projections are candidate laws and necessary conditions for a near-zero family. They are not assigned decoders, need not be native mixtures, and do not assert existence of that family.

Proof. Every normalized replacement must add at least $a(D)$ mass on the lower-violation coordinates and remove at least $b(D)$ on the upper-violation coordinates. Its total addition and removal are equal and each equals its TV displacement. Thus (17.2) has the stated lower bound.

For attainment clip coordinatewise to $c(z)=\min\{h(z),\max\{l(z),D(z)\}\}$. Its total mass is $1+a-b$. All relevant sums are finite, since $l,h,c$ are summable. If $a\ge b$, put $\delta=a-b$ and $M_-=\sum_z(c(z)-l(z))$. Since $\sum l\le1$, $M_-\ge\delta$. If $\delta>0$, set

$$
D'(z)=c(z)-\frac{\delta}{M_-}(c(z)-l(z));
\tag{17.5}
$$

if $\delta=0$, take $D'=c$. This countable redistribution is well-defined, remains in the box and has total mass one. No mass is removed from a lower violation because there $c=l$. The initial additions still total $a$, while the removals total $b+\delta=a$. Thus its TV distance is $a$. If $b\ge a$, use $\delta=b-a$, $M_+=\sum_z(h(z)-c(z))\ge\delta$ and
$D'=c+\delta(h-c)/M_+$ when $\delta>0$. Additions occur only where $c<h$, so no upper-violation removal is undone. Both total changes are $b$. This proves (17.2), including countably many coordinates and the noncompletion atom.

The complete coordinate triangle identity is

$$
\operatorname{TV}(D,P_1)+\operatorname{TV}(D,P_2)
=\operatorname{TV}(P_1,P_2)+a(D)+b(D).
\tag{17.6}
$$

It follows by summing the scalar absolute-value identity, as in (12.5); all summands are absolutely summable. The endpoint configuration losses of the same stationary row are each at most $\rho_s+e$ by (2.3). Their sum and $\operatorname{TV}(P_1,P_2)=2\rho_s$ give an expected outside-box mass $\mathbb E(a+b)\le2e$. Formula (17.2) gives (17.3). This is a bound on configuration averages before TV, not an inference from a marginal forecast. The projected infinite mass is zero because both endpoint masses there are zero. Their immediate completion coordinates lie in the endpoint interval, so their emissions are regular and their continuation probabilities are positive.

For completeness, if normalized laws $P,Q$ have positive masses $m,n$ on a continuation event $E$, then

$$
\max\{m,n\}\operatorname{TV}(P(\cdot\mid E),Q(\cdot\mid E))
\le\operatorname{TV}(P,Q).
\tag{17.7}
$$

If $m\ge n$, write their conditional laws as $p,q$. The variation on $E$ is at least $m\|p-q\|_1-(m-n)$, while that on the complement is at least $m-n$. Add and divide by two. Interchange the laws for $n\ge m$. Deleting a common operation block preserves this estimate. In the old and projected p laws, the p-$\beta$ continuation has mass at least $3/5$, giving the factor $5/3$; in the suspended laws the $\alpha$ continuation has mass at least $1/3$, giving the factor 3. The original own-law equations identify the old residuals as $\sum_yB_{xy}W_y$ and $\sum_xA_{yx}Q_x$. Triangle inequality, mixture convexity, $\pi B=\tau$ and $\tau A=\pi$ now give (17.4). Any construction from these candidate laws still owes exact own-law generation, or a proved regeneration error; the full-measure finite coupling/repair criterion does not remove that obligation. ∎

**Theorem 17.2 (zero-risk normal form and finite versus arbitrary support).** Use the endpoint-positive events of §12,

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\},
$$

and their midpoint constants

$$
C_p=11758471/22781250,\qquad C_\beta=5261/6750.
\tag{17.8}
$$

A feasible pair has $\Phi_\mu=0$ if and only if its marginals satisfy all three conditions:

1. $\sigma_s$ is concentrated on $\mathcal K_s\cap\mathcal B_s$ in each phase.
2. $\int q(E_p)\,d\sigma_p=C_p$ and $\int w(E_\beta)\,d\sigma_\beta=C_\beta$.
3. For every actually supported interior depth $k\ge3$, its two configuration losses are at most $\rho_p,\rho_\beta$, respectively.

Consequently a finite common endpoint observer in the original class exists if and only if a zero-risk feasible pair exists with **both** marginals finitely supported. The original unrestricted infimum is zero if and only if **some** zero-risk feasible pair exists, with arbitrary marginal support. A strictly positive unrestricted gap is equivalent to absence of every such zero-risk pair. An unattained zero infimum requires both existence of a zero-risk pair and exclusion of every pair with both marginals finitely supported.

Proof. Suppose $\Phi_\mu=0$. Both endpoint configuration losses in either phase are at most $\rho_s$. Integrate (17.6). Its nonnegative outside-box term must have expectation zero, so $a(D)+b(D)=0$ almost surely, proving complete box membership. In this box the positive endpoint-1 difference event gives

$$
\operatorname{TV}(D,P_{s,r_1})=P_{s,r_1}(E_s)-D(E_s),\qquad
\operatorname{TV}(D,P_{s,r_2})=D(E_s)-P_{s,r_2}(E_s).
\tag{17.9}
$$

Indeed $D$ lies coordinatewise between the two endpoints, and the sign of their difference is fixed on each coordinate. The endpoint-positive events are exactly those listed above; §12 gives their probabilities and their difference $2\rho_s$. The two averaged inequalities in (17.9) force the midpoint identity. Every supported interior inequality is also part of $\Phi_\mu=0$. Conversely box membership and the midpoint identity give both endpoint losses exactly $\rho_s$. Together with every supported interior inequality, continuity extends the bounds to $R_\mu$ and gives $\Phi_\mu\le0$. Lemma 16.2 gives equality. No finite diagnostic interior set can replace condition 3 for an unspecified countable support.

If both marginals have finite support, both edge measures are concentrated on their finite Cartesian product. The singleton-cell exact realization at the end of Theorem 16.3 gives a finite regular stationary table with those exact complete laws and configuration losses. Equation (2.3) turns them into the same all-positive-history risks. The separate phase minima make both endpoint bounds equalities. Conversely a finite regular stationary endpoint table gives a zero-risk finite-support pair by (16.16). Corollary 2.3 supplies the exact endpoint equivalence with the original arbitrary finite class; this assertion is stronger than, and separately included alongside, its numerical infimum sandwich. Thus finite attainment has the stated finite-marginal-support characterization.

By Lemma 16.2, $V_\mu\ge0$ is attained. Hence $V_\mu=0$ exactly when some zero-risk pair exists. By (16.9) this is equivalent to $J(\mathfrak M_\mu)=0$, and absence of every zero-risk pair is equivalent to $V_\mu>0$ and to a positive original gap. Conditional on a zero-risk pair, Theorem 16.3 supplies actual finite tables of excess at most $a_p(t)\to0$; that is the required finite approximation, rather than installation of the compact minimizer. It does not make any one table exact. Finally an infinite-support zero pair does not exclude a different finite-support zero pair. Zero value and absence of all finite-support zero pairs are both needed to conclude nonattainment. ∎

## 18. Whole-product certificates and finite rational verification

The existence of some finite positive-gap certificate is already supplied by §10. The following form instead tests inequalities on the complete-law product, without first fixing a label count. Its use of convex separation and polynomial approximation is mature machinery; the source-specific content is its compatibility with both actual edges and the value bridge of Theorem 16.3.

**Theorem 18.1 (whole-product certificate and strict positive-gap completeness).** Choose finite sets $S_p,S_\beta\subset\{r_k:\mu(k)>0\}$, possibly empty in one phase, and weights

$$
\theta_{s,r}\ge0,\qquad
\sum_{r\in S_p}\theta_{p,r}+\sum_{r\in S_\beta}\theta_{\beta,r}=1.
\tag{18.1}
$$

Define the weighted losses, distinct from the midpoint constants $C_s$ of (17.8), by

$$
H_p(q)=\sum_{r\in S_p}\theta_{p,r}[\operatorname{TV}(q,P_{p,r})-\rho_p],\qquad
H_\beta(w)=\sum_{r\in S_\beta}\theta_{\beta,r}[\operatorname{TV}(w,P_{\beta,r})-\rho_\beta].
\tag{18.2}
$$

Let $a\in C(\mathcal K_p),b\in C(\mathcal K_\beta)$, and choose finitely many state tests $f_i\in C(\mathcal K_p),g_j\in C(\mathcal K_\beta)$ with complete outcomes $z_i\in\Omega_\beta,t_j\in\Omega_p$. Empty test lists are allowed. Set

$$
\begin{aligned}
G_B(q,w)&=H_p(q)+a(q)+b(w)+\sum_i f_i(q)\mathcal E_{B,z_i}(q,w),\\
G_A(q,w)&=H_\beta(w)-a(q)-b(w)+\sum_j g_j(w)\mathcal E_{A,t_j}(q,w).
\end{aligned}
\tag{18.3}
$$

If, on the **whole** product $\mathcal K_p\times\mathcal K_\beta$,

$$
G_B\ge c_B-\delta_B,\qquad G_A\ge c_A-\delta_A,\qquad
\delta_B,\delta_A\ge0,
\tag{18.4}
$$

then every original finite observer satisfies

$$
e(M):=\max_s\{R_{{\rm conf},s}(M)-\rho_s\}
\ge\frac{11}{61}\max\{0,c_B+c_A-\delta_B-\delta_A\}.
\tag{18.5}
$$

Conversely, $V_\mu>0$ if and only if finite data of this form exist with exact inequalities $\delta_B=\delta_A=0$ and $c_B+c_A>0$. This is existence of a finite strict certificate, not attainment of an optimal dual or a supplied numerical margin. Restricting (18.4) to endpoint boxes, native mixtures, one finite shape or sampled points does not give this conclusion.

Proof. Integrate $G_B$ against $\gamma$ and $G_A$ against $\zeta$ for a feasible pair. Shared p and suspended marginals cancel $a$ and $b$, separately. Each conditional generator term vanishes by (16.5). What remains is

$$
\sum_{s,r}\theta_{s,r}
\left[\int\operatorname{TV}(D,P_{s,r})\,d\sigma_s(D)-\rho_s\right]
\le\Phi_\mu(\gamma,\zeta).
\tag{18.6}
$$

The last inequality uses nonnegative weights jointly summing to one and losses from this same feasible pair. Since the two edge measures each have mass one, (18.4) lower-bounds the left side by $m=c_B+c_A-\delta_B-\delta_A$. Minimize over feasible pairs and use $V_\mu\ge0$ and (16.9). Then $e(M)\ge J(\mathfrak M_\mu)\ge(11/61)\max\{0,m\}$, proving (18.5). In particular an exact positive certificate implies $V_\mu>0$.

For the converse choose $0<d<V_\mu$. On the compact convex space
$\mathcal U=\operatorname{Prob}(\mathcal K)^2$ of two unconstrained, separately normalized edge measures, impose all marginal equalities tested by continuous functions, all equations (16.5), and every actually supported loss inequality at threshold $d$. Before marginal agreement is imposed, define these losses specifically as

$$
\ell_{p,r}(\gamma,\zeta)=\int\operatorname{TV}(q,P_{p,r})\,d\gamma_p-\rho_p,\qquad
\ell_{\beta,r}(\gamma,\zeta)=\int\operatorname{TV}(w,P_{\beta,r})\,d\zeta_\beta-\rho_\beta.
\tag{18.7}
$$

This choice is essential for the separated two-edge functional. All conditions are closed in $\mathcal U$. Their full intersection is empty: otherwise marginal agreement would identify the losses with (16.6), and continuity in the parameter would give a feasible value at most $d$ on $R_\mu$. By the finite intersection property, finitely many equality conditions and finitely many of these supported loss inequalities already have empty intersection.

Let $X\subset\mathbb R^{h+m}$ be the image of $\mathcal U$ under their equality-coordinate and loss-coordinate integrals. This is a compact convex set, because all coordinates are continuous affine functions. It is disjoint from the closed convex set

$$
Y=\{(0,y):y_i\le d\ (1\le i\le m)\}.
\tag{18.8}
$$

Finite-dimensional strict separation of a compact convex set from a disjoint closed convex set gives coefficients $\lambda_0,\theta_0$ with

$$
\inf_{(x,y)\in X}(\lambda_0\cdot x+\theta_0\cdot y)
>\sup_{(0,y)\in Y}\theta_0\cdot y
=d\sum_i\theta_{0,i}.
\tag{18.9}
$$

Unbounded negative directions in $Y$ force every $\theta_{0,i}\ge0$. They cannot all be zero: the equality-feasible endpoint-tag pair (16.7) gives an element of $X$ with equality coordinates zero, contradicting a strict lower bound greater than zero if $\theta_0=0$. Thus divide the whole separating functional by $\sum_i\theta_{0,i}>0$. This gives joint normalization (18.1), combining repeated loss coordinates if needed.

The equality multipliers for p-marginal agreement combine into one $a(q)$; those for suspended-marginal agreement combine into one $b(w)$. The remaining equality multipliers combine into finitely many $f_i\mathcal E_{B,z_i}$ and $g_j\mathcal E_{A,t_j}$, with their signs absorbed into the tests. Equation (18.7) then makes the separating functional exactly
$\int G_B\,d\gamma+\int G_A\,d\zeta$. Over the unconstrained product $\mathcal U$ its minimum is

$$
\min_{(q,w)\in\mathcal K}G_B(q,w)
+\min_{(q,w)\in\mathcal K}G_A(q,w)>d.
\tag{18.10}
$$

Indeed the two probability measures vary independently, so point masses can minimize the two continuous integrands separately. Choose constants slightly below these two minima, retaining a positive sum. They give the finite certificate. Only compactness and finite strict separation were used; no relative-interiority or optimal-dual-attainment hypothesis is needed. Convex separation is the mature principle behind transport duality [GRST18, §9.2], rather than a new duality theorem here. ∎

**Theorem 18.2 (rational finite-coordinate certificates on exact projection polytopes).** Whenever $V_\mu>0$, a certificate of Theorem 18.1 can be chosen with rational jointly normalized $\theta$, rational finite-coordinate polynomial potentials and state tests, finite complete outcomes, rational lower constants of positive combined margin, and weighted level-$T$ partition losses in place of the full losses. Such a specified certificate is a finite universal semialgebraic assertion on the exact projection polytopes below. Its validity directly lower-bounds full configuration risk. No degree, partition level, actual positive margin, runtime bound, support oracle or optimizer is supplied by this existence statement.

Proof. Begin with a strict certificate, of combined lower margin $m>0$. The algebra of polynomials in finitely many complete finite-atom coordinates contains constants and separates points of each compact $\mathcal K_s$. Infinite coordinates are identically zero there, so they are not needed to separate laws. The real Stone–Weierstrass theorem (Rudin, *Principles of Mathematical Analysis*, Chapter 7) uniformly approximates each of the finitely many continuous potentials and state tests by these polynomials. Coordinate values lie in $[0,1]$, so sufficiently close rational coefficients preserve the approximation. Every generator residual in (16.4) is bounded in absolute value by one. Hence the total error in each $G$ is bounded by the sum of its finitely many uniform approximation errors. Terms with an infinite test outcome vanish identically on $\mathcal K$ and can be deleted.

Approximate the finite vector of weights **within** its nonnegative sum-one simplex by rational vectors. For example, round all but one coordinate down to multiples of $1/n$ and put the remainder into the last coordinate; the total error tends to zero and normalization and nonnegativity hold exactly. Each loss $\operatorname{TV}(D,P_{s,r})-\rho_s$ has absolute value at most one, so this perturbation too has uniformly vanishing effect. Every selected parameter is an actual Fibonacci ratio, hence rational; no possibly irrational closure parameter has been inserted into the certificate. Take all these errors sufficiently small that the integrands with polynomial potentials and tests still have lower bounds of positive combined margin.

Let $\Pi_{s,T}$ be the level-$T$ partition of Definition 5.1, with one residual cell containing all later completions and noncompletion. For any normalized complete $D$,

$$
\begin{aligned}
0&\le\operatorname{TV}(D,P_{p,r})-
 \operatorname{TV}((\Pi_{p,T})_*D,(\Pi_{p,T})_*P_{p,r})\le(6/25)^T,\\
0&\le\operatorname{TV}(D,P_{\beta,r})-
 \operatorname{TV}((\Pi_{\beta,T})_*D,(\Pi_{\beta,T})_*P_{\beta,r})\le(2/5)(6/25)^T.
\end{aligned}
\tag{18.11}
$$

This is the residual-cell estimate in Theorem 5.2: refinement increases TV by at most the smaller residual mass, and the target masses are $a_r^T$ and $ra_r^T$. It is uniform over the candidate law; it does not need the candidate to be native or generated by a particular finite table. Replace the losses in (18.2) by these partition losses. The sum of the two possible downward errors is at most

$$
(6/25)^T\left(\sum_r\theta_{p,r}+(2/5)\sum_r\theta_{\beta,r}\right)\le(6/25)^T.
\tag{18.12}
$$

Choose $T$ large enough to retain a positive combined margin, and choose rational constants below the resulting minima, still with positive sum. Denote the resulting integrands by $\widetilde G_B,\widetilde G_A$. Since the weights are nonnegative, the corresponding full-loss integrands are pointwise at least these partition-loss integrands. A proved lower bound for the latter is therefore already a valid lower bound for full risk by Theorem 18.1. No further tail subtraction is owed after the certificate has been stated with these lower losses.

It remains to describe the whole finite verification domain exactly. Choose $N\ge1$ with $N\ge T$, large enough that **every** atom occurring in a polynomial, an unprefixed test coordinate, and a prefixed coordinate $q(\beta z_i)$ or $w(\alpha t_j)$ is distinguished before level $N$. In particular if $z_i=\alpha w_{j,b}$ then its p prefix is $w_{j+1,b}$, so that higher level must be included. The coordinate $q(\alpha)$ and the standalone suspended $w(\beta)$ are included as well. Residual partition coordinates are linear combinations of the retained coordinates and the single level-$N$ residual; they are not infinite-atom coordinates.

Write the p projection vector as $(q_{j,b}:j<N;R_p)$, where $q_{j,b}=q(w_{j,b})$, and the suspended vector as $(z_\star;z_{j,b}:j<N;R_\beta)$, where $z_\star=w(\beta)$ and $z_{j,b}=w(\alpha w_{j,b})$. All entries are nonnegative. Their exact projection sets $\mathcal P_{p,N},\mathcal P_{\beta,N}$ are the rational polytopes defined by

$$
\begin{aligned}
\sum_{j<N,b}q_{j,b}+R_p&=1,&q_{0,0}&\in[1/3,2/5],\\
\sum_{L\le j<N,b}q_{j,b}+R_p&\le\lambda^L&&(0\le L\le N),\\[2pt]
z_\star+\sum_{j<N,b}z_{j,b}+R_\beta&=1,&1-z_\star&\in[1/3,2/5],\\
\sum_{L\le j<N,b}z_{j,b}+R_\beta&\le(2/5)\lambda^L&&(0\le L\le N).
\end{aligned}
\tag{18.13}
$$

Every law in $\mathcal K_s$ projects into this polytope by its tail bounds. Conversely, for any p vector in the polytope keep its distinguished coordinates, put its residual $R_p$ at the complete atom $w_{N,0}$, and put zero at every other later atom and at $\infty_p$. Since $N\ge1$, the emission coordinate is unchanged. All tail totals for $L\le N$ are exactly the ones in (18.13), and those for $L>N$ are zero. This normalized law belongs to $\mathcal K_p$. For a suspended vector put $R_\beta$ at $\alpha w_{N,0}$, leaving $z_\star$ unchanged and putting zero at all other later outcomes and at $\infty_\beta$. The same argument proves membership in $\mathcal K_\beta$. Thus these are the exact projection sets, not outer relaxations or sampled grids.

All coordinates used by $\widetilde G_B,\widetilde G_A$ lie in these vectors. Their generator terms are polynomials and their partition losses are finite sums of absolute values of affine coordinate differences with rational target probabilities. Universal inequalities on $\mathcal K$ are consequently equivalent to the finite statements

$$
\forall(q^N,w^N)\in\mathcal P_{p,N}\times\mathcal P_{\beta,N},\qquad
\widetilde G_B(q^N,w^N)\ge c_B,\qquad
\widetilde G_A(q^N,w^N)\ge c_A.
\tag{18.14}
$$

Finite sign cases, or auxiliary variables with their exact absolute-value equations, express these as first-order statements over the real closed field with rational coefficients. Real quantifier elimination supplies in-principle decision for specified represented data [TAR18]. This verifies a universal lower-bound certificate. It does not infer equality of complete generated laws from finite coordinates, find a certificate of any prescribed size, or decide whether the full value is zero. For an opaque countable prior the existence argument still selects finitely many actually supported parameters mathematically, but effective selection or enumeration of admissible targets requires additional support data. ∎

The complete-law spaces, separate acquired edge normalization, Borel-cell extension and finite regeneration establish the source-specific value bridge. The compact zero-value alternatives and the endpoint-box rates are its direct consumers; the whole-product certificate is another. Original-domain installation, phase minima, target parameter continuity, full-tail estimates, cell covariance and two-phase contraction are supplied by §§1–2, 5 and 9. The error-corrected bounded-shape certificates and their positive-gap completeness in §10 are reused capabilities, not a second claim of new dual existence. The finite complete-measure coupling criterion is consistent with the singleton-cell case of Theorem 16.3; no native-tail rigidity result or restricted-mixture obstruction is needed for this append.

The mature machinery has a precise role. Billingsley's compact-space weak compactness applies because the **law** spaces have already been proved compact in full TV. Continuous functions determine finite signed Borel measures, and Stone–Weierstrass applies to a unital coordinate algebra separating those compact spaces. Gozlan, Roberto, Samson and Tetali [GRST18, §9.2, Theorem 9.7] state Fenchel–Legendre duality for lower-semicontinuous convex functions on Hausdorff locally convex spaces; the certificate here uses only finite-dimensional strict separation after compactness, and asserts no optimal dual attainment. Finite-dimensional martingale-coupling criteria, when used for a specified finite collection of full laws, need an injective full-measure embedding; no unchecked infinite-dimensional extension of such a criterion is invoked here. Real quantifier elimination applies only to the finitely represented rational polytopes and expressions in (18.14). These attributions locate established tools; they make no global priority claim for the source-specific synthesis.

No zero-risk pair, finite common optimizer, actual vanishing-excess family or explicit positive-margin certificate is provided by §§16–18. Theorem 17.2 states exactly what each would have to supply or exclude. The compact analysis space is not an infinite observer installation, and its attained minimum is not a finite-table attainment theorem. Theorems 16.3 and 18.1 compare risk on the same once-$K$ source and all its original positive paid histories; they preserve no prescribed hard marginalized-defect, COMPLETE-state, precision, program, workspace, acquisition, fee or total-work budget. Abstract real finite entries remain mathematical stochastic rules. Effective sampling needs separately represented data and charged service states. Physical realization, chronology recovery and original optimization completion do not follow from these ordinary mathematical proofs.

[BILL16]: https://doi.org/10.1002/9780470316962
[GRST18]: https://arxiv.org/html/1412.7480v4
[TAR18]: https://www.rand.org/pubs/reports/R109.html

The references are P. Billingsley, *Convergence of Probability Measures*, second edition, Wiley, §5; W. Rudin, *Real and Complex Analysis*, third edition, McGraw–Hill, Chapters 2 and 6, and *Principles of Mathematical Analysis*, third edition, McGraw–Hill, Chapter 7; N. Gozlan, C. Roberto, P.-M. Samson and P. Tetali, *Kantorovich duality for general transport costs and applications*, §9.2; and A. Tarski, *A Decision Method for Elementary Algebra and Geometry*, RAND report R-109. The proofs above are ordinary mathematical proofs; no Lean/kernel verification or effective observer synthesis is asserted.

## 追加锚（本行以下为增补区）
