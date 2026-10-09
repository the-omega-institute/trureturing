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

## 12. Exact emission-weighted interfaces of an acquired-flow quotient

The unweighted circulation in (2.1) preserves the acquired private rows. It does not identify those rows with the private rows selected by conditioning a synthetic continuation. This section derives that difference at both phase interfaces, before estimating it. It also separates preservation of a stationary cell centroid from preservation of each configuration's decoder and of arbitrary initial private rows. These are different recovery requirements on the same original source and future carrier.

**Definition 12.1 (positive cells and the two successor measures).** Fix any period-one table of Definition 2.1. Delete zero-row labels as in Definition 9.1, so that every retained $\pi_x,\tau_y$ is positive. Let $\mathcal C,\mathcal D$ be arbitrary partitions of $X,Y$ into nonempty cells, not necessarily the bins of Definition 9.1. Reuse the positive masses and centroids (9.3), the unweighted flow kernels $\widehat B,\widehat A$ of (9.9), and the mean emissions $\bar u,\bar v$ of (9.10). Write

$$
\begin{gathered}
\omega_C(x)=\pi_x/\bar\pi_C\quad(x\in C),\qquad
\zeta_D(y)=\tau_y/\bar\tau_D\quad(y\in D),\\
s_x=1-u_x,\quad \bar s_C=1-\bar u_C,\quad
b_{xD}=\sum_{y\in D}B_{xy},\quad a_{yC}=\sum_{x\in C}A_{yx},\\
H_x^B=\sum_yB_{xy}W_y,\qquad H_y^A=\sum_xA_{yx}Q_x,\\
L_C^B=\sum_D\widehat B_{CD}\bar W_D,\qquad
L_D^A=\sum_C\widehat A_{DC}\bar Q_C.
\end{gathered}
\tag{12.1}
$$

All these laws are on the complete raw successor carrier, including its infinite noncompletion outcome. A comparison on a full original record fiber applies the corresponding $I_c$ after deleting the next operation and its original event block. The weights are analysis data, not an acquired cell-observation port, a posterior register or an extra runtime archive.

For a finite weight row $w$ and scalar entries $e_i$, put $\bar e=\sum_iw_ie_i$ and define the signed measure

$$
\operatorname{Cov}_w(e,H)=\sum_iw_i(e_i-\bar e)H_i.
\tag{12.2}
$$

Its total mass is zero. For a zero-mass signed measure $\sigma$ use $\|\sigma\|_{\rm TV}=\sup_E|\sigma(E)|$, equivalently half its $\ell^1$ norm on the countable complete carrier. Define the unweighted decoder-transport errors and emission covariances by

$$
\begin{aligned}
E_C^B&=\sum_{x\in C}\omega_C(x)\sum_yB_{xy}(W_y-\bar W_{D(y)}),&
\kappa_C^B&=\operatorname{Cov}_{\omega_C}(s,H^B),\\
E_D^A&=\sum_{y\in D}\zeta_D(y)\sum_xA_{yx}(Q_x-\bar Q_{C(x)}),&
\kappa_D^A&=\operatorname{Cov}_{\zeta_D}(v,H^A).
\end{aligned}
\tag{12.3}
$$

In particular $\bar\pi_C,\bar\tau_D>0$, $\bar s_C\in[3/5,2/3]$ and $\bar v_D\in[1/3,2/5]$. Every conditional law and denominator below is therefore defined. For a more general table with a zero conditioning probability, the corresponding conditional identity would be omitted, using Definition 1.3's zero-probability convention rather than dividing by zero.

**Theorem 12.2 (two exact covariance identities).** For every table and partitions of Definition 12.1, the p-$\beta$ and suspended-$\alpha$ interfaces satisfy

$$
\begin{aligned}
\operatorname{res}_\beta\bar Q_C-\sum_{x\in C}\omega_C(x)H_x^B
 &=\kappa_C^B/\bar s_C,\\
\operatorname{res}_\alpha\bar W_D-\sum_{y\in D}\zeta_D(y)H_y^A
 &=\kappa_D^A/\bar v_D,\\
\operatorname{res}_\beta\bar Q_C-L_C^B
 &=E_C^B+\kappa_C^B/\bar s_C,\\
\operatorname{res}_\alpha\bar W_D-L_D^A
 &=E_D^A+\kappa_D^A/\bar v_D.
\end{aligned}
\tag{12.4}
$$

The first two compare emission-weighted synthetic continuation with the actual successor decoder average from a stationary row conditioned on the current private cell. The last two compare it with the successor centroid used by the unweighted acquired-flow quotient. The latter comparison includes a separate transport error; it is not generally just an emission covariance.

For the full acquired rows, put $\bar s=\sum_x\pi_xs_x$, $\bar v=\sum_y\tau_yv_y$, $\kappa_X^B=\operatorname{Cov}_\pi(s,H^B)$ and $\kappa_Y^A=\operatorname{Cov}_\tau(v,H^A)$. At every original positive history in the respective phase,

$$
\delta(h,\beta)=\|\kappa_X^B\|_{\rm TV}/\bar s\quad(h\in\mathcal H_p),\qquad
\delta(h,\alpha)=\|\kappa_Y^A\|_{\rm TV}/\bar v\quad(h\in\mathcal H_\beta).
\tag{12.5}
$$

Thus unweighted stationary flow and exact individual same-update generation alone do not assert zero marginalized defect.

Proof. The supplied individual generator equations (9.12) give

$$
\operatorname{res}_\beta\bar Q_C
=\frac{\sum_{x\in C}\omega_C(x)s_xH_x^B}{\bar s_C},\qquad
\operatorname{res}_\alpha\bar W_D
=\frac{\sum_{y\in D}\zeta_D(y)v_yH_y^A}{\bar v_D}.
\tag{12.6}
$$

Subtract each unweighted average. Expanding $s_x=\bar s_C+(s_x-\bar s_C)$ and $v_y=\bar v_D+(v_y-\bar v_D)$ proves the first two identities of (12.4). By (9.9),

$$
\sum_{x\in C}\omega_C(x)\sum_yB_{xy}\bar W_{D(y)}=L_C^B,\qquad
\sum_{y\in D}\zeta_D(y)\sum_xA_{yx}\bar Q_{C(x)}=L_D^A.
\tag{12.7}
$$

Their differences from the actual successor averages are precisely (12.3), proving the remaining identities. All sums over labels are finite; the identities are equalities of complete measures, not of a finite truncation.

For the first interface on a whole actual history, the private row before $\beta$ is $\pi$ and after it is $\pi B=\tau$. The source's acquired $\beta$ does not select labels by $s_x$: the private randomness is independent of the common source and the acquired word, by the latch rule and induction in Definition 2.1. Hence its successor forecast is $\sum_y\tau_yW_y=\sum_x\pi_xH_x^B$. Synthetic conditioning selects $\pi_xs_x/\bar s$ instead. This proves the first formula of (12.5). The second uses $\tau A=\pi$ and weights $\tau_yv_y/\bar v$. They hold for every positive paid history, after any number of fourth returns, under every allowed finite or countable prior. Applying the original record rendering preserves each difference and TV. Completing letters and the matching Stop/delivery have the original deterministic residuals; they add no defect to these fourth-phase formulas. ∎

**Proposition 12.3 (centroid compatibility, decoder agreement and coefficient criteria).** Call the stationary centroid quotient compatible when the centroids themselves satisfy both generator equations (9.13), with the unweighted $\widehat B,\widehat A$ and the mean emissions. Then compatibility is equivalent to the two signed equalities

$$
\bar s_C E_C^B+\kappa_C^B=0\quad(\forall C),\qquad
\bar v_D E_D^A+\kappa_D^A=0\quad(\forall D).
\tag{12.8}
$$

Under these equalities the quotient's own generated complete laws are exactly $\bar Q_C,\bar W_D$. This concerns stationary centroids; it does not by itself preserve each old configuration's decoder or an arbitrary initial private row. It also does not require the original marginalized defects (12.5) to vanish. On every original positive fourth-phase history, the compatible quotient preserves the marginalized forecast and law-order loss, and its configuration-order loss is no greater than the old loss. Equality of centroids alone does not guarantee equality of the configuration-order loss.

At the p-$\beta$ interface, if $W_y=\bar W_{D(y)}$ for every $y$, then $E_C^B=0$ and compatibility at that interface is equivalent to $\kappa_C^B=0$. At suspended-$\alpha$, the dual hypothesis $Q_x=\bar Q_{C(x)}$ makes compatibility equivalent to $\kappa_D^A=0$. These are the within-cell successor-decoder agreement and zero signed-covariance criteria. Without the agreement hypothesis, (12.8) permits cancellation and neither error is separately forced to vanish.

Under the respective agreement hypothesis, the covariances have the exact coefficient expansions

$$
\kappa_C^B=\sum_D\operatorname{Cov}_{\omega_C}(s,b_{\cdot D})\bar W_D,
\qquad
\kappa_D^A=\sum_C\operatorname{Cov}_{\zeta_D}(v,a_{\cdot C})\bar Q_C.
\tag{12.9}
$$

Scalar covariance here is $\operatorname{Cov}_w(e,f)=\sum_iw_i(e_i-\bar e)f_i$. Each family of coefficients sums to zero. If the successor centroids in that expansion are affinely independent as measures, its signed covariance vanishes if and only if every displayed scalar coefficient vanishes. Without affine independence only the measure equality is necessary; equality of each coefficient is sufficient but need not be necessary.

A quotient preserving every old individual decoded law necessarily has $Q_x=\bar Q_{C(x)}$ and $W_y=\bar W_{D(y)}$. Preserving the acquired cell update from every private label, for arbitrary starting rows, additionally requires strong lumpability:

$$
b_{xD}=\widehat B_{CD}\quad(x\in C),\qquad
a_{yC}=\widehat A_{DC}\quad(y\in D).
\tag{12.10}
$$

Constant emissions within each source cell, together with (12.10) at both phases, are a supplied sufficient case for this stronger, configurationwise preservation. Constant emissions alone kill $\kappa$ but need not kill $E$ for an arbitrary partition. In the successor-agreement case, strong lumpability alone kills the respective coefficient covariances even when source-cell emissions vary.

Proof. Subtract (9.13), with centroids in place of its generated laws, from the averaged (9.12). Immediate completion masses already agree by the definition of the mean emissions. The remaining differences are the prefixed signed measures $\bar s_C E_C^B+\kappa_C^B$ and $\bar v_D E_D^A+\kappa_D^A$, by (12.4). Prefixing is injective, proving (12.8). If these differences vanish, compare the centroids with the quotient's own generated laws. Their maximum TV discrepancies $d_p,d_\beta$ obey $d_p\le(2/3)d_\beta$ and $d_\beta\le(2/5)d_p$, hence both are zero. Normalization and the zero noncompletion masses used here follow from the regular survival bound, not conditioning on completion. The old and quotient acquired rows are $\pi,\tau$ and $\bar\pi,\bar\tau$ on every original positive history. Since $\sum_C\bar\pi_C\bar Q_C=\sum_x\pi_xQ_x$ and likewise at suspension, their marginalized forecasts agree on that same record fiber. For the unchanged target $T_h^\mu$, TV convexity inside each cell bounds the quotient configuration loss by the original configuration average, whereas equality of the forecasts gives equality of the law loss. This does not move TV through the configuration average.

Successor agreement sets the relevant terms of (12.3) to zero. Grouping $H_x^B$ or $H_y^A$ by successor cell proves (12.9). Since $\sum_Db_{xD}=\sum_Ca_{yC}=1$, each coefficient sum is zero. Affine independence means exactly that a zero signed combination with coefficient sum zero has only zero coefficients, proving the coefficient criterion.

Configurationwise preservation forces decoder equality in each cell. Preserving the acquired cell transition for an initial point mass at any $x$ or $y$ forces (12.10); conversely (12.10) transports every private row by linearity and then every acquired word by induction. For the sufficient case, generate the quotient laws with the constant cell emissions. Compare each $Q_x,W_y$ with its cell's generated law. Strong lumpability groups the old successor weights into the same quotient rows, and the two maximum discrepancies again satisfy $d_p\le(2/3)d_\beta$, $d_\beta\le(2/5)d_p$. They vanish, establishing decoder agreement. This is the explicit two-phase use of the supplied strong-lumpability descent, not a new general lumpability theorem. ∎

**Theorem 12.4 (diameter and emission-oscillation bounds).** For the table and cells of Definition 12.1 put

$$
\begin{gathered}
\varepsilon_p=\max_C\max_{x,x'\in C}\operatorname{TV}(Q_x,Q_{x'}),\qquad
\varepsilon_\beta=\max_D\max_{y,y'\in D}\operatorname{TV}(W_y,W_{y'}),\\
\gamma_C^B=\max_{x,x'\in C}\operatorname{TV}(H_x^B,H_{x'}^B),\qquad
\gamma_D^A=\max_{y,y'\in D}\operatorname{TV}(H_y^A,H_{y'}^A),\\
o_C^u=\max_{x\in C}u_x-\min_{x\in C}u_x,\qquad
o_D^v=\max_{y\in D}v_y-\min_{y\in D}v_y.
\end{gathered}
\tag{12.11}
$$

A singleton diameter is zero. The exact identities imply

$$
\begin{aligned}
\|E_C^B\|_{\rm TV}&\le\varepsilon_\beta,&
\|\kappa_C^B\|_{\rm TV}&\le o_C^u\gamma_C^B/4,\\
\|E_D^A\|_{\rm TV}&\le\varepsilon_p,&
\|\kappa_D^A\|_{\rm TV}&\le o_D^v\gamma_D^A/4,\\
\operatorname{TV}(\operatorname{res}_\beta\bar Q_C,L_C^B)
 &\le\varepsilon_\beta+\frac{o_C^u\gamma_C^B}{4\bar s_C},\\
\operatorname{TV}(\operatorname{res}_\alpha\bar W_D,L_D^A)
 &\le\varepsilon_p+\frac{o_D^v\gamma_D^A}{4\bar v_D}.
\end{aligned}
\tag{12.12}
$$

The corresponding unconditioned generator discrepancies are bounded by

$$
\begin{aligned}
\operatorname{TV}\bigl(\bar Q_C,\bar u_C\delta_\alpha+\bar s_C\beta L_C^B\bigr)
 &\le\bar s_C\varepsilon_\beta+o_C^u\gamma_C^B/4,\\
\operatorname{TV}\bigl(\bar W_D,(1-\bar v_D)\delta_\beta+\bar v_D\alpha L_D^A\bigr)
 &\le\bar v_D\varepsilon_p+o_D^v\gamma_D^A/4.
\end{aligned}
\tag{12.13}
$$

In the reverse direction the first residual distance is at least $\max\{0,\|\kappa_C^B\|_{\rm TV}/\bar s_C-\varepsilon_\beta\}$, with the analogous suspended bound. Thus exact cancellation requires the normalized covariance norm to be no greater than the decoder-transport bound; an upper bound does not certify a positive defect or a positive risk gap. With successor agreement the residual distance is exactly $\|\kappa\|_{\rm TV}$ divided by its positive conditioning mass. All bounds compare complete laws for one fixed table and partition; they neither optimize over shapes nor establish a configuration-risk minimum.

Proof. Convexity bounds $\operatorname{TV}(W_y,\bar W_{D(y)})$ by $\varepsilon_\beta$ and its p analogue by $\varepsilon_p$. Averaging with the unweighted rows proves the two transport bounds. For a finite family $H_i$ with diameter $\gamma$, split the zero-sum coefficients $w_i(e_i-\bar e)$ into positive and negative parts. Their common total mass is $m=\frac12\sum_iw_i|e_i-\bar e|$. If $m=0$ the covariance is zero; otherwise it is $m$ times the difference of two convex mixtures of the $H_i$, whose TV is at most $\gamma$. If $e_i\in[a,b]$, convexity of $|e-\bar e|$ gives

$$
m\le\frac{(\bar e-a)(b-\bar e)}{b-a}\le\frac{b-a}{4}
\tag{12.14}
$$

when $b>a$, and $m=0$ when $b=a$. Apply this with $e=s$ or $v$; $s$ has the same oscillation as $u$. The triangle and reverse triangle inequalities in (12.4) prove (12.12) and its lower bounds. Immediate completion atoms agree, so the unconditioned discrepancies are exactly $\bar s_C$ and $\bar v_D$ times their residual distances. This proves (12.13). Taking $\gamma\le1$ recovers the covariance estimate (9.14); the extra successor-diameter factor identifies when emission variation has no continuation consequence. ∎

**Example 12.5 (exact calibration of the supplied passive counterexample).** Reuse the persistent-tag table of Proposition 6.1 on the original source of Definition 1.1, written as the period-one table

$$
X=Y=\{0,1\},\qquad \pi=\tau=(1/2,1/2),\qquad
B=A=I_2,\qquad u=v=(1/3,2/5).
\tag{12.15}
$$

It is a regular rational table. Its actual flow is exactly $\pi B=\tau$, $\tau A=\pi$, at every original positive history. Its individually generated complete laws are $Q_i=P_{p,r_{i+1}}$, $W_i=P_{\beta,r_{i+1}}$ for $i=0,1$. Nevertheless, at every original positive history in the relevant phase,

$$
\begin{aligned}
\delta(h,\beta)&=\frac1{38}\operatorname{TV}(W_0,W_1)
 =\frac{239}{128250}>\frac1{570}>0,\\
\delta(h,\alpha)&=\frac1{22}\operatorname{TV}(Q_0,Q_1)
 =\frac{1116529}{250593750}>\frac1{330}>0.
\end{aligned}
\tag{12.16}
$$

Proposition 6.1 already supplies this table and its qualitative positive defects; neither is counted as a new construction here. The exact calibration (12.16) instantiates both covariance interfaces. The table is a counterexample to deriving marginalized coherence from actual-flow identities and exact individual generation, not a lower bound for all tables, a new small-risk witness or a solution of Open question 8.2.

Proof. Identity updates hold the independently sampled label. The two equations (9.12) therefore expand to (1.2) with the fixed parameter $r_{i+1}$ at that label. This identifies the whole stopped law, including noncompletion with mass zero. The actual labels remain fair because acquired letters are emitted by the same source $K$, not by the private synthetic parameter. After synthetic p-$\beta$, the conditional label weights are $(10/19,9/19)$ instead; after synthetic suspended-$\alpha$ they are $(5/11,6/11)$. Subtracting the fair actual successor measures gives $(W_0-W_1)/38$ and $(Q_1-Q_0)/22$. Homogeneity of the signed TV norm proves the first expressions in (12.16).

For completeness these full-tail TV values can be computed without a truncation. Set $a_0=2/9$, $a_1=6/25$. On p branch $w_{j,0}$ the ratio of label-0 to label-1 masses is $(5/6)(25/27)^j<1$. On p branch $w_{j,1}$ it is $(100/81)(25/27)^j$, greater than one precisely for $j=0,1,2$. On suspended immediate $\beta$ the difference is positive; on suspended branch $\alpha w_{j,0}$ its ratio is $(25/36)(25/27)^j<1$, and on branch $\alpha w_{j,1}$ it is $(250/243)(25/27)^j$, greater than one only for $j=0$. The decreasing ratios and their boundary comparisons establish the signs for every $j\ge0$. Thus, using the positive part of a zero-mass signed measure,

$$
\begin{aligned}
\operatorname{TV}(Q_0,Q_1)
 &=\sum_{j=0}^2\left[\frac49\left(\frac29\right)^j-\frac9{25}\left(\frac6{25}\right)^j\right]
 =\frac{1116529}{11390625},\\
\operatorname{TV}(W_0,W_1)
 &=\left(\frac23-\frac35\right)+\left(\frac4{27}-\frac{18}{125}\right)
 =\frac{239}{3375}.
\end{aligned}
\tag{12.17}
$$

The immediate-successor events alone give $\operatorname{TV}(W_0,W_1)\ge1/15$ and $\operatorname{TV}(Q_0,Q_1)\ge1/15$, proving the weaker rational lower bounds as well. These calculations corroborate the supplied endpoint distances $2\rho_s$, rather than supplying new phase minima.

Install (12.15) by Lemma 2.1.1: before the latch retain the entire original $C_0$ and fair synthetic emission; the original third-completion update writes its complete record before latching and then samples the fair label in that same update. All paid rejected seed words, both accepted seeds, selectors, marker trees, bare fields, held $B,Q^+,Z$, permissions, finite return histories and matching Stop/delivery are retained. Completing letters clear the label. Synthetic execution applies the identical acquired identity kernels and original event blocks. Neither the already acquired suspended letter nor a second copy of a record is inserted into the future. The full carriers retain all unbounded legal continuations and noncompletion; no law is normalized on future completion.

All sampling probabilities have a common denominator 30. A represented sampler can use a five-bit candidate, reject candidates at least 30, and use finite thresholds; its bits, candidate, cursor, selectors, table, workspace and service program states are charged. Retries reuse finite storage and need no retained retry count. This gives exact probabilities and almost-sure service return, with no finite worst-case bit or work bound. $C_0$, all samplers, program/table data, addresses, output cursors and persistent randomness belong to COMPLETE, so two private labels do not mean two total states. The single common-depth provider, all actual Reads, fresh randomness, internal work, installation and offline mathematics, synthesis/output and any recipient archive have separate costs. There is no source reset, correlated source label, posterior port, clock, continuous register, free acquired history or post-Stop Read; pending/delivered menus are unchanged. These statements hold under every allowed installed prior, without changing it between histories or between phases. ∎

**Proposition 12.6 (restricted passive continuation-dispersion obstruction).** Restrict to finite period-one tables with $X=Y$, $B=A=I$, $\pi=\tau$, positive retained weights and regular emissions. No source or control reset is permitted. Then for every original positive history in the appropriate phase,

$$
\delta(h,\beta)\ge\frac{|\operatorname{Cov}_\pi(u,v)|}{\sum_x\pi_x(1-u_x)},\qquad
\delta(h,\alpha)\ge\frac{|\operatorname{Cov}_\pi(u,v)|}{\sum_x\pi_xv_x}.
\tag{12.18}
$$

In particular if, on this same table, $v_x=a+b u_x$ with $b\ge b_0>0$ and $\operatorname{Var}_\pi(u)\ge\sigma^2>0$, both emission vectors still in $[1/3,2/5]$, then

$$
\delta(h,\beta)\ge\frac32b_0\sigma^2,\qquad
\delta(h,\alpha)\ge\frac52b_0\sigma^2.
\tag{12.19}
$$

For a passive family satisfying fixed such floors, neither interface defect can tend to zero. For two positive labels of weights $\lambda,1-\lambda$, the numerator in (12.18) is exactly $\lambda(1-\lambda)|(u_0-u_1)(v_0-v_1)|$. Nonconstant emissions at both labels therefore prevent zero defect in this two-label passive class. The statement is a continuation-coherence obstruction with explicit dispersion hypotheses, not a positive conf/conf risk gap.

Proof. With identity kernels, $H_x^B=W_x$ and $H_x^A=Q_x$. On the suspended successor event consisting of immediate completion $\beta$, $W_x(\beta)=1-v_x$. Hence

$$
\kappa_X^B(\{\beta\})
=\operatorname{Cov}_\pi(1-u,1-v)=\operatorname{Cov}_\pi(u,v).
\tag{12.20}
$$

On the p successor event of immediate completion $\alpha$, $Q_x(\alpha)=u_x$, so $\kappa_Y^A(\{\alpha\})=\operatorname{Cov}_\pi(v,u)$. Evaluating the signed norms in (12.5) on these events proves (12.18). The affine relation gives $\operatorname{Cov}_\pi(u,v)=b\operatorname{Var}_\pi(u)$; the denominators are at most $2/3$ and $2/5$. This proves (12.19). Expanding the two-label covariance gives the displayed product, the scalar identity supplied by the repository's binary-mixture covariance certificate. All events and weights refer to the same realization, not to separately selected extrema. ∎

The passive hypothesis is material. For example $B_{xy}=\tau_y$ for every $x$ and $A_{yx}=\pi_x$ for every $y$ satisfy the same actual-flow equations but make $H_x^B$ and $H_y^A$ independent of their current labels. Both covariances in (12.5) then vanish even with nonconstant emissions. This is a charged private-label refresh within the original update, not a reset of $K$, $C_0$, records or paid histories; it illustrates why the passive bound cannot be transported to switching tables. It supplies no risk optimum. Without a variance or separation floor, even passive dispersion can tend to zero. Moreover the allowed full class has no zero-defect requirement: nonzero marginalized defect, as in Theorem 11.2, is compatible with very small simultaneous configuration excess.

## 13. Suppliers and the remaining common-realization obligation

**Mathematical correspondence 13.1 (what is reused and what is derived).** Definitions 1.1–2.1 and Lemma 2.1.1 supply the source, all original operations, full record rendering, complete stopped laws and exact same-update realization. Proposition 6.1 supplies the persistent-tag counterexample and the fact that both of its marginalized defects are positive. Equations (9.9)–(9.14) supply the flow quotient, generator equations and elementary oscillation estimate. The new bridge is the exact split (12.4) into unweighted decoder transport and emission selection, its distinction between centroid and configurationwise recovery, its coefficient test, and its scoped passive continuation obstruction. It is not another tuned positive-tolerance risk table.

The pinned repository declaration [DESC12, `stochastic_descent_equivalence`] characterizes exact descent of a PMF state kernel through its effective readout image by constancy of pushed-forward rows. To identify its acquired kernel here, take the disjoint union $X\sqcup Y$, send $X$ to $Y$ by $B$ and $Y$ to $X$ by $A$, and keep the phase in the readout together with its cell. Its row-constancy condition is exactly (12.10). It supplies the acquired quotient for arbitrary private rows, not the emission-weighted conditional residual in (12.6). [CF, Proposition 7.2] additionally requires equality of full decoded measures within each cell to preserve both risk orders on each history. That requirement explains why averaging unequal decoders is insufficient for a configurationwise recovery claim. The pinned scalar declaration [COV12, `binary_mixture_covariance_certificate`] supplies the two-label covariance product only. [STOP12, `actual_fourth_segment_stopped_word_law` and `actual_noncompletion_mass_zero`] supplies the fixed-parameter actual raw fourth-tail law, with $\alpha=0,\beta=1$; it does not identify an acquired posterior with a synthetic label row.

Geiger and Temmel, *Lumpings of Markov chains, entropy rate preservation, and higher-order lumpability*, [GT12] v6, Definition 7, separates a stationary weak lumping from a strong lumping valid for every initial distribution. Their Theorem 9 uses their stationary irreducible aperiodic setup to characterize strong higher-order lumpability by an entropy equality. Here the acquired disjoint-union chain alternates phases and can be reducible, including (12.15). No use of their entropy theorem on that chain is made; the relevant supplied distinction is the initial-row quantifier. Their hidden-state lumping concerns an observation of one Markov law. The present synthetic joint transition is instead $s_x B_{xy}$ or $v_y A_{yx}$, whereas acquired flow uses $B_{xy},A_{yx}$. The source-specific residual normalization in (12.6) is the missing correspondence, not a consequence of naming both chains hidden-state models.

Czaja, Jaming and Matolcsi, *An efficient algorithm for positive realizations*, [CJM12] v2, §1 and Lemma 2.1, concerns nonnegative realizations of a supplied scalar rational transfer function and lifting a realization of a shifted impulse-response sequence. In this table the p-word coordinates have the positive linear form $(H^ju)_x$ and $(H^jg)_x$, with $H=\operatorname{diag}(1-u)B\operatorname{diag}(v)A$ and $g=\operatorname{diag}(1-u)B(\mathbf1-v)$. Thus scalar nonnegative realization is a relevant supplier for an individual coefficient sequence. It does not impose this shared two-phase factorization, the regular emission interval, stochastic acquired $B,A$, or the separate unweighted identities $\pi B=\tau$, $\tau A=\pi$ on one common realization. The shift lemma supplies none of the original control/record or actual-history correspondences. No positive-system existence or dimension theorem is transferred to the EP common-risk problem without those additional obligations.

Van Rooyen and Williamson, *Le Cam meets LeCun: Deficiency and Generic Feature Learning*, [VRW12] v2, §§2–4, describes factorization of experiments by a stochastic channel and weighted directed deficiency as an infimum of average variational discrepancies; its randomization theorem compares optimized decision values over losses and priors. Its normalization is its own, and no numerical constant is transferred here. Our $E,\kappa$ are computed for one specified acquired-flow quotient and complete successor laws; no infimum over reconstructing channels is taken. Configuration-risk averages decoder TV before the phase/history supremum, while law-risk takes TV after mixing. Neither equals the optimized decision value or the prior-weighted experiment criterion merely by sharing TV vocabulary. These external suppliers do not provide one common finite EP endpoint model, a vanishing-excess family or an all-shape risk lower bound. No external originality or literature-priority claim is made for the ordinary derivations here.

**Boundary 13.2 (exact recovery and unrestricted alternatives).** Theorem 12.2 identifies the complete continuation relation that an unweighted acquired-flow quotient fails to transport. Proposition 12.3 gives an evaluated algebraic condition on a supplied finite table and partition: with (12.8), the same quotient recovers both complete centroid laws; without it, the exact signed residual and Theorem 12.4 bound its failure. This is a compatibility bridge on an already supplied common realization, not an existence theorem for the endpoint laws. Example 12.5 falsifies the inference that acquired circulation forces emission-weighted coherence. Proposition 12.6 obstructs zero coherence only in its specified passive class with its dispersion floors.

The unrestricted alternatives of Open question 8.2 remain separate. Finite exact endpoint attainment needs one finite same-update table attaining both complete configuration minima on every original positive history. Zero excess infimum without finite attainment needs a family on this same source and installed prior with simultaneous excess tending to zero and a separate nonattainment proof. A strictly positive unrestricted infimum needs an inequality valid over all finite switching shapes, or a proved risk-preserving reduction of that full union to a class carrying such an inequality. No such reduction to the passive class is supplied by (12.18); Corollary 2.3 reduces to stationary regular tables, which still allow switching and nonzero defect. Optima under fixed COMPLETE, precision, sampler, time or other budgets require their own representation and resource constraints. The private-cell quotient and complete-law estimates do not preserve a prescribed budget or identify a total-resource optimum.

For the persistent minimal-relation question, the attained bridge is precisely between generated continuation, acquired circulation and a finite cell boundary on each complete original record fiber. The current boundary and stationary cell weights recover a centroid future through a same-update quotient exactly under (12.8); recovering each configuration's future or transporting arbitrary private rows requires the stronger conditions stated in Proposition 12.3. This does not recover the actual chronology, erased paid rejection words, exact common-depth posterior or a free history from a finite cell. All write-before-latch, holding/delivery, legal menus, unbounded future and COMPLETE accounting remain those of the original source. No physical-spacetime, global completion, Lean/kernel verification, or completion of the persistent research objective follows from this ordinary mathematical unit.

[DESC12]: https://github.com/the-omega-institute/trureturing/blob/fb8045ef81325a141ed320e9cdffb423bba16776/D5/S3/Estimation/DecisionRisk/StochasticDescentEquivalence.lean
[COV12]: https://github.com/the-omega-institute/trureturing/blob/fb8045ef81325a141ed320e9cdffb423bba16776/D5/S3/ConceptDynamics/PartialIdentification/ConditionalMarkovianBenefitBoundary.lean
[STOP12]: https://github.com/the-omega-institute/trureturing/blob/fb8045ef81325a141ed320e9cdffb423bba16776/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.lean
[GT12]: https://arxiv.org/pdf/1212.4375v6
[CJM12]: https://arxiv.org/pdf/math/0612551v2
[VRW12]: https://arxiv.org/pdf/1402.4884v2

## 追加锚（本行以下为增补区）
