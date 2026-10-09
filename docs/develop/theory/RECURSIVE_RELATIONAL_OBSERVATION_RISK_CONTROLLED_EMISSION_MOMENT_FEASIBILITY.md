# Risk-controlled emission clipping and finite moment feasibility for the unchanged stopped Fibonacci source

## 1. Source, complete futures and common-model coordinates

**Definition 1.1 (unchanged source and legal cuts).** Fix $m=2,d=1,\ell=2,n=4$, and let $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$. A finite or countable prior $\mu$ on positive integers satisfies $\mu(1),\mu(2)>0$. A single $K$ is drawn before the first actual Read. Conditional on $K=k$, all actual letters are independent, each with $\alpha$ probability $r_k$ and $\beta$ probability $1-r_k$, where

$$
r_k=\frac{F_{k+1}}{F_{k+3}},\qquad r_1=\frac13,\quad r_2=\frac25,
\qquad \frac38\le r_k\le\frac5{13}\quad(k\ge3).
$$

The same $K$ supplies paid seed rejection and every payload. Equal seed pairs are rejected; $\alpha\beta$ accepts seed 0 and $\beta\alpha$ accepts seed 1. In segment $p_i$, $\alpha$ completes marker 0 and $\beta$ enters $q_{\beta,i}$. In $q_{\beta,i}$, $\alpha$ returns to $p_i$ and $\beta$ completes marker 1. The third record is written before its latch. Records remain held thereafter. Fourth completion enters the original pendingStop, whose unique Stop enters deliveredStop. Neither terminal admits Read.

The original finite control $C_0$ includes parser, seeds, selectors, bare fields, the complete marker tree, records, permissions, completion, pendingStop and deliveredStop. The history domain contains both seeds, every marker triple, all positive finite paid rejection histories and all positive finite payload return histories. $\mathcal H_3$ denotes the cut immediately after the third latch and before any fourth-segment Read; $\mathcal H_p$ and $\mathcal H_\beta$ are all positive finite fourth-segment p and suspended cuts after that latch. No source reset, new source query, future-event conditioning or post-Stop operation is admitted. These source conventions are those of [ST, §§1–2] and [FLOW, §2].

**Definition 1.2 (complete tail space).** For probability measures on a common measurable space, $\operatorname{TV}(P,Q)=\sup_E|P(E)-Q(E)|$; on a countable carrier this is half the $\ell^1$ distance. Put $a_r=r(1-r)$ and

$$
w_{j,0}=(\beta\alpha)^j\alpha,\qquad
w_{j,1}=(\beta\alpha)^j\beta\beta,\qquad j\ge0.
$$

At p, the finite raw futures are these words; at a suspended cut they are $\beta$ and $\alpha w_{j,b}$. Each phase also retains its unique infinite noncompletion word. The fixed-parameter laws are

$$
P_{p,r}(w_{j,0})=r a_r^j,\qquad
P_{p,r}(w_{j,1})=(1-r)^2a_r^j,
$$

$$
P_{\beta,r}(\beta)=1-r,\qquad
P_{\beta,r}(\alpha w_{j,0})=r^2a_r^j,\qquad
P_{\beta,r}(\alpha w_{j,1})=r(1-r)^2a_r^j.
\tag{1.1}
$$

Their infinite-word masses are zero. The original transcript map $I_c$ retains every future Read and produces its original records, control, permissions, completion and Stop events. Its inverse reads back the letters. It is a measurable bijection onto the legal transcript space and preserves TV [FLOW, Definition 2.4]. A suspended cut does not charge its already acquired $\beta$ as a future Read.

At an actual finite history $h$, the target is

$$
T_h^\mu=(I_c)_*\sum_k\nu_h(k)P_{s,r_k},\qquad
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
{\sum_t\mu(t)r_t^{A(h)}(1-r_t)^{B(h)}}.
\tag{1.2}
$$

The counts include every paid seed rejection, payload and partial parse. The posterior is an analysis coordinate, never a runtime input.

**Definition 1.3 (observer and risks).** An observer has a fixed finite COMPLETE configuration set, source-independent initialization, fixed time-homogeneous source-independent letter kernels, and a decoder reading only its actual configuration. COMPLETE includes $C_0$, selectors, tables, program, workspace, output indices and all persistent randomness. There is no uncounted clock, archive, advice, tape, model index, correlated source seed, continuous register or readable distribution vector.

A decoded law is the complete legal future generated from that configuration by its synthetic letter probabilities and the very same letter-update kernels used by actual acquired letters. Synthetic generation never queries the actual source. This per-configuration same-update condition is exact. The abstract real-kernel interpretation is the finite indexed stochastic rule of [FLOW, Definition 2.6]; it grants no numerical oracle or exact-real sampling device. Effective finite sampling is asserted only for separately specified effective tables.

For the configuration row $\rho_h$ after the same actual history, write

$$
Q_h=\sum_z\rho_h(z)D_z,
\quad e_{\rm law}(h)=\operatorname{TV}(Q_h,T_h^\mu),
\quad e_{\rm conf}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu).
$$

$R_j(\mathcal H_s)=\sup_{h\in\mathcal H_s}e_j(h)$, for $j\in\{\mathrm{law},\mathrm{conf}\}$. Actual-history-average error is a different quantity. The supplied separate minima are

$$
\rho_p=\frac{1116529}{22781250},\qquad
\rho_\beta=\frac{239}{6750}.
\tag{1.3}
$$

They apply to either risk order on its respective full phase domain [ST; PH, Theorem 2.1].

**Definition 1.4 (marginal update defect).** At an actual positive history, for a legal next operation $x$ with predicted probability $q_h(x)>0$, let $\operatorname{res}_xQ_h$ be the conditional law after deleting that operation and its original event block. Put

$$
\delta(h,x)=\operatorname{TV}(\operatorname{res}_xQ_h,Q_{hx}).
$$

If $q_h(x)=0$, set the defect to zero without creating a conditional law; the actual successor and its risk remain in the domain. $\Delta_4$ takes the supremum over all fourth-segment positive finite histories and legal next Reads; $\Delta_{\rm all}$ includes all original operations from initialization through deliveredStop. PendingStop has its unique zero-defect Stop successor, and the delivered empty supremum is zero. This is the convention of [PRICE, Definition 2.1]. It relaxes only marginalized conditioning/update coherence, not per-configuration generation.

**Mathematical citation 1.5 (terminal projection, finite witnesses and the endpoint-tag limitation).** The projection of a complete transcript to its terminal marker and Stop has the sharp risks $13/266$ at p and $9/266$ at suspension for both risk orders [ST, Theorems 2.1 and 3.1]. Projection contracts TV and does not recover the full-tail risks (1.3). The finite positive-history lower-bound witnesses of [ST, Theorem 2.1 and §§3.1–3.3] are supplied results; no acquisition-length optimization is included here.

The fair persistent endpoint-tag generator attains the full-tail minima when the prior has exactly the two endpoints, but its configuration-risk upper bound fails for the actual prior $(1/10000,1/10000,4999/5000)$ on $\{1,2,3\}$ at $h_0=\beta\alpha\mid\beta\beta\alpha\alpha$ [ST, equations (3.17)–(3.21)]. The complete word $(\beta\alpha)^3\beta\beta$ has actual conditional mass above both endpoint masses there. This is a counterexample to that generator's configuration-risk bound; it is neither an arbitrary-kernel obstruction nor a marginalized-risk violation. The phasewise full-prior minima in [PH, Theorem 2.1] and the three common combinations in [FOUR; SWITCH] retain their stated domains. The remaining common conf/conf problem permits arbitrary nonnative decoded laws.

## 2. Actual flow and finite table coordinates

**Definition 2.1 (periodic actual flow).** For a positive integer $d$ denoting an observer period, distinct from the fixed source parameter of Definition 1.1, let $X_i,Y_i$ be finite p and suspended label sets, with indices modulo $d$. There are probability rows $\pi_i,\tau_i$, row-stochastic actual kernels $B_i:X_i\to Y_i$, $A_i:Y_i\to X_{i+1}$, and synthetic $\alpha$ probabilities $u_i,v_i$, satisfying

$$
\pi_iB_i=\tau_i,\qquad \tau_iA_i=\pi_{i+1}.
\tag{2.1}
$$

All rows here are analysis coordinates. The installed machine samples $\pi_0$ source-independently in the same original update that writes the third record and then latches it. It uses $B_i$ after an actual p-$\beta$ and $A_i$ after an actual suspended-$\alpha$; the finite mode advances only in the suspended-$\alpha$ return update, in actual execution and in same-update synthetic generation. Completion clears the labels and retains the original pendingStop. Before the latch, synthetic letters are fair and the original updates are used. Both seeds and every current actual record use this same rule. The finite mode is a charged part of COMPLETE.

Put

$$
U_i=\operatorname{diag}(1-u_i),\quad V_i=\operatorname{diag}(v_i),
\quad H_i=U_iB_iV_iA_i,
\quad f_i=u_i,\quad g_i=U_iB_i(1-v_i).
\tag{2.2}
$$

For $j\ge0$, define

$$
Z_{i,b}^{(j)}=H_iH_{i+1}\cdots H_{i+j-1}t_{i+j,b},
\quad t_{i,0}=f_i,\quad t_{i,1}=g_i,
\tag{2.3}
$$

where an empty product is the identity. Then

$$
Q_{i,x}(w_{j,b})=Z_{i,b}^{(j)}(x),
$$

$$
W_{i,y}(\beta)=1-v_i(y),\qquad
W_{i,y}(\alpha w_{j,b})=(V_iA_iZ_{i+1,b}^{(j)})(y).
\tag{2.4}
$$

The remaining mass after $L$ returns is

$$
t_i^{(L)}=H_i\cdots H_{i+L-1}\mathbf1
$$

at p, and $V_iA_it_{i+1}^{(L)}$ after the suspended initial $\alpha$. The limits of these remaining masses include infinite noncompletion. Equations (2.2)–(2.4), rather than a posterior update, define the same-update decoder.

**Mathematical citation 2.2 (supplied comparison).** [FLOW, §3] supplies the following comparison for every observer of Definition 1.3. One periodic table of Definition 2.1 satisfies, simultaneously,

$$
R_j(\mathcal H_s;M^\circ)\le R_j(\mathcal H_s;M),
\qquad
\Delta_{\rm all}(M^\circ)=\Delta_4(M^\circ)\le\Delta_4(M).
\tag{2.5}
$$

For every mode and every $k$ with $\mu(k)>0$, its pure-target configuration risks are bounded by the corresponding original risks. The source, positive finite histories, current records and original control are unchanged. The comparison does not preserve a state or total-resource budget. Periodicization, finite-chain limits and actual circulation in this statement are supplied results.

**Proposition 2.3 (all-history interpretation of a table).** For every table of Definition 2.1,

$$
R_{\rm conf}(\mathcal H_p)=\sup_{i,k:\mu(k)>0}
\sum_x\pi_i(x)\operatorname{TV}(Q_{i,x},P_{p,r_k}),
\tag{2.6}
$$

and the analogous suspended formula uses $\tau_i,W_{i,y},P_{\beta,r_k}$. The law-order formulas use the TV of the corresponding mixture before taking this supremum. All four formulas belong to the same installed model. Its early and terminal defects are zero; its fourth defects depend only on the finitely many modes and the two noncompletion letters.

**Proof.** Conditional on any acquired fourth-segment history, the actual label row is exactly $\pi_i$ or $\tau_i$ by (2.1), independently of the actual posterior. Countable TV convexity and (1.2) give the upper bounds in (2.6) and its three companions.

For the converse use the paid rejection histories of [FLOW, equations (3.1)–(3.2)], followed by its fixed legal seed/marker suffix and a fixed number of returns giving mode $i$. For each supported $k$, the posterior tends to its pure depth while the table row is unchanged. These are finite positive histories in the same fixed prior; the supplied dominated-convergence argument includes every countable nonendpoint weight. TV is 1-Lipschitz in its target, so their risks approach the displayed pure-target risk. Current records and transcript maps preserve these comparisons.

The pre-latch label is fixed; the latch sampler is the same source-independent update in actual and synthetic generation. Therefore conditioning any positive pre-latch synthetic letter produces exactly the next report. Terminal residuals are the deterministic original Stop or empty future. In the fourth segment, conditioning a completing letter gives that same deterministic terminal residual. Only p-$\beta$ and suspended-$\alpha$ remain. ∎

For $\mathcal H_3$ alone, (2.6) uses mode 0 only. It does not become the supremum over all modes unless that extra equality is proved.

## 3. Quantitative clipping on the unchanged actual flow

**Theorem 3.1 (risk-controlled emission clipping).** Let $M$ be any observer of Definition 1.3. Set

$$
\varepsilon_p=R_{\rm conf}(\mathcal H_p;M)-\rho_p\ge0,
\qquad
\varepsilon_\beta=R_{\rm conf}(\mathcal H_\beta;M)-\rho_\beta\ge0.
$$

Use its supplied periodic comparison $M^\circ$. For a scalar $t$, write $[t]_{[a,b]}=\min\{b,\max\{a,t\}\}$. Replace only its emission entries by

$$
\widehat u_i=[u_i]_{[1/3,2/5]},\qquad
\widehat v_i=[v_i]_{[1/3,2/5]}.
\tag{3.1}
$$

The actual rows, actual letter kernels, mode rule, current records and source are unchanged. The resulting finite table $\widehat M$ has exact per-configuration same-update generation. Define

$$
T_p=\frac{30\varepsilon_p+20\varepsilon_\beta}{11},
\qquad
T_\beta=\frac{12\varepsilon_p+30\varepsilon_\beta}{11}.
\tag{3.2}
$$

At every same actual fourth-segment history, in either risk order,

$$
|e_j(h;\widehat M)-e_j(h;M^\circ)|\le T_s
\qquad(h\in\mathcal H_s).
\tag{3.3}
$$

Consequently, simultaneously for all four coordinates, $R_j(\mathcal H_s;\widehat M)\le R_j(\mathcal H_s;M)+T_s$. In particular the same model satisfies

$$
R_{\rm conf}(\mathcal H_p;\widehat M)
\le\rho_p+\frac{41\varepsilon_p+20\varepsilon_\beta}{11},
$$

$$
R_{\rm conf}(\mathcal H_\beta;\widehat M)
\le\rho_\beta+\frac{12\varepsilon_p+41\varepsilon_\beta}{11}.
\tag{3.4}
$$

If $\max(\varepsilon_p,\varepsilon_\beta)<1/6$, then

$$
\Delta_{\rm all}(\widehat M)=\Delta_4(\widehat M)
\le\Delta_4(M)+
\max\left\{\frac{10}{3}T_p+T_\beta,\ T_p+6T_\beta\right\}.
\tag{3.5}
$$

If both excesses are at most $e<1/6$, the additional defect is at most $302e/11$.

**Proof.** On either complete countable phase space, for endpoint laws $P_1,P_2$ and any law $D$, the coordinate absolute-value identity gives

$$
\operatorname{TV}(D,P_1)+\operatorname{TV}(D,P_2)-2\rho_s
=\sum_w\operatorname{dist}(D(w),[P_1(w)\wedge P_2(w),P_1(w)\vee P_2(w)]).
\tag{3.6}
$$

This includes the infinite word. Its use at exact endpoint equality is supplied by [NATIVE, equation (6.4); FLOW, equation (7.2)]. Here apply it to each mode's configuration expectation with the two pure-target bounds in Citation 2.2. The single p word $\alpha$ has probability $u_i(x)$; the single suspended word $\beta$ has probability $1-v_i(y)$. Consequently

$$
D_{u,i}:=\pi_i|u_i-\widehat u_i|\le2\varepsilon_p,
\qquad
D_{v,i}:=\tau_i|v_i-\widehat v_i|\le2\varepsilon_\beta.
\tag{3.7}
$$

Indeed the two expected endpoint distances at mode $i$ sum to at most $2\rho_s+2\varepsilon_s$; their nonnegative coordinate excesses in (3.6) therefore have total at most $2\varepsilon_s$. Each of the indicated single-word excesses is bounded by this total. No assertion that every configuration is individually close to a center is used.

Let $\widehat H_i$ be the clipped return mass kernel and $C_i=B_iA_i$ the actual return kernel. Entrywise,

$$
0\le\widehat H_i\le\lambda C_i,
\qquad \lambda=\frac4{15},
\qquad \pi_i C_i=\pi_{i+1}.
\tag{3.8}
$$

Couple old and clipped synthetic letters maximally while their configurations agree; after a matched letter couple their identical actual-update row identically. At a p step the mismatch probability is $|u-\widehat u|$, and at a suspended step it is $|v-\widehat v|$. The probability that the coupled paths are still identical is dominated by the clipped survival subprobability. From $\pi_i$, (3.8) bounds its p row at the $j$th return by $\lambda^j\pi_{i+j}$, and its suspended row by $(2/3)\lambda^j\tau_{i+j}$.

The clipped generator completes almost surely. Summing the mismatch hazards up to that completion, including all possible return lengths, gives

$$
\sum_x\pi_i(x)\operatorname{TV}(Q_{i,x},\widehat Q_{i,x})
\le\sum_{j\ge0}\lambda^j\left(D_{u,i+j}+\frac23D_{v,i+j}\right)
\le T_p.
\tag{3.9}
$$

Starting at a suspended row, its first mismatch hazard is $D_{v,i}$. A matched initial $\alpha$ gives a p subrow bounded by $(2/5)\pi_{i+1}$. Thus

$$
\sum_y\tau_i(y)\operatorname{TV}(W_{i,y},\widehat W_{i,y})
\le D_{v,i}+\frac25T_p\le T_\beta.
\tag{3.10}
$$

The last inequality is the identity $2\varepsilon_\beta+(2/5)T_p=T_\beta$. The coupling bounds also cover possible old infinite noncompletion: on no mismatch the old path completes with the clipped one. Stepwise coupling is a mature tool [ART, §3.2]; the stationary actual-flow domination (3.8) and the endpoint-risk control (3.7) are the source-specific ingredients.

The actual rows have not changed at any acquired history. The triangle inequality, convexity for the law order, and (3.9)–(3.10) therefore prove (3.3) on every positive history, irrespective of its length or posterior. Combine it with (2.5) to obtain (3.4).

For the defect, the old p-$\beta$ probability is at least $3/5-D_{u,i}>0$, and its old suspended-$\alpha$ probability is at least $1/3-D_{v,i}>0$ under the stated excess bound. The corresponding clipped probabilities are at least $3/5$ and $1/3$. For probability laws at TV distance at most $t$, conditioning on a common positive event whose second-law probability is at least $q$ changes the conditional law by at most $2t/q$. For the old law $P$, clipped law $Q$ and any event $A$, the difference after conditioning on $E$ is

$$
\frac{P(A\cap E)}{P(E)}-\frac{Q(A\cap E)}{Q(E)}
=\frac{P(A\cap E)-Q(A\cap E)}{Q(E)}
+\frac{P(A\cap E)}{P(E)}\frac{Q(E)-P(E)}{Q(E)}.
$$

Both terms are bounded by $t/Q(E)$, proving the estimate for every conditional event. Deleting the original operation block contracts TV. Apply this estimate to the old and clipped marginal forecasts, then use the next-cut forecast differences $T_\beta,T_p$ from (3.9)–(3.10). This gives $10T_p/3+T_\beta$ and $6T_\beta+T_p$. Completing letters and terminals have zero defect in both models. Proposition 2.3 covers earlier histories, proving (3.5). Substitution of $T_p\le50e/11,T_\beta\le42e/11$ gives $302e/11$. ∎

**Proposition 3.2 (tail, actions and resource bridge).** The clipped table has zero infinite noncompletion mass. From every p configuration its probability of at least $L$ returns is at most $(4/15)^L$; from a suspended configuration its probability of an initial $\alpha$ followed by at least $L$ returns is at most $(2/5)(4/15)^L$. Its expected future synthetic Read counts are at most $25/11$ and $21/11$, respectively.

Clipping adds no returned-cut mode or label. If the supplied periodic comparison uses $d$ modes and fiber sizes $n,m$, the macro returned-cut carrier can be allocated within $|C_0|(1+d(n+m))$ configurations. For an original return-state bound $N$, [FLOW, §7] permits $n+m\le N$ and $d\le\operatorname{lcm}(1,\ldots,N)$ in this bound. This is an allocation bound, not preservation of $N$ or of total COMPLETE cost.

For a rational installed table, clipped emissions remain rational; their denominator bounds increase only to include 3 and 5. The same actual-update samplers, initialization and charged program structure can be retained, with any necessary sampler workspace charged. Arbitrary abstract real kernel entries remain mathematical constants of the original parameter class; this statement provides no exact-real oracle or universal finite-bit sampler.

**Proof.** The first two assertions follow from (3.8). At p, each return block contributes at most $1+2/3$ expected Reads times its survival probability, hence $(5/3)/(1-4/15)=25/11$. At suspension the initial Read contributes one and an $\alpha$ continuation contributes at most $(2/5)(25/11)$, giving $21/11$.

The table replacement in (3.1) changes neither (2.1) nor any actual letter transition. Coupling the actual executions of $M^\circ$ and $\widehat M$ with the same source letters, initialization and actual-update randomness gives the same macro label/mode trajectory, original records, permissions and paid Read/Stop counts. The changed synthetic forecasts do not become additional source queries. A mode, label and current original control are sufficient macro fields for Definition 2.1. Early and terminal controls use no active label, giving the displayed generous allocation. The stated bound on $d$ is the supplied finite-chain period bound, not an additional clock. Rational clipping replaces an out-of-range emission by one of two rational endpoints; the other entries are retained. Finite rational categorical sampling, its workspace and canonical returned cut are as in [FLOW, §8]. No new actual source call or persistent random tape is required. Private sampler microstates and workspace belong to COMPLETE; these risk and defect bounds concern the original returned Read/Stop cuts and add no microstate query. The random-bit count, total output, time, table description, source acquisition, held records and physical costs remain separate accounts; the expected Read bounds are not finite worst-case bounds. ∎

## 4. Exact attainment, zero excess and positive gaps

**Definition 4.1 (regular periodic class).** $\mathfrak E_\mu$ is the union of all finite periodic tables of Definition 2.1 with every $u_i,v_i\in[1/3,2/5]$, installed with the original source and controls. Let $\mathfrak M_\mu$ be the full class of Definition 1.3, and put

$$
J(\mathfrak A)=\inf_{M\in\mathfrak A}
\max\{R_{\rm conf}(\mathcal H_p;M)-\rho_p,
R_{\rm conf}(\mathcal H_\beta;M)-\rho_\beta\}.
\tag{4.1}
$$

**Theorem 4.2 (equivalence at the joint endpoint and at zero excess).** For each allowed finite or countable prior:

1. A common conf/conf endpoint model exists in $\mathfrak M_\mu$ if and only if one exists in $\mathfrak E_\mu$. This equivalence also preserves a specified defect bound $\Delta_4\le D$ at exact attainment.
2. The two joint infima satisfy

$$
J(\mathfrak M_\mu)\le J(\mathfrak E_\mu)
\le\frac{61}{11}J(\mathfrak M_\mu).
\tag{4.2}
$$

Thus zero excess infimum and strictly positive joint gap are each equivalent between these two classes.
3. If a full-class sequence has both excesses tending to zero and $\limsup\Delta_4\le D$, a regular periodic sequence has the same properties. A hard per-model bound $\Delta_4\le D$ along the approximating sequence is not asserted.

**Proof.** At exact attainment, (3.7) vanishes. Clipping changes no positive-row emission, hence no positive-row complete law or defect. The supplied comparison and (3.5) prove the forward part of assertion 1; the reverse part is class inclusion. Zero-row labels can be deleted because (2.1) prevents positive actual flow into them.

For assertion 2, class inclusion gives the first inequality. Given any full-class model with maximal excess $e$, Theorem 3.1 gives a regular periodic model with maximal excess at most $61e/11$. Take the infimum; no optimizer is presumed. For assertion 3 eventually $e<1/6$, and (3.5) adds a quantity tending to zero. ∎

The theorem distinguishes exact attainment from an unattained zero infimum. It gives no value for either infimum. The rational five-coordinate closure of [FLOW, Theorem 6.1] can be composed with rational clipping to approach the same zero-excess regime using paid rational tables, with vanishing additional defect. It does not give a rational exact endpoint model or preservation of a closed defect boundary at every approximation.

## 5. Finite complete-word moments and explicit residual bounds

**Definition 5.1 (finite complete-tail partition).** At p, $\mathcal P_{p,L}$ distinguishes $w_{j,0},w_{j,1}$ for $0\le j<L$ and places every other outcome, including infinite noncompletion, into a single residual cell. At suspension, $\mathcal P_{\beta,L}$ also distinguishes $\beta$ and $\alpha w_{j,b}$ for $0\le j<L$, with one residual cell. These are mathematical partitions of the original legal tail, not added runtime operations.

Let $z_{i,x}^{p,L}$ be the probability vector of $Q_{i,x}$ on this partition: its entries are (2.3) and $t_i^{(L)}(x)$. Let $z_{i,y}^{\beta,L}$ be its suspended counterpart using (2.4) and $V_iA_it_{i+1}^{(L)}$. The corresponding actual vectors $p_{s,r}^{L}$ are given by (1.1) and residual masses $a_r^L,r a_r^L$.

For $s=p,\beta$, define the finite configuration and law errors

$$
F_{p,i,L}(r)=\frac12\sum_x\pi_i(x)\|z_{i,x}^{p,L}-p_{p,r}^{L}\|_1,
$$

$$
G_{p,i,L}(r)=\frac12\left\|\sum_x\pi_i(x)z_{i,x}^{p,L}-p_{p,r}^{L}\right\|_1,
\tag{5.1}
$$

and likewise with $\tau_i,z^{\beta,L}$. Write $F_{s,i}(r),G_{s,i}(r)$ for their complete-tail counterparts.

**Theorem 5.2 (uniform risk and defect certificates).** For every regular periodic table, every mode and every $r\in[1/3,2/5]$, put $b=6/25$. Then

$$
0\le F_{p,i}(r)-F_{p,i,L}(r)\le b^L,
\qquad
0\le F_{\beta,i}(r)-F_{\beta,i,L}(r)\le\frac25b^L.
\tag{5.2}
$$

The same inequalities hold for $G$. For the marginalized noncompletion-letter defects, their finite-partition values $D_{i,L}^{p\beta},D_{i,L}^{\beta\alpha}$ satisfy

$$
0\le D_i^{p\beta}-D_{i,L}^{p\beta}\le\frac25\lambda^L,
\qquad
0\le D_i^{\beta\alpha}-D_{i,L}^{\beta\alpha}\le\lambda^L,
\quad\lambda=\frac4{15}.
\tag{5.3}
$$

Every quantity on the left of these finite certificates uses the same table, actual flow and prior domain.

**Proof.** If a partition leaves one residual cell of masses $a,c$, refining that cell increases TV by at most $\min(a,c)$: its additional half-$\ell^1$ contribution is at most $[(a+c)-|a-c|]/2$. At p the actual residual mass is $a_r^L\le b^L$; at suspension it is $r a_r^L\le(2/5)b^L$. Apply the bound configurationwise and then average; mixtures obey the same bound. This proves (5.2), including any infinite outcome in the residual cell.

For clarity, the conditional label rows involved in (5.3) are

$$
q_i=\pi_i(1-u_i)\ge\frac35,
\qquad \gamma_i=\frac{\pi_iU_iB_i}{q_i},
$$

$$
a_i^{\rm first}=\tau_i v_i\ge\frac13,
\qquad \eta_i=\frac{\tau_iV_iA_i}{a_i^{\rm first}}.
\tag{5.4}
$$

The p-$\beta$ conditional residual is $\sum_y\gamma_i(y)W_{i,y}$; its actual successor report is $\sum_y\tau_i(y)W_{i,y}$. The suspended-$\alpha$ residual and actual successor use $\eta_i$ and $\pi_{i+1}$ on $Q_{i+1,x}$. In particular the finite-partition defects are exactly

$$
\begin{aligned}
D_{i,L}^{p\beta}
&=\frac12\left\|\sum_y(\gamma_i(y)-\tau_i(y))z_{i,y}^{\beta,L}\right\|_1,\\
D_{i,L}^{\beta\alpha}
&=\frac12\left\|\sum_x(\eta_i(x)-\pi_{i+1}(x))z_{i+1,x}^{p,L}\right\|_1.
\end{aligned}
\tag{5.4a}
$$

These formulas define both finite values directly from the common table. Every suspended law has residual mass at most $(2/5)\lambda^L$, and every p law at most $\lambda^L$, by Proposition 3.2. Apply the residual-cell inequality to these pairs of mixtures. ∎

**Proposition 5.3 (finite support nets for arbitrary countable priors).** Let $r_*=(3-\sqrt5)/2$ and $c=25/64$. Then

$$
|r_k-r_*|\le\frac1{15}c^{k-1},
\tag{5.5}
$$

and for any two parameters in $[1/3,2/5]$,

$$
\operatorname{TV}(P_{p,r},P_{p,t})\le\frac{125}{57}|r-t|,
\qquad
\operatorname{TV}(P_{\beta,r},P_{\beta,t})\le\frac{107}{57}|r-t|.
\tag{5.6}
$$

If the actual support is infinite, define

$$
S_M=\{r_k:k\le M,\ \mu(k)>0\}\cup\{r_*\}.
\tag{5.7}
$$

The limit point is a necessary target by continuity, not a new actual depth or acquired history. The supremum over actual supported targets in Proposition 2.3 differs from the maximum over $S_M$ by at most

$$
\zeta_{p,M}=\frac{25}{171}c^M,
\qquad
\zeta_{\beta,M}=\frac{107}{855}c^M,
\tag{5.8}
$$

for either risk order. For finite support, use its entire finite set and set both $\zeta$ to zero. For a support without an effective presentation, these finite sets are mathematical data; no support-membership algorithm or runtime prior oracle is supplied.

**Proof.** Fibonacci recurrence gives $r_{k+1}=(1-r_k)/(2-r_k)$. Its derivative magnitude on the interval is at most $25/64$; its fixed point is $r_*$. The initial distance is at most the interval width $1/15$, proving (5.5).

Couple two iid synthetic source-letter streams with mismatch probability $|r-t|$ at each Read until the original parser completes. At parameter $r$, the expected p Read count is $(2-r)/(1-a_r)\le125/57$ and the suspended count is $1+r(2-r)/(1-a_r)\le107/57$. The union bound on mismatch before completion gives (5.6). This is a proof coupling, not an actual source experiment.

Distance to a fixed decoded law is 1-Lipschitz in the target; the same holds after configuration averaging or forecast marginalization. Infinite supported Fibonacci parameters approach $r_*$, so their risk supremum includes its limiting risk. Each omitted $k>M$ lies within $c^M/15$ of it. Multiply this distance by (5.6). ∎

## 6. A finite polynomial family with a common realization

**Definition 6.1 (fixed shape and finite feasibility family).** Fix $d$, positive integers $n_i=|X_i|,m_i=|Y_i|$, and a defect budget $D\in[0,1]$. A shape is this finite list, including its mode successor relation. Its variables are the entries of

$$
(\pi_i,\tau_i,B_i,A_i,u_i,v_i)_{i\bmod d}.
$$

All probability entries are nonnegative, all required row sums are one, (2.1) holds, and $1/3\le u_i,v_i\le2/5$. Zero-row labels are allowed in the parameter space. There is no source-dependent entry or runtime posterior variable.

At level $L\ge1$, take $S_L$ from (5.7) for infinite support, or the whole finite support. Define $\mathcal F_L(D)$ by the preceding flow constraints and, for every mode and every $r\in S_L$,

$$
F_{p,i,L}(r)\le\rho_p,
\qquad F_{\beta,i,L}(r)\le\rho_\beta,
\tag{6.1}
$$

$$
D_{i,L}^{p\beta}\le D,
\qquad D_{i,L}^{\beta\alpha}\le D.
\tag{6.2}
$$

Each of these is a finite system of polynomial equalities and inequalities with auxiliary variables for absolute values. The only denominators in defect expressions are $q_i$ and $a_i^{\rm first}$ from (5.4); they are positive and can be cleared. Coefficients are rational, except for the explicitly algebraic $r_*$ when used. This family is a finite nonlinear moment family at each level, not a single polytope.

A finite level can additionally impose the necessary endpoint moment equalities

$$
\pi_i\bigl(g_i+H_ig_{i+1}+H_iH_{i+1}g_{i+2}\bigr)
=C_p:=\frac{11758471}{22781250},
$$

$$
\tau_i\bigl(1-v_i+V_iA_ig_{i+1}\bigr)
=C_\beta:=\frac{5261}{6750},
\tag{6.3}
$$

and the positive-row endpoint coordinate boxes for the complete words already represented at that level. For example each box can be written without strict positivity as

$$
\pi_i(x)(Z_{i,b}^{(j)}(x)-\ell_{p,j,b})\ge0,
\qquad
\pi_i(x)(u_{p,j,b}-Z_{i,b}^{(j)}(x))\ge0,
\tag{6.4}
$$

where $\ell,u$ are the smaller and larger endpoint masses; suspended boxes use $\tau_i$. These additions do not change the infinite intersection's endpoint solutions.

**Theorem 6.2 (exact fixed-shape completeness and quantified finite soundness).** For a fixed shape, a regular periodic common model with

$$
R_{\rm conf}(\mathcal H_p)=\rho_p,
\qquad R_{\rm conf}(\mathcal H_\beta)=\rho_\beta,
\qquad \Delta_{\rm all}=\Delta_4\le D
\tag{6.5}
$$

exists if and only if $\mathcal F_L(D)$ is nonempty for every $L$. The statement remains true with the additions (6.3)–(6.4).

Every point of a finite level itself defines one lawful abstract finite common observer with

$$
R_{\rm conf}(\mathcal H_p)\le\rho_p+b^L+\zeta_{p,L},
$$

$$
R_{\rm conf}(\mathcal H_\beta)\le\rho_\beta+\frac25b^L+\zeta_{\beta,L},
\qquad
\Delta_{\rm all}=\Delta_4\le D+\lambda^L.
\tag{6.6}
$$

These are bounds on every original positive finite history; no finite observation grid is promoted to an exact endpoint certificate.

**Proof.** Finite-word entries in (2.3)–(2.4) and residual entries are finite products of the same table variables. Clearing the positive denominators in (5.4), and expressing an absolute value by a bounded nonnegative auxiliary variable dominating both signs, yields the stated finite polynomial description. The variables for absolute values are existential and may be chosen equal to the absolute values; they introduce no additional runtime data. The auxiliary variables can be bounded in $[0,1]$: finite probability differences have absolute value at most one, and after clearing a conditional denominator the corresponding difference is at most that denominator, also at most one. The base table parameter space is compact. Each level, viewed as a set of tables admitting such auxiliary variables, is a compact projection of a closed bounded polynomial set and hence is closed.

The partitions refine with $L$, so finite TV values increase. The target sets $S_L$ increase. Thus these closed feasible sets are nested. If every level is nonempty, compactness gives one common table in their intersection. For each supported parameter and mode, Theorem 5.2 and Proposition 5.3 send (6.1) to the full configuration-risk bounds. They send (6.2) to the full defects. Proposition 2.3 then supplies all actual histories, and the separate lower bounds (1.3) force equality. Definition 2.1 installs this table before the first actual Read, with its charged mode and original controls.

Conversely any table satisfying (6.5) satisfies every finite-partition inequality. If the support is infinite, (5.6) includes the limiting target $r_*$. To justify the optional constraints, endpoint equality and (3.6) put every positive-row law in its complete endpoint coordinate box. At p, the endpoint-positive difference event is $E_p=\{w_{0,1},w_{1,1},w_{2,1}\}$; at suspension it is $E_\beta=\{\beta,\alpha w_{0,1}\}$, with endpoint 1 minus endpoint 2 in both cases. Endpoint risk equality centers their average masses at the endpoint midpoint. Direct substitution of (1.1) gives $P_{p,r_1}(E_p)=412/729$, $P_{p,r_2}(E_p)=7299/15625$, $P_{\beta,r_1}(E_\beta)=22/27$ and $P_{\beta,r_2}(E_\beta)=93/125$. Their respective arithmetic midpoints are the two constants in (6.3). All partial boxes (6.4) follow. These are moment constraints on the same complete generator, not separate optimum witnesses.

Finally (5.2), (5.3), (5.8) and Proposition 2.3 prove (6.6) for each finite feasible table. ∎

**Proposition 6.3 (finite risk minima at a fixed charged shape).** Omit a defect restriction and the optional exact-endpoint constraints. For a fixed regular shape let

$$
J_{\rm shape}=\min_{\rm tables}\max\{R_{\rm conf}(\mathcal H_p)-\rho_p,
R_{\rm conf}(\mathcal H_\beta)-\rho_\beta\}.
$$

Let $j_L$ be the finite polynomial minimum replacing the full risks by $\max_{i,r\in S_L}F_{s,i,L}(r)$. Then

$$
0\le J_{\rm shape}-j_L
\le\max\left\{b^L+\zeta_{p,L},\ \frac25b^L+\zeta_{\beta,L}\right\}.
\tag{6.7}
$$

The finite value $j_L$ is allowed to be negative because partitioning lowers the risks. In particular a proved $j_L>0$ is a positive-gap certificate for this whole fixed shape, not merely for sampled parameter values.

**Proof.** Theorem 5.2 and Proposition 5.3 bound, uniformly over all table parameters, the difference of each full risk and its finite expression by the displayed errors. Each finite expression is continuous on the compact table space. The full expression is its uniform limit, hence continuous and attains its minimum. Taking the maximum and then the minimum preserves the uniform bound. ∎

**Definition 6.4 (remaining unrestricted quantifier).** By Theorem 4.2, full-class endpoint attainment with defect bound $D$ is equivalent to

$$
\exists\text{ one finite shape }\quad
\forall L\ge1:\ \mathcal F_L(D)\ne\varnothing.
\tag{6.8}
$$

The fixed-shape theorem does not license interchanging this with $\forall L\,\exists$ a finite shape; the reverse implication from that weaker pattern is unproved. It gives no uniform cutoff in $L$, no universal finite state bound and no all-shape infeasibility certificate. Excluding one shape or every fixed finite grid does not establish full-class nonattainment or a positive gap. Equation (6.7) concerns a fixed charged macro shape; it is not a total-program, sampler-workspace or physical-resource optimum.

The finite vectors in Definition 5.1 also give the law-order coordinates $G$ on the same table. Thus all four phase/risk coordinates can be compared without joining different models or posteriors. The common conf/conf feasibility claim (6.8) makes no new attainment assertion for the other three combinations, which are supplied by [FOUR], [SWITCH] and the two-endpoint case of [ST].

## 7. Bounded semantic whitebox information and source correspondence

**Definition 7.1 (task-relative quality).** For either risk order set $W_j(\mathcal H_s)=1-R_j(\mathcal H_s)$. A finite semantic certificate consists of a table of Definition 2.1, its current original control, the selected finite complete-tail partition and all four common-model risk coordinates. It is a finite law description, not a readable hidden distribution or a claim about a trained network's implementation.

**Corollary 7.1.1 (quality of one common clipped model).** Under Theorem 3.1, the same clipped table satisfies $W_j(\mathcal H_s;\widehat M)\ge W_j(\mathcal H_s;M)-T_s$ for both phases and both risk orders, with the simultaneous defect bound (3.5). These are semantic task coordinates on the same actual source and positive histories; they do not determine internal program structure.

**Proof.** Subtract the simultaneous four risk bounds of Theorem 3.1 from one. The defect is that of the same clipped table. ∎

**Proposition 7.2 (same finite observation, different lawful complete future).** For every $L\ge1$ there is one rational finite COMPLETE observer on the unchanged source, with emissions in $[1/3,2/5]$, and two positive-probability configurations at the same actual $\mathcal H_3$ history, such that their $\mathcal P_{p,L}$ law vectors agree but their complete decoded laws differ. Any decoder forced to give the same complete law to these two finite observations has maximum error at least

$$
\frac1{30}\left(\frac29\right)^L.
\tag{7.1}
$$

This observer is not claimed to attain the endpoint minima.

**Proof.** At the third latch, independently sample a persistent bit $J\in\{0,1\}$ fairly and set a charged return mode to zero. Use $L+1$ modes cyclically, incremented only by the actual suspended-$\alpha$ return; both actual noncompletion updates preserve $J$. Let all suspended emissions be $1/3$. Let all p emissions be $1/3$, except that at mode $L$ the $J=1$ emission is $2/5$. Synthetic generation uses precisely these same updates; earlier stages and current records follow Definition 1.1.

At initial mode zero the two laws have the same complete-word probabilities for $j<L$ and the same residual mass $(2/9)^L$. They therefore have the same finite-partition observation. But the probabilities of $w_{L,0}$ are $(2/9)^L/3$ and $2(2/9)^L/5$. Their difference is $(2/9)^L/15$, so their complete-law TV is at least this amount. The triangle inequality gives (7.1) for any common law. Both configurations occur at the same actual latch history with positive observer probability. The bit, mode, table and sampler workspace are charged. All actual finite return histories remain available; no clock advance, source reset or added source observation is used. ∎

**Interface 7.3 (bounded transfer from a different source).** This is a bounded instantiation of the supplied joint reply/successor/cost criterion [A, §19; B, Interface B-20.2]. Fix one installed source/prior, one finite observer and a prescribed finite future horizon in a different source/control system. An interpretation maps its acquired histories, charged observer configurations and original controls into the table system of Definition 2.1. The following are sufficient correspondence conditions.

The interpretation preserves the source's actual conditional reply kernel at each corresponding positive acquired history, the source-independent observer initializer, and the entire joint observer kernel of reply, successor configuration, original event block and charged cost. It intertwines both actual letter updates and the synthetic joint kernels $q_z(x)P_x(z,z')$; thus each individual decoded law, before averaging over configurations, maps to the interpreted same-update law. It preserves enabled and rejected operations, completing branches, the unique Stop and delivered permissions. For each compared actual cut its transcript map is a measurable TV isometry on the selected future partition and commutes with conditioning a positive next-letter event and deleting its original block. The interpreted emissions obey Definition 4.1, and the actual rows obey (2.1).

Under these conditions the finite law/conf errors and conditioning defects agree at corresponding histories. Their suprema agree on the corresponding image domains; equality to the interpreted table's unrestricted history suprema additionally requires that every compared table history be represented. A table upper bound valid on every history transfers to any such image domain. A complete-tail transfer further requires a compatible family of transcript maps on refining partitions that determines the complete legal transcript, with the residual bounds in Theorem 5.2 on both sides. A single finite-horizon map provides no complete-tail conclusion.

**Proof.** Starting with the corresponding initial laws, induction on legal words preserves the same actual joint reply/successor/control/cost law and therefore the corresponding actual configuration row and target partition law. The synthetic-kernel intertwining gives the corresponding finite generated law separately for each configuration. The per-cut TV isometry first preserves each configuration's distance to its own actual target; averaging with the corresponding actual row preserves conf error. Applying it after this averaging preserves law error. The conditioning correspondence preserves the predicted next-letter probabilities and conditional residuals, including the zero-probability convention, while the successor-row correspondence preserves the next report. It therefore preserves the finite defects. Taking suprema gives the stated image-domain conclusion and explains the extra coverage condition for equality on the unrestricted domain.

For the compatible refining family, Theorem 5.2 bounds the difference between each finite-partition quantity and its full-tail value uniformly. Let the partition level tend to infinity in the finite equalities. The generating transcript correspondence and vanishing residuals identify the complete stopped laws and pass their TV errors and defects to the limit. No individual marginal equality substitutes for the joint-kernel induction or the per-configuration obligation. ∎

The FIB five-mode source in [A, Definitions A-1.1–A-1.3] has ordered tree selection, composition, numerical replies and legal continuation guards. Its five modes are not the p/suspended prediction configurations in Definition 2.1. Its task-fiber criterion [A, §19; B, Interface B-20.2] concerns the joint reply, successor and cost on that different source. Interface 7.3 specifies the bounded mathematical correspondence needed for a transfer; equality of a Fibonacci index, number of modes, spectrum or probability marginal does not supply its hypotheses. Proposition 7.2 supplies an actual stopped-source pair against replacing full semantic response by a fixed finite word observation. Neither statement classifies trained networks by the FIB five modes or identifies semantic response with internal implementation.

## 8. Mathematical scope of the remaining feasibility problem

**Definition 8.1 (distinct unsettled properties).** The unrestricted original conf/conf problem has the following separate predicates: existence of a finite exact common endpoint model; nonexistence of every such finite model; zero joint excess infimum without an optimizer; strictly positive joint excess infimum; and optimum under fixed COMPLETE, program, time, output or other charged budgets. Theorem 4.2 equates the first four with their stated regular periodic versions without evaluating them. Theorem 6.2 gives fixed-shape finite moment completeness, and Proposition 6.3 gives fixed-shape quantitative certificates. Neither settles the remaining all-shape quantifier (6.8), a hard approximation boundary in defect, actual-history-average risk or total resource minima.

**Mathematical citation 8.2 (tools and metric boundaries).** [ART, Theorems 1–2 and §3.2] supplies mature finite-product perturbation and coupling methods; its total variation norm is twice the convention here. Its finite-product bounds do not contain (3.7), the actual-flow domination (3.8), or the all-history source bridge. [SURVEY, §§2.3, 4.1–4.2, 6.1, 7.3] treats finite memory, source-independent randomization and time-invariant algorithms, with long-run testing or estimation losses. Those losses do not supply this stopped-history full-tail conditional-TV optimum. Compactness, geometric summation, finite polynomial constraints and TV convexity are intermediate tools inside the source-specific clipping and feasibility proofs. [LMC, §4 and Proposition 12] concerns approximation of the output-law TV between labelled Markov chains and permits irrational distance even for rational descriptions. It does not impose the acquired-letter flow equations (2.1), supply configuration-before-marginal risk, or decide the common-model feasibility family. [SVA, Theorem 7.1] bounds squared word-function error for a square-summable minimal weighted automaton after singular-value truncation; this need not retain stochastic positivity, normalization, actual-flow stationarity or conditional TV. Positive moment representations of native geometric mixtures are separately limited by [NATIVE, §§4–7]; they are not hypotheses imposed on the arbitrary decoded laws here.

**Mathematical citation 8.3 (acquisition horizons and exact digital coherence).** [FLOOR, Theorems 5.1 and 8.1] shows that even fixed positive endpoint prior masses and a fixed COMPLETE digital observer do not give a uniform cap on acquired-history length for arbitrary full-history risk. Its Theorem 8.2 gives finite uniform existence under a fixed finite depth menu and a floor on every supported mass. Here $L$ truncates the predicted future into complete-word and residual cells, while Proposition 2.3 already ranges over every positive acquired history at one fixed installed prior. No $L$-dependent acquisition cap or modulus uniform over changing prior supports is asserted. The all-history reduction uses a comparison observer and can lower risk; it neither identifies an arbitrary original observer's transient bad histories nor recovers their acquisition lengths.

[PHCONT, Definitions 37.1–37.2] imposes a charged finite-peak binary architecture and both exact compatibility conditions, including actual-history marginalized update coherence. Its Theorem 42.1 gives a budget-dependent gap above the exactly coherent joint optimum, and Theorems 45.2 and 46.1–46.2 transfer certified endpoint margins to paid finite histories under quantitative installed-prior data. Those conditions do not supply (3.7)–(3.10) for arbitrary positive-defect kernels. Clipping preserves exact per-configuration same-update generation and obeys (3.5); it need not preserve exact marginalized coherence at positive excess or the original COMPLETE budget. These cited scope distinctions add no premise to Theorems 3.1–6.2 and do not decide the unrestricted common conf/conf predicates of Definition 8.1.

[ST]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md
[PH]: https://github.com/the-omega-institute/trureturing/blob/e36230b266eb5e9e1c05ee5a99778e4854d6bf9c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md
[PRICE]: https://github.com/the-omega-institute/trureturing/blob/7db69da19a9e3f5be1ba2df57c38eb2facb9ac66/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_APPROXIMATE_COHERENCE_PRICE.md
[FOUR]: https://github.com/the-omega-institute/trureturing/blob/b041140a98877d0430d8b4b98ad2a5df5c084211/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MIXED_PHASE_DEFECT_ATTAINMENT.md
[SWITCH]: https://github.com/the-omega-institute/trureturing/blob/b041140a98877d0430d8b4b98ad2a5df5c084211/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONFIGURATION_LAW_SWITCH_ATTAINMENT.md
[NATIVE]: https://github.com/the-omega-institute/trureturing/blob/85d1c54171c811c4c9e383901a709fe33fc8781d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md
[FLOW]: https://github.com/the-omega-institute/trureturing/blob/f165cf2ce07205f272210bc7d0b7c0669a6c2782/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FLOW_PRESERVING_RATIONAL_FRONTIER.md
[A]: https://github.com/the-omega-institute/trureturing/blob/287f11b193836c1d0688efc0cba049427d6d2589/docs/develop/theory/AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md
[B]: https://github.com/the-omega-institute/trureturing/blob/287f11b193836c1d0688efc0cba049427d6d2589/docs/develop/theory/AURIC_FIB_ATOM_INTRINSIC_CLASSIFICATION_AND_POLYGON_GEOMETRY.md
[FLOOR]: https://github.com/the-omega-institute/trureturing/blob/dd1c0122041a03e4a437d9029fd7d9aba5eaec8e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ENDPOINT_FLOOR_HISTORY_LOCALIZATION.md
[PHCONT]: https://github.com/the-omega-institute/trureturing/blob/dd1c0122041a03e4a437d9029fd7d9aba5eaec8e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md
[ART]: https://arxiv.org/html/1311.3066v1
[SURVEY]: https://arxiv.org/html/2312.15225v1
[LMC]: https://arxiv.org/html/1405.2852v1
[SVA]: https://arxiv.org/html/1711.05994v2

## 追加锚（本行以下为增补区）
