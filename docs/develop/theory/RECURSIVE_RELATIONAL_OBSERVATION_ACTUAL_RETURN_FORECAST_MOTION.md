# Common configuration-risk optimality requires acquired-return forecast motion

## 1. The unchanged question and the new necessary relation

The remaining common conf/conf question allows arbitrary finite stochastic updates and nonnative complete future laws. This article proves that approaching both separate configuration-risk minima requires a uniformly positive amount of semantic forecast change along an actual fourth-segment return. The constant is defined by a compact two-parameter comparison problem and proved strictly positive; no numerical value for it is asserted. This is a necessary update property, not an unrestricted positive risk gap or an attaining construction.

Use the source, complete observer and risk conventions of [ST], [E1], [CLIP] and [PAID]. Fix $m=2,d=1,\ell=2,n=4$. One $K$ is drawn before any actual Read from a fixed finite or countable prior $\mu$, with $\mu(1),\mu(2)>0$. Conditional on that same $K=k$, every paid seed and payload Read is independent with alpha probability

$$
r_k=F_{k+1}/F_{k+3},\qquad r_1=1/3,\quad r_2=2/5,\quad r_k\in I_0=[3/8,5/13]\quad(k\ge3).
$$

The same depth supplies all rejected equal seed pairs and all four payloads. Unequal pairs accept the two original seeds. At p, alpha completes marker 0 and beta suspends; at suspension, alpha returns to p and beta completes marker 1. The third record is written before its latch. The whole original finite control $C_0$ includes both seeds, parser, selectors, bare fields, full marker tree, held $B,Q^+,Z$ records, flags, permissions and completion/Stop control. Fourth completion enters the matching original pendingStop; its unique Stop delivers once. Pending and delivered cuts admit no Read. Both seeds, every marker triple, every positive finite rejection and every positive finite return history remain in the domain. There is no reset, fresh depth, future-$E_1$ conditioning, additional observation or controller port.

Put $a_r=r(1-r)$ and

$$
w_{j,0}=(\beta\alpha)^j\alpha,\qquad w_{j,1}=(\beta\alpha)^j\beta\beta,\qquad j\ge0.
$$

The p carrier consists of these completed words and its unique infinite noncompletion word. The suspended carrier consists of beta, $\alpha w_{j,b}$, and its infinite noncompletion word. The source laws are

$$
P_{p,r}(w_{j,0})=ra_r^j,\qquad P_{p,r}(w_{j,1})=(1-r)^2a_r^j,
$$

$$
P_{\beta,r}(\beta)=1-r,\qquad
P_{\beta,r}(\alpha w_{j,0})=r^2a_r^j,\qquad
P_{\beta,r}(\alpha w_{j,1})=r(1-r)^2a_r^j.
\tag{1.1}
$$

Their infinite-word masses are zero. For current original control $c$, the supplied map $I_c$ keeps all future Reads and inserts their original deterministic records, control, permissions, completion and Stop events. Reading the letters back is its measurable inverse. It preserves TV and commutes with removing the next operation and its event block. The already acquired suspended beta is not charged as a future Read.

The complete acquired history has the following ordinary source-law correspondence. Delete only Stop from a legal operation list and read off its ordered letters; do not delete rejected pairs, accepted seed letters, early payloads, returns or partial pairs. Induction over the original operations shows that the event of acquiring that list is exactly its finite raw-prefix cylinder. A Read consumes the next raw letter and performs the original deterministic event block; the unique enabled Stop consumes no raw letter, and no event follows delivery. The current full control is the original operation fold, and the unread source begins after exactly the number of paid Reads in that prefix. Thus, conditional on $K=k$, a positive history $h$ has likelihood $r_k^{A(h)}(1-r_k)^{B(h)}$, and its unread letters remain independent with the same parameter $r_k$. This is finite-prefix conditioning, without conditioning on future completion. It proves the posterior and continuation formula below also for countable priors: its positive denominator is a summable mixture of the prefix likelihoods, and conditional on each supported depth the unread tail has (1.1). The deterministic statements in [PREFIX], `native_acquired_prefix_cylinder` and `native_acquired_prefix_resumption`, have this same Read/Stop prefix shape; they do not themselves supply the probabilistic posterior or a finite COMPLETE posterior register.

At a positive acquired history $h$, the actual complete target is

$$
T_h^\mu=(I_{C_0(h)})_*\sum_k\nu_h(k)P_{s,r_k},\qquad
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}{\sum_t\mu(t)r_t^{A(h)}(1-r_t)^{B(h)}}.
\tag{1.2}
$$

All paid Reads, including rejected and partial pairs, enter the counts. Counts and posterior rows are analysis quantities, never runtime inputs.

An observer has one fixed finite COMPLETE carrier, source-independent initialization, fixed time-homogeneous source-independent letter updates, and a decoder reading one actual configuration. COMPLETE counts the original controls and records, private labels, program/table selectors, workspace, addresses, output indices and persistent randomness. There is no free tape, clock, archive, advice, continuous register, correlated source seed, exact posterior or readable state-distribution vector. Every decoded law is its own complete legal generator law, using its synthetic emissions and those same acquired-letter updates. This individual generation requirement stays exact.

For the actual conditional configuration row $\rho_h$ and decoded laws $D_z$, set

$$
Q_h=\sum_z\rho_h(z)D_z,\qquad
e_{\rm law}(h)=\operatorname{TV}(Q_h,T_h^\mu),\qquad
e_{\rm conf}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu).
$$

TV is the event supremum, equivalently half the countable $\ell^1$ distance here. $R_{j,s}$ is the supremum over all positive histories in $\mathcal H_s$, $s=p,\beta$. $\mathcal H_p$ includes arbitrary fourth returns; $\mathcal H_3$ contains only the first p cut. Actual-history-average risk is different. The supplied separate full-tail minima are

$$
\rho_p=1116529/22781250,\qquad \rho_\beta=239/6750.
\tag{1.3}
$$

The supplied terminal-projection values $13/266,9/266$ do not replace these full-tail values.

Retain the original marginalized defect: for a legal next operation $a$ with $q_h(a)=Q_h([a])>0$, condition on its cylinder and remove that operation and its original event block, obtaining $\operatorname{res}_aQ_h$, and put $\delta(h,a)=\operatorname{TV}(\operatorname{res}_aQ_h,Q_{ha})$. If $q_h(a)=0$, the defect is zero without defining a conditional law; the actual successor and its risk remain in the domain. $\Delta_4$ and $\Delta_{\rm all}$ are their original respective suprema. Pending Stop has zero defect and the delivered empty supremum is zero. No defect budget is assumed below, and no replacement is claimed to preserve one or recover zero defect.

## 2. An actual-update statistic and the statement

At a fourth p history, let $C_h$ be the observer's acquired update for the legal two-Read word $\beta\alpha$. It updates the full configuration, including any private label. This return leaves the original p control and held records unchanged. The two decoded p laws therefore have a common legal future carrier, with the same $I_{C_0(h)}$ rendering. Define

$$
\mathcal V_h(M)=\sum_{x,z}\rho_h(x)C_h(x,z)\operatorname{TV}(D_x,D_z),\qquad
\mathcal V(M)=\sup_{h\in\mathcal H_p}\mathcal V_h(M).
\tag{2.1}
$$

Equivalently, this is expected TV between the two decoded configuration laws, conditional on the same acquired history and the next actual word being $\beta\alpha$. To check the conditioning, observer initialization and random updates are independent of $K$ and of the raw source. For any fixed acquired $h$, their likelihood factors from the source-prefix likelihood. Hence $K$ and the actual configuration $Z_h$ are conditionally independent given $h$. More explicitly,

$$
\Pr(K=k,Z_h=x,\text{next actual word}=\beta\alpha,Z_{h\beta\alpha}=z\mid h)
=\nu_h(k)\rho_h(x)a_{r_k}C_h(x,z).
\tag{2.1a}
$$

Summing over $k$ and dividing by the strictly positive probability $\sum_k\nu_h(k)a_{r_k}$ gives precisely the joint row $\rho_h(x)C_h(x,z)$ in (2.1). Synthetic emissions do not tilt it. The source posterior can change after this return; (2.1) measures the configuration decoder's motion, not that target change. It requests no new source observation or runtime probability-vector input. It is an analysis statistic of the existing two paid Reads, distinct from target risk, TV after configuration marginalization, and marginalized conditioning defect.

For $(u,v)\in S=[1/3,2/5]^2$, put $a=(1-u)v$, $b=(1-u)(1-v)$ and define the two-phase geometric generator laws

$$
G_p^{u,v}(w_{j,0})=ua^j,\quad G_p^{u,v}(w_{j,1})=ba^j,
$$

$$
G_\beta^{u,v}(\beta)=1-v,\quad G_\beta^{u,v}(\alpha w_{j,c})=vG_p^{u,v}(w_{j,c}).
\tag{2.2}
$$

They are normalized, retain the infinite outcomes with zero mass, and are generated by one persistent label with p emission $u$, suspended emission $v$, and identity private updates. They permit $u\ne v$.

For a Borel probability measure $\omega$ on the compact rectangle $S$ and $r\in I_0$, define

$$
\Psi(\omega,r)=\max_{s\in\{p,\beta\}}\max_{t\in\{1/3,2/5,r\}}
\left\{\int_S\operatorname{TV}(G_s^{u,v},P_{s,t})\,\omega(du,dv)-\rho_s\right\},
$$

$$
\gamma=\min_{\omega\in\mathcal P(S),\ r\in I_0}\Psi(\omega,r).
\tag{2.3}
$$

This measure is only an enlarged mathematical comparison class. No continuous mixture register or infinite table is installed. Actual comparison observers used in the proof have finitely many persistent labels.

**Theorem 2.1.** The constant in (2.3) exists and satisfies $\gamma>0$. For every allowed finite observer on every allowed prior with $\mu(\{k\ge3\})>0$, put $\varepsilon_s=R_{{\rm conf},s}-\rho_s\ge0$ and $e=\max(\varepsilon_p,\varepsilon_\beta)$. Then

$$
\gamma\le\frac{1183}{121}e+\frac6{11}\mathcal V(M).
\tag{2.4}
$$

Consequently exact common conf/conf attainment requires

$$
\mathcal V(M)\ge\frac{11}{6}\gamma>0.
\tag{2.5}
$$

For any sequence of allowed finite observers on such priors with $e\to0$, $\liminf\mathcal V\ge11\gamma/6$. State counts, tables and installed priors may vary, provided each prior retains the stated source contract and a supported nonendpoint. The theorem does not assert that any such sequence or exact optimizer exists.

The rest of the article proves this one result. The finite comparison and sign lemmas are its ingredients.

## 3. The source-specific sign for two-phase geometric laws

Write

$$
d_p=2\rho_p=1116529/11390625,\quad d_\beta=2\rho_\beta=239/3375,
$$

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\quad E_\beta=\{\beta,\alpha w_{0,1}\},
$$

$$
C_p=11758471/22781250,\quad C_\beta=5261/6750.
\tag{3.1}
$$

[ST], [CLIP] and [NATIVE] supply these endpoint-positive events: their endpoint-1 and endpoint-2 probabilities are $412/729,7299/15625$ at p and $22/27,93/125$ at suspension. Their midpoints are $C_p,C_\beta$.

**Lemma 3.1.** Suppose $G_p^{u,v}$ lies coordinatewise between the two endpoint p laws on every completed word. Then

$$
D(u,v):=\frac{412/729-G_p^{u,v}(E_p)}{d_p}
-\frac{22/27-G_\beta^{u,v}(E_\beta)}{d_\beta}\ge0.
\tag{3.2}
$$

Equality holds exactly at $(u,v)=(1/3,1/3)$ and $(2/5,2/5)$.

**Proof.** Write $a=(1-u)v$, $b=1-u-a$. The marker-0 word bounds $\frac13(2/9)^j\le ua^j\le\frac25(6/25)^j$ for all $j$ imply $2/9\le a\le6/25$: otherwise their ratio to the corresponding endpoint tends to zero or infinity. Also $1/3\le u\le2/5$, so $3/5\le a+b\le2/3$. Two marker-1 upper bounds give

$$
b\le\frac{16}{729a^2},\qquad b\le\frac{1944}{390625a^3}.
\tag{3.3}
$$

Put $q=177147/781250$. The first upper bound is the smaller for $a\le q$, the second for $a\ge q$. On $[2/9,q]$ the sum $a+16/(729a^2)$ decreases and stays above $3/5$. On $[q,6/25]$ the sum $a+1944/(390625a^3)$ decreases to $3/5$. These monotonicities follow from derivatives $1-2b/a<0$ and $1-3b/a<0$ on the respective intervals. Thus increasing $b$ from its actual value to the relevant bound keeps $a+b\ge3/5$.

Since

$$
D(a,b)=\frac{412/729-b(1+a+a^2)}{d_p}
-\frac{22/27-b(1+a)/(a+b)}{d_\beta},
$$

through that increase

$$
\partial_bD=-\frac{1+a+a^2}{d_p}
+\frac{a(1+a)}{d_\beta(a+b)^2}
\le-\frac{346649715}{266850431}<0.
\tag{3.4}
$$

The bound uses $a\ge2/9$, $a\le6/25$, $a+b\ge3/5$. It suffices to check the two substituted upper bounds.

Exact polynomial expansion gives

$$
D\left(a,\frac{16}{729a^2}\right)
=\frac{-250(9a-2)P(a)}{266850431a^2(729a^3+16)},
$$

$$
P(a)=515692089a^4+133957242a^3+22330580a^2-10516000a-1912000,
\tag{3.5}
$$

and

$$
D\left(a,\frac{1944}{390625a^3}\right)
=\frac{-162(25a-6)Q(a)}{6671260775a^3(390625a^4+1944)},
$$

$$
\begin{aligned}
Q(a)={}&3693798828125a^6+919180031250a^5+253271520000a^4\\
&+48234052800a^3-15260544828a^2-3499952328a-677410128.
\end{aligned}
\tag{3.6}
$$

All displayed denominators are positive. Here are short whole-interval rational sign certificates. On $[2/9,q]$, use $q<227/1000$ in the positive terms and $a\ge2/9$ in the negative linear term to get

$$
P(a)\le515692089(227/1000)^4+133957242(227/1000)^3
+22330580(227/1000)^2-10516000(2/9)-1912000<-150000.
$$

For $L=2267/10000<q$ and $U=6/25$, direct substitution gives $Q(L)>25000000$. On $[L,U]$, its derivative is bounded below by

$$
6(3693798828125)L^5+5(919180031250)L^4+4(253271520000)L^3
+3(48234052800)L^2-2(15260544828)U-3499952328>30000000000.
$$

Each inequality is a positive-denominator rational comparison. Hence $Q>0$ throughout $[q,6/25]$. Equations (3.5)–(3.6) are strictly positive in their interval interiors and vanish only at $a=2/9$ or $a=6/25$, respectively. Strict decrease in (3.4) further forces $b$ to equal its substituted upper bound in an equality case. These two cases give $b=4/9,u=v=1/3$ or $b=9/25,u=v=2/5$. Conversely those endpoint laws give equality. This proves the lemma. $\square$

## 4. A positive comparison gap, without an installed continuum

**Lemma 4.1.** The minimum in (2.3) exists and is strictly positive.

**Proof.** From $a\le4/15$ the mass surviving $L$ returns in (2.2) is at most $(4/15)^L$. The corresponding target mass is at most $(6/25)^L$. Finite-word probabilities depend continuously on $(u,v,t)$. Refining the residual cell changes TV by at most the smaller residual mass, including the infinite outcome. Thus the complete-law distance is a uniform limit of continuous finite-partition distances on $S\times[1/3,2/5]$ and is continuous. Compactness of probability measures on compact $S$, in the weak topology, and this joint continuity make $\Psi$ continuous on $\mathcal P(S)\times I_0$. Its minimum exists. Endpoint triangle inequalities give $\Psi\ge0$.

Suppose the minimum were zero at $(\omega,r)$. Both endpoint expected configuration losses in each phase would be at most $\rho_s$. For any normalized countable laws $D,P_1,P_2$,

$$
\operatorname{TV}(D,P_1)+\operatorname{TV}(D,P_2)-\operatorname{TV}(P_1,P_2)
=\sum_w\operatorname{dist}\bigl(D(w),[\min(P_1(w),P_2(w)),\max(P_1(w),P_2(w))]\bigr).
\tag{4.1}
$$

This is the supplied coordinate triangle identity [NATIVE] (6.4) and [CLIP] (3.6). Integrate it. Its nonnegative right side must be zero. Countably many zero-integral coordinates imply that almost every decoded law lies in its phase endpoint box. Each endpoint expected loss is exactly $\rho_s$. Within the box, the signed events (3.1) give

$$
\int G_p^{u,v}(E_p)\,d\omega=C_p,\qquad
\int G_\beta^{u,v}(E_\beta)\,d\omega=C_\beta.
\tag{4.2}
$$

Consequently $\int D\,d\omega=1/2-1/2=0$. Lemma 3.1 applies almost everywhere and makes $\omega$ concentrate on the two endpoint pairs. The first equality in (4.2) forces their weights to be $1/2,1/2$.

The supplied source-specific interior excess [NATIVE] (6.1)–(6.6) is

$$
\eta=(5/13)^3(8/13)^5-(2/5)^3(3/5)^5
=14219478376/318644812890625>0.
$$

For every $r\in I_0$, the target word $w_{3,1}$ exceeds both endpoint masses by at least $\eta$. Indeed $r^3(1-r)^5$ decreases on $I_0$ and its endpoint-2 value exceeds its endpoint-1 value. Applying (4.1) with $D=P_{p,r}$ yields

$$
\tfrac12\operatorname{TV}(P_{p,1/3},P_{p,r})
+\tfrac12\operatorname{TV}(P_{p,2/5},P_{p,r})\ge\rho_p+\eta/2.
$$

This contradicts $\Psi=0$. Therefore $\gamma>0$. Compactness is used only inside the enlarged two-parameter comparison; it does not make the union of all finite observer shapes compact. $\square$

## 5. Collapsing one actual circulation to finitely many persistent forecasts

**Lemma 5.1.** Let one finite stationary regular table have p/suspended sets $X,Y$, acquired kernels $B,A$, rows $\pi B=\tau$, $\tau A=\pi$, and emissions $u,v\in[1/3,2/5]$. Its same-update laws are $Q_x,W_y$. Set

$$
C=BA,\quad H=\operatorname{diag}(1-u)B\operatorname{diag}(v)A,\quad
V=\sum_{x,z}\pi_xC_{xz}\operatorname{TV}(Q_x,Q_z).
\tag{5.1}
$$

There is one finite persistent-label observer on the same original source and prior, with labels $x\in X$, installed row $\pi$, emissions $(u_x,\bar v_x)$ where $\bar v_x=(Bv)_x$, and identity private letter updates. It generates (2.2) on each label and satisfies simultaneously

$$
R_{j,p}^{\rm tag}\le R_{j,p}^{\rm old}+4V/11,\qquad
R_{j,\beta}^{\rm tag}\le R_{j,\beta}^{\rm old}+6V/11,
\qquad j\in\{\mathrm{law},\mathrm{conf}\}.
\tag{5.2}
$$

No fixed COMPLETE budget or marginalized-defect budget is preserved.

**Proof.** Put $a_x=(1-u_x)\bar v_x$, $b_x=(1-u_x)(1-\bar v_x)$. Exact individual generation gives

$$
Q_x=u_x\delta_\alpha+b_x\delta_{\beta\beta}+\beta\alpha\sum_zH_{xz}Q_z,
$$

where prefixing keeps the complete legal word and its rendered events. Its scalar comparison $G_x=G_p^{u_x,\bar v_x}$ satisfies the same equation with the last sum replaced by $a_xG_x$. The first two atoms agree exactly. In the remaining prefixed signed measure, insert $Q_x$:

$$
\sum_z H_{xz}(Q_z-G_x)
=\sum_z H_{xz}(Q_z-Q_x)+a_x(Q_x-G_x).
$$

Prefixing is injective on the complete carrier, and TV of these zero-total-mass signed measures is their half-$\ell^1$ norm. Thus $d_x\le\sum_zH_{xz}\operatorname{TV}(Q_z,Q_x)+a_xd_x$. Since $a_x\le4/15<1$, rearranging gives

$$
d_x:=\operatorname{TV}(Q_x,G_x)
\le\frac{\sum_zH_{xz}\operatorname{TV}(Q_z,Q_x)}{1-a_x}
\le\frac4{11}\sum_zC_{xz}\operatorname{TV}(Q_z,Q_x).
\tag{5.3}
$$

The last step uses $H\le(4/15)C$ entrywise. Thus $\sum_x\pi_xd_x\le4V/11$. It compares complete laws, including infinite outcomes, rather than just terminal markers.

For the suspended comparison introduce $L_{xy}=(1-v_y)\delta_\beta+v_y\alpha Q_x$. Individual generation gives $W_y=(1-v_y)\delta_\beta+v_y\alpha\sum_zA_{yz}Q_z$, so

$$
\sum_{x,y}\pi_xB_{xy}\operatorname{TV}(L_{xy},W_y)\le(2/5)V.
\tag{5.4}
$$

For fixed $x$, averaging $L_{xy}$ by $B_{xy}$ gives $(1-\bar v_x)\delta_\beta+\bar v_x\alpha Q_x$. Its TV distance from $G_\beta^{u_x,\bar v_x}$ is $\bar v_xd_x$. Convexity in the decoder, (5.4), $\pi B=\tau$, and (5.3) therefore give, for every suspended target $T$,

$$
\sum_x\pi_x\operatorname{TV}(G_\beta^{u_x,\bar v_x},T)
\le\sum_y\tau_y\operatorname{TV}(W_y,T)+\frac25V+\frac25\frac4{11}V
=\sum_y\tau_y\operatorname{TV}(W_y,T)+\frac6{11}V.
\tag{5.5}
$$

At p the configuration inequality follows directly from (5.3). For law order the p marginalized reports differ by at most $4V/11$. At suspension, average (5.4) before taking TV and add the $\bar v_xd_x$ comparison; the marginalized reports differ by at most $6V/11$. Triangle inequalities give both law-order comparisons against the same target. No old law risk is replaced by old conf risk in these two comparisons.

Install the finite tag independently after the original third record write and latch, inside that same third-completion update. Use fair synthesis earlier, identity private updates later, and original completion, clearing, pendingStop and delivery. Every original $C_0$ fiber uses the same row while retaining its own records. The tag row is $\pi$ after every actual fourth history. This is the full-domain product realization of [PAID] (Lemma 2.1.1). Its own synthetic p/suspended laws are exactly (2.2); it never queries the source. The old table rows are likewise $\pi,\tau$ at every actual history. Applying the preceding comparisons to the same posterior target (1.2), then rendering with $I_c$ and taking the same suprema, proves all four bounds (5.2). $\square$

## 6. Arbitrary finite kernels, including zero emissions

**Proof of Theorem 2.1.** Lemma 4.1 proves the first assertion. Fix an arbitrary allowed original observer and a supported $r_{k_0}\in I_0$. Reuse the common paid-history extraction [MIXSEP] (Lemma 2.1): on one original record fiber it yields p and suspended carriers, original acquired kernels $B,A$, stationary rows $\pi B=\tau$, $\tau A=\pi$, and simultaneous pure-target configuration bounds by the original $R_{{\rm conf},s}$ for every supported depth. Its proof uses finite positive paid rejection histories exposing each supported depth, followed by actual returns and Cesaro averaging; it includes countable priors. All positive stationary coordinates are reachable after finite positive actual histories. The extracted table uses the original emissions and exact own-generated raw laws $Q_x,W_y$; no emission positivity is assumed. For the suspended configuration bound, retain the same extraction proof with its loss linear in the suspended row, as expressly allowed after that supplied lemma. The proof can retain all four risk orders on this one row; no suspended law bound is being substituted for a suspended configuration bound.

Apply that lemma's bounded-statistic assertion to $f(x)=\sum_z(BA)_{xz}\operatorname{TV}(Q_x,Q_z)$. Formula (2.1) on the same fiber is precisely its actual-history expectation. Hence the common stationary row satisfies

$$
V:=\sum_x\pi_xf(x)\le\mathcal V(M).
\tag{6.1}
$$

Delete zero-row labels in both phases. From $\pi B=\tau$, a zero-$\tau$ suspended label receives no $B$ transition from a positive-$\pi$ p label; from $\tau A=\pi$, the converse holds for $A$. Thus the remaining label sets are closed under all noncompleting acquired and synthetic transitions, since the latter use those same kernels. Install the resulting stationary table by the same finite product realization used in Lemma 5.1. Its fourth decoder laws remain $Q_x,W_y$, and its pure-target risks are no greater than the original ones. This comparison changes only the private latch distribution and earlier own-generated laws; it does not change the source or actual histories and asserts no budget preservation.

Now reuse [CLIP] (Theorem 3.1, (3.9)–(3.10)) on that stationary table, clipping emissions into $[1/3,2/5]$ and preserving both acquired flows. In terms of the original nonnegative excesses define

$$
T_p=(30\varepsilon_p+20\varepsilon_\beta)/11,\qquad
T_\beta=(12\varepsilon_p+30\varepsilon_\beta)/11.
\tag{6.2}
$$

The regenerated clipped laws $\widehat Q,\widehat W$ satisfy

$$
\sum_x\pi_x\operatorname{TV}(Q_x,\widehat Q_x)\le T_p,\quad
\sum_y\tau_y\operatorname{TV}(W_y,\widehat W_y)\le T_\beta,
$$

and both clipped configuration risks increase by at most the corresponding $T_s$. These are average full-law comparisons on this common stationary row, including any original infinite noncompletion mass. The supplied clipping proof derives emission control from endpoint risk excess, so it covers original zero and unit emissions rather than imposing regularity on the arbitrary competitor.

Let $\widehat V$ be (5.1) for the clipped p laws. Triangle inequalities and $\pi C=\pi$ give

$$
\widehat V\le V+2T_p.
\tag{6.3}
$$

Apply Lemma 5.1 to this one clipped table. The resulting finite tag measure is a particular $\omega$ in (2.3). Use the same supported $r_{k_0}$. Its three-target functional is bounded by its all-supported pure-target configuration risks. These equal its all-positive-history risks by [CLIP] (Proposition 2.3), since its acquired tag row is fixed; the equality includes the paid rejection exposure and the entire countable posterior. Therefore

$$
\begin{aligned}
\gamma&\le\max\{\varepsilon_p+T_p+(4/11)(V+2T_p),\\
&\hspace{43mm}\varepsilon_\beta+T_\beta+(6/11)(V+2T_p)\}\\
&=\max\left\{\frac{691\varepsilon_p+380\varepsilon_\beta}{121}+\frac4{11}V,
\frac{492\varepsilon_p+691\varepsilon_\beta}{121}+\frac6{11}V\right\}\\
&\le\frac{1183}{121}e+\frac6{11}\mathcal V(M).
\end{aligned}
\tag{6.4}
$$

This proves (2.4), without enumeration of configurations or a finite history grid. Equations (2.5) and the stated liminf consequence follow algebraically. The prior can vary because $\gamma$ minimizes over all $r\in I_0$, while each original extraction is performed on its own single installed prior and actual model. No coordinates from different actual models are identified. $\square$

## 7. Scope, represented resources and task-relative whitebox quality

For the regular stationary class on an allowed prior supporting a nonendpoint, the proof gives the sharper relation $\gamma\le\max\{\varepsilon_p+4V/11,\varepsilon_\beta+6V/11\}$. The larger coefficient in (2.4) pays for the supplied arbitrary-emission clipping. Neither relation bounds $e$ positively when forecast motion is unrestricted. Exact attainment, an unattained zero infimum, a positive unrestricted gap and fixed-resource optima therefore remain distinct.

The comparisons in Lemma 5.1 use one finite common model, source, prior and actual history for all four risk coordinates. They compare law with law and conf with conf, retaining the placement of TV. The obstruction in Theorem 2.1 specifically uses conf/conf. It gives no analogous motion necessity from either law coordinate alone, and it does not alter the supplied law/law, law/conf and conf/law attainments. If conf/conf exact attainment exists, its two law risks also equal their separate minima by convexity and the supplied lower bounds; this conditional observation supplies no existence claim.

The proof preserves exact individual generation. It allows positive marginalized defect throughout. In the tag comparison its positive fourth-event residuals tilt $\pi$ by $1-u_x$ after beta or by $\bar v_x$ after alpha, whereas acquired execution keeps $\pi$ fixed. Those are different rows unless their decoded mixtures coincide. Earlier fair synthesis uses its own latch sampler and terminal residuals are original deterministic Stop or empty futures. No limit argument here restores zero defect or predicted support coverage.

The Borel measure in (2.3) and stationary extraction rows are analysis objects. Installed comparisons use one sampled finite label, never a continuous vector or an infinite table. For a supplied rational stationary table, $\bar v_x=(Bv)_x$ and all new table entries are rational. Exact categorical sampling can reuse a finite candidate-bit register, bit cursor, thresholds, row selector and program counter, with every microstate counted in COMPLETE. Fresh bits and rejection attempts have charged work but no persistent unbounded attempt counter. For arbitrary real entries the statement is only the original abstract finite indexed stochastic-rule interpretation; it supplies no exact-real oracle or digital sampler for those constants. The comparison does not preserve state count, installed numeric precision, program size, sampler workspace, output storage or a physical resource budget. Actual Reads, retained configuration, model description, synthesis, random bits, time and energy remain separate accounts. Arbitrarily long legal returns and rejection sampling preclude a finite worst-case total-work or output-length assertion.

Define task-relative configuration whitebox quality by $W_s=1-R_{{\rm conf},s}$. On this source, for every allowed prior with $\mu(\{k\ge3\})>0$, simultaneously having $W_s\ge1-\rho_s-e$ forces

$$
\mathcal V(M)\ge\frac{11}{6}\left(\gamma-\frac{1183}{121}e\right)_+.
$$

Thus a nearly optimal common predictor cannot make its complete semantic forecast constant along all acquired return transitions, even by adding arbitrarily many finite labels. This is a property of decoded law and actual update together. It neither identifies an internal implementation from its semantic response nor classifies arbitrary trained networks by FIB's five windows. Transfer from passive five-mode memory, tensor-sign acquisition, native-tree geometry, KBonacci or atomic constructions requires the joint source/reply/update/control/cost and complete-tail correspondence of [CLIP] (Interface 7.3); none is presumed here.

A concrete remaining path is to constrain this necessary acquired-return motion jointly with the endpoint word boxes and original two acquired flows, rather than seek another constant-parameter source mixture. An exact table must sustain positive motion while keeping every active decoder's endpoint-coordinate constraints and its supported interior configuration losses. To derive an unrestricted positive risk gap, one would still need an independent upper obstruction on that motion or an evaluated corrected all-shape certificate. This article supplies neither.

## 8. Supplier overlap and sources

The new source-specific ingredients are the two-phase geometric sign (3.2), the complete-law collapse controlled by the same acquired $BA$ circulation (5.3)–(5.5), and their common-model propagation to (6.4). Compactness, coordinate triangle identities, convexity and finite-chain extraction are mature tools consumed inside the proof, not renamed research products.

[PH] (§§14–20) supplies single-mode and deterministic finite-cycle budget relations. A mixture's configuration expectation can be smaller than the maximum over its tags; those results do not by themselves give Lemma 4.1 for arbitrary Borel phase-asymmetric mixtures or the acquired-return bound. [NATIVE] restricts mixtures of constant source parameters. The family (2.2) also contains $u\ne v$: its scalar return moments would force a native representing measure to concentrate on one $r$ with $r(1-r)=a$, then force $u=r=v$. Thus these phase-asymmetric laws generally lie outside that native family. The sign lemma concerns this larger nonnative family and does not tune [MIXSEP]'s signed coefficients. [MIXSEP] supplies a risk-plus-native-representation inequality, without an unrestricted risk gap; it also supplies the common paid-history row used here. [PAID] (§§9–10) supplies aggregation and corrected all-shape certificates, not the semantic-return statistic in (2.1). Its §11 gives a lawful common rational witness with both excesses below $11/10^8$ and its own positive p excess above $109467/10^{12}$. None of those bounds is contradicted or republished here. The constant $\gamma$ has not been numerically evaluated.

The supplied actual three-depth endpoint-tag counterexample remains a failure of that method's configuration risk, not a universal arbitrary-kernel obstruction or a marginalized-risk violation. Here its complete-word excess is consumed only after the new two-phase sign has forced an enlarged comparison measure to be the fair endpoint measure.

The current supplier pin is `6c41ff54e3291b59f7e59c60691736f8148a5548`. Chronology [CH] (§§24–28) concerns original erased retry/return placement and equal-future-law collisions. [GEOM] (§76) concerns planar grounding and unit-skeleton dimension; its §77 proves a robust width-or-area obstruction for prescribed near-unit planar cable lengths on one fixed authentic tree. That theorem allows arbitrary positive source heights and excludes the stated planar assembly for sufficiently small thinning, under its fixed chamber data. It supplies neither a stochastic acquired $B,A$ circulation nor conditional full-tail configuration risks. [KB] (§91) concerns positive-child fees and incoming endpoint compatibility. Their observation, operation, metric and resource contracts do not provide a stopped-source risk transfer.

The named current public acquisition and observer statements have these bounded correspondences. The links below point to their declaration source and, where useful, their exact Scribe scope statement. They are read for correspondence and overlap only; this article makes no current compilation or kernel-verification claim.

| Supplier | Load-bearing domain and conclusion | Relation to the present theorem |
| --- | --- | --- |
| [CACHE], `cacheEquiv`, `compatible_cache_card` | An ordered coarse address/reply history has its full raw-lift fiber, with $2^{\text{noneCount}}$ nominal lifts, including branch/absent choices not realized by any source. | A raw-cache multiplicity, not a stopped future law, stochastic emission table or configuration-risk bound. |
| [PURE], `pure_actual_prefix_cache`, `pure_admissible`, `pure_joint_price` | For immutable finite ordered Boolean trees with at most $N$ leaves, one source-independent finite acquisition observer preserves the exact preorder cache and has price $c\,\mathrm{nominalCard}(N)+\mathrm{nodeMax}(N,\tau)$. | This charges a finite tree-address cache and distinct actual node fees; it does not pay the repeated iid letters or retain unbounded acquired prefixes in the present source. |
| [COARSE], `completion_contract` | A finite coarse route and positive prototypes admit an all-source decision completion with truthful actual-request cache entries and exact paid address sets. | Its leaf/branch/absent readouts, prototype verification and acquisition policy are different operations; no full-tail TV risk correspondence is supplied. |
| [ABSENT], `Observer`, `Admissible`, `outside_Q_N_absent` | A deterministic complete nominal observer on a bounded immutable tree has truthful cache transitions at actual prefixes; addresses outside the tree budget return raw absent. | Here both source letters stay possible after every positive history. There is no absent-address operation to eliminate. |
| [NORM], `absent_normalization_contract` | Static absent-orbit elimination preserves the whole nominal carrier, transports original actual runs and unrestricted coarse pairs, and dominates nonnegative distinct-address fees. | Its source-specific redesign does not dominate present repeated-Read costs, generated stopped laws or the acquired semantic-return statistic. |
| [TABLE], `admissible_competitor_table_coverage` | After that normalization, finite native tables preserve all nominal transitions, caches, actual/counterfactual semantics and the tree contract's price. | Its finite table universe has deterministic four-reply transitions and bounded address/cache alphabets; it is not the unrestricted stochastic stopped observer class. |
| [PREFIX], `native_acquired_prefix_cylinder`, `native_acquired_prefix_resumption` | Original native stream execution emits exactly each legal ordered raw-prefix cylinder, counts only Read, and resumes on its unread tail with the full returned state. | This is the deterministic prefix correspondence used in §1's ordinary argument. Its source and [PREFIX-S]'s scope supply no shared-depth probability law, posterior, conditional risk or finite online count register. |

The mismatch in the cache rows is substantive. Re-querying a tree address returns the same immutable raw reply and charges only its first occurrence. In the unchanged stopped source, another Read at the same original p control consumes the next random letter, with both outcomes positive conditional on every supported $K$, and remains paid. Installing cached replies in place of those Reads would change the source law and legal transcript. A correspondence transporting the joint operations, full laws and charges would have to preserve that distinction; none of these suppliers provides one. Conversely the native prefix correspondence is consistent with the ordered paid-letter cylinder, but its returned count is a mathematical index, and its full native carrier is not asserted to be a finite COMPLETE stochastic observer. The ordinary argument in §1, rather than a transplanted count register or a fresh formal claim, supplies the likelihood and same-depth continuation needed here.

These suppliers do not contain the sign lemma for the enlarged phase-asymmetric family, the return-motion collapse, or their risk propagation. The uncovered delta is therefore the source-specific necessary relation (2.4), beyond published PAID/MIXSEP, within the searched named corpus. No global originality claim follows.

Primary literature separates the nearby questions. [CK] (Theorem 7 and Corollary 8) approximates TV for a supplied pair of labelled Markov chains, without these unweighted acquired flows and configuration-before-TV risks. [Z] (§2) gives chronological realization separations for controlled root-word responses with a shared terminal effect, rather than this stopped conditional full-tail loss. [A] (Theorem A and §§4–5) studies observed-law closure and architecture prices for stationary continuous-time Markov processes under entropy-production cost; it does not supply a paid-Read conditional-TV transfer. These are scope comparisons, not a claim that all relevant literature has been exhausted or that the present result has global priority. All new proofs here are ordinary mathematics; no Lean verification, independent review, physical realization, new kernel authority or completion of the continuing research goal is asserted.

- **ST.** [Randomized stopped-tail minimax](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md), §§1–3.
- **E1.** [Full E1 scope extension](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FULL_E1_SCOPE_EXTENSION.md), §2.
- **PH.** [Phase-coherent full-tail minimax](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md), §§2,10,14–20.
- **NATIVE.** [Native-mixture recurrence obstruction](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md), §§3–7.
- **CLIP.** [Risk-controlled emission moment feasibility](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md), §§2–7.
- **PAID.** [Effective paid-history certificates](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md), §§2,9–11.
- **MIXSEP.** [Uniform mixture separation](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_MIXTURE_SEPARATION.md), §§2–6.
- **CH.** [Spatial records chronology](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPATIAL_RECORDS_CHRONOLOGY.md), §§24–28.
- **GEOM.** [Recursive holographic boundary geometry continuation II](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_II.md), §§76–77.
- **KB.** [KBonacci full positive-window logarithmic price](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/KBONACCI_FULL_POSITIVE_WINDOW_LOGARITHMIC_PRICE.md), §91.
- **CACHE.** [Full compatible acquisition-cache fibers](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.lean#L81), `cacheEquiv` and `compatible_cache_card`; [Scribe scope](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.scribe.cs).
- **PURE.** [Exact finite pure acquisition](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.lean#L399), `pure_actual_prefix_cache`, `pure_admissible`, `pure_node_fee` and `pure_joint_price`; [Scribe scope](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.scribe.cs).
- **COARSE.** [Actual coarse-readout completion](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.lean#L163), `completion_contract`.
- **ABSENT.** [Complete bounded-tree observer and absent elimination](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.lean#L48), `Observer`, `Admissible` and `outside_Q_N_absent`.
- **NORM.** [Actual absorbing normalization](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.lean#L708), `NormalizationContract` and `absent_normalization_contract`.
- **TABLE.** [Exact full nominal native tables](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.lean#L273), `admissible_competitor_table_coverage`.
- **PREFIX.** [Exact native acquired-prefix cylinders and resumption](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.lean#L143), `native_acquired_prefix_cylinder` and `native_acquired_prefix_resumption`.
- **PREFIX-S.** [Native acquired-prefix Scribe scope](https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.scribe.cs#L53), The final scope paragraph excludes a probabilistic posterior and conditional-law theorem.
- **CK.** Chen and Kiefer, [On the Total Variation Distance of Labelled Markov Chains](https://arxiv.org/html/1405.2852v1), §4.
- **Z.** Zhao, [Exact Local Optimality Does Not Compose: The Complexity of Chronological Realization](https://arxiv.org/html/2609.19707v1), §2.
- **A.** Aznagulov, [Thermodynamic Realizability of Hidden Markov Processes: Attainment, Observable Certificates, and the Price of Architecture](https://arxiv.org/html/2609.14623v1), Theorem A and §§4–5.

[ST]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md
[E1]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FULL_E1_SCOPE_EXTENSION.md
[PH]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md
[NATIVE]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md
[CLIP]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md
[PAID]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md
[MIXSEP]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_MIXTURE_SEPARATION.md
[CH]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPATIAL_RECORDS_CHRONOLOGY.md
[GEOM]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_II.md
[KB]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/docs/develop/theory/KBONACCI_FULL_POSITIVE_WINDOW_LOGARITHMIC_PRICE.md
[CACHE]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.lean#L81
[PURE]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.lean#L399
[COARSE]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.lean#L163
[ABSENT]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination.lean#L48
[NORM]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.lean#L708
[TABLE]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.lean#L273
[PREFIX]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.lean#L143
[PREFIX-S]: https://github.com/the-omega-institute/trureturing/blob/6c41ff54e3291b59f7e59c60691736f8148a5548/Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.scribe.cs#L53
[CK]: https://arxiv.org/html/1405.2852v1
[Z]: https://arxiv.org/html/2609.19707v1
[A]: https://arxiv.org/html/2609.14623v1

## 追加锚（本行以下为增补区）

## 9. A quantitative bound for the complete comparison class

**Definition 9.1 (carriers, conventions and unchanged functional).** Use the original words $w_{j,0}=(\beta\alpha)^j\alpha$, $w_{j,1}=(\beta\alpha)^j\beta\beta$, $j\ge0$. The p carrier contains all these finite completed words and $(\beta\alpha)^\infty$; the suspended carrier contains $\beta$, all $\alpha w_{j,c}$, and $\alpha(\beta\alpha)^\infty$. Completion and the unique original Stop are rendered by $I_c$ as in §1; all future Reads, finite fields and permissions are retained. TV is the event supremum, equal to half the countable $\ell^1$ distance on these carriers.

Write $t_1=1/3,t_2=2/5$, $S=[t_1,t_2]^2$ and $I_0=[3/8,5/13]$. For $t\in[t_1,t_2]$, put $a_t=t(1-t)$ and retain the complete source laws

$$
P_{p,t}(w_{j,0})=t a_t^j,\qquad
P_{p,t}(w_{j,1})=(1-t)^2a_t^j,
$$

$$
P_{\beta,t}(\beta)=1-t,\qquad
P_{\beta,t}(\alpha w_{j,c})=tP_{p,t}(w_{j,c}).
\tag{9.1}
$$

For every $(u,v)\in S$, without imposing $u=v$, put $a=(1-u)v,b=(1-u)(1-v)$ and retain

$$
G_p^{u,v}(w_{j,0})=ua^j,\qquad
G_p^{u,v}(w_{j,1})=ba^j,
$$

$$
G_\beta^{u,v}(\beta)=1-v,\qquad
G_\beta^{u,v}(\alpha w_{j,c})=vG_p^{u,v}(w_{j,c}).
\tag{9.2}
$$

All infinite-word masses in (9.1)–(9.2) are zero. Indeed $u+b=1-a$, so the completed p masses sum to 1, with mass $a^L\le(4/15)^L$ surviving $L$ returns; the suspended surviving mass is $va^L\le(2/5)(4/15)^L$. The source bounds are $a_t^L\le(6/25)^L$ and $ta_t^L\le(2/5)(6/25)^L$. The same normalized complete laws and both infinite outcomes remain in every distance below.

Set

$$
\rho_p=\frac{1116529}{22781250},\qquad
\rho_\beta=\frac{239}{6750},\qquad d_s=2\rho_s.
$$

For every Borel probability $\omega$ on the entire rectangle and every $r\in I_0$, retain exactly (2.3):

$$
\Psi(\omega,r)=
\max_{s\in\{p,\beta\},\ t\in\{t_1,t_2,r\}}
\left(\int_S\operatorname{TV}(G_s^{u,v},P_{s,t})\,d\omega-\rho_s\right),
\qquad
\gamma=\min_{\omega\in\mathcal P(S),\ r\in I_0}\Psi(\omega,r).
\tag{9.3}
$$

The integral takes TV of each individual law before averaging; it is not the TV of a marginalized mixture. $\omega$ is an analysis comparison measure, with no finite-support restriction, and supplies no observer register or sampler.

**Theorem 9.2 (explicit full-class comparison lower bound).** For every pair permitted in Definition 9.1,

$$
\Psi(\omega,r)\ge c_*:=
\frac{3554869594}{1857643496310087890625}
>\frac1{10^{12}}.
\tag{9.4}
$$

Consequently the unchanged minimum satisfies $\gamma\ge c_*$. The proof consists of the pointwise stability and Borel integration below; it does not identify the numerical optimum of $\gamma$.

**Proof, endpoint and complete-coordinate ingredients.** Consume the exact endpoint signs and distances of [ST, §2.2], used also by [PH, §2] and (3.1). At p the endpoint-2/endpoint-1 ratios on marker 0 words are $(6/5)(27/25)^j>1$, and on marker 1 words are $(81/100)(27/25)^j$, below 1 exactly at $j=0,1,2$. In suspension the ratios on prefixed marker 0 words are $(36/25)(27/25)^j>1$, those on prefixed marker 1 words are $(243/250)(27/25)^j$, below 1 only at $j=0$, and the direct $\beta$ mass is larger at endpoint 1. These comparisons cover every completed word; both infinite masses vanish. Thus the endpoint 1 positive events are

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\}.
$$

Their probabilities, differences and midpoints are

$$
\begin{aligned}
P_{p,t_1}(E_p)&=412/729,&P_{p,t_2}(E_p)&=7299/15625,\\
P_{\beta,t_1}(E_\beta)&=22/27,&P_{\beta,t_2}(E_\beta)&=93/125,\\
d_p&=1116529/11390625,&d_\beta&=239/3375,\\
C_p&=11758471/22781250,&C_\beta&=5261/6750.
\end{aligned}
\tag{9.5}
$$

Here $C_s$ is the midpoint event probability and $\operatorname{TV}(P_{s,t_1},P_{s,t_2})=d_s$. These are credited intermediate values, rather than a new endpoint minimax assertion.

The complete-coordinate triangle identity of [NATIVE, (6.4)] and [CLIP, (3.6)] states, for normalized countable laws,

$$
\begin{aligned}
&\operatorname{TV}(D,P_1)+\operatorname{TV}(D,P_2)-\operatorname{TV}(P_1,P_2)\\
&\hspace{7mm}=\sum_w\operatorname{dist}
\bigl(D(w),[\min(P_1(w),P_2(w)),\max(P_1(w),P_2(w))]\bigr).
\end{aligned}
\tag{9.6}
$$

It follows by summing the scalar absolute-value identity, including the infinite coordinate. All terms on the right are nonnegative and the sum converges by normalization. This full slack, rather than an objective on selected words alone, will control two selected violations.

## 10. Stability on the entire phase-asymmetric rectangle

**Proof of Theorem 9.2, transformed coordinates.** Write $a_i=t_i(1-t_i)$, $b_i=(1-t_i)^2$, so $(a_1,b_1)=(2/9,4/9)$ and $(a_2,b_2)=(6/25,9/25)$. Define

$$
D(a,b)=\frac{412/729-b(1+a+a^2)}{d_p}
-\frac{22/27-b(1+a)/(a+b)}{d_\beta},
$$

$$
h_2=(ba^2-16/729)_+,\qquad
h_3=(ba^3-1944/390625)_+,\qquad H=h_2+h_3,
$$

$$
F=D+13000H,\qquad
d(u,v)=\min_{i=1,2}(|u-t_i|+|v-t_i|).
\tag{10.1}
$$

The event expressions are $G_p(E_p)=b(1+a+a^2)$ and $G_\beta(E_\beta)=b(1+a)/(a+b)$, since $u=1-a-b,v=a/(a+b)$. We prove on all of $S$ that

$$
F\ge0,\qquad d(u,v)\le112F.
\tag{10.2}
$$

The image of $S$ satisfies

$$
1/5\le a\le4/15,\quad9/25\le b\le4/9,\quad
3/5\le a+b\le2/3,\quad3a/2\le b\le2a.
\tag{10.3}
$$

The derivatives are

$$
\partial_bD=-\frac{1+a+a^2}{d_p}
+\frac{a(1+a)}{d_\beta(a+b)^2},\qquad
\partial_aD=-\frac{b(1+2a)}{d_p}
+\frac{b(b-1)}{d_\beta(a+b)^2}.
\tag{10.4}
$$

On the larger box given by the first two bounds in (10.3) and $a+b\ge3/5$, both absolute derivatives are bounded by

$$
\frac2{d_p}+\frac{25}{9d_\beta}<100,
\qquad d_p>9/100,
\quad d_\beta>7/100.
\tag{10.5}
$$

For example $1+a+a^2<2$, $b(1+2a)<2$, $a(1+a)<1$ and $b(1-b)<1$ give this bound. All comparison segments below stay in this box. For $\delta_i=|a-a_i|+|b-b_i|$ the inverse coordinates also give

$$
|u-t_i|\le\delta_i,\qquad
|v-t_i|\le\tfrac53|a-a_i|+\tfrac23\delta_i,
\qquad |u-t_i|+|v-t_i|\le4\delta_i.
\tag{10.6}
$$

Indeed the second inequality follows by putting the two fractions $a/(a+b)$ and $a_i/(a_i+b_i)$ over their denominators, using $a+b\ge3/5$ and $t_i\le2/5$.

## 11. Three-region rational coercivity

**Proof of Theorem 9.2, lower region $a\le a_1$.** Compare $b$ with $2a$. Both endpoints of this vertical segment satisfy the derivative box and the sum bound. On it,

$$
\partial_bD\le-\frac{31/25}{d_p}
+\frac{22/81}{(9/25)d_\beta}
=-\frac{14383223125}{7204961637}<-1.
\tag{11.1}
$$

The function $f(a)=D(a,2a)$ satisfies $f(a_1)=0$ and

$$
f'(a)=-\frac{2(1+2a+3a^2)}{d_p}+\frac2{3d_\beta}
\le-\frac{2(38/25)}{d_p}+\frac2{3d_\beta}
=-\frac{5763782250}{266850431}<-1.
\tag{11.2}
$$

Integration in $a,b$ yields $D\ge(a_1-a)+(2a-b)\ge0$. Moreover $\delta_1=3(a_1-a)+(2a-b)\le3D$. Thus (10.6) gives $d\le12D\le112F$.

**Proof of Theorem 9.2, middle region $a_1\le a\le a_2$.** Put

$$
q=\frac{177147}{781250},\qquad
B(a)=\min\left\{\frac{16}{729a^2},\frac{1944}{390625a^3}\right\}.
\tag{11.3}
$$

The first branch applies on $[a_1,q]$, the second on $[q,a_2]$, and the branches agree at $q$. $B$ decreases from $b_1$ to $b_2$ and is 6-Lipschitz: the branch derivatives have magnitudes $2B/a$ and $3B/a$, each at most $3b_1/a_1=6$. On each branch $a+B(a)$ has derivative $1-mB/a<0$, $m=2$ or 3, since $B\ge b_2,a\le a_2$. Thus $3/5\le a+B(a)\le2/3$, and the segment from actual $b$ to $B(a)$ stays in the derivative box. There,

$$
\partial_bD\le-\frac{103/81}{d_p}
+\frac{(6/25)(31/25)}{(9/25)d_\beta}
=-\frac{346649715}{266850431}<-1.
\tag{11.4}
$$

The exact identities (3.5)–(3.6) supply the sign polynomials. Retaining their coefficients, the quantitative estimate needed here is

$$
D(a,B(a))\ge\tfrac14\min(a-a_1,a_2-a).
\tag{11.5}
$$

Indeed the first branch has

$$
D(a,16/(729a^2))=
\frac{-250(9a-2)P(a)}{266850431a^2(729a^3+16)},
$$

$$
P(a)=515692089a^4+133957242a^3+22330580a^2-10516000a-1912000.
\tag{11.6}
$$

Using $q<227/1000$ in positive terms and $a\ge2/9$ in the negative linear term gives, throughout $[a_1,q]$,

$$
P(a)\le515692089(227/1000)^4+133957242(227/1000)^3
+22330580(227/1000)^2-10516000(2/9)-1912000
=-\frac{1458200744339967359}{9000000000000}<-150000.
\tag{11.7}
$$

The second branch has

$$
D(a,1944/(390625a^3))=
\frac{-162(25a-6)Q(a)}{6671260775a^3(390625a^4+1944)},
$$

$$
\begin{aligned}
Q(a)={}&3693798828125a^6+919180031250a^5+253271520000a^4\\
&+48234052800a^3-15260544828a^2-3499952328a-677410128.
\end{aligned}
\tag{11.8}
$$

For $L=2267/10000<q$ and $U=6/25$, exact substitution gives

$$
Q(L)=\frac{2821236205035871506801869}{102400000000000000}>25000000,
$$

and throughout $[L,U]$,

$$
\begin{aligned}
Q'(a)\ge{}&6(3693798828125)L^5+5(919180031250)L^4
+4(253271520000)L^3\\
&+3(48234052800)L^2-2(15260544828)U-3499952328\\
&=\frac{6927164613779257879197}{204800000000}>30000000000.
\end{aligned}
\tag{11.9}
$$

Hence $Q(a)>25000000$ on the entire second branch. These are rational enclosures with explicit endpoints, not assertions based on samples. The denominators in (11.6),(11.8) are positive and increasing. Consequently the two branches respectively give

$$
D(a,B(a))\ge k_1(a-a_1),\qquad
k_1=\frac{2250(150000)}{266850431a_2^2(729a_2^3+16)}
=\frac{11444091796875}{13591493002123}>1/4,
$$

$$
D(a,B(a))\ge k_2(a_2-a),\qquad
k_2=\frac{4050(25000000)}{6671260775a_2^3(390625a_2^4+1944)}
=\frac{2441406250}{7204961637}>1/4.
\tag{11.10}
$$

This proves (11.5). For an explicit coefficient verification of the rational identities, let $A_0=412/729,B_0=22/27$ and $c=16/729,m=2$ or $c=1944/390625,m=3$. Clearing the denominator $a^m(a^{m+1}+c)$ in $D(a,c/a^m)$ gives the polynomial

$$
(A_0/d_p-B_0/d_\beta)a^m(a^{m+1}+c)
-\frac c{d_p}(1+a+a^2)(a^{m+1}+c)
+\frac c{d_\beta}(1+a)a^m.
\tag{11.11}
$$

Multiplying (11.11) by $266850431\cdot729$ in the first case gives $-250(9a-2)P(a)$, and by $6671260775\cdot390625$ in the second gives $-162(25a-6)Q(a)$. Thus all coefficients and signs in the comparison can be reproduced by rational polynomial arithmetic.

Set $t=\min(a-a_1,a_2-a)$, $y=(B(a)-b)_+$ and $z=(b-B(a))_+$. Equations (10.5),(11.4),(11.5) give

$$
D\ge\tfrac14t+y-100z,\qquad
D+101z\ge\tfrac14t+y+z\ge0.
\tag{11.12}
$$

Choose $i$ with $|a-a_i|=t$. The cap's Lipschitz bound gives

$$
\delta_i\le7t+y+z\le28(D+101z).
$$

On the first branch $z=h_2/a^2$, and on the second $z=h_3/a^3$, including $z=0$ in both formulas. As $a\ge a_1$, $z\le125H$. Since $101\cdot125=12625<13000$, $F\ge D+101z\ge0$. Equation (10.6) then gives $d\le112F$ throughout this closed region.

**Proof of Theorem 9.2, upper region $a>a_2$.** Here $b\ge3a/2>b_2$, so $h_3>0$. Monotone products give

$$
h_3\ge\tfrac32(a^4-a_2^4)\ge6a_2^3(a-a_2),\qquad
6a_2^3>1/13,
$$

$$
h_3\ge a_2^3(b-b_2),\qquad a_2^{-3}<73.
\tag{11.13}
$$

Thus $\delta_2\le(13+73)h_3=86h_3$. The straight segment to $(a_2,b_2)$ lies in the derivative box. Since $D(a_2,b_2)=0$, (10.5) yields $D\ge-100\delta_2\ge-8600h_3$. Therefore

$$
F\ge4400H\ge0,\qquad
d\le344h_3\le344H\le F\le112F.
\tag{11.14}
$$

Together the three regions prove (10.2) on the whole rectangle, including all its boundary points.

## 12. Integration without a support or phase restriction

**Proof of Theorem 9.2, arbitrary Borel measures.** Fix any $\omega\in\mathcal P(S)$ and $r\in I_0$, and write $e=\Psi(\omega,r)$. The two endpoint triangle inequalities in either phase imply $e\ge0$; all six expected distances in (9.3) are at most the corresponding $\rho_s+e$.

The endpoint event inequalities give

$$
\left|\int G_p(E_p)\,d\omega-C_p\right|\le e,\qquad
\left|\int G_\beta(E_\beta)\,d\omega-C_\beta\right|\le e.
\tag{12.1}
$$

For example the endpoint 1 distance is at least $P_{s,t_1}(E_s)-G_s(E_s)$ and the endpoint 2 distance at least $G_s(E_s)-P_{s,t_2}(E_s)$; integrate both and use (9.5). Since $(P_{s,t_1}(E_s)-C_s)/d_s=1/2$, the constant terms cancel in $D$, and

$$
\int D\,d\omega\le(1/d_p+1/d_\beta)e\le26e.
\tag{12.2}
$$

In the full p triangle slack (9.6), $h_2$ and $h_3$ are upper-box violations at the distinct complete words $w_{2,1}$ and $w_{3,1}$. Their endpoint upper masses are, respectively,

$$
\max_iP_{p,t_i}(w_{2,1})=16/729,
\qquad
\max_iP_{p,t_i}(w_{3,1})=1944/390625.
$$

Thus $H$ is bounded by that complete nonnegative slack. Tonelli's theorem for its countable sum and the two endpoint expected distances yield $\int H\,d\omega\le2e$. Integrating (10.2), without restricting the support of $\omega$, gives

$$
m:=\int d(u,v)\,d\omega
\le112(26+2\cdot13000)e=2914912e.
\tag{12.3}
$$

The functions $D,H,d$ are bounded continuous functions on the compact rectangle; all denominator bounds were retained. TV as a countable sum of continuous coordinate terms is Borel, and the uniform geometric tails make it continuous jointly in $(u,v,t)$. Hence all displayed integrals are well defined for every Borel probability, not just for discrete mixtures.

**Proof of Theorem 9.2, endpoint selector and complete-law recurrence.** Assign each $(u,v)$ to the nearest endpoint pair $(t_i,t_i)$ in $\ell^1$ distance, with ties assigned to endpoint 1. The two distance functions are continuous, so this is a Borel selector. Let $\lambda$ be the probability assigned to endpoint 1.

For the entire p law, including the infinite outcome,

$$
\operatorname{TV}(G_p^{u,v},P_{p,t_i})
\le2(|u-t_i|+|v-t_i|).
\tag{12.4}
$$

To verify this without truncating a tail, put $x=|u-t_i|,y=|v-t_i|$ and let $q_p,q_\beta$ be the distances of the two complete phase laws to their endpoint laws. Split each complete law by its first emission. Inserting a law with matched first-emission weights, then using triangle inequalities and the injective prefix maps, gives

$$
q_p\le x+(1-u)q_\beta,\qquad
q_\beta\le y+vq_p.
$$

These are normalized residual laws; the infinite word is in the residual carrier too. Rearrangement and $a=(1-u)v\le4/15$ give

$$
q_p\le\frac{x+(1-u)y}{1-a}
\le\frac{15}{11}(x+y)\le2(x+y).
\tag{12.5}
$$

Thus the expected p distance to the selected endpoint law is at most $2m$. Applied to $E_p$, this and (12.1) give

$$
d_p|\lambda-1/2|\le e+2m.
\tag{12.6}
$$

Indeed the selected endpoint event average is $\lambda P_{p,t_1}(E_p)+(1-\lambda)P_{p,t_2}(E_p)$, whose difference from $C_p$ is exactly $d_p(\lambda-1/2)$.

## 13. Uniform interior excess and the rational constant

**Proof of Theorem 9.2, the unchanged closed interior interval.** Consume the full-word interior excess of [NATIVE, (6.1)–(6.2)]. Its word is $w_{3,1}$, with source mass

$$
J(r)=r^3(1-r)^5,\qquad
J'(r)=r^2(1-r)^4(3-8r).
$$

Thus $J$ is nonincreasing on the entire closed $I_0=[3/8,5/13]$, including its zero derivative at the left boundary. The larger endpoint mass is $J(t_2)>J(t_1)$, and

$$
\begin{aligned}
J(r)&\ge J(5/13)=J(t_2)+\eta,\\
\eta&=(5/13)^3(8/13)^5-(2/5)^3(3/5)^5\\
&=\frac{14219478376}{318644812890625}>0.
\end{aligned}
\tag{13.1}
$$

Apply (9.6) with $D=P_{p,r}$. This one full coordinate is outside the endpoint box by at least $\eta$, so

$$
\tfrac12\operatorname{TV}(P_{p,t_1},P_{p,r})
+\tfrac12\operatorname{TV}(P_{p,t_2},P_{p,r})
\ge\rho_p+\eta/2.
\tag{13.2}
$$

Let $f_i=\operatorname{TV}(P_{p,t_i},P_{p,r})$. Reverse triangle inequalities imply $|f_1-f_2|\le d_p$. The selected endpoint comparison (12.4) and (12.6) now give

$$
\begin{aligned}
\rho_p+e
&\ge\int\operatorname{TV}(G_p^{u,v},P_{p,r})\,d\omega\\
&\ge\lambda f_1+(1-\lambda)f_2-2m\\
&\ge\rho_p+\eta/2-d_p|\lambda-1/2|-2m\\
&\ge\rho_p+\eta/2-e-4m.
\end{aligned}
\tag{13.3}
$$

Consequently $4e+8m\ge\eta$. Using (12.3) proves the exact identities and strict rational comparison

$$
e\ge\frac{\eta}{4+8(2914912)}
=\frac{\eta}{23319300}
=\frac{3554869594}{1857643496310087890625}=c_*>
\frac1{10^{12}},
$$

$$
3554869594\cdot10^{12}-1857643496310087890625
=1697226097689912109375>0.
\tag{13.4}
$$

The suspended interior constraint remains in (9.3), although this lower estimate only needs the p interior constraint and both phases' endpoint constraints. Every bound applies before minimization, on the entire phase-asymmetric rectangle and the entire Borel class; neither $u=v$, a finite preset support nor a modified risk order is imposed.

For completeness, the minimum in (9.3) is the original minimum rather than an infimum over a replacement class. Finite-coordinate probabilities are continuous, and the bounds $(4/15)^L,(6/25)^L$ make finite-partition TV distances converge uniformly to complete TV. Joint continuity on $S\times[t_1,t_2]$ follows. Probability measures on compact $S$ are weakly compact; uniform continuity in $r$ and weak continuity of integration make all six expected distances, and their maximum, continuous on $\mathcal P(S)\times I_0$. This is the compactness step already used in Lemma 4.1. The minimum therefore exists and inherits (13.4). Its attainment inside this enlarged comparison class does not construct a common optimal finite observer. This completes the proof of Theorem 9.2. $\square$

The complete-law viewpoint also occurs in Taolue Chen and Stefan Kiefer, *On the Total Variation Distance of Labelled Markov Chains*, CSL-LICS, DOI [10.1145/2603088.2603099](https://doi.org/10.1145/2603088.2603099), [author preprint](https://arxiv.org/html/1405.2852v1), Theorem 7 and Corollary 8. Their two converging bounds and rational approximation concern a supplied pair of labelled-chain laws. They do not optimize (9.3) or transfer configuration risk along an acquired return. Here the complete-coordinate identity, tails and rational enclosures provide the elementary intermediate arguments; the additional quantitative content is (10.2), (12.3) and (13.4).

## 14. Exact original-source necessary acquired motion

**Definition 14.1 (source and individual same-update contract).** Retain precisely the source and observer class of Theorem 2.1. Fix $m=2,d=1,\ell=2,n=4$, and draw one $K$ before all Reads from a finite or countable prior with

$$
\mu(1)>0,\qquad\mu(2)>0,\qquad\mu(\{k\ge3\})>0,
\qquad r_k=F_{k+1}/F_{k+3}.
$$

Conditional on that same $K$, every paid seed and payload Read is independent with alpha probability $r_k$. Retain both seeds, all paid equal-pair rejections, every marker record, all positive finite returns and partial parses, the write-before-third-latch rule, and the full original $C_0$ with records, permissions, completion, unique pending and delivered Stop. There is no reset, depth redraw, conditioning on future completion, extra observation or controller port.

An observer has a fixed finite COMPLETE carrier, source-independent initialization and fixed time-homogeneous source-independent acquired-letter kernels. COMPLETE includes the original control and records, private labels, selectors, tables, workspace, addresses, output indices and persistent randomness. Its decoder reads one actual configuration. Each decoded full legal law is generated by that configuration's own synthetic emissions and those very same acquired updates. There is no free archive, clock, advice, tape, exact posterior, continuous register, correlated source seed or runtime configuration-distribution vector. Zero and unit original emissions, arbitrary real kernel entries in the abstract stochastic-rule model, and original noncompletion mass remain permitted. No new exact-real sampling oracle or preservation of a fixed resource budget is assumed.

For each original positive fourth history $h$, let $\rho_h$ be its conditional configuration row and $D_z$ its full decoded law. Retain configuration-before-TV risk and its original all-positive-history phase suprema:

$$
e_{\mathrm{conf}}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu),\quad
R_{\mathrm{conf},s}=\sup_{h\in\mathcal H_s}e_{\mathrm{conf}}(h),\quad
\varepsilon_s=R_{\mathrm{conf},s}-\rho_s\ge0,
$$

$$
e_M=\max(\varepsilon_p,\varepsilon_\beta).
\tag{14.1}
$$

The $\rho_s$ on the right are the separate full-tail radii in Definition 9.1. They are not terminal-output radii or actual-history-average losses.

For a fourth p history let $C_h$ be the actual acquired update for the two paid Reads $\beta\alpha$. The return preserves the original control and held records, so both configurations' laws are rendered on the same complete carrier. Retain the source statistic

$$
\mathcal V(M)=\sup_{h\in\mathcal H_p}
\sum_{x,z}\rho_h(x)C_h(x,z)\operatorname{TV}(D_x,D_z).
\tag{14.2}
$$

**Corollary 14.2 (explicit necessary motion with all original hypotheses).** Every observer in Definition 14.1 satisfies

$$
\boxed{\mathcal V(M)\ge\frac{11}{6}
\left(c_*-\frac{1183}{121}e_M\right)_+.}
\tag{14.3}
$$

If common exact conf/conf attainment exists in this class, it requires

$$
\mathcal V(M)\ge\frac{11c_*}{6}
=\frac{19551782767}{5572930488930263671875}
>\frac{11}{6\cdot10^{12}}.
\tag{14.4}
$$

Every sequence of allowed observers on allowed priors with $e_M\to0$ satisfies $\liminf\mathcal V(M)\ge11c_*/6$. Finite shapes and priors may vary while each retains every condition of Definition 14.1. Neither such a sequence nor a common exact optimizer is asserted to exist.

**Proof.** The conditioning in (14.2) is the original actual-return conditioning, not synthetic sampling. Given an acquired $h$, source-independent initialization and updates factor observer randomness from the source likelihood; $K$ and the actual configuration are conditionally independent. The joint probability is precisely (2.1a):

$$
\Pr(K=k,Z_h=x,\text{next actual word}=\beta\alpha,
Z_{h\beta\alpha}=z\mid h)
=\nu_h(k)\rho_h(x)a_{r_k}C_h(x,z).
\tag{14.5}
$$

Summing in $k$ and dividing by the positive actual word probability $\sum_k\nu_h(k)a_{r_k}$ leaves $\rho_h(x)C_h(x,z)$. There is no tilt by the decoder's synthetic emissions. The original source posterior can change on this return, but $\mathcal V$ measures the actual joint configurations' decoded-law motion.

Apply Theorem 2.1, under its exact extraction, realization and clipping suppliers [MIXSEP], [PAID], [CLIP], to this observer and the same source. It gives

$$
\gamma\le\frac{1183}{121}e_M+\frac6{11}\mathcal V(M).
\tag{14.6}
$$

The coefficient is the source's simultaneous propagation, not a law-risk substitution: with $T_p=(30\varepsilon_p+20\varepsilon_\beta)/11$ and $T_\beta=(12\varepsilon_p+30\varepsilon_\beta)/11$, its two bounds are

$$
\varepsilon_p+T_p+\tfrac4{11}(V+2T_p)
=\frac{691\varepsilon_p+380\varepsilon_\beta}{121}+\frac4{11}V,
$$

$$
\varepsilon_\beta+T_\beta+\tfrac6{11}(V+2T_p)
=\frac{492\varepsilon_p+691\varepsilon_\beta}{121}+\frac6{11}V,
\qquad V\le\mathcal V(M).
\tag{14.7}
$$

This preserves the placement of configuration TV; $492+691=1183$ is the larger excess coefficient sum. The arbitrary original observer is not narrowed to $S$: the supplied extraction and clipping comparison in §6, including zero/unit emissions and original infinite mass, is what links it to (9.3). Combining (14.6) with Theorem 9.2 and $\mathcal V(M)\ge0$ gives (14.3); exact attainment and liminf give (14.4) and the sequence consequence.

No positive unrestricted common risk gap follows from (14.3) while acquired motion is unrestricted. It also does not restore zero marginalized defect, preserve a defect or fee budget, replace either conf coordinate by law risk, prove a minimum COMPLETE resource, or transfer to a static no11 label, immutable-address cache, FIB window archive, KBonacci process or physical time/energy model. Such consequences require additional joint source, operation, update, full-law and cost hypotheses. In particular the deterministic fixed-law all-cut result of [future-response sufficiency](RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md) §§39–40 has neither the arbitrary stochastic configuration contract nor individual same-update generation; it cannot replace Theorem 2.1 in this proof. The qualitative comparison, sign polynomials, endpoint fractions, triangle slack, interior excess and source motion relation remain the credited suppliers of this quantitative extension. $\square$

## 追加锚（本行以下为增补区）
