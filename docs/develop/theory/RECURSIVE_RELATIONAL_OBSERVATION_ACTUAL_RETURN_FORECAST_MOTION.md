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
