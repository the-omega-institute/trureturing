# Common complete-tail calibration requires suspended emission heterogeneity

**Mathematical status.** This volume gives ordinary mathematical proofs in the unchanged complete-tail configuration-risk model. It has no new Lean kernel verification or frozen formal status. Public supplier arguments are used with their stated hypotheses and remain fallible ordinary mathematics.

## 1. The original source and the new restricted gap

**Definition 1.1 (unchanged source and complete histories).** Set $m=2,d=1,\ell=2,n=4$, with $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$. Install a finite or countable probability prior $\mu$ on positive integers, with $\mu(1),\mu(2)>0$. Draw one $K$ before the first actual Read. Conditional on that same $K=k$, every seed and payload Read is independent, with alpha probability

$$
r_k=\frac{F_{k+1}}{F_{k+3}},\qquad
r_1=a=\frac13,\qquad r_2=b=\frac25,\qquad
r_k\in[3/8,5/13]\quad(k\ge3).
$$

The paid seed parser rejects equal pairs, accepts alpha-beta as seed 0 and beta-alpha as seed 1. Each payload segment starts at p: alpha completes marker 0 and beta suspends. At suspension, alpha returns to p and beta completes marker 1. The first three completions advance segments; the third record write precedes its latch. The fourth completion enters its matching pendingStop, whose unique original Stop enters deliveredStop. Neither terminal admits Read.

Keep the entire original finite control $C_0$: both seeds, parser, selectors, bare fields, the full marker tree, held $B,Q^+,Z$ records, write/latch flags, permissions, completion and Stop delivery. Both seeds, every marker triple, every positive finite seed-rejection history and every positive finite payload-return history remain admissible. There is no source reset, fresh depth, future-event conditioning, new actual observation or controller port. These are the source and full-record conventions of [ST, Sections 1–3], [CLIP, Section 1] and [PAID, Section 1].

Write $\mathcal H_p,\mathcal H_\beta$ for all positive finite fourth-segment histories at p and suspension after the third latch. They include arbitrarily many fourth returns. The first p cut $\mathcal H_3$ is a proper subdomain and is not substituted for $\mathcal H_p$.

**Definition 1.2 (complete residual laws).** Put $a_r=r(1-r)$ and

$$
w_{j,0}=(\beta\alpha)^j\alpha,\qquad
w_{j,1}=(\beta\alpha)^j\beta\beta,\qquad j\ge0.
$$

The p future carrier consists of these finite words and its infinite noncompletion word. At suspension it consists of beta, $\alpha w_{j,c}$ and its infinite noncompletion word. Fixed-depth raw masses are

$$
P_{p,r}(w_{j,0})=ra_r^j,\qquad
P_{p,r}(w_{j,1})=(1-r)^2a_r^j,
$$

$$
P_{\beta,r}(\beta)=1-r,\qquad
P_{\beta,r}(\alpha w_{j,0})=r^2a_r^j,\qquad
P_{\beta,r}(\alpha w_{j,1})=r(1-r)^2a_r^j.
\tag{1.1}
$$

Both infinite-word masses are zero. For current original control and records $c$, the renderer $I_c$ retains every future Read and inserts its original deterministic event blocks, held records, permissions, completion and Stop. Reading the letters back is its inverse. This measurable bijection preserves TV and commutes with removing the next operation and its event block [ST, Section 2.1]. The already acquired suspended beta is not a future Read.

At an actual positive finite history $h$, including all paid rejections and partial parses in its counts,

$$
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
 {\sum_t\mu(t)r_t^{A(h)}(1-r_t)^{B(h)}},\qquad
T_h^\mu=(I_{C_0(h)})_*\sum_k\nu_h(k)P_{s,r_k}.
\tag{1.2}
$$

The denominator is positive. The same actual $K$ supplies the acquired prefix and unread letters. Counts and posterior vectors are analysis objects, not runtime inputs.

**Definition 1.3 (finite observer, risks and exact generation).** An observer has one fixed finite COMPLETE configuration carrier, source-independent initialization and fixed time-homogeneous source-independent acquired-letter stochastic updates. COMPLETE includes $C_0$, tables, program selectors, numerical representation, workspace, addresses, output indices and all persistent randomness. Runtime reads its actual configuration. It has no continuous hidden register, uncounted tape, correlated source seed, readable distribution or posterior vector, clock, archive or advice.

From each configuration $z$, its synthetic emissions and those same acquired-letter kernels generate its decoded complete law $D_z$. For a legal operation $o$ and residual event $E$,

$$
D_z(oE)=q_z(o)\sum_{z'}P_o(z,z')D_{z'}(E).
\tag{1.3}
$$

The cylinder contains the original event block. This equality holds also at $q_z(o)=0$; the actual successor kernel still exists. Synthesis makes no source call. The output describes a finite installed generator and its current configuration, rather than an infinite table or a free exact-real probability oracle.

For the actual conditional configuration row $\rho_h$, define

$$
\overline D_h=\sum_z\rho_h(z)D_z,
$$

$$
e_{\mathrm{law}}(h)=\operatorname{TV}(\overline D_h,T_h^\mu),\qquad
e_{\mathrm{conf}}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu),
$$

$$
R_{j,s}=\sup_{h\in\mathcal H_s}e_j(h),\qquad
\rho_p=\frac{1116529}{22781250},\qquad
\rho_\beta=\frac{239}{6750},
$$

$$
\varepsilon_s(M)=R_{\mathrm{conf},s}(M)-\rho_s\ge0,\qquad
e(M)=\max\{\varepsilon_p(M),\varepsilon_\beta(M)\}.
\tag{1.4}
$$

TV is the event-supremum convention, equivalently half the countable $\ell^1$ distance here. The radii and their original finite positive-history lower witnesses are supplied by [ST; CLIP]. The terminal projection values $13/266,9/266$ are different quantities. Marginal-law TV, configuration-before-TV and actual-history-average loss are not identified.

At a positive actual history $h$, put $q_h(o)=\sum_z\rho_h(z)q_z(o)$ for a legal next operation $o$. If $q_h(o)>0$, let $\operatorname{res}_o\overline D_h$ condition on that operation and delete it and its original event block. Define the supplied marginalized update defect by

$$
\delta(h,o)=
\begin{cases}
\operatorname{TV}(\operatorname{res}_o\overline D_h,\overline D_{ho}),&q_h(o)>0,\\
0,&q_h(o)=0.
\end{cases}
$$

The zero case creates no conditional law; the actual successor and its risk remain in the domain. Let $\Delta_4$ take the supremum over legal operations at positive fourth-segment active and pending cuts, and let $\Delta_{\mathrm{all}}$ take the supremum over every original positive operation cut. The pendingStop successor is deterministic and has zero defect; deliveredStop has empty supremum zero. Only actual-history marginalized conditioning/update coherence is relaxed. Exact individual generation (1.3) remains an obligation, including at zero predicted probabilities.

For a fixed installed prior and an allowed counted resource allocation, an achievable comparison tuple is

$$
(R_{\mathrm{law},p},R_{\mathrm{conf},p},
 R_{\mathrm{law},\beta},R_{\mathrm{conf},\beta},
 \Delta_4,\Delta_{\mathrm{all}})
$$

produced by one observer on that same source and all its original histories. Every comparison below uses that observer or the explicitly constructed comparison table with its own charged resources. No hard defect budget is assumed, no zero-defect recovery theorem is asserted, and separate attainable coordinates are not identified with joint attainment.

**Definition 1.4 (constant emission on the designated held-record fibre).** Use the original seed-1, marker-100 held-record fibre reached by

$$
S=\beta\alpha\mid\beta\beta\alpha\alpha.
\tag{1.5}
$$

Let $\mathcal Z_\beta^*(M)$ be the union of suspended configurations having positive probability after some positive finite actual history on this fibre, as in [PAID, Section 14]. Say that $M$ has constant suspended emission on this fibre if there is one $s_0\in[0,1]$ such that every $y\in\mathcal Z_\beta^*(M)$ has next synthetic alpha probability $s_0$.

This condition permits arbitrary finite private kernels, arbitrary p emissions, transient modes, zero and unit transition entries, and arbitrary behavior on other record fibres. In particular $s_0$ may be strictly interior, zero or one. It asserts no equality of complete suspended laws or successor kernels.

**Theorem 1.5 (evaluated original-observer gap).** Every observer of Definitions 1.1–1.4 satisfies

$$
e(M)>\frac1{195200}.
\tag{1.6}
$$

Consequently the infimum of $e$ in this entire class is at least $1/195200$. Every exact common conf/conf attainer must have at least two distinct suspended emission probabilities among the reachable configurations on the designated held-record fibre. In any sequence with both configuration excesses tending to zero, every sufficiently late member must have such emission heterogeneity.

The theorem is uniform over all finite COMPLETE carriers and all installed finite or countable priors with positive endpoint masses. It does not require a supported nonendpoint. It gives a positive gap for the stated class, not for the unrestricted class. No exact unrestricted attainer, vanishing family or fixed-resource optimum is asserted.

The proof is completed in Section 4. Its new ingredient is the joint four-word constraint of Section 3. It compares complete-word residuals from one stationary actual chain; neither phase is assigned an independent optimizing law.

## 2. The supplied original-domain reduction and endpoint consequences

**Mathematical citation 2.1 (common actual circulation and clipping).** [PAID, Lemma 14.1] supplies, for every original finite observer, finite p and suspended carriers $X,Y$, actual noncompleting kernels $B:X\to Y$, $A:Y\to X$ and probability rows $\pi,\tau$ on the fibre (1.5), with

$$
\pi B=\tau,\qquad \tau A=\pi.
\tag{2.1}
$$

Positive-row configurations are reachable original configurations on that fibre. Their complete raw decoders are the original decoders pulled back through their own $I_c$. For every supported depth, their configuration losses on these common rows are bounded by the corresponding original phase risks. These are stationary analysis rows, obtained from positive paid histories and Cesaro averaging; the original process itself need not be stationary or irreducible. Transient labels can disappear from the extracted support, without being removed from the original history domain.

Delete zero-row labels; nonnegativity in (2.1) excludes transitions into them from positive-row labels. Clip both synthetic emission vectors to $[a,b]$, retain $B,A,\pi,\tau$ and regenerate their complete laws. The source-specific coupling of [CLIP, Theorem 3.1] supplies one finite regular stationary comparison table with

$$
\widehat\varepsilon_p\le\frac{41\varepsilon_p+20\varepsilon_\beta}{11},\qquad
\widehat\varepsilon_\beta\le\frac{12\varepsilon_p+41\varepsilon_\beta}{11},
$$

$$
\widehat e\le\frac{61}{11}e(M).
\tag{2.2}
$$

The clipping theorem can be applied on the extracted closed support directly. Its endpoint coordinate identity bounds

$$
\sum_x\pi_x|u_x-[u_x]_{[a,b]}|\le2\varepsilon_p,
\qquad
\sum_y\tau_y|v_y-[v_y]_{[a,b]}|\le2\varepsilon_\beta.
$$

The regenerated clipped return kernel is entrywise at most $(4/15)BA$. Since $\pi BA=\pi$, the supplied same-update coupling bounds the configuration-average change of entire p laws by $(30\varepsilon_p+20\varepsilon_\beta)/11$, and that of suspended laws by $(12\varepsilon_p+30\varepsilon_\beta)/11$ [CLIP, equations (3.6)–(3.10)]. Adding the original phase bounds yields (2.2). These are averages of complete-law distances on the same rows; they require neither pointwise minimax centering nor a posterior variance identity.

These comparisons include original zero/one emissions and possible original noncompletion mass. The regular table has the original-domain product realization and exact individual generation [PAID, Lemma 2.1.1]. It need not preserve a fixed resource budget or a hard defect bound. No new source experiment, runtime row or posterior is installed.

If Definition 1.4 holds, every positive extracted suspended label has emission $s_0$, and every clipped suspended emission is the same $s=[s_0]_{[a,b]}$. Thus this supplied reduction preserves the property needed below.

**Definition 2.2 (regular table and complete mean laws).** A regular stationary table has (2.1), synthetic alpha probabilities $u_x,v_y\in[a,b]$, and exact complete raw laws

$$
Q_x=u_x\delta_\alpha+(1-u_x)\beta\sum_yB_{xy}W_y,
$$

$$
W_y=(1-v_y)\delta_\beta+v_y\alpha\sum_xA_{yx}Q_x.
\tag{2.3}
$$

Every synthetic return has probability at most $(2/3)(2/5)=4/15$. These are normalized complete laws; the legal infinite outcomes remain with mass zero. Write

$$
\overline Q=\sum_x\pi_xQ_x,\qquad
\overline W=\sum_y\tau_yW_y.
$$

Suppose nonnegative $\epsilon_p,\epsilon_\beta$ bound the two endpoint mean losses:

$$
\operatorname{TV}(\overline Q,P_{p,r})\le\rho_p+\epsilon_p,\qquad
\operatorname{TV}(\overline W,P_{\beta,r})\le\rho_\beta+\epsilon_\beta,
\quad r\in\{a,b\}.
\tag{2.4}
$$

Expected endpoint configuration losses with these bounds imply (2.4) by convexity. No individual configuration is assumed to be a minimax center.

**Mathematical citation 2.3 (endpoint events and boxes).** Use the supplied positive-difference events

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\}.
$$

Their endpoint masses and midpoints are

$$
P_{p,a}(E_p)=\frac{412}{729},\quad
P_{p,b}(E_p)=\frac{7299}{15625},\quad
C_p=\frac{11758471}{22781250},
$$

$$
P_{\beta,a}(E_\beta)=\frac{22}{27},\quad
P_{\beta,b}(E_\beta)=\frac{93}{125},\quad
C_\beta=\frac{5261}{6750},\quad
c=1-C_\beta=\frac{1489}{6750}.
\tag{2.5}
$$

The event-mass differences are exactly $2\rho_p,2\rho_\beta$ [ST; CLIP; INTERIOR]. Projection of (2.4) to these complete events yields

$$
|\overline Q(E_p)-C_p|\le\epsilon_p,\qquad
|\overline W(E_\beta)-C_\beta|\le\epsilon_\beta.
\tag{2.6}
$$

Indeed a law within $d/2+\epsilon$ of both endpoint laws has event mass between their midpoint minus $\epsilon$ and midpoint plus $\epsilon$ whenever that event realizes their TV distance $d$.

The full countable coordinate identity also gives

$$
\sum_w\operatorname{dist}\bigl(\overline Q(w),
 [\min(P_{p,a}(w),P_{p,b}(w)),\max(P_{p,a}(w),P_{p,b}(w))]\bigr)
\le2\epsilon_p.
\tag{2.7}
$$

To see this, sum $|q-A|+|q-B|=|A-B|+2\operatorname{dist}(q,[\min(A,B),\max(A,B)])$ over all coordinates and divide by two. The left endpoint-loss sum is at most $2\rho_p+2\epsilon_p$, whereas endpoint TV is $2\rho_p$. Include the infinite outcome in that sum. In particular

$$
\overline Q(w_{3,1})\le q_*+2\epsilon_p,\qquad
q_* =P_{p,b}(w_{3,1})=\frac{1944}{390625}.
\tag{2.8}
$$

The other endpoint is smaller: their difference is $254584/2562890625>0$. These are consequences of complete-law losses, rather than replacements of those losses by a scalar target.

## 3. A joint four-word response constraint

**Theorem 3.1 (constant suspended emission separator).** Let a regular stationary table satisfy (2.4) and $v_y=s$ for every positive-row suspended label, for one $s\in[a,b]$. Put $\epsilon=\max(\epsilon_p,\epsilon_\beta)$. Then

$$
\epsilon>\frac1{35200}.
\tag{3.1}
$$

More precisely the same $s$ must satisfy the two joint constraints

$$
C_p-F(s)\le\epsilon_p+5\epsilon_\beta,
\qquad
G(s)-q_*\le2\epsilon_p+\epsilon_\beta/5,
\tag{3.2}
$$

where

$$
F(s)=\left(1-\frac cs\right)
 \left(1+\frac{19}{15}s+\frac{271}{225}s^2\right)
 -\frac25s(1-s)\left(1+\frac{19}{15}s\right),
$$

$$
G(s)=\frac4{15}\left(\frac{31}{15}s^3
 +\frac{29}{15}s^4-4cs^2\right).
\tag{3.3}
$$

These constraints use the same complete laws and the same unweighted acquired circulation. Their incompatibility at small $\epsilon$ is evaluated below.

Proof. Put $C=BA$, $U_x=1-u_x$, $L=3/5$, $H=2/3$. Thus $U_x\in[L,H]$ and $\pi C=\pi$. Let $X_0,X_1,\ldots$ be the finite analysis Markov chain with initial row $\pi$ and kernel $C$, and write $U_i=U_{X_i}$. All its one-time marginals agree. Define

$$
m=\mathbb E U_0,\qquad
M_j=\mathbb E\prod_{i=0}^{j-1}U_i\quad(j\ge1),\qquad M_0=1.
$$

This chain is an analysis coupling of actual private updates. Its index is not a runtime clock. The $U_i$ are private configuration statistics, not source posterior variables.

Since $v=s$, the actual p-return kernel is still $C$, while its synthetic survival matrix is $s\operatorname{diag}(U)C$. The marker-1 completion vector is $(1-s)U$. Expanding the same-update equations (2.3) therefore gives the exact complete-word identities

$$
\overline Q(w_{j,1})=(1-s)s^jM_{j+1},\qquad j\ge0.
\tag{3.4}
$$

The other actual flow $\tau A=\pi$ gives, on entire complete laws,

$$
\overline W=(1-s)\delta_\beta+s\alpha\overline Q.
\tag{3.5}
$$

It follows in particular that

$$
\overline W(E_\beta)=1-s+s(1-s)m.
$$

Set $d=\overline W(E_\beta)-C_\beta$. Equations (2.6) and (2.5) give

$$
|d|\le\epsilon_\beta,\qquad s(1-s)m=s-c+d.
\tag{3.6}
$$

There is one common $m$ in all four moments. No separately attainable moment extremum is assumed jointly attainable.

Here are elementary bounds used inside this source-specific proof. Stationarity and $xy\le(x^2+y^2)/2$ give $M_2\le\mathbb E U_0^2$. The identity

$$
x^3+y^3+z^3-3xyz
=\frac{x+y+z}{2}\bigl((x-y)^2+(y-z)^2+(z-x)^2\bigr)
$$

gives $M_3\le\mathbb E U_0^3$. On $[L,H]$ the quadratic and cubic chords give

$$
M_2\le(L+H)m-LH,\qquad
M_3\le(L^2+LH+H^2)m-LH(L+H).
\tag{3.7}
$$

The chord differences factor as $(t-L)(t-H)$ and $(t-L)(t-H)(t+L+H)$, respectively, and are nonpositive.

For four numbers $x_i\in[L,H]$ one also has

$$
\prod_{i=0}^3x_i\ge LH^2\left(\sum_{i=0}^3x_i-L-2H\right).
\tag{3.8}
$$

The difference is affine in each coordinate, so its minimum over the box is attained at a vertex; equivalently it is a convex combination of vertex values. With $k$ coordinates equal to $H$, its five possible values are

$$
\begin{array}{c|ccccc}
k&0&1&2&3&4\\ \hline
\text{difference}&L(H-L)^2(L+2H)&LH(H-L)^2&0&0&H^2(H-L)^2.
\end{array}
$$

All are nonnegative. Taking expectations on the same stationary path gives

$$
M_4\ge LH^2(4m-L-2H).
\tag{3.9}
$$

Bounds (3.7)–(3.9) are elementary product estimates, not separate new general inequalities.

Now (3.4), (3.7) and $\overline Q(E_p)\ge C_p-\epsilon_p$ imply

$$
C_p-\epsilon_p
\le(1-s)(m+sM_2+s^2M_3)
\le F(s)+\left(\frac1s+\frac{19}{15}+\frac{271}{225}s\right)d.
$$

The last equality uses (3.6), $L+H=19/15$, $LH=2/5$ and $L^2+LH+H^2=271/225$. The displayed coefficient is positive and less than $5$ on $[a,b]$. For example it is at most $3+19/15+(271/225)(2/5)<5$. This proves the first inequality in (3.2).

Likewise (3.4) at $j=3$, (3.9) and (3.6) give

$$
\overline Q(w_{3,1})
\ge(1-s)s^3LH^2(4m-L-2H)
=G(s)+4LH^2s^2d
\ge G(s)-\epsilon_\beta/5.
$$

Here $LH^2=4/15$, $L+2H=29/15$ and $4LH^2s^2\le64/375<1/5$. Combine with (2.8) to obtain the second inequality in (3.2).

Both $F$ and $G$ are strictly increasing on $[a,b]$. For $F$, expansion yields

$$
F'(s)=\frac c{s^2}+\left(\frac{13}{15}-\frac{271}{225}c\right)
 +\frac{494}{225}s+\frac{38}{25}s^2>0.
$$

Indeed $0<c<1/4$, so the parenthesized coefficient exceeds $509/900$. For $G$,

$$
G'(s)=\frac4{15}s\left(\frac{31}{5}s+\frac{116}{15}s^2-8c\right)>0,
$$

because $s\ge1/3$ and $c<1/4$ make even $31s/5-8c>1/15$.

Take the single rational cut $s_*=3679/10000$. Exact substitution gives

$$
C_p-F(s_*)-\frac1{4000}
=\frac{12788985483823}{33524887500000000000}>0,
$$

$$
G(s_*)-q_*-\frac1{16000}
=\frac{3659950318741}{5062500000000000000}>0.
\tag{3.10}
$$

If $s\le s_*$, monotonicity and (3.2) imply $6\epsilon>1/4000$, so $\epsilon>1/24000>1/35200$. If $s\ge s_*$, they imply $(11/5)\epsilon>1/16000$, so $\epsilon>1/35200$. These cases exhaust the entire interval, including its endpoints. This proves (3.1). ∎

The four-word constraint does not assert log-convexity of complete-word masses, independence of private chain coordinates, reversibility or a constant successor mean. Only the one-time marginal of the actual analysis chain is stationary. The full laws in (2.3) remain those of the same finite generator.

## 4. Lifting the separator to every original finite carrier in the class

**Proof of Theorem 1.5.** Apply Mathematical citation 2.1 to the original observer. Its positive suspended support lies among the reachable configurations in Definition 1.4. Clipping therefore produces one regular stationary table with constant suspended emission $s\in[a,b]$, even when $s_0=0$ or $1$.

For each endpoint, its expected configuration loss is at most $\rho_s+\widehat\varepsilon_s$. Convexity in the decoder gives the mean-law bounds (2.4) with $\epsilon_s=\widehat\varepsilon_s$. Theorem 3.1 and (2.2) imply

$$
\frac1{35200}<\widehat e\le\frac{61}{11}e(M),\qquad
 e(M)>\frac{11}{61\cdot35200}=\frac1{195200}.
$$

The endpoint lower bounds ensure the excesses are nonnegative. Taking the infimum proves its non-strict lower bound. An exact common conf/conf attainer has $e=0$ and thus cannot satisfy Definition 1.4. A sequence with $e\to0$ is eventually below $1/195200$, so its late members also cannot satisfy that definition. ∎

This proof retains arbitrary original transient modes and arbitrary original emission entries. It does not assume that every original configuration is recurrent: the supplied support inclusion is sufficient. No originally admissible history is removed. The fixed fibre supplies necessary bounds for the original full-domain suprema; it does not replace the domain by that fibre or by a finite set of probes.

The comparison can enlarge or change counted resources. The conclusion is therefore a uniform lower bound over the stated class, not a budget-preserving reduction or a fixed-resource optimum. Exact per-configuration generation follows from the actual program before reduction and from the changed same-update program after clipping. Marginalized coherence is not inferred from either statement.

## 5. The new exclusion differs from the supplied structural exclusions

**Proposition 5.1 (a lawful interior example with noncollapsed laws and both update directions).** There is an original-domain rational finite observer with constant suspended emission strictly inside $(a,b)$, distinct p and suspended complete laws, positive complete-return motion, positive absolute alpha-edge change and positive alpha-edge decrease. Neither acquired interface is a complete redraw, and one p decoder is outside the entire constant-parameter stopped-p mixture family on $[a,b]$.

Proof. On each original record fibre install the product realization of Definition 2.2 with two labels, fair rows and

$$
u_0=a,\qquad u_1=b,\qquad
v_0=v_1=s_*=\frac{3679}{10000},\qquad
B=I,\qquad A=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\tag{5.1}
$$

Both acquired flows preserve the fair rows. The latch row is sampled source-independently after the third record write and latch in that same original update. Earlier synthetic letters are fair; all original controls, records, permissions, completion and Stop are retained. This is the full original-domain construction supplied by [PAID, Lemma 2.1.1]. No comparison depth, posterior or analysis chain is a runtime port.

The p laws differ on immediate alpha by $b-a$. The suspended laws differ on alpha-alpha by $s_*(b-a)$ because their alpha successors have p emissions $b,a$, respectively. Both successor-law dispersions and phase diameters are positive. Each acquired kernel is a deterministic bijection with different rows, rather than a row-independent redraw. An actual return swaps the p labels, so its expected complete-law motion is at least $b-a>0$. On the suspended alpha edge the expected decrease is $(s_*-a)/2>0$ and the expected absolute change is $(b-a)/2>0$. Its suspended interior tent mass is $\min(s_*-a,b-s_*)>0$.

For the p law starting at label 1 put $q_j=Q_1(w_{j,0})$. Exact generation from (5.1) gives

$$
q_1=(1-b)s_*a,\quad
q_2=(1-b)(1-a)s_*^2b,\quad
q_3=(1-b)^2(1-a)s_*^3a.
$$

Consequently

$$
q_2^2-q_1q_3
=(1-b)^2(1-a)s_*^4\bigl((1-a)b^2-(1-b)a^2\bigr)>0.
$$

The bracket equals $1/25>0$. For a Borel stopped-p mixture, these coordinates would be $q_j=\int r[r(1-r)]^j\,d\kappa(r)$, and Cauchy gives $q_2^2\le q_1q_3$. Thus this particular decoder is not such a mixture. This elementary moment check only locates the example; it is not the separator proof. ∎

The example is not near-optimal: Theorem 1.5 applies to it. Its purpose is to separate the newly excluded class from the no-interior-emission class of INTERIOR, the zero-return-motion class of MOTION, the alpha-conserving class of ALPHA, the nondecreasing-alpha class of DIRECTION, the complete-redraw classes of PAID and the native-mixture classes. Positive values of those supplied necessary statistics do not discharge the joint constraint (3.2).

**Proposition 5.2 (counted realization and the source boundary).** The construction (5.1) has a finite exact rational implementation with all service states charged, and the analysis in Sections 2–4 introduces no new source or runtime capability.

Proof. The two-label component is a finite product with the full original $C_0$. On each actual acquired letter its projection is precisely the original update and event block. Induction over operations preserves both seeds, all paid rejections, every marker triple, write-before-latch, held records, permissions and the unique matching Stop. The same updates define each synthetic complete law.

A common denominator for $a,b,s_*$ and the fair probabilities is $30000<2^{15}$. Draw a fresh 15-bit candidate, reject values at least $30000$, and use the accepted integer's fixed threshold. The alpha thresholds for $a,b,s_*$ and $1/2$ are respectively $10000,12000,11037,15000$. Acceptance is positive, so the reusable rejection service returns almost surely and gives each exact rational probability. The acquired private updates in (5.1) are deterministic; the latch sample is source-independent. This is the finite rational sampling convention of [PAID, Proposition 11.3], instantiated for this example. Candidates, bit cursors, thresholds, program selectors, addresses, output and every service microstate belong to COMPLETE. Rejection uses no unbounded retained attempt counter. Internal microstates carry the conditional continuation of that same service program and create no additional actual source-query cut or permission. At each original returned cut the law description is the finite installed generator and current configuration, rather than a stored infinite output table.

The general theorem permits arbitrary public real stochastic entries as mathematical constants; it supplies no physical exact-real sampler. Actual Reads, installed table and program size, numerical representation, random bits, internal work, output, synthesis and physical source preparation are separate accounts. Positive arbitrarily long return histories and sampler rejection preclude a finite worst-case total time or output bound. The stationary rows, private analysis path and its moments are used only in the proof. ∎

## 6. Attribution, candidate methods and the remaining frontier

**Mathematical citation 6.1 (new content and reused tools).** The source, complete-tail radii, held-record renderer, endpoint events and coordinate identity, positive-history stationary extraction, clipping constants and original-domain product realization are supplied by [ST; CLIP; PAID; INTERIOR]. They are not new claims of this volume. The elementary product bounds (3.7)–(3.9) are used within the source-specific proof and carry no separate novelty claim.

The source-specific delta is the simultaneous response constraint (3.2) with its evaluated rational incompatibility (3.10), the regular-table gap (3.1) and the original finite-observer gap (1.6). The positive-cycle/single-mode budget results of [PH, Sections 14–20] concern deterministic modewise losses; their all-observer transfer remains conditional on the domination premise explicitly retained there. No such premise is used here. Constancy of $v$ leaves both $B$ and $A$ arbitrary and leaves the complete laws noncollapsed. The obstruction is therefore not the complete-redraw result of [PAID, Section 12], nor a coefficient change to the free motion, alpha-change or interiority statistics. It needs four successive complete marker-1 words and the common actual chain; independent scalar moment choices cannot establish it.

Positive realization theory supplies mature tools for realizing a prescribed output law, including the stable polyhedral-cone formulation reviewed in [MW, Section 2]. It does not supply the additional unweighted actual circulation and simultaneous source-specific endpoint loss bounds used here. [CK] studies comparison and approximation for a specified pair of labelled Markov-chain laws; it does not by that result provide the uniform constant-suspension separator. These are bounded correspondence statements, not claims of global literature priority. The mathematical attribution of this derivation is `repo-derived`; it has ordinary proofs and no Lean kernel verification or frozen status.

**Mathematical citation 6.2 (new public proof methods under their hypotheses).** [JM, Sections 61–64] uses one immutable ordered tree, fixed full leaf word, literal-address queries, retained four-valued cache replies and coarse action control. Its actual-cache image and full-block recombination are distinct relations. No address query or tree intervention is transported into the present Read source. The common path in (3.4) is proved from the original $B,A$ rather than assembled from independently selected residual projections.

[HIST] compares normalized full-history rows at the same observed history and controls the remaining deletion tail under its second original law. Its finite survivor comparison assumes a uniform positive entry lower bound on the second original law and an entrywise row comparison at the same history. Its rational search additionally assumes a legal prefix-free code, a depth-budget promise with effective subexponential modulus and strict budget sum below one. No such search is an observer-synthesis theorem. In the binary raw alphabet the original complete stopping code has one word at every positive length, so its uniform budget sum is $\sum_{n\ge1}2^{-n}=1$; the final survivor has source mass zero. Thus the strict budget promise cannot be invoked for that entire code. Applying finite-prefix comparison with an original-law tail does not itself evaluate the joint loss separator sought here; [PAID, Sections 5 and 9–10] already supplies the relevant stopped-law partition comparisons. No conclusion from [HIST] is assumed in (3.2).

**Corollary 6.3 (task-relative whitebox consequence and unresolved alternatives).** For a predictive model assigned the source, operation, complete-tail loss and counted finite same-update semantics of Section 1, common endpoint-optimal configuration prediction requires suspended emission heterogeneity on the designated actual held-record fibre. Define the task quality $W_{\mathrm{conf},s}=1-R_{\mathrm{conf},s}$. Every model in the constant-suspension class satisfies at least one of

$$
W_{\mathrm{conf},p}<1-\rho_p-\frac1{195200},
\qquad
W_{\mathrm{conf},\beta}<1-\rho_\beta-\frac1{195200}.
$$

If a nonendpoint is supported, the supplied positive interior tent mass of INTERIOR must hold in addition for an exact common conf/conf attainer. This statement concerns configuration semantics, not identification of an internal implementation or a classification of all trained networks by FIB windows.

Proof. Theorem 1.5 implies that at least one configuration excess exceeds $1/195200$; subtract its corresponding risk from one. Its heterogeneity conclusion applies to any exact common conf/conf attainer. Under the additional supported-nonendpoint hypothesis, apply the supplied INTERIOR theorem to the same original observer and its original history domain. Both necessities refer to that one observer; no claim of their joint sufficiency follows. ∎

The new theorem proves a positive gap on the constant-suspension structural class and hence one new necessary constraint on any unrestricted conf/conf attainer or vanishing sequence. It does not determine exact unrestricted attainment, an unattained zero infimum, a positive unrestricted infimum or any fixed-resource optimum. It does not construct an observer meeting the new constraint. Of the four phase combinations, the original-observer theorem covers conf/conf only. The published law/law, law/conf and conf/law attainments retain their supplied scopes [PAID, Definition 1.3 and the cited mixed/switch suppliers]; no new constant-suspension lower bound for those three arbitrary-original-observer classes is proved here. The regular-table theorem also bounds endpoint mean laws, but the conf-based clipping reduction is not asserted to transport an arbitrary original law/law, law/conf or conf/law model.

A concrete remaining mathematical question is whether nonconstant genuinely interior suspended emissions permit a lawful common generator meeting both endpoint calibrations and every supported interior complete-law configuration loss. When $v$ varies, $B\operatorname{diag}(v)A$ is a weighted kernel, while $BA$ is the actual kernel; (3.4) no longer reduces to a single stationary product process with one scalar $s$. A proposed construction must satisfy this weighted and unweighted relation on the same actual circulation. An obstruction must control that relation uniformly over all finite shapes. Neither question is resolved by (1.6).

## 7. References

- **ST:** [Randomized stopped-tail minimax](https://github.com/the-omega-institute/trureturing/blob/eefbcdeb4026909f0fcdfa7ad7f4bcdb402c3441/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md), Sections 1–3.
- **CLIP:** [Risk-controlled emission moment feasibility](https://github.com/the-omega-institute/trureturing/blob/eefbcdeb4026909f0fcdfa7ad7f4bcdb402c3441/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md), Sections 1–3.
- **PH:** [Phase-coherent full-tail minimax](https://github.com/the-omega-institute/trureturing/blob/eefbcdeb4026909f0fcdfa7ad7f4bcdb402c3441/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md), Sections 14–20.
- **PAID:** [Effective paid-history certificates](https://github.com/the-omega-institute/trureturing/blob/eefbcdeb4026909f0fcdfa7ad7f4bcdb402c3441/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md), Sections 2, 5, 9–15.
- **INTERIOR:** [Suspended-emission interiority](https://github.com/the-omega-institute/trureturing/blob/eefbcdeb4026909f0fcdfa7ad7f4bcdb402c3441/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SUSPENDED_EMISSION_INTERIORITY.md).
- **ALPHA:** [Acquired-alpha calibration compatibility](https://github.com/the-omega-institute/trureturing/blob/eefbcdeb4026909f0fcdfa7ad7f4bcdb402c3441/docs/develop/theory/AURIC_FIB_ATOM_ACQUIRED_ALPHA_CALIBRATION_COMPATIBILITY.md).
- **DIRECTION:** [Directional alpha calibration](https://github.com/the-omega-institute/trureturing/blob/eefbcdeb4026909f0fcdfa7ad7f4bcdb402c3441/docs/develop/theory/AURIC_FIB_ATOM_DIRECTIONAL_ALPHA_CALIBRATION.md).
- **MOTION:** [Actual-return forecast motion](https://github.com/the-omega-institute/trureturing/blob/eefbcdeb4026909f0fcdfa7ad7f4bcdb402c3441/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_RETURN_FORECAST_MOTION.md).
- **JM:** [Joint moment fibres](https://github.com/the-omega-institute/trureturing/blob/eefbcdeb4026909f0fcdfa7ad7f4bcdb402c3441/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md), Sections 61–64.
- **HIST:** [Historical survivor transport and rational search](https://github.com/the-omega-institute/trureturing/blob/eefbcdeb4026909f0fcdfa7ad7f4bcdb402c3441/Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/EffectiveRationalTransportTail.md), with its [formal source](https://github.com/the-omega-institute/trureturing/blob/eefbcdeb4026909f0fcdfa7ad7f4bcdb402c3441/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/EffectiveRationalTransportTail.lean).
- **MW:** Alex Monràs and Andreas Winter, *Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem*, [arXiv:1412.3634v1](https://arxiv.org/html/1412.3634v1), Section 2.
- **CK:** Taolue Chen and Stefan Kiefer, *On the Total Variation Distance of Labelled Markov Chains*, [arXiv:1405.2852v1](https://arxiv.org/html/1405.2852v1), DOI [10.1145/2603088.2603099](https://doi.org/10.1145/2603088.2603099).

## 追加锚（本行以下为增补区）
