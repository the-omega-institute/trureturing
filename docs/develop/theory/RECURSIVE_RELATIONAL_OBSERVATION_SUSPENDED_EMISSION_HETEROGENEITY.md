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

## 8. A quantitative modulus for variable suspended emissions

**Definition 8.1 (original oscillation and unchanged joint excess).** For an arbitrary observer of Definitions 1.1–1.3, without the constancy restriction of Definition 1.4, let $v_M(y)$ be its next synthetic alpha probability at a suspended COMPLETE configuration. On exactly the designated seed-1, marker-100 held-record fibre of (1.5), define

$$
\omega=\operatorname{osc}(M)
=\max_{y\in\mathcal Z_\beta^*(M)}v_M(y)
 -\min_{y\in\mathcal Z_\beta^*(M)}v_M(y).
\tag{8.1}
$$

The set $\mathcal Z_\beta^*(M)$ includes every configuration reached with positive probability after any positive finite actual suspended history on that fibre, including transient configurations and configurations whose emission is zero or one. It is nonempty and finite. No stationary-support restriction is made in (8.1).

Throughout this chapter the loss is the original configuration-before-TV loss, with

$$
\begin{aligned}
e=e(M)&=\max\left\{R_{\mathrm{conf},p}(M)-\frac{1116529}{22781250},
 R_{\mathrm{conf},\beta}(M)-\frac{239}{6750}\right\},\\
R_{\mathrm{conf},s}(M)&=\sup_{h\in\mathcal H_s}
 \sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu).
\end{aligned}
\tag{8.2}
$$

In particular the supremum contains all original positive finite fourth-segment histories, not only the first p cut. The installed prior is finite or countable with $\mu(1),\mu(2)>0$; additional supported depths are permitted but not required. The actual source draws the same single $K$ as in Definition 1.1. Its paid rejection histories, partial parses, arbitrary finite payload returns, both seeds, all marker records, original permissions, write-before-latch rule and matching Stop remain those of Section 1. Equation (1.3), including its zero-predicted-probability cases, is unchanged. The quantities in (8.2) are neither marginal-law risks nor actual-history averages.

**Mathematical citation 8.2 (conditional original-domain suppliers).** The conclusions below assume the suppliers declared in Mathematical citations 2.1 and 2.3: simultaneous supported-depth configuration-loss bounds on common reachable stationary analysis rows, their original-history extraction, the clipping comparison (2.2), the full complete-law endpoint radii and coordinates (2.5)–(2.8), and the full-record realization of the same-update comparison laws. These are ordinary mathematical premises from [ST, Sections 1–3], [CLIP, Theorem 3.1 and equations (3.6)–(3.10)] and [PAID, Lemmas 14.1 and 2.1.1]. Their truth is not a consequence of the finite algebra below.

More explicitly, retain the extracted acquired kernels $B:X\to Y$, $A:Y\to X$ and the probability rows

$$
\pi B=\tau,\qquad\tau A=\pi,
\tag{8.3}
$$

delete zero-row labels only in this comparison, and clip the synthetic emissions to $[a,b]=[1/3,2/5]$. Write $u_x,v_y$ for the clipped entries and $Q_x,W_y$ for their regenerated complete raw laws (2.3). For every supported depth, expected configuration losses on these same rows obey the supplied bounds. Consequently their endpoint mean laws satisfy (2.4) with

$$
\epsilon_p=\frac{61}{11}e,\qquad
\epsilon_\beta=\frac{53}{11}e.
\tag{8.4}
$$

Indeed the separate numerators in (2.2) are $41\varepsilon_p+20\varepsilon_\beta$ and $12\varepsilon_p+41\varepsilon_\beta$, and each original excess is between zero and $e$. Convexity of TV is applied only after these configuration-loss comparisons. This is the sole passage from the original configuration risk to endpoint mean-law constraints.

Every positive-row suspended label is originally reachable on the fibre in (8.1). Since clipping is monotone and 1-Lipschitz, the distinct analysis quantity

$$
t=\max_{y:\tau_y>0}v_y-\min_{y:\tau_y>0}v_y
\quad\hbox{satisfies}\quad
0\le t\le\min\{\omega,1/15\}.
\tag{8.5}
$$

Transient labels may be absent from this extracted support. They remain in (8.1), in the original history domain and in (8.2). Original zero/one emissions and possible original noncompletion mass are handled by the clipping supplier, not by an extra termination assumption on $M$.

The actual p-return matrix is $BA$, with $\pi BA=\pi$. The weighted transfer is $B\operatorname{diag}(v)A$, and the full synthetic p-survival matrix is

$$
K_{\mathrm{syn}}=\operatorname{diag}(1-u)B\operatorname{diag}(v)A
\le\frac4{15}BA
\tag{8.6}
$$

entrywise. Thus the clipped generator survives $j$ returns with probability at most $(4/15)^j$. No stationarity of $K_{\mathrm{syn}}$ or of the weighted transfer is assumed. The deterministic original event blocks and Stop are restored by each configuration's renderer $I_c$, which preserves TV. The comparison uses the same source, prior and acquired $B,A$; rows, moments and centered variables used below are analysis coordinates, not installed runtime observations.

**Theorem 8.3 (uniform quantitative suspended-emission modulus).** Under Mathematical citation 8.2, every original finite COMPLETE observer of Definitions 1.1–1.3 satisfies

$$
e(M)+\frac{\operatorname{osc}(M)}{898}>\frac1{195200}.
\tag{8.7}
$$

A stronger necessary inequality is

$$
A_\lambda e(M)+\lambda P(\operatorname{osc}(M))
 +R(\operatorname{osc}(M))\ge D_\lambda,
\tag{8.8}
$$

where

$$
\begin{aligned}
P(t)&=\frac{45211}{337500}t+\frac{283}{270}t^2+\frac2{27}t^3,\\
R(t)&=\frac{235691}{25312500}t+\frac5{54}t^2
 +\frac4{45}t^3+\frac4{81}t^4,\\
\lambda&=\frac{788005464525177451917}{16672435848499576471250},\\
A_\lambda&=\frac{326}{11}\lambda+\frac{663}{55},\\
D_\lambda&=\frac{15204298625345638971348873871931843}
 {202570095559269854125687500000000000000}.
\end{aligned}
\tag{8.9}
$$

The constants are uniform over finite carrier size, the allowed installed priors, original transient modes and original emission entries in $[0,1]$. The proof consists of the same-path comparison and rational separation below.

**Lemma 8.4 (one dependent path and its centered complete-word expansion).** Start $Y_{-1}$ with row $\tau$, and use alternately $A,B,A,B,\ldots$ to obtain

$$
Y_{-1},X_0,Y_0,X_1,Y_1,X_2,Y_2,\ldots.
$$

All $X_i$ have marginal $\pi$, and all $Y_i$ have marginal $\tau$, by (8.3). Put

$$
\begin{gathered}
L=\frac35,\quad H=\frac23,\quad
U_i=1-u(X_i)\in[L,H],\quad V_i=v(Y_i),\\
s=\mathbb E V_i\in[a,b],\quad\zeta_i=V_i-s,\quad
m=\mathbb E U_0,\quad
M_j=\mathbb E\prod_{i=0}^{j-1}U_i\ (j\ge1).
\end{gathered}
\tag{8.10}
$$

Here $V_{-1}=v(Y_{-1})$ and $\zeta_{-1}=V_{-1}-s$ have the same conventions. For $j=0,1,2,3$ exact generation on this common path gives

$$
\begin{aligned}
\overline Q(w_{j,1})
 &=\mathbb E\left[
 \left(\prod_{i=0}^{j}U_i\right)
 \left(\prod_{i=0}^{j-1}V_i\right)(1-V_j)\right],\\
\overline W(E_\beta)
 &=1-s+\mathbb E[V_{-1}U_0(1-V_0)].
\end{aligned}
\tag{8.11}
$$

The empty product for $j=0$ is one. In particular these identities do not require independent path coordinates.

Proof. Each p beta contributes $U_i$ and kernel $B$, each suspended alpha contributes $V_i$ and kernel $A$, and the final suspended beta contributes $1-V_j$. Summing the finite path weights proves the first identity for the entire complete word $(\beta\alpha)^j\beta\beta$. Starting at suspension, $E_\beta$ is the disjoint union of immediate beta and alpha-beta-beta. Its latter path has factors $V_{-1}U_0(1-V_0)$ and acquired kernels $A,B$. This proves the second identity. The continuation path after a stopping word is only an analysis extension of its finite acquired-kernel path measure. It asserts no additional actual operation after completion. ∎

The following error estimates are embedded uses of bounded-range covariance and Cauchy–Schwarz. If a real random variable lies in an interval of width $d$, its variance is at most $d^2/4$: its second moment about the interval midpoint is at most $d^2/4$, and the mean minimizes that centered second moment. Thus $\mathbb E\zeta_i=0$, $\mathbb E\zeta_i^2\le t^2/4$ and $|\zeta_i|\le t$. If $Z$ is any product of $n$ of the $U$ coordinates, then $Z\in[L^n,H^n]$ and

$$
|\mathbb E[Z\zeta_i]|
=|\operatorname{Cov}(Z,V_i)|
\le\frac{H^n-L^n}{4}t.
\tag{8.12}
$$

For any $k\ge2$, bounding $k-2$ factors by $t$ and applying Cauchy–Schwarz to two remaining factors gives

$$
\mathbb E|\zeta_{i_1}\cdots\zeta_{i_k}|\le\frac{t^k}{4},
\qquad
\left|\mathbb E[Z\zeta_{i_1}\cdots\zeta_{i_k}]\right|
\le\frac{H^n}{4}t^k.
\tag{8.13}
$$

Dependence, repeated labels and periodic paths are allowed in these estimates.

Expand every $V_i=s+\zeta_i$ in (8.11). The sums of absolute coefficients at each positive degree in the centered variables, before multiplication by $Z$, have the following bounds on $s\in[1/3,2/5]$:

$$
\begin{array}{c|cccc}
\text{factor}&\text{degree 1}&\text{degree 2}&\text{degree 3}&\text{degree 4}\\ \hline
V_{-1}(1-V_0)&1&1&0&0\\
1-V_0&1&0&0&0\\
V_0(1-V_1)&1&1&0&0\\
V_0V_1(1-V_2)&16/25&7/5&1&0\\
V_0V_1V_2(1-V_3)&44/125&6/5&9/5&1
\end{array}
\tag{8.14}
$$

For completeness, for the factor with $j$ initial $V$ entries, the degree-$k$ coefficient sum for $1\le k\le j$ is

$$
\binom jk s^{j-k}(1-s)+\binom j{k-1}s^{j-k+1},
$$

and the degree-$j+1$ sum is one. For $j=2$ these sums are $2s-s^2,1+s,1$; for $j=3$ they are $3s^2-2s^3,3s,1+2s,1$. Their maxima on the stated interval give (8.14). The first row follows directly from the coefficients $1-s,-s,-1$.

Combining (8.12)–(8.14) gives errors $\eta_\beta,\eta_0,\ldots,\eta_3$ with

$$
\begin{aligned}
\overline W(E_\beta)&=1-s+s(1-s)m+\eta_\beta,
 &|\eta_\beta|&\le b(t),\\
\overline Q(w_{j,1})&=(1-s)s^jM_{j+1}+\eta_j,
 &|\eta_j|&\le k_j(t),
\end{aligned}
\tag{8.15}
$$

where every coefficient is explicit:

$$
\begin{aligned}
b(t)&=\frac{t}{60}+\frac{t^2}{6},\\
k_0(t)&=\frac{t}{60},\\
k_1(t)&=\frac{19t}{900}+\frac{t^2}{9},\\
k_2(t)&=\frac{1084t}{84375}+\frac{14t^2}{135}+\frac{2t^3}{27},\\
k_3(t)&=\frac{37829t}{6328125}+\frac{8t^2}{135}
 +\frac{4t^3}{45}+\frac{4t^4}{81}.
\end{aligned}
\tag{8.16}
$$

For example, the linear coefficient of $k_j$ is $(H^{j+1}-L^{j+1})/4$ times the degree-one entry in (8.14); all higher coefficients are $H^{j+1}/4$ times their entries. The first row uses $n=1$, giving $(H-L)t/4+Ht^2/4=b(t)$. This accounts for every term without replacing a dependent expectation by a product of expectations.

**Lemma 8.5 (robust simultaneous response constraints).** The same scalar $s$ in (8.10) satisfies

$$
\begin{aligned}
C_p-F(s)&\le\epsilon_p+5\epsilon_\beta+P(t),\\
G(s)-q_*&\le2\epsilon_p+\epsilon_\beta/5+R(t),
\end{aligned}
\tag{8.17}
$$

with $F,G$ exactly as in (3.3), $C_p=11758471/22781250$, $q_*=1944/390625$ and the polynomials in (8.9).

Proof. The common stationary $U$ marginals suffice for the product inequalities (3.7)–(3.9):

$$
\begin{aligned}
M_2&\le(L+H)m-LH,\\
M_3&\le(L^2+LH+H^2)m-LH(L+H),\\
M_4&\ge LH^2(4m-L-2H).
\end{aligned}
\tag{8.18}
$$

Indeed $xy\le(x^2+y^2)/2$ and the three-variable identity preceding (3.7) first give $M_2\le\mathbb E U_0^2$ and $M_3\le\mathbb E U_0^3$; the interval chords then give the first two bounds. The four-product inequality (3.8) is multi-affine in its four arguments. At vertices with respectively $0,1,2,3,4$ arguments equal to $H$, its exact differences are $29/5625,2/1125,0,0,4/2025$. Multilinear interpolation makes the difference nonnegative throughout the box. Taking expectations with the common marginal mean gives the last bound. No equality case or independent attainability of these estimates is used.

Put $c=1489/6750$ and $d=\overline W(E_\beta)-C_\beta$. The supplied endpoint event constraint (2.6) and (8.15) give

$$
|d|\le\epsilon_\beta,\qquad
s(1-s)m=s-c+d-\eta_\beta.
\tag{8.19}
$$

Using the first three word identities in (8.15) and the first two bounds of (8.18),

$$
\begin{aligned}
\overline Q(E_p)
&\le(1-s)(m+sM_2+s^2M_3)+k_0+k_1+k_2\\
&\le F(s)+h(s)(d-\eta_\beta)+k_0+k_1+k_2,\\
h(s)&=\frac1s+\frac{19}{15}+\frac{271}{225}s.
\end{aligned}
\tag{8.20}
$$

Here and below the $k_j$ are evaluated at $t$. Substitution of (8.19) gives the equality defining $F$ in (3.3), since $L+H=19/15$, $LH=2/5$ and $L^2+LH+H^2=271/225$. On the interval, $0<h(s)\le3+19/15+542/1125<5$. Together with $\overline Q(E_p)\ge C_p-\epsilon_p$, this proves the first inequality of (8.17) with error

$$
k_0+k_1+k_2+5b
=\frac{45211}{337500}t+\frac{283}{270}t^2+\frac2{27}t^3=P(t).
\tag{8.21}
$$

For the fourth word, (8.15), (8.18) and (8.19) instead give

$$
\begin{aligned}
\overline Q(w_{3,1})
&\ge(1-s)s^3LH^2(4m-L-2H)-k_3\\
&=G(s)+g(s)(d-\eta_\beta)-k_3,\\
g(s)&=4LH^2s^2\le\frac{64}{375}<\frac15.
\end{aligned}
\tag{8.22}
$$

The equality uses $LH^2=4/15$, $L+2H=29/15$ and $4-L-2H=31/15$, giving precisely $G$ in (3.3). Since $g(s)>0$, combine this with the complete-coordinate upper bound (2.8) to obtain the second inequality of (8.17). Its error is

$$
k_3+b/5
=\left(\frac{37829}{6328125}+\frac1{300}\right)t
 +\frac5{54}t^2+\frac4{45}t^3+\frac4{81}t^4=R(t).
\tag{8.23}
$$

Both inequalities concern the one clipped generator, its two complete mean laws, one actual circulation and one common mean $m$. ∎

**Lemma 8.6 (a convex tangent with positive rational separation).** Set $s_*=3679/10000$ and $\lambda=G'(s_*)/F'(s_*)$. This is the positive rational in (8.9), and

$$
\lambda(C_p-F(s))+G(s)-q_*\ge D_\lambda
\quad(a\le s\le b).
\tag{8.24}
$$

Proof. Differentiating the explicit functions (3.3) gives

$$
\begin{aligned}
F'(s)&=\frac c{s^2}+\frac{13}{15}-\frac{271}{225}c
 +\frac{494}{225}s+\frac{38}{25}s^2>0,\\
G'(s)&=\frac4{15}s\left(\frac{31}{5}s+\frac{116}{15}s^2-8c\right)>0,\\
F''(s)&=-\frac{2c}{s^3}+\frac{494}{225}+\frac{76}{25}s,\\
G''(s)&=\frac4{15}\left(\frac{62}{5}s+\frac{116}{5}s^2-8c\right).
\end{aligned}
\tag{8.25}
$$

The positive first derivatives also follow from the bounds in Section 3. Both second derivatives are increasing on this positive interval. Their relevant endpoint evaluations are

$$
F''(2/5)=-\frac{94013}{27000}<0,\qquad
G''(1/3)=\frac{66776}{50625}>0.
\tag{8.26}
$$

Therefore $H_\lambda(s)=\lambda(C_p-F(s))+G(s)-q_*$ is strictly convex. Its derivative vanishes at $s_*$ by the definition of $\lambda$, and $s_*\in(a,b)$. Hence its minimum is $H_\lambda(s_*)=D_\lambda$, yielding (8.24) and the exact value in (8.9).

The following rational comparisons give an explicit positive margin:

$$
\begin{gathered}
\frac{189}{4000}<\lambda<\frac{5908}{125000},\\
C_p-F(s_*)-\frac1{4000}
=\frac{12788985483823}{33524887500000000000}>0,\\
G(s_*)-q_*-\frac1{16000}-\frac7{10000000}
=\frac{116200318741}{5062500000000000000}>0.
\end{gathered}
\tag{8.27}
$$

The latter two identities refine the evaluations (3.10). Multiplication by the positive $\lambda$ gives

$$
D_\lambda>
\frac{189}{4000}\frac1{4000}+\frac1{16000}+\frac7{10000000}
=\frac{6001}{80000000}>\frac3{40000}.
\tag{8.28}
$$

This is a separation of simultaneous constraints at one tangent; it does not optimize either phase independently. ∎

**Proof of Theorem 8.3.** Multiply the first inequality of (8.17) by $\lambda$ and add the second. Equations (8.4) and (8.24) imply

$$
\begin{aligned}
D_\lambda
&\le(\lambda+2)\epsilon_p+(5\lambda+1/5)\epsilon_\beta
 +\lambda P(t)+R(t)\\
&=\left(\frac{326}{11}\lambda+\frac{663}{55}\right)e
 +\lambda P(t)+R(t).
\end{aligned}
\tag{8.29}
$$

All coefficients of $P,R$ are positive. Thus $t\le\omega$ proves (8.8).

To deduce the strict linear modulus, suppose instead that $e+\omega/898\le T$, where $T=1/195200$. The supplied nonnegative excesses imply

$$
0\le\omega\le898T=\frac{449}{97600}<\frac1{217},\qquad
\frac1{217}-\frac{449}{97600}=\frac{167}{21179200}>0.
\tag{8.30}
$$

Because $P(t)/t$ and $R(t)/t$ have nonnegative coefficients and increase for $t\ge0$, their exact endpoint margins give

$$
\begin{aligned}
\frac{347}{2500}-217P(1/217)&=\frac{38669}{3973134375}>0,\\
\frac{487}{50000}-217R(1/217)&=\frac{169810643}{1034604191250000}>0.
\end{aligned}
\tag{8.31}
$$

Consequently $P(\omega)\le(347/2500)\omega$ and $R(\omega)\le(487/50000)\omega$, including $\omega=0$. Using the upper bound for $\lambda$ in (8.27), define

$$
\begin{aligned}
A^+&=\frac{326}{11}\frac{5908}{125000}+\frac{663}{55}
 =\frac{2312626}{171875},\\
K^+&=\frac{5908}{125000}\frac{347}{2500}+\frac{487}{50000}
 =\frac{2546913}{156250000}.
\end{aligned}
\tag{8.32}
$$

The two budget margins are exactly

$$
\begin{aligned}
\frac3{40000}-\frac{A^+}{195200}&=\frac{25453}{4193750000}>0,\\
\frac3{40000}-\frac{898K^+}{195200}&=\frac{186063}{15250000000000}>0.
\end{aligned}
\tag{8.33}
$$

Finally, (8.8) and the supposed linear bound yield

$$
\begin{aligned}
D_\lambda
&\le A_\lambda e+\lambda P(\omega)+R(\omega)\\
&\le A^+e+K^+\omega\\
&\le\max\{A^+,898K^+\}(e+\omega/898)\\
&\le\max\{A^+,898K^+\}T
 <\frac3{40000}<D_\lambda,
\end{aligned}
$$

a contradiction. This proves (8.7). The only use of mean-law bounds was downstream of (8.4); no mean/configuration risk identification is needed. ∎

**Corollary 8.7 (strict baseline-attainment threshold and limiting necessity).** If an original observer simultaneously attains the two declared baseline radii, meaning precisely

$$
R_{\mathrm{conf},p}=\rho_p,\qquad
R_{\mathrm{conf},\beta}=\rho_\beta,
\quad\hbox{equivalently }e=0,
$$

then

$$
\operatorname{osc}(M)>\frac{449}{97600}.
\tag{8.34}
$$

More generally, for $e<T$, one has $\operatorname{osc}(M)>898(T-e)$. Let $t_0$ be the unique positive root of

$$
\lambda P(t_0)+R(t_0)=D_\lambda.
\tag{8.35}
$$

Then $e=0$ implies $\operatorname{osc}(M)\ge t_0$, and every sequence of original observers with $e(M_n)\to0$ satisfies

$$
\liminf_{n\to\infty}\operatorname{osc}(M_n)\ge t_0.
\tag{8.36}
$$

Proof. Equation (8.34) is the strict specialization of (8.7), since $898/195200=449/97600$. The polynomial $J(t)=\lambda P(t)+R(t)$ is continuous, starts at zero, is strictly increasing on $[0,\infty)$ and tends to infinity. This proves uniqueness and positivity in (8.35). Equation (8.8) gives $J(\operatorname{osc}(M))\ge D_\lambda-A_\lambda e(M)$. For $e=0$, monotonicity gives the non-strict root bound. For the sequence, oscillations lie in $[0,1]$; a subsequence converging to their liminf and continuity give $J(\liminf\operatorname{osc}(M_n))\ge D_\lambda$. This proves (8.36). Neither root equality nor the existence of the sequence is asserted. ∎

Here simultaneous baseline attainment is a specified objective. An unknown unrestricted optimizer might have $e>0$; calling it an optimum does not license the $e=0$ specialization.

**Proposition 8.8 (stopped-law coupling comparison).** Under the same suppliers, a second, weaker quantitative consequence is

$$
e(M)+\frac{15}{122}\operatorname{osc}(M)>\frac1{195200}.
\tag{8.37}
$$

Proof. In the clipped table set $s_0=(\max v+\min v)/2$ and replace only $v$ by $s_0$, retaining $u,B,A,\pi,\tau$. This is one regular constant-emission comparison with its own charged realization. Its suspended Bernoulli perturbation is at most $t/2$. Couple emissions from identical labels maximally, and after matched letters use the same acquired-update randomness. At p emissions already agree. From suspension the probability of reaching the $j$th further suspended visit without completion or an earlier discrepancy is at most $(4/15)^j$. The coupling inequality and the geometric sum therefore give, for complete stopped laws,

$$
\sup_y\operatorname{TV}(W_y,W_y^{s_0})\le\frac{t/2}{1-4/15}=\frac{15t}{22},
\qquad
\sup_x\operatorname{TV}(Q_x,Q_x^{s_0})\le\frac23\frac{15t}{22}=\frac{5t}{11}.
\tag{8.38}
$$

Both regular generators terminate almost surely; their legal infinite outcomes have zero mass. Matching letters and labels match every rendered deterministic event and Stop. These bounds thus concern full laws rather than terminal projections. The triangle inequality before configuration averaging, followed by convexity, gives the endpoint mean-law bounds of Theorem 3.1 for this one constant table, with excess bounds $\epsilon_p+5t/11$ and $\epsilon_\beta+15t/22$. Hence

$$
\frac1{35200}<\max\{\epsilon_p+5t/11,\epsilon_\beta+15t/22\}
\le\frac{61}{11}e+\frac{15}{22}t.
$$

Multiply by $11/61$, use $t\le\omega$ and $11/(61\cdot35200)=1/195200$ to prove (8.37). Only synthetic geometric survival is used, not actual-chain convergence or mixing. ∎

**Mathematical citation 8.9 (proof suppliers and attribution).** The bounded-range covariance estimate in (8.12) is the classical Grüss bound, proved here from a variance bound and Cauchy–Schwarz; (8.13), interval chords, multi-affine interpolation and convex tangent separation are likewise embedded elementary proof steps. Sequential coupling, the coupling inequality and conditional-product TV perturbation are mature suppliers for (8.38). They are not standalone discoveries of this chapter.

For the classical arbitrary-dependence covariance bound, see Martín Egozcue, Luis Fuentes García, Wing-Keung Wong and Ričardas Zitikis, *Grüss-Type Bounds for the Covariance of Transformed Random Variables*, Journal of Inequalities and Applications, volume 2010, article 619423, [DOI 10.1155/2010/619423](https://doi.org/10.1155/2010/619423), Section 2. Only the bounded-range inequality proved in (8.12) is used, not its dependence-sensitive refinements.

For a public precise reference for conditional-product coupling, see Alessandro Abate, Frank Redig and Ilya Tkachev, *On the effect of perturbation of conditional probabilities in total variation*, [arXiv:1311.3066v1](https://arxiv.org/abs/1311.3066v1), Theorems 1–2, Lemma 2 and Section 3.2. Its total-variation norm is twice the event-supremum TV used here. Finite configuration spaces and countable stopped-word carriers meet its measurable-space conditions. Its finite-horizon product estimates require the additional geometric survival argument above to control entire stopped laws uniformly. [CK] supplies context for distances between specified labelled-chain output laws; it does not supply the original-history extraction or simultaneous configuration-loss comparison.

The mathematical contribution here is the source-specific uniform variable-emission modulus (8.7)–(8.9), obtained through the dependent centered-response comparison (8.11)–(8.23). Its attribution is repo-derived ordinary mathematics conditional on Mathematical citation 8.2. The existing source-specific products (3.7)–(3.9), complete-tail events and radii, clipping constants and full-record realization are reused at their declared scopes. No external novelty, priority or optimality of the coefficient $1/898$ is asserted.

**Open mathematical boundary 8.10 (necessity, realization and optimization).** These inequalities are necessary conditions for the original conf/conf objective. They neither construct simultaneous baseline attainment nor establish that a family with $e\to0$ exists. The unrestricted infimum, its sign, attainment, fixed-resource optimization and attainability of the polynomial root remain undetermined by this chapter. Satisfying the inequalities is not sufficient: one same generator must still satisfy exact individual generation, the common actual circulation and all supported-depth full configuration-loss constraints.

No comparison here preserves a fixed COMPLETE allocation or a hard bound on either marginalized defect $\Delta_4,\Delta_{\mathrm{all}}$. It introduces no law/law or mixed-risk transfer, physical-memory bit bound, exact-real physical sampler, new actual source access or runtime access to an analysis posterior, row or path coordinate. The comparison's full-record realization is conditional on the stated supplier; its resource costs belong to that comparison. All original transient histories, zero/one emissions, held records and Stop obligations remain within the original hypotheses. No irreducibility, aperiodicity, independent path coordinates, mixing, or separate stationary law for $B\operatorname{diag}(v)A$ or $K_{\mathrm{syn}}$ is available or required.

## 追加锚（本行以下为增补区）
