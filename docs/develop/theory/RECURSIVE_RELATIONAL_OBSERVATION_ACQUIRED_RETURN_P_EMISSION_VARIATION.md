# Common complete-tail calibration requires p-emission variation on an acquired return

With positive endpoint masses and a supported nonendpoint depth, common endpoint-optimal complete-tail configuration prediction requires a change in the immediate p alpha emission on some actual noncompleting return of the designated fibre. Theorem 1.5 evaluates a uniform gap for the conserved-emission class, while allowing arbitrary nonconstant suspended emissions. The unrestricted attainment and infimum alternatives remain unresolved.

**Mathematical citation 1 (status and attribution).** All proofs below are ordinary mathematics. No new kernel verification or frozen status is asserted. The source, separate minimax radii, stationary extraction, clipping, and the supported-interior word are supplied results with their stated hypotheses. The new source-specific assertion is Theorem 3.1 and its original-observer consequence, Theorem 1.5. Its attribution is `repo-derived`; no global literature-priority claim is made.

## 1. Source, observer and the new excluded class

**Definition 1.1 (unchanged source and histories).** Put $m=2,d=1,\ell=2,n=4$, $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$, and

$$
r_k=F_{k+1}/F_{k+3},\qquad a=r_1=1/3,\qquad b=r_2=2/5.
$$

Install one finite or countable prior $\mu$ on positive integers, with $\mu(1),\mu(2)>0$. Draw one $K$ before the first actual Read. Conditional on that same $K=k$, every seed and payload letter is independent, with alpha probability $r_k$. For $k\ge3$, $r_k\in[3/8,5/13]$.

The paid seed parser rejects equal pairs, accepts alpha-beta as seed 0 and beta-alpha as seed 1. Every payload starts at p: alpha completes marker 0 and beta suspends; at suspension, alpha returns to p and beta completes marker 1. Keep the complete original finite control $C_0$, parser, selectors, bare fields, four-marker tree, held $B,Q^+,Z$ records, write and latch flags, permissions, completion and Stop delivery. The third record write precedes its latch. Fourth completion enters its matching pendingStop; its unique original Stop enters deliveredStop. Neither terminal permits Read.

On all sixteen completed marker words and their prefixes, let $t$ be the old completed-marker count and $j$ the old one-count. A completed marker $e$ recognizes the first zero as event $a$ ($e=0,t-j=0$), the second zero as $c$ ($e=0,t-j=1$), the first one as $b$ ($e=1,j=0$), and the second one as $d$ ($e=1,j=1$). For old $t<3$, append a recognized event to each original relation scope $S_1^+=\{a,c,d\}$ and $S_2^+=\{b,c\}$ containing it. Unmatched ordinal events, rejected pairs, returns, partial parses and completions with old $t\ge3$ hold these relation fields. Write $Z=e$ only at the first marker. At old $t=2$, complete the third record update before latching the original bare snapshot $B$; thereafter the held $B,Q^+,Z$ fields remain while the fourth segment and Stop continue. This is the full-tree writer supplied in [ALPHA, Section 2], retaining the original bare fields and selectors as part of $C_0$.

Both seeds, all marker triples, every positive finite paid rejection history and every positive finite payload-return history stay in the domain. There is no source reset, fresh depth, future-event conditioning, new observation or controller port. $\mathcal H_p,\mathcal H_\beta$ are all positive finite fourth-segment p and suspended histories after the third latch, including arbitrarily many returns. $\mathcal H_3$ is only the first p cut and is not substituted for $\mathcal H_p$. These are the contracts of [ST, Sections 1–3; CLIP, Section 1; PAID, Section 1].

**Definition 1.2 (complete tails and exact individual generation).** For $j\ge0$ put

$$
w_{j,0}=(\beta\alpha)^j\alpha,\qquad
w_{j,1}=(\beta\alpha)^j\beta\beta,\qquad h_r=r(1-r).
$$

The p carrier contains these finite words and its infinite noncompletion word. The suspended carrier contains beta, $\alpha w_{j,c}$ and its infinite noncompletion word. Fixed-depth masses are

$$
P_{p,r}(w_{j,0})=rh_r^j,\qquad
P_{p,r}(w_{j,1})=(1-r)^2h_r^j,
$$

$$
P_{\beta,r}(\beta)=1-r,\quad
P_{\beta,r}(\alpha w_{j,0})=r^2h_r^j,\quad
P_{\beta,r}(\alpha w_{j,1})=r(1-r)^2h_r^j.
\tag{1.1}
$$

The infinite masses are zero. The current-record renderer $I_c$ retains every future Read and inserts its original event blocks, records, permissions, completion and Stop. Reading the letters back is its inverse; it preserves TV and commutes with removing the next original operation and its block [ST, Section 2.1]. The already acquired suspended beta is not a future Read.

At a positive actual history $h$, with all paid letters and partial parses counted,

$$
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
 {\sum_t\mu(t)r_t^{A(h)}(1-r_t)^{B(h)}},\qquad
T_h^\mu=(I_{C_0(h)})_*\sum_k\nu_h(k)P_{s,r_k}.
\tag{1.2}
$$

The denominator is positive. These counts and posterior rows are analysis objects, not runtime inputs.

An observer has one fixed finite COMPLETE configuration carrier, source-independent initialization and fixed time-homogeneous source-independent acquired-letter stochastic updates. COMPLETE counts $C_0$, private labels, program and tables, numerical representation, selectors, workspace, addresses, output indices and all persistent randomness. Runtime reads its actual finite configuration. There is no uncounted tape, clock, archive, advice, correlated source seed, continuous hidden register or readable probability row.

From each configuration $z$, synthetic emissions and those same acquired-letter updates generate its complete decoded law $D_z$. For a legal operation $o$ and residual event $E$,

$$
D_z(oE)=q_z(o)\sum_{z'}P_o(z,z')D_{z'}(E).
\tag{1.3}
$$

The cylinder includes the original event block. This equality remains binding when $q_z(o)=0$; its actual update still exists. Synthesis makes no source call. A finite installed-generator description and current configuration index describe the law; an infinite output table or exact-real oracle is not supplied.

**Definition 1.3 (risks and marginalized defect).** For the actual conditional configuration row $\rho_h$, put $\overline D_h=\sum_z\rho_h(z)D_z$ and

$$
e_{\rm law}(h)=\operatorname{TV}(\overline D_h,T_h^\mu),\qquad
e_{\rm conf}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu),
$$

$$
R_{j,s}=\sup_{h\in\mathcal H_s}e_j(h),\quad
\rho_p=\frac{1116529}{22781250},\quad
\rho_\beta=\frac{239}{6750},\quad
\varepsilon_s=R_{{\rm conf},s}-\rho_s\ge0,\quad
e=\max(\varepsilon_p,\varepsilon_\beta).
\tag{1.4}
$$

TV is the event-supremum convention, or half $\ell^1$ on these countable carriers. The radii and their finite positive-history lower witnesses are supplied by [ST; CLIP]. Terminal projection radii $13/266,9/266$ are different quantities. Actual-history-average error is a third risk and is not used here.

At a positive actual history, let $q_h(o)=\sum_z\rho_h(z)q_z(o)$. If $q_h(o)>0$, let $\operatorname{res}_o\overline D_h$ condition on $o$ and delete it and its event block; set

$$
\delta(h,o)=\operatorname{TV}(\operatorname{res}_o\overline D_h,\overline D_{ho}).
$$

When $q_h(o)=0$, set $\delta(h,o)=0$ without creating a conditional law. The actual successor and its risk remain in the domain. $\Delta_4$ and $\Delta_{\rm all}$ take the fourth-segment and full original-operation suprema; pendingStop has zero defect and deliveredStop has empty supremum zero. Only this marginalized conditioning/update coherence is relaxed; (1.3) is exact. No hard defect budget is assumed.

The comparison tuple $(R_{{\rm law},p},R_{{\rm conf},p},R_{{\rm law},\beta},R_{{\rm conf},\beta},\Delta_4,\Delta_{\rm all})$ belongs to one observer, one installed source and all its original histories. Separate attainable coordinates are not identified with joint attainment.

**Definition 1.4 (return-conserved p emission).** Use the original seed-1, marker-100 held-record fibre reached by

$$
S=\beta\alpha\mid\beta\beta\alpha\alpha.
\tag{1.5}
$$

Let $u_x$ be the next synthetic alpha probability at a reachable p configuration $x$ on that fibre. Require

$$
u_{x'}=u_x
\quad\text{whenever the actual noncompleting return }\beta\alpha
\text{ can take }x\text{ to }x'\text{ with positive probability}.
\tag{1.6}
$$

Reachability ranges over every positive finite history on the fibre. This is conservation of one immediate p emission on the actual return, not conservation of complete forecasts. Suspended emissions may be nonconstant and strictly interior; both interfaces and all other fibres remain arbitrary. Zero predicted probabilities do not remove any actual edge from (1.6). Original transient configurations remain in the history domain.

**Theorem 1.5 (new original-observer class gap).** Suppose also that $\mu(k)>0$ for at least one $k\ge3$. Every observer of Definitions 1.1–1.4 satisfies

$$
e(M)>\frac{\eta}{2300000},\qquad
\eta=\frac{14219478376}{318644812890625}>0.
\tag{1.7}
$$

The infimum in this entire class is at least $\eta/2300000$. An exact common conf/conf attainer for such a prior must change its immediate p alpha emission on some positive actual return on the designated fibre. Any sequence with both configuration excesses tending to zero eventually violates (1.6).

This is uniform in all finite COMPLETE carriers, arbitrary stochastic entries and the allowed countable priors. It excludes a class with genuinely nonconstant suspended emissions. It asserts no unrestricted positive gap, exact attainer, vanishing family or fixed-resource optimum. With only the two endpoint depths supported, native endpoint tags are lawful exact attainers satisfying (1.6); the supported-nonendpoint assumption is essential to this consequence.

## 2. Supplied source reduction and endpoint slack

**Mathematical citation 2.1 (one common acquired circulation).** [PAID, Lemma 14.1] extracts from each original observer finite p and suspended carriers $X,Y$, their actual noncompleting kernels $B:X\to Y$, $A:Y\to X$, and probability rows $\pi,\tau$ with

$$
\pi B=\tau,\qquad \tau A=\pi.
\tag{2.1}
$$

Every positive-row label is an original reachable configuration on (1.5), with its own complete decoder pulled back through its own $I_c$. For every supported depth, the configuration losses on these same rows are bounded by the original phase suprema. Paid-history limits and Cesaro averaging produce analysis rows, not runtime inputs. Their countable-prior argument uses a summable dominating likelihood-ratio sequence. The original process need not be stationary or irreducible. Transient labels can disappear from the extracted support without being removed from the original domain.

Delete zero-row labels; (2.1) excludes transitions into them from positive-row labels. Clip both emission vectors to $[a,b]$, retain $B,A,\pi,\tau$ and regenerate complete laws. The supplied same-update coupling [CLIP, Theorem 3.1; SEH, Citation 2.1] gives

$$
\widehat\varepsilon_p\le(41\varepsilon_p+20\varepsilon_\beta)/11,
\qquad
\widehat\varepsilon_\beta\le(12\varepsilon_p+41\varepsilon_\beta)/11,
\qquad \widehat e\le(61/11)e(M).
\tag{2.2}
$$

For every supported depth the clipped common rows have the corresponding configuration-loss bounds. This permits original zero/unit emissions and noncompletion mass, but does not preserve a resource budget or hard defect constraint. Clipping preserves (1.6), because equal emissions remain equal after clipping. It makes no new source observation.

**Definition 2.2 (regular stationary same-update table).** A regular table has (2.1), $u_x,v_y\in[a,b]$ and complete raw laws

$$
Q_x=u_x\delta_\alpha+(1-u_x)\beta\sum_yB_{xy}W_y,
\qquad
W_y=(1-v_y)\delta_\beta+v_y\alpha\sum_xA_{yx}Q_x.
\tag{2.3}
$$

Every synthetic return has probability at most $\lambda=4/15$, so these laws normalize with infinite outcomes retained at mass zero. This finite table has the supplied original-domain product realization: source-independent latch initialization, original controls and records on every fibre, $B$ after actual p-beta, $A$ after actual suspended-alpha, and the original completion/Stop rules [PAID, Lemma 2.1.1].

Assume the same rows satisfy, for each supported depth,

$$
\sum_x\pi_x\operatorname{TV}(Q_x,P_{p,r_k})\le\rho_p+\epsilon_p,
\qquad
\sum_y\tau_y\operatorname{TV}(W_y,P_{\beta,r_k})\le\rho_\beta+\epsilon_\beta.
\tag{2.4}
$$

Write $\epsilon=\max(\epsilon_p,\epsilon_\beta)$, with both slacks nonnegative. Return conservation on this table is $u_{x'}=u_x$ on positive $BA$ edges. On positive stationary support it is equivalently $(BA)u=u$: stationarity gives

$$
\sum_{x,x'}\pi_x(BA)_{xx'}(u_x-u_{x'})^2
=2\pi u^2-2\sum_x\pi_xu_x((BA)u)_x.
$$

If $(BA)u=u$, this vanishes, and each positive summand vanishes. This elementary stationary identity is used only to identify the class.

**Mathematical citation 2.3 (endpoint consequences).** Put

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\},
$$

$$
C_p=\frac{11758471}{22781250},\qquad
C_\beta=\frac{5261}{6750},\qquad
d_p=2\rho_p,\quad d_\beta=2\rho_\beta.
$$

The supplied endpoint events realize their full TV differences, so (2.4) implies

$$
|\pi Q(E_p)-C_p|\le\epsilon_p,\qquad
|\tau W(E_\beta)-C_\beta|\le\epsilon_\beta.
\tag{2.5}
$$

The supplied coordinate triangle identity gives

$$
\sum_x\pi_x\sum_w\operatorname{dist}
\bigl(Q_x(w),[P_{p,a}(w)\wedge P_{p,b}(w),
               P_{p,a}(w)\vee P_{p,b}(w)]\bigr)
\le2\epsilon_p.
\tag{2.6}
$$

It includes the infinite outcome. In particular the upper endpoint bound for $w_{2,1}$ is $T_a=16/729$, the lower bound for $w_{1,1}$ is $F_b=54/625$, and the upper bound for $w_{3,1}$ is $q_*=1944/390625$ [ST; CLIP; INTERIOR; SEH]. These are consequences of configuration-before-TV risk, not pointwise minimax assumptions.

## 3. A compatibility relation for nonconstant suspended emissions

Set

$$
\chi=\frac{d_p}{d_\beta}=\frac{1116529}{806625},\qquad
\zeta_0=\frac{412}{729}-\chi\frac{22}{27}
        =-\frac{151298}{268875}.
\tag{3.1}
$$

The same intercept is obtained from the other endpoint, and $C_p-\chi C_\beta-\zeta_0=0$.

**Theorem 3.1 (evaluated weighted-return compatibility).** Every regular stationary return-conserved table satisfies

$$
\begin{aligned}
\pi Q(E_p)-\chi\tau W(E_\beta)-\zeta_0
\le{}&106\sum_x\pi_x(b-u_x)\bigl(Q_x(w_{2,1})-T_a\bigr)\\
&+365\sum_x\pi_x(u_x-a)\bigl(Q_x(w_{3,1})-q_*\bigr)\\
&-\frac1{10}\sum_x\pi_x(u_x-a)(b-u_x).
\end{aligned}
\tag{3.2}
$$

Here $v$ is arbitrary in $[a,b]^Y$. In particular (2.4) implies

$$
\pi[(u-a)(b-u)]\le520\epsilon.
\tag{3.3}
$$

Proof. Partition the positive p support by its emission value $c$. If $B_{xy}>0$ and $A_{yx'}>0$, return conservation gives $u_{x'}=u_x$. Every positive-row suspended label therefore has all its incoming and outgoing p labels in the same class. Both kernels preserve these classes; their p and suspended row masses agree. Condition the rows on one class and write $U=1-c$.

Let $Y_0,Y_1,\ldots$ be the stationary analysis chain with conditional row $\tau$ and actual unweighted kernel $AB$. Write $V_i=v_{Y_i}$ and

$$
N_j=\mathbb E\prod_{i=0}^{j-1}V_i,\qquad N_0=1.
$$

Expanding (2.3), on this same acquired circulation, gives

$$
\overline Q_c(w_{j,0})=cU^jN_j,\qquad
\overline Q_c(w_{j,1})=U^{j+1}(N_j-N_{j+1}),
\tag{3.4}
$$

$$
\overline W_c(E_\beta)=1-cN_1-UN_2.
\tag{3.5}
$$

Indeed a synthetic return uses $UB\operatorname{diag}(v)A$, whereas the stationary analysis uses $AB$ at suspension and $BA$ at p. No weighted return is replaced by a normalized actual kernel. The index $i$ is an analysis index, not a runtime clock.

Put

$$
P_c=U(1-N_1)+U^2(N_1-N_2)+U^3(N_2-N_3),
\quad H_c=1-cN_1-UN_2,
$$

$$
T_c=U^3(N_2-N_3),\qquad Z_c=U^4(N_3-N_4).
$$

We prove the following joint bound for every such stationary process:

$$
P_c-\chi H_c-\zeta_0
\le106(b-c)(T_c-T_a)+365(c-a)(Z_c-q_*)
   -\frac{(c-a)(b-c)}{10}.
\tag{3.6}
$$

Conditionally on the stationary $Y$ path, independently round each $V_i$ to $a$ or $b$, with probability $(V_i-a)/(b-a)$ of $b$. Each conditional rounded mean is $V_i$. Products at distinct time positions therefore retain every $N_j$, $j\le4$. The rounded binary process is stationary. This is a proof coupling of finite moments, not a change to any decoder, configuration risk or runtime operation.

Its four-bit probabilities form a nonnegative unit circulation on the binary overlap graph: vertices are triples, and $z_0z_1z_2z_3$ is the edge from $z_0z_1z_2$ to $z_1z_2z_3$. Prefix and suffix triple masses agree by stationarity. Any finite nonnegative circulation decomposes into directed simple cycles: follow positive edges until a vertex repeats, subtract the smallest edge mass on the resulting cycle, and repeat. Balance survives and at least one positive edge disappears at each subtraction. Dividing each cycle's total edge mass by the original unit mass gives convex weights summing to one. Thus it suffices to prove (3.6) on every simple cycle of this eight-vertex, sixteen-edge graph.

Here is a complete exact certificate. Write $L=3/5$, $H=2/3$, $U(t)=L+t/15$, $0\le t\le1$. For a cyclic binary word $s$ of length $\ell$, put $v_i=a$ for bit zero and $b$ for bit one, with cyclic indices, and

$$
n_j(s)=\frac1\ell\sum_{i=0}^{\ell-1}\prod_{h=0}^{j-1}v_{i+h}.
$$

Use these four moments in $P_c,H_c,T_c,Z_c$, and define the polynomial

$$
\begin{aligned}
R_s(t)={}&P_c-\chi H_c-\zeta_0
 -106(U-L)(T_c-T_a)-365(H-U)(Z_c-q_*)\\
&+(U-L)(H-U)/10,\qquad c=1-U(t).
\end{aligned}
\tag{3.7}
$$

Its degree is at most five. If $R_s(t)=\sum_{j=0}^5 d_jt^j$, its degree-twelve Bernstein coefficients are

$$
\beta_i(s)=\sum_{j=0}^{\min(i,5)}d_j
             \frac{\binom{i}{j}}{\binom{12}{j}},\qquad 0\le i\le12.
\tag{3.8}
$$

Consequently $R_s(t)=\sum_i\beta_i(s)\binom{12}{i}t^i(1-t)^{12-i}$. This identity follows by expanding $(t+(1-t))^{12-j}$ in each monomial. Each basis polynomial is nonnegative.

All directed simple cycles, up to rotation, are the words in the table. Words grouped in a row have identical four moments. The column $m$ states that every nonzero $\beta_i$ is at most $-m/10^9$; the zero column lists every zero coefficient. Substituting the displayed rational moments in (3.7)–(3.8) gives these rational inequalities by integer multiplication.

| Cyclic words | $n_1$ | $n_2$ | $n_3$ | $n_4$ | Zero indices | $m$ |
| --- | ---: | ---: | ---: | ---: | --- | ---: |
| $0$ | $1/3$ | $1/9$ | $1/27$ | $1/81$ | $12$ | $73680$ |
| $0001$ | $7/20$ | $11/90$ | $23/540$ | $2/135$ | none | $681704$ |
| $0001011,0001101$ | $38/105$ | $206/1575$ | $223/4725$ | $134/7875$ | none | $869821$ |
| $00010111,00011101$ | $11/30$ | $121/900$ | $1331/27000$ | $9/500$ | none | $771811$ |
| $00011$ | $9/25$ | $146/1125$ | $157/3375$ | $56/3375$ | none | $1159118$ |
| $000111$ | $11/30$ | $91/675$ | $1001/20250$ | $182/10125$ | none | $1016286$ |
| $001$ | $16/45$ | $17/135$ | $2/45$ | $32/2025$ | none | $561249$ |
| $001011,001101$ | $11/30$ | $181/1350$ | $11/225$ | $181/10125$ | none | $712008$ |
| $0010111,0011101$ | $13/35$ | $31/225$ | $134/2625$ | $446/23625$ | none | $882070$ |
| $0011$ | $11/30$ | $121/900$ | $11/225$ | $4/225$ | none | $935808$ |
| $00111$ | $28/75$ | $157/1125$ | $292/5625$ | $12/625$ | none | $1188992$ |
| $01$ | $11/30$ | $2/15$ | $11/225$ | $4/225$ | none | $38387$ |
| $011$ | $17/45$ | $32/225$ | $4/75$ | $68/3375$ | none | $176847$ |
| $0111$ | $23/60$ | $11/75$ | $7/125$ | $8/375$ | none | $685092$ |
| $1$ | $2/5$ | $4/25$ | $8/125$ | $16/625$ | $0$ | $70688$ |

For completeness, cycle enumeration can be performed directly on triples $0,\ldots,7$: the successors of $x$ are $2x\bmod8$ and $(2x+1)\bmod8$. Start each cycle at its least vertex and forbid repeated vertices before returning to it. The resulting vertex lists are

$$
\begin{gathered}
(0),\ (0124),\ (0125364),\ (01253764),\ (01364),\
(0136524),\ (013764),\ (01376524),\ (124),\
(125364),\ (1253764),\ (1364),\ (136524),\
(13764),\ (1376524),\ (25),\ (365),\ (3765),\ (7).
\end{gathered}
$$

Their leading triple bits give exactly the listed nineteen cyclic words. This finite graph classification concerns the moment circulation, not the number of observer states. Every coefficient in (3.8) is nonpositive, so $R_s(t)\le0$ on the entire interval. Convex cycle decomposition and the rounding equality prove (3.6) for every original stationary $V$ process.

Multiply (3.6) by each class mass and sum. Equations (3.4)–(3.5) give exactly (3.2). By (2.5), its left side has absolute value at most $\epsilon_p+\chi\epsilon_\beta$. On $[a,b]$, the two nonnegative weights in (3.2) are bounded by $106/15$ and $365/15=73/3$. Equation (2.6), applied to the two selected upper-coordinate violations together, bounds their weighted positive parts by $(146/3)\epsilon_p$. Thus

$$
\frac1{10}\pi[(u-a)(b-u)]
\le\frac{149}{3}\epsilon_p+\chi\epsilon_\beta
<52\epsilon
$$

when $\epsilon>0$; the non-strict bound at zero follows directly. This proves (3.3). $\square$

## 4. Complete-law recovery toward endpoint tags in the conserved class

**Proposition 4.1 (risk-controlled complete-law comparison).** Under Theorem 3.1 and (2.4), round $u_x$ to its nearer endpoint $r(x)\in\{a,b\}$, using $a$ at a tie. Then

$$
D:=\sum_x\pi_x\operatorname{TV}(Q_x,P_{p,r(x)})\le93000\epsilon.
\tag{4.1}
$$

These native laws are proof comparisons, not replacement decoders or independent phase attainers.

Proof. The rounded endpoint is constant on each class. Put $M=\pi|u-r(u)|$. Since the nearer endpoint distance is at most $30(u-a)(b-u)$,

$$
M\le15600\epsilon.
\tag{4.2}
$$

We first control the suspended emission distance on the same acquired classes. On a class $c$ rounded to $a$, write $D_i=V_i-a\in[0,1/15]$. Stationarity and expansion give, with $\overline D=\mathbb E D_0$,

$$
\begin{aligned}
\mathbb E[V_0V_1(1-V_2)]
={}&a^2(1-a)+(2a-3a^2)\overline D
 +(1-a)\mathbb E D_0D_1\\
&-a\mathbb E(D_0D_2+D_1D_2)-\mathbb E D_0D_1D_2\\
\ge{}&a^2(1-a)+\frac{64}{225}\overline D.
\end{aligned}
\tag{4.3}
$$

For the last inequality discard the nonnegative term and bound each negative pair by $(1/15)\overline D$ and the negative triple by $(1/225)\overline D$. The coefficient in (4.3) is $1/3-2/45-1/225=64/225$; the term $\mathbb E D_1D_2$ has the same one-time bound by stationarity. The class mean $t_c=\overline Q_c(w_{2,1})$ is $U^3$ times the left side. Since $U\ge3/5$, and

$$
T_a-U^3a^2(1-a)\le\frac8{81}(c-a),
$$

we obtain

$$
\mathbb E(V_0-a)\le17(t_c-T_a)_++2(c-a).
\tag{4.4}
$$

Indeed $225/(64(3/5)^3)<17$, and multiplying that factor by $8/81$ gives a number below $2$.

On a class rounded to $b$, write $D_i=b-V_i$. Then

$$
\mathbb E[V_0(1-V_1)]
=b(1-b)-(1-2b)\mathbb E D_0-\mathbb E D_0D_1.
$$

The class mean $f_c=\overline Q_c(w_{1,1})$ is $U^2$ times this expectation. Using $1-2b=1/5$ and

$$
U^2b(1-b)-F_b\le(8/25)(b-c)
$$

gives

$$
\mathbb E(b-V_0)\le14(F_b-f_c)_++5(b-c).
\tag{4.5}
$$

The constants follow from $5/(3/5)^2<14$ and $(5/(3/5)^2)(8/25)<5$. Average (4.4)–(4.5) over the same classes. Positive parts of class means are bounded by class averages of the corresponding positive parts. The two p-coordinate violations together have total at most $2\epsilon_p$ by (2.6). Therefore

$$
\sum_y\tau_y|v_y-r(y)|\le34\epsilon+5M.
\tag{4.6}
$$

Compare the complete synthetic program with the program having emission $r$ at both phases and the same $B,A$. Because $r$ is constant on an acquired class, that comparison program generates exactly $P_{p,r}$ from every p label in the class. Couple the next emissions maximally and use identical private transitions whenever letters agree. A p discrepancy has probability $|u-r|$; a reached suspended discrepancy contributes at most $(2/3)|v-r|$. A matched noncompleting return contributes at most $\lambda=4/15$ times the remaining complete-law discrepancy.

If $d_x=\operatorname{TV}(Q_x,P_{p,r(x)})$, this coupling yields

$$
d_x\le|u_x-r(x)|+\frac23\sum_yB_{xy}|v_y-r(y)|
              +\lambda\sum_{x'}(BA)_{xx'}d_{x'}.
$$

The bound applies to entire laws, including infinite noncompletion; regular survival tends to zero, so finite-prefix couplings pass to complete tails. Average using both actual flows and (4.6):

$$
D\le\frac{15}{11}\left(M+\frac23(34\epsilon+5M)\right)
=\frac{65}{11}M+\frac{340}{11}\epsilon
\le\frac{1014340}{11}\epsilon<93000\epsilon
$$

when $\epsilon>0$, with equality zero at zero slack. This proves (4.1). $\square$

## 5. Consuming the original supported-interior loss and lifting

**Theorem 5.1 (regular conserved-return gap).** A regular stationary return-conserved table satisfying (2.4), with a supported nonendpoint, has

$$
\epsilon>\eta/400000.
\tag{5.1}
$$

Proof. Let $w=\pi\{r(u)=a\}$. Event calibration and (4.1) give

$$
d_p|w-1/2|\le\epsilon_p+D.
\tag{5.2}
$$

For every $r\in[3/8,5/13]$, the supplied original complete word $w_{3,1}$ has mass $r^3(1-r)^5\ge q_*+\eta$ [ALPHA; DIRECTION; INTERIOR]. Its derivative has sign $3-8r$, and the minimum on this interval is at $5/13$; subtraction of $q_*$ gives the stated rational $\eta$.

The complete coordinate triangle identity therefore gives

$$
\frac{\operatorname{TV}(P_{p,a},P_{p,r})+
       \operatorname{TV}(P_{p,b},P_{p,r})}{2}
\ge\rho_p+\eta/2.
\tag{5.3}
$$

Changing the fair weights to $(w,1-w)$ changes the left side by at most $d_p|w-1/2|$. Reverse triangle and (5.2), on the same row and same supported depth, yield

$$
\sum_x\pi_x\operatorname{TV}(Q_x,P_{p,r})
\ge\rho_p+\eta/2-\epsilon_p-2D.
$$

Compare with (2.4) to obtain $\epsilon_p+D\ge\eta/4$. Thus $93001\epsilon\ge\eta/4$, and $372004<400000$ proves (5.1). No inaccessible endpoint posterior or finite depth grid is substituted for the original histories. $\square$

**Proof of Theorem 1.5.** Apply Citation 2.1 on the designated original fibre. Every positive retained label is originally reachable, so (1.6) holds on its actual $BA$ edges. Clipping retains the kernels and preserves conservation. The regular comparison therefore satisfies Theorem 5.1, with $\widehat\epsilon\le(61/11)e(M)$ and every original supported depth in its loss bounds. Consequently

$$
e(M)>\frac{11\eta}{61\cdot400000}>\frac{\eta}{2300000}.
$$

The last comparison is $11\cdot2300000>61\cdot400000$. Taking an infimum gives the non-strict class bound. Exact attainment and the eventual statement for a vanishing sequence follow by comparison with this positive threshold. The proof uses stationary support only as a necessary test of the original full-history risks; no transient or admissible actual history is removed. $\square$

## 6. A lawful nonconstant-emission member and the precise new consequence

**Proposition 6.1 (conserved immediate emission with moving complete forecasts).** There is one original-domain rational finite observer satisfying (1.6), with strictly interior nonconstant suspended emissions, positive actual-return complete-law motion, positive suspended-alpha emission change and decrease, noncollapsed successor laws, and neither interface a complete redraw. One p decoder is outside the entire Borel constant-parameter native mixture family on $[a,b]$.

Proof. On every original record fibre use two labels, fair rows and

$$
u_0=u_1=\frac{11}{30},\qquad
v_0=\frac7{20},\quad v_1=\frac{23}{60},\qquad
B=I,\qquad A=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\tag{6.1}
$$

Use the original product realization of Definition 2.2. Fair latch sampling is source-independent and takes place after the third write and latch in that same original update. Both acquired flows are fair. All original controls, records, paid histories and Stop permissions remain, and synthetic generation uses these exact acquired updates.

Each actual return swaps labels while preserving $u=11/30$. The p laws differ on $w_{0,1}=\beta\beta$ by $(19/30)(v_1-v_0)=19/900$, so complete-return motion is positive. Suspended laws differ on immediate beta by $1/30$. The actual alpha edge has expected absolute emission change $1/60$ and expected decrease $1/120$. The supplied suspended-interiority tent has expectation $1/60$. The kernels are distinct-row bijections and do not redraw a common row. The conditional successor laws differ at both interfaces.

For the p law at label 1, write $q_j=Q_1(w_{j,0})$, $c=11/30$, $U=19/30$. Then $q_0=c$, $q_1=cUv_1$, $q_2=cU^2v_1v_0$, and

$$
q_1^2-q_0q_2=c^2U^2v_1(v_1-v_0)>0.
$$

A native mixture would have $q_j=\int r[r(1-r)]^j\,d\kappa(r)$ and hence $q_1^2\le q_0q_2$ by Cauchy. This decoder is therefore not such a mixture. All entries are rational. A common denominator is $60$: draw a fresh six-bit candidate, reject values at least $60$, and use thresholds $22,21,23,30$ for $u,v_0,v_1$ and the fair latch, respectively. Acceptance probability is $15/16$, so reuse of the same finite candidate and cursor storage gives exact probabilities and almost-sure service return. The updates $B,A$ are deterministic. The bit candidate, cursor, current phase and label, installed thresholds, program counter, addresses, event/output cursors and every service microstate belong to COMPLETE. Retries store no unbounded counter. Internal service states carry the conditional continuation of that same program and add no original Read cut or permission. At each original returned cut, acquired and synthetic updates use the same represented sampler. This instantiates the supplied rational-table convention [PAID, Lemma 2.1.1 and Proposition 11.3]. The two labels are not the total COMPLETE count. Installed tables, program, numerical representation, randomness, workspace, output and synthesis are separately charged; no physical exact-real oracle or finite worst-case time bound is inferred. $\square$

This example is not near-optimal, and it does not establish independence from every supplied quantitative conjunction. It separates the new conserved-p-return predicate from zero complete-return motion, zero alpha change/decrease, endpoint suspended emissions, constant suspended emission and complete redraw. Theorem 1.5 concerns a different class from SEH: it permits the varying $v$ in (6.1) and arbitrary within-class suspended dynamics.

**Corollary 6.2 (task-relative quality).** For a model with the exact source, operation, full-tail configuration-risk and counted same-update semantics of Section 1, a supported nonendpoint and (1.6), at least one task quality $W_{{\rm conf},s}=1-R_{{\rm conf},s}$ satisfies

$$
W_{{\rm conf},p}<1-\rho_p-\eta/2300000
\quad\text{or}\quad
W_{{\rm conf},\beta}<1-\rho_\beta-\eta/2300000.
$$

Proof. Subtract the corresponding excess bound of Theorem 1.5 from one. $\square$

**Definition 6.3 (remaining frontier and mathematical correspondence).** The unrestricted alternatives remain separate: exact common conf/conf attainment; no finite exact attainer with zero infimum; positive unrestricted infimum; and fixed-resource optima. The theorem evaluates a structural class, not the unrestricted infimum. It supplies neither an attainer satisfying all necessities nor a vanishing family. It claims no lower bound on the amplitude of p-emission variation outside (1.6), no zero-defect recovery and no fixed-resource-preserving clipping. The three other phase-risk combinations retain their published scopes; (2.6) uses both configuration risks, so no new arbitrary-original-observer law/law, law/conf or conf/law gap is asserted.

The concrete next same-source question is whether one finite generator can keep both endpoint boxes and all supported-interior configuration losses while satisfying the now necessary p-emission variation as well as the supplied suspended decreases, interiority, heterogeneity and complete forecast motion. When u varies along returns, the class decomposition used in (3.4) fails. The weighted kernel $\operatorname{diag}(1-u)B\operatorname{diag}(v)A$ and unweighted $BA$ must then be handled together with their changing p-emission classes. The finite overlap graph in this proof encodes only stationary moment relations under conserved u; it is not an observer with sixteen runtime states, an unrestricted separator, or a universal encoding of other source contracts.

The whitebox consequence is task-relative semantic control of one model's actual return and generated laws. It identifies no internal implementation and classifies no arbitrary trained network by the FIB five windows.

## 7. Mathematical attribution and method boundaries

**Mathematical citation 7.1 (covered inputs and exact delta).** The raw laws, source renderer, positive-history lower witnesses, stationary extraction, clipping constants, endpoint events and boxes, rational product realization, and the interior word $\eta$ are covered by [ST; CLIP; PAID; ALPHA; DIRECTION; INTERIOR; SEH]. Their ordinary proofs remain supplied fallible inputs. The new relation (3.2) uses arbitrary nonconstant suspended emissions and the same actual circulation under return conservation of u. Its nineteen-cycle rational certificate, complete-law endpoint recovery and resulting class gap are not the constant-v stationary-product calculation of [SEH, Section 3]. The elementary circulation decomposition, independent rounding, Bernstein identity, TV coupling and triangle identity are mature tools used inside this source-specific argument, not separately claimed new general results.

**Mathematical citation 7.2 (primary realization and comparison methods).** [MW, Section 2] formulates positive realization for a stationary output process through compatible invariant cones; it does not by that result supply the additional unweighted acquired circulation or configuration-before-TV loss bounds here. [CK, Section 4] approximates TV for two specified labelled Markov-chain laws; its output-law comparison does not evaluate this joint configuration-risk minimax problem over all observer shapes. [BOS, Sections 2.3, 4, 6–7] treats finite memory, source-independent randomization and time-invariant statistical algorithms, with long-run testing or estimation losses. Those losses are not the positive-history complete-tail risk in (1.4). [TS, Abstract and Introduction] minimizes positive realizations in a specified Markov canonical form for a prescribed single-input single-output transfer function, with equality to the unrestricted positive realization dimension only for its stated system classes. [CJM, Introduction] studies existence and dimension of positive realizations of prescribed discrete-time single-input single-output transfer functions. Neither formulation prescribes the two unweighted acquired-letter flows and both conditional configuration risks of this task. These primary authored sources give bounded method context, not borrowed stopped-source conclusions or a global nonexistence search claim.

**Mathematical citation 7.3 (current DEV proof candidates under their actual scopes).** [ATOMIC, Section 7] gives closure for one deterministic rho and fixed readout, fixed-leaf residual reconstruction, and growing slice-indexed boundaries. The present proof instead checks both original stochastic acquired updates and their synthetic products explicitly in (3.4). No growth-indexed boundary is installed as fixed finite memory. [KB, Section 30] proves full-INITIAL adaptive $2r-1$ and GLOBAL $4r-1$ grid fees for a controlled deterministic complete-block reader. Its literal controls and paid endpoints are not operations of this source; no fee or stochastic-risk conclusion is transferred. [RT, Sections 45–46] removes a fixed family of Fourier certificates under same-basis Schur-diagonal layers without mixing. The binary circulation certificate here has no such basis or layer hypotheses and is proved directly. [GEOM, Section 78] gives a fixed-commission spatial-limit comparison with its stated domains and clocks, rather than an acquired stopped-source predictor. No physical map, new source query, clock, posterior port, resource optimum or risk bound from those different contracts is assumed. Their proof methods need no universal foreign-class encoding to be considered, but each borrowed conclusion would need its exact source/operation/metric/resource bridge. None is used in Theorems 3.1–5.1.

**Mathematical citation 7.4 (joint projection and quantum contraction boundaries).** [JP] is an explicitly open supplied reference. Its Sections 3–4 invert static five-mode projections under a fixed common probability law; Sections 18–20 concern compatible multiwindow marginals and hidden higher-order relations. Sections 26–30 put fixed mode-response kernels in a common signed-measure space and discuss a separately assumed mode–depth joint posterior. The hypotheses include a specified actual mode law, shared future domain and fixed response kernels. Those mode weights are not the acquired configuration rows $\pi,\tau$ here, and the response-kernel linear identity supplies neither the two acquired flows nor configuration-before-TV calibration. The moment circulation in Section 3 is derived directly from this source's actual $AB$ path; it does not install a five-mode joint law or a new observation. Thus the static projection, window-dimension and mode–depth identities do not supply (3.2) or its class gap. No conclusion from [JP] is a premise of that proof.

[CMI] concerns finite-dimensional density matrices, a finite Kraus channel, its local trace-norm contraction ratio and a trace-norm conditional mutual-information functional on tripartite states. Its stated flagged-qubit counterexample keeps the latter functional while contracting local trace distance. These quantum state and channel hypotheses are not the acquired letter kernels or complete countable tail losses here. The elementary maximal couplings in Sections 2 and 4 are between the two explicitly specified classical same-update programs; they invoke no local-to-CMI contraction statement. No quantum risk, matrix coordinate, ancillary system, measurement or physical resource is transported into this source. The public formal and Blueprint descriptions are inspected as supplied sources, without new compilation or any claim of their current kernel or frozen status.

## 8. References

- **ST:** [Randomized stopped-tail minimax](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md).
- **CLIP:** [Risk-controlled emission moment feasibility](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md), Sections 1–3.
- **PAID:** [Effective paid-history certificates](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md), Lemma 2.1.1, Sections 9–15.
- **ALPHA:** [Acquired-alpha calibration compatibility](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/AURIC_FIB_ATOM_ACQUIRED_ALPHA_CALIBRATION_COMPATIBILITY.md).
- **DIRECTION:** [Directional alpha calibration](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/AURIC_FIB_ATOM_DIRECTIONAL_ALPHA_CALIBRATION.md).
- **INTERIOR:** [Suspended-emission interiority](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SUSPENDED_EMISSION_INTERIORITY.md).
- **SEH:** [Suspended-emission heterogeneity](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SUSPENDED_EMISSION_HETEROGENEITY.md).
- **ATOMIC:** [Atomic boundary trichotomy](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md), Section 7.
- **KB:** [KBonacci self-calibrating boundaries](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/KBONACCI_SELF_CALIBRATING_BOUNDARIES.md), Section 30.
- **RT:** [Arithmetic holographic RT](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/ARITHMETIC_HOLOGRAPHIC_RT.md), Sections 45–46.
- **GEOM:** [Boundary geometry continuation III](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md), Section 78.
- **JP:** [Joint projection, multiwindow order and response fibres](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/docs/develop/theory/AURIC_FIB_ATOM_JOINT_PROJECTION_MULTIWINDOW_ORDER_AND_RESPONSE_FIBERS.md), Sections 3–4, 18–20 and 26–30; open supplied reference.
- **CMI:** [Trace-norm CMI contraction refutation description](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/Blueprint/D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.md), with its [formal source](https://github.com/the-omega-institute/trureturing/blob/2b7dbda6e57e482bfe85e6767e23fd933a099b3d/D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.lean); finite-dimensional quantum scope.
- **MW:** Alex Monràs and Andreas Winter, *Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem*, [arXiv:1412.3634v1](https://arxiv.org/html/1412.3634v1), Section 2.
- **CK:** Taolue Chen and Stefan Kiefer, *On the Total Variation Distance of Labelled Markov Chains*, [arXiv:1405.2852v1](https://arxiv.org/html/1405.2852v1), DOI [10.1145/2603088.2603099](https://doi.org/10.1145/2603088.2603099).
- **TS:** Hamed Taghavian and Jens Sjölund, *Minimal positive Markov realizations*, [arXiv:2502.21102v3](https://arxiv.org/html/2502.21102v3), Abstract and Introduction.
- **CJM:** Wojciech Czaja, Philippe Jaming and Máté Matolcsi, *An efficient algorithm for positive realizations*, [arXiv:math/0612551v2](https://arxiv.org/html/math/0612551v2), Introduction.
- **BOS:** Tomer Berg, Or Ordentlich and Ofer Shayevitz, *Statistical Inference with Limited Memory: A Survey*, [arXiv:2312.15225v1](https://arxiv.org/html/2312.15225v1).

## 追加锚（本行以下为增补区）

## 9. A uniform bridge from small actual-return variation to the conserved class

**Definition 9.1 (unweighted conditional return variation).** Retain exactly Definitions 1.1–1.3. Let $\mathcal H_{p,S}$ be all positive original p histories on the seed-1, marker-100 held-record fibre of (1.5), including every legal paid prefix and every finite fourth-segment return. At such a history let $\rho_h(x)$ be the actual conditional configuration row, $B_{xy}$ the actual p-beta update and $A_{yx'}$ the actual suspended-alpha update on that fibre. Write $u_x$ for the configuration's next synthetic alpha probability. Define

$$
\begin{aligned}
\mathcal V_h(M)
&=\sum_{x,y,x'}\rho_h(x)B_{xy}A_{yx'}|u_x-u_{x'}|,\\
\mathcal V(M)&=\sup_{h\in\mathcal H_{p,S}}\mathcal V_h(M).
\end{aligned}
\tag{9.1}
$$

This is the conditional mean of $|u_{\mathrm{before}}-u_{\mathrm{after}}|$ given $h$ and the actual noncompleting return beta-alpha. The future actual letters, conditional on the same once-sampled $K$, are independent of the observer's private choices; source-independent initialization and updates imply the same independence conditional on a fixed observed history. The probability of that actual return is $\sum_k\nu_h(k)r_k(1-r_k)>0$ and is independent of the current private configuration conditional on $h$. It therefore cancels from the conditional expectation. No factor $(1-u_x)v_y$ belongs in (9.1), even when a synthetic noncompletion letter has probability zero. All rows, conditionings and absolute differences in this definition are analysis objects, not new runtime inputs.

For a regular stationary table of Definition 2.2 put

$$
V_\pi=\sum_{x,y,x'}\pi_xB_{xy}A_{yx'}|u_x-u_{x'}|,
\qquad g=\frac{\eta}{400000}.
\tag{9.2}
$$

**Theorem 9.2 (finite closure of small return flow, with both configuration risks).** Let $X,Y,\pi,\tau,B,A,u,v$ be a regular stationary table of Definition 2.2, after deleting zero-row labels. For every $t>0$ there is one regular stationary table with the same p labels and row $\pi$, a finite split suspended carrier $Y^c$, row $\tau^c$, kernels $B^c,A^c$, and emissions $u^c,v^c$, whose p emission is conserved on every positive actual return. Both acquired flow identities hold exactly. With $Q_x,W_y$ and $Q_x^c,W_{y,C}^c$ denoting their own generated complete laws, there is a split row satisfying $\sum_C\tau^c_{y,C}=\tau_y$ and

$$
\begin{aligned}
D_p&:=\sum_x\pi_x\operatorname{TV}(Q_x,Q_x^c)
 \le\frac{15}{11}t+\frac4{11}\frac{V_\pi}{t},\\
D_\beta&:=\sum_{(y,C)\in Y^c}\tau^c_{y,C}
 \operatorname{TV}(W_y,W_{y,C}^c)
 \le\frac6{11}t+\frac6{11}\frac{V_\pi}{t}.
\end{aligned}
\tag{9.3}
$$

For every pair of probability targets $T_p,T_\beta$ on the two original complete raw carriers, these same quantities bound the absolute differences of the corresponding configuration-before-TV losses. In particular, (2.4) for the old table implies (2.4) for the new table with slacks $\epsilon_p+D_p,\epsilon_\beta+D_\beta$, simultaneously for every supported depth. The construction has at most

$$
|Y|\min\{|X|,\lceil(b-a)/t\rceil+2\}
\tag{9.4}
$$

suspended labels. This label count is not a COMPLETE or total-resource bound.

Proof. Choose a shifted interval grid of width $t$. For $\theta\in[0,t)$ give $x$ the bin index $\lfloor(u_x-\theta)/t\rfloor$. Let $\mathcal C$ be the occupied bins, viewed as subsets of $X$, and let $C(x)$ denote the bin of $x$. Define the crossing mass

$$
\delta_\theta=
\sum_{x,y,x':\,C(x)\ne C(x')}\pi_xB_{xy}A_{yx'}.
\tag{9.5}
$$

For two real numbers separated by $d$, the proportion of shifts putting them in different width-$t$ bins is $\min\{1,d/t\}$. Integrating the finite sum (9.5) over the shift therefore gives

$$
\frac1t\int_0^t\delta_\theta\,d\theta
=\sum_{x,y,x'}\pi_xB_{xy}A_{yx'}
 \min\{1,|u_x-u_{x'}|/t\}\le V_\pi/t.
\tag{9.6}
$$

There is a fixed shift with crossing mass $\delta\le V_\pi/t$. Choose one such shift. The integration is a mathematical selection argument: the installed observer has no shift sampler or correlated source seed. Each occupied bin has emission diameter less than $t$. Choose one old emission $c_C\in[a,b]$ in each bin and put $u_x^c=c_{C(x)}$. There are at most $\min\{|X|,\lceil(b-a)/t\rceil+2\}$ occupied bins.

Split a suspended label by the bin of its incoming p label. Retain exactly the pairs $(y,C)$ with

$$
\tau^c_{y,C}=\sum_{x\in C}\pi_xB_{xy}>0.
\tag{9.7}
$$

Define

$$
B^c_{x,(y,C)}=\mathbf1_{\{x\in C\}}B_{xy},
\qquad v^c_{y,C}=v_y.
\tag{9.8}
$$

Every row of $B^c$ sums to one; a nonzero entry cannot point to a deleted pair because $\pi_x>0$. Thus $\pi B^c=\tau^c$ exactly and $\sum_C\tau^c_{y,C}=\tau_y$.

For $x'\in C$ define the missing influx

$$
d_{x'}^C=\pi_{x'}-\sum_y\tau^c_{y,C}A_{yx'}\ge0,
\qquad D_C=\sum_{x'\in C}d_{x'}^C,
\qquad m_{y,C}=\sum_{x'\notin C}A_{yx'}.
\tag{9.9}
$$

Nonnegativity follows from $\tau A=\pi$ and $\tau^c_{y,C}\le\tau_y$. The equality of outgoing and incoming crossing masses for one bin is

$$
\begin{aligned}
D_C
&=\pi(C)-\sum_y\tau^c_{y,C}\sum_{x'\in C}A_{yx'}\\
&=\sum_y\tau^c_{y,C}m_{y,C},
\qquad \sum_C D_C=\delta.
\end{aligned}
\tag{9.10}
$$

Here $\sum_y\tau^c_{y,C}=\pi(C)$. If $D_C>0$, repair the outgoing cross-bin probability by

$$
A^c_{(y,C),x'}=
\begin{cases}
A_{yx'}+m_{y,C}d_{x'}^C/D_C,&x'\in C,\\
0,&x'\notin C.
\end{cases}
\tag{9.11}
$$

If $D_C=0$, (9.10) implies $m_{y,C}=0$ for every retained pair in that bin; set $A^c_{(y,C),x'}=\mathbf1_{\{x'\in C\}}A_{yx'}$. No division by zero occurs. Every row is stochastic and supported inside $C$. For $x'\in C$,

$$
\sum_y\tau^c_{y,C}A^c_{(y,C),x'}
=\sum_y\tau^c_{y,C}A_{yx'}+d_{x'}^C=\pi_{x'},
\tag{9.12}
$$

with the same identity in the zero case. Hence $\tau^c A^c=\pi$. Moreover

$$
\operatorname{TV}(A_{y,\cdot},A^c_{(y,C),\cdot})=m_{y,C},
\qquad
\sum_{y,C}\tau^c_{y,C}m_{y,C}=\delta.
\tag{9.13}
$$

Indeed probability $m_{y,C}$ is removed outside $C$ and added inside $C$. Every new positive $B^cA^c$ edge stays in one bin, so $u^c$ is exactly return-conserved. This proof uses stationarity for balance, without irreducibility, reversibility or a mixing-time bound.

Use these emissions and these same acquired-letter kernels to generate the new decoders. Both old and new synthetic returns have survival probability at most $4/15$, from every label; their complete laws therefore normalize while retaining the infinite outcome with mass zero. Write

$$
p_x=\operatorname{TV}(Q_x,Q_x^c),
\qquad b_{y,C}=\operatorname{TV}(W_y,W_{y,C}^c).
$$

Maximally couple the p emissions and then use the identical $B$ row with its indicated split label whenever beta matches. The complete-law recursion gives

$$
p_x\le |u_x-c_{C(x)}|+
\frac23\sum_yB_{xy}b_{y,C(x)}.
\tag{9.14}
$$

At suspension the emissions agree. Compare the old and repaired $A$ rows first, and compare their successor laws configuration by configuration next. Equation (9.13), TV contraction under a kernel of probability laws, and convexity give

$$
b_{y,C}\le\frac25\left(m_{y,C}+
\sum_{x'}A^c_{(y,C),x'}p_{x'}\right).
\tag{9.15}
$$

These inequalities concern entire stopped laws. They can also be obtained on every finite prefix and passed to the complete carrier using the uniform geometric survival bound; no conditioning on eventual completion is used. Average (9.14)–(9.15) with the same rows, and use both exact new flows:

$$
D_p\le t+\frac23D_\beta,
\qquad D_\beta\le\frac25(\delta+D_p).
\tag{9.16}
$$

Solving gives $D_p\le15t/11+4\delta/11$ and $D_\beta\le6t/11+6\delta/11$. Equation (9.6) proves (9.3). For a target $T_p$, the configurationwise reverse triangle inequality gives

$$
\left|\sum_x\pi_x\operatorname{TV}(Q_x^c,T_p)
-\sum_x\pi_x\operatorname{TV}(Q_x,T_p)\right|\le D_p.
\tag{9.17}
$$

At suspension apply the same inequality to each pair $(y,C)$ and use $\sum_C\tau^c_{y,C}=\tau_y$ to obtain the bound $D_\beta$. Thus both risks and every target are controlled by one repaired table, with TV taken before the configuration average.

For its original-domain interpretation, apply [PAID97, Lemma 2.1.1] to this single finite table: keep the full original $C_0$, sample the fixed row $\pi$ privately after the original third record write and latch in that same update, use $B^c$ on p-beta and $A^c$ on suspended-alpha, and use the unchanged original completion and Stop rules. Before the latch use the supplied original-control product and fair synthesis. Both seeds, all marker records, all paid rejections, every finite return and every original permission remain. At every original history on every held-record fibre its actual private row is $\pi$ or $\tau^c$ by induction over these exact flows. Its target is the unchanged posterior mixture for that same once-sampled $K$. Countable TV convexity applies to the target only after each configuration's TV; it therefore turns simultaneous pure-depth upper bounds into all-history configuration-risk upper bounds for this one comparison. Rendering through each original $I_c$ preserves the complete-law comparisons and their Stop blocks.

Only a finite label and the charged original control are retained online. Bins, shifts, flows, deficits and row vectors are fixed mathematical construction data, not readable online rows, an archive, a clock, an acquisition counter, a posterior or a source-reset operation. If all old table data and $t$ are rational, the crossing function has finitely many rational breakpoints and is constant between them. A rational shift in an interval minimizing that function, rational representatives $c_C$, and (9.7)–(9.11) give rational new tables. The supplied finite exact categorical-sampling convention charges all installed thresholds, program, numerical representation, workspace and sampler microstates to COMPLETE and uses the same sampler on acquired and synthetic updates. Arbitrary real entries specify abstract finite stochastic rules, without a physical exact-real oracle. No fixed resource budget or hard marginalized-defect budget is preserved. $\square$

**Theorem 9.3 (uniform original risk–return-variation inequality).** For every finite COMPLETE observer satisfying Definitions 1.1–1.3, on every fixed finite or countable prior with $\mu(1),\mu(2)>0$ and a supported $k\ge3$,

$$
\frac{61}{11}e(M)+\frac{19}{11}\sqrt{\mathcal V(M)}>g
=\frac{\eta}{400000}.
\tag{9.18}
$$

This is a uniform lower bound on a joint risk-and-variation expression, with no carrier-size, mixing-rate, prior-mass-floor, defect or prescribed-resource hypothesis. It is not a lower bound on the unrestricted excess alone.

Proof. Start from the literal original observer, including its source-independent initialization before the first paid seed Read. Extract the same common rows and actual kernels on (1.5) by [PAID97, Lemma 14.1], as in Citation 2.1. The extraction also retains the needed return statistic. To see this additional consequence, write

$$
f_x=\sum_{y,x'}B_{xy}A_{yx'}|u_x-u_{x'}|.
$$

The supplied paid histories approaching each supported pure depth have the same limiting row $\lambda$ from the original initialized rejection-chain and suffix updates. For every fixed $j$, appending $j$ actual returns gives rows tending to $\lambda(BA)^j$. Every approximant remains a positive original history in $\mathcal H_{p,S}$, so its row applied to $f$ is at most $\mathcal V(M)$. Finite-row continuity gives $\lambda(BA)^j f\le\mathcal V(M)$. The same Cesaro averages and the same convergent subsequence used for both phase-risk bounds then give

$$
\pi f\le\mathcal V(M).
\tag{9.19}
$$

The two extracted pure-depth configuration-risk bounds still hold on these same rows, for every supported depth. In particular, no stationary row is optimized independently at either interface. The supplier's summable likelihood-ratio domination handles the countable prior, and all approximants include their actual paid rejections, original records and returns. Transient configurations remain in the original risk and variation domains, although the necessary stationary test can omit them from its positive support.

Delete zero-row labels and clip the two emissions to $[a,b]$, retaining the actual kernels and both rows. The common-row form of [CLIP97, Theorem 3.1], used in Citation 2.1, gives simultaneous slacks at most $61e(M)/11$ in (2.4). Scalar clipping is 1-Lipschitz, hence the clipped stationary variation satisfies

$$
\widehat V_\pi
=\sum_{x,y,x'}\pi_xB_{xy}A_{yx'}
 |[u_x]_{[a,b]}-[u_{x'}]_{[a,b]}|
\le\pi f\le\mathcal V(M).
\tag{9.20}
$$

If $\mathcal V(M)>0$, apply Theorem 9.2 to this clipped table with $t=\sqrt{\mathcal V(M)}$. Its two complete-law error bounds satisfy

$$
D_p\le\frac{19}{11}\sqrt{\mathcal V(M)},
\qquad
D_\beta\le\frac{12}{11}\sqrt{\mathcal V(M)}.
\tag{9.21}
$$

The one repaired table is exactly return-conserved and satisfies (2.4), simultaneously for the entire supported depth set, with both slacks bounded by

$$
\epsilon^c=\frac{61}{11}e(M)
 +\frac{19}{11}\sqrt{\mathcal V(M)}.
\tag{9.22}
$$

The supplied conserved-class Theorem 5.1 applies to that comparison and gives $\epsilon^c>g$. If $\mathcal V(M)=0$, (9.20) and nonnegativity show that every positive clipped $BA$ edge conserves its emission. Apply Theorem 5.1 directly with the common slack $61e(M)/11$, obtaining the same strict inequality without a width-zero construction. This proves (9.18).

The original initialization, paid acquisition and complete history domain are used in (9.19); they have not been replaced by a stationary initial source. The repaired observer is a comparison used to contradict the supplied conserved-class bound. Its existence is not sufficient for an unrestricted optimizer, and no comparison changes the meaning of the original $e(M)$ or $\mathcal V(M)$. $\square$

**Corollary 9.4 (nonvanishing return amplitude in a vanishing-excess family).** Under Theorem 9.3's hypotheses, if $e(M)<11g/61$, then

$$
\mathcal V(M)>
\left(\frac{11g-61e(M)}{19}\right)^2.
\tag{9.23}
$$

For any sequence of lawful finite COMPLETE observers for one fixed such prior, with both original configuration excesses tending to zero,

$$
\liminf_n\mathcal V(M_n)\ge
\left(\frac{11\eta}{7600000}\right)^2>0.
\tag{9.24}
$$

A finite exact common conf/conf attainer, if one exists, must satisfy the strict inequality $\mathcal V(M)>(11\eta/7600000)^2$. The carriers of the sequence may grow; every member separately obeys the full finite contract.

Proof. Multiply (9.18) by $11$ and isolate its strictly positive square-root term to obtain (9.23). Apply it to a tail of the sequence and pass to the lower limit. The exact-attainer statement is (9.23) with $e(M)=0$. $\square$

**Mathematical citation 9.5 (supplied facts, new bridge and literature scope).** In this section [PAID97] is [Effective paid-history certificates at the fixed source revision](https://github.com/the-omega-institute/trureturing/blob/97ef5c26c09451e8640cad4e381bf66681defe17/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md), specifically Lemmas 2.1.1 and 14.1, and [CLIP97] is [Risk-controlled emission moment feasibility at that revision](https://github.com/the-omega-institute/trureturing/blob/97ef5c26c09451e8640cad4e381bf66681defe17/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md), specifically Theorem 3.1. These supply original-domain realization, initialized paid-history extraction and the $61/11$ factor. Theorem 5.1 supplies the evaluated positive conserved-class constant. They are reused with their original hypotheses, not reproved as new content.

[PAID97, Theorem 9.2] aggregates cells defined by already close complete-law vectors and regenerates decoders while preserving both flows. It does not make p emissions constant on every return when only the mean immediate-emission increment is small. [PAID97, Theorem 13.1] replaces an entire phase kernel by a redraw and controls loss by dispersion of complete successor laws, a different hypothesis. [ALPHA, Theorem 1.1] controls suspended-to-p emission mismatch, which (9.1) does not measure. The new bridge is the directed crossing-flow repair (9.7)–(9.13) together with both complete configuration-loss comparisons (9.14)–(9.17), consumed on the original acquired histories in (9.19)–(9.22). It extends the zero-variation class consequence to an evaluated positive-amplitude necessity; it supplies no new unrestricted risk-only gap.

Random shifted intervals, balancing finite nonnegative flows, maximal couplings and triangle inequalities are mature intermediate tools. Positive realization in [MW, Section 2] starts from a stationary output process and compatible invariant cones. [TS, Abstract and Introduction] and [CJM, Introduction] seek positive realizations of a prescribed linear single-input single-output transfer function, with [TS] minimizing dimension in Markov form. Those results do not by their stated hypotheses supply the two prescribed unweighted acquired flows or configuration-before-TV risk comparisons in (9.17). [CK, Theorem 7 and Corollary 8] evaluates TV for a supplied pair of labelled Markov-chain laws; it does not close this risk-versus-return-variation bridge over every finite observer.

A. Yu. Mitrophanov, *Sensitivity and convergence of uniformly ergodic Markov chains*, [DOI 10.1239/jap/1134587812](https://doi.org/10.1239/jap/1134587812), relates perturbation sensitivity to uniform ergodicity and the iterated-kernel ergodicity coefficient. No uniform ergodicity of the actual return kernel is assumed here. Equations (9.10)–(9.12) instead preserve the chosen stationary p row exactly, and the complete-tail comparison uses the fixed stopping survival bound. No conclusion about perturbations of stationary distributions is borrowed. Theorems 9.2–9.3 are ordinary `repo-derived` mathematics from these supplied source facts and the explicit repair; no kernel verification, frozen status, physical implementation theorem or global literature-priority claim is asserted.

**Definition 9.6 (remaining joint problem and completion criterion).** The original unrestricted quantity is still $\inf_M e(M)$ over all lawful finite COMPLETE observers for the same installed prior, with both risk interfaces and all original positive histories belonging to each one observer. Whether this infimum is zero and whether a finite member attains it remain unresolved by (9.18). The inequality is consistent with a positive unrestricted gap, an unattained zero infimum, or an exact common attainer with sufficiently large actual-return variation. A zero-infimum construction must provide one lawful finite observer per tolerance, with both full-domain excesses tending to zero; a finite-attainment construction must supply one table satisfying both complete phase bounds for every supported depth and its original-domain realization. The positive necessity (9.24), like the supplied alpha, heterogeneity and continuation necessities, is an additional joint condition for such a construction and is not sufficient for one. A positive unrestricted-gap proof must remove the unconstrained variation term by a further original-contract argument; a stationary finite grid or separate phase optimizers do not do so.

## 追加锚（本行以下为增补区）

## 10. Linear compatibility stability on the unchanged acquired circulation

**Definition 10.1 (the original compatibility functional).** Use the regular stationary table of Definition 2.2: finite carriers $X,Y$, stochastic actual acquired kernels $B,A$, probability rows $\pi,\tau$ with $\pi B=\tau$ and $\tau A=\pi$, emissions $u_x,v_y\in[a,b]=[1/3,2/5]$, and the complete laws (2.3). Delete only zero-row labels by the support-closed rule of Citation 2.1. The configuration-risk inequalities (2.4) are not part of the hypotheses in this definition. Retain $E_p,E_\beta,T_a,q_*$ from Citation 2.3 and exactly $\chi,\zeta_0$ from (3.1). Put

$$
\begin{aligned}
\mathcal C={}&\pi Q(E_p)-\chi\tau W(E_\beta)-\zeta_0\\
&-106\sum_x\pi_x(b-u_x)\bigl(Q_x(w_{2,1})-T_a\bigr)\\
&-365\sum_x\pi_x(u_x-a)\bigl(Q_x(w_{3,1})-q_*\bigr)\\
&+\frac1{10}\sum_x\pi_x(u_x-a)(b-u_x),\\
V_\pi={}&\sum_{x,y,x'}\pi_xB_{xy}A_{yx'}|u_x-u_{x'}|.
\end{aligned}
\tag{10.1}
$$

Thus $\mathcal C$ is the left side minus the right side of (3.2), and $V_\pi$ is exactly (9.2). Its acquired-return weights are unweighted by synthetic emission or survival probabilities. An actual transition is never deleted because a predicted letter has probability zero.

**Theorem 10.2 (unconditional linear weighted-return compatibility).** Every table of Definition 10.1 satisfies

$$
\mathcal C\le5000V_\pi.
\tag{10.2}
$$

The constant is independent of the finite carriers, their stochastic entries and their stationary masses. No configuration-risk, irreducibility, reversibility, mixing or additional resource hypothesis is imposed. At $V_\pi=0$, (10.2) is exactly the original compatibility inequality (3.2).

Proof. Take the stationary alternating analysis chain

$$
X_0\ \xrightarrow{B}\ Y_0\ \xrightarrow{A}\ X_1
\ \xrightarrow{B}\ Y_1\ \xrightarrow{A}\ X_2\ \cdots,
\qquad X_0\sim\pi.
$$

Set $c_i=u_{X_i}$, $U_i=1-c_i$ and $V_i=v_{Y_i}$. The two flow identities imply stationarity under a shift of one complete $BA$ pair, including all joint finite windows. Consequently

$$
\mathbb E|c_{i+1}-c_i|=V_\pi,
\qquad
\mathbb E|c_i-c_0|\le iV_\pi.
\tag{10.3}
$$

The second assertion follows by the triangle inequality and the first one. This chain describes finite compositions of the actual acquired kernels. It does not condition the original source on infinite noncompletion, and its index is not a runtime clock.

For $0\le j\le3$, let

$$
t_j=\left(\prod_{i=0}^{j}U_i\right)
       \left(\prod_{i=0}^{j-1}V_i\right)(1-V_j),
\qquad
H^{\rm act}=1-V_0+V_0U_1(1-V_1),
\tag{10.4}
$$

where an empty product equals one. Iterating the exact individual generation equations (2.3) gives, for any real function $g$ on $[a,b]$,

$$
\sum_x\pi_xg(u_x)Q_x(w_{j,1})
=\mathbb E[g(c_0)t_j],
\qquad
\tau W(E_\beta)=\mathbb EH^{\rm act}.
\tag{10.5}
$$

Indeed $w_{j,1}$ has $j$ noncompleting beta-alpha pairs, followed by p-beta and suspended-beta. Its successive synthetic probabilities are $U_iV_i$ for $i<j$ and $U_j(1-V_j)$ at the end; the intervening transitions are precisely the displayed $B,A$ path. The suspended event has immediate beta probability $1-V_0$, or alpha followed by $w_{0,1}$ with probability $V_0U_1(1-V_1)$. In particular its p factor before comparison is $U_1$, not $U_0$. These identities expand finite words of the complete laws; they neither normalize a weighted return kernel nor replace either complete law.

Replace only the later p factors in these finite expressions by $U_0$:

$$
t_j^0=U_0^{j+1}\left(\prod_{i=0}^{j-1}V_i\right)(1-V_j),
\qquad
H^0=1-V_0+U_0V_0(1-V_1).
\tag{10.6}
$$

All factors lie in $[0,1]$. The identity obtained by changing one factor at a time therefore yields

$$
|t_j-t_j^0|\le\sum_{i=1}^{j}|c_i-c_0|,
\qquad
|H^{\rm act}-H^0|\le|c_1-c_0|.
$$

Together with (10.3), this gives

$$
\mathbb E|t_j-t_j^0|\le\frac{j(j+1)}2V_\pi,
\qquad
\mathbb E|H^{\rm act}-H^0|\le V_\pi.
\tag{10.7}
$$

For a fixed $c\in[a,b]$ and $z=(z_0,z_1,z_2,z_3)\in[a,b]^4$, put $U=1-c$ and

$$
\begin{aligned}
P(c,z)&=U(1-z_0)+U^2z_0(1-z_1)+U^3z_0z_1(1-z_2),\\
H(c,z)&=1-z_0+Uz_0(1-z_1)=1-cz_0-Uz_0z_1,\\
T(c,z)&=U^3z_0z_1(1-z_2),\\
Z(c,z)&=U^4z_0z_1z_2(1-z_3),\\
f_c(z)&=P(c,z)-\chi H(c,z)-\zeta_0\\
&\quad-106(b-c)(T(c,z)-T_a)-365(c-a)(Z(c,z)-q_*)\\
&\quad+\frac1{10}(c-a)(b-c).
\end{aligned}
\tag{10.8}
$$

Define $F^0=\mathbb Ef_{c_0}(V_0,V_1,V_2,V_3)$. By (10.5), this is exactly the expression for $\mathcal C$ with $t_j,H^{\rm act}$ replaced by $t_j^0,H^0$. The two root weights still use $c_0$; constants and the tent term have not changed. Since $b-a=1/15$ and $0<\chi<2$, (10.7) implies

$$
\begin{aligned}
|\mathcal C-F^0|
&\le\left(1+3+\chi+\frac{106}{15}\,3
                         +\frac{365}{15}\,6\right)V_\pi\\
&\le174V_\pi.
\end{aligned}
\tag{10.9}
$$

The first two errors are those for $w_{1,1},w_{2,1}$ in $E_p$; $w_{0,1}$ has zero error. The bounds for the weighted $w_{2,1}$ and $w_{3,1}$ use their nonnegative root weights bounded by $106/15$ and $365/15$. The displayed coefficient is $4+\chi+106/5+146<174$.

We now control $F^0$ on the same joint chain. Regard the binary endpoint tuple $z\in\{a,b\}^4$ as an edge

$$
(z_0,z_1,z_2)\longrightarrow(z_1,z_2,z_3)
\tag{10.10}
$$

of the eight-vertex overlap graph from Section 3, with edge weight $f_c(z)$. On a cyclic word $s$, the mean of its $j$th word term is $U^{j+1}(n_j(s)-n_{j+1}(s))$, and the mean of $H$ is $1-cn_1(s)-Un_2(s)$. Hence its mean edge weight is exactly $R_s(15(b-c))$ of (3.7): $U-3/5=b-c$ and $2/3-U=c-a$. The supplied complete simple-cycle certificate (3.7)–(3.8) therefore gives nonpositive total weight on every directed simple cycle, for every $c\in[a,b]$. It is reused without a second cycle enumeration. Any closed walk has nonpositive total weight, since successively cutting at repeated vertices decomposes it into directed simple cycles.

For each vertex $s$ define $h_c(s)$ as the maximum total $f_c$ weight of a vertex-simple directed path starting at $s$, allowing any endpoint and the zero-length path. Such paths have at most seven edges and form a finite set. Deleting a nonpositive cycle from any walk cannot decrease its total weight and preserves its start and endpoint. Thus $h_c(s)$ is also the maximum over all finite walks starting at $s$. Prepend an edge $s\to t$ to a maximizing path starting at $t$ and delete cycles if needed. It follows that

$$
f_c(s\to t)\le h_c(s)-h_c(t).
\tag{10.11}
$$

This finite-path shortening is the sign-reversed elementary step in [KARP, Lemma 1 proof, printed p.2]. It is used here inside the source-specific proof, without any graph hypothesis about the actual acquired carrier.

The potential can be chosen uniformly Lipschitz in its parameter. For every endpoint tuple in (10.8), direct differentiation gives

$$
|\partial_cP|\le1+2+3=6,\qquad
|\partial_cH|=z_0(1-z_1)\le1,\qquad
|\partial_cT|\le3,\qquad |\partial_cZ|\le4.
$$

Both $T,T_a$ and $Z,q_*$ lie in $[0,1]$, so their corresponding absolute differences are at most one. Also

$$
\left|\partial_c\frac{(c-a)(b-c)}{10}\right|
=\frac{|a+b-2c|}{10}\le\frac1{150}.
$$

The product rule, the two root weights at most $1/15$, and $\chi<2$ consequently give

$$
|\partial_cf_c(z)|
\le6+2+106\left(1+\frac3{15}\right)
        +365\left(1+\frac4{15}\right)+\frac1{150}
=\frac{89631}{150}<600.
\tag{10.12}
$$

Every simple-path weight is therefore $4200$-Lipschitz as a function of $c$. The finite maximum defining $h_c(s)$ has the same bound: if each path function changes by at most $4200|c-d|$, taking its maximum at the two parameters preserves that inequality in both directions. Hence

$$
|h_c(s)-h_d(s)|\le4200|c-d|
\quad(c,d\in[a,b]).
\tag{10.13}
$$

This argument also applies at ties between maximizing paths and at zero-weight cycles.

Conditionally on the entire acquired analysis path, round each $V_i$ independently to $\xi_i\in\{a,b\}$, with

$$
\Pr(\xi_i=b\mid\text{path})=\frac{V_i-a}{b-a},
\qquad \mathbb E(\xi_i\mid\text{path})=V_i.
\tag{10.14}
$$

Distinct time positions use independent proof coins, even when the same suspended configuration recurs. The expression $f_c$ is affine separately in each of its four $z$ arguments. Conditional independence thus preserves each of its monomials, including all their correlations with $c_0$:

$$
F^0=\mathbb Ef_{c_0}(\xi_0,\xi_1,\xi_2,\xi_3).
\tag{10.15}
$$

The rounded joint process stays stationary under the shift of one acquired pair. Put $S_i=(\xi_i,\xi_{i+1},\xi_{i+2})$. In particular $(c_0,S_0)$ and $(c_1,S_1)$ have the same distribution. Apply (10.11) to the edge $S_0\to S_1$ at its actual parameter $c_0$, use this joint stationarity, and then (10.13):

$$
\begin{aligned}
F^0
&\le\mathbb E\bigl[h_{c_0}(S_0)-h_{c_0}(S_1)\bigr]\\
&=\mathbb E\bigl[h_{c_1}(S_1)-h_{c_0}(S_1)\bigr]\\
&\le4200\mathbb E|c_1-c_0|=4200V_\pi.
\end{aligned}
\tag{10.16}
$$

All expectations are finite because the graph is finite and its path weights are bounded on the compact parameter interval. The equality does not assume stationarity conditional on $c_0$, independence between p and suspended emissions, or independence of the acquired configurations. Such a conditional-stationarity premise would be unjustified when $u$ varies.

Combining (10.9) and (10.16) gives $\mathcal C\le4374V_\pi\le5000V_\pi$. The stated constant is merely sufficient. If $V_\pi=0$, every nonnegative summand defining $V_\pi$ in (10.1) vanishes, so every positive stationary actual $BA$ edge conserves $u$. All finite-product errors and the potential increment in this proof vanish as well, giving $\mathcal C\le0$, precisely (3.2). The argument alters no emission, acquired kernel, stationary row, target or complete law of the given table. Its paths, rounding coins and potentials are analysis objects. $\square$

**Corollary 10.3 (same-table endpoint concentration).** Add exactly the simultaneous configuration-risk bounds (2.4) to the table of Definition 10.1, with the same two rows, nonnegative slacks and every supported depth, including both original endpoints. Put $\epsilon=\max(\epsilon_p,\epsilon_\beta)$ and $J=\pi[(u-a)(b-u)]$. Then

$$
\begin{aligned}
J
&\le50000V_\pi+\frac{1490}{3}\epsilon_p+10\chi\epsilon_\beta\\
&\le50000V_\pi+520\epsilon,\\
\pi\operatorname{dist}(u,\{a,b\})
&\le1500000V_\pi+15600\epsilon.
\end{aligned}
\tag{10.17}
$$

For $0<d\le1/30$,

$$
\pi\{a+d\le u\le b-d\}
\le\min\left\{1,
\frac{50000V_\pi+520\epsilon}{d(1/15-d)}\right\}.
\tag{10.18}
$$

Proof. Write $L=\pi Q(E_p)-\chi\tau W(E_\beta)-\zeta_0$ and let $G$ be the sum of the two weighted coordinate terms subtracted in (10.1). Identity (3.1) and (2.5) give $-L\le\epsilon_p+\chi\epsilon_\beta$. The two weights are nonnegative and bounded by $106/15$ and $365/15$; the larger bound is $73/3$. Equation (2.6) bounds the sum of the two selected upper-coordinate positive violations by $2\epsilon_p$. Thus $G\le(146/3)\epsilon_p$, even when one of its terms is negative. Rearranging (10.2) yields

$$
\frac J{10}\le5000V_\pi-L+G
\le5000V_\pi+\frac{149}{3}\epsilon_p+\chi\epsilon_\beta.
\tag{10.19}
$$

Since $149/3+\chi<52$, this proves the first line of (10.17), including zero slack. For $u\in[a,b]$, its nearer endpoint distance is at most $30(u-a)(b-u)$: the farther endpoint distance is at least $1/30$. This proves the second bound. On $[a+d,b-d]$ the tent is at least $d(1/15-d)$, proving (10.18). Both configuration risks and the variation have been evaluated on this one actual stationary table. Configuration TV remains inside its configuration average; a bound only on the marginalized law would not supply (2.6). No supported nonendpoint is needed for these concentration bounds, while any such depths remain in (2.4). $\square$

Concentration of $u$ alone does not identify $Q_x$ with a native endpoint law. The acquired-class invariance used in Proposition 4.1 is not assumed here, so its complete-law endpoint recovery is not inferred for a varying-$u$ table.

**Corollary 10.4 (necessary extracted and clipped concentration for an original observer).** Let $M$ satisfy Definitions 1.1–1.3 for its one fixed finite or countable prior, with $\mu(1),\mu(2)>0$. Use the one common-row extraction on (1.5) of [PAID97, Lemma 14.1], followed by the emission clipping of Citation 2.1, keeping the extracted actual kernels and both rows. Denote its clipped p emission by $\widehat u$ and its variation by $\widehat V_\pi$. Then this same extracted, regenerated regular table satisfies

$$
\begin{aligned}
\widehat{\mathcal C}&\le5000\widehat V_\pi
                         \le5000\mathcal V(M),\\
\pi[(\widehat u-a)(b-\widehat u)]
&\le\frac{31720}{11}e(M)+50000\mathcal V(M).
\end{aligned}
\tag{10.20}
$$

Writing $N_M=31720e(M)/11+50000\mathcal V(M)$, the same table also satisfies $\pi\operatorname{dist}(\widehat u,\{a,b\})\le30N_M$ and, for $0<d\le1/30$, $\pi\{a+d\le\widehat u\le b-d\}\le\min\{1,N_M/[d(1/15-d)]\}$. All supported depths retain their configuration-risk bounds on these same extracted rows.

Proof. The initialized paid-history extraction retains the actual-return statistic on the same Cesaro rows as both phase losses, as established in (9.19). Thus the unclipped extracted variation is at most $\mathcal V(M)$. Scalar clipping is 1-Lipschitz and retains $B,A,\pi,\tau$, so (9.20) gives $\widehat V_\pi\le\mathcal V(M)$. The common-row clipping consequence (2.2), supplied by [CLIP97, Theorem 3.1], bounds both clipped slacks by $61e(M)/11$, simultaneously for every supported depth. Apply Theorem 10.2 and Corollary 10.3 to this one table, and use $520\cdot61=31720$. These extraction and clipping steps require no supported nonendpoint for this conclusion. $\square$

The assertions in (10.20) concern the extracted clipped stationary emissions and their regenerated complete laws. They do not assert the same functional inequality for unclipped emissions outside $[a,b]$, or concentration at every original history. Original transient labels and every positive paid history remain in the suprema defining $e(M)$ and $\mathcal V(M)$; omission from a stationary support removes no original risk obligation. The extraction begins with the original source-independent initialization before the first paid seed Read, not a substituted stationary initialization of the actual observer.

**Mathematical citation 10.5 (source-specific deduction and bounded literature scope).** Theorem 10.2 is `repo-derived` ordinary mathematics. Its supplied source-specific inputs are (2.1), (2.3), the original functional coefficients, and the conserved-parameter cycle certificate (3.7)–(3.8). The new deduction transfers that fixed finite certificate with a Lipschitz parameter potential on the actual joint circulation and bounds the finite-word p-factor changes by its unweighted return variation. Corollary 10.3 reuses the endpoint consequences (2.5)–(2.6), and Corollary 10.4 reuses the initialized common-row extraction and risk-controlled clipping identified in Citation 9.5. Theorem 9.2 already supplies a conservative comparison of complete laws by a repaired table, and Theorem 9.3 consumes its square-root error. Neither result is a premise of the unconditional functional proof above; the extraction consequences (9.19)–(9.20) are used only for the original-observer corollary.

**KARP:** Richard M. Karp, *A Characterization of the Minimum Cycle Mean in a Digraph*, memorandum UCB/ERL M77/47, [original report](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1977/ERL-m-77-47.pdf), Lemma 1 proof, printed p.2. The report reduces its minimum-cycle-mean problem to strongly connected components, then assumes a strongly connected graph; its full Lemma 1 assumes minimum cycle mean zero. The particular intermediate fact used here is its no-negative-cycle path-shortening step: a minimum-weight walk can be taken with fewer than the number of vertices in edges. Sign reversal gives the nonpositive-cycle formulation explicitly proved before (10.11). No minimum-cycle-mean formula, shortest-path algorithm, zero-cycle existence or strong-connectivity premise is transferred to the actual return kernel. The parameter estimate (10.12)–(10.16) and the stopped-source coefficients are not conclusions of that report.

The finite-graph potential, cycle deletion, conditional rounding, product telescoping and stationary cancellation are mature intermediate methods, not separately new general theory. The supplied [CK, Section 4, Theorem 7 and Corollary 8] concerns approximation of TV between two specified initial laws of a labelled Markov chain, rather than the universal joint acquired-return functional (10.1). These are bounded method and source correspondences. The source-specific deduction carries no claim of global literature priority, exhaustive literature coverage or unrestricted optimality.

**Definition 10.6 (original-domain and spatial obligations retained by this necessary test).** Sections 1–2 retain the complete original carrier and fixed COMPLETE cap per observer, the paid parser and four-marker tree, both seeds, the once-sampled shared $K$, actual histories and permissions, the third-write-before-latch rule, held records, both interfaces, complete tails including noncompletion, and the original completion and Stop delivery. In a regular table, the infinite outcomes have mass zero by the same survival bound $4/15$; they are not discarded or used for conditioning. In an original observer, zero or unit synthetic emissions and possible noncompletion are allowed before the supplied clipping comparison. Their actual acquired updates, including edges of zero synthetic probability, remain part of the original contract. The proof constructs no runtime sampler, observable row, posterior port, clock, source query, reset or compensation operation. Original Read, refusal, beta-empty updates, Stop and graft obligations keep their domains wherever applicable, together with the actual clocks, lifetime and every resource account. The extraction and clipping retain their stated comparison scopes and establish no preservation of a prescribed COMPLETE, hard-defect or total-resource budget.

The same-source spatial programme continues to require complete ordered and symmetric mixed traces, both cross blocks, arbitrary joint correlations and actual same-inverse LINEAR compensation, together with its original source, operation, metric, acquisition, recovery, clock and resource correspondences. The common calibration and menu-closure hypotheses of [the internal three-axis interface, Section 10](AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md) and the retained obligations of [GEOM, Definition 78.12] remain separate. Neither endpoint concentration, the eight-vertex proof graph nor an analysis coordinate rank supplies those correspondences or selects physical dimension three. The inequality is a necessary finite-response constraint; it supplies no unrestricted impossibility, attainment, infimum conclusion or fixed-resource improvement.

## 追加锚（本行以下为增补区）
