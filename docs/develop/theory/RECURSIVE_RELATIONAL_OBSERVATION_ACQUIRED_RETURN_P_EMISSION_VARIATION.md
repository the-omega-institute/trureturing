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

## 11. Sharp compatibility constants and a complete-law-flow diagnostic

**Definition 11.1 (same-object hypotheses and notation).** Retain Definitions 1.1–1.3, including the single originally sampled positive integer $K$, the fixed finite or countable prior, both seeds, every paid rejection and partial parse, the full $m=2,d=1,\ell=2,n=4$ control $C_0$, all markers and held records, third-write-before-latch, every finite fourth-segment return, completion and its matching Stop. A regular stationary table means Definition 2.2 on positive finite supports, with its actual acquired kernels $B,A$, rows $\pi,\tau$, emissions $u,v$ and its own complete laws $Q,W$. All quantities below belong to this one table. Write

$$
\begin{gathered}
a=\frac13,\quad b=\frac25,\quad
\chi=\frac{1116529}{806625},\quad
\zeta_0=-\frac{151298}{268875},\\
T_a=\frac{16}{729},\quad q_*=\frac{1944}{390625},\quad
f_x=Q_x(E_p),\quad h_y=W_y(E_\beta),\\
J=\pi[(u-a)(b-u)],\qquad
V_\pi=\sum_{x,y,x'}\pi_xB_{xy}A_{yx'}|u_x-u_{x'}|.
\end{gathered}
\tag{11.1}
$$

Products inside $\pi[\,\cdot\,]$ are coordinatewise. The functional $\mathcal C$ is exactly (10.1). The risk hypotheses, when imposed, are the simultaneous configuration-before-TV bounds (2.4) on these same laws and rows, with nonnegative slacks $\epsilon_p,\epsilon_\beta$ and $\epsilon=\max\{\epsilon_p,\epsilon_\beta\}$. Endpoint-only hypotheses suffice for Corollary 11.3; Proposition 11.4 and Theorem 11.5 also retain every supported-depth bound and a supported nonendpoint.

The local citations **PAID42**, **CLIP42** and **PAIRED42** denote respectively [Effective paid-history certificates](https://github.com/the-omega-institute/trureturing/blob/b58f2009bfa2e7c2f5d084e7f0b5616ffa1fac08/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md), [Risk-controlled emission moment feasibility](https://github.com/the-omega-institute/trureturing/blob/b58f2009bfa2e7c2f5d084e7f0b5616ffa1fac08/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md), and [Paired calibration observability](https://github.com/the-omega-institute/trureturing/blob/b58f2009bfa2e7c2f5d084e7f0b5616ffa1fac08/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md) at that fixed source. The potential, joint stationary cancellation and stopped-product restoration used below are the structure of Theorem 10.2. The following sharpening concerns their numerical estimates.

### 11.1 The sharper stationary estimate

**Theorem 11.2 (81 compatibility on the actual circulation).** Every regular stationary table of Definition 11.1, without a risk hypothesis, satisfies

$$
\begin{aligned}
\pi f-\chi\tau h-\zeta_0
\le{}&106\pi[(b-u)(Q(w_{2,1})-T_a)]\\
&+365\pi[(u-a)(Q(w_{3,1})-q_*)]
-\frac{J}{10}+81V_\pi.
\end{aligned}
\tag{11.2}
$$

Equivalently, $\mathcal C\le81V_\pi$. There is no return-conservation, reversibility, irreducibility, mixing, state-count or stationary-mass-floor assumption.

Proof. Use the stationary unweighted alternating chain of Theorem 10.2,

$$
X_0\xrightarrow{B}Y_0\xrightarrow{A}X_1\xrightarrow{B}Y_1
\xrightarrow{A}\cdots,\qquad X_0\sim\pi,
$$

and set $c_i=u_{X_i}$, $U_i=1-c_i$, $v_i=v_{Y_i}$. The two exact flow identities imply joint stationarity under one $BA$ shift. In particular,

$$
\mathbb E|c_{i+1}-c_i|=V_\pi,\qquad
\mathbb E|c_i-c_0|\le iV_\pi.
\tag{11.3}
$$

This is a chain of acquired kernels used to expand words. Its definition does not condition the original source on an infinite return path.

For fixed $c\in[a,b]$, put $U=1-c$ and use the polynomial $f_c(z)$ of (10.8), here denoted $R(c,z)$:

$$
\begin{aligned}
P&=U(1-z_0)+U^2z_0(1-z_1)+U^3z_0z_1(1-z_2),\\
H&=1-z_0+Uz_0(1-z_1),\\
T&=U^3z_0z_1(1-z_2),\qquad
Z=U^4z_0z_1z_2(1-z_3),\\
R(c,z)&=P-\chi H-\zeta_0
-106(b-c)(T-T_a)-365(c-a)(Z-q_*)
+\frac{(c-a)(b-c)}{10}.
\end{aligned}
\tag{11.4}
$$

For endpoint tuples $z\in\{a,b\}^4$, regard $z$ as the edge from $(z_0,z_1,z_2)$ to $(z_1,z_2,z_3)$. The mean edge weight on each simple directed cycle is exactly (3.7), with $t=15(b-c)$. The complete nineteen-cycle Bernstein certificate (3.7)–(3.8) therefore gives nonpositive total weight on every such cycle, for every $c$. This identification and the path construction are the ones in (10.10)–(10.11); no classification of observer carriers is used.

For each triple $s$, let $\Phi_c(s)$ be the maximum weight of a vertex-simple path starting at $s$, including the empty path and permitting every endpoint. A simple path has at most seven edges. Every closed walk decomposes into simple cycles by cutting at repeated vertices, so its weight is nonpositive. Deleting such a subwalk cannot decrease a path's weight. Prepending an edge to a maximizing path at its terminal vertex and deleting cycles consequently gives

$$
R(c,s\to s')\le\Phi_c(s)-\Phi_c(s').
\tag{11.5}
$$

Here is a sharper parameter estimate than (10.12). On the entire box $z\in[a,b]^4$,

$$
\begin{gathered}
|\partial_cP|\le\frac{262}{225},\quad
|\partial_cH|=z_0(1-z_1)\le\frac4{15},\\
0\le T\le\frac{64}{2025},\quad
|T-T_a|\le\frac{64}{2025},\quad
|\partial_cT|\le\frac{32}{225},\\
0\le Z\le\frac{256}{30375},\quad
|Z-q_*|\le\frac{256}{30375},\quad
|\partial_cZ|\le\frac{512}{10125}.
\end{gathered}
\tag{11.6}
$$

For example the three differentiated terms of $P$ are bounded by $2/3$, $16/45$ and $32/225$, whose sum is $262/225$. The other bounds follow by inserting $U\le2/3$, $z_i\le2/5$ and $1-z_i\le2/3$; both fixed comparison constants lie inside the respective displayed intervals. Since $\chi<7/5$, $b-c,c-a\le1/15$, and the differentiated tent has absolute value at most $1/150$, the product rule gives

$$
\begin{aligned}
|\partial_cR|
&\le\frac{262}{225}+\frac{28}{75}
+\frac{6784}{2025}+\frac{3392}{3375}
+\frac{93440}{30375}+\frac{186880}{151875}
+\frac1{150}\\
&=\frac{620033}{60750}<11.
\end{aligned}
\tag{11.7}
$$

The seven contributions are those of $P$, $\chi H$, the two differentiated $T$ terms, the two differentiated $Z$ terms and the tent. Each path weight is therefore $77$-Lipschitz in $c$. Taking the finite maximum preserves that bound, including at ties:

$$
|\Phi_c(s)-\Phi_d(s)|\le77|c-d|.
\tag{11.8}
$$

Conditionally on the acquired analysis path, independently round each time-position $v_i$ to $\xi_i\in\{a,b\}$ with conditional mean $v_i$. Distinct visits to the same label use distinct proof coins. The polynomial in (11.4) is affine in each $z_i$ separately, so this rounding preserves its conditional expectation, including its correlation with $c_0$. Put $S_i=(\xi_i,\xi_{i+1},\xi_{i+2})$. The rounded joint process is stationary; applying (11.5) and then joint stationarity yields

$$
\begin{aligned}
F^0&:=\mathbb E R(c_0,v_0,v_1,v_2,v_3)
=\mathbb E R(c_0,S_0\to S_1)\\
&\le\mathbb E[\Phi_{c_0}(S_0)-\Phi_{c_0}(S_1)]\\
&=\mathbb E[\Phi_{c_1}(S_1)-\Phi_{c_0}(S_1)]
\le77V_\pi.
\end{aligned}
\tag{11.9}
$$

The equality uses the identical distributions of $(c_0,S_0)$ and $(c_1,S_1)$; it assumes neither conditional stationarity given $c_0$ nor independence of the original emissions. The rounding and future-indexed triples are mathematical auxiliaries, not observer observations or a conditioning on future source events.

It remains to restore the actual stopped products. The exact word expansion (10.4)–(10.5) uses

$$
t_j=\left(\prod_{i=0}^jU_i\right)
\left(\prod_{i=0}^{j-1}v_i\right)(1-v_j),\qquad
H^{\rm act}=1-v_0+v_0U_1(1-v_1).
$$

Its frozen counterparts are $t_j^0=U_0^{j+1}(\prod_{i=0}^{j-1}v_i)(1-v_j)$ and $H^0=1-v_0+v_0U_0(1-v_1)$. When a factor $U_i$ is changed to $U_0$, the remaining $j$ p factors, $j$ suspended-alpha factors and final suspended-beta factor bound its multiplier by $(2/3)(4/15)^j$. Telescoping and (11.3) give

$$
\mathbb E|t_j-t_j^0|
\le\frac23\left(\frac4{15}\right)^j
\frac{j(j+1)}2V_\pi,\qquad
\mathbb E|H^{\rm act}-H^0|\le\frac4{15}V_\pi.
\tag{11.10}
$$

Thus the total error for the three terms of $P$ is at most $8V_\pi/25$, that for $T$ is at most $32V_\pi/225$, and that for $Z$ is at most $256V_\pi/3375$. The root weights still use $c_0$, and are bounded by $106/15$ and $365/15$. Consequently

$$
|\mathcal C-F^0|
\le\left(\frac8{25}+\frac{28}{75}
+\frac{3392}{3375}+\frac{93440}{50625}\right)V_\pi
=\frac{35884}{10125}V_\pi<4V_\pi
\tag{11.11}
$$

when $V_\pi>0$, with equality zero for the bound at $V_\pi=0$. Combining the non-strict bounds $F^0\le77V_\pi$ and $|\mathcal C-F^0|\le4V_\pi$ proves (11.2). The table's emissions, kernels, rows and complete laws have not been modified. Zero entries, reducibility, negative eigenvalues and arbitrarily small positive stationary coordinates require no separate case. $\square$

**Corollary 11.3 (endpoint tent and mean rounding error).** Under the same table's two endpoint configuration-risk bounds in (2.4),

$$
J\le520\epsilon+810V_\pi,\qquad
M:=\pi\operatorname{dist}(u,\{a,b\})
\le15600\epsilon+24300V_\pi.
\tag{11.12}
$$

Proof. The endpoint calibration (2.5) and $C_p-\chi C_\beta-\zeta_0=0$ imply
$\pi f-\chi\tau h-\zeta_0\ge-\epsilon_p-\chi\epsilon_\beta$. The complete coordinate triangle identity (2.6) bounds the sum of the two positive upper-coordinate violations for $w_{2,1},w_{3,1}$ by $2\epsilon_p$. Their nonnegative weights in (11.2) are at most $365/15=73/3$. It follows that

$$
\frac{J}{10}\le\frac{149}{3}\epsilon_p+\chi\epsilon_\beta+81V_\pi
\le52\epsilon+81V_\pi.
\tag{11.13}
$$

Indeed $149/3+\chi<52$. For $d=\operatorname{dist}(c,\{a,b\})$, one has $0\le d\le1/30$ and $(c-a)(b-c)=d(1/15-d)\ge d/30$. Averaging gives $M\le30J$ and hence (11.12). Both calculations use TV before averaging configurations. $\square$

### 11.2 The complete-loss comparison and the original necessity

**Proposition 11.4 (endpoint repair with its actual mean emission error).** Suppose the regular table satisfies (2.4) for every supported depth and the prior supports a nonendpoint. Round $u_x$ to its nearest endpoint $r_x$, with a tie rounded to $a$, and let $M=\pi|u-r|$. There is one finite regular conserved-return comparison table, with at most $2|Y|$ suspended labels, whose own generated complete laws satisfy, for every complete target simultaneously,

$$
D_p\le\frac{15M+4\delta}{11},\qquad
D_\beta\le\frac{6M+6\delta}{11},\qquad
\delta\le15V_\pi+30M.
\tag{11.14}
$$

Here $\delta$ is the original acquired crossing mass between the two endpoint classes, and $D_p,D_\beta$ are configurationwise complete-law comparisons on the rows specified below. In particular,

$$
\frac{2901611\epsilon+4519890V_\pi}{11}
>g=\frac{\eta}{400000},\qquad
\eta=\frac{14219478376}{318644812890625}.
\tag{11.15}
$$

Proof. Let $\mathscr C$ be the occupied classes $C=\{x:r_x=a\}$ and $C=\{x:r_x=b\}$. Define

$$
\delta=\sum_{x,y,x':r_x\ne r_{x'}}\pi_xB_{xy}A_{yx'}.
$$

Since $|r_x-r_{x'}|=(1/15)\mathbf1_{\{r_x\ne r_{x'}\}}$, stationarity of the two p marginals gives

$$
\frac{\delta}{15}
\le\sum_{x,y,x'}\pi_xB_{xy}A_{yx'}
\bigl(|u_x-u_{x'}|+|u_x-r_x|+|u_{x'}-r_{x'}|\bigr)
=V_\pi+2M.
\tag{11.16}
$$

Use exactly the directed repair of (9.7)–(9.13), now on these two classes. Retain only pairs $(y,C)$ with positive mass

$$
\tau^c_{y,C}=\sum_{x\in C}\pi_xB_{xy},\qquad
B^c_{x,(y,C)}=\mathbf1_{\{x\in C\}}B_{xy},\qquad
u_x^c=r_x,\quad v^c_{y,C}=v_y.
\tag{11.17}
$$

Then $\pi B^c=\tau^c$ and $\sum_C\tau^c_{y,C}=\tau_y$. For $x'\in C$ set

$$
d^C_{x'}=\pi_{x'}-\sum_y\tau^c_{y,C}A_{yx'}\ge0,\quad
D_C=\sum_{x'\in C}d^C_{x'},\quad
m_{y,C}=\sum_{x'\notin C}A_{yx'}.
$$

The nonnegativity follows from $\tau^c_{y,C}\le\tau_y$ and $\tau A=\pi$. Direct summation gives

$$
D_C=\sum_y\tau^c_{y,C}m_{y,C},\qquad \sum_CD_C=\delta.
\tag{11.18}
$$

If $D_C>0$, set $A^c_{(y,C),x'}=A_{yx'}+m_{y,C}d^C_{x'}/D_C$ for $x'\in C$, and zero outside $C$. If $D_C=0$, (11.18) gives $m_{y,C}=0$ on every retained row; keep its inside-$C$ entries without division. Every row is nonnegative and sums to one. Its incoming mass at $x'\in C$ equals the old inside-class influx plus $d^C_{x'}$, hence $\tau^cA^c=\pi$. All positive repaired returns stay in $C$ and conserve $u^c$. Moreover,

$$
\operatorname{TV}(A_{y,\cdot},A^c_{(y,C),\cdot})=m_{y,C}.
\tag{11.19}
$$

These are balance identities, without a reversibility or mixing premise.

Generate $Q_x^c,W_{y,C}^c$ from the two repaired phase equations (2.3), using exactly the repaired acquired kernels. Their return survival, like that of the old table, is at most $4/15$; their entire laws normalize with infinite outcomes retained at mass zero. Set

$$
p_x=\operatorname{TV}(Q_x,Q_x^c),\quad
b_{y,C}=\operatorname{TV}(W_y,W_{y,C}^c),\quad
D_p=\sum_x\pi_xp_x,\quad
D_\beta=\sum_{y,C}\tau^c_{y,C}b_{y,C}.
$$

The same complete-law coupling as (9.14)–(9.15), retaining the actual emission error rather than a bin width, gives

$$
p_x\le|u_x-r_x|+\frac23\sum_yB_{xy}b_{y,C(x)},\qquad
b_{y,C}\le\frac25\left(m_{y,C}+\sum_{x'}A^c_{(y,C),x'}p_{x'}\right).
\tag{11.20}
$$

For the first inequality, couple the two Bernoulli emissions, then use their identical $B$ transitions on matched beta. For the second, the suspended emissions agree; a change of successor row costs its TV in (11.19), and a common successor costs $p_{x'}$. Convexity contracts each law mixture. The inequalities hold on finite prefixes and pass to the complete laws by the geometric survival bound, including the infinite outcome. Averaging with the exact new flows gives

$$
D_p\le M+\frac23D_\beta,\qquad
D_\beta\le\frac25(\delta+D_p).
$$

Solving these inequalities gives (11.14). For every normalized target $T_p$ the reverse triangle inequality bounds the absolute change of its configuration loss by $D_p$. At suspension the same argument uses the split row and $\sum_C\tau^c_{y,C}=\tau_y$, giving $D_\beta$. This proves simultaneous comparison for every supported target and every posterior mixture, without replacing configuration risk by marginal-law risk.

By (11.16), both law comparisons are at most $(186M+90V_\pi)/11$: the p bound is at most $(135M+60V_\pi)/11$ and the suspended bound at most $(186M+90V_\pi)/11$. The conserved comparison thus has common supported-depth slack bounded by

$$
\epsilon+\frac{186M+90V_\pi}{11}
\le\frac{2901611\epsilon+4519890V_\pi}{11},
\tag{11.21}
$$

where (11.12) was used in the last step. Theorem 5.1 applies to this one comparison table and requires its common slack to exceed $g$, proving (11.15). Empty endpoint classes and zero deficits were included above.

The comparison is algebraic for real table data. Rational data give rational deficits, rows and repaired entries, so the finite exact-sampling convention of PAID42, Lemma 2.1.1 and Proposition 11.3, applies when a represented comparison is needed. No exact-real sampler follows from the algebraic construction. Neither a prescribed COMPLETE budget nor a hard marginalized-defect budget is preserved. $\square$

**Theorem 11.5 (linear original-observer necessity).** Fix any finite or countable prior with positive masses at depths 1 and 2 and a supported depth $k\ge3$. Every original source-independent finite COMPLETE observer of Definitions 1.1–1.3 satisfies

$$
\frac{176998271}{121}e(M)+\frac{4519890}{11}\mathcal V(M)>g,
\qquad
1500000e(M)+411000\mathcal V(M)>\frac{\eta}{400000}.
\tag{11.22}
$$

Here $\mathcal V(M)$ is exactly the original worst-history acquired-return statistic (9.1). Zero or unit emissions, possible noncompletion, reducible acquired kernels and all finite positive original histories remain allowed.

Proof. Start from the original initialized observer, before the first paid seed Read. PAID42, Lemma 14.1, extracts common rows on the original seed-1, marker-100 fibre, using finite paid rejection histories and the fixed legal suffix $S$ of (1.5). Its histories approaching every supported depth have the same limiting private row $\lambda$ obtained from that original initialization, and appending any fixed $j$ returns gives the row $\lambda(BA)^j$. For a countable prior, the supplier bounds each relative likelihood by a fixed constant times $\mu(i)/\mu(k)$; this summable bound justifies posterior concentration. Every approximant retains all of its paid letters and original control and record updates.

Let $F_x=\sum_{y,x'}B_{xy}A_{yx'}|u_x-u_{x'}|$ for the original, possibly unclipped emissions. Every positive approximating history has row applied to $F$ at most $\mathcal V(M)$ by its definition. Finite-row continuity and then the very same Cesaro subsequence used for both phase risks give

$$
\lambda(BA)^jF\le\mathcal V(M)\quad(j\ge0),\qquad
\pi F\le\mathcal V(M).
\tag{11.23}
$$

Thus the statistic and every supported-depth configuration-loss bound belong to the same extracted table, as in (9.19). No independently chosen row at either interface is substituted. Positive extracted labels are original reachable configurations; transient labels absent from the stationary support remain in the original suprema.

Delete zero-row labels, which cannot be reached from positive-row labels by the nonnegative flow identities. Clip the two emissions to $[a,b]$ and regenerate complete laws with the same $B,A,\pi,\tau$. The initialized common-row clipping consequence (2.2), supplied by CLIP42, Theorem 3.1, gives simultaneous supported-depth slacks with $\epsilon\le61e(M)/11$. Clipping is 1-Lipschitz, so (11.23) also gives $\widehat V_\pi\le\mathcal V(M)$. Proposition 11.4 applied to this one clipped table therefore yields

$$
\frac{2901611(61e(M)/11)+4519890\mathcal V(M)}{11}>g.
$$

Since $2901611\cdot61=176998271$, this is the first inequality of (11.22). Finally $176998271<1500000\cdot121$ and $4519890<411000\cdot11$; both original quantities are nonnegative, so the second inequality follows.

When an original product comparison is used, PAID42, Lemma 2.1.1, retains the full $C_0$ and performs the independent private latch sampling in the original third-completion update after its record write and latch. Both seeds, paid rejections and partial parses, every marker fibre, held registers, every finite return and the matching Stop keep their original transitions and permissions. The actual private rows after that latch are $\pi$ and $\tau^c$ by the repaired flow identities; the same $B^c,A^c$ are used synthetically. For a posterior target $\sum_k\nu_h(k)P_{s,r_k}$, countable convexity is applied inside each configuration's TV before the row average. The current-record maps $I_c$ preserve full tails, completion and Stop. This comparison changes neither the once-sampled source nor the meanings of the original $e(M)$ and $\mathcal V(M)$. It is a necessary comparison, not a construction of small excess or of a common attainer. $\square$

**Corollary 11.6 (amplitude consequence and coefficient non-dominance).** For any sequence of lawful finite COMPLETE observers for one fixed prior as in Theorem 11.5, if $e(M_n)\to0$, then

$$
\liminf_n\mathcal V(M_n)\ge\frac{\eta}{164400000000}.
\tag{11.24}
$$

An exact common conf/conf attainer, if one exists, has the strict inequality $\mathcal V(M)>\eta/164400000000$. The retained Section 9 relation is

$$
\frac{61}{11}e(M)+\frac{19}{11}\sqrt{\mathcal V(M)}>g.
\tag{11.25}
$$

Neither numerical necessary condition uniformly implies the other on the nonnegative coordinate domain.

Proof. Rearrange the second inequality of (11.22) as $\mathcal V(M_n)>(g-1500000e(M_n))/411000$ and pass to the lower limit. Set $e=0$ for an exact attainer. Equation (11.25) is Theorem 9.3 with its unchanged hypotheses and proof.

For coefficient comparison alone, take $V=0$ and $e=11g/122$. The left side of (11.25) is $g/2$, whereas $1500000e>g$. Thus the larger coefficient of $e$ in (11.22) prevents uniform dominance of (11.25). Conversely take $e=0$ and $V=g/822000$. The linear left side is $g/2$, while $(19/11)\sqrt V>g$, since $0<g<1/400000<361/(121\cdot822000)$. These are comparisons of the numerical conditions, not assertions that observers realize these chosen coordinate pairs. Each valid observer must obey both conditions. Their free variation terms remain; neither condition evaluates the unrestricted risk-only infimum. $\square$

### 11.3 Equal complete predictions with different actual return motion

**Definition 11.7 (the two rational six-label tables).** At each phase use labels $(\sigma,i)$ with $\sigma\in\{7/20,23/60\}$ and $i\in\{0,1,2\}$. Put $\pi=\tau=(1/6,\ldots,1/6)$, $B=I$, and

$$
u_{\sigma,0}=\frac13,\quad u_{\sigma,1}=\frac{11}{30},\quad
u_{\sigma,2}=\frac25,\qquad v_{\sigma,i}=\sigma.
\tag{11.26}
$$

There are no cross-block transitions. Within each block choose either

$$
A_0=\begin{pmatrix}
1/2&0&1/2\\0&1&0\\1/2&0&1/2
\end{pmatrix},\qquad
A_1=\begin{pmatrix}
1/3&1/3&1/3\\1/3&1/3&1/3\\1/3&1/3&1/3
\end{pmatrix}.
\tag{11.27}
$$

The subscripts 0 and 1 distinguish the two tables, with the same choice in both blocks. Write $m=11/30$, $q=19/30$, $t_\sigma=q\sigma$.

**Proposition 11.8 (explicit counterexample to prediction-only motion identification).** The two tables of Definition 11.7 are regular stationary and have identical complete phase laws at every corresponding label. Their common indexed paired arrays $f,h$ are both nonconstant. Nevertheless,

$$
V_\pi(A_0)=\frac1{45},\qquad V_\pi(A_1)=\frac4{135}.
\tag{11.28}
$$

Their mean actual-return TV motion of complete p laws equals the respective quantity in (11.28), and therefore also differs.

Proof. Both matrices are doubly stochastic and send $(1/3,11/30,2/5)^\mathsf T$ to $m\mathbf1$. Together with $B=I$ this proves $\pi B=\tau$, $\tau A_s=\pi$ for $s=0,1$. Define a p law $G_\sigma$ by

$$
G_\sigma(w_{j,0})=m t_\sigma^j,\qquad
G_\sigma(w_{j,1})=q(1-\sigma)t_\sigma^j\quad(j\ge0),\qquad
G_\sigma(\infty_p)=0.
\tag{11.29}
$$

These nonnegative masses sum to one, since $m+q(1-\sigma)=1-t_\sigma$ and $t_\sigma<1$. Put

$$
W_\sigma=(1-\sigma)\delta_\beta+\sigma\alpha G_\sigma,\qquad
Q_{\sigma,i}=u_i\delta_\alpha+(1-u_i)\beta W_\sigma.
\tag{11.30}
$$

The geometric masses (11.29) give $G_\sigma=m\delta_\alpha+q\beta W_\sigma$. Since each row of either $A_s$ averages $u$ to $m$, that row's mixture of the laws $Q_{\sigma,i}$ is exactly $G_\sigma$. Equations (11.30) are consequently the two same-update phase equations for both tables, with $W_{\sigma,i}=W_\sigma$. They are their own generated full laws: finite cylinder iteration of the recursions has unique limits, since survival for $L$ returns is at most $(4/15)^L$. Infinite outcomes are retained at mass zero, without completion conditioning.

For clarity the individual complete masses are

$$
\begin{aligned}
Q_{\sigma,i}(w_{0,0})&=u_i,\\
Q_{\sigma,i}(w_{j,0})&=(1-u_i)\sigma m t_\sigma^{j-1}\quad(j\ge1),\\
Q_{\sigma,i}(w_{j,1})&=(1-u_i)(1-\sigma)t_\sigma^j\quad(j\ge0),\\
W_\sigma(\beta)&=1-\sigma,\\
W_\sigma(\alpha w_{j,0})&=\sigma m t_\sigma^j,\\
W_\sigma(\alpha w_{j,1})&=\sigma q(1-\sigma)t_\sigma^j.
\end{aligned}
\tag{11.31}
$$

Thus the arrays are exactly

$$
f_{\sigma,i}=(1-u_i)(1-\sigma)(1+t_\sigma+t_\sigma^2),\qquad
h_{\sigma,i}=(1-\sigma)(1+t_\sigma).
\tag{11.32}
$$

Their rational values can be displayed as follows, with $f_{\sigma,i}=(1-u_i)k_\sigma$:

| $\sigma$ | $t_\sigma$ | $k_\sigma$ | $h_{\sigma,i}$ |
| --- | --- | --- | --- |
| $7/20$ | $133/600$ | $5947357/7200000$ | $9529/12000$ |
| $23/60$ | $437/1800$ | $156050053/194400000$ | $82769/108000$ |

Within either block $f$ varies with the three distinct $u_i$. Across blocks $h$ varies: $h(\sigma)=1-m\sigma-q\sigma^2$ is strictly decreasing for positive $\sigma$. This proves nonconstancy of both full indexed arrays; it does not merely compare their means.

In one block, with the conditional uniform p row, the only nonzero $A_0$ contributions to return variation are $0\to2$ and $2\to0$, each of transition probability $1/2$ and difference $1/15$. Their total is $1/45$. For $A_1$ the six ordered off-diagonal differences are $1/30,1/30,1/15$ in each direction, so their sum is $4/15$ and their uniform edge weight is $1/9$. The total is $4/135$. The two equal block masses preserve those values globally.

Finally $Q_{\sigma,i}-Q_{\sigma,j}=(u_i-u_j)(\delta_\alpha-\beta W_\sigma)$. The two probability laws inside the last parentheses have disjoint supports. Hence

$$
\operatorname{TV}(Q_{\sigma,i},Q_{\sigma,j})=|u_i-u_j|.
\tag{11.33}
$$

Every actual return remains in its block. Weighting (11.33) by $\pi B A_s$ proves the asserted full-law return motion. This equality of the two motion quantities is specific to (11.30), not a general identification of immediate-emission variation and complete-law dispersion. $\square$

### 11.4 The exact two-flow comparison for this pair

**Proposition 11.9 (equal two joint law flows and unequal return law measure).** Use precisely the compatible-flow definition of PAIRED42, Definition 11.2, and its finite-table map (11.24). Both tables of Definition 11.7 induce the same two joint probability measures

$$
\Gamma_B=\frac16\sum_{\sigma,i}\delta_{(Q_{\sigma,i},W_\sigma)},\qquad
\Gamma_A=\frac16\sum_{\sigma,i}\delta_{(W_\sigma,Q_{\sigma,i})}.
\tag{11.34}
$$

They satisfy both of that definition's full residual identities. In contrast, their three-stage actual-return law measures

$$
\Xi_s=\frac16\sum_{\sigma,i,j}(A_s)_{ij}
\delta_{(Q_{\sigma,i},W_\sigma,Q_{\sigma,j})},\qquad s=0,1,
\tag{11.35}
$$

are different. Thus the two-flow quotient preserves both phase-law distributions, both directional one-step law-pair distributions and all configuration losses against every complete target for this pair, but does not determine its actual return motion.

Proof. The laws lie in the descriptor spaces $\mathcal K_p,\mathcal K_\beta$ of PAIRED42, (11.2): they are regular generated laws, whose complete return-tail bounds are $(4/15)^L$ at p and $(2/5)(4/15)^L$ at suspension. The finite-table map uses the unweighted flows $\pi_xB_{xy}$ and $\tau_yA_{yx}$, without synthetic continuation factors. Since $B=I$ and $W_{\sigma,i}=W_\sigma$, its first measure is the displayed $\Gamma_B$. For its second measure, aggregating the repeated input law gives, at $(W_\sigma,Q_{\sigma,j})$, the mass

$$
\sum_i\frac16(A_s)_{ij}=\frac16
$$

for each $s$, by the column sums. This proves equality of both joint measures, not merely equality of their marginals. The six p laws are distinct: $Q(\alpha)$ distinguishes $i$ within a block, and for equal $i$ in different blocks $Q(\beta\beta)=(1-u_i)(1-\sigma)$ distinguishes $\sigma$. The two suspended laws are distinguished by $W_\sigma(\beta)=1-\sigma$. Thus the atom calculation includes every identification in this quotient.

The common marginals are $\nu_p=(1/6)\sum_{\sigma,i}\delta_{Q_{\sigma,i}}$ and $\nu_\beta=(1/2)\sum_\sigma\delta_{W_\sigma}$. The normalized residuals in PAIRED42, (11.3), satisfy

$$
\mathcal R_B(Q_{\sigma,i})=W_\sigma,\qquad
\mathcal R_A(W_\sigma)=G_\sigma=\frac13\sum_iQ_{\sigma,i}.
\tag{11.36}
$$

The first equality makes each integrand of the $B$ residual equation vanish. Conditional on $W_\sigma$, $\Gamma_A$ gives uniform mass to the three $Q_{\sigma,i}$; the second equality makes its conditional residual barycentre exactly $\mathcal R_A(W_\sigma)$. Therefore for every continuous input-descriptor test and every complete-word atom, including the infinite outcomes, both identities (11.7) of PAIRED42 hold. The condition is on the whole descriptor, as that definition requires.

The measures $\Xi_s$ are the actual unweighted $\pi B A_s$ pushforwards, because $B$ carries $Q_{\sigma,i}$ to the suspended label $(\sigma,i)$ before $A_s$ is applied. Their first-two and last-two marginals are respectively (11.34). Fix either $\sigma$. At the triple $(Q_{\sigma,1},W_\sigma,Q_{\sigma,0})$ their masses are zero for $s=0$ and $1/18$ for $s=1$. Hence $\Xi_0\ne\Xi_1$, despite equality of both directional pair measures. Integrating $|u(Q)-u(Q')|$ or $\operatorname{TV}(Q,Q')$ against (11.35) gives the different values (11.28), by (11.33).

For this finite pair the conditionally independent join of the two measures (11.34) is

$$
\frac1{18}\sum_{\sigma,i,j}
\delta_{(Q_{\sigma,i},W_\sigma,Q_{\sigma,j})}=\Xi_1.
\tag{11.37}
$$

Indeed the block has suspended mass $1/2$ and each of its incoming and outgoing conditional law distributions is uniform on three atoms. The join is not $\Xi_0$: in that table the middle suspended label retains information about the incoming p label which its repeated complete law does not distinguish. The finite law-atom realization of PAIRED42, Theorem 11.8, correspondingly has six p-law labels, two suspended-law labels, a deterministic $B$ to the appropriate suspended block, and a uniform $A$ to that block's three p laws. Its flows and laws are (11.34), and its return variation is $4/135$. It supplies the flow-preserving realization promised by that theorem, without preserving $A_0$'s hidden return coupling.

For every complete target $T$, each configuration loss is an integral of $\operatorname{TV}(Q,T)$ or $\operatorname{TV}(W,T)$ against the respective phase marginal. These integrals are equal for the two tables, with TV still inside the integral. All integrals depending on either one of the two directional law pairs are also equal. The return integral depends on (11.35), whose equality was neither asserted by the quotient definition nor implied by its residual identities. This establishes the stated scope on this actual pair, without a general classification of quotient fibres. $\square$

### 11.5 Original initialization, finite representation and applicability

**Proposition 11.10 (the two original represented observers).** Either table of Definition 11.7 has a finite rational original-domain product realization under PAID42, Lemma 2.1.1. At every corresponding original fourth-phase history its private phase row is uniform, its label-indexed complete forecast is (11.30) rendered by the history's own $I_c$, and its configuration risk equals that of the other table. Every label is positively reachable. On the designated fibre,

$$
\mathcal V(M_0)=\frac1{45},\qquad
\mathcal V(M_1)=\frac4{135}.
\tag{11.38}
$$

Proof. Before the third latch retain the full original $C_0$ with fair synthesis. In its third-completion update first perform the complete original record write and latch, then independently sample the uniform six-label p row. Use $B=I$ after p-beta and the chosen $A_s$ after suspended-alpha, in both acquired and synthetic execution. Completing letters clear the private labels and enter their original matching pendingStop; only its unique Stop enters deliveredStop. The projection to $C_0$ is exactly the original update, so induction over original operations preserves both seeds, all paid equal-pair rejections and partial parses, every marker word and prefix, held $B,Q^+,Z$ fields, flags, permissions and all original event blocks. No terminal permits Read. No source reset or resampling of $K$ occurs.

At the first fourth p cut the label row is uniform and independent of the acquired word. At a p-beta cut $B$ keeps it uniform; at a suspended-alpha cut either doubly stochastic $A_s$ keeps it uniform. Conditional on any fixed acquired history, the next actual source letter is independent of the private configuration: the source-independent sampler and updates use private randomness independent of the single $K$ and its letters. Thus actual letters do not reweight private labels by their synthetic emissions. Induction proves the same uniform rows after every finite legal return, on every original record fibre and for either seed. Each of the six labels consequently has probability $1/6$ at every applicable phase cut and is reachable.

The same-update recursions proved in Proposition 11.8 give the raw phase laws from every such label; applying $I_c$ inserts precisely that configuration's future records, completion and Stop, and preserves TV. The original target at history $h$ remains the same posterior mixture (1.2), with its paid rejection and partial-parse counts. Uniform rows and equality of the individual laws make the two observers' configuration-averaged TV losses equal at every fourth-phase history, for any finite or countable prior. Before the latch the two products use the same fair emissions and the same latch row, followed by equal corresponding fourth-phase laws; their corresponding pre-latch decoded laws also agree. The original terminal laws agree as well.

The conditional actual return probability given a designated-fibre history is $\sum_k\nu_h(k)r_k(1-r_k)>0$ and is independent of its private label. It cancels when conditioning on that return, as in Definition 9.1. The uniform p row and kernels in (11.27) therefore give the respective constant values (11.28) at every such history. Taking the full original history supremum proves (11.38), rather than replacing that supremum by an arbitrarily chosen stationary initialization.

All primitive probabilities, including pre-latch fairness, the uniform latch and both stochastic updates, have denominators dividing 60. One exact sampler draws six fresh independent fair bits as a candidate integer in $\{0,\ldots,63\}$, rejects values at least 60, and assigns accepted integers by finite cumulative thresholds. Each represented row has integer counts summing to 60; this includes rows with zero entries and deterministic rows. Acceptance has probability $15/16$, so the service returns almost surely. Rejections reuse the same finite candidate storage and cursor without a persistent retry count. Use independent emission and update service bits where the synthetic joint transition requires them.

The installed tables and thresholds, phase and label addresses, sampler candidate and cursor, program counter, numerical representation, workspace, event and output cursors, all service microstates and all persistent randomness belong to COMPLETE, together with $C_0$. Internal service states carry the conditional continuation of that same finite program and add no original Read cut or permission. Acquired and synthetic updates use exactly the same represented row sampler. No random tape, readable probability row, posterior, acquired-age counter, source query or external clock is supplied. Sampling work, fresh bits, synthesis, output, installed description and actual paid source Reads are all charged; arbitrarily many possible sampler rejections and actual returns give no finite worst-case work bound. This discharges the rational-sampler hypotheses without interpreting six labels as the total COMPLETE count. $\square$

**Mathematical citation 11.11 (attribution and precise limits).** The sharp constants in (11.2), (11.12) and (11.22), and the exact pair in (11.26)–(11.38), are source-specific `repo-derived` ordinary mathematical consequences. Theorem 10.2 already supplies the varying-parameter potential, stationary cancellation and stopped-product restoration with $5000V_\pi$; Theorem 11.2 sharpens their estimates. Section 3 supplies the finite cycle certificate, Citation 2.3 the endpoint event and coordinate-box consequences, Section 9 the directed repair and initialized extraction of the return statistic, Theorem 5.1 the conserved-class gap, and PAID42 and CLIP42 the original product realization, common-row extraction and clipping hypotheses. Cycle deletion, finite maxima of Lipschitz functions, product telescoping, mean-preserving independent rounding, maximal coupling and the TV triangle identity are mature intermediate methods, with the bounded primary correspondence already given in Citation 10.5 and KARP there. No new general potential, realization or coupling theorem is attributed to this chapter.

PAIRED42, Section 4, recovers emissions and complete laws from the indexed paired arrays when $B,A$ are prescribed and its unprojected completion equations hold. The pair above changes $A$; it is therefore consistent with that inverse. PAIRED42, Chapter 11, uses two full joint law-flow measures and conditional residual barycentres, which are stronger data than marginal law equality. Proposition 11.9 establishes equality of those stronger data directly for this pair; it also exhibits the three-stage law measure they fail to determine. Equality of marginal complete-law dispersion or event readouts alone would not have justified that conclusion. Immediate-emission variation, complete-law return motion, phase-law dispersion, event ranges and suspended-to-p descent remain distinct functionals; the special identity (11.33) does not identify them in general.

The two tables are diagnostics, with nonconstant laws and arrays, and are not asserted to satisfy the common endpoint midpoint means or every full endpoint/interior risk face at zero excess. They supply no optimizer or vanishing-excess construction. The inequalities are necessary relations on the same acquired table or the same original observer; their terms have not been independently optimized. Neither $81$ nor the linear amplitude consequence removes the unconstrained return-variation term, evaluates an unrestricted risk-only separation, or establishes common attainment. Definition 9.6's finite exact attainer, unattained zero infimum and positive unrestricted gap alternatives, together with the original fixed-resource questions, remain unresolved by this chapter. Algebraic real comparison tables and finitely represented effective observers retain their separate domains and all original sampling and resource obligations.

## 追加锚（本行以下为增补区）

## 12. Prescribed actual-return regeneration and its joint loss consumer

**Definition 12.1 (the prescribed complete-law triple).** Use the complete countable carriers $\Omega_p,\Omega_\beta$, including their infinite noncompletion outcomes, and the convex compact TV spaces $\mathcal K_p,\mathcal K_\beta$ of [PAIRED, Section 11.1 and Lemma 11.1](RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md). Retain $a=1/3$, $b=2/5$, $\lambda=4/15$, $u(Q)=Q(\alpha)$, $v(W)=1-W(\beta)$ and the normalized residual maps $\mathcal R_B,\mathcal R_A$ in that section. Their domains are these compact spaces; their codomains are the full opposite probability simplices, without an assumption that every residual belongs to the opposite compact space.

An admissible prescribed return measure is a Borel probability $\Xi$ on $\mathcal K_p\times\mathcal K_\beta\times\mathcal K_p$, with coordinates $(Q,W,Q')$, such that

$$
\Xi_1=\Xi_3=\nu_p,\qquad \Xi_2=\nu_\beta,\qquad
\mathbb E_\Xi[W\mid Q]=\mathcal R_B(Q),\qquad
\mathbb E_\Xi[Q'\mid Q,W]=\mathcal R_A(W).
\tag{12.1}
$$

Each conditional equality is an equality of complete measures, or equivalently of every coordinate of the countable carrier almost surely. The second equality conditions on the whole incoming pair. All marginals and expectations are unweighted acquired ones. Set

$$
\mathcal L_p^\Xi(T)=\int\operatorname{TV}(Q,T)\,d\nu_p(Q),\qquad
\mathcal L_\beta^\Xi(T)=\int\operatorname{TV}(W,T)\,d\nu_\beta(W),\qquad
V_\Xi=\int|u(Q)-u(Q')|\,d\Xi.
\tag{12.2}
$$

Targets are arbitrary normalized complete probability laws at their respective phases and may charge noncompletion. TV is half the $\ell^1$ distance and remains inside the configuration integral. On triples use the cost

$$
d_\Sigma((Q,W,Q'),(q,w,q'))
 =\operatorname{TV}(Q,q)+\operatorname{TV}(W,w)
    +\operatorname{TV}(Q',q').
\tag{12.3}
$$

A regular finite table $F$ means Definition 2.2 with its own generated complete laws $Q_x^F,W_y^F$. Its actual triple is

$$
\Xi_F=\sum_{x,y,k}\pi_xB_{xy}A_{yk}
       \delta_{(Q_x^F,W_y^F,Q_k^F)}.
\tag{12.4}
$$

The claim of approximation below concerns a coupling cost (12.3), not the outer TV distance between probability measures on the descriptor product. The first-two and last-two projections of an admissible $\Xi$ form a compatible pair of PAIRED, Definition 11.2: the first equation in (12.1) supplies its $B$ equation, and conditioning the second equation further on $W$ supplies its $A$ equation. These projections need not determine $\Xi$.

**Theorem 12.2 (exact finite realization of each prescribed atomic triple).** Every admissible $\Xi$ with $N$ positive atoms is exactly $\Xi_F$ for a finite regular table with real entries, at most $N$ p labels and at most $N$ suspended labels. Its generated phase laws and its two configuration losses are exactly those of $\Xi$. This is an algebraic real-table assertion. An effective original observer additionally requires permitted finitely represented exact samplers for the latch row, both updates and the emissions; arbitrary real entries do not supply such samplers.

**Proof.** List the distinct p-law atoms as $q_i$ and the distinct suspended-law atoms as $w_j$. Equality of the first and third marginals ensures that the same p list suffices at both ends. Put

$$
t_{ijk}=\Xi\{(q_i,w_j,q_k)\},\qquad
\pi_i=\sum_{j,k}t_{ijk}=\sum_{r,j}t_{rji},\qquad
\tau_{ij}=\sum_k t_{ijk}.
\tag{12.5}
$$

Retain the p labels with $\pi_i>0$ and the suspended labels $y=(i,j)$ with $\tau_{ij}>0$. All subsequent suspended-label sums omit deleted pairs. The suspended label retains the incoming p index even when different labels have the same complete law $w_j$. Define

$$
B_{i,(r,j)}=\mathbf1_{\{r=i\}}\frac{\tau_{ij}}{\pi_i},
\qquad
A_{(i,j),k}=\frac{t_{ijk}}{\tau_{ij}},
\qquad
u_i=u(q_i),\quad v_{ij}=v(w_j).
\tag{12.6}
$$

All divisions are on positive rows. Zero rows have no incident positive flow and are deleted without a transition into a deleted label. Direct summation proves that the rows are stochastic,

$$
\pi B=\tau,\qquad \tau A=\pi,\qquad
\pi_iB_{i,(i,j)}A_{(i,j),k}=t_{ijk}.
\tag{12.7}
$$

The two conditional equalities of (12.1), tested at these atoms, give

$$
\sum_jB_{i,(i,j)}w_j=\mathcal R_B(q_i),\qquad
\sum_kA_{(i,j),k}q_k=\mathcal R_A(w_j).
\tag{12.8}
$$

The second equality uses the atom $(q_i,w_j)$, not just $w_j$. Expanding the residual definitions turns (12.8) into the two complete recursions (2.3) for $q_i,w_j$. The normalized own-law generation and uniqueness argument in PAIRED, (11.19)–(11.20), applies with these finite carriers: the maximal phase distances of two solutions obey $z_p\le(2/3)z_\beta$ and $z_\beta\le(2/5)z_p$. Its two-step factor is $4/15<1$, independently of reducibility or periodicity. Therefore the atoms are the table's own complete laws, including the infinite outcomes at mass zero. Equation (12.7) now gives $\Xi_F=\Xi$. There are at most $N$ distinct first-coordinate atoms and at most $N$ positive incoming pairs, proving the label bounds.

The conditional identities also survive collisions of generated descriptors in this and subsequent constructions. In fact, in any regular finite table sample $(X,Y,X')$ with probability $\pi_xB_{xy}A_{yk}$. Its complete recursions give, coordinatewise,

$$
\mathbb E[W_Y^F\mid X]=\mathcal R_B(Q_X^F),\qquad
\mathbb E[Q_{X'}^F\mid X,Y]=\mathcal R_A(W_Y^F).
\tag{12.9}
$$

Conditioning the first identity on $Q_X^F$, and the second on $(Q_X^F,W_Y^F)$, proves (12.1) for its descriptor pushforward. The right sides are functions of exactly the descriptors conditioned upon. Thus a collision only mixes equal right sides, and does not invalidate either identity. The first and third marginals agree by $\tau A=\pi$. This argument identifies descriptors after generation; it does not merge private labels or change an update row.

For the specific diagnostic in Proposition 11.9, each $\Xi_s$ in (11.35) is admissible even for the stronger incoming-pair condition. At $(Q_{\sigma,i},W_\sigma)$ the outgoing barycentre is $G_\sigma=\mathcal R_A(W_\sigma)$ for each row of $A_s$, by Proposition 11.8, while $\mathcal R_B(Q_{\sigma,i})=W_\sigma$. In (12.5)–(12.6) its p index is $(\sigma,i)$ and its suspended index is the retained pair $((\sigma,i),\sigma)$. Thus $\pi_i=\tau_{i,\sigma}=1/6$, $B$ is deterministic to this retained label, and its outgoing row is exactly the original row of $A_s$. For $s=0$ the construction therefore returns $\Xi_0$, and for $s=1$ it returns $\Xi_1$, with the corresponding own laws (11.30).

Within either block the return variations are respectively

$$
\frac13\left(\frac12+\frac12\right)\frac1{15}
 =\frac1{45},\qquad
\frac19\,2\left(\frac1{30}+\frac1{30}+\frac1{15}\right)
 =\frac4{135}.
\tag{12.10}
$$

The two block masses are $1/2$, so these values hold globally. The two directional flows, complete phase-law distributions and losses against every target are still the equal quantities of Proposition 11.9. In particular the input $\Xi_0$ has not been replaced by the independent join (11.37), which would return $\Xi_1$. The retained suspended labels are precisely what distinguishes these two exact constructions. $\square$

**Theorem 12.3 (finite real regeneration of an arbitrary prescribed triple).** Let $\Xi$ be any admissible Borel return measure and $0<h\le1$. Put $s=\min\{h,1/15\}$. There is one finite regular table $F_h$ whose actual generated triple satisfies (12.1), whose first and third marginals agree exactly, and which has a coupling with $\Xi$ satisfying

$$
\mathbb E d_\Sigma\le \frac{47}{11}h+\frac{15}{2}hs
 \le\frac{105}{22}h.
\tag{12.11}
$$

For every complete target simultaneously, its own configuration losses satisfy

$$
\left|\mathcal L_p^{\Xi_{F_h}}(T)-\mathcal L_p^\Xi(T)\right|
 \le\frac{15}{11}h+\frac52hs,\qquad
\left|\mathcal L_\beta^{\Xi_{F_h}}(T)-\mathcal L_\beta^\Xi(T)\right|
 \le\frac{17}{11}h+\frac52hs,
\tag{12.12}
$$

and its return variation satisfies $|V_{\Xi_{F_h}}-V_\Xi|\le s$. Constants are independent of the target, positive row masses and label counts.

**Proof.** By compactness, take finite Borel partitions $(C_i)$ of $\mathcal K_p$ and $(D_j)$ of $\mathcal K_\beta$ with TV diameter at most $h$, using finite $h/2$ covers and disjointifying them in order. Use exactly the same p partition for $Q$ and $Q'$. Set

$$
\begin{gathered}
t_{ijk}=\Xi(C_i\times D_j\times C_k),\qquad
\pi_i=\nu_p(C_i),\quad \tau_{ij}=\sum_k t_{ijk},\\
q_i=\mathbb E[Q\mid Q\in C_i],\qquad
w_{ij}=\mathbb E[W\mid Q\in C_i,\ W\in D_j].
\end{gathered}
\tag{12.13}
$$

Keep only $\pi_i>0$ and $\tau_{ij}>0$, and use (12.6) for $B,A$, now with $u_i=u(q_i)$ and $v_{ij}=v(w_{ij})$. Both flow identities and (12.7) hold as before. All centroids are complete probability laws in the respective convex compact spaces. TV convexity gives

$$
\operatorname{TV}(Q,q_i)\le h\quad(Q\in C_i),\qquad
\operatorname{TV}(W,w_{ij})\le h
\quad\text{on }C_i\times D_j\times\mathcal K_p.
\tag{12.14}
$$

The same bound holds for $Q'\in C_k$ and $q_k$. Equality of the first and third marginals is used here to identify their cell centroid, rather than selecting a different third-coordinate approximation.

We use the elementary covariance estimate inside this proof. If a real random variable $e$ has range width at most $s$, and a family of probability laws $H$ has TV diameter at most $D$, then

$$
\left\|\mathbb E[(e-\mathbb Ee)H]\right\|_{\rm TV}
 \le \frac{sD}{4}.
\tag{12.15}
$$

The signed measure has mass zero, so its norm is half its $\ell^1$ norm. Indeed $c=\mathbb E(e-\mathbb Ee)_+=\mathbb E(e-\mathbb Ee)_-=\frac12\mathbb E|e-\mathbb Ee|\le s/4$, by the scalar chord bound used in PAIRED, (11.16). If $c>0$, the signed measure is $c(H_+-H_-)$ for two weighted barycentres of $H$. Their TV distance is at most $D$, by integrating the pairwise diameter bound. If $c=0$ the measure vanishes. This proves (12.15), including conditional versions.

Write $H_B=\mathcal R_B(Q)$. On $C_i$ its TV diameter is at most $(10/3)h$ by PAIRED, (11.5), and the range width of $u(Q)$ is at most $s$. The first equation in (12.1) gives

$$
\sum_jB_{i,(i,j)}w_{ij}
 =\mathbb E[W\mid C_i]=\mathbb E[H_B\mid C_i].
$$

Averaging $Q=u(Q)\delta_\alpha+(1-u(Q))\beta H_B$ and subtracting the proposed centroid recursion leaves precisely the prefixed covariance of $1-u(Q)$ and $H_B$. Hence

$$
e_p:=\max_i\operatorname{TV}
 \left(q_i,u_i\delta_\alpha+(1-u_i)\beta
                   \sum_jB_{i,(i,j)}w_{ij}\right)
 \le\frac56hs.
\tag{12.16}
$$

For a retained event $E_{ij}=\{Q\in C_i,W\in D_j\}$ put $H_A=\mathcal R_A(W)$. The second equation in (12.1) gives

$$
\mathbb E[Q'\mid E_{ij}]=\mathbb E[H_A\mid E_{ij}],\qquad
\sum_k A_{(i,j),k}q_k
 =\mathbb E[q_{c(Q')}\mid E_{ij}],
\tag{12.17}
$$

where $c(Q')$ is its p-cell index. The difference between the two right-hand means has TV at most $h$, by (12.14). On $E_{ij}$ the range width of $v(W)$ is at most $s$ and the TV diameter of $H_A$ is at most $6h$. Subtracting the proposed recursion from
$w_{ij}=(1-v_{ij})\delta_\beta+\alpha\mathbb E[v(W)H_A\mid E_{ij}]$
leaves the covariance of $v(W),H_A$, plus $v_{ij}$ times the difference in (12.17). Thus

$$
e_\beta:=\max_{i,j}\operatorname{TV}
 \left(w_{ij},(1-v_{ij})\delta_\beta
                +v_{ij}\alpha\sum_kA_{(i,j),k}q_k\right)
 \le\frac25h+\frac32hs.
\tag{12.18}
$$

This step uses the actual joint restriction $E_{ij}$. Replacing it by conditioning only on $D_j$ would not prove (12.17). Both covariance estimates take place in the full residual simplices; no opposite-compact-space assertion about arbitrary residuals has entered.

Let $q_i^g,w_{ij}^g$ be the laws actually generated by this table. Reuse the normalized stopping construction in PAIRED, (11.19): from p its complete return tail is at most $\lambda^L$, and from suspension it is at most $b\lambda^L$. Noncompletion remains present at zero mass. Comparing its exact recursions with (12.16)–(12.18), and setting
$d_p=\max_i\operatorname{TV}(q_i,q_i^g)$ and
$d_\beta=\max_{i,j}\operatorname{TV}(w_{ij},w_{ij}^g)$, gives

$$
d_p\le e_p+\frac23d_\beta,\qquad
d_\beta\le e_\beta+\frac25d_p.
$$

Since $1-(2/3)(2/5)=11/15$, substitution yields

$$
d_p\le\frac4{11}h+\frac52hs,\qquad
d_\beta\le\frac6{11}h+\frac52hs.
\tag{12.19}
$$

The centroids were not assumed to solve the recursions, and it is these regenerated laws that form the decoder.

Map a sampled triple in $C_i\times D_j\times C_k$ to
$(q_i^g,w_{ij}^g,q_k^g)$, defining the map arbitrarily on discarded null cells. Its pushforward has mass $t_{ijk}$ on these generated label triples, and (12.7) proves that it is exactly $\Xi_{F_h}$, even if some generated descriptors collide. It is not a separately chosen join of its two flows. Equation (12.9) proves its exact descriptor-conditional identities. By (12.14) and (12.19), this coupling costs at most

$$
3h+2d_p+d_\beta
 \le\frac{47}{11}h+\frac{15}{2}hs.
$$

Since $s\le1/15$, this proves (12.11). For each target apply the reverse triangle inequality to each sampled configuration before integration. The p and suspended errors are at most $h+d_p$ and $h+d_\beta$, respectively, proving (12.12). This does not substitute the TV loss of a centroid for the average TV loss of the descriptors in its cell.

Finally, $u(q_i^g)=u_i$ by its recursion. Under the normalized p marginal on $C_i$, the scalar chord bound gives $\mathbb E|u(Q)-u_i|\le s/2$. The same statement holds for $Q'$ on its corresponding cell, because their marginals agree. Therefore

$$
\begin{aligned}
|V_{\Xi_{F_h}}-V_\Xi|
 &\le\mathbb E\bigl(|u(Q)-u_{c(Q)}|
                       +|u(Q')-u_{c(Q')}|\bigr)
 \le s.
\end{aligned}
\tag{12.20}
$$

All partitions, masses and centroids are mathematical construction data. No availability of their exact computation from an unspecified $\Xi$ is asserted. $\square$

**Proposition 12.4 (rational closure retaining every middle edge label).** Let $F$ be either table constructed in Theorems 12.2–12.3, with balanced probability tensor $t_{ijk}$, incoming-pair labels $(i,j)$, and emissions in $[a,b]$. For every $0<\delta\le1$ and $\rho>0$ there is a rational balanced tensor $t^r$ with exactly the same positive labelled support, and a rational regular table $F^r$ of the same label shape, such that

$$
\operatorname{TV}(t,t^r)\le\delta,\qquad
\max_i|u_i-u_i^r|\le\rho,\qquad
\max_{i,j}|v_{ij}-v_{ij}^r|\le\rho.
\tag{12.21}
$$

It uses (12.6) with the new tensor, not independent rounded update rows. Its own actual triple is admissible. There is a coupling of $\Xi_F,\Xi_{F^r}$ with

$$
\mathbb E d_\Sigma\le\frac{71\rho+109\delta}{11}.
\tag{12.22}
$$

For every complete target simultaneously,

$$
\begin{aligned}
|\mathcal L_p^{\Xi_{F^r}}(T)-\mathcal L_p^{\Xi_F}(T)|
 &\le\frac{25\rho+39\delta}{11},\\
|\mathcal L_\beta^{\Xi_{F^r}}(T)-\mathcal L_\beta^{\Xi_F}(T)|
 &\le\frac{21\rho+31\delta}{11},\\
|V_{\Xi_{F^r}}-V_{\Xi_F}|&\le2\rho+\frac{\delta}{15}.
\end{aligned}
\tag{12.23}
$$

These bounds contain no inverse minimal positive row mass.

**Proof.** Regard each positive $t_{ijk}$ as a directed edge $i\to k$ bearing its middle label $j$. Parallel edges with different $j$ remain different edges. The equality of the first and third marginals is exactly balance at every vertex. The finite cycle deletion used in PAIRED, Lemma 11.6, applies to this labelled multigraph, including loops. Follow positive edges until a vertex repeats; balance prevents a dead end. Subtract the smallest edge mass on the resulting simple cycle. At least one positive edge disappears and balance remains. Repetition terminates after at most $|\operatorname{supp}t|$ subtractions, giving

$$
t=\sum_{c=1}^{M}w_c z_c,\qquad
w_c>0,\quad \sum_cw_c=1,\quad
z_c=\frac1{\ell_c}\mathbf1_{\{\text{labelled edges of cycle }c\}},
\quad M\le|\operatorname{supp}t|.
\tag{12.24}
$$

Indeed, if the subtracted edge amount is $h_c$, its contribution to total mass is $w_c=\ell_ch_c$. Every $z_c$ is a rational balanced probability tensor on the original labelled edges. This argument needs no irreducibility, recurrence estimate or inverse stationary mass; reducible closed classes are handled by the same deletion.

Choose an integer $D\ge M/\delta$ and define

$$
n_c=\lfloor Dw_c\rfloor+1,\qquad
N=\sum_cn_c,\qquad r_c=n_c/N,\qquad
t^r=\sum_cr_c z_c.
\tag{12.25}
$$

For $b_c=n_c-Dw_c$ one has $0<b_c\le1$. With $S_0=\sum_cb_c\le M$, $N=D+S_0$ and

$$
\operatorname{TV}(w,r)
 =\frac1{2(D+S_0)}\sum_c|b_c-S_0w_c|
 \le\frac{S_0}{D+S_0}\le\frac MD\le\delta.
$$

Contraction through the finite probability kernel $c\mapsto z_c$ proves the first part of (12.21). Every $r_c$ is positive, so the positive edge support is exactly unchanged. In particular both end marginals $\pi^r$ coincide, every retained $\tau_{ij}^r$ is positive, and (12.6) gives rational stochastic $B^r,A^r$ satisfying both balances exactly. The label $j$ has not been summed away in (12.24). Performing this construction on $\sum_jt_{ijk}$ alone would not determine, and need not approximate, the prescribed triple.

Choose an integer $H$ with $1/(15H)\le\rho$ and round each emission downward on the grid with denominator $15H$ between $5H/(15H)=a$ and $6H/(15H)=b$. This proves the remaining parts of (12.21), with both endpoints retained.

We need an average conditional-row estimate. If $f_{xy},g_{xy}$ are two probability arrays with the same positive row support and row masses $p_x,p_x^r$, then

$$
\begin{aligned}
\sum_xp_x\operatorname{TV}
 \left(\frac{f_{x,\cdot}}{p_x},
       \frac{g_{x,\cdot}}{p_x^r}\right)
 &=\frac12\sum_{x,y}
       \left|f_{xy}-\frac{p_x}{p_x^r}g_{xy}\right|\\
 &\le\operatorname{TV}(f,g)+\operatorname{TV}(p,p^r)
 \le2\operatorname{TV}(f,g).
\end{aligned}
\tag{12.26}
$$

In the middle inequality the added scaling term has $\ell^1$ norm
$\sum_x|p_x-p_x^r|$; there is no division bound by a small row mass. For $B$, the joint array is the pushforward of $t$ to $(i,(i,j))$, with masses $\tau_{ij}$. For $A$, it is the pushforward to $((i,j),k)$, with masses $t_{ijk}$. Thus (12.21) and contraction give

$$
\sum_i\pi_i\operatorname{TV}(B_i,B_i^r)\le2\delta,\qquad
\sum_{i,j}\tau_{ij}\operatorname{TV}(A_{ij},A_{ij}^r)\le2\delta,
\quad
\operatorname{TV}(\pi,\pi^r),\operatorname{TV}(\tau,\tau^r)\le\delta.
\tag{12.27}
$$

Let $q_i^g,w_{ij}^g$ and $q_i^r,w_{ij}^r$ be the two tables' own normalized complete laws. Set

$$
X=\sum_i\pi_i\operatorname{TV}(q_i^g,q_i^r),\qquad
Y=\sum_{i,j}\tau_{ij}\operatorname{TV}(w_{ij}^g,w_{ij}^r).
$$

Changing one Bernoulli emission costs at most $\rho$. Compare the two successor mixtures first with the old row and changed laws, and then with the changed row and new laws. TV convexity gives the pointwise bounds

$$
\begin{aligned}
\operatorname{TV}(q_i^g,q_i^r)
 &\le\rho+\frac23
   \left(\sum_jB_{i,(i,j)}\operatorname{TV}(w_{ij}^g,w_{ij}^r)
                       +\operatorname{TV}(B_i,B_i^r)\right),\\
\operatorname{TV}(w_{ij}^g,w_{ij}^r)
 &\le\rho+\frac25
   \left(\sum_kA_{(i,j),k}\operatorname{TV}(q_k^g,q_k^r)
                       +\operatorname{TV}(A_{ij},A_{ij}^r)\right).
\end{aligned}
$$

Averaging uses the old exact balances, not a changed row requiring a new mass comparison. Equations (12.27) therefore imply

$$
X\le\rho+\frac23Y+\frac43\delta,\qquad
Y\le\rho+\frac25X+\frac45\delta.
$$

Solving with factor $11/15$ yields

$$
X\le\frac{25\rho+28\delta}{11},\qquad
Y\le\frac{21\rho+20\delta}{11}.
\tag{12.28}
$$

The complete stopping construction justifies these comparisons on the normalized full laws, including noncompletion, rather than only a truncated prefix.

On an old label triple with law $t$, changing its three descriptors costs on average $2X+Y$: both p marginals are $\pi$ and the middle marginal is $\tau$. Couple the label probabilities $t,t^r$ maximally. The unmatched probability is at most $\delta$, and the cost (12.3) between any two descriptor triples is at most $3$. Thus a coupling between the two generated triples costs at most $2X+Y+3\delta$, which is (12.22). This construction remains valid under descriptor collisions, since label triples are coupled before their pushforward.

For a fixed target, the loss-wise reverse triangle inequality gives $X$ or $Y$, and replacing the row by its new row adds at most $\delta$, because the remaining loss function takes values in $[0,1]$. This proves the first two bounds of (12.23). Finally the own p emissions equal the installed $u_i,u_i^r$. On a fixed label triple, the change in $|u_i-u_k|$ is at most $2\rho$; the new function $|u_i^r-u_k^r|$ lies in $[0,1/15]$, so changing $t$ to $t^r$ adds at most $\delta/15$. This proves the last bound. Its own descriptor identities follow from (12.9), with no injectivity condition. $\square$

**Corollary 12.5 (finite rational prescribed-return approximation with evaluated constants).** For every admissible Borel $\Xi$ and every $0<h\le1$, there is a finite rational regular table $F_h^r$ and a coupling of its own actual triple with $\Xi$ such that

$$
\mathbb E d_\Sigma\le\frac{543}{110}h<5h.
\tag{12.29}
$$

For all complete targets simultaneously,

$$
\begin{aligned}
|\mathcal L_p^{\Xi_{F_h^r}}(T)-\mathcal L_p^\Xi(T)|
 &\le C_p h,\qquad C_p=\frac{2621}{1650}<\frac85,\\
|\mathcal L_\beta^{\Xi_{F_h^r}}(T)-\mathcal L_\beta^\Xi(T)|
 &\le C_\beta h,\qquad C_\beta=\frac{2903}{1650}<\frac95,\\
|V_{\Xi_{F_h^r}}-V_\Xi|
 &\le C_Vh,\qquad C_V=\frac{1531}{1500}.
\end{aligned}
\tag{12.30}
$$

Every generated triple satisfies (12.1) exactly, with exactly equal first and third unweighted marginals. These marginals may differ from $\nu_p$.

**Proof.** Apply Theorem 12.3 and Proposition 12.4 with $\delta=\rho=h/100$. Glue their couplings through the finite old label triple; conditional restrictions to its finitely many positive cells give such a gluing directly. The cost is at most

$$
\frac{105}{22}h+\frac{180}{1100}h
 =\frac{543}{110}h.
$$

Since $s\le1/15$, the two real loss bounds in (12.12) are at most $101h/66$ and $113h/66$. Adding respectively $64h/1100$ and $52h/1100$ gives exactly $2621h/1650$ and $2903h/1650$. Equation (12.20), $s\le h$, and the last bound of (12.23) give
$h+2h/100+h/1500=1531h/1500$ for variation.

Balance, generation and (12.9) prove the exact constraints after rationalization. The coupling costs tend to zero on the compact descriptor product, hence give weak convergence to this prescribed $\Xi$. They also control the entire triple, rather than only its two projections. Outer TV convergence is neither needed nor implied: if $\Xi$ is nonatomic, each finite triple law is supported on a finite set of $\Xi$-mass zero and its outer TV distance from $\Xi$ is one. The quantifier is existence of a finite rational table for each $\Xi,h$, not an algorithm extracting it from an unrepresented Borel measure. $\square$

**Proposition 12.6 (original-domain installation under the exact sampling bridge).** A finite table in Theorems 12.2–12.3 or Corollary 12.5 admits an original-domain represented installation if its latch row, acquired kernels and emissions admit permitted finite exact sampler services: at each allowed entrance the returned conditional distribution is the specified row, the service uses source-independent randomness, returns almost surely and restores a fixed canonical service workspace at the original operation cut. Finite rational data satisfy this premise under the existing fresh private fair-bit convention of [PAID, Proposition 11.3](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md), PAIRED, Corollary 11.7, and Proposition 11.10 above. Its original-domain adapter is PAID, Lemma 2.1.1, and PAIRED, Section 11.4. There is one installed table for all original histories, both accepted seeds, every record fibre and every target.

At each positive fourth-phase original history its private row is $\pi$ or $\tau$. At every such p history its conditional noncompleting actual-return triple of pulled-back complete laws is exactly (12.4). Thus for an admissible input $\Xi$ and the rational table of Corollary 12.5, at every fourth-phase history $h_0$ of phase $s$,

$$
\left|e_{\mathrm{conf}}^{F_h^r}(h_0)
       -\mathcal L_s^\Xi(T_{s,h_0})\right|\le C_s h,\qquad
T_{s,h_0}=\sum_k\nu_{h_0}(k)P_{s,r_k}.
\tag{12.31}
$$

The loss on the left is the full-record loss through that history's own $I_{C_0(h_0)}$. Every source-supported pure-depth target is covered by the same bound. No prescribed COMPLETE, marginalized-defect or total-resource budget is preserved.

**Proof.** Install the finite description before the first actual Read and initialize the actual original $C_0$ independently of the source. Retain the whole original control, parser and records, using the supplied fair synthesis before the third latch. In the original third-completion update perform its full record write, then its latch, and only thereafter sample the same fixed private p row $\pi$. Use the table's $B$ after an actual p-beta and its $A$ after an actual suspended-alpha. Use these identical kernels in synthetic generation; synthetic emissions use the table's $u,v$. The suspended label $(i,j)$ is finite private memory of its incoming p cell, not a new source observation.

This is precisely the product adapter of PAID, Lemma 2.1.1. Its projection to $C_0$ is the original update on each operation, including its entire event block. Consequently it retains both seed 0 and seed 1, all equal-pair paid rejections, all partial seed and payload parses, all sixteen marker words and their prefixes, every original selector and bare field, the full held $B,Q^+,Z$ records, flags and permissions. The third-write-before-latch order is unchanged. A fourth completing letter clears the private labels and enters its original matching pendingStop. Only that terminal's original Stop delivers it; deliveredStop is absorbing and neither terminal permits Read. Source depth $K$ is sampled once by the original provider before the first actual Read and is never resampled. No new Read, wait, reset, posterior input, future-event conditioning, controller port or clock has been added.

Private initialization and update bits are independent of the entire source, conditional as well as unconditional on its single $K$. Thus conditioning on an actual acquired word does not reweight a private row by its synthetic emission. At the first fourth p cut the row is $\pi$; after any actual p-beta it is $\pi B=\tau$, and after any suspended-alpha it is $\tau A=\pi$. Induction proves these same rows at every positive finite fourth history, including all finite numbers of returns and all paid prefixes on every record fibre.

Given a p history $h_0$, the actual next noncompleting return has probability
$\sum_k\nu_{h_0}(k)r_k(1-r_k)>0$. This event is independent of the private label and update randomness. Conditioning on it cancels this common source factor, leaving exactly the unweighted label probability $\pi_iB_{i,(i,j)}A_{(i,j),k}$. The intermediate and outgoing complete laws are those of the same installed generator. Their pullbacks through their own current-record renderers are $q_i^F,w_{ij}^F,q_k^F$, so the actual triple is $\Xi_F$. In particular the designated-fibre history supremum of conditional immediate-emission return variation is $V_{\Xi_F}$ for this installation.

From every retained operation cut, define the decoder to be the law of this finite installed synthetic program. This gives the exact individual cylinder identity (1.3), with the same acquired update even on an edge whose synthetic probability is zero. The complete-law and renderer conclusions of PAID, Lemma 2.1.1, apply before the latch, in both fourth phases and at the terminals. The regular return bound $\lambda^L$, together with the supplied pre-latch stopping bounds, proves normalization without conditioning on completion. All legal infinite noncompletion paths remain in the carrier at zero mass. For the actual original source they likewise retain their original zero mass at each depth, and hence for a countable prior.

The posterior target in (12.31) is exactly (1.2), with all paid rejections and partial parses counted. No counts or posterior row are runtime inputs. Applying (12.30) directly to this normalized target and then the full-record TV isometry proves (12.31). For bounds against every supported pure-depth law, target convexity is applied at each configuration before averaging:

$$
\mathcal L_s^\Xi\left(\sum_k\nu_{h_0}(k)P_{s,r_k}\right)
 \le\sum_k\nu_{h_0}(k)\mathcal L_s^\Xi(P_{s,r_k}).
\tag{12.32}
$$

All sums are countable nonnegative sums. Thus the same installed table controls all histories at once. The exact identity of its original phase suprema with its supported pure-depth suprema is the supplied PAID, (2.3), and [CLIP, Proposition 2.3](RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md); its lower direction uses actual paid histories and the countable-prior domination, not an extra pure-source query.

For clarity, the rational sampling bridge uses only fresh independent private fair bits, deterministic finite bit operations and reusable finite workspace with almost-sure internal return. These are the primitive convention in PAID, Proposition 11.3; [PH, Definition 30.2](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md) likewise explicitly permits the source-independent fresh fair-bit operation and charges bit arithmetic and addresses. They are not the original acquired seed $R\in\{0,1\}$, nor additional paid source letters used to manufacture a new random supply.

For one rational categorical row choose a denominator $d$ and integer counts summing to $d$. If $d=1$ it is deterministic. Otherwise let $m=\lceil\log_2d\rceil$, draw $m$ fresh fair bits as an integer in $\{0,\ldots,2^m-1\}$, and reject candidates at least $d$. An accepted integer is assigned by the installed cumulative counts. Acceptance has probability $d/2^m>1/2$, unless $d$ is a power of two, when it is one. Repeated independent attempts yield each accepted integer with probability $1/d$ and hence the exact row. The service terminates almost surely, with mean bit use $m2^m/d\le2m$. It reuses candidate and cursor storage without retaining an unbounded retry count, and clears that service workspace to its fixed canonical value before the original operation returns, retaining only the chosen label or output. A finite common denominator for all primitives is also possible. Separate fresh independent bit calls for synthetic emission and update give exactly the joint transition $q_z(o)P_o(z,z')$, and the same update service implements the acquired kernel. No exact uniform-real or arbitrary-real probability primitive is needed.

All installed thresholds, denominators, code, numerical representation, p and incoming-pair label memory, row selectors, addresses, program counter, bit cursor, candidate, arithmetic workspace, event and output cursors, persistent randomness and internal service microstates belong to COMPLETE together with $C_0$. Microstates describe the conditional continuation of that same finite service program and introduce no new original operation cut or permission. Tables and label counts alone are not a COMPLETE bound. Integer comparisons, threshold arithmetic, installation and any construction arithmetic are separately charged rather than unit-cost wide operations. Fresh bit supply, every sampler rejection and its time, synthetic computation and output, receiver storage and waiting, original paid rejections and partial acquisitions, every source call, and the provider's original prior and once-sampled $K$ retain independent resource accounts. Arbitrarily many possible sampler rejections and actual returns exclude a deterministic worst-case total time or bit bound.

If a narrower domain supplies only a fixed finite private seed, the acquired seed $R$, a deterministic finite bound on fair-bit use, or no permitted fresh independent bit service, the implication from rational representation to this exact sampler has an additional premise. It is then exactly the finite-service sampling premise stated in the proposition, and is not inferred from a rational number alone. In particular this proof does not enlarge that domain's random permissions. An unrepresented real $\Xi$ need not effectively specify the rational approximants, and an unrepresented real table need not satisfy the sampler premise. The approximation and analytic limit do not assert effectivity in either case. $\square$

**Corollary 12.7 (the prescribed-return analytic inequality consumed by Proposition 11.4).** Fix the original finite or countable prior with $\mu(1),\mu(2)>0$ and at least one supported $k\ge3$. Let $\Xi$ be any admissible return measure satisfying, for every depth supported by this same prior,

$$
\mathcal L_p^\Xi(P_{p,r_k})\le\rho_p+\epsilon_p,\qquad
\mathcal L_\beta^\Xi(P_{\beta,r_k})\le\rho_\beta+\epsilon_\beta,
\qquad
\epsilon_p,\epsilon_\beta\ge0,\quad
\epsilon=\max\{\epsilon_p,\epsilon_\beta\}.
\tag{12.33}
$$

Then

$$
\frac{2901611\epsilon+4519890V_\Xi}{11}
 \ge \frac{\eta}{400000},\qquad
\eta=\frac{14219478376}{318644812890625}.
\tag{12.34}
$$

This is a nonstrict joint loss–return-variation inequality on the prescribed measure. It assumes the same supported-depth bounds as (2.4), not just endpoint bounds.

**Proof.** Use the rational tables of Corollary 12.5, all generated with their own same acquired and synthetic updates. For each $h$ their losses satisfy (2.4), with the nonnegative slacks

$$
\epsilon_p^h=\epsilon_p+C_ph,\qquad
\epsilon_\beta^h=\epsilon_\beta+C_\beta h,\qquad
\epsilon^h=\max\{\epsilon_p^h,\epsilon_\beta^h\}
 \le\epsilon+C_\beta h.
\tag{12.35}
$$

Uniformity over targets ensures that these are bounds for every depth in the one fixed installed support. Each is a regular finite table, so Proposition 11.4, with its supported-nonendpoint hypothesis, gives

$$
\frac{2901611\epsilon^h+4519890V_{\Xi_{F_h^r}}}{11}
 >\frac{\eta}{400000}.
$$

By (12.30) the variation tends to the prescribed $V_\Xi$, and (12.35) gives $\epsilon^h\to\epsilon$. Passing to the limit proves (12.34), with $\ge$; strictness of each finite-table inequality need not survive the limit. No sampler premise is needed for this algebraic application of Proposition 11.4. Where the original sampling bridge of Proposition 12.6 holds, these same rational tables also have its original-history realization.

The quantity $J$ in (11.1) and (11.12) is the endpoint moment $\int(u-a)(b-u)\,d\nu_p$, rather than the supported-depth loss slack in (12.33). The substitution above uses precisely the $\epsilon$ of (2.4) and (11.15), and does not identify these two quantities. The prior's supported nonendpoint is indispensable to invoking the conserved-class gap inside Proposition 11.4; no endpoint-only version of that positive right-hand side is asserted.

This consumer leaves $V_\Xi$ free and supplies no unrestricted positive risk-only gap. It asserts neither existence of a zero-level admissible $\Xi$ nor an optimizer, attainment or resource optimum. $\square$

**Mathematical citation 12.8 (suppliers and applicability).** The compact law spaces, normalized residual continuity, own complete-law generation and stopping contraction are PAIRED, Lemma 11.1 and (11.19)–(11.20). Its Theorem 11.4, Theorem 11.8 and Chapter 13 preserve their stated pair-flow and marginal scopes; none is used to identify a prescribed triple from two flows. Its Chapter 14 supplies the separate four-moment loss comparison and exclusion, without replacing the present incoming-pair condition. Proposition 11.9 supplies the distinct actual triples consumed in the proof of Theorem 12.2. Proposition 11.4 supplies the finite-table strict inequality consumed in Corollary 12.7. The original source, exact sampler convention and full-history adapter are the suppliers cited in Proposition 12.6. The new source-relative deduction here is regeneration of each specified actual triple, including its finite rational closure and the joint analytic consumer. These are ordinary mathematical proofs, with no new formal certification or literature-priority assertion.

For a primary comparison, Benjamin Jourdain and Gilles Pagès, [*Quantization and martingale couplings*, arXiv:2012.10370v1, Theorem 3.1](https://arxiv.org/html/2012.10370v1), assumes probability measures $\mu\le_{\rm cx}\nu$ on $\mathbb R^d$ with compactly supported $\nu$, quadratic optimal primal quantization of $\mu$ and optimal dual quantization of $\nu$. For every prescribed two-time martingale coupling its construction (3.21) gives quantized martingale couplings; at $p=1$ its Wasserstein error is bounded by the sum of the primal quadratic and dual first-order quantization errors. Finite coordinate projections of $(\mathcal R_B(Q),W)$ in (12.1) satisfy a two-time martingale relation by conditional expectation, have bounded support, and therefore meet the relevant finite-dimensional convex-order hypotheses. That statement concerns those projected two-time marginals and their prescribed coupling. It does not preserve the incoming $Q$ descriptor through projection, identify a cyclic full-law triple, or provide the same finite generator with equal end marginals here. Its term stationary quantization is a conditional-centroid property, not the acquired balance $\pi BA=\pi$.

Lasse Leskelä and Matti Vihola, [*Conditional convex orders and measurable martingale couplings*, arXiv:1404.0999v3, Theorem 1.3](https://arxiv.org/html/1404.0999v3), concerns probability kernels from a measurable parameter space to $\mathbb R^d$, with finite first moments at every parameter. Pointwise convex order is equivalent to existence of a measurable pointwise martingale-coupling kernel. For a finite coordinate projection $\Pi$, the second equality in (12.1) provides, almost surely in the parameter $(Q,W)$, a projected law of $Q'$ with barycentre $\Pi\mathcal R_A(W)$. To obtain a pointwise comparison on every parameter, outside a Borel full-measure set define this projected law to be $\delta_{\Pi\mathcal R_A(W)}$ and compare it with that same point mass. These bounded projected kernels meet the stated first-moment and convex-order hypotheses. This extension is a finite-dimensional context comparison, not an assertion of a new prescribed full-law kernel off the original full set. Selecting some coupling under that theorem would not retain this specified conditional measure, its common end marginal or its finite same-update realization. Neither primary theorem is invoked as a supplier of (12.11), (12.22) or (12.34); the whole-descriptor cyclic bridge and its constants are proved above. Conditioning, the scalar chord bound, cycle decomposition, maximal coupling and finite rational sampling are mature intermediate tools rather than new general results.

The interface is one noncompleting return on the original stopped domain, together with complete predictive laws and target-uniform configuration losses. It does not assert fidelity of arbitrary-length acquired joint paths or reconstruction of $\Xi$ from its two directional flows. The spatial research retains separate obligations for ordered and symmetric mixed traces, both cross blocks, arbitrary correlations and LINEAR compensation by the same actual inverse. No map establishing those obligations is supplied by this probabilistic construction; its label counts, state counts and sampling operations imply no physical-space dimension.

## 追加锚（本行以下为增补区）

## 13. Finite actual-triple necessity and the sharp SAME two-flow motion fiber

**Hypotheses 13.1 (original source and complete descriptor scope).** Retain Definitions 1.1–1.3 and 12.1. The source has its original $m=2,d=1,\ell=2,n=4$, one fixed finite or countable prior with positive masses at depths 1 and 2, and one positive integer $K$ sampled before the first paid Read. The unrestricted common conf/conf question also retains a supported nonendpoint. Conditional on this same $K=k$, the letters have alpha probability $r_k=F_{k+1}/F_{k+3}$. Every original paid rejection and partial parse, both accepted seeds, all marker triples and held $B,Q^+,Z$ records, third-write-before-latch, every finite return, fourth completion and its matching Stop remain in the domain. The control is the full $C_0$ of Definition 1.1, with neither terminal permitting Read.

There is one source-independent finite COMPLETE observer, whose acquired-letter kernels also generate its individual synthetic complete laws through (1.3). COMPLETE includes installed program, numerical representation, original control, labels, selectors, addresses, output cursors, workspace, service microstates and persistent randomness. There is no posterior, count, clock, readable probability row, correlated source seed, source reset, future-event-conditioned update, auxiliary measurement or exact-real runtime port. A mathematical finite stochastic table with real entries and a finitely represented effective exact sampler remain different assertions.

The complete raw carriers, including their infinite outcomes, are those of Definition 1.2; each actual configuration uses its own current-record TV isometry $I_c$. Retain exactly the normalized regular descriptor spaces $\mathcal K_p,\mathcal K_\beta$ of [PAIRED, (11.2)](RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md), already used in Definition 12.1. Their emission bounds are $a=1/3,b=2/5$ and their return-tail bound uses $\lambda=4/15$. In particular the SAME source-dependent residual maps are

$$
u(Q)=Q(\alpha),\qquad v(W)=1-W(\beta),\qquad
\mathcal R_B(Q)(E)=\frac{Q(\beta E)}{1-u(Q)},\qquad
\mathcal R_A(W)(E)=\frac{W(\alpha E)}{v(W)}.
\tag{13.1}
$$

Prefixing includes infinite outcomes and deletes precisely the original next-operation block through $I_c$. The denominators satisfy $1-u\ge3/5$ and $v\ge1/3$. The residual codomains are the full opposite probability simplices; arbitrary residuals need not lie in the opposite regular descriptor space. Regularity is a hypothesis on the prescribed laws in this finite fiber, not a restriction on the unrestricted original observer class, which still permits zero/unit emissions and possible noncompletion.

**Definition 13.2 (two prescribed finite joint flows).** Take distinct full-law atoms $Q_i\in\mathcal K_p$ for a finite nonempty set $I$ and distinct $W_j\in\mathcal K_\beta$ for a finite nonempty set $J$. Let

$$
\Gamma_B=\sum_{i,j}b_{ij}\delta_{(Q_i,W_j)},\qquad
\Gamma_A=\sum_{j,k}a_{jk}\delta_{(W_j,Q_k)}
\tag{13.2}
$$

be a compatible pair in exactly [PAIRED, Definition 11.2](RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md). Thus the masses are nonnegative, each directional total is one, and, after deleting zero phase atoms, their common unweighted marginals are

$$
\pi_i=\sum_jb_{ij}=\sum_ja_{ji}>0,\qquad
\tau_j=\sum_ib_{ij}=\sum_ka_{jk}>0.
\tag{13.3}
$$

For every completed-word and infinite atom of the respective carrier they satisfy

$$
\sum_jb_{ij}W_j(\eta)=\pi_i\mathcal R_B(Q_i)(\eta),\qquad
\sum_ka_{jk}Q_k(\omega)=\tau_j\mathcal R_A(W_j)(\omega).
\tag{13.4}
$$

These full-law row equations are equivalent to that definition's continuous-test equations on finite supports: its bounded Borel extension isolates each whole input atom, and summing the atomic row equations gives every test equation. Neither synthetic continuation factor occurs in (13.3).

**Definition 13.3 (actual triples and two realization scopes).** At a positive original fourth p history $h$, let $X,Y,Z$ be the full configurations before beta, after beta and after alpha, conditioned on the next actual noncompleting return beta-alpha. Pull their complete decoder laws back through their respective original record renderers. On the prescribed supports write their joint law as

$$
\Xi=\sum_{i,j,k}x_{ijk}\delta_{(Q_i,W_j,Q_k)}.
\tag{13.5}
$$

Its first-two and last-two marginals must be exactly (13.2). Arbitrarily many distinct finite COMPLETE labels may carry the same descriptor; incoming memory and persistent randomness remain in those full labels. An abstract original-domain realization is one source-independent initialized finite observer with mathematical real stochastic kernels, retaining the full source/control contract of Hypotheses 13.1; it has these flows and triple at every positive fourth p history and these directional flows at their corresponding phases. A represented realization additionally supplies permitted finite exact sampler services for every primitive row and emission, with all their data and states charged. No uniform COMPLETE or other resource bound is asserted in either scope.

**Theorem 13.4 (finite incoming-pair criterion, including arbitrary initialized refinements).** Under Hypotheses 13.1 and Definitions 13.2–13.3, an abstract finite original-domain realization of (13.5) exists if and only if

$$
x_{ijk}\ge0,\qquad \sum_kx_{ijk}=b_{ij},\qquad
\sum_ix_{ijk}=a_{jk},
\tag{13.6}
$$

and the following equality holds for every $i,j$ and every $\omega\in\Omega_p$, including $\infty_p$:

$$
\boxed{\ \sum_kx_{ijk}Q_k(\omega)
       =b_{ij}\mathcal R_A(W_j)(\omega).\ }
\tag{13.7}
$$

Necessity already holds at any single such original history, with arbitrary finite COMPLETE refinements and nonstationary history rows. Sufficiency reuses the exact atomic construction of Theorem 12.2. Its represented original installation uses Proposition 12.6 when its specified sampling premise holds. Rational latch, update and emission probabilities satisfy that premise under the supplied fresh private fair-bit convention. The algebraic iff is not an unconditional effective-sampling theorem for arbitrary real data.

**Proof of necessity.** Use the observer's complete-state kernels $B_{xy},A_{yz}$ and actual conditional row $\rho_h(x)$. For a fixed acquired history its private evolution is independent of $K$: source-independent initialization and the applied kernels depend on that word and the complete private state, not on source depth. The same statement includes all persistent random state; no private seed correlated with the source is permitted. The probability of the next actual beta-alpha, with $\nu_h$ exactly the paid-history posterior (1.2), is

$$
s_h=\sum_k\nu_h(k)r_k(1-r_k)>0.
\tag{13.8}
$$

This factor is the same for every current private state and private update path, so conditioning cancels it. Consequently

$$
\Pr(X=x,Y=y,Z=z\mid h,\beta\alpha)
       =\rho_h(x)B_{xy}A_{yz}.
\tag{13.9}
$$

There are no synthetic factors $(1-u_x)v_y$ in this actual acquired probability. All original paid letters, including rejected pairs and partial parses, remain in $\nu_h$; it is an analysis posterior, not an observer input.

At each complete suspended configuration reached with positive mass, the exact cylinder identity (1.3), pulled back through its own renderer, gives

$$
W_y=(1-v_y)\delta_\beta+
           v_y\alpha\sum_zA_{yz}Q_z,
\qquad
\sum_zA_{yz}Q_z=\mathcal R_A(W_y).
\tag{13.10}
$$

The analogous p identity is $\sum_yB_{xy}W_y=\mathcal R_B(Q_x)$. These are equalities of normalized full measures, including infinity, and their denominators are positive by the prescribed regular laws. Every positive successor contribution in (13.9) belongs to the specified supports. A zero contribution needs no descriptor assignment.

Push (13.9) to descriptors. The exact two joint marginals give (13.6). For a fixed incoming pair $(i,j)$ and complete atom $\omega$, (13.10) gives

$$
\begin{aligned}
\sum_kx_{ijk}Q_k(\omega)
 &=\sum_{\substack{x,y:Q_x=Q_i\\ W_y=W_j}}
        \rho_h(x)B_{xy}\sum_zA_{yz}Q_z(\omega)\\
 &=b_{ij}\mathcal R_A(W_j)(\omega).
\end{aligned}
$$

All retained incoming memory is already in $y$. Averaging complete states having the same law $W_j$ leaves its residual unchanged, even when their conditional mixture depends on the incoming $Q_i$. Thus no conditional independence of descriptor coordinates, stationary latent row, reversibility or mixing has been assumed. This proves (13.7) under every finite COMPLETE refinement. At $b_{ij}=0$, nonnegativity in (13.6) forces the entire cell to be zero and (13.7) is the undivided equality $0=0$. Likewise $a_{jk}=0$ forces all its incident masses to vanish and is never a divisor.

**Proof of sufficiency by the prescribed-triple supplier.** The finite tensor (13.6) has total mass one. Its first and third marginals both equal $\sum_i\pi_i\delta_{Q_i}$ by (13.3), and its middle marginal is $\sum_j\tau_j\delta_{W_j}$. Its first-two marginal and the first equation of (13.4) give $\mathbb E[W\mid Q]=\mathcal R_B(Q)$. Equation (13.7), divided only on positive incoming cells, gives $\mathbb E[Q'\mid Q,W]=\mathcal R_A(W)$. The laws belong to the exact descriptor spaces of Definition 12.1, and all the identities hold at every finite and infinite atom. Hence every hypothesis of admissibility (12.1) is discharged.

Apply Theorem 12.2 with its $t_{ijk}=x_{ijk}$ and its incoming-pair mass $\tau_{ij}=b_{ij}$. In its notation (12.6) specializes to

$$
\widetilde B_{i,(r,j)}=\mathbf1_{\{r=i\}}\frac{b_{ij}}{\pi_i},\qquad
\widetilde A_{(i,j),k}=\frac{x_{ijk}}{b_{ij}},\qquad
\widetilde u_i=u(Q_i),\qquad
\widetilde v_{(i,j)}=v(W_j),\qquad b_{ij}>0.
\tag{13.11}
$$

These are the supplier's rows, not a second regeneration procedure. Theorem 12.2 supplies their stochasticity, exact balances $\pi\widetilde B=(b_{ij})$ and $(b_{ij})\widetilde A=\pi$, own-law identification with $Q_i,W_j$, and exact tensor $x_{ijk}$. In particular its generated-law uniqueness uses finite stochastic rows and $\widetilde u,\widetilde v\in[a,b]$, all verified here; the two-step contraction is $4/15<1$. It retains the infinite outcomes at zero mass and needs no recurrence or mixing hypothesis. There are at most $|\operatorname{supp}x|$ labels at either phase, before charging original control and representation.

For the algebraic initialized-source conclusion, this table satisfies every hypothesis of [PAID, Definition 2.1 and Lemma 2.1.1](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md): use observer period one, the finite nonempty positive label sets in (13.11), normalized latch row $\pi$, the two exact flow balances, emissions in $[a,b]$, fair pre-latch synthesis on full $C_0$, and the same fixed source-independent latch row after the original third record write and latch. The acquired updates are precisely $\widetilde B$ on p-beta and $\widetilde A$ on suspended-alpha; they also generate the synthetic laws. Completing letters clear labels and use their original pendingStop, followed only by the matching original Stop. These are exactly the adapter conditions, with no change to source $d=1$.

For a represented installation, require each primitive service in (13.11), the latch row and pre-latch fairness to return its specified conditional distribution at every allowed entrance, use source-independent randomness, return almost surely and restore canonical service workspace at the original operation cut. This is exactly Proposition 12.6's premise. Its proof and PAID, Lemma 2.1.1, then supply one initialized observer on all original histories, both seeds and every record fiber, with exact individual generation at every original cut. They preserve all paid rejections, held records, write-before-latch, finite returns, completion and Stop, including the full infinite-tail carrier. The actual rows are $\pi,(b_{ij}),\pi$ through each return and the mass in (13.9) is $\pi_i\widetilde B_{i,(i,j)}\widetilde A_{(i,j),k}=x_{ijk}$. Its two descriptor marginals are the exact whole measures (13.2). No source query, posterior service or future conditioning enters the construction.

Rational primitive data meet this sampling premise by the finite rejection service in Proposition 12.6: finite installed thresholds, fresh independent private fair bits, reusable finite candidate and cursor storage, almost-sure return and clearing of workspace before the operation cut. Independent emission and update draws give the required product cylinder. All installed data, program, arithmetic, workspace, service microstates and persistent randomness are charged alongside $C_0$; the service adds no actual Read or observable cut. Under a narrower randomness convention the stated service premise remains required. Arbitrary real entries alone provide no represented sampler, and no sampler-preserving extraction from an arbitrary observer is asserted. This proves both the algebraic iff and the conditional represented converse. $\square$

**Theorem 13.5 (the complete SAME six-law fiber).** Keep exactly the two joint flows (11.34) and the individual complete laws (11.29)–(11.31). Thus $\Sigma=\{7/20,23/60\}$, $(u_0,u_1,u_2)=(1/3,11/30,2/5)$, and the notation $m=11/30,q=19/30,t_\sigma=q\sigma$ is that of Definition 11.7; this local scalar $m$ does not change the source parameter $m=2$. Every abstract realizable triple with these flows, allowing arbitrary finite COMPLETE refinements, has exactly the form

$$
\Xi=\frac16\sum_{\sigma,i,k}T^\sigma_{ik}
             \delta_{(Q_{\sigma,i},W_\sigma,Q_{\sigma,k})},
\tag{13.12}
$$

where the full block parameterization is

$$
T^\sigma_{i,\cdot}=(s_i^\sigma,1-2s_i^\sigma,s_i^\sigma),\qquad
0\le s_i^\sigma\le\tfrac12,\qquad
\sum_{i=0}^2s_i^\sigma=1.
\tag{13.13}
$$

Every real choice in (13.13) has the abstract original initialized realization of Theorem 13.4. Rational choices have represented exact realizations under Proposition 12.6's fresh private fair-bit convention.

**Proof.** Propositions 11.8–11.9 already establish the normalized full masses, including zero infinite coordinates, their membership in the required descriptor spaces and the two compatible whole flows. Their distinctness is also exact: alpha distinguishes the three $i$ values, $Q_{\sigma,i}(\beta\beta)=(1-u_i)(1-\sigma)$ distinguishes equal $i$ in different blocks, and $W_\sigma(\beta)=1-\sigma$ distinguishes the two suspended atoms. Thus the p atom masses are $1/6$ and the suspended atom masses are $1/2$, without an unaccounted collision.

Use the SAME residual identities (11.36). The affine full-law relation (11.30) also gives $Q_{\sigma,1}=G_\sigma$ because $u_1=m$. Hence

$$
\mathcal R_B(Q_{\sigma,i})=W_\sigma,\qquad
\mathcal R_A(W_\sigma)=G_\sigma=Q_{\sigma,1}
                         =\tfrac13\sum_kQ_{\sigma,k}.
\tag{13.14}
$$

These equalities include every completed word and infinity, and verify (13.4) for these exact flows. Nonnegativity and the exact first-two and last-two marginals exclude all cross-block triple mass. Writing the remaining mass as $T^\sigma_{ik}/6$ forces every row and column of each $T^\sigma$ to sum to one.

For an incoming $i$, the full-law condition (13.7) is $\sum_kT^\sigma_{ik}Q_{\sigma,k}=G_\sigma$. Testing alpha makes it necessary that

$$
\sum_kT^\sigma_{ik}u_k=m.
\tag{13.15}
$$

Conversely, the row sum and the full affine formula $Q_{\sigma,k}=u_k\delta_\alpha+(1-u_k)\beta W_\sigma$ turn (13.15) into the whole mixture $m\delta_\alpha+q\beta W_\sigma=G_\sigma$. This proves every full-law coordinate, including infinity. The reduction to this emission equation is justified by the fixed full-law affine relation, not by emissions alone for general descriptors.

Since $u_k=m+(k-1)/30$, (13.15) is exactly $T^\sigma_{i0}=T^\sigma_{i2}$. Nonnegative row sums give the row form and bounds in (13.13). Column 0 forces $\sum_i s_i^\sigma=1$; this gives column 2 equal to one and column 1 equal to $3-2=1$. These conditions are therefore necessary and sufficient, including boundary rows with zeros. Theorem 13.4 applies to every such tensor. Its supplied realization has p labels $(\sigma,i)$, suspended labels retaining the same incoming $(\sigma,i)$, uniform six-label phase rows, $B=I$ and block alpha-update $A=T^\sigma$. This is a sufficient realization of every triple, while necessity allowed arbitrary refinements and nonstationary original history rows; it imposes no identity-update or reversibility requirement on those other realizations. $\square$

**Theorem 13.6 (sharp joint full-law and emission motion).** On the fiber of Theorem 13.5 define

$$
V_u(\Xi)=\int|u(Q)-u(Q')|\,d\Xi,\qquad
V_Q(\Xi)=\int\operatorname{TV}(Q,Q')\,d\Xi.
\tag{13.16}
$$

Their abstract attainable set is exactly

$$
\boxed{\ \{(V_u,V_Q)\}=\{(v,v):1/45\le v\le1/30\}.\ }
\tag{13.17}
$$

Both endpoints and every rational value in this interval have a finite represented original observer under the exact sampler convention in Proposition 12.6. Arbitrary real points are attained in the algebraic table sense, without an effective exact sampler claim at an arbitrary real interpolation parameter. For the supplied installations, these are also the conditional motions at every original fourth p history and their designated-fiber history suprema.

**Proof.** The covered full-law identity (11.33) gives $\operatorname{TV}(Q_{\sigma,i},Q_{\sigma,k})=|u_i-u_k|=|i-k|/30$: the difference of laws is $(u_i-u_k)(\delta_\alpha-\beta W_\sigma)$, whose two probability laws have disjoint supports. No cross-block triple contributes. Put $d=1/30$. The three row costs of (13.13) are $d$, $2ds_1^\sigma$ and $d$. With uniform incoming block row, their mean is $(1+s_1^\sigma)/45$. The two blocks each have mass $1/2$, so

$$
V_u=V_Q=\frac1{45}
              +\frac{s_1^{7/20}+s_1^{23/60}}{90}.
\tag{13.18}
$$

Each middle parameter lies in $[0,1/2]$, proving the asserted bounds. The lower endpoint holds exactly when both middle parameters are zero; then each block's other two row parameters are $1/2$. The upper endpoint holds exactly when both middle parameters are $1/2$; then the other two parameters in each block sum to $1/2$. In particular choose in both blocks

$$
T_{\min}=\begin{pmatrix}1/2&0&1/2\\0&1&0\\1/2&0&1/2\end{pmatrix},\qquad
T_{\max}=\begin{pmatrix}1/4&1/2&1/4\\1/2&0&1/2\\1/4&1/2&1/4\end{pmatrix}.
\tag{13.19}
$$

The lower matrix is the supplied $A_0$. Every point of the interval is realized by

$$
T(\theta)=(1-\theta)T_{\min}+\theta T_{\max},\qquad
0\le\theta\le1,\qquad
V_u=V_Q=1/45+\theta/90,
\tag{13.20}
$$

using the same choice in both blocks. Its row parameters are $(1/2-\theta/4,\theta/2,1/2-\theta/4)$, which satisfy (13.13). The supplied independent join's $A_1$ is $T(2/3)$, with motion $4/135$ strictly between the endpoints.

For represented endpoints, instantiate Proposition 12.6's sampler with common denominator 60. Each of the six latch labels receives 10 accepted integers; pre-latch fairness receives 30. The p alpha counts are 20, 22, 24 and the suspended alpha counts are 21, 23. The beta update is deterministic. The block alpha-update row counts of the two matrices (13.19) are respectively

$$
(30,0,30),(0,60,0),(30,0,30),\qquad
(15,30,15),(30,0,30),(15,30,15).
\tag{13.21}
$$

The supplier's six-bit rejection service accepts candidates below 60 with probability $15/16$, assigns the indicated cumulative intervals, and restores canonical candidate and cursor workspace before returning. Its output is exactly uniform on the 60 accepted integers, so these counts give all the claimed probabilities, including zero and unit entries. Fresh independent draws for emission and update give the same product cylinder as the algebraic table. All service states, thresholds, row tables, arithmetic, addresses, program counters, output cursors and persistent randomness are included in COMPLETE with $C_0$. Service microstates carry the continuation law of that same installed program; they introduce no original Read or extra queried cut.

For rational $\theta$, all primitive probabilities have a finite common denominator $D$. Proposition 12.6's service with $L=\lceil\log_2D\rceil$ fair bits and rejection of candidates at least $D$ verifies the same premises. Every rational $v$ in (13.17) has rational $\theta=90(v-1/45)$. This proves exact represented attainment without claiming finite worst-case bit, work or output bounds: internal rejections and original paid rejections and returns may be arbitrarily numerous. Six private labels per phase are not the total COMPLETE count.

The rows of every (13.13) are doubly stochastic. Theorem 13.4 and Proposition 12.6 therefore give uniform private phase rows at every positive original history, with one source-independent latch on all seeds and record fibers. Equation (13.8) cancels at each p history. A beta-alpha return leaves the original p control and held records unchanged, so the before and after complete raw laws use the same TV isometry $I_c$. Thus (13.18) is the actual conditional full-record and emission motion at each such history, in particular throughout the designated seed-1, marker-100 fiber. Taking its history supremum gives the same value. $\square$

**Corollary 13.7 (fixed full predictions, risks and paired semantic arrays).** Across all parameters (13.13), both joint flows (11.34), all six individual p laws, both suspended laws with their repetitions and their phase distributions are fixed. For arbitrary complete targets the configuration losses are

$$
\frac16\sum_{\sigma,i}\operatorname{TV}(Q_{\sigma,i},T_p),\qquad
\frac12\sum_\sigma\operatorname{TV}(W_\sigma,T_\beta).
\tag{13.22}
$$

For the initialized installations, both full fourth-phase configuration-risk suprema are identical. Corresponding original pre-latch and terminal laws also agree. Their indexed event arrays are the unchanged nonconstant arrays (11.32).

**Proof.** The exact two margins give the fixed phase distributions. Integrating per-configuration TV gives (13.22); TV has not been moved outside the configuration average. At every original history the same once-sampled source gives its unchanged posterior target (1.2). Proposition 12.6 supplies the same phase row there, and its own $I_c$ preserves TV, proving the equality of all fourth-phase history losses and their suprema. Before the latch, the same fair original-control program reaches the same uniform latch mixture of the same individual laws. Conditioning on its first latch entrance, or taking the finite-prefix limit with the supplied pre-latch survival bounds, proves equality of the entire pre-latch laws. Completing configurations have the same deterministic original Stop/delivery laws. Internal sampler continuations may differ between different installed row programs; they are not additional queried histories.

The events in (11.32) are coordinates of those fixed full laws. Within a block $f_{\sigma,i}=(1-u_i)(1-\sigma)(1+t_\sigma+t_\sigma^2)$ varies with $i$. The suspended array is $h_{\sigma,i}=(1-\sigma)(1+t_\sigma)=1-m\sigma-q\sigma^2$, strictly decreasing between the two positive $\sigma$ values. Both indexed arrays are therefore nonconstant. [PAIRED, Theorem 4.1 and Corollary 4.2](RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md) identifies regular emissions and full laws from both indexed arrays on known fixed $B,A$, with its projected fixed point and unprojected equations as the joint realization test. Here the alpha-update varies; this does not assert identification of an unknown kernel from two marginal numbers. These arrays remain semantic events, not runtime probes or free oracle inputs. $\square$

**Proposition 13.8 (diagonal proxy failure and the independent interior point).** The measure

$$
\Xi_{\rm diag}=\frac16\sum_{\sigma,i}
             \delta_{(Q_{\sigma,i},W_\sigma,Q_{\sigma,i})}
\tag{13.23}
$$

has the two exact joint marginals (11.34) and zero motion, but no original same-update realization with those full laws. Its successor barycenter conditioned only on $W_\sigma$ nevertheless equals the required $G_\sigma$. The conditional independent join is the supplied lawful $\Xi_1$ in (11.37), with motion $4/135$, and conditional independence is not necessary for realization.

**Proof.** The displayed marginals follow by summation. At incoming $i=0$, testing alpha in (13.7) would require $(1/6)(1/3)=(1/6)(11/30)$, which is false. The analogous defect occurs at $i=2$. If identity return rows were imposed, that incoming suspended state's alpha-alpha mass would be $\sigma/3$ instead of the prescribed $\sigma m$. Yet averaging the three successors conditional only on $W_\sigma$ gives $\tfrac13\sum_iQ_{\sigma,i}=G_\sigma$ by (13.14), so that weaker test misses the failure. Conversely (11.37) is $T^\sigma_{ik}=1/3$, which satisfies (13.13), and Theorem 13.6 evaluates its motion. The lower lawful witness has $T_{10}=0$ and differs from that independent join. It proves that imposing conditional independence would discard realizable triples. More generally the independent tensor $x_{ijk}=b_{ij}a_{jk}/\tau_j$ satisfies (13.6)–(13.7) by (13.3)–(13.4); the criterion restricts prescribed triples over a compatible pair and creates no new obstruction to existence of some triple over a finite compatible pair. $\square$

**Mathematical citation 13.9 (exact suppliers and correspondence).** The complete descriptor spaces and source-dependent residual equations are PAIRED, Lemma 11.1 and Definition 11.2. Its Chapter 11 already gives finite same-update regeneration, own-law uniqueness, rational tolerance approximation, exact all-shape regular-infimum equality and finite-atomic attainment criteria. Theorem 12.2 above already gives sufficient regeneration of each prescribed atomic triple, including the retained incoming label and descriptor collisions; Proposition 12.6 gives its exact original installation and sampling bridge. Theorem 13.4 uses precisely those results after verifying (12.1), and adds necessity directly from arbitrary original COMPLETE histories. Propositions 11.8–11.10 already give the explicit laws, equal two whole flows, distinct actual triples, independent join and two represented witnesses. Theorems 13.5–13.6 characterize their entire realizable fiber and its sharp joint motion, including the upper endpoint and all endpoint equality conditions. Conditional expectation and finite affine row algebra are the intermediate methods.

[PAID, Lemma 14.1](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md) supplies original paid-history common-row extraction, including its countable-prior domination. [CLIP, Theorems 3.1 and 4.2](RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md) supplies regular clipping and its unrestricted risk comparison. Neither is used here to claim preservation of an arbitrary prescribed triple, effective sampler representation or resource budget. PAIRED, Chapter 12 supplies four-moment identities and synchronized endpoint-chord rigidity; its endpoint-chord hypothesis is not forced throughout the unrestricted zero face and is not imposed here. Its Chapters 13–14 retain their separate marginal-realization and quantitative chord-comparison scopes. [REV](RECURSIVE_RELATIONAL_OBSERVATION_REVERSIBLE_COMMON_GENERATOR_CONSTRAINTS.md) retains its $A=I$ and reversible hypotheses, none of which is used for this characterization. The finite-dimensional conditional-coupling literature comparison and its whole-descriptor limitations are those of Mathematical citation 12.8; no additional generic gluing or compactness theorem is invoked.

**Limits 13.10 (the unchanged unrestricted alternatives).** Section 9's directed crossing-flow repair already gives simultaneous configuration-loss control and the joint original necessity (9.18), namely $61e(M)/11+19\sqrt{\mathcal V(M)}/11>\eta/400000$ for the same fixed prior with a supported nonendpoint. This remains an inequality on one observer. Immediate-emission return variation, full-law return motion, phase-law dispersion, suspended-to-p mismatch and paired event ranges are distinct quantities. Equality of the first two in Theorem 13.6 uses the particular full-law affine relation (11.30). No independently attainable values are multiplied, and no risk-only lower bound follows while variation and ranges remain free. The linear necessity in Theorem 11.5 and the prescribed-return analytic consumer in Corollary 12.7 retain their existing scopes.

The finite atomic characterization does not evaluate a nonatomic triple problem or a global zero-face value; the approximation and analytic statements already established in Chapter 12 retain their own hypotheses. These SAME-fiber witnesses are not asserted to satisfy every endpoint and supported-interior zero-excess risk face. Thus they supply no common exact zero-excess observer, same-prior vanishing-excess family, evaluated unrestricted positive gap, minimal COMPLETE size, exact fixed-resource optimum or physical dimension. Exact finite common attainment, an unattained zero infimum, a positive unrestricted gap, finite-dimensional relaxations and resource-constrained optima remain separate. The special two-endpoint-prior attainment keeps its own scope. Regular supports in this theorem do not remove original zero/unit emissions or possible noncompletion from the unrestricted class. All conclusions here are ordinary mathematical statements; universal formal applications remain OPEN.

## 追加锚（本行以下为增补区）

## 14. Complete middle-cut minima and motion budgets in the SAME actual-triple fiber

**Hypotheses 14.1 (original source, complete configurations and supplied laws).** Retain exactly the original source, complete carriers, renderer and observer convention of Hypotheses 13.1 and Definitions 13.2–13.3 and [PAID, Definitions 1.1–1.3](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md). One positive integer $K$ is sampled before the first paid Read from one installed finite or countable prior with positive masses at 1 and 2. Conditional on $K=k$, every paid letter has alpha probability $r_k=F_{k+1}/F_{k+3}$. The source parameters remain $m=2,d=1,\ell=2,n=4$. The unrestricted common conf/conf question retains a supported nonendpoint. All claims below concern finite observers in the specified SAME fiber, not a restriction of that unrestricted question.

The original control $C_0$ retains both seeds, every paid equal-pair rejection and partial parse, every marker triple, selectors, bare and held $B,Q^+,Z$ records, write/latch flags, permissions, completion and delivery. The third record is written before latching. Every finite legal return remains; fourth completion permits only its matching Stop, and terminal states permit no Read. The bijection $I_c$ renders the complete raw future, including infinite outcomes, with all original event blocks on the current control/record fiber. It preserves TV and commutes with deleting an original block. An already acquired suspended beta is not a future Read.

COMPLETE includes original control and every live private register, program mode, installed numerical description, address, cursor, workspace, sampler residue and persistent randomness. One source-independent initialized observer uses fixed acquired-letter kernels, and synthetic generation uses these same kernels. There is no source reset, extra measurement, future conditioning, count/clock/posterior/probability-row input or exact-real runtime port. Abstract stochastic rules and finitely represented exact samplers are distinct scopes.

Theorems 13.4–13.6 supply the incoming-cell full-law criterion, the entire SAME fiber and its sharp joint motion. Propositions 11.8–11.10 supply the laws, equal two-flow/unequal-triple example and independent join. These are covered results. The increment here is their complete middle-cut minimum and the separately optimized motion images.

**Definition 14.2 (the fixed complete laws, two joint flows and whole triple).** Put

$$

\sigma_-=7/20,\quad\sigma_+=23/60,\quad
u=(1/3,11/30,2/5),\quad \bar u=11/30,\quad q=19/30.

$$

On the original carriers $w_{n,0}=(\beta\alpha)^n\alpha$, $w_{n,1}=(\beta\alpha)^n\beta\beta$, and their infinite outcomes, retain

$$

G_\sigma(w_{n,0})=\bar u(q\sigma)^n,\qquad
G_\sigma(w_{n,1})=q(1-\sigma)(q\sigma)^n,\qquad G_\sigma(\infty_p)=0,

$$

$$
W_\sigma=(1-\sigma)\delta_\beta+\sigma\alpha G_\sigma,
\qquad Q_{\sigma,i}=u_i\delta_\alpha+(1-u_i)\beta W_\sigma.
\tag{14.1}

$$

The six $Q$'s and two $W$'s are distinct: alpha distinguishes $i$, beta-beta distinguishes the two blocks at equal $i$, and $W_\sigma(\beta)=1-\sigma$ distinguishes suspension. These are precisely (11.29)–(11.31), with $\bar u$ denoting the local scalar called $m$ there, not the original source parameter $m=2$. Their masses normalize because $\bar u+q(1-\sigma)=1-q\sigma$ and $q\sigma<1$. The SAME residual maps, on every word and infinity, are

$$

\mathcal R_B(Q)(E)=Q(\beta E)/(1-Q(\alpha)),\qquad
\mathcal R_A(W)(E)=W(\alpha E)/(1-W(\beta)),

$$

$$
\mathcal R_B(Q_{\sigma,i})=W_\sigma,\qquad
\mathcal R_A(W_\sigma)=G_\sigma=\tfrac13\sum_iQ_{\sigma,i}.
\tag{14.2}

$$

Both prescribed full JOINT measures are fixed:

$$

\Gamma_B=\tfrac16\sum_{\sigma,i}\delta_{(Q_{\sigma,i},W_\sigma)},\qquad
\Gamma_A=\tfrac16\sum_{\sigma,k}\delta_{(W_\sigma,Q_{\sigma,k})}.
\tag{14.3}

$$

By Theorem 13.5, with the exact laws (11.29)–(11.31) and the two joint flows (11.34), every lawful whole triple over (14.3) is exactly

$$

\Xi(s^-,s^+)=\tfrac16\sum_{\sigma,i,k}T^\sigma_{ik}
\delta_{(Q_{\sigma,i},W_\sigma,Q_{\sigma,k})},\qquad
T^\sigma_{i\cdot}=r(s_i^\sigma),\quad r(t)=(t,1-2t,t),
\tag{14.4}

$$

where $s^\sigma\in[0,1/2]^3$, $\sum_i s_i^\sigma=1$, and $s^-=s^{\sigma_-}$, $s^+=s^{\sigma_+}$. Each $s^\sigma$ is determined by the whole triple. In particular (14.4) does not replace either joint margin by a phase margin. The descriptor-space hypotheses hold by Proposition 11.9: the p tail is bounded by $(4/15)^n$ and the suspended tail by $(2/5)(4/15)^n$. Both full joint flows are exactly a compatible pair of PAIRED, Definition 11.2, with its common unweighted marginals and every-word and infinity residual equations. Theorem 13.4 applies through the full affine relation (14.1), as checked in Theorem 13.5. All these full-law residual identities are covered reuse, not consequences of generic marginal gluing.

**Definition 14.3 (reachable COMPLETE returned-cut count and its minimum).** Fix an original reachable fourth-segment suspended control/record value $c$. A counted cut is after the acquired p-beta update, including its internal service, has returned and before the next original Read. Let $Y_\sigma(M,c)$ be the set of COMPLETE configurations at these cuts reachable with positive conditional probability at some positive original history with $C_0=c$, whose raw decoder law is $W_\sigma$. Count actual configurations, without identifying different private registers, incoming selectors, program modes, sampler residues or persistent random states. Histories themselves are not states. The definition takes a union over all such histories, including all finite returns.

For a prescribed whole $\Xi$, let $n_\sigma(\Xi;c)$ be the minimum of $\lvert Y_\sigma(M,c)\rvert$ over all original initialized abstract finite observers realizing the individual laws (14.1) at every positive fourth-phase history, the two flows (14.3) at their corresponding phases, and this SAME $\Xi$ at every positive fourth p history. Allow arbitrary finite p refinements and nonstationary actual configuration rows. Let $N(\Xi;c)$ minimize the sum of the two cardinalities over that same class. No operation/service cut is moved. All intermediate service configurations belong to total COMPLETE but are not returned original suspended cuts.

**Theorem 14.4 (exact complete middle-cut minimum).** Write $C=(1/3,1/3,1/3)$. For every triple (14.4) and every such $c$,

$$

n_\sigma(\Xi;c)=1+\mathbf1_{\{s^\sigma\ne C\}},\qquad
N(\Xi;c)=2+\mathbf1_{\{s^-\ne C\}}+\mathbf1_{\{s^+\ne C\}}.
\tag{14.5}

$$

One original initialized observer attains both block minima simultaneously on every control/record fiber. Rational parameters admit such an observer with finite exact rational services and canonical workspace at all counted cuts. Arbitrary real parameters have the abstract conclusion; a represented real conclusion additionally requires the finite exact services specified below.

**Proof of necessity.** At any positive original p history $h$, let $X,Y,Z$ be the complete configurations before beta, after its returned update, and after the subsequent returned alpha update. Conditional on the acquired word, the private evolution is independent of $K$: initialization and every kernel use source-independent randomness and the known word only. Hence the positive source return probability

$$

\sum_k\nu_h(k)r_k(1-r_k)

$$

uses exactly the paid-history posterior $\nu_h$ of (1.2), is independent of those private choices and cancels. With actual row $\rho_h$ and complete-state kernels $B,A$,

$$

\Pr(X=x,Y=y,Z=z\mid h,\beta\alpha)=\rho_h(x)B_{xy}A_{yz}.
\tag{14.6}

$$

There are no synthetic weights $ (1-u_x)v_y$ here. This is (13.9), whose source-independence hypotheses are exactly Hypotheses 14.1, directly at the original history, without stationary extraction.

The positive block mass $1/2$ forces at least one middle configuration of each law. If a block has only one, denote it by $y_\sigma$ and set

$$

a_k=\sum_{z:Q_z=Q_{\sigma,k}}A_{y_\sigma z}.

$$

Nonnegativity and the exact joint supports force all reached successors into this block. Every incoming $Q_{\sigma,i}$ has mass $1/6$; (14.6) then gives $T^\sigma_{ik}=a_k$, irrespective of its p refinements or their history-dependent masses. The last-two JOINT margin in (14.3) gives $(1/2)a_k=1/6$, so every $a_k=1/3$. Thus $s^\sigma=C$. The argument already holds at each single history; taking the union over histories cannot reduce the bound. Any hidden selector that changed this outgoing row would be a different COMPLETE middle configuration. The two blocks cannot share a configuration because $W_{\sigma_-}\ne W_{\sigma_+}$. This proves the simultaneous lower bounds in (14.5).

**Proof of attainment and full-law obligations.** Use six p labels $(\sigma,i)$, initialized with $\pi_{\sigma,i}=1/6$. For a uniform block use one suspended label $(\sigma,*)$, with

$$

B_{(\sigma,i),(\sigma,*)}=1,\qquad
A_{(\sigma,*),(\sigma,k)}=1/3,\qquad \tau_{\sigma,*}=1/2.
\tag{14.7}

$$

For a nonuniform block use exactly two suspended labels $(\sigma,0),(\sigma,1)$, with

$$

B_{(\sigma,i),(\sigma,0)}=1-2s_i^\sigma,\qquad
B_{(\sigma,i),(\sigma,1)}=2s_i^\sigma,

$$

$$
A_{(\sigma,0),(\sigma,\cdot)}=(0,1,0),\qquad
A_{(\sigma,1),(\sigma,\cdot)}=(1/2,0,1/2),\qquad
(\tau_{\sigma,0},\tau_{\sigma,1})=(1/6,1/3).
\tag{14.8}

$$

All other block transitions vanish. Use p emission $u_i$ and suspended emission $\sigma$. Every row is nonnegative stochastic, including zero and unit entries. Directly,

$$

\pi B=\tau,\qquad \tau A=\pi,\qquad
\sum_jB_{(\sigma,i),(\sigma,j)}A_{(\sigma,j),(\sigma,k)}=T^\sigma_{ik}.
\tag{14.9}

$$

For (14.8), the first two equalities use $\sum_i s_i^\sigma=1$; all retained middle masses are strictly positive. Formula (14.7) applies only to a uniform block.

Every middle label in a block has candidate law $W_\sigma$. The full-law mixtures of each of its outgoing rows are $G_\sigma$: in (14.7) this is (14.2); in (14.8) it is respectively $Q_{\sigma,1}$ and $(Q_{\sigma,0}+Q_{\sigma,2})/2$. Both equal $G_\sigma$ by the affine FULL-law identity (14.1). Therefore, for every word and infinity,

$$

\sum_yB_{xy}W_y=\mathcal R_B(Q_x),\qquad
\sum_zA_{yz}Q_z=\mathcal R_A(W_y).
\tag{14.10}

$$

This explicitly preserves the source residuals; equality of immediate emissions alone would not suffice without (14.1).

The hypotheses of [PAIRED, (11.19)](RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md) hold: the finite kernels are stochastic, all candidate laws are normalized, and all emissions are in $[1/3,2/5]$. More explicitly, with

$$

L=\operatorname{diag}(1-u)B\operatorname{diag}(v)A,\qquad
g=\operatorname{diag}(1-u)B(1-v),

$$

we have $L\mathbf1\le(4/15)\mathbf1$ and
$\sum_{n<N}L^n(u+g)=\mathbf1-L^N\mathbf1$.
Thus the generated masses of the two completed words are $L^nu,L^ng$, sum to one, and retain infinity with mass zero. Suspension is generated by its same-update recursion and has tail at most $(2/5)(4/15)^N$. Two normalized solutions of (14.10) with these emissions have maximal phase TV discrepancies $z_p\le(2/3)z_\beta$, $z_\beta\le(2/5)z_p$, hence both vanish. The candidate laws are exactly the generated full laws. No mixing, irreducibility, conservation or reversibility assumption is used.

**Proof of original initialization.** Equations (14.7)–(14.9) and the emission bounds discharge [PAID, Definition 2.1](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md) with observer period one, distinct from the unchanged source parameter. Apply its Lemma 2.1.1 as follows. Keep the entire $C_0$; before the third latch synthesize fair letters. In the third-completion update perform the entire original record write, then latch, then sample the fixed uniform six-label row independently of the source and acquired word, using the identical rule on both seeds and every marker/held-record fiber. Apply exactly $B$ after acquired p-beta and $A$ after acquired suspended-alpha, and use these same kernels synthetically. Completing letters clear private labels and enter precisely the matching original pendingStop; only original Stop delivers.

The projection of each update to $C_0$ and its entire event block is the original one. Induction over operations therefore preserves all paid rejections, partial parses, seeds, marker triples, held fields, flags, permissions, every finite return, fourth completion and Stop. No extra source operation occurs. Fair pre-latch synthetic seed rejection and early return survivals are $1/2$ and $1/4$; the post-latch bound is $4/15$. Actual survivals at each source depth are at most $5/9$ for seed rejection and $6/25$ per payload return. Infinite outcomes remain in the full carrier with zero mass, also after mixing over the countable prior, without conditioning on completion. Pre-latch and internal-service decoders are the conditional continuations of this same installed generator; pending/delivered laws are the original deterministic ones.

At the first fourth p cut the row is $\pi$. Source independence and (14.9) inductively give row $\tau$ after beta and $\pi$ after alpha at EVERY positive finite original history. Equation (14.6) then pushes forward to masses $T^\sigma_{ik}/6$, giving the prescribed whole $\Xi$ and both exact JOINT flows (14.3). Each retained middle label has positive mass at every applicable history. Rendering uses each history's own $I_c$. No probability row or posterior is runtime input.

**Proof of representation and exact returned count.** For rational $s$, choose a finite common denominator $D$ for (14.7)–(14.8), emissions, fairness and the uniform latch, and an integer $b$ with $2^b\ge D$. Draw $b$ fresh independent fair bits into a bounded candidate register; reject candidates at least $D$ and retry in the same finite workspace, with no retry counter. Accepted candidates select consecutive intervals of integer lengths $Dp_j$. Acceptance probability $D/2^b>0$ proves almost-sure return and exact output probabilities $p_j$. Empty intervals and a single full interval handle zero and unit rows. Emission and update services use fresh independent bits as needed for the joint synthetic kernel.

After committing the selected target label, deterministically clear the candidate, bit cursor, incoming index, row/address selector, emission flag, temporary output and every other scratch register; finish the original event block and return with the common idle program counter and canonical cursors. No bits are prefetched or retained. This finite cleanup uses no Read and occurs inside the same update, before its original returned cut. It is possible because copying the chosen target to its retained label precedes overwriting all old registers; these are ordinary, not reversibility-constrained updates. Immutable tables are common to all cuts of this installed observer. At a fixed $c$, the only varying component on return is exactly the indicated middle label. Thus the COMPLETE configurations at that original cut number precisely (14.7) or (14.8), not a quotient concealing workspace.

All installed constants, program, thresholds, addresses, service states and transient workspace remain charged to total COMPLETE. Internal rejection may run forever on a null set; it adds no original query cut. The count concerns returned cuts and the services return almost surely, not within bounded work. For arbitrary real parameters (14.7)–(14.8) specify abstract finite stochastic rules only. The represented conclusion is conditional on allowed finitely represented, finite-COMPLETE exact services for all primitive probabilities, independent fresh randomness, almost-sure return, and this canonical cleanup. Merely effective approximations to real inputs do not discharge those hypotheses; no external exact-real service or uncounted workspace is assumed. This completes (14.5). ∎

**Theorem 14.5 (separately optimized motion budgets).** Let $V_u,V_Q$ be the actual $\Xi$-integrals of $|u(Q)-u(Q')|$ and $\operatorname{TV}(Q,Q')$. Reuse exactly Theorem 13.6, specifically (13.18):

$$

V_u=V_Q=v=\frac1{45}+\frac{s_1^-+s_1^+}{90}.
\tag{14.11}

$$

For an abstract budget $b$ of returned suspended configurations summed over the two blocks in a fixed fiber, the attainable scalar motion images are

$$

\begin{array}{c|c}
b&\{v:N(\Xi;c)\le b\}\\\hline
2&\{4/135\}\\
3&[7/270,17/540]\\
4&[1/45,1/30].
\end{array}
\tag{14.12}

$$

The separately optimized minimum $M(v)=\min_{\Xi:\,V_u=V_Q=v}N(\Xi;c)$ is 2 at $4/135$, 3 on the three-label interval elsewhere, and 4 on the rest of $[1/45,1/30]$. No triple exists outside that interval. The joint images are the corresponding diagonal sets $(v,v)$. Rational $v$ in every stated budget image has rational exact attainment.

**Proof.** Two configurations force both vectors to be $C$, hence $s_1^-+s_1^+=2/3$. At most three force at least one vector to be $C$, so the sum ranges over $[1/3,5/6]$. Each value occurs by taking the other vector

$$

s(t)=((1-t)/2,t,(1-t)/2),\qquad 0\le t\le1/2.

$$

Four permit both middle coordinates throughout $[0,1/2]$, independently within the already lawful WHOLE-triple family (14.4); taking $s^-=s^+=s(t)$ gives the full sum interval $[0,1]$. Substitution in the covered (14.11) proves (14.12), including endpoints; (14.5) then proves $M$. This is joint realization by the explicit kernels, not multiplication of separately attainable quantities.

For the rational global endpoints use $s^-=s^+=L=(1/2,0,1/2)$, giving $v=1/45,N=4$, and $s^-=s^+=H=(1/4,1/2,1/4)$, giving $v=1/30,N=4$. The three-label endpoints are $(C,L)$ and $(C,H)$. Their primitive denominators divide 60, so the service above can accept 60 of 64 six-bit candidates. For rational motion the displayed $t$'s are rational, giving the same finite representation with a suitable denominator.

Let $D=(1/2,1/3,1/6)$. The three distinct whole triples with block pairs $(C,C),(C,D),(D,D)$ all have motion $4/135$, but their prescribed-triple minima are respectively 2, 3 and 4. Distinctness follows from (14.4), for example its incoming-0/outgoing-0 mass in each changed block. Therefore $M(v)$ cannot substitute for the minimum of a prescribed $\Xi$. ∎

**Corollary 14.6 (unchanged complete configuration risks).** For the installations of Theorem 14.4, at every original fourth-phase history the full configuration losses remain exactly

$$

\frac16\sum_{\sigma,i}\operatorname{TV}((I_c)_*Q_{\sigma,i},T_h^\mu),\qquad
\frac12\sum_\sigma\operatorname{TV}((I_c)_*W_\sigma,T_h^\mu),
\tag{14.13}

$$

with the respective phase's $c$ and original posterior target (1.2). TV stays inside the average.

**Proof.** Theorem 14.4 supplies the same six p masses $1/6$ and total suspended mass $1/2$ for each law, at every positive original history. Applying that history's own TV isometry $I_c$ proves (14.13); this also discharges the hypotheses of Corollary 13.7 for the refined middle labels. The posterior uses every paid letter and is only an analysis quantity. These equalities hold for every finite or countable installed prior and all histories; hence their full original risk suprema agree. The common uniform latch and identical subsequent full laws also preserve corresponding pre-latch laws and deterministic terminal laws. Internal sampler laws can differ across programs; they are not added queried histories. $\square$

**Mathematical citation 14.7 (exact reuse and type correspondence).** Theorem 13.4 supplies the incoming-pair full-law criterion; Theorem 13.5 supplies exactly the entire SAME fiber; Theorem 13.6 supplies its joint motion formula and extrema. Propositions 11.8–11.10 supply the six p laws, two suspended laws, both whole joint flows, distinct actual triples, independent join and original represented witnesses. These results are reused with those identical laws, residual maps and joint measures. The additional deduction in Theorems 14.4–14.5 is the minimum number of reachable COMPLETE returned suspended configurations and its separately optimized motion images. Conditional kernels and the two outgoing full-law barycentres in (14.8) give that deduction; the supplied fiber and motion proofs are not new results here.

[PAIRED, Definition 11.2 and (11.19)](RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md) supplies the precise two-flow domain and normalized own-law recursion, including all infinite coordinates. Its Chapter 11 already supplies compact law spaces, descriptor-conditioned residual barycentres, finite same-update regeneration, rational tolerance approximation, all-shape regular-infimum correspondence and the finite-atomic exact-attainment criterion. Theorem 14.4 uses only the stated finite rows, their exact full-law recursions and stopping contraction. [PAID, Definition 2.1 and Lemma 2.1.1](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md) supplies original initialized product realization; the displayed balances, emission bounds, fixed source-independent latch and full original control discharge each premise. Proposition 12.6 supplies the exact sampling bridge, whose finite-service and canonical-return hypotheses are verified explicitly in Theorem 14.4. Neither stationary extraction nor clipping is used to preserve the prescribed triple or the count. [REV](RECURSIVE_RELATIONAL_OBSERVATION_REVERSIBLE_COMMON_GENERATOR_CONSTRAINTS.md) retains its identity-alpha-update and reversibility scopes; neither is assumed here.

The mature comparisons have different inputs. Leskelä and Vihola, [*Conditional convex orders and measurable martingale couplings*, Theorems 1.2–1.3](https://arxiv.org/html/1404.0999v3), concerns finite-dimensional integrable barycentric kernels. Bounded finite word-coordinate projections meet its integrability hypothesis, but its coupling existence does not preserve this prescribed whole triple or construct the original initialized observer. Monràs and Winter, [*Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem*, Section 2, Theorem 6](https://arxiv.org/html/1412.3634v1), records the classical stable pointed polyhedral-cone criterion with its own attribution. Taghavian and Sjölund, [*Minimal positive Markov realizations*, Sections III–IV](https://arxiv.org/html/2502.21102v3), concerns positive transfer-function realization. Neither positive-realization result is a supplier for the present original-cut count. O'Connor, McGoff and Nobel, [*Optimal Transport for Stationary Markov Chains via Policy Iteration*](https://jmlr.org/papers/v23/21-0519.html), concerns dynamically constrained stationary transition couplings; its optimization theorem is not used in the nonstationary-history necessity proof. Abate, Redig and Tkachev, [*On the effect of perturbation of conditional probabilities in total variation*](https://arxiv.org/html/1311.3066v1), concerns path-law perturbation, and Haesaert, Soudjani and Abate, [*Verification of General Markov Decision Processes by Approximate Similarity Relations and Policy Refinement*](https://doi.org/10.1137/16M1079397), concerns approximate simulation and control refinement. Neither replaces exact full-law generation and original initialization. Van den Bos and Vaandrager, [*State Identification for Labeled Transition Systems with Inputs and Outputs*, Sections 3–4](https://arxiv.org/html/1907.11034v2), concerns legal controlled tests; no corresponding controllable source experiment is available here. These are applicability comparisons, not additional theorem invocations or an exhaustive priority claim.

The qualified Auric comparisons are [Occlusion and second projection, Q2–Q4](AURIC_FIB_ATOM_OCCLUSION_SECOND_PROJECTION_AND_LOCAL_RECOVERY.md), [Local clock and output seam, Q2, Q4, Q6 and Q16](AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md), and [Symmetric seam and Fibonacci hierarchy, Q6–Q7 and Q10–Q11](AURIC_FIB_ATOM_SYMMETRIC_SEAM_PATH_DEFECT_AND_FIBONACCI_HIERARCHY.md). Their hypotheses require a common source law, calibrated exact readouts, legal control/output operations, full compatible histories and explicit correspondence of the objects being compared. Static seam coordinates, noncommuting responses, paired event arrays, complete future laws and actual triple correlations are different objects. No type-preserving map from this returned-cut count to a native-FIB or physical realization is supplied.

**Limits 14.8 (joint necessities and the unchanged unrestricted target).**

The source-specific equality $V_u=V_Q$ does not identify return variation with phase-law dispersion, suspended-to-p mismatch or event ranges. Section 9, specifically (9.18), retains its joint necessity

$$

\frac{61}{11}e(M)+\frac{19}{11}\sqrt{\mathcal V(M)}>
\frac{\eta}{400000},\qquad \eta=\frac{14219478376}{318644812890625},

$$

where $e=\max\{R_{\mathrm{conf},p}-1116529/22781250,R_{\mathrm{conf},\beta}-239/6750\}$ and $\mathcal V$ is the original seed-1, marker-100 fiber's history supremum. For the constructed observers that supremum equals (14.11), since (14.6) and (14.9) hold at each such history. No risk-only gap follows with variation free. [PAIRED, Chapters 11, 12 and 14](RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md) already supplies its compatible-law correspondence, four-moment rigidity, common endpoint-weight stability and evaluated joint excess/four-moment exclusion. The stability comparison fixes neither the actual $\Xi$ nor its return variation. No endpoint-chord condition is imposed here on the unrestricted zero face.

[PAIRED, Theorem 4.1 and Corollary 4.2](RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md) identifies emissions and full laws from indexed paired semantic arrays on KNOWN $B,A$, with the projected fixed point and all unprojected equations. These arrays are not two marginal numbers or runtime observations. On the p labels the values remain $f_{\sigma,i}=(1-u_i)(1-\sigma)(1+q\sigma+(q\sigma)^2)$, and on each retained suspended label $y$ in block $\sigma$ the value is $h_y=(1-\sigma)(1+q\sigma)$, as in (11.32). The first varies with $i$; the second equals $1-\bar u\sigma-q\sigma^2$ and strictly decreases between the blocks. Thus neither indexed array is constant. The present realizations change acquired kernels and label multiplicities; the fixed-known-kernel hypothesis must be applied separately to each installed table, and no unknown-kernel inverse is asserted. The qualified Auric same-law calibrated readouts, static coordinates, commutators and complete future laws have different types. No native-FIB, physical or free-measurement bridge follows from the count.

This proof uses direct conditional kernels and an explicit two-row interpolation, not a new generic positive-realization, compactness, gluing, rounding or factorization theorem. Positive-realization/invariant-cone results concern their specified word functions or transfer functions; stationary transition coupling, approximate simulation and controlled testing do not replace (14.6), (14.10) or original initialization. The correspondence and limits are specified in Mathematical citation 14.7.

The minima in (14.5) and (14.12) are returned-cut counts in this fixed finite law fiber. They are not total COMPLETE minima, sampler size, description size, finite samples, number of histories, worst-case work/bit bounds or unrestricted fixed-resource optima. Finite exact common attainment, an unattained zero infimum, a positive unrestricted gap, finite-dimensional relaxations and fixed-resource optima remain separate. No zero-face existence/value, nonatomic characterization or unrestricted zero/gap alternative is settled. Endpoint-only prior attainments keep their separate scope. The original unrestricted class still admits zero/unit emissions and possible noncompletion. All new universal formal applications remain **OPEN**.

## 追加锚（本行以下为增补区）
