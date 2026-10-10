# Paired finite-readout observability on the original acquired stopped circulation

## 1. The joint relation and its original-source consequence

The results below have ordinary mathematical proofs. No Lean verification, frozen status or CI result is asserted.

Two particular finite complete-word events, one at each original phase, jointly determine every regular emission on a fixed acquired circulation. Their individual readouts do not have this property. Proposed arrays admit one common regular completion exactly when the unique projected feedback solution also satisfies the unprojected equations. The joint inverse is uniform in the finite numbers of configurations and requires no native residual, conserved emission, reversibility or irreducibility hypothesis. Its consequence for the original unrestricted observer class is that semantic variation cannot be hidden entirely outside these two event readouts.

Put

$$
a=\frac13,\qquad b=\frac25,\qquad
\rho_p=\frac{1116529}{22781250},\qquad
\rho_\beta=\frac{239}{6750}.
$$

Use the complete raw words and original full-record renderer defined in Section 2. Define

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\},
$$

$$
C=\frac{11758471}{22781250},\qquad
H=\frac{5261}{6750},\qquad c=1-H=\frac{1489}{6750}.
\tag{1.1}
$$

These events, endpoint radii and midpoint values are supplied by [ST] and [PAID, Section 12]. They are not newly chosen minimax targets.

For an original observer $M$, write

$$
e(M)=\max\{R_{\mathrm{conf},p}(M)-\rho_p,
                 R_{\mathrm{conf},\beta}(M)-\rho_\beta\}.
\tag{1.2}
$$

Fix the original seed-1, marker-100 held-record fibre reached by

$$
S=\beta\alpha\mid\beta\beta\alpha\alpha.
\tag{1.3}
$$

Pull each configuration's complete law back through its current full-record renderer. Let $\mathcal Z_s^*(M)$ be the union of configurations reachable with positive probability after a positive finite actual history on this fibre, at phase $s$. Define the two event ranges

$$
\mathcal O_p(M)=\sup_{z,z'\in\mathcal Z_p^*(M)}
 |D_z(E_p)-D_{z'}(E_p)|,
$$

$$
\mathcal O_\beta(M)=\sup_{z,z'\in\mathcal Z_\beta^*(M)}
 |D_z(E_\beta)-D_{z'}(E_\beta)|.
\tag{1.4}
$$

The configurations in a comparison need not coexist after one history. The events are interpreted in each configuration's own current-record chart. These are semantic readouts of finite law descriptions, not new actual observations or runtime ports.

**Theorem 1.1 (original-source paired-event noncollapse).** Every original finite COMPLETE observer and every installed finite or countable prior with $\mu(1),\mu(2)>0$ satisfy

$$
367e(M)+20\mathcal O_p(M)+52\mathcal O_\beta(M)
>\frac1{25000}.
\tag{1.5}
$$

In particular, the class in which both designated event readouts are constant on their reachable phase fibres has

$$
e(M)>\frac1{9175000},\qquad
\inf_M e(M)\ge\frac1{9175000}.
\tag{1.6}
$$

Exact common conf/conf attainment requires

$$
20\mathcal O_p(M)+52\mathcal O_\beta(M)>\frac1{25000}.
\tag{1.7}
$$

For any sequence with $e(M_n)\to0$,

$$
\liminf_n\bigl(20\mathcal O_p(M_n)+52\mathcal O_\beta(M_n)\bigr)
\ge\frac1{25000}.
\tag{1.8}
$$

No supported nonendpoint is needed for these statements. The event ranges are free in the unrestricted original class, so this is not an unrestricted positive gap. No exact common attainer, vanishing-excess construction or fixed-resource optimum is supplied. The main mathematical result is the nonlinear finite-readout inverse in Section 4; (1.5) is its risk consequence, rather than a renamed full-law-diameter estimate.

## 2. Unchanged source, complete laws and finite resources

Fix the original parameters $m=2,d=1,\ell=2,n=4$, with $F_0=0,F_1=1$ and $F_{j+2}=F_{j+1}+F_j$. Before the first actual Read, draw one depth $K$ from one installed finite or countable prior $\mu$. Conditional on this same $K=k$, all actual Reads are independent with alpha probability

$$
r_k=\frac{F_{k+1}}{F_{k+3}},\qquad
r_1=a,\quad r_2=b,\quad r_k\in[3/8,5/13]\quad(k\ge3).
$$

Equal seed pairs are paid rejections. Alpha-beta accepts seed 0 and beta-alpha accepts seed 1. In payload phase p, alpha completes marker 0 and beta suspends. At suspension, alpha returns to p and beta completes marker 1. The first three completions advance segments. The third record is written before its latch. Fourth completion enters the matching pendingStop; its unique original Stop enters deliveredStop. Neither terminal permits Read.

The original finite control $C_0$ retains both seeds, parser, selectors, full marker tree, bare fields, held $B,Q^+,Z$ records, write/latch flags, permissions, completion and Stop delivery. Both seeds, every marker triple and every positive finite rejection and return history remain in the domain. There is no source reset, fresh depth, future-event conditioning, extra actual query or controller port.

At p, the raw complete futures are

$$
w_{j,0}=(\beta\alpha)^j\alpha,
\qquad w_{j,1}=(\beta\alpha)^j\beta\beta,
\qquad j\ge0,
$$

and the unique infinite noncompletion word. The suspended carrier contains beta, $\alpha w_{j,i}$ and its infinite noncompletion word. The already acquired suspended beta is not a future Read. Writing $a_r=r(1-r)$, the native masses are

$$
P_{p,r}(w_{j,0})=r a_r^j,
\qquad P_{p,r}(w_{j,1})=(1-r)^2a_r^j,
$$

$$
P_{\beta,r}(\beta)=1-r,
\quad P_{\beta,r}(\alpha w_{j,0})=r^2a_r^j,
\quad P_{\beta,r}(\alpha w_{j,1})=r(1-r)^2a_r^j.
\tag{2.1}
$$

Their infinite-word masses are zero. For current original control and records $c_0$, the deterministic renderer $I_{c_0}$ keeps every future Read and inserts its original record, control, permission, completion and Stop blocks. Reading the letters back is its inverse on the legal transcript space. Thus it is a measurable bijection, preserves TV, and commutes with deletion of the next operation and its block [ST, Section 2.1; FLOW, Definition 2.4]. None of the comparisons below discard held registers from the prediction task.

At a positive active fourth-segment actual history $h$, the true complete law is

$$
T_h^\mu=(I_{C_0(h)})_*\sum_k\nu_h(k)P_{s,r_k},
\qquad
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
 {\sum_i\mu(i)r_i^{A(h)}(1-r_i)^{B(h)}}.
\tag{2.2}
$$

All paid rejections and partial parses enter these counts. Counts and posterior rows are analysis objects only.

An allowed observer has one fixed finite COMPLETE configuration set, source-independent initialization and fixed time-homogeneous source-independent acquired-letter stochastic kernels. COMPLETE counts $C_0$, model/program/table selectors, addresses, output indices, workspace and all persistent randomness. Runtime reads the actual finite configuration only. There is no uncounted tape, archive, advice, clock, continuous register, exact posterior input, readable state-distribution vector or source-correlated seed.

Every configuration's decoder is exactly the full law generated by its synthetic emissions and those same acquired-letter kernels. If $o$ is a legal next operation and $E$ a residual event, then

$$
D_z(oE)=q_z(o)\sum_{z'}P_o(z,z')D_{z'}(E).
\tag{2.3}
$$

The left cylinder contains the original operation block. This identity still holds at $q_z(o)=0$; the acquired kernel remains defined. Synthetic generation does not query the actual source. Decoding identifies a finite installed generator and its current configuration, not an infinite table of probabilities.

For the actual configuration row $\rho_h$, let

$$
\overline D_h=\sum_z\rho_h(z)D_z,
\qquad
e_{\rm law}(h)=\operatorname{TV}(\overline D_h,T_h^\mu),
$$

$$
e_{\rm conf}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu),
\qquad R_{j,s}=\sup_{h\in\mathcal H_s}e_j(h).
\tag{2.4}
$$

$\mathcal H_p,\mathcal H_\beta$ contain all positive finite fourth-segment histories at their respective phases. $\mathcal H_3$ contains only the first p cut after the third latch and is not substituted for $\mathcal H_p$. TV is the event-supremum convention, or half the countable $\ell^1$ distance. Marginalized law loss, configuration-before-TV loss and actual-history-average loss are distinct.

The separate full-tail minima in either risk order on their respective full phase domains are $\rho_p,\rho_\beta$ [ST; PH, Theorem 2.1; CLIP, Definition 1.3]. In particular $e(M)\ge0$. These separate minima do not assert one common conf/conf attainment. The supplied terminal-only minima $13/266,9/266$ are different projections. The three-depth endpoint-tag counterexample is a failure of that particular generator, not an unrestricted gap or a marginalized-risk violation.

The endpoint-distance calculation used below can be checked directly from (2.1). The second-to-first ratios on the two p branches are $(6/5)(27/25)^j$ and $(81/100)(27/25)^j$; only the second ratio is below one, exactly for $j=0,1,2$. At suspension the ratios are $9/10$ on beta, $(36/25)(27/25)^j$ on $\alpha w_{j,0}$ and $(243/250)(27/25)^j$ on $\alpha w_{j,1}$, with the last below one only at $j=0$. Thus $E_p,E_\beta$ are the complete endpoint positive-difference events, and their mass differences are exactly $2\rho_p,2\rho_\beta$. This verifies the particular endpoint premises consumed in (5.7) and (6.4), while the phasewise attainments remain supplied results.

Only actual-history-marginalized conditioning coherence may be relaxed. For a positive actual history and legal operation with predicted probability $q_h(o)>0$, set

$$
\delta(h,o)=\operatorname{TV}(\operatorname{res}_o\overline D_h,
                                      \overline D_{ho}).
$$

At $q_h(o)=0$ set this defect to zero without defining a conditional law; the actual successor and its risk stay in the domain. The fourth-segment and full-operation suprema are $\Delta_4$ and $\Delta_{\rm all}$. PendingStop has its unique zero-defect Stop, and the delivered empty supremum is zero. The theorems below impose no defect budget, so they include the zero-defect subclass. They supply no zero-defect recovery or joint attainment from separate phase attainments. All four risks, both defects and resource coordinates must refer to one observer, source, prior and actual history domain.

## 3. The two readouts on one actual circulation

For the regular-table arguments let $X,Y$ be finite p and suspended label sets, with strictly positive probability rows $\pi,\tau$ and stochastic acquired kernels

$$
B:X\longrightarrow Y,\qquad A:Y\longrightarrow X,
\qquad \pi B=\tau,\qquad \tau A=\pi.
\tag{3.1}
$$

Emissions satisfy $u_x,v_y\in[a,b]$. Put $U_x=1-u_x$, with $U$ denoting a column and $\operatorname{diag}(U)$ its diagonal matrix; put $V=\operatorname{diag}(v)$. The exact own laws satisfy

$$
Q_x=u_x\delta_\alpha+U_x\beta\sum_yB_{xy}W_y,
\qquad
W_y=(1-v_y)\delta_\beta+v_y\alpha\sum_xA_{yx}Q_x.
\tag{3.2}
$$

Define

$$
L=\operatorname{diag}(U)BVA,
\qquad g=\operatorname{diag}(U)B(1-v).
$$

Then $Q_x(w_{j,0})=(L^ju)_x$ and $Q_x(w_{j,1})=(L^jg)_x$. Since

$$
0\le L\le\lambda BA,
\qquad \lambda=\frac4{15},
\qquad \pi BA=\pi,
\tag{3.3}
$$

both laws complete almost surely, with probability of at least $j$ further returns at most $\lambda^j$ from p and at most $b\lambda^j$ after a suspended alpha. Infinite outcomes remain in their carriers with mass zero.

The readout arrays are

$$
f_x=Q_x(E_p),\qquad h_y=W_y(E_\beta).
$$

Their exact equations are

$$
f=g+Lg+L^2g,\qquad h=1-v+VAg.
\tag{3.4}
$$

Here $g\in[9/25,4/9]^X$, and therefore

$$
0\le f_x\le M_f:=\frac{1204}{2025},
\qquad h_-:=\frac{93}{125}\le h_y\le h_+:=\frac{22}{27}.
\tag{3.5}
$$

Indeed (3.3) bounds each term of $f$ by $(4/9)\lambda^j$ for $j=0,1,2$. For $h$, bound $Ag$ between $9/25$ and $4/9$ in $1-v+vAg$ and use $a\le v\le b$.

**Lemma 3.1 (joint nonlinear elimination).** The same acquired kernels and the same emissions obey

$$
f=\operatorname{diag}(U)
 \left[Bh+BVA\bigl(\operatorname{diag}(U)B(v+h-1)\bigr)\right],
\tag{3.6}
$$

$$
v=\frac{1-h}{1-A[\operatorname{diag}(U)B(1-v)]}.
\tag{3.7}
$$

Divisions are coordinatewise. Both denominators used in these identities are positive.

**Proof.** From the second equation of (3.4), $VAg=v+h-1$. Hence

$$
Lg=\operatorname{diag}(U)B(v+h-1),
\qquad g+Lg=\operatorname{diag}(U)Bh.
$$

Apply $L$ to the first displayed identity and add to the second to get (3.6). The other equation of (3.4) gives $1-h=v(1-Ag)$, proving (3.7). Since $Ag\le4/9$, its denominator is at least $5/9$. The bracket in (3.6) is at least $Bh\ge h_-$, because $v+h-1=VAg\ge0$. No emission-weighted transition is replaced by an unweighted acquired transition. $\square$

For columns set

$$
\|q\|_\pi=\sum_x\pi_x|q_x|,\qquad
\|r\|_\tau=\sum_y\tau_y|r_y|,
\qquad \|(q,r)\|_* =\|q\|_\pi+\frac43\|r\|_\tau.
\tag{3.8}
$$

The acquired-flow identities imply

$$
\|Br\|_\pi\le\|r\|_\tau,
\qquad \|Aq\|_\tau\le\|q\|_\pi.
\tag{3.9}
$$

These are weighted analysis norms on one actual circulation. For indexed law families,
$\pi\operatorname{TV}(Q,Q')$ means $\sum_x\pi_x\operatorname{TV}(Q_x,Q'_x)$, and similarly for $\tau\operatorname{TV}(W,W')$. It is the average of individual configuration-law distances, not the TV distance between the two averaged laws.

## 4. A global finite-readout inverse for fixed acquired kernels

For data arrays $F\in[0,M_f]^X$ and $J\in[h_-,h_+]^Y$, define on the regular emission cube
$\mathcal C=[3/5,2/3]^X\times[a,b]^Y$ the feedback map

$$
\Psi^U_{F,J}(U,v)=
\frac{F}{BJ+BVA[\operatorname{diag}(U)B(v+J-1)]},
$$

$$
\Psi^v_{F,J}(U,v)=
\frac{1-J}{1-A[\operatorname{diag}(U)B(1-v)]}.
\tag{4.1}
$$

For every input in this cube, $v+J-1\ge a+h_--1=29/375>0$. Thus the first denominator is at least $h_-$, and the second at least $5/9$. The map need not itself preserve the cube. Let $\Pi$ be coordinatewise projection onto the two intervals defining $\mathcal C$.

**Theorem 4.1 (paired finite-readout observability and stability).** Fix $B,A,\pi,\tau$ satisfying (3.1). For two regular emission assignments $(u,v),(u',v')$ on these same kernels, let $(f,h),(f',h')$ be their event-readout arrays and $(Q,W),(Q',W')$ their complete generated laws. Put

$$
\delta_f=\|f-f'\|_\pi,\qquad
\delta_h=\|h-h'\|_\tau.
$$

Then

$$
\|u-u'\|_\pi+\frac43\|v-v'\|_\tau
\le14\delta_f+38\delta_h.
\tag{4.2}
$$

Consequently the paired readout arrays uniquely determine all emissions and both complete laws, and

$$
\pi\operatorname{TV}(Q,Q')\le20\delta_f+52\delta_h,
\qquad
\tau\operatorname{TV}(W,W')\le20\delta_f+52\delta_h.
\tag{4.3}
$$

For actual readout data $(F,J)=(f,h)$, iteration of $\Pi\Psi_{F,J}$ from any point of $\mathcal C$ converges to $(1-u,v)$. After $n$ iterations its emission error in (3.8) is at most

$$
\frac7{45}\left(\frac9{10}\right)^n,
\tag{4.4}
$$

and either weighted complete-law TV error is at most

$$
\frac7{33}\left(\frac9{10}\right)^n.
\tag{4.5}
$$

These are analysis and offline reconstruction statements. They do not provide a new source query, runtime posterior port or resource-preserving observer replacement.

**Proof of the emission inverse.** For two inputs write $d_U=\|U-U'\|_\pi$ and $d_v=\|v-v'\|_\tau$. Let

$$
T(U,v)=BVA[\operatorname{diag}(U)B(v+J-1)].
$$

Split its difference by first changing the outer $V$, then $U$, then the inner $v$. Bounds (3.9), $U\le2/3$, $v\le b$ and $J\le h_+$ give

$$
\|T(U,v)-T(U',v')\|_\pi
\le b(b+h_+-1)d_U+\frac23(2b+h_+-1)d_v.
\tag{4.6}
$$

For example the outer-$V$ term is bounded by $(2/3)(b+h_+-1)d_v$; the inner-$v$ term is bounded by $(2/3)b d_v$. This explicitly keeps both appearances of the same emission in the feedback equation.

Using $|1/s-1/t|=|s-t|/(st)$ and the positive denominator bounds in (4.1), one obtains

$$
\begin{pmatrix}
\|\Psi^U(U,v)-\Psi^U(U',v')\|_\pi\\
\|\Psi^v(U,v)-\Psi^v(U',v')\|_\tau
\end{pmatrix}
\le
\begin{pmatrix}
\alpha&\beta\\ \gamma&\gamma
\end{pmatrix}
\begin{pmatrix}d_U\\d_v\end{pmatrix},
\tag{4.7}
$$

where valid exact bounds are

$$
\alpha=\frac{1745800}{18915363}<\frac1{10},\qquad
\beta=\frac{24983000}{56746089}<\frac9{20},\qquad
\gamma=\frac{1728}{3125}<\frac{14}{25}.
$$

To verify them, $M_f/h_-^2=752500/700569$. Multiplying this by the two coefficients in (4.6) gives $\alpha,\beta$. In the second map, $1-J\le1-h_-=32/125$, and

$$
\|\operatorname{diag}(U)B(1-v)
 -\operatorname{diag}(U')B(1-v')\|_\pi
\le\frac23(d_U+d_v).
$$

Its reciprocal-denominator factor is $(32/125)/(5/9)^2$; multiplication by $2/3$ gives $\gamma$.

In the norm (3.8), the coarse matrix in (4.7) has operator norm at most

$$
\max\left\{\frac1{10}+\frac43\frac{14}{25},
             \frac34\frac9{20}+\frac{14}{25}\right\}
=\frac{359}{400}<\frac9{10}.
\tag{4.8}
$$

Projection $\Pi$ is nonexpansive in this norm, so the projected map has the same bound.

Now freeze the second assignment's actual readouts $(f',h')$ in (4.1). The first assignment is a fixed point for its own $(f,h)$ by Lemma 3.1. Its first denominator changes by

$$
B(h-h')+BVA[\operatorname{diag}(U)B(h-h')],
$$

whose norm is at most $(19/15)\delta_h$. Changing its numerator changes the norm by at most $\delta_f/h_-$. Since

$$
\frac1{h_-}=\frac{125}{93}<\frac75,
\qquad \frac{M_f}{h_-^2}\frac{19}{15}<\frac75,
$$

the residual in the first map is at most $(7/5)(\delta_f+\delta_h)$. In the second map its exact residual is $(h'-h)/(1-Ag)$, of norm at most $(9/5)\delta_h$. Therefore

$$
\|(U,v)-\Psi_{f',h'}(U,v)\|_*
\le\frac75\delta_f+\frac{19}{5}\delta_h.
\tag{4.9}
$$

The second assignment is a fixed point of $\Psi_{f',h'}$. Compare the two inputs using (4.8) and (4.9), bring the $(9/10)$ term to the left, and multiply by ten. This proves (4.2), since $|U-U'|=|u-u'|$.

**Proof of the complete-law bounds.** Couple emissions maximally while the two generators have the same configuration. After a matched letter use identical randomness for the same acquired update row. From the stationary p row, the surviving p subrow after $j$ returns is bounded by $\lambda^j\pi$, and its suspended subrow by $(2/3)\lambda^j\tau$. The mismatch hazards are $|u-u'|$ and $|v-v'|$. Summing them gives

$$
D_p:=\pi\operatorname{TV}(Q,Q')
\le\frac{15}{11}d_U+\frac{10}{11}d_v.
\tag{4.10}
$$

Starting at suspension gives a first hazard $d_v$ and a matched-alpha p subrow at most $(2/5)\pi$, hence

$$
D_\beta:=\tau\operatorname{TV}(W,W')
\le\frac6{11}d_U+\frac{15}{11}d_v.
\tag{4.11}
$$

These couplings include every return, the infinite outcome and all deterministic original event blocks. Almost-sure completion follows from (3.3); no finite terminal projection is substituted for a full law. Each bound is at most $(15/11)(d_U+d_v)$, which (4.2) bounds by $(210/11)\delta_f+(570/11)\delta_h$. These coefficients are at most $20,52$, proving (4.3).

**Proof of reconstruction.** The closed finite-dimensional cube is complete in (3.8). The projected map is a contraction by (4.8). Its iterates are Cauchy: the sum of successive increments is bounded by a geometric series. Their limit is a fixed point by continuity, and two fixed points would have distance at most $(9/10)$ of that same distance, so are equal. Actual data have the fixed point $(1-u,v)$ by Lemma 3.1. The cube diameter in (3.8) is

$$
\left(\frac23-\frac35\right)+\frac43\left(\frac25-\frac13\right)=\frac7{45}.
$$

Contraction gives (4.4). Applying (4.10)–(4.11) to the iterated and actual emissions gives (4.5). For data outside the actual readout image the projected map still has a fixed point, but that point need not reproduce the supplied data; existence of a projected fixed point is not a realization certificate. $\square$

The mature contraction principle and maximal coupling are tools in this proof. The new relation is the exact simultaneous elimination (3.6)–(3.7) and its all-shape inverse: two short stopped-event arrays suffice for every regular emission and the complete same-update future law on these acquired kernels. A generic rank or static moment inverse does not establish these feedback identities.

**Corollary 4.2 (joint completion criterion on prescribed acquired kernels).** Given the same acquired circulation and arbitrary arrays $F\in[0,M_f]^X$, $J\in[h_-,h_+]^Y$, let $(U_{F,J},v_{F,J})$ be the unique fixed point of $\Pi\Psi_{F,J}$ in $\mathcal C$. These arrays are the two event readouts of one regular same-update table on the prescribed $B,A$ if and only if

$$
\Psi_{F,J}(U_{F,J},v_{F,J})=(U_{F,J},v_{F,J}).
\tag{4.12}
$$

If so, that table's emissions and complete laws are unique. This is an exact mathematical criterion, not a finite-time decision algorithm for arbitrary real data or a claim that the table meets any minimax risk budget.

**Proof.** The projected map has a unique fixed point for all the specified data by the contraction proof above. A realizing table is fixed under the unprojected map by Lemma 3.1, hence under the projected map, proving necessity and uniqueness.

Conversely assume (4.12), set $u=1-U_{F,J}$, and generate the complete laws by (3.2) on the prescribed acquired kernels. They normalize by (3.3). With $g=\operatorname{diag}(U)B(1-v)$, the second unprojected equation gives $J=1-v+VAg$. Thus $v+J-1=VAg$, and the first unprojected equation becomes

$$
F=\operatorname{diag}(U)BJ+L^2g=g+Lg+L^2g.
$$

Equations (3.4) show that these generated laws have exactly the requested two readout arrays. No separately chosen phase decoder is spliced into this law pair. If an original-domain comparison is wanted, retain $C_0$ and its current-record renderer, use the original source-independent latch initialization $\pi$ after the third record write, and use precisely $B,A$ on the noncompleting acquired letters and in synthetic generation. This is the supplied product realization used in Proposition 7.1. The unweighted rows remain $\pi,\tau$ on every positive fourth-segment history, while every full tail comes from that same installed table. Mathematical real entries alone do not supply effective samplers; an effective implementation requires a separately charged finite representation and sampling procedure. $\square$

## 5. What simultaneous calibrated readouts force

The two readouts are jointly compared with their required endpoint midpoints. Define

$$
t_p=\|f-C\mathbf1\|_\pi,
\qquad t_\beta=\|h-H\mathbf1\|_\tau.
\tag{5.1}
$$

**Lemma 5.1 (the unique calibrated phase-asymmetric law).** There is a unique regular constant emission pair $(u_*,v_*)$ whose p and suspended event masses are $C,H$. On every acquired circulation it generates the same constant-law pair $(G_*,W_*)$. If a regular table has $f=C\mathbf1$ and $h=H\mathbf1$, all its emissions equal this pair and all its generated phase laws equal $G_*,W_*$.

**Proof.** Let $S(t)=1+t+t^2$ and put

$$
g(t)=\frac{C}{S(t)},\qquad U(t)=t+g(t),
\qquad v(t)=\frac{t}{U(t)},\qquad u(t)=1-U(t).
\tag{5.2}
$$

Then $U(1-v)=g$, $Uv=t$ and the p event mass is exactly $C$. The suspended event mass is $h(t)=1-v(t)+v(t)g(t)$. At the rational endpoints $t_0=233/1000$, $t_1=117/500$,

$$
h(t_0)-H=\frac{1703748888347}{4015751307792750}>0,
\qquad
h(t_1)-H=-\frac{251260555397}{502971865044750}<0.
\tag{5.3}
$$

All the pairs in this interval are regular. To check this without a numerical approximation, $51/100<C<13/25$ and $32/25<S(t)<13/10$ there. Thus

$$
\frac{51}{130}<g(t)<\frac{13}{32},
\qquad
\frac35<\frac{233}{1000}+\frac{51}{130}
<U(t)<\frac{117}{500}+\frac{13}{32}<\frac23.
$$

The same bounds give

$$
\frac13<\frac{233/1000}{117/500+13/32}
<v(t)<\frac{117/500}{233/1000+51/130}<\frac25.
$$

Continuity and (5.3) give a root $t_*\in(t_0,t_1)$. Let $u_*,v_*,g_*$ be (5.2) there. Its constant laws are

$$
G_*(w_{j,0})=u_*t_*^j,
\qquad G_*(w_{j,1})=g_*t_*^j,
\qquad
W_*=(1-v_*)\delta_\beta+v_*\alpha G_*.
\tag{5.4}
$$

They normalize because $u_*+g_*+t_*=1$. The phases have different emissions: $C>103/200$ and $S(t)<129/100$ on the chosen interval give $U(t)>631/1000$. Since $U(t)>1/2$, one has $U(t)(1-U(t))<232839/10^6<233/1000\le t$, and thus $v(t)>u(t)$. A constant pair obeys (3.2) on any stochastic $B,A$. Theorem 4.1 gives uniqueness of every regular assignment having these two constant readouts, including any other regular constant pair. This proves all assertions. $\square$

This is a comparison law, not an asserted near-optimal original observer. The algebraic root is not a free exact-real physical sampler.

**Lemma 5.2 (evaluated endpoint comparison).** The law $G_*$ satisfies

$$
\max_{r\in\{a,b\}}\operatorname{TV}(G_*,P_{p,r})
>\rho_p+\frac1{25000}.
\tag{5.5}
$$

**Proof.** The larger endpoint mass on $w_{3,1}$ is $q_*=1944/390625$. The function $Ct^3/S(t)$ is strictly increasing for $t>0$, since its derivative has numerator $Ct^2(3+2t+t^2)>0$. Direct rational arithmetic gives

$$
\frac{Ct_0^3}{S(t_0)}-q_*-\frac1{12500}
=\frac{445572012107}{29326052531250000}>0.
\tag{5.6}
$$

Thus $G_*(w_{3,1})>q_*+1/12500$. For any probability law $D$ on the complete carrier,

$$
\operatorname{TV}(D,P_{p,a})+\operatorname{TV}(D,P_{p,b})-2\rho_p
=\sum_w\operatorname{dist}\bigl(D(w),
 [P_{p,a}(w)\wedge P_{p,b}(w),P_{p,a}(w)\vee P_{p,b}(w)]\bigr).
\tag{5.7}
$$

This is the supplied coordinate triangle identity [CLIP, equation (3.6)], obtained by applying $|x-y|+|x-z|-|y-z|=2\operatorname{dist}(x,[y\wedge z,y\vee z])$ to each coordinate. It includes the infinite atom. The $w_{3,1}$ contribution is greater than $1/12500$, proving (5.5). The singleton obstruction and endpoint-box mechanism are existing supplies [PAID, Section 12]; their numerical comparison is used here inside the new inverse bridge. $\square$

**Theorem 5.3 (regular-table risk/readout compatibility).** Let a regular table on one acquired circulation have both endpoint configuration risks at most $\rho_p+e$ and $\rho_\beta+e$, respectively. Then

$$
e+20t_p+52t_\beta>\frac1{25000}.
\tag{5.8}
$$

**Proof.** Compare the table with the constant assignment of Lemma 5.1 on its same $B,A,\pi,\tau$. Theorem 4.1 yields

$$
\pi\operatorname{TV}(Q,G_*)\le20t_p+52t_\beta.
$$

For either endpoint, triangle inequality configuration by configuration gives

$$
\operatorname{TV}(G_*,P_{p,r})
\le\pi\operatorname{TV}(Q,P_{p,r})+
     \pi\operatorname{TV}(Q,G_*)
\le\rho_p+e+20t_p+52t_\beta.
$$

Combine with (5.5). This uses one entire generated law pair and the actual common acquired circulation. $\square$

The endpoint assumptions alone suffice here. Every additionally supported interior target and every supplied motion, directional, interiority, residual and return constraint must still be met by a proposed common attainer. Nothing in the proof removes those targets or restricts the remaining kernels to a previously excluded class.

## 6. Returning to arbitrary original finite observers

For the fibre (1.3), define centered same-history diagnostics

$$
\mathcal T_p(M)=\sup_{h\text{ p on the fibre}}
 \sum_z\rho_h(z)|D_z(E_p)-C|,
$$

$$
\mathcal T_\beta(M)=\sup_{h\text{ suspended on the fibre}}
 \sum_z\rho_h(z)|D_z(E_\beta)-H|.
\tag{6.1}
$$

These use the actual unweighted acquired configuration rows. They are not synthetic conditioning rows and impose no extra capability.

**Reused common-row and clipping statements.** [PAID, Lemma 14.1] extracts from every original observer one finite support-closed stationary table on this held-record fibre, with the same acquired $B,A$, copied complete laws and $\pi B=\tau,\tau A=\pi$. Its two configuration risks against every supported pure depth are bounded by the respective original risks. Every positive-row label is an original reachable configuration. Any bounded nonnegative state statistic, including each summand in (6.1), has extracted expectation at most its worst-positive-history expectation.

For completeness, the common-object feature comes from paid histories, not a runtime posterior. At the seed boundary the equal-pair update matrices have powers converging along finite recurrent periods. Choose rejection exponents with alpha and beta proportions tending to each supported $r_k$, then append the same suffix (1.3). The observer row tends to one common row, independent of $k$. The likelihood ratio to every competing depth contains $\exp[-2n\operatorname{KL}(\operatorname{Ber}(r_k)\Vert\operatorname{Ber}(r_i))]$ with uniformly bounded rounding factors. All $r_i\in[a,b]$, so the suffix ratios and rounding factors are uniformly bounded. Multiplication by $\mu(i)/\mu(k)$ gives a summable dominating sequence, proving concentration also for countable priors. Appending any fixed finite return preserves these conclusions. Cesaro averages of the common row under $BA$ yield $\pi BA=\pi$ and $\tau=\pi B$. Finite-row limits and averaging preserve the risk and bounded-statistic inequalities. A positive stationary coordinate was positive after some finite return and then after a sufficiently late finite paid approximant, proving actual reachability. Nonnegative flow forbids a retained label from transitioning to a deleted zero-row label. This is the existing source-specific extraction, with no new source draw, reset or query.

[CLIP, Theorem 3.1 and equations (3.7)–(3.10)] supplies the clipping estimates used on this extracted stationary support. Clip both emissions to $[a,b]$, keep these acquired kernels and rows, and regenerate the full laws. With $e=e(M)$, this regular table obeys

$$
\widehat e\le\frac{61}{11}e,
\quad
\pi\operatorname{TV}(Q,\widehat Q)\le\frac{50}{11}e,
\quad
\tau\operatorname{TV}(W,\widehat W)\le\frac{42}{11}e.
\tag{6.2}
$$

To specify the specialization without a further change of the extracted kernels, let
$D_u=\pi|u-\widehat u|$ and $D_v=\tau|v-\widehat v|$. The two endpoint risk bounds and the supplied coordinate identity (5.7), applied configuration by configuration, give $D_u,D_v\le2e$: the p coordinate $\alpha$ has mass $u_x$, and the suspended coordinate $\beta$ has mass $1-v_y$. In the supplied old-versus-clipped coupling, the still-matched paths are dominated by the clipped survival kernel
$\widehat L\le(4/15)BA$. Hence on these very rows and kernels,

$$
\pi\operatorname{TV}(Q,\widehat Q)
\le\frac{15D_u+10D_v}{11}\le\frac{50e}{11},
\qquad
\tau\operatorname{TV}(W,\widehat W)
\le\frac{6D_u+15D_v}{11}\le\frac{42e}{11}.
$$

Here $\widehat e$ is the maximum of the clipped table's two pure-depth configuration-risk suprema over all $k$ with $\mu(k)>0$, minus their respective radii. The supplied original product realization equates these suprema to its all-positive-history configuration risks. Adding the displayed distances to the extracted risks for every supported pure depth, then taking the suprema, gives
$\widehat e\le e+50e/11=61e/11$. This is the supplied clipping argument specialized to a period-one common row, not a second periodicization or a new clipping result. It applies to arbitrary original zero/unit emissions and possible original noncompletion mass. Transient configurations need not survive extraction; the reachable-fibre ranges and history suprema still include them. No original regularity, coherence-defect budget or resource-preservation premise is assumed.

**Theorem 6.1 (original centered-readout compatibility).** Every original observer of Section 2 satisfies

$$
295e(M)+20\mathcal T_p(M)+52\mathcal T_\beta(M)
>\frac1{25000}.
\tag{6.3}
$$

**Proof.** Extract the common support just described, keeping the two centered state statistics. Their expectations are at most $\mathcal T_p,\mathcal T_\beta$. For each event, changing a law by TV distance $d$ changes its probability by at most $d$, and hence changes its centered absolute readout by at most $d$. Thus the clipped table has

$$
\widehat t_p\le\mathcal T_p+50e/11,
\qquad
\widehat t_\beta\le\mathcal T_\beta+42e/11.
$$

Apply Theorem 5.3 to that one table. The resulting upper bound for its left side is

$$
\frac{61+20\cdot50+52\cdot42}{11}e
 +20\mathcal T_p+52\mathcal T_\beta
=295e+20\mathcal T_p+52\mathcal T_\beta.
$$

This proves (6.3). Clipping alters comparison forecasts, while every extracted decoder and diagnostic before clipping belongs to the original common observer. $\square$

**Proof of Theorem 1.1.** On the unmodified extracted table let $\bar f=\pi f$ and $\bar h=\tau h$. The endpoint event values are

$$
P_{p,a}(E_p)=412/729=C+\rho_p,
\quad P_{p,b}(E_p)=7299/15625=C-\rho_p,
$$

$$
P_{\beta,a}(E_\beta)=22/27=H+\rho_\beta,
\quad P_{\beta,b}(E_\beta)=93/125=H-\rho_\beta.
\tag{6.4}
$$

Projection to the event contracts TV and averaging cannot increase configuration loss. The two endpoint bounds therefore imply

$$
|\bar f-C|\le e,\qquad |\bar h-H|\le e.
\tag{6.5}
$$

Every positive extracted label is reachable on the designated original fibre. The mean $\bar f$ belongs to the convex hull of its reachable p event values, and similarly for $\bar h$. Every reachable event value is consequently within $\mathcal O_p$ of $\bar f$, or $\mathcal O_\beta$ of $\bar h$. This remains true at every actual positive-history row on the fibre, including rows not retained by extraction. Hence

$$
\mathcal T_p\le\mathcal O_p+e,
\qquad \mathcal T_\beta\le\mathcal O_\beta+e.
$$

Substitute these into (6.3), giving $(295+20+52)e=367e$ and proving (1.5). Setting both ranges to zero proves the strict individual bound (1.6); taking an infimum gives its non-strict version. Setting $e=0$ proves (1.7), and taking a liminf proves (1.8). $\square$

This lift is universal over original arbitrary finite kernels. It does not assert that the regular comparison preserves $\Delta_4$, $\Delta_{\rm all}$, a fixed state budget or total charged resources. No such preservation is needed for a necessary inequality on the original observer.

## 7. Neither one readout alone determines the emissions

**Proposition 7.1 (lawful paired counterexamples to one-readout inversion).** There are regular original product observers with $f=C\mathbf1$ and unequal emissions and complete p laws. There are also such observers with $h=H\mathbf1$ and unequal emissions and complete p laws.

**Proof.** Take two p and two suspended labels, fair rows and $B=A=I$. These are two persistent singleton components on one source-independent randomized initializer. For the first example use (5.2) separately with $t=23/100$ and $t=7/30$. The resulting regular emissions are

$$
(u_0,v_0)=
\left(\frac{68771837}{187046820},\frac{215103843}{591374915}\right),
\quad
(u_1,v_1)=
\left(\frac{42933491}{117348750},\frac{27381375}{74415259}\right).
$$

Both p event readouts equal $C$ by construction. The first pair is the supplied phase-p model A of [PH, Theorem 2.1]; it is reused as a comparison component, without a new attainment claim. The suspended readouts are respectively

$$
\frac{11570335464}{14784372875},
\qquad \frac{870126854}{1116228885},
$$

which are unequal. The p laws differ already on alpha because $u_0\ne u_1$.

For the second example choose $v_0=367/1000$, $v_1=369/1000$ and set

$$
g_i=1-c/v_i,\qquad U_i=g_i/(1-v_i),\qquad u_i=1-U_i.
$$

Then $h_i=1-v_i+v_i g_i=H$. The regular p emissions are

$$
u_0=\frac{2319397}{6272397},\qquad
u_1=\frac{2279653}{6286653},
$$

and the p event readouts are respectively

$$
\frac{1483518258989}{2894441502429},
\qquad \frac{1500952786739}{2891854093347},
$$

which are unequal. All regularity inequalities follow by cross-multiplication against $a,b$. The probabilities of infinite noncompletion are zero by (3.3).

Install each table using the existing original product construction: keep $C_0$, use fair synthetic letters before the third latch, sample the fair label independently in the update that writes the third record and then latches, and use $B,A$ on the original noncompleting acquired letters. Completing letters clear private labels and retain the original matching pendingStop and unique Stop. On every record fibre, the decoder is exactly the same finite program's generated full law. Induction over original operations preserves all records, permissions, seeds, markers and paid histories. The examples add neither a source action nor a hidden depth or clock. $\square$

These examples only show the need for the paired readouts in the inverse. They are not near-optimal witnesses and are not asserted independent of every earlier excluded subclass.

## 8. Source correspondence and a task-relative whitebox path

The actual-law relation (3.6)–(3.7) is an original-source correspondence: $B$ is exactly the acquired p-beta update, $A$ exactly the acquired suspended-alpha update, both phase rows are the same actual circulation, and each event probability is generated by the same complete program. The raw renderer transports the full record-bearing law and commutes with the operation blocks. These facts bind the inverse and its risk consequence to the original task rather than to separate fitted distributions.

The common-row extraction and clipping use existing comparison constructions, with changed forecasts explicitly regenerated. They never turn synthetic conditioning into the actual acquired row. The inverse theorem itself does not modify either update kernel. In particular $A Q$ may be nonnative, $u$ may vary on actual returns, and suspended emissions may be genuinely heterogeneous and interior. No native tag is inferred from an interior probability.

For a represented rational table, the two finite event arrays can be calculated from finite matrix products (3.4). Given the same known acquired kernels and these arrays, the reconstruction iteration (4.1) uses finite rational arithmetic and interval projections. It has the explicit semantic error bounds (4.4)–(4.5). Its data are model-law readouts, not samples that reveal the hidden source depth. Unknown kernels are not identified by Theorem 4.1, and a marginal two-number report $\pi f,\tau h$ is not the array input required for reconstruction.

All finite arrays, installed tables, intermediate numerators and denominators, workspace and output indices must be charged if this offline procedure is implemented. The geometric iteration rate is not a bit-complexity bound or a claim of free precision. Public real constants specify mathematical stochastic rules only. No exact-real oracle or physically exact sampler is supplied by the root in Section 5. For rational product examples, finite exact categorical sampling can use fresh independent bits and reusable finite workspace, all included in COMPLETE. Unbounded positive source rejection/return histories and sampler rejection attempts preclude a finite worst-case total execution bound. Source Reads, program/model description, retention, random bits, numerical work, synthesis/output, runtime, energy and physical preparation remain separate accounts.

**Corollary 8.1 (semantic whitebox quality for this task).** Fix one known acquired circulation $B,A,\pi,\tau$ and compare two regular same-update emission assignments on these same kernels. Their configuration-indexed paired readout discrepancies $\delta_f,\delta_h$ bound their weighted complete-law discrepancies by (4.3). This estimate compares the two specified generated models; it bounds error against an actual target only when that target has the stated same-kernel realization. Separately, an original model with both common configuration excesses zero must expose reachable semantic variation in at least one of these two explicit event readouts, quantitatively as (1.7).

**Proof.** The first assertion is exactly Theorem 4.1 on the supplied common kernels. The second is Theorem 1.1 on the original observer. Neither conclusion equates semantic response with internal implementation. Relabelings, different architectures and distinct implementations with the same lawful semantics remain possible. No classification of every trained network by FIB five windows is a hypothesis or consequence. $\square$

The next theoretical path is a joint construction or obstruction for the nonconstant paired readout arrays together with their shared acquired kernels and the full endpoint/interior configuration-loss boxes. Corollary 4.2 supplies the exact common-completion condition once those acquired kernels and arrays are prescribed. The inverse removes the possibility that both arrays are calibrated constants while other complete-law coordinates secretly carry all necessary variation. It does not remove the remaining nonconstant finite-kernel frontier. A prospective exact or vanishing construction must satisfy (4.12) and all original targets on one actual circulation; separately feasible arrays or independently optimized phase laws do not certify that joint solution.

## 9. Mathematical attribution and remaining alternatives

The source laws, full-record renderer, sharp phase radii, event masses, paid-history common rows, endpoint coordinate identity, clipping bounds and original product realization are supplied by [ST], [PH], [FLOW], [CLIP] and [PAID]. Sections 3–4 add the simultaneous nonlinear elimination and its uniform paired finite-readout inverse. Sections 5–6 consume that inverse to obtain the original-source paired-event restriction. Singleton law obstruction, contraction, coupling and interval projection are credited ingredients, not separately claimed new mathematical content.

The constant-parameter mixture exclusions, actual-return motion, alpha calibration/decrease, suspended interiority and heterogeneity, native acquired-residual restriction, and p-return conservation obstruction remain covered inputs with their existing scopes. The present proof assumes none of their excluded structural equalities. Its specific addition is that variation outside the two named finite-event arrays cannot satisfy the common risk problem when both arrays collapse: those arrays already control the entire regular generated law through the acquired update relation. This is stronger information than a requirement for some unspecified full-law diameter, without asserting that event variation is sufficient for joint attainment.

The latest paid-feedback result [KB, Section 31] concerns two versus three complete deterministic block fees on its actual full INITIAL support. Its separate legal children need not have one common literal completion. The authenticated-history results [ATOMIC, Sections 8–9] concern records paired with actual source/epoch histories. Their shared lesson is to retain the joint operation/source relation. No stopped-risk theorem, source port, preset action choice or observer clock is transferred from either result here; all used source/risk/update transport is instead proved by (2.1)–(3.7) and the supplied original paid-history extraction.

At the public comparison pin `1d46c8c01a8197d8ec786853ad532da21f640a47`, the complete bodies of [ST], [FLOW], [CLIP], [PAID], [NATIVE-ACQUIRED] and [KB] equal their cited scientific-snapshot bodies. [ATOMIC] includes its Section 10 correction for the finite-horizon endpoint of a fixed-radius substitution clock; its actual source/epoch Sections 8–9 remain unchanged. That deterministic known-origin clock supplies no acquired clock or stopped-risk premise here. The public exact-trace compiler, support-pruning and phase-replay descriptions [DEV-TRACE] use a bounded ordered-tree source, full coarse control histories, chronological raw caches and original route/verifier/acquisition phases. Their exact-prefix and nominal-table correspondences grant none of the original stochastic predictor's missing source observations, and do not prove a per-configuration complete-law or conf/conf risk correspondence. No transfer from these optional contextual inputs is invoked.

For primary literature, Monras and Winter [MW, Definition 5 and Theorem 6] describe positive realization of a specified stationary process by an invariant pointed polyhedral cone containing the prescribed terminal vector, invariant under the word maps, with the initial functional in its dual. Taghavian and Sjolund [TS, Sections I–III] study minimum positive Markov-form realizations of specified SISO transfer functions; the Markov-form minimum is generally an upper bound for the unrestricted positive-realization dimension. Those mature positive-realization methods motivate keeping state cones and their update maps together. No conclusion from them is used as attainment or obstruction for this common private-risk problem. Here the uncovered relation is derived directly from the original source's two phase equations.

Van den Bos and Vaandrager [BV, Definitions 7–11 and Figure 3] require legal adaptive tests and distinction through completed observable traces, with irreversible mergers affecting what later tests can distinguish. This supports the use of an operation-sensitive joint representation, rather than treating a recovered abstract history as an available runtime clock. Their testing theorem is not invoked to grant extra inputs to the stopped observer.

This is a bounded project and primary-literature comparison, not an exhaustive priority claim. Every supplied ordinary text remains fallible. For the original general-prior common conf/conf problem, exact common attainment, an unattained zero infimum, a positive unrestricted gap and fixed-resource optima remain different unresolved questions. The supplied exact two-endpoint-prior attainer is retained within its stated scope. The supplied rational near-optimal two-label witness retains its positive-excess upper bound; no vanishing family follows from it or from (1.5). The other three risk-order combinations retain their supplied scopes, and no new restriction for them is proved here. No finite theorem in this volume completes the continuing research goal.

## 10. Sources

Project mathematical references use the complete public scientific snapshot at `ca5d786446ea5c665e17596a4eea7cf4f891bfa4`, except the separately pinned phase-minimax and public p-return volumes. [DEV-TRACE] is contextual input at public comparison pin `1d46c8c01a8197d8ec786853ad532da21f640a47`.

- **ST:** [Randomized stopped-tail minimax](https://github.com/the-omega-institute/trureturing/blob/ca5d786446ea5c665e17596a4eea7cf4f891bfa4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md).
- **PH:** [Phase-coherent full-tail minimax](https://github.com/the-omega-institute/trureturing/blob/e36230b266eb5e9e1c05ee5a99778e4854d6bf9c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md), Theorem 2.1, for the separately attained full-prior phase minima.
- **FLOW:** [Flow-preserving rational frontier](https://github.com/the-omega-institute/trureturing/blob/ca5d786446ea5c665e17596a4eea7cf4f891bfa4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FLOW_PRESERVING_RATIONAL_FRONTIER.md).
- **CLIP:** [Risk-controlled emission moment feasibility](https://github.com/the-omega-institute/trureturing/blob/ca5d786446ea5c665e17596a4eea7cf4f891bfa4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md), especially Theorem 3.1.
- **PAID:** [Effective paid-history certificates](https://github.com/the-omega-institute/trureturing/blob/ca5d786446ea5c665e17596a4eea7cf4f891bfa4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md), especially Sections 11–14 and Lemma 14.1.
- **NATIVE-ACQUIRED:** [Native acquired-residual obstruction](https://github.com/the-omega-institute/trureturing/blob/ca5d786446ea5c665e17596a4eea7cf4f891bfa4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_RESIDUAL_OBSTRUCTION.md).
- **P-RETURN:** [Acquired-return p-emission variation](https://github.com/the-omega-institute/trureturing/blob/9b7d4777248e632bd64fdab914d1d834712c94ef/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md), public ordinary source independently of merge status.
- **KB:** [KBonacci self-calibrating boundaries](https://github.com/the-omega-institute/trureturing/blob/ca5d786446ea5c665e17596a4eea7cf4f891bfa4/docs/develop/theory/KBONACCI_SELF_CALIBRATING_BOUNDARIES.md), Section 31.
- **ATOMIC:** [Atomic boundary trichotomy](https://github.com/the-omega-institute/trureturing/blob/ca5d786446ea5c665e17596a4eea7cf4f891bfa4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md), Sections 8–9.
- **DEV-TRACE:** [Exact finite trace compiler](https://github.com/the-omega-institute/trureturing/blob/1d46c8c01a8197d8ec786853ad532da21f640a47/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.md), [exact support pruning](https://github.com/the-omega-institute/trureturing/blob/1d46c8c01a8197d8ec786853ad532da21f640a47/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.md), and [original completion phase replay](https://github.com/the-omega-institute/trureturing/blob/1d46c8c01a8197d8ec786853ad532da21f640a47/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.md), ordinary rendered public inputs; no fresh kernel verification is asserted here.
- **MW:** Alex Monras and Andreas Winter, [*Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem*, arXiv:1412.3634v1](https://arxiv.org/html/1412.3634v1), Definition 5 and Theorem 6.
- **TS:** Hamed Taghavian and Jens Sjolund, [*Minimal positive Markov realizations*, arXiv:2502.21102v3](https://arxiv.org/html/2502.21102v3), Sections I–III.
- **BV:** Petra van den Bos and Frits Vaandrager, [*State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2), Definitions 7–11 and Figure 3.

## 追加锚（本行以下为增补区）

## 11. Common complete-law flows and finite same-update regeneration

### 11.1 The fixed task and the complete-law domain

Throughout this chapter the source, installed prior, complete future, configuration-risk order and COMPLETE convention are exactly those of Section 2. In particular, $K$ is sampled once before the first paid Read, $\mu(1),\mu(2)>0$, and every supported depth remains a target. The original $C_0$, both accepted seeds, paid equal-pair rejections, full records, write-before-latch, permissions, fourth completion and matching Stop are retained. There is no prescribed hard marginalized-defect or total-resource budget. The finite tables used below belong to the regular stationary class $\mathfrak S_\mu$ of [PAID, Corollary 2.3]. Abstract finite stochastic rules and finitely represented exact samplers remain distinct notions.

Write $\Omega_p,\Omega_\beta$ for the two complete raw carriers of Section 2, and $\infty_p,\infty_\beta$ for their infinite noncompletion outcomes. Prefixing a suspended future by beta maps $\Omega_\beta$ bijectively onto $\Omega_p\setminus\{\alpha\}$; prefixing a p future by alpha maps $\Omega_p$ bijectively onto $\Omega_\beta\setminus\{\beta\}$. These maps also send the corresponding infinite outcomes to the infinite outcomes. On a current record fibre they include exactly the next original operation block, through $I_c$.

Put $\lambda=4/15$ and, for $j\ge0$, define the complete tail sets

$$
T_p(j)=\{w_{n,i}:n\ge j,\ i\in\{0,1\}\}\cup\{\infty_p\},
$$

$$
T_\beta(j)=\{\alpha w_{n,i}:n\ge j,\ i\in\{0,1\}\}\cup\{\infty_\beta\}.
\tag{11.1}
$$

The suspended completing word beta is outside $T_\beta(0)$. Define

$$
\mathcal K_p=\{Q\in\mathcal P(\Omega_p):
 a\le Q(\alpha)\le b,\quad Q(T_p(j))\le\lambda^j\ (j\ge0)\},
$$

$$
\mathcal K_\beta=\{W\in\mathcal P(\Omega_\beta):
 a\le1-W(\beta)\le b,\quad W(T_\beta(j))\le b\lambda^j\ (j\ge0)\}.
\tag{11.2}
$$

Here $\mathcal P$ means normalized probability laws, not subprobability vectors. Both spaces carry complete-law TV. Set

$$
u(Q)=Q(\alpha),\qquad U(Q)=1-u(Q),\qquad v(W)=1-W(\beta).
$$

For $Q\in\mathcal K_p$ and $W\in\mathcal K_\beta$, define the normalized residuals

$$
\mathcal R_B(Q)(E)=\frac{Q(\beta E)}{U(Q)},\qquad
\mathcal R_A(W)(E)=\frac{W(\alpha E)}{v(W)}.
\tag{11.3}
$$

The first residual is a probability law on $\Omega_\beta$, the second on $\Omega_p$. Neither is required to belong to the opposite $\mathcal K$ for an arbitrary descriptor. Their denominators satisfy $U\ge3/5$ and $v\ge1/3$. In particular the identities

$$
Q=u(Q)\delta_\alpha+U(Q)\beta\mathcal R_B(Q),\qquad
W=(1-v(W))\delta_\beta+v(W)\alpha\mathcal R_A(W)
\tag{11.4}
$$

hold on the entire carriers, including the infinite outcomes.

**Lemma 11.1 (normalized compact law spaces).** The spaces in (11.2) are convex and compact in TV. Every one of their laws has zero mass at its infinite outcome. The residual maps are TV-continuous, with the bounds

$$
\operatorname{TV}(\mathcal R_B(Q),\mathcal R_B(Q'))
 \le\frac{10}{3}\operatorname{TV}(Q,Q'),
$$

$$
\operatorname{TV}(\mathcal R_A(W),\mathcal R_A(W'))
 \le6\operatorname{TV}(W,W').
\tag{11.5}
$$

**Proof.** The emission and tail inequalities are affine closed constraints in the probability simplex. From each sequence of laws choose a subsequence on which every completed-word coordinate converges. For each $L$, the finite p set $\{w_{n,i}:n<L\}$ has complement $T_p(L)$ of mass at most $\lambda^L$. At suspension include beta in the finite set; its complement has mass at most $b\lambda^L$. The coordinate limits therefore have total mass one: their finite-set masses approach one uniformly as $L$ increases. Set the infinite coordinate to zero. Its value is also forced by $\Pr(\infty_s)\le\Pr(T_s(L))\to0$.

On a fixed finite set the subsequence converges in $\ell^1$. Outside that set the sum of the two tail masses bounds its $\ell^1$ difference by $2\lambda^L$, or $2b\lambda^L$. Thus the convergence is in complete-law TV. All inequalities survive this convergence. This proves sequential compactness, hence compactness in the metric spaces. The same affine constraints show that barycentres of Borel probability measures on either space remain in that space, by countable summation of coordinates. No mass is removed and no completion conditioning is used.

For normalized laws $P,P'$ and a common conditioning event of probability at least $q$ in $P'$, the conditional event difference is at most $2\operatorname{TV}(P,P')/q$, as proved in [CLIP, Theorem 3.1]. Apply this with the beta cylinder and $q=3/5$, or the alpha cylinder and $q=1/3$, and delete the next block. This gives (11.5). These are maps to the full opposite probability simplex, so continuity does not assume the additional opposite-space tail bounds. $\square$

### 11.2 Two conditional residual equations with common marginals

**Definition 11.2 (compatible complete-law flows).** A compatible pair is a Borel probability measure $\Gamma_B$ on $\mathcal K_p\times\mathcal K_\beta$ and a Borel probability measure $\Gamma_A$ on $\mathcal K_\beta\times\mathcal K_p$ with the same respective phase marginals:

$$
(\Gamma_B)_1=(\Gamma_A)_2=\nu_p,\qquad
(\Gamma_B)_2=(\Gamma_A)_1=\nu_\beta.
\tag{11.6}
$$

For every continuous real $\phi$ on $\mathcal K_p$, every continuous real $\psi$ on $\mathcal K_\beta$, and every atom $\eta\in\Omega_\beta$, $\omega\in\Omega_p$, require

$$
\int\phi(Q)\bigl(\mathcal R_B(Q)(\eta)-W(\eta)\bigr)
 \,d\Gamma_B(Q,W)=0,
$$

$$
\int\psi(W)\bigl(\mathcal R_A(W)(\omega)-Q(\omega)\bigr)
 \,d\Gamma_A(W,Q)=0.
\tag{11.7}
$$

The atom tests include the infinite outcomes. Denote this domain by $\mathfrak C$. Its flows are unweighted acquired flows: no factors $U(Q)$ or $v(W)$ are inserted into their marginals. Such factors enter only the synthetic recursions (11.4).

For a fixed $\eta$, the residual difference in the first equation of (11.7) defines a finite signed measure on $\mathcal K_p$ by projection. Annihilation of all continuous functions forces that signed measure to vanish. For example, continuous approximations to the indicator of a closed set, followed by bounded convergence and regularity, prove uniqueness of the signed measure. Consequently (11.7) also holds for every bounded Borel $\phi$, and likewise for $\psi$. Atomwise equalities give equalities of full measures on the countable carrier.

Equivalently, disintegrating these measures on their compact metric spaces gives

$$
\mathcal R_B(Q)=\int W\,\Gamma_B(dW\mid Q)
 \quad(\nu_p\text{-almost every }Q),
$$

$$
\mathcal R_A(W)=\int Q\,\Gamma_A(dQ\mid W)
 \quad(\nu_\beta\text{-almost every }W).
\tag{11.8}
$$

This interpretation conditions on the entire input descriptor. Conditioning only on its residual value would be weaker. A finite realization below does not require constructing these disintegrations. The descriptor spaces are mathematical carriers, not available continuous configuration registers.

Define the configuration losses against any complete raw target by

$$
\mathcal L_p(T)=\int\operatorname{TV}(Q,T)\,d\nu_p(Q),\qquad
\mathcal L_\beta(T)=\int\operatorname{TV}(W,T)\,d\nu_\beta(W),
$$

and define the joint excess

$$
\mathcal J(\Gamma_B,\Gamma_A)=
\max\left\{
 \sup_{k:\mu(k)>0}\mathcal L_p(P_{p,r_k})-\rho_p,
 \sup_{k:\mu(k)>0}\mathcal L_\beta(P_{\beta,r_k})-\rho_\beta
\right\},\qquad
j_c=\min_{\mathfrak C}\mathcal J.
\tag{11.9}
$$

TV remains inside each configuration integral. Formula (11.9) fixes the original targets; it neither optimizes them nor substitutes a new prior.

**Lemma 11.3 (compact feasible domain and attained analytic minimum).** $\mathfrak C$ is nonempty, convex and compact for weak convergence of its two measures. The minimum in (11.9) exists and lies in $[0,1]$.

**Proof.** Borel probability measures on a compact metric space are weakly sequentially compact. One elementary proof uses nested finite Borel partitions of diameter tending to zero. From any sequence select a subsequence with convergent masses on all cells of all partitions. These limiting masses are nonnegative, normalized and consistent under refinement. Subdivide the unit interval recursively according to these masses. Away from the countably many subdivision endpoints, each interval point selects a nested sequence of cells. The closures of those nonempty cells are nested compact sets with diameter tending to zero and hence specify a unique space point. Its distribution is a Borel probability measure. Uniform continuity shows that integrals of each continuous function along the subsequence converge to its integral against this distribution. This proves the stated compactness fact with normalized limits.

Apply this fact to the two compact products in Definition 11.2 and take one joint subsequence. Equalities of marginals are weakly closed, by testing continuous functions on each factor. Every integrand in (11.7) is continuous and bounded, by Lemma 11.1 and continuity of atom evaluation. Thus all the residual constraints are weakly closed. They are linear, as are (11.6), so $\mathfrak C$ is convex and compact.

For nonemptiness take the own complete laws of one singleton regular generator with $u=v=a$, and use point masses on its two ordered law pairs. Its return probability is $(1-a)a\le\lambda$, so those laws lie in (11.2); its recursions give (11.7). This is only a feasible law pair, with no zero-excess assertion.

For each fixed supported target, the function $Q\mapsto\operatorname{TV}(Q,P_{p,r_k})$ is bounded continuous; the suspended function is likewise. The supremum of these weakly continuous integrals is lower semicontinuous, even for countable support. Hence $\mathcal J$ attains its minimum on $\mathfrak C$. Integrating the endpoint triangle inequality gives

$$
\mathcal L_s(P_{s,a})+\mathcal L_s(P_{s,b})\ge2\rho_s,
$$

so each phase supremum is at least $\rho_s$ and $\mathcal J\ge0$. Every TV is at most one, giving the stated upper bound. Compactness and an attained analytic minimum supply neither the value $j_c$ nor a finite observer. $\square$

### 11.3 Regeneration from a possibly nonatomic pair

**Theorem 11.4 (finite common-flow regeneration).** Let $(\Gamma_B,\Gamma_A)\in\mathfrak C$ and $0<\varepsilon\le1$. There is one finite regular stationary table with positive rows $\pi,\tau$, acquired kernels $B,A$, and emissions $u,v$ such that

$$
\pi B=\tau,\qquad\tau A=\pi.
\tag{11.10}
$$

Its own complete laws $\widehat Q_i,\widehat W_j$ satisfy, for the cell barycentres $\bar Q_i,\bar W_j$ constructed below,

$$
\max_i\operatorname{TV}(\widehat Q_i,\bar Q_i)
 \le d_p^*=\frac{81}{44}\varepsilon,\qquad
\max_j\operatorname{TV}(\widehat W_j,\bar W_j)
 \le d_\beta^*=\frac{61}{44}\varepsilon.
\tag{11.11}
$$

For every complete probability target $T$ at the relevant phase, the same table has

$$
-(\varepsilon+d_p^*)\le
 \sum_i\pi_i\operatorname{TV}(\widehat Q_i,T)-\mathcal L_p(T)
 \le d_p^*,
$$

$$
-(\varepsilon+d_\beta^*)\le
 \sum_j\tau_j\operatorname{TV}(\widehat W_j,T)-\mathcal L_\beta(T)
 \le d_\beta^*.
\tag{11.12}
$$

The bounds are uniform over targets, including every original supported depth and every original posterior target. They hold after any common measurable projection of the future, using the projected losses. The finite table, rather than its barycentres, is the generator. Its two own-law flow measures can be chosen to converge jointly and weakly to the given pair as $\varepsilon\downarrow0$.

**Proof of the common finite flows.** Choose finite Borel partitions $(C_i)$ of $\mathcal K_p$ and $(D_j)$ of $\mathcal K_\beta$ whose cells have TV diameter at most $\varepsilon$. Finite covers by balls of radius $\varepsilon/2$, made disjoint in a fixed order, suffice. Delete zero-marginal cells. Put

$$
\pi_i=\nu_p(C_i),\quad\tau_j=\nu_\beta(D_j),\qquad
\bar Q_i=\frac1{\pi_i}\int_{C_i}Q\,d\nu_p(Q),\quad
\bar W_j=\frac1{\tau_j}\int_{D_j}W\,d\nu_\beta(W),
$$

$$
F^B_{ij}=\Gamma_B(C_i\times D_j),\quad
F^A_{ji}=\Gamma_A(D_j\times C_i),\qquad
B_{ij}=F^B_{ij}/\pi_i,\quad A_{ji}=F^A_{ji}/\tau_j,
$$

$$
u_i=\bar Q_i(\alpha),\qquad v_j=1-\bar W_j(\beta).
\tag{11.13}
$$

All barycentres are normalized complete laws in their respective spaces. Convexity and the cell diameters give

$$
\operatorname{TV}(Q,\bar Q_i)\le\varepsilon\quad(Q\in C_i),\qquad
\operatorname{TV}(W,\bar W_j)\le\varepsilon\quad(W\in D_j).
\tag{11.14}
$$

The first marginals make $B,A$ stochastic. The other marginals give

$$
\sum_i\pi_iB_{ij}=\sum_iF^B_{ij}=\tau_j,
\qquad
\sum_j\tau_jA_{ji}=\sum_jF^A_{ji}=\pi_i.
$$

A deleted zero-marginal cell has zero mass under both incident flows, so no positive-row transition enters it. The two flow identities hold exactly. Both emission vectors lie in $[a,b]$. In particular this is a single finite table; its two directional flows have not been optimized separately.

**Proof of the centroid residual bounds.** Use the bounded Borel tests $\mathbf1_{C_i}U(Q)$ and $\mathbf1_{D_j}v(W)$ in (11.7). Combining the resulting full-measure identities with (11.4) gives

$$
\bar Q_i=u_i\delta_\alpha+
 \frac1{\pi_i}\int_{C_i\times\mathcal K_\beta}U(Q)\beta W\,d\Gamma_B(Q,W),
$$

$$
\bar W_j=(1-v_j)\delta_\beta+
 \frac1{\tau_j}\int_{D_j\times\mathcal K_p}v(W)\alpha Q\,d\Gamma_A(W,Q).
\tag{11.15}
$$

There is no hypothesis that the centroids satisfy the finite-table recursion exactly.

For a probability measure $m$, a scalar $e$ of range width at most $\varepsilon$, its mean $\bar e$, and a measurable family of probability laws $H$, the signed covariance has mass zero and

$$
\left\|\int(e-\bar e)H\,dm\right\|_{\rm TV}
 \le\frac12\int|e-\bar e|\,dm\le\frac\varepsilon4.
\tag{11.16}
$$

Here the norm is half the $\ell^1$ norm of a zero-mass signed measure. The first inequality follows by summing coordinates and Tonelli. For $e\in[c,d]$ with mean $z$, the chord bound for $|e-z|$ gives

$$
\int|e-z|\,dm\le\frac{2(z-c)(d-z)}{d-c}\le\frac{d-c}{2};
$$

the zero-width case is zero. Thus (11.16) applies to integrals, not only finite sums. It is the covariance estimate supplied in [PAID, equation (9.14)].

In the first equation of (11.15), replace $W$ in each $D_j$ by $\bar W_j$. By (11.14) and $U\le2/3$, this costs at most $2\varepsilon/3$. Under the normalized restriction $\Gamma_B|_{C_i\times\mathcal K_\beta}/\pi_i$, the mean of $U$ is $1-u_i$. Its range width is at most $\varepsilon$, because atom evaluation is 1-Lipschitz in TV on $C_i$. Replace $U$ by this mean. Equation (11.16), applied to the probability-law family $\bar W_{j(W)}$, bounds the additional cost by $\varepsilon/4$. Its unweighted mean is exactly $\sum_jB_{ij}\bar W_j$. Therefore

$$
\operatorname{TV}\left(\bar Q_i,
 u_i\delta_\alpha+(1-u_i)\beta\sum_jB_{ij}\bar W_j\right)
 \le\left(\frac23+\frac14\right)\varepsilon=\frac{11}{12}\varepsilon.
\tag{11.17}
$$

Apply the same argument to the second equation of (11.15). Replacing $Q$ by its cell centroid costs at most $2\varepsilon/5$. The range of $v(W)$ on $D_j$ has width at most $\varepsilon$ and its conditional mean is $v_j$. Its covariance costs at most $\varepsilon/4$. The remaining unweighted mean is $\sum_iA_{ji}\bar Q_i$. Hence

$$
\operatorname{TV}\left(\bar W_j,
 (1-v_j)\delta_\beta+v_j\alpha\sum_iA_{ji}\bar Q_i\right)
 \le\left(\frac25+\frac14\right)\varepsilon=\frac{13}{20}\varepsilon.
\tag{11.18}
$$

These estimates retain the possible dependence between emission and successor law. Omitting that dependence would give a different, unjustified recursion.

**Proof of own-law generation and contraction.** Generate the finite table's complete laws using exactly its emissions and acquired kernels. With

$$
L=\operatorname{diag}(1-u)B\operatorname{diag}(v)A,
\qquad g=\operatorname{diag}(1-u)B(1-v),
$$

its p word masses are $(L^nu)_i$ and $(L^ng)_i$. Since $L\mathbf1\le\lambda\mathbf1$,

$$
\sum_{n<L_0}L^n(u+g)=\mathbf1-L^{L_0}\mathbf1,
\qquad L^{L_0}\mathbf1\le\lambda^{L_0}\mathbf1.
$$

Thus the word masses sum to one and the infinite outcome has mass zero. Suspension uses $(1-v_j)\delta_\beta+v_j\alpha\sum_iA_{ji}\widehat Q_i$, also normalized. Its tail in (11.1) is bounded by $b\lambda^{L_0}$. Infinite outcomes remain in both carriers, and no residual is lost by renormalization. These own laws satisfy

$$
\widehat Q_i=u_i\delta_\alpha+(1-u_i)\beta\sum_jB_{ij}\widehat W_j,
$$

$$
\widehat W_j=(1-v_j)\delta_\beta+v_j\alpha\sum_iA_{ji}\widehat Q_i.
\tag{11.19}
$$

These normalized recursions have a unique solution: two solutions with maximal phase distances $z_p,z_\beta$ would obey $z_p\le(2/3)z_\beta$ and $z_\beta\le(2/5)z_p$, so both distances vanish. The contraction is due to synthetic stopping, with no irreducibility or mixing assumption on $BA$.

Let $d_p,d_\beta$ be the maximum distances between these own laws and their centroids. Comparing (11.19) with (11.17)–(11.18) gives

$$
d_p\le\frac{11}{12}\varepsilon+\frac23d_\beta,
\qquad d_\beta\le\frac{13}{20}\varepsilon+\frac25d_p.
\tag{11.20}
$$

Since $1-(2/3)(2/5)=11/15$, substitution gives

$$
d_p\le\frac{15}{11}\left(\frac{11}{12}+\frac23\frac{13}{20}\right)\varepsilon
 =\frac{81}{44}\varepsilon,
$$

$$
d_\beta\le\frac{15}{11}\left(\frac{13}{20}+\frac25\frac{11}{12}\right)\varepsilon
 =\frac{61}{44}\varepsilon.
$$

Both constants come from (11.13) and its one own-law regeneration.

**Proof of the target-uniform losses.** For every p target $T$, configurationwise triangle inequality and centroid convexity give

$$
\sum_i\pi_i\operatorname{TV}(\widehat Q_i,T)
 \le\sum_i\pi_i\operatorname{TV}(\bar Q_i,T)+d_p
 \le\int\operatorname{TV}(Q,T)\,d\nu_p(Q)+d_p.
$$

Conversely, for $Q\in C_i$, (11.14) and (11.11) give $\operatorname{TV}(Q,\widehat Q_i)\le\varepsilon+d_p^*$. Integrate the reverse triangle inequality to get the lower bound in (11.12). Use $\tau,W$ for suspension. Every step works after pushing all laws and the target through a common measurable projection, since TV contracts and centroid formation commutes with pushforward. The corresponding marginal-law losses also differ by at most $d_s^*$, since the old mean law is exactly the weighted mean of its centroids. These marginal comparisons do not replace the configuration comparisons.

Finally, push $\Gamma_B$ forward by $(Q,W)\mapsto(\widehat Q_{i(Q)},\widehat W_{j(W)})$, and push $\Gamma_A$ forward by the reversed corresponding map, defining the maps arbitrarily on deleted marginal-null cells. The resulting measures have masses $F^B_{ij},F^A_{ji}$ on the generated law pairs. By (11.10) and (11.19) they are exactly the finite table's compatible own-law flows, even when generated labels share a law. On each product the transport changes the sum-of-phase-TV distance by at most

$$
2\varepsilon+d_p^*+d_\beta^*=\frac{115}{22}\varepsilon.
$$

Uniform continuity of every continuous function on the compact products proves joint weak convergence of these two pushforwards to the original pair. Thus $\mathfrak C$ is the weak closure of the compatible flows embedded from finite regular tables; no independent selection of a phase limit is involved. $\square$

### 11.4 Original histories and complete resources

Install the finite table of Theorem 11.4 by [PAID, Lemma 2.1.1], with the entire original $C_0$ as a component. Before the third latch use fair synthesis and original control updates. In the same third-completion update, perform the original record write and latch before sampling the source-independent private row $\pi$. Use $B$ after an actual p-beta and $A$ after an actual suspended-alpha, as well as in synthetic generation. Completing letters clear the labels and enter precisely their original matching pendingStop; Stop and delivery keep their original rules.

Induction over original operations preserves every record, seed, marker, flag and permission. At the first fourth-segment p cut the private row is $\pi$. Equation (11.10) makes the row $\tau$ after any noncompleting p-beta and $\pi$ after any suspended-alpha return. This holds on every positive finite acquired fourth-segment history, on every original record fibre. Conditioning on actual letters does not weight private configurations by synthetic probabilities. Private initialization and all updates are source-independent, and the actual source remains the single originally sampled $K$.

For any such history, pull its target back through $I_{C_0(h)}$:

$$
T_{s,h}=\sum_k\nu_h(k)P_{s,r_k}.
$$

This is a normalized countable mixture under the fixed original prior, incorporating every paid rejection and partial parse. For example,

$$
\int\operatorname{TV}(Q,T_{p,h})\,d\nu_p(Q)
 \le\sum_k\nu_h(k)\int\operatorname{TV}(Q,P_{p,r_k})\,d\nu_p(Q).
\tag{11.21}
$$

The target convexity in (11.21) is applied to each descriptor before integrating; it does not move TV outside the configuration average. Equation (11.12) applies to $T_{s,h}$ itself. Rendering then preserves these complete-law inequalities, including all future records, original operation blocks and the matching Stop. Hence

$$
R_{\mathrm{conf},p}(\widehat M)
 \le\sup_{k:\mu(k)>0}\mathcal L_p(P_{p,r_k})+\frac{81}{44}\varepsilon,
$$

$$
R_{\mathrm{conf},\beta}(\widehat M)
 \le\sup_{k:\mu(k)>0}\mathcal L_\beta(P_{\beta,r_k})+\frac{61}{44}\varepsilon.
\tag{11.22}
$$

The exact equality of a finite stationary table's phase suprema with its supported pure-depth suprema is [CLIP, Proposition 2.3]. Its lower direction uses finite paid rejection histories concentrating at each supported depth and a fixed legal seed/marker suffix. The summable likelihood-ratio domination in [PAID, Lemma 14.1] covers countable priors. Thus using pure targets here retains the full original history problem, rather than replacing it with hypothetical pure-source experiments.

Only the finite table and label are retained with $C_0$. Cells, descriptors, both flow measures, their barycentres and posterior rows are mathematical construction data. They are not retained as a continuous register or exposed to the observer. For a represented table, installation data, selector and label addresses, numerical thresholds, sampler states, program, workspace and output indices belong to COMPLETE. Every acquired Read, fresh random bit, internal operation and synthetic output remains charged. Each finite approximant may have a different charged size or precision. No fixed COMPLETE budget, hard marginalized-defect bound, worst-case execution bound or physical exact-real sampler follows from (11.22).

### 11.5 Exact all-shape infimum correspondence

**Theorem 11.5 (the compact flow value is the regular infimum).** With exactly the unrestricted source-specific risk scope above,

$$
j_c=J(\mathfrak S_\mu)=J(\mathfrak E_\mu),
\qquad
\frac{11}{61}j_c\le J(\mathfrak M_\mu)\le j_c.
\tag{11.23}
$$

In particular $J(\mathfrak M_\mu)=0$ if and only if a compatible pair has $\mathcal J=0$. A strictly positive $j_c$ is equivalent to a strictly positive unrestricted original gap. These are equivalences without an evaluation of either alternative.

**Proof.** Start with one finite stationary regular table on positive labels. Its own laws belong to (11.2) by the regular survival bound. Push the two finite acquired flows forward to laws:

$$
\Gamma_B=\sum_{x,y}\pi_xB_{xy}\delta_{(Q_x,W_y)},\qquad
\Gamma_A=\sum_{y,x}\tau_yA_{yx}\delta_{(W_y,Q_x)}.
\tag{11.24}
$$

Both are probability measures. Their shared marginals are $\sum_x\pi_x\delta_{Q_x}$ and $\sum_y\tau_y\delta_{W_y}$. The exact same-update recursions (3.2), divided by their positive continuation probabilities, give (11.7), including when different labels have identical laws. Configuration-before-TV risks are unchanged by this pushforward. The all-history equality just cited gives $\mathcal J=e(M)$. Taking the infimum over every finite shape proves $j_c\le J(\mathfrak S_\mu)$.

Conversely, take one compatible pair, without a finite-support assumption. For each $\varepsilon>0$, Theorem 11.4 and its original product realization give one finite same-update observer with

$$
e(\widehat M)\le\mathcal J(\Gamma_B,\Gamma_A)+\frac{81}{44}\varepsilon.
$$

Taking $\varepsilon\downarrow0$ proves $J(\mathfrak S_\mu)\le\mathcal J$ for this pair, hence $J(\mathfrak S_\mu)\le j_c$. This converse starts with measure-valued law flows rather than a supplied finite observer. The stationary/periodic equality and the two original-class inequalities are exactly [PAID, Corollary 2.3], which uses [CLIP, Theorem 4.2]. Their hypotheses retain the original complete-law targets, paid histories and same-update observer class; they impose no resource or hard-defect preservation. The equivalences follow from these inequalities, nonnegativity and Lemma 11.3. $\square$

### 11.6 Rational approximants preserve both flows

**Lemma 11.6 (one finite circulation can be rationalized).** Every finite table produced by Theorem 11.4 has rational regular stationary tables of the same finite label shape converging in all its parameters. Their two unweighted flow identities hold exactly. Their complete configuration losses converge uniformly over all complete targets, and therefore over all original positive histories.

**Proof.** View $F^B,F^A$ in (11.13) as one directed bipartite circulation: edges run from p labels to suspended labels and back. Conservation holds at every vertex, and each directional edge total is one. A finite nonnegative circulation decomposes into finitely many directed simple cycles. To see this, follow positive outgoing edges from a positive edge; conservation prevents a dead end. A repeated vertex gives a directed cycle. Subtract its smallest edge flow, deleting at least one positive edge, and repeat. Finitely many subtractions finish the decomposition.

If cycle $c$ has $m_c$ edges in each direction and its coefficient is $h_c>0$, then

$$
(F^B,F^A)=\sum_c w_c Z_c,\qquad
Z_c=\frac1{m_c}\mathbf1_{\text{edges of }c},\qquad
w_c=m_ch_c,\quad\sum_cw_c=1.
\tag{11.25}
$$

Each $Z_c$ is rational, conserved and has each directional total one. Approximate the positive weights by positive rational weights summing exactly to one. This preserves conservation and both directional totals, as well as every positive edge in the given cycle support. The resulting rational vertex masses $\pi',\tau'$ converge to the positive original masses. Dividing incident flows by those masses gives rational stochastic $B',A'$ with $\pi'B'=\tau'$ and $\tau'A'=\pi'$, converging to $B,A$. Approximate $u,v$ rationally inside the same closed rational interval $[a,b]$. Thus the two phase tables are approximated jointly, with no stationary-row repair assumed after separate rounding.

For completeness, put

$$
x_u=\max_i|u_i-u_i'|,\quad x_v=\max_j|v_j-v_j'|,
\quad x_B=\max_i\operatorname{TV}(B_{i,\cdot},B'_{i,\cdot}),
\quad x_A=\max_j\operatorname{TV}(A_{j,\cdot},A'_{j,\cdot}).
$$

Generate both tables' own normalized complete laws. Their maximal law differences satisfy

$$
z_p\le x_u+\frac23x_B+\frac23z_\beta,
\qquad z_\beta\le x_v+\frac25x_A+\frac25z_p.
\tag{11.26}
$$

Changing a Bernoulli emission costs its absolute difference; changing a successor row costs its TV by contraction through a probability-law kernel. The remaining terms are the continuing-law differences. Solving (11.26) shows $z_p,z_\beta\to0$. This argument compares the full normalized laws; its geometric stopping justification is the same as in (11.19).

For every complete target $T$, the difference of configuration losses at p is at most

$$
z_p+\operatorname{TV}(\pi,\pi'),
\tag{11.27}
$$

because the law-wise reverse triangle bound is $z_p$, and each remaining loss is a function with values in $[0,1]$. Suspension uses $z_\beta+\operatorname{TV}(\tau,\tau')$. These bounds do not depend on $T$. Both tables have their stationary rows on every acquired fourth history and the identical original posterior targets, so (11.27) gives the claimed full-history uniformity. $\square$

**Corollary 11.7 (represented infimum and the conditional tolerance family).** Let $\mathfrak S_\mu^{\mathbb Q}$ denote the stationary regular tables with rational latch rows, kernels and emissions, installed using the supplied finite exact categorical-sampling convention. Then

$$
J(\mathfrak S_\mu^{\mathbb Q})=j_c.
\tag{11.28}
$$

If a compatible pair with $\mathcal J=0$ is supplied, then for every $0<\eta\le1$ there is one rational finite COMPLETE observer with both original configuration excesses at most $\eta$.

**Proof.** Rational tables are included in $\mathfrak S_\mu$. Apply Lemma 11.6 to each finite table approaching $j_c$ in Theorem 11.5, choosing an arbitrarily small additional loss. This proves (11.28). For the conditional statement choose $\varepsilon=22\eta/81$ in Theorem 11.4, so its maximal added loss is at most $\eta/2$, and rationalize that one table to add at most $\eta/2$.

A fixed rational categorical distribution can be sampled exactly using fresh independent fair bits, finite rational thresholds and reusable finite rejection workspace. The program, threshold representation, latch selector, cursors and all sampler microstates are finite and charged; the same represented sampler implements acquired and synthetic updates. Almost-sure termination of this internal service adds no source query or operation permission. Unbounded possible rejection attempts, paid source rejections and legal returns still have no finite worst-case bit or time bound. Thus each chosen table is separately represented and finite. This is an existence statement for finite effective members, not an algorithm taking an arbitrary nonatomic real measure as finite input. Without the zero-level premise it provides no vanishing-excess family. $\square$

### 11.7 Finite atomicity and exact attainment

**Theorem 11.8 (analytic minimizers and finite attainability).** For any compatible pair with both phase marginals finitely supported, there is a finite regular stationary table whose own laws are precisely those marginal atoms and whose configuration losses against every target are exactly $\mathcal L_p,\mathcal L_\beta$. Consequently:

1. The regular value $j_c$ is attained by an abstract finite stationary table if and only if some minimizing compatible pair has finitely supported phase marginals.
2. A finite abstract common conf/conf attainer exists in the original class $\mathfrak M_\mu$ if and only if a zero-level compatible pair has finitely supported phase marginals.

Finite support of both marginals is equivalent here to finite support of both flow measures.

**Proof.** Write

$$
\nu_p=\sum_i\pi_i\delta_{Q_i},\qquad
\nu_\beta=\sum_j\tau_j\delta_{W_j},\qquad \pi_i,\tau_j>0,
$$

with distinct atoms at each phase. Both flow measures are supported on the respective finite products, because their marginals assign mass one to those products. Define $B_{ij}=\Gamma_B(\{(Q_i,W_j)\})/\pi_i$ and $A_{ji}=\Gamma_A(\{(W_j,Q_i)\})/\tau_j$, and take emissions $u_i=Q_i(\alpha)$, $v_j=1-W_j(\beta)$. The margin equalities give both flow identities. The Borel indicator tests following Definition 11.2 isolate each input atom and give

$$
\mathcal R_B(Q_i)=\sum_jB_{ij}W_j,\qquad
\mathcal R_A(W_j)=\sum_iA_{ji}Q_i.
$$

Together with (11.4), these are exactly (11.19) for $Q_i,W_j$. The unique normalized solution established there shows that the descriptors are the table's own complete generated laws. Thus all losses agree exactly, rather than merely being compared to fitted centroid laws.

For assertion 1, this construction supplies the forward finite realization, and (11.24) embeds every finite minimizing table as a finitely supported minimizing pair. For assertion 2, a finite zero-level pair supplies an original product attainer by Section 11.4 and the separate lower minima. Conversely a finite abstract original attainer gives a finite regular stationary attainer by [CLIP, Theorem 4.2; PAID, Corollary 2.3], and (11.24) gives its finite zero-level pair. No equivalence of positive original and regular minimizers is inferred from the comparison factor. $\square$

**Effective boundary.** Theorem 11.8 concerns finite indexed stochastic rules with real entries. To turn its atomic witness into an effective exact observer, its resulting latch row, both acquired kernels and both emissions must admit allowed finitely represented exact sampling procedures, with all description and workspace charged to COMPLETE. Rational entries are a sufficient instance. Finite atomicity alone supplies no such sampler and does not imply rational exact attainment. In the represented stationary subclass, exact attainment is equivalent to an atomic zero-level witness with these sampler conditions. The abstract extraction from an arbitrary original attainer establishes the atomic criterion; without an additional sampler-preservation argument it does not establish an effective extraction theorem for every numerical representation convention.

An analytic minimizing pair may be nonatomic. Compactness alone therefore proves neither attainment at a finite label shape nor any total-resource optimum. Even a nonatomic zero-level witness gives only the conditional finite tolerance family of Corollary 11.7; Theorem 11.8 requires a possibly different finite atomic zero-level witness for exact finite attainment. The existence of one nonatomic minimizing pair does not exclude another atomic minimizer.

### 11.8 The zero face, mathematical correspondence and residual problem

At $\mathcal J=0$, both endpoint configuration risks at each phase equal their separate radii. Integrate the coordinate triangle identity (5.7). Its nonnegative right-hand side has expectation zero, so, for almost every descriptor and every complete atom,

$$
P_{s,a}(\omega)\wedge P_{s,b}(\omega)
 \le D(\omega)\le
P_{s,a}(\omega)\vee P_{s,b}(\omega).
\tag{11.29}
$$

The simultaneous almost-everywhere statement follows because the complete carrier is countable. Inside this coordinate box, the two endpoint distances are opposite signed differences on the endpoint-positive event. Their equality gives

$$
\int Q(E_p)\,d\nu_p(Q)=C,\qquad
\int W(E_\beta)\,d\nu_\beta(W)=H.
\tag{11.30}
$$

This is the supplied endpoint geometry of [CLIP, Theorem 6.2], now imposed on the same marginals as both residual equations. The coordinate boxes, event midpoint means and all supported interior losses must coexist with (11.7). Separately feasible phase marginals or two scalar calibrated reports need not have this simultaneous compatibility. When an atomic pair is realized, Section 4's inverse applies to its resulting fixed $B,A$ with its full indexed paired arrays; it does not identify the unknown kernels from (11.30).

The new source-relative inference is the implication from a compatible, possibly nonatomic pair of complete-law flows to one finite same-update generator with both full configuration losses controlled, and hence the equality with the all-shape regular infimum and the finite-atomicity criterion. [PAID, Theorem 9.2] already aggregates a supplied finite observer's circulation and proves the emission-successor covariance bound. Equations (11.15)–(11.20) extend that argument to measures without assuming a finite observer to begin with. [PAID, Section 10] already gives error-corrected bounded-shape certificates; [CLIP, Section 6] already gives compact completeness at a fixed finite shape. Those conclusions, standard probability compactness, conditional barycentres, Jensen's inequality and finite cycle decomposition are reused tools, not additional claims of novelty.

For a primary-literature comparison, Leskela and Vihola, *Conditional convex orders and measurable martingale couplings*, [arXiv:1404.0999v3](https://arxiv.org/html/1404.0999v3), Theorems 1.2–1.3, concern probability laws on $\mathbb R^d$ with finite first moments, or probability kernels from a measurable parameter space into $\mathbb R^d$ with that integrability at every parameter. Convex order is equivalent to a martingale coupling; Theorem 1.3 additionally supplies a measurable family of pointwise couplings. Finite completed-word probability projections and their normalized residual projections are bounded finite-dimensional vectors, so the singleton-parameter hypotheses hold for such projected distributions. This supplies mature finite-dimensional barycentric-coupling theory. It does not by itself condition on the entire original descriptor, lift a sequence of unrelated projected witnesses to two full-law flows with the same marginals, or regenerate a finite observer with configuration-before-TV losses. No convex-order converse or new Strassen theorem is needed in the direct proof above. The correspondence identifies a source-specific uncovered delta, without a global priority claim.

The suppliers used here have their full original hypotheses: [ST, Section 2.1] supplies complete stopped laws and the injective full-record renderer; [PAID, Lemma 2.1.1] supplies finite original-domain product realization; [PAID, Lemma 14.1] supplies common paid-history rows and countable-prior domination; [CLIP, Theorems 3.1 and 4.2] supplies complete-law clipping and the $61/11$ comparison; [PAID, Lemma 2.2 and Corollary 2.3] supplies finite stationary replacement in the unrestricted risk scope. These constructions do not preserve a preassigned total-resource or hard-defect budget. No reversible-candidate formula is a premise.

The self-calibration gained by (11.7) is calibration of common realization: the two phase distributions of complete predicted laws must have conditional residual barycentres carried by shared acquired marginals. It does not reveal $K$, install its posterior or evaluate the optimum. The paired-event inequality (1.5) remains a necessary restriction on finite constructions; [RETURN9, Theorem 9.3] remains an additional necessary restriction when the original installed prior supports a nonendpoint depth $k\ge3$. Their free event-range and acquired-return variation terms are not replaced by risk-only bounds.

For the fixed original installed support, the remaining mathematical question is whether the full endpoint faces (11.29), midpoint means (11.30), all supported configuration-loss bounds and both conditional residual equations admit a zero-level pair. If they do, finite atomicity with the sampler conditions decides the stated finite boundary; a general zero-level pair supplies finite positive-tolerance approximants. If the compact minimum is strictly positive, (11.23) transfers that evaluated positivity to the original unrestricted class. No zero-level pair, finite atomic zero-level pair or evaluated positive value is supplied here. The zero-versus-positive original infimum, its numerical value, finite exact attainment and fixed-resource optima consequently remain unresolved in the general-prior problem. The supplied two-endpoint-prior attainer and the supplied strictly positive-excess rational witness retain exactly their original scopes.

- **RETURN9:** [Acquired-return p-emission variation](https://github.com/the-omega-institute/trureturing/blob/47cbb149f0695bff742784a5cb367a6fd15147e6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md), Theorem 9.3.

## 追加锚（本行以下为增补区）
## 12. Four-moment full-law rigidity and its incompatibility consumer

**Standing assumptions 12.1 (the original domain and four coordinates).** Use exactly the fixed source and installed finite or countable prior of Section 11.1, with positive endpoint masses, every supported target, both seeds, all paid histories, source-independent initialization, original records, same-update rules, completion and Stop. The complete countable carriers and their noncompletion outcomes, the regular law spaces $\mathcal K_p,\mathcal K_\beta$, and both descriptor-conditioned residual equations are those of Definition 11.2. A compatible pair has the common **unweighted** marginals $\nu_p,\nu_\beta$ in (11.6); its losses are the configuration-before-TV integrals in (11.9). No finite support, reversibility, irreducibility, native-mixture representation or zero acquired-return variation is assumed.

Set $a=1/3$, $b=2/5$ and, for its two marginals, write

$$
m_p=\int u(Q)\,d\nu_p(Q),\qquad
m_\beta=\int v(W)\,d\nu_\beta(W),\qquad t=m_p+m_\beta,
$$

$$
q=\int Q(\beta\beta)\,d\nu_p(Q),\qquad
z=\int W(\alpha\alpha)\,d\nu_\beta(W).
\tag{12.1}
$$

These are complete raw words $w_{0,1}$ and $\alpha w_{0,0}$, with their original completion and Stop blocks supplied by $I_c$; $\alpha\alpha$ is not two further Reads after completion. Put

$$
J_p=\int(u-a)(b-u)\,d\nu_p,\qquad
J_\beta=\int(v-a)(b-v)\,d\nu_\beta,
$$

$$
M_B=\int(u(Q)-v(W))^2\,d\Gamma_B(Q,W),\qquad
M_A=\int(v(W)-u(Q))^2\,d\Gamma_A(W,Q).
\tag{12.2}
$$

**Theorem 12.2 (the synchronized endpoint-chord fibre).** Fix $0\le\theta\le1$. Among all compatible pairs of Definition 11.2, the four coordinates

$$
m_p=m_\beta=(1-\theta)a+\theta b,\qquad
q=(1-\theta)(1-a)^2+\theta(1-b)^2,\qquad
z=(1-\theta)a^2+\theta b^2
\tag{12.3}
$$

specify exactly one pair. Its marginals are

$$
\nu_p=(1-\theta)\delta_{P_{p,a}}+\theta\delta_{P_{p,b}},\qquad
\nu_\beta=(1-\theta)\delta_{P_{\beta,a}}+\theta\delta_{P_{\beta,b}},
\tag{12.4}
$$

and its flows are

$$
\Gamma_B=(1-\theta)\delta_{(P_{p,a},P_{\beta,a})}
             +\theta\delta_{(P_{p,b},P_{\beta,b})},
$$

$$
\Gamma_A=(1-\theta)\delta_{(P_{\beta,a},P_{p,a})}
             +\theta\delta_{(P_{\beta,b},P_{p,b})}.
\tag{12.5}
$$

In particular, prescribing both full barycentres to be $(1-\theta)P_{s,a}+\theta P_{s,b}$ prescribes this same unique compatible pair. The restriction (12.3) is essential to the assertion.

The native endpoint laws and endpoint-tag construction are supplied by [ST, Sections 2.1 and 2.4](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md). [Acquired-alpha calibration, Sections 5–6](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/docs/develop/theory/AURIC_FIB_ATOM_ACQUIRED_ALPHA_CALIBRATION_COMPATIBILITY.md) already supplies finite-table dynamic rigidity under exact endpoint calibration and zero alpha-emission change, and its consumed risk–update obstruction; [Directional alpha calibration, Theorem 3.1 and Proposition 5.1](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/docs/develop/theory/AURIC_FIB_ATOM_DIRECTIONAL_ALPHA_CALIBRATION.md) supplies a signed refinement. The classification here takes just the four barycentre coordinates (12.3), for any $\theta$, on arbitrary Borel full-law descriptors. It derives both endpoint-stratum preservation and full-law concentration, then excludes the nonnative marginal construction in Proposition 12.4.

**Proof.** Take $\phi(Q)=1-u(Q)$ and the suspended atom beta in the first equation of (11.7). Take $\psi(W)=v(W)$ and the p atom alpha in the second equation. Their positive residual denominators cancel, giving

$$
q=\int(1-u(Q))(1-v(W))\,d\Gamma_B(Q,W),\qquad
z=\int v(W)u(Q)\,d\Gamma_A(W,Q).
\tag{12.6}
$$

Neither multiplier changes a flow marginal. For $x\in[a,b]$, the elementary identity

$$
x^2=(a+b)x-ab-(x-a)(b-x)
$$

and the expansion of $(u-v)^2$ give, on either directional flow,

$$
2\int uv\,d\Gamma_s=(a+b)t-2ab-J_p-J_\beta-M_s,
\qquad s\in\{B,A\}.
$$

The shared unweighted marginals are used in both integrals of $u^2+v^2$. Since $q=1-t+\int uv\,d\Gamma_B$, (12.6) yields the exact identities

$$
D_B:=\frac{26}{15}-\frac{19}{15}t-2q=J_p+J_\beta+M_B,
$$

$$
D_A:=\frac{11}{15}t-\frac4{15}-2z=J_p+J_\beta+M_A.
\tag{12.7}
$$

At (12.3), $D_B=D_A=0$. Every term on the right is nonnegative. Thus $u,v$ take values only in $\{a,b\}$ almost surely, and $u(Q)=v(W)$ on each directional flow almost surely. Both flows preserve the two emission strata. Their respective common masses are $1-\theta,\theta$, as determined by either emission mean.

For an emission stratum $r\in\{a,b\}$ of positive mass, restrict and normalize the two marginals and flows, denoting them by $\nu_p^r,\nu_\beta^r,\Gamma_B^r,\Gamma_A^r$. The bounded Borel indicator extension following (11.7) and the full-descriptor conditional form (11.8) retain both residual equations on this stratum. The native complete laws satisfy

$$
P_{p,r}=r\delta_\alpha+(1-r)\beta P_{\beta,r},\qquad
P_{\beta,r}=(1-r)\delta_\beta+r\alpha P_{p,r}
$$

on the entire carriers [ST, Section 2.1]. Prefixing is a TV isometry, including the infinite outcomes. Define

$$
d_p^r=\int\operatorname{TV}(Q,P_{p,r})\,d\nu_p^r(Q),\qquad
d_\beta^r=\int\operatorname{TV}(W,P_{\beta,r})\,d\nu_\beta^r(W).
$$

Equations (11.4), (11.8) and TV convexity imply

$$
d_p^r\le(1-r)d_\beta^r,\qquad d_\beta^r\le r d_p^r.
\tag{12.8}
$$

For example, condition on the entire Q in the first inequality, compare its residual barycentre with $P_{\beta,r}$, and then integrate using $(\Gamma_B^r)_2=\nu_\beta^r$. Since $r(1-r)\le6/25<1$, (12.8) forces both distances to be zero. Each stratum therefore contains only its corresponding native complete law almost surely. The zero-mass strata contribute nothing, which also covers $\theta=0,1$. This proves (12.4), and emission matching proves (12.5).

Conversely, the native recursions verify both full residual equations for (12.5). Their tails are $[r(1-r)]^j$ and $r[r(1-r)]^j$, so the laws belong to (11.2). Their four coordinates are (12.3). No noncompletion mass is discarded: its vanishing is supplied by Lemma 11.1 and by the native geometric tails. This proves existence and uniqueness.

The bounded-square identity, TV convexity and contraction are mature tools. [Leskela and Vihola, Theorems 1.2–1.3](https://arxiv.org/html/1404.0999v3) supplies finite-dimensional convex-order and measurable martingale-coupling theory for laws with finite first moments. Bounded finite word/residual projections meet those integrability hypotheses, including on a singleton parameter space. That theorem does not itself prescribe both full-descriptor residual flows with these same marginals or classify this source-specific four-coordinate fibre; (12.6)–(12.8) give that inference directly. $\square$

**Corollary 12.3 (a restricted zero-face exclusion).** Suppose the fixed installed prior supports some $k\ge3$. No compatible pair with $\mathcal J=0$ satisfies (12.3) for any $\theta$. In particular its four coordinates cannot be

$$
(m_p,m_\beta,q,z)=\left(\frac{11}{30},\frac{11}{30},
                              \frac{181}{450},\frac{61}{450}\right).
\tag{12.9}
$$

This excludes the specified fibre only. Outside that fibre, the existence alternative in Theorem 11.5 and the finite-atomicity and represented exact-sampling requirements in Theorem 11.8 are unchanged. The unrestricted value $j_c$, finite exact attainment and hard-resource optima are not evaluated. The free $V_\pi$ in [RETURN9, Theorem 10.2] is not fixed or converted into a risk-only gap.

**Proof.** By Theorem 12.2 the p marginal is the endpoint-tag marginal. At $\mathcal J=0$, its endpoint event midpoint (11.30) forces $\theta=1/2$, because $P_{p,a}(E_p)-P_{p,b}(E_p)=2\rho_p>0$.

For every supported nonendpoint, $r=r_k\in[c,d]=[3/8,5/13]$. The complete word $w_{3,1}$ has native mass $f(r)=r^3(1-r)^5$. Its derivative is $r^2(1-r)^4(3-8r)$, so $f$ is nonincreasing on this interval. The larger endpoint mass is $f(b)=1944/390625$, and

$$
f(r)-\max(f(a),f(b))\ge
 g_*:=\frac{14219478376}{318644812890625}>0.
\tag{12.10}
$$

The coordinate triangle identity (5.7), applied to $P_{p,r}$ and the two endpoints, consequently gives

$$
\frac{\operatorname{TV}(P_{p,a},P_{p,r})+
       \operatorname{TV}(P_{p,b},P_{p,r})}{2}
\ge\rho_p+\frac{g_*}{2}>\rho_p.
$$

This contradicts that supported target's p loss bound in (11.9). The pure-target interpretation uses [CLIP, Proposition 2.3; PAID, Lemma 14.1], with the original paid histories and countable-prior domination. The interior-word excess and endpoint-tag failure are supplied by [ST, Section 3.3] and [NATIVE-MIXTURE, Section 6](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md); their use here is on the pair forced by four-moment rigidity. If the prior supports only depths 1 and 2, the supplied fair endpoint-tag pair does have $\mathcal J=0$, so the nonendpoint hypothesis cannot be omitted. $\square$

**Proposition 12.4 (separately full-risk-feasible, nonnative marginals with no common flow).** Let

$$
M_p=\frac{P_{p,a}+P_{p,b}}2,\qquad
M_\beta=\frac{P_{\beta,a}+P_{\beta,b}}2,\qquad
\varepsilon=\frac1{10000},
$$

$$
Q_\pm=M_p\pm\varepsilon(\delta_\alpha-\delta_{\beta\beta}),\qquad
W_\pm=M_\beta\pm\varepsilon(\delta_\beta-\delta_{\alpha\alpha}),
$$

$$
\nu_p=\frac{\delta_{Q_+}+\delta_{Q_-}}2,\qquad
\nu_\beta=\frac{\delta_{W_+}+\delta_{W_-}}2.
\tag{12.11}
$$

These are candidate descriptor marginals, not an observer. They belong to the original regular law spaces, satisfy every complete endpoint coordinate box in (11.29), have the full endpoint-midpoint barycentres and hence both event midpoint means in (11.30), and obey

$$
\int\operatorname{TV}(D,P_{s,r_k})\,d\nu_s(D)\le\rho_s
\quad\text{for every supported }k\text{ and }s\in\{p,\beta\}.
\tag{12.12}
$$

Nevertheless no compatible pair has these marginals. None of the four descriptors is a Borel mixture of native laws $P_{s,r}$ with $r\in[a,b]$. The respective native-law and native-successor-residual hypotheses of [NATIVE-MIXTURE](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md) and [NATIVE-ACQUIRED](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_RESIDUAL_OBSTRUCTION.md) are not premises of this proposition.

**Proof.** The changed p coordinates have half endpoint widths $1/30,19/450$; the changed suspended coordinates have half widths $1/30,11/450$. All exceed $\varepsilon$. Thus all four descriptors are nonnegative normalized laws inside the full endpoint boxes; all other coordinates are midpoint coordinates, including the zero infinite coordinates.

Write $h(r)=r(1-r)$. For $j\ge1$ their p tail masses are $(h(a)^j+h(b)^j)/2\le(6/25)^j\le\lambda^j$, and their suspended tail masses are $(a h(a)^j+b h(b)^j)/2\le b\lambda^j$. At $j=0$ the p mass is one; the suspended alpha-cylinder masses are $11/30\mp\varepsilon\le b$. The immediate emission bounds also hold. This verifies membership in exactly (11.2), without completion conditioning.

Their full barycentres are $M_p,M_\beta$. Within an endpoint coordinate box, the two endpoint TV distances are affine functions of the descriptor coordinates. Averaging (12.11) therefore makes both endpoint configuration losses exactly $\rho_s$. This proves (12.12) for $k=1,2$ while keeping TV inside the descriptor average.

For a complete-tail bound uniform over every nonendpoint depth, put $c=3/8$, $d=5/13$. All original parameters $r_k$ with $k\ge3$ lie in $[c,d]$ [ST, Section 3.1]. Set

$$
F_p=\{w_{j,i}:0\le j<4,\ i\in\{0,1\}\},\qquad
F_\beta=\{\beta\}\cup\alpha F_p,
$$

$$
H_p(r)=h(r)^4,\qquad H_\beta(r)=r h(r)^4.
$$

For $c\le r\le d$, every coordinate $P_{s,r}(\omega)$ with $\omega\in F_s$ is monotone. Indeed the p coordinates are $r^{j+1}(1-r)^j$ and $r^j(1-r)^{j+2}$; their derivative signs are respectively $(j+1)-(2j+1)r$ and $j-(2j+2)r$. The alpha-prefixed suspended signs are $(j+2)-(2j+2)r$ and $(j+1)-(2j+3)r$, and its standalone beta decreases. For $0\le j<4$, none changes sign in $[c,d]$. Also $H_s(r)\le H_s(d)$. Consequently complete-law TV satisfies

$$
\operatorname{TV}(M_s,P_{s,r})\le B_s:=
\frac12\sum_{\omega\in F_s}
 \max\{|M_s(\omega)-P_{s,c}(\omega)|,
       |M_s(\omega)-P_{s,d}(\omega)|\}
+\frac12\left(\frac{H_s(a)+H_s(b)}2+H_s(d)\right).
\tag{12.13}
$$

The last term bounds both whole tail masses, including the infinite outcome. Substitution of the native masses [ST, (2.2)–(2.3)] gives the exact bounds

$$
B_p=\frac{2068244698214078338643191}{70149855778976563200000000}<\frac3{100},
\qquad
B_\beta=\frac{3283743424817}{168920121093750}<\frac1{50}.
\tag{12.14}
$$

Each perturbed law is at TV distance $\varepsilon$ from its midpoint. Hence each nonendpoint loss is at most $B_s+\varepsilon$, strictly less than $\rho_p=1116529/22781250$ or $\rho_\beta=239/6750$ at its respective phase. This proves (12.12) simultaneously for arbitrary finite or countable installed support. For any original actual history, countable TV convexity applies to its same-depth posterior mixture, and the supplied full-record isometry $I_{C_0(h)}$ retains the complete target and these bounds. This marginal feasibility supplies no dynamics, source reset or borrowed trajectory.

The coordinates of (12.11) are (12.9), so $D_B=D_A=0$. But their immediate emissions give

$$
J_p=J_\beta=\frac1{900}-\varepsilon^2
                  =\frac{999991}{900000000}>0.
\tag{12.15}
$$

For any proposed shared flow, (12.7) would require $0\ge J_p+J_\beta$, a contradiction. Thus even the first necessary residual identity cannot be met. Equivalently, Theorem 12.2 would require native endpoint-atomic marginals different from (12.11). The four-moment identities have therefore separated an explicitly all-supported-risk-feasible pair, rather than supplied an unconsumed inequality.

Finally suppose one $Q_\pm$ were $\int P_{p,r}\,d\kappa(r)$ for a Borel probability measure on $[a,b]$. Its unchanged marker-0 coordinates at $j=1,\ldots,5$ imply

$$
\int r h(r)(h(r)-h(a))^2(h(r)-h(b))^2\,d\kappa(r)=0.
$$

The integral is a linear combination of those five unchanged moment coordinates, so equals its value for the fair endpoint mixture, namely zero. Its integrand is nonnegative. Since $r h(r)>0$ and $h$ is strictly increasing on $[a,b]$, $\kappa$ is supported on $\{a,b\}$. Its unchanged $j=1$ coordinate, together with normalization, forces fair endpoint weights, contradicting the perturbed alpha mass. For $W_\pm$, the unchanged alpha-prefixed marker-0 coordinates give the same argument with $r^2h(r)$ in place of $rh(r)$; the unchanged $j=1$ coordinate fixes fair weights, contradicting the perturbed standalone beta mass. Thus this incompatibility is not an instance of an assumed native-individual-law restriction. $\square$

## 追加锚（本行以下为增补区）

## 13. One-sided exact finite common-flow realization and attainment consumers

### 13.1 Domain and the exact preservation claim

**Standing assumptions 13.1.** Retain exactly the source and fixed installed finite or countable prior of Section 11.1, with positive masses at depths 1 and 2 and every supported nonendpoint target. Use the complete countable carriers, including noncompletion, the compact TV law spaces $\mathcal K_p,\mathcal K_\beta$, and the compatible-flow domain $\mathfrak C$ of Definition 11.2. Both residual equations condition on the entire input descriptor; both directional flows have the same unweighted phase marginals. Configuration loss is the integral of complete-law TV in (11.9). The original records, both seeds, paid histories, source-independent initialization, same-update generation, completion and matching Stop remain part of the task.

The finite-support hypotheses below concern a marginal of complete predicted laws. They are additional hypotheses on a branch of $\mathfrak C$, not restrictions on the original infimum. Neither the source parameter $n=4$ nor a bound on COMPLETE is this support size. No native-mixture, synchronized endpoint-chord, common geometric return rate, equal-flow, reversible, irreducible or zero-variation hypothesis is imposed.

**Theorem 13.2 (exact finite realization from one finite marginal).** Let $(\Gamma_B,\Gamma_A)\in\mathfrak C$ have

$$
\nu_p=\sum_{i=1}^N\pi_i\delta_{Q_i},\qquad
\pi_i>0,\qquad \sum_i\pi_i=1,
\tag{13.1}
$$

where the complete laws $Q_i$ are distinct. Let $f_1,\ldots,f_q$ be any specified finite list of bounded Borel real functions on $\mathcal K_\beta$, allowing $q=0$. Let $G\subset\mathcal K_\beta$ be any Borel set of full $\nu_\beta$ measure. There is a finite regular stationary table with p labels $1,\ldots,N$, p row exactly $\pi$, p own laws exactly $Q_i$, and suspended labels $1,\ldots,m$ satisfying

$$
1\le m\le N^2+2N+q-1.
\tag{13.2}
$$

Its suspended own laws $W_\ell$ belong to $G$, and its positive suspended row $\tau$ satisfies

$$
\pi B=\tau,\qquad \tau A=\pi,\qquad
\sum_{\ell=1}^m\tau_\ell f_t(W_\ell)
 =\int f_t(W)\,d\nu_\beta(W)\quad(1\le t\le q).
\tag{13.3}
$$

The table satisfies both full complete-law residual equations. It preserves the entire p marginal, hence the p configuration loss against every complete target. In particular, choosing $f_t(W)=\operatorname{TV}(W,T_t)$ preserves each specified suspended complete configuration loss exactly. Taking $G$ to be the full endpoint coordinate box preserves that box at every new suspended law whenever it held almost surely in the input.

There is a symmetric statement with $\nu_\beta=\sum_{i=1}^N\tau_i\delta_{W_i}$: keep that entire marginal and every suspended target loss, and replace the p marginal by at most $N^2+2N+q-1$ labels while preserving any $q$ specified bounded Borel p integrals and any full-measure Borel p constraint.

These are abstract finite stochastic rules with real entries. The new opposite-phase marginal and both joint flow measures can differ from the input. No preservation of the original three-stage return coupling is asserted.

**Proof, p-finite direction.** Disintegrate $\Gamma_A$ over its entire input $W$. Its other marginal is supported on the $Q_i$, so there are Borel functions $\theta_i:\mathcal K_\beta\to[0,1]$ such that, on a Borel full-measure set,

$$
\sum_{j=1}^N\theta_j(W)=1,\qquad
\mathcal R_A(W)=\sum_{j=1}^N\theta_j(W)Q_j,\qquad
\int\theta_j(W)\,d\nu_\beta(W)=\pi_j.
\tag{13.4}
$$

Indeed $\theta_j(W)$ is the conditional mass at $Q_j$; the marginal identity gives the last equality. Equation (11.8) gives the middle equality atomwise. The complete carrier is countable, so intersecting its atomwise full-measure sets gives one Borel set on which it holds as an equality of full normalized measures. Extend the $\theta_j$ off this set by any fixed probability row. On this set (11.4) gives

$$
W=(1-v(W))\delta_\beta
   +v(W)\alpha\sum_{j=1}^N\theta_j(W)Q_j.
\tag{13.5}
$$

Push $\Gamma_B$ to the measure $\xi$ on $\{1,\ldots,N\}\times\mathcal K_\beta$ by replacing $Q_i$ with its index $i$. Its marginals are $\pi,\nu_\beta$. Write $e_i(I,W)=\mathbf1_{\{I=i\}}$. Consider, on this one probability space, the following finite list of bounded Borel functions:

$$
\begin{array}{ll}
e_i & (1\le i\le N),\\
\theta_j(W) & (1\le j<N),\\
e_i v(W)\theta_j(W) & (1\le i,j\le N),\\
f_t(W) & (1\le t\le q).
\end{array}
\tag{13.6}
$$

There are $d=N+(N-1)+N^2+q$ coordinates. Apply [Bayer–Teichmann, Corollary 2](https://arxiv.org/html/math/0502473v2) to their joint map into $\mathbb R^d$ and to the $\xi$-full Borel set where (13.4)–(13.5) hold and $W\in G$. The measure is positive and finite; boundedness gives integrability of the Euclidean norm of this map. That corollary allows nodes in the specified full-measure set and gives $m\le d$ nodes $(i_\ell,W_\ell)$ with positive weights $t_\ell$, matching all the listed integrals. Since $\sum_i e_i=1$ everywhere, their matched integrals give $\sum_\ell t_\ell=1$ without an extra constant coordinate. For $N=1$ the second list is empty.

Set

$$
\tau_\ell=t_\ell,\qquad
B_{i\ell}=\frac{t_\ell}{\pi_i}\mathbf1_{\{i_\ell=i\}},
\qquad A_{\ell j}=\theta_j(W_\ell),\qquad
u_i=Q_i(\alpha),\quad v_\ell=v(W_\ell).
\tag{13.7}
$$

Matching the $e_i$ makes $B$ row-stochastic and gives $\pi B=\tau$. Each row of $A$ sums to one. Matching the unweighted $\theta_j$ gives $\tau A=\pi$ for $j<N$; normalization gives its last coordinate, including when $N=1$. Thus both actual-flow balances are exact, with no synthetic continuation weight.

It remains to prove that these finitely many matched quantities close the entire other residual, rather than a finite projection. Put

$$
M_{ij}=\int e_i v(W)\theta_j(W)\,d\xi(I,W).
$$

The first full residual equation and (13.5) imply, as complete measures on $\Omega_\beta$,

$$
\begin{aligned}
\pi_i\mathcal R_B(Q_i)
 &=\int e_iW\,d\xi\\
 &=\left(\pi_i-\sum_jM_{ij}\right)\delta_\beta
      +\alpha\sum_jM_{ij}Q_j.
\end{aligned}
\tag{13.8}
$$

The node rule matches $\pi_i$ and every $M_{ij}$. Expanding each selected $W_\ell$ by (13.5) therefore gives exactly

$$
\sum_\ell B_{i\ell}W_\ell=\mathcal R_B(Q_i),\qquad
\sum_j A_{\ell j}Q_j=\mathcal R_A(W_\ell).
\tag{13.9}
$$

All completed words and the infinite outcome are included in (13.8)–(13.9). Together with (11.4) these are the table's own same-update recursions

$$
Q_i=u_i\delta_\alpha+(1-u_i)\beta\sum_\ell B_{i\ell}W_\ell,
\qquad
W_\ell=(1-v_\ell)\delta_\beta+v_\ell\alpha\sum_jA_{\ell j}Q_j.
\tag{13.10}
$$

The emissions belong to $[1/3,2/5]$. Synthetic survival through $L$ complete returns is at most $(4/15)^L$ from p and $(2/5)(4/15)^L$ from suspension. The finite generator thus has normalized own complete laws, with noncompletion present at mass zero. Two normalized solutions of (13.10), with maximal phase TV distances $z_p,z_\beta$, obey

$$
z_p\le(2/3)z_\beta,\qquad z_\beta\le(2/5)z_p,
$$

so both distances vanish. Hence the selected descriptors are the actual generated complete laws, not fitted decoding laws. Repeated selected $W_\ell$ may be kept as distinct finite labels; pushing their flows to descriptors still satisfies (11.7). Matching $f_t$ proves (13.3). The unchanged p marginal proves its all-target loss assertion. This proves (13.2) and the p-finite direction.

**Proof, suspended-finite direction.** Now write the finite suspended marginal as $\sum_i\tau_i\delta_{W_i}$. Disintegrate $\Gamma_B$ over the whole $Q$, obtaining Borel $\theta_j(Q)$ with

$$
\sum_j\theta_j(Q)=1,\quad
\mathcal R_B(Q)=\sum_j\theta_j(Q)W_j,\quad
\int\theta_j(Q)\,d\nu_p(Q)=\tau_j.
$$

On one full-measure Borel set put $U(Q)=1-Q(\alpha)$; then

$$
Q=(1-U(Q))\delta_\alpha+U(Q)\beta\sum_j\theta_j(Q)W_j.
$$

Push $\Gamma_A$ to $\xi$ on $\{1,\ldots,N\}\times\mathcal K_p$, with marginals $\tau,\nu_p$. Match the $N$ indicators $e_i$, the $N-1$ functions $\theta_j(Q)$, the $N^2$ functions $e_iU(Q)\theta_j(Q)$, and the $q$ specified p functions. The same corollary supplies at most $d$ nodes $(i_\ell,Q_\ell)$ in the prescribed full-measure set with weights $t_\ell$. Define

$$
\pi_\ell=t_\ell,\qquad
A_{i\ell}=\frac{t_\ell}{\tau_i}\mathbf1_{\{i_\ell=i\}},
\qquad B_{\ell j}=\theta_j(Q_\ell).
\tag{13.11}
$$

The indicator and unweighted moments give $\tau A=\pi$, $\pi B=\tau$. For $M_{ij}=\int e_iU(Q)\theta_j(Q)\,d\xi$, the whole residual identity is

$$
\tau_i\mathcal R_A(W_i)
 =\left(\tau_i-\sum_jM_{ij}\right)\delta_\alpha
       +\beta\sum_jM_{ij}W_j.
\tag{13.12}
$$

Matching these moments gives $\sum_\ell A_{i\ell}Q_\ell=\mathcal R_A(W_i)$; the node identity gives $\sum_jB_{\ell j}W_j=\mathcal R_B(Q_\ell)$. With emissions $Q_\ell(\alpha),1-W_i(\beta)$, the same normalization and contraction proof establishes the two own-law recursions on the full carriers. This proves the symmetric statement. $\square$

The two types of moments in (13.6) have distinct roles: the unweighted $\theta_j$ preserve the actual return marginal, whereas $e_iv\theta_j$ close the synthetic complete-law residual. Equation (13.8) is a finite-dimensional closure of an infinite complete-law equality because the opposite residual is a mixture of the fixed finitely many $Q_j$. No tail truncation or replacement of the full law by its first moments occurs.

### 13.2 Original-observer adapter and its precise risk scope

**Proposition 13.3 (full original realization of the new table).** Each table of Theorem 13.2 has the original-domain product realization of Section 11.4 and [PAID, Lemma 2.1.1]. Its fourth-phase actual label rows at every positive original history are its unweighted stationary rows. Its full original phase configuration-risk suprema are

$$
R_{\mathrm{conf},p}
 =\sup_{k:\mu(k)>0}\sum_i\pi_i\operatorname{TV}(Q_i,P_{p,r_k}),
\qquad
R_{\mathrm{conf},\beta}
 =\sup_{k:\mu(k)>0}\sum_\ell\tau_\ell
       \operatorname{TV}(W_\ell,P_{\beta,r_k}),
\tag{13.13}
$$

with the evident exchanged notation for the symmetric construction.

**Proof.** Retain the entire original $C_0$. Use fair synthesis before the third latch, perform the original third record write and latch, and sample the new p row independently of the source in that same update. Use the table's $B$ after every actual or synthetic p-beta and its $A$ after every actual or synthetic suspended-alpha. Completing letters clear the label and enter the matching original pendingStop; its unique Stop and delivery retain their original transitions. Projection to $C_0$ is its original update at every operation. Thus induction preserves all paid rejections, both seeds, marker words and partial parses, records, fields, permissions and event blocks, without resampling the once-drawn $K$.

At the latch the row is $\pi$; (13.3) or (13.11) gives $\tau$ after a p-beta and $\pi$ after a suspended-alpha. The private sampler and updates are independent of the actual source. Conditioning on an acquired word consequently does not reweight configurations by synthetic emission probabilities. These are the rows at every positive finite fourth-phase history on every record fibre.

The generated raw laws are exactly those proved in (13.10) and its symmetric version. The renderer $I_{C_0(h)}$ adds all original future records, operation blocks, completion and Stop, preserving complete TV and residual operation deletion. Noncompletion is retained; its zero mass follows from the full generation proof, without conditioning on completion. The pre-latch and terminal laws are those of this same product generator.

At any fourth-phase history the actual target remains the countable posterior mixture $T_{s,h}=\sum_k\nu_h(k)P_{s,r_k}$ under the same installed prior. Configurationwise TV convexity gives the upper direction of (13.13). The lower direction is [CLIP, Proposition 2.3], using positive finite paid rejection histories concentrating at each supported depth with a fixed legal seed/marker suffix; [PAID, Lemma 14.1] supplies the countable-prior likelihood domination. Their hypotheses are exactly the source, stationary rows and complete same-update laws just established. Thus all original supported targets and all positive histories are retained.

For a p-finite construction the unchanged p marginal also preserves the loss against every posterior target on its raw record fibre. The specified suspended pure-target losses are preserved, but a suspended loss against a posterior mixture need not equal its old value. Equation (13.13), rather than such a per-history equality, is the consumer below. $\square$

Only the finite table and its active label are installed with $C_0$; the descriptors, measures, disintegrations and moment integrals are proof data. Turning this abstract table into an effective exact observer additionally requires permitted finitely represented exact samplers for its latch row, both acquired kernels and emissions. All representation, sampler states, persistent randomness, program, indices and workspace belong to COMPLETE, and all acquired Reads, fresh bits, internal work, synthesis and output remain charged. The support bounds are label bounds, not fixed COMPLETE, hard-defect or worst-case work bounds.

### 13.3 Finite installed support: exact attainment and one-sided shape cutoff

**Corollary 13.4 (one finite marginal suffices for abstract attainment).** Suppose the original installed support $S=\{k:\mu(k)>0\}$ is finite, of size $s\ge3$. The following are equivalent:

1. A finite abstract original common conf/conf attainer exists.
2. Some zero-level compatible pair has finitely supported p marginal.
3. Some zero-level compatible pair has finitely supported suspended marginal.

If a zero-level pair has $N$ p-law atoms, an abstract attainer can have

$$
|X|=N,\qquad |Y|\le N^2+2N+s-2.
\tag{13.14}
$$

If it has $N$ suspended-law atoms, the exchanged bound holds.

**Proof.** At zero level, (11.29) holds almost surely at both phases and (11.30) gives their endpoint-event midpoint means. On the full endpoint coordinate box, with $E_s=\{\omega:P_{s,a}(\omega)>P_{s,b}(\omega)\}$, normalization gives

$$
\operatorname{TV}(D,P_{s,a})=P_{s,a}(E_s)-D(E_s),\qquad
\operatorname{TV}(D,P_{s,b})=D(E_s)-P_{s,b}(E_s).
\tag{13.15}
$$

Thus both endpoint configuration losses can be preserved by one event-mean integral, rather than two loss integrals. In the p-finite direction apply Theorem 13.2 with $G$ the suspended full endpoint box, the function $W(E_\beta)$, and the $s-2$ functions $\operatorname{TV}(W,P_{\beta,r_k})$ for all supported nonendpoints. There are $q=s-1$ functions, giving (13.14). The event mean remains $H$ and both endpoint losses remain $\rho_\beta$ by (13.15); every nonendpoint suspended loss remains its old value. The entire p marginal, its full box, mean $C$ and all its supported losses are unchanged. The new compatible pair is therefore zero-level. Proposition 13.3 makes it an original abstract attainer with both risks equal to their separate minima.

The symmetric proof uses the p endpoint box, $Q(E_p)$ and every supported nonendpoint p loss, while retaining the entire suspended marginal. Conversely, Theorem 11.8, using the supplied original-to-regular endpoint extraction, embeds any finite abstract original attainer as a compatible zero-level pair with both marginals finite. This proves all three implications. $\square$

For example, a zero-level pair with at most two p-law atoms under a fixed three-depth prior has an abstract realization with at most two p labels and nine suspended labels. This is a conditional branch bound, not a two-law restriction on the original domain or a zero-level witness.

**Theorem 13.5 (exact one-sided shape cutoff for a finite prior).** Under the finite-support hypothesis of Corollary 13.4, for each integer $N\ge1$ let

$$
\mathfrak C_N^p=\{(\Gamma_B,\Gamma_A)\in\mathfrak C:
                         |\operatorname{supp}\nu_p|\le N\},\qquad
D_{N,s}=N^2+2N+s-1.
$$

Then the following are attained minima, with $e(M)$ as in Theorem 11.5:

$$
\min_{\mathfrak C_N^p}\mathcal J
 =\min_{\substack{M\in\mathfrak S_\mu\\
                   |X|\le N,\ |Y|\le D_{N,s}}}e(M).
\tag{13.16}
$$

The symmetric equality bounds $|Y|\le N$ and $|X|\le D_{N,s}$.

If $j_c=0$ but there is no finite abstract original attainer, every zero-level compatible pair has infinite support at both marginals. In any regular stationary sequence with $e(M_n)\to0$, both numbers of distinct phase complete laws tend to infinity.

**Proof.** The set of probability measures on $\mathcal K_p$ with at most $N$ atoms is the continuous image of the compact set $\Delta_N\times\mathcal K_p^N$ under $(t,Q)\mapsto\sum_i t_i\delta_{Q_i}$. Zero weights and repeated atoms are allowed in this parametrization. It is therefore weakly compact and closed. Marginal projection is continuous, so $\mathfrak C_N^p$ is a closed compact subdomain of $\mathfrak C$. It is nonempty by the singleton construction in Lemma 11.3. For finite $S$, $\mathcal J$ is the maximum of finitely many continuous loss integrals, so it has a minimum on this subdomain.

Apply Theorem 13.2 to a minimizer with its actual number $n\le N$ of positive distinct p atoms, listing all $s$ suspended target losses. It preserves the whole objective and produces at most $n^2+2n+s-1\le D_{N,s}$ suspended labels and $n$ p labels. Proposition 13.3 identifies its original excess with this objective. Conversely (11.24) maps each table on the right to a pair in $\mathfrak C_N^p$ with identical excess. This proves (13.16) and realizes its right minimum.

Equivalently, the finite table domain on the right admits a compact padded representation with $N,D_{N,s}$ labels, nonnegative rows, stochastic kernels, emissions in $[a,b]$ and closed balances. Complete laws and losses vary continuously there: every finite completed-word coordinate is polynomial in the parameters, and the common geometric survival bound controls the whole TV tail uniformly. Removing zero-weight labels changes no positive-label generated law or loss; nonnegative balances preclude transitions from a positive label into a zero-weight label. This recovers the stipulated positive-row tables and explains attainment without assuming that the positive-row parameter domain itself is closed.

The first nonattainment assertion follows from Corollary 13.4 in either direction. For the sequence assertion, if one phase's distinct-law count did not tend to infinity, a subsequence would have that count bounded by some $N$. Embed its tables in $\mathfrak C$ by (11.24), take a compact subsequence, and use the closed at-most-$N$ marginal condition. Lower semicontinuity and nonnegativity of $\mathcal J$ make the limiting pair zero-level. Corollary 13.4 would give a finite abstract attainer, a contradiction. The proof works for either phase. These conclusions use absence of an abstract attainer; absence only of an effective attainer is insufficient. $\square$

### 13.4 Countably infinite installed support: strict limit slack

**Theorem 13.6 (all-supported finite realization with strict accumulation slack).** Suppose the original installed support is countably infinite. Let a zero-level compatible pair have $N$ p-law atoms and put

$$
r_*=(3-\sqrt5)/2,\qquad c_*=25/64,\qquad
\delta_\beta=\rho_\beta-\mathcal L_\beta(P_{\beta,r_*}).
$$

If $\delta_\beta>0$, there is a finite abstract original common conf/conf attainer preserving the entire p marginal. For any integer $M\ge2$ such that

$$
\zeta_{\beta,M}:=\frac{107}{855}c_*^M<\delta_\beta/2,
\qquad s_M=|\{k\le M:\mu(k)>0\}|,
\tag{13.17}
$$

it can have

$$
|X|=N,\qquad |Y|\le N^2+2N+s_M-1.
\tag{13.18}
$$

Symmetrically, a zero-level pair with $N$ suspended-law atoms and $\delta_p=\rho_p-\mathcal L_p(P_{p,r_*})>0$ has a finite abstract attainer preserving that marginal, using $\zeta_{p,M}=(25/171)c_*^M<\delta_p/2$ and the exchanged bound (13.18).

Consequently, if no finite abstract original attainer exists, every zero-level pair with finite p marginal must satisfy $\mathcal L_\beta(P_{\beta,r_*})=\rho_\beta$, and every such pair with finite suspended marginal must satisfy $\mathcal L_p(P_{p,r_*})=\rho_p$.

**Proof.** Infinite installed support is unbounded in depth, and $r_k\to r_*$. By [CLIP, Proposition 5.3], on the full complete carriers,

$$
\operatorname{TV}(P_{\beta,r_k},P_{\beta,r_*})\le\zeta_{\beta,M},
\qquad
\operatorname{TV}(P_{p,r_k},P_{p,r_*})\le\zeta_{p,M}
\quad(k>M).
\tag{13.19}
$$

Their hypotheses are the original Fibonacci parameters in $[1/3,2/5]$ and the normalized stopped laws, including all future records through their TV-preserving renderer. They do not truncate the future or require a positive floor on countably many prior masses. Configuration loss is 1-Lipschitz in its complete target, by the reverse triangle inequality before configuration integration. Thus each zero-level pair has $\mathcal L_s(P_{s,r_*})\le\rho_s$ by taking supported depths tending to infinity. The accumulation target is a continuity consequence, not a new installed depth or query.

Choose $M$ as in (13.17). In Theorem 13.2 retain the full suspended endpoint box and list $W(E_\beta)$, the $s_M-2$ full losses at actual supported depths $3\le k\le M$, and the loss at $P_{\beta,r_*}$. These are $q=s_M$ functions. The full endpoint boxes and midpoint mean, all listed supported losses, and the limit loss are exact in the new table, giving (13.18). For every omitted but still installed depth $k>M$, configurationwise triangle inequality and (13.19) give

$$
\begin{aligned}
\mathcal L'_\beta(P_{\beta,r_k})
 &\le\mathcal L'_\beta(P_{\beta,r_*})
          +\operatorname{TV}(P_{\beta,r_k},P_{\beta,r_*})\\
 &\le\rho_\beta-\delta_\beta+\zeta_{\beta,M}
   <\rho_\beta-\delta_\beta/2<\rho_\beta .
\end{aligned}
\tag{13.20}
$$

The entire p marginal remains unchanged, including all its installed target losses. Therefore the new pair is zero-level for the original countably infinite support, and Proposition 13.3 gives the full original attainer. No posterior, prior-support oracle or limit depth is installed in that observer.

In the symmetric case retain $Q(E_p)$, the supported p losses up to $M$ and the p limit loss. The symmetric part of Theorem 13.2 and $\zeta_{p,M}$ give the same proof. In either direction the relevant limit slack is nonnegative by continuity. The contrapositive of the proved strict-slack implication therefore makes it exactly zero in the stated nonattainment case. $\square$

If the limit loss is saturated, $\delta_s=0$, the error term in (13.20) supplies no bound at $\rho_s$. Matching finitely many loss functions then does not establish every installed loss inequality. The saturated case is left unresolved. The integer $M$, support menu and exact moment weights above are mathematical existence data; the argument gives no algorithm extracting them from an opaque installed prior.

### 13.5 Attribution, return-coupling boundary and the remaining criterion

**Mathematical citation 13.7 (primary hypotheses and source-relative delta).** [Christian Bayer and Josef Teichmann, *The proof of Tchakaloff's Theorem*, arXiv:math/0502473v2, Corollary 2](https://arxiv.org/html/math/0502473v2), requires a positive measure on a measurable space, concentration on a specified measurable set, a measurable finite-dimensional map and integrability of its norm. In (13.6) these are respectively $\xi$, the intersection of the descriptor-residual full set with $G$, the listed bounded Borel functions and their automatic integrability. The corollary gives at most the map dimension in positive-weight nodes in that set. Preservation of total mass here follows from $\sum e_i=1$. Polynomial test functions, compact support in Euclidean space and a separately added constant are not needed. The same hypotheses hold for the symmetric list preceding (13.11). Finite quadrature and its node-count theorem are entirely attributed to this primary result.

[Aurelien Alfonsi, Rafael Coyaud, Virginie Ehrlacher and Damiano Lombardi, *Approximation of Optimal Transport problems with marginal moments constraints*, arXiv:1905.05663v1, Proposition 2.1 and Section 3.3.2](https://arxiv.org/html/1905.05663v1), places this finite-moment tool in moment-constrained transport and martingale transport. Proposition 2.1 states the measurable-map finite representation for a measure on $\mathbb R^d$, a Borel full set and integrable feature norm; its normalization caveat requires preserving a constant or its linear equivalent. Applying it to a feature pushforward with the identity map preserves finitely many feature means, but alone does not lift its nodes to full descriptors satisfying both residual equations. Corollary 2 above applies directly to the original measurable descriptor space and its full set, so no such lifting premise is inferred. No transport-cost existence or convergence theorem from that paper is used as a full-law compatibility theorem.

Theorem 11.4 supplies target-uniform approximate common regeneration; Theorem 11.8 supplies exact regeneration when both marginals are already finite; Sections 11.4–11.5, [PAID, Lemma 2.1.1 and Corollary 2.3], and [CLIP, Proposition 2.3] supply the original-history adapter and abstract endpoint-attainment correspondence. [CLIP, Proposition 5.3] supplies precisely the complete-target convergence bounds in (13.19). Those are reused statements. The source-relative unsupplied inference is the exact full-measure closure (13.8) and (13.12) from just one finite marginal, while a separate unweighted moment list preserves actual circulation. It is consumed by the one-sided attainment criterion (13.14), exact opposite-shape cutoff (13.16), semantic-support divergence consequence and all-installed strict-slack bridge (13.20). It neither evaluates the compact zero face nor asserts global priority for finite-moment representation.

The latest supplied [RETURN, Proposition 11.9](https://github.com/the-omega-institute/trureturing/blob/165d338a70c0c4ebfff419f14382d43c42453fa6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md) exhibits two finite observers with equal full directional joint law flows but different three-stage acquired return law measures and different return motion. Theorem 13.2 makes the weaker preservation claim of retaining one marginal, finitely many opposite loss integrals and exact compatibility in newly chosen flows. Its moment matrix uses a residual disintegration of $\Gamma_A$, not the input observer's hidden suspended label. It therefore supplies no preservation or identification of that hidden return coupling, of $V_\pi$, or of complete-law motion. In particular [RETURN, Theorem 10.2]'s free $V_\pi$ remains free and gives no risk-only gap here.

The supplied [BLIND, Conventions 1.1–1.2 and Theorems 5.1, 6.3](https://github.com/the-omega-institute/trureturing/blob/165d338a70c0c4ebfff419f14382d43c42453fa6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_KERNEL_BLIND_DIRECTIONS_AFTER_PAIRED_CALIBRATION.md) uses a coarse observation contract omitting the acquired p-beta kernel, with interior emissions and finite-horizon transcript aliases. It establishes an identification failure of complete laws and a risk coordinate for that interface. Here the input is an entire compatible pair of full-law flows; the task is existence of a possibly different finite table. No unknown kernel is identified from those aliases, and no BLIND table is asserted to lie on the common zero face.

**Audit criterion 13.8.** The finite bridge is falsified by positive nodes matching (13.6) on its stated full set for which either unweighted balance in (13.3), either complete-measure equality in (13.9), or a listed loss integral fails. The symmetric criterion is (13.11)–(13.12). The all-supported countable consumer is falsified by an input satisfying its zero-level, one-sided finite-support and strictly positive opposite limit-slack hypotheses for which the constructed finite table violates any actual supported loss bound; (13.19)–(13.20) provide the uniform full-law check. A saturated limit, an unavailable effective sampler or failure to preserve the old joint flows is outside these affirmative claims.

**Remaining original criterion.** On the unrestricted $\mathfrak C$, the endpoint coordinate boxes (11.29), endpoint-event midpoint means (11.30), both full-descriptor residual equations with shared unweighted marginals and every original supported configuration-loss bound must still be imposed jointly. Existence of a zero-level pair, a vanishing family or an evaluated strict separation is not established in this chapter. For a finite prior, one-sided finite support now suffices for abstract finite attainment if such a zero-level pair exists; it is not proved for any unknown optimizer. For a countably infinite prior, Theorem 13.6 covers strict opposite limit slack, leaving saturated accumulation loss unresolved. Permitted finitely represented exact sampling remains an additional effective-attainment requirement. Theorem 11.5's unrestricted zero-versus-positive alternative, general finite effective attainment and fixed-resource questions retain their original completion criteria.

## 追加锚（本行以下为增补区）

## 14. Quantitative endpoint-chord stability for complete configuration losses

**Standing assumptions 14.1 (the same full-law pair and its four-moment defect).** Let $(\Gamma_B,\Gamma_A)$ be any compatible Borel pair of Definition 11.2, with its original common unweighted marginals $\nu_p,\nu_\beta$ and both full-descriptor conditional residual equations (11.8). Use exactly the source, installed finite or countable prior, complete countable carriers and original history domain of Standing assumptions 12.1. In particular, the actual depth $K$ is sampled once, initialization is source-independent, and both seeds, every paid rejection and partial parse, all records, permissions, third-write-before-latch, fourth completion, its matching Stop and all tails including infinite noncompletion remain in the domain. Configuration losses retain TV inside the descriptor integral, as in (11.9).

Retain $m_p,m_\beta,t,q,z,J_p,J_\beta,M_B,M_A,D_B,D_A$ from (12.1), (12.2) and (12.7), and put

$$
S=D_B+D_A=2J_p+2J_\beta+M_B+M_A\ge0.
\tag{14.1}
$$

For $s\in\{p,\beta\}$, a normalized complete probability target $T\in\mathcal P(\Omega_s)$ and $0\le\theta\le1$, define

$$
H_{s,\theta}(T)=(1-\theta)\operatorname{TV}(P_{s,a},T)
                  +\theta\operatorname{TV}(P_{s,b},T).
\tag{14.2}
$$

These reference laws are mathematical comparisons on the original complete carriers. They are not installed runtime states or assertions of samplers preserving COMPLETE, description size, work, random-bit use, paid Reads or any other separately charged resource. When a pair comes from a stationary original product, its acquired and synthetic kernels and actual initialization remain exactly those of Sections 2 and 11.4.

**Theorem 14.2 (one endpoint weight for all complete configuration losses).** Every pair in Standing assumptions 14.1 has one common $\theta\in[0,1]$, independent of the target and of the phase, such that, for every normalized complete target at the respective phase,

$$
\left|\mathcal L_p(T)-H_{p,\theta}(T)\right|\le C_p S,
\qquad C_p=\frac{540}{11},
$$

$$
\left|\mathcal L_\beta(T)-H_{\beta,\theta}(T)\right|\le C_\beta S,
\qquad C_\beta=\frac{1395}{22}.
\tag{14.3}
$$

The targets may assign positive mass to infinite noncompletion. One admissible common weight is

$$
\theta=\nu_p\left\{Q:u(Q)>\frac{a+b}{2}\right\}.
\tag{14.4}
$$

At $S=0$ this comparison is precisely the compatible endpoint pair (12.4)–(12.5), including the endpoint weights $0$ and $1$.

**Proof.** Set $\delta=b-a=1/15$, $m=(a+b)/2$, $j(x)=(x-a)(b-x)$, and let $r(x)$ be the nearest endpoint, with a tie rounded to $a$. For $a\le x\le b$, the distance $d(x)=|x-r(x)|$ is at most $\delta/2$, so $j(x)=d(x)(\delta-d(x))\ge\delta d(x)/2$. Consequently

$$
e_p:=\int|u-r(u)|\,d\nu_p\le30J_p,
\qquad
e_\beta:=\int|v-r(v)|\,d\nu_\beta\le30J_\beta.
\tag{14.5}
$$

If $r(x)\ne r(y)$, then $(x-m)(y-m)\le0$ and

$$
j(x)+j(y)+(x-y)^2
 =\frac{\delta^2}{2}-2(x-m)(y-m)\ge\frac{\delta^2}{2}.
$$

For equal rounded endpoints the following inequality is automatic. Thus, pointwise on the whole square $[a,b]^2$,

$$
\mathbf1_{\{r(x)\ne r(y)\}}
 \le450\bigl(j(x)+j(y)+(x-y)^2\bigr).
$$

Let $\kappa_B$ and $\kappa_A$ be the probabilities of unequal rounded endpoints under the original $\Gamma_B$ and $\Gamma_A$, respectively. Their common unweighted marginals and the residual identities (12.7) give

$$
\kappa_B\le450(J_p+J_\beta+M_B)=450D_B,
\qquad
\kappa_A\le450(J_p+J_\beta+M_A)=450D_A.
\tag{14.6}
$$

These are estimates on the two given flows separately; neither flow has been replaced or weighted by a synthetic continuation probability.

Write

$$
d_p=\int\operatorname{TV}(Q,P_{p,r(u(Q))})\,d\nu_p(Q),\qquad
d_\beta=\int\operatorname{TV}(W,P_{\beta,r(v(W))})\,d\nu_\beta(W).
$$

The supplied endpoint distances are

$$
\Delta_p=\operatorname{TV}(P_{p,a},P_{p,b})=2\rho_p<\frac1{10},\qquad
\Delta_\beta=\operatorname{TV}(P_{\beta,a},P_{\beta,b})=2\rho_\beta<\frac1{10}.
$$

Apply the normalized whole-law comparison of (11.19)–(11.20) using the native endpoint recursions in the proof of Theorem 12.2. More explicitly, (11.4), the first full-descriptor conditional identity (11.8) and TV convexity give, for $\nu_p$-almost every $Q$,

$$
\begin{aligned}
\operatorname{TV}(Q,P_{p,r(u)})
&\le |u-r(u)|+(1-u)\int
       \operatorname{TV}(W,P_{\beta,r(u)})\,\Gamma_B(dW\mid Q)\\
&\le |u-r(u)|+(1-u)\int
 \left[\operatorname{TV}(W,P_{\beta,r(v)})
       +\Delta_\beta\mathbf1_{\{r(u)\ne r(v)\}}\right]
 \,\Gamma_B(dW\mid Q).
\end{aligned}
$$

The corresponding suspended inequality conditions on the entire $W$ in the second identity (11.8), uses $v$ as its continuation coefficient, and has $\Delta_p$ in its mismatch term. Integrate these inequalities against the respective input marginals. Using $1-u\le2/3$, $v\le2/5$, (14.5) and (14.6), with the original unweighted output marginals, yields

$$
\begin{aligned}
d_p&\le30J_p+\frac23d_\beta+30D_B,\\
d_\beta&\le30J_\beta+\frac25d_p+18D_A.
\end{aligned}
\tag{14.7}
$$

The same two-phase stopping contraction as in (11.20) has denominator $1-(2/3)(2/5)=11/15$. Solving (14.7) and substituting (12.7) gives

$$
\begin{aligned}
d_p
&\le\frac{450J_p+300J_\beta+450D_B+180D_A}{11}\\
&=\frac{1080J_p+930J_\beta+450M_B+180M_A}{11}
 \le\frac{540}{11}S,\\
d_\beta
&\le\frac{180J_p+450J_\beta+180D_B+270D_A}{11}\\
&=\frac{630J_p+900J_\beta+180M_B+270M_A}{11}
 \le\frac{450}{11}S.
\end{aligned}
\tag{14.8}
$$

Let $\theta_p=\nu_p\{r(u)=b\}$ and $\theta_\beta=\nu_\beta\{r(v)=b\}$. On either given flow, the difference between these two event probabilities is bounded by the probability of their indicators differing. Therefore

$$
|\theta_p-\theta_\beta|
 \le\min(\kappa_B,\kappa_A)
 \le450\min(D_B,D_A)\le225S.
\tag{14.9}
$$

For every complete target, the reverse triangle inequality applied to each descriptor before integration gives

$$
|\mathcal L_s(T)-H_{s,\theta_s}(T)|\le d_s.
$$

Also $|\operatorname{TV}(P_{s,a},T)-\operatorname{TV}(P_{s,b},T)|\le\Delta_s$. Choose $\theta=\theta_p$. Equations (14.8)–(14.9) prove the p estimate and bound the suspended error by

$$
d_\beta+\Delta_\beta|\theta_p-\theta_\beta|
 \le\left(\frac{450}{11}+\frac{225}{10}\right)S
 =\frac{1395}{22}S.
$$

All conditional equalities and comparisons here concern full normalized measures on the countable carriers. Boundedness and countable TV summation justify their integrals. The infinite outcomes remain atoms throughout; their zero descriptor masses follow from Lemma 11.1, whereas the target's infinite mass is unrestricted. No completion conditioning is used. TV has remained inside every configuration average.

If $S=0$, (14.5), (14.6) and (14.8) force endpoint emissions, zero mismatch on both flows and zero distance to the corresponding native complete laws. Equation (14.9) makes their endpoint weights common. Hence both marginals and flows are exactly (12.4)–(12.5), agreeing with Theorem 12.2. $\square$

**Corollary 14.3 (the same-history full-record targets and the return boundary).** Fix any positive active fourth-segment actual history $h$, at phase $s$, in the original source domain. Let $I_h=I_{C_0(h)}$ be its existing full-record renderer and

$$
T_{s,h}=\sum_{k:\mu(k)>0}\nu_h(k)P_{s,r_k},\qquad
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
 {\sum_i\mu(i)r_i^{A(h)}(1-r_i)^{B(h)}}.
$$

With the same $\theta$ of Theorem 14.2 for every such history and both phases,

$$
\begin{aligned}
\Bigg|\int\operatorname{TV}\bigl((I_h)_*D,(I_h)_*T_{s,h}\bigr)\,d\nu_s(D)
&-(1-\theta)\operatorname{TV}\bigl((I_h)_*P_{s,a},(I_h)_*T_{s,h}\bigr)\\
&-\theta\operatorname{TV}\bigl((I_h)_*P_{s,b},(I_h)_*T_{s,h}\bigr)\Bigg|
\le C_sS.
\end{aligned}
\tag{14.10}
$$

For the own-law pair (11.24) of an original stationary product, the integral is its original configuration loss at $h$. For a general Borel pair it is a mathematical comparison loss, with no runtime realization assertion. The two flows and these comparisons do not determine the actual three-stage return measure $\Xi$ or its actual return-variation functional $V$.

**Proof.** The posterior is normalized for finite or countable support and includes all paid rejections and partial parses under the same once-sampled $K$, by (2.2). Apply (14.3) to this complete target itself. The full-record isometry of Section 2, supplied by [ST, Section 2.1], transports every law in that inequality through the same $I_h$, giving (14.10). It retains future Read blocks, all held records, permissions, completion and the matching Stop, as well as infinite noncompletion. For an original stationary product the source-independent initialization and same acquired and synthetic updates in Section 11.4 give the phase row $\nu_s$ after every such history; no synthetic-probability reweighting of the actual row occurs.

For the final assertion, the two original tables in [Acquired-return variation, Proposition 11.9](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md) have equal full-law flows and hence equal $S$, marginal configuration losses and the weight (14.4), while their actual $\Xi$ and $V$ differ. Their original initialization and record-preserving renderers are supplied there by Proposition 11.10. Thus all the present comparisons agree on that pair without identifying its actual return motion. No triple join has been used in deriving (14.10). $\square$

**Corollary 14.4 (evaluated exclusion near the four-moment endpoint chord).** Suppose $\mu(1),\mu(2)>0$ and the original installed prior supports at least one $k\ge3$. Every compatible pair satisfies

$$
\mathcal J+\frac{540}{11}S\ge\frac\eta4
 =\frac{3554869594}{318644812890625},\qquad
\eta=\frac{14219478376}{318644812890625}.
\tag{14.11}
$$

In particular there is no compatible pair with both

$$
\mathcal J<\frac{1777434797}{318644812890625},\qquad
S<\frac{19551782767}{172068198960937500}.
\tag{14.12}
$$

Write its four coordinates as $\mathbf c=(m_p,m_\beta,q,z)$ and let

$$
\mathbf c(\theta_0)=\left(
 a+(b-a)\theta_0,\ a+(b-a)\theta_0,
 (1-\theta_0)(1-a)^2+\theta_0(1-b)^2,
 (1-\theta_0)a^2+\theta_0b^2\right).
$$

The explicitly evaluated simultaneous neighborhood

$$
\mathcal J<\frac{1777434797}{318644812890625},\qquad
\|\mathbf c-\mathbf c(\theta_0)\|_\infty
 <\frac{19551782767}{871812208068750000}
 \quad\text{for some }\theta_0\in[0,1]
\tag{14.13}
$$

contains no compatible pair's excess and coordinates. It is a nonempty neighborhood in the ambient nonnegative-excess and moment space, containing $(0,\mathbf c(\theta_0))$ for every $\theta_0$. The supported-nonendpoint hypothesis is necessary: for a prior supported only on depths $1,2$, the fair endpoint-tag pair has $\mathcal J=S=0$.

**Proof.** Put $E=\mathcal J+C_pS$ and use the common $\theta$ of Theorem 14.2. The original two endpoint risk bounds in (11.9) and (14.3) imply

$$
\theta\Delta_p=H_{p,\theta}(P_{p,a})\le\rho_p+E,
\qquad
(1-\theta)\Delta_p=H_{p,\theta}(P_{p,b})\le\rho_p+E.
$$

Since $\Delta_p=2\rho_p$, these inequalities give $|\theta-1/2|\Delta_p\le E$. For a supported $k\ge3$, put $r=r_k$. The complete-word gap (12.10) and its coordinate-triangle consequence in Corollary 12.3 give

$$
H_{p,1/2}(P_{p,r})\ge\rho_p+\frac\eta2.
$$

The reverse triangle inequality for the two endpoint distances gives

$$
\left|H_{p,\theta}(P_{p,r})-H_{p,1/2}(P_{p,r})\right|
 \le|\theta-1/2|\Delta_p\le E.
$$

On the other hand, the supported target's own bound in (11.9) and (14.3) give $H_{p,\theta}(P_{p,r})\le\rho_p+E$. Combining these three inequalities yields $\eta/2-E\le E$, which is (14.11). The same-history interpretation of supported pure targets retains precisely the paid-history and countable-prior hypotheses recorded in Section 11.4; it does not create a pure-source runtime query.

The two thresholds in (14.12) are exactly $\eta/8$ and $\eta/(8C_p)=11\eta/4320$, so their simultaneous strict inequalities would contradict (14.11). To obtain (14.13), sum the exact identities (12.7):

$$
S=\frac{22}{15}-\frac8{15}(m_p+m_\beta)-2q-2z.
$$

This affine expression vanishes at every $\mathbf c(\theta_0)$. Hence if $\|\mathbf c-\mathbf c(\theta_0)\|_\infty<\varepsilon$, its nonnegative value satisfies

$$
0\le S<\left(\frac{16}{15}+2+2\right)\varepsilon
       =\frac{76}{15}\varepsilon.
$$

The coordinate threshold in (14.13) is exactly $11\eta/21888$; multiplying it by $76/15$ gives $11\eta/4320$, the excluded $S$ threshold. All displayed thresholds are strictly positive, proving the asserted ambient nonemptiness and exclusion. For endpoint-only support, the fair pair (12.5) has endpoint losses $\rho_s$, endpoint emissions and no mismatch, so $\mathcal J=S=0$, as in Corollary 12.3.

This argument consumes the complete-loss comparison in the joint feasibility problem of Section 11.8 and quantitatively extends Corollary 12.3's exact-fibre exclusion. Its input tools are the previously supplied residual identities, normalized whole-law stopping contraction, endpoint distances and complete-word gap; it asserts no new general TV or coupling theorem and no literature priority. The necessary relation leaves $S$ free away from the excluded neighborhood and supplies no unrestricted positive risk-only gap, evaluated optimizer, finite attainment, resource optimum or physical-space dimension. $\square$

## 追加锚（本行以下为增补区）
