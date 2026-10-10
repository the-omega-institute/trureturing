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

## 15. An exact failed bridge for the selected event class

### 15.1 Standing data and the selected certificate class

Fix the source and its finite or countable installed prior, with positive endpoint masses and every supported nonendpoint retained, together with the once-sampled positive integer $K$, the original $m=2,d=1,\ell=2,n=4$ stopped renderer, both seeds, all marker triples and held registers, every paid rejection and finite return, the third write before the latch, fourth completion, and the matching Stop. Let all complete records, including the infinite noncompletion outcome, remain in the carriers of Chapter 11. The same source-independent acquired-letter kernels are required for actual and synthetic updates. These are the standing hypotheses of Definition 11.2; no posterior, clock, reset, or completion-conditioned law is added.

Only the complete-law definitions, endpoint geometry, configuration-before-TV losses, and the realization hypotheses already stated in those owners are used here. The appended result concerns a specified event-output subfamily; it does not enlarge the vector residual class in (11.7).

Put

$$
a=\frac13,\qquad b=\frac25,\qquad z_r=r(1-r),\qquad \lambda=\frac4{15},
$$

$$
\rho_p=\frac{1116529}{22781250},\qquad
\rho_\beta=\frac{239}{6750},\qquad
C=\frac{11758471}{22781250},\qquad
H=\frac{5261}{6750}.
$$

Write $w_{n,0}=(\beta\alpha)^n\alpha$ and $w_{n,1}=(\beta\alpha)^n\beta\beta$. The native complete laws are

$$
P_{p,r}(w_{n,0})=r z_r^n,\qquad
P_{p,r}(w_{n,1})=(1-r)^2z_r^n,
$$

$$
P_{\beta,r}(\beta)=1-r,\qquad
P_{\beta,r}(\alpha w_{n,i})=rP_{p,r}(w_{n,i}),
$$

with the infinite outcome having the mass prescribed by the complete stopped renderer (zero for these native laws). Let $T_p(j)$ and $T_\beta(j)$ contain every word with return index at least $j$ together with the infinite outcome. For a complete law $Q$ at phase $p$ and $W$ at phase $\beta$, put

$$
U(Q)=1-Q(w_{0,0}),\qquad v(W)=1-W(\beta),
$$

$$
\mathcal R_B(Q)(E)=\frac{Q(\beta E)}{U(Q)},\qquad
\mathcal R_A(W)(E)=\frac{W(\alpha E)}{v(W)}.
$$

The denominators are positive on the displayed law spaces: $U(Q)\ge 3/5$ and $v(W)\ge1/3$. In particular,

$$
\mathcal R_B(Q)(\beta)=\frac{Q(w_{0,1})}{U(Q)},\qquad
\mathcal R_B(Q)(\alpha w_{n,i})=\frac{Q(w_{n+1,i})}{U(Q)},
$$

$$
\mathcal R_A(W)(w_{n,i})=\frac{W(\alpha w_{n,i})}{v(W)}.
$$

Use the events

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\},
$$

and the actual event and residual-event coordinates

$$
f(Q)=Q(E_p),\qquad h(W)=W(E_\beta),
$$

$$
b_0(Q)=\frac{Q(w_{0,1})+Q(w_{1,1})}{U(Q)},\qquad
a_0(W)=\frac{\sum_{n=0}^{2}W(\alpha w_{n,1})}{v(W)}.
$$

Let $F_p,F_\beta$ denote the complete endpoint coordinate boxes of Chapter 11, with all nonnegativity, normalization, emissions, and tail inequalities. The selected finite domains are their level-five projections, with the level-five tail cell retained as one coordinate. The endpoint interval on that tail is valid because, from level five onward, each endpoint branch has a fixed ordering. Residual endpoint-box conditions may be imposed on the full residuals; the construction below satisfies them on the whole carriers.

For a level $L\le5$, let $\ell_{s,r}^L(D)$ be the total variation distance between the level-$L$ complete-word/tail partition of $D$ and that of $P_{s,r}$, including the infinite outcome in the tail cell. The selected event-output dual permits degree-at-most-two marginal potentials and whole-input polynomial multipliers in the raw displayed coordinates. Its two directional expressions are

$$
\begin{aligned}
S_B(Q,W)&=V_p(Q)-V_\beta(W)+\frac12(F_p(Q)+F_\beta(W))
       +\phi(Q)\bigl(b_0(Q)-h(W)\bigr),\\
S_A(W,Q)&=V_\beta(W)-V_p(Q)+\frac12(F_p(Q)+F_\beta(W))
       +\psi(W)\bigl(a_0(W)-f(Q)\bigr),
\end{aligned}
$$

where

$$
F_p(Q)=c_p'(f(Q)-C)+\sum_r m_{p,r}(\ell_{p,r}^L(Q)-\rho_p),
$$

$$
F_\beta(W)=c_\beta'(h(W)-H)+\sum_r m_{\beta,r}(\ell_{\beta,r}^L(W)-\rho_\beta),
$$

with each loss coefficient nonnegative and each sum finite over supported targets. The input multipliers may depend on the whole descriptor; only the tested output is restricted to the event coordinate. A positive separator would be a pair of valid pointwise lower bounds for $S_B,S_A$ whose constants have positive sum.

The associated normalized-residual square subfamily is

$$
G_p(Q)=\lambda_B b_0(Q)^2-\lambda_A f(Q)^2
 +\alpha_0(f(Q)-C)+\beta_0(b_0(Q)-H)
 +c_p(\ell_{p,r}^L(Q)-\rho_p),
$$

$$
G_\beta(W)=\lambda_A a_0(W)^2-\lambda_B h(W)^2
 +\delta_0(h(W)-H)+\epsilon_0(a_0(W)-C)
 +c_\beta(\ell_{\beta,r}^L(W)-\rho_\beta),
$$

where $\lambda_A,\lambda_B,c_p,c_\beta\ge0$ and the affine coefficients are arbitrary. These squares are squares of normalized residual-event values; they are not assertions that the squares are raw-coordinate polynomials of degree two.

### 15.2 The rational complete-law pair

Define

$$
u_0=\frac{1829}{5000},\qquad U_0=\frac{3171}{5000},\qquad
v_0=\frac{46}{125},\qquad d=\frac{13}{15000},
$$

$$
t=\frac{78975}{2857232}
 =\frac{d}{2\rho_p-(b-a)},\qquad
s_a=\frac{1349641}{2857232}=\frac12-t,\qquad
s_b=\frac{1507591}{2857232}=\frac12+t.
$$

Set

$$
Q(w_{0,0})=u_0,
$$

$$
Q(w_{0,1})=1-\frac{1-H}{v_0}=\frac{995}{2484},
$$

$$
Q(w_{2,1})=C-U_0H=\frac{19907803}{911250000},
$$

$$
Q(w_{1,1})=U_0H-Q(w_{0,1})
=\frac{72763013}{776250000}.
$$

For every other finite $p$-word set

$$
Q(w_{n,i})=s_aP_{p,a}(w_{n,i})+s_bP_{p,b}(w_{n,i}),
$$

and set $Q(\infty_p)=0$. Define the suspended law by

$$
W=(1-v_0)\delta_\beta+v_0\,\alpha Q,
\qquad W(\infty_\beta)=0.
$$

Here $\alpha Q$ prefixes every finite word of $Q$ by $\alpha$ and assigns the corresponding mass to the infinite outcome. This is a pair of mathematical complete laws, not an initialized observer.

The full endpoint mixture $s_aP_{p,a}+s_bP_{p,b}$ has total mass one. Its alpha mass and event mass are respectively

$$
\frac{a+b}{2}+t(b-a),\qquad C-2t\rho_p.
$$

The correction on the four altered atoms has total

$$
u_0-\frac{a+b}{2}-t(b-a)+2t\rho_p
=-d+t\bigl(2\rho_p-(b-a)\bigr)=0.
$$

Consequently $Q$ is normalized, and the definition of $W$ makes $W$ normalized without conditioning on completion.

The exceptional endpoint inequalities are

$$
\frac9{25}\le\frac{995}{2484}\le\frac49,\qquad
\frac{54}{625}\le\frac{72763013}{776250000}\le\frac8{81},\qquad
\frac{324}{15625}\le\frac{19907803}{911250000}\le\frac{16}{729},
$$

and $a\le u_0\le b$. Every unchanged coordinate is a convex endpoint mixture. For marker zero and for marker one with $n\ge3$, the endpoint ratios are

$$
\frac{P_{p,b}(w_{n,0})}{P_{p,a}(w_{n,0})}
=\frac65\left(\frac{27}{25}\right)^n,\qquad
\frac{P_{p,b}(w_{n,1})}{P_{p,a}(w_{n,1})}
=\frac{81}{100}\left(\frac{27}{25}\right)^n.
$$

Thus the ordering is fixed on the unchanged ranges. Since $a\le v_0\le b$, the suspended coordinates inherited from them lie in their endpoint intervals. The remaining suspended margins are

$$
\begin{array}{c|c|c}
\text{atom} & \text{mass minus lower endpoint} & \text{upper endpoint minus mass}\\ \hline
\alpha w_{0,0}&66103/2812500&7933/312500\\
\alpha w_{0,1}&23/6750&1/1350\\
\alpha w_{1,1}&29867117/18984375000&136987/2109375000\\
\alpha w_{2,1}&123638407/170859375000&14512531/56953125000
\end{array}
$$

and $W(\beta)=79/125\in[3/5,2/3]$. Hence $Q\in F_p$ and $W\in F_\beta$ on the complete carriers.

### 15.3 All tails and the opposite residual boxes

For $j\ge3$, no altered $p$-coordinate occurs in the tail and

$$
Q(T_p(j))=s_a z_a^j+s_b z_b^j\le\lambda^j,
$$

because $z_a=2/9<4/15$ and $z_b=6/25<4/15$. The two remaining nontrivial checks are

$$
Q(T_p(1))=\frac{725441}{3105000}<\lambda,\qquad
Q(T_p(2))=\frac{327003972413}{6026973750000}<\lambda^2.
$$

The relation defining $W$ gives

$$
W(T_\beta(j))=v_0Q(T_p(j))\le b\lambda^j
$$

for all $j$. Thus all complete tails, including the zero-mass infinite outcomes, satisfy the original inequalities.

Since $W=(1-v_0)\delta_\beta+v_0\alpha Q$, direct prefix deletion gives

$$
\mathcal R_A(W)=Q
$$

as full measures, including all tail and infinite coordinates. Put $Z=\mathcal R_B(Q)$. Then

$$
Z(\beta)=\frac{1243750}{1969191},\qquad
1-Z(\beta)=\frac{725441}{1969191}\in[a,b].
$$

The exceptional $Z$-coordinate margins are

$$
\begin{array}{c|c|c}
\text{atom} & \text{mass minus lower suspended endpoint} & \text{upper endpoint minus mass}\\ \hline
\beta&311177/9845955&69044/1969191\\
\alpha w_{0,0}&365871334/15289227009&9540049661/382230675225\\
\alpha w_{0,1}&1872137/492297750&169987/492297750\\
\alpha w_{1,1}&881803/577914750&1623269/14447868750\\
\alpha w_{2,1}&4036404044/8829092593125&575293945052/1103636574140625
\end{array}
$$

For marker zero and marker one with $n\ge2$, write

$$
Z(\alpha w_{n,i})=A_0P_{\beta,a}(\alpha w_{n,i})+B_0P_{\beta,b}(\alpha w_{n,i}),
$$

$$
A_0=\frac{s_a(1-a)}{U_0},\qquad B_0=\frac{s_b(1-b)}{U_0},\qquad
A_0+B_0=\frac{3383091125}{3397606002}<1.
$$

The endpoint ratio on each branch increases by $27/25$ when $n$ increases. The lower endpoint inequalities at $(n,i)=(0,0)$ and $(2,1)$, together with the five exceptional checks above, therefore imply every remaining lower inequality; $A_0+B_0<1$ gives the upper inequalities. The residual tails satisfy

$$
Z(T_\beta(j))=\frac{Q(T_p(j+1))}{U_0}.
$$

At $j=0,1$ the margins are

$$
b-\frac{Q(T_p(1))}{U_0}=\frac{311177}{9845955},\qquad
b\lambda-\frac{Q(T_p(2))}{U_0}
=\frac{80708747827}{3822306752250},
$$

and for $j\ge2$,

$$
Z(T_\beta(j))\le
\frac{s_az_a+s_bz_b}{U_0}\lambda^j,\qquad
\frac{s_az_a+s_bz_b}{U_0}=\frac{1861149550}{5096409003}<b.
$$

Therefore $Z\in F_\beta$ and $\mathcal R_A(W)=Q\in F_p$ on the full carriers. In particular, every level-five projection and every residual endpoint-box projection allowed in the selected class contains this pair.

### 15.4 Means and every supported complete-configuration loss

The altered coordinates were chosen so that

$$
f(Q)=C,\qquad b_0(Q)=H,\qquad h(W)=1-v_0+v_0Q(w_{0,1})=H,\qquad a_0(W)=C.
$$

The endpoint coordinate-box triangle identities of Chapter 11 give

$$
\operatorname{TV}(Q,P_{p,a})=P_{p,a}(E_p)-C,\qquad
\operatorname{TV}(Q,P_{p,b})=C-P_{p,b}(E_p),
$$

and the corresponding suspended identities with $h(W)=H$. These are complete-law total variations, so all four complete endpoint configuration losses equal $\rho_p$ or $\rho_\beta$ as appropriate. Every coarser level-$L$ word/tail partition is obtained by contraction and therefore has loss at most, rather than necessarily equal to, its corresponding complete endpoint radius.

For every nonendpoint target supported by the original prior, use the source interval $[3/8,5/13]$. A direct complete-word calculation through level five, with the entire remaining mass (including infinity) bounded by the two tail masses, gives

$$
B_p=\frac{355994686242025987031}{26994670778880000000000}<\frac1{50},
$$

$$
B_\beta=\frac{3515477241015883163647}{421791730920000000000000}<\frac1{75},
$$

where $B_p$ and $B_\beta$ are upper bounds for the complete total variations from $Q,W$ to the native laws at $r_0=3/8$. The complete stopped-parser coupling supplied with the source gives, for $r,t\in[a,b]$,

$$
\operatorname{TV}(P_{p,r},P_{p,t})\le\frac{125}{57}|r-t|,\qquad
\operatorname{TV}(P_{\beta,r},P_{\beta,t})\le\frac{107}{57}|r-t|.
$$

Since $5/13-3/8=1/104$, the triangle inequality yields, uniformly for every $r\in[3/8,5/13]$,

$$
\operatorname{TV}(Q,P_{p,r})
<\frac1{50}+\frac{125}{5928}
=\frac{6089}{148200}<\rho_p,
$$

$$
\operatorname{TV}(W,P_{\beta,r})
<\frac1{75}+\frac{107}{5928}
=\frac{4651}{148200}<\rho_\beta.
$$

Indeed,

$$
\rho_p-\frac{6089}{148200}=\frac{178363777}{22507875000}>0,\qquad
\rho_\beta-\frac{4651}{148200}=\frac{26837}{6669000}>0.
$$

Every supported nonendpoint is in this interval, so every complete configuration loss is bounded before any averaging over configurations. Any level-$L$ partition loss with $L\le5$ is no larger by contraction of total variation.

### 15.5 Universal no-separator theorem for the event-output class

**Theorem 15.1 (event-output quadratic no-separator).** No coefficients in the selected class, over the real or rational numbers, produce pointwise bounds

$$
S_B(Q,W)\ge\kappa_B,\qquad S_A(W,Q)\ge\kappa_A
$$

on the declared complete level-five domains with $\kappa_B+\kappa_A>0$. No coefficients in the normalized-residual square subfamily produce lower bounds $G_p\ge\kappa_p$, $G_\beta\ge\kappa_\beta$ with $\kappa_p+\kappa_\beta>0$. The claim holds for every permitted $L\le5$ and every finite nonnegative combination of supported target losses.

**Proof.** At the admissible pair $(Q,W)$, the two event residuals vanish:

$$
b_0(Q)-h(W)=0,\qquad a_0(W)-f(Q)=0.
$$

The directional point masses

$$
\widehat\Gamma_B=\delta_{(Q,W)},\qquad
\widehat\Gamma_A=\delta_{(W,Q)}
$$

have common unweighted phase marginals $\delta_Q,\delta_W$. Consequently every whole-descriptor multiplier of either displayed event difference integrates to zero, and every marginal potential cancels between the two directions. The centered affine terms vanish by the equalities above. Every allowed loss term is nonpositive because endpoint losses equal their bounds and all interior losses are strictly below them. Therefore any valid pointwise lower bounds imply

$$
\kappa_B+\kappa_A\le F_p(Q)+F_\beta(W)\le0.
$$

For the square subfamily, the affine terms vanish and the square terms cancel exactly:

$$
\lambda_BH^2-\lambda_AC^2+\lambda_AC^2-\lambda_BH^2=0.
$$

The loss terms again have nonpositive sum, so $\kappa_p+\kappa_\beta\le0$. This is an exact coefficient-independent falsifier. $\square$

The same Dirac pair gives equality of the two scalar event laws, so all scalar convex-order tests of the displayed events pass, including every polynomial degree. This equality does not imply the missing complete-coordinate equation.

### 15.6 Exact missing coordinate and the limit of the conclusion

The residual formula gives

$$
Q(w_{0,1})-U_0W(\beta)=-\frac{97339}{388125000},
$$

and therefore

$$
\mathcal R_B(Q)(\beta)-W(\beta)
=-\frac{97339}{246148875}\ne0.
$$

Hence

$$
\operatorname{TV}(\mathcal R_B(Q),W)
\ge\frac{97339}{246148875}>0.
$$

The constant beta-coordinate test in (11.7) already fails. Since both directional marginals are point masses, the only coupling with these marginals is the displayed point mass; changing the coupling cannot repair this coordinate. The pair is therefore not a compatible pair of Chapter 11 and cannot be installed as an observer.

This is a failure of the selected event-output bridge, even though the pair has full endpoint-box membership, all complete tails, both exact event means, both actual event residual equations, the complete $A$ residual equation, and every supported complete-configuration loss. It is not a no-go theorem for the full degree-at-most-two word/tail vector class: the full residual equations of (11.7) remain required, and no global vector separator, zero-level compatible pair, finite exact attainer, evaluated unrestricted gap, or fixed-resource optimum is asserted. The distinction between raw-coordinate polynomial degree at most two and the normalized-residual square extension remains as stated in Section 15.1.

The realization theorem of Chapter 11 applies only after all complete-coordinate barycentre equations hold for common unweighted marginals. Thus its regeneration, rational approximation, finite atomicity, and all-shape infimum conclusions are not invoked for this pair. The original prior, source, paid histories, records, completion, Stop, zero and unit emissions, and possible noncompletion remain exactly those of the standing hypotheses. $\square$

## 追加锚（本行以下为增补区）
## 16. Joint mismatch necessity and the fixed full-residual certificate

Fix the installed finite or countable prior $\mu$, with $\mu(1),\mu(2)>0$, and choose symbolically one supported $k_\star\ge3$, so $\mu(k_\star)>0$.  Put

$$
a=\frac13,
\qquad b=\frac25,
\qquad r_\star=\frac{F_{k_\star+1}}{F_{k_\star+3}}\in\left[\frac38,\frac5{13}\right],
\qquad
\rho_p=\frac{1116529}{22781250},
\qquad
\rho_\beta=\frac{239}{6750}.
$$

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},
\qquad
E_\beta=\{\beta,\alpha w_{0,1}\},
\qquad
C=\frac{11758471}{22781250},
\qquad
H=\frac{5261}{6750}.
$$

$$
\eta=\frac{14219478376}{318644812890625},
\qquad g=\frac{\eta}{400000}.
$$

The depth $K$ is the one positive integer sampled once by the original source.  All statements below retain the original $m=2,d=1,\ell=2,n=4$ control, both seeds, every paid rejection and finite return, all marker triples and held registers, the third write-before-latch, completion and matching Stop.  Complete carriers include every infinite noncompletion outcome.  The same acquired-letter kernels are used by actual and synthetic updates, and configuration TV is taken before its configuration average.

The full source and observer contract is Section 2. In particular, the full-record renderer $I_{C_0(h)}$ is the same measurable bijection on every actual record fibre, including each future operation block and the matching Stop. No future conditioning, reset, extra Read or measurement, count, clock, posterior, configuration-distribution input or exact-real port is available. Zero and unit emissions and positive noncompletion mass remain allowed in the original unrestricted class; regularity below concerns the compatible-law representation and its approximants. The program, installed numerics, sampler microstates, workspace, output indices and every persistent random choice belong to COMPLETE.

### 16.1 Compatible full-law pairs

Let $\Omega_p,\Omega_\beta$ be the complete raw carriers, including their infinity cells, and let

$$
\mathcal K_p=\{Q\in\mathcal P(\Omega_p):a\le Q(\alpha)\le b,\ Q(T_p(j))\le(4/15)^j\ \forall j\ge0\},
$$

$$
\mathcal K_\beta=\{W\in\mathcal P(\Omega_\beta):a\le1-W(\beta)\le b,\ W(T_\beta(j))\le b(4/15)^j\ \forall j\ge0\},
$$

where the tail sets contain all words of return depth at least $j$ and the corresponding infinity cell, for every $j\ge0$.  Write

$$
u(Q)=Q(\alpha),\quad U(Q)=1-u(Q),\quad v(W)=1-W(\beta),
$$

$$
\mathcal R_B(Q)(E)=\frac{Q(\beta E)}{U(Q)},
\qquad
\mathcal R_A(W)(F)=\frac{W(\alpha F)}{v(W)}.
$$

The denominators obey $U\ge3/5$ and $v\ge1/3$.  A compatible pair is a pair of Borel probability measures

$$
\Gamma_B\ \,\text{on }\mathcal K_p\times\mathcal K_\beta,
\qquad
\Gamma_A\ \,\text{on }\mathcal K_\beta\times\mathcal K_p
$$

with common unweighted marginals

$$
(\Gamma_B)_1=(\Gamma_A)_2=\nu_p,
\qquad
(\Gamma_B)_2=(\Gamma_A)_1=\nu_\beta,
\tag{16.1}
$$

and, for every continuous input test and every complete atom (including infinity),

$$
\int \phi(Q)\,[\mathcal R_B(Q)(\eta)-W(\eta)]\,d\Gamma_B=0,
\qquad
\int \psi(W)\,[\mathcal R_A(W)(\omega)-Q(\omega)]\,d\Gamma_A=0.
\tag{16.2}
$$

The continuous-test form extends to bounded Borel input tests by the compact-metric signed-measure argument following Definition 11.2. Atomwise identities also extend to every complete event by countable summation and dominated convergence; bounded tests and normalized residual laws supply domination, including for each tail with its infinite outcome.  Thus (16.2) is a full-descriptor conditional equation, not an equation conditioned only on a residual value.

Define

$$
\begin{aligned}
J_p&=\int (u-a)(b-u)\,d\nu_p,\\
J_\beta&=\int (v-a)(b-v)\,d\nu_\beta,\\
M_B&=\int (u(Q)-v(W))^2\,d\Gamma_B(Q,W),\\
M_A&=\int (v(W)-u(Q))^2\,d\Gamma_A(W,Q).
\end{aligned}
\tag{16.3}
$$

For each supported depth $k$, put $r_k=F_{k+1}/F_{k+3}$.  Define

$$
\mathcal J(\Gamma_B,\Gamma_A)=\max\left\{
\sup_{k:\mu(k)>0}\int\operatorname{TV}(Q,P_{p,r_k})\,d\nu_p(Q)-\rho_p,
\quad
\sup_{k:\mu(k)>0}\int\operatorname{TV}(W,P_{\beta,r_k})\,d\nu_\beta(W)-\rho_\beta
\right\}.
$$

This is the maximum of the two supported-depth suprema; neither supremum is assumed to be attained at a supported depth.  It is the compatible-pair functional of the full original target, with TV inside the configuration integral.

### 16.2 Finite same-object mismatch estimate

**Lemma 16.1 (same-table mismatch control).** The actual return variation of any finite regular stationary table is at most the sum of the square roots of its two directional mismatch energies, as in (16.5).

**Proof.** Consider first one finite regular same-update table with p labels $i$, suspended labels $j$, rows $\pi,\tau$, kernels $B,A$, and emissions $u_i,v_j\in[a,b]$, satisfying

$$
\pi B=\tau,
\qquad \tau A=\pi.
\tag{16.4}
$$

Its actual three-stage return distribution is the single probability law

$$
\Xi(i,j,i')=\pi_iB_{ij}A_{ji'}.
$$

The two directional edge laws are the marginals of this same object:

$$
\Gamma_B^{\rm fin}(i,j)=\pi_iB_{ij},
\qquad
\Gamma_A^{\rm fin}(j,i')=\tau_jA_{ji'}.
$$

Consequently, pointwise on every triple,

$$
|u_i-u_{i'}|
\le |u_i-v_j|+|v_j-u_{i'}|.
$$

Taking expectation under $\Xi$, then using (16.4), gives

$$
V_\pi:=\sum_{i,j,i'}\pi_iB_{ij}A_{ji'}|u_i-u_{i'}|
\le \int|u-v|\,d\Gamma_B^{\rm fin}
   +\int|v-u|\,d\Gamma_A^{\rm fin}.
$$

Both edge measures are probability measures.  Cauchy–Schwarz therefore yields the same-table estimate

$$
V_\pi\le \sqrt{M_B^{\rm fin}}+\sqrt{M_A^{\rm fin}}.
\tag{16.5}
$$

No independently selected edge distributions occur in (16.5): the first marginal is $\pi B=\tau$, and the second is $\tau A=\pi$, exactly as required by the actual triple. $\square$

### 16.3 Passage from an arbitrary compatible Borel pair

**Theorem 16.2 (joint necessity on arbitrary compatible Borel flows).** Every compatible pair in Section 16.1 obeys (16.10), for the fixed installed prior with positive endpoint masses and a supported nonendpoint.

**Proof.** Take any compatible pair (16.1)–(16.2).  Apply the supplied joint finite-flow regeneration to obtain, for $\varepsilon_n\to0$, one finite regular table at each stage whose two own-law flow measures converge jointly to $\Gamma_B$ and $\Gamma_A$.  Its two exact flow identities are (16.4), and its configuration losses against every complete target differ from the compatible-pair losses by a quantity $\delta_n\to0$.  Apply the supplied rationalization to that same table, choosing the rational approximation error to tend to zero as well.  The resulting single rational table still has both exact flows and one pair of own generated full laws.  This is the PAIRED regeneration/rationalization result; no new compactness or one-sided quadrature is being inserted.

Theorem 11.4 gives phase loss errors at most $81\varepsilon_n/44$ and $61\varepsilon_n/44$ on the upper side, uniformly over complete targets, together with joint convergence of its two own-law flows. For each such finite shape, Lemma 11.6 makes the rational flow masses and their own generated law atoms converge. Choose its maximal law displacement and the sum of the absolute flow-weight errors in each direction at most $1/n$. This preserves the joint weak limit: for a bounded continuous test, uniform continuity controls displacement of each law pair, and the sum of the absolute changes of its finitely many flow weights controls the remaining integral. This is a diagonal choice of the supplied two-flow approximation, not a limit assertion about conditional kernels.

For each rational table, use the original-domain product realization.  In the original third-completion update, the complete record is written and latched before the source-independent private row is sampled.  The row is exactly $\pi_n$ at every positive fourth-segment p history and exactly $\tau_n$ after a p-beta return; a suspended-alpha return returns it to $\pi_n$.  The same $(B_n,A_n)$ are used on acquired and synthetic updates.  The installed program, numerical table, sampler states, workspace and persistent randomness are charged to COMPLETE.  The original $C_0$, both seeds, marker and held records, paid histories, every finite fourth return, completion and Stop remain in the product.  The once-sampled $K$ is never resampled.  The decoder laws retain their infinity cells; the geometric $4/15$ bound proves their zero mass without conditioning on completion.

Every rational table has finite nonempty phase label sets, positive probability rows, stochastic $B_n,A_n$, regular emissions and both identities (16.4). These are all the table hypotheses of [PAID, Definition 2.1 and Lemma 2.1.1], with observer period one. Before the latch, retain original control with fair synthesis; completing letters clear the private label and retain the original pendingStop and delivery transitions. A fixed rational categorical sampler uses fresh independent fair bits, finite rational thresholds and reusable finite rejection workspace, as in Corollary 11.7. The identical represented sampler implements actual and synthetic updates. Its internal service adds no source query; its almost-sure termination gives no finite worst-case bit or time bound. Source-independent initial sampling is not a runtime oracle. Neither the Borel flows nor their disintegrations, barycentres or analysis rows are installed as continuous registers.

At every positive fourth-segment history $h$, the target remains $\sum_k\nu_h(k)P_{s,r_k}$ for the same once-sampled $K$. Apply convexity to the target separately inside each configuration's TV, then average and apply the common renderer. The finite paid-history witnesses and the summable likelihood-ratio domination of [PAID, Lemma 14.1] retain every supported depth under a countable prior. They do not require a maximizing depth or a pure-source runtime experiment. Here $e(M)$ is exactly (1.2), and $V(M)$ denotes the unweighted acquired-return statistic $\mathcal V(M)$ of [RETURN9, Definition 9.1] on the seed-1, marker-100 fibre. That fibre is used for a necessary statistic; all other original histories remain in the risks.

PAID initialization and countable-prior domination, together with the configurationwise TV comparison, give an original observer $M_n$ with

$$
e(M_n)\le \mathcal J(\Gamma_B,\Gamma_A)+\delta_n,
\qquad \delta_n\longrightarrow0,
\tag{16.6}
$$

where $e(M_n)$ is its maximum of the two original configuration excesses.  The actual-return statistic on the designated positive-history fibre is exactly $V_{\pi_n}$, because every positive history has the same source-independent stationary row.  Applying (16.5) to that same table gives

$$
V(M_n)=V_{\pi_n}
\le \sqrt{M_{B,n}}+\sqrt{M_{A,n}}.
\tag{16.7}
$$

The functions $(Q,W)\mapsto(u(Q)-v(W))^2$ are bounded continuous on the compact descriptor products.  Joint weak convergence of the two own-law flows therefore gives

$$
M_{B,n}\to M_B,
\qquad M_{A,n}\to M_A.
\tag{16.8}
$$

No convergence of a composed disintegration or of a Markov product is used.

The supplied original risk–return theorem applies to each $M_n$ and gives the strict finite inequality

$$
g<\frac{61}{11}e(M_n)+\frac{19}{11}\sqrt{V(M_n)}.
\tag{16.9}
$$

Insert (16.6) and (16.7), then pass to the limit using (16.8).  The strict sign is thereby correctly weakened to a non-strict sign:

$$
\boxed{
\frac{61}{11}\mathcal J(\Gamma_B,\Gamma_A)
 +\frac{19}{11}\sqrt{\,\sqrt{M_B}+\sqrt{M_A}\,}
\ge g.}
\tag{16.10}
$$

This holds for every compatible Borel pair on the unchanged original domain. $\square$

### 16.4 Edge-mismatch floor at zero excess

**Corollary 16.3 (necessary mismatch floor at zero excess).** On the same compatible pair, $\mathcal J=0$ implies (16.16); the two energies are not optimized separately.

**Proof.** Put

$$
m_p=\int u\,d\nu_p,
\quad m_\beta=\int v\,d\nu_\beta,
\quad t=m_p+m_\beta,
$$

$$
q=\int Q(\beta\beta)\,d\nu_p,
\qquad
z=\int W(\alpha\alpha)\,d\nu_\beta.
$$

Testing the first residual equation with $1-u(Q)$ and the atom $\beta$, and the second with $v(W)$ and the atom $\alpha$, gives the exact identities

$$
q=\int(1-u)(1-v)\,d\Gamma_B,
\qquad
z=\int vu\,d\Gamma_A.
\tag{16.11}
$$

For $x\in[a,b]$,

$$
x^2=(a+b)x-ab-(x-a)(b-x).
$$

Expanding $(u-v)^2$, using the common unweighted marginals in both directional flows, and then using (16.11), gives the supplied exact quartet identities

$$
D_B:=\frac{26}{15}-\frac{19}{15}t-2q
   =J_p+J_\beta+M_B,
\tag{16.12}
$$

$$
D_A:=\frac{11}{15}t-\frac4{15}-2z
   =J_p+J_\beta+M_A.
\tag{16.13}
$$

Thus

$$
E:=D_A+D_B
 =\frac{22}{15}-\frac8{15}t-2(q+z)
 =2(J_p+J_\beta)+M_A+M_B
 \ge M_A+M_B.
\tag{16.14}
$$

Since

$$
\sqrt{M_B}+\sqrt{M_A}
\le\sqrt{2(M_A+M_B)}
\le\sqrt{2E},
$$

(16.10) also implies

$$
\frac{61}{11}\mathcal J
 +\frac{19}{11}(2E)^{1/4}\ge g.
\tag{16.15}
$$

At $\mathcal J=0$, apply $\sqrt{M_B}+\sqrt{M_A}\le\sqrt{2(M_A+M_B)}$ directly in (16.10). Since all terms are nonnegative, raising the resulting inequality $(2(M_A+M_B))^{1/4}\ge11g/19$ to the fourth power gives the explicit necessary floor

$$
\boxed{
M_A+M_B\ge\kappa,
\qquad
\kappa=\frac12\left(\frac{11g}{19}\right)^4
 =\frac12\left(\frac{11\eta}{7\,600\,000}\right)^4>0.}
\tag{16.16}
$$

Equivalently, the exact rational value is

$$
\kappa=
\frac{146132042055060050874608124299926801811521}
{16793910307653031964936642766121613852796435821801424026489257812500000000000000000}.
$$

This is a joint same-pair necessity.  It does not lower-bound $\mathcal J$ by itself and does not imply that the two mismatch energies can be attained independently.  It also does not force the synchronized endpoint chord of the four-coordinate theorem. $\square$

### 16.5 Exact fixed finite full-residual template

Let $\pi_5$ retain the complete coordinates

$$
Q(\alpha),\quad Q(w_{j,i}),\quad W(\beta),\quad W(\alpha w_{j,i})
\quad(0\le j<5,\ i\in\{0,1\}),
$$

the residual cells $Q(T_p(5))$ and $W(T_\beta(5))$, each containing every longer word and its infinity outcome.  Let $Z_p$ and $Z_\beta$ be the outer domains of these projected coordinates subject to normalization, nonnegativity, the endpoint boxes (11.29), $a\le u\le b$, $a\le v\le b$, and all inherited tail inequalities from (11.2).  They are outer domains: every full zero-face descriptor projects into them, but a point of either domain is not asserted to extend to a full law or a compatible flow.  Explicitly, for every retained level-five cell $c$ at phase $s$, impose

$$
\min\{P_{s,a}(c),P_{s,b}(c)\}\le D(c)\le
\max\{P_{s,a}(c),P_{s,b}(c)\},
$$

together with nonnegative cell masses summing to one and the level-five tail inequalities (including the infinity mass) inherited from (11.2).

Here $\alpha=w_{0,0}$ is one p atom, even where its coordinate is displayed twice. Normalization counts each distinct cell once. For $0\le j\le5$, the retained p tail mass is

$$
\sum_{n=j}^{4}\sum_{i=0}^{1}Q(w_{n,i})+Q(T_p(5)),
$$

and the suspended tail mass is the corresponding sum of $W(\alpha w_{n,i})$ plus $W(T_\beta(5))$. Their bounds are $(4/15)^j$ and $b(4/15)^j$, respectively; an empty sum is zero. Every longer word and the infinite outcome stays inside the retained tail cell. Its endpoint interval follows from (11.29): for $n\ge5$, the endpoint ratios from Section 2 have fixed order on both branches, so summing the atomwise bounds gives precisely the two native tail endpoints. These finite constraints do not assert a completion of an outer-domain point to a full descriptor.

Use the complete level-four partitions

$$
\mathscr F_p=\{\{\alpha\}\}\cup
 \{\{w_{j,i}\}:0\le j<4,\ i\in\{0,1\}\}\cup\{T_p(4)\},
$$

$$
\mathscr F_\beta=\{\{\beta\}\}\cup
 \{\{\alpha w_{j,i}\}:0\le j<4, i\in\{0,1\}\}\cup\{T_\beta(4)\}.
$$

The tail cells include the entire infinity outcome.  For $E\in\mathscr F_\beta$ and $F\in\mathscr F_p$, define the full-event residual coordinates

$$
b_E(Q,W)=Q(\beta E)-(1-u(Q))W(E),
\qquad
a_F(W,Q)=W(\alpha F)-v(W)Q(F).
\tag{16.17}
$$

All coordinates in (16.17) are determined by the level-five projection. Indeed, $\beta\{\beta\}=\{w_{0,1}\}$, $\beta\{\alpha w_{j,i}\}=\{w_{j+1,i}\}$, $\beta T_\beta(4)=T_p(5)$, $\alpha\{w_{j,i}\}=\{\alpha w_{j,i}\}$ and $\alpha T_p(4)=T_\beta(4)$, including the respective infinite outcomes. Thus the two pointwise expressions below are functions of the displayed outer coordinates.

These are exact residual equalities in the input-conditioned integral sense: compatible flows annihilate them against the permitted input multipliers, without pointwise vanishing on arbitrary outer-domain pairs.  For example, the $b_E$ term is annihilated by (16.2) with the bounded input test $(1-u)\chi_E$; $a_F$ is annihilated with $v\xi_F$.  The positive original denominators are retained inside these multipliers and are never replaced by an unnormalized or future-conditioned equation.

Set

$$
f=Q(E_p),\quad h=W(E_\beta),\quad q=Q(\beta\beta),\quad z=W(\alpha\alpha).
$$

The fixed potential and multiplier spaces are exactly the following.  Every $\chi_E$ is in $\mathcal P$, and every $\xi_F$ is in $\mathcal S$:

$$
\mathcal P=\operatorname{span}\{1,u,u^2,f,uf,q,Q(w_{3,1})\},
$$

$$
\mathcal S=\operatorname{span}\{1,v,v^2,h,vh,z,W(\alpha w_{3,1})\}.
\tag{16.18}
$$

For $r\in\{a,b,r_\star\}$, put

$$
\ell_{p,r}(Q)=\operatorname{TV}(\pi_4Q,\pi_4P_{p,r})-\rho_p,
\qquad
\ell_{\beta,r}(W)=\operatorname{TV}(\pi_4W,\pi_4P_{\beta,r})-\rho_\beta.
\tag{16.19}
$$

The template asks for potentials $P\in\mathcal P$, $S\in\mathcal S$ and input multipliers $\chi_E\in\mathcal P$ for every $E\in\mathscr F_\beta$, $\xi_F\in\mathcal S$ for every $F\in\mathscr F_p$, all with rational coefficients in the respective seven-dimensional bases (16.18).  The event coefficients satisfy $\alpha_0,\beta_0\in\mathbb Q$.  The risk coefficients satisfy

$$
\lambda_{s,r}\in\mathbb Q_{\ge0}
\qquad\text{for every }s\in\{p,\beta\}
\text{ and }r\in\{a,b,r_\star\}.
$$

The thresholds satisfy $\delta_B,\delta_A\in\mathbb Q$ and $\delta_B+\delta_A>0$.  The $\ell^1$ norm of all scalar coefficients in these expansions is at most one; it includes both potential expansions, every input-multiplier expansion, both event coefficients and all six phase-indexed risk coefficients $\lambda_{s,r}$.  There are ten suspended partition cells and nine p partition cells, since $\{\alpha\}=\{w_{0,0}\}$. Hence the normed rational coefficient vector has exactly

$$
2\cdot7+(10+9)\cdot7+2+6=155
$$

entries. The two rational thresholds are additional variables and are not included in that norm. Coefficients of either potential, every input multiplier and the two event terms may have either sign; only the six risk weights must be nonnegative.

Define

$$
\begin{aligned}
G_B(Q,W)={}&P(Q)-S(W)+\sum_{E\in\mathscr F_\beta}\chi_E(Q)b_E(Q,W)\\
&+\alpha_0(f-C)+\sum_{r\in\{a,b,r_\star\}}\lambda_{p,r}\ell_{p,r}(Q),
\\[2mm]
G_A(W,Q)={}&S(W)-P(Q)+\sum_{F\in\mathscr F_p}\xi_F(W)a_F(W,Q)\\
&+\beta_0(h-H)+\sum_{r\in\{a,b,r_\star\}}\lambda_{\beta,r}\ell_{\beta,r}(W).
\end{aligned}
\tag{16.20}
$$

The exact certificate system is

$$
G_B(Q,W)\ge\delta_B\quad\text{for every }(Q,W)\in Z_p\times Z_\beta,
\tag{16.21}
$$

$$
G_A(W,Q)\ge\delta_A\quad\text{for every }(W,Q)\in Z_\beta\times Z_p,
\tag{16.22}
$$

with (16.21)–(16.22) checked on every absolute-value sign cell of the projected TVs in (16.19), including the residual and infinity cells.  Clearing a denominator is lawful only after retaining $U\ge3/5$ and $v\ge1/3$; the displayed form (16.17) already avoids that loss.

#### 16.5.1 Conditional sufficiency of the certificate

**Proposition 16.4 (conditional full-residual separator).** If the rational coefficient system (16.18)–(16.22) has a solution on the stated outer domains, no compatible full-law pair has $\mathcal J=0$.

**Proof.** Suppose a compatible pair had $\mathcal J=0$ and that a coefficient tuple satisfying (16.21)–(16.22) existed.  The zero-face endpoint geometry supplies

$$
\int f\,d\nu_p=C,
\qquad
\int h\,d\nu_\beta=H.
\tag{16.23}
$$

Integrate (16.21) against $\Gamma_B$ and (16.22) against $\Gamma_A$.  The two potential differences cancel by the common marginals (16.1).  Every residual term vanishes by (16.2), with the input-conditioned multipliers described after (16.17).  The event terms vanish by (16.23).  All three targets $a,b,r_\star$ come from actually supported depths of the installed prior.  For every $r\in\{a,b,r_\star\}$, contraction of TV under the complete projection $\pi_4$, followed by the corresponding supported-depth supremum bound at $\mathcal J=0$, gives

$$
\int\ell_{p,r}(Q)\,d\nu_p(Q)
\le\int\operatorname{TV}(Q,P_{p,r})\,d\nu_p(Q)-\rho_p\le0,
$$

$$
\int\ell_{\beta,r}(W)\,d\nu_\beta(W)
\le\int\operatorname{TV}(W,P_{\beta,r})\,d\nu_\beta(W)-\rho_\beta\le0.
$$

All six $\lambda_{s,r}$ coefficients are nonnegative, and (16.1) identifies these phase integrals with their corresponding flow integrals.  Thus all six weighted risk terms have nonpositive integrals.  This uses no maximizing supported depth.  Hence

$$
\int G_B\,d\Gamma_B+\int G_A\,d\Gamma_A\le0,
$$

whereas (16.21)–(16.22) force this same sum to be at least
$\delta_B+\delta_A>0$, a contradiction.

This argument uses both full residual flows, both common unweighted marginals, and the entire level-four tail; it does not use a finite-shape or native-mixture restriction. $\square$

#### 16.5.2 The unresolved rational coefficient problem

**Open problem 16.5 (the fixed rational coefficient boundary).** For the symbolic $r_\star$ above, no rational coefficient tuple satisfying the global system (16.21)–(16.22) has been established, and no exact proof that this fixed ansatz is infeasible has been established.  The exact unresolved statement is therefore

$$
\exists\,(P,S,\chi,\xi,\alpha_0,\beta_0,\lambda,\delta_B,\delta_A)
\quad\text{over the stated rational coefficient domain such that (16.18)–(16.22) hold globally.}
\tag{16.24}
$$

The universal quantifiers in (16.21)–(16.22) range over the full outer projections and every TV sign cell.  A violating projected descriptor would refute a proposed tuple; a projected feasible point, or failure to find a tuple, would neither provide a compatible full-law pair nor prove the original zero face empty.  Thus (16.24) is a bounded null boundary for this particular degree and event basis, not a substitute for the unrestricted same-prior alternative.

The [sparse-literal-history transport results, Chapters 20–24](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md), concern exact finite literal-tree capacity and replay.  They supply no stochastic full-flow/configuration-TV correspondence, so they do not decide (16.24) or the zero-face question.

### 16.6 Attribution and applicability limits

The mismatch theorem uses Theorem 11.4, Lemma 11.6 and Corollary 11.7, [PAID, Lemmas 2.1.1 and 14.1], and [RETURN9, Theorems 9.2 and 9.3], with equation (12.7) supplying the quartet identities.  The necessary floor is compatible with an off-chord zero pair, an unattained zero infimum, or a positive unrestricted gap.  The synchronized endpoint-chord rigidity and its supported-nonendpoint exclusion remain conditional on that chord; the event means in (16.23) are not equations prescribing the immediate-emission means $m_p,m_\beta$.  No universal formal verification, global novelty, finite exact attainment or resource optimum follows from (16.10), (16.16), or the unresolved certificate system (16.24).

The finite template restricts the certificate search alone. It restricts neither the complete descriptor marginals nor the finite observer shapes in the original problem, and assumes no reversibility, $A=I$, native mixture, constant emission, mixing, private-kernel contraction, conservation, positivity margin, resource or defect budget. Small actual-return variation, complete-law dispersion, suspended-to-p mismatch and paired event ranges remain different quantities attached to one observer. No product of independently attainable values is used. The event constraints in (16.23) are expectations of complete semantic events. They are not runtime observations; the indexed paired arrays determine emissions only on known common $B,A$ under Theorem 4.1 and the projected-fixed-point plus unprojected-equation test of Corollary 4.2.

Theorem 13.2 supplies an exact one-sided finite-support construction under its additional hypothesis, but it may change both joint flows. It cannot replace the prescribed two-flow convergence used in Theorem 16.2. Chapter 15 excludes a specified event-output separator class with a full-law pair that fails a full residual coordinate; that pair is not a compatible witness for (16.1)–(16.2), and its obstruction does not decide (16.24). The synchronized chord remains the conditional fibre of Theorem 12.2 and Corollary 12.3. In particular, the four coordinates $11/30,11/30,181/450,61/450$ at $\theta=1/2$ have no unconditional zero-face forcing assertion here.

The direct tools are the finite triple triangle inequality, Cauchy–Schwarz, continuity of bounded squared emission differences, and integration of the two full residual equations. The compact law spaces, common-flow regeneration and rationalization belong to Chapter 11; the directed crossing-flow repair and its simultaneous configuration-loss comparison belong to [RETURN9, Section 9](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md); the initialized full-source realization and countable-prior witnesses belong to [PAID, Lemmas 2.1.1 and 14.1](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md). These are ordinary source-specific mathematical deductions, with no additional compactness, coupling-existence or rounding theorem claimed.

The applicable distinctions in the primary literature are those of Sections 9 and 11.8: positive realization through invariant cones [Monras–Winter, Definition 5 and Theorem 6](https://arxiv.org/html/1412.3634v1) and positive Markov-form realization [Taghavian–Sjolund, Sections I–III](https://arxiv.org/html/2502.21102v3) concern prescribed output processes or transfer functions; [Leskela–Vihola, Theorems 1.2–1.3](https://arxiv.org/html/1404.0999v3) concerns finite-dimensional integrable laws and conditional martingale couplings. Those results do not supply the two original unweighted full-descriptor residual flows with configuration-before-TV control. No implication from controlled state-identification experiments or an approximate output-law comparison is used to add an observation to this source.

The exact remaining finite mathematical task is the rational existence question (16.24), with every outer-domain sign cell retained. A separator must satisfy both global inequalities with their common coefficients and positive threshold sum; an infeasibility conclusion must concern that entire coefficient domain. Neither outcome by itself constructs an original observer, and failure of this finite ansatz supplies no unrestricted zero witness. The alternatives of exact finite common attainment, an unattained zero infimum and a positive unrestricted gap retain Theorems 11.5 and 11.8 and their exact sampler hypotheses. The two-endpoint-only attainer and the strictly positive-excess rational witness keep their separate prior and risk scopes. No coefficient tuple, exact infeasibility proof, evaluated compact minimum, resource optimum or universal formal application is supplied; these boundaries remain open.

## 追加锚（本行以下为增补区）

## 17. A six-cell complete-residual test for the full-vector certificate

### 17.1. Definitions and scope

Fix the installed finite or countable prior $\mu$, with
$\mu(1),\mu(2)>0$, and choose an actually supported
$k_\star\ge3$. Throughout,
$$
a=\frac13,\quad b=\frac25,\quad
r_\star=\frac{F_{k_\star+1}}{F_{k_\star+3}}\in[3/8,5/13],
$$
$$
\rho_p=\frac{1116529}{22781250},\quad
\rho_\beta=\frac{239}{6750},\quad
C=\frac{11758471}{22781250},\quad H=\frac{5261}{6750}.
$$
Use exactly the level-five outer domains $Z_p,Z_\beta$, level-four
complete output partitions, seven-term input and potential bases, and
coefficient norm of Section 16.5. In particular, all six risk
coefficients are nonnegative and count in that norm. The atom
$w_{0,0}=\alpha$ occurs once, so the output partitions have nine p cells
and ten suspended cells. All tail cells retain infinity.

Write $w_{n,0}=(\beta\alpha)^n\alpha$,
$w_{n,1}=(\beta\alpha)^n\beta\beta$, and $t_r=r(1-r)$. The native laws are
$$
P_{p,r}(w_{n,0})=rt_r^n,\qquad
P_{p,r}(w_{n,1})=(1-r)^2t_r^n,
$$
$$
P_{\beta,r}(\beta)=1-r,\qquad
P_{\beta,r}(\alpha w_{n,i})=rP_{p,r}(w_{n,i}).                 \tag{17.1}
$$
Their infinite masses are zero. Denote the complete depth-at-least-$j$
tails by $T_p(j),T_\beta(j)$, with infinity included.

The original source is unchanged: one positive integer $K$ is sampled
once; $m=2,d=1,\ell=2,n=4$, both seeds, all marker triples and held
registers, all paid rejections and finite returns, the third write before
the latch, fourth completion, and matching Stop remain present. The
full-record renderer is the original $I_{C_0(h)}$, and configuration TV
precedes averaging. No source reset, future conditioning, additional
Read, clock, posterior, configuration-distribution input, or numerical
oracle is introduced.
The original acquired-letter stochastic kernels must be identical in
actual and synthetic updates; no count input or auxiliary measurement is
available. The original COMPLETE carrier includes control, installed
program and numerics, workspace, represented sampler states and every
persistent random choice. Source-independent initialization does not
provide an exact-real runtime port.

The objects below are complete probability laws and their projected
Dirac edge measures. They are not asserted to be an initialized observer.
Their complete A residual vanishes; their complete B residual does not.
This gives a test of arbitrary proposed coefficients, not a null for the
full ansatz.

### 17.2. A rational complete-law pair

Define the following positive rational constants:
$$
c=\frac{467}{2000},\qquad
v=\frac{c(1+cH)}{C+c}=\frac{201200388183}{546492572000},
$$
$$
u=1-\frac cv=\frac{157589663}{430835949},\qquad U=1-u,
\qquad q=1-\frac{1-H}{v}=\frac{2177500722109}{5432410480941},
$$
$$
d_0=q-U(1-v)=\frac{1212298469447}{10864820961882000},\qquad
s=cq-d_0=\frac{21160011224072}{226350436705875},
$$
$$
\varepsilon=sc^2-\frac{1944}{390625}
=\frac{29150733012563}{242345221312500000}.
                                                               \tag{17.2}
$$
Here $c$ is a law-construction parameter, unrelated to the source
parameters or an acquired counter. In particular,
$$
a<u,v<b,\quad \frac29<c<\frac6{25}<\frac4{15},\quad
0<d_0<\varepsilon.
                                                               \tag{17.3}
$$
First define an auxiliary law vector by
$$
Q^0(w_{n,0})=uc^n\quad(n\ge0),\qquad
Q^0(w_{0,1})=q,\qquad
Q^0(w_{n,1})=sc^{n-1}\quad(n\ge1).
$$
Set
$$
Q=Q^0+\varepsilon(\delta_{w_{3,0}}-\delta_{w_{3,1}}),
\qquad W=(1-v)\delta_\beta+v\alpha Q,
\qquad Q(\infty_p)=W(\infty_\beta)=0.                       \tag{17.4}
$$
The prefix $\alpha Q$ includes the corresponding infinite outcome.

**Proposition 17.1.** The laws in (17.4) are normalized and lie in their full
endpoint coordinate boxes and in $\mathcal K_p,\mathcal K_\beta$ of
[PAIRED, (11.2)]. Their level-five projections lie in the exact prescribed
outer domains. They have
$$
Q(E_p)=C,\qquad W(E_\beta)=H,\qquad
Q(w_{3,1})=P_{p,b}(w_{3,1})=\frac{1944}{390625}.              \tag{17.5}
$$

**Proof.** The definitions imply
$$
Uv=c,\qquad
d_0=u+q-1+c,\qquad
u+q+\frac{uc+s}{1-c}=1.
$$
Thus $Q^0$ sums to one, and the modification in (17.4) preserves that sum.
Also
$$
s=-1+\frac{1-H+cH}{v},\qquad
q+s(1+c)=-c+\frac{c(1+cH)}v=C.
$$
The modification is outside $E_p$, and
$1-v+vq=H$; this proves the two means in (17.5). The remaining equality
in (17.5) follows from (17.2).

Here are finite rational bounds proving all exceptional endpoint-box
comparisons. For a phase and atom let $l,h$ be its smaller and larger
native endpoint masses and let $x$ be its mass in (17.4). Each table entry
$(L,R)$ asserts $10^{12}(x-l)\ge L$ and
$10^{12}(h-x)\ge R$; the p upper margin at $(3,1)$ is exactly zero.
Every entry follows by substitution in (17.1)--(17.4) and cross multiplication.

| $(n,i)$ | p lower and upper bounds | suspended lower and upper bounds |
|---|---:|---:|
| $(0,0)$ | $(32443160865,34223505801)$ | $(23555628002,25333260886)$ |
| $(0,1)$ | $(40835085962,43609358482)$ | $(3574146520,574001627)$ |
| $(1,1)$ | $(7083412411,5282019687)$ | $(1495672409,142516891)$ |
| $(2,1)$ | $(1092376798,119497001)$ | $(720524372,257917694)$ |
| $(3,0)$ | $(1118987582,752633450)$ | $(539393875,453119802)$ |
| $(3,1)$ | $(99334711,0)$ | $(206464890,158422679)$ |
| $(4,1)$ | $(106286597,4261383)$ | $(76885224,39590342)$ |

On marker zero the larger endpoint is b for every $n$; on p marker one
it is b for $n\ge3$; on suspended marker one it is b for $n\ge1$.
These orders follow from the endpoint ratios in [CLIP, Section 6].
On every unmodified geometric range, increasing $n$ multiplies the
candidate mass by $c$, the lower endpoint by $2/9$, and the upper
endpoint by $6/25$. By (17.3), a valid comparison propagates to all larger
$n$. Use the $(0,0)$ base for both zero branches except their modified
$n=3$, the three separate small one-branch checks, and the $(4,1)$
base for the remaining one branches. The table therefore proves every
finite coordinate inequality and nonnegativity. The standalone suspended
beta lies in its box since $a<v<b$; infinity lies in its zero endpoint box.

The modification exchanges mass within one return depth. Consequently
$$
Q(T_p(0))=1,\qquad
Q(T_p(j))=T_1c^{j-1}\ (j\ge1),\qquad
T_1=1-u-q=\frac{1267861698065}{5432410480941}<\frac4{15},
                                                               \tag{17.6}
$$
and $W(T_\beta(j))=vQ(T_p(j))$. Equations (17.3) and (17.6) prove every
original tail bound. They prove vanishing mass at infinity without
conditioning on completion. For the level-five tail endpoint box, every
constituent finite coordinate has the same endpoint order; sum the full
coordinate inequalities, including infinity. Thus all projected
normalization, box, emission and retained tail constraints hold. $\square$

### 17.3. All supported losses and the exact full residual vector

**Proposition 17.2.** The four complete endpoint losses of (17.4) equal their
respective radii, as do the level-four endpoint losses. Uniformly for
every $r\in[3/8,5/13]$,
$$
\operatorname{TV}(Q,P_{p,r})<\frac3{100},\qquad
\operatorname{TV}(W,P_{\beta,r})<\frac1{50}.                 \tag{17.7}
$$
In particular all six selected projected losses are nonpositive, with
strict nonendpoint slack greater than
$$
\sigma_p:=\rho_p-\frac3{100}=\frac{866183}{45562500},\qquad
\sigma_\beta:=\rho_\beta-\frac1{50}=\frac{52}{3375}.          \tag{17.8}
$$
The statement retains every actually supported nonendpoint, without
assuming $\mu(3)>0$.

**Proof.** Inside the complete endpoint boxes, the endpoint TV identities
are the signed event differences of [CLIP, Theorem 6.2; PAIRED, (11.30)].
Equation (17.5) makes all four distances equal their radii. Grouping at level
four loses no endpoint TV because every grouped tail atom has the same
endpoint sign and both positive-difference events are retained.

For a direct complete-tail proof of (17.7), put $l=3/8$, $h=5/13$,
$F_p=\{w_{n,i}:n<4\}$, and $F_\beta=\{\beta\}\cup\alpha F_p$.
Every native coordinate in these finite sets is monotone on $[l,h]$.
The derivative signs, after positive factors are removed, are
$(n+1)-(2n+1)r$ and $n-(2n+2)r$ at p, and
$(n+2)-(2n+2)r$ and $(n+1)-(2n+3)r$ at suspension.
For $n<4$ none changes sign in the interval's interior. The standalone
beta decreases. The native tails
$H_p(r)=t_r^4$, $H_\beta(r)=rt_r^4$ increase there. Therefore, for
$D_p=Q,D_\beta=W$, the complete TV is bounded by
$$
B_s=\frac12\sum_{\omega\in F_s}
 \max\{|D_s(\omega)-P_{s,l}(\omega)|,
        |D_s(\omega)-P_{s,h}(\omega)|\}
 +\frac12\{D_s(T_s(4))+H_s(h)\}.                            \tag{17.9}
$$
The last summand bounds the entire infinite complement, not just its
partition mass difference. Exact substitution gives
$$
B_p=\frac{1226181607265976508493031867683}
 {41458271175237999801139200000000}<\frac3{100},
$$
$$
B_\beta=\frac{56912033286509571087020539}
 {2921887678112582400000000000}<\frac1{50}.
$$
Projection contracts TV configurationwise, proving (17.8) and the projected
claims. $\square$

Let $b_E=Q(\beta E)-UW(E)$ and
$a_F=W(\alpha F)-vQ(F)$, with the original positive denominators
$U\ge3/5$, $v\ge1/3$ retained in the normalized residuals.

**Proposition 17.3.** As signed measures on the entire suspended carrier,
$$
U\{\mathcal R_B(Q)-W\}
=d_0(\delta_\beta-\delta_{\alpha w_{0,1}})
 +\varepsilon(\delta_{\alpha w_{2,0}}-\delta_{\alpha w_{2,1}})
 -c\varepsilon(\delta_{\alpha w_{3,0}}-\delta_{\alpha w_{3,1}}),
                                                               \tag{17.10}
$$
whereas $\mathcal R_A(W)=Q$ on the entire p carrier. Thus every A
residual and both level-four tail residuals are zero. The ten B output
residuals, ordered as beta, then $\alpha w_{n,i}$ for $n<4$, then tail,
are exactly
$$
(d_0,0,-d_0,0,0,\varepsilon,-\varepsilon,
  -c\varepsilon,c\varepsilon,0).                            \tag{17.11}
$$
For all seven basis inputs their B moment matrix is the outer product
$$
\left(1,u,u^2,C,uC,q,\frac{1944}{390625}\right)^{\!T}
\left(d_0,0,-d_0,0,0,\varepsilon,-\varepsilon,
  -c\varepsilon,c\varepsilon,0\right),                     \tag{17.12}
$$
and their A moment matrix is zero.

**Proof.** The beta residual is $q-U(1-v)=d_0$. Every other finite
residual is $Q(w_{n+1,i})-cQ(w_{n,i})$. Before the modification, the
only nonzero such residual is $s-cq=-d_0$ at $(n,i)=(0,1)$.
The depth-three exchange creates the four other terms in (17.10) and no
others. Equation (17.6) gives
$Q(T_p(5))-cQ(T_p(4))=0$. Infinity has zero residual. Definition (17.4)
gives the full A equation directly. Evaluating the prescribed input
basis gives (17.12), so no multiplier or output coordinate is omitted.
In particular,
$$
\operatorname{TV}(\mathcal R_B(Q),W)
=\frac{d_0+(1+c)\varepsilon}{U}
=\frac{176521370877569582321}{430670302521750000000000}>0.
                                                               \tag{17.13}
$$
The unique coupling of the Dirac marginals therefore fails the constant
B-beta residual test. $\square$

### 17.4. A coefficient-specific falsifier and a margin ceiling

For an arbitrary tuple in the original allowed coefficient domain, set
$\delta=\delta_B+\delta_A$, $L_p=\lambda_{p,r_\star}$,
$L_\beta=\lambda_{\beta,r_\star}$. Evaluate all multipliers at the single
law Q of (17.4), and define the rational linear functional
$$
\begin{aligned}
\Phi(\chi)={}&d_0(\chi_{\{\beta\}}(Q)-\chi_{\{\alpha w_{0,1}\}}(Q))\\
&+\varepsilon[\chi_{\{\alpha w_{2,0}\}}(Q)
 -\chi_{\{\alpha w_{2,1}\}}(Q)
 -c\chi_{\{\alpha w_{3,0}\}}(Q)
 +c\chi_{\{\alpha w_{3,1}\}}(Q)].
\end{aligned}                                                   \tag{17.14}
$$
For $s=p,\beta$, let
$\tau_s(r)=\rho_s-\operatorname{TV}(\pi_4D_s,\pi_4P_{s,r})$.
These are exact finite absolute-value expressions, with their complete
tail cell, and are rational at the symbolic supported rational
$r=r_\star$.

**Theorem 17.4.** Any tuple satisfying both original global inequalities
must satisfy
$$
\delta\le\Phi(\chi)-L_p\tau_p(r_\star)
                         -L_\beta\tau_\beta(r_\star).       \tag{17.15}
$$
Consequently a tuple violating (17.15) has an explicit violating point in
one of its original outer products. In particular, no positive tuple
can have
$$
\Phi(\chi)\le\sigma_pL_p+\sigma_\beta L_\beta.               \tag{17.16}
$$
This is a constraint on all seven input coefficients of the six named
B output multipliers. It imposes no condition on possible observer
shapes or full-law marginals.

**Proof.** Evaluate $G_B$ at $(\pi_5Q,\pi_5W)$ and $G_A$ at its
reverse. Proposition 17.1 proves these points belong to the full original
domains, including their boundary face $Q(w_{3,1})=P_{p,b}(w_{3,1})$.
The potentials cancel exactly. Both centered events vanish. Proposition
17.3 evaluates every residual term, including tails, to (17.14). Proposition
17.2 makes all four endpoint loss terms zero. Hence the sum of the two
evaluations is exactly the right side of (17.15). If that sum is less than
$\delta_B+\delta_A$, at least one of the two required bounds fails at
the displayed point. Finally $\tau_s(r_\star)>\sigma_s>0$, proving (17.16).
This argument evaluates absolute values themselves; it assumes no
sampled or omitted TV sign regions. $\square$

**Corollary 17.5.** Write
$$
\Delta(r)=r^3(1-r)^5-\frac{1944}{390625},\qquad D(r)=\Delta(r)/2.
$$
Every positive globally valid tuple in the original coefficient norm
satisfies $L_p>0$ and
$$
0<\delta\le
\frac{\varepsilon D(r_\star)}{D(r_\star)+\varepsilon+\sigma_p}
\le\frac{970653033099278294049}{5888989627122173078237500000}
<\frac1{6000000}.                                          \tag{17.17}
$$
If $N_B$ is the sum of the absolute values of all original B multiplier
coefficients, then also
$$
\varepsilon N_B\ge\delta+\sigma_pL_p+\sigma_\beta L_\beta,
\qquad
0<L_p<\frac{\varepsilon}{\varepsilon+\sigma_p}.              \tag{17.18}
$$
All six risk weights, both potential expansions, all A and B multiplier
expansions, and both event coefficients remain charged in these bounds.

**Proof.** Use the fair native endpoint edge measures
$$
\Gamma_B^e=\tfrac12\delta_{(P_{p,a},P_{\beta,a})}
           +\tfrac12\delta_{(P_{p,b},P_{\beta,b})},
\qquad \Gamma_A^e=\text{their reversed pairs}.
$$
They have common unweighted marginals, and (17.1) verifies both entire
residual equations. Their full geometric tails put every projected node
in the original domains. Their event means are C,H. On the complete
level-four partition, the only native p target coordinate outside its
endpoint interval for $r\in[3/8,5/13]$ is $w_{3,1}$, with excess
$\Delta(r)>0$. To verify this, the marker-zero coordinates and grouped
tail increase on $[a,b]$; the marker-one coordinates for $n=0,1,2$
decrease there. For $n=3$, the derivative sign is $3-8r$, and its
value at $5/13$ exceeds its larger endpoint value. Every suspended
coordinate, including its grouped tail, lies between its endpoints:
standalone beta and its $n=0$ one-branch decrease, and its other
retained coordinates increase.

The coordinate triangle identity consequently makes the integrated
p nonendpoint excess exactly $D(r)$, the suspended nonendpoint excess
zero, and all four endpoint excesses zero. Integrating the two proposed
bounds against this same native pair gives
$$
\delta\le L_pD(r_\star).                                   \tag{17.19}
$$
This is the native endpoint-tag comparison of (12.4)--(12.5), with
its projected-tail and sign premises proved above. It tests the proposed
certificate without restricting the original unknown pair.

Every entry of the input vector in (17.12) belongs to $[0,1]$.
By (17.3) and (17.11), every absolute raw residual is at most
$\varepsilon$, so $\Phi(\chi)\le\varepsilon N_B$.
Equation (17.15) and (17.8) prove the first inequality in (17.18).
The original full coefficient budget implies
$N_B+L_p+L_\beta\le1$; all omitted budget terms are nonnegative
absolute values. Therefore
$$
\delta\le\varepsilon-(\varepsilon+\sigma_p)L_p
                     -(\varepsilon+\sigma_\beta)L_\beta.
$$
For $\delta>0$, (17.19) forces $L_p>0$ and
$L_p\ge\delta/D(r_\star)$. Substitution, and $L_\beta\ge0$, prove
the first bound of (17.17) and the second of (17.18). No coefficient has been
removed or renormalized. Finally,
$$
0<\Delta(r_\star)\le\Delta(3/8)
=\frac{344076471}{6553600000000},
$$
because the derivative of $r^3(1-r)^5$ is nonpositive on this interval.
The function $x\mapsto\varepsilon x/(x+\varepsilon+\sigma_p)$
increases for $x>0$. Exact substitution proves both remaining rational
comparisons in (17.17). $\square$

### 17.5. Applicability limits and the unpaid relation

The directional Dirac measures of (17.4) are normalized nonnegative measures
with common full marginals, both exact centered events, all selected
nonpositive losses, and every A input-output residual moment zero. Their
B moment matrix is exactly (17.12), not zero. They are thus neither a
projected null nor a common full-law zero witness. The existing
Chapter 15 object likewise fails a B coordinate, with its different
normalized defect $-97339/246148875$. Its event-output exclusion is
reused only within its published scope. Equations (17.10)--(17.18) give an
explicit sparse full-vector evaluation and coefficient bound for a
different law pair; no event-only exclusion is promoted to full-vector
infeasibility.

The exact fixed-template question remains whether some rational tuple in
the original spaces, with all six required weight signs and full norm
bound, satisfies both inequalities on the entirety of
$Z_p\times Z_\beta$ and its reversal. Equivalently for an exact null
assignment, the two normalized projected edge measures must match every
potential moment, annihilate all seven-input-times-output residual
moments in both directions, center both events, and have all six loss
integrals nonpositive. No such evaluated tuple or null is furnished by
(17.4). The strictly positive upper bound (17.17) does not prove that no
positive tuple exists, and failing (17.15) refutes only the specified tuple.

For the original unrestricted question the simultaneous relation still
unpaid is
$$
\mathcal R_B(Q)=\mathbb E[W\mid Q],\qquad
\mathcal R_A(W)=\mathbb E[Q\mid W],                         \tag{17.20}
$$
conditioned on the entire descriptors, with common unweighted full
marginals, every complete endpoint box, the mean constraints
$\int f=C,\int h=H$, and both supported-depth suprema of complete
configuration losses at most their radii. The two suprema need not have
maximizing depths. Finite projected moment agreement is weaker than
(17.20), even when actual representing measures are supplied. Neither
the event means nor (17.17) identifies the immediate-emission means or
forces the synchronized endpoint chord of [PAIRED, (12.3)].

The supplied identities and necessities remain jointly scoped to one
compatible pair:
$$
S=2(J_p+J_\beta)+M_A+M_B,\qquad
\mathcal J+\frac{540}{11}S\ge\frac\eta4,
$$
$$
\frac{61}{11}\mathcal J+
\frac{19}{11}\sqrt{\sqrt{M_B}+\sqrt{M_A}}\ge\frac\eta{400000}.
$$
They leave S and the mismatches free at zero excess. Return variation,
complete-law dispersion, suspended-to-p mismatch and paired-event
ranges are different quantities; none is multiplied by an independently
attained bound or eliminated here. Sections 16.2--16.4 already derive
the mismatch necessity from the joint own-law regeneration of
[PAIRED, Chapter 11] and the directed crossing-flow repair of [RETURN,
Section 9]; those arguments are not replaced by a new compactness or
rounding principle.

An original-domain realization would require both full residual equations
and a single finite same-update table, or the complete hypotheses of
[PAIRED, Theorems 11.4--11.8 or 13.2]. [PAID, Lemma 2.1.1] then puts its
private row after the original third write and latch; [PAID, Lemma 14.1]
supplies initialized paid-history rows and countable-prior domination.
Acquired kernel rows can contain zeros and ones. Arbitrary original
emissions can also be zero or one, with their kernels defined and their
possible noncompletion retained; clipping to regular emissions is the
separate comparison in [CLIP, Theorem 3.1], not a premise silently imposed
on the full problem. Rational samplers, all installed program and numeric
data, workspace, sampler states and persistent randomness must be charged
to COMPLETE. A mathematical law or finite atomic measure is not an
exact-real runtime port. Proposition 17.3 prevents invoking any of these
realization conclusions for (17.4).

The finite next exact assignment is to evaluate the original coefficient
system subject to the necessary tests (17.15), (17.17), and (17.18), retaining all
its domains and coefficients, or to give representing measures satisfying
its entire projected null system. These extra tests remove no valid
positive certificate and impose no observer restriction. A successful
positive tuple still requires a proof on every nonempty closed TV sign
region and every boundary; a representation-order non-hit proves nothing
about existence. An exact projected null would settle only this ansatz;
full-law extension, common full marginals, all supported losses and
original realization would still be required for a zero witness.
Exact finite common attainment, an unattained zero infimum, a positive
unrestricted gap, and fixed-resource optima remain distinct and unresolved.

### 17.6. Citations and mathematical correspondence

- **FULL:** Chapter 16, especially (16.17)--(16.22), supplies the exact
  full-residual coefficient spaces, all six nonnegative risk weights,
  the 155-entry norm and both universal inequalities. Sections 16.1--16.4
  supply the joint mismatch necessity with its original-source hypotheses.
- **PAIRED:** Sections 2--4 and Chapters 11--15 of this volume supply the
  complete-law domain, native recursions, endpoint geometry, joint
  regeneration, one-sided realization limits and event counterobject.
  Their conclusions retain their stated scopes.
- **CLIP:** [Risk-controlled emission moment feasibility](RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md),
  Sections 1--6. Proposition 17.2 uses its endpoint-box TV identity;
  (17.9) is the elementary complete-tail bound of (12.13), evaluated at
  the laws (17.4).
- **PAID:** [Effective paid-history certificates](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md),
  Definitions 1.1--2.1, Lemmas 2.1.1, 2.2, 14.1 and Corollary 2.3.
- **RETURN:** [Acquired-return p-emission variation](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md),
  Theorems 9.2--9.3. Their necessity is reused through Chapter 16;
  it is not a risk-only lower bound.
- **Endpoint-tag coefficient test:** The complete native laws (2.1),
  their compatible endpoint flows (12.5), and the coordinate triangle
  identity (5.7) give (17.19) by the full projected sign argument in
  Corollary 17.5. Conditional finite-feature tests, elimination of
  redundant terms and polynomial validation provide no evaluated
  separator or projected null without their own full hypotheses.

The complete-law formulation in [PAID, Chapters 16--17](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md)
uses the same normalized compact law spaces and two separately normalized
unweighted flows. Its second flow is written in the reversed coordinate
order: $\gamma=\Gamma_B$ and $\zeta=\mathrm{swap}_*\Gamma_A$,
where $\mathrm{swap}(W,Q)=(Q,W)$. Its raw residual equations
are equivalent to (16.2): multiply input tests by $U$ or $v$ in one
direction, and by $1/U$ or $1/v$ in the other. All these multipliers are
bounded continuous because $U\ge3/5$ and $v\ge1/3$. The complete
atom equations include infinity and extend to complete events as in
Section 16.1. The supremum over the closure of the supported parameters
has the same value as the supported-depth supremum: the complete-target
TV estimates of [CLIP, Proposition 5.3] give continuity in the parameter,
uniformly in the descriptor. No maximizing supported depth is required.
Thus PAID's compactness, finite regeneration, endpoint boxes and zero-value
alternatives are covered by Chapters 11--13 with these exact conventions.
They are reused mathematical supplies, not further compactness results.
Finite abstract realization still requires the represented exact-sampler
conditions of Theorem 11.8 for an effective observer.

[PAID, Theorems 18.1--18.2](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md)
supply conditional existence of finite strict whole-product certificates
and rational finite-coordinate verification when the compact value is
positive. Their tests, polynomial degrees, partitions and supported target
menus are not fixed to Section 16.5. Their exact projection polytopes also
differ from its endpoint-box outer domains, and their loss weights have a
joint sum-one normalization rather than this full 155-coefficient norm.
Consequently they supply neither coefficients for (16.24) nor a null for
that fixed system. Proposition 16.4 reuses cancellation of common marginal
potentials and annihilation of conditional residuals; (17.10)--(17.19)
retain the specific sparse full-vector evaluation and coefficient ceiling.
A pointwise falsifier of one tuple is not a universal certificate.

[Suspended-emission heterogeneity, Section 8](RECURSIVE_RELATIONAL_OBSERVATION_SUSPENDED_EMISSION_HETEROGENEITY.md)
supplies a joint necessary modulus for original excess and suspended
emission oscillation on the reachable held-record fibre, conditional on
its common-row, clipping, endpoint and full-record suppliers. It uses one
dependent acquired path and a convex tangent comparison; it assumes no
independence of path coordinates or private-kernel mixing. That oscillation
remains free and is distinct from both residual mismatch energies here.
Its necessity evaluates neither (16.24) nor the unrestricted infimum and
is not applied as an observer theorem to the incompatible laws (17.4).

Positive realization by invariant pointed polyhedral cones concerns a
specified quasi-realization and compatible word maps [Monras--Winter,
Definition 5 and Theorem 6, arXiv:1412.3634v1]. Conditional convex-order
coupling concerns integrable finite-dimensional vectors or kernels
[Leskela--Vihola, Theorems 1.2--1.3, arXiv:1404.0999v3]. Neither theorem
provides the missing two full-descriptor equations (17.20) for these laws.
Approximate policy refinement for general Markov decision processes
[Haesaert--Soudjani--Abate, arXiv:1605.09557] and optimal transition
couplings of prescribed stationary finite Markov chains
[O'Connor--McGoff--Nobel, arXiv:2006.07998] address different constraints
and losses; no complete stopped-law or initialization correspondence is
asserted. Legal adaptive tests of suspension automata
[van den Bos--Vaandrager, Definitions 7--11, arXiv:1907.11034v2] grant no
extra source observation here. Pointwise martingale-duality failures
[Beiglbock--Nutz--Touzi, Section 8, arXiv:1507.00671v3] preclude borrowing
unqualified dual attainment. Strict polynomial positivity under an
Archimedean quadratic module [Helton--Putinar, Theorem 3.9,
arXiv:math/0612103v1] supplies no separator coefficients or fixed order.
None of these external results is a premise of Propositions 17.1--17.3 or
Theorem 17.4; Corollary 17.5 uses only the displayed native-law comparison.

The native actual-prefix marking and rigidity statements require their
prescribed literal source, complete nominal carrier, exact traces and
truthful cache. The k-bonacci donor, internal-zero and own-path statements
require their literal executor, actual calendar and phase-label
hypotheses. Their variables and costs have not been identified with the
two stochastic complete-law flows. The Robin signed-band decomposition
likewise concerns arithmetic zeros and its fixed exponent, not these
probability residuals. These are qualified contextual analogies only.
The assertions here are ordinary mathematical statements. Universal
formal applications, worldwide novelty, exact common attainment, the
unrestricted zero-versus-positive alternative and fixed-resource optima
remain unestablished.

## 追加锚（本行以下为增补区）

## 18. Finite-p-support eventual-tail rigidity and its repair consumers

### 18.1 Standing data and the new restriction

**Standing assumptions 18.1.** Retain the source, the once-sampled finite or countable prior, both endpoint masses, every supported target, both seeds, all paid histories, source-independent initialization, the complete raw carriers (including their infinite noncompletion outcomes), the original records, completion and matching Stop, and the same-update rules of Definition 11.2. Let $(\Gamma_B,\Gamma_A)\in\mathfrak C$ have the two full-descriptor residual equations (11.7) and the same unweighted marginals (11.6). Assume that the endpoint coordinate boxes (11.29) hold almost surely for both marginals. The only extra hypothesis in this section is that $\nu_p$ has finite support and that its averaged marker-one masses

$$
 d_n=\int Q(w_{n,1})\,d\nu_p(Q)
$$

satisfy, for some integer $N\ge0$,

$$
 d_{n+2}-\frac{104}{225}d_{n+1}+\frac4{75}d_n=0
 \qquad(n\ge N).
 \tag{18.1}
$$

No atomicity of $\nu_\beta$ is assumed in this standing hypothesis. In particular, (18.1) is a condition on one averaged complete-word sequence; it does not assume native individual laws, native acquired residuals, synchronized four-moment barycentres, a common return rate, reversibility, zero return variation, or a fixed label count.

Put

$$
 z_a=\frac29,\qquad z_b=\frac6{25},\qquad
 c_a=(1-a)^2=\frac49,\qquad c_b=(1-b)^2=\frac9{25}.
$$

Thus the two characteristic roots in (18.1) are $z_a,z_b$, and

$$
 P_{p,a}(w_{n,1})=c_a z_a^n,\qquad
 P_{p,b}(w_{n,1})=c_b z_b^n.
 \tag{18.2}
$$

The source-relative gap addressed here is the passage from (18.1), a single averaged tail constraint, to the full descriptor and flow classification below. That passage is absent from the supplied native-mixture and synchronized-fibre results.

### 18.2 A finite positive boundary lemma

**Lemma 18.1 (boundary recurrence lemma).** Let a finite regular stationary table have positive rows $\pi,\tau$, kernels $B,A$, emissions $u_i,v_j\in[a,b]$, and own complete laws $Q_i,W_j$ satisfying the two full recursions in (11.19). Suppose every $Q_i$ and $W_j$ lies in its corresponding endpoint coordinate box (11.29). Set

$$
 L=\operatorname{diag}(1-u)B\operatorname{diag}(v)A,
 \qquad g=\operatorname{diag}(1-u)B(1-v),
$$

so that

$$
 Q_i(w_{n,1})=(L^ng)_i,
 \qquad
 d_n=\pi L^n g.
 \tag{18.3}
$$

If $d_n$ obeys (18.1) eventually, then the positive labels split into two unions of closed communicating classes, indexed by $r\in\{a,b\}$, such that

$$
 u_i=v_j=r
$$

on every p or suspended label in the $r$-union, and no positive $B$- or $A$-edge joins the two unions. Consequently

$$
 Q_i=P_{p,r},\qquad W_j=P_{\beta,r}
$$

on the corresponding union.

**Proof.** Put $C=BA$. The two unweighted balances give $\pi C=\pi$. A finite stochastic matrix with a strictly positive stationary row has only closed irreducible classes on its support. Indeed, for a terminal communicating class, stationarity makes its total incoming flow from outside zero. Positivity of $\pi$ then forbids every incoming edge. Every vertex of the finite component graph has a path to a terminal class, so there can be no nonterminal class. Thus $C$ is block diagonal after a permutation.

For a p-class $X_0$, let $Y_0$ consist of its positive $B$ successors. If $B_{ij}>0$ with $i\in X_0$, then every $k$ with $A_{jk}>0$ has $C_{ik}>0$, hence belongs to $X_0$. Distinct p-classes cannot share such a $j$, since its stochastic $A$ row would have to be supported in both. Every suspended label has an incoming $B$ edge because $\tau=\pi B$ is positive. Consequently these $(X_0,Y_0)$ partition both phases into closed bipartite components. Positivity of $1-u_i$ and $v_j$ makes the support of $L$ exactly the support of $C$, so its p-blocks are irreducible, with no restriction on their periods.

The marker-one endpoint ratio is

$$
 \frac{c_bz_b^n}{c_az_a^n}
 =\frac{81}{100}\left(\frac{27}{25}\right)^n.
$$

It exceeds one at $n=3$ and increases thereafter. Therefore the full endpoint boxes imply

$$
 c_a z_a^n\mathbf1\le L^ng\le c_b z_b^n\mathbf1
 \qquad(n\ge3).
 \tag{18.4}
$$

Row stochasticity and $u_i,v_j\in[a,b]$ also give the finite-coordinate bound

$$
 c_b\le g_i=(1-u_i)\sum_jB_{ij}(1-v_j)\le c_a.
 \tag{18.5}
$$

Fix one component and restrict $L,g$ to $X_0$. The finite irreducible Perron--Frobenius theorem supplies a positive left vector $\ell$ with $\ell^TL=\rho\ell^T$, where $\rho>0$ is this block's spectral radius. Put $S=\ell^T\mathbf1>0$ and $H_0=\ell^Tg>0$. Multiplying (18.4) by $\ell^T$ gives

$$
 c_a z_a^n S\le\rho^n H_0\le c_b z_b^n S
 \qquad(n\ge3).
 \tag{18.6}
$$

Taking scalar $n$th roots shows $z_a\le\rho\le z_b$. At either boundary, (18.5) and one side of (18.6) saturate exactly:

$$
 \begin{aligned}
 \rho=z_a&\ \Longrightarrow\ c_aS\le H_0\le c_aS
                    \ \Longrightarrow\ g=c_a\mathbf1,\\
 \rho=z_b&\ \Longrightarrow\ c_bS\ge H_0\ge c_bS
                    \ \Longrightarrow\ g=c_b\mathbf1.
 \end{aligned}
 \tag{18.7}
$$

The final implications use strict positivity of every $\ell_i$. Each factor in the product defining $g_i$ in (18.5) lies in $[1-b,1-a]$. Its maximum $(1-a)^2$ is attained only when $u_i=a$ and the $B_i$-average of $1-v$ equals $1-a$; the latter equality forces $v_j=a$ on every positive $B_{ij}$. Its minimum $(1-b)^2$ similarly forces $u_i=b$ and $v_j=b$ on every such edge. Every $j\in Y_0$ has such an incoming edge. Hence

$$
 \rho=z_r\ \Longrightarrow\quad
 u_i=v_j=r\quad(i\in X_0,\ j\in Y_0),
 \qquad r\in\{a,b\}.
 \tag{18.8}
$$

This boundary argument uses neither convergence of normalized matrix powers nor visibility of peripheral eigenmodes.

On a component satisfying (18.8), the constant assignment of the native endpoint pair solves both full recursions (11.19). For any two normalized solution pairs, their maximal complete-law TV distances $x,y$ over the two finite label sets obey

$$
 x\le(1-r)y,\qquad y\le r x.
$$

Thus $x=y=0$, since $r(1-r)<1$. Every own law on this component is therefore $P_{p,r}$ or $P_{\beta,r}$, including every early word and the infinite coordinate. The infinite outcomes stay in the carriers; their zero mass also follows from the regular survival bound. Writing $m_{X_0}=\sum_{i\in X_0}\pi_i$, this component contributes exactly $m_{X_0}c_rz_r^n$ to $d_n$ for every $n\ge0$. This also follows directly from $L=z_rC$ and $g=c_r\mathbf1$ on that component.

It remains to prove that every component has a boundary radius. For each component choose a positive right Perron vector $h$ and positive constants $k_-,k_+$ such that $k_-h\le g\le k_+h$. Nonnegativity of $L$ then gives

$$
 k_-(\pi_{X_0}h)\rho^n
 \le\pi_{X_0}L^ng
 \le k_+(\pi_{X_0}h)\rho^n
 \qquad(n\ge0).
 \tag{18.9}
$$

Here $\pi_{X_0}$ is the original positive row restricted to the component, without renormalization. Thus the $n$th-root growth of the positive output of any nonempty collection of components is the largest radius in that collection. This follows by summing the upper bounds and keeping a largest-radius lower bound in (18.9), and holds for periodic blocks as well.

Every scalar sequence satisfying (18.1) is $A_0z_a^n+B_0z_b^n$ for $n\ge N$: solve for the two coefficients at $N,N+1$, then use the recurrence forward. A strictly positive such sequence has positive leading nonzero coefficient, so its $n$th-root growth is either $z_a$ or $z_b$. Applying this to $d_n$ identifies its largest component radius as one of these two values. If the largest radius is $z_a$, (18.6) makes every radius $z_a$, and (18.8) classifies every component.

If the largest radius is $z_b$, first apply (18.8) and the full-law uniqueness argument to all components with that radius. Their total output is $m_bc_bz_b^n$ for every $n$, where $m_b$ is their total p mass. Only now remove these components. Their output itself satisfies (18.1), so the remaining sum still satisfies the eventual recurrence. If this sum is nonempty, it is strictly positive by (18.9), and its largest radius is strictly below $z_b$. Its $n$th-root growth must therefore be $z_a$. Equation (18.6) then makes every remaining radius $z_a$, and (18.8) classifies them. The empty remainder needs no further argument. This accounts for every component without an inference about unobserved eigenmodes or cancellation at smaller poles. Closedness proves the absence of cross-edges between the two endpoint unions. $\square$

The boundary lemma is deliberately finite and exact. It does not claim a stability estimate for approximate recurrences, and it does not extend the conclusion to a nonatomic $\nu_p$.

### 18.3 Eventual averaged-tail rigidity

**Theorem 18.2 (finite-p-support eventual-tail rigidity).** Under Standing assumptions 18.1, there is $\theta\in[0,1]$ such that

$$
 \nu_p=(1-\theta)\delta_{P_{p,a}}+\theta\delta_{P_{p,b}},
 \qquad
 \nu_\beta=(1-\theta)\delta_{P_{\beta,a}}+\theta\delta_{P_{\beta,b}},
 \tag{18.10}
$$

and

$$
 \Gamma_B=(1-\theta)\delta_{(P_{p,a},P_{\beta,a})}
 +\theta\delta_{(P_{p,b},P_{\beta,b})},
$$

$$
 \Gamma_A=(1-\theta)\delta_{(P_{\beta,a},P_{p,a})}
 +\theta\delta_{(P_{\beta,b},P_{p,b})}.
 \tag{18.11}
$$

The eventual recurrence is an additional hypothesis. It is not inferred from the unrestricted endpoint face, and it constrains only the averaged marker-one word sequence sufficiently far into the tail.

**Proof.** Let $G\subset\mathcal K_\beta$ be the full suspended endpoint box. It is closed, hence Borel: it is a countable intersection of closed coordinate intervals, and atom evaluation is TV-continuous. It has full original $\nu_\beta$ measure by hypothesis. Apply Theorem 13.2 with the given finite p marginal, this $G$, and $q=0$. The resulting finite regular table has exactly the original p own-law marginal $\nu_p$, all its suspended own laws lie in $G$, and both its full recursions and unweighted balances hold. Each of its p laws lies in the p endpoint box because its positive-mass marginal is unchanged. Its averaged marker-one sequence is therefore the original $d_n$ and obeys (18.1).

Lemma 18.1 classifies this finite table. Since Theorem 13.2 preserves the entire p marginal, it follows that the original marginal is

$$
 \nu_p=(1-\theta)\delta_{P_{p,a}}+\theta\delta_{P_{p,b}}
$$

for some $\theta\in[0,1]$. No preservation of the original suspended marginal or either original flow is inferred from that realization; those objects are now recovered from the original equations (11.8).

Write $m_a=1-\theta$ and $m_b=\theta$. For each $r\in\{a,b\}$ with $m_r>0$, disintegrate the original $\Gamma_B$ over $Q=P_{p,r}$. Its first residual equation gives the equality of complete measures

$$
 \int W\,\Gamma_B(dW\mid P_{p,r})
 =\mathcal R_B(P_{p,r})=P_{\beta,r}.
$$

Every coordinate $W(\eta)$ lies almost surely between $P_{\beta,a}(\eta)$ and $P_{\beta,b}(\eta)$: this follows from the original second marginal and its full-measure box. At each $\eta$, the barycentre value $P_{\beta,r}(\eta)$ is an endpoint of this interval. Subtracting the lower endpoint, or subtracting from the upper endpoint, gives a nonnegative random variable of mean zero. Thus $W(\eta)=P_{\beta,r}(\eta)$ conditionally almost surely. The carrier is countable, including infinity, so these equalities hold simultaneously and force

$$
 \Gamma_B(dW\mid P_{p,r})=\delta_{P_{\beta,r}}.
$$

This proves the first flow identity in (18.11) for the original pair. Its second marginal, equal to the first marginal of the original $\Gamma_A$ by (11.6), is precisely the suspended marginal in (18.10).

For each such present $r$, the second original residual equation gives

$$
 \int Q\,\Gamma_A(dQ\mid P_{\beta,r})
 =\mathcal R_A(P_{\beta,r})=P_{p,r}.
$$

Its conditional p support is contained in $\{P_{p,a},P_{p,b}\}$. Testing the alpha coordinate, whose values at these two laws are the distinct numbers $a,b$, forces the conditional mass to be entirely at $P_{p,r}$. This proves the second flow identity in (18.11). Null endpoint fibres are omitted throughout, so the argument includes $\theta=0$ and $\theta=1$. No atomicity assumption was made on the original suspended marginal.

The resulting full classification gives

$$
 d_n=(1-\theta)c_a z_a^n+\theta c_b z_b^n
 \qquad(n\ge0).
$$

The coefficients are already uniquely determined by any two consecutive late values: the determinant of the columns $c_az_a^n,c_bz_b^n$ at $n,n+1$ is $c_ac_bz_a^nz_b^n(z_b-z_a)\ne0$. Early and non-marker-one coordinates follow from the full-law classification, without running the assumed recurrence backward. $\square$

### 18.4 Exact consumers

**Corollary 18.3 (tail-preserving PAIRED15 repair obstruction).** In the PAIRED15 construction, suppose a proposed repair has finite p support, satisfies the full compatibility equations and endpoint boxes, and preserves the averaged marker-one coordinates for all sufficiently large $n$. Write

$$
 s_b=\frac12+t,\qquad s_a=\frac12-t,\qquad
 t=\frac{78975}{2857232}.
$$

Then (18.1) holds with

$$
 d_n=s_a c_a z_a^n+s_b c_b z_b^n,
$$

so Theorem 18.2 forces $\theta=s_b$. Consequently its event means must be

$$
 \int f\,d\nu_p=C-2t\rho_p,
 \qquad
 \int h\,d\nu_\beta=H-2t\rho_\beta,
 \tag{18.12}
$$

rather than the two midpoint values $C,H$. In particular, changing only finitely many mean word coordinates cannot repair PAIRED15 while its averaged marker-one coordinates are retained for all sufficiently large $n$.

The p endpoint target already gives the quantitative obstruction

$$
 \mathcal J\ge2t\rho_p
 =\frac{14514877}{5357310000}>\frac1{400},
 \tag{18.13}
$$

and the suspended midpoint displacement is

$$
 2t\rho_\beta=\frac{27963}{14286160}.
 \tag{18.14}
$$

**Proof.** Section 15.2 changes only $w_{0,0},w_{0,1},w_{1,1},w_{2,1}$ of its endpoint-mixture p law. Thus its marker-one sequence has the displayed coefficients for every $n\ge3$. Eventual preservation implies (18.1). Theorem 18.2 and the nonzero two-column determinant in its proof give $\theta=s_b$ from any two consecutive retained late values.

The supplied endpoint event masses are $P_{p,a}(E_p)=C+\rho_p$, $P_{p,b}(E_p)=C-\rho_p$ and $P_{\beta,a}(E_\beta)=H+\rho_\beta$, $P_{\beta,b}(E_\beta)=H-\rho_\beta$. Integrating them against the two classified marginals gives (18.12); $t,\rho_p,\rho_\beta>0$, so both original midpoint equations fail. In particular the p endpoint target $a$, which has positive installed mass, gives

$$
 \mathcal L_p(P_{p,a})-\rho_p
 =s_b\operatorname{TV}(P_{p,b},P_{p,a})-\rho_p
 =2t\rho_p.
$$

Using $\rho_p=1116529/22781250$ and $\rho_\beta=239/6750$ gives (18.13)--(18.14), with

$$
 2t\rho_p-\frac1{400}=\frac{560801}{2678655000}>0.
$$

Enlarging the p support to any other finite size, changing kernels, or changing the coupling cannot evade this conclusion while the same averaged late tail, full compatibility and full boxes are retained. Every successful repair in this class must alter the averaged marker-one sequence at arbitrarily large indices; cancelling only the displayed suspended-coordinate residual of Section 15.6 cannot suffice. $\square$

**Corollary 18.4 (all-supported losses on the rigid branch).** For any fixed finite or countable original prior with positive endpoint masses and at least one supported $k\ge3$, every pair satisfying Theorem 18.2 has

$$
 \mathcal J\ge\frac\eta4,
 \qquad
 \eta=\frac{14219478376}{318644812890625}.
 \tag{18.15}
$$

If both endpoint midpoint equations are imposed, then for every supported nonendpoint target $R=P_{p,r_k}$,

$$
 \mathcal L_p(R)\ge\rho_p+\frac\eta2.
 \tag{18.16}
$$

**Proof.** Put $\Delta=2\rho_p$ and $\delta=|\theta-1/2|$. The endpoint configuration losses of the p marginal are $\theta\Delta$ and $(1-\theta)\Delta$, so their maximum excess is $\Delta\delta$. For a supported nonendpoint $r_k$, the complete word $w_{3,1}$ and the endpoint coordinate triangle identity give the supplied bound of Corollary 12.3 and (12.10), with $\eta=g_*$ there,

$$
 \operatorname{TV}(P_{p,a},R)+\operatorname{TV}(P_{p,b},R)\ge\Delta+\eta,
$$

while the reverse triangle inequality gives

$$
 \left|\operatorname{TV}(P_{p,b},R)-\operatorname{TV}(P_{p,a},R)\right|\le\Delta.
$$

Therefore the mixture loss is at least

$$
 (1-\theta)\operatorname{TV}(P_{p,a},R)+\theta\operatorname{TV}(P_{p,b},R)
 \ge\rho_p+\frac\eta2-\Delta\delta.
$$

The joint excess is at least the maximum of $\Delta\delta$ and $\eta/2-\Delta\delta$, which is at least $\eta/4$. If both midpoint equations hold, the p endpoint event mean is $C$, so $\theta=1/2$ and (18.16) follows. TV is inside the configuration integral throughout. The constant $\eta$ and the endpoint triangle estimate are supplied results; their use here is enabled by the new eventual-tail classification.

For a represented regular table satisfying the theorem's hypotheses, the original-history correspondence of Section 11.4 and Proposition 13.3 in Section 13.2 transfers these supported-target obstructions to its full original configuration-risk suprema. Source-independent latch initialization and both unweighted balances keep the same phase rows at every positive acquired fourth-phase history. At any such history, configurationwise TV convexity compares its fixed-prior posterior target to the supported pure targets. Conversely, positive finite paid histories concentrate the same once-sampled $K$ posterior at each supported depth; the summable likelihood-ratio domination in [PAID, Lemma 14.1] covers countable priors. Complete-law TV continuity then gives the reverse supremum inequality, as in [CLIP, Proposition 2.3]. This retains both seeds, every paid rejection and partial parse, all held records, same-update generation, noncompletion, fourth completion and matching Stop. It supplies no preservation of (18.1) under arbitrary original-observer extraction, clipping or approximation. $\square$

### 18.5 Falsifier, literature boundary and original scope

**Falsifier for Theorem 18.2.** An exact compatible pair with finite $\nu_p$, full endpoint boxes, the two full residual equations and (18.1), but with positive mass on any nonendpoint descriptor, refutes the theorem. A finite regular stationary full-box table with the eventual recurrence and a nonendpoint component would refute Lemma 18.1. More locally, a nonnative closed irreducible component of radius $z_a$ or $z_b$ satisfying these box hypotheses would refute its boundary step.

**Assumption check for Theorem 18.2.** The boxes are essential: with one p and one suspended label, $A=B=(1)$, $u=1/3$ and $v=9/25$, one has

$$
 L=\frac6{25},\qquad g=\frac{32}{75},\qquad
 Q(w_{n,1})=\frac{32}{75}\left(\frac6{25}\right)^n.
$$

This sequence satisfies (18.1), but

$$
 Q(w_{3,1})-P_{p,b}(w_{3,1})=\frac{72}{78125}>0,
$$

so the full endpoint box fails. A return rate or an averaged recurrence without all coordinate boxes is therefore insufficient.

**Mathematical citations and source-relative delta.** The finite-matrix supplier in Lemma 18.1 is precisely the existence of positive left and right Perron vectors at the spectral radius of a finite irreducible nonnegative matrix, as stated in [Chi-Kwong Li and Hans Schneider, *Applications of Perron-Frobenius Theory to Population Dynamics*, arXiv:math/0109008v1, Theorem 2.1(a)](https://arxiv.org/html/math/0109008v1). It applies to each $L$ block because its support equals that of the corresponding closed irreducible $BA$ block. It requires no primitivity. Their Theorem 2.3 on convergence of normalized powers requires primitivity and is not invoked. The positive-vector comparison (18.9) and the elementary solution of the two-root scalar recurrence suffice here; no conclusion about visibility of peripheral modes or absence of smaller-pole cancellation is used.

The finite realization is the supplied Theorem 13.2. Its quadrature input is [Christian Bayer and Josef Teichmann, *The proof of Tchakaloff's Theorem*, arXiv:math/0502473v2, Corollary 2](https://arxiv.org/html/math/0502473v2): a positive measure concentrated on a specified measurable set, a measurable finite-dimensional map, and integrability of its norm give positive-weight nodes in that set matching all coordinates. Here the measure is the probability $\xi$ of (13.6), the full set includes the closed suspended box $G$, and the map consists of the bounded Borel coordinates in (13.6) with $q=0$. Their sum of indicator coordinates preserves total mass. This input and Theorem 13.2 preserve the entire p marginal, not the original opposite marginal or joint flows. The latter conclusion in Theorem 18.2 instead uses the original full-descriptor equations (11.8) and coordinate extremality on the countable complete carriers.

The source-relative addition is the implication from one eventual averaged marker-one recurrence and finite p support, together with both full residual equations, shared unweighted marginals and full endpoint boxes, to the complete matched endpoint pair and both original flows. Neither native individual laws nor native acquired residuals are premises. [NATIVE-MIXTURE, Theorem 5.1](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md) assumes the former; [NATIVE-ACQUIRED, Lemma 3.1](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_RESIDUAL_OBSTRUCTION.md) assumes the latter. Chapters 12 and 14 of this volume assume or measure four synchronized moments. [REV, Chapters 14--15](RECURSIVE_RELATIONAL_OBSERVATION_REVERSIBLE_COMMON_GENERATOR_CONSTRAINTS.md) treats a prescribed swap-plus-fixed-point periodic kernel class, whereas Lemma 18.1 allows arbitrary finite kernels and periods. [RETURN, Chapter 12](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md) regenerates prescribed joint return measures; it does not assert preservation of this exact recurrence under approximation.

**Comparison with the full-residual necessities.** Theorem 16.2 applies to arbitrary compatible Borel pairs, with positive endpoint masses and a supported nonendpoint, and bounds joint excess together with the two edge-mismatch energies. Corollary 16.3 gives a necessary mismatch floor at zero excess. Neither result restricts the eventual marker-one sequence or classifies its descriptors. On the pair forced by Theorem 18.2 both mismatch energies vanish, so these supplied necessities can be applied after the classification; they do not supply that classification. Proposition 16.4 gives a conditional separator from a solution of the fixed 155-coefficient system (16.18)--(16.22). No such solution or full-system infeasibility is supplied by Chapters 16--17, and no coefficient claim follows here.

Chapter 17 tests that fixed system on a different rational complete-law pair. Its full A residual vanishes but its full B residual is the nonzero six-cell measure (17.10). Its multiplier test and positive margin ceiling, (17.15)--(17.18), leave the fixed coefficient problem open. It also has a different late tail: in the notation of (17.2)--(17.4), $Q(w_{n,1})=s c^{n-1}$ for $n\ge4$, with $s>0$ and $z_a<c=467/2000<z_b$. Substitution into the left side of (18.1) gives $s c^{n-1}(c-z_a)(c-z_b)\ne0$ for $n\ge4$. Thus that object meets neither the compatibility nor the eventual-recurrence premise here. Corollary 18.3 concerns the tail of Chapter 15 specifically; it does not exclude every finite-coordinate repair of the Chapter 17 object.

**Comparison with prescribed actual triples.** [RETURN, Theorem 13.4](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RETURN_P_EMISSION_VARIATION.md) starts with both prescribed finite joint flows and their full-law atoms. In addition to the two edge marginals, a realizable actual triple must satisfy the incoming-pair equation $\mathbb E[Q'\mid Q,W]=\mathcal R_A(W)$. RETURN, Theorems 13.5--13.6, classify the actual triples and their motion in the specified SAME six-p-law/two-suspended-law fibre. RETURN, Theorems 14.4--14.5, then minimize returned suspended COMPLETE configurations and compute motion-budget images in that same fibre. These statements preserve the given flows and laws; they neither assume (18.1) nor derive endpoint laws from an averaged tail. Theorem 18.2 instead identifies the original two flows after its one-sided realization. It prescribes no arbitrary whole triple, returned-cut count or total COMPLETE bound. The incoming-pair criterion remains required for a separately prescribed triple; it is not supplied by generic marginal gluing.

**Comparison with return-survival dispersion.** [Return survival dispersion, Definitions 2.2--2.4 and Theorems 3.1 and 4.1](RECURSIVE_RELATIONAL_OBSERVATION_RETURN_SURVIVAL_DISPERSION.md) uses the same compatible full-law pair but its separate statistic is $D=\int|Z-\int Z\,d\Gamma_B|\,d\Gamma_B$, where $Z=(1-u(Q))v(W)$ on the unweighted B edge. Its stated objective fixes a positive prior on $\{1,2,3\}$; the endpoint-only version of Theorem 4.1 still leaves $D$ free. The response envelope and the signed balances of Proposition 3.3 give necessary conditions on that same descriptor path. They do not force (18.1) or imply Theorem 18.2. In particular, the two matched endpoint components have distinct weights $z_a,z_b$; when both occur their edge-weight dispersion is positive. No common return weight is assumed in the present theorem. The dispersion volume's Section 10 reuses the Chapter 15 event-output counterobject and its failed full B coordinate; it does not rule out every compatible finite-p-support repair retaining that object's eventual mean tail. That exclusion is the direct consumer (18.12)--(18.14).

The complete-law compactness, regeneration and attainment alternatives of [PAID, Chapters 16--17](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md) have the correspondence stated in Section 17.6. Its Theorems 18.1--18.2 provide conditional finite strict certificate existence and rational finite-coordinate verification when the compact value is positive. They supply neither that positivity nor the averaged-tail classification here. These results, like the full-flow necessities just compared, remain supplied ordinary mathematics with their original hypotheses.

The direct consumer is Corollary 18.3's exclusion of every finite-p-support full-compatible full-box repair retaining the PAIRED15 eventual mean tail, even after finite support enlargement or kernel changes. Corollary 18.4 consumes the same classification with the supplied complete-word loss bound (12.10); its loss constants are not additional new constants. These are source-relative ordinary deductions, with no global novelty or priority claim.

The [suspended-emission heterogeneity modulus, Theorem 8.3](RECURSIVE_RELATIONAL_OBSERVATION_SUSPENDED_EMISSION_HETEROGENEITY.md) is conditional on its declared suppliers and retains the separate oscillation statistic; it supplies neither this recurrence nor an unrestricted risk-only gap. The [acquired-kernel blind-direction source, Conventions 1.1--1.2 and Theorems 5.1, 6.3](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_KERNEL_BLIND_DIRECTIONS_AFTER_PAIRED_CALIBRATION.md) uses an observation contract omitting the p-to-suspended kernel and a family with interior emissions. Its finite-prefix aliases and risk difference do not settle the compact common face or imply the present classification.

The self-calibration here concerns exactly what the scalar tail determines. Its positive output determines the largest remaining growth rate; the full boxes then force a boundary component to its endpoint emissions and complete laws. Periodic invisible modes are permitted throughout. A one-sided realization transfers only its stated invariants, so the original conditional residual equations are used separately to identify both original flows.

The theorem supplies a restricted bridge only. It does not evaluate the unrestricted $j_c$, prove a zero-level pair or a vanishing family, give a risk-only gap outside the recurrent finite-p-support branch, establish a shape-uniform stability theorem for approximate recurrences, handle nonatomic $\nu_p$, or prove finite effective attainment. Finite atomicity and permitted finitely represented exact sampling remain separate requirements; an arbitrary real endpoint weight need not have a permitted exact sampler. No hard-resource preservation follows. Theorem 10.2 of [RETURN] retains its free $V_\pi$; its bound $\mathcal C\le5000V_\pi$ is not a risk-only unrestricted separation. PAIRED11/RETURN12 approximants need not preserve (18.1), so density of those approximants does not transfer (18.15) to the unrestricted compact domain. The full original quantifiers, complete histories, noncompletion, Stop, TV placement and same-update rules remain those of Sections 11 and 13. $\square$

## 追加锚（本行以下为增补区）
## 19. Equal native endpoint excision and generated opposite-phase slack

### 19.1 Standing data and native unit flows

Retain exactly the source, the once-sampled $K$, the fixed finite or countable installed prior, positive endpoint masses, every actually supported target, both seeds, all paid histories and rejections, source-independent initialization, the complete records, noncompletion outcomes, completion and matching Stop, and the same acquired update rules of Definition 11.2. Let $(\Gamma_B,\Gamma_A)\in\mathfrak C$ satisfy

$$
\mathcal J(\Gamma_B,\Gamma_A)=0.
\tag{19.1}
$$

Thus (11.6)--(11.8), the full endpoint boxes (11.29), the midpoint equations (11.30), and every supported complete-configuration loss budget in (11.9) hold on the same pair. No finite support, reversibility, native-mixture, common rate, or atomicity assumption is made here.

For $r\in\{a,b\}$ write the native laws as $P_{p,r},P_{\beta,r}$ and define the unit native flows

$$
N_r^B=\delta_{(P_{p,r},P_{\beta,r})},
\qquad
N_r^A=\delta_{(P_{\beta,r},P_{p,r})}.
\tag{19.2}
$$

Each pair $(N_r^B,N_r^A)$ is a compatible unit flow: the native complete recursions on the whole carriers, including the infinite cells, are the residual equations for these flows. Put

$$
 m_r^p=\nu_p(\{P_{p,r}\}),\qquad
 m_r^\beta=\nu_\beta(\{P_{\beta,r}\}).
\tag{19.3}
$$

The endpoint laws are distinct because their p alpha masses, and their suspended $v=1-W(\beta)$ masses, are $a$ and $b$.

### 19.2 Native fibres are equal and removable

**Theorem 19.1 (equal native endpoint excision).** Under the standing data above, for each $r\in\{a,b\}$,

$$
 m_r^p=m_r^\beta=:m_r,
\tag{19.4}
$$

and the directional flows contain the native unit flows with exactly these masses:

$$
\Gamma_B\ge m_aN_a^B+m_bN_b^B,
\qquad
\Gamma_A\ge m_aN_a^A+m_bN_b^A.
\tag{19.5}
$$

Set

$$
 t=\min(m_a,m_b),\qquad \theta=2t.
\tag{19.6}
$$

If the installed prior supports a nonendpoint depth $k\ge3$, then $\theta<1$. For $\theta<1$ define

$$
 \widehat\Gamma_B=\frac{\Gamma_B-tN_a^B-tN_b^B}{1-\theta},
 \qquad
 \widehat\Gamma_A=\frac{\Gamma_A-tN_a^A-tN_b^A}{1-\theta},
\tag{19.7}
$$

and let $\widehat\nu_p,\widehat\nu_\beta$ be their common unweighted phase marginals. Then $(\widehat\Gamma_B,\widehat\Gamma_A)\in\mathfrak C$, with the same full regular law spaces, endpoint boxes, midpoint equations, and all supported loss budgets. The remainder may be nonatomic and need not have a finite support.

For every normalized complete target $T$ (including a target with noncompletion mass), put

$$
 \mathcal L_s^N(T)=\frac12\bigl(\operatorname{TV}(P_{s,a},T)+\operatorname{TV}(P_{s,b},T)\bigr),
\tag{19.8}
$$

and

$$
 \widehat{\mathcal L}_s(T)=\int\operatorname{TV}(D,T)\,d\widehat\nu_s(D),
 \qquad
 \mathcal L_s(T)=\int\operatorname{TV}(D,T)\,d\nu_s(D).
$$

Then the exact marginal-linearity identity is

$$
 \widehat{\mathcal L}_s(T)
 =\frac{\mathcal L_s(T)-\theta\mathcal L_s^N(T)}{1-\theta}.
\tag{19.9}
$$

In particular $\mathcal L_s^N(T)\ge\rho_s$ by the endpoint triangle inequality, and hence every old budget $\mathcal L_s(T)\le\rho_s$ remains valid after excision. At the two endpoint targets the remainder losses remain exactly $\rho_s$. If $\theta>0$, then for every actually supported $k\ge3$,

$$
 \widehat{\mathcal L}_p(P_{p,r_k})
 \le \rho_p-\sigma,
 \qquad
 \sigma=\frac{\theta\eta}{2(1-\theta)}>0,
 \qquad
 \eta=\frac{14219478376}{318644812890625},
 \qquad
 \rho_p=\frac{1116529}{22781250}.
\tag{19.10}
$$

No strict suspended-phase inequality or strict worst-case p-risk conclusion is asserted: the endpoint targets remain saturated at $\rho_p$ and $\rho_\beta$.

**Proof.** First suppose $m_r^p>0$. The first full residual equation, with the Borel singleton test $\mathbf1_{\{P_{p,r}\}}$, says that the conditional barycentre of $W$ over $Q=P_{p,r}$ is

$$
\mathcal R_B(P_{p,r})=P_{\beta,r}.
\tag{19.11}
$$

Every conditional $W$ lies in the suspended endpoint box. For each complete atom, including $\infty_\beta$, $P_{\beta,r}(\eta)$ is an endpoint of the interval with endpoints $P_{\beta,a}(\eta),P_{\beta,b}(\eta)$. A random variable in that interval whose mean is this endpoint is equal to it almost surely. The complete carrier is countable, so intersecting these full-measure statements gives

$$
\Gamma_B(dW\mid P_{p,r})=\delta_{P_{\beta,r}}.
\tag{19.12}
$$

No conditioning on a null fibre has been used. Consequently $m_r^\beta\ge m_r^p$. If $m_r^\beta>0$, the second residual equation and the p endpoint box give, by the same singleton and countable-coordinate argument,

$$
\Gamma_A(dQ\mid P_{\beta,r})=\delta_{P_{p,r}},
\tag{19.13}
$$

so $m_r^p\ge m_r^\beta$. If $m_r^p=0$ while $m_r^\beta>0$, (19.13) is impossible; hence both masses vanish. This proves (19.4). The two inequalities also show incoming isolation: the native p-to-native suspended mass already equals the entire native suspended singleton mass, and conversely. Thus no nonnative mass enters either native singleton, proving the measure domination (19.5).

Each pair $(N_r^B,N_r^A)$ satisfies both residual equations, the two unweighted balances, the full boxes, and contributes its native endpoint event values. Subtract the nonnegative subflows in (19.7) before dividing. The residual equations are linear signed-measure identities after the bounded Borel extension of (11.7), so their difference is again zero; the common marginals subtract the same $t$ from both directions. Their total remaining mass is $1-2t$. All remaining descriptors stay in the compact law spaces, so normalization, emission bounds, complete tails, and the zero infinite-cell mass are retained. The midpoint values are retained because the supplied endpoint event identities are

$$
P_{p,a}(E_p)=C+\rho_p,\quad P_{p,b}(E_p)=C-\rho_p,
$$

$$
P_{\beta,a}(E_\beta)=H+\rho_\beta,\quad
P_{\beta,b}(E_\beta)=H-\rho_\beta;
$$

removing $t$ of both endpoints subtracts $2tC$ and $2tH$, respectively. This proves all structural assertions about the normalized pair.

The native part of any marginal contributes
$ t[\operatorname{TV}(P_{s,a},T)+\operatorname{TV}(P_{s,b},T)]=\theta\mathcal L_s^N(T)$. Splitting the configuration integral gives (19.9); TV has remained inside that integral. The reverse triangle inequality and
$\operatorname{TV}(P_{s,a},P_{s,b})=2\rho_s$ give
$\mathcal L_s^N(T)\ge\rho_s$. The separate endpoint minima supplied in Section 2 imply that a zero-level pair has $\mathcal L_s(P_{s,a})=\mathcal L_s(P_{s,b})=\rho_s$, and (19.9) gives the same equalities for the remainder.

For a supported $k\ge3$, Corollary 12.3 supplies

$$
\mathcal L_p^N(P_{p,r_k})\ge\rho_p+\frac\eta2.
\tag{19.14}
$$

Combining (19.9), (19.14), and the old p budget proves (19.10). The same descriptorwise identity applies to a posterior target, since it is a normalized complete law; the usual configurationwise TV convexity for posterior mixtures is unchanged. No posterior port, reset, new sampling of $K$, or completion conditioning has been introduced.

If $\theta=1$, then $m_a=m_b=1/2$ and (19.5) exhausts both probability flows. The pair is exactly the fair native endpoint pair (12.5), which is excluded by Corollary 12.3 when a supported $k\ge3$ exists. Hence $\theta<1$. When $\theta=0$, (19.7)--(19.9) are the identity. Unequal removal of the two native masses would not preserve either midpoint equation, so no unequal-removal zero theorem is claimed. $\square$

### 19.3 A conditional symmetric finite-attainment consumer

**Corollary 19.2 (strict generated slack implies symmetric finite attainment).** Assume the installed support is countably infinite. Suppose a zero-level compatible pair has finite suspended marginal with $N$ distinct atoms and $m_a,m_b>0$. Form the excised pair of Theorem 19.1. Then

$$
1\le N' := |\operatorname{supp}\widehat\nu_\beta|\le N-1,
\tag{19.15}
$$

and the excised pair has finite p-target slack at the accumulation parameter

$$
 r_* =\frac{3-\sqrt5}{2},\qquad c_* =\frac{25}{64},\qquad
 \delta_p^\circ:=\rho_p-\widehat{\mathcal L}_p(P_{p,r_*})\ge\sigma.
\tag{19.16}
$$

Choose $M\ge2$ so that

$$
 \frac{25}{171}c_*^M<\frac\sigma2,
 \qquad
 s_M=|\{k\le M:\mu(k)>0\}|.
\tag{19.17}
$$

Then there is an abstract finite original common conf/conf attainer with private table labels satisfying

$$
 |Y|=N',
 \qquad
 |X|\le N'^2+2N'+s_M-1.
\tag{19.18}
$$

It preserves the excised suspended marginal exactly. It need not preserve the input p marginal, the input flows, or the original pre-excision pair. The finite table has real stochastic entries; allowed finitely represented exact samplers are a separate requirement for effective attainment.

**Proof.** Because the installed support is infinite, its supported depths are unbounded and $r_k\to r_*$. The complete-target continuity bound (13.19) and the original supported-target budgets give

$$
\mathcal L_p(P_{p,r_*})\le\rho_p.
\tag{19.19}
$$

Taking the limit in (19.14), using the same complete-law continuity, gives

$$
\mathcal L_p^N(P_{p,r_*})\ge\rho_p+\frac\eta2.
\tag{19.20}
$$

Apply (19.9) at $T=P_{p,r_*}$ and use (19.19)--(19.20); this proves (19.16). Since $\theta<1$, the excised suspended marginal has positive total mass and at least one atom. At least one of the two distinct native suspended atoms is removed completely, while no new atom is created, so (19.15) holds.

Use the symmetric direction of Theorem 13.6 on the excised pair, with its $N'$ suspended atoms and the strict slack (19.16). Choose $M$ as in (19.17). Its exact feature menu has

$$
Q(E_p),\qquad
\{\operatorname{TV}(Q,P_{p,r_k}):3\le k\le M,\ \mu(k)>0\},
\qquad
\operatorname{TV}(Q,P_{p,r_*}),
\tag{19.21}
$$

which has $1+(s_M-2)+1=s_M$ entries. The symmetric moment list in Theorem 13.2 therefore gives exactly the bound (19.18), while retaining the complete p endpoint box and every listed loss. For every omitted installed depth $k>M$, the full-law estimate (13.19), not a truncated future, gives

$$
\widehat{\mathcal L}_p(P_{p,r_k})
 \le \widehat{\mathcal L}_p(P_{p,r_*})
      +\frac{25}{171}c_*^M
 <\rho_p.
\tag{19.22}
$$

Thus all supported p losses and the endpoint midpoint are valid in the new finite table, and the entire excised suspended marginal is unchanged. Proposition 13.3 and [PAID, Lemma 2.1.1] install this table with the original $C_0$, both seeds, all paid histories and rejections, source-independent latch initialization, the same acquired/synthetic update, complete noncompletion, completion and matching Stop. They also retain the original records and the once-sampled $K$; no posterior or resampling device is added. This is an abstract finite attainer, with the stated sampler qualification. $\square$

### 19.4 Source map, falsifier and remaining obligations

The full residual and marginal hypotheses in Theorem 19.1 are exactly (11.6)--(11.8), with TV inside (11.9). The endpoint boxes and midpoint event values are (11.29)--(11.30). The native recursions and the complete-coordinate gap (19.14) are supplied by Theorem 12.2 and Corollary 12.3; the constant $\eta$ is reused, not rederived. The equal-endpoint conditional extremality is the same countable-coordinate zero-integral mechanism used in PAIRED18.2. [REV, Theorem 5.1](RECURSIVE_RELATIONAL_OBSERVATION_REVERSIBLE_COMMON_GENERATOR_CONSTRAINTS.md) records the analogous endpoint-component propagation in its reversible class; reversibility is not a premise of this theorem. The finite feature closure, the full-law continuity estimate (13.19), and the original product adapter are respectively supplied by Theorems 13.2, 13.6, 13.3 and [PAID, Lemma 2.1.1]. No finite quadrature or realization proof is being claimed again.

A direct falsifier for Theorem 19.1 would be a zero-level compatible pair whose p native singleton has positive mass but whose conditional B flow assigns positive mass to a suspended law different from $P_{\beta,r}$ while every coordinate remains between the two suspended endpoint laws; the analogous A failure is also sufficient. Such a pair would contradict the endpoint mean argument in (19.11)--(19.13). A falsifier for Corollary 19.2 would satisfy all its zero-level and finite-suspended hypotheses but have $\delta_p^\circ<\sigma$, or would violate (19.22) at an omitted supported depth; the former contradicts the full-target limit and (19.9), while the latter would contradict the supplied complete-law estimate (13.19).

The source-relative addition is the simultaneous two-direction equal-mass excision and the generated strict p slack (19.10), followed by the symmetric use of the already supplied Chapter 13.6 consumer. It does not evaluate $j_c$, exhibit a zero pair, construct a vanishing family, or prove a positive unrestricted gap. A zero-level search may still have $m_am_b=0$ in the presence of a supported nonendpoint; Theorem 19.1 gives no strict conclusion there. It makes no weak-closed or compact claim for the atom-missing normal form, and it does not increase any finite-support bound. If no finite abstract attainer exists, the theorem only says that any zero pair with finite suspended marginal cannot have both native endpoint masses positive; it does not supply a zero witness. The finite-prior one-sided attainment statement is already Corollary 13.4. Finite atomicity, permitted exact sampling, COMPLETE resources, and the original unrestricted zero-versus-positive and effective-attainment obligations remain separate and unresolved.

## 追加锚（本行以下为增补区）
