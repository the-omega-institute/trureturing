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
