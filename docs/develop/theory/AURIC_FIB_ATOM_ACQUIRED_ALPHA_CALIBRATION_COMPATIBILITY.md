# Common endpoint calibration requires acquired-alpha emission change

## 1. Result and its precise scope

A finite same-update predictor can change its complete forecast on an acquired return without changing its next-alpha probability on the suspended-alpha update. The two properties are distinct. On the unchanged stopped Fibonacci source, nearly optimal common configuration risk requires both. The complete-return requirement is supplied by [MOTION]. This article proves the second requirement, through a source-specific endpoint calibration inequality on the same two acquired flows.

Let

$$
\eta=\frac{14219478376}{318644812890625}>0,
\qquad \kappa=\eta^2/64.
\tag{1.1}
$$

For an allowed finite observer $M$, write

$$
e(M)=\max_{s\in\{p,\beta\}}
\{R_{\mathrm{conf},s}(M)-\rho_s\}.
$$

At a positive suspended acquired history $h$, let $\rho_h(y)$ be its configuration row, $A_h(y,x)$ its actual alpha-update kernel, $v_y$ its current next-alpha probability, and $u_x$ the successor p configuration's next-alpha probability. Define

$$
\mathcal A_h(M)=\sum_{y,x}\rho_h(y)A_h(y,x)|v_y-u_x|,
\qquad
\mathcal A(M)=\sup_{h\in\mathcal H_\beta}\mathcal A_h(M).
\tag{1.2}
$$

The probability row is an analysis object. Runtime receives no row, posterior or new observation.

**Theorem 1.1.** For every allowed finite COMPLETE observer on every fixed finite or countable prior with positive endpoint masses and a supported nonendpoint,

$$
240e(M)+30\mathcal A(M)>\kappa>0.
\tag{1.3}
$$

Consequently exact common conf/conf attainment requires $\mathcal A(M)>\kappa/30$. A sequence with both excesses tending to zero must have $\liminf\mathcal A\ge\kappa/30$. No existence of such an optimizer or sequence is asserted. In the subclass $\mathcal A=0$, the unrestricted-over-finite-shapes excess is at least $\kappa/240$.

For regular stationary actual-flow tables, the proof gives the stronger, more informative relation

$$
\frac{\mathbb E_\pi[Z(1-Z)]}{16}
+h\mathcal E_C
\le G,
\tag{1.4}
$$

where

$$
Z_x=15u_x-5,\qquad
\mathcal E_C=\frac12\sum_{x,z}\pi_x(BA)_{xz}(u_x-u_z)^2,
$$

$$
G=\frac{\varepsilon_p}{d_p}+\frac{\varepsilon_\beta}{d_\beta}+KJ,
\quad J=\sum_{y,x}\tau_yA_{yx}|v_y-u_x|,
\tag{1.5}
$$

$$
d_p=\frac{1116529}{11390625},\quad d_\beta=\frac{239}{3375},
\quad h=\frac{1586793150}{266850431},
\quad K=\frac{7613443125}{266850431}.
\tag{1.6}
$$

Here $\varepsilon_s=R_{\mathrm{conf},s}-\rho_s$. If the same prior supports a nonendpoint, then $G>\kappa$ and hence

$$
25\max(\varepsilon_p,\varepsilon_\beta)+30J>\kappa.
\tag{1.7}
$$

Thus matching the suspended emission to every actual alpha-successor emission cannot support a nearly optimal common model merely by allowing arbitrarily complicated stochastic beta updates. This excludes a dynamic class without assuming native-mixture decoder laws, detailed balance, deterministic updates, a state-count ceiling or zero marginalized defect.

Equation (1.3) is a risk–update obstruction, not a positive unrestricted risk gap: $\mathcal A$ is unconstrained in the original problem. Exact attainment, an unattained zero infimum, a positive unrestricted gap and fixed-resource optima remain separate. The new relation does not replace the full-return statistic of [MOTION].

## 2. One source, one actual history, and complete laws

Fix $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$ and $m=2,d=1,\ell=2,n=4$. Draw one $K$ before the first Read from a fixed finite or countable prior $\mu$, with $\mu(1),\mu(2)>0$. Conditional on this same $K=k$, all paid seed and payload Reads are independent, with alpha probability

$$
r_k=F_{k+1}/F_{k+3},\quad r_1=1/3,\quad r_2=2/5,
\quad r_k\in I_0=[3/8,5/13]\ (k\ge3).
$$

The original parser rejects equal seed pairs and accepts both unequal seeds. At p, alpha completes marker 0 and beta suspends. At suspension, alpha returns to p and beta completes marker 1. The third record is written before its latch. Keep the entire original finite control $C_0$: seeds, selectors, bare fields, full marker tree, held $B,Q^+,Z$ records, parser, flags, permissions, completion, pendingStop and deliveredStop. Fourth completion enables its matching unique Stop; delivery is once only. Terminal cuts admit no Read. Both seeds, all marker triples, every positive finite paid rejection history and every positive finite return history remain in the domain.

More explicitly, alpha-beta accepts seed 0 and beta-alpha accepts seed 1. On all 16 complete marker words and their prefixes, a completed marker uses the old completed-marker count $t$ and old one-count $j$: the first zero is event $a$ ($e=0,t-j=0$), the second zero is $c$ ($e=0,t-j=1$), the first one is $b$ ($e=1,j=0$), and the second one is $d$ ($e=1,j=1$). For old $t<3$, append a recognized event to the original scopes $S_1^+=\{a,c,d\}$ and $S_2^+=\{b,c\}$ that contain it. Unmatched ordinal events, seed retries, returns, partial parses and completions with old $t\ge3$ hold these relation fields. Write $Z=e$ only at the first marker. At old $t=2$ complete the third record update before latching the original bare snapshot $B$; thereafter $B,Q^+,Z$ hold while the original fourth segment and Stop continue. This is [E1, §2]'s full-tree writer, without restricting to its illustrative accepted $E_1$ cell.

There is no reset, fresh depth, future-$E_1$ condition, extra source observation or controller port. Counts and posterior rows are analysis quantities. Original source and event definitions are supplied by [ST], [E1], [CLIP] and [PAID].

Put $a_r=r(1-r)$ and

$$
w_{j,0}=(\beta\alpha)^j\alpha,
\qquad w_{j,1}=(\beta\alpha)^j\beta\beta.
$$

The p future carrier contains these completed words and its unique infinite noncompletion word. The suspended carrier contains beta, $\alpha w_{j,b}$ and its infinite noncompletion word. The complete raw source laws are

$$
P_{p,r}(w_{j,0})=ra_r^j,
\qquad P_{p,r}(w_{j,1})=(1-r)^2a_r^j,
$$

$$
P_{\beta,r}(\beta)=1-r,
\quad P_{\beta,r}(\alpha w_{j,0})=r^2a_r^j,
\quad P_{\beta,r}(\alpha w_{j,1})=r(1-r)^2a_r^j.
\tag{2.1}
$$

Infinite-word masses are zero. The supplied measurable bijection $I_c$ retains every future Read and inserts its original event blocks, records, control, permissions, completion and Stop. Reading the letters back is its inverse. It preserves TV and commutes with deleting the next operation and its event block. An already acquired suspended beta is not another future Read.

At a positive acquired history $h$, all paid Reads, including rejected and partial pairs, contribute to its likelihood. Its target is

$$
T_h^\mu=(I_{C_0(h)})_*\sum_k\nu_h(k)P_{s,r_k},
\qquad
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
{\sum_t\mu(t)r_t^{A(h)}(1-r_t)^{B(h)}}.
\tag{2.2}
$$

The denominator is positive. To check the source-law correspondence, induct over the original legal operation list. A Read consumes precisely the next raw letter and performs the original deterministic event block; the unique enabled Stop consumes none, and delivery ends the list. Deleting only Stop from the acquired list therefore gives exactly its ordered finite raw-prefix cylinder. Rejected pairs, accepted seed letters, early payloads, returns and partial parses are retained. Its raw-cylinder likelihood conditional on $K=k$ is $r_k^{A(h)}(1-r_k)^{B(h)}$, and the unread letters are independent with this same parameter. Bayes conditioning of the summable prior gives (2.2), including countable priors. Nothing conditions on eventual completion.

An observer has one fixed finite COMPLETE carrier, source-independent initialization and fixed time-homogeneous source-independent acquired-letter stochastic updates. COMPLETE includes $C_0$, private labels, installed tables and program selectors, numerical representation, workspace, addresses, output indices and persistent randomness. There is no free tape, clock, archive, advice, continuous register, source-correlated seed or readable distribution vector. Each configuration's decoder $D_z$ is exactly its own complete legal generator law: its synthetic emissions use the same acquired-letter update kernels and original event blocks. Its output is a finite description of that law, such as the installed generator and current configuration index; it does not materialize a probability vector or an infinite word table. The configuration row and target posterior are used only to analyze this fixed description. An acquired history conditions on the original operation transcript, without selecting on private observer random bits or a sampled decoder report. Synthesis makes no actual source call.

At the same actual history,

$$
Q_h=\sum_z\rho_h(z)D_z,
\quad e_{\mathrm{law}}(h)=\operatorname{TV}(Q_h,T_h^\mu),
\quad e_{\mathrm{conf}}(h)=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu).
$$

TV is the event supremum, or half the countable $\ell^1$ distance on these fourth carriers. $R_{j,s}$ is the supremum over all positive histories $\mathcal H_s$. Full $\mathcal H_p$ includes arbitrary fourth returns; $\mathcal H_3$ includes only the first p cut. Actual-history-average risk is a different quantifier. The supplied separate full-tail minima are

$$
\rho_p=1116529/22781250=d_p/2,
\qquad \rho_\beta=239/6750=d_\beta/2.
\tag{2.3}
$$

The terminal values $13/266,9/266$ are not substituted for (2.3). The supplied finite-history witnesses are also retained with their original scopes. In the positive two-depth source, [ST, Theorem 2.1] gives, for each finite competitor and $0<\epsilon<1$, $0<\zeta<1/2$, two positive actual histories on the same control fibre with configuration-row TV at most $\epsilon$ and endpoint posterior errors at most $\zeta$, so

$$
\min\{R_{\mathrm{law},s},R_{\mathrm{conf},s}\}
\ge\frac{(1-2\zeta)d_s-\epsilon}{2}.
$$

For a finite or countable prior with additional depths, [ST, §3.3; PH, Theorem 2.1] supplies full-posterior endpoint exposure and the bound $(d_s-2\zeta-\epsilon)/2$. These are lower-bound witnesses on original paid histories, not uncharged reset experiments. Their small tolerances recover the separate radii; §7 separately spells out the common-row exposure used by the new proof.

The existing actual three-depth endpoint-tag counterexample uses $\mu=(1/10000,1/10000,4999/5000)$ and $h_0=\beta\alpha\mid\beta\beta\alpha\alpha$, with both seeds and all other histories still allowed. Its posterior weights are proportional to $\mu(k)a_{r_k}^3$. At this actual third-latch history the complete word $w_{3,1}$ has target mass above both endpoint masses. Thus the fair persistent endpoint-tag generator fails its claimed p configuration-risk benchmark there [ST, (3.17)–(3.21)]. This is that generator's configuration-risk failure, not a universal arbitrary-kernel lower bound or a marginalized-risk violation. Section 6 uses the supplied pure-target interior excess only after a new joint calibration argument has forced approximate endpoint tags.

Retain the original marginalized defect: if a legal next operation $a$ has $q_h(a)=Q_h([a])>0$, condition on its cylinder, delete the operation and original event block, and set $\delta(h,a)=\operatorname{TV}(\operatorname{res}_aQ_h,Q_{ha})$. At zero predicted probability set the defect to zero without defining a conditional law; the actual successor and its risk remain in the domain. $\Delta_4$ and $\Delta_{\rm all}$ retain their respective original domains. Pending Stop has zero defect and the delivered empty supremum is zero. This article assumes no defect budget and makes no zero-defect recovery claim. Individual generation remains exact.

For (1.2), conditional on $h$, observer randomness and $K$ are independent: their likelihoods factor along its fixed acquired word. More explicitly, at a suspended cut,

$$
\Pr(K=k,Y_h=y,\text{next actual letter}=\alpha,X_{h\alpha}=x\mid h)
=\nu_h(k)\rho_h(y)r_kA_h(y,x).
$$

Divide its sum over $k$ by $\sum_k\nu_h(k)r_k>0$. The actual edge row is exactly $\rho_h(y)A_h(y,x)$, without synthetic emission tilting. Thus (1.2) is expected next-alpha prediction change conditional on the same actual history and its next actual alpha. It does not acquire an additional letter.

## 3. Common flows and endpoint event calibration

For a regular stationary table, use finite p and suspended label sets $X,Y$, positive probability rows $\pi,\tau$, row-stochastic acquired kernels $B:X\to Y$, $A:Y\to X$, and emissions $u_x,v_y\in[1/3,2/5]$. Both actual flows satisfy

$$
\pi B=\tau,\qquad \tau A=\pi.
\tag{3.1}
$$

Zero-row labels can be deleted: the two nonnegative flow identities exclude transitions into them from positive-row labels. Write $C=BA$. The source-independent latch sampler installs $\pi$ after the original third record write and latch. Its full-domain product realization is supplied by [PAID, Lemma 2.1.1]: take the product with the complete original $C_0$, keep its deterministic update and event block on every operation, and use the private kernels only on the original noncompleting beta and alpha updates. Completion clears private labels and enables only the original matching Stop. Earlier synthetic letters are fair; sampling $\pi$ follows the third record write and latch within that same original update. Both seeds and every marker triple use this rule while retaining their own records. The private component never changes the permission menu. Induction on operations preserves all original fields and legal paths; it introduces no source query or controller port. Define each decoder by running this same synthetic program from its current configuration, including its original completion and Stop. Earlier rejected-pair survival is $1/2$, early payload-return survival is $1/4$, and fourth-return survival is at most $4/15$, so completion is almost sure. Infinite noncompletion stays in the carrier with zero mass rather than being conditioned away. Pending and delivered decoders are the unique Stop future and empty future. All private labels, tables and sampler service states are counted in COMPLETE. Actual rows are $\pi,\tau$ after every fourth history by (3.1), without synthetic weighting.

The generated complete raw laws obey

$$
Q_x=u_x\delta_\alpha+(1-u_x)\beta\sum_yB_{xy}W_y,
\qquad
W_y=(1-v_y)\delta_\beta+v_y\alpha\sum_xA_{yx}Q_x.
\tag{3.2}
$$

Prefixing keeps the entire raw word and its subsequent $I_c$ rendering. Every return survives with probability at most $\lambda=4/15$, so these equations determine normalized complete laws, retaining infinite outcomes with zero mass.

On these tables the supported pure-target configuration-loss supremum equals the full positive-history risk [CLIP, Proposition 2.3]. For the upper direction, substitute (2.2) and use countable convexity of TV with the fixed actual label row. For the converse, the paid rejection histories constructed in §7 expose each supported depth while the installed actual row is unchanged. TV is 1-Lipschitz in its target, so those positive histories approach its pure-target loss. The same reasoning works for the law order after mixing configurations. Endpoint triangle inequalities imply $\varepsilon_p,\varepsilon_\beta\ge0$. This includes the entire countable posterior and paid rejection exposure, not a new reset experiment.

Use the supplied endpoint-positive events

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},
\qquad E_\beta=\{\beta,\alpha w_{0,1}\}.
$$

Their endpoint probabilities are $412/729,7299/15625$ and $22/27,93/125$. Their respective differences are $d_p,d_\beta$; their midpoints are

$$
C_p=11758471/22781250,
\qquad C_\beta=5261/6750.
$$

The endpoint distances can be checked without a future cutoff. On p marker-0 words the endpoint-2/endpoint-1 ratio is $(6/5)(27/25)^j>1$; on marker-1 words it is $(81/100)(27/25)^j$, below one for $j=0,1,2$ and above one for $j\ge3$. At suspension the standalone beta ratio is $9/10<1$, the alpha-marker-0 ratio is $(36/25)(27/25)^j>1$, and the alpha-marker-1 ratio is $(243/250)(27/25)^j$, below one only at $j=0$. Both infinite masses are zero. Thus the displayed events are exactly the positive endpoint-1 difference events on the complete carriers, and their mass differences equal the full TV distances $d_p,d_\beta$.

Let $a=\pi Q(E_p)$ and $b=\tau W(E_\beta)$. Endpoint risk bounds imply

$$
|a-C_p|\le\varepsilon_p,
\qquad |b-C_\beta|\le\varepsilon_\beta.
\tag{3.3}
$$

Indeed TV to endpoint 1 is at least its event probability minus the predicted event probability; TV to endpoint 2 is at least the reverse difference. Average before using these inequalities. Both endpoint risk bounds give (3.3). The argument does not confuse an expected configuration loss with a marginalized loss; convexity permits the event bound in either order.

## 4. A paired-emission comparison controlled by the actual alpha edges

On the same source and prior, construct a comparison table with p and suspended labels both $X$, rows both $\pi$, acquired beta kernel $C=BA$, acquired alpha kernel the identity, and both emissions $u$. It has both exact acquired flows. Denote its own generated laws by $\widetilde Q_x,\widetilde W_x$.

This is a finite installed comparison, not an assigned posterior or a pointwise replacement decoder. Its private beta kernel is the fixed matrix product $BA$; it does not perform another source Read. Its actual and synthetic updates use this same kernel. Product realization retains every original field and permission; earlier synthesis is fair, latch sampling follows the third write, completion clears private labels, and only original Stop delivers. No state, program, sampler-workspace or hard-defect budget is preserved.

Set

$$
J=\sum_{y,x}\tau_yA_{yx}|v_y-u_x|,
\qquad d=\sum_x\pi_x\operatorname{TV}(Q_x,\widetilde Q_x).
$$

**Lemma 4.1.** The complete laws satisfy

$$
d\le10J/11.
\tag{4.1}
$$

If $\widetilde a=\pi\widetilde Q(E_p)$ and $\widetilde b=\pi\widetilde W(E_\beta)$, then

$$
|a-\widetilde a|\le10J/11,
\qquad |b-\widetilde b|\le15J/11.
\tag{4.2}
$$

Proof. Expand the original p continuation by first sampling $y$ through $B$ and $x'$ through $A$. This presampling of $x'$ is a coupling calculation; on a completing beta it is discarded. Its law is still (3.2). At suspension couple the Bernoulli emissions $v_y$ and $u_{x'}$. Their mismatch probability is $|v_y-u_{x'}|$. A matched alpha continues at $x'$ in both generators. The p emissions already agree. For $d_x=\operatorname{TV}(Q_x,\widetilde Q_x)$ this gives

$$
d_x\le(1-u_x)\sum_{y,x'}B_{xy}A_{yx'}
\bigl(|v_y-u_{x'}|+u_{x'}d_{x'}\bigr).
$$

Average by $\pi$. Using (3.1), $1-u\le2/3$, $u\le2/5$ and $\pi C=\pi$ yields $d\le(2/3)J+(4/15)d$, proving (4.1). This couples complete generators through all returns, not just terminal outcomes.

The p event bound follows. Write $g_x=Q_x(w_{0,1})$, $\widetilde g_x=\widetilde Q_x(w_{0,1})$. Then

$$
b=\sum_{y,x}\tau_yA_{yx}(1-v_y+v_yg_x),
\quad \widetilde b=\sum_{y,x}\tau_yA_{yx}(1-u_x+u_x\widetilde g_x).
$$

Their difference is the average of $(u_x-v_y)(1-g_x)+u_x(g_x-\widetilde g_x)$. Since $0\le g_x\le1$, its absolute value is at most $J+(2/5)d\le15J/11$. This proves (4.2). No comparison of the two suspended configuration risks is inferred: averaging through $A$ cannot be reversed using convexity. ∎

## 5. The source-specific calibration energy inequality

The comparison uses any finite stationary row-stochastic $C$; it need not be reversible or irreducible. Put $U_x=1-u_x$, $a_x=u_xU_x$, and use the real inner product $\langle f,g\rangle=\sum_x\pi_xf_xg_x$. Let $C^*$ be its adjoint. It is a stochastic kernel because $\pi C=\pi$. Both $C,C^*$ contract this norm by Jensen. They are analysis tools, not extra runtime updates.

Define

$$
\mathcal E_C=\langle U,(I-C)U\rangle
=\frac12\sum_{x,z}\pi_xC_{xz}(u_x-u_z)^2.
\tag{5.1}
$$

For $P=C$ or $C^*$,

$$
\|(I-P)U\|^2\le2\mathcal E_C.
\tag{5.2}
$$

This follows by expanding the square, using norm contraction and $\langle U,PU\rangle=\langle U,CU\rangle$.

A useful elementary stationary-coupling inequality is

$$
\langle f(U),(I-P)U\rangle\ge0
\quad\text{when }f\text{ is nondecreasing}.
\tag{5.3}
$$

Take a convex primitive $F$ of $f$. Its tangent inequality gives $F(U_z)-F(U_x)\ge f(U_x)(U_z-U_x)$. The stationary expectation of the left side is zero. This proves (5.3), for both $P$, without detailed balance. This convexity fact is a mature tool.

For the paired table, set $H=\operatorname{diag}(U)C\operatorname{diag}(u)$ and $g=\operatorname{diag}(U)CU$. Its p event mean expands as

$$
\widetilde a
=\langle U,CU\rangle+
\langle U,C\operatorname{diag}(a)CU\rangle+
\langle U,C\operatorname{diag}(a)C\operatorname{diag}(a)CU\rangle.
\tag{5.4}
$$

Let

$$
\varphi_p(u)=(1-u)^2(1+u(1-u)+u^2(1-u)^2),
\quad \varphi_\beta(u)=1-u+u(1-u)^2.
$$

**Lemma 5.1.** With $c=15493/50625$,

$$
\widetilde a\le\mathbb E_\pi\varphi_p(u)-c\mathcal E_C,
\qquad
\widetilde b\ge\mathbb E_\pi\varphi_\beta(u)+\mathcal E_C/5.
\tag{5.5}
$$

Proof. Here $U\in[3/5,2/3]$ and $0<a=U-U^2\le a_*=6/25$. The first term in (5.4) is $\langle U,U\rangle-\mathcal E_C$.

For its second term, the weighted square inequality gives

$$
\langle C^*U,\operatorname{diag}(a)CU\rangle
\le\tfrac12\sum_{P\in\{C,C^*\}}
\langle PU,\operatorname{diag}(a)PU\rangle.
$$

Each summand equals

$$
\langle U,\operatorname{diag}(a)U\rangle
-2\langle aU,(I-P)U\rangle
+\langle(I-P)U,\operatorname{diag}(a)(I-P)U\rangle.
$$

The function $aU=U^2-U^3$ has derivative $U(2-3U)\ge0$. Equations (5.2)–(5.3) therefore bound the second term in (5.4) by its diagonal value plus $2a_*\mathcal E_C$.

For the third term, let $t_-=\operatorname{diag}(a)C^*U$ and $t_+=\operatorname{diag}(a)CU$. Norm contraction and Cauchy give $\langle t_-,Ct_+\rangle\le(\|t_-\|^2+\|t_+\|^2)/2$. Each norm square expands as

$$
\|aU\|^2-2\langle a^2U,(I-P)U\rangle
+\|\operatorname{diag}(a)(I-P)U\|^2.
$$

For $f(U)=a^2U=U^3(1-U)^2$,

$$
f'(U)=U^2(1-U)(3-5U)\ge-4/81.
$$

Indeed $U^2(1-U)\le4/27$ and $0\le5U-3\le1/3$ on this interval. Thus $f(U)+(4/81)U$ is nondecreasing. Equations (5.2)–(5.3) bound each square by $\|aU\|^2+(8/81+2a_*^2)\mathcal E_C$. Combining the three terms gives the first inequality in (5.5), since

$$
1-2a_*-8/81-2a_*^2=15493/50625>0.
$$

Finally $\widetilde b=\mathbb E U+\langle a,CU\rangle$. The function $a(U)+U/5$ is nonincreasing, because its derivative $6/5-2U\le0$. Apply (5.3) to its negative. It gives $\langle a,(I-C)U\rangle\le-\mathcal E_C/5$, proving the second inequality. ∎

The supplied stopped-source polynomial sign [MIXSEP, §3] is, for $z=15u-5\in[0,1]$,

$$
\frac{412/729-\varphi_p(u)}{d_p}
-\frac{22/27-\varphi_\beta(u)}{d_\beta}
\ge z(1-z)/16.
\tag{5.6}
$$

It is the pointwise part of its Lemma 3.1. To verify the needed sign directly, the left side of (5.6) factors as

$$
\frac{z(1-z)(17655975+459915z-6931z^2-6931z^3+239z^4)}{239\cdot1116529}.
$$

The parenthesis is at least $17642113$ on $[0,1]$, and $16\cdot17642113=282273808>266850431=239\cdot1116529$. This exact source-specific sign is reused, not claimed as new.

Apply (5.5)–(5.6) to the normalized comparison score

$$
\widetilde D=
\frac{412/729-\widetilde a}{d_p}
-\frac{22/27-\widetilde b}{d_\beta}.
$$

It is at least $\mathbb E[Z(1-Z)]/16+h\mathcal E_C$, with $h=c/d_p+1/(5d_\beta)$. At the two event midpoints the score is zero. Equations (3.3) and (4.2) give its upper bound $G$ in (1.5), with $K=10/(11d_p)+15/(11d_\beta)$. The fractions in (1.6) follow by rational arithmetic. This proves the new joint calibration relation (1.4).

If $J=\varepsilon_p=\varepsilon_\beta=0$, then $u$ is supported on the two endpoints and $C$ preserves $u$ on every positive edge. Equation (4.1) makes the original p laws equal the paired ones. Their return dynamics then retain their endpoint parameter, so each is a pure endpoint source law. Moreover $J=0$ gives $v_y=u_x$ on each positive alpha edge. Since $BA$ preserves $u$, every positive beta edge also preserves that endpoint value. Thus the suspended laws are pure matching endpoint laws. Event calibration forces fair endpoint weights. This is a dynamic rigidity conclusion, without a native-mixture premise.

## 6. Consuming the supported interior full-tail risk

Energy and endpoint calibration alone do not prove an interior risk obstruction. This section supplies that missing consumption on the same table and prior.

Use the supplied complete-law Lipschitz bound [CLIP, Proposition 5.3]

$$
\operatorname{TV}(P_{p,u},P_{p,t})\le L_p|u-t|,
\qquad L_p=125/57.
$$

Here is the complete-law coupling behind this bound. Couple Bernoulli-$u$ and Bernoulli-$t$ letters until their first discrepancy. Before then the original parsers and event blocks agree. The mismatch probability at each live Read is $|u-t|$. The expected remaining Read count at parameter $u$ solves $N_u=1+(1-u)(1+uN_u)$, hence $N_u=(2-u)/(1-u(1-u))\le125/57$. Summing first-discrepancy hazards gives the displayed bound on the entire stopped word and its $I_c$ rendering. Both generators complete almost surely, with the infinite outcome retained. No finite future horizon is used.

Put $d_x'=\operatorname{TV}(\widetilde Q_x,P_{p,u_x})$. The paired equations and a Bernoulli-emission coupling give

$$
d_x'\le(1-u_x)\sum_zC_{xz}
\bigl((1+u_zL_p)|u_z-u_x|+u_zd_z'\bigr).
$$

After averaging, stationarity and $\lambda=4/15$ yield

$$
\mathbb E d_x'\le k\sum_{x,z}\pi_xC_{xz}|u_x-u_z|
\le k\sqrt{2\mathcal E_C},\qquad k=1070/627.
\tag{6.1}
$$

All distances here concern the complete laws, including all return words and infinite outcomes.

Round $u_x$ to the nearer endpoint $t_x\in\{1/3,2/5\}$, taking the lower one on a tie. Since $|u_x-t_x|\le(2/15)Z_x(1-Z_x)$, (1.4), (4.1), (6.1) and the Lipschitz bound give

$$
d_0:=\sum_x\pi_x\operatorname{TV}(Q_x,P_{p,t_x})
\le\frac{10}{11}J+k\sqrt{2\mathcal E_C}+\frac{800}{171}G.
\tag{6.2}
$$

These endpoint laws are comparison laws inside a proof. They are not asserted to be a risk-dominating replacement observer.

Let $w=\pi\{t_x=1/3\}$. The p endpoint event calibration implies

$$
|w-1/2|\le(\varepsilon_p+d_0)/d_p.
\tag{6.3}
$$

For every $r\in I_0$, the supplied interior complete word $w_{3,1}$ has mass above both endpoint masses by at least $\eta$. Its mass is $r^3(1-r)^5$, decreasing on $I_0$, and (1.1) is its value at $5/13$ minus its endpoint-2 value. Endpoint 2 has the larger endpoint mass.

For any normalized countable laws $D,P_1,P_2$, including their infinite outcome, the scalar identity $|d-a|+|d-b|-|a-b|=2\operatorname{dist}(d,[a\wedge b,a\vee b])$ summed over coordinates gives

$$
\operatorname{TV}(D,P_1)+\operatorname{TV}(D,P_2)-\operatorname{TV}(P_1,P_2)
=\sum_w\operatorname{dist}(D(w),[P_1(w)\wedge P_2(w),P_1(w)\vee P_2(w)]).
$$

The single coordinate $w_{3,1}$ is at least $\eta$ outside the endpoint interval. With $D=P_{p,r}$, the identity therefore gives

$$
\frac{\operatorname{TV}(P_{p,1/3},P_{p,r})+
\operatorname{TV}(P_{p,2/5},P_{p,r})}{2}
\ge\rho_p+\eta/2.
\tag{6.4}
$$

This is the supplied [NATIVE, §6] full-tail interior excess. Reverse triangle bounds the change from fair weights by $d_p|w-1/2|$. The triangle inequality for each configuration, followed by (6.3), consequently gives

$$
\sum_x\pi_x\operatorname{TV}(Q_x,P_{p,r})
\ge\rho_p+\eta/2-\varepsilon_p-2d_0.
$$

Choose one actually supported nonendpoint. Its original pure-target configuration risk is at most $\rho_p+\varepsilon_p$. Therefore

$$
\eta/4\le\varepsilon_p+d_0.
\tag{6.5}
$$

This step uses configuration-before-TV. It is not supplied by a marginalized risk bound or by separate phase attainment.

From (1.4), $\mathcal E_C\le G/h$, while $\varepsilon_p\le d_pG$ and $J\le G/K$. Substituting (6.2) into (6.5) gives

$$
\eta/4\le A_0G+B_0\sqrt G,
$$

$$
A_0=d_p+800/171+10/(11K)<5,
\qquad B_0^2=2k^2/h<1.
\tag{6.6}
$$

All comparisons are rational: $A_0=1721459302499479/358022162953125$ and $B_0^2=12220682338076/12476288085327$. If $G\le\eta^2/64$, the right side is at most $5\eta^2/64+\eta/8<\eta/4$, since $0<\eta<8/5$. This contradiction proves $G>\kappa$.

Finally $1/d_p+1/d_\beta=6490644750/266850431<25$ and $K<30$. Hence $G\le25\max(\varepsilon_p,\varepsilon_\beta)+30J$, proving (1.7). The constants are conservative; no optimality is claimed.

## 7. Arbitrary finite observers and zero or unit emissions

Use the common paid-history extraction of [MIXSEP, Lemma 2.1], retaining both configuration-risk bounds. Apply its bounded p-state statistic assertion to

$$
f_B(x)=\sum_yB_{xy}\sum_zA_{yz}|v_y-u_z|.
$$

For every positive p history $h$ on this fiber, its actual successor $h\beta$ is a positive suspended history and $\rho_{h\beta}=\rho_hB$. Therefore $\rho_hf_B=\mathcal A_{h\beta}(M)\le\mathcal A(M)$. No extra observation is supplied. The extraction gives one original record fiber, its original acquired $B,A$, a stationary pair $\pi B=\tau,\tau A=\pi$, the original generated laws, simultaneous supported pure-target risk bounds, and

$$
J_0=\pi f_B=\sum_{y,z}\tau_yA_{yz}|v_y-u_z|\le\mathcal A(M).
\tag{7.1}
$$

For completeness, choose the actual suffix $S=\beta\alpha\mid\beta\beta\alpha\alpha$, which accepts seed 1, writes marker triple 100 and reaches the third latch. At the rejected-pair boundary the acquired updates for $\alpha\alpha$ and $\beta\beta$ are finite stochastic matrices $T_\alpha,T_\beta$. Finite Markov-chain decomposition supplies integers $d_\alpha,d_\beta>0$ such that $T_\alpha^{d_\alpha n}\to E_\alpha$ and $T_\beta^{d_\beta n}\to E_\beta$: transient mass vanishes, and multiples of the closed-class periods make the recurrent classes aperiodic. For each supported $r=r_k$, set

$$
m_n=d_\alpha\lfloor nr/d_\alpha\rfloor,
\qquad t_n=d_\beta\lfloor n(1-r)/d_\beta\rfloor,
\qquad h_n=(\alpha\alpha)^{m_n}(\beta\beta)^{t_n}S.
$$

Every $h_n$ is a positive original paid history. Its configuration row converges to the same $\lambda_0=\rho_0E_\alpha E_\beta P_S$, independently of the chosen depth. The ratio of another supported depth's rejection likelihood to that depth's likelihood is

$$
\exp\{-2n\operatorname{KL}(\operatorname{Ber}(r)\Vert\operatorname{Ber}(r_i))+O(1)\}.
$$

The rounding term is uniformly bounded in $i$, since all parameters lie in $[1/3,2/5]$; the fixed positive suffix-likelihood ratios are uniformly bounded as well. The Fibonacci parameter recurrence $r\mapsto(1-r)/(2-r)$ is a strict contraction with an irrational fixed point; its rational orbit cannot repeat. Thus each other-depth likelihood ratio tends to zero. The uniform bound and summable prior masses allow dominated convergence, so the entire posterior concentrates on the chosen supported depth. Its target converges in TV, since posterior mass $1-\zeta$ at that depth puts the mixture within $\zeta$ of its law. This includes every countable prior in the theorem.

Append any fixed number $j$ of the actual returns $\beta\alpha$, and optionally beta. Concentration survives, while the configuration rows approach $\lambda_0(BA)^j$ and $\lambda_0(BA)^jB$ independently of depth. TV loss is 1-Lipschitz in its target and continuous in the finite configuration row. Both configuration-risk bounds and the bound on $f_B$ therefore hold at these common rows for every supported depth.

Take a convergent subsequence of $\pi_N=N^{-1}\sum_{j<N}\lambda_0(BA)^j$. The identity $\pi_NBA-\pi_N=(\lambda_0(BA)^N-\lambda_0)/N$ gives $\pi BA=\pi$ at its limit. Put $\tau=\pi B$; then both acquired flows hold. Configuration loss and $f_B$ are linear in the row, so all their bounds survive on this one common stationary pair, simultaneously for every supported depth. A positive limiting coordinate is positive at some finite return row and hence at a sufficiently late finite paid-history approximant. It is reachable under the original source. This is the supplied extraction route, not a limiting runtime or a resource-preserving replacement.

Clip the extracted emissions into $[1/3,2/5]$, retaining both actual kernels and rows, and regenerate their own complete laws. The exact supplied clipping result [CLIP, Theorem 3.1] gives

$$
\widehat\varepsilon_p\le(41\varepsilon_p+20\varepsilon_\beta)/11,
\quad \widehat\varepsilon_\beta\le(12\varepsilon_p+41\varepsilon_\beta)/11,
$$

$$
\pi|u-\widehat u|\le2\varepsilon_p,
\qquad \tau|v-\widehat v|\le2\varepsilon_\beta.
\tag{7.2}
$$

These bounds can be verified directly on this extracted stationary pair. Apply the coordinate identity in §6 to each configuration law and then average its two endpoint losses. Their sum is at most $2\rho_s+2\varepsilon_s$, so the mean total outside-box coordinate mass is at most $2\varepsilon_s$. The p word alpha has probability $u_x$, and the suspended word beta has probability $1-v_y$; their outside-box distances are exactly $|u_x-\widehat u_x|$ and $|v_y-\widehat v_y|$. This proves the last two inequalities, including original zero or unit emissions.

For the generated laws, couple old and clipped synthetic letters maximally while their configurations agree, then couple the unchanged acquired-update row identically. The chance of remaining matched is dominated by the clipped generator's survival subprobability. Its p return kernel is bounded entrywise by $\lambda BA$, $\lambda=4/15$, so after $j$ returns its row from $\pi$ is at most $\lambda^j\pi$. At suspension that row is at most $(2/3)\lambda^j\tau$. The clipped generator completes almost surely. Summing mismatch hazards through its whole future yields

$$
\pi\operatorname{TV}(Q,\widehat Q)
\le\frac{2\varepsilon_p+(2/3)2\varepsilon_\beta}{1-4/15}
=\frac{30\varepsilon_p+20\varepsilon_\beta}{11}=:T_p.
$$

From $\tau$, the initial hazard is at most $2\varepsilon_\beta$; a matched alpha gives a p subrow at most $(2/5)\pi$. Hence

$$
\tau\operatorname{TV}(W,\widehat W)
\le2\varepsilon_\beta+(2/5)T_p
=\frac{12\varepsilon_p+30\varepsilon_\beta}{11}=:T_\beta.
$$

On no mismatch the old generator completes with the clipped one, so old positive noncompletion mass is included in the coupling bound. Triangle inequality for each configuration gives the first two bounds in (7.2). No positivity hypothesis is added to the original competitor, and no zero-probability synthetic conditioning is performed.

The same acquired alpha edges give

$$
\widehat J\le J_0+2\varepsilon_p+2\varepsilon_\beta.
\tag{7.3}
$$

Delete zero-row labels and install the clipped stationary table by the original finite product realization. It preserves the source, history domain and current-record maps. Its supported pure-target bounds imply the same all-history bounds by countable target convexity. No hard defect or resource budget is preserved.

The regular result gives $\widehat G>\kappa$. Equations (7.1)–(7.3), with $e=\max(\varepsilon_p,\varepsilon_\beta)$, give

$$
\widehat G\le
\left(\frac{61}{11d_p}+\frac{53}{11d_\beta}+4K\right)e
+K\mathcal A(M)
<240e+30\mathcal A(M)
$$

unless both right-hand quantities vanish; that case is already contradicted by $\widehat G>\kappa$. The coefficient of $e$ is exactly $63706776750/266850431<240$. Thus (1.3) holds for arbitrary finite COMPLETE observers. The argument covers all positive finite rejection and return histories, and finite or countable priors. It does not enumerate finite observer shapes. ∎

## 8. Independence from complete-return motion and consequences

The two necessary update statistics are not equivalent. A persistent single label with p emission $1/3$ and suspended emission $2/5$, and identity private updates, has $\mathcal A=1/15$ but zero p-to-p semantic return motion. Conversely take two labels, fair row, $A=I$, $B$ the label swap, and $u=v=(1/3,2/5)$. It has $\mathcal A=0$ and positive complete p-law return motion: the immediate-alpha coordinates of its two generated p laws differ by $1/15$. Both are lawful rational product observers on the original full domain; neither is offered as a common optimizer. The second example is a genuinely changing same-update generator covered by the new obstruction, without a native-mixture assumption.

At exact endpoint calibration, (1.4) with $J=0$ forces the acquired return to preserve emission values and the generated laws to become pure endpoint tags. The supported interior complete word then defeats their common configuration benchmark. Thus positive full-law motion cannot be reconciled with the two calibration boxes by simply conserving the suspended-to-p emission value on every acquired alpha edge.

For task-relative whitebox quality $W_s=1-R_{\mathrm{conf},s}$, simultaneous $W_s\ge1-\rho_s-e$ requires

$$
\mathcal A(M)\ge\frac{(\kappa-240e)_+}{30}.
$$

The bound is strict when $\kappa-240e>0$. This concerns a semantic emission and actual update together; it does not identify internal implementations or classify arbitrary trained networks by FIB's five windows.

The original law/law and law/conf attainments remain supplied by [FOUR], and conf/law by [SWITCH], on their unchanged full original history domains. Event calibration in §3 works with either order, but §6 consumes p configuration risk and the arbitrary-emission clipping in §7 consumes both configuration risks. No new attainment for any of the four combinations is asserted. The paired comparison does not dominate the original suspended configuration risk. The source, prior and actual histories are common throughout; separately attainable coordinates are never identified as a jointly attained vector.

A concrete next path for the GoalArtifact's common conf/conf consumer is to combine nonzero alpha-edge emission change, the positive complete-return motion of [MOTION], the complete endpoint word boxes and supported interior configuration losses on one actual $B,A$ circulation. A candidate with $J=0$ is now excluded across all finite shapes. A candidate with $J>0$ must still satisfy every original box and risk obligation; this theorem supplies no such table. Establishing that every lawful candidate also has too little $J$, or constructing a compatible table with both necessary changes, remains open.

## 9. Supplier correspondence, checks and limits

The new ingredient is the stationary acquired-flow energy inequality (5.5), its alpha-edge comparison (4.1)–(4.2), and their consumption by complete configuration risk to produce (1.3). Markov norm contraction, convex primitives, Cauchy, coupling, triangle identities and finite-chain extraction are mature tools. The polynomial source sign, interior word excess, phase minima, clipping and actual-history exposure are explicitly reused suppliers.

[MOTION] requires positive complete p-to-p forecast motion and permits phase-asymmetric persistent labels in its comparison. It does not bound alpha-edge emission conservation. [MIXSEP] excludes a neighborhood of native source-mixture laws, but does not assume or derive the new joint emission-energy inequality for arbitrary nonnative generators. [NATIVE] gives mixture recurrence rigidity, not the dynamic $J=0$ exclusion without a mixture premise. [PAID, §§9–10] supplies all-shape approximation/certification, not (5.5); its §11 witness has distinct $u,v$ and positive $J$, so its small positive excess is consistent with (1.3). [PH, §§14–20] controls deterministic-cycle and single-mode budgets; taking expected configuration loss over a stationary stochastic circulation is a different consumer. These named supplier scopes do not contain the new alpha-edge relation.

The stopped-source suppliers are pinned to `adcffe6be4e7cf9793d92a79bfbd5365557a7852`. The current public comparison pin is `4d48962cafb2e5cc7cab08fbf490acdcd654dce2`. The scoped theory-source difference between these pins consists solely of [LOCAL], the 302-line volume with SHA256 `a66d454e0df632c7e9ba4d5af505d84da2b17ba46dea0d74bbc325eb4185f85b`; the named stopped-source suppliers are unchanged. [KB, §§16–21] offers safe original-mod2 phase acquisition and conditional INITIAL full-block fee bounds. Its target-preservation and exact-charge transport obligations remain open. That source has no stochastic p/suspended calibration or complete-tail configuration-risk interface. Its two-window separation suggests checking consecutive operations jointly, but no theorem, operation, risk or cost is transported here. Public tree-cache and chronology suppliers likewise do not provide a runtime posterior or alter repeated paid iid Reads.

The complete [LOCAL] volume studies open position chains with adjacent exclusion. Its local reconstruction and inverse-response claims require strict-interior means and, where declared, first-order Markov or positive product-activity laws. Its arbitrary-law fibre and entropy comparisons retain their separate hypotheses. Its source assumption is not the stopped shared-depth iid source of this article. The correspondence is as follows.

| Contract coordinate | [LOCAL] | This article and transfer boundary |
| --- | --- | --- |
| Object and source | One finite occupation word $b_1,\ldots,b_N$ with $b_ib_{i+1}=0$; core reconstruction uses strict $0<u_i<1$ and $1-u_i-u_{i+1}>0$; first-order Markov or positive product-activity hypotheses where used. General adjacent-exclusion laws appear in its fibre/entropy comparisons. | One $K$ before all paid Reads; conditional iid letters at $r_K$; both equal seed rejections and arbitrary returns remain positive. No source identity is supplied. |
| Operations and history | Reconstruction from declared position means, edge marginals and activities; conditional chain propagation across positions. | Original repeated paid Read/parser/write/latch/Stop operations and two unweighted acquired kernels $B,A$ on the same observer. [LOCAL] installs neither acquired flow. |
| Observation and risk | Mean-completion fibres, relative-entropy/conditional-information identities, inverse covariance and response determinant. | Complete stopped-tail TV with configuration-before-TV on all positive histories. Mean sufficiency inside a declared product model does not imply either endpoint risk box. |
| Resources | A finite mathematical position model and response matrices; no stated runtime calibration/sampling service for this task. | One finite COMPLETE runtime configuration and counted programs, tables, service states and persistent randomness; analysis rows are not runtime inputs. No resource domination follows. |
| Live bridge | Its reconstruction and orthogonal-innovation proofs use the declared Markov factorization; its inverse-covariance proof uses the positive product-activity mean map. These are cited application hypotheses, without a necessity claim for every law sharing a response matrix. | The proof uses stationarity of arbitrary, possibly nonreversible $BA$ and complete same-update generators. It assumes no position-chain or product-activity factorization. |

Even the direct letter-to-occupation identification fails. If alpha is occupation 1, the adjacent-exclusion pair 11 forbids alpha-alpha, yet the actual seed rejection alpha-alpha has probability $r_k^2>0$. If beta is occupation 1, it forbids beta-beta, yet that actual rejection and a legal completing payload have probability $(1-r_k)^2>0$. Thus neither nonconstant binary relabelling transports the actual source and operation domain. This refutes that specific proposed identification, not the existence of every possible more elaborate bridge. A different encoding would need a proved joint law, operation, loss and resource correspondence; none is used here.

[LOCAL]'s conditioning and orthogonal residuals are useful prompts to preserve joint relations rather than infer a source from means alone. Its static Markov uniqueness, conditional-information loss, tridiagonal inverse covariance and Gram determinant neither supply (5.5) nor dominate the alpha-edge comparison and full configuration-risk consumption. This finding uses the complete volume's actual assumptions, rather than its FIB title or the shared word “Markov”.

Primary literature search inspected [CK], [Z], [AZ], [TS], [CJ] and [MW], together with the finite-memory survey and its binary-testing paper [BOS]. [CK] approximates TV between supplied labelled Markov chains. [TS] and [CJ] address positive state-space/Markov realizations of supplied transfer functions. [MW] characterizes completely positive realizations and quotient representations. [Z] treats shared chronological root-word realization; [AZ] uses stationary continuous-time observed laws and entropy-production architecture cost. [BOS] treats long-run hypothesis-testing or estimation losses. None supplies both unweighted acquired $B,A$ flows, the original paid shared-depth exposure, and configuration-before-TV on this complete stopped future. These are bounded correspondence findings, not an exhaustive literature or global priority claim.

Exact rational checks verified the constants in (1.6), (5.5), (6.6), the polynomial factorization (5.6), the coordinate triangle identity including an infinite-outcome atom, and the coefficient in §7. Direct Fraction calculations checked (5.5) on the endpoint swap, a nonreversible three-cycle, and a nonreversible positive three-state circulation. An additional 512 seeded finite random-table probes, with p sizes 2–7 and suspended sizes 2–6, checked the operator inequality, joint score and complete-law comparison bounds using finite-word partitions with rigorous bounds on omitted residual refinement. Their return horizon was 16. They are falsifier checks, not the proof of arbitrary kernels, all shapes, countable priors or unbounded tails. The proof is the stationary operator calculation and complete-law couplings above. No finite failure is used as an impossibility argument.

All new proofs are ordinary mathematics. There is no Lean verification, independent review, kernel authority, physical sampler claim, global trained-network classification, resource-savings claim or completion of the continuing research goal. Abstract real tables are finite indexed stochastic rules only. For rational represented tables, the comparison products remain rational. A categorical row with integer denominator $q$ can be sampled by retaining $\lceil\log_2q\rceil$ fresh candidate bits, rejecting candidates at least $q$, and otherwise using its installed integer thresholds. The candidate buffer, bit cursor, row/program selectors and every service microstate are finite and charged in COMPLETE; retries reuse them without a persistent attempt counter. Fresh bits and retries still have charged work. Effective kernels at returned operation cuts are precisely the specified categorical rows, and internal service-state forecasts are the continuations of this same program. This supplies a finite description and finite memory, with unbounded possible work; it grants no exact-real oracle or physical exact-real sampler. Original Reads, installation, numerical description, program, retention, sampler workspace, random bits, synthesis, output, time, energy and physical resources remain distinct accounts. Arbitrarily long legal returns and rejection sampling preclude a finite worst-case total-work or output-length claim.

## 10. Sources

The stopped-source links below refer to the unchanged scientific supplier baseline; [LOCAL] refers to the current public comparison pin.

- **MOTION:** [Actual-return forecast motion](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_RETURN_FORECAST_MOTION.md), §§1–8.
- **ST:** [Randomized stopped-tail minimax](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md), §§1–3.
- **E1:** [Full E1 scope extension](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FULL_E1_SCOPE_EXTENSION.md), §2.
- **PH:** [Phase-coherent full-tail minimax](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md), §§2,14–20.
- **FOUR:** [Mixed-phase defect attainment](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MIXED_PHASE_DEFECT_ATTAINMENT.md), §§1–3.
- **SWITCH:** [Configuration-law switch attainment](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONFIGURATION_LAW_SWITCH_ATTAINMENT.md), §§1–6.
- **NATIVE:** [Native-mixture recurrence obstruction](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md), §§3–7.
- **CLIP:** [Risk-controlled emission moment feasibility](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md), §§2–5.
- **PAID:** [Effective paid-history certificates](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md), §§2,9–11.
- **MIXSEP:** [Uniform mixture separation](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_MIXTURE_SEPARATION.md), §§2–5.
- **KB:** [KBonacci self-calibrating boundaries](https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/KBONACCI_SELF_CALIBRATING_BOUNDARIES.md), §§16–21.
- **LOCAL:** [Local reconstruction and loop correction](https://github.com/the-omega-institute/trureturing/blob/4d48962cafb2e5cc7cab08fbf490acdcd654dce2/docs/develop/theory/AURIC_FIB_ATOM_LOCAL_RECONSTRUCTION_AND_LOOP_CORRECTION.md), complete §§1–6.
- **CK:** Taolue Chen and Stefan Kiefer, [On the Total Variation Distance of Labelled Markov Chains](https://arxiv.org/html/1405.2852v1), Theorem 7 and Corollary 8.
- **Z:** Yixin Zhao, [Exact Local Optimality Does Not Compose: The Complexity of Chronological Realization](https://arxiv.org/html/2609.19707v1), §2.
- **AZ:** Aznagulov, [Thermodynamic Realizability of Hidden Markov Processes: Attainment, Observable Certificates, and the Price of Architecture](https://arxiv.org/html/2609.14623v1), Theorem A and §§4–5.
- **TS:** Hamed Taghavian and Jens Sjölund, [Minimal positive Markov realizations](https://arxiv.org/html/2502.21102v3), §§III–V.
- **CJ:** Wojciech Czaja, Philippe Jaming and Máté Matolcsi, [An efficient algorithm for positive realizations](https://arxiv.org/html/math/0612551v2), §§2–4.
- **MW:** Alex Monràs and Andreas Winter, [Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem](https://arxiv.org/html/1412.3634v1), §§2,4,7.
- **BOS:** Tomer Berg, Or Ordentlich and Ofer Shayevitz, [Statistical Inference with Limited Memory: A Survey](https://arxiv.org/html/2312.15225v1), §§2.3,6.1,7.3; [Binary Hypothesis Testing with Deterministic Finite-Memory Decision Rules](https://arxiv.org/html/2005.07445v1), §§I–IV.

[MOTION]: https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_RETURN_FORECAST_MOTION.md
[ST]: https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md
[E1]: https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FULL_E1_SCOPE_EXTENSION.md
[PH]: https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md
[NATIVE]: https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md
[CLIP]: https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md
[PAID]: https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md
[MIXSEP]: https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_MIXTURE_SEPARATION.md
[KB]: https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/KBONACCI_SELF_CALIBRATING_BOUNDARIES.md

[FOUR]: https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MIXED_PHASE_DEFECT_ATTAINMENT.md
[SWITCH]: https://github.com/the-omega-institute/trureturing/blob/adcffe6be4e7cf9793d92a79bfbd5365557a7852/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONFIGURATION_LAW_SWITCH_ATTAINMENT.md

[LOCAL]: https://github.com/the-omega-institute/trureturing/blob/4d48962cafb2e5cc7cab08fbf490acdcd654dce2/docs/develop/theory/AURIC_FIB_ATOM_LOCAL_RECONSTRUCTION_AND_LOOP_CORRECTION.md

## 追加锚（本行以下为增补区）
