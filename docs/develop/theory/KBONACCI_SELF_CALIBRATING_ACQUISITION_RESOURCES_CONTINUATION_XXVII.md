# Self-calibrating acquisition resources XXVII: fixed-total common-product completion obstruction

## 394. Complete scores at literal affine mass

**Definition 394.1 (Inherited resources and complete catalogs).** Retain the original source, static prime replies, full Borel disjoint-union tape carrier, distinct marks $\theta_j$, consumer and original nonatomic targets of [IX 207.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md) and [110.1–110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source). The separately selected marked targets are

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}},
\qquad 1\ge a_1\ge a_2\ge\cdots>0,\qquad a_j\longrightarrow0.
\tag{394.1}
$$

The original classes $\mathcal N_2,\mathcal O_2$ use zero advice, one source-independent common seed and measurable sourcewise almost-sure finite handoff. The seed fixes the whole schedule and all terminal outputs before replies. Class $\mathcal N_2$ acquires its entire preselected schedule; $\mathcal O_2$ preselects increasing addresses and stops at its first queried zero or exhaustion. At most two actual requests are allowed, including repeated requests and replies later ignored. Original competitors have arbitrary addresses and full-carrier outputs. There is no source distribution, supplied source label, free observation, reset, copy, second seed, reply-adaptive next address or mean-request relaxation. All positive ordered vanishing tails and all closed cap ties are retained. Every finite Boolean word has actual source witnesses by the source interface in IX 207.1; auxiliary word weights below supply no law on those sources.

For finite $L\ge3$, put $B_L=\{0,1\}^L$, $J_L=\{0,\ldots,L\}$ and $n(w)=\min\{j:w_j=0\}$ for $w\ne1^L$. Use the complete finite catalogs of [XXIII 368.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXIII.md#368-original-resources-complete-cells-and-signed-scores): every empty schedule, singleton and distinct pair $i<j$, with pair cells $00,01,10,11$ for $N$ and $0,10,11$ for $O$. The stopped cell $0$ merges $00$ and $01$. Each table assigns any label in $J_L$ to each cell, including earlier and unqueried labels. Sorting a static pair permutes its table; a repeated coordinate has singleton information, without erasing any actual request charge.

A complete allocation has nonnegative cell vectors $U_{s,c}$ of a common owning mass $m_s$ within each schedule $s$, with $\sum_s m_s=M\ge0$. Its word vector is $p_w=\sum_s U_{s,c_s(w)}$, of mass $M$. At mass one, [109.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#109-an-exact-coefficient-criterion-with-one-common-probability-budget) supplies the common-table realization using one seed fixed before replies. All words, multiple zeros, zero-mass schedules and zero coordinates remain in these definitions.

**Definition 394.2 (Independent row weights, full scores and anchor).** Use the separately weighted event coordinates and literal affine convention of [XXIII 368.3–368.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXIII.md#368-original-resources-complete-cells-and-signed-scores). At a zero word the three coordinates are

$$
z_{A,w}(p)=p_w(0),\qquad z_{C,w}(p)=p_w(n(w)),\qquad
z_{P,w}(p)=p_w(0)+p_w(n(w)),
\qquad z_T(p)=p_{1^L}(0).
\tag{394.2}
$$

Thus there are $3(2^L-1)+1$ separately imposed rows, with independent score coefficients; this is not a claim of linear independence of the event functionals. For a profile $b$ and cap $e$, set

$$
d_{A,w}=1-b_{n(w)}-e,\qquad d_{C,w}=b_{n(w)}-e,\qquad
d_{P,w}=d_T=1-e.
\tag{394.3}
$$

Let $R=O(1,2;1,2,0)$ in stopped-cell order, $\alpha=(1,1,0,\ldots,0)$ and $r=z(R)=d(\alpha,0)$. At mass $M$ the convention is literally

$$
z(p)\ge d(b,e)+(M-1)r,
\qquad z(p)-Mr\ge d(b,e)-r.
\tag{394.4}
$$

No singleton demand is clipped to zero, no union row is deduced from the singleton rows, and no normalization by $M$ is made, including at $M=0$.

A full score $y=(A_w,C_w,P_w;T)\ge0$ has a coefficient at every row, including the rows whose coefficients are zero. Its reward is

$$
\begin{aligned}
g_y(w,\ell)&=A_w\mathbf1_{\ell=0}+C_w\mathbf1_{\ell=n(w)}
                 +P_w\mathbf1_{\ell\in\{0,n(w)\}}\quad(w\ne1^L),\\
g_y(1^L,\ell)&=T\mathbf1_{\ell=0}.
\end{aligned}
\tag{394.5}
$$

For each schedule, sum rewards within each of its complete cells, maximize over every $\ell\in J_L$ separately in that cell, then sum the maxima. Write $B_N(y),B_O(y)$ for the maxima over their entire catalogs. Set

$$
\begin{aligned}
W_y&=y\cdot r
 =\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
\Delta_{\mathcal C}(y)&=B_{\mathcal C}(y)-W_y\ge0
                       \quad(\mathcal C=N,O),\\
Q(y)&=(\beta,K),\qquad
\beta_j=\sum_{n(w)=j}(C_w-A_w),\qquad
K=\sum_w(A_w+C_w+P_w)+T.
\end{aligned}
\tag{394.6}
$$

The sums over $w$ range over all zero words. Completing a stopped table duplicates its first-cell label into $00,01$, so $B_O\le B_N$ and $\Delta_O\le\Delta_N$.

**Definition 394.3 (Signed hull charge and a common certificate).** Retain the hull and signed functional of [IX 207.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md):

$$
\begin{aligned}
H_L=\{(b,e):\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
 &(L+1)e\le\sum_{j=3}^L b_j,\quad
 b_1+\sum_{j=3}^L b_j-(L+1)e\le1\},\\
F_{(\beta,K)}(b,e)&=\sum_j\beta_j(b_j-\alpha_j)-Ke,\qquad
\sigma_{H_L}(q)=\max_{(b,e)\in H_L}F_q(b,e).
\end{aligned}
\tag{394.7}
$$

The argument $q$ can be signed; differences of quotients are never replaced by positive parts. A certificate for $q$ is one full $V\ge0$ and one $\theta\in[0,1]$ satisfying

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(q-Q(V))\le\theta.
\tag{394.8}
$$

The same $V$ and the same $\theta$ are selected before the hull point varies. Both endpoints and nonzero $V$ with $\Delta_N(V)=0$ are allowed. This is the inherited certificate of [VI 199.3–199.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md), with its full event system and literal anchor.

## 395. A family and its fixed-total product completions

**Definition 395.1 (The exchangeable input family).** Fix any finite integer $L\ge8$, and put

$$
m=L-2,\qquad k=\lfloor m/2\rfloor,\qquad
a=\frac{k+1}{2k+1},\qquad t=\frac{k}{2k+1}=1-a.
\tag{395.1}
$$

Here the scalar $a$ is an auxiliary parameter, distinct from the entire amplitude sequence in (394.1). On the $m$ late coordinates $I=\{3,\ldots,L\}$, define one probability $\rho$ by its zero set. If $m=2k+1$, the zero set is a uniformly chosen $(k+1)$-subset. If $m=2k$, mix a uniform $k$-subset with weight $a$ and a uniform $(k+1)$-subset with weight $t$. This is exactly $\rho=\mathcal L_m(a)/2$ from [IX 207.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md): its total-mass factor satisfies $c_ma=2$, and its two even-parity layer masses after division by two are $a,t$. The inherited simultaneous moments give, for every distinct $i,j\in I$,

$$
\rho(X_i=0)=a,\qquad \rho(X_i=X_j=0)=\frac a2,
\qquad
\bigl(\rho_{00},\rho_{01},\rho_{10},\rho_{11}\bigr)
 =\left(\frac a2,\frac a2,\frac a2,1-\frac{3a}{2}\right).
\tag{395.2}
$$

In both parities $k\ge3$, $1/2<a\le4/7$, $1/3<t<1/2$, and every displayed mass is nonnegative.

For $x\in\{0,1\}^I$, define the full score $y$ by

$$
P_{01x}=P_{10x}=\rho(x),\qquad
C_{1^{n-1}0^{L-n+1}}=1\quad(3\le n\le L),\qquad T=1.
\tag{395.3}
$$

All other coefficients are zero, with coincident coefficients added. In particular its individual first-zero row-type totals are

$$
\sum_{n(w)=j}A_w=0,\qquad
\sum_{n(w)=j}C_w=\mathbf1_{j\ge3},\qquad
\sum_{n(w)=j}P_w=\mathbf1_{j\le2},\qquad T=1.
\tag{395.4}
$$

Consequently $W_y=3$ and $Q(y)=q=(0,0,1,\ldots,1;\,m+3)$. Each late correct-row total is positive, including that of label $L$.

**Definition 395.2 (The precise shared-product class).** Choose arbitrary $h\in[0,1]$ and $p=(p_3,\ldots,p_L)\in[0,1]^m$. Let $f_j(0)=1-p_j$, $f_j(1)=p_j$, and let $\pi_p(x)=\prod_{j=3}^L f_j(x_j)$. The fixed-total common-product completion $z=z_{p,h}$ has

$$
\begin{aligned}
P_{00x}&=(1-h)\pi_p(x),&P_{01x}&=h\pi_p(x),&P_{10x}&=\pi_p(x),\\
C_{1^{n-1}0v}&=\prod_{j=n+1}^L f_j(v_j)\quad(3\le n\le L),&&&T&=1.
\end{aligned}
\tag{395.5}
$$

The empty product is one. Every $A$ and every other coefficient is zero. These scores retain each total in (395.4), hence $W_z=3$ and $Q(z)=q$. The free bias $h$ distributes the first class between early prefixes $00,01$; $h=1$ retains the input's $01/10$ split. Both early union classes have the same late product marginal, and every late correct class uses its suffix biases from that very same $p$. Independence only within separately chosen class-dependent laws is a different condition. All closed-cube endpoints and every zero coefficient in (395.5) are included.

## 396. The all-bias obstruction

**Theorem 396.1 (Strict budget overrun for every fixed-total shared-product completion).** For every finite $L\ge8$, Definitions 395.1–395.2 satisfy

$$
\Delta_O(y)=t,\qquad \Delta_N(y)=2t,\qquad
\sigma_{H_L}(Q(y))=\frac{m}{m+1}.
\tag{396.1}
$$

For every $h\in[0,1]$ and every $p\in[0,1]^m$, the full-catalog cost $D=\Delta_O(z_{p,h})$ obeys

$$
\Delta_N(z_{p,h})\ge D\ge r_m
 :=\frac{3(m-1)-\sqrt{(m-1)(m+7)}}{4(m-2)}>t.
\tag{396.2}
$$

Thus no $z_{p,h}/t$, with any $\theta\in[0,1]$, certifies $Q(y/t)$. Nevertheless the existing comparable-measure construction of [IX 209.7–209.8](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md) supplies a correlated full score $V$, with the same $P,T$ as $y$ and

$$
C^V_{1^{n-1}0v}
 =\frac{\rho\{X_n=0,\ X_{n+1..L}=v\}}{a}\quad(3\le n\le L),
\qquad A^V=0,
\tag{396.3}
$$

whose $W_V=3$, $Q(V)=q$ and $\Delta_N(V)=\Delta_O(V)=t$. In particular $(V/t,0)$ is one certificate for $Q(y/t)$.

The bound $r_m$ is necessary, with no assertion that it is attained or optimal. Strictness is for each finite $L$; no positive gap uniform in unbounded $L$ is asserted. The exclusion concerns exactly (395.5), not changed row-type totals even at the same $Q$, correlated or class-dependent suffix laws, general common Markov laws, mixtures of product completions, or unrestricted full $V$ with signed residual payment. The correlated score (396.3) is the IX 209.8 specialization below.

*Proof.* The subset measure in IX 207.4 gives (395.2) for the one full $\rho$ in both parity cases; no separately realizable pair marginals are substituted for it. The base rewards of $y$ at a late pair $i<j$ are $(a,a,a,3t)$, including $T$ in $11$. An absorbing correct word with index $n\le i$ lies in $00$, one with $i<n\le j$ lies in $10$, and one with $n>j$ lies in $11$. Each such label has reward one in that cell, and no late correct label contributes in $01$. Each early label earns half the corresponding union base reward. Since $2a>1$ and $3t>1$, the complete cell maxima are as follows; tuples are in their catalog's cell order.

| Schedule | $N$ cell maxima | $O$ cell maxima |
| --- | --- | --- |
| Empty | $(3)$ | $(3)$ |
| Singleton $1$ or $2$ | $(1,2)$ | $(1,2)$ |
| Singleton $i\in I$ | $(2a,1+2t)$ | $(2a,1+2t)$ |
| Head pair $(1,2)$ | $(0,1,1,1)$ | $(1,1,1)$ |
| Early/late pair $(b,i)$, $b\in\{1,2\}$, $i\in I$ | $(a,t,1,1+t)$ | $(1,1,1+t)$ |
| Late pair $(i,j)$ | $(1,a,1,3t)$ | $(2a,1,3t)$ |

For an early/late pair, the split early-zero rewards sum to one. In $10$, label $i$ has reward one and every other candidate has reward at most one; in $11$, the base reward $1+t$ dominates all late correct labels. For a late singleton, the zero-branch base $2a$ dominates every earlier correct label, and the one-branch base $1+2t$ dominates every future label. The head and empty readings follow from the two early union masses and $T$. Thus the table checks all labels, including earlier and unqueried labels, on all schedule types. It uses the full score on every word, rather than a single-zero restriction. The late $N$ pair has support $3+2t$, every late $O$ pair has support $3+t$, and early/late pairs also have support $3+t$. All shorter schedules and the head have support three. Hence $B_N(y)=3+2t$ and $B_O(y)=3+t$; for example $O(i,j;0,j,0)$ and $O(1,i;1,i,0)$ attain the stopped maximum.

For the hull reading, apply the vertex description already supplied by IX 207.3. Besides $o=0$ and $p=(1,0,\ldots,0;0)$, its vertices are $u_r$, with the first $r$ amplitudes $1/(r-1)$ and all remaining coordinates zero, and $v_r$, with the first $r$ amplitudes one and all remaining coordinates, including $e$, equal to $(r-2)/(r+1)$, for $3\le r\le L$. Direct substitution of this $q$ gives

$$
\begin{aligned}
F_q(o)&=F_q(p)=0,\qquad F_q(u_r)=\frac{r-2}{r-1},\\
F_q(v_r)&=(r-2)+(L-r)\frac{r-2}{r+1}
                   -(L+1)\frac{r-2}{r+1}=0.
\end{aligned}
\tag{396.4}
$$

The largest value is $(L-2)/(L-1)=m/(m+1)$. This proves (396.1) using every vertex family and the inherited signed functional. In particular the normalized input itself has $N$ excess two, while choosing the zero score leaves hull charge $m/((m+1)t)>1$.

Fix now one entire product score $z=z_{p,h}$ and its one full-catalog $D$. On stopped schedule $(1,i)$ the first-cell maximum is one, regardless of $h$: it contains the whole first union class. In $10$, correct label $i$ contributes one; earlier late correct labels contribute $1-p_i$, the second early label contributes $1-p_i$, and every other label contributes at most one. In $11$, the base reward is $1+p_i$, dominating every correct label. Its support is therefore exactly $3+p_i$, so

$$
D\ge p_i\qquad(i\in I).
\tag{396.5}
$$

For every late stopped pair $i<j$, the exact three maxima are

$$
\max\{2(1-p_i),1\},\qquad
\max\{2p_i(1-p_j),1\},\qquad 1+2p_ip_j.
\tag{396.6}
$$

Indeed the first cell contains the entire correct class $i$; earlier late labels have mass at most one, and each early label is bounded by its union base reward. In $10$, the whole class $j$ contributes one; intermediate classes contribute $1-p_j$, earlier classes contribute $p_i(1-p_j)$, and neither exceeds one. In $11$, future classes contribute at most one, intermediate classes at most $p_j$ and earlier classes at most $p_ip_j$; all are dominated by the displayed base reward. Summing (396.6) and subtracting $W_z=3$ yields the simultaneous necessary inequalities

$$
D\ge(2p_i-1)_++(1-2p_i+2p_ip_j)_+
\qquad(3\le i<j\le L),
\tag{396.7}
$$

where $u_+=\max\{u,0\}$. These are readings of the same score and biases as (396.5). Every remaining schedule is still included in $D$ and can only strengthen these lower bounds. Equality of complete $N/O$ support for the common Markov family, including these independent suffixes, is already [VI 198.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md); it is not an upper bound by the input's old cost $t$.

Define

$$
g_m(u)=2(m-2)u^2-3(m-1)u+(m-1).
\tag{396.8}
$$

On $[0,1/2]$ it is strictly decreasing, since $g_m'(u)\le-m-1<0$, while $g_m(0)=m-1>0$ and $g_m(1/2)=-1/2$. Its unique root in this interval is the $r_m$ in (396.2), so $0<r_m<1/2$. If $D\ge1/2$, then already $D>r_m$. If $D=0$, (396.5) forces all $p_i=0$, contradicting (396.7) for any adjacent late pair.

It remains to consider $0<D<1/2$. By (396.5), $0\le p_i\le D$. In (396.7) the first positive part vanishes and the second argument is positive. Thus every adjacent pair forces

$$
p_i(1-p_{i+1})\ge c_D:=\frac{1-D}{2}>0
\qquad(3\le i<L).
\tag{396.9}
$$

In particular each $p_i$ used below as a denominator is positive. On $(0,D]$, the function $u-1+c_D/u$ decreases, because $c_D>1/4>D^2$. Consequently

$$
\begin{aligned}
p_i-p_{i+1}
&\ge p_i-1+\frac{c_D}{p_i}
 \ge D-1+\frac{c_D}{D}
 =d(D):=\frac{(1-D)(1-2D)}{2D}>0,\\
D&\ge p_3-p_L\ge(m-1)d(D).
\end{aligned}
\tag{396.10}
$$

The second line uses $p_3\le D$ and $p_L\ge0$. Multiplying it by $2D$ gives $g_m(D)\le0$, hence $D\ge r_m$.

To compare with the correlated benchmark, use $m\ge2k$ and compute

$$
\begin{aligned}
d(t)&=\frac{k+1}{2k(2k+1)},\\
t-(m-1)d(t)&\le t-(2k-1)d(t)
 =\frac{1-k}{2k(2k+1)}<0.
\end{aligned}
\tag{396.11}
$$

Therefore $g_m(t)=2t((m-1)d(t)-t)>0$, and the strict decrease of $g_m$ gives $t<r_m$. This proves (396.2) for both $m=2k$ and $m=2k+1$. A zero bias used in (396.9) would violate that inequality before division; a bias equal to one gives $D\ge1$ in (396.5). The last bias may be zero without being divided by, and both endpoints of $h$ were included in the support readings. Thus no boundary point of the closed bias cube has been removed.

For the surviving payer, apply IX 209.7–209.8 directly. Take $\nu=2\rho$, of mass $S=2$, early correct totals $c_1=c_2=0$, terminal mass one, late totals $\eta_n=1$, and whole-cube measures

$$
\mu_n=\frac{\rho|_{\{X_n=0\}}}{a}
      =\frac{\nu_n}{2a}\le\nu_n\le\nu.
\tag{396.12}
$$

Each $\mu_n$ has mass one and is comparable to $\nu_n$ as a measure, not merely in total mass. Resetting coordinates before $n$ to one and coordinate $n$ to zero is precisely the map $R_n$ in that theorem; its pushforward gives (396.3). The proportional early rows give $P_{01x}=P_{10x}=\nu(x)/2=\rho(x)$, as required. For every $n<j$ in $I$, (395.2) gives $\mu_n\{X_j=0\}=1/2$. Thus, in the notation of IX (209.13)–(209.14),

$$
\begin{gathered}
m_j=2a,\quad d_{ij}=a,\quad h_{ij}=2-3a,\quad
H=p_1=p_2=p_*=1,\\
U_j=U_{ij}=1,\qquad 0\le Z_j,Z_{ij}\le1,\\
D_j=\max\{a,1\}+\max\{2t,1+t,Z_j\}-2=t,\\
D_{ij}=(1-2a)_++(1-a)_++(Z_{ij}-3t)_+=t.
\end{gathered}
\tag{396.13}
$$

The last line uses $3t>1$. The other terms in IX (209.14) are zero, so that existing theorem gives the exact complete costs $\Delta_N(V)=\Delta_O(V)=t$. The unchanged individual totals give $Q(V)=q$ and $W_V=3$. The full-catalog cost conclusion is therefore the stated application of IX 209.8. The auxiliary conditioning in (396.12) changes score weights only; it is no conditioning of an acquisition on a free source observation.

Finally, positive homogeneity gives

$$
\Delta_O(y/t)=1,\qquad
\Delta_N(V/t)+0=1,\qquad
\sigma_{H_L}(Q(y/t)-Q(V/t))=0.
\tag{396.14}
$$

For every product completion, $\Delta_N(z_{p,h}/t)\ge r_m/t>1$, so adding any nonnegative $\theta$ cannot pay (394.8), even though its residual quotient is zero. This is a restriction on completion at fixed totals, whereas (396.14) is an unrestricted certificate for this family. $\square$

## 397. The unrestricted comparison and its original alternative

**Definition 397.1 (The full comparison assertion).** With the inherited objects of Definitions 394.1–394.3, the comparison assertion remains exactly [XXVI 393.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXVI.md#393-the-simultaneous-replacement-still-required):

$$
\begin{gathered}
\forall L\ge8\ \forall y\ge0\text{ full with }\Delta_O(y)=1,
\quad\exists V\ge0\text{ full}\ \exists\theta\in[0,1]:\\
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(Q(y)-Q(V))\le\theta.
\end{gathered}
\tag{397.1}
$$

No fixed class totals, shared product or Markov law, fixed complementary allocation, named score basis, first-zero-invariant output law or zero residual is required here. All zero-$Q$ gauge directions, signed residuals, both endpoints of $\theta$ and nonzero zero-$N$-excess scores are permitted, with the same entire $V$ and the same $\theta$ in both inequalities. Theorem 396.1 concerns a restricted completion map; its correlated certificate neither proves (397.1) for other full scores nor refutes it.

The original strict-separation alternative has the quantifiers of XXVI 393.1: one entire positive nonincreasing vanishing sequence in (394.1), one complete original common-seed $A_N\in\mathcal N_2$ attaining $c_0=e_a(A_N)$, and some $\varepsilon>0$ such that every original $A_O\in\mathcal O_2$ satisfies $e_a(A_O)\ge c_0+\varepsilon$, where $e_a$ is the supremum of total variation error over all actual sources and measurable events. Every source, arbitrary query address, full-carrier output and closed tail tie remains in that assertion. The auxiliary scores in Theorem 396.1 are not cap-feasible probability kernels or original error attainers, and supply no such separation. The original nonatomic-target and complete paid-$M1$ assertions retain their own target and resource conditions; neither is identified with the fixed-total score completion problem.

## 追加锚（本行以下为增补区）
