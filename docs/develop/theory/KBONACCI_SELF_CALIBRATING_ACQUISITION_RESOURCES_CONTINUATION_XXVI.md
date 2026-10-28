# Self-calibrating acquisition resources XXVI: whole-stock mass saturation and first-zero averaging cost

## 390. Joint stocks and the removable anchor

**Definition 390.1 (Complete affine allocations and their stock projection).** Fix a finite integer $L\ge3$, a catalog $\mathcal C\in\{N,O\}$, a real prefix $b_1,\ldots,b_{L-1}\in[0,1]$ and $e\ge0$. Use the complete schedules, cell maps $c_s(w)$, owning masses and literal affine demands of [XXV 384.1–384.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXV.md#384-complete-allocations-at-literal-affine-mass). Thus every schedule is empty, a singleton, or a pair $i<j$; its nonnegative cell vectors all have the same mass $m_s$, and $\sum_s m_s=M\ge0$. Pair cells are $00,01,10,11$ for $N$ and $0,10,11$ for $O$. All addresses $1,\ldots,L$, all output labels, and every Boolean word, including every multiple-zero word, remain in the catalog.

Write $B_L=\{0,1\}^L$, $J_L=\{0,\ldots,L\}$, $w^*=1^{L-1}0$, $w^+=1^L$ and $c_s^*=c_s(w^*)$. The collapsed set $K_{\mathcal C}(M)$ consists of complete allocations $k$ on labels $0,\ldots,L-1$ satisfying, at every word with first zero $n<L$, the three independent floors

$$
\begin{array}{c|cc}
 &d_A(w)&d_C(w)\\ \hline
n\le2&1-b_n-e&M-1+b_n-e\\
3\le n<L&M-b_n-e&b_n-e
\end{array}
\qquad d_P(w)=M-e,
\tag{390.1}
$$

and the two base floors $k_{w^*}(0),k_{w^+}(0)\ge M-e$. Here $k_w=\sum_s k_{s,c_s(w)}$. The singleton floors are signed; none is replaced by its positive part. Every cell and owning mass varies in $K_{\mathcal C}(M)$.

For one such allocation define

$$
\begin{aligned}
a_s(k)&=k_{s,c_s^*}(0),& I_s(w)&=\mathbf1_{c_s(w)=c_s^*},\\
s_w(k)&=\min\{k_w(0)-d_A(w),\ k_w(0)+k_w(n(w))-d_P(w)\}
&& (n(w)<L),\\
s_+(k)&=k_{w^+}(0)-(M-e).
\end{aligned}
\tag{390.2}
$$

Let $\mathcal J_{\mathcal C}(M)$ be the joint pairs $(k,x)$ with $k\in K_{\mathcal C}(M)$ and

$$
0\le x_s\le a_s(k),\qquad
\sum_s I_s(w)x_s\le s_w(k)\quad(n(w)<L),\qquad
\sum_s I_s(w^+)x_s\le s_+(k).
\tag{390.3}
$$

The entire stock projection and its capacity are

$$
\mathcal X_{\mathcal C}(M)
=\{x:\exists k\ (k,x)\in\mathcal J_{\mathcal C}(M)\},
\qquad
\nu_{\mathcal C}(M)=\max_{x\in\mathcal X_{\mathcal C}(M)}\sum_s x_s.
\tag{390.4}
$$

The maximum is attained when the set is nonempty, by [XXV 385.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXV.md#385-whole-allocation-capacity-and-the-hull-slice). If $K_{\mathcal C}(M)$ is empty, both joint sets are empty and $\nu_{\mathcal C}(M)=-\infty$. Conversely $x=0$ is admissible whenever $K_{\mathcal C}(M)$ is nonempty. A zero capacity and an empty complementary set are different cases.

**Definition 390.2 (Reserved stock and anchor depletion).** For $(k,x)\in\mathcal J_{\mathcal C}(M)$, form cell vectors $U$ on labels $0,\ldots,L$ by moving $x_s$ from label $0$ to label $L$ in $c_s^*$, leaving every other entry unchanged. This is one complete allocation with the same owning masses. The inequalities (390.3) pay its earlier base, union and positive-base losses; earlier correct coordinates are unchanged. No final-label demand is imposed in this definition.

Let $R=O(1,2;1,2,0)$, in stopped-cell order, be the same anchor as in XXV 384.1. In the $N$ catalog its labels in cells $00,01,10,11$ are $1,1,2,0$. Since $L\ge3$, the distinguished cell of schedule $(1,2)$ is $11$. Put

$$
\tau_{\mathcal C}(k,x)=
\begin{cases}
\min\{k_{12,00}(1),\ k_{12,01}(1),\ k_{12,10}(2),\ k_{12,11}(0)-x_{12}\},&\mathcal C=N,\\
\min\{k_{12,0}(1),\ k_{12,10}(2),\ k_{12,11}(0)-x_{12}\},&\mathcal C=O.
\end{cases}
\tag{390.5}
$$

Every term is nonnegative. A joint allocation is depleted when $\tau_{\mathcal C}(k,x)=0$. In lifted coordinates this means that at least one of the displayed anchor-label entries of $U$ is zero. In particular the last entry is the available base after reserving $x_{12}$, rather than the whole collapsed base entry.

## 391. Entire-stock saturation and the bounded mass comparison

**Theorem 391.1 (Stock-preserving anchor extraction).** Under Definition 390.1 set

$$
B=2-b_1-b_2+3e\ge0.
\tag{391.1}
$$

For every finite real $M\ge0$,

$$
\mathcal X_{\mathcal C}(M)
=\mathcal X_{\mathcal C}(\min\{M,B\}),\qquad
\nu_{\mathcal C}(M)=\nu_{\mathcal C}(\min\{M,B\}).
\tag{391.2}
$$

More precisely, every joint pair $(k,x)$ admits subtraction of $\tau=\tau_{\mathcal C}(k,x)$ units of $R$ from schedule $(1,2)$, with the identical stock vector $x$. The resulting joint allocation is depleted, has mass $m=M-\tau\in[0,B]$, and has the same individual earlier base and union slacks and positive slack. No ordering of the prefix or equality $b_2=b_3$ is needed for this theorem.

*Proof.* For any $t\in[0,\tau]$, subtract $t$ from each anchor-label entry of schedule $(1,2)$ and decrease its owning mass by $t$. All its cells then have the same nonnegative mass $m_{12}-t$; other schedules are unchanged. The reservation in (390.5) gives

$$
k'_{12,11}(0)=k_{12,11}(0)-t\ge x_{12}.
\tag{391.3}
$$

All other distinguished stocks retain their old upper bounds. Thus the same $x_s$, separately for every schedule, remains available.

At first zeros $1,2$, the anchor has correct label $n$. Its subtraction leaves base and its floor fixed, and decreases the correct coordinate and its affine floor by $t$. At later first zeros the anchor has label $0$, so base and its affine floor decrease by $t$, while the correct coordinate and its floor stay fixed. Every independent union coordinate and its floor decrease by $t$. The collapsed base coordinates at $w^*,w^+$ and both of their floors also decrease by $t$. Consequently $k'\in K_{\mathcal C}(M-t)$ and

$$
s_w(k')=s_w(k),\qquad s_+(k')=s_+(k).
\tag{391.4}
$$

The incidences and stock losses in (390.3) are unchanged. Hence $(k',x)\in\mathcal J_{\mathcal C}(M-t)$. This checks the separate signed floors, rather than only their sum.

Take $t=\tau$, write $m=M-\tau$, and lift $k'$ using the same $x$ to obtain $U'$ and word laws $p'$. One of the tested anchor entries of $U'$ is zero. For $N$, choose $a\in\{0,1\}$ to match that cell if it is $00$ or $01$; if it is $10$ or $11$, choose either value. For $O$ choose $a=0$. Consider

$$
u=0a1^{L-2},\qquad v=101^{L-2},\qquad z=1^L,
\tag{391.5}
$$

with desired labels respectively $1,2,0$. Schedule $(1,2)$ contributes at most $2m'_{12}$ to the sum of these three desired coordinates: the three visited cells are distinct and at least one tested desired entry is zero.

Every other schedule observes at most one of coordinates $1,2$. All coordinates after $2$ are one on all three words, so such a schedule visits at most two terminal cells on this triple. Within any one cell the desired labels of the words assigned to it are distinct. Their entries sum to at most that cell's owning mass. Thus the contribution of any other schedule is at most $2m_s$. Summing over this one complete allocation gives

$$
p'_u(1)+p'_v(2)+p'_z(0)\le2m.
\tag{391.6}
$$

The earlier correct floors and the paid positive floor of the lifted joint allocation give

$$
p'_u(1)\ge m-1+b_1-e,\quad
p'_v(2)\ge m-1+b_2-e,\quad
p'_z(0)\ge m-e.
\tag{391.7}
$$

Adding these literal inequalities, including any negative floors, proves

$$
3m-2+b_1+b_2-3e\le2m,
\qquad m\le B.
\tag{391.8}
$$

This establishes the asserted depleted construction. In particular, if $M\ge B$, then $\tau\ge M-B$; subtracting just $M-B$ units instead produces mass exactly $B$ with every coordinate of $x$ unchanged. Conversely, adding any nonnegative multiple of the same anchor raises mass, leaves all slacks in (390.3) fixed and does not consume stock. Hence every stock vector feasible at $B$ is feasible at any $M\ge B$. For $M\le B$ (391.2) is the identity.

Because a nonempty complementary set admits zero stock, equality of the stock projections also preserves emptiness. Taking the attained maxima proves the capacity equality with the $-\infty$ convention. At $M=0$ every nonnegative cell and every stock is zero; the joint set is either empty or consists of that zero allocation and stock. The proof divides neither masses nor floors by $M$. $\square$

**Corollary 391.2 (Exact bounded mass domain on the hull).** Let $L\ge4$, fix

$$
1\ge b_1\ge\cdots\ge b_{L-1}\ge e\ge0,\qquad b_2=b_3,
$$

and set

$$
S=\sum_{j=3}^{L-1}b_j,\qquad
\ell=\max\{0,Le-S\},\qquad
u=\min\{b_{L-1}-e,\ 1-b_1-S+Le\}.
\tag{391.9}
$$

Assume $\ell\le u$. The following two assertions are equivalent: for every finite $M\ge1$, or just for every real $1\le M\le\max\{1,B\}$, respectively,

$$
\nu_N(M)\ge\ell\quad\Longrightarrow\quad
\nu_O(M)\ge\min\{\nu_N(M),u\}.
\tag{391.10}
$$

Moreover

$$
B\le C_L:=\max\left\{2,\frac{3(L-2)}{L+1}\right\}<3.
\tag{391.11}
$$

Thus the uniform interval $[1,C_L]$ is also equivalent to the full mass domain; at $L=8$ it is $[1,2]$. These are reductions of the quantified comparison, with no assertion that (391.10) holds.

*Proof.* By [XXV 385.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXV.md#385-whole-allocation-capacity-and-the-hull-slice), the nonempty interval $[\ell,u]$ is exactly the set of demands $\delta=b_L-e$ completing the prefix to $H_L$. Choose any such completion. Its order and lower hull inequality imply

$$
(L+1)e\le\sum_{j=3}^L b_j\le(L-2)b_2.
$$

Since $b_1\ge b_2$ and $b_2\in[0,1]$,

$$
B\le2-2b_2+\frac{3(L-2)}{L+1}b_2
\le\max\left\{2,\frac{3(L-2)}{L+1}\right\}<3.
$$

The bound is independent of the chosen completion. If $M>\max\{1,B\}$, Theorem 391.1 identifies each catalog's capacity at $M$ with its capacity at $\max\{1,B\}$. Thus (391.10) at this endpoint is exactly (391.10) at $M$, including empty capacities and the zero threshold. The remaining masses stay quantified. The reverse implication follows by restriction; (391.11) then gives the uniform interval.

The assumed nonempty hull prefix is essential to this bound; an empty interval has no demands to transfer. At $L=3$ Theorem 391.1 still holds, but a hull slice must additionally impose $\delta=b_2-e$. A depleted allocation can have mass below one: that is why the interval endpoint is $\max\{1,B\}$, and no same-mass transfer below one is asserted. $\square$

## 392. First-zero averaging and exact hard query cost

**Definition 392.1 (Class-constant averaging and finite hard cost).** For a finite $L\ge3$, put $\Omega_n=\{w\in\{0,1\}^L:n(w)=n\}$ and choose arbitrary probability weights $\pi_n$ on each $\Omega_n$. For a vector law $p$ define

$$
v_n=\sum_{w\in\Omega_n}\pi_n(w)p_w,\qquad
v_{L+1}=p_{1^L},\qquad
(\Pi p)_w=v_{n(w)},\quad (\Pi p)_{1^L}=v_{L+1}.
\tag{392.1}
$$

The weights for a class are the same for every output word in that class. This operator does not include arbitrary row-dependent stochastic maps that retain within-class variation. It is an auxiliary average of word laws, with no law on actual sources or free acquisition operation supplied.

For a probability-vector kernel $q$ on the full cube, let $D_{\mathrm{hard}}(q)$ be its minimum exact classical hard query cost. A procedure has one source-independent seed fixing a deterministic decision tree, uses only replies at coordinates in $[L]$, and outputs a label in $J_L$; the cost is the maximum number of actual requests on a supported tree path. Repeated and ignored requests count. Adaptive trees are allowed in this definition, so its lower bounds also apply to preselected or increasing first-zero-stop procedures at the same hard cost. The input domain is the entire Boolean cube.

**Theorem 392.2 (Weight-independent cost inflation).** Every operator (392.1) preserves all the literal affine base, correct, independent union and positive floors at a fixed $(b,e,M)$ whenever its input law satisfies them. Nevertheless the one-request stopped law

$$
p_w=(1-w_L)e_L+w_Le_0
\tag{392.2}
$$

satisfies, for every choice of these weights,

$$
\deg(\Pi p)=L,\qquad D_{\mathrm{hard}}(\Pi p)=L.
\tag{392.3}
$$

In particular $\Pi$ need not preserve either complete hard-two catalog, for any $L\ge3$.

*Proof.* On a first-zero class each demanded coordinate and its floor are fixed linear functionals of the word law. Averaging the inequalities preserves the separate base and correct floors, even if negative, and the independently imposed union floor. The positive class is unchanged. This proves row preservation at literal mass, without constructing common owning masses for the averaged law.

The first-zero expansion is the reused identity [XV (266.8)](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XV.md):

$$
q(w)=v_1+\sum_{k=1}^L(v_{k+1}-v_k)\prod_{i=1}^k w_i
\quad\text{when }q=\Pi p.
\tag{392.4}
$$

It telescopes on each first-zero word and at the positive word. In (392.2), the last zero class and the positive class are singletons, so $v_L=e_L$ and $v_{L+1}=e_0$. The top coefficient in (392.4) is consequently $e_0-e_L\ne0$, independently of every other weight. Thus the degree is exactly $L$.

Use the standard hard decision-tree degree bound, in its scalar expectation form from Kaniewski, Lee and de Wolf, [*Query complexity in expectation*, arXiv:1411.7280v1, Definition 8 and the lower-bound direction of Theorem 9](https://arxiv.org/html/1411.7280v1). Apply it to the indicator of output label $L$, whose expectation is the corresponding law coordinate. A deterministic path of at most $d$ actual requests has a leaf indicator that is a product of at most $d$ literals; repeated static literals reduce degree. Summing leaf indicators and averaging over the common seed gives ordinary multilinear degree at most $d$. The nonzero degree-$L$ coordinate therefore forces cost at least $L$. This uses a worst-path bound, rather than an expected number of requests or the scalar theorem's output-rescaling construction.

For the matching upper bound, query the increasing schedule $1,\ldots,L$ until its first queried zero or exhaustion. One uniform seed fixes, before replies, a label partition for each of the $L+1$ terminal classes with marginal vector $v_n$. On reaching a class use its fixed partition of that same seed. This realizes the whole law with at most $L$ actual requests. Hence the cost is exactly $L$.

The expansion and degree-two invariant subclass are already contained in XV 266.3, and XV 266.4 supplies a uniform-averaging cubic example at $L=3$. Here the single-query input and its forced endpoint difference give the exact cost for every horizon and every class weighting. The claim concerns the finite Boolean query contract; it is not an exact-law lower bound for original algorithms with arbitrary higher addresses. $\square$

**Proposition 392.3 (An original cap-feasible stopped input at every horizon).** Fix any integer $L\ge8$, set

$$
e=\frac25,\qquad \eta=\frac1{10(L-3)},\qquad
a_1=a_2=a_3=1,\qquad a_4=\cdots=a_L=e+\eta,
\tag{392.5}
$$

and append any entire positive nonincreasing vanishing tail with $a_{L+1}\le e$. There is one complete original $A\in\mathcal O_2$ with $e_a(A)=e$ such that, for its finite low-word law $p$, every class-constant average satisfies

$$
\deg(\Pi p)=D_{\mathrm{hard}}(\Pi p)=L.
\tag{392.6}
$$

Thus the averaging obstruction occurs on actual cap-feasible stopped input laws, with every multiple-zero word and closed tail tie included.

*Proof.* With one uniform seed choose each of

$$
O(1,2;1,2,0),\quad O(1,3;1,3,0),\quad O(2,3;2,3,0)
$$

with mass $3/10$, and each singleton $(j;j,0)$, $4\le j\le L$, with mass $\eta$. The pair labels are in cell order $0,10,11$, and singleton labels in reply order $0,1$. Their owning masses sum to $9/10+(L-3)\eta=1$. The common seed selects the entire deterministic table before replies. Execute its actual prime requests, stop at the first queried zero, and hand off the corresponding original mark $\theta_j$ to the unchanged consumer. This is the inherited common-seed realization of [108–110](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#108-common-probability-vector-kernels-and-stopped-schedules), with zero advice, finite handoff and at most two actual requests.

If the first zero is $n\le3$, the two early pairs containing $n$ both output $n$, and no other schedule does. Thus $p_w(n)=3/5$ and the TV distance to $e_n$ is exactly $2/5$, irrespective of all suffix bits.

If $4\le n\le L$, all early pairs output base, singleton $n$ contributes $\eta$ at $n$, and later zero singletons contribute wrong-label mass $z$ with

$$
0\le z\le(L-n)\eta\le\frac1{10}-\eta,\qquad
p_w(0)=1-\eta-z,
\quad p_w(n)=\eta.
$$

For the target $(1-e-\eta)e_0+(e+\eta)e_n$, the base, correct and union deficits are respectively

$$
z-e,\qquad e,\qquad z.
\tag{392.7}
$$

Their maximum is $e$. This verifies all three independent rows on every suffix, not only on single-zero words. At $1^L$ every schedule outputs base. At every actual first absence $n(x)>L$, the same low transcript therefore emits $\theta_0$ and has error $a_{n(x)}\le e$. Every finite word has an actual source witness, so the attained early-fiber error proves $e_a(A)=e$.

Finally

$$
p_{w^*}=(1-\eta)e_0+\eta e_L,\qquad p_{w^+}=e_0.
\tag{392.8}
$$

These singleton classes are unchanged by any averaging weights. Formula (392.4) has label-$L$ top coefficient $-\eta$, proving degree $L$; the hard-cost argument and terminal-class sampler of Theorem 392.2 give the matching exact cost. For example $a_{L+r}=2/(5r)$ supplies an entire permitted tail with the closed tie $a_{L+1}=e$.

The prefix/cap in (392.5) is not in $H_L$: the lower hull difference is

$$
(L+1)e-\sum_{j=3}^L a_j=\frac12>0.
$$

The constructed input is already stopped, so this is a failure of a proposed law transformation, not a separation from all stopped competitors. Its original realization uses the stated finite schedule; the lower bound in (392.6) remains a finite-contract statement. $\square$

## 393. The simultaneous replacement still required

**Definition 393.1 (The unchanged unrestricted comparison).** Retain the full nonnegative scores, anchor excesses $\Delta_N,\Delta_O$, quotient $Q$ and signed support $\sigma_{H_L}$ of [XXIII 368.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXIII.md#368-original-resources-complete-cells-and-signed-scores) and [XXV 389.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXV.md#389-the-unrestricted-assertion). The unresolved assertion is

$$
\begin{gathered}
\forall L\ge8\ \forall y\ge0\text{ full with }\Delta_O(y)=1,
\quad\exists V\ge0\text{ full}\ \exists\theta\in[0,1]:\\
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(Q(y)-Q(V))\le\theta.
\end{gathered}
\tag{393.1}
$$

The same unrestricted $V$ and the same $\theta$ pay both inequalities before the hull point varies. Both endpoints, signed residuals and nonzero zero-$N$-excess $V$ are allowed. No fixed complementary allocation, fixed stock vector, named score basis or first-zero-invariant output restriction is imposed.

Its alternative is one entire positive nonincreasing vanishing profile $a$, one complete original common-seed $A_N\in\mathcal N_2$ attaining $c_0=e_a(A_N)$, and $\varepsilon>0$ such that every original $A_O\in\mathcal O_2$ has $e_a(A_O)\ge c_0+\varepsilon$. Original competitors have arbitrary addresses and full-carrier outputs; repeated and ignored actual requests count, $N$ preselects the whole schedule, and $O$ stops at its first queried zero in its preselected increasing schedule. All original sources, labels and positive ordered vanishing tails with closed ties remain in scope. The original nonatomic-target and complete paid-$M1$ tasks retain their separate target and resource conditions.

**Definition 393.2 (Depleted-anchor replacement and a common price test).** For every $L\ge8$, every prefix/cap of Corollary 391.2 with $\ell\le u$, and every depleted $(k,x)\in\mathcal J_N(m)$ with

$$
0\le m\le B,\qquad \delta:=\sum_s x_s\in[\ell,u],
\tag{393.2}
$$

the required replacement lemma asks for one entire $(\widetilde k,\widetilde x)\in\mathcal J_O(\max\{1,m\})$ with $\sum_s\widetilde x_s\ge\delta$. The entire complementary allocation and every stock coordinate may change. The four depleted $N$ faces are precisely the vanishing of at least one entry in the first case of (390.5).

An equivalent fixed-complement test for this requested output uses prices on the earlier-word and positive stock constraints. Let $\mathcal W=\{w:n(w)<L\}\cup\{w^+\}$, with $s_{w^+}=s_+$, and for one $\widetilde k\in K_O(\max\{1,m\})$ put

$$
\Phi(\widetilde k,\lambda)
=\sum_{w\in\mathcal W}\lambda_w s_w(\widetilde k)
 +\sum_s a_s(\widetilde k)
   \left(1-\sum_{w\in\mathcal W}\lambda_w I_s(w)\right)_+,
\qquad\lambda\ge0.
\tag{393.3}
$$

The price form of the missing lemma requires the same nonempty complement before all prices:

$$
\exists\widetilde k\in K_O(\max\{1,m\})\quad
\forall\lambda\ge0:\ \Phi(\widetilde k,\lambda)\ge\delta.
\tag{393.4}
$$

For fixed $\widetilde k$, finite linear-programming duality gives $\operatorname{cap}(\widetilde k)=\min_{\lambda\ge0}\Phi(\widetilde k,\lambda)$. Indeed the packing has constraints $Ix\le s$, $x\le a$, $-x\le0$ and is nonempty and compact. Its dual has $I^{\mathsf T}\lambda+\mu\ge\mathbf1$ and objective $\lambda\cdot s+\mu\cdot a$; minimizing over $\mu\ge0$ gives (393.3). The valid-inequality alternative in Kaibel, [*Basic Polyhedral Theory*, arXiv:1001.2161v1, Theorem 12](https://arxiv.org/html/1001.2161v1), supplies equality and attainment. This standard duality is only the fixed-complement test: (393.4) still requires selection of one whole complement, including when $\delta=0$. Choosing a different complement for each price is not the asserted lemma.

**Proposition 393.3 (Exact remaining scope of the replacement lemma).** The universally quantified replacement statement in Definition 393.2 is equivalent to (391.10) for every required prefix/cap and every finite $M\ge1$, and hence, through the inherited [VI 199.3–199.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md) and XXV 385.2 bridge, to (393.1). Theorem 391.1 and the averaging obstruction establish neither side of this equivalence.

*Proof.* Assume the requested replacement. For any $N$-feasible final demand $\delta\in[\ell,u]$ at mass $M\ge1$, XXV 385.1 supplies one joint pair with stock total exactly $\delta$, by scaling stock if necessary. Apply full anchor extraction from Theorem 391.1. It preserves every stock coordinate and gives a depleted pair at mass $m\le\min\{M,B\}$. The replacement supplies an $O$ pair at mass $\max\{1,m\}\le M$ with stock at least $\delta$. Add $(M-\max\{1,m\})R$ to restore mass exactly $M$, retaining that stock. XXV 385.1 supplies complete $O$ feasibility at the same final demand. This is the same-mass inclusion equivalent to (391.10).

Conversely, assume that inclusion for every finite mass at least one. Any depleted pair in (393.2) funds its final demand by XXV 385.1. If $m<1$, add $(1-m)R$ before applying the inclusion; otherwise use mass $m$. The resulting complete $O$ witness at mass $\max\{1,m\}$ gives a joint $O$ pair with stock total $\delta$ by the same capacity theorem. Thus the replacement follows. The price formulation is equivalent by the fixed-complement packing test above, and the full signed certificate bridge gives (393.1).

The extraction is an operation within either input catalog. It provides no inclusion between $\mathcal X_N$ and $\mathcal X_O$. The three-word estimate controls mass without paying the simultaneous stopped first-cell mergers. Similarly, averaging preserves canonical cap rows without preserving hard query legality. These facts leave precisely the whole-allocation replacement (393.2)–(393.4) unproved; they imply neither a universal certificate nor an original strict separator. $\square$

## 追加锚（本行以下为增补区）

