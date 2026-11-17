# Recursive Relational Observation: Native Finite Precision Continuation Kernels

## 1. Original source, conditional rows and arithmetic resources

**Definition 1.1 (fixed native source).** The source is exactly [III145–148][III] and [XI43.1][XI]. Its configuration set is the full set $E$ of $89$ legal paths, with the original $26+63$ decomposition and unique ready $q_{\rm r}=\{3,7\}$. Write

$$
x=\varphi^{-1},\qquad y=\sqrt{x},\qquad
\zeta=e^{3\pi i/5},\qquad \alpha=3\pi/5.
$$

The original address projections, matrices and entire positive unit pulses are

$$
Q_* =\begin{pmatrix}x&xy\\xy&x^2\end{pmatrix},\qquad
H_j=-\alpha(I+\mathcal P_j),\qquad
U_j(s)=e^{i\alpha s}[I+(e^{i\alpha s}-1)\mathcal P_j],\quad
K_j=U_j(1),\quad 0\le s\le1.
$$

Here $Q_*$ is the restriction of $\mathcal P_j$ to an actual flippable pair; all original singleton blocks remain. The source configuration follows the original square minimal-current law, with its original independent innovations and node-safe holding construction. A prefix $a$ uses addresses $0,\ldots,10$; an external post-read word $h$ uses $0,\ldots,6$ and is the same request on both record branches. Concatenation is chronological: $K_a e_{q_{\rm r}}$ means the original ordered product.

The literal intermediate report is $I=b_9(Q_-)$, with $Q_+=Q_-$ and the original positive-branch update $M_I\psi/\|M_I\psi\|$. The literal terminal report is $W(Q)=(b_{-1},\ldots,b_8)(Q)$, retaining all $1024$ labels. Both record slices and all original failure, refusal, stop and alarm coordinates remain; the latter have zero mass in this ideal source. No configuration is removed as an unsuccessful outcome. All extra archives, when present, obey precisely III145.2 and XI43.1, including their emission times, counts and absence.

**Definition 1.2 (the conditional continuation consumer).** Fix a literal $a$ and the original cut after its report, pure update and already emitted archives, before the external $h$ arrives. Put

$$
z_i=M_iK_ae_{q_{\rm r}},\qquad
\tau_i=\|z_i\|^2.
$$

For $\tau_i>0$, write $u_i=z_i/\sqrt{\tau_i}$ and $\pi_i(q)=|u_i(q)|^2$. For every $\pi_i(q)>0$, $T_h^i(q,w)$ is the actual XI43.2 conditional continuation row, with entrance vector $u_i$, entrance configuration $q$, and unused original innovations. The entrance vector is not replaced by $e_q$. In particular

$$
T_{\emptyset}^i(q,w)=\mathbf1_{\{W(q)=w\}}.
$$

Fix any one standard Borel already-occurred $Y_{\rm cut}$ allowed by XI43.1, containing the original readable past and possibly mathematical hidden past. The same function is used for every future request; it contains neither unused innovations nor unexecuted counterfactual outputs. On a positive branch let $\nu_i$ be its actual law and $\rho_{i,y}(q)$ the actual cut-configuration posterior. The original unconditional law is

$$
\Lambda_h(\{i\}\times dy\times\{w\})
 =\tau_i\sum_{q:\pi_i(q)>0}\rho_{i,y}(q)T_h^i(q,w)\,\nu_i(dy).
\tag{1.1}
$$

Zero branches contribute zero measures without conditional states. Total variation is the supremum over all measurable joint events, equivalently half the $L^1$ norm for equal-mass measures. Formula (1.1) is the original XI43/XI47 consumer, not a definition of its rows by a Born terminal marginal.

**Definition 1.3 (finite arithmetic presentation).** Inputs to the arithmetic transformation below are only the fixed published source matrices and labels, the literal words $a,h$, and integers $A,N,r$ with $|a|\le A$, $|h|\le N$, $r\ge1$. The matrix data are fixed algebraic constants represented by integer coordinates in the order

$$
\mathcal O=\mathbb Z[y,\zeta],\qquad
y^4+y^2-1=0,\quad \zeta^2+y^2\zeta+1=0,
$$

with the positive real $y\in(0,1)$ and $\operatorname{Im}\zeta>0$ selected. Integer additions, comparisons, shifts and multiplications are charged in bit operations; schoolbook multiplication of $b$-bit integers costs $O(b^2)$. There is no unit-cost arbitrary real arithmetic, transition-probability query, hidden-configuration reader, jump-time reader, past-posterior query or archive oracle in these inputs. The transformation itself uses zero random bits. Its output is a mathematical conditional table, not an acquired physical continuation service.

## 2. Native conditional-table computation and whole-joint substitution

**Theorem 2.1 (finite-bit evaluation of the original rows).** Under Definitions 1.1–1.3 there is a deterministic finite arithmetic transformation producing sparse stochastic dyadic phase tables, and hence rows $\widehat T_h^i(q,w)$, for every positive original record branch. It has the following properties.

For every positive-support entrance $q$ on that branch,

$$
\operatorname{TV}\bigl(T_h^i(q,\cdot),\widehat T_h^i(q,\cdot)\bigr)
 \le 2|h|\,2^{-r}\le2N\,2^{-r}.
\tag{2.1}
$$

At $|h|=0$ the terminal map is exact. Each output row is stochastic on the original labels. No new label or failure mass is introduced, $b_9=i$ is preserved throughout the future, and phase outcomes have positive original phase support whenever they receive positive computed probability. An unoccupied branch needs no row or conditional state. Formal completions of unsupported configuration rows, used only for matrix multiplication, have no conditional-source meaning.

Define the mathematical comparison using the very same original cut law by

$$
\widehat\Lambda_h(\{i\}\times dy\times\{w\})
 =\tau_i\sum_{q:\pi_i(q)>0}\rho_{i,y}(q)
      \widehat T_h^i(q,w)\,\nu_i(dy),
\tag{2.2}
$$

with zero branches zero. Then, for every such fixed original $Y_{\rm cut}$,

$$
\operatorname{TV}(\Lambda_h,\widehat\Lambda_h)
 \le2|h|\,2^{-r}.
\tag{2.3}
$$

This includes every measurable event in the full $(I,Y_{\rm cut},W)$ space, with all branch masses retained. It requires no lower bound on a positive $\tau_i$ or on any positive configuration mass. The claim holds for every original cut law individually; it does not assert a single pointwise conditional version simultaneously for all possible $Y$.

Here are explicit finite resource bounds. Put

$$
\begin{gathered}
L=A+N+1,\qquad H=32(L+2),\\
B=4H+4r+64,\qquad t=4B+32.
\end{gathered}
\tag{2.4}
$$

All sign tests can use the same $t$-bit isolating interval for $y$. All integer registers in the sparse-table transformation have $O(t)$ bits, with constants depending only on the fixed native presentation. For one absolute native constant $C$, the total deterministic bit work, including the root isolation and both record branches, is at most

$$
C\bigl[t^3+89\{A+N(r+1)+1\}t^2\bigr].
\tag{2.5}
$$

Raw vectors and arithmetic need $O(89t)$ working bits. Retaining all sparse phase tables needs an additional $O(89N(r+1))$ bits, besides the literal input words and fixed source data. Output may instead be streamed. If a dense final configuration table is requested, ordinary dyadic matrix multiplication adds at most

$$
C\,89^3(N+1)(2Nr+16)^2
\tag{2.6}
$$

bit operations and $O(89^2(2Nr+16))$ bits of table workspace and output. Grouping by the fixed terminal map gives all $1024$ columns; these fixed dimensions can be absorbed in $C$. These are arithmetic bounds, not physical clock, energy or hardware bounds.

For a prescribed mathematical $0<\epsilon<1$, the sufficient choice

$$
r=\max\left\{1,\left\lceil\log_2
 \frac{2\max\{1,N\}}{\epsilon}\right\rceil\right\}
\tag{2.7}
$$

gives error at most $\epsilon$. The finite arithmetic input is $r$; no exact-real input service for an arbitrary $\epsilon$ is assumed. If $\epsilon$ is given as a positive rational binary numerator and denominator of total length $e$, determining (2.7) uses elementary integer comparisons and adds $O((e+\log(N+1)+1)^2)$ bit work.

The same full joint error bound permits the original lawful passive archives to be adjoined using their same conditional kernel on the matched original readable inputs. This extension retains archive emission times, counts, absence and post-terminal records, but adds no deterministic archive execution, output-length or random-bit bound. Its precise factorization is included in the proof.

Proof. The new arithmetic construction is established below on the original source. Its survival law, algebraic extrema and general probability-composition tools are reused at the indicated steps.

### 2.1 Exact raw vectors in one fixed order

Use the integral basis

$$
\mathcal B=\{y^k\zeta^e:0\le k<4,\ 0\le e<2\}.
$$

The degree-eight field and integral-order property are supplied by [native mixing, Theorem 4.2][Mix]. This is another basis of that same order: $y^2=x$, while $\zeta+\zeta^{-1}=-x$ and $\zeta^2=-1-x\zeta$. The real subfield needed here is $\mathbb Q(y)$, of degree four. Indeed $x$ has conjugate $-\varphi$ and norm $-1$, so it cannot be a square in $\mathbb Q(\sqrt5)$; $y$ therefore has minimal polynomial $X^4+X^2-1$. The displayed real basis has degree four and $\zeta$ adds its nonreal quadratic extension.

For a reduced coordinate vector $v$ let $\|v\|_c$ be the sum of absolute integer coefficients. Direct reduction of the basis products gives

$$
\|vw\|_c\le8\|v\|_c\|w\|_c,
\qquad \|\overline v\|_c\le3\|v\|_c.
\tag{2.8}
$$

For completeness, powers $y^4,y^5,y^6$ reduce respectively to $1-y^2$, $y-y^3$, $2y^2-1$, and $y^7=2y^3-y$. For a product with two $\zeta$ factors replace $\zeta^2$ by $-1-y^2\zeta$. The maximum resulting coefficient sum for the $64$ basis products is $8$ (attained at $y^3\zeta\,y^3\zeta$). Conjugation fixes $y$ and sends $y^k\zeta$ to $-y^{k+2}-y^k\zeta$, whose reduced coefficient sum is at most three. These reductions prove (2.8) for arbitrary integer coordinates.

On an original active pair the endpoint matrix reduces to

$$
K_{00}=-y^2,\qquad
K_{01}=K_{10}=-y^3-y\zeta,\qquad
K_{11}=(1-y^2)(\zeta-1).
\tag{2.9}
$$

For example $K_{00}=\zeta x^2+\zeta^2x=-x$; the other entries follow by the same two order relations. The largest row sum of coefficient norms is six. Original singleton entries are $\zeta$ or $\zeta^2$, with coefficient norms at most two. Thus each original call multiplies the largest raw-coordinate coefficient norm by at most $48<64$; a coordinate projection does not increase it.

Starting from $e_{q_{\rm r}}$, compute $K_ae_{q_{\rm r}}$, then its two coordinate projections $z_i$, then the future endpoint vectors $K_{h_{\le k}}z_i$ exactly. At every stage,

$$
\max_q\|z(q)\|_c\le64^{A+N}\le64^L.
\tag{2.10}
$$

A record has zero mass exactly when all its projected coordinates vanish, decided by integer equality. On a positive branch the normalized physical vector is $z/\sqrt{\tau_i}$. Every current numerator and square-mass denominator has the same factor $1/\tau_i$, which cancels. Hence raw vectors compute exactly the original conditional rates and survival ratios. No numerical division by a record mass occurs, and normalization radicals do not accumulate from call to call.

### 2.2 Each original pulse has two algebraic phase kernels

For one actual active pair let its entrance raw vector be $(z_0,z_1)$. Put $v=Q_*z$, $u=(I-Q_*)z$ on that pair and

$$
\begin{gathered}
m=|z_0|^2+|z_1|^2,\qquad
b=|u_0|^2+|v_0|^2,\qquad D=\overline{u_0}v_0,\qquad E=D\overline D,\\
p(s)=|u_0+e^{i\alpha s}v_0|^2
     =b+2\operatorname{Re}(De^{i\alpha s}),\qquad
p'(s)=-2\alpha\operatorname{Im}(De^{i\alpha s}).
\end{gathered}
\tag{2.11}
$$

Here $p$ is the raw mass of configuration $q_0$ and the other mass is $m-p$. All $m,b,E,p(0),p(1)$ are real elements of $\mathcal O$, hence reduced integer polynomials in $y$. These are the same sinusoidal masses and extrema used in III146 and [V8, (8.4)][V], in a coordinate form suited to the particular unit interval.

If $D=0$, the current vanishes identically. Otherwise $\alpha<\pi$ implies at most one derivative zero in the open pulse. There is an interior turn exactly when the nonzero endpoint derivatives have opposite signs. If the first is positive the turn is the maximum $b+2\sqrt E$; if it is negative the turn is the minimum $b-2\sqrt E$. A zero endpoint derivative is an endpoint turn, requiring no extra interior phase. Both derivatives zero imply $D=0$, since $\sin\alpha\ne0$. If a reduced $D=A_0(y)+A_1(y)\zeta$, then

$$
\operatorname{Im}D=A_1(y)\sin\alpha.
$$

Consequently the derivative signs require only real quartic-field signs, applied to $D$ and $D\zeta$. Neither an extremum time nor an inverse trigonometric function is evaluated.

On any nonconstant monotone interval the departing configuration has a decreasing raw mass $d(s)$; the receiver is absorbing until the interval ends. If its positive start mass is $d_0$ and end mass is $d_1$, its holding probability is

$$
\exp\left(-\int\frac{-d'(s)}{d(s)}\,ds\right)
 =\frac{d_1}{d_0},\qquad
f=1-\frac{d_1}{d_0}\in[0,1].
\tag{2.12}
$$

This is the integral-risk holding formula of [Georgii–Tumulka, §3 (10)–(11)][GT], with III146's original node-safe extension. When $d_1=0$, the survival limit is zero; no atom, seam resampling or artificial jump is inserted. A nonconstant decreasing nonnegative mass has $d_0>0$. An empty block and any unsupported start row may be completed by identity solely as matrix bookkeeping. Constant-current-zero blocks also use identity. These conventions never define a conditional source state at a node.

Thus an original pulse endpoint kernel is the product of at most two one-direction Bernoulli matrices per block. Assemble these by direct sum into two sparse $89$-state matrices, padding an absent second phase by identity. Different blocks may have different turning times: these two direct sums are algebraic factorizations of endpoint kernels, not two common physical times or new controls. Original singleton blocks remain identity on configurations. At a positive phase entrance every positive matrix transition is an actual permitted phase outcome.

Each departing mass at an endpoint of such a phase has the form

$$
d=a+b_0\sqrt E,\qquad a\in\mathbb Z[y],\quad b_0\in\{0,2,-2\}.
\tag{2.13}
$$

At a seam this is just its raw coordinate square; at a turn it is $b\pm2\sqrt E$ or $m-b\mp2\sqrt E$. Both ends of the same phase use the same $E$. The phase kernel therefore uses at most one quadratic radical over the fixed real quartic field. The next call recomputes its data from the exact endpoint vector in $\mathcal O$, so no radical tower arises.

### 2.3 Uniform paid threshold decisions, including equality

The bounds below are deliberately loose. Write $S=64^L$. By (2.8) and the coefficient row sum of $Q_*$, $\|v_q\|_c\le32S$ and $\|u_q\|_c\le64S$. For upper bounds use $\|\overline v\|_c\le8\|v\|_c$. Formula (2.11) then gives

$$
\|D\|_c\le2^{17}S^2,\quad
\|b\|_c\le2^{19}S^2,\quad
\|E\|_c\le2^{40}S^4.
\tag{2.14}
$$

Raw seam masses have coefficient norms at most $64S^2$, and $m$ at most $128S^2$. Consequently the real polynomial coefficients in (2.11)–(2.13), including $m-b$, and the derivative-sign polynomials have coefficient norms less than $2^H$ for the $H$ in (2.4).

For a dyadic threshold $k/2^r$, $0\le k\le2^r$, the sign of $f-k/2^r$ in (2.12), after multiplying by the known positive $2^rd_0$, is the sign of

$$
(2^r-k)d_0-2^rd_1=a+b_1\sqrt E.
\tag{2.15}
$$

Its reduced $a,b_1$ have coefficient norms below $2^{H+r+4}$. Decide $E=0$, $a=0$ and $b_1=0$ by exact coefficient equality. Signs of $a,b_1$ settle the same-sign case. In the opposite-sign case one squaring reduces the decision to the sign of $a^2-b_1^2E$; equality of that reduced polynomial, together with the opposite signs, decides exact cancellation. For example when $a>0>b_1$ the sign is that of $a^2-b_1^2E$; the other case reverses it. All these real sign polynomials have degree at most three after reduction. From (2.8), the largest coefficient norm is bounded by

$$
2^{3H+2r+15}<2^B.
\tag{2.16}
$$

Thus neither exact dyadic boundaries nor zero/one probabilities are assigned by an approximate numerical guess.

Here is a finite sign procedure. For a nonzero reduced $P\in\mathbb Z[X]$ of degree at most three with $\|P\|_1<2^B$, $P(y)$ is a nonzero algebraic integer. The other roots of $X^4+X^2-1$ are $-y,i/y,-i/y$, all of modulus less than two. Each other conjugate of $P(y)$ has modulus less than $8\,2^B$. The nonzero integer norm, the same standard mechanism used in native mixing Theorem 4.2, yields

$$
|P(y)|>2^{-3B-9}.
\tag{2.17}
$$

On $[0,1]$, $|P'|\le3\,2^B$. Isolate the positive root $y$ by $t$ rational bisections of $X^4+X^2-1$ on $[0,1]$. This polynomial is strictly increasing there, so integer comparisons at dyadic midpoints give a width $2^{-t}$ interval. At its midpoint the evaluation error for $P$ is at most $3\,2^{B-t}$, smaller than half (2.17) for (2.4). Exact rational evaluation therefore has the true sign. A reduced zero polynomial was already detected by equality, before this procedure. Midpoint polynomial evaluation involves only $O(t)$-bit integers, even after clearing its fixed-degree dyadic denominator.

Bisection costs $O(t^3)$ schoolbook bit operations in total. Each subsequent quartic sign costs $O(t^2)$; the finitely many reductions and sign decisions for a radical comparison have the same bound. Binary search gives the exact integer $\lfloor2^rf\rfloor$ in $O(r+1)$ comparisons, treating $f=0$ and $f=1$ exactly first. This is a derived finite algorithm for the native holding kernel, not an assumption that its probabilities are available.

### 2.4 Dyadic rows, support and deterministic cost

Replace each phase flip $f$ by

$$
\widehat f=2^{-r}\lfloor2^rf\rfloor.
\tag{2.18}
$$

A Bernoulli row changes in TV by less than $2^{-r}$, or by zero at $f=0,1$. In particular an exactly necessary node-avoiding jump remains certain; a forbidden jump remains impossible. If $0<f<1$, both phase outcomes were already possible. It follows phase by phase that a positive-support entrance cannot acquire an unsupported phase endpoint. Formal identity completions at zero rows never become a substitute for a source law on such rows.

Compose the at most $2|h|$ sparse matrices and then apply the exact terminal map. The usual finite-kernel telescoping bound, as used in [V64, Proposition 6.5][V64], gives (2.1). The support argument ensures that the exact matrices along every row under consideration are the original conditional continuation. A table uses only legal pair edges; future addresses cannot change $b_9$. Thus the computed record/terminal support and ideal failure convention have the asserted legality.

There are $O(89(A+N))$ fixed-dimensional exact field updates and at most $2\cdot89N$ local dyadic phase probabilities per branch. Each needs $O(r+1)$ radical comparisons with the bounds just proved. All intermediates have $O(t)$-bit coordinates. This proves (2.5), including one root isolation shared by all comparisons. A phase flip is an $r$-bit numerator plus its fixed denominator and a constant-size native edge label, proving the sparse-storage bound. The original words cost $O(A+N)$ bits under fixed address encoding.

After at most $2N$ phase matrices the dense denominator divides $2^{2Nr}$; stochasticity bounds every numerator by that denominator. Each dense multiplication can therefore be performed with $O((2Nr+16)^2)$ bit work per fixed triple of configuration indices. At most $2N$ products prove (2.6); padding and final label grouping account for $N=0$ and the fixed dimensions. No arbitrary-width arithmetic is charged as one operation.

### 2.5 The same cut law and the entire unconditional consumer

For every fixed original $(a,i,Y_{\rm cut})$, zero mean of a nonnegative posterior at a zero-square coordinate gives $\rho_{i,y}(q)=0$ there almost everywhere, exactly as XI43.2. Integrate (2.1) against this unchanged actual posterior. Using the same dominating measure $\tau_i\nu_i$ on each record slice gives

$$
\begin{aligned}
\operatorname{TV}(\Lambda_h,\widehat\Lambda_h)
&\le\sum_{i:\tau_i>0}\tau_i
 \int\sum_{q:\pi_i(q)>0}\rho_{i,y}(q)
       \operatorname{TV}(T_h^i(q,\cdot),\widehat T_h^i(q,\cdot))\,d\nu_i(y)\\
&\le2|h|\,2^{-r}\sum_i\tau_i
 =2|h|\,2^{-r}.
\end{aligned}
\tag{2.19}
$$

This reuses XI47's whole-joint integration convention, rather than bounding one selected past event. Both records are retained with their actual unconditional weights, including arbitrarily rare records; no division by a branch mass appears. The joint event's terminal slices may depend on $y$, so (2.19) is the full TV assertion (2.3). Conditional versions are taken for each fixed $Y$; only finite configurations and, if needed, countably many finite words are combined on a common full-measure set.

The arithmetic transformation evaluates neither $\nu_i$ nor $\rho_{i,y}$ and does not regenerate the past. These are retained original mathematical measures in (2.2), not free acquired inputs. Producing all rows from published parameters and actuating a physical continuation from an unknown actual $Q$ are different operations. No access to that $Q$, to $Y$ as a whole, or to original innovation seeds follows from the table.

### 2.6 Exactly which archive extension is permitted

Let $g(Y_{\rm cut})$ decode the original readable cut history. Fix the external literal requests, their original scheduling rule, and the original archive policy. III145.2 says every subsequent archive emission uses only the already readable history and independent archive innovations, without feedback to the source or a new control choice. Before the terminal, these inputs contain the fixed future calls and earlier archive outputs, with the retained $I$ and past history. At the terminal the only new source report is the literal $W$. Subsequent emissions can use this retained report. Therefore the original joint future-archive law factors through one supplied Markov kernel

$$
\mathcal K_{a,h}(d\mathcal A\mid g(y),i,w).
\tag{2.20}
$$

The archive value $\mathcal A$ includes all emission times, numbers, absence and post-terminal values required by the original policy. Any original exogenous scheduling coordinates must also be retained or adjoined through their same supplied kernel; they are not chosen from a changed wavefunction or hidden path. The factorization follows by composing the original causal archive kernels with their independent innovations, inserting the literal terminal report at its actual stage. The absence of hidden triggering and of archive feedback is essential.

Attach this very same (2.20) to $\Lambda_h$ and $\widehat\Lambda_h$. Common-kernel TV contraction gives the same bound (2.3) on the resulting complete specified readable-archive joint laws. No continuity or effective computation of $\mathcal K_{a,h}$ is used. Nothing here supplies a deterministic runtime, random-bit, emission-count or output-length bound for an arbitrary such measurable kernel. A whole executable archive budget would require a separately supplied bounded implementation and its actual costs. If a proposed extension reads hidden jump times, configurations, or discarded intermediate paths, it is not (2.20); it cannot be transported merely because terminal rows are close. This completes the theorem. ∎

## 3. An original conditional row that its Born marginal does not determine

**Theorem 3.1 (the ready two-call discriminator).** Take the original program $\mathsf R((1),(1))$ from $q_{\rm r}=q_0=\{3,7\}$, with $q_1=\{1,3,7\}$ and $w_j=W(q_j)$. At the cut after the first full pulse, $I=0$ surely, both cut configurations have positive mass, and the original pure update is identity on the actual vector. Let

$$
p=3x-1,\qquad a_*=4x^3,\qquad d_*=x^2/4.
$$

For the second original full pulse the conditional rows satisfy

$$
T_1^0(q_0,w_1)=p(1-d_*),\qquad
T_1^0(q_1,w_1)=1-d_*.
\tag{3.1}
$$

They are distinct, while their original Born-weighted average is $p$. Thus the known terminal Born marginal cannot replace both conditional rows in (1.1). All unused labels, the other record slice and ideal failure coordinates remain at their original zero masses for this particular program.

Proof. These are the actual two configurations of III146.2, not another two-state source. Their $b_9$ values are both zero, so the intermediate report and pure update have the stated form. The original $89$-carrier retains its other configurations, which happen to have zero mass here. Under two successive positive address-$1$ pulses,

$$
p_{q_1}(t)=4x^3\sin^2(3\pi t/10),\qquad 0\le t\le2.
$$

Its values at $1,5/3,2$ are respectively $x,a_*,p$, as in III146–147. The first phase of the second pulse moves only $q_0\to q_1$ with probability $(a_*-x)/(1-x)$ conditional on $q_0$. Its second phase moves only $q_1\to q_0$ with probability $(a_*-p)/a_*$ conditional on $q_1$. Using $x^2+x=1$ gives the exact identities

$$
\frac{a_*-x}{1-x}=p,\qquad
\frac{a_*-p}{a_*}=d_*,\qquad
\{(1-x)p+x\}(1-d_*)=p.
\tag{3.2}
$$

All displayed denominators are positive. Since $0<p<1$ and $0<d_*<1$, composing the two original phase kernels proves (3.1) and their strict distinction. At the cut the masses are $1-x,x$, which proves the average assertion. Choosing the fixed mathematical past $Y_{\rm cut}=(\mathcal G_{\rm cut},Q_{\rm cut})$ in XI43 makes its posterior the point mass at that actual $Q_{\rm cut}$. Then the joint masses with $W=w_1$ are $(1-x)p(1-d_*)$ and $x(1-d_*)$ on the two cut-configuration events. Replacing both rows by their marginal $p$ changes those joint masses. No hidden-past reader has been installed, no internal turn has been made a control time, and no conditioning on success has occurred. ∎

## 4. Observation, randomness and recovery boundaries

**Definition 4.1 (the represented continuation relation).** The represented object is the original conditional terminal relation $(a,i,h,q)\mapsto T_h^i(q,\cdot)$ on positive actual cut support, and its use in the unchanged original past/record/terminal law. The sparse phase tables represent this relation to (2.1), not a rounded continuous configuration history. The original raw vector, legal pair geometry and literal chronological word together supply its finite arithmetic computation. Theorem 3.1 distinguishes this relation from the terminal Born marginal. The computation supplies no inverse recovery of an unobserved cut configuration or complete past from a single terminal report.

**Definition 4.2 (paid optional sampling).** If a mathematical sampler for the compiled phase representation is desired, provide fresh independent fair bits explicitly. For each of at most two phase decisions per full future call, draw an integer uniformly from $\{0,\ldots,2^r-1\}$ and compare it with the computed flip numerator. This consumes at most $2|h|r$ fair bits and exactly samples the compiled rows, conditional on a supplied entrance row. It does not exactly sample the original generally nondyadic probabilities. Selecting the actual $I,Y,Q_{\rm cut}$, realizing their original joint law, and executing an arbitrary archive kernel are separate inputs and costs. No physical fair-bit source, access to original source innovations, or new randomized control follows from this mathematical sampling representation. General random-bit sampling methods are established tools; see [Lumbroso][Lumbroso].

**Definition 4.3 (distinct time and event resources).** A word of $|h|$ future calls has $|h|$ original unit-pulse intervals, with any original external waiting/scheduling coordinates retained separately. Theorem 2.1 requests no jump-time grid or physical-time numerical precision. Its at most $2|h|$ phase decisions are computations of endpoint kernels. They are distinct from the already supplied almost-sure bound of $2|h|$ genuine source jumps, from a bound on a stochastic rate, and from a deterministic count of proposal events or arithmetic steps. Neither rate-cap approximation nor almost-sure jump count alone gives (2.5).

**Definition 4.4 (remaining recovery obligations).** The complete continuous-history law, including exact jump times and its original deterministic vector graph, is a different comparison space. Small error in the present terminal relation does not assert small TV there; the exact-cycle and graph-TV distinctions remain those of III183–185 and V64. Input-ray/full-marked-history stability in XI54–56 uses a common actual cut, fixed Hamiltonians, pulses, clocks and the same readable archive kernel. That stability does not compute the present conditional rows, and the present finite-bit computation does not establish that stronger marked-history comparison. A changed or coarsened input to a hidden-path-dependent kernel requires its own bridge.

The full recovery problem for economical relations expressing space, continuation/time, boundary and memory retains the obligations of actual acquisition and usable memory interfaces, source-owner realization, exact-history observation, archive effectivity, and inverse recovery. Finite computation of all conditional tables does not supply any of those interfaces by descriptive encoding. In particular Theorem 2.1 is a conditional mathematical consequence of the original source premises, not a construction of a new physical source or a uniform fixed finite budget for all unbounded word lengths.

## 5. Mathematical attribution

**Definition 5.1 (supplier correspondence).** The source-specific construction in Theorem 2.1 is `repo-derived`: exact original raw-word/projection arithmetic is connected to blockwise monotone pulse kernels, to charged exact radical-threshold decisions, and then to the unchanged XI43/XI47 whole unconditional consumer. The ready witness in Theorem 3.1 identifies why that consumer needs the conditional rows. No claim of worldwide novelty or kernel verification is attached to these ordinary mathematical proofs.

The following are reused within that construction, rather than independent new results: III145–148 supply the fixed matrices, minimal-current process, literal reports, pure update, nodes, common innovations and positive-support conditional continuation; V8 supplies the algebraic sinusoidal extrema and exact full-cycle kernels; III183–185 supplies the cycle/randomness boundaries; [the native finite-rate volume][Rate] supplies its original-source rate-cap/history result in its specified support domain, independently of this arithmetic construction; native mixing Theorem 4.2 supplies the degree-eight integral order and norm-separation method; XI43/XI47 and V64 supply the whole-joint and finite-kernel TV conventions. XI54–56 retains its separate exact-input-ray/marked-history scope. None is used as an oracle for unknown conditional probabilities.

The primary integral-risk and existence suppliers are [Dürr–Goldstein–Tumulka–Zanghì, §2.7][DGTZ] and [Georgii–Tumulka, Theorem 1 and §3][GT]. The parameter match is their configuration projections $P_q=|q\rangle\langle q|$ and $H_{\rm GT}=2H_j$, matching their $\hbar=2$ convention to the present $\hbar=1$, as already fixed in III146. Their existence and holding laws do not themselves supply the native finite arithmetic bound. Generic integer-norm separation, dyadic Bernoulli rounding and finite-kernel composition are standard intermediate tools, not new appendices or new source permissions.

The existing Lean statements `NativeProtocolEventArithmetic.original_event_arithmetic`, `FiniteRuntimeReduction.finite_precision_runtime_reduction` and the positive-linear-leg `OriginalControlMarkedJump.Leg.survival_formula` have different supplied carriers or hypotheses: native event integrality, a given finite runtime product, and a specified positive linear leg, respectively. They are not assertions of this original sinusoidal conditional-row computation. Pinned mathlib number-field norms and kernel composition provide general mathematical infrastructure. These source correspondences assert neither a fresh Lean application nor a global absence theorem for other library results.

[III]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md
[V]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_V.md
[XI]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md
[Mix]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_FIBONACCI_MIXING_CERTIFICATES.md
[Rate]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_FINITE_RATE_CONTINUATION.md
[V64]: AURIC_APPROXIMATE_RELATIONS_RIGIDITY_SQUARE_CALIBRATION_AND_QUANTUM_READOUT_STABILITY_V64.md
[GT]: https://arxiv.org/html/math/0312294v2
[DGTZ]: https://arxiv.org/html/quant-ph/0407116v1
[Lumbroso]: https://arxiv.org/html/1304.1916v1

## 追加锚（本行以下为增补区）
