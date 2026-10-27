# Original-source retained emission timing and complete-law boundaries

This volume studies a single unchanged source and one retained detector across a continuing timing menu. It is a source-relative conditional theory. The source is not replaced by a stationary law, a killed process, a reset, or a re-scaled clock.

## 1. Source, detector, and task

Fix the original parameters $a,\eta>0$. Let

$$
G=H^1\times\mathbb R,
$$

with the original coordinates $(x,y,z,w)$, group operation $w+xy'$ in the fourth coordinate, identity $e$, Haar measure $\mu$, unit Green field $\Gamma$, selector $A(u)=\rho C(u)$, positive normalized $h$, and $m=h^2\mu$. Retain the complete complex form $V_0$ and correction $C_1$, its nonnegative self-adjoint generator $K$, and the conservative semigroup

$$
T_s=\exp(-sK)\quad(s\geq0).
$$

The actual diffusion $Z$ starts at $e$ at original time zero. At each positive deterministic read, the source law is $g_t m$, where $g_t\in L^2(m)$ and $g_t>0$ $m$-almost everywhere. The source, its clock, selector and entrance are the same in every comparison below.

A detector is a fixed Borel simplex

$$
 f=(f_0,f_1,f_3,f_B),\qquad f_i:G\to[0,1],\qquad \sum_i f_i=1.
$$

Conditional on the entire source path, labels at commanded times are fresh and independent with conditional probabilities $f_i(Z_s)$. Reads are passive and do not change $Z$. The attempted deterministic replacement is one time-homogeneous Borel partition $P=(P_0,P_1,P_3,P_B)$ of $G$, installed before the timing menu is selected. It receives no hidden seed, source path, clock index, response history, or extra source state.

For fixed $t>0$ write $\mu_t=g_t m$ and define

$$
\pi_i=\int g_t f_i\,dm,\quad C_{ij}=\int g_t f_i f_j\,dm,
$$

$$
\nu_f^s(i,j)=\int g_t f_i T_s f_j\,dm,
\quad J=1-\sum_i C_{ii}=\int g_t\left(1-\sum_i f_i^2\right)dm,
$$

and

$$
E=\int g_t(1-\max_i f_i)\,dm.
$$

For a partition put $\alpha_i=\mu_t(P_i)$ and denote its pair law by $\nu_P^s$. Total variation on a finite alphabet is half the $\ell^1$ distance. The pair law, the full label word, the joint source-label law, and the source-joint law of a finite timing policy are different targets and remain different throughout this volume.

The source law supplies atomless positive-time marginals and strong $L^2$ continuity $T_su\to u$ as $s\downarrow0$. The existing fixed-pair attainment theorem supplies a partition separately for each fixed positive $(t,s)$; it does not supply one partition for a menu of gaps or an acquired installation procedure.

## 2. A shared short-gap lemma

**(B1) Lemma 2.1 (ordered short-gap limits).** For every fixed $t>0$ and every Borel partition $P$,

$$
\lim_{s\downarrow0}\nu_f^s(i,j)=C_{ij},\qquad
\lim_{s\downarrow0}\nu_P^s(i,j)=\begin{cases}\alpha_i,&i=j,\\0,&i\ne j.\end{cases}
$$

Consequently,

$$
\lim_{s\downarrow0}\operatorname{TV}(\nu_P^s,\nu_f^s)
=\frac12\left(\sum_i|\alpha_i-C_{ii}|+J\right)\geq J.
\tag{2.1}
$$

The infimum over $P$ of the right side is $J$ and is attained by any partition with $\alpha_i=\pi_i$. In the reversed order,

$$
\lim_{s\downarrow0}\inf_P\operatorname{TV}(\nu_P^s,\nu_f^s)=0,
\tag{2.2}
$$

because every fixed positive gap has a separately attained purifier.

**Proof.** Strong continuity gives $T_sf_j\to f_j$ in $L^2(m)$. Since $g_tf_i\in L^2(m)$, the pairings converge to $C_{ij}$. For a partition, $P_iT_sP_j$ converges to $P_iP_j$, which is zero for $i\ne j$ and $P_i$ for $i=j$; integration gives the second limit. The off-diagonal mass of $C$ is $J$, and its diagonal is $C_{ii}$, so the finite-alphabet $ell^1$ calculation yields (2.1). Since $\mu_t$ is atomless, coordinate quantile slabs produce a Borel partition with prescribed masses $\pi_i$; then $\alpha_i-C_{ii}=\int g_t f_i(1-f_i)\,dm+\sum_{j\ne i}\int g_t f_i f_j\,dm\geq0$ and the simplex identity gives $\sum_i(\pi_i-C_{ii})=J$. Thus equality is attained. Equation (2.2) uses the existing exact fixed-pair theorem, with $P$ allowed to depend on $s$. The two limits differ because their quantifiers differ. ∎

## 3. One continuing detector and joint-source sufficiency

**(B2) Theorem 3.1 (shrinking-menu criterion).** Let $D\subset(0,\infty)$ with $\inf D=0$. The following are equivalent:

1. one partition $P$ satisfies $\nu_P^s=\nu_f^s$ for every $s\in D$;
2. $J=0$;
3. $f$ is a simplex vertex $m$-almost everywhere.

When these conditions hold, a Borel repair of $f$ gives equality of the joint source-label law for every finite timing-policy tree whose node delays are deterministic and strictly positive and whose first read occurs after a positive lead-in. Branching on returned labels is allowed. No arbitrary stopping-time or contact-time extension is included.

**Proof.** Choose $s_n\in D$ tending to zero. Equality in (1) and Lemma 2.1 force $J=0$. The integrand defining $J$ is nonnegative and vanishes exactly at simplex vertices. Since $g_t>0$ $m$-almost everywhere, $f$ is vertex-valued $m$-almost everywhere. Repair the common null set by assigning one label, obtaining $P$. For any fixed finite policy tree there are only finitely many positive deterministic sampling epochs. Each source state at such an epoch avoids the repair set almost surely by positive-time absolute continuity. Couple the stochastic and deterministic detectors to the same $Z$; outside this finite union of null events they emit the same labels and therefore take the same branches. Induction down the finite tree gives equality of the full source-joint law. The converse is immediate because the pair projection of a joint law is a pair law and Lemma 2.1 applies. ∎

**Corollary 3.2 (uniform detector).** For $f_i\equiv1/4$, $J=3/4$. Therefore no one source-only partition can preserve every positive lag in any set accumulating at zero, even though a different partition may purify each fixed pair separately.

## 4. One-read optimum and informative spatial examples

**(B3) Theorem 4.1 (literal current-source optimum).** Let $P_f$ and $P_P$ be the one-read joint laws on $G\times\{0,1,3,B\}$:

$$
P_f(dp,i)=\mu_t(dp)f_i(p),\qquad P_P(dp,i)=\mu_t(dp)1_{P_i}(p).
$$

Then

$$
\inf_P\operatorname{TV}(P_P,P_f)=E,
\tag{4.1}
$$

and the infimum is attained by the first-maximizer partition, with any Borel tie rule. For uniform $f_i=1/4$, every partition has joint distance exactly $3/4$ at every fixed positive endpoint. This joint statement remains true for a partition that happens to purify a label pair.

**Proof.** At a point $p$, a deterministic label is a point mass and the conditional distance from $f(p)$ is $1-f_{a(p)}(p)$. Integrating gives (4.1), and choosing a maximizer gives attainment. For uniform $f$, the conditional distance is $3/4$ at every point. A record-only pair equality does not preserve the literal current point, so it cannot improve this joint distance. ∎

**(B8) Proposition 4.2 (two distinct spatial families).** Let $C=\{x>0\}$. The binary half-space detector

$$
 f_1=\frac14+\frac12 1_C,\qquad f_0=1-f_1,qquad f_3=f_B=0
$$

has $J=3/8$ and $E=1/4$. Let $v=x/(1+|x|)$ and

$$
 f_0=\frac{1+v}{4},\quad f_1=\frac{1-v}{4},\quad f_3=f_B=\frac14.
$$

Then

$$
J=\frac34-\frac18\int v^2\,d\mu_t\geq\frac58.
$$

Neither a finite emitted word nor a finite label likelihood exactly acquires the corresponding spatial bit or scalar.

**Proof.** On each half-space the binary probability vector is $(3/4,1/4)$ or $(1/4,3/4)$, giving $J=1-(9/16+1/16)=3/8$ and $E=1-3/4=1/4$. For the second detector, expand $f_0^2+f_1^2+1/16+1/16=(3+v^2)/8$ and integrate. Since $|v|<1$, the lower bound follows. Every finite word has a likelihood that is a finite product of factors in $[1/4,3/4]$ on either open half-space; both sides retain positive mass at every finite positive deterministic branch endpoint. The same conditioning argument leaves a continuous range of $v$ values, so no finite label word equals the spatial scalar. A specified sampler may use two fresh fair bits per read for the half-space detector; those bits and the retained labels are part of its run. ∎

## 5. Fixed positive clock and law-level recovery

For a fixed $\Delta>0$, define the collision profile

$$
C_f(k)=\sum_i\langle g_tf_i,T_{k\Delta}f_i\rangle_m,\qquad k\geq1,
$$

and put $R=1-J=\int g_t\sum_i f_i^2dm$. The next result uses all positive lags of one fixed clock, not a shrinking physical delay.

**(B4) Theorem 5.1 (positive-lag collision inversion).**

$$
R=\lim_{n\to\infty}\sum_{k=1}^n(-1)^{k+1}{n\choose k}C_f(k).
\tag{5.1}
$$

Thus an exact complete positive-lag collision profile determines $J$. It need not determine $f$, its cells, the current source point, the full word law, or an installed evaluator.

**Proof.** Let $Q=T_\Delta$. Functional calculus gives a nonnegative self-adjoint contraction. Since $Q=\exp(-\Delta K)$, its kernel is zero: every finite spectral value has strictly positive multiplier. Zero may still be a limit point of the spectrum. The polynomial

$$
B_n=I-(I-Q)^n=\sum_{k=1}^n(-1)^{k+1}{n\choose k}Q^k
$$

converges strongly to $I$: the multiplier $1-(1-q)^n$ tends to one for every $q>0$ and is bounded by one, while the spectral projection at $q=0$ vanishes. Pair $B_n$ with $g_tf_i$ and $f_i$, both in $L^2(m)$, and sum over $i$. This is the displayed formula. The cross spectral measures need not be positive, so no stationary moment argument is used. The coefficient absolute sum is $2^n-1$; an error $\varepsilon$ in each supplied collision can be amplified by at most $(2^n-1)\varepsilon$, in addition to an uncontrolled truncation bias. A finite passive word does not provide the complete profile. ∎

**(B5) Theorem 5.2 (complete-law criterion).** The following are equivalent:

1. one partition matches $C_f(k)$ for every $k\geq1$;
2. one partition matches every finite word law at times $t+n\Delta$;
3. $J=0$;
4. $f$ is vertex-valued $m$-almost everywhere.

The deterministic complete-law class is therefore the zero-deficit subset of the stochastic class.

**Proof.** For a partition, $\sum_i1_{P_i}^2=1$, so its collision limit is one. If all positive-lag collisions agree, Theorem 5.1 forces $R=1$ and hence $J=0$. Full word equality implies collision equality by projection. If $J=0$, repair $f$ on one Borel null set; the countably many positive sampling states avoid it almost surely, so every word law agrees. Uniform $f$ has $C_f(k)=1/4$, $J=3/4$, and gives a concrete failure. The partition supplied by the fixed-pair theorem may depend on $k$; it does not contradict the common-partition criterion. ∎

For every deterministic partition and every $J>0$ detector, some finite positive lag witnesses a discrepancy, but the witness may depend on the partition and detector. No uniform finite witness horizon or positive margin follows.

## 6. One sequence for all finite schedules

**(B6) Theorem 6.1 (finite-window density and compactness).** There is one sequence of Borel partitions $P^{(r)}$, independent of the finite schedule, such that for every $q$ and every $0<t_1<\cdots<t_q$,

$$
\operatorname{TV}\bigl(L_{P^{(r)}}^{t_1,\ldots,t_q},L_f^{t_1,\ldots,t_q}\bigr)\longrightarrow0.
\tag{6.1}
$$

Consequently deterministic complete-record laws are dense in the stochastic complete-record class for weak convergence on the compact sequence space. The stochastic class is compact and the deterministic class is proper. The functional $J$ is discontinuous at every target with $J>0$.

**Proof.** Use the existing atomless indicator approximation to choose one sequence with $1_{P_i^{(r)}}\to f_i$ weak-star in $L^\infty(m)$. The source-specific smoothing result gives $T_\delta u_r\to T_\delta u$ strongly in $L^2(m)$ for each fixed $\delta>0$. For a word $i_1,\ldots,i_q$, define backwards

$$
 b_q^{(r)}=1_{P_{i_q}^{(r)}},\qquad
 b_j^{(r)}=1_{P_{i_j}^{(r)}}T_{t_{j+1}-t_j}b_{j+1}^{(r)},
$$

and the analogous $b_j$ using $f$. Assume $b_{j+1}^{(r)}\to b_{j+1}$ weak-star. Smoothing makes the next semigroup factors converge strongly in $L^2$. Against any $L^1$ test, truncate the test to a bounded $L^2$ function: the strong error is controlled by Cauchy--Schwarz, and the remaining factor is a fixed weak-star test; remove the truncation using the uniform $[0,1]$ bound. Induction reaches $b_1^{(r)}\to b_1$ weak-star. The Markov word formula pairs it with the actual $g_{t_1}\in L^2\subset L^1$; every cylinder probability converges. Finitely many words give total variation.

The same induction proves continuity of every cylinder probability on the weak-star compact metrizable simplex of emissions. Its image in the compact finite-alphabet sequence space is compact. Theorem 5.2 gives a stochastic law outside the deterministic image, while the sequence above approximates it, proving proper density. All deterministic laws have $J=0$ and the target has $J>0$, so $J$ is discontinuous under weak record-law convergence. The sequence is pointwise in each fixed positive finite schedule; no uniform shrinking-gap, unbounded-horizon, feedback, rate, or computable refinement index is claimed. ∎

## 7. Quantitative minimax boundaries

Let $U_{16}$ be the uniform law on the four-label pair alphabet.

**(B7) Theorem 7.1 (uniform minimax).** For $f_i=1/4$ and every $D\subset(0,\infty)$ with $\inf D=0$,

$$
\min_P\sup_{s\in D}\operatorname{TV}(\nu_P^s,U_{16})=\frac34,
\qquad
\sup_{s\in D}\min_P\operatorname{TV}(\nu_P^s,U_{16})=0.
\tag{7.1}
$$

For a finite positive set $D_0$, $\inf_P\max_{s\in D_0}\operatorname{TV}(\nu_P^s,U_{16})=0$; common exact attainment for arbitrary finite $D_0$ is not asserted.

**Proof.** Lemma 2.1 gives the lower bound $3/4$ for every fixed $P$. Choose an atomless $\mu_t$-equal-mass partition. Every row of its pair law has mass $1/4$; its overlap with the four target entries of size $1/16$ is at least $1/16$ per row, hence total overlap at least $1/4$ and total variation at most $3/4$ for every positive $s$. The two orders in (7.1) follow from the fixed-pair attainment theorem. For a finite $D_0$, use the common weak-star approximation and smoothing argument on the finitely many gaps. ∎

### 7.1. Noisy quadrants

Let $C_0,C_1,C_2,C_3$ be the four oriented quadrants of $(x,y)$, with axes assigned Borelly. Source symmetry gives each positive-time marginal mass $1/4$. For $\varepsilon\in[0,1]$, define

$$
 f_i^\varepsilon=\varepsilon 1_{C_i}+\frac{1-\varepsilon}{4}.
$$

Let $q_{ij}(s)$ be the same-source quadrant pair law and let $U_{16}$ be uniform.

**(B9) Theorem 7.2 (sharp quadrant pair boundary).** For every $t_0>0$,

$$
\inf_P\sup_{k\geq1}\operatorname{TV}(\nu_P^{1/k},\nu_{f^\varepsilon}^{1/k})
=\frac{3(1-\varepsilon^2)}4.
\tag{7.2}
$$

The explicit partition $P_i=C_i$ attains the upper bound for every $t>0$ and $s>0$. Every separately fixed pair has infimum zero. No positive-gap supremum attainment is asserted.

**Proof.** The full-endpoint rotation in $\xi=w-xy/2$ preserves the source entrance, selector, form, and positive-time marginal, so the quadrants are equiprobable. Conditional independence and the two uniform quadrant marginals give

$$
\nu_{f^\varepsilon}^s=\varepsilon^2q(s)+(1-\varepsilon^2)U_{16}.
$$

As $s\downarrow0$, the off-diagonal mass of $q(s)$ tends to zero, so its distance from $U_{16}$ tends to $3/4$. For every partition, Lemma 2.1 applied to the limiting mixture gives the same lower bound. With $P=C$, the difference is $(1-\varepsilon^2)(q(s)-U_{16})$; the row-overlap argument bounds its norm by $3(1-\varepsilon^2)/4$. Fixed-pair attainment gives the last assertion. ∎

**(B10) Theorem 7.3 (full finite bursts).** At fixed $t_0>0$, for every $\varepsilon<1$ and every one fixed partition $P$,

$$
\sup_{n\geq2,\ k\geq1}
\operatorname{TV}(L_P^{t_0,t_0+1/k,\ldots,t_0+(n-1)/k},
L_{f^\varepsilon}^{t_0,t_0+1/k,\ldots,t_0+(n-1)/k})=1.
\tag{7.3}
$$

The infimum over $P$ of this supremum is one. At $\varepsilon=1$, the quadrant partition reproduces the full law exactly.

**Proof.** Consider the event that all $n$ labels are equal. For a fixed $P$, strong continuity and the finite-word Markov formula imply that as $k\to\infty$ its probability tends to one. For the noisy quadrant detector, conditional independence leaves the limit

$$
 c^n+3d^n,qquad c=\frac{1+3\varepsilon}{4},\quad d=\frac{1-\varepsilon}{4}.
$$

For $\varepsilon<1$, this tends to zero as $n\to\infty$. Taking first $k$ large and then $n$ large makes the event gap arbitrarily close to one; total variation is at most one. At $\varepsilon=1$ the detector is the quadrant partition itself. ∎

**(B11) Theorem 7.4 (resolution obstruction).** If $\varepsilon<1$ and $P^{(k)}$ exactly purifies the noisy-quadrant pair at gap $1/k$ and fixed $t_0$, the indicator tuples $(1_{P_i^{(k)}})_i$ have no strongly $L^2(m)$-convergent subsequence. Hence no finite detector dictionary and no $L^2$-precompact family supplies all these exact replacements.

**Proof.** Suppose a subsequence converges strongly to $a$. A further subsequence converges almost everywhere, and the indicator/simplex constraints make $a$ an indicator tuple. Strong continuity with variable inputs gives $T_{1/k}1_{P_i^{(k)}}\to a_i$ in $L^2$. Pairing with $g_{t_0}$ and truncating the $L^2$ weight yields a diagonal short-gap limit for the pair laws. The noisy target has positive limiting off-diagonal mass $3(1-\varepsilon^2)/4$, whereas any deterministic limit has zero off-diagonal mass, a contradiction. A finite program with an unbounded precision or parameter input can still generate a nonprecompact family; this is not a finite-bit or physical lower bound. ∎

## 8. Same-run resource and acquisition boundaries

All temporal comparisons charge the same actual source initialization, fixed original clock and detector installation. A retained deterministic partition has no fresh-emission-noise coordinate, but its Borel description, exact reference, comparisons, timing, reads, controller buffers, source binding, rights, and storage remain. An existential partition is not an acquired finite-bit procedure.

A literal four-label sampler can use two fresh fair bits per read, so an $n$-read run uses $2n$ supplied random bits and $n$ labels, with the clock/menu inputs, source references, payload retention and controller work charged separately. A binary half-space sampler uses two fresh fair bits per read in the displayed implementation. For the noisy quadrant at $\varepsilon=1/2$, one selector bit chooses the quadrant branch; on the other $n-R$ branches two more fair bits are consumed, so the run uses $R$ actual quadrant calls and $3n-2R$ fair bits, with expected $2n$ and worst case $3n$. The lead-in is $t_0$, epochs are $t_0+j/k$, and elapsed post-lead-in time is $(n-1)/k$.

A prepared independent tape moves the randomness to initialization, tape storage, access and consumption; it is a different interface and is not free. The fixed-pair purifier is already a sufficient conditional alternative for one positive pair, but its partition may depend on $(t,s)$ and its acquisition or description cost is uncontrolled. A complete collision profile in Theorem 5.1 is a law-level input, not a finite acquired record. The coefficient sum $2^n-1$ gives no uniform numerical rate. Existing finite exact-real sampling and prospective consumers remain sufficient for their own declared tasks.

The finite source-only criterion is therefore a deletion boundary: fresh detector randomness can be removed for a continuing same-source task exactly on the one-hot class, while changing the task to one pair, changing the timing menu, supplying a prepared tape, or retaining a stateful detector changes the comparison. No universal alpha/beta minimality, global resource optimum, physical proof, or four-view inverse is claimed.

## 9. Supplier correspondence and remaining obligations

Appendix II §§115--117 supplies the unchanged self-adjoint conservative source, positive-time entrance density and nondisturbing emission contract. §§119.6--119.8 supply bounded-order smoothing and one common indicator weak-star approximation. Theorem 122.1 supplies exact deterministic attainment for each separately fixed positive pair. These are reused with their exact hypotheses. The Dvoretzky--Wald--Wolfowitz atomless finite splitting theorem supports prescribed finite masses but does not supply simultaneous nonlinear constraints, a complete process purifier, or an acquired decoder. Standard self-adjoint spectral calculus supplies Theorem 5.1.

The new composition is the separation between the two quantifier orders, the all-lag collision inverse, complete-law criterion, one-sequence finite-window density, joint current-source optimum, spatial examples, attained minimax constants, full-burst and precompactness boundaries. No generic quotient or new harness capability is introduced.

The four expressions remain independently meaningful: Space is the original current point and coordinate frame; Time is the original selected schedule; Boundary is the installed emission map; Memory is the retained labels, timing and controller state. For $J>0$ no mutual inverse follows. A law-level statistic is not a current source acquisition. The source model, exact clock, detector rights, references and records remain the conditions of each theorem. The full common-source programme remains active; this bounded portfolio is not completion.

The finite atomless splitting reference is Dvoretzky--Wald--Wolfowitz, *Relations among certain ranges of vector measures*, Pacific Journal of Mathematics 1 (1951), Theorem 4 and Lemma 2. Its linear-integral scope does not provide a common nonlinear complete-record purifier. The fixed-pair source result and smoothing are the named Appendix II suppliers; the spectral step is standard self-adjoint functional calculus.

## 追加锚（本行以下为增补区）
