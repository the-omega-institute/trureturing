# Recursive Relational Observation: Native Recurrent Quantized Memory

## 1. The original source and the finite joint consumer

**Definition 1.1 (fixed source and operations).** Fix precisely the source of [III138, III145–148][III] and [XI43][XI]. Its carrier is the entire $89$-element set $E$ of legal paths: $b_{-1}b_0=10$, $b_{10}b_{11}b_{12}=010$, and the nine internal bits have no adjacent ones. The $26$-dimensional code and its $63$-dimensional complement remain in $\mathbb C^E$. The unique ready path is $q_{\rm r}=\{3,7\}$. Put

$$
d=89,\quad x=\varphi^{-1},\quad y=\sqrt{x},\quad
\alpha=3\pi/5,\quad\zeta=e^{i\alpha},\quad b_*=\alpha xy<2.
\tag{1.1}
$$

All address projections $\mathcal P_j$ are the original ones in III(138.2a), including every singleton at addresses $0,10$. The only pulses are the original positive unit pulses

$$
H_j=-\alpha(I+\mathcal P_j),\qquad
U_j(t)=e^{i\alpha t}[I+(e^{i\alpha t}-1)\mathcal P_j],\qquad K_j=U_j(1).
\tag{1.2}
$$

Their nontrivial blocks are the original flippable pairs, with

$$
\mathcal P_j\big|_{\{q_0,q_1\}}=
\begin{pmatrix}x&xy\\xy&x^2\end{pmatrix}=:P.
\tag{1.3}
$$

Configurations follow III(145.2)'s minimal-current law. On a nonzero vector $v$, its rate is defined only at $v(r)\ne0$:

$$
\sigma_j^v(q\mid r)=
\frac{[2\operatorname{Im}(\overline{v(q)}(H_j)_{qr}v(r))]_+}{|v(r)|^2}.
\tag{1.4}
$$

It is invariant under multiplication of $v$ by a nonzero scalar. The original node-safe holding law, positive-entrance conditional kernels, equivariance and at most two jumps per pulse are reused from III146.1, III160.1 and [IV278.1][IV]. In particular a kernel conditional on entrance $q$ retains the entire entrance vector; it does not replace that vector by $e_q$.

The programs are exactly $\mathsf T(a)$ and $\mathsf R(a,h)$: $a$ uses $\{0,\ldots,10\}$, while $h$ uses $\{0,\ldots,6\}$ and is the same external word on both record branches. At the intermediate read,

$$
I=b_9(Q_-),\qquad Q_+=Q_-,\qquad
\psi_+=M_I\psi_-/\|M_I\psi_-\|.
\tag{1.5}
$$

The last expression is used only on a positive original branch. The terminal is literally $W(Q)=(b_{-1},\ldots,b_8)(Q)$ with all $1024$ labels. All original failure, refusal, stop and alarm coordinates remain, with their ideal zero masses. No inverse pulse, fractional pulse, reset, extra read, fork, preparation or internal phase intervention is an allowed operation.

**Definition 1.2 (joint task and resources).** For integers $H\ge0$ and $s\ge1$, allow every such program with at most $H$ total pulse calls. Its finite comparison coordinate $C$ contains $Q_0$, the chronologically ordered configuration at every pulse seam, both sides of the configuration-preserving intermediate read when present, the literal $I$ and terminal $W$, the unchanged externally specified requests, order and schedule metadata, and the original ideal failure coordinates. External schedules are fixed common inputs under the original waiting contract; waiting leaves the source unchanged. The metric is probability total variation,

$$
\operatorname{TV}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|
=\tfrac12\sum_c|\mu(c)-\nu(c)|
\tag{1.6}
$$

on the finite random coordinates. Thus every event in the whole chronological tuple is a consumer. Any $Y_{\rm cut}$ that is a function of its already occurred prefix can be retained jointly with the future and reports. Precise internal jump times, an arbitrary original hidden-past variable, and the exact vector graph are not replaced by finite seam coordinates.

A sampler receives $H,s$ and each legal request only when it arrives, plus fresh independent fair bits. Its predictive workspace counts every retained configuration, amplitude coefficient, controller flag, counter, random draw and arithmetic temporary. Retained input, rereadable output, history, physical clock and work are separate resources. An output stream may be discarded after emission; any part still readable by the continuation counts as retained memory.

## 2. A computed support-preserving reencoding

**Definition 2.1 (integer centers and quantizer).** Write $h_p=2^{-p}$ for $p\ge8$. A center is the nonzero vector

$$
n(q)=A_q+B_q\zeta,\qquad A_q,B_q\in\mathbb Z,\qquad
|A_q|,|B_q|\le4\,2^p.
\tag{2.1}
$$

It represents $n/\|n\|$ mathematically; that normalizer is not a stored exact real. A valid runtime configuration additionally has $n(q)\ne0$. After a read with record $i$, the center is supported in $M_iE$.

For a nonzero vector $a\in\mathbb C^E$, uniquely write

$$
a(q)/\|a\|=c_q+d_q\zeta,\qquad c_q,d_q\in\mathbb R.
\tag{2.2}
$$

Round $c_q,d_q$ to nearest multiples of $h_p$, breaking a midpoint tie toward the smaller real number. If $a(q)=0$, use the pair $(0,0)$ exactly. If $a(q)\ne0$ but both rounded coefficients vanish, replace that pair by $(h_p,0)$. Call the resulting vector $w$. Let $\mathcal N_p(a)=w/h_p$ be the stored integer center and $R_p(a)=w/\|w\|$ its direction. This is numerical reencoding with $q$ unchanged, not a source operation.

**Theorem 2.2 (effective native fixed-height quantizer).** For every nonzero $a$,

$$
\operatorname{supp}\mathcal N_p(a)=\operatorname{supp}a,\qquad
\|R_p(a)-a/\|a\|\|_2\le\eta_p,
\qquad \eta_p=4\sqrt d\,2^{-p}.
\tag{2.3}
$$

Its integer coefficients obey (2.1). For the actual arguments $a=K_jn$ and nonzero $a=M_in$, $\mathcal N_p(a)$ is computable by finite integer arithmetic, with $O(dp)$ working bits and $O(dp^3)$ schoolbook bit work. This includes exact zeros, signs, midpoint ties and height reset; neither a sign oracle nor an enumerated codebook is supplied.

Proof. Since $\sin\alpha>1/2$, the real-linear inverse of $(c,d)\mapsto c+d\zeta$ gives $|c_q|,|d_q|<3$ for $|a(q)|/\|a\|\le1$. The ordinary rounding error in a complex coordinate is at most $h_p$. In the exceptional replacement, $|c_q|,|d_q|\le h_p/2$, so the error is at most $2h_p$. Consequently

$$
\|w-a/\|a\|\|\le2\sqrt d\,h_p<1.
\tag{2.4}
$$

The vector $w$ is nonzero. A rounded coefficient pair represents zero only if both coefficients vanish, since $\zeta$ is nonreal; the replacement proves exact support preservation. Also $|A_q|,|B_q|\le3\,2^p+1\le4\,2^p$. Finally,

$$
\|w/\|w\|-a/\|a\|\|
\le|1-\|w\||+\|w-a/\|a\|\|
\le2\|w-a/\|a\|\|,
\tag{2.5}
$$

which proves (2.3).

For effectivity use the exact integral order from [finite precision, §2.1][FP],

$$
\mathcal O=\mathbb Z[y,\zeta],\qquad
y^4+y^2-1=0,\quad \zeta^2+y^2\zeta+1=0,\quad
\overline\zeta=-y^2-\zeta.
\tag{2.6}
$$

Its integral basis is $1,y,y^2,y^3,\zeta,y\zeta,y^2\zeta,y^3\zeta$. In this basis equality is coefficient equality; a real element has no $\zeta$ part. The supplier's coefficient norm satisfies

$$
\|uv\|_c\le8\|u\|_c\|v\|_c,\qquad
\|\bar u\|_c\le3\|u\|_c.
\tag{2.7}
$$

Every native endpoint entry belongs to this order. On an active pair the entries are $-y^2$, $-y^3-y\zeta$ and $(1-y^2)(\zeta-1)$, while a singleton entry is $\zeta$ or $\zeta^2$. Their largest coefficient row sum is six. Thus (2.1) gives

$$
\max_q\|a(q)\|_c\le384\,2^p<2^{p+9}
\tag{2.8}
$$

for either argument of the quantizer. Write $a(q)=A_q(y)+B_q(y)\zeta$ and $S=\sum_q|a(q)|^2>0$. Both $A_q,B_q$ are reduced real quartic-field polynomials, and $c_q=A_q(y)/\sqrt S$, $d_q=B_q(y)/\sqrt S$. A rounding-boundary comparison is the sign of

$$
2^{p+1}A_q(y)-(2k+1)\sqrt S,
\tag{2.9}
$$

or the same expression with $B_q$. Signs of its two real terms settle the same-sign case; when they oppose, one squaring reduces the decision to a reduced polynomial in $y$. Opposite signs together with exact zero of the squared polynomial decide equality. A coordinate is tested for exact zero before rounding. Binary search over $|k|\le4\,2^p+1$ uses $O(p)$ such comparisons per coefficient and implements the declared tie rule.

Here are explicit common precision bounds also sufficient for §3's phase calculations. Set

$$
B=16p+512,\qquad t=5B+32.
\tag{2.10}
$$

Every reduced polynomial whose sign is used has coefficient norm less than $2^B$. To check this accounting, (2.7)–(2.8) give $\|S\|_c<2^{2p+30}$. Squaring (2.9) needs coefficient norm less than $2^{4p+42}$. For phase thresholds, finite precision (2.14) with raw size $2^{p+9}$ bounds $D,b,E$ respectively by $2^{2p+35},2^{2p+37},2^{4p+76}$. Taking its common height $4p+100$ in (2.15)–(2.16), with threshold precision $p$, bounds the final sign polynomial by $2^{14p+315}<2^B$. These bounds cover the accompanying zero and derivative tests as well.

For a nonzero reduced $P\in\mathbb Z[X]$ of degree at most three and $\|P\|_1<2^B$, the other conjugates of $y$ are $-y,i/y,-i/y$, all of modulus less than two. The nonzero algebraic-integer norm therefore gives

$$
|P(y)|>2^{-3B-9}.
\tag{2.11}
$$

On $[0,1]$, $|P'|\le3\,2^B$. Isolate the positive root of $X^4+X^2-1$ on $[0,1]$ by $t$ dyadic bisections. This polynomial is strictly increasing there, so integer evaluations decide every bisection. At the midpoint the error in $P$ is at most $3\,2^{B-t}$, below half the bound (2.11). The sign is therefore exact. Reduced zero polynomials are recognized before isolation is used. This is the supplier's norm-separation method applied at height $O(p)$, not height proportional to the elapsed word.

All operands, cleared fixed-degree denominators, interval endpoints and multiplication scratch have $O(p)$ bits. One isolation costs $O(p^3)$ schoolbook operations and can be shared; each later sign comparison costs $O(p^2)$. The $O(dp)$ comparisons prove the stated $O(dp^3)$ work bound with $O(dp)$ bits. Norms and radicals occur only in these finite comparison expressions. The next center contains just (2.1)'s integer pairs, so no normalization radical or coefficient-height tower is retained. ∎

## 3. Causal native transitions and valid entrances

**Definition 3.1 (recurrent sampler).** Initialize exactly

$$
n=2^p e_{q_{\rm r}},\qquad q=q_{\rm r}.
\tag{3.1}
$$

Store also the stage, record flag, currently arrived address, call counter and parameters. There is no supplied cut law, posterior, hidden configuration, unarrived suffix or precomputed transition table.

On an arrived address $j$, compute the original endpoint conditional kernel from the entrance $n$ using finite precision §2.2. In the actual block containing $q$, put $v=Pn$, $u=(I-P)n$ and

$$
\begin{gathered}
p_0(t)=b+2\operatorname{Re}(De^{i\alpha t}),\qquad
b=|u_0|^2+|v_0|^2,\quad D=\overline{u_0}v_0,\quad E_D=D\bar D,\\
p_0'(t)=-2\alpha\operatorname{Im}(De^{i\alpha t}).
\end{gathered}
\tag{3.2}
$$

The opposite mass is the constant block mass minus $p_0(t)$. When $p_0$ increases, $q_1$ is the departing row and $q_0$ is absorbing; when $p_0$ decreases, $q_0$ is the departing row and $q_1$ is absorbing. There are at most two monotone phases. The exact signs of $\operatorname{Im}D$ and $\operatorname{Im}(D\zeta)$ decide an interior extremum; its value, when present, is $b\pm2\sqrt{E_D}$. Zero endpoint derivatives are endpoint turns, not additional phases. A departing mass decreasing from $d_0>0$ to $d_1\ge0$ has flip probability

$$
f=1-d_1/d_0.
\tag{3.3}
$$

An absorbing row or a singleton has flip zero. For each phase replace $f$ by

$$
\widehat f=2^{-p}\lfloor2^pf\rfloor,
\tag{3.4}
$$

retaining $f=0,1$ exactly, and use a fresh uniform $p$-bit integer to make this Bernoulli decision. The two phases use the same original entrance vector $n$, with the phase configuration updated between decisions. They are computations of a whole unit-pulse endpoint, not common physical control times across different blocks. Having updated $q$, replace $n$ by $\mathcal N_p(K_jn)$, with $q$ unchanged by reencoding.

At the original read report $I=b_9(q)$ and keep $q$. Replace $n$ by $\mathcal N_p(M_In)$. At the terminal return exactly $W(q)$. A constant-current-zero block uses identity. Unsupported rows, required only to make a finite table total, are completed by identity; they are not conditional source rows and will not be invoked from the valid carrier. A zero vector has no quantizer value. No additional failure or rejection output is used.

**Theorem 3.2 (totality on the valid carrier).** For every arrived legal original request sequence, the sampler of Definition 3.1 preserves $n\ne0$ and $n(q)\ne0$. After a read it remains in the reported record sector under every original future address. All invoked native conditional rows and projected vectors are positive entrances. Its arithmetic, including every phase threshold, has the bounds of Theorem 2.2. It uses at most $2Hp$ fresh bits.

Proof. The initialization has the asserted support. A positive phase entrance can end only in the support of its exact phase exit vector: a receiver of positive flip mass is increasing and has positive endpoint mass; a departure with zero endpoint mass has $f=1$, preserved exactly by (3.4). Flooring can remove a possible flip but cannot create an impossible flip. If $0<f<1$, both original outcomes already have positive endpoint mass. Constant and singleton rows are identities on positive support. These facts cover isolated nodes and endpoint turns without ever evaluating a zero-denominator row. In particular $q$ after the last phase lies in $\operatorname{supp}(K_jn)$. The quantizer preserves that immediate support by Theorem 2.2, so the next valid entrance follows.

At the read, $n(q)\ne0$ and $b_9(q)=I$ give $(M_In)(q)=n(q)\ne0$. No zero projection is passed to the quantizer. The other record projection can be zero; it is not normalized or executed on this history. Projection and reencoding remain in $M_IE$, and all seven original future addresses preserve that sector. The pure update has exactly the projected direction, with $q$ unchanged before its numerical reencoding.

Finite precision (2.12)–(2.16) gives the exact native phase holding and radical-threshold expressions from the raw vector. For example comparing $f$ with $k/2^p$ requires the sign of $(2^p-k)d_0-2^pd_1$, with known positive $d_0$; its one-radical sign is reduced by the same sign-before-squaring rule as (2.9). The bounds (2.10) apply to every center, including centers not exactly reachable by an original word. They follow from the order, height and fixed block formulas, not an original-word promise. Each call requires at most two draws; reencoding and the read require no randomness. This proves totality and the bit bound. ∎

## 4. Square domination without a square-law runtime

**Definition 4.1 (comparison shadows).** For a fixed program, first consider the mathematical rounded process using Definition 3.1's exact native phase probabilities instead of (3.4). Its center updates and read remain unchanged. Given the arrived word and the record, the center is deterministic: pulse reencoding depends on $n,j$ alone, and only the literal read selects a record projection using $q$. Thus there is one center direction per record branch, irrespective of the preceding hidden configuration history. Its configuration need not have the center's square marginal.

For the proof let $z$ initially be $e_{q_{\rm r}}$, evolving by the exact original unitaries. At the read replace it by the two subnormalized vectors $z_i=M_iz$. These have their true unconditional branch norms; never normalize a zero $z_i$. Let $w$ initially be the same ready vector. It evolves by the same unitaries, but at each reencoding it keeps its norm and takes the new center's direction. At the read split it into $M_0w,M_1w$ first, then reencode each nonzero component keeping that component's norm. A zero shadow stays the zero vector. At every stage

$$
\sum_i\|z_i\|^2=\sum_i\|w_i\|^2=1,
\qquad E_{\rm vec}=\left(\sum_i\|z_i-w_i\|^2\right)^{1/2},
\tag{4.1}
$$

with one index before the read. Positive $w_i$ have exactly the runtime center directions on branch $i$. The shadows, their norms and all submeasures below are comparison objects; the sampler never receives or computes them.

Let $L,\widetilde L$ be the true and exact-phase rounded laws of their whole configuration histories to the current stage, retaining prior seams and the read. A common submeasure $\beta\le L,\widetilde L$ is square dominated when its current endpoint marginal obeys

$$
\beta(i,Q=q)\le\min\{|z_i(q)|^2,|w_i(q)|^2\}.
\tag{4.2}
$$

Neither equality in (4.2) nor any conditional Born law given the retained past is assumed.

**Theorem 4.2 (native pulse and reencoding invariant).** Starting with mass one at the deterministic ready, a square-dominated common submeasure can be continued through every original pulse, center reencoding and the literal read. During a pulse its loss is at most $16b_*E_{\rm vec}$, where $E_{\rm vec}$ is constant under that pulse. At each reencoding its loss is at most $\eta_p$ and $E_{\rm vec}$ increases by at most $\eta_p$. The read's splitting before reencoding loses no common mass and leaves $E_{\rm vec}$ unchanged. These assertions include zero and arbitrarily rare true record branches.

Proof. The homogeneous form of XI54.3's matching-graph estimate is, for arbitrary possibly subnormalized $z,w$,

$$
\sum_{r:z(r)w(r)\ne0}\min(|z(r)|^2,|w(r)|^2)
  \sum_{q\ne r}|\sigma^z(q\mid r)-\sigma^w(q\mid r)|
\le8b_*(\|z\|+\|w\|)\|z-w\|.
\tag{4.3}
$$

For clarity the normalization change in this reuse is explicit. On a directed active edge write $a=z(r)$, $A=w(r)$, $b=z(q)$, $B=w(q)$ and $c=(H_j)_{qr}$. If $0<|a|\le|A|$, the positive-part inequality gives the XI(54.7) bound

$$
|a|^2|\sigma^z-\sigma^w|
\le2b_*|a||b-B|+6b_*|B||a-A|.
\tag{4.4}
$$

Exchange $z,w$ for the other ordering. The bound is at most
$2b_*(|z(r)|+|w(r)|)|z(q)-w(q)|+6b_*(|z(q)|+|w(q)|)|z(r)-w(r)|$.
The native neighbor map is a permutation on the matched vertices. Cauchy–Schwarz on the two sums gives (4.3). Singletons contribute zero. A one-sided-zero departure contributes zero and its undefined rate is not evaluated. This extends the supplier's last normalization step; it does not postulate uniform bounded rates.

For the families in (4.1), sum (4.3) over $i$. Since

$$
\left(\sum_i(\|z_i\|+\|w_i\|)^2\right)^{1/2}\le2,
\tag{4.5}
$$

Cauchy–Schwarz bounds the total by $16b_*E_{\rm vec}$. Common unitaries preserve this aggregate norm distance, even when the branch norms differ.

To propagate $\beta$ through a pulse use XI54.5's common-risk construction, now starting from the domination (4.2). Where both occupied amplitudes are nonzero put

$$
\begin{aligned}
c_t(q\mid r)&=\min(\sigma_t^z(q\mid r),\sigma_t^w(q\mid r)),\\
D_t(r)&=\sum_{q\ne r}|\sigma_t^z(q\mid r)-\sigma_t^w(q\mid r)|,\\
\ell_t(r)&=\sum_{q\ne r}\max(\sigma_t^z(q\mid r),\sigma_t^w(q\mid r))
=\sum_{q\ne r}c_t(q\mid r)+D_t(r).
\end{aligned}
\tag{4.6}
$$

For each ordered genuine jump list, use jump factors $c_t$ and holding factor $\exp(-\int\ell_t(Q_t)dt)$, multiplying the entire retained past submeasure. Each factor is dominated by the corresponding continuation density in either process. Thus this is a common submeasure on full configuration histories, not a new source operation.

At any intermediate time, its marginal $\beta_t(i,r)$ is bounded by propagation of its entrance marginal through either positive-entrance kernel. Propagate separately the inequalities $\beta(i,q)\le|z_i(q)|^2$ and $\beta(i,q)\le|w_i(q)|^2$. The two square references are equivariant by III146.1 and scale by their fixed squared norms. Consequently

$$
\beta_t(i,r)\le\min(|z_i(t,r)|^2,|w_i(t,r)|^2).
\tag{4.7}
$$

This argument concerns propagation from the submeasure and the two reference laws; it needs no square marginal for $\widetilde L$.

The node passage is precisely the local-risk extension in XI54.5, with (4.7) in place of its initial square equality. Each nonzero active amplitude is a common phase times $A+B e^{i\alpha t}$, so there are finitely many deterministic nodes per pulse. As one departure approaches a node, $\ell$ dominates that side's outgoing rate, whose integrated hazard exhausts survival by [Georgii–Tumulka, §3 Lemma 2(b)][GT]. Common jumps are dominated by each reference's jumps, so cannot create mass at a zero target. The conditional-positive-entrance kernel of IV278.1 supplies each segment without replacing the entrance wave. The native current has at most one turn, so every common surviving path has at most two jumps. There is no explosion term or node/seam atom. Hence all lost common mass is the nonnegative risk integral

$$
\int_0^1\sum_{i,r}\beta_t(i,r)D_{i,t}(r)\,dt
\le16b_*E_{\rm vec}.
\tag{4.8}
$$

One can first integrate on compact positive-support subintervals and then take the monotone limit to the finite nodes; zero survival and finite jumps exclude an additional boundary loss. Zero shadow or true branches carry no $\beta$, and require no conditional direction. This proves the pulse step.

For a reencoding write $w_i^+=\|w_i^-\|R_p(a_i)$, where $a_i$ has the direction of $w_i^-$ and comes from the corresponding runtime center. Set $w_i^+=0$ if $w_i^-=0$. Theorem 2.2 implies

$$
\left(\sum_i\|w_i^+-w_i^-\|^2\right)^{1/2}\le\eta_p.
\tag{4.9}
$$

Thus the triangle inequality increases $E_{\rm vec}$ by at most $\eta_p$. Keep $q$ and all history coordinates unchanged. In the proof alone, let $\gamma_i(q)=\beta(i,q)$. Multiply the entire $(i,q)$ history slice by

$$
\min\{1,|w_i^+(q)|^2/\gamma_i(q)\}
\tag{4.10}
$$

when $\gamma_i(q)>0$; a zero slice remains zero. This thins $\beta$ without changing either probability law. Its removed mass is at most

$$
\sum_{i,q}(|w_i^-(q)|^2-|w_i^+(q)|^2)_+
\le\sum_i\|w_i^-\|^2\eta_p=\eta_p.
\tag{4.11}
$$

Here the square-mass distributions of two unit vectors differ in TV by at most their Euclidean distance, the same coordinate-measurement inequality used in XI54.4; equal branch norms allow its homogeneous use. The thinned submeasure satisfies (4.2) with $w^+$ and remains below both history laws. No configuration is killed, reset or resampled by (4.10).

At the read the same matched $q$ gives the same literal $I$, with $q$ unchanged. Replace $(z,w)$ by $(M_0z,M_1z)$ and $(M_0w,M_1w)$. Orthogonal projection into this direct sum is an isometry, so (4.1)'s distance is unchanged, the sums of squared norms remain one, and $\beta$ splits by the same $q$ without loss. Apply (4.9)–(4.11) to the subsequent reencoding of the nonzero shadow projections. The runtime center has exactly their directions. If $z_i=0$, the original branch and its common submeasure are zero; no original conditional state is assigned, even if the approximate process has small positive mass there. If $M_iw=0$, the valid-entrance theorem forbids that report in the rounded process. In particular no estimate has been divided by a rare branch probability. This proves the invariant through the read and completes the theorem. ∎

## 5. Logarithmic predictive workspace for the whole finite joint law

**Theorem 5.1 (from-ready recurrent finite-memory approximation).** Let $H\ge0$, $p\ge8$ and $s\ge1$. For every original legal $\mathsf T(a)$ with $|a|\le H$, and every original legal $\mathsf R(a,h)$ with $|a|+|h|\le H$, Definition 3.1 defines a causal finite-bit sampler initialized by (3.1). If $L_C$ is the original law of Definition 1.2's entire finite tuple and $\widehat L_C$ its sampled law, then

$$
\operatorname{TV}(L_C,\widehat L_C)
\le\min\{1,(H+1)(1+16b_*H)\eta_p+2H\,2^{-p}\}.
\tag{5.1}
$$

In particular the choice

$$
p=s+2\lceil\log_2(H+1)\rceil+12
\tag{5.2}
$$

gives TV at most $2^{-s}$. All branch masses are unconditional. The bound is uniform over each fixed legal word of the indicated total length and is consistent on actually common arrived prefixes. No conditional error bound after an arbitrarily rare record is asserted.

The predictive workspace is $O(dp+\log(H+1))$ bits, deterministic arithmetic work is $O(d(H+1)p^3)$ schoolbook bit operations, and fresh fair bits are at most $2Hp$. These bounds exclude neither a retained program nor a retained output archive: each is separately charged by its actual retained length. No table indexed by the exponentially many centers is stored.

Proof. First compare the original process with the exact-phase rounded process in Definition 4.1. Start their common submeasure with mass one at ready. There are at most $H+1$ reencodings: one per pulse and one intermediate read, with none needed at initialization or terminal. Theorem 4.2 gives $E_{\rm vec}\le(H+1)\eta_p$ during every pulse, since common unitaries preserve it and the read split is an isometry. Thus pulse losses total at most $16b_*H(H+1)\eta_p$, while all proof-thinning losses total at most $(H+1)\eta_p$. There is common full configuration-history mass at least one minus their sum. Probability measures with common submeasure of mass $1-e$ have probability TV at most $e$. Projecting these history laws to $C$ proves the first part of (5.1).

It remains to compare the exact-phase rounded process with the finite-bit sampler. On a common occurred seam history they have the same center, $q$, stage, record and arrived input. Every phase Bernoulli row differs by less than $2^{-p}$, including exact agreement at zero and one. The usual finite-kernel composition estimate, reused from [V64, Proposition 6.5][V64] and finite precision §2.4, adds at most $2H\,2^{-p}$ to the *whole chronological tuple* distance. Deterministic center updates, original read and terminal are common functions on those histories. Their support invariant ensures all invoked exact rows exist. This final comparison is ordinary kernel rounding; the source-specific argument is Theorem 4.2, which supplies the missing bridge at nonsquare rounded cuts. The triangle inequality proves (5.1). Neither comparison conditions on success, a nonzero record, or a terminal event.

Since $b_*<2$ and $4\sqrt{89}<38$, the untruncated bound in (5.1) is at most

$$
\{38(H+1)(1+32H)+2H\}\,2^{-p}
\le1218(H+1)^2\,2^{-p}.
\tag{5.3}
$$

Together with (5.2) and $1218<2^{12}$ this is at most $2^{-s}$. This also covers $H=0$; the actual empty-pulse run is exact.

For resources, fixed-width sign-magnitude storage of all center pairs needs at most $178(p+4)$ bits. Configuration $q$ needs seven bits, the native address and stage/record flags constant space. The call counter, horizon and precision parameters need $O(\log(H+1)+\log(p+1))$ bits. Center updates, exact reduced raw coordinates, one shared root interval, the threshold operands and fixed-degree multiplication scratch add $O(dp)$ bits by Theorem 2.2. Even holding the old and new vectors simultaneously obeys this bound. One current $p$-bit draw is included. No analytical shadow, branch norm, posterior or proof submeasure is retained.

There are $O(d(H+1))$ fixed-order raw updates, $O(dp(H+1))$ sign comparisons, and one $O(p^3)$ root isolation can serve all of them using (2.10). Each comparison costs $O(p^2)$, proving the displayed work bound. Loop and bit-draw work $O(Hp)$ is absorbed. The fixed native matrices, carrier enumeration, labels, integer reductions and control logic are a constant-size program independent of $H,s$. The bound charges arithmetic on $O(p)$-bit integers as bit work, rather than one unit per exact algebraic operation.

The only stochastic operations are the at most two $p$-bit draws per arrived pulse. They are consumed phase by phase and discarded. A controller can reserve two draw positions per call to give identical randomness on common executed prefixes, discarding any unused positions. This defines a causal family without a future-word input. It is not a reproduction of the original simultaneous coupling of all unexecuted programs by its exponential seeds. Uniformity in (5.1) is a per-program statement on the occurred joint consumer.

A stored address program costs $O(H)$ additional bits under fixed native encoding; the online version needs only the current arrived address. Streaming the seam tuple takes $O(H)$ output symbols. Retaining its configuration coordinates requires $\Theta(H\log d)$ bits for a plain tuple representation, plus request framing and any retained schedule metadata. If only the original readable $I,W$ are exposed, proof seam variables need not be stored or made into new source read ports. Arbitrary externally supplied metadata must be read, forwarded or retained at its actual representation cost; it is not encoded for free by the counter. This completes the finite-bit and work accounts. ∎

**Definition 5.2 (the precise improvement).** For this same from-ready finite-seam task, the exact raw compiler and source-initialized streaming reuse keep native raw coefficient height $O(H)$ and precision $r$, with $O(H+r)$ working bits at fixed $d$ and error at most $2H2^{-r}$. Their holding kernels and arithmetic are reused here. Theorem 5.1 resets coefficient height after every call; for accuracy $2^{-s}$ it keeps $O(d(s+\log(H+1)))$ predictive bits. This is an improvement of that sufficient workspace account, not a matching lower bound or an optimal state count. If the consumer retains a linear history or a whole input tape, the theorem does not reduce that additional storage to logarithmic size. Exact original word support and uniform accuracy of every positive conditional row remain stronger services of the exact raw construction.

## 6. Native paired distinctions and recovery boundaries

**Theorem 6.1 (why the retained configuration and the domination repair matter).** There are two positive actual hidden entrances with the same original wave and same literal intermediate report, but different original continuation rows. Moreover, reencoding a nearby wave while keeping the actual configuration need not produce a square-compatible rounded cut. Thus neither replacing continuation by a Born terminal marginal nor directly iterating XI54.6 at rounded runtime cuts supplies Theorem 5.1.

Proof. Reuse the actual ready discriminator [finite precision, Theorem 3.1][FP]. For $\mathsf R((1),(1))$ put $q_0=q_{\rm r}$, $q_1=\{1,3,7\}$, $w_j=W(q_j)$ and

$$
p_*=3x-1,\qquad d_*=x^2/4.
\tag{6.1}
$$

After the first full address-$1$ pulse, $I=0$ surely and $Q_{\rm cut}$ has masses $1-x,x$ on $q_0,q_1$. Both entrances have the same wave. The next *full positive* address-$1$ pulse gives

$$
T(q_0,w_1)=p_*(1-d_*),\qquad T(q_1,w_1)=1-d_*,
\qquad (1-x)T(q_0,w_1)+xT(q_1,w_1)=p_*.
\tag{6.2}
$$

The two rows differ strictly. Replacing both by the Born terminal marginal $p_*$ changes the joint event $\{Q_{\rm cut}=q_1,W=w_1\}$ by

$$
x(1-d_*-p_*)>0.
\tag{6.3}
$$

An independent Born resampling of $Q$ at the cut is also invalid even with *zero wave error*: retaining the old past coordinate $Y=Q_{\rm cut}$ gives $Y=Q$ surely in the original process, whereas the independent resampling makes $\Pr(Y\ne Q)=2x(1-x)>0$. The empty future already detects this if the cut configuration is retained; the future (6.2) also detects the lost dependence using $Y$ and the original terminal. This is a mathematical joint-law witness, not a new hidden read permission.

To see the separate rounded-cut issue, let $u$ be that cut wave. Choose a unit vector $v_\delta$ with the same coordinate phases and square masses $(1-x-\delta,x+\delta)$ on these two paths, for $0<\delta<1-x$. Then $\|v_\delta-u\|\to0$, but merely replacing the wave description and retaining $Q$ leaves its masses at $(1-x,x)$. XI(54.3)'s marginal premise fails exactly for every $\delta>0$. This is a diagnostic pair of descriptions, not an assertion that every such $v_\delta$ is produced by the specified grid. Theorem 4.2 repairs precisely this missing premise by domination and paid proof thinning; it never asserts square equality for the rounded runtime. All other $87$ configurations, original labels and record slices remain in the source, with their actual zero masses in this witness. ∎

**Definition 6.2 (support, time and acquisition).** The quantizer preserves support of its *immediate argument*. It does not preserve the exact original word support across recurrent approximation: a small change of amplitudes may destroy a later exact cancellation and assign mass to an originally null event. All such mass is included in the unconditional joint-TV error (5.1). Demanding exact original null-event preservation is an additional task, and is not justified merely by requesting the finite tuple of Definition 1.2. The original labels, legal edges, currently represented positive entrances and ideal failure convention are nevertheless preserved exactly by Theorem 3.2.

The source still undergoes its original number of unit-pulse intervals, with waiting governed by its original schedule. The algorithm's phase computations neither implement internal-time interventions nor sample genuine jump times, and its bit-work bound is not a physical clock, energy, hardware or randomness-source bound. A mathematical law sampler from a specified ready state does not acquire or continue an independently running original $Q$. In particular it does not recover an unknown actual $Y_{\rm cut}$, posterior or source innovation seed from reports.

A common measurable readable archive kernel on the actually same request, order, schedule and report inputs can be attached to the compared finite laws by the usual TV contraction. If the source coordinates remain, that extension preserves their TV by projection back. An executable archive extension still requires its actual causal code, supplied inputs, innovations, retained storage and output/time costs. A kernel depending on internal jump times or other absent hidden coordinates is not a kernel of the finite tuple and cannot be attached by this argument. Nor is a free arbitrary measurable-kernel service implied.

[XI55–56][XI] and [V64][V64] retain their exact continuous-history and vector-graph boundaries: distinct deterministic vector graphs can have TV one in the common exact-vector coordinate, even when their rays are close. Here continuous reference paths serve only a comparison proof, and the effective sampled output is the finite tuple. Space is represented by the original adjacency blocks and sectors, continuation by their original unit pulses, boundary by the literal projections/reports, and predictive memory by $(n,q)$ and charged controller state. The theorem supplies this finite approximate forward representation and preserves finite past/future correlations. Inverse recovery, minimal relations among all four structures, source-owner realization, arbitrary hidden-past acquisition and unrestricted unbounded continuation remain separate mathematical or realization obligations.

## 7. Mathematical suppliers and scope of attribution

**Definition 7.1 (attribution of the construction).** Theorems 2.2–5.1 form a `repo-derived` source-specific connection: a computable support-preserving fixed-height grid, valid native entrance recurrence, square-dominated full-history comparison across nonsquare reencodings and the original rare read, and the resulting complete finite-joint/workspace bound. Theorem 6.1 applies the already supplied ready witness to the retained-state and square-compatibility distinction. No worldwide novelty, optimality or kernel certification is asserted for these ordinary mathematical proofs.

[Finite precision, §§2–3][FP] supplies the integral order, exact raw pulse/projection arithmetic, sinusoidal phase factorization, exact radical sign method, support-safe dyadic flips and ready paired rows. [XI54.3–54.5][XI] supplies the occupied-rate calculation and node-safe common-risk construction; Theorem 4.2 explicitly proves the new invariant needed after reencoding rather than borrowing XI54.6's square-compatible cut hypothesis. The direct-sum orthogonal identity, coordinate-measurement distance inequality, common-submeasure principle, norm separation and finite-kernel composition are standard intermediate tools; they are not independent new appendices.

The primary `literature-attested` source premises are [Dürr–Goldstein–Tumulka–Zanghì, *Bell-Type Quantum Field Theories*, §2.7 (23)–(29)][DGTZ] and [Georgii–Tumulka, *Global Existence of Bell's Time-Inhomogeneous Jump Process for Lattice Quantum Field Theory*, Assumption A, Theorem 1 and §3 Lemma 2][GT]. The parameter correspondence is $P_q=|q\rangle\langle q|$ and $H_{\rm GT}=2H_j$, matching their $\hbar=2$ to this source's $\hbar=1$. They supply minimal rates, the square reference, integrated holding and node safety, not a rounded-runtime finite-bit theorem.

[Moore–Crutchfield, *Quantum Automata and Quantum Grammars*, §2.4][MC] represents an acceptance function by a finite real generalized-stochastic linear representation. Its matrices are not thereby stochastic kernels, and a real register is not a fixed-bit memory budget. It supplies neither these conditional configuration histories nor this consumer. Finite-dimensionality alone cannot replace Theorems 3.2 and 4.2.

The repository declaration `QuantizedWordApproximation.quantized_word_approximation` assumes supplied centers, a quantizer and global deterministic Lipschitz update/readout hypotheses. `FiniteRuntimeReduction.finite_precision_runtime_reduction` counts an already supplied finite deterministic product state. Neither constructs native conditional phase probabilities or establishes square domination after reencoding. The private `OriginalControlMarkedJump.Leg.survival_formula` concerns a different five-mode positive linear leg; it is not the present sinusoidal native pulse. These exact scopes are not used as additional hypotheses or as fresh formal evidence.

At pinned mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, number-field norms, inner-product inequalities and `Kernel.comp_apply`/`Kernel.comp_assoc` supply general infrastructure. Its `MeasureTheory.tvDist` is the full variation norm, with the with-density formula equal to an $L^1$ integral; (1.6) is half that norm for probability measures. The bounded comparison here concerns the cited native source, these quantization/runtime suppliers and their primary premises. It is not an exhaustive absence or priority claim about the Lean ecosystem or literature. All physical use of the original source, exact reads and fresh fair bits retains its own realization premises.

[III]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md
[IV]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md
[XI]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md
[FP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_FINITE_PRECISION_CONTINUATION_KERNELS.md
[V64]: AURIC_APPROXIMATE_RELATIONS_RIGIDITY_SQUARE_CALIBRATION_AND_QUANTUM_READOUT_STABILITY_V64.md
[GT]: https://arxiv.org/html/math/0312294v2
[DGTZ]: https://arxiv.org/html/quant-ph/0407116v1
[MC]: https://arxiv.org/html/quant-ph/9707031v1

## 追加锚（本行以下为增补区）
