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

## 8. Native positive-entrance marked refinement codec

**Definition 8.1 (marked law, names and supplied interfaces).** Fix $p\ge8$, any center $n$ of Definition 2.1, an occupied configuration $q$ with $n(q)\ne0$, and an already arrived original address $j$. The pulse law in this section is the positive-entrance minimal-current law with the *entire* entrance vector $n$ and original Hamiltonian $H_j$. Its existence and node-safe conditional meaning are those of III146.1, III160.1 and IV278.1. The new service is separate from Definition 3.1's dyadic phase sampler: its phase probabilities are exact. On composing pulses, its target is precisely Definition 4.1's exact-phase rounded process, with the same center reencodings and literal read. The target is not the unrounded original-word law.

For a genuine jump at pulse age $T\in(0,1)$, its canonical name is the consistent sequence

$$
\mathcal I_r(T)=
\left[2^{-r}\lfloor2^rT\rfloor,
      2^{-r}(\lfloor2^rT\rfloor+1)\right],\qquad r\ge1.
\tag{8.1}
$$

A precision-$r$ answer is the integer $\lfloor2^rT\rfloor$, its length and framing, equivalently that interval. Earlier answers are prefixes of later ones. The limiting name determines the genuine real $T$; a returned interval or one of its endpoints never replaces $T$ in the marked-history coordinate. The floor convention selects the right interval at a dyadic tie. Such ties will be null on each positive jump component. No-jump outcomes have a discrete tag and no time name. Retain the pulse index, phase and candidate labels, configurations immediately before and after each jump, seams, original read and terminal, and actual requests, order and schedule. A path with two jumps retains both times, even if its endpoint equals its entrance.

All $89$ complex coordinates, the $26+63$ decomposition, exterior bits, ready $\{3,7\}$, eleven prefix and seven future addresses, both records, all $1024$ terminal and $2048$ formal record/terminal labels, and every original finite $\mathsf T(a)$ and $\mathsf R(a,h)$ remain in scope. There is no uniform upper bound on the allowed finite word lengths, and the same external $h$ is used on both record branches. Original zero, failure, refusal, stop, alarm, archive and return coordinates remain, with their stipulated unconditional masses. The fair-bit service, native Hamiltonians and holding law, original read/update and quantizer are explicit premises. The names are a mathematical output interface, granting no additional physical read, preparation or control operation.

The original pulse age and the actual schedule are different coordinates. Keep the schedule unchanged, including any original exogenous schedule input and its same conditional kernel. Age names and that coordinate determine actual jump times. For an executable absolute-time query, an effective schedule realizer and every precision it actually uses must additionally be supplied and charged. No effective presentation of an arbitrary measurable schedule, reference or archive is part of Definition 8.1.

**Lemma 8.2 (uniform native mass guard).** Put

$$
A=64(p+64).
\tag{8.2}
$$

Use the original active-pair data $m,b,D,E_D$ of (3.2) and finite precision (2.11). On every nonconstant monotone phase, let $d_0>0$ and $d_1\ge0$ be its departing masses. Every nonzero member of $\{d_0,d_1,d_0-d_1,|D|\}$ lies strictly between $2^{-A}$ and $2^A$. Exact zeros and phase classification are decidable by the existing native algebraic arithmetic. Consequently each phase outcome of positive probability, jump or no jump, has probability at least $2^{-2A}$, uniformly over the entire valid-center domain.

Proof. This is a precision guard for time output, using the existing fixed-order arithmetic, rather than another endpoint compiler. Take the conservative raw size $S=2^{p+9}$ allowed by (2.8). The bounds of finite precision (2.14) give

$$
\|D\|_c<2^{2p+35},\qquad
\|b\|_c<2^{2p+37},\qquad
\|E_D\|_c<2^{4p+76},\qquad
\|m\|_c<2^{2p+25}.
\tag{8.3}
$$

Seam masses, turn masses and differences of two endpoints of a phase therefore have form

$$
\delta=a+c\sqrt{E_D},\qquad
 a\in\mathbb Z[y],\quad |c|\le4,\quad
 \|a\|_c<2^{2p+50}.
\tag{8.4}
$$

Here $c$ is an integer: a seam uses $c=0$, a turn uses $c=2$ or $-2$, and subtraction gives the stated range. For example the two turn rows are $b\pm2\sqrt{E_D}$ and $m-b\mp2\sqrt{E_D}$; seam squares use the original algebraic endpoint entries. The coefficient allowances in (8.4) cover the reductions, real parts and differences using (2.7). Since $0<y<1$ and the basis factors $y^k\zeta^e$ have modulus at most one,

$$
|a\pm c\sqrt{E_D}|<2^{2p+51},\qquad
\|a^2-c^2E_D\|_c<2^{4p+105}.
\tag{8.5}
$$

If the reduced polynomial $a^2-c^2E_D$ is nonzero, apply the quartic norm separation (2.11) at height $4p+105$. It gives

$$
|a^2-c^2E_D|>2^{-12p-324},\qquad
|a+c\sqrt{E_D}|>2^{-14p-375}.
\tag{8.6}
$$

The second inequality follows by division by the other factor's upper bound in (8.5). If the squared expression is zero, the expression in (8.4) is either zero or $2a$. Signs before squaring decide which; when nonzero, the original quartic norm bound for $a$ is stronger than (8.6). This includes $E_D=0$ and exact cancellations. A nonzero $|D|=\sqrt{E_D}$ is similarly bounded below by applying (2.11) to $E_D$ at height $4p+76$; its upper bound follows from (8.3). All these lower and upper exponents are dominated by $A$ for $p\ge8$.

The phase probabilities are $d_1/d_0$ and $(d_0-d_1)/d_0$. A positive numerator is among the guarded quantities, so each positive ratio is at least $2^{-2A}$. This is a statement about local phase outcomes from a fixed grid center. It is not a lower bound on an original record, a selected history event or an external reference event. ∎

**Lemma 8.3 (certified native survival evaluation).** Fix a decreasing phase $[a,\beta]\subseteq[0,1]$ with departing mass $d$ and $d_0=d(a)>0$. Define its clamped survival function by

$$
S(t)=\frac{d(\operatorname{clamp}_{[a,\beta]}t)}{d_0},
\qquad t\in[0,1].
\tag{8.7}
$$

There is one rational outward-enclosure procedure which, on a dyadic $t$ of denominator at most $2^r$ and integers $k\ge0$, $r\ge1$, encloses $S(t)$ with midpoint error and radius at most $2^{-k-4}$. It uses $O(L)$ scratch bits and at most $CL^6$ schoolbook bit operations, where

$$
L=16A+4(k+r)+128
\tag{8.8}
$$

and $C$ is an absolute native constant. It includes queries at turns, nodes and phase endpoints, without an exact transcendental sign or root oracle.

Proof. Reuse the exact classification and endpoint expressions in finite precision §§2.2–2.3 and Theorem 2.2. For $D=0$ no nonconstant phase is needed. Otherwise write $D=u+iv$. The signs of $v$ and $\operatorname{Im}(D\zeta)$ decide whether there is an interior turn and its direction. Zero endpoint derivatives are endpoint turns. The real and imaginary parts needed for quadrant selection have exact quartic-field signs: a positive fixed factor $\sin\alpha$ converts the imaginary coefficient to $v$, and $2\operatorname{Re}D=D+\overline D$. The value of $\sin\alpha$ itself is the positive square root of $1-x^2/4$. Thus all nontrigonometric data have fixed-degree algebraic presentations.

Here is a finite enclosure procedure for a turn, including its branch. Choose the argument $\theta\in[0,2\pi)$ of $D$ by its exact quadrant. Rotate $D$ by a signed multiple of $\pi/2$ until the rotated coordinates satisfy $u'\ge|v'|$ and $u'>0$. Compare magnitudes by their squares in $\mathbb Q(y)$, after deciding signs, and use a fixed rotation convention at a tie. Thus these choices use only the exact native signs. Then

$$
\arg(u'+iv')=2\arctan\frac{v'}{|D|+u'},
\qquad
\left|\frac{v'}{|D|+u'}\right|
\le\sqrt2-1<\tfrac12.
\tag{8.9}
$$

Undo the chosen rotation in the fixed quadrant convention. If an interior turn exists, the selected zero is $\theta+\alpha t=\ell\pi$: $\ell=1$ when $\operatorname{Im}D>0$, and $\ell=2$ when $\operatorname{Im}D<0$. The derivative tests already certify that this solution is in $(0,1)$. If there is no interior turn, the phase endpoints are $0,1$. Thus branch selection uses no numerical comparison with a transcendental boundary. An endpoint derivative equal to zero was recognized algebraically before this construction.

Positive algebraic square roots can be enclosed by rational bisection with signs before squaring; isolate $y$ as in Theorem 2.2. For the remaining constants and functions use

$$
\frac\pi4=4\arctan(1/5)-\arctan(1/239),\qquad
\arctan z=\sum_{h=0}^{N-1}\frac{(-1)^hz^{2h+1}}{2h+1}
       +\varepsilon_N,\quad
|\varepsilon_N|\le\frac{|z|^{2N+1}}{1-|z|^2},
\tag{8.10}
$$

and the real and imaginary parts of the bounded-angle enclosure

$$
e^{iz}=\sum_{h=0}^{N}\frac{(iz)^h}{h!}+\rho_N(z),\qquad
|\rho_N(z)|\le e^2\frac{2^{N+1}}{(N+1)!}\quad(|z|\le2).
$$

The sine/cosine arguments are the native angles $|\alpha t|<2$; the argument series in (8.10) has modulus less than $1/2$. Taking $N\ge16(L+1)$ suffices for the displayed exponential tail to be below $2^{-L}$: at least half the factorial factors are at least $(N+1)/2$, giving a geometric upper bound once $N\ge32$. The geometric tail in (8.10) requires only $O(L)$ terms as well. These reused elementary identities thus provide explicit truncation errors exponentially small in $L$. Evaluate terms by fixed-point recurrences with outward rounding, rather than retaining factorial-sized rational denominators. At each elementary operation retain its rounding enclosure; $O(\log(L+2))$ extra guard bits absorb the sum of $O(L)$ rounding errors. Integer parts have $O(A)$ bits. Bisection intervals, a constant number of series accumulators, loop counters and multiplication scratch consequently have $O(L)$ bits. Schoolbook multiplication and division of those registers, and the $O(L)$ stages, are bounded conservatively by $CL^6$. No table depending on the center or precision is supplied.

For completeness, the error budget is uniform even near a node or a turn. Set $\epsilon=2^{-L/2}$. Compute the algebraic operands, $\pi$, and the series with certified absolute errors at most $\epsilon$ before composition, using the available $L$-bit registers. Guarded nonzero denominators are bounded below by $2^{-A}$: these include $d_0$, $|D|$, and $|D|+u'$. Bisection for a square root uses additional $O(A)$ guard precision if its radicand is small. This fits in $L$, as do coefficient evaluation and the rounding guards just described. Once $L$ has the value (8.8), operand intervals for the positive denominators stay bounded away from zero.

The quotient in (8.9) has perturbation at most $C2^{2A}\epsilon$; $|\arctan'|\le1$ on this range. Division by $\alpha>1$ to obtain the turn changes only the absolute constant. Clamp is nonexpansive in its endpoints: replacing $a,\beta$ by their enclosed approximations changes its value by at most their largest error, without deciding whether $t$ equals an endpoint. Also

$$
|d'(t)|\le2\alpha|D|<2^{A+2}.
\tag{8.11}
$$

Using this bound for the argument error and $d_0>2^{-A}$ for the final division bounds the propagated survival error by $2^{8A+16}\epsilon$. This deliberately enlarged estimate covers the algebraic operand errors, quotient errors and final outward rounding as well. Equations (8.8) and $r\ge1$ give

$$
2^{8A+16}\epsilon
 =2^{-2(k+r)-48}<2^{-k-4}.
\tag{8.12}
$$

One may enlarge the resulting enclosure to the stated radius and intersect with $[0,1]$. There is no division by $d'(t)$, so a zero derivative at a turn causes no singular precision requirement. A mass can vanish at $\beta$; only the positive $d_0$ is a denominator. This proves the asserted certified evaluation and bounds. ∎

**Theorem 8.4 (exact local marked refinement).** For every input of Definition 8.1, one fixed fair-bit codec determines the exact discrete jump count and marks, with at most two jumps, and answers every finite sequence of interleaved integer-precision queries about its occurred jumps almost surely. Its answers are the compatible canonical names (8.1). Their decoded marked law is exactly the native positive-entrance pulse law for $n$. The assertion includes singletons, flat current, endpoint turns, interior turns, no-jump atoms and zero endpoint masses. It needs no prior numerical resolution of an earlier jump time to determine a later phase outcome or pulse endpoint.

Proof. On an original active pair use the phases already supplied by (3.2) and finite precision §2.2. A singleton or an identically zero current has no jumps. On a decreasing phase the departing row has integrated survival $d(t)/d_0$, and the receiver is absorbing until that phase ends. Supply one fresh uniform variable $U\in(0,1)$ by revealing independent fair binary digits only as needed. Its infinite bit string is a probability-space description, not a stored exact real. For $\tau=d_1/d_0$ the rule is

$$
\begin{cases}
\text{no jump},&U\le\tau,\\
\text{one jump at the unique }T\in(a,\beta)
       \text{ with }d(T)=d_0U,&U>\tau.
\end{cases}
\tag{8.13}
$$

The nonconstant phase is strictly decreasing in its interior. The law in (8.13) therefore has survival $d(t)/d_0$ and jump density $-d'(t)/d_0$ there, along with its no-jump atom $\tau$. When $d_1=0$ the jump occurs strictly before the node almost surely. When a configuration is receiving it stays fixed within that phase; no artificial jump is placed at a turn or seam. Positive entrance and exit support follow from these original phase rows, as in Theorem 3.2 with exact probabilities.

This construction respects the original candidate indexing of III145.2(4). If the supplied exponential innovation is $E_{\rm call,c}$, take $U_{\rm call,c}=e^{-E_{\rm call,c}}$. It is uniform, and crossing its integrated hazard is exactly (8.13). An initially receiving row has zero hazard until a possible turn, so its first candidate starts departing there. After a first jump the new row has zero hazard until that turn; the next original candidate is still unused and independent. Its integrated risk then starts from the deterministic second-phase mass of that row, computed from the same entrance pair. If a departing row has no jump in the first phase it becomes receiving after the turn, and cannot have a later jump in that pulse. Thus at most two candidates are relevant. Their labels count genuine next-jump candidates, not blindly the two phase numbers. In particular, zero-hazard waiting does not consume a new candidate. This also explains why no unresolved first timestamp is an input to the second decision. The construction gives the same integrated-risk map when those actual original innovations are supplied; fresh bits alone supply its occurred-history law and do not acquire an independently running source's seeds or assert a new coupling of unexecuted programs.

For an actual finite computation, retain the binary prefix of $U$ and its dyadic interval. Decide $U\le\tau$ by increasing that prefix until it is separated from $\tau$, using the exact radical comparisons of finite precision §2.3 on the two interval endpoints. Handle $\tau=0,1$ exactly. On a jump, start canonical bisection of $[0,1]$. At a midpoint $t$ of binary depth $\ell$, enclose $S(t)$ by Lemma 8.3 with the current seed length $k$ and evaluator parameter $r=\ell$, independently of the eventual requested precision. If the two enclosures are disjoint, $U>S(t)$ means $T<t$, and $U<S(t)$ means $T>t$. If they overlap, reveal the next paid bit of this same $U$, increase the evaluation precision, and repeat. Successful decisions advance one time digit. The clamp in (8.7) makes this comparison valid even when a midpoint lies outside the phase. Stop after the requested $r$ digits and retain both prefixes. A later query continues this identical digit-by-digit procedure, or reads a truncation of the current longer time prefix. No seed is resampled, and no decided time digit is revoked.

The only equalities that can prevent a comparison from eventually separating are $U=\tau$ or $U=S(t)$ for a dyadic midpoint $t$. Each has probability zero. Equivalently, the positive jump component has a density and gives no mass to a prescribed dyadic time, including a dyadic turn. The integer centers, occupied configurations, addresses, phase choices, dyadic midpoints, call/candidate slots and finite words form a countable family. Excluding these equalities gives a common probability-one set on which every such finite query terminates and all its answers refer to the same $T$. On the null complement choose a fixed measurable completion of the decoded map and the floor convention (8.1); a finite query is still asserted to terminate only almost surely. No positive failure, refusal, stop or alarm mass is added.

Keeping the discrete tags, marks and all original metadata makes the infinite canonical name and its decoded marked path measurable inverses on this full-measure space. This is the reversible-coordinate option in XI54.1, not a projection to finite time precision. In particular encoding and decoding preserve probability TV for the same marked laws. ∎

**Lemma 8.5 (creation-conditioned tails and adaptive revelation).** For a candidate seed $e$, let $\mathcal F_e$ be the prior information at its creation, fixing its center pair, address, phase and positive entrance, before any digit of its own fresh $U_e$ is revealed. For a local phase outcome $B$ of positive conditional probability, let $K_e(r)$ be the greatest number of its seed bits used to decide that outcome and, on a jump, to refine its time through depth $r\ge1$ by Theorem 8.4. On a no-jump outcome there are no midpoint queries. Then for every integer $z\ge0$,

$$
\Pr\!\left(K_e(r)>r+2A+16+z\mid\mathcal F_e,B\right)
 \le2^{-z},\qquad
\mathbb E\!\left[K_e(r)\mid\mathcal F_e,B\right]
 \le r+2A+18.
\tag{8.14}
$$

The same inequalities hold after mixing over $B$ and the creation prior. They are not claims conditional on a revealed prefix, an arbitrarily selected query, a rare transcript or a reference event.

For deterministic finite workload caps $H\ge0$, $Q\ge0$, $R\ge1$, allow at most $H$ original pulse calls and at most $Q$ individual mark/precision refinement queries with requested precisions at most $R$, chosen and interleaved using already available information. A grouped request counts its individual mark queries. Define $M_R$ as the maximum seed-prefix length in the mathematical completion that refines every created jumping candidate through depth $R$ and decides every created no-jump candidate. Take $M_R=0$ if none is created. Then

$$
\Pr\!\left(M_R>
 R+2A+16+\lceil\log_2(2H+1)\rceil+z\right)\le2^{-z}.
\tag{8.15}
$$

The actual workload consumes no more bits for each seed than this completion. In particular, its expected total native fresh bits are at most

$$
2H(R+2A+18).
\tag{8.16}
$$

Proof. Fix the creation prior first, so all thresholds for this seed are deterministic. At time depth at most $r$ there are at most $2^r-1$ possible dyadic midpoints in $[0,1]$, irrespective of which bisection path is taken. Include the endpoint threshold $\tau$ as one more. If a comparison remains unresolved after $k$ seed bits, that bit interval and the evaluator enclosure overlap. Lemma 8.3 makes the radius at most $2^{-k-4}$, while the seed interval has length $2^{-k}$. Hence $U_e$ is within $2\cdot2^{-k}$ of the exact threshold. The exact endpoint comparison has the same implication with a smaller constant. A union bound, with allowance for the indexing of the next bit, gives

$$
\Pr(K_e(r)>k\mid\mathcal F_e)
 \le\min\{1,2^{r-k+6}\}.
\tag{8.17}
$$

This bound also covers the no-jump outcome. Intersecting its unresolved set with $B$ and dividing only by $\Pr(B\mid\mathcal F_e)\ge2^{-2A}$ from Lemma 8.2 gives $\min\{1,2^{r-k+2A+6}\}$ as a conditional upper bound. At $k=r+2A+16+z$ it is smaller than the first bound in (8.14). Summing its integer tail gives the expectation, since $\sum_{z\ge0}2^{-z}=2$. The same calculation bounds every fixed moment of the excess by an absolute constant depending only on that moment. No lower bound on an inverse derivative of $d$ was used.

For the workload, regard fresh bits as independent streams labeled by the actually created call and candidate, exposed only on demand. This is a deferred-revelation coupling for the proof; a finite implementation stores only its consumed prefixes and obtains every new bit from the paid fair-bit service. It does not retain an infinite seed or access future original requests. The internal comparison schedule is fixed: at each midpoint use the current prefix, add a bit only on an unresolved comparison, and advance one time digit only on a successful one. Refining all the way to $R$ therefore extends the same decisions as any sequence of shorter queries. The actual state at every query is a prefix of that completed state. This is pathwise domination, not a fresh application of (8.14) conditional on which query was selected.

There are at most $2H$ candidates. A possible slot's entrance may depend on earlier outcomes and query answers, but, conditional on its own creation prior, its unused seed is independent and the same uniform bound applies. Average (8.14) over its two local outcomes and its creation prior, assigning zero length to a slot that is not created. The union bound over these slots and $2H\,2^{-\lceil\log_2(2H+1)\rceil}\le1$ prove (8.15), with no independence assumption between the candidate lengths. Summing their individual expectations proves (8.16). Auxiliary completion bits are solely a domination device and are not charged as consumed actual bits unless actually requested. This proves the adaptive assertion without reconditioning on a selected rare event. ∎

**Theorem 8.6 (fully charged finite-query representation).** Use fixed $d=89$ and schoolbook bit work. For the deterministic analytic caps $H,Q,R$ of Lemma 8.5 there is a sequential current-descriptor representation of the codec with the following native bounds, for one absolute constant $C$:

$$
\begin{aligned}
\mathbb E[\text{native fresh bits}]&\le2H(R+2A+18),\\
\mathbb E[\text{peak active native scratch}]
 &\le C\{89p+A+R+\log(H+1)+1\},\\
\mathbb E[\text{retained current name payload}]
 &\le CH\{p+R+\log(H+1)+1\},\\
\mathbb E[\text{native arithmetic work}]
 &\le C\left[89(H+1)p^3
 +(H+Q)\{A+R+\log(H+1)+1\}^{8}\right].
\end{aligned}
\tag{8.18}
$$

The arithmetic line is supplemented by actual descriptor access, scans, framing, maintenance, rewrites/splices, and input/output copying. All other retained data and all external services are additional, as specified below. The expectations include adaptive query selection under these deterministic caps. Neither deterministic worst-case finite caps nor constant total history memory are asserted.

Proof. At creation of a jumping mark, retain its active entrance pair: four integer coefficients from (2.1), the pair/configuration labels, $j$, phase and candidate, the call identifier, the consumed seed prefix, the largest decided time prefix, and their lengths. The pair determines $m,b,D,E_D$, both phases and every later evaluator input. Thus an entire old $89$-vector is unnecessary. It would be incorrect to discard this pair or its seed prefix when the predictive center advances and later resample an old mark. A no-jump seed may be discarded once its outcome is determined, provided no later permitted operation uses that seed; its no-jump tag and any retained outcome history remain charged. Discarding any jumping descriptor withdraws its future refinement service; the bounds in (8.18) allow all occurred jump descriptors to be kept.

For a mark refined through $r$, this descriptor needs

$$
C\{p+r+K_e(r)+\log(K_e(r)+2)+\log(r+2)
       +\log(H+1)+1\}
\tag{8.19}
$$

bits, with signed coefficient and self-delimiting length framing. The uniform seed prefix is stored literally; unrequested tails are future paid random input. The interval index is its $r$ time digits. $A=O(p)$ and (8.14) make the expectation of (8.19) $O(p+R+\log(H+1)+1)$. There are at most $2H$ marks. The actual final payload is bounded by its depth-$R$ completion, as is its peak payload, since these per-mark prefixes and lengths grow monotonically. This proves the payload bound. The $O(H)$ no-jump/count/mark tags, if kept in the same list, fit in it. Previously retained literal answers, copied descriptors and obsolete versions do not fit for free: their entire encoded lengths must be added. A precision-$r$ interval answer itself has length $O(r+\log(r+2))$ bits, before any additional original metadata.

Choose a sequential list with one current record per mark. Append new records; locate an old one by scanning the actual encoded list, without a free random-access index. Read the selected record into the active workspace. After refinement replace it by its new record, moving the remaining list as necessary. The old and new records while being replaced are active scratch; they are not an uncharged persistent version history. A tape scan and in-place splice can be charged $O(L_{\rm ret}+\ell_{\rm new})$ actual bit access/copy operations, where $L_{\rm ret}$ is the actual current encoded-list length and $\ell_{\rm new}$ is the replacement length. New record framing and length updates are charged too. An implementation which keeps both persistent versions or an immutable refinement log must instead add every retained version, identifier and fragment, together with its access and reconstruction work. Append-only mathematical source has no implication that this private representation must keep immutable snapshots.

The current center, its exact raw update and quantizer scratch use $O(89p)$ bits and $O(89p^3)$ work per pulse/read by Theorem 2.2. Keep the original stage/record flags, current address and configuration, precision parameter and call counter. Their native space is absorbed in $O(p+R+\log(H+1)+1)$. Only the active mark's old/new descriptor, seed prefix, decided time digits and evaluator registers need be added to active scratch. At all times these are bounded by

$$
C\{89p+A+R+M_R+\log(H+1)+1\}.
\tag{8.20}
$$

The list cursor and length registers have logarithmic length in its actual encoding, also absorbed by this bound. Taking expectations in (8.15) proves the active-space line of (8.18). Retained descriptors are an additional resource, not subsumed under that scratch estimate.

To justify the arithmetic exponent, suppose a candidate's current query ends at time depth $r$ and seed length $K$. Its endpoint comparisons are the paid algebraic comparisons of finite precision §2.3 at height $O(p+K)$. Each midpoint evaluation has work at most $C(A+K+r+1)^6$ by Lemma 8.3. A successful comparison advances a time digit; an unsuccessful one reveals another seed bit. Reusing the current prefixes consequently requires at most $C(r+K+1)$ evaluator/comparison calls for a complete refinement, including the outcome decision. This gives the deterministic, deliberately loose bound

$$
C(A+r+K+1)^8
\tag{8.21}
$$

for its native arithmetic. A repeated or lower-precision query can return a truncation; its actual answer copy is still charged. At most $H$ pulse procedures and $Q$ refinement requests need such arithmetic, with at most two candidates per pulse, plus $H+1$ possible whole-vector updates. From (8.15), every fixed moment satisfies

$$
\mathbb E[(A+R+M_R+1)^8]
 \le C\{A+R+\log(H+1)+1\}^8.
\tag{8.22}
$$

Summing (8.21) with this maximum, rather than conditioning on a selected query, proves the arithmetic line of (8.18). Equation (8.16) supplies its fresh-bit line. Almost-sure termination was proved in Theorem 8.4; the exponential tail proves the stronger finite expectations here.

For the native list alone, the expected total scan/splice contribution can additionally be bounded by $C(H+Q)H\{p+R+\log(H+1)+1\}$ under this representation, using the completed total record length. Alternatively charge its actual measured access count. Native bit generation and all comparisons in (8.18) are bit work, not unit-cost real operations. Original input reads, forwarding and output copies remain actual additional work, even when they carry a string already stored elsewhere.

Every retained original request, report, chronological history, readable archive, cut/reference representation, schedule/clock name, input/output buffer and query-controller state is charged at its actual encoded length. The native service needs no $Q$-counter or future request tape; a controller which retains a query count, answers, policies or versions supplies and pays for that state. Add all work and memory of schedule realizers, reference decoders, archive code/state, innovations, emission decisions and emitted outputs, and all acquisition, access, copying and physical service costs. An output is free of retained storage only after it is no longer readable by the continuation. Streaming and retained history are different resource choices.

The parameters $H,Q,R$ are deterministic workload caps for the estimate, not free future inputs to the codec or restrictions of the original word menu. The same procedure runs without a horizon input. If an uncapped random workload is merely finite almost surely, the costs remain finite on each terminating finite run, but finite expectations require a separate integrability argument for the right side and all external/access costs. With unbounded precision or retained history there is no fixed finite total bit, storage or time budget. ∎

**Corollary 8.7 (causal exact rounded law and original from-ready comparison).** Compose Theorem 8.4 with the original endpoint center update $\mathcal N_p(K_jn)$, literal report $I=b_9(q)$, configuration-preserving read update $\mathcal N_p(M_In)$, and literal terminal $W(q)$. Initialize at the known ready by (3.1). For every finite original program, the decoded joint law is exactly Definition 4.1's exact-phase rounded *marked* process. It is consistent on common occurred prefixes. If the program has at most $H$ pulses, on XI54.1's common original marked-source coordinates its distance from the original from-ready law is at most

$$
\operatorname{TV}(L_{\rm original},L_{\rm codec,decoded})
 \le\min\{1,(H+1)(1+16b_*H)\eta_p\},
\qquad \eta_p=4\sqrt{89}\,2^{-p}.
\tag{8.23}
$$

There is no dyadic phase-rounding term. The same original readable archive kernel on its unchanged inputs preserves this comparison, with its execution and resource premises separate.

Proof. Conditional on each arrived valid $(n,q,j)$, Theorem 8.4 identifies the entire marked pulse kernel, not just its endpoint. Exact phase outcomes end on the support of $K_jn$; Theorems 2.2 and 3.2 supply the support-preserving reencoding and valid next entrance. At the read $M_In$ is nonzero because it contains the occupied coordinate; its literal projection and reencoding keep $q$ and the reported sector. No zero true branch is assigned a normalized original state; a rounded-positive branch uses only its own nonzero center projection. The endpoint and next center depend on the exact discrete outcomes, not on how many digits of a genuine time have been requested. Thus old names can continue to be refined after later pulses without changing any source state. Iterated causal kernel composition proves equality with the rounded marked law. Independent fresh candidate tails and processing only arrived requests give common occurred-prefix consistency. They do not add adaptive source controls or give access to the original model's counterfactual noise realization.

For the comparison, directly reuse Theorem 4.2's square-dominated common submeasure on full configuration histories. Its jump-list/holding-factor construction and node limit in (4.6)–(4.8) already retain the genuine jump times and before/after marks; its estimate precedes the projection to $C$ in Theorem 5.1. The pulse losses and $H+1$ reencoding losses there give exactly (8.23). Canonical name decoding is a reversible change of this marked coordinate. There is no comparison with the floored Bernoulli rows (3.4), hence no $2H2^{-p}$ term. In particular this argument does not require the rounded runtime cut to have a square marginal, and does not apply XI54.6 at such a cut.

Retain actual request, schedule, order and failure coordinates, using only their original common external-input contracts. XI54.2's $A_\kappa$ attaches the same original readable archive mechanism on these inputs and reports, not on private descriptors. Common-kernel contraction, and projection back when the source is retained, give the same TV bound (indeed the same distance before and after that common extension). This statement is measurable-kernel composition; an executable archive must separately be supplied with its code, innovations and complete costs. ∎

**Definition 8.8 (continuation, reference and realization boundaries).** A continuation from an actual cut must receive the actual unchanged $(I,Y,Q)$ joint and the stipulated independence of unused source innovations. The local kernel for a supplied center and positive $q$ is defined above; the codec does not acquire that joint, identify an unknown configuration or recover an already realized reference from reports. Equation (8.23) is a known-ready comparison. It does not automatically extend to an arbitrary additional reference joint or to an arbitrary cut. Such an extension requires its own common-joint premises and applicable comparison estimate.

A reference already specified as a Borel function of an occurred decoded history can be transported through the same reversible name map, on the same sample. This gives a measure-theoretic identity. A separately supplied actual reference is kept in its actual joint distribution, with no independent resampling or invented coupling. Neither assertion supplies an evaluator for an arbitrary Borel function, its lawful extraction, its certification or its cost. The same distinction applies to a history decoder with non-effective external coordinates.

Pulse-age names and the unchanged actual schedule preserve actual time. If a start-time realizer and an age name each provide enclosures with errors at most $2^{-r-2}$, their sum gives an absolute-time enclosure with error below $2^{-r}$, plus the actual addition and output costs. This is not automatically a canonical absolute-time binary digit decision: a sum arbitrarily near a dyadic boundary can require deeper comparisons and more schedule queries. Every precision actually requested from that realizer, its retained names and all work are additional charges. No native-only expected or worst-case budget is asserted for an arbitrary supplied schedule.

The original readable archive still receives only $g(Y)$, actually arrived requests and their call times/order, literal original reports/failures and earlier actual archive emissions, as in XI54.2. It never receives private jump names, seeds, unreported configurations or replacement comparison vectors. Emission times, counts, absence, post-terminal archives and return data keep their original coordinates and kernel. Arbitrary measurable archive or reference kernels need not have executable bounded realizers. Their descriptive existence supplies no random-bit source, extraction device or finite resource contract.

All branch and error masses in (8.23) are unconditional. No relative or absolute error guarantee conditional on an arbitrary rare original event is obtained. The grid preserves the support of each immediate argument; it can still remove a later exact cancellation, so exact original-word null support is not asserted. All original labels and legal moves remain. Fixed $p$ gives the displayed horizon-dependent comparison, not a uniform fixed accuracy for every unbounded finite horizon. Query access to names is a computational output service of this law representation, not a newly permitted internal-time observation or physical feedback operation.

The common marked coordinate in (8.23) omits a common exact-vector graph identification. XI55 supplies each model's own deterministic vector reconstruction; different exact graphs can have TV one in one unchanged exact-vector coordinate. The rounded vector is never substituted for the original vector there. Source-preserving inverse or mutual recovery, unrestricted continuation, response identification and the complete relationships among space, time, boundary and memory remain additional obligations. The unknown response remains $\Pi:D_{\rm act}\to\Delta(E)$, with no newly supplied regularity or domain extension. Original R/common odds/calibration, preparation/device/joint/reference contracts and actual histories are retained, not generated by the codec. No reset, clone, affine mixture, inverse control, hidden reader or destructive-to-continuing substitution is introduced.

Actual native source, Hamiltonian/holding/read/update/quantizer realization, a physical independent fair-bit supply, clocks, effective reference/archive/schedule services, lawful acquisition, certification and physical adoption are independent premises. When not separately supplied they are ASSUMED-UNVERIFIED for a physical application. The conditional mathematical implication above does not establish those premises, an energy or real-time deadline bound, physical optimality, or completion of the full quantum-source objective.

**Definition 8.9 (suppliers and the source-specific increment).** The statements here are ordinary conditional paper mathematics. Source identities and interfaces are those of the exact RQ/FP/XI text at repository revision `1bfe29bafbcb2c76bdd9536a55f9c37d5505b3c8`. The reused original pulse, candidate innovations and actual-past contracts are III145–146/160 and IV278; fixed-order endpoint arithmetic and radical signs are finite precision §§2.1–2.3 and Theorems 2.2–3.2 above. The full-history domination/stability proof is Theorem 4.2, with the same XI54 coordinate/archive and XI55 vector-graph boundaries. Those results are used directly rather than claimed anew.

The integral-risk and node suppliers remain [Georgii–Tumulka, arXiv:math/0312294v2, §3 (10)–(11), Lemma 2(a),(b),(d)][GT] and [Dürr–Goldstein–Tumulka–Zanghì, arXiv:quant-ph/0407116v1, §2.7 (23)–(29)][DGTZ]. The same $P_q=|q\rangle\langle q|$, $H_{\rm GT}=2H_j$ correspondence matches their $\hbar=2$ to native $\hbar=1$. They supply holding, node and process premises, not the native computational resource theorem. [Karney, *Sampling exactly from the normal distribution*, arXiv:1303.6257v2, §1 and the u-rand representation/comparison discussion][Karney8] supplies a primary precedent for exact objects with progressively generated random digits. Its normal sampler and cost claims are not suppliers for (8.18). Generic inverse-transform sampling, elementary-function series, certified interval arithmetic, norm separation, tail summation, deferred revelation and measurable isomorphism are reused tools inside the source-specific proof.

The `repo-derived` increment is the native uniform mass/survival-evaluation guard connected to an effective genuine marked-output map, its candidate correspondence, compatible pulse-age names and fully paid finite-query interface, including the creation-conditioned and adaptive-domination resource arguments. The already covered terminal $\Theta(\log H)$ result, finite-seam memory theorem, endpoint arithmetic, square-domination estimate, XI54 archive contract and horizon-free full-seam lower bound do not supply this effective marked-time service. Expected variable-length storage is not a finite worst-case reachable-state count, and (8.23) is not the horizon-free fixed-error premise of that lower bound. No matching optimum, global novelty, exhaustive search, independent physical premise supply or new kernel verification is asserted. A user-authored conditional synthesis remains conditional input; it does not independently realize any of the actual supplies in Definition 8.8.

[Karney8]: https://arxiv.org/html/1303.6257v2

## 追加锚（本行以下为增补区）
