# FIB ATOM whitebox tasks inside a complete SIC time fiber

## 1. The source, observations and acquisition tasks

**Definition 1.1 (Calibrated tensor-sign source).** Fix integers $n,L\ge1$, put $\theta=\pi/(4L)$ and let $S_n=\{-1,+1\}^n$. The system is $\mathcal K=(\mathbb C^2)^{\otimes n}$ with labeled factors and signed computational, $X$, $Y$ and $Z$ standards. For $s\in S_n$ define

$$
U_s=\bigotimes_{i=1}^n\exp(i s_i\theta Z),
\qquad
\Lambda_s(\rho)=U_s\rho U_s^\dagger.
$$

One ordinary source call applies $\Lambda_s$ to this entire $n$-qubit system and the identity to any workspace. The unknown $s$ is selected once. Every subsequent call uses the same memoryless, noiseless channel. The integers $n,L$, the product-unitary promise, factor labels and signed basis standards are public; $s$ is not. Initial workspace data and any private random seed are independent of $s$. In particular, no preparation record containing $s$ is available.

**Definition 1.2 (Complete identity-target SIC time archive).** Let $F_k^{\mathcal F}$ be exactly the product-qubit-SIC functional in Definition 2.3 of [the SIC Pauli-weight volume][SIC], with its normalization and identity target. A frame $\mathcal F$ consists of one qubit SIC on each labeled factor. Define

$$
\mathcal H(s)=
\left(F_k^{\mathcal F}(\Lambda_s^m)
:m\in\mathbb Z_{\ge0},\ 0\le k\le n,\ \mathcal F\text{ a product qubit SIC frame}\right).
$$

The archive grants these exact aggregated values as mathematical data. It grants neither the individual transition records $\operatorname{Tr}(\rho_b\Lambda_s^m(\rho_a))$, other target operations, nor SIC frames on the full system that fail to be products of qubit SICs. No finite acquisition cost for this infinite archive is assumed. Write $Q_w(m;s)$ for the Pauli-weight coordinates of $\Lambda_s^m$ in Convention 2.1 of [SIC]. Products over empty sets and zeroth powers, including $0^0$ in coefficient formulas, have value one.

**Definition 1.3 (Two ordinary-call contracts).** Let $q$ be an integer with $0\le q\le L$. A one-block protocol prepares any $s$-independent density state on $\mathcal K\otimes R$, with $R$ any finite-dimensional reference. It makes $q$ successive ordinary calls with no intervening operation on the system, and then performs any joint POVM and reports $\widehat s\in S_n$. Source-independent randomization and terminal computation are permitted. Operations on a reference alone during the block commute with all source calls and can be deferred to the end.

The controlled comparison class permits arbitrary source-independent finite-dimensional CPTP controls and instruments, including classical adaptation to retained outcomes, before, between and after at most $q$ ordinary calls. Workspace size may be chosen freely, but is finite for each protocol. Every branch uses at most $q$ calls. An unknown controlled-$U_s$, its inverse and a source reset are not primitives of either contract. Ancillary preparations and known conditional swaps, when used by a comparison protocol, belong to its controls rather than to the archive.

**Definition 1.4 (Whole-label success and behavioral distance).** For a protocol $\Pi$, put $p_\Pi(s)=\Pr_s[\widehat s=s]$. Its uniform whole-label Bayes score is $2^{-n}\sum_s p_\Pi(s)$ and its minimax score is $\min_s p_\Pi(s)$. The optimal scores take the supremum over the specified contract. A score-only protocol uses $\mathcal H(s)$ and source-independent resources, with no ordinary calls or other source-dependent input. Zero-error recovery means $p_\Pi(s)=1$ for every promised source, and not just success on average or on one selected bit.

For $s,r\in S_n$, let $h(s,r)=|\{i:s_i\ne r_i\}|$ and define the distance of their $q$-iterate channels by

$$
D_q(s,r)=\sup_{R,\rho}
\frac12\left\|
(\Lambda_s^q\otimes\mathrm{id}_R)(\rho)
-(\Lambda_r^q\otimes\mathrm{id}_R)(\rho)
\right\|_1.
$$

Here the supremum ranges over all finite references and density states; $\|A\|_1=\operatorname{Tr}\sqrt{A^\dagger A}$. This is a distance for the uninterrupted iterate, not the output distance of an arbitrary controlled $q$-call strategy.

**Definition 1.5 (Legal five-window code and complete service).** For $n=3N$ with $N\ge1$, define

$$
B_n=\{b\in\{0,1\}^n:b_i b_{i+1}=0\text{ for }1\le i<n\},
\qquad s_i(b)=(-1)^{b_i},
$$

and write $W_j(b)=(b_{3j-2},b_{3j-1},b_{3j})$ for $1\le j\le N$. The five-window alphabet, in increasing position order, is the one in [the FIB whitebox volume][FIB], Definition 2.1:

$$
\Sigma=\{000,100,010,101,001\},
$$

with respective labels $\mathrm{null},2,3,2\ 5,5$. A word in $B_n$ has each $W_j(b)\in\Sigma$ and every seam satisfies $b_{3j}b_{3j+1}=0$. This is fixed-length finite-word syntax. It includes the all-zero word and words whose final window is $000$. It does not require acceptance of the canonical terminal $\mathrm{End}$ query of [FIB], Definition 6.1; in that interface a final $000$ does not accept $\mathrm{End}$. A null window still occupies three positions.

The acquisition task is to install a closed deterministic service whose reply to every requested index $j\in\{1,\ldots,N\}$ is $W_j(b)$. Installation and each legal reply take finite computation. After installation the service retains its acquired data and no longer accesses the source or source-dependent advice. Success requires correct replies on every finite index-query history, including repetitions and indices selected adaptively from previous replies. Installation may be randomized; the installed service is deterministic. Thus success concerns the whole response service rather than the average correctness of individual queries.

A pointer variant has public initial pointer $p=1$ and state $(b,p)$ with $p\in\{1,\ldots,N+1\}$. An indexed read leaves $p$ unchanged. A $\mathrm{Next}$ request is legal exactly when $p\le N$, returns $W_p(b)$ and updates $p$ to $p+1$. This variant has no $\mathrm{End}$ action. The Fibonacci numbers used below satisfy $F_0=0$, $F_1=1$ and $F_{k+2}=F_{k+1}+F_k$.

**Assumption 1.6 (Priced preparation and restricted angle variation).** The attaining protocol is allowed one preparation of $|0\rangle^{\otimes n}$, known single-qubit $H$ and $S^\dagger$ gates and ideal computational measurements, with $S=\operatorname{diag}(1,i)$. Its calibration inputs include all the signed standards of Definition 1.1, known $L$, the stated angle promise and correct preparation and readout. Their acquisition carries an unspecified separate price $C_{\mathrm{cal}}$; the archive does not supply them.

For the angle-tolerance clause only, replace the source by

$$
\widetilde U_{s,\varepsilon}
=\bigotimes_{i=1}^n\exp\big(i(s_i\theta+\varepsilon_i)Z\big),
\qquad |\varepsilon_i|\le\eta,
$$

where each $\varepsilon_i$ is constant over all calls to that device. Product structure and ideal preparation, known gates and readout are retained. These hypotheses describe systematic product-angle variation, not general state-preparation or measurement noise.

## 2. A source-specific archive fiber and its exact acquisition laws

**Theorem 2.1 (Tensor-sign ambiguity, optimal block recovery and legal service transfer).** Under Definitions 1.1–1.5 and the ideal resources of Assumption 1.6, the following statements hold for every $n,L\ge1$ and integer $0\le q\le L$.

(i) The entire archive $\mathcal H$ is constant on the $2^n$ distinct channels $\Lambda_s$. For every integer $m\ge0$ its common Pauli-weight coordinates are

$$
Q_w(m;s)=\binom nw
\cos(m\theta)^{2(n-w)}\sin(m\theta)^{2w},
\qquad 0\le w\le n.
\tag{2.1}
$$

Within this finite promise family the archive fiber is all of $S_n$. The optimal score-only uniform Bayes and minimax whole-label successes are both $2^{-n}$. Completeness of the hierarchy for the time-indexed weight vector is the already established Corollary 6.2 of [SIC]; it does not imply completeness for the source label or response service.

(ii) If $h=h(s,r)$, then

$$
D_q(s,r)=\sin\left(\frac{\pi\min(hq,L)}{2L}\right).
\tag{2.2}
$$

Every distance is attained by a pure input without a reference. In particular the diameter of this promised family at time $q$ is $\sin(\pi\min(nq,L)/(2L))$.

(iii) The optimal uniform Bayes and minimax whole-label successes in the one-block contract are both

$$
P_q=\left(\frac{1+\sin(q\pi/(2L))}{2}\right)^n.
\tag{2.3}
$$

The same product probe and local measurement attain $P_q$ separately for every $s$. The ratio to score-only optimal success is $(1+\sin(q\pi/(2L)))^n$.

(iv) For a pair of neighboring labels $h(s,r)=1$, every controlled comparison protocol has equal-prior binary success at most

$$
\frac{1+\sin(q\pi/(2L))}{2}.
\tag{2.4}
$$

Consequently $L$ ordinary calls are necessary and sufficient for zero-error recovery of all signs, even in the controlled comparison class. This is a controlled zero-error threshold; (2.3) asserts finite-error optimality only for the one-block class.

(v) The attaining block strategy uses one $n$-qubit computational preparation, $q$ calls to the same full device, $3n$ known single-qubit gates, $n$ computational measurements and $n$ retained answer bits, without an ancilla. It invokes neither an inverse nor an unknown controlled call nor a source reset. Calibration has the separate price $C_{\mathrm{cal}}$ of Assumption 1.6. Under that assumption's restricted angle variation, its $L$-call whole-label success for each $s$ is exactly

$$
\prod_{i=1}^n\cos^2(L\varepsilon_i)
\ \ge\ 1-\sum_{i=1}^n\sin^2(L\varepsilon_i)
\ \ge\ 1-nL^2\eta^2.
\tag{2.5}
$$

Thus, for a target failure tolerance $0\le\delta\le1$, $\eta\le\sqrt{\delta/n}/L$ suffices for whole-label success at least $1-\delta$. This is a sufficient angle tolerance, not an optimal calibration-acquisition law or a bound for general preparation/readout errors.

(vi) When $n=3N$ with $N\ge1$, on the restriction $\{\Lambda_{s(b)}:b\in B_{3N}\}$, the archive remains constant, while different $b$ have different complete indexed services. Under an explicitly uniform legal-word prior, optimal score-only exact-service success, both Bayes and minimax, is

$$
\frac1{|B_{3N}|}=\frac1{F_{3N+2}}.
\tag{2.6}
$$

Installing every exact indexed service, or its pointer variant, has the same sharp controlled zero-error threshold $L$. The $L$-call product readout followed by retention of $b$ gives a task-sufficient representation satisfying the readout, legal-domain and update correspondences of [FIB], Definition 8.1, on every finite legal history. This is the explicit five-window code of Definition 1.5; no realization as a native FIB generation tree is assumed. Formula (2.3) is not an asserted optimum for the nonproduct prior on $B_{3N}$.

### 2.1 Proof of the archive fiber

For $A\subseteq\{1,\ldots,n\}$ set $Z_A=\bigotimes_i Z^{\mathbf1_{i\in A}}$ and $s_A=\prod_{i\in A}s_i$. Expanding each factor gives

$$
U_s^m=\sum_{A\subseteq\{1,\ldots,n\}}
\cos(m\theta)^{n-|A|}
\big(i\sin(m\theta)\big)^{|A|}s_A Z_A.
\tag{2.7}
$$

In the unnormalized Pauli basis, the process matrix of a unitary with coefficient vector $u$ is $uu^\dagger$: this follows by expanding $U\rho U^\dagger$ on both sides. It is the process-matrix convention and unitary coefficient formula in [Korotkov][KOR], Section II, equations (1)–(4), also used by [SIC], Convention 2.1. Thus the diagonal weight of $Z_A$ in (2.7) is

$$
\cos(m\theta)^{2(n-|A|)}\sin(m\theta)^{2|A|},
$$

independent of $s$, and every other Pauli label has diagonal weight zero. Summing over the $\binom nw$ subsets of size $w$ proves (2.1), for all integer times, including $m=0$.

Apply the existing Lemma 3.1 and Theorem 4.1 of [SIC]. They say that each allowed $F_k^{\mathcal F}$ is a fixed functional of these weights, independent of the product SIC frame. Therefore $\mathcal H(s)$ is identical for all $s$. The existing Corollary 6.2 of that volume recovers the weight vector from the hierarchy; neither its inversion nor its joint-simplex description is reproved here. Their application at every $m$ identifies the sequence $(Q_w(m;s))_{m,w}$.

A score-only decision has a source-independent answer distribution $a(s)$ with $\sum_s a(s)=1$. Its uniform success is $2^{-n}\sum_s a(s)=2^{-n}$, and its minimum source success is at most this average. Uniform guessing attains the same success at every source. Allowing a failure answer can only reduce the sum, so does not improve either optimum. Distinctness of all the channels is established in the next part.

### 2.2 Proof of the Hamming-distance formula, including saturation

The trace-distance/numerical-range reduction for unitary channels is the mature result in [Watrous][WAT], Theorems 3.52 and 3.55. Here it takes the following concrete form. For a pure joint input $|\psi\rangle$ with reduced system state $\rho_{\mathcal K}$, the two output unit vectors have overlap

$$
\langle\psi|(V\otimes I_R)|\psi\rangle
=\operatorname{Tr}(\rho_{\mathcal K}V),
\qquad V=(U_s^q)^\dagger U_r^q.
$$

Their half trace distance is

$$
\sqrt{1-|\operatorname{Tr}(\rho_{\mathcal K}V)|^2}.
\tag{2.8}
$$

Indeed, when the two vectors span a two-dimensional space, the difference of their rank-one projectors has trace zero and eigenvalues $\pm\sqrt{1-|\langle\psi_s,\psi_r\rangle|^2}$ on that span, with zeros elsewhere; when their span is one-dimensional the difference is zero. Decomposing an arbitrary mixed input into pure states and using convexity of the trace norm bounds its distance by the largest pure-input distance.

Since $V$ is diagonal unitary, its expectations are precisely convex combinations of its eigenvalues. Conversely every such combination is the expectation on an unreferenced pure state whose amplitudes in the corresponding orthonormal eigenvectors are the square roots of the combination weights. Hence references do not enlarge the possible expectations or the optimum of (2.8).

Put $v=2q\theta=q\pi/(2L)$. The factors on the $n-h$ agreeing positions cancel. On the remaining positions the relative rotation has angles $\pm v$, and its spectrum, disregarding multiplicity, is

$$
\{\exp(i v(h-2j)):0\le j\le h\}.
\tag{2.9}
$$

If $q=0$ or $h=0$, $V=I$ and the distance is zero. Suppose $q>0$ and $h>0$. If $hv\le\pi/2$, all phases in (2.9) lie between $-hv$ and $hv$. Every convex combination has real part at least $\cos(hv)\ge0$, and therefore modulus at least $\cos(hv)$. The equal mixture of the two endpoint eigenvalues attains $\cos(hv)$. Formula (2.8) gives $D_q(s,r)=\sin(hv)$, attained without a reference.

For $hv\ge\pi/2$, a wider endpoint arc alone would not justify saturation, because the spectrum is discrete. The following combination does. Let $b_*=0$ for even $h$ and $b_*=1$ for odd $h$. The spectrum contains the symmetric pair with phases $\pm b_*v$, whose mean is $\cos(b_*v)\ge0$. If this mean is zero, the eigenvalue hull already contains zero. Otherwise choose the smallest integer $a_*\le h$ of the same parity as $h$ such that $a_*v\ge\pi/2$. It exists by $hv\ge\pi/2$, and $a_*>b_*$. Minimality gives

$$
\frac\pi2\le a_*v<\frac\pi2+2v\le\frac{3\pi}2,
$$

so the symmetric eigenvalue pair at phases $\pm a_*v$ has mean $\cos(a_*v)\le0$. With

$$
\lambda=\frac{\cos(b_*v)}{\cos(b_*v)-\cos(a_*v)}\in[0,1],
$$

take weight $\lambda$ on the equal $\pm a_*$ pair and weight $1-\lambda$ on the equal $\pm b_*$ pair. Its expectation is zero. These pairs are actual eigenvalues from (2.9), including the single eigenvalue when $b_*=0$, so the square-root-amplitude construction realizes the combination without a reference. Equation (2.8) now attains distance one. This proves (2.2) in both regimes and at $hq=L$.

For $q=1$ and $h>0$, (2.2) is strictly positive. Thus $s\ne r$ implies $\Lambda_s\ne\Lambda_r$ as channels, completing (i). Maximizing (2.2) over $h\in\{0,\ldots,n\}$ gives the stated diameter, with $h=n$ attained by $r=-s$.

### 2.3 Proof of optimal recovery over all one-block probes

Let $a=q\theta$, $c=\cos a$ and $t=\sin a$, so $0\le a\le\pi/4$ and $c,t\ge0$. It suffices to bound pure probes: any mixed probe can be purified with a finite extra reference, and granting terminal access to that purification can only improve attainable success. Let $|\psi\rangle$ be an arbitrary unit vector on the system and all references. Define

$$
v_A=c^{n-|A|}(it)^{|A|}(Z_A\otimes I)|\psi\rangle,
\qquad
|\psi_s\rangle=\sum_A s_Av_A.
$$

Each $Z_A$ is unitary, hence $\|v_A\|=c^{n-|A|}t^{|A|}$, independent of the probe and reference. For an arbitrary label POVM $(M_s)_{s\in S_n}$, form vectors in the orthogonal direct sum of $2^n$ copies of the output space:

$$
w_A=\big(s_A\sqrt{M_s}\,v_A\big)_{s\in S_n}.
$$

Because $\sum_sM_s=I$, their norms satisfy

$$
\|w_A\|^2=\sum_s\langle v_A,M_sv_A\rangle=\|v_A\|^2.
$$

The average success is therefore bounded by the triangle inequality in that direct sum:

$$
\begin{aligned}
2^{-n}\sum_s\langle\psi_s,M_s\psi_s\rangle
&=2^{-n}\left\|\sum_Aw_A\right\|^2\\
&\le2^{-n}\left(\sum_A\|v_A\|\right)^2\\
&=2^{-n}(c+t)^{2n}
=\left(\frac{1+\sin(2a)}2\right)^n.
\end{aligned}
\tag{2.10}
$$

This bound holds for every probe, finite reference and POVM. Source-independent mixtures of protocols satisfy it as well. Failure outcomes can be assigned a label before applying the bound. The proof optimizes over the input rather than merely optimizing the measurement for a chosen input.

For attainment, prepare $|+\rangle^{\otimes n}$. After the block the state on factor $i$ is

$$
|\psi_{s_i}\rangle
=\frac{e^{i s_i a}|0\rangle+e^{-i s_i a}|1\rangle}{\sqrt2}.
$$

With $Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$ its expectation is $-s_i\sin(2a)$. Measure each $Y_i$, record its eigenvalue $y_i\in\{-1,+1\}$, and decode $\widehat s_i=-y_i$. Each bit is correct with probability $(1+\sin(2a))/2$. Product output states and local measurements make the bit outcomes independent conditional on the fixed $s$, so all $n$ bits are correct with probability (2.3), for every $s$.

No protocol's minimum source success exceeds its average. The strategy just given reaches the average upper bound at each source, proving both optima. At $q=0$ this gives $2^{-n}$; at $q=L$ it gives one. Dividing by the score-only value gives the stated improvement factor.

Maximum-success product laws are mature tools: [Molina and Watrous][MW], Section 4, proves multiplicativity for specified joint outcomes of independent interactive measurements. The direct-sum estimate (2.10) gives the needed bound for the present source family and its entire probe class. Neither that supplier nor this estimate establishes a full-vector finite-error optimum with arbitrary intervening controls.

### 2.4 Proof of the controlled neighbor bound and exact threshold

For neighbors, $V_1=U_s^\dagger U_r$ has eigenvalues $e^{\pm2i\theta}$. Thus every joint unit vector $x$, including an arbitrary workspace, satisfies

$$
\big|\langle x,(V_1\otimes I)x\rangle\big|\ge\cos(2\theta).
\tag{2.11}
$$

The general shortest-eigenvalue-arc zero-error query principle is supplied by [Duan, Feng and Ying][DFY], Theorems 1–2. Its neighbor specialization has arc length $4\theta=\pi/L$ and minimal zero-error call count $L$. To include the present CPTP, adaptive and stopping contract and obtain its quantitative finite-$q$ bound, use the following projective-angle argument.

For unit vectors put $A(x,z)=\arccos|\langle x,z\rangle|\in[0,\pi/2]$. This angle obeys the triangle inequality. To see the inequality for a middle unit vector $y$, align the phases of $x,z$ so their overlaps with $y$ are nonnegative real. Writing

$$
x=\cos\alpha\,y+\sin\alpha\,u,
\qquad z=\cos\beta\,y+\sin\beta\,w,
$$

where $u,w$ are unit and orthogonal to $y$ when their terms are nonzero, gives

$$
\operatorname{Re}\langle x,z\rangle
\ge\cos\alpha\cos\beta-\sin\alpha\sin\beta
=\cos(\alpha+\beta).
$$

When $\alpha+\beta\le\pi/2$, this implies $A(x,z)\le\alpha+\beta$; for a larger sum the angle's range gives the same inequality. Zero sine terms are omitted. Common isometries preserve $A$.

Purify the initial state and all controls, retaining the environments and instrument outcome records. Finite-dimensional channel dilations by isometries are the mature Stinespring characterization; see [Watrous][WAT], Corollary 2.27. Explicitly, if an instrument has Kraus operators $K_{a,\mu}$ for outcome $a$, with $\sum_{a,\mu}K_{a,\mu}^\dagger K_{a,\mu}=I$, use the common isometry

$$
W|x\rangle=\sum_{a,\mu}K_{a,\mu}|x\rangle\otimes|a\rangle_C\otimes|a,\mu\rangle_E.
$$

Its squared norm is $\|x\|^2$. Discarding $E$ yields the original classical outcome record and conditional state. Later outcome-dependent operations act by known controlled isometries on $C$, while every old environment is retained. This constructs the purification successively through an adaptive protocol and preserves its actual decision law when the environments are discarded. Retaining these systems is a grant to the discriminator, so a bound on the purified protocol also bounds its actual output. An instrument's selected branch is not postselected for free: all its outcomes are retained in this purification.

If the two current purifications are $x,y$, then at the next ordinary call,

$$
\begin{aligned}
A\big((U_s\otimes I)x,(U_r\otimes I)y\big)
&\le A\big((U_s\otimes I)x,(U_s\otimes I)y\big)\\
&\quad+A\big((U_s\otimes I)y,(U_r\otimes I)y\big)\\
&\le A(x,y)+2\theta,
\end{aligned}
$$

using (2.11). Starting from a common $s$-independent initial purification, $q$ calls give angle at most $2q\theta\le\pi/2$. The purified output half trace distance is at most $\sin(2q\theta)$ by the pure-state identity (2.8); discarding environments cannot increase trace distance. Finally the Holevo–Helstrom theorem, [Watrous][WAT], Theorem 3.4, gives binary success at most $(1+\sin(2q\theta))/2$.

An at-most-$q$ protocol with classical stopping can be padded to $q$ calls: after a stopping record, retain its decision registers, swap the active port to a fresh uncorrelated computational eigenstate and make the remaining ordinary calls on that state. In each classical branch the dummy state acquires only a global phase, so the retained decisions are unchanged. This is a known, record-conditioned swap followed by an ordinary call, not a controlled unknown unitary. Purification of the padded protocol may retain these phases in its environments; tracing those environments still gives the original decision law. Thus the preceding upper bound applies to stopping protocols as well. Conditioning on a source-independent random seed gives the same bound for each seed, so averaging includes randomized controls.

For $q<L$, $\sin(2q\theta)<1$, so even two neighbors cannot be distinguished with zero error. Whole-label recovery with zero error would distinguish them, proving necessity of $L$. At $q=L$, the product strategy in Section 2.3 gives opposite orthogonal $Y$-eigenstates at each site; all $2^n$ joint outputs are pairwise orthogonal and local readout recovers $s$ with certainty. This proves sufficiency and (iv).

### 2.5 Proof of the resource count and angle tolerance

Apply $H$ to each of the $n$ prepared zeros to obtain the product probe. After $q$ successive device calls, apply $S^\dagger$ and then $H$ at each site and measure computationally. The measured pre-rotation observable is

$$
(HS^\dagger)^\dagger Z(HS^\dagger)=SXS^\dagger=Y.
$$

For computational outcome $z_i\in\{0,1\}$, set $y_i=(-1)^{z_i}$ and $\widehat s_i=-y_i$. There are $n$ preparation gates and $2n$ readout gates, giving $3n$ known gates in total, together with $n$ measurements and $n$ retained answer bits. There is one uninterrupted source run on the prepared system, not $q$ independent preparations, and no auxiliary system is needed. The operation counts do not price calibration, gate implementations, storage lifetime or later service-query computation.

For the perturbed product source of Assumption 1.6, the expectation after $L$ calls on factor $i$ is

$$
-\sin\big(2L(s_i\theta+\varepsilon_i)\big)
=-s_i\cos(2L\varepsilon_i).
$$

The same decoder is correct on that factor with probability

$$
\frac{1+\cos(2L\varepsilon_i)}2=\cos^2(L\varepsilon_i).
$$

Product structure gives the exact success product in (2.5). For $x_i\in[0,1]$, $\prod_i(1-x_i)\ge1-\sum_i x_i$, by induction using $(1-x)(1-y)\ge1-x-y$. Apply this with $x_i=\sin^2(L\varepsilon_i)$ and use $|\sin u|\le|u|$ to prove the two inequalities and the stated sufficient tolerance. Constant angles and ideal preparation/readout are essential premises of this calculation; it introduces no claim about general noisy channels or calibration cost.

### 2.6 Proof of the five-window service correspondence

Definition 1.5 uses the public bijection $b\mapsto s(b)$. The archive is constant on its image by (i). The existing legal-word counting recurrence in [FIB], Section 2, gives $|B_n|=F_{n+2}$: its empty and one-bit counts are $1$ and $2$, and the no-adjacent syntax splits by initial $0$ or $10$. This count is a cited combinatorial step, not a new enumeration claim.

Different $b,b'$ have different blocks at some index $j$, so their services disagree already on the one-query history $(j)$. In particular, one installed deterministic service cannot be successful for two different legal words, regardless of its representation or internal updates. For a score-only randomized installation the law of the installed service is independent of $b$. Its exact-success events for the different $b$ are disjoint, so their probabilities sum to at most one. Uniform averaging bounds Bayes success by $1/|B_n|$, and minimax success by the same value. Uniformly selecting a legal word and installing its true service attains that value separately for every source. This proves (2.6), including services required to answer every future history rather than just one chosen scan.

The legal words $b^{(0)}=0^n$ and $b^{(1)}=(1,0,\ldots,0)$ are both in $B_n$, and their sign labels are neighbors. Their first blocks are $000$ and $100$. A zero-error installation would allow their distinction by a subsequent indexed query at $j=1$, with no new source input. The controlled neighbor bound therefore rules out installation with fewer than $L$ calls. This witness uses finite-word syntax and does not assert that $b^{(0)}$ passes canonical $\mathrm{End}$.

Conversely, the $L$-call readout identifies $s$ and hence the entire legal word $b$ with probability one. Retain its $n$ bits and answer each indexed request by selecting the three corresponding bits. The response at time $t$ on any finite history $(j_1,\ldots,j_k)$ is exactly $W_{j_t}(b)$. A direct induction gives this for repeated or adaptive requests: the retained $b$ is unchanged by an indexed read, so the assertion remains true after each answer. Queries consume whatever computation and retention resources their realization charges; the acquisition count is still $L$ device calls.

For the pointer variant the retained representation is $(b,p)$, not $b$ alone. On a legal $\mathrm{Next}$, it returns the substring at $p$ and increments $p$; indexed reads leave $p$ unchanged. Thus the represented and true services have identical replies, the same legal domain $p\le N$ for $\mathrm{Next}$, and the same next pointer. By induction these equalities hold on every finite legal mixed history. Equivalently, for the latent task state consisting of the fixed source label and service pointer, the coordinate map

$$
e(s(b),p)=(b,p)
$$

preserves the outputs, action domains and updates in the sense of [FIB], Definition 8.1. The inverse sign code is public. In contrast, $(\mathcal H(s(b)),p)$ cannot supply the indexed readout at $j=1$ for the neighbor witness above, since that observation is equal for the two sources while their answers differ. The weight-vector task and this response task therefore have different sufficient observations.

The same retained bits give the $L$-call upper bound for the pointer task, and its first $\mathrm{Next}$ distinguishes the neighbor witness, giving the lower bound. The $n$ stored bits are the resources of this explicit representation, not an asserted minimum storage requirement for $B_n$.

Under the restricted angle variation, the product readout recovers $b$ with the success probability in (2.5). If a measured word is illegal, replace it by any fixed legal word before installation; if it is the true word, this replacement is unnecessary. Thus exact-service success is at least (2.5), with ideal readout still required. Neither this transfer nor the legal-word restriction computes the intermediate-$q$ optimum under the uniform legal-word prior.

This correspondence encodes a constrained finite response task into the promised channels. It does not give a native FIB-tree generation or destructive-root operation. A transfer to any other state model requires a map preserving that model's source, observable information, legal actions, readouts and updates, and requires accounting for the preparation and acquisition resources. The all-history preservation under such maps is the existing implication in [FIB], Definition 8.1. No correspondence with the states or updates of a particular trained network is assumed here. $\square$

## 3. Mathematical suppliers and attribution

**Citation 3.1 (Scope of the supplied mathematics).** The source-specific synthesis of Theorem 2.1 is `repo-derived`: its stated tensor-sign promise, all-time archive fiber, exact Hamming geometry, arbitrary-probe block recovery curve and legal-service acquisition contract are the objects of its proof. The following supplied results are cited steps, with their own hypotheses; they are not separately presented as new theorems of this volume.

| Mathematical source | Exact supplied step |
| --- | --- |
| [SIC Pauli-weight geometry][SIC], Convention 2.1, Definition 2.3, Lemma 3.1, Theorem 4.1, Corollary 6.2 and Remark 7.1 | Repository-supplied Pauli coordinates, normalized identity-target product-SIC scores, frame independence, weight functionals and hierarchy completeness. Their scope fixes Definition 1.2 and the cited steps in Section 2.1. |
| [FIB ATOM and machine-learning whitebox theory][FIB], Sections 2, 6 and 8 | Repository-supplied five-window dictionary, no-adjacent counting recurrence, seam/terminal distinction and task-relative readout/domain/update condition. Section 2.6 uses these under its explicit finite-word code. |
| A. N. Korotkov, [*Error matrices in quantum process tomography*][KOR], arXiv:1309.6405, Section II, equations (1)–(4) | `literature-attested`: the unnormalized Pauli-basis process-matrix convention and the unitary coefficient outer product used in Section 2.1. |
| John Watrous, [*The Theory of Quantum Information*][WAT], Corollary 2.27 and Theorems 3.4, 3.52, 3.55 | `literature-attested`: channel-isometry dilations, Holevo–Helstrom binary testing, stabilized channel testing and absence of an ancilla advantage for two isometric channels. Sections 2.2 and 2.4 specialize those tools to the displayed spectrum and ordinary-call contract. |
| Runyao Duan, Yuan Feng and Mingsheng Ying, [*Entanglement Is Not Necessary for Perfect Discrimination between Unitary Operations*][DFY], Phys. Rev. Lett. 98 (2007), 100503, Theorems 1–2, DOI: 10.1103/PhysRevLett.98.100503 | `literature-attested`: the shortest-eigenvalue-arc minimal-query principle for two unitary operations. The neighbor pair here has arc $\pi/L$; Section 2.4 gives the quantitative bound with the stated adaptive and stopping permissions. |
| Abel Molina and John Watrous, [*Hedging bets with correlated quantum strategies*][MW], arXiv:1104.1140, Section 4 | `literature-attested`: maximum joint-outcome multiplicativity for independent interactive measurements. It supplies method credit in Section 2.3; the present proof bounds its whole-label probe class directly and does not infer arbitrary-controlled finite-error optimality. |
| S. Greenaway, F. Sauvage, K. E. Khosla and F. Mintert, [*Efficient assessment of process fidelity*][GRE], Phys. Rev. Research 3 (2021), 033031, Sections II B and VI; K. Mayer, [*A short note on the 0-fidelity*][MAY], arXiv:2109.09629, Section I | `literature-attested`: the product-SIC hierarchy background and the frame independence of $F_0$. The exact normalization used here is [SIC], Definition 2.3, with its Remark 2.4 concerning the printed expansion; these articles do not replace that definition. |

[SIC]: https://github.com/the-omega-institute/trureturing/blob/5224c87dd29457c7712c8f271d6d1f309826c348/docs/develop/theory/SIC_K_FIDELITY_PAULI_WEIGHT_GEOMETRY.md
[FIB]: https://github.com/the-omega-institute/trureturing/blob/5224c87dd29457c7712c8f271d6d1f309826c348/docs/develop/theory/FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md
[KOR]: https://arxiv.org/abs/1309.6405
[WAT]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf
[DFY]: https://arxiv.org/abs/quant-ph/0601150
[MW]: https://arxiv.org/abs/1104.1140
[GRE]: https://arxiv.org/abs/2102.08101
[MAY]: https://arxiv.org/abs/2109.09629

## 追加锚（本行以下为增补区）
