# Forbidden-word stopping frequency and balanced borders

## 1. The stopped experiment and its sources

**Definition 1.1 (Terminal-inclusive stopped frequency).** Let $n\ge1$ be an integer and let $w=w_1\cdots w_n\in\{0,1\}^n$ be an actual word. On the product probability space $\{0,1\}^{\mathbb N}$ with fair product measure, let $X_1,X_2,\ldots$ be the coordinate variables, so they are independent and $\mathbb P(X_i=0)=\mathbb P(X_i=1)=1/2$. Define

$$
\tau_w=\min\{t\ge n:X_{t-n+1}\cdots X_t=w\},\qquad
N_w=\sum_{i=1}^{\tau_w}X_i,\qquad
q^w=\mathbb E\!\left[\frac{N_w}{\tau_w}\right].
\tag{1.1}
$$

The sum includes every letter of the terminal occurrence, including all its ones. The expectation is taken after division by the random length. Use $\min\varnothing=\infty$; on $\{\tau_w=\infty\}$ the ratio may be assigned zero. This event has probability zero, and existence and integrability are established in the proof of Theorem 2.1.

This is the observable in Bóna–Maga–Richey [BMR1, BMR2, Definition 2.5]. Their Conjecture 6.1 consists of a sentence about $\rho^w$ followed by the sentence “The same holds with $\rho^w$ replaced by $q^w$.” The latter sentence, with exactly (1.1), is the assertion addressed here.

**Definition 1.2 (Actual borders and signed border polynomial).** For $1\le j\le n$, write $w_{[1,j]}=w_1\cdots w_j$ and $w_{[n-j+1,n]}=w_{n-j+1}\cdots w_n$. Put

$$
\begin{aligned}
B(w)&=\{j\in\{1,\ldots,n\}:w_{[1,j]}=w_{[n-j+1,n]}\},\\
a_j&=\sum_{i=1}^j w_i,\qquad d_j=2a_j-j\quad(1\le j\le n),\\
C_w(u)&=\sum_{j\in B(w)}u^j,\qquad
H_w(u)=\sum_{j\in B(w)}d_j u^j,\\
D_w(s)&=1+(1-s)C_w(2/s)\quad(0<s\le1).
\end{aligned}
\tag{1.2}
$$

The full length $n$ belongs to $B(w)$. A nonempty border is balanced when its number of ones equals its number of zeros, equivalently $d_j=0$. The condition that $w$ has balanced borders means $d_j=0$ for every $j\in B(w)$, including $j=n$. The set and coefficients in (1.2) come from the same word; arbitrary polynomial coefficients are not allowed.

**Definition 1.3 (Avoidance frequency).** For an integer $m\ge1$, let $\Omega_m^w$ be the set of binary words of length $m$ containing no contiguous occurrence of $w$, let $U_m$ be uniform on this nonempty finite set, and put

$$
\rho_m^w=\frac1m\mathbb E[|U_m|_1].
\tag{1.3}
$$

When this sequence has a limit, denote it by $\rho^w$. Theorems below concern (1.1) without a hypothesis about this limit.

**Mathematical sources 1.4 (Supplied identities and domain correspondence).** The joint first-hit probability generating function supplied by [BMR1, BMR2, Fact 2.9, (2.12)] is

$$
\begin{aligned}
\Phi_w(s,y)&=\mathbb E[s^{\tau_w}y^{N_w}]=R_w(s,y)^{-1},\\
R_w(s,y)&=1+\left(1-\frac{s(1+y)}2\right)
             \sum_{j\in B(w)}(2/s)^j y^{-a_j}.
\end{aligned}
\tag{1.4}
$$

For each $0<s<1$, (1.4) holds for positive $y$ sufficiently close to $1$. Here the length variable is $s$, the ones marker is $y$, and the measure is the fair product measure of Definition 1.1. In particular $R_w(s,1)=D_w(s)$. This supplies a first-hit law, including the terminal word, rather than a law conditioned on avoidance.

The integration method is also supplied: [BMR1, BMR2, Example 2.10] integrates $s^{-1}\partial_y\Phi_w(s,1)$ to compute $q^{11}$. Balanced-border sufficiency and coefficient symmetry are [BMR1, Proposition 3.5; BMR2, Proposition 3.3]. The unbordered integral formula is [BMR1, Proposition 3.9, (3.7); BMR2, Proposition 3.7, (3.8)]. The one-sided coefficient injections are [BMR1, Theorem 3.7 and §4.3; BMR2, Theorem 3.5 and §4.3]. The already supplied relation to all finite avoidance frequencies is [BMR1, Theorem 3.10 and §4.4; BMR2, Theorem 3.8 and §4.4]:

$$
q^w=\frac12+\sum_{m=n}^{\infty}
\frac{\mathbb P(\tau_w>m)}{m+1}\left(\frac12-\rho_m^w\right).
\tag{1.5}
$$

These are intermediate results, including their proofs, rather than additional conclusions of this volume. The reciprocal-length signed transfer in Theorem 2.1 uses (1.4) to obtain an integral with a pointwise sign for every actual word.

The repository mathematical suppliers [R] include the full first-hit decomposition, signed-moment calculus, scalar evaluation and reciprocal substitutions, escaping weighted averages, and the coefficient lower-envelope and flip arguments. In particular, the algebra used inside Theorem 2.1 is supplied by the private `prefix_imbalance_lower`, `coeff_lower_at_longest_positive`, `hEval_cut`, `hEval_lower_envelope`, `linearEnvelope`, `lowerPoly_eq_linearEnvelope` and `lowerPoly_identity` in `BorderImbalanceExclusion.lean`. With that source's notation,

$$
C_w(u)=\operatorname{corrEval}(w,u),\qquad
H_w(u)=\operatorname{hEval}(w,u),\qquad
F_k(u)=\operatorname{linearEnvelope}(k,u),
\tag{1.6}
$$

where $F_k$ is the envelope used in the proof below; for $k\ge2$, $F_k(u)=\operatorname{lowerPoly}(k-2,u)$. Neither the envelope identity nor its prefix bound is a new algebraic supplier here. The transfer evaluates them on $u=2/s\ge2$ instead of at an avoidance growth root. The `BonaMagaRicheyHalfFrequency.result` supplier concerns the convergence-to-half criterion for (1.3), namely the first sentence of [BMR2, Conjecture 6.1].

The following source correspondences keep the observables distinct.

| Source and hypotheses | Observable and relation to (1.1) |
| --- | --- |
| [CMRW1, §2, Propositions 2.1–2.2; Theorem 3.12], a single forbidden pattern on a uniform alphabet of size $r$ | Its unweighted correlation polynomial is $\varphi_w(t)=\sum_{j\in B(w)}t^{j-1}=C_w(t)/t$. The mean first-hit time is $r\varphi_w(r)$; avoidance counts, entropy, zeta functions and couplings do not themselves give the terminal letter ratio in (1.1). |
| [DPR1, Definitions 2.1–2.2, Theorem 2.3; DPR2, Definitions 2–3, Theorem 4], Bernoulli parameter $p\in(0,1)$, two words $v,w$, neither a contiguous factor of the other for the race formula | Here $O(v,w)$ is the set of nonempty words that are both a suffix of $v$ and a prefix of $w$. The correlation is $vw_p=\sum_{b\in O(v,w)}p^{-|b|_1}(1-p)^{-|b|_0}$ and the race observable is $\mathbb P_p(\tau_v<\tau_w)$. The published Definition 2 explicitly excludes the losing word from a winning terminal sequence; the displayed original Definition 2.1 omits that exclusion. The corresponding correlation and win-probability formulas agree, but this does not identify a win indicator with $N_w/\tau_w$. |
| [K, (1), Theorem 2.1 and its proof], subsequences with indices $i_1<\cdots<i_k$, without a consecutiveness requirement | Its density is the number of such subsequences divided by $\binom{m}{k}$, and, for a measurable $f:[0,1]\to[0,1]$, its limiting integral is $k!\int_{x_1<\cdots<x_k}\prod_i f(x_i)^{w_i}(1-f(x_i))^{1-w_i}\,dx_1\cdots dx_k$. This samples ordered subsequences at a deterministic length, rather than stopping at a contiguous first hit. |

## 2. Reciprocal-length transfer and the all-word criterion

**Theorem 2.1 (Stopped-ratio transfer, sign and zero).** For every integer $n\ge1$ and every word $w\in\{0,1\}^n$, with the law and definitions (1.1)–(1.2),

$$
\boxed{\displaystyle
2q^w-1=\int_0^1
 \frac{(1-s)H_w(2/s)}{sD_w(s)^2}\,ds.}
\tag{2.1}
$$

The integral is absolutely convergent at both endpoints. If $d_j=0$ for all $j\in B(w)$, then $q^w=1/2$. Otherwise the finite nonempty set $\{j\in B(w):d_j\ne0\}$ has a largest element $k$, and

$$
\operatorname{sign}(q^w-1/2)=\operatorname{sign}(d_k).
\tag{2.2}
$$

Consequently

$$
q^w=\frac12
\quad\Longleftrightarrow\quad
\text{every nonempty border of }w\text{ is balanced}.
\tag{2.3}
$$

There is no assumption about an avoidance-frequency limit, a growth root, or irreducibility.

*Proof.* Fix $n$ and $w$. Independence on disjoint length-$n$ blocks gives, for every integer $m\ge0$,

$$
\mathbb P(\tau_w>mn)\le(1-2^{-n})^m.
\tag{2.4}
$$

Indeed, if any of the first $m$ such blocks is exactly $w$, then $\tau_w\le mn$; these block events have independent probability $2^{-n}$. Thus $\tau_w<\infty$ almost surely and has an exponential tail. Since $0\le N_w\le\tau_w$, the ratio in (1.1) lies in $[0,1]$. Set

$$
A_w=2N_w-\tau_w,\qquad |A_w|\le\tau_w.
\tag{2.5}
$$

For each fixed $0<s<1$, the generating function and its first derivatives are represented by their expectations in a neighborhood of $y=1$. For example, choose $0<\epsilon<1/2$ with $s(1+\epsilon)<1$. For $1-\epsilon<y<1+\epsilon$, the absolute derivative terms are bounded by constant multiples of $\tau_w[s(1+\epsilon)]^{\tau_w}$, whose expectation is finite. This justifies the length and letter differentiations of (1.4).

Apply the supplied signed-moment operation, here written as

$$
\mathcal L=2y\partial_y-s\partial_s.
\tag{2.6}
$$

It sends the monomial $s^t y^a$ to $(2a-t)s^t y^a$. This is the signed-moment calculus of [R, `BalancedBordersHalfFrequency.signedMoment`, its monomial and product rules]. Write

$$
V(s,y)=1-\frac{s(1+y)}2,\qquad
T_j(s,y)=(2/s)^j y^{-a_j}.
$$

At $y=1$, the elementary calculations in that calculus give

$$
\begin{aligned}
(\mathcal L V)(s,1)
 &=\left(-sy+\frac{s(1+y)}2\right)_{y=1}=0,\\
\mathcal L T_j&=(j-2a_j)T_j=-d_jT_j,\\
(\mathcal L R_w)(s,1)&=-(1-s)H_w(2/s).
\end{aligned}
\tag{2.7}
$$

By the reciprocal rule applied to (1.4), this yields the first-hit signed moment

$$
M_w(s):=\mathbb E[A_w s^{\tau_w}]
 =(\mathcal L\Phi_w)(s,1)
 =\frac{(1-s)H_w(2/s)}{D_w(s)^2}.
\tag{2.8}
$$

The cancellations and reciprocal algebra in (2.7)–(2.8) use the supplied moment machinery; the relevant consumer is the following normalization at the actual random stopping length. For every integer $t\ge1$, the measure

$$
\nu_t(ds)=t s^{t-1}\,ds\quad(0<s<1)
\tag{2.9}
$$

has mass one. Thus the random signed proportion $A_w/\tau_w$ can be averaged against $\nu_{\tau_w}$ without changing its expectation. The interchange is absolutely justified by Tonelli and (2.5):

$$
\begin{aligned}
\mathbb E\!\left[\int_0^1 |A_w|s^{\tau_w-1}\,ds\right]
 &=\mathbb E\!\left[\frac{|A_w|}{\tau_w}\right]\le1,\\
2q^w-1
 &=\mathbb E\!\left[\frac{A_w}{\tau_w}
             \int_0^1\tau_w s^{\tau_w-1}\,ds\right]\\
 &=\int_0^1\mathbb E[A_w s^{\tau_w-1}]\,ds
  =\int_0^1\frac{M_w(s)}s\,ds.
\end{aligned}
\tag{2.10}
$$

Substitute (2.8) to obtain (2.1). In particular this step retains the expectation of the random ratio. Neither $\mathbb E[N_w]/\mathbb E[\tau_w]$ nor an avoidance-conditioned frequency replaces it. Fubini also gives

$$
\int_0^1\left|\frac{M_w(s)}s\right|ds
\le\mathbb E\!\left[\frac{|A_w|}{\tau_w}\right]\le1.
\tag{2.11}
$$

For explicit endpoint control, let $g_w(s)$ denote the integrand in (2.1). Since $|d_j|\le j\le n$,

$$
|H_w(2/s)|\le n C_w(2/s),\qquad
C_w(2/s)\ge(2/s)^n,\qquad D_w(s)\ge1.
$$

For $0<s\le1/2$, the additional inequality $D_w(s)\ge(1-s)C_w(2/s)$ gives

$$
|g_w(s)|\le\frac{n}{s(1-s)C_w(2/s)}
\le\frac{2n}{2^n}s^{n-1}.
\tag{2.12}
$$

On $1/2\le s<1$, the finite polynomial $H_w$ is bounded on $2\le2/s\le4$, and

$$
|g_w(s)|\le2(1-s)\max_{2\le u\le4}|H_w(u)|.
\tag{2.13}
$$

These bounds prove absolute convergence separately at zero and one, including $n=1$. They also give the continuous endpoint value $g_w(1)=0$ and $g_w(0)=0$ for $n\ge2$. For $n=1$, $B(w)=\{1\}$ and

$$
g_w(s)=\frac{2d_1(1-s)}{(2-s)^2},\qquad g_w(0)=d_1/2.
\tag{2.14}
$$

It remains to determine the sign of (2.1). If every border is balanced, then $H_w=0$, proving sufficiency directly, consistently with [BMR2, Proposition 3.3]. Otherwise let $k$ be the largest border length with nonzero imbalance. Suppose first that $d_k>0$, hence $d_k\ge1$ because it is an integer. The prefix imbalance obeys

$$
d_j\ge d_k-(k-j)\ge j+1-k\quad(1\le j\le k),
\tag{2.15}
$$

since extending a prefix by one binary letter changes its imbalance by either $1$ or $-1$. Equivalently, $d_k-d_j$ is the sum of $k-j$ numbers in $\{-1,1\}$, so it is at most $k-j$. This is exactly the supplied prefix bound [R, `BorderImbalanceExclusion.prefix_imbalance_lower`].

Put $c_j=d_j$ for $j\in B(w)$ and $c_j=0$ otherwise. For a missing border $j<k$, $c_j=0\ge j+1-k$. For a present border, (2.15) gives the same lower bound. All $c_j$ with $j>k$ vanish by the choice of $k$. Therefore, for every real $u\ge0$, the supplied cut and coefficient-envelope comparison give

$$
H_w(u)=\sum_{j=1}^k c_j u^j
\ge F_k(u):=\sum_{j=1}^k(j+1-k)u^j.
\tag{2.16}
$$

This uses the imbalances of nested prefixes of the actual word, even when its different borders have different signs. The envelope in (2.16), together with its algebraic identity below, is the complete lower-envelope intermediate from [R], not a separate new polynomial theorem.

For $k=1$ and $k=2$ one has $F_1(u)=u$ and $F_2(u)=u^2$, respectively. For $k\ge3$, the supplied identity `lowerPoly_identity`, with index $k-2$, reads

$$
(u-1)^2 F_k(u)
 =(u-2)u^{k+1}+(k-1)u^2-(k-2)u.
\tag{2.17}
$$

For completeness its polynomial evaluation can be obtained without division by a series: $F_2=u^2$ and (2.16) imply

$$
F_{k+1}(u)=uF_k(u)-(k-1)u\quad(k\ge2).
$$

The identity holds at $k=2$ by direct multiplication. Multiplying the recurrence by $(u-1)^2$ changes its right side to

$$
u\big[(u-2)u^{k+1}+(k-1)u^2-(k-2)u\big]
 -(k-1)u(u-1)^2
 =(u-2)u^{k+2}+ku^2-(k-1)u,
$$

which is the same identity at $k+1$. This is the supplied induction and its index correspondence.

For $u\ge2$, the first term on the right of (2.17) is nonnegative, while

$$
(k-1)u^2-(k-2)u
 =u\big((k-1)(u-1)+1\big)>0.
\tag{2.18}
$$

Since $(u-1)^2>0$, equations (2.16)–(2.18), together with $k=1,2$, show $H_w(u)>0$ for all $u\ge2$. In particular $H_w(2/s)>0$ at every $0<s<1$.

If $d_k<0$, use the supplied flip correspondence: the complemented word $\overline w=(1-w_1)\cdots(1-w_n)$ has the same border lengths and imbalances $\overline d_j=-d_j$. This follows because equality of a prefix and a suffix is preserved by complement, and $|\overline w_{[1,j]}|_1=j-a_j$. Its longest nonzero border is still $k$, now with positive imbalance, and $H_{\overline w}=-H_w$. The preceding argument gives $H_w(u)<0$ for all $u\ge2$.

Finally $D_w(s)>0$ and $(1-s)/s>0$ for $0<s<1$. Thus $g_w$ has the strict sign of $d_k$ throughout that interval. It is continuous there and nonzero, so its integral on any fixed closed subinterval with nonempty interior has that strict sign; the remaining integrand has the same sign, and the whole integral is absolutely convergent. This proves the strict statement (2.2). Hence an unbalanced border precludes $q^w=1/2$, giving necessity in (2.3).

*Short lengths in the same stopped experiment.* For $w=1$, the first-hit time has $\mathbb P(\tau_w=t)=2^{-t}$ for every $t\ge1$, and $N_w=1$. Therefore

$$
q^1=\sum_{t=1}^{\infty}\frac{2^{-t}}t=\log2>\frac12,\qquad
q^0=1-\log2<\frac12.
\tag{2.19}
$$

The series equality follows by integrating the geometric series from $0$ to $1/2$; strictness also follows from Theorem 2.1. Complementation pairs stopping at $w$ with stopping at $\overline w$ and replaces the proportion by its complement under a measure-preserving flip, which gives the second equality. For length two, $B(01)=B(10)=\{2\}$ with $d_2=0$, so $q^{01}=q^{10}=1/2$. For $11$ the imbalances at borders $1,2$ are $1,2$, and for $00$ they are $-1,-2$; thus $q^{11}>1/2$ and $q^{00}<1/2$. The value for $11$ is also the integrated special case of [BMR1, BMR2, Example 2.10]. No short length is discarded by Theorem 2.1.

*Mixed signs and a balanced full word.* The following borders can be checked directly by comparing prefixes and suffixes:

| Word $w$ | $B(w)$ | $(d_j)_{j\in B(w)}$ in increasing order | Consequence of Theorem 2.1 |
| --- | --- | --- | --- |
| $10001$ | $\{1,5\}$ | $(1,-1)$ | $q^w<1/2$ |
| $100011110001$ | $\{1,5,12\}$ | $(1,-1,0)$ | $q^w<1/2$ |
| $11000011$ | $\{1,2,8\}$ | $(1,2,0)$ | $q^w>1/2$ |

These words occur among the mixed-sign and balanced-word examples in [BMR1, BMR2]. In the second and third rows the full word is balanced; a shorter unbalanced border decides the sign. In the first two rows, the sign of the shortest border differs from the sign of the longest nonzero border. Thus neither the full-word count alone nor an assumption that all nonzero border imbalances have one sign can replace the criterion.

*Correspondence with the supplied unbordered integral.* If $B(w)=\{n\}$ and $a=a_n$, then $H_w(u)=(2a-n)u^n$. Under $t=2/s-2$, one has $u=t+2$, $1-s=t/(t+2)$ and

$$
D_w(s)=1+t(t+2)^{n-1},\qquad |ds|=\frac{2}{(t+2)^2}\,dt.
$$

Consequently (2.1) becomes

$$
q^w=\frac12+\left(a-\frac n2\right)
\int_0^{\infty}
\frac{t(t+2)^{n-2}}{[1+t(t+2)^{n-1}]^2}\,dt.
\tag{2.20}
$$

For $n\ge3$, this is exactly [BMR1, Proposition 3.9; BMR2, Proposition 3.7]. The substitution is a correspondence with that supplied special case; the all-word result uses the full signed border polynomial in (2.1). $\square$

## 3. Mathematical scope and references

**Scope 3.1.** Theorem 2.1 uses one actual finite binary word and fair independent input, with the terminal occurrence included. Its integral transfers a first-hit signed moment to the expectation of a proportion. The supplied coefficient envelope gives its sign on the full interval $u\ge2$. The result therefore proves the second sentence of [BMR1, BMR2, Conjecture 6.1] in the literal model of their Definition 2.5, and additionally identifies the strict sign by the longest unbalanced border.

The theorem does not give a biased-input analogue, a multiple-word race analogue, an arbitrary-alphabet analogue, or a global ordering between $q$ and $\rho$. For biased input, even the one-letter cancellation in (2.7) changes; for races, cross-correlations enter the joint first-hit law. An extension would have to specify the new observable and law and establish both its corresponding transfer and the required sign comparison. Existence of $\lim_m\rho_m^w$ without an additional convergence argument, and irreducibility of associated border polynomials, are separate questions. Formula (1.5) is the supplied finite-$\rho$ relation and is not a proof of a global $q/\rho$ comparison.

**References 3.2 (Primary mathematical sources).**

[BMR1] Miklós Bóna, Balázs Maga and Jacob Richey, *Letter frequency in shifts of finite type with one forbidden word*, [arXiv:2606.06655v1](https://arxiv.org/pdf/2606.06655v1). Definition 2.5; Fact 2.9, (2.12); Example 2.10; Proposition 3.5; Theorem 3.7 and its proof in §4.3; Proposition 3.9; Theorem 3.10 and its proof in §4.4; Conjecture 6.1.

[BMR2] Miklós Bóna, Balázs Maga and Jacob Richey, *Letter frequency in shifts of finite type with one forbidden word*, [arXiv:2606.06655v2](https://arxiv.org/pdf/2606.06655v2), [version history](https://arxiv.org/abs/2606.06655). Definition 2.5; Fact 2.9, (2.12); Example 2.10; Proposition 3.3; Theorem 3.5 and its proof in §4.3; Proposition 3.7; Theorem 3.8 and its proof in §4.4; Conjecture 6.1. The definition of $q^w$ and the second sentence of Conjecture 6.1 agree between [BMR1] and [BMR2]; the proposition and theorem numbers above specify the corresponding intermediate results.

[CMRW1] Nishant Chandgotia, Brian Marcus, Jacob Richey and Chengyu Wu, *Shifts of finite type obtained by forbidding a single pattern*, [arXiv:2409.09024v1](https://arxiv.org/pdf/2409.09024v1), §2 and Theorem 3.12. Journal bibliographic counterpart: [DOI 10.3934/dcds.2025152](https://doi.org/10.3934/dcds.2025152). The mathematical correspondence in 1.4 is to the specified preprint version.

[DPR1] Mathew Drexel, Xuanshan Peng and Jacob Richey, *Word length, bias and bijections in Penney's ante*, [arXiv:2409.19195v1](https://arxiv.org/pdf/2409.19195v1), §2, Definitions 2.1–2.2 and Theorem 2.3.

[DPR2] Mathew Drexel, Xuanshan Peng and Jacob Richey, *Word length, bias and bijections in Penney's ante*, *Electronic Journal of Combinatorics* **32**(4), P4.57, [published text](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i4p57/pdf), [DOI 10.37236/13609](https://doi.org/10.37236/13609), §2, Definitions 2–3 and Theorem 4.

[K] Richard Kenyon, *Patterns in sequences*, [arXiv:2601.04078v1](https://arxiv.org/pdf/2601.04078v1), (1), §2, Theorem 2.1 and its proof.

**References 3.3 (Repository mathematical suppliers).** [R] denotes the following sources at revision `fe7b34d6b30cf7ef13938bcf35fef00afc8dbd1a` in `D5/S1/Words/Forbidden/`, together with their corresponding mathematical expositions under `Blueprint/D5/S1/Words/Forbidden/`:

| Source | Supplied mathematics |
| --- | --- |
| `ForbiddenWordCounting.lean` | `FirstHit`, uniqueness and existence, snoc extension partition, overlap splice bijection and weighted counts, `firstHit_letters_equation`, `firstHit_overlap_equation`, and `forbidden_word_counting_identity`, including their private calculations. |
| `BalancedBordersHalfFrequency.lean` | `signedMoment`, monomial, sum and product rules, the letter cancellation, `balanced_tail`, overlap and word moments, denominator nonvanishing, `balanced_signedMoment_avoidSeries`, and exact balanced finite-frequency symmetry. |
| `ForbiddenWordRationalBoundary.lean` | Real evaluation, summability and finite-product calculations, scalar count, length and moment identities, tail imbalance, reciprocal overlap and denominator identities, and the growth-root boundary chain. |
| `ForbiddenWordGrowth.lean` | Submultiplicative growth, exponential summability, escaping weighted-average estimates and their private preliminary calculations. |
| `BorderImbalanceExclusion.lean` | Prefix bound, coefficient cut and lower envelope, `linearEnvelope`, `lowerPoly`, its unconditional identity and its envelope correspondence, and the complete border, imbalance, polynomial and avoidance flip correspondences. |
| `BonaMagaRicheyHalfFrequency.lean` | Normalized density weights, total mass and finite-mass escape, `assumed_limit_imbalance_ratio`, boundary moment cross identity and the short-length arguments for the convergence-to-half criterion for $\rho_m^w$. |

The source correspondences in (1.4)–(1.6) and [R] supply the old intermediates. The retained connection is (2.8)–(2.10) for the original stopped proportion, followed by use of the supplied envelope on $u=2/s\ge2$ to obtain (2.2)–(2.3). This finite source correspondence makes no assertion of worldwide priority or of the present status of every subsequent treatment of the conjecture.

## 追加锚（本行以下为增补区）
