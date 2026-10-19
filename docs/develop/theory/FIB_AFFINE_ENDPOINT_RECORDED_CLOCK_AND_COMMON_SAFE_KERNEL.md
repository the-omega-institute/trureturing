# Recorded-clock collapse and a common safe kernel at the affine endpoint

At the candidate minimum of $d+5$ exact reads, the recorded clock couples the kernels at different affine slopes. A polynomial kernel vector of degree at most two has only common-kernel coefficients. An identically singular pencil of rank three at every real slope consequently has a constant or cubic primitive kernel generator. The cubic case has an unsafe real-slope kernel and an actual positive-source collision. Thus every identically singular pencil still eligible for uniform recovery has a single common safe kernel, whose recorded signal is a polynomial of degree at most $d-1$. This is an all-history necessary restriction; the sharp uniform read count remains unresolved.

## 1. Actual model, clock, and target

**Definition 1.1 (one predetermined cumulative history).** Fix $d\ge0$ and $n=d+5$. Let

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\quad A_{i+1}=W_iA_i\quad(0\le i<n-1),
$$

where every $W_i$ is a predetermined finite word in $M,J$, possibly empty. Products act on the left and are executed from right to left. The recorded indices are exactly $0,\ldots,n-1$. Every recorded scalar advances this index, including an empty-word repeat; unread atoms do not.

Write $V=\operatorname{Mat}_{2\times2}(\mathbb R)$ and

$$
\mathcal R_+=\left\{S=\begin{pmatrix}p&q\\r&s\end{pmatrix}:
 p,q,r,s>0,\ ps=qr\right\}.
$$

An actual effective target is $(S,k,D)\in\mathcal R_+\times\mathbb R\times\mathcal P_d$, with observations

$$
z_i=(1+ki)\operatorname{tr}(A_iS)+D(i).
\tag{1.1}
$$

Here $\mathcal P_h$ is the real polynomial space of degree at most $h$, including zero; set $\mathcal P_{-1}=\{0\}$. The slope $k$ is arbitrary real. All sampled gain zeros and negative gains are included. The target contains the entire polynomial $D$, used throughout its run.

In original parameters $S=\alpha R$, $k=\beta/\alpha$, $\alpha>0$, and $R=c\ell$ has a strictly positive column $c$ and one strictly positive row $\ell$ fixed throughout its run. Each effective source has the actual realization

$$
\alpha=1,\quad\beta=k,\quad R=S,\qquad
c=(p,r)^{\mathsf T},\quad \ell=(1,q/p).
\tag{1.2}
$$

Indeed $rq/p=s$, so $c\ell=S$ and $\ell A_ic=\operatorname{tr}(A_iS)$. Both atoms preserve positive columns:

$$
M(v_1,v_2)^{\mathsf T}=(v_2,v_1+v_2)^{\mathsf T},\qquad
J(v_1,v_2)^{\mathsf T}=(v_2,v_1)^{\mathsf T}.
$$

Thus the same row realizes every read and unread state. There is no reset, copy, free row change, independent lift, per-read drift, inverse acquisition, or combination of unexecuted histories. Candidate runs can have different fixed rows, as the source domain permits.

For a fixed effective target the original relation/gain representations are exactly $R=S/t$, $\alpha=t>0$, $\beta=kt$, with $D$ fixed. A fixed relation has the separate internal positive-factor freedom $c\mapsto\mu c$, $\ell\mapsto\ell/\mu$, $\mu>0$. These credited representation fibres do not identify distinct effective triples.

## 2. Credited quotient, safe directions, and a complete realization interface

Define

$$
\mathcal L(X)_i=\operatorname{tr}(A_iX),\qquad
(\mathcal I v)_i=iv_i,
$$

$$
(\Lambda v)_j=\sum_{h=0}^{d+1}(-1)^{d+1-h}
 \binom{d+1}{h}v_{j+h},\qquad j=0,1,2,3,
$$

$$
B=\Lambda\mathcal L,\qquad C=\Lambda\mathcal I\mathcal L,
\qquad T_k=B+kC.
\tag{2.1}
$$

These operators always come from the one actual history in Definition 1.1. They are not arbitrary substituted matrices. In fixed bases $T_k$ is a four-by-four real matrix pencil. Call it **regular** when $\det T_k$ is not identically zero, and **identically singular** otherwise. A regular pencil can still have singular real slopes.

The exact quotient identity

$$
\ker\Lambda=\operatorname{ev}(\mathcal P_d)
\tag{2.2}
$$

is the credited Lemma 2.1 of *Affine slope transfer and sign-change obstructions at the minimum read count*. Evaluation is on the $n$ distinct recorded nodes. In particular, for a vector $u\in\ker\Lambda$ its unique polynomial is

$$
P_u(t)=\sum_{h=0}^d u_h
 \prod_{\substack{0\le b\le d\\b\ne h}}\frac{t-b}{h-b}.
\tag{2.3}
$$

The products are one when $d=0$; all other denominators are nonzero node differences. The underlying root fact is that division by $t-a$ at a root removes one degree and leaves every other distinct root in the quotient. Thus a nonzero polynomial has no more distinct roots than its degree. All degree bounds below include zero and lower actual degrees.

Define the closed cones and functional

$$
\mathcal K_{\rm safe}=\left\{\begin{pmatrix}a&b\\c&e\end{pmatrix}:
 a,e\ge0,\ b,c\le0\right\},\qquad
\mathcal U=\mathcal K_{\rm safe}\cup(-\mathcal K_{\rm safe}),
\qquad \Phi(X)=a-b-c+e.
\tag{2.4}
$$

Theorem 2.1 and Theorem 3.1 of [Affine-gain erasure, positive secants, and drift-kernel collisions](FIB_AFFINE_GAIN_ERASURE_SPAN_AND_POSITIVE_GAIN_COLLISIONS.md) supply these exact interfaces:

* A nonzero $X$ is a difference of two distinct members of $\mathcal R_+$ exactly when $X\notin\mathcal U$.
* A linear subspace contained in $\mathcal U$ has dimension at most one. Thus prescribed-slope injectivity is equivalent to $\ker T_a$ being zero or a line generated by a nonzero safe vector.
* The functional $\Phi$ is strictly positive on nonzero safe vectors and strictly negative on their negatives; it vanishes on no nonzero member of $\mathcal U$.

These are credited results, not new claims of this volume. For an explicit endpoint interface, recall their construction. If $X=(\begin{smallmatrix}a&b\\c&e\end{smallmatrix})\notin\mathcal U$, put $\delta=\det X$ and $F(x,y)=exy+a-cx-by$. The coefficients $a,-b,-c,e$ have both strict signs. The limits at $(\varepsilon,\varepsilon)$, $(T,T)/T^2$, $(T,T^{-2})/T$, and $(T^{-2},T)/T$ isolate these four coefficients. Choose positive points with $F_-<0<F_+$ and their straight positive segment. Let $m>0$ bound below every entry of $(\begin{smallmatrix}xy&x\\y&1\end{smallmatrix})$ on the segment. Choose

$$
\tau>\max\left(\frac{\max|X_{uv}|}{m},
 \frac{|\delta|}{\min(-F_-,F_+)}\right).
$$

At a segment point with $F=-\delta/\tau$, the credited endpoints are

$$
S_0=\tau\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
S_1=S_0+X.
\tag{2.5}
$$

Both are strictly positive of rank one; the determinant identity is $\det S_1=\tau F+\delta=0$. The formula includes $\delta=0$ and matrices with zero individual entries.

**Realization interface 2.1 (every same-slope exclusion).** If $0\ne X\in\ker T_a$ is unsafe, take the endpoints (2.5), ordered $S_1-S_0=X$. Put

$$
u_i=(1+ai)\operatorname{tr}(A_iX),\qquad
D_0=0,\quad D_1=-P_u,\quad k_0=k_1=a.
\tag{2.6}
$$

Equation (2.2) gives $u_i=P_u(i)$ at every recorded node, since $\Lambda u=T_aX=0$. Therefore

$$
z_i^{(1)}-z_i^{(0)}=(1+ai)\operatorname{tr}(A_iX)-P_u(i)=0
\tag{2.7}
$$

at all $n$ positions. Each $D_b$ is one entire polynomial of degree at most $d$. Apply (1.2) to each endpoint and execute exactly the given words with its own fixed row. This gives the actual positive realizations, including every unread state, sampled gain zero, and negative gain. The sources differ, so this is a target collision, not a representation scale. Every exclusion below uses this same explicit bridge.

For later comparison, if $T_aS_0=T_bS_1$ for positive rank-one sources, use instead

$$
u_i=(1+ai)\operatorname{tr}(A_iS_0)
 -(1+bi)\operatorname{tr}(A_iS_1),\qquad
D_0=0,\quad D_1=P_u.
\tag{2.8}
$$

The identical quotient and factorization interfaces give all observations on that same history. The sign in (2.8) differs from (2.6) because $u$ is now ordered as run zero minus run one.

## 3. A low-degree kernel vector collapses under the recorded clock

**Theorem 3.1 (N1: polynomial-kernel clock collapse).** Let

$$
X(k)=\sum_{a=0}^m k^aX_a,\qquad 0\le m\le2,
\qquad T_kX(k)=0\quad\hbox{for every real }k.
$$

No positivity or rank assumption is made on these matrices. For every coefficient there is a polynomial $Q_a\in\mathcal P_{d-1}$ such that

$$
\operatorname{tr}(A_iX_a)=Q_a(i)\quad(0\le i<n).
\tag{3.1}
$$

In particular $BX_a=CX_a=0$ for every $a$.

**Proof.** Interpolate the first $d+1$ sampled values as a polynomial in two variables:

$$
P(k,t)=\sum_{h=0}^d(1+kh)\operatorname{tr}(A_hX(k))
 \prod_{\substack{0\le b\le d\\b\ne h}}\frac{t-b}{h-b}.
\tag{3.2}
$$

It has degree at most $d$ in $t$ and at most $m+1$ in $k$. By $T_kX(k)=0$ and (2.2), for every real $k$,

$$
P(k,i)=(1+ki)\operatorname{tr}(A_iX(k))\quad(0\le i<n).
\tag{3.3}
$$

All coefficients are real polynomials, so these are polynomial identities in $k$. Write $P(k,t)=\sum_{a=0}^{m+1}k^aP_a(t)$, allowing zero coefficients, and form

$$
R(t)=\sum_{a=0}^{m+1}(-1)^at^{m+1-a}P_a(t).
\tag{3.4}
$$

For every actual noninitial recorded node $j=1,\ldots,d+4$, (3.3) gives

$$
R(j)=j^{m+1}P(-1/j,j)=0.
$$

The degree of $R$ is at most $d+m+1\le d+3$, smaller than these $d+4$ distinct roots. Hence $R=0$. This is where the consecutive endpoint clock enters; no extra observations have been introduced.

To divide without inverting $t$, set

$$
Q_0=P_0,\qquad Q_a=P_a-tQ_{a-1}\quad(1\le a\le m),
\qquad Q(k,t)=\sum_{a=0}^m k^aQ_a(t).
$$

Coefficient comparison gives

$$
P-(1+kt)Q=k^{m+1}(P_{m+1}-tQ_m),\qquad
P_{m+1}-tQ_m=(-1)^{m+1}R=0.
\tag{3.5}
$$

Thus $P=(1+kt)Q$ in $\mathbb R[k,t]$, including $t=0$. If $Q\ne0$, view it as a polynomial in $t$ over the integral domain $\mathbb R[k]$. Its nonzero leading coefficient is multiplied by $k$ in the new highest power of $t$, so multiplication by $1+kt$ raises its $t$-degree by exactly one. Consequently $\deg_tQ\le d-1$. If $d=0$, a nonzero $Q$ would give $\deg_tP\ge1$, which is impossible; hence $Q=P=0$. If $Q=0$ at any $d$, the desired degree statements hold by convention.

At each recorded node, (3.3) and (3.5) imply

$$
(1+ki)\bigl[\operatorname{tr}(A_iX(k))-Q(k,i)\bigr]=0
\quad\hbox{in }\mathbb R[k].
$$

The first factor is a nonzero polynomial, including the constant one at $i=0$. Cancellation in this integral domain gives $\operatorname{tr}(A_iX(k))=Q(k,i)$. Comparing coefficients proves (3.1), and every $Q_a$ has degree at most $d-1$. The sequences of its values and of $tQ_a$ are both annihilated by $\Lambda$, giving $BX_a=CX_a=0$. At $d=0$ both sequences are zero. This also covers $m=0$, $m=1$, vanishing leading coefficients, and $X=0$. ∎

## 4. Primitive adjugate kernels and the constant-or-cubic dichotomy

A nonzero polynomial vector is **primitive** if its four entries have no common nonconstant real polynomial factor. Its degree is the largest degree of a nonzero entry.

**Lemma 4.1 (primitive kernel from an adjugate).** Suppose $\det T_k=0$ identically and $\operatorname{rank}T_a=3$ for every real $a$. There is a primitive polynomial vector $K(k)$ of degree at most three such that

$$
T_kK(k)=0,\qquad K(a)\ne0\quad(a\in\mathbb R).
\tag{4.1}
$$

Its value spans $\ker T_a$ at each real slope.

**Proof.** Every entry of $\operatorname{adj}(T_k)$ is a three-by-three minor of an affine pencil, hence a polynomial of degree at most three. Cofactor expansion gives $T_k\operatorname{adj}(T_k)=(\det T_k)I=0$. At a rank-three real slope some three-by-three minor is nonzero. Therefore the adjugate has a nonzero polynomial column $v(k)$.

The Euclidean algorithm in $\mathbb R[k]$, whose nonzero remainder degrees strictly decrease, gives a greatest common divisor $g$ of the nonzero entries of this column; zero entries impose no additional constraint. Divide every entry by $g$ to obtain a primitive nonzero $K$. From $gT_kK=0$ and the absence of zero divisors, $T_kK=0$. Division cannot increase its degree. If $K(a)=0$ at a real number $a$, the factor theorem makes $k-a$ a divisor of all four entries, contradicting primitivity. The kernel has dimension one at each real slope, so the nonzero $K(a)$ spans it. ∎

**Theorem 4.2 (N2: constant or cubic).** Under Lemma 4.1's hypotheses its primitive kernel vector has degree zero or three. If it has degree three, $\ker T_a$ contains an unsafe nonzero matrix at some real slope $a$, and (2.5)–(2.7) give an actual same-slope collision.

**Proof.** If $\deg K\le2$, Theorem 3.1 puts every coefficient of $K$ in $\ker B\cap\ker C$. Because $B=T_0$ has rank three, $\ker B$ is a line. All coefficients are therefore multiples of one fixed nonzero vector $K_*$. Write $K(k)=f(k)K_*$. Choosing a nonzero constant entry of $K_*$ shows that a nonconstant $f$ would be a common nonconstant divisor of all entries. Primitivity forces $f$ to be constant. Hence this case has degree zero, and the only other possible degree is three.

In the cubic case let $K_3\ne0$ be its leading coefficient. If $K_3\notin\mathcal U$, closedness of $\mathcal U$ and $K(k)/k^3\to K_3$ as $k\to+\infty$ imply $K(a)/a^3\notin\mathcal U$ for some sufficiently large positive real $a$. Since $\mathcal U$ is closed under every real scalar multiple, $K(a)$ is unsafe.

If $K_3\in\mathcal U$, reverse the sign of $K$ if necessary so that $K_3$ is safe. Then $\Phi(K_3)>0$, so $\Phi(K(k))$ is a real cubic with opposite limits at the two ends of the real line. It has a real root $a$. Primitivity gives $K(a)\ne0$, whereas $\Phi(K(a))=0$. Equation (2.4) makes that vector unsafe. The two cases exhaust all possible leading coefficients. In either case $T_aK(a)=0$, so the explicit positive-source and single-drift bridge in Section 2 supplies the claimed actual collision. Individual entries of $K$ may vanish; the argument requires only that they do not all vanish together. ∎

## 5. The surviving identically singular branch has one common safe kernel

**Theorem 5.1 (N2: restriction on every surviving singular pencil).** Fix any history in Definition 1.1. If its pencil is identically singular and it has no prescribed-slope positive-source collision at any real slope, then

$$
\operatorname{rank}T_a=3,\qquad
\ker T_a=\mathbb RK\quad\hbox{for every }a\in\mathbb R,
\qquad 0\ne K\in\mathcal K_{\rm safe},
\tag{5.1}
$$

for one constant matrix $K$. Moreover there is one $Q\in\mathcal P_{d-1}$ such that

$$
\operatorname{tr}(A_iK)=Q(i)\quad(0\le i<n),\qquad BK=CK=0.
\tag{5.2}
$$

In particular every uniformly recovering identically singular history must have this form. This conclusion does not assume that the transverse tests are sufficient.

**Proof.** If $\operatorname{rank}T_a\le2$ at some real $a$, choose two independent vectors $U,V$ in its kernel. If either is unsafe, retain it. Otherwise orient both safe and set $X=\Phi(V)U-\Phi(U)V$. This is a nonzero kernel vector with $\Phi(X)=0$, hence unsafe by the credited safe-subspace criterion. In each case (2.5)–(2.7) give a collision. Rank three with an unsafe line gives the same collision directly. Thus the no-collision hypothesis forces rank three and a safe line at every real slope.

Lemma 4.1 constructs the primitive adjugate kernel. Theorem 4.2 excludes degree three, leaving a constant nonzero vector $K$ which can be oriented safe. It spans every real-slope kernel, establishing (5.1). Applying Theorem 3.1 at $m=0$ proves (5.2).

The degree drop also has a separate direct check once the kernel is common. Since $BK=CK=0$, (2.2) gives $\mathcal L(K)=\operatorname{ev}(P)$ and $\mathcal I\mathcal L(K)=\operatorname{ev}(H)$ for $P,H\in\mathcal P_d$. The polynomial $H-tP$ has degree at most $d+1$ and vanishes at $n=d+5$ distinct nodes. It is zero. Thus either $P=0$ or $\deg P\le d-1$, and $Q=P$. At $d=0$ this forces $P=H=0$. Every excluded branch has an unsafe kernel at a real slope, so every exclusion has the actual realization and entire drift already specified in Section 2. ∎

A constant kernel vector outside $\mathcal U$ is also excluded by that bridge. The theorem does not assert that every common safe kernel survives different-slope collisions. It restricts the residual after the exact prescribed-slope tests.

## 6. Constant and affine drift consequences

**Lemma 6.1 (a safe zero signal collapses the legal matrix span).** If $0\ne K\in\mathcal K_{\rm safe}$ and $\operatorname{tr}(A_iK)=0$ for every recorded $i$, then $\operatorname{rank}\mathcal L\le2$, and consequently $\operatorname{rank}T_a\le2$ for every real $a$.

**Proof.** The initial matrix is $I$, so $\operatorname{tr}K=0$. The two nonnegative diagonal entries of $K$ must both be zero. Write its off-diagonal entries as $b,c\le0$, with at least one negative. Every legal cumulative matrix has nonnegative integer entries and determinant $\pm1$, since both atoms do and products preserve these properties. The zero trace equation is

$$
b(A_i)_{21}+c(A_i)_{12}=0.
$$

Both summands are nonpositive. If $b<0$, every $(A_i)_{21}=0$, so all $A_i$ are upper triangular. Their nonnegative integer diagonal entries have product $\pm1$; nonnegativity forces product one and both entries one. They therefore lie in the span of $I$ and the upper single-entry matrix. If $b=0$, then $c<0$ and the same argument gives the analogous lower triangular span. If both are negative, both off-diagonal entries of every $A_i$ vanish, so every $A_i=I$. In all cases their span has dimension at most two. The trace pairing is nondegenerate, so $\operatorname{rank}\mathcal L\le2$. Finally $T_a=\Lambda(\operatorname{Id}+a\mathcal I)\mathcal L$ has rank at most that of $\mathcal L$. ∎

**Corollary 6.2 (N3 at $d=0$).** A uniformly recovering five-read constant-drift history must have a regular pencil.

**Proof.** If it were identically singular, Theorem 5.1 would give a nonzero safe $K$ with signal in $\mathcal P_{-1}=\{0\}$ and rank three everywhere. Lemma 6.1 contradicts that rank. ∎

This is consistent with, and also follows from, the credited one-erasure span restrictions. It is not a new read lower bound and does not exclude regular five-read pencils.

**Corollary 6.3 (N3 at $d=1$).** A six-read identically singular history still eligible for uniform recovery has one common safe generator normalized by

$$
\operatorname{tr}K=1,\qquad \operatorname{tr}(A_iK)=1
\quad(0\le i\le5).
\tag{6.1}
$$

Equivalently its six recorded matrices lie in the affine hyperplane $\{A:\operatorname{tr}(AK)=1\}$ in matrix space.

**Proof.** Theorem 5.1 makes $Q$ constant. Its value at $A_0=I$ is $\operatorname{tr}K\ge0$. If this constant were zero, Lemma 6.1 would contradict rank three. Hence it is strictly positive. Dividing $K$ by this positive trace preserves safety, the common kernel line, and rank, and gives (6.1). The trace functional defined by a nonzero $K$ is nonzero by nondegeneracy of the trace pairing, so this level set is an affine hyperplane. ∎

The hyperplane condition is necessary only. It provides no unknown-slope inverse and does not settle the choice between six and seven reads.

## 7. Connection to the credited critical-point and quadratic tests

The mathematical supplier for this section is Sections 6–10 of *Affine slope transfer and sign-change obstructions at the minimum read count*. Its results are ordinary source-level theorems, without an assertion here of independent review or Lean verification. The following labels identify credited tests, not new versions of them.

Put

$$
\mathfrak b(X,Y)=\det(X+Y)-\det X-\det Y,
\qquad E(x,y)=\begin{pmatrix}x&xy\\1&y\end{pmatrix},
$$

$$
E_x=\begin{pmatrix}1&y\\0&0\end{pmatrix},\qquad
E_y=\begin{pmatrix}0&x\\0&1\end{pmatrix}.
$$

Every positive source is $rE(x,y)$ with $r,x,y>0$; its tangent space is $\{V:\mathfrak b(S,V)=0\}$.

**Credited R1 (regular-slope strict sign).** At an invertible $T_a$, set $H=T_a^{-1}C$ and $Q_H(S)=\mathfrak b(S,H(S))$. The supplier's Theorem 7.1 shows that any positive-source zero of $Q_H$ forces an actual collision, including a zero of a one-sided form and the identically zero case. Recovery requires one strict sign on all positive sources at that slope. This is stronger than the supplier's earlier opposite-strict-sign criterion.

**Credited R2 (safe singular transverse test).** If $\operatorname{rank}T_a=3$, $\ker T_a=\mathbb RK$ with $K$ oriented safe, and $wT_a=0$ for a nonzero covector $w$, put $h(S)=w(CS)$. The supplier's Theorem 8.1 and Proposition 8.2 show that a positive-source zero of $h$ gives an actual different-slope collision, and that derivative nonsingularity on that slice is exactly $h(S)\ne0$. Thus $h$ must have entry coefficients all of one weak sign and not all zero. The inverse function theorem supplies a local inverse only.

**Credited R3 (critical points and quadratic requirement).** The supplier's Theorems 9.1–9.2 show, specifically for this model, that any actual-target critical point forces some actual collision. In the chart $(r,x,y,k)$ after quotienting drift, the derivative determinant is $r^3j(k;x,y)$, where

$$
\begin{aligned}
c(x,y)&=\det_4[BE,BE_x,BE_y,CE],\\
b_1(x,y)&=\det_4[BE,CE_x,BE_y,CE]
             +\det_4[BE,BE_x,CE_y,CE],\\
a_2(x,y)&=\det_4[BE,CE_x,CE_y,CE],\\
j(k;x,y)&=c+b_1k+a_2k^2.
\end{aligned}
\tag{7.1}
$$

Here $\det_4$ is the determinant of four quotient columns. Recovery requires at each positive shape exactly one alternative

$$
a_2=b_1=0,\ c\ne0,
\qquad\hbox{or}\qquad
a_2\ne0,\ b_1^2-4a_2c<0.
\tag{7.2}
$$

The value $c$ has one common strict sign over all shapes, and every nonzero $a_2$ has that same sign. These are necessary tests, equivalent to everywhere derivative nonsingularity when imposed at all shapes, and are not a global injectivity theorem.

**Proposition 7.1 (the new excluded singular branches fail the credited quadratic test).** If an identically singular history fails the conclusion (5.1)–(5.2), the exclusions of Theorem 5.1 give a real slope and a positive source shape with $j=0$ in (7.1).

**Proof.** The proof of Theorem 5.1 gives either rank at most two at a real slope $a$, or an unsafe nonzero $X\in\ker T_a$ at a rank-three slope. In the first case the source/slope derivative $(V,t)\mapsto T_aV+tCS$ has rank at most three, at any source, so its determinant is zero.

In the second case write $X=(\begin{smallmatrix}a_0&b_0\\c_0&e_0\end{smallmatrix})$. On a positive shape,

$$
\mathfrak b(E(x,y),X)=a_0y+e_0x-b_0-c_0xy.
$$

Because $X$ is unsafe, $a_0,e_0,-b_0,-c_0$ contain both strict signs. The limits at $(\varepsilon,\varepsilon)$, $(T,T)/T^2$, $(T,T^{-2})/T$, and $(T^{-2},T)/T$ isolate respectively $-b_0,-c_0,e_0,a_0$. Thus the expression has both signs on positive shapes. A straight positive path between two such shapes has a zero. At that shape the nonzero $X$ is tangent to the rank-one source cone and $T_aX=0$, so the source/slope derivative has a nonzero kernel vector $(X,0)$. Equation (7.1) gives $j(a;x,y)=0$. This argument also explains directly how the same-slope exclusion meets the credited critical-point test; it does not use an invalid general claim about derivatives of injective smooth maps. ∎

For the surviving common-safe-kernel pencils, R2 and (7.2) still apply. For regular pencils, R1, all singular-slope tests, and (7.2) still apply. Passing these necessary conditions leaves possible distant different-slope collisions unresolved.

## 8. Provenance, unchanged bounds, and the remaining all-history target

The common positive source, trace convention, effective target, and representation fibres are credited through the supplied affine companions. The original self-calibrating model is background provenance carried by those companions; no additional original-source input is required by the new proofs here.

[Shared affine gain and zero-crossing recovery](FIB_SHARED_AFFINE_GAIN_ZERO_CROSSING_RECOVERY.md), Theorems 2.1 and 5.1, supplies $\max(d+6,7)$ reads as an upper bound and $d+5$ as the all-fixed-history lower bound. Its Theorem 4.1 concerns only its specified baseline/shear prefix. [Common polynomial-gain shear calibration and erasure recovery](FIB_POLYNOMIAL_GAIN_SHEAR_CALIBRATION_AND_ERASURE_RECOVERY.md), Theorem 4.1 and Lemma 3.2, supplies the broader polynomial-gain construction; its Theorems 6.1 and 8.1 supply its scale fibre and specified-prefix continuation optimum. For the affine restriction the complete target correspondence is

$$
R_0=S/\operatorname{tr}S,\qquad
H(t)=(\operatorname{tr}S)(1+kt),\qquad
S=H(0)R_0,\quad k=H'(0)/H(0),\quad H(0)>0.
$$

[Six-read constant-drift recovery and different-slope collisions](FIB_AFFINE_SIX_READ_RECOVERY_AND_UNKNOWN_SLOPE_COLLISIONS.md), Theorem 2.1 and Proposition 2.2, supplies the six-read constant-drift upper bound and its exact compatibility criterion. Its affine-drift example already shows that all prescribed-slope slices can be injective while different slopes collide on that particular path. None of these constructions or bounds is claimed anew.

The safe-cone/secant and prescribed-slope criteria used throughout are the credited results specified in Section 2. Their polynomial-erasure and one-erasure span tests retain their original scope. The quotient, transfer obstruction, R1–R3, and quadratic tests are credited to the critical-point companion specified in Sections 2 and 7, including its appended Sections 6–10. The present theorems add the simultaneous clock restriction on polynomial kernels and its common-safe-kernel consequence. The proofs range over all legal histories in Definition 1.1 rather than a new proper family of excluded words.

Let $C_{\rm fix}(d)$ denote the smallest uniform exact-read bound over all predetermined legal finite-word cumulative histories for the entire actual target. The credited numerical intervals remain exactly

$$
5\le C_{\rm fix}(0)\le6,\qquad
 d+5\le C_{\rm fix}(d)\le d+6\quad(d\ge1).
\tag{8.1}
$$

The remaining problem is to decide each lower-versus-upper endpoint and supply a matching actually legal fixed history with a common-source inverse valid for every real affine slope, all gain-zero cases, and the entire degree-at-most-$d$ drift; alternatively, a universal endpoint obstruction must cover every legal endpoint history. Regular pencils and identically singular pencils with the common safe kernel and lower-degree signal above still require such a uniform inverse or universal obstruction. No endpoint construction, global inverse from derivative nonsingularity, or universal endpoint collision theorem is established here. At $d=0$ the regular five-read branch remains; at $d=1$ the trace-normalized hyperplane is only necessary.

All statements are ordinary conditional mathematics under the exact model. Source preparation is not independent review, kernel verification, or completion of the programme. No adaptive impossibility, optimal atom count, precision bound, noisy stability, physical-resource conclusion, general neural-network result, empirical assertion, or external-priority claim is made. Reading index, atomic-operation count, elapsed time, bit precision, and acquisition cost remain distinct resources.

## 追加锚（本行以下为增补区）

## 追加结果：记录 $M$ 或 $JMJ$ 的完整 $d=1$ stratum

本节固定 $d=1$，故实际记录索引恰为 $0,1,2,3,4,5$。沿用前文的
$\mathcal R_+$、$\mathcal L$、$\mathcal I$、$\Lambda$、$B$、$C$ 和
$T_k=B+kC$。假设历史位于仍可能统一恢复的 identically singular 分支：

$$
\operatorname{rank}T_k=3,\qquad
\ker T_k=\mathbb R K\quad(k\in\mathbb R),
$$

其中 $K\ne0$ 为一个共同的 safe kernel 生成元，并作归一化

$$
\operatorname{tr}K=\operatorname{tr}(A_iK)=1\qquad(0\le i\le5).
\tag{10.1}
$$

本节记

$$
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$

本节只分类实际记录的累计矩阵。它不把 regular pencil 排除在含有同一矩阵的其它历史之外。

### 定理 10.1（记录 $M$ 的完整合法分类）

若某个记录位置的累计矩阵为

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},
$$

则必有

$$
K=E_{22}=\begin{pmatrix}0&0\\0&1\end{pmatrix},
$$

并且全部六个记录矩阵按实际时间恰为

$$
I,\quad\text{一个 }\{U,U,M\}\text{ 的排列},\quad
H_a,\quad H_b,\qquad H_h=U^hM,\quad1\le a<b.
\tag{10.2}
$$

也就是说，$H_a,H_b$ 在记录索引 $4,5$，而 $\{U,U,M\}$ 在索引
$1,2,3$；由于两个 $U$ 相同，前缀有三个实际排列。反之，每个
$1\le a<b$ 及每个前缀排列都由一个合法的单向 $M/J$ 历史实现，并满足
(10.1)、$\operatorname{rank}T_k=3$ 以及

$$
\ker T_k=\mathbb R E_{22}\qquad(k\in\mathbb R).
\tag{10.3}
$$

这些历史的每个固定斜率切片 $(S,D)\mapsto(z_0,\ldots,z_5)$ 都是全局单射；
但每一条都存在两个斜率不同、来源严格为正的实际碰撞。因此，满足本节假设且
记录 $M$ 的历史不能统一恢复未知斜率目标。

#### 证明

把共同 safe 生成元写成

$$
K=\begin{pmatrix}a&-b\\-c&e\end{pmatrix},
\qquad a,b,c,e\ge0,\qquad a+e=1.
$$

在记录的 $M$ 位置，

$$
1=\operatorname{tr}(MK)=e-b-c.
$$

与 $a+e=1$ 相减得 $a+b+c=0$，故 $a=b=c=0$，$e=1$。于是每个
记录矩阵 $A$ 都满足 $\operatorname{tr}(AE_{22})=A_{22}=1$。每个合法累计
矩阵仍是非负整数矩阵且行列式为 $1$ 或 $-1$，因为两个原子 $M,J$
具有这些性质。

先看记录 $M$ 的前后邻接。若 $A$ 是同一历史中 $M$ 的记录前驱，则存在
非负整数 unimodular 矩阵 $V$ 使 $M=VA$。写

$$
A=\begin{pmatrix}u&v\\w&1\end{pmatrix}.
$$

零的左上角迫使 $u=0$ 或 $w=0$。若 $w=0$，unimodularity 给出 $u=1$，而

$$
V=MU^{-v}=\begin{pmatrix}0&1\\1&1-v\end{pmatrix}
$$

的非负性只允许 $v=0,1$，所以 $A=I$ 或 $U$。若 $u=0$，则
$-vw=\det A=\pm1$，故 $v=w=1$，即 $A=M$。同理，若 $A=WM$ 是
$M$ 的记录后继，写 $W=\left(\begin{smallmatrix}x&y\\z&t\end{smallmatrix}\right)$。
由 $A_{22}=z+t=1$，只有两种情形：$(z,t)=(0,1)$ 时 $W=U^y$ 且
$A=H_y$；$(z,t)=(1,0)$ 时 $W=U^xJ$ 且 $A=U^{x+1}$。这些 $V,W$
是已有历史中实际执行的累计左乘积，不是逆操作。

令 $M$ 是首次记录的 $M$。对它之前的每个记录位置，整段实际左乘积 $V$
都满足 $M=VA$，所以上述前驱结论说明此前只能记录 $I$ 或 $U$。在 $M$
之后，若当前记录矩阵为 $U^b$ 且 $b\ge2$，任何后继 $B=VU^b$ 的条件
$B_{22}=1$ 给出 $V_{21}b+V_{22}=1$，故 $V=U^c$，以后只能记录上三角剪切。
若当前为 $H_h$ 且 $h\ge1$，同一计算因 $(H_h)_{12}=h+1\ge2$ 给出后继只能是
$U^cH_h=H_{h+c}$。若当前为 $U$，由后继的第二行和为一，后继只能是某个
$U^b$ 或某个 $H_h$。因此整个实际历史中的记录矩阵只能来自 $I,U^b,H_h$，
其中 $H_0=M$。

若出现 $U^b$ 且 $b\ge2$，正的 $H_h$ 不可能在它之前（否则其后继只能仍为
$H$），也不可能在它之后（上面的上三角结论）。于是所有记录矩阵落在

$$
\operatorname{span}\{I,E_{12},M\}.
$$

又因 $\operatorname{tr}(AE_{22})=1$ 对全部记录成立，$\mathcal L(E_{22})$ 是
常数向量，而 $\Lambda$ 消去常数向量，故
$\operatorname{rank}B\le3-1=2$，与 $\operatorname{rank}T_0=3$ 矛盾。
因而不存在 $b\ge2$，记录矩阵只可能是 $I,U,H_h$。

还需把记录次数固定下来。若完全没有 $U$ 记录，全部记录矩阵落在
$\operatorname{span}\{I,M,E_{11}+E_{12}\}$，因为 $H_h=M+h(E_{11}+E_{12})$。
这使 $\operatorname{rank}\mathcal L\le3$；又因非零的常数向量
$\mathcal L(E_{22})$ 被 $\Lambda$ 消去，故 $\operatorname{rank}B\le2$，直接矛盾。
若恰有一个 $U$ 记录，删去这一非初始位置后，剩余矩阵才全部落在同一个至多三维空间，
与下述删点引理矛盾。这两种情形分别使用全表秩和删点秩，不能合并为同一全表张成断言。
若没有 $H$，全表只有 $I,U$；若恰有一个 $H$，全表张成至多三维，仍由常数像给出
$\operatorname{rank}B\le2$。若恰有两个 $H$，删去其中任意一个后，剩余张成落在
$\operatorname{span}\{I,U,\text{剩下的 }H\}$，与删点引理矛盾。因此至少有两个 $U$
和三个 $H$。连同 $A_0=I$，六次记录恰好用完，故恰有一个 $I$、两个 $U$、三个 $H$。
三个 $H$ 参数也必须互异：若三者全同，全表张成至多三维；若只有两个不同参数，删去
只出现一次的那个参数所在记录，剩下两个 $H$ 相同，剩余只有 $I,U,H$ 三种矩阵。
这两种重复情形分别违反全表秩或删点引理。由于 $H_0=M$，
另两个参数为正整数 $a,b$。正的 $H$ 一旦出现，后继参数只能增加；互异性给出
$a<b$。所以 $M$ 与两个 $U$ 必在前三个非初始位置，且整个列表正是 (10.2)。

现在证明所用删点引理。若删去某个非初始位置 $j$ 后剩余矩阵张成至多三维，非退化
trace pairing 给出非零矩阵 $X$ 消灭所有剩余累计矩阵。因 $I$ 保留，
$\operatorname{tr}X=0$，所以 $X$ 不是 $\mathbb R E_{22}$。在斜率
$k=-1/j$ 下，向量

$$
(1-i/j)\operatorname{tr}(A_iX)
$$

在所有剩余位置因 $X$ 的消灭性质为零，在 $j$ 位置因增益为零也为零，故
$T_{-1/j}X=0$，违反 (10.3)。因此任何非初始删点后都必须保留四维矩阵张成。
以上计数、重复和边界情形均在实际记录索引上完成。

反向合法性也逐项成立。三种前缀分别由

$$
I\xrightarrow{(M,J)}U,\quad I\xrightarrow{M}M,\quad
U\xrightarrow{J}M,\quad M\xrightarrow{J}U,\quad U\xrightarrow{\varnothing}U
$$

实现。若前缀末项为 $M$，用实际左乘积 $U^a$ 到达 $H_a$；若末项为 $U$，
用实际左乘积 $U^aJ$ 到达 $U^aJU=U^aM=H_a$，再用 $U^{b-a}$ 到达
$H_b$。这些乘积都由有限的实际 $M,J$ 原子组成，词内不插入记录，所以索引
仍为 $0,\ldots,5$。所有中间未读状态也由正列保持正性。

为验证反向的秩和固定斜率结论，设两个 $U$ 的实际索引为 $j<\ell$，三个
$H$ 的实际索引按时间为 $i_1<i_2<i_3$，对应互异参数
$h_1,h_2,h_3\in\{0,a,b\}$。对任意

$$
S=\begin{pmatrix}p&q\\r&s\end{pmatrix}\in\mathcal R_+,
$$

定义

$$
A=p+s,\qquad t=p+r,\qquad v=q-p,\qquad
\zeta=A+\delta_0,\qquad \eta=\delta_1+k(A+r).
$$

其正性域精确为

$$
r>0,\qquad t>r,\qquad v>r-t,\qquad
s=\frac{r(p+v)}p,\quad p=t-r.
\tag{10.4}
$$

整条 affine drift 被写成

$$
D(x)=\zeta-A+[\eta-k(A+r)]x.
$$

直接按实际记录位置展开，得到

$$
\begin{aligned}
z_0&=\zeta,\\
z_j&=\zeta+r+\eta j,\qquad z_\ell=\zeta+r+\eta\ell,\\
z_{i_h}&=\zeta+\eta i_h+r+(1+ki_h)(h_ht+v),\qquad h=1,2,3.
\end{aligned}
\tag{10.5}
$$

其中使用了 $\operatorname{tr}(US)=A+r$ 与
$\operatorname{tr}(H_hS)-A=r+h(p+r)+(q-p)=r+ht+v$。因此数据坐标

$$
\zeta=z_0,\qquad
\eta=\frac{z_\ell-z_j}{\ell-j},\qquad
r=z_j-\zeta-j\eta,\qquad
Y_h=z_{i_h}-\zeta-\eta i_h-r
\tag{10.6}
$$

是六个实际读取的可逆线性重排；反向由 (10.5) 重建全部原始读数。

固定任意真实 $k$，把 $\mathbf a=(h_1,h_2,h_3)^{\mathsf T}$、
$\mathbf e=(1,1,1)^{\mathsf T}$、$\mathbf i=(i_1,i_2,i_3)^{\mathsf T}$、
$\mathbf w=(i_1h_1,i_2h_2,i_3h_3)^{\mathsf T}$，并设

$$
P_k=[\mathbf a+k\mathbf w,\ \mathbf e+k\mathbf i].
\tag{10.7}
$$

则 $Y=P_k(t,v)^{\mathsf T}$。每个 $1+ki_h$ 至多有一个零，任取两个非零的
$g_h=1+ki_h$，它们对应的 $h_h$ 不同，故相应二行行列式
$g_ug_v(h_u-h_v)\ne0$。所以 $P_k$ 对每个实 $k$ 都有秩二，即使第三个
$H$ 读数被增益擦除。于是固定斜率下 $t,v$ 唯一，(10.4) 恢复 $p,q,r,s$，
再由 $\zeta,\eta$ 恢复整条 $D$。这证明每个固定斜率切片全局单射，并且没有把
擦除的读数当成除数。

同一计算也给出整个满矩阵 quotient 的精确核。对任意实矩阵 $X$ 以及 affine drift，
令 $r=X_{21}$、$t=X_{11}+r$、$v=X_{12}-X_{11}$，并以
$\zeta=\operatorname{tr}X+\delta_0$、$\eta=\delta_1+k(\operatorname{tr}X+r)$
定义相同坐标。若六个读数全为零，两个 $U$ 读数先给 $r=\zeta=\eta=0$，三行
$P_k$ 的秩二再给 $t=v=0$。于是 $X=sE_{22}$，且唯一补偿漂移为

$$
\delta_0=-s,\qquad \delta_1=-ks.
$$

反向代入立即消去每个读数。因此

$$
\ker T_k=\mathbb R E_{22},\qquad \operatorname{rank}T_k=3
\tag{10.8}
$$

对所有实 $k$ 成立。这也验证了 (10.1) 的共同核与所有三种前缀排列，而非只验证
一个抽象矩阵表。

最后给出每条分类历史的实际不同斜率碰撞。对 (10.7) 定义精确双线性尾映射

$$
F(t,v,k)=P_k\binom tv,\qquad
J(t,v,k)=\det_3[\mathbf a+k\mathbf w,\ \mathbf e+k\mathbf i,\ t\mathbf w+v\mathbf i].
$$

多重线性展开给出

$$
J(t,v,k)=J_0(t,v)+k(tL_t+vL_v),
$$

其中

$$
J_0(t,v)=\det_3[\mathbf a,\mathbf e,t\mathbf w+v\mathbf i],\quad
L_t=\det_3[\mathbf a,\mathbf i,\mathbf w],\quad
L_v=\det_3[\mathbf w,\mathbf e,\mathbf i].
\tag{10.9}
$$

这里 $\mathbf w=(i_1h_1,i_2h_2,i_3h_3)^{\mathsf T}$ 是实际索引与对应 $H$ 参数的逐项乘积，
$\mathbf i=(i_1,i_2,i_3)^{\mathsf T}$ 是实际尾索引向量；二者不是新的读数。$k^2$ 的系数恰为

$$
\det_3[\mathbf w,\mathbf i,t\mathbf w+v\mathbf i]=0,
$$

因为第三列是前两列的线性组合。不能有
$L_t=L_v=0$。事实上，若 $L_v=0$，则 $\mathbf w=A\mathbf e+B\mathbf i$。
若 $A=0$，三个互异 $h_h=w_h/i_h$ 全相等，矛盾。若 $A\ne0$ 且
$\mathbf a=C\mathbf e+D\mathbf i$，则三个互异 $i_h$ 都是非零二次式
$D x^2+(C-B)x-A$ 的根，矛盾。故 $\mathbf a,\mathbf i,\mathbf e$ 独立，进而
$L_t=A\det_3[\mathbf a,\mathbf i,\mathbf e]\ne0$。

取明确允许的正源形状

$$
(r_*,t_*,v_*)=(1,2,0)\quad\text{若 }L_t\ne0,\qquad
(r_*,t_*,v_*)=(1,2,1)\quad\text{若 }L_t=0.
$$

两种情形都满足 $p_*=t_*-r_*=1>0$、$q_*=p_*+v_*>0$、
$s_*=q_*/p_*>0$。令

$$
L_*=t_*L_t+v_*L_v=2L_t+v_*L_v\ne0,\qquad
k_*=-\frac{J_0(t_*,v_*)}{L_*}.
\tag{10.10}
$$

于是 $J(t_*,v_*,k_*)=0$。由 $P_{k_*}$ 秩二，$\mathbf b=t_*\mathbf w+v_*\mathbf i$
在 $P_{k_*}$ 的列空间中，存在 $X=(X_t,X_v)^{\mathsf T}$ 使
$P_{k_*}X=\mathbf b$。为明确记录所有除数，选两个非零增益的实际尾索引
$u=i_\mu<w=i_\nu$，其中 $1\le\mu<\nu\le3$，并在 (10.11) 中明确约定
$h_u:=h_\mu$、$h_w:=h_\nu$：它们分别是实际累计矩阵 $A_u=H_{h_\mu}$、
$A_w=H_{h_\nu}$ 的参数，而非用实际索引直接索引长度为三的参数表。令

$$
R_u=\frac{u(h_ut_*+v_*)}{1+k_*u},\qquad
R_w=\frac{w(h_wt_*+v_*)}{1+k_*w},\qquad
X_t=\frac{R_u-R_w}{h_u-h_w},\qquad X_v=R_u-h_uX_t.
\tag{10.11}
$$

这里只除以特意选取的非零增益和 $h_u-h_w\ne0$；第三行由 $J=0$ 自动满足，
即使第三增益为零。

取任意非零实数 $\varepsilon$ 满足

$$
|\varepsilon|<\min\left\{
\frac1{2(1+|X_t|)},
\frac{1+v_*}{2(1+|X_t+X_v|)}
\right\}.
\tag{10.12}
$$

定义两次实际运行

$$
(k_0,t_0,v_0)=(k_*,t_*+\varepsilon X_t,v_*+\varepsilon X_v),
$$

$$
(k_1,t_1,v_1)=(k_*+\varepsilon,t_*,v_*),\qquad
r_0=r_1=1,\quad
\zeta_0=\zeta_1=\eta_0=\eta_1=0.
$$

由 $P_k$ 对 $k$ 的仿射性和 (10.11)，有逐项的精确有限恒等式

$$
P_{k_0}\binom{t_0}{v_0}
=P_{k_*}\binom{t_*}{v_*}+\varepsilon\mathbf b
=P_{k_*+\varepsilon}\binom{t_*}{v_*}
=P_{k_1}\binom{t_1}{v_1}.
\tag{10.13}
$$

把 $p_b=t_b-1$、$q_b=p_b+v_b$、$s_b=q_b/p_b$，并令

$$
S_b=\begin{pmatrix}p_b&q_b\\1&s_b\end{pmatrix},\qquad
A_b=p_b+s_b,\qquad D_b(x)=-A_b-k_b(A_b+1)x.
\tag{10.14}
$$

(10.12) 给出 $p_0>1/2$、$q_0>(1+v_*)/2$，而
$p_1=1$、$q_1=1+v_*>0$。所以两个 $S_b$ 都严格正、秩一，且每条运行使用
一整条 affine 漂移 $D_b$。在每次运行中取

$$
\alpha_b=1,\quad \beta_b=k_b,\quad R_b=S_b,\quad
c_b=\binom{p_b}{1},\quad \ell_b=(1,q_b/p_b).
\tag{10.15}
$$

于是 $c_b\ell_b=S_b$，每个 $M,J$ 原子都把正列送到正列，固定行 $\ell_b$
在全部读与未读状态保持不变。代入实际记录方程，$I$ 位置给 $z_0=0$，两个
$U$ 位置给 $z_i=1$，三个 $H$ 位置给

$$
z_{i_h}=1+(1+k_bi_h)(h_ht_b+v_b).
$$

由 (10.13) 三个尾读数逐项相等。两次运行的斜率相差非零的 $\varepsilon$，所以是不同的
有效目标；这不是 representation scale，也没有重置来源、改变行、组合未执行历史或
为各读数另选漂移。等式在增益为零或为负的样本处仍按未除增益的原始方程成立。

因此，记录 $M$ 的每一条合法分类历史都保留固定斜率的 rank-three common kernel，
却必有实际的不同斜率碰撞。

### 定理 10.2（记录 $N=JMJ$ 的镜像分类）

若某个记录位置的累计矩阵为

$$
N=JMJ,
$$

则全部结论由 $J$-共轭精确搬运：

$$
K=E_{11},\qquad
I,\quad\text{一个 }\{L,L,N\}\text{ 的排列},\quad
L^aN,\quad L^bN,\qquad
L=MJ=JUJ,\quad1\le a<b.
\tag{10.16}
$$

这些历史的每个固定斜率切片仍全局单射，并且每一条都有不同斜率的严格正来源碰撞。

#### 证明

令 $A'_i=JA_iJ$、$K'=JKJ$。若 $A_{i+1}=W_iA_i$，则
$A'_{i+1}=(JW_iJ)A'_i$，而 $JW_iJ$ 仍是有限 $M/J$ 词；初始矩阵仍为 $I$，且
$N$ 变为 $M$。迹的共轭不变性给出
$\operatorname{tr}(A_iS)=\operatorname{tr}(A'_iS')$（取 $S'=JSJ$），所以
读数、实际索引和整条漂移均保持。由定理 10.1，$K'=E_{22}$，故 $K=E_{11}$，
且 $H_h$ 共轭为 $L^hN$。

反向碰撞不引入物理共轭操作：对定理 10.1 中构造的每个原始端点，直接取
$S_b=JS'_bJ$、$c_b=Jc'_b$、$\ell_b=\ell'_bJ$，并沿原历史使用同一 $k_b,D_b$。
这些因子仍严格为正、在原始 $M/J$ 词的全部未读状态保持正，且
$\operatorname{tr}(A_iS_b)=\operatorname{tr}(A'_iS'_b)$。所以 (10.16) 的每个历史
也有同样的实际碰撞。

### 余下边界

定理 10.1–10.2 只处理 $d=1$ identically singular common-safe-kernel 分支中实际记录
$M$ 或 $JMJ$ 的历史。它们不处理记录事件集合中不含这两个矩阵的其它 kernel 方向，也不
处理 regular pencils；特别是，regular 五读 $d=0$ 分支仍在原问题内。对 $d\ge2$，
共同 safe kernel 的记录信号一般是次数至多 $d-1$ 的多项式，不能由本节的常值超平面分类
替代。全局 sharp endpoint、所有斜率的统一逆、以及覆盖其余合法历史的普适碰撞仍未结算。
原有界保持为

$$
5\le C_{\mathrm{fix}}(0)\le6,\qquad
d+5\le C_{\mathrm{fix}}(d)\le d+6\quad(d\ge1).
$$

本节增加的是完整的实际记录 $M/JMJ$ stratum 分类、每个 $a<b$ 的合法历史、固定斜率
全局逆和严格正来源的不同斜率碰撞；它不把该 stratum 的结论外推成全历史 endpoint 结论。


## 11. Diagonal generators and the complete legal-chain normal form

Continue at $d=1$ with the six actual nodes $0,\ldots,5$ and hypotheses (10.1): for every real $k$, the pencil has rank three and the same safe kernel line. These hypotheses are the necessary residual supplied by Theorem 5.1 and Corollary 6.3. The results of Sections 11–15 extend the preceding mathematical proposal *Diagonal safe-kernel word normal form and a two-or-three initial lower-shear restriction at the unrecorded affine endpoint*. That proposal supplies the diagonal classification and collision route; it is preceding mathematical work, with ordinary conditional proofs. Section 10 uses the preceding proposal *Exact affine-drift classification and different-slope collisions in the common-safe-kernel stratum recording M or JMJ*. Neither proposal is independent certification. The complete arguments and source realizations used here are given below.

We first record two consequences of the residual hypotheses. The whole matrix list spans four dimensions. Indeed $\mathcal L(K)=\mathbf1\ne0$ is killed by $\Lambda$, so

$$
3=\operatorname{rank}B\le\operatorname{rank}\mathcal L-1\le3.
\tag{11.1}
$$

Also deletion of any noninitial read must leave four-dimensional matrix span. If the survivors spanned at most three dimensions, choose $X\ne0$ annihilating them under the nondegenerate trace pairing. Since $I$ survives, $\operatorname{tr}X=0$, so $X\notin\mathbb RK$ because $\operatorname{tr}K=1$. At $k=-1/j$ the vector $(1-i/j)\operatorname{tr}(A_iX)$ vanishes at every survivor and at the erased position $j$. Thus $X\in\ker T_{-1/j}$, a contradiction. This argument includes repeated endpoints and uses the actual noninitial index $j$, which is a nonzero integer.

### Theorem 11.1 (mixed positive diagonal generators are excluded)

If the normalized common safe generator $K$ is diagonal, then it is $E_{22}$ or $E_{11}$.

**Proof.** Suppose instead that $K=\operatorname{diag}(a,e)$ with $a,e>0$ and $a+e=1$. Every recorded endpoint is nonnegative integral and unimodular. For

$$
A=\begin{pmatrix}u&v\\w&t\end{pmatrix},
\qquad au+et=1,
$$

if $u,t\ge1$, positivity of $a,e$ forces $u=t=1$. Then $1-vw=\pm1$ gives $vw=0$ or $2$. Thus these endpoints are $I$, upper or lower shears, or the two positive matrices

$$
P_0=\begin{pmatrix}1&1\\2&1\end{pmatrix},\qquad
Q_0=\begin{pmatrix}1&2\\1&1\end{pmatrix}.
$$

If $u=0$, unimodularity forces $v=w=1$ and $t=1/e$ to be an integer $m\ge2$, giving

$$
Z_m=\begin{pmatrix}0&1\\1&m\end{pmatrix}.
$$

If $t=0$, the analogous endpoint is $JZ_\ell J$ for the integer $\ell=1/a\ge2$. Both diagonal entries cannot be zero because $au+et=1$. This exhausts all endpoints; if a displayed reciprocal is not an integer, its case simply does not occur.

The following order restrictions concern existing left multipliers, not inverse acquisitions. A nontrivial upper shear $U^h$ and lower shear $L^g$, with $h,g\ge1$ and $L=MJ$, cannot coexist in one chain: $L^g(U^h)^{-1}$ has upper-right entry $-h$, and $U^h(L^g)^{-1}$ has lower-left entry $-g$. Every actual multiplier is nonnegative. A positive endpoint remains positive under every later nonnegative invertible multiplier, because each multiplier row is nonzero. Moreover

$$
Q_0P_0^{-1}=\begin{pmatrix}3&-1\\1&0\end{pmatrix},\qquad
P_0Q_0^{-1}=\begin{pmatrix}0&1\\-1&3\end{pmatrix},
$$

so $P_0$ and $Q_0$ cannot both occur. Neither can coexist with $Z_m$: it cannot precede the zero of $Z_m$, whereas

$$
P_0Z_m^{-1}=\begin{pmatrix}1-m&1\\1-2m&2\end{pmatrix},\qquad
Q_0Z_m^{-1}=\begin{pmatrix}2-m&1\\1-m&1\end{pmatrix}
$$

have negative entries for every $m\ge2$. Conjugation by $J$ gives the same exclusion for $JZ_\ell J$ and exchanges $P_0,Q_0$. Consequently a chain containing a positive endpoint lies in the span of $I$, one shear direction, and that one positive endpoint, of dimension at most three. Repetition adds no dimension.

If $Z_m$ occurs, no nontrivial lower shear can precede it, since $Z_m(L^g)^{-1}$ has upper-left entry $-g$. None can follow it: its second column is positive and stays positive, whereas a lower shear has zero upper-right entry. The mirrored zero-diagonal endpoint cannot coexist with $Z_m$ either. Its positive first column prevents it from preceding the zero in the first column of $Z_m$; the positive second column of $Z_m$ prevents the opposite order. Positive endpoints were already excluded. Thus every endpoint in a chain containing $Z_m$ lies in $\{I,U^h,Z_m\}$, a space of dimension at most three. Its mirror has the same property. If there is no positive or zero-diagonal endpoint, only one shear direction can occur, giving span at most two.

In all cases $\operatorname{rank}\mathcal L\le3$. The nonzero constant image $\mathcal L(K)=\mathbf1$ is killed by $\Lambda$, so $\operatorname{rank}B\le2$, contrary to (11.1). A diagonal safe matrix has nonnegative diagonal entries summing to one. Removing the case in which both are positive leaves exactly $E_{22}$ and $E_{11}$. ∎

The exclusion also has a complete actual-source collision interpretation. For any legal history in the mixed diagonal hyperplane, the span calculation gives $\dim\ker B\ge2$. Choose two independent kernel vectors $X_0,X_1$. If either is outside the safe-cone union, retain it as $X$. Otherwise orient both safe and take their nonzero combination $\Phi(X_1)X_0-\Phi(X_0)X_1$; it has $\Phi=0$ and is therefore unsafe. This supplies an unsafe $X\ne0$ in $\ker B$.

For completeness the full positive-secant construction is as follows. Write $X=(\begin{smallmatrix}a_0&b_0\\c_0&e_0\end{smallmatrix})$ and $\delta=\det X$. The coefficients $a_0,-b_0,-c_0,e_0$ contain both strict signs, so

$$
F(x,y)=e_0xy+a_0-c_0x-b_0y
$$

takes both signs on the positive quadrant. The limits at $(\epsilon,\epsilon)$, $(T,T)/T^2$, $(T,T^{-2})/T$, and $(T^{-2},T)/T$ isolate respectively $a_0,e_0,-c_0,-b_0$. Choose opposite-sign positive points and their straight segment. Every entry of $E_0(x,y)=(\begin{smallmatrix}xy&x\\y&1\end{smallmatrix})$ on that compact segment has a positive lower bound $m_0$. With endpoint values $F_-<0<F_+$, choose

$$
\tau>\max\left\{\frac{\max|X_{ab}|}{m_0},
\frac{|\delta|}{\min(-F_-,F_+)}\right\}.
$$

Both divisors are positive. Continuity supplies a segment point with $F=-\delta/\tau$, including when $\delta=0$. Then

$$
S_0=\tau E_0(x,y),\qquad S_1=S_0+X
$$

are distinct strictly positive matrices of rank one: the second determinant is $\tau F+\delta=0$, and its entries are positive by the strict bound on $\tau$. Since $BX=0$ and the second-difference quotient has exactly affine evaluation as its kernel, the one entire affine polynomial

$$
H(t)=\operatorname{tr}X+t\bigl(\operatorname{tr}(A_1X)-\operatorname{tr}X\bigr)
$$

satisfies $H(i)=\operatorname{tr}(A_iX)$ at all six nodes. Give both runs slope zero, with $D_0=0$ and $D_1=-H$. Their observation difference at every actual index is $\operatorname{tr}(A_iX)-H(i)=0$. For each endpoint set $\alpha_b=1$, $\beta_b=0$, $R_b=S_b$, $c_b=(p_b,r_b)^{\mathsf T}$ and $\ell_b=(1,q_b/p_b)$. Positivity and $p_bs_b=q_br_b$ give $c_b\ell_b=S_b$ and $\ell_bA_ic_b=\operatorname{tr}(A_iS_b)$. Each actual atom preserves positive columns with this fixed positive row. This supplies positive read and unread states on the original prescribed words, one whole affine drift per run, and a target distinction beyond the scale fibre. Thus the rank exclusion is supported by an actual collision, rather than by dimension alone.

### Theorem 11.2 (all chains in the $E_{22}$ hyperplane)

Put

$$
D_h=L^h=\begin{pmatrix}1&0\\h&1\end{pmatrix}\quad(h\ge0).
$$

A legal recorded chain starting at $I$ and satisfying $(A_i)_{22}=1$ has the following exact description. If every upper-right entry is zero, it is a nondecreasing list of $D_h$ starting at $D_0=I$. Otherwise choose an integer $w$ and sign $\sigma\in\{1,-1\}$ with

$$
w\ge0\quad(\sigma=1),\qquad w\ge1\quad(\sigma=-1),\qquad
m=\min(w,w+\sigma),
$$

and define

$$
P=\begin{pmatrix}w+\sigma&1\\w&1\end{pmatrix},\qquad
Q=JP=\begin{pmatrix}w&1\\w+\sigma&1\end{pmatrix},
$$

$$
T_\nu=\begin{pmatrix}\nu w+\sigma&\nu\\w&1\end{pmatrix}
=U^{\nu-1}P\quad(\nu\ge1).
\tag{11.2}
$$

There is an initial phase of $a\ge1$ readings

$$
D_{h_0},\ldots,D_{h_{a-1}},\qquad
h_0=0,\quad0\le h_0\le\cdots\le h_{a-1}\le m,
$$

then a possibly empty phase consisting of $P,Q$ in any order with repetitions, then a possibly empty final phase of $T_\nu$ with $\nu\ge2$ nondecreasing, with repetitions. At least one of the last two phases is nonempty. Conversely every such list is a legal chain in this hyperplane. Without a final phase the orientation of the pair need not be unique; no uniqueness of that choice is required.

**Proof.** Write an endpoint as $A=(\begin{smallmatrix}u&v\\w&1\end{smallmatrix})$ with $u-vw=\pm1$. If $v=0$, then $u=1$, so $A=D_w$. The multiplier from $D_h$ to $D_g$ is $L^{g-h}$; nonnegativity forces $g\ge h$. Once $v>0$, a later endpoint cannot have upper-right entry zero, because that entry is $V_{11}v+V_{12}$ and the first row of the nonnegative invertible multiplier $V$ is nonzero.

Suppose $v=1$ and a later endpoint still has upper-right entry one. The bottom-right equation is $V_{21}+V_{22}=1$. If the bottom row is $(0,1)$, unimodularity gives $V_{11}=1$, and the upper-right equation gives $V_{12}=0$, hence $V=I$. If it is $(1,0)$, unimodularity gives $V_{12}=1$ and the upper-right equation gives $V_{11}=0$, hence $V=J$. Therefore the entire $v=1$ phase consists of just one pair of row swaps $P,Q$, with arbitrary swaps and repetitions.

If $v\ge2$, the later bottom-right equation $V_{21}v+V_{22}=1$ forces $V_{21}=0$, $V_{22}=1$. Unimodularity gives $V_{11}=1$, so $V=U^c$ for an integer $c\ge0$. Thereafter the bottom row $(w,1)$ and determinant sign $\sigma$ stay fixed. The endpoints are precisely $T_\nu$, with nondecreasing $\nu\ge2$. Nonnegativity gives the stated restrictions on $w,\sigma$. The earlier $v=1$ pair, if present, must be $P=T_1,Q=JP$. To see this explicitly, write its last endpoint as $A=(\begin{smallmatrix}x&1\\y&1\end{smallmatrix})$. In the first transition to a final endpoint with upper-right entry $\nu\ge2$, the multiplier bottom row is $(0,1)$ or $(1,0)$ because its entries sum to one. In the first case unimodularity gives the top row $(1,\nu-1)$, so the old endpoint is $P$ for the new bottom row and determinant sign, and the new endpoint is $U^{\nu-1}P$. In the second case the top row is $(\nu-1,1)$, the old endpoint is $Q$, and the new endpoint is $U^{\nu-1}JQ=U^{\nu-1}P$. All earlier $v=1$ endpoints differ from it by $I$ or $J$. If there is no final phase, take either member of the $v=1$ pair as $P$; nonnegative entries again give the stated restrictions.

From an initial $D_h$ to a first endpoint $T_\nu$, the existing multiplier is

$$
T_\nu D_h^{-1}
=\begin{pmatrix}\nu(w-h)+\sigma&\nu\\w-h&1\end{pmatrix}.
$$

Its nonnegativity is exactly $h\le m$: for $\sigma=1$ this is $h\le w$; for $\sigma=-1$, $w-h=0$ would make the top-left entry negative, so $h\le w-1$. A first $Q$ gives the same condition by swapping the two $v=1$ rows. All earlier $h$ obey it by their monotonicity. This proves necessity, including a first positive upper-right entry greater than one.

Conversely $D_h\to D_g$ uses $L^{g-h}$. From $D_h$ to $P$ use the actual left multiplier $UL^{w-h}$ for $\sigma=1$, and $ML^{w-h-1}$ for $\sigma=-1$. These exponents are nonnegative by $h\le m$. Prepend $J$ to reach $Q$, or prepend $U^{\nu-1}$ to reach $T_\nu$. Within the pair phase use $I$ or $J$; from $P$ to $T_\nu$ use $U^{\nu-1}$, from $Q$ use $U^{\nu-1}J$, and within the final phase use $U^{\nu'-\nu}$. The all-$D$ case uses the first rule alone. Since $U=JM$ and $L=MJ$, every multiplier is a finite $M/J$ word, with empty words for repetitions and no extra reads inside a word. These words preserve positivity at every unread state. This proves sufficiency. ∎

This theorem is a legality and hyperplane equivalence. It does not assert rank three or recovery for every listed chain.

## 12. Six-read rank consequences and the one-initial-zero-entry class

### Proposition 12.1 (a final phase and at most three initial lower-shear readings)

Under (10.1) with $K=E_{22}$, the normal form of Theorem 11.2 has a nonempty final phase and $1\le a\le3$.

**Proof.** An all-$D$ list has span at most two. Without a final phase, any other list lies in $\operatorname{span}\{I,E_{21},P,Q\}$. Full span requires a nonzero $D_h$, a $P$, and a $Q$. Each of these three categories must occur at least twice among the noninitial reads: deleting its sole occurrence leaves span at most three, contrary to the deletion condition preceding Theorem 11.1. Together with $I$ this would require at least seven reads, whereas there are six. Thus a final phase is necessary. If $a\ge4$, at most two positive-upper-right endpoints remain. Delete one of these noninitial endpoints. The surviving $D$ matrices span at most two dimensions, and at most one other endpoint remains, so the surviving span is at most three. This again contradicts the deletion condition. ∎

### Theorem 12.2 (exact classification when $a=1$)

Suppose (10.1), $K=E_{22}$, and $a=1$, so $I$ is the only recorded endpoint with upper-right entry zero. Then among the other five endpoints there are exactly two $Q$ readings and three $T_\nu$ readings with distinct positive integer parameters, and

$$
d_*=w+\sigma-1\ne0.
\tag{12.1}
$$

At most one of the three $T$ readings is $T_1=P$; it lies in the pair phase, with the two $Q$ readings. Every other $T$ parameter is at least two, and those readings form the final strictly increasing phase. Conversely every such six-entry list, with this order, is legal and satisfies (10.1), $\ker T_k=\mathbb RE_{22}$ and $\operatorname{rank}T_k=3$ at every real slope. Every prescribed-slope slice has a global positive-source inverse. Each of these histories nevertheless has the different-slope collision constructed in Section 14.

**Proof of necessity.** Count $P$ as $T_1$. If no $Q$ occurs, all endpoints lie in $\operatorname{span}\{I,P,R\}$, where

$$
R=\begin{pmatrix}w&1\\0&0\end{pmatrix},\qquad
T_\nu=P+(\nu-1)R.
$$

That span is at most three. If exactly one $Q$ occurs, deleting it gives the same failure. Thus there are at least two $Q$ reads. There must be at least three $T$ reads: with none, the full span is at most two; with one, it is at most three; with two, deleting one leaves only $I,Q$ and one $T$. The six total reads force exactly two $Q$ reads and three $T$ reads. If the three parameters have only one distinct value, full span fails. If they have exactly two distinct values, delete the parameter occurring only once, leaving just $I,Q$ and one $T$ value. Thus the three parameters are distinct.

To check the remaining parameter degeneracy, use the trace coefficients on $(p,q,r)$. The matrices $P-I,Q-I,R$, all with lower-right entry zero, have respective coefficient vectors

$$
\mathbf p=(w+\sigma-1,w,1)^{\mathsf T},\quad
\mathbf q=(w-1,w+\sigma,1)^{\mathsf T},\quad
\mathbf r=(w,0,1)^{\mathsf T}.
$$

Subtracting the first column from the second and expanding gives

$$
\det_3[\mathbf p,\mathbf q,\mathbf r]
=\sigma(w+\sigma-1).
$$

If $d_*=0$, the span of $I,Q,P,R$ is at most three, contradicting full span. Hence (12.1) holds. It implies $w\ge1$: for $\sigma=1$, $w=0$ is excluded; for $\sigma=-1$, nonnegativity already required $w\ge1$ and (12.1) additionally excludes $w=2$. The order assertions follow from Theorem 11.2; distinctness allows at most one $T_1$. Converse legality follows from that theorem, and the exact rank and inverse are proved next. ∎

In this class $N=JMJ$ cannot be recorded, because $N_{22}=0$. A recorded $M$ is exactly $T_1$ in the case $w=1,\sigma=-1$. The alternative $Q=M$ would require $w=0,\sigma=1$, already excluded by $d_*=0$. Thus in the residual with neither $M$ nor $N$ recorded, the case $w=1,\sigma=-1$ requires all three $T$ parameters to be at least two. All other allowed $w,\sigma$ are retained. This statement concerns recorded cumulative matrices; unread $M$ atoms remain allowed.

## 13. Exact all-slope rank and a global inverse on every prescribed-slope slice

Take any list in Theorem 12.2. Let $j<\ell$ be the two actual $Q$ indices, and let $i_1<i_2<i_3$ be the three actual $T$ indices. Define their parameters by

$$
A_{i_b}=T_{\nu_b},\qquad h_b=\nu_b-1\quad(b=1,2,3).
$$

The $h_b$ are distinct; they are attached to the actual $i_b$, including a possible early $T_1$. For a source $S=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})\in\mathcal R_+$ put

$$
a_S=p+s,\qquad
u=(w-1)p+(w+\sigma)q+r,\qquad
t=wp+r,\qquad v=\sigma(p-q).
\tag{13.1}
$$

The symbol $u$ is a source coordinate, distinct from the integer tail parameter $\nu_b$. Since $w\ge1$, $w+\sigma\ge0$ and $r>0$, one has $u>0$. The linear map $(p,q,r)\mapsto(u,t,v)$ has inverse

$$
p=\frac{u-t+\sigma(w+\sigma)v}{d_*},\qquad
q=p-\sigma v,\qquad r=t-wp.
\tag{13.2}
$$

Indeed $u-t=-p+(w+\sigma)q$, so the numerator in the first equation equals $d_*p$. No sign of $d_*$ is assumed; only its nonvanishing is used.

For $D(x)=\delta_0+\delta_1x$, set

$$
\zeta=a_S+\delta_0,\qquad
\eta=\delta_1+k(a_S+u).
$$

The exact original equations at all six positions become

$$
\begin{aligned}
z_0&=\zeta,\\
z_j&=\zeta+u+\eta j,\qquad z_\ell=\zeta+u+\eta\ell,\\
z_{i_b}&=\zeta+u+\eta i_b+(1+ki_b)(h_bt+v)\quad(b=1,2,3).
\end{aligned}
\tag{13.3}
$$

These follow from $\operatorname{tr}(QS)=a_S+u$ and

$$
\operatorname{tr}((T_{\nu_b}-Q)S)
=(\nu_b-1)(wp+r)+\sigma(p-q)=h_bt+v.
$$

The whole drift, rather than separate sampled values, is

$$
D(x)=\zeta-a_S+[\eta-k(a_S+u)]x.
\tag{13.4}
$$

The output coordinates change invertibly to

$$
\zeta=z_0,\qquad
\eta=\frac{z_\ell-z_j}{\ell-j},\qquad
u=z_j-\zeta-j\eta,\qquad
Y_b=z_{i_b}-\zeta-u-\eta i_b.
\tag{13.5}
$$

Equations (13.3) reconstruct all original outputs, so this is a linear isomorphism of the six data coordinates.

Define

$$
\mathbf a=(h_1,h_2,h_3)^{\mathsf T},\quad
\mathbf e=(1,1,1)^{\mathsf T},\quad
\mathbf i=(i_1,i_2,i_3)^{\mathsf T},\quad
\boldsymbol\omega=(i_1h_1,i_2h_2,i_3h_3)^{\mathsf T},
$$

$$
P_k=[\mathbf a+k\boldsymbol\omega,\ \mathbf e+k\mathbf i].
\tag{13.6}
$$

Then $Y=P_k(t,v)^{\mathsf T}$. Its row $b$ is $(1+ki_b)(h_b,1)$. The gain with intercept one has at most one zero among three distinct actual nodes. Any two surviving rows $b,c$ have determinant

$$
(1+ki_b)(1+ki_c)(h_b-h_c)\ne0.
$$

Thus $P_k$ has rank two for every real $k$, including an erased third row and arbitrary negative gains. For a prescribed $k$, recover $\zeta,\eta,u$ from (13.5), choose any two nonerased rows and set

$$
V_b=\frac{Y_b}{1+ki_b},\qquad V_c=\frac{Y_c}{1+ki_c},\qquad
t=\frac{V_b-V_c}{h_b-h_c},\qquad v=V_b-h_bt.
$$

Equations (13.2) then give $p,q,r$, actual positivity gives $p>0$, and $s=qr/p$ recovers the source. Finally (13.4) recovers the entire original affine drift. The divisors are the positive integer $\ell-j$, selected nonzero gains, distinct $h_b-h_c$, $d_*\ne0$, and $p>0$. Each step returns the actual parameters, so equal data at a fixed slope give equal targets globally. At a zero gain the original equation is retained; no erased gain is divided out.

To establish the exact quotient rank, apply the same linear coordinates to an arbitrary real full matrix $X$ and an affine compensating drift. If all six observations vanish, (13.5) gives $\zeta=\eta=u=0$, and rank two of $P_k$ gives $t=v=0$. Equations (13.2) give $p=q=r=0$; $s$ is free and the drift is $-s(1+kx)$. Conversely this cancels every observation because every endpoint has lower-right entry one. Since $\ker\Lambda$ is exactly affine evaluation, these homogeneous full-matrix equations characterize $\ker T_k$. Hence

$$
\ker T_k=\mathbb RE_{22},\qquad\operatorname{rank}T_k=3\quad(k\in\mathbb R).
\tag{13.7}
$$

Also $\operatorname{tr}(A_iE_{22})=1$ at every node. This completes the converse in Theorem 12.2. The full-matrix calculation analyzes a linear kernel; positive sources in the inverse and collision are the single rank-one sources explicitly displayed.

## 14. Exact finite different-slope collisions for every $a=1$ list

For the actual vectors in (13.6), define

$$
\begin{aligned}
J(t,v,k)&=\det_3[\mathbf a+k\boldsymbol\omega,\ \mathbf e+k\mathbf i,
 t\boldsymbol\omega+v\mathbf i],\\
J_0(t,v)&=\det_3[\mathbf a,\mathbf e,t\boldsymbol\omega+v\mathbf i],\\
L_t&=\det_3[\mathbf a,\mathbf i,\boldsymbol\omega],\qquad
L_v=\det_3[\boldsymbol\omega,\mathbf e,\mathbf i].
\end{aligned}
$$

Multilinearity gives

$$
J(t,v,k)=J_0(t,v)+k(tL_t+vL_v),
\tag{14.1}
$$

because the quadratic coefficient is exactly

$$
\det_3[\boldsymbol\omega,\mathbf i,t\boldsymbol\omega+v\mathbf i]=0.
$$

The vector $\boldsymbol\omega$ consists of the actual index–parameter products, and $\mathbf i$ of actual tail indices. The last column is a linear combination of the first two.

The constants $L_t,L_v$ cannot both vanish. If $L_v=0$, independence of $\mathbf e,\mathbf i$ gives $\boldsymbol\omega=A\mathbf e+B\mathbf i$, so $h_b=B+A/i_b$. All $i_b$ are positive integers. Distinct $h_b$ force $A\ne0$. If $\mathbf a=C\mathbf e+E\mathbf i$, then

$$
A+(B-C)i_b-Ei_b^2=0\quad(b=1,2,3).
$$

The three distinct nodes would be roots of a nonzero polynomial of degree at most two, contradicting the root bound. Thus $\det_3[\mathbf a,\mathbf i,\mathbf e]\ne0$, and $L_t=A\det_3[\mathbf a,\mathbf i,\mathbf e]\ne0$.

The linear coefficient in actual source coordinates is

$$
tL_t+vL_v=(wL_t+\sigma L_v)p-\sigma L_vq+L_tr.
\tag{14.2}
$$

Its three coefficients cannot all vanish: the coefficient of $r$ would give $L_t=0$, and that of $q$ would give $L_v=0$. Choose a strictly positive triple explicitly by the following symbolic rule. Start at $p=q=r=1$. If (14.2) is nonzero there, keep this triple. Otherwise select any coordinate with a nonzero coefficient and replace its value by $2$, leaving the others $1$; (14.2) then equals that nonzero coefficient. Set $s=qr/p>0$ and define $u,t,v$ by (13.1). With

$$
F_*=tL_t+vL_v\ne0,\qquad k_*=-\frac{J_0(t,v)}{F_*},
$$

one has $J(t,v,k_*)=0$. This is an unexecuted symbolic source selection for each actual history.

Rank two of $P_{k_*}$ implies that $\mathbf b=t\boldsymbol\omega+v\mathbf i$ is in its range, since the displayed three-column determinant vanishes. Its preimage $(X_t,X_v)$ is unique. To exhibit every divisor, select rows $b,c$ with nonzero gains $g_b=1+k_*i_b$, $g_c=1+k_*i_c$, and put

$$
R_b=\frac{i_b(h_bt+v)}{g_b},\qquad
R_c=\frac{i_c(h_ct+v)}{g_c},\qquad
X_t=\frac{R_b-R_c}{h_b-h_c},\qquad X_v=R_b-h_bX_t.
\tag{14.3}
$$

Two such rows always exist and have different parameters. The zero determinant ensures the third equation $P_{k_*}(X_t,X_v)^{\mathsf T}=\mathbf b$ as well, even when that row has zero gain.

Hold $u$ fixed and define

$$
\Delta_p=\frac{-X_t+\sigma(w+\sigma)X_v}{d_*},\qquad
\Delta_q=\Delta_p-\sigma X_v,\qquad
\Delta_r=X_t-w\Delta_p.
$$

Choose any nonzero real $\epsilon$ with

$$
|\epsilon|<\min\left\{
\frac{p}{2(1+|\Delta_p|)},\quad
\frac{q}{2(1+|\Delta_q|)},\quad
\frac{r}{2(1+|\Delta_r|)}\right\}.
\tag{14.4}
$$

All three upper bounds are strictly positive. Run $1$ uses $(p_1,q_1,r_1)=(p,q,r)$ and $k_1=k_*+\epsilon$. Run $0$ uses

$$
(p_0,q_0,r_0)=(p,q,r)+\epsilon(\Delta_p,\Delta_q,\Delta_r),\qquad k_0=k_*.
$$

The inverse linear formulas (13.2) give the same $u$ in both runs, while $(t_0,v_0)=(t+\epsilon X_t,v+\epsilon X_v)$ and $(t_1,v_1)=(t,v)$. Each perturbed entry is greater than half its original positive value. Set, for $b=0,1$,

$$
s_b=\frac{q_br_b}{p_b},\qquad
S_b=\begin{pmatrix}p_b&q_b\\r_b&s_b\end{pmatrix},\qquad a_b=p_b+s_b,
$$

$$
D_b(x)=-a_b-k_b(a_b+u)x.
\tag{14.5}
$$

Both $S_b$ are strictly positive and of rank one. Each $D_b$ is one entire allowed affine polynomial, giving $\zeta=\eta=0$ in (13.3). The equality of tail data is the exact finite identity

$$
\begin{aligned}
P_{k_0}\binom{t_0}{v_0}
&=P_{k_*}\binom tv+\epsilon\mathbf b\\
&=P_{k_*+\epsilon}\binom tv
=P_{k_1}\binom{t_1}{v_1}.
\end{aligned}
\tag{14.6}
$$

Consequently at the actual initial index both readings are zero. At the two actual $Q$ indices both readings equal $u$. At each of the three actual $T$ indices the two readings are

$$
u+(1+k_0i_b)(h_bt_0+v_0),\qquad
u+(1+k_1i_b)(h_bt_1+v_1),
$$

and (14.6) makes them equal row by row. This verifies every original observation equation at the six actual nodes. No sampled gain was required to be positive or nonzero; erased and negative samples satisfy these undivided identities. The collision is finite and exact, rather than an inference from a singular derivative alone.

For each run choose the original parameters

$$
\alpha_b=1,\quad\beta_b=k_b,\quad R_b=S_b,\qquad
c_b=(p_b,r_b)^{\mathsf T},\quad\ell_b=(1,q_b/p_b).
\tag{14.7}
$$

The only new source divisor is $p_b>0$. These positive factors multiply to $S_b$, since $p_bs_b=q_br_b$, and $\ell_bA_ic_b=\operatorname{tr}(A_iS_b)$. Along exactly the original words, $M$ sends a positive column $(x,y)^{\mathsf T}$ to $(y,x+y)^{\mathsf T}$ and $J$ sends it to $(y,x)^{\mathsf T}$. Every read and unread state is therefore positive with the same unchanged row during its run. The fixed parameters and the single polynomial (14.5) are used at every node. The two slopes differ by $\epsilon\ne0$, so the effective targets differ irrespective of any exceptional coincidence of source entries. There is no reset, lifted-source replacement, row change, alternative-history combination, or per-read choice of drift. The argument supplies an affine-drift collision; it does not assert a constant-drift collision.

## 15. Mirror realization, exact residual, and unchanged endpoint bounds

Conjugation by $J$ exchanges $E_{22}$ and $E_{11}$ and exchanges upper and lower entries. For an original history put $A'_i=JA_iJ$ and $K'=JKJ$. Then $A'_0=I$ and each multiplier is $JW_iJ$, a finite $M/J$ word, including the empty word when $W_i$ is empty. The six actual indices, traces, pencil ranks and safety are preserved under the source isomorphism $S'=JSJ$. Apply Sections 11–14 in the primed coordinates. To realize their collisions on the original history, set

$$
S_b=JS'_bJ,\qquad c_b=Jc'_b,\qquad\ell_b=\ell'_bJ,
$$

and keep $k_b,D_b$ unchanged. Both factors are strictly positive, fixed within their run, and multiply to $S_b$. Moreover $\operatorname{tr}(A_iS_b)=\operatorname{tr}(A'_iS'_b)$ at every original node. The original $M/J$ atoms preserve positivity throughout their unread states as well. Thus conjugation is a mathematical correspondence realizing sources on the original words, without requesting a conjugation acquisition or combining observations of two histories.

Combining the results gives the following necessary restriction on the entire diagonal-kernel part of the surviving $d=1$ branch. Mixed positive diagonal generators are excluded by Theorem 11.1. For $E_{22}$, Theorem 11.2 gives the complete legal-chain normal form, Proposition 12.1 requires a final phase and $a\le3$, and Sections 12–14 exclude every $a=1$ list by actual different-slope collisions. Therefore a uniformly recovering diagonal-kernel history must have exactly

$$
a=2\quad\text{or}\quad a=3
$$

initial lower-shear readings $D_h$, including $A_0=I$. These are exactly its endpoints with $(A_i)_{12}=0$; no later endpoint can return to that zero entry. In the $E_{11}$ branch the corresponding number of initial upper-shear readings, or endpoints with $(A_i)_{21}=0$, is two or three. The initial shears may repeat $I$ or may be nontrivial; neither possibility is silently excluded. Section 10 separately excludes every recorded-$M/JMJ$ list under the common-safe-kernel hypotheses.

The remaining $d=1$ diagonal residual is precisely the normal-form candidates with $a=2$ or $3$, still subject to every all-real-slope rank, transverse and quadratic necessary test and to exclusion of recorded $M$ or $JMJ$ for recovery. No global inverse or universal collision for these candidates is established. Every non-diagonal normalized safe generator remains in scope, with any off-diagonal entries and determinant allowed by the safe cone; those generators are not classified by the diagonal argument. Regular pencils remain for every degree, including the regular five-read $d=0$ branch. For $d\ge2$ the common safe signal has degree at most $d-1$, so the constant-hyperplane chain argument does not classify those histories. These residuals leave the original all-history endpoint goal unchanged.

The credited numerical intervals are exactly

$$
5\le C_{\mathrm{fix}}(0)\le6,\qquad
d+5\le C_{\mathrm{fix}}(d)\le d+6\quad(d\ge1).
$$

The goal remains to choose each endpoint over all predetermined finite-word cumulative histories and provide a matching legal history with a common-source inverse for every real slope, all zero and negative gain samples, and the entire degree-bounded drift; alternatively an endpoint obstruction must realize collisions for every remaining history. A legal normal form is not rank sufficiency, and rank or local nonsingularity is not global recovery sufficiency.

The suppliers credited in Sections 2, 7 and 8 retain their original roles: the positive-secant and fixed-slope criteria, the exact drift quotient, the recorded-clock common-kernel theorem, the critical and quadratic necessary tests, the affine and polynomial recovery constructions, the fixed-prefix continuation optima, the six-read constant-drift result and the representation scales. Section 10's recorded-event classification and finite tail transfer are credited to the preceding recorded-stratum proposal. The mixed diagonal exclusion, complete diagonal legal-chain description, one-initial-zero-entry classification, all-slope inverse and finite collision in Sections 11–14 are credited to the preceding diagonal-stratum proposal named above. Their incorporation supplies proofs and the resulting precise residual in this owning volume; it is not a claim of new priority over those suppliers. No independent review, Lean verification, universal obstruction, improved numerical optimum, adaptive impossibility, optimal atom count, precision or noisy guarantee, physical or empirical claim, general neural-network conclusion, external priority or programme completion is asserted.

## 追加锚（本行以下为增补区）
