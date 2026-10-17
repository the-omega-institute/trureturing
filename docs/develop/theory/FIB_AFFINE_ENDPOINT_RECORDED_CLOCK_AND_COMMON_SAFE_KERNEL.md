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
