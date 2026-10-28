# Affine-gain erasure, positive secants, and drift-kernel collisions

The common-source affine model admits both erased-signal collisions and collisions with strictly positive gains. Positive rank-one secants give an exact criterion at each prescribed slope; its gain-zero specialization tests polynomial agreement of surviving signals. These results restrict candidate fixed histories while leaving the sharp uniform reading count unresolved.

## 1. Common source, chronological history, and recovery target

Let

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$

Fix a known integer $d\ge0$. A legal predetermined $n$-read history has $A_0=I$ and $A_{i+1}=W_iA_i$, where each $W_i$ is a finite word in $M,J$, possibly empty. Matrices act on the left; a displayed product is executed from right to left. The recorded indices are exactly $i=0,\ldots,n-1$. Every recorded scalar advances this index, including an empty-word repeat; an unread atomic operation does not.

The fixed initial relation and instrument satisfy $R=c\ell$, with $c$ a strictly positive column and $\ell$ a strictly positive row. The known operations act only on the column. There are fixed numbers $\alpha>0,\beta\in\mathbb R$ and one fixed polynomial $D\in\mathcal P_d$, where $\mathcal P_d$ denotes all real polynomials of degree at most $d$, including zero. The exact observations are

$$
z_i=(\alpha+\beta i)\operatorname{tr}(A_iR)+D(i)
=(1+\kappa i)\operatorname{tr}(A_iS)+D(i),
\qquad S=\alpha R,\quad\kappa=\beta/\alpha.
$$

Thus

$$
\mathcal R_+=\left\{S=\begin{pmatrix}p&q\\r&s\end{pmatrix}:
 p,q,r,s>0,\ ps=qr\right\},
$$

and the effective recovery target is the entire triple $(S,\kappa,D)$. The slope is arbitrary real; gain zeros and negative gain samples are permitted. There is no reset, copy, physical inverse operation, or combination of observations from unexecuted histories.

**Proposition 1.1 (actual positive realization and representation fibre).** Every effective target in this domain has a single-source, fixed-instrument realization. For a fixed effective target its original relation/gain representations are exactly

$$
R=S/t,\qquad \alpha=t>0,\qquad\beta=\kappa t,
\qquad D\text{ unchanged}.
$$

A positive factorization of a fixed relation has exactly the internal freedom $c\mapsto\lambda c,\ell\mapsto\ell/\lambda$ for $\lambda>0$.

Proof. For $S=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})\in\mathcal R_+$ take

$$
\alpha=1,\quad\beta=\kappa,\quad R=S,\qquad
c=\begin{pmatrix}p\\r\end{pmatrix},\quad
\ell=(1,q/p).
$$

Then $c\ell=S$ because $rq/p=s$, and
$\ell A c=\operatorname{tr}(Ac\ell)=\operatorname{tr}(AS)$.
Both atomic operations preserve strict positivity of the column:
$M(c_1,c_2)^{\mathsf T}=(c_2,c_1+c_2)^{\mathsf T}$ and
$J(c_1,c_2)^{\mathsf T}=(c_2,c_1)^{\mathsf T}$. The row stays fixed throughout the history.

The identities $S=\alpha R$ and $\kappa=\beta/\alpha$ force the displayed representation with $t=\alpha$. Conversely substitution gives
$(t+\kappa ti)\operatorname{tr}(AS/t)=(1+\kappa i)\operatorname{tr}(AS)$ at every position. For the internal factorization, equality $c\ell=c'\ell'$ and positivity of the first columns imply $c'=(\ell_1/\ell'_1)c$; substituting determines both entries of $\ell'$. The converse rescaling preserves the product. On an injective history these are the full remaining representation freedoms. A collision between different effective triples is an additional ambiguity, not this scale fibre. ∎

## 2. The full cone of positive rank-one secants

Define the closed pointed cone

$$
\mathcal C=\left\{\begin{pmatrix}a&b\\c&e\end{pmatrix}:
 a,e\ge0,\ b,c\le0\right\}.
$$

**Theorem 2.1 (exact positive-secant characterization).** A nonzero real matrix $\Delta$ is a difference $S_1-S_0$ of two distinct members of $\mathcal R_+$ if and only if

$$
\Delta\notin\mathcal C\cup(-\mathcal C).
$$

The sufficiency proof constructs positive endpoints for every such matrix, including singular matrices and matrices with nonzero trace.

Proof. Suppose first that $0\ne\Delta\in\mathcal C$. If $S_1=S_0+\Delta$ and both endpoints are strictly positive, the product of the diagonal entries weakly increases while the product of the off-diagonal entries weakly decreases. At least one comparison is strict: a nonzero entry of $\Delta$ changes a positive factor strictly in the indicated direction. The two endpoints therefore cannot both satisfy equality of these products. Exchanging the endpoints excludes $-\mathcal C$ as well.

For sufficiency write $\Delta=(\begin{smallmatrix}a&b\\c&e\end{smallmatrix})$ and $\delta=\det\Delta$. Being outside both cones says that the coefficients $a,-b,-c,e$ include a strictly positive and a strictly negative number. Put

$$
L(x,y)=exy+a-cx-by\qquad(x,y>0).
$$

Each nonzero coefficient can determine the sign at a positive point, as follows:

$$
\begin{aligned}
L(\varepsilon,\varepsilon)&\longrightarrow a,\\
L(T,T)/T^2&\longrightarrow e,\\
L(T,T^{-2})/T&\longrightarrow-c,\\
L(T^{-2},T)/T&\longrightarrow-b.
\end{aligned}
$$

The first limit is as $\varepsilon\downarrow0$ and the other three as $T\to\infty$. Hence there are positive points $(x_-,y_-)$ and $(x_+,y_+)$ with $L_-<0<L_+$, where $L_\pm=L(x_\pm,y_\pm)$.

On their straight segment let

$$
x_\theta=(1-\theta)x_-+\theta x_+,\qquad
y_\theta=(1-\theta)y_-+\theta y_+,\qquad 0\le\theta\le1.
$$

Set $x_* =\min(x_-,x_+)$, $y_* =\min(y_-,y_+)$ and
$m_* =\min(1,x_*,y_*,x_*y_*)>0$. Every entry of

$$
B_\theta=\begin{pmatrix}x_\theta y_\theta&x_\theta\\y_\theta&1\end{pmatrix}
$$

is at least $m_*$. Choose $t>0$ strictly larger than both

$$
\frac{\max(|a|,|b|,|c|,|e|)}{m_*},\qquad
\frac{|\delta|}{\min(-L_-,L_+)}.
$$

Then $-\delta/t$ lies strictly between $L_-$ and $L_+$, also when $\delta=0$. Continuity on the segment supplies $\theta$ with $L(x_\theta,y_\theta)=-\delta/t$. Define

$$
S_0=tB_\theta,
\qquad S_1=tB_\theta+\Delta.
$$

The first endpoint is the positive outer product
$t(x_\theta,1)^{\mathsf T}(y_\theta,1)$. Its entries exceed the absolute values of the entries of $\Delta$, so the second endpoint is also strictly positive. Expanding its determinant gives

$$
\det S_1=t(ex_\theta y_\theta+a-cx_\theta-by_\theta)+\delta=0.
$$

Both endpoints are nonzero and have rank one. Their difference is the prescribed nonzero $\Delta$. Proposition 1.1 supplies actual positive source factorizations for both. ∎

**Proposition 2.2 (the inherited trace-zero secants, with explicit endpoints).** For $0\ne\Delta=(\begin{smallmatrix}a&b\\c&-a\end{smallmatrix})$, the condition in Theorem 2.1 is exactly

$$
a\ne0\quad\text{or}\quad bc<0.
$$

Proof. Membership in either cone forces both $a\ge0,-a\ge0$ or both reversed, hence $a=0$. The remaining forbidden cases have $b,c$ of the same weak sign. This proves the stated equivalence.

Here is a direct endpoint construction. If $a\ne0$, set

$$
L_0=1+|b|+|c|,\qquad
\tau=\frac{a^2+bc+(b+c)L_0}{a},\qquad
h=\sqrt{\tau^2+4L_0^2},
$$

$$
p=\frac{h-\tau}{2},\quad s=\frac{h+\tau}{2},\qquad
S_0=\begin{pmatrix}p&L_0\\L_0&s\end{pmatrix},\quad
S_1=\begin{pmatrix}p+a&L_0+b\\L_0+c&s-a\end{pmatrix}.
$$

Since $h>|\tau|$, $p,s>0$, $ps=L_0^2$ and $s-p=\tau$. The off-diagonal entries of $S_1$ are positive and

$$
\det S_1=a\tau-a^2-bc-(b+c)L_0=0.
$$

Thus $(p+a)(s-a)=(L_0+b)(L_0+c)>0$. If $a>0$, $p+a>0$ forces $s-a>0$; if $a<0$, $s-a>0$ forces $p+a>0$. These are positive rank-one endpoints with difference $\Delta$.

If $a=0,b>0>c$, set $h=\sqrt{-2bc}>0$ and

$$
S_0=\begin{pmatrix}h&b\\-2c&h\end{pmatrix},\qquad
S_1=\begin{pmatrix}h&2b\\-c&h\end{pmatrix}.
$$

They are positive, have determinants $h^2+2bc=0$, and have the required difference. If $b<0<c$, apply this construction to $-\Delta$ and exchange the endpoints. ∎

This trace-zero mechanism is the result of §§14–15 of *FIB 自校准关系数学*. The full nonzero-trace classification in Theorem 2.1 extends that mechanism. Neither criterion requires $\det\Delta\ne0$.

## 3. Exact identifiability at a prescribed slope

Fix a legal history and a real number $\kappa$. Define the linear interpolation kernel

$$
\mathcal K(\kappa,d)=\left\{\Delta:\ \exists H\in\mathcal P_d,
\ (1+\kappa i)\operatorname{tr}(A_i\Delta)=H(i)
\text{ for every }0\le i<n\right\}.
$$

This is a linear subspace of the four-dimensional matrix space. It describes a difference of signals compensated by a single polynomial, without introducing independent lifted sources.

**Theorem 3.1 (fixed-slope criterion, including the safe line).** Suppose $n\ge d+1$. At this prescribed slope the observation map on $\mathcal R_+\times\mathcal P_d$, with target $(S,D)$, is injective if and only if

$$
\mathcal K(\kappa,d)\subseteq\mathcal C\cup(-\mathcal C).
$$

Equivalently, its kernel is zero or is a one-dimensional subspace with a nonzero generator in $\mathcal C\cup(-\mathcal C)$. In particular a nonzero kernel alone does not imply a positive-source collision; its direction matters. A path recovering the unknown-slope target must satisfy this criterion for every real $\kappa$.

Proof. If $\mathcal K(\kappa,d)$ contains a matrix outside the two cones, Theorem 2.1 supplies $S_1-S_0=\Delta$ with positive rank-one endpoints. Let $H$ be its interpolation polynomial. Use the same $\alpha=1,\beta=\kappa$ in the two runs and set $D_0=0,D_1=-H$. Then at every recorded index

$$
z_i^{(1)}-z_i^{(0)}
=(1+\kappa i)\operatorname{tr}(A_i\Delta)-H(i)=0.
$$

The endpoints are distinct actual sources by Proposition 1.1. Each run uses its own one fixed polynomial throughout, as the unknown-drift model permits.

Conversely, equal observations from two targets at the same slope imply, with $\Delta=S_1-S_0$ and $H=D_0-D_1$,

$$
(1+\kappa i)\operatorname{tr}(A_i\Delta)=H(i).
$$

Thus $\Delta\in\mathcal K(\kappa,d)$. If $\Delta\ne0$, Theorem 2.1 puts it outside the two cones, contradicting the inclusion. Hence $S_1=S_0$. Then $D_0-D_1$ vanishes at $n\ge d+1$ distinct points and is zero. The root fact here follows by repeated factorization: a root $x$ gives a factor $t-x$, and every other distinct root remains a root of the quotient. A nonzero polynomial with $m$ distinct roots therefore has degree at least $m$. This also covers constant polynomials and zero leading coefficients in an upper-degree contract.

To prove the subspace alternative define

$$
\Phi\begin{pmatrix}a&b\\c&e\end{pmatrix}=a-b-c+e.
$$

It is strictly positive on $\mathcal C\setminus\{0\}$ and strictly negative on $-\mathcal C\setminus\{0\}$. If a subspace contained in the union had two independent vectors, changing signs would give independent $u,v\in\mathcal C$. Then
$w=\Phi(v)u-\Phi(u)v$ would be nonzero in the subspace but have $\Phi(w)=0$, impossible in the union. Its dimension is therefore at most one. Conversely a line generated by a vector in either cone lies in their union, as does the zero subspace.

Finally full-target injectivity implies injectivity on every fixed-slope slice, proving necessity for every $\kappa$. It does not exclude collisions between different slopes. ∎

If $n<d+1$, recovery of the full drift already fails at a fixed source and slope: the nonzero polynomial $\prod_{i=0}^{n-1}(t-i)$ has degree $n\le d$ and vanishes at all reads, so adding it to $D$ changes the target without changing any observation. Thus the read-length hypothesis in the exact criterion accounts for the drift-only ambiguity.

## 4. Drift-compensated gain erasure on every fixed history

For each noninitial index $1\le j<n$ define

$$
\mathcal E_j=\left\{\Delta:\ \exists Q\in\mathcal P_{d-1},
\ \operatorname{tr}(A_i\Delta)=Q(i)\text{ for every }i\ne j\right\},
$$

where $\mathcal P_{-1}=\{0\}$ when $d=0$. There is no condition on the unweighted signal at $j$.

**Theorem 4.1 (exact erasure interpolation kernel).** For every legal fixed history,

$$
\mathcal E_j=\mathcal K(-1/j,d).
$$

If $n\ge d+1$, recovery of $(S,D)$ at that gain-zero slope is equivalent to $\mathcal E_j$ being zero or being a line with a generator in $\mathcal C\cup(-\mathcal C)$. Any element of $\mathcal E_j$ outside those cones gives an actual collision for the original unknown-slope target.

Proof. Put $g(t)=1-t/j$. For $\Delta\in\mathcal K(-1/j,d)$ its polynomial $H$ satisfies $H(j)=0$, because the actual gain is zero at that recorded index. If $d\ge1$, the factor theorem writes $H(t)=g(t)Q(t)$ with $\deg Q\le d-1$: divide by $t-j$ and multiply the quotient by $-j$. At each survivor $g(i)\ne0$, so the defining equations give $\operatorname{tr}(A_i\Delta)=Q(i)$. If $d=0$, $H$ is constant and its value at $j$ makes it zero, yielding precisely $Q=0$ and zero surviving traces.

Conversely let $\Delta,Q$ satisfy the surviving equations. The polynomial $H=gQ$ has degree at most $d$ and satisfies $H(i)=g(i)\operatorname{tr}(A_i\Delta)$ at every survivor. Both sides vanish at $j$. This proves equality of the two spaces, without dividing by the erased gain. Theorem 3.1 proves the stated exact criterion.

For the actual collision take endpoints $S_1-S_0=\Delta$ from Theorem 2.1, the shared parameters $\alpha=1,\beta=-1/j$, and drifts $D_0=0,D_1=-gQ$. At a survivor their observation difference is $g(i)(\operatorname{tr}(A_i\Delta)-Q(i))=0$; at $j$ both the gain and the drift difference vanish. The two entire drift polynomials meet the declared bound, and Proposition 1.1 realizes both complete histories. ∎

**Corollary 4.2 (square criterion at the candidate minimum).** For $d\ge1$ and $n=d+5$, consider

$$
T_j:(\Delta,Q)\longmapsto
\bigl(\operatorname{tr}(A_i\Delta)-Q(i)\bigr)_{i\ne j},
\qquad Q\in\mathcal P_{d-1}.
$$

Both spaces have dimension $d+4$. Its kernel projects injectively onto $\mathcal E_j$. A recovering history must have zero kernel or a one-dimensional kernel whose matrix generator belongs to $\mathcal C\cup(-\mathcal C)$. Nullity at least two, or a one-dimensional kernel with a matrix generator outside the union, gives the collision in Theorem 4.1.

Proof. The domain dimension is $4+d$ and there are $n-1=d+4$ survivor equations. Projection has image exactly $\mathcal E_j$ by definition. If its matrix part is zero, $Q$ vanishes at $d+4$ distinct nodes despite having degree at most $d-1$, so the polynomial root argument gives $Q=0$. Projection is injective. The rest follows from Theorems 3.1 and 4.1. These dimensions express the proved positive-source criterion; they do not replace it. ∎

For $d=0$ the surviving list includes $I$, so every $\Delta\in\mathcal E_j$ has trace zero. Proposition 2.2 then gives the inherited secant test. For $d\ge1$ the surviving polynomial can be nonzero, and the matrix difference need not have trace zero. A uniform full-target recovery path must pass all these tests, but passing them is not a sufficiency theorem for unknown slope.

## 5. One-erasure matrix-span obstruction

**Theorem 5.1 (full surviving matrix span is necessary).** If deletion of some noninitial position $j$ leaves

$$
\dim\operatorname{span}_{\mathbb R}\{A_i:i\ne j\}\le3,
$$

the fixed path fails uniform recovery for every $d\ge0$. It has two distinct positive rank-one effective sources with the same $\alpha=1$, the same $\kappa=-1/j$, and the shared drift $D=0$. The statement allows arbitrary read counts and arbitrary finite words between reads.

Proof. Each cumulative matrix is a nonnegative integer matrix with determinant $\pm1$, since both atoms have these properties. The survivors include $I$. Select survivors $A,B$ so that $I,A,B$ span the surviving space, repeating $I$ if fewer generators are needed. On trace-zero matrices

$$
\Delta=\begin{pmatrix}a&b\\c&-a\end{pmatrix},\qquad
A=\begin{pmatrix}u&v\\w&x\end{pmatrix},
$$

one has $\operatorname{tr}(A\Delta)=(u-x)a+wb+vc$. The two homogeneous equations for $A,B$ in three variables have a nonzero solution.

If this solution has $a\ne0$ or $bc<0$, retain it. Otherwise $a=0,bc\ge0$; change its sign so that $b,c\ge0$, not both zero. For each selected matrix the equation is $wb+vc=0$, a sum of nonnegative terms. If $b>0$ its lower-left entry is zero; if $c>0$ its upper-right entry is zero. Thus both selected matrices are triangular. Their nonnegative integer diagonal entries have product $\pm1$, hence product $1$ and both entries $1$. Therefore $\Delta_0=\operatorname{diag}(1,-1)$ also annihilates $I,A,B$. Replace the solution by $\Delta_0$.

In either case Proposition 2.2 supplies distinct positive rank-one endpoints with difference $\Delta$ and identical surviving traces. The common gain $1-i/j$ hides the only possibly unequal signal at $j$; it is zero there. The shared zero drift meets every degree bound. Every surviving observation and the erased observation are equal. Proposition 1.1 supplies the positive fixed-row realizations on precisely the prescribed history. ∎

The trace-zero secant and triangular unimodular argument are inherited from §§14–15 of *FIB 自校准关系数学*. Their one-erasure formulation applies them to affine gain and all legal fixed histories. Theorem 4.1 additionally permits polynomial surviving trace differences. Section 9 exhibits a family excluded by that additional mechanism despite full surviving matrix span.

**Corollary 5.2 (five-read restriction).** A uniformly recovering five-read path must have five distinct cumulative matrices. Deleting any noninitial read must leave four linearly independent matrices.

Proof. The second assertion is the contrapositive of Theorem 5.1. If a five-read list has at most three distinct matrices, every surviving span has dimension at most three. If it has at most four distinct matrices and total span at most three, the same conclusion holds. In the remaining case it has exactly four distinct matrices and total rank four. At least three of the four matrices occur only once, and at least two of these single occurrences are noninitial. Deleting one such noninitial occurrence leaves at most three distinct matrices. Theorem 5.1 again gives a collision. This distinctness assertion is specific to five reads. ∎

**Proposition 5.3 (a larger distinct-endpoint collision family).** For every $n\ge5$, the legal path

$$
A_0=I,\quad A_1=M,\quad
A_i=U^{i-1}\ (2\le i\le n-2),\quad
A_{n-1}=MU^{n-3}
$$

has a collision. In particular $n=d+5$ excludes a candidate at the inherited lower endpoint for every $d\ge0$.

Proof. Execute $M$, then $J$ to reach $U$, then successive $U$ blocks to reach the listed powers, and finally $M$. Each $U$ block is chronologically $M,J$ without an intermediate read. This is one legal path with distinct recorded matrices.

Take

$$
S_0=\begin{pmatrix}3&5\\6&10\end{pmatrix},\qquad
S_1=\begin{pmatrix}4&6\\6&9\end{pmatrix}.
$$

They are positive and their determinants are $30-30=0$ and $36-36=0$. Both have trace $13$, $M$ signal $21$, and lower-left entry $6$. Since $U^k=(\begin{smallmatrix}1&k\\0&1\end{smallmatrix})$, their $U^k$ signals are both $13+6k$. The last signals, with $k=n-3$, are respectively $21+10k$ and $21+9k$. Use the common $\kappa=-1/(n-1)$ and $D=0$. The last gain is zero and all earlier signals agree, so every reading agrees. Proposition 1.1 gives actual positive factorizations. This family has neither an initial repeated-read block nor the recorded $I,U,U^2$ calibration prefix. ∎

## 6. Omitting the recorded second shear: the residual inverse

Define

$$
F=M^2U^2=\begin{pmatrix}1&3\\1&4\end{pmatrix},\quad
G=JF=\begin{pmatrix}1&4\\1&3\end{pmatrix},\quad
H=UG=\begin{pmatrix}2&7\\1&3\end{pmatrix}.
$$

For any integer $B\ge1$, take $B$ initial reads at $I$, followed by $U,F,G,H$ at indices $B,B+1,B+2,B+3$. After the last initial read the chronological blocks are $M,J$; then $M,J,M,M$; then $J$; then $M,J$. The intermediate $U^2$ is executed but unrecorded. There are nine atomic operations and $B+4$ scalar reads. Omitting this read changes all later recorded indices relative to the successful calibration scheme.

For $S=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$ put $a=\operatorname{tr}S$ and, with $(C_1,C_2,C_3,C_4)=(U,F,G,H)$, set $V_k(S)=\operatorname{tr}(C_kS)-a$. Then

$$
V(S)=(r,\ q+3r+3s,\ q+4r+2s,\ p+q+7r+2s).
$$

**Proposition 6.1 (invertible residual map and every erasure span).** The linear map $V$ on the full matrix space is invertible. Every noninitial erasure of the $B+4$-read history leaves four-dimensional matrix span.

Proof. Given $v=V(S)$, direct substitution yields

$$
r=v_1,\qquad s=v_2-v_3+v_1,\qquad
q=3v_3-2v_2-6v_1,\qquad p=v_4-v_3-3v_1.
$$

For example, the expression for $s$ cancels the $q$ terms and leaves $s$; the expression for $q$ leaves $q$; the last leaves $p$. These equations recover every entry and also verify $V$ applied to the recovered matrix equals $v$. Thus the four trace functionals of $C_k-I$ are independent, and the five matrices $I,U,F,G,H$ have rank four. Entrywise,

$$
I-2U+F-2G+H=0.
$$

This is their unique dependence up to scale, and every coefficient is nonzero. A dependence on four would extend to a dependence on five with a zero coefficient, contradicting uniqueness. Hence any four of them are independent. Deleting a tail read leaves $I$ and three other tail matrices. Deleting a noninitial initial repeat, when one exists, leaves an $I$ and all four tail matrices. Both surviving lists have rank four. ∎

## 7. A constant-drift five-read collision with positive gains

**Theorem 7.1 (positive-gain failure of $I,U,F,G,H$).** For $d=0$ and $B=1$, the path in §6 has distinct effective targets with equal observations and strictly positive gain samples at every recorded index.

Proof. Set $\varepsilon=1/1000$. Let $T$ be the smaller root of

$$
11\varepsilon T^2+(57\varepsilon-2)T+109\varepsilon+22=0,
$$

or explicitly

$$
T=\frac{2-57\varepsilon-\sqrt{4-1196\varepsilon-1547\varepsilon^2}}{22\varepsilon}.
$$

To check the root and positivity, put
$f(T)=2T-22-\varepsilon(11T^2+57T+109)$.
It is a concave quadratic, $f(11)=-2067\varepsilon<0$, and
$f(13)=4-2709\varepsilon>0$. It tends to $-\infty$ as $T\to\infty$, so it has two distinct real roots, one in $(11,13)$ and the other above $13$. For $0<T\le11$, both terms make $f(T)<0$. The root in $(11,13)$ is the smaller root; in particular the displayed discriminant is strictly positive and this formula selects a positive root with $11<T<13$.

Define

$$
S_1=\begin{pmatrix}1&T\\1&T\end{pmatrix},\qquad
Q=\begin{pmatrix}T+15&10T+17\\T+2&-T-5\end{pmatrix},
\qquad S_0=S_1+\varepsilon Q.
$$

The first source is positive rank one. The first three entries of $S_0$ are positive. Its bottom-right entry is
$T-\varepsilon(T+5)>11-18/1000>0$. The mixed determinant coefficient and the determinant of $Q$ are respectively

$$
2T-22,\qquad -11T^2-57T-109.
$$

Indeed the first is
$(-T-5)+T(T+15)-T(T+2)-(10T+17)$, and the second is
$(T+15)(-T-5)-(10T+17)(T+2)$. Consequently

$$
\det S_0=\varepsilon\bigl[(2T-22)-\varepsilon(11T^2+57T+109)\bigr]=0.
$$

This proves strict positivity and rank one for both sources.

To verify every read, use the linear operator

$$
N\begin{pmatrix}p&q\\r&s\end{pmatrix}
=\begin{pmatrix}2p+q+13r&-p+5q+18r+5s\\p+s+r&-q-5r\end{pmatrix}.
$$

Substitution in the four residual formulas gives

$$
\begin{aligned}
V_1(N(S))&=p+r+s=\operatorname{tr}(US),\\
V_2(N(S))&=2p+2q+6r+8s=2\operatorname{tr}(FS),\\
V_3(N(S))&=3p+3q+12r+9s=3\operatorname{tr}(GS),\\
V_4(N(S))&=8p+4q+28r+12s=4\operatorname{tr}(HS).
\end{aligned}
$$

Here $N(S_1)=Q$ and $\operatorname{tr}Q=10$. Give run $0$ the parameters $\kappa_0=0,D_0=0$, and run $1$ the parameters $\kappa_1=\varepsilon,D_1=10\varepsilon$, with $\alpha=1$ in both. Their initial readings coincide because
$\operatorname{tr}S_0=\operatorname{tr}S_1+10\varepsilon$.
At actual tail index $k=1,2,3,4$, subtract this common initial reading. Run $0$ gives $V_k(S_0)$, while run $1$ gives

$$
V_k(S_1)+\varepsilon k\operatorname{tr}(C_kS_1)
=V_k(S_1)+\varepsilon V_k(N(S_1))=V_k(S_0).
$$

Thus all five observations agree. Gains are respectively $1$ and $1+\varepsilon i>0$, and both drifts are constants. Proposition 1.1 realizes each positive source with one fixed positive row. The differing slopes make the effective targets distinct. ∎

This excludes this particular five-read path. It does not prove a six-read lower bound for constant drift or provide a six-read recovering path.

## 8. Positive-gain collisions for every affine-drift degree bound

**Theorem 8.1 (the omitted-$U^2$ family fails for every $d\ge1$).** For every $d\ge1$ and every integer $B\ge1$, the $B+4$-read history of §6 has a collision with positive gain samples and drift polynomials of degree at most one. Taking $B=d+1$ excludes a $d+5$-read candidate. Extra initial $I$ reads do not repair this tail family.

Proof. Write $m=B-1$ and choose

$$
0<h<\min\left(\frac1{20},\frac1{2(m+1)}\right),\qquad
\varepsilon=\frac h{1-mh}>0.
$$

In fact $mh<1/2$, so the denominator is positive. The coefficient $39-91h$ is positive. The quadratic

$$
(39-91h)T^2-(28+823h)T-(267+1167h)=0
$$

has negative constant term and positive leading coefficient, so its roots are real of opposite signs and its positive root is unique. It is

$$
T=\frac{28+823h+\sqrt{(28+823h)^2+4(39-91h)(267+1167h)}}{2(39-91h)}.
$$

Its polynomial takes the value $-4455h<0$ at $T=3$, hence this positive root satisfies $T>3$.

Set

$$
S_1=\begin{pmatrix}7&7T\\3&3T\end{pmatrix},\qquad
L\begin{pmatrix}p&q\\r&s\end{pmatrix}
=\begin{pmatrix}4p+q+13r+2s&5q+18r+6s\\r&-q-5r\end{pmatrix},
$$

$$
L(S_1)=\begin{pmatrix}67+13T&54+53T\\3&-15-7T\end{pmatrix},\qquad
S_0=\frac{S_1+hL(S_1)}{1-mh}.
$$

The first source is strictly positive rank one. The numerator of $S_0$ has positive first three entries. Its bottom-right entry is

$$
T(3-7h)-15h>9-36h>0,
$$

since $T>3$ and $h<1/20$. Direct two-by-two expansion gives mixed determinant coefficient $39T^2-28T-267$ and
$\det L(S_1)=-91T^2-823T-1167$. More explicitly these are

$$
7(-15-7T)+3T(67+13T)-21T-3(54+53T),
$$

and

$$
(67+13T)(-15-7T)-3(54+53T),
$$

respectively. Therefore

$$
\det(S_1+hL(S_1))
=h\bigl[(39-91h)T^2-(28+823h)T-(267+1167h)\bigr]=0.
$$

The positive denominator preserves positivity and rank one of $S_0$.

The four residual identities are

$$
\begin{aligned}
V_1(L(S))&=r=V_1(S),\\
V_2(L(S))&=2q+6r+6s=2V_2(S),\\
V_3(L(S))&=3q+12r+6s=3V_3(S),\\
V_4(L(S))&=4p+4q+28r+8s=4V_4(S).
\end{aligned}
$$

They follow by substituting the displayed entries of $L$ into $V$. Since

$$
S_0=S_1+\varepsilon\bigl(mS_1+L(S_1)\bigr),
$$

these identities give

$$
V_k(S_0)=[1+\varepsilon(m+k)]V_k(S_1),\qquad1\le k\le4.
$$

Let $a_b=\operatorname{tr}S_b$. Give run $0$ the parameters
$\kappa_0=0,D_0(t)=-a_0$ and run $1$ the parameters
$\kappa_1=\varepsilon,D_1(t)=-a_1(1+\varepsilon t)$, again with $\alpha=1$. Every initial $I$ reading is zero in both runs, including the actual indices $0,\ldots,B-1$. At tail index $i=B+k-1=m+k$, their observations are respectively

$$
V_k(S_0),\qquad (1+\varepsilon i)V_k(S_1),
$$

which agree by the preceding identity. Gains are $1$ or $1+\varepsilon i>0$ at every recorded index. Both drifts have degree at most one, and thus at most $d$. The targets differ in slope. Proposition 1.1 supplies actual positive factors and fixed instruments throughout the nine-operation history. ∎

The results in §§6–8 are the positive-gain omitted-calibration family. They concern the specific tail $U,F,G,H$; they do not exclude arbitrary four-tail choices.

## 9. A different full-span family detected by polynomial erasure

Put

$$
T_0=MU=\begin{pmatrix}0&1\\1&2\end{pmatrix},\qquad
T_1=UMU=\begin{pmatrix}1&3\\1&2\end{pmatrix},\qquad
T_2=U^2MUMU=\begin{pmatrix}5&12\\2&5\end{pmatrix}.
$$

**Theorem 9.1 (strictness beyond every matrix-span test).** For every $d\ge1$, let $B=d+1$. Take $B$ initial reads at $I$ followed by $U,T_0,T_1,T_2$. This $d+5$-read history passes every noninitial one-erasure matrix-span test but has a common-slope positive-source collision. The same construction works for any $B\ge1$ when affine drift is allowed.

Proof. After the empty-word initial repeats, execute $M,J$ to reach $U$ and read at $B$; execute $M$ to reach $T_0$ and read at $B+1$; execute $M,J$ to reach $T_1$ and read at $B+2$; execute $M,M,J,M,J$ to reach $T_2$ and read at $B+3$. The final block has left multiplier $U^2M$, giving $U^2MT_1=U^2MUMU$. These blocks have lengths $2,1,2,5$, hence ten atomic operations and $B+4$ actual reads. The unread intermediate states do not advance the reading clock.

The four matrices $I,U,T_0,T_1$ are independent. To verify this using the nondegenerate trace pairing, let $\Delta=(\begin{smallmatrix}a&b\\c&e\end{smallmatrix})$ annihilate them. Successively their equations give

$$
a+e=0,\quad a+c+e=0,\quad b+c+2e=0,\quad a+b+3c+2e=0.
$$

Thus $c=0$, subtracting the third equation from the fourth gives $a=0$, and then $e=b=0$. A matrix annihilating all four is zero, so their four trace functionals, and hence the four matrices, are independent. Entrywise the five matrices satisfy

$$
I-2U+2T_0-4T_1+T_2=0.
$$

Rank four makes this the unique dependence up to scale. Every coefficient is nonzero, so any four of the five are independent. Deleting a tail read therefore leaves rank four, as does deleting a noninitial initial repeat when such a repeat exists. All inherited erasure-span tests pass.

Now take

$$
S_0=\begin{pmatrix}6&9\\1&3/2\end{pmatrix}
=\begin{pmatrix}6\\1\end{pmatrix}(1,3/2),\qquad
S_1=\begin{pmatrix}4&5\\2&5/2\end{pmatrix}
=\begin{pmatrix}4\\2\end{pmatrix}(1,5/4).
$$

They are positive rank one and distinct. Their difference is

$$
\Delta=S_1-S_0=\begin{pmatrix}-2&-4\\1&1\end{pmatrix},
$$

outside both cones. Its traces at $I,T_0,T_1,T_2$ are respectively

$$
-2+1=-1,\quad -4+1+2=-1,\quad
-2-4+3+2=-1,\quad -10-8+12+5=-1.
$$

At $U$ its trace is $-2+1+1=0$. Thus $\Delta\in\mathcal E_B$ with the constant surviving polynomial $Q=-1$, despite the full surviving span.

Use $\alpha_0=\alpha_1=1$, the common slope $\kappa=-1/B$, and

$$
g(t)=1-t/B,\qquad D_0(t)=0,\qquad D_1(t)=g(t).
$$

These drifts have degree at most $d$ when $d\ge1$. At every index except $B$ the unweighted signal difference is $-1$, giving observation difference $-g(i)+g(i)=0$. At $B$ the gain is zero and $D_1(B)=0$, so that observation also agrees. This accounts for every initial repeat, the erased read, and the later negative gains. The displayed positive factorizations use one fixed row in each run for the entire legal history. The effective sources and drifts differ, so the collision is not a representation rescaling. ∎

This tail differs from $U,F,G,H$ and does not have a recorded $I$-block,$U,U^2$ prefix. It proves that the drift-compensated condition is strictly stronger than the inherited matrix-span exclusion for $d\ge1$. Its gain samples include a zero and later negative values; the separate collisions of §§7–8 have strictly positive gains. The drift difference here is affine, so this family is not a constant-drift collision.

## 10. Credited numerical bounds and their common-source interfaces

Let $C_{\mathrm{fix}}(d)$ denote the smallest uniform exact-read bound over all legal predetermined finite-composite-word cumulative histories for the full target $(S,\kappa,D)$.

**Theorem 10.1 (inherited bounds, unchanged).** The affine recovery companion *Shared affine gain and zero-crossing recovery*, Theorems 2.1 and 5.1, gives

$$
d+5\le C_{\mathrm{fix}}(d)\le\max(d+6,7).
$$

The upper bound uses a legal nine-operation history and allows every real slope, including every gain zero. These numerical bounds are credited existing results.

Proof of the upper interface. Set $B=\max(d+1,2)$ and record $B$ reads at $I$, then $U,U^2,F,G,H$. The chronological blocks after the initial repeats are $M,J$; $M,J$; $M,M$; $J$; $M,J$, so the history has nine operations and $B+5$ reads. Put $a=\operatorname{tr}S$ and $P(t)=D(t)+a(1+\kappa t)$. This polynomial has degree at most $B-1$; its $B$ initial values determine it by

$$
P(t)=\sum_{j=0}^{B-1}z_j
\prod_{\substack{0\le h<B\\h\ne j}}\frac{t-h}{j-h}.
$$

Each denominator is a fixed nonzero integer. The products take the prescribed values at all nodes, and uniqueness follows from the root argument in Theorem 3.1.

The two shear signals are $a+r$ and $a+2r$. Hence

$$
v_0=z_B-P(B)=r(1+\kappa B),\qquad
v_1=\frac{z_{B+1}-P(B+1)}2=r(1+\kappa(B+1)).
$$

Thus $\eta=v_1-v_0=\kappa r$, $r=v_0-B\eta>0$, and $\kappa=\eta/r$, without dividing by either gain sample.

At each nonzero-gain final position form
$V_i=(z_i-P(i))/(1+\kappa i)=\operatorname{tr}(A_iS)-a$.
For $F,G,H$, after subtracting respectively $3r,4r,7r$, these yield

$$
X=q+3s,\qquad Y=q+2s,\qquad Z=p+q+2s.
$$

The affine gain has intercept one and at most one zero, so at least two are available. The following three inverses cover every pair:

$$
\begin{array}{c|l}
(X,Y)&s=X-Y,\quad q=Y-2s,\quad p=qr/s,\\
(Y,Z)&p=Z-Y,\quad s=rY/(p+2r),\quad q=ps/r,\\
(X,Z)&h=Z-X,\quad b=h+3r,\quad
s=2rX/(\sqrt{b^2+4rX}+b),\quad p=s+h,\quad q=ps/r.
\end{array}
$$

For actual positive sources the first denominator is $s>0$, and $p+2r>0$ in the second pair. For the third pair $h=p-s$ and $rX=(p+3r)s$ imply $s^2+bs-rX=0$. Since $rX>0$, exactly one root is positive; rationalizing that root gives the formula, whose denominator is positive because $\sqrt{b^2+4rX}>|b|$. It covers either sign of $h$, either sign of $b$, and $b=0$. Consequently every available pair recovers the true positive source. Set

$$
D(t)=P(t)-(p+s)(1+\kappa t).
$$

For $d=0$ the possibly affine part of $P$ cancels exactly, leaving the actual constant drift. For $d\ge1$ the degree bound also holds. Equal data force equal $P,r,\kappa$, the same available pair, and hence equal $S,D$. Proposition 1.1 realizes the entire single-source history. This proves the upper interface, including every zero-gain case.

Proof of the lower interface. Use the injective actual-target chart

$$
\mathcal V=(0,\infty)^3\times\mathbb R^{d+2},\qquad
(p,q,r,\kappa,\delta_0,\ldots,\delta_d),
$$

$$
S=\begin{pmatrix}p&q\\r&qr/p\end{pmatrix},\qquad
D(t)=\sum_{h=0}^d\delta_ht^h.
$$

Its dimension is $N=d+5$, and every point has the positive realization of Proposition 1.1. For any fixed $m$-read history the observation map $F:\mathcal V\to\mathbb R^m$ is smooth with components

$$
F_i=(1+\kappa i)\left((A_i)_{00}p+(A_i)_{10}q+(A_i)_{01}r
 +(A_i)_{11}\frac{qr}{p}\right)+\sum_{h=0}^d\delta_hi^h.
$$

Suppose $m<N$ and let $\rho$ be its largest attained Jacobian rank. Then $\rho\le m<N$. If $\rho=0$, integration of the zero derivative along line segments in a small convex ball shows that $F$ is constant there, giving distinct actual targets with identical observations.

If $\rho>0$, choose a nonzero $\rho$-minor at a point. On a sufficiently small neighborhood it stays nonzero, and maximality of $\rho$ makes the total rank exactly $\rho$. Permute coordinates and outputs to put this minor in the first $\rho$ coordinates and components. The implicit function theorem makes the level set of those first components through the point a smooth graph over a small open ball in the remaining $N-\rho>0$ coordinates. At every graph point, all other output differentials are linear combinations of the first $\rho$ output differentials, since those rows are independent and the total rank is $\rho$. They therefore vanish on all graph tangent vectors. Integrating along paths in the connected graph patch makes all output components constant. The graph contains distinct actual targets, proving noninjectivity.

If a fixed protocol stops early, extend its predetermined history to its claimed uniform bound. Equal complete observations give equal prefixes and the same stopping decisions, so the padded collision still prevents recovery. This smooth fixed-history argument does not establish an adaptive lower bound. ∎

For finite proposed data on the upper-bound history, positivity and rank one of the decoded $S$, the declared degree of the decoded $D$, and every actual observation equation, including all gain-zero positions, are necessary and sufficient for common-source compatibility. Necessity follows from the inverse just proved. For sufficiency choose $\alpha=1,R=S,\beta=\kappa$ and the positive factorization in Proposition 1.1; the checked equations realize all the proposed readings on that one history. Under its injectivity the representation fibre is precisely Proposition 1.1.

## 11. Credits and the exact remaining sharp question

The source *FIB 自校准关系数学*, Definitions 10.1–10.3 and 38.1, supplies the positive rank-one domain, cumulative left action, fixed instrument, counted initial read, finite-composite-word contract, and effective target. Its §§1–5 supply the trace identity, Fibonacci recurrence, four-trace relation inverse, and positive factorization scale. Its §§14–15 supply the trace-zero secants and nonnegative integer unimodular collision mechanism used in §5. The fixed/adaptive reading distinctions and action boundaries of §§10–17 are retained. The unbiased fixed-fibre stability and word-frontier results of §§18–32 do not supply an affine-gain sharpness theorem here.

Sections 33–35 of that source supply the known-unit-gain affine and bounded-degree additive-drift interfaces; §36 gives the positive-source five-read result for known unit gain and affine additive drift. Section 37 supplies the ten-dimensional lifted inverse and the distinction between independent lifted matrices and one common source. Theorem 38.2 supplies the $d+7$ restricted-gain and $d+8$ unrestricted single-switch upper bounds; Proposition 38.4 supplies its particular zero-gain collision, Proposition 38.5 its finite-data compatibility interface, and Corollary 38.3 its positive relation/gain scale. They remain credited separate results.

The corrected affine companion supplies the smaller $\max(d+6,7)$ upper bound, the $d+5$ fixed-history lower bound, its exact positive-scale fibre, and its obstruction for predetermined continuations of the recorded $I$-block,$U,U^2$ prefix. Section 10 reproduces the complete bound interfaces. The omitted-$U^2$ family in §§6–8 omits that recorded calibration position and has positive-gain collisions; it is a separate restriction on candidate paths. The secant-cone and drift-kernel results in §§2–4 give the complete fixed-slope criterion, including safe one-dimensional kernels. The ten-operation family in §9 proves a strict additional exclusion even after every matrix-span test has passed. These are mathematical restrictions and equivalences, without an external priority claim.

Section 39 of the main source treats a broader nonzero common polynomial gain $G$ of known degree at most $k$ and drift of degree at most $d$. Its single-switch recovery bound is $3k+d+5$, for normalized target $(R_0,H,D)$ with $R_0=R/\operatorname{tr}R$ and $H=(\operatorname{tr}R)G$. It includes initial gain zero and remains separate from the present affine model with $\alpha>0$. In the affine submodel the target correspondence is

$$
R_0=\frac S{\operatorname{tr}S},\qquad
H(t)=(\operatorname{tr}S)(1+\kappa t),
$$

and conversely $S=H(0)R_0$, $\kappa=H'(0)/H(0)$ when $H(0)>0$. Thus its $k=1$ bound is $d+8$; it does not settle the smaller affine optimum.

The numerical intervals remain exactly

$$
d+5\le C_{\mathrm{fix}}(d)\le d+6\quad(d\ge1),\qquad
5\le C_{\mathrm{fix}}(0)\le7.
$$

The unresolved target is the sharp uniform number of exact scalar reads over all predetermined legal finite-word cumulative paths, with a matching actual common-source inverse valid for every real affine slope and the entire declared drift polynomial. No uniform $d+5$ construction and no obstruction covering every $d+5$ path is established here; the constant-drift optimum is also unresolved. The excluded families do not exhaust the legal paths. A surviving matrix span of four is not sufficient. Even passing every fixed-slope criterion would not exclude collisions between distinct slopes. The affine-drift family in §9 provides no constant-drift consequence.

All operation counts are counts of actual $M/J$ atoms on the specified histories. Reading count, atomic-operation count, elapsed time, bit precision, and acquisition cost are distinct quantities. The theorems concern exact mathematical observations under the stated model; they give no adaptive impossibility theorem, noisy-stability guarantee, or optimal operation count.

## 追加锚（本行以下为增补区）
