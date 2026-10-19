# Terminal repetition and recorded-clock obstructions with affine gain

For every positive declared additive degree, terminal repetition gives a recovering history with the sharp $d+5$ exact reads and seventeen literal $M/J$ atoms, independently of $d$. This improves the two credited growing atom counts for $d\ge2$; the credited fifteen-atom construction remains better at $d=1$. A separate constant-drift theorem gives two necessary recorded-clock determinants in a specified diagonal endpoint stratum and constructs actual positive-gain collisions when either fails under the stated erasure-span hypothesis. The original constant-drift question remains $5\le C_{\mathrm{fix}}(0)\le6$.

## 1. The unchanged common-source programme

Let

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
$$

A legal fixed history has $A_0=I$ and $A_{i+1}=W_iA_i$, with each $W_i$ a predetermined finite word in $M,J$, possibly empty. Products act on the left and execute from right to left. Thus chronological $(M,J)$ implements $U$, while $(J,M)$ implements $L$. Every scalar read advances the consecutive recorded index $i$, including a repeat after an empty word; an unread atom does not advance it.

The effective source and complete observations are

$$
S=\begin{pmatrix}p&q\\r&s\end{pmatrix},\qquad
p,q,r,s>0,\quad ps=qr,
$$

$$
z_i=(1+ki)\operatorname{tr}(A_iS)+D(i),\qquad
k\in\mathbb R,\qquad D\in\mathbb R[\tau],\quad\deg D\le d.
\tag{1.1}
$$

The integer upper degree $d\ge0$ is known; smaller actual degrees and the zero polynomial are included. The target is the entire triple $(S,k,D)$. In original parameters, $S=\alpha R$, $k=\beta/\alpha$, $\alpha>0$, $\beta\in\mathbb R$, and $R$ is a single strictly positive rank-one relation. There is one fixed positive row during each run. All real slopes, sampled gain zeros, and negative gains belong to the domain. There are no resets, source copies, inverse acquisitions, alternative unexecuted histories, independently lifted sources, or extra acquisition clocks.

Every allowed effective source has the actual realization

$$
\alpha=1,\quad\beta=k,\quad R=S,\qquad
c_{\mathrm{col}}=\binom p r,\qquad\ell=(1,q/p).
\tag{1.2}
$$

Indeed $c_{\mathrm{col}}\ell=S$, since $s=qr/p$. For $A=(\begin{smallmatrix}a&b\\c&e\end{smallmatrix})$,

$$
\ell A c_{\mathrm{col}}=\operatorname{tr}(AS)=ap+br+cq+es.
\tag{1.3}
$$

Both factors are strictly positive. Each atom preserves positive columns:

$$
M\binom{x}{y}=\binom{y}{x+y},\qquad
J\binom{x}{y}=\binom{y}{x}\qquad(x,y>0).
\tag{1.4}
$$

Consequently every recorded and unread state along any of the words below is positive, with the same row $\ell$. Different candidate runs may have different fixed rows. Every cumulative word matrix is nonnegative integral with determinant $\pm1$.

Write $C_{\mathrm{fix}}(d)$ for the least uniform exact-read bound over all such predetermined histories recovering (1.1). The original programme asks for this sharp count for every $d\ge0$, with the whole target and its exact representation fibres. The credited positive-degree equality $C_{\mathrm{fix}}(d)=d+5$ is preserved here. The new positive-degree construction concerns its atom cost; the constant-drift obstruction narrows a proper class of five-read candidates.

## 2. Terminal repetition with seventeen literal atoms

**Theorem 2.1.** For every integer $d\ge1$, let

$$
Q=\begin{pmatrix}6&1\\5&1\end{pmatrix},\qquad
T=\begin{pmatrix}11&2\\6&1\end{pmatrix},\qquad
B=\begin{pmatrix}17&3\\6&1\end{pmatrix}.
$$

The $d+5$ actual recorded endpoints

$$
A_0=I,\qquad A_1=L^2,\qquad A_2=Q,\qquad A_3=T,\qquad
A_i=B\quad(4\le i\le d+4)
\tag{2.1}
$$

globally recover (1.1) for every allowed source, every real $k$, and every whole polynomial $D$ of degree at most $d$. They admit the literal seventeen-atom implementation below and the finite whole-image inverse in Section 5.

The successive nonempty left multipliers are

$$
L^2,\qquad UL^3,\qquad UJ,\qquad U.
\tag{2.2}
$$

Their chronological atom blocks are

$$
(J,M,J,M),\qquad
(J,M,J,M,J,M,M,J),\qquad
(J,M,J),\qquad(M,J).
$$

Their lengths are $4,8,3,2$, totaling seventeen. The final $d$ transitions are empty words. Direct multiplication, using $U^j=(\begin{smallmatrix}1&j\\0&1\end{smallmatrix})$ and $L^j=(\begin{smallmatrix}1&0\\j&1\end{smallmatrix})$, gives

$$
Q=UL^5=(UL^3)L^2,\qquad
JQ=\begin{pmatrix}5&1\\6&1\end{pmatrix},\qquad T=UJQ,\qquad B=UT.
$$

These are exactly the displayed endpoints on one forward history. There are no interior reads within the words. The first four readings occur at indices $0,1,2,3$ and the final $d+1$ readings at $4,\ldots,d+4$. Equations (1.2)–(1.4) realize this execution with one positive source and an unchanged row. The remaining proof of the theorem occupies Sections 3–5.

## 3. Coordinates and the entire polynomial reduction

Put $a=p+s$ and use the three linear source coordinates

$$
\chi=16p+6q+3r,\qquad t=6p+r,\qquad v=q-p.
\tag{3.1}
$$

Their exact inverse is

$$
p=\frac{\chi-3t-6v}{4},\qquad
q=\frac{\chi-3t-2v}{4},\qquad
r=\frac{11t+18v-3\chi}{2}.
\tag{3.2}
$$

For example, the first two numerators are $4p,4q$, and $t-6p$ gives the last formula. Thus the actual source domain is precisely positivity of these three expressions, followed by $s=qr/p$. In particular $\chi>0$. For fixed $\chi$, the permitted $(t,v)$ are an intersection of three open affine half-planes and form a convex set. At a midpoint the entries $p,q,r$ are their positive arithmetic means; its fourth entry is reconstructed as $qr/p$.

Trace expansion gives

$$
\begin{aligned}
\operatorname{tr}(IS)&=a,&
\operatorname{tr}(L^2S)&=a+2q,\\
\operatorname{tr}(QS)&=a+5p+5q+r,&
\operatorname{tr}(TS)&=a+10p+6q+2r,\\
\operatorname{tr}(BS)&=a+\chi.
\end{aligned}
$$

In particular

$$
\begin{aligned}
\operatorname{tr}((B-I)S)&=\chi,\\
\operatorname{tr}((B-L^2)S)&=\chi-2q=(\chi+3t+2v)/2,\\
\operatorname{tr}((B-Q)S)&=11p+q+2r=2t+v,\\
\operatorname{tr}((B-T)S)&=6p+r=t.
\end{aligned}
\tag{3.3}
$$

The single polynomial

$$
P(\tau)=D(\tau)+(a+\chi)(1+k\tau)
\tag{3.4}
$$

has degree at most $d$, since $d\ge1$. All final readings are actual values $z_j=P(j)$, $4\le j\le d+4$. Hence

$$
P(\tau)=\sum_{j=4}^{d+4}z_j
\prod_{\substack{4\le h\le d+4\\h\ne j}}\frac{\tau-h}{j-h}.
\tag{3.5}
$$

All denominators are fixed nonzero integers. The interpolation formula has the prescribed values at its distinct nodes. Uniqueness follows because successive division by distinct root factors makes a polynomial of degree at most $d$ with $d+1$ distinct roots identically zero. Lower actual degrees, cancellation, and $P=0$ are included.

Form from the recorded data

$$
\begin{aligned}
\chi&=P(0)-z_0,&R_1&=P(1)-z_1,& W&=2R_1-\chi,\\
Y&=P(2)-z_2,& Z&=P(3)-z_3.
\end{aligned}
\tag{3.6}
$$

The data value $\chi$ agrees with (3.1). Equations (3.3) give

$$
(W,Y,Z)=F_\chi(t,v,k)
=\bigl((1+k)(3t+2v)+k\chi,\ (1+2k)(2t+v),\ (1+3k)t\bigr).
\tag{3.7}
$$

The first coordinate uses $2R_1=(1+k)(\chi+3t+2v)$. Every identity is undivided at gain zeros.

The change from the complete data to $(P,\chi,W,Y,Z)$ is a linear isomorphism. Its inverse has $z_j=P(j)$ on the terminal block and

$$
z_0=P(0)-\chi,\qquad z_1=P(1)-(W+\chi)/2,\qquad
z_2=P(2)-Y,\qquad z_3=P(3)-Z.
\tag{3.8}
$$

Evaluating the decoded polynomial is not an added observation. Once $t,v,k$ are recovered, (3.2), $s=qr/p$, and

$$
D(\tau)=P(\tau)-(p+s+\chi)(1+k\tau)
\tag{3.9}
$$

recover the entire original drift, with the declared degree bound.

## 4. A strict determinant and global uniqueness

At fixed $\chi$, write $g_j=1+jk$. In coordinate order $(t,v,k)$,

$$
DF_\chi=\begin{pmatrix}
3g_1&2g_1&3t+2v+\chi\\
2g_2&g_2&2(2t+v)\\
g_3&0&3t
\end{pmatrix}.
$$

Expanding along the last column gives

$$
\begin{aligned}
\mathcal J:=\det DF_\chi
&=-(3t+2v+\chi)g_2g_3+4(2t+v)g_1g_3-3t g_1g_2\\
&=(2t+2v-\chi)+(8t+6v-5\chi)k-6\chi k^2.
\end{aligned}
$$

Substitution of (3.1) yields

$$
-\mathcal J
=p(96k^2+38k+6)+q(36k^2+24k+4)+r(18k^2+7k+1).
\tag{4.1}
$$

The brackets equal, respectively,

$$
96(k+19/96)^2+215/96,\qquad
4(3k+1)^2,\qquad
18(k+7/36)^2+23/72.
$$

The first and third are strictly positive and the second is nonnegative. Since $p,r>0$, $\mathcal J<0$ for every real $k$, including $k=-1/3$ where the middle bracket vanishes.

This sign has a global consequence through an exact finite identity. Set $y=(t,v)^{\mathsf T}$. At fixed $\chi$, the reduced map is of the form

$$
F_\chi(y,k)=A y+k C y+k\chi e_1
$$

for fixed real matrices $A,C$ and $e_1=(1,0,0)^{\mathsf T}$. For two points use bars for arithmetic means and $\Delta$ for their difference. The identity

$$
k_0y_0-k_1y_1=\bar k\,\Delta y+\bar y\,\Delta k
$$

gives

$$
F_\chi(y_0,k_0)-F_\chi(y_1,k_1)
=DF_\chi(\bar y,\bar k)(\Delta t,\Delta v,\Delta k)^{\mathsf T}.
\tag{4.2}
$$

For two actual sources at the same $\chi$, convexity from (3.2) makes the midpoint's $p,q,r$ positive. Its $s$ is reconstructed as $qr/p$, so it is an admissible source. Equation (4.1) makes the midpoint matrix invertible for the real midpoint slope. Equal reduced outputs therefore force equal $t,v,k$.

Two actual targets with the same whole recorded data have the same $P,\chi,W,Y,Z$ by (3.5)–(3.6). Equation (4.2) gives the same $t,v,k$; (3.2) and rank one give the same $S$; (3.9) gives the same entire $D$. This proves global uniqueness, beyond local nonsingularity.

## 5. A finite inverse on the whole data image

**Proposition 5.1.** Arbitrary proposed real data at the positions (2.1) have a common-source realization exactly when the following finite procedure has a passing candidate. A passing effective target is unique.

Interpolate $P$ by (3.5), form (3.6), and require $\chi>0$. Consider the distinct real roots of

$$
H(k)=-(W-\chi k)(1+2k)(1+3k)
+2Y(1+k)(1+3k)-Z(1+k)(1+2k).
\tag{5.1}
$$

Its leading coefficient is $6\chi>0$. Thus it is a nonzero cubic, with at most three distinct real roots by successive division at roots, and at least one by continuity and its opposite limits at the two ends of the real line. Repeated roots are considered once. This is an exact finite algebraic prescription.

For a root define

$$
C_k=\begin{pmatrix}3g_1&2g_1\\2g_2&g_2\\g_3&0\end{pmatrix},\qquad
b_k=(W-\chi k,Y,Z)^{\mathsf T}.
$$

At most one of $g_1,g_2,g_3$ vanishes. The pairwise determinants of the unweighted rows $(3,2),(2,1),(1,0)$ are $-1,-2,-1$. Any two surviving rows are independent, so $\operatorname{rank} C_k=2$ for every real $k$. Cofactor expansion gives

$$
H(k)=\det[C_k^{(1)},C_k^{(2)},b_k].
\tag{5.2}
$$

Consequently $H=0$ is exactly consistency of all three equations $C_k(t,v)^{\mathsf T}=b_k$, including the required right-hand side of an erased row.

Define only the available quotients from

$$
V_1=(W-\chi k)/g_1,\qquad V_2=Y/g_2,\qquad V_3=Z/g_3.
$$

Use any surviving pair:

| Surviving rows | $t$ | $v$ |
|---|---|---|
| $2,3$ | $V_3$ | $V_2-2V_3$ |
| $1,3$ | $V_3$ | $(V_1-3V_3)/2$ |
| $1,2$ | $2V_2-V_1$ | $2V_1-3V_2$ |

Equation (5.2) ensures the remaining row. Form $p,q,r$ by (3.2), require them positive, and set $s=qr/p$. Form the single polynomial (3.9). Require $\deg D\le d$ and every original equation (1.1) at every recorded index $0,\ldots,d+4$, including every erased reading. The degree test is automatic here but is included in the image criterion.

**Proof.** For actual data all identities above hold, the true slope is a root, and a surviving pair returns its true $t,v$. Positivity and every original equation pass. Conversely a passing candidate supplies a strictly positive rank-one $S$, one real slope, and one whole polynomial of the required degree. Equations (1.2)–(1.4) realize it on exactly (2.2) with positive unread states and a fixed row. The checked equations produce all proposed data. Section 4 excludes two passing targets. This proves necessity, sufficiency, and the whole-image inverse. ∎

A zero-gain terminal reading still equals $P(i)$ and remains an interpolation datum. At $k=-1,-1/2,-1/3$ one early reduced row is erased and the other two remain independent; (5.2) retains its zero right-hand-side condition. Gain at zero is one. Gain zeros elsewhere, roots between samples, negative gains, arbitrary signs of readings, $k=0$, zero coefficients, lower actual degrees, and complete polynomial cancellation impose no additional restriction. There is no compulsory division by any gain sample or leading polynomial coefficient. Divisors are fixed nonzero integers, selected surviving gains, and the proved-positive entry $p$.

## 6. Terminal padding, read optimality, and exact fibres

The mechanism has a general formulation. Suppose four legal early endpoints $A_0,\ldots,A_3$ and a later legal endpoint $B$ have an injective residual map

$$
(S,k)\longmapsto
\bigl((1+ki)\operatorname{tr}((B-A_i)S)\bigr)_{i=0}^3
\tag{6.1}
$$

on the original source domain. For every $d\ge1$, record $B$ at the actual indices $4,\ldots,d+4$. Then $P=D+\operatorname{tr}(BS)(1+k\tau)$ has degree at most $d$ and is interpolated from these $d+1$ readings. Its early residuals are exactly (6.1), recovering $S,k$, then the entire $D$. The same finite words suffice for every degree; only empty-word reads are added. This proves the terminal repetition principle. Sections 3–5 verify its hypothesis and an explicit inverse for (2.1).

For completeness, the credited all-fixed-history lower bound applies on the identical target. For a known $d\ge0$, use the injective open actual-target chart

$$
(p,q,r,k,\delta_0,\ldots,\delta_d)\in(0,\infty)^3\times\mathbb R^{d+2},
\quad S=\begin{pmatrix}p&q\\r&qr/p\end{pmatrix},\quad
D(\tau)=\sum_{h=0}^d\delta_h\tau^h.
\tag{6.2}
$$

It has dimension $N=d+5$, and (1.2) realizes every point. For any predetermined $m$-read history, its observation map $F$ is smooth, with components

$$
F_i=(1+ki)\bigl((A_i)_{11}p+(A_i)_{12}r+(A_i)_{21}q+(A_i)_{22}qr/p\bigr)
+\sum_{h=0}^d\delta_hi^h.
$$

If $m<N$, let $\rho\le m<N$ be the greatest attained derivative rank. If $\rho=0$, integrate the zero derivative along segments in a small convex chart ball; $F$ is constant there and has a collision. Otherwise a nonzero maximal $\rho$-minor stays nonzero on a neighborhood, on which maximality makes the rank exactly $\rho$. Reorder inputs and outputs to place that minor first. The implicit function theorem makes the level set of the first $\rho$ outputs a smooth graph over a small connected open ball in $N-\rho>0$ remaining coordinates. Every remaining output differential is in the span of the first $\rho$ differentials, and vanishes on graph tangent vectors. Integration along paths makes all outputs constant on that graph. Distinct graph points are distinct actual targets with identical complete data. Thus fewer than $d+5$ reads cannot recover the target uniformly. A fixed list with early stopping can be padded along its predetermined continuation to its claimed limit, using empty words where needed; equal complete data give equal prefixes and stopping decisions. This argument does not apply to adaptive word selection.

Together with Theorem 2.1, this retains the credited equality

$$
C_{\mathrm{fix}}(d)=d+5\qquad(d\ge1).
\tag{6.3}
$$

For $d=0$ the same lower bound is five. Applying Theorem 2.1 with declared upper degree one to the constant-drift submodel gives six reads and returns its true entire constant polynomial. Thus

$$
5\le C_{\mathrm{fix}}(0)\le6.
\tag{6.4}
$$

This restriction of a six-read inverse does not prove a five-read inverse.

Let $A_*(d)$ denote the minimum total number of executed literal $M/J$ occurrences among recovering fixed histories with exactly $d+5$ reads. Theorem 2.1 gives $A_*(d)\le17$ for every $d\ge1$. The credited parity family has count $2w+2a-1$, where $a=d+3$ and $w$ is the smallest even integer at least $a$: its count is $4d+11$ for odd $d$ and $4d+13$ for even $d$. The other credited family has count $6d+9$. Both have fifteen at $d=1$ and exceed seventeen for $d\ge2$. Hence the new construction strictly improves these two counts for $d\ge2$, while the stronger credited bound $A_*(1)\le15$ remains. No unrestricted atom optimum or shortest-word claim follows.

For every uniquely recovered effective target, the complete original relation/gain fibre is exactly

$$
R=S/b,\qquad\alpha=b>0,\qquad\beta=bk,\qquad D\text{ fixed}.
\tag{6.5}
$$

Necessity follows from $S=\alpha R$ and $k=\beta/\alpha$. Conversely substitution preserves every observation, including future indices on any common history, and preserves positivity and rank one. For fixed $R=c_{\mathrm{col}}\ell$, all positive factorizations have precisely the internal scale freedom

$$
c'_{\mathrm{col}}=\mu c_{\mathrm{col}},\qquad\ell'=\ell/\mu,\qquad\mu>0.
$$

Equality of first columns forces this positive scalar, and equality of second columns forces the remaining row component. These are representation freedoms; they do not identify different effective targets.

## 7. Constant drift: the actual one-erasure obstruction

The rest of the volume concerns exactly five readings at $i=0,1,2,3,4$, with $D(\tau)=\delta$ constant. All histories and sources retain Section 1's contract.

**Lemma 7.1.** If there exists a noninitial position $j\in\{1,2,3,4\}$ whose deletion leaves a matrix span of dimension at most three, the history has an actual collision between distinct positive rank-one sources, with common slope $k=-1/j$ and common constant drift zero. Therefore uniform five-read recovery requires the four surviving matrices to be independent after every such deletion.

**Proof.** The survivors include $I$. Choose survivors $A,B$ so that $I,A,B$ span them, repeating $I$ if needed. There is a nonzero trace-zero matrix $X=(\begin{smallmatrix}a&b\\c&-a\end{smallmatrix})$ annihilating $A,B$ under the trace pairing: these are only two homogeneous equations in three unknowns. For $A=(\begin{smallmatrix}u&v\\w&x\end{smallmatrix})$ its equation is

$$
(u-x)a+wb+vc=0.
$$

If $a\ne0$ or $bc<0$, the four coefficients $a,-b,-c,-a$ have both strict signs. Otherwise $a=0$ and $bc\ge0$; orient $X$ so that $b,c\ge0$, not both zero. Nonnegativity makes $wb+vc=0$ force the appropriate off-diagonal entry of each selected matrix to vanish. Such a triangular nonnegative integral unimodular matrix has both diagonal entries one. Thus $\operatorname{diag}(1,-1)$ also annihilates $I,A,B$, and hence all survivors. Replace $X$ by this matrix. In either case we have a nonzero annihilator $X=(\begin{smallmatrix}a&b\\c&e\end{smallmatrix})$ for which $a,-b,-c,e$ contain both strict signs.

We construct positive rank-one endpoints with difference $X$. Define

$$
E(x,y)=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
f(x,y)=exy+a-cx-by,\qquad x,y>0.
$$

The function $f$ takes both signs: its values at $(\epsilon,\epsilon)$ tend to $a$; its values at $(T,T)$ divided by $T^2$ tend to $e$; its values at $(T,T^{-2})$ and $(T^{-2},T)$ divided by $T$ tend to $-c,-b$. Any strictly signed coefficient therefore supplies an actual point of its sign. Choose positive points with $f_-<0<f_+$ and join them by a positive straight segment. All entries of $E$ on this compact segment have a common lower bound $m>0$.

Put $\Delta=\det X$ and choose

$$
\lambda>\max\left\{\frac{\max_{a,b}|X_{ab}|}{m},
\frac{|\Delta|}{\min(-f_-,f_+)}\right\}.
$$

The intermediate value theorem gives a segment point with $f=-\Delta/\lambda$. At that point set $S_0=\lambda E$ and $S_1=S_0+X$. Both are strictly positive, $\det S_0=0$, and

$$
\det S_1=\lambda f+\Delta=0.
$$

Thus both are positive rank one and are distinct. All surviving traces agree because $X$ annihilates them. At $k=-1/j$ the remaining gain is zero, so all five observed readings agree with drift zero. Equations (1.2)–(1.4) realize each source on precisely the original words with a fixed positive row. ∎

## 8. A quotient bridge from sign changes to finite collisions

For a five-read history define linear maps on real $2\times2$ matrices by

$$
\mathcal L(X)_i=\operatorname{tr}(A_iX),\qquad
(\mathcal I v)_i=iv_i,\qquad
\mathcal Qv=(v_i-v_0)_{i=1}^4,
$$

$$
\mathsf B=\mathcal Q\mathcal L,\qquad
\mathsf C=\mathcal Q\mathcal I\mathcal L,\qquad
\mathsf T_k=\mathsf B+k\mathsf C.
\tag{8.1}
$$

The kernel of $\mathcal Q$ is exactly the constant vectors. Write

$$
\mathfrak b(X,Y)=\det(X+Y)-\det X-\det Y.
$$

For $S=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$,

$$
\mathfrak b(S,Y)=sY_{11}+pY_{22}-rY_{12}-qY_{21}.
\tag{8.2}
$$

**Lemma 8.1.** Suppose $\mathsf T_a$ is invertible and $\mathsf H=\mathsf T_a^{-1}\mathsf C$. If $\mathfrak b(S,\mathsf H S)$ takes both strict signs on positive rank-one sources, there are actual collisions with slopes $a,a+\epsilon$, for arbitrarily small $\epsilon>0$, and one entire constant drift per run.

**Proof.** Parameterize all positive rank-one sources as

$$
S=\sigma\begin{pmatrix}uv&u\\v&1\end{pmatrix},\qquad\sigma,u,v>0.
\tag{8.3}
$$

Connect two strictly signed sources by straight interpolation of their positive parameters. This is a compact positive rank-one path $S(\theta)$. Let $m>0$ bound all entries from below, put

$$
K=1+\max_{\theta,a,b}|(\mathsf H S(\theta))_{ab}|,
$$

and let $\eta>0$ be the smaller magnitude of the endpoint values of $\mathfrak b(S,\mathsf H S)$. Since $|\det(\mathsf H S)|\le2K^2$, choose

$$
0<\epsilon<\min\{m/(2K),\eta/(4K^2)\},
$$

with any additional prescribed positive upper bound. The entries of $S+\epsilon\mathsf H S$ remain positive. The continuous function

$$
\mathfrak b(S,\mathsf H S)+\epsilon\det(\mathsf H S)
$$

still has opposite endpoint signs and has a zero. At that zero set

$$
S_1=S,\qquad S_0=S+\epsilon\mathsf H S.
$$

The determinant identity

$$
\det(S+\epsilon\mathsf H S)
=\epsilon\mathfrak b(S,\mathsf H S)+\epsilon^2\det(\mathsf H S)
$$

makes $S_0$ rank one. Moreover

$$
\mathsf T_aS_0=\mathsf T_aS_1+\epsilon\mathsf C S_1
=\mathsf T_{a+\epsilon}S_1.
\tag{8.4}
$$

Thus the five-vector

$$
u_i=(1+ai)\operatorname{tr}(A_iS_0)
-(1+(a+\epsilon)i)\operatorname{tr}(A_iS_1)
$$

is constant, with value $u_0=\operatorname{tr}(S_0-S_1)$. Take the whole drifts

$$
D_0(\tau)=0,\qquad D_1(\tau)=u_0.
\tag{8.5}
$$

Every original reading then agrees, including the initial one. The slopes differ, so the targets differ even if their sources coincide. Equations (1.2)–(1.4) give the original positive factors, fixed rows, and positive unread states on the prescribed words. No gain was divided out. If $|a|<1/16$ and $0<\epsilon<1/16$, both slopes have magnitude less than $1/8$, so all gains at $i\le4$ are strictly positive. ∎

## 9. Necessary off-diagonal recorded-clock determinants

**Theorem 9.1.** Suppose a legal five-read history satisfies $(A_i)_{22}=1$ for every recorded position. Define five-vectors

$$
\mathbf1=(1,1,1,1,1)^{\mathsf T},\quad
\mathbf t=(0,1,2,3,4)^{\mathsf T},\quad
\mathbf x=((A_i)_{21})_{i=0}^4,\quad
\mathbf y=((A_i)_{12})_{i=0}^4,
$$

and coordinatewise products $\mathbf t\mathbf x=(i x_i)_i$, $\mathbf t\mathbf y=(i y_i)_i$. Uniform recovery of the complete constant-drift target requires

$$
\det[\mathbf1,\mathbf t,\mathbf x,\mathbf y,\mathbf t\mathbf x]=0,
\qquad
\det[\mathbf1,\mathbf t,\mathbf x,\mathbf y,\mathbf t\mathbf y]=0.
\tag{9.1}
$$

More precisely, assume deletion of every noninitial endpoint leaves four independent matrices. If either determinant in (9.1) is nonzero, there are actual different-slope collisions on the original five readings with both slopes arbitrarily close to zero and every sampled gain strictly positive. The mirror theorem holds when every $(A_i)_{11}=1$.

If $\mathbf1,\mathbf t,\mathbf x,\mathbf y$ are independent, (9.1) is equivalent to the six vectors $\mathbf1,\mathbf t,\mathbf x,\mathbf y,\mathbf t\mathbf x,\mathbf t\mathbf y$ spanning at most four dimensions. Without that extra independence, only the two determinant equalities are asserted.

**Proof.** First assume the erasure independence in the stronger statement. Let $K_0=E_{22}$. In (8.1),

$$
\mathsf B K_0=0,\qquad\mathsf C K_0=\mathbf e=(1,2,3,4)^{\mathsf T}.
$$

The full trace map $\mathcal L$ is injective, since the endpoints span four dimensions. If $\mathsf B X=0$, then $\mathcal L X$ is constant, and $\mathcal L K_0=\mathbf1$ makes injectivity imply $X\in\mathbb R K_0$. Thus

$$
\ker\mathsf B=\mathbb R K_0,\qquad\operatorname{rank}\mathsf B=3.
\tag{9.2}
$$

The pencil is regular. At $k=-1/j$, the equation $\mathsf T_kX=0$ says $(1-i/j)\operatorname{tr}(A_iX)$ is constant. Its value at $j$ is zero, so every value is zero. The four surviving gains are nonzero and their matrices independent, forcing $X=0$. Therefore $\mathsf T_{-1/j}$ is invertible. Its determinant is a nonzero polynomial in $k$; consequently $\mathsf T_a$ is invertible for every sufficiently small nonzero $a$.

Choose a nonzero left null covector $w$ of $\mathsf B$. The functional $h=w\mathsf C$ is nonzero: otherwise all ranges of $\mathsf B,\mathsf C$, hence of every $\mathsf T_k$, would lie in the three-dimensional space $\ker w$, contradicting regularity. At a positive rank-one source $S$, its determinant tangent space is

$$
V_S=\{V:\mathfrak b(S,V)=0\}.
$$

It is three-dimensional, and $\mathfrak b(S,K_0)=p>0$. Hence $K_0$ is not tangent, and $\mathsf B$ maps $V_S$ isomorphically onto its range. The quotient derivative at slope zero, $(V,\lambda)\mapsto\mathsf B V+\lambda\mathsf C S$, is therefore invertible exactly when $h(S)\ne0$. Such an interior source exists. Indeed, if $h$ vanished on every $S=(\begin{smallmatrix}uv&u\\v&1\end{smallmatrix})$, the polynomial $h_puv+h_qu+h_rv+h_s$ would vanish for every $u,v>0$. Applying the polynomial root bound successively in $u,v$ forces all four coefficients to vanish, a contradiction.

Use vectors

$$
\begin{aligned}
\mathbf a&=\mathsf B E_{12},&\mathbf b&=\mathsf B E_{21},&\mathbf c&=\mathsf B E_{11},\\
\mathbf A&=\mathsf C E_{12},&\mathbf B'&=\mathsf C E_{21},&\mathbf C'&=\mathsf C E_{11}.
\end{aligned}
$$

Here $\mathbf a,\mathbf b,\mathbf A,\mathbf B'$ are respectively the tails at $1,\ldots,4$ of $\mathbf x,\mathbf y,\mathbf t\mathbf x,\mathbf t\mathbf y$. At the source (8.3), the quotient observation is $\sigma F(u,v,k)$, where

$$
F=k\mathbf e+u(\mathbf a+k\mathbf A)
+v(\mathbf b+k\mathbf B')+uv(\mathbf c+k\mathbf C').
\tag{9.3}
$$

Its derivative determinant in order $(\sigma,u,v,k)$ is $\sigma^3 j(u,v,k)$, with

$$
j=\det[F,F_u,F_v,F_k].
$$

The preceding interior source gives $j(\bar u,\bar v,0)\ne0$ for some positive $\bar u,\bar v$. The source parameterization is a smooth chart with inverse $\sigma=s,u=q/s,v=r/s$, so it preserves derivative nonsingularity.

Two exact auxiliary boundary identities are

$$
j(u,0,k)=ku\det[\mathbf e,\mathbf a,
\mathbf b+k\mathbf B'+u(\mathbf c+k\mathbf C'),\mathbf A],
\tag{9.4}
$$

$$
j(0,v,k)=kv\det[\mathbf e,
\mathbf a+k\mathbf A+v(\mathbf c+k\mathbf C'),\mathbf b,\mathbf B'].
\tag{9.5}
$$

For (9.4), subtract $uF_u$ from the first determinant column, leaving $k\mathbf e$, and use $F_k=\mathbf e+u\mathbf A$; multilinearity gives the factor $ku$, and the second column's $k\mathbf A$ term vanishes against the last column. For (9.5), subtract $vF_v$, then use $F_k=\mathbf e+v\mathbf B'$. These are polynomial evaluations at an auxiliary boundary, not assertions that a zero-entry source is allowed.

Put

$$
d_x=\det[\mathbf e,\mathbf a,\mathbf b,\mathbf A],\qquad
d_y=\det[\mathbf e,\mathbf a,\mathbf b,\mathbf B'].
$$

If $d_x\ne0$, choose $u_*>0$ sufficiently small that

$$
u_*\det[\mathbf e,\mathbf a,\mathbf b+u_*\mathbf c,\mathbf A]
$$

is nonzero with the sign of $d_x$. Equation (9.4) shows that $j(u_*,0,k)$ has sign $\operatorname{sign}(kd_x)$ for all sufficiently small nonzero $k$. Choose the sign of an arbitrarily small nonzero $a$ so this is opposite to $j(\bar u,\bar v,0)$. Require also $\mathsf T_a$ invertible, $|a|<1/16$, and preservation of the interior sign at $a$. Regularity and continuity allow all these requirements. Finally take $v_*>0$ sufficiently small that $j(u_*,v_*,a)$ retains the boundary sign. These are two actual positive sources with opposite derivative signs at the same invertible slope. If $d_y\ne0$, (9.5) gives the same construction with $u,v$ exchanged.

At $\sigma=1$, with $\mathsf H=\mathsf T_a^{-1}\mathsf C$, the exact identity is

$$
j(u,v,a)=-\det(\mathsf T_a)\mathfrak b(S,\mathsf H S),
\qquad S=\begin{pmatrix}uv&u\\v&1\end{pmatrix}.
\tag{9.6}
$$

To check it, factor $\mathsf T_a$ out of the four derivative columns in (9.3), using $\mathsf C S=\mathsf T_a\mathsf H S$. In matrix-entry order $(p,q,r,s)$, direct expansion gives

$$
\det[S,S_u,S_v,X]=-\mathfrak b(S,X).
$$

Thus opposite $j$ signs give opposite strict transfer-form signs. Lemma 8.1 constructs the actual finite collision and its whole constant drifts. Both $a$ and $\epsilon$ can be arbitrarily small; its positive-gain bounds apply.

Since all of $t_0,x_0,y_0,(\mathbf t\mathbf x)_0,(\mathbf t\mathbf y)_0$ vanish, expansion in row zero gives

$$
\det[\mathbf1,\mathbf t,\mathbf x,\mathbf y,\mathbf t\mathbf x]=d_x,\qquad
\det[\mathbf1,\mathbf t,\mathbf x,\mathbf y,\mathbf t\mathbf y]=d_y.
$$

This proves the stronger collision statement. A recovering history must satisfy the erasure independence by Lemma 7.1, so it must satisfy (9.1).

For the mirror, replace $A_i,W_i$ by $JA_iJ,JW_iJ$. A conjugated letter is again a finite word ($J J J=J$ and $J M J$ is literal), so this is a legal history with the same indices. Conjugation exchanges the diagonal entries and the off-diagonal sequences. A collision on the conjugated history transfers back by $S_b=JS'_bJ$, $c_b=Jc'_b$, $\ell_b=\ell'_bJ$, leaving slopes and drifts unchanged. These are positive fixed factors and

$$
\operatorname{tr}((JA_iJ)S'_b)=\operatorname{tr}(A_iJS'_bJ).
$$

Thus all original readings agree without adding a conjugation acquisition. Finally, if the first four displayed five-vectors are independent, each extra determinant vanishes exactly when its last column lies in their span. This proves the stated rank interpretation. ∎

Here $E_{22}$ is a kernel direction of $\mathsf B$ at slope zero; it is not a common kernel of the pencil, since $\mathsf C E_{22}=\mathbf e\ne0$. The regularity proof is for constant drift and does not import an affine-drift common-kernel classification.

## 10. An infinite full-survivor-span family with positive-gain collisions

**Theorem 10.1.** For every integer $w\ge3$, the legal five-read history

$$
A_0=I,\qquad A_1=L,\qquad
A_2=Q_w=\begin{pmatrix}w&1\\w-1&1\end{pmatrix},
$$

$$
A_3=T_{3,w}=\begin{pmatrix}3w-1&3\\w&1\end{pmatrix},\qquad
A_4=T_{4,w}=\begin{pmatrix}4w-1&4\\w&1\end{pmatrix}
\tag{10.1}
$$

has distinct endpoints and four independent survivors after every noninitial deletion, yet has different-slope actual constant-drift collisions with both slopes arbitrarily close to zero and all sampled gains positive.

**Proof.** The successive left multipliers are

$$
L,\qquad UL^{w-2}=JML^{w-2},\qquad U^2J,\qquad U.
$$

Indeed $UL^{w-1}=Q_w$, $JQ_w=(\begin{smallmatrix}w-1&1\\w&1\end{smallmatrix})$, $U^2JQ_w=T_{3,w}$, and $UT_{3,w}=T_{4,w}$. The chronological blocks are $(J,M)$; then $w-2$ repetitions of $(J,M)$ followed by $(M,J)$; then $(J,M,J,M,J)$; then $(M,J)$. Their lengths are $2,2w-2,5,2$, totaling $2w+7$, with no interior reads. They occur at precisely the consecutive indices $0,\ldots,4$. Section 1 realizes all unread states positively with one fixed row.

The matrices $I,L,Q_w,T_{3,w}$ are independent. After subtracting $I$, their three nonconstant trace coefficient vectors on $(p,q,r)$ are

$$
(0,1,0),\qquad(w-1,w-1,1),\qquad(3w-2,w,3).
$$

Their determinant is nonzero, since its reduced two-by-two determinant is $3(w-1)-(3w-2)=-1$. The five matrices have the unique dependence up to scalar

$$
(w-3)I+(2-w)L+2Q_w-2T_{3,w}+T_{4,w}=0.
\tag{10.2}
$$

For the upper-right, lower-left, lower-right, and upper-left entries the corresponding sums are, respectively,

$$
2-6+4=0,\quad (2-w)+2(w-1)-2w+w=0,
$$

$$
(w-3)+(2-w)+2-2+1=0,
$$

$$
(w-3)+(2-w)+2w-2(3w-1)+(4w-1)=0.
$$

Every noninitial coefficient $2-w,2,-2,1$ is nonzero for $w\ge3$. A dependence on any four noninitial-deletion survivors would extend to a five-matrix dependence with that missing coefficient zero, contradicting uniqueness. At $w=3$ only the initial coefficient vanishes, which does not affect the claim. The upper-right entries are $0,0,1,3,4$ and $I\ne L$, so all endpoints are distinct.

Their off-diagonal vectors are

$$
\mathbf x=(0,1,w-1,w,w)^{\mathsf T},\qquad
\mathbf y=(0,0,1,3,4)^{\mathsf T}.
$$

The four vectors $\mathbf1,\mathbf t,\mathbf y,\mathbf t\mathbf y$ are independent. A zero combination with coefficients $\alpha,\beta,\gamma,\eta$ first gives $\alpha=\beta=0$ from indices zero and one. Indices two and three then give $\gamma+2\eta=0$ and $3\gamma+9\eta=0$, forcing both remaining coefficients zero. Their one-dimensional left nullspace contains

$$
\nu=(5,-12,12,-8,3)^{\mathsf T}.
$$

Explicitly its pairings with $\mathbf1,\mathbf t,\mathbf y,\mathbf t\mathbf y$ are

$$
5-12+12-8+3=0,\qquad -12+24-24+12=0,
$$

$$
12-24+12=0,\qquad24-72+48=0.
$$

In contrast,

$$
\nu\cdot\mathbf x=-12+12(w-1)-8w+3w=7w-24\ne0
$$

for integer $w$. Therefore $\mathbf1,\mathbf t,\mathbf x,\mathbf y,\mathbf t\mathbf y$ are independent and the second determinant in (9.1) is nonzero. Theorem 9.1 and Lemma 8.1 now supply a finite actual collision, not just a critical point.

In that construction the sources obey $S_0=S_1+\epsilon\mathsf T_a^{-1}\mathsf C S_1$, the slopes are $a,a+\epsilon$, and the whole drifts are $0,\operatorname{tr}(S_0-S_1)$. Equation (8.4) makes the difference of their undrifted signals exactly this same constant at all five original readings; (8.5) makes the observations identical. Choose $|a|<1/16$ and $0<\epsilon<1/16$ for strictly positive sampled gains. Both sources have (1.2)'s strictly positive factors, fixed in their respective runs, and (1.4) proves positivity throughout these precise words. Their slopes differ, beyond the representation fibre. ∎

At $w=4$ the endpoints are the credited six-read affine-drift construction with its repeated $Q$ read removed. The later indices become $3,4$, so its gain and drift equations must be evaluated at these indices. The constant-drift proof above checks this new recorded clock directly; deleting a read from an affine-drift inverse is not used as a recovery argument.

## 11. Credits and the exact remaining boundaries

The original recovery programme and *Shared affine gain and zero-crossing recovery* supply the common strictly positive rank-one model, counted initial read, fixed row, finite-word contract, effective target, positive scale fibre, and the all-fixed-history $d+5$ lower bound. Section 6 reproduces that bound with its actual-target chart and maximal-rank proof. The earlier nine-atom construction uses more reads and its calibration-prefix obstruction retains its prefix-specific scope.

*Sharp positive-degree recovery and six-read stability with affine gain* supplies the already established $C_{\mathrm{fix}}(d)=d+5$ for $d\ge1$, the fifteen-atom $d=1$ construction, the parity and $6d+9$ families, and the source-coordinate, determinant, exact midpoint, and cubic-inverse methods. Its credited component *Sharp six-read affine-drift recovery in the diagonal a=2 branch, with a global cubic inverse* supplies the six-read endpoints used for the $w=4$ comparison. Its stability results and conditional three-initial-lower-shear obstruction retain their own hypotheses; they are not premises for a constant-drift universal exclusion here.

The supplied candidate *Seventeen literal atoms suffice at the sharp d+5 read count for every positive drift degree* supplies the terminal-repetition endpoints, invariant, determinant, cubic, and degree-independent literal count proved in Sections 2–6. The supplied candidate *Two off-diagonal clock determinants obstruct regular five-read constant-drift histories* supplies the two determinants, boundary calculation, transfer collision, and infinite family proved in Sections 7–10. Its credited one-erasure positive-secant interface and constant-drift quotient/sign-transfer mechanism are proved here in the exact forms used. These are mathematical supplier credits, not independent approval or external priority claims. Embedded references to other supplier texts add no premises to these proofs.

The positive-degree contribution is a concrete seventeen-atom upper construction at the existing sharp read count, with a global inverse and a necessary-and-sufficient finite image criterion. It is not a new read lower bound, an unrestricted atom optimum, or an improvement over fifteen at $d=1$. Terminal padding explains how additional required reads can occur without additional executed atoms. It requires $d\ge1$: the absorbed gain signal is affine, and substitution of $d=0$ into its degree-$d$ interpolation argument is invalid.

The constant-drift contribution excludes the displayed infinite family even though it passes every noninitial one-erasure span test. More generally it supplies necessary determinants only in the stratum $(A_i)_{22}=1$ and its $(A_i)_{11}=1$ mirror. The stronger positive-gain collision theorem explicitly assumes four independent survivors after every noninitial deletion; histories failing that assumption already have Lemma 7.1's zero-gain collision. The determinant equalities are not sufficient for recovery. Histories with varying diagonal entries and histories satisfying both equalities remain unresolved by these results.

The unchanged original constant-drift optimum remains either five or six. There is no global five-read inverse and no collision theorem for every legal five-read history here. Classification of all read-optimal histories, determinant-zero cases, other endpoint strata, and unrestricted atom optima also remains open. The positive-degree theorem and the proper constant-drift obstruction are bounded progress, not completion of the all-degree programme.

All arguments are ordinary conditional exact-real textual mathematics. Literal atom counts are distinct from recorded reads. The conclusions do not establish adaptive lower bounds, numerical decoding stability, an off-image noise decoder, precision or bit/time bounds, physical acquisition or resource costs, general neural-network performance, empirical or Lean/kernel certification, or worldwide originality. Strict positivity, one rank-one common source, arbitrary real slope, one whole declared-degree drift per run, every original reading, positive unread states, and one unchanged row per run are retained throughout.

## 追加锚（本行以下为增补区）
