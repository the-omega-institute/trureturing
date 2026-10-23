# Sharp positive-degree recovery and six-read stability with affine gain

For every integer $d\ge1$, a predetermined forward history with $d+5$ exact scalar reads recovers one strictly positive rank-one effective source, an arbitrary real affine-gain slope, and the entire degree-at-most-$d$ additive drift. The all-fixed-history lower bound matches the construction, so $C_{\mathrm{fix}}(d)=d+5$ throughout this positive-degree range. The six-read member also has quantitative inverse bounds with explicit domains and actual-source counterexamples to unrestricted stability. A separate finite collision excludes the three-initial-lower-shear diagonal stratum under its stated rank hypothesis. The constant-drift endpoint remains $5\le C_{\mathrm{fix}}(0)\le6$ and is unresolved; this does not complete the original all-degree programme.

## 1. Model, actual realization, and target

Let

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
$$

A legal predetermined history has $A_0=I$ and $A_{i+1}=W_iA_i$, where each $W_i$ is a finite word in $M,J$, including the empty word. Matrices act on the left. A displayed product is executed from right to left; the chronological pair $(M,J)$ implements $U$, and $(J,M)$ implements $L$. The consecutive recorded indices are $i=0,1,\ldots$. Every scalar read advances this index, including a repeat after an empty word. Unread atoms do not advance it.

The effective source and observations are

$$
S=\begin{pmatrix}p&q\\r&s\end{pmatrix},\qquad
p,q,r,s>0,\qquad ps=qr,
$$

$$
z_i=(1+ki)\operatorname{tr}(A_iS)+D(i),\qquad
k\in\mathbb R,\qquad D(\tau)=\sum_{h=0}^d\delta_h\tau^h,\qquad d\ge0.
\tag{1.1}
$$

Let $C_{\mathrm{fix}}(d)$ be the smallest uniform exact-read bound over all legal predetermined finite-word histories that recover the whole target. The integer upper degree $d$ is known. Sections 2–6 and 8 specialize to $d=1$, so there $D(\tau)=\delta_0+\delta_1\tau$; Sections 9–10 treat every $d\ge1$, and Sections 11–15 concern stability of the six-read $d=1$ history. The target is exactly $(S,k,D)$, including the entire polynomial $D$. In original parameters $S=\alpha R$, $k=\beta/\alpha$, $\alpha>0$, and $R=c\ell$ with $c$ a strictly positive column and $\ell$ a strictly positive row fixed during its run. Negative gains, sampled gain zeros, zero drift, and constant drift are included. No reset, copy, inverse acquisition, instrument change, extra clock, independently lifted sources, or combination of unexecuted histories is permitted.

Every allowed effective source has the actual realization

$$
\alpha=1,\qquad \beta=k,\qquad R=S,\qquad
c=\binom p r,\qquad \ell=(1,q/p).
\tag{1.2}
$$

Indeed $rq/p=s$, so $c\ell=S$. For any $A=(\begin{smallmatrix}a&b\\c_0&e\end{smallmatrix})$,

$$
\ell Ac=\operatorname{tr}(AS)=ap+br+c_0q+es.
\tag{1.3}
$$

At every atom the positive column stays positive:

$$
M\binom{x}{y}=\binom{y}{x+y},\qquad
J\binom{x}{y}=\binom{y}{x}\qquad(x,y>0).
\tag{1.4}
$$

Thus (1.2) supplies one source and one unchanged row at all recorded and unread states on any prescribed legal history. Different candidate runs may have different fixed rows. Every cumulative word matrix is nonnegative integral with determinant $1$ or $-1$, because both atoms have these properties and the empty word is $I$.

## 2. The attaining six-read history

**Theorem 2.1.** The cumulative matrices

$$
A_0=I,\quad A_1=L,\quad A_2=Q,\quad A_3=Q,\quad
A_4=T_3,\quad A_5=T_4,
\tag{2.1}
$$

where

$$
Q=\begin{pmatrix}4&1\\3&1\end{pmatrix},\qquad
T_3=\begin{pmatrix}11&3\\4&1\end{pmatrix},\qquad
T_4=\begin{pmatrix}15&4\\4&1\end{pmatrix},
$$

recover the complete $d=1$ target in (1.1) for every allowed source, every real $k$, and every affine $D$. A literal realization uses fifteen atoms.

The left multipliers between the six reads are, in order,

$$
L,\qquad UL^2,\qquad I,\qquad U^2J,\qquad U.
\tag{2.2}
$$

Their chronological atom lists are

$$
(J,M),\quad(J,M,J,M,M,J),\quad\varnothing,
\quad(J,M,J,M,J),\quad(M,J).
$$

The lengths are $2,6,0,5,2$, totaling fifteen. Multiplication gives

$$
Q=UL^3,\qquad
JQ=\begin{pmatrix}3&1\\4&1\end{pmatrix},\qquad
T_3=U^2JQ,\qquad T_4=UT_3.
$$

This proves legality at the actual indices $0,\ldots,5$. There is no read inside any displayed word. Equations (1.2)–(1.4) realize the entire history with a positive source and a fixed positive row. The recovery and uniqueness proof follows in Sections 3–5.

## 3. Source coordinates and exact data reduction

Write $a=p+s$ and introduce three linear source coordinates

$$
u=3p+3q+r,\qquad t=4p+r,\qquad v=q-p.
\tag{3.1}
$$

Their inverse is

$$
p=\frac{u-t-3v}{2},\qquad
q=\frac{u-t-v}{2},\qquad
r=3t+6v-2u.
\tag{3.2}
$$

For example $u-t-3v=2p$; substituting into the other two formulas returns $q,r$. These formulas are a linear isomorphism of three-dimensional real spaces. The positive rank-one domain is exactly $p,q,r>0$, with $s=qr/p$. In particular $u>0$. For fixed $u$, the allowed pairs $(t,v)$ form the intersection of the three open affine half-planes in (3.2). This domain is convex. Convexity here concerns the coordinates $(p,q,r)$, with $s$ reconstructed by $qr/p$.

Set

$$
\zeta=a+\delta_0,\qquad
\eta=\delta_1+k(a+u).
\tag{3.3}
$$

The traces on the recorded history are

$$
\operatorname{tr}(LS)=a+q,\qquad
\operatorname{tr}(QS)=a+u,
$$

$$
\operatorname{tr}(T_3S)=a+u+2t+v,\qquad
\operatorname{tr}(T_4S)=a+u+3t+v.
$$

Expanding (1.1) at its six actual indices gives exactly

$$
\begin{aligned}
z_0&=\zeta,\\
z_1&=\zeta+\eta+q+k(q-u),\\
z_2&=\zeta+u+2\eta,\\
z_3&=\zeta+u+3\eta,\\
z_4&=\zeta+u+4\eta+(1+4k)(2t+v),\\
z_5&=\zeta+u+5\eta+(1+5k)(3t+v).
\end{aligned}
\tag{3.4}
$$

Consequently data determine

$$
\begin{aligned}
\zeta&=z_0,&\eta&=z_3-z_2,&u&=z_2-\zeta-2\eta,\\
E&=z_1-\zeta-\eta,&W&=u-2E,\\
Y&=z_4-\zeta-u-4\eta,&Z&=z_5-\zeta-u-5\eta.
\end{aligned}
\tag{3.5}
$$

This is an invertible linear change of all six data coordinates to $(\zeta,\eta,u,W,Y,Z)$. Its inverse is

$$
\begin{aligned}
z_0&=\zeta,&z_1&=\zeta+\eta+(u-W)/2,\\
z_2&=\zeta+u+2\eta,&z_3&=\zeta+u+3\eta,\\
z_4&=\zeta+u+4\eta+Y,&z_5&=\zeta+u+5\eta+Z.
\end{aligned}
$$

Since $u-2q=t+v$, the remaining source and slope equations are

$$
(W,Y,Z)=F_u(t,v,k),
$$

$$
F_u(t,v,k)=
\bigl((1+k)(t+v)+ku,\ (1+4k)(2t+v),\ (1+5k)(3t+v)\bigr).
\tag{3.6}
$$

After recovering $t,v,k$, the entire original drift is

$$
D(\tau)=\zeta-a+[\eta-k(a+u)]\tau,
\qquad a=p+qr/p.
\tag{3.7}
$$

All identities so far hold without dividing by any gain. Equations (3.1)–(3.6) also hold for an arbitrary full real matrix if $s$ is left free; rank one is imposed only when reconstructing the actual source.

## 4. A signed derivative and a global midpoint proof

At fixed $u$, the derivative of $F_u$ in the order $(t,v,k)$ is

$$
DF_u=
\begin{pmatrix}
1+k&1+k&t+v+u\\
2(1+4k)&1+4k&4(2t+v)\\
3(1+5k)&1+5k&5(3t+v)
\end{pmatrix}.
$$

Put $g_j=1+jk$. Expansion along the last column yields

$$
\begin{aligned}
\mathcal J:=\det DF_u
&=-(t+v+u)g_4g_5+8(2t+v)g_1g_5-5(3t+v)g_1g_4\\
&=(2v-u)+(12t+14v-9u)k-20uk^2.
\end{aligned}
\tag{4.1}
$$

Substitution from (3.1) gives the decisive identity

$$
-\mathcal J
=p(60k^2-7k+5)+q(60k^2+13k+1)+r(20k^2-3k+1).
\tag{4.2}
$$

Every bracket is strictly positive at every real $k$:

$$
\begin{aligned}
60k^2-7k+5&=60(k-7/120)^2+1151/240,\\
60k^2+13k+1&=60(k+13/120)^2+71/240,\\
20k^2-3k+1&=20(k-3/40)^2+71/80.
\end{aligned}
$$

Thus $\mathcal J<0$ on the entire positive source domain for every real slope.

For completeness, the following exact identity supplies global injectivity. Write $y=(t,v)^{\mathsf T}$. At fixed $u$, (3.6) has the form

$$
F_u(y,k)=Ay+kBy+ku e_1
$$

for fixed real matrices $A,B$ and $e_1=(1,0,0)^{\mathsf T}$. For two points set $\bar y=(y_0+y_1)/2$, $\bar k=(k_0+k_1)/2$. Expansion gives

$$
k_0y_0-k_1y_1=\bar k(y_0-y_1)+\bar y(k_0-k_1),
$$

and therefore

$$
F_u(y_0,k_0)-F_u(y_1,k_1)
=DF_u(\bar y,\bar k)
\begin{pmatrix}t_0-t_1\\v_0-v_1\\k_0-k_1\end{pmatrix}.
\tag{4.3}
$$

If both endpoints have positive $p,q,r$, (3.2) makes the midpoint's $p,q,r$ their positive arithmetic means. Hence the derivative in (4.3) is invertible by (4.2). Equal values force $t_0=t_1$, $v_0=v_1$, $k_0=k_1$.

Two actual targets giving identical six data first have the same $\zeta,\eta,u,W,Y,Z$ by (3.5). Equation (4.3) then makes their $t,v,k$ identical; (3.2), $s=qr/p$, and (3.7) make their entire targets identical. The midpoint source uses $s=qr/p$ at its own coordinates, so it remains in the declared source family. This establishes global recovery in Theorem 2.1.

## 5. Finite cubic inverse and exact common-source compatibility

**Proposition 5.1.** Arbitrary real data $z_0,\ldots,z_5$ on (2.1) have a realization in (1.1) exactly when the following procedure has a passing candidate. If one passes, it is the unique effective target.

First form (3.5) and require $u>0$. Define

$$
\begin{aligned}
H(k)={}&-(W-ku)(1+4k)(1+5k)\\
&+2Y(1+k)(1+5k)-Z(1+k)(1+4k).
\end{aligned}
\tag{5.1}
$$

Its leading coefficient is $20u>0$, so it is a nonzero cubic. Consider its distinct real roots, counting a repeated root once. This is a finite exact algebraic prescription. A nonzero cubic has at most three distinct roots: at any root polynomial division removes a linear factor, and every other distinct root remains a root of the quotient. It has at least one real root by its opposite limits at the two ends of the real line and continuity.

For each root define

$$
P_k=\begin{pmatrix}
1+k&1+k\\
2(1+4k)&1+4k\\
3(1+5k)&1+5k
\end{pmatrix},\qquad
b_k=\begin{pmatrix}W-ku\\Y\\Z\end{pmatrix}.
\tag{5.2}
$$

Label these rows by $n=1,2,3$, with associated clock indices $j_1=1$, $j_2=4$, $j_3=5$. At least two gains $1+j_nk$ are nonzero, since the affine gain has intercept one and at most one root. Any two surviving rows have determinant

$$
(1+j_nk)(1+j_mk)(n-m)\ne0\qquad(n\ne m).
$$

Thus $P_k$ has rank two for every real $k$. Expanding a three-by-three determinant gives

$$
H(k)=\det_3[P_k^{(1)},P_k^{(2)},b_k],
\tag{5.3}
$$

where the superscripts denote columns. Since the first two columns are independent, $H(k)=0$ is exactly $b_k\in\operatorname{range}P_k$, including the equation of any erased row.

Choose any two surviving row labels $n<m$. Define only their corresponding quotients from

$$
V_1=\frac{W-ku}{1+k},\qquad
V_2=\frac{Y}{1+4k},\qquad
V_3=\frac{Z}{1+5k},
$$

and set

$$
t=\frac{V_m-V_n}{m-n},\qquad v=V_n-nt.
\tag{5.4}
$$

Their denominators are selected nonzero gains and a positive integer. The third row is satisfied by (5.3), whether or not its gain vanishes. Form (3.2) and require $p,q,r>0$. Then form

$$
s=qr/p,\qquad S=\begin{pmatrix}p&q\\r&s\end{pmatrix},
$$

and the whole affine $D$ in (3.7). Require every original observation equation (1.1) at all six matrices in (2.1).

**Proof.** For actual data $u>0$, the true slope satisfies (5.1) by (3.6) and (5.3). Rank two of $P_k$ makes (5.4) return the true $t,v$; all positivity and original equations hold, and (3.7) returns the entire original drift. Thus a candidate passes for every actual target.

Conversely a passing candidate has strictly positive entries and $ps=qr$. Its one affine polynomial meets the declared bound. Use the original parameters and positive factors (1.2) on exactly the words (2.2). Equations (1.3)–(1.4) realize all positive read and unread states with a fixed row, and the checked six equations realize the proposed data. Thus compatibility is sufficient in the original common-source model. Section 4 excludes two passing targets. ∎

All degeneracies are covered. The branch $k=0$ is included in the cubic. The repeated $Q$ observations use the linear formulas (3.5) even when their gains vanish at $k=-1/2$ or $-1/3$. At $k=-1$, $-1/4$, or $-1/5$, exactly one row of (5.2) is erased; the other two determine $t,v$, and (5.3) retains the erased right-hand-side equation. Gain at index zero is one. Negative slopes, negative gains, zero or negative readings, repeated cubic roots, and zero drift coefficients require no further restriction. No leading gain coefficient or prescribed gain sample is a compulsory divisor. Apart from the fixed integer divisions and selected surviving gains, source reconstruction divides only by $p>0$.

## 6. Common safe kernel, scales, and the mirrored construction

For any six-read history define $\mathcal L(X)_i=\operatorname{tr}(A_iX)$, $(\mathcal I v)_i=iv_i$, and

$$
(\Lambda v)_j=v_j-2v_{j+1}+v_{j+2}\quad(j=0,1,2,3),
\qquad \mathcal T_k=\Lambda(\operatorname{Id}+k\mathcal I)\mathcal L.
\tag{6.1}
$$

The rows of $\Lambda$ are independent: in a nonzero combination, the largest row index has a last nonzero coordinate absent from all earlier rows. They kill affine evaluation vectors. Their kernel has dimension two, so it is exactly evaluation of affine polynomials at $0,\ldots,5$; that evaluation space has dimension two because its values at $0,1$ determine the polynomial.

All endpoints in (2.1) have lower-right entry one. Thus $E_{22}$, the matrix with only its lower-right entry equal to one, obeys

$$
\operatorname{tr}(A_iE_{22})=\operatorname{tr}E_{22}=1,\qquad
\mathcal T_kE_{22}=0.
$$

It is safe in the cone

$$
\mathcal K_{\mathrm{safe}}=
\left\{\begin{pmatrix}a&b\\c&e\end{pmatrix}:
 a,e\ge0,\ b,c\le0\right\}.
$$

To establish the exact kernel, allow any full real matrix $X=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$ and an affine compensating drift, at a prescribed real $k$. Equations (3.1)–(3.6) still hold without positivity or rank one. If the six observations vanish, (3.5) gives
$\zeta=\eta=u=W=Y=Z=0$. Rank two in (5.2) then gives $t=v=0$, and (3.2) gives $p=q=r=0$. The remaining $s$ is free, and the drift is $-s(1+k\tau)$. Conversely that matrix and drift cancel every reading. The exact affine quotient in (6.1) therefore gives

$$
\ker\mathcal T_k=\mathbb RE_{22},\qquad
\operatorname{rank}\mathcal T_k=3\qquad(k\in\mathbb R).
\tag{6.2}
$$

This places the construction in the diagonal common-safe-kernel stratum. There are two initial lower-shear reads $I,L$, two $Q$ reads, and final parameters $3,4$. Neither $M$ nor $JMJ$ is recorded. The legality, rank, and global inverse above are established directly, without needing that normal form as a recovery sufficiency theorem.

For compatible data the entire original relation/gain fibre is exactly

$$
R=S/b,\qquad \alpha=b>0,\qquad \beta=bk,\qquad D\text{ fixed}.
\tag{6.3}
$$

The equations $S=\alpha R$, $k=\beta/\alpha$ force this form. Conversely substitution gives $(b+bki)\operatorname{tr}(A_iS/b)=(1+ki)\operatorname{tr}(A_iS)$ for every recorded or future index. Global recovery leaves no further effective-target ambiguity. A fixed relation's positive factorizations have exactly the internal freedom $c'=\mu c$, $\ell'=\ell/\mu$, $\mu>0$: equality of first columns forces this positive scalar, and equality of second columns forces the remaining row component. This internal scale leaves $R$ itself unchanged.

There is also a recovering mirror history obtained by replacing each $A_i$ and multiplier $W_i$ by $JA_iJ$ and $JW_iJ$. The latter is again a finite $M/J$ word, including the empty word. Its six matrices are

$$
I,\quad U,\quad
\begin{pmatrix}1&3\\1&4\end{pmatrix},\quad
\begin{pmatrix}1&3\\1&4\end{pmatrix},\quad
\begin{pmatrix}1&4\\3&11\end{pmatrix},\quad
\begin{pmatrix}1&4\\4&15\end{pmatrix}.
$$

For a source $S'$ on this mirror, $S=JS'J$ gives
$\operatorname{tr}((JA_iJ)S')=\operatorname{tr}(A_iS)$. Apply the inverse already proved and conjugate the recovered source back, leaving $k,D$ unchanged. Positive factors transform as $Jc$ and $\ell J$ and remain fixed during their run. The common safe kernel becomes $E_{11}$. This is a correspondence of legal histories and actual sources. It requires no added conjugation acquisition. The fifteen-atom count belongs to (2.2); it is not an asserted optimal atom count.

## 7. The matching all-fixed-history lower bound

The following is the actual-target lower-bound argument of [Shared affine gain and zero-crossing recovery](FIB_SHARED_AFFINE_GAIN_ZERO_CROSSING_RECOVERY.md), Theorem 5.1, reproduced with the parameter correspondence explicit.

For general known $d\ge0$, use the injective chart

$$
(p,q,r,k,\delta_0,\ldots,\delta_d)
\in(0,\infty)^3\times\mathbb R^{d+2},
$$

$$
S=\begin{pmatrix}p&q\\r&qr/p\end{pmatrix},\qquad
D(\tau)=\sum_{h=0}^d\delta_h\tau^h.
\tag{7.1}
$$

Its dimension is $N=d+5$. Every chart point has the actual positive realization (1.2) on any legal history. For any predetermined $m$-read cumulative history, the observation map $F$ on this open chart has smooth components

$$
F_i=(1+ki)\left((A_i)_{11}p+(A_i)_{12}r
 +(A_i)_{21}q+(A_i)_{22}\frac{qr}{p}\right)
 +\sum_{h=0}^d\delta_hi^h.
$$

Suppose $m<N$ and let $\rho$ be its largest attained derivative rank. Then $\rho\le m<N$. If $\rho=0$, integrate the zero derivative along line segments in a small convex ball to obtain distinct chart points with identical outputs. If $\rho>0$, choose a nonzero maximal $\rho$-minor. On a sufficiently small neighborhood it stays nonzero, while maximality makes the total rank exactly $\rho$. Reorder coordinates and outputs so this is the first $\rho$ input coordinates and output components. The implicit function theorem makes the level set of those components a smooth graph over a small open ball in the remaining $N-\rho>0$ coordinates.

At each graph point, every other output differential is in the span of the first $\rho$ differentials, since those rows are independent and the total rank is $\rho$. It therefore vanishes on the graph's tangent vectors. Integrating along paths in the connected graph patch makes every output constant there. Distinct chart points in that patch are distinct actual targets with the same observations. Thus $m<d+5$ cannot recover the entire target uniformly.

A predetermined word list with earlier stopping can be extended by empty-word reads to its uniform bound. Identical full padded observations give identical prefixes and stopping decisions, so the collision remains. This is an all-fixed-history lower bound under the finite-word contract. At $d=1$ its chart is precisely the six-dimensional target of (1.1), and it excludes every bound below six. Theorem 2.1 attains six on that same target, proving

$$
\boxed{C_{\mathrm{fix}}(1)=6}.
\tag{7.2}
$$

## 8. Complete obstruction for three initial lower-shear reads

The notation $a=3$ below means the number of initial recorded endpoints whose upper-right entry is zero, including the initial read. It is independent of the source trace $a$ used earlier.

**Theorem 8.1.** Consider any legal six-read history with

$$
A_0=I,\qquad A_1=D_{h_1},\qquad A_2=D_{h_2},\qquad
D_h=L^h=\begin{pmatrix}1&0\\h&1\end{pmatrix},
\qquad 0\le h_1\le h_2,
$$

$$
A_i=\begin{pmatrix}u_i&v_i\\w_i&1\end{pmatrix},\qquad
v_i>0\quad(i=3,4,5).
\tag{8.1}
$$

Assume that $\mathcal T_k$ in (6.1) has rank three and kernel $\mathbb RE_{22}$ for every real $k$. Then two actual targets with strictly positive rank-one sources, different real slopes, and one whole affine drift per run have identical six observations on this very history. The mirror statement holds with $E_{11}$ and three initial upper-shear reads.

This covers every $a=3$ member of the diagonal $E_{22}$ normal form satisfying its all-real-slope rank hypothesis. It permits repeated initial shears, either determinant sign at legal endpoints, any permitted pair phase or its absence, and any permitted final repetition. No additional normal-form restriction on the three tail matrices is used in the proof.

**Proof.** First verify the interface with the legal stratum. If an endpoint has lower-right entry one and upper-right entry zero, nonnegative integrality and determinant $\pm1$ force it to be $D_h$ for an integer $h\ge0$. Between two such endpoints the actual multiplier is, algebraically, $D_gD_h^{-1}=L^{g-h}$; nonnegativity forces $g\ge h$. Once an endpoint has upper-right entry $v>0$, a later upper-right entry cannot be zero: it is $V_{11}v+V_{12}$ for a nonnegative invertible multiplier $V$, whose first row is nonzero. Thus the three-initial-zero-entry case has precisely (8.1), including all its allowed repetitions. Inverses in this interface merely identify an already existing multiplier.

Write $x=(p,q,r)^{\mathsf T}>0$, $s=qr/p$, and $a_S=p+s$. Set

$$
f_i(x)=(u_i-1)p+w_iq+v_ir,
$$

using $f_0=0$, $f_1=h_1q$, $f_2=h_2q$ for the initial shears. Absorb the source trace into the one affine polynomial

$$
P(\tau)=D(\tau)+a_S(1+k\tau).
$$

Then the original observations are $z_i=(1+ki)f_i(x)+P(i)$. Eliminate this polynomial using

$$
z_i-z_0-i(z_1-z_0)\qquad(i=2,3,4,5).
$$

The resulting four-vector is $G(x,k)=\mathcal M(k)x$, where row $i$ is

$$
(1+ki)(u_i-1,w_i,v_i)-i(1+k)(0,h_1,0).
\tag{8.2}
$$

In particular its first row, indexed by $i=2$, is $(0,\lambda(k),0)$, with

$$
\lambda(k)=h_2-2h_1+2k(h_2-h_1).
\tag{8.3}
$$

The elimination map has exactly affine evaluation as its kernel: its zero vectors are $z_i=z_0+i(z_1-z_0)$. The source trace direction is $E_{22}$ and is absorbed by $P$. Hence (8.2) has the same remaining matrix kernel as the quotient in (6.1). The hypothesis gives

$$
\operatorname{rank}\mathcal M(k)=3\qquad(k\in\mathbb R).
\tag{8.4}
$$

On the three actual tail indices define

$$
\mathbf a=(u_i-1)_{i=3}^5,\qquad
\mathbf c=(v_i)_{i=3}^5,\qquad
\mathsf D=\operatorname{diag}(3,4,5).
$$

The two vectors $\mathbf a,\mathbf c$ are independent. Otherwise the $p,r$ columns of (8.2) would be dependent at every slope, contrary to (8.4). All entries of $\mathbf c$ are strictly positive. The plane $V=\operatorname{span}(\mathbf a,\mathbf c)$ is not invariant under $\mathsf D$: invariance would put $\mathbf c,\mathsf D\mathbf c,\mathsf D^2\mathbf c$ in a two-dimensional plane. A relation between these three vectors, divided coordinatewise by $v_i>0$, would give a polynomial of degree at most two vanishing at the three distinct nodes $3,4,5$. Successive factorization at its roots makes it zero, so these vectors are independent, a contradiction.

At the boundary $q=0$, consider the four-by-four derivative determinant of $G$ in the order $(p,q,r,k)$. Its first row is $(0,\lambda,0,0)$, so

$$
\mathcal J(k;p,0,r)=-\lambda(k)H(k;p,r),
\tag{8.5}
$$

$$
H(k;p,r)=\det_3\bigl[
(\operatorname{Id}+k\mathsf D)\mathbf a,
(\operatorname{Id}+k\mathsf D)\mathbf c,
\mathsf D(p\mathbf a+r\mathbf c)\bigr].
\tag{8.6}
$$

This boundary is only an auxiliary polynomial calculation. Positive actual sources will be constructed below. The function $H$ is affine in $k$ because its quadratic coefficient is

$$
\det_3[\mathsf D\mathbf a,\mathsf D\mathbf c,
 p\mathsf D\mathbf a+r\mathsf D\mathbf c]=0.
$$

If $h_2>h_1$, the affine $\lambda$ has a simple real root $k_0$. At $k_0$, (8.4) and the zero first row make the three tail rows of $\mathcal M(k_0)$ invertible. In particular the first two columns in (8.6) are independent. The linear functional $H(k_0;p,r)$ is nonzero. To see this, suppose it were zero for every $p,r$. Both $\mathsf D\mathbf a$ and $\mathsf D\mathbf c$ would belong to the plane $W$ spanned by those first two columns. Subtracting $k_0$ times these vectors would place $\mathbf a,\mathbf c$ in $W$ too. Independence and dimension two would then give $V=W=\mathsf DV$, contradicting the preceding noninvariance. Choose $p,r>0$ with $H(k_0;p,r)\ne0$. Equation (8.5) then has a simple root at $k_0$.

If $h_2=h_1=h$, the value $h=0$ is impossible: at $k=-1/3$ the first row and tail row $i=3$ of (8.2) would both vanish, giving rank at most two. Thus $h>0$ and $\lambda=-h$ is constant nonzero. The coefficient of $k$ in (8.6) is

$$
p\det_3[\mathbf a,\mathsf D\mathbf c,\mathsf D\mathbf a]
+r\det_3[\mathsf D\mathbf a,\mathbf c,\mathsf D\mathbf c].
\tag{8.7}
$$

Its two coefficients cannot both vanish. The vectors $\mathsf D\mathbf a,\mathsf D\mathbf c$ are independent, since $\mathsf D$ is invertible. If both coefficients vanished, $\mathbf a,\mathbf c$ would lie in their plane, again giving $V=\mathsf DV$. Choose $p,r>0$ where (8.7) is nonzero. The affine $H$ has a simple real root, and so does (8.5).

The choices of positive $p,r$ in both cases are explicit in the following symbolic sense. For a nonzero linear functional use $(p,r)=(1,1)$ if its value is nonzero; otherwise replace one coordinate with nonzero coefficient by $2$. The resulting value is that coefficient. Any division used to name a root of a nonconstant affine polynomial therefore has nonzero denominator.

In either case choose two slopes on opposite sides of the simple boundary root, sufficiently close that (8.5) has opposite strict signs at them. At these two fixed slopes continuity preserves those signs for every sufficiently small $q>0$. Fix such a $q$. The intermediate value theorem in $k$ gives a real $b$ with

$$
\mathcal J(b;p,q,r)=0,
\qquad x=(p,q,r)^{\mathsf T}>0.
\tag{8.8}
$$

By (8.4), the first three columns of that derivative, namely $\mathcal M(b)$, are independent. Its last column $\mathbf b=\mathcal M'(b)x$ consequently lies in their range. There is a unique real vector $X$ such that

$$
\mathcal M(b)X=\mathcal M'(b)x.
\tag{8.9}
$$

It can be obtained by any nonzero three-row minor of $\mathcal M(b)$; that determinant is a justified nonzero divisor, and (8.8) supplies the remaining row equation. Choose any nonzero real $\epsilon$ satisfying

$$
|\epsilon|<\min_{j=1,2,3}\frac{x_j}{2(1+|X_j|)}.
\tag{8.10}
$$

Use the two source coordinates and slopes

$$
x_0=x+\epsilon X,\qquad k_0=b,\qquad
x_1=x,\qquad k_1=b+\epsilon.
$$

Each coordinate of $x_0$ exceeds half the corresponding positive coordinate of $x$. Affineness of $\mathcal M$ in $k$ gives the exact finite identity

$$
\mathcal M(k_0)x_0
=\mathcal M(b)x+\epsilon\mathcal M'(b)x
=\mathcal M(b+\epsilon)x_1
=\mathcal M(k_1)x_1.
\tag{8.11}
$$

For each run $j=0,1$, write $x_j=(p_j,q_j,r_j)^{\mathsf T}$, set

$$
s_j=q_jr_j/p_j,\qquad
S_j=\begin{pmatrix}p_j&q_j\\r_j&s_j\end{pmatrix},\qquad
a_j=p_j+s_j,
$$

and take the one entire affine drift

$$
D_j(\tau)=-a_j(1+k_j\tau)-(1+k_j)h_1q_j\tau.
\tag{8.12}
$$

Both sources are strictly positive of rank one, with divisor $p_j>0$. Direct substitution in the original equations gives $z_0=z_1=0$ in each run. At every actual index $i=2,3,4,5$ it gives row $i$ of $\mathcal M(k_j)x_j$. Equation (8.11) makes these four observations identical. This verifies all six original equations, including every zero or negative gain, with one whole drift per run.

Finally use $\alpha_j=1$, $\beta_j=k_j$, $R_j=S_j$, and the fixed factors

$$
c_j=\binom{p_j}{r_j},\qquad \ell_j=(1,q_j/p_j).
$$

Their product is $S_j$, and (1.3)–(1.4) realize precisely the originally prescribed words with positive read and unread states. Their slopes differ by $\epsilon\ne0$, so their effective targets differ even if their sources happen to coincide. Equations (8.11)–(8.12) provide a finite actual-source collision. The derivative zero in (8.8) was used to construct that identity.

For $E_{11}$, conjugate the given history by $J$, apply the preceding proof, and realize it on the original words using $S_j=JS'_jJ$, $c_j=Jc'_j$, $\ell_j=\ell'_jJ$ with unchanged $k_j,D_j$. These factors are positive and fixed in their run, and the traces agree at the original six indices. This proves the mirror statement. ∎

## 9. Sharp recovery for every positive upper degree

**Theorem 9.1.** For every integer $d\ge1$, put

$$
a=d+3,\qquad b=a+1,\qquad m=a-2,
$$

and choose the smallest even integer $w\ge a$. Thus $w=a$ for even $a$ and $w=a+1$ for odd $a$. Set $h=(w-2)/2$. Define

$$
Q_w=UL^{w-1}=\begin{pmatrix}w&1\\w-1&1\end{pmatrix},\qquad
T_\nu=U^{\nu-1}JQ_w=\begin{pmatrix}\nu w-1&\nu\\w&1\end{pmatrix}.
$$

The $d+5$ consecutive recorded endpoints

$$
A_0=I,\quad A_1=L^h,\quad
A_i=Q_w\ (2\le i\le d+2),\quad
A_a=T_{a-1},\quad A_b=T_a
\tag{9.1}
$$

recover exactly $(S,k,D)$ for all sources in (1.1), all real $k$, and every whole polynomial $D$ of degree at most $d$. A literal implementation uses $2w+2a-1$ atoms.

**Legal realization.** Powers of the shears are

$$
U^j=\begin{pmatrix}1&j\\0&1\end{pmatrix},\qquad
L^j=\begin{pmatrix}1&0\\j&1\end{pmatrix}\quad(j\ge0).
$$

The successive nonempty multipliers are

$$
L^h,\quad UL^{w-1-h},\quad U^{a-2}J,\quad U,
\tag{9.2}
$$

with $d$ empty words between the $d+1$ consecutive $Q_w$ reads. In particular $w-1-h=w/2\ge0$. Chronologically $L$ is $(J,M)$, $U$ is $(M,J)$, and $U^{a-2}J$ is one $J$ followed by $a-2$ pairs $(M,J)$. Their lengths are $2h$, $2+2(w-1-h)$, $1+2(a-2)$, and $2$, giving the stated total. There is no interior read in any word. Equations (1.2)–(1.4) realize these exact words with one positive source, one unchanged row, and positive unread states.

**Coordinates and polynomial reduction.** Write $a_S=p+s$ and set

$$
u=(w-1)(p+q)+r,\qquad t=wp+r,\qquad v=q-p.
\tag{9.3}
$$

The exact linear inverse is

$$
p=\frac{u-t-(w-1)v}{w-2},\qquad
q=\frac{u-t-v}{w-2},\qquad r=t-wp.
\tag{9.4}
$$

Indeed $u-t=-p+(w-1)q=(w-2)p+(w-1)v$. The fixed divisor $w-2$ is positive. Positivity means exactly that these three expressions are positive, followed by $s=qr/p$. Thus $u>0$ and the fixed-$u$ domain of $(t,v)$ is convex.

Direct trace expansion gives

$$
\operatorname{tr}(L^hS)=a_S+hq,\quad
\operatorname{tr}(Q_wS)=a_S+u,\quad
\operatorname{tr}(T_\nu S)=a_S+u+(\nu-1)t+v.
$$

The single polynomial

$$
P(\tau)=D(\tau)+(a_S+u)(1+k\tau)
\tag{9.5}
$$

has degree at most $d$, because $d\ge1$. At the actual $Q_w$ indices $j=2,\ldots,d+2$, it equals $z_j$. Consequently its entire value is determined by

$$
P(\tau)=\sum_{j=2}^{d+2}z_j
\prod_{\substack{2\le e\le d+2\\e\ne j}}
\frac{\tau-e}{j-e}.
\tag{9.6}
$$

Every denominator is a fixed nonzero integer. Uniqueness follows because successive division by distinct linear root factors makes a degree-at-most-$d$ polynomial with $d+1$ distinct roots zero. Lower actual degrees, cancellations, and $P=0$ are included.

Form the residual coordinates, using $E$ as an auxiliary quantity

$$
u=P(0)-z_0,\quad E=z_1-P(1),\quad W=-2E-u,
\qquad Y=z_a-P(a),\quad Z=z_b-P(b).
\tag{9.7}
$$

For actual data the first coordinate agrees with (9.3), and

$$
E=(1+k)(hq-u),\qquad hq-u=-\frac{u+t+v}{2}.
$$

Therefore

$$
(W,Y,Z)=F_u(t,v,k)
=\bigl((1+k)(t+v)+ku,\ (1+ak)(mt+v),\ (1+bk)((m+1)t+v)\bigr).
\tag{9.8}
$$

The data change to $(P,u,W,Y,Z)$ is a linear isomorphism: its inverse has $z_j=P(j)$ on the $Q_w$ block and

$$
z_0=P(0)-u,\quad z_1=P(1)-(W+u)/2,\quad
z_a=P(a)+Y,\quad z_b=P(b)+Z.
$$

Polynomial evaluation here is decoding, not a virtual read. All reductions are undivided identities at gain zeros as well.

**Determinant and its sign.** At fixed $u$, write $g_j=1+jk$. Differentiating (9.8) in the order $(t,v,k)$ gives

$$
DF_u=\begin{pmatrix}
g_1&g_1&t+v+u\\
mg_a&g_a&a(mt+v)\\
(m+1)g_b&g_b&b((m+1)t+v)
\end{pmatrix}.
$$

Expansion along its last column gives

$$
\begin{aligned}
\mathcal J&=-(t+v+u)g_ag_b
 +am(mt+v)g_1g_b-b(m-1)((m+1)t+v)g_1g_a\\
&=[(a-m^2)t+(a-m)v-u]\\
&\quad+[(a^2-m^2)t+(a^2-m)v-(2a+1)u]k-abuk^2.
\end{aligned}
\tag{9.9}
$$

Let $R_0=a^2-5a+5$ and $R_1=-2a+5$. Substitution of (9.3), with $m=a-2$, gives the exact identity

$$
-\mathcal J=pP_p(k)+qP_q(k)+rP_r(k),
\tag{9.10}
$$

where

$$
\begin{aligned}
P_p(k)&=(w-1)abk^2+[wR_1+a^2-3a+1]k+wR_0+1,\\
P_q(k)&=(w-1)abk^2+[(2a+1)w-a^2-a-3]k+w-3,\\
P_r(k)&=abk^2+R_1k+R_0.
\end{aligned}
\tag{9.11}
$$

For clarity, the constant part of $-\mathcal J$ before substitution is $(R_0-1)t-2v+u$, and its linear part is $-(4a-4)t-(a^2-a+2)v+(2a+1)u$, which give exactly the coefficients displayed in (9.11).

All three quadratics are strictly positive for every real $k$. At $a=w=4$, they are precisely the three completed squares in (4.2). For $a\ge5$, $R_0=a(a-5)+5\ge5$, and

$$
4abR_0-R_1^2\ge20a(a+1)-(2a-5)^2
=16a^2+40a-25>0.
$$

For even $a\ge6$, $w=a$, the leading, linear, and constant coefficients of $P_q$ are

$$
(a^3-a,\ a^2-3,\ a-3).
$$

Its discriminant is

$$
-3a^4+12a^3-2a^2-12a+9
=-3a^3(a-4)-2a^2-12a+9<0.
$$

For odd $a\ge5$, $w=a+1$, the corresponding coefficients are

$$
(a^2(a+1),\ a^2+2a-2,\ a-2),
$$

and its discriminant is

$$
-3a^4+8a^3+8a^2-8a+4
=-a^2(3a^2-8a-8)-8a+4<0,
$$

since $3a^2-8a-8=27+(a-5)(3a+7)\ge27$.

For $P_p$ in the even case, its coefficients are

$$
A=a^3-a>a^2,\quad B=-a^2+2a+1,\quad
C=a^2(a-5)+5a+1>a^2.
$$

Here $|B|<a^2$, so $B^2-4AC<a^4-4a^4<0$. In the odd case they are

$$
A=a^2(a+1)>a^2,\quad B=-a^2+6,\quad
C=a^2(a-4)+6>a^2,
$$

and the same strict discriminant bound applies. In every case the leading coefficient is positive. The identity

$$
4A(Ak^2+Bk+C)=(2Ak+B)^2+4AC-B^2
$$

then proves positivity. Since $p,q,r>0$, (9.10) proves $\mathcal J<0$ throughout the full domain, without a gain-sign restriction.

**Global uniqueness.** For fixed $u$, (9.8) has the form $Ay+kBy+kue_1$, with $y=(t,v)^{\mathsf T}$. Its exact bilinear midpoint identity is

$$
F_u(y_0,k_0)-F_u(y_1,k_1)
=DF_u(\bar y,\bar k)
(\Delta t,\Delta v,\Delta k)^{\mathsf T},
\tag{9.12}
$$

because $k_0y_0-k_1y_1=\bar k\Delta y+\bar y\Delta k$. The fixed-$u$ positive domain in (9.4) is convex; its midpoint has positive $p,q,r$, and its fourth entry is reconstructed as $qr/p$. The midpoint derivative is invertible by (9.10). Equal reduced data therefore force equal $t,v,k$. Equal complete data first give equal $P,u,W,Y,Z$, so (9.4) gives equal $p,q,r,s$, and

$$
D(\tau)=P(\tau)-(p+s+u)(1+k\tau)
\tag{9.13}
$$

gives the same entire original polynomial. This proves recovery globally, using the finite midpoint identity rather than local nonsingularity alone.

**Whole-image inverse.** For arbitrary proposed data compute (9.6)–(9.7) and require $u>0$. Consider the distinct real roots of

$$
H(k)=-(W-ku)(1+ak)(1+bk)
+mY(1+k)(1+bk)-(m-1)Z(1+k)(1+ak).
\tag{9.14}
$$

Its leading coefficient is $abu>0$, so it is a nonzero cubic. It has at most three distinct real roots by successive root factorization, and at least one by continuity and its opposite limits. This finite exact algebraic prescription requires no numerical root approximation.

At each root form

$$
P_k=\begin{pmatrix}
g_1&g_1\\mg_a&g_a\\(m+1)g_b&g_b
\end{pmatrix},\qquad b_k=(W-ku,Y,Z)^{\mathsf T}.
$$

The coefficient labels $c_1=1,c_2=m,c_3=m+1$ are distinct, as are their clock indices $j_1=1,j_2=a,j_3=b$. At most one gain vanishes. Any two surviving rows have determinant $g_{j_e}g_{j_f}(c_e-c_f)\ne0$, so $P_k$ has rank two at every real slope. Cofactor expansion gives

$$
H(k)=\det[P_k^{(1)},P_k^{(2)},b_k].
$$

Consequently $H=0$ is exactly consistency of all three rows, including the right-hand side of an erased row. Select any two surviving row labels $e<f$ and form only their quotients from

$$
V_1=(W-ku)/g_1,\quad V_2=Y/g_a,\quad V_3=Z/g_b.
$$

Then

$$
t=\frac{V_f-V_e}{c_f-c_e},\qquad v=V_e-c_et.
$$

The selected gains and the positive integer divisor are nonzero. Use (9.4), require $p,q,r>0$, set $s=qr/p$, and form (9.13). Require its degree bound and every original observation equation at all $d+5$ actual positions. A passing candidate is sufficient: (1.2)–(1.4) realize its positive source and fixed row on exactly (9.2), with this one whole polynomial. Actual data necessarily supply a passing candidate, and (9.12) excludes two passing targets.

This proves an exact common-source membership test and inverse on the entire image. A gain zero within the repeated $Q_w$ block still gives the value of $P$ at that node. At a zero of $g_1$, $g_a$, or $g_b$, the determinant and final check retain the erased equation while the other two rows survive. Repeated cubic roots are considered once. Both signs of nonzero gains, $k=0$, lower actual drift degrees, zero polynomial $P$, and arbitrary signs of readings are covered.

At $d=1$, $a=w=4$ and $h=1$; (9.1) is exactly (2.1), with its fifteen atoms. The source coordinates, reduced map, and cubic also coincide. This member is the credited sharp-six result.

## 10. A second explicit family, common kernel, and the sharp range

The same proof also admits a simpler expression for the shear parameter, with literal atom count $6d+9$.

**Theorem 10.1.** For every integer $d\ge1$, take

$$
w=2d+2,\quad h=d,\quad a=d+3,\quad b=d+4,\quad m=d+1.
\tag{10.1}
$$

Then (9.1), (9.3)–(9.8), and (9.13)–(9.14) give another globally recovering $d+5$-read history and whole-image inverse. Its nonempty multipliers are $L^d$, $UL^{d+1}$, $U^{d+1}J$, and $U$, with $d$ empty repeats at $Q_w$. Their lengths $2d,2d+4,2d+3,2$ total $6d+9$.

**Proof.** Legality, the actual-source realization, the coordinate inverse, interpolation, and the cubic rank argument in Section 9 only require $w-2=2h>0$ and $m=a-2\ge2$, and still apply. To prove the missing determinant sign, substitute (10.1) in (9.11). With

$$
B=(d+3)(d+4),\quad A=B(2d+1),
$$

one obtains

$$
\begin{aligned}
-\mathcal J={}&p[Ak^2-(3d^2+3d+1)k+2d^3+4d^2-1]\\
&+q[Ak^2+(3d^2+11d-1)k+2d-1]\\
&+r[Bk^2-(2d+1)k+d^2+d-1].
\end{aligned}
$$

Put $x=d-1\ge0$. The positive discriminant margins for the $q$ and $r$ brackets are

$$
\begin{aligned}
4A(2d-1)-(3d^2+11d-1)^2
&=7x^4+74x^3+253x^2+306x+71>0,\\
4B(d^2+d-1)-(2d+1)^2
&=4x^4+48x^3+188x^2+264x+71>0.
\end{aligned}
$$

For the $p$ bracket, its constant exceeds the $q$ constant by $2d(d^2+2d-1)>0$, while

$$
0<3d^2+3d+1<3d^2+11d-1
$$

because the difference is $8d-2>0$. Its discriminant margin is therefore strictly larger than the $q$ margin. All leading coefficients are positive, so completing squares gives positivity of all three brackets for every real slope. The same midpoint proof and cubic inverse now apply in full. ∎

Both families have an exact common safe kernel. Let $n=d+5$ and let $\Lambda_d$ consist of the four shifted $(d+1)$-st forward differences on these $n$ readings. A first difference lowers polynomial degree, so it kills every degree-at-most-$d$ evaluation vector. The four rows are independent: in any nonzero row combination, the greatest row index has a last nonzero coordinate absent from earlier rows. Polynomial evaluations have dimension $d+1$ by interpolation. Thus the kernel of $\Lambda_d$ is exactly that evaluation space.

Write $\mathcal L(X)_i=\operatorname{tr}(A_iX)$ and $(\mathcal I v)_i=iv_i$. Every endpoint has lower-right entry one, so $E_{22}$ has constant trace signal one and

$$
\mathcal T_k=\Lambda_d(\operatorname{Id}+k\mathcal I)\mathcal L,
\qquad E_{22}\in\ker\mathcal T_k.
$$

Conversely, if a full real matrix $X$ belongs to this kernel, the exact quotient supplies one degree-at-most-$d$ compensating polynomial with all observations zero. The coordinate and interpolation identities of Section 9 hold without rank or positivity. Zero observations give $P=u=W=Y=Z=0$. Rank two of $P_k$ gives $t=v=0$; (9.4) gives $p=q=r=0$. The remaining $s$ is free, with compensator $-s(1+k\tau)$. Hence for both families

$$
\ker\mathcal T_k=\mathbb RE_{22},\qquad
\operatorname{rank}\mathcal T_k=3\quad(k\in\mathbb R).
$$

The safe signal is the constant one; it lies in degree at most $d-1$ for every $d\ge1$. This full-matrix quotient is an auxiliary rank assertion. Actual-source recovery was separately established above.

The conjugation argument of Section 6 applies to each family: replace every endpoint and multiplier by $JA_iJ$ and $JW_iJ$. These remain finite legal words, and $S=JS'J$, with positive factors $Jc$ and $\ell J$, preserves all actual observations. The mirrored kernels are $\mathbb RE_{11}$, and $k,D$ are unchanged. No physical conjugation step or extra read is inserted. The full positive relation/gain fibre for every family is exactly (6.3), with the same internal factor scale proved there.

Section 7 supplies the credited lower bound on the identical actual target for all predetermined histories. Together with either attaining family it gives

$$
\boxed{C_{\mathrm{fix}}(d)=d+5\qquad\text{for every integer }d\ge1.}
\tag{10.2}
$$

For $d=0$ the same lower bound is five, and the $d=1$ six-read inverse also works when the true drift is constant. Thus $5\le C_{\mathrm{fix}}(0)\le6$. No five-read construction or universal five-read collision is supplied. The positive-degree proof uses both polynomial absorption with $d\ge1$ and a positive coordinate divisor; it does not settle this endpoint.

## 11. Norms and the exact six-read stability problem

All stability statements below concern the six-read history (2.1), with $d=1$. They compare two actual compatible targets and their exact data vectors on this history. For vectors use the maximum norm, for matrices use the maximum absolute entry, and for the entire affine drift use

$$
\|D\|_{\mathrm{coef}}=\max(|\delta_0|,|\delta_1|).
$$

The full-target distance is

$$
\max\{\|S_0-S_1\|_{\max},\ |k_0-k_1|,
\|D_0-D_1\|_{\mathrm{coef}}\}.
$$

This is a coefficient norm, not a supremum over all real $\tau$; it implies

$$
|D_0(\tau)-D_1(\tau)|\le(1+|\tau|)\|D_0-D_1\|_{\mathrm{coef}}.
$$

Use the coordinates of Section 3, write $\Delta$ for endpoint zero minus endpoint one, bars for arithmetic means, and $e=\|\Delta z\|_\infty$. Their observed linear expressions simplify to

$$
\begin{aligned}
\zeta&=z_0,&\eta&=z_3-z_2,&u&=3z_2-2z_3-z_0,\\
W&=z_0-2z_1+z_2,&Y&=z_2-2z_3+z_4,&Z&=2z_2-3z_3+z_5.
\end{aligned}
$$

Consequently

$$
|\Delta\zeta|\le e,\quad |\Delta\eta|\le2e,\quad
|\Delta u|\le6e,\quad \|\Delta(W,Y,Z)\|_\infty\le6e.
\tag{11.1}
$$

On the fixed-$u$ positive domain $\Omega_u$ from (3.2),

$$
p<u/3,\quad q<u/3,\quad r<u,\quad
0<t<4u/3,\quad |v|<u/3.
$$

The stability theorems do not normalize away a source scale or a gain zero.

## 12. Uniform reduced stability on every calibrated invariant slice

**Theorem 12.1.** Set $C_0=43200$. Fix any $u>0$. For any two points in $\Omega_u\times\mathbb R$, let $H=1+|\bar k|$ and $e_F=\|\Delta F_u\|_\infty$. Then

$$
\max\{H|\Delta t|,\ H|\Delta v|,\ u|\Delta k|\}
\le C_0e_F.
\tag{12.1}
$$

In particular the inverse of the reduced map is globally Lipschitz, with

$$
\|\Delta(t,v,k)\|_\infty
\le C_0\max(1,1/u)e_F,
$$

uniformly over all positive shapes and all real slopes at this fixed $u$. For raw six-read data on this slice,

$$
\max\{|\Delta\zeta|,|\Delta\eta|,|\Delta t|,|\Delta v|,u|\Delta k|\}
\le6C_0e.
$$

**Proof.** Subtract $(1+k^2)/4$ from each of the three quadratic brackets in (4.2). The resulting leading coefficients are positive, and their discriminants are respectively $-4345/4,-41/4,-201/4$. The completed-square criterion therefore gives

$$
|\mathcal J|\ge\frac{(p+q+r)(1+k^2)}4
\ge\frac{u(1+k^2)}{12}
\ge\frac{u(1+|k|)^2}{24}.
\tag{12.2}
$$

Here $u\le3(p+q+r)$ and $(1+|k|)^2\le2(1+k^2)$.

At any source point put $H_k=1+|k|$. The first two columns of the matrix in Section 4 have absolute entries at most $15H_k$ and $5H_k$. Its third column, in source coordinates, is

$$
(6p+4q+2r,\ 28p+4q+8r,\ 55p+5q+15r)^{\mathsf T}.
$$

The entries are bounded by $2u,28u/3,55u/3$, hence by $20u$. Each cofactor in either of the first two rows of the inverse has absolute value at most $600uH_k$; each in the last row is at most $150H_k^2$. The adjugate formula, including the three terms in each row sum, and (12.2) give, for every vector $w$,

$$
\begin{aligned}
H_k\max\{|(DF_u^{-1}w)_1|,|(DF_u^{-1}w)_2|\}
&\le43200\|w\|_\infty,\\
u|(DF_u^{-1}w)_3|&\le10800\|w\|_\infty.
\end{aligned}
\tag{12.3}
$$

Here $DF_u^{-1}$ denotes the inverse derivative matrix at the given point. Apply these inequalities at the positive midpoint in (4.3). This proves (12.1). Equation (11.1) proves its raw-data consequence. ∎

A bound on the determinant alone would not supply this estimate: the cofactor bounds and the exact finite midpoint identity are both used. No positive lower bound on $p/u$ or bound on $k$ enters Theorem 12.1.

## 13. Global stability of the source and entire drift

**Theorem 13.1.** Fix $0<\rho<1/3$. Let $\mathcal C_\rho$ be all actual six-read targets with

$$
p\ge\rho u,\qquad u=3p+3q+r,
$$

and otherwise unrestricted positive source coordinates, real slopes, and affine drift coefficients. Define

$$
\begin{aligned}
C_x&=108C_0+12,&C_b&=9(6+15C_x),\\
L_\rho&=\frac1{3\rho^2}+\frac4{3\rho},\\
C_{SD}(\rho)&=\max\{1+(1+L_\rho)C_x,\ 2+(8+L_\rho)C_b\}.
\end{aligned}
$$

For every pair in this class,

$$
\max\{\|\Delta S\|_{\max},\|\Delta D\|_{\mathrm{coef}}\}
\le C_{SD}(\rho)e.
\tag{13.1}
$$

There is no lower or upper scale bound, slope bound, or drift-coefficient bound in this assertion. It bounds $S,D$, without asserting a bound on $\Delta k$ yet.

**Proof.** First allow $u_0,u_1$ to differ. The full bilinear midpoint expansion of (3.6) is

$$
\Delta F=DF_{\bar u}(\bar t,\bar v,\bar k)
(\Delta t,\Delta v,\Delta k)^{\mathsf T}
+\bar k\Delta u\,e_1.
$$

The midpoint of $x=(p,q,r)$ is positive and has invariant $\bar u$, by the linear coordinate change. With $d_u=|\Delta u|$, (12.3) gives

$$
\max(|\Delta t|,|\Delta v|)
\le\frac{C_0(e_F+|\bar k|d_u)}{1+|\bar k|}
\le C_0(e_F+d_u).
$$

Equation (3.2) implies

$$
\|\Delta x\|_\infty\le9\max(|\Delta t|,|\Delta v|)+2d_u
\le C_xe.
\tag{13.2}
$$

This step needs no shape restriction. Next put $b_x=kx$, an actual common-gain multiple at each endpoint. Direct substitution gives

$$
(W,Y,Z)^{\mathsf T}=Ax+Bb_x,
$$

$$
A=\begin{pmatrix}3&1&1\\7&1&2\\11&1&3\end{pmatrix},\qquad
B=\begin{pmatrix}6&4&2\\28&4&8\\55&5&15\end{pmatrix},
$$

$$
B^{-1}=\frac1{40}\begin{pmatrix}20&-50&24\\20&-20&8\\-80&190&-88\end{pmatrix}.
$$

Multiplication gives the identity matrix; $\det B=40$. The maximum absolute row sums of $A$ and $B^{-1}$ are $15$ and $179/20<9$. Hence

$$
\|\Delta b_x\|_\infty
\le9(e_F+15\|\Delta x\|_\infty)\le C_be.
\tag{13.3}
$$

This linear estimate does not introduce independent lifted sources: $b_x=kx$ is retained exactly.

On the convex positive cone $p\ge\rho(3p+3q+r)$, put $f(x)=qr/p$. Its derivative satisfies

$$
|\partial_pf|\le\frac1{3\rho^2},\qquad
|\partial_qf|\le\frac1\rho,\qquad
|\partial_rf|\le\frac1{3\rho}.
$$

Integrating along a segment in that cone gives

$$
|\Delta f(x)|\le L_\rho\|\Delta x\|_\infty.
\tag{13.4}
$$

Extend $f$ to the negative of this cone and to zero by the same rational formula off zero and $f(0)=0$. In either common-sign cone the same derivative bounds apply. Continuity at zero follows from $|f(b)|\le|b_q|/\rho$. For opposite-sign endpoints, $f$ has the corresponding signs, and

$$
|f(b_0)-f(b_1)|\le\frac{|b_{0q}|+|b_{1q}|}{\rho}
=\frac{|\Delta b_q|}{\rho}\le L_\rho\|\Delta b\|_\infty.
$$

Thus (13.4) holds on this entire two-cone domain including zero. Every $b_x=kx$ lies there, and $f(b_x)=ks$ for positive, negative, or zero $k$.

Finally the entire original drift has coefficients

$$
\delta_0=\zeta-p-f(x),\qquad
\delta_1=\eta-[4(b_x)_p+3(b_x)_q+(b_x)_r+f(b_x)].
$$

The second equality uses $k(a+u)=4kp+3kq+kr+ks$. Equations (11.1), (13.2)–(13.4) give

$$
\begin{aligned}
|\Delta\delta_0|&\le[1+(1+L_\rho)C_x]e,\\
|\Delta\delta_1|&\le[2+(8+L_\rho)C_b]e.
\end{aligned}
$$

Also $\|\Delta S\|_{\max}\le(1+L_\rho)C_xe$. These prove (13.1), with no division by a sampled gain. ∎

## 14. Full-target domains, local inverses, and compact sets

**Theorem 14.1.** On $\mathcal C_\rho$ with exactly calibrated $u=u_0>0$, the full target has the bound

$$
\max\{\|\Delta S\|_{\max},|\Delta k|,\|\Delta D\|_{\mathrm{coef}}\}
\le\max\{C_{SD}(\rho),6C_0/u_0\}\,e
\tag{14.1}
$$

for all real slopes. On $\mathcal C_\rho$ with $u\ge m_0>0$ and $|k|\le K<\infty$, it instead has the bound

$$
\max\{\|\Delta S\|_{\max},|\Delta k|,\|\Delta D\|_{\mathrm{coef}}\}
\le\max\{C_{SD}(\rho),(7C_b+6K)/m_0\}\,e.
\tag{14.2}
$$

No upper scale bound or drift bound is needed in either assertion.

**Proof.** For (14.1) combine (12.1) and (13.1). For (14.2), set $b_u=3(b_x)_p+3(b_x)_q+(b_x)_r=ku$. The exact product identity is

$$
\bar u\Delta k=\Delta b_u-\bar k\Delta u.
$$

Here $|\Delta b_u|\le7C_be$, $|\Delta u|\le6e$, $\bar u\ge m_0$, and $|\bar k|\le K$. This proves the slope bound and hence (14.2). ∎

These are sufficient domains, not a classification of every restricted family that can admit stability. For example, prescribing $q$ proportional to $p$ can make $s$ linear without this particular shape bound; prescribing $k$ removes slope estimation entirely.

The unrestricted six-read map is globally injective by Section 4 and is a local smooth diffeomorphism at every actual target. To see the latter, use the open chart $(p,q,r,k,\delta_0,\delta_1)$ with $s=qr/p$. Its change to $(\zeta,\eta,u,t,v,k)$ is smooth and invertible: the source change has (3.2), and the drift change is triangular with unit coefficients in $\delta_0,\delta_1$. The output change to $(\zeta,\eta,u,W,Y,Z)$ is a linear isomorphism. Its remaining derivative block is exactly $DF_u$, whose determinant is nonzero by (4.2). The inverse function theorem supplies local smooth inverses; global injectivity makes them agree on the exact image.

Every compact subset of this actual-target chart has positive minima of $u$ and $p/u$, and bounded $k$. Choose $\rho<1/3$ below its shape minimum, a positive $m_0$ below its scale minimum, and a finite $K$ bounding its slopes. Equation (14.2) then gives a Lipschitz inverse on that entire compact set. This separates local smooth inversion, compact-domain Lipschitz estimates, and the stronger global domain claims.

For each fixed $d\ge1$, use the drift coefficient norm $\max_{0\le h\le d}|\delta_h|$ and the same maximum product norm on $(S,k,D)$. Both higher-degree families also have local smooth inverses by the same coordinate argument with $(P,u,t,v,k)$ and (9.9)–(9.11). On any compact actual-target set these inverses are Lipschitz as well: cover the compact image by finitely many small output balls whose larger concentric balls admit smooth local inverses with bounded derivatives. A positive Lebesgue number gives a uniform local pair bound; pairs farther apart are bounded by the finite target diameter divided by that number. This compactness statement does not assert the quantitative six-read constants for higher degrees or any unrestricted higher-degree stability domain.

## 15. Actual-source failures of unrestricted six-read stability

The following pairs use precisely (2.1) and its fixed fifteen-atom implementation. For every source below use $\alpha=1$, $\beta=k$, $R=S$, and positive factors as specified. The row is fixed during each run. Equations (1.3)–(1.4) then verify every read and unread state, so these are original-model pairs.

**Shape boundary at fixed invariant.** For $0<\epsilon<1/4$ and $j=1,2$, set

$$
p_j=\epsilon,\quad q_j=2-(1+j/3)\epsilon,\quad
r_j=j\epsilon,\quad s_j=jq_j,\quad k_j=0,
\qquad D_j(\tau)=-(p_j+s_j).
$$

Every entry is positive, $p_js_j=q_jr_j$, and $u_j=3p_j+3q_j+r_j=6$. Use $c_j=(\epsilon,j\epsilon)^{\mathsf T}$ and $\ell_j=(1,q_j/\epsilon)$. Their product is $S_j$. The one constant polynomial $D_j$ is used at every index. Direct trace substitution gives the entire data vector

$$
z^{(j)}=\bigl(0,\ 2-(1+j/3)\epsilon,\ 6,\ 6,
8+(6+5j/3)\epsilon,\ 8+(10+8j/3)\epsilon\bigr).
$$

Thus

$$
\|z^{(2)}-z^{(1)}\|_\infty=8\epsilon/3\longrightarrow0,
\qquad s_2-s_1=2-2\epsilon,
\qquad \|D_2-D_1\|_{\mathrm{coef}}=2-2\epsilon.
$$

The matrices and drift coefficients stay bounded. Hence even at fixed $u=6$, bounded sources and drifts, and zero slope, the unrestricted full $S,D$ inverse is not uniformly continuous. The reduced estimate of Section 12 still holds; reconstruction of $s=qr/p$ fails uniformly near this shape boundary.

**Scale approaching zero.** For any chosen $0<\rho<1/3$ put

$$
\theta=\frac{1-3\rho}{8\rho}>0,\qquad
S_*=\begin{pmatrix}1&\theta\\\theta&\theta^2\end{pmatrix},\qquad u_*=3+4\theta.
$$

Here $p_*/u_*>\rho$, because $1-3\rho-4\rho\theta=(1-3\rho)/2>0$. Set $a_i=\operatorname{tr}(A_iS_*)$; explicitly

$$
(a_0,\ldots,a_5)=(1+\theta^2,\ 1+\theta+\theta^2,
4+4\theta+\theta^2,\ 4+4\theta+\theta^2,
11+7\theta+\theta^2,\ 15+8\theta+\theta^2).
$$

For $\epsilon>0$ take $S_0=S_1=\epsilon S_*$, $k_0=0$, $k_1=1$, and $D_0=D_1=0$. Use $c_j=\epsilon(1,\theta)^{\mathsf T}$ and $\ell_j=(1,\theta)$. Each run has this one positive factorization. The observation difference at index $i$ is $\epsilon ia_i$, so its maximum norm is $5\epsilon a_5\to0$, while $|k_1-k_0|=1$. Both sources obey the same strict shape condition and $u=\epsilon u_*\to0$. A shape bound and bounded slopes therefore do not supply uniformly continuous slope recovery when scale can vanish.

**Unbounded slopes with varying invariant.** Keep this $S_*$ and, for positive integers $n$, put

$$
\lambda_n=1+1/n,\quad S_0=S_*,\quad k_0=n,\quad
S_1=\lambda_nS_*,\quad k_1=n/\lambda_n,\quad D_0=D_1=0.
$$

Use $c_0=(1,\theta)^{\mathsf T}$, $c_1=\lambda_n(1,\theta)^{\mathsf T}$ and $\ell_0=\ell_1=(1,\theta)$. The exact observations obey

$$
z_i^{(1)}-z_i^{(0)}
=[\lambda_n(1+(n/\lambda_n)i)-(1+ni)]a_i=a_i/n.
$$

Their distance is $a_5/n\to0$, whereas

$$
|k_0-k_1|=n/(n+1)\longrightarrow1.
$$

The sources lie in the compact positive segment $\{\lambda S_*:1\le\lambda\le2\}$, preserve $p/u>\rho$, and have $u\in[u_*,2u_*]$. Both drifts are zero and all gains are positive. Thus allowing unbounded slopes while the invariant varies destroys uniform continuity of slope recovery even on this compact source domain. It does not contradict fixed-$u$ stability or compactness of the full target, since the slopes escape every bounded set.

These failures change effective targets, rather than merely moving along the positive representation fibre. They do not assert that every particular smaller shape or slope family is unstable.

## 16. Credits, theorem scope, and the remaining original target

The original common positive rank-one model, fixed row, effective target, actual recorded clock, and positive relation/gain fibre are credited through *Shared affine gain and zero-crossing recovery* and the supplied original recovery programme. That companion's Theorem 5.1 supplies the all-fixed-history $d+5$ lower bound, fully reproduced in Section 7. Its $\max(d+6,7)$ upper construction and its particular-prefix obstruction are prior results; they are not discoveries of this volume. The broader polynomial-gain construction also retains its own domain and prefix scope. Its affine target conversion is

$$
R_0=S/\operatorname{tr}S,\qquad H(\tau)=(\operatorname{tr}S)(1+k\tau),
\qquad S=H(0)R_0,\qquad k=H'(0)/H(0),\qquad H(0)>0,
$$

with the entire $D$ unchanged. Its broader $H(0)=0$ domain is outside the present positive-intercept model.

*Sharp six-read affine-drift recovery in the diagonal a=2 branch, with a global cubic inverse* supplies the specific history, coordinates, determinant, midpoint method, cubic, exact kernel, and conditional $a=3$ collision retained in Sections 2–8. The sharp-six result and the credited lower bound are not relabelled as new discoveries. *Recorded-clock collapse and a common safe kernel at the affine endpoint* supplies the diagonal-stratum context. The $a=3$ proof here is directly conditional on its displayed actual endpoints and rank hypothesis and does not use an unproved normal-form sufficiency criterion. The other constant-drift, secant, and critical-point companions supply their stated path-specific and necessary-obstruction context; those results are not treated as global sufficiency theorems.

The supplied candidate *Sharp d+5 fixed-history recovery for every positive drift upper degree* supplies the parity family and determinant proof in Section 9, including its higher-degree common-kernel consequence. The candidate *The prescribed family attains d+5 reads for every integer d>=1* supplies the explicit $w=2d+2$ verification in Section 10 and credits those endpoints to its caller. The candidate *Uniform inverse stability on every positive calibrated-invariant slice, and precise source, drift, and slope boundaries* supplies the quantitative six-read bounds and actual-source failure families in Sections 11–15. These are mathematical supplier credits, not independent approval or external priority claims. The complete arguments and actual-source correspondences used here are given in this volume.

The proved read optimum is $C_{\mathrm{fix}}(d)=d+5$ for every positive integer upper degree, with the original $(S,k,D)$ target, every real slope, every gain-zero crossing, and one whole drift per run. The unresolved constant-drift endpoint remains

$$
5\le C_{\mathrm{fix}}(0)\le6.
$$

The original all-degree programme therefore remains incomplete. The equality does not classify all optimal histories. The conditional $a=3$ exclusion does not classify other $a=2$ histories, non-diagonal safe kernels, or regular pencils. No such classification is required for the positive-degree optimum once a legal family attains the all-history lower bound.

Quantitative global stability here concerns only the stated six-read domains and target components. The constants are not optimized. Other constrained source/slope families and unrestricted higher-degree stability are not classified. All inequalities compare pairs of compatible exact data; they do not specify a globally stable decoder for arbitrary off-image noisy data. The finite algebraic image tests do not themselves establish numerical root-selection stability.

All conclusions are ordinary conditional textual mathematics, without Lean or empirical certification or a worldwide-originality claim. They preserve strict positivity, rank one, the positive initial gain intercept, known $M,J$, a counted initial scalar read, arbitrary finite predetermined forward words including empty words, and one fixed positive row per run. Literal atom counts are construction counts; they are separate from reads and are not proved optimal. No adaptive lower bound, precision, bit/time, physical-resource, acquisition-cost, or general neural-network conclusion follows. The exact representation freedoms are the positive relation/gain scale and the internal factor scale already proved in Section 6.

## 追加锚（本行以下为增补区）
