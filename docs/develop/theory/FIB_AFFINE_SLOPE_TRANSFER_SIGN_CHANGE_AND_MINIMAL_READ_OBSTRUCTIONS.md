# Affine slope transfer and sign-change obstructions at the minimum read count

Removing the additive drift leaves a four-dimensional quotient at the candidate minimum read count. At an invertible slope, that quotient determines a linear transfer between nearby slopes. A sign change of the transferred source determinant then forces a collision between actual positive rank-one sources. This gives a necessary condition for arbitrary minimum-length fixed histories and excludes an infinite family of legal histories whose matrix spans survive every single noninitial deletion.

## 1. Model, clock, and existing results

Fix a known integer $d\ge0$ and matrices

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$

A predetermined $n$-read history has $A_0=I$ and $A_{i+1}=W_iA_i$, where each $W_i$ is a finite word in $M,J$, possibly empty. Matrix products act on the left. A chronological atom list $(E_1,\ldots,E_h)$ has multiplier $E_h\cdots E_1$; thus the chronological pair $(M,J)$ implements $U$. Every recorded scalar read advances the consecutive index $i=0,\ldots,n-1$, including a read after an empty word. Unread atomic operations do not advance this index.

The original source is $R=c\ell$, with a strictly positive column $c$ and one strictly positive row $\ell$ fixed throughout its run. There are fixed parameters $\alpha>0$, $\beta\in\mathbb R$, and one entire real polynomial $D$ of degree at most $d$. Write

$$
S=\alpha R,\qquad \kappa=\beta/\alpha,\qquad
\mathcal R_+=\left\{
\begin{pmatrix}p&q\\r&s\end{pmatrix}:p,q,r,s>0,\ ps=qr
\right\}.
$$

The observations and complete effective target are

$$
z_i=(1+\kappa i)\operatorname{tr}(A_iS)+D(i),
\qquad (S,\kappa,D)\in\mathcal R_+\times\mathbb R\times\mathcal P_d,
$$

where $\mathcal P_d$ includes the zero polynomial. The slope may have either sign, and gain zeros are allowed. Each run has one source, one fixed row, and one polynomial used at all its recorded positions. Only the column is acted on; there are no resets, copies, inverse acquisitions, instrument changes, or combinations of unexecuted histories.

We use the actual-source and representation interfaces of [Affine-gain erasure, positive secants, and drift-kernel collisions](FIB_AFFINE_GAIN_ERASURE_SPAN_AND_POSITIVE_GAIN_COLLISIONS.md), Proposition 1.1. In particular, an effective source has the positive realization

$$
\alpha=1,\quad R=S,\quad\beta=\kappa,\quad
c=(p,r)^{\mathsf T},\quad\ell=(1,q/p).
$$

For a fixed effective target its original relation/gain representations are exactly $R=S/t$, $\alpha=t>0$, $\beta=\kappa t$, with $D$ fixed. The positive factorization of a fixed relation has the separate internal freedom $c\mapsto\lambda c$, $\ell\mapsto\ell/\lambda$, $\lambda>0$. These representation freedoms do not identify distinct effective triples.

Let $C_{\mathrm{fix}}(d)$ be the smallest uniform exact-read bound over all the permitted predetermined histories. Theorem 5.1 of [Shared affine gain and zero-crossing recovery](FIB_SHARED_AFFINE_GAIN_ZERO_CROSSING_RECOVERY.md) supplies the all-fixed-history lower bound $d+5$. Its Theorem 2.1 supplies the upper bound $\max(d+6,7)$ for arbitrary real affine slopes. The constant-drift six-read recovery result in [Affine six-read recovery and unknown-slope collisions](FIB_AFFINE_SIX_READ_RECOVERY_AND_UNKNOWN_SLOPE_COLLISIONS.md) improves the constant-drift upper endpoint to six. Thus the credited current intervals are

$$
5\le C_{\mathrm{fix}}(0)\le6,\qquad
 d+5\le C_{\mathrm{fix}}(d)\le d+6\quad(d\ge1).
$$

These numerical bounds, their recovery proofs, and the positive-scale fibre are existing results. The results below give further obstructions at the lower endpoint.

## 2. The exact drift quotient and slope transfer

For this section fix any legal history with $n=d+5$. For a matrix $T$ define its signal vector

$$
\mathcal L(T)=\bigl(\operatorname{tr}(A_iT)\bigr)_{i=0}^{n-1},
\qquad
\mathcal I v=(iv_i)_{i=0}^{n-1}.
$$

Define the four-component difference map

$$
(\Lambda v)_j=
\sum_{h=0}^{d+1}(-1)^{d+1-h}\binom{d+1}{h}v_{j+h},
\qquad j=0,1,2,3.
$$

**Lemma 2.1 (exact polynomial quotient).** If $\operatorname{ev}(P)=(P(i))_{i=0}^{n-1}$, then

$$
\ker\Lambda=\operatorname{ev}(\mathcal P_d).
$$

Proof. One forward difference lowers the degree of a nonconstant polynomial: the highest terms of $(t+1)^h$ and $t^h$ cancel. It kills a constant. The binomial expansion of the iterated difference gives the displayed coefficients. Applying $d+1$ differences therefore gives $\Lambda\operatorname{ev}(P)=0$ for every $P\in\mathcal P_d$.

Evaluation is injective on $\mathcal P_d$ by the polynomial root bound, as stated in Lemma 2.1 of [Common polynomial-gain shear calibration and erasure recovery](FIB_POLYNOMIAL_GAIN_SHEAR_CALIBRATION_AND_ERASURE_RECOVERY.md). Its image consequently has dimension $d+1$. The four rows of $\Lambda$ are independent: in a nonzero row combination, take the largest row index $j$ with nonzero coefficient. Coordinate $j+d+1$ has coefficient one in that row and is absent from every earlier row, so the combination cannot vanish. Thus $\Lambda$ has rank four and its kernel has dimension $n-4=d+1$. The inclusion already proved is therefore equality. This includes $d=0$, zero polynomials, and lower actual degrees. ∎

Put

$$
\mathcal B=\Lambda\mathcal L,\qquad
\mathcal C=\Lambda\mathcal I\mathcal L,\qquad
\mathcal T_\kappa=\mathcal B+\kappa\mathcal C.
$$

Each $\mathcal T_\kappa$ maps the four-dimensional real matrix space to $\mathbb R^4$. Whenever $\mathcal T_{\kappa_0}$ is invertible, define the slope-transfer operator

$$
\mathcal H=\mathcal T_{\kappa_0}^{-1}\mathcal C.
$$

This inverse is an algebraic operation on the observation quotient, not an allowed acquisition operation. For $S=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$ define

$$
Q_{\mathcal H}(S)
=s\,\mathcal H(S)_{11}+p\,\mathcal H(S)_{22}
-r\,\mathcal H(S)_{12}-q\,\mathcal H(S)_{21}.
$$

Here $\det(\mathcal H(S))$ below is a determinant of a two-by-two matrix. Expanding that source determinant gives, for rank-one $S$,

$$
\det\bigl(S+\varepsilon\mathcal H(S)\bigr)
=\varepsilon Q_{\mathcal H}(S)
 +\varepsilon^2\det\bigl(\mathcal H(S)\bigr).
$$

## 3. A general different-slope obstruction

**Theorem 3.1 (sign change forces an actual collision).** Suppose $\mathcal T_{\kappa_0}$ is invertible. If $Q_{\mathcal H}$ takes both a strictly negative and a strictly positive value on $\mathcal R_+$, then for every sufficiently small $\varepsilon>0$ there are two distinct actual effective targets with slopes $\kappa_0$ and $\kappa_0+\varepsilon$ giving the same entire $n=d+5$ observations on the prescribed history.

Consequently a uniformly recovering history must satisfy, at every slope where $\mathcal T_\kappa$ is invertible, either

$$
Q_{\mathcal T_\kappa^{-1}\mathcal C}(S)\ge0
\quad\hbox{for every }S\in\mathcal R_+,
$$

or the reversed inequality for every such $S$. The choice of sign may depend on $\kappa$. This is a necessary condition only.

Proof. Choose $S_-,S_+\in\mathcal R_+$ with opposite strict signs of $Q_{\mathcal H}$. Every member of $\mathcal R_+$ has unique coordinates

$$
S=r\begin{pmatrix}x&xy\\1&y\end{pmatrix},\qquad r,x,y>0.
$$

Interpolate each of these three coordinates linearly between the two endpoints. This gives a continuous path $S(\theta)$, $0\le\theta\le1$, lying entirely in $\mathcal R_+$. Compactness supplies a common positive lower bound $b$ for its four entries. Let

$$
K=1+\max_{\theta,a,b'}|\mathcal H(S(\theta))_{ab'}|,
\qquad
\eta=\min\bigl(-Q_{\mathcal H}(S_-),Q_{\mathcal H}(S_+)\bigr)>0,
$$

after ordering the endpoints so that $S_-$ has the negative sign. These quantities are finite, and $|\det(\mathcal H(S(\theta)))|\le2K^2$. For every

$$
0<\varepsilon<\min\left(\frac b{2K},\frac\eta{4K^2}\right)
$$

the entries of $S(\theta)+\varepsilon\mathcal H(S(\theta))$ exceed $b/2$. The continuous function

$$
Q_{\mathcal H}(S(\theta))
 +\varepsilon\det\bigl(\mathcal H(S(\theta))\bigr)
$$

still has opposite strict endpoint signs. The intermediate value theorem gives an interior $\theta_\varepsilon$ where it vanishes. Set

$$
S_1=S(\theta_\varepsilon),\qquad
S_0=S_1+\varepsilon\mathcal H(S_1).
$$

The determinant identity makes $\det S_0=0$; positivity makes its rank exactly one. Thus both sources belong to $\mathcal R_+$.

The transfer identity is

$$
\mathcal T_{\kappa_0}(S_0)
=\mathcal T_{\kappa_0}(S_1)+\varepsilon\mathcal C(S_1)
=\mathcal T_{\kappa_0+\varepsilon}(S_1).
$$

Hence the vector

$$
u_i=(1+\kappa_0 i)\operatorname{tr}(A_iS_0)
 -(1+(\kappa_0+\varepsilon)i)\operatorname{tr}(A_iS_1)
$$

lies in $\ker\Lambda$. Lemma 2.1 gives one entire polynomial $P\in\mathcal P_d$ with $P(i)=u_i$ at every recorded position. Explicitly it is

$$
P(t)=\sum_{h=0}^{d}u_h
\prod_{\substack{0\le b'\le d\\b'\ne h}}
\frac{t-b'}{h-b'}.
$$

The denominators are nonzero node differences; for $d=0$ the product is one. Membership in $\ker\Lambda$ ensures agreement at all the remaining nodes as well. Choose $D_0=0$ and $D_1=P$. For every actual recorded index,

$$
(1+\kappa_0 i)\operatorname{tr}(A_iS_0)+D_0(i)
=(1+(\kappa_0+\varepsilon)i)\operatorname{tr}(A_iS_1)+D_1(i).
$$

This also checks a position at which either gain is zero; no division by a gain has occurred.

For $a=0,1$, set $R_a=S_a$, $\alpha_a=1$, $\beta_a=\kappa_0+a\varepsilon$, and use

$$
c_a=(p_a,r_a)^{\mathsf T},\qquad\ell_a=(1,q_a/p_a).
$$

These factors are positive and their product is $S_a$, since $r_aq_a/p_a=s_a$. Expansion gives $\ell_a A_i c_a=\operatorname{tr}(A_iS_a)$. At every intermediate atom,

$$
M(c_1,c_2)^{\mathsf T}=(c_2,c_1+c_2)^{\mathsf T},\qquad
J(c_1,c_2)^{\mathsf T}=(c_2,c_1)^{\mathsf T},
$$

so each complete prescribed history has positive read and unread states with its one unchanged row. The displayed $D_a$ is used throughout its run. The targets are distinct because their slopes differ, even if an exceptional transfer gives $S_0=S_1$.

A uniformly recovering history cannot admit these collisions. Absence of both strict signs is exactly the alternative that all values are nonnegative or all are nonpositive, including the identically zero case. This proves the necessary condition. ∎

Invertibility also means that the prescribed-slope matrix/drift kernel at $\kappa_0$ is zero: applying $\Lambda$ to a compensated signal gives $\mathcal T_{\kappa_0}(T)=0$, hence $T=0$, and then the polynomial vanishes. Theorem 3.1 therefore detects a different-slope obstruction even at such an individually injective slice. The prescribed-slope criterion in Theorem 3.1 of [Affine-gain erasure, positive secants, and drift-kernel collisions](FIB_AFFINE_GAIN_ERASURE_SPAN_AND_POSITIVE_GAIN_COLLISIONS.md) concerns a different question.

No conclusion is asserted at a slope with singular $\mathcal T_\kappa$. At an invertible slope, a zero or one-sided $Q$ does not establish recovery: the argument only supplies a collision from opposite strict signs. It does not exclude other collisions, either nearby or between distant slopes.

## 4. An infinite family at $d+5$ reads

Put

$$
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
$$

For every integer $m\ge2$, define four tail matrices

$$
C_1=U,\qquad C_2=LU,\qquad C_3=U^2LU,\qquad C_4=L^mU^2LU.
$$

**Theorem 4.1 (positive-gain collisions with full surviving spans).** For every $d\ge0$ and $m\ge2$, the history

$$
A_i=I\quad(0\le i\le d),\qquad
A_{d+j}=C_j\quad(1\le j\le4)
$$

has $d+5$ reads and admits distinct positive rank-one effective sources with slopes $0$ and $\varepsilon>0$, degree-at-most-$d$ drifts, and identical observations. Every recorded gain is strictly positive. Deletion of any single noninitial recorded position leaves four-dimensional matrix span. For $d=0$ the five recorded matrices are distinct.

Proof. We first verify the legal history, then identify its slope-transfer operator and construct the actual collision.

After the initial read and $d$ empty-word repeats, use the following chronological atom blocks, with no intermediate reads within a block:

| Endpoint index | Chronological block | Cumulative matrix |
| --- | --- | --- |
| $d+1$ | $(M,J)$ | $U$ |
| $d+2$ | $(J,M)$ | $LU$ |
| $d+3$ | $(M,J,M,J)$ | $U^2LU$ |
| $d+4$ | $m$ repetitions of $(J,M)$ | $L^mU^2LU$ |

The blocks have $2,2,4,2m$ atoms, for $8+2m$ in total. There are $d+1$ baseline reads and four tail reads. These are the actual consecutive read indices; the unread atoms do not change them. Multiplication gives

$$
C_1=\begin{pmatrix}1&1\\0&1\end{pmatrix},\quad
C_2=\begin{pmatrix}1&1\\1&2\end{pmatrix},\quad
C_3=\begin{pmatrix}3&5\\1&2\end{pmatrix},\quad
C_4=\begin{pmatrix}3&5\\3m+1&5m+2\end{pmatrix}.
$$

Each has determinant one. They and $I$ are distinct for $m\ge2$; different $m$ give different final matrices, so this is an infinite family of histories.

For any real matrix $T=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$, put $a=p+s$ and

$$
V_j(T)=\operatorname{tr}(C_jT)-a.
$$

Expanding the traces gives

$$
V(T)=\bigl(r,\ q+r+s,\ 2p+q+5r+s,
2p+(3m+1)q+5r+(5m+1)s\bigr).
$$

This linear map is invertible. For $v=V(T)$ its inverse is

$$
r=v_1,\qquad
p=\frac{v_3-v_2}{2}-2r,\qquad
s=\frac{(v_4-v_3)/m-3(v_2-v_1)}2,\qquad
q=v_2-v_1-s.
$$

Indeed $v_3-v_2=2p+4r$, $v_4-v_3=m(3q+5s)$, and $v_2-v_1=q+s$, which verify all four recovered entries. The only divisors are the fixed positive numbers $2,m$.

Thus $C_j-I$ span the four-dimensional matrix space under the nondegenerate trace pairing. The five matrices $I,C_1,C_2,C_3,C_4$ have rank four and satisfy

$$
-2I+C_1+4C_2+(1/m-1)C_3-(1/m)C_4=0.
$$

To check the relation, use $C_4=C_3+m(\begin{smallmatrix}0&0\\3&5\end{smallmatrix})$; the expression reduces entrywise to zero. Rank four makes this dependence unique up to scale. Every coefficient is nonzero for $m\ge2$, so any four of these five matrices are independent. Deleting a tail read leaves $I$ and three other tails. Deleting a noninitial baseline repeat, when one exists, leaves an $I$ and all four tails. These are precisely all single noninitial deletions, and each surviving span has dimension four.

At slope zero the quotient map $\mathcal B$ of Section 2 is invertible for this history. If $\mathcal B(T)=0$, Lemma 2.1 says the signal vector equals the values of a polynomial $P\in\mathcal P_d$. Its first $d+1$ values are the constant $a=\operatorname{tr}T$, so polynomial uniqueness gives $P=a$. The four tail values then give $V(T)=0$, hence $T=0$. A linear map between two four-dimensional spaces with zero kernel is invertible.

Define the comparison operator

$$
N_0=V^{-1}W,\qquad W_j(T)=j\operatorname{tr}(C_jT),
$$

and set

$$
E=V^{-1}(1,2,3,4)
=\begin{pmatrix}
-3/2&(5-1/m)/2\\
1&(1/m-3)/2
\end{pmatrix}.
$$

Substitution into the inverse of $V$ verifies $E$. Since $\operatorname{tr}(C_jT)=V_j(T)+a$,

$$
V^{-1}\operatorname{diag}(1,2,3,4)V(T)=N_0(T)-aE.
$$

For $d\ge1$ put

$$
N_d=d\operatorname{Id}+N_0-(\operatorname{tr}\,\cdot)E
=V^{-1}\operatorname{diag}(d+1,d+2,d+3,d+4)V.
$$

For $d=0$, the entries of $\mathcal L(N_0T)-\mathcal I\mathcal L(T)$ all equal $\operatorname{tr}(N_0T)$: at index zero this is immediate, and at index $j$ it follows from $V_j(N_0T)=j\operatorname{tr}(C_jT)$. For $d\ge1$, writing $a_N=\operatorname{tr}(N_dT)$, the entries of $\mathcal L(N_dT)-\mathcal I\mathcal L(T)$ equal $a_N-ia$. This holds at each baseline index and at each tail index $i=d+j$, where $V_j(N_dT)=iV_j(T)$ cancels the residual. The respective differences are constant or affine, of degree at most $d$. Applying $\Lambda$ yields

$$
\mathcal B N_d=\mathcal C
$$

in both cases, with $N_d=N_0$ when $d=0$. Consequently the transfer operator $\mathcal H=\mathcal B^{-1}\mathcal C$ at slope zero is exactly this $N_d$.

Consider the actual rank-one sources

$$
S(y)=\begin{pmatrix}1&y\\1&y\end{pmatrix}
=(1,1)^{\mathsf T}(1,y),\qquad y>0.
$$

For completeness, the vector used to compute $N_0$ at a general matrix is

$$
W(T)=\bigl(p+r+s,\ 2p+2q+2r+4s,
9p+3q+15r+6s,
12p+4(3m+1)q+20r+4(5m+2)s\bigr).
$$

Using the displayed inverse of $V$ gives the following entries on $S(y)$:

| Entry | $N_0(S(y))$ | $(N_0-(\operatorname{tr}\,\cdot)E)(S(y))$ |
| --- | --- | --- |
| $11$ | $6-y/2$ | $15/2+y$ |
| $21$ | $2+y$ | $1$ |
| $22$ | $4/m-3+(17/2+3/(2m))y$ | $7/(2m)-3/2+(10+1/m)y$ |
| $12$ | $5-4/m-(7/2+3/(2m))y$ | $5/2-7/(2m)-(6+1/m)y$ |

The second column of values follows from subtracting $(1+y)E$. For $S(y)$ the mixed determinant is $yN_{11}+N_{22}-N_{12}-yN_{21}$. Thus

$$
Q_{N_0}(S(y))=Q_0(y)
=8/m-8+(16+3/m)y-\frac32y^2.
$$

The mixed determinant of $dS(y)$ with $S(y)$ is $2d\det S(y)=0$. Therefore for every $d\ge1$,

$$
Q_{N_d}(S(y))=Q_1(y)
=7/m-4+(45/2+2/m)y+y^2.
$$

For all $m\ge2$ these have opposite signs at the same positive endpoints:

$$
\begin{aligned}
Q_0(1/100)&\le-4+\frac{35}{200}<0,
&Q_0(1)&=13/2+11/m>0,\\
Q_1(1/100)&\le-1/2+\frac{47}{200}+\frac1{10000}
=-\frac{2649}{10000}<0,
&Q_1(1)&=39/2+9/m>0.
\end{aligned}
$$

These follow from $1/m\le1/2$; the negative quadratic term of $Q_0$ was discarded only for its upper bound. They prove the sign-change hypothesis of Theorem 3.1 at slope zero for every member of the family.

We now give the sources and full observation equations explicitly. Write $N=N_0$ if $d=0$ and $N=N_d$ otherwise, and choose the corresponding $Q_0$ or $Q_1$. On the compact interval $[1/100,1]$ put

$$
K=1+\max_{y,a,b}|N(S(y))_{ab}|,
\qquad \eta=\min(-Q(1/100),Q(1))>0.
$$

Choose any

$$
0<\varepsilon<\min\left(\frac1{200K},\frac\eta{4K^2}\right).
$$

Every entry of $S(y)$ is at least $1/100$, so every entry of $S(y)+\varepsilon N(S(y))$ exceeds $1/200$. Also $|\det(N(S(y)))|\le2K^2$, so $Q(y)+\varepsilon\det(N(S(y)))$ retains its opposite strict endpoint signs. There is an interior $y_\varepsilon$ where it vanishes. Define

$$
S_1=S(y_\varepsilon),\qquad
S_0=S_1+\varepsilon N(S_1),\qquad
\kappa_0=0,\qquad\kappa_1=\varepsilon.
$$

The determinant expansion in Section 2 and the entrywise bound make both sources strictly positive of rank one. They are distinct: $(N_0(S_1))_{21}=2+y_\varepsilon>0$ for $d=0$, while $(N_d(S_1))_{21}=d+1>0$ for $d\ge1$. Hence $(S_0)_{21}>1=(S_1)_{21}$. Every sampled gain is $1$ or $1+\varepsilon i>0$.

Let $a_b=\operatorname{tr}S_b$. If $d=0$, use the single constant polynomials

$$
D_0(t)=0,\qquad D_1(t)=\varepsilon\operatorname{tr}(N_0(S_1)).
$$

The initial readings agree because $a_0=a_1+\varepsilon\operatorname{tr}(N_0(S_1))$. At each actual tail index $j=1,2,3,4$, the difference between run 0 and run 1 is

$$
\begin{aligned}
\operatorname{tr}(C_jS_0)
 -(1+\varepsilon j)\operatorname{tr}(C_jS_1)-D_1(j)
&=\varepsilon\bigl[
V_j(N_0(S_1))-j\operatorname{tr}(C_jS_1)\bigr]\\
&=0.
\end{aligned}
$$

Thus all five original equations hold with the same constant used throughout each run.

If $d\ge1$, use the single entire polynomials

$$
D_0(t)=-a_0,\qquad D_1(t)=-a_1(1+\varepsilon t).
$$

Their degrees are at most one and therefore at most $d$. All initial $I$ readings at indices $0,\ldots,d$ are zero in both runs. At actual tail index $i=d+j$ the observations are respectively

$$
V_j(S_0),\qquad (1+\varepsilon(d+j))V_j(S_1).
$$

They agree since $V_j(N_d(S_1))=(d+j)V_j(S_1)$. This checks every baseline and tail equation at its original clock index, with no per-sample choice of drift.

Finally take $\alpha_0=\alpha_1=1$, $\beta_0=0$, $\beta_1=\varepsilon$, and $R_b=S_b$. Run 1 has the explicit fixed positive factors $c_1=(1,1)^{\mathsf T}$ and $\ell_1=(1,y_\varepsilon)$. Run 0 has $c_0=(p_0,r_0)^{\mathsf T}$ and $\ell_0=(1,q_0/p_0)$; positivity and $p_0s_0=q_0r_0$ make their product exactly $S_0$. Each row remains fixed along the full chronological word list, and the atomic positivity formulas in Theorem 3.1 cover every unread state as well. These are two actual original-model runs with distinct effective sources and slopes. Their equality of observations is an additional ambiguity beyond the representation fibre. ∎

## 5. Relation to the existing obstructions and the unresolved target

Theorem 2.1 of [Affine-gain erasure, positive secants, and drift-kernel collisions](FIB_AFFINE_GAIN_ERASURE_SPAN_AND_POSITIVE_GAIN_COLLISIONS.md) gives the exact positive-secant cone. Its Theorems 3.1 and 4.1 give the prescribed-slope and polynomial-erasure criteria, and its Theorem 5.1 gives the single noninitial erasure matrix-span obstruction. Those results remain separate credited tools. The family of Theorem 4.1 passes that matrix-span test for every permitted deletion, and at slope zero its full matrix/drift map is injective. The new collision compares different slopes at this injective slice; it is not an application of a nonzero prescribed-slope kernel there.

The same companion's Theorems 7.1 and 8.1 treat its $U,F,G,H$ tail, while its Theorem 9.1 treats a different polynomial-erasure family. Theorem 4.1 here uses the $U,LU,U^2LU,L^mU^2LU$ tails, including a constant-drift subfamily with five distinct recorded matrices and positive gains. These additional excluded histories still constitute a proper family of all legal histories.

The six-read companion already supplies both the unrestricted constant-drift upper bound and a separate affine-drift example in which every prescribed-slope kernel is safe but different positive slopes collide. Neither result is claimed anew here. Theorem 3.1 adds a determinant sign test quantified over arbitrary $d+5$ histories at their invertible slopes, and Theorem 4.1 gives its infinite actual-history application.

For the broader common polynomial-gain model, Theorem 4.1 and Lemma 3.2 of [Common polynomial-gain shear calibration and erasure recovery](FIB_POLYNOMIAL_GAIN_SHEAR_CALIBRATION_AND_ERASURE_RECOVERY.md) already give $\max(k,d)+2k+4$ reads. Its Theorem 6.1 gives its scale fibre, and Theorem 8.1 and Corollary 8.2 give its specified-prefix continuation optimum. The affine target embeds at $k=1$ by

$$
R_0=\frac S{\operatorname{tr}S},\qquad
H(t)=(\operatorname{tr}S)(1+\kappa t),
$$

and conversely $S=H(0)R_0$, $\kappa=H'(0)/H(0)$ when $H(0)>0$. This is a correspondence of complete common-source targets. The broader polynomial-gain domain also permits $H(0)=0$, outside the present positive-intercept affine model. Its prefix optimum, like Theorem 4.1 of the affine recovery companion, is restricted to its specified prefix and does not settle all predetermined histories.

The original remaining target is unchanged: determine the sharp uniform number of exact scalar reads over every legal predetermined finite-word cumulative $M/J$ history, with a matching actual common-source inverse recovering the entire $(S,\kappa,D)$ for every real affine slope and every drift of degree at most $d$. The alternatives remain $5$ versus $6$ for $d=0$, and $d+5$ versus $d+6$ for every $d\ge1$. No history achieving the lower endpoint uniformly and no collision obstruction covering every history at that endpoint is established here.

The necessary sign condition does not classify singular quotient slopes or prove sufficiency at one-sided slopes. The infinite family does not exhaust histories, establish an adaptive lower bound, or give an optimal atom count. All statements concern exact scalar observations and ordinary conditional mathematical proofs. Read count, literal atomic-operation count, bit precision, elapsed time, and physical acquisition cost are distinct resources; the results assert no noisy-stability, empirical-learning, physical-resource, or external-priority conclusion.

## 追加锚（本行以下为增补区）

## 6. Determinant geometry and the common-source collision bridge

Continue with an arbitrary legal history at $n=d+5$ and the operators $\mathcal B,\mathcal C,\mathcal T_\kappa$ of Section 2. None of the following results restricts the finite words, their lengths, or empty-word repetitions. Define the symmetric bilinear form on the real matrix space by

$$
\mathfrak b(X,Y)=\det(X+Y)-\det X-\det Y.
$$

For $S=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$ this is

$$
\mathfrak b(S,Y)=sY_{11}+pY_{22}-rY_{12}-qY_{21},
\qquad \mathfrak b(X,X)=2\det X.
$$

Testing the four single-entry matrices shows that $\mathfrak b$ is nondegenerate. At a positive rank-one $S$, the source tangent space is

$$
\mathsf V_S=\{V:\mathfrak b(S,V)=0\}.
\tag{6.1}
$$

Indeed the determinant differential is the displayed nonzero functional, and the positive source chart $S=rE(x,y)$, with

$$
E(x,y)=\begin{pmatrix}x&xy\\1&y\end{pmatrix},
\qquad r,x,y>0,
$$

parametrizes exactly the positive part of its zero set. For any linear operator $H$ on matrices, put

$$
Q_H(S)=\mathfrak b(S,H(S)),\qquad R_H(S)=\det(H(S)).
$$

The determinant expansion of Section 2 is therefore
$\det(S+tH(S))=tQ_H(S)+t^2R_H(S)$ on this source domain.

We use the following common-source bridge for every quotient equality below. Given positive rank-one $S_0,S_1$ and slopes $\kappa_0,\kappa_1$ with
$\mathcal T_{\kappa_0}S_0=\mathcal T_{\kappa_1}S_1$, define

$$
u_i=(1+\kappa_0i)\operatorname{tr}(A_iS_0)
 -(1+\kappa_1i)\operatorname{tr}(A_iS_1).
$$

By Lemma 2.1, $\Lambda u=0$ means that one entire polynomial $P\in\mathcal P_d$ agrees with $u$ at every recorded position. Its explicit expression is

$$
P(t)=\sum_{h=0}^d u_h
 \prod_{\substack{0\le b\le d\\b\ne h}}\frac{t-b}{h-b}.
\tag{6.2}
$$

The node differences are nonzero; the product is one when $d=0$. Use $D_0=0,D_1=P$. Thus every original observation agrees, including a position where either affine gain vanishes. The quotient identity guarantees all $d+5$ equations, beyond the first $d+1$ interpolation nodes.

For each endpoint $S_a=(\begin{smallmatrix}p_a&q_a\\r_a&s_a\end{smallmatrix})$, the actual original parameters are

$$
R_a=S_a,\quad \alpha_a=1,\quad\beta_a=\kappa_a,
\qquad c_a=(p_a,r_a)^{\mathsf T},\quad
\ell_a=(1,q_a/p_a).
\tag{6.3}
$$

Positivity and $p_as_a=q_ar_a$ give $c_a\ell_a=S_a$ and
$\ell_a A_i c_a=\operatorname{tr}(A_iS_a)$. The fixed row $\ell_a$ is used at every read and unread state of its run. Each atom sends a positive column to a positive column:
$M(v_1,v_2)^{\mathsf T}=(v_2,v_1+v_2)^{\mathsf T}$ and
$J(v_1,v_2)^{\mathsf T}=(v_2,v_1)^{\mathsf T}$. This realizes the prescribed history with its actual recorded clock and the single polynomial $D_a$ throughout each run. Different slopes give distinct effective targets even if $S_0=S_1$. For same-slope collisions the positive-secant criterion supplies distinct sources. Equations (6.2)–(6.3) implement the credited quotient and realization interfaces; they introduce neither independent lifted sources nor per-read drift choices.

## 7. Strict sign at every regular quotient slope

**Theorem 7.1 (a zero of the transfer form obstructs recovery).** Fix a real $a$ such that $\mathcal T_a$ is invertible, and put $H=\mathcal T_a^{-1}\mathcal C$. If $Q_H(S_*)=0$ at any positive rank-one $S_*$, the prescribed history has two distinct actual effective targets with identical observations. Consequently a uniformly recovering history must satisfy, at every such slope, either

$$
Q_H(S)>0\quad\hbox{for every }S\in\mathcal R_+,
\qquad\hbox{or}\qquad
Q_H(S)<0\quad\hbox{for every }S\in\mathcal R_+.
\tag{7.1}
$$

This excludes zeros of a one-sided form as well as an identically zero form.

**Proof.** If $R_H(S_*)=0$, then for every sufficiently small nonzero $\varepsilon$ the matrix
$S_0=S_*+\varepsilon H(S_*)$ has positive entries and zero determinant. Set $S_1=S_*$. The exact transfer equality is

$$
\mathcal T_a S_0
 =\mathcal T_a S_1+\varepsilon\mathcal C S_1
 =\mathcal T_{a+\varepsilon}S_1.
\tag{7.2}
$$

The bridge of Section 6 gives the complete collision, including the case $H(S_*)=0$.

Suppose next that $R_H(S_*)\ne0$ and that $Q_H$ is not identically zero on $\mathcal R_+$. Choose $S_b$ with $q_b=Q_H(S_b)\ne0$ and write $\sigma=\operatorname{sign}(q_b)$. Connect $S_*$ to $S_b$ by linear interpolation of their three positive coordinates $(r,x,y)$. Along the resulting compact positive rank-one path $S(\theta)$ let $m>0$ be a common lower bound for its entries and put

$$
K=1+\max_{\theta,j,k}|H(S(\theta))_{jk}|.
$$

Choose any nonzero $\varepsilon$ of the sign specified by
$\operatorname{sign}(\varepsilon R_H(S_*))=-\sigma$, with

$$
|\varepsilon|<
\min\left(\frac{m}{2K},
 \frac{|q_b|}{2(1+|R_H(S_b)|)}\right).
$$

Then $F_\varepsilon(\theta)=Q_H(S(\theta))+\varepsilon R_H(S(\theta))$ has sign $-\sigma$ at zero and sign $\sigma$ at one. Continuity gives an interior zero. At that source $S_1$, put $S_0=S_1+\varepsilon H(S_1)$. Every entry of $S_0$ exceeds $m/2$, and its determinant is $\varepsilon F_\varepsilon=0$. Equality (7.2) again applies. This works for every sufficiently small magnitude of the specified sign, without assuming a nonzero derivative of $Q_H$ at its zero. In particular it applies to an interior minimum or maximum of a one-sided form.

It remains to treat a form that vanishes identically on $\mathcal R_+$. As a homogeneous quadratic polynomial in $(p,q,r,s)$ it then satisfies

$$
Q_H(X)=\rho\det X
\quad\hbox{for every real matrix }X
\tag{7.3}
$$

for some real $\rho$. To prove this identity, substitute $(p,q,r,s)=(x,xy,1,y)$ into its ten quadratic monomials:

$$
\begin{array}{c|cccccccccc}
 &p^2&q^2&r^2&s^2&pq&pr&ps&qr&qs&rs\\ \hline
 &x^2&x^2y^2&1&y^2&x^2y&x&xy&xy&xy^2&y .
\end{array}
$$

Only $ps$ and $qr$ coincide. A polynomial vanishing for every positive $x,y$ has all coefficients zero, by fixing one variable and applying the polynomial root bound in each variable. Thus the two coincident coefficients sum to zero and every other coefficient vanishes, proving (7.3).

Let $H^*$ denote the adjoint for $\mathfrak b$, defined by
$\mathfrak b(HX,Y)=\mathfrak b(X,H^*Y)$. It exists uniquely by nondegeneracy. Polarizing (7.3) gives

$$
\mathfrak b(X,HY)+\mathfrak b(HX,Y)
 =\rho\mathfrak b(X,Y),
\qquad H+H^*=\rho\operatorname{Id}.
\tag{7.4}
$$

In particular $H^*=\rho\operatorname{Id}-H$ commutes with $H$.

For sufficiently small nonzero $t$, define

$$
\gamma=1+\rho t,\qquad
t'=-\frac{t}{1+\rho t},\qquad
A_t=\operatorname{Id}+tH,\qquad
G=A_{t'}^{-1}A_t .
\tag{7.5}
$$

If $\rho\ne0$, require $|\rho t|<1$. Both $A_t$ and $A_{t'}$ are invertible near zero, and $\gamma\ne0$. Formula (7.4) gives
$A_{t'}=\gamma^{-1}A_t^*$, hence

$$
G=\gamma(A_t^*)^{-1}A_t,\qquad
G^*=\gamma A_t^*A_t^{-1},\qquad
G^*G=\gamma^2\operatorname{Id}.
$$

The last identity follows because all these factors commute. Therefore

$$
\det(GX)=\tfrac12\mathfrak b(GX,GX)
 =\tfrac12\mathfrak b(X,G^*GX)=\gamma^2\det X.
\tag{7.6}
$$

For any fixed $S\in\mathcal R_+$, $G$ tends to the identity as $t$ tends to zero. Thus $S'=GS$ is strictly positive and has determinant zero for all sufficiently small $t$. Moreover $t'\ne t$: equality for nonzero $t$ would force $\rho t=-2$, excluded by the stated smallness condition, and when $\rho=0$ one has $t'=-t$. This transformation of slopes is an involution, since
$1+\rho t'=1/(1+\rho t)$ and applying (7.5) again returns $t$.

Finally $\mathcal T_{a+t}=\mathcal T_a A_t$, so

$$
\mathcal T_{a+t'}S'
 =\mathcal T_a A_{t'}A_{t'}^{-1}A_tS
 =\mathcal T_{a+t}S.
$$

The bridge supplies actual runs with these different slopes and with the entire compensating drift. This argument does not require $\det(H(S))=0$ and covers $\rho=0$.

All possible zeros have now been excluded for a recovering history. The positive source domain is connected in $(r,x,y)$, so a continuous form with no zeros has one strict sign there. This proves (7.1). The opposite-strict-sign obstruction in Theorem 3.1 remains a credited result; the additional conclusions concern zeros and the explicit involution. ∎

## 8. Safe singular slopes and a transverse sign restriction

Write

$$
\mathcal C_{\mathrm{safe}}=
\left\{\begin{pmatrix}A&B_0\\C_0&E_0\end{pmatrix}:
 A,E_0\ge0,\ B_0,C_0\le0\right\}.
$$

The positive-secant and prescribed-slope criteria used here are Theorems 2.1 and 3.1 of [Affine-gain erasure, positive secants, and drift-kernel collisions](FIB_AFFINE_GAIN_ERASURE_SPAN_AND_POSITIVE_GAIN_COLLISIONS.md). Their matrix interpolation kernel is exactly $\ker\mathcal T_a$, by Lemma 2.1. A subspace contained in
$\mathcal C_{\mathrm{safe}}\cup(-\mathcal C_{\mathrm{safe}})$ has dimension at most one. We use those existing results without re-proving them.

**Theorem 8.1 (transverse zeros force different-slope collisions).** At a singular slope $a$, a uniformly recovering history must have $\operatorname{rank}\mathcal T_a=3$ and

$$
\ker\mathcal T_a=\mathbb R K,\qquad
K\in\mathcal C_{\mathrm{safe}}\setminus\{0\}.
\tag{8.1}
$$

Choose any nonzero covector $w$ with $w\mathcal T_a=0$, and define the linear functional

$$
h(S)=w(\mathcal C S)
 =h_pp+h_qq+h_rr+h_ss .
$$

If $h(S_*)=0$ at a positive rank-one source, there are actual different-slope collisions with slopes $a$ and $a+t$ for every sufficiently small nonzero $t$ of either sign. Thus recovery requires either that $(h_p,h_q,h_r,h_s)$ be all nonnegative and not all zero, or that they be all nonpositive and not all zero.

**Proof.** If $\operatorname{rank}\mathcal T_a\le2$, its kernel has dimension at least two and cannot lie in the safe cone union. If the rank is three but the kernel line is unsafe, it already contains a nonzero positive secant. In both cases the credited prescribed-slope criterion supplies an actual same-slope collision. Its matrix difference has a polynomial compensator by Lemma 2.1; Section 6 supplies the entire drifts and actual positive factors. Hence only (8.1) can remain.

Now suppose (8.1) holds and set $S=S_*$. The range of $\mathcal T_a$ equals $\ker w$, since inclusion holds and both have dimension three. The condition $h(S)=0$ therefore gives a real matrix $X$ with

$$
\mathcal T_a X=\mathcal C S.
\tag{8.2}
$$

Explicitly, choose three matrices whose images form a basis of the range, express $\mathcal C S$ in that basis, and use the same coefficients on those matrices. No singular inverse is used.

For $K=(\begin{smallmatrix}A&B_0\\C_0&E_0\end{smallmatrix})$, positivity of $S$ gives

$$
v=\mathfrak b(S,K)=sA+pE_0-rB_0-qC_0>0,
\tag{8.3}
$$

because all four terms are nonnegative and some entry of $K$ is nonzero. Put $m=\min_{j,k}S_{jk}>0$. Choose $\eta>0$ with
$\eta\max|K_{jk}|<m/4$ and $\eta|\det K|<v/2$; the latter bound is automatic if $\det K=0$. Then

$$
\det(S+\eta K)>\eta v/2>0,\qquad
\det(S-\eta K)<-\eta v/2<0.
$$

For every sufficiently small $|t|$, these endpoint signs persist for
$\det(S+tX+\eta K)$ and $\det(S+tX-\eta K)$. Also require
$|t|\max|X_{jk}|<m/4$, which imposes no restriction if $X=0$. Every
$S+tX+\lambda K$, $-\eta\le\lambda\le\eta$, then has entries greater than $m/2$. Continuity in $\lambda$ gives a value $\lambda(t)$ making its determinant zero. Set

$$
S_0=S+tX+\lambda(t)K,\quad S_1=S,\quad
\kappa_0=a,\quad\kappa_1=a+t .
$$

Both sources are positive rank one, and (8.1)–(8.2) yield

$$
\mathcal T_a S_0
 =\mathcal T_a S+t\mathcal C S
 =\mathcal T_{a+t}S_1.
$$

For each nonzero $t$ the slopes differ. Equations (6.2)–(6.3) realize every observation, including any sampled gain zero, with one entire polynomial and one fixed positive row in each run.

For completeness, a linear functional has no zero on $\mathcal R_+$ exactly when its four entry coefficients have one weak sign and are not all zero. Evaluate it on $E(x,y)$. The limits

$$
\begin{aligned}
h(E(\varepsilon,\varepsilon))&\longrightarrow h_r,\\
h(E(T,T))/T^2&\longrightarrow h_q,\\
h(E(T,T^{-2}))/T&\longrightarrow h_p,\\
h(E(T^{-2},T))/T&\longrightarrow h_s
\end{aligned}
$$

isolate each nonzero coefficient, with $\varepsilon\downarrow0$ and $T\to\infty$. Mixed signs therefore give both signs on positive sources and a zero along a positive-coordinate path. All zero coefficients give zeros everywhere. Conversely one nonzero coefficient and a common weak sign give a strict sign at every source because all source entries are positive. Applying this equivalence to $h$ proves the coefficient requirement, which is invariant under nonzero rescaling of $w$. ∎

**Proposition 8.2 (the local meaning of the transverse test).** Under (8.1), the derivative of
$f(S,\kappa)=\mathcal T_\kappa S$ on the source/slope domain is nonsingular at $(S,a)$ exactly when $h(S)\ne0$.

**Proof.** By (6.1) and (8.3), $K$ is not in the source tangent space $\mathsf V_S$. Thus $\mathcal T_a$ restricts injectively from this three-dimensional space onto its three-dimensional range. The derivative is

$$
(V,t)\longmapsto\mathcal T_a V+t\mathcal C S,\qquad V\in\mathsf V_S.
$$

Its first three dimensions give precisely that range. It is invertible exactly when $\mathcal C S$ lies outside the range, or equivalently when $w(\mathcal C S)\ne0$. Together with (8.1), the coefficient condition of Theorem 8.1 characterizes nonsingularity at every source on this singular slice. It asserts local derivative nonsingularity, without a global inverse. ∎

## 9. Actual-target critical points and an exact quadratic obstruction

**Theorem 9.1 (a critical point forces noninjectivity in this model).** For any legal $n=d+5$ history, if the full observation map on the actual target chart has a singular derivative at any allowed target, that history admits two distinct actual effective targets with identical observations. Consequently a uniformly recovering endpoint history must have an everywhere nonsingular derivative and be a local smooth diffeomorphism at every target. The collision need not pass through the particular critical target.

**Proof.** Use the actual chart

$$
(r,x,y,\kappa,\delta_0,\ldots,\delta_d),\quad
r,x,y>0,\qquad
S=rE(x,y),\quad D(t)=\sum_{j=0}^d\delta_jt^j .
$$

It parametrizes the target injectively; Section 6 realizes every chart point with positive factors. Apply to the output vector the fixed linear map

$$
v\longmapsto(v_0,\ldots,v_d,\Lambda v).
\tag{9.1}
$$

This is an isomorphism. Its kernel is zero: Lemma 2.1 gives $v=\operatorname{ev}(P)$, and its first $d+1$ zero entries force $P=0$ by interpolation. Its domain and codomain both have dimension $d+5$.

In these output coordinates, drift appears only in the first $d+1$ components. Its derivative block there is the invertible evaluation map for degree-at-most-$d$ polynomials at $0,\ldots,d$. The last four components equal $f(S,\kappa)=\mathcal T_\kappa S$. Ordering the drift coordinates first makes the derivative block triangular. Hence the full derivative is singular exactly when the four-dimensional derivative of $f$ is singular.

Fix the slope $a$ of such a point. If $\mathcal T_a$ is invertible, the kernel equation for the quotient derivative is

$$
\mathcal T_a V+t\mathcal C S=0,\quad V\in\mathsf V_S,
\qquad\hbox{equivalently}\qquad V=-tH(S).
$$

A nonzero kernel vector must have $t\ne0$. Equation (6.1) then says exactly $Q_H(S)=0$, and Theorem 7.1 supplies a collision in every branch of that condition.

If $\mathcal T_a$ has rank at most two or an unsafe kernel line, the prescribed-slope criterion used in Theorem 8.1 already gives a collision. The only remaining case has rank three and a safe kernel line. Proposition 8.2 says that a singular quotient derivative there means $h(S)=0$, and Theorem 8.1 supplies a different-slope collision. These cases exhaust all quotient ranks and kernels. Every collision uses the complete Section 6 bridge. The inverse function theorem gives the asserted local diffeomorphism when the derivative is nonsingular. This argument uses the determinant and pencil structure of this model; it is not a theorem about arbitrary smooth injective maps. ∎

For $E=E(x,y)$ define

$$
E_x=\begin{pmatrix}1&y\\0&0\end{pmatrix},
\qquad
E_y=\begin{pmatrix}0&x\\0&1\end{pmatrix}.
$$

The symbol $\det_4$ below is the determinant of four quotient vectors as columns; it is distinct from the two-by-two source determinant. Put

$$
\begin{aligned}
c(x,y)&=\det_4[\mathcal B E,\mathcal B E_x,\mathcal B E_y,\mathcal C E],\\
b_1(x,y)&=\det_4[\mathcal B E,\mathcal C E_x,\mathcal B E_y,\mathcal C E]\\
&\quad+\det_4[\mathcal B E,\mathcal B E_x,\mathcal C E_y,\mathcal C E],\\
a_2(x,y)&=\det_4[\mathcal B E,\mathcal C E_x,\mathcal C E_y,\mathcal C E].
\end{aligned}
\tag{9.2}
$$

**Theorem 9.2 (quadratic no-real-root requirement).** Every uniformly recovering $n=d+5$ history must satisfy, for each $x,y>0$, exactly one of the alternatives

$$
a_2=b_1=0,\quad c\ne0,
\qquad\hbox{or}\qquad
a_2\ne0,\quad b_1^2-4a_2c<0.
\tag{9.3}
$$

Moreover $c$ has one common strict sign over all positive source shapes, and every nonzero $a_2$ has that same sign. Failure of (9.3) at one positive shape gives an actual collision on that history. Satisfying (9.3) at every shape is equivalent to an everywhere nonsingular actual-target derivative; it is a necessary condition for recovery.

**Proof.** The vectors $E,E_x,E_y$ are independent: their $21$, then $11$, then $22$ entries force the coefficients in a zero linear combination to vanish successively. They span the three-dimensional source tangent in (6.1), with the appropriate nonzero factors of $r$.

In chart order $(r,x,y,\kappa)$ the four quotient derivative columns are

$$
\mathcal T_\kappa E,\qquad
r\mathcal T_\kappa E_x,\qquad
r\mathcal T_\kappa E_y,\qquad r\mathcal C E.
$$

Factoring out $r^3$ and subtracting $\kappa$ times the last column from the first gives

$$
\begin{aligned}
\det Df
&=r^3\det_4[\mathcal B E,
 (\mathcal B+\kappa\mathcal C)E_x,
 (\mathcal B+\kappa\mathcal C)E_y,\mathcal C E]\\
&=r^3\bigl(c+b_1\kappa+a_2\kappa^2\bigr).
\end{aligned}
\tag{9.4}
$$

Thus the apparent cubic term vanishes exactly, without an invertibility assumption on any $\mathcal T_\kappa$.

For a fixed positive shape, write $j(\kappa)=c+b_1\kappa+a_2\kappa^2$. If $a_2=0$ and $b_1\ne0$, it has the root $-c/b_1$. If $a_2=b_1=0$, it has no real root precisely when $c\ne0$; otherwise it is the zero polynomial. If $a_2\ne0$, its real roots exist exactly when the discriminant
$\Delta=b_1^2-4a_2c$ is nonnegative, and are
$(-b_1\pm\sqrt{\Delta})/(2a_2)$. This includes a repeated root when $\Delta=0$. When $\Delta<0$, completing the square gives
$4a_2j(\kappa)=(2a_2\kappa+b_1)^2-\Delta>0$, so there is no real root. These are all degree and discriminant degeneracies, proving that (9.3) is exactly the no-real-root condition.

Theorem 9.1 and (9.4) require this condition for recovery. Conversely, if it fails at a positive shape, choose one of the real roots just described, any $r>0$, and any allowed drift. The full derivative at that actual target is singular by (9.1)–(9.4). The exhaustive cases of Theorem 9.1 produce a collision with the actual positive factors and drift compensation of Section 6.

If (9.3) holds for every shape, (9.4) and the invertible drift block show that the full derivative is everywhere nonsingular. The function
$j(\kappa;x,y)$ is continuous and nonzero on the connected domain
$\mathbb R\times(0,\infty)^2$, so its sign is common throughout. In particular $c=j(0;x,y)$ has a common strict sign. Wherever $a_2\ne0$, the sign for large $|\kappa|$ equals the sign of $a_2$, giving the stated agreement with $c$. These conclusions also cover singular or identically singular quotient pencils through the rank cases of Theorem 9.1. They do not supply global injectivity. ∎

## 10. Credits, conditions, and the surviving endpoint problem

Theorem 3.1 supplies the existing opposite-strict-sign obstruction. Theorem 7.1 strengthens it by excluding every positive-source zero at an invertible slope, including a one-sided zero and the identically zero case. Theorem 8.1 treats singular slopes: rank at most two or an unsafe line reuses the existing prescribed-slope criterion, while the safe rank-three case acquires a further transverse sign requirement. Theorems 9.1–9.2 combine these branches into an all-history critical-point obstruction and the exact quadratic requirement (9.3). These results range over every legal minimum-length history at their stated hypotheses; no additional excluded tail family replaces that quantifier.

The exact quotient and transfer are those of Section 2. The positive-secant and safe-subspace results, actual positive factorization, and prescribed-slope collision criterion are credited to Proposition 1.1 and Theorems 2.1 and 3.1 of [Affine-gain erasure, positive secants, and drift-kernel collisions](FIB_AFFINE_GAIN_ERASURE_SPAN_AND_POSITIVE_GAIN_COLLISIONS.md). They are consumed in Section 8 and the singular branches of Section 9; their old proofs and excluded families are not repeated here. Equations (6.2)–(6.3) apply their realization interface to every new quotient collision.

The upper and lower numerical bounds retain their credited sources. Theorems 2.1 and 5.1 of [Shared affine gain and zero-crossing recovery](FIB_SHARED_AFFINE_GAIN_ZERO_CROSSING_RECOVERY.md) give the affine upper bound $\max(d+6,7)$ and all-fixed-history lower bound $d+5$. Its Theorem 4.1 concerns its specified baseline/shear prefix. Theorem 2.1 and Proposition 2.2 of [Affine six-read recovery and unknown-slope collisions](FIB_AFFINE_SIX_READ_RECOVERY_AND_UNKNOWN_SLOPE_COLLISIONS.md) give the six-read constant-drift construction and its compatibility test. Its prescribed-slope safe-line inverse and different-positive-slope collisions remain separate path-specific results.

Theorem 4.1 and Lemma 3.2 of [Common polynomial-gain shear calibration and erasure recovery](FIB_POLYNOMIAL_GAIN_SHEAR_CALIBRATION_AND_ERASURE_RECOVERY.md) give the broader common polynomial-gain construction, with its positive-scale fibre and specified-prefix optimum in Theorems 6.1 and 8.1. On the affine restriction its target conversion is
$R_0=S/\operatorname{tr}S$ and
$H(t)=(\operatorname{tr}S)(1+\kappa t)$, with inverse
$S=H(0)R_0$, $\kappa=H'(0)/H(0)$, and $H(0)>0$.
These are correspondences of entire common-source targets. The references to the original self-calibrating source in Sections 1 and 5 remain credits with their stated scopes.

The original numerical alternatives are unchanged:

$$
5\le C_{\mathrm{fix}}(0)\le6,\qquad
d+5\le C_{\mathrm{fix}}(d)\le d+6\quad(d\ge1).
$$

The unresolved target is a sharp uniform count over all predetermined finite-word cumulative histories, with a legal attaining history and a common-source inverse for every real affine slope and the entire degree-at-most-$d$ drift. No endpoint construction or universal endpoint collision obstruction is established here.

More precisely, the surviving regular-slope residual consists of transfer forms strictly of one sign on all positive rank-one sources. The singular residual consists of rank-three slopes with a safe kernel line and a transverse functional whose entry coefficients have one weak sign and are not all zero. A candidate must meet these requirements simultaneously at all slopes and satisfy (9.3) at every positive source shape. These results neither show that a legal history satisfies all of them nor eliminate distant different-slope collisions for a history that does. Everywhere local derivative nonsingularity does not give a global common-source inverse.

All statements keep strict positive rank one, one fixed positive row per run, the known $M,J$, every finite cumulative word including the empty word, the actual recorded-reading index, arbitrary real slopes, and one entire allowed drift polynomial. Sampled gain zeros and negative gains are included by the undivided equations in Section 6. The representation scales remain exactly those of Section 1. These ordinary conditional proofs assert no independent review or Lean certification, adaptive lower bound, optimal atom count, bit-precision bound, noisy stability, physical acquisition claim, empirical-learning consequence, external priority, or completion of the programme.

## 追加锚（本行以下为增补区）
