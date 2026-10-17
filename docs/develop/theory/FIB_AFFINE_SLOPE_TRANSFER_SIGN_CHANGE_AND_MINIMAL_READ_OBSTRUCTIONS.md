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
