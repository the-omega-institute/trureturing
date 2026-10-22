# An exact cubic matrix-polynomial frame at the literal atomic clock

## 1. Original worlds, clock, and prefix

**Definition 1.1 (original world).** Let

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

An original world is a triple

$$
W=(P,g,d),\qquad
P=P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
\quad 0<r<1,\quad b>0,\quad d\in\mathbb R,
\quad 0\ne g\in\mathbb R[t],\quad\deg g\le3.
$$

Equivalently, $P$ has four strictly positive entries, determinant zero and trace one. Indeed trace one gives $P_{22}=1-P_{11}$, positivity gives $0<P_{11}<1$ and $P_{12}>0$, and determinant zero gives the displayed $P_{21}$. These are the worlds of [An exact unequal-diagonal pair for the original terminal M response, Definition 1.1](FIB_STRICT_REAL_UNEQUAL_DIAGONAL_ACTUAL_M_PAIR.md).

At known absolute atomic clock $t$, with cumulative left multiplier $Q$, the reading is

$$
y=d+g(t)\operatorname{tr}(QP).
$$

Every atom is either $J$ or $M$, advances the clock by one and is immediately read. One world uses the same $P$, whole polynomial $g$ and constant $d$ throughout its history and all terminal responses. The allowed acquisition has no reset, copy, additional port, unread atom, physical inverse, skipped reading or empty-word clock advancement. Lower gain degrees, repeated roots, vanishing gain samples, either gain sign and zero drift belong to the domain.

**Definition 1.2 (continuation coordinates).** Fix a known invertible matrix $Q_0$ and a known clock $t_0$. For chronological continuation atoms $E_1,\ldots,E_{16}$ set

$$
A_0=I,\qquad A_i=E_iA_{i-1},\qquad
Y_i=d+g(t_0+i)\operatorname{tr}(A_iQ_0P),\quad 0\le i\le16.
$$

For an acquired legal prefix, $t_0$ is its nonnegative integer length and $Y_0$ is its already acquired current reading. The algebraic continuation equations also make sense for any specified invertible real $Q_0$ and real $t_0$; that extension does not assert legal attainability of an arbitrary matrix.

## 2. A completely explicit observation matrix

**Definition (ambient observations).** 
Write the matrix polynomial as

$$
Z(s)=Z_0+sZ_1+s^2Z_2+s^3Z_3,\qquad
Z_j=\begin{pmatrix}z_{j,11}&z_{j,12}\\z_{j,21}&z_{j,22}\end{pmatrix}.
$$

For this section the sixteen entries of the four $Z_j$ and $d$ are independent real unknowns. The coefficient column, in its exact order, is

$$
x=(d,\ z_{0,11},z_{0,12},z_{0,21},z_{0,22}, z_{1,11},z_{1,12},z_{1,21},z_{1,22}, z_{2,11},z_{2,12},z_{2,21},z_{2,22}, z_{3,11},z_{3,12},z_{3,21},z_{3,22})^{\mathsf T}.
$$

For $A=\left(\begin{smallmatrix}a&b\\c&e\end{smallmatrix}\right)$ define the trace-pairing row

$$
v(A)=(a,c,b,e),\qquad
\operatorname{tr}(AZ_j)=a z_{j,11}+c z_{j,12}+b z_{j,21}+e z_{j,22}.
$$

Thus $v(A)$ is the transpose-flattening of $A$ paired with the row-major flattening of $Z_j$; the off-diagonal entries are interchanged exactly as the trace requires. The scalar equation at local clock $i$ is

$$
Y_i=d+\operatorname{tr}(A_iZ(i))=C_i x,\qquad
C_i=(1,\ v(A_i),\ i\,v(A_i),\ i^2v(A_i),\ i^3v(A_i)).
$$

Here $i^0=1$, including at $i=0$. The seventeen scalar equations are printed below by their complete seventeen-entry rows.

**Theorem 2.1 (literal cubic frame).** The chronological atom word is

$$
(E_1,\ldots,E_{16})=(J,M,M,J,J,J,M,M,M,J,J,M,J,M,M,M).
$$

Equivalently the chronological letter string is `JMMJJJMMMJJMJMMM`; the cumulative multiplier is $E_{16}\cdots E_1$. Its prefixes and observation matrix are as follows.

| $i$ | atom $E_i$ | $(A_{i,11},A_{i,12},A_{i,21},A_{i,22})$ |
|---:|:---:|:---|
| 0 | I (current) | (1, 0, 0, 1) |
| 1 | J | (0, 1, 1, 0) |
| 2 | M | (1, 0, 1, 1) |
| 3 | M | (1, 1, 2, 1) |
| 4 | J | (2, 1, 1, 1) |
| 5 | J | (1, 1, 2, 1) |
| 6 | J | (2, 1, 1, 1) |
| 7 | M | (1, 1, 3, 2) |
| 8 | M | (3, 2, 4, 3) |
| 9 | M | (4, 3, 7, 5) |
| 10 | J | (7, 5, 4, 3) |
| 11 | J | (4, 3, 7, 5) |
| 12 | M | (7, 5, 11, 8) |
| 13 | J | (11, 8, 7, 5) |
| 14 | M | (7, 5, 18, 13) |
| 15 | M | (18, 13, 25, 18) |
| 16 | M | (25, 18, 43, 31) |

The following array is $C$ in row order $i=0,\ldots,16$. Each line is the full coefficient row of the scalar equation $Y_i=C_i x$; the vertical grouping is the intercept followed by four blocks of four entries.

| $i$ | intercept | $v(A_i)$ | $i v(A_i)$ | $i^2v(A_i)$ | $i^3v(A_i)$ |
|---:|---:|:---|:---|:---|:---|
| 0 | $1$ | $1, 0, 0, 1$ | $0, 0, 0, 0$ | $0, 0, 0, 0$ | $0, 0, 0, 0$ |
| 1 | $1$ | $0, 1, 1, 0$ | $0, 1, 1, 0$ | $0, 1, 1, 0$ | $0, 1, 1, 0$ |
| 2 | $1$ | $1, 1, 0, 1$ | $2, 2, 0, 2$ | $4, 4, 0, 4$ | $8, 8, 0, 8$ |
| 3 | $1$ | $1, 2, 1, 1$ | $3, 6, 3, 3$ | $9, 18, 9, 9$ | $27, 54, 27, 27$ |
| 4 | $1$ | $2, 1, 1, 1$ | $8, 4, 4, 4$ | $32, 16, 16, 16$ | $128, 64, 64, 64$ |
| 5 | $1$ | $1, 2, 1, 1$ | $5, 10, 5, 5$ | $25, 50, 25, 25$ | $125, 250, 125, 125$ |
| 6 | $1$ | $2, 1, 1, 1$ | $12, 6, 6, 6$ | $72, 36, 36, 36$ | $432, 216, 216, 216$ |
| 7 | $1$ | $1, 3, 1, 2$ | $7, 21, 7, 14$ | $49, 147, 49, 98$ | $343, 1029, 343, 686$ |
| 8 | $1$ | $3, 4, 2, 3$ | $24, 32, 16, 24$ | $192, 256, 128, 192$ | $1536, 2048, 1024, 1536$ |
| 9 | $1$ | $4, 7, 3, 5$ | $36, 63, 27, 45$ | $324, 567, 243, 405$ | $2916, 5103, 2187, 3645$ |
| 10 | $1$ | $7, 4, 5, 3$ | $70, 40, 50, 30$ | $700, 400, 500, 300$ | $7000, 4000, 5000, 3000$ |
| 11 | $1$ | $4, 7, 3, 5$ | $44, 77, 33, 55$ | $484, 847, 363, 605$ | $5324, 9317, 3993, 6655$ |
| 12 | $1$ | $7, 11, 5, 8$ | $84, 132, 60, 96$ | $1008, 1584, 720, 1152$ | $12096, 19008, 8640, 13824$ |
| 13 | $1$ | $11, 7, 8, 5$ | $143, 91, 104, 65$ | $1859, 1183, 1352, 845$ | $24167, 15379, 17576, 10985$ |
| 14 | $1$ | $7, 18, 5, 13$ | $98, 252, 70, 182$ | $1372, 3528, 980, 2548$ | $19208, 49392, 13720, 35672$ |
| 15 | $1$ | $18, 25, 13, 18$ | $270, 375, 195, 270$ | $4050, 5625, 2925, 4050$ | $60750, 84375, 43875, 60750$ |
| 16 | $1$ | $25, 43, 18, 31$ | $400, 688, 288, 496$ | $6400, 11008, 4608, 7936$ | $102400, 176128, 73728, 126976$ |

Its exact determinant is

$$
\boxed{\det C=2064008635379195904\ne0.}
$$

**Proof (integer-preserving elimination).** Left multiplication acts on the entry tuple by

$$
J(a,b,c,e)=(c,e,a,b),\qquad
M(a,b,c,e)=(c,e,a+c,b+e).
$$

Starting at $(1,0,0,1)$, these formulas give every row of the prefix table; inserting $v(A_i)$ and the powers of $i$ gives every printed scalar row.

Use indices starting at zero and the classical fraction-free elimination recurrence of E. H. Bareiss, “Sylvester’s Identity and Multistep Integer-Preserving Gaussian Elimination”, *Mathematics of Computation* 22 (1968), 565–578, [doi:10.1090/S0025-5718-1968-0226829-0](https://doi.org/10.1090/S0025-5718-1968-0226829-0). Its determinant identity is proved below. Let $B^{(0)}=C$ and $p_{-1}=1$. For $k=0,\ldots,15$, put $p_k=B^{(k)}_{kk}$ and, for $i,j>k$, set

$$
B^{(k+1)}_{ij}
=\frac{p_kB^{(k)}_{ij}-B^{(k)}_{ik}B^{(k)}_{kj}}{p_{k-1}}.
$$

Only the active trailing submatrix is needed. No row or column permutation is used. The complete pivot list, including $p_{16}=B^{(16)}_{16,16}$, is

| $k$ | $p_k$ |
|---:|---:|
| 0 | $1$ |
| 1 | $-1$ |
| 2 | $-1$ |
| 3 | $-1$ |
| 4 | $1$ |
| 5 | $2$ |
| 6 | $-12$ |
| 7 | $36$ |
| 8 | $-24$ |
| 9 | $-768$ |
| 10 | $342280$ |
| 11 | $-3591520$ |
| 12 | $69120$ |
| 13 | $8151452928$ |
| 14 | $22333707680256$ |
| 15 | $-16054581032128512$ |
| 16 | $2064008635379195904$ |

All divisions in this recurrence are exact integer divisions and every pivot is nonzero. To establish the determinant identity, let $\Delta_k$ denote the determinant of the leading $k$-by-$k$ block of $C$, with $\Delta_0=1$. Inductively, each active $B^{(k)}_{ij}$ is the bordered minor with ordered rows $(0,\ldots,k-1,i)$ and ordered columns $(0,\ldots,k-1,j)$. The identity

$$
\Delta_k\det C[(0,\ldots,k,i),(0,\ldots,k,j)]
=B^{(k)}_{kk}B^{(k)}_{ij}-B^{(k)}_{ik}B^{(k)}_{kj}
$$

follows by eliminating the invertible leading $k$-by-$k$ block: both sides are $\Delta_k^2$ times the determinant of the same two-by-two Schur complement. For $k=0$ it is the two-by-two determinant identity. Since $p_{k-1}=\Delta_k$, the recurrence gives exactly these bordered minors and $p_k=\Delta_{k+1}$. The displayed nonzero pivots justify every elimination and the final entry is $\Delta_{17}=\det C$, with no permutation sign.

Consequently $C$ is invertible over $\mathbb Q$ and $\mathbb R$. The full ambient inverse is explicitly

$$
\boxed{x=C^{-1}Y=\frac{\operatorname{adj}(C)Y}{2064008635379195904}.}
$$

The adjugate formula, together with every entry of $C$ above, specifies every recovered coefficient without any unprinted data. It proves recovery for arbitrary four matrix coefficients and any intercept, independently of positivity, rank, a common gain, or a specified nonzero gain sample. ∎

## 3. Known-prefix and absolute-time transport

**Theorem 3.1 (original-world reconstruction).** For every world of Definition 1.1, every known invertible $Q_0$ and every known $t_0$, the seventeen equations of Theorem 2.1 determine $(P,g,d)$ uniquely.

**Proof.** Define

$$
h(s)=g(t_0+s)=\sum_{j=0}^3h_js^j,\qquad
Z_j=h_jQ_0P.
$$

Then $Y_i=d+\operatorname{tr}(A_i\sum_j i^jZ_j)$. The ambient inverse of Theorem 2.1 returns the actual $d,Z_0,\ldots,Z_3$. Set

$$
B_j=Q_0^{-1}Z_j,\qquad h_j=\operatorname{tr}B_j.
$$

Since $B_j=h_jP$ and $\operatorname{tr}P=1$, these are the actual shifted gain coefficients. Translation is invertible on polynomials, so $h\not\equiv0$. Choose the smallest $k$ with $h_k\ne0$ and recover

$$
\boxed{P=B_k/h_k,\qquad r=P_{11},\quad b=P_{12},\qquad
 g(t)=\sum_{j=0}^3h_j(t-t_0)^j.}
$$

Every possible nonzero coefficient gives the same $P$. Explicitly, if $g(t)=\sum_{a=0}^3g_at^a$, then

$$
g_a=\sum_{j=a}^3\binom ja h_j(-t_0)^{j-a}.
$$

These formulas are a left inverse, hence prove uniqueness as well as recovery. The drift is the recovered intercept. The inverse $Q_0^{-1}$ is used only as decoder arithmetic. The use of a nonzero recovered coefficient, rather than a prescribed gain sample, is the coefficient normalization already used in [FIB self-calibrating relation mathematics, Theorem 39.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md). ∎

**Proposition 3.2 (ambient coordinate changes).** If the four ambient coefficients are instead $U_j$ with $Z_j=Q_0U_j$, their observation determinant is

$$
2064008635379195904\,(\det Q_0)^8.
$$

Replacing local polynomial coefficients by absolute polynomial coefficients preserves invertibility.

**Proof.** Left multiplication by $Q_0$ acts independently on the two columns of a matrix and has determinant $(\det Q_0)^2$ on $\operatorname{Mat}_2(\mathbb R)$. It acts on four matrix blocks, giving the eighth power. Cubic time translation is triangular with diagonal one on each scalar entry's coefficient vector. Thus it has determinant one on the sixteen matrix coefficients; any reordering of this same basis in both coordinates is a conjugation and does not change that determinant. Both changes leave the intercept fixed. ∎

## 4. Zero samples and exact finite-data compatibility

**Corollary 4.1 (degree and root degeneracies).** Theorem 3.1 includes every nonzero gain of degree at most three, with no prescribed sample or prescribed coefficient required to be nonzero.

**Proof.** Its only gain-dependent division is by the recovered $h_k\ne0$. Such a coefficient exists whenever the whole polynomial is nonzero. Consequently degree drop, repeated roots and zero gain at any specified clocks allowed by a nonzero cubic cause no exceptional denominator. For nonzero constant gain, $k=0$. A nonzero polynomial of degree at most three has at most three distinct roots: each distinct root contributes a distinct linear factor by the factor theorem. In particular its seventeen sampled gain values cannot all vanish. ∎

**Theorem 4.2 (finite-data realization criterion).** Fix known invertible $Q_0$, known $t_0$ and arbitrary $Y\in\mathbb R^{17}$. Compute $d,Z_0,\ldots,Z_3$ by Theorem 2.1 and set

$$
B_j=Q_0^{-1}Z_j,\qquad h_j=\operatorname{tr}B_j.
$$

The continuation equations have an original-world realization if and only if:

1. At least one $h_j$ is nonzero.
2. For the smallest $k$ with $h_k\ne0$, the matrix $P=B_k/h_k$ has four strictly positive entries and determinant zero.
3. $B_j=h_jP$ for all $j=0,1,2,3$.

The realization is then unique and is the world of Theorem 3.1.

**Proof.** For an original world, $B_j=h_jP$, so all conditions are necessary. Conversely, condition 1 defines $k$, and

$$
\operatorname{tr}P=\operatorname{tr}(B_k)/h_k=1.
$$

Condition 2 therefore makes $P$ exactly a source of Definition 1.1. Define $h(s)=\sum_jh_js^j$ and $g(t)=h(t-t_0)$. Condition 1 makes $g$ nonzero of degree at most three. Condition 3 gives $Z_j=h_jQ_0P$, so

$$
Y_i=d+\operatorname{tr}(A_i\sum_j i^j Z_j)
=d+g(t_0+i)\operatorname{tr}(A_iQ_0P)
$$

for every $i$. This gives existence, and Theorem 3.1 gives uniqueness. For a general invertible $Q_0$, the criterion concerns these algebraic equations; legal attainability is an additional hypothesis, satisfied by an actually acquired prefix. The affine matrix-polynomial lifting and common-factor distinction are already present in [FIB self-calibrating relation mathematics, Definition 37.1 and Proposition 37.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md). ∎

**Proposition 4.3 (identically zero gain and constant observations).** In the enlarged source model allowing $g\equiv0$, the continuation readings are all $d$, and the source $P$ is not determined. Conversely, a constant vector $Y_i=c$ has the unique ambient solution $d=c$, $Z_0=\cdots=Z_3=0$. Hence no constant observation vector, including the all-zero vector, is realized by an original world.

**Proof.** If $g\equiv0$, the observation formula is independent of $P$. The stated ambient solution gives a constant vector, and ambient invertibility makes it unique. Its trace coefficients are all zero, so condition 1 of Theorem 4.2 fails. Thus excluding the identically zero whole gain is necessary. Zero individual readings, including those caused by drift cancellation, are not excluded by this argument. ∎

## 5. Full source realization and faithful resources

**Proposition 5.0 (positive factor realization).** Every original source has the positive factorization

$$
P=c\ell,\qquad c=\begin{pmatrix}b\\1-r\end{pmatrix},\qquad
\ell=(r/b,1),\qquad \operatorname{tr}(QP)=\ell Qc.
$$

Every legal prefix and continuation acts on the same positive object column and keeps the same instrument row. All positive factorizations of $P$ differ by $(c,\ell)\mapsto(\lambda c,\ell/\lambda)$ with $\lambda>0$.

**Proof.** Multiplication gives the displayed $P$, and expanding the diagonal gives the trace identity. The atom actions are

$$
J\begin{pmatrix}c_1\\c_2\end{pmatrix}=\begin{pmatrix}c_2\\c_1\end{pmatrix},\qquad
M\begin{pmatrix}c_1\\c_2\end{pmatrix}=\begin{pmatrix}c_2\\c_1+c_2\end{pmatrix}.
$$

They preserve strict positivity. Both atoms are nonnegative integer matrices with determinant $-1$, so every legal prefix is nonnegative and invertible. Gain signs and zeros do not alter the object column. If $P=c'\ell'$ is another positive factorization, its second column gives $c'\ell'_2=c$ because the displayed $\ell_2=1$. Thus $c'=\lambda c$ for $\lambda=1/\ell'_2>0$, and the first column then forces $\ell'=\ell/\lambda$. These are the trace and factor interfaces of [Common polynomial-gain shear calibration and erasure recovery, Lemma 1.2](FIB_POLYNOMIAL_GAIN_SHEAR_CALIBRATION_AND_ERASURE_RECOVERY.md). ∎

**Proposition 5.1 (ambient dimension boundary).** For the unrestricted space

$$
\mathcal X=\mathbb R\oplus\operatorname{Mat}_2(\mathbb R)^4,
$$

recovery of every point from $n$ fixed scalar linear observations requires $n\ge17$. Theorem 2.1 attains that bound.

**Proof.** The dimension is $1+4\cdot4=17$. A linear map to $\mathbb R^n$ for $n<17$ has a nonzero kernel by rank-nullity, so distinct ambient points have the same data, irrespective of the decoding rule. Theorem 2.1 supplies an invertible observation map when $n=17$. This argument concerns fixed linear observations of the whole ambient space; its hypothesis is not the constrained common-source domain, an already restricted data fibre, or an adaptive acquisition rule. ∎

**Proposition 5.2 (acquisition count).** Starting from an acquired prefix, the word of Theorem 2.1 adds sixteen atoms and sixteen readings and uses seventeen readings including the current one. Starting after the six-atom history $(J,M,J,M,M,M)$, its complete history has twenty-two atoms and twenty-three readings, at clocks $0,\ldots,22$.

**Proof.** The word has sixteen letters and each letter has its mandatory reading. $Y_0$ is reused at the current clock. The six-atom prefix has seven readings, so the total is $6+16$ atoms and $7+16$ readings. All three consecutive $J$ letters are executed and read: although $J^2=I$, their clocks and intermediate readings remain distinct. Removing them would change the observation matrix. All inverses and coefficient divisions occur in the decoder; one actual forward path supplies all data. ∎

## 6. Prior common-source recovery and the fixed-history problem

**Proposition 6.1 (the fourteen-read common-source construction).** In the domain of Definition 1.1, the chronological word consisting of eight $M$ atoms, then $J$, then four $M$ atoms recovers $(P,g,d)$ in fourteen readings and thirteen atoms. The same construction recovers these original parameters after every known acquired legal prefix at known absolute time.

**Proof.** At the identity, specialize [FIB self-calibrating relation mathematics, Definition 39.1 and Theorem 39.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md) to gain degree bound $k=3$ and additive-drift degree bound $0$. Its parameters are $N=9$, $m=8$, $L=14$, and its cumulative matrices are

$$
A_i=M^i\quad(0\le i\le8),\qquad
A_{9+j}=M^jJM^8\quad(0\le j\le4).
$$

Each transition is a single read atom, so that source's recorded indices agree with the literal atomic clock along this history. Its trace-normalized source is $P$, its normalized gain is $g$, and its drift is $d$.

For an acquired legal prefix $Q_0$ at clock $t_0$, put

$$
R=Q_0P,\quad a=\operatorname{tr}R>0,\quad R_0=R/a,\quad
h(s)=g(t_0+s),\quad H=ah.
$$

Proposition 5.0 shows that $R$ is strictly positive and rank one. Hence the cited theorem recovers $(R_0,H,d)$ from those same fourteen continuation readings. Define

$$
\eta=\operatorname{tr}(Q_0^{-1}R_0)=1/a>0.
$$

Then

$$
P=Q_0^{-1}R_0/\eta,\qquad h=\eta H,\qquad g(t)=h(t-t_0).
$$

These formulas prove the claimed transport using the cited common-source result. The unrestricted affine analogue with two independent matrix coefficients and affine drift is [the same source, Definition 37.1 and Theorem 37.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md); it is a ten-dimensional observation model. ∎

**Proposition 6.2 (different parameter spaces).** The common-source cubic models form a proper subset of $\mathcal X$. Fourteen scalar linear observations cannot recover every point of $\mathcal X$, even though Proposition 6.1 recovers the constrained family. The seventeen-read lower bound of Proposition 5.1 imposes no seventeen-read lower bound on that family.

**Proof.** For a fixed invertible $Q_0$, common-source coefficients satisfy $Z_j=h_jQ_0P$. Thus $Q_0^{-1}Z_j$ are scalar multiples of a single positive rank-one trace-one matrix. For example, the ambient point $Z_0=Q_0$, $Z_1=Z_2=Z_3=0$ fails this condition because $Q_0^{-1}Z_0=I$ has rank two. Properness follows. Rank-nullity gives a kernel of dimension at least three for any fourteen fixed linear observations on $\mathcal X$. Proposition 6.1 is about injectivity on the smaller domain, so it does not contradict that kernel. ∎

**Definition 6.3 (the entire original child).** For $p,v\in\mathbb R$, let $C(p,v)$ be all original worlds with chronological acquired word $(J,M,J,M,M,M)$ and all seven readings

$$
(y_0,y_1,y_2,y_3,y_4,y_5,y_6)=(0,24,147/5,24,18,p,v).
$$

This is [An exact unequal-diagonal pair for the original terminal M response, Definition 1.2](FIB_STRICT_REAL_UNEQUAL_DIAGONAL_ACTUAL_M_PAIR.md), without any restriction to a local source chart or regular stratum. For a world $W$, set $q=r(1-r)/b$ and write $g_i=g(i)$. Its seven acquired matrices and traces are

| $i$ | chronological word | $Q_i$ | $\operatorname{tr}(Q_iP)$ |
|---:|:---|:---|:---|
| 0 | empty | $I$ | $1$ |
| 1 | $J$ | $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ | $b+q$ |
| 2 | $JM$ | $\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ | $1+b$ |
| 3 | $JMJ$ | $\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ | $r+b+q$ |
| 4 | $JMJM$ | $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ | $1+2b$ |
| 5 | $JMJMM$ | $\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$ | $1+r+3b+q$ |
| 6 | $JMJMMM$ | $\left(\begin{smallmatrix}3&1\\5&2\end{smallmatrix}\right)$ | $2+r+5b+q$ |

In particular

$$
Q_6=\begin{pmatrix}3&1\\5&2\end{pmatrix},\qquad
Q_6^{-1}=\begin{pmatrix}2&-1\\-5&3\end{pmatrix}.
$$

**Theorem 6.4 (compatibility with every acquired row).** Given $p,v$ and a continuation vector $Y\in\mathbb R^{17}$ starting at $Q_6,t_0=6$, the combined data come from a world in $C(p,v)$ if and only if the conditions of Theorem 4.2 hold and its unique recovered world satisfies

$$
\begin{aligned}
d+g_0&=0,\\
d+g_1(b+q)&=24,\\
d+g_2(1+b)&=147/5,\\
d+g_3(r+b+q)&=24,\\
d+g_4(1+2b)&=18,\\
d+g_5(1+r+3b+q)&=p,\\
d+g_6(2+r+5b+q)&=v.
\end{aligned}
$$

In that event the combined realization is unique and $Y_0=v$.

**Proof.** Starting at $I$, left multiplication by $J$ interchanges the two rows, and left multiplication by $M$ replaces the rows $(R_1,R_2)$ by $(R_2,R_1+R_2)$. Applying these identities to the six chronological letters gives exactly the seven displayed matrices. Pairing their transposed entries with the row-major entries of $P$ gives their displayed traces. Thus the seven equations are precisely all the earlier observation equations. Necessity follows for any combined realization. For sufficiency, Theorem 4.2 gives one whole world realizing every continuation row, and the seven additional equations realize every acquired original row using that same $P,g,d$. The last equation and the continuation equation at $i=0$ both give the same clock-six reading, hence $Y_0=v$. Uniqueness follows from the continuation inverse. No assumption divides by a sampled gain or discards a singular stratum. ∎

**Problem 6.5 (independent pairs in one entire child).** Find $p\ne24$ and $v$ and independently selected pairs of worlds

$$
W_0,W_1,W_2,W_3\in C(p,v),\qquad W_0\ne W_1,\quad W_2\ne W_3,
$$

such that

$$
\begin{aligned}
d_0+g_0(7)\operatorname{tr}(JQ_6P_0)
 &=d_1+g_1(7)\operatorname{tr}(JQ_6P_1),\\
d_2+g_2(7)\operatorname{tr}(MQ_6P_2)
 &=d_3+g_3(7)\operatorname{tr}(MQ_6P_3).
\end{aligned}
$$

Here $g_a$ denotes the whole polynomial of world $W_a$, rather than a coefficient. The pairs may overlap. Their two common terminal values need not agree. Each world retains its own drift and whole nonzero polynomial; no equality of drifts between worlds is imposed. All of Definition 1.1, including degree drops, repeated roots, zero samples, zero drift and exceptional source strata, remains in this problem. The independent same-base obligation is [An exact unequal-diagonal pair for the original terminal M response, Section 8](FIB_STRICT_REAL_UNEQUAL_DIAGONAL_ACTUAL_M_PAIR.md). Its existence question remains unresolved here.

**Proposition 6.6 (later separation of a terminal collision).** For $W\in C(p,v)$, write $F_i(W)$ for its continuation reading at clock $6+i$, $0\le i\le16$, along Theorem 2.1's word. The map $W\mapsto(F_0(W),\ldots,F_{16}(W))$ is injective. If distinct $W,W'\in C(p,v)$ have equal terminal $J$ responses, then $F_i(W)\ne F_i(W')$ for some $2\le i\le16$. If they have equal terminal $M$ responses, then $F_i(W)\ne F_i(W')$ for some $1\le i\le16$.

**Proof.** Injectivity is the restriction of Theorem 3.1 to $C(p,v)$. Both worlds have $F_0=v$. Since the continuation's first atom is $J$, equality of their terminal $J$ responses also gives $F_1(W)=F_1(W')$. The distinct worlds must therefore differ at a later coordinate. In the terminal $M$ case, injectivity and equality of $F_0$ alone give a differing coordinate among $1,\ldots,16$; no terminal $M$ reading is borrowed into this $J$-first continuation. These implications are conditional on the collision pairs and decide neither their existence nor their nonexistence in Problem 6.5. ∎

## 追加锚（本行以下为增补区）

