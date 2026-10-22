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

## 7. The unrestricted general-degree literal frame

**Definition 7.1 (independent matrix coefficients and polynomial drift).** Fix known integers $k,\delta\ge0$. All entries of all coefficient matrices and all drift coefficients in

$$
Z(t)=\sum_{h=0}^k Z_ht^h,\qquad Z_h\in\operatorname{Mat}_2(\mathbb R),
\qquad D(t)=\sum_{h=0}^{\delta}d_ht^h
$$

are independent unrestricted real unknowns. There is no common-source, rank, positivity, gain, trace or nonzero-coefficient hypothesis. The ambient dimension is

$$
N=4(k+1)+(\delta+1)=4k+\delta+5.
$$

The known atoms are precisely the matrices $M,J$ of Definition 1.1. Starting with $A_0=I$, every chronological atom is left multiplied, advances the local clock by one and is read. The current reading is included, and

$$
Y_i=D(i)+\operatorname{tr}(A_iZ(i)).
$$

Set

$$
q=k+1,\quad \rho=\delta+1,\quad s=2q+\rho=2k+\delta+3,
\quad m=s-1=2k+\delta+2.
$$

**Theorem 7.2 (general-degree ambient reconstruction).** The chronological word

$$
\boxed{M^{\,2k+\delta+2}\ J\ M^{\,2k+1}}
$$

recovers every one of the $N$ independent coefficients of Definition 7.1 from exactly $N$ scalar readings including the current one. Each displayed power means that many executed and immediately read individual atoms. The complete cumulative path is

$$
A_i=M^i\quad(0\le i\le m),\qquad
A_{s+j}=M^jJM^m\quad(0\le j<2q).
$$

The observation map is a linear bijection on the entire ambient space.

**Proof.** Define

$$
\lambda=\frac{1+\sqrt5}{2},\quad
\mu=\frac{1-\sqrt5}{2},\quad
S=\begin{pmatrix}1&1\\\lambda&\mu\end{pmatrix},\qquad
\Lambda=\operatorname{diag}(\lambda,\mu).
$$

Both roots satisfy $x^2=x+1$, so $MS=S\Lambda$. They are distinct, nonzero and different from one, and

$$
\lambda+\mu=1,\quad \lambda\mu=-1,\quad
\mu-\lambda=-\sqrt5,\quad (1-\lambda)(1-\mu)=-1.
$$

Thus $S$ is invertible. Direct multiplication gives

$$
S^{-1}=\frac1{\mu-\lambda}\begin{pmatrix}\mu&-1\\-\lambda&1\end{pmatrix},\qquad
K=S^{-1}JS=
\frac1{\mu-\lambda}
\begin{pmatrix}-2&\mu\\-\lambda&2\end{pmatrix},
\qquad K_{12}K_{21}=\frac15\ne0.
$$

Write the independent eigenbasis entries as

$$
S^{-1}Z(t)S=
\begin{pmatrix}a(t)&b(t)\\c(t)&e(t)\end{pmatrix}.
$$

Each has degree at most $k$, and conjugation preserves independence of all four matrix-entry polynomials. During the first $s$ readings,

$$
Y_i=\lambda^ia(i)+\mu^ie(i)+D(i),\qquad 0\le i<s.
$$

To invert this block and the switched block below, use the classical confluent Vandermonde calculation as an intermediate step. See Batenkov–Yomdin, “On the Accuracy of Solving Confluent Prony Systems”, §2B, [arXiv:1106.1137v3](https://arxiv.org/abs/1106.1137v3), [DOI:10.1137/110836584](https://doi.org/10.1137/110836584). The fixed-node and drift-separation ingredients are also used in [FIB self-calibrating relation mathematics, Theorems 35.2 and 39.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md). The following derivation fixes the sign and factorial normalization required by this frame.

For an integer $n\ge1$, put

$$
\mathfrak F(n)=\prod_{h=0}^{n-1}h!.
$$

Let $x_1,\ldots,x_a$ be distinct nonzero real numbers and let $n_1,\ldots,n_a$ be positive integers. Put $L=\sum_b n_b$. In the ordered columns $(b,h)$, first by $b$ and then by $0\le h<n_b$, define

$$
\mathcal V(x_1:n_1,\ldots,x_a:n_a)_{i,(b,h)}=i^h x_b^i,
\qquad 0\le i<L.
$$

The convention is $i^0=1$, including at $i=0$. Then

$$
\boxed{
\det\mathcal V
=\left(\prod_{b=1}^a x_b^{n_b(n_b-1)/2}\mathfrak F(n_b)\right)
 \prod_{b<c}(x_c-x_b)^{n_bn_c}\ne0.
}
$$

Consequently $L$ consecutive samples beginning at zero uniquely recover all coefficients of $\sum_b x_b^i p_b(i)$, where the $p_b$ are independent real polynomials of degrees less than $n_b$. No condition is imposed on their actual degrees or coefficients.

First consider the derivative evaluation matrix

$$
U_{i,(b,h)}=\left.\frac{d^h}{dx^h}x^i\right|_{x=x_b}
=(i)_h x_b^{i-h},
$$

where $(i)_h=i(i-1)\cdots(i-h+1)$, with $(i)_0=1$. Its determinant is

$$
\det U=\left(\prod_b\mathfrak F(n_b)\right)
\prod_{b<c}(x_c-x_b)^{n_bn_c}.
$$

Here is a derivation including its sign and factorial normalization. In each group choose distinct ordered auxiliary real numbers $\xi_{b,0},\ldots,\xi_{b,n_b-1}$ and apply the ordinary Vandermonde identity to the ordered nodes $x_b+\varepsilon\xi_{b,h}$. Let $c_0=\sum_b n_b(n_b-1)/2$. The coefficient of the lowest power $\varepsilon^{c_0}$ in its product formula is

$$
\left(\prod_b\prod_{u<v}(\xi_{b,v}-\xi_{b,u})\right)
\prod_{b<c}(x_c-x_b)^{n_bn_c}.
$$

Expand each column by its finite Taylor formula at $x_b$. A term with two identical derivative orders in one group has equal columns and vanishes. The least possible sum of distinct nonnegative orders in that group is $0+\cdots+(n_b-1)$. Multilinearity therefore makes the same coefficient equal to

$$
\det U\prod_b
\det\left[\frac{\xi_{b,u}^h}{h!}\right]_{0\le h,u<n_b}
=\det U\prod_b
\frac{\prod_{u<v}(\xi_{b,v}-\xi_{b,u})}{\mathfrak F(n_b)}.
$$

Cancelling the nonzero auxiliary factors proves the displayed formula for $U$. The ordinary Vandermonde identity itself follows because its determinant is alternating in its nodes, has total degree $L(L-1)/2$, and the coefficient of $\prod_{j=0}^{L-1}x_j^j$ is one.

For every $h$, expansion in the monic falling-factorial basis gives $i^h=\sum_{u=0}^h c_{h,u}(i)_u$ with $c_{h,h}=1$. Hence

$$
i^h x_b^i=\sum_{u=0}^h c_{h,u}x_b^u U_{i,(b,u)}.
$$

This is a triangular column change of determinant $\prod_{h=0}^{n_b-1}x_b^h$ in group $b$. Multiplying these factors proves the formula for $\mathcal V$. Its nonzero determinant proves coefficient recovery, including when some or all coefficient polynomials vanish.

The fixed-node calculation just derived at the three nodes $(\lambda:q,\mu:q,1:\rho)$ recovers the coefficients of $a,e,D$ uniquely. Explicitly, with $V_3=\mathcal V(\lambda:q,\mu:q,1:\rho)$ and coefficient columns in that group order,

$$
\begin{pmatrix}[a]\\[e]\\[D]\end{pmatrix}
=\frac{\operatorname{adj}(V_3)}{\det V_3}
\begin{pmatrix}Y_0\\\vdots\\Y_{s-1}\end{pmatrix}.
$$

Here $[p]$ always lists the polynomial's coefficients in ascending ordinary powers, padded with zero coefficients to its declared bound.

The reading after the switch has absolute local clock $t=s+j$, not $j$. Conjugating its cumulative matrix gives $\Lambda^jK\Lambda^m$. The trace is therefore

$$
\begin{aligned}
Y_{s+j}={}&D(s+j)
+\lambda^{j+m}K_{11}a(s+j)
+\mu^{j+m}K_{22}e(s+j)\\
&+\lambda^j\mu^mK_{12}c(s+j)
+\mu^j\lambda^mK_{21}b(s+j).
\end{aligned}
$$

Subtract the three known terms in the first line and call the residual $R_j$. Define independent polynomials

$$
F(u)=\mu^mK_{12}c(s+u),\qquad
G(u)=\lambda^mK_{21}b(s+u).
$$

They have degree at most $k$, and

$$
R_j=\lambda^jF(j)+\mu^jG(j),\qquad 0\le j<2q.
$$

The fixed-node calculation above at $(\lambda:q,\mu:q)$ recovers both entire polynomials. In full finite form, with $V_2=\mathcal V(\lambda:q,\mu:q)$,

$$
\begin{pmatrix}[F]\\[G]\end{pmatrix}
=\frac{\operatorname{adj}(V_2)}{\det V_2}
\begin{pmatrix}R_0\\\vdots\\R_{2q-1}\end{pmatrix}.
$$

All denominators are fixed nonzero known constants. Undoing translation and scaling yields

$$
\boxed{
c(t)=\frac{F(t-s)}{\mu^mK_{12}},\qquad
b(t)=\frac{G(t-s)}{\lambda^mK_{21}},\qquad
Z(t)=S\begin{pmatrix}a(t)&b(t)\\c(t)&e(t)\end{pmatrix}S^{-1}.
}
$$

These formulas return the actual $Z,D$ for every point in the stated ambient space. Conversely, for arbitrary $Y\in\mathbb R^N$, the first inverse fits every initial reading and the second inverse fits every remaining residual, using these same four polynomials and the same drift. Thus they give a two-sided inverse and establish bijectivity. There are $s+2q=4q+\rho=N$ readings, at clocks $0,\ldots,N-1$. ∎

## 8. Exact observation determinant and the switch conditions

**Theorem 8.1 (determinant in ordinary entry coordinates).** Order the unknowns as

$$
x=(d_0,\ldots,d_\delta,
 z_{0,11},z_{0,12},z_{0,21},z_{0,22},\ldots,
 z_{k,11},z_{k,12},z_{k,21},z_{k,22})^{\mathsf T}.
$$

Let $C_{k,\delta}$ have the rows

$$
C_i=\bigl((i^h)_{h=0}^{\delta},\ (i^h v(A_i))_{h=0}^{k}\bigr),
\qquad v(A)=(A_{11},A_{21},A_{12},A_{22}),
$$

in the path order of Theorem 7.2. The blocks are concatenated in the displayed order and $i^0=1$, including at $i=0$. For a zero degree bound the relevant list contains just its constant block. Then

$$
\boxed{
\det C_{k,\delta}
=5^{k(k+1)}
\left(\prod_{h=0}^k h!\right)^4
\left(\prod_{h=0}^{\delta}h!\right)>0.
}
$$

**Proof.** Use the intermediate coefficient order

$$
\theta=([a],[e],[D],[c],[b])^{\mathsf T}.
$$

The first $s$ rows have zero coefficients on $[c],[b]$. The entire observation matrix in $\theta$ coordinates is block triangular. Its first diagonal block is $V_3$. For the second block, translation from coefficients in $t$ to coefficients in $u$ of a polynomial evaluated at $s+u$ is triangular with diagonal one. Its two scalar multipliers are $\mu^mK_{12}$ and $\lambda^mK_{21}$, each on $q$ coefficients. Consequently the determinant in these coordinates is

$$
B=\det V_3\det V_2\bigl((\lambda\mu)^mK_{12}K_{21}\bigr)^q.
$$

The fixed-node calculation in the proof of Theorem 7.2 gives the signed expressions

$$
\begin{aligned}
\det V_2
&=(\lambda\mu)^{q(q-1)/2}\mathfrak F(q)^2(\mu-\lambda)^{q^2},\\
\det V_3
&=\det V_2\,\mathfrak F(\rho)
 (1-\lambda)^{q\rho}(1-\mu)^{q\rho}.
\end{aligned}
$$

Because $q(q-1)$ is even, $(\mu-\lambda)^{2q^2}=5^{q^2}$ and $K_{12}K_{21}=1/5$, their product yields

$$
B=(-1)^{q\rho+mq}5^{q^2-q}\mathfrak F(q)^4\mathfrak F(\rho)
=(-1)^q5^{q(q-1)}\mathfrak F(q)^4\mathfrak F(\rho).
$$

The last sign uses $m=2q+\rho-1$.

It remains to transport this signed determinant to $x$. Conjugation $Z_h\mapsto S^{-1}Z_hS$ has determinant one on the four-dimensional matrix space: left multiplication contributes $(\det S^{-1})^2$ and right multiplication contributes $(\det S)^2$. Initially retain the coefficient-wise order $(a_h,b_h,c_h,e_h)$ and drift first. Grouping the four entries by entry type has $6\binom q2$ inversions, an even number. Reordering the four groups from $([a],[b],[c],[e])$ to $([a],[e],[c],[b])$ has $3q^2$ inversions, of parity $q$. Moving the $\rho$ drift coordinates past the first two groups has $2q\rho$ inversions, again even. Thus the coefficient change $x\mapsto\theta$ has determinant $(-1)^q$. Since the observation matrix in $x$ is the observation matrix in $\theta$ multiplied by that coefficient change, its determinant is $B(-1)^q$. Substitution of $q=k+1,\rho=\delta+1$ proves the formula. ∎

At $k=\delta=0$, the word is $M^2JM$, the two block lengths are $3$ and $2$, and the ordinary-coordinate matrix is

$$
C_{0,0}=\begin{pmatrix}
1&1&0&0&1\\
1&0&1&1&1\\
1&1&1&1&2\\
1&1&1&2&1\\
1&1&2&1&3
\end{pmatrix},\qquad \det C_{0,0}=1.
$$

More generally, $k=0$ gives $q=1$, so neither spectral group is empty, and $\delta=0$ gives $\rho=1$, so the drift group is still present. All factorial products include $0!=1$. The argument uses degree upper bounds throughout, including constant and zero polynomials.

**Proposition 8.2 (precise algebraic conditions behind the two blocks).** More generally, keep the same degree bounds and path lengths and suppose the known first atom is real diagonalizable with distinct nonzero real eigenvalues $\lambda,\mu$, both different from one. Let its eigenbasis switch matrix be $K$. For this two-block observation map, invertibility is equivalent to $K_{12}K_{21}\ne0$.

**Proof.** The first-block formula and the fixed-node calculation in the proof of Theorem 7.2 remain valid for these three distinct nonzero nodes. The second-block determinant is exactly

$$
\det\mathcal V(\lambda:q,\mu:q)
\bigl((\lambda\mu)^mK_{12}K_{21}\bigr)^q.
$$

It is nonzero if and only if $K_{12}K_{21}\ne0$. If $K_{12}=0$, any nonzero polynomial in entry $c$ alone is invisible in both blocks; if $K_{21}=0$, the same holds for entry $b$. These are explicit nonzero ambient kernel directions. The fixed $M,J$ of Theorem 7.2 satisfy every required condition by their displayed values, with $K_{12}K_{21}=1/5$. This proposition does not assert a criterion for atoms with repeated eigenvalues or eigenvalues zero or one. ∎

## 9. Known-prefix transport and all degree and root degeneracies

**Theorem 9.1 (known left multiplier and absolute clock).** Let $Q_0$ be any known invertible real matrix and $t_0$ any known real number. Suppose the independent absolute-time unknowns are

$$
U(t)=\sum_{h=0}^kU_ht^h,\qquad
\mathcal D(t)=\sum_{h=0}^{\delta}\eta_ht^h,
$$

and readings on the same continuation word are

$$
Y_i=\mathcal D(t_0+i)+\operatorname{tr}(A_iQ_0U(t_0+i)).
$$

They uniquely recover all coefficients of $U,\mathcal D$. In the ordinary coefficient order of Theorem 8.1, now applied to $(\eta_h,U_h)$, the determinant is

$$
\boxed{\det C_{k,\delta}\,(\det Q_0)^{2(k+1)}\ne0.}
$$

**Proof.** Define local polynomials

$$
Z(s)=Q_0U(t_0+s),\qquad D(s)=\mathcal D(t_0+s).
$$

These are exactly the independent unknowns of Definition 7.1, because time translation and left multiplication are invertible. Theorem 7.2 recovers them, after which

$$
U(t)=Q_0^{-1}Z(t-t_0),\qquad
\mathcal D(t)=D(t-t_0).
$$

For example, if $Z(s)=\sum_jZ_js^j$ and $D(s)=\sum_jd_js^j$, the absolute coefficients are

$$
U_h=Q_0^{-1}\sum_{j=h}^k\binom jh Z_j(-t_0)^{j-h},\qquad
\eta_h=\sum_{j=h}^{\delta}\binom jh d_j(-t_0)^{j-h}.
$$

On every scalar polynomial coefficient vector, translation has a triangular matrix with diagonal one, hence determinant one. Left multiplication by $Q_0$ has determinant $(\det Q_0)^2$ on each matrix coefficient, since it acts on the two columns independently. There are $k+1$ such blocks and the drift block is unaffected by left multiplication. Multiplication of these determinants proves the assertion. ∎

For an actually acquired legal prefix, $Q_0$ is its cumulative product and $t_0$ its nonnegative integer length. Since each atom has determinant $-1$, every such $Q_0$ is invertible. The theorem's extension to other specified invertible $Q_0$ and real $t_0$ is algebraic, with no assertion of legal attainability. Matrix inverses and translations occur only in the decoder, not as physical interventions.

Invertibility and knowledge of the stated coordinates matter. If $Q_0$ is singular, take a nonzero matrix $H$ with $Q_0H=0$. Replacing $U(t)$ by $U(t)+H$ leaves every observation unchanged, even on arbitrarily long continuations. If the absolute origin is unknown, then for any real $h$ the simultaneous replacement

$$
t_0\mapsto t_0+h,\qquad U(t)\mapsto U(t-h),\qquad
\mathcal D(t)\mapsto\mathcal D(t-h)
$$

preserves every reading and all degree bounds. Thus local polynomial recovery does not identify an unknown absolute time origin. This is the time-translation ambiguity already expressed in [FIB self-calibrating relation mathematics, Proposition 37.4](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md).

**Corollary 9.2 (zero and lower-degree strata).** The ambient inverse includes lower actual degrees of any entry or the drift, repeated roots, zero entries at any sampled clock, identically zero entry polynomials and $Z\equiv0$. No polynomial coefficient or value of an unknown polynomial is a denominator. In particular $Z\equiv0$ with arbitrary polynomial drift is still uniquely recovered in the ambient model.

**Proof.** Every division in Theorem 7.2 is by a fixed determinant or by one of the fixed nonzero numbers $\mu^mK_{12},\lambda^mK_{21}$. The observation matrix itself is independent of all unknowns. Its bijectivity therefore applies to each named stratum and their intersections, including the zero matrix polynomial. No selection of nonzero samples or root positions is involved. ∎

**Corollary 9.3 (common-source specialization and its exact boundary).** In the additional constrained model

$$
U(t)=g(t)P,\qquad \operatorname{tr}P=1,\qquad
0\ne g\in\mathbb R[t],\quad\deg g\le k,
$$

the same ambient measurements recover $P,g,\mathcal D$ after every known invertible prefix and at every known clock. For arbitrary data, membership in the strictly positive rank-one common-source submodel is characterized as follows. From the recovered local $Z_j$ define

$$
B_j=Q_0^{-1}Z_j,\qquad h_j=\operatorname{tr}B_j.
$$

At least one $h_j$ must be nonzero. For any such index $a$, set $P=B_a/h_a$. The necessary and sufficient remaining conditions are that $P$ have four strictly positive entries, $\det P=0$, and $B_j=h_jP$ for all $j$. Then

$$
g(t)=\sum_{j=0}^k h_j(t-t_0)^j.
$$

**Proof.** A genuine realization has $B_j=h_jP$ with $h(s)=g(t_0+s)$, because taking traces uses $\operatorname{tr}P=1$. Translation preserves nonzeroness, so some coefficient $h_a$ is nonzero. Division by that recovered coefficient gives the genuine $P$ and then $g$. Conversely, under the stated conditions $\operatorname{tr}P=\operatorname{tr}(B_a)/h_a=1$, and $g$ is nonzero with the required degree bound. The identities $B_j=h_jP$ and the recovered drift give one common realization of every reading. Ambient uniqueness and the normalization formulas prove uniqueness in this constrained model. Different choices of $a$ give the same $P$. If $g\equiv0$ is allowed, every $P$ instead gives the same matrix polynomial $U\equiv0$; ambient recovery survives, but separate recovery of that $P$ does not. ∎

This specialization uses an extra common-factor constraint only after the unrestricted inverse. It is not a hypothesis of Theorems 7.2, 8.1 or 9.1. Degree drops and all root degeneracies of a nonzero common gain are included without dividing by any gain sample. Without declared finite degree bounds, finite data do not certify future polynomial behavior: adding a nonzero multiple of $\prod_{i=0}^{N-1}(t-(t_0+i))$ to the drift preserves all these readings while changing its future values.

## 10. Literal resource counts and the sharp ambient lower bound

**Proposition 10.1 (one physical path and its exact counts).** Starting at an acquired prefix, Theorem 7.2 adds $N-1=4k+\delta+4$ atoms and the same number of new mandatory readings, and uses $N$ readings including the current one. The new terminal absolute clock is $t_0+N-1$. The switch reading is at $t_0+s$, and the second block uses $2k+2$ consecutive readings, including that switch reading.

**Proof.** The first power executes $m=2k+\delta+2$ atoms, followed by one $J$ and then $2k+1$ more atoms. Their sum is $4k+\delta+4=N-1$. The first block reads clocks $0,\ldots,m$, including the already acquired clock zero. The switch advances to $m+1=s$ and is read. The last power contributes the following $2k+1$ read clocks. Thus the second block has $2k+2=2q$ readings and ends at $s+2q-1=N-1$. Every step on the displayed cumulative path is one allowed atom. Nothing resets the object, clock or drift; no unread atom, omitted intermediate reading, empty-word time advance, copy, extra port or physical inverse is used. ∎

**Theorem 10.2 (sharp fixed-linear ambient reading bound).** On the unrestricted space

$$
\mathcal X_{k,\delta}
=\operatorname{Mat}_2(\mathbb R)^{k+1}\oplus\mathbb R^{\delta+1},
$$

any recovery of every point from $n$ fixed scalar linear observations requires $n\ge N=4k+\delta+5$, regardless of the decoding rule. Theorem 7.2 attains this bound with legal literal-clock observations.

**Proof.** The vector space has dimension $N$. For $n<N$, the linear observation map has rank at most $n$, hence a nonzero kernel. Zero and any nonzero point of that kernel give identical data, so no decoder can uniquely recover both. Theorem 8.1 supplies an invertible $N$-row observation matrix on a legal path. This proves sharpness in exactly the stated class. ∎

The lower bound concerns fixed linear observations of the full unrestricted ambient space. It is not a lower bound for the common-source family, a particular acquired child or adaptive acquisition, and does not imply any terminal collision in those domains.

## 11. Exact prior coverage and the unchanged original problem

The known mathematical components have different scopes. [FIB self-calibrating relation mathematics, §§33–35](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md) treats a fixed arbitrary matrix and polynomial drift, so it already includes the degree-zero matrix case. Its §36 imposes positive rank one and has a different recording contract at composite intermediate operations. Its Theorem 37.2 proves the unrestricted affine-matrix, affine-drift case $k=\delta=1$; that instance of the present ambient conclusion is already known. Its §§38–39 treat a single positive rank-one source multiplied by one common gain polynomial. Their arbitrary gain degree does not make the four matrix-entry polynomials independent. In particular, the $3k+\delta+5$-read upper bound of Theorem 39.2 applies to that constrained family, whereas Theorem 7.2 uses $4k+\delta+5$ readings to recover the larger independent-coefficient space. The first-block recurrence/interpolation inverse is already an intermediate ingredient of that theorem.

The general unrestricted two-block conclusion here retains the two independent off-diagonal coefficient polynomials after the switch and recovers them by a second complete fixed-node evaluation inverse. Its exact determinant, all-degree literal-clock count, and invertible-prefix/absolute-time transport concern the entire space of Definition 7.1. They extend the named cubic ambient frame and the existing affine ambient case using established interpolation facts; they assert no literature priority.

**Corollary 11.1 (cubic constant-drift instance at the acquired history).** At $k=3,\delta=0$, the chronological word is $M^8JM^7$, with sixteen atoms and seventeen readings including the current one. Starting after the original six atoms $(J,M,J,M,M,M)$, it ends at absolute clock $22$; the whole history has twenty-two atoms and twenty-three readings. It recovers every original world of Definition 1.1 from its actual new continuation data. For arbitrary proposed continuation data, realization by a world in the entire $C(p,v)$ is equivalent to Corollary 9.3's source conditions together with all seven original equations of Theorem 6.4.

**Proof.** Substitute $k=3,\delta=0$ in Theorems 7.2 and 9.1 and Proposition 10.1. The acquired $Q_6$ and $t_0=6$ are those of Definition 6.3. The common-source inverse of Corollary 9.3 supplies exactly one original world if its source conditions hold. That world realizes the preceding history if and only if each of its seven actual acquired readings equals the given original row, which is exactly the seven equations in Theorem 6.4. The last such equation identifies the current continuation reading with $v$. Necessity and sufficiency follow using one whole gain, one drift and one source for every row; uniqueness follows from the continuation inverse. ∎

The data word in Corollary 11.1 is distinct from the word in Theorem 2.1; no readings from their different continuations are equated. The original seven readings remain

$$
(0,24,147/5,24,18,p,v)
$$

at clocks $0,\ldots,6$, and both alternative terminal responses in Problem 6.5 are still evaluated at clock $7$. That problem still requires some $p\ne24,v$ and two independently chosen distinct-world pairs in the same entire $C(p,v)$, one pair colliding under $J$ and one under $M$. Its full degree/root/source domain and its allowance of independent drifts between worlds are unchanged.

Later recovery from additional acquired readings proves neither existence nor nonexistence of these two pairs. Explicitly, if two distinct worlds share the entire acquired child and the terminal $M$ response, then their readings along $M^8JM^7$ agree at continuation indices zero and one but differ at some index $2\le i\le16$, by injectivity. If they instead collide under the alternative terminal $J$, injectivity only implies a differing index $1\le i\le16$ on this $M$-first path. Both statements are conditional on the respective pair's existence and create no such pair. The independent same-child $J/M$ existence question of Problem 6.5 remains open.

## 追加锚（本行以下为增补区）

