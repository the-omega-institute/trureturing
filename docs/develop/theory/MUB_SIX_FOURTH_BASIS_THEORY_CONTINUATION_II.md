# 六维第四个无偏基问题：理论续卷 II

本卷承接[前卷](MUB_SIX_FOURTH_BASIS_THEORY.md)与[理论续卷 §§52–61](MUB_SIX_FOURTH_BASIS_THEORY_CONTINUATION.md)，沿用相同的实际输入基约定与实参数支。第 62 节证明移动 canonical 基在中心参数处的局部唯一性；第 63 节确定前续卷所列六条中心非 canonical 射线的局部正交图。两节均允许任意邻近实际候选，不假设循环或反射协变性。

## 62. Local uniqueness of the moving canonical basis through the center

### 62.1 Actual input bases and the local statement

Retain the real branch \(|b|<1\), the matrix \(M(b)=\sqrt6H_0(b)\),
and the positive radicals \(c,d,k\) of (60.1). Put
\(\omega=(-1+i\sqrt3)/2\), \(f_l=(1,\omega^l,\omega^{2l})\), and

\[
 g_0(b)=\frac{-2b^3+i(b^2+3)}{ck},\qquad
 g_1(b)=g_2(b)=\frac{b+i}{c}.
\]

Write \(C(b)\) for the **unnormalized common-flat input matrix** whose
columns, in this fixed order, are

\[
 C(b)=\bigl((f_0,g_0f_0),(f_0,-g_0f_0),
 (f_1,g_1f_1),(f_1,-g_1f_1),
 (f_2,g_1f_2),(f_2,-g_1f_2)\bigr).
\tag{62.1}
\]

By (60.2), \(C(b)^*C(b)=6I_6\), every entry of \(C(b)\) has modulus
one, and every entry of \(M(b)C(b)\) has squared modulus six. The
normalized common-flat input basis is \(C(b)/\sqrt6\); the associated
ordinary common-unbiased column basis for \((I,H_0(b))\) is
\(H_0(b)C(b)/\sqrt6\). Set \(V=C(0)\). Its first row is identically one.

**Theorem 62.1 (repo-derived central canonical-basis germ).**
There is a neighborhood of \((0,[C(0)/\sqrt6])\) in which every pair
\((b,[B])\), with \(B\) an actual common-flat orthonormal input basis
for \(H_0(b)\), belongs to the moving canonical family
\((b,[C(b)/\sqrt6])\). Brackets identify independent column phases and
column permutations only.

Equivalently, after matching the columns and normalizing their first
entries, the only sufficiently nearby unit-entry matrices \(Z\) satisfying

\[
 Z^*Z=6I_6,\qquad |(M(b)Z)_{ak}|^2=6
 \quad(0\le a,k\le5)
\tag{62.2}
\]

are \(Z=C(b)\). No covariance, row-phase quotient, Fourier-support
restriction, or relation between different candidate columns is imposed.
The assertion concerns all nearby solutions, including singular or
nondifferentiable approaches to the canonical family.

The central first derivative has rank 28 in 31 variables, so an ordinary
full-rank argument cannot prove this statement. The proof below resolves
the two extra tangent directions by a coercive quadratic residual whose
remainder vanishes on the exact moving canonical axis.

### 62.2 Complete phase chart and original constraints

Let \(\theta_{rk}\) be 30 independent real variables, with
\(1\le r\le5\), \(0\le k\le5\), and put

\[
 \theta_{0k}=0,\qquad Z_{rk}(\theta)=V_{rk}e^{i\theta_{rk}}.
\]

Restrict all phases to a sufficiently small neighborhood of zero. This is
a complete local chart after fixing only the six column phases. Define
\(F(b,\theta)\in\mathbb R^{60}\) in the following zero-based order:

1. For \(j<k\), in lexicographic order, take
   \(\operatorname{Re}(Z^*Z)_{jk}\), then
   \(\operatorname{Im}(Z^*Z)_{jk}\). These are rows 0 through 29.
2. For \(k=0,\ldots,5\), then \(a=0,\ldots,4\), take
   \(|(M(b)Z)_{ak}|^2-6\). These are rows 30 through 59.

The Gram diagonal and the input moduli are automatic. Since
\(M(b)^*M(b)=6I_6\), the sixth output equation for each column follows
from the first five. Thus \(F=0\) is equivalent to all of (62.2).
Order the variables as

\[
 z=(\theta_{10},\ldots,\theta_{50},
 \theta_{11},\ldots,\theta_{51},\ldots,
 \theta_{15},\ldots,\theta_{55},b)\in\mathbb R^{31}.
\]

Write \(\mathcal J=DF(0,0)\), and let \(Q_{\mathrm{full}}\) be the
homogeneous degree-two term of
\(F(z)=\mathcal Jz+Q_{\mathrm{full}}(z)+O(\|z\|^3)\).

### 62.3 Exact rank and the full three-dimensional kernel

Put \(p=(\sqrt3+i)/2\), \(t=-2i/\sqrt3\), and let \(I=I_3\).
Differentiating the actual radical family (60.1) gives

\[
 M'(0)=\begin{pmatrix}pI&-pI\\-\bar pI&-\bar pI\end{pmatrix},
 \qquad
 M''(0)=\begin{pmatrix}tI&tI\\-tI&tI\end{pmatrix}.
\tag{62.3}
\]

Set \(Y=M(0)V\), \(Y'=M'(0)V\). Before taking real and imaginary
parts, the Gram derivative at the variable \(\theta_{r\ell}\) is

\[
 i\bar V_{rj}V_{rk}(\delta_{\ell k}-\delta_{\ell j});
\]

its parameter derivative is zero. For the output row indexed by \((a,k)\),

\[
 \begin{aligned}
 \partial_{\theta_{r\ell}}F_{ak}
   &=2\delta_{\ell k}\operatorname{Re}
       (i\bar Y_{ak}M(0)_{ar}V_{rk}),\\
 \partial_bF_{ak}&=2\operatorname{Re}(\bar Y_{ak}Y'_{ak}).
 \end{aligned}
\tag{62.4}
\]

These formulas specify the full real matrix \(\mathcal J\) over
\(\mathbb Q(\sqrt3)\). Select columns \(0,\ldots,27\) and rows

\[
 \rho=(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,19,
 22,23,29,30,31,32,35,36,40,50).
\]

Exact elimination gives

\[
 \det\mathcal J[\rho,0{:}28]=-153055008\ne0.
\tag{62.5}
\]

Here \(0{:}28\) denotes columns zero through 27. To describe the full
kernel, put \(s=\sqrt3\) and define

\[
 \begin{aligned}
 A_+&=(-2+s,-1+s,-1+s,s,-2),\\
 A_-&=(-1,1+s,-1+s,1,0),\\
 B_+&=(-1+s,-2+s,-1+s,-2,s),\\
 B_-&=(1+s,-1,-1+s,0,1).
 \end{aligned}
\]

Let \(K_1\) have successive five-phase blocks
\((A_+,A_-,A_+,A_-,A_+,A_-)\) and final parameter coordinate zero.
Define \(K_2\) similarly with \(B_+,B_-\). Let \(K_c\) have final
parameter coordinate one and phase entries

\[
 (K_c)_{rk}=
 \begin{cases}-1,&k\ge2\text{ and }r\ge3,\\0,&\text{otherwise}.
 \end{cases}
\]

Direct multiplication in (62.4) gives
\(\mathcal JK_1=\mathcal JK_2=\mathcal JK_c=0\). Their coordinate
submatrix on indices \((28,29,30)\) is

\[
 \begin{pmatrix}1&0&-1\\0&1&-1\\0&0&1\end{pmatrix}.
\]

It has determinant one. Together with (62.5), this proves

\[
 \operatorname{rank}\mathcal J=28,\qquad
 \ker\mathcal J=\operatorname{span}_{\mathbb R}\{K_1,K_2,K_c\}.
\tag{62.6}
\]

The vector \(K_c\) is the tangent to the actual canonical family.
The repeated patterns of \(K_1,K_2\) are consequences of the complete
Jacobian calculation, not assumptions on candidate bases.

### 62.4 Four annihilators and the exact quadratic obstruction

The following sparse rows \(\Lambda_0,\ldots,\Lambda_3\) have length
60. Each displayed pair is (row index, coefficient), omitted entries
are zero, and \(s=\sqrt3\):

\[
\begin{aligned}
\Lambda_0:\quad&
(2,s/9),(3,-1/9),(8,-1/9),(9,-s/27),\\
&(22,-1/9),(23,s/27),(30,-s/162),(31,-2s/81),\\
&(32,-2s/81),(33,-s/54),(34,-s/27),\\
&(40,2s/81),(41,-s/81),(42,-s/81);\\[2pt]
\Lambda_1:\quad&
(2,1/9),(8,-s/27),(22,-s/27),(31,-1/108),\\
&(32,-1/54),(34,-1/36),(40,1/54),(42,-1/54);\\[2pt]
\Lambda_2:\quad&
(2,(1-s)/12),(3,-(s+1)/12),\\
&(8,1/12-s/36),(9,-1/12-s/36),\\
&(22,1/12-s/36),(23,s/36+1/12),\\
&(30,s/108+1/36),(31,-s/54),(32,-1/36+s/108),\\
&(40,1/36-s/108),(41,-1/36-s/108),(42,s/54);\\[2pt]
\Lambda_3:\quad&
(2,-1/6),(3,-1/6),(8,s/18),(9,-s/18),\\
&(22,s/18),(23,s/18),(30,s/54),\\
&(31,-1/36-s/108),(32,1/36-s/108),\\
&(40,-1/36+s/108),(41,-s/54),(42,s/108+1/36).
\end{aligned}
\tag{62.7}
\]

Let \(\Lambda\) be the matrix with these four rows. Exact substitution
in the original derivatives gives

\[
 \Lambda\mathcal J=0,\qquad
 \Lambda Q_{\mathrm{full}}(xK_1+yK_2+bK_c)
 =\begin{pmatrix}x^2-y^2\\xy-\frac{\sqrt3}{2}y^2\\bx\\by\end{pmatrix}.
\tag{62.8}
\]

For an explicit expansion of the second identity, let \(\Phi\) be the
phase-coordinate matrix of \(xK_1+yK_2+bK_c\), with its first row zero.
Using coordinatewise multiplication \(\odot\) and coordinatewise
squaring, put

\[
 \begin{aligned}
 Z_1&=iV\odot\Phi,& Z_2&=-\tfrac12V\odot\Phi^2,\\
 Y_1&=M(0)Z_1+bM'(0)V,&
 Y_2&=M(0)Z_2+bM'(0)Z_1+\tfrac12b^2M''(0)V.
 \end{aligned}
\tag{62.9}
\]

For \(j<k\), the complex Gram quadratic term is

\[
 -\frac12\sum_{r=0}^5\bar V_{rj}V_{rk}
       (\Phi_{rk}-\Phi_{rj})^2.
\]

The output quadratic term is
\(|(Y_1)_{ak}|^2+2\operatorname{Re}(\bar Y_{ak}(Y_2)_{ak})\).
Taking real and imaginary parts in the order of §62.2 gives
\(Q_{\mathrm{full}}\) on the full kernel. Thus (62.3)–(62.9) are
finite exact formulas for every coefficient of the displayed identities;
no selected phase ansatz has replaced the original constraints.

### 62.5 Analytic elimination and its second-order correction

The free phase variables left by (62.5) are indices 28 and 29, namely
\(\theta_{45}\) and \(\theta_{55}\). Use the coordinates

\[
 \theta_{45}=x-\arctan b,\qquad
 \theta_{55}=y-\arctan b.
\tag{62.10}
\]

The analytic implicit-function theorem, applied to the selected 28
original equations, solves uniquely for the other 28 phases in terms of
\((b,x,y)\) near zero. Denote the resulting full 31-coordinate map by
\(\Psi(b,x,y)\). Every nearby zero of all 60 equations lies in this chart.

The actual canonical phase curve has all upper-channel phases zero.
Its lower-channel relative phases, for both signs of each mode, are

\[
 \theta^{\rm can}_{r,0}(b)=\theta^{\rm can}_{r,1}(b)
 =\arctan\frac{2b^3}{b^2+3}\quad(r\ge3),
 \qquad
 \theta^{\rm can}_{rk}(b)=-\arctan b\quad(r\ge3,\ k\ge2).
\tag{62.11}
\]

Indeed \(g_0/i=(b^2+3+2ib^3)/(ck)\) has positive real part near zero,
and \(g_1/i=(1-ib)/c=e^{-i\arctan b}\). The minus-column signs cancel
against their signs in \(V\). These identities and IFT uniqueness give

\[
 \Psi(b,0,0)=(\theta^{\rm can}(b),b)
\tag{62.12}
\]

for the exact canonical family, not just its tangent.

The first derivative of \(\Psi\) is \(xK_1+yK_2+bK_c\), by (62.6)
and the prescribed free coordinates (62.10). Write

\[
 \Psi(b,x,y)=xK_1+yK_2+bK_c+E_2(b,x,y)
               +O((|b|+|x|+|y|)^3),
\]

where \(E_2\) is the actual quadratic correction from eliminating the
regular variables. Define the analytic reduced residual
\(G=\Lambda F\circ\Psi\). Its quadratic term is

\[
 \Lambda\bigl(\mathcal JE_2+
 Q_{\mathrm{full}}(xK_1+yK_2+bK_c)\bigr).
\]

The first summand vanishes exactly by \(\Lambda\mathcal J=0\).
The quadratic part is therefore precisely the four-vector in (62.8).
No second-order eliminated variable has been omitted or assumed zero.
Moreover \(G(b,0,0)=0\) identically by (62.12).

### 62.6 Coercivity, the factored remainder, and the proof

Put \(r=\sqrt{x^2+y^2}\) and

\[
 q(b,x,y)=(x^2-y^2,xy-\tfrac{\sqrt3}{2}y^2,bx,by).
\]

For \(m=(x^2,xy,y^2)^T\), define

\[
 T=\begin{pmatrix}
 1&0&-15/16\\
 0&7/8&-\sqrt3/2\\
 -15/16&-\sqrt3/2&7/4
 \end{pmatrix},\qquad
 B=T-\operatorname{diag}(1/1024,1/512,1/1024).
\]

The leading principal minors of \(B\) are

\[
 \frac{1023}{1024},\qquad
 \frac{457281}{524288},\qquad
 \frac{4775103}{536870912},
\]

all positive. Hence \(B\) is positive definite, and direct expansion yields

\[
 (x^2-y^2)^2+(xy-\tfrac{\sqrt3}{2}y^2)^2
       -\frac{(x^2+y^2)^2}{1024}=m^TBm\ge0.
\]

It follows that \(\|q\|\ge r^2/32\). Its last two coordinates also give
\(\|q\|\ge|b|r\). Taking half the sum of these lower bounds gives

\[
 \|q(b,x,y)\|\ge\frac{r(|b|+r)}{64}.
\tag{62.13}
\]

Let \(R=G-q\). It is analytic, all its Taylor terms through degree two
vanish, and \(R(b,0,0)=0\). On a sufficiently small convex chart
neighborhood, Taylor's theorem applied to the derivative in \((x,y)\)
gives a finite constant \(L\) such that

\[
 \|D_{(x,y)}R(b,x,y)\|\le L(|b|+r)^2.
\]

Integrating this derivative along \(t\mapsto(b,tx,ty)\) gives

\[
 \|R(b,x,y)\|\le Lr(|b|+r)^2.
\tag{62.14}
\]

The factor \(r\) is essential and follows from the exact axis identity,
not just from the vanishing quadratic jet. This estimate is uniform even
when \(r\) is arbitrarily smaller than \(b^2\).

If \(G=0\) and \(r>0\), (62.13)–(62.14) imply
\(1/64\le L(|b|+r)\). Shrink the neighborhood so that
\(L(|b|+r)<1/64\). The contradiction forces \(r=0\) for every nearby
full solution. Equation (62.12) then identifies it with the actual
canonical family. This proves Theorem 62.1. No explicit radius for this
neighborhood is asserted.

### 62.7 Uniform basis separation on compact parameter sets

**Corollary 62.2 (compact-parameter canonical-basis separation).**
For every compact \(K\subset(-1,1)\), there exists \(\eta_K>0\) such
that every noncanonical actual common-flat orthonormal input basis
\(B\) at a parameter \(b\in K\) satisfies

\[
 \inf_{D,\Pi}\left\|B-\frac{C(b)D\Pi}{\sqrt6}\right\|_F
 \ge\eta_K,
\tag{62.15}
\]

where \(D\) ranges over diagonal unitary matrices and \(\Pi\) over
column permutation matrices. No explicit value of \(\eta_K\) is claimed.
The set \(K\) may contain zero.

**Proof.** Fix the first entry of each unnormalized input column to one.
The resulting 30-phase torus is compact. The common-flat orthonormal
basis equations define a closed subset of its product with \(K\), and
quotienting by the finite column-permutation action preserves compactness.
The moving canonical graph is compact, hence closed in this solution space.

It is also relatively open. At zero this follows from Theorem 62.1.
At each nonzero parameter, the canonical-ray separation of
[§49](MUB_SIX_FOURTH_BASIS_THEORY.md#49-实参数支上-canonical-射线的显式隔离半径)
gives the lower bound \(|a(b)|/80\) for a distinct ray, with
\(a(b)=b\sqrt{(3-b^2)/(1+b^2)}\). On a sufficiently small interval
around a fixed nonzero parameter this bound stays positive. Together with
continuity of \(C(b)\), it makes the canonical basis graph relatively
open there as well.

Its complement in the compact solution space is consequently compact.
The distance in (62.15), minimized over the compact phase and permutation
group, is continuous and has no zero on this complement. Its minimum is
strictly positive whenever the complement is nonempty. If it is empty,
any positive constant satisfies the assertion. This proves the corollary.

The convention in (62.15) is the input-basis convention of (62.1).
For ordinary common-unbiased column completions, multiplication of both
terms by \(H_0(b)\) leaves the Frobenius distance unchanged, so the same
bound holds with \(B\) and \(C(b)/\sqrt6\) replaced by
\(H_0(b)B\) and \(H_0(b)C(b)/\sqrt6\).

Unlike the punctured single-ray bound, this compactness consequence stays
positive across the center; it applies to complete bases, not to
individual rays. Neither the proof nor the corollary uses a finite census
of central rays or completions. The noncanonical orthogonal-triple problem
outside this canonical neighborhood, and a general fourth-basis
exclusion for the paired-circulant family, remain open.

## 63. The local graph of the displayed central noncanonical completion

### 63.1 Six unrestricted ray germs

Return to the six noncanonical rays of (61.3), in the order
\((u_0,u_1,u_2,\Theta u_0,\Theta u_1,\Theta u_2)\).
To distinguish this representative from the canonical matrix in §62,
write

\[
 V_{\rm nc}=U\operatorname{diag}(1,1,1,-\gamma,-\gamma,-\gamma)
\]

for its first-row-dephased unit-entry matrix. All its columns are
orthogonal and common-flat for the actual central seed, as proved in
§61.2. Here and throughout this section the parameter varies in the
same actual real family \(M(b)=\sqrt6H_0(b)\).

**Theorem 63.1 (repo-derived local noncanonical graph).**
There are six disjoint ray neighborhoods \(\mathcal U_0,\ldots,
\mathcal U_5\) and \(\varepsilon>0\) such that for each
\(|b|<\varepsilon\) the common-flat ray locus in their union consists
of exactly six rays \(v_j(b)\), depending analytically on \(b\), with
\(v_j(0)=[(V_{\rm nc})_{:j}/\sqrt6]\).
At \(b=0\) their orthogonality graph is \(K_6\). For every
\(0<|b|<\varepsilon\), it is exactly

\[
 K_2\text{ on }\{0,3\}\quad\sqcup\quad
 K_{2,2}\text{ between }\{1,2\}\text{ and }\{4,5\}.
\tag{63.1}
\]

In particular no common-flat orthogonal triple at such a nonzero
parameter has all three rays in this union. Every three-column subset
of the displayed central basis is locally isolated in joint
parameter-and-triple space, modulo its column phases and ordering.
Nearby candidates are arbitrary; no cyclic or reflection covariance
is assumed.

### 63.2 Exact continuation from the original single-ray equations

For each column \(j\), use the complete five-phase chart

\[
 z_j(\theta)_r=(V_{\rm nc})_{rj}e^{i\theta_r},
 \qquad \theta_0=0.
\]

Take the five original equations
\(F_j(b,\theta)_a=|(M(b)z_j(\theta))_a|^2-6\), \(a=0,\ldots,4\).
The sixth follows from \(M(b)^*M(b)=6I_6\), so no condition has been
dropped from the common-flat system. Put
\(Y=M(0)V_{\rm nc}\), \(Y'=M'(0)V_{\rm nc}\), with \(M'(0)\) as
in (62.3). The phase Jacobian \(A_j\) and parameter column \(f_j\) are

\[
 \begin{aligned}
 (A_j)_{ar}&=2\operatorname{Re}
 (i\bar Y_{aj}M(0)_{ar}(V_{\rm nc})_{rj})\quad(1\le r\le5),\\
 (f_j)_a&=2\operatorname{Re}(\bar Y_{aj}Y'_{aj}).
 \end{aligned}
\tag{63.2}
\]

Exact determinants give

\[
 \det A_j=
 \begin{cases}
 196830\sqrt7/49,&j=0,1,2,\\
 -196830\sqrt7/49,&j=3,4,5.
 \end{cases}
\tag{63.3}
\]

The analytic implicit-function theorem therefore supplies the unique
local common-flat curve \(z_j(b)\) in each ray chart. Shrinking six
product neighborhoods yields a common parameter interval and the six
disjoint neighborhoods in Theorem 63.1.

For explicit differentiation, the phase tangents solve
\(A_j\theta'_j(0)+f_j=0\). With \(s=\sqrt{21}\), they are the rows
of the following matrix divided by 84, in the phase order \(r=1,\ldots,5\):

\[
 \begin{pmatrix}
 0&-48+20s&-104&-104&-56+20s\\
 70-14s&59-17s&-32-14s&38&-21-17s\\
 -70+14s&-11-3s&-32+14s&-102&-91-3s\\
 0&-48-20s&-104&-104&-56-20s\\
 -70-14s&-11+3s&-32-14s&-102&-91+3s\\
 70+14s&59+17s&-32+14s&38&-21+17s
 \end{pmatrix}.
\tag{63.4}
\]

All entries in (63.2)–(63.4) come from the same actual matrix and the
same six original columns. The normalized input rays are represented
by \(z_j(b)/\sqrt6\).

### 63.3 Ten disappearing edges

Let \(h_{jk}(b)=z_j(b)^*z_k(b)\). Since every pair is orthogonal at
zero, \(h_{jk}(0)=0\). Differentiation in the complete charts gives

\[
 h'_{jk}(0)=i\sum_{r=1}^5
 \overline{(V_{\rm nc})_{rj}}(V_{\rm nc})_{rk}
       \bigl(\theta'_{k,r}(0)-\theta'_{j,r}(0)\bigr).
\tag{63.5}
\]

Substitution of (61.2)–(61.3) and (63.4) yields

\[
 |h'_{jk}(0)|^2=
 \begin{cases}
 1075/84,&(j,k)\in\{(0,1),(0,2),(3,4),(3,5)\},\\
 11/14,&(j,k)\in\{(0,4),(0,5),(1,3),(2,3)\},\\
 25/3,&(j,k)\in\{(1,2),(4,5)\},\\
 0,&(j,k)\in\{(0,3),(1,4),(1,5),(2,4),(2,5)\}.
 \end{cases}
\tag{63.6}
\]

For example, \(h'_{12}(0)=5\sqrt3/6+5i/2\).
The first ten derivatives are nonzero. Since \(h_{jk}(b)/b\) tends
to that derivative, each corresponding overlap stays nonzero on a
sufficiently small punctured interval. Taking the minimum of these
finitely many interval radii removes all ten edges simultaneously.
For normalized overlaps the squared derivative values in (63.6) are
divided by 36.

### 63.4 Five persistent edges and local triple isolation

For every real synchronous permutation \(R=\operatorname{diag}(R_3,R_3)\),
where \(R_3\) permutes three coordinates, the actual family obeys
\(RH_0=H_0R\). Also \(H_0\Theta=-\Theta H_0\), with
\(\Theta(x,y)=(-\bar y,\bar x)\). Both operations preserve the
common-flat ray locus. If \(R\) is symmetric, then for every vector
\(w=(x,y)\),

\[
 w^*\Theta w=0,\qquad
 w^*R\Theta w=-\bar x^TR_3\bar y+\bar y^TR_3\bar x=0.
\tag{63.7}
\]

Choose the transposition interchanging coordinates zero and one in both
channels. From (61.3),

\[
 Ru_0=u_0,\qquad Ru_1=\omega u_2,\qquad Ru_2=\omega^2u_1.
\]

Uniqueness of the unrestricted single-ray continuations transports these
projective relations to small \(b\): \(R\) fixes ray 0 and interchanges
rays 1 and 2. The same uniqueness argument identifies the \(\Theta\)
partners as \(0\leftrightarrow3\), \(1\leftrightarrow4\),
\(2\leftrightarrow5\).

Consequently (63.7) preserves edges \((0,3),(1,4),(2,5)\) through
\(\Theta\), and edges \((1,5),(2,4)\) through \(R\Theta\).
They are precisely the five edges not removed by (63.6). This proves
the exact graph (63.1), which has no triangle.

At the central parameter, each of the six neighborhoods contains only
its displayed ray. Hence any one of the twenty central three-column
subsets is the only triple at \(b=0\) in its matched neighborhoods;
at a sufficiently small nonzero parameter, no triple is possible there.
This proves the joint local-isolation assertion in Theorem 63.1.

The theorem is local to the six displayed ray neighborhoods. It neither
enumerates other central rays nor excludes triples using rays outside
their union. Its symmetry identities transport certificates and the
uniquely continued rays; they do not restrict arbitrary candidates to
a covariance ansatz. No exhaustive census or general noncanonical
orthogonal-triple exclusion follows.

## 64. Central reflection-fixed rays and a finite-census congruence

### 64.1 Exact fixed-ray classification

At the actual central seed, put

\[
 \omega=\frac{-1+i\sqrt3}{2},\qquad A=J_3+(\omega-1)I_3,
 \qquad M=\begin{pmatrix}A&A\\\bar A&-\bar A\end{pmatrix}.
\]

Let \(R=\operatorname{diag}(R_3,R_3)\), where \(R_3\) exchanges
coordinates zero and one. Common-flat rays have unit-entry
representatives \(z\) satisfying \(|(Mz)_j|^2=6\).

**Theorem 64.1 (repo-derived reflection-fixed classification).**
Exactly six common-flat rays are projectively fixed by \(R\). After
first-coordinate dephasing, two are

\[
 (1,1,1,i,i,i),\qquad(1,1,1,-i,-i,-i).
\]

The other four are \((1,1,T,g,g,Tq)\), one for each of the four roots

\[
 \begin{gathered}
 G(g)=7g^4+11g^2+7=0,
 \qquad g=\frac{\varepsilon\sqrt3+5\eta i}{2\sqrt7},
 \quad\varepsilon,\eta\in\{-1,1\},\\
 q=\frac{g(21g^2-16)}{35},\qquad
 T=\frac{7\sqrt3\,i g^3+21g^2+13\sqrt3\,i g+14}{20}.
 \end{gathered}
\tag{64.1}
\]

All four are noncanonical. The same count holds for either of the other
synchronous transpositions by conjugation in \(S_3\).

**Proof.** If \(Rz=\lambda z\), its unchanged, nonzero third coordinate
forces \(\lambda=1\). Hence every fixed ray has the unique chart

\[
 z=(1,1,T,g,g,Tq),\qquad |T|=|g|=|q|=1.
\]

Put \(r_\pm=1\pm g\) and \(s_\pm=T(1\pm q)\). Its top outputs are
\(-\omega^2r_++s_+,-\omega^2r_++s_+,2r_++\omega s_+\), and the
bottom outputs are
\(-\omega r_-+s_-,-\omega r_-+s_-,2r_-+\omega^2s_-\).
Since \(A^*A=3I_3\), their channel norms and one equation from each
channel reduce the full six equations exactly to

\[
 \begin{gathered}
 q+q^{-1}=-2(g+g^{-1}),\\
 A_1T+\bar A_1T^{-1}=-R_0,
 \qquad B_1T+\bar B_1T^{-1}=-S_0,\\
 A_1=\omega(1+g^{-1})(1+q),\quad
 B_1=\omega^2(1-g^{-1})(1-q),\\
 R_0=2+g+g^{-1},\qquad S_0=2-g-g^{-1}.
 \end{gathered}
\tag{64.2}
\]

Here the bar sends \(i\) to \(-i\), \(g\) to \(g^{-1}\), and \(q\)
to \(q^{-1}\). For explicit equivalence, let \(F_j=|(Mz)_j|^2-6\)
and set

\[
 \ell=2(g+g^{-1})+q+q^{-1},\quad
 p=A_1T+\bar A_1T^{-1}+R_0,\quad
 r=B_1T+\bar B_1T^{-1}+S_0.
\]

Direct expansion gives \(F_0=F_1=-p+\ell\),
\(F_3=F_4=-r-\ell\),
\(F_0+F_1+F_2=3\ell\), and
\(F_3+F_4+F_5=-3\ell\). Thus \(F=0\) is equivalent to (64.2).

No denominator stratum is discarded. The cases \(g=\pm1\) would
require \(q+q^{-1}=\mp4\), impossible on the unit circle. If \(q=1\),
the norm equation gives \(g+g^{-1}=-1\), and the first bottom output
has squared modulus three. If \(q=-1\), the first top output likewise
has squared modulus three. Both contradict six. Consequently
\(g^2\ne1\), \(q^2\ne1\), and the two-by-two determinant is nonzero:

\[
 \Delta=A_1\bar B_1-\bar A_1B_1
 =\frac{i\sqrt3(g-1)(g+1)(q-1)(q+1)}{gq}.
\]

With \(N=-R_0\bar B_1+S_0\bar A_1\) and
\(O=-S_0A_1+R_0B_1\), Cramer's rule gives \(T=N/\Delta\),
\(T^{-1}=O/\Delta\), and

\[
 \begin{gathered}
 T=\frac{gq-1+(i/\sqrt3)(q-g)}{q^2-1},\\
 NO-\Delta^2
 =\frac{(g-1)^2(g+1)^2(q-g)C(g,q)}{g^3q^2},\qquad
 C(g,q)=3gq^3+gq-q^2-3.
 \end{gathered}
\tag{64.3}
\]

Thus either \(q=g\) or \(C=0\). Multiplying the norm equation by
\(gq\) gives \(E(g,q)=gq^2+2(g^2+1)q+g=0\).
When \(q=g\), it reduces to \(3g(g^2+1)=0\), hence \(g=\pm i\)
and \(T=1\). Otherwise polynomial division and a resultant give

\[
 \begin{aligned}
 C\bmod E&=\frac2g\bigl[(6g^4+12g^2+7)q+g(3g^2+2)\bigr],\\
 \operatorname{Res}_q(E,C)&=12g(g^2+1)(7g^4+11g^2+7).
 \end{aligned}
\tag{64.4}
\]

At \(g=\pm i\), the monic gcd of \(E,C\) is \(q-g\), giving no new
ray. The remaining roots satisfy \(G=0\). The denominator
\(D=6g^4+12g^2+7\) cannot vanish there, because

\[
 \left(-\frac{18g^2}{25}-\frac{149}{175}\right)D+
 \left(\frac{108g^2}{175}+\frac{174}{175}\right)G=1.
\tag{64.5}
\]

Solving (64.4) and reducing (64.3) modulo \(G\) gives exactly (64.1).
Conversely the four distinct roots in (64.1) are unit phases. With
\(\bar g=g^{-1}\), substitution modulo \(G\) gives

\[
 q\bar q=T\bar T=1,\qquad
 |(M(1,1,T,g,g,Tq)^T)_j|^2=6\quad(0\le j\le5).
\tag{64.6}
\]

These are exact rational-function identities: the denominators are
coprime to \(G\), as are \(g\), \(g^2-1\), \(g^2+1\), and the
substituted \(q^2-1\). Thus necessity and sufficiency both hold.
The first coordinate is one and the four values of \(g\) are distinct,
so the four rays are distinct. A canonical ray fixed by this
transposition must have mode zero, hence \(T=1\) and \(g=\pm i\).
The quartic roots do not satisfy \(g^2+1=0\), proving their
noncanonical character. This completes the proof.

### 64.2 Stabilizers and the conditional total count

Let \(\mathcal G\) be the projective group generated by synchronous
\(S_3\) and \(\Theta(x,y)=(-\bar y,\bar x)\).
The identities \(M\Theta=-\Theta M\), \(MR=RM\),
\(R\Theta=\Theta R\), and \(\Theta^2=-I\) show that it preserves
the central common-flat ray locus. Its twelve projective operations
form \(S_3\times C_2\).

**Corollary 64.2 (repo-derived central orbit constraint).**
The canonical rays have orbits of sizes two and four. There are exactly
two noncanonical orbits of size six. Every other noncanonical orbit
has size twelve. If the entire central ray locus is finite, its size is

\[
 N=18+12m\equiv6\pmod{12}
\tag{64.7}
\]

for a nonnegative integer \(m\). No finiteness premise is needed for
the classification of fixed rays or the two noncanonical six-orbits.

**Proof.** No antiunitary operation \(R\Theta\) fixes a ray. Indeed a
unit representative of an antiunitary-fixed ray would satisfy
\(Tv=\lambda v\), \(|\lambda|=1\), and therefore \(T^2v=v\).
For the identity or a transposition \(R\), one has
\((R\Theta)^2=-I\); for a three-cycle, \((R\Theta)^6=-I\).
Both contradict that necessary condition.

A ray fixed projectively by a three-cycle has both three-coordinate
channels in its same one-dimensional Fourier eigenspace. Thus it is
\((f_l,gf_l)\), \(|g|=1\), after dephasing. The corresponding channel
eigenvalues of \(A\) and \(\bar A\) both have squared modulus three.
Flatness forces \(|1+g|^2=|1-g|^2=2\), equivalently \(g=\pm i\).
These are exactly the six canonical rays. Synchronous permutations and
\(\Theta\) give the orbit sizes two and four.

A noncanonical stabilizer lies in \(S_3\), contains no three-cycle,
and cannot contain two distinct transpositions. It is therefore trivial
or generated by one transposition. Its orbit has size twelve or six.
In a six-orbit \(\mathcal G/H\), a specified transposition fixes
exactly two cosets: its centralizer has size four and \(|H|=2\).
Theorem 64.1 gives exactly four noncanonical fixed rays, so precisely
two such six-orbits exist. This proves (64.7) when the whole locus is
finite.

For a separate count check, Burnside's lemma gives the number of orbits
of a finite locus as

\[
 \frac{N+3\cdot6+2\cdot6+6\cdot0}{12}
 =\frac{N+30}{12}\in\mathbb Z.
\tag{64.8}
\]

Here the terms are respectively the identity, three transpositions, two
three-cycles, and six antiunitary operations. This again forces the
congruence without determining \(N\).

### 64.3 Scope and the unresolved reported count

The exact Fourier bridge (61.14)–(61.15) identifies this ray problem
with the ordinary common-unbiased columns for \((I,F(1/6,0))\).
It is a unitary ray bijection, so the change of input/output convention
does not alter finite cardinalities.

[Brierley–Weigert, *Constructing Mutually Unbiased Bases in Dimension Six*,
§4.2 and Table 2](https://arxiv.org/html/0901.4051v2#S4.SS2)
report \(N_v=48\) for their sampled Fourier matrices, including this
parameter; their Eq. (6) already fixes the overall phase. Their §3.4
also discusses upper bounds obtained through numerical approximation.
The congruence (64.7) rules out 48 as an exact finite distinct-ray census
for the actual equations here. Its relation to the reported count and
the scope of that approximation argument remains unresolved. No phase
or multiplicity reinterpretation, source erratum, complete census, or
42-ray completeness is established by this section.

Only the transposition-fixed locus is classified exhaustively. The
remaining free-orbit count, finiteness of the full locus, and arbitrary
noncanonical orthogonal triples remain separate questions.

## 65. The complete local graph on 36 named noncanonical ray germs

### 65.1 Statement and exact parameter reflection

Continue the actual family \(M(b)=\sqrt6H_0(b)\) of (60.1).
Let \(X(x,y)=(y,x)\) and \(L=\operatorname{diag}(I_3,-I_3)\).
Its block coefficients satisfy \(P(-b)=Q(b)\), so

\[
 M(-b)=LM(b)X.
\tag{65.1}
\]

Thus \(X\) transports common-flat input rays at \(b\) to those at
\(-b\). It is a fixed-parameter symmetry at zero, but not in general
away from zero. Synchronous permutations \(R_p\) and the antiunitary
\(\Theta(x,y)=(-\bar y,\bar x)\) preserve the common-flat locus at
each parameter, by the identities in §63.4.

**Theorem 65.1 (repo-derived full 36-ray graph germ).** The 36 central
rays defined below are distinct and noncanonical. Each has a unique
unrestricted analytic common-flat continuation near zero. For some
\(\varepsilon>0\), their orthogonality graph at every
\(0<|b|<\varepsilon\) is the disjoint union of two copies of
\(K_{3,3}\) and two connected four-regular bipartite graphs on twelve
vertices. In particular, there are 36 disjoint ray neighborhoods
whose union contains no common-flat orthogonal triple at these
parameters.

The conclusion controls all edges between the 36 rays, including
edges between different transported six-ray copies. It does not by
itself claim that these neighborhoods cover the entire noncanonical
locus, at zero or away from zero.

### 65.2 Explicit rays, stabilizers, and distinctness

Use the constants and seed rays from §61:

\[
 \begin{gathered}
 \omega=\frac{-1+i\sqrt3}{2},\qquad
 \gamma=-\frac{\sqrt3+5i}{2\sqrt7},\\
 t=-\frac12-\frac{3\sqrt{21}}{28}
       +i\left(-\frac{\sqrt3}{4}+\frac{3\sqrt7}{14}\right),
 \qquad \delta=-\frac{3+i\sqrt7}{4},\\
 \tau=\omega^2t,\quad \sigma=\omega^2\delta,\quad
 f_m=(1,\omega^m,\omega^{2m}),\\
 u_m=((1,1,\tau)\odot f_m,(\gamma,\gamma,\sigma)\odot f_m).
 \end{gathered}
\tag{65.2}
\]

For \(p=(p_0,p_1,p_2)\), define
\(R_p(x,y)=((x_{p_0},x_{p_1},x_{p_2}),
(y_{p_0},y_{p_1},y_{p_2}))\). Put

\[
 \begin{aligned}
 \mathcal P_0&=((0,1,2),(0,2,1),(2,0,1)),\\
 \mathcal P_1&=((0,1,2),(0,2,1),(1,0,2),
                  (1,2,0),(2,0,1),(2,1,0)),\\
 z_{s,p,e,c}&=d(X^c\Theta^eR_pu_s),\qquad d(v)=v/v_0,
 \quad s=0,1,\quad p\in\mathcal P_s,\quad e,c\in\{0,1\}.
 \end{aligned}
\tag{65.3}
\]

Order this list lexicographically by \((s,p,e,c)\) and index its
entries by \(0,\ldots,35\). Here the permutation order is exactly
the displayed order in each \(\mathcal P_s\).

The six-ray construction of §61 proves common flatness of \(u_0,u_1\).
The symmetries and (65.1) prove it for every entry of (65.3).
Distinctness can be checked without a numerical comparison. Both seeds
have channel-ratio triple

\[
 (y_j/x_j)_{j=0}^2=(\gamma,\gamma,q),
 \qquad q=\sigma/\tau=\frac{\sqrt3+2i}{\sqrt7}\ne\gamma.
\tag{65.4}
\]

The unique repeated ratio is \(\gamma\). Under \(\Theta,X,X\Theta\)
it becomes respectively \(-\gamma,\bar\gamma,-\bar\gamma\).
These four values are distinct. Hence an element
\(X^c\Theta^eR_p\) mapping one seed to either seed projectively must
have \(e=c=0\), and then \(p\) fixes the unique \(q\)-position.
The only possibilities are the identity and the transposition
\((0\ 1)\). Both fix \(u_0\); only the identity fixes \(u_1\), since
its first two upper coordinates are \(1,\omega\). Neither maps one
seed to the other, since the upper-coordinate ratio on the repeated
pair is one for \(u_0\) and is \(\omega\) or \(\omega^2\) for \(u_1\).

Projectively these transformations form a group of order 24:
\(S_3\) commutes with \(X,\Theta\), while
\(\Theta^2=-I\), \(X^2=I\), and \(X\Theta=-\Theta X\).
The two disjoint orbits therefore have sizes 12 and 24, and (65.3)
selects them without repetition. Their ratio triples are nonconstant,
whereas every central canonical ray has all three ratios equal to
\(i\) or \(-i\). This also proves noncanonicity.

### 65.3 Unrestricted continuations and reconstructible tangents

The original five-phase Jacobians at \(u_0,u_1\) are invertible by
(63.2)–(63.3). The analytic implicit-function theorem supplies unique
unrestricted common-flat ray curves through these seeds. Transport
by \(R_p,\Theta\), and by \(X\) with the parameter replaced by
\(-b\), is an invertible transformation of the full original solution
set. It therefore supplies unique unrestricted curves through all
36 rays, not just curves within a symmetry-restricted ansatz.

For completeness, the two seed phase tangents needed to reconstruct
every comparison are, in coordinate order \(1,\ldots,5\),

\[
 \begin{aligned}
 \alpha_0&=\frac1{84}(0,-48+20\sqrt{21},-104,-104,-56+20\sqrt{21}),\\
 \alpha_1&=\frac1{84}(70-14\sqrt{21},59-17\sqrt{21},
                 -32-14\sqrt{21},38,-21-17\sqrt{21}).
 \end{aligned}
\tag{65.5}
\]

Set \((v_s)_0=0\), \((v_s)_r=i(u_s)_r\alpha_{s,r}\).
For a label \((s,p,e,c)\), first form

\[
 w=X^c\Theta^eR_pu_s,\qquad
 v=(-1)^cX^c\Theta^eR_pv_s.
\]

The dephased value and velocity are then

\[
 z_r=\frac{w_r}{w_0},\qquad
 \dot z_r=\frac{v_rw_0-w_rv_0}{w_0^2}.
\tag{65.6}
\]

The sign \((-1)^c\) records the parameter reflection in (65.1).
All derivatives are with respect to the real parameter \(b\).
Shrinking finitely many implicit-function neighborhoods gives a
common interval and 36 disjoint fixed ray neighborhoods, each
containing exactly its named curve.

### 65.4 A complete 38-orbit certificate for all 630 pairs

For distinct indices \(j,k\), write

\[
 h_{jk}(0)=\sum_r\bar z_{jr}z_{kr},\qquad
 h'_{jk}(0)=\sum_r(\overline{\dot z_{jr}}z_{kr}
                              +\bar z_{jr}\dot z_{kr}).
\tag{65.7}
\]

These are unnormalized overlaps. The following data reconstruct every
pair comparison using only (65.2)–(65.7). Set
\(A_\pm=(297\pm27\sqrt{21})/56>0\).
The first two group generators, acting on the zero-based indices, are

\[
\begin{aligned}
 R_{(1,0,2)}={}&(4\ 8)(5\ 9)(6\ 10)(7\ 11)
 (12\ 20)(13\ 21)(14\ 22)(15\ 23)\\
 & (16\ 28)(17\ 29)(18\ 30)(19\ 31)
 (24\ 32)(25\ 33)(26\ 34)(27\ 35),\\
 R_{(1,2,0)}={}&(0\ 4\ 8)(1\ 5\ 9)(2\ 6\ 10)(3\ 7\ 11)\\
 &(12\ 24\ 28)(13\ 25\ 29)(14\ 26\ 30)(15\ 27\ 31)\\
 &(16\ 32\ 20)(17\ 33\ 21)(18\ 34\ 22)(19\ 35\ 23).
\end{aligned}
\tag{65.8}
\]

Within each consecutive block \((4r,4r+1,4r+2,4r+3)\),
\(\Theta\) exchanges the first with the third and the second with
the fourth, while \(X\) exchanges the first with the second and the
third with the fourth. Together these four permutations generate all
24 actions. Unlisted indices in (65.8) are fixed.

The 38 rows below are disjoint pair orbits under these generators;
their sizes sum to \(\binom{36}{2}=630\). Thus the table covers all
pairs, not just pairs inside transported six-ray bases. Each value
follows by substitution in (65.7), in the exact field
\(\mathbb Q(\sqrt3,\sqrt7,i)\), using
\((\sqrt3)^2=3\), \((\sqrt7)^2=7\), and \(i^2=-1\).
The last column is needed only when the central overlap is zero.

| Representative | Orbit size | \(|h(0)|^2\) | \(|h'(0)|^2\) if \(h(0)=0\) |
|---|---:|---:|---:|
| \((0,1)\) | 6 | \(0\) | \(400/49\) |
| \((0,2)\) | 6 | \(0\) | \(0\) |
| \((0,3)\) | 6 | \(18\) | — |
| \((0,4)\) | 12 | \(9/4\) | — |
| \((0,5)\) | 12 | \(243/28\) | — |
| \((0,6)\) | 12 | \(0\) | \(0\) |
| \((0,7)\) | 12 | \(18/7\) | — |
| \((0,12)\) | 24 | \(0\) | \(1075/84\) |
| \((0,13)\) | 24 | \(27/7\) | — |
| \((0,14)\) | 24 | \(0\) | \(11/14\) |
| \((0,15)\) | 24 | \(36/7\) | — |
| \((0,16)\) | 24 | \(A_+\) | — |
| \((0,17)\) | 24 | \(A_+\) | — |
| \((0,18)\) | 24 | \(81/7\) | — |
| \((0,19)\) | 24 | \(99/14\) | — |
| \((0,24)\) | 24 | \(A_-\) | — |
| \((0,25)\) | 24 | \(A_-\) | — |
| \((0,26)\) | 24 | \(81/7\) | — |
| \((0,27)\) | 24 | \(99/14\) | — |
| \((12,13)\) | 12 | \(0\) | \(100/49\) |
| \((12,14)\) | 12 | \(0\) | \(0\) |
| \((12,15)\) | 12 | \(36/7\) | — |
| \((12,16)\) | 12 | \(A_-\) | — |
| \((12,17)\) | 12 | \(A_-\) | — |
| \((12,18)\) | 12 | \(0\) | \(0\) |
| \((12,19)\) | 12 | \(18/7\) | — |
| \((12,20)\) | 12 | \(0\) | \(25/3\) |
| \((12,21)\) | 12 | \(27/7\) | — |
| \((12,22)\) | 12 | \(0\) | \(0\) |
| \((12,23)\) | 12 | \(18\) | — |
| \((12,24)\) | 24 | \(9/4\) | — |
| \((12,25)\) | 24 | \(243/28\) | — |
| \((12,26)\) | 24 | \(81/7\) | — |
| \((12,27)\) | 24 | \(99/14\) | — |
| \((12,32)\) | 12 | \(A_+\) | — |
| \((12,33)\) | 12 | \(A_+\) | — |
| \((12,34)\) | 12 | \(0\) | \(0\) |
| \((12,35)\) | 12 | \(18/7\) | — |

The orbit reduction is valid for the derivatives in the table:
transport changes an overlap to a unit-modulus scalar times the
original overlap or its conjugate, evaluated at \(b\) or \(-b\).
At a zero central overlap, differentiating the scalar contributes
zero. Hence both \(|h(0)|\) and, on the zero-overlap stratum,
\(|h'(0)|\) are invariant along a pair orbit.

The table gives 486 nonedges at zero, 78 simple-zero edges, and
66 edges with zero first derivative. Among the 78 simple-zero edges,
the squared derivative values and multiplicities are

\[
 (400/49,6),\ (1075/84,24),\ (11/14,24),\
 (100/49,12),\ (25/3,12).
\tag{65.9}
\]

The 486 nonzero overlaps stay nonzero by continuity. For each of the
78 simple-zero overlaps, \(h_{jk}(b)/b\to h'_{jk}(0)\ne0\), so it
is nonzero on a sufficiently small punctured interval. A common
interval works for all finitely many pairs. Normalizing the vectors
divides overlaps by six and squared overlap derivatives by 36.

### 65.5 Exact persistence and the bipartite graph

There is no unresolved higher-order case among the remaining 66
pairs. Their six orbit representatives are respectively obtained
from the first ray by \(R\Theta\) with the following synchronous
three-coordinate permutation:

\[
\begin{array}{c|cccccc}
 (j,k)&(0,2)&(0,6)&(12,14)&(12,18)&(12,22)&(12,34)\\
 R_3&I&(1\ 2)&I&(1\ 2)&(0\ 1)&(0\ 2).
\end{array}
\tag{65.10}
\]

Each \(R_3\) is real symmetric. The identity (63.7) therefore makes
\(w^*R\Theta w=0\) for every vector \(w\), at every parameter.
Conjugating by any of the 24 projective symmetries preserves this
class of relations; when \(X\) occurs, both curves undergo the same
parameter reflection. Uniqueness of each unrestricted ray curve
identifies the transported curve with its named continuation.
Consequently every pair in these six orbits persists exactly.

The four connected components are indexed by the seed type \(s\)
and the flag \(c\) in (65.3). The two parts in each component are
\(e=0\) and \(e=1\). For \(s=0\), the four operations \(R\Theta\)
with \(R_3\) the identity or a transposition give three distinct
neighbors, hence \(K_{3,3}\). For \(s=1\), they give four distinct
neighbors in the opposite part. These twelve-vertex graphs are
connected because the three transpositions generate \(S_3\).
The table excludes every other edge, including all edges between
these components. Thus the graph is bipartite and triangle-free.

An arbitrary common-flat orthogonal triple in the union of the 36
neighborhoods would have to consist of three of these unique ray
curves. Distinct orthogonal rays cannot coincide, and the graph has
no triangle. This proves Theorem 65.1 without a covariance assumption
on the candidate triple. \(\square\)

## 66. Exact classification of all central common-flat rays

### 66.1 Central census theorem

At \(b=0\), write

\[
 M=\begin{pmatrix}A&A\\\bar A&-\bar A\end{pmatrix},
 \qquad A=J_3+(\omega-1)I_3,\qquad
 \omega=\frac{-1+i\sqrt3}{2}.
\]

**Theorem 66.1 (repo-derived exact central census).** The entire
projective common-flat input locus of this matrix consists of
exactly 42 rays: the six canonical rays and the 36 noncanonical rays
in (65.3).

The following proof establishes an upper bound for every solution
of the original equations. Finiteness, covariance, and completeness
of a numerical sample are not assumptions.

### 66.2 Equivalent Fourier correlations and all pole strata

Let \(F=(\omega^{jk})_{0\le j,k\le2}\),
\(D=\operatorname{diag}(1,\omega^2,\omega^2)\), and
\(E=\operatorname{diag}(\omega,1,1)\). Entrywise multiplication gives

\[
 A=E\bar FD,\qquad \bar A=\bar EF\bar D,
 \qquad \bar DD^{-1}=D.
\tag{66.1}
\]

For a unit-entry input \((x,y)\), put \(\alpha=Dx\), \(\beta=Dy\),
and \(t_j=\beta_j/\alpha_j=y_j/x_j\). The two Fourier inputs are
\(v=\alpha+\beta\) and \(w=D(\alpha-\beta)\).
For either \(F\) or \(\bar F\), the three squared output moduli of
a vector \(h\in\mathbb C^3\) equal six exactly when

\[
 \sum_j|h_j|^2=6,\qquad
 \sum_j\bar h_jh_{j+1}=0,
\tag{66.2}
\]

where indices are modulo three. This is the direct expansion of the
three Fourier squared moduli, using \(1+\omega+\omega^2=0\).
With \(e_j=\bar\alpha_j\alpha_{j+1}\), the original six output
conditions are therefore equivalent to

\[
 \begin{gathered}
 \sum_j\operatorname{Re}t_j=0,\qquad
 \sum_je_j(1+t_j^{-1})(1+t_{j+1})=0,\\
 \sum_j\rho_je_j(1-t_j^{-1})(1-t_{j+1})=0,
 \qquad (\rho_0,\rho_1,\rho_2)=(\omega^2,1,\omega).
 \end{gathered}
\tag{66.3}
\]

Here \(|e_j|=|t_j|=1\) and \(e_0e_1e_2=1\).

No \(t_j=-1\) is possible. If exactly one ratio equals \(-1\),
exactly one coordinate of \(v\) is zero, and its cyclic correlation
has precisely one nonzero summand. If at least two ratios equal
\(-1\), at most one coordinate of \(v\) is nonzero, with squared
modulus at most four, contradicting its norm six. The identical
argument with \(w\) excludes \(t_j=1\). Thus every ratio has the
unique finite nonzero real Cayley parameter

\[
 t_j=\frac{1+iu_j}{1-iu_j},\qquad u_j\in\mathbb R\setminus\{0\}.
\tag{66.4}
\]

This treats both the infinite-parameter and zero-parameter strata,
including the cases where two or all three ratios equal a pole.

### 66.3 Repeated-ratio rigidity for every original solution

Write \((u_0,u_1,u_2)=(a,b,c)\), and define

\[
 B_j=\frac4{(1+iu_j)(1-iu_{j+1})},\quad
 k_j=\rho_ju_ju_{j+1},\quad f_j=e_jB_j.
\]

The two correlation equations reduce to

\[
 f_0+f_1+f_2=0,\qquad k_0f_0+k_1f_1+k_2f_2=0.
\tag{66.5}
\]

The \(k_j\) are pairwise distinct: equality of two would equate a
nonreal cube root of unity with a nonzero real ratio. Consequently
this system has rank two, its kernel is spanned by

\[
 K=(k_1-k_2,k_2-k_0,k_0-k_1),
\]

and every coordinate of \(K\) is nonzero. Write \(f=\lambda K\).
The unit-modulus conditions on \(e_j\), together with
\(\operatorname{Re}(\rho_j\bar\rho_k)=-1/2\) for \(j\ne k\), give

\[
 \frac{c^2(a^2+b^2+ab)}{1+c^2}
 =\frac{a^2(b^2+c^2+bc)}{1+a^2}
 =\frac{b^2(c^2+a^2+ca)}{1+b^2}.
\tag{66.6}
\]

All cancelled denominators and common factors are positive.
Suppose \(a,b,c\) were pairwise distinct. The first equality factors
as \((a-c)T(a,b,c)=0\), where

\[
 T(a,b,c)=a^3c^2+a^2bc^2+a^2c^3-ab^2-abc-b^2c.
\]

Hence \(T(a,b,c)=T(b,c,a)=T(c,a,b)=0\). Put
\(S=a+b+c\), \(P=ab+bc+ca\), and \(H(t)=St^2(S-t)+P\).
The exact identities

\[
 T(a,b,c)-T(b,c,a)=(c-b)H(a),\qquad
 H(a)-H(b)=SP(a-b)
\tag{66.7}
\]

and their cyclic versions give \(H(a)=H(b)=H(c)=0\) and \(SP=0\).
If \(S=0\), then \(P=0\), so
\(a^2+b^2+c^2=S^2-2P=0\), a contradiction. If \(S\ne0\), then
\(P=0\), and \(H(a)=Sa^2(b+c)=0\). Since \(a\ne0\), the three
cyclic equations force \(b+c=c+a=a+b=0\), again a contradiction.
Thus every original common-flat ray has two equal channel ratios.

### 66.4 Exhaustive elimination of the repeated-ratio sector

If \(a=b=c\), the norm equation gives
\(3(1-a^2)/(1+a^2)=0\), so \(a=\pm1\). There are two possible
all-equal ordered ratio triples.

Otherwise the equal pair is unique. A cyclic relabeling places it
at \((u_0,u_1,u_2)=(a,a,c)\), with \(c\ne a\). Equation (66.6)
and the norm equation give respectively

\[
 \begin{gathered}
 (a-c)(2ac^2-a+c^3-2c)=0,\\
 N(a,c)=3-a^2+c^2-3a^2c^2=0.
 \end{gathered}
\tag{66.8}
\]

Let \(T_2=2ac^2-a+c^3-2c\), \(D_0=3a^2-1\),
\(H_0=7a^2-5\), and \(L_0=H_0c+a(5a^2-7)\). Then

\[
 D_0T_2+L_0=-(2a+c)N.
\tag{66.9}
\]

Since \(T_2=N=0\), this gives \(L_0=0\) without division.
The case \(H_0=0\) is impossible: it would give
\(a^2=5/7\) and \(L_0=-24a/7\ne0\). Therefore

\[
 c=\frac{a(7-5a^2)}{7a^2-5}.
\tag{66.10}
\]

Also \(D_0=0\) is impossible because \(N=8/3\) when \(a^2=1/3\).
The remaining substitution is the exact identity

\[
 H_0^2N\left(a,\frac{a(7-5a^2)}{H_0}\right)
 =-3(a^2-1)(a^2+1)(25a^4-62a^2+25).
\tag{66.11}
\]

The real factor \(a^2+1\) is positive. If \(a^2=1\), the norm
forces \(c^2=1\). The unequal case has \(c=-a\), but then
\(T_2(a,-a)=a(a^2+1)=2a\ne0\), impossible. Thus the repeated
parameter lies among precisely four distinct real quartic roots:

\[
 25a^4-62a^2+25=0,\qquad
 a=\frac{\pm\sqrt{31+4\sqrt{21}}}{5}
 \quad\hbox{or}\quad
 a=\frac{\pm\sqrt{31-4\sqrt{21}}}{5}.
\tag{66.12}
\]

The radicands are positive and unequal. None of these roots is
zero or \(\pm1\), and none makes \(D_0H_0\) vanish. For each root,
(66.10) leaves at most one \(c\). There are therefore at most four
non-all-equal ratio triples for each of the three possible equal-pair
positions.

### 66.5 Exact projective phase counting and attainment

Fix one possible ordered ratio triple. The numbers \(B_j,K_j\) from
§66.3 are nonzero and fixed. The phase equations imply

\[
 e_j=\lambda K_j/B_j,\qquad
 \lambda^3=\frac{B_0B_1B_2}{K_0K_1K_2}\ne0.
\tag{66.13}
\]

There are exactly three distinct complex roots of the cubic, hence
at most three admissible phase lifts. Each root determines at most
one projective input ray: dephase \(x_0=\alpha_0=1\), then set
\(\alpha_1=e_0\), \(\alpha_2=e_0e_1\). The third cyclic relation
is precisely \(e_0e_1e_2=1\). These determine \(x=D^{-1}\alpha\)
and \(y_j=t_jx_j\) uniquely. Unit-modulus requirements can remove
cubic roots but cannot add any. Thus this counts projective rays,
not algebraic multiplicities or different global phases.

The all-equal sector has at most \(2\cdot3=6\) rays. The other
sector has at most \(3\cdot4\cdot3=36\) rays. The sectors are
disjoint, and a non-all-equal triple has only one equal pair, so no
positional ambiguity affects this upper bound. The entire original
locus has at most 42 rays; in particular, finiteness is a conclusion.

The six canonical rays \((f_m,\pm if_m)\), \(m=0,1,2\), attain
the first count. Section 65.2 constructs 36 distinct noncanonical
rays, verifies original common flatness by the explicit seed and
exact symmetries, and proves their distinctness and disjointness
from the canonical set. They attain the other count. This proves
Theorem 66.1. \(\square\)

The exact central count now follows from the original equations and
the displayed construction, independently of the numerical counts
discussed in §64. It does not resolve how the external reported
count was obtained or interpreted, and no external count is used as
an upper-bound premise.

## 67. Punctured central uniqueness and local quartet exclusion

### 67.1 Complete-basis classification

Let \(C(b)\) denote the unit-entry canonical **input** matrix of §62,
so \(C(b)^*C(b)=6I_6\) and \(|M(b)C(b)|^2=6\) entrywise.

**Theorem 67.1 (repo-derived punctured central classification).**
There exists \(\varepsilon>0\) such that, for every
\(0<|b|<\varepsilon\), any complete common-flat input basis is
\(C(b)/\sqrt6\), up to column phases and permutation.

**Proof.** Dephase the first coordinate of each unnormalized unit-entry
column to one. An ordered complete basis is then a point of the
compact torus \((S^1)^{30}\), subject to

\[
 |(M(b)z_k)_r|^2=6,\qquad z_j^*z_k=6\delta_{jk}.
\tag{67.1}
\]

These equations are continuous in \(b\) and the phase coordinates.
If the theorem were false, there would be a sequence
\(0<|b_n|<1/n\) and noncanonical complete common-flat bases \(Z_n\).
After passage to a subsequence in the compact torus, \(Z_n\to Z_*\).
The limit satisfies (67.1) at zero. Its six column rays remain
mutually orthogonal and distinct; no zero-coordinate or colliding-ray
limit can occur.

If one column of \(Z_*\) is canonical, Corollary 60.4 makes the
entire limiting basis canonical. Apply a fixed permutation of its
columns to match the ordering of \(C(0)\). The dephasing already
removes all column-phase ambiguity. The sequence then eventually
lies in the joint canonical-basis neighborhood of Theorem 62.1.
That theorem forces \(Z_n\) to equal the moving canonical basis,
contradicting its choice. This step uses the complete 30-phase basis
germ, not a restriction fixing any individual ray.

If no column of \(Z_*\) is canonical, Theorem 66.1 places all six
among the 36 noncanonical rays of §65. Choose any three columns.
They converge to three distinct centers of the fixed disjoint ray
neighborhoods in Theorem 65.1. For sufficiently large \(n\), the
three corresponding columns of \(Z_n\) lie in those neighborhoods
and \(b_n\) lies in their common punctured interval. This is a
common-flat orthogonal triple forbidden by Theorem 65.1.

The two cases exhaust the exact central census. Both contradict the
assumed sequence, proving the theorem. The canonical basis exists
throughout the open branch, so the conclusion is uniqueness rather
than an empty-locus assertion. \(\square\)

### 67.2 Explicit transport to the fixed MUB pair

**Corollary 67.2.** For \(0<|b|<\varepsilon\), the pair
\((I_6,H_0(b))\) admits exactly one common-unbiased basis up to column
phases and permutation, namely

\[
 B_{\rm can}(b)=H_0(b)C(b)/\sqrt6.
\tag{67.2}
\]

Consequently this fixed pair cannot belong to a quartet of mutually
unbiased bases on that punctured parameter interval.

**Proof.** A unitary matrix \(B\) is unbiased to both members of the
pair exactly when both \(B\) and \(H_0(b)^*B\) have entry moduli
\(1/\sqrt6\). Set \(W=H_0(b)^*B\). Then \(W\) is unitary and both
\(W\) and \(H_0(b)W=B\) are flat. Thus \(W\) is precisely a
common-flat input basis in the convention of Theorem 67.1.
That theorem gives \(W=C(b)/\sqrt6\) up to phases and permutation,
which yields (67.2). Conversely (67.2) satisfies both flatness
conditions by the defining canonical identities.

A quartet extending the pair would supply two additional common-
unbiased bases. Both would have the same column-ray set (67.2).
Their relative unitary would therefore be monomial, with entry moduli
zero or one, rather than all \(1/\sqrt6\). They cannot be mutually
unbiased. \(\square\)

### 67.3 Scope of the local conclusion

The radius \(\varepsilon\) is positive but is not evaluated numerically.
The parameter is restricted to the actual one-parameter family of
(60.1). No exclusion on the entire open branch or for every
six-dimensional Hadamard pair follows from this local argument.

Zero is excluded from the uniqueness theorem: the explicit
noncanonical complete central basis in §61 remains a genuine
exception. The proof also does not classify every noncanonical
single-ray branch approaching a canonical ray, or exclude every
arbitrary noncanonical orthogonal triple near such rays. Compactness
closes the complete-basis problem by using the full canonical-basis
germ in precisely that limiting case.

## 68. An exact central overlap gap and ambient quartet exclusion

### 68.1 Pairwise gap and neighborhood theorem

Let \(H_\star=H_0(0)\). For a unitary matrix \(H\), define

\[
 \mathcal F(H)=\left\{v\in\mathbb C^6:
 |v_r|^2=|(Hv)_r|^2=\frac16\text{ for }r=0,\ldots,5\right\}.
\tag{68.1}
\]

These are normalized common-flat input vectors. Put

\[
 \delta=\frac{9\sqrt7-21}{14}>0.
\]

**Theorem 68.1 (repo-derived central gap and ambient exclusion).**
The exact central minimum is

\[
 \min_{v,w\in\mathcal F(H_\star)}
 \left|\,|v^*w|^2-\frac16\right|
 =\frac\delta{36}=\frac{9\sqrt7-21}{504}.
\tag{68.2}
\]

The minimum includes equal rays and both orderings. Moreover there
exists \(r>0\) such that, for every unitary \(H\) with
\(\|H-H_\star\|_{\mathrm F}<r\) and every
\(v,w\in\mathcal F(H)\),

\[
 \left|\,|v^*w|^2-\frac16\right|
 \ge\frac\delta{72}=\frac{9\sqrt7-21}{1008}>0.
\tag{68.3}
\]

Thus no two such common-flat vectors are mutually unbiased. In
particular no complex Hadamard unitary in this ambient neighborhood
can occur with \(I_6\) in a quartet of mutually unbiased bases.
The neighborhood includes the central point and is not restricted
to the one-parameter family. No numerical value of \(r\) is asserted.

### 68.2 Complete exact central pair comparison

Theorem 66.1 supplies all 42 central rays. Index the canonical
unit-entry representatives by

\[
 c_{2m}=(f_m,if_m),\qquad c_{2m+1}=(f_m,-if_m),
 \qquad f_m=(1,\omega^m,\omega^{2m}),\quad m=0,1,2,
\]

and use \(z_0,\ldots,z_{35}\) from (65.3) for the other rays.
For unit-entry representatives, write \(h=z^*z'\). Normalization
divides \(|h|^2\) by 36; hence mutual unbiasedness corresponds to
\(|h|^2=6\).

Canonical/canonical squared overlaps are 36 on the diagonal and
zero off it. The 38-orbit table in §65.4 gives the complete set of
noncanonical/noncanonical squared overlaps off the diagonal:

\[
 0,18,\frac94,\frac{243}{28},\frac{18}{7},\frac{27}{7},
 \frac{36}{7},\frac{297\pm27\sqrt{21}}{56},
 \frac{81}{7},\frac{99}{14}.
\tag{68.4}
\]

Every distance of a number in (68.4) from six is at least \(6/7\).
For the two radical values this follows from \(\sqrt{21}>4\):

\[
 \frac{27\sqrt{21}-39}{56}>\frac{69}{56}>\frac67,
 \qquad
 \frac{39+27\sqrt{21}}{56}>\frac{147}{56}>\frac67.
\]

Their diagonal overlaps are again 36. Reversing a pair leaves its
squared overlap unchanged.

It remains to compare all \(6\cdot36=216\) mixed pairs. The four
generators of §65.4 act on the canonical indices as

\[
 \begin{aligned}
 R_{(1,0,2)}&=(2\ 4)(3\ 5),& R_{(1,2,0)}&=\mathrm{id},\\
 \Theta&=(0\ 1)(2\ 5)(3\ 4),& X&=(0\ 1)(2\ 3)(4\ 5).
 \end{aligned}
\tag{68.5}
\]

Together with their displayed action on noncanonical indices, they
produce the following ten disjoint orbits. Each table value is a
direct substitution of the exact representatives; orbit sizes sum
to 216, and squared moduli are invariant under every group element.

| \((j,k)\), meaning \((c_j,z_k)\) | Orbit size | \(|c_j^*z_k|^2\) |
|---|---:|---:|
| \((0,0)\) | 12 | \(9-9\sqrt7/7\) |
| \((0,1)\) | 12 | \(9+9\sqrt7/7\) |
| \((0,12)\) | 24 | \(9/2-9\sqrt7/14\) |
| \((0,13)\) | 24 | \(9/2+9\sqrt7/14\) |
| \((2,0)\) | 24 | \(9/2-9\sqrt7/14\) |
| \((2,1)\) | 24 | \(9/2+9\sqrt7/14\) |
| \((2,12)\) | 24 | \(9-9\sqrt7/7\) |
| \((2,13)\) | 24 | \(9+9\sqrt7/7\) |
| \((2,14)\) | 24 | \(9/2+9\sqrt7/14\) |
| \((2,15)\) | 24 | \(9/2-9\sqrt7/14\) |

The respective distances from six of the four mixed values
\(9-9\sqrt7/7\), \(9+9\sqrt7/7\), \(9/2-9\sqrt7/14\), and
\(9/2+9\sqrt7/14\) are

\[
 2\delta,\qquad 2\delta+6,\qquad \delta+3,\qquad\delta.
\tag{68.6}
\]

Since \(0<\delta<1/4<6/7\), the exact minimum over all pair types
is \(\delta\), attained for instance by \((c_0,z_{13})\).
There are 72 attaining mixed pairs with the canonical ray first,
and 144 attaining ordered pairs after reversal. This comparison
covers all \(42^2=1764\) ordered pairs, including all 42 diagonal
pairs. Dividing by 36 proves (68.2).

### 68.3 Compactness in the ambient unitary space

The fixed flat-input torus

\[
 \mathcal T=\{v\in\mathbb C^6:|v_r|^2=1/6\text{ for all }r\}
\]

is compact. If no positive radius made (68.3) true, there would be
unitaries \(H_n\to H_\star\) and vectors
\(v_n,w_n\in\mathcal F(H_n)\) with

\[
 \left|\,|v_n^*w_n|^2-\frac16\right|<\frac\delta{72}.
\]

Pass to convergent subsequences in \(\mathcal T\times\mathcal T\).
Continuity of all output-modulus equations gives
\(v_n\to v\), \(w_n\to w\) with
\(v,w\in\mathcal F(H_\star)\). Continuity of the overlap gives

\[
 \left|\,|v^*w|^2-\frac16\right|\le\frac\delta{72},
\]

contradicting (68.2). This proves the ambient half-gap (68.3).
No finiteness or regularity of nearby ray loci is assumed, and
possible rays approaching canonical points are included.
The argument supplies a positive radius by compactness, not a
numerical matrix-radius estimate from the central overlap gap alone.

### 68.4 Quartet obstruction and coordinate convention

If \(H\) is a complex Hadamard unitary in the neighborhood, a unitary
basis \(B\) is unbiased to \((I_6,H)\) exactly when \(B\) and
\(H^*B\) are flat. Each column \(v=H^*B_j\) therefore belongs to
\(\mathcal F(H)\), with output \(Hv=B_j\).

If two additional bases \(B,C\) formed a quartet with the pair,
choose any columns and set \(v=H^*B_j\), \(w=H^*C_k\). Unitarity
and mutual unbiasedness would give

\[
 |v^*w|^2=|B_j^*C_k|^2=\frac16,
\]

contradicting (68.3). This proves the last assertion of Theorem 68.1.
\(\square\)

The multiple common-unbiased bases at the central point remain:
they are not mutually unbiased to one another. The theorem excludes
quartets containing the specified nearby pair, and does not settle
the general dimension-six fourth-basis problem or every parameter
of the full Hadamard family.
