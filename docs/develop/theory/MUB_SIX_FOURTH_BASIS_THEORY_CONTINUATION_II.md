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
