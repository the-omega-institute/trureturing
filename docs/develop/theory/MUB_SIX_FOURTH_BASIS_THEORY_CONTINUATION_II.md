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

## 69. An effective but extremely small ambient neighborhood

### 69.1 Explicit local consequence

Retain \(H_\star=H_0(0)\) and the normalized common-flat input locus
\(\mathcal F(H)\) from §68. Define

\[
 E=3255\,2^{83},\qquad K=3255\,2^{82}+11,\qquad
 \rho=2^{-K},\qquad\beta=2^{-(K+1)}.
\tag{69.1}
\]

**Theorem 69.1 (effective local exclusion).** If \(H\) is unitary and
\(\|H-H_\star\|_{\mathrm F}\le\rho\), then

\[
 \left|\,|v^*w|^2-\frac16\,\right|>\frac1{360}
 \qquad(v,w\in\mathcal F(H)).
\tag{69.2}
\]

Thus every Hadamard unitary in this closed ball defines a pair
\((I_6,H)\) that cannot belong to a quartet. In the actual family of
§49, the conclusion applies whenever \(|b|\le\beta\), including zero.

This is an effective version of the local exclusion in §68, obtained
using a general polynomial-minimum theorem. The radius is astronomically
small: \(K=15740214171382471854674411531\). It supplies neither useful
numerical coverage nor exclusion on the remaining open branch. This is
an analytic paper proof, not a Lean-kernel verification claim.

### 69.2 A compact integer-polynomial problem

Use 21 real variables
\((x_1,\ldots,x_5,y_1,\ldots,y_5,u_1,\ldots,u_5,v_1,\ldots,v_5,r)\)
and define

\[
 z=(1,x_1+iy_1,\ldots,x_5+iy_5),\qquad
 w=(1,u_1+iv_1,\ldots,u_5+iv_5),
\]

\[
 Q=\left(1+\sum_{j=1}^5(x_ju_j+y_jv_j)\right)^2
  +\left(\sum_{j=1}^5(x_jv_j-y_ju_j)\right)^2-6.
\tag{69.3}
\]

In particular \(Q=|z^*w|^2-6\). Let \(T\subset\mathbb R^{21}\) be
defined by the eleven equalities and three weak inequalities

\[
\begin{aligned}
 x_j^2+y_j^2-1&=0,&u_j^2+v_j^2-1&=0 &&(1\le j\le5),\\
 r^2-3&=0,&r&\ge0,\\
 1-10Q&\ge0,&1+10Q&\ge0.
\end{aligned}
\tag{69.4}
\]

Thus \(r=\sqrt3\) on \(T\); the other algebraic conjugate is excluded.
The set is closed and bounded, hence compact. It is nonempty: choose
\(z=(1,1,1,1,1,1)\),
\(w=(1,1,1,-1,i,(1-2i)/\sqrt5)\), and \(r=\sqrt3\).
Then \(|2+i+(1-2i)/\sqrt5|^2=6\), so \(Q=0\).

Define the following polynomial matrix, with conjugation fixing the
real indeterminate \(r\):

\[
 A_2(r)=2J_3+(-3+ir)I_3,\qquad
 B(r)=\begin{pmatrix}A_2(r)&A_2(r)\\
 \overline{A_2(r)}&-\overline{A_2(r)}\end{pmatrix}.
\tag{69.5}
\]

In particular \(B(\sqrt3)=2\sqrt6H_\star\). Put

\[
 F_{a,j}=\bigl(\Re(B(r)a)_j\bigr)^2+
          \bigl(\Im(B(r)a)_j\bigr)^2-24,
 \qquad G=\sum_{a\in\{z,w\}}\sum_{j=0}^5F_{a,j}^2.
\tag{69.6}
\]

These formulas define integer polynomials in the 21 real variables,
and \(G\ge0\). If \(G=0\) on \(T\), all twelve summands vanish, giving
\(z/\sqrt6,w/\sqrt6\in\mathcal F(H_\star)\). The exact central gap
in §68 instead requires

\[
 |Q|\ge\delta=\frac{9\sqrt7-21}{14}>\frac15>\frac1{10}.
\]

Here \(\delta>1/5\) follows from
\(45^2\cdot7-119^2=14>0\), comparing positive quantities. This
contradicts (69.4). Hence \(G\) has a strictly positive attained minimum
on the entire compact set \(T\).

### 69.3 Degrees, heights, and an effective lower bound

For an integer polynomial \(p\), let \(\|p\|_1\) be the sum of the
absolute values of its coefficients. This norm is submultiplicative
and bounds each coefficient. Each row of (69.5) has four entries
\(\pm2\) and two entries \(\pm(-1\pm ir)\). Each real or imaginary
part of \((B(r)a)_j\) therefore has degree at most two and coefficient
norm at most \(4\cdot2+2(1+1)=12\). Dephasing can only decrease that
bound. Consequently

\[
 \deg F_{a,j}\le4,\quad\|F_{a,j}\|_1\le2\cdot12^2+24=312,
 \qquad\deg G\le8,\quad
 \|G\|_1\le12\cdot312^2=1168128<2^{21}.
\tag{69.7}
\]

The overlap forms in (69.3) have coefficient norms 11 and 10, so
\(\|Q\|_1\le11^2+10^2+6=227\) and
\(\|1\pm10Q\|_1\le2271<2^{21}\). The remaining constraints have
degree at most two and coefficient magnitudes at most three. Thus
simultaneous valid bounds for all constraints and the objective are

\[
 n=21,\qquad m=14,\qquad d=8\text{ (even)},\qquad H=2^{21}.
\tag{69.8}
\]

We use Theorem 1.1 of G. Jeronimo, D. Perrucci, and E. Tsigaridas,
“On the Minimum of a Polynomial Function on a Basic Closed Semialgebraic
Set and Applications,” SIAM J. Optim. 23 (2013), 241–255,
[DOI 10.1137/110857751](https://doi.org/10.1137/110857751),
[primary published text, p. 242](https://ri.conicet.gov.ar/bitstream/handle/11336/14866/CONICET_Digital_Nro.18274.pdf?isAllowed=y&sequence=1).
For a basic closed set in \(\mathbb R^n\), \(n\ge2\), defined by
\(m\) integer polynomials and an integer objective, assume degrees at
most an even \(d\) and coefficient magnitudes at most \(H\). On a
compact connected component, any nonzero objective minimum has absolute
value at least

\[
 \bigl(2^{4-n/2}\widetilde H d^n\bigr)^{-n2^nd^n},
 \qquad\widetilde H=\max\{H,2n+2m\}.
\tag{69.9}
\]

No regularity or genericity is required. Choose a global minimizer of
\(G\) on \(T\) and its connected component. The component is compact,
and its minimum equals the positive global minimum. Thus (69.9)
applies even if \(T\) is disconnected. For (69.8),
\(\widetilde H=2^{21}>70\), and

\[
 2^{4-n/2}\widetilde H d^n=2^{155/2},\qquad
 n2^nd^n=21\,2^{84},\qquad
 G\ge2^{-3255\,2^{83}}=2^{-E}\quad\text{on }T.
\tag{69.10}
\]

This is an application of the cited effective minimum theorem; the
integer encoding and its normalization above are specific to this family.

### 69.4 Conversion from residual to matrix distance

Suppose \(H\) is unitary,
\(\eta=\|H-H_\star\|_{\mathrm F}\le\rho\), and (69.2) fails.
Separately dephase \(v,w\in\mathcal F(H)\) and multiply by \(\sqrt6\)
to obtain unit-entry vectors \(z,w\) with first coordinate one. Then

\[
 |Q|=36\left|\,|v^*w|^2-1/6\,\right|\le1/10,
\]

so these coordinates with \(r=\sqrt3\) belong to \(T\).
Write \(M_\star=\sqrt6H_\star\) and \(M=\sqrt6H\).
For either \(a=z,w\), unitarity and \(\|a\|_2=\sqrt6\) give

\[
 |(M_\star a)_j|\le6,\qquad |(Ma)_j|\le6,\qquad
 |((M_\star-M)a)_j|\le6\|H_\star-H\|_{\mathrm{op}}\le6\eta.
\]

Output flatness gives \(|(Ma)_j|^2=6\). Therefore

\[
 |F_{a,j}|=4\left|\,|(M_\star a)_j|^2-|(Ma)_j|^2\,\right|
 \le4(6+6)6\eta=288\eta,
\]

\[
 G\le12\cdot288^2\eta^2=995328\eta^2
 <2^{20}\rho^2=2^{-E-2}<2^{-E}.
\tag{69.11}
\]

This contradicts (69.10), proving the strict gap (69.2) even on the
closed-radius boundary. If additional bases \(B,C\) formed a quartet
with \(I_6,H\), the input vectors \(H^*B_j,H^*C_k\) would lie in
\(\mathcal F(H)\), while their squared overlap would be \(1/6\).
Unitarity preserves that overlap, contradicting (69.2).

### 69.5 Actual-family parameter interval and scope

For the parameterization in §49, let
\(h=\sqrt{(3-b^2)/(1+b^2)}\), \(a=bh\), and retain its coefficients
\(P=(a-3+i(h+b))/2\), \(Q=(-a-3+i(h-b))/2\).
Only twelve diagonal block entries change with \(b\), so

\[
 \|H_0(b)-H_\star\|_{\mathrm F}^2
 =|P(b)-P(0)|^2+|Q(b)-Q(0)|^2
 =\frac{b^2h^2+(h-\sqrt3)^2+b^2}{2}.
\tag{69.12}
\]

For \(|b|\le1/2\), \(0<h\le\sqrt3\) and

\[
 |h-\sqrt3|=\frac{4b^2}{(1+b^2)(h+\sqrt3)}
 \le\frac{4b^2}{\sqrt3}.
\]

Thus (69.12) is at most
\(2b^2+(8/3)b^4\le(8/3)b^2\le4b^2\). It follows that
\(\|H_0(b)-H_\star\|_{\mathrm F}\le2|b|\).
Since \(\beta=\rho/2<1/2\), every \(|b|\le\beta\) is inside the
certified ambient ball. This establishes effectiveness of the local
exclusion, while the status of the rest of the open branch remains unchanged.

## 70. A certified boundary of the common-flat pair-gap method

### 70.1 An unbiased ray pair on the actual branch

**Theorem 70.1 (a ray-pair transition).** There is an algebraic parameter

\[
 0.105461989024891<b_*<0.105461989224891
 \tag{70.1}
\]

and a reflection-fixed noncanonical unit-entry vector \(w_*\) such that both
\(w_*/\sqrt6\) and a canonical input vector \(k_*/\sqrt6\) are common-flat
for \(H_0(b_*)\), and

\[
 \left|\left\langle w_*/\sqrt6,k_*/\sqrt6\right\rangle\right|^2=1/6.
 \tag{70.2}
\]

Moreover a single continuous reflection-fixed common-flat branch exists over
\([21/200,53/500]=[0.105,0.106]\), contains this isolated algebraic transition,
and has opposite overlap-minus-six signs at its endpoints. Thus a claim of no
mutually-unbiased common-flat ray pair cannot hold on the entire open branch.
This is a boundary of that particular sufficient method for quartet exclusion;
it does not refute a basis-level no-quartet assertion.

### 70.2 Rational coordinates and original equations

Use real coordinates \(X=(T,G,S,c,h)\) and the real parameter \(b\). Set

\[
 \chi(q)={1-q^2+2iq\over1+q^2},\quad
 t=\chi(T),\quad g=\chi(G),\quad s=\chi(S),\quad
 w=(1,1,t,g,g,s).
 \tag{70.3}
\]

All denominators \(1+q^2\) are positive on the real line, and every entry of
\(w\) has modulus one. It is fixed by the synchronous transposition of
coordinates zero and one in each channel. Define

\[
 P=(bh-3+i(h+b))/2,\qquad Q=(-bh-3+i(h-b))/2,
\]

\[
 M=\begin{pmatrix}J_3+PI_3&J_3+QI_3\\
 J_3+\bar QI_3&-J_3-\bar PI_3\end{pmatrix},\qquad
 D=(1+b^2)h^2-3+b^2.
 \tag{70.4}
\]

Direct multiplication gives the exact identities

\[
 M^*M-6I_6={D\over2}I_6,\qquad
 |1+P|^2=|1+Q|^2=1+D/4.
 \tag{70.5}
\]

Thus, when \(D=0\), \(-1<b<1\), and \(h>0\), \(M/\sqrt6\) is exactly
\(H_0(b)\): \(h=\sqrt{(3-b^2)/(1+b^2)}\). It is both unitary and Hadamard.

Write \(S_x=2+t\), \(S_y=2g+s\), and

\[
 U_0=S_x+S_y+P+Qg,\quad U_2=S_x+S_y+Pt+Qs,\quad
 V_0=S_x-S_y+\bar Q-\bar Pg.
\]

Our five rational equations are

\[
 F(X,b)=\bigl(|U_0|^2-6,\ |U_2|^2-6,\ |V_0|^2-6,
               c^2-1-b^2,\ D\bigr)=0.
 \tag{70.6}
\]

The first and second upper outputs are both \(U_0\); the first and second
lower outputs are both \(V_0\). Consequently the first three equations of
(70.6) set five of the six output squared moduli to six. Equation (70.5), \(D=0\),
and \(\|w\|^2=6\) set their total to 36, so the remaining output also has
squared modulus six. This reconstructs all original flatness equations, rather
than only a subset without a converse.

The boxes below have \(c,h>0\), so (70.6) also fixes \(c=\sqrt{1+b^2}\).
Let \(\omega=(-1+i\sqrt3)/2\), \(f=(1,\omega,\omega^2)\), and define

\[
 g_1=(b+i)/c,\qquad k=(f,-g_1f).
 \tag{70.7}
\]

This is a unit-entry canonical common-flat vector. For completeness,
\(J_3f=0\), \(|P|^2+|Q|^2=6+D/2\), and
\(\Re(P\bar Q(b-i))=-bD/4\). Since \(|g_1|=1\), the squared moduli of
the two output channel factors \(P-Qg_1\) and \(\bar Q+\bar Pg_1\) are
respectively \(6+(D/2)(1+b/c)\) and \(6+(D/2)(1-b/c)\), both six at a
solution of (70.6).

The raw overlap with (70.3) is

\[
 k^*w=\omega\bigl[(t-1)-(b-i)(s-g)/c\bigr].
\]

Define the rational numerator

\[
 N(X,b)=|c(t-1)-(b-i)(s-g)|^2-6c^2.
 \tag{70.8}
\]

Then \(|k^*w|^2-6=N/c^2\). Thus \(N=0\) is exactly (70.2); its endpoint
signs are also the signs of the raw overlap-minus-six. Throughout the uniform
box, \(T>0\), so \(t\ne1\). A canonical vector with equal first two upper
coordinates must have Fourier mode zero and all three upper coordinates equal.
Therefore every \(w\) in this branch is noncanonical.

### 70.3 Contraction and same-branch identification

All centers, radii, and preconditioning matrices below are exact rationals.
For a box \(\mathcal X=x_0+[-r_1,r_1]\times\cdots\times[-r_n,r_n]\),
use the weighted norm \(\|u\|_r=\max_i|u_i|/r_i\). For a square system
\(F_b\) and a fixed rational matrix \(Y\), let

\[
 \mathcal T_b(x)=x-YF_b(x),\quad
 E_{ij}\supseteq\delta_{ij}-\sum_kY_{ik}\,\partial_jF_{b,k}(\mathcal X).
\]

Set

\[
 e_i=\sum_j\sup|E_{ij}|r_j,\quad
 d_i\ge|(YF_b(x_0))_i|,\quad
 q=\max_i e_i/r_i,\quad a=\max_i(d_i+e_i)/r_i.
 \tag{70.9}
\]

The bounds \(q<1\) and \(a<1\) make \(\mathcal T_b\) a contraction of
\(\mathcal X\) into its interior. Invertibility of \(Y\) follows from
\(\|I-YJ\|_r<1\) at any point of the box. Its unique fixed point is
therefore the unique zero of \(F_b\) in the box.

For the uniform parameter interval \(B=[b_0-\epsilon,b_0+\epsilon]\),
with \(b_0=211/2000\) and \(\epsilon=1/2000\), derivative intervals in
(70.9) range over \(\mathcal X\times B\). The bound at the center is obtained
by the one-variable mean-value inequality after preconditioning:

\[
 d_i=\sup|(YF(x_0,b_0))_i|
       +\epsilon\sup|(YF_b(x_0,B))_i|.
 \tag{70.10}
\]

This avoids treating different occurrences of the common parameter as unrelated
perturbations. It is an ordinary derivative bound, not a numerical cancellation
assumption. Uniform contraction gives a unique zero \(X(b)\in\mathcal X\)
for every \(b\in B\). It is continuous: the fixed-point difference is bounded
by \((1-q)^{-1}\|\mathcal T_b(X(b'))-\mathcal T_{b'}(X(b'))\|_r\), which
tends to zero as \(b\to b'\).

The following rational upper bounds result from the exact interval evaluations
specified in §70.5. The endpoint and joint boxes have all radii \(10^{-10}\).

| Box | Number of unknowns | Contraction bound \(q\) | Inclusion bound \(a\) |
|---|---:|---:|---:|
| Uniform branch, \(b\in[0.105,0.106]\) | 5 | \(<0.255\) | \(<0.744\) |
| Left endpoint, \(b=0.105\) | 5 | \(<3\cdot10^{-8}\) | \(<9\cdot10^{-6}\) |
| Right endpoint, \(b=0.106\) | 5 | \(<3\cdot10^{-8}\) | \(<5\cdot10^{-6}\) |
| Joint system \((F,N)=0\) | 6 | \(<10^{-7}\) | \(<18\cdot10^{-6}\) |

The endpoint boxes lie strictly inside the uniform five-dimensional box.
Uniqueness therefore identifies their zeros with the endpoint values of the
same branch \(X(b)\). Their exact rational sign enclosures are

\[
 N(X(0.105),0.105)\in[0.001197089,0.001197100],\qquad
 N(X(0.106),0.106)\in[-0.001398270,-0.001398260].
 \tag{70.11}
\]

Continuity already gives a zero of \(N\) on this branch. Independently, the
six-dimensional joint contraction gives a unique zero of \((F,N)\) inside
its much smaller box. Its first five coordinates lie strictly inside the
uniform box, and its parameter interval lies strictly inside \(B\). By
uniqueness of the uniform zero at that parameter, this isolated joint zero
necessarily lies on the same continued branch. Its sixth coordinate gives (70.1).

All rational denominators in (70.6) and (70.8) are nonzero on the real boxes.
Multiplying every equation of the six-dimensional joint system by
\(4(1+T^2)^2(1+G^2)^2(1+S^2)^2\) gives integer polynomials. The contraction
bound implies a nonsingular joint Jacobian at its zero; clearing those nonzero
denominators preserves nonsingularity. Thus it is an isolated complex zero of
a rational polynomial system, and its coordinates are algebraic. Equations
(70.1), (70.3), and the isolating box specify an exact algebraic witness, rather than
only a decimal approximate solution.

### 70.4 Scope and an ambient upper boundary

At \(b_*\), (70.5)–(70.8) prove the full original common-flat equations and the
mutual unbiasedness of the two normalized rays. Applying \(H_0(b_*)\) to
both rays preserves their overlap and gives the corresponding output rays
unbiased to the fixed pair \((I_6,H_0(b_*))\). This does not produce complete
bases containing them with the required pairwise relations.

In particular the universal no-unbiased-ray-pair property of §68 cannot extend
to the entire branch. One can also give a simple upper boundary for that
property in the ambient Frobenius metric. The family identity from §69 gives

\[
 \|H_0(b)-H_\star\|_F^2
 ={b^2h^2+(h-\sqrt3)^2+b^2\over2}.
\]

For \(|b|<1\), \(1<h\le\sqrt3\) and
\(|h-\sqrt3|\le(3/2)b^2\), since \(h+\sqrt3>8/3\). Hence this squared
distance is at most \(2b^2+(9/8)b^4\). The joint box has
\(b_*<211/2000\), and direct rational comparison gives

\[
 2(211/2000)^2+(9/8)(211/2000)^4<9/400.
\]

Thus the open ambient ball of radius \(3/20\) already contains a Hadamard
matrix admitting the unbiased ray pair (70.2). This is an upper bound on a
possible universal pair-gap radius, not on a no-quartet radius.

### 70.5 Exact interval arithmetic

All rational centers, radii, and preconditioners are printed in §70.6.
The bounds in §70.3 can be reproduced by evaluating (70.3), (70.6),
and (70.8), together with their derivatives, using outward interval
arithmetic at precision \(p=160\). The following rules specify one
integer-only evaluation, so no external numerical data are needed.

For completeness, an interval is stored as two integers \([L,U]\) representing
\([L2^{-p},U2^{-p}]\). Addition and negation are exact. Multiplication forms
the four integer products, divides their minimum and maximum by \(2^p\), and
rounds the lower result down and upper result up. Reciprocation, only for
intervals excluding zero, encloses the two endpoint values \(2^{2p}/L\) and
\(2^{2p}/U\) by integer floor and ceiling. Division is multiplication by that
reciprocal. Rational input endpoints are similarly rounded outwards.
Derivatives use the ordinary sum, product, and reciprocal rules with these same
interval operations. Therefore each reported enclosure contains the exact
rational-function value or derivative on the full box.

The strict rational inequalities in (70.9), the signs in (70.11),
and the containment of the smaller boxes in the uniform box follow
from these finite interval operations on the displayed data. The boxes
also have \(c,h,T>0\) and \(-1<b<1\). All bounds in the table and
sign display are outward rational bounds, with terminating decimals
interpreted exactly. The original-equation identities and the continuity
argument above turn these inequalities into the asserted existence and
isolation theorem. No completeness assertion for rays away from zero
or first-transition assertion is used.

### 70.6 Complete rational certificate

In the following display every listed integer is divided by \(10^{15}\).
For each five-dimensional box the coordinate order is \((T,G,S,c,h)\); the
joint box adds \(b\) last. Each matrix is the preconditioner \(Y\), with rows in coordinate order
and columns in the equation order (70.6), followed by (70.8) for the joint system. The uniform
radii are \((1/1000,1/500,1/1000,1/10000,3/10000)\); all other radii are
\(10^{-10}\). The endpoint parameters are exactly 0.105 and 0.106.

#### Uniform branch

```text
center = (529322879299284, -1605655737839222, 1301727298984411, 1005549725274688, 1719293190587559) / 10^15
Y = (
  -74044001425458, 39686004319955, -91711927520803, 0, 138195680616564
  413580454626374, 253403812921686, 248735147031824, 0, -561869295995595
  -1131740770487, 209311966526076, 216342259234050, 0, -197015992650825
  0, 0, 0, 497240452095409, 0
  0, 0, 0, 0, 287615944218974
) / 10^15
```

#### Left endpoint

```text
center = (529120265701108, -1604702305739784, 1301213362340955, 1005497389355139, 1719412952309946) / 10^15
Y = (
  -73969362636663, 39703104392307, -91676292100711, 0, 138159191843137
  413255438382929, 252999304611860, 248326826687288, 0, -561182741782829
  -861441097563, 209201659092948, 216229793634887, 0, -197111220417418
  0, 0, 0, 497266333352360, 0
  0, 0, 0, 0, 287625850385156
) / 10^15
```

#### Right endpoint

```text
center = (529525692514863, -1606608797143242, 1302242764448628, 1005602307077704, 1719172876633730) / 10^15
Y = (
  -74118720964880, 39668808183601, -91747697282248, 0, 138232357512250
  413904717017460, 253808785439379, 249143968948468, 0, -562555463491845
  -1402980885040, 209422330738926, 216454808775754, 0, -196919805733297
  0, 0, 0, 497214451956666, 0
  0, 0, 0, 0, 287605993085056
) / 10^15
```

#### Joint transition

```text
center = (529307469246133, -1605583269271241, 1301688174970133, 1005545737970272, 1719302314481277, 105461989124891) / 10^15
Y = (
  -157842156508316, 9642501601810, -277985385100540, -674288644944426, 369859108470934, -156236367095223
  807679088737143, 394671578888433, 1124747349189986, 3171130365632635, -1651326414314056, 734768250402058
  -213861552165031, 133029688411627, -256560285180258, -1711797308720764, 391101115539714, -396632799207163
  -21680934421846, -7772907917973, -48191608362986, 322796846239391, 59934489229981, -40419994463473
  49611259252648, 17786306732102, 110274139009855, 399173974974323, 150471987981016, 92490793307202
  -206720652473969, -74112146882584, -459491299163216, -1663281799341056, 571455845871278, -385391490325439
) / 10^15
```

## 71. Scope of the external rank and real-entry exclusion arguments

### 71.1 Statements, conventions, and the boundary of this note

Chen--Yu's [Theorem 3, arXiv:1610.04875v3](https://arxiv.org/pdf/1610.04875v3)
states that a quartet containing identity cannot contain another basis of
operator Schmidt rank at most two on \(\mathbb C^2\otimes\mathbb C^3\).
Their Definition 4 uses “MUB trio” for the three Hadamards in addition to
identity. The rank-two part invokes Lemma 13(ii.d), proved in Appendix D.
The 2026 [McNulty--Weigert review, Theorem 7.12](https://arxiv.org/pdf/2410.23997)
repeats that exclusion.

The actual family has exactly this rank and tensor convention, as shown
below. Thus the stated theorem would exclude the whole branch if imported.
However, the following exact examples invalidate two specific intermediate
steps in the inspected proof. A separate example contradicts the
two-representative classification in
[Liang--Chen, arXiv:2504.15576v3, Lemma 1](https://arxiv.org/pdf/2504.15576v3).
The conclusions here concern those intermediate claims. They neither
construct a quartet nor disprove the no-quartet conclusions, which could
have alternative proofs. The local theorems in §§62--69 do not depend on
these external exclusions. No novelty claim about the whole-branch exclusion problem is made.

### 71.2 Exact Schmidt rank of the actual family

Use the ordered tensor basis
\((e_0\otimes f_0,e_0\otimes f_1,e_0\otimes f_2,
e_1\otimes f_0,e_1\otimes f_1,e_1\otimes f_2)\).
For \(-1<b<1\), put

\[
h=\sqrt{\frac{3-b^2}{1+b^2}},\qquad
P=\frac{bh-3+i(h+b)}2,\qquad
Q=\frac{-bh-3+i(h-b)}2.
\tag{71.1}
\]

Writing \(J=J_3\) and \(I=I_3\), the actual unit-entry matrix is

\[
M=\sqrt6H_0(b)=
\begin{pmatrix}J+PI&J+QI\\J+\bar QI&-J-\bar PI\end{pmatrix}
=F_2\otimes J+L\otimes I,
\quad
F_2=\begin{pmatrix}1&1\\1&-1\end{pmatrix},\quad
L=\begin{pmatrix}P&Q\\\bar Q&-\bar P\end{pmatrix}.
\tag{71.2}
\]

Indeed,

\[
\frac12F_2^*L=-\frac32I_2+\frac i2K,\qquad
K=\begin{pmatrix}b&h(1+ib)\\h(1-ib)&-b\end{pmatrix},
\qquad K^2=3I_2.
\tag{71.3}
\]

Since \(h>0\), \(K\) is not scalar; hence \(F_2,L\) are linearly
independent. So are \(J,I\). Therefore \(H_0(b)\) has operator Schmidt
rank exactly two. No change of tensor factorization is used.

Retaining independent real \(b,h\), direct multiplication also gives

\[
D=(1+b^2)h^2+b^2-3,\qquad
M^*M=(6+D/2)I_6,\qquad
|1+P|^2=|1+Q|^2=1+D/4.
\tag{71.4}
\]

These verify the original Hadamard equations at \(D=0\).

### 71.3 A unitary counterexample to the equal-magnitude step

At \(\alpha=\beta=\pi/4\), the Appendix D argument immediately before
(D11) infers \(v_{jk}=\pm i w_{jk}\) from its entrywise conditions.
Consider instead

\[
V=\begin{pmatrix}
1/\sqrt3&1/\sqrt3&1/\sqrt3\\
1/\sqrt2&-1/\sqrt2&0\\
1/\sqrt6&1/\sqrt6&-2/\sqrt6
\end{pmatrix},\qquad
R=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad W=iRV.
\tag{71.5}
\]

Both \(V,W\) are unitary. Their entries are respectively real and
imaginary, and column normalization of \(V\) gives, at every position,

\[
\operatorname{Re}(\bar v_{jk}w_{jk})=0,\qquad
|v_{jk}|^2+|w_{jk}|^2=2/3.
\tag{71.6}
\]

But \(v_{23}=0\), whereas \(w_{23}=-2i/\sqrt6\); thus neither sign
in \(v_{23}=\pm i w_{23}\) is possible. Global unitarity does not
repair the stated inference.

This example gives a genuine six-dimensional flat unitary:

\[
H=\frac12\begin{pmatrix}V+W&V-W\\V-W&V+W\end{pmatrix}
=(F_2/\sqrt2\otimes I)\operatorname{diag}(V,W)
 (F_2/\sqrt2\otimes I).
\tag{71.7}
\]

Unitarity follows from the factorization; (71.6) makes each squared entry
modulus \(1/6\). Linear independence of \(V,W\) gives Schmidt rank two.
This uses precisely \(\alpha=\beta=\pi/4,\gamma=0\) in the source's
normal form. Its auxiliary matrices may have zero entries, but \(H\)
has none. This is a counterexample to an intermediate implication, not
to the claimed quartet exclusion.

### 71.4 Phase normalization and a second flat unitary

For flat three-by-three \(V,W\), write
\(v_{jk}\bar w_{jk}=e^{i\theta_{jk}}/3\). Substituting into Eq. (41)
of the same source yields

\[
\cos(2\alpha)\cos(2\beta)
+\cos\theta_{jk}\sin(2\alpha)\sin(2\beta)=0.
\tag{71.8}
\]

Thus, when the sine factors are nonzero,
\(\cos\theta_{jk}=-\cot(2\alpha)\cot(2\beta)\). The additional
factor \(1/3\) in the arccos expression following (D12) does not arise
from that substitution.

This difference matters for genuine Hadamards. With
\(\omega=(-1+i\sqrt3)/2\), set

\[
V=\frac{J+(\omega-1)I}{\sqrt3},\qquad
W=\frac{\omega[J+(\bar\omega-1)I]}{\sqrt3},\qquad
c^2=\frac{1+1/\sqrt3}{2},\quad s^2=\frac{1-1/\sqrt3}{2},
\quad cs=1/\sqrt6.
\tag{71.9}
\]

Both \(V,W\) are flat unitaries. Their relative phases
\(3v_{jk}\bar w_{jk}\) equal \(\omega\) on the diagonal and
\(\bar\omega\) off it, so every real part of \(v_{jk}\bar w_{jk}\)
is \(-1/6\). Dephasing gives opposite Fourier orientations for \(V,W\),
as required in the corresponding case of the source argument.

Choose \(\alpha=\beta\in(0,\pi/4)\) with
\(\cos(2\alpha)=1/\sqrt3\), so \(c=\cos\alpha,s=\sin\alpha\).
Then

\[
G=\begin{pmatrix}
c^2V+s^2W&cs(V-W)\\cs(V-W)&s^2V+c^2W
\end{pmatrix}
\tag{71.10}
\]

is the source normal form with \(\gamma=0\), hence unitary. Directly,

\[
|c^2v+s^2w|^2=\frac{1-2/6}{3}-\frac1{18}=\frac16,
\qquad
|cs(v-w)|^2=\frac16\left(\frac23+\frac13\right)=\frac16.
\tag{71.11}
\]

The other two blocks have the same modulus. Thus \(G\) is a rank-two
CHM with \(\cot(2\alpha)\cot(2\beta)=1/2\) and all relative phase
cosines \(-1/2\), rather than \(-1/6\). Also \(2\alpha>\pi/4\).
The corrected relation therefore permits the \(2\pi/3\) phase spacing
discarded by the printed final angle argument. Again, no quartet follows.

### 71.5 The 24-real-entry interior matrix and its invariant

The inspected Reply's Lemma 1, printed p. 2, assumes only an order-six
CHM with more than 22 real entries and concludes equivalence to one of
its two displayed matrices. The first has fourth-root entries and the
second sixth-root entries. There is no printed quartet or all-real-row
hypothesis in that lemma.

At the actual interior parameter \(b=1/2\), put

\[
u=\frac{\sqrt{55}-10+i(2\sqrt{55}+5)}{20},\qquad
v=\frac{-\sqrt{55}-10+i(2\sqrt{55}-5)}{20}.
\tag{71.12}
\]

The unit-entry matrix is

\[
M=\begin{pmatrix}
u&1&1&v&1&1\\1&u&1&1&v&1\\1&1&u&1&1&v\\
\bar v&1&1&-\bar u&-1&-1\\
1&\bar v&1&-1&-\bar u&-1\\
1&1&\bar v&-1&-1&-\bar u
\end{pmatrix}.
\tag{71.13}
\]

Equation (71.4), with \(h=\sqrt{55}/5\), proves \(M^*M=6I\)
and unit entry moduli. Precisely 24 entries are real. The other twelve
have nonzero imaginary parts because \(2\sqrt{55}-5>0\).

For a unit-entry matrix \(A\), its Haagerup cross-ratio set is

\[
\Lambda(A)=\{a_{ij}a_{k\ell}\bar a_{i\ell}\bar a_{kj}:
             i,j,k,\ell\in\{1,\ldots,6\}\}.
\tag{71.14}
\]

Row and column phases cancel, and permutations merely relabel this set.
It is therefore invariant under monomial equivalence, which is broader
than permutation equivalence. Transpose preserves it and conjugation
conjugates it. Fourth-root matrices have cross-ratio real parts in
\(\{-1,0,1\}\); sixth-root matrices have them in
\(\{-1,-1/2,1/2,1\}\).

Rows 1,2 and columns 1,2 of (71.13) give \(u^2\in\Lambda(M)\), with

\[
\operatorname{Re}(u^2)
=2\left(\frac{\sqrt{55}-10}{20}\right)^2-1
=-\frac9{40}-\frac{\sqrt{55}}{10}.
\tag{71.15}
\]

This is irrational. Consequently \(M\) is not monomial equivalent to
either representative, even allowing transpose or conjugation. It is an
exact counterexample to that two-representative classification as printed.
It does not contradict exclusion of the two representatives themselves.

### 71.6 Consequence for the scope of the present results

The [2025 McNulty--Weigert Comment](https://arxiv.org/pdf/2504.13067)
addresses a different step, Lemma 11(v), Part 6, concerning real submatrices.
The explicit examples above identify separate boundaries in the inspected
rank-two and real-entry arguments. They do not establish that those
no-quartet statements are false, that no repair exists, or that all relevant
literature has been exhausted.

Accordingly, the reported global exclusions are not imported here as
certificates for the whole actual branch. The exact central census and
the local basis and ambient no-quartet theorems retain their independent
proofs. The ray pair in §70 limits a sufficient pair-gap method and does
not provide two additional mutually unbiased bases.

## 72. The actual branch in a controlled Fourier normal form

### 72.1 Exact factorization and scope

The corrected cosine relation in §71.4 is attained by the actual curve,
not only by the isolated example there. The following product-monomial
factorization gives a legitimate reduction of the fixed-pair problem.
It does not use the rank-two no-quartet assertion discussed in §71.

Use the ordered \(\mathbb C^2\otimes\mathbb C^3\) convention of §71.2.
For the moment allow \(-1\le b\le1\), with the two endpoints understood
only as algebraic limits of the actual open branch. Set

\[
 c=\sqrt{1+b^2},\qquad h=\sqrt{\frac{3-b^2}{1+b^2}},\qquad
 \omega=\frac{-1+i\sqrt3}{2},
\]

\[
 F_2=\begin{pmatrix}1&1\\1&-1\end{pmatrix},\quad
 K=\begin{pmatrix}b&h(1+ib)\\h(1-ib)&-b\end{pmatrix},\quad
 V_0=\frac{J_3+(\omega-1)I_3}{\sqrt3},\quad
 W_0=\frac{J_3+(\bar\omega-1)I_3}{\sqrt3}.
 \tag{72.1}
\]

Both \(V_0,W_0\) are flat unitaries. Define positive \(p,q\) and the
unit-modulus number \(z\) by

\[
 p=\sqrt{\frac{1+b/\sqrt3}{2}},\quad
 q=\sqrt{\frac{1-b/\sqrt3}{2}},\quad z=\frac{1-ib}{c},\qquad
 R_\beta=\begin{pmatrix}p&q\\q&-p\end{pmatrix},\qquad
 U=\operatorname{diag}(1,z)R_\beta.
 \tag{72.2}
\]

The identity \(pq=hc/(2\sqrt3)\) gives, by direct multiplication,
\(K=U\operatorname{diag}(\sqrt3,-\sqrt3)U^*\). Therefore the tensor
identity in §71.2 yields

\[
 H_0(b)=(A\otimes I_3)\operatorname{diag}(V_0,W_0)
       (R_\beta\operatorname{diag}(1,\bar z)\otimes I_3),
 \qquad A=F_2U/\sqrt2.
 \tag{72.3}
\]

Indeed the two controlled eigenblocks before multiplication by
\(F_2/\sqrt2\) are
\((J_3+(-3/2\pm i\sqrt3/2)I_3)/\sqrt3=V_0,W_0\).
Equation (72.3) holds on the whole closed algebraic interval, including zero.

### 72.2 Product-monomial normalization for positive parameters

For \(0<b\le1\), define \(0<\alpha,\beta<\pi/4\) by

\[
 C=\cos\alpha=\sqrt{\frac{1+h/\sqrt3}{2}},\qquad
 S=\sin\alpha=\sqrt{\frac{1-h/\sqrt3}{2}},\qquad
 \cos\beta=p,\quad\sin\beta=q.
 \tag{72.4}
\]

Then

\[
 CS=\frac{b}{\sqrt3c},\qquad
 \cos2\alpha=\frac h{\sqrt3},\qquad
 \cos2\beta=\frac b{\sqrt3},\qquad
 \boxed{\cot2\alpha\cot2\beta=\frac12}.
 \tag{72.5}
\]

For the last equality, square the positive quantities and use
\((3-h^2)(3-b^2)=4h^2b^2\). In particular \(\alpha+\beta>\pi/4\),
since
\(\cos(2\alpha+2\beta)=\sin2\alpha\sin2\beta(1/2-1)<0\).

Write

\[
 A=\begin{pmatrix}a&d\\e&f\end{pmatrix}
 =\frac1{\sqrt2}
   \begin{pmatrix}p+zq&q-zp\\p-zq&q+zp\end{pmatrix},
\]

and put

\[
 \xi=\frac{p+zq}{\sqrt2C},\qquad
 \delta=\frac{c(1+ih)}2,\qquad
 D=\operatorname{diag}(1,\delta),\qquad
 R_\alpha=\begin{pmatrix}C&S\\S&-C\end{pmatrix}.
 \tag{72.6}
\]

Both \(\xi\) and \(\delta\) have modulus one. The following identities
specify the phases without an implicit choice of square root:

\[
 |a|^2=C^2,\quad |d|^2=|e|^2=S^2,\qquad
 a\bar d=\frac{b\omega^2}{\sqrt3c}=CS\omega^2,\qquad
 e\bar a=\frac{b(1+ih)}{2\sqrt3}=CS\delta.
 \tag{72.7}
\]

They follow by expanding the entries above and using
\(p^2-q^2=b/\sqrt3\), \(pq=hc/(2\sqrt3)\), and
\(h^2=(3-b^2)/(1+b^2)\). Thus
\(a=\xi C\), \(d=\xi\omega S\), and \(e=\xi\delta S\).
Unitarity of \(A\), with \(S>0\), gives
\(f=-\xi\delta\omega C\). Consequently

\[
 A=\xi D R_\alpha\operatorname{diag}(1,\omega).
 \tag{72.8}
\]

Define

\[
 \mathcal H(\alpha,\beta)
 =(R_\alpha\otimes I_3)\operatorname{diag}(V_0,\omega W_0)
  (R_\beta\otimes I_3).
 \tag{72.9}
\]

Substitution in (72.3) proves

\[
 \boxed{H_0(b)=\xi(D\otimes I_3)\mathcal H(\alpha,\beta)
                 (\operatorname{diag}(1,\bar z)\otimes I_3).}
 \tag{72.10}
\]

The scalar and both outer factors are unitary monomial matrices. Hence
\(\mathcal H\) is a genuine complex Hadamard matrix, and (72.10) is a
permitted equivalence of the fixed-pair problem. In particular it is stronger
than merely expressing the two matrices as equivalent under arbitrary local
unitaries, which would not suffice for that purpose.

### 72.3 The corrected phase condition on the actual curve

For \(V=V_0\) and \(W=\omega W_0\), direct entrywise multiplication gives

\[
 3v_{jk}\bar w_{jk}=
 \begin{cases}\omega,&j=k,\\\bar\omega,&j\ne k.\end{cases}
 \tag{72.11}
\]

Thus every relative phase in (72.11) has cosine \(-1/2\), exactly as
required by the corrected equation
\(\cos\varphi=-\cot2\alpha\cot2\beta\) from §71.4.
The expression with an additional factor \(1/3\) does not hold.
Dephasing \(V\) and \(W\) gives the two opposite order-three Fourier
orientations, as in the example in §71.4.

In [Chen--Yu, arXiv:1610.04875v3](https://arxiv.org/pdf/1610.04875v3),
Lemma 13(ii), this matrix is the displayed normal form
\(H_2(\alpha,\beta,0,V_0,\omega W_0)\). This identifies the actual
curve within that formula; it does not import the subsequent exclusion claim.

### 72.4 Zero, negative parameters, and endpoint limits

The expressions (72.2), (72.4), and (72.6) contain no division by \(b\) or
\(S\). At zero they give

\[
 h=\sqrt3,\quad c=1,\quad p=q=1/\sqrt2,\quad z=1,\quad
 \alpha=0,\quad\beta=\pi/4,\quad\xi=1,\quad\delta=-\omega^2.
 \tag{72.12}
\]

Here \(A=I_2\), and (72.8) follows directly from
\(\operatorname{diag}(1,-\omega^2)\operatorname{diag}(1,-1)
\operatorname{diag}(1,\omega)=I_2\). Therefore (72.10) also holds at zero.
No cotangent product is asserted at zero, where one factor is undefined;
the undivided flatness relation is instead identically zero.

For a negative parameter write \(b=-t\), \(t>0\), and set

\[
 Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
 X=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

Interchanging \(P(t)\) and \(Q(t)\) in the original matrix gives

\[
 H_0(-t)=(Z\otimes I_3)H_0(t)(X\otimes I_3)
 =\xi(t)(ZD(t)\otimes I_3)\mathcal H(\alpha(t),\beta(t))
   (\operatorname{diag}(1,\bar z(t))X\otimes I_3).
 \tag{72.13}
\]

This supplies explicit outer product-monomial factors while keeping the
normal-form angles in the stated positive range. It avoids silently moving
\(\beta\) outside the source convention.

At \(b=1\), one has \(h=1\) and \(\alpha=\beta\), with
\(\cos2\alpha=1/\sqrt3\). Equation (72.9) is then exactly the
phase-normalization example of §71.4. All displayed denominators remain
nonzero; the negative endpoint follows from (72.13). These endpoint identities
are algebraic limits and do not enlarge the actual open parameter branch.
The factorization proves neither an exhaustive classification of rank-two
Hadamard matrices nor a whole-branch no-quartet theorem.

## 73. Complete reduction of the nondegenerate opposite-Fourier stratum

### 73.1 Controlled-form hypothesis and conclusion

**Theorem 73.1.** Let

\[
 R_\theta=\begin{pmatrix}\cos\theta&\sin\theta\\
 \sin\theta&-\cos\theta\end{pmatrix},\qquad
 H=(R_\alpha\otimes I_3)\operatorname{diag}(V,W)(R_\beta\otimes I_3),
 \tag{73.1}
\]

where \(V,W\) are order-three unitaries,
\(0<\alpha,\beta\le\pi/4\), and
\((\alpha,\beta)\ne(\pi/4,\pi/4)\). Suppose \(H\) is complex Hadamard
and the two controlled blocks have opposite dephased Fourier orientations
in the same row and column order. Their flatness follows in the proof, so
this last condition is well defined without a separate flatness assumption.

Then \(H\) reduces to \(H_0(b)\) for some \(0<b\le1\), using unitary
monomial factors, complex conjugation, and optionally transpose. More precisely,

\[
 \cot2\alpha\cot2\beta=\frac12,
 \tag{73.2}
\]

both angles are strictly below \(\pi/4\), and after optional exchange of
angles one has \(\alpha\le\beta\) and \(b=\sqrt3\cos2\beta\).
The value \(b=1\) is an algebraic endpoint; it is retained in the theorem
rather than silently included in the actual open branch.

This is a reduction of the explicitly assumed controlled stratum.
The source formula \(H_2(\alpha,\beta,\gamma,V,W)\) in
[Chen--Yu, arXiv:1610.04875v3, equation (39)](https://arxiv.org/pdf/1610.04875v3)
has an additional left factor \(\operatorname{diag}(1,e^{i\gamma})\otimes I_3\),
which is monomial and can first be removed. No assertion that every rank-two
Hadamard has the form (73.1), and no rank-two no-quartet theorem, is imported.

### 73.2 Original flatness and the forced phase angle

For one entry pair \(v=v_{jk},w=w_{jk}\), the corresponding four entries
of (73.1), writing \(c_\alpha=\cos\alpha\) and \(s_\alpha=\sin\alpha\), are

\[
 c_\alpha c_\beta v+s_\alpha s_\beta w,\quad
 c_\alpha s_\beta v-s_\alpha c_\beta w,\quad
 s_\alpha c_\beta v-c_\alpha s_\beta w,\quad
 s_\alpha s_\beta v+c_\alpha c_\beta w.
 \tag{73.3}
\]

Their four squared moduli equal \(1/6\). Summing in pairs gives

\[
 |v|^2+|w|^2=2/3,\qquad
 \cos2\alpha(|v|^2-|w|^2)=\cos2\beta(|v|^2-|w|^2)=0.
 \tag{73.4}
\]

At least one cosine is nonzero, so every \(|v|=|w|=1/\sqrt3\).
Thus \(V,W\) are indeed Hadamard. Substitution in the first squared
modulus in (73.3) yields

\[
 \cos2\alpha\cos2\beta+
 3\operatorname{Re}(v\bar w)\sin2\alpha\sin2\beta=0.
 \tag{73.5}
\]

For \(r=w/v\) this says \(\operatorname{Re}r=-\tau\), where
\(\tau=\cot2\alpha\cot2\beta\ge0\). Since \(|r|=1\), one has
\(\tau\le1\). Put \(\theta=\arccos(-\tau)\in[\pi/2,\pi]\).
Every ratio \(r\) lies in \(\{e^{i\theta},e^{-i\theta}\}\).

Use indices \(j,k\in\{0,1,2\}\) and \(F_{jk}=\omega^{jk}/\sqrt3\).
For a three-dimensional Hadamard with unit-entry rescaling \(a_{jk}\),
the factors

\[
 L_0=\operatorname{diag}(\bar a_{j0}),\qquad
 R_0=\operatorname{diag}(a_{00}\bar a_{0k})
 \tag{73.6}
\]

dephase its first row and column to \(1/\sqrt3\). The other two entries
of its second row are \(\omega/\sqrt3,\omega^2/\sqrt3\) in one order:
three unit phases with sum zero form an equilateral triangle. Orthogonality
fixes the third row. Thus its dephased form is \(F\) or \(\bar F\),
without permutations. Apply the same factors (73.6) to both controlled blocks;
this is a permitted monomial operation on (73.1). If necessary conjugate the
whole matrix so that the first block is \(F\).

The opposite-orientation hypothesis now gives

\[
 W=\operatorname{diag}(\gamma_0,\gamma_1,\gamma_2)
       \bar F\operatorname{diag}(\delta_0,\delta_1,\delta_2),
 \qquad\delta_0=1,\qquad
 r_{jk}=\gamma_j\delta_k\omega^{jk}.
 \tag{73.7}
\]

The phases \(\gamma_j=r_{j0}\) take only two possible values, so two
are equal. For those distinct rows \(j,l\),
\(r_{j1}/r_{l1}=\omega^{j-l}\) is a nontrivial cube root. On the other
hand this ratio must be \(e^{2i\theta}\) or \(e^{-2i\theta}\).
The only possibility with \(\theta\in[\pi/2,\pi]\) is
\(\theta=2\pi/3\). This proves (73.2) and
\(r_{jk}\in\{\omega,\omega^2\}\). It also excludes zero cotangent
product, forcing both angles below \(\pi/4\).

### 73.3 Six patterns and all simultaneous transports

Write \(\gamma_j=\omega^{a_j}\), \(\delta_k=\omega^{c_k}\).
The first column and then the first row of (73.7) show that these are
cube roots, with \(a_j\in\{1,2\}\) and \(c_0=0\). The ratio exponent
matrix therefore satisfies, modulo three,

\[
 A_{jk}=a_j+c_k+jk\in\{1,2\}.
 \tag{73.8}
\]

The complete list is as follows; each three-digit string denotes one row.

| \(a\) | \((c_0,c_1,c_2)\) | Rows of \(A\) | \(\epsilon\) | \(d\) |
|---|---|---|---:|---:|
| \((1,1,2)\) | \((0,0,1)\) | 112 / 121 / 211 | 1 | 2 |
| \((1,2,1)\) | \((0,1,0)\) | 121 / 211 / 112 | 1 | 1 |
| \((1,2,2)\) | \((0,1,1)\) | 122 / 212 / 221 | -1 | 0 |
| \((2,1,1)\) | \((0,2,2)\) | 211 / 112 / 121 | 1 | 0 |
| \((2,1,2)\) | \((0,0,2)\) | 221 / 122 / 212 | -1 | 2 |
| \((2,2,1)\) | \((0,2,0)\) | 212 / 221 / 122 | -1 | 1 |

This is an exhaustive \(2^3\cdot3^2\) check of (73.8). An elementary
structural verification is also available. Any two rows agree once and
differ twice, and so do any two columns. A uniform row would force the other
two rows to differ from it twice and from each other twice, leaving two
columns differing in only one position. Thus no row is uniform. Nonuniform
binary rows of different weights cannot differ in exactly two positions;
hence all rows have the same weight. Their exceptional entries occupy a
permutation of the columns. Substitution in (73.8) gives exactly the table,
equivalently

\[
 A_{jk}=\begin{cases}-\epsilon,&k=-\epsilon j+d,\\
 \epsilon,&k\ne-\epsilon j+d,\end{cases}
 \qquad\epsilon\in\{1,-1\},\quad d\in\{0,1,2\}.
 \tag{73.9}
\]

Define \(\sigma(k)=-\epsilon k+d\) modulo three and let
\(\Pi_\sigma\) have column \(k\) equal to \(e_{\sigma(k)}\).
Put

\[
 \ell_j=\epsilon\mathbf1_{j=0}-jd,\quad
 r_0=0,\quad r_1=r_2=-\epsilon,\qquad
 L=\operatorname{diag}(\omega^{\ell_j}),\quad
 R=\operatorname{diag}(\omega^{r_k}).
 \tag{73.10}
\]

For every row of the table, direct exponent arithmetic proves

\[
 LF\Pi_\sigma R=V_\epsilon
 :=\frac{J_3+(\omega^\epsilon-1)I_3}{\sqrt3},\qquad
 LW\Pi_\sigma R=W_\epsilon:=\omega^\epsilon V_{-\epsilon}.
 \tag{73.11}
\]

Indeed the first block has exponents
\(\ell_j+j\sigma(k)+r_k=\epsilon\mathbf1_{j=k}\).
After the column permutation, the ratio exponents are \(-\epsilon\)
on the diagonal and \(\epsilon\) off it. Adding them gives the second
block's exponents, zero on its diagonal and \(\epsilon\) off it.
This verifies the actual matrices and every phase factor.

The factors \(I_2\otimes L\) and \(I_2\otimes(\Pi_\sigma R)\)
commute with the qubit reflections, so (73.11) acts simultaneously on the
controlled pair. For \(\epsilon=1\) the result is exactly
\((V_0,\omega W_0)\) from §72; for \(\epsilon=-1\) it is its complex
conjugate. Conjugating the latter whole matrix gives the former because
both qubit reflections are real.

### 73.4 Parameter coverage and fixed-pair transport

The two blocks in §72 are symmetric, and therefore

\[
 \mathcal H(\alpha,\beta)^T=\mathcal H(\beta,\alpha).
 \tag{73.12}
\]

After optional transpose take \(\alpha\le\beta\), and set
\(b=\sqrt3\cos2\beta>0\), \(h=\sqrt3\cos2\alpha\ge b\).
Equation (73.2) gives

\[
 (3-h^2)(3-b^2)=4h^2b^2,\qquad
 h^2=\frac{3-b^2}{1+b^2}.
 \tag{73.13}
\]

Since \(h\ge b\), one has \((b^2-1)(b^2+3)\le0\), hence
\(0<b\le1\). Conversely every such \(b\) gives exactly the positive
angles of §72, with \(\alpha\le\beta\) and cotangent product \(1/2\).
The explicit product-monomial identity (72.10) completes the reduction.

Transpose preserves the fixed-pair problem even though it need not be a
monomial equivalence. If \(w,Hw\) are both normalized flat vectors, then
\(v=\overline{Hw}\) is flat and \(H^Tv=\bar w\) is flat. This
antiunitary bijection preserves absolute inner products and orthogonality
of collections. Equivalently, conjugate a collection of bases and multiply
all of them by \(H^T\); this exchanges the fixed pair for \((H^T,I)\).
The permitted operations therefore preserve quartet existence, without
asserting that any quartet exists.

### 73.5 Obligations outside this reduction

The balanced case \(\alpha=\beta=\pi/4\) is excluded: (73.4) then
allows nonflat controlled blocks. If one angle is zero, flatness forces
the other to be \(\pi/4\); the undivided phase equation imposes no
six-pattern restriction. Those zero-angle strata are not identified with
only the single central matrix \(H_0(0)\). Same dephased Fourier
orientations are also outside the theorem. The endpoint \(b=1\) remains
an explicit obligation when applying the reduction to the actual open curve.

Thus the theorem gives complete coverage of the stated positive-angle,
non-balanced opposite-orientation controlled stratum. It supplies neither
universal rank-two coverage nor a no-quartet proof. The unrestricted
noncanonical orthogonal-triple problem on the rest of the actual open
branch remains separate.

## 74. Reflection-edge rigidity at the two half parameters

This section gives an exact finite-parameter obstruction inside the actual
family. It classifies reflection-generated orthogonal pairs, with no
restriction on the candidate ray. Its graph consequence concerns one
symmetry-orbit union at a time.

### 74.1. Statement in the original input convention

Write
\[
 h=\sqrt{\frac{3-b^2}{1+b^2}},\qquad
 P=\frac{bh-3+i(h+b)}2,\qquad Q=\frac{-bh-3+i(h-b)}2,
\]
\[
 H_0(b)=\frac1{\sqrt6}
 \begin{pmatrix}J_3+PI_3&J_3+QI_3\\
 J_3+\bar QI_3&-J_3-\bar PI_3\end{pmatrix}.                 \tag{74.1}
\]
Let \(R\) exchange coordinates 0 and 1 synchronously in the two channels,
and let \(\Theta(x,y)=(-\bar y,\bar x)\).

**Theorem 74.1 (half-parameter reflection-edge classification).**
For \(b=1/2\) or \(b=-1/2\), suppose \(w=(x,y)\) and \(H_0(b)w\)
have all six coordinates of modulus one, and \(w^*Rw=0\).
Then the projective ray of \(w\) is one of exactly four rays
\[
 \left(f_m,\ \varepsilon\frac{b+i}{\sqrt{1+b^2}}f_m\right),
 \quad m\in\{1,2\},\quad\varepsilon\in\{-1,1\},
 \qquad f_m=(1,\omega^m,\omega^{2m}),\quad
 \omega=\frac{-1+i\sqrt3}{2}.                              \tag{74.2}
\]
The same statement holds for either other synchronous transposition.
Here \(w/\sqrt6\) is the normalized input vector; (74.1) acts on that
input, so no input/output basis identification is implicit.

The proof below prints the original reduction, every exceptional chart,
and two finite rational ideal certificates. They use elementary polynomial
operations only. No ray census or external no-quartet theorem is assumed.

### 74.2. A quaternionic reduction retaining individual flatness

Use the quaternion realization
\[
 (\Re z,\Im z,\Re t,\Im t)
 \longleftrightarrow
 \begin{pmatrix}z&t\\-\bar t&\bar z\end{pmatrix}.
\]
Quaternion conjugation is denoted by \(*\). Pure quaternions are vectors in
\(\mathbb R^3\), with \(uv=-u\cdot v+u\times v\); put \(e=(1,0,0)\).
The channel pair \((x_j,y_j)\) is the first column of the quaternion
\(W_j=T(x_j,-\bar y_j)\). Its squared norm is
\(|x_j|^2+|y_j|^2\), and the \(e\)-component of \(W_jeW_j^*\)
is \(|x_j|^2-|y_j|^2\).

In interleaved channel order, \(iH_0\) is a quaternionic unitary matrix
with off-diagonal entry \(A=A_0/\sqrt6\) and diagonal entry \(D=D_0/\sqrt6\),
where
\[
 A_0=(0,1,0,1),\qquad
 D_0=\left(-\frac{h+b}{2},\frac{bh-1}{2},
              -\frac{h-b}{2},\frac{-bh-1}{2}\right).
\]
Put \(B=D-A\). Direct multiplication, using
\((1+b^2)h^2=3-b^2\), gives
\[
 |A|^2=|D|^2=\frac13,\quad |B|^2=1,\quad
 D_0^*A_0=-1+\boldsymbol K,\qquad
 \boldsymbol K=(-b,bh,-h),\quad|\boldsymbol K|^2=3.           \tag{74.3}
\]
These identities also verify unitarity of (74.1).

The four normalized columns associated with
\(w,Rw,\Theta w,R\Theta w\) are mutually orthogonal: \(R\) is real
symmetric, commutes with \(\Theta\), and \(\Theta^2=-I\).
They form a quaternionic two-plane containing the \(R\)-odd line.
Its complementary quaternionic line is \(R\)-even. Its complex
projector has diagonal \(1/3\), since the four flat columns contribute
\(2/3\). Thus its unit vector has the unique right normalization
\[
 C_{\mathcal Q}=\frac{(1,1,\mathcal Q)}{\sqrt3},
 \qquad |\mathcal Q|=1.
\]
An orthonormal quaternionic basis of its complement is
\[
 E_{\mathcal Q}=\frac{(1,1,-2\mathcal Q)}{\sqrt6},\qquad
 O_0=\frac{(1,-1,0)}{\sqrt2}.
\]
Output flatness of the four columns gives the same complementary
projector diagonal. Since the first two output coefficients agree,
unitarity shows this is equivalent to
\[
 |2A+D\mathcal Q|^2=1,
 \qquad\langle-1+\boldsymbol K,\mathcal Q\rangle=-1.        \tag{74.4}
\]
The bracket is the Euclidean quaternion inner product.
Set
\[
 L=A+D-2A\mathcal Q,\quad T_0=D\mathcal Q-A,\quad F=L^*B.
\]
Then \(|L|=|T_0|=1\), and the images of the displayed basis are
\((L,L,-2T_0)/\sqrt6\) and \((B,-B,0)/\sqrt2\). Moreover,
\[
 F=1+\frac{(1-\mathcal Q^*)(-3-\boldsymbol K)}3,
 \qquad \mathcal Q=\frac{(3+\boldsymbol K)(3F^*-\boldsymbol K)}{12}.
                                                                    \tag{74.5}
\]
The complement conditions are exactly
\[
 |F|=1,\qquad \Im(F)\cdot\boldsymbol K=0.                   \tag{74.6}
\]
For example,
\[
 |\mathcal Q|^2-1=\tfrac34(|F|^2-1)
                   +\tfrac12\Im(F)\cdot\boldsymbol K,
\]
\[
 |F|^2-1=\tfrac43(|\mathcal Q|^2-1)
          +\tfrac23(\langle-1+\boldsymbol K,\mathcal Q\rangle+1).
\]
No parameter-dependent denominator is used here.

Reflection orthogonality and equal input channel-pair norms give
\[
 W_0=\frac{(1+\sqrt3 V)\eta}{\sqrt2},\quad
 W_1=\frac{(1-\sqrt3 V)\eta}{\sqrt2},\quad
 W_2=-\sqrt2\mathcal Q\eta,                                \tag{74.7}
\]
where \(\eta\) is unit, \(V\) is pure unit, \(v=\Im V\), and
\(n=\eta e\eta^*\) is unit. The output pair norms equal two precisely
when \(\Im(F)\cdot v=0\). The six individual input/output imbalances
are exactly
\[
 n\cdot(e\times v)=0,\quad
 n\cdot(3(e\cdot v)v-e)=0,\quad
 n\cdot\mathcal Q^*e\mathcal Q=0,                           \tag{74.8}
\]
\[
 n\cdot(\mathbf h\times v-h_0v)=0,\quad
 n\cdot(e_L-3e_B+6(e_B\cdot v)v)=0,\quad
 n\cdot T_0^*eT_0=0,                                     \tag{74.9}
\]
where \(e_B=B^*eB\), \(e_L=L^*eL\), and
\(B^*eL=h_0+\mathbf h\). These follow by expanding (74.7) and
its output, obtained by replacing \(1,V,\mathcal Q\) with
\(L,BV,T_0\). Conversely, choose any lift \(\eta e\eta^*=n\)
and use (74.7). The pair norms and (74.8)–(74.9) give all twelve
original unit moduli and reflection orthogonality. The lifts differ
only by a right unit complex scalar, which is the common projective
phase. Thus the projector condition has not replaced individual flatness.

Writing \(c=e\cdot v\), when \(|c|<1\) the first two input equations give
\[
 N(v)=(1-3c^2)v+2ce,\qquad
 n=\frac{\pm N(v)}{\sqrt{(1-c^2)(1+3c^2)}}.                \tag{74.10}
\]
At \(v=\pm e\), instead they give \(n\cdot e=0\). This exceptional
circle will be handled without (74.10).

### 74.3. Real poles, axis, and parallel exceptions

If \(F\) is real, \(F=\pm1\) and \(L=\pm B\).
The first two input and output equations become
\[
 n\cdot(e\times v)=n\cdot(e_B\times v)=0,\quad
 n\cdot(3(e\cdot v)v-e)=n\cdot(3(e_B\cdot v)v-e_B)=0.
\]
The axes are independent, since \(e\cdot e_B=-bh/3\) and
\(|bh|\le1\). These equations force
\(v\perp e,e_B\) and \(n=\pm v\). Indeed, outside the axes' plane
the first two equations force \(n\parallel v\), and the last two
then give the perpendicularities. Inside that plane they force \(n\)
inside it and \(n-3(n\cdot v)v=0\), contradicting \(|n|=1\).

For \(F=1\), (74.5) gives \(\mathcal Q=1\) and \(T_0=B\).
Since \(V\eta=\pm\eta e\), (74.7) gives the two nonzero Fourier
patterns \((f_m,gf_m)\). Original flatness requires
\(\Re(P\bar Q\bar g)=0\); the identity
\[
 P\bar Q=\frac{(b^2+3)(1-ib)}{1+b^2}
\]
gives exactly (74.2). For \(F=-1\),
\(\mathcal Q=(-1-\boldsymbol K)/2\), whereas
\[
 (e\times e_B)\cdot\mathcal Q^*e\mathcal Q
       =-\frac{h(b^2+3)}6\ne0.
\]
This contradicts the third input equation. Both pole arguments include
\(v=\pm e\).

Assume henceforth \(\Im F\ne0\). Rotate about \(e\) so that
\(\boldsymbol K=(-b,k,0)\), \(k=\sqrt{3-b^2}>0\). Put
\[
 \rho=\frac{3b}{b^2+3},\qquad d_0=\boldsymbol K+2\rho e,
 \qquad e_B=-\frac{b^2+3}{3h(1+b^2)}d_0.                  \tag{74.11}
\]
The scalar multiplier is nonzero.
If \(v=\pm e\), write \(F=a+(0,0,kt)\),
\(a^2+k^2t^2=1\), and \(n=(0,n_y,n_z)\). With
\(D_1=2\rho-b=b(3-b^2)/(b^2+3)\), the output equations give
\[
 n_z(a+D_1t)=0,\qquad n_y[a(a+D_1t)-2]=0.
\]
Because \(|D_1|<k\), \(|D_1at|<1/2\); hence the second bracket
cannot vanish. Thus \(n_y=0\), \(n_z=\pm1\), and \(a+D_1t=0\).
The third input equation is \(a+2bt=1\). At \(b=0\) these are
inconsistent. Otherwise they give
\[
 t=\frac{b^2+3}{3b(1+b^2)},\qquad
 a=-\frac{3-b^2}{3(1+b^2)},\qquad
 a^2+k^2t^2=\frac{3-b^2}{b^2(1+b^2)}.
\]
The sphere condition forces \((b^2-1)(b^2+3)=0\).
In particular neither half parameter survives. This argument excludes
the axis on the open branch, without making an endpoint claim.

If \(v\parallel\boldsymbol K\), write
\(F=a+(kp,bp,kq)\), \(a^2+3p^2+k^2q^2=1\).
Here \(n\) is proportional to
\(N_0=(1-b^2)\boldsymbol K-2be\ne0\). The output-pair sum becomes
\[
\begin{aligned}
0&=N_0\cdot[F d_0F^*-3d_0+2(d_0\cdot\boldsymbol K)\boldsymbol K]\\
 &=\frac{2(3-b^2)}{b^2+3}
       [(3-b^2)(a+2bq)^2+3(1+b^2)]>0.
\end{aligned}                                                     \tag{74.12}
\]
Thus this full stratum is impossible. We may now write
\[
 F=a+t(\boldsymbol K\times v),\quad t\ne0,\quad
 d=\boldsymbol K\cdot v,\quad\Delta=e\cdot(\boldsymbol K\times v),
\]
\[
 \Delta^2=3-b^2-3c^2-d^2-2bcd,\qquad
 a^2+t^2(3-d^2)=1.                                     \tag{74.13}
\]
The excluded parallel case was essential for this parametrization.

### 74.4. The remaining scalar equations

For \(\lambda=1,3\), define
\[
\begin{gathered}
 A_c=1-3c^2,\quad V_c=1-c^2,\quad Z=3cV_c,\quad
 W=A_cd-2bc,\quad J=3-d^2,\quad u_0=a-1-td,\\
 E_\lambda=-bu_0+3tc-\lambda t\Delta,\quad
 N_\lambda=u_0W+3tV_c-2\lambda ct\Delta,\\
 P_\lambda=3u_0^2+9t^2+\lambda^2t^2J+6u_0td,\quad
 C_\lambda=-u_0A_c\Delta+\lambda t(bV_c+cW).
\end{gathered}
\]
The four remaining equations, after replacing \(n\) by its nonzero
multiple \(N(v)\), are
\[
\begin{aligned}
 I={}&[(1+3a)^2-P_3]Z+2E_3N_3-2(1+3a)C_3=0,\\
 D_f={}&2\Delta[ca-t\{\rho(1+c^2)+cd\}]=0,\\
 S_f={}&[a^2-t^2J-3](W+2\rho Z)+8\rho ct^2\Delta^2\\
      &+2at[(3-2\rho b)V_c-(d+2\rho c)W]
         +6(d+2\rho c)V_c=0,\\
 O_f={}&[(3+a)^2-P_1](W+2\rho Z)
       +2[3(a-1)+2\rho E_1]N_1\\
      &-2(3+a)[-6ct\Delta-t(3V_c-dW)+2\rho C_1]=0.
\end{aligned}                                                     \tag{74.14}
\]
For direct reconstruction from (74.8)–(74.9), use
\[
 \mathcal Q=\frac{1+3F^*+\boldsymbol K(F^*-1)}4,\qquad
 G=B^*T_0=\frac{3+F^*+\boldsymbol K(F^*-1)}4.             \tag{74.15}
\]
Then \(I=16N\cdot\mathcal Q^*e\mathcal Q\), \(S_f\) is
\(N\cdot[F d_0F^*-3d_0+6(d_0\cdot v)v]\), and
\(O_f=16N\cdot G^*d_0G\). The difference equation is \(D_f=0\).
Expansion by scalar and vector quaternion multiplication proves these
identities; (74.13) supplies only the unit-vector and Gram relations.

We now fix \(b=1/2\), so \(k^2=11/4\) and \(\rho=6/13\).
Two exact ideal certificates exclude the remaining plane and nonplane charts.

### 74.5. Finite polynomial-operation convention

Both certificates below are fully specified by their printed seeds and
operation tables. Over \(\mathbb Q\), use graded reverse lexicographic
order in the displayed variable order: larger total degree is larger;
at equal degree, at the last differing coordinate the smaller exponent
is larger. Write \(\operatorname{LM},\operatorname{LC}\) for leading
monomial and coefficient. Define
\[
 \mathsf S(f,g)=\frac{m}{\operatorname{LM}(f)}
                    \frac f{\operatorname{LC}(f)}
              -\frac{m}{\operatorname{LM}(g)}
                    \frac g{\operatorname{LC}(g)},\qquad
 m=\operatorname{lcm}(\operatorname{LM}(f),\operatorname{LM}(g)).
\]
Define \(\mathsf R(f;g_1,\ldots,g_s)\) by ordinary ordered multivariate
division: repeatedly cancel the leading term using the first listed
\(g_j\) whose leading monomial divides it; if none divides it, transfer
that term to the remainder. Normalize the final nonzero remainder by
its leading coefficient. An empty divisor list just makes \(f\) monic.
All displayed uses have nonzero divisors and nonzero final remainder.

In each table, row \(j\) defines polynomial \(z_j\). The notation
\(\mathsf I(i)\) means seed \(i\), \(\mathsf S(p,q)\) means
\(\mathsf S(z_p,z_q)\), and \(\mathsf R(p;q_1,\ldots,q_s)\)
means \(\mathsf R(z_p;z_{q_1},\ldots,z_{q_s})\).
Every reference points backward. By induction every row lies in the
seed ideal: an S-polynomial is a polynomial combination, and a division
remainder differs from its input by polynomial multiples of divisors.
Thus no theorem asserting correctness of a Gröbner-basis implementation
is needed. The tables specify finite rational calculations, including
the divisor order, rather than a choice of elimination strategy.

### 74.6. The plane chart and its strictly positive consequence

If \(\Delta=0\), the retained nonparallel vectors satisfy
\[
 v=(x,ky,0),\quad F=a+(0,0,kt),\quad
 x^2+k^2y^2=a^2+k^2t^2=1.
\]
The already handled points \(v=\pm e\), \(F=-1\) allow the complete
Cayley chart
\[
 x=\frac{1-k^2u^2}{1+k^2u^2},\quad y=\frac{2u}{1+k^2u^2},\qquad
 a=\frac{1-k^2r^2}{1+k^2r^2},\quad t=\frac{2r}{1+k^2r^2},
 \qquad u\ne0.                                         \tag{74.16}
\]
All denominators are positive. Set \(N=(1-3x^2)v+2xe\).
The three retained original equations are
\[
 N\cdot\mathcal Q^*e\mathcal Q=0,\quad
 N\cdot[F d_0F^*-3d_0+6(d_0\cdot v)v]=0,\quad
 N\cdot G^*d_0G=0.                                    \tag{74.17}
\]
Use variable order \((r,u)\). The following coefficient table defines
polynomials \(p_i=\sum_{j=0}^4p_{ij}(u)r^j\). Define seeds
\(f_0=p_0/14641\), \(f_1=p_1/190333\), and \(f_2=p_2/73205\).

| i | j | \(p_{ij}(u)\) |
| --- | --- | --- |
| 0 | 4 | \(121 \left(11 u^{2} - 4 u - 4\right) \left(11 u^{2} + 22 u - 4\right)\) |
| 0 | 3 | \(44 \left(121 u^{4} + 726 u^{3} - 176 u^{2} - 264 u + 16\right)\) |
| 0 | 2 | \(- 44 \left(121 u^{4} - 1386 u^{3} - 176 u^{2} + 504 u + 16\right)\) |
| 0 | 1 | \(- 192 \left(121 u^{4} - 176 u^{2} + 16\right)\) |
| 0 | 0 | \(- 768 u \left(11 u^{2} - 4\right)\) |
| 1 | 4 | \(1573 \left(11 u^{2} + 4\right)^{2}\) |
| 1 | 3 | \(484 \left(121 u^{4} - 858 u^{3} - 176 u^{2} + 312 u + 16\right)\) |
| 1 | 2 | \(264 \left(11 u^{2} - 4\right) \left(143 u^{2} + 44 u - 52\right)\) |
| 1 | 1 | \(- 176 \left(121 u^{4} - 858 u^{3} - 176 u^{2} + 312 u + 16\right)\) |
| 1 | 0 | \(208 \left(11 u^{2} + 4\right)^{2}\) |
| 2 | 4 | \(121 \left(605 u^{4} - 726 u^{3} - 880 u^{2} + 264 u + 80\right)\) |
| 2 | 3 | \(121 \left(605 u^{4} + 462 u^{3} - 880 u^{2} - 168 u + 80\right)\) |
| 2 | 2 | \(66 \left(121 u^{4} + 726 u^{3} - 176 u^{2} - 264 u + 16\right)\) |
| 2 | 1 | \(44 \left(121 u^{4} - 858 u^{3} - 176 u^{2} + 312 u + 16\right)\) |
| 2 | 0 | \(8 \left(1573 u^{4} + 726 u^{3} - 2288 u^{2} - 264 u + 208\right)\) |

Writing \(D_0'=(11r^2+4)^2(11u^2+4)^3>0\), the three expressions in
(74.17) are respectively
\[
 \frac{161051u}{D_0'}f_0,\qquad
 \frac{1288408u}{D_0'}f_1,\qquad
 -\frac{6442040u}{13D_0'}f_2.                            \tag{74.18}
\]
These exact identities follow from (74.15)–(74.16). Every multiplier is
nonzero, so no solution is lost. The following finite certificate uses
these three seeds.

| j | Definition of \(z_j\) |
| --- | --- |
| 0 | \(\mathsf I(0)\) |
| 1 | \(\mathsf I(1)\) |
| 2 | \(\mathsf I(2)\) |
| 3 | \(\mathsf R(0;)\) |
| 4 | \(\mathsf R(1;0)\) |
| 5 | \(\mathsf R(2;0)\) |
| 6 | \(\mathsf R(3;)\) |
| 7 | \(\mathsf R(4;)\) |
| 8 | \(\mathsf R(5;4)\) |
| 9 | \(\mathsf R(6;)\) |
| 10 | \(\mathsf R(7;)\) |
| 11 | \(\mathsf R(8;)\) |
| 12 | \(\mathsf S(9,11)\) |
| 13 | \(\mathsf R(12;11,10)\) |
| 14 | \(\mathsf S(10,11)\) |
| 15 | \(\mathsf R(14;11,10,13)\) |
| 16 | \(\mathsf S(15,11)\) |
| 17 | \(\mathsf R(16;15,11,10,13)\) |
| 18 | \(\mathsf S(17,13)\) |
| 19 | \(\mathsf R(18;17,15,11,10)\) |
| 20 | \(\mathsf S(19,15)\) |
| 21 | \(\mathsf R(20;17,19,15,11,10)\) |
| 22 | \(\mathsf S(21,17)\) |
| 23 | \(\mathsf R(22;17,21,19,15,11,10)\) |
| 24 | \(\mathsf S(23,19)\) |
| 25 | \(\mathsf R(24;17,21,23,19,15,11,10)\) |
| 26 | \(\mathsf S(25,10)\) |
| 27 | \(\mathsf R(26;25,17,23,19,15,11)\) |
| 28 | \(\mathsf S(27,11)\) |
| 29 | \(\mathsf R(28;27,25,17,23,19,15)\) |
| 30 | \(\mathsf S(29,15)\) |
| 31 | \(\mathsf R(30;29,27,25,17,23,19)\) |
| 32 | \(\mathsf S(31,19)\) |
| 33 | \(\mathsf R(32;31,29,27,25,17,23)\) |
| 34 | \(\mathsf S(33,23)\) |
| 35 | \(\mathsf R(34;33,31,29,27,25,17)\) |
| 36 | \(\mathsf S(35,17)\) |
| 37 | \(\mathsf R(36;35,33,31,29,27,25)\) |
| 38 | \(\mathsf S(37,25)\) |
| 39 | \(\mathsf R(38;37,35,33,31,29,27)\) |
| 40 | \(\mathsf S(39,27)\) |
| 41 | \(\mathsf R(40;39,37,35,33,31,29)\) |
| 42 | \(\mathsf S(41,29)\) |
| 43 | \(\mathsf R(42;41,39,37,35,33,31)\) |
| 44 | \(\mathsf R(33;39,41,43)\) |
| 45 | \(\mathsf R(39;41,43)\) |

The last two rows have the particularly small values
\[
 z_{44}=u^6+\frac8{11}u^4+\frac{64}{121}u^2-\frac{192}{1331}
                -\frac{144}{121}ru-\frac{12}{11}r^3u,
\]
\[
 z_{45}=\frac{256}{1089}u-\frac{40}{99}u^3-\frac29u^5
             -\frac{16}{121}r+\frac{12}{11}ru^2
             -\frac4{33}r^3+r^3u^2.
\]
Consequently the following explicit combination lies in the seed ideal:
\[
\begin{aligned}
 &(14641u^2-5324/3)z_{44}+15972u z_{45}\\
 &\qquad=14641u^8+5324u^6+704u^2+256\\
 &\qquad=(11u^2+4)^2[(11u^2-2)^2+12]>0.                 \tag{74.19}
\end{aligned}
\]
This excludes the entire remaining real plane chart.

### 74.7. The nonplane chart and its impossible interior root

Now \(\Delta\ne0\), \(|c|<1\), and \(t\ne0\). The undivided
\(D_f=0\) in (74.14), with \(\rho=6/13\ne0\), excludes \(c=0\).
Hence the substitutions
\[
 U=c^2,\quad R=cd,\quad K=c\Delta,\quad T=t/c,\qquad
 a=T\left[\frac6{13}(1+U)+R\right],\qquad0<U<1            \tag{74.20}
\]
are legitimate. In this subsection \(K,R,T\) are formal scalar
variables, distinct from \(\boldsymbol K\), the reflection operator,
and the quaternion \(T_0\). The five polynomial seeds are as follows;
the variable order is \((T,K,R,U)\).

For \(i=0,1,2\), set \(f_i=A_iT^2+B_iT+C_i\), where

\[
A_0=9 \left(676 K^{2} U - 72 K U^{3} - 354 K U^{2} - 258 K U + 24 K + 676 R^{2} U + 12 R U^{3} + 735 R U^{2} + 43 R U - 4 R - 72 U^{4} + 1830 U^{3} - 1506 U^{2} - 28 U\right).
\]
\[
B_0=156 \left(6 K U^{2} - 9 K U - 2 K - 3 R U^{2} + 24 R U + R - 18 U^{3} + 12 U^{2} + 17 U\right).
\]
\[
C_0=169 \left(6 K U - 2 K + 3 R U - R + 6 U^{2} - 5 U\right).
\]
\[
A_1=2704 K^{2} U + 2704 R^{2} U - 468 R U^{3} + 4693 R U^{2} + 2613 R U + 156 R - 432 U^{4} + 4404 U^{3} - 3143 U^{2} + 1992 U.
\]
\[
B_1=0.
\]
\[
C_1=169 \left(13 R U + 13 R + 12 U^{2} + U\right).
\]
\[
A_2=676 K^{2} U - 216 K U^{3} - 1062 K U^{2} - 774 K U + 72 K + 676 R^{2} U - 360 R U^{3} + 1480 R U^{2} + 1284 R U + 120 R + 216 U^{4} + 1110 U^{3} - 1613 U^{2} + 1380 U.
\]
\[
B_2=- 156 \left(6 K U^{2} - 48 K U - 2 K + 3 R U^{2} - 24 R U - R + 18 U^{3} - 12 U^{2} - 17 U\right).
\]
\[
C_2=1014 \left(3 U - 1\right) \left(K - 2 R - U\right).
\]
\[
f_3=4 K^{2} + 4 R^{2} + 4 R U + 12 U^{2} - 11 U.
\]
\[
f_4=156 R T^{2} U + 156 R T^{2} + 36 T^{2} U^{2} + 579 T^{2} U + 36 T^{2} - 169.
\]

Substituting (74.20) backward, \(f_0,f_1,f_2\) equal respectively
\(169cI\), \((2197c/3)S_f\), and \((2197c/12)O_f\).
The other two equal
\[
 4c^2(\Delta^2-11/4+3c^2+d^2+cd),\qquad
 169[a^2+t^2(3-d^2)-1].                                 \tag{74.21}
\]
Thus all five seeds vanish on the chart, with every used multiplier
nonzero. The finite certificate is:

| j | Definition of \(z_j\) |
| --- | --- |
| 0 | \(\mathsf I(0)\) |
| 1 | \(\mathsf I(1)\) |
| 2 | \(\mathsf I(2)\) |
| 3 | \(\mathsf I(3)\) |
| 4 | \(\mathsf I(4)\) |
| 5 | \(\mathsf R(0;)\) |
| 6 | \(\mathsf R(1;)\) |
| 7 | \(\mathsf R(2;0,1)\) |
| 8 | \(\mathsf R(3;)\) |
| 9 | \(\mathsf R(4;)\) |
| 10 | \(\mathsf R(5;)\) |
| 11 | \(\mathsf R(6;)\) |
| 12 | \(\mathsf R(7;)\) |
| 13 | \(\mathsf R(8;)\) |
| 14 | \(\mathsf R(9;)\) |
| 15 | \(\mathsf S(11,14)\) |
| 16 | \(\mathsf R(15;13,14,12)\) |
| 17 | \(\mathsf S(16,12)\) |
| 18 | \(\mathsf R(17;13,14)\) |
| 19 | \(\mathsf S(16,14)\) |
| 20 | \(\mathsf R(19;14,18,16)\) |
| 21 | \(\mathsf S(20,18)\) |
| 22 | \(\mathsf R(21;14,18,16,20)\) |
| 23 | \(\mathsf S(22,16)\) |
| 24 | \(\mathsf R(23;22,14,18)\) |
| 25 | \(\mathsf S(22,14)\) |
| 26 | \(\mathsf R(25;24,22,14,18,20)\) |
| 27 | \(\mathsf S(18,13)\) |
| 28 | \(\mathsf R(27;13,24,22,18,20)\) |
| 29 | \(\mathsf S(18,16)\) |
| 30 | \(\mathsf R(29;13,24,22,14,26,18,20)\) |
| 31 | \(\mathsf S(30,28)\) |
| 32 | \(\mathsf R(31;13,24,22,14,30,18,20)\) |
| 33 | \(\mathsf S(32,30)\) |
| 34 | \(\mathsf R(33;13,24,22,14,26,32,30,18,20)\) |
| 35 | \(\mathsf S(32,18)\) |
| 36 | \(\mathsf R(35;13,24,22,14,26,32,30,18,20,34)\) |
| 37 | \(\mathsf S(30,24)\) |
| 38 | \(\mathsf R(37;13,24,22,14,26,32,30,18,20,34)\) |
| 39 | \(\mathsf S(38,14)\) |
| 40 | \(\mathsf R(39;13,24,22,14,38,32,30,18,20)\) |
| 41 | \(\mathsf S(38,26)\) |
| 42 | \(\mathsf R(41;13,24,22,14,26,38,32,40,30,18,20,36,34)\) |
| 43 | \(\mathsf S(38,13)\) |
| 44 | \(\mathsf R(43;13,24,22,14,26,38,32,40,30,18,20,42,36,34)\) |
| 45 | \(\mathsf S(30,20)\) |
| 46 | \(\mathsf R(45;13,24,22,14,26,38,32,30,18,20,36,34)\) |
| 47 | \(\mathsf S(46,22)\) |
| 48 | \(\mathsf R(47;13,24,22,14,46,38,32,40,30,18,20)\) |
| 49 | \(\mathsf S(46,38)\) |
| 50 | \(\mathsf R(49;13,24,22,14,46,26,38,48,32,40,30,18,20,44,42,36,34)\) |
| 51 | \(\mathsf S(50,34)\) |
| 52 | \(\mathsf R(51;24,22,46,50,38,48,32,40,30,18,20,36)\) |
| 53 | \(\mathsf S(46,13)\) |
| 54 | \(\mathsf R(53;13,24,22,14,46,50,26,38,52,48,32,40,30,18,20,44,42,36)\) |
| 55 | \(\mathsf S(54,50)\) |
| 56 | \(\mathsf R(55;24,54,46,50,38,52,48,32,40,30,18,44,42,36)\) |
| 57 | \(\mathsf S(54,13)\) |
| 58 | \(\mathsf R(57;13,24,54,46,50,38,56,52,48,32,40,30,18,44,42,36)\) |
| 59 | \(\mathsf S(58,36)\) |
| 60 | \(\mathsf R(59;24,54,46,58,50,38,52,48,32,40,30,18)\) |
| 61 | \(\mathsf S(60,26)\) |
| 62 | \(\mathsf R(61;13,24,22,60,54,14,46,58,50,26,38,56,52,48,32,40,30,18,44,42)\) |
| 63 | \(\mathsf S(62,24)\) |
| 64 | \(\mathsf R(63;24,22,62,60,54,14,46,38,48,32,40,30,18)\) |
| 65 | \(\mathsf S(64,24)\) |
| 66 | \(\mathsf R(65;24,22,64,62,60,54,14,46,58,38,52,48,32,40,30,18)\) |
| 67 | \(\mathsf S(66,54)\) |
| 68 | \(\mathsf R(67;24,66,22,64,62,60,54,14,46,58,50,26,38,56,52,48,32,40,30)\) |
| 69 | \(\mathsf S(68,30)\) |
| 70 | \(\mathsf R(69;24,68,66,22,64,62,60,54,14,46,58,38,56,52,48,32,40)\) |
| 71 | \(\mathsf S(70,62)\) |
| 72 | \(\mathsf R(71;24,70,68,66,22,64,62,60,54,14,46,58,50,26,38,56,52,48,32)\) |
| 73 | \(\mathsf S(68,60)\) |
| 74 | \(\mathsf R(73;24,70,68,66,22,64,62,60,54,14,46,72,58,50,26,38,56,52,48,32)\) |
| 75 | \(\mathsf S(74,68)\) |
| 76 | \(\mathsf R(75;74,24,70,68,66,22,64,62,60,54,14,46,72,58,50,26,38,56,52,48)\) |
| 77 | \(\mathsf S(74,66)\) |
| 78 | \(\mathsf R(77;13,74,24,70,68,66,22,64,62,60,54,14,46,76,72,58,50,26,38,56,52,48)\) |
| 79 | \(\mathsf S(78,70)\) |
| 80 | \(\mathsf R(79;78,74,24,70,68,66,22,64,62,60,54,14,46,76,72,58,50,26,38,56,52)\) |
| 81 | \(\mathsf S(80,74)\) |
| 82 | \(\mathsf R(81;13,80,78,74,24,70,68,66,22,64,62,60,54,14,46,76,72,58,50,26,38)\) |
| 83 | \(\mathsf S(78,74)\) |
| 84 | \(\mathsf R(83;13,80,78,74,24,70,68,66,22,64,62,60,54,14,46,76,72,58,50,26,38,82,56)\) |
| 85 | \(\mathsf S(74,22)\) |
| 86 | \(\mathsf R(85;80,78,74,24,70,68,66,22,64,62,60,54,14,46,58,50,26,38,84,82,56)\) |
| 87 | \(\mathsf S(70,68)\) |
| 88 | \(\mathsf R(87;13,80,78,74,24,70,68,66,22,64,62,60,54,14,46,86,76,72,58,50,26,38,84,82,56)\) |
| 89 | \(\mathsf S(88,74)\) |
| 90 | \(\mathsf R(89;13,88,80,78,74,24,70,68,66,22,64,62,60,54,14,46,86,76,72,58,50,26,38,84,82)\) |
| 91 | \(\mathsf S(90,82)\) |
| 92 | \(\mathsf R(91;90,88,80,78,74,24,70,68,66,22,64,62,60,54,14,86,76,72,58,50,26,84)\) |
| 93 | \(\mathsf S(16,10)\) |
| 94 | \(\mathsf R(93;13,90,92,88,80,78,74,24,70,68,66,22,64,62,60,54,14,76,72,58,50,26)\) |
| 95 | \(\mathsf S(94,14)\) |
| 96 | \(\mathsf R(95;94,90,88,80,78,74,24,70,68,66,22,64,62,60,54)\) |
| 97 | \(\mathsf S(96,54)\) |
| 98 | \(\mathsf R(97;96,94,90,88,80,78,74,24,70,68,66,22,64,62,60)\) |
| 99 | \(\mathsf S(98,60)\) |
| 100 | \(\mathsf R(99;98,96,94,90,88,80,78,74,24,70,68,66,22,64,62)\) |
| 101 | \(\mathsf S(100,62)\) |
| 102 | \(\mathsf R(101;100,98,96,94,90,88,80,78,74,24,70,68,66,22,64)\) |
| 103 | \(\mathsf S(102,64)\) |
| 104 | \(\mathsf R(103;102,100,98,96,94,90,88,80,78,74,24,70,68,66,22)\) |
| 105 | \(\mathsf S(104,22)\) |
| 106 | \(\mathsf R(105;104,102,100,98,96,94,90,88,80,78,74,24,70,68,66)\) |
| 107 | \(\mathsf S(106,66)\) |
| 108 | \(\mathsf R(107;106,104,102,100,98,96,94,90,88,80,78,74,24,70,68)\) |
| 109 | \(\mathsf S(108,68)\) |
| 110 | \(\mathsf R(109;108,106,104,102,100,98,96,94,90,88,80,78,74,24,70)\) |
| 111 | \(\mathsf S(110,70)\) |
| 112 | \(\mathsf R(111;110,108,106,104,102,100,98,96,94,90,88,80,78,74,24)\) |
| 113 | \(\mathsf S(112,24)\) |
| 114 | \(\mathsf R(113;112,110,108,106,104,102,100,98,96,94,90,88,80,78,74)\) |
| 115 | \(\mathsf S(114,74)\) |
| 116 | \(\mathsf R(115;114,112,110,108,106,104,102,100,98,96,94,90,88,80,78)\) |
| 117 | \(\mathsf S(116,78)\) |
| 118 | \(\mathsf R(117;116,114,112,110,108,106,104,102,100,98,96,94,90,88,80)\) |
| 119 | \(\mathsf S(118,80)\) |
| 120 | \(\mathsf R(119;118,116,114,112,110,108,106,104,102,100,98,96,94,90,88)\) |
| 121 | \(\mathsf S(120,88)\) |
| 122 | \(\mathsf R(121;120,118,116,114,112,110,108,106,104,102,100,98,96,94,90)\) |
| 123 | \(\mathsf S(122,104)\) |
| 124 | \(\mathsf R(123;122,120,118,116,114,112,110,108,106)\) |
| 125 | \(\mathsf S(124,106)\) |
| 126 | \(\mathsf R(125;124,122,120,118,116,114,112,110,108)\) |
| 127 | \(\mathsf S(126,108)\) |
| 128 | \(\mathsf R(127;126,124,122,120,118,116,114,112,110)\) |
| 129 | \(\mathsf S(128,110)\) |
| 130 | \(\mathsf R(129;128,126,124,122,120,118,116,114,112)\) |
| 131 | \(\mathsf R(120;126,128,130,122,124)\) |

Its final value is exactly
\[
 z_{131}=U^3-U=U(U-1)(U+1).                              \tag{74.22}
\]
This contradicts \(0<U<1\). The plane and nonplane cases, together
with §74.3, exhaust all the original real charts, proving the upper
classification at \(b=1/2\). Direct substitution verifies that all
four rays (74.2) attain it and are projectively distinct.

### 74.8. Negative transport and the same-union graph consequence

Let \(X=\begin{psmallmatrix}0&1\\1&0\end{psmallmatrix}\) and
\(Z=\operatorname{diag}(1,-1)\). Directly from (74.1),
\[
 H_0(-b)=(Z\otimes I_3)H_0(b)(X\otimes I_3).             \tag{74.23}
\]
Both factors are monomial, \(X\otimes I_3\) commutes with every
synchronous permutation, and channel exchange maps (74.2) to the
negative-parameter set, with the sign relabeled after dephasing.
This proves the negative half case. Conjugation inside \(S_3\) proves
the other two transposition cases.

**Corollary 74.2 (one symmetry-union is bipartite).** At \(b=\pm1/2\),
for every noncanonical common-flat ray \([w]\), the orthogonality graph
induced on \(S_3[w]\cup S_3[\Theta w]\) is bipartite, with these two
orbits as its parts. In particular this union contains no orthogonal
triple.

To prove it, a relative transposition edge is excluded by Theorem 74.1.
An order-three edge \(w\perp Sw\) gives the full synchronous triple
\(w,Sw,S^2w\), excluded outside canonical rays by Proposition 57.1
in [Continuation I](MUB_SIX_FOURTH_BASIS_THEORY_CONTINUATION.md).
Its parameter convention agrees with (74.1): put \(a=bh\), so its
\(p(a)-1=P\), \(q(a)-1=Q\), using the positive roots \(h+b,h-b\).
Thus neither orbit has an internal edge. The original identities
\(H_0\Theta=-\Theta H_0\), \(R\Theta=\Theta R\), and
\(\Theta^2=-I\) show that \(\Theta\) preserves common-flatness and
the canonical set. The two projective orbits are disjoint: a fixed
projective ray of \(R\Theta\) is impossible since its square is
\(-I\) for a transposition, and its \(2\operatorname{ord}(R)\)-th
power is \(-I\) for odd-order \(R\). An antiunitary projective
fixed ray instead has positive scalar even powers. This proves the
corollary.

Edges between different such unions remain outside this result.
Neither an exhaustive half-parameter ray census nor arbitrary
noncanonical-triple exclusion follows from the same-union statement.
The whole-open-branch pair and basis classification remains open.

## 75. Exact channel charts and low-dimensional common-flat ray quotients

### 75.1. Original equations and the coverage theorem

**Definition 75.1 (channels and allowed symmetries).** Retain the actual
matrix (74.1), and write
\[
 M=\sqrt6H_0,\qquad A=3+P,\quad B=3+Q,\qquad
 w=(x,y),\quad X=\sum_{j=0}^2x_j,\quad Y=\sum_{j=0}^2y_j.
\]
A common-flat input has \(|x_j|=|y_j|=1\) and every entry of \(Mw\)
of squared modulus six. Its normalized ray is \([w/\sqrt6]\).
The original output channels are
\[
 a_j=X+Y+Px_j+Qy_j,\qquad
 \ell_j=X-Y+\bar Qx_j-\bar Py_j.                    \tag{75.1}
\]
The synchronous \(S_3\) action permutes both channels in the same order.
The antiunitary \(\Theta(x,y)=(-\bar y,\bar x)\) preserves common-flatness,
commutes with this action, and satisfies \(\Theta^2=-I\).
Common scalar phases do not change rays. An aligned repeated pair means
that two equal entries occupy the same two positions in both channels;
a constant channel permits any repeated pair.

**Theorem 75.1 (complete punctured-branch chart coverage).** For every
\(0<|b|<1\), every common-flat ray has one of the following descriptions:

1. One of the four canonical nonzero-mode rays (74.2).
2. A solution of the four-real-variable system (75.13)–(75.15), followed
   by its cubic reconstruction in any of the six root orders, and
   optionally by \(\Theta\).
3. A common phase and synchronous permutation of an aligned input
   \((1,1,z;g,g,gr)\). These are exactly the two constant canonical rays
   (75.28), the finite two-real-variable quotient (75.31) with both
   \(\Theta\) choices, and the pole pair (75.36)–(75.37).

The pole pair occurs only when \(b^2\) equals the unique zero in \((0,1)\)
of \(2t^5+33t^4+90t^3+4t-1\). No finite number of solutions of either
quotient is asserted. The center and endpoints are outside this coverage
theorem; the unaligned exclusion in Theorem 75.4 includes them.

The proof is supplied by Theorems 75.2–75.5 below and their concluding
coverage argument. These model-specific reductions are repo-derived.
Algebraic construction of vectors unbiased to a prescribed Hadamard
matrix has a prior computational treatment in Brierley and Weigert,
[Constructing Mutually Unbiased Bases in Dimension Six](https://arxiv.org/abs/0901.4051v2),
Phys. Rev. A 79, 052316 (2009). No census, approximation bound or
no-quartet assertion from that source is a premise here.

### 75.2. Zero channel means force the four nonzero-mode rays

**Theorem 75.2 (zero-channel-mean classification).** If \(0<|b|<1\) and
\(w\) is common-flat, then \(X=0\) or \(Y=0\) implies \(X=Y=0\),
and its ray is one of the four rays (74.2).

**Proof.** By \(\Theta\), it suffices first to exclude \(X=0,Y\ne0\).
Choose the common phase so \(Y=3t>0\). A zero-sum triple of unit phases
is a scalar multiple of the three cube roots of unity. Synchronous
permutation gives \(x=\lambda(1,\omega,\omega^2)\), \(|\lambda|=1\).
The vectors \(1,x,\bar x\) are an orthogonal basis, so write uniquely
\(y=t1+cx+d\bar x\). With \(e=\bar\lambda^3\), input flatness gives
\[
 t^2+|c|^2+|d|^2=1,\qquad
 t(c+\bar d)+e\bar c d=0.                           \tag{75.2}
\]
The two original unnormalized output channels are
\[
 Bt1+(P+Qc)x+Qd\bar x,\qquad
 -\bar At1+(\bar Q-\bar Pc)x-\bar Pd\bar x.
\]
For \(kt1+Cx+D\bar x\), the coefficient of \(x\) in its squared moduli
is \(t(\bar kC+k\bar D)+e\bar CD\). Adding the two output coefficients
and subtracting six times the input coefficient, then dividing by
\(t>0\), gives
\[
 h(b+i)+(-3-ib)c+(-3+ib)\bar d=0.                   \tag{75.3}
\]
Subtracting \(|Q|^2\) times the input coefficient from the upper output
coefficient gives
\[
 t[\bar BP+3Qc+3\bar Q\bar d]+e\bar PQd=0.
\]
Multiply this by \(\bar c\) and subtract \(\bar PQ\) times the second
identity in (75.2). The upper constant norm equation gives the second
of the following necessary equations:
\[
\begin{aligned}
 E&=\bar c[\bar BP+3Qc+3\bar Q\bar d]-\bar PQ(c+\bar d)=0,\\
 N&=2\operatorname{Re}(P\bar Q\bar c)
                  -3bh(1-|c|^2-|d|^2)=0.           \tag{75.4}
\end{aligned}
\]
No division by \(c\) or \(d\) has been made. Put \(q=b^2\),
\(d=u+iv\), \(r^2=u^2+v^2\). Equation (75.3) gives
\[
 c=\frac{h(b+i)+(-3+ib)(u-iv)}{3+ib}.
\]
Define the following three real quadratics:
\[
\begin{aligned}
 F_0={}&3h(q+1)(q+3)r^2-2(q^2-15q-36)v
                         -2b(q+21)u+18h(q+1),\\
 F_1={}&3h(q+1)(q+3)r^2-2hq(q+1)
                         +(-4q^2+6q+18)v+2b(q-3)u,\\
 F_2={}&3bh(q+1)(q+9)r^2-2bh(q+1)(q+3)
                         -2b(q-3)(q+3)v+(q^2-42q-27)u.
                                                               \tag{75.5}
\end{aligned}
\]
Direct substitution, using \((1+b^2)h^2=3-b^2\), yields
\[
 \operatorname{Re}E=\frac{-bF_0}{(q+1)(q+9)},\quad
 \operatorname{Im}E=\frac{3F_1}{(q+1)(q+9)},\quad
 N=\frac{2F_2}{(q+1)(q+9)}.                         \tag{75.6}
\]
Since \(b\ne0\), all three \(F_j\) must vanish. But
\[
 F_0-F_1=2(q+9)[h(q+1)+(q+3)v-2bu],
\]
and \((q+3)F_2-b(q+9)F_0\) is linear in \(u,v\). Substituting
\(v=[2bu-h(q+1)]/(q+3)\) into it gives
\[
 \frac{q+1}{q+3}
 [3(q+9)(q^2-12q-9)u-2bh(q-3)(q^2+12q+9)]=0.
\]
For \(0<q<1\), the factor \(q^2-12q-9\) is strictly negative. Thus
\[
 u=\frac{2bh(q-3)(q^2+12q+9)}{3(q+9)(q^2-12q-9)},\qquad
 v=\frac{h(q+3)(q^2+36q+27)}{3(q+9)(q^2-12q-9)}.
\]
At these forced values,
\[
\begin{aligned}
 F_0&=-\frac{h(q+1)(q+3)^2 C(q)}{3(q+9)(q^2-12q-9)^2},\\
 C(q)&=4q^5+15q^4-306q^3+864q^2+1782q+729\\
     &=4q^5+15q^4+q^2(864-306q)+1782q+729>0
        \quad(0\leq q\leq1).                       \tag{75.7}
\end{aligned}
\]
This contradicts \(F_0=0\). Applying \(\Theta\) excludes
\(Y=0,X\ne0\) as well.

If both means vanish, each channel is a scalar multiple of \(f_1\)
or \(f_2\). If their modes differ, upper-output flatness requires
\(\operatorname{Re}z=\operatorname{Re}(z\omega)
=\operatorname{Re}(z\omega^2)=0\) for a nonzero scalar \(z\), because
\[
 P\bar Q=\frac{(b^2+3)(1-ib)}{1+b^2}\ne0.
\]
These three real equations force \(z=0\), a contradiction. For equal
modes, dephase to \(w=(f_m,gf_m)\), \(|g|=1\). Flatness becomes
\(\operatorname{Re}(P\bar Q\bar g)=0\), whose two solutions are
\(g=\pm(b+i)/\sqrt{1+b^2}\). Both satisfy the original equations.
This proves the theorem. \(\square\)

### 75.3. A necessary-and-sufficient four-real-variable quotient

**Theorem 75.3 (three-distinct selected channel).** For \(|b|<1\), the
common-flat rays whose upper channel has three distinct entries and
nonzero mean are exactly the reconstructions (75.16) from the system
(75.13)–(75.15). Every root order is retained.

**Proof and definition of the system.** Normalize \(X=3t>0\) by the
unique common phase. Then \(0<t<1\). Put
\(\xi=x_0x_1x_2\) and \(u=x-t1\). The vectors \(1,u,\bar u\) are
linearly independent: multiplying their evaluation matrix by the three
nonzero \(x_j\) reduces its determinant to a nonzero Vandermonde factor.
Consequently there are unique complex \(g,c,d\) with
\[
 y=gt1+cu+d\bar u,\qquad g=Y/X.
\]
The elementary symmetric identities of the three unit roots give
\[
 u^2=tu+\xi\bar u+2t(t-\xi)1,\qquad
 |u|^2=(1-t^2)1-t(u+\bar u).                        \tag{75.8}
\]
For a channel \(kt1+Cu+D\bar u\), define
\[
 \mathcal F(k,C,D)=\bar kC+k\bar D-|C|^2-|D|^2+C\bar D.
\]
Its squared-modulus \(u\)-coefficient and constant coefficient are
\[
 t\mathcal F(k,C,D)+\bar\xi\bar CD,\qquad
 |k|^2t^2+(|C|^2+|D|^2)(1-t^2)
                         +4t\operatorname{Re}[C\bar D(t-\xi)].  \tag{75.9}
\]
Independence of \(1,u,\bar u\) makes vanishing of the first expression
necessary and sufficient for constant moduli.

Set
\[
\begin{gathered}
 U=A+Bg,\qquad V=\bar B-\bar Ag,\\
 Y_c=\mathcal F(g,c,d),\quad
 T_c=\mathcal F(U,P+Qc,Qd),\quad
 L_c=\mathcal F(V,\bar Q-\bar Pc,-\bar Pd),\quad e=\bar\xi/t.
\end{gathered}
\]
The input and two output correlations are
\[
\begin{aligned}
 Y_c+e\bar cd&=0,\\
 T_c+e(|Q|^2\bar c+Q\bar P)d&=0,\\
 L_c+e(|P|^2\bar c-Q\bar P)d&=0.                    \tag{75.10}
\end{aligned}
\]
Using \(|P|^2+|Q|^2=6\), their sum-difference has the exact form
\[
\begin{gathered}
 T_c+L_c-6Y_c=-3(\alpha+\beta c+\bar\beta\bar d),\\
 \alpha=3-ib-h(b+i)\bar g,\qquad
 \beta=(3+ib)\bar g+h(b-i).                         \tag{75.11}
\end{gathered}
\]
If \(\beta=0\), then \(\alpha=12/(3+ib)\ne0\). Every solution
therefore has \(\beta\ne0\) and
\[
 c=-\alpha/\beta-(\bar\beta/\beta)\bar d.           \tag{75.12}
\]
Neither \(c\) nor \(d\) can vanish. Indeed, if \(d=0,c\ne0\), the map
\(y=(g-c)t+cx\) sends three distinct points of the unit circle to the
unit circle. Two distinct circles have at most two intersection points,
so \(g=c\), \(|c|=1\). But the real part of \(\alpha+\beta g\) is six.
If \(c=0,d\ne0\), apply the same argument to \(\bar x\): it gives
\(g=d\), \(|d|=1\), whereas
\(\alpha+\bar\beta\bar g=6-2ib\ne0\).
If \(c=d=0\), the lower channel is a nonzero constant \(y_0\).
The output channels are \(Px+(3t+By_0)1\) and
\(\bar Qx+(3t-\bar Ay_0)1\). Since \(P,Q\ne0\), the same circle
argument forces both centers to vanish, contrary to
\((B+\bar A)y_0=(3-ib)y_0\ne0\). Thus all these strata are excluded
by original flatness, rather than by an additional chart assumption.

The four real unknowns are the real and imaginary parts of \(g,d\),
with \(c\) given by (75.12). Put
\[
 A_c=|c|^2+|d|^2,\quad B_c=|cd|^2,\quad
 A_t=|P+Qc|^2+|Qd|^2,\quad B_t=(P+Qc)\bar Q\bar d.
\]
The system consists of one complex equation and two real equations:
\[
\begin{aligned}
 E&=\bar c(T_c-|Q|^2Y_c)-Q\bar P Y_c=0,\\
 N_y&=(A_c-1)|Y_c|^2
       +B_c[|g|^2-A_c+4\operatorname{Re}(c\bar d+Y_c)]=0,\\
 N_t&=(A_t-6)|Y_c|^2
       +B_c[|U|^2-A_t+4\operatorname{Re}(B_t+T_c)]=0.          \tag{75.13}
\end{aligned}
\]
Its nonzero-denominator and real inequalities are
\[
 \beta cdY_c\ne0,\qquad q=\frac{B_c}{|Y_c|^2},\quad 0<q<1,\qquad
 e=-\frac{Y_c}{\bar cd},                             \tag{75.14}
\]
\[
 \mathscr D=q^2(3-8\operatorname{Re}e)+6q-1<0.        \tag{75.15}
\]
For a fixed parameter these are rational equations and inequalities in
four real variables. Jointly in \(b,h\), adjoin
\((1+b^2)h^2=3-b^2\), \(h>0\). Clearing positive squared-modulus
denominators gives an equivalent real semialgebraic system.

For reconstruction put \(t=\sqrt q>0\), \(\xi=t\bar e\). By definition
of \(q,e\), \(|\xi|=1\). Choose the three roots, in any order, of
\[
 z^3-3tz^2+3t\xi z-\xi=0,\qquad
 x=(x_0,x_1,x_2),\quad u=x-t1,\quad y=gt1+cu+d\bar u.        \tag{75.16}
\]
The discriminant divided by \(\xi^2\) is
\[
 27(3t^4+6t^2-1-8t^3\operatorname{Re}\xi)=27\mathscr D.
\]
Its negative sign is exactly the condition that all three roots are
unit and distinct. To see the equivalence, the cubic is self-inversive,
so its multiset of roots is invariant under \(z\mapsto1/\bar z\)
and contains at least one unit root. If the other two are off the circle,
they are \(re^{i\phi},r^{-1}e^{i\phi}\), \(r>0,r\ne1\); the product
formula for the discriminant makes its quotient by \(\xi^2\) strictly
positive. For three distinct unit roots, writing each difference as
\(2i\) times a sine makes the quotient strictly negative. Discriminant
zero is precisely the repeated-root boundary.

Definition of \(e\) imposes the first equation of (75.10). Since
\(c,d\ne0\), the complex equation in (75.13) reconstructs the second;
(75.11) reconstructs the third. For a channel with zero correlation,
(75.9) rewrites its constant squared norm as
\[
 |C|^2+|D|^2+t^2[|k|^2-|C|^2-|D|^2
                    +4\operatorname{Re}(C\bar D+\mathcal F(k,C,D))].
\]
Thus \(N_y=0\) gives every lower input modulus one, and \(N_t=0\)
gives every upper output squared modulus six. The lower output moduli
are constant by their correlation, so original unitarity \(M^*M=6I\)
forces their common squared modulus to be six. This proves sufficiency.
Conversely the original equations gave every displayed relation; in
particular \(Y_c=-e\bar cd\ne0\). Necessity follows as well.

The six root orders are exactly the synchronous \(S_3\) orbit. An
optional centered coordinate \(Z=\beta c+\alpha/2\), \(A_0=\alpha/2\)
gives the invertible change
\[
 c=\frac{Z-A_0}{\beta},\quad
 d=-\frac{\bar Z+\bar A_0}{\beta},\quad
 |c|^2+|d|^2=\frac{2(|Z|^2+|A_0|^2)}{|\beta|^2},\quad
 c\bar d=\frac{A_0^2-Z^2}{|\beta|^2}.               \tag{75.17}
\]
No covariance condition on the candidate ray or restriction on root
order was used. \(\square\)

### 75.4. Exact exclusion of different repeated pairs

**Theorem 75.4 (unaligned two-value exclusion).** For every \(|b|\leq1\),
there is no common-flat input
\[
 (1,1,z;g,gr,g),\qquad |z|=|r|=|g|=1,\quad z\ne1, r\ne1.     \tag{75.18}
\]

**Proof.** Use the original outputs (75.1), with \(X=2+z\),
\(Y=g(2+r)\), and form the four vanishing differences
\[
\begin{aligned}
 \delta T_1&=\frac{zr(|a_1|^2-|a_0|^2)}{r-1},&
 \delta T_2&=\frac{zr(|a_2|^2-|a_0|^2)}{z-1},\\
 \delta L_1&=\frac{zr(|\ell_1|^2-|\ell_0|^2)}{r-1},&
 \delta L_2&=\frac{zr(|\ell_2|^2-|\ell_0|^2)}{z-1}.
\end{aligned}
\]
Set \(U=(b-i)hg\), \(V=(b+i)h\bar g=\bar U\), so
\(|U|^2=3-b^2\). The following rows, dotted with \((1,U,V)\), are
respectively \(\delta T_1+\delta L_1\), \(\delta T_2+\delta L_2\),
\((1+b^2)h(\delta T_1-\delta L_1)\), and
\((1+b^2)h(\delta T_2-\delta L_2)\):
\[
\begin{aligned}
 S_1={}&(-3z[(r-1)+ib(r+1)],\ -r(2z+1),\ z(z+2)),\\
 S_2={}&(3r[ib(z+1)-(z-1)],\ -r(r+2),\ z(2r+1)),\\
 D_1={}&(-(3-b^2)z[b(r-1)-3i(r+1)],\\
       &\hspace{8mm}-r[i(b^2+3)+2b(2z+1)],\
                 z[-i(b^2+3)z+2b(z+2)]),\\
 D_2={}&((3-b^2)r[b(z-1)+3i(z+1)],\\
       &\hspace{8mm}r[i(b^2+3)r+2b(r+2)],\
                 z[i(b^2+3)-2b(2r+1)]).             \tag{75.19}
\end{aligned}
\]
These are direct identities using only unit phases and the branch
relation. All scalar multipliers are nonzero in (75.18). Define
\[
\begin{aligned}
 f={}&br^2z+brz^3+4brz^2+4brz+br+bz^2\\
     &-2ir^2z^2-ir^2z+irz^3-2irz^2+2irz-ir+iz^2+2iz,\\
 k={}&-ibr^3z-4ibr^2z-ibr^2-ibrz^2-4ibrz-ibz\\
     &-r^3z+2r^2z^2+2r^2z-r^2+rz^2-2rz-2r+z.
\end{aligned}
\]
Expansion of the three-row minors gives
\[
 \det(S_1,S_2,D_1)=6rz(b^2+3)f,\qquad
 \det(S_1,S_2,D_2)=-6irz(b^2+3)k.                  \tag{75.20}
\]
Hence \(f=k=0\). If \(z=-1\), \(r=(1+iv)/(1-iv)\ne-1\), then
\[
 f(-1,r)=\frac{4i(v^2+bv+2)}{(v+i)^2}\ne0
\]
because \(v^2+bv+2=(v+b/2)^2+2-b^2/4>0\). Similarly for
\(r=-1\), \(z=(1+iu)/(1-iu)\ne-1\),
\[
 k(z,-1)=\frac{-4(u^2-bu+2)}{(u+i)^2}\ne0.
\]
At \(z=r=-1\), \(f=4i\), \(k=-4\). All Cayley poles are excluded.

Write \(z=(1+iu)/(1-iu)\), \(r=(1+iv)/(1-iv)\), with real nonzero
\(u,v\). Then
\[
 f=\frac{4iF}{(u+i)^3(v+i)^2},\qquad
 k=\frac{-4G}{(u+i)^2(v+i)^3},
\]
where
\[
\begin{aligned}
 F={}&bu^3v+bu^2+buv+2bv^2+3b+u^3v^2+2u^3+3u^2v-uv^2+3v,\\
 G={}&-2bu^2-buv^3-buv-bv^2-3b+u^2v^3-u^2v+3uv^2+3u+2v^3.
                                                               \tag{75.21}
\end{aligned}
\]
Their sum factors as
\[
\begin{aligned}
 F+G&=(u+v)K,\\
 K&=u^2v^2+2u^2+2v^2+3+b(u-v)(uv-1)\\
  &=[uv-1+b(u-v)/2]^2+\frac{2-b^2}{4}(u-v)^2
                            +\frac32(u+v)^2+2>0.  \tag{75.22}
\end{aligned}
\]
Thus \(v=-u\), including the singular locus of the first two rows;
no division by \(u+v\) has been made.

Put \(U=p+iq\), \(V=p-iq\). Under the Cayley substitution,
\[
 S_1\cdot(1,U,V)=\frac{-2A_1}{(u+i)^2(v+i)},\qquad
 S_2\cdot(1,U,V)=\frac{2A_2}{(u+i)(v+i)^2},
\]
where
\[
\begin{aligned}
 A_1={}&3bu^2+3b+pu^2v-2pu+3pv+qu^2+2quv+3q+3u^2v+3v,\\
 A_2={}&3bv^2+3b+puv^2+3pu-2pv-2quv-qv^2-3q-3uv^2-3u.
\end{aligned}
\]
At \(v=-u\), \(A_1+A_2=6(b-u)(1+u^2)\), so \(u=b\).
The remaining \(S_1\) equation is
\[
 b(b^2+5)p+(b^2-3)q=0.
\]
The \(D_1\) row is \(-2D_0/[(b-i)(b+i)^2]=0\), where
\[
 D_0=(5b^4+18b^2-3)p+b(b^4+2b^2-15)q-b^6-b^4+9b^2+9.
\]
The two coefficient rows have determinant
\((b^2-3)(b^2+1)^2(b^2+3)\ne0\), forcing
\[
 p=\frac{3-b^2}{1+b^2},\qquad q=\frac{b(b^2+5)}{1+b^2},\qquad
 p^2+q^2-(3-b^2)=2(b^2+3)>0.                       \tag{75.23}
\]
This contradicts \(|U|^2=3-b^2\). At \(b=0\), the earlier \(u=b\)
already contradicts \(u\ne0\); the norm contradiction remains valid.
Neither \(b\) nor \(1-b^2\) was divided out. \(\square\)

### 75.5. The aligned chart: a two-real quotient and its unique pole pair

**Theorem 75.5 (complete aligned reduction).** Fix \(0<|b|<1\) and a
repeated pair of positions. The common-flat inputs
\[
 w=(1,1,z;g,g,gr),\qquad |z|=|r|=|g|=1             \tag{75.24}
\]
are precisely the constant rays (75.28), the finite reconstructions
(75.31)–(75.32) with both signs, and the pole pair (75.36)–(75.37).
The finite system parametrizes \(\Theta\) pairs bijectively.

**Proof.** Put \(R=3-b^2\), \(\kappa=(b-i)h\), and
\(\kappa g=p+iq\), with real \(p,q\). Then
\[
 |g|=1\quad\Longleftrightarrow\quad p^2+q^2=R.       \tag{75.25}
\]
If \(z,r\ne-1\), use real Cayley coordinates
\[
 z=\frac{1+iu}{1-iu},\quad r=\frac{1+iv}{1-iv},\qquad
 s=u+v,\quad D=u-v,\quad T=uv,\quad K=D^2+4T=s^2.
\]
For \(s\ne0\), write \(p=sa\), \(q=sc\). The symbol \(D\) here
is a real coordinate. Define three affine-linear polynomials in \(a,c\):
\[
\begin{aligned}
 P_0={}&K[Da-(T+1)c]+bD(1-T)-D^2-2T(T+1),\\
 P_1={}&[bD^2-DT(b^2+1)+D(b^2-3)+b(T^2-2T-3)]a\\
       &+[-b^2D^2-4bD+T^2-2b^2(T+1)+4T+3]c
                              +(b^2-3)(T+1-bD),\\
 P_2={}&[5bD^2+2DT(b^2+2)-2Db^2+3b(T+1)^2]a\\
       &+[-3D^2-2bD(T+1)-(2b^2+7)T^2-10T+2b^2-3]c
                              +2(b^2-3)(T+1+bD).  \tag{75.26}
\end{aligned}
\]
Write \(N_j=|a_j|^2-6\), \(L_j=|\ell_j|^2-6\) for the original
outputs (75.1), where \(j=0\) is a repeated position and \(j=2\)
is the unique position. With \(Z=(u+i)^2(v+i)^2\), substitution gives
\[
 zr(N_0+L_0)=4P_0/Z,\qquad
 zr(1+b^2)h(N_0-L_0)=-4sP_1/Z,\qquad
 zr(1+b^2)h(N_2-L_2)=4sP_2/Z.                       \tag{75.27}
\]
These identities use (75.25). Original unitarity gives
\(2(N_0+L_0)+(N_2+L_2)=0\). Thus, for \(s\ne0\), all original
flatness equations are equivalent to \(P_0=P_1=P_2=0\) and
\(K(a^2+c^2)=R\).

Before dividing by \(s\), the first numerator is
\(s[Dp-(T+1)q]+bD(1-T)-D^2-2T(T+1)\); the second and third
numerators are their coefficient rows in (75.26) dotted with \((p,q)\),
plus \(s\) times their constant terms. This is a polynomial extension
of (75.27) to \(s=0\). At \(v=-u\), the first reduces to
\(-2u(u-b)(1+u^2)=0\). If \(u=0\), then \(z=r=1\), and the
remaining equation is \(-3bp+(3-2b^2)q=0\). Its intersection with
(75.25) consists of exactly
\[
 (p,q)=\pm\frac{\sqrt R(3-2b^2,3b)}
                        {\sqrt{(3-2b^2)^2+9b^2}},\qquad
 g=(p+iq)/\kappa.                                  \tag{75.28}
\]
These are the two constant canonical rays. If \(u=b\ne0\), the other
two original equations are homogeneous linear equations in \(p,q\)
with coefficient determinant
\(-6b(b^2-1)(b^2+1)^3(b^2+3)\ne0\). They force \(p=q=0\), contrary
to (75.25). Every nonconstant finite ray therefore has \(K>0\).

Write (75.26) as \(M_1(a,c)^T+k_1=0\), where \(M_1\) is a real
\(3\times2\) polynomial matrix and \(k_1\) its constant column.
Put \(F_0=D^2+(T+1)^2\). On \(K>0\), \(F_0>0\) and the first
row is nonzero. Its minors with the second and third rows are
\[
 \det(M_1)_{01}=-Kb(Db-T+3)F_0,\qquad
 \det(M_1)_{02}=3K[-D+b(T+1)]F_0.                  \tag{75.29}
\]
Rank less than two would force
\(D=4b/(1-b^2)\), \(T=(b^2+3)/(1-b^2)\). At that point, with
\(d_1=-k_1\), the augmented consistency minor is
\[
 (M_1)_{00}(d_1)_1-(M_1)_{10}(d_1)_0
          =\frac{384b(b^2-3)(b^2+1)}{(b^2-1)^3}\ne0.        \tag{75.30}
\]
Thus no actual solution has deficient rank.

Define, polynomially in the two real variables \(D,T\),
\[
\begin{gathered}
 G_1=M_1^TM_1,\quad \Delta=\det G_1,\quad
 \eta=-\operatorname{adj}(G_1)M_1^Tk_1,\\
 F=\det[k_1\mid M_1],\qquad
 N=K(\eta_0^2+\eta_1^2)-R\Delta^2.
\end{gathered}
\]
The complete finite nonconstant quotient is
\[
 F=0,\quad N=0,\quad K>0,\quad\Delta>0.             \tag{75.31}
\]
Indeed \(\Delta\) is the sum of squares of the three \(2\times2\)
minors, so \(\Delta>0\) is exactly rank two. In that rank, \(F=0\)
is consistency, its unique solution is \((a,c)=\eta/\Delta\),
and \(N=0\) imposes the circle equation (75.25). Choose
\[
\begin{gathered}
 s=\sqrt K>0,\qquad u=(s+D)/2,\quad v=(s-D)/2,\\
 p=sa,\quad q=sc,\quad g=(p+iq)/\kappa,\qquad
 z=(1+iu)/(1-iu),\quad r=(1+iv)/(1-iv).              \tag{75.32}
\end{gathered}
\]
Then (75.25) and (75.27) give every original input and output modulus.
Conversely every nonconstant finite ray reconstructs this solution.
Changing \(s\) to \(-s\) sends \((u,v,g)\) to \((-v,-u,-g)\),
which is exactly \(\Theta\) followed by dephasing the first coordinate.
The parameters \(D,T\) are unchanged, proving the stated bijection
modulo \(\Theta\). All matrices in (75.31) have at most three rows;
(75.26) completely specifies the polynomial system.

It remains to treat the Cayley poles. If \(z=r=-1\), then the original
norm-sum residual \(N_0+L_0=-8\), impossible. For \(z=-1\),
\(r=(1+iv)/(1-iv)\ne-1\), direct original substitution gives
\[
\begin{aligned}
 p={}&v(b+q)+2v^2+1,\\
 0={}&(v-b)[b^2(v^2+1)+bq(v^2+1)+2bv^3-2v^2-4],\\
 0={}&2b^3v^2+2b^3+7b^2v^3+9b^2v+3bqv^3+3bqv\\
     &\hspace{6mm}+6bv^4+17bv^2-b-3qv^2-3q+8v^3-2v.       \tag{75.33}
\end{aligned}
\]
For \(v\ne b\), the second solves
\[
 q=-\frac{b^2(v^2+1)+2bv^3-2v^2-4}{b(v^2+1)}.
\]
The third equation and the norm circle respectively require \(H=J=0\),
where
\[
\begin{aligned}
 H={}&b^4v^2+b^4+2b^3v^3+3b^3v+10b^2v^2+b^2
                                      +10bv^3+5bv-3v^2-6,\\
 J={}&b^4v^2+b^4+2b^3v^3+2b^2v^4-b^2v^2-5b^2
                                      +2bv^3+4bv+2v^4+8v^2+8.
                                                               \tag{75.34}
\end{aligned}
\]
The determinant of their \(7\times7\) Sylvester matrix is
\[
 \operatorname{Res}_v(H,J)=2b^4(b^2-1)^2(b^2-3)^2(b^4+22b^2+25)
          (9b^8+28b^6-170b^4-612b^2+2025).          \tag{75.35}
\]
Every factor is nonzero on \(0<|b|<1\); the last is at least
\(2025-170-612=1243\). Hence the case \(v\ne b\) is impossible.

For \(v=b\), the third equation in (75.33) instead gives
\[
 q=\frac{b(5b^4+12b^2-1)}{1-b^4},\qquad p=bq+3b^2+1,\qquad
 p^2+q^2-R=\frac{2f(b^2)}{(b^2-1)^2(b^2+1)},
\]
\[
 f(t)=2t^5+33t^4+90t^3+4t-1.                       \tag{75.36}
\]
This polynomial is strictly increasing on \([0,1]\); its signs at
\(0,1\) are opposite, and its unique root \(t_0\) lies in
\((3/20,4/25)\). At exactly \(b=\pm\sqrt{t_0}\), the displayed
\(p,q\) give an actual upper-pole ray with
\[
 z=-1,\qquad r=\frac{1+ib}{1-ib},\qquad
 g_\mathrm{up}=(p+iq)/\kappa.
\]
Substitution into (75.33) and (75.25) proves sufficiency directly.
The lower-pole ray is precisely its dephased \(\Theta\) partner,
\[
 (z,r,g)=\left(\frac{1-ib}{1+ib},-1,-g_\mathrm{up}\right).   \tag{75.37}
\]
This exhausts the poles. For the fixed repeated positions it is one
\(\Theta\) pair; its synchronous permutation union consists of six
rays, since each nonconstant aligned ray has orbit size three and the
two \(\Theta\) orbits are disjoint. Disjointness follows from the
antiunitary projective-fixed-point argument following Corollary 74.2.
The pole pair is a coordinate exception; no orthogonality transition
is implied. \(\square\)

### 75.6. Coverage and the remaining orthogonality problem

**Proof of Theorem 75.1.** If a channel mean vanishes, Theorem 75.2
gives the first class. Otherwise both means are nonzero. If either
channel has three distinct entries, select it as the upper channel,
using \(\Theta\) if necessary, and apply Theorem 75.3. If neither
does, each has a repeated pair. When both channels are nonconstant
and their repeated pairs differ, common phase and synchronous
permutation give exactly (75.18), excluded by Theorem 75.4. If their
pairs agree, the input is of form (75.24). A constant channel also
permits (75.24), by choosing the other channel's repeated pair.
Theorem 75.5 supplies every finite and pole case of this remaining
chart. This proves complete coverage. \(\square\)

**Definition 75.2 (scope of the reduction).** The four-real system keeps
all six root orders; the aligned system keeps both \(\Theta\) choices,
all synchronous permutations and its explicit exceptional parameter.
For a pair of candidate rays, independently selecting channels by
\(\Theta\) is not an orthogonality-preserving operation on just one
member. Both types of cross equation must be retained in the pair
problem, selecting ordinary orthogonality for equal relative \(\Theta\)
parity and the symplectic bilinear equation for opposite parity; they
are not imposed simultaneously on one selected pair.
No pair-spinor implication, finite ray count, arbitrary noncanonical
orthogonal-triple obstruction or whole-branch basis classification is
a consequence asserted by this section. Those questions require joint
constraints across the reconstructed rays, beyond the single-ray
necessity and sufficiency proved here.

## 76. Complete root-free systems for the noncanonical pair problem

### 76.1. Relative antiunitary parity and the remaining implication

Retain the unit-entry input convention of §75 and fix \(0<|b|<1\).
For \(w=(x,y)\), put \(\mu(w)=(\sum x_j,\sum y_j)\in\mathbb C^2\).
Theorem 75.2 makes both entries nonzero for every noncanonical ray.
The following implication remains a separate mathematical question:
\[
 w\perp v\quad\Longrightarrow\quad\mu(w)\perp\mu(v)
 \qquad(w,v\text{ noncanonical common-flat}).                 \tag{76.1}
\]
This section gives exact finite systems equivalent to its failure; it
proves no emptiness assertion for those systems.

The choice of a three-distinct upper channel in Theorem 75.1 records a
\(\Theta\) flag. Simultaneous application of \(\Theta\) preserves
orthogonality, so only the relative flag matters. For selected inputs
\(w=(x,y)\), \(v=(x',y')\), the applicable cross equations and targets are
\[
\begin{array}{c|c}
 \mathcal O=\sum_j(\bar x_jx'_j+\bar y_jy'_j)=0
   &\bar X X'+\bar Y Y'=0\\
 \mathcal S=\sum_j(x_jy'_j-y_jx'_j)=0
   &X Y'-Y X'=0.
\end{array}                                                   \tag{76.2}
\]
Indeed \(w^*\Theta v=-\overline{\mathcal S}\). These are two alternative
systems selected by relative parity, not simultaneous requirements.

### 76.2. Two three-distinct-channel representatives

For one solution of (75.13)–(75.15), use \(q,e,g,c,d\), set
\(t=\sqrt q\), \(E=\bar e\), and define
\[
\begin{aligned}
 f(Z)&=Z^3-3Z^2+3EZ-E/q,\\
 B(Z)&=(Z^2-3Z+3E)/E,\\
 L(Z)&=g+c(Z-1)+d(B(Z)-1),\\
 L^c(Z)&=\bar g+\bar c(B(Z)-1)+\bar d(Z-1).
\end{aligned}                                                   \tag{76.3}
\]
The original upper entries are \(tZ_j\), where the \(Z_j\) are the
three roots of \(f\); the lower entries are \(tL(Z_j)\).
On the strict single-ray domain, \(B(Z_j)=\bar Z_j\) and
\(L^c(Z_j)=\overline{L(Z_j)}\). In particular \(qZ_jB(Z_j)=1\).

Here is an explicit algebra containing every root order. Let
\[
 C=\begin{pmatrix}0&0&E/q\\1&0&-3E\\0&1&3\end{pmatrix},\quad
 X_1=\operatorname{diag}(C,C),\quad
 X_2=\begin{pmatrix}0&-C^2+3C-3EI_3\\I_3&3I_3-C\end{pmatrix},\quad
 X_3=3I_6-X_1-X_2.                                             \tag{76.4}
\]
The matrices commute and each satisfies \(f(X_j)=0\). The quadratic
for the second root is
\[
 X_2^2+(X_1-3I_6)X_2+X_1^2-3X_1+3EI_6=0.
\]
Its two roots are exactly the two roots of \(f\) different from the
selected first root. Since the strict discriminant condition makes all
three roots distinct, this algebra is a product of six copies of
\(\mathbb C\), one for each ordered triple. Equivalently, evaluation in
the basis \(1,Z_1,Z_1^2,Z_2,Z_1Z_2,Z_1^2Z_2\) gives the six distinct
characters. No cyclic-order restriction has been imposed.

For a second quotient point use \(Y_j,B',L'\), with mean ratio \(k\).
Define the \(36\times36\) matrices
\[
\begin{aligned}
 \mathsf O_{gg}&=\sum_{j=1}^3
     [B(X_j)\otimes Y_j+L^c(X_j)\otimes L'(Y_j)],\\
 \mathsf S_{gg}&=\sum_{j=1}^3
     [X_j\otimes L'(Y_j)-L(X_j)\otimes Y_j].
\end{aligned}                                                   \tag{76.5}
\]
Their evaluations are precisely the original cross expressions divided
by \(tt'\), for all 36 pairs of root orders. Thus each determinant
vanishes if and only if some relative order satisfies its cross equation.
Simultaneous permutation invariance also shows that each determinant is
the sixth power of the product over the six relative orders.
The corresponding mean targets, after removing the nonzero factor
\(9tt'\), are
\[
 1+\bar gk=0,\qquad k-g=0.                                    \tag{76.6}
\]
Consequently failure of (76.1) in this case is exactly the union of two
systems: both complete strict single-ray quotients, the applicable
complex determinant equation in (76.5), and a strictly positive squared
modulus of the corresponding expression in (76.6).

### 76.3. A three-distinct-channel representative and an aligned one

Write the aligned input as \((1,1,z;h_a,h_a,h_ar)\), using either its
finite quotient or its explicit pole stratum from Theorem 75.5.
The symbol \(h_a\) is its unit phase. The three possible positions of its
unique coordinate lead to the companion-matrix norms
\[
\begin{aligned}
 \mathsf O_{ga}&=3(1+\bar gh_a)I_3
                +(z-1)B(C)+h_a(r-1)L^c(C),\\
 \mathsf S_{ga}&=3(h_a-g)I_3
                +h_a(r-1)C-(z-1)L(C).
\end{aligned}                                                   \tag{76.7}
\]
Their determinants are products of all three relative-position cross
expressions divided by \(t\). Permuting the two repeated positions only
duplicates values. The exact mean targets are
\[
 (2+z)+\bar gh_a(2+r)=0,\qquad
 h_a(2+r)-g(2+z)=0.                                           \tag{76.8}
\]
The mixed failure systems consist of the two single-ray descriptions,
the relevant determinant equation, and nonzero squared modulus of its
target. Reversing the order of the rays conjugates \(\mathcal O\) or
negates \(\mathcal S\), so introduces no further zero-condition case.

### 76.4. Two aligned representatives and completeness

Write \(w=(1,1,z;g,g,gr)\), \(v=(1,1,Z;k,k,kR)\), where \(R\) here
is a unit phase ratio. The two relative positions are matched or different.
Their cross expressions are
\[
\begin{aligned}
 O_m&=2+\bar zZ+\bar gk(2+\bar rR),\\
 O_d&=1+\bar z+Z+\bar gk(1+\bar r+R),\\
 S_m&=k(2+zR)-g(2+rZ),\\
 S_d&=k(1+R+z)-g(1+Z+r).
\end{aligned}                                                   \tag{76.9}
\]
The respective mean targets are
\[
\begin{aligned}
 (2+\bar z)(2+Z)+\bar gk(2+\bar r)(2+R)&=O_m+2O_d,\\
 (2+z)k(2+R)-g(2+r)(2+Z)&=S_m+2S_d.
\end{aligned}                                                   \tag{76.10}
\]
For each parity and relative position, impose one cross expression to
vanish and the corresponding mean target to have nonzero squared modulus.
Retain both complete aligned quotients, every finite/pole combination,
and every recorded \(\Theta\) choice.

**Theorem 76.1 (complete pair reduction).** At fixed \(0<|b|<1\), failure
of (76.1) is equivalent to nonemptiness of the finite list of systems
(76.5)–(76.10), with the full single-ray conditions of §75. The respective
numbers of free real quotient coordinates are at most eight, six, and
four. Polynomial auxiliary variables retain every square-root identity
and its strict sign, including \(s^2=K,s>0\) in the aligned chart;
the pole parameter retains its defining polynomial and isolating interval.
These auxiliary variables are not additional free coordinates. Every
nonzero denominator and discriminant condition from §75 remains required.

**Proof.** Theorem 75.1 covers every noncanonical ray. The three pair types
exhaust the possible chart pairings. The evaluation-algebra arguments
prove necessity and sufficiency of each determinant zero condition for
some allowed relative order. Equations (76.2), (76.6), (76.8), and (76.10)
compute the actual mean targets. Taking their finite union therefore
preserves both directions, including the exceptional pole strata. ∎

If all these systems were empty, three mutually orthogonal noncanonical
rays would give three nonzero mutually orthogonal vectors in
\(\mathbb C^2\), which is impossible. This remains a conditional consumer;
the reduction itself neither proves (76.1) nor excludes arbitrary triples.

## 77. Exact aligned-pair rigidity at the half parameter

### 77.1. The induced eighteen-ray graph

**Theorem 77.1 (aligned graph at \(b=1/2\)).** There are exactly eighteen
noncanonical common-flat rays that, after a common phase and synchronous
permutation, have the aligned form \((1,1,z;g,g,gr)\). Their induced
orthogonality graph is \(K_{3,3}\sqcup K_{3,3}\sqcup K_{3,3}\).
Every orthogonal pair among them has orthogonal nonzero channel-mean
spinors. In particular they contain no orthogonal triple.

This theorem controls the entire aligned set, including edges between
its different symmetry orbits. It does not control edges involving a
three-distinct-channel ray, or establish a complete ray census at this
parameter. The following model-specific certificate uses the exact
original-equation equivalence in Theorem 75.5.

### 77.2. A complete quintic quotient, including the omitted chart

Set \(b=1/2\) in (75.26), and retain its variables \(D,T,a,c\). Write
\[
 K=D^2+4T=s^2,\quad J=D-2T+6,\quad F_0=D^2+(T+1)^2,\quad
 \kappa=(1/2-i)\sqrt{11/5}.
\]
The input reconstruction is
\[
 u=(s+D)/2,\quad v=(s-D)/2,\quad
 z=\frac{1+iu}{1-iu},\quad r=\frac{1+iv}{1-iv},\quad
 g=\frac{s(a+ic)}{\kappa}.                                   \tag{77.1}
\]
Every nonconstant finite ray has \(K>0\). The pole polynomial (75.36)
does not vanish at \(b^2=1/4\), and the finite \(s=0\) cases are the two
constant canonical rays. Thus these exclusions lose no noncanonical
aligned input at the specified parameter.

The first two rows of the linear system (75.26) have determinant a
nonzero scalar times \(KJF_0\). At \(J=0\), their two augmented minors,
with the right-hand side moved to its own column, are
\[
 33(T-3)(5T^2-22T+37),\qquad
 -\frac{33}{2}(T+1)(5T^2-22T+37).                             \tag{77.2}
\]
The quadratic has discriminant \(-256\), so the two minors cannot both
vanish for real \(T\). Since \(K,F_0>0\), every solution therefore admits
the unique Cramer solutions \(a=A(D,T),c=C_a(D,T)\) from those two rows.
These definitions refer to the printed original polynomials in (75.26),
not to an auxiliary numerical fit.

The primitive numerators of the remaining consistency and norm equations
are the following integer polynomials:
\[
\begin{aligned}
 F={}&-91D^4+228D^3T+286D^3-99D^2T^2-414D^2T-299D^2\\
     &+98DT^3+1284DT^2+674DT-168T^4-104T^3-728T^2-792T,\\
 N={}&109D^6-404D^5T-704D^5+433D^4T^2+2012D^4T+963D^4\\
     &-352D^3T^3-3540D^3T^2-4400D^3T-572D^3\\
     &+460D^2T^4+4786D^2T^3+11710D^2T^2+5206D^2T-130D^2\\
     &-80DT^5-1288DT^4-7096DT^3-7576DT^2-1688DT\\
     &+160T^6+2088T^5+12704T^4+18992T^3+7424T^2-792T.
\end{aligned}                                                   \tag{77.3}
\]
In the allowed chart, \(F=N=0\) is equivalent to the three linear
original equations and \(K(a^2+c^2)=11/4\). Exact elimination gives
\[
\begin{aligned}
 \operatorname{Res}_T(F,N)
   &=4857532416D^4(D-1)(D^2+4)^2(5D^2+16D+64)^2Q(D)f(D),\\
 Q(D)&=4401D^4-26064D^3-6144D^2+139776D+173056,\\
 f(D)&=375110171D^5-8916868590D^4+40906895520D^3\\
     &\hspace{12mm}-77786080640D^2+72033832960D-29539434496.
\end{aligned}                                                   \tag{77.4}
\]
At \(D=0\), the common equations imply \(T(T+1)=0\), so \(K\leq0\).
At \(D=1\), they imply \(4T+1=0\), so \(K=0\). Both quadratic factors
have no real zero. For \(Q\), the signed Euclidean Sturm chain starting
with \(Q,Q'\) has signs \((+,-,+,+,+)\) at \(-\infty\) and
\((+,+,+,-,+)\) at \(+\infty\), hence no real zero.

Define
\[
\begin{aligned}
 p(D)={}&114047721647124035355853D^4
          -2505469425841722936728842D^3\\
        &+7945256094215455341030448D^2
          -9563607328530302248289792D\\
        &+4919733805467906194268928,\\
 c_0={}&673563651603438045093120,\qquad \tau(D)=p(D)/c_0.
\end{aligned}                                                   \tag{77.5}
\]
The exact ideal identity in \(\mathbb Q[D,T]\) is
\[
 \langle F,N,f\rangle=\langle f,c_0T-p(D)\rangle.              \tag{77.6}
\]
It can be reconstructed by rational polynomial division from
(77.3)–(77.5). Consequently \(T=\tau(D)\) at every remaining solution.
The Sturm chain for \(f\) has signs \((-,+,-,-,+,-)\) at \(-\infty\)
and \((+,+,+,-,-,-)\) at \(+\infty\), giving exactly three real roots.
Each of the following rational intervals contains one of them:
\[
 \frac{(172239608,172239609)}{10^8},\qquad
 \frac{(199204026,199204028)}{10^8},\qquad
 \frac{(1843634963,1843634964)}{10^8}.                         \tag{77.7}
\]
Ordinary rational Horner evaluation of \(D^2+4\tau(D)\) and
\(D-2\tau(D)+6\) on these intervals gives, respectively,
\[
 (K,J)\in(4,5)\times(7,8),\quad
 (3/10,2/5)\times(9,10),\quad
 (368,369)\times(10,11).                                     \tag{77.8}
\]
Substitution of \(T=\tau(D)\) and the Cramer solutions into all three
polynomials (75.26) and \(K(a^2+c^2)-11/4\) gives zero modulo \(f\).
Thus all three real roots are admissible and each yields both signs
\(s=\pm\sqrt K\). Sign change is precisely dephased \(\Theta\), while
synchronous permutation supplies three distinct unique-coordinate
positions. Distinct roots remain distinct because \(D=u-v\) is recovered
from the finite Cayley coordinates. This proves the count eighteen.

### 77.3. A characteristic-zero rank certificate for all pairs

The pair exclusion does not rely on a modular point count. Work over
\(\mathbb K=\mathbb Q(i)\). Reduce \(\tau,A(D,\tau),C_a(D,\tau)\) and
\(K(D)=D^2+4\tau(D)\) modulo the monic normalization of \(f\), writing
the reduced Cramer solutions as \(a(D),c(D)\). Define
\[
 \mathcal A=\mathbb K[D,E,s,t]/
  (f(D),f(E),s^2-K(D),t^2-K(E)).                              \tag{77.9}
\]
This algebra has dimension 100. Its ordered basis is
\(s^\epsilon t^\eta D^jE^k\), with \(\epsilon,\eta\in\{0,1\}\),
\(0\leq j,k<5\), indexed by \(50\epsilon+25\eta+5j+k\).
The monic triangular relations prove freeness; simplicity or reality of
roots is not needed for this dimension statement.

In this algebra put
\[
\begin{gathered}
 z(D,s)=\frac{2+i(s+D)}{2-i(s+D)},\qquad
 r(D,s)=\frac{2+i(s-D)}{2-i(s-D)},\\
 G=\frac{st(a(D)-ic(D))(a(E)+ic(E))}{11/4},\\
 O_m=2+\bar z(D,s)z(E,t)+G[2+\bar r(D,s)r(E,t)],\\
 O_d=1+\bar z(D,s)+z(E,t)+G[1+\bar r(D,s)+r(E,t)].             \tag{77.10}
\end{gathered}
\]
Bars here replace \(i\) by \(-i\) while fixing the four algebra variables.
At real reconstructed points these are ordinary conjugates, and
\(O_m,O_d\) are exactly the original overlaps for matched and different
unique-coordinate positions. The denominator \(11/4=|\kappa|^2\)
accounts for the actual input normalization of the lower phase.

All inverses in (77.9)–(77.10) exist and are integral at the split prime
\(73\), with \(i\mapsto27\). The rational constants in \(f,\tau,11/4\)
are units there. With \(f\) monic, the resultants modulo 73 for the
remaining one-variable denominators are
\[
\begin{array}{c|ccccc}
 d&K&J&F_0&(2-iD)^2+K&(2+iD)^2+K\\ \hline
 \operatorname{Res}_D(f,d)&20&34&16&55&37.
\end{array}                                                   \tag{77.11}
\]
Here \(J=D-2\tau+6\), \(F_0=D^2+(\tau+1)^2\). Nonzero resultants give
inverses in the characteristic-zero algebra over the local coefficient
ring, so reduction of the multiplication matrices is legitimate.

Let \(M_m,M_d\) be multiplication by \(O_m,O_d\) in the ordered basis
of (77.9), and use the same principal index set
\[
 I=\{0,\ldots,69\}\cup\{75,\ldots,94\}.
\]
The complete finite certificate is
\[
 \det M_m[I,I]\equiv16,\qquad
 \det M_d[I,I]\equiv64\pmod{73}.                             \tag{77.12}
\]
To reconstruct these matrices, multiply each basis monomial by (77.10),
reduce powers of \(s,t\) with their quadratic relations, and reduce
powers of \(D,E\) with the monic quintic. Inverses use the one-variable
Euclidean algorithm justified by (77.11). Thus (77.3)–(77.12), together
with the two printed original rows (75.26), determine every matrix entry
and every denominator; the certificate has no numerical-search or
unpublished-data premise. Each characteristic-zero rank is at least 90.

### 77.4. Identifying the entire overlap ideal

Let \(\mathcal B=\mathbb K[D,s]/(f(D),s^2-K(D))\), of dimension ten.
The substitution
\[
 \varphi:\mathcal A\longrightarrow\mathcal B,\qquad
 E\longmapsto D,\quad t\longmapsto-s                         \tag{77.13}
\]
is surjective. The exact norm identity from §77.2 implies
\(\varphi(G)=-1\), and the phase formulas give
\[
 z(D,-s)=\bar r(D,s),\qquad r(D,-s)=\bar z(D,s).
\]
Hence \(\varphi(O_m)=\varphi(O_d)=0\). The image of multiplication by
either overlap lies in the 90-dimensional space \(\ker\varphi\).
The lower rank bounds (77.12) therefore prove equality of ideals:
\[
 (O_m)=\ker\varphi=(O_d).                                    \tag{77.14}
\]
In particular \(E-D\) and \(t+s\) belong to either overlap ideal.
Any complex evaluation with \(O_m=0\) or \(O_d=0\) must consequently
have \(E=D,t=-s\). This is a characteristic-zero conclusion obtained
from a modular lower rank bound and an exact matching upper rank bound.

For every real quintic root, the opposite signs give zero overlap at all
three-by-three pairs of positions, by the same identities. Equal signs
cannot give an edge because \(s\ne0\). Distinct roots cannot give an edge
by (77.14). The induced graph is therefore exactly three copies of
\(K_{3,3}\). Finally, synchronous permutations preserve channel sums and
\(\Theta\) sends a spinor \((X,Y)\) to \((-\bar Y,\bar X)\), orthogonal
to it. Division of the input vectors by \(\sqrt6\) multiplies overlaps
by \(1/6\), preserving their zeros. This proves Theorem 77.1. ∎

The generic–generic and generic–aligned failure systems of §76 remain
unresolved. Neither this induced graph nor the pair reduction supplies
an arbitrary-triple or whole-branch no-quartet conclusion.

[Continue with the exact half-parameter census and all-pair rigidity in §§78–80](MUB_SIX_FOURTH_BASIS_THEORY_CONTINUATION_III.md).
