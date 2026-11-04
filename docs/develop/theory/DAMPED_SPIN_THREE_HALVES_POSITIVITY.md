# Exact universal positivity for the damped spin-three-halves distribution

## 1. The fixed distribution and its conventions

**Definition 1.1 (States and magnetic coordinates).** Let $\mathcal H=\mathbb C^4$ with orthonormal basis $e_0,e_1,e_2,e_3$, in descending magnetic order

$$
m_i=\frac32-i\qquad(0\leq i\leq3).
$$

A density matrix is a complex matrix $\rho$ satisfying $\rho=\rho^\dagger$, $v^\dagger\rho v\geq0$ for every complex vector $v$, and $\operatorname{tr}\rho=1$. Write $\mathcal D$ for all such matrices. In particular, neither real entries nor diagonal form are required. This is the positive-semidefinite, trace-one definition in the [density supplier](https://github.com/the-omega-institute/trureturing/blob/84f79a3dabe3c6ee4b66aad17b6823a6c89d77d2/D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.lean), with its [mathematical description](https://github.com/the-omega-institute/trureturing/blob/84f79a3dabe3c6ee4b66aad17b6823a6c89d77d2/Blueprint/D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.scribe.cs). No channel or relative-entropy assertion from those sources is assumed.

The spin and ordering parameters throughout this volume are $J=3/2$ and $\sigma=1$. The distribution is that of D. C. Brody, E.-M. Graefe and R. Melanathuru, [*Phase-space measurements and decoherence for angular momentum systems*, arXiv:2605.02696v1](https://arxiv.org/abs/2605.02696v1), equations (12), (13), (35), (36), (44) and footnote 1. The [convention supplier](https://github.com/the-omega-institute/trureturing/blob/84f79a3dabe3c6ee4b66aad17b6823a6c89d77d2/Library/QuantumStates/brodygraefemelanathuru2026phasespace.md), [complete tensor and harmonic supplier](https://github.com/the-omega-institute/trureturing/blob/84f79a3dabe3c6ee4b66aad17b6823a6c89d77d2/D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.lean), and its [mathematical description](https://github.com/the-omega-institute/trureturing/blob/84f79a3dabe3c6ee4b66aad17b6823a6c89d77d2/Blueprint/D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.scribe.cs) fix the literal factorial and associated-Legendre conventions used below.

**Definition 1.2 (Racah coefficients, tensors and multipoles).** For nonnegative half-integers $j_1,j_2,j$ and admissible magnetic indices $m_1,m_2,m$, put $C^{jm}_{j_1m_1j_2m_2}=0$ unless $m=m_1+m_2$, the triangle inequalities hold, and $j_1+j_2+j$ is an integer. Magnetic admissibility means $-j_a\leq m_a\leq j_a$ and $j_a-m_a$ is an integer, and likewise for $j,m$. On the admissible indices define

$$
\begin{aligned}
C^{jm}_{j_1m_1j_2m_2}
={}&\left[
\frac{(2j+1)(j+j_1-j_2)!(j-j_1+j_2)!(j_1+j_2-j)!}
 {(j_1+j_2+j+1)!}\right.\\
&\left.\hspace{8mm}\cdot
(j+m)!(j-m)!(j_1+m_1)!(j_1-m_1)!
(j_2+m_2)!(j_2-m_2)!
\right]^{1/2}\\
&\cdot\sum_z\frac{(-1)^z}
 {z!(j_1+j_2-j-z)!(j_1-m_1-z)!(j_2+m_2-z)!
 (j-j_2+m_1+z)!(j-j_1-m_2+z)!}.
\end{aligned}
$$

The sum is over integers $0\leq z\leq j_1+j_2-j$ for which every factorial argument is nonnegative; other terms are omitted. Square roots are nonnegative real square roots. This is the Racah convention of the tensor supplier in Definition 1.1: its six integer arguments are respectively $2j_1,2m_1,2j_2,2m_2,2j,2m$. All divisions by two in that supplier therefore have integral values on these admissible arguments. No factorial of a negative integer contributes.

For $0\leq L\leq3$, $-L\leq k\leq L$, set

$$
(T_{Lk})_{ij}=\sqrt{\frac{2L+1}{4}}\,
 C^{\frac32,m_i}_{\frac32,m_j,L,k},
\qquad
\rho_{Lk}=\operatorname{tr}(T_{Lk}^{\dagger}\rho).
$$

Rows are $m_i$ and columns are $m_j$. These are exactly equations (12) and (13) of arXiv:2605.02696v1, with the adjoint in the coefficient definition.

**Definition 1.3 (Literal harmonics on real angles).** For a nonnegative integer $L$, let

$$
S_L(u)=\sum_{r=0}^L(-1)^r\binom Lr\binom{L+r}{L}u^r,
\qquad P_L(x)=S_L\left(\frac{1-x}{2}\right).
$$

This is the shifted-polynomial definition used in the harmonic supplier. Its coefficient definition is also given in [the pinned shifted-Legendre source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean). For $0\leq k\leq L$ define

$$
A_{Lk}(x)=(-1)^k\bigl(\sqrt{1-x^2}\bigr)^k P_L^{(k)}(x),
\qquad
Y_{Lk}(\theta,\phi)=
\sqrt{\frac{(2L+1)(L-k)!}{(L+k)!}}\,
A_{Lk}(\cos\theta)e^{ik\phi}.
$$

For $k>0$ define

$$
Y_{L,-k}(\theta,\phi)=(-1)^k\overline{Y_{Lk}(\theta,\phi)}.
$$

Orders outside $[-L,L]$ are zero. Both angles range over all of $\mathbb R$. In particular, $Y_{00}=1$, and the normalization is $\sqrt{4\pi}$ times the Condon–Shortley harmonic, as in footnote 1 of the original paper. The sign in $A_{Lk}$ is part of the definition and is not inserted a second time.

Write

$$
x=\cos\theta,\qquad s=\sqrt{1-x^2}=|\sin\theta|,\qquad z=e^{i\phi}.
$$

Thus $s\geq0$, $x^2+s^2=1$, and $|z|=1$, for every real pair of angles. Equivalently, $\beta=\arccos x\in[0,\pi]$ has $\cos\beta=x$ and $\sin\beta=s$. The literal harmonics at $(\theta,\phi)$ equal those at $(\beta,\phi)$ by their definitions, including when $\sin\theta<0$. These observations do not assume a signed-sine continuation of a rotation formula.

**Definition 1.4 (Damped distribution and universal positivity).** For finite $\gamma>0$, finite $t\geq0$, and $\rho\in\mathcal D$, put

$$
\begin{aligned}
r_L&=\frac{\binom3L}{\binom{4+L}{L}},\qquad q=e^{-\gamma t},\\
F_\gamma(\rho;\theta,\phi,t)
&=\frac12\sum_{L=0}^3\sum_{k=-L}^L
 e^{-\gamma L(L+1)t/2}r_L^{-1/2}
 \rho_{Lk}\overline{Y_{Lk}(\theta,\phi)}.
\end{aligned}
$$

The factor $1/2=(2J+1)^{-1/2}$ is the $a_J$ of original equations (35)–(36). This formula is precisely equation (44), retaining its conjugated harmonic and its time variable. Let $\mathcal P(\gamma,t)$ mean that this complex expression is real and nonnegative for every $\rho\in\mathcal D$ and every real $\theta,\phi$. Positivity here refers only to this specified function; it is not a definition of separability or of a physical classicality property.

## 2. The exact universal criterion

**Theorem 2.1 (Sharp fixed-spin criterion).** Define

$$
p(u)=1-3u+5u^3-7u^6.
$$

There is a unique $q_\star\in(0,1)$ with $p(q_\star)=0$, and it satisfies the exact inequalities

$$
\frac12<q_\star<\frac59.
$$

For every finite $\gamma>0$ and finite $t\geq0$, the distribution in Definition 1.4 is real for all states and all real observation angles, and

$$
\mathcal P(\gamma,t)
\quad\Longleftrightarrow\quad
p(e^{-\gamma t})\geq0
\quad\Longleftrightarrow\quad
 e^{-\gamma t}\leq q_\star
\quad\Longleftrightarrow\quad
 t\geq T_\gamma:=\frac{-\log q_\star}{\gamma}.
$$

The threshold $T_\gamma$ is positive, finite, and attained. At every observation angle there is an actual pure density matrix giving a negative value at every $0\leq t<T_\gamma$, and an actual pure density matrix giving zero at $t=T_\gamma$. For every finite $t>T_\gamma$, every density matrix gives a strictly positive value at every angle. On $t\geq T_\gamma$ the minimum over all states at any fixed angle, and hence also over all states and angles, is exactly $p(e^{-\gamma t})/4$.

The polynomial for the lowest-weight state at the north pole already occurs in the [published coefficient-condition refutation and its root discussion](https://github.com/the-omega-institute/trureturing/blob/84f79a3dabe3c6ee4b66aad17b6823a6c89d77d2/Problems/brody-graefe-melanathuru-2026-damped-kernel-positivity.md). The statement here quantifies over the full complex density space and all literal real-angle observations. The tensor covariance and orthogonality underlying spin phase-space kernels are established background, including equations (3)–(5) of arXiv:2605.02696v1. The finite correspondence and the complete state-space implication needed here are proved below.

Proof. We first evaluate all tensor entries needed for the full matrix, then all harmonics, and finally construct an orthonormal eigenbasis of the resulting observation matrix.

*The factorial calculation.* Magnetic conservation forces $k=j-i$. With $i=j-k$, substitution in Definition 1.2 gives

$$
(T_{Lk})_{j-k,j}=\sqrt{D_{Lkj}}\,\Sigma_{Lkj},
$$

where

$$
\begin{aligned}
c_L&=\frac{(2L+1)(3-L)!(L!)^2}{(L+4)!},\\
D_{Lkj}&=c_L(3-j+k)!(j-k)!(3-j)!j!(L+k)!(L-k)!,\\
\Sigma_{Lkj}
&=\sum_{\max(0,k,L+j-3)\leq v\leq\min(L,j,L+k)}
 \frac{(-1)^v}{v!(L-v)!(j-v)!(L+k-v)!(3-L-j+v)!(v-k)!}.
\end{aligned}
$$

Here $0\leq j-k,j\leq3$. In particular

$$
(c_0,c_1,c_2,c_3)
=\left(\frac{6}{24},\frac{6}{120},\frac{20}{720},\frac{252}{5040}\right)
=\left(\frac14,\frac1{20},\frac1{36},\frac1{20}\right).
$$

The following table displays every nonnegative-order entry. Tuples in each row follow the indicated increasing values of $j$. The column for $\Sigma$ displays the individual live summands, so zero entries arising by cancellation are included.

| $L,k$ | $j$ | $D_{Lkj}$ | $\Sigma_{Lkj}$ |
| --- | --- | --- | --- |
| $0,0$ | $0,1,2,3$ | $(9,1,1,9)$ | $(1/6,1/2,1/2,1/6)$ |
| $1,0$ | $0,1,2,3$ | $(9/5,1/5,1/5,9/5)$ | $(1/2,1-1/2,1/2-1,-1/2)$ |
| $1,1$ | $1,2,3$ | $(6/5,2/5,6/5)$ | $(-1/2,-1,-1/2)$ |
| $2,0$ | $0,1,2,3$ | $(4,4/9,4/9,4)$ | $(1/4,1/4-1,-1+1/4,1/4)$ |
| $2,1$ | $1,2,3$ | $(2,2/3,2)$ | $(-1/2,-1/2+1/2,1/2)$ |
| $2,2$ | $2,3$ | $(8,8)$ | $(1/4,1/4)$ |
| $3,0$ | $0,1,2,3$ | $(324/5,36/5,36/5,324/5)$ | $(1/36,-1/4,1/4,-1/36)$ |
| $3,1$ | $1,2,3$ | $(144/5,48/5,144/5)$ | $(-1/12,1/4,-1/12)$ |
| $3,2$ | $2,3$ | $(72,72)$ | $(1/12,-1/12)$ |
| $3,3$ | $3$ | $(1296)$ | $(-1/36)$ |

For example, for $L=2,k=1,j=2$, the admissible indices are $v=1,2$; their denominators are both $2$, their signs are opposite, and the square-root prefactor is $\sqrt{2/3}$. More generally, the displayed limits give all and only the live terms: the lower limits come from $v!$, $(v-k)!$ and $(3-L-j+v)!$, and the upper limits from the other three factorials. Thus the table exhausts the factorial calculation, rather than discarding any entries by a symmetry assumption.

For negative orders, exchange $i$ and $j$, replace $k$ by $-k$, and make the substitution $v'=v-k$ in the sum. The square-root prefactor is unchanged. The six factorials in the new denominator are the old six in a different order, and $(-1)^{v'}=(-1)^k(-1)^v$. The admissible terms correspond bijectively, since all six nonnegativity conditions correspond. Consequently

$$
T_{L,-k}=(-1)^kT_{Lk}^{\dagger}.
$$

All the entries are real. Taking the square roots and multiplying by the table's sums yields the entire tensor family in the following compact form; an order-$k$ tuple gives the entries $(T_{Lk})_{j-k,j}$ in increasing $j$, and all other entries are zero:

$$
\begin{array}{c|c|c}
L&k&\text{entry tuple}\\ \hline
0&0&(1,1,1,1)/2\\
1&0&(3,1,-1,-3)/(2\sqrt5)\\
1&1&(-\sqrt3,-2,-\sqrt3)/\sqrt{10}\\
2&0&(1,-1,-1,1)/2\\
2&1&(-1,0,1)/\sqrt2\\
2&2&(1,1)/\sqrt2\\
3&0&(1,-3,3,-1)/(2\sqrt5)\\
3&1&(-1,\sqrt3,-1)/\sqrt5\\
3&2&(1,-1)/\sqrt2\\
3&3&(-1)
\end{array}
$$

These entries also prove the expansion identity in original equation (13). Different orders have disjoint matrix diagonals and hence zero Hilbert–Schmidt inner product. For order zero, the unnormalized tuples

$$
(1,1,1,1),\quad(3,1,-1,-3),\quad
(1,-1,-1,1),\quad(1,-3,3,-1)
$$

have squared norms $4,20,4,20$. Their six pairwise dot products are respectively

$$
3+1-1-3,\quad1-1-1+1,\quad1-3+3-1,
\quad3-1+1-3,\quad3-3-3+3,\quad1+3-3-1,
$$

all zero. For order one the squared unnormalized norms are $3+4+3=10$, $1+1=2$, and $1+3+1=5$; the cross numerators are $\sqrt3-\sqrt3$, $\sqrt3-2\sqrt3+\sqrt3$, and $1-1$. For order two the vectors $(1,1)$ and $(1,-1)$ have squared norm $2$ and zero dot product; order three has its single unit entry. The adjoint identity proves the same facts for negative orders. There are $4+2\cdot3+2\cdot2+2\cdot1=16$ orthonormal matrices, so they are a basis of all complex $4$ by $4$ matrices. Therefore

$$
\rho=\sum_{L=0}^3\sum_{k=-L}^L\rho_{Lk}T_{Lk}
$$

with exactly the coefficients in Definition 1.2. In particular this expansion does not restrict the allowed densities. For Hermitian $\rho$, finite-sum conjugation and cyclicity of trace give

$$
\overline{\rho_{Lk}}
=\operatorname{tr}(\rho T_{Lk})
=(-1)^k\rho_{L,-k}.
$$

Cyclicity here is simply $\sum_{i,j}A_{ij}B_{ji}=\sum_{i,j}B_{ij}A_{ji}$, so the adjoint placement introduces no extra assumption.

*The harmonic calculation.* Directly from the binomial definition in Definition 1.3,

$$
\begin{aligned}
S_0(u)&=1,\\
S_1(u)&=1-2u,\\
S_2(u)&=1-6u+6u^2,\\
S_3(u)&=1-12u+30u^2-20u^3.
\end{aligned}
$$

Indeed their coefficient tuples are respectively $(1)$, $(1,-1\cdot1\cdot2)$, $(1,-1\cdot2\cdot3,1\cdot1\cdot6)$ and $(1,-1\cdot3\cdot4,1\cdot3\cdot10,-1\cdot1\cdot20)$. Substituting $u=(1-x)/2$ yields

$$
P_0=1,\quad P_1=x,\quad
P_2=\frac{3x^2-1}{2},\quad
P_3=\frac{5x^3-3x}{2}.
$$

For example the last substitution is $1-6(1-x)+(15/2)(1-2x+x^2)-(5/2)(1-3x+3x^2-x^3)$, whose constant and quadratic coefficients vanish and whose remaining terms are $(5x^3-3x)/2$. Write $Y_{Lk}=h_{Lk}z^k$ for $k\geq0$. Every derivative and normalization factor used to obtain $h_{Lk}$ is displayed below; the multiplier of the derivative is $(-s)^k$ times the square root in the third column.

| $L,k$ | $P_L^{(k)}(x)$ | $(2L+1)(L-k)!/(L+k)!$ | $h_{Lk}$ |
| --- | --- | --- | --- |
| $0,0$ | $1$ | $1$ | $1$ |
| $1,0$ | $x$ | $3$ | $\sqrt3x$ |
| $1,1$ | $1$ | $3/2$ | $-\sqrt{3/2}s$ |
| $2,0$ | $(3x^2-1)/2$ | $5$ | $\sqrt5(3x^2-1)/2$ |
| $2,1$ | $3x$ | $5/6$ | $-\sqrt{15/2}xs$ |
| $2,2$ | $3$ | $5/24$ | $\sqrt{15/8}s^2$ |
| $3,0$ | $(5x^3-3x)/2$ | $7$ | $\sqrt7(5x^3-3x)/2$ |
| $3,1$ | $(15x^2-3)/2$ | $7/12$ | $-\sqrt{21}(5x^2-1)s/4$ |
| $3,2$ | $15x$ | $7/120$ | $\sqrt{105/8}xs^2$ |
| $3,3$ | $15$ | $7/720$ | $-\sqrt{35}s^3/4$ |

These follow by differentiation of the four displayed polynomials. For instance, the last three square-root products use $9(7/12)/4=21/16$, $225(7/120)=105/8$ and $225(7/720)=35/16$. Thus all phases, square roots, and the nonnegative value of $s$ come from the literal definitions. Negative-order values follow from their defining conjugation identity for every real angle.

*The observation operator.* Set

$$
B_L=\sum_{k=-L}^LT_{Lk}^{\dagger}\overline{Y_{Lk}},
\qquad
K(q;x,s,z)=\frac12\sum_{L=0}^3q^{L(L+1)/2}r_L^{-1/2}B_L.
$$

All sums are finite, and direct substitution in Definition 1.4 gives

$$
F_\gamma(\rho;\theta,\phi,t)=\operatorname{tr}(\rho K(q;x,s,z)).
$$

The two conjugation identities give $T_{L,-k}Y_{L,-k}=T_{Lk}^{\dagger}\overline{Y_{Lk}}$ term by term. Reindexing the sum therefore gives

$$
B_L=\sum_{k=-L}^LT_{Lk}Y_{Lk}=B_L^{\dagger}.
$$

In particular, above the main diagonal its entries are exactly the products of the two positive-order tables, with phase $z^k$; below it they are their complex conjugates. This proves Hermiticity using the actual conjugation in (44). At $q=1$, $K$ is exactly the $\sigma=1$ kernel in original equation (36), and its trace pairing is equation (35). For arbitrary $q=e^{-\gamma t}$ the same trace pairing includes exactly the original multipole damping in (44).

Introduce the following Hermitian matrix, whose displayed upper entries fix the azimuthal sign:

$$
X=\begin{pmatrix}
3x/2&\sqrt3sz/2&0&0\\
\sqrt3s\bar z/2&x/2&sz&0\\
0&s\bar z&-x/2&\sqrt3sz/2\\
0&0&\sqrt3s\bar z/2&-3x/2
\end{pmatrix}.
$$

Put $Q=X^2-5I/4$ and $R=(20X^3-41X)/6$. The tables imply the polynomial identities

$$
B_0=I/2,\qquad
B_1=\sqrt{3/5}X,\qquad
B_2=\frac{\sqrt5}{2}Q,\qquad
B_3=\frac{\sqrt{7/5}}2R.
$$

For completeness, these matrix identities can be obtained without invoking tensor rotation. Let $d_i=(3/2-i)x$, let $a_1=\sqrt3s/2$, $a_2=s$, $a_3=\sqrt3s/2$, and let $a_0=a_4=0$. The first upper diagonal of $X$ is $a_jz$. Its powers have the entries

$$
\begin{aligned}
(X^2)_{ii}&=d_i^2+a_i^2+a_{i+1}^2,\\
(X^2)_{j-1,j}&=a_j(d_{j-1}+d_j)z,\\
(X^2)_{j-2,j}&=a_{j-1}a_jz^2,\\
(X^3)_{ii}&=d_i^3+a_i^2(2d_i+d_{i-1})
                    +a_{i+1}^2(2d_i+d_{i+1}),\\
(X^3)_{j-1,j}&=a_j\bigl(d_{j-1}^2+d_{j-1}d_j+d_j^2
                +a_{j-1}^2+a_j^2+a_{j+1}^2\bigr)z,\\
(X^3)_{j-2,j}&=a_{j-1}a_j(d_{j-2}+d_{j-1}+d_j)z^2,\\
(X^3)_{0,3}&=a_1a_2a_3z^3.
\end{aligned}
$$

Terms with indices outside $0,1,2,3$ in the diagonal formula are omitted. Every formula is obtained by listing the paths of length two or three through adjacent or equal indices in matrix multiplication. Substituting $s^2=1-x^2$ gives the following entire upper halves, with the phase $z^k$ suppressed in the order-$k$ row. Write $P=(5x^3-3x)/2$.

| order $k$ | entries of $Q$ | entries of $R$ |
| --- | --- | --- |
| $0$ | $(3x^2-1)(1,-1,-1,1)/2$ | $P(1,-3,3,-1)$ |
| $1$ | $xs(\sqrt3,0,-\sqrt3)$ | $s(5x^2-1)(\sqrt3/2,-3/2,\sqrt3/2)$ |
| $2$ | $\sqrt3s^2(1,1)/2$ | $5\sqrt3xs^2(1,-1)/2$ |
| $3$ | $(0)$ | $(5s^3/2)$ |

To spell out the cubic reductions, the first two diagonal entries of $X^3$ are $(6x^3+21x)/8$ and $(19x-18x^3)/8$; the last two are their negatives in reverse order. For order one, the bracket in the displayed cubic formula is $(6x^2+7)/4$ at either outer edge and $(10-9x^2)/4$ at the middle edge. Thus $(20X^3-41X)/6$ multiplies the outer edges of $X$ by $5x^2-1$ and the middle edge by $-3(5x^2-1)/2$. For order two the sum of the three diagonals is $3x/2$ or $-3x/2$, and for order three $a_1a_2a_3=3s^3/4$. These give every entry in the last column. Multiplication by $\sqrt5/2$ or $\sqrt{7/5}/2$ reproduces the products of the tensor and harmonic entries. Order zero and order one give $B_0,B_1$ immediately from their tables. Lower entries follow by Hermiticity, completing all four identities.

The binomial ratios and exponents are, explicitly,

$$
(r_0,r_1,r_2,r_3)
=\left(\frac11,\frac35,\frac3{15},\frac1{35}\right)
=\left(1,\frac35,\frac15,\frac1{35}\right),
\qquad
\left(\frac{L(L+1)}2\right)_{L=0}^3=(0,1,3,6).
$$

It follows, with no coefficient inequality substituted for the distribution, that

$$
K(q;x,s,z)=\frac14I+\frac q2X
  +\frac{5q^3}{4}\left(X^2-\frac54I\right)
  +\frac{7q^6}{24}(20X^3-41X).
\tag{1}
$$

*An orthonormal basis for every observation.* We now determine the whole spectrum of (1). This also supplies an explicit convention correspondence in place of any unproved rotation formula. On $\mathbb C^2$ with basis $f_0,f_1$, define

$$
H=\begin{pmatrix}x&sz\\s\bar z&-x\end{pmatrix},
\qquad
A=\frac12(H\otimes I\otimes I+I\otimes H\otimes I+I\otimes I\otimes H).
$$

Let $E_j$ be the normalized sum of the $\binom3j$ tensor words with exactly $j$ occurrences of $f_1$. The four $E_j$ form an orthonormal basis of the symmetric subspace of $(\mathbb C^2)^{\otimes3}$: permutation-invariant coefficients are constant on each of the four sets of words, and these sets are disjoint. Identify $e_j$ with $E_j$.

The diagonal entry of $A$ on $E_j$ is $(3/2-j)x$. Between $E_j$ and $E_{j-1}$, changing one $f_1$ to $f_0$ produces $j\binom3j$ pairs of words, each with coefficient $sz/2$. After normalization the coefficient is

$$
\frac{sz}{2}\frac{j\binom3j}{\sqrt{\binom3j\binom3{j-1}}}
=\frac{sz}{2}\sqrt{j(4-j)}.
$$

All other off-diagonal entries vanish except the conjugate ones. Thus the restriction of $A$ is exactly the matrix $X$, including the phase $z$ above the diagonal and the descending order. The tensor product is only a construction of this matrix's basis; it imposes no restriction on $\rho\in\mathcal D$.

Set

$$
a=\sqrt{\frac{1+x}{2}},\qquad b=\sqrt{\frac{1-x}{2}},
\qquad
\nu_+=\begin{pmatrix}a\\b\bar z\end{pmatrix},\qquad
\nu_-=\begin{pmatrix}-bz\\a\end{pmatrix}.
$$

Then $a^2+b^2=1$, $a^2-b^2=x$, and $2ab=s$. Consequently

$$
xa+sb=a,\qquad sa-xb=b.
$$

These identities hold also when $a=0$ or $b=0$, since they follow by substituting $x=a^2-b^2$ and $s=2ab$, without division. Direct multiplication now gives $H\nu_+=\nu_+$ and $H\nu_-=-\nu_-$; their norms are one and their inner product is zero. For $j=0,1,2,3$, let $V_j$ be the normalized symmetric sum of tensor words with $j$ copies of $\nu_-$ and $3-j$ copies of $\nu_+$. Tensor words in these two orthonormal vectors are themselves orthonormal, so the four $V_j$ are orthonormal. They belong to the symmetric subspace and span it, since its dimension is four. Each word has $A$-eigenvalue $3/2-j$. Under the identification above, their images $v_j\in\mathbb C^4$ therefore form an orthonormal basis satisfying

$$
Xv_j=(3/2-j)v_j.
$$

This establishes the full angle-independent spectrum, including $s=0$ and every real $\phi$. In particular, the matrix with columns $v_j$ is unitary and conjugates $\operatorname{diag}(3/2,1/2,-1/2,-3/2)$ to the actual $X$. No conventional rotation matrix is assumed.

*The full-state bridge.* Applying (1) to this basis gives the following four eigenvalues of $K$, indexed in the same order:

$$
\begin{aligned}
\lambda_0(q)&=\frac{1+3q+5q^3+7q^6}{4},\\
\lambda_1(q)&=\frac{1+q-5q^3-21q^6}{4},\\
\lambda_2(q)&=\frac{1-q-5q^3+21q^6}{4},\\
\lambda_3(q)&=\frac{1-3q+5q^3-7q^6}{4}.
\end{aligned}
\tag{2}
$$

Indeed $(m^2-5/4)$ has values $(1,-1,-1,1)$, while $(20m^3-41m)$ has values $(6,-18,18,-6)$ at $m=(3/2,1/2,-1/2,-3/2)$. Inserting these two tuples and $q m/2$ into (1) produces each coefficient in (2).

For any complex density $\rho$, define $w_j=v_j^\dagger\rho v_j$. Positivity gives $w_j\geq0$ as real numbers. The identity $\sum_jv_jv_j^\dagger=I$ and the trace-one hypothesis give $\sum_jw_j=1$. Expanding the trace in this basis yields exactly

$$
F_\gamma(\rho;\theta,\phi,t)=\sum_{j=0}^3\lambda_j(q)w_j.
\tag{3}
$$

This proves real-valuedness for every allowed density, not merely a statement about real parts. It also proves that the minimum and maximum over all densities at a fixed angle are respectively the smallest and largest of (2): every convex combination lies between them, and $\rho=v_jv_j^\dagger$ attains the corresponding endpoint. These rank-one matrices are actual densities because, for every $u\in\mathbb C^4$,

$$
u^\dagger(v_jv_j^\dagger)u=|v_j^\dagger u|^2\geq0,
\qquad \operatorname{tr}(v_jv_j^\dagger)=v_j^\dagger v_j=1.
$$

Thus nonnegativity for the full state space at any observation is equivalent to nonnegativity of all four numbers (2). In particular, no coefficientwise comparison or restriction to a selected family of densities has been used as a sufficiency argument.

*The scalar signs.* For $0\leq u\leq1$ put

$$
h(u)=1-5u^2+14u^5,\qquad g(u)=2-5u^2-7u^5.
$$

We have $p'(u)=-3h(u)$. To see $h>0$ on this entire interval, its derivative is

$$
h'(u)=10u(7u^3-1).
$$

Its minimum occurs at $r=7^{-1/3}$, where $h(r)=1-3r^2$. This is positive: $(3r^2)^3=27/49<1$, and $3r^2\geq0$. Monotonicity on either side of $r$ proves $h(u)\geq h(r)>0$, including both endpoints. It follows that $p$ is strictly decreasing on $[0,1]$. Since $p(0)=1$ and $p(1)=-4$, continuity and strict monotonicity give the unique root $q_\star$. The rational evaluations

$$
p(1/2)=\frac1{64}>0,\qquad
p(5/9)=\frac{531441-885735+455625-109375}{531441}
       =-\frac{8044}{531441}<0
$$

give its stated exact bounds. These determine the root without a numerical approximation.

For $0\leq u\leq5/9$, monotonicity of $u^2$ and $u^5$ gives

$$
g(u)\geq g(5/9)
=\frac{118098-91125-21875}{59049}
=\frac{5098}{59049}>0.
$$

Direct subtraction of the numerators in (2) gives

$$
4\lambda_1(u)=p(u)+2ug(u),\qquad
4\lambda_2(u)=p(u)+2uh(u),\qquad
4\lambda_0(u)-p(u)=6u+14u^6.
\tag{4}
$$

If $0<u\leq q_\star$, then $p(u)\geq0$, $g(u)>0$, and $h(u)>0$, so $\lambda_0,\lambda_1,\lambda_2$ are strictly larger than $\lambda_3=p(u)/4$. The latter is positive for $u<q_\star$ and zero at $q_\star$. At $u=0$ all four eigenvalues are $1/4$. If $q_\star<u\leq1$, then $\lambda_3=p(u)/4<0$. Equations (3)–(4) prove the exact necessary-and-sufficient criterion on the full interval of $q$ and the claimed exact minimum on its nonnegative portion.

Finally, for finite $\gamma>0$, the map $t\mapsto q=e^{-\gamma t}$ decreases continuously and strictly from $1$ to $0$ as $t$ ranges from $0$ to infinity. Since $0<q_\star<1$, $T_\gamma=-\log(q_\star)/\gamma$ is strictly positive and finite, and $q\leq q_\star$ is equivalent to $t\geq T_\gamma$.

For a concrete actual-state attainment at each angle, the eigenvector $v_3$ is the image of $\nu_-^{\otimes3}$ and has coordinates

$$
(v_3)_j=\sqrt{\binom3j}(-bz)^{3-j}a^j\qquad(0\leq j\leq3).
$$

It is normalized by the binomial identity $(a^2+b^2)^3=1$. The density $v_3v_3^\dagger$ gives exactly $p(q)/4$, hence a negative value for every earlier time and zero at the threshold. At $\theta=0$ it is simply $e_3e_3^\dagger$, with $\phi$ arbitrary; in particular its value at the original-domain point $t=0$ is $p(1)/4=-1$. At later finite times all four eigenvalues are strictly positive, and (3) makes every density's value strictly positive. This proves every assertion. $\square$

## 3. Damping rates, zero damping and limits

**Theorem 3.1 (Rate dependence and finite-product limits).** Keep the definitions of Section 1. Let $c=-\log q_\star$, so $c>0$ is finite. For positive finite rates,

$$
T_\gamma=\frac c\gamma,
\qquad
T_{a\gamma}=\frac{T_\gamma}{a}\quad(a>0),
\qquad
\frac{9}{5}<e^c<2.
$$

Consequently $T_\gamma\to+\infty$ as $\gamma\downarrow0$ and $T_\gamma\to0$ as $\gamma\to+\infty$. These limits of thresholds do not put either infinite rate or infinite time in the original domain.

For finite $\gamma\geq0$ and finite $t\geq0$ the same formula defining $F$ is well-defined. At zero damping it fails universal positivity at every finite time, and its infinite-time limit is still that same undamped function. For a fixed positive rate the infinite-time limit, and for a fixed positive time the infinite-rate limit, are both the constant function $1/4$, uniformly over all $\rho\in\mathcal D$ and all real angles. At fixed $t=0$, however, the infinite-rate limit is the undamped function and fails universal positivity.

More generally, let $(\gamma_n,t_n)$ be any sequence of finite nonnegative pairs, and define the ordinary finite real products $d_n=\gamma_nt_n$ before taking any limit. If $d_n\to d<\infty$, the distributions converge uniformly over states and angles to the expression (3) with $q=e^{-d}$; this limit is universally nonnegative if and only if $d\geq c$, and strictly positive everywhere if $d>c$. If $d_n\to+\infty$, the distributions converge uniformly to $1/4$. These statements assign no value to an extended-real product such as $0\cdot\infty$.

Proof. The formula for $T_\gamma$ is Theorem 2.1. Taking reciprocals in $1/2<q_\star<5/9$ yields $9/5<1/q_\star<2$, proving the bound on $e^c$ and the inverse-rate scaling. The two one-variable limits of $c/\gamma$ follow since $0<c<\infty$.

For finite zero rate, every exponent in Definition 1.4 is zero, including at $t=0$, and hence $q=1$ for every finite $t$. The density $e_3e_3^\dagger$ at $\theta=0$ always gives $-1$ by Theorem 2.1. Thus taking $t\to\infty$ along the identically zero-rate family leaves a fixed function with a negative value. No multiplication involving an infinite time is needed.

For quantitative uniform convergence, denote by $F(q;\rho,\theta,\phi)$ the right side of (3). The coefficients in (2) give for $q\in[0,1]$

$$
\left|F(q;\rho,\theta,\phi)-\frac14\right|
\leq \max_j\left|\lambda_j(q)-\frac14\right|
\leq\frac{3q+5q^3+21q^6}{4}.
\tag{5}
$$

The first inequality uses the nonnegative weights summing to one, and the second bounds every displayed coefficient separately after the exact spectral identity has already been established. This estimate concerns convergence, not a replacement positivity criterion. It is independent of the state and angles. At fixed $\gamma>0$, $e^{-\gamma t}\to0$ as $t\to\infty$; at fixed $t>0$, $e^{-\gamma t}\to0$ as $\gamma\to\infty$. Equation (5) proves both uniform limits. At fixed $t=0$, $e^{-\gamma\cdot0}=1$ for every finite rate, so that limit is undamped instead.

For general finite pairs, (2)–(3) continue to hold at $\gamma=0$. If $d_n\to d<\infty$, continuity gives $q_n=e^{-d_n}\to e^{-d}$. The eigenvectors and weights in (3) depend on the observation and state, but not on $q$. Thus

$$
\sup_{\rho,\theta,\phi}|F(q_n;\rho,\theta,\phi)-F(q;\rho,\theta,\phi)|
\leq\max_{0\leq j\leq3}|\lambda_j(q_n)-\lambda_j(q)|\longrightarrow0,
$$

because the four eigenvalues are polynomials. The same scalar sign proof as in Theorem 2.1, including the pure-state obstruction when $q>q_\star$, gives the exact positivity statements at this limit. If $d_n\to\infty$, then $q_n\to0$, and (5) applies directly.

For specificity, the separate limits of the factors do not determine a joint limit. With $t_n=n$ and $\gamma_n=d/n$ for any fixed $d>0$, the factors tend to infinity and zero respectively but their finite products equal $d$. The same factor limits with $\gamma_n=1/n^2$ yield products tending to zero, whereas $\gamma_n=1/\sqrt n$ yields products tending to infinity. Likewise, with $\gamma_n=n$ and $t_n=d/n$ any fixed $d>0$ is realized while rate tends to infinity and time to zero; choices $t_n=1/n^2$ and $t_n=1/\sqrt n$ realize product limits zero and infinity. These are exact sequences of finite parameters. They explain why threshold collapse as rate grows does not turn $t=0$ into a positive original-domain point. All assertions concern the fixed $J=3/2,\sigma=1$ distribution; they do not extend the positivity criterion to other spins or ordering parameters, or identify it with separability or another physical property. $\square$

## 追加锚（本行以下为增补区）
