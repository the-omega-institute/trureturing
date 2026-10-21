# 六维第四个无偏基问题：理论续卷 V

本卷承接[理论续卷 IV](MUB_SIX_FOURTH_BASIS_THEORY_CONTINUATION_IV.md)，保留同一实际 paired-circulant 族、原始输入基约定及所有相位、排列和参数例外。第 97–100 节给出穿过退化点的线性提升、完整 source guard 清除、aligned 坐标 guard 清除及两主元拼接。第 101 节逐点处理四个新的 punctured 参数纤维；连同此前结果，共有二十四个指定的带符号例外参数得到证明。第 102 节从原始方程证明物理通道碰撞的必要参数条件，并给出可逐项重建的新有限 guard。

所有尚需的重建、幂基和正交矩阵条件仍被保留。这里没有断言新 guard 的实零点严格少于旧 guard，也没有断言剩余 guard 无零点。固定 MUB 对的四基排除只在所述 guard 非零集合、已单独处理的纤维及明确证明的邻域成立。

## 97. Global linear lifts and nonreduced specialization

Throughout §§97–102, use the actual input convention of §§75,87 and
\(0<|b|<1\). Write
\[
 B=b^2,\qquad R=3-B,\qquad
 \kappa=(b-i)\sqrt{R/(1+B)}.
\]
Thus the physical coefficients are \(G/\kappa,C/\kappa,D/\kappa\).
The symbol \(B\) in this continuation denotes \(b^2\); occurrences of
\(3+b^2\) in the earlier equations are written \(3+B\) here.
All six cubic orders and the optional \(\Theta\) channel choice remain.

### 97.1. A line identity through the quadratic-leading zero

Use the original polynomial definitions of §87. Put
\[
 \operatorname{Re}(E_n)/6=Au+D_0v+C_0,\qquad
 \sigma=A^2+D_0^2,\qquad \tau=-D_0u+Av,
 \qquad d=\beta\bar\beta.
\]
On every original strict selected-channel ray, \(d,\sigma>0\), and
\[
 u=(-AC_0-D_0\tau)/\sigma,\qquad
 v=(-D_0C_0+A\tau)/\sigma.                             \tag{97.1}
\]
Let \(Q_g,Y_g,D_g\) be the globally substituted original equations
of §87.4, and write
\[
 q_2=-8(3+B)F_8,\qquad
 L_Y=a_Y\tau+\mu_Y,\qquad L_D=a_D\tau+\mu_D.
\]
Exact polynomial division gives
\[
\begin{split}
 q_2Y_g&=Q_g H_Y+\frac{R(3+B)d^2\sigma^3}{4608}L_Y,\\
 q_2D_g&=Q_g H_D-\frac{(3+B)d^2\sigma^2}{96}L_D.       \tag{97.2}
\end{split}
\]
These equations also define the two polynomial quotients \(H_Y,H_D\)
uniquely by division by \(Q_g\) in the coefficient ring. Their
numerators, divisors and constants are the original polynomials printed
in §87; hence (97.2) is reconstructible without a new coefficient input.
The divisions are exact identities of polynomials, including \(A=0\).
They are not divisions by the value of \(q_2\) at a solution.

At every original strict ray, \(Q_g=Y_g=D_g=0\). The two remaining
multipliers in (97.2) are nonzero. Therefore
\[
 a_Y\tau+\mu_Y=a_D\tau+\mu_D=0                       \tag{97.3}
\]
even when \(F_8=0\). In particular any legal unique linear lift of
(97.3), followed by (97.1), recovers the actual original coordinates
without a quadratic-leading division. This is uniqueness of line
coordinates for the selected source point, not uniqueness of an ordered
ray. The original source necessity in Theorem 87.2 is likewise independent
of \(F_8\), so it may be applied before choosing this lift.

### 97.2. Two discriminants that are not inversion hypotheses

For the degree-twenty model (89.1), put
\[
 a=1+k^2,\qquad d_{\rm rad}=t^2+4Ra,\qquad
 \delta=q^2[3-4(e+\bar e)]+6q-1.
\]
At an actual selected generic point, \(k,t\) are real and \(R>0\), so
\(d_{\rm rad}>0\). The original single-ray reconstruction still requires
\[
 \beta C D Y_c\ne0,\qquad 0<q<1,\qquad \delta<0.       \tag{97.4}
\]
These pointwise physical requirements are not removed. Their strict
cubic sign can also be checked directly: for the three original distinct
unit roots \(z_1,z_2,z_3\), set \(\xi=z_1z_2z_3\) and
\(V=(z_1-z_2)(z_1-z_3)(z_2-z_3)\). The cubic (87.4) has
discriminant \(27\xi^2\delta=V^2\), while
\(\bar V=-V/\xi^2\). Hence
\[
 \delta=-|V|^2/27<0.
\]
This is a statement at an actual physical ray, without a full-algebra
unit assumption.

The algebraic construction itself does not invert either discriminant.
The monic relation
\[
 X^2=(t/a)X+R/a
\]
gives a free rank-two extension even at a nonreduced complex fibre. The
involution \(\iota(X)=t/a-X\) needs only \(a\). The identity
\(X(aX-t)=R\) makes \(X\), and hence \(G=X(1+ik)\) and
\(\bar G=X(1-ik)\), units using \(R,a\). No discriminant is used.

For precision, the other operations in §§89–90 have the following
inversions. The decic construction uses its leading coefficient,
\(F_k,a\); the original lift uses its chosen linear pivot and
\(\sigma,\beta,\bar\beta\). The original \(q,e,\bar e\) formulas
use \(C,D,Y_c\) and their bars. The power-basis change uses its own
determinant. The nine ordinary-overlap arguments use only
\(R,q,\bar e\) and their second-factor versions after those coefficients
are constructed. The mixed companion determinant uses the same generic
denominators and the aligned denominators of §90. None uses
\(F_8^{-1},d_{\rm rad}^{-1},\delta^{-1}\). The capital quantity
\(\Delta=D\bar D-C\bar C\) is a different marking and remains required.

Consequently the three separate nonzero-norm markings
\[
 \operatorname{Nm}(F_8),\quad
 \operatorname{Nm}(d_{\rm rad}),\quad
 \operatorname{Nm}(\delta)                            \tag{97.5}
\]
may be omitted from the construction of §§89–90. Every old reduced
scalar denominator, including a denominator of one of these three norms,
and every other required marking is retained. A factor required elsewhere
is not removed by omitting its appearance in (97.5).

### 97.3. Specialization without reducedness

Here and below a finite guard is specified by the finite construction rule
of §89.3: include the reduced denominators of every constructed scalar
entry and the numerators of all declared required-nonzero scalars,
together with coefficient conjugates; discard constants and take the
primitive integer part with positive leading coefficient.

Let \(S\) be the product of the retained construction denominators and
nonzero scalars. Over \(\mathbb Q(i)[b,1/S]\), the monic decic quotient
is free of rank ten, and its monic radial extension is free of rank twenty.
An algebra inverse is constructed by its multiplication adjugate and its
retained determinant. These statements do not require a reduced fibre.
The involution preserves the radial relation. The map
\[
 \rho(a\otimes c)=a\iota(c)
\]
has the linear section \(a\mapsto a\otimes1\); its split kernel sequence
therefore survives every allowed base change.

The established characteristic-zero identity \(\rho(N)=0\) of §89
has coefficients in this localized ring. They vanish in its fraction
field and hence in the ring. The original analytic half-parameter branch
used to establish the identity is unchanged. In particular the strict
conditions at that branch are not being assumed at every later parameter.
At each allowed specialization, the retained generic minor gives rank
at least 380, while \(\rho(N)=0\) gives rank at most 380. Thus
\[
 N(\mathcal A_b\otimes\mathcal A_b)=\ker\rho_b.        \tag{97.6}
\]
The unchanged mixed determinant gives its invertibility directly.
The original coverage and (97.3) then give all the pair and basis
consequences of §§89–91. No generic ideal multiplier with an unrecorded
pole is specialized. This proves the marking changes (97.5), including
at nonreduced fibres, while retaining (97.4) and every remaining guard.

## 98. The complete projective-source guard has only twelve known fibres

Use the six triples \((P_j,N_j,D_j)\), including the two repeated
components, and the primitive source polynomials \(h_0,h_1,h_2\) of
§88. The polynomials \(L(B),P_{48}(B),P_{98}(B)\) are those printed
in §§92–94. Define
\[
 J_{\rm src}(b)=L(b^2)P_{48}(b^2)P_{98}(b^2).
\]

**Theorem 98.1.** If \(0<|b|<1\) and \(J_{\rm src}(b)\ne0\),
the entire real projective source zero set relevant to the original
selected-channel problem consists of
\[
 [1:k:T(b,k)/F_k(b,k)],\qquad F(b,k)=0,\quad k\in\mathbb R.
                                                               \tag{98.1}
\]
All twelve signed zeros of \(J_{\rm src}\) have their separate
original-equation closures in §§92–94. The proof here does not extend
the particular quotient \(T/F_k\) through those zeros.

### 98.1. Ordered determinant and sign conventions

Put \(k=bK\). There are integer polynomials \(p_j,d_j\) defined
uniquely by
\[
 P_j(b,bK)=b^{e_j}p_j(B,K),\qquad
 D_j(b,bK)=b^{f_j}d_j(B,K),
\]
where the six pairs \((e_j,f_j)\), in order, are
\[
 (6,5),(0,1),(0,1),(4,3),(0,1),(0,2).                  \tag{98.2}
\]
Their \(K\)-degrees are \(10,4,4,4,4,4\), and
\(d_0=\partial_Kp_0\). These definitions use the full characteristic-zero
polynomials in §88, not reductions at one parameter.

For \(p,q\) of respective \(K\)-degrees \(m,n\),
\(\operatorname{Res}_K(p,q)\) means the determinant with the \(n\)
shifted descending-coefficient rows of \(p\) first and the \(m\)
rows of \(q\) second. This order fixes all scalar signs. Its degree in
\(B\) is at most
\[
 n\deg_Bp+m\deg_Bq.                                    \tag{98.3}
\]
The matrix keeps these symbolic row lengths even at a sampled value
where a leading coefficient vanishes. For scaled polynomials as in
(98.2), the exact identity is
\[
 \operatorname{Res}_k(P,Q)
 =b^{en+fm-mn}\operatorname{Res}_K(p,q).                \tag{98.4}
\]
Negative exponents cause no loss because \(b\ne0\).

Here is a finite reconstruction rule used for the determinant identities
below. For an integer-polynomial matrix with degree bound \(n\), evaluate
its determinant exactly at \(B=0,\ldots,n\). If the values are \(a_j\),
the polynomial is
\[
 \sum_{j=0}^n(\nabla^j a_0)\binom Bj,\qquad
 \nabla a_j=a_{j+1}-a_j.                                \tag{98.5}
\]
All divisions are rational and exact. The degree bound and these
\(n+1\) distinct values prove equality over \(\mathbb Q[B]\).
Thus (98.2)–(98.5), the printed §88 coefficients, and the following
small tables are complete definitions of the large polynomials used here.

### 98.2. Component denominators and separations

Define
\[
\begin{split}
 A_4&=B^4+24B^3-54B^2+81,\\
 C_4&=B^4-8B^3+22B^2+24B+9,\\
 W_2&=B^2-6B-3,\qquad Q_2=4B^2-3B+9,\\
 U_3&=B^3+15B^2+9B+27,\\
 U_4&=2B^4+21B^3-153B^2-189B-81,\\
 U_8&=43B^8+168B^7-2664B^6+20304B^5-4050B^4\\
    &\hspace{12mm}-126360B^3-151632B^2-69984B-6561.
\end{split}                                                    \tag{98.6}
\]
The six leading coefficients \(\ell_j=\operatorname{lc}_Kp_j\) are
\[
 3B^2L,\quad81B^4,\quad9B^2A_4,\quad(B-3)^2,
 \quad243B^2C_4,\quad B^2.                               \tag{98.7}
\]
For \(u_j=\operatorname{Res}_K(p_j,d_j)\), the ordered products are
\[
\begin{split}
 u_0={}&-\ell_0\,2^{26}B^6(B+1)^5(B-3)^8(B+3)^{42}
                    Q_2P_{48}P_{98}^2,\\
 u_1={}&-177147(B-3)^2B^8(B+3)^{12}U_8,\\
 u_2={}&944784(B-3)^2(B+1)^2B^6(B+3)^8Q_2^2U_3^2A_4,\\
 u_3={}&(B+1)^4U_4^4,\\
 u_4={}&-4782969B^4(B-3)^6(B+3)^{12}W_2^2C_4U_8,\\
 u_5={}&16(B+9)^4.
\end{split}                                                    \tag{98.8}
\]
The sign in \(u_0\) is \((-1)^{10\cdot9/2}=-1\).
The degree bound (98.3) and reconstruction (98.5) verify all six
identities directly. For the signed Euclidean Sturm sequence beginning
with a polynomial and its derivative and continuing with negative exact
remainders, the endpoint variation pairs at 0 and 1 are, in the order
\(A_4,C_4,W_2,Q_2,U_3,U_4,U_8\),
\[
 (1,1),(2,2),(1,1),(1,1),(1,1),(2,2),(3,3).
\]
Zero signs are omitted; division by a positive content is harmless.
None of these polynomials vanishes at an endpoint. Thus each has no root
in \((0,1)\). Together with the already printed root inventories of
\(L,P_{48},P_{98}\), this identifies every leading or
component-denominator zero.

For each \(i<j\), define \(W_{ij}\) by the exact polynomial quotient
\[
 W_{ij}(B)=\frac{\operatorname{Res}_K(p_i,p_j)}
 {c_{ij}B^{r_0}(B-1)^{r_1}(B+1)^{r_2}(B-3)^{r_3}(B+3)^{r_4}}.
                                                               \tag{98.9}
\]
The table gives \((i,j,c_{ij},r_0,\ldots,r_4,d,n,\mathcal C)\),
where \(d=\deg W_{ij}\), \(n\) is the bound (98.3), and
\(\mathcal C\) is its signed dyadic Bernstein cover. All data are integers.

```text
# i j c r0 r1 r2 r3 r4 d n : (depth,index,sign) leaves
0 1 27 9 0 0 0 20 93 122 : (1,0,1),(2,2,1),(2,3,1)
0 2 2304 8 0 0 0 16 96 132 : (0,0,1)
0 3 1 0 0 4 0 0 80 92 : (0,0,1)
0 4 6912 10 0 2 4 20 91 132 : (0,0,1)
0 5 4096 10 0 2 4 0 64 92 : (0,0,1)
1 2 6561 8 0 0 0 0 36 44 : (0,0,1)
1 3 1 0 0 0 0 0 28 28 : (0,0,1)
1 4 177147 9 0 0 0 0 35 44 : (0,0,1)
1 5 1 12 0 0 0 0 16 28 : (0,0,1)
2 3 1 0 0 0 0 0 28 32 : (1,0,1),(1,1,1)
2 4 186624 10 0 0 0 12 24 48 : (0,0,1)
2 5 256 8 0 0 0 0 16 32 : (0,0,1)
3 4 1 0 0 0 0 0 30 32 : (0,0,1)
3 5 1 0 0 4 0 0 8 16 : (0,0,1)
4 5 256 10 0 0 0 0 20 32 : (0,0,1)
```

For a degree-\(d\) polynomial \(W=\sum a_kB^k\), set
\[
 \beta_j=\sum_{k\le j}a_k\frac{\binom jk}{\binom dk},\qquad
 W(B)=\sum_{j=0}^d\beta_j\binom djB^j(1-B)^{d-j}.        \tag{98.10}
\]
A leaf \((h,r,s)\) refers to \([r2^{-h},(r+1)2^{-h}]\).
Repeated de Casteljau averages \((\beta_j+\beta_{j+1})/2\)
reconstruct the coefficients on each half. In every listed leaf all
coefficients have strict sign \(s\); the leaves cover \([0,1]\).
These checks, including the exact divisions (98.9), follow by (98.5).
Therefore all fifteen separation resultants are nonzero on the puncture.
No irreducibility of any \(W_{ij}\) is needed.

### 98.3. The vertical source chart

Let \(v_0(b,z),v_1(b,z)\) be the homogeneous coordinate-degree-eight
and coordinate-degree-ten parts of the first two primitive sources,
with their second coordinate set to one, exactly as in §88. Put
\[
 v_0(b,bK)=bV_0(B,K),\qquad v_1(b,bK)=b^2V_1(B,K).
\]
Their \((K,B)\)-degrees are \((8,12),(10,15)\). Define
\[
 W_{64}=
 \frac{\operatorname{Res}_K(V_0,V_1)}
 {c_vB^{41}(B+1)^4(B-3)^{39}(B+3)^{28}L},\qquad
 c_v=1338662775249539744601275586607292586269882992619224032746668032.
                                                               \tag{98.11}
\]
The degree-240 version of (98.5) verifies that this is a polynomial of
degree 64. All its 65 coefficients (98.10) are strictly positive.
This is the single Bernstein leaf \((0,0,+1)\).
The original vertical determinant has ten shifted \(v_0\) rows then
eight shifted \(v_1\) rows in ascending powers of \(z\).
Column and row-block reversals have total positive sign, so (98.4) gives
\[
 b^{54}v(b)=c_vB^{41}(B+1)^4(B-3)^{39}(B+3)^{28}L(B)W_{64}(B).
                                                               \tag{98.12}
\]
Its only punctured zeros are the two signed \(L\) fibres.

### 98.4. Two affine bases replace the one-minor chart

Order the 210 monomials \(t^ak^c\), \(a+c\le19\), by descending
total degree and then descending \(a\). Form the 188 rows
\(t^ak^ch_j\) in the order \(j=0,1,2\), then increasing
\(a=0,\ldots,19-n_j\), then increasing \(c=0,\ldots,19-n_j-a\),
where \((n_0,n_1,n_2)=(8,10,10)\). All indices below start at zero.
The first matrix \(M\) deletes rows
\[
 1,13,78,183,184,185,186,187
\]
and keeps the columns outside
\[
 \mathcal B_0=\{t^ak^c:a+c\le6\}\cup\{tk^6,k^7\}.
\]
The alternate matrix \(M'\) deletes rows
\[
 1,13,78,182,184,185,186,187
\]
and keeps the columns outside
\[
 \mathcal B_1=\{t^ak^c:a+c\le6\}\cup\{t^2k^5,k^7\}.
\]
Rows and columns retain their original order. Both matrices are
\(180\times180\), and both complementary sets have 30 monomials,
contain 1, and have maximum degree seven.

After \(k=bK\), the source transformations are
\[
 h_0(b,bK,t)=bH_0(B,K,t),\quad
 h_1(b,bK,t)=H_1(B,K,t),\quad
 h_2(b,bK,t)=b^2H_2(B,K,t).
\]
Form \(A,A'\) by the same rule using the \(H_j\).
Each original row/column coefficient acquires the factor
\(b^{c+e_j-v}\), where \((e_j)=(1,0,2)\) and \(v\) is the
column's \(k\)-exponent. Summing the exponents gives, for both matrices,
\[
 \det M=b^{-475}\det A(B),\qquad
 \det M'=b^{-475}\det A'(B).                            \tag{98.13}
\]

Define \(A_r\) canonically as follows: in row order, divide every row
of \(A\) by the positive-leading gcd in \(\mathbb Z[B]\) of all its
nonzero entries; then do the same once for each column in column order.
This gives 105 nontrivial row divisions and 127 column divisions,
with total factor
\[
 c_r(B)=2^{456}3^2B^{77}(B+3)^{105}(B-3)^{258}(B+9).    \tag{98.14}
\]
Every division is exact in \(\mathbb Z[B]\). Define additionally
\[
\begin{split}
 J_4&=B^4-33B^3+387B^2+729B+324,\\
 E_4&=2B^4+9B^3-27B^2+9B+27,\\
 F_4&=5B^4-6B^3-18B+27,\\
 G_6&=B^6-37B^5+234B^4-396B^3+351B^2-999B+1134,\\
 H(B)&=2^{717}3^{718}B^{239}(B-1)^8(B+1)^{62}(B-3)^{205}
       (B+3)^{461}(B+9)^{25}\\
     &\hspace{12mm}\cdot L^{12}A_4^{12}C_4^{12}W_2^6J_4^{18}E_4F_4G_6.
\end{split}                                                    \tag{98.15}
\]
This \(H\) has degree 1386. The following definition avoids any
unprinted high-degree factor input. For \(j=0,\ldots,184\), let
\[
 z_j=\det A_r(2j+2)/H(2j+2),\qquad
 Z(B)=\sum_{j=0}^{184}(\nabla^jz_0)\binom{(B-2)/2}{j}. \tag{98.16}
\]
All 185 displayed denominators are nonzero. Exact rational interpolation
gives \(Z\in\mathbb Z[B]\) of degree 184.

Here are degree and negative-valuation potentials for \(A_r\).
Each block lists its 180 row potentials followed by its 180 column
potentials, in the specified matrix order.

```text
degree_rows = [
  2,1,0,-1,-2,-3,-4,-5,-6,-6,-7,3,1,0,-1,-2,-3,-4,-5,-5,
  -6,3,2,1,0,-1,-2,-3,-4,-4,-5,3,2,1,0,-1,-2,-3,-3,-4,
  3,2,1,0,-1,-2,-2,-3,3,2,1,0,-1,-1,-2,3,2,1,0,0,
  -1,3,2,1,1,0,3,2,2,1,3,3,2,4,3,4,5,4,3,2,
  1,0,-1,-2,-3,6,5,4,3,2,1,0,-1,-2,6,5,4,3,2,1,
  0,-1,6,5,4,3,2,1,0,6,5,4,3,2,1,6,5,4,3,2,
  6,5,4,3,6,5,4,6,5,6,5,4,3,2,1,0,-1,-2,-3,-4,
  5,4,3,2,1,0,-1,-2,-3,5,4,3,2,1,0,-1,-2,5,4,3,
  2,1,0,-1,5,4,3,2,1,0,5,4,3,2,1,5,4,3,2,5
]
degree_columns = [
  0,3,4,6,7,8,9,10,11,12,12,13,14,15,16,15,16,15,16,15,
  3,4,5,6,7,8,9,10,11,12,13,14,14,15,15,15,15,15,15,5,
  6,7,8,9,10,11,12,13,14,15,15,16,15,16,15,16,15,5,6,7,
  8,9,10,11,12,13,14,14,15,15,15,15,15,15,5,6,7,8,9,10,
  11,12,13,13,14,14,15,14,15,14,5,6,7,8,9,10,11,12,12,13,
  13,14,14,14,14,5,6,7,8,9,10,11,11,12,12,13,13,14,13,5,
  6,7,8,9,10,10,11,11,12,12,13,13,5,6,7,8,9,9,10,10,
  11,11,12,12,5,6,7,8,8,9,9,10,10,11,11,5,6,7,7,8,
  8,9,9,10,10,5,5,6,7,7,8,8,9,9,5,5,6,6,7,7
]
negative_B_valuation_rows = [
  -6,-6,-5,-5,-4,-4,-3,-3,-2,-1,0,-7,-6,-5,-5,-4,-4,-3,-3,-2,
  -1,-7,-6,-6,-5,-5,-4,-4,-3,-3,-2,-7,-6,-6,-5,-5,-4,-4,-3,-3,
  -7,-6,-6,-5,-5,-4,-4,-3,-7,-6,-6,-5,-5,-4,-4,-6,-6,-5,-5,-4,
  -4,-6,-5,-5,-4,-4,-5,-5,-4,-4,-5,-4,-4,-4,-4,-4,-7,-6,-6,-5,
  -5,-4,-4,-3,-2,-7,-7,-6,-6,-5,-5,-4,-4,-3,-7,-7,-6,-6,-5,-5,
  -4,-4,-7,-7,-6,-6,-5,-5,-4,-7,-7,-6,-6,-5,-5,-7,-6,-6,-5,-5,
  -6,-6,-5,-5,-6,-5,-5,-5,-5,-5,-6,-6,-5,-5,-4,-4,-3,-3,-2,-1,
  -6,-6,-5,-5,-4,-4,-3,-3,-2,-6,-6,-5,-5,-4,-4,-3,-3,-6,-6,-5,
  -5,-4,-4,-3,-6,-6,-5,-5,-4,-4,-6,-5,-5,-4,-4,-5,-5,-4,-4,-5
]
negative_B_valuation_columns = [
  4,4,4,4,4,4,4,4,4,4,3,3,2,2,1,2,1,1,0,0,
  4,4,4,4,4,4,4,4,4,4,3,3,2,2,1,2,1,1,0,4,
  4,4,4,4,4,4,4,3,3,2,2,1,2,1,2,1,1,4,4,4,
  4,4,4,4,4,3,3,2,2,1,2,1,2,1,5,5,5,5,5,5,
  4,4,3,3,2,2,1,2,1,2,5,5,5,5,5,5,4,4,3,3,
  2,2,1,2,1,6,6,6,6,5,5,4,4,3,3,2,2,1,2,6,
  6,6,6,5,5,4,4,3,3,2,2,1,7,7,6,6,5,5,4,4,
  3,3,2,2,7,7,6,6,5,5,4,4,3,3,2,7,7,6,6,5,
  5,4,4,3,3,7,7,6,6,5,5,4,4,3,7,7,6,6,5,5
]
```

For every nonzero entry, direct inspection gives
\[
 \deg_B(A_r)_{ij}\le r_i+c_j,\qquad
 -\operatorname{ord}_B(A_r)_{ij}\le r'_i+c'_j.
\]
The two total sums are \(2050\) and \(-193\). Thus
\(\deg\det A_r\le2050\) and \(B^{193}\mid\det A_r\).
Negative individual potentials are allowed: each determinant term uses
every row and column exactly once.

The complete finite identity certificate is
\[
 \det A_r(2j+2)=H(2j+2)Z(2j+2),\qquad 0\le j\le1857. \tag{98.17}
\]
The first 185 values define \(Z\); all remaining equalities are checked
from the original matrix, with integer determinants. The difference
\((\det A_r-HZ)/B^{193}\) has degree at most 1857 and has 1858
distinct nonzero roots. Hence
\[
 \det A_r=HZ                                                \tag{98.18}
\]
is an identity in characteristic zero. This explains why a degree-184
interpolation alone would not be a certificate.

One exact integer determinant algorithm for (98.17) is row-primitive
elimination. Divide each row by its positive integer gcd and accumulate
those factors. At an active \(m\times m\) matrix choose a nonzero
first-column pivot \(p\), recording the row-swap sign. Replace lower
row \(i\) by \(p\) times that row minus its first entry times the
pivot row. Divide it by its positive gcd \(g_i\), and recurse on the
remaining block \(C\). The exact relation is
\[
 \det(\text{active})=\det C\,\prod_i g_i/p^{m-2}.
\]
All accumulated rational operations are exact; the final denominator
is one. A missing pivot or zero row gives zero.

### 98.5. An exact coprimality check covers every zero of the first minor

The signed Sturm endpoint variation pairs for \(E_4,F_4,G_6\) are
\((1,1),(2,2),(5,5)\). All are nonzero at 0 and 1. The other small
factors of (98.15) are nonzero on \((0,1)\): this was checked above
for \(A_4,C_4\); \(W_2<0\), while
\(387B^2-33B^3>0\) makes \(J_4>0\).
Consequently
\[
 \det M(b)=0,\ L(b^2)\ne0\quad\Longrightarrow\quad Z(b^2)=0.
                                                               \tag{98.19}
\]
No real-root count for \(Z\) is required.

The row-degree sum of the original alternate matrix \(A'\) is 3400.
In \(\mathbb F_{10007}[B]\), define \(f\) by the exact interpolation
(98.5) of its 3401 determinants at \(B=0,\ldots,3400\).
The nodes are distinct and \(j!\ne0\) for all these \(j\).
This reconstructs the full reduction of \(\det A'\), whose degree is
2012. Direct Euclidean division gives
\[
 \deg\bar Z=184,\qquad \gcd(f,\bar Z)=1.                \tag{98.20}
\]
Here \(Z\) is reconstructed by (98.16), so (98.20) is a finite
certificate from printed source matrices, without external polynomial
coefficients. To replay it, form \(f\bmod\bar Z\), apply monic
Euclid with \(\bar Z\), and check its terminal constant equals one.
The normalized extended Euclidean identity supplies the corresponding
Bezout identity over \(\mathbb F_{10007}\).

Preservation of \(\deg Z\) makes (98.20) a characteristic-zero
coprimality certificate. A primitive nonconstant common factor of
\(\det A'\) and \(Z\) in \(\mathbb Z[B]\) would retain its degree
modulo 10007, since the leading coefficient of \(Z\) is nonzero there.
It would contradict (98.20). Hence \(\det A'\) is nonzero at every
complex root of \(Z\). By (98.13), (98.18) and (98.19), at least one
of \(\det M,\det M'\) is nonzero whenever \(0<|b|<1\) and \(L\ne0\).

### 98.6. Full quotient, including the nonreduced components

A nonzero one of these two minors expresses every non-basis monomial
of degree at most 19 in its complementary 30-dimensional span modulo
the original sources. Every one-step \(k\)- or \(t\)-multiple of a
basis monomial has degree at most eight. Induction on multiplication
therefore spans the entire quotient, not merely a truncation. Thus
\[
 \dim_{\mathbb C}\mathbb C[k,t]/(h_0,h_1,h_2)\le30.
\]
When \(J_{\rm src}\ne0\), (98.7)–(98.12) supply all the component,
denominator and vertical hypotheses of §88. Its eighteen original
characteristic-zero identities give a surjection onto the product of
six component algebras of total dimension 30. The repeated factors retain
their full nonreduced lengths. The upper bound makes this an isomorphism.
The five nonreal-component exclusions in §88 and the vertical exclusion
then prove Theorem 98.1.

As a precise guard change, the required-nonzero source marking \(E_*\)
may therefore be replaced by \(J_{\rm src}\). Every other scalar array,
reduced scalar denominator, original-lift unit, basis determinant and
overlap marking is retained. This replaces a proof hypothesis; it does
not assert that no retained denominator has the same factor.

## 99. The aligned coordinate guards have only four known fibres

Retain the exact original aligned quintic \(Q_5(b,D)\), shape polynomials
\(U,V\), and strict reconstruction of §90. In this section \(D\) is
the aligned real quotient coordinate. Put
\[
\begin{split}
 A_{10}(b)&=2b^{10}+33b^8+90b^6+4b^2-1,\\
 A_{14}(b)&=9b^{14}+181b^{12}+140b^{10}-4254b^8+1537b^6\\
          &\hspace{15mm}+30305b^4-58758b^2+24696.
\end{split}                                                    \tag{99.1}
\]
These are the aligned exceptional polynomials denoted \(Q_{10},Q_{14}\)
in §96. The names \(A_{10},A_{14}\) distinguish them from generic-pivot
factors below.

**Theorem 99.1.** For \(0<|b|<1\) and \(A_{10}A_{14}\ne0\), the
quintic has degree five and is squarefree. In its entire coefficient
algebra, \(D,V\) and, with \(T=U/V\),
\[
 K=D^2+4T,\quad J=bD-T+3,\quad F_a=D^2+(T+1)^2,
 \quad(2-iD)^2+K,\quad(2+iD)^2+K
\]
are units. Every noncanonical aligned original ray is covered by the
quintic and the original finite lift of §90. All signs, positions and
strict filters remain, including a constant channel when present.
The four signed exceptional fibres in (99.1) have the separate closure
of §96.

### 99.1. A complete ordered-resultant certificate

Define the integer polynomials
\[
 K_n=D^2V+4U,\quad J_n=(bD+3)V-U,\quad
 F_n=D^2V^2+(U+V)^2.                                    \tag{99.2}
\]
The following coefficient lists define eighteen integer polynomials
\(f_j(b)\). The first three are \(b,b+1,b-1\). For \(j\ge4\), a
listed vector \([c_0,\ldots,c_d]\) means
\(f_j(b)=\sum_{r=0}^d c_rb^{2r}\); thus its variable is \(B=b^2\).

```text
f1=b
f2=b+1
f3=b-1
f4=[1,1]
f5=[3,1]
f6=[-3,1]
f7=[-27,9,2]
f8=[49,22,9]
f9=[81,18,-23,4]
f10=[9,39,103,9]
f11=[2025,-612,-170,28,9]
f12=[-1,4,0,90,33,2]
f13=[24696,-58758,30305,1537,-4254,140,181,9]
f14=[
  29241,-19584,4603342,8757060,
  6901815,1531408,-547836,-326408,
  4615,30800,6574,484,
  9
]
f15=[
  4435236,33890481,634854510,2873798955,
  20894667400,46105854185,93746778938,-37487362117,
  -33603834556,7213066859,4594255138,-439649991,
  -297226800,-921861,7663734,613089
]
f16=[
  177147,-1889568,14644152,-120092544,
  449323524,-223490016,307606248,-90873792,
  -125776782,51887904,28837832,-32830464,
  12465444,-1410592,-116712,-43200,
  16875
]
f17=[
  -126557359740,509399484525,-409272743682,68401952145,
  -735950815416,-1928673285444,-879813799344,-315505756900,
  -299007962576,-120852186354,-142015028452,3224100118,
  7991198136,-11434667076,-2786509728,1268457084,
  610479180,100092429,7492662,216513
]
f18=[
  131878903006822500,-2539226871826763688,36260801783288542773,482035392247050850158,
  2068154327006051604921,-41879115742384871825328,445082317106129551182456,-1968491022058964641889664,
  5119317659976843100099176,-4838226081773216694739344,-6979442063885728436013876,6547179154646827373280120,
  10432815776010514356932988,5106273390639653491135632,-5731240644240325354744760,-5709316395888402819288928,
  1648031044653906480589408,1929073381456210262294432,-249128907004949997294914,-319138096425100376691388,
  7759640408951208702166,30279637878572675757296,2367026472497068030024,-1615709119427029551168,
  -317690313273880782408,34194307321423412496,16547805379423795788,809685469050913368,
  -353383243368657156,-53646706965748176,486983363762808,701015042767392,
  62994718818972,2146427528328,16763125365,-222142338,
  4782969
]
```

Each following row states
\(\operatorname{Res}_D(Q_5,W)=c\prod_j f_j^{m_j}\), with the first
argument's shifted rows first as in (98.3). The pairs are \((j,m_j)\).
The label \(Q'_5\) means the derivative, not its discriminant.

```text
# W : scalar ; (factor, exponent)
Q5prime: 274877906944 ; (1,6),(6,1),(4,1),(5,2),(11,1),(12,1),(16,1),(17,2)
V: 19807040628566084398385987584 ; (1,11),(4,1),(5,1),(6,5),(7,2),(11,2),(13,1),(14,2),(15,2),(17,2),(18,1)
Kn: -20282409603651670423947251286016 ; (3,2),(2,2),(1,13),(4,3),(5,5),(6,6),(8,1),(7,2),(9,1),(10,1),(11,2),(13,1),(14,2),(15,2),(17,2),(18,1)
Jn: 4928625533687355913019182062501888 ; (1,11),(5,1),(4,2),(6,7),(7,2),(11,1),(13,1),(14,2),(15,2),(17,2),(18,1)
Fn: 105312291668557186697918027683670432318895095400549111254310977536 ; (3,2),(2,2),(1,26),(5,2),(4,5),(6,10),(8,1),(7,4),(9,1),(11,4),(13,2),(14,4),(15,4),(17,4),(18,2)
```

All five identities are equalities in \(\mathbb Z[b]\). They can be
verified from the original §90 shape minors by exact Sylvester
reconstruction (98.3)–(98.5), now with variable \(b\). In particular,
computing a resultant with its arguments exchanged requires the factor
\((-1)^{\deg_DQ_5\deg_DW}\). The displayed scalar signs use the order
\((Q_5,W)\) throughout.

The complete signed Sturm inventory is as follows. Columns are
\(j,\deg_bf_j,V_j(0),V_j(1)\), and the number of roots in \((0,1)\).

```text
1 1 0 0 0
2 1 0 0 0
3 1 1 0 0
4 2 1 1 0
5 2 1 1 0
6 2 1 1 0
7 4 2 2 0
8 4 2 2 0
9 6 3 3 0
10 6 3 3 0
11 8 4 4 0
12 10 5 4 1
13 14 7 6 1
14 24 12 12 0
15 30 15 15 0
16 32 16 16 0
17 38 19 19 0
18 72 36 36 0
```

The chain begins with \(f,f'\) and uses negative exact remainders;
zero signs are omitted and only positive normalization is allowed.
The endpoint roots of \(f_1,f_3\) are excluded explicitly. Every other
factor is even and nonzero at 0 and 1. Thus the negative puncture has
the same inventory, and the only exceptional factors are
\(f_{12}=A_{10}\), \(f_{13}=A_{14}\).

### 99.2. Units and complete original chart coverage

The direct scalar identities are
\[
\begin{split}
 \operatorname{lc}_DQ_5&=f_{11}A_{10},\\
 Q_5(b,0)&=-8192b^3(b^2-3)(b^2+3)(2b^4+9b^2-27).
\end{split}                                                    \tag{99.3}
\]
They are nonzero in the stated domain. Thus \(D\) is a unit and the
quintic retains degree five. The derivative resultant proves squarefreeness.
The four other products make \(V,K_n,J_n,F_n\) units. Dividing by
the appropriate powers of \(V\) gives the claimed \(K,J,F_a\) units.
Moreover
\[
\begin{split}
 (2\mp iD)^2+K&=4((1\mp iD)V+U)/V,\\
 ((1-iD)V+U)((1+iD)V+U)&=F_n.
\end{split}                                                    \tag{99.4}
\]
A product which is a unit in a commutative algebra has each factor a
unit. Hence both complex Cayley denominators are units. Adjoining
\(s^2=K\) preserves reducedness since \(K\) is a unit and the
characteristic is zero. No algebra point is presumed physical.

For completeness the two original finite exceptional cofactor
resultants of §90 are
\[
\begin{split}
 r_0={}&4718592b^4(b^2-3)^3(b^2+3)(2b^4+9b^2-27),\\
 r_2={}&12582912b^{11}(b^2-3)^3(b^2+1)(b^2+4)^2
        (b^6+11b^4+4b^2+12)A_{14}.
\end{split}                                                    \tag{99.5}
\]
For \(D=2b\), \(r_2\) uses the sextic cofactor first and the quartic
cofactor second, after removal of their common \(T+b^2\) factor.
This states the argument order explicitly. Every displayed factor
except \(A_{14}\) is nonzero on the puncture. The remaining common
factors and the \(s=0\) deficiency have the original exclusions of
§90; the actual Cayley poles occur only at \(A_{10}=0\). Thus no
finite exceptional chart or pole is lost by using the unit algebra.
This proves Theorem 99.1 from the complete original necessity/sufficiency
classification.

This section accounts for the aligned coordinate, rank and reconstruction
requirements in (99.2)–(99.5). It does not replace a mixed-overlap
invertibility requirement or any generic reconstruction requirement.

## 100. Original reconstruction units and a regular two-pivot lift

The source theorem now supplies a free rank-twenty coefficient algebra
at every real punctured parameter with \(J_{\rm src}\ne0\). This
section proves the required original \(\beta,\bar\beta,\sigma\)
units and glues the two global linear equations. It leaves the subsequent
coefficient, power-basis and overlap requirements explicit.

### 100.1. The scaled source algebra

Set
\[
\begin{gathered}
 k=bK,\quad a=1+BK^2,\quad
 F_0(B,K)=b^{-6}F(b,bK),\\
 D_s=\partial_KF_0,\quad N_s=b^{-5}T(b,bK),\quad t=N_s/D_s.
\end{gathered}                                                    \tag{100.1}
\]
All indicated powers divide coefficientwise. The symbol \(D_s\) is
distinct from the line coefficient \(D_0\) and the reconstructed
coefficient \(D\). First take the monic \(F_0\) quotient and then
its monic radial extension
\[
 aX^2-tX-R=0.                                             \tag{100.2}
\]
Use basis \((1,K,\ldots,K^9,X,KX,\ldots,K^9X)\).
The original mean is \(G=X(1+ibK)\); bars fix \(b,K,X\) and conjugate
\(i\). The source theorem makes \(D_s\) a unit. Separation from
\(P_5=(1+k^2)^2\) makes \(a\) a unit, independently of whether a
complex fibre is reduced.

Define \(W_{32}\) by the exact ordered quotient
\[
 W_{32}(B)=\frac{\operatorname{Res}_K(F_0,a)}
 {2^6B^5(B-3)^2(B+1)}.                                  \tag{100.3}
\]
The determinant degree bound is 46. Its 47-value reconstruction proves
that the quotient is an integer polynomial of degree 32. It has no zero
on \((0,1)\) by the separation just proved. The source derivative
resultant, with its argument order fixed, is
\[
 \operatorname{Res}_K(F_0,D_s)
 =-3\cdot2^{26}B^8(B+1)^5(B-3)^8(B+3)^{42}Q_2LP_{48}P_{98}^2.
                                                               \tag{100.4}
\]

### 100.2. Full-algebra beta and sigma norms

Put
\[
\begin{split}
 C_3&=B^3+7B^2-129B+441,\\
 C_{10}&=64B^{10}+756B^9-8223B^8+12996B^7+20340B^6-6012B^5\\
       &\hspace{12mm}-50922B^4-18468B^3+30132B^2+29160B+6561.
\end{split}
\]
Let \(S_{83}\) be the degree-83 polynomial given below. The exact
multiplication norms in the full algebra (100.2) are
\[
\begin{split}
 \operatorname{Nm}(\beta\bar\beta)
 &=\frac{2^{32}3^{20}(B-3)^{20}(B-1)^2(B+1)^6(B+3)^{14}
                Q_2C_3C_{10}}{BW_{32}},\\
 \operatorname{Nm}(\sigma)
 &=\frac{2^{108}3^4(B-3)^{56}(B+1)^4(B+3)^{44}S_{83}}
              {B^2W_{32}^3}.                            \tag{100.5}
\end{split}
\]
Here and in all subsequent polynomial lists, coefficients are constant
first, in the variable \(B\).

```text
S83=[
  159881708616880647126690698091882456822336,14813780532494879749705047657055719754118352,741960040018020286090620953146629708392700744,
  18998497832748745947061470692280817682543776209,288407591234997349125385303447750460150148948384,2939674861053335520799958406565269917305811887176,
  22739643493186017437962655217470436720642280436016,137989442731328270911803965916182734016546297095656,586066483228065265693148498573490951129174792086280,
  1336821176743968394167274972108337781687989722947648,-1401777377418747576977379841260531120172034902184160,-27981353363521464766035412579519412384759353247797992,
  -101994910492690336146278399169027315266206170917123616,48264485312327407732104184960111359341734923650806704,1220728253253800324537227721891586383153054306850515136,
  1631893040904750658067687199340285793608985286801750528,-6160327112010061525026395551331659268720678063725005696,-16605931297225005806739657098072486897805761065770278208,
  9410713230829581811762459293583274489642400303026158560,73944997926046276023491886963644502300733937042379654444,42783272882481745362744418664753899834463211464315991936,
  -165551766262869638229316244836238395123584351157247222016,-227086055371160580130827650828092633271915953366587946368,176591605419946475993585737395030390809571128693056357440,
  467652026071917548064464190124804025074342620332380540704,-37169647843489227020303029161087693524969643389956995648,-555832372991362256671063623578681489790765424105436293056,
  -109512348581312369785287577683744275230759965553012269864,445759491442502533390064927065763737624539018273461409792,129232868093764859968040199182799916241782721008515773280,
  -288380644743500905425623598496166508190583406971568943296,-66225654461906864392966831704121297114858961654310234048,175348913295165489537502810147191592870374118182966334848,
  15324579042806925891062606844015718400120247917591836512,-96919652194754095540914335694999760626494688291691264848,7054085150129945316924728530354782222789188879489995830,
  44527698923861735713421005831842277742988169181154591936,-15885966635679201392396906996015375422553335907360055600,-14328522777139584919724382030277412862371967172722407328,
  12622444701554708404410573552501609373831098038567613840,1213705108162071563152042803499006982351688694107272304,-4759740053981149996413413760260656869886253354583309120,
  1163085867158094610262160083486418234673582585056398592,785986763088076035968260847396002971037067011241360856,-493145207906124439888978483277573422724530191907016256,
  -12509787858015222886657814485883894310650408418668352,91529741554305534524966543539733573463195061329645504,-17953900962516029204517618675072482841574195718378880,
  -7557437437373874206237178693761408883103058430774144,3253476247634160744789962409933386210775358877429184,-859783783358865277866968303594186565029519513434656,
  368670206014321480475967129793080366607680749904588,74911337537667576931491895625966219488536502100352,-146060824453889919209053412347330015353324326718912,
  35228314132431172770871984535208394166081872592640,16218369103599295945347810771832224773741739080832,-9709427122014490188334550996565467655163882514016,
  -302454769233153343430823556558708789938882786240,1423701604362229035731864338127110819801592962752,-305882010893849441332537315577013570353093866200,
  -59119610178149265406046683371598895020811059968,31937474478774035335089012833402955977236873632,-793823909487662188120075295417600060730576960,
  -1998937727102672458387774036883750729587322304,423550971813350956498147175247775926028987200,9776513928717698997944355220309103511470928,
  -12661629358619373068434966949461000533474744,12529070699889469215197528681851682096769,553966499165055726433144287890992108187808,
  -78573925051179980253642593303636540287064,-1756916953176906778814959328499314191120,1302035364712266656627901047935144221640,
  -85127134583233542043198200262564412472,-3092197899257243455552199495946008320,449262107459688071253265333937219808,
  -46898269052547894679895160659110256,5933512782748030308898751402098528,422755955763180403462293748816528,
  -68226116325837815159509355024256,-3664331627494743732330007545600,169515192327957951052700491776,
  21387712303951244382370332672,862036419350470131695222784,7539108308462036494319616
]
```

For a direct reconstruction of (100.5), put \(c=3+BK\) and
\(z_\pm=c\pm ib(1-3K)\). The original definitions give
\(\beta=R+z_+X\), \(\bar\beta=R+z_-X\), with
\(z_++z_-=2c\), \(z_+z_-=(B+9)a\). The two-dimensional determinant is
\[
 \operatorname{Nm}_{\rm rad}(R+zX)=R^2+Rzt/a-Rz^2/a.
\]
Consequently, if
\[
 H_\beta=(B+9)t^2-4(B+3)ct+144a-4Rc^2,\qquad
 P_\beta=D_s^2H_\beta(B,K,N_s/D_s),
\]
then \(\operatorname{Nm}_{\rm rad}(\beta\bar\beta)=R^2H_\beta/a\),
and the ordered product is
\[
\begin{split}
 \operatorname{Res}_K(F_0,P_\beta)
 ={}&2^{90}3^{22}B^{20}(B-1)^2(B+1)^{17}(B-3)^{18}(B+3)^{98}\\
 &\cdot Q_2^3L^2P_{48}^2P_{98}^4C_3C_{10}.             \tag{100.6}
\end{split}
\]
The \((K,B)\)-degrees of \(P_\beta\) are \((20,39)\); those of
\(F_0\) are \((10,18)\). The degree bound is 750. Evaluating the
fixed ordered Sylvester matrix at \(B=0,\ldots,750\) proves (100.6)
by (98.5); the product has degree 694.

For \(\sigma\), reconstruct \(E_n\) from (87.5) and take
\(\operatorname{Re}(E_n)/6=Au+D_0v+C_0\), \(\sigma=A^2+D_0^2\),
then substitute \((x,y)=(X,bKX)\). Its \(X\)-degree is six and
all powers of \(b\) are even. Define the exact polynomial quotient
\[
 H_\sigma(B,K,t)=
 \frac{\operatorname{Res}_X(aX^2-tX-R,\sigma(B,K,X))}
 {16a^3(B-3)^4}.                                        \tag{100.7}
\]
It has 186 terms and degrees \((11,6,6)\). This definition derives it
from the original equations, without an unprinted coefficient input.
Let \(P_\sigma=D_s^6H_\sigma(B,K,N_s/D_s)\). Then
\[
\begin{split}
 \operatorname{Res}_K(F_0,P_\sigma)
 ={}&2^{242}3^{10}B^{61}(B-3)^{70}(B+1)^{37}(B+3)^{296}\\
 &\cdot Q_2^6L^6P_{48}^6P_{98}^{12}S_{83}.             \tag{100.8}
\end{split}
\]
The degrees of \(P_\sigma\) are at most \((60,119)\), so the bound
is 2270. The complete exact checks at \(B=2,4,\ldots,4542\) establish
(100.8), whose right side has degree 2119. A specialization must retain
the symbolic degree 60, either by the fixed Sylvester matrix or its
leading-coefficient correction. These are integer identities, not
inferences from a modular pattern.

The rule \(\operatorname{Nm}_{F_0}(Q)=
\operatorname{Res}(F_0,Q)/\operatorname{lc}(F_0)^{\deg_KQ}\)
then gives
\[
\begin{split}
 \operatorname{Nm}(\beta\bar\beta)
 &=R^{20}\frac{\operatorname{Res}(F_0,P_\beta)}
 {\operatorname{Res}(F_0,a)\operatorname{Res}(F_0,D_s)^2},\\
 \operatorname{Nm}(\sigma)
 &=16^{10}R^{40}\frac{\operatorname{Res}(F_0,P_\sigma)}
 {\operatorname{Res}(F_0,D_s)^6\operatorname{Res}(F_0,a)^3}.
\end{split}
\]
Equations (100.3), (100.4), (100.6), (100.8) prove (100.5), including
both scalar constants.

The Bernstein coefficient lists (98.10) of \(C_3,C_{10}\) are
\[
\begin{gathered}
 441,398,1072/3,320;\\
 6561,9477,65313/5,171639/10,748458/35,175432/7,
 191376/7,137232/5,376576/15,104448/5,16384.
\end{gathered}
\]
They are strictly positive. The signed Sturm endpoint variations of
\(S_{83}\) are \((39,39)\), with nonzero endpoints. Hence both
norms in (100.5) are nonzero throughout the stated source domain.
Nonzero multiplication determinants imply units even in a nonreduced
algebra; multiplicativity
then makes \(\beta\) and \(\bar\beta\) individually units.

### 100.3. Exact radial norms of the two original linear pivots

Use \(a_Y,a_D,\mu_Y,\mu_D\) from (97.3), and substitute
\((x,y)=(X,bKX)\). The exact quotients
\[
 V_Y=a_Y/[2^{16}3^2(B+3)],\qquad V_D=a_D/[-2^{12}3b]
\]
are polynomials in \(B,K,X\) of \(X\)-degree fourteen. For either
\(V=\sum_{j=0}^{14}V_jX^j\), define
\[
\begin{gathered}
 P_0=0,\ P_1=1,\quad P_j=tP_{j-1}+RaP_{j-2},\\
 L_V=\sum_{j=1}^{14}V_ja^{14-j}P_j,\qquad
 C_V=V_0a^{13}+R\sum_{j=1}^{14}V_ja^{14-j}P_{j-1}.
\end{gathered}
\]
The remainder of \(a^{13}V\) modulo the radial equation is
\(L_VX+C_V\). Thus
\[
 \operatorname{Res}_X(aX^2-tX-R,V)
 =\frac{aC_V^2+tC_VL_V-RL_V^2}{a^{13}}
 =a^7R^8\mathcal H_V(B,K,t).                            \tag{100.9}
\]
Both divisions are exact polynomial divisions. They define
\(\mathcal H_Y,\mathcal H_D\) completely from the printed original
pivots. Their term counts and degrees in \((B,K,t)\) are respectively
\(1719;(23,14,14)\) and \(2079;(25,14,14)\).

Put \(\mathcal P_V=D_s^{14}\mathcal H_V(B,K,N_s/D_s)\), and
\(R_V=\operatorname{Res}_K(F_0,\mathcal P_V)\), retaining symbolic
\(K\)-degree 140 for the second argument. Its \(B\)-degree is at
most 275 for \(Y\), 277 for \(D\), so the resultant bounds are
5270 and 5290. The norm formulas, with all scalar factors, are
\[
\begin{split}
 \operatorname{Nm}(a_Y)
 &=\frac{(2^{16}3^2)^{20}(B+3)^{20}R^{80}R_Y}
 {\operatorname{Res}(F_0,D_s)^{14}\operatorname{Res}(F_0,a)^7},\\
 \operatorname{Nm}(a_D)
 &=\frac{(-2^{12}3b)^{20}R^{80}R_D}
 {\operatorname{Res}(F_0,D_s)^{14}\operatorname{Res}(F_0,a)^7}.
                                                               \tag{100.10}
\end{split}
\]
There is no factor \((B+3)^{20}\) in the second formula. The powers
of the decic leading coefficient cancel because \(140=14\cdot9+7\cdot2\).

Define
\[
\begin{split}
 Q_6&=9B^6+55B^5-581B^4+390B^3+2187B^2+675B+81,\\
 Q_8&=36B^8+1153B^7-8163B^6+20457B^5-106407B^4\\
    &\hspace{12mm}+440883B^3-628641B^2+299619B-24057,\\
 Q_{10}&=324B^{10}-1224B^9+289B^8-15316B^7+29116B^6+32580B^5\\
       &\hspace{12mm}+208710B^4+176148B^3+433512B^2+166212B+18225.
\end{split}                                                    \tag{100.11}
\]
Here \(Q_8(b^2)\) is exactly the collision polynomial of §95, and
\(Q_{10}(B)\) differs from the aligned \(A_{10}(b)\). Define the
remaining pivot polynomial by this complete coefficient list:

```text
Q90=[
  -4005048807989186562104915177737358400,-8790247748367933423286516957804806405,1380978839874562164726979915673259516990,
  -7386682486559236781271731145922863576672,-761515190702069323072671210176628839019819,-7799212877933246878948062475839486098892510,
  55329395025795374763573916296800848397792229,2022454087022543929330756178350855297409020065,22371161346232839076777815539800132820438973138,
  142311113483805973841670305903423456800872737535,582926755420409894694437328469566005036900887035,1601363154758666163936551685305220725652787887186,
  3080692605379499211399668844904641930026440794471,4503796075251241352499922724768751858935709819324,4281560701062345778293278558499161441319281341956,
  -5085482528460984177968975856322774881599301436563,-27565534748900408428460824290485012040237395581572,-15638085129294180805504162674482925987863108202912,
  90892272918353154230296565713301341009835166355368,133436852296212078631009018396320464460425005070244,-130187513433153555643626654146839994486731324558992,
  -278718342147548251822703612458778205815288270053272,331725978719150545953061073234353534124639124723132,817496445119479925405342172826130415051286335075540,
  -120228980557092373424842919970000595494873424042248,-1246519346891778724167297308318975215662418869498084,-754181301858754952712819033853513120719040097987244,
  348520576441980979763417243532955554560006210325528,522025659995662769829777502894181031100901087038668,73998190022122875302397782684041708846437153350688,
  -256146190119921514819696373286972936715696949775384,-30936230099947714633012595726295438304923240353868,473613159231717954091691652183832803902877332315328,
  267247042564306967774895699382042836482811166175850,-361198193470025427891196594780564217735649960829956,-296698432572826715200320557677941184538015502055680,
  132960790057561963952219654403685919877570419002854,167439863945139529218091435156083923460056434800876,18729133483218898825002781603192615236802232197326,
  -22744243311753512128312165529868740884792171949490,-17780169866085346412343768216244914137039594711892,-6199011469144884505932606065141443371039991261278,
  1849671018270914973723883341472941828100002416994,1530909734387086992897540600042933475051852189260,1365325513273022986330113145320180780111902754306,
  -219752017471455235245683732064623413156047861480,-523922581011623106464811305018465812602986640096,97026545744037742426752745468498949541294767334,
  3676427090830471438640975182858217128711474872,66800330783848625358206831185911617628732852516,-31081909652077786920593100271605809890870273152,
  -11042453834875015463256203718364067358738763320,12815533411719845053930658144696644841584120716,-6390230369392923451296291333058458170971976328,
  3788081992785436778607650659989386008857449820,-1953009058608374793069228485047811419600973916,396451151269829776506196467358121996616332664,
  303847080557852393964545584113563764806395820,-418842222982663170993460720346789277084610092,338119628394510929008042882262532790831144152,
  -223038818942155836098818761193868887670344260,125337032740520218306229813930331150909373440,-61177844908127308702441061632836890737592136,
  26570449263832816891722634950121621607056164,-10440084027993028879274792317985339375248608,3723767526060205891702483928541311676847059,
  -1201909484862333994129879003948151063513226,350415767638947923760842039961653034526272,-92249868813939991001294275958885549576691,
  21817463310732152820439534196540369026818,-4563922114042444331260462853625108456459,821970083548373960585033006443838844057,
  -122756157558569066309891213050390541550,14391318015263039348336461221215441559,-1186801439170240873359841650289909765,
  44207843123298116366237164231971698,3969785760380945911806644463224079,-731422090474620139237057461638644,
  32120842807310447021587600391100,3947502612936869756168361971413,-712576986497322514062612044500,
  43463065183824995200029378372,-104246783741232900216446296,-117706662039710492649645900,
  408079204072159411668284,693496168837343225121808,-34169264104804772513600,
  -608324304428388085248,73058982154568745984,401249132923981824,
  2603725458849792
]
```

The exact ordered product is
\[
\begin{split}
 R_Y={}&2^{556}3^{78}B^{142}(B-3)^{166}(B+1)^{78}(B+3)^{658}\\
      &\cdot Q_2^{14}L^{14}P_{48}^{14}P_{98}^{28}Q_6^2Q_8^2Q_{10}^2Q_{90}^2.
                                                               \tag{100.12}
\end{split}
\]
Its degree is 4940. The complete certificate evaluates the original
fixed-degree Sylvester determinant at \(B=2,4,\ldots,10542\).
All 5271 values equal (100.12), so its proved degree bound establishes
the identity over \(\mathbb Q[B]\). Combining with (100.10) gives
\[
 \operatorname{Nm}(a_Y)=
 \frac{2^{470}3^{104}(B-3)^{120}(B+1)(B+3)^{90}
 Q_6^2Q_8^2Q_{10}^2Q_{90}^2}{B^5W_{32}^7}.              \tag{100.13}
\]
The Sturm endpoint variation pairs for \(Q_6,Q_8,Q_{10},Q_{90}\) are
\((2,2),(5,3),(5,5),(47,45)\), and their endpoints are nonzero.
Thus only \(Q_8,Q_{90}\) contribute punctured pivot zeros.

For the alternate pivot, reduce the original \(R_D\) modulo 10007.
Reconstruct it by exact interpolation at \(B_j=2j+2\),
\(0\le j\le5290\). These nodes are distinct modulo 10007. Retain
both symbolic degrees ten and 140 even at a leading-degree drop; the
fixed Sylvester matrix is an unambiguous definition. The reconstruction
has degree 4960, and monic Euclid gives
\[
 \deg\bar Q_{90}=90,\qquad
 \gcd(\overline{R_D},\bar Q_{90})=1.                    \tag{100.14}
\]
Equations (100.1), (100.9) and this finite interpolation are complete
reconstruction instructions for the Bezout certificate; no modular
coefficient list is an input. Degree preservation of \(Q_{90}\)
proves \(\gcd_{\mathbb Q[B]}(R_D,Q_{90})=1\), by the same primitive
factor argument as (98.20). Therefore, away from
\(J_{\rm src}(b)Q_8(b^2)=0\), at least one of the full-algebra
multiplication norms of \(a_Y,a_D\) is nonzero.

### 100.4. A scalar-adjugate lift valid through each individual pivot zero

Let \(M_Y,M_D\) be the multiplication matrices of \(a_Y,a_D\)
in the fixed rank-twenty basis. Their structure constants are regular
away from \(J_{\rm src}=0\). Write their reduced rational-function
determinants as
\[
 n_Y=f_Y/d_Y,\qquad n_D=f_D/d_D.
\]
Choose integer-polynomial numerators and denominators with their actual
constant ratio retained, and compute the monic polynomial gcd and
Euclidean coefficients
\[
 g=\gcd(f_Y,f_D),\qquad u_0f_Y+v_0f_D=g.
\]
All these choices are exact scalar operations. Define the coordinate
column
\[
 \mathrm{Tau}=-\frac{
 u_0d_Y\operatorname{adj}(M_Y)\mu_Y+
 v_0d_D\operatorname{adj}(M_D)\mu_D}{g}.                \tag{100.15}
\]
Here \(\mu_Y,\mu_D\) mean their coordinate columns in the same basis.
Equation (100.14) shows that \(g\ne0\) throughout the target domain
\(J_{\rm src}Q_8\ne0\). In the coefficient field over
\(\mathbb Q(i)(b)\), both equations (97.3) hold for the same
\(\tau\), by the established original field identities of §89.
The adjugate identities and scalar Bezout equation prove
\(\mathrm{Tau}=\tau\) there. Every original identity therefore
holds with (100.15), and specializes wherever its actual denominators
are regular. This does not require a reduced fibre.

At an actual original selected-channel point one of \(M_Y,M_D\)
is invertible. Its equation (97.3) forces the original \(\tau\)
to equal (100.15). Formula (97.1), with the established unit \(\sigma\),
recovers its original \(u,v\) uniquely. The six root orders and the
optional \(\Theta\) choice remain distinct parts of the reconstruction.

Thus the two individual pivot inverses and individual pivot norm markings
can be replaced by (100.15). All actual denominators used in that formula,
including \(g\), are retained in any regenerated guard. Recompute the
subsequent original coefficients and overlap matrices using this lift;
retain their actual denominators and all their still-required markings.
The source and \(\beta,\bar\beta,\sigma\) norms have been accounted
for, but this argument does not declare the later guard empty.

## 101. Four additional linear-pivot fibres

Let \(Q_{90}(B)\) be the complete polynomial in §100 and put
\(Q_{180}(b)=Q_{90}(b^2)\).

**Theorem 101.1.** At each real \(0<|b|<1\) with \(Q_{180}(b)=0\),
no three original noncanonical common-flat rays are mutually orthogonal.
Every common-flat input orthonormal basis is the moving canonical basis,
up to column phases and permutations. The fixed pair \((I_6,H_0(b))\)
cannot belong to a quartet. There are exactly four parameters in this
statement, distinct from the twenty signed fibres in §§92–96.

### 101.1. Exact parameter field and good reduction

The following arrays, constant first, are the monic factors of
\(Q_{90}(B)\) modulo 73 and 97. Their products equal its respective
monic reductions, whose original leading residues are 18 and 10.

```text
factor73_1=[-6, 1]
factor73_2=[-13, -25, 17, 8, 5, 1]
factor73_3=[8, -28, 34, 11, -2, 10, -13, -31, -24, 1]
factor73_4=[34, -6, 20, 3, 2, 31, -5, -18, -30, 7, 3, 1, -16, 16, 36, 15, 32, 27, 0, 0, -36, 17, -31, 33, 6, -35, -23, 36, -20, -1, -33, 17, 34, -24, -19, 31, -27, 21, -10, -14, -27, -22, -20, 23, -10, 6, -3, 3, -7, 5, 34, -19, -4, -26, -4, 17, 30, 28, -23, 34, -35, 35, 34, -7, 25, -19, 1, 14, 20, -30, -22, -17, 19, -9, 16, 1]
factor97_1=[-20, 38, -36, -35, 44, -14, 25, -36, 43, -43, -16, 48, -41, 10, -41, -44, -29, 5, -5, -39, 11, -1, -19, -10, 24, 17, -12, -34, -35, 1]
factor97_2=[-44, 11, 27, -28, 26, 37, -7, 41, -6, -38, -47, -24, 48, 29, 7, 4, 41, -17, -13, -35, 39, -39, -3, -13, -17, -5, 13, 47, 34, 9, 36, 43, 18, -35, -43, -43, 47, -26, -15, 18, 44, -13, 20, -37, 22, -43, 13, -29, 6, -45, 29, 0, 31, 45, 32, 12, 31, 6, -20, 46, -9, 1]
```

For each factor \(f\) of degree \(n\), exact modular exponentiation
verifies \(B^{p^n}=B\bmod f\), and
\(\gcd(f,B^{p^{n/r}}-B)=1\) for every prime \(r\mid n\).
The factor degrees are \((1,5,9,75)\) at 73 and \((29,61)\) at 97.
Their possible proper subset degrees have empty intersection, proving
irreducibility of \(Q_{90}\) over \(\mathbb Q\).
The norm of its root is
\[
 -3179336870641215263572082490075/2066921216<0.
\]
A square in this degree-ninety number field has nonnegative rational norm.
Thus adjoining \(b\), with \(b^2=B\), doubles the degree and proves
that \(Q_{180}\) is irreducible of degree 180.

The exact Sturm variations of \(Q_{90}\) at 0 and 1 are \((47,45)\),
and neither endpoint is a root. Its two roots in \((0,1)\) give
exactly four signed punctured parameters. This is an interval count:
the variation at \(+\infty\) is 38, so there are nine positive
\(B\) roots globally and eighteen real \(b\) embeddings globally.
A real embedding excludes \(i\) from \(\mathbb Q[b]/(Q_{180})\),
so \(Q_{180}\) remains irreducible over \(\mathbb Q(i)\).
Work in the field
\[
 \mathbb K=\mathbb Q(i)[b]/(Q_{180}).
\]
Exact Euclidean gcds with
\(L(b^2),P_{48}(b^2),P_{98}(b^2),Q_8(b^2),A_{10}(b),A_{14}(b)\)
are all one. Thus none of the earlier twenty signed exceptional fibres
is being recounted.

Use the good map \((p,b,i)=(101,19,10)\). Direct evaluation gives
\(Q_{180}(19)=0\bmod101\), and \(10^2=-1\).
Every nonzero residue below proves a nonzero element of \(\mathbb K\),
hence nonvanishing at every embedding, including all four with
\(0<|b|<1\). Denominators are checked before reduction. A zero residue
is never used to assert a characteristic-zero identity.

### 101.2. Complete original source and primitive element

Use the original unscaled source minor \(M\), its complementary basis
\(\mathcal B_0\), and vertical minor of §§88,98. The residues are
\[
 \det M=52,\qquad \det V_*=10\pmod{101}.
\]
Let \(C_s\) be the selected 30 source basis columns. The expressions
of nonbasis monomials are the rows of \(-M^{-1}C_s\); basis monomials
have their standard columns. Define the \(30\times30\) border matrices
\(K_s,T_s\) by the one-step \(k,t\) multiples of each basis monomial.
These lie within degree 19. The characteristic-zero commuting,
source-annihilation and cyclic-constant-vector identities of §93.2
specialize through \(\det M\ne0\). Conversely the same border relations
span the entire source quotient. Thus its dimension remains exactly 30,
including the nonreduced complementary components, before any linear
lift is chosen. The vertical minor excludes missing projective means
with \(x=0\).

Let \(P_{\rm other}=\prod_{j=1}^5P_j\) and construct
\[
 e(k)=P_{\rm other}(k)[P_{\rm other}^{-1}\bmod F]
                  \pmod{FP_{\rm other}},\qquad E=e(K_s).
\]
The separation resultant is 87 modulo 101. Take
\(J=E_{[:,0:10]}\), \(J_0=J_{[0:10,:]}\); its determinant is 91.
The induced matrices and constant column are
\[
 K_g=J_0^{-1}(K_sJ)_{[0:10,:]},\quad
 T_g=J_0^{-1}(T_sJ)_{[0:10,:]},\quad
 {\bf1}_g=J_0^{-1}(E{\bf1})_{[0:10]}.
\]
All ranks are characteristic-zero ranks: \(E^2=E\) and
\(\operatorname{tr}E=10\) specialize, and the displayed minor selects
its full image. The five other components have no real projective points
on the puncture by §88.3, so every original generic mean is in this
image.

For \(W=K_g+T_g\), the power columns
\({\bf1}_g,W{\bf1}_g,\ldots,W^9{\bf1}_g\) have determinant 44.
Let \(f_W\) be its characteristic polynomial and express
\(K_g{\bf1}_g,T_g{\bf1}_g\) in these columns to obtain
\(k=k(w),t=t(w)\). This defines the polynomials over \(\mathbb K\),
not merely in a residue field. As a normalization check, the reduction is
\[
 f_W(w)=w^{10}-41w^9+w^8-23w^7-23w^6-28w^5-29w^4
        -2w^3+46w^2+28w-32\pmod{101}.
\]
The complete radial algebra is
\[
 \mathcal A=\mathbb K[w,X]/
 \bigl(f_W(w),(1+k(w)^2)X^2-t(w)X-R\bigr),              \tag{101.1}
\]
with ordered basis \((1,w,\ldots,w^9,X,Xw,\ldots,Xw^9)\).
The norms of \(1+k^2,f_W',t^2+4R(1+k^2)\) are \(47,33,17\).
The norm of \(y=kX\) is 38 and the determinant of its twenty power
columns is 85. These certify the alternative power basis used below.

### 101.3. The alternate original linear lift

Construct the global original coefficients from §87, and use
\[
\begin{split}
 \tau&=-(\mu_Y+\mu_D)/(a_Y+a_D),\\
 u&=(-AC_0-D_0\tau)/\sigma,\qquad
 v=(-D_0C_0+A\tau)/\sigma.                              \tag{101.2}
\end{split}
\]
The norm residues of \(a_Y+a_D,a_D,\sigma,\beta,\bar\beta\) are
\(15,44,46,38,72\). Thus this lift is regular. It also equals
\(-\mu_D/a_D\). The actual failure of \(a_Y\) as an algebra unit
follows from the characteristic-zero identity (100.13), rather than its
zero residue at the good map.

Original source necessity and (97.3) hold at every leading or pivot zero.
Therefore each actual selected generic ray belongs to (101.1), and its
original line coordinates are forced by (101.2). No \(F_8\) unit has
been assumed in establishing coverage. Over the generic coefficient
field, the original identity \(a_Y\mu_D-\mu_Ya_D=0\) identifies
(101.2) with the old lift. Rewrite the established original equations
and overlap identities using this regular expression before specializing.
Their coefficients have only the checked denominators, so their vanishing
in characteristic zero specializes legitimately.

The remaining complete coordinate norm inventory is

```text
Yc*barYc:25; barC*D:58; C*barD:81;
C:17; barC:56; D:84; barD:82; Yc:78; barYc:56;
q:95; e:71; bare:78; F8:46; G:46; barG:93;
Delta:36; delta:76.
```

All are multiplication determinants in (101.1), with the original
§87 formulas and \(\Delta=D\bar D-C\bar C\). Hence each indicated
inverse is legal at every embedding. Physical reconstruction still uses
\(0<q<1\), \(\delta<0\), and the unscaled coefficients
\(G/\kappa,C/\kappa,D/\kappa\), where
\(\kappa=(b-i)\sqrt{(3-b^2)/(1+b^2)}\).
All six root orders and optional channel choice remain.

### 101.4. Generic and mixed overlap certificates

Evaluate the complete all-six-order polynomial \(\mathcal N\) of
§79 at the ordinary arguments of §89, using the new exact arrays,
to obtain \(N\in\mathcal A\otimes\mathcal A\). The involution
\(\iota(k)=k\), \(\iota(X)=t/(1+k^2)-X\) defines the split map
\(\rho(a\otimes c)=a\iota(c)\). The original characteristic-zero
branch identity \(\rho(N)=0\) specializes by (101.2). Thus the
multiplication image is contained in its 380-dimensional kernel.
In basis \(y^r\otimes y^s\), indexed by \(20r+s\), the leading
\(380\times380\) principal minor is **31 modulo 101**. It follows
in characteristic zero that
\[
 N(\mathcal A\otimes\mathcal A)=\ker\rho.               \tag{101.3}
\]
The element \(1+\bar GG'/R\) belongs to this kernel. Evaluation at
an arbitrary original orthogonal pair gives \(G'=-R/\bar G\).
The \(\Delta\) unit makes the other channel three-distinct, and unique
original lifting identifies the second point with the \(\Theta\)
coefficient point. Hence each edge lies in the \(S_3\)-\(\Theta\)
union of its endpoints. The uniform within-union bipartite theorem
excludes all-generic noncanonical triples. Optional \(\Theta\) parity
is handled by its actual channel transport, not by imposing ordinary
and symplectic equations simultaneously.

For aligned rays use the original quintic and shape of §90. The residues
of \(r_0,r_2,\operatorname{lc}Q_5,A_{10}\) are \(38,81,27,18\).
The norm inventory in the quintic algebra is

```text
D:81; V:13; K=D^2+4T:92; J=bD-T+3:65; Fa=D^2+(T+1)^2:40;
(2-iD)^2+K:91; (2+iD)^2+K:24.
```

This covers all original rank deficiencies, poles and constant-channel
cases by §90. Adjoin both signs of \(s^2=K\), obtaining dimension ten.
Form the exact mixed norm (90.14), retaining its printed barred \(C\)
coefficient. Its multiplication determinant on the 200-dimensional
mixed tensor algebra is **13 modulo 101**. It is therefore invertible
in characteristic zero and excludes every original generic–aligned
orthogonal pair. The norm construction retains all three positions,
both aligned signs and all generic root orders.

### 101.5. Complete triple and basis conclusion

The §75 charts cover every noncanonical ray: either a selected channel
has three distinct entries, or the channels share a repeated pair,
including a constant channel when present. All-generic triples are
excluded by (101.3); any mixed triple contains the forbidden mixed
edge; all-aligned triples are uniformly excluded by §85.
A common-flat basis with a canonical ray is canonical by §60; one with
none would contain a forbidden noncanonical triple.

An output basis \(\mathcal B\) common-unbiased to \((I_6,H_0)\)
corresponds to the common-flat input basis \(H_0^*\mathcal B\).
Conversely multiply an input basis by \(H_0\). This unitary transport
preserves orthogonality and all relevant unbiasedness norms. Uniqueness
of the input canonical basis gives uniqueness of the output common-
unbiased basis. Two further mutually unbiased complete bases cannot both
be that same basis up to phases and permutations. This proves the
fixed-pair quartet exclusion in Theorem 101.1.

Finally, the already proved finite guard has finitely many real zeros.
Each of these four closed points has an open parameter neighborhood
containing no other zero of that guard. The existing safe-parameter
result and Theorem 101.1 therefore give the same basis and quartet
conclusion throughout that neighborhood. Its radius is existential;
no other exceptional fibre is closed by this argument.

## 102. Physical channel collisions and an exact regenerated finite guard

### 102.1. The necessary parameter condition for a channel collision

We first prove the original-equation implication
\[
 \begin{gathered}
 0<|b|<1,\quad\text{one channel three-distinct and the other two-valued}
 \\\Longrightarrow\quad Q_8(b^2)=0,                    \tag{102.1}
 \end{gathered}
\]
where \(Q_8\) is (100.11). Only necessity is required here; no count
or existence assertion is used in the proof.

Use the original unit-entry input convention \((x,y/\kappa)\), with
\(|x_j|=1\), \(|y_j|^2=R\). By a simultaneous permutation and common
phase, an ordered repeated-lower pair has the form
\[
 x_1=u+iv,\quad x_2=u-iv,\quad x_3=a+ic,\quad
 v=\sqrt{1-u^2}>0,\quad y_1=y_2=P+iQ.
\]
This includes the antipodal case \(u=0\). Upper three-distinctness
implies \(a-u\ne0\). Initially let \(y_3=e+if\) be arbitrary.
The two output differences from (78.1), divided only by \(2v\), are
\[
\begin{split}
 2Q-ab-2bu-3c+f&=0,\\
 -4Qb+ab^2-3a-b^3c-b^2e+2b^2u+3bc-2bf-3e-6u&=0.
\end{split}
\]
Their determinant in \((e,f)\) is \(b^2+3\). Therefore, necessarily,
\[
 p=P+iQ,\qquad q=-2u-a-bc+i[b(2u+a)+3c-2Q],\qquad
 y=(p,p,q).                                             \tag{102.2}
\]

For fully reconstructible elimination, let \(X=2u+a+ic\), \(Y=2p+q\),
and denote the two real original output forms by
\[
\begin{split}
 S(\xi,\eta)={}&|X|^2+|Y|^2/R+
 \operatorname{Re}[(-3+ib)\bar X\xi-\bar X\eta
       +\bar Y\xi+(-3-ib)\bar Y\eta/R],\\
 D_o(\xi,\eta,\zeta)={}&\operatorname{Re}[2(b+i)\bar XY
 +R(b+i)\bar X\xi+(-2b-i(3+b^2))\bar X\eta\\
 &\hspace{9mm}+(-2b+i(3+b^2))\bar Y\xi
 -(b-i)\bar Y\eta+2i(3+b^2)\zeta].
\end{split}
\]
These are precisely (78.1). Define the six real polynomials
\[
\begin{gathered}
 F_1=RS(u,p),\quad F_2=D_o(u,p,up),\quad
 F_3=D_o(a+ic,q,(a-ic)q),\\
 F_4=P^2+Q^2-R,\quad F_5=|q|^2-R,\quad F_6=a^2+c^2-1.
                                                               \tag{102.3}
\end{gathered}
\]
The denominator in \(F_1\) cancels. Exact expansion gives
\(S(x_1,p)=S(x_2,p)=F_1/R\), \(S(x_3,q)=-2F_1/R\),
and the three \(D_o\) forms are \(F_2,F_2,F_3\).
Thus every original collision solves (102.3); these definitions also
reconstruct all six equations directly from the original matrix.

Put \(t_0=a-u\ne0\) and divide the five real variables by \(t_0\).
Write their normalized values as
\[
 u/t_0=k,\quad a/t_0=k+1,\quad c/t_0=c_0,\quad
 (p-q)/t_0=L+iM.
\]
For the algebra below rename \(c_0\) as \(c\). The normalized
substitution is
\[
 u=k,\quad a=k+1,\quad
 P=L-3k-1-bc,\quad Q=(M+b(3k+1)+3c)/3.                \tag{102.4}
\]
Define \(g_1,\ldots,g_5\) by this substitution into
\((F_1,F_2,F_3,F_4-RF_6,F_5-F_4)\). These combinations are homogeneous
of degree two in the five original variables, so every physical point
solves them after normalization. Retain \(L^2+M^2>0\).
The omitted input norm gives \(t_0^2((k+1)^2+c^2)=1\); it is not
needed for the following necessary elimination.

Set \((h_1,h_2,h_3)=(g_1/2,g_5/2,(g_3-g_2)/2)\).
Each is affine-linear in \((k,c)\). Define its coefficient matrix by
\(h_j=H_{j1}k+H_{j2}c+H_{j3}\), and put
\[
\begin{split}
 d_0&=H_{11}H_{22}-H_{12}H_{21},\quad
 k_0=H_{12}H_{23}-H_{22}H_{13},\\
 c_0&=H_{21}H_{13}-H_{11}H_{23},\qquad a_0=\det H.
\end{split}
\]
Here \(c_0\) is a Cramer numerator, no longer the earlier normalized
coordinate label. Direct expansion gives
\[
 d_0=-(b^2-3)(3LM+6Lb+M^2b+Mb^2-9M)/3.                \tag{102.5}
\]
Consistency requires \(a_0=0\); if \(d_0\ne0\),
\(k=k_0/d_0,c=c_0/d_0\).

### 102.2. Exceptional elimination charts

If \(L=0\), then \(M\ne0\). A vanishing \(d_0\) would give
\(bM+b^2=9\), while
\(c_0=M^2(bM+b^2-3)/2=3M^2\ne0\), contradicting consistency.
For \(d_0\ne0\), let
\[
 n_j=\sum_{r,s}[k^rc^s]g_j\ k_0^rc_0^sd_0^{2-r-s},
 \qquad j=2,4.
\]
For a rational-coefficient polynomial \(P\), let \(\operatorname{Int}P\)
mean multiplication by the least positive integer clearing all its
coefficient denominators; no content or sign is subsequently removed.
Define, at \(L=0\),
\[
 z_1=\operatorname{Int}(a_0/M^2),\quad
 z_2=\operatorname{Int}(n_2/[M^3(b^2-3)]),\quad
 z_3=\operatorname{Int}(n_4/[M^2(b^2-3)]).
\]
These are polynomials. The monic gcd in \(\mathbb Q[b]\) of their
three pairwise ordered \(M\)-resultants is
\((b^2-3)^3(b^4+22b^2+25)\), which is nonzero for \(|b|\le1\).
Thus \(L=0\) is impossible.

Now \(L\ne0\); set \(r=M/L\). Under this substitution define
\(d=d_0/L,\ \widehat k=k_0/L,\ \widehat c=c_0/L^2\).
The exact identities are
\[
\begin{split}
 \operatorname{Res}_L(d,\widehat c)
 &=-(r-b)(b^2-3)(r^2+1)(br-3),\\
 \operatorname{Res}_L(d,\widehat k)
 &=(r-b)^2(b^2-3)^2(r^2+1)(b^2r+6b-9r)/3.
\end{split}                                                    \tag{102.6}
\]
If the minor vanishes, consistency forces both numerators to vanish.
For real \(|b|\le1\), (102.6) implies \(r=b\): the alternative
\(br=3,\ b^2r+6b-9r=0\) would give \(b^2=3\).

The entire branch \(r=b\), including nonsingular points, is excluded
as follows. The fifth equation gives \(L=6k+2\). The first then factors as
\[
 -2(bc+3k+1)[2(b^2+3)k+b^2+1]=0.
\]
In the first factor, \(b=0\) would force \(L=0\). For \(b\ne0\),
substitute \(c=-(3k+1)/b\). The next equation is
\(-2k(b^2+1)(b^2+3)(3k+1)/b=0\). Since \(L\ne0\), it forces
\(k=0\), and the third equation becomes
\(2(b^2+3)(b^2+1)/b\ne0\). In the other factor,
\(k=-(b^2+1)/(2(b^2+3))\), the fourth equation is
\[
 2(b^2-1)c^2+\frac{b^6+b^4-b^2-33}{2(b^2+3)^2}<0
 \quad (|b|\le1).
\]
Consequently every possible original collision has
\(L\ne0,r\ne b,d_0\ne0\). No hypothesis on either channel mean
or an individual single-ray chart denominator entered this argument.

### 102.3. Complete necessary parameter resultant

Define the three polynomials
\[
 A=\operatorname{Int}(a_0),\quad
 B_1=\operatorname{Int}(n_2/[(L^2+M^2)(b^2-3)]),\quad
 E_1=\operatorname{Int}(n_4/(b^2-3)).
\]
After \(M=rL\), put \(a_r=A/L^2,b_r=B_1/L,e_r=E_1/L^2\).
They have \(L\)-degrees 2,3,4. The leading coefficient of \(a_r\) is
\(-(b^2+3)T\), where
\[
 T=(b^2-12)r^4+18br^3-(3b^2+27)r^2+18br-27.
\]
For \(|b|\le1\), the inequalities
\(18|r|^3\le9r^4+9r^2\), \(18|r|\le9r^2+9\) give
\(T\le(b^2-3)r^4-(3b^2+9)r^2-18<0\).
Thus this leading coefficient never drops in the real target domain.

Use the standard fixed-degree pseudo-remainder
\(\operatorname{prem}_L(f,g)=\operatorname{rem}_L
(\operatorname{lc}(g)^{\deg f-\deg g+1}f,g)\).
The exact polynomial divisions
\[
 B_*={\operatorname{prem}_L(b_r,a_r)\over
 108(r-b)(b^2-3)(r^2+1)},\qquad
 E_*={\operatorname{prem}_L(e_r,a_r)\over
 648(r-b)(b^2-3)^2(r^2+1)}
\]
give two affine polynomials in \(L\). Every displayed divided factor
has now been proved nonzero at a physical solution.
The following three explicit polynomials use variables \(b,r\):

```text
W=b^4*r^4 + 2*b^4*r^2 + b^4 - 16*b^3*r^3 - 16*b^3*r + 22*b^2*r^4 + 44*b^2*r^2 + 6*b^2 - 32*b*r^3 + 25*r^4 + 18*r^2 + 9
U=b^7*r^6 + 2*b^7*r^4 - 15*b^7*r^2 + 24*b^6*r^5 + 132*b^6*r^3 - 36*b^6*r - 30*b^5*r^6 - 177*b^5*r^4 + 504*b^5*r^2 + 27*b^5 - 126*b^4*r^5 - 2088*b^4*r^3 - 378*b^4*r + 171*b^3*r^6 + 2610*b^3*r^4 + 675*b^3*r^2 + 972*b^3 - 864*b^2*r^5 + 1404*b^2*r^3 - 1620*b^2*r - 54*b*r^6 - 2187*b*r^4 - 324*b*r^2 - 1215*b + 486*r^5 + 648*r^3 + 1458*r
V=b^8*r^4 - 3*b^8*r^2 + 30*b^7*r^3 - 18*b^7*r - 27*b^6*r^4 + 234*b^6*r^2 - 27*b^6 - 468*b^5*r^3 + 540*b^5*r + 234*b^4*r^4 - 1998*b^4*r^2 + 2214*b^3*r^3 - 810*b^3*r - 729*b^2*r^4 + 2106*b^2*r^2 + 243*b^2 - 1296*b*r^3 + 81*r^4 - 243*r^2
```

Direct ordered resultants give
\[
\begin{split}
 \operatorname{Res}_L(B_*,E_*)&=-9(b^2+3)^3T^2WU,\\
 \operatorname{Res}_L(a_r,B_*)&=-36(b^2-3)(b^2+3)^3T^2WV,\\
 \operatorname{disc}_rW&=589824(b^2-15)^2(b^2-3)^2(b^2+1)^6.
\end{split}                                                    \tag{102.7}
\]
The leading \(r\)-coefficient of \(W\) is \(b^4+22b^2+25>0\).
Neither it nor the discriminant vanishes on \([-1,1]\).
At \(b=0\), \(W=25r^4+18r^2+9>0\). Continuity of roots, with
no multiple root or loss of degree, proves \(W>0\) for real \(r\)
throughout this interval. Hence a physical solution must satisfy \(U=V=0\).
Finally
\[
\begin{split}
 \operatorname{Res}_r(U,V)
 ={}&4897760256b^2(b^2-3)^7(b^2+3)^7Q_-Q_+P_{12}Q_8(b^2),\\
 Q_-={}&(b^2-3b+3)^2+3b^2,\quad Q_+(b)=Q_-(-b),\\
 P_{12}={}&4b^{12}-147b^{10}+1494b^8-7695b^6+16281b^4+6318b^2+729.
\end{split}                                                    \tag{102.8}
\]
Both \(Q_\pm\) are strictly positive. For \(|b|\le1\),
\(P_{12}\ge4b^{12}+1347b^8+8586b^4+6318b^2+729>0\).
Every other factor of (102.8) is nonzero on \(0<|b|<1\).
This proves (102.1) with all elimination charts retained.
All polynomials and resultants in (102.5)–(102.8) are reconstructed by
(102.2)–(102.4); no numerical classification is a premise.

### 102.4. The channel determinant needs a physical exception, not an algebra unit

For an actual selected generic ray, §75 gives the unique interpolation
\[
 y_{\rm unit}=A\mathbf1+c x+d\bar x,\qquad c,d\ne0,
\]
with physical \(c=C/\kappa,d=D/\kappa\). Therefore
\[
 \Delta=D\bar D-C\bar C=R(|d|^2-|c|^2).
\]
The real-linear map \(z\mapsto cz+d\bar z\) has determinant
\(|c|^2-|d|^2\). If \(\Delta=0\), it has rank one; rank zero would
force \(c=d=0\). Its affine image is a real line, which meets the unit
circle in at most two points. The lower channel cannot be constant:
otherwise \(cx_j^2+(A-y_0)x_j+d=0\) at three distinct upper entries,
forcing this quadratic to be identically zero. Thus its lower channel
is exactly two-valued. Applying (102.1) gives
\[
 \Delta=0\text{ at an original generic point}
       \quad\Longrightarrow\quad Q_8(b^2)=0.           \tag{102.9}
\]
At \(Q_8(b^2)\ne0\), the real-linear map is invertible, so the other
channel is three-distinct as well. Both means are nonzero by §75.
The actual \(\Theta\) ray therefore has its strict selected-channel
chart. This statement concerns original physical points; it does not
claim \(\Delta\) is a unit at every complex algebra point.

No algebraic step in the ordinary or mixed norm construction in
§§89–90 divides by \(\Delta\). The radial involution, \(\rho\),
and \(1+\bar GG'/R\) contain no \(\Delta\) inverse. Its norm is
computed by a determinant, which also requires no inverse.
Thus its separate required-nonzero norm marking may be replaced by
\(Q_8(b^2)\), retaining the old norm's actual scalar denominators.
The finite-free specialization proof of §97.3 still gives the exact
kernel identity. At an arbitrary physical orthogonal pair it forces
\(G'=-R/\bar G\); (102.9) and unique lifting identify this with
\(S_3\Theta\) of the first ray. The unchanged mixed determinant
supplies the mixed exclusion. This proves the replacement without
weakening the strict physical cubic test \(\delta<0\).

### 102.5. An explicit finite construction and its exact boundary

The following deterministic rules specify new nonzero integer guard
polynomials; an expanded polynomial is not required to define them.
Start with the exact scalar, matrix and norm constructions of §§89–90,
including their declared order and normalization of algebra bases.

1. Replace only the source-completeness marking \(E_*\) by
   \(J_{\rm src}\), using Theorem 98.1. Keep the decic and radial
   structure constants and their actual denominators.
2. Derive the line identities without \(F_8^{-1}\) by (97.2), and
   use the scalar-adjugate formula (100.15) instead of the obsolete
   individual pivot inverse. Do not compute either discarded pivot
   inverse or require either individual pivot norm. Include the actual
   denominators of (100.15), including \(g\), and mark
   \(J_{\rm src}Q_8(b^2)\) as required nonzero. The two pivot norms
   used to define its scalar gcd are computed as determinants.
3. Reconstruct all subsequent original coefficients, the power-basis
   change and the ordinary overlap matrix with this lift. Keep every
   actual reduced scalar denominator. Keep every original required
   norm or minor except the four separate markings
   \(\operatorname{Nm}(F_8),\operatorname{Nm}(d_{\rm rad}),
   \operatorname{Nm}(\delta),\operatorname{Nm}(\Delta)\).
   Retain even the reduced denominators of these four computed norms.
   Their removal is justified by §§97,102.4, not by an assumed lack
   of real roots. The original coefficient units, including
   \(C,D,Y_c\) and their bars, and the power-basis and rank minors,
   remain required. The \(\beta,\bar\beta,\sigma\) inverses remain
   constructed; (100.5) proves their norms nonzero on the source domain.
4. For the generic guard \(G_{\rm new}\), take the primitive integer
   part, with positive leading coefficient, of the product of all these
   reduced scalar denominators and required-nonzero scalar numerators,
   together with their coefficient conjugates, as in §89.3.
5. For the full guard \(H_{\rm new}\), include additionally the aligned
   construction, its actual scalar denominators, the factor
   \(A_{10}A_{14}\), and the unchanged mixed multiplication determinant.
   The aligned coordinate/unit markings in Theorem 99.1 may be replaced
   by \(A_{10}A_{14}\); their actual inverse arrays and all their
   reduced denominators remain. Apply the same integer normalization.

No proof-only resultant or temporary matrix inverse is inserted into
these construction lists. A denominator actually used by a retained
coefficient array is never discarded just because its zero lies in a
separately studied family. Rational functions are reduced in
\(\mathbb Q(i)(b)\) before their numerator and denominator are recorded.
The construction is finite, and every listed denominator or required
numerator is nonzero at \(b=1/2\). For the new scalar \(g\), this
follows from the nonzero half-parameter pivot norm; for all unchanged
arrays it is their established half-parameter certificate. Thus both
guards are nonzero polynomials.

**Theorem 102.1.** At \(G_{\rm new}(b)\ne0\) in the real puncture,
every orthogonal pair of original generic noncanonical rays has its
second endpoint in \(S_3\Theta\) of its first. At
\(H_{\rm new}(b)\ne0\), there is no noncanonical orthogonal triple;
the canonical common-flat basis is unique up to phases and permutations,
and the fixed pair \((I_6,H_0(b))\) cannot belong to a quartet.

Indeed source coverage and unique original lifting follow from
§§98,100. The finite-free kernel argument of §97.3 and the physical
transport (102.9) prove the per-edge conclusion. Each generic edge
lies entirely within its endpoints' orbit union, whose graph is
bipartite by §82. The mixed determinant excludes mixed edges, while
§85 excludes all-aligned triples. These are the complete §75 classes,
including constant channels in the aligned class. Finally §60 and
the explicit input/output transport in §101.5 prove the basis and
quartet conclusions.

All previously closed fibres remain valid independently. To express
maximal removal of their factors without assuming any other root has
been classified, set
\[
 J_{24}=J_{\rm src}\,Q_8(b^2)A_{10}A_{14}Q_{180}.
\]
Its real punctured zero set consists of exactly 24 distinct signed
parameters, by §§92–96 and101. Starting with \(H_{\rm new}\), repeatedly
divide by its monic gcd with \(J_{24}\) until that gcd is constant,
and clear any rational scalar content with positive-leading primitive
integer normalization. Call the result \(H_{\rm res}\).
This finite procedure removes every primary power supported on these
known factors and no other factor. If \(H_{\rm res}(b)\ne0\), then
either \(H_{\rm new}(b)\ne0\) or \(J_{24}(b)=0\); both cases
have the asserted triple, basis and fixed-pair conclusion.

Every other root of \(H_{\rm res}\) remains an exception to this
particular guard implication unless independently closed elsewhere.
No assertion is made that the regenerated guard has fewer real zeros
than an earlier one, or that the residual guard has no real punctured
root. The remaining obligations are the actual retained reconstruction,
power-basis and overlap guards. No exceptional fibre is removed by density.

## 103. Original generic reconstruction units on the complete source algebra

### 103.1. Statement and retained domain

Use the actual paired-circulant family, original input convention and
complete generic source algebra of §§87–102. In this note
B=b² and R=3−B; the earlier original-equation symbol B is therefore
written B+3 here. Let Jsrc=L(B)P48(B)P98(B), up to the harmless
nonzero constants used in §98. Let Q8 be (100.11).

**Theorem 103.1.** At every real 0<|b|<1 with Jsrc Q8!=0, the
original scaled interpolation coefficients C,D,Yc and their coefficient
conjugates are units in the full rank-twenty source algebra. The same holds
for the original T and its conjugate. Together with the source,
beta,barbeta,sigma and scalar-adjugate lift results, this proves that every
original generic reconstruction-unit marking and every actual denominator
in those reconstruction arrays is regular and nonzero as required on this
domain. This includes the Q90 pivot fibres: no individual aY inverse is
used when specializing there.

The physical coefficients are G/kappa,C/kappa,D/kappa as in §87.1.
The assertion concerns the scaled original quotient, with this convention
unchanged. All six root orders and both channel choices remain available.
Every physical strict test, especially 0<q<1 and delta<0, is retained.
No ordinary or mixed overlap determinant is claimed nonzero here.

### 103.2. Global polynomial numerators from original equations

Set G=x+iy, alpha=3−ib−barG, beta=R+(3+ib)barG. Reconstruct
A,D0,C0,sigma=A²+D0² from the original En by (87.5)–(87.6).
Use the global linear identity aY*tau+muY=0 of (97.3). Define

Cpol=[−(A+iD0)C0*aY+(D0−iA)muY−sigma R alpha aY/2]/(sigma beta),
Dpol=[ (A−iD0)C0*aY−(D0+iA)muY−sigma R baralpha aY/2]/(sigma beta).

These are exact polynomial divisions in Q(i)[b,x,y]. The quotients have
2113 and 2258 nonzero terms, respectively, and degrees at most (28,14,14)
in (b,x,y). In the aY unit chart, direct substitution into the original
formulas gives C=Cpol/aY and D=Dpol/aY. This is an identity of rational
functions, proved by exact polynomial multiplication; it makes no division
by A or F8 and loses no leading stratum.

Let h=2^16*3² and put CN=Cpol/h, DN=Dpol/h,
VY=aY/[h(B+3)]. Thus C=CN/[(B+3)VY] and D=DN/[(B+3)VY].

For the original T in (87.2), write

L=R(b+i)+(−2b+i(B+3))barG,
N=−2b−i(B+3)−(b−i)barG,
Tpol=[3L−2i(B+3)barG]aY+3N Cpol
     +[3barN−4i(B+3)]barDpol+2i(B+3)barCpol.

The exact quotient TN=Tpol/[6 i h(B+3)] is a polynomial, and
T=6i TN/VY. The construction uses only original equations and polynomial
operations. In particular it does not invert Yc or assume Yc is a unit.

### 103.3. Complete radial reconstruction

Use K=k/b, a=1+BK², F0,Ds,Ns and t=Ns/Ds of (100.1), and substitute
x=X,y=bKX. The first quotient uses F0 divided by its leading coefficient; the
second uses (aX²−tX−R)/a, so both defining polynomials are monic. Their rank is twenty. The source
proof gives the required a and Ds units, including nonreduced radial fibres.

For any V=sum(j=0..n)Vj X^j, set P0=0,P1=1 and
Pj=t P(j−1)+Ra P(j−2). Define

LV=sum(j=1..n)Vj a^(n−j)Pj,
CV=V0 a^(n−1)+R sum(j=1..n)Vj a^(n−j)P(j−1).

The remainder of a^(n−1)V is LV X+CV, hence

Res_X(aX²−tX−R,V)=[a CV²+t CV LV−R LV²]/a^(n−1).

Every division used below is an exact polynomial division. Applying this
formula with n=14 to CN,DN and n=15 to TN gives

Res_X(radial,CN)=a^7 R^8 HC,
Res_X(radial,DN)=a^6 R^8 HD,
Res_X(radial,TN)=a^7 R^8 HT.

Write HV=HV0+i b HV1, with HVj in Z[B,K,t]. Their complete definitions
are the preceding original-polynomial and radial operations. The following
term counts, contents and degree bounds provide reconstruction checks:

C0:2104 terms, content1, degrees(27,14,14);
C1:2038 terms, content6, degrees(25,14,14);
D0:2532 terms, content1, degrees(28,16,14);
D1:2484 terms, content2, degrees(27,16,14);
T0:2513 terms, content1, degrees(28,16,15);
T1:2536 terms, content1, degrees(27,16,15).

The degree triples refer to(B,K,t), and the term counts are unchanged by
removing the stated integer content. No stored coefficient list is needed
to define any HV.

### 103.4. Three ordered outer-resultant identities

Put PC=Ds^14 HC(B,K,Ns/Ds), PD=Ds^14 HD(B,K,Ns/Ds),
PT=Ds^15 HT(B,K,Ns/Ds). Define RC,RD,RT as the ordered resultants
Res_K(F0,PV), retaining the declared symbolic degrees of both arguments.
F0 has K-degree10 and b-degree36. The second-argument K-degrees,
b-degree bounds, and resulting Sylvester b-degree bounds are:

C:140,558,10620;
D:142,560,10712;
T:151,596,11396.

The bound is 10*(second b-degree)+36*(second K-degree). It does not
assume that specialized leading coefficients are nonzero at every parameter.

Use the twelve base factors of (100.12), in this exact order:

(B−3), B, (B+1), (B+3), L, Q2, P48, P98, Q6, Q8, Q10, Q90.

The exponents in the three resultants are, respectively,

RC:[174,142,74,677,14,14,14,28,2,1,1,2],
RD:[179,151,81,675,14,14,14,28,2,1,1,2],
RT:[187,159,87,713,15,16,15,30,2,1,1,2].

Define the small factors

P3=b³+5ib²−9b−21i,
S4=9B⁴−68B³+118B²+60B+9,
P14=U(B)+ib V(B),
U=36B⁷+266B⁶+9B⁵+6975B⁴+2862B³−19440B²+1701B−729,
V=−6B⁶−93B⁵−2697B⁴+8082B³+12636B²−8181B+243,
P2=2b²−3ib−3,
P3a=6b³−ib²+6b−3i,
P4=3b⁴+4ib³−14b²−12ib+3,
Q=23B²−78B−9.

Using precisely the decic F(b,k) of (88.1), define the exact quotients
J33=F(b,i)/[b(b²−3)] and J32bar=barJ33/[−432(b+i)].
Their degrees are 33 and 32; the latter is monic over Q(i).
Then the remaining factors, including every scalar, are

RC:2^556*3^78 (b−i)^8 P3² S4 P14²,
RD:2^572*3^90 J33² Q,
RT:2^610*3^93 S_T,

where S_T=b(B−1)²(b−i)^7 P2 P3a P3 P4 Q J32bar.
Multiplying the twelve powered factors by the indicated remaining factor
is the complete claimed identity. The right-side b-degrees are 9940,9998,
10636, all within the proved bounds.

The finite characteristic-zero certificate evaluates the original ordered
integer resultants at b=i(j+2), for 0≤j≤10620,10712,11396 respectively.
At these nodes the original K-degrees are exactly 10 and 140/142/151.
The coefficient parity makes every specialized polynomial integral.
Each exact original determinant is compared with the complete stated
product. The numbers of distinct verified nodes are 10621,10713,11397,
one more than each proved bound. The stated ordered determinant equals the displayed product at each of
these nodes, by integer polynomial elimination. The degree bounds
therefore prove the three identities over Q(i)[b]. A modular factorization
or a smaller discovery sample is not used as a proof premise.

### 103.5. Norm conversion, with all scalar factors

Let RY be (100.12), Ra=Res_K(F0,a), Rs=Res_K(F0,Ds). The tower
norm formulas give

Nm(C)=RC/[(B+3)^20 RY],
Nm(D)=RD/[(B+3)^20 RY Ra],
Nm(T)=6^20 RT/[RY Rs Ra].

Indeed the radial norms are their resultants divided by a^14,a^14,a^15.
The remaining powers of a are−7,−8,−8. The outer leading coefficients
cancel because140=14*9+7*2,142=14*9+8*2 and151=15*9+8*2.
These are identities of multiplication determinants in a finite-free tower;
no assumption of reduced fibres is required.

Use Ra=2^6 B^5(B−3)^2(B+1)W32 and the exact ordered Rs formula
(100.4). Cancelling the displayed factors gives

Nm(C)=(B−3)^8(b−i)^8 P3² S4 P14² /
      [(B+1)^4(B+3)Q8 Q10],

Nm(D)=2^10*3^12(B−3)^11 B^4(B+1)^2 J33² Q /
      [(B+3)^3 Q8 Q10 W32],

Nm(T)=−2^42*3^34 B^4(B−3)^11(B+1)^3(B+3)^13 Q2 S_T /
      [Q8 Q10 W32].

The original E=barC*T−2i(B+3)Yc is identically zero in the source field.
Both sides specialize regularly once the line lift,C,D and their bars do;
no inverse of Yc occurs in that argument. Thus

Nm(Yc)=Nm(barC)Nm(T)/[2^20(B+3)^20].

Exact half-parameter checks modulo 97, with i=22, give
Nm(C)=25,Nm(barC)=64,Nm(D)=80,Nm(T)=39,Nm(Yc)=39.
These agree with the original half-algebra certificates and check scalar
normalization only; the full identities were established in §103.4.

### 103.6. Exact real nonvanishing and the pivot strata

For 0<B<1, the Bernstein coefficients of S4 on [0,1] are
(9,24,176/3,96,128), all positive. The real part of P3 is b(B−9).
The ordered resultant of U,V in B is the nonzero integer

210880036177211402657506969366919563393892352.

The same nonzero resultant supplies an extended Euclidean identity
uU+vV=1 over the rational numbers.
Thus P14 cannot vanish for real b!=0. The imaginary parts of P2,P3a,P4
are −3b,−(B+3),4b(B−3), respectively. Finally
−Q=9+55B+23B(1−B)>0 on [0,1]. Every other displayed small linear or
endpoint factor is nonzero in the real puncture.

The source-circle identity is

Res_K(F0,a)=B^4 F(b,i)F(b,−i),
J33 barJ33=64(B+1)W32(B).

It follows directly by evaluating a at K=±i/b and using
F0(B,K)=b^−6 F(b,bK). The already proved source-circle unit therefore
makes J33,J32bar and their bars nonzero on the retained real domain.
The polynomial Q10 has no root on (0,1) by the exact Sturm result in §100.
Q2 is positive there. Hence all four displayed norm expressions are
regular and nonzero whenever Jsrc Q8!=0.

The derivation temporarily used aY−1, but specialization does not.
The scalar-adjugate line lift (100.15) is regular throughout Jsrc Q8!=0,
including the Q90 roots. It agrees with the aY lift in Q(i)(b), so their
finite-free multiplication determinants are the same rational functions.
The displayed expressions have no Q90 denominator. Evaluating the regular
scalar-adjugate lift at any such root therefore gives exactly the nonzero
norm values asserted here. No density argument declares a pole harmless:
regularity of every coordinate is supplied by the previously proved lift,
and its actual determinant is evaluated by the rational identity.

This proves C,D,T,Yc units and, by coefficient conjugation, their bars.
The original formulas and scalar-adjugate lift have no A or F8 division,
so the preceding reasoning retains all of those original strata as well.

### 103.7. Consequence for reconstruction guards only

The monic radial equation has unit constant coefficient−R/a, so X is a
unit. Since G=X(1+ibK), barG=X(1−ibK), and the two linear factors
multiply to the source-circle unit a, G and barG are units. Now

q=C barC D barD/(Yc barYc),
e=−Yc/(barC D), epsilon=bare

are units too. Together with the beta,barbeta,sigma and source
units, this accounts for every retained original generic reconstruction
unit. Any adjugate inverse of such an element has a nonzero determinant
at each retained real parameter, so all its scalar entries are regular.
Their reduced scalar denominators cannot have a real zero there.
The same applies to polynomially computed discarded norm markings and
their retained denominators; none is secretly inverted again.

This result concerns only the original reconstruction arrays, source
involution and their required units. The old Y-power-basis change, the
ordinary overlap rank certificate and the mixed determinant remain separate
obligations unless replaced by the construction in §104.
All 24 previously closed signed fibres retain their individual proofs.
No conclusion that the residual guard is empty, or that the entire actual
branch admits no quartet, is made here.

## 104. An intrinsic norm for distinct-projective-mean orthogonality

### 104.1. Canonical finite-free off-diagonal algebra

Work over a localization S of Q(i)[b] on which all source and original
reconstruction arrays used in §102 are regular and their required units
remain units. Retain 0<|b|<1, Jsrc Q8!=0 and every other required scalar
of that construction, except the Y-power basis and the old ordinary
380-minor. The reconstruction-unit hypotheses in this paragraph are discharged by
Theorem 103.1 on its stated domain. The construction below is also valid
on any smaller localization where the same required units exist.

Let f(K) be the monic normalization of F0(B,K) from (100.1), B=b².
The source theorem makes f' a unit in S[K]/(f). Put

Q(K,K')=[f(K')−f(K)]/(K'−K).

This is a polynomial, monic of degree 9 in K'. The algebra

Boff=S[K,K']/(f(K),Q(K,K'))

is free of rank 90 with basis K^r K'^s,0≤r≤9,0≤s≤8.
Its relation implies f(K')=0. Moreover K'−K is a unit in Boff:
modulo K'−K the second relation is f'(K), already a unit. Equivalently,
Q and K'−K generate the unit ideal over S[K]/(f), since their resultant
in K' is, up to the harmless degree-nine sign, the unit f'(K).
This argument retains nonreduced radial fibres; only the already required
etaleness of the degree-ten source algebra is used.

Put a(K)=1+BK² and t(K)=Ns(K)/Ds(K), using precisely (100.1).
The source proves these inverses regular. Base change gives the same units
at K'. Adjoin the two monic radial equations

X²−t(K)X/a(K)−R/a(K)=0,
X'²−t(K')X'/a(K')−R/a(K')=0.

The resulting algebra O is free of rank 360. One fixed basis is
K^r K'^s X^e X'^f, with 0≤r≤9,0≤s≤8 and e,f∈{0,1}, ordered as
(left B20 index, right index in 1,K',...,K'^8,X',K'X',...,K'^8X').
The defining construction of this algebra does not use an original
Y-power basis or its inverse.

### 104.2. Original overlap and full norm

Reconstruct the original G,C,D,Yc,q,e and their bars in each factor by
§102, with scaled original-input convention G=X(1+ibK) and physical
coefficients G/kappa,C/kappa,D/kappa as in §87.1. All arrays here are
base changes of the same original coefficients; no new candidate ray
restriction or synchronous-root assumption is used.

Evaluate the integral 508-term ordinary overlap polynomial of (79.8)–(79.9)
in O, with exactly the nine arguments of §89.3. Call the result Noff.
Define the rational function

z_off(b)=det(M_Noff:O→O)

in the fixed rank 360 basis. This full multiplication determinant is
basis-independent. It is not an unspecified minor or a numerical search.

The exact half-parameter multiplication determinant is

z_off(1/2)=85 mod97, with i=22.

The half source basis change is invertible. The certificate rebuilds it
from the original G,barG and X=(G+barG)/2, K=Y/(bX).
Its determinant is 27 modulo 97. It then uses the diagonal source idempotent

E=Q(K,K')/f'(K)

in the tensor square of the rank-twenty generic algebra. Write Q−f'(K)=(K'−K)H. Then
Q(Q−f')=(f(K')−f(K))H=0, so E²=E directly in the tensor algebra.
Under the source etale splitting, E is 1 on equal K and 0 on unequal K;
therefore 1−E has rank 360, even when radial fibres are nonreduced.
Its image is canonically O. The original overlap multiplication matrix preserves
that image. Restriction to the explicitly specified monomial columns of
1−E gives determinant 85. The multiplication matrix in the displayed monomial basis therefore
provides the same determinant without a sampled-rank argument.
The half data and the 508-term polynomial come from the earlier exact
original half-algebra proof. No new irreducibility assumption is used.

### 104.3. Physical implication

Suppose two original generic common-flat rays are orthogonal at a regular
real parameter and their projective means have K!=K'. Their original
coordinate evaluations define a homomorphism O→C, because the decic
relations and the divided-difference relation hold. Orthogonality of any
relative root order makes Noff zero by the original product-of-six-overlaps
identity. Consequently z_off must vanish. Hence z_off!=0 forces K=K'.

Away from Q8 every generic ray has both channels three-distinct, by the
physical collision classification. The punctured zero-mean lemma
makes the ordinary upper-channel gauge available for each ray. Thus the
preceding ordinary-overlap argument covers all original generic rays,
without applying Theta to just one endpoint or losing a parity case.

For a fixed physical K, the radial equation has precisely the two possible
mean roots X and X'=-R/[a(K)X], with multiplicity retained algebraically.
In the real physical domain a>0 and R>0, so its two real roots are distinct.
If two points use the same root, uniqueness of the original line lift and
original reconstruction makes all quotient coordinates equal. All six
root orders therefore give precisely S3-related rays.
For the opposite root,

G'=X'(1+ibK)=−R/barG.

This is exactly the mean action of Theta in (89.6). Original lift uniqueness
and the already proved involution identify the full coefficient point;
all root orders give S3Theta-related rays. Thus z_off!=0 implies every
original generic orthogonal pair lies entirely in one S3–Theta union.
The induced graph on that union is bipartite by §82.

### 104.4. Mixed determinant and complete guarded consumer

Construct the same mixed element of (90.14), using B20 for the generic
factor and the original ten-dimensional aligned basis. Its full determinant
is the identical rational function h_m of (90.15), by similarity over
Q(i)(b); h_m(1/2)=57 mod97. The construction does not require the old
Y-power change at a specialized parameter.

Define a new guard by the finite operations of §102, retaining every source,
aligned, original-unit, actual-denominator and physical-collision condition,
but never constructing the old Y-power basis or its inverse and never
constructing the old ordinary principal minor. Instead construct O,Noff,
z_off and the intrinsic-basis mixed matrix. Mark their full determinants
z_off,h_m nonzero; retain all actual reduced scalar denominators and the
coefficient conjugates, with the same primitive integer normalization.
This gives a nonzero polynomial, since all required half certificates,
including 85 and 57, are nonzero.

Off this guard, no generic pair can cross its orbit union; no mixed edge
exists; and the all-aligned triple obstruction applies. Therefore
there is no noncanonical orthogonal triple. The canonical basis uniqueness
and fixed-pair no-quartet consumer then follows exactly as in §102. All 24
previously closed fibres retain their separate proofs and may be removed
with the same maximal-primary-factor procedure.

No claim is made that this guard has fewer real zeros than the previous
one. The new full determinant z_off and h_m remain unclassified functions.
The combination with Theorem 103.1 is stated precisely in §105.

## 105. The residual condition consists of two overlap norms

### 105.1. Domain and earlier closed fibres

Retain the actual family and the original input/output convention. Work on
0<|b|<1. Let Z24 be precisely the union of the 24 signed parameter fibres
individually closed in Sections 92–102: twelve source fibres, four channel
collisions, four aligned coordinate exceptions, and four linear-pivot
fibres. These are distinct finite sets with the previously established
exact defining polynomials and root counts. No unclassified norm root is
silently added to this list.

The generic source factor is Jsrc=L(b²)P48(b²)P98(b²). The collision
factor is Q8(b²) of (100.11). The two aligned exception polynomials are A10(b),A14(b), written
Q10(b),Q14(b) in §96. This aligned Q10(b) is different from the
positive degree-ten-in-B factor also called Q10 in (100.12). The linear
pivot factor is Q180(b)=Q90(b²). Precisely, put

J24(b)=Jsrc(b) Q8(b²) A10(b) A14(b) Q180(b),
Z24={b real:0<|b|<1 and J24(b)=0}.

This is exactly the polynomial and set of §102, with no alteration to
its real roots or multiplicities.

### 105.2. Regular original algebras

At every real punctured parameter outside Z24, the source theorem gives
the complete degree-ten source algebra and the finite-free rank-twenty
radial algebra. The scalar-adjugate lift gives the unique original
line coordinates; Theorem 103.1 gives C,D,T,Yc
and their conjugates as units. The previously proved beta,barbeta,sigma,
source-circle and radial constant units are retained. Hence every original
generic reconstruction expression is regular, including q,e and epsilon.
All physical tests, six root orders, and optional channel choices remain.

The aligned clearance supplies the complete finite-free degree-ten aligned
algebra with regular original phases outside its four already closed
coordinate exceptions. Constant channels and the shared repeated pair
remain in the aligned class. All original Cayley poles occur in the
already closed exceptional fibres; none is omitted from the consumer.

A reduced scalar denominator of a rational coordinate regular at a real
parameter cannot vanish there: after cancellation in Q(i)[b], numerator
and denominator are coprime, and over the local ring the coordinate's
regularity forbids a denominator factor supported at that parameter.
Thus every actual reconstruction denominator has its real punctured zeros
among the earlier closed fibres. No separate unit marking from those
constructions is needed in the residual parameter guard.

### 105.3. Exactly two remaining overlap functions

Use the monic divided-difference algebra O of rank 360 and its
original ordinary overlap element Noff. Define

 z_off(b)=det(M_Noff on O).

Use the intrinsic rank-twenty generic basis and the original rank-ten
aligned basis to define the original mixed element Nm of (90.14). Define

 h_m(b)=det(M_Nm on the tensor product of the generic and aligned algebras).

Both are rational functions defined entirely by the printed original
reconstruction operations. No Y-power basis or inverse is used; no
principal minor or sampled rank is retained. Their nonzero half witnesses
are respectively 85 and 57 modulo 97, with i=22. These witness nonzero
rational functions; they do not prove uniform real nonvanishing.

Their full multiplication matrices are regular outside Z24, so their
reduced scalar denominators have no punctured real zeros there. Write
z_off=n_o/d_o and h_m=n_m/d_m in reduced Q(i)[b] form. Define

 P(b)=n_o(b) bar(n_o(b)) n_m(b) bar(n_m(b)),

then clear rational constants and take primitive integer content. P is an
explicit nonzero real polynomial, defined by finite exact operations, even
before its expanded coefficients are computed. This is the residual guard.
The old reconstruction, power-basis and principal-minor factors are absent.
Set Pres=P and repeatedly replace Pres by Pres/gcd(Pres,J24), using
the monic gcd over Q[b], until this gcd is constant. Then normalize
by clearing rational denominators and taking positive-leading primitive
integer content. Each nonconstant step strictly decreases degree. The
procedure removes every primary power supported on J24 and no other
factor. A zero of P outside Z24 remains a zero of Pres. Conversely,
Pres(b)≠0 implies either P(b)≠0 or J24(b)=0. These assertions hold
even if J24 has repeated or reducible factors; they use neither a list
of unknown norm roots nor an irreducibility assumption.

### 105.4. Guarded pair and basis consequence

**Theorem 105.1.** At any real 0<|b|<1 outside Z24 with P(b)≠0, any generic orthogonal pair has equal projective mean
K, and hence its endpoints lie in the same S3–Theta orbit union. The
induced graph of that union is bipartite. The mixed norm excludes every
aligned/generic edge. The uniform all-aligned triple theorem handles the
remaining case. Therefore no three noncanonical rays are orthogonal.
Together with the single-canonical rigidity theorem, the only entire
common-unbiased basis is the canonical basis, up to phases and permutations.
For completeness, a unitary output basis B is unbiased to the fixed pair
(I6,H0(b)) exactly when W=H0(b)^* B and H0(b)W=B are both flat,
where * is the adjoint. Thus W is the original common-flat input basis.
It must be Ccan(b)/sqrt(6), up to phases and column permutation; the
output basis is H0(b)Ccan(b)/sqrt(6). Two additional bases in a quartet
would both have that column-ray set, so their relative unitary would be
monomial and could not be flat. This proves the fixed-pair conclusion.
Each fibre in Z24 has the same triple, basis and fixed-pair conclusion
by its independent earlier proof. Therefore the entire conclusion holds
whenever Pres(b)≠0, with no separate J24 nonzero hypothesis.

Every other real punctured zero of Pres remains an exception to this
guard-based implication unless independently closed elsewhere. All
earlier exact-fibre and neighborhood results retain their own scope.
Nothing here proves Pres has no such zero, gives a numerical parameter radius,
or resolves the entire actual branch. The center retains its separately proved quartet exclusion, complete
ray census, and explicit noncanonical central basis.


## 106. The original reflection-odd Jacobian and its exact norm

Retain the actual paired-circulant family and the original input convention
of §§60,74–75. Throughout §§106–111 put
\[
 B=b^2,\quad R=3-B,\quad h=\sqrt{R/(1+B)},\quad\kappa=(b-i)h,
 \qquad 0<|b|<1.
\]
Here B differs from the symbol 3+b² used in §87. Write J3 for the
three-by-three all-ones matrix, and set
\[
 P=(bh-3+i(h+b))/2,\qquad Q=(-bh-3+i(h-b))/2,
\]
so that the actual matrix is
\[
 H_0=6^{-1/2}\begin{pmatrix}J3+PI&J3+QI\\J3+\bar QI&-J3-\bar PI\end{pmatrix}.
\tag{106.1}
\]
All bars fix the real coordinates and conjugate i. The statements below
concern this paired-circulant family and its original common-flat inputs.

### 106.1. Genuine phase derivatives and both row factors

Take an original aligned input w=(1,1,z;g,g,gr), with |z|=|r|=|g|=1,
and its two reflection-odd phase directions
\[
 w(\alpha,\beta)=(e^{i\alpha},e^{-i\alpha},z;
                  ge^{i\beta},ge^{-i\beta},gr).
\]
Put M=√6 H0, and let Nu,j=|(Mw)j|²−6 and Nl,j=|(Mw)j+3|²−6.
The repeated output numerators at α=β=0 are
\[
 A_0=2+z+P+g(2+r+Q),\qquad
 L_0=2+z+\bar Q-g(2+r+\bar P).
\]
Direct differentiation of the six output expressions gives
\[
 J_{\rm odd}=\frac{\partial(N_{u,0}-N_{u,1},N_{l,0}-N_{l,1})}
 {\partial(\alpha,\beta)}=-4\mathcal E,
\quad
 \mathcal E=\Im\begin{pmatrix}
 \bar A_0P&\bar A_0Qg\\
 \bar L_0\bar Q&-\bar L_0\bar Pg
 \end{pmatrix}.
\tag{106.2}
\]
Indeed each paired difference differentiates |A+iαa|²−|A−iαa|²,
whose derivative is −4 Im(bar(A)a). Thus **both** original rows have
factor 4 and det Jodd=16 det E. If residuals |H0w|²−1 are used instead,
each row is divided by 6 and the determinant by 36. No unspecified
normalizing scalar is being discarded.

### 106.2. Complete aligned algebra used by the norm

Here are finite definitions of the aligned operations, with their original
scalings. Let d,θ be the §90 variables and write
\[
 K_a=d^2+4\theta,\qquad J_a=bd-\theta+3,\qquad
 F_a=d^2+(\theta+1)^2.
\]
Define the three original linear equations in a,c by
\[
\begin{aligned}
 P_0={}&K_a[da-(\theta+1)c]+bd(1-\theta)-d^2-2\theta(\theta+1),\\
 P_1={}&[bd^2-d\theta(B+1)+d(B-3)+b(\theta^2-2\theta-3)]a\\
 &+[-Bd^2-4bd+\theta^2-2B(\theta+1)+4\theta+3]c
 +(B-3)(\theta+1-bd),\\
 P_2={}&[5bd^2+2d\theta(B+2)-2dB+3b(\theta+1)^2]a\\
 &+[-3d^2-2bd(\theta+1)-(2B+7)\theta^2-10\theta+2B-3]c
 +2(B-3)(\theta+1+bd).
\end{aligned} \tag{106.3}
\]
Let (a,c) be the Cramer solution of P0=P1=0. Its two-by-two determinant
is −b Ka Ja Fa. Set, by exact cancellation,
\[
 \Phi=\frac{bK_aJ_a}{2}P_2(a,c),\qquad
 \Psi=\frac{b^2K_aJ_a^2F_a}{2}[K_a(a^2+c^2)-R].
\tag{106.4}
\]
These are polynomials of θ-degrees 4 and 6 with 33 and 77 terms.
To define U,V, form the eight rows
of coefficients of
\[
 \theta^2\Psi,\ \theta\Psi,\ \Psi,\
 \theta^4\Phi,\ \theta^3\Phi,\ \theta^2\Phi,\ \theta\Phi,\ \Phi
\]
in descending columns θ⁸,θ⁷,…,θ⁰. Let L be the determinant of the first
eight columns and C the determinant of the first seven columns followed
by the last column. Then
\[
 V=L/[6d^2b^4(B-3)^2],\qquad U=-C/[6d^2b^4(B-3)^2],\qquad\theta=U/V.
\tag{106.5}
\]
Both divisions are exact polynomial divisions. U and V have 186 and 173
terms. This fixes their signs and factors without a subresultant convention.

Use Q5=Σ(j=0..5) qj d^j, where
\[
\begin{aligned}
q_0={}&-8192b^3(B-3)(B+3)(2B^2+9B-27),\\
q_1={}&512B(9B^6+86B^5+215B^4-564B^3-4401B^2+7614B+2673),\\
q_2={}&32b(9B^7-329B^6-3335B^5+8559B^4+72195B^3
 -100179B^2-95877B-8019),\\
q_3={}&-16(27B^8-416B^7-3906B^6+10260B^5+60296B^4
 -77256B^3-173718B^2-21996B-2187),\\
q_4={}&2b(9B^8-1024B^7-6256B^6+19608B^5+108898B^4
 -101552B^3-586392B^2-56040B-16227),\\
q_5={}&(9B^4+28B^3-170B^2-612B+2025)
       (2B^5+33B^4+90B^3+4B-1).
\end{aligned} \tag{106.6}
\]
Polynomial division by Q5 gives the following original shape identities:
V⁴Φ(U/V) has 2717 terms and quotient 2088 terms; V⁶Ψ(U/V) has
6076 terms and quotient 5112 terms; both remainders are zero.
Thus the shape satisfies the original consistency and norm-circle equations,
not only a projection equation. The complete chart coverage and pole
clearance are exactly those of §§90,99.

Adjoin s²=Ka and reconstruct
\[
 u=(s+d)/2,\quad v=(s-d)/2,\quad
 z=(1+iu)/(1-iu),\quad r=(1+iv)/(1-iv),\quad g=s(a+ic)/\kappa.
\tag{106.7}
\]
Reduce (106.2) using h²=R/(1+B), |κg|²=R and s²=Ka. The element
j=det(E)/h belongs to the rank-five Q5 algebra and is independent of the
sign of s. All divisions refer to the displayed original rational operations.

### 106.3. Exact norm identity and its degree-bounded proof

Put
\[
 f_8=9B^2+22B+49,\quad f_9=4B^3-23B^2+18B+81,\quad
 f_{10}=9B^3+103B^2+39B+9,
\]
and define
\[
\begin{aligned}
 W(B)={}&48699B^{10}-436510B^9+1411279B^8-3024104B^7
 +7818278B^6\\
 &-12049524B^5+14203782B^4-12899304B^3
 -613089B^2+1902690B+492075.
\end{aligned}\tag{106.8}
\]
**Theorem 106.1.** In the original aligned algebra,
\[
 \operatorname{Nm}_5(j)=
 \frac{-243(B+3)^{10}W(B)}
 {32b(B-3)^3(B-1)^4(B+1)f_8f_9f_{10}}.
\tag{106.9}
\]
Consequently the genuine original row-difference determinant has norms
\[
 \operatorname{Nm}_5(\det J_{\rm odd})=
 \frac{2^{15}3^5h(B+3)^{10}W(B)}
 {b(3-B)(1-B)^4(1+B)^3f_8f_9f_{10}},
\tag{106.10}
\]
\[
 \operatorname{Nm}_{10}(\det J_{\rm odd})=
 \frac{2^{30}3^{10}(B+3)^{20}W(B)^2}
 {B(3-B)(1-B)^8(1+B)^7f_8^2f_9^2f_{10}^2}.
\tag{106.11}
\]
The rank-ten norm is squared because the determinant is independent of
s. The degree-ten polynomial W is the primitive residual factor, not the
entire squarefree numerator of a rank-ten norm.

**Proof.** Put d=bx and define
\[
 f(B,x)=Q_5(b,bx)/b^3,\qquad
 \overline U(B,x)=U(b,bx)/b^3,\qquad
 \overline V(B,x)=V(b,bx)/b^3.
\]
After exact rational cancellation these are polynomials in B,x with
respective degree pairs (10,5), (17,14), (17,13). Write b j=N0/D0 after this
substitution and rational cancellation, before θ=U/V; take N0,D0 to be
coprime polynomials in Q[B,x,θ]. They have respective degree triples
(7,8,8), (6,8,7) in (B,x,θ).
Homogenize both to common θ-degree 8. Their x-degrees are at most 112
and their B-degrees at most 143 and 142.

For either polynomial n, use the ordered resultant with declared
x-degree 112, meaning
lc(f)^(112−deg_x(n)) Res_x(f,n), where f=Q5/b³.
Equivalently use the corresponding padded Sylvester matrix. Both use the
same padding, so their ratio equals the actual quotient norm; no missing
leading-coefficient factor is suppressed. Their B-degree bounds are
5·143+112·10=1835 and 5·142+112·10=1830.
The proposed norm of b j is
\[
 \frac{-243B^2(B+3)^{10}W}
 {32(B-3)^3(B-1)^4(B+1)f_8f_9f_{10}},
\]
with numerator and denominator degrees 22 and 16. Its cross-multiplied
difference from the actual resultant ratio therefore has degree at most
max(1835+16,1830+22)=1852.

Here is an explicit finite rational identity completing the interpolation.
For each integer n with 4≤n≤1856, put
\[
 f_n(x)=\operatorname{monic}_x f(n,x),\qquad
 \mathcal R_n=\mathbb Q[x]/(f_n).
\]
All the following polynomial remainders have degree less than five. Inverses
in Rn are defined by the extended Euclidean identity with the monic fn.
Put Vn=rem_x(V̄(n,x),fn) and θn=rem_x(Ū(n,x),fn)/Vn in Rn.
Let nn,dn be the remainders of
N0(n,x,θn),D0(n,x,θn), and put en=nn/dn. The original reduction
(106.2)–(106.7) eliminates b,h,i,s, so these lie in Rn.
If en=Σ(r=0..4) er x^r, define Mn to have column k equal to the
coefficient vector of rem_x(x^k en,fn), for 0≤k≤4. These are complete
finite definitions using only rational polynomial arithmetic. They give
\[
\begin{gathered}
 \gcd_x(f_n,V_n)=1,\qquad
 \gcd_x(f_n,d_n)=1,\\
 32(n-3)^3(n-1)^4(n+1)f_8(n)f_9(n)f_{10}(n)\det M_n
       +243n^2(n+3)^{10}W(n)=0
 \quad(4\le n\le1856).
\end{gathered}\tag{106.13}
\]
The two gcds are normalized to be monic. Multiplication by the common
θ-degree-eight power of V̄ does not change the norm ratio because Vn is
a unit in every Rn.
For the last equality, the determinant is the finite sum
Σ(σ∈S5) sgn(σ)∏(k=0..4)(Mn)σ(k),k; substitution and rational cancellation
give zero for every indicated integer n. Since there are 1853 distinct nodes and the degree bound
is 1852, their vanishing proves (106.9). Multiplying by (16h)^5 and then
squaring for the s-extension gives (106.10) and (106.11). ∎

### 106.4. Real scope

For the signed Euclidean Sturm chain of W, the endpoint signs are
\[
0:(+,+,-,+,+,+,-,+,+,-,+),\qquad
1:(-,-,+,-,-,-,+,-,-,-,+).
\]
There are respectively 6 and 5 variations. Thus W has exactly one root
B* in (0,1), isolated for example by
\[
 178534/314901 < B_* < 179855/317231.
\tag{106.12}
\]
It gives b=±√B*, with B*≈0.566952788342580 and |b|≈0.752962673937148.
Both W(B) and W(b²) are irreducible over Q(i), and hence over Q.
For irreducibility, work first in \(\mathbb F_{113}\), and put
\[
\begin{aligned}
f_{113}(B)={}&B^{10}+26B^9+51B^8+56B^7+48B^6+27B^5
 +23B^4+32B^3+16B^2+B+10,\\
r_{113}(B)={}&-50B^9+15B^8+10B^7-25B^6-44B^5+49B^4
 -23B^3-39B^2-23B+13,\\
a_{113}(B)={}&15B^9+29B^8+25B^7-27B^6+45B^5+30B^4
 +53B^3-35B^2-33B-3,\\
q_{113}(B)={}&-41B^9+31B^8+29B^7+16B^6-20B^5-40B^4
 -40B^3+28B^2-45B+34.
\end{aligned}
\]
The following polynomial identities hold:
\[
\begin{gathered}
f_{113}(B)=28W(B),\\
b^{113^4}\equiv b\,r_{113}(b^2)\pmod{f_{113}(b^2)},\qquad
b^{113^{10}}\equiv-b\pmod{f_{113}(b^2)},\\
B\,a_{113}(B)\bigl(r_{113}(B)-1\bigr)+q_{113}(B)f_{113}(B)=1.
\end{gathered}
\]
Here the first identity, and all coefficients in this proof up to the lifting step, are in \(\mathbb F_{113}\).

Set \(F(b)=f_{113}(b^2)\). Raising the second Frobenius congruence to the \(113^{10}\)-th power gives
\(b^{113^{20}}\equiv b\pmod F\). Also,
\[
\gcd\bigl(F,b^{113^{10}}-b\bigr)=\gcd(F,-2b)=1,
\]
since \(F(0)=10\), and substitution \(B=b^2\) in the displayed Bézout identity gives
\[
b\,a_{113}(b^2)\bigl(b\,r_{113}(b^2)-b\bigr)+q_{113}(b^2)F(b)=1,
\]
so \(\gcd(F,b^{113^4}-b)=1\).

Every irreducible divisor of \(F\) therefore has degree dividing \(20\), but no such degree divides \(10\) or \(4\). Every proper divisor of \(20\) divides one of \(10,4\); hence every irreducible divisor of \(F\) has degree \(20\). As \(\deg F=20\), \(F\) is irreducible.

Now reduce \(\mathbb Z[i]\) modulo the Gaussian prime \(7-8i\), whose norm is \(113\). This reduction is \(i\mapsto15\) because \(15^2=-1\) in \(\mathbb F_{113}\). The leading coefficient of \(W(b^2)\) reduces to \(109\ne0\), with inverse \(28\). Moreover \(\gcd(48699,436510)=1\), so \(W(b^2)\) is primitive over \(\mathbb Z[i]\). Its irreducible reduction \(28W(b^2)=F(b)\) consequently proves irreducibility over \(\mathbb Q(i)\) by Gauss's lemma. A nontrivial factorization of \(W(B)\) over \(\mathbb Q(i)\) would, after \(B=b^2\), give a nontrivial factorization of \(W(b^2)\). Thus \(W(B)\) is irreducible as well.

All factors in the denominators of (106.9)–(106.11) are nonzero on the
puncture: f8 and f10 are positive coefficient polynomials and f9≥81−23>0.
W is coprime to the two aligned guards A10,A14 of (99.1). Therefore outside
those coordinate-exception fibres, W≠0 implies nonsingularity of the
original reflection-odd block at every aligned noncanonical ray. This is
not a claim about the full phase Jacobian. A vanishing norm alone would
not establish a physical singular point; that obligation is handled next.

## 107. The physical aligned W point and its original projective mean

**Proposition 107.1.** For each b=±√B*, exactly six aligned noncanonical
original common-flat rays have singular reflection-odd block. Their quotient
coordinates and original projective mean are given below.

**Proof.** Work in F=Q[B]/(W), with the real embedding B=B*. Let f(B,x) be the
monic normalization of Q5(b,bx)/b³. Reduce the numerator n and denominator
d of b j in F[x]/(f), using the original θ=U/V. Exact Euclidean divisions
give
\[
 \gcd(f,d)=1,\qquad\gcd(f,n)=x-x_*.
\tag{107.1}
\]
There is thus exactly one odd-singular aligned quotient point, not merely
an unspecified zero of the norm. Put θ*=θ(x*), a*=a(bx*,θ*),
c*=c(bx*,θ*) and A*=b a*. These are independent of the sign of b in the
indicated scaled coordinates. The following coefficient arrays provide
explicit coordinates; every array is in descending powers B⁹,…,B⁰ and
is reduced modulo W. They are the rational remainders determined by (107.1).

\[
x_*\leftrightarrow\begin{pmatrix}
\frac{3982736563944554419}{65835713602566881280} \\\frac{-2634026916170255136941}{4147649956961713520640} \\\frac{382388971292541065473}{148130355605775482880} \\\frac{-739211685616871138447}{115212498804492042240} \\\frac{6387004522335616763963}{414764995696171352064} \\\frac{-61749338506588860666983}{2073824978480856760320} \\\frac{96216679408769700701}{2383706871817076736} \\\frac{-14196538270734276187}{330121773078773760} \\\frac{137607005336544012469}{5689506113802076160} \\\frac{3269240671864047023}{1137901222760415232}
\end{pmatrix}.
\]
\[
\theta_*\leftrightarrow\begin{pmatrix}
\frac{-59344918236922297}{812786587686010880} \\\frac{14285593340548697923}{21945237867522293760} \\\frac{-20719406652295056685}{9875357040385032192} \\\frac{224264803816628280689}{49376785201925160960} \\\frac{-1165567024018875792497}{98753570403850321920} \\\frac{1785440201490664649777}{98753570403850321920} \\\frac{-12510482093553093607}{567549255194542080} \\\frac{318489713041616317}{15720084432322560} \\\frac{-172157895195960143}{487671952611606528} \\\frac{-267663227826023931}{162557317537202176}
\end{pmatrix}.
\]
\[
K_*\leftrightarrow\begin{pmatrix}
\frac{1267049439241281888451}{34518849837754420592640} \\\frac{-105976247109581085847199}{310669648539789785333760} \\\frac{90989053789048983417263}{77667412134947446333440} \\\frac{-203497903088354966758831}{77667412134947446333440} \\\frac{1023637064118863739471101}{155334824269894892666880} \\\frac{-37555760845651065289429}{3451884983775442059264} \\\frac{38745855846466233303281}{2876570819812868382720} \\\frac{-36796183392318595911721}{2876570819812868382720} \\\frac{815590415622845696507}{426158639972276797440} \\\frac{45316844845185569471}{28410575998151786496}
\end{pmatrix}.
\]
\[
t_*\leftrightarrow\begin{pmatrix}
\frac{-29600059014223272577}{639237959958415196160} \\\frac{7559409611686809797}{18181485994302554112} \\\frac{-1954310950617080270717}{1438285409906434191360} \\\frac{29923532544254118588379}{10067997869345039339520} \\\frac{-154256068785357683247881}{20135995738690078679040} \\\frac{2989637390753455711693}{248592539983828131840} \\\frac{-5658424561867363202821}{372888809975742197760} \\\frac{5175124921213255774637}{372888809975742197760} \\\frac{-1229144438224959350839}{497185079967656263680} \\\frac{78700139165324745573}{33145671997843750912}
\end{pmatrix}.
\]

The arrays for x*,θ* agree exactly with the gcd and shape operations.
The three original equations (106.3) and
\[
 (Bx_*^2+4\theta_*)[A_*^2/B+c_*^2]=3-B
\tag{107.2}
\]
vanish by exact reduction in F. Exact rational interval arithmetic, using
the Sturm-isolating interval
\[
 \frac{27268907919444276}{48097316884465325}
 < B_* <
 \frac{7055706205463736077}{12444962526933263674},
\tag{107.3}
\]
gives
\[
7<x_*<8,\quad1<\theta_*<2,\quad42<s^2=Bx_*^2+4\theta_*<43,
\]
\[
5<Bx_*-\theta_*+3<6,\qquad
42<Bx_*^2+(\theta_*+1)^2<43.
\tag{107.4}
\]
The rational Horner interval recursion on (107.3), with each product
interval equal to the minimum and maximum of its four endpoint products,
gives the displayed strict bounds for the reduced degree-nine coordinates.
Thus the Cramer and Cayley reconstruction is defined and s²>0. More
explicitly, besides A0,L0 in (106.2), define
\[
 A_2=2+z+Pz+g(2+r+Qr),\qquad
 L_2=2+z+\bar Qz-g(2+r+\bar Pr).
\]
Substitution of (106.7) and reduction by W, (107.1) and s²=Ka give
\[
 |g|^2=|z|^2=|r|^2=1,\qquad
 |A_0|^2=|A_2|^2=|L_0|^2=|L_2|^2=6.
\tag{107.7}
\]
These are the two repeated and the two singleton output equations of the
original six-by-six matrix. They hold for both signs of s, proving both
reconstructions are original common-flat rays. The three
singleton positions give six distinct such rays per signed parameter.
Under the complete aligned coverage, these are all aligned noncanonical
rays with singular odd block at W. No full-Jacobian conclusion is used.

Let Lr=θ*²+10θ*+9+3Bx*². Directly from the original mean
G=κg(2+r)/(2+z), one obtains
\[
 K_* = \frac{c_*L_r-2A_*x_*(3-\theta_*)}
 {A_*L_r+2Bc_*x_*(3-\theta_*)}.
\tag{107.5}
\]
It is independent of the two Θ signs. Let F0, Ns, Ds be exactly the
public §88/(100.1) polynomials, with
\[
 F_0(B,K)=b^{-6}F(b,bK),\quad N_s(B,K)=b^{-5}T(b,bK),\quad
 D_s=\partial_KF_0,
\quad t_*=N_s(B,K_*)/D_s(B,K_*).
\tag{107.6}
\]
Exact substitution gives F0(B,K*)=0, and (107.5)–(107.6) agree with the
printed K*,t* arrays. Their denominators are units in F. Rational interval
arithmetic also gives 1/5<K*<1/4 and 7/2<t*<18/5.
This identifies the singular aligned quotient and its mean in the original
generic source algebra. ∎

## 108. The removed source component has no strict generic lift

**Proposition 108.1.** Over the mean K* of Proposition 107.1, both original
radial lifts satisfy δ=0 and 0<q<1. Neither is a strict generic ray.

### 108.1. Original-equation construction on both radial roots

**Proof.** Put H=3+B and aK=1+BK*², and work in
\[
 \mathcal A_*=F[X]/(X^2-\lambda X-\mu),\qquad
 \lambda=t_*/a_K,\quad\mu=R/a_K.
\tag{108.1}
\]
A radial element u+vX has norm u²+λuv−μv². The unit of each divisor below is equivalent to its nonzero radial norm;
all equalities are in this rank-two algebra, retaining both radial roots. Adjoin j=ib,
j²=−B, and let the bar operation fix F,X and send j to −j. Set
G=X(1+jK*) and Z=u+jv; v denotes Im(Z)/b.

The following explicit polynomial operations restate the original §87.2
construction in this scaled j basis. Write [Y]0 and [Y]1 for the
coefficients of 1,j in Y, and |Y|²=Y bar(Y). Set
\[
\begin{aligned}
 \alpha&=3-j-\bar G,&\beta&=R+(3+j)\bar G,&d_\beta&=|\beta|^2,\\
 C_n&=Z-R\alpha/2,&D_n&=-\bar Z-R\bar\alpha/2,\\
 Y_n&=\bar GC_n\bar\beta+G\bar D_n\beta-|C_n|^2-|D_n|^2+C_n\bar D_n,\\
 L_s&=R(1-j)+(H+2j)\bar G,&N_s^\circ&=-H+2j+(1+j)\bar G,\\
 T_n^\circ&=3[L_sd_\beta+N_s^\circ C_n\bar\beta
                  -\bar N_s^\circ\bar D_n\beta]
 -2H[\bar Gd_\beta+2\bar D_n\beta-\bar C_n\beta],\\
 E^\circ&=\bar C_nT_n^\circ-2HY_n\bar\beta,\\
 J_n^\circ&=[18(1-j)G+3L_s+3N_s^\circ G+2HG]d_\beta
                +2H(-C_n+2D_n)\bar\beta,\\
 A_n&=|C_n|^2+|D_n|^2,\\
 Y^\circ&=(A_n-Rd_\beta)|T_n^\circ|^2
 +4H^2|D_n|^2d_\beta
 [|G|^2d_\beta-A_n+4[C_n\bar D_n+Y_n]_0],\\
 D^\circ&=2H[C_n\bar\beta]_1|T_n^\circ|^2
 +4H^2|D_n|^2d_\beta[J_n^\circ+2T_n^\circ]_1.
\end{aligned}\tag{108.2}
\]
The superscript circle prevents collision with the source polynomials Ns
and with the differently scaled original numerators. Precisely,
L=iLs, N=iNs-circle, original T=iTn-circle/dβ,
original E=iE-circle/(barβ dβ), Y-circle=dβ³ NY, and
D-circle=−dβ³ ND/b. These are identities by substitution into (87.2).
Their cleared factors are units in the displayed radial algebra.

Write [E-circle]1=A u+H1 v+C0; direct coefficient extraction verifies
there are no quadratic terms and A is a unit in the radial algebra. Substitute
u(w)=−(H1 w+C0)/A and v=w. Then [E-circle]0 is a quadratic
Q=q2 w²+q1 w+q0, Y-circle is quartic, and D-circle is cubic
P=d3 w³+d2 w²+d1 w+d0. Modulo Q the fraction-free remainder of P is
\[
 r_1w+r_0,\quad
 r_1=q_2^2d_1-q_1q_2d_2+(q_1^2-q_0q_2)d_3,
\quad r_0=q_2^2d_0-q_0q_2d_2+q_0q_1d_3.
\tag{108.3}
\]
Both q2 and r1 are units. Consequently the only possible original lift is
\[
 v=-r_0/r_1,\qquad u=-(H_1v+C_0)/A.
\tag{108.4}
\]
The quartic Y-circle also has an affine remainder with
unit leading coefficient and the same root. Exact substitution in (108.2)
gives E-circle=Y-circle=D-circle=0. This proves existence and uniqueness
for the original equations at both radial roots.

### 108.2. Exact cubic boundary, distinct from channel collision

Reconstruct
\[
 C=C_n/\beta,\quad D=D_n/\beta,\quad Y_c=Y_n/d_\beta,
\quad q=|C|^2|D|^2/|Y_c|^2,\quad e=-Y_c/(\bar CD).
\]
Reduction in (108.1), followed by reduction modulo W, gives
\[
 q|e|^2=1,\qquad
 \delta=q^2(3-8[e]_0)+6q-1=0,
\tag{108.5}
\]
while β,C,D,Yc,q,1−q and
\[
 \Delta=|D|^2-|C|^2
\]
are units. For clarity, these equalities mean zero remainder after successively
substituting (108.4), replacing X² by λX+μ, and dividing each coefficient
by the monic W. A divisor u+vX is a unit precisely when the remainder of
u²+λuv−μv² modulo W is nonzero. Applying this criterion to A,q2,r1 and
the displayed reconstruction divisors gives nonzero remainders. These
finite rational operations, together with the four arrays of §107, define
every entry and every unit assertion in (108.5). For explicit nonzero
witnesses, the reduction B=99 modulo 137 gives K*=31,t*=4,
aK=62,λ=31,μ=78 and λ²+4μ=40. The rank-two norms in this radial
algebra are
\[
\begin{array}{c|rrrrrrrr}
V&A&q_2&r_1&\operatorname{lc}(Y^\circ\bmod Q)&
 \operatorname{lc}(D^\circ\bmod Q)&d_\beta&q&1-q\\\hline
\operatorname{Nm}_2(V)&89&48&39&25&119&70&27&106
\end{array}
\]
and
\[
 \operatorname{Nm}_2(\Delta)=37,\quad
 \operatorname{Nm}_2(|C|^2)=72,\quad
 \operatorname{Nm}_2(|D|^2)=64,\quad
 \operatorname{Nm}_2(|Y_c|^2)=125.
\tag{108.8}
\]
All denominators of these finite rational operations have nonzero images.
Since W is irreducible, a zero radial norm in F would reduce to zero;
the displayed residues therefore prove the stated units. The zero
remainders in (108.5), in contrast, are characteristic-zero identities
in F[X]/(X²−λX−μ), obtained by the polynomial operations above.

To identify these radial lifts with the aligned points, for either sign
s=±√Ka set z_s,r_s by (106.7) at the coordinates of §107 and define
\[
 G_s=s(a_*+ic_*)\frac{2+r_s}{2+z_s},\qquad
 X_s=(G_s+\bar G_s)/2.
\]
Reduction by W and s²=Ka gives the three identities
\[
 G_s=X_s(1+ibK_*),\qquad
 a_KX_s^2-t_*X_s-R=0,\qquad
 q(X_s)=|2+z_s|^2/9.
\tag{108.7}
\]
The rationalized real numerator of Gs changes sign with s, whereas its
denominator |2+z_s|² is positive. Since aK,R>0, the radial roots are
nonzero, distinct and of opposite signs. Thus Xs for the two signs of s
are precisely the two radial roots. Finally |z_s|=1 and (107.4) exclude
z_s=±1, so (108.7) gives 1/9<q<1 on both roots.

For t=√q and ξ=t bar(e), the selected-channel cubic is
p(z)=z³−3tz²+3tξz−ξ. Its discriminant is
\[
 \operatorname{disc}(p)=27\xi^2[3t^4-4t^3(\xi+\xi^{-1})+6t^2-1]
 =27\xi^2\delta.
\tag{108.6}
\]
Hence δ=0 is exactly a repeated-root boundary of the selected-channel
cubic. Every original strict generic ray requires δ<0. Therefore neither
radial root over K* supplies a strict generic ray. The permissible channel
collision condition Δ=0 is a different invariant, and is not used to
exclude physical rays. Both Θ signs and all root orders remain covered. ∎

## 109. Retained original overlap norms at W

### 109.1. Exact retained algebras and a common good map

Let E=Q(i)[b]/(W(b²)); by §106.4 this is a field. Let f=F0/lc(F0)
be the **full** monic source decic. In E[K], define
\[
 g(K)=f(K)/(K-K_*),\qquad
 a(K)=1+b^2K^2,\quad t(K)=N_s(K)/D_s(K),
\]
\[
 A_{\rm ret}=E[K,X]/(g(K),X^2-t(K)X/a(K)-R/a(K)).
\tag{109.1}
\]
The factor K−K* is simple, and this algebra has rank 18. Importantly,
Ds remains the derivative of the **full decic before removing K−K***.
Replacing it by g' would change the radial equation.

The exact source and coordinate operations have the good reduction
\[
 p=137,\quad B=99,\quad b=28,\quad i=37,\quad K_*=31,\quad t_*=4.
\tag{109.2}
\]
Here W(99)=0, W'(99)=118, 28²=99 and 37²=−1 modulo 137; all rational
coefficient denominators of K*,t* and the leading coefficient of W are
nonzero. Using the literal §88 arrays and scalings (107.6), the ascending
coefficient lists are

\[
\begin{aligned}
F_0&\leftrightarrow (67,126,63,121,63,38,17,75,127,136,69),\\
N_s&\leftrightarrow (21,84,108,54,91,114,125,38,74,107),\\
D_s&\leftrightarrow (126,126,89,115,53,102,114,57,128,5).
\end{aligned}
\]

They give
\[
 F_0=69(K-31)g_9,
\quad g_9=K^9+29K^8+57K^7-K^6+3K^5+32K^4+22K^3-35K^2-22.
\tag{109.3}
\]
The identities K^(137⁹)=K and gcd(g9,K^(137³)−K)=1 prove g9 irreducible
by the degree-nine finite-field criterion. Also g9(31)=9≠0, so the full
decic is separable. The ordered derivative resultant (100.4) then proves
Jsrc=L P48 P98 nonzero in E. The remaining public coverage guards reduce to
\[
 Q_8(99)=3,\qquad A_{10}(28)=115,\qquad A_{14}(28)=116.
\tag{109.4}
\]
Thus §§98,99,103 give the complete original source, aligned and
reconstruction coverage at both real W embeddings. Q90 separation is
not required by Theorem 103.1; it will be used only for the finite-set
count in §111.

In F137[K]/(g9), write X²=λX+μ. The ascending
K-coefficient lists are

\[
\begin{aligned}
\lambda&\leftrightarrow (38,4,16,16,72,120,71,22,123),\\
\mu&\leftrightarrow (36,0,71,5,40,35,19,29,0).
\end{aligned}
\]

These lists are the remainders of t/a and R/a, respectively, with
t=Ns/Ds and a=1+BK². Direct powering gives
\[
 X^{137^9}=\lambda-X\ne X,\qquad X^{137^{18}}=X.
\tag{109.5}
\]
Consequently the rank-18 reduction is the field F_(137¹⁸).

Reconstruct the original coordinates by the same equations (108.2)–(108.4),
now at the variable K in (109.1). The public universal original lift
identities identify this rational construction with the unique original
quotient coordinates, with source and line regularity supplied by §§98,103.
The same substitutions in characteristic 137 satisfy the original
equations and q|e|²=1. Substituting j=ib into the unscaled (87.2) yields
identical C,D,Yc, with the scaling identities stated after (108.2).

Here are multiplication norms in the entire retained rank-18 algebra.
The values follow by multiplication and reduction in the basis
{X^e K^k: e∈{0,1}, 0≤k≤8}; the full multiplication determinants are:

| Element | Norm mod 137 |
|---|---:|
| Ds | 38 |
| a=1+BK² | 119 |
| λ²+4μ | 76 |
| affine line pivot A | 101 |
| Q leading coefficient q2 | 91 |
| Y-circle remainder leading coefficient | 112 |
| D-circle remainder leading coefficient | 112 |
| fraction-free r1 | 119 |
| β barβ | 107 |
| q | 34 |
| 1−q | 93 |
| Δ | 37 |
| δ | 93 |
| C barC | 74 |
| D barD | 107 |
| Yc barYc | 112 |
| evaluated bar(e) | 136 |

The corresponding formally barred reconstruction divisors are units too. Bars are evaluated by replacing i with −i while fixing the
real algebra variables; they are **not** finite-field Frobenius.
Every strict generic physical ray is in this retained algebra: §108
excludes exactly the removed component by δ=0, while §75 and the public
source theorem cover all remaining strict generic rays. No physical filter
is dropped, and all six root orders are retained.

### 109.2. The literal six-order polynomial and rank-288 norm

For two original coefficient points put E0=bar(e), E1=bar(e'). To avoid
confusing formal polynomial arguments with the parameter B, name the
nine arguments Ao,Bo,Co,Do,m,Po,So,Qo,To. They are
\[
\begin{aligned}
 P_o&=1-E_0,&S_o&=2-3E_0+E_0/q,\\
 Q_o&=1-E_1,&T_o&=2-3E_1+E_1/q',\\
 H_o&=\bar C/E_0,&K_o&=\bar D-H_o,\\
 F_o&=C'-D'/E_1,&J_o&=D'/E_1,\\
 A_o&=1/E_0+H_oF_o/R,&B_o&=-1/E_0+K_oF_o/R,\\
 C_o&=H_oJ_o/R,&D_o&=K_oJ_o/R,&m&=1+\bar GG'/R.
\end{aligned}\tag{109.6}
\]
In four formal variables α,β,γ,η put
\[
 L_0=A_o\alpha^2\gamma+B_o\beta\gamma+C_o\alpha^2\eta^2+D_o\beta\eta^2,
\quad
 L_1=A_o\beta^2\eta+B_o\alpha\eta+C_o\beta^2\gamma^2+D_o\alpha\gamma^2.
\]
Expand
\[
 (m^3+L_0^3+L_1^3-3mL_0L_1)
 (m^3+L_0^3+L_1^3-3mL_0L_1)_{\gamma\leftrightarrow\eta}.
\tag{109.7}
\]
Group monomials into their orbits under α↔β and γ↔η. Within either
pair, exponent differences are divisible by 3. Replace an equal-exponent
pair α^rβ^r by Po^r. Replace the unequal pair orbit by
Po^min(r,s) U_|r−s|/3, with U0=2, U1=So and
Un=So U(n−1)−Po³ U(n−2). Use the same rule with Qo,To for γ,η.
This defines the integer polynomial N with 508 terms. Expanding its
pullback Po=αβ, So=α³+β³, Qo=γη, To=γ³+η³ gives exactly (109.7).
Thus every coefficient is fixed by a finite integer calculation.
By §79.3 this is the product of all six relative ordinary overlaps,
divided by the nonzero physical normalization (3√q√q')⁶.

Use the monic divided-difference algebra
\[
 O_{\rm ret}=E[K,K',X,X']/
 \left(g(K),\frac{g(K')-g(K)}{K'-K},
 X^2-\frac{t(K)}{a(K)}X-\frac R{a(K)},
 X'^2-\frac{t(K')}{a(K')}X'-\frac R{a(K')}\right).
\tag{109.8}
\]
It is free of rank 9·8·2·2=288, and K'−K is a unit by source
separability. Evaluate N with (109.6), and call the resulting element
Noff,ret. This is the intrinsic construction of §104 on the retained
factor; no power-basis change or selected principal minor is introduced.

**Theorem 109.1.**
\[
 \det(M_{N_{\rm off,ret}}:O_{\rm ret}\to O_{\rm ret})\ne0
 \quad\hbox{in E},
\qquad \text{its reduction under (109.2) is }76.
\tag{109.9}
\]
**Proof.** Let φ be Frobenius on F_(137¹⁸). For a fixed first
coefficient point, the second endpoints with distinct K are precisely
φ^r(point), 1≤r≤17, r≠9. Indeed K has degree nine, so only r=0,9
have the same K. Put
\[
 P_N=\prod_{1\le r\le17,\ r\ne9}N(\mathrm{point},\phi^r(\mathrm{point})).
\]
Writing P_N=P0(K)+X P1(K), the ascending lists are

\[
\begin{aligned}
P_0&\leftrightarrow (100,38,135,85,10,84,91,136,79),\\
P_1&\leftrightarrow (56,91,5,14,70,41,108,63,85).
\end{aligned}
\]

In the degree-nine field, put T=P0²+λP0P1−μP1². The following finite
identities specify the scalar norm without selecting any physical root:
\[
 P_N^{1+137+\cdots+137^{17}}=76,
 \qquad
 \det\bigl([\operatorname{rem}(K^kT,g_9)]_j\bigr)_{0\le j,k\le8}=76.
\tag{109.13}
\]
Here [·]j denotes the K^j coefficient. Reduction of each product by the
monic g9 and X²−λX−μ proves these equalities in F137. Equivalently,
the multiplication determinant of P_N in the eighteen-element basis is 76. Under the etale splitting, the 288 points
of (109.8) are exactly these 18·16 ordered pairs; their product is the
full intrinsic determinant. The characteristic-zero implication is proved
in §109.4. ∎

### 109.3. Literal mixed determinant on all aligned factors

Tensor Aret with the **entire** aligned algebra of (106.3)–(106.7), of
rank ten. No aligned factor, singleton position or sign is discarded.
In that tensor, put Hs=s(a+ic)=κg,
\[
 z=\frac{2+i(s+d)}{2-i(s+d)},\qquad
 r=\frac{2+i(s-d)}{2-i(s-d)},\qquad E_0=\bar e,
\]
\[
\begin{aligned}
 A_m&=(z-1)/E_0+(H_s/R)(r-1)\bar C/E_0,\\
 B_m&=-3(z-1)/E_0+(H_s/R)(r-1)(\bar D-3\bar C/E_0),\\
 C_m&=3z+3\bar GH_s/R+(H_s/R)(r-1)(\bar G+2\bar C-\bar D),\\
 C_Z&=\begin{pmatrix}0&0&E_0/q\\1&0&-3E_0\\0&1&3\end{pmatrix},
\qquad N_m=\det(A_mC_Z^2+B_mC_Z+C_mI_3).
\end{aligned}\tag{109.10}
\]
These are exactly the original §90.14 definitions, including bar(C) and
all scalings. The cubic determinant covers every possible position of
the singleton among the generic cubic roots; swapping the other two
entries does not change the aligned overlap. Thus all six generic orders
and all aligned singleton positions are included.

Expanding the cubic determinant gives the following identity for q²Nm in
A=Am, Bm, C=Cm, E=E0 and q:
\[
\begin{aligned}
 &A^3E^2+3A^2B_mE^2q+9A^2CE^2q^2-6A^2CEq
 +3AB_m^2Eq\\
 &+9AB_mCEq^2-3AB_mCEq-6AC^2Eq^2+9AC^2q^2+B_m^3Eq\\
 &+3B_m^2CEq^2+3B_mC^2q^2+C^3q^2.
\end{aligned}\tag{109.11}
\]
The right-hand side is also q² times the ordered resultant of
Z³−3Z²+3EZ−E/q and AZ²+Bm Z+C; it agrees with the cubic multiplication
determinant. The q² multiplier is removed using the q unit.

The aligned reconstruction at (109.2), using the eight-by-eight minors
(106.5), has the following ascending d-coefficient lists:

\[
\begin{aligned}
Q_5&\leftrightarrow (110,132,51,129,25,129),\\
U&\leftrightarrow (106,132,53,4,116),\\
V&\leftrightarrow (93,53,10,70,41),\\
\theta&\leftrightarrow (80,9,17,8,109).
\end{aligned}
\]

All five roots are retained; the modular factorization is
−8(d−33)(d−21)(d−11)(d²−58d+13), followed by both roots of s²=Ka.
Reduction in the full quintic algebra gives P0=P1=P2=0 and
Ka(a²+c²)=R. Its rank-five unit norms are

| Element | Norm mod 137 |
|---|---:|
| d | 48 |
| 6d²b⁴(B−3)² | 41 |
| V | 92 |
| Ka | 90 |
| Ja | 110 |
| Fa | 91 |
| −b Ka Ja Fa | 67 |
| (2−id)²+Ka | 71 |
| (2+id)²+Ka | 76 |

The scalar leading and clearance factors of §90 also remain nonzero:
ell=129, r0=124, r2=30, R=41, b=28, 1−B=39, 1+B=100.
The full tensor algebra satisfies z bar(z)=r bar(r)=1 and
Hs bar(Hs)=R, with both s signs retained.

**Theorem 109.2.** On the rank-180 tensor algebra,
\[
 \det(M_{N_m})\ne0\quad\hbox{in E},
 \qquad\text{its reduction under (109.2) is }46.
\tag{109.12}
\]
**Proof.** Use the norm tower of ranks 180→90→18→9→1.
The first norm eliminates s, the next eliminates d, the next X, and the
last K. The five elimination pivots for the d-norm have rank-18 norms
34,95,127,109,29, all nonzero. After the X norm the ascending K list is

\[
\begin{aligned}
(81,22,126,120,99,30,56,65,2).
\end{aligned}
\]

and its rank-nine multiplication determinant is 46. Equivalently form the
full 180-by-180
multiplication matrix of the literal Nm in basis
s^ε d^j X^e K^k, indexed by 90ε+18j+9e+k, with
ε,e∈{0,1}, 0≤j≤4, 0≤k≤8. Reduction uses only the four displayed monic
relations. Its determinant is 46. This follows either by the norm tower just given or
by ordinary elimination in F137.
The characteristic-zero implication is proved next. ∎

### 109.4. Why these reductions prove characteristic-zero nonvanishing

All constructions use rational operations in the literal public source
coefficients and the explicit W coordinates. Localize the integral
coefficient ring at every scalar denominator and multiplication norm
actually inverted. The nonzero residues above show that the good map
(109.2) is defined on this local integral model. This is **not** a field
homomorphism from a characteristic-zero field to a positive-characteristic
field. The monic degrees stay 9,2 and respectively 9,8,2,2 or 9,2,5,2;
hence the displayed power bases specialize without a dimension loss.
Multiplication matrices and their full determinants commute with reduction.
A zero norm in E would therefore reduce to zero, contradicting 76 or 46.

Since E is a field, its complex embeddings are injective. The nonzero
norms therefore apply at both b=+√B* and b=−√B*, including the two
coefficient-conjugate choices of i. This proves simultaneous invertibility
on the complete retained algebras, not only at one modular sample or one
selected real ray. The identification of coefficient functions with the
original quotient uses the original equations and public universal lift
identities; a modular vanishing check alone is not used to prove a
characteristic-zero identity.

## 110. Local triple, basis and fixed-pair consequences at W

**Theorem 110.1.** At b=±√B*, for the actual H0(b):

1. No three noncanonical original common-flat rays are mutually orthogonal.
2. The only complete common-flat input orthonormal basis is the canonical
   basis, up to phases and column permutation.
3. The fixed pair (I6,H0(b)) cannot belong to a quartet of MUBs.

**Proof.** The original classification §75 covers every noncanonical ray,
including constant channels, repeated pairs, optional channel choices and
phase poles. By (109.4) and source separability, §§98,99,103 apply.
Away from Q8 every generic ray has both channels three-distinct, and the
punctured zero-mean lemma permits its ordinary upper-channel gauge. Thus
no one-endpoint Θ change or root-order restriction is needed.

Section 108 excludes strict generic lifts only on K*. Every strict generic
physical ray is consequently represented by Aret. If an orthogonal pair
had K≠K', its evaluations would define a homomorphism from Oret to C.
One of the six factors in (109.7) would vanish, contradicting invertibility
of Noff,ret. Therefore every generic orthogonal pair has equal K.

For fixed real physical K, a=1+b²K²>0 and R>0. The radial equation
aX²−tX−R=0 has two distinct nonzero real roots, since its discriminant is
t²+4aR>0. If two rays use the same root, original lift uniqueness gives
the same quotient coefficients and cubic; its six orders are precisely
synchronous S3 permutations. For opposite roots X'=-R/(aX),
\[
 G'=X'(1+ibK)=-R/\bar G.
\tag{110.1}
\]
This is exactly the mean action of the original antiunitary
Θ(x,y)=(-bar(y),bar(x)), with |κ|²=R. Θ preserves genericity here
because both channels are three-distinct. It supplies an actual solution
at the opposite mean, and original lift uniqueness identifies its whole
coefficient point. Thus every generic edge lies in one S3w∪S3Θw.
Theorem 82.1 makes the induced graph on that entire union bipartite.
An all-generic triple would lie in the union of any one of its vertices,
contradicting this theorem.

Theorem 109.2 excludes every generic/noncanonical-aligned edge, using
all aligned factors, signs and singleton positions. The all-aligned case
is excluded by Theorem 85.1, which applies on the full puncture and
explicitly permits different singleton positions, different symmetry unions,
constants and poles. These cases exhaust noncanonical triples.

By Proposition 60.1 and Corollary 60.4, any common-flat ray orthogonal
to a canonical ray is one of the other canonical rays. Hence a complete
common-flat input basis containing a canonical ray is canonical; one
containing no canonical ray would contain a forbidden noncanonical triple.
This proves input basis uniqueness without a covariance hypothesis.

For an output unitary basis B0 unbiased to (I6,H0), put Winput=H0* B0,
where * denotes the adjoint. Both Winput and H0 Winput=B0 are flat, so
Winput must be Ccan/√6, up to phases and permutation. The unique output
column-ray set is therefore H0 Ccan/√6, not the untransported input basis.
Two additional bases in a quartet would have this same column-ray set;
their relative unitary is monomial and cannot be flat. This proves the
fixed-pair conclusion. ∎

This proof uses the retained ranks 288 and 180 after the justified boundary
exclusion. It does not assert that the original full-rank 360 norm z_off,
the original rank-200 mixed norm h_m, or P of §105 is nonzero at W.
It is a local application of the §104.3 argument on the retained algebras.

## 111. The explicit finite exceptional set and remaining guard

**Corollary 111.1.** Let Z24 and J24 be exactly (105.1). The enlarged set
Z26 defined below has 26 signed points, all satisfying Theorem 110.1.
The residual guard can be reduced by J26 as described below.

**Proof.** The polynomial W has one root in (0,1). It has no common root
with Jsrc by the full-source derivative resultant and separability in
§109.1. Equations (109.4) prove separation from Q8,A10,A14. For the last
old factor, exact Euclidean division against the complete printed Q90
coefficient list gives gcd(W,Q90)=1; at the good map Q90(99)=8≠0.
Irreducibility of W also makes this nonzero reduction sufficient for
separation. This separation from Q90 serves the finite-set count; it is not an
additional reconstruction assumption.

Define
\[
 J_{26}(b)=J_{24}(b)W(b^2),\qquad
 Z_{26}=Z_{24}\cup\{-\sqrt{B_*},\sqrt{B_*}\}.
\tag{111.1}
\]
The previously established positive-B counts for
L,P48,P98,Q8,A10,A14,Q90 are respectively 1,2,3,2,1,1,2,
with all earlier factors mutually disjoint. Their sum is 12; W contributes
one new positive B value and hence two new signed parameters.
**The explicit finite exceptional set now has 26 signed points**, each
with the triple, basis and fixed-pair conclusion. Earlier interval and
neighborhood conclusions retain their existing scopes.

For an updated residual guard, start with the original P of §105.3 and
repeatedly divide by its monic gcd with J26 until that gcd is constant;
clear rational constants and take positive-leading primitive integer
content. Call the result Pres,26. This terminates by degree descent and
removes only primary powers supported on J26. No claim that W divides P
is required. If Pres,26(b)≠0 at a real punctured parameter, then either
P(b)≠0 or J26(b)=0. The first case is Theorem 105.1 and the second is
an earlier fibre theorem or Theorem 110.1. Thus the full guarded consumer
continues to hold after this justified removal. ∎

The guard implication is restricted to Pres,26≠0 together with the
separately closed fibres. It gives no uniform nonvanishing assertion or
new neighborhood radius. Proposition 107.1 counts only aligned
noncanonical rays with singular reflection-odd block; it does not count
all common-flat rays or describe the full phase Jacobian.


## 112. Symmetry-normalized overlap norms and physical multiple zeros

Retain the original family, input convention, algebras and overlap
polynomials of §§104–105. Put R=3−b² and let S be a localization of
Q(i)[b] on which those original constructions are regular. At a real
0<|b|<1 outside Z24, §105.2 supplies this regularity. Let A be the
rank-twenty generic algebra, Ba the rank-ten aligned algebra, and O the
rank-360 distinct-projective-mean algebra. Bars conjugate i and fix the
real algebra generators. All statements below retain the physical tests
and every relative root order.

**Theorem 112.1.** There are specified nonzero real rational functions
Do,Dm and a specified rational-function unit η such that
\[
 z_{\rm off}=D_o^2,\qquad h_m=\eta^{15}D_m,
 \qquad \eta\bar\eta=1.
\tag{112.1}
\]
The unit η is regular and invertible at every real punctured parameter
outside Z24. An original generic orthogonal pair in different
S3–Θ unions forces a zero of Do of multiplicity at least two, and hence
a zero of zoff of multiplicity at least four. An original generic/aligned
orthogonal pair forces a zero of Dm and hm of multiplicity at least two.
These lower bounds do not assert that the multiplicities are even.

### 112.1. Full-algebra overlap transport

**Proof.** Let ι be the radial involution of the original generic algebra.
It fixes K and sends G to −R/bar(G). Normalize a generic vector to upper
channel sum three, writing v=w/√q on physical points. Its coefficient
form, without a choice of √q, is
\[
 v=(Z_j,L_p(Z_j)/\kappa)_{j=0}^2,
\quad E_p=\bar e_p,\quad
 f_p(Z)=Z^3-3Z^2+3E_pZ-E_p/q_p,
\]
\[
 B_p(Z)=\frac{Z^2-3Z+3E_p}{E_p},\qquad
 L_p(Z)=G_p+C_p(Z-1)+D_p(B_p(Z)-1).
\tag{112.2}
\]
Here Bp(Z) is the conjugate normalized root: q_p Z B_p(Z)=1
modulo f_p, and its physical squared modulus is 1/q_p. Define
\[
 F_p(Z)=1+
 \frac{\bar D_p(Z-1)+\bar C_p(B_p(Z)-1)}{\bar G_p}.
\tag{112.3}
\]
The following three remainders modulo f_p vanish in A[Z]:
\[
 f_{\iota p}(F_p(Z)),\qquad
 L_{\iota p}(F_p(Z))+\frac{R B_p(Z)}{\bar G_p},\qquad
 F_{\iota p}(F_p(Z))-Z.
\tag{112.4}
\]
For a proof using the complete original field rather than a pairwise
sampling argument, take the actual analytic solution interval of §89.2.
On it both channels are three-distinct, and applying Θ with upper mean
restored gives (112.3), the lower-channel identity in (112.4), and the
involutive return map. Each remainder has degree at most two and
vanishes at all three distinct roots on that interval. Every coefficient
therefore vanishes there. Fieldness of the original degree-twenty algebra
and the field identity principle of §89.2 make these coefficient
identities in A. The same argument gives the original circle identities
and q_(ιp)=q_p G_p bar(G_p)/R.

The three identities identify the full reciprocal-root multisets in a
faithful generic splitting extension, and give
\[
 v_{\iota p}=-\frac{\bar\kappa}{\bar G_p}\,\Theta v_p.
\tag{112.5}
\]
Adjoining κ if necessary is a faithful extension; the scalar identities
below belong to the original base. Apply (112.4) independently to both
factors, not to a single branch of the reducible pair algebra. All six
relative root orders are retained. The resulting polynomial identities
descend from the splitting extension to O. Torsion-freeness then extends
them to the regular localization; no cubic discriminant or channel
collision divisor is added to its specialization hypotheses.

Let N be exactly Noff of §104.2. If S0 swaps the two endpoints and J
applies ι to both, put
\[
 T=\frac{\bar G_pG_q}{R}.
\]
The product of the six overlaps ⟨vp,Pvq⟩/3 gives
\[
 S_0(N)=\bar N,\qquad J(N)=\bar N/\bar T^6,
 \qquad S_0(T)=\bar T,\qquad J(T)=1/\bar T.
\tag{112.6}
\]
Indeed endpoint reversal replaces P by P⁻¹, and Θ commutes with each
synchronous permutation. Equation (112.5) supplies the scalar in the
second identity. This proves (112.6) in the full original algebra, not
only on physical evaluations.

### 112.2. The exact rank-180 square root

Set
\[
 L=N/T^3,\qquad \tau=JS_0,\qquad E=O^\tau.
\]
The involutions commute, and (112.6) yields
\[
 \tau(L)=L,\qquad S_0(L)=J(L)=\bar L.
\tag{112.7}
\]
The unit u=K−K′ of §104.1 is τ-anti-invariant. Since 2 is invertible,
projection to the two eigenspaces, followed by division of the
anti-invariant part by u, gives
\[
 O=E\oplus uE.
\tag{112.8}
\]
Thus E is finite projective of rank 180, and free over the chosen
localization of the PID Q(i)[b]. Define
\[
 D_o=\operatorname{Nm}_{E/S}(L).
\tag{112.9}
\]
Multiplication by L is the same on the two summands of (112.8), so
Nm_O(L)=Do². Each generic point occurs eighteen times as each endpoint
in the distinct-mean algebra. The two radial roots at a fixed K have
product −R/(1+b²K²), and G bar(G)=(1+b²K²)X². Hence
\[
 \operatorname{Nm}_A(G\bar G)=R^{20},\qquad
 \operatorname{Nm}_O(T)=
 \frac{\operatorname{Nm}_A(G\bar G)^{18}}{R^{360}}=1.
\tag{112.10}
\]
These are rational-function identities, proved in the generic splitting
and valid at every regular specialization. Therefore zoff=Do² exactly,
with no omitted scalar factor. Bar preserves E, and S0 acts on E and
sends L to bar(L); determinant invariance gives Do=bar(Do). Thus
Do∈Q(b). Its nonvanishing as a rational function follows from the
nonzero half witness for zoff. This removes one specified forced square,
not an assumed squarefree part or any further perfect power.

### 112.3. A real mixed normalization

In Ba put H=s(a+ic)=κg. The aligned involution ja fixes d and changes
s to −s. Direct substitution in the phase formulas gives
\[
 (z,r,H)\longmapsto(\bar r,\bar z,-H),\qquad
 w_{j_a a}=(-g)\Theta w_a.
\]
Together with (112.5), the three-position overlap product of (90.14)
therefore satisfies, for Jm=ι⊗ja,
\[
 J_m(N_m)=(H/G)^3\bar N_m.
\tag{112.11}
\]
The singleton positions are merely permuted. The same universal product
identity holds on the entire aligned algebra, whose circle relation is
H bar(H)=R. Define
\[
 g_N=\operatorname{Nm}_A(G),\qquad
 h_N=\operatorname{Nm}_{B_a}(H),\qquad
 \eta=h_N^2/g_N.
\tag{112.12}
\]
All are units on the regular domain. Their ranks give
\[
 \eta\bar\eta=1,\qquad
 \operatorname{Nm}_{A\otimes B_a}(H/G)
   =h_N^{20}/g_N^{10}=\eta^{10}.
\]
Taking norms in (112.11) gives hm=η³⁰bar(hm), so
\[
 D_m=h_m/\eta^{15}=\bar D_m\in\mathbb Q(b).
\tag{112.13}
\]
The half witness makes Dm nonzero. Multiplication by the unit η¹⁵
preserves local zero orders. Equation (112.11) is a conjugation pairing;
it does not imply that Dm is a square.

### 112.4. Two distinct physical evaluations

A matrix over a local parameter DVR whose reduction has corank r has
determinant valuation at least r: constant invertible row and column
operations reduce an invertible maximal minor, and every entry of the
remaining Schur complement is divisible by the parameter. Also, if an
element of a finite algebra vanishes at r distinct complex characters,
its multiplication cokernel has dimension at least r. The distinct
maximal ideals are comaximal, and evaluation surjects onto C^r through
that cokernel. This argument retains nilpotents and ramified components.

Consider a physical cross-union generic edge at b0 outside Z24. Equal K
would put both endpoints in one S3–Θ union by §104.3; thus Kp≠Kq.
Its ordered evaluations (p,q) and (q,p) both annihilate L and give two
distinct characters of E. Indeed (112.8) identifies
O≅E[Y]/(Y²−c), where c=u² is a unit of E. Its two extensions of each E-character
are exactly a τ orbit. The two displayed pairs cannot be equal, and
cannot be τ partners unless p=ιp and q=ιq. At a physical point the
radial roots have negative product −R/(1+b²K²); they are distinct, so
no such fixed point occurs. Thus multiplication by L on E has corank
at least two, proving ord_b0(Do)≥2 and ord_b0(zoff)≥4.

For a physical mixed edge, (p,a) and (ιp,ja a) are distinct characters
annihilating Nm. Θ preserves orthogonality, and the regular original
coverage retains both endpoints. Distinctness follows already from
p≠ιp. The full rank-200 multiplication map has corank at least two,
so ord_b0(hm)=ord_b0(Dm)≥2. No reducedness hypothesis on the other
algebra points is needed.

For precision, fibre length alone would not suffice: in S[x]/(x²−t),
Nm(x)=−t has a simple zero despite the length-two nonreduced fibre.
The proof counts distinct characters after the genuine quotient
(112.8). Nor does corank two imply even valuation: the diagonal matrix
(t,t,t) has determinant t³. These algebra examples delimit the argument;
they are not asserted to occur as MUB fibres. This proves Theorem 112.1. ∎

## 113. Exact orders of the original two norms at W

**Theorem 113.1.** Let w(b)=W(b²), with W from §106. Then, for the
original full norms of §105,
\[
 v_w(z_{\rm off})=0,\qquad v_w(h_m)=4.
\tag{113.1}
\]
Consequently w has exponent exactly eight in the real numerator product
P of §105.3. These are local factor statements; no other norm root is
classified by them.

### 113.1. Full original boundary identification

**Proof.** By §106.4, w is irreducible over Q(i). Use the characteristic-zero
W field and both signs of the aligned point in §107. To make the full
ray identification explicit, adjoin σ=s/b with
σ²=(Bx*²+4θ*)/B and j=ib with j²=−B. Obtain A*=ba* and c* from the
original scaled Cramer equations, and put
\[
 z=\frac{2+j(\sigma+x_*)}{2-j(\sigma+x_*)},\qquad
 r=\frac{2+j(\sigma-x_*)}{2-j(\sigma-x_*)},\qquad
 H=\sigma(A_*+jc_*),
\]
\[
 G_s=H(2+r)/(2+z),\qquad X_s=(G_s+\bar G_s)/2.
\tag{113.2}
\]
The original generic u,v at Xs are exactly the affine-line and
fraction-free-remainder expressions (108.2)–(108.4). Retain both roots
in this same quadratic algebra. With their E=bar(e) and lower-channel
polynomial L from (112.2), exact reduction gives
\[
 E=\frac{3(1+2z)}{(2+z)^2},\qquad
 L\left(\frac3{2+z}\right)=\frac{3H}{2+z},\qquad
 L\left(\frac{3z}{2+z}\right)=\frac{3Hr}{2+z},
 \qquad q=\frac{|2+z|^2}{9}.
\tag{113.3}
\]
These equalities are finite characteristic-zero identities: substitute
(108.4), reduce σ² by its displayed relation, reduce j²=−B, and divide
each remaining rational coefficient by W. The remainders are zero.
The original E-circle, Y-circle and D-circle are zero by the same
substitution. Both 2+z and 1−z are units; their norms are nonzero in
the W field. Equivalently, at its complex embedding with real positive b,
§107 gives unit phases and §108.7 gives 1/9<q<1, excluding z=1;
faithfulness of that embedding proves the stated field nonvanishing.

Put α=3/(2+z) and β=3z/(2+z). Equations (113.3) make the complete
original cubic (Z−α)²(Z−β), with α≠β, and identify both lower-channel
values. Thus the full mean-normalized boundary vector is
\[
 v_*=\frac3{2+z}(1,1,z;g,g,gr).
\tag{113.4}
\]
This proves the relative phase and interpolation, not only the mean G
and q identities.

### 113.2. The full ordinary norm is a unit

For any retained generic point p and boundary aligned point a, the six
orders of (113.4) repeat each of its three singleton positions twice.
The original six-order and three-position product definitions give
\[
 N_{\rm off}(p,*)=\frac{N_m(p,a)^2}{(2+z)^6}.
\tag{113.5}
\]
The second endpoint scalar is not conjugated. The reverse identity is
its formal bar. This is a polynomial product identity under repeated
root specialization, or equivalently an identity in the universal
splitting algebra. It does not treat evaluation at the two distinct
root values as a faithful map from the nonreduced cubic algebra.

The retained rank-180 mixed norm is nonzero by §109, with residue 46.
Hence Nm is a unit on the retained-generic × entire-aligned algebra,
and remains a unit on its boundary-aligned quotient. Equation (113.5)
makes both rank-36 ordinary cross pieces units. The complete source
factorization at W splits the rank-360 off-diagonal algebra into these
two pieces and the rank-288 retained off-diagonal piece. There is no
boundary × boundary piece, since both means would equal K*.
The retained ordinary norm, with residue 76, makes the last piece a
unit too. Therefore the full zoff is nonzero in the W field. Its
regularity excludes a denominator pole, proving v_w(zoff)=0.

### 113.3. Characteristic-zero lower bound for the mixed order

Work over the DVR Q(i)[b]_(w). The complete original coordinates and
mixed matrix are regular there by §§105,107–109. The source, radial and
aligned algebras are étale at w. For example their displayed good map
has retained field F_(137^18), removed radial discriminant 40, a
squarefree aligned quintic and nonzero norm of Ka. Nonzero reductions
certify the corresponding characteristic-zero discriminants are units
modulo w.

After an unramified splitting extension, hm is the determinant of the
direct sum of the 200 cubic matrices (109.10), of total size 600.
For the boundary generic point and its opposite Θ-aligned partner,
Theorem 82.1 gives all three singleton overlaps zero. By (113.3),
the quadratic Q(Z)=Am Z²+Bm Z+Cm therefore vanishes at α and β.
Multiplication by Q in C[Z]/((Z−α)²(Z−β)) has kernel dimension
at least two, namely deg gcd(Q,(Z−α)²(Z−β)). The reverse radial and
aligned sign pair supplies a second distinct block of corank at least
two. The complex embedding with real positive b is faithful, so this
rank statement holds over the residue field. The determinant argument
of §112.4 gives v_w(hm)≥4.

### 113.4. A single exact local expansion proves equality

Use the Gaussian prime above 137 with i↦37 and the field
k=F137[ρ]/(ρ²−40), where 40 is a nonsquare. In k[ε]/(ε⁵) put
B=99+ε. Let b lift 28 with b²=B; let K lift 31 as a root of the
**complete** F0(B,K); let t=Ns/Ds, with Ds=∂K F0 before any factor
removal. Let X± be both roots of
\[
 X^2-\frac{tX}{1+BK^2}-\frac{3-B}{1+BK^2}=0.
\]
Let d lift 21 as a root of the complete Q5, let θ lift 73 as a root of
Φ(b,d,θ), and let s lift 78ρ with s²=d²+4θ. The relevant constant
Hensel derivatives are 2b=56, Ds(31)=73, Q5′(21)=58 and Φθ=10;
the radial and sign roots are also simple. Successive Newton steps
therefore determine all series uniquely. In ascending ε powers they are
\[
\begin{aligned}
 b&=(28,115,99,68,57),&K&=(31,108,130,47,41),\\
 d&=(21,78,122,23,93),&\theta&=(73,27,80,0,71),\\
 s&=\rho(78,78,80,88,87),\\
 X_+&=(84+69\rho,64+58\rho,41+127\rho,44+67\rho,86+114\rho),
\end{aligned}\tag{113.6}
\]
and X− is obtained by ρ↦−ρ. Three iterations y↦y−f(y)/f′(y)
suffice modulo ε⁵.

Use the original Cramer formulas for a,c. Substitution gives
P0=P1=P2=0 and (d²+4θ)(a²+c²)=3−B modulo ε⁵. Reconstruct the generic
u,v on each radial lift by (108.2)–(108.4); the original three equations
vanish modulo ε⁵, with every divisor a unit. Evaluation of the literal
cubic determinant (109.10), or of its equal expanded resultant (109.11),
gives
\[
\begin{array}{c|cc}
 &s&-s\\\hline
 X_+&49+47\rho+O(\varepsilon)&(108+77\rho)\varepsilon^2+O(\varepsilon^3)\\
 X_-&(108-77\rho)\varepsilon^2+O(\varepsilon^3)&49-47\rho+O(\varepsilon)
\end{array}
\tag{113.7}
\]
Their product is 51ε⁴ modulo ε⁵, since the two constant coefficient
norms are 77 and 6, respectively, and 77·6=51 modulo 137.

The other aligned d factors form the monic quartic
\[
 (d-33)(d-11)(d^2-58d+13).
\]
Retain both signs over this entire quotient. At ε=0 use the public
ascending shape θ=(80,9,17,8,109) and the original Cramer formulas.
All three equations and the circle hold. The two rank-eight norms of
Nm, for X+ and X−, are 26+100ρ and 26−100ρ; their product is 31.
These values are determined by the quadratic sign norm followed by
the multiplication determinant on 1,d,d²,d³ in this quartic. Thus the
complete removed-mean rank-twenty contribution is 74ε⁴ modulo ε⁵.
The complementary retained rank-180 norm has constant value 46 by
§109. Consequently the original complete norm satisfies
\[
 h_m=46\cdot31\cdot51\varepsilon^4+O(\varepsilon^5)
     =116\varepsilon^4+O(\varepsilon^5).
\tag{113.8}
\]

For the characteristic-zero upper bound, use the local integral model
at this Gaussian prime and B=99. The complete source leading
coefficient, full derivative divisors, reconstruction divisors and
aligned phase divisors are units by the public retained and removed
unit tables and the displayed simple-root constants. The literal full
multiplication determinant therefore belongs to this local model.
The leading coefficient of W is a unit too. Monic polynomial division,
or Gauss's lemma after multiplying the unit denominators, implies that
characteristic-zero divisibility by w⁵ would persist in this model.
Its reduction would then vanish modulo ε⁵, contrary to 116≠0.
Together with the lower bound this proves v_w(hm)=4. The normalization
is also fixed by
\[
 W'(99)=118,\qquad (h_m/W^4)(99)=116/118^4=84\pmod{137}.
\tag{113.9}
\]
This one local expansion is not an interpolation of the global norm.
Finally w is real, regularity excludes it from both reduced denominators,
and conjugation preserves its valuation. Equation (113.1) therefore
gives exponent 0+0+4+4=8 in P. ∎

## 114. A derivative-gcd guard for the remaining physical zeros

**Corollary 114.1.** Write the specified real functions of Theorem 112.1
in reduced form Do=ao/co and Dm=am/cm over Q[b], normalizing the
nonzero numerators to be monic. Define
\[
 r_o=\gcd(a_o,a_o'),\qquad r_m=\gcd(a_m,a_m').
\tag{114.1}
\]
Every physical cross-union generic edge outside Z24 lies over ro=0,
and every physical mixed edge outside Z24 lies over rm=0. Thus a simple
zero of ao excludes the former kind of edge, and a simple zero of am
excludes the latter kind of edge.

**Proof.** The denominators do not vanish on the regular real domain,
so Theorem 112.1 gives numerator multiplicity at least two. In
characteristic zero a root has multiplicity at least two precisely when
it is a common root of the polynomial and its derivative. This gives
both assertions. Constant numerators are allowed and have gcd one.

Start with ro rm and remove all primary powers supported on J26 by
the terminating repeated-gcd procedure of §111; clear constants and
take the positive-leading primitive integer normalization. Denote the
result Rmult,26. If Rmult,26(b)≠0 for 0<|b|<1, then either b is a
separately closed J26 fibre, or neither forbidden type of edge exists.
The within-union bipartite graph and all-aligned obstruction then give
no noncanonical orthogonal triple. Single-canonical rigidity gives the
same unique input basis and transported output basis as §110, and
therefore the same fixed-pair no-quartet conclusion. ∎

This construction takes the two derivative gcds separately after
removing the specified ordered-pair square and harmless mixed gauge.
Applying gcd(P,P′) directly would retain built-in squares from
zoff=Do² and coefficient conjugation, and would not give this test.
Theorem 113.1 identifies the already closed W contribution: its order
in ao is zero and in am is four, hence in rm is three before J26 removal.
Passing between b and B=b² preserves local multiplicities in the
puncture because 2b≠0.

The corollary does not compute the remaining gcd coefficients, their
degrees or real-root counts, or prove that their zero set is strictly
smaller than the earlier guard. Other repeated norm zeros need not be
physical. The explicit separately closed finite set remains the
26 signed points of §111, with all earlier interval and neighborhood
results retaining their own scope. No whole-branch conclusion follows
without resolving the remaining physical zeros or an independent argument.


## 115. The mixed derivative gcd preserves all regular real zeros

**Proposition 115.1.** For the original mixed norm hm and its specified
real normalization Dm in §112, every real zero b0 with 0<|b0|<1 and
b0 outside Z24 has order at least two. Consequently the reduced numerator
am of Dm and rm=gcd(am,am′) have the same real zero set on that domain.
After removing all J26-supported primary factors from each polynomial,
their real zero sets in the puncture are again equal.

**Proof.** Put O=C[b]_(b−b0). By §105.2 the actual algebra
T=A⊗Ba is finite free of rank 200 over O, with all required original
units. In particular a=1+b²K² and X are units by the monic radial
equation aX²−tX−R=0, where R=3−b². Since
G=X(1+ibK) and (1+ibK)(1−ibK)=a, both G and bar(G) are units.
The aligned identity H bar(H)=R makes H and bar(H) units as well.
These assertions concern the entire algebra, not only physical points.

Write c0 for coefficient conjugation, fixing b,K,X,d,s and conjugating
complex scalars. It preserves O because b0 is real. The two original
involutions
\[
 \iota(K)=K,\quad\iota(X)=-R/(aX),\qquad
 j_a(d)=d,\quad j_a(s)=-s
\]
have real tower-coordinate formulas, so they commute with c0. Thus
τ=(ι⊗ja)c0 is a conjugate-linear involution of T. Let T0=T/(b−b0)T.
For a complex character χ:T0→C define another complex character by
\[
 (\sigma\chi)(f)=\overline{\chi(\tau f)}.
\tag{115.1}
\]
The overline in (115.1) conjugates the evaluated number; it is distinct
from c0 acting on algebra coefficients. The two conjugations make σχ
C-linear, and σ²χ=χ.

If χ(K)=k and χ(X)=x, then
\[
 (\sigma\chi)(K)=\bar k,\qquad
 (\sigma\chi)(X)=
 -\frac{R_0}{(1+b_0^2\bar k^2)\bar x},\qquad R_0=3-b_0^2>0.
\]
A fixed character would have k real and
\[
 (1+b_0^2k^2)|x|^2=-R_0,
\tag{115.2}
\]
which is impossible: x is nonzero, and the left side is positive while
the right side is negative. Hence σ has no fixed character. This
argument does not assume that the character satisfies physical tests.

Coefficient conjugation of the full-algebra identity (112.11) gives
\[
 \tau(N_m)=\left(\frac{\bar H}{\bar G}\right)^3N_m.
\tag{115.3}
\]
Its multiplier is a unit. Therefore χ(Nm)=0 implies (σχ)(Nm)=0,
and these are distinct zero characters. If hm(b0)=0, multiplication by
Nm on T0 is singular, so Nm is a nonunit and lies in a maximal ideal.
The residue field is C, giving such a character χ. The two distinct
maximal ideals are comaximal, and evaluation induces a surjection
T0/(Nm)→C². The multiplication cokernel therefore has dimension at
least two, including when T0 is nonreduced. The local corank argument
of §112.4 yields ord_b0(hm)≥2.

The factor η in Dm=hm/η¹⁵ is a regular unit, so Dm has the same order.
Its reduced denominator is nonzero at b0. Thus every real zero of am
on this domain is also a zero of am′, proving the asserted equality
with rm. Saturation removes precisely the J26-supported factors;
neither saturated polynomial retains a zero in Z26, and their remaining
real zero sets agree by the preceding argument. ∎

This proposition strengthens the mixed necessity in §114 without changing
its implication. The mixed derivative operation itself discards no
regular real norm zero, including one supported only on nonphysical
complex characters. A further factor or real-root analysis could still
prove that the common remaining real zero set is empty; multiplicity
alone does not distinguish physical from nonphysical points over it.
No parity assertion, corresponding statement for Do, or additional
closed parameter fibre is asserted. The explicit finite union of closed fibres
remains the 26 signed points of §111; all earlier interval and
neighborhood results retain their own scope.


## 116. An intrinsic aligned-mean quintic and exclusion of opposite generic means

### 116.1. Statement and original charts

Use the actual family, original ray classes and finite set \(Z_{26}\) of
§111. All bars in this section are complex conjugates at real physical
coordinates. Put \(B=b^2\), \(R=3-B\). For the aligned chart (90.11),
write \(H=\kappa g\), and define its scaled channel mean
\[
 G_a=H\frac{r+2}{z+2}.
 \tag{116.1}
\]
Both factors in the fraction are nonzero because \(|z|=|r|=1\), and
\(|H|^2=R>0\). In particular \(G_a\ne0\).

**Proposition 116.1 (repo-derived).** At every real
\(0<|b|<1\) outside \(Z_{26}\), no original strict generic mean \(G\)
equals \(G_a\) or \(-R/\bar G_a\) for an original noncanonical aligned
ray. More precisely, whenever \(\operatorname{Re}G_a\ne0\), the two
means cannot have both the same projective coordinate and radial trace
\[
 K(G)=\frac{\operatorname{Im}G}{b\operatorname{Re}G},\qquad
 t(G)=\frac{|G|^2-R}{\operatorname{Re}G}.
 \tag{116.2}
\]
Consequently, for every such physical generic–aligned pair,
\[
 M=z+2+\frac HR(r+2)\bar G\ne0.
 \tag{116.3}
\]
The assertion retains both aligned radial signs, every repeated-pair
position, constant-channel subcases, all generic root orders and the
optional channel presentations supplied by §105.2.

The proof below uses only the original equations and finite polynomial
identities. It does not assume that two different projective classes
cannot be orthogonal. Thus it excludes one source subcase without
asserting nonvanishing of the full mixed overlap norm or closing an
additional parameter fibre.

By §105.2, outside \(Z_{24}\subset Z_{26}\) every generic ray has its
regular selected-channel presentation
\[
 G=X(1+ibK),\quad X\in\mathbb R\setminus\{0\},\quad
 F_0(B,K)=0,\quad t=N_s/D_s,\quad D_s=\partial_KF_0\ne0,
 \tag{116.4}
\]
with precisely the normalization (100.1). The original strict conditions
\(0<q<1\), \(\delta<0\), and all source reconstruction conditions
are retained. No channel-collision determinant is substituted for the
strict cubic discriminant.

For aligned rays use (90.1)–(90.11):
\(K_a=d^2+4\theta=s^2>0\), \(H=s(a+ic)\), and the original
Cramer values \(a=A_a,c=C_a\). The physical factors
\(b,K_a,F_a=d^2+(\theta+1)^2\) are nonzero; (90.2) excludes
\(J_a=bd-\theta+3=0\) by consistency, without a parameter guard.
The complete aligned clearance in §105.2 supplies \(Q_5=0\),
\(\theta=U/V\) and \(V\ne0\) outside the already closed coordinate
exceptions. It retains constant channels and accounts for every actual
Cayley pole. No new zero of an original denominator is discarded here.

### 116.2. Mean and radial-trace identities, including the added zero chart

Set
\[
 A=3-\theta,\quad L=\theta^2+10\theta+9+3d^2,\quad
 M_r=aL+2cAd,\quad M_i=cL-2aAd,
\]
\[
 u=(s+d)/2,\quad v=(s-d)/2,\quad
 D_0=A^2+(2s-d)^2.
\]
The Cayley formulas and \(s^2=d^2+4\theta\) give
\[
 \frac{r+2}{z+2}=\frac{L-2iAd}{D_0},\qquad
 D_0=(1+v^2)(9+u^2)>0,
 \tag{116.5}
\]
\[
 \operatorname{Re}G_a=\frac{sM_r}{D_0},\quad
 \operatorname{Im}G_a=\frac{sM_i}{D_0},\quad
 |G_a|^2=R\frac{D_0+8sd}{D_0}.
 \tag{116.6}
\]
For the last equality, the numerator difference is exactly
\((1+u^2)(9+v^2)-(1+v^2)(9+u^2)=8sd\).
Thus, on \(M_r\ne0\),
\[
 K(G_a)=\frac{M_i}{bM_r},\qquad t(G_a)=\frac{8Rd}{M_r}.
 \tag{116.7}
\]
These expressions do not depend on the sign of \(s\). Direct substitution
of \(-Rx/(x^2+y^2),-Ry/(x^2+y^2)\) for \(x,y\) also shows that
both invariants (116.2) are unchanged by \(G\mapsto-R/\bar G\).

If \(M_r=0\), then (116.6) and \(G_a\ne0\) make \(G_a\) and
its opposite radial mean nonzero purely imaginary numbers. Neither can
equal (116.4), whose real part is \(X\ne0\). This treats the entire
added zero chart before forming (116.7). It uses the complete public
regular generic coverage, rather than asserting a separate exclusion of
unexamined vertical source strata. No division by \(d\) is used.

### 116.3. Two integral intrinsic identities

For a polynomial in \(b,d\) even after \(d=bx\), write
\(\mathcal E(P)(B,x)=P(b,bx)\), with \(b^2\) replaced by \(B\).
The following expressions are polynomials, by the original Cramer
cancellations:
\[
 D=\mathcal E(bK_aJ_aM_r),\quad
 N=\mathcal E(K_aJ_aM_i),\quad
 T_n=8(3-B)Bx(Bx^2+4\theta)(Bx-\theta+3).
 \tag{116.8}
\]
Here \(\theta\) is left unchanged by \(\mathcal E\). All three have
\(\theta\)-degree at most four. On the original chart,
\(K(G_a)=N/D\) and \(t(G_a)=T_n/D\). Since \(bK_aJ_a\ne0\),
the condition \(D=0\) is exactly the zero chart already treated.

Define
\[
 U_0=\mathcal E(U/b^3),\quad V_0=\mathcal E(V/b^3),\quad
 Q=\mathcal E(Q_5/b^3)\in\mathbb Z[B,x],
\]
using exactly the determinant definitions (90.8) and quintic (90.4).
The apparent powers of \(b\) divide after the indicated substitution.
For \(P=N,D,T_n\), put
\[
 P_h=V_0^4P(B,x,U_0/V_0).
 \tag{116.9}
\]
These are homogeneous polynomial evaluations; no inverse of \(V_0\)
is taken in defining them.

Define the integral polynomials
\(A_5(B,K)=\sum_{j=0}^5 a_j(B)K^j\) and
\(T_5(B,K)=\sum_{j=0}^4 t_j(B)K^j\) by the following coefficients.
The lists are in descending \(K\)-order; all displayed expressions are
polynomials in \(B\).

```text
a5 = B*(8676*B^11 + 323800*B^10 - 887699*B^9 - 5915187*B^8 + 13176396*B^7 + 29363364*B^6 - 33350778*B^5 - 69007626*B^4 - 2210328*B^3 - 13043268*B^2 - 282123*B - 177147)
a4 = 3*B*(2610*B^11 + 98339*B^10 - 413189*B^9 - 1183490*B^8 + 6015720*B^7 + 2674674*B^6 - 28927854*B^5 + 7116984*B^4 + 43563582*B^3 + 4067091*B^2 + 1506843*B - 196830)
a3 = 3*(720*B^12 + 32069*B^11 - 43013*B^10 - 860971*B^9 + 1283359*B^8 + 8595786*B^7 - 21221658*B^6 + 4667058*B^5 + 8065494*B^4 + 5718033*B^3 - 3552417*B^2 + 2053593*B + 177147)
a2 = 2*(3447*B^11 + 71072*B^10 - 712118*B^9 + 1536525*B^8 + 4523058*B^7 - 18749556*B^6 - 7637976*B^5 + 50503662*B^4 + 45296415*B^3 - 18187092*B^2 - 8358714*B - 1594323)
a1 = (B - 3)*(432*B^10 + 29559*B^9 - 138518*B^8 - 608172*B^7 + 1105344*B^6 + 14872410*B^5 - 22588956*B^4 - 19783116*B^3 - 13973472*B^2 - 4573017*B - 2716254)
a0 = (B - 3)*(720*B^9 + 39683*B^8 - 289700*B^7 + 216672*B^6 + 273420*B^5 + 4483566*B^4 - 4788396*B^3 - 441288*B^2 + 3467124*B + 1830519)

t4 = -6*B*(B - 3)*(2610*B^11 + 83963*B^10 - 384033*B^9 - 1777698*B^8 + 6962964*B^7 + 8952246*B^6 - 26754570*B^5 - 19004868*B^4 + 17236962*B^3 - 6089337*B^2 + 229635*B - 118098)
t3 = -6*B*(B - 3)*(1440*B^11 + 48793*B^10 - 170566*B^9 - 1220795*B^8 + 4702664*B^7 + 7946706*B^6 - 45791316*B^5 + 24873426*B^4 + 55049544*B^3 + 2369493*B^2 - 190998*B + 59049)
t2 = -12*B*(B - 3)*(927*B^10 + 22937*B^9 - 407286*B^8 + 1151072*B^7 + 4388766*B^6 - 17176086*B^5 - 1301292*B^4 + 21454632*B^3 + 19477179*B^2 - 4201227*B - 144342)
t1 = -2*(B - 3)*(1728*B^11 + 56217*B^10 - 645986*B^9 - 259527*B^8 + 8571960*B^7 + 17163522*B^6 - 129667068*B^5 + 120842442*B^4 + 100187928*B^3 + 2902149*B^2 - 9146034*B + 1240029)
t0 = -2*(B - 3)*(3168*B^10 + 111223*B^9 - 980977*B^8 + 1417368*B^7 + 3135888*B^6 - 2266866*B^5 - 24552234*B^4 + 47915712*B^3 + 43349256*B^2 + 4918563*B - 1240029)
```

For a designated \(K\)-degree \(m\), let
\(P^{[m]}(N_h,D_h)=D_h^mP(B,N_h/D_h)\). Define
\[
 F_A=A_5^{[5]}(N_h,D_h),\qquad
 F_T=D_hT_5^{[4]}(N_h,D_h)-T_{n,h}(\partial_KA_5)^{[4]}(N_h,D_h).
 \tag{116.10}
\]
The exact integral identities are
\[
 F_A=Q R_A,\qquad F_T=Q R_T,
 \quad R_A,R_T\in\mathbb Z[B,x].
 \tag{116.11}
\]
Here is a finite integer specification of the divisions, including a
coefficient bound that distinguishes them from interpolation. For a
polynomial \(P\), write \(\|P\|_1\) for the sum of absolute values
of its coefficients. Put \(w=2^{1032}\), and evaluate
\((B,x)=(w^{281},w)\). The two integer divisions by
\(Q(w^{281},w)\) have zero remainder. Expand the signed integer
quotients in balanced base \(w\), with digits in
\([-w/2,w/2)\), and replace digit position \(281j+k\),
\(0\le k<281\), by the monomial \(B^jx^k\). This defines
\(R_A,R_T\) with the following finite data:

```text
                 raw degree bounds (B,x)   quotient degrees (B,x)   terms
F_A                       (367,280)                 (357,270)       67011
F_T                       (368,280)                 (358,270)       67177

||F_A||_1 < 2^963;   ||R_A||_1 < 2^914;
||F_T||_1 < 2^966;   ||R_T||_1 < 2^919;
||Q||_1 = 27949666;  deg_x Q = 5.
```

Every integer and bound here is fixed by (90.1), (90.3), (90.8), and
(116.8)–(116.10). The raw bounds can also be obtained without expanding
the products, by the triangle inequality and
\(\|PQ\|_1\le\|P\|_1\|Q\|_1\). The decoded quotients can be
re-encoded to the two integer quotients. In each case the difference
\(F-QR\) has \(x\)-degree below 281 and coefficient norm below
\(2^{967}<w/2\). Therefore its monomials do not collide under
\(B\mapsto w^{281},x\mapsto w\). If the resulting integer polynomial
in \(w\) had a highest nonzero coefficient, that integer coefficient's
leading power would dominate the sum of all lower powers, whose
coefficients have magnitude below \(w/2\). Its zero evaluation is
impossible. Thus both differences vanish identically, proving (116.11)
in characteristic zero.

On the physical shape chart \(Q=0\), \(V_0D\ne0\), division only
by the indicated mean and shape denominators gives
\[
 A_5(B,K(G_a))=0,\qquad
 (\partial_KA_5)(B,K(G_a))\,t(G_a)=T_5(B,K(G_a)).
 \tag{116.12}
\]
There is no division by \(\partial_KA_5\) or by the leading
coefficient of \(A_5\). Both their zero specializations are retained.
In particular the second equation is valid through projected collisions.

### 116.4. Exact elimination and a degree-preserving coprimality certificate

Use the literal \(F_0,N_s,D_s\) of (100.1), and put
\[
 C_5=N_s\partial_KA_5-T_5D_s.
 \tag{116.13}
\]
Their degrees \((\deg_K,\deg_B)\) are
\((10,18)\), \((5,12)\), \((13,31)\) for
\(F_0,A_5,C_5\), respectively. The ordered resultant has the exact
factorization
\[
 \operatorname{Res}_K(F_0,A_5)
 =1024B^5(B-3)^2(B+1)^4(B+3)^{19}W(B)R_{160}(B).
 \tag{116.14}
\]
The polynomial \(W\) is exactly (106.8). Equation (116.14) specifies
\(R_{160}\) by exact division in \(\mathbb Z[B]\); it is primitive
of degree 160. The left side has degree 200. No irreducibility of
\(R_{160}\) is asserted or needed. Both the factorization and quotient
are reconstructed from the fixed-degree Sylvester determinant with
\(K\)-degrees 10 and 5.

Put
\[
 R_2=\operatorname{Res}_K(C_5,A_5)\in\mathbb Z[B],
 \tag{116.15}
\]
using \(K\)-degrees 13 and 5, in that order. Its Sylvester rows are
\(K^4C_5,\ldots,C_5,K^{12}A_5,\ldots,A_5\) in descending
columns \(K^{17},\ldots,1\). Modulo 137 these two degrees are
unchanged, so the same Sylvester determinant reduces to
\(\overline{R_2}\). It has \(B\)-degree 298. The reduction
\(\overline{R_{160}}\) has degree 160 and leading coefficient 136.
The following coefficient lists define two polynomials \(U_{137}\),
\(V_{137}\) in \(\mathbb F_{137}[B]\). Lists run from constant
coefficient upward, with line breaks carrying no additional meaning.

```text
U137 = [
  68,20,133,27,107,22,3,17,57,43,10,101,84,59,107,21,78,60,
  130,111,102,57,118,93,25,74,108,27,111,28,136,52,28,89,104,23,
  33,48,80,65,132,8,122,131,8,4,64,26,36,131,49,120,78,43,
  52,118,87,71,94,4,85,74,37,38,80,54,120,38,40,64,40,64,
  0,88,66,43,73,127,16,106,59,102,70,33,95,83,11,38,96,90,
  88,2,26,22,102,120,78,129,4,15,37,60,96,45,72,92,103,7,
  7,83,57,79,11,132,24,5,1,78,22,53,83,39,70,20,84,109,
  100,100,13,1,68,52,33,133,37,69,78,100,51,59,126,76,113,96,
  77,8,28,123,127,64,133,105,90,134,105,44,49,9,34,55,27,12,
  101,69,23,116,89,12,81,92,84,2,35,7,135,88,98,32,15,36,
  84,16,66,125,59,80,88,103,31,16,68,63,41,69,2,114,123,99,
  63,83,114,26,71,132,86,66,87,55,54,105,87,101,6,57,68,93,
  10,2,19,58,98,66,14,105,6,69,122,49,110,51,5,72,105,105,
  126,70,16,115,113,135,20,7,16,126,75,115,29,93,114,120,111,48,
  99,128,132,86,2,73,87,39,110,31,9,56,41,111,133,25,36,51,
  92,121,7,136,29,131,110,69,133,79,65,132,1,36,118,46,9,104,
  98,104,47,59,14,10,131,27,91,32
]
V137 = [
  135,4,13,46,18,56,65,42,100,67,95,128,5,76,60,99,5,81,
  57,5,31,2,73,118,45,37,88,120,57,86,125,46,5,69,16,125,
  126,63,76,75,68,83,127,79,112,23,114,6,5,30,55,19,87,69,
  46,80,95,40,68,42,95,36,19,112,106,10,52,87,78,66,112,24,
  107,83,115,47,4,70,24,122,40,70,135,63,44,133,35,52,75,111,
  8,45,69,104,59,60,77,37,47,60,22,25,92,37,45,112,40,53,
  28,64,58,39,41,29,7,16,20,4,4,22,28,23,6,20,11,120,
  58,133,34,42,125,40,126,24,77,51,59,93,19,62,45,34,128,63,
  105,48,69,41,79,61,37,88,15,8,16,79,107,25,56,118
]
```

They have degrees 297 and 159, and direct polynomial multiplication gives
\[
 U_{137}\overline{R_{160}}+V_{137}\overline{R_2}=1.
 \tag{116.16}
\]
All coefficients in this identity are determined by (100.1), the printed
\(A_5,T_5\), and (116.13)–(116.15); no modular fit or inferred
characteristic-zero degree is used.

It follows that \(R_{160}\) and \(R_2\) are coprime over
\(\mathbb Q[B]\). Indeed, a nonconstant common factor could be chosen
primitive and integral by Gauss's lemma. Its leading coefficient would
divide that of \(R_{160}\), hence would be a 137-adic unit. Its
reduction would retain positive degree and divide both reductions,
contradicting (116.16). This argument does not require knowing
\(\deg_B R_2\) in characteristic zero or preserving its leading
coefficient. It uses the proved degree preservation of \(R_{160}\)
and the exact reduction of the declared Sylvester determinant.

### 116.5. Physical consumer and precise consequence

Suppose the generic and aligned invariants (116.2) agreed, with
\(\operatorname{Re}G_a\ne0\). Equations (116.4), (116.12) imply
\[
 F_0(B,K)=A_5(B,K)=C_5(B,K)=0.
 \tag{116.17}
\]
A common finite \(K\)-root forces both resultants (116.14)–(116.15)
to vanish, even at a specialized leading-coefficient drop. For
\(0<B<1\), the factors \(B,B-3,B+1,B+3\) are nonzero. Coprimality
then forces \(W(B)=0\). This belongs to the already closed
\(Z_{26}\), contrary to the hypothesis. The added
\(\operatorname{Re}G_a=0\) chart was handled in §116.2. Equality of
\(G\) with either radial mean is therefore impossible.

Finally
\[
 M=(z+2)\left(1+\frac{G_a\bar G}{R}\right).
 \tag{116.18}
\]
Since \(z+2\ne0\), its vanishing is exactly
\(G=-R/\bar G_a\), proving (116.3). This proof of \(M\ne0\)
makes no division by a mixed-overlap coefficient. Thus, in any
rank-one mixed chart with the nonzero scale
\(\mu=(H/R)(r-1)/\bar\beta\),
\(\beta=R+(3+ib)\bar G\), and \(J=M/\mu\),
the entire \(J=0\) source branch is excluded. Zeros of \(\mu\) do
not evade (116.3); they simply do not belong to that normalized chart.

The argument selects a genuine physical source subcase, beyond the
multiplicity-only limitation of §115. It leaves other mixed-source
subcases and the two residual overlap-zero problems open. The explicit
finite union of closed fibres remains the 26 signed points of §111;
no additional point closure or global dimension-six conclusion is drawn.


## 117. The second intrinsic mean and exclusion of singular rank-one compatibility

### 117.1. Original overlap coefficients and statement

Retain the family, source classes and strict physical hypotheses of
§116. In particular \(B=b^2\), \(R=3-B>0\), and the generic mean
has the complete regular presentation (116.4) outside \(Z_{24}\).
Use the original generic reconstruction (87.2), writing its complex
coordinate as \(U_g\) to distinguish it from the aligned shape numerator:
\[
 \alpha=3-ib-\bar G,\quad \beta=R+(3+ib)\bar G,\quad
 C=\frac{U_g-R\alpha/2}{\beta},\quad
 D=\frac{-\bar U_g-R\bar\alpha/2}{\beta}.
 \tag{117.1}
\]
Here \(D,\beta,\bar\beta\) are retained units by §§103,105.2.
For a chosen generic normalized channel root \(Z\), the mixed overlap
with the aligned ray, after removal of its nonzero normalization, is
\[
 f_o(Z)=a_o\bar Z+b_oZ+c_o,
\]
\[
 \begin{split}
 a_o&=(z-1)+\frac HR(r-1)\bar C,\\
 b_o&=\frac HR(r-1)\bar D,\\
 c_o&=3+\frac HR\bigl((r+2)\bar G-(r-1)(\bar C+\bar D)\bigr).
 \end{split}
 \tag{117.2}
\]
These are the literal channel sums in (90.14): the selected upper and
scaled lower coordinates are \(\sqrt q Z\) and
\(\sqrt q(G+C(Z-1)+D(\bar Z-1))\). The exceptional aligned
position can be any of the three positions; selecting that coordinate
and retaining all generic root orders gives the same formula.
In particular \(a_o+b_o+c_o=M\), with \(M\) as in (116.3).

Define the mixed-overlap quantities
\[
 \Delta_o=|b_o|^2-|a_o|^2,\qquad
 N_o=a_o\bar c_o-\bar b_o c_o.
 \tag{117.3}
\]
They are not the generic channel-collision determinant or the strict
cubic discriminant. No condition on either of those is replaced here.
On the chart
\[
 \mu=\frac{H(r-1)}{R\bar\beta}\ne0,
 \quad \Sigma=\frac{z-1}{\mu}-R\bar\alpha,
 \quad J=\frac M\mu,\quad h=J+\bar J,
 \tag{117.4}
\]
the following assertions hold.

**Proposition 117.1 (repo-derived).** For real \(0<|b|<1\) outside
\(Z_{24}\), no original strict generic ray and noncanonical aligned ray
in this chart satisfy \(\Sigma=0\). Consequently, outside \(Z_{26}\),
every actual generic–aligned orthogonal pair with \(\Delta_o=0\) has
\(a_ob_o\mu h\ne0\). In particular both singular compatible branches
\(h=0,J=0\) and \(h=0,\Sigma=0\) are absent.

The first assertion is a source intersection exclusion and does not
require an overlap zero. The second uses §116. The remaining
\(h\ne0\) rank-one compatibility branch is not excluded by this
proposition. It adds no parameter fibre to the explicit finite union
of 26 signed closed points in §111.

### 117.2. Complete finite mean chart for \(\Sigma=0\)

Put \(k=z-1\), \(l=H(r-1)\). On (117.4), \(l\ne0\), and
\(\Sigma=0\) is exactly
\[
 k\bigl(R+(3-ib)G\bigr)=l(3+ib-G).
\]
Thus define
\[
 D_\Sigma=(3-ib)k+l,\quad N_\Sigma=(3+ib)l-Rk,
 \qquad D_\Sigma G=N_\Sigma.
 \tag{117.5}
\]
The linear map \((k,l)\mapsto(D_\Sigma,N_\Sigma)\) has determinant
\(9+B+R=12\). If \(D_\Sigma=0\), (117.5) also gives
\(N_\Sigma=0\), forcing \(k=l=0\), a contradiction. Hence the
complete solution on this chart is the finite mean
\[
 G_\Sigma=N_\Sigma/D_\Sigma,
 \qquad \bar\beta=12l/D_\Sigma,\qquad
 \mu=D_\Sigma/(12R).
 \tag{117.6}
\]
No denominator-zero solution of (117.5) has been discarded.

Use the original aligned coordinates \(u=(s+d)/2\), \(v=(s-d)/2\),
\(s^2=K_a=d^2+4\theta>0\), \(H=s(a+ic)\). Set
\[
 D_c=(3-ib)(u-i\theta)+H(v-i\theta),\quad
 N_c=(3+ib)H(v-i\theta)-R(u-i\theta).
\]
The pairs \((D_\Sigma,N_\Sigma)\) and \((D_c,N_c)\) differ by
the same nonzero factor \(2i/((1-iu)(1-iv))\); therefore \(D_c\ne0\).
Define
\[
 \begin{split}
 q_r={}&3\bigl[2\theta((\theta+1+bd)a+(d-b(\theta+1))c)-Rd\bigr],\\
 q_i={}&2\theta\bigl[(3b(\theta+1)+(B-6)d)a
 +(3bd-(B-6)(\theta+1))c\bigr]-bRd,\\
 q_t={}&-2R\bigl[2\theta((3(\theta+1)+bd)a
 +(3d-b(\theta+1))c)+(B+3)d\bigr].
 \end{split}
 \tag{117.7}
\]
Direct expansion using both \(s^2=K_a\) and \(K_a(a^2+c^2)=R\)
gives
\[
 \operatorname{Re}(N_c\bar D_c)=sq_r,\quad
 \operatorname{Im}(N_c\bar D_c)=sq_i,\quad
 |N_c|^2-R|D_c|^2=sq_t.
 \tag{117.8}
\]
For completeness, after reduction by \(s^2-K_a\), the three left sides
minus their asserted right sides are respectively \(K_a(a^2+c^2)-R\)
times
\[
 -\tfrac32(-2\theta^2-2\theta-d^2+ds),\quad
 -\tfrac b2(-2\theta^2-2\theta-d^2+ds),\quad
 -(B+3)(-2\theta^2-2\theta-d^2+ds).
\]
Thus both signs of \(s\), including the terms odd in \(s\), are retained.
When \(q_r\ne0\), the invariants (116.2) become
\[
 K(G_\Sigma)=q_i/(bq_r),\qquad t(G_\Sigma)=q_t/q_r.
 \tag{117.9}
\]
When \(q_r=0\), (117.8) instead gives
\(\operatorname{Re}G_\Sigma=0\), including the possible zero mean.
It cannot equal the regular generic mean with real part \(X\ne0\).
This treats the entire added zero chart before any division by \(q_r\).
No division by \(d\) is used.

The remaining source units \(b,K_a,J_a,F_a,V\) and original Cayley
coverage are exactly those discussed in §116.1. The actual Cayley poles
already belong to the closed coordinate exceptions in \(Z_{24}\).
The subcase \(r=1\) is outside (117.4); its role in the physical
rank-one conclusion is treated explicitly in §117.5.

### 117.3. Integral intrinsic mean and trace identities

With the Cramer values \(a=A_a,c=C_a\), define the integral polynomials
\[
 \mathscr D=\mathcal E(bK_aJ_aq_r),\quad
 \mathscr N=\mathcal E(K_aJ_aq_i),\quad
 \mathscr T=\mathcal E(bK_aJ_aq_t),
 \tag{117.10}
\]
using exactly the even substitution of §116.3. Their degrees in
\((B,x,\theta)\) are at most \((4,4,4),(4,4,4),(5,4,4)\),
respectively; they have 24, 24 and 31 terms. On \(q_r\ne0\),
\(K(G_\Sigma)=\mathscr N/\mathscr D\) and
\(t(G_\Sigma)=\mathscr T/\mathscr D\). The multiplier
\(bK_aJ_a\ne0\), so no further zero chart is introduced.

Keep \(Q,U_0,V_0\) exactly as in §116.3 and set
\(P_h=V_0^4P(B,x,U_0/V_0)\) for
\(P=\mathscr N,\mathscr D,\mathscr T\), as homogeneous polynomial
evaluations. Define \(A_\Sigma=\sum_{j=0}^5 a_jK^j\) and
\(T_\Sigma=\sum_{j=0}^4 t_jK^j\) by the following coefficients,
again in descending \(K\)-order.

```text
a5 = B*(981*B^8 - 9988*B^7 + 33252*B^6 - 35100*B^5 + 18414*B^4 + 46980*B^3 - 90396*B^2 - 2916*B - 2187)
a4 = -B*(B - 3)*(879*B^7 - 14147*B^6 + 55671*B^5 - 52659*B^4 + 27621*B^3 + 54351*B^2 - 17739*B - 729)
a3 = 210*B^9 - 7555*B^8 + 77064*B^7 - 307344*B^6 + 545940*B^5 - 359478*B^4 - 73224*B^3 + 169128*B^2 + 30618*B + 6561
a2 = -(B - 3)*(40*B^8 - 1249*B^7 + 17177*B^6 - 80553*B^5 + 167913*B^4 - 119259*B^3 - 38637*B^2 + 17253*B - 3645)
a1 = -2*(B - 3)*(75*B^7 - 1201*B^6 + 6771*B^5 - 23769*B^4 + 45873*B^3 - 36531*B^2 - 5103*B + 3645)
a0 = -4*(B - 3)^2*(2*B^6 + 53*B^5 - 115*B^4 + 390*B^3 - 900*B^2 + 2349*B - 243)

t4 = 2*B*(B - 3)*(B + 3)*(879*B^8 - 9704*B^7 + 46936*B^6 - 102312*B^5 + 74574*B^4 - 49464*B^3 + 69984*B^2 + 5832*B + 2187)
t3 = -8*B*(B - 3)*(B + 3)*(105*B^8 - 2138*B^7 + 15946*B^6 - 58902*B^5 + 95592*B^4 - 38934*B^3 + 17982*B^2 - 17658*B - 729)
t2 = 6*(B - 3)^2*(B + 3)*(40*B^8 - 759*B^7 + 6041*B^6 - 23855*B^5 + 49705*B^4 - 7773*B^3 + 7587*B^2 + 1539*B + 243)
t1 = 16*B*(B - 3)*(B + 3)*(45*B^7 - 664*B^6 + 3287*B^5 - 10350*B^4 + 24651*B^3 - 34236*B^2 + 13041*B - 2430)
t0 = 4*(B - 3)^2*(B + 3)*(20*B^7 + 211*B^6 - 1076*B^5 + 1511*B^4 + 132*B^3 + 10593*B^2 - 11556*B + 1701)
```

For designated \(K\)-degree \(m\), the notation
\(P^{[m]}(\mathscr N_h,\mathscr D_h)\) means
\(\mathscr D_h^mP(B,\mathscr N_h/\mathscr D_h)\). Put
\[
 F_A=A_\Sigma^{[5]}(\mathscr N_h,\mathscr D_h),
\]
\[
 F_T=\mathscr D_hT_\Sigma^{[4]}(\mathscr N_h,\mathscr D_h)
 -(B+1)\mathscr T_h(\partial_KA_\Sigma)^{[4]}
       (\mathscr N_h,\mathscr D_h).
 \tag{117.11}
\]
The exact integral identities are
\[
 F_A=Q R_A,\qquad F_T=Q R_T,\qquad R_A,R_T\in\mathbb Z[B,x].
 \tag{117.12}
\]
Here is a finite specification and coefficient certificate in the same
form as (116.11). Set \(w=2^{1020}\) and evaluate at
\((B,x)=(w^{281},w)\). Both integer divisions by \(Q(w^{281},w)\)
have zero remainder. Decode the two signed integer quotients in
balanced base \(w\), replacing digit position \(281j+k\),
\(0\le k<281\), by \(B^jx^k\). They give the respective \(R_A,R_T\)
with the following data:

```text
                 raw degree bounds (B,x)   quotient degrees (B,x)   terms
F_A                       (369,280)                 (359,270)       66337
F_T                       (371,280)                 (361,270)       66875

||F_A||_1 < 2^949;   ||R_A||_1 < 2^900;
||F_T||_1 < 2^954;   ||R_T||_1 < 2^904;
||Q||_1 = 27949666;  deg_x Q = 5.
```

All inputs are specified by the original determinants (90.8), (117.7),
(117.10) and the printed coefficients. The raw coefficient bounds
follow by the triangle inequality and multiplicativity bound for
\(\|\cdot\|_1\). The decoded coefficients re-encode to the integer
quotients. Both differences \(F-QR\) have \(x\)-degree below 281
and coefficient norm below \(2^{955}<w/2\). The no-collision and
leading-digit domination argument of §116.3 therefore proves the
identities (117.12) in characteristic zero. It requires no interpolation
or specialization assumption.

On \(Q=0\), with the retained \(V_0\mathscr D\ne0\), these yield
\[
 A_\Sigma(B,K(G_\Sigma))=0,\qquad
 (B+1)(\partial_KA_\Sigma)(B,K(G_\Sigma))\,t(G_\Sigma)
   =T_\Sigma(B,K(G_\Sigma)).
 \tag{117.13}
\]
The factor \(B+1\) is part of the trace identity and is retained.
There is no division by the quintic derivative or its leading
coefficient, so both their zero specializations remain covered.

### 117.4. Exact generic intersection exclusion

With the literal generic \(F_0,N_s,D_s=\partial_KF_0\) of (100.1), put
\[
 C_\Sigma=(B+1)N_s\partial_KA_\Sigma-T_\Sigma D_s.
 \tag{117.14}
\]
The degrees \((\deg_K,\deg_B)\) of \(F_0,A_\Sigma,C_\Sigma\)
are \((10,18),(5,9),(13,29)\). The ordered Sylvester determinant
has the exact factorization
\[
 \operatorname{Res}_K(F_0,A_\Sigma)
 =2048B^5(B-3)^2(B+1)^2(B-1)^5(B+3)^{25}R_{135}(B).
 \tag{117.15}
\]
This specifies \(R_{135}\) by exact division in \(\mathbb Z[B]\).
It is primitive of degree 135; the full determinant has degree 174.
No irreducibility of this quotient is assumed.

Define in the explicit order
\[
 R_{\Sigma,2}=\operatorname{Res}_K(C_\Sigma,A_\Sigma).
 \tag{117.16}
\]
Its \(18\times18\) Sylvester rows are
\(K^4C_\Sigma,\ldots,C_\Sigma,K^{12}A_\Sigma,\ldots,A_\Sigma\)
in descending columns \(K^{17},\ldots,1\). Modulo 137 the input
\(K\)-degrees 13 and 5 survive, and the determinant reduces exactly
to \(\overline{R_{\Sigma,2}}\), of \(B\)-degree 255.
The reduction \(\overline{R_{135}}\) has degree 135 and leading
coefficient 4. The following lists, from constant coefficient upward,
define \(U_\Sigma,V_\Sigma\in\mathbb F_{137}[B]\).

```text
USigma = [
  7,129,128,62,110,125,69,28,57,99,29,25,55,35,46,84,58,5,
  115,40,50,81,29,34,58,111,103,1,96,28,134,110,135,4,84,124,
  26,123,119,109,113,97,100,106,15,103,11,55,115,86,94,76,124,21,
  126,115,132,92,67,80,126,29,126,95,10,136,38,78,130,134,128,120,
  69,107,37,98,72,7,131,24,135,58,16,39,60,80,12,54,42,62,
  17,55,58,118,29,105,105,67,119,129,34,35,13,54,66,101,111,13,
  114,104,4,50,79,123,64,62,90,67,77,59,32,62,40,103,30,48,
  59,128,106,9,115,0,6,86,91,12,106,18,129,81,43,106,115,22,
  90,95,67,109,5,65,107,105,45,23,101,76,95,49,17,80,22,73,
  128,17,19,40,54,115,122,57,15,104,23,2,85,113,21,97,6,37,
  116,99,117,125,119,121,52,47,98,116,58,54,59,90,11,97,8,16,
  21,59,102,107,116,52,31,112,30,31,80,69,136,101,51,102,107,117,
  124,85,36,26,55,13,94,4,14,81,79,49,22,60,91,34,121,42,
  9,90,12,117,108,86,129,114,128,69,136,47,126,83,101,14,4,28,
  83,27,118
]
VSigma = [
  47,59,34,58,94,133,31,52,105,51,5,26,84,84,21,11,31,40,
  31,56,49,4,85,59,135,103,81,46,4,83,45,82,108,33,20,113,
  79,23,47,64,57,103,86,125,130,128,9,19,19,38,0,77,105,91,
  24,96,128,31,77,136,66,46,98,107,98,110,78,75,76,17,93,56,
  25,80,17,16,118,0,59,33,42,5,17,104,5,34,49,109,15,38,
  132,8,61,40,106,2,85,127,111,94,77,5,115,10,73,50,112,55,
  30,8,121,62,107,22,136,120,131,64,114,19,48,13,75,74,35,127,
  39,35,122,101,7,122,129,101,130
]
```

Their degrees are 254 and 134. Direct polynomial multiplication gives
\[
 U_\Sigma\overline{R_{135}}+
 V_\Sigma\overline{R_{\Sigma,2}}=1.
 \tag{117.17}
\]
All terms are fixed by (100.1), the printed \(A_\Sigma,T_\Sigma\)
and the declared Sylvester determinants. In particular this is not
a fit to modular samples.

The same degree-preserving Gauss argument as in §116.4 proves
\(\gcd_{\mathbb Q[B]}(R_{135},R_{\Sigma,2})=1\).
Any primitive integral common factor would have leading coefficient
prime to 137, since it divides the leading coefficient of \(R_{135}\).
It would retain positive degree on reduction and contradict (117.17).
No characteristic-zero degree assertion for \(R_{\Sigma,2}\) is needed.

Suppose now that \(\Sigma=0\) for an actual source pair outside
\(Z_{24}\). The zero-real-part case has already been excluded in
§117.2. The remaining mean satisfies both (116.4) and (117.13), so
\[
 F_0(B,K)=A_\Sigma(B,K)=C_\Sigma(B,K)=0.
 \tag{117.18}
\]
A common finite \(K\)-root makes both declared Sylvester determinants
vanish, including specializations where a leading coefficient drops.
Every scalar factor in (117.15) is nonzero for \(0<B<1\); thus
\(R_{135}(B)=R_{\Sigma,2}(B)=0\), contradicting coprimality.
This proves the first assertion of Proposition 117.1 with all its
source denominator cases retained.

### 117.5. Original compatibility and complete singular-branch consumer

The identity
\[
 a_o\overline{f_o(Z)}-\bar b_o f_o(Z)=-\Delta_o Z+N_o
 \tag{117.19}
\]
shows that any physical overlap zero with \(\Delta_o=0\) must satisfy
\(N_o=0\). If \(a_o=b_o=0\), an overlap zero also forces \(c_o=0\),
and then \(M=0\), contrary to §116 outside \(Z_{26}\).
Otherwise \(\Delta_o=0\) forces both \(a_o,b_o\) nonzero.
The expression for \(b_o\), with \(H,D\) nonzero, implies
\(r-1\ne0\); the retained \(\bar\beta\ne0\) then makes \(\mu\ne0\).
This explicitly handles the zero-scale and \(r=1\) cases before
entering the normalized chart.

On that chart put
\[
 \xi=\bar U_g+\frac{z-1}{\mu}-\frac R2\bar\alpha.
\]
Substitution of (117.1) into (117.2) gives, without a sign assumption,
\[
 \frac{a_o}{\mu}=\xi,\quad
 \frac{b_o}{\mu}=\bar\Sigma-\bar\xi,\quad
 \frac{c_o}{\mu}=J-\xi-\bar\Sigma+\bar\xi.
 \tag{117.20}
\]
Consequently
\[
 \frac{\Delta_o}{|\mu|^2}
   =|\Sigma|^2-\Sigma\bar\xi-\bar\Sigma\xi,\qquad
 \frac{N_o}{|\mu|^2}
   =\frac{\Delta_o}{|\mu|^2}+h\xi-\Sigma J.
 \tag{117.21}
\]
At \(h=0\), the necessary equations \(\Delta_o=N_o=0\)
therefore give \(\Sigma J=0\). Section 116 gives \(M\ne0\),
hence \(J\ne0\), outside \(Z_{26}\). The first part of this
proposition gives \(\Sigma\ne0\), already outside \(Z_{24}\).
Both factors being nonzero is a contradiction. This proves \(h\ne0\)
and completes the stated physical rank-one consequence.

There is also an exact reason not to replace this source intersection
argument by an assumed strict sign of \(h\). On the hypothetical
\(\Sigma=0\) aligned mean, substitution of (117.6), the unit phases
and \(|H|^2=R\) gives
\[
 h=\frac{144R\,P_0}
 {(1+u^2)(1+v^2)|D_\Sigma|^2},
 \tag{117.22}
\]
where \(P_0\) is the original aligned equation (90.1).
One direct verification is to set
\[
 E=R(z+2)\bar D_\Sigma+H(r+2)\bar N_\Sigma,
\]
\[
 S=\operatorname{Re}z+\operatorname{Re}r-2+
 b(\operatorname{Im}z-\operatorname{Im}r)
 +\operatorname{Re}\bigl(\bar H(\bar r-z)\bigr).
\]
The unit identities give \(E+\bar E=6RS\), the Cayley substitution
gives \(S=2P_0/((1+u^2)(1+v^2))\), and (117.6) gives
\(h=12(E+\bar E)/|D_\Sigma|^2\). Thus \(h=0\) follows from the
aligned source equation on this branch; it is the simultaneous
generic source conditions that exclude it.

The proof retains \(d=0\), the newly added \(q_r=0\) and
\(D_\Sigma=0\) cases, derivative and leading-coefficient zeros,
both radial signs and every source presentation supplied by §105.2.
It imposes no new assumption on the strict cubic discriminant.
It removes both singular compatibility branches while leaving the
regular \(h\ne0\) rank-one problem, the other mixed overlaps and the
ordinary cross-union overlap problem open. There is no new point
closure, whole-family closure or global dimension-six conclusion here.
