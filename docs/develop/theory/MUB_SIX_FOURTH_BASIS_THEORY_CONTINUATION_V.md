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
