# 六维第四个无偏基问题：理论续卷 IV

本卷承接[理论续卷 III](MUB_SIX_FOURTH_BASIS_THEORY_CONTINUATION_III.md)，沿用实际 paired-circulant 族与原始输入基约定。第 87–90 节给出所有 generic 射线的投影必要条件、有限代数分类、任意 generic 正交对刚性及 generic–aligned 混合边排除证书；第 91 节推出明确有限代数例外集之外的 canonical 基唯一性与固定 MUB 对的四基排除。全部 guard 零点仍作为未决参数纤维保留；本卷不将稠密补集的结论延伸到这些例外点。

## 87. Global line coordinates and projective necessity at every leading stratum

### 87.1. Original equations and normalization

Throughout §§87–91 use the actual paired-circulant family and input
convention of §§60,75,78, with \(0<|b|<1\). Put
\[
 R=3-b^2,\qquad B=3+b^2,\qquad
 \kappa=(b-i)\sqrt{R/(1+b^2)}.                         \tag{87.1}
\]
The generic chart selects a channel with three distinct unit entries and
dephases its mean to \(\sum_jx_j=3\sqrt q>0\). Write \(G=x+iy\),
\(Z=u+iv\), with all four coordinates real. The scaled lower entries
are \(y_j\); original inputs are \((x_j,y_j/\kappa)\). In particular
physical mean and interpolation coefficients are \(G/\kappa,C/\kappa,
D/\kappa\). Bars below fix all real coordinates and conjugate \(i\).

The necessary-and-sufficient selected-channel quotient of §§75,78.2 is
\[
\begin{aligned}
 \alpha&=3-ib-\bar G,&\beta&=R+(3+ib)\bar G,\\
 C&=(Z-R\alpha/2)/\beta,&D&=(-\bar Z-R\bar\alpha/2)/\beta,\\
 Y_c&=\bar GC+G\bar D-|C|^2-|D|^2+C\bar D,\\
 L&=R(b+i)+(-2b+iB)\bar G,&
 N&=(-2b-iB)-(b-i)\bar G,\\
 T&=3(L+NC+\bar N\bar D)-2iB(\bar G+2\bar D-\bar C),\\
 E&=\bar CT-2iBY_c,&
 J&=18(b+i)G+3L+3NG+2iB(G-C+2D),\\
 A_c&=|C|^2+|D|^2,\\
 N_Y&=(A_c-R)|T|^2+4B^2|D|^2[|G|^2-A_c+4\Re(C\bar D+Y_c)],\\
 N_D&=\Re(2iBC)|T|^2+4B^2|D|^2\Re(J+2T).
\end{aligned}                                                    \tag{87.2}
\]
The equations are \(E=N_Y=N_D=0\), on the strict domain
\[
 \beta CDY_c\ne0,\quad q=|CD|^2/|Y_c|^2,\quad
 e=-Y_c/(\bar CD),\quad 0<q<1,\quad
 \delta=q^2(3-8\Re e)+6q-1<0.                         \tag{87.3}
\]
All six root orders are retained. Explicitly, with \(t=\sqrt q\) and
\(\xi=t\bar e\), take the three distinct unit roots of
\[
 X^3-3tX^2+3t\xi X-\xi=0,
 \qquad y_j=Gt+C(x_j-t)+D(\bar x_j-t).                \tag{87.4}
\]
These are precisely the original rays in the selected chart. Section 75
retains the optional \(\Theta\) channel choice and all aligned finite
and pole charts. No restriction on candidate root order is introduced.

Here are polynomial definitions of every coefficient used below. Set
\[
\begin{aligned}
 d&=\beta\bar\beta,& C_n&=Z-R\alpha/2,&D_n&=-\bar Z-R\bar\alpha/2,\\
 Y_n&=\bar GC_n\bar\beta+G\bar D_n\beta
       -C_n\bar C_n-D_n\bar D_n+C_n\bar D_n,\\
 T_n&=3(Ld+NC_n\bar\beta+\bar N\bar D_n\beta)
        -2iB(\bar Gd+2\bar D_n\beta-\bar C_n\beta),\\
 E_n&=\bar C_nT_n-2iBY_n\bar\beta,\\
 \mathscr F&=\Re(E_n)/6,& I&=\Im(E_n),&
 \mathcal Y&=d^3N_Y,&\mathcal D&=d^3N_D/B.
\end{aligned}                                                    \tag{87.5}
\]
The last two expressions are polynomials; the division by \(B\) is
exact. One has \(E_n=\bar\beta dE\). Expansion gives an affine real
polynomial
\[
 \mathscr F=A u+D_0v+C_0,\qquad
 A=\partial_u\mathscr F,\quad D_0=\partial_v\mathscr F,\quad
 C_0=\mathscr F|_{u=v=0},\quad \sigma=A^2+D_0^2.       \tag{87.6}
\]
Thus (87.2) implies \(\mathscr F=I=\mathcal Y=\mathcal D=0\),
and the converse holds on (87.3).

### 87.2. Uniform regularity of the real affine equation

**Lemma 87.1.** On \(0<|b|<1\), the conditions
\(\mathscr F=0\) and \(\beta\ne0\) imply \(\sigma>0\).

Here is a finite exact ideal certificate, including every parameter fibre.
Work in \(\mathbb Q(b)[x,y]\) and start with rows
\(f_0=A,f_1=D_0,f_2=C_0\), reconstructed by (87.5)–(87.6).
Two traces below use lexicographic order and graded reverse lexicographic
order, in both cases \(x>y\). For clarity their operations are:

- \(M(j)\): divide \(f_j\) by its leading coefficient.
- \(S(j,a,c;k,d,e)\): form \(x^ay^cf_j-x^dy^ef_k\).
- \(R(j;j_1,\ldots,j_m)\): divide \(f_j\) by the ordered list of
  previous rows, and retain the remainder. At each step use the first
  listed leading monomial dividing the current leading monomial; subtract
  its exact coefficient multiple. If none divides, move that leading
  term to the remainder. Continue until zero. This fixes all quotients.

Each displayed row is the result of its operation. No claim that these
rows form a Gröbner basis is required. They are simply rational polynomial
identities expressing their outputs in the ideal of the three seeds.

Lexicographic trace:

```text
3: M(0)
4: M(1)
5: R(2;0,1)
6: M(5)
7: S(4,0,0;6,0,1)
8: R(7;6,4,3)
9: M(8)
10: S(9,1,0;6,0,2)
11: R(10;9,6,4,3)
12: M(11)
13: S(12,0,1;9,0,0)
14: R(13;12,6,3)
15: M(14)
16: S(15,0,1;12,0,0)
17: R(16;15)
18: M(17)
19: S(15,1,0;6,0,0)
20: R(19;18,15)
21: S(3,0,0;6,1,0)
22: R(21;18,15)
23: M(22)
24: S(23,0,1;18,0,0)
25: R(24;23,15)
26: M(25)
27: S(26,0,1;23,0,0)
28: R(27;26,15)
29: M(28)
30: S(29,0,1;26,0,0)
31: R(30;29,15)
32: M(31)
33: S(32,0,1;29,0,0)
34: R(33;32,15)
35: M(34)
36: S(35,0,1;32,0,0)
37: R(15;35)
```

Graded reverse lexicographic trace:

```text
3: M(0)
4: M(1)
5: R(2;0,1)
6: M(5)
7: S(4,0,0;6,0,1)
8: R(7;6,4,3)
9: M(8)
10: S(3,0,0;6,1,0)
11: R(10;6,9,4,3)
12: M(11)
13: S(12,1,0;9,0,1)
14: R(13;6,12,9,4,3)
15: M(14)
16: S(15,0,1;9,0,0)
17: R(16;15,6,12,3)
18: M(17)
19: S(18,0,1;12,0,0)
20: R(19;18,15,6,3)
21: M(20)
22: S(21,0,1;15,0,0)
23: R(22;21,18)
24: M(23)
25: S(24,0,1;18,0,0)
26: R(25;24,21)
27: S(21,1,0;6,0,0)
28: R(21;24)
```

The terminal rows are, respectively, \((f_{37},f_{35})\) and
\((f_{28},f_{24})\), and both pairs equal
\[
 \ell_x=x+\frac{9-3b^2}{b^2+9},\qquad
 \ell_y=y+\frac{-b^3+3b}{b^2+9}.                       \tag{87.7}
\]
To check all scalar specialization failures, collect the reduced
coefficient denominators of every row and division quotient, and the
numerators and denominators of every leading coefficient inverted in
an \(M\) operation. Let \(P_L,P_R\) be their squarefree least common
multiples, up to nonzero rational constants. Direct reconstruction gives
\[
 \gcd(P_L,P_R)=b(b-3)(b+3)(b^2-3)(b^2+3)(b^2+9)Q_b,
 \quad Q_b=b^8-33b^6+387b^4+729b^2+324.                \tag{87.8}
\]
For an explicit factor inventory, put \(z=b^2\) and let \(P_0\) denote
the product in (87.8). Then, up to nonzero constants,
\[
\begin{aligned}
 P_L/P_0={}&(2z+9)(3z^2+10z-9)
 (4z^3-81z^2-252z-135)\\
 &\cdot(2z^4-75z^3+2943z^2-16929z-61965)\\
 &\cdot(z^4-18z^3+1440z^2-486z-8505)\\
 &\cdot(473z^6+6552z^5+31653z^4+28296z^3
                 -170829z^2-279936z+98415),\\
 P_R/P_0={}&(z^4+9z^3-351z^2+1053z+2916)\\
 &\cdot(7z^7+36z^6+711z^5-23220z^4-14499z^3
                    +825228z^2+3636981z+2755620)\\
 &\cdot(343z^{11}-6174z^{10}-14778z^9+641871z^8+380700z^7
       -26240598z^6-50719446z^5+384290892z^4\\
 &\hspace{18mm}+1928284461z^3+3102906852z^2+127545840z-3228504075)\\
 &\cdot(49z^{12}-1638z^{11}+40851z^{10}-363528z^9-1169640z^8
       +22370580z^7+56458134z^6-821017296z^5\\
 &\hspace{18mm}-1374024303z^4+11763623682z^3+57002538807z^2
                    +106615567656z+58113073350).
\end{aligned}                                                    \tag{87.9}
\]
The gcd in (87.8) follows by exact univariate division of these factors.
All its factors are nonzero on the puncture, since in particular
\[
 Q_b=b^8+354b^4+729b^2+324+33b^4(1-b^2)>0.
\]
At least one complete trace therefore specializes at every target
parameter. If \(A=D_0=C_0=0\), its terminal equations (87.7) give
\(x=3(b^2-3)/(b^2+9)\), \(y=b(b^2-3)/(b^2+9)\).
Substitution gives \(\beta=0\), a contradiction. This proves the lemma.

### 87.3. The global line and fixed-power polynomial construction

Set \(\tau=-D_0u+Av\). Lemma 87.1 gives the exact global line bijection
\[
 u=\frac{-AC_0-D_0\tau}{\sigma},\qquad
 v=\frac{-D_0C_0+A\tau}{\sigma}.                      \tag{87.10}
\]
It includes \(A=0\), and loses no original strict point. Define
\[
 Q_g=\sigma^2 I(u(\tau),v(\tau)),\quad
 Y_g=\sigma^4\mathcal Y(u(\tau),v(\tau)),\quad
 D_g=\sigma^3\mathcal D(u(\tau),v(\tau)).             \tag{87.11}
\]
These are polynomials, of respective \(\tau\)-degrees at most 2,4,3.
They vanish at every original ray. Degree drops are retained throughout.

For reconstructing their small remainders without any stored coefficient
file, first perform the following formal old-line substitutions:
\[
 Q(v)=A^2I((-D_0v-C_0)/A,v),\quad
 Y(v)=A^4\mathcal Y((-D_0v-C_0)/A,v),\quad
 D_*(v)=A^3\mathcal D((-D_0v-C_0)/A,v).                \tag{87.12}
\]
They mean expanded polynomial numerators, not divisions at individual
points. Write \(Q=q_2v^2+q_1v+q_0\) and define the exact quotient
\(F_8=q_2/(-8B)\). For a degree-\(m\) polynomial \(p\), use the
fixed pseudo-remainder obtained by dividing \(q_2^{m-1}p\) by \(Q\).
The following exact divisions define affine polynomials and three mean
polynomials:
\[
\begin{aligned}
 L_Y=a_Yv+b_Y&=\frac{72\operatorname{prem}(Y,Q)}{RB^3d^2A^3F_8^2},\\
 L_D=a_Dv+b_D&=\frac{12\operatorname{prem}(D_*,Q)}{B^2d^2A^2F_8},\\
 F_{16}&=\frac{a_Yb_D-b_Ya_D}{dAF_8},\\
 C_Y&=\frac{q_0a_Y^2-q_1a_Yb_Y+q_2b_Y^2}{A^2d^2F_8},\\
 C_D&=\frac{q_0a_D^2-q_1a_Db_D+q_2b_D^2}{A^2d^2F_8}.
\end{aligned}                                                    \tag{87.13}
\]
All quotients in (87.13) are polynomial identities in
\(\mathbb Q[b,x,y,v]\); no zero stratum is discarded. The mean degrees
of \(F_8,F_{16},C_Y,C_D\) are 8,16,20,20. The pseudo-divisions require
exactly three and two steps, respectively, before any specialization.
Equations (87.2),(87.5),(87.12),(87.13) specify every coefficient by finite
exact arithmetic. They are also a direct reconstruction certificate for
the polynomial divisions asserted here.

Define further exact polynomial quotients
\[
\begin{aligned}
 \mu_Y&=(\sigma b_Y-D_0C_0a_Y)/A,&
 \mu_D&=(\sigma b_D-D_0C_0a_D)/A,\\
 q_{1g}&=(\sigma q_1-2D_0C_0q_2)/A,&
 q_{0g}&=(\sigma^2q_0-\sigma D_0C_0q_1+D_0^2C_0^2q_2)/A^2.
\end{aligned}                                                    \tag{87.14}
\]
Thus \(Q_g=q_2\tau^2+q_{1g}\tau+q_{0g}\). Put
\(L_{gY}=a_Y\tau+\mu_Y\), \(L_{gD}=a_D\tau+\mu_D\).
Affine substitution in (87.13) yields the polynomial identities
\[
\begin{aligned}
 \operatorname{prem}(Y_g,Q_g)&=RB^3d^2F_8^2\sigma^3L_{gY}/72,\\
 \operatorname{prem}(D_g,Q_g)&=B^2d^2F_8\sigma^2L_{gD}/12,\\
 a_Y\mu_D-\mu_Ya_D&=\sigma dF_8F_{16},\\
 q_{0g}a_j^2-q_{1g}a_j\mu_j+q_2\mu_j^2
                 &=\sigma^2d^2F_8C_j\quad(j=Y,D).
\end{aligned}                                                    \tag{87.15}
\]
The fixed pseudo-division powers here are \(q_2^3,q_2^2\). To verify the
extension through \(A=0\), first transform over the fraction field using
\(v=(A\tau-D_0C_0)/\sigma\). A degree-\(m\) remainder scales by
\(\sigma^m/A^m\), while \(a v+b=A(a\tau+\mu)/\sigma\).
The factors cancel exactly to (87.15). Both sides are polynomials by
(87.14), so these are identities also at \(A=0\). No density of physical
solution branches is assumed.

### 87.4. Projective constraints are necessary even when \(F_8=0\)

**Theorem 87.2.** Every original strict selected-channel ray satisfies
\(F_{16}=C_Y=C_D=0\), including every leading-coefficient and affine-pivot
stratum. In particular \(F_8=0\), \(q_{1g}=q_{0g}=0\), \(A=0\), and
\(a_Y=a_D=0\) require no exceptions in this necessity statement.

The cancellation uses the following exact coprimality certificate:
\[
 \gcd(F_8,q_{1g})=1\quad\hbox{in }\mathbb Q[b,x,y].    \tag{87.16}
\]
Indeed the \(x\)-degrees are 8 and 12, and direct reconstruction gives
\[
\begin{aligned}
 [x^8]F_8&=-3b^2(b^2+9)^2,\\
 [x^0y^0]F_8&=3b^2(b^2-3)^6,\\
 [x^6y^0]F_8&=-6(b^2-3)(b^6+26b^4+99b^2-54).
\end{aligned}                                                    \tag{87.17}
\]
Any \(x\)-content factor over \(\mathbb Q[b,y]\) divides the first
polynomial, hence depends only on \(b\). The second restricts it to a
factor of \(b^2\); the third has value \(-972\) at \(b=0\), so the
content is one. At \(b=2,y=0\), the ascending \(x\)-coefficient arrays
modulo 101 are

```text
F8:  12,34,9,45,53,62,17,27,93
q1g: 71,69,15,49,3,6,12,89,70,75,72,7,81
```

Both degrees are preserved. Their conventional Sylvester determinant is
\(53\pmod{101}\), certifying a nonzero characteristic-zero resultant.
They are coprime over \(\mathbb Q(b,y)[x]\). The content calculation
and Gauss's lemma prove (87.16). This modular calculation witnesses a
nonzero integer polynomial, rather than counting real roots.

Work in the UFD \(S=\mathbb Q[b,x,y,B^{-1}]\). Since
\(q_2=-8BF_8\), (87.16) implies \(\gcd(Q_g,q_2)=1\) in \(S[\tau]\):
a common divisor has \(\tau\)-degree zero and divides both \(F_8\)
and \(q_{1g}\). Only UFD divisibility is used; a Bézout unit-ideal
assertion in this multivariate ring is unnecessary.
Put
\[
 k_Y=RBd^2\sigma^3/4608,\quad k_D=-Bd^2\sigma^2/96,
 \quad c=-\sigma^2d^2/(8B),\quad c_0=-\sigma d/(8B).    \tag{87.18}
\]
These coefficients are nonzero at every original strict point.
Fixed-power pseudo-division in (87.15) gives polynomial quotients
\(\Pi_Y,\Pi_D\) such that
\[
 q_2^3Y_g=Q_g\Pi_Y+q_2^2k_YL_{gY},\qquad
 q_2^2D_g=Q_g\Pi_D+q_2k_DL_{gD}.                     \tag{87.19}
\]
Coprimality forces \(q_2^2\mid\Pi_Y\) and \(q_2\mid\Pi_D\).
Thus \(H_Y=\Pi_Y/q_2^2\), \(H_D=\Pi_D/q_2\) are genuine
polynomials in \(S[\tau]\), and formal cancellation gives
\[
 q_2Y_g=Q_gH_Y+k_YL_{gY},\qquad
 q_2D_g=Q_gH_D+k_DL_{gD}.                            \tag{87.20}
\]
These identities remain valid at \(q_2=0\). Defining polynomials by
proved exact division is different from inverting their divisor at a ray.

For \(j=Y,D\), write \(P_Y=Y_g,P_D=D_g\), and define
\(Z_j=q_2a_j\tau+q_{1g}a_j-q_2\mu_j\). Direct quadratic expansion and
(87.15) give
\[
 a_j^2Q_g-Z_jL_{gj}=q_2cC_j.
\]
After substituting (87.20),
\[
 Q_g(k_ja_j^2+Z_jH_j)-q_2Z_jP_j=q_2k_jcC_j.
\]
Coprimality again proves that
\(A_j=(k_ja_j^2+Z_jH_j)/q_2\) is polynomial. Cancel the formal factor
to obtain
\[
 k_jcC_j=Q_gA_j-Z_jP_j.                              \tag{87.21}
\]
Similarly the cross identity in (87.15) gives
\[
\begin{aligned}
 q_2k_Yk_Dc_0F_{16}
 &=q_2(k_Ya_YD_g-k_Da_DY_g)
    +Q_g(k_Da_DH_Y-k_Ya_YH_D),\\
 A_{16}&=(k_Da_DH_Y-k_Ya_YH_D)/q_2\ \in S[\tau],\\
 k_Yk_Dc_0F_{16}&=k_Ya_YD_g-k_Da_DY_g+Q_gA_{16}.
\end{aligned}                                                    \tag{87.22}
\]
The membership statement for \(A_{16}\) follows from the same
coprimality before cancellation. Equations (87.19)–(87.22) specify all
syzygy cofactors by exact polynomial operations; expanded cofactor lists
are not required to reconstruct them.

At an original ray \(Q_g=Y_g=D_g=0\). Since the multipliers in
(87.18) are nonzero, (87.21)–(87.22) force \(C_Y=C_D=F_{16}=0\).
Neither \(F_8\), \(q_{1g}\), \(q_{0g}\), \(A\), \(a_Y\) nor
\(a_D\) was inverted at that point. This proves the theorem, including
the entire constant-leading and double-pivot strata.

### 87.5. Homogeneous mean equations and complete regular lifts

For \(P=F_{16},C_Y,C_D\), put respectively \(n=8,10,10\), and write
\(P(x,kx)=\sum_{j=0}^{2n}h_j(b,k)x^j\). Exact coefficient division
of the polynomials defined in (87.13) gives
\[
 h_{n+j}=(1+k^2)^jH_j,\qquad h_{n-j}=(-R)^jH_j
       \quad(1\le j\le n).                          \tag{87.23}
\]
Define \(p_0=2,p_1=t\), \(p_j=tp_{j-1}+R(1+k^2)p_{j-2}\), and
\[
 h_P(b,k,t)=h_n+\sum_{j=1}^nH_jp_j(t),\qquad
 \mathcal H_P(b;X,Y,Z)=X^nh_P(b,Y/X,Z/X).             \tag{87.24}
\]
The total \((k,t)\)-degree is \(n\), so the homogenization is a
polynomial. The three \(h_P\) have 471,906,959 terms, with respective
positive integer contents
\[
 32614907904,\qquad6262062317568,\qquad2717908992.     \tag{87.25}
\]
All 28 reciprocity identities in (87.23), and these coefficient counts
and contents, are directly checkable from the finite construction
(87.5),(87.12)–(87.14). There is no coefficient interpolation premise.
The polynomial identity
\[
 P(x,y)=\mathcal H_P(b;x,y,x^2+y^2-R)                 \tag{87.26}
\]
holds also at \(x=0\). Theorem 87.2 therefore assigns every generic ray
to a real projective common zero
\[
 \mathcal H_{F_{16}}=\mathcal H_{C_Y}=\mathcal H_{C_D}=0,
 \qquad[X:Y:Z]=[x:y:x^2+y^2-R],\quad(X,Y)\ne(0,0).    \tag{87.27}
\]
The punctured zero-channel-mean result in §75 excludes the omitted
projective point. Vertical slopes are included in (87.27).

For use in the converse direction, on \(F_8\ne0\) equations (87.15)
show that the original equations on the global line are equivalent to
\(Q_g=L_{gY}=L_{gD}=0\). The projective equations and the following
rules retain every affine-pivot case. If \(a_Y^2+a_D^2>0\), the unique
lift is
\[
 \tau=-\frac{a_Y\mu_Y+a_D\mu_D}{a_Y^2+a_D^2}.          \tag{87.28}
\]
The cross identity gives consistency, and either nonzero coefficient's
quadratic compatibility gives \(Q_g(\tau)=0\). If \(a_Y=a_D=0\),
the two compatibility identities force \(\mu_Y=\mu_D=0\); retain
every real root of the genuine quadratic \(Q_g\), including a double
root once. Apply the original strict tests (87.3) and all six orders
(87.4) in both cases. These are necessary and sufficient on
\(F_8\ne0\); no converse at \(F_8=0\) is asserted or needed below.

## 88. Exact projective decic outside a specified finite guard

### 88.1. Six component algebras and coefficient data

Let \(h_0,h_1,h_2\) be the three affine polynomials \(h_P\) of
(87.24), divided by their respective positive contents (87.25).
Their total \((k,t)\)-degrees are \(n_0=8,n_1=n_2=10\).
This section specifies an exact nonzero polynomial \(E_*(b)\).
For every real \(0<|b|<1\) with \(E_*(b)\ne0\), the entire allowed
real projective zero set is
\[
 [1:k:T(b,k)/F_k(b,k)],\qquad F(b,k)=0,\quad k\in\mathbb R.
                                                               \tag{88.1}
\]
In particular no vertical projective point is missed. Every zero of the
guard is retained; the theorem does not assert that the guard has no zeros.

Here are complete finite data for six triples \((P_i,N_i,D_i)\), with
\(\deg_k P_i=10,4,4,4,4,4\). For \(i=0\), put \(P_0=F,N_0=T,D_0=F_k\).
To specify the two larger polynomials compactly, let \(z=b^2\) and use
\[
 F=d(z)k^{10}+\sum_{j=0}^9b^{j\bmod2}n_j(z)k^j,
 \qquad T=\sum_{j=0}^9b^{(j+1)\bmod2}m_j(z)k^j.         \tag{88.2}
\]
The following lists are ascending coefficient lists in \(z\), including
all zero coefficients. Thus \([c_0,\ldots,c_d]\) denotes
\(\sum_{a=0}^dc_az^a\). No overall primitive rescaling is implicit.

```text
d: [-4782969, -100973790, -623911734, -51136434, 3423897216, -4443378201, 3710094597, -1980453159, -317812653, 549356904, -97822836, -56495664, 42503394, -12831873, 2291829, -213735, 7668]
n0: [0, 0, 0, 11160261, 27812079, 56805138, -205470837, 256469490, -410692356, 527169789, -345821562, 99659889, -10525545, -108396, 28671, 520, 878, 45]
n1: [0, 0, -38263752, -99910908, 73338858, 839558682, -2487970566, 4619744442, -5591809080, 4333703796, -2072069748, 533909880, -57560166, -126270, 128802, 13034, 3796, 144]
n2: [0, 0, 14348907, -63772920, -1720097370, 1328012010, 5553597816, -16817069907, 25477008165, -23413324347, 13857999615, -5426082918, 1261527048, -132110604, 949410, 135713, 34621, 4845, 108]
n3: [0, -111602610, 155535066, 1277466066, -11401850142, 8784955926, 23371134930, -56964548430, 65468872890, -48452931054, 24134994414, -8130887226, 1694599302, -173717182, 4011494, -13130, 44382, 2376]
n4: [0, -52612659, -1112306013, 1585642797, 10479307932, -36034888446, 13542002415, 59745863493, -103018565016, 93230908956, -58739335623, 25838470935, -7636685436, 1436641830, -151476627, 6131959, -69960, 33903, 648]
n5: [9565938, -387951930, -4917600720, 4902484176, 29487614058, -46742046786, -12420812808, 85737590856, -104526126810, 80199806994, -45051347664, 17745148944, -4705782978, 833876410, -90427352, 4154456, -36672, 10800]
n6: [14348907, 172186884, -400883661, -9895667616, 8926673526, 19012419873, -3865878981, -42433013808, 64127353968, -61445638287, 43636671621, -22175934552, 7981912554, -2018919933, 339645953, -32917848, 1310725, -3609, 972]
n7: [57395628, 545258466, 703982178, -10887572718, 27359251902, -36577824318, 33111962946, -26431561494, 24506150022, -21599388882, 14298241014, -7032664170, 2534432106, -605838986, 85047398, -6230546, 175782, 1080]
n8: [9565938, 162089505, 1092465549, 560493108, -18934357095, 46884158046, -46538865738, 17563842927, -4183098228, 4312691829, -3529812519, 2737325466, -1632516975, 562623036, -105272684, 10451731, -512856, 10368]
n9: [9565938, 179627058, 2176073748, 3410197848, -21872300724, 24741845928, -12768637662, 4427340930, 912791106, -1086873390, -293050008, 503873964, -241843368, 61526132, -8357246, 537434, -12024]
m0: [0, 0, 95659380, 127545840, -335870712, -130143996, -1831070124, 3416968800, 344583720, -2875721292, 1239833628, -26691120, -65070216, 9530028, -268260, 47840, -3752, -612]
m1: [0, 0, -784406916, -1235068884, -3141170604, -223205220, 14871451284, -15230311740, 2577869388, 13017260196, -14968606572, 5334871572, -155693556, -265751676, 44229708, -1195652, 111572, -26436, -2160]
m2: [0, -382637520, -4914766368, -8198363160, -9356195952, -17658642816, 83736835776, -40957068744, -33233267088, 49900376592, -32686423776, 10391725656, -516010896, -453352032, 79311616, -1427832, 70544, -40800, -1728]
m3: [0, -937461924, -5016803040, -14137747776, -23027220432, 82353199608, -172241996400, 202925431440, -40590824976, -88524954432, 81112867344, -40874451552, 12231579024, -990500952, -352763728, 63982096, -206768, -79548, -22896]
m4: [-57395628, -6224236992, -10056989484, -20369779236, -97589337516, 389877321060, -440997956172, 227414696364, -8392087620, -83707878924, 70701092028, -33613194348, 9614279484, -1270228500, -18749668, 16133604, 470112, -178308, -7776]
m5: [0, -1192553604, -17890429824, 32633311752, 28650102408, -273257829288, 528267470544, -398480550408, 138753270216, -21433066560, -29995182576, 36331636536, -17954492904, 5584686792, -1252739536, 160402376, -6675048, 334500, -80784]
m6: [-76527504, -5080575960, -37579255992, 102161855880, 79676941464, -247514827248, 162907897896, -106461252936, 98060921784, -43267230864, 456353784, 8093813112, -6200679288, 2968827984, -784013576, 98675528, -4554056, 61704, -7776]
m7: [114791256, 1383872364, -824796432, -38812199112, 97325978976, -46662881760, 35541514368, -87280353144, 1740886992, 51229973448, -28786941216, 9619076808, -355825440, -2324308896, 1178757888, -239878536, 21623448, -649908, -6480]
m8: [184941468, 2385107208, 4067295120, -33318516348, 64214842716, -114615053784, 100540659024, -28248875388, 9436447188, 7968367224, -14620371696, 5112009612, 598339188, -777006504, 205113360, -26147220, 1656000, -41472]
m9: [38263752, 440033148, 1252074996, 158015124, -18713100492, 33424489620, -20586134772, 13769780652, -13980904884, 896960628, 4501286316, -2055671028, 145590732, 167159052, -65656876, 10656052, -816532, 24048]
```

For each remaining component the next lists are coefficients in ascending
powers of \(k\). Entries are literal polynomials in \(b\), with `^`
denoting an integer power.

```text
P1: [-b^10 - 126*b^6 + 378*b^4 + 243*b^2 + 243, 6*b^3*(b^2 - 6)*(b^4 - 6*b^2 + 27), -3*(7*b^8 - 42*b^6 + 198*b^4 - 324*b^2 - 81), 18*b^3*(b^4 - 6*b^2 + 27), 81*b^4]
N1: [2*b*(b^2 - 3)*(b^2 + 3)^2*(b^4 - 6*b^2 + 27), -6*b^2*(b^2 - 12)*(b^2 - 3)*(b^2 + 3)^2, 0, 18*b^2*(b^2 - 3)*(b^2 + 3)^2]
D1: [3*b^3*(b^2 - 6)*(b^4 - 6*b^2 + 27), -3*(7*b^8 - 42*b^6 + 198*b^4 - 324*b^2 - 81), 27*b^3*(b^4 - 6*b^2 + 27), 162*b^4]
P2: [b^8 + 84*b^6 + 594*b^4 + 108*b^2 + 81, 36*b*(3*b^6 + 23*b^4 - 33*b^2 - 9), 6*(7*b^8 + 78*b^6 - 108*b^4 + 162*b^2 + 81), 108*b*(b^2 + 3)*(b^4 - 3), 9*(b^8 + 24*b^6 - 54*b^4 + 81)]
N2: [-2*b*(b^2 - 3)*(b^6 + 36*b^4 + 135*b^2 - 54), -18*b^2*(b^2 - 3)*(5*b^4 + 22*b^2 - 33), -6*b^3*(b^2 - 3)*(7*b^4 + 48*b^2 - 81), -54*b^2*(b^2 - 3)*(b^4 - 4*b^2 - 3)]
D2: [9*b*(3*b^6 + 23*b^4 - 33*b^2 - 9), 3*(7*b^8 + 78*b^6 - 108*b^4 + 162*b^2 + 81), 81*b*(b^2 + 3)*(b^4 - 3), 9*(b^8 + 24*b^6 - 54*b^4 + 81)]
P3: [16*b^4, 16*b^3*(b^2 - 3), 4*b^2*(b^2 - 5)*(b^2 - 3), -4*b*(b^2 - 3)^2, (b^2 - 3)^2]
N3: [-6*b^3*(2*b^10 + 21*b^8 - 126*b^6 + 216*b^4 + 540*b^2 + 243), -2*b^2*(b^2 - 3)*(4*b^10 + 37*b^8 - 327*b^6 + 405*b^4 + 1107*b^2 + 486), 3*b*(b^2 - 3)*(4*b^10 + 40*b^8 - 285*b^6 + 45*b^4 + 513*b^2 + 243), -3*(b^2 - 3)^2*(b^8 + 12*b^6 - 42*b^4 - 72*b^2 - 27)]
D3: [b^3*(b^2 + 1)*(2*b^8 + 21*b^6 - 153*b^4 - 189*b^2 - 81)]
P4: [-2*b^10 + 33*b^8 - 180*b^6 + 486*b^4 + 486*b^2 + 729, -4*b*(b^10 - 21*b^8 + 126*b^6 - 594*b^4 + 81*b^2 - 729), 6*(11*b^10 - 90*b^8 + 594*b^6 - 540*b^4 + 1539*b^2 + 486), -216*b*(b^8 - 10*b^6 + 18*b^4 - 54*b^2 - 27), 243*(b^4 - 4*b^3 + 4*b^2 + 3)*(b^4 + 4*b^3 + 4*b^2 + 3)]
N4: [-2*b^3*(b^2 - 3)*(b^2 + 3)*(b^4 - 12*b^2 + 63), -6*(b^2 - 3)*(b^2 + 3)*(b^8 - 10*b^6 + 45*b^4 - 90*b^2 - 54), 6*b*(b^2 - 3)*(b^2 + 3)*(11*b^6 - 36*b^4 + 153*b^2 + 108), -54*(b^2 - 3)*(b^2 + 3)*(2*b^6 - 11*b^4 - 18*b^2 - 9)]
D4: [b*(b^10 - 21*b^8 + 126*b^6 - 594*b^4 + 81*b^2 - 729), -3*(11*b^10 - 90*b^8 + 594*b^6 - 540*b^4 + 1539*b^2 + 486), 162*b*(b^8 - 10*b^6 + 18*b^4 - 54*b^2 - 27), -243*(b^4 - 4*b^3 + 4*b^2 + 3)*(b^4 + 4*b^3 + 4*b^2 + 3)]
P5: [1, 0, 2, 0, 1]
N5: [9*(b^4 + 3), 4*b*(b^2 - 3*b + 3)*(b^2 + 3*b + 3), -3*(b^4 - 12*b^2 - 9), 36*b]
D5: [2*b^2*(b^2 + 9)]
```

These data give 190 terms in \(F\) and 180 in \(T\). For each
\(i=0,\ldots,5\), \(a=0,1,2\), direct polynomial division gives
\[
 P_i\mid D_i^{n_a}h_a(b,k,N_i/D_i)
                         \quad\hbox{in }\mathbb Q[b,k].          \tag{88.3}
\]
The right side means homogeneous expansion, so it is polynomial even at
zeros of \(D_i\). For an explicit bounded reconstruction of all eighteen
identities, write \(h_a=\sum_{j=0}^{n_a}c_j(b,k)t^j\), initialize
\(r=c_{n_a}\), \(d=1\), and for \(j=n_a-1,\ldots,0\) perform
\[
 d\leftarrow\operatorname{rem}_{P_i}(dD_i),\qquad
 r\leftarrow\operatorname{rem}_{P_i}(rN_i+c_jd).
                                                               \tag{88.4}
\]
Here \(\operatorname{rem}_{P_i}\) is multivariate division over
\(\mathbb Q\) with lexicographic order \(k>b\). Each final remainder
is exactly zero over \(\mathbb Q[b,k]\).
Equations (87.5),(87.12)–(87.14),(87.23)–(87.25) and the literal arrays
above specify every input to these checks. This is a characteristic-zero
polynomial certificate, rather than an interpolation or modular inference.

Two components must retain their nonreduced lengths:
\[
 P_3=Q^2,\quad Q=(b^2-3)k^2-2b(b^2-3)k-4b^2,
 \qquad P_5=(1+k^2)^2.                                \tag{88.5}
\]
Their four-dimensional algebras are not replaced by quadratic squarefree
quotients in the completeness argument.

### 88.2. The finite determinant and resultant guard

The symbolic calculation is over \(K=\mathbb Q(b)\). At a fixed real
parameter satisfying the guard below, take \(K=\mathbb C\) and specialize
every displayed coefficient; the same finite-dimensional argument applies.

Order all 210 monomials \(t^ak^c\), \(a+c\le19\), by descending
total degree and then descending \(a\). Set
\[
 \mathcal B=\{t^ak^c:a+c\le6\}\cup\{tk^6,k^7\};
 \qquad |\mathcal B|=30.                              \tag{88.6}
\]
For \(j=0,1,2\), form the coefficient rows of \(t^ak^ch_j\), listing
\(a=0,\ldots,19-n_j\), and then \(c=0,\ldots,19-n_j-a\) for each
\(a\). There are 78,55,55 rows, in that order. Delete zero-based row
indices \(1,13,78,183,184,185,186,187\); keep the 180 columns whose
monomials are outside \(\mathcal B\), in the specified order. Call the
resulting matrix \(M_*(b)\), and \(m_*(b)=\det M_*(b)\). Direct exact
reduction gives
\[
 m_*(1/2)=560\pmod{1009},\qquad
 m_*(-1/2)=449\pmod{1009}.                            \tag{88.7}
\]
Here \(1/2\) and \(-1/2\) reduce to 505 and 504, respectively.

If \(m_*(b)\ne0\), the selected relations express every non-\(\mathcal B\)
monomial of degree at most 19 in the span of \(\mathcal B\) modulo
\((h_0,h_1,h_2)\). Every one-step \(t\)- or \(k\)-multiple of a member
of \(\mathcal B\) has degree at most eight, hence has such an expression.
Starting at 1 and multiplying successively proves the full quotient bound
\[
 \dim K[k,t]/(h_0,h_1,h_2)\le30.                      \tag{88.8}
\]
This is not merely a truncated Macaulay rank or a count at one parameter.

For the vertical chart put
\(v_j(b,s)=h_j^{\rm hom}(b;0,1,s)\). Read it from terms \(k^at^c\)
with \(a+c=n_j\), replacing them by \(s^c\). In columns
\(1,s,\ldots,s^{17}\), use the ten rows \(s^av_0\), \(0\le a\le9\),
followed by the eight rows \(s^av_1\), \(0\le a\le7\). For this
\(18\times18\) matrix \(V_*(b)\),
\[
 v_*(b)=\det V_*(b),\qquad v_*(\pm1/2)=598\pmod{1009}.
                                                               \tag{88.9}
\]
If \(v_*(b)\ne0\), these rows span 1, so no common vertical point
exists. The excluded point \([0:0:1]\) is already outside (87.27).

Let \(\ell_i\) be the leading \(k\)-coefficient of \(P_i\), and put
\[
 u_i=\operatorname{Res}_k(P_i,D_i),\quad
 r_{ij}=\operatorname{Res}_k(P_i,P_j),\qquad
 E_*=m_*v_*\prod_i\ell_i u_i\prod_{i<j}r_{ij}.         \tag{88.10}
\]
All resultants use the displayed argument order. These finite definitions
specify one integer polynomial without expanding a very large determinant.
At \(b=1/2\), the pairs \((\ell_i,u_i)\) modulo 1009 are
\[
 (782,916),(951,933),(99,182),(449,448),(28,249),(1,142).
                                                               \tag{88.11}
\]
The fifteen pair-resultant residues, ordered lexicographically by
\((i,j)\), are given below. Their nonvanishing proves that \(E_*\) is
nonzero at the half parameter, hence is a nonzero polynomial with a finite
real zero set.

```text
596,497,501,510,709,985,991,267,100,512,674,216,1008,841,503
```

### 88.3. Characteristic-zero completeness and real-component exclusion

At any parameter with \(E_*\ne0\), form
\[
 \mathcal A_i=K[k]/(P_i),\qquad
 \mathcal A_{\rm prod}=\prod_{i=0}^5\mathcal A_i.
\]
Its dimension is \(10+5\cdot4=30\). All \(D_i\) are units by their
resultant guards, and the Chinese remainder theorem shows that \(k\)
alone generates the product algebra. Put \(t=N_i/D_i\) on factor \(i\).
The eighteen exact identities (88.3) induce a surjection
\[
 K[k,t]/(h_0,h_1,h_2)\longrightarrow\mathcal A_{\rm prod}.
\]
The left side has dimension at most 30 by (88.8), while the right side
has dimension 30. The map is therefore an isomorphism. This proves the
complete component description with multiplicities, at every safe
parameter, rather than only at a generic point or a sampled specialization.
Equation (88.9) simultaneously excludes all allowed vertical points.

Five components have no real points on the entire puncture. Indeed
\[
 Q=-R(k-b)^2-b^2(1+b^2)<0,\qquad P_5=(1+k^2)^2>0.
                                                               \tag{88.12}
\]
For \(i=1,2,4\), write \(P_i=a_0+a_1k+a_2k^2+a_3k^3+a_4k^4\).
The three even polynomials
\[
 a_0,\quad a_4,\quad S_i=4a_0a_2a_4-a_1^2a_4-a_3^2a_0
                                                               \tag{88.13}
\]
have the following Bernstein coefficient lists in \(z=b^2\). A list
\([B_0,\ldots,B_d]\) means exactly
\(\sum_{j=0}^dB_j\binom djz^j(1-z)^{d-j}\).

```text
1 a0: [243, 1458/5, 378, 2448/5, 3069/5, 737]
1 a4: [0, 0, 81]
1 S: [0, 0, 3188646/11, 57395628/55, 27398736/11, 4822335, 624876201/77, 134948835/11, 931699908/55, 107464806/5, 274301316/11, 25879986, 22503096]
2 a0: [81, 108, 234, 480, 868]
2 a4: [729, 729, 648, 540, 468]
2 S: [114791256, 133923132, 1717617312/11, 10059115248/55, 11879714016/55, 2835611712/11, 23973579072/77, 380969568, 26006645376/55, 32791843008/55, 8417405952/11, 1001991168, 1341633024]
4 a0: [729, 4131/5, 972, 5742/5, 1344, 1552]
4 a4: [2187, 3645, 5994, 8748, 11664]
4 S: [18596183472, 23761789992, 1047585002256/35, 16952487477336/455, 2984011454304/65, 8014011237216/143, 339400908753408/5005, 11633435281152/143, 69190548281856/715, 571231795041792/5005, 133585208377344/1001, 5413227687936/35, 80807123017728/455, 7068127371264/35, 227221438464, 252709797888]
```

Expansion verifies each Bernstein identity against (88.13). Every entry
is nonnegative and each list has a positive entry, so all three
polynomials are strictly positive for \(0<z<1\). The Gram matrix
\[
 \begin{pmatrix}a_0&a_1/2&0\\a_1/2&a_2&a_3/2\\0&a_3/2&a_4\end{pmatrix}
                                                               \tag{88.14}
\]
has positive endpoint block and Schur complement \(S_i/(4a_0a_4)>0\).
It is positive definite, proving \(P_i(k)>0\) for every real \(k\).
Thus only \(P_0=F\) has real points. This proves (88.1).

For a real root \(k\) set \(t=T/F_k\) and retain both radial lifts
\[
 x_\pm=\frac{t\pm\sqrt{t^2+4R(1+k^2)}}{2(1+k^2)},
 \qquad y_\pm=kx_\pm.                                 \tag{88.15}
\]
The radicand is strictly positive and neither lift is zero. The two scaled
means satisfy \(G_-=-R/\bar G_+\). At each mean use the entire line-lift
rule of §87.5 and the original strict filters and root orders. The degree
of \(F\) alone is not a count of physical rays. This construction is
necessary for every original generic ray by Theorem 87.2, and sufficient
with the stated filters whenever \(F_8\ne0\).

## 89. Arbitrary generic pairs outside a finite parameter guard

### 89.1. A degree-twenty coefficient field

Work over \(K=\mathbb Q(i)(b)\). Use the literal \(F,T\) of §88,
and set
\[
 t=T/F_k,\qquad
 \mathcal A=K[k,X]/(F,(1+k^2)X^2-tX-R).                \tag{89.1}
\]
The notation first takes the quotient by the monic normalization of
\(F\), inverts \(F_k\) and \(1+k^2\), then adjoins the monic radial
quadratic. These are legitimate operations: their norms at \(b=1/2\)
are nonzero, as certified below. A fixed basis is
\[
 \mathcal B_{20}=(1,k,\ldots,k^9,X,kX,\ldots,k^9X).
\]
Put \(Y=kX\), \(G=X+iY\), and let bar fix \(b,k,X\) and conjugate
\(i\). Define the involution
\[
 \iota(k)=k,\qquad \iota(X)=t/(1+k^2)-X.
\]
The radial relation proves
\[
 X\iota(X)=-R/(1+k^2),\qquad
 \iota(G)=-R/\bar G.                                  \tag{89.2}
\]
Indeed \(X((1+k^2)X-t)=R\) makes \(X\) a unit, and
\(G\bar G=(1+k^2)X^2\) makes both mean elements units.

Here is an exact half specialization, using only the already printed
coefficient lists in §78.A. Let \(f=f_{1,20}\), with
\((x,u,v)=(P_x,P_u,P_v)/f'(y)\) in \(\mathbb Q[y]/(f)\). Set
\[
 k=y/x,\qquad t=(x^2+y^2-11/4)/x.
\]
Homogeneous substitution and exact univariate division give
\[
 F(1/2,k)=0,\qquad tF_k(1/2,k)=T(1/2,k).               \tag{89.3}
\]
The required denominators are units. These identities define a surjection
from the half specialization of (89.1) onto \(\mathbb Q(i)[y]/(f)\):
its image contains \(y=kX\). Both algebras have dimension twenty, so this
is an exact isomorphism. The coordinates \(x,u,v\) are the original
scaled input coordinates of §§78,87; no phase convention changes here.

For completeness, the following two-prime certificate proves that \(f\)
is irreducible. Its leading coefficients modulo 7 and 73 are 5 and 44.
After dividing by those constants, its respective factorizations are

```text
mod 7:
y^10 + 3*y^8 - 3*y^7 + 3*y^6 + 2*y^5 + 3*y^4 - y^2 + 1
y^10 + 2*y^9 + 3*y^8 - y^7 + 3*y^6 + 3*y^5 - 2*y^4 + 3*y^3 - 2

mod 73:
y^2 + 20*y - 6
y^2 + 31*y - 36
y^16 + 18*y^15 + 35*y^13 + 28*y^12 - 7*y^11 + 15*y^10 - 8*y^9
 + 19*y^8 + 29*y^7 + 31*y^6 - 31*y^5 - 11*y^4 + 28*y^3
 - 18*y^2 - 21*y - 30
```

Multiplication gives the exact reductions of the printed \(f\).
For each degree-\(n\) factor \(g\) over \(\mathbb F_p\), repeated
modular squaring and exact Euclidean gcd give
\(y^{p^n}=y\pmod g\) and
\(\gcd(g,y^{p^{n/\ell}}-y)=1\) for every prime \(\ell\mid n\).
The required smaller Frobenius exponents \(n/\ell\) are 2,5 for each
decic, 1 for the quadratics, and 8 for the degree-sixteen factor.
Thus all displayed factors are irreducible. A proper rational factor of
\(f\) would have degree 10 from the first prime, but one of
2,4,16,18 from the second, which is impossible.

The exact Sturm count in §78.6 is eight real roots. Hence the number
field \(\mathbb Q[y]/(f)\) has a real embedding and does not contain
\(i\). Since \(\mathbb Q(i)/\mathbb Q\) is quadratic Galois, \(f\)
remains irreducible over \(\mathbb Q(i)\).

The characteristic polynomial of multiplication by \(Y\) in (89.1)
is monic of degree twenty, regular at \(b=1/2\), and specializes by
(89.3) to the monic \(f\). It is irreducible over \(K\). Otherwise
monic proper factors would have coefficients integral over the local
ring \(\mathbb Q(i)[b]_{(b-1/2)}\): their coefficients are symmetric
functions of integral roots. This ring is integrally closed, so the factor
coefficients lie in it. Specialization preserves the two positive monic
degrees and contradicts the irreducibility of \(f\). Consequently
\(\mathcal A=K[Y]\) is a field, with basis \(1,Y,\ldots,Y^{19}\).
No claim that every individual specialization remains a field is needed.

### 89.2. Original coordinates, unit witnesses and one physical branch

Evaluate the coefficient polynomials of §87 at \((x,y)=(X,Y)\), and put
\[
 \tau=-\mu_Y/a_Y,\quad
 u=(-AC_0-D_0\tau)/\sigma,\quad
 v=(-D_0C_0+A\tau)/\sigma.                             \tag{89.4}
\]
Then construct \(C,D,Y_c,q,e\) from (87.2)–(87.3), and set
\[
 \epsilon=\bar e,\quad \Delta=D\bar D-C\bar C,\quad
 \delta=q^2[3-4(e+\epsilon)]+6q-1.                    \tag{89.5}
\]
All inversions are legitimate in the field and regular at the half
parameter. The following multiplication norms in the exact degree-twenty
half algebra, reduced modulo 97 with \(i=22\), certify this in order:

```text
1+k^2:18; F_k:49; radial discriminant:11;
X:52; F8:60; aY:17; sigma:65;
G:92; barG:82; beta:89; barbeta:80;
C:25; barC:64; D:80; barD:46;
Yc:39; barYc:55; q:62; e:12; epsilon:3;
Delta:75; delta:53.
```

Here the radial discriminant is \(t^2+4R(1+k^2)\). Each norm is the
determinant of multiplication by the named element, in the monic \(f\)
quotient with basis \(1,y,\ldots,y^{19}\). Polynomial inverses are
computed by the adjugate of their multiplication matrix. Thus (87.2),
(87.13)–(87.14), (89.3)–(89.5), and §78.A reconstruct every entry of
these small certificates. The determinant of the \(\mathcal B_{20}\)
columns expressed in the \(Y\)-power basis is \(79\pmod{97}\).

The exact half specialization of (89.4) equals the original \(u,v\)
from §78.A over \(\mathbb Q(i)\). To see this without relying on a
modular equality, those RUR coordinates satisfy all original equations
identically. The exact remainder identities give
\(a_Y\tau+\mu_Y=0\); since \(a_Y,\sigma\) are units there, the
coordinates are uniquely (89.4). All other coordinates use the same
original definitions. The nonzero modular norms are unit certificates,
not substitutes for this characteristic-zero identification.

At one of the six strict physical half points of §78.6, \(F_k\ne0\).
The real implicit function theorem continues its \(k\)-root analytically
near \(1/2\). The radial discriminant is strictly positive; (89.4)
and the original coordinates therefore continue analytically too.
All strict tests (87.3) persist on some open interval. The cubic roots
are simple and may be ordered analytically locally. Equation (87.4)
then gives an actual analytic common-flat ray \(w(b)\).

The centered lower-channel map is real-linear with determinant
\(|C|^2-|D|^2=-\Delta\ne0\), so the lower channel is also
three-distinct locally. Its mean is nonzero. The actual \(\Theta w\)
therefore admits the same selected-channel normalization; its scaled mean
is
\[
 -|\kappa|^2/\bar G=-R/\bar G=\iota(G).               \tag{89.6}
\]
The transformed \(F_8\) and \(a_Y\) are units, since \(\iota\)
preserves units. Uniqueness of the line lift identifies its full
coefficient point with \(\iota\) applied to the first. Arbitrary common
phase and all six root orders are retained in this identification.

We will use a simple field identity principle. If an element of a finite
field extension of \(\mathbb Q(i)(b)\) vanishes on an actual analytic
solution branch on an open parameter interval, it is zero in the field.
Otherwise write its inverse in the fixed finite basis with rational-function
coefficients. Away from finitely many parameter poles both evaluate on
the branch and their product is 1, contradicting the vanishing. The proved
field property is essential; one branch in a reducible algebra would not
suffice.

### 89.3. All-order overlaps, exact rank and the complete guard

Use the integer 508-term polynomial \(\mathcal N\) reconstructed by
(79.8)–(79.9). Those equations specify it as the product of all six relative
ordinary overlaps, with a finite orbit-sum recurrence and no root choices.
Evaluate it in \(\mathcal A\otimes_K\mathcal A\), using exactly the
nine arguments in (79.8), with primed quantities in the second factor
and the current symbolic \(R=3-b^2\). Call the element \(N\).
For any physical pair, it is the product of its six relative overlaps,
divided by \((3\sqrt{qq'})^6\). Thus every arbitrary orthogonal generic
pair annihilates \(N\), irrespective of relative permutation.

Define the surjective algebra map
\[
 \rho:\mathcal A\otimes_K\mathcal A\longrightarrow\mathcal A,
 \qquad \rho(a\otimes c)=a\iota(c),\qquad \dim\ker\rho=380.
                                                               \tag{89.7}
\]
Along the actual branch above, the second point is \(\Theta w\).
The original identity \(w\perp\Theta w\) makes one overlap factor
zero. The field identity principle yields \(\rho(N)=0\) in
characteristic zero. Therefore multiplication by \(N\) has image inside
\(\ker\rho\) and rank at most 380. This uses an open actual solution
branch and fieldness, rather than inferring an identity from one parameter.

For the matching lower bound, form the \(400\times400\) multiplication
matrix in basis \(Y^r\otimes Y^s\), indexed by \(20r+s\), and let
\(h(b)\) be its leading \(380\times380\) principal minor. The exact
half bridge identifies its specialization with (79.10), so
\[
 h(1/2)=2\pmod{97}.                                  \tag{89.8}
\]
Equivalently, exchanging row pairs \((38,39),(167,168),(257,258)\)
gives the residue 95. This is only a fixed overall sign. The principal
minor convention in (89.8) is used here. In either convention \(h\)
is a nonzero rational function, regular and nonzero at the half parameter.

Here is the complete finite safe-specialization guard. It is useful to
state the construction rather than an impractically expanded polynomial.
All operations are in rational functions of \(b\), with coefficients
in \(\mathbb Q(i)\).

1. Include \(E_*(b)\), \(b,R,1+b^2\), and the leading coefficient of
   \(F\) as required nonzero scalars.
2. Construct (89.1) in \(\mathcal B_{20}\) by companion reduction in
   \(k\) and the monic radial quadratic. Compute every inverse by the
   adjugate and determinant of its multiplication matrix. Construct
   (89.4)–(89.5), the involution, and the basis-change matrix with columns
   \(Y^j\). Mark the norms of every inverted element as required
   nonzero scalars. Also mark every norm listed in §89.2, their needed
   conjugates, and the basis-change determinant.
3. Construct the nine overlap arguments, \(N\), its multiplication
   matrix in the \(Y\)-power basis, and the fixed principal minor
   \(h(b)\). Mark \(h\) as a required nonzero scalar.
4. Reduce every scalar rational-function entry in these finite arrays
   to coprime numerator and denominator over \(\mathbb Q(i)[b]\).
   Include every nonconstant denominator and its coefficient-conjugate.
   For each required nonzero scalar include also its numerator and its
   coefficient-conjugate. Multiply all factors, discard nonzero constants,
   and clear the final rational constant denominator. Taking the primitive
   integer part with positive leading coefficient fixes a normalization.

Call this polynomial \(G_*(b)\). Every factor is nonzero, regular and
nonzero at \(b=1/2\), by the exact half bridge and the printed witnesses.
In particular a reduced denominator cannot vanish at that regular point.
Hence \(G_*\in\mathbb Q[b]\) is nonzero and \(G_*(1/2)\ne0\), and
its real zero set is finite. This includes every chosen pivot, degree,
unit, basis-change and matrix-denominator failure. No root of the guard
is declared harmless without proof.

At any real parameter with \(G_*\ne0\), the specialized algebra has
dimension twenty, \(\rho\) remains onto, \(\rho(N)=0\) specializes
exactly, and the selected lower minor stays nonzero. Thus
\[
 N(\mathcal A_b\otimes\mathcal A_b)=\ker\rho_b.        \tag{89.9}
\]
The ideal conclusion is obtained anew after specialization from the two
rank bounds. It does not silently specialize an unrecorded generic ideal
multiplier with a possibly vanishing denominator.

### 89.4. Complete generic coverage and arbitrary-pair consequence

For every original generic ray, Theorem 87.2 gives the projective constraints
without any \(F_8\ne0\) assumption. If \(G_*(b)\ne0\), the classification in §88.1
places its mean in the complete degree-twenty radial algebra. The norm
of \(F_8\) is part of the guard, so \(F_8\) is a unit on that entire
specialized algebra and cannot vanish at this mean. This proves complete
regular coverage of the original generic rays at every such parameter.
There is no circular appeal to the converse at \(F_8=0\). All original
leading and pivot strata were retained before applying this unit test.

Put \(M=1+\bar GG'/R\). Equation (89.2) gives \(\rho(M)=0\), so
(89.9) places \(M\) in the ideal generated by \(N\). Evaluate at any
actual orthogonal generic pair. Its all-order overlap norm is zero, hence
\[
 1+\bar GG'/R=0,\qquad G'=-R/\bar G.                  \tag{89.10}
\]
The original channel-mean spinors, proportional to
\((1,G/\kappa)\) and \((1,G'/\kappa)\), are therefore orthogonal.
This assertion was derived for arbitrary pair order and phase, without
assuming covariance of the candidates.

The right side of (89.10) is precisely the other radial lift on the same
projective axis. The actual \(\Theta\) ray has this mean. Its selected
upper channel is three-distinct because \(\Delta\) is a unit; its
transformed \(F_8\) and \(a_Y\) are units too. The global line lift is
unique there, so the second ray has the same coefficient point as this
\(\Theta\) ray. All six orders in (87.4) give
\[
 w'\in S_3\Theta w\quad\hbox{projectively}.           \tag{89.11}
\]
If a ray was initially represented only through its optional \(\Theta\)
channel choice, the same unit and inverse-transport argument shows that
the ray itself has a regular presentation. Thus no relative \(\Theta\)
parity was excluded from the pair statement.

**Theorem 89.1.** For every \(0<|b|<1\) with \(G_*(b)\ne0\), all
orthogonal pairs among the complete original noncanonical generic set
satisfy (89.10)–(89.11). Its graph is a disjoint union of the four-regular
bipartite \(6+6\) orbit-union graphs of §82. In particular there is no
orthogonal triple of generic rays.

Indeed the nonzero mean fixes the common phase and three distinct upper
entries make the six synchronous permutations distinct. The two cosets
are disjoint, since intersection would give \(|G|^2=-R\). The exact
within-union theorem supplies four opposite-coset neighbors per vertex,
and (89.11) excludes every cross-union edge. Such a \(6+6\) graph is
connected: two components would each need at least four vertices on each
side. Alternatively the triple exclusion follows directly because three
nonzero spinors in \(\mathbb C^2\) cannot be pairwise orthogonal.
The theorem retains all guard-zero fibres and makes no aligned-pair
assertion; those are addressed separately next.

## 90. An aligned quintic and all mixed-edge exclusions off a finite guard

### 90.1. Original aligned chart and a uniform Cramer pivot

An aligned ray means that both channels have at most two distinct values
and share a repeated pair; a constant channel is allowed. Use the original
finite chart of §75, with the repeated positions chosen as 1,2:
\[
 w=(1,1,z;g,g,gr),\quad z=(1+iu)/(1-iu),\quad
 r=(1+iv)/(1-iv),\quad d=u-v,\quad \theta=uv,\quad s=u+v.
\]
Put \(K_a=d^2+4\theta=s^2\), \(F_a=d^2+(\theta+1)^2\),
\(J_a=bd-\theta+3\), and write \(\kappa g=s(a+ic)\).
Every nonconstant finite aligned ray has \(K_a>0\); the constant and
\(s=0\) cases are already classified in §75. Its exact original equations
are \(P_0=P_1=P_2=0\), \(K_a(a^2+c^2)=R\), where
\[
\begin{aligned}
 P_0={}&K_a[da-(\theta+1)c]+bd(1-\theta)-d^2-2\theta(\theta+1),\\
 P_1={}&[bd^2-d\theta(b^2+1)+d(b^2-3)+b(\theta^2-2\theta-3)]a\\
 &+[-b^2d^2-4bd+\theta^2-2b^2(\theta+1)+4\theta+3]c
 +(b^2-3)(\theta+1-bd),\\
 P_2={}&[5bd^2+2d\theta(b^2+2)-2db^2+3b(\theta+1)^2]a\\
 &+[-3d^2-2bd(\theta+1)-(2b^2+7)\theta^2-10\theta+2b^2-3]c
 +2(b^2-3)(\theta+1+bd).
\end{aligned}                                                    \tag{90.1}
\]
The first two coefficient rows have determinant \(-K_abJ_aF_a\).
The factors \(b,K_a,F_a\) are nonzero on the physical chart:
\(F_a=0\) would give \(d=0,\theta=-1\), contradicting \(K_a>0\).
At \(J_a=0\), the two normalized Cramer numerators are
\[
 6(b^2-3)(bd+4)V_0,\qquad6d(b^2-3)V_0,
 \quad V_0=(1+b^2)d^2+8bd+16
 =(1+b^2)\left(d+\frac{4b}{1+b^2}\right)^2+\frac{16}{1+b^2}>0.
                                                               \tag{90.2}
\]
Consistency would force both \(d=0\) and \(bd+4=0\), a contradiction.
Thus the first-two-row Cramer solutions \(a=A_a(b,d,\theta)\),
\(c=C_a(b,d,\theta)\) cover every real finite nonconstant aligned ray,
uniformly throughout the puncture.

Define the literal integer polynomials
\[
 \Phi=\frac{bK_aJ_a}{2}P_2(A_a,C_a),\qquad
 \Psi=\frac{b^2K_aJ_a^2F_a}{2}
                 [K_a(A_a^2+C_a^2)-R].                         \tag{90.3}
\]
The cancellations are exact. These formulas define all coefficients from
(90.1), without a rational-function fitting step. The polynomials have
33 and 77 terms, and total \((d,\theta)\)-degrees four and six.
On the physical chart the original system is exactly \(\Phi=\Psi=0\)
with the Cramer values and the retained norm condition.

### 90.2. Projection, all discarded factors and both special differences

The exact resultant factorization is
\[
 \operatorname{Res}_{\theta}(\Phi,\Psi)
 =-162b^6(b^2-3)^4d^4(2b-d)(d^2+4)^2V_0^2Q_4Q_5.      \tag{90.4}
\]
For \(z_b=b^2\), write \(Q_4=\sum_{j=0}^4a_jd^j\), where
\[
\begin{aligned}
 a_0&=64(z_b+3)^2,&a_1&=64b(z_b^2+8z_b+15),\\
 a_2&=384z_b^2+576z_b-192,&
 a_3&=-8b(z_b^3-21z_b^2-9z_b+29),\\
 a_4&=(1-z_b)^2(z_b^2+22z_b+25).
\end{aligned}
\]
With \(\eta=-8(z_b+3)(1-z_b)(z_b+5)\), a Gram matrix in
\((1,d,d^2)\) is
\[
 M_4=\begin{pmatrix}
 a_0&a_1/2&\eta\\a_1/2&a_2-2\eta&a_3/2\\\eta&a_3/2&a_4
 \end{pmatrix}.
\]
Its leading minors in coordinate order \((1,d^2,d)\) are
\[
 64(z_b+3)^2,\quad768z_b(1-z_b)^2(z_b+3)^2,\quad
 -4096z_b(1-z_b)^4(z_b+3)^2(z_b^2-2z_b-5),             \tag{90.5}
\]
all positive on \(0<z_b<1\). Thus \(Q_4\), \(d^2+4\), and \(V_0\)
have no real zeros on the domain.

Here are the ascending \(d\)-coefficients of the remaining literal
quintic \(Q_5\). They fix the normalization in (90.4).

```text
q0: -8192*b^3*(b^2 - 3)*(b^2 + 3)*(2*b^4 + 9*b^2 - 27)
q1: 512*b^2*(9*b^12 + 86*b^10 + 215*b^8 - 564*b^6 - 4401*b^4 + 7614*b^2 + 2673)
q2: 32*b*(9*b^14 - 329*b^12 - 3335*b^10 + 8559*b^8 + 72195*b^6 - 100179*b^4 - 95877*b^2 - 8019)
q3: -16*(27*b^16 - 416*b^14 - 3906*b^12 + 10260*b^10 + 60296*b^8 - 77256*b^6 - 173718*b^4 - 21996*b^2 - 2187)
q4: 2*b*(9*b^16 - 1024*b^14 - 6256*b^12 + 19608*b^10 + 108898*b^8 - 101552*b^6 - 586392*b^4 - 56040*b^2 - 16227)
q5: (9*b^8 + 28*b^6 - 170*b^4 - 612*b^2 + 2025)*(2*b^10 + 33*b^8 + 90*b^6 + 4*b^2 - 1)
```

At \(d=0\), remove the common factor \(\theta(\theta+1)\) from
\(\Phi,\Psi\). The resultant of the remaining cofactors, in this order,
is
\[
 r_0=4718592b^4(b^2-3)^3(b^2+3)(2b^4+9b^2-27),
\]
which is nonzero on the puncture. The only common \(\theta\) values
are therefore 0 or \(-1\), both incompatible with \(K_a>0\).

At \(d=2b\), remove \(\theta+b^2\). With the explicit reverse order
\(\operatorname{Res}_{\theta}(\Psi/(\theta+b^2),
\Phi/(\theta+b^2))\), the cofactor resultant is
\[
\begin{aligned}
 r_2={}&12582912b^{11}(b^2-3)^3(b^2+1)(b^2+4)^2
          (b^6+11b^4+4b^2+12)\\
 &\cdot(9b^{14}+181b^{12}+140b^{10}-4254b^8+1537b^6
               +30305b^4-58758b^2+24696).             \tag{90.6}
\end{aligned}
\]
It is nonzero at \(b=1/2\). Every zero of \(r_2\) is retained in the
guard. Away from those zeros, the only common \(\theta=-b^2\) gives
\(K_a=0\), again impossible. No assertion that \(r_2\) has no punctured
roots is used. Thus every physical finite aligned ray off this guard
has \(Q_5(b,d)=0\).

### 90.3. A completely reconstructible rational quintic lift

The degree-one subresultant of the ordered pair \((\Psi,\Phi)\) is
\[
 S_1=6d^2b^4(b^2-3)^2[V(b,d)\theta-U(b,d)].            \tag{90.7}
\]
The following determinant definition fixes every sign and coefficient
without a stored polynomial list. Form the eight coefficient rows
\[
 \theta^2\Psi,\ \theta\Psi,\ \Psi,\quad
 \theta^4\Phi,\ \theta^3\Phi,\ \theta^2\Phi,\ \theta\Phi,\ \Phi
\]
in the nine columns \(\theta^8,\theta^7,\ldots,1\). Let \(L\) be
the determinant using the first eight columns, and \(C\) the determinant
using the first seven columns and the final constant column. Set
\[
 W=6d^2b^4(b^2-3)^2,\qquad V=L/W,\qquad U=-C/W.        \tag{90.8}
\]
Both quotients are integer polynomials. They have \(d\)-degrees
13 and 14, \(b\)-degree 27, and respectively 173 and 186 terms.
The determinant expansion gives a polynomial combination of \(\Phi\)
and \(\Psi\), so every common root annihilates (90.7), without assuming
that the specialized subresultant degrees remain unchanged.

The leading quintic coefficient is
\[
 \ell=(9b^8+28b^6-170b^4-612b^2+2025)
             (2b^{10}+33b^8+90b^6+4b^2-1).             \tag{90.9}
\]
Retain \(\ell\) and \(\operatorname{Res}_d(Q_5,V)\) in the guard.
The latter is nonzero at the half parameter by §90.4. At a physical
point outside the guard, \(d\ne0\) and (90.7) gives uniquely
\(\theta=U/V\). The exact characteristic-zero divisions are
\[
 Q_5\mid V^4\Phi(b,d,U/V),\qquad
 Q_5\mid V^6\Psi(b,d,U/V).                            \tag{90.10}
\]
The homogeneous expressions have 2717 and 6076 terms. Direct division
using (90.1),(90.3),(90.8) and the printed quintic gives zero remainders;
the integer quotient term counts are 2088 and 5112. This reconstructs
both identities without omitted data.

Conversely every real quintic root passing the retained units and
\(K_a=d^2+4U/V>0\), with each sign \(s=\pm\sqrt{K_a}\), reconstructs
an original ray by
\[
 u=(s+d)/2,\quad v=(s-d)/2,\quad
 z=(1+iu)/(1-iu),\quad r=(1+iv)/(1-iv),\quad
 g=s(A_a+iC_a)/\kappa.                                \tag{90.11}
\]
Use all three repeated-pair positions. The two signs form the dephased
\(\Theta\) pair. Constant-channel subcases such as \(u=0\) or \(v=0\)
are retained. The complete pole analysis of §75 puts every actual Cayley
pole on the zero set of the second factor in (90.9), so every such fibre
is explicitly retained in the guard. No pole is lost by a finite-chart
division, and the quintic degree alone asserts no physical root count.

### 90.4. Exact half bridge and the mixed multiplication determinant

At \(b=1/2\), the printed \(Q_5\) is \(1/131072\) times the
quintic of §77. Exact univariate division in that quintic algebra gives
\(U/V=\tau(d)\) of (77.5); the two Cramer values coincide with
\(A(d,\tau),C_a(d,\tau)\) from (77.3). These are equalities of rational
algebra elements, not comparisons of approximate roots.

Over \(K=\mathbb Q(i)(b)\), construct the free ten-dimensional algebra
\[
 \mathcal B=K[d,s]/(Q_5,s^2-K_a(d)),\qquad
 \theta=U/V,\quad K_a(d)=d^2+4U/V,                    \tag{90.12}
\]
using the monic quintic and basis
\((1,d,\ldots,d^4,s,sd,\ldots,sd^4)\).
Its construction needs no irreducibility or real-root assumption.
The exact multiplication norms in the degree-five half quotient, modulo
97 with \(i=22\), are
\[
\begin{aligned}
 &\operatorname{Nm}(d)=76,\quad\operatorname{Nm}(V)=74,
 \quad\operatorname{Nm}(K_a)=51,\quad\operatorname{Nm}(J_a)=83,\\
 &\operatorname{Nm}(F_a)=90,\quad
 \operatorname{Nm}((2-id)^2+K_a)=15,\quad
 \operatorname{Nm}((2+id)^2+K_a)=36.                  \tag{90.13}
\end{aligned}
\]
Each is the determinant of the actual reduced multiplication matrix in
\(1,d,\ldots,d^4\). In particular the residue for \(V\) is 74 with
this norm convention. The last two certify the phase denominators in
\(\mathcal B\). All these norms and all scalar denominators are included
in the guard below.

In \(\mathcal A\otimes_K\mathcal B\), use the scaled aligned phase
\(H=s(A_a+iC_a)\) and phases
\[
 z=\frac{2+i(s+d)}{2-i(s+d)},\qquad
 r=\frac{2+i(s-d)}{2-i(s-d)}.
\]
The original lower phase is \(H/\kappa\). With \(E=\bar e\), put
\[
\begin{aligned}
 A_m&=(z-1)/E+(H/R)(r-1)\bar C/E,\\
 B_m&=-3(z-1)/E+(H/R)(r-1)(\bar D-3\bar C/E),\\
 C_m&=3z+3\bar GH/R+(H/R)(r-1)(\bar G+2\bar C-\bar D),\\
 C_Z&=\begin{pmatrix}0&0&E/q\\1&0&-3E\\0&1&3\end{pmatrix},
 \qquad N_m=\det(A_mC_Z^2+B_mC_Z+C_mI_3).
\end{aligned}                                                    \tag{90.14}
\]
The derivation of (79.13) is symbolic in \(R\), so it applies verbatim:
for the generic normalized upper root \(Z\) at the singleton position,
the ordinary mixed overlap divided by \(\sqrt q\) is
\(A_mZ^2+B_mZ+C_m\). The companion determinant is its product over
all three relative positions. Thus any actual mixed orthogonal pair
annihilates \(N_m\). Both signs of \(s\), all six generic orders and
all optional \(\Theta\) choices are retained.

Let \(h_m(b)\) be the full multiplication determinant of \(N_m\) in
basis \(s^\epsilon Y^id^j\), indexed by \(100\epsilon+5i+j\),
\(\epsilon=0,1\), \(0\le i<20\), \(0\le j<5\).
The exact half bridges identify this with the already reconstructed
matrix (79.15), giving
\[
 h_m(1/2)=57\pmod{97}.                               \tag{90.15}
\]
Therefore \(h_m\) is a nonzero rational function. Its numerator,
denominator and coefficient-conjugates are retained in the guard.
Where that guard is nonzero, multiplication by \(N_m\) is invertible,
so \(N_m\) cannot vanish at any pair of complex evaluations, and in
particular at any physical mixed pair.

### 90.5. Complete final guard and mixed theorem

Define \(H_*(b)\) by the following finite exact construction, with the
same reduced numerator/denominator and conjugation convention as §89.3:

1. Include the full \(G_*(b)\) construction and all its required scalars.
2. Include \(b,1-b^2,1+b^2,R,r_0,r_2,\ell\), and
   \(\operatorname{Res}_d(Q_5,dV)\) as required nonzero scalars.
3. In the monic degree-five quotient construct \(U/V,A_a,C_a,K_a,J_a,F_a\)
   and the two phase-norm denominators. Compute inverses by multiplication
   adjugates, and include every inverted element's norm as well as all
   seven norms in (90.13).
4. Construct (90.12), the fixed tensor basis, (90.14), and the full
   multiplication determinant \(h_m\). Include \(h_m\) as a required
   nonzero scalar and retain the reduced denominator of every scalar entry
   produced in these finite operations.
5. Multiply the nonconstant reduced denominators, the numerators of all
   required nonzero scalars, and their coefficient-conjugates. Clear
   rational constant denominators and take the primitive integer part
   with positive leading coefficient.

Every factor is nonzero and regular/nonzero at \(b=1/2\), by the exact
half bridges, the printed norms and minors, and the displayed exceptional
polynomials. Consequently \(H_*\in\mathbb Q[b]\) is nonzero,
\(H_*(1/2)\ne0\), and its real zero set is finite. These rules specify
the polynomial exactly by finite operations on public data, rather than
by an unspecified genericity condition. No zero of \(H_*\) is discarded.

**Theorem 90.1.** For every \(0<|b|<1\) with \(H_*(b)\ne0\), every
original noncanonical aligned ray is covered by (90.11), with all repeated
positions and signs, and no such ray is orthogonal to any original
noncanonical generic ray.

The aligned coverage follows from the original Cramer argument, complete
resultant strata and the rational shape identity. Generic coverage,
including the original \(F_8=0\) obligation, is already complete under
\(G_*\ne0\) by §89.4. Every mixed edge would annihilate \(N_m\),
contradicting its invertible multiplication matrix. This proves the theorem
without a numerical census or a presumption that candidate rays share an
orbit union. The finite guard fibres, including all actual aligned poles,
remain unresolved by this statement.

## 91. Complete basis classification outside the explicit finite set

### 91.1. The finite-exception theorem

Let \(H_*(b)\) be the exact nonzero polynomial specified in §90.5, and
put
\[
 \mathcal E=\{b\in\mathbb R:0<|b|<1,\ H_*(b)=0\}.     \tag{91.1}
\]
This is a finite algebraic set, defined by public coefficient arrays and
finite determinant, resultant and denominator rules. It is not a numerical
list of suspected exceptions. No assertion that it is empty or minimal is
made; a guard zero need not correspond to an actual extra ray or basis.

Let \(C(b)\) be the unit-entry canonical **input** matrix of §§62,67:
\(C(b)^*C(b)=6I_6\), \(|M(b)C(b)|^2=6\) entrywise, where
\(M(b)=\sqrt6H_0(b)\).

**Theorem 91.1.** For every \(0<|b|<1\) outside \(\mathcal E\):

1. There are no three mutually orthogonal noncanonical common-flat rays.
2. Every complete common-flat input basis is \(C(b)/\sqrt6\), up to
   column phases and permutation.
3. The fixed pair \((I_6,H_0(b))\) has exactly one common-unbiased basis
   up to column phases and permutation, namely
   \(H_0(b)C(b)/\sqrt6\), and cannot belong to a quartet of mutually
   unbiased bases.

This covers the actual punctured parameter branch outside a finite,
explicitly specified exceptional set. It is not a theorem at all of its
exceptional fibres, the center or the endpoints, nor a classification of
all six-dimensional Hadamard pairs.

### 91.2. Exhausting every ray and every triple type

The complete original chart reduction in §75 divides every noncanonical
ray on the puncture into two types, retaining its finite choices:

- Aligned: both channels have at most two distinct values and share a
  repeated pair, including a constant channel when present. Every repeated
  position, finite chart and actual Cayley pole is retained.
- Generic: after at most the optional \(\Theta\) channel interchange,
  the selected channel has three distinct values and satisfies the full
  strict original chart (87.3), with all six root orders.

The zero-channel-mean and unaligned-two-value exclusions are proved parts
of this coverage. Constant-channel cases are routed through the aligned
chart, rather than excluded wholesale. No intersection with a canonical
ray or covariance of a candidate basis is assumed.

At \(H_*\ne0\), §89.4 covers every original generic ray, including
all originally possible \(F_8=0\), pivot and line-coordinate strata.
Each generic orthogonal edge lies entirely in the \(S_3\)-\(\Theta\)
orbit union of either endpoint, by Theorem 89.1. The exact within-union
graph is bipartite, so no all-generic orthogonal triple exists.

Theorem 90.1 excludes all generic–aligned edges at the same parameter.
The uniform all-aligned theorem of §§83–85 excludes every all-aligned
noncanonical orthogonal triple, including rays from different orbit unions
and all poles. It does not assume that the entire aligned graph consists
only of its within-union edges.

Any noncanonical orthogonal triple is entirely generic, entirely aligned,
or contains both types. The first two cases are excluded by the preceding
triple results. The last case contains a forbidden mixed edge. This proves
assertion 1 and exhausts the complete original ray domain.

### 91.3. Arbitrary bases and the normalized MUB transport

Take any complete common-flat input basis. If it contains a canonical ray,
Proposition 60.1 identifies every common-flat ray orthogonal to that ray
with one of the other five canonical rays. Hence the whole basis is
canonical, up to column phases and permutation. If it contains no canonical
ray, any three of its six columns contradict assertion 1. Thus assertion 2
holds without assuming a canonical intersection in advance.

A unitary output matrix \(B\) is unbiased to \(I_6,H_0(b)\) exactly
when both \(B\) and \(H_0(b)^*B\) have entry moduli \(1/\sqrt6\).
Set \(W=H_0(b)^*B\). Then \(W\) is unitary and both \(W\) and
\(H_0(b)W=B\) are flat. It is precisely a common-flat input basis in
the convention above. Assertion 2 therefore gives
\[
 W=C(b)/\sqrt6,\qquad B=H_0(b)C(b)/\sqrt6              \tag{91.2}
\]
up to the same column phases and permutation. Conversely these canonical
identities give both required flatness conditions.

A quartet extending the fixed pair would supply two further common-unbiased
bases. Both would have the same column-ray set (91.2), so their relative
unitary would be monomial, with entry moduli zero or one. They could not
be mutually unbiased. This proves assertion 3 with the original input/output
normalization explicit.

### 91.4. Exact remaining boundary

No compactness or numerical radius is needed for Theorem 91.1. All zeros
of \(H_*\) are retained as unresolved fibres of this argument, including
possible coordinate, unit, chosen-minor and actual pole degeneracies.
The density of their complement does not settle them: an additional basis
could in principle exist at an isolated parameter. No limiting argument
here erases that possibility.

The delivered central and half-parameter neighborhood theorems remain
separate conclusions. At the center the canonical-basis uniqueness
assertion is false because the exact noncanonical completion exists;
its fixed-pair quartet exclusion is supplied by the independent ambient
pair-gap theorem. The present proof supplies a finite-exception extension
along the specified actual curve. Classification of the retained finite
fibres, or a division-free obstruction covering them, remains the route
to a whole-punctured-branch statement.
