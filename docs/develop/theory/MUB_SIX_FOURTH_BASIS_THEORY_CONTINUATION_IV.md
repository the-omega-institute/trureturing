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


## 92. Closing the two leading-coefficient fibres

### 92.1. Statement and exact parameter field

Use the original input convention and actual family of §§75,
87–91. Let

\[
\begin{aligned}
L(b)={}&2556b^{32}-71245b^{30}+763943b^{28}-4277291b^{26}
+14167798b^{24}-18831888b^{22}-32607612b^{20}\\
&+183118968b^{18}-105937551b^{16}-660151053b^{14}
+1236698199b^{12}-1481126067b^{10}+1141299072b^8\\
&-17045478b^6-207970578b^4-33657930b^2-1594323.
\end{aligned}
\]

The decic \(F(b,k)\) in §88 has leading coefficient \(3L(b)\).

**Theorem 92.1.** At every real \(b\) with \(0<|b|<1\) and
\(L(b)=0\), there is no noncanonical common-flat orthogonal triple.
Consequently the canonical complete common-flat input basis is unique up
to phases and permutations, and the fixed pair \((I_6,H_0(b))\) cannot
belong to a quartet. There are exactly two such parameters, \(b=\pm b_L\),
where \(559/625<b_L<1789/2000\).

Here is an exact irreducibility certificate. The monic reductions of \(L\)
have these factorizations:

```text
mod 5:
(b+1)(b-1)
(b^4-2b^2+b+1)(b^4-2b^2-b+1)
(b^22-2b^18+2b^14+b^12-2b^8-2b^6-2b^4-2b^2-2)

mod 7:
(b^14+2b^12+3b^10-b^8-b^4-3b^2-3)
(b^18-b^16-3b^14-b^12-3b^10+2b^8-3b^6-2b^4+3b^2+1)
```

Each factor passes the exact Rabin criterion: for a degree \(n\) factor
\(f\) over \(\mathbb F_p\), \(b^{p^n}=b\bmod f\), and
\(\gcd(f,b^{p^{n/q}}-b)=1\) for every prime divisor \(q\) of \(n\).
The possible proper factor degrees modulo 5 are

```text
1,2,4,5,6,8,9,10,22,23,24,26,27,28,30,31,
```

whereas modulo 7 they are 14 and 18. Their intersection is empty.
Gauss's lemma therefore proves irreducibility over \(\mathbb Q\).
The signs \(L(0)=-1594323\), \(L(1)=12779520\) give a real embedding of
\(\mathbb Q[b]/(L)\). This field cannot contain \(i\); adjoining \(i\)
has degree two, so \(L\) remains irreducible over \(\mathbb Q(i)\).

Ordinary exact Sturm division gives one root in \((0,1)\), and one in
\((559/625,1789/2000)\). Evenness gives the stated negative partner.
All subsequent operations may be performed in the characteristic-zero
field \(K_L=\mathbb Q(i)[b]/(L)\), without selecting an approximate root.

Two good residue maps used below are

\[
(p,b,i)=(97,9,22),\qquad (101,13,10).
\]

They satisfy \(L(b)=0\) and \(i^2=-1\) modulo the indicated prime; neither
prime divides the leading coefficient 2556. The second map is needed
only for three component resultants, which have rational coefficients.

**Specialization principle used throughout.** A finite computation in
\(K_L\), performed by polynomial multiplication and inverses expressed as
adjugates divided by determinants, is legitimate whenever each inverted
determinant has a nonzero residue at one of these good maps. Such a residue
proves nonvanishing in the characteristic-zero field. Consequently it
proves nonvanishing at every complex root of \(L\), with a fixed choice of
\(i\). This is an irreducible-number-field argument, not an inference that
a modular solution set equals a real solution set. Different polynomial
scalars may use different good maps.

### 92.2. Complete projective classification in the opposite chart

Write the physical scaled mean \(G=x+iy\), \(R=3-b^2\), and set

\[
 \ell=x/y,\qquad s=(x^2+y^2-R)/y.
\]

The old variables were \(k=y/x\), \(t=(x^2+y^2-R)/x\). Thus on the
overlap \(k=1/\ell, t=s/\ell\). For each primitive source curve
\(h(b,k,t)\) of degree \(n=8,10,10\) from §87, define

\[
 h^\vee(b,\ell,s)=\ell^n h(b,1/\ell,s/\ell).
\]

The homogeneous global identities in §87 make these necessary for every
original generic ray with \(y\ne0\), without assuming \(F_8\ne0\).
The global zero-mean exclusion guarantees \((x,y)\ne(0,0)\). The
opposite vertical test below excludes \(y=0\), so this chart is complete
at the roots of \(L\).

For a component \(P_j(b,k)\) of degree \(n_j\), put
\(P_j^\vee=\ell^{n_j}P_j(b,1/\ell)\). For the decic put

\[
 F^\vee=\ell^{10}F(b,1/\ell),\quad
 T^\vee=-\ell^9T(b,1/\ell),\quad D^\vee=\partial_\ell F^\vee.
\]

Its lift is \(s=T^\vee/D^\vee\). Indeed modulo \(F^\vee\),
\(D^\vee=-\ell^8F_k(b,1/\ell)\); on the generic overlap this gives
\(s=\ell t\). For each other component with old numerator \(N_j\) and
denominator \(D_j\), set

\[
 a_j=\max(\deg_kD_j,\deg_kN_j-1),\quad
 N_j^\vee=\ell^{a_j+1}N_j(b,1/\ell),\quad
 D_j^\vee=\ell^{a_j}D_j(b,1/\ell).
\]

The eighteen published component identities transport to these formulas.
One precise way to justify specialization, including the new point
\(\ell=0\), is to reduce each transformed identity by the monic
\(P_j^\vee\), with inverses of \(D_j^\vee\) formed by multiplication
adjugates. Over \(\mathbb Q(i)(b)\) it is zero by the overlap identity.
The following leading-coefficient and denominator witnesses show every
coefficient operation is regular in \(K_L\). The zero identity therefore
specializes there, without division by \(\ell\) at the exceptional point.

Use exactly the degree-19 Macaulay construction of §88, in variables
\((s,\ell)\). Its 210 columns are the pairs \((e_s,e_\ell)\) of total
degree at most 19, in descending order of \((e_s+e_\ell,-e_\ell)\).
Retain the 30 basis monomials of total degree at most 6, together with
\((1,6),(0,7)\). Use all source multiples in the printed source order and
in increasing multiplier \(e_s\), then increasing \(e_\ell\). Delete
row indices \(1,13,78,183,184,185,186,187\), with zero-based indexing.
The remaining 180-by-180 minor, on the nonbasis columns, is
\(65\bmod97\). The 18-by-18 opposite vertical Sylvester minor formed
from the first two source curves is \(28\bmod97\). Thus the affine
algebra has dimension at most 30 and there is no opposite vertical point.
As in §88, every border of the 30 proposed basis monomials is within the
represented degree range, so the finite matrix bound is an algebra bound.

Here are the component leading coefficients and denominator resultants,
in order \(j=0,\ldots,5\), modulo 97 at \(b=9\):

```text
(25,48), (65,51), (26,65), (22,61), (67,10), (1,50).
```

For the pairwise component resultants the residues modulo 97 are:

```text
01:33, 02:96, 03:22, 04:45, 05:50,
12:44, 13:35, 14:0, 15:0,
23:31, 24:72, 25:35, 34:25, 35:61, 45:0.
```

The three zero residues are replaced by the nonzero witnesses at
\((p,b)=(101,13)\): \(14:69, 15:68, 45:24\). They do not indicate
characteristic-zero collisions. Every component denominator is a unit,
every pair of components is coprime, and their degrees sum to 30. The
transported identities give a surjection onto their product. The dimension
upper bound therefore gives an isomorphism with this full product,
retaining the two nonreduced components just as in §88.

The homogeneous positivity proofs for the other five components exclude
all their real projective points. At \(\ell=0\) this uses their old
strictly positive leading coefficients; it is not an affine division by
\(\ell\). Thus every physical generic mean lies in the decic radial algebra

\[
 \mathcal A^\vee_L=K_L[\ell,Y]/\bigl(F^\vee,
 (1+\ell^2)Y^2-sY-R\bigr),\quad
 s=T^\vee/D^\vee,\quad x=\ell Y,\quad y=Y.             \tag{92.1}
\]

It is a free algebra of dimension 20. No physical root count is needed.

### 92.3. All original lifts and units

Construct \(G=x+iy\), the original affine-line coefficients
\(A,D_0,C_0,\sigma\), and the global arrays \(a_Y,\mu_Y,F_8\) from
§87. Then

\[
 \tau=-\mu_Y/a_Y,\quad
 u=(-AC_0-D_0\tau)/\sigma,\quad
 v=(-D_0C_0+A\tau)/\sigma.
\]

Construct \(C,D,Y_c,q,e,\bar e,\Delta,\delta\) by the original equations
of §§87,89. Here the original input coefficients remain
\(G/\kappa,C/\kappa,D/\kappa\), not the scaled quantities themselves.

The following are exact multiplication norms in algebra (92.1), modulo 97 at
\(b=9,i=22\). The derivative is that of the unnormalized \(F^\vee\).

```text
1+l^2:73; Fvee_l:81; radial discriminant:94; Y:24;
aY:1; \sigma:17; beta:89; barbeta:17;
C:16; barC:62; D:95; barD:12; Yc:44; barYc:23;
q:29; e:81; bare:37; F8:38; G:49; barG:94;
\Delta:47; \delta:65.
```

The radial discriminant is \(s^2+4R(1+\ell^2)\). The determinant of
the columns \(1,Y,\ldots,Y^{19}\) in the ordered basis
\((1,\ell,\ldots,\ell^9,Y,Y\ell,\ldots,Y\ell^9)\) is \(33\bmod97\).
Every division in this reconstruction is therefore valid over \(K_L\).
Direct finite-algebra multiplication also gives both parts of \(E=0\) and the two
original equations \(N_Y=N_D=0\) in the entire specialized algebra.
Those modular checks corroborate the transported characteristic-zero
identities; they are not their proof.

Necessity gives a point of algebra (92.1) before any \(F_8\) division. The nonzero
norm of \(F_8\) then proves it cannot vanish at that point. The complete
line-lift uniqueness and sufficiency of §87 now apply. This handles all
original leading and pivot strata noncircularly. Both channels are
three-distinct because the centered lower interpolation determinant
\(-\Delta\) is a unit. Every root order and phase gauge is retained.

### 92.4. Arbitrary generic pairs at these fibres

In algebra (92.1) the radial involution fixes \(\ell\) and sends

\[
 Y\longmapsto s/(1+\ell^2)-Y
       =-R/((1+\ell^2)Y),\qquad G\longmapsto-R/\bar G.
\]

It is defined at every point, including \(\ell=0\). The global
characteristic-zero identities identifying this with the normalized
\(\Theta\) action are those proved in §89. On the generic overlap the old
and new algebras are isomorphic under \(k=1/\ell, X=\ell Y\). The physical
coordinate \(Y=y\) is the same on both sides. All new construction
denominators are units above, so those identities extend to \(K_L\).
No claim that \(\ell\) itself is a unit at \(L=0\) is used.

Evaluate the same all-six-order overlap norm \(N\) of §§79,89 in
\(\mathcal A^\vee_L\otimes\mathcal A^\vee_L\), with the current \(R\).
Let \(\rho(a\otimes c)=a\iota(c)\). It is onto, so its kernel has dimension
380. The already proved field identity \(\rho(N)=0\) transports and
specializes by the unit argument above. Thus multiplication by \(N\)
has rank at most 380 in characteristic zero.

In the tensor basis \(Y^r\otimes Y^s\), indexed by \(20r+s\), the leading
380-by-380 principal minor has residue **17 modulo 97** at \(b=9,i=22\).
Its exact construction uses the same 508-term integer norm, without a
restriction on candidate relative order. Irreducibility of \(L\) proves
the minor nonzero in \(K_L\); hence the rank is exactly 380 and

\[
 N(\mathcal A^\vee_L\otimes\mathcal A^\vee_L)=\ker\rho.
\]

In particular \(1+\bar GG'/R\), which lies in \(\ker\rho\), belongs to
the principal ideal of \(N\). At an arbitrary physical orthogonal pair,
\(N=0\), so its means are orthogonal. Full lift uniqueness identifies the
second coefficient point with \(\iota\) of the first. Thus the second ray
is in \(S_3\Theta\) of the first, up to phase, with all six orders retained.
The uniform within-union graph theorem excludes an all-generic
noncanonical orthogonal triple. It is applied separately to the union
of each edge's endpoints, without a global single-union assumption.

### 92.5. Complete aligned coverage and mixed exclusion

Use the literal quintic \(Q_5\), Cramer formulas, shape polynomials \(U,V\),
and retained exceptional scalars of §90. Their construction is unchanged.
At \(b=9\bmod97\), the specialized quintic has degree five, and the
cofactor resultants \(r_0,r_2\), its leading coefficient and the actual
Cayley-pole factor are all nonzero. Their exact residues are respectively 27, 7, 13 and 53, reconstructed
from the literal formulas of §90. This proves their nonvanishing at all roots of \(L\), including
both real signs. The zero-angle, constant-channel and finite rank strata
remain covered by the uniform original analysis of §90. No actual pole
occurs on these fibres.

In the monic quintic algebra, the exact norm residues are

```text
d:38; V:39; K_a:60; J_a:88; F_a:58;
(2-id)^2+K_a:19; (2+id)^2+K_a:3.
```

Thus every finite aligned ray has the same rational shape lift
\(\theta=U/V\), with both signs of the square root of \(K_a\), all three
positions and all phase choices. Constant channels are included whenever
the original strict chart permits them.

Construct the mixed norm of §90.4 in the 200-dimensional algebra
\(\mathcal A^\vee_L\otimes K_L[d,S]/(Q_5,S^2-K_a)\), using the original
input normalization and basis \(S^\epsilon Y^id^j\) indexed by
\(100\epsilon+5i+j\). The full multiplication determinant has residue
**54 modulo 97**. All construction denominators have been certified above.
Hence multiplication is invertible over \(K_L\), and no physical
generic–aligned orthogonal pair exists at any real root of \(L\).

### 92.6. Consumer and retained boundary

All noncanonical rays are generic or aligned by §75, including
constant-channel aligned cases. An all-generic triple is excluded by §92.4;
an all-aligned triple by the uniform §§83–85 theorem; a mixed triple has
an edge excluded by §92.5. The canonical-intersection rigidity of §60 then
forces every complete common-flat input basis to be canonical. The exact
input/output transport \(W=H_0^*B\) of §91 proves the fixed-pair quartet
exclusion. None of these steps assumes a canonical intersection or cyclic
covariance of a candidate basis.

This closes the retained fibres \(L=0\). If \(H_*\) is the guard, one may remove its full \(L\)-primary factor and retain every other
factor: let \(v\) be maximal with \(L^v\mid H_*\), and put
\(H_{\rm new}=H_*/L^v\). At \(H_{\rm new}\ne0\), either \(L\ne0\) and
Theorem 91.1 applies, or \(L=0\) and the present proof applies.
No expanded computation of \(H_*\), no claim about the other fibres,
and no limiting argument across them is used. The center and endpoints
remain outside this basis-uniqueness statement.

## 93. Complete source algebras at six projection-collision fibres

### 93.1. Exact parameter field

Let \(P(B)=\sum_{j=0}^{98}p_jB^j\) be the primitive integer polynomial
whose complete ascending coefficient list is in §93.7. Put
\(Q(b)=P(b^2)\).

**Theorem 93.1.** For every real \(0<|b|<1\) with \(Q(b)=0\),
there is no original noncanonical common-flat orthogonal triple.
Every complete common-flat input basis is canonical up to phases and
permutation, and the fixed pair \((I_6,H_0(b))\) cannot belong to a quartet.
There are exactly six such parameters, three positive and their negatives.

The polynomial \(P\) has multiplicity exactly two in the discriminant of
\(\widetilde F(B,K)=b^{-6}F(b,bK)\), where \(B=b^2\) and \(F\) is the
literal decic in §88. The substitution is a polynomial identity.
Exact discriminant division verifies \(P^2\mid\operatorname{disc}_K
\widetilde F\) and \(P^3\nmid\operatorname{disc}_K\widetilde F\).
No numerical discriminant is used.

The monic reductions of \(P\) have irreducible factor degrees
\[
\begin{array}{c|c}
19&1,1,2,4,90\\
29&2,9,15,17,19,36\\
61&1,4,13,80.
\end{array}
\]
The following ascending coefficient arrays specify all monic factors.
For each prime, multiply its listed polynomials in \(B\); the result is
the monic reduction of \(P\).

~~~text
factor19_1: [6, 1]
factor19_2: [-7, 1]
factor19_3: [3, -5, 1]
factor19_4: [9, 6, 9, -9, 1]
factor19_5: [-5, -3, 9, 8, 2, 1, 8, 6, -7, 5, -2, -8, 6, -5, 0, 9, -4, 0, 6, -7, 3, 3, 2, 4, 7, -9, -6, 9, 1, -9, -8, 4, -4, -2, 4, 0, -2, 6, 8, -9, -2, 2, 2, 6, 2, 4, -8, -8, -5, -6, 1, -9, -1, 9, 5, -3, -7, -1, 3, -9, -3, -1, -7, -4, -8, 3, 6, -5, 7, 5, 0, 0, -6, 9, -4, -5, -8, -3, 3, 6, 0, -3, -1, -5, -9, 7, -1, -5, 0, -2, 1]
factor29_1: [-3, 7, 1]
factor29_2: [13, 2, -8, 1, 14, 9, 6, 1, 9, 1]
factor29_3: [-3, -11, 3, 2, -14, 4, 9, -2, 8, -2, -8, -4, 12, 6, 0, 1]
factor29_4: [-3, -1, -8, -14, 2, 13, -1, 11, -10, -10, 4, 4, -5, 6, 10, -1, 3, 1]
factor29_5: [3, 9, 4, 14, 2, -12, -13, -12, 11, 5, 9, -3, -3, 4, 7, -10, 9, 10, 2, 1]
factor29_6: [-13, 4, -9, 5, 10, 2, 8, -5, -1, -6, 6, -11, -1, 3, -7, -13, -10, 6, -3, 3, -2, 3, 5, -9, -7, 9, 4, 2, -4, 4, -7, 8, 13, -10, -5, -6, 1]
factor61_1: [-25, 1]
factor61_2: [22, 7, 11, 9, 1]
factor61_3: [-21, -11, 13, 4, -21, -25, 16, -3, 28, 28, 9, 23, -12, 1]
factor61_4: [-7, -21, -7, 9, -1, -27, -30, 7, -1, 26, -14, 26, -30, -14, 22, -11, 21, 16, -8, -14, 21, 22, 27, 19, -6, 15, 0, -11, -3, 23, 8, -26, -16, -2, -13, -13, -2, -20, 22, 5, -15, 26, -17, 19, 1, 7, 19, -6, 11, -15, 11, 6, 17, -27, 26, -14, -16, -29, -27, 21, -1, 8, -4, -3, -10, 18, 25, 24, -16, -5, 25, 7, 16, -27, 16, 10, -20, -24, -22, -6, 1]
~~~

Their products are as stated, and each factor satisfies the Rabin criterion: for a
degree \(n\) factor \(f\), \(B^{p^n}=B\bmod f\), and
\(\gcd(f,B^{p^{n/r}}-B)=1\) for each prime \(r\mid n\).
The proper subset-degree intersection for the first two rows is
\(\{2,96\}\), while the third allows neither. Hence \(P\) is irreducible.

For a root \(\beta\), its exact norm is
\[
 \operatorname{Nm}(\beta)
 =\frac{3736172995358363574201349399792269}{23265280}
 =\frac{3^{59}11\,13\,43^2}{2^{16}5\,71}.
\]
Its 5-adic valuation is \(-1\), so \(\beta\) cannot be a square in
\(\mathbb Q(\beta)\). Adjoining its square root has degree two. Thus
\(Q\) is irreducible of degree 196.
Exact Sturm division gives three roots of \(P\) in \((0,1)\), one in each
\[
\begin{split}
 &(282912/349561,\ 274537/339213),\\
 &(215864/248923,\ 158403/182662),\\
 &(508935/581954,\ 49319/56395).
\end{split}
\]
For reproducibility, use the Sturm sequence beginning with \(P,P'\),
replace each nonzero next term \(-\operatorname{rem}(A,B)\) by its
positive primitive integer multiple, and omit zero signs when counting
variations. Its endpoint variation counts are:

~~~text
0: 53
1: 50
282912/349561: 53
274537/339213: 52
215864/248923: 52
158403/182662: 51
508935/581954: 51
49319/56395: 50
~~~

Their positive and negative square roots are the six stated parameters.
In particular \(\mathbb Q[b]/(Q)\) has a real embedding, so it cannot
contain \(i\). Thus \(Q\) remains irreducible over \(\mathbb Q(i)\).
Work in \(K_Q=\mathbb Q(i)[b]/(Q)\).

The good residue map is \(b\mapsto5,\ i\mapsto11\) modulo 61:
\(P(25)=0\), \(11^2=-1\), and the leading coefficient of \(Q\) is nonzero.
A nonzero residue of any constructed scalar proves its nonvanishing in
\(K_Q\), hence at every complex root of \(Q\). Inverses are always formed
by adjugates and determinants, with all denominators certified below.
This irreducible-number-field argument does not identify a modular
solution set with the real solution set.

### 93.2. Full source algebra without dividing by a direction derivative

Use the three primitive source curves \(h_0,h_1,h_2\) of §87.5, of degrees
8,10,10 in \(k,t\). Use exactly the degree-19 monomial order, 30-element
basis \(\mathcal B\), 188 source multiples and selected 180 rows in §88.2.
The basis has total degree at most six, together with
\((e_t,e_k)=(1,6),(0,7)\), in inherited monomial order.
Let \(M\) be the selected matrix on the 180 nonbasis columns, and \(C\)
its 30 basis columns. The exact residues are
\[
 \det M=8,\qquad \det V_*=57\pmod{61}.
\]
The second is the original vertical 18-by-18 minor. It excludes physical
means with \(x=0\). Every other degree-at-most-19 monomial has its basis
expression from \(-M^{-1}C\); basis monomials have their standard vectors.
Define \(K,T\) by the expressions of the one-step \(k,t\) multiples
of every basis monomial. These borders all lie in the represented range.

Here is the characteristic-zero specialization justification. Over
\(\mathbb Q(i)(b)\), the source/CRT theorem makes \(K,T\)
the actual multiplication matrices. Therefore they commute,
\(h_j(K,T)=0\), and evaluation of each basis monomial on the constant
vector gives its standard basis vector. These are rational-function
identities whose construction denominators divide powers of \(\det M\)
and fixed scalar contents. They specialize to \(K_Q\) because \(\det M\)
is a unit. They provide a 30-dimensional algebra representation generated
by its constant vector. Conversely the same Macaulay border relations
bound the full quotient by 30. Hence
\[
 K_Q[k,t]/(h_0,h_1,h_2)
\]
is exactly this free 30-dimensional algebra. No old component derivative
is assumed invertible in this argument.

### 93.3. Generic component and a new primitive element

Let \(F=P_0\) be the old decic and \(P_{\rm other}=\prod_{j=1}^5P_j\)
the other five component polynomials. Their product annihilates \(K\),
by the same transported rational identity. Their degrees are 10 and 20,
and
\[
 \operatorname{Res}_k(F,P_{\rm other})=56\pmod{61}.
\]
Construct
\[
 e(k)=P_{\rm other}(k)[P_{\rm other}^{-1}\bmod F]
          \pmod{F P_{\rm other}},\qquad E=e(K).
\]
The identities \(E^2=E\), \(\operatorname{tr}E=10\) hold generically and
specialize by the resultant unit. In characteristic zero they imply
\(\operatorname{rank}E=10\).

Take the first ten columns \(J=E_{[:,0:10]}\), and their first ten rows
\(J_0\). One has \(\det J_0=15\bmod61\). Define
\[
\begin{split}
 K_g&=J_0^{-1}(KJ)_{[0:10,:]},\qquad
 T_g=J_0^{-1}(TJ)_{[0:10,:]},\\
 {\bf1}_g&=J_0^{-1}(E{\bf1})_{[0:10]}.
\end{split}
\]
The five other homogeneous components have no real projective points
on the entire puncture, by §88.3. Therefore every original generic
physical source point belongs to this image.

Put \(W=K_g+T_g\). The ten columns
\({\bf1}_g,W{\bf1}_g,\ldots,W^9{\bf1}_g\) have determinant \(56\bmod61\).
Thus \(W\) is a primitive element. Its characteristic polynomial has
residue
\[
 z^{10}-19z^9+16z^8-23z^7-12z^6-25z^5+
 6z^4+27z^3-22z^2+27z-2,
\]
with discriminant \(23\bmod61\). In particular the ten source points are
distinct in characteristic zero. Reconstruct \(k(z),t(z)\), each of
degree at most nine, by expressing \(K_g{\bf1}_g,T_g{\bf1}_g\) in these
power columns. This exact finite construction never divides by \(F_k\).
The repeated direction root is separated by the coordinate \(k+t\);
completeness follows from the full source algebra, not from that diagnostic.

### 93.4. Original generic reconstruction and all units

Form the twenty-dimensional free algebra
\[
 \mathcal A_Q=K_Q[z,X]/
 (f_W(z),\ (1+k(z)^2)X^2-t(z)X-R),\qquad R=3-b^2,
\]
and set \(x=X,\ y=k(z)X,\ G=x+iy\). Construct the original affine
line and \(a_Y,\mu_Y,F_8\) from §87. Then
\[
 \tau=-\mu_Y/a_Y,\quad
 u=(-AC_0-D_0\tau)/\sigma,\quad
 v=(-D_0C_0+A\tau)/\sigma.
\]
Construct \(C,D,Y_c,q,e,\bar e,\Delta,\delta\) by the original formulas.
The physical unscaled input coefficients are
\(G/\kappa,C/\kappa,D/\kappa\).

The exact multiplication norm residues modulo 61 are:

~~~text
1+k^2:57; fW_prime:41; radial discriminant:22; y:49;
aY:57; sigma:35; beta:1; barbeta:10;
C:55; barC:59; D:55; barD:40; Yc:41; barYc:41;
q:5; e:39; bare:56; F8:4; G:39; barG:45;
Delta:47; delta:48.
~~~

The radial discriminant is \(t^2+4R(1+k^2)\). The determinant of
\(1,y,\ldots,y^{19}\) in the ordered basis
\((1,z,\ldots,z^9,X,Xz,\ldots,Xz^9)\) is \(17\bmod61\).
All reconstruction divisions are therefore regular at every root of \(Q\).

Over the generic parameter field this source representation is the same
source/decic algebra as §89. Its original-equation identities consequently
transport to the new finite arrays and specialize through the certified
denominators. Direct finite-algebra multiplication also gives both parts of
\(E=0\), and \(N_Y=N_D=0\), as exact corroboration.

For necessity, the division-free §87 theorem first puts every original
generic mean into the full source quotient. Positivity removes the other
five components, so its mean lies in \(\mathcal A_Q\) before any \(F_8\)
division. The norm \(4\bmod61\) proves \(F_8\ne0\) there. The complete
line reconstruction and strict physical filters then cover all original
leading and pivot strata and all six root orders. The unit \(\Delta\)
ensures both channels are three-distinct; optional \(\Theta\) chart
interchanges lose no rays.

### 93.5. Generic pair rigidity and mixed exclusion

The radial involution fixes \(z,k,t\) and sends
\[
 X\longmapsto t/(1+k^2)-X,\qquad G\longmapsto-R/\bar G.
\]
The full normalized \(\Theta\) identities of §89 hold generically and
specialize through the new source construction. They require no unit
assumption on the old derivative \(F_k\).

Use the complete all-six-order overlap norm \(N\) from §§79,89. For
\(\rho(a\otimes c)=a\iota(c)\), the transported identity \(\rho(N)=0\)
bounds multiplication rank by 380. The map is onto a twenty-dimensional
algebra, so its kernel has dimension 380. In basis \(y^r\otimes y^s\),
indexed by \(20r+s\), the leading 380-by-380 principal minor is
**52 modulo 61**. The equivalent row order with seven swaps
\[
 (22,23),(36,37),(57,58),(140,141),(163,164),(194,195),(361,362)
\]
has residue 9. Thus the ranks agree in characteristic zero and the image
ideal is \(\ker\rho\). Every arbitrary physical orthogonal generic pair
has orthogonal mean spinors. Full lift uniqueness places its second ray
in \(S_3\Theta\) of the first, up to phase. The uniform
within-union bipartite theorem excludes all-generic noncanonical triples.

For aligned rays use the complete original §90 quintic construction.
The scalar cofactor resultants \(r_0,r_2\), leading quintic coefficient,
and actual Cayley-pole factor are nonzero polynomials of degree less than
196. Irreducibility of \(Q\) proves none vanishes at its roots; their residues are respectively 9, 45, 43 and 3 at the good map. All constant-channel, finite rank
and pole cases of §90 are therefore retained.
The aligned norm residues are:

~~~text
d:44; V:35; K_a:11; J_a:22; F_a:49;
(2-id)^2+K_a:43; (2+id)^2+K_a:11.
~~~

Construct the §90.4 mixed norm in the 200-dimensional tensor algebra,
using both signs of the aligned square root, all three repeated
positions, all generic orders and the original input normalization.
Its full multiplication determinant is **41 modulo 61**. Hence it is
invertible in characteristic zero and excludes every original
generic–aligned orthogonal edge.

### 93.6. Consumer and exact boundary

The complete §75 charts include all noncanonical rays. All-generic triples
are excluded above; all-aligned triples by uniform §§83–85; every mixed
triple has a forbidden mixed edge. A complete common-flat basis containing
a canonical ray is canonical by §60. A basis containing none contradicts
the triple obstruction. The exact \(W=H_0^*B\) transport of §91 gives
the output-basis uniqueness and fixed-pair quartet exclusion.

No ray census or numerical continuation is used. This closes only the six
specified fibres of \(Q\). Every other retained guard fibre, remains outside this section. The four simple-discriminant fibres are
handled separately in §94.
The center and endpoints are not included.

### 93.7. Complete parameter coefficients

The following ascending integer list defines \(P(B)=\sum_{j=0}^{98}p_jB^j\).

~~~text
p0: 351735202430630662916120520249352697119088463
p1: 18992614092931372111896364933620398108043516849
p2: 477812092482784278653722215769569783638490690591
p3: 7278223791495749967518822745209219963466617216544
p4: 74184182071568229611924405809794004696086089309553
p5: 534016659498625590276166272382849278790287333033621
p6: 2786905716668020644073379466243600149852879202557499
p7: 10510398100149828410996392398744706841040023899048446
p8: 26943152967545408533686473566893766850425806013570503
p9: 31594159058944591917927803105986713102947606157230931
p10: -84522058659676565651705491991284720354378455059874573
p11: -531386513223936950763518699696239241318834073737203590
p12: -1055455940959683134625606960980697134825418639919130532
p13: 776508751933078151708979310815243357574262003700223836
p14: 8439962907305726954771773471660983871962718206636581352
p15: 11300827496376157014898160585885449787431061141280741690
p16: -30677225766147204979455834755208165575193187251258075765
p17: -110335916557678735165027423916252403654682304869837690491
p18: 92306974405526286756700313240587933506851312373321430107
p19: 485588029164550876304288522786632326879480854590413708138
p20: 464696693203125166138335446738405867092644285934700211687
p21: -4226903466330088245139621145153512065272786178930969194685
p22: 2029378756730194299908996341857469362240313155109228827177
p23: 7846396763394149416717939060074284509730924811961856366760
p24: 7038785951330854246339027897712816753563898590058883893079
p25: -5429722240181887194718142445886417729122304726558502730729
p26: -345541458497742312381837261025120763092369340611872833560437
p27: 1572950383327258321608868863863174252220626680734135211592028
p28: -4216139081729396532095184826131076242800903851028896561781088
p29: 10260872820446236566385706911068214035523106570068369398608928
p30: -25892760160841548414523649812673545024405262350848290465954576
p31: 59147383169338926589558446073182610987040174602677569254804296
p32: -107322566871319005514388909460815371236426733212052208540336034
p33: 145464057400172904684532581239278791091831063010502659016742722
p34: -137977249161313641833414844605176774746693459078435268969891650
p35: 72997593026901414425836314474237563741987759603817925959022728
p36: 16596553754688272845779441440702384262320069592958034848364154
p37: -76258806940440966258827970986641939990386524657774628513549534
p38: 76902715343128425099294332703035161817405706900379041898294446
p39: -35793404983755285291378682292686194460639061135689603838166972
p40: -7090325027813122266140303174025248195882315276276799388495746
p41: 25754724316666631843451612378487289645642612947092301464889734
p42: -21206710584882398842484096590971928309938362710103115544460682
p43: 8391558705012257928691304624773674775145590716907158049775004
p44: 920274670001660221181207772003076676955065200259766873220344
p45: -3921222408235388299349334556306615554270196350270573834957000
p46: 3107514720493938774458159911957286215600747223360335085052864
p47: -1417289205049654247474905130202722827066180896908177467030740
p48: 263809006507777195610212054878978168156235788823612872978798
p49: 188374049794198175613296579535661711598592092083529694124242
p50: -234103553654380802765149775925450233332812228618559359480498
p51: 150895762900423618759467175453423651939616835620372349173004
p52: -72782620818036994837337862423335129052856836377331039490818
p53: 29454648700462256224299468054022927815934409354195023727478
p54: -10881953791246859233450633360064065178600131192369087031886
p55: 3848688572135098340939359027427155585037685462115516848504
p56: -1248679407769293826500376002354101793233332968704692765866
p57: 320258075720483010634037733546334356369130567405779135750
p58: -42297909360835891711792504124532127191525994019521803138
p59: -10268777935132090664805096123449158044571427054309484192
p60: 8295289260746321847359007138404516870236060926564842304
p61: -2583579708783376447170497464730214038022984978088146048
p62: 376508966899447076067614534281451507035279628243266896
p63: 42761772564783204761346678452635823316694631467863144
p64: -39546225514096756030068821028758320941663400001306157
p65: 10485935402033101566101945149549912703634260036405901
p66: -1041362625157945603367196666513400824671262281416797
p67: -238645958227819289608160847646410690772863089795448
p68: 113360764724004460655755698115970546348691761935173
p69: -17979810988890637947384848956385274378047676238023
p70: -298085032170848690294152143784120666641361534905
p71: 711141156811351075580437894149030475300155468846
p72: -135227433007582444784305701086420246493457663461
p73: 5016165925669039049138165325530063530702209255
p74: 2666247417292302544029269947519644011901751095
p75: -570578839359689165617436817137890354752558310
p76: 33604607462520006440629278299932857482958028
p77: 6265172795965241201768346885270869964756620
p78: -1575907691402194295957251934169832682404008
p79: 129999410035496942602251264568695628930282
p80: 4395282640298078667412746335013089681799
p81: -2170565501067014900202217925481812551127
p82: 203990878849878006447089864192124164055
p83: 281006209797824569196600603149797466
p84: -2058631232434401599933007168632616469
p85: 216384948050030793309174116410390615
p86: -5248735778057663119367032990264075
p87: -1066538782235109635917542423277200
p88: 130008579954066342055904640984819
p89: -4873433854716832872135939451101
p90: -277790551010338782545484956073
p91: 44476500690189262332348075540
p92: -2328471351813890844181979136
p93: 23068170527298051972532032
p94: 4868006586427309347944640
p95: -368218365442945200145152
p96: 13427343533044623025152
p97: -262686200569147330560
p98: 2190267415500226560
~~~

## 94. Four nonreduced discriminant fibres

### 94.1. Statement and exact parameter field

Let \(P(B)=\sum_{j=0}^{48}p_jB^j\) be the primitive integer polynomial
in §94.6, and put \(Q(b)=P(b^2)\).

**Theorem 94.1.** At every real \(0<|b|<1\) with \(Q(b)=0\),
there is no noncanonical common-flat orthogonal triple. Every complete
common-flat input basis is canonical up to phases and permutations,
and the fixed pair \((I_6,H_0(b))\) cannot belong to a quartet.
There are exactly four such parameters.

With the exact decic \(F(b,k)\) of §88, define
\(\widetilde F(B,K)=b^{-6}F(b,bK)\), \(B=b^2\).
This is a polynomial identity. Exact rational discriminant division gives
\[
 P\mid\operatorname{disc}_K\widetilde F,\qquad
 P^2\nmid\operatorname{disc}_K\widetilde F.
\]
The monic factorizations of \(P\) have degrees
\[
\begin{array}{c|l}
7&4,4,5,5,7,7,8,8\\
11&2,6,6,17,17\\
13&5,5,14,24\\
17&16,16,16.
\end{array}
\]
The following ascending coefficient arrays specify all monic factors.
For each prime, multiply its listed polynomials in \(B\); the result is
the monic reduction of \(P\).

~~~text
factor7_1: [-1, -1, 1, -2, 1]
factor7_2: [1, 1, -2, -2, 1]
factor7_3: [-2, -2, 0, 3, 1, 1]
factor7_4: [3, -3, -3, -3, -1, 1]
factor7_5: [-3, -1, -2, -1, -3, -2, 2, 1]
factor7_6: [-3, 1, 0, 2, -1, 2, -3, 1]
factor7_7: [3, -3, -3, 1, 1, -2, 0, 0, 1]
factor7_8: [3, 3, 1, 0, 3, 0, 2, 2, 1]
factor11_1: [4, 1, 1]
factor11_2: [5, 2, -1, 0, 4, 4, 1]
factor11_3: [1, -1, -2, 5, 3, 5, 1]
factor11_4: [-3, -1, 2, -2, -1, 5, 4, -3, 0, 4, 5, 3, -2, 3, -1, -2, 1, 1]
factor11_5: [4, -1, 0, 3, -2, 3, 0, 5, -2, -1, -5, -2, 0, -4, -4, 0, 4, 1]
factor13_1: [2, -1, -6, 2, 3, 1]
factor13_2: [3, 0, -6, 4, -4, 1]
factor13_3: [3, 3, -3, 4, -6, 1, -2, 3, -6, 0, 0, 3, -5, 3, 1]
factor13_4: [-6, 1, 5, 2, 3, 4, -2, 5, 5, 1, 0, -4, 5, -3, 5, -5, 3, 6, 2, 2, 1, 4, -1, -6, 1]
factor17_1: [2, -7, -1, 4, -3, -7, 5, 3, -5, 5, -6, -7, -4, -1, -8, 7, 1]
factor17_2: [6, 7, -8, 2, 8, -8, -1, -4, -7, 4, 5, -5, -2, 8, -4, -7, 1]
factor17_3: [-2, -4, 3, -2, 2, -5, 0, 2, 6, 8, 1, 6, -7, -6, -6, -2, 1]
~~~

Every factor satisfies the exact Rabin power and gcd conditions of §92.1. The proper subset-degree intersections
after the first three rows are \(\{14,19,29,34\}\); the final row permits
only 16 and 32. Hence \(P\) is irreducible over \(\mathbb Q\).

The norm of a root \(\beta\) is
\[
 \operatorname{Nm}(\beta)=-7625597484987/61063168<0.
\]
A square in \(\mathbb Q(\beta)\) has square, hence nonnegative, rational
norm. Thus \(\beta\) is not a square, and \(Q\) is irreducible of degree 96.
Exact primitive integer Sturm division gives two roots of \(P\) in
\((0,1)\), one in each interval
\[
 (22911/28745,\ 435902/546899),\qquad
 (158289/188234,\ 150101/178497).
\]
For reproducibility, use the Sturm sequence beginning with \(P,P'\),
replace each nonzero next term \(-\operatorname{rem}(A,B)\) by its
positive primitive integer multiple, and omit zero signs when counting
variations. Its endpoint variation counts are:

~~~text
0: 26
1: 24
22911/28745: 26
435902/546899: 25
158289/188234: 25
150101/178497: 24
~~~

Their signed square roots give the four parameters. The real embedding
of \(\mathbb Q[b]/(Q)\) excludes \(i\), so \(Q\) remains irreducible over
\(\mathbb Q(i)\). Work in \(K_Q=\mathbb Q(i)[b]/(Q)\).

The good residue map is \((p,b,i)=(113,25,15)\).
It has \(P(25^2)=0\), \(15^2=-1\), and nonzero leading coefficient.
All nonzero residues below certify nonzero elements of \(K_Q\), hence
nonvanishing at every root of \(Q\). Inverses are defined by adjugates and
determinants. This is characteristic-zero number-field certification,
not an identification of modular and real solution sets.

### 94.2. Complete source algebra before taking its reduced quotient

Use the original primitive \(h_0,h_1,h_2\), degree-19 monomial order,
30 basis monomials and 180 selected rows of §88.2. In particular
the basis consists of total degree at most six and \((e_t,e_k)=(1,6),(0,7)\).
The nonbasis matrix \(M\) and original vertical minor have residues
\[
 \det M=67,\qquad \det V_*=101\pmod{113}.
\]
The latter excludes \(x=0\) in the physical mean \(G=x+iy\).
Form the exact border multiplication matrices \(K,T\) from
\(-M^{-1}C\), where \(C\) is the selected basis-column block.

Over \(\mathbb Q(i)(b)\) these are the actual quotient matrices by §88.
Commutation, all three source identities, and the cyclic constant-vector
identities are therefore rational identities whose denominators divide
powers of \(\det M\) and fixed scalar contents. They specialize in \(K_Q\).
Together with the same border upper bound, they identify
\[
 K_Q[k,t]/(h_0,h_1,h_2)
\]
with a free algebra of dimension 30. This argument does not invert \(F_k\)
or discard nilpotents.

Let \(P_{\rm other}=\prod_{j=1}^5P_j\), with the five other §88 components.
The exact residue
\(\operatorname{Res}_k(F,P_{\rm other})=17\)
makes the generic projector
\[
 E=e(K),\qquad
 e=P_{\rm other}(P_{\rm other}^{-1}\bmod F)\bmod(FP_{\rm other})
\]
regular. Its transported identities \(E^2=E,\operatorname{tr}E=10\)
give a ten-dimensional image in characteristic zero. Set
\(J=E_{[:,0:10]}\), \(J_0=J_{[0:10,:]}\); then
\(\det J_0=9\bmod113\). Restrict \(K,T\) and the constant vector using
\(J_0^{-1}\), exactly as for any invariant direct summand.
The five other homogeneous components have no real projective points
on the puncture by the uniform positivity proof.

The ten power columns of the restricted \(K\) on the constant vector have
determinant \(2\bmod113\). Hence \(k\) itself is primitive in this full
ten-dimensional source algebra. Its characteristic polynomial is
\[
 f(k)=F(b,k)/\operatorname{lc}_kF.
\]
The leading coefficient has residue 93. The polynomial expression
\(t=t(k)\) of degree at most nine is obtained from those same power columns;
it is not the singular formula \(T/F_k\).

Now \(f\) has zero discriminant in \(K_Q\). Its first subresultant
with \(f'\) has nonzero linear coefficient: at the good map the
subresultant sequence degrees are \(10,9,\ldots,1\), with final polynomial
\[
 -51k-55.
\]
The zeroth subresultant is zero by the exact discriminant factor.
Thus \(\gcd(f,f')\) is exactly the monic linear polynomial \(g\) obtained
by normalizing the first subresultant. Put \(f_{\rm red}=f/g\).
It is squarefree of degree nine, and \(g\mid f_{\rm red}\).
The good residues are
\[
\begin{split}
g&=k-10,\\
f_{\rm red}&=k^9+3k^8+56k^7-14k^6+38k^5-31k^4
+48k^3-51k^2+45k+26,\\
\operatorname{disc}(f_{\rm red})&=31.
\end{split}
\]
The full source component \(K_Q[k]/(f)\) has exactly one double factor.
Its quotient by \((f_{\rm red})\) is the reduced nine-dimensional algebra,
and the quotient kernel is square-zero because \(f\mid f_{\rm red}^2\).
Every field-valued physical source point factors through this quotient.
No physical point is removed by deleting nilpotents.

### 94.3. Original reconstruction through the nonreduced model

Put \(R=3-b^2\). First form the full free radial algebra
\[
 \mathcal A_{\rm full}=
 K_Q[k,X]/(f,\ (1+k^2)X^2-t(k)X-R).
\]
It has dimension twenty. Then form its quotient
\[
 \mathcal A_{\rm red}=
 K_Q[k,X]/(f_{\rm red},\ (1+k^2)X^2-t(k)X-R),              \tag{94.1}
\]
of dimension eighteen. The quotient kernel is square-zero.
The unit \(1+k^2\) is certified below; the radial discriminant also is a
unit, so (94.1) is reduced. Necessity places every original generic mean
in (94.1) before any lift denominator is used.

Set \(x=X,y=kX,G=x+iy\). Construct the original affine-line coefficients
\(A,D_0,C_0,\sigma=A^2+D_0^2\) and the global linear coefficients
\(a_Y,\mu_Y,a_D,\mu_D,F_8\) of §87. Use the valid combined pivot
\[
 \tau=-\frac{\mu_Y+\mu_D}{a_Y+a_D},\qquad
 u=\frac{-AC_0-D_0\tau}{\sigma},\quad
 v=\frac{-D_0C_0+A\tau}{\sigma}.                            \tag{94.2}
\]
Both individual linear equations hold generically, so (94.2) agrees there
with their unique original lift. Construct \(C,D,Y_c,q,e,\bar e,\Delta,\delta\)
by the original formulas. Physical input coefficients are
\(G/\kappa,C/\kappa,D/\kappa\).

The multiplication norms in (94.1), in basis
\((1,k,\ldots,k^8,X,Xk,\ldots,Xk^8)\), have residues:

~~~text
1+k^2:88; f_red_prime:57; radial discriminant:109; y:34;
aY+aD:67; sigma:40; beta:88; barbeta:107;
C:75; barC:40; D:43; barD:45; Yc:80; barYc:18;
q:48; e:71; bare:44; F8:69; G:23; barG:74;
Delta:7; delta:31.
~~~

The radial discriminant is \(t^2+4R(1+k^2)\).
The power columns \(1,y,\ldots,y^{17}\) have determinant \(72\bmod113\).

Here the order of the specialization argument matters. A unit modulo a
nilpotent ideal lifts to a unit, by a finite geometric-series inverse.
Consequently every original reconstruction denominator certified in (94.1)
is also a unit in \(\mathcal A_{\rm full}\). The generic source construction
and all original rational identities therefore specialize first to that
full twenty-dimensional algebra, with its double source point retained.
Only afterward are they passed to (94.1). We do not attempt to treat the
nine-dimensional quotient as a flat generic-parameter family.

In particular both parts of \(E=0\) and \(N_Y=N_D=0\) are characteristic-zero
identities in (94.1); direct finite-algebra multiplication gives the same equalities.
The nonzero F8 norm is proved only after universal necessity has placed
every original generic source point in this algebra. It therefore gives
noncircular F8 coverage, including all original leading and pivot zeros.
The complete line uniqueness and original strict reconstruction filters
retain all six root orders. The unit \(\Delta\) ensures both channels are
three-distinct. No physical ray count is asserted.

### 94.4. Arbitrary generic pairs and all mixed edges

The radial involution fixes \(k,t(k)\) and sends
\[
 X\longmapsto t/(1+k^2)-X,\qquad G\longmapsto-R/\bar G.
\]
It preserves the square-zero ideal and descends to (94.1). The complete
normalized Theta identities specialize first in the full algebra by the
preceding unit argument, and then descend to (94.1).

Evaluate the all-six-order generic overlap norm \(N\) of §§79,89 in
\(\mathcal A_{\rm red}\otimes\mathcal A_{\rm red}\).
For the onto map \(\rho(a\otimes c)=a\iota(c)\), the transported identity
\(\rho(N)=0\) bounds multiplication rank by \(18^2-18=306\).
In the power basis \(y^r\otimes y^s\), indexed by \(18r+s\),
the leading 306-by-306 principal minor has residue **66 modulo 113**.
Hence in characteristic zero the image ideal of \(N\) equals \(\ker\rho\).
Every original orthogonal generic pair has orthogonal mean spinors;
full lift uniqueness then places its second ray in \(S_3\Theta\) of the
first, with all six relative orders retained. The uniform
within-union bipartite theorem excludes all-generic noncanonical triples.

Use the complete original aligned quintic and shape lift of §90.
At the same good map the scalar cofactor resultants \(r_0,r_2\), quintic
leading coefficient and actual pole factor have residues respectively
\[
 96,\quad1,\quad26,\quad15.
\]
Thus all their exceptional charts are resolved by nonvanishing at every
root of \(Q\). All finite rank, constant-channel and phase cases remain
covered by the original aligned classification. Its norm residues are

~~~text
d:78; V:35; K_a:5; J_a:68; F_a:112;
(2-id)^2+K_a:1; (2+id)^2+K_a:64.
~~~

The complete mixed norm of §90.4 in the 180-dimensional algebra
\[
 \mathcal A_{\rm red}\otimes K_Q[d,S]/(Q_5,S^2-K_a)
\]
has full multiplication determinant **77 modulo 113**.
The construction retains both signs of \(S\), every aligned position,
all generic orders and the original input normalization. It is a unit
in characteristic zero, so no generic–aligned orthogonal edge exists.

### 94.5. Consumer and retained boundary

The complete §75 charts cover every noncanonical ray, including an aligned
constant channel whenever present. All-generic triples are excluded above,
all-aligned triples by uniform §§83–85, and a mixed triple contains an
excluded mixed edge. A common-flat basis containing a canonical ray is
canonical by §60; a basis without one would contain a forbidden triple.
The exact input/output transport \(W=H_0^*B\) of §91 gives the fixed-pair
quartet exclusion.

The conclusion concerns only the four real punctured roots of the exact
degree-96 polynomial \(Q\). Other retained guard fibres, the center and
the endpoints are not covered by this argument. No density or continuity
claim removes those remaining exceptions.

The three sections give a combined strict improvement of the finite guard
without changing the statement or proof of §91. Write
\[
 Q_{98}(b)=P_{93}(b^2),\qquad Q_{48}(b)=P_{94}(b^2),
\]
where \(P_{93}\) and \(P_{94}\) are the complete polynomials in §§93.7
and 94.6. The irreducible polynomials \(L,Q_{98},Q_{48}\) have distinct
degrees 32,196,96, so they are pairwise coprime. Their punctured real
root sets are disjoint and have total cardinality \(2+6+4=12\).

Let \(v_L,v_{98},v_{48}\) be the maximal nonnegative integers for which
the corresponding powers divide the explicitly constructed \(H_*\) of
§91. Each exponent is positive: the guard explicitly retains the leading
coefficient of \(F\), and its component denominator resultant
\(\operatorname{Res}_k(F,F_k)\) retains both discriminant factors
certified in §§93–94. Define the exact nonzero polynomial
\[
 H_{\mathrm{reduced}}=
 \frac{H_*}{L^{v_L}Q_{98}^{v_{98}}Q_{48}^{v_{48}}}.        \tag{94.3}
\]
For every \(0<|b|<1\) with \(H_{\mathrm{reduced}}(b)\ne0\), there is no
noncanonical common-flat orthogonal triple, the complete common-flat
basis is canonical, and \((I_6,H_0(b))\) cannot belong to a quartet.
Indeed, away from the three displayed factors §91 applies; on any of
them the corresponding section above applies. Maximality and irreducibility
also show that \(H_{\mathrm{reduced}}\) is nonzero at every root of
these three factors, so all twelve certified parameters are included.
This argument neither
expands \(H_*\) nor assumes that these twelve points exhaust its real
zeros. All zeros of the remaining guard are retained as unresolved by
this finite-fibre extension.


### 94.6. Complete parameter coefficients

The following ascending list defines \(P(B)=\sum_{j=0}^{48}p_jB^j\).

~~~text
p0: -50031545098999707
p1: -1967907440560655142
p2: -33456279509719989255
p3: -301498120520723925693
p4: -1463497638517823881986
p5: -2842513135519665642813
p6: 5692717288525141989099
p7: 36589455340777231215570
p8: 21762698312972135675367
p9: -178739814881410046948331
p10: -254585219538017926833678
p11: 647018721835747647704325
p12: 1077193076743510212442392
p13: -2216443016806157505345156
p14: -3015635507141450791581684
p15: 10012672505287398099743784
p16: -5075165694944134501363710
p17: -15126770622773260231809120
p18: 37246334237072319750027030
p19: -45619964323819998132689730
p20: 36121996471456960970616612
p21: -17138614154213214785467638
p22: 513859329122638713237450
p23: 7601757127695087990619356
p24: -8188905195779219571337794
p25: 5305519440750917005431246
p26: -2330939948168124115585272
p27: 595784481517924741024362
p28: 57619738525082168808216
p29: -176801266151477947316916
p30: 137410119283541814839772
p31: -87761817841153999484664
p32: 53088924176420394790377
p33: -29261413111933204128978
p34: 14004202234782367091401
p35: -5692353997091298926705
p36: 1948693609285148229006
p37: -584470856448333487285
p38: 170678490043698619235
p39: -49480435047363174366
p40: 11763828717714746123
p41: -1641452215054120843
p42: -19052657704172754
p43: 54673375345148929
p44: -9089238344520416
p45: 328753841930784
p46: 78014475053568
p47: -10390332513024
p48: 400635445248
~~~


## 95. Four channel-collision fibres: a 19-point lift and two parity norms

### 95.1. Statement and exact parameter field

Put
\[
\begin{split}
Q(b)={}&36b^{16}+1153b^{14}-8163b^{12}+20457b^{10}-106407b^8\\
       &+440883b^6-628641b^4+299619b^2-24057.
\end{split}
\]
**Theorem 95.1.** For every real \(0<|b|<1\) with \(Q(b)=0\),
there is no orthogonal triple of noncanonical original common-flat rays.
Every common-flat input basis is the canonical basis up to phases and
permutations. The fixed pair \((I_6,H_0(b))\) cannot belong to a quartet.
There are exactly four parameters in this statement.

Write \(Q(b)=P(b^2)\). The monic reduction of \(P\) modulo 7 is
\[
 B^8-2B^7-B^6+3B^5+2B^3+B^2-2B+2.
\]
Rabin's test gives \(B^{7^8}=B\) and
\(\gcd(P,B^{7^4}-B)=1\), so \(P\) is irreducible over \(\mathbb Q\).
The norm of its root is \(-24057/36<0\). A square has nonnegative
rational norm, so this root is not a square in its degree-eight field.
Thus \(Q\) is irreducible of degree sixteen. Exact Sturm division gives
two positive roots in \((0,1)\), one in each rational interval
\[
\frac{(315813416603,315813418603)}{10^{12}},\qquad
\frac{(897459468779,897459470779)}{10^{12}}.
\]
For the signed Sturm sequence beginning with \(Q,Q'\), replacing each
negative remainder by its positive primitive integer multiple and omitting
zero signs, the variation counts are

~~~text
0: 8
1: 6
315813416603/10^12: 8
315813418603/10^12: 7
897459468779/10^12: 7
897459470779/10^12: 6
~~~

Their negatives are the other two roots in the puncture. The real
embedding excludes \(i\), so \(Q\) is irreducible over \(\mathbb Q(i)\).
All algebra below is over \(K=\mathbb Q(i)[b]/(Q)\).

Use the good reduction \((p,b,i)=(137,66,37)\). Every rational field
coefficient is reduced only after its denominator is checked nonzero.
A nonzero residue proves a nonzero element of \(K\), hence nonvanishing
at every complex embedding and all four real fibres. Matrix residues
below certify characteristic-zero units or rank lower bounds; no modular
solution count is identified with a real solution count.

### 95.2. The complete source and full radial algebra

Use the primitive source \(h_0,h_1,h_2\), degree-19 monomial order,
30 basis monomials, and fixed 180-row border minor of §88.2.
The source minor and vertical minor have residues 80 and 64. The border
matrices therefore specialize without losing a source point; the vertical
minor excludes \(x=0\) for the physical scaled mean \(G=x+iy\).
As in §93, the characteristic-zero rational commutation, source-identity,
and cyclic-vector identities specialize before any lift denominator is
inverted. Together with the border upper bound they give the full
30-dimensional source quotient over \(K\).

Project onto the decic component using the five complementary factors
of §88. The projector resultant is 13. Its first ten columns restricted
to its first ten rows have determinant 13. This gives the complete
ten-dimensional generic source summand. The other five components have
no real projective points on the puncture by the positivity
argument. No F8 hypothesis is used in this source coverage.

The element \(w=k+t\) is primitive in this summand: the ten power columns
on the constant vector have determinant 6. Let \(f_W\) be its monic
characteristic polynomial and obtain \(k=k(w),t=t(w)\) by the same power
basis. This defines them over \(K\), not merely modulo 137. Set
\[
\mathcal A_{20}=K[w,X]/\bigl(f_W(w),
 (1+k(w)^2)X^2-t(w)X-R\bigr),\qquad R=3-b^2.
\tag{95.1}
\]
The following are multiplication norms in (95.1), except the basis minor:

~~~text
1+k^2:101; f_W':50; t^2+4R(1+k^2):25;
y=kX:125; G=X+iy:79; barG=X-iy:91;
(1,y,...,y^19) basis determinant:27; disc(f_Y):75.
~~~

Thus (95.1) is a reduced algebra of dimension twenty, and \(y\) is primitive.
Let \(f_Y\) be its monic characteristic polynomial. Its good reduction is

~~~text
Y^20+61Y^19-48Y^18+42Y^17+12Y^16-44Y^15-28Y^14-21Y^13
-38Y^12-50Y^11+2Y^10+51Y^9+55Y^8-16Y^7-47Y^6-23Y^5
+66Y^4+38Y^3+42Y^2-3Y-12.
~~~

All field-valued original generic source points lie in (95.1), including
points where F8 or both linear lift pivots vanish.

### 95.3. Two exact mean points and the excluded linear F8 chart

The following rational polynomials define \(x_C,y_C\) in \(K\):
\[
\begin{split}
x_C={}&\frac{6227638877b^{14}}{2100947893920}
+\frac{7431822595793b^{12}}{75634124181120}
-\frac{7091765173453b^{10}}{12605687363520}
+\frac{2889816706213b^8}{2801263858560}\\
&-\frac{587361173209b^6}{77812884960}
+\frac{25936875770923b^4}{933754619520}
-\frac{2953352598239b^2}{155625769920}
-\frac{78990949899}{103750513280},\\
y_C={}&\frac{47902082597b^{15}}{6302843681760}
+\frac{56542077041273b^{13}}{226902372543360}
-\frac{57976598645773b^{11}}{37817062090560}
+\frac{26717818392413b^9}{8403791575680}\\
&-\frac{42467452612321b^7}{2100947893920}
+\frac{72865663112161b^5}{933754619520}
-\frac{35242166643919b^3}{466877309760}
+\frac{4306128200621b}{311251539840}.
\end{split}
\tag{95.2}
\]
Put \(h=x_C^2+y_C^2\), and define
\[
 (x_B,y_B)=-\frac R h(x_C,y_C).
\tag{95.3}
\]
Their good residues are \((22,42)\) and \((71,11)\), respectively.
Direct division by \(Q\) verifies that both are decic/radial source
points: for \(k=y/x,t=(x^2+y^2-R)/x\),
\(F(b,k)=0\) and \(T(b,k)=tF_k(b,k)\) with the exact §88 numerator.
The good residues are \(h=56,x_C=22,x_B=71,F_k=32\); thus
the denominators here, including \(F_k\), are nonzero. Therefore (95.2)
and (95.3) are points of (95.1). They are exchanged by the radial involution
\(X\mapsto t/(1+k^2)-X\).

Use the global original-coordinate system of §87. Let
\(\operatorname{Re}E_n/6=Au+D_0v+C_0\),
\(\sigma=A^2+D_0^2\), and use the division-free line coordinate
\[
 u=(-AC_0-D_0\tau)/\sigma,\qquad
 v=(-D_0C_0+A\tau)/\sigma.
\tag{95.4}
\]
The global imaginary equation is
\(Q_g=-8(b^2+3)F_8\tau^2+Q_1\tau+Q_0=0\).
Its two global linear necessary equations are
\(a_Y\tau+\mu_Y=a_D\tau+\mu_D=0\).

At the source point B, exact division by \(Q\) gives
\[
 F_8=a_Y=a_D=\mu_Y=\mu_D=0,\qquad Q_1\ne0,\quad\sigma\ne0.
\]
The original imaginary equation is genuinely linear. Its unique candidate
is \(\tau=-Q_0/Q_1\), with good residues
\[
 (\sigma,Q_1,Q_0,\tau)=(130,82,116,32).
\]
Substitute (95.4) into the original, cleared norm equations \(N_Y,N_D\)
from the quaternion/original-flatness system. Their exact field values
have residues 103 and 43, respectively. Both are nonzero. Thus B has no
original common-flat lift with three distinct entries in the selected upper
channel. This excludes it using original equations,
not by declaring F8 invertible or by deleting a source root.

At C the combined linear pivot is nonzero. Its unique lift (95.4), with
\(\tau=-(\mu_Y+\mu_D)/(a_Y+a_D)\), satisfies the original complex
\(E_n=0\) and both norm equations exactly in \(K\). At this lift
\(\Delta=D\bar D-C\bar C=0\). These are characteristic-zero polynomial
checks; existence of a strict physical lift is not needed in the argument.
C is retained throughout the complete coverage algebra.

### 95.4. Complete 19-dimensional lift and the auxiliary 18-dimensional algebra

Define
\[
 f_{19}(Y)=f_Y(Y)/(Y-y_B),\qquad
 \mathcal A_{19}=K[Y]/(f_{19}).
\tag{95.5}
\]
This quotient removes exactly B. It is reduced, and every original
strict generic ray in the selected three-distinct upper-channel chart
maps to (95.5). The other channel is allowed to be two-valued.

Reconstruct by (95.4) and the combined pivot, then by the original formulas
for \(G,C,D,Y_c,q,e,\bar e\). Physical input coefficients are
\(G/\kappa,C/\kappa,D/\kappa\), with \(|\kappa|^2=R\).
The complete unit inventory in (95.5) is

~~~text
aY+aD:36; sigma:42; beta:86; barbeta:61;
Yc*barYc:48; barC*D:46; C*barD:94;
y:111; C:59; barC:11; D:54; barD:55; Yc:99; barYc:42;
q:33; e:114; bare:87; F8:10; G:130; barG:14; delta:11.
~~~

Here \(\delta=q^2(3-4(e+\bar e))+6q-1\). The original complex and norm
identities hold on (95.5). All original strict inequalities and the six
upper-root orders are retained when selecting physical points. The norm
of \(\Delta\) is zero; it is never inverted on (95.5).

For clarity about specialization, let \(\mathcal O\) be the local ring
of \(\mathbb Q(i)[b]\) at \((Q)\), with the finitely many certified scalar
and source units inverted. The full source/radial construction is finite
free over \(\mathcal O\). Localizing it at the original lift denominators,
including \(a_Y+a_D\), is torsion-free over \(\mathcal O\).
Every original identity valid over the generic fraction field therefore
holds in this localization, and hence on its special fibre. That special
fibre is (95.5), because B is the only removed point and every denominator
above is a unit on (95.5). This proves the characteristic-zero original
identities on (95.5). It does not pretend that the odd-dimensional quotient
(95.5) is a finite flat generic-parameter family.

The exact point C has \(\Delta=0\); the good reduction satisfies
\(\gcd(f_{19},\Delta)=Y-42\). Subresultant rank gives degree at most one
in characteristic zero, while C gives degree at least one. Thus C is the
unique \(\Delta\)-zero of (95.5). For an auxiliary rank argument only, set
\[
 \mathcal A_{18}=K[Y]/\bigl(f_Y/((Y-y_B)(Y-y_C))\bigr).
\tag{95.6}
\]
It is reduced and is preserved by the radial involution \(\iota\), because
B and C are radial partners. All lift units and \(\Delta\) are units in
(95.6). The exact normalized Theta transport therefore holds in (95.6), by
localizing the full algebra also at the radial transforms of the lift
units. There is no Theta-invariance claim for (95.5).

### 95.5. Ordinary overlap: rank 343 with an 18-dimensional zero graph

Let \(\mathcal N\) be the universal 508-term polynomial defined by the
exact orbit-sum construction in §79.3. Evaluate the ordinary arguments
of (79.8) in \(\mathcal A_{19}\otimes\mathcal A_{19}\), obtaining \(N_O\).
Its factors are all six relative ordinary overlaps, up to a nonzero
normalizing factor. Let \(\pi:\mathcal A_{19}\to\mathcal A_{18}\).
The map
\[
 \rho:\mathcal A_{19}\otimes\mathcal A_{19}\to\mathcal A_{18},\qquad
 \rho(a\otimes c)=\pi(a)\iota(\pi(c))
\tag{95.7}
\]
is onto. The full normalized Theta identity on (95.6) gives \(\rho(N_O)=0\)
in characteristic zero, by the same faithful cubic-splitting argument as
§79. Its kernel has dimension \(19^2-18=343\).

In the ordered power tensor basis \(Y^r\otimes Y^s\), index \(19r+s\),
the leading principal 343-by-343 minor has determinant 9 modulo 137. Hence multiplication by \(N_O\)
has rank exactly 343 in characteristic zero, and
\[
 N_O(\mathcal A_{19}\otimes\mathcal A_{19})=\ker\rho.
\tag{95.8}
\]
The polynomial \(1+\bar GG'/R\) lies in this kernel. An original
orthogonal ordinary pair evaluates \(N_O\) to zero, hence every element
of (95.8) to zero. Its means are radial partners. More precisely, since the
ideal in (95.8) is the kernel of the surjection (95.7), that pair factors
through the graph (95.7); both points belong to (95.6). Unique original
reconstruction and all six root orders put the second ray in
\(S_3\Theta\) of the first. In particular C cannot acquire an ordinary
partner by using the excluded B point.

### 95.6. Symplectic overlap: a separate 19-dimensional diagonal kernel

This step retains C and avoids any inverse of \(\Delta\).
Write upper roots as \(Z_j=1+a\omega^j+b_1\omega^{-j}\) and
\(Z'_j=1+c\omega^j+d\omega^{-j}\). Let \(E=\bar e,E'=\bar e'\),
\(P=1-E,S=2-3E+E/q\), \(Q'=1-E',T=2-3E'+E'/q'\).
Thus \(ab_1=P\), \(a^3+b_1^3=S\), and similarly for \(c,d\).
The scaled lower values are
\(\mathcal L(Z)=G+C(Z-1)+D(\overline Z-1)\), with
\(\overline Z=(Z^2-3Z+3E)/E\).

For the bilinear overlap \(\sum_j(Z_j\mathcal L'(Z'_j)-
\mathcal L(Z_j)Z'_j)/3\), define
\[
 A_s=-D/E,\qquad B_s=C'-C-D'/E'+D/E,\qquad
 C_s=0,\qquad D_s=D'/E',\qquad m_s=G'-G.
\tag{95.9}
\]
Direct Fourier summation gives the three cyclic factors
\(m_s+\omega^jL_0+\omega^{-j}L_1\), where
\[
 L_0=A_sa^2c+B_sb_1c+D_sb_1d^2,\quad
 L_1=A_sb_1^2d+B_sad+D_sac^2.
\]
Exchanging \(c,d\) gives the other three factors. Consequently the same
universal polynomial evaluated at
\((A_s,B_s,0,D_s,m_s,P,S,Q',T)\) is an all-six-order symplectic norm
\(N_S\). The original bilinear overlap differs by the nonzero factor
\(3tt'/\kappa\), where \(t=\sqrt q,t'=\sqrt{q'}\).
These six identities follow by expanding the displayed Fourier sums for the six permutations; no cyclic covariance of the candidate rays is imposed.

Under the diagonal multiplication map
\[
 \mu:\mathcal A_{19}\otimes\mathcal A_{19}\to\mathcal A_{19},
 \qquad \mu(a\otimes c)=ac,
\]
(95.9) becomes \((-D/E,0,0,D/E,0,P,S,P,S)\). The universal integer identity
\[
 \mathcal N(-d_0,0,0,d_0,0,P,S,P,S)=0
\tag{95.10}
\]
proves \(\mu(N_S)=0\) over characteristic zero, without a Theta chart.
The kernel has dimension \(19^2-19=342\). The leading principal 342-by-342 minor has residue 35 modulo 137.
Thus
\[
 N_S(\mathcal A_{19}\otimes\mathcal A_{19})=\ker\mu.
\tag{95.11}
\]
An original symplectically orthogonal pair therefore has the same point
of (95.5), not merely a coincident projection. Unique lift reconstruction
implies its selected representatives differ only by a synchronous
permutation. After restoring the relative Theta parity, the actual
orthogonal endpoints again belong to the same \(S_3\)-Theta union.

Every generic ray is representable by this selected chart after a
possible Theta, by the complete single-ray coverage. Ordinary and
symplectic equations are selected by relative Theta parity; they are not
simultaneously imposed. Therefore every generic orthogonal edge at these
four parameters lies within the orbit union of either endpoint, including
all channel-collision rays. The uniform within-union bipartite
theorem now excludes all-generic noncanonical orthogonal triples.

### 95.7. All mixed pairs, aligned triples, and the basis conclusion

Use the complete aligned quintic and reconstruction of §90. At the good
map, its scalar exceptions have residues
\[
 (r_0,r_2,\operatorname{lc}F_{\rm al},\text{pole factor})=(45,95,79,100),
\]
and its five-dimensional unit norms are

~~~text
d:116; V:2; K:2; J:96; Fa:13; zden:84; rden:39.
~~~

Thus every original aligned chart, including constant channels and all
poles, is covered by the same exact shape at these four parameters.
Form the full generic/aligned ordinary norm of §79.5 in the
\(19\times5\times2=190\)-dimensional algebra. Its determinant is
97 modulo 137 and hence nonzero in \(K\). No selected generic ray is
ordinary-orthogonal to an aligned ray at any position. The aligned set is
Theta-stable. Moving relative Theta parity onto the aligned endpoint
therefore excludes symplectic mixed edges as well, without requiring
Theta-stability of (95.5).

An arbitrary noncanonical triple is either all generic, mixed, or all
aligned. The first case was excluded above, the second contains an
excluded mixed edge, and the third is excluded uniformly by delivered
§85, including constant channels, poles and both parameter signs.
An arbitrary common-flat basis containing a canonical ray is canonical
by §60. A basis containing no canonical ray would contain a forbidden
noncanonical triple. This proves basis uniqueness at the four roots.

Finally, if output rays are flat and unbiased to columns of \(H_0(b)\),
then \(w=H_0(b)^*v\) is a common-flat input ray, and inner products are
preserved. Two output bases extending \((I_6,H_0(b))\) would transport to
two common-flat input bases. Both would be the same canonical basis up
to phases and permutations, so could not be mutually unbiased. Hence the
specified fixed pair cannot belong to a quartet.

### 95.8. Verification boundary

The parameter, two exceptional source points and their original equations
are checked directly over the degree-sixteen characteristic-zero field.
The complete source, original lift and Theta identities specialize from
the earlier characteristic-zero identities through the explicitly
stated torsion-free localizations. The finite residue calculations only
certify the required units and rank lower bounds. The two distinct
rank-upper identities are proved separately in (95.7) and (95.10).

Every calculation is reconstructible from the source border construction,
the original equations, the two displayed field points and the specified
multiplication norms. In particular the two 361-dimensional norm matrices
and the 190-dimensional mixed matrix require no external data file.
Neither a twenty-point Theta-stable physical census nor an F8-unit
assumption is made. All other parameter fibres, including remaining
zeros of the finite guard, retain their previously stated status.


## 96. Four aligned-coordinate exceptional fibres

### 96.1. Statement and parameter fields

Define
\[
\begin{split}
Q_{10}(b)&=2b^{10}+33b^8+90b^6+4b^2-1,\\
Q_{14}(b)&=9b^{14}+181b^{12}+140b^{10}-4254b^8+1537b^6
 +30305b^4-58758b^2+24696.
\end{split}
\tag{96.1}
\]
**Theorem 96.1.** For every real \(0<|b|<1\) satisfying
\(Q_{10}(b)Q_{14}(b)=0\), there is no orthogonal triple of noncanonical
original common-flat rays. The canonical input basis is the only
common-flat basis up to phases and permutations, and the fixed pair
\((I_6,H_0(b))\) cannot belong to a quartet. There are exactly four
parameters in this statement, two roots of each polynomial.

Writing \(Q_{10}=P_5(b^2)\), \(Q_{14}=P_7(b^2)\), the monic reductions
of \(P_5\) modulo 3 and \(P_7\) modulo 19 are respectively
\[
 B^5-B+1,\qquad B^7-B^6+5B^5-4B^4+4B^3+B+8.
\]
Both are irreducible. The exact
Rabin certificates check the Frobenius powers \(3^5,19^7\), respectively,
and the degree-one Frobenius gcds. The norm of the root of \(P_5\) is
\(1/2\), which is not a rational square. The norm of the root of \(P_7\)
is \(-2744\), also not a rational square. Therefore those roots are
not squares in their respective fields, and the even polynomials in
(96.1) are irreducible of degrees ten and fourteen over \(\mathbb Q\).
Both fields have real embeddings, so they remain irreducible over
\(\mathbb Q(i)\).

The polynomial \(P_5\) is strictly increasing on \([0,1]\), and its
unique zero lies in \((3/20,4/25)\). Exact Sturm division gives precisely
one positive punctured root of \(Q_{14}\), in
\[
 (6110/7847,\ 63003/80914).
\]
Using the signed primitive Sturm convention of §95.1, the variation
counts for Q14 at 0, 1, 6110/7847 and 63003/80914 are 7, 6, 7 and 6.
Evenness gives the two signed roots of each polynomial, and their gcd
is one. Work separately over \(K_j=\mathbb Q(i)[b]/(Q_j)\).
The good maps are
\[
 (p,b,i)=(137,64,37)\quad(j=10),\qquad
 (p,b,i)=(149,10,44)\quad(j=14).
\tag{96.2}
\]
Every nonzero residue below certifies a nonzero element of its irreducible
characteristic-zero field, hence nonvanishing at both real embeddings in
the puncture. The matrices and norms are defined over these fields by
original formulas and adjugate inverses, not by interpolation from a prime.

### 96.2. Complete generic coefficient algebras at both fields

Use the source \(h_0,h_1,h_2\), its fixed 180-row border minor and vertical
minor of §88.2. The complete source construction of §§92–94
is applied afresh at each field. The residues are

~~~text
                   Q10 / mod137   Q14 / mod149
source minor             62            130
vertical minor          102            103
projector resultant      67            116
generic basis minor      88             11
w=k+t power basis        82             57
~~~

For the projector restriction, take its first ten columns. The invertible
row set is \(0,\ldots,9\) over \(K_{10}\) and
\(0,\ldots,8,10\) over \(K_{14}\); these define the basis minors 88 and 11.
The restricted multiplication matrices and constant vector are obtained
by the inverse of those submatrices. Thus every entry in the table has
a fixed rational reconstruction from the earlier source definitions.

The source rational identities specialize through these units and give
the complete 30-dimensional source algebra. The generic decic projector
has dimension ten; the other five components are uniformly nonreal on
the puncture. The vertical minor excludes \(x=0\). No original F8-zero
case is discarded in placing a physical point in the source algebra.

Let \(f_W\) be the characteristic polynomial of \(w=k+t\) in the
projected summand. Obtain \(k(w),t(w)\) from its power columns and form
\[
 \mathcal A_j=K_j[w,X]/(f_W(w),
 (1+k(w)^2)X^2-t(w)X-R),\quad R=3-b^2.
\tag{96.3}
\]
It has dimension twenty. Put \(x=X,y=kX,G=x+iy\). The original global
line and combined-pivot reconstruction is
\[
 \tau=-(\mu_Y+\mu_D)/(a_Y+a_D),\quad
 u=(-AC_0-D_0\tau)/\sigma,\quad
 v=(-D_0C_0+A\tau)/\sigma,
\]
where \(\operatorname{Re}E_n/6=Au+D_0v+C_0\) and
\(\sigma=A^2+D_0^2\). Construct the original scaled \(C,D,Y_c,q,e\)
as in §87. Physical input coefficients are \(G/\kappa,C/\kappa,D/\kappa\),
with \(|\kappa|^2=R\).

The full multiplication norms, and the final basis determinant, are:

~~~text
name                  Q10 / mod137   Q14 / mod149
aY+aD                       26            138
sigma                       65             58
beta                        53            147
barbeta                     21             49
Yc*barYc                     1             46
barC*D                      17             31
C*barD                      93              4
1+k^2                       28             20
f_W'                        30            140
radial discriminant        100            144
y                           27             57
C                           18             59
barC                       107             21
D                            4            115
barD                        28             43
Yc                          12             63
barYc                       80            145
q                           74             61
e                           41            127
bare                        48            148
F8                          69             49
G                           90            111
barG                        82             13
Delta                      119            102
delta                      100              7
y-power basis              100             28
~~~

Here the radial discriminant is \(t^2+4R(1+k^2)\),
\(\Delta=D\bar D-C\bar C\), and
\(\delta=q^2[3-4(e+\bar e)]+6q-1\).
All entries are nonzero. Thus (96.3) is reduced, y is primitive, and the
original reconstruction and exact normalized Theta identities specialize
in the full twenty-dimensional algebra. This follows by first forming
the finite free source/radial algebra over the local ring at \((Q_j)\),
then inverting the listed units. Characteristic-zero rational identities
valid over the generic fraction field persist in this torsion-free
localization. Direct finite-algebra substitution also verifies the original complex and
norm equations at both good maps.

Universal original necessity puts every strict selected-channel generic
ray in (96.3) before F8 is tested. Its nonzero norm therefore excludes all
F8-zero possibilities noncircularly at these fields. All strict filters,
all six root orders and both optional Theta choices remain retained.

The radial involution is
\(\iota(X)=t/(1+k^2)-X\), so \(\iota(G)=-R/\bar G\).
For the ordinary all-six-order overlap norm N of §79, the onto map
\(\rho(a\otimes c)=a\iota(c)\) gives \(\rho(N)=0\) in characteristic
zero by the normalized Theta identity and faithful cubic splitting.
Its kernel has dimension \(400-20=380\). The leading principal
380-by-380 minors, in basis \(y^r\otimes y^s\) indexed by \(20r+s\),
are respectively 65 modulo 137 and 26 modulo 149. Hence
\[
 N(\mathcal A_j\otimes\mathcal A_j)=\ker\rho.
\tag{96.4}
\]
Every generic orthogonal edge belongs to the synchronous S3–Theta union
of either endpoint. The exact uniform within-union graph is bipartite,
so there is no all-generic noncanonical orthogonal triple at these fields.
The full generic set is Theta-stable, by the original reconstruction and
unit \(\Delta\). This also permits moving a relative Theta onto an
aligned endpoint in the mixed-pair argument below.

### 96.3. The two genuine Cayley-pole fibres Q10=0

Use the original aligned finite chart with coordinates D,T, the quartic
and sextic original equations F,N of §90, and the exact projection
factorization and subresultant \(V T-U\) from that section.
At Q10=0, the leading D coefficient of the quintic Q5 vanishes, while
its D-degree is exactly four. Its degree-four coefficient has residue 72.
Let \(f_4\) be its monic normalization in \(K_{10}[D]\).

The two exceptional finite cofactor resultants \(r_0,r_2\) have residues
97 and 25. Thus D=0 and D=2b remain impossible for a physical finite
nonconstant ray. The other projection factors are uniformly positive
on the puncture by §90. Every such ray therefore maps to \(f_4=0\). The complete original finite
chart here includes a constant channel whenever present; only the
both-constant canonical case is outside the noncanonical classification.
The original lift is still \(T=U/V\), with unit norms

~~~text
D:6; V:23; K=D^2+4T:5; J=bD-T+3:94;
Fa=D^2+(T+1)^2:101; zden:42; rden:55.
~~~

Here zden and rden are \((2-iD)^2+K\) and \((2+iD)^2+K\).
The monic quartic discriminant is 61 modulo 137.
The global polynomial divisibilities
\(Q_5\mid V^4F(D,U/V)\) and \(Q_5\mid V^6N(D,U/V)\)
are identities in \(\mathbb Q[b,D]\); they specialize even though the
quintic leading coefficient vanishes. They give the original finite
reconstruction on this quartic, without pretending that a degree-four
quotient is the original finite flat degree-five family.

For both signs \(s^2=K\), put
\[
 u=(s+D)/2,\quad v=(s-D)/2,\quad
 z=\frac{1+iu}{1-iu},\quad r=\frac{1+iv}{1-iv},\quad
 h=s(a+ic),
\tag{96.5}
\]
where \(a,c\) are the original Cramer functions. This retains both
Theta-related rays at all three unique positions. Their generic/finite
mixed norm in \(\mathcal A_{10}\otimes K_{10}[D,s]/(f_4,s^2-K)\)
has dimension 160 and full multiplication determinant 101 modulo 137.
Therefore no generic ray is orthogonal to a finite aligned ray.

The complete original pole classification of §75 gives exactly the
following two dephased rays, at each unique position:
\[
\begin{split}
 q_p&=\frac{b(5b^4+12b^2-1)}{1-b^4},\qquad
 p_p=bq_p+3b^2+1,\qquad h_p=p_p+iq_p,\\
 (z,r,h)&=\left(-1,\frac{1+ib}{1-ib},h_p\right),\qquad
 \left(\frac{1-ib}{1+ib},-1,-h_p\right).
\end{split}
\tag{96.6}
\]
The actual input is \((1,1,z;h/\kappa,h/\kappa,hr/\kappa)\).
The original pole equations hold exactly, and
\[
 p_p^2+q_p^2-R=\frac{2Q_{10}}{(b^2-1)^2(b^2+1)}.
\]
The second ray in (96.6) is the dephased Theta partner. All other Cayley-pole
strata were excluded in the original uniform pole classification, including
the double pole and the finite v≠b alternative.

For each triple (z,r,h), set H=h/R and E=bar e in \(\mathcal A_{10}\),
and form the quadratic polynomial in a generic upper root Z:
\[
\begin{split}
 A_m&=(z-1)/E+H(r-1)\bar C/E,\\
 B_m&=-3(z-1)/E+H(r-1)(\bar D-3\bar C/E),\\
 C_m&=3z+3H\bar G+H(r-1)(\bar G+2\bar C-\bar D).
\end{split}
\tag{96.7}
\]
In the positive upper-mean gauge, its value is the original overlap divided by \(\sqrt q\), which is nonzero by the original zero-channel lemma.
The determinant of multiplication by \(A_mZ^2+B_mZ+C_m\) in
\(Z^3-3Z^2+3EZ-E/q=0\) is the product over all three relative positions.
Its multiplication norm in \(\mathcal A_{10}\) has residues 24 and 13
for the two rays (96.6). Both are nonzero, so every pole mixed edge is
excluded, in both relative Theta parities.

### 96.4. The two D=2b cofactor-resultant fibres Q14=0

At Q14=0 the original quintic has the exact factor D−2b, since
\[
 Q_5(b,2b)=64b^5(b^2-1)(b^2+1)Q_{14}(b).
\tag{96.8}
\]
Its leading coefficient has residue 27 and is nonzero. Define
\(f_4=Q_5/(D-2b)\), normalized to be monic in \(K_{14}[D]\).
The second exact identity
\[
 V(b,2b)=524288b^5(b^2-3)(b^2+1)(b^2+4)^2
 (b^6+11b^4+4b^2+12)Q_{14}(b)                         \tag{96.8a}
\]
shows that V vanishes at D=2b. Its norm on this quartic quotient is
nonzero, so D=2b cannot also be a root of the quotient. Thus D=2b is
not a repeated root of Q5. At D=0 the cofactor resultant remains nonzero, with residue
122. The Cayley-pole factor Q10 has residue 67, so there are no poles here.
Every finite nonconstant ray with D≠2b maps to this quartic, with norms

~~~text
D:101; V:91; K:114; J:49; Fa:49; zden:83; rden:72.
~~~

The original polynomial identities give both directions of its finite
reconstruction (96.5). The full 160-dimensional mixed determinant is 86
modulo 149, excluding all mixed edges to these rays.

It remains essential to retain D=2b rather than divide it out. Define
\[
\begin{split}
 T_0={}&-\frac{3611b^{12}}{2460416}
 -\frac{264835b^{10}}{11071872}
 +\frac{90905b^8}{1581696}
 +\frac{97589b^6}{345996}\\
 &-\frac{28536763b^4}{22143744}
 +\frac{4602029b^2}{3690624}
 +\frac{24895}{43936}.
\end{split}
\tag{96.9}
\]
Exact division in \(K_{14}[T]\) gives
\[
 \gcd(F(b,2b,T),N(b,2b,T))=(T+b^2)(T-T_0).
\tag{96.10}
\]
For a short complete certificate, both original polynomials are exactly
divisible by the right side; the resultant of their remaining cofactors
has residue 6 modulo 149. Thus no other T root is omitted. The factor
T=−b² has K=4b²+4T=0 and is impossible in the nonconstant physical chart.
The second factor is retained without assuming a physical existence count.

At \(D=2b,T=T_0\), the good residues are
\[
 (D,T_0,a,c,K,J,F_a)=(20,40,118,8,113,14,144).
\]
All original Cramer denominators are units. Therefore the two signs
\(s^2=K\), the reconstruction (96.5) and all three unique positions cover
every remaining original aligned possibility. The original equations
follow from (96.10) and the exact Cramer identities; no vanished V is used
at this special point.

The mixed norm in \(\mathcal A_{14}[s]/(s^2-K)\) has dimension 40 and
full multiplication determinant 41 modulo 149. It retains both signs and
all three relative positions. Thus these special rays have no mixed
edge either. The full finite aligned set is Theta-stable by the explicit
sign operation, so the ordinary mixed tests cover both relative parities.

### 96.5. Consumer and precise remaining boundary

For either parameter field, a noncanonical orthogonal triple is all
generic, mixed, or all aligned. The generic case is excluded by (96.4) and
the uniform within-union bipartite theorem. Every mixed possibility has
been covered by the finite quartic and the applicable exceptional pair.
The all-aligned case is excluded by the uniform original Gram argument
of §85, including constant channels, all poles and both parameter signs.

A common-flat basis containing a canonical ray is canonical by §60.
A basis containing none would contain a forbidden noncanonical triple.
This proves basis uniqueness at the four roots of (96.1).
If \(B\) is an output basis unbiased to \(I_6\) and \(H_0\), then \(W=H_0^*B\) is a
common-flat input basis; the transformation is unitary and preserves
orthogonality and pairwise unbiasedness. Two additional output bases
would both transport to the same canonical input basis up to phases and
permutation, and therefore could not be mutually unbiased. This proves
the stated fixed-pair quartet exclusion.

The source, lift and rank-upper assertions are characteristic-zero
arguments. The residue matrices certify only the explicitly named units
and rank lower bounds. In particular no constant physical ray count,
continuation through a vanished chart denominator, or equality of
modular and real solution sets is assumed. Every other zero of the
previous finite guard retains its prior status.


### 96.6. Combined removal of the newly resolved primary factors

Write \(Q_{16}\) for the polynomial of §95.1. The irreducible parameter
polynomials \(Q_{10},Q_{14},Q_{16}\) have distinct degrees 10, 14 and 16.
They are pairwise coprime, and are coprime to the three irreducible
polynomials of degrees 32, 196 and 96 in §94.5. Therefore the eight
parameters resolved in §§95–96 are mutually distinct and disjoint from
the twelve parameters resolved in §§92–94.

Let \(H_{\mathrm{reduced}}\) be the exact nonzero polynomial (94.3), and
let \(v_{10},v_{14},v_{16}\) be the maximal nonnegative exponents such that
the corresponding powers divide it. Define
\[
 H_{\mathrm{next}}=
 \frac{H_{\mathrm{reduced}}}
 {Q_{10}^{v_{10}}Q_{14}^{v_{14}}Q_{16}^{v_{16}}}.          \tag{96.11}
\]
The exponents are defined by exact polynomial divisibility; no expansion
or numerical approximation of the large guard is needed. This polynomial
is nonzero and is coprime to each of the three displayed factors.

For every real \(0<|b|<1\) with \(H_{\mathrm{next}}(b)\ne0\), there is no
noncanonical common-flat orthogonal triple. The only complete common-flat
input basis is canonical up to phases and permutations, and the fixed
pair \((I_6,H_0(b))\) cannot belong to a quartet. Away from the three new
factors this follows from §94.5; at their roots it follows from Theorems
95.1 and 96.1. In particular all twenty explicitly certified parameters
from §§92–96 are included. Every zero of the remaining guard is retained;
these arguments do not establish that the displayed factors exhaust it.

后续的 guard 重建与新增例外纤维处理见[理论续卷 V](MUB_SIX_FOURTH_BASIS_THEORY_CONTINUATION_V.md)。
