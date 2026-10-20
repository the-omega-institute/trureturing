# FIB off-24 unequal-ratio collision geometry

This volume records an ordinary-mathematical continuation of the common-parent FIB geometry. It gives one exact complete-world collision away from the known (p=24) mirror components. The collision is defined by a rational isolating box and a contraction certificate; decimal values are only orientation.

## 1. Literal parent and the regular lift

**Definition 1.1 (complete world and the fixed history).** A complete world is

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\ r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,
$$

where $g\in\mathbb R[s]$ is one nonzero polynomial of degree at most three and $d\in\mathbb R$ is fixed through the whole run. The actions are

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
Q_i=E_iQ_{i-1},\quad Q_0=I,\qquad
y_i=d+g(i)\operatorname{tr}(Q_iP).
$$

The original clocks are $0,\ldots,7$, with the chronological word $(J,M,J,M,M,M,M)$. The literal parent is

$$
H_4=(0,J,24,M,147/5,J,24,M,18).
$$

No gain sample, source coordinate, reset, copy, skipped clock, shifted clock or extra observation is added. Lower-degree gains, repeated roots, sampled zeros, zero drift, singular source charts and unbounded legal (b) remain members of the complete domain.

For a strict source define

$$
 j=b+\frac{r(1-r)}b,\qquad n=j+r,\qquad T=1+b,\qquad U=1+2b,
$$

and

$$
 \Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,\qquad B=\frac6T-\frac2U.
$$

The parent traces at clocks $0,\ldots,4$ are $(1,j,T,n,U)$. The actual $(M,M,M)$ continuation traces at clocks $(5,6,7)$ are $(U+n,2U+n,3U+2n)$.

**Lemma 1.2 (one entire gain and one fixed drift).** On the regular locus $\Lambda\ne0$, put

$$
 e=-\frac{24}{5}\left(b-\frac18\right)\frac{B}{\Lambda},\qquad d=24+e,
$$

and prescribe the four gain values

$$
(q_0,q_1,q_2,q_3)=
\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right).
\tag{1}
$$

Let $g_{r,b}$ be the unique polynomial of degree at most three interpolating these values at $(0,1,2,3)$:

$$
 g_{r,b}(s)=\sum_{i=0}^{3}q_i
 \prod_{\substack{0\le k\le3\\k\ne i}}
 \frac{s-k}{i-k}.
\tag{2}
$$

Then $W(r,b)=(P(r,b),g_{r,b},d)$ realizes $H_4$.

**Proof.** Formula (2) gives $g(0)=q_0,\ldots,g(3)=q_3$, so the first four readings are $(0,24,147/5,24)$. At $s=4$, the interpolation identity is

$$
 g(4)=-q_0+4q_1-6q_2+4q_3.
$$

Substitution into the fifth parent row gives the exact residual identity

$$
 d+Ug(4)-18
 =U\left(e\Lambda+\frac{24}{5}\left(b-\frac18\right)B\right)=0.
\tag{3}
$$

The last equality is the definition of $e$. Thus the fifth parent reading is $18$. The polynomial is defined at every clock by (2), and it is not identically zero because $g(0)=-d$ while the first two readings are different. ∎

## 2. The actual response map

**Definition 2.1 (three later responses).** The same interpolation formula gives

$$
\begin{aligned}
g(5)&=-4q_0+15q_1-20q_2+10q_3,\\
g(6)&=-10q_0+36q_1-45q_2+20q_3,\\
g(7)&=-20q_0+70q_1-84q_2+35q_3.
\end{aligned}
$$

Define the actual response map of this complete world by

$$
\Psi(r,b)=\left(
 d+(U+n)g(5),
 d+(2U+n)g(6),
 d+(3U+2n)g(7)
\right).
\tag{4}
$$

The three entries are respectively the actual fifth-$M$, sixth-$M$, and seventh-$M$ readings. They evaluate the one polynomial and the one drift already fixed by (1)–(2).

The source-specific matrix products are

$$
\operatorname{tr}(Q_iP)=\left(1,j,T,n,U,U+n,2U+n,3U+2n\right)_i,\qquad 0\le i\le7,
\tag{5}
$$

as follows by direct multiplication of $(J,M,J,M,M,M,M)$. Therefore equality of the three coordinates of $\Psi$ is equality of the actual readings, rather than equality of a projected or rescaled system.

## 3. An exact zero of the three-response difference

**Definition 3.1 (isolating box).** Fix the first source coordinate $r_A=1/8$. For

$$
\begin{aligned}
z&=(\xi,\tau,\zeta)=(b_A,r_B,b_B),\\
F(z)&=\Psi\left(\frac18,\xi\right)-\Psi(\tau,\zeta),
\end{aligned}
\tag{6}
$$

let

$$
z_0=\frac1{10^{18}}
\begin{pmatrix}
23987140659295483\\
893793132424690909\\
25022873150407289
\end{pmatrix},\qquad
\rho=\frac1{10^{12}},\qquad
X=z_0+[-\rho,\rho]^3.
\tag{7}
$$

All entries in (7) are exact rationals. Let $C$ be the rational matrix

$$
C=\frac1{10^{12}}
\begin{pmatrix}
5243562804458&-4374555673860&717669526134\\
3964915631058&-3296878123863&541497661837\\
5775627325121&-4821015492245&790827420333
\end{pmatrix}.
\tag{8}
$$

Its determinant is

$$
det C=\frac{70263682584632593638580103231}{20000000000000000000000000000000000},
$$

which lies strictly between $3/10^6$ and $4/10^6$.

**Proposition 3.2 (rational contraction certificate).** The map $N(z)=z-CF(z)$ maps $X$ into its interior and is a contraction in the infinity norm. Consequently $F$ has exactly one zero $z_*$ in $X$.

**Proof.** The certificate uses closed rational intervals. Addition and subtraction use endpoints, multiplication uses the minimum and maximum of the four endpoint products, and a reciprocal is $[1/v,1/u]$ for $[u,v]$ excluding zero. Forward differentiation uses

$$
\begin{aligned}
D(xy)&=y\,Dx+x\,Dy,\\
D(x/y)&=\frac{Dx-(x/y)Dy}{y},
\end{aligned}
$$

with the three coordinate derivatives initialized as the standard basis. Applied in the order $j,n,T,U,\Lambda,B,e,d,q_0,\ldots,q_3,\Psi$, this gives the following exact enclosure for $DF(X)$; every displayed endpoint is divided by $10^7$:

$$
J_F(X)\subseteq
\begin{pmatrix}
[9413098549,9413098557]&[-1074026073,-1074026071]&[-7806900995,-7806900987]\\
[-22985723971,-22985723951]&[5014028228,5014028233]&[17426139632,17426139653]\\
[-208871210485,-208871210393]&[38410254019,38410254033]&[163261207840,163261207932]
\end{pmatrix}\frac1{10^7}.
\tag{9}
$$

Multiplying these rational intervals by (8), every entry of $10^8(I-CDF(X))$ lies in

$$
\begin{pmatrix}
[-976,980]&[-200,225]&[-985,1014]\\
[-737,739]&[-151,170]&[-743,766]\\
[-1076,1078]&[-220,248]&[-1084,1119]
\end{pmatrix}.
\tag{10}
$$

Thus the three row sums of absolute endpoint maxima are at most $2219,1675,2445$, divided by $10^8$. Set $q=2445/10^8<1/40000$. Point rational evaluation at $z_0$ gives

$$
\lVert CF(z_0)\rVert_\infty<10^{-18}.
\tag{11}
$$

The box is convex, so the mean-value inequality from (9)–(10) gives

$$
\begin{aligned}
\lVert N(z)-N(w)\rVert_\infty&\le q\lVert z-w\rVert_\infty,\\
\lVert N(z)-z_0\rVert_\infty&\le 10^{-18}+q\rho<\rho.
\end{aligned}
$$

Hence $N$ is a contraction from the complete box $X$ into its interior. Banach's fixed-point theorem gives a unique fixed point $z_*$. Since $\det C\ne0$, $N(z_*)=z_*$ is equivalent to $F(z_*)=0$. ∎

## 4. Domain and response enclosures

The same rational interval evaluation over the whole box $X$ gives the following strict guards. All intervals are closed and all endpoints in this table are the listed integers divided by $10^7$, unless a separate denominator is shown.

| quantity | first source $(1/8,\xi)$ | second source $(\tau,\zeta)$ |
| --- | ---: | ---: |
| source coordinates | $0<\xi<1/10$ | $89/100<\tau<9/10$, $0<\zeta<1/10$ |
| $\Lambda$ | $[60915297,60915298]/10^7$ | $[59095514,59095515]/10^7$ |
| drift $d$ | $[243144843,243144844]/10^7$ | $[243206696,243206697]/10^7$ |
| $\chi=n/U$ | $[44931655,44931656]/10^7$ | $[44878272,44878273]/10^7$ |
| fifth response $p$ | $[26301764,26301765]/10^7$ | $[26301764,26301765]/10^7$ |
| sixth response $u$ | $[1321806875,1321806876]/10^7$ | $[1321806875,1321806876]/10^7$ |
| seventh response $m$ | $[8027807170,8027807172]/10^7$ | $[8027807170,8027807172]/10^7$ |

The source intervals in the first row follow directly from (7); the wider rational bounds make positivity and $0<r<1$ explicit. Every denominator in (1)–(4), including $j,n,T,U,\Lambda$, is separated from zero on $X$. The two $\chi$ intervals are disjoint.

## 5. Fully lifted collision theorem

**Theorem 5.1 (exact off-$24$, unequal-$\chi$ collision).** Let $z_*=( \xi_*, \tau_*, \zeta_* )$ be the unique zero from Proposition 3.2 and define

$$
W_A=W\left(\frac18,\xi_*\right),\qquad W_B=W(\tau_*,\zeta_*),
\tag{12}
$$

using the entire polynomial (2) and drift in (1). Then $W_A,W_B$ are distinct complete worlds in the unchanged literal parent $H_4$, their analytical ratios are unequal, and

$$
\Psi(W_A)=\Psi(W_B)=(p_*,u_*,m_*),\qquad
p_*\in\left[\frac{26301764}{10^7},\frac{26301765}{10^7}\right]\subset(2,3),
$$

so $p_*\ne24$. In particular,

$$
\chi(W_A)\in\left[\frac{44931655}{10^7},\frac{44931656}{10^7}\right],\qquad
\chi(W_B)\in\left[\frac{44878272}{10^7},\frac{44878273}{10^7}\right],
$$

and $W_A\ne W_B$.

**Proof.** Proposition 3.2 supplies exact real source coordinates in $X$. The table in §4 gives strict positivity of both source matrices and separates every denominator used by the regular lift. Lemma 1.2 therefore gives both complete worlds, with one fixed drift and one polynomial used at every clock. Equations (4)–(6) and $F(z_*)=0$ give equality of the actual fifth, sixth and seventh readings. The response intervals place $p_*$ in $(2,3)$, hence away from $24$. The $\chi$ intervals are disjoint, while the first source has $r=1/8$ and the second has $r>89/100$; the complete triples are distinct. ∎

For orientation only, the exact source coordinates have the approximations

$$
\xi_*\approx0.0239871406592954830,\qquad
\tau_*\approx0.8937931324246909093,\qquad
\zeta_*\approx0.0250228731504072887,
$$

and the common response is approximately

$$
(p_*,u_*,m_*)\approx(2.6301764285,132.18068756,802.78071709).
$$

These decimals are not used in the existence proof.

## 6. Consequence and boundaries

**Corollary 6.1 (failure of off-$24$ injectivity).** The actual map $W\mapsto(p,u,m)$ on complete worlds realizing the fixed $H_4$ is noninjective after restricting to $p\ne24$. The collision is in the unequal-$\chi$ residual sector. Thus the entire-sector exclusion alternative for the stated existential question is false.

The result is an existential member of the full domain. It does not classify the remaining collision locus, decide simultaneous terminal-$J$ and terminal-$M$ pairs in one acquired child, settle adaptive original-root lower bounds, decide the separate $p=24$ work, or complete the through-2027 programme. The analytical coordinate $\chi$ is used only to certify that the two worlds differ; it is not treated as an acquired response.

## 7. Sources, overlap, and finite verification boundary

**Source statement.** The complete-world parametrization and actual trace convention use *FIB common-parent geometry and two exact mixed children*, immutable pin `416bdd31f206db9fe5dd1113e2902e94dff6bc46`, Definitions 1.1–1.3 and Theorem 2.1. The supplied zero-safe full-parent interface is used only to identify the regular lift as a legal subfamily. The supplied all-response finite-fibre volume, at the same pin, is used within scope: its finite bounds are not treated as an injectivity theorem, its exact-$p_J$ result is not exported, its sampled-root/$d=24$ exhaustion is not applied outside that stratum, and its equal-\chi classification is not applied to this unequal-\chi pair. The known $p=24$ mirror components remain in their published scope.

**Literature-attested.** Berrut and Trefethen, "Barycentric Lagrange Interpolation," *SIAM Review* 46 (2004), 501–517, DOI [10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715), §2, gives the fixed-node Lagrange interpolant and its uniqueness. S. M. Rump, "Verification methods: rigorous results using floating-point arithmetic," *Acta Numerica* 19 (2010), 287–449, DOI [10.1017/S096249291000005X](https://doi.org/10.1017/S096249291000005X), Theorem 13.3, gives the interval fixed-point/root framework. Those sources supply classical tools only; they do not supply this FIB collision.

**Attribution boundary.** No worldwide-priority claim is made. The exact new content is the root $z_*$, the rational certificate (7)–(11), and the lift (12).

**Finite verification boundary.** Exact rational interval arithmetic checked (9)–(11), all strict guards in §4, the determinant in (8), the three source-response rows, and the original eight trace identities. The symbolic interpolation residuals reduce to zero, including the parent residual (3). These are ordinary mathematical checks; no Lean/kernel certification, exhaustive search, physical-realization claim, optimality claim, or full collision classification is asserted.

## 追加锚（本行以下为增补区）
