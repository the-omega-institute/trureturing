# Native complete-continuation residual contact curve

## 58. Original problem, source coefficients and normalization

**Convention 58.1 (same problem and conditional antecedents).** This is a
same-topic continuation of [JR, §§29–57][JR]. Its section numbering
continues JR. Retain JR Definition 41.1 and Convention 53.1, including the
sole normalized reached-cut unknown specimen, all twelve histories
$y\in\{5,16,27\}$, $e,n\in\{\pm1\}$, one common all-complex CPTP
processor, and HALF the complete stopped-cq trace norm. In particular

$$
\begin{aligned}
p_y&=(y/128,(64-y)/128,1/2),&
a_y&=(\sqrt{p_{yi}})_i,& U_{e,n}&=\operatorname{diag}(e,n,1),\\
\rho_{y,e,n}&=U_{e,n}a_ya_y^TU_{e,n}^\dagger,&
E&=((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2),&P&=EE^\dagger.
\end{aligned}
\tag{RC.1}
$$

The ideal live block and the five separately labelled failure measures
are CG.111 and CG.50. Their density is $f_y(t)=6y/(y+6t)^2$, their weights,
in original label order $(0,1,2,3,13)$, are $(0,1/4,1/2,1/4,0)$.
The simulator density is the different function $g_{\rm time}(t)=2/(1+t)^2$.
All live coherences, passive-reference amplifications, singular-time,
wrong-support, abort and zero-target sectors retain their original meaning.
No prior, acceptance division, postselection, helper specimen, history
oracle, copy, reset, retry or uncounted bypass is supplied.

The isolated CG root, its ranks, normalization and minimax identification
remain inherited ordinary conditional premises. All operator identities
and TP assertions below apply at that root. Off-root boxes establish
inequalities of derived expressions only. CG supplies the source and
minimax premises; JR §§34–40 supplies the sharp worst-history jointly
counted acquisition cost. The necessary statements cover the original
finite and countable instruments and only CG Convention 21.3's explicitly
stipulated measurable finite-dimensional-fibre, measurable-Kraus,
integrable-effect/live-Choi extension, with full-output TP decoders almost
everywhere. No arbitrary disintegration or infinite-dimensional coding
extension is asserted.

**Definition 58.2 (coefficient dictionary).** Write the source Kraus
matrices as

$$
D_{\rm src}=\operatorname{diag}(h_0,h_1,h_2),\quad
T_{\rm src}=a_{\rm src}e_0e_1^T+b_{\rm src}e_1e_0^T,\quad
S_{\rm src}=c_{\rm src}e_0e_2^T+d_{\rm src}e_2e_0^T,
$$

and $M_f=\operatorname{diag}(0,m_1,m_2)$, as in JR.2. Put

$$
\begin{gathered}
\theta=\frac{a_{\rm src}b_{\rm src}}{h_0h_1},\quad
\omega_{\rm src}=\frac{c_{\rm src}d_{\rm src}}{h_0h_2},\quad
\delta=\theta+\omega_{\rm src},\quad s_0=\sqrt\delta,\quad
\beta=\chi=\frac{\omega_{\rm src}}\delta,\quad\alpha=1-\beta,\\
L=\operatorname{diag}(s_0,1,1),\quad
Q=\operatorname{diag}(1,-\alpha,-\beta),\quad
C=(e_0e_1^T+e_1e_0^T)/2,\\
G=\begin{pmatrix}g_0&x&y\\x&g_1&z\\y&z&g_2\end{pmatrix}=LNL,
\qquad j(\tau)=J_{s_0\tau}.
\end{gathered}
\tag{RC.2}
$$

Here $N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger)$,
$(K_0,K_1,K_2)=(D_{\rm src},T_{\rm src},S_{\rm src})$ and
$\Delta=\rho_{27,+,+}-\rho_{5,+,+}$. Equivalently, with
$d_i=p_{27,i}-p_{5,i}$ and
$q_{ij,y}=\sqrt{p_{yi}p_{yj}}$,

$$
\begin{aligned}
\Delta A&=\sum_i h_i^2d_i,&
g_0&=\delta\Delta A,\\
g_1&=b_{\rm src}^2d_0+a_{\rm src}^2d_1,&
g_2&=d_{\rm src}^2d_0+c_{\rm src}^2d_2,\\
x&=s_0(h_0a_{\rm src}+h_1b_{\rm src})(q_{01,27}-q_{01,5}),\\
y&=s_0(h_0c_{\rm src}+h_2d_{\rm src})(q_{02,27}-q_{02,5}),\\
z&=a_{\rm src}c_{\rm src}(q_{12,27}-q_{12,5}).
\end{aligned}
\tag{RC.3}
$$

Define $L_f=\|M_f^{1/2}\Delta M_f^{1/2}\|_1$ and
$T_{\rm flat}=((1-\delta)\Delta A+L_f+\operatorname{tr}G)/2$,
as in JR.130. This $T_{\rm flat}$ is not the different strong-regime
constant with the same historical name in JR.50.

The global parameters $a,k,D$ introduced in §59 are scalar algebraic
coordinates. They are not $a_{\rm src}$, the CG root coordinates, the
initial-frame $k(t),D(t)$ of JR.140, or AS's raw transfer parameters.
In particular the normalized residual $\beta$ is $\omega_{\rm src}/\delta$,
not the raw AS transfer ratio $\omega_{\rm src}$.

**Definition 58.3 (complete source and comparison boxes).** Use the entire
nine-coordinate CG Proposition 13.2 box

$$
\mathcal B_9=\prod_{i=0}^8[c_i-10^{-24},c_i+10^{-24}],
\quad
u=(\lambda_{\rm CG},\alpha_1,\alpha_2,\beta_1,\beta_2,z_{\rm CG},
\eta_0,\eta_1,\eta_2),
\tag{RC.4}
$$

with these exact rational decimal centres:

| Coordinate | $c_i$ |
| --- | --- |
| $\lambda_{\rm CG}$ | $0.479508042205945691075728241615$ |
| $\alpha_1$ | $1.412018697539825943102823246594$ |
| $\alpha_2$ | $1.185897402486986028204155873343$ |
| $\beta_1$ | $0.413330945620125544606320492846$ |
| $\beta_2$ | $0.809647491041060318009094562763$ |
| $z_{\rm CG}$ | $0.066998926272600209516864472757$ |
| $\eta_0$ | $0.279795267654829218213193898783$ |
| $\eta_1$ | $0.199570407911600478528148253443$ |
| $\eta_2$ | $0.091392615490799158339482855657$ |

For every point of this box form $S_0,S_{01},S_{02}$ by CG.112–.113,
$H=1000\eta_0\operatorname{adj}S_0$ and
$Q^{0i}=\eta_i\operatorname{adj}S_{0i}$ by CG.116, and use exactly
CG.134's positive-pivot formulas

$$
h=He_0/\sqrt{H_{00}},\quad
(a_{\rm src},b_{\rm src})^T=Q^{01}e_0/\sqrt{Q^{01}_{00}},\quad
(c_{\rm src},d_{\rm src})^T=Q^{02}e_0/\sqrt{Q^{02}_{00}}.
\tag{RC.5}
$$

No singular source matrix is inverted. These formulas define the
comparison expressions off root as well, without asserting rank-one
factorization there. Define the independent seven-coordinate closed box
$\mathcal B_7$ by the following integer endpoints divided by $10^{23}$:

| Coordinate | Lower integer | Upper integer |
| --- | --- | --- |
| $\beta$ | $12228666915779851600692$ | $12228666915779851600715$ |
| $g_0$ | $126934124154363919620$ | $126934124154363919621$ |
| $g_1$ | $292224504683244786341$ | $292224504683244786342$ |
| $g_2$ | $167719666504311385249$ | $167719666504311385250$ |
| $x$ | $237055800155858174667$ | $237055800155858174668$ |
| $y$ | $220801123770243408728$ | $220801123770243408729$ |
| $z$ | $-10165551560101453541$ | $-10165551560101453540$ |

**Proposition 58.4 (source-box inclusion and original optimization).**
The image of $\mathcal B_9$ under (RC.2)–(RC.5) is contained in the
interior of $\mathcal B_7$. For the conditional source root the original
problem is

$$
\begin{aligned}
j(\tau)=\max\;&\sum_{r,\epsilon=\pm1}\epsilon\operatorname{tr}(GX_{r,\epsilon}),\\
&X_{r,\epsilon}\succeq0,\quad\operatorname{tr}(QX_{r,\epsilon})=0,
\quad\sum_{r,\epsilon}X_{r,\epsilon}=I,\quad
\sum_{r,\epsilon}r(X_{r,\epsilon})_{01}\geq\tau,
\end{aligned}
\tag{RC.6}
$$

and $\mathcal T(s_0\tau)=T_{\rm flat}+(j(\tau)-\operatorname{tr}G)/2$.
On the residual interval every optimizing tuple has
$X_{+,-}=0$, saturated contrast, and corresponds to

$$
A=X_{+,+},\quad B=X_{-,+},\quad C_0=X_{-,-},\qquad
A+B+C_0=I,\quad \operatorname{tr}(QA)=\operatorname{tr}(QB)
=\operatorname{tr}(QC_0)=0,
\tag{RC.7}
$$

with $2A_{01}=\tau$ and objective
$\operatorname{tr}G-2\operatorname{tr}(GC_0)$.

Proof. The inclusion is a finite rational/radical comparison: substitute
all nine intervals in CG.112–.113, take adjugates, the three positive
pivots in (RC.5), then (RC.2)–(RC.3). Directed arithmetic is specified in
§60; its integer endpoint comparisons give precisely the strict
inclusions in the table. In particular no coordinate $\eta_i$ is held
at its centre. These comparisons also imply the coarse JR.86 box.
The optimization and its connection with the original experiment are
JR Theorems 42.1 and 45.1, JR.83–.85 and Lemma 53.2, reused with their
full all-error-optimizer scope. CA Theorem 5.1's real exposed face is a
consequence of the complex equality conditions. It is not an assumption
that the competitors are real processors. Necessity uses analytic
refinement only as an upper bound on actual-label TV; the converse
constructs an instrument that actually generates the labels. In
particular no other binary-effect entry or forgotten complete channel
is fixed in the lower bound. $\square$

## 59. A selected algebraic curve on the complete parameter rectangle

**Definition 59.1 (polynomials and exact division).** For

$$
(a,k)\in\mathcal R=[0,37/125]\times[7/20,2/5]
$$

put

$$
\begin{aligned}
D&=\alpha(1-2a)+a^2,&U&=-\alpha+2a-a^2,&V&=\alpha-a^2,\\
n&=(D,U,V)^T,&\sigma&=DU,\\
W&=D Cn-2\beta ak Qn,&H&=-n^TQW,&R&=W^TQW,\\
Z&=2HW+Rn,&\mathcal E&=2H W^TW+DR\sigma,\\
g&=Z^TGZ,&\ell&=D^2\sigma Z^TCZ-\mathcal E^2,\\
\ell_1&=\ell/a,&
\mathcal P&=\frac1a\det[D^2\sigma CZ-\mathcal E W,\ QZ,\ GZ].
\end{aligned}
\tag{RC.8}
$$

The $g$ in (RC.8) is a scalar polynomial, distinct from the time density.
The two divisions by $a$ mean division in the polynomial ring, before
interval evaluation. They do not leave an undefined endpoint.

**Proposition 59.2 (identities and root selection).** Both divisions in
(RC.8) are exact. For every $0\leq a\leq37/125$ there is precisely one
$k(a)\in(7/20,2/5)$ with $\mathcal P(a,k(a))=0$. This selected root
is real analytic, including one-sided analytic extensions at the two
endpoints. Throughout $\mathcal R$,

$$
D,H,R,\mathcal E>0,\quad \sigma<0,\quad g<0,\quad
\ell_1<0,
\tag{RC.9}
$$

and

$$
n^TQn=Z^TQZ=0,\quad n^TQZ=-2H^2,\quad
n^TW=D\sigma,\quad Z^TW=\mathcal E.
\tag{RC.10}
$$

Proof. Expansion of $D^2-\alpha U^2-\beta V^2$ gives zero.
Consequently
$Z^TQZ=4H^2R+4HRn^TQW=0$ and
$n^TQZ=2Hn^TQW=-2H^2$.
The last two identities follow from $n^TQn=0$ and $n^TCn=DU$.
At $a=0$ the exact values are

$$
n=\alpha(1,-1,1)^T,\quad
W=\alpha^2(-1,1,0)^T/2,\quad
Z=\alpha^5\beta(-1,1,1)^T/4.
\tag{RC.11}
$$

They make $\ell=0$ and the first determinant column in (RC.8) zero.
Thus every coefficient of $a^0$ vanishes identically, proving exact
divisibility. The full-domain bounds in Proposition 60.1 give
$\mathcal P(a,7/20)>0$, $\mathcal P(a,2/5)<0$ and
$\mathcal P_k<0$. The intermediate value theorem and strict monotonicity
give existence and uniqueness for each $a$. Since the root is strictly
inside the $k$ interval and $\mathcal P_k\ne0$, the analytic implicit
function theorem applies at every point, including the endpoint roots.
The same bounds give (RC.9). $\square$

**Definition 59.3 (aggregate, value and feasibility boundary).** All the
following expressions are evaluated at $(a,k(a))$:

$$
\begin{aligned}
B(a)&=-\frac{R}{2D\sigma H}nn^T,&
C_0(a)&=\frac{ZZ^T}{2H\mathcal E},& A(a)&=I-B(a)-C_0(a),\\
\tau(a)&=2A(a)_{01},&
\omega(a)&=\operatorname{tr}A(a)-1
=2-\operatorname{tr}B(a)-\operatorname{tr}C_0(a).
\end{aligned}
\tag{RC.12}
$$

Here $\omega(a)$ is an aggregate eigenvalue, not $\omega_{\rm src}$.
Let $a_\dagger$ be the unique zero of $\omega$ on $[0,37/125]$.
Its existence, uniqueness and enclosure are proved in §60. The exact
value to be established for $0\leq a\leq a_\dagger$ is

$$
j(\tau(a))=\operatorname{tr}G-\frac{g}{H\mathcal E},\qquad
\mathcal T(s_0\tau(a))=T_{\rm flat}-\frac{g}{2H\mathcal E}.
\tag{RC.13}
$$

## 60. Whole-domain finite arithmetic

**Definition 60.1 (rational comparison convention).** Every terminating
decimal below is an exact rational. Directed arithmetic uses
$\Lambda=2^{288}$. The interval $[l/\Lambda,h/\Lambda]$ has integer
endpoints. Embed a rational $q$ with the floor and ceiling of
$\Lambda q$. Add and negate endpoints exactly. Multiply using the
minimum and maximum of the four endpoint products, divided by
$\Lambda$ with floor and ceiling. For a nonzero interval reciprocal use
$[\lfloor\Lambda^2/h\rfloor,\lceil\Lambda^2/l\rceil]/\Lambda$;
the interval must exclude zero. For a positive interval square root use
$[\lfloor\sqrt{l\Lambda}\rfloor,\lceil\sqrt{h\Lambda}\rceil]/\Lambda$,
with the ceiling obtained by the integer-square comparison. Determinants
and adjugates use their finite signed permutation expansions. This
specifies (RC.4)–(RC.5)'s box inclusion without a root solver.

For polynomial comparisons expand (RC.8) using coefficientwise rational
interval addition and convolution, with the coefficients enclosed by the
entire independent $\mathcal B_7$. Cancel identically zero constant
powers of $a$ before the two divisions. For a polynomial
$P(a,k)=\sum p_{ij}a^ik^j$ and a rectangle
$[l,h]\times[v,w]$, define

$$
\begin{aligned}
E_i^{N}(t;l,h)
&=\sum_{r=0}^{\min(i,t)}\binom ir l^{i-r}(h-l)^r
                       \frac{\binom tr}{\binom Nr},\\
b_{tu}(P)&=\sum_{i,j}p_{ij}E_i^N(t;l,h)E_j^M(u;v,w),
\quad 0\leq t\leq N,\quad0\leq u\leq M.
\end{aligned}
\tag{RC.14}
$$

Here $i\leq N,j\leq M$. This is equivalently the affine change to
$[0,1]^2$ followed by monomial-to-Bernstein conversion. All sums in
(RC.14) are finite rational comparisons with directed endpoints; terms
are accumulated in increasing indices. The Bernstein basis is
nonnegative and sums to one, so a common strict lower bound for all
$b_{tu}$ is a strict bound on the whole rectangle, including its edges.
This is a universal certificate, not an inference from sampled values.

**Proposition 60.2 (root, sign and denominator bounds).** Put

$$
\begin{aligned}
N_Q&=\beta W_1^2+\alpha W_2^2-\alpha\beta W_0^2,\\
D_\kappa&=\beta Z_2\ell_1,\\
N_\kappa&=(GZ)_2\ell_1+g(2\beta^2kV)\mathcal E.
\end{aligned}
\tag{RC.15}
$$

With bidegree $(N,M)=(40,10)$, every Bernstein coefficient on the
specified rectangle exceeds the corresponding bound in the following
tables, uniformly over the entire $\mathcal B_7$.

| Polynomial on $\mathcal R$ | Strict lower bound |
| --- | --- |
| $D,-U,V$ | $.44,.37,.79$, respectively |
| $H,R,\mathcal E$ | $.012,.0016,.0003$, respectively |
| $-Z_0,Z_1,Z_2$ | $.0016,.0016,.0013$, respectively |
| $W_1$ | $.08$ |
| $N_Q$ | $2\cdot10^{-6}$ |
| $\beta W_0^2-W_2^2$ | $.001$ |
| $n^TGn$ | $.0025$ |
| $-g$ | $8\cdot10^{-9}$ |
| $-\ell_1$ | $10^{-8}$ |
| $gD^2\sigma+\ell/25$ | $3\cdot10^{-11}$ |
| $-N_\kappa-(3/1000)D_\kappa$ | $3\cdot10^{-15}$ |
| $N_\kappa-(3/1000)D_\kappa$ | $8\cdot10^{-15}$ |
| $\mathcal P(a,7/20)$ | $10^{-14}$ |
| $-\mathcal P(a,2/5)$ | $10^{-15}$ |
| $-\mathcal P_k$ | $10^{-13}$ |

Define

$$
\begin{aligned}
\Omega&=-4D\sigma H\mathcal E-R\mathcal E n^Tn+D\sigma Z^TZ,\\
\mathscr D&=-2D\sigma H\mathcal E>0,\qquad \omega=\Omega/\mathscr D.
\end{aligned}
\tag{RC.16}
$$

The additional comparisons are:

| Rectangle | Polynomial | Strict lower bound |
| --- | --- | --- |
| $[0,7/25]\times[7/20,2/5]$ | $\Omega$ | $9\cdot10^{-9}$ |
| $[7/25,37/125]\times[39/100,79/200]$ | $\mathcal P(a,.39)$ | $6\cdot10^{-16}$ |
| same | $-\mathcal P(a,.395)$ | $3\cdot10^{-16}$ |
| same | $\mathcal P_a$ | $10^{-14}$ |

On the second rectangle put
$N_a=\Omega_a\mathscr D-\Omega\mathscr D_a$ and
$N_k=\Omega_k\mathscr D-\Omega\mathscr D_k$.
At degree $(60,12)$, all Bernstein coefficients of the four polynomials

$$
N_a+4\mathscr D^2,\quad
-\tfrac9{10}\mathscr D^2-N_a,\quad
N_k+6\mathscr D^2,\quad -3\mathscr D^2-N_k
\tag{RC.17}
$$

are strictly positive. In particular

$$
-4<\omega_a<-.9,\qquad -6<\omega_k<-3.
\tag{RC.18}
$$

Proof. These are finite coefficient certificates using exactly (RC.14),
(RC.8), (RC.15)–(RC.17) and the integer box of Definition 58.3.
The degrees of $\ell_1$ and $\mathcal P$ are at most $(26,6)$ and
$(36,8)$; the table fits $(40,10)$ and (RC.17) fits $(60,12)$.
For specificity, strictly smaller rational lower bounds than the
coefficient minima for the two $\kappa$ rows and the last root derivative
row are $3.1488\cdot10^{-15}$, $8.1964\cdot10^{-15}$ and
$2.0459\cdot10^{-13}$. For the four expressions in (RC.17), smaller
positive lower bounds are, in order,
$6.1323\cdot10^{-13}$, $5.5156\cdot10^{-13}$,
$5.4370\cdot10^{-13}$ and $6.2266\cdot10^{-13}$.
All comparisons are lower endpoints of (RC.14)'s finite sums, so rounding
cannot turn an unproved sign into a positive one. The positivity of the
Bernstein basis proves the assertions for every point in each rectangle.
Dividing (RC.17) by $\mathscr D^2>0$ proves (RC.18). $\square$

**Proposition 60.3 (unique simple feasibility boundary).** The zero
$a_\dagger$ in Definition 59.3 exists uniquely, with

$$
.2951251<a_\dagger<.2951252,
\quad \omega(a)>0\ (0\leq a<a_\dagger),
\quad \omega'(a)<-.9\ (7/25\leq a\leq37/125).
\tag{RC.19}
$$

Proof. On the early rectangle $\Omega>0$ and $\mathscr D>0$.
On the late rectangle the root lies in $(.39,.395)$, and
$k'(a)=-\mathcal P_a/\mathcal P_k>0$. Thus (RC.18) gives
$\omega'=\omega_a+\omega_k k'<-.9$ along it.
The following exact comparisons complete isolation:

| $a$ | Enclosure for $k(a)$ | Enclosure for $\omega(a)$ |
| --- | --- | --- |
| $.2951251$ | $(.393637406,.393637409)$ | $(1.2\cdot10^{-7},1.9\cdot10^{-7})$ |
| $.2951252$ | $(.393637421,.393637424)$ | $(-1.9\cdot10^{-7},-1.2\cdot10^{-7})$ |

For each $k$ bracket, evaluating $\mathcal P$ at its two endpoints gives
respectively positive and negative intervals. To specify a stable finite
comparison for the last column, evaluate $\Omega/\mathscr D$ at the
bracket midpoint and enlarge by $6$ times its half-width using (RC.18).
The resulting intervals are contained respectively in
$(1.4257,1.6059)10^{-7}$ and $(-1.6746,-1.4945)10^{-7}$.
Continuity, the two opposite signs, strict decrease on the late segment
and positivity on the early segment prove (RC.19), including simplicity.
Direct interval substitution in $Z_2/Z_1$ on these brackets also gives

$$
1.04172<\left.\frac{Z_2}{Z_1}\right|_{a_\dagger}<1.04179.
\tag{RC.20}
$$

All these are rational comparisons with nonzero denominators, using
(RC.9); no remaining matrix optimization is involved. $\square$

## 61. Primal feasibility and all four original dual blocks

**Theorem 61.1 (matching original primal and dual).** For every
$0<a\leq a_\dagger$ the tuple $(A,0,B,C_0)$ of (RC.12) is feasible
for the original problem at $\tau(a)$ and has a matching finite original
four-block dual. Its active slack ranks, in $(A,B,C_0)$ order, are
$(1,2,2)$; the fourth slack can be positive definite. Formula (RC.13)
is the global optimum over the original competitor class.

Proof. The signs in (RC.9) make $B,C_0$ positive rank-one null matrices.
Equations (RC.10) give

$$
BW=-\frac R{2H}n,\quad C_0W=\frac Z{2H},\quad AW=0.
\tag{RC.21}
$$

The vectors $n,Z$ are independent by $n^TQZ=-2H^2\ne0$.
Thus $B+C_0$ has rank two and $A$ has an eigenvalue $1$ on its
orthogonal complement. Equation (RC.21) gives an eigenvalue $0$, so

$$
\operatorname{spec}A=(1,\omega,0).
\tag{RC.22}
$$

Since $\omega\geq0$, $A\succeq0$. Also $\operatorname{tr}Q=0$ gives
$\operatorname{tr}(QA)=0$. This establishes primal feasibility, without
assuming an optimal rank pattern.

For the dual define

$$
\begin{aligned}
\mathcal H&=C-\frac{WW^T}{D^2\sigma},&r_0&=\frac{2\beta ak}{D},\\
\lambda&=-\frac{gD^2\sigma}{\ell},&\kappa_0&=\frac{N_\kappa}{D_\kappa},\\
S_A&=-\frac{2\lambda}{D^2\sigma}WW^T,&
Y&=G+\lambda C+S_A,\\
\nu_A&=0,&\nu_B&=-2\lambda r_0,&\nu_C&=2\kappa_0.
\end{aligned}
\tag{RC.23}
$$

Proposition 60.2 proves $\lambda>1/25$ and $|\kappa_0|<3/1000$;
$D_\kappa<0$, and $\ell=a\ell_1<0$ for $a>0$. Hence these are finite.
The original dual slacks, with exactly JR.126's normalization, are

$$
\begin{aligned}
S_{+,+}&=Y-G-\lambda C+\nu_AQ=S_A,\\
S_{-,+}&=Y-G+\lambda C+\nu_BQ
       =S_A+2\lambda C-2\lambda r_0Q,\\
S_{-,-}&=Y+G+\lambda C+\nu_CQ
       =2(G+\lambda\mathcal H+\kappa_0Q),\\
S_{+,-}&=Y+G-\lambda C+\nu_4Q=S_A+2G+\nu_4Q.
\end{aligned}
\tag{RC.24}
$$

First consider $K=C-r_0Q$. Its third diagonal block is $r_0\beta>0$;
the determinant of its first two coordinates is
$-r_0^2\alpha-1/4<0$. Its inertia is therefore $(2+,1-)$.
Moreover $Kn=W/D$ and $n^TKn=\sigma<0$. The elementary negative-direction
removal identity is

$$
M-\frac{Mvv^TM}{v^TMv}\succeq0,\quad
\operatorname{rank}=2,\quad\ker=\mathbb Rv
\quad\text{if }\operatorname{inertia}M=(2+,1-),\ v^TMv<0.
\tag{RC.25}
$$

Indeed take $v$ as the first basis vector and choose the other two in
its $M$-orthogonal complement. Congruence gives a negative scalar block
and a positive definite $2\times2$ block; the displayed subtraction
removes exactly the former. Applying this to $K,n$ gives

$$
\frac{S_{-,+}}{2\lambda}
=K-\frac{Knn^TK}{n^TKn},\qquad \ker S_{-,+}=\mathbb Rn.
\tag{RC.26}
$$

Next $Z^T\mathcal HZ=\ell/(D^2\sigma)>0$, whereas $Z^TQZ=0$.
Thus $\mathcal HZ$ and $QZ$ are independent. The determinant equation
$\mathcal P=0$ puts $GZ$ in their span. Pairing with $Z$ determines
$\lambda$, and coordinate $2$ determines $\kappa_0$, because

$$
W_2=2\beta^2akV,\qquad
(G+\lambda\mathcal H+\kappa_0Q)Z=0.
\tag{RC.27}
$$

This also derives (RC.23)'s $\kappa_0$ formula with no extra singularity.
Put $M_0=G+\lambda C+\kappa_0Q$. The source box and the preceding
multiplier bounds imply

$$
(M_0)_{22}>.001310,\quad(M_0)_{11}>0,\quad(M_0)_{01}>.022370,
$$

and $|(M_0)_{00}|<.00427$,
$(M_0)_{11}<.005556$, $(M_0)_{22}<.002045$.
Using $y>0,z<0$ in the determinant expansion gives

$$
\begin{aligned}
\det M_0
&=(M_0)_{00}(M_0)_{11}(M_0)_{22}
 +2(M_0)_{01}yz-(M_0)_{00}z^2
 -(M_0)_{11}y^2-(M_0)_{22}(M_0)_{01}^2\\
&<.00427\cdot.005556\cdot.002045
 +.00427(.000102)^2-.001310(.022370)^2<-6\cdot10^{-7}.
\end{aligned}
\tag{RC.28}
$$

A positive diagonal entry excludes three negative eigenvalues, and the
negative determinant excludes zero eigenvalues, so $M_0$ has inertia
$(2+,1-)$. Set $\zeta=-\lambda/(D^2\sigma)>0$.
Equation (RC.27) says $(M_0+\zeta WW^T)Z=0$;
$Z^TM_0Z=-\zeta\mathcal E^2<0$. Consequently
$M_0+\zeta WW^T$ is exactly the subtraction in (RC.25), applied to
$M_0,Z$. This proves $S_{-,-}\succeq0$, rank two and kernel
$\mathbb RZ$. The slack $S_A$ is rank-one PSD with kernel $W^\perp$.

The fourth original block remains necessary. Let $R_4=S_A+2G$.
For a nonzero real $Q$-null vector $v$, if $v^TCv\geq0$, JR.133's
strict right-half-ellipse positivity gives $v^TGv>0$, hence
$v^TR_4v>0$. This includes $v^TCv=0$: normalize its nonzero coordinate
$0$ to one and its $u$ coordinate is nonnegative. If $v^TCv<0$ then

$$
v^TR_4v=v^TS_{-,-}v-2\lambda v^TCv>0.
$$

The unit null set is compact, so its $R_4$ minimum $m_0$ is positive.
Choose any $0<e<m_0$. Apply Xia–Wang–Sheu's equality S-lemma,
[Theorem 3, arXiv:1403.2816v3][SLEM], to the homogeneous pair
$v^T(R_4-eI)v$ and $v^TQv$. Its Assumption 1 holds because $Q$ takes
both signs. The only exceptional case requires a zero quadratic
constraint matrix and nonzero linear constraint; our constraint matrix
is the nonzero $Q$. It supplies finite $\nu_4$ with

$$
R_4+\nu_4Q\succeq eI\succ0.
\tag{RC.29}
$$

There is also a precise algebraic choice: sort the distinct real roots
of the cubic $\det(R_4+\nu Q)$, test the three leading Sylvester minors
at each adjacent midpoint, and take the midpoint whose three minors
are positive. The PD set is a nonempty convex open interval. It is
bounded since $Q$ has both signs; its finite endpoints are consecutive
determinant roots. Since $\det Q\ne0$, the cubic is not identically
zero. Thus this prescription selects a finite scalar for every $a>0$
in the claimed domain, rather than omitting a dual block.

Complementarity now gives $S_AA=S_{-,+}B=S_{-,-}C_0=0$.
Taking traces, using all three null constraints, yields

$$
\operatorname{tr}Y-\lambda\tau(a)
=\operatorname{tr}G-2\operatorname{tr}(GC_0)
=\operatorname{tr}G-\frac{g}{H\mathcal E}.
\tag{RC.30}
$$

The left side bounds every feasible original four-tuple above: its gap
is the sum of the four nonnegative slack pairings plus
$\lambda(\sum r(X_{r,\epsilon})_{01}-\tau)$. Equality proves the
original global optimum and (RC.13), without restricting competitors
to the proposed ranks or canonical channel. $\square$

## 62. Exact contact rays, weights, uniqueness and coverage

**Theorem 62.1 (four contacts and unique optimizing aggregates).** For
$0\leq a<a_\dagger$ the aggregate ranks are $(2,1,1)$. At
$a=a_\dagger$ they are $(1,1,1)$. The two $A$ contacts, normalized to
coordinate $0$ equal to one, are

$$
\begin{aligned}
v_\pm&=\frac{-\alpha W_0W_2\pm W_1\sqrt{N_Q}}
                    {\alpha W_2^2+\beta W_1^2},\\
u_\pm&=-\frac{W_0+W_2v_\pm}{W_1},\qquad
q_\pm=(1,u_\pm,v_\pm)^T,\\
w_+&=\frac{A_{02}-v_-A_{00}}{v_+-v_-},\qquad
w_- =\frac{v_+A_{00}-A_{02}}{v_+-v_-}.
\end{aligned}
\tag{RC.31}
$$

There are four distinct real null lines
$\mathbb Rq_+,\mathbb Rq_-,\mathbb Rn,\mathbb RZ$, and

$$
A=w_+q_+q_+^T+w_-q_-q_-^T,
\qquad w_\pm>0\quad(0\leq a<a_\dagger).
\tag{RC.32}
$$

For $0<a\leq a_\dagger$ the tuple in (RC.12) is the unique original
optimizing aggregate tuple at its contrast. Uniqueness here does not
mean uniqueness of the complete output instrument.

Proof. The restriction of $Q$ to $W^\perp$ is indefinite because

$$
N_Q=-\alpha\beta W^TQ^{-1}W>0.
$$

It has exactly two distinct real null lines. Eliminating $u$ from
$W_0+W_1u+W_2v=0$ and $\alpha u^2+\beta v^2=1$ gives (RC.31).
Its denominators are positive by Proposition 60.2.
Furthermore $W_1>0$, $W_2\geq0$, and $W_0<0$ follows from
$W_0=D(U/2-2\beta ak)$. The bound
$\beta W_0^2-W_2^2>0$ implies
$W_0+W_2v<0$ for every null $v$, since $|v|\leq1/\sqrt\beta$.
Consequently $u_\pm>0$. The other two lines are distinct from each
other by $n^TQZ\ne0$, and from $W^\perp$ by
$n^TW=D\sigma\ne0$, $Z^TW=\mathcal E\ne0$.

By (RC.22), $A$ is supported on $W^\perp$. Write a symmetric matrix
on this plane in the basis $q_+,q_-$. Both diagonal $Q$ pairings vanish
and the mixed one is nonzero, since the restricted form is indefinite
and nondegenerate. Thus $\operatorname{tr}(QA)=0$ eliminates the
mixed coefficient. Positivity forces the two remaining coefficients
nonnegative; rank two forces both strictly positive. Entries $00,02$
then give exactly the weights in (RC.31). At $a_\dagger$ precisely one
of them vanishes. The ranks follow from (RC.22).

Fix the dual of Theorem 61.1 at $a>0$. Any original optimizer must
annihilate all its slacks; its fourth block is zero by (RC.29), its
$B,C_0$ are supported on $n,Z$, and its $A$ on $W^\perp$.
The null-trace constraint therefore confines it to these same four
rank-one projectors. Four distinct projectors on this real null conic
are linearly independent. To prove this directly, normalize a ray as

$$
(1,\cos\vartheta/\sqrt\alpha,\sin\vartheta/\sqrt\beta).
$$

The independent projector coordinates are equivalent to
$1,\cos\vartheta,\sin\vartheta,\cos2\vartheta,\sin2\vartheta$.
A nonzero polynomial in this trigonometric system has at most four
distinct circle zeros: multiply by $e^{2i\vartheta}$ to obtain a
nonzero polynomial of degree at most four. Hence evaluation at any
five distinct points is invertible. Add any fifth point to the four
in question; independence of the five evaluation columns implies
independence of the original four. Their sum being $I$ therefore
uniquely determines their coefficients, including when one is zero.
This proves aggregate uniqueness also at $a_\dagger$. $\square$

**Theorem 62.2 (bijective contrast coverage and derivatives).** Put
$\tau_c=\tau(a_\dagger)$. The map $a\mapsto\tau(a)$ is a continuous
strictly decreasing bijection

$$
[0,a_\dagger]\longrightarrow[\tau_c,1].
\tag{RC.33}
$$

For every $\tau_c<\tau<1$ there is therefore one exact selected
algebraic $a$ and one exact selected $k$, and (RC.13) evaluates the
original optimum. The interior multiplier is continuous and

$$
j'(\tau)=-\lambda,\qquad
\frac{d\mathcal T(s_0\tau)}{d\tau}=-\lambda/2,\qquad
\frac{d\mathcal T(s)}{ds}=-\lambda/(2s_0).
\tag{RC.34}
$$

Proof. At $a=0$ direct evaluation of (RC.12) gives

$$
\begin{aligned}
B(0)&=\tfrac14(1,-1,1)(1,-1,1)^T,\\
C_0(0)&=\tfrac14(1,-1,-1)(1,-1,-1)^T,\\
A(0)&=\begin{pmatrix}1/2&1/2&0\\1/2&1/2&0\\0&0&1/2\end{pmatrix},
\qquad\tau(0)=1.
\end{aligned}
\tag{RC.35}
$$

This endpoint is the inherited optimal endpoint primal of JR Theorem
51.4. For $a>0$ the normalized $B$ ray has

$$
\frac UD=-1+\frac{2\beta a}D\in(-1,0),\qquad
\frac d{da}\frac{2\beta a}D=\frac{2\beta V}{D^2}>0.
\tag{RC.36}
$$

Its positive coefficient weight prevents equality in
$\sum\pi|u|\leq\sqrt{(\sum\pi)(\sum\pi u^2)}=1$:
equality would require every positive ray to have $|u|=1$.
The reports are aligned, as in Lemma 53.2, so $\tau(a)<1$.
Different $a$ give different $B$ rays and hence different aggregates.
If two positive parameters had the same contrast, Theorem 62.1's
uniqueness at that contrast would contradict this difference.
Together with $\tau(a)<1$ this proves continuity and injectivity on
the closed interval. A continuous injective real function on an
interval is strictly monotone; its endpoint $1$ forces decrease.
This proves (RC.33) with no unexamined gap in the contrast domain.

Each finite certificate supplies the global support inequality
$j(\tau')\leq j(\tau)-\lambda(\tau'-\tau)$.
Use it at the two ends of a difference quotient. The inverse in
(RC.33) is continuous, and (RC.23) is continuous for $a>0$, so the two
support slopes tend to the same $-\lambda$. This proves (RC.34)
without assuming $\tau'(a)\ne0$. These multipliers are normalized
for $j$; neither the CG root multiplier nor JR's spectral-plateau
multiplier is this $\lambda$. $\square$

## 63. Identification of the first zero and quantitative gluing

**Proposition 63.1 (the first vanishing factor).** Use exactly JR.140–.143's
frame, $h,\psi,d_-,d_+,d_N$ and their scales. Then

$$
\begin{gathered}
1.04175447537<t_\dagger<1.04175447539,\\
.9962433511188<\tau_\dagger<.9962433511192,\\
d_+(t_\dagger)=0,\quad d_-(t_\dagger)>0,\quad d_N(t_\dagger)>0,
\quad d_+'(t_\dagger)<0,\\
.0460291518<\lambda_\dagger<.0460291520,\qquad
.0081796784563<j(\tau_\dagger)<.0081796784566.
\end{gathered}
\tag{RC.37}
$$

Proof. These refinements require the entire source box, not JR.86 alone.
For a fully specified interval comparison use the 384 closed cells

$$
\left[\frac{1700+i}{2000},\frac{1701+i}{2000}\right],
\quad i=0,\ldots,383,
\tag{RC.38}
$$

whose union is $[.85,1.042]$. Substitute JR.140, using its positive
radicals and rationalized frame root. Write
$M_{\rm fr}=F^TGF$, $c=F^TCF$, $q=F^TQF$ and evaluate the multiplier
by the algebraically identical formula

$$
\lambda(t)=
\frac{(M_{\rm fr})_{02}/q_{02}-(M_{\rm fr})_{01}/q_{01}}
{c_{01}/q_{01}-c_{12}/q_{12}}=2\psi'(t)/h'(t).
\tag{RC.39}
$$

This avoids numerical differentiation. Form $d_-,d_+,d_N$ by JR.142.
Propagate the value and exact first derivative by the sum, product,
quotient rules, with $(\sqrt v)'=v'/(2\sqrt v)$, initializing $t'=1$.
Use Definition 60.1 for each value/derivative interval. All radicals are
positive and every divisor excludes zero on every cell. The resulting
uniform strict comparisons are

$$
d_->1/2000,\qquad d_N>3\cdot10^{-6},\qquad d_+'<-3/5000.
\tag{RC.40}
$$

For example smaller bounds than the respective aggregate lower,
lower and negative-upper margins are $.00052123$,
$.0000043166$ and $-.00072074$. The endpoint comparisons are

$$
\begin{aligned}
d_+(1.04)&>1.95\cdot10^{-6},&d_+(1.042)&<-2.7\cdot10^{-7},\\
d_+(1.04175447537)&>10^{-14},&
d_+(1.04175447539)&<-10^{-14}.
\end{aligned}
\tag{RC.41}
$$

These are direct rational interval substitutions, with the same
complete $\mathcal B_7$. Thus $d_+$ has precisely one zero on this
interval, it is simple, and neither other factor vanishes there.
JR's $t_*\in(.85,.9)$ and its least-zero definition identify that root
with $t_\dagger$. Substituting the entire narrow $t$ bracket into
$h$, (RC.39), and $\operatorname{tr}G-2\psi$ gives, respectively,

$$
\begin{gathered}
(.9962433511188805,.9962433511191363),\\
(.04602915183020,.04602915189613),\\
(.0081796784563517,.0081796784565250),
\end{gathered}
$$

which imply (RC.37). This identifies and refines the boundary of the
already proved initial branch; it does not repeat its optimality proof.
$\square$

**Theorem 63.2 (gluing, contact uniqueness and genuine onset).**
The boundary in (RC.19) satisfies

$$
\frac{Z_2}{Z_1}(a_\dagger)=t_\dagger,\qquad
\tau_c=h(t_\dagger)=\tau_\dagger.
\tag{RC.42}
$$

The two exact value branches and their normalized multipliers agree
there, so the value is $C^1$ at this finite contact. At the contact the
unique aggregate is the original three orthogonal rank-one null
projections. The fourth distinct contact has zero weight. Immediately
above $\tau_\dagger$, and throughout $\tau_\dagger<\tau\leq1$,
there are four distinct positive real-null atoms and aggregate ranks
$(2,1,1)$. There is no later interior support or rank transition.

Proof. At $a_\dagger$ three positive rank-one matrices sum to $I$;
putting their scaled vectors into a square matrix proves that these
vectors form an orthonormal basis. Their negative-height column is
$f_0=-Z/\|Z\|$, and its last-coordinate ratio is in (RC.20).
Its first coordinate is positive, its last two negative. The $A$ ray
has positive $01$ product by (RC.31); the $B$ ray has negative product
by $U<0$. The unsquared branch and sign choices in JR.140 therefore
identify the frame, in $(C_0,A,B)$ order, with JR's $F(t_c)$,
$t_c=Z_2/Z_1$.

Gauge the new dual by $Y\mapsto Y+\nu_CQ$,
$\nu_i\mapsto\nu_i-\nu_C$, so that $\nu_C=0$.
Complementarity with the three frame columns imposes exactly the
linear equations JR.146–.148. Their remaining compatibility equation
fixes $\lambda=2\psi'(t_c)/h'(t_c)$, since $h'(t_c)>0$.
The ranks of the three active slacks are $(1,2,2)$ in $(A,B,C_0)$
order by Theorem 61.1. Their compression determinants are respectively
$4\lambda d_+$, $4\lambda d_-$ and $4d_N$. Thus
$d_+(t_c)=0$, $d_-(t_c),d_N(t_c)>0$. Proposition 63.1 and (RC.20)
force $t_c=t_\dagger$. Equation (RC.30) then matches JR.150's value;
(RC.39) matches its multiplier. The two support-slope arguments give
$C^1$ gluing. This is at the finite contact, not at $\tau=1$.

For precision, the reduced active dual is unique at the contact after
fixing $\nu_C=0$. For any optimal reduced dual, complementarity with
$f_0,f_1,f_2$ imposes the three kernel equations. The first fixes the
first column of $F^TYF$; the other two determine all its remaining
entries and $\nu_A,\nu_B$ as JR.146. Their compatibility determines
$\lambda$ by the nonzero denominator of (RC.39). This leaves no
freedom in the reduced dual. The original fourth scalar is allowed to
vary and is not claimed unique. Aggregate uniqueness at the contact
already follows from Theorem 62.1, including the zero coefficient.

It remains to identify which weight vanishes and quantify its onset.
At $t=t_\dagger$ use $M_{\rm fr},c,q$ of (RC.39), put

$$
\begin{aligned}
k_+^{\rm fr}&=q_{02}c_{12}/q_{12}-c_{02},\\
a_g&=-\lambda_\dagger k_+^{\rm fr},\qquad
b_g=-(M_{\rm fr})_{00}-\lambda_\dagger c_{00},\\
g_{\rm loc}&=a_g f_0+b_g f_2,\\
z_{\rm raw}&=g_{\rm loc}
 -\frac{g_{\rm loc}^TQg_{\rm loc}}{2f_1^TQg_{\rm loc}}f_1,
\qquad z_{\rm new}=z_{\rm raw}/\|z_{\rm raw}\|.
\end{aligned}
\tag{RC.43}
$$

The rank-one compression in JR.148 annihilates $g_{\rm loc}$.
Its kernel plane contains $f_1$ and $g_{\rm loc}$; (RC.43) produces
the second null line because $f_1^TQf_1=0$. The same interval rules
on the narrow $t$ bracket give

$$
\begin{gathered}
a_g<0<b_g,\qquad .00048130<f_1^TQg_{\rm loc}<.00048132,\\
.6491799<(z_{\rm new})_0<.6491801,\\
.6813365<(z_{\rm new})_1<.6813368,\\
.3381503<(z_{\rm new})_2<.3381505,\qquad
z_{\rm new}^TGz_{\rm new}>.00510289.
\end{gathered}
\tag{RC.44}
$$

In particular this contact is nondegenerate and has positive height.
It has positive third coordinate, whereas the old $f_1$ in JR.140 has
negative third coordinate. Therefore it is $\mathbb Rq_+$, and
$w_+(a_\dagger)=0$, $w_-(a_\dagger)>0$. The four projectors are
independent even here; in the frame the new one has a nonzero $02$
entry proportional to $a_gb_g$, whereas the old three are diagonal.

Define

$$
K_A=\|q_+\|^2\|q_-\|^2-(q_+^Tq_-)^2>0.
$$

Taking the product of the two nonzero eigenvalues in (RC.32) gives
$w_+w_-K_A=\omega$. All functions are analytic near $a_\dagger$ and
$\omega'(a_\dagger)<-.9$, whence

$$
\lim_{a\uparrow a_\dagger}
\frac{w_+(a)}{a_\dagger-a}
=\frac{-\omega'(a_\dagger)}{w_-(a_\dagger)K_A(a_\dagger)}>0.
\tag{RC.45}
$$

There is a useful explicit lower onset bound on $7/25\leq a<a_\dagger$.
Here $\omega(a)>.9(a_\dagger-a)$ by (RC.19), $w_-\leq A_{00}\leq1$,
and $\|q_\pm\|^2\leq1+1/\beta<10$, so $K_A<100$. Consequently

$$
w_+(a)>\frac9{1000}(a_\dagger-a).
\tag{RC.46}
$$

The strict rank-two property for every smaller $a$, and the four-line
independence and positive weights of Theorem 62.1, prove the genuine
three-to-four transition and absence of any later interior transition
on the entire contrast interval supplied by (RC.33). Its minimum
real-null rank-one atom count is exactly four: each optimizing aggregate
requires at least its rank, and the actual decomposition has four.
At $\tau=1$ this uses the inherited endpoint corner rigidity of
JR.157–.158 and JR Theorem 43.2, with the same four weights and sectors.
At the contact it is three, with a fourth exposed zero-weight line.
These conclusions concern the normalized coefficient face, not a
minimum physical acquisition alphabet with arbitrary multi-Kraus
labels. $\square$

## 64. Endpoint identification and inherited quantitative law

**Proposition 64.1 (same endpoint, normalizations and coefficient).**
As $a\downarrow0$ the four normalized rays reach
$(1,1,1)$, $(1,1,-1)$, $(1,-1,1)$ and $(1,-1,-1)$, each with
coordinate-$0$ coefficient weight $1/4$. Put

$$
\xi=2\beta a/D,\quad c_-=(1,-1,-1)^T,\quad
f_-=c_-^TGc_-<0,\quad
\mathcal D=(Gc_-)_1-\alpha(Gc_-)_0>0.
\tag{RC.47}
$$

Then

$$
k_0=k(0)=-\frac{f_-}{4\mathcal D},\qquad
L_\xi=\lim_{\xi\downarrow0}\lambda\xi=\frac{\mathcal D}{\beta}.
\tag{RC.48}
$$

The branch has $1-\tau=e_2\xi^2+O(\xi^3)$, where

$$
e_2=\frac18\left[(4\alpha k_0-1)^2+(4k_0-1)^2+1+
 (3-4(1+\alpha)k_0)^2\right]>0,
\tag{RC.49}
$$

and $L_\xi\sqrt{e_2}$ is exactly JR.155's $\Gamma$.

Proof. Equation (RC.11) gives (RC.35); the plane $W^\perp$ at zero
has $u=1$ and its two null lines have $v=\pm1$. The weights follow
from the $00,02$ entries of $A(0)$; those of $B,C_0$ follow from
(RC.35). Expanding the exact polynomial divisions at $a=0$ gives

$$
\mathcal P(0,k)=-\frac{\beta^5\alpha^{18}}{32}
 (4\mathcal Dk+f_-),\qquad
\ell_1(0,k)=-\frac{\beta^4\alpha^{13}}2k.
\tag{RC.50}
$$

These follow by retaining the coefficients of $a^1$ in (RC.8), since
the constant terms already vanish by (RC.11). The first identity fixes
$k_0$; substituting the second and (RC.11) into
$-gD^2\sigma\xi/(a\ell_1)$ yields
$-f_-/(4\beta k_0)=\mathcal D/\beta$, proving (RC.48).

The auxiliary contact derivative has a normalization that matters.
Use

$$
c_{\rm aux}=\frac{Z}{\beta D^5},\qquad c_{\rm aux}(0)=-c_-/4.
$$

For $b=n/D=(1,-1+\xi,\sqrt{(1-\alpha(-1+\xi)^2)/\beta})$ put
$w=W/D^2=Cb-\xi kQb$. Then
$\mathcal H=C-ww^T/(b^TCb)$. Differentiating at $\xi=0$ gives

$$
\left.\frac d{d\xi}(\mathcal Hc_{\rm aux})\right|_0
=\tfrac14(1-3k_0,\ 1-3\alpha k_0,\ \beta k_0)^T.
\tag{RC.51}
$$

For coordinate-$0$-one normalization $\widehat c=Z/Z_0$, the derivative
of $\mathcal H\widehat c$ is $-4$ times (RC.51): the derivative of the
normalizing scalar contributes zero because
$\mathcal H(0)c_{\rm aux}(0)=0$. This explicitly distinguishes the two
vectors. The scalar root $k_0$, $L_\xi$ and $\Gamma$ are invariant.
For an additional check of (RC.48), the limiting contact equation paired
with $c_-$ gives $f_-=-4\beta k_0L_\xi$, and subtracting $\alpha$
times coordinate $0$ from coordinate $1$ gives
$\mathcal D=\beta L_\xi$.

For completeness the four derivatives of $|u|$ in corner order
$(++),(+-),(-+),(--)$ are

$$
s_{++}=4\alpha k_0-1,\quad s_{+-}=4k_0-1,\quad
s_{-+}=-1,\quad s_{--}=3-4(1+\alpha)k_0.
\tag{RC.52}
$$

The $B$ ray gives $s_{-+}=-1$ directly. The $W^\perp$ equation with
$v(0)=\pm1$ gives the first two, and the normalization identity
$\sum\pi u^2=\sum\pi=1$ gives $\sum s=0$, hence the fourth.
The exact moment identity is
$1-\tau=\tfrac12\sum\pi(|u|-1)^2$. Analyticity and the limiting
weights $1/4$ therefore prove (RC.49). In JR.155 notation,
$\mathcal D=R_1$ and $f_-=-(R_1+R_2)$. Substitution of
$4k_0=(R_1+R_2)/R_1$ into (RC.52) gives, for each corner,

$$
L_\xi s_{\sigma\eta}=-b_{\sigma\eta}.
\tag{RC.53}
$$

Thus $L_\xi^2e_2=\tfrac18\sum b_{\sigma\eta}^2=\Gamma^2$;
positivity selects $L_\xi\sqrt{e_2}=\Gamma$. $\square$

**Corollary 64.2 (inherited endpoint attainment and dual boundary).**
This exact branch has the same endpoint primal and quantitative
square-root law as JR Theorems 51.4, 55.2 and 55.3. In particular,
for $0<\varepsilon\leq10^{-8}$,

$$
T_0+\Gamma\sqrt\varepsilon-15\varepsilon
\leq\mathcal T(s_0(1-\varepsilon))
\leq T_0+\Gamma\sqrt\varepsilon+11\varepsilon,
\quad T_0=T_{\rm flat}-f_-/4.
\tag{RC.54}
$$

Every optimal normalized multiplier has JR.172's limit $\Gamma$ and
remainder estimate. At $\tau=1$ the finite four-atom primal is attained
and the original dual infimum equals it, but there is no finite
original dual minimizer. Equations (RC.23)–(RC.24) apply only for $a>0$.

Proof. Proposition 64.1 identifies the exact branch and the coefficient
with the inherited endpoint objects, so the existing bounds and
all-multiplier theorem apply directly; no new endpoint-bound proof is
needed. In particular $f_-/4$ is JR.50's $\mathsf b(1)$.
The scale in (RC.34) gives
$\mathcal T-T_0=L_\xi e_2\xi+O(\xi^2)$, not twice this amount.
Equivalently its square-root coefficient is $\Gamma$.
The endpoint nonattainment of the dual and equality of its infimum
are exactly JR Theorems 51.4 and 55.3, and are consistent with
$\lambda\xi\to L_\xi>0$. The finite contact of §63 has neither this
divergence nor this failure of finite dual attainment. $\square$

## 65. Actual common instruments and exact original output correspondence

**Definition 65.1 (finite generated labels).** For each selected
$0\leq a\leq a_\dagger$, take the coefficient vectors

$$
\begin{aligned}
h_+&=\sqrt{w_+}\,q_+,&h_-&=\sqrt{w_-}\,q_-,\\
h_B&=\sqrt{-R/(2D\sigma H)}\,n,&
h_C&=Z/\sqrt{2H\mathcal E}.
\end{aligned}
\tag{RC.55}
$$

Omit $h_+=0$ at $a_\dagger$. Each remaining vector is nonzero and

$$
\sum_i h_ih_i^T=I,\quad h_i^TQh_i=0,\quad
c_i=Lh_i,\quad K_i=(c_i)_0D_{\rm src}+(c_i)_1T_{\rm src}+(c_i)_2S_{\rm src}.
\tag{RC.56}
$$

The actual low reports are $r_+=r_-=+1$, $r_B=r_C=-1$.
Before arrival of the unknown specimen fix the image isometry
$V_i:\mathbb C^2\to\operatorname{ran}K_i$ by IR.22.
Generate and dephase label $i$ with encoder
$V_i^\dagger K_iE^\dagger$; its decoder on the entire declared fibre
is $X\mapsto EV_iXV_i^\dagger E^\dagger$.

Add two high encoders
$\sqrt{(1-\delta)/2}\,D_{\rm src}E^\dagger$, with fair reports and
whole-$M_3$ decoder $X\mapsto EXE^\dagger$.
Let $v_+,v_-$ be fixed real unit eigenvectors of
$\Xi=M_f^{1/2}\Delta M_f^{1/2}$ on coordinates $1,2$.
For each $\epsilon,r=\pm1$ use the scalar spectral row
$2^{-1/2}\langle v_\epsilon|M_f^{1/2}E^\dagger$, report $r$, and
scalar decoder $z\mapsto zw_\ell g_{\rm time}(t)dt\,P_f$ at each
original failure label. Finally use two fair-report scalar complement
encoders $X\mapsto\tfrac12\operatorname{tr}((I-P)X)$, each decoded
as $zg_{\rm time}(t)dt\,P_f$ at label $2$ only. The internal complement
Kraus multiplicity is permanently discarded. This is precisely JR
Definition 53.3 with the exact new coefficient atoms substituted.

**Theorem 65.2 (all-complex/reference/five-Borel identity and all histories).**
At the conditional source root, Definition 65.1 is one common finite
instrument with whole-fibre TP decoders and total encoder effect $I_5$.
For every complex matrix $X\in M_5$, $X_V=E^\dagger XE$, its forgotten
live map and its failure measure for every Borel $\mathcal B\subseteq[0,1]$
are exactly

$$
\begin{aligned}
\widehat\Phi^L(X)
 &=E[D_{\rm src}X_VD_{\rm src}^\dagger+
       T_{\rm src}X_VT_{\rm src}^\dagger+
       S_{\rm src}X_VS_{\rm src}^\dagger]E^\dagger,\\
\widehat\Phi^f_\ell(\mathcal B)(X)
 &=\left(\int_{\mathcal B}\frac{2\,dt}{(1+t)^2}\right)
 [w_\ell\operatorname{tr}(M_fX_V)
  +\mathbf1_{\ell=2}\operatorname{tr}((I-P)X)]P_f,
\quad \ell\in\{0,1,2,3,13\}.
\end{aligned}
\tag{RC.57}
$$

These are CP-map identities with arbitrary passive-reference
amplification and the original conditional reference partial traces.
Every one of the twelve original history errors is unchanged; their
maximum remains $E_*$. This does not assert that each individual
history has error $E_*$.

Proof. Every nonzero real null vector has nonzero coordinate $0$.
The determinant identity JR.22 applied to (RC.56) gives $\det K_i=0$;
the lower-right minor $h_1h_2(c_i)_0^2\ne0$ gives rank exactly two.
Thus IR Lemma 4.2's fixed image isometry exists and its decoder is TP
on all $M_2$, not merely the encoded support. Its composite live
matrix is $EK_iE^\dagger$. The coefficient Gram is

$$
\sum_i c_ic_i^T=\operatorname{diag}(\delta,1,1),\qquad
\operatorname{diag}(\delta,1,1)+(1-\delta)e_0e_0^T=I_3.
\tag{RC.58}
$$

Expansion in the three source Kraus matrices proves (RC.57)'s live
identity on every complex matrix unit. No equality of an entry and its
complex conjugate is assumed. The total live effect is $I_3-M_f$ by
the exact root identity CG.141. The four spectral rows sum to $M_f$;
the complement adds $I-P$, giving total effect $I_5$. Every encoder
branch is CP/TNI since its positive effect is bounded by this total.
The scalar decoders are TP because $\int_0^1g_{\rm time}=1$ and
$\sum_\ell w_\ell=1$. The high and low isometric decoders are TP on
their entire declared fibres.

Summing the spectral rows gives $\operatorname{tr}(M_fX_V)$ and
summing the complement gives $\operatorname{tr}((I-P)X)$ at original
label $2$ only. Integration of their specified scalar decoders proves
the second identity for every Borel set, separately for all five labels,
including zero-target labels $0,13$. There are no additional singular
measures. Cross-support terms are annihilated, as in CG.142.

Tensor every finite Kraus identity with $I_R$ for a passive reference.
The scalar traces in the failure formula become respectively

$$
\operatorname{Tr}_5[(EM_fE^\dagger\otimes I_R)X],\qquad
\operatorname{Tr}_5[((I-P)\otimes I_R)X],
\tag{RC.59}
$$

which are conditional reference operators, not the unconditional
reference marginal. This proves the full complex/reference/Borel
correspondence, rather than only probabilities on twelve inputs.
Consequently the forgotten channel is exactly the credited CG/JR
channel, with all twelve HALF complete-cq errors preserved. Its actual
common density $g_{\rm time}$ has not replaced any ideal $f_y$.
The TP step uses CG.141 at the source root; none of it is inferred
from an arbitrary off-root comparison point. $\square$

**Theorem 65.3 (actual contrast, attained TV and sharp joint cost).**
The actual generated instrument has

$$
\mathsf V=s_0\tau(a),\quad
\mathsf W=(1-\delta)A_{27}=\mathsf C(s_0\tau(a)),\quad
\operatorname{TV}(P^R_{5,+,+},P^R_{27,+,+})
=T_{\rm flat}-\frac{g}{2H\mathcal E}.
\tag{RC.60}
$$

It has twelve physical acquisition labels for $0\leq a<a_\dagger$
and eleven at contact. These are construction counts, not universal
lower bounds for physical-label alphabets.

Proof. The $A$ contacts have $u>0$, hence positive height by JR.133;
$n^TGn>0$ and $Z^TGZ<0$ by Proposition 60.2. Thus the four low
height signs in (RC.55) are $(+,+,+,-)$ and their actual reports are
$(+,+,-,-)$. They are individually aligned with their $01$ products.
The low contrast moment is
$\sum r_i(h_i)_0(h_i)_1=2A_{01}=\tau$; high, failure and complement
reports are fair. JR.136 therefore gives $\mathsf V=s_0\tau$,
which satisfies exactly the original contrast inequality with equality.
No other effect entry is imposed.

For coordinate-$0$-one rays $q_i=(1,u_i,v_i)$ write
$h_i=\sqrt{\pi_i}q_i$. Their exact coefficient weights are

$$
\pi_+=w_+,\quad\pi_-=w_-,\quad
\pi_B=-\frac{RD}{2\sigma H},\quad
\pi_C=\frac{Z_0^2}{2H\mathcal E}.
\tag{RC.61}
$$

Their actual Born probabilities on a history are instead

$$
p(i\mid y,e,n)=\|K_iU_{e,n}a_y\|^2.
\tag{RC.62}
$$

The weights satisfy $\sum\pi_i=1$ and are not input priors or
acquisition probabilities. A unit-vector presentation has outer-product
weight $\pi_i\|q_i\|^2$, again not a Born probability. At contact the
three surviving unit-vector weights are $1$; at the contrast endpoint
the four coordinate-$0$-one weights are $1/4$.

Because these low labels are actually generated and retained, their
absolute height-difference sum is
$\operatorname{tr}(GA)+\operatorname{tr}(GB)-\operatorname{tr}(GC_0)
=j(\tau)$. The two generated high labels contribute
$(1-\delta)\Delta A$, and the spectral failure readout contributes
$\|\Xi\|_1=L_f$; complement contributes zero on the supported histories.
HALF their sum is (RC.60)'s TV. For arbitrary original instruments,
analytic refinement yields only an upper inequality. In particular the
endpoint gain relation is
$T_{\rm instr}-T_0\leq-\mathbb E\mathfrak r$ with $\mathfrak r$
defined by JR.159;
equality requires the actually generated refined labels and optimal
spectral failure readout. It is valid for this construction, not for a
hidden Kraus index of another realization.

Only the two high fibres have dimension at least three. Their total
probability is $(1-\delta)A_y$ on every $(y,e,n)$, maximized at $27$.
JR §§34–40 proves that this is the sharp original worst-history cost,
not merely the cost within the canonical-channel family. All
future-accessible input-bearing specimen, memory, quantum controller,
environment, return systems and entanglement shares count jointly in
each fibre at this same cut. Unretained dilation systems are permanently
inaccessible; retaining one would change the resource accounting.
There are four low, two high, four spectral and two complement labels,
or one fewer when $h_+=0$. Multi-Kraus physical labels can group
products, so neither this count nor the four real contact rays proves
a physical-label minimum. $\square$

## 66. Mathematical correspondence and remaining original scope

**Convention 66.1 (precise continuation).** The new source-specific
relations are the selected complete post-contact curve (RC.8)–(RC.33),
its four original matching dual blocks, the identified simple first
$d_+$ zero with quantitative gluing, and the exact positive four-contact
weights with no later interior transition. In combination with JR.144,
the residual value is now specified throughout by

$$
j(\tau)=
\begin{cases}
\operatorname{tr}G-2\psi(t),&\tau=h(t),\quad t_*\leq t\leq t_\dagger,\\
\operatorname{tr}G-g/(H\mathcal E),&\tau=\tau(a),\quad0\leq a\leq a_\dagger.
\end{cases}
\tag{RC.63}
$$

The plateau and strong-regime branches retain JR §§43,50–51's exact
hypotheses and values. JR §§53–57's initial optimality, endpoint
square-root estimates, every-multiplier bounds and pre-cap obstruction
are reused, not supplied anew. The root-specific ranks, source
normalization and minimax identification remain CG antecedents; the
sharp joint-cost attribution remains JR §§34–40. The real-face and
image-decoder mechanisms are CA Theorem 5.1 and IR Lemma 4.2.
The equality S-lemma [SLEM] supplies only the fourth-slack completion,
under the explicit sign-changing quadratic hypotheses used in §61.
Bernstein positivity, inertia, conic contact independence and finite
Kraus bilinearity are intermediate classical tools. No generic moment
quadrature or extremal-POVM rank bound supplies the source-specific
optimum; in particular a full-arc Chebyshev hypothesis would fail for
a system containing $|u|-u$, which vanishes on an open half arc.
The source-specific synthesis is repository-derived; no literature-wide
priority or new classical S-lemma claim is made.

The [AS all-strength selected-input law][AS] fixes a complete channel and
complete binary effects and minimizes acquired mass on an admitted
selected input. Here the objective is height-record TV at sharp
worst-history cost over all original error optimizers, with only a
contrast inequality. The [critical-energy response][CE] concerns a
full complex differential-operator domain and its same-realization
energy coefficient, not acquired payload probability. No value,
optimizer, exponent, control or resource conclusion transfers among
these objectives without an established correspondence. Their own
remaining questions retain their original domains.

All conclusions here are ordinary conditional mathematics, not
Lean/kernel certification or native execution. Lawful access to the sole
unknown specimen, D/T/S calibration, coherent storage of all jointly
accessible shares, controlled decoding, one aligned clock, actual FIRST
absorbing failure with no subsequent positive-carrier action, terminal
live output, archive/controller/permission semantics and actual joint
resource accounting remain unresolved native bridges. OriginalControl
is geometric, not an actuator. Noncommuting probability-phase controls
do not justify an exhaustive Schur control menu. The unchanged
quantum-first through-2027 programme, including its native and
joint-height/clock questions, remains active; the finite conditional
residual/contact theorem does not establish programme completion.

[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[IR]: FIB_NATIVE_INTERIOR_RECORD_RESOURCE_REDUCTION.md
[CA]: FIB_NATIVE_COMPLEX_ATOMIC_CONE_AND_OPTIMAL_RESOURCE_FACES.md
[AS]: FIB_NATIVE_NONREAL_ALL_STRENGTH_ACQUISITION_RESOURCE_LAW.md
[CE]: FIB_NATIVE_EXACT_CRITICAL_ENERGY_RESPONSE_AND_SCALE_ALTERNATIVES.md
[SLEM]: https://arxiv.org/pdf/1403.2816v3

## 追加锚（本行以下为增补区）

## 67. Finite-budget contact geometry in the original weak class

**Convention 67.1 (objects, antecedents and inherited results).** Retain
Convention 58.1, the source dictionary (RC.1)–(RC.5), the original
contrast inequality, and the sharp worst-history cost of jointly acquired
dimension at least three. The source-root existence, isolation,
Jacobian, rank, TP normalization and minimax identifications remain CG
antecedents. The following are ordinary conditional mathematics at that
source, with no assertion of Lean/kernel or native certification.

Write $D=D_{\rm src}$, $T=T_{\rm src}$, $S=S_{\rm src}$ and abbreviate
their amplitudes by $a,b,c,d$ respectively. Here $b$ is the source
amplitude in $T$, not a label's failure ratio. Use $x_G,y_G,z_G$ for
$x,y,z$ in (RC.2); coordinates of a contact remain $z,w$. Put

$$
\begin{gathered}
\mathscr C=\{h=(1,z,w)^T:\alpha z^2+\beta w^2=1\},\quad
K_h=s_0D+zT+wS,\quad \ell(h)=h^TGh,\quad H_0=(1-\delta)N_{00},\\
\widehat n_h=(dw/h_2,-bz/h_1)^T,\quad n_h=(0,\widehat n_h^T)^T,\quad
\Delta_f=\begin{pmatrix}-11/64&(\sqrt{37}-\sqrt{59})/16\\
(\sqrt{37}-\sqrt{59})/16&0\end{pmatrix},\quad
f(h)=\widehat n_h^T\Delta_f\widehat n_h,\\
\mathcal D(h)=h_0^2\delta+b^2z^2+d^2w^2,\qquad
\mathcal N(h)=h_1^2h_2^2\delta+a^2h_2^2z^2+c^2h_1^2w^2,\\
c(h)=\mathcal N(h)/\mathcal D(h),\quad
c_*(u)=c\left(1,\sqrt u,\sqrt{(1-\alpha u)/\beta}\right),\quad
C(h)=t c(h),\quad t=e^A-1.
\end{gathered}
\tag{RC.64}
$$

Both $\mathcal D$ and $\mathcal N$ are strictly positive on the circle.
The quantity $C(h)$ is a scalar capacity, distinct from the matrix $C$
in (RC.2). On failure support put

$$
\begin{gathered}
M_2=\operatorname{diag}(m_1,m_2),\quad
\Xi=M_2^{1/2}\Delta_fM_2^{1/2}
=\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},\\
d_f=11m_1/64,\quad z_f<0,\quad
L_f=\sqrt{d_f^2+4z_f^2},\\
V=m_2h_1^2/b^2,\quad W=m_1h_2^2/d^2,\quad
\mu=\alpha V+\beta W,\quad u_f=V/\mu,\quad v_f=W/\mu,\\
c_f=c_*(u_f),\quad \nu=\mu/c_f,\quad t_0=W/c_f,\quad
\tau=s/s_0,\quad q=\nu/t,\\
\tau_{\max}(t)=q\sqrt{u_f}+\sqrt{(1-q)(1-qu_f)}.
\end{gathered}
\tag{RC.65}
$$

These are FA's $V_f,W_f,\mu,u_f,v_f,c_f,\nu$. In particular
$0<V<W$, $\alpha u_f+\beta v_f=1$, and $c_*$ is strictly increasing
on $[0,1/\alpha]$. The spectral eigenvectors of $\Xi$ are whitened
coordinates: their physical effects are
$M_2^{1/2}e_\epsilon e_\epsilon^TM_2^{1/2}$, not the bare projectors.
No spectral direction is silently substituted for $\widehat n_h$.

The original-class reduction used here is [FA69–70, FA72 and FA.37][FA67],
with JR42's all-error-optimizer equality conditions. For an actual CP
encoder $\mathcal E_j$, call its supported restriction
$\mathcal E_j^P(X)=\mathcal E_j(EXE^\dagger)$, $X\in M_3$.
Let $\mathcal J_+(\Phi)$ be the actual low labels with
$\mathcal E_j^P\ne0$, and $\mathcal J_0(\Phi)$ the nonzero actual
low labels with $\mathcal E_j^P=0$. In the stipulated integral case
these are almost-everywhere domains. Every sum over $j$ and every
label coordinate $p_j,h_j,b_j$ in §§67–76 ranges over
$\mathcal J_+(\Phi)$ only. For each such supported-nonzero low label,
its effective supported live product and attached failure effect have,
for $p_j>0$, the form

$$
\begin{gathered}
K_j=\sqrt{p_j}K_{h_j},\qquad
N_j=p_j b_j n_{h_j}n_{h_j}^T,\qquad 0\le b_j\le C(h_j),\\
\sum_jp_jh_jh_j^T=I_3,\qquad
\sum_jp_jb_j\widehat n_{h_j}\widehat n_{h_j}^T=M_2,\qquad
\sum_jp_j|z_j|\ge\tau,\\
2T_{\rm actual}=H_0+\sum_jp_j|\ell(h_j)+b_jf(h_j)|.
\end{gathered}
\tag{RC.66}
$$

Labels in $\mathcal J_0$ have no positive-$p_j$ ellipse direction and
contribute zero to the twelve supported acquisition laws, contrast and
height TV. They remain admitted nonzero full-$M_5$ acquisition outcomes:
[TA Definition 1.2][TA67] counts them in the complete actual alphabet,
and their entire joint fibres still obey the activity bound. No such
label is deleted from the full instrument. FA Definition 77.2 counts
only $\mathcal J_+$ in its low live-bearing minima; full actual-low
and total-alphabet counts also include $\mathcal J_0$.
Indeed $\mathcal E_j^P=0$ implies $C_{ja}E=0$ for every encoder
Kraus matrix $C_{ja}$: the sum of their positive effects on support
is zero. Every composite supported live and failure map then vanishes.
Conversely finite whole-fibre survival ensures that a nonzero supported
encoder has nonzero supported live composition, the domain of FA69.
Thus the two domains exhaust the actual low labels without imposing
an extra restriction on the original full-$M_5$ instrument.

The equality conditions yield the real coefficient directions from the
full complex, multi-Kraus comparison class on this supported-nonzero
domain; real processors are not assumed in the lower bound. For the
admitted countable/measurable extension, sums have their original
integral meaning and the measurable finite-dimensional-fibre hypotheses of Convention 58.1 remain in force.
The common canonical time density is used only to construct attainments.
Necessity retains every admitted failure-time CP measure and TP survivor
control. In particular finite whole-fibre activity gives terminal live
effect at least $e^{-A}I$ by FA68's trace balance, so every nonzero
encoded positive output has positive terminal live mass. This excludes
failure-only full encoders, but does not make a supported-zero encoder
nonzero on support; it leaves $\mathcal J_0$ admitted. The static
certain-failure rows of JR44 would instead need hazard $2/(1-u^2)$
with infinite integral. They do not supply a missing finite-$A$ competitor. At $t=0$, (RC.66) would
force $M_2=0$, so the class is empty.

Endpoint splitting of each supported-nonzero label's $b_j$ into
$0,C(h_j)$, already supplied by FA72, preserves all moments and contrast
and weakly increases height. It yields the attained two-sheet moment
problem with heights
$H_\eta(h)=\ell(h)+\eta C(h)f(h)$, $\eta\in\{0,1\}$. Its value is
$2\mathcal T_A(s)-H_0$. Its feasibility threshold and maximum contrast
are FA78–79's $t_0$ and (RC.65). This is reuse of those results, not a
new survival, feasibility, or compression theorem. The finite-height
continuation's continuous null roof, fixed-allocation rank-at-most-two
formulas, existence of at most nine supported-nonzero low labels plus
one high label, and identity between minimum counts
$n_{\rm total}=n_{\rm low}+1$ retain their separate meanings. Here $n_{\rm low}$ counts $\mathcal J_+$;
the total minimum is attained by putting the complement in the high
fibre. This is not a count identity for every full instrument.
None chooses the full weak finite-budget frontier.

## 68. Attainment of a common dual at every strict interior point

**Theorem 68.1 (finite common multipliers).** Suppose $t>t_0$ and
$0\le\tau<\tau_{\max}(t)$. There are finite real symmetric matrices
$Y\in\operatorname{Sym}_3$, $Z\in\operatorname{Sym}_2$ and
$\lambda\ge0$ such that, on the entire circle,

$$
\begin{aligned}
h^TYh&\ge|\ell(h)|+\lambda|z|,\\
h^TYh+C(h)\widehat n_h^TZ\widehat n_h
&\ge|\ell(h)+C(h)f(h)|+\lambda|z|,\\
2\mathcal T_A(s)-H_0
&=\operatorname{tr}Y+\operatorname{tr}(ZM_2)-\lambda\tau.
\end{aligned}
\tag{RC.67}
$$

Every optimal endpoint family of supported-nonzero low labels is
supported on the corresponding contact equalities and satisfies
$\lambda(\sum p_j|z_j|-\tau)=0$.

**Proof.** Let $\rho_\circ$ be uniform angular probability on
$z=\cos\phi/\sqrt\alpha$, $w=\sin\phi/\sqrt\beta$, and let
$\rho_u$ assign equal mass to the four sign choices of
$(1,\sqrt u,\sqrt{(1-\alpha u)/\beta})$. For small $\varepsilon>0$ set

$$
\begin{aligned}
u_\varepsilon&=\frac{u_f-\varepsilon/(2\alpha)}{1-\varepsilon},\\
d\sigma_\varepsilon
&=\mu[(1-\varepsilon)d\rho_{u_\varepsilon}
                  +\varepsilon d\rho_\circ],\qquad
 dp_1=d\sigma_\varepsilon/(tc(h)).
\end{aligned}
\tag{RC.68}
$$

Here $0<u_\varepsilon<1/\alpha$. The moments of $\sigma_\varepsilon$
are exactly $(\mu,V,W,0)$ for $(1,z^2,w^2,zw)$. The congruence
$\widehat n=\left(\begin{smallmatrix}0&d/h_2\\-b/h_1&0\end{smallmatrix}\right)(z,w)^T$
therefore gives the full failure matrix $M_2$. The remaining live Gram
$B_\varepsilon=I-\int hh^Tdp_1$ is diagonal. At $\varepsilon=0$ it is

$$
B_0=\operatorname{diag}(1-q,1-qu_f,1-qv_f)\succ0,
\tag{RC.69}
$$

since $t>t_0$ means $q<1/v_f$. Subtract a small positive multiple
$a_\circ\int hh^Td\rho_\circ$ from $B_\varepsilon$. The remainder is
still positive diagonal and $Q$-null. Writing it as
$\operatorname{diag}(m,d_z,d_w)$, its four-point representation has
mass $m$ and coordinates $(\pm\sqrt{d_z/m},\pm\sqrt{d_w/m})$;
$\alpha d_z+\beta d_w=m$ puts them on the circle. Add back
$a_\circ\rho_\circ$ to obtain $p_0$. Both sheets now have full-support
positive density components. As $\varepsilon,a_\circ\downarrow0$,
their contrast tends to (RC.65): the saturated part contributes
$q\sqrt{u_f}$ and the pure part contributes
$\sqrt{(1-q)(1-qu_f)}$. Choose them positive with contrast strictly
above $\tau$.

Consider the finite-dimensional cone of live moments, failure moments
and a contrast coordinate allowed to decrease freely below achieved
contrast. A supporting functional vanishing at our target is
nonnegative on every sheet atom and on the downward contrast ray.
Strict contrast slack forces its contrast coefficient to vanish.
The full-support components then force its continuous sheet functions
to vanish identically. On the pure sheet this says $h^TYh=0$ on the
ellipse; comparison of the constant, first and second harmonics gives
$Y=a_QQ$. On the saturated sheet it then says
$\widehat n_h^TZ\widehat n_h=0$ everywhere, hence $Z=0$, because
$\widehat n_h$ traverses every projective direction. Thus only the
identity $h^TQh=0$ remains. After quotienting this identity, the target
is in the relative interior of the moment projection.

Adjoin height and its downward slack. Locally the first live moment
bounds total measure mass; compactness of the two circles and continuity
of all integrands make the upper height boundary closed and bounded.
Separate its attained optimum from higher heights. The height
coefficient of a nonzero supporting functional cannot vanish: that
would support the relative-interior moment target just proved. Its
sign is positive by downward height slack, so normalize it to one.
The downward contrast ray gives $\lambda\ge0$. Evaluation on individual
atoms yields the two inequalities in (RC.67); evaluation at the target
gives equality of values. Integration of the nonnegative gaps gives
contact and complementary slackness for every optimizer. $\square$

This proof supplies the double-sheet relative-interior hypothesis,
not merely primal feasibility. It makes no claim of finite dual
attainment on $t=t_0$ or $\tau=\tau_{\max}(t)$; the known boundary
value retains FA79's separate proof.

## 69. Eight full-circle polynomial tests and a finite contact inventory

**Theorem 69.1 (polynomials, nonidentity and contact bound).** For any
certificate in Theorem 68.1 and $\epsilon,r\in\{\pm1\}$ put

$$
\begin{aligned}
P^0_{\epsilon r}(h)&=h^T(Y-\epsilon G)h-\lambda rz,\\
P^1_{\epsilon r}(h)&=\mathcal D(h)P^0_{\epsilon r}(h)
+t\mathcal N(h)\widehat n_h^T(Z-\epsilon\Delta_f)\widehat n_h.
\end{aligned}
\tag{RC.70}
$$

The two dual inequalities are equivalent to nonnegativity of all eight
polynomials on the full circle. None is identically zero. Their
trigonometric degrees are at most two and four respectively, and their
homogeneous half-angle degrees are at most four and eight. Each pure
polynomial has at most two distinct circle zeros; each saturated
polynomial has at most four. Thus every endpoint contact is in a set
of at most 24 sheet contacts, with coincidences counted only once when
appropriate.

**Proof.** Taking the maximum over $\epsilon$ and $r$ gives the two
absolute values. Multiplication by the strictly positive $\mathcal D$
introduces no sign changes or spurious zeros. All factors in (RC.70)
are quadratic or linear in the circle coordinates, which gives the
stated degrees. At $w=0$ the failure height is zero. The source box gives

$$
0<a_z:=g_0+g_1/\alpha
<b_z:=2x_G/\sqrt\alpha.
\tag{RC.71}
$$

For example $\alpha>7/8$ and the coarse rational bounds obtained from
(RC.4)–(RC.5) give
$a_z<(1270+(8/7)2923)10^{-6}<4740\,10^{-6}<b_z$.
Both sheet heights consequently take positive and negative values at
these two axis points. If $\lambda>0$ and one polynomial vanished
identically, changing $r$ would add $2\lambda rz$ times either $1$
or $\mathcal D$. This cannot be nonnegative on the whole circle.
If $\lambda=0$, identity of one polynomial would force its sheet
height to have the fixed sign $\epsilon$ everywhere, contradicting
the two axis points. Nonidentity follows.

Set $\tan(\phi/2)=U/V$ and clear $(U^2+V^2)^2$ or
$(U^2+V^2)^4$. The resulting nonzero nonnegative real binary forms
have degrees four or eight. Every real projective zero has even
multiplicity, so there are at most two or four distinct zeros.
$V=0$ includes the missing point of the affine half-angle chart;
axis contacts are retained. Summing the four bounds on each sheet gives
24. $\square$

The count concerns the support candidates of a particular certificate.
It is neither an actual-label bound nor an improvement of the inherited
nine-supported-nonzero-low-label existence bound. Fejér–Riesz factorization can certify
an already selected nonnegative polynomial, including its zeros; it
does not select $Y,Z,\lambda$, contacts or common positive weights.

## 70. Strictly unsaturated labels and degeneracies

**Theorem 70.1 (common-kernel necessity).** At a strict interior point,
let a globally optimal supported-nonzero actual low label have $p_j>0$ and
$0<b_j<C(h_j)$. Its two endpoint heights have a common sign
$\epsilon\in\{\pm1\}$, with zeros allowed. For every optimal common
certificate,

$$
(Z-\epsilon\Delta_f)\widehat n_{h_j}=0.
\tag{RC.72}
$$

Consequently if both $Z-\Delta_f$ and $Z+\Delta_f$ are invertible,
every supported-nonzero optimal low label is pure or saturated.
Supported-zero actual labels have no assigned endpoint or contact.

**Proof.** Endpoint splitting gives

$$
|\ell+b_jf|\le(1-b_j/C)|\ell|+(b_j/C)|\ell+Cf|.
\tag{RC.73}
$$

Strictly opposite endpoint signs would make this strict and yield a
strictly better instrument with the same moments and contrast by §75.
Thus there is a common maximizing sign $\epsilon$. Optimality and
positive endpoint weights imply contact on both sheets, for any optimal
certificate. Choose a maximizing report sign $r$. The corresponding
$P^0,P^1$ are nonnegative and zero at $h_j$, so both angular derivatives
vanish there. Subtracting $\mathcal D P^0$ from $P^1$ and differentiating,
using $\mathcal N>0$, gives

$$
\widehat n^TB\widehat n=0,\qquad
(\widehat n')^TB\widehat n=0,\quad B=Z-\epsilon\Delta_f.
\tag{RC.74}
$$

On the parametrization in §68,
$\det[\widehat n,\widehat n']=bd/(h_1h_2\sqrt{\alpha\beta})\ne0$.
The two equations therefore imply $B\widehat n=0$. The final assertion
uses $\widehat n\ne0$. $\square$

**Proposition 70.2 (axis and zero-height conditions).** If $\lambda>0$,
no endpoint contact has $z=0$. At any contact of zero sheet height,
the angular derivative of that height vanishes. Thus a simple zero of
the height is excluded. Axes and multiple zeros are retained when not
excluded by these statements.

**Proof.** At $z=0$ both choices of $r$ have the same zero gap. Their
angular derivatives would both vanish, but differ by
$2\lambda z'$ times a positive sheet denominator; $z'\ne0$ at these
points. This is impossible when $\lambda>0$. If a sheet height is zero,
both choices of $\epsilon$ have zero gap for a maximizing $r$.
Subtracting their zero derivative equations gives zero derivative of
the height (the positive denominator has no effect at a zero).
When $\lambda=0$ the report constraints coincide, so the first argument
does not exclude $z=0$. No generic-simple-root assumption removes these
cases. $\square$

## 71. Complete orientation optimization for a fixed even-moment family

**Definition 71.1 (the fixed data).** Remove zero weights, and fix a
finite family indexed by $i=1,\ldots,m$, with $q_i>0$,
$v_i=(z_i,w_i)^T$, $\eta_i\in\{0,1\}$ satisfying
$\alpha z_i^2+\beta w_i^2=1$ and

$$
\sum_iq_i=1,\quad \sum_iq_iv_iv_i^T=I_2,\quad
\sum_iq_i\eta_iC(h_i)\widehat n_{h_i}\widehat n_{h_i}^T=M_2,
\quad\sum_iq_i|z_i|\ge\tau.
\tag{RC.75}
$$

The family is even under $v\mapsto-v$ but its actual orientation may
vary. Set

$$
\begin{aligned}
a_i&=g_0+g_1z_i^2+g_2w_i^2+2z_Gz_iw_i
                 +\eta_iC(h_i)f(h_i),\\
b_i^{\rm odd}&=2(x_Gz_i+y_Gw_i),\\
m_i&=(|a_i+b_i^{\rm odd}|+|a_i-b_i^{\rm odd}|)/2,\\
d_i&=(|a_i+b_i^{\rm odd}|-|a_i-b_i^{\rm odd}|)/2,\\
p_{i,\pm}&=q_i(1\pm\vartheta_i)/2,\qquad
-1\le\vartheta_i\le1,\qquad \sum_iq_i\vartheta_iv_i=0.
\end{aligned}
\tag{RC.76}
$$

The last equation is precisely the missing live first-moment condition.
All the even moments, capacity and contrast remain fixed.

**Theorem 71.2 (finite formula and full degenerate recovery).** For each
pair with $\det(v_i,v_j)\ne0$, let $u_{ij}$ solve
$u_{ij}\cdot v_i=d_i$, $u_{ij}\cdot v_j=d_j$. The maximum low height is

$$
\sum_iq_im_i+
\min_{\det(v_i,v_j)\ne0}\sum_kq_k|d_k-u_{ij}\cdot v_k|.
\tag{RC.77}
$$

For a minimizing pair set $r_k=d_k-u_{ij}\cdot v_k$. Set
$\vartheta_k=\operatorname{sgn}r_k$ for $r_k\ne0$. On the zero-residual
indices enumerate box vertices as follows: choose zero, one or two
free indices, put every other zero-residual index at $\pm1$, and solve
$\sum q_k\vartheta_kv_k=0$. With zero free indices check this equation;
with one solve its scalar coefficient and check both coordinates;
with two use Cramer's formula only when their columns $q_kv_k$ are
independent. Retain values in $[-1,1]$ and remove zero actual weights.
At least one candidate exists. Repeated or parallel residual lines and
an all-zero residual vector are allowed.

**Proof.** For every $u\in\mathbb R^2$ the balance equation gives

$$
\sum_iq_id_i\vartheta_i
=\sum_iq_i(d_i-u\cdot v_i)\vartheta_i
\le F(u):=\sum_iq_i|d_i-u\cdot v_i|.
\tag{RC.78}
$$

The covariance $I_2$ implies that the $v_i$ span the plane and hence
$\min_{\|e\|=1}\sum_iq_i|e\cdot v_i|>0$. Thus $F$ is coercive and
attains its minimum. Its zero subgradient condition supplies precisely
the balanced $\vartheta_i$, fixed to residual signs off the zero set.
This attains the bound. The minimizing set is a nonempty compact
polyhedron. At one of its vertices the active zero-residual normals
must span two dimensions. Otherwise a nonzero direction preserving all
zero residuals leaves the objective locally affine; minimality makes
it locally constant in both directions, contradicting the vertex.
Thus a minimizing pair exists, proving (RC.77).

For a fixed minimizing $u$, the residual-zero balance section of the
box is nonempty and compact and has a vertex. If the columns of its
strictly fractional variables were dependent, a small two-sided
perturbation in their kernel would contradict that vertex. There are
therefore at most two such variables and their columns are independent.
The zero-, one- and two-variable enumeration above includes this
vertex. Duplicated and parallel rows remain constraints but never
supply an invalid two-by-two inverse. The same argument covers no
fractional variables and the all-zero residual case. $\square$

**Corollary 71.3 (when balanced orientation is optimal).** The choice
$\vartheta_i=0$ is optimal exactly when some common $u$ satisfies
$d_i=u\cdot v_i$ for all $i$ on both sheets.

**Proof.** Its orientation contribution is zero, whereas (RC.77)'s
minimum is nonnegative and attained. That minimum is zero exactly when
all its positive-weight absolute residuals vanish. $\square$

Separate pure and saturated balance would impose extra constraints.
The common $u$ is essential. This theorem evaluates the orientation of
the fixed even family; it does not select that family or evaluate the
global finite frontier.

## 72. The entire two-projection-line layer

**Definition 72.1 (what is counted).** Let
$\mathscr L(\Phi)=\{\mathbb R(z_j,w_j):j\in\mathcal J_+(\Phi)\}$.
This counts every supported-nonzero low live projection line, including
pure-live labels. Supported-zero actual labels in $\mathcal J_0$ have
no projected line; they remain allowed in this layer and counted in
its full actual alphabet and whole-fibre activity.
The vectors $(1,z,w)$ and $(1,-z,-w)$ are distinct live directions but
have the same projected line. Neither failure-ray count, Hilbert-space
dimension, hidden Kraus multiplicity nor readable alphabet cardinality
is this count. Let $\mathcal T_A^{[2]}(s)$ be the supremal original
height restricted to $|\mathscr L|\le2$.

**Lemma 72.2 (the lines are forced).** In every feasible instrument in
this layer, the supported-nonzero low labels use all four directions

$$
h_{z,\pm}=(1,\pm\alpha^{-1/2},0),\qquad
h_{w,\pm}=(1,0,\pm\beta^{-1/2}).
\tag{RC.79}
$$

**Proof.** The physical congruence in §68 transforms (RC.66) into

$$
\sum_jp_jv_jv_j^T=I_2,\qquad
\sum_jp_jb_jv_jv_j^T=\operatorname{diag}(V,W).
\tag{RC.80}
$$

Rank two of the first matrix requires two independent lines. Aggregate
its weights on unit representatives of the two lines and form the
square matrix $U$ with these weighted columns. Then $UU^T=I_2$, so
$U$ is orthogonal. The second equation is a spectral decomposition in
the same orthogonal basis, with eigenvalues equal to the weighted
failure ratios on the lines. Since $V<W$, its eigendirections are
uniquely the coordinate axes. The ellipse fixes their lengths as in
(RC.79). First moments force both orientations on each axis. $\square$

**Lemma 72.3 (the source-specific signs).** Put

$$
\begin{gathered}
c_z=c_*(1/\alpha)>c_w=c_*(0),\qquad t_{\rm ax}=W/c_w,\\
a_z=g_0+g_1/\alpha,\quad b_z=2x_G/\sqrt\alpha,\quad
 a_w=g_0+g_2/\beta,\quad b_w=2y_G/\sqrt\beta,\\
k_w=11d^2/(64h_2^2\beta).
\end{gathered}
\tag{RC.81}
$$

Then $0<a_z<b_z$, $0<b_w<a_w$, $\beta Wk_w=d_f$,
$f(h_{z,\pm})=0$, $f(h_{w,\pm})=-k_w$, and
$Wk_w>a_w+b_w$.

**Proof.** (RC.71) gives the first sign. The rational source bounds
$1/9<\beta<1/8$ give
$a_w>(1269+8\cdot1677)10^{-6}>6\cdot2209\,10^{-6}>b_w>0$.
Substitution in $f$ and $W$ gives the failure identities. At the
conditional root trace preservation gives
$d_f=N_{00}+g_1+g_2$. Hence

$$
d_f-\beta(a_w+b_w)
=N_{00}(1-\beta\delta)+g_1-2y_G\sqrt\beta>0,
\tag{RC.82}
$$

because $N_{00}>0$, $\beta\delta<1$, $2\sqrt\beta<1$ and
$g_1>y_G>0$. All coarse inequalities are consequences of (RC.4)–(RC.5)
and the positive-pivot formulas; no TP identity is imposed off root.
The monotonicity of $c_*$ gives $c_z>c_w$. $\square$

**Theorem 72.4 (complete feasibility, value, attainer and minimum counts).**
The two-line layer is feasible exactly when

$$
0\le s\le s_0\sqrt\alpha=\sqrt\theta,\qquad t\ge t_{\rm ax}.
\tag{RC.83}
$$

On it set $q_{\rm ax}=\beta W/(tc_w)\in(0,\beta]$. Then

$$
2\mathcal T_A^{[2]}(s)=H_0+\alpha b_z+\beta a_w+d_f
 -2a_wq_{\rm ax}+2b_w\min(q_{\rm ax},\beta-q_{\rm ax}).
\tag{RC.84}
$$

Let $P_w=\beta/2$, $x_- =\min(P_w,q_{\rm ax})$,
$x_+=q_{\rm ax}-x_-$. An attainer consists of the following
supported-nonzero actual low labels, with zero rows deleted:

| Direction | Weight $p$ | Failure ratio $b_j$ |
| --- | --- | --- |
| $h_{z,+}$ | $\alpha/2$ | $V$ |
| $h_{z,-}$ | $\alpha/2$ | $V$ |
| $h_{w,+}$, pure | $P_w-x_+$ | $0$ |
| $h_{w,+}$, saturated | $x_+$ | $tc_w$ |
| $h_{w,-}$, pure | $P_w-x_-$ | $0$ |
| $h_{w,-}$, saturated | $x_-$ | $tc_w$ |

At this layer's optimal height, the minimum number of supported-nonzero
low labels equals the minimum number of all nonzero actual low labels;
write this common minimum as $n_{\rm low}^{[2]}$. The complete total
actual-alphabet minimum is $n_{\rm total}^{[2]}$. They are

$$
n_{\rm low}^{[2]}=
\begin{cases}4,&t=t_{\rm ax}\text{ or }t=2t_{\rm ax},\\
5,&t>t_{\rm ax},\ t\ne2t_{\rm ax},\end{cases}
\qquad n_{\rm total}^{[2]}=n_{\rm low}^{[2]}+1.
\tag{RC.85}
$$

Every optimizer has the same supported-nonzero $w$-axis pure/saturated
mass allocation $x_\pm$. The $z$-axis failure allocation need not be unique: it has
aggregate $\sum_{z\text{-axis}}p_jb_j=\alpha V$ and the individual
capacity bounds, but its height is independent of this allocation.

**Proof.** The live first and second moments give total mass
$\alpha/2$ at each $z$ orientation and $\beta/2$ at each $w$
orientation. Failure requires total $pb$ masses $\alpha V,\beta W$.
The capacity conditions are $tc_z\ge V$, $tc_w\ge W$; the latter is
stronger since $V<W$ and $c_z>c_w$. The available normalized contrast
$\sum_jp_j|z_j|$ is always $\sqrt\alpha$; arbitrary binary reports can
attenuate the actual contrast, while the deterministic reports in §75
attain this available value. This proves necessity of (RC.83), and the table
proves sufficiency of all moments, capacities and contrast.

The $z$ contribution is $\alpha b_z$ since $f=0$. Set $C_w=tc_w$.
At either $w$ orientation the pure height $a_w\pm b_w$ is positive,
whereas the saturated height $a_w\pm b_w-C_wk_w$ is negative by
$C_w\ge W$ and Lemma 72.3. Endpoint splitting therefore bounds the
$w$ contribution by

$$
\beta a_w+d_f
-2[x_-(a_w-b_w)+x_+(a_w+b_w)],\quad
x_-+x_+=q_{\rm ax},\quad 0\le x_\pm\le P_w.
\tag{RC.86}
$$

Since $b_w>0$, the unique maximizing allocation fills $x_-$ first.
This proves (RC.84) and the table's attainment. Every supported-nonzero
actual $w$ label of strictly intermediate failure ratio would make endpoint
splitting strict, so all optimizing $w$ labels are endpoints. At
$q_{\rm ax}=\beta$ or $\beta/2$ each direction needs one label;
at every other finite feasible $q_{\rm ax}$ exactly one $w$
direction needs both positive pure and saturated masses. Those cannot
be combined: their opposite signs make (RC.73) strict. Different
supported-nonzero low live directions cannot share one actual label by FA69's rigidity.
All four directions have positive total mass. Thus every competitor
needs at least four or five supported-nonzero low labels as in (RC.85),
and hence at least as many actual low labels. Each $z$ direction can
use one label with ratio $V$. Positive high acquired mass requires at
least one high label. Section 75 attains both lower bounds with exactly
these supported-nonzero low labels, no separate supported-zero low label,
and one high label containing the complement. Any separate labels in
$\mathcal J_0$ add to the actual low and total counts without changing
(RC.80) or (RC.84). Their presence is permitted; the minimum uses the
aggregated completion. Every full joint fibre is counted even on
supported-zero inputs. $\square$

The formula is constant in $s$ over this layer's entire feasible
contrast inequality. The four/five changes here are layer minima,
not the finite-budget global optimal alphabet, the strong fixed-source
counts, or the static unbudgeted counts.

## 73. A strict global exclusion for the whole two-line layer

**Theorem 73.1 (strict gap and a projection-line lower bound).** On every
point satisfying (RC.83),

$$
\mathcal T_A(s)>\mathcal T_A^{[2]}(s).
\tag{RC.87}
$$

Consequently every globally optimal instrument in a nonempty original
weak finite-budget class has at least three supported-nonzero low
projection lines, that is, $|\mathscr L(\Phi)|\ge3$ regardless of any
additional supported-zero actual labels.

**Proof.** First the entire axis layer lies strictly inside the domain
of Theorem 68.1. Indeed $c_w<c_f$ gives
$t\ge W/c_w>W/c_f=t_0$. At $t=t_0$, write
$\tau_*=\tau_{\max}(t_0)$. The identities in (RC.65) give

$$
\tau_*-\sqrt\alpha
=\frac{\beta\sqrt{u_f}(1-\sqrt{\alpha u_f})}
       {1-\alpha u_f}>0.
\tag{RC.88}
$$

FA's maximum-contrast formula increases with $t$, so
$\tau\le\sqrt\alpha<\tau_*<\tau_{\max}(t)$.
If global and layer values were equal, the explicit table in Theorem
72.4 would be globally optimal. Its two $z$ labels both satisfy
$0<V<tc_z$. Their endpoint heights have opposite signs, respectively
$+$ and $-$, by (RC.71), and both physical failure directions are the
second axis of the two-dimensional failure support. Theorem 70.1
applied to the same certificate would imply

$$
(Z-\Delta_f)e_2=0,\qquad (Z+\Delta_f)e_2=0.
\tag{RC.89}
$$

This forces $\Delta_fe_2=0$, contradicting
$\Delta_fe_2=((\sqrt{37}-\sqrt{59})/16,0)^T\ne0$.
This proves the strict gap. One line cannot have rank-two projected
live covariance, and any two-line optimizer would belong to the layer
just excluded. The lower bound follows, including feasible parameters
outside the layer. $\square$

The argument uses a common dual and the supported-nonzero actual-label
unsaturated kernel, with no maximum-contrast live-completion restriction. The conclusion
is not an upper bound of three lines and is not TC's limiting
failure-line theorem. It does not count quantum dimension or the
number of readable labels.

## 74. An independent explicit large-budget common-instrument improvement

**Theorem 74.1 (finite eight-low-label witness).** Define

$$
\begin{gathered}
\rho_z=V/c_z,\quad \rho_w=W/c_w,\quad
 a_0=\alpha\rho_z+\beta\rho_w,\\
J_\square=\frac14\sum_{\sigma,\upsilon=\pm1}
 |\ell(1,\sigma,\upsilon)|,\qquad
J_{\rm ax}=\alpha b_z+\beta a_w,\qquad \gamma=9/10000,\\
D_* =a_0g_0+\rho_zg_1+\rho_wg_2
 +2x_G(a_0+\rho_z)+2y_G(a_0+\rho_w)
 +2|z_G|(\rho_z+\rho_w),\\
K_*=D_*+\beta\rho_w(2b_w-a_w)_+,\\
t_* =\max\left\{2\rho_w,
 \frac{a_0+\rho_z}{1-\sqrt\alpha},\frac{2K_*}{\gamma}\right\}.
\end{gathered}
\tag{RC.90}
$$

For every $t\ge t_*$ put saturated mass $\alpha\rho_z/(2t)$
at each $z$ axis point, and $\beta\rho_w/(2t)$ at each $w$ axis
point. Set

$$
\begin{gathered}
m=1-a_0/t,\quad d_z=1-\rho_z/t,\quad d_w=1-\rho_w/t,\\
h_{\sigma\upsilon}=(1,\sigma\sqrt{d_z/m},\upsilon\sqrt{d_w/m}),
\qquad p_{\sigma\upsilon}=m/4,\quad b_{\sigma\upsilon}=0.
\end{gathered}
\tag{RC.91}
$$

These eight positive supported-nonzero low atoms satisfy (RC.66) with
normalized contrast at least $\sqrt\alpha$. For every $0\le s\le\sqrt\theta$, the
single original instrument of §75 built from them has low height
strictly more than $\gamma/2$ above the layer value (RC.84), and
hence TV improvement strictly more than $\gamma/4$.

**Proof.** The saturated axes supply exactly $M_2$ and live Gram
$\operatorname{diag}(a_0/t,\rho_z/t,\rho_w/t)$. Since
$\alpha d_z+\beta d_w=m$, the four pure points in (RC.91) lie on
$\mathscr C$ and complete the live Gram. We have
$0<\rho_z<\rho_w$, $a_0<\rho_w$, and $t\ge2\rho_w$, so all
residual diagonal entries, masses and square roots are strictly positive.
Their contrast is

$$
\sqrt\alpha\,\rho_z/t+
\sqrt{(1-a_0/t)(1-\rho_z/t)}\ge\sqrt\alpha,
\tag{RC.92}
$$

using $\sqrt{(1-x)(1-y)}\ge1-x-y$ for $0\le x,y\le1$ and
the second threshold in (RC.90).

For the height gap, replacing just the $(-,-)$ corner by its negative
inside the absolute-value sum gives

$$
\begin{aligned}
J_\square-J_{\rm ax}\ge{}&
(\alpha-\tfrac12)g_0+\tfrac12g_1-\tfrac12g_2
+x_G(1-2\sqrt\alpha)+y_G-z_G>\gamma.
\end{aligned}
\tag{RC.93}
$$

This lower bound does not require guessing the corner's sign. For an
explicit rational comparison, use
$\alpha>7/8$, $\sqrt\alpha<1$, and the coarse bounds
$10^6(g_0,g_1,g_2,x_G,y_G,z_G)$ in
$(1269,1270)\times(2922,2923)\times(1677,1678)
\times(2370,2371)\times(2208,2209)\times(-102,-101)$.
The lower bound is at least
$[(3/8)1269+1461-839-2371+2208+101]10^{-6}
=0.001035875>\gamma$. These bounds follow from the complete
nine-coordinate box, not a rounded source-center identity.

Compare the residual pure height with $J_\square$ term by term.
After multiplication by $m$, its constant and diagonal coefficients
change by $a_0g_0/t$, $\rho_zg_1/t$, $\rho_wg_2/t$.
The linear coefficients contain $\sqrt{md_z}$ and $\sqrt{md_w}$,
and the cross coefficient contains $\sqrt{d_zd_w}$. The same elementary
square-root inequality bounds their changes by
$(a_0+\rho_z)/t$, $(a_0+\rho_w)/t$, and
$(\rho_z+\rho_w)/t$. The absolute value is 1-Lipschitz; averaging
gives residual pure height at least $J_\square-D_*/t$.
The saturated axes contribute
$\alpha\rho_z b_z/t+d_f-\beta\rho_wa_w/t$.
For $t\ge2\rho_w$ we have $q_{\rm ax}\le\beta/2$. Subtract
(RC.84)'s low height and discard the positive $z$ contribution to get

$$
\text{low height gain}\ge
J_\square-J_{\rm ax}-K_*/t>\gamma/2.
\tag{RC.94}
$$

The last threshold in (RC.90) proves the claim, and §75 realizes all
constraints together. $\square$

This is an explicit improvement witness, with no assertion of global
optimality or minimum labels. Its positive residual Gram has rank three;
it is not a rank-at-most-two fixed-allocation formula. The proof of
Theorem 73.1 covers all budgets in the layer, independently of this
large-budget construction.

## 75. One common original output and chronological decoder

**Proposition 75.1 (simultaneous original-class realization).** Every
finite supported-nonzero low family in (RC.66), in particular the axis
and eight-atom families, has one common instrument on the original unknown five-mode specimen
which attains its actual height and contrast, all twelve required errors,
the sharp weak worst-history joint cost, and the stated finite activity.
It has precisely one additional actual high acquisition label, with
the complementary subspace included in that label. The five failure
labels and every Borel component and passive-reference
conditional operator retain their original meanings.

**Proof.** This is the full-fibre constructor of FA70 and FA86 applied
to these moment families, with the complement aggregated into one high
fibre as permitted in the original JR class. The formulas below specify
the common realization rather than separate optima. Omit zero weights
before taking inverses. For each supported-nonzero low label set

$$
\begin{gathered}
K_j=\sqrt{p_j}K_{h_j},\quad N_j=p_jb_jn_{h_j}n_{h_j}^T,\quad
J_j:\mathbb C^2\longrightarrow\operatorname{ran}K_j^\dagger
\text{ an isometry},\\
Q_j=J_j^\dagger(K_j^\dagger K_j+N_j)J_j,\quad
C_j=Q_j^{1/2}J_j^\dagger E^\dagger,\\
B_j=K_jJ_jQ_j^{-1/2},\qquad
F_j=Q_j^{-1/2}J_j^\dagger N_jJ_jQ_j^{-1/2}.
\end{gathered}
\tag{RC.95}
$$

The ellipse makes $K_h$ rank two. Its kernel is spanned by
$(s_0,-bz/h_1,-dw/h_2)^T$, which is orthogonal to $n_h$.
Thus $Q_j\succ0$, $B_jC_j=K_jE^\dagger$ and
$C_j^\dagger F_jC_j=EN_jE^\dagger$. Direct multiplication gives

$$
B_j^\dagger B_j+F_j=I_2,\quad
I_2-F_j\succ0,\qquad
\frac{\lambda_{\max}(F_j)}{1-\lambda_{\max}(F_j)}
=\frac{b_j}{c(h_j)}.
\tag{RC.96}
$$

The final identity is FA69's rank-one generalized Rayleigh/capacity
formula, with the same positive $\mathcal N/\mathcal D$ in (RC.64).
It holds at both axes as well as off axis. For $b_j=0$, $F_j=0$.

Use relative time $u\in[0,1]$ on the original clock, with

$$
\begin{gathered}
g(u)=2/(1+u)^2,\quad G_{\rm time}(u)=2u/(1+u),\\
Z_j(u)=\sqrt{I_2-G_{\rm time}(u)F_j},\qquad
R_j(u)=g(u)F_j[I_2-G_{\rm time}(u)F_j]^{-1}.
\end{gathered}
\tag{RC.97}
$$

All these commuting functions are defined on the entire counted qubit.
The not-yet-failed propagator from $u$ to $v$ is
$\operatorname{Ad}_{Z_j(v)Z_j(u)^{-1}}$. Its instantaneous loss effect
is $R_j(u)$. On the current survivor matrix $Y$, the jump into original
label $\ell$ has density

$$
Y\longmapsto w_\ell g(u)
\operatorname{tr}(F_jZ_j(u)^{-1}YZ_j(u)^{-1})P_f,
\quad (w_0,w_1,w_2,w_3,w_{13})=(0,1/4,1/2,1/4,0).
\tag{RC.98}
$$

This positive functional is CP, including with passive references.
Its sum over $\ell$ is the loss effect of the survivor propagator.
At every cut the survivor effect plus the integrated preceding jump
effects is $I_2$. Survivors at $u=1$ receive the terminal isometry
$EB_j(I_2-F_j)^{-1/2}$; its cumulative live map is
$\operatorname{Ad}_{EB_j}$. There is no terminal failure atom.
Since the largest eigenvalue of $F_j$ stays fixed along (RC.97),

$$
\int_0^1\|R_j(u)\|\,du
=-\log(1-\lambda_{\max}(F_j))
=\log(1+b_j/c(h_j))\le A.
\tag{RC.99}
$$

Pure rows have zero activity and saturated rows have activity $A$.
Terminal survivor effect is at least $e^{-A}I_2$, for every qubit
input, including those not supplied by the original histories.

Choose isometries $W_\perp:\mathbb C^2\to P^\perp$ and
$J_0:\mathbb C^2\to\mathbb C^3$. The single high label has encoder

$$
C_H=\begin{pmatrix}\sqrt{1-\delta}\,DE^\dagger\\
W_\perp^\dagger\end{pmatrix}:\mathbb C^5\to\mathbb C^3\oplus\mathbb C^2,
\tag{RC.100}
$$

zero rate and deterministic report $+$. Its terminal decoder has the
two hidden Kraus operators $E[I_3\ 0]$ and $EJ_0[0\ I_2]$.
Their effects sum to $I_5$. The high fibre is the entire five-dimensional
joint space, although its supported original-history part has rank
three. The hidden Kraus index is not a readable acquisition label.
This coherent completion differs from the fixed CA.10 certain-failure
completion and has finite zero activity on its whole fibre.

The same supported family also permits the separate FA70.2/FA86.1
completion: replace $C_H$ by a high encoder
$\sqrt{1-\delta}\,DE^\dagger$ into $\mathbb C^3$, with decoder $E$,
and an actual low encoder $C_\perp=W_\perp^\dagger$ into
$\mathbb C^2$, with decoder $EJ_0$. Give both deterministic report $+$
and zero rate. The latter full encoder is nonzero with effect $I_5-P$,
but $C_\perp E=0$; it belongs to $\mathcal J_0$ and has no $p,h,b$
coordinates. Its survivor effect is $I_2$ at every time. The two
encoders' effects sum to $C_H^\dagger C_H$, and their composed live
CP maps sum to the high branch's composed live map in (RC.102).
Consequently the total acquisition effect (RC.101), the forgotten-label
live map, all five failure-labelled Borel output maps (RC.102), their
passive-reference amplifications (RC.103), and all errors (RC.104)
are unchanged for all complex $M_5$ inputs. The supported histories give the complementary label probability
zero, so height TV, contrast and sharp high acquisition cost are also
unchanged. The separate completion has one more actual low label and
one more total label; its complementary qubit is fully counted and obeys the same
activity bound. Neither completion excludes the other from the original
class. The minimum-count witnesses use (RC.100).

The low live coefficient Gram is $\operatorname{diag}(\delta,1,1)$;
the high part adds $(1-\delta)D$ in squared-coefficient weight. Thus
summing encoder effects gives, using the conditional root TP identity,

$$
\sum_jC_j^\dagger C_j+C_H^\dagger C_H=I_5.
\tag{RC.101}
$$

Each acquisition is CP/TNI and their sum is TP. The same instrument,
on every complex $X\in M_5$, has forgotten-label outputs

$$
\begin{aligned}
\Phi^L(X)&=E[\Lambda_*(E^\dagger XE)
       +J_0W_\perp^\dagger XW_\perp J_0^\dagger]E^\dagger,\\
\Phi^f_\ell(\mathcal B)(X)&=
 w_\ell\left(\int_{\mathcal B}g(u)\,du\right)
 \operatorname{tr}(EME^\dagger X)P_f,\qquad M=\operatorname{diag}(0,m_1,m_2).
\end{aligned}
\tag{RC.102}
$$

Here $\Lambda_*(A)=DAD^\dagger+TAT^\dagger+SAS^\dagger$.
The first identity follows from the full coefficient Gram, not just
its diagonal or its action on twelve states. The second follows from
$\sum N_j=M$ and the pulled-back jump density. It proves equality on
every Borel subset, including separate zero components at labels $0,13$.
At a passive reference the live Kraus operators are tensored with $I_R$;
the failure output on any joint matrix $X$ is precisely

$$
w_\ell\left(\int_{\mathcal B}g(u)\,du\right)P_f\otimes
\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X].
\tag{RC.103}
$$

The reference operator is conditional; it is not replaced by an
unconditional marginal. Cross coherences inside the live output are
retained. No abort, wrong-support, singular-time or extra uncounted
sector occurs in these witnesses.

Give low label $j$ the deterministic report $\operatorname{sgn}z_j$
with $+$ at zero. Its acquisition effect includes $N_j$ as well as
$K_j^\dagger K_j$, including mass that later fails. Failure effects
annihilate coordinate zero, and the high report has no relevant
interference term. Therefore $\mathsf V=s_0\sum p_j|z_j|\ge s$.
The actual acquisition-height TV is (RC.66); live and failure height
are combined inside each generated label before the absolute value.
For the original specimens the complement term in (RC.102) vanishes.
If $B_y^{\rm ideal}=\xi_y\xi_y^T$ with

$$
(\xi_{yi}^2)_i=
\left(y/128,\ y(58-y)/(128(y+6)),\ y/(2(y+6))\right),
$$

the complete stopped-cq HALF error for each sign pair is

$$
e_y=\frac12\left[\|\Lambda_*(\rho_y)-B_y^{\rm ideal}\|_1+
\sum_\ell w_\ell\int_0^1
\left|\operatorname{tr}(M\rho_y)g(u)-\frac{6y}{(y+6u)^2}\right|du\right].
\tag{RC.104}
$$

Covariance supplies every $e,n\in\{\pm1\}$.
CG.143 gives $e_{5,e,n}=e_{27,e,n}=E_*$ and
$e_{16,e,n}<71/484<37/250<E_*$. All twelve errors are preserved;
they are not all equal to $E_*$, and simulator $g$ is not ideal $f_y$.

Only the high acquisition has joint dimension at least three. On each
height-$y$ specimen its probability is
$(1-\delta)\operatorname{tr}(D^\dagger D\rho_y)$, maximized at $27$,
which is JR34–40's sharp weak $\mathsf C(s)$. The complementary
coherent share in (RC.100) is counted in the same high fibre even though the
original specimens have zero probability in it. Resource is the maximum
over actual labels of (RC.99) on each entire joint fibre, not an expected
activity, instantaneous maximum or integral of a cross-label maximum.

The construction fixes every operation before the sole unknown input.
There is no helper specimen, copy, history oracle, reset, retry,
postselection or acceptance division. At relative time $u$ the first
executed failure is at absolute time $6+u$. The cutwise trace balance
already proved supplies a chronological FIRST instrument. Only survivors
receive the terminal isometry; failed carriers receive no later
positive-carrier action and there is no forced deadline absorption.
This is a mathematical CP/TP instrument; it supplies no native access,
actuator, calibration or clock permission. $\square$

## 76. A sufficient analytic continuation criterion

**Theorem 76.1 (local continuation from an already certified seed).**
At a strict interior parameter $(t,\tau)$ suppose there is a finite
positive endpoint family of supported-nonzero low labels and a matching
full-circle certificate of Theorem 68.1. Suppose all zeros of the eight
nonnegative polynomials are tracked, isolated double zeros with strictly positive angular
second derivative, with no additional zeros. Fix the gauge
$Y\mapsto Y+a_QQ$. Choose either the branch $\lambda>0$ with
contrast equality, or the branch $\lambda=0$ with strict contrast
slack. In the first branch contacts have $z\ne0$ by Proposition 70.2.

Form the analytic equations for the complete moment constraints,
contact values and angular derivatives, and active contrast when
appropriate. Assume a square set of independent equations in all
contact, positive-weight and certificate unknowns has nonsingular
Jacobian, and every remaining equation is an analytic consequence in
a neighborhood. Identical report constraints at $\lambda=0$ are
counted only once. Then a sufficiently small parameter neighborhood
has an analytic family of common original global optimizers and
matching certificates.

**Proof.** The analytic implicit function theorem continues the
unknowns; the consequence hypothesis retains every equation, rather
than silently discarding dependent-looking ones. Weights, branch
signs, strict contrast slack when present, and positive denominators
persist. Near each tracked zero, its zero value and derivative together
with uniformly positive angular second derivative give a nonnegative
gap. On the compact complement of these neighborhoods every polynomial
has a strictly positive minimum at the seed; continuity preserves it.
Thus the eight whole-circle inequalities remain feasible. The complete
moments, contact equalities and contrast complementarity give equality
of primal and dual values. The common constructor in §75 then gives
original global optimizers. $\square$

This is sufficient, not a seed-existence assertion. Extra zeros,
vanishing weights, zero curvature, a singular Jacobian or a change of
contrast branch require separate analysis. A certificate may have
unused zeros, but those must be tracked as well to apply the theorem.
A finite set of KKT equations without the full-circle inequality and
complete-equation hypotheses is insufficient. No actual globally
optimal three-line or larger interior seed, parameter atlas, or global
root inventory is supplied here; the two-line family cannot be such
a seed by Theorem 73.1.

## 77. Primary interfaces, compatible source contracts and the full programme

**Convention 77.1 (primary statements and exact limits of transfer).**
The proofs above use finite-dimensional separation, positive moment
representations, piecewise-linear convex duality and the analytic
implicit function theorem with their explicitly proved interfaces.
The following primary statements identify what can and cannot be
borrowed; they are not claims of literature-wide novelty.

| Primary source and locator | Exact interface and boundary |
| --- | --- |
| Halaseh–Magron–Skomra, arXiv:2604.15072v1, Theorem 1.1, PDF p.2; Theorem 3.3, p.14 [HMS67] | The polynomial generalized moment theorem assumes $h_1\equiv1$, $b_1>0$ and $b$ in the relative interior of the moment cone for dual attainment. Primal attainment/no gap alone in Theorem 3.3 does not assert dual attainment. Section 68 proves the required continuous rational two-sheet and contrast-slack interface directly. |
| Dritschel–Rovnyak, arXiv:0903.3639v1, Theorem 2.1, PDF p.4 [DR67] | A full-circle nonnegative operator Laurent polynomial has a same-degree analytic factor $P^*P$, with zeros allowed. The scalar case applies to already nonnegative (RC.70), without selecting multipliers, roots or common weights. |
| Dette–Melas, arXiv:1105.3575v1, (3.2)–(3.4), PDF p.5, Theorem 3.1, p.6 [DM67] | The complete-class support bound requires $\Psi_0=1$, the distinguished diagonal information-matrix entry in (3.2), and either the two ordinary Chebyshev systems in (3.3) or the corresponding pair in (3.4) on an interval; the stronger extended-Chebyshev notion is defined separately and is not a hypothesis of Theorem 3.1. The present nine functions include $b_j,b_jz^2,b_jzw$, all identically zero on the pure sheet; nine pure-sheet evaluations have zero determinant. There is no direct three-atom transfer to this two-sheet problem. |
| Martin–Goldsztejn–Granvilliers–Jermann, DOI 10.1007/s10898-014-0201-3, author manuscript, §§3.1–3.3, PDF pp.8–12, conclusion p.13 [MG67] | Certified tracing starts from a given regular initial curve, with $C^2$ data and stable one-at-a-time activity changes. It certifies feasibility/local optimality/connectivity on that component; other singularities stop tracing. It provides neither this full-circle global inequality nor a complete two-parameter atlas. |
| Leppäjärvi–Sedlák, arXiv:2212.11225v2, §6.1, Definition 7, PDF p.15 [LS67] | Finite-output instrument postprocessing requires equality of the per-output CP compositions, not merely of effects. Equations (RC.102)–(RC.103) separately prove the all-complex Borel/reference extension used here. |
| Hsieh–Tavakoli–Ku–Skrzypczyk, arXiv:2603.27676v1, (1)–(3), Result 1, PDF pp.1–2 [HT67] | The finite-dimensional interactive-instrument robustness SDP measures noise mixing into noninteractive instruments. This is not the maximum-per-actual-label integrated whole-fibre rate norm, and gives no value of the original activity frontier. |

FA supplies original capacity, endpoint splitting, boundary feasibility,
minimum-budget height and fixed-strength coefficient existence; JR/CG
supply the original comparison and source. Sections 68–74 and 76 supply
the additional conditional contact, orientation, exact layer and
exclusion synthesis. Proposition 75.1 is the necessary common application
of the inherited constructor. RC58–66's static residual dual, the
continuous null roof and nine-coordinate compression of the finite-height
continuation, TC's unique at-most-three-line limiting failure structure,
SC's convexity and saturation curvature, JS's full-product limit and
recovery, and WE's universal critical law retain their established
hypotheses. None of those limiting support bounds is imposed on finite
live labels. In particular 24 sheet contacts, nine supported-nonzero low
labels, at least three supported-nonzero live projection lines, two/three limiting failure lines, and actual
total labels are five different assertions.

**Convention 77.2 (limiting selection and current native interfaces).**
The selected limiting-interpolation construction in [JS, §§11–18][JS67]
supplies every limiting budget by its unique clamped scalar root and
strictly monotone inverse. That global budget selection coexists with
[TB][TB67]'s local bands and selected-branch regularity, whose hypotheses
remain local. It is not necessary to re-open the scalar selection as a
missing result. The transition-root inventory, isolation, ordering,
multiplicity and sign changes still need proof; neither this limiting
selection nor the local bands evaluate the full finite-$(s,A)$ frontier.
JS14 already supplies the every-instrument critical strip and the
sub-spectral uniform $O(t^{-1})$ value estimate. JS15 supplies finite
Gram stability and zero-corner handling; JS16 supplies the compact-uniform
spectral product/value layer, with JS17's common original realization.
Only the other uniform regimes and next terms remain outstanding. These
are asymptotics, not exact finite-frontier values. The source is
mathematical input independently of any publication status.

The JS/TB dictionary is $d_0^{\rm TB}=d_f$,
$\zeta^{\rm TB}=b_{\rm off}=-z_f$, $\gamma^{\rm TB}=\gamma_f$,
$A^{\rm TB}(p)=a(p)$, $B^{\rm TB}(p,q)=D_J(p,q)$ and
$g^{\rm TB}=g_+$. The clamped-edge derivative test has
$\phi_\varpi'(x_+)=-E_{\rm edge}/P_{+,y}$ with $P_{+,y}>0$;
TB's $c(p)=-v(p)E_{\rm edge}/C'$ has $C'>0$. Thus the two edge
criteria coincide, while interior stationarity is the same
$T(p,q)=0$. TC uniqueness and the common global certificate identify
both selections wherever TB's local bands apply. The changed-cost
counterexample to a decreasing-curvature shortcut in TB does not refute
JS's convex contour selection, which does not assume that shortcut.
No single-transition or global $C^2$ conclusion follows.

The current [AURIC control construction, §§35–36, Definition 55.1,
Assumption 55.2, Proposition 55.3 and Theorem 56.1][AO67]
uses independently driven drift-free local PXP flips, its specified
reusable phase at positions $(1,3)$, and supplied encoding and
initialization. Those controls are not granted by the original fixed
sum waiting menu. Even approximate unitary universality at that
contract does not grant this specimen's acquisition, calibrated
$D,T,S$, joint resource counting or FIRST services. The
[self-calibrating relation theorem, §39][CAL67] assumes a positive
rank-one relation, nonzero common polynomial gain of degree at most
$k$, drift of degree at most $d$, and the exact integer sequence clock.
Its $3k+d+5$ reads recover the normalized relation and gain product;
individual zero gain positions are allowed, identically zero gain is
excluded. It is not unknown-clock or physical apparatus calibration.
The [general-target incidence-cycle theorem, §§1 and 10][GT67] assumes
canonical beta initialization, completed predecessors, separately
authorized boot, strong atomic patch primitives and a paid foundation.
It does not implement those primitives through the lower engine or
complete the raw original task. These explicit contracts have no proved
common quantum operation/resource realization bridge to §75.

**Definition 77.3 (the still-required original programme).** The full
quantum-first programme retains, without restriction to this layer or
these constructions, all the following obligations. First is the
complete evaluated original weak $\mathcal T_A(s)$ for every feasible
finite interior point, with a common positive global contact/weight
family, all rank/contact/degenerate changes and a complete parameter
atlas. An implicit SDP, fixed even family, finite KKT system or bare
algorithm is not that evaluation. The original precontact/contact
$K(s)$ coefficients, orientation, gluing and degenerate seams remain
required, alongside the credited postcontact formulas and coefficient
existence. Global minimum actual finite-$A$ alphabets remain separate
from the exact axis-layer four/five counts and existing existence bounds.

The limiting budget selection just credited still leaves transition-root
inventory and the remaining uniform rates, next terms and critical
five-label/static-contact joint scales. CG root/isolation/Jacobian/rank,
normalization, minimax and sharp-cost premises remain conditional;
source-box inequalities or finite numerical diagnostics do not discharge
them. Lawful access to the sole unknown specimen, physical calibration,
coherent joint acquisition/storage/counting and duration, decoder
actuation, an aligned clock, FIRST absorption without subsequent carrier
action, and archive/source/epoch/controller/permission semantics remain
unproved native bridges. OriginalControl remains geometry rather than
an actuator. No finite source unit, conditional theorem or compatible
native contract completes or narrows the unchanged through-2027 goal.

[FA67]: FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md
[TA67]: FIB_NATIVE_TOTAL_ACTUAL_ACQUISITION_ALPHABET.md
[JS67]: FIB_NATIVE_JOINT_ENDPOINT_SATURATION_BOUNDARY.md
[TB67]: FIB_NATIVE_JOINT_TRANSITION_BANDS_AND_SELECTED_BRANCHES.md
[AO67]: AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md
[CAL67]: FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md
[GT67]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GENERAL_TARGET_INCIDENCE_CYCLE.md
[HMS67]: https://arxiv.org/pdf/2604.15072v1
[DR67]: https://arxiv.org/pdf/0903.3639v1
[DM67]: https://arxiv.org/pdf/1105.3575v1
[MG67]: https://pagesperso.ls2n.fr/~jermann-c/dw/mggj-jogo14.pdf
[LS67]: https://arxiv.org/pdf/2212.11225v2
[HT67]: https://arxiv.org/pdf/2603.27676v1

## 追加锚（本行以下为增补区）

## 78. 接触前系数的原始类、条件与规范

**约定 78.1（原始仪器和继承前提）。** §78–87 在本卷 §58.1 的原始类中工作：在 reached cut 只有一份未知五模 specimen；仪器在输入到来前共同固定，不获知历史 $y,e,n$，不使用先验、额外 specimen、copy、reset、retry、postselection、history oracle 或未计入的未来可访问量子份额。保留十二个历史 $y\in\{5,16,27\}$、$e,n\in\{\pm1\}$，完整 stopped-cq 误差取原范数的 HALF，不除以接受概率，也不以 diamond norm 代换。保留 live 相干、任意被动参考的条件部分迹，以及 $\ell\in\{0,1,2,3,13\}$ 五个分别标记的 exact-time Borel 失败 CP 测度。

所有竞争者仍是原全复数、多 Kraus 类；有限、可数及约定的有限 fibre、可积 Kraus 可测扩展分别沿用 JR53.1、RC58.1 和 FA87 的几乎处处含义，不扩展到任意无限维编码。被丢弃的 Kraus 索引不可读。实际报告约束始终是 $\mathsf V\ge s$；其他二元 effect 坐标自由。资源成本是所有未来共同可访问量子份额的**联合**获取维数至少三的最坏历史概率，并限制在所有原误差最优者中达到原 sharp cost $\mathsf C(s)$ 的仪器，绝非某个展示分解、选定输入或期望维数。

本节的定理有以下明确的文稿前提。[CG13][CG78] 的孤立九坐标源根、根处秩和 TP 恒等式、CG14–16 的完整输出 HALF minimax 和十二误差结论作为源供应；CG17 的平均 live 和预平均 support/effect 结论只按其原范围使用。[JR34–45][JR78]，尤其 JR42 的未平均实暴露面和 sharp-cost 等号桥，另行供应全部原复数、多 Kraus 竞争者的 low/high coefficient Grams、无 supported high failure 及实 null live 产品。[FA69][FA67] 的双重秩刚性、容量和 FA72 的端点分裂沿用其整个 fibre 假设。JR50–54 供应初始平台、严格递减和 residual 报告/高度符号约化；RC58–66 供应静态全局最优性、选定接触根、完整静态曲线和接触后的连续对偶分支。源根的局部唯一性不等于全局唯一性，也不认证另一个 RC 接触根。以下源特定评价均在这些前提之内，不将普通算术证据提升为 Lean/kernel 证明、物理实现或无条件源认证。

活动量按每个**实际生成的整个联合 decoder fibre** 定义为

$$
\mathsf A(\Phi)=\max_{\gamma\ {\rm actual}}
\int_0^1\|R_\gamma(u)\|_{\rm op}\,du\le A.
$$

它不是期望跳跃数、瞬时率最大值、跨标签最大值的积分或后选择平均。吸收为正，not-yet-failed controls 为 TP，终端 survivor processing 为 TP；live survival 严格正。实际 FIRST 事件发生在绝对时间 $6+u$，无截止时刻强制吸收、终端失败原子或失败后的正载体动作。下界保留每个允许的原失败时间 CP 法则；§86 的 $g$ 只是一个共同达到族的选择。

**定义 78.2（系数规范）。** 对 $A>0$ 置

$$
b_A=e^A-1,\qquad \eta_A=b_A^{-1},\qquad
K(s)=\lim_{A\to\infty}b_A[\mathcal T(s)-\mathcal T_A(s)].
\tag{RC.105}
$$

$\mathcal T$ 是无活动上界的 sharp-cost 原误差最优类的最大实际记录 TV，$\mathcal T_A$ 加上上述活动约束。FA80 已供应固定强度系数的存在性；以 $e^A$ 代替 $b_A$ 得到同一极限。以下给出接触前的具体源值、谱取向及跨接触的一致余项，不把存在性本身作为新增结果。

**命题 78.3（有限活动排除 supported 非零 failure-only 标签）。** 对整个 fibre 上的任意正输入 $X$，FA68 的 survivor coercivity 给出

$$
\operatorname{tr}\mathcal S_{\gamma,1}(X)
\ge e^{-A}\operatorname{tr}X.
\tag{RC.106}
$$

因而原支持上非零的 encoder 不能有零 composite live map。静态 JR/TA 中可独立生成的 certain-failure spectral rows 不能直接充当有限 $A$ acquisition labels。结合约定 78.1 的 sharp-cost 实等号面，每个 supported failure 必须按 FA69 容量附着于一个非零 low live 产品。

证明。正吸收和 TP survivor controls 给出 $d\operatorname{tr}X_u/du\ge-\|R_\gamma(u)\|\operatorname{tr}X_u$；积分得 (RC.106)，终端 TP 保持 surviving trace。对任一使 supported encoder 输出非零的正输入，该下界严格正，故 composite live 不可能为零。实等号面和双重秩刚性再给出 §79 的一射线表示。这不排除原支持上为零、全 $M_5$ 上非零的 encoder；这些标签仍须计入实际字母表和整个 fibre 活动量，但不为它们虚构正 $p_j$ 或 null 射线。$\square$

## 79. 源参数、物理白化与谱承载质量

**定义 79.1（归一化源和容量）。** 令 $a_y=(\sqrt{y/128},\sqrt{(64-y)/128},1/\sqrt2)^T$，$U_{e,n}=\operatorname{diag}(e,n,1)$。原 supported 输入是

$$
\rho^{(3)}_{y,e,n}=U_{e,n}a_ya_y^TU_{e,n}^\dagger,\qquad
\rho^{(5)}_{y,e,n}=E\rho^{(3)}_{y,e,n}E^\dagger,
$$

其中 $E=((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2):\mathbb C^3\to\mathbb C^5$ 是原等距嵌入。以下 $\rho$ 和 $\Delta$ 未标维数时使用 supported qutrit 坐标。保留

$$
D=\operatorname{diag}(h_0,h_1,h_2),\qquad
T=a|0\rangle\langle1|+b|1\rangle\langle0|,
$$

$$
S=c|0\rangle\langle2|+d|2\rangle\langle0|,\qquad
M=\operatorname{diag}(0,m_1,m_2),
$$

以及根处恒等式

$$
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3.
$$

定义

$$
\theta=\frac{ab}{h_0h_1},\quad
\omega=\frac{cd}{h_0h_2},\quad
\delta=\theta+\omega,\quad s_0=\sqrt\delta,
$$

$$
\alpha=\frac{\theta}{\delta},\quad
\beta=\frac{\omega}{\delta},\quad
L=\operatorname{diag}(s_0,1,1),\quad L_0=L^2,
$$

$$
Q=\operatorname{diag}(1,-\alpha,-\beta),\qquad
C=\frac{e_0e_1^T+e_1e_0^T}{2}.
$$

在约定 78.1 的源根处， $\alpha>\beta>0$ 、 $\alpha+\beta=1$。令

$$
\Delta=\rho_{27,+,+}-\rho_{5,+,+},\qquad
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),
\quad (K_0,K_1,K_2)=(D,T,S),
$$

$$
G=LNL=
\begin{pmatrix}
g_0&\mathsf x&\mathsf y\\
\mathsf x&g_1&\mathsf z\\
\mathsf y&\mathsf z&g_2
\end{pmatrix},
\qquad
H_0=(1-\delta)N_{00}.
\tag{RC.107}
$$

这里 $\mathsf x,\mathsf y>0$ 、 $\mathsf z<0$。对完整 null 椭圆

$$
\mathscr C=\{h=(1,z,w)^T:\alpha z^2+\beta w^2=1\}
$$

定义

$$
\ell(h)=h^TGh,\qquad K_h=s_0D+zT+wS,
$$

$$
n_h=\left(0,\frac{dw}{h_2},-\frac{bz}{h_1}\right)^T,
$$

$$
\operatorname{cap}(h)=
\frac{h_1^2h_2^2s_0^2+a^2h_2^2z^2+c^2h_1^2w^2}
{h_0^2s_0^2+b^2z^2+d^2w^2}>0.
\tag{RC.108}
$$

FA69–72 给出的 supported 非零原实际 low label 数据为

$$
\sqrt{p_j}K_{h_j},\qquad
N_j=p_j b_j n_{h_j}n_{h_j}^T,
$$

$$
p_j>0,\qquad 0\le b_j\le b_A\operatorname{cap}(h_j),
$$

$$
\sum_jp_jh_jh_j^T=I_3,\qquad
\sum_jN_j=M,\qquad
\sum_jp_j|z_j|\ge\tau:=s/s_0.
\tag{RC.109}
$$

这些 $p_j$ 是 coefficient weights，不是 acquisition 概率。对五模密度 $\rho^{(5)}$，实际 acquisition 概率是

$$
\operatorname{tr}\!\left[
E\bigl(p_jK_{h_j}^{\dagger}K_{h_j}+N_j\bigr)E^\dagger
\,\rho^{(5)}
\right].
$$

### 79.2 两个物理谱效应

在原坐标 $(1,2)$  上令

$$
M_2=\operatorname{diag}(m_1,m_2),
$$

$$
\Xi=M_2^{1/2}\Delta_{\{1,2\}}M_2^{1/2}
=
\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},
$$

$$
d_f=\frac{11m_1}{64},\qquad
z_f=\frac{\sqrt{m_1m_2}(\sqrt{37}-\sqrt{59})}{16}<0,
\qquad
L_f=\sqrt{d_f^2+4z_f^2}.
$$

取

$$
\lambda_\epsilon=\frac{-d_f+\epsilon L_f}{2},\qquad \epsilon=\pm1,
$$

$$
t_f=\frac{-2z_f}{d_f+L_f},\qquad
e_-=\frac{(1,t_f)^T}{\sqrt{1+t_f^2}},\qquad
e_+=\frac{(t_f,-1)^T}{\sqrt{1+t_f^2}},
$$

$$
B_\epsilon^{\rm sp}
=M_2^{1/2}e_\epsilon e_\epsilon^TM_2^{1/2},
\tag{RC.110}
$$

并在坐标零上补零。于是

$$
B_+^{\rm sp}+B_-^{\rm sp}=M,\qquad
\operatorname{tr}(\Delta B_\epsilon^{\rm sp})=\lambda_\epsilon.
$$

定义

$$
V_f=\frac{m_2h_1^2}{b^2},\qquad
W_f=\frac{m_1h_2^2}{d^2},
$$

$$
\chi_\epsilon
=\alpha V_f(e_\epsilon)_2^2+\beta W_f(e_\epsilon)_1^2.
$$

选定 $z>0$  的基准取向：

$$
z_\epsilon=
\frac{\sqrt{V_f}|(e_\epsilon)_2|}{\sqrt{\chi_\epsilon}}>0,
$$

$$
w_\epsilon=
-\frac{\operatorname{sgn}((e_\epsilon)_2)\sqrt{W_f}(e_\epsilon)_1}
{\sqrt{\chi_\epsilon}},
$$

$$
h_{\epsilon,o}=(1,o z_\epsilon,o w_\epsilon)^T,\qquad o=\pm1.
\tag{RC.111}
$$

因此 $w_+>0>w_-$，并且

$$
B_\epsilon^{\rm sp}
=\chi_\epsilon n_{h_{\epsilon,o}}n_{h_{\epsilon,o}}^T.
$$

最后置

$$
\nu_\epsilon=
\frac{\chi_\epsilon}{\operatorname{cap}(h_{\epsilon,+})}>0.
\tag{RC.112}
$$

承载整个 $B_\epsilon^{\rm sp}$  的预算饱和 live mass 正是

$$
p_\epsilon=\eta_A\nu_\epsilon.
\tag{RC.113}
$$

其最小整个 fibre 活动量为

$$
\log\!\left(1+\frac{\nu_\epsilon}{p_\epsilon}\right)=A.
$$

所有白化均发生在物理 failure support 上；特别是下面使用

$$
q_\epsilon(h)=
\left|e_\epsilon^TM_2^{-1/2}(n_h)_{\{1,2\}}\right|^2.
\tag{RC.114}
$$

## 80. 接触前三射线族、平台选根和强度逆式

**定义 80.1（三射线 frame）。** 以下静态参数记为 $r$，不与 $b_A$  混用。置

$$
k_r=\sqrt{\alpha+\beta r^2},\qquad
d_r=1+\alpha+(1+\beta)r^2,
$$

$$
B_r=\alpha r^2+\beta,\qquad
R_r=\sqrt{\beta^2(1+\alpha)+\alpha^2(1+\beta)r^2},
$$

$$
u_1=\frac{\beta k_r+rR_r}{B_r},\qquad
v_1=\frac{\alpha k_rr-R_r}{B_r},
$$

$$
u_2=\frac{\beta k_r-rR_r}{B_r},\qquad
v_2=\frac{\alpha k_rr+R_r}{B_r}.
$$

定义

$$
f_0(r)=\frac{(k_r,-1,-r)^T}{\sqrt{d_r}},
$$

$$
f_i(r)=\frac{(1,u_i,v_i)^T}{\sqrt{1+u_i^2+v_i^2}},
\qquad i=1,2,
\qquad F(r)=(f_0,f_1,f_2).
\tag{RC.115}
$$

直接代入可得

$$
F^TF=I,\qquad f_i^TQf_i=0.
$$

在 $r_\star\le r\le r_{\rm c}$ 上，

$$
u_1>0,\quad v_1<0,\qquad u_2<0,\quad v_2>0.
$$

对应的 coordinate-zero-one rays 与权重为

$$
a_i=\frac{f_i}{(f_i)_0},\qquad
\pi_i=(f_i)_0^2>0.
\tag{RC.116}
$$

它们满足

$$
\sum_{i=0}^2\pi_i a_ia_i^T=I.
$$

原静态报告和 live height 符号分别为

$$
(r_0,r_1,r_2)=(-,+,-),\qquad
(\operatorname{sgn}\ell(a_0),\operatorname{sgn}\ell(a_1),
\operatorname{sgn}\ell(a_2))=(-,+,+).
\tag{RC.117}
$$

这些符号与该族的原始全局静态最优性来自 JR50–54／RC60–63 静态供应。令

$$
h_{\rm fr}(r)=2(f_1)_0(f_1)_1
=\frac{2u_1}{1+u_1^2+v_1^2},
$$

$$
\psi(r)=f_0(r)^TGf_0(r)=\frac{P(r)}{d_r},
$$

$$
P(r)=g_0k_r^2+g_1+g_2r^2
-2\mathsf x k_r-2\mathsf y k_rr+2\mathsf z r.
\tag{RC.118}
$$

### 80.2 平台端点的确切选择

令 $r_\star$  为方程

$$
d_rP'(r)-2(1+\beta)rP(r)=0
\tag{RC.119}
$$

的唯一正根，其中

$$
P'(r)=
2r(\beta g_0+g_2)+2\mathsf z
-\frac{2\beta r(\mathsf x+\mathsf y r)}{k_r}
-2\mathsf y k_r.
$$

原静态供应给出选择区间

$$
\frac{17}{20}<r_\star<\frac9{10}.
\tag{RC.120}
$$

这里的唯一性也有直接解析解释。置 $p=(f_0)_2^2$，则

$$
(f_0)_1^2=\frac{1-(1+\beta)p}{1+\alpha},\qquad
(f_0)_0^2=\frac{\alpha+(\beta-\alpha)p}{1+\alpha}.
$$

这里 $p_0=(f_0)_0^2$、$p_1=(f_0)_1^2$ 都是 $p$ 的正仿射函数。$\psi$ 是一个线性函数，加上

$$
-2\mathsf x\sqrt{p_0p_1}
-2\mathsf y\sqrt{p_0p}
-2|\mathsf z|\sqrt{p_1p}.
$$

对正仿射函数 $u,v$，

$$
(\sqrt{uv})''
=-\frac{(u'v-uv')^2}{4(uv)^{3/2}}.
$$

故 $\psi$  在 $0<p<1/(1+\beta)$  上严格凸，其两端导数分别趋于 $-\infty,+\infty$。这确定唯一根，而不是留下一个待优化的最小化。源给出的有理区间 (RC.120) 用于选定实际静态分支。记

$$
\tau_{\rm p}=h_{\rm fr}(r_\star),\qquad s_{\rm p}=s_0\tau_{\rm p}.
$$

实际静态接触参数 $r_{\rm c}$  在 §84.1 用 RC 选根完全绑定；其供应区间为

$$
1.04175447537<r_{\rm c}<1.04175447539,
$$

$$
\tau_{\rm c}=h_{\rm fr}(r_{\rm c}),\qquad
.9962433511188<\tau_{\rm c}<.9962433511192,
\qquad s_{\rm c}=s_0\tau_{\rm c}.
\tag{RC.121}
$$

### 80.3 从强度直接恢复 $r$

对 $0\le\tau\le\tau_{\rm p}$，置 $r(\tau)=r_\star$。对 $\tau_{\rm p}<\tau\le\tau_{\rm c}$，可以直接使用根式

$$
\kappa_\tau=
\frac{\beta+\sqrt{\beta^2+(\alpha-\beta)(1+\beta)\tau^2}}
{(1+\beta)\tau},
$$

$$
u_\tau=\sqrt{\frac{\kappa_\tau^2-\alpha}{\beta}},\qquad
\mathcal R_\tau=
\sqrt{\beta^2(1+\alpha)+\alpha^2(1+\beta)u_\tau^2},
$$

$$
\boxed{\quad
r(\tau)=
\frac{1-\alpha\kappa_\tau^2}
{u_\tau+\kappa_\tau\mathcal R_\tau}.
\quad}
\tag{RC.122}
$$

在所列区间，根式取正根、分母严格正。这是 $h_{\rm fr}(r)=\tau$ 的选定分支。为核对选根，令 $u=-v_1/u_1>0$ 和 $\kappa=\sqrt{\alpha+\beta u^2}$。由 $H(u)=\tau$ 得

$$
\tau[(1+\beta)\kappa^2+(\beta-\alpha)]=2\beta\kappa.
$$

$\alpha>\beta$ 和 $\tau>0$ 使该二次式只有一个正 $\kappa$，正是上式的 $\kappa_\tau$。正交关系 $k_r\kappa+ru=1$ 对正 $r$ 严格递增；平方并有理化其选定根得到 (RC.122)。§81 证明 $h_{\rm fr}'(r)>0$，故不存在同一分支的第二个 $r$。$\tau=0$ 单独用平台分支，不使用含 $1/\tau$ 的式子。静态值供应因而可写为

$$
j(\tau)=\operatorname{tr}G-2\psi(r(\tau)),
\qquad
\mathcal T(s_0\tau)=\frac{H_0+L_f+j(\tau)}2.
\tag{RC.123}
$$

## 81. 三射线联合矩映射可逆与显式静态对偶

考虑三个正权重 null atoms 的映射

$$
\mathscr M:
(\pi_i,\phi_i)_{i=0}^2
\longmapsto
\left(
\sum_i\pi_i a(\phi_i)a(\phi_i)^T,\
\sum_i\pi_i|a(\phi_i)_1|
\right).
\tag{RC.124}
$$

其中 $a(\phi)=(1,\cos\phi/\sqrt\alpha,\sin\phi/\sqrt\beta)^T$，局部角度图取在各主射线处。Gram 分量属于五维空间

$$
\mathscr V_Q=\{X=X^T:\operatorname{tr}(QX)=0\}.
$$

所以 (RC.124) 的定义域和值域都是六维。

**引理 81.1（实际六维联合矩映射）。** 整个 $r_\star\le r\le r_{\rm c}$ 区间，包括接触处，$D\mathscr M$ 可逆。

证明。写

$$
q=F^TQF,\qquad c=F^TCF.
$$

由于 $q_{ii}=0$  且

$$
2q_{01}q_{02}q_{12}=\det q=\det Q=\alpha\beta>0,
\tag{RC.125}
$$

三个非对角元都不为零。把列变化写成 $\dot F=FZ$。null 切向条件是

$$
\sum_jq_{ij}Z_{ji}=0.
$$

保持 Gram 的条件是 $Z+Z^T=0$。两组条件的共同解恰为一维：

$$
Z_{01}=q_{02}q_{12}t,\qquad
Z_{02}=-q_{01}q_{12}t,\qquad
Z_{12}=q_{01}q_{02}t.
\tag{RC.126}
$$

沿此方向，对比度的变化为

$$
4tq_{02}(q_{12}c_{01}-q_{01}c_{12}).
\tag{RC.127}
$$

现在直接证明它不为零。令

$$
u(r)=-v_1(r)/u_1(r)>0.
$$

正报告列可以写成

$$
f_1=
\frac{(\sqrt{\alpha+\beta u^2},1,-u)^T}
{\sqrt{(1+\alpha)+(1+\beta)u^2}}.
$$

与 $f_0$  正交等价于

$$
k_r\sqrt{\alpha+\beta u^2}+ru=1.
$$

因此

$$
u'(r)=-
\frac{\beta r\sqrt{\alpha+\beta u^2}/k_r+u}
{r+\beta u k_r/\sqrt{\alpha+\beta u^2}}<0.
\tag{RC.128}
$$

另一方面，

$$
H(u)=
\frac{2\sqrt{\alpha+\beta u^2}}
{(1+\alpha)+(1+\beta)u^2}
$$

满足

$$
H'(u)=
\frac{2u[\beta^2-2\alpha-\beta(1+\beta)u^2]}
{\sqrt{\alpha+\beta u^2}
[(1+\alpha)+(1+\beta)u^2]^2}<0.
\tag{RC.129}
$$

故 $h_{\rm fr}'(r)=H'(u)u'(r)>0$，包括 $r=r_{\rm c}$。实际 frame 曲线保持 Gram；因 $f_0$ 的方向随 $r$ 非常数，其导数是上述一维 Gram 核的非零向量。因此 (RC.127) 在该核上非零，核中没有能同时消去对比度的非零方向。六维定义域和值域同维，联合导数可逆。 $\square$

这里的六个变量是三个正权重及其三个 null 角度；结论直接作用于实际 Gram 加绝对对比度矩映射。

**约定 81.2（主射线的一致正性）。** 在继承的源盒和选定分支区间 $[r_\star,r_{\rm c}]\subset[.85,1.042]$ 上，三个 $\pi_i$ 的下界严格正，$u_1,-v_1,-u_2,v_2$ 严格正，且静态高度符号保持 $(-,+,+)$。可取以下粗有理下界：

| 量 | 严格下界 |
| --- | --- |
| $\min_i\pi_i$ | $.17486$ |
| $u_1$、$-v_1$ | $1.0657$、$.05902$ |
| $-u_2$、$v_2$ | $.7482$、$1.7685$ |
| $u=-v_1/u_1$ | $.05526$ |
| $-H'(u)$、$-u'(r)$ | $.05802$、$.1658$ |
| $\lvert\ell(a_0)\rvert$、$\ell(a_1)$、$\ell(a_2)$ | $.00115$、$.00429$、$.00262$ |
| $\lvert c_{01}/q_{01}-c_{12}/q_{12}\rvert$ | $.04315$ |

这些是 RC58 源盒与上述闭区间代入 (RC.115)–(RC.129) 的有理外包络后果，使用的是整个区间。它们作为该源盒的条件性数值界，不是新的源根或接触根认证。解析上一致可逆还可直接从引理 81.1、导数连续性和紧致性取得：主权重有正下界，所选角度图无报告轴或高度零交叉，$D\mathscr M$ 的逆范数在紧区间有有限上界。

### 81.3 明确恢复静态对偶

令

$$
H=F^TGF,\qquad c=F^TCF,\qquad q=F^TQF,
$$

$$
\lambda(r)=
\frac{H_{02}/q_{02}-H_{01}/q_{01}}
{c_{01}/q_{01}-c_{12}/q_{12}}
=\frac{2\psi'(r)}{h_{\rm fr}'(r)}.
\tag{RC.130}
$$

引理 81.1 保证分母不为零。并且

$$
\lambda(r_\star)=0,\qquad
\lambda(r)>0\quad(r_\star<r\le r_{\rm c}).
$$

定义对称矩阵

$$
\widehat{\mathcal Y}=
\begin{pmatrix}
-H_{00}-\lambda c_{00}
&
-H_{01}-\lambda c_{01}
&
-H_{02}-\lambda c_{02}
\\
*
&
H_{11}+\lambda c_{11}
&
H_{12}-\lambda c_{12}-2H_{02}q_{12}/q_{02}
\\
*
&
*
&
H_{22}-\lambda c_{22}
\end{pmatrix},
$$

$$
\mathcal Y(r)=F(r)\widehat{\mathcal Y}(r)F(r)^T.
\tag{RC.131}
$$

这些都是显式矩阵运算。令

$$
D_r(h)=h^T\mathcal Y(r)h-\lambda(r)|z|.
$$

则

$$
D_r(h)\ge|\ell(h)|\qquad(h\in\mathscr C),
\tag{RC.132}
$$

$$
\operatorname{tr}\mathcal Y-\lambda h_{\rm fr}(r)
=\operatorname{tr}G-2\psi(r).
\tag{RC.133}
$$

**命题 81.3（全椭圆对偶）。** 在约定 78.1 的静态全局最优性前提下，(RC.132)–(RC.133) 成立。

证明。三个接触列的互补和角向切触方程给出 (RC.130)–(RC.131)。任取一个新的 null atom，加入微小正质量，再用引理 81.1 精确修复原三条射线的 Gram 和对比度。原静态全局最优性要求目标的一阶增量非正，恰好得到 (RC.132)。任意插入点都可如此处理，故得到全椭圆不等式；仅有三个点的切触方程本身不足以给出该不等式。迹恒等式由 $F^TF=I$、$\operatorname{tr}C=0$ 和 $h_{\rm fr}=2c_{11}$ 直接相加得到。$\square$

## 82. 接触前系数、全类下界和共同修复上界

对 $\epsilon=\pm1$  定义

$$
Z_\epsilon(r)=\mathcal Y(r)-\epsilon G,
$$

$$
a_\epsilon(r)=
(Z_\epsilon)_{00}
+(Z_\epsilon)_{11}z_\epsilon^2
+(Z_\epsilon)_{22}w_\epsilon^2
+2(Z_\epsilon)_{12}z_\epsilon w_\epsilon
-\lambda z_\epsilon,
$$

$$
b_\epsilon(r)=
(Z_\epsilon)_{01}z_\epsilon+(Z_\epsilon)_{02}w_\epsilon.
\tag{RC.134}
$$

**定理 82.1（接触前系数与一致余项）。** 在约定 78.1 的原始类和全部继承前提下，对全部 $0\le\tau\le\tau_{\rm c}$，

$$
\boxed{
K(s_0\tau)=
\frac12\sum_{\epsilon=\pm1}
\nu_\epsilon
\left[a_\epsilon(r(\tau))-2|b_\epsilon(r(\tau))|\right].
}
\tag{RC.135}
$$

此外存在源决定的有限 $B,C>0$，使得

$$
\boxed{
\left|
\mathcal T(s)-\mathcal T_A(s)-\frac{K(s)}{b_A}
\right|
\le\frac{C}{b_A^2},
\qquad
0\le s\le s_{\rm c},\quad b_A\ge B.
}
\tag{RC.136}
$$

式 (RC.135) 的输入全部由 (RC.107)–(RC.122)、(RC.130)–(RC.134) 确定。它不含自由的静态对偶、测度优化或未评价的 tangent minimization。

### 82.2 全部谱取向选择

对每个谱号，首阶取向的全部最优选择是

$$
\begin{array}{c|c}
b_\epsilon(r)<0&o=+1\\
b_\epsilon(r)>0&o=-1\\
b_\epsilon(r)=0&o=+1\text{ 与 }o=-1\text{ 均最优}
\end{array}
\tag{RC.137}
$$

在等号处，可以把 $B_\epsilon^{\rm sp}$  任意按非负比例分给两个取向，并按相同比例分配 (RC.113) 的 live mass。除此之外，该两点取向问题没有剩余优化者。这张表评价的是谱承载的首阶取向问题；它不声称分类所有精确有限 $A$  最优仪器。

### 82.3 覆盖全部原竞争者的下界

证明下界。使用 FA72 的容量端点分裂上界，令 $\mu$  表示 pure-live 测度， $\sigma$  表示 saturated failure 系数测度。其必要约束为

$$
\int hh^T\,d\mu
+\eta_A\int\frac{hh^T}{\operatorname{cap}(h)}\,d\sigma=I,
$$

$$
\int n_hn_h^T\,d\sigma=M,
$$

$$
\int|z|\,d\mu
+\eta_A\int\frac{|z|}{\operatorname{cap}(h)}\,d\sigma\ge\tau.
\tag{RC.138}
$$

对原来一条 $(p,b,h)$，端点分裂令 $t=b/[b_A\operatorname{cap}(h)]\in[0,1]$：pure 部分质量 $p(1-t)$，saturated 部分 live 质量 $pt$，其失败系数为 $pb$。这样保持原 Gram、失败 effect 和可用绝对对比度。标量绝对值的凸性给出原未分裂标签高度不超过分裂后的高度；可数和约定的可积可测情形逐项或积分使用同一不等式。该分裂只用于原实际 TV 的上界，不给仪器新增可读记录，也不把丢弃的 Kraus 索引变成控制记录。写

$$
f(h)=n_h^T\Delta n_h
=\lambda_+q_+(h)+\lambda_-q_-(h),
$$

$$
m(h)=\lambda_+q_+(h)-\lambda_-q_-(h).
$$

物理白化恒等式给出

$$
\int q_\epsilon\,d\sigma=1,\qquad
\int m\,d\sigma=L_f.
$$

由 (RC.132)–(RC.133)，两倍 TV 缺额至少为

$$
\int
\left[
m-\left|f+\eta_A\ell/\operatorname{cap}\right|
+\eta_A D_r/\operatorname{cap}
\right]d\sigma.
\tag{RC.139}
$$

被省略的 pure-live slack 和对比度 slack 都非负。零阶谱 slack

$$
m-|f|=2\min\{\lambda_+q_+,-\lambda_-q_-\}
$$

只在四个谱相容取向处消失。$M_2$ 可逆，$n_h$ 在椭圆上从不为零；从 null 椭圆到物理射影方向的映射由一个可逆二维线性变换诱导，局部导数非零。因此在每个零点处，另一谱分量是一个具有非零线性因子的平方。可选互不相交的固定小邻域，谱 slack 在其中至少为到零点距离平方的正常数倍；离开这些邻域则由紧致性取得严格正的统一下界。令

$$
\kappa_\epsilon(r)
=\nu_\epsilon[a_\epsilon(r)-2|b_\epsilon(r)|].
$$

在对应谱点，

$$
\frac{D_r-\epsilon\ell}{\operatorname{cap}}
\ge \kappa_\epsilon q_\epsilon.
$$

在匹配谱点 $q_\epsilon=1/\chi_\epsilon$，另一 $q$ 为零，所以该式的常数与 (RC.112) 一致。在它的小邻域内，$f$ 的非零谱符号不变；对足够小的 $\eta_A$，$f+\eta_A\ell/\operatorname{cap}$ 也保持该符号。函数 $(D_r-\epsilon\ell)/\operatorname{cap}$ 在紧参数段上一致 Lipschitz，$\kappa_\epsilon(r)$ 一致有界，即使取向并列也不改变此界。另一谱 $q$ 在匹配点二阶消失，故减去 $\eta_A\sum\kappa_\epsilon q_\epsilon$ 后，有一个 $c d^2-\eta_A C_1d-O(\eta_A d^2)$ 下界；减小 $\eta_A$ 阈值后可吸收最后的二次项。因而配方

$$
c\,d^2-\eta_A C_1d\ge-C_2\eta_A^2
$$

给出各邻域的下界；邻域外严格正的零阶谱 gap 支配有界的 $\eta_A$ 扰动，故得到整个椭圆上的下界

$$
m-\left|f+\eta_A\ell/\operatorname{cap}\right|
+\eta_A D_r/\operatorname{cap}
\ge
\eta_A\sum_\epsilon\kappa_\epsilon q_\epsilon-C_3\eta_A^2.
\tag{RC.140}
$$

 $\sigma$  的总质量被

$$
\frac{\operatorname{tr}M}
{\min_{h\in\mathscr C}\|n_h\|^2}
$$

一致控制。积分后得到

$$
2(\mathcal T-\mathcal T_{\rm instr})
\ge
\eta_A(\kappa_++\kappa_-)-C_4\eta_A^2.
\tag{RC.141}
$$

这个证明保留原全复数、多 Kraus 竞争者和任意允许的原失败时间 CP 法则。

### 82.4 同一个有限原子族的上构造

证明上界。按 (RC.137) 选择 $o_\epsilon$，加入两个实际饱和标签

$$
K_\epsilon^{\rm sat}
=\sqrt{\eta_A\nu_\epsilon}\,K_{h_{\epsilon,o_\epsilon}},
\qquad
N_\epsilon^{\rm sat}=B_\epsilon^{\rm sp}.
\tag{RC.142}
$$

用引理 81.1，将同一个静态三射线族的六个参数改变 $O(\eta_A)$，精确满足剩余 Gram

$$
I-\eta_A\sum_\epsilon
\nu_\epsilon h_{\epsilon,o_\epsilon}h_{\epsilon,o_\epsilon}^T
$$

和剩余对比度

$$
\tau_{\rm target}-\eta_A\sum_\epsilon\nu_\epsilon|z_\epsilon|,\qquad
\tau_{\rm target}=\max(\tau,\tau_{\rm p}).
$$

平台上将总对比度保持在 $\tau_{\rm p}$ ；活跃区间将其保持在请求的 $\tau$。剩余 Gram 的 $Q$ 迹仍为零，故它和剩余 contrast 确实属于 $\mathscr M$ 的值域空间。以 (RC.116) 中三个主权重和三个主角度为变量，对同一原子族应用局部逆映射，得到精确等式而非一阶残差。扰动范数至多为源决定常数乘 $\eta_A$，三个主要权重仍严格正。静态 slack $D_r-|\ell|$ 在原接触点取零且角向一阶导数为零；主射线高度符号不变，故二阶 Taylor 界给出三个 pure-live 标签总 slack 为 $O(\eta_A^2)$。饱和标签的实际高度差为

$$
\lambda_\epsilon+
\eta_A\nu_\epsilon\ell(h_{\epsilon,o_\epsilon}),
$$

其符号对充分大预算固定为 $\epsilon$。于是该同一族的缺额为

$$
\frac{\eta_A}{2}(\kappa_++\kappa_-)+O(\eta_A^2).
\tag{RC.143}
$$

§86 给出这族原子的完整 CP、参考、五 Borel 与 FIRST 实现。由于 $r\in[r_\star,r_{\rm c}]$  紧，三个主要权重有正下界，联合矩导数的逆一致有界，且只有有限个取向选择，上下界中的二阶常数可一致选取。这证明 (RC.135)–(RC.136)。 $\square$

## 83. 初始平台的明确常数和严格谱取向

令

$$
\psi_\star=\psi(r_\star)<0,\qquad
k_\star=k_{r_\star},\qquad d_\star=d_{r_\star}.
$$

在平台端点， $\lambda=0$。设 $\mu_\star=H_{02}/q_{02}$，则 (RC.131) 可化为

$$
\mathcal Y_\star
=G-2\mu_\star Q-2\psi_\star f_0f_0^T.
$$

所以在 null 椭圆上

$$
D_\star(h)=\ell(h)-2\psi_\star(f_0^Th)^2.
\tag{RC.144}
$$

**定理 83.1（整个平台的明确常数）。** 在约定 78.1 下，两个谱号的最优取向都唯一为 $o=+1$。因此，写 $h_\epsilon=h_{\epsilon,+}$，有

$$
\boxed{
K_{\rm flat}
=
\nu_-\ell(h_-)
-\frac{\psi_\star}{d_\star}
\sum_{\epsilon=\pm1}
\nu_\epsilon
(k_\star-z_\epsilon-r_\star w_\epsilon)^2.
}
\tag{RC.145}
$$

并且

$$
K(s)=K_{\rm flat}
\qquad(0\le s\le s_{\rm p}).
\tag{RC.146}
$$

证明。对正谱号，

$$
b_+(r_\star)
=
\frac{2\psi_\star k_\star}{d_\star}
(z_++r_\star w_+)<0.
$$

对负谱号，FA74 的物理相容参数给出

$$
w_-=-z_-/q_f,\qquad .18<q_f<.22.
$$

因此

$$
\frac{b_-(r_\star)}{2z_-}
=
\mathsf x-\frac{\mathsf y}{q_f}
+
\frac{\psi_\star k_\star}{d_\star}
\left(1-\frac{r_\star}{q_f}\right).
\tag{RC.147}
$$

下面使用 RC58 的源盒界和平台选根区间的粗有理推论：

$$
\mathsf x<.00238,\qquad \mathsf y>.00220,\qquad
|\psi_\star|<.00333,
$$

$$
k_\star<1,\qquad d_\star>2.68,\qquad
r_\star/q_f-1<4.
$$

其中 $G\succeq-.00333I$  可直接由所给七参数盒的逐行对角占优下界取得。故

$$
\frac{b_-(r_\star)}{2z_-}
<
-.00762+\frac{.00333\cdot4}{2.68}<0.
$$

两个选择都严格，(RC.145) 随即由 (RC.144) 得到。 $\square$

这包括 $s=0$  及平台右端；没有在 $s=0$  使用含 $1/\tau$  的逆式。

## 84. 实际静态接触值与两侧统一拼接

### 84.1 完全绑定接触参数

为了使接触公式没有未指定矩阵，以下重列实际使用的 RC 代数量。对 $(a,\varkappa)$  置

$$
D_a=\alpha(1-2a)+a^2,\quad
U_a=-\alpha+2a-a^2,\quad
V_a=\alpha-a^2,
$$

$$
n_a=(D_a,U_a,V_a)^T,\qquad \sigma_a=D_aU_a,
$$

$$
W_a=D_aCn_a-2\beta a\varkappa Qn_a,
$$

$$
H_a=-n_a^TQW_a,\qquad R_a=W_a^TQW_a,
$$

$$
Z_a=2H_aW_a+R_an_a,\qquad
\mathcal E_a=2H_aW_a^TW_a+D_aR_a\sigma_a,
$$

$$
g_a=Z_a^TGZ_a,
$$

$$
\mathcal P(a,\varkappa)
=
a^{-1}\det[D_a^2\sigma_aCZ_a-\mathcal E_aW_a,\ QZ_a,\ GZ_a],
$$

$$
\Omega(a,\varkappa)=
-4D_a\sigma_aH_a\mathcal E_a
-R_a\mathcal E_a n_a^Tn_a
+D_a\sigma_a Z_a^TZ_a.
\tag{RC.148}
$$

取 RC 已选定的唯一共同根

$$
\mathcal P(a_{\rm c},\varkappa_{\rm c})=0,\qquad
\Omega(a_{\rm c},\varkappa_{\rm c})=0,
$$

$$
.2951251<a_{\rm c}<.2951252,\qquad
.393637406<\varkappa_{\rm c}<.393637424.
\tag{RC.149}
$$

其选择沿 RC 的唯一 $\mathcal P=0$ 分支。这里 $\omega_{\rm RC}(a)=\operatorname{tr}A(a)-1$ 是 RC 的 aggregate eigenvalue，区别于源比率 $\omega$；在接触附近沿选支有 $\omega_{\rm RC}'<-.9$。这些根区间、窄 $r_{\rm c}$ 区间和选择结论作为 RC60–63 的选根前提继承；九坐标源根证书不认证这个接触根，粗 $(a,\varkappa)$ 盒的像也不替代窄区间。以下带下标 ${\rm c}$  的量均在此根取值。定义

$$
r_{\rm c}=(Z_{\rm c})_2/(Z_{\rm c})_1,
$$

$$
\gamma_{\rm c}
=
-\frac{2g_{\rm c}}
{\mathcal E_{\rm c}^2-D_{\rm c}^2\sigma_{\rm c}
(Z_{\rm c})_0(Z_{\rm c})_1}>0,
$$

$$
\lambda_{\rm c}=-\frac{\gamma_{\rm c}D_{\rm c}^2\sigma_{\rm c}}2.
\tag{RC.150}
$$

RC 的接触对偶为

$$
\mathcal Y_{\rm c}
=G+\lambda_{\rm c}C+\gamma_{\rm c}W_{\rm c}W_{\rm c}^T
\tag{RC.151}
$$

模一个 $Q$  倍数。该自由度不改变 null 值、迹或取向判别。

**定理 84.1（实际接触处的明确系数）。** 在约定 78.1 及本节选定根前提下，在实际接触处，两个最优谱取向仍唯一为 $o=+1$，而且

$$
\boxed{
K(s_{\rm c})
=
\nu_-\ell(h_-)
+
\frac{\gamma_{\rm c}}2
\sum_{\epsilon=\pm1}
\nu_\epsilon(W_{\rm c}^Th_\epsilon)^2.
}
\tag{RC.152}
$$

这是由源参数、两个物理谱效应和选定 RC 根确定的系数值。

证明。由 (RC.148) 直接展开，

$$
\begin{aligned}
b_+
={}&\gamma\beta^2a\varkappa D_a
\bigl[
-(V_a^2+4\alpha a\varkappa U_a)z_+\\
&\hspace{43mm}
+(U_a-4\beta a\varkappa)V_aw_+
\bigr].
\end{aligned}
\tag{RC.153}
$$

这里

$$
V_a^2+4\alpha a\varkappa U_a
>.79^2-4(.296)(.4)>0,
$$

而第二个括号系数为负，故 $b_+<0$。对负谱方向，

$$
\frac{b_-}{z_-}
=
2\mathsf x-\frac{2\mathsf y}{q_f}
+\frac{\lambda_{\rm c}}2
+\gamma_{\rm c}(W_{\rm c})_0
\left((W_{\rm c})_1-\frac{(W_{\rm c})_2}{q_f}\right).
\tag{RC.154}
$$

由 RC60–63 的选定接触盒及继承的源界得到保守界

$$
-(W_{\rm c})_0>.09,\quad
(W_{\rm c})_1>.0868,\quad
(W_{\rm c})_2<.0029,
$$

$$
(W_{\rm c})_1-(W_{\rm c})_2/q_f>.07,\qquad
\gamma_{\rm c}>2.5,\qquad \lambda_{\rm c}/2<.024.
$$

因此

$$
b_-/z_-<-.01524+.024-2.5(.09)(.07)<0.
$$

在这两个取向上 $h^TCh=|z|=z$，故 (RC.151) 的对比度项抵消，得到 (RC.152)。 $\square$

### 84.2 接触后的系数接口与统一修复

为明确接触右侧的输入，沿 RC60–63 的选定 $\mathcal P(a,\varkappa(a))=0$ 分支，$a<a_{\rm c}$ 对应 $s>s_{\rm c}$。使用本卷 (RC.8)、(RC.16)、(RC.31)、(RC.61) 的同一四射线静态族。为避免与 (RC.118) 的初始分支多项式 $P(r)$ 混淆，下式始终用 $\mathcal P$ 表示二维代数选根。令

$$
\gamma_a=-\frac{2g_a}
 {\mathcal E_a^2-D_a^2\sigma_a(Z_a)_0(Z_a)_1},\qquad
\Lambda_a=-\gamma_a D_a^2\sigma_a/2,
$$

$$
\mathcal Y_a=G+\Lambda_a C+\gamma_a W_aW_a^T\quad\pmod Q,
\qquad D_a^{\rm dual}(h)=h^T\mathcal Y_a h-\Lambda_a|z|.
$$

$D_a^{\rm dual}$ 是 dual function，区别于代数标量 $D_a$。RC 全局对偶供应 $D_a^{\rm dual}\ge|\ell|$。既有谱承载和 rank 条件修复机制给出的接触后表达式为

$$
K(s_0\tau(a))=\frac12\sum_{\epsilon=\pm1}\nu_\epsilon
\min_{o=\pm1}\{D_a^{\rm dual}(h_{\epsilon,o})
                         -\epsilon\ell(h_{\epsilon,o})\}.
$$

这里仅重列接触接口以明确拼接对象；接触后系数机制、FA80 的存在性和一般 rank 条件修复不是接触前三射线计算的新内容。下式的新增可用性来自引理 81.1 在**实际接触**仍成立。

RC 的第四条静态射线在接触处权重为零；原有三条权重严格正。引理 81.1 已证明这三条的联合矩映射在接触处可逆。在接触后的 RC 四射线分支上，采用如下同一修复规则：固定新增第四条射线的静态方向和静态权重；加入 (RC.142) 的谱承载标签；只修复原有三条正权重射线的六个参数。这里第四条的静态权重按实际 $s$ 取值，修复时才固定。这六维导数连续趋向引理 81.1 的接触导数，逆因而一致有界。整个构造不除以新增射线的小权重。

**推论 84.2（两侧一致拼接与联合极限）。** 在约定 78.1 的连续对偶分支前提下，存在 $d,C,B>0$，使得

$$
\left|
\mathcal T(s)-\mathcal T_A(s)-\frac{K(s)}{b_A}
\right|
\le \frac{C}{b_A^2}
\qquad
(|s-s_{\rm c}|\le d,\ b_A\ge B),
\tag{RC.155}
$$

其中接触后的 $K$ 使用本节所列、由既有静态对偶与一般谱承载机制供应的表达式。由 RC63 的对偶与乘子拼接，

$$
\boxed{
\lim_{s\uparrow s_{\rm c}}K(s)
=
K(s_{\rm c})
=
\lim_{s\downarrow s_{\rm c}}K(s).
}
\tag{RC.156}
$$

对任意 $s_A\to s_{\rm c}$，都有

$$
\boxed{
b_A\bigl[\mathcal T(s_A)-\mathcal T_A(s_A)\bigr]
\longrightarrow K(s_{\rm c}).
}
\tag{RC.157}
$$

平台端点也有

$$
\lim_{s\downarrow s_{\rm p}}K(s)=K_{\rm flat}.
$$

证明。把接触后第四条方向及其非负静态权重完全固定，减去它的 Gram 和 contrast 后，另外三条正权重射线的六维导数连续趋向引理 81.1 的接触导数。取足够小的闭接触邻域，导数逆范数、二阶导数和三个主权重的正下界统一受控。新增两个谱承载标签后只改变这六个参数，精确补回剩余 Gram 和 contrast；不需要改变第四条方向或除以它趋零的权重。固定第四条在原静态对偶下 slack 为零，另三条的总 slack 仍是 $O(\eta_A^2)$。这给出接触两侧共同的上界。

下界重复 §82.3 的四谱点二次 coercivity，所用物理谱、容量和零集都不随静态分支改变；RC 对偶与乘子在接触连续，故所有 Lipschitz 界在该闭邻域统一有限。有限个取向选择给出同一个预算阈值和二阶常数。于是 (RC.155) 在两侧同时成立。RC63 的两个接触对偶只差 $Q$ 倍数，$\operatorname{tr}Q=0$ 且所有 $h$ 都 $Q$-null，故系数值在接触完全相等。有限个连续取向分支的最小值连续，得到 (RC.156)。

若 $s_A\to s_{\rm c}$、$A\to\infty$，最终 $s_A$ 在上述邻域，(RC.155) 乘 $b_A$ 后误差至多 $C/b_A\to0$；再用 $K(s_A)\to K(s_{\rm c})$ 得 (RC.157)。平台处则由 $\lambda(r_\star)=0$ 和 (RC.135) 连续性得到平台常数的右极限。整个证明不要求 $\tau'(a_{\rm c})\ne0$，也不把固定强度极限与 $s\uparrow s_0$ 的端点极限互换。所需非退化性是实际三射线联合矩映射的非退化性。$\square$

## 85. 并列、零高度、零权重与端点边界

式 (RC.135) 在以下情形不需要额外选支假设。

**约定 85.1（取向并列）。**  当 $b_\epsilon(r_0)=0$，两方向都达到相同首阶成本，任意比例分配均可。系数连续。如果该零点有限阶为 $m$，相应项含有

$$
-\nu_\epsilon |b_{\epsilon,m}|\,|r-r_0|^m
$$

的局部绝对值项；简单零点可能导致导数折角，不能因此声称 $K$  全域 $C^1$。若判别函数在一段恒零，则该段保留全部分配比例。

**约定 85.2（live 高度为零）。**  若某谱承载方向满足 $\ell(h_{\epsilon,o})=0$，混合标签仍有非零主高度差 $\lambda_\epsilon$。式 (RC.139)–(RC.143) 仍成立。

**约定 85.3（静态零权重）。**  接触处的第四条静态射线不生成；它没有进入任何分母。接触后固定其小权重而修复另外三条，给出 (RC.155)。

**约定 85.4（轴方向竞争者）。**  下界中的完整椭圆包含所有轴方向。容量及谱 slack 估计没有删去它们。当前源的两个谱承载方向本身不在轴上，因为 $z_f\ne0$。

**命题 85.5（严格正系数）。**  FA74.27 给出负谱相容的两种 live 取向都有正高度。因此

$$
K(s)\ge
\nu_-\min_{o=\pm1}\ell(h_{-,o})>0.
\tag{RC.158}
$$

**约定 85.6（预算零与弱端点）。**  $A=0$  的原类为空，且 $s=s_0$  在有限预算下不可行，沿用 FA 的结论。本节公式范围为 $s\le s_{\rm c}<s_0$。中间区间的 $b_\pm$ 零集尚未逐根隔离；(RC.137) 的首阶取向分类不扩大为全部有限预算优化仪器分类。有序转移清单仍未给出，(RC.135) 的逐点值没有剩余自由优化。

## 86. 一个共同的完整原五模仪器

FA70、FA87 及本卷 §75 的全 fibre 构造应用到 §82–84 的同一矩族，给出以下完整实现。接触前和接触处统一由三个修复后的 pure-live 标签和两个谱承载标签组成；接触后邻域保留固定的第四个 pure-live 标签。若出现方向重合，仍分别实际生成；不能只凭 effect 相同或隐藏 Kraus 分解合并成可读标签。

### 86.1 每个 low label 的整个二维 fibre

对上述实际 $K_j,N_j$，取

$$
J_j:\mathbb C^2\to\operatorname{ran}K_j^\dagger
$$

为该实际标签固定的 isometry，并置

$$
Q_j=J_j^\dagger(K_j^\dagger K_j+N_j)J_j,
$$

$$
C_j=Q_j^{1/2}J_j^\dagger E^\dagger:\mathbb C^5\to\mathbb C^2,\qquad
B_j=K_jJ_jQ_j^{-1/2},
$$

$$
F_j=Q_j^{-1/2}J_j^\dagger N_jJ_jQ_j^{-1/2}.
$$

$K_j=\sqrt{p_j}K_{h_j}$ 的秩是二，因其下方 $2\times2$ minor 非零且 null 行列式为零；其核由 $(s_0,-bz_j/h_1,-dw_j/h_2)^T$ 张成，$n_{h_j}$ 与此核正交。因此 $N_j$ 支撑在 $\operatorname{ran}K_j^\dagger$，$Q_j\succ0$，所有逆都在整个实际二维 fibre 上定义。于是

$$
B_jC_j=K_jE^\dagger,\qquad C_j^\dagger F_jC_j=EN_jE^\dagger,
$$

$$
B_j^\dagger B_j+F_j=I_2,\qquad
L_j^{\rm dec}:=B_j^\dagger B_j\succ0.
\tag{RC.159}
$$

 $L_j^{\rm dec}$  是终端 live CP map 的 effect，与归一化矩阵 $L$  不同。选定

$$
g(u)=\frac2{(1+u)^2},\qquad G_{\rm time}(u)=\frac{2u}{1+u},
$$

$$
S_j(u)=\sqrt{I-G_{\rm time}(u)F_j},
$$

$$
R_j(u)=g(u)F_j[I-G_{\rm time}(u)F_j]^{-1}.
\tag{RC.160}
$$

对当前 survivor 矩阵 $Y$，第 $\ell$ 个跳跃 CP 密度为

$$
Y\longmapsto w_\ell g(u)\operatorname{tr}
[F_jS_j(u)^{-1}YS_j(u)^{-1}]P_f.
$$

not-yet-failed propagator 从 $u$ 到 $v$ 为 $\operatorname{Ad}_{S_j(v)S_j(u)^{-1}}$，故初始 fibre 输入的每个原失败分量恰为

$$
Y\longmapsto w_\ell g(u)\operatorname{tr}(F_jY)P_f.
$$

终端只对幸存者施加到五模 live 空间的 isometry

$$
EB_j(I-F_j)^{-1/2}.
$$

源容量的广义 Rayleigh 恒等式是

$$
\frac{\lambda_{\max}(F_j)}{1-\lambda_{\max}(F_j)}
=\frac{b_j}{\operatorname{cap}(h_j)}.
$$

因此 $S_j(u)$ 直到 $u=1$ 都可逆，且沿固定谱基积分得到

$$
\int_0^1\|R_j(u)\|_{\rm op}\,du
=-\log(1-\lambda_{\max}(F_j))
=\log(1+b_j/\operatorname{cap}(h_j))\le A.
$$

这给出实际 FIRST 事件时间 $6+u$。饱和标签取 $b_j=b_A\operatorname{cap}(h_j)$，活动量恰为 $A$；pure-live 标签 $b_j=0$，活动量为零。这些都是整个实际 fibre 上的读数，不是仅在输入态支撑上的读数。没有终端失败原子、强制截止吸收或失败后的正载体动作。任意 prescribed-path 定理的使用仍须保留其独立假设

$$
\mathcal L_{\rm dec}^{\dagger}(I)
=I-\int_0^1B(u)\,du\succ0.
$$

这里 $B(u)$ 指一般 prescribed-path 的拉回失败 effect 密度，区别于 live 矩阵 $B_j$；一般非交换路径仍须满足 FA68–70 的整条路径条件和指定终端 CP map，不能仅由 endpoint live-effect coercivity 推出。本构造选择 (RC.160)；必要性没有把竞争者的时间法则固定成 $g$。

### 86.2 同一个计入成本的 high 和 complement 完成

固定明确类型的 isometries

$$
W_\perp:\mathbb C^2\to\operatorname{ran}(E)^\perp,\qquad
J_0:\mathbb C^2\to\mathbb C^3.
$$

使用一个 high encoder

$$
C_H=
\begin{pmatrix}
\sqrt{1-\delta}\,DE^\dagger\\
W_\perp^\dagger
\end{pmatrix}
:\mathbb C^5\to\mathbb C^3\oplus\mathbb C^2.
\tag{RC.161}
$$

整个五维 fibre 都计为 high acquisition，活动量为零。终端 TP map 的两个 Kraus 矩阵是

$$
E[I_3\ 0],\qquad EJ_0[0\ I_2].
$$

将上述两个矩阵分别记为 $R_{H,0},R_{H,1}$。它们的 $R_{H,0}^\dagger R_{H,0}+R_{H,1}^\dagger R_{H,1}=I_5$，故定义全 $M_5$ 上的同一个 TP decoder。其 Kraus 索引不成为可读控制。补空间 qubit 内部相干保留，块间交叉项在终端处理时消去。high report 固定为 $+1$，因为其 supported effect 的 $01$  元为零。该完成属于允许的原 JR 类，在补空间上明确区别于固定 CA10。

### 86.3 全复矩阵、参考与五个 Borel 分量

对每个 $X\in M_5$，忘记 acquisition labels 后，

$$
\Phi^L(X)
=
E\left[
\Lambda_*(E^\dagger XE)
+J_0W_\perp^\dagger XW_\perp J_0^\dagger
\right]E^\dagger,
\tag{RC.162}
$$

$$
\Phi_\ell^f(X)(B)
=
w_\ell\left(\int_Bg(u)\,du\right)
\operatorname{tr}(EME^\dagger X)P_f,
$$

$$
\ell\in\{0,1,2,3,13\},\qquad
w=(0,\tfrac14,\tfrac12,\tfrac14,0).
\tag{RC.163}
$$

对任意 passive reference，失败分量为

$$
w_\ell\left(\int_Bg(u)\,du\right)
P_f\otimes
\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X].
\tag{RC.164}
$$

live 部分逐个 Kraus 张量 $I_R$。所以这里保留的是条件 reference partial trace。标签 $0,13$  的 CP measures 分别为零，其余三个标签保持分开。在 supported 代数上，修复后的 $\sum p_jh_jh_j^T=I_3$ 给出低 live coefficient Gram $\operatorname{diag}(\delta,1,1)$；加 high 的 $\operatorname{diag}(1-\delta,0,0)$ 后得到 $\Lambda_*=\operatorname{Ad}_D+\operatorname{Ad}_T+\operatorname{Ad}_S$。总 encoder effect 明确为

$$
E\!\left[\sum_j(K_j^\dagger K_j+N_j)+(1-\delta)D^\dagger D\right]E^\dagger
+W_\perp W_\perp^\dagger=I_5.
$$

所以每个 acquisition 分支 CP/TNI，各完整 decoder 均 TP，所有声明的 Borel 分量同时成立。对十二个原输入，输出正是给定原模拟器，故

$$
e_5=e_{27}=E_*,
\qquad
e_{16}<71/484<37/250<E_*.
\tag{RC.165}
$$

令 $\mathsf B_y=|b_y\rangle\langle b_y|$ 为 CG15 的原 ideal live operator，$T_y=\Lambda_*(a_ya_y^T)$，$q_y=\operatorname{tr}(Ma_ya_y^T)$。原 ideal failure density 仍为 $f_y(u)=6y/(y+6u)^2$，区别于所选 approximate density $g(u)$；无接受概率除法。对应 HALF 误差的完整形式是

$$
e_y=\tfrac12\left[\|T_y-\mathsf B_y\|_1+
\int_0^1|q_yg(u)-f_y(u)|\,du\right].
$$

四种 $e,n$ 由同一符号协变输出给出相同的 $e_y$；上述 strict middle bound 只属于这个共同达到族，不扩展为每个 optimizer 的相同中间误差。

给每个 supported 低标签报告 $\operatorname{sgn}z_j$；若 $z_j=0$ 则任选固定报告。附着失败 effect 杀死坐标零，不改变 $01$ 项。实际报告满足

$$
\mathsf V=s_0\sum_jp_j|z_j|\ge s,
$$

其中 $A_y=\langle a_y,D^\dagger Da_y\rangle=h_0^2y/128+h_1^2(64-y)/128+h_2^2/2$，是源的 $D$ effect 读数。唯一维数至少三的获取 fibre 是上面的五维 high，它对任意五模输入的 effect 为

$$
(1-\delta)ED^\dagger DE^\dagger+(I_5-EE^\dagger).
$$

补空间输入的全部概率也计为 high。对十二个原 supported 历史，补空间项为零，high acquisition 在每个原历史上的概率是

$$
(1-\delta)A_y,
$$

其最坏历史仍为 $27$，在整个弱区间给出同一 sharp cost $\mathsf C(s)=(1-\delta)A_{27}$。这同一族同时承担 Gram 修复、谱失败、对比度、完整输出、参考和时钟要求。没有使用第二份 specimen、历史先验、postselection、重试或未计入的可访问 quantum share。

### 86.4 计数与辅助字典

接触前和接触处，上述选择给出 五个 supported low live-bearing labels 加一个 high label 的构造上界。它不是有限 $A$  精确优化者的最小字母表定理。接触后邻域还保留 RC 的第四条 pure-live 标签，简单构造为六 low 加一 high。取向并列可以选一个取向保持上述上界；若采用任意比例拆分，则实际生成的 low 标签数可增加。为完整对应 FA74.3，若引用其辅助量，令

$$
r_\epsilon^{\rm aux}=-z_\epsilon/w_\epsilon,\qquad
\bar{\mathbf c}_\epsilon=
(\sqrt{\theta(r_\epsilon^{\rm aux})^2+\omega},
-r_\epsilon^{\rm aux},1)^T,
$$

$$
a_0=
\left(4\sum_\epsilon
\bar{\mathbf c}_\epsilon^TL_0^{-1}\bar{\mathbf c}_\epsilon\right)^{-1}.
$$

FA 的辅助族由两条 $\sqrt{a_0}\bar{\mathbf c}_\epsilon$ 和剩余 Gram 的至多三个 support-restricted null atoms 构成，且

$$
\nu_\star^{\rm FA}
=
\max_\epsilon
\frac{m_1h_2^2(e_\epsilon)_1^2}
{a_0d^2\operatorname{cap}(\bar{\mathbf c}_\epsilon)}.
\tag{RC.166}
$$

这里 $\operatorname{cap}(\bar{\mathbf c})$ 按原非归一化 coefficient 向量的 FA69 齐次容量解释。两条辅助向量满足 $L_0-a_0\sum_\epsilon\bar{\mathbf c}_\epsilon\bar{\mathbf c}_\epsilon^T\succeq3L_0/4$，再用支撑限制的 null 分解，故只需至多三个剩余 atoms。$\nu_\star^{\rm FA}$ 是该固定辅助族的预算常量，区别于 $\nu_\epsilon$，也区别于 FA 的最小预算端点质量和容量常量。这是供应字典；§82 的达到族具体使用 (RC.142) 的谱载荷及同一个三射线修复。
## 87. 结果的来源、数值范围与原问题边界

**约定 87.1（复用与源特定推导的范围）。** CG13–17 供应孤立源、完整输出 minimax 及其有限范围的平均/预平均等号事实；JR34–45 另行供应 sharp 联合获取成本和未平均实面，JR50–54 供应平台、严格递减、报告和高度符号约化。RC58–66 的静态最优值、三到四射线接触、选定代数根及全局对偶保持其原条件。FA67–72、FA74、FA80、FA87 的整个 fibre 活动、双重秩、容量、端点分裂、物理谱承载、系数存在性和全输出构造均按原范围复用。§75 和 §86 是这些构造在各自同一矩族上的应用，不能将改写视为另一项独立定理。

本节的源特定推导是 (RC.115)–(RC.122) 的具体 frame 和强度逆式、实际六维 Gram/contrast 映射在接触仍非退化、(RC.135) 的逐点系数和两个严格端点取向、平台值 (RC.145)、接触值 (RC.152)，以及固定第四条原子后由三个正主射线得到的一致两侧拼接。一般谱 slack、局部 rank 条件修复及接触后系数表达式是继承机制；这里将其适用条件在实际接触上验证并接入同一族，不重复计作一般方法的新发现。这些是仓内条件性综合和具体源评价，不含经文献穷尽认证的原创性或优先权结论。

对既有第四 slack 完成，所用外部结果限于 Xia–Wang–Sheu，*S-Lemma with Equality and Its Applications*，arXiv:1403.2816v3 的 Assumption 1（PDF/印刷页 3）与 Theorem 3（PDF/印刷页 11）[SLEM]。此处等式二次矩阵 $Q=\operatorname{diag}(1,-\alpha,-\beta)$ 非零且不定，线性项 $b=0$；约束取两种符号，而该定理列出的异常要求零二次约束矩阵和非零线性项，故不落入异常。它只供应继承的第四二次 slack 完成，不供应源特定系数、六维矩可逆性、contact sensitivity、有限预算最优标签数或物理实现。

**约定 87.2（源条件下的保守数值范围）。** 在约定 78.1 的源盒与选根前提下，显式公式有以下有理外包络；小数端点均按其有限十进有理数解释。

| 量和所用选根条件 | 下端点 | 上端点 |
| --- | --- | --- |
| $r_\star$ | $.8687895589321182$ | $.8687895589321187$ |
| $K_{\rm flat}$ | $.4187926661607985$ | $.4187926661607991$ |
| $K(s_{\rm c})$，(RC.135) 与继承的窄 $r_{\rm c}$ 区间 | $.4959141069433$ | $.4959141734456$ |
| $K(s_{\rm c})$，(RC.152) 与粗 $(a,\varkappa)$ 接触盒 | $.4956981979152$ | $.4961304063752$ |

第三项的窄接触输入正是 (RC.121)，不是从 (RC.149) 粗盒新推出的根认证。两个系数表达式的精确相等由接触对偶模 $Q$ 的解析恒等式承担；外包络重叠只给出相容性，不能代替该恒等式或根选择。数值范围不解除源、minimax、sharp-cost、静态全局最优性或 RC 选根前提。

**定义 87.3（尚缺的原完整前沿和转移分类）。** 完整有限 $(s,A)$ 弱高度前沿仍须在整个原可行内点上联合评价**定向 failure allocation 和所有 live-height decompositions**，包含低于固定 allocation 最大对比度的分解。只评价最大对比度 face、固定 even family、静态接触支撑、隐式 SDP、有限 KKT 系统或裸算法均不满足这一目标。全局有限预算 contact、rank、optimizer 变化、共同正权重参数 atlas，以及精确有限 $A$ 优化者的最小实际获取字母表仍未由 (RC.135)–(RC.157) 决定。

逐点取向表 (RC.137) 已处理所有两取向并列，但中间 $b_+$、$b_-$ 的零点隔离、顺序、重数、符号区间及与已知重合集的全部交叉尚未枚举。连续的绝对值公式不自动给出全域 $C^1$，更不分类所有有限预算最优仪器。五 low 加一 high 和接触后简单六 low 加一 high 只是本节首阶达到族的构造上界；它们不证明精确最小值，不替代弱 $3/4/5$ 可行性计数，也不转移到强固定源计数。强固定源计数在其原范围内仍是 $r=1,2$ 时四、其他可行 $r$ 时五，无可达六标签强区域。TA 的静态全字母表、隐藏 Kraus 数、极限失败射线数、live 投影线数与共同量子维数各是不同的量。

JS11–17 已供应 limiting selector、严格单调 inverse、物理两/三失败射线判据、every-instrument critical strip、sub-spectral uniform layer、Gram 稳定、零角点处理及 compact-uniform spectral layer；这些保持其已供应范围。剩余的 transition-root inventory 包括 JS12 的有限非空零集

$$
E_{\rm edge}(p)=g_+(p)C'(p)-g_+'(p)D_J(p,1-p)=0,
\qquad p\in(p_z,p_s),
$$

其中符号按 JS.58 的原字典。该零集尚未全部隔离和排序；不能从每个预算具有唯一 selected optimizer 推出仅有一个简单转移。其他统一端点区间、下一项、临界五标签与静态接触的精确联合插值及相应尺度仍须分别解决。推论 84.2 的任意 $s_A\to s_{\rm c}$ 首阶极限不提供这些下一项，也不允许与 $s\uparrow s_0$ 的非一致端点极限互换。

**约定 87.4（原生和形式证据边界）。** 对唯一未知 specimen 的合法获取、原历史和目标的校准、全部未来可访问份额的共同 coherent storage/计数/持续时间、decoder actuation、统一物理时钟、实际 FIRST 服务，以及 archive/source/epoch/controller/permissions 的共同实现桥均未由这些矩阵和 CP 测度构造验证。OriginalControl 继续是几何供应，不是执行器。有限的条件性数学增补不完成或收缩完整 quantum-first programme，不推出宇宙本体、native service、Lean/kernel 认证或 source-final 批准。

[CG78]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR78]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md

## 追加锚（本行以下为增补区）

## 88. 同源连续取向问题与精确输入区间

**约定 88.1（条件、分支和原问题）。** §88–94 使用 §78.1 的原始类及 §79 的同一物理源。源根是 (RC.4) 的九坐标局部孤立根，源振幅由 (RC.5) 的正 pivot 公式取得；秩、根处 TP 恒等式、CG13–17 的 HALF 完整输出 minimax 及其平均／预平均等号事实保持原范围。JR34–45 另行供应 sharp 最坏历史联合获取成本和未平均实等号面；JR50–54 供应平台、严格递减及报告／高度符号约化。§60–63 的静态全局最优性、实际接触选根和连续对偶分支，以及 §81–86 的六维矩修复、容量、共同达到族和一致余项，都是以下系数结论的明确前提。

具体地，令 $r_\star$ 是 (RC.119) 所选的真正平台极小点，$17/20<r_\star<9/10$；令 $r_{\rm c}=(Z_{\rm c})_2/(Z_{\rm c})_1$，其中 $Z_{\rm c}$ 由 (RC.148)–(RC.150) 的同一个选定 $\mathcal P=\Omega=0$ 根给出，并保留 (RC.121) 的窄区间，特别是 $r_{\rm c}<21/20$。记

$$
I=[r_\star,r_{\rm c}]\subset[17/20,21/20].
$$

以下不重新隔离这两个根。九坐标源根、局部根唯一性、静态全局最优性及 RC 接触根是不同的前提：源区间本身不推出静态最优性，接触点的切触方程本身也不推出全椭圆对偶不等式。

原竞争者保留 sole unknown specimen、全部十二历史、一个共同全复多 Kraus 仪器、$\mathsf V\ge s$ 不等式及 sharp 联合获取成本。有限、可数和约定的可测有限 fibre、可积 Kraus 扩展仍仅在 §78.1 的范围内。整个实际 decoder fibre 的活动量、五个分别标记的 Borel 失败 CP 分量（包括分别为零的 $0,13$）、被动参考的条件部分迹、正 survivors、TP 未失败控制和绝对时间 $6+u$ 的 FIRST 均保留。没有强制终端吸收或失败后的正载体动作。

**定义 88.2（源字典与整数区间证书）。** 写 $\mathsf x=G_{01}$、$\mathsf y=G_{02}$、$\mathsf z=G_{12}$，与 (RC.107) 一致；$a_{\rm src},b_{\rm src},c_{\rm src},d_{\rm src}$ 是 (RC.5) 的振幅，分别是 §79 的 $a,b,c,d$。其中 $d_{\rm src}$ 不同于静态归一化量 $d_r$。完整对应为

$$
\begin{gathered}
\theta=\frac{a_{\rm src}b_{\rm src}}{h_0h_1},\quad
\omega=\frac{c_{\rm src}d_{\rm src}}{h_0h_2},\quad
\delta=\theta+\omega,\quad s_0=\sqrt\delta,\quad
\alpha=\theta/\delta=1-\beta,\quad\beta=\omega/\delta,\\
(K_0,K_1,K_2)=(D,T,S),\quad
\Delta=\rho_{27,+,+}-\rho_{5,+,+},\quad
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\\
G=\operatorname{diag}(s_0,1,1)N\operatorname{diag}(s_0,1,1),\quad
\Delta A=N_{00},\quad M=\operatorname{diag}(m_0,m_1,m_2),\quad m_0=0.
\end{gathered}
\tag{RC.167}
$$

源证书给出的下列区间均为 $[L/D_{\rm cert},U/D_{\rm cert}]$，共同分母是

$$
D_{\rm cert}=2^{224}
=26959946667150639794667015087019630673637144422540572481103610249216.
$$

这些是同一九坐标源的外包络输入，不把各参数视为独立中心值，也不把盒内点视为处处 TP。

| 量 | $L$ | $U$ |
| --- | --- | --- |
| $\beta$ | $3296842078597743037413473231959988404966987722955647639968047305372$ | $3296842078597743037414228158069975732764908643825242059562820404625$ |
| $g_0$ | $34221372174431290786718999261791211913632513952393836659553436688$ | $34221372174431290786780685200389826628501112496695844777618146828$ |
| $g_1$ | $78783570610947918076504457783823376875791541957489725211853654103$ | $78783570610947918076528781413699780090811566031886072291211212877$ |
| $g_2$ | $45217132639885265280065628896983675495273546961325526453963593339$ | $45217132639885265280113507252983523546922593561790580491093661556$ |
| $\mathsf x$ | $63910117293406567136997332254455271417331233917251423202613394599$ | $63910117293406567137040175213816913730280255820235874754516426984$ |
| $\mathsf y$ | $59527865208926896968702198521424412882206778336312391207706909528$ | $59527865208926896968773639959878055405231936608490807444733614519$ |
| $\mathsf z$ | $-2740627279025051691705416351839235775900350270525561152827355761$ | $-2740627279025051691701021642264762102188060554422868821033090259$ |
| $a_{\rm src}$ | $1770311394972945197641994965733434776804318798358636960993665423441$ | $1770311394972945197642330191383860313598676849494811590399527112584$ |
| $b_{\rm src}$ | $3935965654294995608601979521892857651473674590095072143984588712921$ | $3935965654294995608602313422828891500221393677289956783118602628225$ |
| $c_{\rm src}$ | $417790356983612701857377130657326048451791786364520663159403140999$ | $417790356983612701857967962172137068830255220590298423542851403047$ |
| $d_{\rm src}$ | $2663205433690388662341049091689729175826547547021472884789707223172$ | $2663205433690388662342459064972096088182130849082266016544667607076$ |
| $h_0$ | $26537788820506109500788498850443291999899441414357450708533697655768$ | $26537788820506109500793183315073538792668688684001205079732940054331$ |
| $h_1$ | $19041394653590742992836842417055357808127410672381937576282066738318$ | $19041394653590742992839410055472468226237891451663919566364482743060$ |
| $h_2$ | $21824004785988993361054584934895991870094398276315525145506200547608$ | $21824004785988993361057348440025413753058042469208985303844669006803$ |
| $m_0$ | $0$ | $0$ |
| $m_1$ | $13395056598782546673904842458375183527737029361412185934273944851861$ | $13395056598782546673906662453967195540019733666091401589339664139139$ |
| $m_2$ | $9286998735773460367948153511490550124076700197961256553923028397389$ | $9286998735773460367951141007906400979909044212876537994791222399466$ |
| $\theta$ | $371754732146348110957677599704942803872157131983090154113316006024$ | $371754732146348110957895283892442664871296384732895240664094147987$ |
| $\omega$ | $51794414349620443188334230846373069826950088927783643990123454218$ | $51794414349620443188450600275043575937037912978110040885162911192$ |
| $\delta$ | $423549146495968554146011830551315873699107220910873798103439460242$ | $423549146495968554146345884167486240808334297711005281549257059179$ |
| $s_0$ | $3379180729178077789001472963110194729984725431101496002002178454791$ | $3379180729178077789002805544643664895183520534907765266655915068614$ |
| $\Delta A$ | $2178274649664917026219840788436610404284546028134588617028215950658$ | $2178274649664917026222049243107662090560048935982720049984373276804$ |

由整数大小比较立即得到以下严格外界；所有有限小数均表示精确有理数：

$$
\begin{gathered}
3/25<\beta<1/8,\qquad7/8<\alpha<22/25,\qquad\alpha+\beta=1,\\
.00126<g_0<.00128,\quad .0029<g_1<.003,\quad .0016<g_2<.0017,\\
.0023<\mathsf x<.00238,\quad .0022<\mathsf y<.00221,\quad -.000103<\mathsf z<0,\\
.145<b_{\rm src}<.147,\quad .098<d_{\rm src}<.100,\\
.706<h_1<.707,\quad .809<h_2<.810,\quad
.496<m_1<.497,\quad .344<m_2<.345.
\end{gathered}
\tag{RC.168}
$$

例如 $25L_\beta>3D_{\rm cert}$、$8U_\beta<D_{\rm cert}$ 给出 $\beta$ 的两个界；其余行同样直接交叉相乘。$\alpha$ 始终用 $1-\beta$，并非另取一个无关区间。源根的坐标、正 pivot 和 TP 身份仍是 (RC.4)–(RC.5) 及 §78.1 的供应。

## 89. 物理谱方向及整个闭区间的正分母

**引理 89.1（同源物理方向的有理界）。** 对 (RC.110)–(RC.112) 的物理谱承载方向，定义

$$
R_f=\sqrt{W_f/V_f}
=\frac{b_{\rm src}h_2}{d_{\rm src}h_1}\sqrt{m_1/m_2},\quad
c_+=R_ft_f=\frac{w_+}{z_+},\quad
q_f=t_f/R_f=-\frac{z_-}{w_-}.
\tag{RC.169}
$$

则

$$
1.98<R_f<2.08,\quad .39<t_f<.42,\quad
0<c_+<.8736<1,\quad 3/16<q_f<7/33,
\tag{RC.170}
$$

特别是 $.18<q_f<.22$。两个 $z_\epsilon$、容量和 $\nu_\epsilon$ 都严格正，两个物理谱值非零、异号且不同。

证明。保留实际物理白化，而非以未白化特征向量代替 effect：

$$
\begin{gathered}
\Xi=\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},\quad
 d_f=11m_1/64,\quad
 z_f=\sqrt{m_1m_2}(\sqrt{37}-\sqrt{59})/16<0,\\
L_f=\sqrt{d_f^2+4z_f^2},\quad
 t_f=\frac{-2z_f}{d_f+L_f},\quad
 e_-=(1,t_f)^T/\sqrt{1+t_f^2},\quad
 e_+=(t_f,-1)^T/\sqrt{1+t_f^2},\\
B_\epsilon^{\rm sp}=M_2^{1/2}e_\epsilon e_\epsilon^TM_2^{1/2},\quad
M_2=\operatorname{diag}(m_1,m_2).
\end{gathered}
\tag{RC.171}
$$

将 (RC.168) 代入 $R_f^2$，上下界分别由

$$
\left(\frac{145\cdot809}{100\cdot707}\right)^2\frac{496}{345}
>\left(\frac{99}{50}\right)^2,\qquad
\left(\frac{147\cdot810}{98\cdot706}\right)^2\frac{497}{344}
<\left(\frac{52}{25}\right)^2
$$

这两个纯有理比较给出。平方比较还给出 $6.08<\sqrt{37}<6.09$、$7.68<\sqrt{59}<7.69$，故 $1.59<\sqrt{59}-\sqrt{37}<1.61$。因此

$$
a_f:=|z_f|/d_f=\frac4{11}\sqrt{m_2/m_1}(\sqrt{59}-\sqrt{37})
\quad\hbox{满足}\quad .47<a_f<.50.
$$

这里 $a_f$ 仅是本节的谱比率。$t_f\in(0,1)$ 满足 $a_f=t_f/(1-t_f^2)$，右侧严格递增；而

$$
\frac{.39}{1-.39^2}<.47,\qquad
\frac{.42}{1-.42^2}>.50.
$$

这给出 $t_f$ 的界。相乘、相除得 $c_+<2.08(.42)=.8736$ 及
$q_f>.39/2.08=3/16$、$q_f<.42/1.98=7/33$；端点比例等式不会消除输入不等式的严格性。

显式地，原正 $z$ 取向正是

$$
\begin{gathered}
z_+=(\alpha+\beta c_+^2)^{-1/2},\quad w_+=c_+z_+,\\
z_-=(\alpha+\beta/q_f^2)^{-1/2},\quad w_-=-z_-/q_f,\quad
h_{\epsilon,o}=(1,oz_\epsilon,ow_\epsilon)^T,\\
\chi_\epsilon=\alpha V_f(e_\epsilon)_2^2+\beta W_f(e_\epsilon)_1^2,\quad
\nu_\epsilon=\chi_\epsilon/\operatorname{cap}(h_{\epsilon,+}).
\end{gathered}
\tag{RC.172}
$$

容量仍是同一个严格正函数

$$
\operatorname{cap}(1,z,w)=
\frac{h_1^2h_2^2s_0^2+a_{\rm src}^2h_2^2z^2+c_{\rm src}^2h_1^2w^2}
{h_0^2s_0^2+b_{\rm src}^2z^2+d_{\rm src}^2w^2}.
\tag{RC.173}
$$

源振幅、$s_0,m_1,m_2$ 正，故所有谱归一化、$\chi_\epsilon$、容量和 $\nu_\epsilon$ 都正。$\det\Xi=-z_f^2<0$ 给出两个非零异号谱值；$L_f>0$ 给出其分离。两谱方向均不在轴上。$\square$

**引理 89.2（未平方分支和统一几何界）。** 为简化记号，以下写 $k=k_r$、$R=R_r$、$d=d_r$，并令

$$
\begin{gathered}
k=\sqrt{\alpha+\beta r^2},\quad d=1+\alpha+(1+\beta)r^2,\quad
R=\sqrt{\beta^2(1+\alpha)+\alpha^2(1+\beta)r^2},\\
u=-v_1/u_1=
\frac{R-\alpha kr}{\beta k+rR}
=\frac{1-\alpha k^2}{r+kR},\quad
l=\sqrt{\alpha+\beta u^2},\quad e=1+\alpha+(1+\beta)u^2,\\
J=\alpha r+\beta u,\qquad
\Theta=2\alpha-\beta^2+\beta(1+\beta)u^2.
\end{gathered}
\tag{RC.174}
$$

在整个 $I$ 上，

$$
\begin{gathered}
kl+ru=1,\quad 1/20<u<1/10,\quad .98<k<1.007,\quad .93<l<.94<k,\\
2.68<d<13/4,\quad e>0,\quad119/160<J<1,\quad
17/10<\Theta<177/100,\quad9/10<kl<1.
\end{gathered}
\tag{RC.175}
$$

证明。两个 $u$ 根式的相等由有理化直接得到。第二式分子 $1-\alpha k^2>0$，因为 $\alpha<.88$、$k^2\le1+(1/8)((21/20)^2-1)<1.013$；分母正。平方后的正交式是

$$
\begin{aligned}
\mathcal E_{\rm fr}
&=(\alpha+\beta r^2)(\alpha+\beta u^2)-(1-ru)^2\\
&=(\beta k^2-r^2)u^2+2ru+\alpha k^2-1=0.
\end{aligned}
\tag{RC.176}
$$

代入有理化式还给出

$$
1-ru=\frac{kR+\alpha r k^2}{r+kR}>0.
$$

因此取的确是未平方的正根 $kl+ru=1$，没有引入另一条平方分支。对固定 $r>0$，$u\mapsto k\sqrt{\alpha+\beta u^2}+ru$ 在 $u\ge0$ 严格递增。先由 $k^2=1+\beta(r^2-1)$ 得 $.98<k<1.007$。该函数在 $u=.05$ 的值小于
$1.007(.939)+1.05(.05)=.998073<1$；在 $u=.1$ 的值大于
$.98(.936)+.85(.1)=1.00228>1$。所用 $.939,.936$ 是直接平方比较的严格根式界。这证明 $1/20<u<1/10$。其余界由 (RC.168)、$r\in[.85,1.05]$ 逐项代入得到；例如 $J>(7/8)(17/20)=119/160$，$J<(.88)(1.05)+(.125)(.1)<1$，且 $kl=1-ru<1$、$kl>.98(.93)>.9$。

所有实际分母 $r+kR,\beta k+rR,k,l,d,e,J$ 均正。若把几何恒等式改写成多项式，(RC.176) 的 $u^2$ 首项系数为

$$
\beta k^2-r^2=\alpha[\beta-(1+\beta)r^2]<0
\tag{RC.177}
$$

于整个外盒成立，因为 $\beta<1/8$、$1+\beta>28/25$、$r^2\ge289/400$。所以以它作消元的首项因子不会丢掉实际分支；清除 $k$ 的正偶次幂也合法。恒等式的使用始终保留 $\alpha+\beta=1$、根式平方关系和 $1-ru>0$，不把任意平方根当成原分支。$\square$

## 90. 原静态对偶的通用非对角分解

**引理 90.1（frame、乘子与非零分母）。** (RC.115) 的同一 frame 可写成

$$
\begin{gathered}
f_0=(k,-1,-r)^T/\sqrt d,\qquad f_1=(l,1,-u)^T/\sqrt e,\\
f_2=f_0\mathbin\times f_1
=(u+r,ku-rl,k+l)^T/\sqrt{de},\qquad F=(f_0,f_1,f_2),\\
H=F^TGF,\qquad q=F^TQF,\qquad c=F^TCF,\qquad
\psi=H_{00}=P/d,\qquad h_{\rm fr}=2l/e.
\end{gathered}
\tag{RC.178}
$$

这里 $f_2$ 的 coordinate-zero 为正，与原 $f_2$ 选向相同。$F\in SO(3)$，$q_{ii}=0$，且

$$
\begin{gathered}
q_{01}=\frac{1+\alpha-(1+\beta)ru}{\sqrt{de}}>0,\quad
q_{12}=\frac{J}{l\sqrt d}>0,\quad
2q_{01}q_{02}q_{12}=\alpha\beta>0,\\
\xi:=c_{01}-q_{01}c_{12}/q_{12}
=-\frac{u\Theta l\sqrt d}{2e^{3/2}J}<0.
\end{gathered}
\tag{RC.179}
$$

因而 $q_{02}>0$，(RC.130) 的分母 $\xi/q_{01}\ne0$。原乘子为

$$
\lambda=\frac{H_{02}/q_{02}-H_{01}/q_{01}}
{c_{01}/q_{01}-c_{12}/q_{12}}
=2\psi'/h_{\rm fr}',\qquad
\lambda(r_\star)=0,\quad \lambda(r)>0\ (r>r_\star).
\tag{RC.180}
$$

证明。把 (RC.178) 代入，$kl+ru=1$ 给出正交、范数和两列 null；第三列 null 由 $\operatorname{tr}Q=0$ 得到。直接相乘给出 $q_{01},q_{12}$ 和

$$
c_{01}q_{12}-q_{01}c_{12}=-\frac{u\Theta}{2e^{3/2}}.
$$

$q_{01}$ 的分子大于 $1+7/8-(9/8)(21/200)>0$。$q$ 零对角的行列式是 $2q_{01}q_{02}q_{12}$，同时等于 $\det Q=\alpha\beta$，故三个除数非零且符号如上。

沿未平方正交式求导得

$$
u'=-\frac{\beta r l/k+u}{r+\beta uk/l}<0,\qquad
\left(\frac{2l}{e}\right)'_{u}=-\frac{2u\Theta}{le^2}<0.
\tag{RC.181}
$$

所以 $h_{\rm fr}'>0$，在两个闭端点也成立。再置 $p=r^2/d$，$p'=2r(1+\alpha)/d^2>0$，并写

$$
p_0=\frac{\alpha+(\beta-\alpha)p}{1+\alpha},\qquad
p_1=\frac{1-(1+\beta)p}{1+\alpha}.
$$

于是 $\psi$ 为线性项减去 $2\mathsf x\sqrt{p_0p_1}+2\mathsf y\sqrt{p_0p}+2|\mathsf z|\sqrt{p_1p}$。对正仿射 $v,w$，

$$
(\sqrt{vw})''=-\frac{(v'w-vw')^2}{4(vw)^{3/2}}.
$$

已有 $\mathsf x>0$ 且 $p_0'p_1-p_0p_1'=\beta/(1+\alpha)\ne0$，故 $\psi$ 对 $p$ 严格凸。所选 $r_\star$ 是其极小点，故 $\psi'(r_\star)=0$，右侧 $\psi'>0$。这与 $h_{\rm fr}'>0$ 一起证明 (RC.180) 的符号，而不预设探测器符号。$\square$

**引理 90.2（同一个对偶的精确矩阵恒等式）。** 令 $\mu=H_{02}/q_{02}$。则 (RC.131) 的对偶满足

$$
\begin{aligned}
\mathcal Y={}&G-\lambda C-2\mu Q-2\psi f_0f_0^T
+2\lambda c_{11}f_1f_1^T\\
&+2\lambda\xi(f_0f_1^T+f_1f_0^T),\qquad c_{11}=l/e.
\end{aligned}
\tag{RC.182}
$$

它的两个实际非对角元可写成

$$
\begin{aligned}
\mathcal Y_{01}-\mathsf x&=2\psi k/d+\lambda B_1,\\
\mathcal Y_{02}-\mathsf y&=2\psi kr/d+\lambda B_2,\\
B_1&=-\tfrac12+2l^2/e^2-\frac{u\Theta l(k-l)}{e^2J},\\
B_2&=\frac{u}{e^2}\left[\frac{\alpha\Theta klu}{J}
-\beta(\beta+\alpha u^2)\right].
\end{aligned}
\tag{RC.183}
$$

证明。在 $F$ 坐标中，(RC.180) 等价于

$$
\frac{H_{01}+\lambda c_{01}}{q_{01}}
=\mu+\lambda c_{12}/q_{12}.
$$

(RC.182) 右侧的三个对角元为
$-H_{00}-\lambda c_{00},H_{11}+\lambda c_{11},H_{22}-\lambda c_{22}$。
$01$ 元是 $H_{01}-\lambda c_{01}-2\mu q_{01}+2\lambda\xi
=-H_{01}-\lambda c_{01}$；$02$ 元是 $-H_{02}-\lambda c_{02}$；$12$ 元是 $H_{12}-\lambda c_{12}-2H_{02}q_{12}/q_{02}$。对称元相同，故全部九元与 (RC.131) 一致。此处 $-\lambda C$ 必须保留。

回到物理坐标，$Q$ 没有非对角元。$-2\psi f_0f_0^T$ 给出 $2\psi k/d,2\psi kr/d$；将 $c_{11}=l/e$ 和 (RC.179) 的 $\xi$ 代入其他项，$01$ 系数正是 $B_1$。$02$ 系数先为

$$
-2l^2u/e^2+\frac{u\Theta l(ku+rl)}{e^2J}.
$$

利用下列直接展开的恒等式即得 $B_2$：

$$
\begin{gathered}
l(ku+rl)=J+\alpha klu,\qquad
\Theta-2l^2=-\beta(\beta+\alpha u^2),\\
e^2-4l^2=\beta^2+2\alpha(2+\beta)u^2+(1+\beta)^2u^4.
\end{gathered}
\tag{RC.184}
$$

这些是自由参数满足 (RC.174)–(RC.176) 时的恒等式。它们不依赖源中心或有限采样；所有清分母因子均由 (RC.175)、(RC.177)、(RC.179) 排除为零。对偶加任意 $Q$ 倍数不会改变 (RC.183)。$\square$

## 91. 连续外盒上的两个严格符号界

**引理 91.1（纯几何系数的严格界）。** 在整个 $I$ 上，

$$
B_1<0<B_2,\qquad B_1+B_2<-\frac{19}{4000e^2}.
\tag{RC.185}
$$

证明。(RC.184) 给出 $e^2-4l^2>0$，而 $k>l,\Theta,J,u>0$，故 (RC.183) 的 $B_1<0$。$B_2$ 括号中的正项和减项分别满足

$$
\frac{\alpha\Theta klu}{J}
>\frac78\frac{17}{10}\frac9{10}\frac1{20}>\frac3{50},\qquad
\beta(\beta+\alpha u^2)
<\frac18\left(\frac18+\frac{22}{2500}\right)<\frac{17}{1000}.
$$

因此 $B_2>0$。同时

$$
e^2B_2<\frac{\alpha\Theta kl}{J}u^2
<\frac{(22/25)(177/100)}{119/160}u^2<\frac{21}{10}u^2.
$$

另一方面，(RC.184) 与 $B_1$ 的最后一个正损失项给出

$$
-e^2B_1>
\frac{\beta^2}{2}+\alpha(2+\beta)u^2
>\frac9{1250}+\frac{371}{200}u^2.
$$

相减得到

$$
-e^2(B_1+B_2)>
\frac9{1250}-\frac{49}{200}u^2
>\frac9{1250}-\frac{49}{20000}=\frac{19}{4000}.
$$

这证明整个连续区间的界。$\square$

**引理 91.2（同源 $\psi$ 的两侧统一界）。** 在整个 $I$ 上，

$$
-\frac{333}{100000}<\psi< -\frac{19}{32500}< -\frac1{2000}.
\tag{RC.186}
$$

证明。由 $2|v_iv_j|\le v_i^2+v_j^2$，任意实向量满足

$$
v^TGv\ge\sum_i\left(g_i-\sum_{j\ne i}|G_{ij}|\right)v_i^2.
$$

(RC.168) 给出的三个行系数分别严格大于
$(-.00333,.000417,-.000713)$；故 $G\succ-.00333I$。$f_0$ 为单位向量，得到下界。对上界，保持 (RC.118) 的完整源多项式

$$
P=g_0k^2+g_1+g_2r^2-2\mathsf x k-2\mathsf y kr+2\mathsf z r.
$$

利用 $\mathsf z<0$、$.98<k<1.01$ 和 $.85\le r\le1.05$ 得

$$
\begin{aligned}
P<&\ .00128(1.01)^2+.003+.0017(1.05)^2\\
&-2(.0023)(.98)-2(.0022)(.98)(.85)\\
=&-.001993222<-19/10000.
\end{aligned}
$$

由于 $0<d<13/4$，除以负数上界时保留正确方向：$\psi=P/d<-19/32500$。$\square$

**定理 91.3（原两个探测器在全闭区间严格为负）。** 对 (RC.134) 的原探测器，在每个 $r\in I$ 都有

$$
\boxed{\quad
\frac{b_+(r)}{z_+}< -\frac3{10000},\qquad
\frac{b_-(r)}{z_-}< -\frac3{1000}.
\quad}
\tag{RC.187}
$$

证明。仍用 $Z_\epsilon=\mathcal Y-\epsilon G$ 和
$b_\epsilon=(Z_\epsilon)_{01}z_\epsilon+(Z_\epsilon)_{02}w_\epsilon$，没有换成代理函数。由 (RC.169)、(RC.183)，

$$
\frac{b_+}{z_+}
=\frac{2\psi k}{d}(1+c_+r)+\lambda(B_1+c_+B_2).
$$

$0<c_+<1$、$B_2>0$、$B_1+B_2<0$ 给出 $B_1+c_+B_2<0$。再用 $\lambda\ge0$、$\psi<-1/2000$、$k>.98$、$d<13/4$，可得严格界

$$
\frac{b_+}{z_+}
<-\frac{1}{1000}\frac{.98}{13/4}
=-\frac{49}{162500}
=-\frac3{10000}-\frac1{650000}.
\tag{RC.188}
$$

负谱号的 $Z_-=\mathcal Y+G$，因此

$$
\frac{b_-}{2z_-}
=\mathsf x-\frac{\mathsf y}{q_f}
+\frac{\psi k}{d}\left(1-\frac r{q_f}\right)
+\frac\lambda2\left(B_1-\frac{B_2}{q_f}\right).
$$

最后一项非正，$r/q_f>1$，所以中间 $\psi$ 项为正且必须作上界。由 (RC.168)、(RC.170)、(RC.175)、(RC.186)，

$$
\mathsf x-\mathsf y/q_f<.00238-.0022/.22=-.00762,
\qquad r/q_f-1<1.05/.18-1=29/6.
$$

故

$$
\begin{aligned}
\frac{b_-}{z_-}
&<2\left[-.00762+\frac{.00333(1.01)}{2.68}\frac{29}{6}\right]\\
&=-\frac{83313}{26800000}
=-\frac3{1000}-\frac{2913}{26800000}.
\end{aligned}
\tag{RC.189}
$$

这覆盖 $r_\star$、$r_{\rm c}$ 和其间每个实参数；没有从两个端点符号推断内部符号。$\square$

## 92. 空的有序零清单与唯一首阶取向

**推论 92.1（两个有序清单及退化情形）。** 定义原闭区间中的有序零清单

$$
\mathcal Z_\epsilon=\{r\in[r_\star,r_{\rm c}]:b_\epsilon(r)=0\}
\quad\hbox{按 }r\hbox{ 递增排列}.
$$

则 $\mathcal Z_+=\mathcal Z_-=\varnothing$，合并有序清单也是空集。两个函数各只有一个符号分量，即整个 $I$，在其上严格为负。因此无端点根、共同根、切触根、偶重或其他多重根、恒零区间和取向并列，也没有待排列的零点重数。

证明。$z_+,z_->0$，直接应用 (RC.187)。$\lambda(r_\star)=0$ 时 (RC.188) 的严格 $\psi$ 界仍成立；$r_{\rm c}$ 处第四条静态射线的零权重未进入任何分母。若某个 live 高度 $\ell(h_{\epsilon,o})=0$，对应物理谱值仍非零，不改变探测器证明或 §82 的谱主符号。$b_+(r)=b_-(r)<0$ 只是两个不同函数的值相等，不是任何一个两点问题的并列；本结论不判定这种相等是否发生及其位置。$\square$

**推论 92.2（全部两点首阶最优选择）。** 在全部 $I$ 上，对每个谱号，(RC.137) 的最优取向都唯一为 $o=+1$，即 $z>0$。若把该谱 effect 的固定正比例 $t\in(0,1]$ 及匹配的 live mass 分给 $o=-1$，该谱号对 $K$ 的首阶贡献恰增加

$$
2t\nu_\epsilon|b_\epsilon(r)|>0.
\tag{RC.190}
$$

证明。由原定义，

$$
h_{\epsilon,o}^T(\mathcal Y-\epsilon G)h_{\epsilon,o}
-\lambda z_\epsilon=a_\epsilon+2ob_\epsilon.
$$

两个方向的成本差是 $-4b_\epsilon=4|b_\epsilon|>0$；乘系数规范中的 $\nu_\epsilon/2$ 及反向比例 $t$ 即得 (RC.190)。这是首阶两点成本的唯一性，不排除有限预算族中 $t=t(A)\to0$ 的反向比例，也不分类全部精确有限 $A$ 最优仪器。$\square$

在本源及本闭区间，§85.6、§87.3 所列的中间 $b_\pm$ 零清单缺口由推论 92.1 给出空清单；§85.1 的一般并列规则仍保留其条件含义，但在这里没有触发点。这只结算这两个探测器，不结算 JS 边缘转移、接触后的取向／重合集或其他原转移问题。

## 93. 无绝对值的系数分支与准确正则性

**推论 93.1（条件系数及继承的一致性）。** 在约定 88.1 的全部系数前提下，$0\le s\le s_{\rm c}$ 时，取 $r=r_\star$ 于 $s\le s_{\rm p}$，其余用 (RC.122) 的同一选定逆式。则

$$
\boxed{
K(s)=\frac12\sum_{\epsilon=\pm1}
\nu_\epsilon[a_\epsilon(r)+2b_\epsilon(r)]
=\frac12\sum_{\epsilon=\pm1}\nu_\epsilon
[h_{\epsilon,+}^T(\mathcal Y(r)-\epsilon G)h_{\epsilon,+}
-\lambda(r)z_\epsilon].
}
\tag{RC.191}
$$

这里 $b_A=e^A-1$，$K(s)=\lim_{A\to\infty}b_A[\mathcal T(s)-\mathcal T_A(s)]$，保持 (RC.105) 的规范。$\mathcal Y,\lambda$ 仍由 (RC.130)–(RC.131) 明确给出，$a_\epsilon,b_\epsilon$ 仍由 (RC.134) 给出，故没有剩余取向优化。

证明。(RC.187) 使 $|b_\epsilon|=-b_\epsilon$，代入 (RC.135) 即得。§82 的同一个三条正主射线矩修复和两个饱和物理谱标签现在统一选 $h_{+,+},h_{-,+}$，无需更换源、失败 effect 或容量。原全类下界与同族上界继续给出 (RC.136) 的一致 $O(b_A^{-2})$ 余项；接触邻域仍按 §84.2 固定第四条射线及其静态权重，只修复原三条正射线，故 (RC.155)–(RC.157) 的连续拼接和联合首阶极限保持其原条件。这里没有重新从符号估计推出那些全类系数桥。$\square$

**推论 93.2（解析参数分支及接缝边界）。** (RC.191) 的 $r$ 参数表达式在闭区间 $I$ 的一个邻域有实解析延拓；$K(s)$ 在非平台开区间 $(s_{\rm p},s_{\rm c})$ 实解析，并在两个端点各有来自这条分支的单侧解析表达。平台上 $K=K_{\rm flat}$，其与非平台分支及静态接触处的连续性沿用 (RC.146)、(RC.156)。本区间没有由 $|b_\epsilon|$ 零点产生的折角或更高阶绝对值奇性。

证明。所有根式被开方量严格正，所有列出的分母及 $h_{\rm fr}'$ 非零；紧致性使这些性质在 $I$ 的一个邻域保持。故 $F,\psi,\lambda,\mathcal Y$ 和 (RC.191) 的参数式解析。又 $s=s_0h_{\rm fr}(r)$ 的导数严格正，解析逆给出非平台的 $s$ 表达式和分支单侧延拓。平台和接触的连续性使用原连续对偶与系数拼接前提。$\square$

探测器零接缝为空并不消除物理静态支撑／接触接缝。这里没有计算 $s_{\rm p}$ 或 $s_{\rm c}$ 两侧导数，也不据此断言两侧导数相等、全域 $C^1$、更高阶平滑或接触后额外正则性。有限预算精确接触、最优支撑和字母表也不由解析首阶式决定。

## 94. 结果来源和完整有限前沿的边界

**约定 94.1（复用、内容与文献范围）。** §88–93 是仓内同源矩阵恒等式与连续有理估计的普通条件性综合，文献身份为 repo-derived。源根／秩／TP、HALF minimax、sharp 联合成本、未平均实等号面、静态符号约化和全局静态曲线各按约定 88.1 的供应范围使用；端点取向、系数存在性、一般谱 slack／容量／修复机制、完整共同构造及连续接触拼接保持 §78–87 的归属。本节补充的是两个原探测器在整个闭区间上的严格符号界、空的有序零清单及其恰当首阶推论。

通用线性代数、有理不等式及根式分支核对已在证明中展开；没有另借外部根数、敏感度或图论转移定理。§87.1 的 equality S-lemma 仍只承担其原第四 slack 完成接口，本节不新增该外部定理的适用范围。不主张文献穷尽、外部新颖性、优先权或 Lean/kernel 证明。

**约定 94.2（原 programme 完整保留）。** 原弱有限 $(s,A)$ 前沿仍须在全部可行内点上联合评价定向 failure allocation 和全部 live-height decompositions，包括低于固定 allocation 最大对比度的情形，并给出共同正全局最优族、完整 contact／rank／optimizer 变化和参数 atlas。隐式 SDP、静态支持、局部 KKT、首阶达到族或五 low 加一 high 的构造上界均不替代该目标。精确有限 $A$ 最优仪器及其最小实际字母表、JS 边缘根清单、接触后重合集、剩余统一端点区间、下一项、临界五标签／静态接触联合插值与尺度均保留原范围的未决义务。不把固定强度或接触首阶极限与 $s\uparrow s_0$ 的非一致端点极限互换。

同一个原共同达到族保持全部十二输出，$e_{5,e,n}=e_{27,e,n}=E_*$，$e_{16,e,n}<71/484<37/250<E_*$；没有十二误差全相等的结论。报告是 $\mathsf V\ge s$，联合量子份额按未来可访问性计数，活动按每个实际整个 fibre 积分后取最大；隐藏 Kraus 数、静态原子数、极限失败射线数、live 投影线数及实际获取标签数仍是不同数量。五 Borel 分量、条件参考、正 survivors、TP 控制及 FIRST $6+u$ 由原同一构造同时承担，不能用分别可达到的边缘值拼成一个仪器。

未知 specimen 的合法 native 访问、原源／目标校准、共同 coherent storage／计数和持续时间、decoder actuation、统一物理时钟、实际 FIRST、archive/source/epoch/controller/permission 的共同实现桥仍未验证。OriginalControl 仍为几何供应；没有 Boolean／native／资源计数转移，也没有全有限平面、完整 programme 或源最终批准结论。

## 追加锚（本行以下为增补区）
