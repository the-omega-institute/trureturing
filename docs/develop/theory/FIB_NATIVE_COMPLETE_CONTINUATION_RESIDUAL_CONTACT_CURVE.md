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
