# Native explicit zero-transfer loss gap

> This is a new ordinary-theory reference volume. Its intended atomizer is
> `generic-v1`; no ingestion or ledger status is asserted here. After admission,
> corrections and extensions belong after the final append anchor, preserving
> the preceding source bytes. The arguments below are ordinary mathematics,
> conditional on the exact premises expressly identified in §5. They have not
> been verified by the Lean kernel.

## 1. The quantitative increment and its provenance

**Convention 1.1 (the bounded claim).** In the original twelve-history,
single-specimen experiment of [Complete Continuation Gap][CG], let
$E_\star$ denote its complete-output common-CPTP optimum. This volume gives
a closed positive algebraic constant $\epsilon_{\rm q}$ such that every
original common processor whose supported live map has zero population
transfer satisfies

$$
E(\Phi)\geq E_\star+\epsilon_{\rm q}.
\tag{ZG.1}
$$

The exact task is restated in §§2–4, the credited algebraic point is specified
in §5, and the constant is defined in §6. Sections 7–8 prove its positivity
and its uniform applicability. No unknown minimum, distance to an optimizer,
stability modulus or optimization value occurs in that constant.

CG18 already proves an existential zero-transfer gap. CG17 already identifies
every optimizer's sign-averaged live map and four necessary positive
transfers. Current CG21–25 also already prove an actual joint acquisition
bottleneck, Schmidt-number-three necessity, an existential dimension-two gap
and positive high-dimensional mass on every normalized input. Those results
are prior coverage, with the precise correspondence in §10. The increment
here is the explicit constant in (ZG.1), for the zero-transfer class. It does
not quantify the distinct dimension-two gap.

**Convention 1.2 (authorship, evidence and review status).** The supplied
explicit-gap proposal and its separately supplied independent check are
credited mathematical evidence for this construction. Their conclusions are
fallible inputs, rather than instructions or proof authority. A sole CLI
mathematical source author selected and checked the deductions and exposition
given here against the complete supplied current DEV source. The useful
structure and GitHub mathematics conventions come from the supplied
`theory-volume-template` materials. No delegated source authorship or new
mathematical execution is part of this volume. No claim about heterogeneous
models or sterile priors is made. A fresh independent final-review triplet,
publication through PR and required CI are separate subsequent obligations;
this source is not their approval. The continuing research objective remains
active.

## 2. The actual original histories and legal request

**Definition 2.1 (original path premises).** The original source uses a base
$b=(X,Y,Z)$, $r=1-Z$, with $0<Z<1$ and $0<X,Y<r$. Its permitted height
interval, populations and real phase coefficients are

$$
\begin{aligned}
J_b&=(\max(0,X+Y-r),\min(X,Y)),\\
\pi_b(k)&=(r-X-Y+k,X-k,Z,Y-k,k),\\
\mathbf d&=(1,-1,0,-1,1),\\
I_b(k)&=\sum_{i\in\{0,1,3,4\}}\pi_b(k)_i^{-1},
&w_b(k)_i&=\frac{\mathbf d_i}{\pi_b(k)_i I_b(k)}.
\end{aligned}
\tag{ZG.2}
$$

An original history has finite duration $T\geq0$, continuous real coordinates
$k,\chi$, strict $k(t)\in J_b$ and finite variation of $\chi$. The regularity
permission is either absolute continuity of both coordinates, or the original
finite-piecewise-$C^1$ alternative whose derivative rates extend continuously
on each closed piece. For the common preparation lift $\theta$, its normalized
live vector has coordinates

$$
\psi_i(t)=\sqrt{\pi_b(k(t))_i}\,
 \exp\!\left(-i\left[\theta_i+
 \int_0^t w_b(k(s))_i\chi'(s)\,ds\right]\right).
\tag{ZG.3}
$$

Real phase lifts and signed integer winding
$\chi(T)-\chi(0)=2\pi m$ are retained. Literal chronological composition does
not read or reset that lift. These source permissions are credited as in
CG2; selecting the following catalogue does not modify the original class.
Original failure index $4$ always names mode $13$.

**Definition 2.2 (fixed catalogue from one preparation).** Fix

$$
c=\frac14,\quad Z=\frac12,\quad b=(c,c,Z),\quad
a=\frac1{16},\quad h=\frac{11}{256},\quad d=\frac6{256},\quad L=1.
\tag{ZG.4}
$$

Here $J_b=(0,c)$,
$\pi_b(k)=(k,c-k,Z,c-k,k)$ and

$$
w_b(k)=\left(\frac{c-k}{2c},-\frac{k}{2c},0,
                         -\frac{k}{2c},\frac{c-k}{2c}\right).
\tag{ZG.5}
$$

In the original five-mode space let

$$
|+\rangle=\frac{e_0+e_4}{\sqrt2},\qquad
|-\rangle=\frac{e_1+e_3}{\sqrt2},\qquad |2\rangle=e_2,
\qquad V=\operatorname{span}\{|+\rangle,|-\rangle,|2\rangle\}.
\tag{ZG.6}
$$

The isometry $\iota:\mathbb C^3\to\mathbb C^5$ has these ordered columns.
Within three-dimensional matrices only, indices $0,1,2$ mean $(+,-,2)$,
and $P_j=|j\rangle\langle j|$ refers to this basis. These indices do not
rename the five failure sectors.

The twelve actual histories are

$$
\mathcal H=\{(x_{\rm old},\beta,m):
256x_{\rm old}\in\{5,16,27\},\quad
\beta\in\{0,\pi\},\quad m\in\{0,1\}\}.
\tag{ZG.7}
$$

They start from the same preparation at $a_0=1/8$, with calibration
$\theta=0$. To specify the credited realization, put $q_0=1/16$ and
$B_{\rm rect}=8\beta-4\pi m$. Each row below lasts one unit and has affine
coordinates, with the displayed real values joined literally.

| Leg | Height | Real phase coordinate |
| --- | --- | --- |
| 1 | $a_0$ | $0\longrightarrow2\pi m$ |
| 2 | $a_0\longrightarrow q_0$ | $2\pi m$ |
| 3 | $q_0$ | $2\pi m\longrightarrow2\pi m+B_{\rm rect}$ |
| 4 | $q_0\longrightarrow a_0$ | $2\pi m+B_{\rm rect}$ |
| 5 | $a_0$ | $2\pi m+B_{\rm rect}\longrightarrow2\pi m$ |
| 6 | $a_0\longrightarrow x_{\rm old}$ | $2\pi m$ |

Their residual phase vector is
$(\beta,\beta-\pi m,0,\beta-\pi m,\beta)$. At time six the actual normalized
live vector is consequently

$$
\psi_{x_{\rm old},\beta,m}
=\frac{|2\rangle}{\sqrt2}
 +e^{-i\beta}\left(\sqrt{2x_{\rm old}}\,|+\rangle
       +(-1)^m\sqrt{2(c-x_{\rm old})}\,|-\rangle\right).
\tag{ZG.8}
$$

The source's old reached-cut probabilities at heights $5/256,16/256,27/256$
are respectively $32/177,2/9,32/111$. The comparison starts with the sole
specimen normalized at that already reached cut. Those probabilities are
neither new source priors nor acceptance weights. Earlier failure archives
remain absorbing; no repeated preparation or additional acquisition success
event is conditioned upon.

**Convention 2.3 (unchanged continuation permissions).** The public command
is the relative ramp
$k(t)=x_{\rm old}+dt$, $\chi(6+t)=\chi(6)$, $0\leq t\leq1$. Its legal
height domain is
$(0,c-d)=(0,58/256)$, containing all three catalogue heights, and its terminal
heights are $11/256,22/256,33/256$. More generally the source's relative
increments $A,C$ start at zero and have height domain
$(\ell_b-\min A,u_b-\max A)$ when $J_b=(\ell_b,u_b)$. The request here is
promised legal on the catalogue. Naming a partial command supplies no sensor
for an unknown domain violation. A known denial or mismatch keeps its visible
unexecuted rejection and controller update. Zero duration permits only the
matching zero-displacement identity, not an instantaneous nonzero path.

The six legs and ramp use finite duration and finite winding, not a wall
limit. On this experiment every population is at least $5/256$, height speed
is at most $27/256$, phase speed at most $8\pi$ and phase variation at most
$16\pi$, as already recorded in CG2. Original synthesis, calibrated execution
and these permission conventions are credited source premises; no extra
actuator is inferred from the geometric paths.

## 3. The one-channel complete-output task

**Definition 3.1 (one input and common apparatus).** Along with the normalized
old-cut specimen there is a fixed common metadata/blanks state
$\tau_{\rm meta}$. It contains the no-failure flag, aligned cut clock,
source/preparation/epoch identity, fixed reference calibration, common
permissions and controller state. It contains no readable unknown history,
old waveform, generator word, height programme, parity helper, environment
port, source callback or additional specimen. No source-dependent installed
processor is furnished.

The comparison allows arbitrary independent ancillary spaces, private
randomness, computation, finite adaptive instruments and retained classical
or quantum records, with a fixed common output interpretation. Branches stay
unnormalized and every acquisition abort, denial and unexecuted rejection is
included. Absorbing $\tau_{\rm meta}$ and independent apparatus gives one
history-independent CPTP map on the entire complex input algebra. A map on
the original five-mode algebra restricts along $\iota$ to a CPTP map on
$M_3(\mathbb C)$; all arguments below hold for that entire algebra, including
non-Hermitian matrix units and arbitrary passive reference amplification.
They are not fits to twelve separate density matrices. Enlarging to all
common CPTP maps confers no additional legal quantum read or native control.

**Definition 3.2 (the twelve targets).** Write $y=256x_{\rm old}$ and set

$$
\begin{aligned}
p_y&=\left(\frac y{128},\frac{64-y}{128},\frac12\right),
&a_y&=(\sqrt{p_{y0}},\sqrt{p_{y1}},\sqrt{p_{y2}})^T,
&\rho_y&=a_ya_y^T,\\
d_y&=\left(\frac y{128},\frac{y(58-y)}{128(y+6)},
                           \frac y{2(y+6)}\right),
&\xi_y&=(\sqrt{d_{y0}},\sqrt{d_{y1}},\sqrt{d_{y2}})^T,
&B_y&=\xi_y\xi_y^T,\\
s_y&=\frac y{y+6},
&f_y(t)&=\frac{6y}{(y+6t)^2},
&w&=(0,1/4,1/2,1/4,0).
\end{aligned}
\tag{ZG.9}
$$

The formulas for $a_z,p_z$ also apply at the three successor heights
$z=y+6$. All roots mean positive real roots. Thus $\operatorname{tr}\rho_y=1$,
$\xi_y=\sqrt{s_y}a_{y+6}$ and $\operatorname{tr}B_y=s_y$.
Put $U=U_{e,n}=\operatorname{diag}(e,n,1)$, where
$e=(-1)^{\beta/\pi}$ and $n=e(-1)^m$. The four original pairs
$(\beta,m)=(0,0),(0,1),(\pi,0),(\pi,1)$ give
$(e,n)=(1,1),(1,-1),(-1,-1),(-1,1)$ respectively. The actual input in these
coordinates is $U\rho_yU^\dagger$.

The full ideal output $\Omega_{y,U}$ has the coherent live block
$UB_yU^\dagger$ and, for EACH separately labelled original failure sector
$\ell=0,1,2,3,4$, the entire measure

$$
(\Omega_{y,U})_\ell(dt)=w_\ell f_y(t)\,dt\,P_f,
\qquad 0\leq t\leq1,\qquad P_f=|f\rangle\langle f|.
\tag{ZG.10}
$$

Index $4$ retains the name mode $13$, including its zero ideal measure.
The two minus-mode labels $1$ and $3$ remain distinct. Time is the exact
measurable elapsed time $t$, equivalently the absolute time $6+t$; no binning
or finite-bit representation is assumed. The live and failure traces are
$s_y$ and $\int_0^1 f_y(t)dt=1-s_y$, so the complete target is normalized.
It has zero mass in extra, abort and rejection sectors. The first executed
failure is absorbing: no later retry, reset, reversal, replacement or
positive-carrier operation follows it. Old archives and declared controller
updates stay in their respective branches.

For clarity, the calibrated source law underlying this target, with
$\nu=d$, $x=x_{\rm old}$ and $S_x(t)=x/(x+\nu t)$, has terminal live operator
and failure densities on $V$

$$
\begin{aligned}
K_x&=\operatorname{diag}\left(1,
 \sqrt{\frac{x(c-x-d)}{(x+d)(c-x)}},\sqrt{\frac{x}{x+d}}\right),\\
\mathcal I_{x,2}(dt)(A)
 &=f_x(t)|f\rangle\langle2|A|2\rangle\langle f|\,dt,
&f_x(t)&=\frac{\nu x}{(x+\nu t)^2},\\
\mathcal I_{x,\ell}(dt)(A)
 &=\frac{cf_x(t)}{2(c-x)}|f\rangle\langle-|A|-\rangle\langle f|\,dt
 &&(\ell=1,3),\\
\mathcal I_{x,0}&=\mathcal I_{x,4}=0.
\end{aligned}
\tag{ZG.11}
$$

These are the credited calibrated, source-indexed instruments of CG4;
their total effect is $I_V$. Applied to (ZG.8), they give (ZG.9)–(ZG.10).
Their dependence on $x$ does not make $x$ readable or install $K_x$ in a
common processor.

**Definition 3.3 (the complete objective).** For normalized complete cq
outputs use $\operatorname{dist}(\omega,\eta)=\|\omega-\eta\|_{1,\rm cq}/2$.
If both have densities in the canonical sectors, the norm is the live trace
norm plus the sum of the five integrated stopped trace norms, together with
all other sector contributions. For arbitrary countably additive simulated
measures, choose a common dominating scalar measure in each sector and
integrate the trace norms of their Radon–Nikodym densities. This includes
atomic and singular-continuous time mass. Every wrong-support, extra,
abort and rejection contribution is counted, even when its ideal mass is
zero. Fixed common interpretation may forget extra record fields but never
delete an outcome or divide its mass by success probability.

The objective and benchmark are exactly CG.20:

$$
E(\Phi)=\max_{y\in\{5,16,27\},\ e,n\in\{\pm1\}}
 \frac12\|\Omega_{y,U}-\Phi(U\rho_yU^\dagger)\|_{1,\rm cq},
\qquad E_\star=\inf_{\Phi\ {\rm common\ CPTP}}E(\Phi).
\tag{ZG.12}
$$

All twelve targets remain in this maximum. This is a source-indexed target
experiment, not a demand that source-dependent instruments act as one map.

## 4. Zero transfer and the direction of a finite necessary test

**Definition 4.1 (the exact subclass).** Compress the live output of a common
full channel to $V$ and call that CP, trace-nonincreasing map $\Lambda$.
It is zero-transfer if

$$
T_{ij}:=\langle i|\Lambda(P_j)|i\rangle=0\qquad(i\ne j).
\tag{ZG.13}
$$

We reuse CG18.1's equivalence with diagonal live Kraus operators and with

$$
\Lambda(A)=C\odot A,
\qquad C\succeq0,
\qquad 0\leq C_{ii}\leq1,
\qquad G_L=\Lambda^\dagger(I)=\operatorname{diag}(C_{ii}).
\tag{ZG.14}
$$

The matrix $C$ may be complex Hermitian. The elementary reason for the exact
scope is $T_{ij}=\sum_a|(L_a)_{ij}|^2$ in any live Kraus representation:
zero transfer forces every off-diagonal entry of every $L_a$ to vanish.
Factoring $C$ recovers diagonal Kraus operators, and its diagonal is exactly
the live effect. Equivalently, its output-input Choi matrix is supported on
$\operatorname{span}\{|00\rangle,|11\rangle,|22\rangle\}$ with block $C$.
This recalls a prior characterization; it imposes neither reality nor an
additional covariance hypothesis on competitors.

**Convention 4.2 (the finite contraction).** The common CPTP output operation
$\mathcal C$ of CG17 retains the supported live compression, sends the trace
of the entire canonical failure register to a scalar failure flag, and sends
all remaining mass to an other flag. Live-complement cross terms are
discarded by that operation. It counts every mode, exact time, stopped
support and singular measure in the failure flag, and every abort, rejection
and live-complement mass in other. It is a necessary test of (ZG.12).

Using the unnormalized output-input convention
$J_\Lambda=\sum_{i,j}\Lambda(|i\rangle\langle j|)\otimes|i\rangle\langle j|$,
ALL finite candidates of CG.155 are triples with

$$
\begin{aligned}
&J_\Lambda,G_f,G_o\succeq0,
\qquad \operatorname{Tr}_{\rm out}J_\Lambda+G_f^T+G_o^T=I_3,\\
&\Theta(A)=(\Lambda(A),\operatorname{tr}(G_fA),\operatorname{tr}(G_oA)),\\
&E_c(\Theta)=\max_{y,U}\frac12\left(
 \|UB_yU^\dagger-\Lambda(U\rho_yU^\dagger)\|_1
 +\left|1-s_y-\operatorname{tr}(G_fU\rho_yU^\dagger)\right|
 +\operatorname{tr}(G_oU\rho_yU^\dagger)\right).
\end{aligned}
\tag{ZG.15}
$$

The budget is a whole-complex-algebra CP/TP condition. In particular,
$\operatorname{Tr}_{\rm out}J_\Lambda=G_L^T$; transposes cannot be dropped
for arbitrary complex effects. For an original channel, contractivity gives

$$
E(\Phi)\geq E_c(\mathcal C\Phi),
\tag{ZG.16}
$$

and the contraction leaves its supported live map unchanged. A lower bound
proved for ALL zero-transfer triples therefore transfers in the displayed
direction. No arbitrary finite optimizer is presumed to lift to an optimal
full exact-time channel. The full proof in §8 also works directly without
performing this contraction.

## 5. The exact conditional algebraic data

**Definition 5.1 (the certificate chart).** In this section $x$ means the
six-coordinate chart variable, not the scalar original height:

$$
x=(\lambda,\alpha_1,\alpha_2,\beta_1,\beta_2,z).
\tag{ZG.17}
$$

The chart coordinates $\beta_1,\beta_2$ are unrelated to the original
history phase $\beta$. With the fixed matrices of (ZG.9), define

$$
\begin{aligned}
v_5&=(\alpha_1,\alpha_2,-1)^T,
&v_{27}&=(\beta_1,\beta_2,1)^T,
&R_y&=\frac{v_yv_y^T}{v_y^Tv_y},\\
A_5&=\lambda R_5,
&A_{27}&=(1-\lambda)R_{27},
&\zeta&=(z,\lambda p_{51},\lambda p_{52}),\\
Z_d&=\operatorname{diag}\zeta,
&N&=A_5\odot\rho_5+A_{27}\odot\rho_{27},
&S_0&=Z_d-N.
\end{aligned}
\tag{ZG.18}
$$

For $i<j$ set

$$
S_{ij}=\begin{pmatrix}
\zeta_j-\sum_{y\in\{5,27\}}(A_y)_{ii}p_{yj}&-N_{ij}\\
-N_{ij}&\zeta_i-\sum_{y\in\{5,27\}}(A_y)_{jj}p_{yi}
\end{pmatrix}.
\tag{ZG.19}
$$

Finally put

$$
\begin{aligned}
F(x)&=\operatorname{tr}(A_5B_5)+\operatorname{tr}(A_{27}B_{27})
                    -\operatorname{tr}Z_d+\frac6{11}\lambda,\\
g(x)&=(1000\det S_0,\det S_{01},\det S_{02}),\\
\Psi(x,\eta)&=\bigl(\nabla_x(F+\eta\cdot g),g\bigr),
\qquad \eta=(\eta_0,\eta_1,\eta_2).
\end{aligned}
\tag{ZG.20}
$$

These reproduce CG.111–CG.114 as algebraic definitions. Their only chart
denominators are $1+\alpha_1^2+\alpha_2^2$ and
$1+\beta_1^2+\beta_2^2$, so the rational functions and all derivatives are
defined on the entire real chart.

**Premise 5.2 (credited isolated root, ranks and margins).** CG13.2–13.3
supply a unique exact zero $u_\star=(x_\star,\eta_\star)$ of $\Psi$ in the
closed box of radius $10^{-24}$ in EACH coordinate about the following
rational center, in this order:

| Coordinate | Exact rational center |
| --- | --- |
| $\lambda$ | $0.479508042205945691075728241615$ |
| $\alpha_1$ | $1.412018697539825943102823246594$ |
| $\alpha_2$ | $1.185897402486986028204155873343$ |
| $\beta_1$ | $0.413330945620125544606320492846$ |
| $\beta_2$ | $0.809647491041060318009094562763$ |
| $z$ | $0.066998926272600209516864472757$ |
| $\eta_0$ | $0.279795267654829218213193898783$ |
| $\eta_1$ | $0.199570407911600478528148253443$ |
| $\eta_2$ | $0.091392615490799158339482855657$ |

The point is algebraic, $D\Psi(u_\star)$ is nonsingular, and the credited
strict arithmetic margins include

$$
\begin{gathered}
\frac{47}{100}<\lambda_\star<\frac{49}{100},\qquad
\eta_{k,\star}>0\quad(k=0,1,2),\\
\kappa:=z_\star-\lambda_\star p_{50}>\frac6{125},\qquad
(S_{0,\star})_{00}>\frac6{125},\qquad
\det S_{0,\star}[\{0,1\}]>\frac{23}{10000},\\
S:=S_{0,\star}\succeq0,\quad\operatorname{rank}S=2,\qquad
S_{01,\star},S_{02,\star}\succeq0\text{ of rank }1,\qquad
S_{12,\star}\succ0.
\end{gathered}
\tag{ZG.21}
$$

CG16.1 further supplies the ORIGINAL full-output equality

$$
E_\star=F(x_\star).
\tag{ZG.22}
$$

The box center is not substituted for its exact zero. Existence, uniqueness
in that box, its algebraicity, nonsingularity, ranks, strict margins and the
matching full-output optimum are credited ordinary computer-assisted
premises. This volume does not rerun their arithmetic, claim uniqueness of
all algebraic roots or full channels, or assert kernel verification. The
new proof below needs the positive $\lambda_\star,1-\lambda_\star,
\eta_{1,\star},\kappa$, rank-two positivity of $S$, stationarity,
nonsingularity and (ZG.22); it does not require a new certificate at a
perturbed point.

**Lemma 5.3 (the prior gradient-rank consequence).** Let
$G=[\nabla g_0\ \nabla g_1\ \nabla g_2]_{x_\star}$, a real $6$ by $3$
matrix. Then $G^TG\succ0$ and $\nabla F(x_\star)=-G\eta_\star$.

Proof. Stationarity is part of $\Psi(u_\star)=0$. The bordered Jacobian is
$\left(\begin{smallmatrix}A&G\\G^T&0\end{smallmatrix}\right)$.
If $Gc=0$, it annihilates $(0,c)^T$; its nonsingularity therefore gives
$c=0$. This is exactly the already extracted consequence CG.164, recalled
to expose the dependence of the inverse used next. For every nonzero real
$c$, $c^TG^TGc=\|Gc\|^2>0$. $\square$

## 6. A closed algebraic loss constant

**Definition 6.1 (an exact ascent direction).** In constraint order
$(g_0,g_1,g_2)$ let $e^{(1)}=(0,1,0)^T$ and define

$$
d=-G(G^TG)^{-1}e^{(1)},\qquad x(r)=x_\star+rd.
\tag{ZG.23}
$$

Every entry of $G$ is a fixed derivative of the displayed rational
functions, rather than a new datum. More explicitly, for chart coordinate
$x_i$ and constraint index $k$,

$$
G_{ik}=c_k\operatorname{tr}\left(
 \operatorname{adj}(S_k)\,\partial_{x_i}S_k\right)_{x_\star},
\quad (S_k,c_k)=(S_0,1000),(S_{01},1),(S_{02},1).
\tag{ZG.24}
$$

Partial differentiation here means the ordinary finite sum, product and
quotient rules on (ZG.18)–(ZG.19). Thus (ZG.24) defines finite algebraic
entries without an unspecified bound or optimization. Lemma 5.3 gives

$$
G^Td=-e^{(1)},\qquad
\nabla g_0(x_\star)\cdot d=0,\qquad
\nabla F(x_\star)\cdot d=\eta_{1,\star}>0.
\tag{ZG.25}
$$

Write

$$
\ell=d_\lambda,\qquad
q_5=\sqrt{d_{\alpha_1}^2+d_{\alpha_2}^2},\qquad
q_{27}=\sqrt{d_{\beta_1}^2+d_{\beta_2}^2},\qquad
c_\kappa=d_z-p_{50}\ell.
\tag{ZG.26}
$$

The symbol $d$ in (ZG.23) is a chart direction, distinct from the fixed
scalar ramp displacement $6/256$ in (ZG.4).

**Definition 6.2 (explicit matrix and scalar bounds).** Put
$K=\left.\frac{d}{dr}S_0(x(r))\right|_{r=0}$. To specify it without leaving
an unevaluated directional-derivative operation, let
$w_5=(d_{\alpha_1},d_{\alpha_2},0)^T$ and
$w_{27}=(d_{\beta_1},d_{\beta_2},0)^T$, and at $x_\star$ form

$$
\begin{aligned}
R'_y&=\frac{w_yv_y^T+v_yw_y^T}{v_y^Tv_y}
       -\frac{2v_y^Tw_y}{v_y^Tv_y}R_y,\\
K&=\operatorname{diag}(d_z,\ell p_{51},\ell p_{52})
 -\ell(R_5\odot\rho_5-R_{27}\odot\rho_{27})\\
&\hspace{1em}-\lambda_\star R'_5\odot\rho_5
 -(1-\lambda_\star)R'_{27}\odot\rho_{27}.
\end{aligned}
\tag{ZG.27}
$$

All $v_y,R_y,R'_y$ on the right of (ZG.27) are at the exact starred point.
Define

$$
\begin{aligned}
k&=\sqrt{\operatorname{tr}(K^2)},
&\gamma&=\frac{(\operatorname{tr}S)^2-\operatorname{tr}(S^2)}
                         {2\operatorname{tr}S},
&m_\lambda&=\lambda_\star(1-\lambda_\star),\\
M&=2|\ell|(q_5+q_{27})+7(q_5^2+q_{27}^2),
&b_{\rm q}&=M+\frac{2k^2}{\gamma}.
\end{aligned}
\tag{ZG.28}
$$

Here $m_\lambda$ is not the history's winding. Finally set

$$
\begin{aligned}
\tau_{\rm q}
&=\left[1+\frac{2(1+|\ell|)}{m_\lambda}
 +\frac{2(1+|c_\kappa|)}{\kappa}
 +\frac{2(1+k)}{\gamma}
 +\frac{2(1+M+3b_{\rm q})}{\eta_{1,\star}}\right]^{-1},\\
\boxed{\epsilon_{\rm q}=\frac{\eta_{1,\star}\tau_{\rm q}}2.}
\end{aligned}
\tag{ZG.29}
$$

The auxiliary parameter $r$ and its endpoint $\tau_{\rm q}$ do not alter the
failure-time variable $t$ or the fixed metadata $\tau_{\rm meta}$. This is the
constant supplied in the explicit-gap proposal, with notation disambiguated.
An inverse in (ZG.23) may be written as adjugate divided by determinant;
absolute values may be written $|a|=\sqrt{a^2}$. Hence every operation in
(ZG.23)–(ZG.29) is finite algebraic arithmetic and a specified nonnegative
square root applied to the isolated algebraic point and fixed algebraic
matrices. The following proofs establish that every denominator is positive.
No numerical value or sharpness is claimed.

## 7. Controlled ascent and a quadratic positivity correction

**Lemma 7.1 (positive constants and the entire segment).** All expressions in
§6 are finite, $\gamma,m_\lambda,\kappa,\eta_{1,\star},\tau_{\rm q},
\epsilon_{\rm q}>0$, and for $0\leq r\leq\tau_{\rm q}$,

$$
0<\lambda(r)<1,\qquad
\kappa(r):=z(r)-p_{50}\lambda(r)>\kappa/2,\qquad
rk<\gamma/2.
\tag{ZG.30}
$$

Proof. Write the two positive eigenvalues of $S$ as $\sigma_1,\sigma_2$.
The formula (ZG.28) gives
$\gamma=\sigma_1\sigma_2/(\sigma_1+\sigma_2)>0$, with
$\gamma\leq\min(\sigma_1,\sigma_2)$. The eigenvalues justify this bound;
they are not unknown spectral extrema in the definition of $\gamma$.
Premise 5.2 and Lemma 5.3 supply the other positive denominators and the
inverse. The real symmetric $K$ has finite Frobenius norm $k$, and
$M,b_{\rm q}\geq0$. Thus the reciprocal in (ZG.29) is finite and positive.
It is smaller than $1$ and separately smaller than each of

$$
\frac{m_\lambda}{2(1+|\ell|)},\quad
\frac{\kappa}{2(1+|c_\kappa|)},\quad
\frac{\gamma}{2(1+k)},\quad
\frac{\eta_{1,\star}}{2(1+M+3b_{\rm q})}.
\tag{ZG.31}
$$

Since $m_\lambda\leq\min(\lambda_\star,1-\lambda_\star)$ and
$\lambda(r)=\lambda_\star+r\ell$, the first bound leaves $\lambda(r)$
strictly between zero and one on the entire interval. The affine identity
$\kappa(r)=\kappa+rc_\kappa$ and the second bound give its assertion.
The third gives $rk<\gamma/2$, also if $k=0$. None of this requires the
segment to stay in the isolation box or to consist of roots of $\Psi$.
$\square$

**Lemma 7.2 (exact tangent and uniform Taylor remainders).** Let

$$
P=\frac{\operatorname{adj}S}{\operatorname{tr}(\operatorname{adj}S)},
\qquad Q=I_3-P.
\tag{ZG.32}
$$

Then $P$ is the rank-one orthogonal kernel projection of $S$,
$PKP=0$, $S\succeq\gamma Q$, and throughout $0\leq r\leq\tau_{\rm q}$,

$$
\begin{aligned}
\|S_0(x(r))-S-rK\|_{\rm op}&\leq Mr^2,\\
F(x(r))&\geq F(x_\star)+\eta_{1,\star}r-Mr^2.
\end{aligned}
\tag{ZG.33}
$$

Proof. Rank-two positivity gives
$\operatorname{adj}S=\sigma_1\sigma_2P$. The zero $g_0$ derivative in
(ZG.25) is $1000\operatorname{tr}((\operatorname{adj}S)K)=0$.
Thus $\operatorname{tr}(PK)=0$, and rank one implies $PKP=0$.
The eigenvalue bound in Lemma 7.1 gives $S\succeq\gamma Q$.

For the remainder estimates, along either chart vector write
$v(r)=v(0)+rw$, with last coordinate fixed at $-1$ or $1$,
$h(r)=\|v(r)\|\geq1$, $q=\|w\|$ and $u=v/h$. Direct differentiation gives

$$
\begin{aligned}
u'&=(I-uu^T)w/h,\\
u''&=-\frac{2w(v^Tw)}{h^3}
      -\frac{v\|w\|^2}{h^3}
      +\frac{3v(v^Tw)^2}{h^5}.
\end{aligned}
\tag{ZG.34}
$$

Consequently $\|u'\|\leq q$ and $\|u''\|\leq6q^2$: the three terms in the
second line have bounds $2q^2/h^2,q^2/h^2,3q^2/h^2$. Differentiating
$R=uu^T$ now yields

$$
\|R'\|_{\rm op}\leq2q,\qquad
\|R''\|_{\rm op}\leq14q^2.
\tag{ZG.35}
$$

The second bound uses $2\|u''\|+2\|u'\|^2$. As $\lambda(r)\in(0,1)$,

$$
\begin{aligned}
A_5''&=2\ell R'_5+\lambda(r)R''_5,\\
A_{27}''&=-2\ell R'_{27}+(1-\lambda(r))R''_{27},\\
\|A_5''\|_{\rm op}+\|A_{27}''\|_{\rm op}
&\leq4|\ell|(q_5+q_{27})+14(q_5^2+q_{27}^2)=2M.
\end{aligned}
\tag{ZG.36}
$$

For any Hermitian $X$, entrywise multiplication satisfies
$X\odot\rho_y=\operatorname{diag}(a_y)X\operatorname{diag}(a_y)$, and hence
$\|X\odot\rho_y\|_{\rm op}\leq\|X\|_{\rm op}$ because every $p_{yi}\leq1$.
Also $B_y\succeq0$ and $\operatorname{tr}B_y=s_y\leq1$, so
$|\operatorname{tr}(XB_y)|\leq\|X\|_{\rm op}$. The matrix $Z_d(x(r))$ and
the scalar $\lambda(r)$ are affine. Equations (ZG.18), (ZG.20) and
(ZG.36) therefore give

$$
\|S_0''(x(r))\|_{\rm op}\leq2M,\qquad
\left|\frac{d^2}{dr^2}F(x(r))\right|\leq2M.
\tag{ZG.37}
$$

The integral Taylor remainder is the integral of $(r-s)$ times the second
derivative over $0\leq s\leq r$. Its norm, or absolute value, is at most
$Mr^2$. Use (ZG.25) for the first derivative of $F$ to obtain (ZG.33).
$\square$

**Lemma 7.3 (explicit positive-semidefinite correction).** For
$0\leq r\leq\tau_{\rm q}$,

$$
S_0(x(r))+b_{\rm q}r^2 I_3\succeq0.
\tag{ZG.38}
$$

Proof. Put $c_{\rm q}=2k^2/\gamma$. In the decomposition
$\operatorname{ran}P\oplus\operatorname{ran}Q$, consider
$S+rK+c_{\rm q}r^2I$. Its $P$ block is $c_{\rm q}r^2P$, since $PKP=0$.
Its $Q$ block is at least $(\gamma-rk)Q\succeq(\gamma/2)Q$, since
$\|K\|_{\rm op}\leq\sqrt{\operatorname{tr}(K^2)}=k$. The off-diagonal
block is $rPKQ$, of norm at most $rk$. The Schur complement of the positive
$Q$ block is therefore at least

$$
\left(c_{\rm q}-\frac{2k^2}{\gamma}\right)r^2P=0.
\tag{ZG.39}
$$

Thus $S+rK+c_{\rm q}r^2I\succeq0$, including $r=0$ and $k=0$.
The first Taylor bound in (ZG.33) gives
$S_0(x(r))\succeq S+rK-Mr^2I$. Adding
$b_{\rm q}r^2I=(M+c_{\rm q})r^2I$ proves (ZG.38). Only the diagonal
Choi-support block is required for zero transfer. The perturbed
$S_{01},S_{02},S_{12}$ are not required to remain positive. $\square$

## 8. The uniform bound on the original full output

**Lemma 8.1 (a complete-output payoff witness).** Fix a real chart point
$x$ with $0<\lambda<1$. Suppose a real diagonal matrix $\widehat Z$ satisfies

$$
\widehat Z-N(x)\succeq0,\qquad
\widehat Z-D_f\succeq0,\qquad
\widehat Z\succeq0,
\qquad D_f=\lambda\operatorname{diag}(p_5).
\tag{ZG.40}
$$

For every zero-transfer original common channel,

$$
E(\Phi)\geq\operatorname{tr}(A_5B_5)+\operatorname{tr}(A_{27}B_{27})
                  +\frac6{11}\lambda-\operatorname{tr}\widehat Z.
\tag{ZG.41}
$$

The same bound holds with $E_c$ for every zero-transfer triple (ZG.15).

Proof. For each actual sign $U$ at height $5$, choose a mathematical
output effect $M_{5,U}$ whose supported live part is $UR_5U^\dagger$,
whose part on the ENTIRE canonical failure register is identity, and whose
part on every other output is zero. For height $27$, use live part
$UR_{27}U^\dagger$ and zero on all nonlive sectors. Give the four effects
at each endpoint the weights $\lambda/4$ and $(1-\lambda)/4$ respectively.
They are valid effects, their eight positive weights sum to one, and their
weighted ideal payoff is

$$
I_{\rm ideal}=\operatorname{tr}(A_5B_5)
             +\operatorname{tr}(A_{27}B_{27})+\frac6{11}\lambda.
\tag{ZG.42}
$$

These are lower-bound coefficients, not supplied preparation priors,
accessible input labels or extra observations. The height-$16$ histories
remain in the original maximum.

For an arbitrary full channel in the stated class, (ZG.14) describes its
supported live map. Let $G_f$ be its positive input effect of the entire
canonical failure register: it includes all five labels and all exact times,
every stopped quantum support, atoms and singular-continuous mass there.
Let $G_o=I-G_L-G_f\succeq0$. It includes every remaining outcome, including
live mass outside $V$, aborts and rejections. These effects arise jointly
from the SAME full channel on the whole complex input algebra. In particular
they cannot be chosen separately for different histories.

Schur form gives
$\Lambda(U\rho_yU^\dagger)=U(C\odot\rho_y)U^\dagger$ for every actual sign.
Entrywise tracing, with $A_y,\rho_y$ real symmetric, shows that the eight
weighted simulated live payoffs sum to $\operatorname{tr}(N C)$, also when
$C$ is complex. Averaging the four ACTUAL height-$5$ inputs gives
$\operatorname{diag}(p_5)$, so the simulated failure payoff is
$\operatorname{tr}(D_fG_f)$. Diagonality of $\widehat Z$ and
$G_L=\operatorname{diag}(C_{ii})$ now gives the exact budget identity

$$
\begin{aligned}
\operatorname{tr}\widehat Z-\operatorname{tr}(NC)
                   -\operatorname{tr}(D_fG_f)
={}&\operatorname{tr}((\widehat Z-N)C)
 +\operatorname{tr}((\widehat Z-D_f)G_f)
 +\operatorname{tr}(\widehat ZG_o)\geq0.
\end{aligned}
\tag{ZG.43}
$$

Indeed $\operatorname{tr}(\widehat ZC)=\operatorname{tr}(\widehat ZG_L)$,
and $G_L+G_f+G_o=I$. Each trace on the right pairs positive Hermitian
matrices. This proves the inequality on complex matrices without suppressing
the transpose of a nondiagonal Choi multiplier.

For every individual full normalized output difference $\Delta$, total
trace is zero and any effect $M$ satisfies

$$
\operatorname{tr}(M\Delta)
=\frac12\operatorname{tr}((2M-I)\Delta)
\leq\frac12\|\Delta\|_{1,\rm cq}.
\tag{ZG.44}
$$

The inequality follows because $2M-I$ is a Hermitian contraction. It also
holds for arbitrary countably additive output measures, by integrating the
same contraction inequality against a common dominating scalar measure.
Subtract the simulated payoff, bounded above by (ZG.43), from (ZG.42),
apply (ZG.44), and bound the positive weighted average of the eight errors
by the unchanged twelve-history maximum. This proves (ZG.41).

No exceptional output mass has been dropped: failure-register mass enters
$G_f$ with its entire mass, other mass enters $G_o$, and ALL of it remains
in the full norm used in (ZG.44). The proof makes no identification of that
norm with a pooled failure probability.

For a finite triple (ZG.15), use the same live effects, identity on its
failure flag at height $5$, and zero on other. Choi positivity, zero transfer
and the joint budget give exactly (ZG.14) and (ZG.43). Its full normalized
finite output obeys (ZG.44), proving the same bound for EVERY such triple,
without any lift assumption. $\square$

**Theorem 8.2 (explicit uniform zero-transfer loss).** Under Premise 5.2,
the algebraic constant (ZG.29) is strictly positive. Every original common
full-output CPTP channel with zero-transfer live compression satisfies
(ZG.1). Every zero-transfer finite candidate of CG.155 also satisfies
$E_c(\Theta)\geq E_\star+\epsilon_{\rm q}$.

Proof. For $0\leq r\leq\tau_{\rm q}$ set

$$
\widehat Z(r)=Z_d(x(r))+b_{\rm q}r^2I_3,
\qquad D_f(r)=\lambda(r)\operatorname{diag}(p_5).
\tag{ZG.45}
$$

Lemma 7.3 supplies $\widehat Z(r)-N(x(r))\succeq0$. The special form of
$Z_d$ gives the other constraints directly:

$$
\widehat Z(r)-D_f(r)=\kappa(r)P_0+b_{\rm q}r^2I_3\succeq0,
\qquad D_f(r)\succ0,
\qquad \widehat Z(r)\succ0.
\tag{ZG.46}
$$

Here Lemma 7.1 supplies $\lambda(r)>0$ and $\kappa(r)>0$, and all entries
of $p_5$ are positive. Thus Lemma 8.1 applies and, since the added identity
has trace $3$, yields

$$
\begin{aligned}
E(\Phi)
&\geq F(x(r))-3b_{\rm q}r^2\\
&\geq F(x_\star)+\eta_{1,\star}r-(M+3b_{\rm q})r^2.
\end{aligned}
\tag{ZG.47}
$$

At $r=\tau_{\rm q}$, the last bound in (ZG.31) implies
$(M+3b_{\rm q})\tau_{\rm q}<\eta_{1,\star}/2$. With (ZG.22) this proves

$$
E(\Phi)>E_\star+\frac{\eta_{1,\star}\tau_{\rm q}}2
             =E_\star+\epsilon_{\rm q},
\tag{ZG.48}
$$

and hence the asserted weak uniform inequality. Lemma 7.1 proves positivity
of the constant. The identical calculation using the finite version of
Lemma 8.1 proves the stated finite-class bound. For an original channel,
(ZG.16) also transfers that finite necessary lower bound in the correct
direction. No compactness argument, minimax interchange, marginal lifting,
numerical optimizer or additional information port enters this proof.
$\square$

**Comparison 8.3 (what becomes explicit).** CG18 defines
$\mu_0=\min_{\mathcal K_0}E_c$ over all zero-transfer finite triples and
$\epsilon_0=\mu_0-E_\star>0$ by compactness and rigidity. Theorem 8.2 gives
$\epsilon_0\geq\epsilon_{\rm q}>0$. It neither solves that restricted
minimization nor defines its explicit constant in terms of $\mu_0$.
The mechanism is exact ascent with derivative $\eta_{1,\star}$ after the
transfer-block constraints are removed, followed by the explicit quadratic
correction of the remaining live-support constraint.

## 9. Consequences and the boundary between two resource classes

**Corollary 9.1 (the precisely defined diagonal closure).** The explicit
bound (ZG.1) holds for the implementation class of CG18.2–18.3: the sole
specimen has live interactions diagonal in the common calibrated basis;
with an actually retained apparatus/record $R$, the allowed live Kraus
operators are $\sum_jP_j\otimes B_{a,j}$. Record-local operations
$I_V\otimes B$, choices from actually acquired classical records, independent
randomization, finite composition and summation over unobserved branch
records are allowed. All coefficients and permissions are common, initial
apparatus is independent, and failure is absorbing with no return to live.
No other specimen-bearing interaction is included. The bound also holds
for explicitly defined Choi-norm limits of these live maps.

Proof. The prior closure argument preserves each specimen subspace
$|j\rangle\otimes R$ through every surviving branch. Products, sums,
independent mixtures and discarding records therefore give $T_{ij}=0$ for
$i\ne j$; absorption prevents later live contributions from failed branches.
Those zero Choi diagonal entries are closed under the stipulated limits.
Apply Theorem 8.2. This conditional class is not an exhaustive native-menu
classification. $\square$

**Corollary 9.2 (the same-effects pair with an explicit separation).** The
particular instruments $\Phi_K,\Phi_D$ of CG19.1 satisfy

$$
E(\Phi_K)=E_\star,\qquad
E(\Phi_D)\geq E_\star+\epsilon_{\rm q}>E_\star.
\tag{ZG.49}
$$

To fix the pair without an implicit optimizer choice, at the credited point
put $H=1000\eta_{0,\star}\operatorname{adj}S_{0,\star}$ and
$Q^{0j}=\eta_{j,\star}\operatorname{adj}S_{0j,\star}$ for $j=1,2$.
Their credited positive pivots define

$$
\begin{aligned}
h&=He_0/\sqrt{H_{00}},
&b^{0j}&=Q^{0j}e_0/\sqrt{Q^{0j}_{00}},\\
K_0&=\operatorname{diag}(h),
&K_{0j}&=b^{0j}_0|0\rangle\langle j|+b^{0j}_1|j\rangle\langle0|,\\
D_0&=K_0,
&D_{0j}&=b^{0j}_1P_0+b^{0j}_0P_j.
\end{aligned}
\tag{ZG.50}
$$

The live maps sum the three corresponding Kraus conjugations. Both have
the same five failure densities
$w_\ell h_0(t)\operatorname{tr}(M_fA)dt\,P_f$, where
$h_0(t)=2/(1+t)^2$ and

$$
M_f=\operatorname{diag}(0,1-H_{11}-Q^{01}_{00},
                           1-H_{22}-Q^{02}_{00}).
\tag{ZG.51}
$$

Their credited joint normalization and positivity are CG15/CG19. Their
five-mode completion compresses by $\iota$ and sends the full complementary
support to original failure label $2$ with density $h_0$ in BOTH instruments.

Proof. CG16 and CG19 supply the value for $\Phi_K$ and the same-effects
identities, including identical unnormalized reference marginals in each
corresponding branch on arbitrary joint inputs, and identical complete
failure measures. All $D_a$ are diagonal, retaining their signed amplitudes,
so $\Phi_D$ is zero-transfer. Apply Theorem 8.2 to it. Equality of effects
is also transparent from $D_{0j}^\dagger D_{0j}=K_{0j}^\dagger K_{0j}$;
it does not identify the live successor operations. The canonical live
output sums over the internal live Kraus label, just as in CG.20. No bound
for a changed task exposing that extra label is inferred. $\square$

**Proposition 9.3 (zero transfer and Schmidt number at most two differ).**
Let $\mathfrak S_2$ be the homogeneous cone of live Choi matrices admitting
a positive rank-one decomposition into vectors whose reshaped $3$ by $3$
matrices all have rank at most two, as in CG.187. The zero-transfer class
and the class $J_\Lambda\in\mathfrak S_2$ are incomparable. Consequently
(ZG.1) does not supply an explicit replacement for CG23's $\epsilon_2$.

Proof. The always-live identity channel is zero-transfer: its Schur matrix
has every entry one. Its Choi matrix is
$|\Omega\rangle\langle\Omega|$, with
$|\Omega\rangle=|00\rangle+|11\rangle+|22\rangle$, of Schmidt number
three. Every positive rank-one decomposition of a rank-one positive matrix
is supported on its range, so it cannot have rank-at-most-two vectorized
terms. This gives a zero-transfer channel outside $\mathfrak S_2$.

Conversely, the live Kraus operator $L=|0\rangle\langle1|$ has product
Choi vector $|01\rangle$ and $T_{01}=1$. Complete it to a common CPTP
channel by routing the positive complementary effect $I-P_1$ to original
failure label $2$ with density $h_0(t)P_f$. Since $\int_0^1h_0=1$, this
is a full normalized channel with live Schmidt number one and nonzero
transfer. On the original five-mode algebra use
$\widehat L=\iota L\iota^\dagger$ and complementary effect
$I_5-\iota P_1\iota^\dagger$ with the same router. These are abstract
comparison channels, not newly supplied native operations. The examples
prove both noninclusions. Theorem 8.2 applies to their zero-transfer side;
CG23's distinct existential theorem applies to its own cone. $\square$

## 10. Reuse, literature state and remaining original obligations

**Attribution 10.1 (current DEV correspondence).** All CG references below
refer to the supplied complete current continuation volume [CG], including
its §§21–25. Earlier open minimax questions in its §§7 and 11 are answered
by CG16; they are not treated here as still unresolved.

| Prior current DEV coverage | Use and boundary in this volume |
| --- | --- |
| CG1–4, CG.1–CG.20 | Actual preparation and original path permissions, twelve histories, normalized old-cut input, common metadata, calibrated coherent live successors, five exact-time stopped laws and complete error. Their nested source/control/instrument suppliers remain credited premises. |
| CG5–12 | Coherence-retaining lower tests, attainment, strict nonoptimality of the earlier lower bound, and scalar-live/fixed-filter upper channels are established prior results. None is claimed as the new explicit subclass gap. |
| CG13, CG.111–CG.123 | Exact algebraic chart, isolated rational box, arithmetic margins, ranks and nonsingular bordered Jacobian. These are conditional ordinary computer-assisted premises, not rerun here. |
| CG14–16, CG.124–CG.154 | Whole-complex lower witness, transposed Choi budget, matching common full-output instrument and exact optimum $E_\star=F(x_\star)$. The new witness keeps their effect normalization and full-output scope. |
| CG17, CG.155–CG.166 | Necessary finite contraction, rigidity of every optimizer's sign-averaged live matrix, gradient injectivity and four positive population transfers. These are reused prior coverage, not new rigidity claims. |
| CG18, CG.167–CG.170 | Exact Schur/zero-transfer characterization, existential compactness gap and precisely defined diagonal implementation closure. Theorem 8.2 replaces the unknown size by an explicit positive lower bound, without solving the restricted optimum. |
| CG19, CG.171–CG.177 | Same-effects instruments, identical branch probabilities and unnormalized reference marginals, identical failure measures, different live successors on at least eight actual histories, and a strict performance separation. Corollary 9.2 quantifies that separation. |
| CG20, CG.178 | Conditional synthesis needs a calibrated diagonal instrument, generated-record-controlled swaps, calibrated support decomposition, absorbing router and an actual exact-time service. An inverse-CDF timestamp alone is not physical first-failure timing. These obligations remain separate. |
| CG21, CG.179–CG.183 | An ACTUAL tagged acquisition cut has one joint payload algebra $\bigoplus_\alpha M_{d_\alpha}$, encoder CP branches with total effect $I$, and common full-output TP decoders whose live parts are TNI. Every accessible specimen, memory, environment, returned system and entanglement share is counted jointly; no bypass is free. Finite, countable and explicitly measurable/integrable integral versions have their stated scope. Integral encoder densities need not individually be TNI. An algebraic decomposition does not install an observed flag. |
| CG22, CG.184–CG.189 | Every full or finite-test optimizer has $\operatorname{tr}(W_3J_\Lambda)=\delta_\star>19/10$ for $W_3=|\Omega\rangle\langle\Omega|-2I_9$, hence live Schmidt number exactly three. This is already an all-optimizer conclusion, not a new consequence of (ZG.1). Its additional arithmetic margins remain source-credited. |
| CG23, CG.190–CG.192 | Every live map in $\mathfrak S_2$, hence every actual joint acquisition through fibres of dimension at most two and its stated reduced-triple closure, has a distinct existential loss $\epsilon_2>0$. Proposition 9.3 explains why the explicit zero-transfer constant does not quantify it. |
| CG24, CG.193–CG.199 | For every actual tagged factorization attaining $E_\star$, every normalized $\rho\in M_3$ individually obeys $p_H^{\rm acq}(\rho)\geq p_H^L(\rho)\geq\delta_\star^2/24>361/2400>3/20$. This unconditional high-dimensional branch mass, covering all twelve original inputs, is prior coverage. No near-optimal extension of it is claimed here. |
| CG25, CG.200–CG.203 | An abstract sufficient factorization has fibre dimensions $3,2,2,1,1$ plus the five-mode complementary branch, with explicit input-dependent qutrit-branch probabilities. The dephasing/identity, rank-boundary and omitted-entanglement-share counterexamples and the unsupplied native acquisition/timing services remain in force. Abstract sufficiency does not acquire those services. |

The supplied explicit-gap proposer is credited for the finite algebraic
construction in §6 and its quantitative mechanism. The supplied checker is
credited for a separate ordinary assessment of that candidate. Their
agreement supplies no additional premise: (ZG.23)–(ZG.48) give the complete
argument used by this author. Current CG21–25 were also checked for overlap
in this exposition; the new contribution is not their already established
dimension or all-input branch-mass necessity.

**Convention 10.2 (literature state and verification boundary).** The
literature state of the new quantitative deduction is `repo-derived`:
Lemmas 7.1–7.3, the zero-transfer application of Lemma 8.1, Theorem 8.2
and its two performance corollaries are established here from the credited
data and the supplied proposal. Standard Kraus/Choi positivity, the Schur
characterization, finite-dimensional spectral and Schur-complement facts,
trace-norm/effect comparison and elementary differentiation are mature tools.

The current source attributes these tools, within their exact scopes, to
de Vicente–Streltsov for genuine-coherence/Schur operations,
Heinosaari–Jivulescu–Reeb–Wolf for finite quantum-operation extension,
Nechita–Park for sign-covariant maps with transfer and reverse coherence,
and Terhal–Horodecki, Chruściński–Kossakowski and Sekatski for
Schmidt-number/bottleneck facts. Those are SOURCE-REPORTED literature
attributions; no external text was consulted or independently authenticated
for this volume. No `suspected-novel` or worldwide-priority assertion is
made. External originality has not been assessed.

The new proof is symbolic ordinary analysis. No new numerical evaluation,
enumeration, experiment, SDP, CAS, mathematical test, build, ingestion or
kernel verification establishes its claims. Raw source seals establish
identity only; the precise credited mathematical premises are in §5, and
the complete new deduction is in §§6–8. If one of those premises fails,
the claimed additive gap above the original optimum is not established by
this volume. In particular, without (ZG.22) the argument supplies the
conditional lower witness above $F(x_\star)$, not a claimed comparison with
an independently known optimum.

**Boundary 10.3 (the remaining native obligation).** The original task,
specimen, common metadata, legal histories, full coherent successors, all
five labelled exact-time laws, first-failure absorption and every exceptional
outcome remain unchanged. No source prior, helper, callback, extra
observation, postselection, retry or changed information port has been
introduced. The perturbed witness is positive on the exact zero-transfer
live support; it is not a higher lower bound for unrestricted transfer
channels, whose benchmark remains (ZG.22).

Native acquisition, storage and actuation still need an actually supplied
joint encoder/decoder implementation within the original permissions. In
particular the diagonal instrument and record-controlled swaps of CG20,
the calibrated support decomposition, access to and retention of the joint
payload of CG21, and a physical absorbing event at the required elapsed time
with terminal live output at time $1$ are separate services. A geometric
path, source-indexed $K_x$, Kraus decomposition, algebraic flag or sampled
timestamp does not supply them. The original probability-changing,
noncommuting native geometry does not classify the full callable menu as
Schur. Neither Corollary 9.1 nor the joint dimension statements prove such
a classification.

No numerical size, sharp loss constant, restricted optimizer, useful
conditioning bound, finite exact-event storage, physical realization or
efficiency theorem is asserted. There is no full-channel uniqueness claim,
general neural-network or empirical-learning conclusion, kernel claim,
unconditional-prefix optimum, global native impossibility or completion of
the broader programme. Within the exact credited scope no additional failed
step in the explicit gap deduction is identified; final independent review
and the original resource/interface obligations remain separate.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md

## 追加锚（本行以下为增补区）
