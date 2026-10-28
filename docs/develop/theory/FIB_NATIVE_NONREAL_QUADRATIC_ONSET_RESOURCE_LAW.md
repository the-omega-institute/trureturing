# A sharp quadratic resource onset for native nonreal inputs

> The results below are ordinary conditional mathematics. The calibrated
> experiment, isolated algebraic coefficient source, arithmetic certificates
> and minimax identification are inherited premises. For each fixed admitted
> genuinely nonreal input, this companion evaluates the right onset beyond
> its maximal initial plateau, with a lower bound for the full finite
> acquisition class and an actual twelve-label matching instrument. It does
> not evaluate the entire later curve or enact the required native operations.
> The volume uses the generic-v1 append convention.

## 1. The original specimen, histories and complete-output task

**Definition 1.1 (calibrated paths and the old cut).** For
$b=(X,Y,Z)$ let $0<Z<1$, $r_b=1-Z$ and $0<X,Y<r_b$. Define

$$
\begin{aligned}
J_b&=(\max(0,X+Y-r_b),\min(X,Y)),\\
\pi_b(k)&=(r_b-X-Y+k,X-k,Z,Y-k,k),\\
\mathbf d&=(1,-1,0,-1,1),\qquad
I_b(k)=\sum_{i\in\{0,1,3,4\}}\pi_b(k)_i^{-1},\\
w_b(k)_i&=\mathbf d_i/(\pi_b(k)_iI_b(k)).
\end{aligned}
\tag{QO.1}
$$

The conditional original control contract requires a finite duration
$T\geq0$, continuous real coordinates $k,\vartheta$, strict
$k(t)\in J_b$, finite phase variation, and either absolute continuity
of both coordinates or a finite piecewise-$C^1$ presentation with rates
continuous on each closed piece. Its live lift has components

$$
\sqrt{\pi_b(k(t))_i}\exp\left(-i\left[\theta_i+
 \int_0^t w_b(k(v))_i\vartheta'(v)\,dv\right]\right).
\tag{QO.2}
$$

Signed real phase lifts, integer winding and chronological composition
are literal data. Zero duration allows only zero matching displacement.
Known denial or mismatch remains an unexecuted rejection with its
controller update. These path conditions do not construct an actuator
on an unknown quantum input.

Here $b=(1/4,1/4,1/2)$ and
$\pi_b(k)=(k,1/4-k,1/2,1/4-k,k)$. Five-mode indices are
$0,1,2,3,4$, with mode $4$ retaining its original name mode $13$.
Set

$$
E=\left((e_0+e_4)/\sqrt2,(e_1+e_3)/\sqrt2,e_2\right),\qquad
P_5=EE^\dagger,\quad Q_5=I_5-P_5,\quad V=\operatorname{ran}E.
\tag{QO.3}
$$

Supported coordinates $0,1,2$ refer to $(+,-,2)$, without renaming
the stopped labels. The original catalogue has $y\in\{5,16,27\}$,
$x=y/256$, $\beta_{\rm hist}\in\{0,\pi\}$ and $m\in\{0,1\}$.
Starting from the common height $1/8$ and zero phase, its six unit
legs use $B_{\rm hist}=8\beta_{\rm hist}-4\pi m$:

| Leg | Height | Real phase lift |
| --- | --- | --- |
| 1 | $1/8$ | $0\to2\pi m$ |
| 2 | $1/8\to1/16$ | $2\pi m$ |
| 3 | $1/16$ | $2\pi m\to2\pi m+B_{\rm hist}$ |
| 4 | $1/16\to1/8$ | $2\pi m+B_{\rm hist}$ |
| 5 | $1/8$ | $2\pi m+B_{\rm hist}\to2\pi m$ |
| 6 | $1/8\to x$ | $2\pi m$ |

Indeed $w_b(1/8)=(1/4,-1/4,0,-1/4,1/4)$ and
$w_b(1/16)-w_b(1/8)=(1/8,1/8,0,1/8,1/8)$.
The residual phases are
$(\beta_{\rm hist},\beta_{\rm hist}-\pi m,0,
\beta_{\rm hist}-\pi m,\beta_{\rm hist})$.
The earlier reach masses $32/177,2/9,32/111$ are not source priors
or weights in the present resource.

At absolute time six, one already reached normalized sole specimen is
received. The common continuation keeps the phase fixed and uses
$k(t)=x+6t/256$, $0\leq t\leq1$, on the strict common relative domain
$(0,58/256)$. Terminal heights are $11/256,22/256,33/256$.
For a relative increment $A(t)$ and original height interval
$(\ell_b,u_b)$, legal starting heights form
$(\ell_b-\min A,u_b-\max A)$; this is not a domain sensor.
The six-leg paths have populations at least $5/256$, height speed
at most $27/256$, phase speed at most $8\pi$ and total phase variation
at most $16\pi$. No limiting wall or infinite winding is used.

**Definition 1.2 (all twelve inputs and their targets).** Put

$$
\begin{aligned}
p_y&=(y/128,(64-y)/128,1/2),& a_y&=(\sqrt{p_{yi}})_i,\\
U_{e,n}&=\operatorname{diag}(e,n,1),&
\rho_{y,e,n}&=U_{e,n}a_ya_y^TU_{e,n}^\dagger,\\
d_y&=\left(\frac y{128},\frac{y(58-y)}{128(y+6)},
                         \frac y{2(y+6)}\right),&
B_y^{\rm tar}&=(\sqrt{d_{yi}d_{yj}})_{ij},\\
s_y&=y/(y+6),& f_y(t)&=6y/(y+6t)^2,\\
w&=(0,1/4,1/2,1/4,0),&P_f&=|f\rangle\langle f|.
\end{aligned}
\tag{QO.4}
$$

The independent signs satisfy $e=(-1)^{\beta_{\rm hist}/\pi}$,
$n=e(-1)^m$, and $en=(-1)^m$. The physical input is
$E\rho_{y,e,n}E^\dagger$. Its ideal live block is
$EU_{e,n}B_y^{\rm tar}U_{e,n}^\dagger E^\dagger$, and its ideal
failure measure in each original label $j$ is $w_jf_y(t)dt\,P_f$.
Labels $1$ and $3$ remain distinct; labels $0$ and mode $13$ remain
named zero measures. The live trace is $s_y$ and
$\int_0^1 f_y=1-s_y$.

The source-indexed ideal instrument uses $d_{\rm ramp}=6/256$,
$c_{\rm wall}=1/4$ and

$$
\begin{aligned}
K_x^{\rm tar}&=\operatorname{diag}\left(1,
 \sqrt{\frac{x(c_{\rm wall}-x-d_{\rm ramp})}
 {(x+d_{\rm ramp})(c_{\rm wall}-x)}},
 \sqrt{\frac{x}{x+d_{\rm ramp}}}\right),\\
\mathcal I_{x,2}(dt)(A)&=
 \frac{d_{\rm ramp}x}{(x+d_{\rm ramp}t)^2}
 |f\rangle\langle2|A|2\rangle\langle f|\,dt,\\
\mathcal I_{x,j}(dt)(A)&=
 \frac{c_{\rm wall}}{2(c_{\rm wall}-x)}
 \frac{d_{\rm ramp}x}{(x+d_{\rm ramp}t)^2}
 |f\rangle\langle1|A|1\rangle\langle f|\,dt\quad(j=1,3),\\
\mathcal I_{x,0}&=\mathcal I_{x,4}=0 .
\end{aligned}
\tag{QO.5}
$$

Writing this target family does not install the unknown $x$ in a
common processor. Available metadata and blanks have one common fixed
state: no-failure flag, aligned clock, source/preparation/epoch,
calibration, permissions and controller state. There is no readable
old height, phase, waveform, generator word, source programme, callback,
environment port or helper specimen. Independent ancillas, coins,
computation and finite adaptive operations can be included in one common
CPTP map on the whole complex algebra.

For complete target $\Omega_{y,e,n}$, the original error remains

$$
E(\Phi)=\max_{y,e,n}\frac12
 \|\Omega_{y,e,n}-\Phi(E\rho_{y,e,n}E^\dagger)\|_{1,\rm cq}.
\tag{QO.6}
$$

This is HALF the full cq norm on all twelve constraints. It counts
every live coherence, each separately labelled exact-time measure,
singular or atomic additions, wrong support, abort, rejection and all
extra sectors, including those with zero ideal weight. A common
dominating measure defines the matrix-valued measure norm without bins.
First executed failure is absorbing, with no later positive-carrier
action, copy, reset, retry, reversal or replacement. Old stopped
archives and controller updates remain in their original branches.
Elapsed $t$ means absolute time $6+t$, and live output occurs at elapsed
one. No outcome is deleted and no mass is divided by survival or acceptance.

## 2. Exact conditional coefficient dictionary and fixed channel

**Definition 2.1 (the inherited algebraic point).** To make the source
unambiguous, use coordinates
$\mathbf x=(\lambda_{\rm src},\alpha_1,\alpha_2,\beta_1,\beta_2,z_{\rm src})$
and $\eta=(\eta_0,\eta_1,\eta_2)$. They are unrelated to the history
phase and to $\alpha,\beta$ used below. Define

$$
\begin{aligned}
v_5&=(\alpha_1,\alpha_2,-1)^T,&
v_{27}&=(\beta_1,\beta_2,1)^T,\\
A_5^{\rm src}&=\lambda_{\rm src}v_5v_5^T/\|v_5\|^2,&
A_{27}^{\rm src}&=(1-\lambda_{\rm src})v_{27}v_{27}^T/\|v_{27}\|^2,\\
\zeta&=(z_{\rm src},59\lambda_{\rm src}/128,\lambda_{\rm src}/2),&
N^{\rm src}&=\sum_{y=5,27}A_y^{\rm src}\odot a_ya_y^T,\\
S_0^{\rm src}&=\operatorname{diag}\zeta-N^{\rm src},\\
S_{ij}^{\rm src}&=\begin{pmatrix}
\zeta_j-\sum_y(A_y^{\rm src})_{ii}p_{yj}&-N_{ij}^{\rm src}\\
-N_{ij}^{\rm src}&\zeta_i-\sum_y(A_y^{\rm src})_{jj}p_{yi}
\end{pmatrix}\quad(i<j),\\
F^{\rm src}&=\sum_{y=5,27}\operatorname{tr}(A_y^{\rm src}B_y^{\rm tar})
             -\sum_i\zeta_i+6\lambda_{\rm src}/11,\\
g^{\rm src}&=(1000\det S_0^{\rm src},\det S_{01}^{\rm src},
                                      \det S_{02}^{\rm src}),\\
\Psi(\mathbf x,\eta)&=
 (\nabla_{\mathbf x}(F^{\rm src}+\eta\cdot g^{\rm src}),g^{\rm src}).
\end{aligned}
\tag{QO.7}
$$

The named source premise is the unique zero of $\Psi$ in the
radius-$10^{-24}$ product box around these exact rational centres:

| Coordinate | Rational centre |
| --- | --- |
| $\lambda_{\rm src}$ | $0.479508042205945691075728241615$ |
| $\alpha_1$ | $1.412018697539825943102823246594$ |
| $\alpha_2$ | $1.185897402486986028204155873343$ |
| $\beta_1$ | $0.413330945620125544606320492846$ |
| $\beta_2$ | $0.809647491041060318009094562763$ |
| $z_{\rm src}$ | $0.066998926272600209516864472757$ |
| $\eta_0$ | $0.279795267654829218213193898783$ |
| $\eta_1$ | $0.199570407911600478528148253443$ |
| $\eta_2$ | $0.091392615490799158339482855657$ |

All source expressions are evaluated at that zero, not at its centre.
With adjugate meaning transposed cofactor matrix, set

$$
\begin{aligned}
H^{\rm src}&=1000\eta_0\operatorname{adj}S_0^{\rm src},&
Q^{01}&=\eta_1\operatorname{adj}S_{01}^{\rm src},&
Q^{02}&=\eta_2\operatorname{adj}S_{02}^{\rm src},\\
(h_0,h_1,h_2)^T&=H^{\rm src}e_0/\sqrt{H^{\rm src}_{00}},&
(a,b)^T&=Q^{01}e_0/\sqrt{Q^{01}_{00}},&
(c,d)^T&=Q^{02}e_0/\sqrt{Q^{02}_{00}},\\
m_1&=1-H^{\rm src}_{11}-Q^{01}_{00},&
m_2&=1-H^{\rm src}_{22}-Q^{02}_{00},\\
D&=\operatorname{diag}(h_0,h_1,h_2),&
T&=a|0\rangle\langle1|+b|1\rangle\langle0|,&
S&=c|0\rangle\langle2|+d|2\rangle\langle0|,\\
M&=\operatorname{diag}(0,m_1,m_2),&
\kappa&=h_0a+h_1b .
\end{aligned}
\tag{QO.8}
$$

The source rank-one factors and enclosures, credited to CG, JR and RG,
give

$$
\begin{gathered}
h_i,a,b,c,d,m_1,m_2>0,\qquad0<\kappa<1/4,\\
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\\
.968<h_0^2<.970,\quad .498<h_1^2<.500,\quad .655<h_2^2<.656,\\
h_0h_1>.695,\quad h_0h_2>.796,\quad
a^2+b^2+c^2+d^2<.036,\quad
(S_{01}^{\rm src})_{00},(S_{02}^{\rm src})_{00}>.1 .
\end{gathered}
\tag{QO.9}
$$

Finite decimals in inequalities denote rationals. Put

$$
\alpha=\frac{ab}{h_0h_1},\quad \beta=\frac{cd}{h_0h_2},\quad
\ell=\alpha+\beta,\qquad k=1-\ell .
\tag{QO.10}
$$

The combined square bound and $2ab+2cd\leq a^2+b^2+c^2+d^2$
give $0<\ell<18/695<1/36$. Thus $\alpha,\beta,k$ are positive,
and $\alpha,\beta<1$. This implication does not recertify the isolated
point, bordered Jacobian or enclosures.

**Definition 2.2 (the entire channel held fixed).** For any complex
$A\in M_5$ write $A_V=E^\dagger AE$ and $g(t)=2/(1+t)^2$.
The particular channel is

$$
\begin{aligned}
\Phi_*^L(A)&=E(DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger)E^\dagger,\\
\Phi_{*,j}^f(A)(dt)&=
 g(t)\left[w_j\operatorname{tr}(MA_V)
       +\mathbf1_{j=2}\operatorname{tr}(Q_5A)\right]dt\,P_f .
\end{aligned}
\tag{QO.11}
$$

Cross-support maps, complement live output and every additional sector
are zero. Its identities are identities of complex maps, amplified by
identity on any passive reference and evaluated on each labelled Borel
time set. Common fixed metadata are carried identically. Equation
(QO.9) and $\int_0^1g=1$ give TP. The inherited minimax identification
is

$$
E_* =F^{\rm src}(\mathbf x_*)\in
(0.14817810291080132013,0.14817810291080132014).
\tag{QO.12}
$$

Every upper instrument below forgets to (QO.11), so this credited error
is retained. Neither a fresh certificate nor whole-channel uniqueness
among original error optimizers is asserted.

## 3. Full acquisition class and universal coefficient necessity

**Definition 3.1 (actual acquired mass).** For $s\in[0,1]$ prescribe
on every five-mode input the binary effects

$$
F_r(s)=\frac{I_5+r s\kappa EX_{01}E^\dagger}{2},\qquad
X_{01}=|0\rangle\langle1|+|1\rangle\langle0|,\qquad r=\pm1 .
\tag{QO.13}
$$

A competitor has any finite actually generated accessible classical
alphabet $\Xi$, report function $r(\xi)$, finite joint fibre dimensions
$d_\xi\geq1$, common CP encoders $\mathcal C_\xi:M_5\to M_{d_\xi}$
and common full-output CPTP decoders $\mathcal R_\xi$, satisfying

$$
\sum_\xi\mathcal C_\xi^\dagger(I)=I_5,\quad
\sum_{\xi:r(\xi)=r}\mathcal C_\xi^\dagger(I)=F_r(s),\quad
\sum_\xi\mathcal R_\xi\mathcal C_\xi=\Phi_* .
\tag{QO.14}
$$

Independent report coins can be absorbed into generated labels.
The whole future-accessible input-dependent quantum system is counted
jointly: specimen, memory, quantum controller, accessible environment,
returned systems and entanglement shares. A coherent flag counts as
quantum until an actual classical direct sum is generated. Other dilation
systems are permanently inaccessible before the cut. Passive references
are inaccessible to execution. There is no prior, sensor, readable
history, helper, bypass, hidden share, extra specimen or postselection.
Every decoder is TP on its entire carrier; its live restriction is
only TNI.

Define

$$
G_{\rm acq}=\sum_{\xi:d_\xi\geq3}\mathcal C_\xi^\dagger(I),\qquad
E_s(\sigma)=\inf_{\text{(QO.14)}}\operatorname{tr}(G_{\rm acq}\sigma).
\tag{QO.15}
$$

This is unnormalized acquired mass, including high acquisition later
failing. For supported $\rho$ abbreviate
$E_s(\rho)=E_s(E\rho E^\dagger)$. A public selected test input and
strength may determine the fixed instrument before execution; that
instrument is still common on all unknown inputs. Separate selected
minima are not a common all-input minimizer. The lower arguments impose
no real, covariant, isometric, pure, wholly-live, JR-conditioned or
chosen-failure restriction.

**Lemma 3.2 (coefficient conventions and complete rank-two locus).**
In order $(D,T,S)$ define

$$
\begin{aligned}
K(z)&=uD+vT+wS,\quad z=(u,v,w)^T,\quad (K_D,K_T,K_S)=(D,T,S),\\
B_0&=\operatorname{diag}(1,-\alpha,-\beta),\quad
X_c=|D\rangle\langle T|+|T\rangle\langle D|,\\
\Theta(Z)&=\sum_{i,j}Z_{ij}K_j^\dagger K_i,\qquad
C(\rho)_{ij}=\operatorname{tr}(K_i^\dagger K_j\rho),\\
\mathcal Z&=\{u=0\}\cup\{u^2-\alpha v^2-\beta w^2=0\},\\
\mathcal C_2&=\left\{\sum_{j=1}^N z_jz_j^\dagger:
                      z_j\in\mathcal Z,\ N<\infty\right\}.
\end{aligned}
\tag{QO.16}
$$

Zero sums are allowed. Then
$z^\dagger C(\rho)z=\operatorname{tr}(K(z)^\dagger K(z)\rho)$ and
$\operatorname{tr}(CZ)=\operatorname{tr}(\Theta(Z)\rho)$.
For unnormalized output-input Choi columns
$\mathcal V=(|D\rangle\!\rangle,|T\rangle\!\rangle,|S\rangle\!\rangle)$,
the coefficient Choi is $\mathcal VZ\mathcal V^\dagger$ and its output
partial trace is $\Theta(Z)^T$. Every nonzero singular $K(z)$ has
rank exactly two, and (QO.16) contains its entire complex locus.

Proof. Expansion of traces gives the stated index convention; output
partial trace of $|K_i\rangle\!\rangle\langle\!\langle K_j|$ is
$(K_j^\dagger K_i)^T$. Direct determinant expansion gives

$$
K(z)=\begin{pmatrix}h_0u&av&cw\\bv&h_1u&0\\dw&0&h_2u\end{pmatrix},
\qquad
\det K(z)=h_0h_1h_2u(u^2-\alpha v^2-\beta w^2).
\tag{QO.17}
$$

When $u\ne0$, the rows/columns $1,2$ minor is $h_1h_2u^2\ne0$.
When $u=0,z\ne0$, column zero is nonzero in rows one/two and some
other column is nonzero in row zero. They are independent. This proves
the rank statement on both components and their intersection, including
all phases. $\square$

**Proposition 3.3 (necessity before any normalization of arrays).**
Every original finite competitor has $H_r\succeq0$, $L_r\in\mathcal C_2$
such that, with $Z_r=H_r+L_r$ and $H=H_++H_-$,

$$
\begin{gathered}
Z_++Z_-=I_3,\qquad0\preceq H\preceq I_3,\\
N=(I_3+s\kappa X_{01})/2-\Theta(Z_+),\qquad0\preceq N\preceq M,\\
\operatorname{Re}(Z_+)_{DT}=s/2,\qquad
G_{\rm acq}\succeq E\Theta(H)E^\dagger .
\end{gathered}
\tag{QO.18}
$$

Its supported-live high cost is $\operatorname{tr}(CH)$.

Proof. Multiply each encoder Kraus matrix by each supported-live decoder
Kraus matrix. Their positive Choi projectors sum to the live Choi of
(QO.11). A vector in the kernel of that sum has zero squared pairing
with every product, so each product lies in its three-column support
and equals $EK(z)E^\dagger$. In particular it kills complement and
cross-support inputs. The embedded columns are independent. Apply
their Gram left inverse
$(\mathcal W^\dagger\mathcal W)^{-1}\mathcal W^\dagger$ on both sides
of the Choi identity to obtain $\sum zz^\dagger=I_3$. Their norms
have not been set to one.

Group these same products by actual report and actual fibre dimension.
Products through dimension at most two have rank at most two and hence
belong to $\mathcal Z$; they yield $L_r$. The rest yield $H_r$.
This Kraus refinement is analytic and does not create an accessible
record of an old discarded environment. The plus supported failure
effect is $N$, the minus effect is $M-N$. Both are positive. Since
$M$ kills coordinate zero, positive two-by-two minor bounds force both
of their first rows and columns to vanish. For Hermitian $Z$,

$$
\Theta(Z)_{01}=h_1bZ_{DT}+h_0a\overline{Z_{DT}}.
\tag{QO.19}
$$

Its real part is $\kappa\operatorname{Re}Z_{DT}$, proving the record
condition. No conditioned live or failure measure has been fixed here.

For each high branch, the full TP decoder has live adjoint identity
at most its whole identity. Pull this inequality back through its
encoder and sum. This proves the full five-mode operator inequality
in (QO.18), including acquired-to-failure loss and all complement or
cross-support contributions. Evaluation on any positive input gives
the required acquired lower bound without acceptance normalization.
$\square$

## 4. The admitted nonreal physical continuum

**Lemma 4.1 (strict source sign).** The conditional source implies
$\chi=h_1b-h_0a>0$.

Proof. The source box gives
$.479<\lambda_{\rm src}<.480$,
$1.412<\alpha_1<1.413$, $1.185<\alpha_2<1.186$,
$.413<\beta_1<.414$, $.809<\beta_2<.810$.
Positive multiplication gives
$4.39<1+\alpha_1^2+\alpha_2^2<4.41$,
$1.82<1+\beta_1^2+\beta_2^2<1.83$,
$(A_5^{\rm src})_{01}<.185$ and
$(A_{27}^{\rm src})_{01}<.097$. Therefore

$$
N_{01}^{\rm src}
=\frac{(A_5^{\rm src})_{01}\sqrt{295}
       +(A_{27}^{\rm src})_{01}\sqrt{999}}{128}<.051,
\tag{QO.20}
$$

using $\sqrt{295}<18$ and $\sqrt{999}<32$.
The rank-one adjugate gives
$a/b=N_{01}^{\rm src}/(S_{01}^{\rm src})_{00}<.51$.
Also $(h_1/h_0)^2>498/970>(7/10)^2$.
Thus $h_0a/(h_1b)<(51/100)/(7/10)<1$.
Only rational implications of the inherited source were used. $\square$

**Definition 4.2 (public state and admission).** Choose $\tau_i>0$ with
$\sum_i\tau_i=1$, and set
$A=\sum_i h_i^2\tau_i$, $B=b^2\tau_0+a^2\tau_1$,
$C_S=d^2\tau_0+c^2\tau_2$. For $0<\xi<1$ put

$$
\begin{aligned}
\theta_0&=2\arctan\xi,&
c_0&=\frac{1-\xi^2}{1+\xi^2},&
\sigma_0&=\frac{2\xi}{1+\xi^2},\\
\delta_0&=1-\alpha-\beta c_0,&
Z_0&=\sqrt{\delta_0^2+\beta^2\sigma_0^2},\\
p&=(Z_0+\delta_0)/2,&
q&=(Z_0-\delta_0)/(2\alpha),&
r_0&=\beta\sigma_0/(2\sqrt\alpha),\\
k_{\rm tilt}&=(1-\alpha)c_0-\beta,&
\lambda&=\frac{Ap-Bq}{c_0Z_0},&
d_{\rm cert}&=B+\lambda\alpha c_0,\\
\gamma&=\lambda\sqrt\alpha\,\sigma_0+d_{\rm cert}\sqrt{q/p}.
\end{aligned}
\tag{QO.21}
$$

Admission is exactly

$$
p+q<1,\quad k_{\rm tilt}>0,\quad Ap>Bq,\quad
\gamma<\chi\sqrt{\tau_0\tau_1}.
\tag{QO.22}
$$

For admitted parameters define

$$
\rho=\begin{pmatrix}\tau_0&i\gamma/\chi&0\\
-i\gamma/\chi&\tau_1&0\\0&0&\tau_2\end{pmatrix},\qquad
C=\begin{pmatrix}A&i\gamma&0\\-i\gamma&B&0\\0&0&C_S\end{pmatrix},
\quad h=(\sqrt p,i\sqrt q,0)^T,
\quad H_*=hh^\dagger,\quad s_*=\sqrt{1-p-q},\quad F=\lambda k_{\rm tilt}.
\tag{QO.23}
$$

The coefficient vector $h$ is distinct from the source amplitudes $h_i$.

**Proposition 4.3 (nonemptiness, positive margins and algebraicity).**
These are normalized positive definite physical states with
$C=C(\rho)>0$ genuinely nonreal. For every positive $\tau$ there is
an explicit admitted interval. Namely

$$
\begin{aligned}
T_0&=2\beta+\frac{\beta^2(1+\alpha)}{\alpha k},&
G_0&=4A\sqrt\alpha+
       \frac{\beta(B+2\alpha A)}{\sqrt\alpha k},\\
\xi_0&=\min\left\{\frac14,\sqrt{\frac{\ell}{2T_0}},
 \sqrt{\frac{k}{4(1-\alpha)}},
 \sqrt{\frac{A\alpha k^2}{2B\beta^2}},
 \frac{\chi\sqrt{\tau_0\tau_1}}{2G_0}\right\}>0 .
\end{aligned}
\tag{QO.24}
$$

Every $0<\xi\leq\xi_0$ is admitted. For every admitted $\xi$,
$p>k$, $q>0$, $pq=r_0^2$, and $0<s_*<\sqrt\ell$.

Proof. From (QO.21),
$p-\alpha q=\delta_0=k+\beta(1-c_0)\geq k$ and $pq=r_0^2>0$.
All defining radicals and denominators are positive. Admission makes
$\lambda,d_{\rm cert},\gamma$ positive. The leading state determinant
is $\tau_0\tau_1-(\gamma/\chi)^2>0$, so $\rho>0$ with trace one.
Multiplication gives
$C_{DT}=h_0a\rho_{10}+h_1b\rho_{01}=i\gamma$;
the other off-diagonal entries vanish. Independence of $D,T,S$ and
$\rho>0$ imply $\operatorname{tr}(K(z)^\dagger K(z)\rho)>0$
for nonzero $z$, so $C>0$.

For $0<\xi\leq\xi_0$ one has $c_0>1/2$, $\sigma_0\leq2\xi$,
$1-c_0\leq2\xi^2$, $p\geq k$ and
$q=r_0^2/p\leq\beta^2\xi^2/(\alpha k)$. Consequently

$$
p+q\leq k+T_0\xi^2\leq1-\ell/2,\qquad
k_{\rm tilt}\geq k/2,\qquad Ap-Bq\geq Ak/2.
\tag{QO.25}
$$

Moreover $\lambda\leq A/c_0\leq2A$ and
$\sqrt{q/p}\leq\beta\xi/(\sqrt\alpha k)$.
Thus $\gamma\leq G_0\xi\leq\chi\sqrt{\tau_0\tau_1}/2$.
Each required inequality is strict even at $\xi_0$.
The choice $\tau=(1/3,1/3,1/3)$, $\xi=\xi_0/2$ is a concrete
member without a search. Algebraic $\tau,\xi$ give algebraic matrices
and constants; angles are only auxiliary coordinates.
Finally $p+q=\delta_0+(1+\alpha)q>k$, giving the endpoint bounds.
$\square$

## 5. The inherited plateau geometry, with the needed proof

**Lemma 5.1 (tilted dual on both complex components).** For
$\cos\theta\geq0$ let

$$
B_\theta=\begin{pmatrix}
\cos\theta&i\sqrt\alpha\sin\theta&0\\
-i\sqrt\alpha\sin\theta&-\alpha\cos\theta&0\\0&0&-\beta
\end{pmatrix}.
\tag{QO.26}
$$

Every $L\in\mathcal C_2$ has $\operatorname{tr}(B_\theta L)\leq0$.
At $\theta_0$, $\mathcal S=C-\lambda B_{\theta_0}$ is PSD of rank
two with kernel $\mathbb C h$, and every original competitor obeys
$\operatorname{tr}(G_{\rm acq}E\rho E^\dagger)\geq
\operatorname{tr}(CH)\geq F$. Equality in the latter forces $H=H_*$.

Proof. For a quadratic-null vector put
$x_0=|u|^2-\alpha|v|^2$, $y_0=2\sqrt\alpha\operatorname{Im}(u\bar v)$.
Expansion gives $x_0^2+y_0^2=\beta^2|w|^4$.
Its pairing with $B_\theta$ is
$x_0\cos\theta+y_0\sin\theta-\beta|w|^2\leq0$.
On the whole plane $u=0$ it is
$-\alpha\cos\theta|v|^2-\beta|w|^2\leq0$.
Finite positive sums prove the claim without discarding the plane.

The definitions imply
$A-\lambda c_0=d_{\rm cert}q/p$ and
$\gamma-\lambda\sqrt\alpha\sigma_0=d_{\rm cert}\sqrt{q/p}$.
Hence

$$
\mathcal S=
d_{\rm cert}\begin{pmatrix}q/p&i\sqrt{q/p}&0\\
-i\sqrt{q/p}&1&0\\0&0&0\end{pmatrix}
+(C_S+\lambda\beta)|S\rangle\langle S|.
\tag{QO.27}
$$

This proves its rank and kernel. Since $I-H\in\mathcal C_2$,
$\operatorname{tr}(B_{\theta_0}H)\geq\operatorname{tr}B_{\theta_0}
=k_{\rm tilt}$. Direct multiplication gives
$h^\dagger B_{\theta_0}h=k_{\rm tilt}$, so
$F=\operatorname{tr}(CH_*)=Ap+Bq-2\gamma r_0>0$.
The identity

$$
\operatorname{tr}(CH)-F
=\lambda[\operatorname{tr}(B_{\theta_0}H)-k_{\rm tilt}]
 +\operatorname{tr}(\mathcal S H)
\tag{QO.28}
$$

has nonnegative terms. If both vanish, positivity gives
$\operatorname{ran}H\subseteq\mathbb Ch$, so $H=aH_*$.
The positive $B_{\theta_0}$ pairing fixes $a=1$.
The acquisition inequality is Proposition 3.3. $\square$

**Lemma 5.2 (real null decomposition and complex lift).** A real PSD
matrix $T_0$ of $B_0$ trace zero is a sum of
$\operatorname{rank}T_0$ nonzero real null projectors. Define

$$
R_\theta=\begin{pmatrix}
\cos(\theta/2)&-i\sqrt\alpha\sin(\theta/2)&0\\
-i\sin(\theta/2)/\sqrt\alpha&\cos(\theta/2)&0\\0&0&1
\end{pmatrix}.
\tag{QO.29}
$$

Then $\det R_\theta=1$,
$R_\theta^TB_0R_\theta=B_0$ and
$R_\theta X_cR_\theta^\dagger=X_c$.

Proof. Factor $T_0=YY^T$ with $Y$ injective and rank-many columns.
$Y^TB_0Y$ has trace zero. If a nonzero real symmetric trace-zero
matrix has eigenvalues $a_+>0>a_-$, the unit vector
$(\sqrt{-a_-}e_++\sqrt{a_+}e_-)/\sqrt{a_+-a_-}$ has zero
Rayleigh value. Its orthogonal compression still has trace zero.
Induction, allowing any basis for a zero compression, produces an
orthonormal zero-Rayleigh basis. Multiply by $Y$. This gives all
nonzero null columns and their exact projector sum.

Multiplication of the two-by-two block in (QO.29) proves the three
identities. Under this Hermitian congruence a real DT block
$\left(\begin{smallmatrix}u&v\\v&w\end{smallmatrix}\right)$ retains
its real off-diagonal $v$, its new diagonal difference is
$\cos\theta(u-\alpha w)$, and its imaginary off-diagonal is
$\sin\theta(u-\alpha w)/(2\sqrt\alpha)$. Determinants are unchanged.
These identities will also give the local true-cone decomposition.
$\square$

**Proposition 5.3 (credited exact maximal plateau and endpoint ranks).**
The maximal initial plateau is $E_s(\rho)=F$ on $0\leq s\leq s_*$.
Its upper construction uses fourteen actual labels below $s_*$ and
twelve at $s_*$. The physical high Kraus matrices remain rank THREE
at the endpoint. The high coefficient projector has rank one.
The complete low coefficient block has rank three below the endpoint
and rank two at it; every physical low Kraus matrix has rank two.

Proof of the needed geometry. Let

$$
u_L=\frac{\beta+\sqrt{\beta^2+4\alpha s_*^2}}2,\qquad
v_L=\frac{-\beta+\sqrt{\beta^2+4\alpha s_*^2}}{2\alpha}.
\tag{QO.30}
$$

They are positive, $u_L-\alpha v_L=\beta$, $u_Lv_L=s_*^2$.
The identities of Lemma 5.2 show
$I-H_*=R_{\theta_0}\operatorname{diag}(u_L,v_L,1)R_{\theta_0}^\dagger$:
the imaginary entry is $ir_0$, the diagonal difference is $\beta c_0$,
and the positive diagonal sum is fixed by the determinant and difference.
For $s\leq s_*$ take
$H_r=H_*/2$, $L_r=(I-H_*+r sX_c)/2$.
The inverse congruence of $L_r$ is
$\frac12\left(\begin{smallmatrix}u_L&r s&0\\r s&v_L&0\\0&0&1\end{smallmatrix}\right)$,
real PSD with zero $B_0$ trace. Its DT determinant is
$(s_*^2-s^2)/4$. Lemma 5.2 supplies three null columns below the
endpoint and two at it. After $R_{\theta_0}$ their first coefficients
have nonzero real part, and (QO.17) makes every physical product rank
two. At the endpoint the explicit low vectors are
$R_{\theta_0}(\sqrt{u_L},r\sqrt{v_L},\pm1)^T/2$.
Use fixed range encoders, isometric full decoders, two supported scalar
failure rows and one scalar complement map at each report as specified
in §10. Their coefficient sum is $I$ and failure effect is $M/2$ per
report; the normalization and complete identities proved there apply
also here. Their only high vectors are $h/\sqrt2$ and their cost is $F$.
This gives counts $2(1+3+2+1)=14$ and $2(1+2+2+1)=12$.

For these high vectors, $v/u=i\sqrt{q/p}=ir_0/p$, so
$u^2-\alpha v^2=u^2(1+\alpha r_0^2/p^2)>0$.
Their physical $K$ matrices are invertible, including at $s=s_*$.
No physical high rank loss occurs.

At equality the certificate forces $H=H_*$. Positive report components
of this rank-one aggregate have real DT entry zero. The low aggregate
DT block is
$A_L=\left(\begin{smallmatrix}1-p&ir_0\\-ir_0&1-q\end{smallmatrix}\right)$.
For $0\preceq W\preceq A_L$, maximize
$2\operatorname{Re}W_{DT}$ using the positive spectral part of
$A_L^{1/2}X_{01}A_L^{1/2}$. Its eigenvalues are $\pm s_*$,
so the maximum is $s_*$. The record condition therefore requires
$s\leq s_*$. A limiting equality above the endpoint is excluded by
the compact localization argument in §8, applied at fixed later
strength. Thus the plateau is maximal. Its evaluated value, maximality,
quantitative quartic later lower bound, affine later upper bound and
same-strength scalar-trace separation are inherited NP results;
only the geometry needed for the onset is reconstructed here. $\square$

## 6. Necessary-array averaging and the exact local cone slice

**Proposition 6.1 (analytic averaging with the correct cost direction).**
From every original competitor one obtains necessary arrays of the form

$$
\begin{aligned}
H_r&=\frac12\begin{pmatrix}
P&r t-iR&0\\r t+iR&Q&0\\0&0&0
\end{pmatrix},\\
L_r&=\frac12\begin{pmatrix}
1-P&r(s-t)+iR&0\\r(s-t)-iR&1-Q&0\\0&0&1
\end{pmatrix},\\
W&=AP+BQ-2\gamma R\leq
        \operatorname{tr}(G_{\rm acq}E\rho E^\dagger).
\end{aligned}
\tag{QO.31}
$$

Here $H_r\succeq0$, $L_r\in\mathcal C_2$ and $N_r=M/2$.
With

$$
x=\sqrt{PQ-R^2}\geq0,\qquad
g=(1-P)(1-Q)-R^2=1-P-Q+x^2\geq0,
\tag{QO.32}
$$

the universal record necessity is $s\leq x+\sqrt g$.
These are operations on necessary arrays, not a physical normal form.

Proof. First average under $J_S=\operatorname{diag}(1,1,-1)$ in
coefficient coordinates, induced on specimen coordinates by
$\operatorname{diag}(-1,-1,1)$. It fixes $D,T$, changes the sign of
$S$, and kills DS and TS entries. It preserves $C$, binary effects,
the full singular locus, positivity and failure inequalities.

Then average the arrays with

$$
(H_r,L_r)\longmapsto
(J_T\overline{H_{-r}}J_T,J_T\overline{L_{-r}}J_T),
\qquad J_T=\operatorname{diag}(1,-1,1).
\tag{QO.33}
$$

On specimen coordinates $U_T=\operatorname{diag}(1,-1,1)$ gives
$\Theta(J_T\bar ZJ_T)=U_T\overline{\Theta(Z)}U_T$.
Record reversal compensates $U_TX_{01}U_T=-X_{01}$, and the new
plus failure effect is $U_T\overline{(M-N)}U_T$, still between zero
and $M$. The real polynomial defining $\mathcal Z$ is preserved, as
is the selected objective because $C=J_T\bar C J_T$. The two
involutions commute. Conjugating an array here is an algebraic device;
no conjugation channel on an unknown specimen is invoked.

The total record diagonals now agree between reports, hence are $1/2$
by their sum $I$. For each total record $Z_r$, the vanishing first
failure row and (QO.19) give
$\operatorname{Re}(Z_r)_{DT}=r s/2$ and
$\chi\operatorname{Im}(Z_r)_{DT}=0$. Lemma 4.1 makes the imaginary
entry zero. Thus $Z_r=(I+r sX_c)/2$ and $N_r=M/2$ after averaging.
The high SS diagonal is separated and nonnegative. Move it to
the low S-axis plane atom in each report. This preserves $Z_r$ and
all constraints and decreases the objective by $C_S$ times its
total mass. Together with Proposition 3.3 this proves the cost
inequality in (QO.31). It does not remove acquired-to-failure loss
from the original accounting.

The two averages give precisely the DT entries in (QO.31).
Positive two-by-two determinants imply $|t|\leq x$ and
$|s-t|\leq\sqrt g$. Since $s\geq0$, their triangle inequality yields
$s\leq x+\sqrt g$. This uses only necessary conditions and holds
for every original competitor. $\square$

**Lemma 6.2 (true block-cone membership, including plane slack).**
For a PSD matrix

$$
L=\frac12\begin{pmatrix}U&v+iR&0\\v-iR&V&0\\0&0&1\end{pmatrix},
\qquad d=U-\alpha V>0,\qquad
m=\sqrt{d^2+4\alpha R^2},
\tag{QO.34}
$$

where $v,R$ are real, one has $L\in\mathcal C_2$ if and only if
$m\leq\beta$.

Proof. Choose $\cos\theta=d/m>0$,
$\sin\theta=2\sqrt\alpha R/m$. Lemma 5.1 gives
$0\geq\operatorname{tr}(B_\theta L)=(m-\beta)/2$.
This proves necessity against both components of the complex locus.

Conversely, replace the SS entry inside the bracket by $m/\beta$.
The resulting matrix is PSD because its DT and SS blocks are separated.
Inverse congruence by $R_\theta$ makes the DT block real with
diagonal difference $m$. Indeed, if a block has difference $d$ and
imaginary off-diagonal $R$, this inverse sends their two-vector
$(d,2\sqrt\alpha R)$ to $(m,0)$, and leaves real off-diagonal $v$
unchanged. Its $B_0$ trace is therefore
$(m-\beta(m/\beta))/2=0$. Lemma 5.2 decomposes this real PSD
matrix into finitely many real null projectors. Transform those
vectors by $R_\theta$; bilinear preservation makes them genuine
quadratic-null atoms. Restore the removed SS part as the plane atom
$\frac12(1-m/\beta)|S\rangle\langle S|$. This proves sufficiency.

When $m=\beta$, $v\ne0$ and the DT determinant is zero, the inverse block
has positive diagonals $u_L,v_L$ determined by
$u_L-\alpha v_L=\beta$ and $u_Lv_L=v^2$. For $v\ne0$ the two
vectors
$R_\theta(\sqrt{u_L},\operatorname{sign}(v)\sqrt{v_L},\pm1)^T/2$
give the entire block. The matching path below uses $v>0$.
The transformation is not a full-cone automorphism: it need not send
a plane atom to a singular atom. Only its stated action on quadratic
null vectors was used. Thus this local iff neither substitutes a
scalar trace relaxation for the general complex cone nor eliminates
plane slack globally. $\square$

## 7. Exact local identity and evaluated onset constants

**Definition 7.1 (coordinates at the exposed endpoint).** Work near
$(P,Q,R)=(p,q,r_0)$ in (QO.31). There
$d=(1-P)-\alpha(1-Q)>0$ and $R>0$. Define

$$
m=\sqrt{d^2+4\alpha R^2},\qquad
\eta=\beta-m\geq0,\qquad
\theta=\operatorname{atan2}(2\sqrt\alpha R,d),\qquad
u=\theta-\theta_0 .
\tag{QO.35}
$$

The sign of $\eta$ follows from Lemma 6.2. The positive local branch is

$$
\begin{aligned}
\delta&=1-\alpha-m\cos\theta,\qquad R=\frac{m\sin\theta}{2\sqrt\alpha},\\
Z&=\sqrt{\delta^2+m^2\sin^2\theta+4\alpha x^2},\\
P&=(\delta+Z)/2,\qquad Q=(Z-\delta)/(2\alpha).
\end{aligned}
\tag{QO.36}
$$

It solves $P-\alpha Q=\delta$ and $PQ=R^2+x^2$.
At $(m,\theta,x)=(\beta,\theta_0,0)$ it gives $(p,q,r_0)$.
Choose one sufficiently small closed neighborhood of this point.
All radicals and reciprocals in (QO.36), and $\sqrt g$, are smooth
there, because $p,q,s_*,\beta$ have strict positive margins.
All local constants below refer to this fixed selected input.

**Lemma 7.2 (exact nonnegative cost identity).** Let
$l_0=\sqrt{q/p}$. In these coordinates,

$$
\begin{aligned}
W-F
&=\lambda[\beta-m\cos u]
  +d_{\rm cert}(l_0^2P+Q-2l_0R)\\
&=\lambda\eta+\lambda m(1-\cos u)
  +\frac{d_{\rm cert}}P\bigl[(l_0P-R)^2+x^2\bigr].
\end{aligned}
\tag{QO.37}
$$

Every term on the last line is nonnegative in the chosen neighborhood.

Proof. The pairing with the old dual is
$\operatorname{tr}(B_{\theta_0}H)-k_{\rm tilt}
=\beta-m\cos(\theta-\theta_0)$, by substituting
$P-\alpha Q=1-\alpha-m\cos\theta$ and
$2\sqrt\alpha R=m\sin\theta$. The other term of (QO.28)
is the DT trace from (QO.27), since the reassigned high SS entry is
zero. Finally $Q=(R^2+x^2)/P$ completes its square. The exact
identity retains radial slack; it is not just a Hessian calculation.
$\square$

**Definition 7.3 (fully evaluated constants).** Set

$$
\begin{aligned}
p_1&=\frac{\beta\sigma_0}{2}
              \left(1+\frac{1-\alpha}{Z_0}\right),\\
q_1&=\frac{\beta\sigma_0}{2\alpha}
              \left(\frac{1-\alpha}{Z_0}-1\right),&
r_1&=\frac{\beta c_0}{2\sqrt\alpha},\\
a_{\rm curv}&=\frac{d_{\rm cert}}p=\frac{\alpha A+B}{Z_0},&
b_{\rm rec}&=-\frac{p_1+q_1}{2s_*},\\
c_{\rm curv}&=\frac{\lambda\beta}{2}
              +a_{\rm curv}(l_0p_1-r_1)^2,\\
D_{\rm onset}&=\frac1{a_{\rm curv}}+\frac{b_{\rm rec}^2}{c_{\rm curv}},&
K_{\rm onset}&=\frac1{D_{\rm onset}}
 =\frac{a_{\rm curv}c_{\rm curv}}
        {c_{\rm curv}+a_{\rm curv}b_{\rm rec}^2}.
\end{aligned}
\tag{QO.38}
$$

**Proposition 7.4 (signs and complete local remainders).** For every
fixed admitted input,
$p_1,q_1,a_{\rm curv},c_{\rm curv},D_{\rm onset}>0$,
$b_{\rm rec}<0$ and $0<K_{\rm onset}<a_{\rm curv}$. Uniformly in
the fixed neighborhood,

$$
\begin{aligned}
W-F={}&\lambda\eta+a_{\rm curv}x^2+c_{\rm curv}u^2\\
 &+O\!\left(\eta^2+\eta|u|+|u|^3+
                  (\eta+|u|)x^2+x^4\right),\\
s-s_* \leq{}&x+b_{\rm rec}u+O(\eta+x^2+u^2).
\end{aligned}
\tag{QO.39}
$$

Proof. At $m=\beta,x=0$ differentiate
$\delta=1-\alpha-\beta\cos\theta$ and
$Z^2=(1-\alpha)^2+\beta^2-2\beta(1-\alpha)\cos\theta$.
They give $\delta'=\beta\sin\theta$ and
$Z'=\beta(1-\alpha)\sin\theta/Z$, hence exactly $p_1,q_1,r_1$.
Also
$d_{\rm cert}Z_0=B(p+\alpha q)+\alpha(Ap-Bq)
=p(B+\alpha A)$, proving the second expression for $a_{\rm curv}$.

Admission gives $\beta<(1-\alpha)c_0$, so
$Z_0^2<(1-\alpha)^2$. Thus $p_1,q_1>0$ and $b_{\rm rec}<0$.
All other positive signs follow from (QO.21), and the nonzero
$b_{\rm rec}$ makes $K_{\rm onset}<a_{\rm curv}$ strict.
These expressions are algebraic when the public parameters and
conditional source are algebraic.

For the remainders, the coordinates are smooth in $\eta,u,x^2$.
Since $l_0p=r_0$,
$l_0P-R=(l_0p_1-r_1)u+O(\eta+u^2+x^2)$.
Insert this in (QO.37), expand $1/P$ about $1/p$ and
$1-\cos u=u^2/2+O(u^4)$. The retained terms are exactly
$\lambda\eta,a_{\rm curv}x^2,c_{\rm curv}u^2$; products of
remaining terms are bounded by the displayed first remainder after
shrinking the neighborhood. In particular even dependence on $x$
prevents an omitted term linear in $x$.

The function $\sqrt{1-P-Q+x^2}$ has base value $s_*$,
angular derivative $-(p_1+q_1)/(2s_*)=b_{\rm rec}$ and zero
$x$ derivative. Taylor's formula and $s\leq x+\sqrt g$ give the
second remainder. Bounded derivatives on the one closed neighborhood
provide common constants for all arrays in it. $\square$

## 8. A lower estimate uniform over the entire original finite class

**Theorem 8.1 (localization and the uniform cubic lower).** For the
fixed admitted input there are finite constants $C_-,\epsilon_->0$
such that every original competitor at $s=s_*+\epsilon$ satisfies

$$
\operatorname{tr}(G_{\rm acq}E\rho E^\dagger)
 \geq F+K_{\rm onset}\epsilon^2-C_-\epsilon^3
 \qquad(0<\epsilon<\epsilon_-).
\tag{QO.40}
$$

The constants do not depend on the competitor, its alphabet or its
fibre dimensions.

Proof. First justify using local coordinates for all designs capable
of a cost improvement. Write their actual cost as $A_{\rm act}$ and
apply Proposition 6.1. The resulting aggregate $H$ lies in the compact
set $0\preceq H\preceq I$ and has $F\leq W\leq A_{\rm act}$.
Every such $H$ satisfies the two nonnegative certificate inequalities
in (QO.28). Suppose a sequence has $W\to F$. A convergent
subsequence of $H$ has a limit satisfying those same continuous
inequalities, with equality. The proof of Lemma 5.1 forces its
limit to be $H_*$. Thus every sequence with $W\to F$ converges to
$H_*$. No closure or attainment of the space of full decoder
measures is being assumed.

For designs with
$A_{\rm act}-F\leq2K_{\rm onset}\epsilon^2$, a compactness
contradiction now puts every normalized array in the same neighborhood
of §7 for all sufficiently small $\epsilon>0$. Otherwise a sequence
outside that neighborhood with $\epsilon\downarrow0$ would have
$W\to F$ and a limit $H_*$ inside it. The same reasoning at a
fixed $s>s_*$ excludes an infimum $F$: the continuous record inequality
would limit to $s\leq s_*$.

Inside the neighborhood, (QO.37), strict $\lambda>0$, bounded positive
$P$ and $m$, and $1-\cos u\geq c u^2$ give

$$
\eta=O(\epsilon^2),\qquad x=O(\epsilon),\qquad
u=O(\epsilon)
\tag{QO.41}
$$

uniformly on the threshold set. For example the $x^2/P$ term controls
$x^2$, and the angular term alone controls $u^2$; no cancellation of
nonnegative summands is used. Substituting (QO.41) in (QO.39) gives

$$
\begin{aligned}
A_{\rm act}-F&\geq
 \lambda\eta+a_{\rm curv}x^2+c_{\rm curv}u^2-C\epsilon^3,\\
x+b_{\rm rec}u&\geq\epsilon-C'\epsilon^2 .
\end{aligned}
\tag{QO.42}
$$

For small positive $\epsilon$ the last right side is positive.
Weighted Cauchy--Schwarz yields

$$
(x+b_{\rm rec}u)^2\leq
D_{\rm onset}(a_{\rm curv}x^2+c_{\rm curv}u^2).
\tag{QO.43}
$$

Consequently (QO.42) is at least
$K_{\rm onset}(\epsilon-C'\epsilon^2)^2-C\epsilon^3$.
This proves (QO.40) on the threshold set with one cubic constant.
Designs above the threshold already have
$A_{\rm act}-F>2K_{\rm onset}\epsilon^2$ and satisfy the same
lower estimate after reducing the radius. These two cases exhaust the
entire original finite class. Taking an infimum preserves (QO.40);
no original minimizer or implemented averaging was required. $\square$

## 9. An exact algebraic matching path

**Definition 9.1 (path constants and selected root).** Define

$$
v_\theta=\frac{b_{\rm rec}}{c_{\rm curv}D_{\rm onset}}<0,\qquad
t_x=\frac1{a_{\rm curv}D_{\rm onset}}>0,\qquad
t_x+b_{\rm rec}v_\theta=1 .
\tag{QO.44}
$$

For $s=s_*+\epsilon$ put

$$
\begin{aligned}
\zeta_\epsilon&=\xi+\frac{1+\xi^2}{2}v_\theta\epsilon,&
c_\epsilon&=\frac{1-\zeta_\epsilon^2}{1+\zeta_\epsilon^2},&
\sigma_\epsilon&=\frac{2\zeta_\epsilon}{1+\zeta_\epsilon^2},\\
\theta_\epsilon&=2\arctan\zeta_\epsilon,&
\delta_\epsilon&=1-\alpha-\beta c_\epsilon,&
R_\epsilon&=\frac{\beta\sigma_\epsilon}{2\sqrt\alpha},\\
a_2&=4\alpha s^2-(1+\alpha)^2,\\
a_1&=2s[2\alpha(1-s^2)+(1-\alpha)\delta_\epsilon],\\
a_0&=\alpha(1-s^2)^2+
 (1-\alpha)\delta_\epsilon(1-s^2)-\delta_\epsilon^2
 -(1+\alpha)^2R_\epsilon^2,\\
x_\epsilon&=\frac{-2a_0}{a_1+\sqrt{a_1^2-4a_2a_0}},&
w_\epsilon&=1-s^2+2s x_\epsilon,\\
P_\epsilon&=\frac{\alpha w_\epsilon+\delta_\epsilon}{1+\alpha},&
Q_\epsilon&=\frac{w_\epsilon-\delta_\epsilon}{1+\alpha},\\
U_\epsilon&=1-P_\epsilon,&V_\epsilon&=1-Q_\epsilon,&
v_\epsilon&=s-x_\epsilon .
\end{aligned}
\tag{QO.45}
$$

The letters $a_i$ here are polynomial coefficients, not source
amplitudes. The actual path uses rational functions and radicals;
the angle is an auxiliary notation.

**Proposition 9.2 (nonempty exact domain and leading slopes).** For
all sufficiently small positive $\epsilon$, (QO.45) is well defined,
with

$$
\begin{gathered}
0<s<1,\quad0<\zeta_\epsilon<1,\quad
(1-\alpha)c_\epsilon-\beta>0,\quad a_1>0,\quad
a_1^2-4a_2a_0>0,\\
0<x_\epsilon<s,\qquad0<P_\epsilon,Q_\epsilon<1,\\
P_\epsilon Q_\epsilon=R_\epsilon^2+x_\epsilon^2,\qquad
U_\epsilon V_\epsilon=R_\epsilon^2+v_\epsilon^2,\\
U_\epsilon-\alpha V_\epsilon=\beta c_\epsilon,\qquad
2\sqrt\alpha R_\epsilon=\beta\sigma_\epsilon,\\
x_\epsilon=t_x\epsilon+O(\epsilon^2),\qquad
\theta_\epsilon-\theta_0=v_\theta\epsilon+O(\epsilon^2).
\end{gathered}
\tag{QO.46}
$$

Proof. Eliminating $P,Q$ from $P+Q=w$,
$P-\alpha Q=\delta$ gives

$$
PQ=\frac{\alpha w^2+(1-\alpha)\delta w-\delta^2}{(1+\alpha)^2}.
\tag{QO.47}
$$

Substitute $w=1-s^2+2sx$ and subtract $R^2+x^2$.
The constant, linear and quadratic numerators are respectively
$a_0,a_1,a_2$. Thus the displayed selected root solves exactly
$PQ=R^2+x^2$. At $\epsilon=0$ one has $a_0=0$, $a_1>0$,
and $a_2<0$; indeed
$a_2=-(1-\alpha)^2-4\alpha(1-s^2)<0$ for $s<1$.
The rationalized root is the continuous root $x=0$, and its
denominator equals $2a_1>0$ at the base.

To check its sign without an extraneous squaring branch, use the smooth
$m=\beta$ coordinates (QO.36) and
$S(\theta,x)=x+\sqrt{1-P(\theta,x)-Q(\theta,x)+x^2}$.
At the base $S=s_*$, $S_x=1$, $S_\theta=b_{\rm rec}$.
The implicit-function theorem produces the unique local solution
$S(\theta_\epsilon,x)=s$ with
$x=(1-b_{\rm rec}v_\theta)\epsilon+O(\epsilon^2)
=t_x\epsilon+O(\epsilon^2)>0$. It solves the polynomial just
derived and agrees with its selected local root. The derivative
of $2\arctan\zeta_\epsilon$ is $v_\theta$ at zero, proving the
angular expansion.

All other strict conditions on the first two lines of (QO.46) follow
from the base margins by continuity; $x_\epsilon>0$ is supplied
by its strictly positive derivative. Hence they define a nonempty
punctured interval, with no numerical radius claimed. Finally the
definition of $w_\epsilon$ gives
$1-P_\epsilon-Q_\epsilon+x_\epsilon^2=(s-x_\epsilon)^2$.
Combine this with $PQ=R^2+x^2$ for the second determinant identity.
Positive diagonals and $0<x_\epsilon<s$ fix every square-root sign.
The difference and imaginary identities follow directly from
(QO.45), so the low radial parameter is exactly $m=\beta$.
$\square$

## 10. Twelve actual labels and the full normalized matching channel

**Definition 10.1 (all acquired branches).** For each $r=\pm1$ put

$$
\begin{aligned}
h_r&=\frac1{\sqrt2}
 \left(\sqrt{P_\epsilon},
       \frac{r x_\epsilon+iR_\epsilon}{\sqrt{P_\epsilon}},0\right)^T,\\
\widehat u_L&=\frac{\beta+\sqrt{\beta^2+4\alpha v_\epsilon^2}}2,\qquad
\widehat v_L=\frac{-\beta+\sqrt{\beta^2+4\alpha v_\epsilon^2}}{2\alpha},\\
z_{r,\pm}&=\frac12R_{\theta_\epsilon}
       (\sqrt{\widehat u_L},r\sqrt{\widehat v_L},\pm1)^T .
\end{aligned}
\tag{QO.48}
$$

For each particular low $z$, let $b_1,b_2$ be specimen columns
one and two of $K(z)$, and fix

$$
q_1=b_1/\|b_1\|,\quad
\widetilde q_2=b_2-q_1(q_1^\dagger b_2),\quad
q_2=\widetilde q_2/\|\widetilde q_2\|,\quad U_z=(q_1,q_2).
\tag{QO.49}
$$

All these matrices are fixed from public constants before the specimen
arrives. For a Kraus matrix $C$, the encoder notation below means
$A\mapsto CAC^\dagger$. Define the scalar supported decoder
$\mathcal R_f$ by
$\mathcal R_{f,j}(z)(dt)=z w_jg(t)dt\,P_f$ for each original $j$,
with zero live and extra output; define $\mathcal R_\perp$ similarly
using only original label $2$ with weight one.

The complete generated acquired alphabet is the following twelve labels:

| Actual label | Entire joint fibre dimension | Encoder | Full decoder |
| --- | --- | --- | --- |
| $(+,H)$ | $3$ | $K(h_+)E^\dagger$ | $X\mapsto EXE^\dagger$ in live |
| $(+,L,+)$ | $2$ | $U_{z_{+,+}}^\dagger K(z_{+,+})E^\dagger$ | $X\mapsto EU_{z_{+,+}}XU_{z_{+,+}}^\dagger E^\dagger$ in live |
| $(+,L,-)$ | $2$ | $U_{z_{+,-}}^\dagger K(z_{+,-})E^\dagger$ | $X\mapsto EU_{z_{+,-}}XU_{z_{+,-}}^\dagger E^\dagger$ in live |
| $(+,f,1)$ | $1$ | $\sqrt{m_1/2}\langle1\rvert E^\dagger$ | $\mathcal R_f$ |
| $(+,f,2)$ | $1$ | $\sqrt{m_2/2}\langle2\rvert E^\dagger$ | $\mathcal R_f$ |
| $(+,\perp)$ | $1$ | $A\mapsto\operatorname{tr}(Q_5A)/2$ | $\mathcal R_\perp$ |
| $(-,H)$ | $3$ | $K(h_-)E^\dagger$ | $X\mapsto EXE^\dagger$ in live |
| $(-,L,+)$ | $2$ | $U_{z_{-,+}}^\dagger K(z_{-,+})E^\dagger$ | $X\mapsto EU_{z_{-,+}}XU_{z_{-,+}}^\dagger E^\dagger$ in live |
| $(-,L,-)$ | $2$ | $U_{z_{-,-}}^\dagger K(z_{-,-})E^\dagger$ | $X\mapsto EU_{z_{-,-}}XU_{z_{-,-}}^\dagger E^\dagger$ in live |
| $(-,f,1)$ | $1$ | $\sqrt{m_1/2}\langle1\rvert E^\dagger$ | $\mathcal R_f$ |
| $(-,f,2)$ | $1$ | $\sqrt{m_2/2}\langle2\rvert E^\dagger$ | $\mathcal R_f$ |
| $(-,\perp)$ | $1$ | $A\mapsto\operatorname{tr}(Q_5A)/2$ | $\mathcal R_\perp$ |

Only the dephased generated label and its stated entire fibre remain
future-accessible. All other input-dependent dilation systems are
discarded permanently before the counted cut. In particular the
complement map can be represented by two fixed orthonormal
$V^\perp$ bra rows divided by $\sqrt2$; their Kraus multiplicity is
discarded, leaving one scalar carrier, not an uncounted coherent
two-dimensional register. No specimen part, controller, memory,
environment or entanglement share is retained outside these fibres.

**Theorem 10.2 (actual ranks, TP, every input, reference and time label).**
Definition 10.1 is a normalized original finite competitor. Every high
physical $K(h_r)$ has rank three, every low physical $K(z_{r,\pm})$
has rank two, and every decoder is TP on its whole fibre. Its actual
high effect is supported on $V$ and has selected cost

$$
W_\epsilon=AP_\epsilon+BQ_\epsilon-2\gamma R_\epsilon .
\tag{QO.50}
$$

It preserves (QO.11) on all complex inputs, at every passive reference,
and on every separate labelled Borel time set, with all zero sectors.

Proof. By (QO.46),

$$
\begin{aligned}
H_r&=h_rh_r^\dagger=
\frac12\begin{pmatrix}
P_\epsilon&r x_\epsilon-iR_\epsilon&0\\
r x_\epsilon+iR_\epsilon&Q_\epsilon&0\\0&0&0
\end{pmatrix},\\
L_r&=\sum_{\pm}z_{r,\pm}z_{r,\pm}^\dagger=
\frac12\begin{pmatrix}
U_\epsilon&r v_\epsilon+iR_\epsilon&0\\
r v_\epsilon-iR_\epsilon&V_\epsilon&0\\0&0&1
\end{pmatrix}.
\end{aligned}
\tag{QO.51}
$$

For the low identity, before congruence the sum is
$\frac12\left(\begin{smallmatrix}
\widehat u_L&r v_\epsilon&0\\r v_\epsilon&\widehat v_L&0\\0&0&1
\end{smallmatrix}\right)$.
Its DT determinant is zero, its diagonal difference is $\beta$,
and $\widehat u_L\widehat v_L=v_\epsilon^2$.
After congruence Lemma 5.2 gives difference $\beta c_\epsilon$,
imaginary entry $iR_\epsilon$ and real entry $r v_\epsilon$.
The positive diagonals with that determinant and difference are
uniquely $U_\epsilon,V_\epsilon$: solving the positive quadratic
for either diagonal proves uniqueness. This proves (QO.51).

Each precongruence low vector is $B_0$ null because
$\widehat u_L-\alpha\widehat v_L=\beta$. Its transformed first
coefficient has real part
$\cos(\theta_\epsilon/2)\sqrt{\widehat u_L}/2>0$.
Thus (QO.17) makes it rank two and its columns one and two independent.
Both denominators in (QO.49) are positive,
$U_z^\dagger U_z=I_2$, and $U_zU_z^\dagger K(z)=K(z)$.
The range decoder is a TP isometry on its entire two-dimensional
fibre, and the encoder-decoder product is $EK(z)E^\dagger$.

For the high vector, the T/D ratio is
$(r x_\epsilon+iR_\epsilon)/P_\epsilon$ with strictly positive
imaginary part. With zero S coefficient, singularity would require
this ratio to be one of the real numbers $\pm1/\sqrt\alpha$.
It is therefore invertible, and the dimension-three live decoder is
TP. This proof includes $\epsilon=0$, where the ratio is
$i r_0/p$: the physical high rank stays three. The two low physical
products stay rank two; their complete low coefficient block in
(QO.51) has rank two because its DT block has rank one and its SS
entry is positive. The high coefficient blocks have rank one.

The scalar decoders are TP on their whole one-dimensional inputs since
$\sum_jw_j=1$ and $\int_0^1g=1$. The sum of coefficient moments at
report $r$ is

$$
H_r+L_r=(I+r sX_c)/2,\qquad
\Theta(I)=I-M,\qquad\Theta(X_c)=\kappa X_{01}.
\tag{QO.52}
$$

Consequently all encoder effects at that report sum to

$$
E[\Theta(H_r+L_r)+M/2]E^\dagger+Q_5/2
=F_r(s).
\tag{QO.53}
$$

Summing reports gives $E[\Theta(I)+M]E^\dagger+Q_5=I_5$.
Each individual effect is positive and bounded by this sum, so each
encoder is TNI and the total instrument TP. This includes all scalar
failure and complement branches; no live-only normalization was used.

The total decoded live coefficient moment is $I_3$. Expanding its
Kraus sum therefore gives exactly the D,T,S live map in (QO.11) on
every complex matrix, including imaginary matrix units. The supported
scalar rows sum to $M/2$ at each report, and the complement effect is
$Q_5/2$. Their decoded measures give each original label its
specified failure measure. Supported rows precompose $E^\dagger$;
the complement scalar trace kills cross-support entries. Thus all
$V$--$V^\perp$ cross operators, complement live maps and every
extra-sector map vanish. There are no endpoint atoms or singular
time additions. Labels $1$ and $3$ stay separate, and labels $0$
and mode $13$ remain named zero measures.

For completeness let $X$ be any joint complex operator with passive
reference $\mathcal H_R$. The scalar row sums produce the conditional
reference operators

$$
R_{f,r}(X)=\operatorname{Tr}_5[(E(M/2)E^\dagger\otimes I_R)X],
\qquad
R_{\perp,r}(X)=\tfrac12\operatorname{Tr}_5[(Q_5\otimes I_R)X].
\tag{QO.54}
$$

In each original label $j$ and every Borel set $B_{\rm time}$,
the record-$r$ output is

$$
P_f\otimes
[w_jR_{f,r}(X)+\mathbf1_{j=2}R_{\perp,r}(X)]
 \int_{B_{\rm time}}g(t)\,dt .
\tag{QO.55}
$$

These are the Kraus-row conditional operators, not an unconditional
reference marginal. Summing reports gives the reference amplification
of (QO.11). The live Kraus identity tensors with $I_R$ as well.
Finite matrix identities give every finite amplification; trace-class
infinite-reference versions follow by finite-rank approximation.
This proves all complex, reference, separate-time and zero-sector
identities simultaneously. Fixed common metadata stay identical.

Finally only the two high branches have dimension at least three.
Their whole decoders are live, so their actual acquired effect is
$E\Theta(H_++H_-)E^\dagger$, giving (QO.50).
This equality belongs to this construction. The universal lower
continued to allow high acquisition followed by failure. Every one
of the twelve encoders is nonzero on its full input algebra, including
the endpoint limit. These are actual generated branches of a new
finite instrument, not an assertion that an old Kraus index is readable.
$\square$

## 11. Sharp quadratic onset and its necessary leading direction

**Theorem 11.1 (evaluated right onset).** Fix any admitted $\tau,\xi$
and their genuinely nonreal state (QO.23). There exist finite
$C_{\rm rem},\epsilon_0>0$, depending on this fixed input and the
conditional source, such that

$$
F+K_{\rm onset}\epsilon^2-C_{\rm rem}\epsilon^3
\leq E_{s_*+\epsilon}(\rho)
\leq F+K_{\rm onset}\epsilon^2+C_{\rm rem}\epsilon^3
\quad(0<\epsilon<\epsilon_0).
\tag{QO.56}
$$

In particular the right onset exponent is two, and its coefficient is
the explicit positive number (QO.38). The lower remainder is uniform
over the entire original finite complex class.

Proof. Along the path, $m=\beta$, $\eta=0$,
$x_\epsilon=t_x\epsilon+O(\epsilon^2)$ and
$u_\epsilon=v_\theta\epsilon+O(\epsilon^2)$.
The cost identity and its remainder give

$$
W_\epsilon-F=
(a_{\rm curv}t_x^2+c_{\rm curv}v_\theta^2)\epsilon^2+O(\epsilon^3).
\tag{QO.57}
$$

Substitution of (QO.44) evaluates the bracket as
$(1/a_{\rm curv}+b_{\rm rec}^2/c_{\rm curv})/D_{\rm onset}^2
=K_{\rm onset}$. Theorem 10.2 is a normalized actual upper for
every sufficiently small positive $\epsilon$. Theorem 8.1 gives
the full-class lower with one cubic constant. Take the smaller of
the two radii and the larger finite constant. Neither an attained
original infimum nor an exact later optimizer has been presumed.
$\square$

**Theorem 11.2 (forced slopes for normalized necessary arrays).**
Let $\epsilon\downarrow0$ along any sequence of original designs whose
actual selected costs equal
$F+K_{\rm onset}\epsilon^2+o(\epsilon^2)$.
Apply precisely the averages and high-SS reassignment of Proposition
6.1, and form the coordinates of §7. Then

$$
\frac{\eta}{\epsilon^2}\longrightarrow0,\qquad
\frac{x}{\epsilon}\longrightarrow t_x,\qquad
\frac{\theta-\theta_0}{\epsilon}\longrightarrow v_\theta<0.
\tag{QO.58}
$$

Also $(A_{\rm act}-W)/\epsilon^2\to0$.
This is a direction statement about those analytic necessary arrays,
not uniqueness of a whole physical instrument.

Proof. Localization and the rate bounds (QO.41) apply to the sequence.
Any subsequential limits $e,x_0,u_0$ of
$\eta/\epsilon^2,x/\epsilon,u/\epsilon$ satisfy
$e\geq0$, $x_0+b_{\rm rec}u_0\geq1$, and

$$
K_{\rm onset}\geq
\lambda e+a_{\rm curv}x_0^2+c_{\rm curv}u_0^2 .
\tag{QO.59}
$$

Weighted Cauchy--Schwarz gives a lower bound $K_{\rm onset}$ for
the quadratic under that linear constraint. Equality has the unique
point $(x_0,u_0)=(t_x,v_\theta)$: its equality vectors are proportional
to $(1/a_{\rm curv},b_{\rm rec}/c_{\rm curv})$, and the active linear
constraint fixes the proportionality factor $1/D_{\rm onset}$.
The extra nonnegative radial term forces $e=0$. Every subsequence
has these limits, proving (QO.58). The same quadratic lower bound
and $W\leq A_{\rm act}$ force the acquisition/reassignment gap to
be $o(\epsilon^2)$.

If instead the old tilt is held fixed in these normalized arrays and
the cost is $F+O(\epsilon^2)$, then $u=0$ and (QO.42) forces
$x/\epsilon\geq1-o(1)$. Its leading excess is at least
$a_{\rm curv}\epsilon^2$, strictly above
$K_{\rm onset}\epsilon^2$. The negative angular slope is therefore
necessary for this reduced asymptotic optimum. It imposes no
unknown-state conjugation, no unique Kraus realization, and no claim
about designs away from the local regime. $\square$

## 12. Original twelve-vector, scaling and closed boundaries

**Proposition 12.1 (one common vector and strict original domination).**
The single matching instrument has on every original history the
actual acquired cost

$$
P_\epsilon A_y+Q_\epsilon B_y,\qquad
A_y=\sum_i h_i^2p_{yi},\qquad
B_y=b^2p_{y0}+a^2p_{y1}.
\tag{QO.60}
$$

For all sufficiently small positive $\epsilon$ this vector is strictly
dominated in every original coordinate by the credited JR common weak
vector $(kA_y)_{y,e,n}$ at the same strength and complete channel.

Proof. The high aggregate in (QO.51) has imaginary DT entry
$-iR_\epsilon$ and zero SS entry. The original inputs are real
symmetric and their coefficient Grams are real, so that imaginary
entry contributes zero to every trace pairing. This gives (QO.60)
for all signs without averaging or introducing a prior.
At the endpoint $p>k$, $q>0$, $s_*<\sqrt\ell$.
Continuity gives $P_\epsilon>k$, $Q_\epsilon>0$ and
$s_*+\epsilon<\sqrt\ell$ on a smaller interval.
All $A_y,B_y$ are positive. JR supplies one common instrument with
every coordinate $kA_y$ on that same weak-strength interval. Hence
each strict domination compares two simultaneous vectors.
The selected nonreal optimum supplies no new original-twelve Pareto
point, sharp sign-mean law or worst-history law. $\square$

**Proposition 12.2 (unnormalized positive inputs).** For any positive
five-mode $\sigma$ with $E^\dagger\sigma E=t\rho$, $t>0$, including
complement and cross-support components,

$$
E_{s_*+\epsilon}(\sigma)
=tF+tK_{\rm onset}\epsilon^2+O(t\epsilon^3).
\tag{QO.61}
$$

If the compression is zero, $E_s(\sigma)=0$ at every strength.

Proof. Proposition 3.3 gives
$\operatorname{tr}(G_{\rm acq}\sigma)\geq
\operatorname{tr}(\Theta(H)E^\dagger\sigma E)
=t\operatorname{tr}(CH)$ for each competitor.
Thus the normalized-input lower proof multiplies by $t$.
The matching high effect is supported on $V$, so its expectation
also multiplies by $t$, proving the upper. There is no division by
acceptance. Equivalently $A,B,C_S,\gamma,\lambda,d_{\rm cert},
a_{\rm curv},c_{\rm curv},F,K_{\rm onset}$ scale by $t$;
$p,q,s_*,b_{\rm rec},t_x,v_\theta$ do not change.

When compression is zero, positivity kills the cross-support block.
At any $s\in[0,1]$ factor the PSD coefficient matrices
$(I+r sX_c)/2$ into finitely many columns and assign their products
supported dimension-three fibres with live isometry decoders. Add
the same scalar supported and complement branches of §10.
Equations (QO.52)--(QO.55) give a normalized full instrument.
Its high effects are supported, so its acquired high mass on this
$\sigma$ is zero. Nonnegativity proves the minimum is zero. No
positive-definite formula was applied to a zero or singular Gram.
$\square$

**Convention 12.3 (strict endpoints and equivalent descriptions).**
The theorem fixes $\tau_i>0$ and admitted $\xi>0$. Its constants and
radius are uniform over competitors for that input, not over varying
inputs, $\xi\downarrow0$, $s_*\downarrow0$ or singular limits.
The plateau includes $s=0,s_*$, and the twelve-label path has a
valid continuous $\epsilon=0$ limit with high physical rank three.
Below the plateau endpoint the earlier rank-many low construction
has complete low coefficient rank three; this is the rank that
drops at the endpoint. The matching path low blocks and physical
low products have rank two throughout. Construction counts are not
minimal alphabet sizes or exact-clock storage bounds.

For fixed $\tau$, $\xi\downarrow0$ sends
$p\to k$, $q,r_0,\gamma\to0$, $F\to kA$ and
$s_*\to\sqrt\ell$. This recovers the diagonal plateau as a limit,
not an onset theorem at $\xi=0$ or an input-uniform cubic estimate.
No zero-discriminant, $x=s$, nonadmitted or singular-Gram branch is
included. A global phase on a coefficient vector leaves its projector
and CP branch unchanged.

The negative-imaginary mirror uses conjugated fixed encoder matrices
and range maps for the conjugate public state. Real $D,T,S$ and the
real prescribed effects ensure the same complete channel and costs.
This specifies different CP maps and is not conjugation of an unknown
state as an operation. Negative record strength is handled by swapping
the report names. At zero strength the binary report is fair, while
the finer generated alphabet can still depend on the input.
The exponent and coefficient are evaluated; a numerical radius,
numerical cubic constant, exact positive later-interval law,
later exact optimizer or whole-instrument uniqueness is not.

## 13. Attribution, parameter correspondences and distinct DEV tasks

**Convention 13.1 (mathematical credit).** The source-specific increment
here is the evaluated quadratic onset (QO.56), its exact coefficient,
full original finite-class cubic lower, actual matching instrument,
and necessary-array direction. The admitted nonreal family, tilted
plateau value, maximality, fourteen/twelve-label plateau attainers,
quartic later lower, affine later upper and strict scalar-trace gap
are credited to NP. They are not counted again as the onset increment.
The additional conclusion is supported by the ordinary derivations
in §§6–11, with the conditional antecedents specified in §§1–5.

| Supplied source | Content retained at its stated scope |
| --- | --- |
| CG §§1–28 | Calibrated histories, targets, source isolation and coefficient enclosures, original minimax benchmark and chosen full completion; averaged-live rigidity, restricted Schur obstruction, actual acquisition model, Schmidt bottleneck and stability/individual transfer penalties. Its generic and private-library antecedents remain conditional. |
| JR §§29–33 | Explicit acquired winding records, full complex/reference/time realization, actual family mass law, fixed-channel phase compatibility and parity ceilings. Its initial family cost is not a universal envelope. |
| JR §§34–40 | Broader all-error-optimizer sharp diagonal/common-attainer, original four-sign averages and worst-history laws, inverse budget, actual H/L construction and laws; finite, countable and stipulated integral scopes as stated there. Sign averaging fixes averaged live Choi and total failure effect, not an optimizer's full forgotten channel. |
| RE §§6–10 | Endpoint envelopes and actual separate attainers, paired resource effects, Pareto and nonattainment distinctions; its earlier interior family is an upper. |
| IR and integrated companion | Binary-live freedom, coherent perturbations, nonleast effects and lack of a simultaneous pointwise optimum; full complex compact coefficient reduction and finite realization/attainment. Integrated diagonal attribution belongs to JR. |
| CA §§3–9 | Plane-plus-quadratic cone, plane slack with Takagi criterion, six low atoms and generic twenty-four-branch exact reduction, trace-zero real face, scalar-trace obstruction/separator, sharp-mean singleton and exceptional-segment classification. |
| RG §§3–9 | Real positive-definite Gram spectral law, two lifts, positive sufficient record caps, fourteen-label realization, rational source ratios, original pure Grams and selected-coordinate Pareto vectors. Its sufficient caps are not all maximal, and its real evaluation does not cover the present genuinely nonreal family. |
| NP §§4–11 | Physical admitted family and source sign, full-cone tilted certificate, attained maximal plateau, actual closed-endpoint instruments, quantitative later bracket and same-strength trace-relaxation gap; strict original-twelve domination. |

The parameter dictionary is exact:
JR $(\theta,\omega,\delta)=(\alpha,\beta,\ell)$,
its $k$ is the present $k$, and
$(p_s,q_s)=(1-\beta-\alpha v_s,1-v_s)$.
Weak strengths have $(p_s,q_s)=(k,0)$.
Later $p_s-\alpha q_s=k$ and
$s=\sqrt{p_sq_s}+\sqrt{(1-p_s)(1-q_s)}$,
ending at $p_s=q_s=k/(1-\alpha)$.
Its costs are $p_sA_y+q_sB_y$ with worst height $27$.
Its diagonal selected-input law is $p_sA+q_sB$.
The four-sign mean identity
$\frac14\sum_{e,n}\rho_{y,e,n}=\operatorname{diag}p_y$
is a deterministic linear identity, not a prior.

IR, CA, RG and NP use the same compression, source coefficients and
coefficient order $(D,T,S)$ as (QO.8),(QO.16).
CA's budget matrix and RG's real spectral budget are $B_0$.
NP's $R_\xi,B_T,k_\xi$ are the present $Z_0,B,k_{\rm tilt}$;
NP's $R$ is $R_{\theta_0}$. Its source matrix $H^{\rm src}$ is
not the coefficient high aggregate $H$. Neither CA's plane-slack
criterion nor RG's real spectral formula is replaced by the local
slice lemma; the latter proves exactly its stated block domain.

**Proposition 13.2 (the latest height-TV results concern a distinct
constraint).** JR §§41–49 supply the original all-error-optimizer,
sharp worst-history-cost, actual-record height-TV task. Its binary
constraint is the contrast inequality
$2|\operatorname{Re}F_{01}|/\kappa\geq s$, with other effect entries
free. It does not prescribe (QO.13) or fix (QO.11) for every competitor.
Its results are credited without moving their optimality to this task.

Explanation of the exact boundary. JR §42 proves supported live and
aggregate-effect rigidity at simultaneous original error and sharp
worst-history cost, and excludes high-fibre later nonlive mass there.
It does not classify full five-mode channels or each labelled failure
CP measure. JR §§43–44 evaluate the strong-regime height-TV law,
including its transition to a flat part, and give actual common
attainment using a spectral scalar failure readout, with strict gain
over coordinate failure readout. These necessity results retain their
finite/countable/stipulated-integral scopes; their arithmetic signs
remain conditional on their source box.

JR §45 gives an exact compact four-real-PSD optimization and finite
attainment on its weak cost plateau, without evaluating the full weak
law. Section 46 gives a strict three-low-branch comparison retaining
every comparator label. Sections 48–49 evaluate that specified
symmetric point and improve it locally by another three-low-branch
instrument; retaining all labels under classical attenuation preserves
TV and can restore exact contrast. They do not prove optimality of
the improving point, nonoptimality of every three-low construction,
or a complete weak-plateau evaluation.

The local JR improving effect has a strictly positive $02$ entry,
whereas (QO.13) has zero $02$ entry. Its optimization is a
height-TV objective under sharp worst-history equality; the present
objective is selected nonreal-input acquired mass with the full binary
effect fixed. The present matching vector is strictly above JR's weak
common resource vector on all twelve histories. Thus neither JR's
rigidity nor its local improvement is a shortcut to the onset theorem,
and the onset does not settle its unevaluated weak TV law. $\square$

**Convention 13.3 (other current DEV carriers).** XXII §§363–367 treat
classical Fibonacci-window paid requests, common-seed two-request
comparisons, marked atomic versus nonatomic targets and same-cap
stopped-survivor laws. Its $p^*/q^*$ separation is not automatically
a target-risk separation; joint selection remains unresolved.
SI §§1–12 treat the tree-source Boolean installed-state/paid-query
support-incidence problem: incidence, short gaps, span-four/right-cut
conditions, both-conflict capacity, qualified grid laws, switched-order
two-block injection and above-grid overload. Its unrestricted collective
inequalities and unrestricted minimum budget remain open. Its latches,
separate eight-state reader and services cannot be replaced by an
uncharged source, state or oracle. Neither task supplies a quantum
acquired-resource or native permission correspondence here.

JG's zero-transfer/Schmidt-two comparison criterion concerns a Schur
restriction, whereas the present channel has nonzero T,S transfers.
Its later §§9–14 concern a separate all-Schur-fixing single-slot
supermap with a supplied $d$-dimensional slot and a jointly counted
bypass. Even bypass dimension one leaves that quantum slot available.
Its metric is UNHALVED diamond distance, whereas (QO.6) uses HALF
the full twelve-target cq norm. Identity fixing forces its actual
branch probabilities input independent by rank-one Choi support and
full TP decoding; those probabilities are not the acquired masses
in (QO.15).

The source-state repair in JG is an additional condition: fixing the
four connected spanning pure sign states forces identity on the
supported qutrit, but the original simulator changes live states and
produces failures. A transfer would need a proved map preserving
every original target/error comparison and not increasing the entire
joint acquired payload. No slot/bypass frontier, diamond bound,
classical allocation score, entropy identity or support-count
inequality supplies that map. No auxiliary number is inserted into
$E_s,F,K_{\rm onset}$ or the original twelve frontier.

**Convention 13.4 (mature methods and external boundaries).** Positive
Choi support, Gram left inverses, Kraus ranks, finite PSD spectral
factorizations, zero-Rayleigh induction, complex triangle and
Cauchy--Schwarz inequalities, Taylor estimates, the implicit-function
theorem and Gram--Schmidt are established methods. The increment is a
repository-derived source-specific application, not an invention of
those methods. Generic Kraus/Born identities and the pinned
Physlib/mathlib references named in the supplied texts are inherited
source reuse, not newly compiled Lean applications.

The supplied texts attribute finite CP extension to
Heinosaari--Jivulescu--Reeb--Wolf, Schmidt overlap bounds to
Terhal--Horodecki, Choi/Kraus correspondence to
Chruściński--Kossakowski, classical-assisted dimension/image compression
to Sekatski, and finite compatible-instrument mechanisms to
Leppäjärvi--Sedlák and Muñoz-Moller--Leppäjärvi--Heinosaari.
JG credits Mayer--Knill for connected spanning-state rigidity;
JR notes Uhlmann's affine-flat decomposition antecedent.
These are conditional inherited attributions, not independent readings
or authentication of those external works. No unproved continuous
instrument disintegration is needed: all present acquisitions are
finite and each time measure is checked directly. Root isolation,
enclosures, Jacobian, minimax, nested control/library compatibility
and physical calibration keep their declared conditional status.
No literature-wide absence or worldwide novelty/priority is certified.

## 14. Unresolved mathematics and native enactment

**Open problem 14.1 (broader original programme).** Evaluate this same
$E_s$ for arbitrary positive complex supported inputs, general
nonreal DT/DS/TS coherence, singular coefficient Grams and all
strengths. The present result fixes one admitted nonreal input and
evaluates only its right local onset. Its algebraic path is a matching
asymptotic upper, not a proven exact later minimizer on a positive
interval. General later minimizers, individual original-history later
laws, and the entire original twelve-coordinate undominated frontier
beyond known faces and selected points remain unresolved. Neither a
compact reduction nor separate pointwise minima settles that frontier.
No separate physical singular-Gram candidate is used here.

JR's full weak height-TV evaluation, SI's unrestricted collective
compensation and XXII's joint selection retain their own unresolved
boundaries. No unconditional-prefix optimum, whole-channel uniqueness,
new kernel/frozen truth, quantum capacity formula, generic neural-network
or empirical-learning conclusion follows. This bounded mathematical
result does not complete the continuing theory/DEV/native programme.

**Definition 14.2 (remaining native operations and actual time).**
The twelve-label specification is an actual normalized mathematical CP
encoder/full-TP-decoder instrument. Native enactment still requires
lawful access to the sole unknown specimen, genuinely generated
classical flags, calibrated support and range encodings, coherent
storage of the entire joint quantum fibre, and permitted controlled
range decoding. Permanently discarded systems cannot return as free
shares. These operations and their acquisition placement must fit the
same aligned original clock without extra execution time. Source,
preparation, epoch, calibrations, permissions, controller updates,
metadata and old stopped archives retain their original semantics.

The native timing service must cause the FIRST absorbing failure at
actual elapsed $t$, absolute $6+t$, forbid every later positive-carrier
operation on that failed branch, and deliver live output at elapsed
one. A scalar branch destined to fail, a Borel CP output measure, or
a timestamp sampled and recorded later does not supply that physical
event, its timing service or finite exact-clock storage. All complex,
passive-reference, separate original labels, complement/cross-support
and zero-sector identities must be enacted together.

OriginalControl gives finite duration, strict-domain continuity,
bounded phase variation and its absolute-continuity or finite
piecewise-$C^1$ alternatives. Its chronological composition constructs
paths, not the above encoders or controlled decoders. The original
probability-changing phase controls include
$P=\partial_\kappa$ and $Q=\sum_aw_a(\kappa)\partial_{h_a}$;
their double-wall commutator
$[P,Q]=-(\partial_u+\partial_v)/r_b\ne0$ prevents replacing the
native menu by an exhaustive diagonal/Schur restriction. It supplies
neither arbitrary unknown-input actuation nor a global impossibility
theorem. Native feasibility, efficiency, impossibility and capacity
remain unproved. Their recertification is not a prerequisite asserted
for the conditional CP theorem established here.

The source volumes are [CG], [JR], [RE], [IR], [CA], [RG], [NP],
[JG], [XXII] and [SI], at the scopes identified in §13.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[RE]: FIB_NATIVE_FIXED_CHANNEL_RECORD_RESOURCE_ENVELOPE.md
[IR]: FIB_NATIVE_INTERIOR_RECORD_RESOURCE_REDUCTION.md
[CA]: FIB_NATIVE_COMPLEX_ATOMIC_CONE_AND_OPTIMAL_RESOURCE_FACES.md
[RG]: FIB_NATIVE_REAL_GRAM_SMALL_RECORD_RESOURCE_LAW.md
[NP]: FIB_NATIVE_NONREAL_MAXIMAL_PLATEAU_RESOURCE_LAW.md
[JG]: FIB_NATIVE_JOINT_TRANSFER_COHERENCE_INTERFACE_GEOMETRY.md
[XXII]: KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXII.md
[SI]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SUPPORT_INCIDENCE_AND_COUNT_RELAXATION.md

## 追加锚（本行以下为增补区）


