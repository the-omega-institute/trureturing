# The all-strength acquisition-resource law for admitted native nonreal inputs

> This volume gives ordinary conditional mathematics for the selected-input
> resource problem. For every input in the admitted physical family below,
> it evaluates the entire strength interval, proves the lower bound against
> the full finite complex acquisition class, and supplies finite instruments
> attaining equality. The calibrated algebraic source and its certificates
> remain premises. Abstract CP instruments do not supply native actuators,
> an aligned-clock execution or an absorbing-failure implementation. The
> volume follows the generic-v1 append convention.

## 1. Original task and conditional coefficient source

**Definition 1.1 (specimen and original complete-output comparison).**
Use five orthonormal modes $e_0,e_1,e_2,e_3,e_4$; the last retains its
original name mode $13$. Define

$$
E=\left((e_0+e_4)/\sqrt2,(e_1+e_3)/\sqrt2,e_2\right),\qquad
P_5=EE^\dagger,\quad Q_5=I_5-P_5.
\tag{AS.1}
$$

The supported coordinates $0,1,2$ mean $(+,-,2)$ and do not rename
failure labels. For $y\in\{5,16,27\}$ and independent $e,n\in\{\pm1\}$,
put

$$
\begin{aligned}
p_y&=(y/128,(64-y)/128,1/2),&a_y&=(\sqrt{p_{yi}})_i,\\
U_{e,n}&=\operatorname{diag}(e,n,1),&
\rho_{y,e,n}&=U_{e,n}a_ya_y^TU_{e,n}^\dagger,\\
d_y&=\left(\frac y{128},\frac{y(58-y)}{128(y+6)},\frac y{2(y+6)}\right),&
B_y^{\rm tar}&=(\sqrt{d_{yi}d_{yj}})_{ij},\\
f_y(t)&=\frac{6y}{(y+6t)^2},&
w&=(0,1/4,1/2,1/4,0),\\
P_f&=|f\rangle\langle f|.&&
\end{aligned}
\tag{AS.2}
$$

The input is $E\rho_{y,e,n}E^\dagger$. Its ideal live output is
$EU_{e,n}B_y^{\rm tar}U_{e,n}^\dagger E^\dagger$; its five ideal
failure measures are separately $w_j f_y(t)dt\,P_f$. The live trace is
$y/(y+6)$ and the remaining mass is $\int_0^1 f_y$. For the complete
ideal output $\Omega_{y,e,n}$, the original benchmark is

$$
E(\Phi)=\max_{y,e,n}\frac12
 \|\Omega_{y,e,n}-\Phi(E\rho_{y,e,n}E^\dagger)\|_{1,\mathrm{cq}}.
\tag{AS.3}
$$

Every live coherence, separate labelled Borel-time measure, singular or
atomic addition, wrong support, abort, rejection and extra sector is
included, also when its target is zero. This is HALF the full cq norm,
without time bins or survival/acceptance division.

The underlying calibrated probability path has
$\pi(k)=(k,1/4-k,1/2,1/4-k,k)$ with strict $0<k<1/4$.
The twelve histories have $x=y/256$, $\beta_{\rm hist}\in\{0,\pi\}$,
$m\in\{0,1\}$, $e=(-1)^{\beta_{\rm hist}/\pi}$ and $n=e(-1)^m$.
From common height $1/8$ and zero phase their six unit legs are: phase
$0\to2\pi m$; height $1/8\to1/16$; phase
$2\pi m\to2\pi m+B_{\rm hist}$; height $1/16\to1/8$; phase
back to $2\pi m$; height $1/8\to x$, where
$B_{\rm hist}=8\beta_{\rm hist}-4\pi m$ and each undisplayed coordinate
is held fixed. Residual phases are
$(\beta_{\rm hist},\beta_{\rm hist}-\pi m,0,
\beta_{\rm hist}-\pi m,\beta_{\rm hist})$.
At absolute time six the sole already reached normalized specimen is
received. The continuation is $k(t)=x+6t/256$ with fixed phase,
$0\leq t\leq1$, on the common legal starting domain $(0,58/256)$.
The old reach masses $32/177,2/9,32/111$ are not priors.

The original path contract retains finite nonnegative duration,
continuity, strict height domain, real signed phase lifts of finite
variation, absolute continuity or the stipulated finite piecewise-$C^1$
alternative, and chronological composition. Zero duration permits only
zero matching displacement. The preparation uses no wall limit or
infinite winding. Common fixed metadata include the no-failure flag,
aligned clock, source/preparation/epoch, calibration, permissions and
controller. There is no readable old waveform, height, phase, history,
generator word, programme, callback or discarded-environment port.
First executed failure is absorbing, with no later positive-carrier
action; the stopped archives and their controller updates remain intact.
Elapsed $t$ means absolute $6+t$; live output is at elapsed one.

**Definition 1.2 (the exact inherited point).** The following identifies
the conditional CG source also used by NP and QO. Coordinates
$\mathbf x=(\lambda_{\rm src},\alpha_1,\alpha_2,\beta_1,\beta_2,z_{\rm src})$
and $\eta=(\eta_0,\eta_1,\eta_2)$ are distinct from the parameters below.
Write

$$
\begin{aligned}
v_5&=(\alpha_1,\alpha_2,-1)^T,&v_{27}&=(\beta_1,\beta_2,1)^T,\\
A_5^{\rm src}&=\lambda_{\rm src}v_5v_5^T/\|v_5\|^2,&
A_{27}^{\rm src}&=(1-\lambda_{\rm src})v_{27}v_{27}^T/\|v_{27}\|^2,\\
\zeta&=(z_{\rm src},59\lambda_{\rm src}/128,\lambda_{\rm src}/2),&
N^{\rm src}&=\sum_{y=5,27}A_y^{\rm src}\odot a_ya_y^T,\\
S_0^{\rm src}&=\operatorname{diag}\zeta-N^{\rm src},&&\\
S_{ij}^{\rm src}&=\begin{pmatrix}
\zeta_j-\sum_y(A_y^{\rm src})_{ii}p_{yj}&-N_{ij}^{\rm src}\cr
-N_{ij}^{\rm src}&\zeta_i-\sum_y(A_y^{\rm src})_{jj}p_{yi}
\end{pmatrix}\quad(i<j),&&\\
F^{\rm src}&=\sum_y\operatorname{tr}(A_y^{\rm src}B_y^{\rm tar})
 -\sum_i\zeta_i+6\lambda_{\rm src}/11,&&\\
g^{\rm src}&=(1000\det S_0^{\rm src},\det S_{01}^{\rm src},\det S_{02}^{\rm src}).&&
\end{aligned}
\tag{AS.4}
$$

The named premise is the isolated zero of
$(\nabla_{\mathbf x}(F^{\rm src}+\eta\cdot g^{\rm src}),g^{\rm src})$
in the radius-$10^{-24}$ product box about the following exact rationals.

| Coordinate | Centre |
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

All expressions use this zero, not its centre. Define

$$
\begin{aligned}
H^{\rm src}&=1000\eta_0\operatorname{adj}S_0^{\rm src},&
Q^{01}&=\eta_1\operatorname{adj}S_{01}^{\rm src},&
Q^{02}&=\eta_2\operatorname{adj}S_{02}^{\rm src},\\
(h_0,h_1,h_2)^T&=H^{\rm src}e_0/\sqrt{H^{\rm src}_{00}},&
(a,b)^T&=Q^{01}e_0/\sqrt{Q^{01}_{00}},&
(c,d_{\rm src})^T&=Q^{02}e_0/\sqrt{Q^{02}_{00}},\\
m_1&=1-H^{\rm src}_{11}-Q^{01}_{00},&
m_2&=1-H^{\rm src}_{22}-Q^{02}_{00}.&&
\end{aligned}
\tag{AS.5}
$$

Adjugate means transposed cofactor matrix. Set

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=a|0\rangle\langle1|+b|1\rangle\langle0|,\quad
S=c|0\rangle\langle2|+d_{\rm src}|2\rangle\langle0|,\quad
M=\operatorname{diag}(0,m_1,m_2),\quad \kappa=h_0a+h_1b,\\
\alpha=\frac{ab}{h_0h_1},\quad
\beta=\frac{cd_{\rm src}}{h_0h_2},\quad
\ell=\alpha+\beta,\quad k=1-\ell,\quad \chi=h_1b-h_0a.
\end{gathered}
\tag{AS.6}
$$

The source supplies positive amplitudes and $m_1,m_2$, its rank-one
factor identities, and

$$
\begin{gathered}
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\quad 0<\kappa<1/4,\\
.968<h_0^2<.970,\quad .498<h_1^2<.500,\quad .655<h_2^2<.656,\\
h_0h_1>.695,\quad h_0h_2>.796,\quad
a^2+b^2+c^2+d_{\rm src}^2<.036,\\
0<\ell<18/695<1/36,\quad \chi>0.
\end{gathered}
\tag{AS.7}
$$

For example $2ab+2cd_{\rm src}$ is bounded by the square sum,
giving the stated bound for $\ell$. NP/QO's strict sign proof uses
$a/b<.51$ from the source adjugate and $h_1/h_0>7/10$, so
$h_0a/(h_1b)<51/70<1$. These are implications of the inherited
source conditions. No root isolation, bordered-Jacobian check,
interval certificate or minimax verification is performed here.

**Definition 1.3 (the particular complete channel).** For every complex
$A\in M_5$, write $A_V=E^\dagger AE$ and $g(t)=2/(1+t)^2$. Fix

$$
\begin{aligned}
\Phi_*^L(A)&=E(DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger)E^\dagger,\\
\Phi_{*,j}^f(A)(B)&=\left(\int_Bg(t)dt\right)
 [w_j\operatorname{tr}(MA_V)+\mathbf1_{j=2}\operatorname{tr}(Q_5A)]P_f
\end{aligned}
\tag{AS.8}
$$

for each original label and each Borel $B\subseteq[0,1]$. Cross-support
maps, complement live output and additional sectors are zero; common
fixed metadata are carried identically. The normalization in (AS.7),
$\sum_jw_j=1$ and $\int_0^1g=1$ give TP. The conditional CG minimax
premise is

$$
E(\Phi_*)=E_*=F^{\rm src}(\mathbf x_*)\in
(0.14817810291080132013,0.14817810291080132014).
\tag{AS.9}
$$

The actual density $g$ is not an ideal $f_y$. Fixing (AS.8) retains
the inherited error; it does not assert that all original optimizers
have this entire channel or these individual failure measures.

## 2. Acquisition class and exactly the admitted physical family

**Definition 2.1 (selected-input acquisition resource).** Let
$X_{01}=|0\rangle\langle1|+|1\rangle\langle0|$. For $0\leq s\leq1$
prescribe the full every-input effects

$$
F_r(s)=\frac{I_5+r s\kappa EX_{01}E^\dagger}{2},\qquad r=\pm1.
\tag{AS.10}
$$

A competitor consists of a finite actually generated accessible
classical label $\xi$, a report $r(\xi)$, a finite joint quantum fibre
$\mathbb C^{d_\xi}$, CP encoders $\mathcal C_\xi:M_5\to M_{d_\xi}$,
and full-output whole-fibre CPTP decoders $\mathcal R_\xi$, with

$$
\sum_\xi\mathcal C_\xi^\dagger(I)=I_5,\quad
\sum_{r(\xi)=r}\mathcal C_\xi^\dagger(I)=F_r(s),\quad
\sum_\xi\mathcal R_\xi\mathcal C_\xi=\Phi_*.
\tag{AS.11}
$$

All future-accessible input-dependent quantum systems are counted
jointly: specimen, memory, controller, environment, returned systems
and entanglement shares. A coherent flag counts as quantum until an
actual classical direct sum is generated. Every omitted dilation share
is permanently inaccessible before this cut. Independent later blank
ancillas are permitted; a correlated accessible share is not a blank.
Passive references are inaccessible to execution. The decoder's live
restriction is TNI, whereas the whole decoder is TP.

Define

$$
G_{\rm acq}=\sum_{d_\xi\geq3}\mathcal C_\xi^\dagger(I),\qquad
E_s(\sigma)=\inf_{\text{(AS.11)}}\operatorname{tr}(G_{\rm acq}\sigma).
\tag{AS.12}
$$

This is acquired mass, including high acquisition later failing. There
is no prior, history sensor, helper, bypass, hidden share, extra copy,
callback, reset, retry or postselection. For supported states abbreviate
$E_s(\rho)=E_s(E\rho E^\dagger)$. A public selected input and strength
may select fixed matrices before the unknown specimen arrives; the
chosen instrument still acts commonly on every unknown input. Pointwise
minima are not one simultaneous twelve-input or all-input optimum.

**Definition 2.2 (admission and physical Gram).** Choose $\tau_i>0$,
$\sum_i\tau_i=1$, and $0<\xi<1$. Define

$$
\begin{aligned}
A&=\sum_i h_i^2\tau_i,&B&=b^2\tau_0+a^2\tau_1,&
C_S&=d_{\rm src}^2\tau_0+c^2\tau_2,\\
c_0&=\frac{1-\xi^2}{1+\xi^2},&\sigma_0&=\frac{2\xi}{1+\xi^2},&
\theta_0&=2\arctan\xi,\\
\delta_0&=1-\alpha-\beta c_0,&
Z_0&=\sqrt{\delta_0^2+\beta^2\sigma_0^2},&
r_0&=\frac{\beta\sigma_0}{2\sqrt\alpha},\\
p&=(Z_0+\delta_0)/2,&q&=(Z_0-\delta_0)/(2\alpha),&
k_{\rm tilt}&=(1-\alpha)c_0-\beta,\\
\lambda_0&=\frac{Ap-Bq}{c_0Z_0},&
d_{\rm cert}&=B+\lambda_0\alpha c_0,&
\gamma&=\lambda_0\sqrt\alpha\,\sigma_0+d_{\rm cert}\sqrt{q/p}.
\end{aligned}
\tag{AS.13}
$$

Admission is exactly

$$
p+q<1,\qquad k_{\rm tilt}>0,\qquad Ap>Bq,\qquad
\gamma<\chi\sqrt{\tau_0\tau_1}.
\tag{AS.14}
$$

For every such choice set

$$
\rho=\begin{pmatrix}\tau_0&i\gamma/\chi&0\cr
-i\gamma/\chi&\tau_1&0\cr0&0&\tau_2\end{pmatrix},\quad
C=\begin{pmatrix}A&i\gamma&0\cr-i\gamma&B&0\cr0&0&C_S\end{pmatrix},\quad
h_*=(\sqrt p,i\sqrt q,0)^T,\quad H_*=h_*h_*^\dagger,\quad
s_*=\sqrt{1-p-q},\quad F=\lambda_0 k_{\rm tilt}.
\tag{AS.15}
$$

**Proposition 2.3 (credited physical nonemptiness and margins).** The
admitted family is nonempty for every positive $\tau$. Its states and
coefficient Grams are positive definite and genuinely nonreal;
$A>B>0$, $pq=r_0^2$, $p-\alpha q=\delta_0$, $p>k$,
$0<s_*<\sqrt\ell$, and $F>0$.

Proof. Set

$$
\begin{aligned}
T_0&=2\beta+\frac{\beta^2(1+\alpha)}{\alpha k},\quad
G_0=4A\sqrt\alpha+\frac{\beta(B+2\alpha A)}{\sqrt\alpha k},\\
\xi_0&=\min\left\{\frac14,\sqrt{\frac\ell{2T_0}},
\sqrt{\frac{k}{4(1-\alpha)}},
\sqrt{\frac{A\alpha k^2}{2B\beta^2}},
\frac{\chi\sqrt{\tau_0\tau_1}}{2G_0}\right\}>0.
\end{aligned}
\tag{AS.16}
$$

For $0<\xi\leq\xi_0$, $c_0>1/2$, $\sigma_0\leq2\xi$,
$p\geq k$, and $q=r_0^2/p\leq\beta^2\xi^2/(\alpha k)$. Hence
$p+q=k+\beta(1-c_0)+(1+\alpha)q\leq k+T_0\xi^2\leq1-\ell/2$,
$k_{\rm tilt}\geq k/2$, $Ap-Bq\geq Ak/2$,
$\lambda_0\leq2A$, and
$\gamma\leq G_0\xi\leq\chi\sqrt{\tau_0\tau_1}/2$.
This proves admission. For arbitrary admitted parameters the leading
minor of $\rho$ is $\tau_0\tau_1-(\gamma/\chi)^2>0$;
its trace is one and $\gamma>0$. Direct trace expansion yields exactly
$C_{ij}=\operatorname{tr}(K_i^\dagger K_j\rho)$ with
$(K_D,K_T,K_S)=(D,T,S)$: its $DT$ entry is $i\gamma$ and the other
cross entries vanish. For $z\ne0$, $K(z)=\sum_i z_iK_i\ne0$ by
independent supports, and $\rho>0$ gives
$z^\dagger Cz=\operatorname{tr}(K(z)^\dagger K(z)\rho)>0$.
The source bounds give $A>.498$ and $B<.036$, thus $A>B$.
The identities for $p,q$ follow from (AS.13); $\xi>0$ gives
$p\geq\delta_0>k$, so $p+q>k$ and $s_*<\sqrt\ell$.
This is the NP/QO nonemptiness argument, retained as an antecedent.
$\square$

## 3. Explicit statement of the entire law

**Definition 3.1 (selected scalar algebraic branch).** For $s_*<s<1$ put

$$
\begin{gathered}
j=1-s^2,\quad a_0=1+\alpha,\quad b_0=2\sqrt\alpha\,s,\quad
\Delta=a_0^2-b_0^2=(1-\alpha)^2+4\alpha j,\\
w_A=\frac{\alpha A+B}{2\alpha},\quad
w_B=\frac{\alpha A-B}{2\alpha},\quad n=\frac\gamma{\sqrt\alpha},\\
c_s(d)=(1-\alpha)d+2\alpha j,\quad
d_{\min}=\frac{\beta\sqrt\Delta-2\alpha j}{1-\alpha},\quad
I_s=(\max\{0,d_{\min}\},\beta),\\
e_s(d)=\sqrt{c_s(d)^2-\Delta\beta^2},\quad
r(d)=\sqrt{\beta^2-d^2},\quad
u_s(d)=\frac{a_0c_s(d)+b_0e_s(d)}\Delta.
\end{gathered}
\tag{AS.17}
$$

Here $d$ is an optimization coordinate, distinct from $d_{\rm src}$.
Let $d_s$ be the unique root in $I_s$ of

$$
\frac{w_A(1-\alpha)}\Delta
 \left(a_0+\frac{b_0c_s(d)}{e_s(d)}\right)+w_B
 =\frac{nd}{\sqrt{\beta^2-d^2}}.
\tag{AS.18}
$$

Existence, uniqueness and positivity of every denominator are proved
below. This specifies a scalar root, not a residual optimization.

**Theorem 3.2 (all-strength selected-input law).** For exactly every
admitted state (AS.15), in the entire class (AS.11), the infimum is
attained and

$$
\boxed{
E_s(\rho)=\begin{cases}
F,&0\leq s\leq s_*,\\
A+B-w_Au_s(d_s)-w_Bd_s-n\sqrt{\beta^2-d_s^2},&s_*<s<1,\\
\displaystyle\frac{k}{1-\alpha}(A+B),&s=1.
\end{cases}}
\tag{AS.19}
$$

It is continuous and convex on $[0,1]$, constant exactly on $[0,s_*]$,
strictly increasing on $[s_*,1]$, and real analytic on $(s_*,1)$.
There is one later branch with no additional interior rank degeneration.
The plateau and sharp quadratic onset are credited NP/QO results; the
whole later evaluation and endpoint follow from Sections 4–8.

**Proposition 3.3 (optional reversible polynomial specification).** Define

$$
\begin{gathered}
L=\frac{w_A(1-\alpha)a_0}\Delta+w_B,\qquad
N=\frac{w_A(1-\alpha)b_0}\Delta,\quad c=c_s(d),\\
e_2=c^2-\Delta\beta^2,\qquad r_2=\beta^2-d^2,\\
\mathcal P(d)=(n^2d^2+L^2r_2)e_2-N^2c^2r_2.
\end{gathered}
\tag{AS.20}
$$

Equivalently $d_s$ is the unique root in $I_s$ satisfying

$$
\mathcal P(d)^2-4n^2d^2L^2r_2e_2^2=0,\quad
\mathcal P(d)>0,\quad nd>L\sqrt{r_2}.
\tag{AS.21}
$$

The carrier has degree at most eight in $d$. It is algebraic over the
inherited source and algebraic public parameters; for arbitrary admitted
real public parameters it is algebraic relative to those parameters.
No claim that arbitrary real inputs are algebraic numbers is needed.

## 4. Full-class necessity and the global outer problem

**Lemma 4.1 (complete singular locus and conventions).** In coefficient
order $(D,T,S)$ set

$$
\begin{gathered}
K(z)=uD+vT+wS=\begin{pmatrix}
h_0u&av&cw\cr bv&h_1u&0\cr d_{\rm src}w&0&h_2u
\end{pmatrix},\quad
B_0=\operatorname{diag}(1,-\alpha,-\beta),\quad
X_c=|D\rangle\langle T|+|T\rangle\langle D|,\\
\Theta(Z)=\sum_{i,j}Z_{ij}K_j^\dagger K_i,\qquad
\mathcal Z=\{u=0\}\cup\{u^2-\alpha v^2-\beta w^2=0\},\\
\mathcal C_2=\left\{\sum_{a=1}^N z_az_a^\dagger:z_a\in\mathcal Z,
\ N<\infty\right\}.
\end{gathered}
\tag{AS.22}
$$

Then $\det K=h_0h_1h_2u(u^2-\alpha v^2-\beta w^2)$.
Every nonzero singular product has rank exactly two: for $u\ne0$
the $1,2$ minor is $h_1h_2u^2\ne0$; for $u=0$, column zero in
rows one/two and a nonzero row-zero column are independent. Thus the
entire complex plane and quadratic component are included. Also
$\operatorname{tr}(CZ)=\operatorname{tr}(\Theta(Z)\rho)$.
For output-input Choi columns $\mathcal V=(|K_i\rangle\!\rangle)_i$,
the coefficient Choi is $\mathcal VZ\mathcal V^\dagger$ with output
partial trace $\Theta(Z)^T$. These index and transpose conventions
follow by expanding each matrix unit. $\square$

**Proposition 4.2 (necessity for arbitrary original competitors).** Every
competitor has $H_r\succeq0$, $L_r\in\mathcal C_2$, $Z_r=H_r+L_r$,
and supported binary failure effect $N$ such that

$$
\begin{gathered}
Z_++Z_-=I_3,\qquad
N=(I_3+s\kappa X_{01})/2-\Theta(Z_+),\quad0\preceq N\preceq M,\\
\operatorname{Re}(Z_+)_{DT}=s/2,\qquad
G_{\rm acq}\succeq E\Theta(H_++H_-)E^\dagger.
\end{gathered}
\tag{AS.23}
$$

Proof. Multiply each encoder Kraus matrix by each live-decoder Kraus
matrix, without declaring these analytic refinements accessible labels.
Their positive Choi projectors sum to the fixed live Choi of (AS.8).
A kernel vector has zero squared pairing with each summand, so each
product lies in the three-column support and equals $EK(z)E^\dagger$.
Apply the Gram left inverse
$(\mathcal W^\dagger\mathcal W)^{-1}\mathcal W^\dagger$ of the three
embedded columns to both sides of their Choi sum to obtain
$\sum zz^\dagger=I_3$. The independent columns have not been
normalized. Group these same products by actual report and actual
fibre dimension. A product through $d_\xi\leq2$ has rank at most two
and lies in (AS.22); the other products give $H_r$.

The plus and minus supported nonlive effects are $N$ and $M-N$.
Positivity and $M|0\rangle=0$ kill their first rows and columns.
For Hermitian $Z$,
$\Theta(Z)_{01}=h_1bZ_{DT}+h_0a\overline{Z_{DT}}$;
the prescribed effect therefore gives $\operatorname{Re}Z_{DT}=s/2$.
Arbitrary report-dependent failure measures are allowed in this argument.
For each high branch full TP decoding gives live adjoint identity at
most the whole identity. Pulling it back through that encoder and
summing proves the last five-mode operator inequality. This includes
high acquisition later failing, complement and cross-support effects.
No real, covariant, isometric or wholly-live restriction has been placed
on a competitor. $\square$

**Lemma 4.3 (analytic array reduction).** For the selected Gram (AS.15),
every competitor bounds below arrays of the form

$$
\begin{aligned}
H_r&=\frac12\begin{pmatrix}P&r t-iR&0\cr r t+iR&Q&0\cr0&0&0\end{pmatrix},\\
L_r&=\frac12\begin{pmatrix}1-P&r(s-t)+iR&0\cr
r(s-t)-iR&1-Q&0\cr0&0&1\end{pmatrix}\in\mathcal C_2,
\end{aligned}
\tag{AS.24}
$$

with $W=AP+BQ-2\gamma R$ no greater than its actual cost.

Proof. Average coefficient arrays under $J_S=\operatorname{diag}(1,1,-1)$,
induced by specimen $\operatorname{diag}(-1,-1,1)$, to remove $DS,TS$.
It preserves $C$, the singular locus, positivity and the full effect
condition, transforming failure subeffects by the same specimen unitary.
Then average with
$(H_r,L_r)\mapsto(J_T\overline{H_{-r}}J_T,
J_T\overline{L_{-r}}J_T)$, $J_T=\operatorname{diag}(1,-1,1)$.
For specimen $U_T=\operatorname{diag}(1,-1,1)$, $\Theta$ transforms
as $U_T\overline{\Theta(\cdot)}U_T$; report reversal compensates
the sign of $X_{01}$. The new plus failure effect is
$U_T\overline{(M-N)}U_T\in[0,M]$. Both operations preserve the
selected trace cost, since $C=J_T\overline C J_T$; they commute.
They are operations on necessary arrays, not conjugation channels
applied to an unknown state or a physical normal form.

The report diagonals become $1/2$. The report symmetry and
$Z_++Z_-=I$ make $(Z_+)_{DT}$ real, and (AS.23) fixes it to $s/2$.
Consequently $Z_r=(I+r sX_c)/2$ and $N_r=M/2$.
The separated high $SS$ entry can be moved to the genuine low plane
atom along $S$. This preserves all totals and low-cone membership and
decreases the high-live cost by its nonnegative coefficient times
$C_S>0$. Parametrizing the remaining $DT$ block gives (AS.24).
This reproduces the QO necessary-array reduction at its stated scope.
$\square$

**Lemma 4.4 (tilts valid on the whole complex low cone).** For every
$\theta$ with $\cos\theta\geq0$ the matrix

$$
B_\theta=\begin{pmatrix}
\cos\theta&i\sqrt\alpha\sin\theta&0\cr
-i\sqrt\alpha\sin\theta&-\alpha\cos\theta&0\cr0&0&-\beta
\end{pmatrix}
\tag{AS.25}
$$

satisfies $\operatorname{tr}(B_\theta L)\leq0$ for $L\in\mathcal C_2$.
For a quadratic-null $z=(u,v,w)$, put
$x=|u|^2-\alpha|v|^2$, $y=2\sqrt\alpha\operatorname{Im}(u\overline v)$.
Expansion gives $x^2+y^2=|u^2-\alpha v^2|^2=\beta^2|w|^4$;
thus $x\cos\theta+y\sin\theta\leq\beta|w|^2$.
On the entire plane $u=0$, the pairing is
$-\alpha\cos\theta|v|^2-\beta|w|^2\leq0$. Sum over atoms.
This is the NP full-cone tilt, including the plane. $\square$

**Definition 4.5 (necessary outer value).** Set

$$
Z_s=\begin{pmatrix}1&s\cr s&1\end{pmatrix},\quad
X=\begin{pmatrix}P&t-iR\cr t+iR&Q\end{pmatrix},\quad
Y=Z_s-X=\begin{pmatrix}U&v+iR\cr v-iR&V\end{pmatrix},
\quad U=1-P,\ V=1-Q,\ v=s-t,\ d=U-\alpha V.
\tag{AS.26}
$$

Let $V(s)$ minimize $W=\operatorname{tr}(C_{DT}X)$ over

$$
0\preceq X\preceq Z_s,\qquad
(\max\{d,0\})^2+4\alpha R^2\leq\beta^2.
\tag{AS.27}
$$

Here $C_{DT}$ denotes the leading $2\times2$ block of $C$.
The last inequality is exactly the intersection of
$d\cos\theta+2\sqrt\alpha R\sin\theta\leq\beta$ over the right
half-circle: its maximum is $\sqrt{d^2+4\alpha R^2}$ for $d\geq0$
and $2\sqrt\alpha|R|$ for $d\leq0$. Hence every actual competitor
has cost at least $V(s)$ by Lemmas 4.3–4.4, including negative $d$
and plane slack. These affine tilt conditions and the PSD conditions
give a convex feasible graph in $(s,X)$. Fibres are closed and bounded.
They are nonempty: $X=(1-\zeta)Z_s$ for any fixed
$0<\zeta<\beta/(1-\alpha)$ has $R=0$, $d=(1-\alpha)\zeta<\beta$.
Thus $V(s)$ is a finite attained auxiliary minimum. Sufficiency of an
arbitrary outer point is neither assumed nor needed.

## 5. Global branch exclusions and scalar evaluation

**Lemma 5.1 (the credited plateau is also the exact outer plateau).**
$V(s)=F$ exactly when $0\leq s\leq s_*$. Equality forces
$(P,Q,R,t)=(p,q,r_0,0)$.

Proof. Removing the real entry $t$ from $X$ gives
$H=\left(\begin{smallmatrix}P&-iR\\iR&Q\end{smallmatrix}\right)$.
The determinants of $X,Y$ imply $0\preceq H\preceq I_2$.
The $\theta_0$ tilt implies
$\operatorname{tr}(B_{\theta_0,DT}H)\geq k_{\rm tilt}$. Directly
from (AS.13),

$$
C_{DT}-\lambda_0B_{\theta_0,DT}
=d_{\rm cert}\begin{pmatrix}q/p&i\sqrt{q/p}\\
-i\sqrt{q/p}&1\end{pmatrix}\succeq0,\qquad
\ker(C_{DT}-\lambda_0B_{\theta_0,DT})
=\operatorname{span}\{(\sqrt p,i\sqrt q)^T\}.
\tag{AS.28}
$$

In particular
$\operatorname{tr}(B_{\theta_0,DT}H_{*,DT})=k_{\rm tilt}$ and
$\operatorname{tr}(C_{DT}H_{*,DT})=F=Ap+Bq-2\gamma r_0$.
The exact difference is

$$
W-F=\lambda_0[\operatorname{tr}(B_{\theta_0,DT}H)-k_{\rm tilt}]
 +\operatorname{tr}((C_{DT}-\lambda_0B_{\theta_0,DT})H)\geq0.
\tag{AS.29}
$$

If it vanishes, positive support gives $H=aH_{*,DT}$ and the
positive pairing $k_{\rm tilt}$ gives $a=1$. Then
$\det X=-t^2\geq0$ forces $t=0$ and
$\det Y=s_*^2-s^2\geq0$ forces $s\leq s_*$. Conversely the
NP plateau construction, explicitly realized in Section 7, gives these
arrays for every $s\leq s_*$. Attainment of the compact outer problem
therefore gives $V(s)>F$ for every $s>s_*$. This proves strictness
in the necessary relaxation itself. $\square$

**Lemma 5.2 (convexity, monotonicity and both active determinants).**
$V$ is convex, nondecreasing, and strictly increasing on $[s_*,1]$.
At every minimizer with $s_*<s<1$, $X,Y$ are nonzero rank-one
matrices and

$$
t=\sqrt{PQ-R^2}\geq0,\qquad
v=s-t=\sqrt{UV-R^2}\geq0.
\tag{AS.30}
$$

Proof. Convexity follows by interpolating feasible points in the convex
graph (AS.27). To lower strength from $s>0$ to $\sigma\in[0,s]$,
replace $t$ by $\sigma t/s$ and keep $P,Q,R$ fixed. The real
off-diagonal of $Y$ also scales by $\sigma/s$, so both determinant
constraints improve, and all tilt conditions and the cost are unchanged.
This proves monotonicity. If $s_*<a<b\leq1$, convexity gives

$$
V(a)\leq F+\frac{a-s_*}{b-s_*}(V(b)-F)<V(b),
\tag{AS.31}
$$

using $V(b)>F$; the case $a=s_*$ follows from Lemma 5.1.

At a later minimizer put $x=\sqrt{PQ-R^2}$ and
$y=\sqrt{UV-R^2}$. Positivity gives $s\leq x+y$, while

$$
x+y\leq\sqrt{PQ}+\sqrt{UV}\leq
\sqrt{(P+U)(Q+V)}=1.
\tag{AS.32}
$$

If $x+y>s$, changing strength to $x+y$ and $t$ to $x$ preserves
feasibility and cost, contradicting strict increase. Thus $x+y=s$.
The inequalities $|t|\leq x$, $|s-t|\leq y$ force (AS.30), so both
determinants vanish. $X=0$ contradicts $W\geq F>0$.
$Y=0$ has cost $A+B$, beaten by the feasible
$(1-\zeta)Z_s$ in Definition 4.5. Thus both are nonzero, and for
$s<1$ both have rank one. $\square$

**Lemma 5.3 (positive difference and saturated tilt, globally).** At
every later minimizer, $R\geq0$, $d>0$ and
$d^2+4\alpha R^2=\beta^2$.

Proof. Replacing negative $R$ by $|R|$ preserves all constraints
and strictly reduces $W$, since $\gamma>0$.
Suppose $d\leq0$. From $U\leq\alpha V$,
$P-Q\geq(1-\alpha)(1-Q)\geq0$; equality requires $P=Q=1$,
which would give $Y=0$, already excluded. Thus $P>Q$.
Swapping $P,Q$ in $X$ while keeping its off-diagonal gives
$X_{\rm swap}$ with both $X_{\rm swap}$ and $Z_s-X_{\rm swap}$ PSD:
the diagonal products and off-diagonal moduli are unchanged.
A mixture of size $\varepsilon>0$ decreases $W$ by
$\varepsilon(A-B)(P-Q)>0$ and increases $d$ by
$\varepsilon a_{\rm mix}$, $a_{\rm mix}=(1+\alpha)(P-Q)>0$.

For $d<0$, small mixtures remain negative and retain the $R$ bound.
For $d=0$ with $2\sqrt\alpha R<\beta$, feasibility follows by
continuity. At $d=0$, $2\sqrt\alpha R=\beta$, also replace $R$ by
$R(1-K\varepsilon^2)$, where
$K>a_{\rm mix}^2/(2\beta^2)$ is fixed. Reducing $|R|$ improves the
PSD inequalities; the new disk expression is

$$
\varepsilon^2a_{\rm mix}^2+\beta^2(1-K\varepsilon^2)^2
\leq\beta^2
\tag{AS.33}
$$

for sufficiently small positive $\varepsilon$. The cost correction is
$2\gamma RK\varepsilon^2$, so the linear decrease persists. This
excludes $d\leq0$ without extending a local positive-$d$ theorem to
the whole cone.

Now the outer bound is the disk $m=\sqrt{d^2+4\alpha R^2}\leq\beta$.
If $m<\beta$, scaling $X$ to $(1-\varepsilon)X$ preserves
$0\preceq X\preceq Z_s$ and, by continuity, the strict disk condition
for small $\varepsilon$. Its positive cost decreases. Hence $m=\beta$.
$\square$

**Proposition 5.4 (the uniquely selected later root).** The interval
$I_s$ is nonempty, its radicals are positive, and (AS.18) has precisely
one root there. It evaluates $V(s)$ by the middle line of (AS.19).

Proof. At a later minimizer let $u=U+\alpha V$. Lemmas 5.2–5.3 give

$$
v=\frac{\sqrt{u^2-\beta^2}}{2\sqrt\alpha},\qquad
R=\frac{\sqrt{\beta^2-d^2}}{2\sqrt\alpha}.
\tag{AS.34}
$$

For $s<1$, $Z_s$ is positive definite. Since $Y$ and $X=Z_s-Y$
are rank one, whitening $Y$ by $Z_s$ gives eigenvalues $1,0$.
Equivalently $\operatorname{tr}(Z_s^{-1}Y)=1$, or
$U+V-2sv=j$. In the variables of (AS.17) this reads

$$
a_0u-b_0\sqrt{u^2-\beta^2}=c_s(d).
\tag{AS.35}
$$

The left side for $u\geq\beta$ has minimum $\beta\sqrt\Delta$ at
$u=a_0\beta/\sqrt\Delta$. Thus $d\geq d_{\min}$. Its larger
solution is exactly $u_s(d)$; it is genuine, since

$$
u_s\geq a_0\beta/\sqrt\Delta\geq\beta,\qquad
a_0u_s-c_s=\frac{b_0(b_0c_s+a_0e_s)}\Delta>0.
\tag{AS.36}
$$

Here $s>0$; at the lower discriminant endpoint the same last expression
is positive. Some smaller roots of the squared equation need not solve
(AS.35); only genuine smaller solutions are compared.

For every $0\leq d\leq\beta$ with $c_s(d)\geq\beta\sqrt\Delta$,
use the larger solution to set
$U=(u_s+d)/2$, $V=(u_s-d)/(2\alpha)$ and the entries (AS.34).
Then $U,V\geq0$, $Y\succeq0$, $\det Y=0$ and
$\operatorname{tr}(Z_s^{-1}Y)=1$. Whitening therefore proves
$0\preceq Y\preceq Z_s$, with $X=Z_s-Y$ rank-one PSD.
This proves feasibility of the larger solution, including its
unsquared sign. A smaller genuine solution has smaller $u$ and
strictly greater cost because $w_A>0$.

It remains to maximize, on the possible closed $d$ interval,

$$
\mathscr J_s(d)=w_Au_s(d)+w_Bd+n\sqrt{\beta^2-d^2},\qquad
W=A+B-\mathscr J_s(d).
\tag{AS.37}
$$

This maximization will now be evaluated. On $I_s$ direct
differentiation gives

$$
\begin{aligned}
u_s'&=\frac{1-\alpha}\Delta\left(a_0+\frac{b_0c_s}{e_s}\right),\\
u_s''&=-\frac{b_0(1-\alpha)^2\beta^2}{e_s^3}<0,\\
\mathscr J_s''&=w_Au_s''-\frac{n\beta^2}{(\beta^2-d^2)^{3/2}}<0.
\end{aligned}
\tag{AS.38}
$$

The exact identity

$$
c_s(\beta)^2-\Delta\beta^2
=4\alpha j[\beta k+\alpha j]>0
\tag{AS.39}
$$

gives $d_{\min}<\beta$ and finite $u_s'(\beta)$.
Hence $\mathscr J_s'\to-\infty$ at the upper endpoint. If
$d_{\min}\geq0$, it tends to $+\infty$ at the lower discriminant
endpoint, including $d_{\min}=0$. If $d_{\min}<0$, it has at zero
the positive bound

$$
\mathscr J_s'(0)\geq
\frac{w_A(1-\alpha)}{1+\alpha}+w_B
=\frac{A-B}{1+\alpha}>0.
\tag{AS.40}
$$

Thus there is exactly one derivative root, and strict concavity makes
it the unique global maximizer on the whole possible interval.
Neither a discriminant-zero endpoint nor $d=0$ nor $d=\beta$ can
minimize $W$. This proves (AS.18), the value formula, and
$0<d_s<\beta$, $e_s(d_s)>0$, $R>0$.
Since $b_0>0$, the larger solution has $u_s>\beta$, so $v>0$.
Nonzero rank-one $X,Y$ with $R>0$ imply $P,Q,U,V>0$.
Equation (AS.30) supplies $t\geq0$; strict positivity follows below.
No variational problem remains in (AS.19). $\square$

Proof of Proposition 3.3. On $I_s$, $c,e_s,r,d,N$ are positive and

$$
L\geq\frac{w_A(1-\alpha)}{1+\alpha}+w_B
=\frac{A-B}{1+\alpha}>0,
\tag{AS.41}
$$

because $\Delta\leq a_0^2$. Equation (AS.18) is
$nd/r=L+Nc/e_s$, equivalently $e_s(nd-Lr)=Ncr>0$.
Squaring once gives
$\mathcal P(d)=2ndLr e_s^2>0$; squaring again gives (AS.21).
Each term of $\mathcal P$ has degree at most four, so the carrier
has degree at most eight. Conversely its positive $\mathcal P$ filter
recovers $\mathcal P=2ndLr e_s^2$. Rearrangement gives
$e_s^2(nd-Lr)^2=N^2c^2r^2$. The other filter $nd>Lr$ recovers
$e_s(nd-Lr)=Ncr$, exactly the original equation. Both squarings
are therefore reversible with the stated filters; Proposition 5.4
proves uniqueness over their entire interval. $\square$

## 6. A positive full-class certificate and the closed endpoint

**Theorem 6.1 (explicit universal lower certificate).** At $s_*<s<1$
write $u=u_s(d_s)$ and form

$$
\begin{gathered}
U=(u+d_s)/2,\quad V=(u-d_s)/(2\alpha),\quad P=1-U,\quad Q=1-V,\\
R=\frac{\sqrt{\beta^2-d_s^2}}{2\sqrt\alpha},\quad
v=\frac{\sqrt{u^2-\beta^2}}{2\sqrt\alpha},\quad t=s-v,\\
\cos\theta=d_s/\beta,\quad \sin\theta=2\sqrt\alpha R/\beta,\quad
0<\theta<\pi/2.
\end{gathered}
\tag{AS.42}
$$

Use $X,Y$ from (AS.26), and $B=B_{\theta,DT}$. Define

$$
\begin{gathered}
f_u=a_0-su/v=\frac{e_s(d_s)}{\sqrt{u^2-\beta^2}}>0,\qquad
\mu=\frac{\alpha A+B}{f_u}>0,\qquad \nu=\mu t/v,\\
\lambda=\frac{\beta}{2\alpha}
 \left(\frac{\gamma}{R}-\frac{\mu s}{v}\right),\qquad
k_\theta=(1-\alpha)\cos\theta-\beta .
\end{gathered}
\tag{AS.43}
$$

Then $\lambda,\mu,\nu,k_\theta,t$ are strictly positive and finite.
For every normalized necessary outer competitor $X',Y'=Z_s-X'$,

$$
\boxed{\operatorname{tr}(C_{DT}X')-W
=\lambda[\beta-\operatorname{tr}(BY')]
 +\mu\operatorname{tr}(\operatorname{adj}(X)X')
 +\nu\operatorname{tr}(\operatorname{adj}(Y)Y')\geq0.}
\tag{AS.44}
$$

Together with Proposition 4.2 and Lemma 4.3 this is a lower bound for
every original finite complex competitor, allowing arbitrary failure
splitting and high acquisition later failing.

Proof. Put $w_u=\sqrt{u^2-\beta^2}$. The larger-root formula gives
$w_u=(b_0c_s+a_0e_s)/\Delta$ and
$a_0w_u-b_0u=e_s$, proving the formula for $f_u$.
Entrywise, the root equation implies

$$
C_{DT}-\lambda B=\mu\operatorname{adj}(X)-\nu\operatorname{adj}(Y).
\tag{AS.45}
$$

Here are all four independent entry checks. The real off-diagonal is
$-\mu t+\nu v=0$. The imaginary off-diagonal is
$(\mu+\nu)R=\mu sR/v=\gamma-\lambda\sqrt\alpha\sin\theta$.
The $\alpha$-weighted diagonal equation is
$\alpha A+B=\mu[a_0-su/v]$. The other diagonal equation is

$$
\mu(1-\alpha)+\alpha A-B=\gamma d_s/R.
\tag{AS.46}
$$

Indeed multiply (AS.18) by $2\alpha$ and use
$u_s'=(1-\alpha)w_u/e_s=(1-\alpha)/f_u$.
These equations verify the whole matrix identity, without a scalar-only
stationarity assumption.

Since $\operatorname{tr}(BY)=\beta$,
$\operatorname{tr}(BX)=k_\theta$,
$\operatorname{tr}(\operatorname{adj}(X)X)=0$ and
$\operatorname{tr}(\operatorname{adj}(Y)X)=\det Z_s=j$, tracing
(AS.45) against $X$ gives

$$
W+\nu j=\lambda k_\theta.
\tag{AS.47}
$$

Initially $\nu\geq0$ by (AS.30). If $k_\theta<0$, scaling $X$ to
$(1-\varepsilon)X$ keeps both PSD conditions, and the active disk's
directional derivative is

$$
\frac{d_s((1-\alpha)-d_s)-4\alpha R^2}{\beta}
=k_\theta<0.
\tag{AS.48}
$$

For small $\varepsilon$ this is a feasible cost decrease, a contradiction.
Thus $k_\theta\geq0$. All quantities in (AS.47) are finite and $W>0$,
so $k_\theta\ne0$ and $\lambda>0$.

For $X',Y'$, the true full-cone tilt yields
$\operatorname{tr}(BY')\leq\beta$. Both adjugates in (AS.44) are
PSD, since $X,Y$ are rank-one PSD. Subtract (AS.47) from the trace
of (AS.45) against $X'$ and use
$\operatorname{tr}(\operatorname{adj}(Y)Z_s)=j$ to obtain exactly
(AS.44). The tilt has positive cosine, so it remains valid on the
whole complex singular plane, also when the competitor has $d'\leq0$.

Finally, if $t=0$, then $\nu=0$. The matrix
$C_{DT}-\lambda B=\mu\operatorname{adj}(X)$ is PSD and the same
tilt at strength zero has constant $\lambda k_\theta=W$:
$\operatorname{tr}(BZ_\sigma)=(1-\alpha)\cos\theta$ is independent
of $\sigma$. It would imply $F=V(0)\geq W=V(s)>F$.
Thus $t>0$ and $\nu>0$. This proves every certificate sign.
$\square$

**Proposition 6.2 (strength one without singular divisions).** Let
$z_0=\beta/(1-\alpha)$ and $q_{\rm end}=1-z_0=k/(1-\alpha)$.
Every original competitor at $s=1$ has cost at least
$q_{\rm end}(A+B)$.

Proof. $Z_1$ has rank one. Positive support domination gives
$X=qZ_1$, $0\leq q\leq1$, so $P=Q=t=q$, $R=0$ and
$U=V=1-q$. The $\theta=0$ full-cone tilt gives
$(1-\alpha)(1-q)\leq\beta$, hence $q\geq q_{\rm end}$.
Its cost is $q(A+B)$. The endpoint construction below supplies
equality in the original class. No inverse of $Z_1$, division by $j$
or continuation through a zero discriminant is used. $\square$

## 7. Actual finite equality instruments

**Lemma 7.1 (interior true-cone atoms and physical ranks).** For the
selected entries (AS.42), define

$$
\begin{gathered}
u_L=\frac{\beta+\sqrt{\beta^2+4\alpha v^2}}2,\qquad
v_L=\frac{-\beta+\sqrt{\beta^2+4\alpha v^2}}{2\alpha}>0,\\
R_\theta=\begin{pmatrix}
\cos(\theta/2)&-i\sqrt\alpha\sin(\theta/2)&0\\
-i\sin(\theta/2)/\sqrt\alpha&\cos(\theta/2)&0\\0&0&1
\end{pmatrix},\\
h_r=\frac1{\sqrt2}\left(\sqrt P,\frac{rt+iR}{\sqrt P},0\right)^T,
\qquad
z_{r,\pm}=\frac12R_\theta(\sqrt{u_L},r\sqrt{v_L},\pm1)^T.
\end{gathered}
\tag{AS.49}
$$

Then $h_rh_r^\dagger=H_r$ and
$\sum_\pm z_{r,\pm}z_{r,\pm}^\dagger=L_r$ in (AS.24).
Every $K(z_{r,\pm})$ has physical rank two, and both $K(h_r)$
have physical rank three.

Proof. $u_L-\alpha v_L=\beta$ and $u_Lv_L=v^2$. Direct bilinear
multiplication gives $\det R_\theta=1$,
$R_\theta^TB_0R_\theta=B_0$, and
$R_\theta X_cR_\theta^\dagger=X_c$. The two real precongruence
low vectors are quadratic-null; their sum of projectors is

$$
\frac12\begin{pmatrix}u_L&r v&0\\r v&v_L&0\\0&0&1\end{pmatrix}.
\tag{AS.50}
$$

On its $DT$ block the congruence preserves the real off-diagonal,
sends the diagonal difference $\beta$ to $\beta\cos\theta=d_s$,
and sends imaginary entry zero to
$\beta\sin\theta/(2\sqrt\alpha)=R$. Its determinant remains zero.
The positive diagonals with this difference and determinant are
uniquely $U,V$, proving the low moment identity. Equation (AS.30)
proves the high identity. This uses $R_\theta$ only on these
quadratic-null atoms, and makes no full plane-plus-quadratic cone
automorphism claim.

Each low vector's $D$ coefficient has nonzero real part
$\cos(\theta/2)\sqrt{u_L}/2$; Lemma 4.1 supplies its nonzero
$1,2$ minor and physical rank two. Each high $T/D$ ratio is
$(rt+iR)/P$, with nonzero imaginary part. With zero $S$ coefficient,
singularity would require the real ratios $\pm1/\sqrt\alpha$.
Thus the high physical matrices are invertible. All inequalities
$P,Q,U,V,R,t,v>0$ hold throughout the open later interval.
$\square$

**Definition 7.2 (twelve actual interior labels).** For each nonzero low
$z=z_{r,\pm}$ fix an isometry $V_z:\mathbb C^2\to\mathbb C^3$ onto
$\operatorname{ran}K(z)$. One explicit choice normalizes specimen
column $1$, subtracts its projection from column $2$, and normalizes
the residual. The nonzero $1,2$ minor ensures both denominators are
positive. All choices depend only on public $\rho,s$.

For each $r=\pm1$ supply the following six acquired labels.

| Label | Whole joint fibre dimension | Encoder | Whole-fibre full-output decoder |
| --- | --- | --- | --- |
| $(r,H)$ | $3$ | Kraus matrix $K(h_r)E^\dagger$ | $X\mapsto EXE^\dagger$ in live |
| $(r,L,+)$, $(r,L,-)$ | $2$ each | Kraus matrix $V_z^\dagger K(z)E^\dagger$ | $X\mapsto EV_zXV_z^\dagger E^\dagger$ in live |
| $(r,f,1)$, $(r,f,2)$ | $1$ each | row $\sqrt{m_j/2}\langle j|E^\dagger$ | scalar $a\mapsto a w_\ell g(t)dt\,P_f$ in each original label $\ell$ |
| $(r,\perp)$ | $1$ | CP map $A\mapsto\operatorname{tr}(Q_5A)/2$ | scalar $a\mapsto a g(t)dt\,P_f$ only in original label $2$ |

The complement map has two Kraus rows but a scalar quantum output;
its multiplicity is discarded. The actual dephased classical label
and the whole stated fibre remain accessible, and every other
input-dependent dilation system is permanently inaccessible before
the cut. On a supported selected input the complement probabilities
are zero, but its two maps remain part of the full-algebra instrument.
The report is the actual retained $r$; no inaccessible old Kraus
index is made readable by this definition.

**Theorem 7.3 (normalization, complete effects and full output).**
Definition 7.2 is one common normalized finite instrument, with
full TP decoders, exact effects (AS.10), exact channel (AS.8), and
actual acquired cost $W=V(s)$.

Proof. Each live decoder is an isometry on its entire fibre.
Each scalar decoder is TP because $\sum_\ell w_\ell=1$ and
$\int_0^1g=1$. Image reconstruction gives
$V_zV_z^\dagger K(z)=K(z)$, so compressed branches have unchanged
effects and decoded products $EK(z)E^\dagger$. The moment identities
are

$$
H_r+L_r=(I_3+r sX_c)/2,\quad
\Theta(I_3)=I_3-M,\quad \Theta(X_c)=\kappa X_{01}.
\tag{AS.51}
$$

Adding the supported scalar effect $EME^\dagger/2$ and complement
effect $Q_5/2$ to the live effect at report $r$ gives exactly
$(I_5+r s\kappa EX_{01}E^\dagger)/2$. Their total is $I_5$.
Each individual positive encoder effect is bounded by this total, so
every encoder is TNI. There is no branch, survival or acceptance
normalization.

Summing both reports makes the live coefficient moment $I_3$,
therefore for every complex $A\in M_5$ the forgotten live map is
the first line of (AS.8). The scalar rows sum to $M$ and the complement
maps to $Q_5$, giving the second line separately for every original
label and every Borel time set. The two side labels $1,3$ remain
distinct; labels $0,4$ (the latter originally mode $13$) remain
zero. No singular or endpoint atom is added. All cross-support
operators, complement live outputs and additional sectors have zero
image, and common fixed metadata remain identical.

For a joint trace-class operator $X_{\rm joint}$ with any passive
reference, tensor each live product with the reference identity.
At each report the exact scalar reference factors are

$$
\begin{aligned}
R_{f,r}&=\operatorname{Tr}_5[(E(M/2)E^\dagger\otimes I)X_{\rm joint}],\\
R_{\perp,r}&=\operatorname{Tr}_5[(Q_5/2\otimes I)X_{\rm joint}].
\end{aligned}
\tag{AS.52}
$$

Thus the output in label $\ell$ on Borel $B$ is

$$
\left(\int_B g(t)dt\right)
P_f\otimes[w_\ell R_{f,r}+\mathbf1_{\ell=2}R_{\perp,r}].
\tag{AS.53}
$$

These are conditional Kraus-row partial traces, not unconditional
reference marginals. Summing reports proves the full amplification of
(AS.8). Matrix-unit identities prove every finite amplification;
trace-class finite-rank approximation gives any stipulated infinite
passive-reference version. Consequently all twelve original HALF
complete-cq error constraints retain the conditional value (AS.9),
including height $16$ and every live coherence and zero sector.

Only the two $H$ labels have fibre dimension at least three. Their
actual acquired effect is

$$
G_{\rm acq}=E\Theta(H_++H_-)E^\dagger,\qquad
\operatorname{tr}(G_{\rm acq}E\rho E^\dagger)
=AP+BQ-2\gamma R=W.
\tag{AS.54}
$$

Their whole decoders happen to be live, as a choice of this attainer.
The lower argument retained arbitrary high acquisition later failing.
Thus $E_s\leq V(s)$, while Section 4 gives $E_s\geq V(s)$.
This establishes equality in value of the outer problem by an actual
true-cone construction, without claiming all outer points realizable.
$\square$

**Proposition 7.4 (closed plateau instruments, credited to NP/QO).**
For $0\leq s\leq s_*$ take high vectors $h_*/\sqrt2$ at the two
reports. Put

$$
u_*=\frac{\beta+\sqrt{\beta^2+4\alpha s_*^2}}2,\quad
v_*=\frac{-\beta+\sqrt{\beta^2+4\alpha s_*^2}}{2\alpha},\quad
T_r=\frac12\begin{pmatrix}u_*&r s&0\\r s&v_*&0\\0&0&1\end{pmatrix}.
\tag{AS.55}
$$

Each $T_r$ is real PSD with $\operatorname{tr}(B_0T_r)=0$,
rank three below $s_*$ and rank two at $s_*$. Decompose it into
rank-many real quadratic-null projectors, then apply $R_{\theta_0}$
to each vector. Their sum is
$L_r=(I_3-H_*+r sX_c)/2$.

For completeness the finite decomposition requires no oracle: factor
$T=YY^T$ on its support. The real symmetric compression
$Y^TB_0Y$ has trace zero. If nonzero, a zero Rayleigh unit vector
exists between a positive and a negative eigenvector; remove it and
repeat on its orthogonal complement, whose trace remains zero.
A zero compression permits any orthonormal basis. Multiplication by
$Y$ gives rank-many real null vectors. This is the IR/CA real-null
decomposition on the support. A nonzero real null vector has nonzero
$D$ coefficient; its transform under $R_{\theta_0}$ still has
nonzero real $D$ part. All low physical products therefore have rank
two. The claimed moment identity follows from the same congruence
calculation as Lemma 7.1: the complementary $DT$ block has
$U-\alpha V=\beta c_0$, imaginary entry $r_0$ and real entry $rs$.
Its inverse congruence is exactly the real block in (AS.55).

Both high physical products have imaginary nonzero $T/D$ ratio,
so remain rank three even at $s_*$. Add the four supported scalar
labels and two complement labels of Definition 7.2 with the same
whole TP decoders. There are fourteen labels for $s<s_*$ and
twelve at $s_*$. Equations (AS.51)–(AS.54) apply verbatim and give
actual cost $F$. Here a complete low coefficient block drops rank;
the high physical Kraus rank does not drop. $\square$

**Proposition 7.5 (actual strength-one equality).** With
$z_0=\beta/(1-\alpha)$ and $q_{\rm end}=1-z_0$, use

$$
h_r=\sqrt{q_{\rm end}}(1,r,0)^T/\sqrt2,\qquad
z_{r,\pm}=(\sqrt{z_0},r\sqrt{z_0},\pm1)^T/2 .
\tag{AS.56}
$$

Their moments are (AS.24) with
$P=Q=t=q_{\rm end}$, $R=0$, $U=V=v=z_0$.
The low vectors are quadratic-null with nonzero $D$ coefficient,
so their physical products have rank two. The high determinant is
nonzero, since its $T/D$ ratio is $r$ and $1-\alpha>0$;
$q_{\rm end}>0$ follows from $k>0$. The range encoders and all
six scalar/complement labels from Definition 7.2 give twelve actual
labels, with every full normalization, effect, complex/reference and
Borel-time identity proved in Theorem 7.3. Their acquired cost is
$q_{\rm end}(A+B)$, proving the reverse inequality in Proposition 6.2.
$\square$

Every construction fixes all matrices, range choices and kernels
before receiving the sole specimen. A finite dilation uses the
encoder Kraus matrices with an orthogonal environment copy of branch
and multiplicity. The joint effect identity makes that map isometric;
tracing the copy dephases the actual label. All unretained shares
are discarded permanently before the cut. This specifies new supplied
CP operations; it grants no access to an environment discarded by
some other implementation.

## 8. Limits, onset, scaling and original-input comparisons

**Theorem 8.1 (closed limits and curve regularity).** On the open later
branch the selected reduced arrays satisfy

$$
\begin{aligned}
(P,Q,R,t,d_s)&\longrightarrow(p,q,r_0,0,\beta c_0)
&& (s\downarrow s_*),\\
(U,V,v)&\longrightarrow(z_0,z_0,z_0),\quad
(P,Q,t)\longrightarrow(q_{\rm end},q_{\rm end},q_{\rm end}),\quad
R\longrightarrow0,\quad d_s\longrightarrow\beta
&& (s\uparrow1).
\end{aligned}
\tag{AS.57}
$$

Proof. Mix the attained plateau endpoint instrument with the attained
strength-one instrument, retaining the independent choice as an actual
classical label. Both forget to the same complete channel; the full
effects interpolate affinely. As $s\downarrow s_*$ the resulting
cost tends to $F$. The universal lower bound gives $V(s)\to F$.
Compactness of the outer matrices and the unique equality in Lemma
5.1 force every subsequential reduced limit to $(p,q,r_0,0)$.
Since $d=(1-P)-\alpha(1-Q)$, its limit is $\beta c_0$.

At one, monotonicity gives a left limit at most $V(1)$. Every compact
subsequential matrix limit is feasible at one, and therefore has
cost at least $V(1)$; this proves equality of the limit. Also
$d_{\min}(s)\to\beta$ and $d_{\min}<d_s<\beta$, hence $d_s\to\beta$.
Equation (AS.17) gives
$u_s(d_s)\to(1+\alpha)\beta/(1-\alpha)$ and then all remaining
limits in (AS.57).

Within $(s_*,1)$, $e_s,r,v,f_u$ and every range denominator have
strict positive margins. The derivative of the defining scalar
equation with respect to $d$ is $\mathscr J_s''<0$.
The real analytic implicit-function theorem gives local real
analyticity at every point; uniqueness joins these into the one
branch throughout the interval. The physical ranks in Section 7
remain fixed there. Convexity and strict increase follow from
Lemma 5.2, now that $E_s=V(s)$ on all branches. This proves all
regularity claims in Theorem 3.2. No endpoint derivative or
input-uniform limit is inferred. $\square$

**Convention 8.2 (the already evaluated sharp onset).** To identify the
credited QO coefficient exactly, put

$$
\begin{gathered}
p_1=\frac{\beta\sigma_0}{2}\left(1+\frac{1-\alpha}{Z_0}\right),\quad
q_1=\frac{\beta\sigma_0}{2\alpha}
 \left(\frac{1-\alpha}{Z_0}-1\right),\quad
r_1=\frac{\beta c_0}{2\sqrt\alpha},\\
a_{\rm curv}=\frac{d_{\rm cert}}p=\frac{\alpha A+B}{Z_0},\quad
b_{\rm rec}=-\frac{p_1+q_1}{2s_*}<0,\\
c_{\rm curv}=\frac{\lambda_0\beta}{2}
 +a_{\rm curv}(\sqrt{q/p}\,p_1-r_1)^2>0,\quad
D_{\rm onset}=\frac1{a_{\rm curv}}+\frac{b_{\rm rec}^2}{c_{\rm curv}},
\quad K_{\rm onset}=D_{\rm onset}^{-1}.
\end{gathered}
\tag{AS.58}
$$

QO proves for each fixed admitted input, uniformly over original
competitors in its lower bound,
$E_{s_*+\varepsilon}=F+K_{\rm onset}\varepsilon^2+O(\varepsilon^3)$,
with $0<K_{\rm onset}<a_{\rm curv}$, and supplies an actual twelve-label
matching asymptotic path. Its normalized necessary-array slopes are
$x/\varepsilon\to1/(a_{\rm curv}D_{\rm onset})$ and
$(\theta-\theta_0)/\varepsilon\to b_{\rm rec}/
(c_{\rm curv}D_{\rm onset})<0$, with radial slack $o(\varepsilon^2)$.
Here $x=\sqrt{PQ-R^2}$ and the radial slack is $\beta-m$.
These are statements about reduced arrays, not whole-instrument
uniqueness. Since (AS.19) evaluates the identical optimization, it has
this same onset; the coefficient and local path are not counted again
as the later-interval increment. There is no input-uniform cubic
constant or radius, nor a theorem at $\xi=0$ or singular limits.

**Proposition 8.3 (homogeneity and equivalent descriptions).** For every
positive five-mode $\sigma$ with $E^\dagger\sigma E=t\rho$, $t>0$,

$$
E_s(\sigma)=tE_s(\rho)\qquad(0\leq s\leq1).
\tag{AS.59}
$$

The lower effect inequality (AS.23) multiplies the selected lower
bound by $t$; the high effects (AS.54) are supported on
$\operatorname{ran}E$ and give equality. No acceptance division is
introduced, even with complement or cross-support components.
If compression is zero, positivity kills the cross block and the
minimum is zero: factor $(I_3+r sX_c)/2$ into finitely many
supported high columns, and add the same scalar completions.
Its high mass on $\sigma$ is zero and nonnegativity is the lower
bound. This separate argument uses no singular Gram inverse.

Conjugate public states use separately fixed conjugated encoders and
range maps. The real source and full effects are preserved; no physical
conjugation of an unknown state is invoked. Negative strength exchanges
report names. A global coefficient phase does not change a CP branch.
These are exact equivalences at their stated scope, not uniform
continuity results at a nonadmitted or singular input. $\square$

**Proposition 8.4 (the simultaneous original twelve-vector).** For
each selected instrument above, all original history costs are
$PA_y+QB_y$, where
$A_y=\sum_i h_i^2p_{yi}$ and $B_y=b^2p_{y0}+a^2p_{y1}$; on the
plateau use $P=p,Q=q$ and at one use $P=Q=q_{\rm end}$.
The high aggregate has only imaginary $DT$ cross entry; the original
states and their Grams are real, so this entry contributes zero for
every sign, without averaging. At $s_*$, $p>k$, $q>0$ and
$s_*<\sqrt\ell$. Continuity preserves $P>k$, $Q>0$ and
$s<\sqrt\ell$ in a right neighborhood. The one JR weak instrument
has the simultaneous vector $kA_y$ there, at the same full effects
and complete channel. It strictly dominates every original coordinate.
This retains the NP/QO comparison and gives no new original-twelve
Pareto point. The entire twelve-coordinate undominated frontier is
not evaluated by selected nonreal minima. $\square$

## 9. Mathematical credit and the different current height-record task

**Convention 9.1 (antecedents and the precise additional content).**
CG denotes [Complete continuation distinguishability][CG], IR the
[interior record reduction][IR], CA the [complex atomic cone][CA],
RG the [real-Gram resource law][RG], and JR the
[complete continuation joint record][JR]. NP denotes
*Native nonreal inputs and an exact maximal resource plateau*, QO
*A sharp quadratic resource onset for native nonreal inputs*, and PG
*Physical singular coefficient Grams and maximal real resource plateaus*.
CG supplies the calibrated twelve histories and targets, algebraic
point, source ranks, normalization and enclosures, bordered-Jacobian
and minimax premises, complete channel, sign-averaged live rigidity,
Schmidt bottleneck, stability and actual acquisition framework.
Its averaged statement is not whole-channel optimizer uniqueness.
IR and CA supply arbitrary finite complex coefficient necessity,
arbitrary binary live/failure freedom, acquired effect at least high
live effect, the compact exact coefficient reduction and finite
attainment, and the full plane-plus-quadratic cone with plane slack
and Takagi condition. CA's real exposed trace-zero face, up-to-six
low atoms and generic at-most-twenty-four-branch realization, and its
resource-face classification remain prior results. A scalar trace
condition alone is insufficient for that complex cone.

RG supplies the real positive-definite small-record spectral law,
two lifts, sufficient caps and fourteen-label instruments, and the
selected-coordinate versus simultaneous-vector distinctions.
NP supplies exactly the admitted physical nonreal family, its
nonempty interval and strict source sign, full-cone tilts, maximal
plateau and equality aggregate, fourteen/twelve-label plateau
attainers, quartic lower and affine later bounds, scalar-trace
separation and original-vector domination. QO supplies the sharp
quadratic onset (AS.58), competitor-uniform fixed-input cubic lower
estimate, normalized slopes and actual local matching path.
These are antecedents, not fresh contributions of this companion.

The all-strength proposal and its supplied check provide ordinary
arguments subject to their source conditions. Sections 4–8 give the proof,
including the larger root's genuine unsquared sign, its whitening
feasibility, global exclusion of $d\leq0$, active disk, reversible
polynomial filters, every certificate sign and all normalization
identities. Author or reviewer approval supplies no mathematical premise.
The precise additional relation relative to NP/QO is the complete
later-interval evaluation by one selected algebraic root, its
full-class certificate, actual twelve-label equality instruments,
the separately evaluated endpoint, and the connected analytic branch
and limits. This is a repository synthesis with ordinary proofs;
no worldwide originality or priority is asserted.

**Convention 9.2 (physical singular results already available).** The
physical singular-Gram volume PG establishes that every nonzero
physical Gram has rank two or three, and any specimen of rank at
least two has positive-definite Gram. With
$r_T=ah_1/(bh_0)$ and $r_S=ch_2/(d_{\rm src}h_0)$, pure
$\psi=(x,y,z)$ is singular exactly when $x=0$ or
$x^2=r_Ty^2+r_Sz^2$. It classifies kernels and realizes every
complex singular coefficient line physically. Its singular pencil
has the exact polynomial
$\lambda(d_1+d_2\lambda-\alpha\beta\lambda^2)$ with the stated
simple-zero/positive-root and real-quadratic double-zero distinctions.
PG gives a direct real quadratic-singular spectral law, without
inverting $C$, and the saturated equality/report-split theorem
upgrading sufficient real lifts to exact maximal initial caps.
That theorem includes real positive-definite saturated and transition
cases and all twelve original selected histories; it is not merely
a singular-limit heuristic. The entire specimen plane $\rho_{00}=0$,
including complex and mixed tests, has exact $kA$ plateau precisely
through $s=\sqrt\ell$. Its two real boundary tests have closed
radical values and caps. Its explicit nonreal singular specimen
has a strict true-cone versus scalar-relaxation gap at every strength,
with the scalar relaxation evaluated at zero strength.

Those PG conclusions are credited at their exact domains. Broader
singular and general-coherence all-strength questions remain open;
calling every singular question unresolved would discard established
content. The current positive-definite admitted family does not
resolve those remaining questions.

**Convention 9.3 (current JR scope through Section 52).** JR's original
joint winding/resource law optimizes over all original error optimizers,
uses a contrast inequality with other effect coordinates free, and
imposes sharp worst-history cost before optimizing height-record TV.
Its four-sign average lower frontier, inverse budget, common H/L
attainers, supported sharp-cost rigidity, strong-regime height-TV
evaluation and spectral failure-record gain remain credited. So do
the weak four-real-PSD reduction, finite attainment, all-label
three-low comparison, and the specified symmetric point's strict
improvement.

The current JR Sections 50–52 go further. In their normalized real-null
problem, $L=\operatorname{diag}(\sqrt\ell,1,1)$,
$\omega/\delta=\beta/\ell$ in their notation, and $G=LNL$ is the
height-difference matrix, not the selected Gram $C$ here.
Their isolated real-null stationary vector $v_*$, its spectral
value $\mu_*<0$, and the orthonormal real-null frame
$(v_*,u_*,w_*)$ give the aggregate three-ray optimum. They prove the
maximal initial height-TV plateau

$$
\mathcal T(s)=T_{\rm flat}-\mu_*
\quad(0\leq s\leq\bar s),\qquad
.99\,s_0<\bar s<s_0,\quad s_0=\sqrt\ell,
\tag{AS.60}
$$

with their exact endpoint $\bar s=2s_0(u_*)_0(u_*)_1$ and finite
eleven-branch common instrument, or twenty-two branches after exact
contrast attenuation retaining all original labels. Their equality
classification fixes aggregate optimal real-atom lines, not a whole
channel or an inaccessible refinement. On $(\bar s,s_0]$ their
height-TV value is strictly decreasing; they give the retained-choice
chord lower bound and the evaluated endpoint at $s_0$.
For $s<s_0$ their four-slack SDP dual has a finite attained minimum;
on the residual interior its contrast multiplier is positive and
the contrast inequality saturates. At $s_0$ the primal is finitely
attained and the dual infimum equals it but has no finite minimizer.
The remaining JR task is the exact residual curve on
$(\bar s,s_0)$, its contact rays and transitions, together with its
native obligations. Its entire initial height plateau is not open.

These height-TV results have a different objective and constraint
set from (AS.11)–(AS.12). For example JR's positive $02$ effect in
its local comparison is outside (AS.10). No optimality, resource,
TV or simultaneous-optimizer migration in either direction is
established by their coexistence.

**Convention 9.4 (mature mechanisms and inherited references).**
Positive Choi support, Gram left inverses, Kraus mixing, finite
CP/range factorization, PSD adjugates, whitening, complex triangle
and Cauchy–Schwarz inequalities, real null decomposition, convexity
and the analytic implicit-function theorem are mature tools.
The supplied library attributions include
UnitaryKrausMixingInvariance.unitary_kraus_mixing_invariance,
FiniteKrausInstrumentBornMarginal.finite_kraus_instrument_born_marginal,
FiniteKrausRepresentation, and
AntidistinguishabilityGram.psd_summand_projection, with the supplied
Physlib selection 6a09b2d1761a0d4430083045a247eb121d8da260
and mathlib pin db584cd6d46c92f209a44c0f1c829460d327499d.
These are inherited source references, not compiled applications here.
Supplied literature credit to Sekatski's finite classical-assisted
rank/image compression, Leppäjärvi–Sedlák and
Muñoz-Moller–Leppäjärvi–Heinosaari's compatible instrument mechanisms,
Uhlmann's affine-flat decomposition, and Xia–Wang–Sheu's equality
S-lemma retains each source's hypotheses. They supply no original
selected-input cost theorem, inaccessible environment or native
actuator. No new external authentication is claimed.

The supplied entropy identities, designated-subspace EOF refutation,
Schur-channel distance statements, three-point positivity gate,
orthostochastic obstruction and classical allocation score have no
established target/resource-preserving conversion to (AS.12).
The finite classical paid-query/support-incidence and joint-selection
problems and the slot-plus-bypass UNHALVED diamond model likewise
retain their own boundaries.

## 10. Operational, learning and evidence boundaries

**Convention 10.1 (abstract realization and native enactment).** The
constructed instruments supply mathematical encoders, calibrated support
and image maps, generated classical flags, coherent storage and
controlled whole-fibre TP decoding. Lawful enactment on the unknown
specimen under the original permissions remains an obligation.
Every future-accessible correlated quantum share must fit the same
jointly counted cut. Its duration and placement must fit the original
aligned clock without extra time.

For the measures (AS.8), native execution must make the FIRST
absorbing failure actually occur at elapsed $t$, absolute $6+t$,
and perform no later positive-carrier action on that branch; live
output occurs at elapsed one. A failure-destined acquired label,
an abstract Borel output density or a subsequently sampled timestamp
does not supply that event, finite exact-time storage or extra
execution time. Original stopped archives, source/preparation/epoch,
calibration, metadata, permissions and controller updates retain
their original semantics.

OriginalControlComposition.OriginalControl gives the finite-duration,
strict-domain and regularity path predicate and its composition; it
does not construct these quantum operations. The original
probability–phase fields $P=\partial_\kappa$ and
$Q=\sum_a w_a(\kappa)\partial_{h_a}$ have the supplied nonzero
double-wall commutator $-(\partial_u+\partial_v)/r$.
They prevent an exhaustive diagonal/Schur restriction, but give
neither arbitrary acquisition access nor global native impossibility.
No native feasibility, efficiency, impossibility or capacity claim
follows from the abstract exact law.

**Convention 10.2 (resource, learning and unresolved mathematics).**
$E_s$ measures future-response acquisition mass for a fixed full
channel and full binary effects. It is not a training loss,
prediction error, generalization bound, sample complexity or empirical
neural-network performance measure. No bridge to generic NN/ML is
provided by this conditional quantum optimization.

For the declared admitted family no strength interval remains
unevaluated in (AS.19). Arbitrary physical complex inputs with
general $DT,DS,TS$ coherence, the unsupplied broader singular
all-strength cases, the whole twelve-coordinate undominated frontier
and a simultaneous all-input minimizer remain separate problems.
The selected reduced-array uniqueness, finite decompositions and
certificate do not imply unique whole instruments, unique five-mode
optimizers or a general resource classification. Branch counts are
existence bounds, not minimal alphabet sizes or exact-clock
storage bounds.

All source/root/isolation/enclosure/Jacobian/minimax, calibration,
nested library, literature and native assertions remain conditional
antecedents. The proofs here are ordinary symbolic deductions with
no executed mathematics or numerical experiment, no Lean/kernel or
frozen evidence, no input-uniform or singular-limit theorem, no
worldwide priority claim and no completion claim for the wider
through-2027 programme.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[IR]: FIB_NATIVE_INTERIOR_RECORD_RESOURCE_REDUCTION.md
[CA]: FIB_NATIVE_COMPLEX_ATOMIC_CONE_AND_OPTIMAL_RESOURCE_FACES.md
[RG]: FIB_NATIVE_REAL_GRAM_SMALL_RECORD_RESOURCE_LAW.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md

## 追加锚（本行以下为增补区）
