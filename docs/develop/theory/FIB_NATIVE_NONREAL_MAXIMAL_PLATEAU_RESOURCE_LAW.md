# Native nonreal inputs and an exact maximal resource plateau

> This volume proves ordinary conditional mathematical statements. The exact
> coefficient source, its arithmetic certificates and the original calibration
> are inherited premises. No Lean verification or native implementation is
> asserted. The additional application is an evaluated family of genuinely
> nonreal physical inputs, with a maximal initial record plateau, matching
> finite instruments, quantitative later bounds and a strict same-strength
> trace-relaxation gap. The general complex-input and original twelve-vector
> programmes remain active. Extensions use the `generic-v1` append convention.

## 1. The complete original experiment

**Definition 1.1 (paths and the received specimen).** In the original
calibrated path law, take $0<Z<1$, put $r_b=1-Z$, and require
$0<X,Y<r_b$ for $b=(X,Y,Z)$. Set

$$
\begin{aligned}
J_b&=(\max(0,X+Y-r_b),\min(X,Y)),\\
\pi_b(k)&=(r_b-X-Y+k,X-k,Z,Y-k,k),\\
\mathbf d&=(1,-1,0,-1,1),\qquad
I_b(k)=\sum_{i\in\{0,1,3,4\}}\pi_b(k)_i^{-1},\\
w_b(k)_i&=\mathbf d_i/(\pi_b(k)_i I_b(k)).
\end{aligned}
\tag{NP.1}
$$

The source premises require finite duration $T\geq0$, continuous real
coordinates $k,\vartheta$, strict $k(t)\in J_b$, finite phase variation,
and either absolute continuity of both coordinates or the finite
piecewise-$C^1$ alternative with rates continuous on every closed piece.
The normalized live lift has components

$$
\sqrt{\pi_b(k(t))_i}\exp\left(-i\left[\theta_i+
 \int_0^t w_b(k(v))_i\vartheta'(v)\,dv\right]\right).
\tag{NP.2}
$$

The phase coordinate is a signed real lift; integer winding, its sign,
and literal chronological composition are retained. Zero duration permits
only matching zero displacement. Known denial or mismatch remains visible
as unexecuted rejection with its controller update. These conditional path
laws do not supply an unknown-input quantum actuator.

For this experiment $b=(1/4,1/4,1/2)$, so

$$
\pi_b(k)=(k,1/4-k,1/2,1/4-k,k),\qquad
w_b(k)=\left(\frac{1/4-k}{1/2},\frac{-k}{1/2},0,
                  \frac{-k}{1/2},\frac{1/4-k}{1/2}\right).
\tag{NP.3}
$$

Five-mode indices are $0,1,2,3,4$, with $e_4$ retaining the original
name mode $13$. Put

$$
E=\left((e_0+e_4)/\sqrt2,(e_1+e_3)/\sqrt2,e_2\right),\quad
V=\operatorname{ran}E,\quad P_5=EE^\dagger,\quad Q_5=I_5-P_5.
\tag{NP.4}
$$

Supported indices $0,1,2$ mean $(+,-,2)$ and do not rename stopped labels.
The twelve original histories have $x=y/256$, $y\in\{5,16,27\}$,
$\beta_{\rm hist}\in\{0,\pi\}$ and $m\in\{0,1\}$. From the common
preparation at height $1/8$ and zero lift, their six chronological unit
legs are as follows, with $B=8\beta_{\rm hist}-4\pi m$.

| Leg | Height | Real phase coordinate |
| --- | --- | --- |
| 1 | $1/8$ | $0\to2\pi m$ |
| 2 | $1/8\to1/16$ | $2\pi m$ |
| 3 | $1/16$ | $2\pi m\to2\pi m+B$ |
| 4 | $1/16\to1/8$ | $2\pi m+B$ |
| 5 | $1/8$ | $2\pi m+B\to2\pi m$ |
| 6 | $1/8\to x$ | $2\pi m$ |

At these heights $w_b(1/8)=(1/4,-1/4,0,-1/4,1/4)$ and
$w_b(1/16)-w_b(1/8)=(1/8,1/8,0,1/8,1/8)$. Consequently the residual
lift is $(\beta_{\rm hist},\beta_{\rm hist}-\pi m,0,
\beta_{\rm hist}-\pi m,\beta_{\rm hist})$. The height-only leg adds no
phase. Earlier reach masses $32/177,2/9,32/111$ belong to the earlier
execution; they are neither priors nor new acceptance weights.

At absolute time six ONE already reached normalized sole specimen is
received. The common continuation is $k(t)=x+6t/256$, with old phase
unchanged, $0\leq t\leq1$. Its strict common relative domain is
$(0,58/256)$ and its terminal heights are $11/256,22/256,33/256$.
For a general relative increment $A(t)$ starting at zero and
$J_b=(\ell_b,u_b)$ the legal starting-height domain is
$(\ell_b-\min A,u_b-\max A)$; this formula supplies no domain sensor.
The six-leg catalogue stays internal: populations are at least $5/256$,
height speed at most $27/256$, phase speed at most $8\pi$, and total
phase variation at most $16\pi$. No wall limit or infinite winding is used.

**Definition 1.2 (all twelve targets and full error).** Define

$$
\begin{aligned}
p_y&=(y/128,(64-y)/128,1/2),& a_y&=(\sqrt{p_{yi}})_i,\\
U_{e,n}&=\operatorname{diag}(e,n,1),&
\rho_{y,e,n}&=U_{e,n}a_ya_y^TU_{e,n}^\dagger,\\
d_y&=\left(\frac y{128},\frac{y(58-y)}{128(y+6)},
                         \frac y{2(y+6)}\right),&
B_y^{\rm tar}&=(\sqrt{d_{yi}d_{yj}})_{ij},\\
s_y&=y/(y+6),& f_y(t)&=6y/(y+6t)^2,\\
w&=(0,1/4,1/2,1/4,0),& P_f&=|f\rangle\langle f|.
\end{aligned}
\tag{NP.5}
$$

Here $e=(-1)^{\beta_{\rm hist}/\pi}$ and $n=e(-1)^m$ range
independently over $\{\pm1\}$; $en$ is winding parity. The actual
five-mode input is $E\rho_{y,e,n}E^\dagger$. Its target live block is
$EU_{e,n}B_y^{\rm tar}U_{e,n}^\dagger E^\dagger$. In EACH original
stopped label $j$ its target is the whole measure
$w_j f_y(t)dt\,P_f$. Labels $1$ and $3$ stay separate, and labels $0$
and mode $13$ stay named with zero ideal mass. Since $\int_0^1 f_y=1-s_y$
and $\operatorname{tr}B_y^{\rm tar}=s_y$, the full target has trace one.

For completeness the calibrated source-indexed target instrument has
$d=6/256$, $c_0=1/4$ and

$$
\begin{aligned}
K_x&=\operatorname{diag}\left(1,
 \sqrt{\frac{x(c_0-x-d)}{(x+d)(c_0-x)}},\sqrt{\frac{x}{x+d}}\right),\\
\mathcal I_{x,2}(dt)(A)&=\frac{dx}{(x+dt)^2}
 |f\rangle\langle2|A|2\rangle\langle f|\,dt,\\
\mathcal I_{x,j}(dt)(A)&=\frac{c_0}{2(c_0-x)}\frac{dx}{(x+dt)^2}
 |f\rangle\langle1|A|1\rangle\langle f|\,dt\quad(j=1,3),\\
\mathcal I_{x,0}&=\mathcal I_{x,4}=0.
\end{aligned}
\tag{NP.6}
$$

Their total effect on $V$ is identity. The unknown $x$ is not installed
in a common processor by writing this target family.

Available metadata and blanks are one fixed common state: no-failure
flag, aligned clock, source/preparation/epoch identity, reference
calibration, permissions and controller state. There is no readable old
height, sign, waveform, generator word, source programme, callback,
environment input port, helper specimen or history-dependent processor.
Common independent ancillas, randomness, computation, finite adaptive
instruments and retained records can be absorbed into one common CPTP map
on the whole complex input algebra. All outcomes are counted.

Let $\Omega_{y,e,n}$ denote this complete target. The original objective
and benchmark are

$$
E(\Phi)=\max_{y,e,n}\frac12\|\Omega_{y,e,n}-
 \Phi(E\rho_{y,e,n}E^\dagger)\|_{1,\mathrm{cq}},\qquad
E_*=\inf_{\Phi\ \mathrm{common\ CPTP}}E(\Phi).
$$

The maximum retains ALL twelve and HALF the full cq trace norm.
The norm includes coherent live matrices, the total-variation trace norm
of EACH separately labelled exact-time measure, all atoms and singular
continuous additions, wrong support, abort, rejection and every extra
sector, including those with zero ideal weight. A common dominating
scalar measure defines matrix-valued measure norms without time bins.
First executed failure is absorbing; no later positive-carrier action,
retry, reversal, reset or replacement is allowed on that branch. Earlier
stopped archives and controller updates remain in their own branches.
An output interpretation cannot delete an acquisition outcome or divide
by survival or acceptance. Time $t$ means actual elapsed time, absolute
$6+t$, and terminal live output is at time one.

## 2. Exact inherited coefficients and the fixed full channel

**Definition 2.1 (conditional algebraic source).** Use source variables
$\mathbf x=(\lambda_{\rm src},\alpha_1,\alpha_2,\beta_1,\beta_2,z_{\rm src})$
and $\eta=(\eta_0,\eta_1,\eta_2)$. These chart coordinates are unrelated
to history phases and to $\alpha,\beta$ below. Put

$$
\begin{aligned}
v_5&=(\alpha_1,\alpha_2,-1)^T,&v_{27}&=(\beta_1,\beta_2,1)^T,\\
R_y&=v_yv_y^T/\|v_y\|^2,& A_5^{\rm src}&=\lambda_{\rm src}R_5,\\
A_{27}^{\rm src}&=(1-\lambda_{\rm src})R_{27},&
\zeta&=(z_{\rm src},59\lambda_{\rm src}/128,\lambda_{\rm src}/2),\\
N^{\rm src}&=\sum_{y=5,27}A_y^{\rm src}\odot a_ya_y^T,&
S_0^{\rm src}&=\operatorname{diag}\zeta-N^{\rm src},\\
S_{ij}^{\rm src}&=\begin{pmatrix}
\zeta_j-\sum_{y=5,27}(A_y^{\rm src})_{ii}p_{yj}&-N_{ij}^{\rm src}\\
-N_{ij}^{\rm src}&\zeta_i-\sum_{y=5,27}(A_y^{\rm src})_{jj}p_{yi}
\end{pmatrix}\quad(i<j),\\
F^{\rm src}&=\sum_{y=5,27}\operatorname{tr}(A_y^{\rm src}B_y^{\rm tar})
                   -\sum_i\zeta_i+6\lambda_{\rm src}/11,\\
g^{\rm src}&=(1000\det S_0^{\rm src},\det S_{01}^{\rm src},
                                      \det S_{02}^{\rm src}),\\
\Psi(\mathbf x,\eta)&=(\nabla_{\mathbf x}(F^{\rm src}+\eta\cdot g^{\rm src}),
                                                        g^{\rm src}).
\end{aligned}
\tag{NP.7}
$$

The inherited premise selects the unique zero of $\Psi$ in the
radius-$10^{-24}$ product box about the following EXACT rational centres.

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

Evaluate all following source quantities there, rather than at the centres:

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
M&=\operatorname{diag}(0,m_1,m_2),&\kappa&=h_0a+h_1b.
\end{aligned}
\tag{NP.8}
$$

The adjugate is the transposed cofactor matrix; first-coordinate vectors
have the relevant matrix size. CG §§13–16,22, current JR Proposition
34.2 and the real-Gram source supply the conditional rank-one positive
factors and identities

$$
\begin{gathered}
h_i,a,b,c,d,m_1,m_2>0,\quad 0<\kappa<1/4,\qquad
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\\
968/1000<h_0^2<970/1000,\quad498/1000<h_1^2<500/1000,\quad
655/1000<h_2^2<656/1000,\\
h_0h_1>695/1000,\quad h_0h_2>796/1000,\quad
 a^2+b^2+c^2+d^2<36/1000,\\
(S_{01}^{\rm src})_{00},(S_{02}^{\rm src})_{00}>1/10.
\end{gathered}
\tag{NP.9}
$$

In particular $h_0^2+b^2+d^2=1$, $h_1^2+a^2+m_1=1$ and
$h_2^2+c^2+m_2=1$. Define

$$
\alpha=\frac{ab}{h_0h_1}>0,\qquad
\beta=\frac{cd}{h_0h_2}>0,\qquad \ell=\alpha+\beta,
\qquad k=1-\ell.
\tag{NP.10}
$$

AM–GM gives $ab+cd<(18/1000)$, and the two product margins imply
$0<\ell<18/695<1/36$. This uses the combined sum-of-squares margin,
not two separate loose estimates. Thus $0<\alpha,\beta<1$ and $k>0$.
The isolation, enclosure, bordered Jacobian, ranks and minimax premises
are not reauthenticated by these symbolic implications.

**Definition 2.2 (complete channel held fixed).** For EVERY complex
$A\in M_5$ let $A_V=E^\dagger AE$ and $g(t)=2/(1+t)^2$, $0\leq t\leq1$.
The specified channel is

$$
\begin{aligned}
\Phi_*^L(A)&=E(DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger)E^\dagger,\\
\Phi_{*,j}^{f}(A)(dt)&=g(t)\left[w_j\operatorname{tr}(MA_V)
                     +\mathbf1_{j=2}\operatorname{tr}(Q_5A)\right]dt\,P_f.
\end{aligned}
\tag{NP.11}
$$

All extra-sector maps and cross-support maps are zero; the complement
has no live output. Since $\int_0^1g=1$ and (NP.9) holds, this is TP.
All identities include arbitrary passive references and every separately
labelled Borel time set. Fixed common metadata is carried identically.
The inherited common-CPTP minimax is

$$
E_*=F^{\rm src}(\mathbf x_*)\in
(0.14817810291080132013,0.14817810291080132014).
\tag{NP.12}
$$

This credited ordinary computer-assisted result is retained because each
constructed forgotten channel equals (NP.11) exactly. It is not reproved,
and no uniqueness of the whole channel among error optimizers is assumed.

## 3. The universal acquisition class and coefficient necessity

**Definition 3.1 (actual finite instruments and resource).** Put
$X_{01}=|0\rangle\langle1|+|1\rangle\langle0|$. At strength $s\in[0,1]$
the prescribed binary effects, on EVERY input, are

$$
F_r(s)=\frac{I_5+r s\kappa EX_{01}E^\dagger}{2},\qquad r=\pm1.
\tag{NP.13}
$$

A competitor consists of any finite actually generated accessible label
set $\Xi$, report function $r:\Xi\to\{\pm1\}$, finite positive integer
joint fibre dimensions $d_\xi$, common CP encoders
$\mathcal C_\xi:M_5\to M_{d_\xi}$, and common full-output CPTP decoders
$\mathcal R_\xi$. They satisfy

$$
\sum_\xi\mathcal C_\xi^\dagger(I)=I_5,\qquad
\sum_{\xi:r(\xi)=r}\mathcal C_\xi^\dagger(I)=F_r(s),\qquad
\sum_\xi\mathcal R_\xi\mathcal C_\xi=\Phi_*.
\tag{NP.14}
$$

Randomized report postprocessing can be absorbed into generated finite
labels. Every decoder is TP on its WHOLE carrier; only its supported live
restriction is TNI. All future-accessible input-dependent specimen parts,
memories, controller/environment parts, returned systems and entanglement
shares count JOINTLY in $d_\xi$. Other dilation systems are permanently
inaccessible before this cut. A receiver's retained entangled share is
not an independent blank; a coherent flag is quantum payload until an
actual classical direct sum is generated. Passive references remain
inaccessible. No helper, bypass, hidden share, history programme, prior,
second specimen, callback, copy, reset, retry or postselection is supplied.

The high acquired effect and its unnormalized cost are

$$
G_{\rm acq}=\sum_{\xi:d_\xi\geq3}\mathcal C_\xi^\dagger(I),\qquad
E_s(\sigma)=\inf_{\text{(NP.14)}}\operatorname{tr}(G_{\rm acq}\sigma).
\tag{NP.15}
$$

High acquisition later failing is included. Define $E_s^L$ using only its
later supported-live mass. For supported $\rho$ write $E_s(\rho)$ for
$E_s(E\rho E^\dagger)$. Constants may be chosen from a public test state
before execution; each resulting instrument remains common on every
unknown input. Separate test-state minima are not one simultaneous
minimizer. No real, covariant, isometric, JR-conditioned, wholly-live or
chosen-failure restriction is placed on these competitors.

**Lemma 3.2 (coefficient order and the complete singular locus).** In
coefficient order $(D,T,S)$ put

$$
\begin{aligned}
K(z)&=uD+vT+wS,\quad z=(u,v,w)^T,\quad(K_D,K_T,K_S)=(D,T,S),\\
B_0&=\operatorname{diag}(1,-\alpha,-\beta),\\
X_c&=|D\rangle\langle T|+|T\rangle\langle D|,\\
\Theta(Z)&=\sum_{i,j}Z_{ij}K_j^\dagger K_i,
\qquad C(\rho)_{ij}=\operatorname{tr}(K_i^\dagger K_j\rho).
\end{aligned}
\tag{NP.16}
$$

Then $z^\dagger C(\rho)z=\operatorname{tr}(K(z)^\dagger K(z)\rho)$
and $\operatorname{tr}(CZ)=\operatorname{tr}(\Theta(Z)\rho)$. If
$\mathcal V=(|D\rangle\!\rangle,|T\rangle\!\rangle,|S\rangle\!\rangle)$
in unnormalized output-input Choi order, its coefficient Choi matrix is
$\mathcal VZ\mathcal V^\dagger$, whose output partial trace is
$\Theta(Z)^T$, not $\Theta(Z)$. The entire nonzero singular locus is

$$
\mathcal Z=\{u=0\}\ \cup\ \{u^2-\alpha v^2-\beta w^2=0\},
\qquad
\mathcal C_2=\left\{\sum_{j=1}^N z_jz_j^\dagger:z_j\in\mathcal Z,
                                                       N<\infty\right\}.
\tag{NP.17}
$$

Zero sums are included. Every nonzero singular $K(z)$ has rank exactly two.

Proof. Expand the trace to obtain (NP.16), keeping its index order.
Vectorization gives the Choi statement on every complex matrix unit.
The matrices $D,T,S$ have disjoint nonzero entry patterns and are linearly
independent, although their Choi columns need not be normalized. Explicitly

$$
K(z)=\begin{pmatrix}h_0u&av&cw\\bv&h_1u&0\\dw&0&h_2u\end{pmatrix},
\qquad
\det K(z)=h_0h_1h_2u(u^2-\alpha v^2-\beta w^2).
\tag{NP.18}
$$

For $u\ne0$ its lower-right minor is $h_1h_2u^2\ne0$. For $u=0,z\ne0$,
column zero is nonzero in rows one/two and some other column is nonzero
in row zero, so there are two independent columns. This proves both
components, including their intersection and every complex phase. $\square$

**Proposition 3.3 (necessity for every original finite competitor).**
Every competitor induces arrays $H_r\succeq0$, $L_r\in\mathcal C_2$ with

$$
\begin{gathered}
\sum_r(H_r+L_r)=I_3,\qquad H=H_++H_-,\quad0\preceq H\preceq I_3,\\
N=\frac{I_3+s\kappa X_{01}}2-\Theta(H_++L_+),\quad0\preceq N\preceq M,\\
\operatorname{Re}(H_++L_+)_{DT}=s/2,\qquad
G_{\rm acq}\succeq E\Theta(H)E^\dagger.
\end{gathered}
\tag{NP.19}
$$

The supported-live high cost is $\operatorname{tr}(C(\rho)H)$.

Proof. Multiply every encoder Kraus matrix by every Kraus matrix of its
supported-live decoder. Their positive vectorized projectors sum to the
live Choi matrix of (NP.11). Testing the kernel of that positive sum
forces every summand into its three-column support. Thus every product
is uniquely $EK(z)E^\dagger$, vanishes on the complement, and has zero
cross-support action. If $\mathcal W$ denotes these embedded Choi
columns, the left inverse
$(\mathcal W^\dagger\mathcal W)^{-1}\mathcal W^\dagger$ applied on
both sides of their Choi sum gives $\sum zz^\dagger=I_3$. This does
not replace the column Gram matrix by identity.

Group those products by report and by the ACTUAL acquired fibre's high
or low dimension. A product through $d_\xi\leq2$ has rank at most two,
so its coefficient belongs to (NP.17). This analytic refinement produces
$H_r,L_r$ and does not grant a new observed flag to an old dilation.
The plus report's supported failure effect is exactly $N$; the minus
failure effect is $M-N$. Positivity gives their stated bounds without
fixing either conditioned live map or the binary time split. Because
$M$ kills coordinate zero, positivity kills row and column zero of
both $N$ and $M-N$: each off-diagonal entry obeys its positive two by
two minor bound. For Hermitian $Z$, multiplication gives

$$
\Theta(Z)_{01}=h_0a\,\overline{Z_{DT}}+h_1b\,Z_{DT},
\qquad\operatorname{Re}\Theta(Z)_{01}=\kappa\operatorname{Re}Z_{DT}.
\tag{NP.20}
$$

No other coefficient pair contributes to this entry. The zero failure
entry and (NP.13) give the real record equality in (NP.19).

Finally, the live part of each full TP decoder is TNI, so its adjoint
identity is at most the full identity. Pulling back through each high
encoder and summing proves the FULL five-mode operator inequality.
It includes high acquisition later failing and any complement or
cross-support contribution in its acquired effect. Evaluating it on
any positive input proves acquired mass at least supported-live high
mass before any normalization or averaging. $\square$

## 4. A nonempty genuinely nonreal physical family

**Lemma 4.1 (the source sign needed by the state).** The inherited source
premises imply

$$
r_T=\frac{ah_1}{bh_0}\in(1/4,2/5),\qquad h_1/h_0>7/10,\qquad
\chi=h_1b-h_0a>\frac9{49}h_1b>0.
\tag{NP.21}
$$

Proof. Here is the rational source implication, also credited to §8 of
*Real coefficient Grams and a small-record resource law*. The source box
implies $.479<\lambda_{\rm src}<.480$,
$1.412<\alpha_1<1.413$, $1.185<\alpha_2<1.186$,
$.413<\beta_1<.414$, $.809<\beta_2<.810$. All finite decimals here are
rational numbers. For $r_5=1+\alpha_1^2+\alpha_2^2$ and
$r_{27}=1+\beta_1^2+\beta_2^2$, positive multiplication gives
$4.39<r_5<4.41$, $1.82<r_{27}<1.83$, and

$$
\begin{gathered}
(A_5^{\rm src})_{00}>.21,\quad(A_{27}^{\rm src})_{00}>.04,\\
.180<(A_5^{\rm src})_{01}<.185,\qquad
.094<(A_{27}^{\rm src})_{01}<.097.
\end{gathered}
\tag{NP.22}
$$

Using $17<\sqrt{295}<18$ and $31<\sqrt{999}<32$ in

$$
N_{01}^{\rm src}=\frac{(A_5^{\rm src})_{01}\sqrt{295}
                         +(A_{27}^{\rm src})_{01}\sqrt{999}}{128}
\tag{NP.23}
$$

gives $.045<N_{01}^{\rm src}<.051$: the lower numerator is
$(180\cdot17+94\cdot31)/1000$ and the upper one is
$(185\cdot18+97\cdot32)/1000$. The two positive pivots in (NP.9)
also satisfy

$$
\begin{aligned}
(S_{01}^{\rm src})_{00}
 &<\frac{(.48-.21)59-.04\cdot37}{128}<3/25,\\
(S_{02}^{\rm src})_{00}&<.24-(.21+.04)/2<3/25.
\end{aligned}
\tag{NP.24}
$$

The rank-one adjugate factor gives $a/b=N_{01}^{\rm src}/
(S_{01}^{\rm src})_{00}$. The diagonal margins give

$$
(7/10)^2<498/970<(h_1/h_0)^2<500/968<(3/4)^2.
\tag{NP.25}
$$

Consequently $r_T>(7/10)(45/1000)/(3/25)=21/80>1/4$ and
$r_T<(3/4)(51/1000)/(1/10)<2/5$. In particular
$h_0a/(h_1b)=r_T/(h_1/h_0)^2<40/49$, proving (NP.21).
These are symbolic consequences of the exact supplied point, not a new
numerical certificate for it. $\square$

**Definition 4.2 (public parameters and admission).** Choose
$\tau_0,\tau_1,\tau_2>0$ with sum one. Put

$$
A=\sum_i h_i^2\tau_i,\qquad
B_T=b^2\tau_0+a^2\tau_1,\qquad C_S=d^2\tau_0+c^2\tau_2.
\tag{NP.26}
$$

All three are positive. For $0<\xi<1$ define

$$
\begin{aligned}
c_\xi&=\frac{1-\xi^2}{1+\xi^2},&
\sigma_\xi&=\frac{2\xi}{1+\xi^2},&
\delta_\xi&=1-\alpha-\beta c_\xi,\\
R_\xi&=\sqrt{\delta_\xi^2+\beta^2\sigma_\xi^2},&
p&=(R_\xi+\delta_\xi)/2,&
q&=(R_\xi-\delta_\xi)/(2\alpha),\\
r_0&=\frac{\beta\sigma_\xi}{2\sqrt\alpha},&
k_\xi&=(1-\alpha)c_\xi-\beta,\\
\lambda&=\frac{Ap-B_Tq}{c_\xi(p+\alpha q)},&
\gamma&=\lambda\sqrt\alpha\,\sigma_\xi+
 (B_T+\lambda\alpha c_\xi)\sqrt{q/p}.
\end{aligned}
\tag{NP.27}
$$

Admission means exactly

$$
p+q<1,\qquad k_\xi>0,\qquad Ap>B_Tq,\qquad
\gamma<\chi\sqrt{\tau_0\tau_1}.
\tag{NP.28}
$$

There is no optimization or numerical search hidden in this definition.
For admitted parameters the selected physical supported state and Gram are

$$
\rho=\begin{pmatrix}
\tau_0&i\gamma/\chi&0\\-i\gamma/\chi&\tau_1&0\\0&0&\tau_2
\end{pmatrix},\qquad
C=C(\rho)=\begin{pmatrix}A&i\gamma&0\\-i\gamma&B_T&0\\0&0&C_S\end{pmatrix}.
\tag{NP.29}
$$

Write

$$
t=p+q,\quad s_* =\sqrt{1-p-q},\quad
h=(\sqrt p,i\sqrt q,0)^T,\quad H_*=hh^\dagger,\quad
F=\lambda k_\xi.
\tag{NP.30}
$$

The vector $h$ in (NP.30) is a coefficient vector, distinct from the
three source coefficients $h_i$.

**Proposition 4.3 (physical positivity and an explicit admitted interval).**
Every admitted state (NP.29) is normalized and positive definite; its
Gram is positive definite and genuinely nonreal. For every chosen
positive $\tau$, a whole explicit interval of $\xi$ is admitted. Namely set

$$
\begin{aligned}
T_0&=2\beta+\frac{\beta^2(1+\alpha)}{\alpha k},\\
G_0&=4A\sqrt\alpha+
            \frac{\beta(B_T+2\alpha A)}{\sqrt\alpha k},\\
\xi_0&=\min\left\{\frac14,
 \sqrt{\frac\ell{2T_0}},
 \sqrt{\frac{k}{4(1-\alpha)}},
 \sqrt{\frac{A\alpha k^2}{2B_T\beta^2}},
 \frac{\chi\sqrt{\tau_0\tau_1}}{2G_0}\right\}>0.
\end{aligned}
\tag{NP.31}
$$

Every $0<\xi\leq\xi_0$ satisfies the strict admission conditions, including
the closed upper edge. For all admitted positive $\xi$,
$0<s_*<\sqrt\ell$.

Proof. First $c_\xi,\sigma_\xi>0$, $c_\xi^2+\sigma_\xi^2=1$ and

$$
p-\alpha q=\delta_\xi=k+\beta(1-c_\xi)\geq k,
\qquad pq=r_0^2>0.
\tag{NP.32}
$$

Thus $p,q>0$, every denominator in (NP.27) is positive, and admission
makes $\lambda,\gamma>0$. The $DT$-state determinant is
$\tau_0\tau_1-(\gamma/\chi)^2>0$, so $\rho>0$ and its trace is one.
Multiplying $D^\dagger T$ against $\rho$ gives
$h_0a\rho_{10}+h_1b\rho_{01}=i\gamma$; the other off-diagonal Gram
entries vanish, proving (NP.29). Independence of $D,T,S$ and $\rho>0$
give $z^\dagger Cz=\operatorname{tr}(K(z)^\dagger K(z)\rho)>0$ for
$z\ne0$. Hence $C>0$, and $\gamma>0$ proves genuine nonreality.

All quantities inside the minimum (NP.31) are finite and positive.
For $0<\xi\leq\xi_0$ one has $c_\xi>1/2$, $\sigma_\xi\leq2\xi$,
$1-c_\xi\leq2\xi^2$, $p\geq k$, and
$q=r_0^2/p\leq\beta^2\xi^2/(\alpha k)$. Therefore

$$
\begin{aligned}
p+q&=\delta_\xi+(1+\alpha)q
 \leq k+T_0\xi^2\leq1-\ell/2<1,\\
k_\xi&\geq k-2(1-\alpha)\xi^2\geq k/2>0,\\
Ap-B_Tq&\geq Ak-\frac{B_T\beta^2\xi^2}{\alpha k}\geq Ak/2>0.
\end{aligned}
\tag{NP.33}
$$

Moreover $0<\lambda\leq A/c_\xi\leq2A$ and
$\sqrt{q/p}=r_0/p\leq\beta\xi/(\sqrt\alpha k)$. Substitution in
$\gamma$ yields
$0<\gamma\leq G_0\xi\leq\chi\sqrt{\tau_0\tau_1}/2$, giving the
last strict inequality in (NP.28). Finally
$t=\delta_\xi+(1+\alpha)q>k$, while admission gives $t<1$;
this proves the asserted endpoint bounds. The exact choice
$\tau=(1/3,1/3,1/3)$, $\xi=\xi_0/2$ is a concrete member without any
search. Algebraic public parameters give algebraic constants and matrices.
$\square$

## 5. A tilted certificate against the full complex cone

**Theorem 5.1 (universal certificate and its unique equality aggregate).**
For every admitted state set

$$
B_\xi=\begin{pmatrix}
c_\xi&i\sqrt\alpha\,\sigma_\xi&0\\
-i\sqrt\alpha\,\sigma_\xi&-\alpha c_\xi&0\\0&0&-\beta
\end{pmatrix},\qquad \mathcal S=C-\lambda B_\xi.
\tag{NP.34}
$$

Every $L\in\mathcal C_2$ has $\operatorname{tr}(B_\xi L)\leq0$.
The matrix $\mathcal S$ is PSD of rank two with kernel $\mathbb C h$.
For EVERY original finite competitor on the normalized input $E\rho E^\dagger$,
put $a_{\rm acq}=\operatorname{tr}(G_{\rm acq}E\rho E^\dagger)$. Then

$$
\begin{aligned}
a_{\rm acq}-F
={}&\operatorname{tr}\left[(G_{\rm acq}-E\Theta(H)E^\dagger)
                                               E\rho E^\dagger\right]\\
 &+\lambda\,[\operatorname{tr}(B_\xi H)-k_\xi]
   +\operatorname{tr}(\mathcal S H)\ \geq\ 0.
\end{aligned}
\tag{NP.35}
$$

All THREE displayed terms are nonnegative. The same lower bound holds
for supported-live high cost. Equality in that live bound forces exactly
$H=H_*$. Furthermore

$$
F=\operatorname{tr}(CH_*)=Ap+B_Tq-2\gamma r_0>0,
\qquad
kA-F=\lambda\beta(1-c_\xi)+
             k(B_T+\lambda\alpha c_\xi)q/p>0.
\tag{NP.36}
$$

Proof. For a quadratic-null $z=(u,v,w)$ define real numbers
$x=|u|^2-\alpha|v|^2$ and
$y=2\sqrt\alpha\operatorname{Im}(u\overline v)$. Expansion gives

$$
x^2+y^2=|u^2-\alpha v^2|^2=\beta^2|w|^4.
\tag{NP.37}
$$

The off-diagonal sign in (NP.34) gives
$z^\dagger B_\xi z=c_\xi x+\sigma_\xi y-\beta|w|^2\leq0$
by Cauchy–Schwarz. On the ENTIRE plane $u=0$ the same pairing is
$-\alpha c_\xi|v|^2-\beta|w|^2\leq0$. Positive finite sums prove the
full-cone inequality. Since $I-H=L_++L_-$, it gives
$\operatorname{tr}(B_\xi H)\geq\operatorname{tr}B_\xi=k_\xi$.
Neither a real cone nor only the quadratic component was substituted.

Let $b_*=B_T+\lambda\alpha c_\xi>0$. The formulas for $\lambda,\gamma$
are exactly the two identities

$$
A-\lambda c_\xi=b_*q/p,\qquad
\gamma-\lambda\sqrt\alpha\,\sigma_\xi=b_*\sqrt{q/p}.
\tag{NP.38}
$$

Thus the $DT$ block of $\mathcal S$ is
$b_*\left(\begin{smallmatrix}q/p&i\sqrt{q/p}\\-i\sqrt{q/p}&1\end{smallmatrix}\right)$,
a positive rank-one outer product whose kernel is
$(\sqrt p,i\sqrt q)^T$. Its other eigenvalue is $b_*(1+q/p)$, and
the $SS$ entry is $C_S+\lambda\beta>0$. This proves its PSD rank and
kernel. The sole nonzero eigenvalue of $H_*$ is $t<1$, so
$0\preceq H_*\preceq I$. Also

$$
h^\dagger B_\xi h=c_\xi(p-\alpha q)
 -2\sqrt\alpha\,\sigma_\xi r_0
 =c_\xi(1-\alpha)-\beta(c_\xi^2+\sigma_\xi^2)=k_\xi.
\tag{NP.39}
$$

Consequently $\operatorname{tr}(CH_*)=\lambda k_\xi=F>0$, and direct
trace evaluation gives its expression in (NP.36). Subtracting this
identity from the cost and using Proposition 3.3 proves (NP.35).

If the last two terms vanish, positivity implies
$\|\mathcal S^{1/2}H^{1/2}\|_F^2=0$, hence
$\operatorname{ran}H\subseteq\mathbb C h$. Write $H=aH_*$ with $a\geq0$.
Its $B_\xi$ trace is $a k_\xi$; equality and $k_\xi>0$ give $a=1$.
Acquired equality also makes the SELECTED expectation of the first
slack term zero; no whole-operator vanishing is inferred from that one
expectation. Finally insert $H_0=k|D\rangle\langle D|$ into the same
last-two-term identity. Its $B_\xi$ excess is $\beta(1-c_\xi)$ and
$\mathcal S_{DD}=b_*q/p$, giving the saving formula. Both summands are
strictly positive. $\square$

## 6. A genuine low-cone lift through the closed endpoint

**Lemma 6.1 (rank-many real null decomposition).** If a real symmetric
$T_0\succeq0$ satisfies $\operatorname{tr}(B_0T_0)=0$, it has a
factorization into exactly $\operatorname{rank}T_0$ nonzero real null
projectors $y_jy_j^T$, $y_j^TB_0y_j=0$. The zero matrix uses none.

Proof. Take a real rank-many spectral factor $T_0=YY^T$, with $Y$
injective on its column space. The real symmetric matrix
$A_0=Y^TB_0Y$ has trace zero. A trace-zero symmetric matrix has an
orthonormal basis with all Rayleigh values zero. To construct one,
if it is nonzero choose orthogonal eigenvectors $e_+,e_-$ for
$a_+>0>a_-$. The unit vector

$$
f=\frac{\sqrt{-a_-}\,e_++\sqrt{a_+}\,e_-}{\sqrt{a_+-a_-}}
\tag{NP.40}
$$

has zero Rayleigh value. Compression to $f^\perp$ still has trace zero;
induct on the dimension, with the zero matrix allowing any basis.
Multiplying that orthonormal basis by $Y$ gives the desired columns.
Injectivity makes every one nonzero and their projectors sum to $T_0$.
This standard zero-Rayleigh argument covers repeated and zero eigenvalues.
$\square$

**Proposition 6.2 (the explicit complex lift).** Put

$$
\begin{aligned}
a_h&=1/\sqrt{1+\xi^2},& b_h&=\xi/\sqrt{1+\xi^2},\\
R&=\begin{pmatrix}a_h&-i\sqrt\alpha\,b_h&0\\
 -ib_h/\sqrt\alpha&a_h&0\\0&0&1\end{pmatrix},\\
u_L&=\frac{1-p+\alpha(1-q)+\beta}{2},&
v_L&=\frac{1-p+\alpha(1-q)-\beta}{2\alpha}.
\end{aligned}
\tag{NP.41}
$$

Then

$$
\begin{gathered}
R^TB_0R=B_0,\qquad RX_cR^\dagger=X_c,\qquad
I-H_*=R\operatorname{diag}(u_L,v_L,1)R^\dagger,\\
u_L,v_L>0,\qquad u_L-\alpha v_L=\beta,\qquad u_Lv_L=s_*^2.
\end{gathered}
\tag{NP.42}
$$

For $r=\pm1$ and $0\leq s\leq s_*$ take

$$
\begin{aligned}
H_r&=H_*/2,& L_r&=(I-H_*+r sX_c)/2,&N_r&=M/2,\\
T_r&=\frac12\begin{pmatrix}u_L&r s&0\\r s&v_L&0\\0&0&1\end{pmatrix},
&&L_r=RT_rR^\dagger.
\end{aligned}
\tag{NP.43}
$$

Each $L_r$ belongs to the TRUE cone $\mathcal C_2$. It has three nonzero
rank-two atoms for $s<s_*$ and two at $s=s_*$.

Proof. The $DT$ determinant of $R$ is $a_h^2+b_h^2=1$, so $R$ is
invertible. Bilinear multiplication cancels its off-diagonal terms and
gives $R^TB_0R=B_0$; Hermitian multiplication gives $RX_cR^\dagger=X_c$.
In the claimed diagonal congruence its $DT$ off-diagonal entry is
$i a_hb_h(u_L/\sqrt\alpha-\sqrt\alpha v_L)=i r_0$.
If its diagonal entries are $d_0,d_1$, they obey

$$
d_0+\alpha d_1=u_L+\alpha v_L=1-p+\alpha(1-q),\quad
 d_0-\alpha d_1=c_\xi(u_L-\alpha v_L)=\beta c_\xi.
\tag{NP.44}
$$

By (NP.32), these are also the sum and difference for $1-p,1-q$.
This proves the congruence. Since $I-H_*>0$, invertible congruence makes
$u_L,v_L>0$. Its $DT$ determinant gives
$u_Lv_L=(1-p)(1-q)-r_0^2=1-p-q=s_*^2$.

The $DT$ determinant in $T_r$ is $(s_*^2-s^2)/4$; its other entry is
$1/2$. Thus $T_r\succeq0$ exactly for this interval, with rank three in
the interior and rank two at the endpoint. Moreover
$\operatorname{tr}(B_0T_r)=(u_L-\alpha v_L-\beta)/2=0$.
Apply Lemma 6.1 and transform its real columns by $z_j=Ry_j$.
Their projectors sum to $L_r$, and $z_j^TB_0z_j=0$. A nonzero real
null $y_j$ has $(y_j)_D\ne0$, since $\alpha,\beta>0$.
Hence $\operatorname{Re}(z_j)_D=a_h(y_j)_D\ne0$. Equation (NP.18)
now proves that EACH transformed matrix $K(z_j)$ has rank exactly two.
This gives the claimed exact numbers of nonzero atoms.

This transformation is only a construction on quadratic-null vectors.
It is not an automorphism of the full plane-plus-quadratic cone: for
example $R(0,1,0)=(-i\sqrt\alpha b_h,a_h,0)$ has quadratic value
$-\alpha$ and nonzero first coordinate, so its $K$ is invertible when
$\xi>0$. No arbitrary cone normal form is used.

Finally $H_r+L_r=(I+r sX_c)/2$, and
$\Theta(I)=I-M$, $\Theta(X_c)=\kappa X_{01}$. Thus

$$
\Theta(H_r+L_r)+M/2=(I+r s\kappa X_{01})/2.
\tag{NP.45}
$$

Summing the two reports gives coefficient identity and exact supported
record normalization. These are upper-construction choices only;
Proposition 3.3 continues to allow all conditioned live maps. $\square$

## 7. Actual normalized instruments with fourteen or twelve labels

**Theorem 7.1 (complete finite attainers).** For every admitted public
state and every $0\leq s\leq s_*$ there is an actual finite instrument
(NP.14) with

$$
G_{\rm acq}=G_{\rm live}=E\Theta(H_*)E^\dagger,\qquad
E_s(\rho)=E_s^L(\rho)=F.
\tag{NP.46}
$$

This construction has exactly fourteen acquired labels for $s<s_*$ and
twelve for $s=s_*$. All declarations below are part of the new instrument,
not flags presumed observable in a pre-existing Kraus representation.

Proof. For each report $r$ take the nonzero atoms $z_{r,j}$ constructed
in Proposition 6.2. Generate the following labels, retain exactly their
declared quantum carriers, and permanently discard every other
input-dependent dilation system. All spectral factors, null columns,
bases and isometries are fixed from public coefficients before acquisition;
none is chosen by observing the unknown specimen.

| Actual label | Fibre dimension | Encoder specification | Full decoder |
| --- | --- | --- | --- |
| $(r,H)$ | $3$ | Kraus $K(h)E^\dagger/\sqrt2$ | $X\mapsto EXE^\dagger$, entirely live |
| $(r,L,j)$ | $2$ | Kraus $U_{r,j}^\dagger K(z_{r,j})E^\dagger$ | $X\mapsto EU_{r,j}XU_{r,j}^\dagger E^\dagger$, entirely live |
| $(r,f,j)$, $j=1,2$ | $1$ | row $\sqrt{m_j/2}\langle j|E^\dagger$ | scalar failure decoder specified below |
| $(r,\perp)$ | $1$ | CP map $A\mapsto\operatorname{tr}(Q_5A)/2$ | scalar mass to original label $2$ with density $g(t)dt\,P_f$ |

For a low matrix use its specimen columns one and two, $k_1,k_2$.
Define, with the calibrated inner product,

$$
u_1=k_1/\|k_1\|,\qquad
\widetilde u_2=k_2-u_1(u_1^\dagger k_2),\qquad
u_2=\widetilde u_2/\|\widetilde u_2\|,\qquad U_{r,j}=(u_1,u_2).
\tag{NP.47}
$$

The lower-right minor in (NP.18) makes these columns independent, so
both denominators are nonzero. They span its rank-two range. Consequently
$U_{r,j}^\dagger U_{r,j}=I_2$ and
$U_{r,j}U_{r,j}^\dagger K(z_{r,j})=K(z_{r,j})$. This proves both the
full TP property of each range decoder and its exact decoded product.
The high decoder is also TP on all of $M_3$. Its product is genuinely
rank three because

$$
\det K(h)=h_0h_1h_2\sqrt p\,(p+\alpha q)\ne0.
\tag{NP.48}
$$

For a supported scalar label its full decoder sends a scalar $x$ to
$x w_\ell g(t)dt\,P_f$ separately in EACH original failure label $\ell$,
with zero live and extra maps. For the complement scalar label it uses
only original label two. These scalar decoders are TP since
$\sum_\ell w_\ell=1$ and $\int g=1$. Choose any fixed orthonormal
basis $q_1,q_2$ of $V^\perp$ to realize the complement encoder by rows
$\langle q_j|/\sqrt2$; their multiplicity is permanently inaccessible,
so its accessible carrier is dimension ONE. There is no extra coherent
register or future-accessible share.

At report $r$ the sum of all encoder effects is

$$
E\bigl[\Theta(H_r+L_r)+M/2\bigr]E^\dagger+Q_5/2=F_r(s).
\tag{NP.49}
$$

Summing reports yields $E[\Theta(I)+M]E^\dagger+Q_5=I_5$.
Every individual encoder is CP and has positive effect at most this
identity; hence it is TNI, and their joint acquisition is TP.
This verifies actual normalization, including the failure and complement
branches, rather than normalizing only the live ensemble.

The live decoded Kraus matrices are $EK(h)E^\dagger/\sqrt2$ and
$EK(z_{r,j})E^\dagger$. Their coefficient projectors sum to $I_3$,
so their forgotten action equals the live part of (NP.11) on EVERY
complex matrix unit. The supported scalar effects sum to $EME^\dagger$,
and the complement effects to $Q_5$; their decoders give exactly
(NP.11) separately at every original label. Precomposition by $E^\dagger$
and complement trace kills every $V$–$V^\perp$ cross matrix unit.
There is no complement live output, singular time part, endpoint atom,
abort, rejection or extra-sector addition. The named zero measures at
labels zero and mode $13$ remain zero. Common metadata is carried
identically, without introducing history information.

To verify the complete reference law, let $X$ be any positive joint
input with an arbitrary passive reference. At report $r$ the supported
scalar branches have the conditional reference operator

$$
R_{f,r}(X)=\operatorname{Tr}_5[(E(M/2)E^\dagger\otimes I)X],\qquad
R_{\perp,r}(X)=\tfrac12\operatorname{Tr}_5[(Q_5\otimes I)X].
\tag{NP.50}
$$

These expressions equal the actual Kraus-row sums; they do not replace
a conditional reference by its unconditional marginal. In failure label
$\ell$ and EVERY Borel set $B_{\rm time}\subseteq[0,1]$, the output is

$$
P_f\otimes\left[w_\ell R_{f,r}(X)
       +\mathbf1_{\ell=2}R_{\perp,r}(X)\right]
                       \int_{B_{\rm time}}g(t)\,dt.
\tag{NP.51}
$$

Summing $r$ is exactly the reference amplification of (NP.11).
The live matrix-product identities tensor by the reference identity as
well. By complex linearity these identities hold for all joint complex
operators, including singular and subnormalized states; trace-class
infinite-reference versions follow by finite-rank approximation. Thus
all complete channel, reference, separate time-label and zero-sector
identities hold together.

For $s<s_*$ the rank-many construction supplies exactly three nonzero
low labels per report; at $s=s_*$ exactly two. The high matrices, two
supported failure rows ($m_j>0$) and complement CP maps ($\operatorname{rank}Q_5=2$)
are nonzero. The actual counts are therefore $2(1+3+2+1)=14$ and
$2(1+2+2+1)=12$. These are counts of THIS specified generated alphabet,
not minimum label counts or finite-clock hardware claims.

Only the two high encoders are charged high, and their full decoders
are wholly live. Their effect is exactly $E\Theta(H_*)E^\dagger$ and
the selected cost is $F$. Theorem 5.1 supplies the universal lower bound
without imposing these upper-construction restrictions. This proves
(NP.46) for the entire closed interval. $\square$

## 8. Maximality and a quantitative gap beyond the plateau

**Lemma 8.1 (binary compression capacity).** For any Hermitian PSD
$2\times2$ matrix $A_2$,

$$
\max_{0\preceq W\preceq A_2}\operatorname{Re}W_{01}
=\frac{\operatorname{Re}(A_2)_{01}
 +\sqrt{(A_2)_{00}(A_2)_{11}-(\operatorname{Im}(A_2)_{01})^2}}2.
\tag{NP.52}
$$

Proof. For $A_2>0$ substitute $W=A_2^{1/2}TA_2^{1/2}$, $0\preceq T\preceq I$.
Twice the objective is $\operatorname{tr}(YT)$ for
$Y=A_2^{1/2}X A_2^{1/2}$, $X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$.
Diagonalize $Y$; the maximum is the sum of its positive eigenvalues.
Its trace is $2\operatorname{Re}(A_2)_{01}$ and determinant is
$-\det A_2$, so that sum is
$\operatorname{Re}(A_2)_{01}+
\sqrt{(A_2)_{00}(A_2)_{11}-(\operatorname{Im}(A_2)_{01})^2}$.
For singular $A_2$, use the same factorization on its support; equivalently
approximate by $A_2+\epsilon I$ and take a convergent maximizing
contraction. At determinant zero the square root is
$|\operatorname{Re}(A_2)_{01}|$, giving the required positive part.
This includes $A_2=0$ and proves (NP.52). $\square$

**Proposition 8.2 (equality designs cannot extend the plateau).** If any
original finite design has acquired or live high cost $F$ on the
selected state, its strength satisfies $s\leq s_*$.

Proof. The certificate forces $H=H_*$. Since $H_+,H_-\succeq0$ sum
to this rank-one matrix, each has range in $\mathbb C h$. Hence
$\operatorname{Re}(H_+)_{DT}=0$. The $DT$ block of $I-H_*$ is

$$
A_L=\begin{pmatrix}1-p&i r_0\\-i r_0&1-q\end{pmatrix}>0,
\qquad\det A_L=s_*^2,\quad\operatorname{Re}(A_L)_{01}=0.
\tag{NP.53}
$$

The corresponding compression of $L_+$ lies between zero and $A_L$.
Lemma 8.1 bounds its real off-diagonal entry by $s_*/2$.
The necessary record equality gives
$s/2=\operatorname{Re}(L_+)_{DT}\leq s_*/2$. This establishes equality
nonexistence above the endpoint; the next theorem also excludes equality
as an unattained infimum. $\square$

**Theorem 8.3 (uniform quartic excess and the exact maximal interval).**
For the normalized selected state define

$$
\begin{aligned}
\delta_S&=\min\{(B_T+\lambda\alpha c_\xi)(1+q/p),C_S+\lambda\beta\}>0,\\
b_v&=k_\xi/t>0,\qquad B_{\rm bd}=1+\alpha+\beta+2\sqrt\alpha,\\
K_0&=\frac{2(1+B_{\rm bd}/b_v)}{\sqrt{\delta_S}}
       +\frac{1+B_{\rm bd}/b_v}{\delta_S}+\frac1{\lambda b_v}>0.
\end{aligned}
\tag{NP.54}
$$

For every $0\leq s\leq1$, both original acquired and supported-live
high costs satisfy, including their infima,

$$
E_s(\rho)\ \geq\ E_s^L(\rho)\ \geq\
F+\frac{((s-s_*)_+)^4}{144K_0^2}.
\tag{NP.55}
$$

Consequently $E_s(\rho)=F$ and $E_s^L(\rho)=F$ hold exactly on
$[0,s_*]$. This is the largest initial plateau, including its endpoint.

Proof. The diagonal and off-diagonal split of $B_\xi$ shows
$\|B_\xi\|_{\rm op}\leq B_{\rm bd}$; the off-diagonal norm is only
$\sqrt\alpha\sigma_\xi$, so the displayed bound is conservative.
Let $d=a_{\rm acq}-F\geq0$. The live excess is at most $d$.
Set $v=h/\sqrt t$, $P=vv^\dagger$, $Q=I-P$,
$\epsilon=\operatorname{tr}(QH)$ and $a_H=v^\dagger Hv$.
The spectral gap of $\mathcal S$ on $Q$ and the certificate give

$$
\epsilon\leq d/\delta_S,\quad
0\leq\operatorname{tr}(B_\xi H)-k_\xi\leq d/\lambda,\quad
0\leq a_H\leq1.
\tag{NP.56}
$$

The positive $P/Q$ block of $H$ has
$\|QHv\|^2\leq a_H\epsilon$, obtained by summing its positive
$2\times2$ minor inequalities in an orthonormal $Q$ basis. The trace
norm of its two off-diagonal blocks is $2\|QHv\|$, while $QHQ$ has
trace norm $\epsilon$. Thus, writing $E_H=H-a_HP$,

$$
\|E_H\|_1\leq2\sqrt\epsilon+\epsilon,\qquad
|a_H-t|\leq\frac{d/\lambda+B_{\rm bd}(2\sqrt\epsilon+\epsilon)}{b_v}.
\tag{NP.57}
$$

The second bound follows from
$(a_H-t)b_v=\operatorname{tr}(B_\xi H)-k_\xi-
\operatorname{tr}(B_\xi E_H)$ and trace/operator norm duality.
Combining the two bounds gives

$$
\|H-H_*\|_1\leq
2(1+B_{\rm bd}/b_v)\sqrt{d/\delta_S}
 +\left[\frac{1+B_{\rm bd}/b_v}{\delta_S}
                     +\frac1{\lambda b_v}\right]d
\leq K_0\sqrt d.
\tag{NP.58}
$$

The last step uses $0\leq d\leq1$: actual acquired mass on a normalized
input is at most one and $F>0$. The same argument works with
$d=\operatorname{tr}(CH)-F$, because
$0\preceq\Theta(H)\preceq\Theta(I)=I-M\preceq I$ also bounds the
live cost by one.

Apply Lemma 8.1 separately to the $DT$ blocks of
$0\preceq H_+\preceq H$ and $0\preceq L_+\preceq I-H$.
The total real off-diagonal entries of $H$ and $I-H$ cancel. Hence
(NP.19) implies

$$
\begin{aligned}
s&\leq\sqrt{f(H)}+\sqrt{g(H)},\\
f(H)&=H_{DD}H_{TT}-(\operatorname{Im}H_{DT})^2,\\
g(H)&=(1-H_{DD})(1-H_{TT})-(\operatorname{Im}H_{DT})^2.
\end{aligned}
\tag{NP.59}
$$

Both radicands are nonnegative. Let $z=\|H-H_*\|_1$.
Every entry change is at most $z$. For any positive contraction $H$,
its diagonals lie in $[0,1]$ and $|H_{DT}|\leq1/2$. Indeed positivity
of $H$ and $I-H$ bounds its square by
$\min(H_{DD}H_{TT},(1-H_{DD})(1-H_{TT}))\leq1/4$; if the diagonal
sum is at most one use the first product and otherwise the second.
The same bounds hold for $H_*$. Each diagonal product in (NP.59)
changes by at most $2z$, and each squared imaginary entry by at most
$z$. Since $f(H_*)=pq-r_0^2=0$ and $g(H_*)=s_*^2$, it follows that

$$
s\leq\sqrt{3z}+\sqrt{s_*^2+3z}
 \leq s_*+2\sqrt{3z}
 \leq s_*+2\sqrt{3K_0}\,d^{1/4}.
\tag{NP.60}
$$

Rearrange the positive part and raise to the fourth power to obtain
(NP.55). This uniform positive excess rules out limiting equality for
every $s>s_*$. Combined with Theorem 7.1 it proves exact maximality,
without a nonattainment shortcut. Constants in (NP.54) are attached to
the NORMALIZED selected state; unnormalized scaling is stated in §11.
$\square$

## 9. A complete actual upper at every later strength

**Proposition 9.1 (credited endpoint circuit and affine extension).** Put
$q_{\max}=k/(1-\alpha)\in(0,1)$ and $U_1=q_{\max}(A+B_T)$.
For $s_*\leq s\leq1$ let $\eta=(s-s_*)/(1-s_*)$. Then

$$
F+\frac{(s-s_*)^4}{144K_0^2}\leq E_s(\rho)
\leq U(s)=(1-\eta)F+\eta U_1.
\tag{NP.61}
$$

The upper has twenty-four actual acquired labels for $s_*<s<1$ and
twelve at either end. $U_1$ is a feasible endpoint value, and (NP.61)
is a bracket, not an evaluation of the later exact law.

Proof. Reuse the current JR strength-one construction. At report $r$
its high live product and two low live products are

$$
\frac{\sqrt{q_{\max}}D+r\sqrt{q_{\max}}T}{\sqrt2},\qquad
\frac{\sqrt{1-q_{\max}}D+r\sqrt{1-q_{\max}}T+\zeta S}{2},
\quad\zeta=\pm1.
\tag{NP.62}
$$

Precompose by $E^\dagger$. Use the high carrier of dimension three
with live isometry decoder $E$, and the low range encoders and full TP
isometry decoders of §7. The high matrix is invertible since
$q_{\max}(1-\alpha)=k>0$. Each low has nonzero first coefficient and
zero determinant because $(1-q_{\max})(1-\alpha)=\beta$; its rank is
two. Add the same two scalar supported failure rows and one scalar
complement map per report as in §7, with the same full TP decoders.

The coefficient sum at each report is $(I+rX_c)/2$: its diagonal
entries are $1/2$, the $DT$ entry is $r/2$, and the two $S$ cross
terms cancel. Equations (NP.49)–(NP.51) therefore prove full complex,
reference, every labelled Borel-time, complement, cross-support and
zero-extra identities for this twelve-label instrument at strength one.
The high aggregate is $\operatorname{diag}(q_{\max},q_{\max},0)$,
so its selected cost is $U_1$, with the imaginary $DT$ Gram entry making
no contribution.

To obtain strength $s$, generate a family label and take every endpoint
encoder from Theorem 7.1 multiplied in Kraus amplitude by
$\sqrt{1-\eta}$, and every encoder from (NP.62) multiplied by
$\sqrt\eta$. Equivalently scale a scalar CP map by its family weight.
Keep the full decoders. All generated labels, including the family label,
are retained as actual classical data; no coherent selector is hidden.
The effects sum to $(1-\eta)I_5+\eta I_5=I_5$, and their report effects
are $(1-\eta)F_r(s_*)+\eta F_r(1)=F_r(s)$.
Both complete forgotten channels equal (NP.11), so their convex sum
preserves that entire channel, including conditional reference laws.
The high effect is the same weighted sum and has cost $U(s)$.
There are twelve nonzero labels in each family, hence twenty-four at
interior weights; remove the zero family at either endpoint. Theorem
8.3 gives the lower bound. No pointwise optimality of this reused
endpoint circuit on the selected nonreal state is required. $\square$

## 10. A strict same-strength scalar-trace relaxation gap

**Lemma 10.1 (the exact real trace-zero face).** The true cone satisfies

$$
\{L\in\mathcal C_2:\operatorname{tr}(B_0L)=0\}
=\{L\succeq0:L\text{ is real symmetric},\operatorname{tr}(B_0L)=0\}.
\tag{NP.63}
$$

Proof. A nonzero plane atom has strictly negative $B_0$ trace.
For a quadratic-null atom,
$|u|^2=|\alpha v^2+\beta w^2|\leq\alpha|v|^2+\beta|w|^2$.
At equality $u\ne0$, and division by $u^2$ shows that
$\alpha(v/u)^2$ and $\beta(w/u)^2$ are nonnegative real numbers with
sum one. The equality case of the triangle inequality gives this also
when one term vanishes. Therefore $v/u,w/u$ are real and the projector
is real symmetric. Every atom's trace is nonpositive, so a finite sum
with trace zero consists only of these zero-trace atoms. This proves
one inclusion; Lemma 6.1 proves the other. This is the established
complex-cone trace face, restated with its proof for the application.
$\square$

**Definition 10.2 (only the scalar trace relaxation).** In the exact
coefficient constraints of Proposition 3.3 retain $H_r\succeq0$,
$\sum_r(H_r+L_r)=I$, the full effect relation defining $N$, and
$0\preceq N\preceq M$. Replace ONLY

$$
L_r\in\mathcal C_2\quad\hbox{by}\quad
L_r\succeq0,\quad\operatorname{tr}(B_0L_r)\leq0.
\tag{NP.64}
$$

Let $R_{\rm tr}(s,C)$ be the minimum of $\operatorname{tr}(C(H_++H_-))$
on this relaxed set. It exists: every positive variable is bounded by
$I$, and the set is closed and nonempty as the constructions below show.
This is an algebraic relaxation and not a physical competitor class.

The unrelaxed coefficient formulation has the same pointwise acquired
minimum as (NP.15), as established in the complex-cone reduction.
For clarity its converse does not require a hidden failure restriction:
spectrally decompose each $H_r$ into coefficient vectors assigned new
actual dimension-three branches, decompose $L_r$ into its finite singular
atoms with dimension-two range encoders, and use scalar Kraus rows for
$N$ or $M-N$ at the two reports. For general singular atoms, including
the plane, fix independent specimen columns $1,2$ when $u\ne0$,
columns $0,1$ when $u=0,v\ne0$, and columns $0,2$ otherwise.
The rank proof in Lemma 3.2 makes these pairs independent; apply
(NP.47) to that chosen pair to obtain the full TP range decoder.
The failure effects $N$ and $M-N$ have rank at most two because
their first row is zero. Decode each scalar with $w_\ell g(t)dt$,
and add a scalar complement effect $Q_5/2$ at each report, decoded at
label two. The total effect and forgotten channel are exactly (NP.14)
by the same proof as §7, including references and all time measures.
Each declared high branch is wholly live, so its acquired cost is the
coefficient objective. This establishes the converse for that NEW
instrument; it does not impose a half split on a general competitor.

**Theorem 10.3 (a quantitative gap with the same input, channel and strength).**
For every admitted state and EVERY $s\in[0,s_*]$,

$$
R_{\rm tr}(s,C)\leq\frac{k}{\delta_\xi}F<F=E_s(\rho),\qquad
E_s(\rho)-R_{\rm tr}(s,C)
 \geq\frac{F\beta(1-c_\xi)}{\delta_\xi}>0.
\tag{NP.65}
$$

No exact value of $R_{\rm tr}$ is asserted.

Proof. Since $\delta_\xi=p-\alpha q=k+\beta(1-c_\xi)>k$, put
$\zeta_{\rm tr}=k/\delta_\xi\in(0,1)$ and set

$$
H_r^{\rm tr}=\zeta_{\rm tr}H_*/2,\qquad
L_r^{\rm tr}=\frac{I-\zeta_{\rm tr}H_*+r sX_c}{2}.
\tag{NP.66}
$$

These are positive: $L_r^{\rm tr}=L_r+(1-\zeta_{\rm tr})H_*/2$.
Their report totals remain $(I+r sX_c)/2$, so the entire effect
relation gives $N=M/2$. All coefficient, normalization and record
constraints except the replaced memberships are unchanged. In addition
$\operatorname{tr}(B_0L_r^{\rm tr})=
[k-\zeta_{\rm tr}(p-\alpha q)]/2=0$. Their objective is
$\zeta_{\rm tr}F$. However
$\operatorname{Im}(L_r^{\rm tr})_{DT}=\zeta_{\rm tr}r_0/2\ne0$,
so Lemma 10.1 excludes them from the actual low cone.
The actual true minimum is attained and equals $F$ by §7.
Subtract the exhibited relaxed value to obtain (NP.65).
This is a strict resource separation at the SAME physical input, full
channel and strength. The earlier abstract cone obstruction supplies
the face mechanism; it alone would not evaluate this actual optimum
or yield this quantitative same-strength gap. $\square$

## 11. The original twelve-vector and closed boundaries

**Proposition 11.1 (one common vector, strictly dominated on the original twelve).**
For fixed admitted parameters the single plateau instrument of §7 has
all twelve original acquired costs

$$
\left(pA_y+qB_y\right)_{y,e,n},\qquad
A_y=\sum_i h_i^2p_{yi},\quad B_y=b^2p_{y0}+a^2p_{y1}.
\tag{NP.67}
$$

At every strength on its plateau, this vector is strictly dominated in
EVERY coordinate by the existing JR weak common vector $(kA_y)_{y,e,n}$.
It supplies no new original-twelve Pareto point.

Proof. The high effect is the ONE matrix $E\Theta(H_*)E^\dagger$.
All original $\rho_{y,e,n}$ are real symmetric; because $D,T,S$ are
real, their coefficient Grams are real symmetric. The imaginary $DT$
entry $(H_*)_{DT}=-ir_0$ cancels in the trace pairing and the $SS$
entry is zero, giving (NP.67) for every independent sign pair.
By (NP.32),
$p=k+\beta(1-c_\xi)+\alpha q>k$ and $q>0$, while $A_y,B_y>0$.
Thus $pA_y+qB_y>kA_y$ individually. Proposition 4.3 gives
$s\leq s_*<\sqrt\ell$, precisely within the credited JR weak regime
where ONE common instrument attains every $kA_y$. There is no prior,
averaging substitution or combination of separate pointwise minimizers
in this coordinatewise domination. The nonreal pointwise optimum and
this negative original-vector conclusion concern different test states
within the SAME original class. $\square$

**Proposition 11.2 (limits, mirrors and unnormalized inputs).** The
following boundaries are part of the stated laws.

As $\xi\downarrow0$ for fixed $\tau$, one has
$c_\xi\to1$, $\sigma_\xi\to0$, $\delta_\xi\to k$,
$p\to k$, $q,r_0,\gamma\to0$, $H_*\to k|D\rangle\langle D|$,
$F\to kA$ and $s_*\to\sqrt\ell$. For the last cost limit use
$\lambda\to A$. This is the inherited diagonal law as a limit;
$\xi=0$ is not a genuinely nonreal case. All admitted positive $\xi$
have positive $q,\gamma$, and the exact laws include $s=0$ and
$s=s_*$. The change from fourteen to twelve labels occurs at the
closed endpoint. At $s=0$ the binary report is fair on every normalized
input, but the finer actual labels can depend on input.

The negative-imaginary mirror uses conjugated FIXED encoder matrices
and the conjugated public input. Since $D,T,S$, the fixed channel and
prescribed effects are real, this is another valid CP instrument with
the same values, thresholds and counts. It is not an anti-linear
conjugation operation on an unknown specimen. A negative binary strength
is handled by swapping the two report names and using its absolute
value; the principal parameter range remains $[0,1]$.

For any positive five-mode input $\sigma$ with
$E^\dagger\sigma E=t_0\rho$, $t_0>0$, including complement and
cross-support terms, the exact plateau value is $t_0F$. The later
bracket becomes

$$
t_0\left[F+\frac{(s-s_*)^4}{144K_0^2}\right]
 \leq E_s(\sigma)\leq t_0 U(s)\quad(s\geq s_*).
\tag{NP.68}
$$

Proof of the scaling assertion. The full operator domination in (NP.19)
gives $\operatorname{tr}(G_{\rm acq}\sigma)\geq
\operatorname{tr}(\Theta(H)E^\dagger\sigma E)=t_0\operatorname{tr}(CH)$.
Use the NORMALIZED selected-state certificate and quartic bound, then
multiply by $t_0$. The constructed upper high effects are supported
on $V$ and ignore complement and cross-support in this expectation;
they give $t_0F$ or $t_0U(s)$. No acceptance division occurs, and the
normalization-dependent step $d\leq1$ is not applied to an unnormalized
$d$ with unchanged constants. If $t_0=0$, positivity also kills the
cross-support block of $\sigma$ and any of these full instruments has
zero supported high cost at every strength, so $E_s(\sigma)=0$.
This does not insert a singular Gram into a positive-definite formula.
The zero input is immediate. $\square$

These construction counts do not bound the minimum number of flags,
continuous-time symbols or exact-clock bits. A finite acquired alphabet
and a decoder with a continuous Borel output measure are different
mathematical objects.

## 12. Exact credit, parameter correspondence and the separate slot task

**Convention 12.1 (what is inherited and what is added).** The references
and named sources below keep their own hypotheses. An inherited ordinary
computer-assisted or literature statement is not kernel authority.

| Source | Precise inherited content and correspondence |
| --- | --- |
| [CG] §§1–4,13–16,21–28 | Original path/calibration/targets, exact isolated coefficient source and minimax, actual jointly counted factorization, positive product-rank bottleneck and homogeneous Schmidt cone; averaged-live stability, individual transfer penalties and near-optimal high-mass/error bounds. The full five-mode completion (NP.11) is the specified source channel. |
| [JR] §§29–40, especially §§34–40 | Evaluated all-strength diagonal law, one common attainer, sharp original sign means and worst-history law, with its stated broader all-error-optimizer/countable/integral scope. In its notation $\theta_{\rm JR}=\alpha$, $\omega_{\rm JR}=\beta$, $\delta_{\rm JR}=\ell$, $p_s=1-\beta-\alpha v_{\rm JR}$, $q_s=1-v_{\rm JR}$. Weak strengths have $(p_s,q_s)=(k,0)$; strong strengths have $p_s-\alpha q_s=k$ and $s=\sqrt{p_sq_s}+\sqrt{(1-p_s)(1-q_s)}$, ending at $p_s=q_s=k/(1-\alpha)$. The height cost is $p_sA_y+q_sB_y$, worst at $y=27$. |
| [RE] §§6–10 | Forced endpoint binary live maps, exhaustive endpoint singular lines, evaluated pointwise clipped scalar law, full separate attainers and paired/Pareto/nonattainment statements. Its earlier interior family is an upper construction. The feasible $U_1$ in §9 is not a replacement for its sharper evaluated endpoint law. |
| [IR] §§5,10–12 | Interior binary-live freedom, lawful coherent perturbations and mate reversal, no simultaneous pointwise optimizer/nonleast effects, compact full-complex coefficient reduction and pointwise attainment/frontier correspondence. Its integrated diagonal attribution belongs to current JR, as recorded in the companion. |
| *Native complex atomic cone and optimal resource faces*, §§3–9 (CA) | Full plane-plus-quadratic complex cone, Takagi lift with plane slack, at most six low atoms, trace-zero real face and concrete scalar-trace obstruction/separator, generic twenty-four-label exact reduction and sharp-mean equality-face classification, including singleton and exceptional-segment vectors. These are established inputs rather than new conclusions of this volume. |
| *Real coefficient Grams and a small-record resource law*, §§3–9 (RG) | Real symmetric PD-Gram two-branch spectral evaluation and certificate, explicit positive sufficient record caps, full fourteen-label attainers, rational source ratios, all original pure Grams and selected-coordinate Pareto points beyond sharp-mean faces. Those sufficient caps were not claimed maximal. Its real-Gram evaluation is not asserted for (NP.29). |
| This volume §§4–11 | An explicitly nonempty genuinely nonreal physical continuum; tilted inequality on the full singular locus, evaluated attained value and unique high aggregate; true-cone lift with fourteen/twelve actual labels; exact maximal plateau, quantitative quartic/affine later bracket and same-strength scalar-trace gap. Its original twelve-vector is strictly dominated, as §11 proves. |

The IR/CA/RG coefficient order is the same $(D,T,S)$, with exactly
the $h_i,a,b,c,d,M,\kappa$ in (NP.8), the compression $E$, and
$\alpha,\beta,\ell,k$ in (NP.10). CA uses $B_0$ and $\mathcal C_2$
as in (NP.17); RG's real spectral budget matrix $B$ is this $B_0$.
Its Gram entries are precisely (NP.16). The three diagonal Gram
entries on $\operatorname{diag}\tau$ are $A,B_T,C_S$ in the notation
of this volume; $C$ here always denotes the entire Gram matrix.
The high aggregate $H$ is a coefficient matrix and is distinct from the source matrix $H^{\rm src}$.

For positive diagonal input $\operatorname{diag}\tau$, JR's law is
$p_sA+q_sB_T$. The comparison $kA$ in (NP.36) refers to that known
weak diagonal value, not to a lower bound imposed on each coherent
state. Original four-sign means use the identity
$\frac14\sum_{e,n}\rho_{y,e,n}=\operatorname{diag}p_y$; this is a
linear relation, not an input prior. In arbitrary error optimizers,
record-preserving sign averaging relabels $r\mapsto en\,r$ and fixes
AVERAGED live Choi data and total failure effect. It does not prove
whole forgotten-channel uniqueness. The new individual lower theorem
is for (NP.11) and the full finite class in Definition 3.1. It makes no
new extension claim for countable or integral acquisition alphabets.

CA's general spectral test retains a PSD plane slack, then applies the
Takagi triangle condition to the bilinear form on the residual. It is
not only $\operatorname{tr}(B_0L)\leq0$, and the special transformation
$R$ in §6 does not remove that slack for arbitrary competitors. Similarly,
RG's selected-coordinate Pareto vectors and CA's classified sharp-mean
faces do not imply that every pointwise nonreal attainer is Pareto for
the original twelve. Proposition 11.1 gives the contrary conclusion
for this particular new construction.

**Proposition 12.2 (the current joint-transfer interface has a different resource).**
[Joint Transfer Interface][JG] §§9–14 concerns a single-slot supermap

$$
\mathcal S(\Phi)=\sum_c\mathcal D_c
 (\Phi\otimes\operatorname{id}_{m_c})\mathcal E_c,
\quad \sum_c\mathcal E_c^*(I)=I_d,
\quad\mathcal S(\Lambda)=\Lambda
 \ \text{for every TP complex Schur channel }\Lambda.
\tag{NP.69}
$$

Its decoders are TP on all of $M_d\otimes M_{m_c}$; $m_c$ is the
JOINT quantum bypass past the separately supplied $d$-dimensional slot.
Its distance is the UNHALVED diamond distance to the entire TP Schur
class. Its sharp auxiliary capped-memory and high-memory-mass frontiers
are not numerical values or lower bounds for (NP.15) or for the original
half-cq error.

Proof and scope correspondence. Identity fixing in that task forces
$\mathcal D_c\mathcal E_c=p_c\operatorname{id}$ by rank-one Choi
support, with $\mathcal E_c^*(I)=p_c I$ by full TP of the decoder.
Thus its ACTUAL branch probabilities $p_c$ are input independent.
They differ from the history-dependent acquired masses in (NP.15).
Even when $m_c=1$, the slot still retains a $d$-dimensional system;
its total coherent code is not an original dimension-one acquired fibre.
Conversely the original acquisition charges its ENTIRE joint future
quantum payload, not only a bypass around another supplied operation.
Its every-input binary law (NP.13) does not require all-Schur fixing
or fixing dephasing.

At one original height the four pure vectors
$(e\sqrt{y/128},n\sqrt{(64-y)/128},1/\sqrt2)$ span $\mathbb C^3$
by their three signed sums. Their single-sign-flip overlaps are
$1-y/64$ and $y/64$, both positive; their simultaneous-flip overlap is
zero. If a CPTP repair fixes these four densities, a Stinespring
isometry maps each to the same vector tensored with an environment
state. Inner-product preservation on the connected four-cycle of
nonzero overlaps forces all environment states identical. Spanning
then forces identity on the embedded qutrit, including references,
but not on $V^\perp$ or its cross-support operators. This is JG's
source application of the known Mayer–Knill rigidity theorem.
The original simulator instead changes its live states to successors
and produces the failure laws (NP.5); it is not required to fix those
four source states. That repair calibration is therefore EXTRA.
The auxiliary sharp uniform lower bound also uses dephasing fixing,
which source-state calibration alone does not imply.

A transfer into the original problem would require a proved
transformation of the FULL original instrument preserving all twelve
target comparisons, contracting their full half-cq errors, and not
increasing actual jointly counted acquisition cost. Equation (NP.69)
and its auxiliary diamond or bypass bounds supply no such map.
Consequently no slot cap, branch probability, high-memory allowance or
distance is inserted into $E_s$, $E_*$, $F$ or the twelve-vector frontier.
A specialized non-source-preserving reduction is not excluded by this
argument. JG's distinct-slot results neither subsume nor invalidate the
nonreal plateau proved here. $\square$

**Convention 12.3 (mature methods and literature boundaries).** Choi/Kraus
vectorization, positive-sum support, product ranks, trace/operator duality,
Cauchy–Schwarz, real spectral theory, Takagi congruence, positive-block
compression and zero-Rayleigh decompositions are mature tools. The
additional application is `repo-derived` relative to the supplied source
bodies, with its full ordinary derivations above. Generic spectral or
cone machinery is not claimed as invented here.

The sources report Heinosaari–Jivulescu–Reeb–Wolf for finite CP extension,
Terhal–Horodecki for Schmidt-number overlap bounds,
Chruściński–Kossakowski for the Choi/Kraus correspondence, Sekatski for
classical-assisted dimension bottlenecks, and coherence/covariance and
instrument-postprocessing literature in their stated scopes. JG credits
Mayer–Knill's *Quantum process fidelity bounds from sets of input states*,
§V, Theorem 1, for its source-state rigidity, and distinguishes its
all-Schur-fixing task from the transition-preserving dephasing-superchannel
and classically correlated supermap literature. These are inherited
attributions, not independent authentication of those external texts or
of private-library compatibility. The fixed-source algebraic isolation,
enclosures, bordered Jacobian, normalization/minimax and nested control,
instrument and calibration premises retain their supplied conditional
status. No literature-wide absence, novelty or priority claim follows.
Other referenced classical acquisition/count programmes have different
carriers, targets and paid resources; no quantum correspondence is
supplied by a shared name or an analogous cone obstruction.

## 13. Continuing mathematical and native obligations

**Open problem 13.1 (the unchanged broader mathematical programme).**
Continue evaluating $E_s(\rho)$ for ALL positive complex supported inputs
and all strengths. General nonreal $DS$ and $TS$ coherences, mixed
real/imaginary $DT$ inputs beyond the admitted continuum, singular
coefficient Grams, and later exact values above this family's plateau
remain outside the evaluated law. The bounds (NP.61) do not evaluate
those later values. Determine general minimizers; for the original
twelve, retain the known endpoint laws and real-PD common interval while
seeking their individual later laws and maximal plateau endpoints.
Classify the ENTIRE twelve-coordinate undominated frontier beyond the
known sharp-mean faces and selected-coordinate Pareto points. Neither
a compact reduction nor separate pointwise attainers constitutes that
classification. The new strictly dominated vector is not a frontier
component.

The original full-error restricted questions also remain separate: a
live-membership test or an auxiliary slot replacement does not determine
the optimal full exact-time error on an intersected native restriction.
No unconditional-prefix optimum, whole-channel uniqueness, new kernel
or frozen-truth result, quantum capacity formula, generic neural-network
or empirical-learning conclusion is asserted.

**Definition 13.2 (actual native realization obligations).** The finite
CP encoders and full TP decoders in §§7,9 are explicit ordinary
instruments. A native realization under the original permissions must
still supply lawful access to the sole unresolved specimen, actual
classical flags, calibrated encoding, storage of the ENTIRE jointly
counted coherent carrier, and permitted controlled range decoding.
No discarded environment or entanglement share may reappear as a free
bypass. The support correspondence $E$ must be calibrated, and the
acquisition cut and all decoding must fit the SAME aligned original
clock without added execution time. Source/preparation/epoch identity,
calibrations, permissions, controller updates, metadata and old stopped
archives must all match their original branches.

A native time service must cause the FIRST absorbing event at actual
elapsed time $t$, absolute $6+t$, perform no later positive-carrier
action on that failed branch, and deliver terminal live output at time
one. The scalar measure $g(t)dt$, a generated label destined to fail,
or a sampled timestamp written after another event does not itself
implement that physical event or finite exact-clock storage. Mathematical
CPTP completion and isometry formulas do not install these services.
All complex/reference, original separate labels, zero sectors,
complement and cross-support identities must hold simultaneously.

The original control predicate in §1 gives finite-duration strict-domain
regularity and chronological path permissions. Its probability-changing
geometry includes the fields $P=\partial_\kappa$ and
$Q=\sum_a w_a(\kappa)\partial_{h_a}$; the credited double-wall bracket
is $[P,Q]=-(\partial_u+\partial_v)/r_b\ne0$. Thus a conditional
Schur/diagonal closure is not an exhaustive native menu. Conversely
noncommuting paths do not synthesize arbitrary rotations, acquisition,
controlled range decoders or swaps on an unknown specimen. Neither
native feasibility or efficiency nor global native impossibility is
proved by this volume. The complete original acquisition/control,
absorbing-event, archive and clock programme remains active.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[RE]: FIB_NATIVE_FIXED_CHANNEL_RECORD_RESOURCE_ENVELOPE.md
[IR]: FIB_NATIVE_INTERIOR_RECORD_RESOURCE_REDUCTION.md
[JG]: FIB_NATIVE_JOINT_TRANSFER_COHERENCE_INTERFACE_GEOMETRY.md

## 追加锚（本行以下为增补区）
