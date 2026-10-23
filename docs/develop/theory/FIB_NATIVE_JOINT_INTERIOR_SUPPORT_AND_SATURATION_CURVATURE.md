# Joint interior records: support obstruction and saturation curvature

## 1. Conditional experiment and exact limiting problem

**Convention 1.1 (sources and scope).** The isolated CG root, its
isolation/Jacobian certificate, exact ranks, TP normalization and original
minimax/support identification are named `ASSUMED-UNVERIFIED`
antecedents. Operator equalities apply at that root. Supplied enclosures
are conditional inequalities, not off-root normalization. All statements
here are ordinary conditional mathematics.

[JR] denotes *Native complete-continuation joint record and quantum
payload*; [RC] denotes *Native complete-continuation residual contact
curve*; [FA] denotes *Native complete-continuation finite activity
frontier*. WE denotes the supplied companion *Weak finite-activity
endpoint: an evaluated feasibility constant and the full-record limit*.
JS denotes the supplied companion *Joint endpoint records: the evaluated
finite-activity saturation boundary*. Their named results retain their
stated analytic and CP hypotheses.

There is one unknown normalized reached-cut specimen in the original
five modes $(0,1,2,3,13)$. Write

$$
\begin{gathered}
E=((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2),\qquad P=EE^\dagger,\\
p_y=(y/128,(64-y)/128,1/2),\quad a_y=(\sqrt{p_{yi}})_i,\\
\rho_{y,e,n}=U_{e,n}a_ya_y^TU_{e,n}^\dagger,\quad
U_{e,n}=\operatorname{diag}(e,n,1),\\
y\in\{5,16,27\},\qquad e,n\in\{\pm1\}.
\end{gathered}
\tag{SC.1}
$$

The received state is $E\rho_{y,e,n}E^\dagger$; original height is
$y/256$ and winding parity is $en=(-1)^m$. Neither history is supplied.
The ideal live block remains the entire coherent matrix
$EU_{e,n}B_y^{\rm ideal}U_{e,n}^\dagger E^\dagger$ of CG.111. The five
separate ideal failure measures are $w_\ell f_y(u)du\,P_f$, with

$$
w=(0,1/4,1/2,1/4,0),\qquad f_y(u)=\frac{6y}{(y+6u)^2},\qquad 0\le u\le1.
\tag{SC.2}
$$

Absolute time is $6+u$. Error is HALF the full stopped-cq trace norm,
maximized over all twelve histories, including every live coherence,
singular-time part, abort, wrong-support and zero-target sector. Every
passive-reference amplification retains its conditional reference
operators. The recovery density $g(u)=2/(1+u)^2$ never replaces the
ideal $f_y$.

An acquisition has CP encoders of total effect $I_5$, actually generated
dephased labels, and whole-fibre full-output TP decoders. Each fibre
jointly counts every future-accessible input-bearing specimen, memory,
quantum controller, environment, return system and entanglement share.
Other dilation systems are permanently inaccessible before the same cut.
The cost is the sharp worst-history ACQUIRED probability of dimension
at least three, including later failure. With binary plus effect $F$,
the constraint remains

$$
\mathsf V(F)=2|\operatorname{Re}F_{01}|/\kappa\ge s,
\qquad \mathsf W=\mathsf C(s),\qquad E(\Phi)=E_*.
\tag{SC.3}
$$

Other effect coordinates and the forgotten full channel remain free.
There is no prior, helper, copy, postselection, acceptance division,
reset, retry, readable history, hidden Kraus access, bypass or free time.

Use exactly FA Definition 67.2: measurable PSD first-event rates on
whole fibres have integrable operator norm; arbitrary admitted
noncommuting and unobserved TP survivor controls are allowed; terminal
survivor processing is TP on the whole fibre. Loss obeys trace balance.
There is no singular or forced deadline failure, or positive-carrier
action after first absorption. Activity is the supremum over labels of
the integrated rate norm. Necessity covers finite and convergent
countable instruments and exactly CG Convention 21.3's stipulated
measurable/integrable finite-fibre extension, without further
continuous-outcome or infinite-dimensional extensions. More explicitly,
for each survivor map $\mathcal S_{j,u}$,

$$
-\frac d{du}\operatorname{tr}\mathcal S_{j,u}(X)
=\operatorname{tr}(R_j(u)\mathcal S_{j,u}(X)),\quad
\mathcal S_{j,0}=\mathrm{id},\qquad
\mathsf A=\sup_j\int_0^1\|R_j(u)\|du.
$$

Use a maximum for finite labels and the stipulated essential supremum
for integral instruments. For nonempty classes, $\mathcal T_A(s)$ is
the supremal TV between the full actual acquisition-label laws at
$(5,+,+)$ and $(27,+,+)$, under (SC.3) and $\mathsf A\le A$.
The necessary measurable extension retains measurable Kraus fields,
integrable effects/live Choi matrices and whole-output TP decoders
almost everywhere. Empty classes have no claimed TV maximum.

**Definition 1.2 (source coefficients).** Use JS.6--JS.8:

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=ae_0e_1^T+be_1e_0^T,\quad S=ce_0e_2^T+de_2e_0^T,\\
M=\operatorname{diag}(0,m_1,m_2),\qquad
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\\
\theta=ab/(h_0h_1),\quad\omega=cd/(h_0h_2),\quad
\delta=\theta+\omega,\quad s_0=\sqrt\delta,\quad\kappa=h_0a+h_1b,\\
\alpha=\theta/\delta,\quad\beta=\omega/\delta,\quad U=1/\alpha,\\
V=m_2h_1^2/b^2,\quad W=m_1h_2^2/d^2,\quad
\mu=\alpha V+\beta W,\quad r=V/\mu.
\end{gathered}
\tag{SC.4}
$$

All seven amplitudes and $m_i$ are positive; $0<\delta<1$,
$\alpha+\beta=1$, and $0<r<1<U$. The undecorated $d$ is the source
amplitude. On the entire closed interval $[0,U]$ set

$$
\begin{aligned}
Y(x)&=(1-\alpha x)/\beta,& H(x)&=(\sqrt x-1)^2/2,\\
D_c(x)&=D_0+D_1x=\delta h_0^2+b^2x+d^2Y(x),\\
N_c(x)&=N_0+N_1x=\delta h_1^2h_2^2+a^2h_2^2x+c^2h_1^2Y(x),\\
c_*(x)&=N_c(x)/D_c(x),& \rho_c(x)&=D_c(x)/N_c(x),\\
\mathcal F(x)&=H(x)\rho_c(x),& C_{\rm end}&=\mu\mathcal F(r).
\end{aligned}
\tag{SC.5}
$$

Both affine functions $D_c,N_c$ are strictly positive, including the
axes. The radial $x$ is unrelated to history height.

On $\mathcal E=\{(z,w):\alpha z^2+\beta w^2=1\}$ put

$$
\begin{gathered}
h(z,w)=(1,z,w)^T,\quad K(z,w)=s_0D+zT+wS,\\
n(z,w)=(0,dw/h_2,-bz/h_1)^T,\quad
\Delta=\rho_{27,+,+}-\rho_{5,+,+},\quad k(z,w)=n^T\Delta n,\\
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\quad
(K_0,K_1,K_2)=(D,T,S),\quad L=\operatorname{diag}(s_0,1,1),\\
G=LNL,\qquad f(z,w)=h(z,w)^TGh(z,w),\\
d_f=11m_1/64,\quad z_f=\sqrt{m_1m_2}(\sqrt{37}-\sqrt{59})/16<0,\\
\Xi=\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},\quad
L_f=\sqrt{d_f^2+4z_f^2},\quad
\gamma=(L_f-d_f)/2>0,\quad b_f=(L_f+d_f)/2>0,\\
u_f=\frac{-2z_f}{d_f+L_f}\in(0,1),\quad
e_+=\frac{(u_f,-1)^T}{\sqrt{1+u_f^2}},\quad
e_-=\frac{(1,u_f)^T}{\sqrt{1+u_f^2}}.
\end{gathered}
\tag{SC.6}
$$

Thus $\Xi e_+=\gamma e_+$, $\Xi e_-=-b_fe_-$ and
$\gamma+b_f=L_f$. For a nonnegative ellipse measure write
$C_\nu=\int\mathcal F(z^2)d\nu$. The limiting problem is exactly JS.20:

$$
\Phi(\lambda)=\max\left\{\int k_+d\nu:
\int nn^Td\nu=M,\quad C_\nu\le\lambda\right\}.
\tag{SC.7}
$$

Its covariance fixes mass $\mu$, $z^2$ moment $V$ and $zw$ moment zero;
the $w^2$ moment is $W$. JS Lemma 4.2 supplies compact attainment and
an at-most-five-atom representative, including axes. These are credited
facts, not new support bounds here.

For explicit endpoint values set

$$
\begin{gathered}
a_+=\frac{\alpha V+\beta Wu_f^2}{1+u_f^2},\quad
a_-=\frac{\alpha Vu_f^2+\beta W}{1+u_f^2},\\
x_+=\frac{V}{\alpha V+\beta Wu_f^2},\quad
x_-=\frac{Vu_f^2}{\alpha Vu_f^2+\beta W},\\
C_{\rm sat}=a_+\mathcal F(x_+)+a_-\mathcal F(x_-),\\
H_{\rm live}=(1-\delta)\Delta A,\quad
\Delta A=\operatorname{tr}(D^\dagger D\Delta)>0,\\
S_{\rm corner}=\tfrac14\sum_{\sigma,\eta=\pm1}|f(\sigma,\eta)|,\quad
T_0=(H_{\rm live}+S_{\rm corner}+L_f)/2,\quad B_0=T_0-\gamma.
\end{gathered}
\tag{SC.8}
$$

JS Theorems 8.2 and 9.2 give $C_{\rm end}<C_{\rm sat}$,
$\Phi(C_{\rm end})=0$, $\Phi(C_{\rm sat})=\gamma$, continuity,
concavity and strict increase between them. The formula for $C_{\rm sat}$
and the spectral equality cases are credited JS results.

## 2. Global convexity of the exact source cost

**Theorem 2.1 (P1: strict convexity through both axes).** The function
$\mathcal F$ is strictly convex on $[0,U]$. Every tangent at an interior
point is strictly supporting away from that point.

Proof. The supplied JR.52, JR.86 and FA Proposition 74.1 enclosures imply

$$
\beta<1/8,\quad \alpha/\beta<8,\quad \delta>39/2500,\quad
h_0>123/125,\quad b>29/200,\quad a<33/500,\quad
h_1>353/500,\quad d<1/10.
\tag{SC.9}
$$

They also give $J=adh_2-bch_1>0$: the lower product
$65\cdot98\cdot809=5153330$ exceeds the upper product
$147\cdot16\cdot707=1662864$, with common denominator $10^9$.
These are symbolic uses of inherited inequalities. Substitution gives

$$
\begin{gathered}
D_0=\delta h_0^2+d^2/\beta>0,\quad
N_0=\delta h_1^2h_2^2+c^2h_1^2/\beta>0,\\
D_1=-bJ/(ch_1)<0,\quad N_1=(ah_2/d)J>0,\\
\rho_c'=\frac{D_1N_0-D_0N_1}{(N_0+N_1x)^2}<0,\qquad
\rho_c''=\frac{-2N_1(D_1N_0-D_0N_1)}{(N_0+N_1x)^3}>0.
\end{gathered}
\tag{SC.10}
$$

For $0<x<1$, $H'<0$ and $H''=1/(4x^{3/2})>0$, so
$\mathcal F''=H''\rho_c+2H'\rho_c'+H\rho_c''>0$.
For $1\le x\le U$, (SC.9) gives $U<8/7$, $\sqrt U<15/14$ and

$$
\begin{gathered}
D_c\ge\delta h_0^2+b^2>
(39/2500)(123/125)^2+(29/200)^2>9/250,\\
|D_1|<d^2\alpha/\beta<2/25,\qquad
|D_1|/D_c<20/9<9/4,\\
0<N_1/N_c<a^2/(\delta h_1^2)<
\frac{(33/500)^2}{(39/2500)(353/500)^2}<3/5.
\end{gathered}
\tag{SC.11}
$$

Hence $-\rho_c'/\rho_c<57/20$. Retaining the nonnegative term
$H\rho_c''$ and using $2H'=1-1/\sqrt x$ yields

$$
\begin{aligned}
\mathcal F''(x)
&\ge\frac{\rho_c(x)}{4x^{3/2}}
\left[1-4x(\sqrt x-1)\left(\frac{|D_1|}{D_c}+\frac{N_1}{N_c}\right)\right]\\
&>\frac{\rho_c(x)}{4x^{3/2}}
\left[1-\frac{16}{49}\frac{57}{20}\right]
=\frac{17}{245}\frac{\rho_c(x)}{4x^{3/2}}>0.
\end{aligned}
\tag{SC.12}
$$

Continuity at both endpoints extends strict convexity to the closed
interval. Integrating the strictly increasing interior derivative proves
the strict tangent inequalities, also at the endpoints. There is no
finite right derivative at $x=0$: $\mathcal F'(x)\to-\infty$ there.
At $U$ the radial formula has a finite one-sided derivative. In
particular this theorem does not assert differentiability of its
circle pullback at every physical axis. $\square$

## 3. Evaluated two-line obstruction and four-line existence

**Definition 3.1 (whitened cost and explicit threshold).** Set
$A_*=\alpha V$, $B_*=\beta W$ and, for $0\le p\le1$, define

$$
A(p)=B_*+(A_*-B_*)p,\quad x(p)=Vp/A(p),\quad
\mathcal J(p)=A(p)\mathcal F(x(p)),\quad
\mathcal C(p)=\mathcal J(p)+\mathcal J(1-p).
\tag{SC.13}
$$

The scalars $A_*,B_*$ are unrelated to activity and $B_0$. Put
$p_z=d_f^2/L_f^2$, $p_s=1/(1+u_f^2)$ and

$$
\begin{gathered}
R_1=\alpha Vd_f^2+4\beta Wz_f^2,\quad
R_2=4\alpha Vz_f^2+\beta Wd_f^2,\\
\boxed{C_{\rm two}=\frac{R_1}{L_f^2}
\mathcal F\!\left(\frac{Vd_f^2}{R_1}\right)
+\frac{R_2}{L_f^2}
\mathcal F\!\left(\frac{4Vz_f^2}{R_2}\right)=\mathcal C(p_z).}
\end{gathered}
\tag{SC.14}
$$

This is a finite rational/radical expression with no residual
minimization or root selection. The $R_i$ in (SC.14) are local scalars,
not JR's endpoint residues.

**Lemma 3.2 (exact whitening and line equivalence).** With
$M_2=\operatorname{diag}(m_1,m_2)$, let
$t=M_2^{-1/2}n$, $e=t/\|t\|$ and $dm=\|t\|^2d\nu$. Then

$$
\int ee^Tdm=I_2,\quad \int dm=2,\quad
C_\nu=\int d(e)dm,\quad \int k_+d\nu=\int(e^T\Xi e)_+dm,
\tag{SC.15}
$$

where, for a unit whitened vector $e=(e_1,e_2)^T$,

$$
a_e=\alpha Ve_2^2+\beta We_1^2,\quad
z_e=-\sqrt V e_2/\sqrt{a_e},\quad
w_e=\sqrt W e_1/\sqrt{a_e},\quad
d(e)=a_e\mathcal F(Ve_2^2/a_e)=\mathcal J(e_2^2).
\tag{SC.16}
$$

Conversely $d\nu=a_e dm$ at these ellipse points. A failure line
corresponds to the two antipodal ellipse points. Proportional splitting
and antipodal reversal change neither cost nor objective.

Proof. Directly $t=(w/\sqrt W,-z/\sqrt V)^T$, and the ellipse equation
implies $a_e=1/\|t\|^2$. Also
$n(z_e,w_e)=M_2^{1/2}e/\sqrt{a_e}$. Thus (SC.15) follows by
congruence, including at both axes. The inverse formulas are unique up
to simultaneous reversal. $\square$

**Theorem 3.3 (P2: support obstruction and optimizing representation).**
One has $C_{\rm end}<C_{\rm two}<C_{\rm sat}$. For
$C_{\rm end}<\lambda\le C_{\rm two}$, no optimizing failure measure
can have at most two distinct failure lines. For every
$C_{\rm end}<\lambda<C_{\rm sat}$ every optimizer uses cost exactly
$\lambda$, and some optimizer has at most four failure lines. Thus the
minimum optimizing line count in the initial specified interval is
three or four. These counts concern failure directions, not minimum
physical labels or all their proportional splittings.

Proof. Two distinct whitened lines with weights $t_1,t_2>0$ must obey
$t_1e_1e_1^T+t_2e_2e_2^T=I_2$. The square matrix with columns
$\sqrt{t_i}e_i$ is orthogonal, so the lines are orthogonal and both
weights are one. One line cannot have rank-two covariance. If the
larger squared second coordinate is $p\ge1/2$, their cost is
$\mathcal C(p)$.

For $0<p<1$, direct differentiation and Theorem 2.1 give

$$
x'(p)=VB_*/A(p)^2,\qquad
\mathcal J''(p)=\frac{V^2B_*^2}{A(p)^3}\mathcal F''(x(p))>0.
\tag{SC.17}
$$

Thus $\mathcal C$ is symmetric about $1/2$ and strictly increasing on
$[1/2,1]$. At $1/2$, both radial coordinates are $r$ and
$A(1/2)=\mu/2$, giving $\mathcal C(1/2)=C_{\rm end}$. The spectral
pair gives $\mathcal C(p_s)=C_{\rm sat}$.

The supplied $m_1>496/1000$, $m_2<345/1000$ imply

$$
\frac{d_f}{2|z_f|}
=\frac{\sqrt{59}+\sqrt{37}}{16}\sqrt{m_1/m_2}
>\frac{27}{32}\sqrt{496/345}>1,
\tag{SC.18}
$$

since $729\cdot496=361584>353280=1024\cdot345$.
For the favorable off-diagonal sign the possible positive expectation
of an orthogonal pair is

$$
g(p)=2|z_f|\sqrt{p(1-p)}-d_f(1-p),
\tag{SC.19}
$$

and its companion is negative. With the other sign the only possible
candidate is $2|z_f|\sqrt{p(1-p)}-d_fp<0$ for $p\ge1/2$.
For $p<1$, (SC.19) is positive exactly when $p>p_z$; at $p=1$
both expectations are nonpositive. Also $1/2<p_z<p_s<1$, because
$g(p_s)=\gamma>0$. Strict increase of $\mathcal C$ proves the
claimed constant inequalities. A two-line measure with positive
objective must have cost strictly above $C_{\rm two}$. JS Theorem
9.2 gives $\Phi(\lambda)>0$ above $C_{\rm end}$, proving the
obstruction, including at $\lambda=C_{\rm two}$. Two-line feasibility
itself is not excluded.

If an optimizer had cost $C'<\lambda<C_{\rm sat}$, its same value
would be feasible at $C'$, contradicting JS's strict increase (and its
zero value at $C_{\rm end}$). Thus cost is active. Begin with JS
Lemma 4.2's at-most-five-atom optimizer, merging antipodal duplicates.
If five distinct lines remain, the constraint columns

$$
(1,z_i^2,z_iw_i,\mathcal F(z_i^2))^T\in\mathbb R^4
\tag{SC.20}
$$

have a nonzero linear dependence $c_i$. Its first coordinate gives
$\sum c_i=0$, so both signs occur. Small weight changes in both
directions preserve covariance and active cost. Optimality forces
$\sum c_i k(z_i,w_i)_+=0$, since otherwise one direction improves the
objective. Move until a weight vanishes. The same covariance, cost and
value then have at most four lines. This is an existence statement;
it does not restrict arbitrarily split optimizing measures. $\square$

## 4. Sharp saturation loss over all measures

**Definition 4.1 (evaluated derivative coefficient).** For $x>0$ put

$$
\begin{aligned}
\mathcal F_1(x)
&=\frac{(1-1/\sqrt x)(D_0+D_1x)}{2(N_0+N_1x)}
+\frac{(\sqrt x-1)^2(D_1N_0-D_0N_1)}{2(N_0+N_1x)^2},\\
\mathcal J_1(p)
&=(A_*-B_*)\mathcal F(x(p))+
\frac{VB_*}{A(p)}\mathcal F_1(x(p)),\\
\boxed{D_{\rm sat}}
&=\boxed{\frac{2u_f}{1+u_f^2}
[\mathcal J_1(p_s)-\mathcal J_1(1-p_s)]>0},\\
\boxed{K_{\rm sat}}&=\boxed{L_f/D_{\rm sat}^2>0}.
\end{aligned}
\tag{SC.21}
$$

These are finite source rational/radical expressions. In particular no
differentiation or minimization remains unevaluated in their definition.
The arguments $x(p_s),x(1-p_s)$ lie strictly between $0$ and $U$.
Differentiation gives $\mathcal F_1=\mathcal F'$,
$\mathcal J_1=\mathcal J'$. Strict positivity of $D_{\rm sat}$ follows
from (SC.17), $p_s>1/2$ and $u_f>0$.

**Theorem 4.2 (P3: quadratic saturation with full-measure necessity).**
There are source-dependent constants $h_{\rm loc},K>0$ such that

$$
\boxed{\left|\Phi(C_{\rm sat}-h)-\gamma+K_{\rm sat}h^2\right|
\le Kh^3\qquad(0<h<h_{\rm loc}).}
\tag{SC.22}
$$

In particular $\Phi$ has left derivative zero at $C_{\rm sat}$. The
neighborhood is existential; no explicit size or projective optimality
is asserted.

Proof. First rotate the spectral pair simultaneously:

$$
e_+(\vartheta)=\cos\vartheta\,e_++\sin\vartheta\,e_-,\qquad
e_-(\vartheta)=-\sin\vartheta\,e_++\cos\vartheta\,e_-.
\tag{SC.23}
$$

Use the ellipse points and masses $a_e$ of (SC.16). Their covariance
is exactly $M$ for every $\vartheta$. For sufficiently small
$\vartheta$, their expectation signs retain the strict spectral signs,
so their objective is $\gamma-L_f\sin^2\vartheta$. Their cost is
$\mathcal C(p(\vartheta))$, where

$$
p(\vartheta)=\frac{(-\cos\vartheta+u_f\sin\vartheta)^2}{1+u_f^2},
\qquad p'(0)=-2u_f/(1+u_f^2).
\tag{SC.24}
$$

Its cost derivative at zero is $-D_{\rm sat}$. Both physical coordinates
are nonzero at the two spectral vectors. Hence this cost is analytic
near zero, and the inverse-function theorem gives
$\vartheta(h)=h/D_{\rm sat}+O(h^2)>0$ with cost exactly
$C_{\rm sat}-h$. This admissible family gives, for the optimal deficit,

$$
0\le\mathfrak d(h):=\gamma-\Phi(C_{\rm sat}-h)
\le K_{\rm sat}h^2+O(h^3).
\tag{SC.25}
$$

A separate argument is needed for sharpness against every measure.
Use (SC.15) for any covariance-admissible measure, and write its unit
vectors in the spectral basis as $e=\xi e_++\eta e_-$.
Partition the circle into $\Omega_+=\{\gamma\xi^2-b_f\eta^2>0\}$
and $\Omega_-$, assigning the zero boundary to the latter. Write

$$
\begin{gathered}
d_+=d(e_+),\quad d_-=d(e_-),\quad
R(e)=d(e)-d_+\xi^2-d_-\eta^2,\\
r_+=\left.\frac{d}{dt}d(\cos t\,e_++\sin t\,e_-)\right|_{t=0},\quad
r_-=\left.\frac{d}{dt}d(\cos t\,e_-+\sin t\,e_+)\right|_{t=0}.
\end{gathered}
\tag{SC.26}
$$

The simultaneous cost derivative proves $r_+-r_-=-D_{\rm sat}$.
There is a finite source constant $K_0>0$ such that, on the entire unit
circle, respectively,

$$
|R(e)-r_+\xi\eta|\le K_0\eta^2,\qquad
|R(e)-r_-\xi\eta|\le K_0\xi^2.
\tag{SC.27}
$$

Here is the global remainder justification. The cost $d(e)$ is even,
continuous and bounded on the full circle because $a_e>0$ and
$\mathcal F$ is continuous on $[0,U]$. Near $\pm e_+$ it is analytic:
neither physical coordinate vanishes there. In the coordinate
$\eta/\xi$, the first numerator in (SC.27) has zero constant and
linear terms, so its quotient by $\eta^2$ is bounded locally. Evenness
handles both antipodes. Near $\pm e_-$, the coordinate $\xi/\eta$
gives the same statement for the second numerator. Away from those
respective neighborhoods, the denominators are bounded away from zero
and continuity on a compact set bounds the quotients. This includes
both physical axes, where no differentiability is required. At a
zero-expectation boundary both spectral coordinates are nonzero. Thus
(SC.27) also permits either boundary assignment without omitting any
measure or axis mass.

Define

$$
\mathsf u=\int_{\Omega_-}\xi^2dm,\quad
\mathsf v=\int_{\Omega_+}\eta^2dm,\quad
\mathsf m=\int_{\Omega_+}\xi\eta\,dm.
\tag{SC.28}
$$

Covariance gives $\int\xi^2=\int\eta^2=1$ and $\int\xi\eta=0$.
Thus the positive and negative aggregate effects in this basis are

$$
E_+=\begin{pmatrix}1-\mathsf u&\mathsf m\\\mathsf m&\mathsf v\end{pmatrix}
\succeq0,\qquad
E_-=\begin{pmatrix}\mathsf u&-\mathsf m\\-\mathsf m&1-\mathsf v\end{pmatrix}
\succeq0,\qquad E_++E_-=I_2.
\tag{SC.29}
$$

For this measure's deficit $\mathfrak d=\gamma-\int(e^T\Xi e)_+dm$,

$$
\mathfrak d=\gamma\mathsf u+b_f\mathsf v,\quad
\mathsf m^2\le(1-\mathsf u)\mathsf v\le\mathsf v,\quad
\mathsf m^2\le\mathsf u(1-\mathsf v)\le\mathsf u,\quad
\mathfrak d\ge L_f\mathsf m^2.
\tag{SC.30}
$$

Integrate the first remainder on $\Omega_+$ and the second on
$\Omega_-$. Since $d_++d_-=C_{\rm sat}$, this gives the exact estimate

$$
C_\nu-C_{\rm sat}=-D_{\rm sat}\mathsf m+\mathcal R,\qquad
|\mathcal R|\le K_0(\mathsf u+\mathsf v)\le K_1\mathfrak d,
\quad K_1=K_0/\min(\gamma,b_f)>0.
\tag{SC.31}
$$

In particular every measure with cost at most $C_{\rm sat}-h$ satisfies

$$
h\le D_{\rm sat}\sqrt{\mathfrak d/L_f}+K_1\mathfrak d.
\tag{SC.32}
$$

This is a full-measure lower deficit bound, not a stationary-family
condition. Explicitly, putting $a_0=D_{\rm sat}/\sqrt{L_f}$, it implies

$$
\mathfrak d\ge
\left[\frac{2h}{a_0+\sqrt{a_0^2+4K_1h}}\right]^2
=K_{\rm sat}h^2+O(h^3).
\tag{SC.33}
$$

The inequality follows by solving the increasing quadratic in
$\sqrt{\mathfrak d}\ge0$. Its Taylor remainder has a fixed source
constant. Apply it to a maximizing measure and combine with (SC.25).
Both sides now give the uniform two-sided remainder (SC.22). Finally
$[\Phi(C_{\rm sat})-\Phi(C_{\rm sat}-h)]/h
=K_{\rm sat}h+O(h^2)\to0$. $\square$

## 5. Strict chord loss and uniform optimizing contacts

**Theorem 5.1 (P4: chord and aggregate contact asymptotics).** For every
$C_{\rm end}<\lambda<C_{\rm sat}$,

$$
\Phi(\lambda)>\gamma\frac{\lambda-C_{\rm end}}{C_{\rm sat}-C_{\rm end}}.
\tag{SC.34}
$$

For every optimizing failure measure at $\lambda=C_{\rm sat}-h$,
the aggregates (SC.28) satisfy, uniformly over all such measures,

$$
\mathsf m=h/D_{\rm sat}+O(h^2),\qquad
\mathsf u=h^2/D_{\rm sat}^2+O(h^3),\quad
\mathsf v=h^2/D_{\rm sat}^2+O(h^3).
\tag{SC.35}
$$

Writing $t_h=h/D_{\rm sat}$, their directional remainders obey

$$
\int_{\Omega_+}(\eta-t_h\xi)^2dm=O(h^3),\qquad
\int_{\Omega_-}(\xi+t_h\eta)^2dm=O(h^3).
\tag{SC.36}
$$

These are weighted aggregate and mean-square assertions, not exact
contacts, projective optimality, uniqueness or a support classification.

Proof. Subtract the endpoint chord from the concave continuous
$\Phi$. The difference is nonnegative and zero at both endpoints.
If it vanished at an interior point, express that point as a strict
convex combination of any earlier point and the right endpoint.
Concavity forces the difference at that earlier point to be zero.
Using the left endpoint proves the same for every later point. Thus
$\Phi$ would be affine, with positive slope
$\gamma/(C_{\rm sat}-C_{\rm end})$. Theorem 4.2's zero left derivative
excludes this, proving (SC.34).

Every optimizer has active cost by Theorem 3.3. Equations (SC.22) and
(SC.31) therefore give $h=D_{\rm sat}\mathsf m+O(h^2)$.
Also (SC.30) gives the nonnegative identity

$$
0\le\gamma(\mathsf u-\mathsf m^2)+b_f(\mathsf v-\mathsf m^2)
=\mathfrak d(h)-L_f\mathsf m^2=O(h^3).
\tag{SC.37}
$$

Each nonnegative summand is $O(h^3)$, proving (SC.35). All constants
come from the fixed trial and global remainder bounds, so are independent
of the chosen optimizer. Expanding the two squares in (SC.36) gives,
respectively,
$\mathsf v-2t_h\mathsf m+t_h^2(1-\mathsf u)$ and
$\mathsf u-2t_h\mathsf m+t_h^2(1-\mathsf v)$, both $O(h^3)$.
This also proves optimizer-uniformity of (SC.36). $\square$

## 6. Transfer to the original class and common realization

**Proposition 6.1 (explicit correspondence with JS).** For every fixed
finite $\lambda>C_{\rm end}$ and every prescribed sequence
$q_n>0$, $q_n\to0$, $t_n=e^{A_n}-1$, $q_nt_n\to\lambda$, define

$$
\mathcal R(\lambda)=\lim_n\mathcal T_{A_n}(s_0(1-q_n)).
\tag{SC.38}
$$

Under Convention 1.1 this limit exists, the classes are eventually
nonempty, and JS Theorem 7.1 gives $\mathcal R(\lambda)=B_0+\Phi(\lambda)$.
Consequently the new original-objective conclusions include

$$
\mathcal R(C_{\rm sat}-h)=T_0-K_{\rm sat}h^2+O(h^3),\qquad
\mathcal R(\lambda)>B_0+
\gamma\frac{\lambda-C_{\rm end}}{C_{\rm sat}-C_{\rm end}}
\quad(C_{\rm end}<\lambda<C_{\rm sat}).
\tag{SC.39}
$$

The support obstruction concerns limiting optimizing failure measures.
The expansion is iterated: first the original $q_n$ limit at a fixed
finite $\lambda$, then $h=C_{\rm sat}-\lambda\downarrow0$.

Proof. Here is the theorem and parameter correspondence, including why
it covers the original class. In JS Lemma 2.1 the variables
$(q,t,\mathcal F,c_*,\nu,k,\Phi)$ are exactly those of (SC.4)--(SC.7),
with $q=1-s/s_0$ and $t=e^A-1$. JR Theorem 42.1 fixes supported live
map $\Lambda_*=D(\cdot)D^\dagger+T(\cdot)T^\dagger+S(\cdot)S^\dagger$,
failure effect $M$, zero other effect, zero high failure and weak low
coefficient Gram $\operatorname{diag}(\delta,1,1)$. These are conditional
all-complex equality consequences, not a static support restriction.

For any admitted TP survivor controls trace balance gives
$p'(u)\ge-\|R(u)\|p(u)$, hence whole-fibre live effect at least
$e^{-A}I$. FA Theorem 69.1 applies to each actual low label: a nonzero
null live product has rank two, so its encoder has an onto Kraus matrix
and its live decoder an injective one. The kernels of $xD+zT+wS$ and
its adjoint are

$$
\mathbb C(1,-bz/(h_1x),-dw/(h_2x))^T,\qquad
\mathbb C(1,-az/(h_1x),-cw/(h_2x))^T.
\tag{SC.40}
$$

A common image or kernel fixes both ratios. Fixing the injective decoder
matrix makes all encoder matrices proportional; fixing the onto encoder
makes all live-decoder matrices proportional. Zero products with those
fixed matrices force zero factors. Thus the double rigidity concerns the
existing actual label and exposes no Kraus index. Its matrices are
$\sqrt\pi K(z,w)$ and attached failure $\pi vnn^T$. Failure kills both
coordinate zero and the live kernel. FA Theorem 69.2's Schur complement

$$
K^\dagger K-
\frac{K^\dagger Ke_0e_0^TK^\dagger K}{(K^\dagger K)_{00}}
=c_*(z^2)nn^T
\tag{SC.41}
$$

pulls the survival bound back to $0\le v\le tc_*(z^2)$, including axes.
Full decoder TP makes its acquisition effect
$\pi(K^\dagger K+vnn^T)$. On the actual labels let $P$ have masses
$\pi$ and $d\nu=v\,dP$. Their exact identities are

$$
\int hh^TdP=I_3,\quad \int nn^Td\nu=M,\quad
\int H(z^2)dP=1-\int|z|dP\le q,\quad C_\nu\le tq.
\tag{SC.42}
$$

Their full actual-label TV is exactly
$\tfrac12[H_{\rm live}+\int|f+vk|dP]$. As $q\to0$, the $P$ laws
concentrate at the four corners, with weights $1/4$ fixed by their zero
first and mixed moments. The fixed-mass failure measures on the compact
ellipse have subsequential limits preserving covariance and cost
$\le\lambda$. Since $\int k\,d\nu=-d_f$, the triangle inequality gives
JS Theorem 4.3's bound $\limsup T_{\rm instr}\le B_0+\Phi(\lambda)$.
This uses no special time law and includes all admitted noncommuting
controls. Compactness is used for $\nu$, not for $tP$ or unbounded
label multipliers.

For the matching direction use JS Theorems 5.1, 6.1 and 7.1 with an
optimizing $\nu_*$ and the covariance measure $\nu_0$ of masses
$\mu/2$ at $(\sqrt r,\pm\sqrt{W/\mu})$, of cost $C_{\rm end}$.
For strict-interior $\lambda$, Theorem 3.3 permits $\nu_*$ on at most
four lines. Choose one ellipse point per line. With
$c_{\min}=\min c_*>0$, set

$$
B=\frac{\mu(1+U+1/\beta)}{c_{\min}},\quad K_B=B^2/4,\quad
\epsilon_n=\frac{2(|q_nt_n-\lambda|+K_B/t_n)}{\lambda-C_{\rm end}},\quad
\nu_n=(1-\epsilon_n)\nu_*+\epsilon_n\nu_0.
\tag{SC.43}
$$

For large $n$ these measures have exact covariance and a strict finite
cost margin. JS.23--JS.27 generates rare capacity-saturated labels with
weights $a_i/(t_nc_i)$ and attached effects $a_in_in_i^T$, where
$c_i=c_*(z_i^2)$, and repairs their six live moments by four pure-live
labels. In particular, if
$\mathsf U=\sum_i(a_i/c_i)h_ih_i^T=(b_{ij})$, with
$b_0=b_{00}$ and $b_{11}$ its second diagonal entry, that exact repair
has normalized deficit

$$
e_t=\frac{C_{\nu_n}}t+
\frac{(b_0-b_{11})^2}
{4t^2[1-(b_0+b_{11})/(2t)+\sqrt{(1-b_0/t)(1-b_{11}/t)}]}.
\tag{SC.44}
$$

The trace of $\mathsf U$ is at most $B$. JS's uniform positivity and
moment identities hold for $t_n\ge16B$, and
$t_ne_{t_n}\le C_{\nu_n}+K_B/t_n\le q_nt_n$ by (SC.43).
Thus the same finite instrument satisfies the original contrast
inequality at every sufficiently large $n$; cost equality of a limiting
measure is never substituted for a finite margin. Its actual-label
absolute differences converge to $S_{\rm corner}+\int|k|d\nu_*$,
plus the high contribution. This proves common recovery of
$B_0+\Phi(\lambda)$, not a gluing of separately optimal marginals.

The whole-fibre constructor is precisely JS Theorem 6.1 (FA70/75).
It uses row-space encoding for each rank-two $K$, effect $K^\dagger K+N$,
positive terminal survival and a whole-fibre TP first-event decoder
with activity $\log(1+v/c_*)$. Add the fair high pair
$\sqrt{(1-\delta)/2}\,DE^\dagger$, and the fair coherent counted
complement $W_\perp^\dagger/\sqrt2$ with isometric decoder $EJ_0$.
Their total encoder effect is $I_5$. This freely chosen complement
preserves the complementary qubit and is distinct from the fixed
certain-failure completion. For every complex $A\in M_5$, with
$A_V=E^\dagger AE$, its forgotten maps are exactly

$$
\begin{aligned}
\Phi^L(A)&=E[DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger
+J_0W_\perp^\dagger AW_\perp J_0^\dagger]E^\dagger,\\
\Phi_\ell^f(\mathcal B)(A)&=
 w_\ell\left(\int_{\mathcal B}\frac{2\,du}{(1+u)^2}\right)
 \operatorname{tr}(EME^\dagger A)P_f,
\qquad \ell\in\{0,1,2,3,13\}.
\end{aligned}
\tag{SC.45}
$$

These equalities follow from the exact live Gram and attached failure
sum, on all complex matrix units and every Borel $\mathcal B$.
Cross-support terms vanish; complementary coherences remain. Labels
$0,13$ are separately zero and no extra or singular sector is added.
For every passive reference the live conjugating matrices tensor with
$I_R$, and the failure map is exactly

$$
w_\ell\left(\int_{\mathcal B}g(u)du\right)P_f\otimes
\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X].
\tag{SC.46}
$$

All twelve original outputs therefore preserve their HALF full-cq
errors: conditionally $e_5=e_{27}=E_*$ and
$e_{16}<71/484<37/250<E_*$. Only the high pair has dimension at
least three; its acquired mass on each history is $(1-\delta)A_y$,
where $A_y=\sum_i h_i^2p_{yi}$, maximized at $27$ and equal to JR's
sharp $\mathsf C(s)$ on the weak plateau. Low probabilities include
all $N$ mass, even when it later fails. All matrices and labels are
fixed before the sole specimen arrives. The chosen chronological
recovery has actual mathematical first events, no deadline atom and
no action after absorption. Necessity allowed every FA67.2 path.
This verifies the hypotheses and common realization needed to apply
JS Theorem 7.1; (SC.22) and (SC.34) now give (SC.39). $\square$

## 7. Attribution and the remaining original target

**Convention 7.1 (new implications and credited mathematics).** The new
source-specific implications are P1's global strict convexity, P2's
evaluated positive-objective two-line obstruction and four-line
optimizing representation, P3's explicit sharp saturation coefficient
with full-measure remainder, and P4's strict chord inequality and
optimizer-uniform aggregate/mean-square asymptotics.

CG supplies the conditional source root, ranks, TP and minimax/support
premises. JR34--40 supplies the sharp worst-history acquired cost;
JR42--45 supplies supported equality and the real weak optimization;
JR50--57 supplies the static plateau, dual and endpoint results.
RC58--66 already supplies the complete static residual/contact curve
and its transition/gluing. FA68--75 supplies the full activity class's
prescribed-path minimum, actual-label double rigidity, capacity,
chronological construction, finite attainment and threshold/deficit
results. WE supplies the evaluated $C_{\rm end}$, tangent at $r$,
threshold strip, concentration and critical full-record limit. JS
supplies compact limiting necessity, exact finite repair and recovery,
$C_{\rm sat}$, spectral equality and qualitative transition. The
five-atom result and these constructions are reused, not counted as new.
CA/IR and the classical CP, spectral and convex mechanisms credited
inside those suppliers retain their stated scopes. No new external
or kernel authentication or worldwide priority claim is made.

**Definition 7.2 (unresolved scalar and native scope).** The values of
$\Phi$ throughout $(C_{\rm end},C_{\rm sat})$, exact contacts and
weights, possible interior transitions and a global contact-selection
certificate remain unresolved. The endpoint expansion does not settle
that target. The full finite-$(s,A)$ scalar frontier, exact additive
threshold correction, finite-budget contacts and optimal deficit
coefficients remain unresolved beyond supplied results. No simultaneous
finite-$q$, varying-$\lambda$ error theorem, $\lambda=\infty$ theorem,
strict concavity, projective optimality, exact contact classification,
minimum physical alphabet or whole-instrument uniqueness follows.
Saturation here is a limit; no finite-$A$ endpoint attainment is claimed.

Lawful native access to the unknown specimen, D/T/S calibration, actual
label generation, joint coherent storage, controlled whole-fibre TP
decoding, acquisition duration/placement on the same aligned clock,
native first absorption at $6+u$, terminal live output, and original
archive/source/epoch/controller/permission semantics remain
`ASSUMED-UNVERIFIED`. Geometric OriginalControl is not an actuator.
Admitted probability-changing noncommuting controls do not justify an
exhaustive Schur or diagonal menu. Spectral energy, acquired mass,
activity, record TV and original error remain distinct. No physical
dimension/SO3, ML-error, general NN, empirical ML, native permission,
Lean/kernel/frozen certification or programme-completion assertion is
made. The original full scalar interior and native targets remain open.

[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[RC]: FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md
[FA]: FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md

## 追加锚（本行以下为增补区）
