# Native complete continuation: activity growth and contrast transitions

## 1. Conditional experiment and the two parameters

**Convention 1.1 (source premises).** This volume concerns the same
complete-output experiment as [CG, §§13–17][CG], [JR, §§41–57][JR],
[FA, §§67–79, 87–92][FA] and [RC, §§58–73][RC]. The source is the
positive-pivot algebraic source specified by CG.112–.117 and CG.134.
Its root existence, isolation, Jacobian certificate, exact ranks,
root trace-preservation identity, minimax identification and the
sharp acquired-cost equality characterization are inherited premises,
`ASSUMED-UNVERIFIED`. All theorems below are ordinary conditional
mathematics under these premises. Inequalities on a surrounding
coefficient box do not assert trace preservation away from the root.
No Lean/kernel or physical implementation certification is asserted.

Let the five physical modes be indexed by $0,1,2,3,13$, and set

$$
E=((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2),\qquad P=EE^\dagger.
\tag{AC.1}
$$

The sole unknown normalized reached-cut specimen is one of
$E\rho_{y,e,n}E^\dagger$, where

$$
\begin{gathered}
y\in\{5,16,27\},\quad e,n\in\{\pm1\},\qquad
p_y=(y/128,(64-y)/128,1/2),\\
a_y=(\sqrt{p_{y0}},\sqrt{p_{y1}},\sqrt{p_{y2}})^T,\quad
U_{e,n}=\operatorname{diag}(e,n,1),\quad
\rho_{y,e,n}=U_{e,n}a_ya_y^TU_{e,n}^\dagger.
\end{gathered}
\tag{AC.2}
$$

For $d_y=(y/128,y(58-y)/(128(y+6)),y/(2(y+6)))$ and
$\xi_y=(\sqrt{d_{yi}})_i$, the ideal live block is
$EU_{e,n}\xi_y\xi_y^TU_{e,n}^\dagger E^\dagger$.
The five separately labelled ideal failure measures have labels
$\ell\in\{0,1,2,3,13\}$, weights

$$
(w_0,w_1,w_2,w_3,w_{13})=(0,1/4,1/2,1/4,0),\qquad
f_y(u)=\frac{6y}{(y+6u)^2},\quad 0\le u\le1,
\tag{AC.3}
$$

and densities $w_\ell f_y(u)P_f$. Here $P_f$ is the absorbing
failure state; elapsed time $u$ means absolute time $6+u$.
The error is HALF the complete stopped classical-quantum norm,
maximized over all twelve histories. It counts live coherences,
all five Borel measures, singular-time components, aborts, wrong
supports and zero-target sectors.

An actual acquisition is a common complex CP instrument
$\{\mathcal E_j\}$ on $M_5$ with total encoder effect $I_5$.
The retained label is actually generated. Its conditional decoder
is TP on its whole quantum fibre. That fibre jointly counts every
subsequently accessible input-bearing specimen, memory, controller,
environment and entanglement share. Inaccessible Kraus indices are
not actual labels. There is no prior, helper specimen, readable
history, copy, reset, retry, postselection, acceptance division or
uncounted quantum bypass. Arbitrary complex encoders and arbitrary
hidden Kraus multiplicity remain in the comparison class.

**Definition 1.2 (activity and original constraints).** On each whole
finite-dimensional decoder fibre let $R_j(u)\succeq0$ be a measurable
first-event rate with integrable operator norm. Between events,
Hamiltonian and unobserved TP survivor controls are allowed, and
trace loss occurs only through $R_j$. Terminal processing on survivors
is TP. A first failure is absorbing: no later positive-carrier action
and no forced terminal absorption is allowed. Put

$$
\mathsf A=\max_j\int_0^1\|R_j(u)\|\,du.
\tag{AC.4}
$$

The cost $\mathsf W$ is the maximum over the twelve histories of
the probability that the jointly acquired quantum dimension is at
least three. It is neither expected dimension nor expected activity.
Let $F$ be the plus effect of a binary report from that acquisition,
$\kappa=h_0a+h_1b_{\rm src}$, and
$\mathsf V(F)=2|\operatorname{Re}F_{01}|/\kappa$ on the supported
qutrit. The source amplitudes $h_0,a$ are defined in §2.
The class $\mathfrak F_{s,A}$ imposes exactly

$$
E(\Phi)=E_*,\qquad \mathsf V(F)\ge s,\qquad
\mathsf W=\mathsf C(s),\qquad \mathsf A\le A,
\tag{AC.5}
$$

with JR's original sharp cost $\mathsf C$. Its objective is actual
acquisition-record total variation between histories $(5,+,+)$ and
$(27,+,+)$, with the HALF convention. Denote its maximum by
$\mathcal T_A(s)$ when nonempty; $\mathcal T(s)$ denotes the
unbudgeted counterpart. No complete binary effect is prescribed.

The principal class has finitely many actual labels. Necessity also
covers the convergent countable and expressly measurable/integrable
finite-fibre extensions of CG Convention 21.3 and JR41: measurable
fibre dimensions and Kraus fields, integrable effects and Choi
matrices, full-output TP decoders almost everywhere. There one uses
supremum or essential supremum in AC.4. No general disintegration or
infinite-dimensional coding theorem is assumed. All attainments used
here have finite actual alphabets.

## 2. Supported directions and physical failure moments

**Definition 2.1 (source dictionary).** Let

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=a|0\rangle\langle1|+b_{\rm src}|1\rangle\langle0|,\\
S=c_{\rm src}|0\rangle\langle2|+d_{\rm src}|2\rangle\langle0|,
\qquad M=\operatorname{diag}(0,m_1,m_2),\\
\Lambda_*(X)=DXD^\dagger+TXT^\dagger+SXS^\dagger.
\end{gathered}
\tag{AC.6}
$$

All seven amplitudes and both $m_i$ are positive. Equivalently the
amplitudes are the positive factors of $H,Q^{01},Q^{02}$ in CG.134:
$h_i=\sqrt{H_{ii}}$, $a=\sqrt{Q^{01}_{00}}$,
$b_{\rm src}=\sqrt{Q^{01}_{11}}$,
$c_{\rm src}=\sqrt{Q^{02}_{00}}$,
$d_{\rm src}=\sqrt{Q^{02}_{11}}$; the stipulated source ranks and
positive off-diagonal factors identify these matrices at the root.
There $D^\dagger D+T^\dagger T+S^\dagger S+M=I_3$.
Set

$$
\begin{gathered}
\theta=\frac{ab_{\rm src}}{h_0h_1},\quad
\omega=\frac{c_{\rm src}d_{\rm src}}{h_0h_2},\quad
\delta=\theta+\omega\in(0,1),\quad s_0=\sqrt\delta,\\
\alpha=\theta/\delta,\quad \beta=\omega/\delta,\quad
Q=\operatorname{diag}(1,-\alpha,-\beta),\quad
\mathscr C=\{h=(1,z,w)^T:\alpha z^2+\beta w^2=1\},\\
L=\operatorname{diag}(s_0,1,1),\quad
\Delta=\rho_{27,+,+}-\rho_{5,+,+},\quad
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\quad
(K_0,K_1,K_2)=(D,T,S),\\
G=LNL=\begin{pmatrix}g_0&x_G&y_G\\x_G&g_1&z_G\\y_G&z_G&g_2\end{pmatrix},
\quad K_h=s_0D+zT+wS,\quad \ell(h)=h^TGh,\quad H_0=(1-\delta)N_{00}.
\end{gathered}
\tag{AC.7}
$$

Here $L$ normalizes coefficients; it is not a decoder survival effect.
The failure support is coordinates $(1,2)$ of the supported qutrit.
Its physical coordinates and height are

$$
\begin{gathered}
\widehat n_h=(d_{\rm src}w/h_2,-b_{\rm src}z/h_1)^T,\quad
n_h=(0,\widehat n_h)^T,\\
\Delta_f=\begin{pmatrix}-11/64&(\sqrt{37}-\sqrt{59})/16\\
(\sqrt{37}-\sqrt{59})/16&0\end{pmatrix},\quad
f(h)=\widehat n_h^T\Delta_f\widehat n_h,\\
M_2=\operatorname{diag}(m_1,m_2),\quad
\Xi=M_2^{1/2}\Delta_fM_2^{1/2}
=\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},\\
d_f=11m_1/64>0,\quad z_f<0,\quad
L_f=\sqrt{d_f^2+4z_f^2},\quad
\lambda_\pm=(-d_f\pm L_f)/2.
\end{gathered}
\tag{AC.8}
$$

Whitening a physical effect $B$ means
$M_2^{-1/2}BM_2^{-1/2}$. A unit whitened vector $e$ corresponds to
physical effect $M_2^{1/2}ee^TM_2^{1/2}$, not $ee^T$.
The capacity is

$$
c(h)=\frac{h_1^2h_2^2\delta+a^2h_2^2z^2+
 c_{\rm src}^2h_1^2w^2}
 {h_0^2\delta+b_{\rm src}^2z^2+d_{\rm src}^2w^2}>0.
\tag{AC.9}
$$

**Convention 2.2 (the supported-nonzero domain).** Partition actual
low labels into $\mathcal J_+$, those whose restriction
$X\mapsto\mathcal E_j(EXE^\dagger)$ is nonzero, and
$\mathcal J_0$, those with zero such restriction. Only labels in
$\mathcal J_+$ receive positive coefficient weights and ellipse
coordinates. FA69's arbitrary-complex, arbitrary-Kraus equality
rigidity gives for them one effective supported live product and
pulled-back failure effect

$$
K_j=\sqrt{p_j}K_{h_j},\qquad
N_j=p_jb_jn_{h_j}n_{h_j}^T,\qquad p_j>0,
\quad 0\le b_j\le t c(h_j),\quad t=e^A-1.
\tag{AC.10}
$$

This is a consequence of the original equality class, not a real or
single-Kraus restriction on competitors. The full whole-fibre rate
bound gives the capacity for every admitted time law. In particular
finite activity excludes any nonzero supported failure-only label.

Nonzero full-$M_5$ labels in $\mathcal J_0$ remain allowed and
actually counted. For example, take isometries
$W_\perp:\mathbb C^2\to P^\perp$ and
$J_0:\mathbb C^2\to\mathbb C^3$. The encoder
$\operatorname{Ad}_{W_\perp^\dagger}$ followed by the rate-zero
live decoder $\operatorname{Ad}_{EJ_0}$ is nonzero on $M_5$ and
zero on all twelve specimens. It has no positive-$p$ representation
in AC.10. It contributes no supported contrast or record TV, but
adds an actual label if retained separately, and its whole fibre
still obeys AC.4. No deletion of it from the competitor class is made.

**Proposition 2.3 (reused exact weak correspondence).** For
$0\le s<s_0$, put $\tau=s/s_0$. Every original competitor gives
on $\mathcal J_+$ the full moments

$$
\begin{gathered}
\sum_jp_jh_jh_j^T=I_3,\qquad
\sum_jp_jb_j\widehat n_j\widehat n_j^T=M_2,\\
k:=\sum_jp_j|z_j|\ge\tau,\qquad
v:=\sum_jp_j|\ell(h_j)+b_jf(h_j)|,
\qquad 2T_{\rm actual}=H_0+v.
\end{gathered}
\tag{AC.11}
$$

Its actual requested contrast obeys
$s\le\mathsf V(F)\le s_0k$. Conversely every finite family
satisfying AC.9–.11 has one simultaneous original realization with
report signs $\operatorname{sgn}z_j$ and contrast $s_0k$.
The maximum is attained. These are FA69–72 and FA77's correspondence;
§13 displays the common realization, including the complement.
The $p_j$ are coefficient masses, not source priors or acquisition
probabilities. The acquisition mass on a supported input $\rho$ is
$\operatorname{tr}((K_j^\dagger K_j+N_j)\rho)$.

Put

$$
V=\frac{m_2h_1^2}{b_{\rm src}^2},\quad
W=\frac{m_1h_2^2}{d_{\rm src}^2},\quad
\mu=\alpha V+\beta W,\quad d\sigma=b\,dp.
\tag{AC.12}
$$

The physical failure equation is equivalent to

$$
\int z^2d\sigma=V,\quad \int w^2d\sigma=W,\quad
\int zw\,d\sigma=0,\quad \sigma(\mathscr C)=\mu.
\tag{AC.13}
$$

This auxiliary measure expresses necessary moments. It does not
replace the original objective's absolute value on each actual label.

## 3. Closed weak feasibility and inherited boundary information

**Convention 3.1 (feasible domain).** Write
$c_*(u)=c(1,\sqrt u,\sqrt{(1-\alpha u)/\beta})$ on
$[0,1/\alpha]$. It is a positive increasing linear-fractional function
under the source inequalities of FA78. Set

$$
\begin{gathered}
u_f=V/\mu,\quad v_f=W/\mu,\quad c_f=c_*(u_f),\quad
\nu=\mu/c_f,\quad t_0=W/c_f,\quad q=\nu/t,\\
\tau_{\max}(t)=q\sqrt{u_f}+\sqrt{(1-q)(1-qu_f)},\qquad
\tau_*=\tau_{\max}(t_0).
\end{gathered}
\tag{AC.14}
$$

Here $0<u_f<1<v_f$, $\alpha u_f+\beta v_f=1$.
FA78 evaluates the entire weak feasibility threshold: it is exactly
$t\ge t_0$, $0\le\tau\le\tau_{\max}(t)<1$. Equivalently
$t_{\min}(\tau)=t_0$ for $\tau\le\tau_*$, and for
$\tau>\tau_*$ it is the unique $t>t_0$ solving
$\tau=\tau_{\max}(t)$. Put
$A_{\min}(s)=\log(1+t_{\min}(s/s_0))$.
FA79 supplies attainment, height and capacity equality on this minimum
boundary, including the collapsed residual direction at $t=t_0$.
Those are boundary results, not boundary dual-attainment assertions.

At $A=0$, AC.10 cannot supply $M_2\succ0$, so the class is empty.
The weak interval is separate from FA71's isolated strong point:
for $s\in[s_0,1]$ finite feasibility occurs only at
$s=s^\dagger\in(s_0,1)$ and $A\ge A_\dagger$, with the exact
$s^\dagger,A_\dagger$ of FA71. In particular $s=s_0$ and $s=1$
are infeasible at finite activity. No theorem about the weak interval
below is asserted on the isolated strong component.

**Lemma 3.2 (strictly increasing contrast capacity).** The function
$\tau_{\max}(t)$ increases strictly for $t\ge t_0$.

Proof. Differentiate its expression in $q=\nu/t$. The negative term
in the derivative dominates $\sqrt{u_f}$ because

$$
(1+u_f-2qu_f)^2-4u_f(1-q)(1-qu_f)=(1-u_f)^2>0,
\tag{AC.15}
$$

and $1+u_f-2qu_f>0$. The derivative with respect to $q$ is strictly
negative; $q$ strictly decreases with $t$. The endpoint follows by
continuity. $\square$

## 4. The common certificate and the static strict gap

**Proposition 4.1 (reused attained common dual).** At
$t>t_0$ and $\tau<\tau_{\max}(t)$ there exist optimal finite
$Y\in\operatorname{Sym}_3$, $Z\in\operatorname{Sym}_2$ and
$\lambda\ge0$ such that, on the entire ellipse,

$$
\begin{aligned}
h^TYh&\ge|\ell(h)|+\lambda|z|,\\
h^TYh+tc(h)\widehat n_h^TZ\widehat n_h
 &\ge|\ell(h)+tc(h)f(h)|+\lambda|z|,
\end{aligned}
\tag{AC.16}
$$

and the optimal low height is
$\operatorname{tr}Y+\operatorname{tr}(ZM_2)-\lambda\tau$.
Every original optimizer satisfies pointwise contact almost everywhere
and $\lambda(k-\tau)=0$.

This is the continuous common-dual theorem of RC68, with its original
conditional scope. Its relevant hypothesis is relative interior of
the full two-sheet moment projection, not just primal feasibility.
For precision, a uniform angular probability $\rho_\circ$ and a
balanced four-sign measure $\rho_u$ give the full-support failure
measure

$$
\sigma_\varepsilon
=\mu[(1-\varepsilon)\rho_{u_\varepsilon}
 +\varepsilon\rho_\circ],\qquad
u_\varepsilon=\frac{u_f-\varepsilon/(2\alpha)}{1-\varepsilon}.
\tag{AC.17}
$$

It preserves AC.13. Its saturated live measure is
$\sigma_\varepsilon/(tc)$; the residual Gram is positive definite
for sufficiently small $\varepsilon$, since at zero it equals
$\operatorname{diag}(1-q,1-qu_f,1-qv_f)$. A small positive angular
component can also be inserted into a pure completion of this Gram.
The resulting two full-support sheets retain strict contrast slack,
because their contrast tends to $\tau_{\max}(t)>\tau$.
Any supporting functional of their moment projection must have zero
contrast coefficient and vanish identically on both sheets. The pure
identity is a multiple of $h^TQh=0$; the remaining failure quadratic
then vanishes identically, so its physical matrix is zero. After
quotienting the identity the target is relatively interior.
Compactness and fixed total live mass make the height boundary closed;
a separating functional at its optimum therefore has a positive height
coefficient and can be normalized. Its two sheet inequalities are
AC.16. This records the actual continuous-cone argument underlying the
supplier, without assuming a polynomial relaxation selects a contact.

For each competitor's own $b\in[0,tc(h)]$, convex interpolation of
$|\ell+bf|$ between its two endpoints gives

$$
h^TYh+b\widehat n_h^TZ\widehat n_h
 \ge|\ell(h)+bf(h)|+\lambda|z|.
\tag{AC.18}
$$

Integration gives the stated upper bound; equality gives the contact
and complementarity assertions. Supported-zero labels have zero
supported difference and do not invalidate this bound.

**Proposition 4.2 (reused strict static gap).** At every nonempty weak
finite-budget point,

$$
\mathcal T_A(s)<\mathcal T(s),\qquad
2\mathcal T(s)-H_0=j(\tau)+L_f,
\tag{AC.19}
$$

where $j$ is RC's static optimal live height under the same Gram and
contrast inequality. The reason is the all-class equality condition
in TA6–7: static height equality requires a nonzero supported
negative-spectral failure-only actual outcome. That negative spectral
row cannot attach to any optimal weak live row or to a supported high
row. Finite whole-fibre activity gives
$L_{{\rm dec},j}\succeq e^{-A}I$ by FA68, excluding that outcome.
FA72's attained maximum then makes the gap strict. Neither a limiting
certain-failure decoder nor a supported-zero complement removes this
obstruction. This uses the full static equality theorem, not an upper
bound for one proposed allocation.

## 5. A source-specific covariance obstruction

**Lemma 5.1 (nonpositive live height occupies a strict slope sector).**
Under the conditional source inequalities,

$$
\ell(1,z,w)\le0\ \Longrightarrow\ z\ne0,
\qquad -1/4<w/z<16.
\tag{AC.20}
$$

Proof. The following rational relaxations of the source enclosure
suffice, with $\gamma_G=-z_G>0$:

$$
\begin{gathered}
1269<10^6g_0<1270,\quad2922<10^6g_1<2923,\quad
1677<10^6g_2<1678,\\
2370<10^6x_G<2371,\quad2208<10^6y_G<2209,\quad
101<10^6\gamma_G<102,\quad 1/9<\beta<1/8.
\end{gathered}
\tag{AC.21}
$$

Put $a_\circ=\sqrt\alpha$, $b_\circ=\sqrt\beta$,
$A_0=g_1+\alpha g_0$, $A_2=g_2+\beta g_0$.
In particular $93/100<a_\circ<19/20$ and
$1/3<b_\circ<177/500$. Direct endpoint comparisons yield

$$
\begin{gathered}
A_2-2y_Gb_\circ>1/4000,\qquad
A_0-2x_Ga_\circ>-3/4000,\\
2\gamma_G+2y_Ga_\circ>1/250,\qquad
A_2-x_G\beta/a_\circ>0,\\
A_0+2x_Ga_\circ>1/125,\qquad
2\gamma_G+2x_Gb_\circ-2y_Ga_\circ>-1/400,\\
2\gamma_G+2x_Gb_\circ<1/500,\qquad
A_0-y_G\alpha/b_\circ>-13/5000,\qquad
x_G\alpha/b_\circ<3/400.
\end{gathered}
\tag{AC.22}
$$

These comparisons use the displayed broad box, with
$\alpha=1-\beta$; no root or off-root normalization is used.
For $z=0$, both orientations have height at least
$(A_2-2y_Gb_\circ)/\beta>0$.
For $z\ne0$ let $r=w/z$. The lower of the two oriented heights has
positive denominator $\alpha+\beta r^2$ and numerator

$$
F(r)=A_0-2\gamma_Gr+A_2r^2
 -2|x_G+y_Gr|\sqrt{\alpha+\beta r^2}.
\tag{AC.23}
$$

If $r=-u$, $1/4\le u\le x_G/y_G$, use
$\sqrt{\alpha+\beta u^2}\le a_\circ+\beta u^2/(2a_\circ)$.
Then

$$
\begin{aligned}
F(-u)\ge{}&A_0-2x_Ga_\circ+(2\gamma_G+2y_Ga_\circ)u\\
&+(A_2-x_G\beta/a_\circ)u^2+(y_G\beta/a_\circ)u^3\\
>{}&-3/4000+u/250\ge1/4000.
\end{aligned}
\tag{AC.24}
$$

If $u\ge x_G/y_G$, use
$\sqrt{\alpha+\beta u^2}\le a_\circ+b_\circ u$ instead. It gives

$$
F(-u)>(u^2/4000)-(u/400)+1/125
 =((u-5)^2+7)/4000>0.
\tag{AC.25}
$$

The shared sign boundary is covered by both estimates. For $r\ge16$,
$\sqrt{\alpha+\beta r^2}\le b_\circ r+\alpha/(2b_\circ r)$ gives

$$
F(r)>r^2/4000-r/500-13/5000-3/(400r)
 \ge4/125-13/5000-3/6400>0.
\tag{AC.26}
$$

The quadratic and negative reciprocal terms increase in this range.
This proves AC.20 for both orientations, zero height, the finite
endpoints and the infinite-slope axis. $\square$

**Theorem 5.2 (unavoidable positive-live failure mass).** Define

$$
R(z,w)=4z^2+(63/4)zw-w^2=(w+z/4)(16z-w),
\tag{AC.27}
$$

and

$$
B_R=\frac{\beta^{-1}-4\alpha^{-1}+
\sqrt{(4\alpha^{-1}+\beta^{-1})^2+(63/4)^2/(\alpha\beta)}}2.
\tag{AC.28}
$$

Every original feasible weak family satisfies

$$
\sigma\{\ell>0\}\ge\frac{W-4V}{B_R}>0,\qquad
p\{\ell>0,b>0\}\ge\frac{W-4V}{B_Rtc_z}>0,
\quad c_z=c_*(1/\alpha).
\tag{AC.29}
$$

Proof. The source bound $u_f<1807/2500$ implies
$u_f(1+3\beta)<19877/20000<1$. Since
$\mu=\alpha V+\beta W$, this is $W>4V$.
Lemma 5.1 gives $R>0$ on $\{\ell\le0\}$, whereas AC.13 gives
$\int R\,d\sigma=4V-W<0$. In the coordinates
$(\sqrt\alpha z,\sqrt\beta w)$, the matrix of $R$ has diagonal
$4/\alpha,-1/\beta$ and off-diagonal
$63/(8\sqrt{\alpha\beta})$. Its least eigenvalue is $-B_R$, so
$R\ge-B_R$ on the entire ellipse. Splitting the measure at
$\ell=0$ proves the first inequality. Since $b\le tc(h)\le tc_z$,
it also proves the second. In particular the full failure covariance
cannot be supported on nonpositive live-height directions. These are
coefficient/effect-mass bounds, not acquisition probabilities. $\square$

**Lemma 5.3 (failure loss exceeds all available live height).** Put

$$
J_{\rm b}=\operatorname{tr}G+2(x_G+y_G+|z_G|).
\tag{AC.30}
$$

Every full live Gram satisfies $\int|\ell|dp\le J_{\rm b}$, and
at the conditional source $d_f>J_{\rm b}$.

Proof. The diagonal moments are all one. Termwise triangle inequality
and Cauchy–Schwarz give $\int|z|dp,\int|w|dp,\int|zw|dp\le1$,
proving the height bound. AC.21 gives
$J_{\rm b}<15235/10^6<1/50$. At the root, trace preservation and
$\operatorname{tr}\Delta=0$ give
$d_f=N_{00}+g_1+g_2$, while $g_0=\delta N_{00}$.
The inherited source enclosure $s_0<13/100$ therefore yields
$d_f>1269/16900>7/100>J_{\rm b}$. The TP identity in this step is
used only at the source root. $\square$

## 6. Strict saturated slack in every optimum

**Theorem 6.1 (all-optimizer, all-dual strict slack).** Fix
$t>t_0$, $0\le\tau<\tau_{\max}(t)$, an arbitrary original global
optimizer, and any attained optimal common dual $(Y,Z,\lambda)$.
For every measurable maximizing-sign choice
$\epsilon(\ell+bf)=|\ell+bf|$, $\epsilon\in\{\pm1\}$, define

$$
a(h,b)=h^TYh-\epsilon\ell(h)-\lambda|z|\ge0,
\qquad \mathscr D=\int a\,dp.
\tag{AC.31}
$$

Then $\mathscr D>0$. Almost everywhere on $\{a>0\}$,

$$
b=tc(h),\qquad
\widehat n_h^T(Z-\epsilon\Delta_f)\widehat n_h
 =-a/(tc(h))<0.
\tag{AC.32}
$$

Thus a positive coefficient-measure set of supported-nonzero low labels
is saturated and has strict pure-sheet slack of that same height sign.
For a finite alphabet this includes a positive-weight actual label;
no positive singleton is asserted for a nonatomic record.

Proof. Integrating AC.18 and using primal-dual equality makes its
nonnegative gap vanish almost everywhere and gives
$\lambda(k-\tau)=0$. With
$q_\epsilon=\widehat n^T(Z-\epsilon\Delta_f)\widehat n$ this says

$$
a+bq_\epsilon=0,
\quad a\ge0,\quad a+tc(h)q_\epsilon\ge0.
\tag{AC.33}
$$

For $b=0$, $a=0$. For $0<b<tc(h)$ the zero gap is a strict convex
combination of the two nonnegative signed endpoint gaps, so both
vanish and $a=0$. Hence $a>0$ forces AC.32.

Suppose $\mathscr D=0$. Then $a=0$ almost everywhere. On $b>0$,
$q_\epsilon=0$, so the pure and saturated sheets have a common
contact of the same height sign, and
$\epsilon\ell=|\ell|$. Their signed smooth inequalities imply

$$
(Z-\epsilon\Delta_f)\widehat n_h=0.
\tag{AC.34}
$$

Here is the differential justification including cusps. Parameterize
$z=\cos\phi/\sqrt\alpha$, $w=\sin\phi/\sqrt\beta$ and choose
either maximizing report sign $r$ with $rz=|z|$. Both smooth
functions with $\lambda rz$ in place of $\lambda|z|$ are globally
nonnegative and vanish at the common contact. Their derivatives vanish.
Subtracting gives $q_\epsilon'=0$ because $q_\epsilon=0$ already.
The vectors $\widehat n,\widehat n'$ are independent everywhere:
with $A=d_{\rm src}/(h_2\sqrt\beta)$ and
$B=b_{\rm src}/(h_1\sqrt\alpha)$ their determinant is $AB>0$.
The two scalar equalities force AC.34. This uses no division by $z$
and no derivative of an absolute-value cusp. At $z=0$ both report
signs are available; if $\lambda>0$ their derivative conditions
would themselves exclude pure contact. Zero heights allow either
maximizing $\epsilon$ throughout this argument.

Group the physical failure effects by that chosen sign:

$$
M_\epsilon=\int_{b>0,\,\text{sign}=\epsilon}
 b\widehat n\widehat n^Tdp,\qquad M_++M_-=M_2.
\tag{AC.35}
$$

If $M_-=0$, all failure-carrying actual height differences are
nonnegative. Summing them gives
$0\le\int_{b>0}\ell\,dp-d_f$, contradicting Lemma 5.3.
If $M_+=0$, their pure contacts all have $\ell\le0$ and yet
carry AC.13, contradicting Theorem 5.2. Thus both groups are nonzero.

If either has rank two, AC.34 forces $Z=\epsilon\Delta_f$.
The opposite kernel matrix is then $2\epsilon\Delta_f$, invertible
since $\det\Delta_f=-\Delta_{12}^2<0$, and cannot carry the other
nonzero group. Both groups must therefore have rank one.

Whiten them physically:
$P_\epsilon=M_2^{-1/2}M_\epsilon M_2^{-1/2}$.
Two positive rank-one matrices summing to $I_2$ are complementary
orthogonal projections $e_\epsilon e_\epsilon^T$.
For $\widetilde Z=M_2^{1/2}ZM_2^{1/2}$, AC.34 becomes

$$
\widetilde Ze_+=\Xi e_+,\qquad
\widetilde Ze_-=-\Xi e_-.
\tag{AC.36}
$$

Symmetry of $\widetilde Z$ gives $e_+^T\Xi e_-=0$.
Thus these are the two spectral directions of $\Xi$, leaving exactly
$\widetilde Z=|\Xi|$ or $\widetilde Z=-|\Xi|$.
In the reverse assignment the plus group has total failure height
$\lambda_-$. Its nonnegative actual height forces its integrated live
height to be at least $-\lambda_->d_f>J_{\rm b}$, impossible.

In the forward assignment each failure and pure height has its chosen
sign. Hence

$$
\int|\ell+bf|dp=\int|\ell|dp+L_f.
\tag{AC.37}
$$

Pure contact and contrast complementarity give
$\int|\ell|dp=\operatorname{tr}Y-\lambda\tau$.
The pure certificate upper-bounds every static live decomposition,
while this very live Gram is statically feasible. The equality is
therefore $j(\tau)$, not merely the value of a selected allocation.
AC.37 would attain the static value in AC.19, contradicting its strict
finite-activity gap. All rank/sign cases are exhausted, and
$\mathscr D>0$ follows. $\square$

The theorem does not require every failure label to saturate. A label
in AC.32 may still contact the pure sheet at the opposite height sign;
that possibility is not excluded. No maximum-contrast completion or
fixed residual Gram rank entered the proof.

## 7. Full budget use, strict growth and regular sensitivity

**Theorem 7.1 (every optimum uses the activity budget).** At every
nonempty weak finite-budget point each original height optimizer has
$\mathsf A=A$.

Proof. In the strict interior, Theorem 6.1 gives a positive-measure
set with $b=tc$. FA69's whole-fibre necessity for any admitted time
law requires activity at least
$\log(1+b/c)=\log(1+t)=A$ on those labels. Feasibility gives the
opposite bound. At the minimum-budget boundary, FA79's capacity
equality classification supplies saturated failure-carrying mass,
including the floor and its collapsed residual case. It yields the
same conclusion without extending Proposition 4.1 to that boundary.
The statement concerns the maximum, supremum or essential supremum
of actual whole-fibre activity, as appropriate. $\square$

**Theorem 7.2 (strict finite-budget growth).** For fixed $0\le s<s_0$,

$$
A_{\min}(s)\le A_1<A_2<\infty
\quad\Longrightarrow\quad
\mathcal T_{A_1}(s)<\mathcal T_{A_2}(s).
\tag{AC.38}
$$

Proof. Take an attained $A_1$ optimizer and retain its actual encoders,
decoders and time laws at budget $A_2$. Every supported-nonzero low
label obeys $b\le t_1c<t_2c$, where $t_i=e^{A_i}-1$.
The $A_2$ point is strict interior: $t_2>t_0$ and
$\tau<\tau_{\max}(t_2)$ by §3 and Lemma 3.2, also when
$A_1=A_{\min}(s)$. Equality of optimal heights would make the same
instrument $A_2$-optimal without any saturated supported label,
contradicting Theorem 6.1. $\square$

**Proposition 7.3 (slope on a given regular matched branch).** Suppose
at fixed $s$ a finite optimal pure/saturated family and an attained
matching whole-circle certificate are differentiable in $t$ on an
open parameter interval. Require positive used weights, fixed sheet
indices, fixed report and maximizing-height signs in legal local
charts, and the exact differentiated moment/contact equations.
Use a fixed active-contrast branch $k=\tau$, or a fixed
$\lambda=0$ branch. At a zero-height or report-sign change the signed
differentiation must be justified separately. Then

$$
\partial_t(2\mathcal T_A(s)-H_0)=\mathscr D/t>0,\qquad
\partial_A\mathcal T_A(s)=\frac{1+t}{2t}\mathscr D>0.
\tag{AC.39}
$$

Proof. Differentiate the finite signed Lagrangian with live and
physical failure constraints. Its moment derivatives eliminate
multiplier changes; contact values and angular derivatives eliminate
weight and angle changes; the active equation or $\lambda=0$
eliminates the contrast term. The remaining explicit $t$ derivative is

$$
\sum_{\rm sat}p_jc(h_j)
 [\epsilon_jf(h_j)-\widehat n_j^TZ\widehat n_j]
 =\frac1t\sum_{\rm sat}p_ja_j=\mathscr D/t,
\tag{AC.40}
$$

using AC.33 and $a=0$ on pure rows. Apply the HALF factor and
$dt/dA=1+t$. $\square$

This proposition does not supply such a branch, a boundary derivative,
or everywhere differentiability, and does not interchange differentiation
with an endpoint or joint limit.

## 8. A single contrast platform at each fixed budget

**Theorem 8.1 (global weak platform structure).** Fix $t\ge t_0$ and
write

$$
v_t(\tau)=2\mathcal T_{\log(1+t)}(s_0\tau)-H_0,
\qquad 0\le\tau\le\tau_{\max}(t).
\tag{AC.41}
$$

This function is concave, nonincreasing and continuous on its whole
closed domain. Let $\mathscr O_t$ be the compact set of unconstrained
height-maximizing moment measures and define

$$
\tau_c(t)=\max_{\zeta\in\mathscr O_t}\int|z|d\zeta.
\tag{AC.42}
$$

Then $v_t(\tau)=v_t(0)$ exactly for $\tau\le\tau_c(t)$,
and $v_t$ is strictly decreasing afterwards if that interval is
nonempty. Every optimizer at $\tau>\tau_c(t)$ has $k=\tau$
and actual requested contrast $\mathsf V(F)=s_0\tau$.
In the strict-interior dual domain every attained optimal dual has
$\lambda=0$ for $\tau<\tau_c(t)$ and $\lambda>0$ for
$\tau>\tau_c(t)$. No generic multiplier assertion at
$\tau=\tau_c(t)$ is included.

Proof. On the compact set
$\{(h,b):h\in\mathscr C,0\le b\le tc(h)\}$ the integrands of
all live/failure moments, $k$ and $v$ are continuous. Their joint
convex hull is compact. Fixing AC.11 gives a compact convex set of
pairs $(k,v)$. Finite convex representation preserves these moments,
$k$ and $v$ simultaneously; Proposition 2.3 then reconstructs an
original instrument. A mixture uses an actually generated retained
choice, not an unacquired integral control. Mixtures prove concavity
of $v_t$; nesting of feasible sets proves monotonicity. Compactness
proves attainment and upper semicontinuity. Concavity supplies lower
limits at both endpoints by chords to any interior point, so
continuity holds also at $t=t_0$ and at $\tau_{\max}(t)$.

The maximum in AC.42 is attained. Its optimizer is feasible for every
smaller request, while equality of heights above $\tau_c$ would put
an optimizer in $\mathscr O_t$ with larger $k$, a contradiction.
Concavity forbids a later flat segment below the top value. Explicitly,
mixing a top optimizer with a hypothetical equal-valued pair beyond
the platform gives a strictly higher feasible value at the lower
request. If an optimizer after the platform had $k>\tau$, its same
moments would be feasible at request $k$, contradicting strict decline.
Finally $s_0\tau\le\mathsf V(F)\le s_0k$ gives actual equality.

For $\tau<\tau_c$, a top optimizer with $k=\tau_c>\tau$
forces every attained dual multiplier to vanish by complementarity.
For $\tau>\tau_c$, a zero multiplier would certify the same upper
bound for the unconstrained problem, contradicting the strictly lower
value. $\square$

AC.42 is a structural definition. It does not evaluate the entire
finite frontier, threshold curve or optimizer partition. The platform
along $s$ and strict growth along finite $A$ are different statements.

## 9. The platform extends strictly past the axis contrast

**Lemma 9.1 (the two-projection-line obstruction).** No globally
height-optimal weak finite-budget instrument can have all its
supported-nonzero low projection lines in at most two lines.
Additional supported-zero labels remain allowed.

Proof. This is RC72–73's common-dual exclusion, recalled with its
operative conditions. The projected live covariance is $I_2$ and the
same two-line failure covariance is $\operatorname{diag}(V,W)$,
with $V<W$. Two weighted live columns summing to $I_2$ form an
orthogonal matrix. The failure covariance diagonalizes in that basis;
its distinct eigenvalues force the two lines to be the coordinate
axes. Live first moments then force both orientations, with masses
$\alpha/2$ at $(1,\pm\alpha^{-1/2},0)$ and $\beta/2$ at
$(1,0,\pm\beta^{-1/2})$.

The layer is feasible only for $t\ge t_{\rm ax}=W/c_w$,
$\tau\le\sqrt\alpha$, where $c_w=c_*(0)<c_f<c_z$.
It has an explicit height attainer using the two $z$ rows with
$b=V$, and a pure/saturated allocation on the $w$ rows filling the
lower positive pure height first. To justify that optimization, the
source signs are

$$
\begin{gathered}
a_z=g_0+g_1/\alpha<b_z=2x_G/\sqrt\alpha,\quad a_z>0,\\
a_w=g_0+g_2/\beta>b_w=2y_G/\sqrt\beta>0,\quad
f(h_{z,\pm})=0,\quad f(h_{w,\pm})=-k_w,\\
k_w=11d_{\rm src}^2/(64h_2^2\beta),\qquad
Wk_w>a_w+b_w.
\end{gathered}
\tag{AC.43}
$$

Thus each $w$-row's endpoint splitting is optimal, and the negative
orientation must be filled before the positive one. If the layer
value equalled the global value, this specific layer attainer would
also be globally optimal. It lies in the strict dual domain because
$t_{\rm ax}>t_0$ and

$$
\tau_* -\sqrt\alpha
=\frac{\beta\sqrt{u_f}(1-\sqrt{\alpha u_f})}
 {1-\alpha u_f}>0.
\tag{AC.44}
$$

Its two $z$ rows are strictly unsaturated, $0<V<tc_z$, have opposite
nonzero live heights, and have the same physical failure line $e_2$.
The common-contact kernel argument AC.34, applied to their strict
endpoint interpolation equalities, forces simultaneously
$(Z-\Delta_f)e_2=0$ and $(Z+\Delta_f)e_2=0$.
But $\Delta_fe_2=(\Delta_{12},0)^T\ne0$. This contradiction
excludes global equality for the entire layer. One line cannot give
rank-two live covariance. This proves the lemma without fixing a
maximum-contrast completion or citing a support-count heuristic.
$\square$

**Theorem 9.2 (strict platform lower bound).** At every $t\ge t_0$,

$$
\min_{\zeta\in\mathscr O_t}k(\zeta)>\sqrt\alpha,
\qquad s_0\tau_c(t)>\sqrt\theta.
\tag{AC.45}
$$

Proof. Pointwise on the ellipse,
$|z|\ge\sqrt\alpha z^2$. Integration gives $k\ge\sqrt\alpha$.
Equality forces $z=0$ or $|z|=\alpha^{-1/2}$ almost everywhere,
so all projected lines are the two axes. Lemma 9.1 excludes that
for any top optimizer. Compactness of the top face upgrades the
strict individual inequalities to a strict minimum. Since
$s_0\sqrt\alpha=\sqrt\theta$, AC.45 follows. $\square$

## 10. Automatic nondegeneracy of three pure and two saturated contacts

**Definition 10.1 (eight moments and the matching hypothesis).** At
fixed $t>t_0$ use circle coordinates
$u=\cos\phi$, $v_{\rm circ}=\sin\phi$,
$h(\phi)=(1,u/\sqrt\alpha,v_{\rm circ}/\sqrt\beta)^T$.
For a sheet index $\eta\in\{0,1\}$ put

$$
\begin{gathered}
\Gamma_\eta(\phi)=
(1,u,v_{\rm circ},u^2,uv_{\rm circ},
 \eta c,\eta cu^2,\eta cuv_{\rm circ}),\\
B(t)=(1,0,0,\alpha,0,\mu/t,\alpha V/t,0),\qquad
H_\eta(\phi)=\ell(h(\phi))+\eta tc(h(\phi))f(h(\phi)).
\end{gathered}
\tag{AC.46}
$$

Here $c=c(h(\phi))$. The eight equations
$\sum_i p_i\Gamma_{\eta_i}(\phi_i)=B(t)$ are exactly the full live
Gram and physical failure covariance. The circle identity restores
the omitted live square moment, and
$\mu=\alpha V+\beta W$ restores the omitted failure square moment.

The matching hypothesis $\mathrm M$ consists of five positive
weights and five pairwise distinct circle points, with
$(\eta_0,\ldots,\eta_4)=(0,0,0,1,1)$, satisfying those eight
moments, and $d\in\mathbb R^8$ satisfying

$$
d\cdot\Gamma_\eta(\phi)\ge|H_\eta(\phi)|
\quad\text{on the whole circle, for }\eta=0,1.
\tag{AC.47}
$$

The entire geometric zero set consists exactly of these five contacts;
the pure and saturated zero sets are disjoint. Require
$H_{\eta_i}(\phi_i)\ne0$, $z_i\ne0$, and, for its maximizing
height sign $\epsilon_i$,

$$
q_i(\phi)=d\cdot\Gamma_{\eta_i}(\phi)
 -\epsilon_iH_{\eta_i}(\phi),\quad
q_i(\phi_i)=q_i'(\phi_i)=0,\quad
\gamma_i=q_i''(\phi_i)>0.
\tag{AC.48}
$$

The functions are analytic in the angles with positive denominators.
No Jacobian nonsingularity or contrast-response assumption is included
in $\mathrm M$.

**Lemma 10.2 (automatic rank eight).** With
$x=(p_0,\ldots,p_4,\phi_0,\ldots,\phi_4)$ and
$J=\partial_x\sum p_i\Gamma_{\eta_i}(\phi_i)$, hypothesis
$\mathrm M$ implies $\operatorname{rank}J=8$.

Proof. The three pure weight/angle pairs span the five live moment
differentials. Otherwise a nonzero degree-two trigonometric polynomial

$$
a_0+a_1\cos\phi+a_2\sin\phi+a_3\cos^2\phi
 +a_4\cos\phi\sin\phi
\tag{AC.49}
$$

would have value and derivative zero at three distinct points.
After multiplication by $e^{2i\phi}$ it is a polynomial of degree at
most four with six zeros counted with multiplicity. It must vanish
identically, contradicting independence of these five circle functions.
This argument includes any half-angle chart infinity.

The two saturated physical effects sum to $M_2\succ0$, so their
directions $\widehat n_3,\widehat n_4$ are independent. A symmetric
physical matrix $Z$ annihilating the failure weight and angle
differentials would satisfy, at each point,

$$
\widehat n_i^TZ\widehat n_i=0,\qquad
(\widehat n_i')^TZ\widehat n_i=0.
\tag{AC.50}
$$

The derivative of $c$ drops out after the first equality. Independence
of $\widehat n_i,\widehat n_i'$ gives $Z\widehat n_i=0$;
the two directions then give $Z=0$. The saturated failure
differentials thus span all three failure moments. Pure variables
change none of those moments, and can repair all five live
differentials. The full rank is eight. $\square$

**Lemma 10.3 (weight independence and positive reduced Hessian).**
The five weight columns $\Gamma_{\eta_i}(\phi_i)$ are independent.
For

$$
D_x=\operatorname{diag}(0,0,0,0,0,p_0\gamma_0,\ldots,p_4\gamma_4),
\tag{AC.51}
$$

its restriction to the two-dimensional space $\ker J$ is positive
definite. Consequently

$$
\begin{pmatrix}-D_x&-J^T\\J&0\end{pmatrix}
\tag{AC.52}
$$

is nonsingular, as is the eighteen-equation system of eight moments,
five contact values and five contact derivatives in legal local charts.

Proof. A linear dependence among weight columns first vanishes on the
three failure coordinates. The two saturated rank-one physical effects
are independent, so both their coefficients are zero. Three distinct
pure vectors $h_i$ are independent: otherwise three distinct points
of a nondegenerate ellipse would lie on one affine line. Their rank-one
matrices are then independent by congruence with their invertible
column matrix. This removes the remaining three coefficients.

If a vector in $\ker J$ has zero $D_x$ quadratic form, positivity of
$p_i\gamma_i$ makes all its angle coordinates zero. The independent
weight columns then make its weight coordinates zero. To prove AC.52,
apply it to $(\dot x,\dot d)$ in its kernel and multiply its first
row by $\dot x^T$. This gives $\dot x^TD_x\dot x=0$, hence
$\dot x=0$, and then $J^T\dot d=0$ gives $\dot d=0$ by Lemma 10.2.
The actual contact-derivative stationarity rows differ by the positive
$p_i$ row scalings. Changing regular angular charts and clearing
positive denominators at a root are invertible row/column operations.
Thus the asserted eighteen-equation Jacobian is nonsingular. $\square$

## 11. An exact nonzero contrast response on a whole angle box

**Lemma 11.1 (a legitimate increasing-contrast tangent).** Assume
$\mathrm M$ and let the three pure angles have charts

$$
\phi_0=2\arctan a_0,\quad
\phi_1=\pi+2\arctan a_1,\quad
\phi_2=\pi+2\arctan a_2,
\tag{AC.53}
$$

with

$$
a_0\in[1/50,3/100],\quad
 a_1\in[-3/10,-29/100],\quad a_2\in[3/25,7/50].
\tag{AC.54}
$$

Then $dk$ is nonzero on $\ker J$. In fact there is a tangent with
both saturated atoms fixed and $\dot k>0$, integrable to a local
positive-weight curve preserving all moments.

Proof. The pure report signs are $+,-,-$. Put
$A_{\rm p}=(\sqrt{p_0}h_0,\sqrt{p_1}h_1,\sqrt{p_2}h_2)$ and
$S_{\rm p}=A_{\rm p}^TQA_{\rm p}$. Here $h_i$ denotes the
contact vector, not an amplitude from $D$. Its diagonal is zero and

$$
(S_{\rm p})_{ij}=\sqrt{p_ip_j}
 [1-\cos(\phi_i-\phi_j)]>0\quad(i\ne j).
\tag{AC.55}
$$

Take the antisymmetric $\Omega$ with
$\Omega_{10}=1/(S_{\rm p})_{01}$,
$\Omega_{20}=-1/(S_{\rm p})_{02}$ and
$\Omega_{21}=1/(S_{\rm p})_{12}$. Then
$\dot A_{\rm p}=A_{\rm p}\Omega$ preserves its Gram to first
order, and $\operatorname{diag}(S_{\rm p}\Omega)=0$ preserves
the individual null constraints to first order. Each positive-weight
column therefore gives a valid $(\dot p_i,\dot\phi_i)$.
The derivative is

$$
\dot k=2\left[
\frac{z_0+z_1}{1-\cos(\phi_0-\phi_1)}
-\frac{z_0+z_2}{1-\cos(\phi_0-\phi_2)}\right].
\tag{AC.56}
$$

For $\rho_1=(a_0-a_1)/(1+a_0a_1)$ and
$\rho_2=(a_0-a_2)/(1+a_0a_2)$, elementary half-angle identities
factor this exactly as

$$
\dot k=\frac{2\cos\phi_0}{\sqrt\alpha}
 (\rho_1-\rho_2)(\rho_1+\rho_2-\tan\phi_0).
\tag{AC.57}
$$

All denominators below are positive on the full box AC.54.
Monotonicity of these rational functions in their two arguments gives

$$
\begin{gathered}
1550/4971\le\rho_1\le330/991,\qquad
-300/2507\le\rho_2\le-225/2509,\\
\tan\phi_0\le600/9991,\qquad
\rho_1+\rho_2-\tan\phi_0
\ge\frac{16446570850}{124510809327}>129/1000.
\end{gathered}
\tag{AC.58}
$$

Also $\rho_1-\rho_2>0$ and $\cos\phi_0>0$, proving strict
response on every point of the box, independently of the weights.

This is more than a formal tangent. With the saturated atoms fixed,
the pure live moment map has rank five on its six variables by the
first part of Lemma 10.2. Its fixed-moment set is a smooth
one-dimensional manifold. The tangent just constructed lies in its
tangent space and integrates to a local curve on that manifold.
Positive weights and the nonzero $z$ signs persist. All failure moments
are unchanged, so the curve is genuinely original-feasible by §13.
$\square$

If this particular factored response were zero outside the displayed
box, it would only invalidate this chosen direction. It would not
prove $dk|_{\ker J}=0$; the other tangent direction would remain.

## 12. The automatic first contrast seam

**Theorem 12.1 (global first seam from the matching data).** Assume
$\mathrm M$ and AC.54 at fixed $t>t_0$, and let

$$
\tau_c=\sum_{i=0}^4p_i|z_i|,\quad s_c=s_0\tau_c,\quad
A=\log(1+t).
\tag{AC.59}
$$

Then this $\tau_c$ is exactly AC.42's platform endpoint, and
$\sqrt\alpha<\tau_c<\tau_{\max}(t)$.
There is a positive right neighborhood of $s_c$ on which global
original optimizers are given by the same three pure and two saturated
contacts with positive weights and analytic active-side parameters.
For any $10\times2$ matrix $N_T$ whose columns form a basis of
$\ker J$, define

$$
\mathscr H=N_T^TD_xN_T\succ0,\qquad
q_T=N_T^T\nabla_xk\ne0,\qquad
\chi=q_T^T\mathscr H^{-1}q_T>0.
\tag{AC.60}
$$

The scalar is independent of the chosen tangent basis, and

$$
\mathcal T_A(s)=\mathcal T_A(s_c)
 -\frac{(s-s_c)^2}{4s_0^2\chi}+O((s-s_c)^3)
\quad(s\downarrow s_c\text{ from the right}).
\tag{AC.61}
$$

At the seam the value is $C^1$ and necessarily not $C^2$: its left
second derivative is zero and its right second derivative equals
$-1/(2s_0^2\chi)<0$. On both local sides and at the seam the minimum
number of supported-nonzero low labels is five and the minimum total
actual acquisition alphabet is six. The pure residual Gram has rank
three and the physical failure covariance has rank two.

Proof. AC.47 and the exact positive moment match attain $v_t(0)$.
Every other top optimizer must have zero gap for this same certificate.
For an interior $0<b<tc(h)$, endpoint interpolation equality requires
both endpoint gaps to be zero at the same direction. The disjoint
sheet zero sets exclude that. Hence all its supported data are among
exactly the five given sheet contacts. Lemma 10.3 makes their aggregate
weights unique. Thus every top optimizer has the same $k$, proving
AC.59 is the structural platform endpoint. Theorem 9.2 gives the
strict lower bound. Lemma 11.1 supplies a positive-weight feasible
curve with increasing $k$, so $\tau_c<\tau_{\max}(t)$.

For local continuation use $\lambda$ as a parameter in

$$
\mathcal L(x,d;\lambda)=
\sum_i p_i\epsilon_iH_{\eta_i}(\phi_i)+\lambda k(x)
-d\cdot\left(\sum_i p_i\Gamma_{\eta_i}(\phi_i)-B(t)\right).
\tag{AC.62}
$$

At $\lambda=0$ its stationarity and moment equations have the
nonsingular Jacobian AC.52. The analytic implicit function theorem
gives $x(\lambda),d(\lambda)$; no independent nonsingularity
hypothesis has been inserted.

Global sufficiency requires more than local stationarity. Around each
old contact, height and report signs are fixed. The corresponding
smooth signed gap still has value and derivative zero and strictly
positive second derivative, so on a sufficiently small neighborhood
it remains nonnegative and has that contact as its only zero.
On the complement of all five contact neighborhoods the original
absolute-value gap is continuous and strictly positive on a compact
union of two circles. It has a positive minimum. Uniform continuity
preserves that margin under small perturbations, including the axes,
$z=0$, zero-height directions and every chart's infinity. The opposite
height sign also has a strict margin near each contact. Consequently
for sufficiently small $\lambda\ge0$,

$$
d(\lambda)\cdot\Gamma_\eta(\phi)
 \ge|H_\eta(\phi)|+\lambda|z(\phi)|
\quad\text{for the entire two circles}.
\tag{AC.63}
$$

No new zero or unexamined sign sector has been discarded.

For completeness the physical common multipliers of this coordinate
dual are, with zero-based matrix indices,

$$
Y=\begin{pmatrix}
d_0&\sqrt\alpha d_1/2&\sqrt\beta d_2/2\\
\sqrt\alpha d_1/2&\alpha d_3&\sqrt{\alpha\beta}d_4/2\\
\sqrt\beta d_2/2&\sqrt{\alpha\beta}d_4/2&0
\end{pmatrix},
\tag{AC.64}
$$

$$
Z=\frac1t\begin{pmatrix}
\beta d_5h_2^2/d_{\rm src}^2&
-\sqrt{\alpha\beta}d_7h_1h_2/(2b_{\rm src}d_{\rm src})\\
-\sqrt{\alpha\beta}d_7h_1h_2/(2b_{\rm src}d_{\rm src})&
\alpha(d_5+d_6)h_1^2/b_{\rm src}^2
\end{pmatrix}.
\tag{AC.65}
$$

Then $d\Gamma_0=h^TYh$ and
$d\Gamma_1=h^TYh+tc\widehat n^TZ\widehat n$.
The physical $1/t$ factor is essential, and
$dB(t)=\operatorname{tr}Y+\operatorname{tr}(ZM_2)$.
For any original competitor's own $b$ the endpoint chord gives AC.18.
Integration of its complete moments and $k\ge\tau$ yields
$v\le dB(t)-\lambda\tau$. The continued family matches this upper
bound at $\tau=k(\lambda)$ and is realized by §13. It is therefore
a global original optimizer, not only a five-variable-family stationary
point or a polynomial root.

Differentiate AC.62's equations at zero:

$$
-D_xx'-J^Td'+\nabla_xk=0,\qquad Jx'=0.
\tag{AC.66}
$$

Writing $x'=N_T\xi$ gives $\mathscr H\xi=q_T$ and
$dk/d\lambda=\chi$. Lemmas 10.3 and 11.1 prove positivity.
Under $N_T\mapsto N_TR$ for invertible $R$, the transformations
$\mathscr H\mapsto R^T\mathscr HR$ and $q_T\mapsto R^Tq_T$
leave $\chi$ invariant. If desired, for a two-by-two $\mathscr H$,

$$
\chi=\frac{\mathscr H_{22}q_1^2-2\mathscr H_{12}q_1q_2+
 \mathscr H_{11}q_2^2}
 {\mathscr H_{11}\mathscr H_{22}-\mathscr H_{12}^2}.
\tag{AC.67}
$$

Thus $k(\lambda)=\tau_c+\chi\lambda+O(\lambda^2)$ is strictly
increasing and analytically invertible. Stationarity on the fixed
moment manifold gives $dv/d\lambda=-\lambda\,dk/d\lambda$,
so $dv/dk=-\lambda$ and

$$
v(k)=v_t(0)-(k-\tau_c)^2/(2\chi)+O((k-\tau_c)^3).
\tag{AC.68}
$$

The transformations $T=(H_0+v)/2$ and $s=s_0k$ give AC.61 with
its stated HALF factors. The left branch is constant by Theorem 8.1,
proving both differentiability assertions.

The five weights remain positive; the exact zero set and its disjoint
sheet structure persist. The same equality and weight-independence
argument forces every optimizer to use all five aggregate supported
contacts. FA69 forbids combining different effective supported live
directions into one actual low label, regardless of hidden Kraus
multiplicity. Positive fixed high acquired mass requires at least one
additional actual high label. Section 13 realizes exactly five low
plus one high, proving the minimum six. Three distinct pure $h_i$
with positive weights give rank-three pure Gram; the two saturated
effects continue to sum to $M_2\succ0$. $\square$

**Corollary 12.2 (what changes at the seam).** The unique aggregate
supported law in ordered local weight/angle coordinates is constant
on the platform and analytic on the active side. It is continuous but
not differentiable across the seam: on the right
$dk/ds=1/s_0$, whereas on the left $k$ is constant. Its available
contrast $s_0k$ is $s_c$ on the platform and the request $s$ on the
active side. Section 13's deterministic sign-report realization attains
that available contrast. Other legal platform reports may attenuate
actual contrast while satisfying $\mathsf V(F)\ge s$; after the seam,
every optimizer has $\mathsf V(F)=s$ by Theorem 8.1.
The value is $C^1$ although that law is not. Aggregate uniqueness
does not imply uniqueness of the whole instrument, binary report,
time laws, hidden Kraus representation or its supported-zero completion.
Optimizers may split labels or retain extra $\mathcal J_0$ outcomes;
the five/six statements are minima, not counts of every implementation.

Indeed, keep the entire acquisition record and all its CP maps fixed.
If $F_{\rm sign}$ is the full plus effect of the sign report, the legal
report kernel that changes a minus report to plus with probability
$1-q$ has plus effect $qF_{\rm sign}+(1-q)I_5$. On the platform its
actual contrast is $qs_c$, so every $q\in[s/s_c,1]$ meets the request.
At $s=0$, $q=0$ is the deterministic all-plus report. These report
choices preserve acquisition-record TV and every quantum/resource
interface; they need not attain the available contrast.

## 13. One common original instrument for all the interfaces

**Proposition 13.1 (full-complex chronological reconstruction).** Every
finite moment family in Proposition 2.3, including those in Theorem
12.1, has the following simultaneous realization. For each supported
low label choose an isometry
$J_j:\mathbb C^2\to\operatorname{ran}K_j^\dagger$ and put

$$
\begin{gathered}
Q_j=J_j^\dagger(K_j^\dagger K_j+N_j)J_j\succ0,\quad
C_j=Q_j^{1/2}J_j^\dagger E^\dagger,\\
B_j=K_jJ_jQ_j^{-1/2},\qquad
F_j=Q_j^{-1/2}J_j^\dagger N_jJ_jQ_j^{-1/2}.
\end{gathered}
\tag{AC.69}
$$

The entire low fibre is a qubit. Its identities are

$$
B_jC_j=K_jE^\dagger,\qquad
C_j^\dagger F_jC_j=EN_jE^\dagger,\qquad
B_j^\dagger B_j+F_j=I_2,\quad I_2-F_j\succ0.
\tag{AC.70}
$$

Use, for this attainer, the elapsed-time law

$$
g(u)=\frac2{(1+u)^2},\quad G_{\rm time}(u)=\frac{2u}{1+u},\quad
Z_j(u)=\sqrt{I_2-G_{\rm time}(u)F_j},\quad
R_j(u)=g(u)F_j[I_2-G_{\rm time}(u)F_j]^{-1}.
\tag{AC.71}
$$

The current-survivor failure density at label $\ell$ is the CP map

$$
Y\longmapsto w_\ell g(u)
\operatorname{tr}(F_j Z_j(u)^{-1}Y Z_j(u)^{-1})P_f.
\tag{AC.72}
$$

At the end only survivors receive the fixed isometry
$EB_j(I_2-F_j)^{-1/2}$. It composes with the no-event evolution to
cumulative live matrix $EB_j$.

For the complement take the isometries of Convention 2.2 and use one
jointly counted five-dimensional high fibre with encoder

$$
C_H=\begin{pmatrix}\sqrt{1-\delta}\,DE^\dagger\\W_\perp^\dagger\end{pmatrix}.
\tag{AC.73}
$$

Its rate is zero, its report is $+$, and its TP terminal decoder has
two inaccessible Kraus matrices
$E[I_3\ 0]$ and $EJ_0[0\ I_2]$.

Proof. The rank-two product and its right null vector imply that
$K_j^\dagger K_j$ and $N_j$ are supported in
$\operatorname{ran}K_j^\dagger$. This proves AC.70 and positivity
of $I-F_j$. The rank-one generalized eigenvalue calculation behind
FA69–70 gives the only possible nonzero eigenvalue

$$
\lambda(F_j)=\frac{b_j}{c(h_j)+b_j},\qquad
\int_0^1\|R_j(u)\|du=\log(1+b_j/c(h_j)).
\tag{AC.74}
$$

For a saturated row this is $t/(1+t)$ and activity $A$; its least
terminal survival eigenvalue is $1/(1+t)>0$. A pure row has zero
rate. These formulas concern the whole qubit, not only a sampled input.

Since $Z_j(u)^\dagger Z_j(u)+G_{\rm time}(u)F_j=I_2$, survival
plus all first-event effects sum to identity at every cut. Pulling
AC.72 back through $\operatorname{Ad}_{Z_j(u)}$ gives exactly
$w_\ell g(u)\operatorname{tr}(F_jY)P_f$. At terminal time
$Z_j(1)=\sqrt{I-F_j}$, and AC.70 makes the stated survivor map an
isometry. This proves full TP and chronological consistency; using
$EB_j$ alone as terminal processing would not have that property.
The high decoder effects sum to $I_5$ on its whole fibre.

The live Gram yields
$\sum K_j^\dagger K_j=\delta D^\dagger D+T^\dagger T+S^\dagger S$,
and the failure sum is $M$. Together with AC.73 and root TP, the
encoder effects sum to $I_5$. On every complex $M_5$ input $X$ the
forgotten outputs are exactly

$$
\Phi^L(X)=E[\Lambda_*(E^\dagger XE)+
 J_0W_\perp^\dagger XW_\perp J_0^\dagger]E^\dagger,
\tag{AC.75}
$$

$$
\Phi^f_\ell(\mathcal B)(X)=
 w_\ell\left(\int_{\mathcal B}g(u)du\right)
 \operatorname{tr}(EME^\dagger X)P_f
\quad(\mathcal B\subseteq[0,1]\text{ Borel}).
\tag{AC.76}
$$

These are complex-linear Kraus identities, so for any passive
reference and joint input $X$ the failure output is

$$
w_\ell\left(\int_{\mathcal B}g(u)du\right)P_f\otimes
\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X].
\tag{AC.77}
$$

This is the conditional partial trace, not the unconditional reference
marginal. The live map amplifies in the same way. The five maps remain
separate; labels $0,13$ are individually zero. No inaccessible Kraus
index or algebraic contact index becomes an extra free control.

Give low label $j$ report $\operatorname{sgn}z_j$, arbitrary at zero.
Failure effects have no coordinate-zero entry. The $01$ entry of the
low acquisition effect is $p_js_0\kappa z_j$, its total is zero,
and the plus report selects its positive half. Hence
$\mathsf V(F)=s_0\sum p_j|z_j|\ge s$ without any additional
actual label. The high acquisition probability on history $y$ is

$$
(1-\delta)A_y,\qquad A_y=\sum_{i=0}^2h_i^2p_{yi}.
\tag{AC.78}
$$

Its maximum is at $y=27$ and equals the original weak sharp cost
$\mathsf C(s)$ by JR's equality characterization. All low fibres
have dimension two; every future-accessible share is counted in the
high fibre. The supported encoder masses have signed height
differences $p_j(\ell+b_jf)$ and the high difference is the fixed
positive $H_0$, giving precisely AC.11.

The supported forgotten live and failure maps agree with JR's original
error optimizer. Relative to the ideal density $f_y$ in AC.3,
CG/JR's conditional minimax identification therefore gives, for each
$e,n$,

$$
e_{5,e,n}=e_{27,e,n}=E_*,\qquad e_{16,e,n}<E_*.
\tag{AC.79}
$$

It does not make the twelve errors equal, or replace the ideal
$f_y$ by the chosen $g$. All coherences and Borel sectors enter the
same original HALF error simultaneously with cost, contrast, activity
and actual record TV.

The free coherent counted complement in AC.73–.75 is permitted by the
JR class; it is distinct from the fixed CA10 completion that sends
the complementary subspace to certain failure. Splitting it off as
Convention 2.2's supported-zero low outcome is also permitted but adds
an actual label. Aggregation attains the minimal additional one high
label used in Theorem 12.1.

Every failure in this construction is a first event on the absolute
clock $6+u$. Only survivors receive terminal processing, all nonzero
whole-fibre inputs retain positive terminal survival, and no deadline
failure or postfailure positive-carrier action is introduced. These
are mathematical CP/TP statements; no native access, actuator,
controller or clock permission follows. Necessity in §§2–9 admitted
every stipulated time law, not only AC.71's chosen $g$. $\square$

## 14. Application to the selected finite strip

**Definition 14.1 (the exact strip matching family).** Use the existing
selected five-contact family on

$$
9999/10\le t\le10001/10.
\tag{AC.80}
$$

It is the exact root family with sheet indices $(0,0,0,1,1)$,
height signs $(+,+,-,+,-)$, angular bases $(0,\pi,\pi,0,3\pi/2)$,
and local coordinates $\phi_i=b_i^{\rm chart}+2\arctan x_i$.
The unknown order is
$X=(x_0,\ldots,x_4,p_0,\ldots,p_4,d_0,\ldots,d_7)$.
Its equations are the eight moments AC.46 and five pairs
$P_i(x_i)=P_i'(x_i)=0$, where $P_i$ is the positive-denominator-cleared
numerator of $d\Gamma_{\eta_i}-\epsilon_iH_{\eta_i}$.
These equations define exact roots, not the decimal comparison centres.

An explicit polynomial dictionary fixes the selected system. Set
$r=1+x^2$ and $(U,V_c)=(1-x^2,2x)$, $(-1+x^2,-2x)$ or
$(2x,-1+x^2)$ at bases $0,\pi,3\pi/2$, respectively. Put
$Z_c=U/\sqrt\alpha$, $W_c=V_c/\sqrt\beta$ and

$$
\begin{aligned}
D_c&=h_0^2\delta r^2+b_{\rm src}^2Z_c^2+d_{\rm src}^2W_c^2,\\
N_c&=h_1^2h_2^2\delta r^2+a^2h_2^2Z_c^2+
 c_{\rm src}^2h_1^2W_c^2,\\
L_c&=(r,Z_c,W_c)^TG(r,Z_c,W_c),\\
F_c&=\Delta_{11}(d_{\rm src}W_c/h_2)^2
 -2\Delta_{12}d_{\rm src}b_{\rm src}Z_cW_c/(h_1h_2).
\end{aligned}
\tag{AC.81}
$$

The pure numerator vector and denominator are
$(r^2,rU,rV_c,U^2,UV_c,0,0,0)$ and $r^2$, with height
numerator $L_c$. The saturated ones are

$$
(D_cr^2,D_crU,D_crV_c,D_cU^2,D_cUV_c,
 N_cr^2,N_cU^2,N_cUV_c),\quad D_cr^2,
\tag{AC.82}
$$

with height numerator $D_cL_c+tN_cF_c$.
The denominators are positive, so contact and derivative equations
are exactly those of the original gaps. The pure/saturated degrees
are four/eight, including their homogeneous points at infinity.

For specificity the exact rational box of the selected strip family
has the following decimal centres and rational radii. The source
expressions vary over all nine coordinates of CG's radius-$10^{-24}$
box; at its root their values are precisely AC.6–.9. Off root the
positive-pivot expressions are used only for interval inequalities.

| Coordinate | Exact centre | Exact radius |
| --- | --- | --- |
| $x_0$ | $0.0239983886642378607964294310901679274398090903664722197137187518454914256245$ | $\frac{1352398717422798889168526835628920448116113862103032228719459}{200000000000000000000000000000000000000000000000000000000000000000}$ |
| $x_1$ | $-0.295345657849378476306024301450483432304865657374456698646986628268886428144$ | $\frac{381833374155145598509658983054360083042002380519547448655637}{20000000000000000000000000000000000000000000000000000000000000000}$ |
| $x_2$ | $0.127640893565866832951084082477176300214962315541575619037141303345451632888$ | $\frac{18011592673256829614677545091765025569273064836904316025829}{3125000000000000000000000000000000000000000000000000000000000000}$ |
| $x_3$ | $0.151088636285802408169627202014237321102259249309113798503448321432425648207$ | $\frac{100159994713263644019028801958541273719092334035232276562767}{500000000000000000000000000000000000000000000000000000000000000000}$ |
| $x_4$ | $0.251237409581127356717457548926907910867475688233491094351221514230825083392$ | $\frac{614418380658562468145597081670027784278430316981003834567969}{2000000000000000000000000000000000000000000000000000000000000000000}$ |
| $p_0$ | $0.40356105912434429587028385796306861440267440303930150136389554751929146834$ | $\frac{923899159127341094528761555702862378160696139561701848702143}{100000000000000000000000000000000000000000000000000000000000000000}$ |
| $p_1$ | $0.183968107565001260784005926671856498076335410359553001589052683256527679673$ | $\frac{387522578665535945188776504826320822890302003655553563917499}{200000000000000000000000000000000000000000000000000000000000000000}$ |
| $p_2$ | $0.320043755240561323971427131511530770797419136045901918140238020651677504285$ | $\frac{655475919025580098848599222483946625113410709916376524851637}{100000000000000000000000000000000000000000000000000000000000000000}$ |
| $p_3$ | $0.0361481337929972639565176638271383531983401158115725409751968219643484098342$ | $\frac{8482811159806863759403423970878237933555697083021458679957}{1562500000000000000000000000000000000000000000000000000000000000}$ |
| $p_4$ | $0.0562789442770958554177654200264057635252309347436710379316169266081549378682$ | $\frac{1685447749185027880362306783274882728162793930626906403131773}{200000000000000000000000000000000000000000000000000000000000000000}$ |
| $d_0$ | $0.0244863499508953549551714115254785990455229653352660072423427775163528545274$ | $\frac{800823523742675546667615068988807767441824381899632603186881}{1000000000000000000000000000000000000000000000000000000000000000000}$ |
| $d_1$ | $0.00358535399816408539814614897471262212522535275458846005404812615848843507412$ | $\frac{267944088317750172635873009279825251400566010875974157485331}{4000000000000000000000000000000000000000000000000000000000000000000}$ |
| $d_2$ | $0.00715283156818416310756463367571142082407236735174105388329649684474543316655$ | $\frac{563814823723489601322051170541417590121564218974323506332229}{2000000000000000000000000000000000000000000000000000000000000000000}$ |
| $d_3$ | $-0.0183927422338048386671395313708612800603754221994926300815476732972939276256$ | $\frac{341968864127295411431475225768540518197668024562134210408331}{400000000000000000000000000000000000000000000000000000000000000000}$ |
| $d_4$ | $0.00403186188336576407517441402354141469657869331844789615857271955201630579117$ | $\frac{485911365836504603996658476655180965602759861531750400245937}{20000000000000000000000000000000000000000000000000000000000000000000}$ |
| $d_5$ | $21.7811418184010051130038082491418452870010839274827565904191911611069497405$ | $\frac{133162481853169764620438649635802076910660757864467559081967}{40000000000000000000000000000000000000000000000000000000000000}$ |
| $d_6$ | $-17.6924448925415546973374521319795072232789713541765300081920400162650964287$ | $\frac{272214511421723779859411793204890296953793919160356279071039}{100000000000000000000000000000000000000000000000000000000000000}$ |
| $d_7$ | $-11.0558270043314784681815861874335551388404582163945740457886311004049481113$ | $\frac{662232017060871770142826056659860481985593878352300811727}{400000000000000000000000000000000000000000000000000000000000}$ |

**Proposition 14.2 (scope of the supplied exact match).** Conditional
on Convention 1.1, this family has five positive weights, the indicated
nonzero height signs, pairwise distinct projection lines, the exact
moments and the whole-circle certificate AC.47 throughout AC.80.
Its only zeros are the five listed contacts, with positive angular
curvatures. It is analytic in $t$ on the interior of the strip and
regular at each endpoint as a local root family.

The mathematical ingredients of this existing selected-family result
are as follows. Its rational interval certificate gives a fixed
preconditioner $R$ for the eighteen equations $F_t(X)=0$ and the
box $X_*$ above. If $c_i,r_i$ denote its centres and radii, define

$$
q_i=\sum_j\sup_{X_*,t}|(I-RD_XF_t)_{ij}|\,r_j/r_i,
\qquad \eta_i\ge\sup_t|(RF_t(c))_i|.
\tag{AC.83}
$$

The exact bounds are $\max_iq_i<1/100$ and
$\max_i(\eta_i/r_i+q_i)<3/4$ uniformly in the strip and entire
source box. The varying common parameter is kept correlated before
preconditioning: $RF_{1000}(c)$ and
$R\partial_tF_t(c)$ bound the displacement over $|t-1000|\le1/10$.
In particular its two varying moment-target derivative rows are
$\mu/t^2$ and $\alpha V/t^2$. These are not independently varied
copies of $t$.
The map $X\mapsto X-RF_t(X)$ is a strict contraction from the box
into itself. Its unique fixed point is a root, since
$\|I-RD_XF_t\|<1$ makes $RD_XF_t$, hence $R$, invertible.
This is root existence and selection for the conditional matching
system; it is not authentication of the original CG source root.

The whole-circle signed gaps have exact repeated factors and positive
quotients as follows. In the table the coordinate $x$ is that row's
chart coordinate, while $x_i$ denotes its selected local root.

| Sheet and height sign | Chart base | Repeated factors | Quotient degree | Strict lower Bernstein control |
| --- | --- | --- | --- | --- |
| $0,+$ | $0$ | $(x-x_0)^2(x+1/x_1)^2$ | $0$ | $>0.00296843127843595$ |
| $0,-$ | $\pi$ | $(x-x_2)^2$ | $2$ | $>0.00932129211342938$ |
| $1,+$ | $0$ | $(x-x_3)^2$ | $6$ | $>0.00006045820572454$ |
| $1,-$ | $3\pi/2$ | $(x-x_4)^2$ | $6$ | $>0.00042530646409792$ |

The moment/contact equations force the exact zero remainders in these
divisions; no small residual is rounded to zero. For an even-degree
quotient $q(x)=\sum_{k=0}^na_kx^k$, use both signs
$\sigma=\pm1$ and the compactification

$$
(1-y)^nq(\sigma y/(1-y))
 =\sum_{k=0}^na_k\sigma^k y^k(1-y)^{n-k},\quad0\le y\le1.
\tag{AC.84}
$$

The corresponding initial Bernstein controls are
$a_k\sigma^k/\binom nk$. The supplied rational dyadic subdivisions
cover the two half-lines with respectively $2,4,7,4$ leaves and
maximum depths $0,2,5,2$. Every leaf's lower controls exceed the
strict bounds in the table. Positivity of Bernstein basis functions
therefore proves positivity on each full closed interval. The positive
leading coefficient includes $y=1$, the homogeneous point at infinity.
Thus all geometric zeros have been exhausted on both sheets; an angular
sample or a local curvature check alone would not give this conclusion.

The following coarser strict rational enclosures record the margins
needed for the application. They are consequences of the exact strip
bounds, and do not replace the source premises.

| Contact | Weight interval | Height sign | Angular curvature interval |
| --- | --- | --- | --- |
| $0$ | $(0.40355,0.40358)$ | $+$ | $(0.01678,0.01679)$ |
| $1$ | $(0.18396,0.18398)$ | $+$ | $(0.01678,0.01679)$ |
| $2$ | $(0.32003,0.32006)$ | $-$ | $(0.06031,0.06032)$ |
| $3$ | $(0.03614,0.03616)$ | $+$ | $(17.237,17.242)$ |
| $4$ | $(0.05627,0.05629)$ | $-$ | $(0.8519,0.8571)$ |

Use the normalized circle vectors
$\bar h_i=(1,\cos\phi_i,\sin\phi_i)^T$ and
$\bar r_i=(\cos\phi_i,\sin\phi_i)^T$. Throughout the strip,
$\det(\bar h_0,\bar h_1,\bar h_2)\in(1.5240,1.5244)$ and
$|\det(\bar r_i,\bar r_j)|>0.0459$ for every $i<j$.
The invertible diagonal rescalings to $h_i$ and $(z_i,w_i)^T$
preserve nondegeneracy. A five-weight moment minor lies in
$(-0.015478,-0.015475)$. These data establish the
geometric match required by $\mathrm M$ with the original physical
moments, not merely matching scalar thresholds. Multipliers are
converted by AC.64–.65 with the physical factor $1/t$.

**Corollary 14.3 (the automatic seam on this strip).** For each fixed
$t$ in AC.80, the exact strip family satisfies all hypotheses of
Theorem 12.1. Its critical contrast is

$$
s_c(t)=s_0\sum_{i=0}^4p_i(t)|z_i(t)|
\in(0.12421255682840184212039978060973179,
      0.12422087673167824424030274149411269).
\tag{AC.85}
$$

Every requested $0\le s\le3/25$ is on its initial platform, with

$$
\mathcal T_{\log(1+t)}(s)
=\frac12\left[H_0+d_0+\alpha d_3+
 \frac\mu t d_5+\frac{\alpha V}t d_6\right].
\tag{AC.86}
$$

At $s_c(t)$ it has the quadratic loss AC.61 with the exact positive
matrix expression AC.60; the minimum supported-low/total actual counts
remain five/six across the first seam.

Proof. The actual rational strip radii in Definition 14.1 imply the
strict pure-chart bounds

$$
\begin{aligned}
0.0239916&<x_0<0.0240052,\\
-0.2953648&<x_1<-0.2953265,\\
0.1276351&<x_2<0.1276467.
\end{aligned}
\tag{AC.87}
$$

Every one is strictly inside its corresponding interval AC.54.
This containment is for the whole strip box, not just the three
comparison centres. Proposition 14.2 supplies the other parts of
$\mathrm M$: full covariance, all zeros, positive weights, signs,
and angular curvature. Theorem 12.1 now proves automatic rank eight,
positive reduced Hessian, nonzero response and the first seam at
each $t$. Its identification of the top aggregate law makes AC.85
the platform endpoint, not simply a lower bound on available contrast.
AC.85 and $3/25=0.12$ give slack on the stated rectangle; evaluating
the common dual there gives AC.86. The same original instrument from
§13 attains every listed interface. $\square$

The qualitative strip application in this section gives neither a numerical
enclosure for $\chi$ nor a specified positive width of the active
neighborhood; §§19–23 supply quantitative response bounds and an explicit
right interval on the same strip. It does
not locate later zero-weight, collision, extra-zero, height-sign or
curvature seams, or extend the threshold curve outside the strip.
Analytic dependence on the strip and a pointwise local seam are not
a global finite-parameter atlas.

## 15. Primary theorem scopes and the matrix-roof obstruction

**Convention 15.1 (literature use).** The mechanisms below are existing
convex, spectral and continuation results. Their stated domains are
part of their conclusions' scope. The source-specific sector,
covariance, strict-slack and automatic-seam proofs in §§5–12 do not
depend on an unproved transfer of a roof theorem. There is no claim
of exhaustive literature coverage or worldwide priority.

[Uhlmann, *Roofs and Convexity*, arXiv:1108.3218v1][Uhlmann], Proposition 2.1
(PDF p.4), takes a real continuous $g$ on the entire pure-state set
$\Omega_{\rm pure}(\mathcal H)$ and a roof extension $G$. It gives
optimal decompositions of length at most $(\dim\mathcal H)^2+1$
and existence of minimal and maximal roof extensions. This is not
a theorem about every constrained subfamily of pure decompositions.

His Proposition 4.1 (PDF p.17, equations 51–53) requires a Hermitian
**antilinear** operator $\vartheta$ on $\mathcal H$ and the payoff

$$
g(|\psi\rangle\langle\psi|)=|\langle\psi,\vartheta\psi\rangle|.
\tag{AC.88}
$$

For the ordered eigenvalues $\lambda_1\ge\lambda_2\ge\cdots$ of
$|\sqrt\omega\,\vartheta\sqrt\omega|$, its convex and concave
roofs are respectively

$$
g^\cup(\omega)=\max\{0,\lambda_1-\sum_{j>1}\lambda_j\},
\qquad g^\cap(\omega)=\sum_j\lambda_j;
\tag{AC.89}
$$

both roofs are flat. Here $\omega$ is a density operator, unrelated
to AC.7's scalar $\omega$. Applying this formula would require an
exact identification of the payoff, the entire decomposition domain,
and the additional coupled live and physical failure moments.
A restricted real $Q$-null ellipse with two endpoint sheets and
rational saturated payoff supplies none of those identifications
merely by resembling a roof problem. No such transfer is used here.

[Hildebrand, *Concurrence of Lorentz-positive maps*,
quant-ph/0612064v1][Hildebrand], Theorems 4.4 and 5.1 (PDF pp.7–8), assumes a
Lorentz-positive map $\Upsilon:\mathbb R^m\to\mathbb R^n$.
The determinant pencil $\det\Upsilon(x)-\lambda\det x$ has real
generalized eigenvalues. Concurrence uses its second-largest eigenvalue
and I-fidelity its smallest in
$2\sqrt{\det\Upsilon(x)-\lambda\det x}$. Interior Lorentz points
have optimal decompositions into two boundary points in the indicated
eigenspace direction. The input cone and map positivity are essential.

**Proposition 15.2 (no direct whole-cone Lorentz identification).** The
full real null-Gram cone

$$
\mathcal K_Q=\{X\in\operatorname{Sym}_3:X\succeq0,
 \operatorname{tr}(QX)=0\}
\tag{AC.90}
$$

is not linearly isomorphic to a Lorentz cone.

Proof. Since $I_3\succ0$ and $\operatorname{tr}Q=0$, it has
relative dimension five. The nonnegative functional $X\mapsto X_{22}$
exposes the proper two-dimensional face

$$
\left\{\begin{pmatrix}\alpha u&v&0\\v&u&0\\0&0&0\end{pmatrix}:
 u\ge0,\ |v|\le\sqrt\alpha\,u\right\}.
\tag{AC.91}
$$

Positive semidefiniteness makes the last row zero when $X_{22}=0$;
the null trace then gives exactly this face. Every proper nonzero
face of a Lorentz cone of dimension at least three is a ray: two
nonproportional boundary rays have an interior sum by strict triangle
inequality. Linear cone isomorphisms preserve faces and dimensions,
so AC.91 rules out the identification. $\square$

This excludes the direct whole-cone route, not separately proved
rank-two slices, embeddings, alternative representations or other
roof formulas. The saturated rational payoff and the joint moment
constraints would still require their own correspondence.

[Halaseh–Magron–Skomra, arXiv:2604.15072v1][HMS], Theorem 1.1 (PDF p.2),
assumes $h_1\equiv1$, $b_1>0$ and $b$ in the relative interior of
the moment cone in its compact generalized moment problem, and
concludes dual attainment. Primal compactness/no-gap is a different
statement. Proposition 4.1 explicitly provides the continuous two-sheet
relative-interior argument, denominators, absolute values and contrast
slack needed here. Quoting a polynomial GMP theorem without that
mapping would not supply the common dual, a seed or a finite frontier.

Hauenstein–Mohammad-Nezhad–Tang–Terlaky,
*On computing the nonlinearity interval in parametric semidefinite
optimization*, [arXiv:1908.10499v3][Hauenstein], uses independent constraint matrices
and primal/dual strict feasibility (Assumptions 1–2, PDF p.2), with a
fixed-direction linear objective perturbation. Theorem 1 (p.8) gives
finitely many transitions. Lemma 2 (p.11) relates nonsingular optimal
KKT Jacobians to nondegeneracy and strict complementarity; Theorem 2
(p.12) gives the analytic optimal trajectory when that Jacobian is
nonsingular. An algebraic root need not be PSD or optimal, and a
singular algebraic point need not be a transition. These results do
not establish the automatic rank and reduced positivity of §10;
those were proved directly for the present contact system.

Martin–Goldsztejn–Granvilliers–Jermann's author manuscript,
[DOI 10.1007/s10898-014-0201-3][Martin], §§3.1–3.2 (PDF pp.8–11), starts
ParCont from a solution on a regular one-manifold and certifies the
tracked component by interval parallelotopes. Its active-system
changes handle one activity change at a time; other singularities
stop certification. It supplies neither an initial matching family,
whole-circle global inequalities, disconnected-component coverage nor
a two-parameter atlas. In §12 global sufficiency comes from AC.63,
not from continuation alone.

The related complete-class theorem of Dette–Melas,
[arXiv:1105.3575v1][DetteMelas], Theorem 3.1 and equations 3.2–3.4, uses a
distinguished information-matrix diagonal entry and the specified two
**ordinary Chebyshev-system** conditions, with either the 3.3 or 3.4
alternative. They must not be relabelled as extended-Chebyshev
hypotheses. The pure sheet here has identically zero failure rows,
so the full two-sheet function list does not directly satisfy those
determinant conditions. No finite three-atom theorem follows from
that attribution.

## 16. Exact credit and unresolved finite mathematics

The path minimum, positive-survival obstruction, arbitrary-complex
label rigidity, capacity and full-output realization are supplied by
FA68–70 and JR42. FA72/77 supplies the moment correspondence and
attainment, FA78–79 the entire scalar feasibility threshold and its
minimum-budget height. RC's static dual/contact curve and TA's full
static equality obstruction supply AC.19. RC68/70/72–73 supplies the
attained common certificate, common-contact kernel and two-line
exclusion, with the actual conditional proofs recalled in §§4,6,9.
The selected five-contact strip supplies the exact matching data in
§14. These are reused mathematical inputs; reformulating their
interfaces is not an additional discovery.

The additional deductions here are the source-specific covariance
obstruction with quantitative coefficient mass, impossibility of
all-common-contact optimal failure allocation, strict all-optimizer
saturation and finite-budget growth, the single-platform structure,
and automatic first-seam response and regularity under $\mathrm M$.
The qualitative strip application in §14 pays $\mathrm M$ and the whole
pure angle-box containment only on AC.80. Quantitative bounds for $\chi$
and a specified active-side width are supplied in §§19–23.

The following parts of the original programme remain unresolved.
The full weak finite frontier requires evaluated global roots and
positive common weights for every feasible interior $(s,A)$, the
whole-circle certificate on both sheets, all optimizer/contact/rank
changes and every seam. The structural threshold AC.42 and a selected
finite strip do not supply that global evaluation. Nor do the known
existence bounds of at most nine supported-nonzero low labels plus
one high, or at most twenty-four certificate sheet contacts, specify
minimum actual alphabets. Projection lines, physical failure rays,
readable labels, hidden Kraus multiplicity and jointly acquired
Hilbert dimension remain different counts.

The fixed-strength deficit coefficient $K(s)$ still needs its
precontact/contact evaluation, chosen orientations, degenerate cases
and gluing beyond the supplied postcontact and local formulas.
A source-specific common attaining family $\nu_\star$, where needed,
requires the original moments, signs and rank conditions; a scalar
failure allocation or fixed maximum-contrast completion is insufficient.
Global finite-$A$ optimizer acquisition alphabets and their transitions
remain open beyond their stated local or boundary results.

[JS, §§11–12][JS] already supplies the global clamped limiting selector
and inverse, exact pointwise two/three physical-failure-ray criterion
and its endpoint matching. Its §§14 and 16 supply the critical
every-instrument strip, sub-spectral uniform rate and compact-uniform
spectral layer. These are not left unresolved here. The remaining
JS.58 source-specific zero inventory, isolation, ordering,
multiplicities, sign intervals and required next terms are different
obligations. Critical five-label and static-contact joint layers
outside those results still require proof. A limiting selector and
uniform asymptotic layer do not evaluate the finite frontier.

FA's isolated strong branch and its four-low counts at normalized
budgets $r=1,2$, five at every other feasible strong budget, with no
six-low strong region, retain their separate scope. Weak feasibility
counts, static counts and the present five/six optimum minima are
not transferred into that branch. In joint limits, finite positive
survival must not be replaced by a finite-budget certain-failure row.

## 17. Physical and operational application boundaries

All source-root and minimax antecedents of Convention 1.1 remain
`ASSUMED-UNVERIFIED`. The CP instrument in §13 supplies a simultaneous
conditional mathematical realization, not lawful access to the sole
unknown specimen or native execution. Calibration, actual acquisition
and report generation, coherent storage and joint counting of every
accessible share, acquisition duration and cut placement, whole-fibre
decoder actuation and the same absolute FIRST clock require their
own bridges. So do positive terminal survivors, stopped archives,
source and epoch identification, controller and permissions.

An affine-coordinate or cyclic-state model supplies none of those
quantum resources by numerical or naming agreement. OriginalControl
remains geometric until an operational correspondence is supplied.
No extra specimen, time interval, callback or postfailure action is
licensed by the conditional formulas. The full quantum-first AURIC
FIB ATOM programme retains its original finite-frontier, coefficient,
joint-limit and native obligations.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[FA]: FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md
[RC]: FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md
[TA]: FIB_NATIVE_TOTAL_ACTUAL_ACQUISITION_ALPHABET.md
[JS]: FIB_NATIVE_JOINT_ENDPOINT_SATURATION_BOUNDARY.md

[Uhlmann]: https://arxiv.org/abs/1108.3218v1
[Hildebrand]: https://arxiv.org/abs/quant-ph/0612064v1
[HMS]: https://arxiv.org/abs/2604.15072v1
[Hauenstein]: https://arxiv.org/abs/1908.10499v3
[Martin]: https://doi.org/10.1007/s10898-014-0201-3
[DetteMelas]: https://arxiv.org/abs/1105.3575v1

## 追加锚（本行以下为增补区）

## 18. Quantitative first activation and its selected equations

**Convention 18.1 (conditional scope and canonical data).** Sections 18–25
retain the complete original experiment and every condition in §§1–3.
In particular the original source root, ranks, root TP identity, HALF
complete stopped-cq minimax/error identification, and JR34–42's sharp
joint-cost and unaveraged all-error-optimizer equality identification
remain the named premises of Convention 1.1. The necessary reduction is
FA69, FA72 and FA87, for arbitrary complex encoders and hidden Kraus
multiplicity in the original finite/countable and stipulated measurable
finite-fibre class. None of these premises is replaced by a restriction
to the displayed attainer. The additional spectral/strict-decrease
supplier used in RC58.4/RC.7 retains its separate hypotheses; sharp-cost
rigidity alone does not establish that supplier. The quantitative
contact argument below uses the full attached moment correspondence,
not those additional residual-optimizer signs.

Use the source dictionary AC.6–.14, the eight moments AC.46, and the
polynomial numerators AC.81–.82. In particular $N_{ij}$ is the height
matrix, $G=LNL$, $L=\operatorname{diag}(s_0,1,1)$ and
$M_2=\operatorname{diag}(m_1,m_2)$. Physical failure whitening and
the spectral quantities $d_f,z_f,L_f$ are exactly AC.8. The complete
source comparison expressions and all nine varying source coordinates
are [FA94][FA] and RC58.3. Only at the source root are they asserted
to define the original normalized experiment.

Let $\bar X$ be FA94's exact eighteen-entry rational centre, let
$\varrho$ be FA95's eighteen strip radii, and let $R$ be **that same**
FA95 rational $18\times18$ preconditioner. These specified data,
including all 324 entries of $R$, are used without taking a numerical
inverse or introducing a second matrix specification. Set

$$
I=[9999/10,10001/10],\qquad
\mathcal B_X=\prod_{j=0}^{17}[\bar X_j-\varrho_j,\bar X_j+\varrho_j],
\qquad \|v\|_\varrho=\max_j|v_j|/\varrho_j.
\tag{AC.92}
$$

This eighteen-coordinate contact root is distinct from the original
nine-coordinate CG source root. A statement about uniqueness below
means uniqueness in $\mathcal B_X$ for this selected contact system.

**Definition 18.2 (report normalization and selected root).** Write
$u=\cos\phi$, $v=\sin\phi$, $z=u/\sqrt\alpha$,
$w=v/\sqrt\beta$, and set

$$
k_u=\sum_i p_i|u_i|,\qquad
C_s=s_0/\sqrt\alpha,\qquad s_\lambda=C_s k_u.
\tag{AC.93}
$$

Thus $k_u=\sqrt\alpha\,k_z$, where $k_z=\sum p_i|z_i|$
is the contrast moment in AC.11. Here $\lambda$ multiplies $|u|$;
the corresponding multiplier of $|z|$ is $\lambda\sqrt\alpha$,
and the multiplier of physical requested contrast is
$\lambda/C_s=\lambda\sqrt\alpha/s_0$. None is a CG root coordinate.
The five contacts have the following fixed charts and signs:

| $i$ | Sheet $\eta_i$ | Height sign $\epsilon_i$ | Maximum-report sign $\sigma_i$ | Chart base |
| --- | --- | --- | --- | --- |
| $0$ | $0$ | $+$ | $+$ | $0$ |
| $1$ | $0$ | $+$ | $-$ | $\pi$ |
| $2$ | $0$ | $-$ | $-$ | $\pi$ |
| $3$ | $1$ | $+$ | $+$ | $0$ |
| $4$ | $1$ | $-$ | $+$ | $3\pi/2$ |

For $\phi=b^{\rm chart}+2\arctan x$, put $r=1+x^2$ and
use $(U,V_c)=(1-x^2,2x)$, $(-1+x^2,-2x)$ or
$(2x,-1+x^2)$ in the respective charts. With the numerator
dictionary AC.81–.82, define

$$
\begin{gathered}
D_0=r^2,\quad D_1=D_cr^2,\qquad
W_0=rU,\quad W_1=D_crU,\\
P_{\eta,\epsilon,\sigma;\lambda}
 =d\cdot\Gamma_\eta^{\rm num}
  -\epsilon H_\eta^{\rm num}-\lambda\sigma W_\eta.
\end{gathered}
\tag{AC.94}
$$

In particular $W_\eta=D_\eta u$. The ordered equations
$\mathcal F(X;t,\lambda)=0$ are the eight components of
$\sum_i p_i\Gamma_{\eta_i}(\phi_i)-B(t)$, followed, in increasing
$i$, by

$$
P_{\eta_i,\epsilon_i,\sigma_i;\lambda}(x_i)=0,\qquad
P'_{\eta_i,\epsilon_i,\sigma_i;\lambda}(x_i)=0.
\tag{AC.95}
$$

The unknown order is $(x_0,\ldots,x_4,p_0,\ldots,p_4,d_0,\ldots,d_7)$.
All denominators are positive on the real charts. At a zero, clearing
them preserves value and stationarity exactly. Pure and saturated
degrees are at most four and eight. Their homogeneous values also
specify each chart's point at infinity.

## 19. A uniform rational multiplier rectangle

**Lemma 19.1 (weighted perturbation margins).** On the entire source
comparison box, $t\in I$ and $X\in\mathcal B_X$,

$$
\|R\partial_\lambda\mathcal F\|_\varrho<4\cdot10^9,
\qquad
\|R D_X\partial_\lambda\mathcal F\|_\varrho<10^6.
\tag{AC.96}
$$

Proof. The following exact rational bounds use FA95's row and column
order. In the last column $L_i>\sum_{j=8}^{17}|R_{ij}|$; the first
eight rows of $\partial_\lambda\mathcal F$ vanish.

| $i$ | Strict lower bound for $\varrho_i$ | $L_i$ |
| --- | --- | --- |
| $0$ | $6\cdot10^{-6}$ | $5$ |
| $1$ | $10^{-5}$ | $70$ |
| $2$ | $5\cdot10^{-6}$ | $32$ |
| $3$ | $2\cdot10^{-7}$ | $2$ |
| $4$ | $3\cdot10^{-7}$ | $3$ |
| $5$ | $9\cdot10^{-6}$ | $1$ |
| $6$ | $10^{-6}$ | $43$ |
| $7$ | $6\cdot10^{-6}$ | $44$ |
| $8$ | $5\cdot10^{-6}$ | $3/50$ |
| $9$ | $8\cdot10^{-6}$ | $13/100$ |
| $10$ | $8\cdot10^{-7}$ | $2$ |
| $11$ | $6\cdot10^{-8}$ | $2$ |
| $12$ | $2\cdot10^{-7}$ | $2$ |
| $13$ | $8\cdot10^{-7}$ | $2$ |
| $14$ | $2\cdot10^{-8}$ | $2$ |
| $15$ | $3\cdot10^{-3}$ | $260$ |
| $16$ | $2\cdot10^{-3}$ | $350$ |
| $17$ | $10^{-3}$ | $160$ |

Each last entry is obtained by summing ten absolute rational entries
of the specified $R$; it involves no new inverse. The same radii give

$$
\begin{gathered}
\max_{i<5}\varrho_i<2\cdot10^{-5},\qquad
\max_{5\le i<10}\varrho_i<10^{-5},\\
\sum_{i=10}^{14}\varrho_i<3\cdot10^{-6},\qquad
\sum_{i=15}^{17}\varrho_i<8\cdot10^{-3}.
\end{gathered}
\tag{AC.97}
$$

For coefficient $\ell^1$ norms in each of the three needed charts,
the positive-pivot source enclosures give

$$
\|D_c\|_1<1/2,\quad \|N_c\|_1<1/25,\quad
\|L_c\|_1<3/10,\quad \|F_c\|_1<1/4.
\tag{AC.98}
$$

These follow directly, for example, from the rational relaxations
$0.98<h_0<0.99$, $0.70<h_1<0.71$, $0.80<h_2<0.81$,
$0.065<a<0.066$, $0.145<b_{\rm src}<0.146$,
$0.015<c_{\rm src}<0.016$, $0.098<d_{\rm src}<0.099$,
$0.87<\alpha<0.88$, $0.12<\beta<0.13$,
$0.125<s_0<0.126$ and $|G_{ij}|<0.003$.
The coefficient norms of the first five moment numerators are at
most four on the pure sheet and two on the saturated sheet; the last
three saturated norms are at most $4/25$. Consequently
$\|W_\eta\|_1\le4$, and for the contact coordinates $|x_i|<0.3$,

$$
|W_\eta|,|W'_\eta|<32,\qquad |W''_\eta|<224.
\tag{AC.99}
$$

Indeed their degrees are at most eight and $|x|<1$; derivative
coefficient sums give these conservative bounds. The weighted row
bounds in AC.96 are bounded respectively by
$\max_i32L_i/\varrho_i$ and
$\max_i224L_i\max_{j<5}\varrho_j/\varrho_i$.
Substitution of the displayed rational bounds proves AC.96.
$\square$

**Theorem 19.2 (selected analytic root and displacement).** For every
$t\in I$, $0\le\lambda\le10^{-12}$ and each source comparison
point, AC.95 has a unique root in $\mathcal B_X$. It is real analytic
in the parameters on their analytic domains, with local extensions
at the rectangle endpoints, and satisfies

$$
\|\partial_\lambda X(t,\lambda)\|_\varrho<5\cdot10^9,
\qquad
\|X(t,\lambda)-X(t,0)\|_\varrho<5\cdot10^9\lambda
\quad(\lambda>0).
\tag{AC.100}
$$

At $\lambda=0$ the displacement is zero. These are contact-root
statements, not source-root or off-root TP assertions.

Proof. FA96's correlated-parameter rational certificate for
$T_0(X)=X-R\mathcal F(X;t,0)$ gives self-map radius ratio $<3/4$
and weighted derivative norm $<1/100$. Its centre residual is
preconditioned before taking the common $t$ interval; in particular
the two target derivative rows are $\mu/t^2$ and $\alpha V/t^2$.
No independent copies of that parameter are introduced. By AC.96,
$T_\lambda=X-R\mathcal F(X;t,\lambda)$ has

$$
\begin{aligned}
T_\lambda(\mathcal B_X)&\subset
\bar X+(3/4+4\cdot10^9\lambda)(\mathcal B_X-\bar X)
\subset\bar X+(4/5)(\mathcal B_X-\bar X),\\
\|D_XT_\lambda\|_\varrho
&<1/100+10^6\lambda\le0.010001<1/50.
\end{aligned}
\tag{AC.101}
$$

The geometric-series contraction argument gives its unique fixed
point. The Neumann series makes $RD_X\mathcal F$ invertible;
since these are square matrices, both $R$ and $D_X\mathcal F$ are
invertible, and a fixed point is a root. Differentiation gives
$X_\lambda=-(D_X\mathcal F)^{-1}\mathcal F_\lambda$ and
norm $<4\cdot10^9/(1-1/50)<5\cdot10^9$. Integration proves
AC.100. The positive source pivots and denominators make the equations
analytic. Their invertible Jacobian and common-box uniqueness identify
the local implicit solutions on overlaps, including the endpoints.
$\square$

## 20. Every report half-circle and every intermediate height

**Theorem 20.1 (uniform whole-circle certificate).** At the selected
source-root family of Theorem 19.2,

$$
d(t,\lambda)\cdot\Gamma_\eta(\phi)
\ge |H_\eta(\phi)|+\lambda|\cos\phi|
\quad(\eta=0,1,\ \phi\in\mathbb R/2\pi\mathbb Z).
\tag{AC.102}
$$

The maximum-report absolute-height gap has exactly the five specified
zeros. The pure and saturated zero sets are disjoint. All used weights,
height signs, report signs, curvatures and ranks remain nondegenerate
throughout the closed parameter rectangle.

Proof. Fix the same $t$ and compare the selected $\lambda$ root with
its zero-multiplier root. The moment numerator bounds, AC.97 and
AC.100 imply for every needed signed report polynomial

$$
\|P_\lambda-P_0\|_1<7\cdot10^6\lambda,
\qquad \|P_0\|_1<20,
\qquad |x_i(t,\lambda)-x_i(t,0)|<10^5\lambda.
\tag{AC.103}
$$

For the first estimate an explicit majorant is
$5\cdot10^9\lambda[4(3\cdot10^{-6})+(4/25)(8\cdot10^{-3})]
+4\lambda<7\cdot10^6\lambda$. All these are coefficient bounds,
not evaluations on an angular grid.

Let $\mathscr D_a^2$ mean twice taking the quotient upon division
by $x-a$. The descending synthetic-division recurrence gives, for
$|a|<0.3$,

$$
\|\mathscr D_a^2\|_{1\to1}\le(1-0.3)^{-2}<3,
\qquad
\|\partial_a\mathscr D_a^2\|_{1\to1}
\le2(1-0.3)^{-3}<6.
\tag{AC.104}
$$

At a designated contact the remainder is **exactly** zero by AC.95;
an interval containing zero is not used as zero. For its deflated
quotient, AC.103–AC.104 give

$$
\|Q_\lambda-Q_0\|_1
<3(7\cdot10^6)\lambda+6(20)(10^5)\lambda
<4\cdot10^7\lambda\le4\cdot10^{-5}.
\tag{AC.105}
$$

FA97's exact double-root divisions and covering Bernstein partitions
supply the following normalized margins at $\lambda=0$:

| Sheet and height sign | Contact's chart | Quotient degree $n$ | Usable margin $m$ |
| --- | --- | --- | --- |
| Pure, $-$ | $\pi$ | $2$ | $9/1000$ |
| Saturated, $+$ | $0$ | $6$ | $6\cdot10^{-5}$ |
| Saturated, $-$ | $3\pi/2$ | $6$ | $4\cdot10^{-4}$ |

More precisely, for both signs of the real chart, every Bernstein
control of $(1-y)^nQ_0(\pm y/(1-y))$ on its specified closed
dyadic leaf exceeds $m$. Hence
$Q_0(x)>m(1+|x|)^n\ge m(1+x^2)^{n/2}$ on the full real axis.
For any degree-at-most-$n$ perturbation,

$$
\frac{|(Q_\lambda-Q_0)(x)|}{(1+x^2)^{n/2}}
\le\|Q_\lambda-Q_0\|_1.
\tag{AC.106}
$$

The least margin $6\cdot10^{-5}$ exceeds $4\cdot10^{-5}$.
Thus all three deflated quotients stay strictly positive, including
their positive homogeneous leading coefficients at infinity. These
prove the needed inequalities on the report half containing each
contact.

The two pure positive-height contacts require two report polynomials.
At zero multiplier, in the base-zero chart,

$$
P_0(x)=a_*(x-a_0)^2(x-b_1)^2,\qquad
0.0029<a_*<0.003,\quad |a_0|<0.025,\quad3.38<b_1<3.4,
\tag{AC.107}
$$

where $a_0=x_0(t,0)$ and $b_1=-1/x_1(t,0)$.
On $u\ge0$, base-zero $x\in[-1,1]$ covers the entire closed
half-circle. Removing its designated contact leaves
$Q_0=a_*(x-b_1)^2>1/100$. On $u\le0$ use the base-$\pi$
coordinate $y\in[-1,1]$. The homogeneous change $x=-1/y$
gives, after removal of the first contact in this chart,
$\widetilde Q_0=a_*b_1^2(1+a_0y)^2>1/100$.
AC.105 preserves both strict margins. At positive multiplier the
two contacts have opposite reports and are not required to be zeros
of one common polynomial.

It remains to check the other report half for each of the three
single-contact gaps. Their designated $|u_i|$ exceed $0.9,0.9,0.4$,
respectively. If $\phi$ belongs to the opposite half-circle, elementary
circle geometry gives

$$
\sin^2\frac{\phi-\phi_i}{2}\ge\frac{u_i^2}{4},\qquad
\frac{(x-a)^2}{1+x^2}
=(1+a^2)\sin^2\frac{\phi-\phi_i}{2}.
\tag{AC.108}
$$

The saturated physical denominator
$D_c/(1+x^2)^2$ is less than one by AC.98. Dividing the old
polynomials by their positive denominators therefore gives opposite-half
gaps strictly greater than $0.0018$, $0.00001215$ and $0.000016$.

For an uncleared-gap perturbation use $0<c(h)<1/4$ on the whole
circle. To verify this last bound write its numerator and denominator
as affine functions of $u^2\in[0,1]$. At $u^2=1$ their bounds are
$N<9/1000$, $D>3/80$, and at $u^2=0$ they are
$N<7/1000$, $D>2/25$. Thus $4N<D$ at both endpoints and
everywhere between. The physical gap change is at most

$$
5\cdot10^9\lambda
 [3\cdot10^{-6}+(1/4)(8\cdot10^{-3})]+\lambda
<1.1\cdot10^7\lambda\le1.1\cdot10^{-5}.
\tag{AC.109}
$$

This is smaller than every opposite-half margin. All height signs
and report signs, both sheets, both axes and every chart infinity
have now been covered. The strict quotient and opposite-half bounds
exclude all additional maximum-report zeros.

For completeness, positive weights and the height signs follow on
the same entire box from FA99's intervals. The angular curvatures of
the perturbed signed gaps have the following strict rational relaxations:

| Contact | Curvature interval |
| --- | --- |
| $0$ | $(0.0167826,0.0167865)$ |
| $1$ | $(0.0167814,0.0167877)$ |
| $2$ | $(0.0603113,0.0603166)$ |
| $3$ | $(17.2374,17.2419)$ |
| $4$ | $(0.85197,0.85710)$ |

They are obtained from
$(P_i''-\lambda\sigma_iW_i'')D_{\eta_i}^{-1}
((1+x_i^2)/2)^2$ when $P_i$ here denotes the zero-report-term
polynomial evaluated with the current $d$; equivalently use
$P_{i,\lambda}''$ directly. The exact value and first derivative
vanish at the selected root. The normalized pure frame
$((1,u_i,v_i))_{i=0}^2$ has determinant in $(1.5240,1.5244)$,
and the moment minor with rows $(1,u,v,\eta c,\eta cu^2)$
lies in $(-0.015478,-0.015475)$. These are the normalized circle
coordinates, before rescaling to $h_i$. Every pairwise normalized
projection determinant has magnitude $>0.0459$. Consequently the
five weight columns are independent, the pure Gram has rank three,
and the two saturated rank-one physical effects have rank-two sum.
No zero weight, height zero, axis contact or line collision occurs.
$\square$

**Corollary 20.2 (global original upper bound).** Let $Y,Z_f$ be
the physical matrices AC.64–.65 evaluated at the selected $d(t,\lambda)$;
in particular $Z_f$ includes the factor $1/t$. Then
$dB=\operatorname{tr}Y+\operatorname{tr}(Z_fM_2)$ and every
admitted original weak competitor obeys

$$
T_{\rm actual}\le\frac12
 [H_0+dB-\lambda(\sqrt\alpha/s_0)s].
\tag{AC.110}
$$

Proof. Substitution gives
$d\Gamma_0=h^TYh$ and
$d\Gamma_1=h^TYh+tc(h)\widehat n_h^TZ_f\widehat n_h$.
For its **own** $b\in[0,tc(h)]$, the absolute-value convex chord
therefore gives

$$
h^TYh+b\widehat n_h^TZ_f\widehat n_h
\ge|\ell(h)+bf(h)|+\lambda|u|.
\tag{AC.111}
$$

Integrate the full live Gram and physical failure covariance. Since
the actual report satisfies $s\le\mathsf V(F)\le C_s\int|u|dp$,
AC.110 follows with the original HALF factor. FA69/87 supplies this
reduction for the full complex/multi-Kraus class, with each competitor's
admitted time laws. No failure direction, low-sheet support or maximum
live-height decomposition was imposed on that class. Supported-zero
full encoders contribute zero supported height and are still admitted.
$\square$

## 21. A strictly positive response with an explicit lower bound

**Theorem 21.1 (response throughout the rectangle).** For the selected
root define $\chi(t,\lambda)=\partial_\lambda k_u(t,\lambda)$.
Then

$$
\frac3{1000}<\chi(t,\lambda)<10^6
\quad(t\in I,\ 0\le\lambda\le10^{-12}).
\tag{AC.112}
$$

Proof. Write $y=(p_0,\ldots,p_4,\phi_0,\ldots,\phi_4)$ and
$J=D_y\sum p_i\Gamma_{\eta_i}(\phi_i)$. The pure five-moment
rank argument of Lemma 10.2 and the independent two saturated
failure directions still apply. Thus $J$ has rank eight. If $\gamma_i$
is the current signed-gap curvature, put

$$
D_y=\operatorname{diag}(0_5,p_0\gamma_0,\ldots,p_4\gamma_4),
\quad \mathscr H=N_T^TD_yN_T,\quad
q_T=N_T^T\nabla_y k_u,
\tag{AC.113}
$$

where the two columns of $N_T$ span $\ker J$. Theorem 20.1 gives
$\gamma_i>0$ and independent weight columns. Zero quadratic form
on $\ker J$ therefore first forces every angle velocity to vanish
and then every weight velocity to vanish. Hence $\mathscr H\succ0$.
Differentiating stationarity and the moment equations gives
$D_yy_\lambda+J^Td_\lambda=\nabla_y k_u$ and $Jy_\lambda=0$,
so

$$
\chi=q_T^T\mathscr H^{-1}q_T.
\tag{AC.114}
$$

This expression is invariant under every invertible change of the
tangent basis. It remains to prove and quantify $q_T\ne0$.

Fix the two saturated atoms. For the three pure atoms put
$A_p=(\sqrt{p_i}h_i)_{i=0}^2$, $S_p=A_p^TQA_p$. Its diagonal
is zero and
$(S_p)_{ij}=\sqrt{p_ip_j}[1-\cos(\phi_i-\phi_j)]>0$ for $i\ne j$.
Choose the skew matrix with
$\Omega_{10}=1/(S_p)_{01}$,
$\Omega_{20}=-1/(S_p)_{02}$,
$\Omega_{21}=1/(S_p)_{12}$. Then $\dot A_p=A_p\Omega$
preserves the pure Gram and each null constraint to first order.
This is an integrable constrained tangent: the pure live moment map
has rank five on six variables, so its fixed-moment level is a smooth
one-manifold. Alternatively the map
$O\mapsto\operatorname{diag}(O^TS_pO)$ has constant-sum image
and rank-two derivative at identity, giving the same local null curve.
Positive first-row entries recover positive weights and normalized $h_i$.
Every failure moment stays fixed.

For $a=x_0$, $b=x_1$, $c=x_2$ define

$$
\rho_1=\frac{a-b}{1+ab},\qquad
\rho_2=\frac{a-c}{1+ac},\qquad q_{12}=\frac{1+bc}{c-b}.
\tag{AC.115}
$$

On the entire box $0.02<a<0.03$, $-0.30<b<-0.29$,
$0.12<c<0.14$, all displayed denominators are positive, and

$$
0.31<\rho_1<0.34,\quad-0.12<\rho_2<-0.08,\quad
0<q_{12}<2.44,\quad\cos\phi_0>0.99,\quad\tan\phi_0<0.061.
\tag{AC.116}
$$

Direct half-angle substitution in $\dot A_p$ gives the three angular
velocities
$(\rho_1-\rho_2)/p_0$, $(\rho_1+q_{12})/p_1$,
$(q_{12}-\rho_2)/p_2$. The preserved first live moment and pure
report signs $(+,-,-)$ give the exact rational identity

$$
\dot k_u=2\cos\phi_0(\rho_1-\rho_2)
 (\rho_1+\rho_2-\tan\phi_0)>9/100.
\tag{AC.117}
$$

For example its lower bound follows from
$2(0.99)(0.31+0.08)(0.31-0.12-0.061)>0.09$.
This also supplies a direct algebraic check of the orientation signs.
The weight bounds $p_0>2/5$, $p_1>9/50$, $p_2>3/10$ and
curvatures $\gamma_0,\gamma_1<1/50$, $\gamma_2<7/100$ give

$$
\dot y^TD_y\dot y
<\frac1{50}\frac{0.46^2}{0.4}
 +\frac1{50}\frac{2.78^2}{0.18}
 +\frac7{100}\frac{2.56^2}{0.3}<5/2.
\tag{AC.118}
$$

Cauchy–Schwarz for the positive tangent metric in AC.114 now yields
$\chi\ge\dot k_u^2/(\dot y^TD_y\dot y)>(0.09)^2/2.5>3/1000$.
For the upper bound, AC.100 and the exact radii give
$|p'_i|<5\cdot10^4$, $|x'_i|<10^5$. Since $\sum p_i=1$
and $|\partial_xu_i|<4$ in these charts,
$\chi<5(5\cdot10^4)+4\cdot10^5<10^6$.
$\square$

## 22. The exact platform endpoint and an evaluated positive interval

**Theorem 22.1 (first activation and quantitative right branch).**
Under Convention 18.1 let

$$
s_c(t)=C_s k_u(t,0),\qquad
T_c(t)=\tfrac12[H_0+d(t,0)\cdot B(t)].
\tag{AC.119}
$$

For every $t\in I$, the original weak value equals $T_c(t)$
exactly on $0\le s\le s_c(t)$. Every feasible larger weak request
has strictly smaller value. The endpoint satisfies AC.85's enclosure.
The map $\lambda\mapsto s_\lambda(t)$ is strictly increasing and
covers

$$
\boxed{\quad s_c(t)\le s\le s_c(t)+3\cdot10^{-16}.\quad}
\tag{AC.120}
$$

For each request in this interval take the unique
$\lambda\in[0,10^{-12}]$ satisfying $C_s k_u(t,\lambda)=s$.
Then the original value is

$$
\boxed{\mathcal T_{\log(1+t)}(s)
 =\tfrac12[H_0+d(t,\lambda)\cdot B(t)-\lambda k_u(t,\lambda)].}
\tag{AC.121}
$$

The system, root box and strictly monotone equation specify its value;
there is no remaining optimization or unselected algebraic root.

Proof. The eight exact equations restore both full moment identities
in AC.11: the omitted live $v^2$ moment follows from $u^2+v^2=1$,
and the omitted failure $v^2$ moment from $\mu=\alpha V+\beta W$.
Positive weights and the five height signs turn contact equality into
$\sum_i p_i|H_{\eta_i}|=dB-\lambda k_u$. Section 13's common
instrument therefore matches AC.110 when its request is $s_\lambda$.

At $\lambda=0$, any unconstrained original maximizer must have zero
integrated nonnegative certificate slack. A strict intermediate
$0<b<tc$ would require both endpoint gaps to vanish at that same
direction. Their disjoint zero sets exclude this. Thus every supported
nonzero low label belongs to the five listed endpoint directions.
The independent five columns and positive matching weights fix their
aggregate weights uniquely. Every top law has **available** contrast
$s_c(t)$. It is feasible for every smaller request, whereas FA72's
attainment prevents an equal value at any larger feasible weak request.
This identifies the actual first endpoint, rather than merely a contrast
of one displayed maximizer. The same argument works for countable
slack sums and, only in the stipulated integral model, almost everywhere.

The source bounds give $1/8<C_s<4/25$. Integrating AC.112 yields

$$
s_{10^{-12}}(t)-s_c(t)
>\frac18\frac3{1000}10^{-12}
=3.75\cdot10^{-16}>3\cdot10^{-16}.
\tag{AC.122}
$$

Strict monotonicity gives unique inversion and AC.121. There is a
feasible higher contrast even at the upper endpoint in AC.120.
Together with $t_0<265<9999/10$ and $s_\lambda<s_0$, this is
an original weak interior interval, not a maximum-contrast boundary.
$\square$

**Proposition 22.2 (actual reports and the isolated strong comparison).**
On the platform the unique aggregate supported law has available
contrast $s_c(t)$. A maximum-contrast report attains that value; a
general optimizing report need only lie between the request and
$s_c(t)$. On the active interval $s>s_c(t)$ every optimizer has
available contrast and actual report contrast both equal to $s$.
For this budget strip, every feasible larger request in the separate
strong component also has value strictly less than $T_c(t)$.

Proof. For $0\le s<s_c$, let $\gamma=s/s_c$. Independently
flipping the maximum report with probability $(1-\gamma)/2$ gives
$F_+^{(\gamma)}=\gamma F_+ +(1-\gamma)I_5/2$ and actual contrast
$s$. Retaining the original acquisition record preserves its TV,
cost, decoder and activity. If a report coin is retained as an extra
actual outcome, it is counted as a split outcome; it is not a free
hidden Kraus control. Maximum reports already attain the platform
minimum alphabet because the original constraint is an inequality.
Thus no claim that every platform optimizer reports $s_c$ is needed.

On the active side $\lambda>0$. Equality in AC.110 forces
$k_u=s/C_s$, and $s\le\mathsf V(F)\le C_sk_u$ forces actual
equality. This is also the global platform argument of Theorem 8.1.

For the remaining feasible requests reuse FA71.1: at finite activity
the only feasible contrast in $[s_0,1]$ is $s^\dagger$; in particular
$s_0$ and $1$ are infeasible. Let
$v^\dagger=m_2d_{\rm src}^2h_1^2/(m_1b_{\rm src}^2h_2^2)$,
$u^\dagger=\theta v^\dagger+\omega$ and
$K_{\sigma\tau}=\sqrt{u^\dagger}D+
\sigma\sqrt{v^\dagger}T+\tau S$ as in that supplier.
Its two high differences are positive. With
$H=(1-u^\dagger)N_{00}+(1-v^\dagger)N_{11}$, the supplied
four-ray law and triangle inequality bound every such strong value by

$$
\frac12\left[H+\frac14\sum_{\sigma,\tau=\pm1}
 |\operatorname{tr}(K_{\sigma\tau}\Delta K_{\sigma\tau}^\dagger)|
 +d_f\right]
<0.08569449380880800673445923202444725
<0.10278797993678910558710493681877579<T_c(t).
\tag{AC.123}
$$

The first strict rational comparison is substitution of the complete
positive-pivot source box in the displayed expression; its four terms
are $u^\dagger N_{00}+v^\dagger N_{11}+N_{22}
+2\sigma\sqrt{u^\dagger v^\dagger}N_{01}
+2\tau\sqrt{u^\dagger}N_{02}+2\sigma\tau\sqrt{v^\dagger}N_{12}$.
The last lower bound is the whole-strip zero-multiplier value
enclosure from FA's matching data. FA71.2 only subtracts further
nonnegative capacity losses. This comparison uses the existing strong
theorem at its scope; it transfers no weak alphabet count to that
component. Requests above one are infeasible by the original sharp
contrast law. $\square$

## 23. Exact HALF loss, seam coefficient and a rational right-side point

**Theorem 23.1 (quadratic loss and regularity).** On AC.120 put
$v_*=dB-\lambda k_u$. Then

$$
\partial_\lambda v_*=-\lambda\chi,\qquad
\frac{dv_*}{dk_u}=-\lambda,\qquad
\partial_s\mathcal T_A(s)=-\frac{\lambda\sqrt\alpha}{2s_0}.
\tag{AC.124}
$$

For each $t\in I$ the right expansion at its first seam is

$$
\mathcal T_A(s)=T_c(t)
 -\frac{\alpha}{4s_0^2\chi(t,0)}(s-s_c)^2
 +O((s-s_c)^3),
\tag{AC.125}
$$

and throughout the explicitly covered strict right interval,

$$
10^{-5}(s-s_c)^2<T_c(t)-\mathcal T_A(s)
<7000(s-s_c)^2.
\tag{AC.126}
$$

The value is $C^1$ and not $C^2$ at this seam: its left second
derivative is zero and its right second derivative is
$-\alpha/(2s_0^2\chi(t,0))<0$.

Proof. Differentiating the matched signed Lagrangian on the fixed
moment level eliminates changes of weights, angles and multipliers
by their exact stationarity and moment equations. Only the report
term remains, giving $\partial_\lambda v_*=-\lambda\partial_\lambda k_u$.
Analyticity and AC.112 give local inversion; use $s=C_sk_u$ and
$T=(H_0+v_*)/2$ to obtain AC.124–AC.125. In particular the coefficient
is an exact selected-root expression, not a numerical value of $\chi$.
It can also be written without choosing $N_T$ as

$$
\chi=-\frac{\nabla_Xk_u^T\operatorname{adj}(D_X\mathcal F)
                  \partial_\lambda\mathcal F}
                 {\det(D_X\mathcal F)}.
\tag{AC.127}
$$

The denominator is nonzero by AC.101. No extremization is hidden in
either AC.114 or AC.127. Along the entire branch
$10<\alpha/(4s_0^2)<20$ and $3/1000<\chi<10^6$.
Since $d\lambda/ds=1/(C_s\chi)$, integration of AC.124 bounds
the loss between coefficients $10/10^6=10^{-5}$ and
$20/(3/1000)<7000$, proving AC.126 without an unspecified
neighborhood remainder. The platform is constant, so its first
derivative joins the zero right derivative, while its second derivative
cannot join the strictly negative right value. This is finite-budget
gluing, not a joint asymptotic limit. $\square$

**Corollary 23.2 (a fixed rational point strictly beyond activation).**
At $t=1000$ choose the exact rational request
$s_+=0.1242167167887866$. Then

$$
\begin{gathered}
0.12421671678878638487626873539472489<s_c(1000)
 <0.12421671678878651209298880874023137,\\
8\cdot10^{-17}<s_+-s_c(1000)<2.2\cdot10^{-16},\\
5\cdot10^{-22}<\lambda_+<6\cdot10^{-13},\\
6\cdot10^{-38}<T_c(1000)-\mathcal T_{\log1001}(s_+)
 <4\cdot10^{-28},\\
0.10283536503869052<\mathcal T_{\log1001}(s_+)
 <0.10283536503869072.
\end{gathered}
\tag{AC.128}
$$

Proof. Use the same centre and $R$ with radius $10^{-16}$ in all
eighteen coordinates at $t=1000$, as specified in FA94–96. Its
zero-multiplier contraction is $<10^{-12}$ and its self-map ratio
is $<1/200$; it lies inside $\mathcal B_X$ and selects the same root.
Substituting this seed box and the full source box in
$C_s\sum p_i\sigma_i u_i$ gives the first strict enclosure.
Exact rational subtraction gives the next line, within AC.120.
Integrating $ds/d\lambda=C_s\chi$ with
$1/8<C_s<4/25$ and AC.112 gives the multiplier bounds.
AC.126 applied to the rational gap bounds gives the strict loss bounds.
Finally FA93's seed TV enclosure
$(0.10283536503869052157453180203846052,
0.10283536503869071116976210460262283)$ retains the last, relaxed
interval after subtracting the loss. Strict decrease is proved by
the loss bound, not by subtracting the wider decimal value endpoints.
$\square$

## 24. Actual outcomes and the simultaneous original instrument

**Theorem 24.1 (local minimum alphabet and all interfaces).** Under
Convention 18.1, on the entire platform $0\le s\le s_c(t)$ and
the active interval AC.120, every original optimizer has at least
five supported-nonzero actual low outcomes and at least six total
actual outcomes. These minima are attained by one common instrument
with joint fibre dimensions $(2,2,2,2,2,5)$ at each parameter point.
It simultaneously satisfies the complete complex-input, passive-reference,
five-labelled Borel-output, twelve-error, sharp-cost, finite-activity
and absolute-FIRST conditions of the original experiment.

Proof. At zero multiplier the unique top aggregate law was proved
in Theorem 22.1; on the active side equality in AC.110 gives the
same exact zero-set restriction for the current certificate. Each
strictly intermediate height would require both endpoint contacts at
one direction, which Theorem 20.1 excludes. The independent five
moment columns and positive solution weights require all five aggregate
masses. FA69's rigidity is about each existing actual low outcome:
different effective supported directions cannot be merged inside one
such outcome, whatever its inaccessible Kraus multiplicity. Positive
fixed high acquired mass requires a further high outcome. A finite
alphabet with fewer outcomes cannot carry the five positive masses;
in the stipulated measurable model the same zero-slack argument is
almost everywhere, and a positive nonatomic alphabet is already infinite.
Extra nonzero full-$M_5$ outcomes whose supported restrictions vanish
remain allowed and counted. They cannot reduce this lower bound.

For attainment use precisely §13's full-fibre constructor with

$$
K_i=\sqrt{p_i}(s_0D+z_iT+w_iS),\qquad
N_i=p_i\eta_i t c(h_i)n_in_i^T.
\tag{AC.129}
$$

The two complete moment identities have already been proved. For the
typed row-space isometries $J_i:\mathbb C^2\to\operatorname{ran}K_i^\dagger$,
AC.69–.70 gives $B_iC_i=K_iE^\dagger$,
$C_i^\dagger F_iC_i=EN_iE^\dagger$,
$B_i^\dagger B_i+F_i=I_2$ and $I_2-F_i\succ0$ on the entire
qubit fibre. Take AC.71's fixed simulator density
$g(u)=2/(1+u)^2$ only for this attainer, with current-survivor jumps
AC.72 and terminal survivor isometry $EB_i(I-F_i)^{-1/2}$.
The three pure outcomes have zero activity. The two saturated outcomes
have activity exactly $\log(1+t)$ and least terminal survival
eigenvalue $1/(1+t)>0$.

Choose fixed isometries $W_\perp:\mathbb C^2\to P^\perp$ and
$J_0:\mathbb C^2\to\mathbb C^3$. The single high encoder is
$C_H=(\sqrt{1-\delta}DE^\dagger;W_\perp^\dagger)$ into a
jointly counted five-dimensional fibre. Its rate is zero and its TP
decoder has the two inaccessible Kraus matrices $E[I_3\ 0]$ and
$EJ_0[0\ I_2]$. Thus its coherent complementary share is acquired
and counted before decoding. This is the allowed free JR completion,
explicitly distinct from CA10's certain-failure completion. Splitting
off a supported-zero complementary outcome would add an actual label.

Source-root TP and the exact Gram/failure sums give total encoder
effect $I_5$. Expanding the low Gram gives
$\delta D(\cdot)D^\dagger+T(\cdot)T^\dagger+S(\cdot)S^\dagger$;
the high supported term adds $(1-\delta)D(\cdot)D^\dagger$.
Consequently, for every complex $X\in M_5$, the complete outputs
are exactly AC.75–.76, and on every passive reference they are
AC.77 and the amplified live Kraus conjugations. In particular the
failure reference operator is
$\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X]$, multiplied by
$w_\ell\int_{\mathcal B}g(u)du$ and $P_f$; it is not the
unconditional reference marginal. The weights
$(0,1/4,1/2,1/4,0)$ remain five separate Borel components, with
labels $0,13$ individually zero. The terminal live map has its stated
CP effect $L_{\rm dec}=I-F_i$ and isometry normalization. No
arbitrary prescribed noncommuting time law is inferred merely from
endpoint coercivity; such laws retain FA68's full path-cost hypotheses.

All twelve specimens lie in $P$. Their complete stopped-cq outputs
are therefore exactly the original simulator outputs, compared with
the ideal coherent blocks and ideal $f_y$ of AC.3. Under the named
HALF minimax/error identification, for each sign pair
$e_{5,e,n}=e_{27,e,n}=E_*$ and $e_{16,e,n}<E_*$. The maximum
error is not substituted for all twelve individual errors.

Only the high fibre has dimension at least three. Its acquired
probability is $(1-\delta)A_y$, where $A_y=\sum h_i^2p_{yi}$;
$h_0>h_1$ makes the worst history $27$. JR's original sharp-cost
identity gives $(1-\delta)A_{27}=\mathsf C(s)$ throughout this weak
range. Every low acquisition probability uses
$K_i^\dagger K_i+N_i$, including future failure; no acceptance or
survival division occurs. Maximum low reports $\operatorname{sgn}z_i$
and high report plus give $C_sk_u\ge s$, with equality on the active
side; Proposition 22.2 permits platform attenuation when desired.
No hidden Kraus index becomes a readable decoder control.

The chosen jump construction is chronologically TP at every cut,
with absorbing first failure at absolute time $6+u$. Only not-yet-failed
carriers receive terminal processing; there is neither deadline
absorption nor later positive-carrier action. Necessity in AC.110
retains every admitted competitor time law, not only this $g$.
All rates and activity integrals are on entire jointly counted fibres.
This proves simultaneous attainment at the original mathematical scope.
$\square$

The five low projection lines, two nonzero physical failure lines,
five supported-nonzero outcomes, six total actual outcomes, hidden
Kraus multiplicity and joint quantum dimensions are different counts.
The minimum is attained without asserting that every implementation
uses exactly six: splitting and supported-zero outcomes remain admitted.
Both endpoints of $I$, zero request and threshold attainment are
included. No axis, zero-height or zero-weight degeneration occurs in
this rectangle; elsewhere those cases remain in the original comparison
class and require their own analysis. At $t=0$, $M_2\succ0$ makes
the class empty before any division by $t$. The strong fixed-source
four-low counts at normalized budgets $r=1,2$ and five-low counts at
every other feasible $r$ retain FA's separate scope; there is no
reachable six-low strong region inferred here.

## 25. Roof transfer, attribution and the unchanged larger problem

**Proposition 25.1 (an explicit full-pure-roof transfer obstruction).**
Let $\mathcal C$ be coordinate conjugation on $\mathbb C^3$,
$\vartheta=Q\mathcal C$ and $\omega_0=I_3/3$. For the payoff
$g(|\psi\rangle\langle\psi|)=|\langle\psi,\vartheta\psi\rangle|$,
the concave roof restricted to real $Q$-null pure decompositions
of $\omega_0$ is zero, while the roof over all complex pure
decompositions is $2/3$.

Proof. Every allowed real null vector has payoff $|\psi^TQ\psi|=0$.
The four vectors $(1,\sigma,\upsilon)^T/\sqrt3$,
$\sigma,\upsilon=\pm1$, are unit and null because
$\alpha+\beta=1$; their equally weighted projectors sum to
$I_3/3$. Thus the restricted domain is nonempty and its roof is zero.
The Hermitian antilinear operator $Q\mathcal C$ satisfies the
hypotheses of Uhlmann, *Roofs and Convexity*, Proposition 4.1,
§4.2, equations (51)–(53), PDF p.17 of arXiv:1108.3218v1.
The singular eigenvalues of
$|\sqrt{\omega_0}\vartheta\sqrt{\omega_0}|$ are
$1/3,\alpha/3,\beta/3$, whose sum is $2/3$. This gives the
full-pure concave roof. Independently, its upper bound follows from
$|\psi^TQ\psi|\le\psi^T|Q|\overline\psi$ and averaging,
and the coordinate basis decomposition attains $\operatorname{tr}|Q|/3$.
The constrained trace-null state section contains the full-rank
$I_3/3$ but is a proper subset of the state space, hence is not a
support face. The face restriction in Uhlmann's Hadamard-extension
proof, PDF p.19, cannot identify these two decomposition domains.
$\square$

This is a counterexample to unrestricted transfer of a roof formula,
not a counterexample to this source's particular height payoff.
The entire real null domain, rational saturated payoff, matrix moments,
allowed operations and physical whitening must all match before a
roof or complete-class theorem can supply an original finite optimum.
The literature hypotheses in §15 retain their stated scopes: ordinary
Chebyshev information-matrix conditions, compact generalized-moment
relative interior, Lorentz-positive maps, and nonsingular feasible
continuation systems cannot be inferred from scalar resemblance.

The exact selected zero-multiplier family and its rational data are
reused from FA93–100. The whole-fibre path minimum, rigidity, capacities
and chronological constructor are FA68–70/87; the original unaveraged
equality and sharp cost are JR34–42. RC and the static residual-height
results retain their original static scopes. The added quantitative
conclusions are AC.96–AC.112's uniform perturbation and report-split
global certificate, AC.119–AC.128's selected first endpoint, specified
positive right interval, rational point and loss bounds. Their tools
are the classical contraction argument, Bernstein positivity, analytic
implicit functions and a positive constrained second variation. This
is a repository-derived conditional synthesis, with no originality or
exhaustive literature claim. Ordinary source proofs and rational
inequalities supply no Lean/kernel or native certification.

The complete original finite-$(s,A)$ problem remains: evaluated
global roots, positive common weights and whole-circle necessities
for every jointly chosen oriented failure allocation and every
live-height decomposition, including below fixed-allocation maximum
contrast; all later contact, sign, zero-weight, rank, collision,
extra-zero and actual-label transitions; and all gluing and degenerate
directions. The present fixed rectangle does not supply that atlas.
Existence of the fixed-strength coefficient $K(s)$ is not its
evaluation or continuity. Its original precontact/contact values,
chosen attaining auxiliary family $\nu_\star$, orientations and
coefficients remain required beyond the supplied postcontact and
rank-conditional results. The selected measure
$\sum p_i\delta_{(h_i,\eta_i tc(h_i))}$ here is a finite-budget
attainer, not an evaluation of that separate $\nu_\star$ problem.

The published TC/SC limiting support, strict concavity/convexity and
quadratic results, JS full-class finite-product/common recovery and
spectral saturation, and FA strong/path/rank/moment/rate results retain
their precise completed ranges. JS's clamped limiting selector,
pointwise two/three physical-failure-ray criterion, critical strip,
sub-spectral uniform rate and compact-uniform spectral layer are
reused results. The remaining JS.58 root inventory, isolation,
ordering, multiplicities and sign intervals, next terms, critical
five-label/static-contact joint layers and other required uniform
joint scales remain separate duties. A limiting moment problem's
threshold values do not provide its full interpolation or every rate;
limiting three-line structure does not bound finite-budget support
or all actual acquisition outcomes. Weak three/four/five feasibility
counts, static support counts and global optimizer alphabet minima
remain distinct from the local five/six theorem.

Finally the mathematical instrument has no native realization bridge
for lawful access to the sole specimen, calibration, actual acquisition
and report generation, acquisition duration/cut placement, coherent
joint storage and every accessible-share charge, whole-fibre decoder
actuation, aligned absolute FIRST clock, stopped archives, source/epoch,
controller or permissions. OriginalControl remains geometry. A native
cyclic state-count theorem provides no quantum operation, acquisition,
resource or permission correspondence without such a bridge. The
quantum-first AURIC FIB ATOM programme through 2027 and all its original
output, competitor and resource requirements remain unchanged.

## 追加锚（本行以下为增补区）
## 26. Two selected later-contact problems at activity log 1001

**Convention 26.1 (conditional original scope).** Sections 26–34 use
exactly the experiment, competitor class and source dictionary of §§1–3
and Convention 18.1. The original nine-coordinate positive-pivot source
root, its isolation in CG's radius-$10^{-24}$ box, exact ranks and
root TP identity remain inherited ordinary mathematical premises.
The complete-output HALF minimax identification and precisely CG17's
averaged-live and preaverage support consequences are separate premises
from JR34–42's further sharp jointly acquired cost and unaveraged real
supported equality face. The latter is not inferred from averaging alone.
The source enclosures below bound expressions; physical normalization
and minimax identification are invoked only at that isolated root.
These are conditional analytic results, without Lean/kernel certification.

Necessity retains arbitrary complex encoders, hidden Kraus multiplicity,
all admitted original time laws, freely chosen other binary-effect entries
and JR's free full-$M_5$ completion. It uses FA69's actual-label double
rigidity, whole-fibre capacity and FA72/87's correspondence. The extension
is only the finite/countable and expressly stipulated measurable
finite-dimensional-fibre, measurable-Kraus, integrable-effect/live-Choi
class stated in §1; no unrestricted disintegration theorem is asserted.
The all-twelve-history, one-specimen, contrast-inequality, sharp
worst-history joint-cost, whole-fibre activity and chronological
absolute-FIRST conditions are retained. Static spectral signs and
strict-decrease results have only their static scope. The first seam
in §§18–25 is reused only on its stated strip and tiny active interval.

Fix $t=1000$, $A=\log1001$. To distinguish circle coordinates from
elapsed time, write $(u,v)=(\cos\phi,\sin\phi)$ and use elapsed time
$q\in[0,1]$. Set $z=u/\sqrt\alpha$, $w=v/\sqrt\beta$ and use
$\Gamma_\eta,H_\eta,B$ from AC.46. Write $c(h)$ for AC.9's capacity,
$\boldsymbol d=(d_0,\ldots,d_7)$ for the common multiplier and

$$
k_u=\sum_i p_i|u_i|,\quad \tau=k_u/\sqrt\alpha,\quad
s=C_sk_u=s_0\tau,\qquad C_s=s_0/\sqrt\alpha.
\tag{AC.130}
$$

The multiplier $\lambda$ multiplies $|u|$, not $|z|$, and is unrelated
to the original source-root coordinates. Its physical-strength multiplier
is $\lambda/C_s$. All contact systems below use AC.81–.82 and AC.94,
with the following six indexed chart/sign choices:

| $i$ | $\eta_i$ | $\epsilon_i$ | $\sigma_i$ | Chart base |
| --- | --- | --- | --- | --- |
| $0$ | $0$ | $+$ | $+$ | $0$ |
| $1$ | $0$ | $+$ | $-$ | $\pi$ |
| $2$ | $0$ | $-$ | $-$ | $\pi$ |
| $3$ | $1$ | $+$ | $+$ | $0$ |
| $4$ | $1$ | $-$ | $+$ | $3\pi/2$ |
| $5$ | $0$ | $+$ | $+$ | $0$ |

**Definition 26.2 (exact selected systems).** For $n=5,6$ define
$\mathcal F_n(X;\lambda)$ in the unknown order

$$
X=(x_0,\ldots,x_{n-1},p_0,\ldots,p_{n-1},d_0,\ldots,d_7)
\tag{AC.131}
$$

by eight moment residuals $\sum_{i<n}p_i\Gamma_{\eta_i}(\phi_i)-B$,
followed by the interleaved pairs $P_i(x_i),P_i'(x_i)$ in increasing
$i$. Here $\phi_i=b_i^{\rm chart}+2\arctan x_i$, and

$$
P_i=\boldsymbol d\cdot\Gamma_{\eta_i}^{\rm num}
       -\epsilon_i H_{\eta_i}^{\rm num}-\lambda\sigma_iW_{\eta_i}.
\tag{AC.132}
$$

The denominators are $r^2$ or $D_cr^2$, $r=1+x^2$, all strictly
positive. The height numerators are $L_c$ and $D_cL_c+1000N_cF_c$;
the report numerators are $rU$ and $D_crU$. In particular
$F_c=-(11/64)(d_{\rm src}W_c/h_2)^2
-2\Delta_{12}d_{\rm src}b_{\rm src}Z_cW_c/(h_1h_2)$, with the
physical negative cross sign and $\Delta_{12}=(\sqrt{37}-\sqrt{59})/16$.
A prime in the selected equations is local-$x$ differentiation.

The selected six-contact point $S$ is the zero of
$\mathcal F_6(X;1/4)$ in the box specified in §27. The selected
activation $D$ is the zero of the twenty-equation system

$$
\mathcal F_D(X_5,\lambda,x_5)
 =\bigl(\mathcal F_5(X_5;\lambda),P_5(x_5),P_5'(x_5)\bigr)=0
\tag{AC.133}
$$

in its §27 box. Its order is $(x_0,\ldots,x_4,p_0,\ldots,p_4,
\boldsymbol d,\lambda,x_5)$ and its sixth weight is exactly zero.
The unused contact is part of the equations, not an assumed extra
outcome. Both systems have twenty variables and twenty equations.

## 27. Rational source enclosures, root boxes and contraction certificates

The following exact data specify the selected roots without external
certificate files or rounded root equations. Decimal centres are exact
rationals. In the source table an integer pair $(l,r)$ means the closed
interval $[l/2^{224},r/2^{224}]$. The table contains the source quantities
needed for every subsequent inequality; $\alpha=1-\beta$ and
$s_0=\sqrt\delta$. The source-root certificate supplying these intervals
has SHA256 `cfea57666a799df3d74adfbdc624c32705219e214cfb85840b5d3d125ad5d346`.
Its role is only source isolation/ranks/TP and these expression bounds,
not the later contact systems, minimax or sharp-cost theorem.

| Quantity | Lower numerator | Upper numerator |
| --- | --- | --- |
| $h_0$ | $26537788820506109500788498850443291999899441414357450708533697655768$ | $26537788820506109500793183315073538792668688684001205079732940054331$ |
| $h_1$ | $19041394653590742992836842417055357808127410672381937576282066738318$ | $19041394653590742992839410055472468226237891451663919566364482743060$ |
| $h_2$ | $21824004785988993361054584934895991870094398276315525145506200547608$ | $21824004785988993361057348440025413753058042469208985303844669006803$ |
| $a$ | $1770311394972945197641994965733434776804318798358636960993665423441$ | $1770311394972945197642330191383860313598676849494811590399527112584$ |
| $b_{\rm src}$ | $3935965654294995608601979521892857651473674590095072143984588712921$ | $3935965654294995608602313422828891500221393677289956783118602628225$ |
| $c_{\rm src}$ | $417790356983612701857377130657326048451791786364520663159403140999$ | $417790356983612701857967962172137068830255220590298423542851403047$ |
| $d_{\rm src}$ | $2663205433690388662341049091689729175826547547021472884789707223172$ | $2663205433690388662342459064972096088182130849082266016544667607076$ |
| $\delta$ | $423549146495968554146011830551315873699107220910873798103439460242$ | $423549146495968554146345884167486240808334297711005281549257059179$ |
| $\beta$ | $3296842078597743037413473231959988404966987722955647639968047305372$ | $3296842078597743037414228158069975732764908643825242059562820404625$ |
| $N_{00}$ | $2178274649664917026219840788436610404284546028134588617028215950658$ | $2178274649664917026222049243107662090560048935982720049984373276804$ |
| $g_0$ | $34221372174431290786718999261791211913632513952393836659553436688$ | $34221372174431290786780685200389826628501112496695844777618146828$ |
| $g_1$ | $78783570610947918076504457783823376875791541957489725211853654103$ | $78783570610947918076528781413699780090811566031886072291211212877$ |
| $g_2$ | $45217132639885265280065628896983675495273546961325526453963593339$ | $45217132639885265280113507252983523546922593561790580491093661556$ |
| $x_G$ | $63910117293406567136997332254455271417331233917251423202613394599$ | $63910117293406567137040175213816913730280255820235874754516426984$ |
| $y_G$ | $59527865208926896968702198521424412882206778336312391207706909528$ | $59527865208926896968773639959878055405231936608490807444733614519$ |
| $z_G$ | $-2740627279025051691705416351839235775900350270525561152827355761$ | $-2740627279025051691701021642264762102188060554422868821033090259$ |
| $m_1$ | $13395056598782546673904842458375183527737029361412185934273944851861$ | $13395056598782546673906662453967195540019733666091401589339664139139$ |
| $m_2$ | $9286998735773460367948153511490550124076700197961256553923028397389$ | $9286998735773460367951141007906400979909044212876537994791222399466$ |

Each row of the next two tables specifies $[c_i-r_i,c_i+r_i]$ in the
coordinate order AC.131 or AC.133. Write these boxes as $\mathcal B_S$
and $\mathcal B_D$, with radius vectors $r_S,r_D$.


The $S$ box:

| Coordinate | Exact rational centre | Exact radius |
| --- | --- | --- |
| $x_0$ | $0.089915341881929305760705090170788889246518603013156863496553096941973$ | $\frac{2708052700357549}{500000000000000000000000000000000}$ |
| $x_1$ | $-0.22574704931878158462583408729341298761372875026407680732482726099239$ | $\frac{1}{1000000000000000000}$ |
| $x_2$ | $0.15123801708581888971733645734797458922851140806037489606663465438766$ | $\frac{1}{1000000000000000000}$ |
| $x_3$ | $0.15770144425230728474684612406488617579434553351292120855124961637748$ | $\frac{123382645171699}{78125000000000000000000000000000}$ |
| $x_4$ | $0.26133142654763628061990269461456172080684190068897628495263684050447$ | $\frac{7643395066864083}{2000000000000000000000000000000000}$ |
| $x_5$ | $-0.069791976001318501401991839333803553104540068336095309689448317917247$ | $\frac{254103498513593}{40000000000000000000000000000000}$ |
| $p_0$ | $0.25054404174195016134830889399503319886996487732830431010856839520739$ | $\frac{5486278198335937}{500000000000000000000000000000000}$ |
| $p_1$ | $0.22381409262209222544748281037701456393827758536893047677233844965931$ | $\frac{1}{1000000000000000000}$ |
| $p_2$ | $0.27528793923596088193045211831992361635038094007056955385080855119058$ | $\frac{5103033915121747}{5000000000000000000000000000000000}$ |
| $p_3$ | $0.036372335864799412643713623601075478438234250924765241915256242105494$ | $\frac{1}{1000000000000000000}$ |
| $p_4$ | $0.055792157538078948006713323797161150457377692596622844358879730244198$ | $\frac{1}{1000000000000000000}$ |
| $p_5$ | $0.15818943299711837062332922990979199194576465371080757299414863159303$ | $\frac{177534869593453}{15625000000000000000000000000000}$ |
| $d_0$ | $0.13935722546768914055376352858982176103723779416148733432634662935503$ | $\frac{1}{1000000000000000000}$ |
| $d_1$ | $0.0032770303897412742420257048971060705564771828150558352722315462466535$ | $\frac{1}{1000000000000000000}$ |
| $d_2$ | $0.0075930716495027380842159856299152205709556249613653594311959099016927$ | $\frac{1}{1000000000000000000}$ |
| $d_3$ | $0.11704492704926548319611436581084924519708948213386003545837005232783$ | $\frac{1}{1000000000000000000}$ |
| $d_4$ | $0.0044781537395288282581674686222698344468398486054307440847002097749592$ | $\frac{1}{1000000000000000000}$ |
| $d_5$ | $20.928462944424460825865748611325874770152711455391972863960804808785$ | $\frac{17875395940703217}{100000000000000000000000000000000}$ |
| $d_6$ | $-16.545760244424116439409971218031321735872458945749497613336533265436$ | $\frac{77991958149829}{312500000000000000000000000000}$ |
| $d_7$ | $-11.707958064272696938651356035645782034758380112634330029753558507453$ | $\frac{15029209796976267}{100000000000000000000000000000000}$ |

The $D$ box:

| Coordinate | Exact rational centre | Exact radius |
| --- | --- | --- |
| $x_0$ | $0.026852509279830982801137895473304120859173660651133366029798845900503$ | $\frac{13922483850834169}{10000000000000000000000000000000000}$ |
| $x_1$ | $-0.24912465604010272264523633749869606787774244986461798965991607099632$ | $\frac{14476410544080053}{1000000000000000000000000000000000}$ |
| $x_2$ | $0.15639610586877108029737289481243067324183956310179319928270077301745$ | $\frac{2608835203511191}{250000000000000000000000000000000}$ |
| $x_3$ | $0.15519431474002212990881824017503319606279007514516225220968814114325$ | $\frac{7555695013153903}{2000000000000000000000000000000000}$ |
| $x_4$ | $0.25751605122380976967093899733372963239337619582914080501701880477151$ | $\frac{35306538587711}{5000000000000000000000000000000}$ |
| $p_0$ | $0.40372007831357148483813098107475447992513620682734581397472783980978$ | $\frac{1}{1000000000000000000}$ |
| $p_1$ | $0.21981666410055560632383924129174396986731526119178856685736009516741$ | $\frac{11827248669410189}{1000000000000000000000000000000000}$ |
| $p_2$ | $0.28419980478646447017451428782343813947588941120831440361334836964173$ | $\frac{12263222782787813}{1000000000000000000000000000000000}$ |
| $p_3$ | $0.036286490774106003819355159974779369025049061725704562564024660627154$ | $\frac{1}{1000000000000000000}$ |
| $p_4$ | $0.055976962025302434844160329835284041706610059046846652990539034753924$ | $\frac{1}{1000000000000000000}$ |
| $d_0$ | $0.094348743674920060563680539726917531460264924355519441124473380409065$ | $\frac{4066414972819613}{100000000000000000000000000000000}$ |
| $d_1$ | $0.0032381908120145737136009615122037251785603809000267633213481254731177$ | $\frac{1}{1000000000000000000}$ |
| $d_2$ | $0.0077354166488794354150104418635345094023869829283708517122305598367066$ | $\frac{1}{1000000000000000000}$ |
| $d_3$ | $0.068793148982652264114454705363760422200033370046530754001149573019123$ | $\frac{2423788209149049}{50000000000000000000000000000000}$ |
| $d_4$ | $0.0042711626885214764274137399503304237103478109823158661097696109116146$ | $\frac{1}{1000000000000000000}$ |
| $d_5$ | $21.273402004513098475322880695289237328696753964654646551967800572931$ | $\frac{2302781229265241}{5000000000000000000000000000000}$ |
| $d_6$ | $-17.001812285310939276654542386579924925386331580739881338710146460948$ | $\frac{6298632295176107}{10000000000000000000000000000000}$ |
| $d_7$ | $-11.472344568119663524884011884024286195212754565892009101101214354928$ | $\frac{918319054337261}{2500000000000000000000000000000}$ |
| $\lambda$ | $0.15672072828366031990558863805077139734865378925531746474421328075332$ | $\frac{8900537138292257}{100000000000000000000000000000000}$ |
| $x_5$ | $0.0040051118654759391118197019828709821776351689727822861221197665803536$ | $\frac{21081539730263803}{10000000000000000000000000000000}$ |

For precision the fixed rational preconditioners are given as integer
row vectors below. In every displayed array $R=2^{-241}A$; row and
column indices start at zero. $A_S,A_D$ use the full equation and
unknown orders of AC.131–.133. Thus their specifications include every
matrix entry, including zero entries, and require no numerical inverse.
The two arrays $A_5,A_6$ in §31 have the same convention.


The integer matrix $A_S$:

| Row $i$ | First column $j$ | Entries $A_{i,j},\ldots,A_{i,j+4}$ (last block stops at the matrix width) |
| --- | --- | --- |
| $0$ | $0$ | $(8374449400545362128033897020891271576719055217544279155536043475340761901,485518776585775783124628705464135031834692828753889681638366802018415675,-814342706007207310883272375949488292378422006247211809176662531387612047,-9078642650448769367652564611243470855653025902285000843751931849708858481,471875181149804124228185379250296800826155203298562750449113682606888993)$ |
| $0$ | $5$ | $(-135920138754128120280981672608054174747845497461536550448055899109192605747,156913649369811695353322346425563458510213990507404254132890692757998205213,-30426861278167216689056649061841019434458841521831249426967373114845087559,-738033274977264738296503538948648964091516838587743776687641681819615784969,84517446325684696915224903465141450624786325306548709262969722847405784001)$ |
| $0$ | $10$ | $(-12626750164181473724030875660273147633400923537658703482685697720937412153,9018687709083371096253468055347353192822562145723959185668737322411442801,12477324426319151437268825700143180517951063723087279177202967281697761777,-11970710534005847522611890179557062422504025612041071375778909762806891447,-608676252479084490960848632065597400688033316159314700011161759643926663)$ |
| $0$ | $15$ | $(357761309650130871612299212920263604090129199535719162858463109682064807,-673721883041586237675148368245689189547408722740035958449135641656161229,386712706342968150141923776304811836225561247884247130326344350535601671,738604440000900328158434403015016171192397875674972580946761489655767653835,34108847658190419799660316961891003792352425655283968195047827393512560177)$ |
| $1$ | $0$ | $(-1732593113387906604464743089141276947081423992294628887390757362661757679,-100449169670576258148075305803436089951205181824112260615635754344584651,168479681096870391472427121915370055871422327179368065341653847162569247,1878283930410150270663074799897311696029014328772974045475198214807973959,-97626440872110324368473345028918938211116219533398932139105329127646915)$ |
| $1$ | $5$ | $(28120570692181292151187804669110569455841510903532528256413831130528710365,-32463926318188247511055777581107401316393927285723354657733338909790999293,6295025235823695941387613524935307973498151950811851714235932551463193033,-16632012855646728917917795260171192687784050517898746707029618479898136737,10972856435565743063000271021696961567709659382245596439660523462086885559)$ |
| $1$ | $10$ | $(33143723255640869576277164584627573195112157685845722719526382037023042547,10164869733573078143477833771852915633158854687820000577596695413801925271,-33188521511792265073343583594841971642834067284919455827409074001985145745,2476624986500956579032160532913023090589069162846469650702432455307498847,125929268049472416693586100939229476109875618371672128581512331995208233)$ |
| $1$ | $15$ | $(-74017377344961793920333710606504725041429863493876269951125620920813991,139386584008802872690517587474953802486930679869087357972215716304221837,-80007143135379572524122720234312124883722878382943873414419161699804247,17004193208775671232273533699297347534920358247899397214967965153364207889,-7056792838742262757612853825327255538640405945485390256879469743867767389)$ |
| $2$ | $0$ | $(1771099586217453639054867339576173216657025116906905309865835708690009741,102681628747541675541696370588662274955816687180158128295278177930960123,-172224102226307781296251616726992960709970868614973924899572122818747695,-1920028347246188063174417475500276673254291139821380237885437404781442247,99796165468057997287922991491201286221157084768446422482895723065963961)$ |
| $2$ | $5$ | $(-28745543735732461110854881222241385706058225814107689078070768757714428179,33185429414935150507402272919033021382752259474902352419273552225613300155,-6434930685251791303969915351363916757229019571811996450891283744068539607,28045637993093725534862947795572865655213953106305981854301388562372758061,-11216725578836448280920337813753395157207504753571252732538201229675017615)$ |
| $2$ | $10$ | $(31080615926288629362635531103416879468596016622849295952361364478513084321,1907348567744859474115483349402174415261428971829435667913185844775238389,-31035288109312240780230841527381685266217148802270724429732107097326132171,9671274832951187238542791161982476299878238509810517890729146306619927419,-128728016296318358172024245606978998789272076177253940218922738012119005)$ |
| $2$ | $15$ | $(75662396078803423771016952342122541642964648357775228630090680191872039,-142484417925182218682543476073838754289928327577728940136810052475508121,81785282999555762318187690536988089085403708727682268628912138226887355,-28163733064685498965940037281774919731531586695799329720264401820155034879,7213628393269792200569846623498913912074299016212982790713964968527815315)$ |
| $3$ | $0$ | $(-18909812561667828451088997111104319870571052542319737891443210409475423,-1096319127536839367350391195065951499653295952664663243519590393983099,1838815568048550131621445501150132502151507437560026234892999304014953,20499906635434393385608311836619972285092277993428675300377479174647507,-1065511390810332982944249138110911852515349684609026190873309344845517)$ |
| $3$ | $5$ | $(26500180825486693936078765430845774156956843907498076429795378741911810569,-41650122653083701201645049585164079704091523992289510086145004774738667243,38289047612104747240624568951600873876986872449826854661277205969978817893,-748616772411901778821437966815501041858982130092903970387708355816213097,119759600138837225765594521358278299274899471628796787558447936250571263)$ |
| $3$ | $10$ | $(-129083372365470027391249362350504916010100762225120880332444156364055111,-20364526188417585931948344375670758079951248590021915021006471496689703,176471401502290497618856018709701181272880785045049270018277680869840569,27030301528037398069677099643857886600455170654683251861430527577992269,-1512871676668255020607555340265166927563735050960838497116358028468926931)$ |
| $3$ | $15$ | $(889219762021227763734089729178512250539700978807437930196759413015453635,-1674543323571248585793080992792469308136623019051462513933641606295293799,961178784372088357790877469588635552976319271537166541810466979430030573,658667314495598593380982566791485530478565167094623546119691671378534905,-77019023587253418135745402724671625803327114358693534368656642089172991)$ |
| $4$ | $0$ | $(-28723492008482133017804371125451953830298110356404582969939209814350969,-1665278997126828752272711684249212236458772682632834756997098212452755,2793110936539956569173717419987972292288041942416370634667441247735131,31138801746303267978315376046800715504107008447685311494371653206735649,-1618482881259608345097683460309472543645177955467980603877662539476233)$ |
| $4$ | $5$ | $(-157145694176991776823854567146212206663647571273379607370222399500192719287,247949689176818404807055297219331236183174582097527099363514008771830271033,-229877642430004828683181318582292771677596499341613921779272610321098099055,-1137128557444168189632721704710300971709717608094988077196952798789181113,181911581952957734138067925545557449110890614140954083564615053112358541)$ |
| $4$ | $10$ | $(-196074138888264248106454997146962480850472441479618249564088650603347157,-30933162521942334557656457283028605427611636467176017510644008579303819,268055268884675437919932885657535868268212598210012582892075319727647387,41058294332398522769207142088945108036229112306253996354736960581586451,-2298011012691227881259736158646319223566050734081430583222536329452864577)$ |
| $4$ | $15$ | $(1350700682246655901202762956600067693341864295778342933204823438626753219,-2543585856052166206143244113641006658620634860248969724952378817461939069,1460004483999983882130150623802967916014593693021726035323377080262367149,1000497772384796994422827332877766864321795997566723501103500943283912917,-116989806286818716798041449716782380921025992371978841368342690366171431)$ |
| $5$ | $0$ | $(-8475727676736022488285581746704195977857517106764593720253846304604289555,-491390506463038341208639507253638146060816201008269817620626340856238019,824191141593608574460948926129369298095199085408278304938262215458570669,9188437245151148422255823119042114018859395981585564662580866957187525033,-477581909155217294214289579327982081378026820851112232871589034272857553)$ |
| $5$ | $5$ | $(137563919341269408739477262702339394710741234142952563613335147380356006167,-158811319671327316231434673655971373020855605511795948523126118726938155619,30794835327893333532963974750903786004301491479457956680565511259971515959,-985149245809024439053149447826992949039926020575316914889141130322569680959,53678467416921630269294824097851459382053944589240834061831710542978740075)$ |
| $5$ | $10$ | $(3334174039596880640534884463185530404530546687045103329880709674358874641,-9127757225297580621364677051131928669004813899495204331504304529139188885,-3328588864261105545876844242548274356503847454209171851691573820666819739,12115480998268553470232092031837207141655839627167992946257982831637954737,616037414826696065008267623572047946651637727802991305719391590159164937)$ |
| $5$ | $15$ | $(-362087976036904755283421012340365471463379354572732842875121924022974149,681869689265352309083522584943273952511599633134587559463054812037804381,-391389502918620074809551273311504120519322479655503830766649064306018521,984590838291382324264295361552989820220730514897428417598186009985588944567,103033147663111826262051759016192026352648846712071534733891629596092726771)$ |
| $6$ | $0$ | $(-3725796525594682861200469811445454841663306848510488091747920112789490537,576480314668101722425428563604740422189403719903073711322219704523906531,5796494083989247179983545829683629703998393437107068444813525345434029667,4825870580999017757644487034851772065855452564281673726196361651882799011,5616965247472429471674302463412198240443852409827130956734461075263916495)$ |
| $6$ | $5$ | $(143717533245778689664108914676122404084222566622791955887678930241119876699,-173530076311640970262879186138559044268249012369183982013484706923570317161,-41055769585312979279703902047095992823522560784374943881885834606197694233,2071842293872614402514028810302534366140603872314457789869957155040003383407,-177354966378440608354236009168054956555931080917070769499347760575959596899)$ |
| $6$ | $10$ | $(21789048493419149320089586950052931051139364673789429217466263755699219557,-2618771228235089410179093461872592235735229050233279045832501366181132925,-21597130019681353924851437246325429094176053300955562356545861174694040345,6428956185698552744301039903244275455065455151760886901077369114497207565,898869628339236670305651281283668703982757093191060421346068342527807925)$ |
| $6$ | $15$ | $(-528328112242923348770892388611150375899863878609707935411420173623474163,994926508381252630984483398765449464376386501746898556301486200019882781,-571082418952279778475983233051420554869591938873768624415192900164193697,-2072044242432981087148561995085625373420950205951904471382924663065920605441,-153789699966376286215437769100675478661558036895301666723330179189955054463)$ |
| $7$ | $0$ | $(985178965450367346814859296799982982001736772462401924677930915315355141,-749242811427082583642996648852326262951798630677976549178691126091413917,2513855064329833228908034119452973159640888494541864561187228197201759447,-252820814106614440177353113283552047165921751550227421152516602965653821,-2572942353118462005480314061775104134448093908203929464035059617325966687)$ |
| $7$ | $5$ | $(14836351502858279112189094245519159394895724630709012212970644909190657277,-19488114527038608040281947192860236946917257312203877465824366736116136651,8387719041612276938856136416242781433879085275607055811384503566973783537,28107076753042511441159920419508866005031353639928571957931854656224748399,-5548488222130249358896622977591666317887951186946162501521610250642525695)$ |
| $7$ | $10$ | $(37412852428470183792000274404814048374819096731370724158783802442875766887,5463312970164114886529686693233194503999228260451447954368464057420069763,-37400140981652128404631343018226926561148727758633489781294250580388436873,8556225940940490371428249266022019558932007092682246838361849402740261203,154436529378864301826682598378498593137429875217957041671564526725449221)$ |
| $7$ | $15$ | $(-90773074821580902855556861509718677907952172920229495138880420460095649,170940247725716906198980434666671750857296729422635369560377944375675333,-98118774949854197385463562245505576410922088450589359666706504970826109,-28042584664795335378996470763778725911550928063204636797429903576608604091,1933956125437270438383587579745538372007082400235673891658329390544000213)$ |
| $8$ | $0$ | $(586258728507404636463058792322054200103277040286413182613902373148169355,-1104439297316260716698087753023690476258624324851644457379217366623396695,-2439387611197649086661342982341732218387858905162943992807870880291881105,518477315563347797279743840717099358879329215239447271747784971444964631,2470535495477812929137068288379481410077721479370456344554591194489603417)$ |
| $8$ | $5$ | $(-30884640248558802094108855147444673372309422317369015697011320456416480129,39004844217268039995035538236167013971541662612904115193812776530033252007,-14692847954066538337967568876287577278763446015729312259774165593088181331,-18817541803259577661773160045299233673047128480516582065195177816246410805,1392291928027660917343340366831357588653125072091872002834417332552686351)$ |
| $8$ | $10$ | $(-36412999614410802839287920881258190487709627214875346150482786790055997575,-6725769804235523423633348483196152789151516450596597714897896097675861687,36418566772380563174667672973744918073374184945867598926089069704956422593,-6969040724923690759347011950194749749742255311504734590982788080066482273,-252316033887466760988991933031215863839115391266754973327121240205880115)$ |
| $8$ | $15$ | $(148303657916091866317903228145668985869579473978775026536467868921944871,-279279555888522305942182519997099749699984388987682821719661289265522437,160304950161825466740662934407246970469058887706851808513158046731945349,18665158640085129748673096268695117274830880004544138573423986740759477527,628882885228370391176619319280220427521131924205489829174047366336280947)$ |
| $9$ | $0$ | $(-651313956510135216588688186188260842958693424679390720642920962638161,-37760710013657586099719035497735746565575426190651292344688164321807,63334643800007166411307034060181936870918731908140062150469641351589,706081842708414739563634954543048307185809790126394283209894633554929,-36699593789843799396250201202039965509717020018277551041618531537829)$ |
| $9$ | $5$ | $(5750775719415004982232250773545064984406602757382416722725810925974792455,9101259089645177841177411778768462628109319441726245890629227803451513155,18567455576138453999021638864261670785502539667667034167741239263313060951,-25784737440382046265876319419832868117926314544420010735595753535611099,4124900695981207841765124946936429573470144762812714633905628146600741)$ |
| $9$ | $10$ | $(-4446041001244599422020731418266987328952770344923166301102748245534357,-701418910471880152583849463305144738498917963043129867000937847369327,6078235114627069060479507635195068755224241140500354138818433752697579,931009367569068461761050712310471466517830841584860103311351198833539,-52108101770418385515285921303315258106441216338306820665620101767546563)$ |
| $9$ | $15$ | $(30627550617982710790047309883435376752681811241814134099794079286781133,-57676586368375236482121407330346348881482834660464616450300786765253581,33106047715777664131269593448639717317495898385943890513236767880940733,22686592647547454743637017589723910435410362330794416348404884789988965,-2652779598717348149665532369001982617088469171687977531884044446463665)$ |
| $10$ | $0$ | $(1394789970911921897994071724429188409274859280436872151200743433681795,80864626183921489406653849795980650079696821069014669456281734873527,-135631249876578190794226194811299392641376366380893626128280204974977,-1512075494481409588603391948168745129649359596965446793631458678081125,78592243944674373140747137134351014661453633509980521573747902075307)$ |
| $10$ | $5$ | $(48530961301791251591834188321877090807764151671012420688939485019333808595,-48661448860910807815792756559731784723096043025901391981687452686971159719,-15295342105255400226093905020881729861357134045794245876740617681618337481,55218060084487642645914592635655658570399043040838109413134852887488899,-8833482016245825717122738168345807884985617894775390398820594709316997)$ |
| $10$ | $10$ | $(9521204538632771442434931626962824500502169570234249470564977389479853,1502089816985092752824599915518797793353682906884790009397339262050925,-13016551071855599571952506907144059949559243776800984244619309810165667,-1993758180261228029203257182937247880591077500324734450438494144147001,111589590590181589664719147362539042488174467392726865421915557534043577)$ |
| $10$ | $15$ | $(-65588952929023811713864496178629913535555944904892176579887994991255909,123514510043810493474922261546215866715540379253104826394013528620261925,-70896658775620254279431566706017319203419987163047539353376861031091031,-48583377621005934250734483263368132236369587210887726459638064824384535,5680932125508863394448312294736770534072611285238482269484694538247985)$ |
| $11$ | $0$ | $(5687309485179277750407741340271013763646944663657153419268741404608471811,1277158690159071314012348903456978072117505114231668931858577194635261015,-5870889240515354751205854047634119527795652568851516259628904851811469471,-5090721088803978119897838005291693680746396478164054524281208456385041847,-5514600282481935225904801186952507827122631717607149540224524781853862999)$ |
| $11$ | $5$ | $(-181950981521284423256255592869619045898979623364526789815303550640969501963,193573536392677168282740939876215589338611330652658890376554522013172848369,44088785026884186905887600663760847744261515902624412039274875049203890903,-2081161262145041441889795608949959821263040570202366197861371370986000619515,181515871253863461413664649392036674663477422505057022673799868461671907369)$ |
| $11$ | $10$ | $(-22793976471015918444822354673817484775420383589510118308936741637932555225,3880427391399984734682514501383336867832662475434587146219537004810504297,22585642544910147685326580290079386573144931116357753841856842923264691361,-8015078652902660196814835012600918487841133686279659274109303293981318085,-860471612650397415292775172690175217662804828196682534446807084842143599)$ |
| $11$ | $15$ | $(505758931459453486232363208270394604721110711214240446493926640859385697,-952425123893882488234082167650890983367756386774491314085915596974442937,546686854800151099268945834147056762697379228394609824408881451570539855,2081447565242664751258392467046382626279471213235445062917041813068085620225,151223832803183853870632779421723985074112838428746952497760201783902102825)$ |
| $12$ | $0$ | $(-326004145609259251526897942926148897050767960510377611052173729517515787,-18900482451752714922774476026355094160342163384175391585859011423259621,31701080919746585586775706334503456401453803609928942683012719940347339,353417281422536453490996795399032193643311783309197908855628203780216015,-18369358737177202067327242204640659761954269532298917446392217672161231)$ |
| $12$ | $5$ | $(5291157255394713865829405819758050348771087482526426038768790130010239593,-6108401609532090817028018140347174617767146756229536583272907615489218657,1184469860659065223869346461305678501323561328979740150582303967182822329,-4402894013461151938950125496074905176756043550927771305164261001458164871,2064649027823291921277311636454416408101590587796959483895378161557242997)$ |
| $12$ | $10$ | $(590300253346301070420539894852741195140586331704059542087868135606823017,-351083329839569452705064879231219118292408525157870170993498674105168725,284728320910834704183885672484044278171910729955870109729072547667717339,466000936099774705740756123559538860157794034114129403148150601699878301,23694809312379086825230492557365449354425828219217385483381720525053163)$ |
| $12$ | $15$ | $(-13927085173736346997706582451766282853711739214604055181923243816748689,26226933420235416890142021600686785989119705554418313145329440602980493,-15054117518385597625822206856425540780448573997254567341176950298323403,5263423420600319221322722049821012853122934611734405104014309810280230637,-1327803800187820962005154432972297592483853655388194232659904574167186353)$ |
| $13$ | $0$ | $(-18900482451752714922774476026355094160342163384175391585859011423259621,-1095778203192475696473243785456279483283522580403916856351300846386355,1837908295630721273054207105846801019812838416332705585406943556702741,20489791972397178249874539690459391897446652247937135302544380954719037,-1064985667016950809077746034300172850444143504258714871806075341202759)$ |
| $13$ | $5$ | $(306761205959987854704995573330141881897250295475405522444273783175044371,-354141930353232393511651680170659373653399706903815757662647035688941301,68671064823970763136444584100727318064636971213393081834444576219695499,524564352393822981546093577576614527318397340576584988998065199776755117,119700510698947672167965871061931815418935528447367915218110919622139927)$ |
| $13$ | $10$ | $(-695830718895834783205105905352945287900495839410192376715058495325495403,-20354478322153046612275178281570739172145875874789188289575785321989063,-1071576287116995138299011332436963461275477687450832782737636586567934163,27016964765260252559442120193180287105941477693079385365100990211255343,1373735069439951274110829797552018636405633241131327243738465435256327)$ |
| $13$ | $15$ | $(-807439514115163300604585147364291935813050479519757625620208511390903,1520538010171755513689494975777771794302354199640082998790274371554955,-872780569863982802858962930366274674345785346820447945995640807310761,1243420674083873454185364874967137031625552342501265860254844217187674353,-76981022366814011712169783062617647901222343431852227223191580840200011)$ |
| $14$ | $0$ | $(31701080919746585586775706334503456401453803609928942683012719940347339,1837908295630721273054207105846801019812838416332705585406943556702741,-3082655680964377099747405448301700492678335183318254487738512643242701,-34366771060148350498030164047918440961307162402157163129139167202044383,1786261112363501778480922816423507885763728283816720497553152498649489)$ |
| $14$ | $5$ | $(-514519237167663834325754798221521974798231065805339522454555505942538277,593989175665829944390840669207831636073757701468974082668210673334561193,-115179439910433807851127386650757636857274743524762705492019637241457351,5775521793537692869874762624760825886510939400937868943951285201414227329,-200769244144370549086957589797643403203984127486792220629179293593902003)$ |
| $14$ | $10$ | $(2305302454357129892383215413755486877054389882613409201201786620207007257,34139814473887362531882769201209067892323715888729915237978283599478625,-2304710690344614704211064270175120718062106800136804392440754720250658283,-45314556832914817102642796292498849457286228067189456046118390102526051,-2304115078002738140363802295965727684089526718093140788437365236595301)$ |
| $14$ | $15$ | $(1354288465392690310810638748664193916213589623269469237745925002513425,-2550342226715765951855230475055232143086105330876585423769754599333921,1463882604111774308994852032904043391141290032737855579210087114642211,-5778240438670520021452394358271818263992043892795886823954020697412799169,129117424677637621374163641723321512884967544880725486963162718263374867)$ |
| $15$ | $0$ | $(353417281422536453490996795399032193643311783309197908855628203780216015,20489791972397178249874539690459391897446652247937135302544380954719037,-34366771060148350498030164047918440961307162402157163129139167202044383,-383135541343093834156105387346495954049932053089212307903317686345964375,19914006965266319190430825331284824868200110647471695868982348530634745)$ |
| $15$ | $5$ | $(-5736081697016362587569978692668225036573872637703736894209259954763274017,6622046743127558482716434311650813094109034786388852938421079605077624561,-1284069922788024408540523034189956209343073953762974906330062991650907163,5547334843116185695133823630671582291071579911613783757000501143069422669,-2238261863637681384223161315391327968616201044646589525460276030520437649)$ |
| $15$ | $10$ | $(98120350093302556102721265143184202328844249889128086872290870115636791,380605331729095001904005017746715704464649535010503599798819125195100143,794328198713582272807952628011933485095012990326909530560911573023126661,-505186164638950095339694448232289299605286759530509718450576548257420463,-25687265649202751568781808153078845520666153762528336893097269688492943)$ |
| $15$ | $15$ | $(15098190150445177662107826947698653769243032817543385010204069972222379,-28432311779676353061342892558199071059203131145209721365158762407131747,16319992733896411934134564626984621631080219203034609184340740646632291,-4641585923418518343598766230593933001010912610872317376383922676963415161,1439456570246645943032254707292882341418718765159251759158571610748750191)$ |
| $16$ | $0$ | $(-18369358737177202067327242204640659761954269532298917446392217672161231,-1064985667016950809077746034300172850444143504258714871806075341202759,1786261112363501778480922816423507885763728283816720497553152498649489,19914006965266319190430825331284824868200110647471695868982348530634745,-1035058433948714011296325841626901844336373988873940630286162289890449)$ |
| $16$ | $5$ | $(298140888906545457311078073329752666830164060905261493256210335415158621,-344190164412003271836768134320523841399489407735509310505759315068419465,66741334663575787520420772579885405793002784698634621150784037711838681,5485724913352986732869223533203130993813029747935810378749417386069999273,116336798685706688575886995075774289557445259579852505698331035277286801)$ |
| $16$ | $10$ | $(-2346462490988934419158307318273809025682651222673440059544308741454845867,-19782495772908323169577025461082556589676845244578654357629604322073139,2345751781090691578889792303237342907332083201427593609374291544808809829,26257759241310777756366811473859996340643685037185692703151998630515967,1335131648877216579376319345767151725807928708644041175478498298398061)$ |
| $16$ | $15$ | $(-784749602620754657621491969343022845948780268468986649189858634770263,1477809270406660764028058911818666144288124226153157097199952797184445,-848254505015701416307830231498143436593425155689903573443840620872655,-5482053388570395879437115664728112139006011506342074514557268183197829135,-74817773536756166403609270196319971853578317268733619545866290756240463)$ |
| $17$ | $0$ | $(5291157255394713865829405819758050348771087482526426038768790130010239593,306761205959987854704995573330141881897250295475405522444273783175044371,-514519237167663834325754798221521974798231065805339522454555505942538277,-5736081697016362587569978692668225036573872637703736894209259954763274017,298140888906545457311078073329752666830164060905261493256210335415158621)$ |
| $17$ | $5$ | $(-2334922425276931080491311862560162971279400636107296141834746190156262907779,3644943021138639028613527296375931878648732114365738273088022170095446308369,-3300955970337314328063433409815363690151723699018350269256737449839992919699,153377144546379117120864110972477582423602570295654348175531002935078064373,-33509950197089077903657557889516415727154717859726057275308119171791803109)$ |
| $17$ | $10$ | $(18328294919330556089691235077648950898121730301736961471303158438566098297,5698200875504487078365957256170385421922530959334776259521068128691122121,-25045680469912125299788241114719273165802485790460095328382456242642230049,-7563352390678986466673613637963786461980157036806903685556261107645225419,64758910332614293106268171074353216149523232814121272035641645652040853465)$ |
| $17$ | $15$ | $(19517394700363772301880497510119787227824094283282773895281062435062466851,527697528086210364005551419207793494537232123128211950697171201869434731215,-82360798852386132413503110767815353947025292404230327620514408757476471909,-174204209376475804982312358371215817731460751267505292333614485337955210719,21550703589902196727369580012941274390987506490742490630844573772714437767)$ |
| $18$ | $0$ | $(-6108401609532090817028018140347174617767146756229536583272907615489218657,-354141930353232393511651680170659373653399706903815757662647035688941301,593989175665829944390840669207831636073757701468974082668210673334561193,6622046743127558482716434311650813094109034786388852938421079605077624561,-344190164412003271836768134320523841399489407735509310505759315068419465)$ |
| $18$ | $5$ | $(3644943021138639028613527296375931878648732114365738273088022170095446308369,-5704697304514459546761267593274573741344028662539075905335699938532561015319,5196108981454957602503839342690431687369293926205812645900623785220042978129,-184560011682439386877828036546724078968575371092979875652530923843951172823,38685721069911640123057083036957121681506373443329906890957175073323559355)$ |
| $18$ | $10$ | $(-23296058214301151987695423617205355686028878796320522531799544725025783839,-6578315048920659182344419463484403041319597399453076532799073208302962945,32115886014855394112115986593439686031324872315055124213689102235995781001,8731548069106754377783676679718877708127100372057780318178733078179448853,265528379090980123183677720266308850813385381293279988925401612020230390083)$ |
| $18$ | $15$ | $(-30675333443648961618218313832632160614721951061356908954525024523734155067,-570413817783781181578986443206706366104163004393308045957160879228993031581,129951600537035643060005642831328554564657957321026759602356892900572999565,184789624772911001459224991859131901974495626778411677551740295669944288803,-24879312056146283764518531107653415243205772044829657259202148817269640549)$ |
| $19$ | $0$ | $(1184469860659065223869346461305678501323561328979740150582303967182822329,68671064823970763136444584100727318064636971213393081834444576219695499,-115179439910433807851127386650757636857274743524762705492019637241457351,-1284069922788024408540523034189956209343073953762974906330062991650907163,66741334663575787520420772579885405793002784698634621150784037711838681)$ |
| $19$ | $5$ | $(-3300955970337314328063433409815363690151723699018350269256737449839992919699,5196108981454957602503839342690431687369293926205812645900623785220042978129,-4792896778444839283578781686556935561810537146494598008046641072065828132181,-37723525607868083795664996680721206326764106810752467870898196034371857833,-7501482969565865983357308252409507964066401343663206272525919325226253743)$ |
| $19$ | $10$ | $(8689980068284818516749846856032972835253370171930226119467533857231045891,1275589983672233574747963002502064505608829552383611229556706325544400565,-13041735237330748756690882443031657741801229774597366632477585632101872515,-1693119769435892355118097780565728086058674003327105441462274405345099393,301288856312529268455506776482064319054259472929131631343408716296081578435)$ |
| $19$ | $15$ | $(28199900214558050065427099515377959336356879014007924531311933104159677327,-38646011748305978881506170116977621436636572783141748215793582101834300559,-120479955674219173749723163101708809992479819584681446942827040359742657107,45002659952955614489898490618142808673015297222826536520320562051043821563,4824305467808677214648390042946797203970532632435551664336536313108956159)$ |

The integer matrix $A_D$:

| Row $i$ | First column $j$ | Entries $A_{i,j},\ldots,A_{i,j+4}$ (last block stops at the matrix width) |
| --- | --- | --- |
| $0$ | $0$ | $(-419183038017584254121803935333822536525344916915245730653948089024594773,-131081963416076804368232914800302521978156325773649373362960200556270441,2141829350811155606831320759735943565989725587933465466179516239478740927,313670822894813226347207117146402731931967482541334401622400532127916799,2283390352453456729782077616250110565789726747882153100397683437785849719)$ |
| $0$ | $5$ | $(41508821276904487771296150376525109467729276590778505662327000384086381863,-45110664522846035442257289242108901521419766988002773997413613809137561911,-21765616578331482599943106165471106935936571148678525264404547859569748107,305901082321301809695688378197336318921612991339798895909198505719638876021,-6885006028982250800695860806100904954332587333932640197137203097113790593)$ |
| $0$ | $10$ | $(3473314511951324142262444680860245983466310880461657052518823404587091453,515800283744220510935412932128118444387605281690061105841855488952454273,-3480526114815193500937894687912219287287154948959839557343357650455234313,875213013338409553735955451783279222162644903554751221595155644385408975,231776854380196338476410581356599444026392908729484006658882080025523021)$ |
| $0$ | $15$ | $(-138091877217603887388692765480394633231353996553484941674975847482227843,258596867913419638864973992627385053595426530997221755538048945289416473,-150179696384338152569760915948867232140983339840927519093142971874150095,-305879884001992194272217741383242281855339902585313417628446424561488199131,29950319)$ |
| $1$ | $0$ | $(-6909780129934164233453117063755334179887573798254863943134927285256663367,-568402853844952910211776891618339010708878758803805027902853850881899841,1056151928033307813041209485108837564500093765539507303239608148184091117,7454854868410106509212366861059481611154419251705039310057917541232934029,-236993683653223536182072248935577581454091844296864887402243555574014547)$ |
| $1$ | $5$ | $(119716279860261375643133085380870231268171582649691755535078989441137377013,-136941802870100190242927956325072526574712414903524981537079958707784454279,24228990556963038281810096067945044316846262329223402161662330542925160387,5436833798360223536392055357780808910274514753215726418694906867246829502985,-123108272688243241387082563598408106754212551819704515346107906523817190711)$ |
| $1$ | $10$ | $(44680023161958137884134191606420744188890366344895867133703081886745655471,5582725259421036719466920808712407095255102049255608245427937109994101479,-44690893290401802922947130283525687358026696540781174826081269725808434407,12353961186228846005607951993889734295199279650280394047194429685856030635,537115909346996123236419607517173676373406514473416341193591360020064755)$ |
| $1$ | $15$ | $(-320011868327023319656975160835311505136432897415425017531645463034445407,599268172117660499740251860055488313702651323262370462765078803985432969,-348023983691711202161338653813745436842632018093479840868748645847693597,-5436790515642772116784713192375576228144820982059601864630814512232051368067,532344959)$ |
| $2$ | $0$ | $(2676834377860435412195681233566666222445689135672449628218343677067380251,218903345227191905976688881945967923610840666809745744801248093753785229,-381302726706123678917211622451994945812207424658087257301232941379798941,-2889852579128697421717460911941742242777683178577270757341148837422198249,122607987223452039160301709794221590746059042495459702396841376185120527)$ |
| $2$ | $5$ | $(-45918832340885384696457655748238219917050369868837325568840955472669488893,52557694266858688123988738371289195686556521851440280678537301633580391793,-9697686850878313552952138919998902706700112037796161108218441664542987171,4206228363236450618784607725268237593022236989180904734959596806460592585117,-95371455138618643242080393775257051275994061181422400791713564856879354735)$ |
| $2$ | $10$ | $(31611144953902027500200949627703952344673351535064479730844015468624567049,3697734086695648552752552947306760886428876938258739452343171792598196869,-31599221552119453650351978907232928561585503839577947295607065355149610793,9002773917010141206783231227255712853468562296012850885969594465575478529,-205407788730863590027456131570400098433852833736788310193447469235254339)$ |
| $2$ | $15$ | $(122381275804326092659470710191776229302209679629695761307890985574643495,-229176510971585922258980139790554055464217439899768041525917063360733481,133093873540873785516862803978808738005295678067678915573015634542309561,-4206252682097237971406914133363942585449234753587149292265799956749810990429,411856481)$ |
| $3$ | $0$ | $(-434581858260148015424222229187064392679175174762309936395193050027129475,-35879930855927774377428533652085902522804879230909252479346307274169729,69242023087565186752340219883576570194927851513573608873522099506871549,468675779365703040332099404515042539330749193427540858752189298451723641,-11790476425827369714865676922733151170515468197748470507561294409365951)$ |
| $3$ | $5$ | $(30789390673633511557494253502742854833470858589592265902263970727659482681,-45260730131098559316750643627341905176983795116217729988749391438966505439,36192439422380584133393864958761784859910087960871350845635408242862676359,966498235659048622161888227015497741034850370004186181829350254374175734675,-22212718249868187257661608511994387855772239277951065515344630478687629583)$ |
| $3$ | $10$ | $(384550008481611325336604319772236558962359606068503908548101577864390403,-596465586665259053184964157741122961028509236002531920600232664847720535,-334488246424420310407909448180248062345130603127843274055933991691892289,777157203449102107717325584230434141517298551083043945920467783345229019,-1492357459819069078928478826582943743697355364706366926176337301628270195)$ |
| $3$ | $15$ | $(889141599825415412236798419974928370550626901754716627736434764406652367,-1665045312433976394761814561087954623113092537003209021714733326131218601,966972266544314227376031127224907316332836003670952228518098492262271209,-966638354647406519492731345902498173645438068546370606453221191155684503669,94648681)$ |
| $4$ | $0$ | $(-662581987315406428063771559121232622000120180066393723663017417754484237,-54704068840878399855667739917036124210573980990060083570084860748949221,105569333811524508976682719858812173811791142784725859047889735109393209,714563029717711592848733339379055363708795513616408297020065797497973573,-17976261901258795623587919690502360659276646473408452462580867988893383)$ |
| $4$ | $5$ | $(-148349136244926724480798481026864480009154966350737151018352845325626582789,238887122165420445864059724132894704718255107321437173950839546733776784793,-236745701557710818853230418099833031907614327145769997533475934238795237719,1473564322918564199782108168803763172151064752773428941329155279528754055421,-33866455126768244042449536605281248838537877308070907402828607349625148319)$ |
| $4$ | $10$ | $(586301300891804161835642462846006900233720364020914844730043109656407851,-909396805840292010555131932101936117357592609352691778539167085657696083,-509975008935759143302025974083393867225524657388871776582886702192679443,1184886931036002248096678413293026408935332657808189096239398069587181541,-2275311665034974314257076369228622016236837986883994689863176651136026525)$ |
| $4$ | $15$ | $(1355623105335568132408910273215404106851147054134216221929059234477581027,-2538598910915177715216154040914284811707951806165434341559544634532659443,1474287050570532013748024483240510735994579125401954032437113843075958465,-1473777954288586148865151428170766565320164302315447352025576029729881535033,144305407)$ |
| $5$ | $0$ | $(807836008778819513491243821445123006906880837600509877858112802089713421,1762318592279309735104679933411244781064169693540888444716043677720947277,94061934398147259658216984429164431186483282199214658839402981156403503,958235181566184321084812677238262867028628038134672072458093817212837161,103674499971387571947480730757656259510498849300648898627162009838783117)$ |
| $5$ | $5$ | $(-18078038401644185243451582587132699733680789790246657484464362407299399697,-2908950124572975233628819187435754763187071360518718149649810055725383345,6998954696759016288149868551661909856009501028900914389109165332590407407,-28420669015249160582844415399202463843182509531124687757378629113188782573,670646308932184639743852301417283017109079823362613764241136747001398413)$ |
| $5$ | $10$ | $(391178966812013919345801833276740937421920232582207460464955593646159061,102151621777885924499634417026612046711416625846643468453954679158872007,-395419866085941984606560073953776898324943286917539950799193475810958527,52711084436199164111516537583291996286911682586609580398608474558927521,128439662041570523123848635008466953920708880047505562625295105741988069)$ |
| $5$ | $15$ | $(-76523922494094169485416322271247512699718536382052621757745526741118345,143302032502889018864251999294099382710724932277658084493931113491268219,-83222414510247885559271036783694240195743095128727879577405198071847773,28432660684711798201361250726321379012138147914511531153070454293894627729,-2783993)$ |
| $6$ | $0$ | $(135773673004225673961552936121653906169688758559827300198781613708683537,-789881078606130464999236153882468520996503907005823118711249560800097917,2510825800693271636506287299626460999738313550773180412472096001201619415,651316873931784970656964282681459379736305055400889679602423033966066355,-2448613126311061867043642760092430047223038739576383177483052323014431893)$ |
| $6$ | $5$ | $(28550698454645524658632243588024413004573522634311172891964739901079634995,-35216116824387109780503735193266974223439549970011038272253152215846462483,11340423182857101188991583936971425055992711910561708177816101859029605873,4871715898794823522958973041914613475166751984353871245857601615863383832445,-110367563997231127236651181973292994946370599494780330285663145791824763269)$ |
| $6$ | $10$ | $(38757450294677801862678546344461433412803770720975122430115632552821574645,4733689360704767231653166318480191273914719171575813700668648045058046043,-38758396027686695213927608638240892694393029529525991316006737628099426219,10829845669186014797880607217232796832766276188808955453641098349153713393,212712192392305039956944174355983906240221109827062726763911633966688229)$ |
| $6$ | $15$ | $(-126733215156773242412735435376906174884863990655897625260327226663064943,237326142279143550197077398090533304599374043906515915968016180485006657,-137826758224624387524252535015941030072672649893307716317159336707580411,-4871702116814090498105414512087544831099761287916466334510826177691870814835,477014161)$ |
| $7$ | $0$ | $(2572865463499547168843791790950212304384806229985064654573812591254410023,-973859146798041372391766288152449040100765183578597030906435434108564223,-2602144230538720287705009068086216688770006989677218849394577188214427557,-1590982203302817479776015583477073193417844041844210253924652157571263041,2344471464574169033955662687131155800999461241260241023908652875747216653)$ |
| $7$ | $5$ | $(-64623605999031298322645340467317756866142545038080623693603334059038047289,77554551569412595700967307453716055553894315294114874564845556261748789285,-21780135064782426323894629313505772064425903306424782558639668364047771727,-4805000676970906383537314019089958045370698161243293145389941179077121842431,108816806291651017980250964697744697350600113726339317462020459817884457059)$ |
| $7$ | $10$ | $(-39133392637082187031682223411874385157115150489978975156906792002666316739,-4859474117096220769151832295819166166303849870360299792726139478190739179,39140562814414614068633843697113237660459184238302922605690677459914371179,-10851764263299844551094430051239056422513483166771234782095792637201826101,-400281979503872524550558131067134731713921941529460496071817292537883773)$ |
| $7$ | $15$ | $(238486669058837264759808366994957534309699136813648505276932957228899519,-446600530750534666527850052325514802411474682332213399118365316249968985,259362507575518163478775666443400845861882908313729624012131309887332493,4804969351531994304284244879175681539841511402313416013562383271559499607313,-470480003)$ |
| $8$ | $0$ | $(-14791713389878019421005112103768633939867845474087189635884909581912063,-1221232878413951317547190439355141238539783941265318264561141978145931,2356766948687196898120557968408393912019498723168724402595566962663613,15952156468080782559055261341759577784670392540530525086673333893429461,-401308394968830601241043768392273158054139946208531995772051575219259)$ |
| $8$ | $5$ | $(5738661166698189944474676832723716603614763803330044030950804955014513273,9184709888474503425860935451335620301362005555190282560437575153562055871,18239089868856031069916621989378391227884688181381996798237495887444163073,32896368364124178465173646333328246015969895693560085480063523557605179425,-756046658913863525974560836370803765020022688217875184031724521580143295)$ |
| $8$ | $10$ | $(13088796509609776993506134881040266037643531609096767986614733464616725,-20301694231323653421295311989360997990665766050262368948430945202298417,-11384861515390657033304672161838002963736683321235689080429463333692551,26451832707238432308030695753516560034954814603717860849974814251519919,-50794858094780134420598006539528018505481874302143131166467967377837829)$ |
| $8$ | $15$ | $(30263407129531383943821760972413937894296246961119651228401056459659351,-56672575199722260313248274371477323780795865377820734038131351645615543,32912502790491791916702270233179196794593960361586151387951282947243829,-32901137545986871359888944354998991813751294006505024108914115754638176609,3221525)$ |
| $9$ | $0$ | $(32010697664054322291011565072616448133459813079923273248390305119998545,2642866003276053603869699063027921271639180984797023166202459166920903,-5100271501385805357615773937817136066809342018344946319517361099933661,-34522008663232594524816637784408631131759444231882023222538027499303089,868470160474091741740385972010259871132788961701786943009488983155955)$ |
| $9$ | $5$ | $(48412284779331768962990002633702326991635048390686064255152151609889929307,-48614194508927014112695688524348946868629699518775400703380169145576520275,-14798332683689722223163445164505954075460997814419836806523094715016404625,-71190921172792157303988253758781211968841209273013498190345331284037168223,1636158055561788142630925810501818343681428633296274243433273751416680277)$ |
| $9$ | $10$ | $(-28325420917238527335630900744829459148183995187451501660410877793967593,43934828844891266420326872301723843668379838988104992551967699116046747,24637940873413786933629687243269935222525261461844350195683106794704827,-57244323029607843205724399330548966574659519228048112793889000772582443,109924983164777095890363328242211890058473825957035337849078520210578997)$ |
| $9$ | $15$ | $(-65492938537501236805478370319217784619412856736817909487261260286142427,122644931168224357779768929312359438882171571525860132694549373922843347,-71225837631137682311954364876944772388061123653280179505518058055501507,71201242143371266979697326540540904059863031695043813904286567490990996061,-6971691)$ |
| $10$ | $0$ | $(-7608036657137806611923233386636748443082389471062136661890820072125592993,-628155099525440518641519905881046512208394270934461386666249284716454477,1212634665742521905121867247675079286856268000189767521739673033843747043,8204874542604619645073404660063919887925221503181246312879119119950227281,-205919192159784036006884401093350069796539065050928881052912452808285525)$ |
| $10$ | $5$ | $(132634089712387690806199210904308960521791441470131928563536120105945492449,-151661537480023697963711437683320673815216496699063977504266950426228604935,26121003233068533556262676265744974418580443250184862188801397783135252735,17072169704535701497406380626277751781521908537930123687110990022561282412949,-391152011162133072377941278976860785702840351102290135189681242210650582231)$ |
| $10$ | $10$ | $(9477795284161360621882046938589600260112930425081179859891692613261587339,-10441831343509998776396793386302643976204502150208360756029280793000167447,-8592461281627996614138082499018003595285093238141312403671277366466536361,13605381982625768378133826500598836284440123412663272923850627608549889347,596163245738223268240841002835668869474078018901534493089973723170371717)$ |
| $10$ | $15$ | $(-355192074516156023760971514709090600255077780477029375681154247218027389,665148159531563756328044607948248882523522561729541083500033269805377415,-386283675649529298583009669233043885635064106956722574908382988236442275,-17072135639169104705121144905894502712919922821919465252249570424089834224171,1671623235)$ |
| $11$ | $0$ | $(-27035239750914536818458295494661749390583738287782452043181811530396721,-2205986192877253774445415872699413249643911470906794647107948772692215,3746228034215975243633914153830814179711936787977111276521456146366949,29193651873089398959625110094282268496651057500607384670326240610891985,-1354220850237793521159680218548007711513414546093012391598943734871821)$ |
| $11$ | $5$ | $(462039068285582722529770014617792782134088561504005300130752243669251365,-528960634274986573835871095263799520277571077576805789698095900653274933,99115951969455157692967851787214791873556369571302119348503696580417761,-65921687539399464962913093204094439318243509076099734352068627972224353703,1501694793645985712148118549839210799213244510871011339875369714199944951)$ |
| $11$ | $10$ | $(-659227375998104171684128915927565192949083862309053653091080151689311063,-37401143199503665856289581197244382936478631124863998656319318886190909,-1107769306148965763784652737987731552520510788467852299339867064609470231,48312801754201630062348047695808818198900883173616682293563186505975431,2064509503221652507110631943692498391894931504518348343967115672486223)$ |
| $11$ | $15$ | $(-1230027880030715832345423687787189256379703892982044469613986428390507,2303403818031215369415105325687076712486464859811380641175635774986951,-1337697895700235540489338119068003410743848389286707364912477988966915,67688808805638843541546618170805514157677033571504460804391966079420788183,-6627769)$ |
| $12$ | $0$ | $(59403444103046852279475667793224637042497783278870116295834526625791869,4864392278998775352044976125046041688137362357196778379178295660147757,-8602844165421500169031914259446844805010383320535448596838036450789215,-64121264541686948174331290355278319158894074498438729704043385991344293,2564839154645544182436348573534589101420002773847574327340653889374533)$ |
| $12$ | $5$ | $(-1021341504274674448305563858007104638843641689436679946145708860046502369,1168842616130567928389875493726193386547691376625620345748159628118698189,-213630051401842022692190544500105187312229786314246227268292562090954675,98102075855979172855419547988020921260835942223126834956014698983439290913,-1391603305891708339039677009948209432650126835544855777083603920769003437)$ |
| $12$ | $10$ | $(2121197265438337612139371130964991379133807414347338205172190900347054637,81984726807044573241296864440939357218404940029463941330851711571141585,-2120990834121649197043138617629105104555432177547312317004429170159720617,-106178254384421982671775803845681095599110456411198917682005190129449913,-4571870167453757003926587501485484920385008795383718858455957924358155)$ |
| $12$ | $15$ | $(2723905005558629365887813877349200297311572536935839347637368479123969,-5100903232861199306085876934007599513042361595248423630783997477855187,2962340978752551630609325803804677395101726763697699940505624939200777,-98102558179605427470910980818542025661593277196617974225038576264919247743,9605741)$ |
| $13$ | $0$ | $(-7640683286337295255266029788940316337140093986565461487074134383946074273,-631554540269698275501672618978289580526344212448064590365404831364735647,1232980084457704448362087742242425885612416565390453668991393902290335399,8239072332235750077465220180311143266873854684828734264953189965740698809,-190057539991257235241681011930471936179543407552045501105591493316884059)$ |
| $13$ | $5$ | $(133452805585041660269243206404930367491855563144590671006369834774525334015,-152580534880391408172019884853600789080287541930346976278298981192148433619,26063758940515214577407324730074384925902962797973647989371121741272866947,20549924580787434435274794253595918375346887520339928111608153824152590191063,-470618038292671012654869414057704644631993745171971616987542281999075867599)$ |
| $13$ | $10$ | $(9793598302337022278735461033530437366497906351787141350688630083155893791,-10478675825213552169629691658677876630789610176918387669351610294249457465,-8904048262495035428002710178293120912313920856515201513030710714302823885,13664680124663822472178382953621820597359587782920539522959944304011641627,600173065756860013819073269787696160696386469500492712718172027158661731)$ |
| $13$ | $15$ | $(-357581111916629033588393108304803044007535713006599628523506116139634707,669621975092176482893829896906764831914773738717277113043206073808347037,-388881836516648913361354980943189242586480510838731060551104376073740849,-20549894489483097682463933915141636351207718414369576546080791643319734021277,2012149027)$ |
| $14$ | $0$ | $(-60165000704706947502585239393425878590917919224448118648069962966564419,-4948927486306534989099338187797462737130616936089418867573940272995017,9190058293854492344915966101489723340483602056593469788083383476562915,64911494701047443412169580231303895850466074051465951188668777976988471,-2070294856661010601445277970923278210245245025316780367918400458696681)$ |
| $14$ | $5$ | $(1042295996931161314103483714509113329167563524962747446148360486763738131,-1192274980030742539112043417787457751693660567224577196152838309242667077,211035373217854675172864899279466915656226340354866681783558841185012425,85679471048999628271355218453247684805487076275596716564396439895010205691,-1040631571233523284204547952710580017051901473689294523519673915866229677)$ |
| $14$ | $10$ | $(-2115469146793882808001836803693956251463782351887955875182077086357319709,-82784992855038465303750638905489225561590303018229515059583843925887411,2115352169278388812677575647971904132073533188059439376982543059687248401,107568333783174217180986073583658474404451094426711308539999482748820137,4676204226087971920779008114924189899113989847568762449968693650707425)$ |
| $14$ | $15$ | $(-2786066889898023196027397196453278961279115651213526488001703584003647,5217310286756432170873528939850730770609152008469683894273714197647779,-3029944179642186802331936914204891756193115733106936983881015014939207,-85679071883071802970140074802821169242937911521963069910099009849637779999,8389291)$ |
| $15$ | $0$ | $(61570602600078064429377689926311313226684023141049566273365877570903308631,5080583538377014214682970360535807238182122151862424882716383298187468645,-9749698995256977684950840800451695883705965515695214084304484094516928033,-66404980128871176774424167953039368699453091852476172627236385037832362011,1737198717978128008665277155249160353350860044555559563791649830200288863)$ |
| $15$ | $5$ | $(-3052331800301239425747795573569569309522707791919245385727878059045825159509,4347869191368376088980425564131211578263279535974338564757410342485778962899,-3171850793233186071985034881809279751354690396493105374265386488241741597965,-123181111514344469183106481564467997719659988462914323115056559192258209342903,2836972542309867379635856200128453155632705549316283110171247700571998027611)$ |
| $15$ | $10$ | $(-51539070572506397246034792176173938401570209140270662168042043147834968677,84537672220195729476111695224764412981856493975021238021373596011551151229,44454103343239254884254224179098701711425682591942219430525845544101322241,-110102271379378630601967317224679018363766338339276577527636463858204569651,61974340434830395536371696841270761528896943661682909172923293962117573983)$ |
| $15$ | $15$ | $(20040246179241088500578628112456537887934508658083864718673098325503521443,528618356515415084391483529066407932029432587837833949194355809845715931863,-81237608832342760804193704423467764398296731223015240697955089931678588687,123167141548940337401701362008821009201517892073949806876400104059449568225893,-12059947273)$ |
| $16$ | $0$ | $(-80763510354663479121368417039120425267521333545617863945018477782762914353,-6665260610096172801034644767697390899041685656466760049537408805364885583,12809278320800090488780073781103239461017680569984522264080713013467644021,87103509872720045440784793680679524054394270765450342612584563599818387947,-2256178996028142430061106510071401937576311125588131585387210095604837177)$ |
| $16$ | $5$ | $(4528567235797573130736421671040992785634851258272649459698924088042148398523,-6530348070867052267319712980740525493369418123918423994050620806458708279523,4944272604313316718462344915295997573068836495760027713723098783977789072475,166282038823233838400556652178796026505771219417846945061540187609907776634037,-3826037685017636810648658558226333740509856159638645203938386464532135496081)$ |
| $16$ | $10$ | $(69256752751717547045559904140812726062088214565119862067792380073341083413,-110879200737633853047564076945659488865841069671249229613143362294195617997,-59958512698383374768539331031836907552998461057535817289545567319369724881,144424798898656318532110876607985215770804433895574161389342738166413446557,270368094906797839186641475980536347633121235271328812267713115798919818785)$ |
| $16$ | $15$ | $(-30835860772576543781536919449942066964556662429413330665946498892670265739,-571372299396001669514153296448186792019641584979679777578909847979306625443,128903326362051532230181899686336142527554551635278144697549771024390921551,-166290866757518466326825527709027396513228433763142014607167635736550416500285,16282419645)$ |
| $17$ | $0$ | $(41042616240127369372628479869861486884524837420145655014188421859989201781,3389210219950583723059088229326700965576028281233858177480457387876141489,-6553337822063968942739885307246972346442399416398188268142168355781668883,-44261567165917856429076151158469996415487440041968011548228557120013014293,1098019628467529951770689658629231042167158010608450730703721878132102035)$ |
| $17$ | $5$ | $(-3675447039351397065129870007441297596217033297484021165210813554399356118889,5484638524535258700906000450536943586369883007318661103837657650627192426443,-4565064700708497457403673595381751274113187910647155484733746374220661692895,-95108433151198007481336441729504063419286391257965955510321035422420079053997,2169771381675970282205694199133613748274969463543130894350384291504363633507)$ |
| $17$ | $10$ | $(-40048419911895436206102893513236844121159498224013361102265153185240794129,56323812068086553603520396369458059046485752064254693692974440274660607473,35308802785263787674012610483506059828065981806216481195072964496697795307,-73396835902113820663252204703914176048675432279772422561131749792400412557,300363925952627246662919262583604411984804932437835851505532562148137603723)$ |
| $17$ | $15$ | $(27581933370276890492540668009243801222510398347091634462048981944731907887,-33724155592134453747454205715907634105193486654152700372638195639561543807,-124018049791097706097963528880771332360583291814017614982215684946547222879,95120733226116344155928495126456385012558132856308810795244301567666761204999,-9313774867)$ |
| $18$ | $0$ | $(-15275760228584595796383968454762125859840813721970387405153011652148152101,-1261916193460966453377489147827825667629921851474721737374793170390514407,2449365028204812741950995214891503844695845529110311230646199610392746817,16473145751388574581052827353994231118417377779593765405135294354097634863,-397327500070030679569385006393011060205840452888231397710962455924506971)$ |
| $18$ | $5$ | $(266549075821750604504095446472562023528638922007726945199220121671909513375,-304771191063224548403128554502149997116794640441431604477407654045278049775,52283859150392391683155491992209749018160000390008292469882596734756379121,37557533177266944872603779208726036985377143142316576968814002242429861279185,-860285288478741866598632895470829130034781875056301512107860726410292469133)$ |
| $18$ | $10$ | $(18612202516762166174759583177840287733756076534263899747092229924302467205,-20957913529788973041339001657750480573734549514258473133316113931991979589,-18604314574292217070605002087913103114190913048142827265277371259310399965,27318384128066343157703877847325150810477776023968956953781479409061775485,1198401527522408431226730489446090067416307223044003700484888353024021721)$ |
| $18$ | $15$ | $(-714003635257521456764582507465484093404066349890719392060070677107186871,1337074326721173891695702942801549561755326335868495540214943089356901681,-776503667853816452192786000736367542666080971424716839426593267752611779,-37559235593998934755373401006132863588811368730932266855844678067024494207887,3677623717)$ |
| $19$ | $0$ | $(3009992158436075912902700708629647278526499092766654334876594867322545149,345313788834941752026971318907460732883197946177295018885317163171662765,-2561711624495892178722540417944702844579743906523238313672740044017819059,-3107261976441378003024668111274099437691007677856250958300699959790141875,-2220938718605540987070401400082147377154764716453013963180135665489191213)$ |
| $19$ | $5$ | $(-86789814810720071523989625126267646952814614184579899258400131932907197839,96879722086487048386647538535840779164504766884979180399373006413388596639,12948051886830718392693197839257073118819000150605084625716648419348231679,-942085752748105796189166507626381624516468936819683167000736990331791128434325,10850232272133262469197963690545845289139832461838434245525560992706959853563)$ |
| $19$ | $10$ | $(-20585393262968844183964064711037317892711183528140697370065829789747131173,3036369904783592301197191039291416297759343924054036948946848907493648799,20246135103588322390188027433572335036416220162234906974568227069431550567,-5508752985222019690217041364172431598509924798553167478475788572713089981,-435456819541279754670787419888614220534068888718970552102941070367607299)$ |
| $19$ | $15$ | $(259443721498709893060263867554129463032476100855602307107362873738859157,-485845620547586717084735853227517824560618255921533546382033394673580927,282154027510982586758920548798968228069625909502541510519122440542845525,942086065728356299323535023832635128332049127375928517731545526469682669471701,10674510465092080951089691608164491836294693802860149555870145856530478591767)$ |

**Lemma 27.1 (selected exact roots).** Each box contains exactly one
zero of its indicated system, uniformly for the source expression
intervals above. At that zero the system Jacobian is nonsingular.
For $\|y\|_r=\max_i|y_i|/r_i$ the certificate bounds are

| System | $\max_i\sum_j\sup|(I-RJ)_{ij}|r_j/r_i$ | $\max_i\{\sum_j\sup|(I-RJ)_{ij}|r_j/r_i+\sup|(RF(c))_i|/r_i\}$ | $\max_i r_i$ |
| --- | --- | --- | --- |
| $S$ | $<8\cdot10^{-15}$ | $<11/10000$ | $<2.50\cdot10^{-16}$ |
| $D$ | $<6.24\cdot10^{-12}$ | $<11/10000$ | $<2.11\cdot10^{-15}$ |

Proof. All bounds in this section are rational interval inequalities.
One precise evaluation convention uses endpoints on $2^{-320}\mathbb Z$:
round lower endpoints down and upper endpoints up after every operation,
take all four endpoint products/quotients, use exact integer square-root
bounds for positive square roots, and apply the product/quotient rules
entrywise for the Jacobian. Evaluate $F(c)$ before multiplication by
$R$; do not replace it by a residual at a rounded alleged zero.
Substitution of the displayed source bounds, centres, radii and matrices
in the two expressions in the table gives the strict bounds shown.
They also remain valid at dyadic precision $2^{-240}$ with the supplied
outward endpoints. The equations specify exact zeros; interval residuals
containing zero alone would not prove their existence.

For $T(X)=X-RF(X)$ the mean-value inequality bounds its Lipschitz
constant by the first column. The second column makes $T$ a strict
self-map of the closed box. The contraction theorem gives a unique fixed
point. Since $\|I-RJ\|_r<1$, the Neumann series makes $RJ$ invertible;
these are square matrices, so $R$ and $J$ are invertible as well.
The fixed point is therefore an actual zero. Positive denominators and
source pivots make the system analytic. This establishes contact-root
selection, not a new global uniqueness statement for the original
nine-coordinate source root or TP away from it. $\square$

## 28. Complete half-circle positivity and the six possible endpoints

**Lemma 28.1 (whole-circle dual and its exact zero sets).** At either
selected zero, for both sheets and every angle,

$$
\boldsymbol d\cdot\Gamma_\eta(\phi)
 \ge |H_\eta(\phi)|+\lambda|u|.
\tag{AC.134}
$$

The geometric zero set consists precisely of the six indexed endpoints
of §26; at $D$ endpoint 5 is unused. Pure and saturated zero sets are
disjoint, all their report coordinates and signed heights are nonzero,
and every listed zero is an exact double zero of its signed gap.

Proof. On $u\ge0$ use the base-zero chart $x\in[-1,1]$; on
$u\le0$ use the base-$\pi$ chart $x\in[-1,1]$. Each is a complete
closed semicircle. For each height sign $\epsilon$ use its report sign
$\sigma$ and the polynomial AC.132. The following exact factor inventory
removes the listed factors $(x-a)^2$:

| $\eta$ | $\epsilon$ | $\sigma$ | Roots $a$ removed | Quotient degree |
| --- | --- | --- | --- | --- |
| $0$ | $-$ | $-$ | $x_2$ | $2$ |
| $0$ | $-$ | $+$ | none | $4$ |
| $0$ | $+$ | $-$ | $x_1$ | $2$ |
| $0$ | $+$ | $+$ | $x_0,x_5$ | $0$ |
| $1$ | $-$ | $-$ | none | $8$ |
| $1$ | $-$ | $+$ | $(x_4-1)/(x_4+1)$ | $6$ |
| $1$ | $+$ | $-$ | none | $8$ |
| $1$ | $+$ | $+$ | $x_3$ | $6$ |

The selected equations give $P=P'=0$ exactly. The chart change for
contact 4 gives its stated base-zero root. Thus synthetic division is
exact at the selected root, and interval division encloses the exact
quotient. In descending coefficients, division by $x-a$ uses
$q_{n-1}=P_n$, $q_{k-1}=P_k+a q_k$; apply this twice per factor.
No numerical remainder is declared zero. Distinct root boxes exclude
collisions of contacts 0 and 5 or any other pair.

Here is the complete positivity certificate. For a quotient
$Q(x)=\sum_{j=0}^n a_jx^j$ and a leaf $[l,r]\subseteq[0,1]$, set

$$
\begin{aligned}
b_j(l,r)&=(2(r-l))^j\sum_{k=j}^n
 a_k\binom{k}{j}(2l-1)^{k-j},\\
\mathcal B_i(l,r)&=\sum_{j=0}^i
 b_j(l,r)\frac{\binom{i}{j}}{\binom{n}{j}},\qquad 0\le i\le n.
\end{aligned}
\tag{AC.135}
$$

These are the Bernstein controls of $Q(2l-1+2(r-l)y)$ on
$0\le y\le1$. Each table entry below is an integer $L$ such that
**every** exact control on that leaf is strictly greater than
$L\,10^{-12}$. The entries result by outward rational substitution of
§27's boxes in the synthetic-division recurrence and AC.135.
They are relaxed lower bounds, not an assertion that rounded controls
are equal to exact controls. Both selected systems use the same complete
partitions; the two bound columns correspond to $S,D$.

| $(\eta,\epsilon,\sigma)$ | Leaf $[l,r]$ | $L_S$ | $L_D$ |
| --- | --- | --- | --- |
| $(0,-1,-1)$ | $[0,1/2]$ | $61970621872$ | $83218831972$ |
| $(0,-1,-1)$ | $[1/2,1]$ | $116435494988$ | $111247014721$ |
| $(0,-1,1)$ | $[0,1/2]$ | $7299105911$ | $7311601216$ |
| $(0,-1,1)$ | $[1/2,1]$ | $19338534425$ | $19318706704$ |
| $(0,1,-1)$ | $[0,1/2]$ | $70386590074$ | $58728522922$ |
| $(0,1,-1)$ | $[1/2,3/4]$ | $13915792430$ | $19686051087$ |
| $(0,1,-1)$ | $[3/4,1]$ | $82449952632$ | $59003944310$ |
| $(0,1,1)$ | $[0,1]$ | $503587022418$ | $317086330420$ |
| $(1,-1,-1)$ | $[0,1/4]$ | $5197535516$ | $5429036047$ |
| $(1,-1,-1)$ | $[1/4,1/2]$ | $6369066347$ | $6381249154$ |
| $(1,-1,-1)$ | $[1/2,1]$ | $36720704108$ | $35794691050$ |
| $(1,-1,1)$ | $[0,1]$ | $8930768772$ | $29250759002$ |
| $(1,1,-1)$ | $[0,1/2]$ | $36757199486$ | $35831186428$ |
| $(1,1,-1)$ | $[1/2,9/16]$ | $1933497373$ | $1696227607$ |
| $(1,1,-1)$ | $[9/16,19/32]$ | $100584374$ | $96583898$ |
| $(1,1,-1)$ | $[19/32,5/8]$ | $1809671784$ | $2067788060$ |
| $(1,1,-1)$ | $[5/8,3/4]$ | $14949067641$ | $15801916829$ |
| $(1,1,-1)$ | $[3/4,1]$ | $264698850353$ | $268454959788$ |
| $(1,1,1)$ | $[0,1]$ | $1104012476659$ | $1108574628148$ |

For each gap the listed adjacent closed leaves cover $[0,1]$ without
holes, hence the whole closed semicircle. All bounds are positive;
the least exceeds $0.0001005$ for $S$ and $0.0000965$ for $D$.
The Bernstein basis is nonnegative and sums to one, proving strict
positivity of every quotient. The only zeros are the removed double
factors. Both axes $u=0$ and the half-angle point missing from a single
unbounded chart are included. The opposite report inequality is weaker
by $2\lambda|u|$, since both selected multipliers are positive.
Taking both height signs proves AC.134 on the entire two-sheet domain.

The signed-height bounds are $\epsilon_iH_i>0.0032$ at every occupied
contact in either system; the unused contact at $D$ is positive too,
by the same source/root substitution. Its pure height has a positive
$0.0032$ lower bound as well. Every contact has $\sigma_i u_i>0$.
These sign bounds ensure that the signed contacts used here are exactly
contacts of the absolute objective, with no cusp substitution.
$\square$

## 29. Exact joint moments and universal original optimality

**Theorem 29.1 (the two evaluated original optima).** Under Convention
26.1, define $k_u,s$ from the occupied weights of $S$ or $D$. Then

$$
\mathcal T_{\log1001}(s)
 =\frac12[H_0+\boldsymbol d\cdot B-\lambda k_u].
\tag{AC.136}
$$

At $S$, where $\lambda=1/4$,

$$
0.12444515769477<s_S<0.12444515769480,\qquad
0.10273812575328<\mathcal T_{\log1001}(s_S)<0.10273812575331.
\tag{AC.137}
$$

At $D$,

$$
\begin{gathered}
0.15672072828365<\lambda_D<0.15672072828368,\\
0.12435694642837<s_D<0.12435694642840,\\
0.10280323941363<\mathcal T_{\log1001}(s_D)<0.10280323941368.
\end{gathered}
\tag{AC.138}
$$

Both are strict original weak interior points. The theorem maximizes
over every original allocation and live-height decomposition, including
those below fixed-allocation maximum contrast.

Proof. The first five exact moment equations give
$\sum p=1$, $\sum pu=\sum pv=\sum puv=0$, $\sum pu^2=\alpha$.
Since $u^2+v^2=1$, the omitted square gives $\sum pv^2=\beta$.
After the diagonal rescaling to $(1,z,w)$ this is the full live Gram
$I_3$, not just its diagonal. The last three exact equations give

$$
1000\sum p\eta c=\mu,\quad
1000\sum p\eta c z^2=V,\quad
1000\sum p\eta c zw=0.
\tag{AC.139}
$$

Using $\mu=\alpha V+\beta W$ restores the $w^2$ moment $W$.
Congruence by $(z,w)\mapsto(d_{\rm src}w/h_2,-b_{\rm src}z/h_1)$
therefore gives $\sum p\eta1000c\,n n^T=M$. This is the physical
failure covariance. In particular neither bare whitened projectors nor
separately optimized failure marginals have replaced it.

For an arbitrary original competitor, FA69's reduction applies to its
**own** actual supported-nonzero low label $(p,h,b)$,
$0\le b\le1000c(h)$. With $a=b/(1000c(h))$, convexity gives

$$
|\ell+bf|\le(1-a)|H_0(h)|+a|H_1(h)|.
\tag{AC.140}
$$

Here $H_0(h)=\ell(h)$ is a sheet height, distinct from the constant
high contribution $H_0$ in AC.7. Apply AC.134 separately to the two
terms. Integration of the same full Gram and physical failure moments
makes the interpolated moment vector exactly $B$. Thus its low height
obeys $v_{\rm low}\le\boldsymbol d B-\lambda\int|u|dp$.
The actual report inequality is
$s\le\mathsf V(F)\le C_s\int|u|dp$; $\lambda>0$ gives

$$
T_{\rm actual}\le\frac12
 [H_0+\boldsymbol d B-\lambda s/C_s].
\tag{AC.141}
$$

This proves a universal necessity on the original full-complex,
multi-Kraus class, with every admitted time law and free other outputs.
No real competitor restriction, fixed failure allocation or
maximum-contrast completion was imposed.

At $S$ all six weights are positive. At $D$ the first five are positive
and $p_5=0$ exactly. The moments hold exactly, every occupied contact
has its required height/report signs, and its signed gap is zero.
Consequently its low absolute height is $\boldsymbol d B-\lambda k_u$.
The simultaneous instrument of §32 attains these very moments, actual
contrast $C_sk_u$, height and sharp cost. It attains AC.141 for the
same joint object. This proves AC.136 without a remaining optimization
or an unselected root. Substitution of the §27 boxes gives the strict
rational bounds AC.137–.138.

For the interior assertion, AC.14 and the source table give
$t_0<265<1000$, $\tau_{\max}(1000)>0.998$, while both selected
$\tau$ are less than $0.993$. These follow using
$u_f=V/\mu$, $c_f=c_*(u_f)$, $q=\mu/(1000c_f)$ in the exact
threshold expression; they certify feasibility slack, not just $s<s_0$.
At $t=0$ the class is empty because its failure covariance is positive,
before any division by $t$ is made. $\square$

## 30. Necessary and attained actual alphabets

**Theorem 30.1 (global minima at the selected points).** At $S$ every
original optimizer needs at least six supported-nonzero actual low
labels and at least seven total actual labels. Both minima are attained:
four pure low qubits, two saturated low qubits and one counted
five-dimensional high fibre. At $D$ the corresponding minima are five
low and six total, attained by three pure low qubits, two saturated low
qubits and that high fibre. These are weak-class statements.

Proof. Equality in AC.141 makes every nonnegative sheet slack vanish
on every positive supported label and forces $k_u=s/C_s$.
A strict intermediate $0<b<1000c$ would have positive weights at
both endpoints of AC.140. Equality would require both endpoints at
the same direction to be contacts, contrary to Lemma 28.1's disjoint
pure/saturated zero sets. Every optimal supported label is therefore
one of the six certified endpoints with its aligned report.

Take the six columns $\Gamma_i$ and rows $(0,1,2,4,3,5)$ in that
order, with zero-based indices in AC.46. Exact interval determinant
elimination on §27's boxes gives

$$
-0.113788<\det\Gamma_{S,\mathrm{rows}}<-0.113786,\qquad
-0.018404<\det\Gamma_{D,\mathrm{rows}}<-0.018402.
\tag{AC.142}
$$

Thus all six columns are independent. Their total weights solving the
moments are unique. At $S$ all six are strictly positive; at $D$ the
unique sixth weight is zero and all the others are positive. FA69's
double rigidity is about each existing actual low label. It forbids
packing two distinct effective supported live directions into one low
label by hiding a Kraus index. Hence at least six or five actual low
labels are necessary. The same zero-integral argument is almost
everywhere in the stipulated integral class; a nonatomic actual record
already has infinitely many outcomes and cannot improve a finite minimum.

The original sharp-cost equality fixes positive high acquired mass,
so at least one further actual high label is needed. Section 32 realizes
exactly one, containing the full complement in its counted fibre.
A full-$M_5$ outcome zero on the supported specimens remains admissible
and is actually counted. It contributes no supported moment and cannot
replace a positive required weight. Extra labels and splitting are
allowed, so these are minimum counts, not counts of every optimizer.
Projection lines, the two physical failure lines, actual readable
outcomes, inaccessible Kraus multiplicity and joint Hilbert dimension
are different quantities. No six- or seven-label strong region follows;
the separate strong fixed-source four-low counts at $r=1,2$ and five-low
counts elsewhere retain their original scope. $\square$

## 31. A transverse local activation and value regularity

At $D$ let $J_5=D_{X_5}\mathcal F_5$ at fixed external $\lambda_D$.
Embed its sixth endpoint at zero weight into the six-atom order:

$$
X_6^D=(x_0,\ldots,x_4,x_5,p_0,\ldots,p_4,0,d_0,\ldots,d_7),
\quad J_6=D_{X_6}\mathcal F_6(X_6^D;\lambda_D).
\tag{AC.143}
$$

The interval domains are the corresponding coordinate projections of
$\mathcal B_D$, with its exact zero weight inserted. The following
complete rational matrices use these orders and the same interleaved
contact equations as AC.131. They are fixed preconditioners, not
assumptions that a rounded inverse is exact; $R_n=2^{-241}A_n$.


The integer matrix $A_5$:

| Row $i$ | First column $j$ | Entries $A_{i,j},\ldots,A_{i,j+4}$ (last block stops at the matrix width) |
| --- | --- | --- |
| $0$ | $0$ | $(-294778275969970510294548017805854347440771281124868035814722139411281457,-120805002962234429852507013967766310956494444702301534914329819550713739,2121881887055382832472923828308100506498715743110626580278088459614550409,179514633827224007839411491829483211555325569043325499272229399209026795,2286626160842795751020744473991870702700151152547426556814507659125885475)$ |
| $0$ | $5$ | $(39338063563022202163863721912266850038623431892396824446158645051223575479,-42628628477776391234731074756904901594695635686062645313784765233991444563,-22191412804457387938153779342580971027062130014886732662608244224509097333,35062686469082240402005106478353530166353594445835380517996290265568755,121099395872083822945869042020003593789666294199474514125366380451514823)$ |
| $0$ | $10$ | $(3321737988712432156561817537375696683425250106622093954384514596282410007,686480119423301655055073720310831119409039089690779743762279868783753493,-3329013830448301027427569566626630629469660705454480617636340705985808905,652733933664330425499984058373083151706575371635359437265499397309739757,222017153086250591847950536217380852583224440711398600105615059966854003)$ |
| $0$ | $15$ | $(-132277079720381489538820462518543694084284485099256129011604118066717877,247707824686329566216949697032298461727624711889282725707969752724516167,-143855902832794298753688072481614703505887202254925278679190822452908117)$ |
| $1$ | $0$ | $(-4698576759669851113816394311716157798559902116789095600993334994575142205,-385737421930763496990952870835732547863365863926855905780589122761544729,701600395125681124858316540077477218583102792571965896678242885651411817,5070327037437419295693668627091159026690544195742384854731613145373393511,-179479563628641841567567673949998833918145711522367651860062072661706705)$ |
| $1$ | $5$ | $(81132654169737932559551793097476869975766799196411539029511965142505125769,-92825433226026932631738904912138894127983163617834093278314128268373092621,16660775042069192158349866793803842725473377162794659409410005442761240581,289711671496293565205699439593651745144427200306246330023685184815896077,1420110895141850456023343331677149330873159838987900526851345243343256635)$ |
| $1$ | $10$ | $(41985861672299841503402962219343352205001848020773668830627364688767339753,8616434111701925678277757665835718770439188845922666798084357699924364089,-41997873599561568939648778597792394686461694674323849824962114353333434303,8399558776774917656056653935325431242939416440293771914317742657923764679,363644379489592564570475932382507285130040761450947276096885558558970747)$ |
| $1$ | $15$ | $(-216658109100816210187286717859606791938732763635354862320659190326915439,405723417990965811188299349347641519945401652326747709114943886178926587,-235623193047718993802540383348174921844766248541492692582136706117109075)$ |
| $2$ | $0$ | $(4387564280010639843605596097833058923829569689609739111122257017837363917,360225134379237600292085460594448886528549473627436980861848318780878507,-655606717625677608126743454236643853865942494112936873001806920585743433,-4734677491125251126688756313221597373858272609711780952864370063259124911,167104629298552851545085059296841730494003658458751860351480898503265977)$ |
| $2$ | $5$ | $(-75769619966204230367715092547997436435350200556719608765429998895883270255,86688970358124028874352745355294615835739347832398038506118173302718873431,-15552947728894425729209010843648911978235185242378023101808346062412699719,166334511991186631970835201807342461015757322929200465128301479943823227,971754322509632715219121565325348164556073692234637824395902420580854699)$ |
| $2$ | $10$ | $(29526767422843426568419122798533985038667267406822965806777296139144115275,6044807412381802823343763228530124239128872154064243013734689173904333707,-29515727390454444777952854438730208749119681076477701982516361197835628051,5943392524072495293058413132815602061210684395542147931529210947633386973,-339616580780293720866040813135410848630048941074296131655442293715020919)$ |
| $2$ | $15$ | $(202342426725858152193017873874082136451460260595209888368504166378243861,-378915247236838569447033580135531783141988019243568461821414890674083917,220054392942134284760285790358444140889905557805848106988842832425350861)$ |
| $3$ | $0$ | $(-41439252990870953320520247108455759911334373284668498129970103854227929,-3402789783735016839645060632356744899736279800572474271226055508297275,6204260381524055859109992786599752850063705939719819969745804320671509,44716818189896462135970544205511086602025208324234724472290765573799555,-1564709185100371236347484953585221580126400664809803878449437317711677)$ |
| $3$ | $5$ | $(23929385244601533298963850859096620647720988890448290918627790464156223331,-37417026232067229661407258471511747889215286598240402557151387637516134441,34846842719346855064722608592958208162365817335247499707025939942875785565,-96304962787104139771253633507661173564917994973263537747300151487167509,-72098436100523403408279232834474976552403726475174604849498385058678411)$ |
| $3$ | $10$ | $(-94460507377818793913469368221464920297377747867302559489518325353350307,-57084986104935325568180862785500437349899018912759061178125240731801543,144319262435263433276023022347595885415399242441436238289800229169980829,74081183195934862515173140295919430169591858956536522730839208503226345,-1523199963998155392012314579695944779465754045573813721474058513544185735)$ |
| $3$ | $15$ | $(907517461002629366435176453232927629234734014106024945733912240483464655,-1699456750973198148029271336326590697757875911417557587260464714744696431,986956651636321184614405021257137522137663202975523107931631374539705859)$ |
| $4$ | $0$ | $(-63180047849859880291246940054640351549734019847164905129407182780529641,-5188038051910698276503580683112847893183036512808993794920162466347251,9459279294055661866699800896103412514242712271592089222813511734406041,68177163173128040262627180870711431069438275370017398510027014318115453,-2385622183091359572503434654392365529344789292346809309718127024881511)$ |
| $4$ | $5$ | $(-158808192332448865742312935409011122678136681885672290401351323096705330675,250845966784798714326833197939072108095823953427888030785439736640794969085,-238797255530052294943145340031537026056844297754046904206856445686100062259,-146830642878833710712946095406725233506832451253893925607354543093140211,-109924342596972925170510892499753193245018766444327207705755548732913305)$ |
| $4$ | $10$ | $(-144018507702525075170278840621002576802675300596291921691703143821562855,-87034198092637903391370940761175389376801996183764896949159156892535485,220035286551259542993540041172125760523104155726326812499102227754757345,112947323160591280224902613440705089418729051900095688995860867630832391,-2322335458882644758420142041190790593562540000846587244867841358299764573)$ |
| $4$ | $15$ | $(1383639724957416170160799135021282975993054789515676640049888195547920457,-2591064053903385043466927477465556476855722857765986112090154995204639743,1504756094176148633477859952839437319001724836801658620488305718158367373)$ |
| $5$ | $0$ | $(796272128406617344682524708227085539209895531309786961581203821517223085,1761363310991664160822052754293617824400971228947939070048930553174905207,95916124549745395485158311520909560544234005099733294672033313572295735,970705492959685318498809902990483808750962673034637398138282800284723213,103373719675635200785574668717830384640857740725040418560220008212027725)$ |
| $5$ | $5$ | $(-17876258484965735935433078962393339688700589657189939722346872326796592347,-3139664507465279474929227818139307611032121213045279863990355229036798475,7038534022669149801948293918977144500533968407558123280803511985515106625,10702925522055981159219880961833220001829948100935436007012641183439511,19403031146370890080172030461910392607915949136185505995228923554299217)$ |
| $5$ | $10$ | $(405268562363814505181667996414381109272739000922060519084176025211448601,86286303045274944136519710082461641378545211249134805082074874502767081,-409503490398227130885228140788608802194900391161789378897063726873260605,73391333490363361121407752769688273411433661762935818727600514559691919,129346862187079584374457899922910984771941551521708842034333509151790439)$ |
| $5$ | $15$ | $(-77064429316660373408633653442491949055069452451532909857109148887831075,144314209136429898398513752206779976144102375454022658461538252913106557,-83810234388883787858026166173691230640185806666616438294937925263080497)$ |
| $6$ | $0$ | $(2117149285809040972338645171624845156510545262300789547180560073081965363,-626201501700469971816840244249884550479262328243863925025077606772079671,2193125597160313410864653201209302185342967353251236148239130494046530153,-1485368225177344578343368073796909084892999387285767318318217797321615797,-2397076901131098635788403666809140002077245778350035186421584620556433621)$ |
| $6$ | $5$ | $(-6022627556364633221363737958301498250031036313421869532815018494636690471,4314891545865526921060899422677082714357599364517074310375799925081847603,4558831830692491590321236407691637895576469464718153907042451951894797403,234597635412109089645890663043718253449038454806438861005115899267421717,1217605260461037632244117566281981717688622083312561033252816000471342321)$ |
| $6$ | $10$ | $(36343314198309265122177219307012046607088140178029705654716940173548784511,7452080991747249171887517954130772727943411735269710553550270102220844879,-36345283054004774029631376531230205546515822927707362905525902333676651015,7286455403652885256163848683920653128460519025875822843082117267610761457,57270922992323697214405010096909540865308939511627085816582389568877949)$ |
| $6$ | $15$ | $(-34121825007693902374423109572037034613258344166043276016501016287724339,63898016684753892496814148904797980610583055466981946329612510015407297,-37108665788212851752948350525234405092436105953988778926344001910206845)$ |
| $7$ | $0$ | $(618630810986335637973094916199054222751587405086173493170782985986493937,-1135296634486173650229400989516910255888760290911520947276144390944961871,-2288795896763821849272332838879724641251184532012251293328486203893576381,516434500124137551273670916399111275870890356301958555377064687038709653,2293641184613350034689850636257723853282573864366327154927433426074389717)$ |
| $7$ | $5$ | $(-30523866753876795125241925476478039832660485456256057378322915838254110367,38565040491006245069565809788645864220105446634573810164444870408517184261,-15091438215009733848434020690564583149480437175823742777267989813318794923,-249116352155628369258125808711799350282901989700169107374754507424366781,-1239864972837448404879555205065703596995356826149083748308574424790246193)$ |
| $7$ | $10$ | $(-36752325470959194971350375142859899976625565141725161943028808466195107153,-7540629113732614446309101560646423437272874529719595069165829155515060061,36760504756203839709209606310868143055639677740746861652822604668539091895,-7356911495590437227448468910067138515486121764605147450959367713510549047,-246969950664437524108551916498103425486824817916498261252431700755888211)$ |
| $7$ | $15$ | $(147143873337963394368220822314362593754273109447339162174919636044460513,-275548030373183695796683169486597698006274127538918716551136831039002143,160024055490888835666256960519472458033515130402520247370745505982736929)$ |
| $8$ | $0$ | $(-1410453615771236209610610691916102961267086368341719297085750794919903,-115819586690807380426746294287160793139601299535155754834030205266393,211172278859240914577915772445101621529216222125586231187839847465119,1522010976298703070524081228213114237047340603324025495690516501285547,-53257468908560515048503356303178487644349636482147379995636929208341)$ |
| $8$ | $5$ | $(5505169518966991208296995224661735230969522197047066018076703580996789903,9451683343036169764390447345655161783417331443375441165318927591087489031,18193290256213836860130482589365769597161476025655287766514499138385271283,-3277898928576474969711408161230288220926663141087896062764085087532485,-2453989696962859074724816276731622447012973139085207007190828106697259)$ |
| $8$ | $10$ | $(-3215119833554456963758414559805891139081490454231283914291112632604653,-1942982057994490911863461205595394569017631211446107962298085721887473,4912145148275198306080319669244368499732341439165546022204349121848529,2521475778589356838900445691873366868482245155645316784416090961130465,-51844633812224056617545567280667756766276461472110113406565061536577751)$ |
| $8$ | $15$ | $(30888860002584416423053658474064076504840958835720314592657487500852801,-57843825509717650127882804347288149301180159468632423419561243948317729,33592704439353454419539624216850277634461676915466939345005196103421955)$ |
| $9$ | $0$ | $(3052357970545940381940816126767384730012858491547081948836986157755855,250644781670268604615225767464465943263568679370272282828776263350055,-456997225096197992056589622932829612279234867676745055825171595765239,-3293778882776994499636826820898607932171584935109042220289464242545625,115254311021960828026865189889640842326311129160287604884336911437027)$ |
| $9$ | $5$ | $(48917583276240173073741747172511142567415489616396734234342078558871359437,-49191950872442662280087928738838804058488139533946121354113915723401495397,-14699217894565744403965992225469971774407141819450759423667483597437147825,7093690150039773422726672867478098840415967120325236679329038362536383,5310670927002741629990424598542760653113659068217983471054581309048399)$ |
| $9$ | $10$ | $(6957830119669800955246253993267726257850110380219956578184981921098585,4204800998084821196927357638782325303451707200304206144513125444838639,-10630356949113746999081958518562650281793226640655575988419328773896157,-5456717331400746675687972315078344439281782254195861122250629535977423,112196799297258299137234573758950657411732363445086651112472272473811447)$ |
| $9$ | $15$ | $(-66846479016193535008217717773897687064969861053459655623310854754456443,125179630061717555029238072722307891440745712527179335694289085039378239,-72697859753145650474822068037397100451045961540550307323748011112029861)$ |
| $10$ | $0$ | $(-664608589728228334864024526911429045365884987797782375868583791645718771,-54565033611752660758443311889219852601231978907906920212111341961135157,99302849212395295624855665653728024641624954488551534347668721926051163,717188112787019760427501625255122719093295181971045077885560513739072601,-25318366102202261082776015110828500642449410372408388060924005608371523)$ |
| $10$ | $5$ | $(11477151746079156588684208347926387422052897868180273565632216871197360795,-13131159253321390008643821666596195669968980998915971125648958350341886535,2355952612673924758965679857448656984532429047825397499672853603977719347,807880086286294920328163921257349768731826026365391660284503581374503613,-118836471074689954347094433606175376484327248820347576333157619489399131)$ |
| $10$ | $10$ | $(1017824230846923058733189057427506401023864314184824338482870383104316361,-915643261245034555188851726350055322935214440390748268475288970661014003,-136075605428700599762743736474786016825712402866486080017458638791080153,1188112251188798710681828190264710144546946670652528936354851496914927023,51443069608789340043282634969134358791165781872868668956513021955476985)$ |
| $10$ | $15$ | $(-30649609388781842404767328762558498267865674105369389336132106728801013,57395794382744008571677331904507871303109723627252218145020054161130293,-33332511115425950485078715615114519758667260512293350587880779078167917)$ |
| $11$ | $0$ | $(-54565033611752660758443311889206724362172843820836089225234157490320069,-4480196586061256737829967639736912740988004801769282307286232815100023,8160444630143283330169648039830281868150086131733696257894131675982347,58881359718009462311270550179405084766833357466341774346148094937740559,-2070279757191690024494834995099855173956710126746373338696595849027385)$ |
| $11$ | $5$ | $(942410650541664347658692836021369921242455888713397002810775791690114753,-1078215659173351317740726872705064767579797831383128964328417235150403651,193341302663687977072472444915922917523713708529084204134547674716092605,1764053191001510974118181392721417646005934201341055670155879282581679597,-48701147304565539545203910637681318945062984008941560877603597054587633)$ |
| $11$ | $10$ | $(-625684685427206710878802836531945099238864086340628150983263174180611721,-75171246329868175965672264921707441598903875310467811127700388892346427,-1141297781163522041437375051552141481213494866999478391065889400642273005,97545669539698605442323165915769278133041526928777213349536194573759225,4224254518953831345213219681310469716926335854963872979051368591804241)$ |
| $11$ | $15$ | $(-2516796760950098745593539570943776528199817595836342085578099972313847,4713063307342503355559117227483461069829010669386082314047401354981025,-2737103593899061391296322567088108603122822825528474331158287833099973)$ |
| $12$ | $0$ | $(99302849212395295624855665653717821532845074458727889987425662901958385,8160444630143283330169648039831903268007115612531670867736064199781141,-15000444419590302990826257795546063442502270270994549924072571687653889,-107148171610448615928771715634398920576081706648730289542844725043619997,3602635679934925975903136775872691017853533042474573644240908533339473)$ |
| $12$ | $5$ | $(-1717552324462435500631176579497289544822723994718214648934160068464719233,1964887397923857263907047983900537269457185220476750791358701011430064329,-350192477474623579226793290451065635826291441136770441545253620493908989,3964290737820878036960704096002355796413398404022485693534908072029567,855412274412830654887054723028419588287046788541531853509033369132502967)$ |
| $12$ | $10$ | $(2072583265409460699784456380810482781976428201306050958902286638636715633,136725588777828823126252148819497621206796119674947905861165319053106983,-2072397436943784492231119217911826897615953135323699825342546654396008743,-177532298893374614103355529351535395351416075811247390337506939870264529,-7702025872621498933933171442500554022731939040890514701714508370375859)$ |
| $12$ | $15$ | $(4588841340404921509202649956440114226957972242540200524940126060169905,-8593264295411114569629096171168268732515853973019792747984507082054765,4990523795776583254756750735363137965592239015404402173891211984714783)$ |
| $13$ | $0$ | $(717188112787019760427501625255109728264118013935041895399922679173387803,58881359718009462311270550179418176950093047214983009032067404711216113,-107148171610448615928771715634408529004630142512228637102604883596685343,-773928112187553764558715462417113325134604353027361251380627474326914355,27333417920404734061725381660544296389631564938070526289352959334710655)$ |
| $13$ | $5$ | $(-12384970338209215024666751518124430347476507852909688177786268918060005247,14169818813815249376859464539107469491851435366661560438991462022140974323,-2542461927707855464397183857660080783567384604495950708041082841197097117,961539553116139503755053677395943316265783388770244699779072307324388235,72369259641323353694805627096066511780970754678499783552218801935473355)$ |
| $13$ | $10$ | $(-389750530179292868330894115567516767323739841927365712507069775128502143,988088738698032766446807971612103387891455491498935594145022864218554801,1274984816973247348939363406342875168297309632512777629515338940301153797,-1282107331911297769839638814520581190329078170727933519265103579081711411,-55511869177110684986579280269927709435062802608161412927055555373571849)$ |
| $13$ | $15$ | $(33073786608350141328863775115214662680204604909545870470268980576263219,-61935414300138464245861660021991016796660788008924427833995124666707209,35968887752140870168288011897653026769134794549051045909992913421859501)$ |
| $14$ | $0$ | $(-25318366102202261082776015110818460549050573946227888723798491290532629,-2070279757191690024494834995098983232457352885058059146808464396877951,3602635679934925975903136775871632089614317068667907490920345438018025,27333417920404734061725381660534549610284812605917764503597438814533573,-1163922538342035684883885723337552166801335789163587237475551268111673)$ |
| $14$ | $5$ | $(434251741862587990959919069010932563182232655574562523317654996252966455,-497039510670775581500661930885112055171106647280882606611936016006252743,91766904208154993339918128059115681383055655679480851207965980454989487,4282671096349298490506178445705709962497372684582672982378061190429215,921827033309965595274426201088935398885486720558777689932782343121141903)$ |
| $14$ | $10$ | $(-2157926779706698173838669229816001107971419181635685318535327164560390377,-34976389952457160674062004653278445783265806022388537133617971431584045,2157791808438690208663468364327992068909583352237155529522483730162596323,45250404240115625343733228500241024845660944211961195371209518116753031,1942444366561412361573896255724842756274448986974812359559478483841617)$ |
| $14$ | $15$ | $(-1157301878509503702468871927363849475644487338029190327766295579828897,2167213937871815395958398093414389112427881142537712938452773136356295,-1258605851709177210165900182766268976489593370637670648553824731049425)$ |
| $15$ | $0$ | $(11477151746079156588684208347926236703990487715029041063864847420080156415,942410650541664347658692836021592355176318220197714123672359442684049309,-1717552324462435500631176579497440978696016223119098822162869406605340777,-12384970338209215024666751518124483308018809912514760977670858009249778681,434251741862587990959919069011101820572491151361446134284875350668048639)$ |
| $15$ | $5$ | $(-2178243517292565841256813437168477265049484475518230298944187083754128544965,3348440000756175288476314543212017269607374724983166987171345795261387113909,-3000397530703792598138915032719439778568843227441810261942972941472949885545,-19552661624865955270411494675553440487853954225548437243439268627846593591,15858687813268950232471990090152945402072052778024629468743691253394425453)$ |
| $15$ | $10$ | $(9495499105633211880315134045846697275791912491936897962863461351232345647,15810866110584587266805953033817023203503748577705609094468580544529470553,-16554599585714400430388699503937273797258876305665891125225132623963319105,-20517719628610968931123696613150622990144108955319100943642369826094350767,65904231132510151544249132532999961925698502970440585447440299734064440153)$ |
| $15$ | $15$ | $(17698830401751940082827965065050515240395359143905300814081245054662701055,533002993749273843182620448780764519876042616982180653107973320760002304523,-83783979536093273248352548207735760428533142050331805720900607787333428685)$ |
| $16$ | $0$ | $(-13131159253321390008643821666596012759588235954487510483130000610678737629,-1078215659173351317740726872705318151539660116281753636280319320842199241,1964887397923857263907047983900715924089477174995628870816934969565387747,14169818813815249376859464539107518937205654930514190273519592404622114781,-497039510670775581500661930885297666971205974932617117817249503465046383)$ |
| $16$ | $5$ | $(3348440000756175288476314543212035943332058105715137150361535436304153877797,-5180995116177994877122249775649794383419449201898094701834078634610956404683,4712789505202111456583936496770128751794886278993211607839335623237304275265,-1290604265314870012715464308847301458740880562452730804010932722261524467,-17185241206747008046952755692115918468572343730644057728708358424750497745)$ |
| $16$ | $10$ | $(-13147461280619157366466629005850557843032318833209134652712437689629728479,-18089516624505400902439437154831469224885722514130567405568132596890617877,22410778024958434799462842266540877541664608053281359874357699411516232669,23474579778733182698691417276216146417048977398960001753969235617021090159,265062256659997201393486278831333681980129633634425122328402542792088980721)$ |
| $16$ | $15$ | $(-27674660032006549681695808077330002449444164272251794575989020134969058925,-577292101681467100021472588988516593625331117599142665324459243977354925523,132341241589177041685263547039646159995544824858802766140741934355921986315)$ |
| $17$ | $0$ | $(2355952612673924758965679857448605299433926361080491864396961525134647151,193341302663687977072472444915959816243229214445483188907137346356199285,-350192477474623579226793290451097694590481443713765400593301436356876981,-2542461927707855464397183857660076848626434837363114694080963129130196405,91766904208154993339918128059145895572505973020119151750822128827826465)$ |
| $17$ | $5$ | $(-3000397530703792598138915032719505104077166964311454041012262233332749624719,4712789505202111456583936496770203977142243475850241473564942803067067135085,-4432653086371199087019385643352740135714324381682256339216389394774922617587,7988615293499160704892334545976032611778636683030287340826345422645774761,-8946212800674819289977996148339314958117712627153976507553061863406489707)$ |
| $17$ | $10$ | $(7087958727031222530226461327857427979342064476176632386633110519420610807,3246797312184815602187541759166729355953894575329964149729645152645570155,-11807599225823648929129212953816037252851928947015038839238828106341348115,-4211595901394670769650618317211051664949870749299501988127038703118920227,303398940648598393033822439939675434513834809036290129201979090516823496973)$ |
| $17$ | $15$ | $(25773681731559849815818466947519833062756040874308529737409040262425501777,-30337944762118126739337768422228852646217417665207520237624019072130079179,-125984586038997944001324483543096734417063501923199059782353939270156805931)$ |

The integer matrix $A_6$:

| Row $i$ | First column $j$ | Entries $A_{i,j},\ldots,A_{i,j+4}$ (last block stops at the matrix width) |
| --- | --- | --- |
| $0$ | $0$ | $(62153330536280780412898565383985842823964330429411053190272487079447895909,5037974565581272415472389860584841723362292217110216896467390854770283843,-7891250782835207990569031401994498766365618668830207004919889456569982309,-67163568981599328525183707122244586721181475066141266737597210638571091883,3910921815342727544770448445492925021637048556157518815561427321616099167)$ |
| $0$ | $5$ | $(-1050328535129321647067018821862384645940583751051736380782692182604055353803,1203291981531627474393307890272639102013743483260102736830480383105413324335,-235930570560969482435894854613232050634319553626575305006286964416864667995,-153537129927955767060743660352179086089826466182392201282400167323269776958381,3517012468505612436955326319242778942893815771589162036300906849571874110681)$ |
| $0$ | $10$ | $(-72765921846866554784930176094606833049952476407472344644428761803627537437,86363529575656594733054623479464200095416662717024643095839184544604621243,72726399682702398023510135663220443098554706988137210099566728086976288723,-111026252845144370347737094751273682698941027052342155276557452732375599921,-4677111130653584040120145063101056444204814946743968987535085651677719407)$ |
| $0$ | $15$ | $(2786607220615072109861325691128582744778800945837124211881479211419694189,-5218322133607105939928697333855749626218193584889690923940001132808107541,3030531807999976937889887817122547027408443277847003482680701185513725473,153544124559510315393143836987104872105292356395547682851052726940182164549661,-459204937141932775121930432864411702054044140217609)$ |
| $1$ | $0$ | $(-1551414508157213623236282933758943047732211728537057809651805013282365605,-125753306626221640846575231717233078969276291104430095246554575807660619,196974174132971593830705702560750727799537742919979842202829521871474629,1676475491154044789022839768619893803066267907964647010126278390777258759,-97620848186880253138531892411717853998382151952845074319867685094491547)$ |
| $1$ | $5$ | $(26217338856522864852597200067569403631655624051235818250713326438297188623,-30035472300357234142520678054400196909126505628116895510790501967233706153,5889082804218138131361710321678628312931116998739126367250940696673279261,-7737436523010313061629725297660432744003945423744291184371943864390086824901,178658909155778116681523180498770004953401006168476972247982046271960896491)$ |
| $1$ | $10$ | $(38151314631645627796694395566675652175875075984329986971750228663013363343,12934252232988926925664045655541314687050564098711517899151879622077594957,-38164951658700233256569569143653080990212268843579137863465006434956757717,2771335630191882855685482234250021853941478109309234554780162533091772679,116745764092624641538523381423128488600711270806076097634025463922705245)$ |
| $1$ | $15$ | $(-69556737077416944989791495532891296680534667817230559226493308787550847,130254977431824311056762196063620229937402437667552518359082613359128667,-75645359207558521812632409279756914869030136193342876562982081612927589,7738076972163616406385730771751520987933716449277064119025147071490985418445,-23142293199402923406136176009620828698343193364017)$ |
| $2$ | $0$ | $(1435321344395418803043380243347752077881711843696222991506659087797071365,116343120539276953601934513136005394938646573444033705080271798907574643,-182234493064998699885596838048800554194938983345852046963461820314692427,-1551023948246687090430410976402161293855081965258393546219145297662173673,90315828763936741764972165809401065770378295912631298079183435849782121)$ |
| $2$ | $5$ | $(-24255481598346222343804556466391787269961235442686310260430987617259375617,27787902108062193474647927740493841547151550567369448999054465620415847199,-5448399640046268226015644826173809702907929100642126549850294920588992019,7258656932854822295355713495975930284723711614877160708469652622426916292417,-165289769000732227485417525251370667084484748859078031499942719511112208559)$ |
| $2$ | $10$ | $(33123822009595226413013298621387286807287540445477667328101239978414388931,1994413112019895258168337330452724916720449384925048588425893936829527009,-33111257527877047195577927865588544753027392471725814794378945240723892113,11223031988666243070161827804820185887036590959622464296194001430891345937,-108009617151856509531671178549314399347110019227565715159305797326449639)$ |
| $2$ | $15$ | $(64351769851825949502983476604670805693783296216345225209512299929345491,-120507928950407570666733975676007809420648372181002740059489641557980493,69984777185069813391065325696073570859730730446043307302344118990757061,-7258819612918556481385274162452974283416482130739407654735538297296267033031,21708976580103437847875223735487153650442630923301)$ |
| $3$ | $0$ | $(-13189252257088542449200475409491383230400798842668963197205512037456717,-1069083777762484868703127063866315292073650457006906334358552910851425,1674563475532602790722306167883348635908994746730390079606664516809707,14252450289330689090300321383031180247774606212278032923535300812640131,-829917462752793848554868390643595010794272866220447780709769343023875)$ |
| $3$ | $5$ | $(23436446662503142678278280331780572780013014580980906953772777400004943181,-36853402147744351497647630244701118068787987085891088315685816997672538993,34750152339473013770985357364148473345819294413946794872937860435191952063,-69552772198470955243218418733691124786995571607187564368728970654273923189,1518857409442917437834951100487775409599276543781381410340300337142893779)$ |
| $3$ | $10$ | $(-128880708198459491135435962339059346982051854182227171636881138521417923,-18326779394725307180030173675835282469739747814576309763061571171367525,178724875806426681952563549687426496753409656199666067874433921993321369,23560334471201286197335751496611673401063219279809309224557081784696269,-1525416210098203722260666239765459953221162049964347439878999110153717833)$ |
| $3$ | $15$ | $(908837893041239417010825476567097906516964766135435687327062070174955781,-1701929449558785639499627390247609658596389146312620582757361089378889173,988392667183724653558804328159762936508443219563148775805712661732285589,69459615574830856280983399933367319881976249821650085232601749030279838813,-207733109263850439889108824934083124755074122723)$ |
| $4$ | $0$ | $(-20108895034625782971670984033330854748051761201604259050606458696666145,-1629970604185911313695370792100175097244479776240370260218750733032607,2553110707258284217402257289644486911366837652773314513455922106853041,21729891980823964907091436271132395095649835968644692042750739254474869,-1265327466682545020487822345623873198518947470814701607175332874387047)$ |
| $4$ | $5$ | $(-159559747463302199036812992309000469219066940191807440855895380843051042803,251705292039158336175070103062840533169667889073496740990317596581095272561,-238944673796216412571109784589274632566548063094950872669966360057718991429,-106043115124634883812422189577937956504566539857079182561332410852987098699,2315714615484454088235473997866468259708768392436304500359657597705790251)$ |
| $4$ | $10$ | $(-196497010037713025279179681378337722486717944344936891980398354130723727,-27941787448428495662648398667624670409664175358133254842749679670030899,272491548240454293164637628715587879462444524851696335674410296250596755,35921088142615064324557865377115101295187727971755841892080990296431503,-2325714441961296435536512352101343285147234131368328577031810520864335951)$ |
| $4$ | $15$ | $(1385652911811924611736159329533547699055089491439207942080495104797860673,-2594834035350447202002070926911284779686653323035691637772291731934447405,1506945504564846545738050340697448385844328387197826384988942805961988189,105901084573543399512147825177385323475446831144835099945622919523100301679,-316718734919801321708614445025250141890001126171)$ |
| $5$ | $0$ | $(-62287052968289692059425640581462299971034932440061634622238240566355148763,-5048813730683057500354934005691414604485679763645816970571661287005290123,7908228750663609044358391600702181961666620706481082500072446657043392523,67308070904651949509134063195460579684752687642549454480127242851542644825,-3919336134769086509044804406013176496309250611524345332616366338078398219)$ |
| $5$ | $5$ | $(1052588309222101182254687151832406680826653752424078162165739131227646653511,-1205880855350598531158469872920981174026069664960596880627790181004300852461,236438173442559982958388016527196444807360851008154898373246040720647416003,-781544090531158885197250728622881737850712019471926705769160447240792664999649,7172897300709740823552400661231956026812538138117994227427337866902075551087)$ |
| $5$ | $10$ | $(58973450909684551743339561904219963350887153183565393307323868813106958409,-86549340072247586253094276228886766179825871839547695281613764322051517907,-59278991641735107704227217576806751196192085450729999445147273272727435869,111265125008859275099238629779704109196309606256271736666554090215280104393,4687173900737994281285701145591594555034385855056842584743045542587163813)$ |
| $5$ | $15$ | $(-2792602585487381321360755934549730497882294956707514654731254918806155401,5229549315170683519606814975069232248967779277565775879442541776006167723,-3037051974822084149982281872104071970370156941873823620946742118834815363,781537126441037124680390281401167457941457142568256541852346890944478912194501,10674510465092080951089689817743823795014173694526793841818296386669847443859)$ |
| $6$ | $0$ | $(-1097160287864109332884148877436398433429328516389368588350338327712437690427,-88939796044638767860671500859836305728761524041540170903083658104335754865,176145838373356199973822955858314255333940159855285682556829830858907163741,1184990235179293008128620562987841113818372107848335091670045040478655123129,-28454834097110608807975331871315933503218760925505962081130429398881998359)$ |
| $6$ | $5$ | $(19140535629310846902969917934274053259301087428762409379864162853204150386055,-21908794343378082812396999413970005531437324056304067726878266936786447026685,3764979564576345465922454980740755314287708760030631303206125543318941810929,2699475474578915638037338372051351372003423457694668596258228299197058083106535,-61833621726187352147099273363620040132030515712048052621374218850264650672393)$ |
| $6$ | $10$ | $(1338171084691680935961737787818826537784856181826525447358441751598672730883,-1506279243101432972810208268566319867108184063595621139588756746257062928771,-1337608367923031991190089660864561699004986399547207642718640595990889824069,1963602447365620603111541471140609684488788194928435608994183226499508403561,86265342646286738623232181277434605094980923764340309819241059598114711983)$ |
| $6$ | $15$ | $(-51396603585381119333661527133366614847945270102682992718055071642940214707,96247519958204037244399663949735043350042396162054855366321822557869981635,-55895585440377680841732207648034405563294076441721490844423597001168117599,-2699597826337220139163710705244586669040096593612608928903909127043659233397985,8073696429010628179953927606284405666487070562415527)$ |
| $7$ | $0$ | $(853688220650720797953666099527612875938849449362284004669966383604217563,-730574832655695101996891348594750274697911933163407244952963491173553251,2395713049515470910946217530328729337870332412082666366129169265165606971,-122871173239383580917749881675450333722284377739195719010959607351046551,-2429939935045168388926705872984280529291223058677448273623830923197051581)$ |
| $7$ | $5$ | $(16023697746943647796737959252311837854088215800267130656154452921941133725,-20892792256984438340156475075037611510148628435278545985417773522206567341,8883239872207237294222450974430036663180892717392163890099191172678461257,3106625386885541740203235490090030944715922331530048908205161832923512620923,-69936756333108968803418366664445339163650383668487190714869984224223212625)$ |
| $7$ | $10$ | $(37882733046529141501050391369864352648009744296451202815017683282238965909,5718647934694307063454876688884974839965274948335307042924825591772681591,-37884049488986562232876119741815239918736723878068889078019512946151187919,9545964206642847341580708644991942289716629716625028367014132857905810445,156390943717545239965751526674399797938821016880660334602277857455243389)$ |
| $7$ | $15$ | $(-93177202941769267161923074165391716295684478777070227957520994483995767,174487691290526835696365949315023448185943355711146232179270912142842787,-101333433433497462325067143631825940364938771611834220558442957970640239,-3106531596465309558226878754931294158166088368502506972902963809291297192149,9290714643603228140408758945842765543062505790139)$ |
| $8$ | $0$ | $(677673124153508179359515036536107876389367688340872607481831199932318681,-1130419204494465001460339490417349585743045734088239849468619064395758257,-2298262933094058137720693759760986850041946186416041448574436123210620517,452764174343429660987380510914769526894086134170675299303387471263540767,2295176894413584191111860943262546936360619453337859160033878008997289949)$ |
| $8$ | $5$ | $(-31554105103627747029215191187949584097417673425323426008319249478066104935,39743011069086887386341553908150158512670201072398970022179857902513418807,-15293520464230258261919077635553811476991683079458841354851286108726027963,-145412669750252713902134994754032252208096894469063657980077723047534789871,2085222136112257294818931071254006638434217773292901098959768655461488919)$ |
| $8$ | $10$ | $(-36824263461166005784268746857918223291945677751422636752198318589264218535,-7459624720141724927850950616646360432536701801109385861101423782754916727,36832412258738509406839610957443128793325463825082741652909436037468488221,-7462499732560287784810967270613677504459164117428475941726573038518046951,-251601890235968233373164177022322102792928613728543602530076578865422339)$ |
| $8$ | $15$ | $(149903567494231275409001535449621556104538426204549374069409705578889039,-280715953929507584665880758183910794340458036533934181984762308226656607,163025318409842831379605465170414782028995654284233560594184613800343799,145170133405921710472910876689160836444866216011383735460877115453403657171,-434160813230695958392508038989622413523392870511)$ |
| $9$ | $0$ | $(-448918047326472482508678230274844430862588264182273341371815450266815,-36388037212921227254126937531240851659822976963676269535009994149543,56996541646726395705477061565263216188130487813117755840975079826167,485105753441424853008647750665100308602775483503251779100341876057633,-28247615525049212012081100520152615943307662204023905576054725092955)$ |
| $9$ | $5$ | $(5488391537818851583450349309524679384697646437192850649595568672369861845,9470867222336409229743337487263331821952572051318582862045774775171932931,18189999238976306114372298073418925000991638890218727341464381687941571719,-2367343809403563930942050975799918187729061317944017237613255362264012797,51696827774903148511791653760403480596048509939094486776335980433279451)$ |
| $9$ | $10$ | $(-4386668382311835978690780190885949157642860403422558457033420240077647,-623782293286672783219904271642285513920735649808491383151316532728691,6083197189026873642525132313256335652913098851063686295596238452999057,801915009206519000630418062686239671129096844983081800088192485233161,-51920067419242520614349276762863614815700518874016165844513345941675783)$ |
| $9$ | $15$ | $(30933803094190049806248355170975657778333616381347709131331075097564681,-57927987901870873095836083565169661307718764958807045038955821241204917,33641581607134088297522892026246451589024129923740082801329522611966433,2364173069412783604015241516016105755570361062422692485229068153993059819,-7070540464161997116760234634790625987715017181)$ |
| $10$ | $0$ | $(971502050515585657965797783308061900630073940022058220679738244319879,78747230094943376546031028375816787261881088662753443202571630367125,-123346025876795693553633033849726699232065076393033743370162163243539,-1049815744748877107016992506213494826239711028694080617032687921598827,61130570642449026118694528015825176607069472269526425632979499270233)$ |
| $10$ | $5$ | $(48953892449342041129836949272860669973595810997561163620636307015172046259,-49233466641719526266029469334534314120132801590020359244843365644730006431,-14692095815127004230584402567166229218213143405987667667238624459388616723,5123160850422146451800513937519411708027567108700869677909373090861154761,-111876932744351777698130843698977620260139600699938944346087928619545997)$ |
| $10$ | $10$ | $(9493174430674148133464907815981081759056945664322552028043896691250779,1349925182585951206210138866625231328364346768834937032315658016462559,-13164626768797214542668674631525597231065179200876666377352715608957713,-1735421599606109313551848380347882158299299370004702479869093784077735,112360044914877520056215663228782594438482480009072564559040317132675103)$ |
| $10$ | $15$ | $(-66943740210996045438500453252227168661930721875595983133153182325915431,125361765614164371015336284644507391115463209279988295223031310576935131,-72803634669090937767034832736381202384126035627411304191171117269702387,-5116299062572359535437842706484800801299316137510205620883427411817677559,15301333060890146834160355024849994217381308581)$ |
| $11$ | $0$ | $(1099162098064858683452826834182265008723265282562406657314842318117522863937,90800747722596045941979439794757354240781678425447996451487256582064900105,-176243222140293382677750631472909312011295460420859782477566006696115279743,-1185319563470405746756436185272322180669079654394208614833423995754579010455,28589564254787075605976070187610106915554339190981245438200110727818117345)$ |
| $11$ | $5$ | $(-19179447505941323696450728000920757118470665917948750336004764087729323097231,21929706723985363480387100466984113947152813216274744791428431859206159761451,-3762067187408171746838546249585875657775370331106446864135905967489423684725,-2702439443113091945646160331009642926545313554724797096340497853989897002222679,61901533440489318307237059138403028855154511531442420496506529213834403142571)$ |
| $11$ | $10$ | $(-1339234660783092433990674206458394718211738709562241609823408547172744133785,1508019493743991091396181352259482828171325058459790657216215611851899602371,1338667086582859814357026313191249036624700336746111888476959201624977616195,-1965684978333112763077998291084665806446400324085563938660552318434627652821,-86230571677263950629266635013552405096808221754013011974948747740732817081)$ |
| $11$ | $15$ | $(51375887157945463321046700770163519341937145352668243963603931612423549729,-96208725473277349993349649341945274302783168104200897211221907750614912621,55873055608463292322147181267205824038291536802821219627431069835843122937,2702561939926272686587396095724013107133272185406185486151895409430653013174851,-8082561213633597440285661257311630434517526196151277)$ |
| $12$ | $0$ | $(-217581440786886083147378537396651194179338161275798618636636322251306539,-17636541037603645221694953031401263743803190781854330946930364752223781,27625063695302191201239050572248652247691413732012253854167722999609985,235120885418608805127718461934999435918893019014386497857507413942341905,-13691044326102732799988870950415871200815168059923880109904340736714069)$ |
| $12$ | $5$ | $(3676906675815485921769984112968397650490447925604584788673740125881271589,-4212388954380004897477679063095463478371096820870888861470998646350925455,825926994183562768769808881730969736076367943394217939629511369377358837,-1098269136459629461470229261855839925375297058087426742135763639000079238571,25056400245799679427212591780614467354558634614825479390481131626502593049)$ |
| $12$ | $10$ | $(473160024150482525923300747234986427776719852427563170346462583655868573,-302334581821697805361968637034454175362492058996602983161003935620539825,408357769912665607104300865466232440252779750497188344699345264723765077,388671883723339702125310114061321140449663307676212945560970115305011893,16373258999112750687833850745342729549562474256215544891493977653255641)$ |
| $12$ | $15$ | $(-9755133131838263653669322989581264067572494044054250664977947714943347,18267887473183087991326713466613967390281729978561770233717321308146059,-10609044944907938221053836368964872886897878590525639798698187387099033,1099126835768437160734188413849408711636734655928587035688670341339857772181,-3287162377446989742447979724408778474795801191451)$ |
| $13$ | $0$ | $(-17636541037603645221694953001629615085859311096935826686595062561304335,-1429568526829172029334915164675428869034238331709948981005394992670289,2239210144792719437630081721175781857370814404381255146182939428070691,19058239202233129427570315500150222609469930638887722225757067053358845,-1109757634804276285230392139159359851655178522322329422048525596419733)$ |
| $13$ | $5$ | $(298039737419401666082549239284471347905170360518351201203432354528697201,-341444428309663714541879041155313478649372987123630585813176306394853151,66947324525028945451805991061744694056751083433870699982753179368268441,-89029666027290217027982973181779134441675644008398071281071760651760511499,2031001493470680676242940250793620637884681559028445326976663555333692411)$ |
| $13$ | $10$ | $(-670678883564898627809295890875847160082173724685885513570525620538217207,-24506392825148004005751938615829457504800472119967801014639630383448635,-1096322651787094245247913187566999182978316191320446974016152533304993727,31504652247263463872983624923026510475299017224063423629451555011097271,1327170429669154099646256104353288377274787343893614829857168993643877)$ |
| $13$ | $15$ | $(-790723717908765648576623092396350184039282650368509366263869414644789,1480743697283842239743487967073307295468063170120519832323809241846369,-859939413324849762990684250365073213861042137671871641830878395558327,90797834737434778897168740513069087455944313543384098677147578599116973875,-271549394109621874565113182111412705343234439829)$ |
| $14$ | $0$ | $(27625063695302191201239049931660406962754730852416503120283443894194719,2239210144792719437630081673031431182054397728321168346223065489711537,-3507395398291244549071597519987212620454424011783757987060644562990945,-29851946068078396424369223247596647160657886875642802544479939039827683,1738273127505593882921079282924559863408871647106927733838292245886715)$ |
| $14$ | $5$ | $(-466835685772362473796687183699147156962728559637554149672371265436878155,534822789817414670792067154830921961814434397554099395050406457235790523,-104863198531432700882481523185252008068974462505508115642890905393539557,176233544183841738462469599091567243023246794280124110957315995377888978517,-3181266978754745403458664915392087908677476904640325079824132024496960537)$ |
| $14$ | $10$ | $(2159916494003923316695421786020815216906426419021789768535913073957909077,38385682390519129717167056023120436115814478472388421206876325862450661,-2159693653288770045387377426881119153747884813247559084192124250100292237,-49347432876625589402745631023460483433346128085635849087664816483268507,-2078818492580875463651229956350028872661258928595347654990626712457787)$ |
| $14$ | $15$ | $(1238553128192296923198072331009302118910814719444662785767542571144875,-2319368569305437799018684356888641810392799010991964626327536541562067,1346969398168768648002485440353903625390398734358345536892796018326205,-176237568069112856413541622711392559779498738064616737332300869432631460359,527074296065674010193546657646179654633279967275)$ |
| $15$ | $0$ | $(235120885418608805127718461977703833821641305608232543992050335264502429,19058239202233129427570315535783290535145537391051345390272737814176119,-29851946068078396424369223945245245236441593234505037117920306426389119,-254074201182339438689745795850143341404503826385509547573259323378968025,14794692289089351446613103715157666403159083251012122820239297786604245)$ |
| $15$ | $5$ | $(-3973305582005486268447064782546323375350350204374629285434332471440450407,4551953590800417319565096598891886673852988832128540704387350396261362321,-892505746176094302938163505428096553340752273634037487695904491771406365,1186189352417246087857147576508465710259985911147592319194212271995849014231,-27076220241439559528222855879986211304426473418241754989684834232354729715)$ |
| $15$ | $10$ | $(197607004124336751999421350715668031854982943300133417832149456277254377,326706056883813108335916963798738682575199540607322344515537433278058205,687876207665770422829332673604262792297757363837117530778640575690863997,-420003089913623204348582492767297843898967618526681869374999860088478553,-17693122810186027059202677889881965634796391176556775419809834680565131)$ |
| $15$ | $15$ | $(10541503590744028444200494953622205846176739929510862880469982125893537,-19740479067924229703134084928825786486829273130893802112353197379678169,11464250038383381859537256441130191330027223499274340507433556128097723,-1185281537150288896236657579339779188582516554078107813983708809387544543391,3544825536789837792123711109539490032340435685669)$ |
| $16$ | $0$ | $(-13691044326102732799988871658826262923431405059513540175575225037065387,-1109757634804276285230392198454462686986033518535322611647878570797999,1738273127505593882921079413175578296943340555690560098237232696987805,14794692289089351446613104477986564569746879602091423457331348176916311,-861492111006406061199781157808840844780207972947833514441269053835315)$ |
| $16$ | $5$ | $(231364826427636046643364887788130746763754753742819118670146674822703767,-265059389645691491386657990043756884078222566908393996946957334654353169,51970439420738902754280237810906793430780594253253026247762389334520291,-28583068585665233833803806064510231704809079267482604862290413689945889921,1576643141883683985506401853965084503734123462930447739178448069127783071)$ |
| $16$ | $10$ | $(-2172093673163127809150017892238362999933800346751092170987562659704444817,-19024031397461348761597174485761475515726002758435143058965758759981991,2171952697896374312630300764924371294241932152859827541237922514118011101,24456699841316678429007132749885858354702975686381149435391870976098747,1030267167589801037169161696350552727498163909211999577765830287988231)$ |
| $16$ | $15$ | $(-613829744081190742403182100277545310929937986192938611346823637111769,1149484332096953129411047771424421096616071492163324207913103027032543,-667561093781970432397364821780645400247034755369893277550124409697909,28588647070969430008091322943741469615274273832534472476801964931007940717,-85500164326439439278730513520823888898585378767)$ |
| $17$ | $0$ | $(3676906675815485921769984102410107265613607834836575978685624668571392955,298039737419401666082549238931756761211364247910259854853530609594029007,-466835685772362473796687193183916371092202887770196847873761069385238245,-3973305582005486268447064770415258060273126148533417217491991243451858043,231364826427636046643364875152342922828778481029264100259336645536877901)$ |
| $17$ | $5$ | $(-2042135848440094274885674574077492736026220079055992862628277004604178988437,3192815014171165448649280664803785479830426343194329616420982155162042598539,-2973699879752904615447291157270342478996001964436491607353841651485898990515,19158410243883851364407089553043790170364389495779030960030041519797095879181,-423427866836877851432278281658942821685378322316804486112379122179274242839)$ |
| $17$ | $10$ | $(18999428124920723438899895287952957048548099957288421245009440486964411979,5109149191262662477920037436568458550114660902423071945535849533159255567,-26054500793394172128332476556380493707274424749808166837819224251339278225,-6568162425966720546368898982058576687599451110388496328702279288493932309,66516169619850448015865818045583054042545704187440608934903312650840469445)$ |
| $17$ | $15$ | $(17334239490875626515153617234450257708751818021100373103601756765678657831,533685742579415000665094779440313634324192986473274339971856973305424340711,-84180484771615656521514212165938030025861011628319131310378676780195795809,-19178832208739622305357938766397431785704853567582611618802781851927622076081,57358198916016154569595151685096201540355655343663)$ |
| $18$ | $0$ | $(-4212388954380004897477679051748670620107776575782655924561665408075036611,-341444428309663714541879040811955085307735149540668087921506403196975465,534822789817414670792067165792109481631411397507837789399141150611256125,4551953590800417319565096585803658618985533965133273468624954871214929281,-265059389645691491386657975614908808212512785288719080635797379528227219)$ |
| $18$ | $5$ | $(3192815014171165448649280664816463975616669219466345489118776565735436441551,-5003054103347660889774942050900567550204845206675501163336201312148965158069,4682263513491925976569136527904774237111376627624802289901203619827103450135,-21929299841809566096057307923142302209306527547014112361024946819675355810217,485093320690486404738401039656726002298280062329977975984792398026294921289)$ |
| $18$ | $10$ | $(-24014217273146369038757172254944533878590868092969821211407082951941875199,-5853214540665805828273365335136033451138807726340491181675265918805676315,33272928633140250858034311595429893874558019629871656500191738781435737797,7524709570601134599151155972794197207957561927626554684409388900410129363,264362568540392355729659897055395383217540000076366930548900696309410491679)$ |
| $18$ | $15$ | $(-27257788182738135070748272660288316886087742323708653383308821515178598245,-578072754075468625533547164769678234329120633892572202235063949937891573007,132794604154852462466116126510360686403683975545716277470066862776700276455,21929003195524639026027124578843853363459771476882178020017988079465440326589,-65583144668510329103447980843535691053374303145613)$ |
| $19$ | $0$ | $(825926994183562768769808888894477262107717423901034760349669325529417463,66947324525028945451805991755410027819334645147176312773891658849958915,-104863198531432700882481526526398536912618127718496989511471415311853855,-892505746176094302938163513006957651334325141225454042789376469985319639,51970439420738902754280235572575414369758018401809661744611322939416835)$ |
| $19$ | $5$ | $(-2973699879752904615447291157431542853609441083724555023117402008819167281991,4682263513491925976569136528086607423295408530292204764457507028036842148625,-4427416316303025907947204828914128583475793247302546132051577473516017183291,3769764596890231851287547809642250520428633150925162857250384629800778726313,-95112695573807931790239627460844667549593384857347510562653949234209286349)$ |
| $19$ | $10$ | $(8952163600703523469660661195677175861944220338719693208508202600686907351,1147645182873471480374420226836810476627836982521332038834646029932041873,-13671014040351553457418979845938938519062982329622727796770287165606107035,-1475376757715767194530964143811584538527156835752319278521461769100916553,303518972975036470530822798098326894167490654136406102166796343132345726479)$ |
| $19$ | $15$ | $(25702166871592682176329731889933370799080225895966071467784204527079714573,-30204022918419569160855474480829622458377171634493767324767118463106068461,-126062360924626543124403446738016252146690750077850508307525077642696540781,-3761946496266661658719632780442541346952451185069841601338985370381728105857,11250866220412777898545913474063230958388705624181)$ |

**Lemma 31.1 (enclosed tangent solves).** Both Jacobians in AC.143 are
nonsingular. For $b_n=-\partial_\lambda\mathcal F_n$, put
$w_n=R_nb_n$. The ordinary infinity-norm bounds are

| $n$ | $q_n=\|I-R_nJ_n\|_\infty$ | $q_n\|w_n\|_\infty/(1-q_n)$ |
| --- | --- | --- |
| $5$ | $<5.89\cdot10^{-14}$ | $<2.61\cdot10^{-13}$ |
| $6$ | $<6.54\cdot10^{-9}$ | $<4.71\cdot10^{-7}$ |

At the transition, along the five- and six-contact branches, respectively,

$$
\begin{gathered}
-0.00009408323<\frac{d}{d\lambda}P_{\rm unused}
 <-0.00009408322,\qquad
71.95465<\frac{dp_5}{d\lambda}<71.95467,\\
0.0039816305<\frac{d\tau_5}{d\lambda}<0.0039816307,\qquad
0.0112044<\frac{d\tau_6}{d\lambda}<0.0112103.
\end{gathered}
\tag{AC.144}
$$

All six signed angular curvatures are positive, each exceeding
$0.00008276009$; the contact boxes are pairwise distinct.

Proof. The matrices, source intervals and transition box give the two
Neumann bounds in the table by the same outward rational arithmetic as
Lemma 27.1. Since $q_n<1$, the exact solve satisfies

$$
\|J_n^{-1}b_n-w_n\|_\infty
 \le\frac{q_n\|w_n\|_\infty}{1-q_n}.
\tag{AC.145}
$$

Indeed $R_nJ_n=I-E_n$, so $J_n^{-1}b_n=(I-E_n)^{-1}w_n$;
subtract $w_n$ and bound the Neumann tail. This encloses the complete
tangent, without finite differences. For explicit reproducibility,
$\partial_\lambda F$ has zero moment rows and contact rows
$-\sigma_iW_i(x_i),-\sigma_iW_i'(x_i)$. At fixed unused $x_5$,

$$
P_{\rm unused}'(\lambda_D)
 =\sum_{j=0}^7(d_j)'\Gamma_{0,j}^{\rm num}(x_5)-W_0(x_5).
\tag{AC.146}
$$

Motion of the minimizing unused angle makes no first-order contribution
because its angular gradient is zero. For either branch,

$$
\tau_n'=\frac1{\sqrt\alpha}\sum_{i<n}\sigma_i
 [p_i'u_i+p_i(\partial_{x_i}u_i)x_i'],\quad
\partial_xu=(U'r-2xU)/r^2.
\tag{AC.147}
$$

Substituting AC.145 into AC.146–.147 gives AC.144. For every contact,
value and first derivative vanish exactly, so its angular curvature is

$$
\gamma_i=\frac{P_i''(x_i)(1+x_i^2)^2}{4D_{\eta_i}(x_i)}.
\tag{AC.148}
$$

In index order $0,\ldots,5$ the curvatures lie respectively in
$(0.00008276009,0.00008276011)$, $(0.05854371,0.05854373)$,
$(0.06407661,0.06407663)$, $(17.00212,17.00214)$,
$(1.13779,1.13780)$ and $(0.00008276009,0.00008276011)$.
These strict rational bounds use the whole transition box, including
its unused contact, not just its centre. $\square$

**Theorem 31.2 (local change of the global minimum).** There is
$\varepsilon>0$ such that at fixed $A=\log1001$ the original value
on $(s_D-\varepsilon,s_D]$ has minimum five supported low and six total
actual labels, and on $(s_D,s_D+\varepsilon)$ it has minimum six low
and seven total actual labels. This local seam has $C^1$ value and
fails to be $C^2$.

Proof. The analytic implicit function theorem applied to $J_5$ continues
the five occupied contacts at fixed $t$ using $\lambda$ as parameter.
At the unused endpoint, positive curvature continues a unique local
minimum of its signed gap. Its value is zero at $D$ and has the
strictly negative derivative AC.144. Thus it is positive immediately
below $\lambda_D$ and negative immediately above. Around every old
occupied contact its exact value/derivative equations and strict
curvature preserve nonnegativity. On the compact complement of all six
contact neighborhoods Lemma 28.1 has a strictly positive margin;
uniform continuity preserves it. Height and report signs persist.
This includes both axes, opposite sign sectors and chart endpoints,
so below the seam the five-atom branch is an original global optimum.

The six-atom Jacobian $J_6$ is also nonsingular even at $p_5=0$.
Its analytic continuation has $p_5'>0$ by AC.144, so its new weight
is positive immediately above the seam while the old weights stay
positive. Both pure-positive double factors and all other signed
contacts persist with strict curvature. The same compact-complement
argument preserves complete-circle nonnegativity. Hence above the seam
this branch also matches a universal bound and is globally optimal.
Column independence, endpoint disjointness and uniqueness of merged
weights persist. Theorem 30.1's equality argument gives the two local
minimum counts, not merely feasibility of an extra outcome. Both
$\tau_n'$ are strictly positive, orienting these branches as lower and
upper physical-strength sides. Their strength images contain an open
one-sided neighborhood of $s_D$.

Let $v_n=\boldsymbol d B-\lambda k_u$ along either branch. Differentiate
the moment equations and contact equations. Weight derivatives multiply
zero contact gaps; angle derivatives multiply zero stationarity gaps;
multiplier derivatives give $B$. Their cancellation yields

$$
v_n'=-\lambda k_u',\qquad
\frac{d\mathcal T_A}{ds}=-\frac{\lambda\sqrt\alpha}{2s_0},\qquad
\frac{d^2\mathcal T_A}{ds^2}
 =-\frac{\sqrt\alpha}{2\delta\tau_n'}.
\tag{AC.149}
$$

At the seam the two exact laws agree after deletion of the zero-weight
endpoint, and their common multiplier is $\lambda_D$. Values and
first derivatives therefore join. The two disjoint positive intervals
for $\tau_n'$ in AC.144 force different one-sided second derivatives.
Thus the value is $C^1$ and not $C^2$ at this seam. This argument
uses IFT only for local unfolding after root selection, full-domain
positivity and transverse signs have been certified. It asserts no
quantitative or maximal neighborhood and no ordering of other seams.
$\square$

## 32. One common original instrument for both selected results

**Proposition 32.1 (simultaneous reconstruction).** The laws in
Theorems 29.1 and 31.2 have one common instrument at each parameter
point satisfying all original interfaces in Convention 26.1.

Proof. Use only occupied endpoints and put
$K_j=\sqrt{p_j}(s_0D+z_jT+w_jS)$,
$N_j=p_j\eta_j1000c(h_j)n_jn_j^T$. Choose
$J_j:\mathbb C^2\to\operatorname{ran}K_j^\dagger$ isometric and set

$$
\begin{gathered}
Q_j=J_j^\dagger(K_j^\dagger K_j+N_j)J_j,\quad
C_j=Q_j^{1/2}J_j^\dagger E^\dagger,\quad
B_j=K_jJ_jQ_j^{-1/2},\\
F_j=Q_j^{-1/2}J_j^\dagger N_jJ_jQ_j^{-1/2},\qquad
L_{{\rm dec},j}=B_j^\dagger B_j=I_2-F_j\succ0.
\end{gathered}
\tag{AC.150}
$$

The rank-two row space contains $N_j$ and makes $Q_j\succ0$.
Direct multiplication yields $B_jC_j=K_jE^\dagger$,
$C_j^\dagger F_jC_j=EN_jE^\dagger$ and
$B_j^\dagger B_j+F_j=I_2$. These are the reused FA70 identities,
now with the selected exact moments of AC.139. $L_{{\rm dec},j}$
is the terminal live CP-map effect on the entire qubit; it is distinct
from the coefficient rescaling matrix $L=\operatorname{diag}(s_0,1,1)$.

For elapsed time $q$ take $g(q)=2/(1+q)^2$,
$G_{\rm time}(q)=2q/(1+q)$, $Z_j(q)=\sqrt{I-G_{\rm time}(q)F_j}$
and $R_j(q)=g(q)F_j[I-G_{\rm time}(q)F_j]^{-1}$.
For each original failure label $\ell$ the current-survivor jump is

$$
Y\longmapsto w_\ell g(q)
 \operatorname{tr}(F_jZ_j(q)^{-1}YZ_j(q)^{-1})P_f.
\tag{AC.151}
$$

Pullback through $Z_j$ gives $w_\ell g(q)\operatorname{tr}(F_jY)P_f$.
At every cut $Z_j^\dagger Z_j+G_{\rm time}F_j=I_2$.
At the end apply only to survivors the isometry
$EB_j(I-F_j)^{-1/2}$, whose composition with $Z_j(1)$ is $EB_j$.
A pure label has zero rate/activity; a saturated label has failure
eigenvalue $1000/1001$, least terminal live eigenvalue $1/1001$,
and whole-fibre activity $\log1001$. Survivors stay positive; failure
is an actual first chronological event at absolute time $6+q$.
There is no terminal absorption atom or subsequent positive-carrier action.
The choice of $g$ is a sufficiency witness; necessities retained every
admitted competitor law, including the prescribed-path qualifications
of FA68. Endpoint coercivity alone is not asserted sufficient for an
arbitrary noncommuting prescribed time law.

Choose $W_\perp:\mathbb C^2\to P^\perp$ and
$J_0:\mathbb C^2\to\mathbb C^3$ isometric. The single high encoder is

$$
C_H=\begin{pmatrix}\sqrt{1-\delta}DE^\dagger\\W_\perp^\dagger\end{pmatrix}
 :\mathbb C^5\longrightarrow\mathbb C^3\oplus\mathbb C^2.
\tag{AC.152}
$$

Its entire jointly accessible fibre has dimension five, including the
complement; its rate is zero and report deterministically plus.
The two hidden terminal Kraus matrices $E[I_3\ 0]$, $EJ_0[0\ I_2]$
have effects summing to $I_5$ on that fibre. This is a general TP
terminal map, while the low terminal maps are isometric. It is the
allowed free coherent JR completion, distinct from fixed CA10's
certain-failure complement. No complementary quantum share is uncounted.

The live Gram and physical failure sum of §29, together with root TP,
give total encoder effect $I_5$. On every complex $X\in M_5$ the
complete forgotten outputs are

$$
\begin{aligned}
\Phi^L(X)&=E[\Lambda_*(E^\dagger XE)
 +J_0W_\perp^\dagger XW_\perp J_0^\dagger]E^\dagger,\\
\Phi^f_\ell(\mathcal B)(X)&=
 w_\ell\int_{\mathcal B}g(q)dq\,
 \operatorname{tr}(EME^\dagger X)P_f.
\end{aligned}
\tag{AC.153}
$$

For an arbitrary passive reference the failure output is exactly

$$
w_\ell\int_{\mathcal B}g(q)dq\,P_f\otimes
 \operatorname{Tr}_5[(EME^\dagger\otimes I_R)X],
\tag{AC.154}
$$

and live Kraus conjugations amplify by $I_R$. These are per-component
CP/Borel identities for the same instrument, including both individually
zero components and three distinct positive measures with weights
$(0,1/4,1/2,1/4,0)$. The conditional reference operator is retained,
not replaced by the unconditional marginal. Expanding the exact Gram
on complex matrix units proves the live identity, and the pulled jump
sum proves every Borel identity, rather than checking only output effects.

All twelve inputs lie in $P$ and have zero complementary probability.
Thus their outputs are the same original simulator, compared against
the original ideal coherent blocks and ideal $f_y$ of AC.3, not against
$g$. Under the inherited complete-output minimax identification,
$e_{5,e,n}=e_{27,e,n}=E_*$ and $e_{16,e,n}<E_*$ for each of the four
sign pairs. No assertion that all twelve errors equal $E_*$ is made.

Give low labels report $\operatorname{sgn}z_j$. Their $01$ acquisition
effects and exact first moment give actual contrast $C_sk_u=s$.
Every acquisition probability uses $K_j^\dagger K_j+N_j$, including
mass that later fails. Only the high fibre has acquired dimension at
least three, with probability $(1-\delta)A_y$ and worst history $27$;
JR's original sharp identity makes its maximum $\mathsf C(s)$.
All quantum shares accessible later are inside the declared fibres.
No discarded Kraus index becomes readable, and no prior, extra copy,
retry, reset, postselection or acceptance division is introduced.
This proves simultaneous mathematical attainment with dimensions
$(2,2,2,2,2,2,5)$ at $S$ and on the local upper side, and
$(2,2,2,2,2,5)$ at $D$ and on the local lower side. $\square$

## 33. Mathematical attribution and limits of external transfer

The new content is the selected later unused-pure-contact activation,
its evaluated location/value, transverse local five-to-six supported-low
and six-to-seven total minimum-count change, and the separate selected
six-low/seven-total optimum at $\lambda=1/4$. Source isolation/ranks/TP,
complete-output minimax, original sharp cost/unaveraged equality face,
static signs, the first seam, capacities/rigidity, constructors and
static/limiting formulae are reused with their original conditions.
The finite measure $\nu_{\rm sel}=\sum p_i\delta_{(h_i,\eta_i1000c(h_i))}$
is the displayed finite-budget family. It does not evaluate the distinct
fixed-strength coefficient problem's chosen auxiliary family $\nu_\star$.
Its physical dictionary remains $N$, $G=LNL$, $M_2$ and the whitened
spectral quantities $d_f,z_f,L_f$ of AC.7–.8, with congruence back to
physical effects. None is replaced by a bare spectral direction.

The proof uses the classical contraction theorem, polynomial division,
Bernstein positivity, weak duality, exact joint moments, double rigidity
and analytic implicit functions. It is a repository-derived conditional
synthesis, without a worldwide originality or priority claim.
The following authenticated primary theorem scopes give context, not
load-bearing substitutes for these certificates:

Dritschel–Rovnyak, *The Operator Fejer–Riesz Theorem*,
[arXiv:0903.3639v1](https://arxiv.org/abs/0903.3639v1), §2, Theorem 2.1,
starts with an operator Laurent polynomial nonnegative on the whole
circle and factors it as a same-degree polynomial square; zeros are
allowed. It does not choose these coupled sheet multipliers or weights.

Xia–Wang–Sheu, *S-Lemma with Equality and Its Applications*,
[arXiv:1403.2816v3](https://arxiv.org/abs/1403.2816v3), Assumption 1 and
Theorem 3, requires the equality quadratic to take both signs. Its
exception has zero constraint quadratic matrix, nonzero constraint
linear part, one negative objective eigenvalue and the stated PSD
restriction. The homogeneous nonzero indefinite $Q$ avoids that
exception for a corresponding pure quadratic null test. This does not
handle the rational-capacity saturated sheet or its joint optimization.

Dette–Melas, [arXiv:1105.3575v1](https://arxiv.org/abs/1105.3575v1),
§3, Theorem 1 in the versioned HTML, equations (10)–(11), uses the
specified ordinary Chebyshev systems and information-matrix entry
condition (the alternative numbering in §15 refers to the paper layout).
The last three $\Gamma$ functions vanish identically on the pure sheet,
so evaluations at distinct pure points fail its full-system determinant
test. No low-support complete-class theorem is transferred here.
The full-complex Uhlmann roof is also not substituted for this real-null
two-sheet domain. These are limited authenticated prior theorem claims;
no exhaustive literature search or external solution of this frontier
is asserted.

## 34. Selected scopes and the unchanged complete programme

The two results do not certify a maximal continuation neighborhood,
that this is the first event after the tiny first-seam interval, an
ordering of intervening events, or a certified connection from that
interval to $D$ or from $D$ to $S$. The strict bounds give $s_D<s_S$,
but ordered points do not certify the interval between them. The local
$C^1$/not-$C^2$ assertion concerns only the selected seam. The selected
$\lambda=1/4$ optimum is globally optimal in the original class at its
own $s_S,A$; it is not a universal all-parameter classification. Weak
minimum counts do not transfer to static supports, limiting failure rays,
weak feasibility counts or the isolated strong component.

The original full finite-$(s,A)$ target remains: evaluated roots, positive
common weights and complete universal inequalities for every feasible
interior point, jointly choosing oriented failure allocation and every
live-height decomposition, including submaximal fixed-allocation
contrast. All budget/contrast topology, unused-zero, height-sign,
zero-weight, capacity, collision, rank and actual-alphabet transitions,
their ordering, degeneracies and global gluing remain required beyond
the specified results. A finite KKT system, an unevaluated SDP, a bare
algorithm or a continuation plot is not that evaluation. In particular
certified intervening intervals and subsequent saturated-contact changes,
including a possible third saturated contact, require their own proof.

The source-specific precontact/contact $K(s)$, coefficient/orientation
and degenerate gluing questions beyond independently established suppliers
remain required. Unverified coefficient candidates supply no premise
here. The existing postcontact and rank-conditional results are retained;
existence of a coefficient is not its evaluated value or continuity.
The credited TC/SC limiting support, strict concavity/convexity and
quadratic results, WE critical limit and JS finite-product/common-recovery,
clamped limiting selector, two/three physical-failure-ray criterion,
critical strip, sub-spectral uniform rate and compact-uniform spectral
layer retain exactly their completed ranges. The remaining limiting
transition-root inventory, isolation, ordering, multiplicities/sign
intervals, next terms, critical five-label/static-contact joint
interpolations and required uniform joint regimes remain unresolved.

The same sole unknown specimen and all twelve complete errors, five
separate failure Borel measures, passive references, original contrast
inequality and sharp worst-history JOINT acquired cost remain mandatory.
The whole-fibre positive-rate activity is a maximum of label integrals,
not an expected activity, instantaneous maximum or postselected average.
FIRST is at absolute $6+q$, without deadline absorption or later
positive-carrier action. Native access and calibration, acquisition/report
generation, coherent joint storage and every accessible-share charge,
acquisition duration/cut placement, whole-fibre decoder actuation, aligned
clock, archives, source/epoch/controller and permission bridges remain
unsupplied. OriginalControl is geometry; a native cyclic-state count
supplies no quantum operation/resource/permission bridge. The original
quantum-first AURIC FIB ATOM programme through 2027 and all its remaining
obligations are unchanged.

## 追加锚（本行以下为增补区）
