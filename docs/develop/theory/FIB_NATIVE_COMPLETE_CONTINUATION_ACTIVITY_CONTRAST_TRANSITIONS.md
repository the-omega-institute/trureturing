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
$dk/ds=1/s_0$, whereas on the left $k$ is constant. Its actual
contrast is $s_c$ before the seam and the request $s$ after it.
The value is $C^1$ although that law is not. Aggregate uniqueness
does not imply uniqueness of the whole instrument, time laws,
hidden Kraus representation or its supported-zero completion.
Optimizers may split labels or retain extra $\mathcal J_0$ outcomes;
the five/six statements are minima, not counts of every implementation.

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

The pure frame determinant lies in $(1.5240,1.5244)$, and a five-weight
moment minor lies in $(-0.015478,-0.015475)$. Distinct projection-line
determinants exceed $0.04598$ in magnitude. These data establish the
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

The strip application gives neither a numerical enclosure for $\chi$
nor a specified positive width of the active neighborhood. It does
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
The strip application pays $\mathrm M$ and the whole pure angle-box
containment only on AC.80. It does not supply numerical $\chi$ or a
specified active-side width.

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
