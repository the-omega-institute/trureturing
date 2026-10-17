# Indefinite common-quadratic compatibility for the original complete continuation

## 1. The original source, experiment and common attained law

**Assumption 1.1 (fixed original mathematical and operational premises).**
Let FC mean [*Complete finite-face criteria for original optimal acquisition
alphabets*, §§1–41](https://github.com/the-omega-institute/trureturing/blob/0512cd17cf4807864a7097fb3169847fcf3eef68/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_FACE_ALPHABET_CRITERION.md),
and let GC mean [*Global actual acquisition counts for the complete finite
continuation*](https://github.com/the-omega-institute/trureturing/blob/321589a8be98de4fe179f99f6e593d8784952db1/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_GLOBAL_ACTUAL_COUNTS.md).
All references to FC and GC below have these fixed meanings.
Retain GC Assumption 1.2 and FC Assumptions 1.1, 17.1 and 23.1 at their
respective scopes. There is one consistent isolated positive source,
with membership in all nine dyadic rows of GC Definition 6.1. Source
existence, isolation, Jacobian, ranks and root TP are premises about that
root, not consequences of evaluating expressions on its enclosing box.

Retain the complete stopped-output minimax supplier, the sharp
worst-history cost of the jointly future-accessible input-dependent
fibre, JR's separate unaveraged supported equality face, the full-complex
multi-Kraus actual-label necessity, physical capacity and common
constructor named in GC Assumption 1.2. Averaged-live equality does not
replace the separate unaveraged supplier. No additional source,
independently optimized marginal, or new dual-attainment supplier is
assumed.

More explicitly, the original experiment is GC Definitions 2.1–2.2.
In the ordered modes $0,1,2,3,13$, put

$$
\begin{gathered}
E=\big((e_0+e_{13})/\sqrt2,\ (e_1+e_3)/\sqrt2,\ e_2\big),\qquad
p_y=(y/128,(64-y)/128,1/2),\qquad a_y=(\sqrt{p_{y0}},\sqrt{p_{y1}},\sqrt{p_{y2}})^T,\\
U_{\epsilon,\chi}=\operatorname{diag}(\epsilon,\chi,1),\qquad
\rho_{y,\epsilon,\chi}=U_{\epsilon,\chi}a_ya_y^TU_{\epsilon,\chi}^{\dagger},\qquad
y\in\{5,16,27\},\quad\epsilon,\chi\in\{\pm1\}.
\end{gathered}
$$

There is one unknown normalized specimen
$E\rho_{y,\epsilon,\chi}E^\dagger$, with no prior on these twelve
histories. The ideal live output is
$EU_{\epsilon,\chi}\xi_y\xi_y^TU_{\epsilon,\chi}^\dagger E^\dagger$,
where $\xi_y$ is positive and has squared coordinates

$$
\left(\frac y{128},\frac{y(58-y)}{128(y+6)},\frac{y}{2(y+6)}\right).
$$

The five separately labelled failure Borel components have densities
$w_\ell f_y(a)\,da\,P_f$, where

$$
(w_0,w_1,w_2,w_3,w_{13})=(0,1/4,1/2,1/4,0),\qquad
f_y(a)=\frac{6y}{(y+6a)^2},\qquad 0\le a\le1.
$$

Both zero-target components remain separate. The error is the maximum,
over all twelve histories, of HALF the complete stopped-cq trace norm
against this ideal output. It includes live coherences, all five
failure measures, singular-time parts, abort and wrong-support sectors.
Arbitrary passive references retain their conditional operators.
The comparison class is the original common full complex CP acquisition
instrument with all hidden Kraus multiplicities, all admitted failure-time
laws and full-output TP conditional decoders; it is not replaced by a
real-only, LOSR, PPT or diamond-norm problem.

The cost counts specimen, memory, controller, accessible environments
and entangled shares jointly. Precisely, $\mathsf W$ is the maximum
over the twelve histories of the probability that this joint
future-accessible input-dependent fibre has dimension at least three.
The original constraints are

$$
\mathsf E(\Phi)=E_*,\qquad
\mathsf V(F)=\frac{2|\operatorname{Re}F_{01}|}{h_0a+h_1b}\ge s,\qquad
\mathsf W=\mathsf C(s),\qquad
\max_{j\ {\rm actually\ generated}}\int_0^1\|R_j(a)\|\,da\le A.
$$

The binary report is produced by the same acquisition.
$E_*$ and $\mathsf C(s)$ have their inherited minimax and sharp JOINT
meanings. Activity is the integral of the operator norm on each entire
counted fibre, maximized over actual generated labels. Survivors are
strictly positive at finite budget; survivor controls are TP; FIRST is the absolute time $6+a$; after failure there
is no later positive-carrier action. Retain the original finite and
convergent countable necessity classes and only the stipulated measurable
finite-dimensional-fibre/Kraus/integrable-effect extension of GC
Convention 2.3. Physical attainments invoked here are finite. There is
no extra specimen, helper, copy, history oracle, reset, retry,
postselection, acceptance or survival division, quantum bypass or
uncounted accessible share.

**Definition 1.2 (the unchanged source dictionary).** Use the positive
source amplitudes $h_0,h_1,h_2,a,b,c_{\rm src},d$ and $m_1,m_2>0$ of
Assumption 1.1. In qutrit coordinates define

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=ae_0e_1^T+be_1e_0^T,\quad
S=c_{\rm src}e_0e_2^T+de_2e_0^T,\quad
M=\operatorname{diag}(0,m_1,m_2),\\
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\quad
\theta=\frac{ab}{h_0h_1},\quad\omega=\frac{c_{\rm src}d}{h_0h_2},\quad
\delta=\theta+\omega\in(0,1),\\
s_0=\sqrt\delta,\quad\alpha=\theta/\delta,\quad\beta=\omega/\delta,\quad
\alpha+\beta=1,\qquad
\Delta=\rho_{27,+,+}-\rho_{5,+,+},\\
(K_0,K_1,K_2)=(D,T,S),\quad
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\quad
L=\operatorname{diag}(s_0,1,1),\quad G=LNL,\quad
H_0=(1-\delta)N_{00}>0.
\end{gathered}
\tag{IC.1}
$$

The TP identity applies at the stipulated root. On the directed circle
$x=(u,v)^T$, $u^2+v^2=1$, put

$$
\begin{gathered}
h=(1,u/\sqrt\alpha,v/\sqrt\beta)^T,\qquad
K_h=s_0D+(u/\sqrt\alpha)T+(v/\sqrt\beta)S,\\
n_h=(0,dv/(h_2\sqrt\beta),-bu/(h_1\sqrt\alpha))^T,\quad
\ell(h)=h^TGh=x^TE_\ell x+l_u u+l_v v,\\
E_\ell=\begin{pmatrix}
\delta N_{00}+N_{11}/\alpha&N_{12}/\sqrt{\alpha\beta}\\
N_{12}/\sqrt{\alpha\beta}&\delta N_{00}+N_{22}/\beta
\end{pmatrix},\quad
l_u=2\sqrt{\delta/\alpha}N_{01},\quad
l_v=2\sqrt{\delta/\beta}N_{02},\\
f(h)=n_h^T\Delta n_h=x^T\mathsf F x=2euv-d_*v^2,\qquad
\mathsf F=\begin{pmatrix}0&e\\e&-d_*\end{pmatrix},\\
e=-\frac{bd\Delta_{12}}{h_1h_2\sqrt{\alpha\beta}}>0,\qquad
d_* =\frac{11d^2}{64\beta h_2^2}>0,\qquad
\Delta_{12}=\frac{\sqrt{37}-\sqrt{59}}{16}.
\end{gathered}
\tag{IC.2}
$$

The exact physical capacity is

$$
\begin{gathered}
\mathfrak c(x)=\frac{N_c(x)}{D_c(x)},\quad
D_c(x)=D_u u^2+D_v v^2,\quad N_c(x)=N_u u^2+N_v v^2,\\
D_u=h_0^2\delta+b^2/\alpha,\quad
D_v=h_0^2\delta+d^2/\beta,\\
N_u=h_1^2h_2^2\delta+a^2h_2^2/\alpha,\quad
N_v=h_1^2h_2^2\delta+c_{\rm src}^2h_1^2/\beta.
\end{gathered}
\tag{IC.3}
$$

All four axial coefficients are positive. Define

$$
\begin{gathered}
V=m_2h_1^2/b^2,\quad W=m_1h_2^2/d^2,\quad
U=\alpha V>0,\quad V_2=\beta W>0,\quad\mu=U+V_2,\\
u_F=V/\mu,\quad v_F=W/\mu,\quad
\mathfrak c_f=\mathfrak c(\sqrt{\alpha u_F},\sqrt{\beta v_F}),\quad
\nu=\mu/\mathfrak c_f,\quad t_0=W/\mathfrak c_f.
\end{gathered}
\tag{IC.4}
$$

The angular point in (IC.4) corresponds to the source-ellipse point
$(1,\sqrt{u_F},\sqrt{v_F})$ in FC (FC.2). In particular
$V_2$ differs from $V$, $d_*$ differs from the amplitude $d$, and
$\mathfrak c$ differs from $c_{\rm src}$.

**Definition 1.3 (one common fractional law and its original targets).**
For finite $t=e^A-1\ge t_0>0$, let

$$
\begin{gathered}
X=\{(u,v,\xi):u^2+v^2=1,\ 0\le\xi\le1\},\quad
b_x=t\mathfrak c(x)\xi,\\
\Gamma(x,\xi)=(1,u,v,u^2,uv,\xi\mathfrak c,
                    \xi\mathfrak c u^2,\xi\mathfrak c uv)^T,\\
B(t)=(1,0,0,\alpha,0,\mu/t,U/t,0)^T,\qquad
k(x,\xi)=|u|,\quad g_t(x,\xi)=|\ell(x)+b_x f(x)|.
\end{gathered}
\tag{IC.5}
$$

A finite law is $\pi=\sum_i p_i\delta_{(x_i,\xi_i)}$ with $p_i>0$
and $\int\Gamma\,d\pi=B(t)$; zero weights are omitted.
These $p_i$ sum to one and are coefficient weights, not acquisition
probabilities. Set

$$
\begin{aligned}
K(\pi)&=\int k\,d\pi,& J_t(\pi)&=\int g_t\,d\pi,\\
R_t(r)&=\max_{\int\Gamma\,d\pi=B,\ K(\pi)\ge r}J_t(\pi),&
C_t(\lambda)&=\max_{\int\Gamma\,d\pi=B}(J_t(\pi)+\lambda K(\pi)).
\end{aligned}
\tag{IC.6}
$$

The original weak request is $r=\sqrt\alpha\,s/s_0$, with

$$
0\le r\le r_{\max}(t)
=\sqrt\alpha\left[q_F\sqrt{u_F}
 +\sqrt{(1-q_F)(1-q_Fu_F)}\right],\qquad q_F=\nu/t.
$$

GC Proposition 12.2 identifies these eight moments with the same full
live Gram $\int hh^T\,d\pi=I_3$ and full physical failure covariance
$\int b_x n_hn_h^T\,d\pi=M$. It identifies the original optimum with
$\mathcal T(s,t)=(H_0+R_t(r))/2$. The absolute value is taken within
each original label before integration. The actual acquisition effect
of a finite low atom is $p_iK_{h_i}^\dagger K_{h_i}+p_i b_i n_{h_i}n_{h_i}^T$.
These identifications use one common law, not a live marginal combined
with a separately optimized failure marginal.

**Assumption 1.4 (entire-cylinder feasibility and joint attainment).**
Fix finite $\lambda>0$ and finite $y=(y_0,\ldots,y_7)\in\mathbb R^8$
such that

$$
\mathscr D(x,\xi)=y\cdot\Gamma(x,\xi)-g_t(x,\xi)-\lambda|u|\ge0
\quad((x,\xi)\in X),\qquad
J_t(\pi)+\lambda K(\pi)=y\cdot B(t)
\tag{IC.7}
$$

for at least one common law. This is FC's jointly attained dual premise,
not nonnegativity at selected roots or on a grid. Let $\mathcal F$ be
the full multiplier face and $[r_-,r_+]$ its achieved contrast interval.
FC Theorem 4.2 gives $y\cdot B=C_t(\lambda)$, and, for every
$r\in[r_-,r_+]$, every height-optimal common law has $K=r$ and zero
integrated gap. No existence of finite duals at all requests, at
$t=t_0$, or at other boundary points is included; (IC.7) must be
supplied there if used. Integral laws have the inherited necessity
scope of Assumption 1.1 and collect into the same finite contact-group
data by FC Theorem 3.3.

**Definition 1.5 (the complete groups, with both paired coordinates).**
Put $\eta_0=\ell$, $\eta_1=\ell+t\mathfrak c f$ and
$\mathscr D_j(x)=\mathscr D(x,j)$. The complete inventory is
$Z=\{(x,j):j\in\{0,1\},\ \mathscr D_j(x)=0\}$, including unused
contacts. At a fixed directed $x$, pair the two endpoint coordinates
exactly when both are contacts and $\eta_0\eta_1\ge0$; otherwise
keep each present endpoint as its own singleton group. Denote this
partition by $\mathscr G$. Zero saturated heights retain both height
signs in their signed descriptions. They are deduplicated only as
one point of their sheet, not across sheets or across antipodes.

FC Theorem 3.3 supplies the exact group interpretation. For a paired
group, endpoint masses $a_0,a_1\ge0$ merge to one label of mass
$p=a_0+a_1$ and fraction $\xi=a_1/p$ when $p>0$. Both columns remain
independently available. Conversely that label splits into endpoint
masses $p(1-\xi),p\xi$ within its same group. This preserves
$(\Gamma,K,J_t)$ because the endpoint signs are weakly compatible.
For opposite heights and two positive endpoint masses, the merge
loses

$$
a_0|\eta_0|+a_1|\eta_1|-|a_0\eta_0+a_1\eta_1|
=2\min(a_0|\eta_0|,a_1|\eta_1|)>0.
$$

This is the credited FC (FC.9)/GC Theorem 15.1 identity; its physical
TV defect has the HALF factor. General endpoint splitting preserves
moments and $K$ but can increase both height and the number of actual
labels. Only the compatible-group mechanism preserves height and
group count. Endpoint count, angular-node count, coefficient mass,
Kraus rank and environment dimension are not definitions of original
actual-label count.

## 2. Four directed charts sharing one failure quadratic

**Definition 2.1 (signed chart and common coefficients).** Retain FC's
homogeneous dual and source matrices:

$$
\begin{gathered}
P_y=y_0+y_1u+y_2v+y_3u^2+y_4uv,\quad
Q=\begin{pmatrix}y_5+y_6&y_7/2\\y_7/2&y_5\end{pmatrix},\quad
Q_y=x^TQx,\quad R_-=Q+t\mathsf F,\quad R_+=Q-t\mathsf F,\\
F_{0,\epsilon,\sigma}=P_y-\epsilon\lambda u-\sigma\ell,\quad
F_{1,\epsilon,\sigma}=D_cF_{0,\epsilon,\sigma}
                      +N_c x^T(Q-\sigma t\mathsf F)x.
\end{gathered}
\tag{IC.8}
$$

For $u\ne0$, write $z=v/u$ and

$$
\begin{gathered}
s(z)=\sqrt{1+z^2},\qquad x_\epsilon(z)=\frac{\epsilon(1,z)^T}{s(z)},
\qquad\epsilon=\operatorname{sgn}u,\\
d_c(z)=D_u+D_vz^2,\quad n_c(z)=N_u+N_vz^2,\quad
p_y(z)=(y_0+y_3)+y_4z+y_0z^2,\\
E(z)=E_{\ell,11}+2E_{\ell,12}z+E_{\ell,22}z^2,\quad
\bar f(z)=2ez-d_*z^2,\\
o_\sigma(z)=(y_1-\sigma l_u)+(y_2-\sigma l_v)z,\\
T_{\epsilon,\sigma}(z)=p_y(z)-\sigma E(z)
                 +s(z)\big(\epsilon o_\sigma(z)-\lambda\big),\\
G_{\epsilon,\sigma}(z)=\sigma t\bar f(z)
                 -\frac{d_c(z)}{n_c(z)}T_{\epsilon,\sigma}(z),\\
q(z)=(1,z)Q(1,z)^T=q_0+q_1z+q_2z^2,\qquad
(q_0,q_1,q_2)=(y_5+y_6,y_7,y_5).
\end{gathered}
\tag{IC.9}
$$

The tags $(\epsilon,\sigma)\in\{\pm1\}^2$ retain both direction and
height sign. At equal $z$, $x_+(z)$ and $x_-(z)$ remain different
original directions. In particular $z=0,\epsilon=-1$ is $(-1,0)$
and is included. A saturated contact has its actual $\epsilon$ and
every maximizing $\sigma$: one sign for nonzero height and both for
zero height. The functions $T_{\epsilon,\sigma}$ and
$G_{\epsilon,\sigma}$ are determined by the original capacity, source
height, $t$, $\lambda$ and $y_0,\ldots,y_4$; they contain no fitted
failure coefficients $q_0,q_1,q_2$.

**Definition 2.2 (original reverse region and endpoint mass).** Put

$$
\Psi(u,v)=(v+u/10)(v-4u),\qquad
T_{\rm rev}=\{x\in S^1:\Psi(x)\ge0\},\qquad
T_{\rm rev}^{\circ}=\{x:\Psi(x)>0\}.
\tag{IC.10}
$$

Here the superscript denotes strict inequality, including the two
report-axis points, not an instruction to discard directed boundaries.
The finite slope rays of $T_{\rm rev}$ are $z\le-1/10$ and $z\ge4$.
Define the saturated endpoint coefficient mass and negative pure
endpoint contribution of any common law by

$$
S_{\rm end}(\pi)=\int_X\xi\,d\pi,\qquad
H_-(\pi)=\int_X(1-\xi)\max\{-\ell,0\}\,d\pi.
\tag{IC.11}
$$

These are FC's $S$ and $H_-$, not acquisition or failure probabilities.
A negative pure coordinate of a paired fractional label would contribute
to $H_-$ even if the actual label were not at $\xi=0$.

## 3. An occupied pair constrains the entire original face

**Theorem 3.1 (occupied reverse anchor, all-tag compatibility and same-law target).**
Under Assumptions 1.1 and 1.4, fix any $r\in[r_-,r_+]$ and any
height-optimal law at that request. Its endpoint representation has
an occupied reverse saturated contact $a$ in $T_{\rm rev}^{\circ}$
and another occupied saturated contact $b$ with different slope.
The latter is the saturated endpoint of a failure-bearing direction
of that very law, in its original group. Write their finite slopes
as $z_a,z_b$, put $h=z_b-z_a\ne0$, and retain their actual tags.
For any maximizing height tags define

$$
g_a=G_{\epsilon_a,\sigma_a}(z_a),\quad
m_a=G_{\epsilon_a,\sigma_a}'(z_a),\qquad
g_b=G_{\epsilon_b,\sigma_b}(z_b),\quad
m_b=G_{\epsilon_b,\sigma_b}'(z_b).
$$

The two tags need not agree; all choices must obey

$$
\begin{gathered}
m_a+m_b=2\frac{g_b-g_a}{h},\\
q_2=\frac{m_b-m_a}{2h},\qquad
q_1=m_a-2z_aq_2,\qquad
q_0=g_a-z_am_a+z_a^2q_2,\\
y_5=q_2,\qquad y_6=q_0-q_2,\qquad y_7=q_1.
\end{gathered}
\tag{IC.12}
$$

These are restrictions on one common $Q$ across the directed and
height branches, without a same-branch assumption or an assertion
that the selected two tags must differ. Globally, for every real $z$
and every one of the four tags,

$$
q(z)\ge G_{\epsilon,\sigma}(z).
\tag{IC.13}
$$

Every saturated contact $i$ in the complete inventory, occupied or
unused, satisfies for all its maximizing tags

$$
q(z_i)=G_{\epsilon_i,\sigma_i}(z_i),\qquad
q'(z_i)=G_{\epsilon_i,\sigma_i}'(z_i).
\tag{IC.14}
$$

Thus (IC.12) reconstructs the only possible three failure coefficients,
and every other saturated contact must pass both constraints with those
same coefficients. Distinct directed labels at an equal slope must
have equal $G$ values and derivatives there; equality does not identify
the labels. Weak-zero contacts retain both height-tag conditions.
The same law also obeys the target equality

$$
J_t(\pi)+\lambda r
=y_0+\alpha y_3+\frac{Uq_0+V_2q_2}{t}.
\tag{IC.15}
$$

No root, weight, fraction or group is removed by these restrictions.

Proof. Reuse the nonnegative-gap support argument in FC Theorems 3.3
and 4.2. Its measure-theoretic intermediate step is the standard
zero-integral support principle of di Dio–Schmüdgen,
[*The multidimensional truncated Moment Problem: Atoms, Determinacy,
and Core Variety*, Lemma 3](https://arxiv.org/html/1703.01497v2).
All positive coordinates are contacts, and all original optimal laws
at $r$ have $K=r$. FC Theorem 12.1 excludes $u=0$ from the complete
endpoint inventory: otherwise both report tests would vanish there,
whereas the difference of their angular derivatives is a nonzero
multiple of $\lambda u'$. FC Proposition 20.1 gives the same exclusion
for actual fractional contacts. Hence the chart covers all contacts,
including the left horizontal point, without a genericity assumption.

Direct substitution of (IC.2)–(IC.3) into the exact signed tests (IC.8)
gives, for each actual report tag $\epsilon$ and both $\sigma$,

$$
\begin{aligned}
F_{0,\epsilon,\sigma}(x_\epsilon(z))
 &=\frac{T_{\epsilon,\sigma}(z)}{1+z^2},\\
F_{1,\epsilon,\sigma}(x_\epsilon(z))
 &=\frac{n_c(z)}{(1+z^2)^2}
                         \big[q(z)-G_{\epsilon,\sigma}(z)\big].
\end{aligned}
\tag{IC.16}
$$

Entire-cylinder feasibility implies nonnegativity of every signed
endpoint test. The prefactor in the second line is strictly positive.
This proves (IC.13). For completeness the opposite report sign at the
same directed point has the strictly larger signed gap

$$
\begin{aligned}
F_{0,-\epsilon,\sigma}-F_{0,\epsilon,\sigma}
 &=\frac{2\lambda}{s(z)},\\
F_{1,-\epsilon,\sigma}-F_{1,\epsilon,\sigma}
 &=\frac{2\lambda d_c(z)}{s(z)^3}>0.
\end{aligned}
\tag{IC.17}
$$

It cannot be a second report description of that contact. At any
maximizing height tag of a saturated contact, (IC.16) vanishes.
The elementary tangency principle for a smooth nonnegative function
at an interior zero gives $q-G=0$ and $(q-G)'=0$. This is the standard
contact-stationarity step, applied to the actual rational source tests,
and proves (IC.14). It applies to every zero, not only to selected or
occupied roots. At zero height both signed tests vanish and give both
pairs of equations.

There really are two occupied, nonparallel directions available for
this calculation. FC Theorem 26.1 and Corollary 27.2, in the complete
face form of Proposition 28.2, give saturated reverse coefficient mass
strictly greater than $4/(5t)$ in every optimal representation. These
contacts are singleton groups because FC Theorem 25.1 gives
$\eta_0>1/20000>0> -1/250>\eta_1$ throughout $T_{\rm rev}$.
Choose any occupied such direction $x_a$. The failure intensity of
this same law satisfies, by FC Proposition 17.3,

$$
\int_X b_x\,xx^T\,d\pi=\operatorname{diag}(U,V_2)\succ0.
\tag{IC.18}
$$

If every failure-bearing direction were parallel to $x_a$, pairing
(IC.18) with a nonzero vector perpendicular to $x_a$ would give zero
on the left and a strictly positive number on the right. Thus another
failure-bearing direction $x_b$ is nonparallel. FC Proposition 20.1
puts its saturated endpoint in contact. In an endpoint representation
it has positive coordinate mass, supplied by $p\xi>0$ for any
corresponding finite atom. If that atom was fractional, this is the
endpoint in its existing compatible group, not an extra counted
original label. For the admitted integral laws, collection into the
finite complete groups gives the same positive-coordinate argument;
no atom of an arbitrary uncollected measure is presumed. Since no
contact has $u=0$, nonparallel directions have distinct finite slopes.

The rest of (IC.12) is the classical two-node quadratic Hermite
interpolation calculation, used here only as an intermediate step.
For $q=q_0+q_1z+q_2z^2$,

$$
q'(z_a)+q'(z_b)=2\frac{q(z_b)-q(z_a)}{z_b-z_a},\qquad
q'(z_b)-q'(z_a)=2q_2(z_b-z_a).
$$

Substitute (IC.14), solve first for $q_2$, then $q_1$ and $q_0$,
and use the last line of (IC.9). This gives (IC.12) with no weight
variables. If four proposed value/derivative data fail its first
equality, no quadratic can fit them all; otherwise these coefficients
are the unique fit. The calculation does not solve the other dual
coefficients, the original roots or their weights.

The all-tag constraints can also be read without identifying any
directions. Put $Y(z)=y_1+y_2z$ and $L_\ell(z)=l_u+l_vz$.
For any two tags $i=(\epsilon,\sigma)$ and
$j=(\widetilde\epsilon,\widetilde\sigma)$,

$$
\begin{aligned}
T_i-T_j
 &=-(\sigma-\widetilde\sigma)E
 +s\big[(\epsilon-\widetilde\epsilon)Y
 -(\epsilon\sigma-\widetilde\epsilon\widetilde\sigma)L_\ell\big],\\
G_i-G_j
 &=(\sigma-\widetilde\sigma)t\bar f
                         -(d_c/n_c)(T_i-T_j).
\end{aligned}
\tag{IC.19}
$$

At an equal slope occupied by both descriptions, the last expression
and its derivative must both vanish. These identities apply to all
six unordered pairs of tags. They retain, in particular, opposite
directed labels and opposite-height descriptions of a weak-zero point.

Integrating the original eight moments, rather than combining marginal
optima, gives

$$
\begin{aligned}
y\cdot B
 &=y_0+\alpha y_3+\frac{\mu y_5+Uy_6}{t}\\
 &=y_0+\alpha y_3+\frac{Uq_0+V_2q_2}{t}.
\end{aligned}
$$

Joint attainment and the already established $K=r$ prove (IC.15).
The zero failure cross moment is essential: it is why the $q_1$ term
does not appear in this target pairing.

There is a further conditional test within this source-specific
compatibility argument. For two contacts $a<b$ on one fixed tag put
$H=(d_c/n_c)T_{\epsilon,\sigma}$. Since $G=\sigma t\bar f-H$ and
$\bar f$ is quadratic, their compatibility requires

$$
\begin{aligned}
0&=H'(a)+H'(b)-2\frac{H(b)-H(a)}{b-a}\\
 &=(b-a)^2\int_0^1\tau(1-\tau)H'''(a+\tau(b-a))\,d\tau.
\end{aligned}
\tag{IC.20}
$$

This is the ordinary integration-by-parts identity for the two-node
Hermite residual: for $\varphi(\tau)=H(a+\tau(b-a))$, integrate
$\tau(1-\tau)\varphi'''$ twice, obtaining
$\varphi'(0)+\varphi'(1)-2(\varphi(1)-\varphi(0))$, and divide
by $b-a$. Consequently a strictly constant sign of this particular
$H'''$ on $[a,b]$ would exclude those two same-tag contacts. No
uniform sign for the source- and dual-dependent $H'''$ is supplied.
There is no contact-count or group-removal conclusion from (IC.20).
$\square$

## 4. Strict barriers on the indefinite branch

**Theorem 4.1 (source-specific strict separation and retained paired columns).**
Under Assumptions 1.1 and 1.4, additionally suppose that the symmetric
matrix $R_-=Q+t\mathsf F$ is indefinite. Use the coefficients of
Theorem 3.1 and define

$$
P_-(z)=q_0+(q_1+2te)z+(q_2-td_*)z^2.
\tag{IC.21}
$$

For every complete negative-height pure contact $x_n$, and for every
complete reverse saturated contact $x_r\in T_{\rm rev}$,

$$
P_-(z_n)>0,\qquad P_-(z_r)<0.
\tag{IC.22}
$$

The first assertion is conditional on the presence of the particular
negative pure contact; indefiniteness alone is not an existence claim.
The inequalities retain every such pure contact, including both if
present, and every reverse group, occupied or unused. Every compatible
paired group has positive pure height and obeys

$$
R_+x=0,\qquad \eta_0(x)>0,\qquad \eta_1(x)\ge0.
\tag{IC.23}
$$

Both endpoint columns and all legal fractions of that group remain
available. The condition permits a zero saturated height and the
algebraic case $R_+=0$; neither is asserted to occur on an attained
face. If $R_+\ne0$ and a paired group exists, its directions lie on
the kernel line of this singular matrix; this still does not select
one endpoint coordinate or identify antipodal labels.

Proof. At a negative pure contact, the actual report tag and negative
height tag give $F_{0,\epsilon,-}=0$. By (IC.8) and global feasibility,

$$
0\le F_{1,\epsilon,-}(x)=N_c(x)x^TR_-x.
$$

Suppose $x^TR_-x=0$. Both nonnegative signed tests now vanish, so
both angular derivatives vanish. Differentiating
$F_1=D_cF_0+N_c x^TR_-x$ at this point yields
$(x^TR_-x)'=0$, since $N_c>0$. For a unit tangent $x^\perp$,
this is $2(x^\perp)^TR_-x=0$. Together with $x^TR_-x=0$,
it gives $R_-x=0$ because $x,x^\perp$ span the plane.
An indefinite symmetric $2\times2$ matrix is invertible. This
contradiction proves $x^TR_-x>0$. In the chart,
$x^TR_-x=P_-(z)/(1+z^2)$, proving the first strict barrier.
The standard minimum-derivative argument is being used inside this
original-source separation proof, not as a separate general theorem.

At a reverse saturated contact, FC Theorem 25.1 gives
$\ell>0>\eta_1$. The pure actual gap is
$\mathscr D_0=P_y-\ell-\lambda|u|\ge0$, so

$$
F_{0,\epsilon,-}=\mathscr D_0+2\ell>0,\qquad
x^TR_-x=-\frac{D_c(x)}{N_c(x)}F_{0,\epsilon,-}(x)<0.
\tag{IC.24}
$$

This identity is FC (FC.119), and applies to every reverse saturated
contact, not only to the mandatory occupied ones. It proves the second
barrier with the same reconstructed coefficients, rather than a
separately chosen negative direction.

For paired groups, reuse the negative-paired exclusion of FC Theorem
34.3. Its paired-endpoint argument uses only whole-circle feasibility,
nonzero pure height and invertibility of $R_-$; the small-mass premise
in that theorem is used to force existence of negative pure coordinates,
not for that exclusion. FC Theorem 19.1 and Proposition 20.1 exclude
zero-height pure contacts in the complete inventory: both signed pure
minima at such a point would force a zero derivative of $\ell$, whereas
its two source zeros are simple. Thus every paired group left by the
credited exclusion has positive pure height. Compatibility gives
$\eta_1\ge0$, including zero, so both endpoints share the maximizing
height tag $+$.

At their two signed zeros the same identity, now
$F_{1,\epsilon,+}=D_cF_{0,\epsilon,+}+N_c x^TR_+x$, gives
$x^TR_+x=0$ and $(x^TR_+x)'=0$. Hence $R_+x=0$ by the
same radial/tangent decomposition. This proves (IC.23). It is a
necessary kernel condition; the converse requires both contact equations,
the height signs and global feasibility. Nothing in it proves the
existence of a paired group, excludes $R_+=0$, or rules out
positive-pure/zero-saturated compatibility. Nor does a kernel condition
replace the two independent masses $(a_0,a_1)$ of Definition 1.5.
$\square$

## 5. Strict orientation and exclusion of the scalar equality lifts

**Theorem 5.1 (negative-pure orientation and conditional exclusion of every FC38 lift).**
Under Assumptions 1.1 and 1.4, suppose separately that the complete
inventory contains a pure contact of strictly negative height. Define

$$
d_-=(y_1+l_u,y_2+l_v)^T,\qquad
o_-(z)=y_1+l_u+(y_2+l_v)z.
\tag{IC.25}
$$

Then $d_-\ne0$, and every complete endpoint contact $(x,j)$ of
weakly negative height $\eta_j(x)\le0$ satisfies

$$
d_-\cdot x<0.
\tag{IC.26}
$$

In particular no antipodal pair of weakly negative saturated contacts
can be present, occupied or unused. In the signed chart this gives
$\epsilon o_-(z)<0$ for every weakly negative saturated contact.
Every negative pure contact has $\epsilon=-1$ and $o_-(z)>0$.
This conclusion uses the same two odd dual coefficients for both sheets
and does not discard any negative pure contact. It requires no
indefiniteness assumption and no saturated-contact cap.

The negative-pure premise is supplied for height-optimal laws with
$S_{\rm end}\le1/100$ by FC Theorem 34.1. Uniformly over all
representations on the supplied face it is therefore supplied when

$$
t\ge\max\{t_0,100\mu/c_{\min}\},\qquad
c_{\min}=\min\{N_u/D_u,N_v/D_v\}.
\tag{IC.27}
$$

The inherited sufficient range $t\ge\max\{t_0,30000\}$ is included.
Neither $t\ge800$ alone nor indefiniteness alone supplies this premise.

For each of the eight full-common-law scalar equality lifts in FC
Theorem 38.1, at

$$
t\ge\max\{t_0,3000,100\mu/c_{\min}\},
\tag{IC.28}
$$

the lift cannot belong to any supplied finite, entire-cylinder feasible,
jointly attained face with positive height multiplier $\lambda$.
Since FC supplies $t_0<3000$, (IC.28) is also
$t\ge\max\{3000,100\mu/c_{\min}\}$; in particular $t\ge30000$
suffices. This excludes membership even when the face is considered
at the lift's own achieved contrast $K$. It is conditional face-membership
exclusion, not a nonoptimality statement without that face premise,
a conclusion at $\lambda=0$, or nonexistence of finite duals.

Proof. For the actual report choice, normalize the negative signed
gaps on the two sheets as

$$
\begin{gathered}
H_{j,-}(x)=P_y+j\mathfrak c Q_y+\ell+jt\mathfrak c f-\lambda|u|
           =\mathcal E_j(x)+d_-\cdot x,\\
\mathcal E_j(x)=y_0+y_3u^2+y_4uv+x^TE_\ell x
                 +j\mathfrak c x^T(Q+t\mathsf F)x-\lambda|u|.
\end{gathered}
\tag{IC.29}
$$

Here $H_{0,-}=F_{0,\epsilon,-}$ and
$H_{1,-}=F_{1,\epsilon,-}/D_c$ at a point of actual report tag
$\epsilon$. Each $H_{j,-}$ is globally nonnegative;
$\mathcal E_j(-x)=\mathcal E_j(x)$ because capacity and all its
quadratic terms are even. These functions are smooth near every
contact, since contacts have $u\ne0$.

A negative pure contact $x_*$ lies in $u<0$ by FC Theorem 11.1.
If $d_-=0$, evenness would give $H_{0,-}(-x_*)=H_{0,-}(x_*)=0$.
But $-x_*$ lies on the right hemisphere, where the same source has
$\ell(-x_*)>0$. Thus
$H_{0,-}(-x_*)=\mathscr D_0(-x_*)+2\ell(-x_*)>0$, a contradiction.
Hence $d_-\ne0$.

At any complete contact with $\eta_j\le0$, the negative height tag
is maximizing, including the weak-zero case. Thus $H_{j,-}(x)=0$,
and antipodal feasibility gives

$$
0\le H_{j,-}(-x)=-2d_-\cdot x.
$$

If equality held, both antipodal functions would be at smooth zero
minima. Write $x=x(\phi)=(\cos\phi,\sin\phi)$.
Evenness gives $\mathcal E_j'(\phi+\pi)=\mathcal E_j'(\phi)$;
the odd linear term has opposite derivatives at these two arguments.
Subtracting the two zero-derivative equations yields
$d_-\cdot x^\perp=0$. Equality had already given $d_-\cdot x=0$,
so $d_-=0$, a contradiction. This proves the strict inequality (IC.26)
for the entire inventory. Antipodes cannot both lie in this strict
half-plane. Finally
$d_-\cdot x_\epsilon(z)=\epsilon o_-(z)/s(z)$; negative pure
contacts have $\epsilon=-1$, giving their stated slope orientation.

Existence of a negative pure contact is a different step from this
parity argument. FC Theorem 34.1 gives
$H_->1/30000$ for every height-optimal law with
$S_{\rm end}\le1/100$. Collection into the complete groups then
supplies a positive negative-pure coordinate and hence a contact.
FC Proposition 34.2 gives the exact minimum in (IC.27): capacity is
a positive-denominator weighted mean of its two axial ratios. The
same law's equation $\int\xi\mathfrak c\,d\pi=\mu/t$ consequently
gives

$$
S_{\rm end}(\pi)\le\frac{\mu}{tc_{\min}}.
$$

This establishes precisely the threshold stated in (IC.27), using
FC's negative-pure theorem rather than inferring existence from
reverse mass, a contact count or a smaller budget range. Its coarse
source bound $\mu<12$, $\mathfrak c>1/25$ yields
$S_{\rm end}<300/t$ and the stated sufficient range $t\ge30000$.

It remains to apply the strict orientation to the actual FC38 laws.
Those are the seven physical scalar witnesses of FC §§36–37
(trace, three sign averages and three plus-sign probabilities), and
separately the intensity witness $\mathsf W=I_2$. Denote a scalar
certificate multiplier there by $\gamma_{\mathsf W}>0$. It is
not the height-dual multiplier $\lambda$ of (IC.7). FC38 uses the
kernel of $\mathsf W-\gamma_{\mathsf W}Q_\Psi$, where

$$
Q_\Psi=\begin{pmatrix}-2/5&-39/20\\-39/20&1\end{pmatrix},\qquad
z_*=-\frac{\mathsf W_{11}+2\gamma_{\mathsf W}/5}
                 {\mathsf W_{12}+39\gamma_{\mathsf W}/20}.
$$

Write $\varsigma$ for the angular intensity measure of a lift.
For each of its eight certificates FC38 supplies
$z_*<-\max\{1/10,V_2/(4U)\}$. With
$z_1=z_*,z_2=-1/10,z_3=4$ and $\{i,j,k\}=\{1,2,3\}$, its
intensity masses are

$$
d_i=\frac{V_2+z_jz_kU}{(z_i-z_j)(z_i-z_k)}>0,\qquad
x_i=\frac{(1,z_i)^T}{\sqrt{1+z_i^2}},\qquad
\varsigma\{x_i\}=\varsigma\{-x_i\}=\frac{d_i(1+z_i^2)}2.
\tag{IC.30}
$$

The coefficient lift divides these positive masses by
$t\mathfrak c(x_i)>0$ and sets $\xi=1$; its four positive pure
atoms fill the residual full live Gram as in FC (FC.171)–(FC.173).
Thus the pair $\pm x_1$ is occupied by actual saturated labels,
not merely by a relaxed intensity representation. It has $\Psi>0$;
the remaining four saturated points have $\Psi=0$. FC Theorem 25.1
therefore gives strictly negative saturated height at both $x_1$
and $-x_1$.

Suppose such a lift belonged to a face satisfying Assumption 1.4.
It would be height optimal at its own achieved $K$, by FC Theorem
4.2. At (IC.28) its same-law $S_{\rm end}$ is at most $1/100$,
so the preceding existence argument supplies a negative pure contact
on that face. Equation (IC.26) would then apply to both occupied
antipodal negative saturated contacts. Their two dot products are
opposite and cannot both be strictly negative. This contradiction
excludes the face membership of each of the eight lifts. Their
scalar equality, feasibility at $s=0$, full moments and physical
realizations remain the separate FC38 conclusions. Neither a scalar
certificate multiplier nor equality in its scalar bound supplies a
height-optimal dual. $\square$

## 6. Mathematical attribution and applicability of the restrictions

**Definition 6.1 (reused results and literature interfaces).** The bearing
content of Theorems 3.1, 4.1 and 5.1 is the repo-derived application to
one original common face: occupied reverse and nonparallel anchors
constrain the same three failure coefficients across every signed
chart and the same-law target; negative pure contacts and reverse
contacts occupy strict opposite sides of the reconstructed indefinite
quadratic; negative-pure orientation excludes all the explicit FC38
scalar lifts in the stated small-mass range. These are source-specific
necessary restrictions, not new general interpolation, moment,
stationarity or symmetry theorems.

The group accounting and all-optima activity are FC Theorems 3.3 and
4.2; the full covariance is FC Proposition 17.3; the report and pure
zero exclusions are FC Theorems 12.1, 19.1 and Proposition 20.1.
Mandatory reverse occupation and strict signs are FC Theorem 25.1,
Corollary 27.2 and Proposition 28.2. Negative pure existence and the
negative-paired exclusion are reused from FC Theorem 34.1,
Proposition 34.2 and Theorem 34.3. GC Propositions 10.1 and 12.2
supply the original same-law physical dictionary and constructor.
The quadratic Hermite calculation, tangency at a nonnegative zero,
antipodal even/odd decomposition and the integration-by-parts identity
are standard intermediate mathematics within the substantive proofs.

The following literature statements have their indicated mathematical
interfaces, without a transfer of quadrature nodes into original labels:

- di Dio–Schmüdgen, [*The multidimensional truncated Moment Problem:
  Atoms, Determinacy, and Core Variety*, Lemma 3 and Proposition 4](https://arxiv.org/html/1703.01497v2):
  a continuous nonnegative function with zero positive-measure integral
  vanishes on the support; a finite-dimensional real integrable function
  space admits an exact finite atomic representative of its integrals.
  The compact original cylinder and its continuous gap meet the first
  interface. The second does not preserve the number of original
  fractional groups or give seven labels.
- Dette–Melas, [*A note on the de la Garza phenomenon for locally
  optimal designs*, §3, Theorem 1](https://arxiv.org/html/1105.3575v1):
  the theorem assumes the interval Chebyshev systems, a distinguished
  diagonal information entry and the stated Loewner comparison.
  None of these constitutes a supplied improvement preserving this
  original rational capacity, exact $K$ and within-label absolute
  $J_t$. On the pure sheet the last three entries of $\Gamma$ vanish;
  an eight-function Chebyshev determinant on that sheet is unavailable.
- Nailwal–Zalar, [*Gaussian Quadratures with prescribed nodes via moment
  theory*, Theorem 3.1](https://arxiv.org/html/2412.20849v1):
  full univariate moments through $D=d_1+2d_2-1$, positive definite
  initial moment matrix, invertible prescribed-node localizing matrix
  and positive definite generated extension are required. Mandatory
  negative-pure and reverse groups do not establish these hypotheses.
  The theorem does not supply a prescribed-node original-law compression.

The indicated general results are literature-attested only in these
scopes; the source-specific combination proved here is repo-derived.
No priority or worldwide novelty assertion is attached to it.

**Definition 6.2 (same-law operational scope and surviving alternatives).**
No deduction above changes any $p_i,x_i,\xi_i,b_i$, capacity or label.
In particular it preserves the exact eight $\Gamma$ moments, full
live Gram, full $M$ including the failure cross entry, active $K=r$
and absolute $J_t$ of the same law. The original HALF optimum is
still $(H_0+J_t)/2$. Through the credited GC constructor, a finite
law retains the full-complex live CP output, arbitrary passive-reference
conditional operators, five separate Borel failure components, all
twelve stopped-cq errors, the sharp worst-history JOINT cost,
entire-fibre activity, strictly positive finite survivors, TP controls,
absolute FIRST $6+a$ and no action on a failed carrier. This is the
inherited conditional interface for that law, not a newly supplied
source, minimax, native actuator or operational certification.

FC Proposition 35.1 supplies a useful boundary of the contact premise:
at $t=10^6$ its seven-low feasible law preserves all original moments
and reverse labels but has $H_-=0$; at its exact achieved $K$, FC's
comparison increases $J_t$ by more than $1/15000$. Thus feasibility,
reverse retention and seven labels do not imply contact equality or
height optimality of that particular law. That inherited example does
not exclude another seven-low optimum. Likewise FC38's scalar equality
lifts do not become height optima by preserving full moments; Theorem
5.1 excludes only their specified positive-multiplier face membership.

Without a negative pure contact the strict orientation premise is
absent. Below the small-mass threshold it must be supplied separately;
no negative group may be omitted on that account. Theorem 4.1 applies
only on the indefinite $R_-$ branch; the singular rank-one negative
semidefinite possibility and its mandatory kernel group remain in the
original domain of FC Theorem 34.3. Positive-pure paired groups,
weak-zero saturated contacts, zero $R_+$ and equal-slope antipodal
labels retain the distinctions stated above. All unused contacts
remain constraints even if their coordinate weights vanish throughout
a particular slice. No coefficient-elimination formula, covariance
rank, endpoint mass, scalar witness or external quadrature resource
is an original actual-count theorem.

## 7. The remaining original group-removal and full-programme problem

**Open problem 7.1 (same-law nine-row removal or evaluated complete coverage).**
For every original supplied face let

$$
\begin{gathered}
A=[\Gamma(x_1)\ \cdots\ \Gamma(x_N)],\quad
\kappa=(|u_1|,\ldots,|u_N|)^T,\quad
\mathcal P=\{w\ge0:Aw=B(t)\},\quad
\mathcal P(r)=\{w\in\mathcal P:\kappa^Tw=r\},\\
\gamma(w)=\#\left\{G\in\mathscr G:\sum_{i\in G}w_i>0\right\}.
\end{gathered}
\tag{IC.31}
$$

The columns enumerate the complete endpoint inventory, including all
unused roots and both coordinates of every compatible paired group.
For a family $\mathcal Q\subseteq\mathscr G$, retain their entire
coordinate set and let $\mathcal P_{\mathcal Q}$ be the corresponding
coordinate face. Define

$$
U_7=\bigcup_{|\mathcal Q|\le7}\kappa^T\mathcal P_{\mathcal Q}.
\tag{IC.32}
$$

FC Theorem 5.2 supplies its equivalent complete vertex/edge coverage
criterion. The original universal seven-low question on this face is
$U_7=[r_-,r_+]$, equivalently every $\mathcal P(r)$ contains a
point with $\gamma(w)\le7$. What remains missing is an original-source
relation preserving all nine joint rows

$$
\begin{pmatrix}A\\\kappa^T\end{pmatrix}w
=\begin{pmatrix}B(t)\\r\end{pmatrix},
\tag{IC.33}
$$

with nonnegative weights, which removes an occupied whole group when
needed, or an evaluated complete-group coverage theorem with the same
consequence. A direction in the kernel of these nine rows is useful
only with sufficient sign and support information to reach a boundary
where the entire group is removed. Driving just one column of a paired
group to zero does not remove the group. A path may require several
steps or a different original law; existence of one kernel vector is
not the required universal relation. On the common contact face the
height row is $g_i=y\cdot\Gamma_i-\lambda\kappa_i$, so preserving
(IC.33) preserves the same $J_t$. This does not permit an independent
choice of the law on any one row.

The alternative higher-count task requires an actual attained
same-root tuple with global entire-cylinder feasibility, a complete
evaluated inventory and nonnegative primal weights at its request,
and exclusion of every at-most-seven-group alternative in
$\mathcal P(r)$. A claim of nine-low necessity additionally requires
exclusion of every at-most-eight-group alternative. Neither ranks of
one table, local stationary roots, node counts, endpoint mass nor
(IC.12) supplies either exclusion. All compatible fractional labels,
negative pure singletons, mandatory reverse groups, weak-zero contacts,
opposite-height singleton groups and unused contacts must remain in
the alternatives. The minimum-total-count relation remains GC.10's
$1+$ minimum supported-low count, an equality of minima rather than
of counts for every instrument.

Theorems 3.1–5.1 do not supply global dual feasibility from locally
compatible roots, a complete evaluated root inventory, positive primal
weights, group removal, universal $U_7$ or $U_8$ coverage, or an
all-alternative higher-count obstruction. The all-budget/all-contrast
finite $(s,A)$ frontier remains the original one, for every common
oriented failure allocation and every live-height decomposition,
including those below maximum contrast at a fixed allocation.
Global branch ordering and connected coverage; selected and unused
roots with signs and multiplicities; collisions; capacity, rank and
count transitions; endpoint, threshold, budget and degenerate-orientation
gluing; evaluated coefficient parameters and physical orientations;
coefficient gluing, limiting root isolation, next terms and uniform
joint limits remain required. Sharp strong optimal counts remain
separate from weak counts and from strong feasibility counts.

Source existence/isolation/Jacobian/ranks/root TP, the full stopped-cq
minimax, sharp worst-history JOINT cost, separate unaveraged equality,
full-complex multi-Kraus necessity, capacity and constructor remain
their original conditional suppliers. Finite positive-multiplier dual
existence outside the supplied scope, $\lambda=0$, nonfinite or
unattained duals and boundary attainment remain unresolved. Native
source access and calibration, jointly counted coherent storage and
accessible shares, entire-fibre actuation, acquisition duration,
absolute FIRST clock alignment, archive/source/epoch/controller
permissions and the general quantum/native-instrument and count
bridges remain unsupplied. The complete original quantum/count/source/
native problem is retained with these obligations.

## 追加锚（本行以下为增补区）
