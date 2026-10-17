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

## 8. A strict positive-residual norm gap from the original attained target

**Theorem 8.1 (strict separation from the zero positive residual).**
Retain the same root, all its source-enclosure and supplier premises in
Assumption 1.1, and the finite globally entire-cylinder feasible dual
and the same finite jointly attaining law in Assumption 1.4. If

$$
t\ge\max\{t_0,10000\},\qquad 0<\lambda<\infty,
$$

then, in exactly the normalization (IC.8),

$$
\|R_+\|_{\rm op}>\frac{t}{500}.
\tag{IC.34}
$$

This is the real Euclidean operator norm of the symmetric dual
coefficient matrix $Q-t\mathsf F$. It is neither a quantum trace or
diamond distance nor a physical resource or actual-label count. No
inertia premise on $R_-$ is needed. The domain here is FC Assumption
17.1 with its own additional cutoff $10000$; it does not extend the
$30000$ premise of
[RB Assumption 1.3](https://github.com/the-omega-institute/trureturing/blob/36adbdd8df3bc6615cae0f0f5fd1207239025477/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_RANK_ONE_BUDGET_EXCLUSION.md).
Here and below RB denotes that fixed source.

Proof. Use the static source expressions of (IC.1)–(IC.4), with
$A_\ell=E_{\ell,11}$, $B_\ell=E_{\ell,22}$ and
$a_\ell=-E_{\ell,12}$. FC Propositions 18.1 and 24.1 and the
positive-denominator estimates in FC Proposition 34.2 give

$$
\begin{gathered}
\alpha>0.876,\quad\beta>0.121,\quad\mu<12,\quad
\mathfrak c(x)>1/25,\\
0<A_\ell<B_\ell<0.02,\quad 0<a_\ell<0.00032,\quad
0<l_u<0.0052,\quad0<l_v<0.013,\\
0.0075<e<0.008,\qquad 0<d_*<0.022.
\end{gathered}
\tag{IC.35}
$$

Every decimal in this argument is an exact terminating rational.
These are static enclosures, with no small-saturated-mass or
large-budget inertia premise. In particular the coarse rectangle of
FC18, and also its FC24 widening to $m_1<0.51$, suffice for these
short bounds. Source membership in the nine GC6.1 dyadic rows supplies
the same root throughout. Evaluating source expressions on a rectangle
does not assume TP at any of its off-root points.

The circle identity and $2|uv|\le1$ give

$$
\begin{aligned}
|\ell|&\le B_\ell+a_\ell+l_u+l_v
 <0.03852<1/20,\\
|f|&\le e+d_*<3/100.
\end{aligned}
\tag{IC.36}
$$

These are the same uniform-height mechanisms used in RB.22–RB.23;
only static inputs are being reused, not RB's rank-one hypotheses.
Put $a_*=\sqrt\alpha$, $b_*=\sqrt\beta$ and
$x_*=(a_*,-b_*)$. This notation is local to this proof. It does not
refer to a negative-pure kernel contact. The point is unit and

$$
\begin{gathered}
\alpha\beta-(8/25)^2>
0.876\cdot0.121-(8/25)^2=899/250000>0,\\
f(x_*)=-2ea_*b_*-d_*\beta<-3/625.
\end{gathered}
\tag{IC.37}
$$

For this same law, the last three moments give

$$
\Lambda:=\int b_xxx^T\,d\pi
=\begin{pmatrix}U&0\\0&V_2\end{pmatrix}\succ0,
\qquad\operatorname{tr}\Lambda=\mu.
\tag{IC.38}
$$

This is FC Proposition 17.3, including its zero mixed entry, not a new
choice of failure marginal. Cauchy–Schwarz for coefficient mass one
gives $K\le\sqrt{\int u^2\,d\pi}=a_*$. Also

$$
J_t\le\int|\ell|\,d\pi+\int b_x|f|\,d\pi
<\frac1{20}+\frac3{100}\mu<\frac{41}{100}.
\tag{IC.39}
$$

Let $S_+=R_+$ and suppose, for contradiction,
$\|S_+\|_{\rm op}\le t/500$. Then $Q=t\mathsf F+S_+$.
Write $\mathcal L_\alpha(P_y)=y_0+\alpha y_3$. The target pairing
already underlying (IC.15) and RB.31 is now

$$
\begin{aligned}
y\cdot B
&=\mathcal L_\alpha(P_y)+\frac1t\operatorname{tr}(Q\Lambda)\\
&=\mathcal L_\alpha(P_y)-d_*V_2
                         +\frac1t\operatorname{tr}(S_+\Lambda),\\
\mathcal L_\alpha(P_y)-\lambda a_*
&=J_t+\lambda(K-a_*)+d_*V_2
                         -\frac1t\operatorname{tr}(S_+\Lambda).
\end{aligned}
\tag{IC.40}
$$

The sign is fixed by $\operatorname{tr}(\mathsf F\Lambda)=-d_*V_2$;
RB's substitution $Q=-t\mathsf F-\rho ww^T$ has a different sign.
The standard PSD trace inequality gives
$|\operatorname{tr}(S_+\Lambda)|\le\mu\|S_+\|_{\rm op}$.
For example it follows by summing the Rayleigh bounds against the
nonnegative eigenvalues of $\Lambda$. Since $\lambda(K-a_*)\le0$
and $V_2\le\mu<12$, (IC.40) implies

$$
\mathcal L_\alpha(P_y)-\lambda a_*
<\frac{41}{100}+\frac{11}{500}\,12+\frac{12}{500}
=\frac{349}{500}.
\tag{IC.41}
$$

Evaluate $P_y$ at the four points $(\epsilon a_*,\tau b_*)$,
$\epsilon,\tau\in\{\pm1\}$. Their equal average is
$\mathcal L_\alpha(P_y)$: the $u,v,uv$ terms cancel and
$u^2=\alpha$. At each point pure feasibility gives
$P_y-\lambda a_*\ge|\ell|\ge0$. Consequently at the particular
point $x_*$,

$$
B_*:=P_y(x_*)-\lambda a_*<\frac{349}{125},\qquad
B_*+\ell(x_*)<\frac{1421}{500}.
\tag{IC.42}
$$

This is sign averaging of polynomial evaluations. The pure four-corner
law has zero failure moments, whereas $B_5(t)=\mu/t>0$, so it is
not being substituted for the original feasible law.

Use global saturated feasibility at $x_*$ with report sign $+$ and
height sign $-$, whether or not this point is occupied or this sign
maximizes its saturated height. By (IC.8), after division by $D_c$,

$$
\begin{aligned}
0&\le B_*+\ell(x_*)+
\mathfrak c(x_*)x_*^T(2t\mathsf F+S_+)x_*,\\
B_*+\ell(x_*)&\ge\mathfrak c(x_*)
               [2t|f(x_*)|-x_*^TS_+x_*]\\
&>\mathfrak c(x_*)\left(\frac6{625}-\frac1{500}\right)t
>\frac{19}{62500}t\ge\frac{76}{25}.
\end{aligned}
\tag{IC.43}
$$

Here $x_*^TS_+x_*\le\|S_+\|_{\rm op}\le t/500$.
The bracket is strictly greater than $(19/2500)t>0$ before
multiplication by the lower capacity bound. The lower bound at
$10000$ exceeds the upper bound (IC.42) by

$$
\frac{76}{25}-\frac{1421}{500}=\frac{99}{500}>0.
\tag{IC.44}
$$

This contradiction proves the strict inequality, including at the
endpoint $t=10000$ whenever the supplied premises hold. The equality
threshold of these particular coarse upper and lower expressions is
$177625/19<10000$; no sharp cutoff is asserted. $\square$

## 9. The complete paired inventory on the separated indefinite domain

**Corollary 9.1 (at most two directed paired groups).** Under Theorem
8.1's hypotheses, suppose separately that $R_-$ is indefinite. Every
compatible paired group in the complete inventory, including unused
ones, has $\ell(x)>0$, $\eta_1(x)\ge0$ and $R_+x=0$.
There are at most two such directed groups.

Proof. Theorem 4.1 already proves the positive-pure and common-kernel
necessity for every supplied pair. Its local ingredients are the
value-and-tangency argument of
[RC Theorem 70.1](https://github.com/the-omega-institute/trureturing/blob/321589a8be98de4fe179f99f6e593d8784952db1/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md)
and the negative-pair exclusion in FC Theorem 34.3. In the complete
endpoint setting used here, the nonzero pure-height fact is FC19/20.
At a compatible pair, the two smooth nonnegative signed gaps and
their angular derivatives vanish. Thus $x^TR_\sigma x=0$ and
$(x^\perp)^TR_\sigma x=0$. These two equations give
$R_\sigma x=0$, rather than inferring a kernel vector from a quadratic
isotropic zero alone. Indefiniteness makes $R_-$ invertible, excluding
the negative sign. For the positive sign Theorem 8.1 gives $R_+\ne0$.
A nonzero $2\times2$ matrix has kernel dimension at most one. A kernel
line meets the directed circle in two distinct antipodes; an invertible
$R_+$ gives no pair. Existence of either allowed direction as a contact
is not implied. $\square$

The algebraic zero-$R_+$ possibilities retained by Theorem 4.1 and
Definition 6.2 are therefore excluded only in Theorem 8.1's additional
domain. This does not exclude weak-zero saturated heights. No inertia
theorem is transported to $10000$: FC34.3's full dichotomy uses its
small-mass range, and RB Corollary 7.2 supplies indefiniteness only at
$t\ge\max(t_0,2000000000)$. At the latter range its own supplied
finite attained-class premises can supply the separate inertia premise.

Both independent columns of every allowed pair remain in (IC.31),
with all nonnegative masses and all fractions
$\xi=a_1/(a_0+a_1)$ for positive total mass. Antipodes remain separate.
The bound concerns only paired groups, with no saturated-singleton,
total-group or actual minimum-count bound. Negative pure singletons,
reverse singletons, other saturated singletons and unused contacts
remain in the complete inventory.

## 10. Original capacity slack and the pure-coordinate obstruction

**Theorem 10.1 (positive conserved slack at the enclosed original source).**
Retain Assumption 1.1 and any feasible finite law of Definition 1.3,
with finite $t\ge t_0$. Write $\zeta=\xi\mathfrak c=b_x/t$,
distinct from the endpoint heights $\eta_j$, and define

$$
\begin{gathered}
\chi_c(x,\zeta)=N_c(x)-\zeta D_c(x)=(1-\xi)N_c(x)\ge0,\\
A_c=N_u\alpha+N_v\beta,\qquad C_c=D_uU+D_vV_2,\\
\int\chi_c\,d\pi=A_c-C_c/t>1/200,\qquad
1/2000<N_uD_v-N_vD_u<1/1000.
\end{gathered}
\tag{IC.45}
$$

Every feasible endpoint representation therefore has positive
pure-coordinate mass. If eight occupied groups are saturated
singletons, at least one other occupied group carries pure mass.
For fixed directions and allowed endpoint coordinates, if exactly one
group carries all the slack and no other non-saturated coordinate is
activated, its pure mass cannot be removed by a slack-preserving
reweighting.

Proof. Expand the slack using $v^2=1-u^2$:

$$
\chi_c=N_v+(N_u-N_v)u^2-D_v\zeta
                                -(D_u-D_v)\zeta u^2.
\tag{IC.46}
$$

Integrating the original moment rows gives $A_c-C_c/t$, using
$\int\zeta\,d\pi=\mu/t$, $\int\zeta u^2\,d\pi=U/t$
and $\mu-U=V_2$. This identity holds before any contact or height
assumption. It is a source-specific linear combination of the existing
rows, not an additional constraint imposed on a new marginal.

Here are strict rational bounds obtained from all nine GC Definition
6.1 rows and the uncancelled axial formulas (IC.3):

| Expression | Strict rational outer interval |
| --- | --- |
| $D_u$ | $(0.039505688487,0.039505688488)$ |
| $D_v$ | $(0.095020185595,0.095020185596)$ |
| $N_u$ | $(0.008354546087,0.008354546088)$ |
| $N_v$ | $(0.006115032697,0.006115032698)$ |
| $A_c$ | $(0.008080683454,0.008080683455)$ |
| $C_c$ | $(0.667238599501,0.667238599502)$ |

The enclosure has an exact source-bound reconstruction. Divide each
of the nine integer endpoint pairs of GC6.1 by $2^{224}$. Form
$r_s=c_{\rm src}dh_1/(abh_2)$, $\alpha=(1+r_s)^{-1}$,
$\beta=1-\alpha$ and
$\delta=ab/(h_0h_1)+c_{\rm src}d/(h_0h_2)$. Then evaluate
(IC.3) and $V,W,U,V_2,A_c,C_c$ by endpoint addition, subtraction,
the minimum and maximum of four endpoint products, and reciprocal
only for positive intervals. These formulas require no radicals and
no TP simplification. Outward rounding to denominator $10^{12}$
gives the displayed table. Thus the integer comparisons are
reconstructible from the actual source rows, without a sampled root.

For the determinant, it already suffices to subtract
$[0.006115032697,0.006115032698]
 [0.039505688487,0.039505688488]$ from
$[0.008354546087,0.008354546088]
 [0.095020185595,0.095020185596]$ by these outward rules.
Both endpoints are strictly between $1/2000$ and $1/1000$.
Also $A_c>0.008$, $C_c<0.7$ and $C_c/A_c<100$.
FC24's dyadic bound
$264.809031388577<t_0<264.809031388578$ gives $t_0>250$;
its coarse rectangle alone does not give that fact. Hence for all
$t\ge t_0$,

$$
A_c-C_c/t>0.008-0.7/250=13/2500>1/200.
\tag{IC.47}
$$

These are expression inequalities at the stipulated root. They supply
neither source existence nor off-root TP.

On a saturated endpoint $\chi_c=0$; on a pure endpoint
$\chi_c=N_c(x)>0$. A compatible pair with masses $(a_0,a_1)$
contributes exactly $a_0N_c(x)$. Thus positive total slack requires
a positive pure coordinate, even if it belongs to a fractional label.
If one fixed group alone carries slack, conservation fixes its pure
mass to $(A_c-C_c/t)/N_c(x)>0$. Making its saturated mass zero leaves
that group occupied. The argument does not prohibit transferring slack
to other original contacts or changing directions in another law.
$\square$

## 11. A mixed-tag fixed-support interpolation interface

**Definition 11.1 (eight selected original saturated singleton groups).**
Under Assumptions 1.1 and 1.4, select eight occupied groups of
$\mathscr G$, each a saturated singleton, with eight pairwise distinct
finite slopes $z_i$. All other columns and their weights stay fixed,
including both coordinates of every pair and every unused contact.
Use the actual direction tags and maximizing height tags:

$$
\begin{gathered}
x_i=\epsilon_i(1,z_i)^T/s_i,\quad s_i=\sqrt{1+z_i^2},\quad
\epsilon_i\in\{\pm1\},\quad d_i=d_c(z_i),\quad n_i=n_c(z_i),\\
\mathcal W(z)=d_c(z)\sqrt{1+z^2},\qquad
\mathcal V(z)=d_c(z)E(z)+t n_c(z)\bar f(z),\\
H_i=\mathcal V(z_i)+\epsilon_i\mathcal W(z_i)(l_u+l_vz_i)
=(1+z_i^2)d_i\eta_1(x_i),\\
\sigma_i\in\operatorname{argmax}_{\sigma\in\{\pm1\}}
                                      \sigma\eta_1(x_i),\qquad
\rho_i=\frac{p_i}{(1+z_i^2)d_i}>0,\\
P_8(z)=\prod_{i=1}^8(z-z_i),\qquad
\mathcal L_r(F)=\sum_{i=1}^8\frac{z_i^rF_i}{P_8'(z_i)}
\quad(r=0,1,2),\\
\mathcal R=\begin{pmatrix}
\mathcal L_0(\epsilon\mathcal W)&\mathcal L_1(\epsilon\mathcal W)&\mathcal L_2(\epsilon\mathcal W)\\
\mathcal L_0(\epsilon z\mathcal W)&\mathcal L_1(\epsilon z\mathcal W)&\mathcal L_2(\epsilon z\mathcal W)\\
\mathcal L_0(\sigma H)&\mathcal L_1(\sigma H)&\mathcal L_2(\sigma H)
\end{pmatrix}.
\end{gathered}
\tag{IC.48}
$$

The evaluations in a tagged row use its actual $\epsilon_i,\sigma_i$.
Either maximizing description is retained at zero saturated height;
$\sigma_iH_i=0$ there. $\mathcal W$ differs from the source scalar
$W$ of (IC.4), and $\mathcal R$ differs from $R_\pm$.

**Theorem 11.2 (exact criterion and nonnegative whole-singleton pivot).**
In Definition 11.1, $\det\mathcal R=0$ if and only if there is a
nonzero signed change of just those eight endpoint masses preserving
all eight $\Gamma$ moments, achieved $K$ and attained $J_t$.
If $a=(a_0,a_1,a_2)^T\ne0$ is in $\ker\mathcal R$, put

$$
\begin{gathered}
A(z)=a_0+a_1z+a_2z^2,\qquad
\delta\rho_i=\frac{A(z_i)}{P_8'(z_i)},\qquad
\delta p_i=(1+z_i^2)d_i\delta\rho_i,\\
\tau_* =\min_{\delta\rho_i<0}
                  \frac{\rho_i}{-\delta\rho_i}>0.
\end{gathered}
\tag{IC.49}
$$

For $0\le\tau\le\tau_*$ the changed masses are nonnegative and
retain all those joint data. At $\tau_*$ at least one selected
entire singleton group has zero mass and is omitted. Simultaneous
zeros are permitted; every remaining positive mass is finite and
strictly positive. Other groups and all fixed original coordinates,
capacities and heights stay fixed.

Proof. Let $\mathbb P_j$ denote polynomials of degree at most $j$.
Multiplying the original augmented column $(\Gamma(x_i,1),|u_i|)$
by the positive factor $(1+z_i^2)d_i$ gives, in original row order,

$$
\big((1+z_i^2)d_i,\ \epsilon_i\mathcal W_i,
 \epsilon_i z_i\mathcal W_i,\ d_i,\ z_i d_i,
 (1+z_i^2)n_i,\ n_i,\ z_i n_i,\ \mathcal W_i\big)^T.
\tag{IC.50}
$$

The six polynomial rows span $d_c\mathbb P_2+n_c\mathbb P_2$.
This equals $\mathbb P_4$ here: the nonzero determinant
$D_uN_v-D_vN_u$, supplied by Theorem 10.1, makes $d_c,n_c$
span $1,z^2$; their multiples by $z$ and $z^2$ then span all
five monomials through degree four. If that determinant were zero
without the original source-enclosure premise, the span would instead
have dimension three. The necessity argument below would then require
that explicit nondegeneracy premise. Sufficiency does not require it.

Reuse the distinct-node leading-coefficient identity in Carl de Boor,
[*Divided Differences*, Example 9, (41)](https://arxiv.org/html/math/0502036v1):
$\sum_i F(z_i)/P_8'(z_i)=0$ for $\deg F\le6$.
Thus each vector $A(z_i)/P_8'(z_i)$ with $\deg A\le2$
annihilates all rows in $\mathbb P_4$. These vectors are three
independent directions, since a nonzero quadratic cannot vanish at
eight distinct nodes. The five-row Vandermonde matrix has rank five,
so they exhaust its kernel. This is standard barycentric interpolation
used inside the original tagged problem, not a new interpolation theorem.

The contact equation is indispensable for the remaining rows. With
the actual original failure polynomial

$$
q(z)=(y_5+y_6)+y_7z+y_5z^2,\qquad
L_c(z)=d_c(z)p_y(z)+n_c(z)q(z)\in\mathbb P_4,
$$

the saturated contact equality, after the same positive scaling, is

$$
L_c(z_i)+\epsilon_i\mathcal W_i(y_1+y_2z_i)
                         -\sigma_iH_i-\lambda\mathcal W_i=0.
\tag{IC.51}
$$

There is no missing $t$ in (IC.50): its failure intensity is
$\zeta=b_x/t=\mathfrak c$; the height in (IC.51) uses
$\ell+t\mathfrak c f$. No fitted external quadratic replaces $q$.

For the barycentric change, the first two rows of $\mathcal R a=0$
preserve the directed first moments. Its third row preserves $J_t$,
since the scaled absolute height is $\sigma_iH_i$.
Summing (IC.51) against $\delta\rho$ gives
$\delta J_t+\lambda\delta K=0$ because the polynomial and first
two tagged sums vanish. As $\lambda>0$, $\delta K=0$ too. This
proves sufficiency for all nine rows and height. Conversely a nonzero
fixed-support change preserving the nine rows annihilates
$\mathbb P_4$, so it has exactly the barycentric form. The first
two tagged sums vanish. Contact equality and preserved $K$ force
the height sum to vanish, giving $\mathcal R a=0$. This proves
necessity without assuming independence of any other original rows.

The direction is nonzero and preserves the mass row. All scale
factors are positive, so it has both signs. Hence the finite minimum
in (IC.49) exists and is strictly positive. At its value all masses
remain nonnegative and at least one is zero. Because each selected
group is a singleton, that zero deletes a whole group. Contact equality
preserves optimality at the original achieved $K$. Omission of a zero
coefficient is before the unknown-input experiment, not postselection.
$\square$

For a common maximizing height sign $\sigma$, the algebraic identity
$\mathcal V\in\mathbb P_4$ would give

$$
\mathcal L_r(\sigma H)=
\sigma l_u\mathcal L_r(\epsilon\mathcal W)
+\sigma l_v\mathcal L_r(\epsilon z\mathcal W),
\tag{IC.52}
$$

and thus a singular matrix. But FC Theorems 12.1 and 12.3 allow at
most three saturated contacts per report/height tag, hence at most six
admitting any one common maximizing height sign. Eight such contacts
with a common height sign have no instance in this original source
class. Weak-zero double descriptions do not evade that cap. An eligible
eight-point configuration must have mixed height signs. In that case
$\mathcal L_r(\sigma\mathcal V)$ need not vanish: multiplication
by varying $\sigma_i$ prevents the polynomial annihilation used in
(IC.52). No mixed-sign singularity or original attained eight-point
instance satisfying $\det\mathcal R=0$ is supplied. The theorem is
a criterion on fixed occupied support, not a universal removal theorem.
An antipodal pair has equal slope and is outside its distinct-slope
hypothesis while remaining two admitted labels in the full problem.

## 12. Full-group directions and a capacity-faithful method obstruction

**Definition 12.1 (fixed complete-group equations and whole-pair exit).**
On the contact chart, let $p_{gj}$ be the endpoint masses of group $g$,
with an absent endpoint identically zero. Put
$\rho_{gj}=p_{gj}/[(1+z_g^2)d_c(z_g)]$. In a pair the two
coordinates are independent; no fixed fraction is imposed. The full
nine-row preservation equations are equivalently

$$
\begin{aligned}
\sum_g d_c(z_g)(1,z_g,z_g^2)
                  (\delta\rho_{g0}+\delta\rho_{g1})&=0,\\
\sum_g n_c(z_g)(1,z_g,z_g^2)\delta\rho_{g1}&=0,\\
\sum_g\mathcal W(z_g)(1,\epsilon_g,\epsilon_g z_g)
                  (\delta\rho_{g0}+\delta\rho_{g1})&=0.
\end{aligned}
\tag{IC.53}
$$

Indeed (IC.50) gives these rows directly, with the failure rows zero
on the pure sheet; replacing $1+z^2$ and $1$ by $1,z^2$ is an
invertible row operation. On contacts, preserving these equations
preserves $J_t$ by $g=y\cdot\Gamma-\lambda k$. Opposite-height
singletons at a common directed angle remain different groups in the
sums. All unused coordinates remain in the complete inventory, whether
held fixed or admitted as additional variables in another direction.

For an initially occupied pair with $\rho_{g0},\rho_{g1}>0$, a
single affine nonnegative pivot deletes the whole group exactly when

$$
\delta\rho_{g0}<0,\quad\delta\rho_{g1}<0,\quad
\frac{\rho_{g0}}{-\delta\rho_{g0}}
=\frac{\rho_{g1}}{-\delta\rho_{g1}}=\tau_*,
\tag{IC.54}
$$

and every other coordinate stays nonnegative up to that pivot. This
follows by solving both affine zero equations; either one alone leaves
the group occupied. An initially zero coordinate must be zero at exit,
and no ratio with its zero initial mass is taken. The height-preserving
merge condition remains exactly $\eta_0\eta_1\ge0$ for two positive
endpoint masses, including either weak zero; the strict opposite-sign
loss and its physical HALF factor remain Definition 1.5. No rank or
endpoint-deletion argument replaces these whole-group conditions.

**Proposition 12.2 (quartic data and contrast still miss a directed row).**
For the actual positive axial coefficients of (IC.3), there are two
three-atom saturated coefficient probability laws on the directed circle
with identical scaled polynomial data through degree four and identical
$K$, but different $v$ first moments. Each uses the original positive
capacity $n_c/d_c$. They are method-level counterexamples; neither law
is asserted to have the original target $B(t)$ or to be on an attained
optimal face.

Proof. Set $L_0=1+D_u/D_v$, $x_j=L_0+j$ for $j=1,2,3$, and
use six distinct slopes $\zeta=\pm\sqrt{x_j}$, all with direction
tag $+$. Let

$$
P_6(z)=\prod_{j=1}^3(z^2-x_j),\qquad
b_\zeta=1/P_6'(\zeta),\qquad
a_\zeta=b_\zeta(1+\zeta^2)d_c(\zeta).
\tag{IC.55}
$$

There are three positive and three negative $a_\zeta$, since the
derivatives at six ordered simple real roots alternate in sign. The
de Boor leading-coefficient identity annihilates polynomials through
degree four against $b_\zeta$. In particular
$\sum a_\zeta=0$, so the positive and negative parts have a common
strictly positive normalizer $M_0$. Divide each part by $M_0$ to
obtain the two probability laws, with saturated capacity $n_c/d_c$.
Their reweighted masses $p/[(1+z^2)d_c]$ agree on all quartics.

The six polynomial rows of (IC.50) consequently agree. The $u$ and
$K$ rows agree as well: on this positive-$u$ arc both have scaled
value $\mathcal W(z)$, which is even, whereas
$b_{-\zeta}=-b_\zeta$. The sole unmatched augmented row is $v$,
whose unnormalized difference is

$$
\begin{gathered}
\sum_\zeta b_\zeta\zeta\mathcal W(\zeta)
=[x_1,x_2,x_3]g
=\frac{g(x_1)-2g(x_2)+g(x_3)}2>0,\\
g(x)=(D_u+D_vx)\sqrt{1+x},\qquad
g''(x)=\frac{4D_v+3D_vx-D_u}{4(1+x)^{3/2}}.
\end{gathered}
\tag{IC.56}
$$

The first equality follows by grouping the two roots at each $x_j$:
$P_6'(\zeta)=2\zeta\prod_{k\ne j}(x_j-x_k)$.
The divided difference and its convexity sign are standard tools, with
equal spacing one. At $x\ge x_1=2+D_u/D_v$ the numerator of $g''$
is at least $10D_v+2D_u>0$. Strict convexity proves the strict
difference for the original coefficients, without substituting
synthetic source amplitudes. Dividing by the common $M_0$ preserves
the inequality. These laws need not match $B(t)$, contact equality
or $J_t$, so they refute only the proposed sufficiency of quartic
data plus $K$ for recovering every original row, not $U_7$ or $U_8$.

The full labelled test space has a related direct obstruction to a
global scalar Chebyshev-system transfer. Its nonzero combination
$k-u=|u|-u$ vanishes on the whole positive-$u$ directed arc and is
positive on the negative-$u$ arc. Its nonzero combination $\chi_c$
from (IC.46) vanishes on the entire saturated sheet and is positive
on the pure sheet. These infinite zero sets violate the finite-zero
property of a scalar Chebyshev system on the complete labelled domain.
Invertible row changes, positive pointwise scaling and injective
reparametrization preserve the obstruction. Piecewise systems or
additional relations on a special finite contact inventory are not
excluded. This explains the missing premise of the Dette–Melas
interface in Definition 6.1; it is not a nonexistence theorem for all
possible original-law compression methods. $\square$

## 13. Attribution, same-law transfer and the unresolved mixed relation

**Definition 13.1 (mathematical sources and conditional synthesis).**
The strict norm gap combines the original attained target and its full
failure covariance with four nonnegative sign-corner evaluations and
the negative failure height at the source direction
$(\sqrt\alpha,-\sqrt\beta)$. The PSD trace bound,
Cauchy–Schwarz and sign averaging are standard intermediate tools.
RB Proposition 5.1, especially RB.31, supplies the prior original
target/failure-trace mechanism; RB.22–RB.23 supplies the uniform-height
mechanism. The different substitution and trace sign in (IC.40) are
essential. RB's own cutoffs and rank-one conclusion are unchanged.
Corollary 9.1 credits RC70.1 and FC34.3 for the local kernel and
negative-pair arguments; rank-nullity itself is standard.

The capacity-slack and interpolation statements use FC.26/FC.57,
GC12.2's joint moments, FC3.3's complete compatible groups and FC4.2's
contact equality. GC Proposition 19.1 already supplies positive
capacity reweighting and the polynomial-quadrature boundary;
(IC.48)–(IC.51) keep the remaining directed and height tags explicitly
in a fixed original support calculation. The source nondegeneracy and
strict slack in Theorem 10.1 are conditional expression consequences
of GC6.1's actual nine source rows. The leading-coefficient and
divided-difference identities are reused from de Boor, Example 9,
(41); the zero-integral support and finite-dimensional moment
interfaces retain the di Dio–Schmüdgen attribution in Definition 6.1.
No generic interpolation, convexity, quadrature, stationarity or
rank theorem is claimed as new. These are repo-derived conditional
source-specific deductions and a method obstruction, with no worldwide
priority claim.

**Open problem 13.2 (mixed signs, slack transfer and complete original coverage).**
It remains to supply a relation forcing the mixed-tag determinant to
vanish on each face that needs this fixed-support removal, or a different
original-law construction preserving all joint rows and deleting whole
groups. Singularity is not established for mixed signs; nonsingularity
would exclude only that particular fixed-support direction, not every
alternative law, direction or activation of unused contacts. Equal
slopes, antipodes, pure groups, paired groups and simultaneous pair
exit remain in the full problem. The positive slack requires another
pure-bearing group beside eight saturated singletons. Starting with
nine occupied groups and deleting only one leaves eight, so that pivot
alone cannot establish seven groups. Universal $U_7$, universal $U_8$
where required, and all-alternative eight-/nine-low necessity remain
the complete-group problems of §7.

Theorem 8.1 constructs neither a finite dual nor a jointly attaining
tuple. It does not extend to $\lambda=0$, absent or nonfinite duals,
unattained values, unsupplied boundaries or infinite budget. Its
paired-group consequence also requires the separate indefinite $R_-$
premise. The algebraic possibility of zero $R_+$ below the stated
domain is not resolved. Neither result bounds saturated singletons or
the total original alphabet.

All restrictions concern the same law. A permitted pivot changes that
law's selected coefficient masses while preserving its complete eight
moments, achieved $K$, within-label absolute $J_t$ and pointwise
capacity. Under the inherited common constructor it therefore preserves
the complete complex forgotten-label live map and each of the five
Borel failure maps, with arbitrary passive-reference conditional
operators. It does not say that the labelled acquisition instrument
or its probability measure stays identical. The resulting height
remains $(H_0+J_t)/2$, with the original HALF factor. One specimen,
twelve histories, both zero failure targets, all supported-zero
competitors and the counted coherent high completion remain as in
Assumption 1.1. The $1+$ minimum-count identity is still an equality
of minima under its supplier, not of counts of every instrument.

All source/root/isolation/Jacobian/rank/TP, stopped-cq minimax,
sharp worst-history JOINT cost, separate unaveraged equality,
full-complex multi-Kraus necessity, physical capacity and constructor
suppliers remain distinct conditional premises. Accessible shares and
the whole counted fibre stay in the resource accounting; survivors
are strictly positive at finite budget, controls are TP, FIRST is
absolute $6+a$, and no positive-carrier action follows failure.
No copy, helper, oracle, reset, retry, postselection, acceptance or
survival division is supplied. All-budget/all-contrast evaluated
roofs, branch ordering and coverage, complete root/multiplicity and
collision data, coefficients and orientations, capacity/rank/count
transitions, endpoint/threshold/budget/degenerate gluing, next terms
and uniform joint limits remain required. Native access/calibration,
coherently counted storage, whole-fibre actuation, duration, absolute
clock alignment, archive/source/epoch/controller permissions and the
general native-instrument/count bridge remain unsupplied. These
ordinary conditional arguments assert no kernel, physical or native
certification of those remaining premises.

## 追加锚（本行以下为增补区）

## 14. Full failure covariance and three-pure whole-group activation

**Definition 14.1 (same-source endpoint Gram and canonical joint columns).**
Retain the complete source and comparison premises of Assumption 1.1,
with the quantities of Definitions 1.2–1.3. For any nonnegative common
law with moments $B(t)$, let $\rho_0,\rho_1$ be its pure and saturated
endpoint measures, respectively:

$$
\begin{gathered}
d\rho_0(x)=\int(1-\xi)\,d\pi(x,\xi),\qquad
d\rho_1(x)=\int\xi\,d\pi(x,\xi),\qquad S=\int1\,d\rho_1,\\
a(x)=(1,u,v)^T,\quad D_3=\operatorname{diag}(1,\alpha,\beta),\quad
M_j=\int a(x)a(x)^T\,d\rho_j(x),\quad M_0+M_1=D_3,\\
c_{\min}=\min\{N_u/D_u,N_v/D_v\}>0,\quad
T_3=\frac{\mu+\max(V,W)}{c_{\min}},\quad
C=\frac{\mu}{tc_{\min}},\quad m=\min(\alpha,\beta)>0.
\end{gathered}
\tag{IC.57}
$$

The measure notation denotes integration against the indicated endpoint
projections; no disintegration hypothesis is added. On an endpoint law
these are its actual sheet measures. The rank of $M_0$ concerns directed
pure coordinates, not physical state purity, Kraus multiplicity or actual
label count. The exact capacity minimum is FC Proposition 34.2's
positive-denominator weighted mean of the two axial ratios.

When Assumption 1.4 is also supplied, retain the entire inventory and
partition of Definition 1.5 and the polytope of (IC.31). For an endpoint
column indexed by $i$, write

$$
H_i=\begin{pmatrix}\Gamma_i\\\kappa_i\end{pmatrix},\qquad
H=\begin{pmatrix}A\\\kappa^T\end{pmatrix},\qquad
\kappa_i=|u_i|.
\tag{IC.58}
$$

Here $A$ has eight rows; $H$ has nine. The notation $H$ in this
section is a moment matrix, distinct from the signed heights $H_i$
in §11. An index set $I$ is called canonical here only when it has
nine strictly positive coordinates in nine distinct complete groups
and $H_I$ is invertible, as supplied by FC Theorem 6.1 for its
nonconstant critical edge. No occupied pure coordinate has an occupied
saturated companion in such a support. Its companion remains available
if the complete group is a pair. For $j=7,8$, $U_j$ has FC Definition
5.1's complete vertex/edge meaning, equivalently the union of contrast
images of coordinate faces using at most $j$ complete groups by FC
Theorem 5.2; thus $U_7$ agrees with (IC.32).

**Theorem 14.2 (uniform original pure rigidity and one-companion deletion).**
Under Definition 14.1, every nonnegative law with the same original
$B(t)$ satisfies the full three-dimensional bound

$$
M_0\succeq\left[1-\frac{\mu+\max(V,W)}{tc_{\min}}\right]D_3.
\tag{IC.59}
$$

If $t>T_3$, every finite such endpoint law has at least three distinct
positive pure coordinates. Now also impose Assumption 1.4 and fix
$w^0\in\mathcal P(r)$ with a canonical support $I$, exactly three
pure and six saturated coordinates. If one occupied pure coordinate
$p\in I$ has its zero-weight saturated companion $j$ in its own
compatible complete group, there is a finite law in $\mathcal P(r)$
with at most eight occupied complete groups. It preserves the same
$B(t)$, active $K=r$, $J_t$ and original absolute height.
The alternative condition $C(1+1/m)<1$ suffices for all these rigidity
and deletion conclusions.

Proof. The bound is a supporting step for the whole-group conclusion.
All integrals in it use the single positive saturated measure $\rho_1$.
The three original failure rows and the circle identity give

$$
\int\mathfrak c(x)\,d\rho_1=\frac\mu t,\qquad
\int\mathfrak c(x)xx^T\,d\rho_1
=\frac1t\operatorname{diag}(\alpha V,\beta W).
\tag{IC.60}
$$

In particular the mixed entry is zero and both diagonal entries are
strictly positive. These are GC Proposition 12.2's full failure
covariance, in angular coordinates, not separately chosen scalar
marginals. Since $\mathfrak c\ge c_{\min}$,

$$
S\le\frac\mu{tc_{\min}},\qquad
\int xx^T\,d\rho_1\preceq
\frac1{tc_{\min}}\operatorname{diag}(\alpha V,\beta W).
\tag{IC.61}
$$

For $z=(z_0,z_1,z_2)^T$, put
$L_z(x)=z_1u/\sqrt\alpha+z_2v/\sqrt\beta$ and
$q_z^2=z_1^2+z_2^2$. The standard Cauchy–Schwarz inequality for
this same positive measure bounds its odd cross term. It gives

$$
\begin{aligned}
z^TD_3^{-1/2}M_1D_3^{-1/2}z
&=\int(z_0+L_z)^2\,d\rho_1\\
&\le\left(|z_0|\sqrt S+
                  \sqrt{\int L_z^2\,d\rho_1}\right)^2\\
&\le\frac{(\sqrt\mu\,|z_0|+
                      \sqrt{\max(V,W)}\,q_z)^2}{tc_{\min}}\\
&\le\frac{\mu+\max(V,W)}{tc_{\min}}\|z\|^2.
\end{aligned}
\tag{IC.62}
$$

The last inequality is ordinary Euclidean Cauchy–Schwarz. Subtracting
from $D_3$ proves (IC.59), including the degenerate case $S=0$ as
an inequality. At $t>T_3$ its right side is positive definite. A sum
of fewer than three positive rank-one pure coordinate matrices has
rank at most two, so cannot equal $M_0$. This inference holds for
every common endpoint law with $B(t)$, including laws reached by
activation. It uses neither an initial-rank assumption alone nor
small mass measured only at the starting law. Finally
$\max(V,W)\le\mu/m$, so $C(1+1/m)<1$ implies $t>T_3$.

For the claimed deletion, keep all inventory columns and define

$$
\delta_j=1,\qquad \delta_I=-H_I^{-1}H_j,\qquad
\delta_i=0\quad(i\notin I\cup\{j\}),\qquad
\tau=\min_{i\in I:\delta_i<0}\frac{w_i^0}{-\delta_i}.
\tag{IC.63}
$$

The mass row gives $\sum_{i\in I}\delta_i=-1$. Thus the minimum
is over a nonempty finite set and $0<\tau<\infty$. On
$0\le s\le\tau$, $w(s)=w^0+s\delta$ is nonnegative, has
$Hw(s)=(B(t),r)^T$, and activates only the saturated column $j$.
Every changed column is a contact of the same supplied dual, so
$g_i=y\cdot\Gamma_i-\lambda\kappa_i$ and $J_t$ is unchanged.
At $s=\tau$ at least one old coordinate dies.

None of the three old pure coordinates can die: no pure coordinate
is activated, and such a death would leave at most two positive pure
coordinates in another nonnegative law with the same $B(t)$,
contradicting (IC.59). Consequently an old saturated coordinate
$q\in I$ dies. Its group is different from the group of $p,j$,
and all its other coordinates remain zero. The nine original groups
were distinct, and the only newly positive coordinate belongs to an
already occupied group. Hence the death of $q$ empties its whole
group and leaves at most eight. Ties can empty more groups and cause
no difficulty. The parent $p$ remains positive; its paired fraction
at exit is $w_j(\tau)/(w_p(\tau)+w_j(\tau))\in[0,1]$.
FC Theorem 3.3 merges all occupied compatible groups, retaining
$(B,r,J_t)$ and producing exactly one original fractional low label
per remaining group. Zero total masses are omitted. $\square$

**Corollary 14.3 (a sufficient original finite range).** Retain all
source premises of Assumption 1.1. For finite $t\ge\max(t_0,800)$,
every nonnegative same-$B(t)$ law satisfies

$$
M_0\succ\frac2{25}D_3.
\tag{IC.64}
$$

In particular Theorem 14.2's exact-three-pure deletion applies
throughout this range whenever its separate attained-face and
companion premises hold.

Proof. The integer endpoints in all nine rows of the pinned GC
Definition 6.1, divided by $2^{224}$, lie strictly inside FC18's
coarse intervals for the seven amplitudes and
$0.49<m_1<0.50$, $0.34<m_2<0.35$. Each containment follows
by multiplying its rational endpoints by $2^{224}$ and comparing
the corresponding original integer pair. Use the cancelled formulas

$$
r_s=\frac{c_{\rm src}dh_1}{abh_2},\quad
\alpha=\frac1{1+r_s},\quad\beta=1-\alpha,\quad
\delta=\frac{ab}{h_0h_1}+\frac{c_{\rm src}d}{h_0h_2}.
$$

Exact outward rational interval evaluation of these expressions and
(IC.3)–(IC.4) gives the following sufficient bounds. The capacity
entry is a lower bound for
$\min(N_u,N_v)/\max(D_u,D_v)$, hence also for $c_{\min}$.

| Expression | Coarse rectangle | Original nine dyadic rows |
| --- | --- | --- |
| uniform capacity lower bound | $0.063190656152$ | $0.064355091074$ |
| upper bound for $V$ | $8.218570560831$ | $8.062157279213$ |
| upper bound for $W$ | $33.674855184265$ | $33.364535594888$ |
| upper bound for $\mu$ | $11.379968841496$ | $11.156300845208$ |

All lower inequalities and upper inequalities in the table are strict;
all decimals are exact rationals. To obtain the first row, form the
lower endpoints of $N_u,N_v$ and upper endpoints of $D_u,D_v$
by addition, the extrema of four endpoint products, and reciprocal
only for positive intervals, then take the indicated minimum divided
by maximum. The remaining rows use those same outward operations on
$V=m_2h_1^2/b^2$, $W=m_1h_2^2/d^2$ and
$\mu=\alpha V+\beta W$. Lower endpoints round down and upper
endpoints round up to denominator $10^{12}$. No radical, TP
simplification, centre evaluation or sampled corner is involved.
In particular the coarse capacity lower bound is exactly
$7898832019/125000000000>1/16$, consistent with FC24.1.

The shorter comparisons in FC (FC.147) follow independently from
these same containing intervals:

$$
\begin{gathered}
V<\frac{0.35(0.707)^2}{(0.1459)^2}<\frac{411}{50},\qquad
W<\frac{0.50(0.810)^2}{(0.0987)^2}<\frac{842}{25},\\
\alpha<0.879,\quad\beta<0.124,\qquad
\mu<0.879\frac{411}{50}+0.124\frac{842}{25}
=\frac{114017}{10000}<12.
\end{gathered}
$$

Thus $c_{\min}>1/16$, $\max(V,W)<34$ and
$T_3<16(12+34)=736$. For $t\ge800$,
$1-T_3/t>1-736/800=2/25$. Apply (IC.59).
These expression enclosures preserve the stipulated single source;
they supply no root existence or off-root TP. $\square$

**Corollary 14.4 (exact-three-pure critical supports have no paired pure parent).**
Under Assumptions 1.1 and 1.4 with $t>T_3$, let
$r\in[r_-,r_+]\setminus U_8$ and take the canonical edge
representation of FC Theorem 6.1 at $r$. If it has exactly three
positive pure coordinates, none belongs to a compatible paired group.

Proof. FC Theorem 6.1 gives nine positive columns in nine distinct
groups, rank $A_I=8$ and rank $H_I=9$. For any occupied pure
coordinate in a pair, its companion has zero weight and is available
in the complete inventory. Theorem 14.2 would give another law at
the same $(B,r,J_t)$ with at most eight groups. FC Theorems 3.3
and 5.2 would put $r$ in $U_8$, a contradiction. This excludes
only the stated critical support pattern; it asserts no universal
$U_8$ or $U_7$ coverage. $\square$

**Corollary 14.5 (an exact-three-pure antipodal obstruction at the original target).**
For any finite nonnegative same-$B(t)$ endpoint law, if its pure
support consists of exactly three distinct points and contains an
antipodal pair, then

$$
m<2S\le\frac{2\mu}{tc_{\min}}.
\tag{IC.65}
$$

Consequently such a pure pattern is impossible whenever
$2\mu/(tc_{\min})\le m$, including equality in this sufficient
condition. No contact or optimality premise is needed.

Proof. Write the pure points as $x,-x,y$, with strictly positive
masses $a,b,c$ and $y\ne\pm x$. Choose a unit $n\perp x$.
The original zero first moments and angular covariance give

$$
 c\,n\cdot y=-\int n\cdot z\,d\rho_1(z),\qquad
 n^T\operatorname{diag}(\alpha,\beta)n
 =c(n\cdot y)^2+\int(n\cdot z)^2\,d\rho_1(z).
$$

Without the failure rows, $|\int n\cdot z\,d\rho_1|\le S$
and $|n\cdot y|\le1$ would give only $m\le2S$.
Here (IC.60) is positive definite. In particular $S>0$, and
$\int(n\cdot z)^2\,d\rho_1<S$: equality would put the
entire saturated measure on $\{n,-n\}$, forcing its positive
capacity-weighted covariance in (IC.60) to have rank at most one.
Cauchy–Schwarz for $\rho_1$ now gives
$|\int n\cdot z\,d\rho_1|<S$, hence also
$c(n\cdot y)^2<S$. Adding the two strict bounds proves
$m<2S$ and (IC.61) completes (IC.65). If $S=0$ the finite
original positive failure covariance already fails, rather than
giving an equality exception. Zero pure masses are outside the
exact-three-positive premise; coincident points are collected first.
No synthetic angular example is asserted to be an original attained
face. $\square$

## 15. Four pure coordinates and two available companions

**Theorem 15.1 (two-companion whole-group deletion on the original face).**
Retain Assumptions 1.1 and 1.4 and $t>T_3$. Suppose
$w^0\in\mathcal P(r)$ has nine positive coordinates $I$ in
nine distinct complete groups, $H_I$ invertible, and exactly four
pure and five saturated coordinates. Suppose two distinct occupied
pure coordinates $p_1,p_2$ have available zero-weight saturated
companions $j_1,j_2$ in their own compatible groups. Then another
finite law in $\mathcal P(r)$ uses at most eight complete groups,
with the same $B(t)$, $K=r$, $J_t$ and original absolute height.
The condition $C(1+1/m)<1$ also suffices, and the sufficient
original range of Corollary 14.3 supplies $t>T_3$.

Proof. Retain every column and set, for $z_1,z_2\ge0$,

$$
\begin{gathered}
w_{j_1}(z)=z_1,\qquad w_{j_2}(z)=z_2,\\
w_I(z)=w_I^0-H_I^{-1}(H_{j_1}z_1+H_{j_2}z_2),\qquad
w_i(z)=0\quad(i\notin I\cup\{j_1,j_2\}),\\
\mathcal D=\{z\in\mathbb R_{\ge0}^2:w_I(z)\ge0\}.
\end{gathered}
\tag{IC.66}
$$

Strict old positivity gives a small feasible quadrant. The set is
closed, and the mass row gives $z_1+z_2\le1$ on it, so it is
bounded. Every feasible point preserves $H w=(B,r)^T$; contact
equality preserves $J_t$. No pure coordinate is activated.
A nonselected old coordinate dying empties its group, since its
unused companions stay zero. A selected parent $p_i$ dying with
$z_i=0$ also empties its group. Any positive satellite belongs to
an original group, so either event leaves at most eight groups.

Follow each coordinate axis to its finite first exit. Existence and
strict positivity of the exit time follow from the mass row, exactly
as in (IC.63). Unless an exit already empties a group, on the first
axis the only dying coordinate is $p_1$, and on the second it is
$p_2$. Ties with any other old coordinate empty a group: on that
axis the other selected satellite is still zero. Thus it remains
only to consider these two exclusive exits.

Write the selected parent weights as

$$
w_{p_1}=u_1-c_{11}z_1-c_{12}z_2,\qquad
w_{p_2}=u_2-c_{21}z_1-c_{22}z_2,\qquad u_1,u_2>0,
\quad C_p=(c_{ij})_{i,j=1}^2.
\tag{IC.67}
$$

The exclusive axis exits imply, with $u_1,u_2$ retaining their
original intercept meanings from (IC.67),

$$
c_{11},c_{22}>0,\qquad
r_2:=u_2-c_{21}u_1/c_{11}>0,\qquad
r_1:=u_1-c_{12}u_2/c_{22}>0.
\tag{IC.68}
$$

These strict inequalities include zero or negative off-diagonal
coefficients; no sign is presumed for them.

If $\det C_p>0$, solve both parent equations:

$$
z^*=\frac1{\det C_p}
\begin{pmatrix}u_1c_{22}-c_{12}u_2\\c_{11}u_2-c_{21}u_1\end{pmatrix}
\in\mathbb R_{>0}^2.
\tag{IC.69}
$$

The numerators are $u_1c_{22}-c_{12}u_2=c_{22}r_1>0$ and
$c_{11}u_2-c_{21}u_1=c_{11}r_2>0$ by (IC.68).
Along $z=s z^*$,
$0\le s\le1$, the selected weights are exactly $(1-s)u_i$.
If any nonselected old coordinate first reaches zero at or before
$s=1$, that event empties its group, with all preceding weights
nonnegative. If none does, the endpoint is feasible and both selected
parents vanish, leaving only the two other pure coordinates. This
contradicts the uniform same-$B(t)$ rigidity of Theorem 14.2.
A simultaneous nonselected zero at $s=1$ is already the required
whole-group exit, whether or not both parents also vanish.

If $\det C_p\le0$, then
$c_{12}c_{21}\ge c_{11}c_{22}>0$. The off-diagonal entries
are nonzero and have the same sign. They cannot both be positive:
(IC.68) would imply
$c_{21}<u_2c_{11}/u_1$ and
$c_{12}<u_1c_{22}/u_2$, whose product contradicts that inequality.
Hence both are strictly negative. The direction

$$
d=(-c_{12},c_{11})^T\in\mathbb R_{>0}^2,\qquad
C_p d=(0,\det C_p)^T
\tag{IC.70}
$$

keeps $p_1$ constant and makes $p_2$ nondecreasing on $z=sd$.
This includes $\det C_p=0$, when both parents are constant.
Along this ray the old total mass is $1-s(d_1+d_2)$, while the
selected parents retain their positive initial masses. Thus at least
one nonselected old coordinate has negative derivative. Its finite
positive first-exit minimum gives a feasible endpoint with a dead
nonselected coordinate, hence a whole-group deletion. Zero
coefficients and determinant zero introduce no missing case.

In every case an entire original group disappears, and only satellites
of already occupied groups were activated. Every remaining paired
fraction is its saturated mass divided by its positive total mass,
so is legal. FC Theorem 3.3 merges the endpoint law without height
loss. The finite surviving coefficient masses are strictly positive
after zero coordinates and zero groups are omitted. $\square$

**Corollary 15.2 (the exact-four-pure critical restriction).**
Under Assumptions 1.1 and 1.4 with $t>T_3$, a canonical
FC6.1 representation at $r\notin U_8$ having exactly four pure
coordinates has at most one occupied pure coordinate belonging to
a compatible paired group.

Under the additional indefinite premise of Corollary 9.1 and its
budget range, the complete paired inventory has at most two directed
antipodal groups. The two allowed groups cannot both be occupied at
their pure coordinates in such an exact-four-pure critical support.

Proof. Two such occupied pure parents give the two available zero
companions in Theorem 15.1, since the canonical positive coordinates
are in distinct groups. Its deletion contradicts $r\notin U_8$
by FC Theorem 5.2. Corollary 9.1 supplies the separate common-kernel
cap on the indefinite branch. The restriction concerns pure-parent
occupancy: it places no analogous restriction on occupying two paired
groups only at saturated coordinates, and it supplies no deletion
for an exact-five-pure support. Losing two of five pure coordinates
would still leave three, so that proof's contradiction is absent.
Neither zero-paired nor one-paired exact-four supports are excluded.
$\square$

## 16. Whole-interval eight-group coverage on the supplied rank-one face

**Theorem 16.1 (mandatory pure-coordinate activation covers the rank-one face).**
Retain Assumptions 1.1 and 1.4, finite
$t\ge\max(t_0,30000)$, and the same symmetric original remainder
$R_-=Q+t\mathsf F$ of (IC.8). Suppose $R_-$ is nonzero rank-one
negative semidefinite. Then its supplied complete attained face has

$$
U_8=[r_-,r_+],\qquad n_t(r)\le8
\quad\text{for every }r\in[r_-,r_+].
\tag{IC.71}
$$

Here $n_t$ is FC Definition 2.3's minimum supported-nonzero low
actual count, under its original suppliers. No existence of a
rank-one attained face is assumed beyond the stated conditional
entry, or inferred from this conclusion. No pure-rank lower bound
is required in this theorem.

Proof. FC Proposition 34.2 gives $S<300/t\le1/100$ for every
same-$B(t)$ law. Every $w\in\mathcal P$ is height optimal at
its own achieved $K$ by FC Theorem 4.2. Apply FC Theorems 34.1
and 34.3 at precisely this scope. There is a unique directed
negative-height pure contact $x_*$ on $\ker R_-$. Its saturated
endpoint is also a contact with $\eta_1(x_*)\le0$, including zero,
and the two endpoints form a compatible complete group $G_*$.
Every $w\in\mathcal P$ has the quantitative pure-coordinate bound

$$
w_{*,0}\,\ell_-(x_*)>1/30000,\qquad
\ell_-(x_*)=\max\{-\ell(x_*),0\}>0.
\tag{IC.72}
$$

This is FC (FC.149): after merging, $w_{*,0}=p(1-\xi)$.
It applies to the pure coordinate, not merely to total mass of $G_*$.
Uniqueness uses the source positivity on $u\ge0$ and the two
directed points of the kernel line; it does not identify antipodes.

The endpoints of the attained contrast interval already belong to
$U_8$, as FC Theorem 6.1 explicitly states and proves. Indeed a
minimizing or maximizing vertex of $\mathcal P$ has independent
positive columns of $A$, since a nonzero kernel vector on positive
support gives opposite feasible perturbations. It therefore has at
most $\operatorname{rank}A\le8$ positive coordinates and at most
eight groups. This also handles a singleton interval and a
constant-$K$ face without any contrast division.

Suppose some other $r\in[r_-,r_+]$ were outside $U_8$.
FC Theorem 6.1 supplies a nonconstant edge strictly bracketing $r$
and its relative-interior law $w^0$ at $K=r$. Its support $I$
consists of exactly nine strictly positive columns in nine distinct
groups, with rank $A_I=8$ and invertible $H_I$. By (IC.72) its
pure column $p=(x_*,0)$ is in $I$. Its saturated companion
$j=(x_*,1)$ has zero weight, because two occupied coordinates
of $G_*$ would violate the distinct-group property. The companion
remains available in the complete inventory.

Activate it by (IC.63). The mass row again supplies a nonempty
negative old-coordinate set and a finite positive first exit
$\tau$. Throughout the segment all weights are nonnegative,
$H w=(B(t),r)^T$, and contact equality preserves $J_t$.
At the endpoint $w(\tau)\in\mathcal P$, (IC.72) still holds.
Thus the selected pure parent $p$ cannot die. At least one other
old coordinate dies. Its group differs from $G_*$, and every
unused coordinate of that group remains zero: $j$ is the only
activated coordinate. Consequently this death empties a whole group.
The surviving activated group $G_*$ has a positive pure parent
and legal fraction, and no new group was created. There are at most
eight occupied groups at the same $(B,r,J_t)$.

FC Theorems 3.3 and 5.2 now put $r$ in $U_8$, a contradiction.
This proves (IC.71) on the entire attained interval, with its
endpoints already covered. Other old pure coordinates are allowed
to die: each such death empties its own distinct original group.
Only the selected parent could leave a newly activated companion
behind, and that parent's pure mass is mandatory. A hypothesis
that only the total mass of $G_*$ is positive would not prevent
the parent from dying while its satellite survives; it is not a
substitute for (IC.72). $\square$

**Corollary 16.2 (conditional original minimum counts on this branch).**
Under Theorem 16.1's hypotheses and the inherited GC actual-count
suppliers, for each $r\in[r_-,r_+]$ there is a finite original
height-optimal weak instrument with at most eight supported-nonzero
low actual labels. Under GC (GC.10)'s equality of minima,

$$
n_{\rm tot}(s,t)=1+n_t(r)\le9,\qquad s=s_0r/\sqrt\alpha.
\tag{IC.73}
$$

Proof. Merge a law realizing (IC.71) within each compatible complete
group. GC Proposition 12.2 supplies exactly the common live Gram,
full failure covariance and pointwise capacity premises of GC
Proposition 10.1. That constructor supplies the finite original
instrument, with one low label per occupied group and its counted
coherent high completion. GC.10 then gives the stated bound on the
minimum total count. It is not a total-count identity for every
instrument, does not give an exact minimum of nine, and does not
supply seven-low compression. $\square$

## 17. Conditional correspondence and the remaining complete-group relation

**Definition 17.1 (bearing mathematical interfaces and attribution).**
Theorems 14.2, 15.1 and 16.1 use the original $B(t)$, complete
inventory, compatible fractions and within-label absolute height of
§1, with the nine-row preservation problem of §7. Their
source-specific content is, respectively, the full failure-covariance
pure bound consumed by exact-three activation, two-companion
whole-group deletion with uniform pure rigidity, and whole-interval
coverage from the mandatory pure kernel coordinate. The rational
source consequences use the actual nine rows of the pinned GC6.1
and the capacity expressions (IC.3). The positive-measure
Cauchy–Schwarz, Loewner bounds, rank inequalities, finite linear
pivots and two-by-two coefficient calculation are standard tools
inside these consumers, not separate new generic theorems.

FC Theorems 3.3 and 4.2 supply the complete groups, activity and
all-optima correspondence; FC Theorems 5.2 and 6.1 supply the exact
coordinate-face criterion, canonical critical ranks and contrast
endpoint coverage. GC Propositions 10.1 and 12.2 supply the full
same-law dictionary and finite constructor; GC Theorem 15.1 supplies
the compatible merge and the opposite-height HALF loss. FC32–34's
pure replacement and inertia results supply the mandatory pure mass
and unique compatible negative kernel group used by Theorem 16.1.
The exact-three argument and this mandatory-coordinate argument
have different premises: only the former needs uniform pure-rank
rigidity.

For the separate inventory interface, let PC denote
[*Finite-face positive-contact cap*, §§1–6](https://github.com/the-omega-institute/trureturing/blob/36adbdd8df3bc6615cae0f0f5fd1207239025477/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_FACE_POSITIVE_CONTACT_CAP.md).
Its own Assumptions 1.1 and 2.3 retain their stated suppliers,
including its GC/RTII revision
`c9635edd5272c1183f71a44e4d199f94a741c57d` and original supplier
revision `321589a8be98de4fe179f99f6e593d8784952db1`.
At finite $t\ge\max(t_0,800)$, PC Theorem 5.2 caps the complete
positive pure inventory by three; FC's negative pure test has at
most two distinct zeros and zero-height pure contacts are excluded.
Thus, when these PC premises are also retained, any canonical
nine-group support in this range has three, four or five pure
coordinates. Corollaries 14.4 and 15.2 give the corresponding new
restrictions in the first two cases. At the range of Theorem 16.1,
PC Corollary 6.2 also caps pure-containing groups by four on its
rank-one branch; the stronger whole-interval conclusion (IC.71)
uses mandatory pure-coordinate mass rather than that inventory cap.
A five-pure inventory in that range retains PC's indefinite-branch
restriction. None of these citations constructs such an inventory.

The literature interfaces in Definitions 6.1 and 13.1 retain their
credited scopes: di Dio–Schmüdgen's positive-measure support and
finite-dimensional moment results, de Boor's divided differences,
and the additional hypotheses required by Dette–Melas and
Nailwal–Zalar. No quadrature node is identified with an original
fractional actual label. The source-specific compositions here are
repo-derived conditional deductions. No worldwide priority or
literature-absence claim is attached to them.

**Definition 17.2 (unchanged original quantum correspondence).**
Every activation above changes coefficient masses within the same
complete inventory and the same $B(t)$; it preserves all eight
$\Gamma$ rows, the full live Gram, the complete physical failure
covariance including its cross entry, active $K=r$, $J_t$ and
$(H_0+J_t)/2$. The two available satellite columns are not replaced
by an independent failure allocation. Both coordinates and all legal
fractions of every paired group remain available. Unused contacts,
weak-zero height descriptions, opposite-height singleton groups,
report-chart endpoints and distinct directed antipodes retain the
conventions of §§1–7 and 13. A zero group is omitted before the
unknown input, with no division by its mass and no postselection.

Through GC Propositions 12.2 and 10.1 the resulting finite law has
the original complex forgotten-label live CP map and all five Borel
failure maps, with arbitrary passive-reference conditional operators.
This preserves the twelve stopped-cq errors with HALF and both
separate zero-target failure components. The labelled acquisition
instrument can change; equality of the forgotten-label maps does
not assert equality of its labelled probability measure. Its minimum
actual counts have exactly the interpretation used in Corollary 16.2.

All source, root, isolation, Jacobian, rank, TP, stopped-cq minimax,
sharp worst-history JOINT cost, separate unaveraged equality,
full-complex multi-Kraus rigidity, physical capacity and constructor
suppliers remain the distinct premises of §1. The original whole
future-accessible fibre counts specimen, memory, controller,
accessible environments and entangled shares jointly. Entire-fibre
activity, strictly positive finite-budget survivors, TP survivor
controls, absolute FIRST $6+a$ and absence of further
positive-carrier action after failure remain the inherited bounds.
No extra specimen, copy, helper, history oracle, reset, retry,
acceptance or survival division is introduced. Necessity retains
its original finite, convergent countable and stipulated measurable
scopes; the realizing instruments used here are finite.

**Open problem 17.3 (seven groups and the uncovered original domains).**
On the supplied rank-one branch in Theorem 16.1's range, (IC.71)
removes nine-low necessity but leaves the problem of removing a
further whole group: $U_7=[r_-,r_+]$ is not established. For the
indefinite branch, Corollaries 14.4 and 15.2 leave canonical
exact-three-pure supports with no paired pure parent,
exact-four-pure supports with at most one paired pure parent, and
the permitted exact-five-pure supports. A missing relation must
either delete a whole group while preserving all nine joint rows
and nonnegativity, possibly by a different law or additional unused
contacts, or evaluate complete coordinate-face coverage including
every alternative original table. Fixed-support rank, positive
initial pure Gram, one endpoint death, saturated-only paired
occupancy, or an unevaluated local stationary inventory does not
supply that relation. No original attained instance realizing any
remaining critical pattern is supplied here.

The rank-one theorem covers exactly one separately supplied finite,
entire-cylinder feasible, jointly attained positive-multiplier face
at $t\ge\max(t_0,30000)$. It supplies neither nonemptiness of
that branch nor all-budget/all-contrast dual attainment. The
exact-three and exact-four activation results require $t>T_3$
and their stated companion premises. At $t=T_3$ the pure bound
is only semidefinite and supplies no strict rank conclusion;
below it these activation proofs require another uniform invariant.
The smaller-budget rank-one domain, $\lambda=0$, absent or
nonfinite duals, unattained values and unsupplied boundary requests
retain the unresolved entries of §§7 and 13. Supplied interval
endpoints are included by Theorem 16.1; arbitrary boundary duals
are not thereby constructed. No universal $U_8$ outside the
stated rank-one domain, universal $U_7$, or all-alternative
higher-count obstruction follows.

The full programme still requires the all-budget evaluated roof,
branch ordering, complete selected and unused root inventories with
multiplicities and collisions, positive joint weights, coefficient
and orientation data, capacity/rank/count transitions,
endpoint/threshold/budget/degenerate gluing, next terms and uniform
joint limits of §§7 and 13. Source existence and its separate
minimax and physical-necessity suppliers are not discharged by
expression enclosures or contact pivots. Native source access,
calibration, jointly counted coherent storage and accessible
shares, whole-fibre actuation, duration, absolute clock alignment,
archive/source/epoch/controller permissions and the general
native-instrument/count correspondence remain unsupplied.

## 追加锚（本行以下为增补区）
