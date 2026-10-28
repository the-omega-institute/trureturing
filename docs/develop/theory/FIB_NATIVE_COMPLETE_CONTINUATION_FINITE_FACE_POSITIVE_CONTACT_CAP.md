# Positive pure contacts and coherent-transfer obstructions for the original finite continuation

## 1. One original source and the complete quantum problem

**Assumption 1.1 (original source and separate suppliers).** Let FC denote
[the finite-face alphabet criterion](FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_FACE_ALPHABET_CRITERION.md)
at revision `0512cd17cf4807864a7097fb3169847fcf3eef68`, GC denote
[the global actual-count source](FIB_NATIVE_COMPLETE_CONTINUATION_GLOBAL_ACTUAL_COUNTS.md),
and RTII denote [Arithmetic Holographic RT II](ARITHMETIC_HOLOGRAPHIC_RT_II.md).
GC and RTII are used at revision
`c9635edd5272c1183f71a44e4d199f94a741c57d`.
Retain GC Assumption 1.2 and FC Assumptions 1.1 and 23.1, with the
same consistent positive isolated source in all nine dyadic rows of
GC Definition 6.1. Their original supplier objects at
`321589a8be98de4fe179f99f6e593d8784952db1` retain their stated scopes.

In particular, CG §§13–17 supplies source existence, isolation,
Jacobian, ranks, root TP and the complete stopped-output minimax.
JR §§34–42 supplies sharp worst-history JOINT cost and the separate
unaveraged supported equality face of JR Theorem 42.1. The averaged
live equality from CG17 alone is insufficient. FA §§69–72 and
RC §§67 and 75 supply full-complex multi-Kraus actual-label rigidity,
physical capacity and the common constructor. FA §§78–79 supplies
the finite feasible domain. RC §68 supplies dual attainment only
under its own strict-interior hypotheses. FA §87 and Theorem 90.1
supply coherent completion and the nine-low existence bound; ST
Theorem 8.2 supplies its conditional seven-low/eight-total region.
The abbreviations and owning source paths are those in GC Assumption
1.2. Expression bounds on a source rectangle do not replace these
separate assumptions or assert TP away from that one root.

**Definition 1.2 (the original input and output).** In the five ordered
ambient modes $0,1,2,3,13$, let

$$
\begin{gathered}
E=\big((e_0+e_{13})/\sqrt2,\ (e_1+e_3)/\sqrt2,\ e_2\big),
\qquad P=EE^\dagger,\\
a_y=\left(\sqrt{y/128},\sqrt{(64-y)/128},1/\sqrt2\right)^T,
\qquad U_{\epsilon,\chi}=\operatorname{diag}(\epsilon,\chi,1),\\
\rho_{y,\epsilon,\chi}
=U_{\epsilon,\chi}a_ya_y^TU_{\epsilon,\chi}^\dagger,
\quad y\in\{5,16,27\},\quad \epsilon,\chi\in\{\pm1\}.
\end{gathered}
\tag{PC.1}
$$

There is one unknown specimen with state
$E\rho_{y,\epsilon,\chi}E^\dagger$, and no prior over the twelve
histories. The ideal live vector has squared qutrit coordinates

$$
\left(\frac y{128},\frac{y(58-y)}{128(y+6)},
                        \frac y{2(y+6)}\right),
\tag{PC.2}
$$

with the same signs and embedding as (PC.1). The five separate
failure-labelled Borel components have densities

$$
w_j\frac{6y}{(y+6a)^2}\,da\,P_f,\qquad
(w_0,w_1,w_2,w_3,w_{13})=(0,1/4,1/2,1/4,0),\quad 0\le a\le1.
\tag{PC.3}
$$

Both zero-target components remain separate. The error is the maximum
over all twelve histories of HALF the trace norm of the complete
stopped-cq output difference, as in GC Definitions 2.1–2.2. It includes
live complex coherences, passive-reference conditional operators,
singular-time, abort, wrong-support and zero-target sectors.

Competitors remain common full complex CP acquisition instruments with
all hidden Kraus multiplicities, admitted failure-time laws and
full-output TP conditional decoders. The original minimax error,
contrast request, sharp JOINT cost and activity constraints are (GC.5).
The jointly future-accessible input-dependent fibre counts specimen,
memory, controller, accessible environments and entangled shares
together. Activity is the integral of the operator norm on each
entire counted fibre, maximized over actually generated labels.
Finite-budget survivors are strictly positive, survivor controls are
TP, FIRST is the absolute time $6+a$, and no positive-carrier action
follows failure. Later blank ancillas are independent; an entangled
accessible share is not blank.

Necessity has the original finite and convergent countable scopes and
only the measurable finite-dimensional-fibre/Kraus/integrable-effect
extension of GC Convention 2.3. Finite realizations use the existing
GC Proposition 10.1 constructor with its counted coherent high fibre.
No helper specimen, copy, history oracle, reset, retry, postselection,
acceptance or survival division, quantum bypass or uncounted accessible
share is allowed.

## 2. The same source, common law and complete attained face

**Definition 2.1 (source quantities).** Use the positive amplitudes
$h_0,h_1,h_2,a_s,b_s,c_s,d_s,m_1,m_2$ of Assumption 1.1 and set

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=a_se_0e_1^T+b_se_1e_0^T,\quad
S=c_se_0e_2^T+d_se_2e_0^T,\quad M=\operatorname{diag}(0,m_1,m_2),\\
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\\
\theta=\frac{a_sb_s}{h_0h_1},\quad
\omega=\frac{c_sd_s}{h_0h_2},\quad
\delta=\theta+\omega\in(0,1),\quad s_0=\sqrt\delta,\\
\alpha=\theta/\delta,\quad \beta=\omega/\delta,
\quad \alpha+\beta=1,\\
\Delta=\rho_{27,+,+}-\rho_{5,+,+},\quad
(K_0,K_1,K_2)=(D,T,S),\quad
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\\
L=\operatorname{diag}(s_0,1,1),\quad G=LNL,\qquad
H_0=(1-\delta)N_{00}>0.
\end{gathered}
\tag{PC.4}
$$

The vectors in the source matrices are qutrit coordinate vectors.
For $u^2+v^2=1$, retain the directed point $(u,v)$ and put

$$
\begin{gathered}
h=(1,u/\sqrt\alpha,v/\sqrt\beta)^T,\qquad
K_h=s_0D+(u/\sqrt\alpha)T+(v/\sqrt\beta)S,\\
n_h=(0,d_sv/(h_2\sqrt\beta),-b_su/(h_1\sqrt\alpha))^T,\\
\ell=h^TGh,\qquad f=n_h^T\Delta n_h,\\
\mathfrak c(u,v)=
\frac{h_1^2h_2^2\delta+(a_s^2h_2^2/\alpha)u^2
                          +(c_s^2h_1^2/\beta)v^2}
     {h_0^2\delta+(b_s^2/\alpha)u^2+(d_s^2/\beta)v^2}>0,\\
V=\frac{m_2h_1^2}{b_s^2},\quad W=\frac{m_1h_2^2}{d_s^2},
\quad \mu=\alpha V+\beta W,\quad
u_F=V/\mu,\quad v_F=W/\mu,\\
\mathfrak c_f=\mathfrak c(\sqrt{\alpha u_F},\sqrt{\beta v_F}),
\qquad t_0=W/\mathfrak c_f.
\end{gathered}
\tag{PC.5}
$$

This is the source dictionary (FC.1)–(FC.3), (FC.55)–(FC.58).
In particular the source amplitude $c_s$ differs from capacity
$\mathfrak c$, and the matrix $K_h$ differs from scalar contrast.

**Definition 2.2 (complete common data).** For finite $t=e^A-1\ge t_0$
define

$$
\begin{gathered}
X=\{(u,v,\xi):u^2+v^2=1,\ 0\le\xi\le1\},\qquad
b_x=t\xi\mathfrak c(u,v),\\
\Gamma(x)=(1,u,v,u^2,uv,\xi\mathfrak c,
                    \xi\mathfrak c u^2,\xi\mathfrak c uv)^T,\\
B(t)=(1,0,0,\alpha,0,\mu/t,\alpha V/t,0)^T,\qquad k(x)=|u|,\\
K(\pi)=\int_X k\,d\pi,\qquad
J_t(\pi)=\int_X|\ell+b_xf|\,d\pi,\qquad
\int_X\Gamma\,d\pi=B(t).
\end{gathered}
\tag{PC.6}
$$

Antipodes are distinct. The measure $\pi$ is the common coefficient
probability law. Its positive atom masses are not acquisition
probabilities. The original request is $K\ge r$, with
$s=s_0r/\sqrt\alpha$ and the feasible interval of GC Definition 12.1.
Write

$$
\begin{aligned}
R_t(r)&=\max\{J_t(\pi):\int\Gamma\,d\pi=B(t),\ K(\pi)\ge r\},\\
C_t(\lambda)&=\max\{J_t(\pi)+\lambda K(\pi):
                                      \int\Gamma\,d\pi=B(t)\}.
\end{aligned}
\tag{PC.7}
$$

GC Proposition 12.2 identifies these complete moments with the live
Gram $\int hh^T d\pi=I_3$ and failure covariance
$\int b_xn_hn_h^T d\pi=M$. The actual supported acquisition effect
of a label is $pK_h^\dagger K_h+pb_xn_hn_h^T$. Its absolute signed
height is taken after combining its live and failure contributions.
The original actual height and optimum are
$(H_0+J_t)/2$ and $(H_0+R_t(r))/2$.

**Assumption 2.3 (finite positive-multiplier joint attainment).**
In addition to Assumption 1.1, fix a finite $t\ge t_0$, $\lambda>0$,
a finite $y\in\mathbb R^8$ and a common law $\pi$ such that

$$
\begin{gathered}
d(x)=y\cdot\Gamma(x)-|\ell+b_xf|-\lambda|u|\ge0
\quad\text{for every }x\in X,\\
\int\Gamma\,d\pi=B(t),\qquad
J_t(\pi)+\lambda K(\pi)=y\cdot B(t).
\end{gathered}
\tag{PC.8}
$$

Thus $y\cdot B=C_t(\lambda)$ by weak duality. The inequality is on
the entire cylinder. It is not a sampled inequality or a condition
only at occupied points. This assumption supplies attainment also
when a boundary point is under consideration; it contains no
existence theorem for finite duals at all boundaries.

**Definition 2.4 (complete contacts and compatible groups).** Set
$\eta_j=\ell+jt\mathfrak c f$, $j\in\{0,1\}$, and let
$Z=\{(u,v,j):d(u,v,j)=0\}$ include every endpoint contact, occupied
or unused. Coincident signed descriptions of one sheet point are
deduplicated. A pure endpoint and saturated endpoint at the same
directed angle form one paired group exactly when both contact and
$\eta_0\eta_1\ge0$. Every other endpoint is a singleton.
Let $\mathscr G$ be this complete partition. For a selected family
$Q\subseteq\mathscr G$, let $I_Q$ contain every endpoint column of
every selected group, including both columns of a pair.

The eight signed tests are the original (FC.7). Explicitly, let $D_c$
and $N_c$ be the positive denominator and numerator in (PC.5), and put

$$
\begin{gathered}
P_y=y_0+y_1u+y_2v+y_3u^2+y_4uv,\qquad
Q_y=y_5+y_6u^2+y_7uv,\\
F_{0,\epsilon,\sigma}=P_y-\epsilon\lambda u-\sigma\ell,\\
F_{1,\epsilon,\sigma}
=D_cF_{0,\epsilon,\sigma}+N_c(Q_y-\sigma t f),
\qquad \epsilon,\sigma\in\{\pm1\}.
\end{gathered}
$$

All eight are nonnegative on the whole circle by (PC.8); their zeros,
on their respective sheets and with coincident descriptions
deduplicated, give $Z$. The omitted affine half-angle point $(-1,0)$,
report axes, weak height signs and repeated zeros retain their
full-circle meanings.

FC Theorems 3.3 and 4.2 give the following exact interfaces. A strict
fractional contact has both endpoints in its group, with weakly
same-sign heights. For endpoint masses $a_0,a_1\ge0$ in a pair,
merging gives $p=a_0+a_1$ and $\xi=a_1/p$ when $p>0$, preserving
all eight moments, $K$ and $J_t$. Zero total mass is omitted.
The triangle identity behind this fact is

$$
\begin{aligned}
d(u,v,\xi)&=(1-\xi)d(u,v,0)+\xi d(u,v,1)\\
&\quad +(1-\xi)|\eta_0|+\xi|\eta_1|
                   -|(1-\xi)\eta_0+\xi\eta_1|.
\end{aligned}
\tag{PC.9}
$$

Every term is nonnegative. Strictly opposite heights therefore
remain separate singletons when both endpoints occur.
For every request $r$ in the complete attained interval $[r_-,r_+]$,
every original optimum has $K=r$ and zero integrated gap. Its endpoint
representation uses the complete inventory above. This activity
conclusion follows from $\lambda>0$ and the original inequality
$K\ge r$; it does not impose equality on arbitrary feasible laws.

## 3. A quantitative lower-left positive-height restriction

**Definition 3.1 (reused source bounds).** Write the source height as

$$
\begin{gathered}
\ell(u,v)=A_\ell u^2-2a_\ell uv+B_\ell v^2+l_u u+l_vv,\qquad
\gamma_\ell=B_\ell-A_\ell,\\
A_\ell=\delta N_{00}+N_{11}/\alpha,\quad
B_\ell=\delta N_{00}+N_{22}/\beta,\quad
a_\ell=-N_{12}/\sqrt{\alpha\beta},\\
l_u=2\sqrt{\delta/\alpha}N_{01},\qquad
l_v=2\sqrt{\delta/\beta}N_{02}.
\end{gathered}
\tag{PC.10}
$$

FC Proposition 18.1, Proposition 24.1 and (FC.139), together with
FC Proposition 34.2, give the strict same-source bounds

$$
\begin{gathered}
\alpha>219/250,\qquad \mu<12,\qquad
\mathfrak c(u,v)>1/25\quad((u,v)\in S^1),\\
A_\ell<463/100000,\quad 0<\gamma_\ell<529/50000,\quad
a_\ell>0,\quad l_u>63/12500,\quad l_v>1251/100000.
\end{gathered}
\tag{PC.11}
$$

The corresponding decimal bounds are $0.00463$, $0.01058$,
$0.00504$ and $0.01251$, each an exact terminating rational.
These are expression enclosures inherited at the one root, rather
than new root-existence or TP hypotheses on a rectangular family.

**Lemma 3.2 (positive lower-left height forces a small horizontal coordinate).**
Under Assumption 1.1, if $a_r,b_r>0$, $a_r^2+b_r^2=1$ and
$\ell(-a_r,-b_r)>0$, then

$$
b_r>9/10,\qquad a_r<\sqrt{19}/10<11/25.
\tag{PC.12}
$$

Proof. On $0\le w<1$ use the actual lower-left directed height

$$
\phi(w)=\ell(-\sqrt{1-w^2},-w)
=A_\ell+\gamma_\ell w^2
 -(2a_\ell w+l_u)\sqrt{1-w^2}-l_vw.
\tag{PC.13}
$$

Its second derivative, also (FC.67), is

$$
\phi''(w)=2\gamma_\ell+
\frac{l_u+2a_\ell w(3-2w^2)}{(1-w^2)^{3/2}}>0.
\tag{PC.14}
$$

In particular $\phi$ is convex on $[0,9/10]$. The endpoint bounds are

$$
\begin{aligned}
\phi(0)&<0.00463-0.00504=-41/100000<0,\\
\phi(9/10)&<0.00463+0.01058\frac{81}{100}
                 -0.00504\frac{43}{100}-0.01251\frac9{10}\\
&=-283/1250000<0.
\end{aligned}
\tag{PC.15}
$$

For the second line, $\sqrt{19/100}>43/100$ by squaring positive
rationals; the term $-2a_\ell w\sqrt{1-w^2}$ is negative.
The convex chord between these two negative endpoint bounds is
negative throughout the interval. Thus $\phi(b_r)>0$ requires
$b_r>9/10$. The circle identity gives $a_r^2<19/100$, and
$19/100<(11/25)^2$ proves the last inequality. $\square$

## 4. One full-law separator retaining all saturated groups

**Theorem 4.1 (uniform exclusion for capped pure endpoints).** Under
Assumption 1.1, let finite $t\ge\max(t_0,800)$. Consider any collection
of pure and saturated endpoint columns of (PC.6) whose every pure
column has $u\le11/25$, with no directional or height-sign restriction
on saturated columns. In the original nine coordinates $(\Gamma,k)$,
put

$$
\zeta=(11/25,-14/25,0,-1,0,28,0,0,0).
\tag{PC.16}
$$

Every retained column has nonnegative pairing with $\zeta$, whereas,
for every real $r$,

$$
\zeta\cdot(B(t),r)=11/25-\alpha+28\mu/t<-2/125.
\tag{PC.17}
$$

Consequently these columns have no nonnegative representation of the
complete target $(B(t),r)$, or even of $B(t)$ alone. Under Assumption
2.3 the conclusion applies to any family $Q$ with the stated pure
cap. It retains negative pure endpoints, every reverse saturated
singleton, all other saturated endpoints and both coordinates of each
selected pair. It also excludes all their legal fractional mixtures.

Proof. Set $a_c=11/25$ and

$$
q(u)=(u+1)(a_c-u)=11/25-(14/25)u-u^2.
\tag{PC.18}
$$

This is nonnegative for $-1\le u\le a_c$. On the entire circle,

$$
q(u)+28/25=(1-u)(u+39/25)\ge0.
\tag{PC.19}
$$

For a pure endpoint, (PC.16) pairs to $q(u)\ge0$ by the cap. At
any saturated endpoint it pairs to

$$
q(u)+28\mathfrak c(u,v)>-28/25+28/25=0.
\tag{PC.20}
$$

This uses only the uniform capacity lower bound, with neither a report
sign nor a saturated-height restriction. In particular a saturated
reverse endpoint is retained even if its own pure endpoint is absent.
If it belongs to a selected pair, its pure endpoint is also retained
and must satisfy the same pure cap. Both endpoint inequalities then
hold independently. Affinity gives, for every fraction in that pair,

$$
\zeta\cdot(\Gamma(u,v,\xi),k(u,v,\xi))
=(1-\xi)q(u)+\xi\big(q(u)+28\mathfrak c(u,v)\big)\ge0.
\tag{PC.21}
$$

No fixed fraction is selected and no column is discarded. The same
calculation applies to a measure on such segments.

At the single common target all nine coefficients give

$$
\begin{aligned}
\zeta\cdot(B(t),r)
&=\frac{11}{25}-\alpha+\frac{28\mu}{t}\\
&<\frac{11}{25}-\frac{219}{250}
                         +\frac{28\cdot12}{800}
=-\frac2{125}.
\end{aligned}
\tag{PC.22}
$$

The strict source inequalities make the bound strict also at $t=800$.
A nonnegative representation would pair to a nonnegative sum, contrary
to (PC.22). The coefficient conjugate to $K$ is exactly zero. Thus
the exclusion holds at every $K$ request and for $K\ge r$ as well;
it does not optimize a separate marginal or replace the original
contrast inequality. For a family $Q$, this is a concrete instance of
FC Theorem 7.3 using all columns in $I_Q$. $\square$

## 5. At most three positive-height pure contacts

**Definition 5.1 (complete positive branches).** Under Assumption 2.3
write

$$
\begin{gathered}
P_y=y_0+y_1u+y_2v+y_3u^2+y_4uv,\\
F_{0,\epsilon,\sigma}=P_y-\epsilon\lambda u-\sigma\ell,
\qquad \epsilon,\sigma\in\{\pm1\},\\
N_R=\#\{(u,v)\in S^1:F_{0,+,+}=0\},\qquad
N_L=\#\{(u,v)\in S^1:F_{0,-,+}=0\}.
\end{gathered}
\tag{PC.23}
$$

These are the original full-circle pure tests (FC.7). They are
nonnegative, nonzero and of trigonometric degree at most two.
FC Theorem 12.1 confines their zeros to their strict report
hemispheres and bounds each inventory by two. FC Proposition 20.1
excludes zero-height pure contacts, and FC Theorem 11.1 gives
$\ell>0$ on $u\ge0$. It follows that $N_R+N_L$ counts precisely
all positive-height pure contacts, including unused contacts; the
negative-height pure contacts have $u<0$ and belong to
$F_{0,-,-}$, which has at most two zeros.

**Theorem 5.2 (positive pure-contact cap).** Under Assumptions 1.1 and
2.3, if finite $t\ge\max(t_0,800)$, then

$$
N_R+N_L\le3.
\tag{PC.24}
$$

This is a bound on the complete inventory of each supplied jointly
attained finite positive-multiplier dual, rather than only on its
occupied pure atoms. It makes no assumption about the number or signs
of its saturated contacts.

Proof. Since $N_R,N_L\le2$, the only case to exclude is
$N_R=N_L=2$. Reuse FC Theorem 12.1's maximal-zero square reduction:
a nonnegative nonzero degree-two trigonometric polynomial with two
distinct directed zeros has the real-square form

$$
F_{0,\epsilon,+}=(v_\epsilon\cdot x+C_\epsilon)^2,
\qquad x=(u,v)^T.
\tag{PC.25}
$$

The two zeros are in one open $u$ hemisphere. Consequently
$v_\epsilon\ne0$, $C_\epsilon\ne0$, and
$0<|C_\epsilon|<\|v_\epsilon\|$. A zero constant would give
antipodal zeros, equality of magnitudes at most one zero, and a larger
constant no zero.

The even part of the two tests is the same function on the circle,
namely the even part of $P_y-\ell$. Its homogeneous quadratic
matrix is therefore, for either sign,

$$
H=v_\epsilon v_\epsilon^T+C_\epsilon^2I_2.
\tag{PC.26}
$$

Equality as quadratic functions on the unit circle implies equality
of the symmetric matrices by homogeneity and polarization. The
eigenvalues of $H$ are $C_\epsilon^2$ and
$C_\epsilon^2+\|v_\epsilon\|^2$, which are distinct. They determine
the same constant magnitude, vector magnitude and top eigenline for
both signs. Hence their nonzero odd vectors
$2C_\epsilon v_\epsilon$ are either equal or opposite. Their
difference, with the plus report first, is $-2\lambda(1,0)^T$.
Because $\lambda>0$, they are opposite and parallel to the $u$ axis.
The signed difference fixes their orientation. For some $A_d,B_d>0$,

$$
\begin{gathered}
F_{0,+,+}=(A_du-B_d)^2,\qquad
F_{0,-,+}=(A_du+B_d)^2,\\
\lambda=2A_dB_d,\qquad a_r=B_d/A_d\in(0,1),\qquad
b_r=\sqrt{1-a_r^2}>0.
\end{gathered}
\tag{PC.27}
$$

Their complete zeros are the four distinct rectangle points
$(a_r,\pm b_r)$ and $(-a_r,\pm b_r)$. At a zero of either
positive-height test, entire-circle feasibility of the opposite
height test forces $\ell\ge0$; FC Proposition 20.1 excludes equality.
In particular $\ell(-a_r,-b_r)>0$. Lemma 3.2 gives $a_r<11/25$.

Every right pure contact is positive-height and therefore a zero of
$F_{0,+,+}$, so its $u$ coordinate equals $a_r$. The left positive
contacts are exactly the other two displayed points. Every other pure
contact is negative-height with $u<0$. Thus every pure column of the
complete inventory satisfies $u\le11/25$.

Apply Theorem 4.1 to the entire group family $Q=\mathscr G$.
All saturated coordinates are retained, without restricting their
directions, their heights, their reverse status or their pairing.
Both coordinates of every compatible pair are retained. Yet no
nonnegative representation of $B(t)$ by these columns exists.

On the other hand the jointly attaining law in (PC.8) has zero
integrated nonnegative gap. FC Theorems 3.3 and 4.2 split and collect
it into exactly such a nonnegative complete-endpoint representation
of $B(t)$, preserving its $K$ and $J_t$. This holds also for the
admitted integral laws because the complete group inventory is finite.
The contradiction excludes $N_R=N_L=2$ and proves (PC.24).
$\square$

**Corollary 5.3 (the remaining five-pure pattern).** Under Theorem 5.2's
hypotheses, a complete inventory with five pure contacts has exactly
three positive-height and two negative-height pure contacts. Its
positive branch counts are $(N_R,N_L)=(2,1)$ or $(1,2)$.

Proof. There are no zero-height pure contacts. The negative test has
at most two zeros, while Theorem 5.2 bounds the two positive tests
together by three. Equality in a total of five forces both bounds.
The per-test bound two gives the two possible ordered patterns.
$\square$

## 6. The conditional rank-one consequence and the saturated gap

**Definition 6.1 (the original failure remainder).** In FC's notation
let

$$
\begin{gathered}
Q=\begin{pmatrix}y_5+y_6&y_7/2\\y_7/2&y_5\end{pmatrix},\qquad
\mathsf F=\begin{pmatrix}0&e\\e&-d_*\end{pmatrix},\\
e=-\frac{b_sd_s\Delta_{12}}{h_1h_2\sqrt{\alpha\beta}}>0,
\qquad d_*=\frac{11d_s^2}{64\beta h_2^2}>0,
\qquad R_-=Q+t\mathsf F.
\end{gathered}
\tag{PC.28}
$$

The saturated endpoint coefficient mass is
$S_{\rm sat}=\int\xi\,d\pi$. FC Proposition 34.2 gives
$S_{\rm sat}<300/t$, using the same $\mu<12$ and
$\mathfrak c>1/25$. This is coefficient mass, not failure probability.

**Corollary 6.2 (at most four pure-containing groups on the rank-one branch).**
Under Assumptions 1.1 and 2.3, suppose
$t\ge\max(t_0,30000)$ and $R_-$ is nonzero rank-one negative
semidefinite. Then the complete inventory has at most four groups
containing a pure endpoint. Its unique negative-height pure contact is
the mandatory compatible kernel group of FC Theorem 34.3.
A five-pure inventory in this budget range requires the indefinite
branch of that theorem.

Proof. The small-mass condition holds for every common representation,
since $S_{\rm sat}<300/t\le1/100$. Reuse FC Theorems 34.1 and 34.3
at this scope. They supply strictly positive negative-pure-coordinate
mass and the dichotomy: $R_-$ is indefinite or nonzero rank-one
negative semidefinite. On the stated rank-one branch, every negative
pure contact lies on its kernel. The negative height requires $u<0$,
so only one of the two directed points on that kernel line qualifies.
Its saturated endpoint is also a contact with $\eta_1\le0$; the
two belong to one compatible group $G_*$. Every representation has
positive pure-coordinate mass there, satisfying the inherited bound

$$
p(1-\xi)\ell_-(x_*)>1/30000,
\qquad \ell_-=\max(-\ell,0).
\tag{PC.29}
$$

Theorem 5.2 gives at most three other, positive-height pure contacts.
Each pure contact belongs to exactly one group, so there are at most
four pure-containing groups. Corollary 5.3 would require two negative
pure contacts for a five-pure inventory; hence that inventory is on
the indefinite branch. $\square$

**Open problem 6.3 (joint families retaining both mandatory types).**
The bound four in Corollary 6.2 supplies no bound three on saturated
singleton groups. In particular it does not imply a seven-group
complete face or seven-low compression. The unresolved families
include indefinite faces retaining reverse saturated singletons and
sufficient negative pure-coordinate mass, and rank-one negative
semidefinite faces retaining $G_*$ and their other saturated groups.
At $t\ge800$ the positive patterns $(2,1)$ and $(1,2)$ remain possible
under the stated restrictions; no existence assertion for either
pattern follows from failure to exclude it. Theorem 4.1 excludes a
family only when all of its pure columns satisfy its cap.

## 7. The coherent RT81 interface

**Definition 7.1 (logical target, records and error).** RTII §66.1 uses
the maximally correlated encodings

$$
\mathcal J_{\rm in}(|x\rangle\langle y|)=|xx\rangle\langle yy|,
\qquad
\mathcal J_{\rm out}(|f\rangle\langle g|)=|ff\rangle\langle gg|.
\tag{PC.30}
$$

RTII §81 concerns arbitrary local CPTP maps
$\mathcal A,\mathcal B:M_{2k}\to M_k$, $k\ge2$, and target

$$
\begin{aligned}
\mathcal F_{k,2}(|f,i\rangle\langle f,j|)
 &=\delta_{ij}|f\rangle\langle f|,\\
\mathcal F_{k,2}(|f,i\rangle\langle g,j|)
 &=\tfrac12|f\rangle\langle g|\quad(f\ne g).
\end{aligned}
\tag{PC.31}
$$

If $V_A,V_B$ are their Stinespring isometries, the correct-output
blocks are contractions

$$
A_fe_i=(\langle f|\otimes I)V_A|f,i\rangle,\qquad
H_fe_i=(\langle f|\otimes I)V_B|f,i\rangle.
\tag{PC.32}
$$

For columns $a_{fi},h_{fi}$ let
$x_{fi}=a_{fi}\otimes h_{fi}$ and let
$K_{(fi),(gj)}=\langle x_{fi},x_{gj}\rangle$ be the forward Gram.
The fixed target Gram $T_k$ has diagonal blocks $I_2$ and
off-diagonal blocks $J_2/2$, where $J_m$ denotes the $m$ by $m$
all-ones matrix. The within-fibre plus/minus transform, with all plus
coordinates ordered before all minus coordinates, gives
$\widehat T_k=\operatorname{diag}(J_k,I_k)$. The transformed $K$
includes its full plus/minus cross block.

The RT81 error is the unhalved arbitrary-reference norm

$$
\delta_{\rm RT}=
\| (\mathcal A\otimes\mathcal B)\mathcal J_{\rm in}
             -\mathcal J_{\rm out}\mathcal F_{k,2}\|_\diamond.
\tag{PC.33}
$$

Its resource $d$ is local Kraus rank, equivalently the least pure
Stinespring environment dimension for the specified local channel;
the purification of any mixed ancilla is included. RTII §81 proves
$\operatorname{Tr}(T_k-K)_+\ge\max(0,k-d^2+1)$ and the corresponding
$\delta_{\rm RT}\ge\max(0,(k-d^2+1)/k)$, using the normalized input

$$
|\Omega_{2k}\rangle
=\frac1{\sqrt{2k}}\sum_{f=1}^k\sum_{i=0}^1
           |f,i\rangle_R\otimes|f,i\rangle_{\rm logical}.
\tag{PC.34}
$$

These are a different input, target, error and resource interface from
(PC.1)–(PC.8). The following exact constructions concern the data
required to identify the interfaces.

## 8. Identical classical branches with two exact coherent witnesses

**Theorem 8.1 (phase-sensitive Gram with globally admissible products).**
For $k=4$, there are two families of correct-output blocks satisfying
(PC.32), each extending to one pair of global RT81 local CPTP maps,
such that the classical qubit instrument

$$
\mathcal I_f(X)=X/4,\qquad f=1,2,3,4,
\tag{PC.35}
$$

is identical for both families, but their fixed-target positive-part
traces are respectively $6$ and $7$.

Proof. Choose $\varepsilon\in\{\pm1\}^4$ and set

$$
A_f=\varepsilon_f I_2/2,\qquad H_f=I_2.
\tag{PC.36}
$$

Each block is a contraction and
$A_fXA_f^\dagger=X/4$. Moreover
$\sum_f A_f^\dagger A_f=I_2$, so (PC.35) is an actual CP
instrument on a single qubit with four readable labels. It is a
comparison instrument for this transfer question, not a new original
GC law. Identifying its four qubit domains with the four logical
fibres specifies the displayed correct-output blocks.

These blocks satisfy the global compatibility required by RT81,
not only its independent-contraction relaxation. Let

$$
\begin{gathered}
D_\varepsilon=\operatorname{diag}(\varepsilon_1,\ldots,\varepsilon_4),
\quad U_\varepsilon=D_\varepsilon(I_4-J_4/2),\\
V_A=U_\varepsilon\otimes I_2:
\mathbb C^8\longrightarrow\mathbb C^4\otimes\mathbb C^2,
\qquad V_B=I_8:
\mathbb C^8\longrightarrow\mathbb C^4\otimes\mathbb C^2.
\end{gathered}
\tag{PC.37}
$$

The identifications send $|f,i\rangle$ to $|f\rangle\otimes|i\rangle$.
Since $J_4^2=4J_4$, $(I_4-J_4/2)^2=I_4$, and both $V_A,V_B$
are global isometries. Taking their environment partial traces
therefore gives local CPTP maps of the precise RT81 dimensions,
with pure environments of dimension two. Their correct-output
blocks are

$$
\begin{aligned}
(\langle f|\otimes I_2)V_A|f,i\rangle
 &=(U_\varepsilon)_{ff}|i\rangle
   =\varepsilon_f|i\rangle/2,\\
(\langle f|\otimes I_2)V_B|f,i\rangle&=|i\rangle.
\end{aligned}
\tag{PC.38}
$$

Thus they realize exactly (PC.36), including any output leakage
outside the correct output. Their product records and full Gram are

$$
x_{fi}=\frac{\varepsilon_f}{2}|i\rangle\otimes|i\rangle,
\qquad
K_\varepsilon=E_\varepsilon\otimes I_2,\qquad
E_\varepsilon=\varepsilon\varepsilon^T/4.
\tag{PC.39}
$$

Here $E_\varepsilon$ is a rank-one orthogonal projection. Applying
the full plus/minus transform gives

$$
\widehat K_\varepsilon=\operatorname{diag}(E_\varepsilon,E_\varepsilon),
\qquad
\widehat T_4=\operatorname{diag}(J_4,I_4).
\tag{PC.40}
$$

The cross block vanishes by the explicit records; it has not been
discarded as an approximation.
For $\varepsilon=(1,1,1,1)$, $E_\varepsilon=J_4/4$ projects onto
the all-ones line. The two blocks of $\widehat T_4-\widehat K$
have spectra $(3,0,0,0)$ and $(1,1,1,0)$. Thus

$$
\operatorname{spec}(T_4-K)=(3,0,0,0,1,1,1,0),\qquad
\operatorname{Tr}(T_4-K)_+=6.
\tag{PC.41}
$$

For $\varepsilon=(1,1,-1,-1)$, the projection line is orthogonal
to the all-ones line. Now the spectra are $(4,-1,0,0)$ and
$(1,1,1,0)$, so

$$
\operatorname{spec}(T_4-K)=(4,-1,0,0,1,1,1,0),\qquad
\operatorname{Tr}(T_4-K)_+=7.
\tag{PC.42}
$$

Both Grams have trace two; the missing correct-output trace is
retained, as in RTII §81.3–81.4. Both examples satisfy the RT81
lower bound. The global channels in (PC.37) change with
$\varepsilon$, while all four classical CP branches in (PC.35)
remain identical. This proves the assertion. $\square$

**Corollary 8.2 (classical CP data do not determine this coherent witness).**
The fixed-$T_4$ functional $\operatorname{Tr}(T_4-K)_+$ in Theorem 8.1
is not a function of the classical acquisition instrument (PC.35)
and its readable labels alone. In the original GC class, independent
phases on all Kraus operators within a fixed classical acquisition
branch likewise preserve its full CP map and physical outputs.

Proof. To identify what the classical data in (PC.35) retain, first
use Watrous, Chapter 2, instrument equations (2.258)–(2.262) and the
Choi/Kraus interfaces of Theorem 2.22 and Corollary 2.27. Summing
the branches in (PC.35) gives the qubit identity channel. It has the
single Kraus operator $I_2$, and its nonzero Choi matrix is
$|\operatorname{vec}I_2\rangle\langle\operatorname{vec}I_2|$, of rank
one. More generally, for any integer $m\ge1$ choose positive
$p_1,\ldots,p_m$ with sum one and define
$\mathcal I_j(X)=p_jX$. These are $m$ nonzero readable branches,
while their sum is still the identity channel. They require no
additional input specimen. Proportional subdivision changes this
readable count without changing the forgotten channel.

Even after fixing the four-label subdivision (PC.35), Theorem 8.1
gives the two values (PC.41) and (PC.42) for that same instrument.
More generally replacing every Kraus operator $C_{fj}$
of a classical branch by $e^{i\vartheta_f}C_{fj}$ cancels the phase
in each $C_{fj}XC_{fj}^\dagger$. It preserves that CP branch,
its effect, all passive-reference conditional outputs and every
subsequent conditional CP operation. In the GC dictionary it therefore
preserves $\Gamma$, $K$, $J_t$ and all physical outputs. Cross-label
coherent record inner products need not be invariant under the same
independent phases, as the example computes.

RT81's $d$ refers to a specified local channel's pure environment
resource. It is neither the number of readable outcomes in (PC.35)
nor the count of original GC optimal labels. The subdivision above
concerns an arbitrary classical instrument; it is not a theorem about
the minimum count among GC height optimizers. Conversely an
environment may be discarded and unreadable. A valid count transfer
must relate the actual jointly accessible original resource to the
particular channel environment used by RT81. $\square$

The phase variation in Theorem 8.1 changes coherent RT81 channels;
it is not two Stinespring descriptions of one fixed coherent channel.
RT81 obtains its relative logical phases from coherent inputs such as
(PC.34). Those phases are additional data to a classical instrument.
The example is an obstruction to deriving that fixed-target witness
from classical branches alone, not an RT81 counterexample or an
original-source actual-count necessity seed.

## 9. Supported Schmidt resources

**Definition 9.1 (the source-preserving local preparation class).**
Let $R$ be a passive reference and let a positive normalized joint
input $X$ satisfy

$$
X=(P\otimes I_R)X(P\otimes I_R),\qquad P=EE^\dagger,
\qquad \operatorname{rank}P=3.
\tag{PC.43}
$$

Allowed preparations append independent blank ancillas on the specimen
side and use specimen-local CP maps, classical conditioning and local
discarding. They do not supply an entangled resource across the
specimen/reference cut or act jointly with the passive reference.
For finite-dimensional systems the Schmidt number of a mixed state
is the least $q$ allowing a convex decomposition into pure states of
Schmidt rank at most $q$; the same bound is understood under trace-norm
limits for the admitted convergent constructions. Scalar normalization
of a nonzero branch does not alter its rank bound and grants no
postselection permission in the original experiment.

**Proposition 9.2 (restricted exact-input obstruction).** Every input
and output in Definition 9.1's preparation class has Schmidt number
at most three across specimen-side systems versus $R$. Therefore no
source-preserving isometry or exact local preparation in that class
identifies such a state with the RT81 input $|\Omega_{2k}\rangle$,
whose Schmidt rank is $2k\ge4$. At $k=4$ the logical dimension eight
also exceeds the original full specimen dimension five.

Proof. Every pure vector in the support of $X$ has the form
$\sum_{j=0}^2 Ee_j\otimes r_j$. Its coefficient matrix has rank
at most three. A spectral decomposition of $X$ therefore gives a
pure decomposition with that bound. Appending a local pure blank
ancilla tensors each specimen vector with the same local vector and
does not increase coefficient-matrix rank. Mixed independent blanks
are handled by their own pure decompositions.

For any local Kraus operator $A$, the coefficient matrix $M_\psi$
of a pure component becomes $AM_\psi$. Since
$\operatorname{rank}(AM_\psi)\le\operatorname{rank}M_\psi$, every
nonzero resulting pure component has rank at most three. Sums over
Kraus operators, classical branches and discarded local systems give
mixtures of these components. Composition preserves the bound. In
finite dimensions the set of states of Schmidt number at most three
is closed: the normalized pure vectors of rank at most three form a
compact set, as the rank condition is given by vanishing minors;
its finite-dimensional convex hull is compact. Thus convergent sums
and admitted integral limits preserve the bound as well. With an
arbitrary reference, the same conclusion follows from the supported
three-term decompositions and their trace-norm closure.

In contrast, (PC.34) has $2k$ equal nonzero Schmidt coefficients.
A pure state of Schmidt rank $2k$ cannot be decomposed into pure
states of smaller rank: every positive summand of its rank-one
density matrix has range in the same one-dimensional span.
Consequently its Schmidt number is $2k$. Local isometries preserve
the original nonzero Schmidt coefficients and cannot make this
identification. Local CP preparation cannot do so by the preceding
rank argument. Finally there is no isometry of an eight-dimensional
logical input into the original five-dimensional ambient specimen;
appending independent local blanks removes that elementary dimension
obstruction but leaves the Schmidt bound. $\square$

This proposition is restricted to supported original inputs and the
specified passive-reference/local-operation class. It supplies no
exclusion of a noisy encoding with a separately proved error
inequality, a transfer using a different justified witness, or any
future operational reduction with an explicit resource correspondence.
Correlated entangled shares require their original joint accounting;
they cannot be inserted into the proposition as independent blanks.

## 10. Primary interfaces and the missing transfer conditions

**Convention 10.1 (mathematical attribution).** The source-specific
deductions in §§3–6 are the lower-left cutoff, the explicit complete
nine-coordinate separator, the positive pure-contact cap and its
conditional rank-one consequence. They are repo-derived applications
of the precise source bounds and complete-face interfaces in FC and
GC. The maximal-zero real-square reduction is FC Theorem 12.1;
the all-optima and compatible-group mechanisms are FC Theorems 3.3,
4.2 and 7.3; the mandatory reverse and negative-pure results are FC
§28 and §§32–34. Theorem 8.1, Corollary 8.2 and Proposition 9.2 give
exact interface obstructions using the coherent RT81 definitions and
elementary matrix identities. No general factorization, separation,
quadrature, Schmidt or Kraus–Stinespring theorem is claimed as new.

The following primary texts specify the finite-support interfaces
relevant to this problem:

| Primary source | Statement and permitted use |
| --- | --- |
| Dritschel–Rovnyak, *The Operator Fejér–Riesz Theorem*, [arXiv:0903.3639v1, §1](https://arxiv.org/html/0903.3639v1) | The scalar nonnegative Laurent polynomial factors as $|p|^2$ on the circle. FC Theorem 12.1 supplies the stronger maximal-zero real-square step used in (PC.25). No operator-factor rank or actual-label bound follows from the scalar citation. |
| Nailwal–Zalar, *Gaussian Quadratures with prescribed nodes via moment theory*, [arXiv:2412.20849v1, Theorem 3.1 and Example 3.6](https://arxiv.org/html/2412.20849v1) | For distinct prescribed nodes, complete univariate moments through $D=d_1+2d_2-1$ and positive definite $M_{\lfloor D/2\rfloor}$, existence of the specified $(d_1+d_2)$-atomic rule requires invertibility of $\mathcal H_f(d_2-1)$ and positive definiteness of the recursively generated $M_{d_1+d_2-1}$. With factorial moments and prescribed $1/3,11$, Example 3.6 violates extension positivity. The original rational-capacity and absolute-value tests are not supplied as such complete polynomial data. |
| di Dio–Schmüdgen, *The Moment Cone*, [arXiv:1809.00584v1, Theorem 52](https://arxiv.org/html/1809.00584v1) | The $m-1$ atom refinement requires at most $m-1$ path-connected components of the normalized evaluation image. A finite exposed contact set need not retain connectedness of the source circle. That hypothesis cannot be inferred from the circle alone. |
| Mädler–Schmüdgen, *On the Truncated Matricial Moment Problem. I*, [arXiv:2310.00957v1, Theorem 5.1](https://arxiv.org/html/2310.00957v1) | On its measurable space with measurable singletons, a nonzero moment functional on a finite-dimensional real space $\mathcal E$ of integrable measurable Hermitian matrix tests has a representation by at most $\dim\mathcal E$ rank-one matrix-mass terms, with the stated measurable support restriction when supplied. This preserves the chosen test functional, not an unproved recovery of fractional labels, height signs or seven original groups. |

At a common matrix node, separate pure and saturated matrix entries
still need the weak-sign condition (PC.9) to merge without height loss.
Neither a node count nor a matrix-mass rank replaces that condition.
The source-specific separator applies directly to the original moments
and needs no quadrature reduction.

Watrous, *The Theory of Quantum Information*, author-hosted
[Chapter 1, Schmidt decompositions](https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf),
[Chapter 2, instrument equations (2.258)–(2.262), Theorem 2.22 and Corollary 2.27](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf),
and [Chapter 3, Definition 3.43](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf),
gives the coefficient-matrix Schmidt correspondence, the
standard instrument construction, Kraus/Choi/Stinespring interfaces
and the arbitrary-reference norm
convention. These textbook interfaces support the elementary arguments
above; they do not supply an original-source reduction. The bounded
source and literature interfaces here carry no exhaustive novelty or
worldwide priority assertion.

**Open problem 10.2 (an admissible coherent-transfer bridge).** To use
RT81 for the original quantum task requires a coherent, phase-consistent
record construction and a source/input/target correspondence; an error
inequality in the direction that transfers its lower bound to the
original twelve-history HALF objective; and a proved relation between
RT81's local pure environment resource and the original actual-label
and jointly accessible fibre resources. The original eight moments do
not specify cross-label coherent phases. The original finite test
objective is not the arbitrary-reference norm of (PC.33), and merely
having that larger norm lower-bounded gives no lower bound on the
original restricted objective. Proposition 9.2 excludes the stated
exact input identification, and Corollary 8.2's instrument calculation
distinguishes readable counts from the specified-channel environment
resource. Noisy encodings and other explicitly proved reductions
remain available.

## 11. The remaining actual-count, source and native mathematics

**Open problem 11.1 (all original optima and saturated groups).** Let
$\mathcal P$ be the complete endpoint polytope with moment target
$B(t)$, let $\gamma(w)$ count occupied compatible groups, and let
$\kappa_i=|u_i|$. The original minimum low count on a supplied face is

$$
n_t(r)=\min\{\gamma(w):w\in\mathcal P,\ \kappa^Tw=r\}.
\tag{PC.44}
$$

FC Theorems 5.2–6.1 identify $U_m$, the union of the contrast images
of all coordinate faces using at most $m$ groups, with
$\{r:n_t(r)\le m\}$. In particular

$$
n_t(r)=8\iff r\in U_8\setminus U_7,\qquad
n_t(r)=9\iff r\in[r_-,r_+]\setminus U_8.
\tag{PC.45}
$$

Universal seven-low compression still requires $U_7=[r_-,r_+]$ at
every required attained-face scope. Universal $U_8$ coverage and an
actual eight-/nine-low necessity seed also remain unresolved here.
A necessity seed needs the same-root attained primal/dual tuple,
global entire-cylinder feasibility, complete circle zeros of all eight
tests, multiplicities, weak-sign groups, positive weights and exclusion
of every shorter alternative optimal representation. A pure-contact
cap, a mandatory singleton, one positive table or its ranks do not
provide those all-family exclusions. GC's minimum total count is
$1+n_t(r)$ under its weak coherent-completion premises; this is an
equality of minima, not every instrument's count identity.

Theorem 5.2 applies only to finite $\lambda>0$, finite jointly attained
duals and $t\ge\max(t_0,800)$. Corollary 6.2 additionally requires
$t\ge30000$ and the nonzero rank-one negative-semidefinite branch.
Neither result supplies a saturated-count bound, a finite-dual
existence theorem, an assertion at $\lambda=0$, nonfinite/unattained
limits or an unsupplied boundary attainment. No forbidden-inventory
attained tuple is exhibited by its conditional exclusion.

**Open problem 11.2 (the full original finite frontier).** The target
remains an evaluated all-budget, all-contrast finite-$(s,A)$ roof over
every common oriented failure allocation and live-height decomposition,
including points below the maximum contrast of a fixed allocation.
Global branch ordering, connected coverage, selected coefficients,
orientations, contacts and positive weights; all occupied and unused
root signs and multiplicities; collisions, capacity/rank/count
transitions; endpoint, threshold, budget and degenerate-orientation
gluing; coefficient gluing, next terms and uniform joint limits retain
their original scopes. FA Theorem 81.2 and the JS limiting interfaces
referenced by FC §40 supply no additional finite-budget optimal-support
restriction. Weak, strong optimal and strong feasible counts remain
different questions.

**Open problem 11.3 (source and physical correspondence).** Source
existence/isolation/Jacobian, root TP and ranks, the stopped-cq minimax,
sharp worst-history JOINT cost, separate unaveraged equality,
full-complex multi-Kraus rigidity, physical capacity and the common
constructor remain the independent suppliers in Assumption 1.1.
Native source access and calibration, coherently counted storage,
whole-fibre actuation, acquisition duration, absolute clock alignment,
archive/source/epoch/controller permissions and the native-instrument
and count bridges remain separate unsupplied conditions. Mathematical
CP/TP constructors do not supply these physical permissions. The
original one-specimen, twelve-history quantum-first AURIC FIB ATOM
task through 2027 retains all of these requirements.

## 追加锚（本行以下为增补区）
