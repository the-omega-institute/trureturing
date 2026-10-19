# Native complete-continuation finite activity frontier

## 67. Original instruments and whole-fibre activity

**Convention 67.1 (conditional source and unchanged experiment).** This
is a same-topic continuation of [JR, §§29–57][JR] and [RC, §§58–66][RC].
All source correspondences in this volume refer to the immutable revision
`e35db6260a4bd66b11e6b36cbece55650c937e70`. The isolated CG root,
isolation and Jacobian certificate, exact ranks, normalization and minimax
identification in [CG, §§13–17][CG] are inherited conditional premises,
`ASSUMED-UNVERIFIED` anew here. Operator identities and trace preservation
are asserted at that root. Comparisons on a surrounding box assert only
inequalities of the displayed expressions, never off-root normalization.
The arguments below are ordinary conditional mathematical proofs, without
Lean/kernel or native certification.

Retain JR Definition 41.1. There is one normalized unknown specimen in
five modes, supported on the isometry
$E=((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2)$, with $P=EE^\dagger$.
The twelve histories are

$$
p_y=(y/128,(64-y)/128,1/2),\quad a_y=(\sqrt{p_{yi}})_i,\quad
\rho_{y,e,n}=U_{e,n}a_ya_y^TU_{e,n}^\dagger,\quad
U_{e,n}=\operatorname{diag}(e,n,1),
$$

where $y\in\{5,16,27\}$ and $e,n\in\{\pm1\}$. The original parameters
are $x_{\rm hist}=y/256$, $e=(-1)^{\beta_{\rm hist}/\pi}$ and
$n=e(-1)^{m_{\rm hist}}$ (CG.179–.180). The ideal live block is CG.111;
the five separate failure labels are $(0,1,2,3,13)$, with weights
$w=(0,1/4,1/2,1/4,0)$ and densities $w_\ell f_y(t)P_f$, where
$f_y(t)=6y/(y+6t)^2$. Time $t\in[0,1]$ means original absolute time
$6+t$. The error is HALF the complete stopped-cq norm, maximized over
these twelve histories, with all coherences, singular-time measures,
wrong supports, aborts and zero-target sectors included. No prior,
acceptance division, postselection, helper specimen, copy, reset, retry,
readable history or uncounted accessible share is admitted.

An actual acquisition has CP encoders $\mathcal E_\alpha$ with total
effect $I_5$ and full-output TP decoders. Its retained classical label
$\alpha$ is generated, not supplied by the source. Its quantum fibre
counts jointly every subsequently accessible input-bearing specimen,
memory, controller, environment and entanglement share. Permanently
discarded Kraus indices are not labels. The principal class has finite
labels; necessity also holds for the convergent countable and expressly
measurable/integrable finite-fibre extensions of CG Convention 21.3.
Nothing here asserts a general disintegration or infinite-dimensional
coding theorem.

**Definition 67.2 (activity-constrained original class).** Each decoder
has a positive absorbing first-event rate $R_\alpha(t)$ on its entire
joint fibre. Between failures its supplied controls preserve trace; loss
occurs only through that rate. More precisely its unnormalized survivor
map $\mathcal S_{\alpha,t}$ and jump densities satisfy the usual
finite-dimensional CP evolution and trace balance

$$
-\frac d{dt}\operatorname{tr}\mathcal S_{\alpha,t}(X)
 =\operatorname{tr}\bigl(R_\alpha(t)\mathcal S_{\alpha,t}(X)\bigr),
\qquad \mathcal S_{\alpha,0}=\mathrm{id}.
$$

The positive rate is measurable and has integrable operator norm.
Hamiltonian and unobserved TP survivor controls are allowed. Terminal
processing on survivors is TP. There is no forced terminal absorption,
singular first-event part, or positive-carrier action after a first
failure. These conditions describe a mathematical control class, not
permission to enact its operations.

Put $\mathsf A=\max_\alpha\int_0^1\|R_\alpha(t)\|\,dt$; in the
stipulated countable/integral extension use supremum/essential supremum.
This is neither an expectation nor an integral of a maximum across
labels. Let $\mathfrak F_{s,A}$ be the original class satisfying
$E(\Phi)=E_*$, $\mathsf V(F)\ge s$, $\mathsf W=\mathsf C(s)$ and
$\mathsf A\le A$. Here $\mathsf V(F)=2|\operatorname{Re}F_{01}|/\kappa$
and $\mathsf W$ is the maximum over all twelve histories of the
probability of acquisition dimension at least three (JR.20).
When this class is nonempty define $\mathcal T_A(s)$ as its supremum of
actual-label TV between heights $5,+,+$ and $27,+,+$. Retain the
unbudgeted optimum $\mathcal T(s)$ of JR.43; empty classes have no
claimed TV maximum. Budgets below zero are infeasible.

**Convention 67.3 (source coefficients).** Use JR.2, .21, .23, .49 and
JR45's $N$:

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=a|0\rangle\langle1|+b|1\rangle\langle0|,\quad
S=c|0\rangle\langle2|+d|2\rangle\langle0|,\quad M=\operatorname{diag}(0,m_1,m_2),\\
\theta=ab/(h_0h_1),\quad\omega=cd/(h_0h_2),\quad
\delta=\theta+\omega,\quad s_0=\sqrt\delta,\quad
v_0=\omega/(1-\theta),\quad u_s=\theta v_s+\omega,\\
\Delta=\rho_{27,+,+}-\rho_{5,+,+},\quad
N=\begin{pmatrix}\Delta A&\xi&\eta\\\xi&\Delta B&\zeta\\
\eta&\zeta&\Delta C\end{pmatrix},\quad
\ell(\mathbf c)=\mathbf c^TN\mathbf c,\quad K(\mathbf c)=xD+zT+wS.
\end{gathered}
$$

All seven amplitudes and $m_1,m_2,\theta,\omega$ are positive;
$0<\delta<1$. The symbols $a,b,c,d$ are source amplitudes, not
history coordinates. $v_s$ and $\mathfrak f$ mean JR.30–.31;
$\Delta A,\Delta B,\Delta C,\xi,\eta,\zeta,d_f,z_f,L_f$ mean JR.49.
In particular $\zeta<0$, $\Delta A,\Delta B,\Delta C,\xi,\eta>0$.
JR42 fixes, for every sharp-cost error optimizer, supported live map
$\Lambda_*=D(\cdot)D^\dagger+T(\cdot)T^\dagger+S(\cdot)S^\dagger$,
failure effect $M$, other effect zero, high failure zero on supported
inputs, and low/high coefficient Grams
$\operatorname{diag}(u_s,v_s,1)$ and
$\operatorname{diag}(1-u_s,1-v_s,0)$. Every nonzero low Kraus product,
with one common phase removed, consequently has

$$
x,z,w\in\mathbb R,\qquad x\ne0,\qquad x^2=\theta z^2+\omega w^2.
\tag{FA.1}
$$

These are consequences of complex equality, not restrictions placed on
competitors. They fix neither a full five-mode completion nor each
labelled time CP measure.

## 68. Prescribed time laws and their exact path cost

**Theorem 68.1 (prescribed-path minimum).** On a finite-dimensional
whole decoder fibre prescribe terminal live CP map $\mathcal L$ and
five measurable finite-dimensional CP densities $\mathcal F_\ell(t)$.
Assume their effects are integrable, put
$B(t)=\sum_\ell\mathcal F_\ell(t)^\dagger(I)$ and
$S(t)=I-\int_0^tB(u)du$, and assume
$L=\mathcal L^\dagger(I)=S(1)\succ0$. In Definition 67.2's class with
known general TP terminal processing, the minimum activity, attained
with every prescribed labelled Borel map, is

$$
\mathfrak a_{\min}=\int_0^1
\|S(t)^{-1/2}B(t)S(t)^{-1/2}\|\,dt.
\tag{FA.2}
$$

It obeys

$$
-\log\lambda_{\min}(L)\le\mathfrak a_{\min}\le-\log\det L.
\tag{FA.3}
$$

The effects need not commute, and $\mathcal L$ may have arbitrary Kraus
multiplicity. A nonzero singular-time failure component cannot be
realized in this finite-rate class. If terminal processing is restricted
to an isometry, the general sufficiency statement requires the normalized
terminal CP map below to be isometric; it is not inferred for an
arbitrary multi-Kraus $\mathcal L$.

**Proof.** In any realization, TP survivor controls and trace balance
give $\mathcal S_t^\dagger(I)=S(t)$ and
$B(t)=\mathcal S_t^\dagger(R(t))$ almost everywhere. Since
$0\preceq R(t)\preceq\|R(t)\|I$, positivity implies
$B(t)\preceq\|R(t)\|S(t)$. Congruence by $S(t)^{-1/2}$ proves the
pointwise lower bound in FA.2. This uses neither a single-Kraus survivor
nor a commutative effect path.

For attainment let $K_t=S(t)^{1/2}$ and
$R(t)=S(t)^{-1/2}B(t)S(t)^{-1/2}$. Since $S(t)\succeq L\succ0$,
the square-root path is absolutely continuous, its derivative and inverse
are integrable/bounded as needed. With $A_t=\dot K_tK_t^{-1}$,
differentiating $K_t^2=S(t)$ gives
$A_t+A_t^\dagger=-R(t)$. The self-adjoint
$H_t=i(A_t-A_t^\dagger)/2$ therefore satisfies
$\dot K_t=(-iH_t-R(t)/2)K_t$. The current-survivor jump density is
$\mathcal J_\ell(t)=\mathcal F_\ell(t)\circ\operatorname{Ad}_{K_t^{-1}}$.
Its total effect is $R(t)$, and
$\mathcal J_\ell(t)\operatorname{Ad}_{K_t}=\mathcal F_\ell(t)$
on every complex matrix. At the end apply only to survivors
$\Theta=\mathcal L\circ\operatorname{Ad}_{L^{-1/2}}$.
It is CP and $\Theta^\dagger(I)=I$, hence TP; this is a fixed map,
not input-dependent normalization. The no-event map followed by
$\Theta$ is exactly $\mathcal L$.

The same construction from any intermediate $s$ uses $K_tK_s^{-1}$.
Differentiating its squared norm gives negative derivative, so it is
contractive. Integrating the jumps plus its terminal effect gives
identity on the whole fibre. Splitting the jump integral at a cut
proves chronological consistency and keeps the first event absorbing.
Thus it supplies an actual CP first-event instrument, not a retrospective
time draw. The finite-dimensional Choi square root supplies measurable
Kraus densities if one is desired; no Kraus index is made readable.

Jacobi's formula and cyclicity give
$\int_0^1\operatorname{tr}R(t)dt=-\log\det L$; positivity gives the
upper bound in FA.3. For any positive input, trace balance gives
$\dot p(t)\ge-\|R(t)\|p(t)$ even with TP survivor controls.
Integration gives $L\succeq e^{-\mathfrak a}I$ and proves the lower
bound. It also proves positive survival for every nonzero input at any
finite activity. All finite-rate jump measures have Lebesgue densities,
so none can equal a nonzero singular component. The terminal-isometry
qualification follows from the displayed $\Theta$ itself. This uses the
mature no-jump/first-jump framework [CKL, §II, II.3–II.11 and
II.17–II.21][CKL] and TP postprocessing [LS, §6.1, Definition 7][LS]
as intermediate tools; the pullback lower bound establishes the claimed
minimum. $\square$

**Proposition 68.2 (an original endpoint-equivalent pair).** There are
two prescribed-time decoders on the same actual original acquisition,
with identical terminal live map, identical integrated maps in each
original failure label, identical supported outputs on all complex
matrices, original errors, contrast and sharp cost, but different minimum
uniform activities. Their high fibre is jointly counted as dimension
five, including a coherent two-dimensional complement.

**Proof.** Take the attained strong instrument of Theorem 71.1 below at
$s^\dagger,A_\dagger$, whose two high matrices are the invertible
$H_\pm=(\sqrt{1-u^\dagger}D\pm\sqrt{1-v^\dagger}T)/\sqrt2$.
Choose an isometry $W:\mathbb C^2\to V^\perp$ and replace the $H_+$
encoder and the separate complementary branch by the single encoder
$\widetilde C_H\psi=(H_+E^\dagger\psi)\oplus W^\dagger\psi$.
Its whole fibre is $\mathbb C^3\oplus\mathbb C^2$; cross-support
coherences enter that fibre coherently. Its encoder effect is
$EH_+^\dagger H_+E^\dagger+WW^\dagger$, so total acquisition
normalization remains $I_5$. Complement has probability zero on all
twelve original inputs and changes none of their costs.

For $0<\ell<1$ use terminal live matrix
$[E\ W](I_3\oplus\sqrt\ell I_2)$ on that fibre. Write $P_3,P_4$ for
its two complementary coordinate projections. Prescribe respectively
$B_\parallel(t)=(1-\ell)(P_3+P_4)$ and
$B_{\rm seq}(t)=2(1-\ell)P_3$ for $t<1/2$,
$2(1-\ell)P_4$ for $t\ge1/2$. In each label prescribe density
$Y\mapsto w_\ell\operatorname{tr}(B(t)Y)P_f$, where the subscript on
$w$ denotes a label and the standalone $\ell$ denotes attenuation.
Their common endpoint effect is $I_3\oplus\ell I_2$ and their
integrated failure maps agree. On supported inputs these decoders are
identity in the first three coordinates, with no failure. FA.2 gives

$$
\mathfrak a_\parallel=-\log\ell,\qquad
\mathfrak a_{\rm seq}=-2\log\ell.
\tag{FA.4}
$$

Indeed each simultaneous scalar loss contributes the same hazard, whose
maximum integrates to $-\log\ell$; the two sequential losses occupy
disjoint half intervals and add. The normalized terminal map here is an
isometry, so both minima are attained. Choose $-\log\ell>A_\dagger$;
all other decoder minima are at most $A_\dagger$, hence the two
minimum uniform budgets differ. This is a statement for the supplied
actual acquisition and prescribed laws. It does not optimize over a
changed acquisition. It refutes endpoint-only path sufficiency inside
the original supported task, on the same clock, without a helper or an
uncounted bypass. Its free completion differs from fixed CA.10.
$\square$

## 69. Double rank rigidity and exact low-label capacity

**Theorem 69.1 (arbitrary Kraus implementations are doubly rigid).**
For finite $A$, every actual low label nonzero on supported inputs has
fibre dimension exactly two. Its supported encoder and live decoder
are CP maps of Kraus rank one,
$\mathcal E_\alpha=\operatorname{Ad}_{C_\alpha}$ and
$\mathcal R_\alpha^L=\operatorname{Ad}_{B_\alpha}$, with
$C_\alpha:\mathbb C^3\to\mathbb C^2$ onto and
$B_\alpha:\mathbb C^2\to\mathbb C^3$ injective. This conclusion is
about the existing actual label; it exposes no discarded Kraus index.

**Proof.** Trace balance proves the whole-fibre live effect
$L_\alpha^{\rm dec}\succeq e^{-A}I$. Thus a nonzero supported encoder
cannot have zero composite live map. Start with arbitrary Kraus matrices
$C_j,B_i$ of these two maps. Some product $B_{i_0}C_{j_0}$ is nonzero.
By FA.1 and the no-rank-one assertion CA Lemma 3.1, it has rank two.
Since the fibre is low, its dimension is two; $C_{j_0}$ is onto and
$B_{i_0}$ is injective. For every real null direction the kernels are

$$
\begin{aligned}
\ker K(\mathbf c)&=\mathbb C(1,-bz/(h_1x),-dw/(h_2x))^T,\\
\ker K(\mathbf c)^\dagger&=\mathbb C(1,-az/(h_1x),-cw/(h_2x))^T.
\end{aligned}
\tag{FA.5}
$$

The lower two equations prove these identities, the upper one following
from FA.1. The coefficients are positive; a common kernel or a common
image fixes both ratios $z/x,w/x$, hence fixes the product up to a
complex scalar. With $B_{i_0}$ fixed, all nonzero $B_{i_0}C_j$ have
its image and are proportional. Injectivity makes all nonzero $C_j$
proportional. With $C_{j_0}$ fixed and onto, all nonzero $B_iC_{j_0}$
have its kernel and are proportional; surjectivity makes all nonzero
$B_i$ proportional. Absorb the sums of squared proportionality constants
into one matrix each. A zero product with the fixed injective/onto
matrix forces the other factor zero, so none has been missed. This also
covers countable Kraus representations in finite dimensions.

The supported other output is zero by JR42. Onto $C_\alpha$ lifts that
zero CP composition to zero on the entire decoder fibre: for every
positive $Y$ choose positive $X$ with $C_\alpha XC_\alpha^\dagger=Y$.
Thus the full decoder consists of live and canonical failure there.
No extra output loss is hidden. $\square$

**Theorem 69.2 (rank-one capacity, including the axes).** For nonzero
$\mathbf c=(x,z,w)$ satisfying FA.1 define

$$
\begin{aligned}
n(\mathbf c)&=(0,dw/h_2,-bz/h_1)^T,\\
\mathcal D(\mathbf c)&=h_0^2x^2+b^2z^2+d^2w^2,\\
\mathcal N(\mathbf c)&=h_1^2h_2^2x^2+a^2h_2^2z^2+c^2h_1^2w^2,\\
\mathfrak c(\mathbf c)&=\mathcal N(\mathbf c)/\mathcal D(\mathbf c)>0.
\end{aligned}
\tag{FA.6}
$$

For an actual label with live product $K(\mathbf c)$, its pulled-back
total failure effect necessarily has the form

$$
N_\alpha=\beta_\alpha n(\mathbf c)n(\mathbf c)^T,\qquad\beta_\alpha\ge0.
\tag{FA.7}
$$

Writing $t_A=e^A-1$, the exact endpoint activity capacity is

$$
N_\alpha\preceq t_AK(\mathbf c)^\dagger K(\mathbf c)
\quad\Longleftrightarrow\quad
0\le\beta_\alpha\le t_A\mathfrak c(\mathbf c).
\tag{FA.8}
$$

For every admitted absolutely continuous prescribed labelled CP time law
on this label the minimum decoder activity is

$$
\mathfrak a_\alpha=\log(1+\beta_\alpha/\mathfrak c(\mathbf c)).
\tag{FA.9}
$$

It is attained with its prescribed time law, when its terminal live map
is retained, using only terminal isometry. Thus FA.8 is necessary for
every competitor and sufficient for an actual finite-rate construction;
it does not require every competitor's density to be $g(t)$.

**Proof.** Put $G=K^\dagger K$. By Theorem 69.1,
$\ker C=\ker K$, and every pulled failure subeffect kills this kernel.
Since $N_\alpha\preceq M$, it also kills $|0\rangle$.
These two independent null vectors leave precisely the line spanned by
$n(\mathbf c)$; $n$ is real and nonzero even if $z=0$ or $w=0$.
Positive rank at most one proves FA.7. The entry $G_{00}=\mathcal D>0$.
Block elimination in coordinate zero gives

$$
G-\frac{G|0\rangle\langle0|G}{G_{00}}
 =\mathfrak c(\mathbf c)n(\mathbf c)n(\mathbf c)^T.
\tag{FA.10}
$$

For explicit algebra, $G_{01}=xz(h_0a+h_1b)$,
$G_{02}=xw(h_0c+h_2d)$, $G_{11}=a^2z^2+h_1^2x^2$,
$G_{22}=c^2w^2+h_2^2x^2$, $G_{12}=aczw$.
Multiplying the $11,12,22$ residual entries by $\mathcal D$ and
substituting $x^2=abz^2/(h_0h_1)+cdw^2/(h_0h_2)$ gives respectively
$\mathcal N d^2w^2/h_2^2$,
$-\mathcal N bdzw/(h_1h_2)$ and
$\mathcal N b^2z^2/h_1^2$; the other entries are zero.
For $t>0$ the Schur complement of the positive $00$ pivot in $tG-N$
therefore proves FA.8. For $t=0$ both sides mean $N=0$, so the endpoint
is included.

Let $F$ be the decoder total failure effect, so
$C^\dagger FC=N$, $C^\dagger(I-F)C=G$.
Since $C|0\rangle\ne0$, $F C|0\rangle=0$ forces
$\operatorname{rank}F\le1$ on its two-dimensional whole domain.
Every time/label subeffect is dominated by $F$, hence has this same
one-dimensional direction, including when its output CP density has
several Kraus operators. Thus the accumulated effect path is
$I-a(t)P_F$, with $a$ absolutely continuous increasing from $0$ to the
nonzero eigenvalue $f<1$ of $F$. FA.2 integrates exactly to
$-\log(1-f)$, independently of the admitted distribution among labels
and times. Surjective congruence by $C$ makes
$F\preceq t(I-F)$ equivalent to $N\preceq tG$.
Its least such $t$ is $f/(1-f)=\beta/\mathfrak c$ by FA.10,
proving FA.9. The live decoder has one Kraus matrix $B$, so its
normalized terminal map is the isometry $B(I-F)^{-1/2}$.
If $\beta=0$, $F=0$, every failure submap is zero and activity zero
attains the live isometry. Signs of $x,z,w$ are unrestricted; a common
phase and $x<0$ change none of the argument. The zero coefficient
vector represents no supported branch and is omitted. $\square$

## 70. Entire-fibre first-event constructors

**Proposition 70.1 (one actual low label).** Let $K=K(\mathbf c)$ and
$N=\beta nn^T$ be as in Theorem 69.2, with finite $\beta\ge0$.
Choose a fixed row-space isometry
$J:\mathbb C^2\to\operatorname{ran}K^\dagger$ and set

$$
Q=J^\dagger(K^\dagger K+N)J,\quad
C=Q^{1/2}J^\dagger,\quad B=KJQ^{-1/2},\quad
F=Q^{-1/2}J^\dagger NJQ^{-1/2}.
\tag{FA.11}
$$

These satisfy on the entire two-dimensional domain

$$
BC=K,\quad C^\dagger FC=N,\quad B^\dagger B+F=I_2,\quad
B^\dagger B\succ0.
\tag{FA.12}
$$

A fixed convenient attained time law uses

$$
\begin{gathered}
g(t)=2/(1+t)^2,\quad G(t)=2t/(1+t),\\
K_{\rm dec}(t)=\sqrt{I-G(t)F},\qquad
R(t)=g(t)F(I-G(t)F)^{-1}.
\tag{FA.13}
\end{gathered}
$$

Its first-event map from the initial decoder input is, separately in
each original label, $Y\mapsto w_\ell g(t)\operatorname{tr}(FY)P_f$.
Its terminal live map is $\operatorname{Ad}_B$. Its activity is FA.9,
and equals $A$ when $\beta=t_A\mathfrak c$. These are full-fibre
CP/TP statements, not just effects on a chosen test input.

**Proof.** Both $G_K=K^\dagger K$ and $N$ are supported on
$\operatorname{ran}K^\dagger$; $G_K$ is strictly positive there.
Consequently $Q\succ0$, $JJ^\dagger$ fixes $K^\dagger$ and $N$,
and multiplication gives all four identities in FA.12.
In particular $0\preceq F\prec I$ and $B$ is injective.
The current-survivor jump CP density, rather than its initial-input
pullback, is explicitly

$$
\mathcal J_\ell(t)(Y)
 =w_\ell g(t)\operatorname{tr}
 \bigl(FK_{\rm dec}(t)^{-1}Y K_{\rm dec}(t)^{-1}\bigr)P_f.
$$

Its total effect is $R(t)$. Here $F$ commutes with the no-jump path,
so $\dot K_{\rm dec}=-R K_{\rm dec}/2$ with Hamiltonian zero.
Precomposition with $\operatorname{Ad}_{K_{\rm dec}(t)}$ gives exactly
the stated initial-input density. At time one use the isometry
$U=B(I-F)^{-1/2}$ on survivors only; $U^\dagger U=I$ by FA.12.
It produces $B$ as the live matrix. The integrated failure effect is
$F$ since $G(1)=1$, complementary to $B^\dagger B$.
Intermediate chronological completeness follows as in Theorem 68.1.
Only the not-yet-failed carrier evolves; after a first jump the stopped
successor and its label/time are retained with no positive-carrier
operation. There is no failure atom at the deadline. The nonzero
eigenvalue of $F$ is $\beta/(\mathfrak c+\beta)$, so integration of
its hazard gives FA.9. This includes $F=0$ with zero jumps and zero
rate. All choices are fixed before the unknown input. $\square$

**Convention 70.2 (assembling original instruments).** Whenever a finite
list of live matrices has total coefficient Gram $I_3$ and its attached
failure effects sum to $M$, encode each low label by FA.11, each high
matrix $H$ directly into its whole three-dimensional fibre with live
isometry $E$, and precompose supported encoders by $E^\dagger$.
For a low label the actual encoder effect is
$E(K^\dagger K+N)E^\dagger$. Generate and retain its declared
classical label and binary report; independent report coins may split
this label without changing its quantum dimension or rate. Add the
coherent counted dimension-two complement of Theorem 75.1. These
operations have total encoder effect $I_5$ and are CP/TNI branchwise,
as proved there. They define a common instrument, not a family indexed
by the unknown history. Competitors need not use FA.13: it is a chosen
attainer. The general prescribed-path realization supplies their own
admitted labelled CP densities whenever those are being retained.

## 71. Complete finite-budget strong regime

**Theorem 71.1 (isolated strong feasibility and attained threshold).**
Define

$$
\begin{gathered}
v^\dagger=\frac{m_2d^2h_1^2}{m_1b^2h_2^2},\quad
s^\dagger=\mathfrak f(v^\dagger),\quad u^\dagger=\theta v^\dagger+\omega,\\
\mathfrak c_\dagger=\mathfrak c(\sqrt{u^\dagger},\sqrt{v^\dagger},1),
\quad\nu_\dagger=\frac{m_1h_2^2}{d^2\mathfrak c_\dagger},
\quad A_\dagger=\log(1+\nu_\dagger).
\end{gathered}
$$

Then $s_0<s^\dagger<1$, and for $s\in[s_0,1]$

$$
\mathfrak F_{s,A}\ne\varnothing
\quad\Longleftrightarrow\quad s=s^\dagger\ \text{and}\ A\ge A_\dagger.
\tag{FA.14}
$$

In particular the threshold is attained, while $s=s_0$ and $s=1$
are infeasible at every finite budget.

**Proof.** JR42–43's equality conditions give four real low rays
$K_{\sigma\tau}=\sqrt uD+\sigma\sqrt vT+\tau S$ with total live
coefficient weight $1/4$ on each, where $v=v_s$, $u=\theta v+\omega$.
This includes $s=s_0$ and $s=1$. By FA.7 all supported failure on such
a ray has line $(0,dh_1,-\sigma\tau\sqrt v\,bh_2)^T$.
Thus its diagonal ratio is $d^2h_1^2/(vb^2h_2^2)$. Finite activity
excludes nonzero supported labels with zero live map, and high labels
cannot carry supported failure by JR42. Summing all failures to $M$
forces $v=v^\dagger$. The whole-box bounds in Proposition 74.1 give
$0<v_0<1/5<v^\dagger<3/10<1$. Strict decrease of $\mathfrak f$ on
$[v_0,1]$ gives the stated location of $s^\dagger$.

Put $b_\kappa=(0,\sqrt{m_1},-\kappa\sqrt{m_2})^T$,
$W_\kappa=b_\kappa b_\kappa^T$. A label on ray $\sigma,\tau$ has
live matrix $\sqrt pK_{\sigma\tau}$ and failure $qW_{\sigma\tau}$.
FA.8, using $\mathfrak c$'s invariance under scalar multiplication,
is exactly

$$
0\le q\le rp,\qquad r=t_A/\nu_\dagger.
\tag{FA.15}
$$

The two signs $\kappa=\sigma\tau$ must each have total $q=1/2$:
the diagonal equations give their sum one and the zero off-diagonal
entry gives their difference zero. Each has two rays with $p=1/4$,
so capacity requires $r\ge1$. Conversely on each ray take
$p=q=1/4$; their failures sum to $M$ and their live Gram is the
required $\operatorname{diag}(u^\dagger,v^\dagger,1)$.
Use FA.11–.13 and the high pair
$H_\sigma=(\sqrt{1-u^\dagger}D+\sigma\sqrt{1-v^\dagger}T)/\sqrt2$,
with report $\sigma$ on low and high labels and fair complement report.
Failures kill coordinate zero and contribute no $01$ report entry.
JR.29 then gives contrast exactly $\mathfrak f(v^\dagger)$;
Theorem 75.1 proves all original outputs and costs simultaneously.
Every low decoder has activity $A_\dagger$, and high/complement rates
are zero. Thus the equality budget is feasible. $\square$

**Theorem 71.2 (attained TV at every feasible strong budget).** Set
$r=t_A/\nu_\dagger\ge1$ and

$$
\begin{gathered}
d_{\sigma\tau}=\operatorname{tr}(K_{\sigma\tau}^\dagger
 K_{\sigma\tau}\Delta)=4\ell_{\sigma,\tau}(s^\dagger),\quad
g_\kappa=d_f+2\kappa z_f>0,\\
k_{\sigma\tau}(r)=\min\{(d_{\sigma\tau})_+/r,g_{\sigma\tau}\},\quad
k_{\kappa,1}(r)\le k_{\kappa,2}(r)
 \ \text{the two values with }\sigma\tau=\kappa,\\
D_\kappa(r)=\min\{1/2,r/4\}k_{\kappa,1}(r)
 +(2-r)_+k_{\kappa,2}(r)/4,\quad
\gamma_f=(L_f-d_f)/2>0.
\end{gathered}
$$

The maximum, including all saturation changes, is

$$
\mathcal T_A(s^\dagger)=\mathcal T(s^\dagger)-\gamma_f
 -D_+(r)-D_-(r).
\tag{FA.16}
$$

For $1\le r\le2$ the two coefficients in $D_\kappa$ are $r/4$
and $(2-r)/4$; for $r\ge2$ they are $1/2$ and zero.
Each $k$ changes formula at $r=d_+/g_\kappa$; equal values may be
ordered either way. This min/sort expression therefore specifies every
piece, including $r=1$, $r=2$ and coincident switches, without an
unresolved optimization.

**Proof.** The actual height difference on one label is $pd-qg$,
since $\operatorname{tr}(W_\kappa\Delta)=-g_\kappa$.
On the interval $0\le q/p\le r$, convexity of $|pd-qg|$ bounds
its absolute difference by that of two genuinely generated endpoint
labels, pure live and saturated, with the same totals. Conversely those
labels are admissible by FA.11. On one ray, with total $P=1/4$ and
total failure coefficient $Q$, the attained absolute-difference sum is

$$
P|d|+Qg-2Q\min\{d_+/r,g\}.
\tag{FA.17}
$$

To verify this also when $d\le0$, use pure-live weight $P-Q/r$ and
saturated weight $Q/r$; the sum is
$(P-Q/r)|d|+(Q/r)|d-rg|$, which gives FA.17 for either sign of
$d-rg$ and either sign of $d$. A zero weight is omitted.

For each $\kappa$, allocate its required total $Q=1/2$ between two
capacities $r/4$. If $1\le r\le2$, assign $r/4$ to the smaller $k$
and $(2-r)/4$ to the other; if $r\ge2$, assign all $1/2$ to the
smaller. This attains the minimum loss $D_\kappa$ and proves its
necessity by the elementary exchange inequality for a linear objective.
At $r=1$ both capacities must be full; at $r=2$ the second allocation
is zero. Crossing equal costs causes no discontinuity or lost attainment.
Both failure directions have negative height difference, so their total
absolute failure contribution is $(g_++g_-)/2=d_f$, rather than
$L_f$. The high branches contribute the fixed positive differences of
JR43; the four live rays have fixed total weights. Relative to JR.51,
replacing $L_f$ by $d_f$ loses $\gamma_f$, and FA.17 loses
$D_++D_-$ after taking HALF the absolute sum. This proves FA.16.
The endpoint splitting, optimal allocation and FA.11–.13 generate a
finite actual instrument attaining every bound simultaneously, with the
same reports, Gram, error and sharp cost. $\square$

**Corollary 71.3 (persistent gap and exact large-budget coefficient).**
There are the signs $d_{--}<0$ and $d_{++},d_{+-},d_{-+}>0$.
Let $d_{\min}=\min\{d_{+-},d_{-+}\}>0$. For
$r\ge\max\{2,d_{\min}/g_-\}$,

$$
\mathcal T(s^\dagger)-\mathcal T_A(s^\dagger)
 =\gamma_f+\frac{\nu_\dagger d_{\min}}{2(e^A-1)}.
\tag{FA.18}
$$

**Proof.** The three positive signs follow from JR43 over its entire
strong interval. Its decreasing $\mathsf b(v)$ is negative already at
$v=1/5$, by Proposition 74.1; $v^\dagger>1/5$ gives the fourth sign.
In the $\kappa=+$ pair the negative ray has zero $k$ and capacity
at least $1/2$ for $r\ge2$, so $D_+=0$. In the other pair
$k_{-,1}=d_{\min}/r$ under the stated saturation condition, whence
$D_-=d_{\min}/(2r)$. Substitute in FA.16. Thus the coefficient of
$e^{-A}$ beyond the persistent $\gamma_f$ is exactly
$\nu_\dagger d_{\min}/2$. Neither gap is an error term in $E_*$.
$\square$

## 72. Exact weak full-class moment formulation

**Theorem 72.1 (eight finite Toeplitz blocks, not a relaxation).** Let
$0\le s<s_0$, $t=e^A-1\ge0$, $L_0=\operatorname{diag}(\delta,1,1)$,
$\alpha_0=\theta/\delta$, $\beta_0=\omega/\delta$ and

$$
\begin{gathered}
\mathbf c(\phi)=(s_0,\cos\phi/\sqrt{\alpha_0},
 \sin\phi/\sqrt{\beta_0})^T,\qquad0\le\phi<2\pi,\\
\mathsf G(\phi)=\mathcal D(\mathbf c(\phi))\mathbf c(\phi)\mathbf c(\phi)^T,
\qquad\mathsf B(\phi)=\mathcal N(\mathbf c(\phi))
 n(\mathbf c(\phi))n(\mathbf c(\phi))^T.
\tag{FA.19}
\end{gathered}
$$

For eight nonnegative circle measures $\mu_{r,\epsilon,\eta}$ indexed
by $(r,\epsilon,\eta)\in\{\pm1\}^2\times\{0,1\}$, define

$$
\begin{aligned}
V^{\rm mom}_{s,t}=\max\quad&\sum_{r,\epsilon,\eta}\epsilon\int
 [\operatorname{tr}(N\mathsf G)+\eta t\operatorname{tr}(\Delta\mathsf B)]
 d\mu_{r,\epsilon,\eta}\\
\text{subject to}\quad&\sum_{r,\epsilon,\eta}\int\mathsf G\,d\mu_{r,\epsilon,\eta}=L_0,\\
&t\sum_{r,\epsilon}\int\mathsf B\,d\mu_{r,\epsilon,1}=M,\\
&\sum_{r,\epsilon,\eta}r\int\mathsf G_{01}\,d\mu_{r,\epsilon,\eta}\ge s.
\end{aligned}
\tag{FA.20}
$$

Then

$$
\mathfrak F_{s,A}\ne\varnothing\quad\Longleftrightarrow\quad
\text{FA.20 is feasible},
\tag{FA.21}
$$

and, when nonempty,

$$
\mathcal T_A(s)=\tfrac12[(1-\delta)\Delta A+V^{\rm mom}_{s,t}].
\tag{FA.22}
$$

Each integrand is a trigonometric polynomial of degree at most four.
With moments $m_k=\int e^{ik\phi}d\mu$, the exact finite condition
for each of the eight blocks is

$$
\operatorname{Toep}_5(m)=(m_{j-i})_{0\le i,j\le4}\succeq0,
\qquad m_{-k}=\overline{m_k}.
\tag{FA.23}
$$

The feasible moment set is compact, the maximum is attained, and at most
forty low labels, together with finitely many high/complement labels,
suffice. Singular and zero blocks are included. This finite SDP and its
implicit optimum are not a scalar evaluation of the weak frontier.

**Proof.** Every nonzero real null coefficient vector can have its
common sign removed and be written $\sqrt p\mathbf c(\phi)$ with
$p>0$: normalize its nonzero first coordinate to $s_0$ and use the
ellipse equation. Theorem 69.1 proves this for actual labels, even
though their starting Kraus representations were arbitrary.
Its failure effect is $p\beta nn^T$ with
$0\le\beta\le t\mathcal N/\mathcal D$. For $t>0$ split the
label, retaining its binary report, into pure-live weight
$p(1-\beta\mathcal D/(t\mathcal N))$ and saturated weight
$p\beta\mathcal D/(t\mathcal N)$. The resulting total live Gram,
failure effect, signed winding coordinate and sharp high effect are
unchanged. Absolute-value convexity bounds the old TV above by the new
one. Give each endpoint coefficient weight $p'$ the measure mass
$p'/\mathcal D$, and assign $\epsilon$ as the sign of its actual
height difference. This gives exactly FA.20. High branches have only
$D$ products in the weak regime; their height differences are all
positive, totaling $(1-\delta)\Delta A$. This proves necessity and
the upper value bound for every original time law. If $t=0$, FA.8
forces all supported failure to vanish, contradicting $M\ne0$;
FA.20 is also infeasible. Thus no division by zero is used.

Conversely a circle atom of mass $a>0$ in block $(r,\epsilon,\eta)$
gives an actual branch with
$K=\sqrt{a\mathcal D(\mathbf c)}K(\mathbf c)$ and
$N_{\rm fail}=a\eta t\mathcal N(\mathbf c)nn^T$.
It satisfies FA.8, purely live or budget-saturated. Use FA.11–.13,
retain report $r$, and add the high pair
$\sqrt{(1-\delta)/2}D$ with fair reports and coherent complement.
The equations in FA.20 give the original contrast inequality, live
Gram, failure sum, high effect and complete output of Theorem 75.1.
The actual absolute-difference sum is at least the signed objective
chosen by $\epsilon$. No full binary effects or channel were fixed
in proving the upper bound.

It remains to justify both the finite reduction and attainment rather
than assuming an arbitrary measure solution can be enacted. Every entry
of $\mathcal D\mathbf c\mathbf c^T$ and $\mathcal Nnn^T$ has degree
at most four, so only $m_{-4},\ldots,m_4$ occur linearly. Necessity of
FA.23 follows by integrating the squared absolute value of a polynomial
of degree at most four. For sufficiency use the classical Toeplitz
Vandermonde fact [YX, §II, Theorem 1][YX]. Its finite-dimensional
argument here also handles all degeneracies: Gram vectors
$v_0,\ldots,v_4$ for the PSD Toeplitz matrix obey
$\langle v_{i+1},v_{j+1}\rangle=\langle v_i,v_j\rangle$ for
$0\le i,j<4$. Thus $v_i\mapsto v_{i+1}$ extends by linearity to a
well-defined isometry of their spans. Domain and range have equal
dimension. Extend it to a unitary on the full Gram space of dimension
at most five, and spectrally decompose that unitary. Since
$v_j=U^jv_0$, its spectral masses at $v_0$ give at most five positive
circle atoms with precisely the prescribed moments (choose the phase
convention to match $m_k$). If $v_0=0$, Toeplitz diagonal equality
makes every vector zero and the empty measure suffices. Singular Gram
spaces require no inversion. This proves FA.23's sufficiency and at
most forty atoms over eight blocks.

On the circle $\operatorname{tr}\mathsf G$ has a strictly positive
minimum: $\mathcal D>0$, $x=s_0>0$, and the circle is compact.
The fixed total Gram therefore bounds the sum of all measure masses;
$|m_k|\le m_0$ bounds all moments. FA.23 and the linear equalities
and inequality form a closed bounded finite-dimensional set. Its
continuous objective attains a maximum when feasible. Spectral
finite realization of a maximizing tuple gives an actual instrument
with TV at least FA.22; the universal upper direction forbids strict
excess. This proves value equality and actual finite attainment.
$\square$

## 73. Attained weak feasibility threshold and endpoint divergence

**Theorem 73.1 (closed threshold and explicit two-sided bounds).** For
$0\le s<s_0$, let $t_{\min}(s)$ be the infimum of $t\ge0$ for which
FA.20 is feasible. It is positive, finite and attained, and

$$
A_{\min}(s)=\log(1+t_{\min}(s)),\qquad
\mathfrak F_{s,A}\ne\varnothing\ \Longleftrightarrow\ A\ge A_{\min}(s).
\tag{FA.24}
$$

Define

$$
\begin{gathered}
\mathfrak c_{\max}=\max\left\{
 \frac{h_2^2ah_1}{h_0b},\frac{h_1^2ch_2}{h_0d}\right\},\quad
V_f=\frac{m_2h_1^2}{b^2},\quad W_f=\frac{m_1h_2^2}{d^2},\\
\mu_f=\alpha_0V_f+\beta_0W_f,\quad
 d_{\rm mom}=\frac{(\sqrt{\mu_f}-\sqrt{V_f})^2}{2}>0,\quad
\nu_0=\max\left\{\frac{m_2}{\theta h_2^2},\frac{m_1}{\omega h_1^2}\right\},\\
\varepsilon_s=\min\left\{1,\frac{s_0-s}{s_0-\sqrt\theta}\right\}.
\end{gathered}
$$

Then

$$
\max\left\{\frac{\mu_f}{\mathfrak c_{\max}},
 \frac{d_{\rm mom}}{\mathfrak c_{\max}(1-s/s_0)}\right\}
\le t_{\min}(s)\le\frac{\nu_0}{\varepsilon_s}.
\tag{FA.25}
$$

In particular

$$
A_{\min}(s)=\log\frac1{1-s/s_0}+O(1),\qquad s\uparrow s_0.
\tag{FA.26}
$$

The implicit threshold itself is not evaluated as a scalar function.

**Proof.** Normalize the low coefficient vectors to
$\sqrt{p_j}(s_0,z_j,w_j)$ as in Theorem 72.1. Their Gram implies
$\sum p_j=\sum p_jz_j^2=\sum p_jw_j^2=1$.
Writing their failures as $p_j\beta_jn_jn_j^T$, the two diagonal
failure equations give
$\sum p_j\beta_jz_j^2=V_f$ and
$\sum p_j\beta_jw_j^2=W_f$.
The null equation $\alpha_0z_j^2+\beta_0w_j^2=1$ then gives
$\sum p_j\beta_j=\mu_f$.
Substitute the null equation into FA.6: the ratio $\mathfrak c$ is
a positive linear-fractional function of $z^2,w^2$, so it lies between
its two axial values. Direct cancellation gives exactly the two entries
of $\mathfrak c_{\max}$. Thus $\beta_j\le t\mathfrak c_{\max}$,
and the first lower bound follows. The signed contrast constraint gives
$\sum p_j|z_j|\ge s/s_0$. Consequently
$\sum p_j(|z_j|-1)^2/2\le1-s/s_0$.
Cauchy–Schwarz in the positive weights $p_j\beta_j$ gives

$$
\sum_jp_j\beta_j(|z_j|-1)^2/2
\ge (\sqrt{\mu_f}-\sqrt{V_f})^2/2.
$$

Since $V_f/W_f=v^\dagger<1$ and $\beta_0>0$,
$\mu_f>V_f$, so this is strictly positive.
Combining with $\beta_j\le t\mathfrak c_{\max}$ proves the other
lower bound, including $s=0$. These sums are coefficient moments, not
a prior on unknown histories.

For the upper bound take $\varepsilon=\varepsilon_s>0$ and the
following finite matrices and attached effects:

$$
\begin{aligned}
H&=\sqrt{1-\delta}\,D,\\
A_\sigma&=\sqrt{\varepsilon/2}(\sqrt\theta D+\sigma T),
&N^A_\sigma&=(m_2/2)|2\rangle\langle2|,\\
B_\tau&=\sqrt{\varepsilon/2}(\sqrt\omega D+\tau S),
&N^B_\tau&=(m_1/2)|1\rangle\langle1|,\\
C_{\sigma\tau}&=\frac{\sqrt{1-\varepsilon}}2
 (\sqrt\delta D+\sigma T+\tau S),&N^C_{\sigma\tau}&=0.
\end{aligned}
$$

Their low Gram is $L_0$, their failures sum to $M$, and the high
effect is $(1-\delta)D^\dagger D$. Use report $\sigma$ on $A,C$,
fair reports on $B,H$ and complement. Their raw contrast is
$(1-\varepsilon)s_0+\varepsilon\sqrt\theta\ge s$.
If exact contrast $s$ is desired, retain all old labels and append the
common binary kernel $(1+r\sigma s/V_{\rm raw})/2$ on the old
report; $V_{\rm raw}>0$ and the ratio is at most one.
The coordinate-zero killing of failure effects preserves this contrast
calculation. The null axes in FA.6–.9 give activities
$\log(1+m_2/(\varepsilon\theta h_2^2))$ and
$\log(1+m_1/(\varepsilon\omega h_1^2))$ on $A,B$, respectively.
The other rates vanish. FA.11–.13 and Theorem 75.1 therefore attain
the upper feasibility bound. When $\varepsilon=1$ omit the zero $C$
matrices; at $s=0$ report fair coins if exact zero contrast is chosen.
No zero-weight division is involved.

Feasibility is upward closed in $t$ because an instrument within a
budget remains within any larger budget. The equality to FA.20 passes
this monotonicity to the moment problem, though saturated/pure moment
coordinates themselves may change. Take feasible $t_n$ decreasing to
the positive finite infimum. The uniform mass bound in Theorem 72.1
is independent of $t_n$. Compactness of their moment tuples gives a
convergent subsequence; the constraints are continuous in moments and
$t$, so its limit is feasible at the infimum. This proves FA.24 and
threshold attainment. Near $s_0$ put $q=1-s/s_0$; FA.25 reads
$t_{\min}\ge d_{\rm mom}/(\mathfrak c_{\max}q)$ and
$t_{\min}\le\nu_0(s_0-\sqrt\theta)/(s_0q)$.
Taking $\log(1+t_{\min})$ proves FA.26 with explicit finite upper
and lower constants. $\square$

## 74. Whole-box positivity and the sharp fixed-strength deficit exponent

**Proposition 74.1 (complete source-box comparison basis).** In this
proposition alone evaluate expressions throughout the independent
nine-coordinate box $\mathcal B_9$ of RC.4, not only at its root.
Use CG.112–.113 for $S_0,S_{01},S_{02}$,
$H=1000\eta_0\operatorname{adj}S_0$,
$Q^{0i}=\eta_i\operatorname{adj}S_{0i}$, the positive-pivot
amplitudes CG.134, and
$m_1=1-H_{11}-Q^{01}_{00}$, $m_2=1-H_{22}-Q^{02}_{00}$.
All pivot and other denominators below are positive. In addition to
JR.52's seven amplitude intervals, the following strict comparisons
hold on the entire box. Define

$$
\begin{gathered}
a_{\rm sp}=(L_f-d_f)/2,\quad b_{\rm sp}=(L_f+d_f)/2,\quad
t_f=-2z_f/(d_f+L_f),\\
e_-=(1,t_f)^T/\sqrt{1+t_f^2},\qquad
e_+=(t_f,-1)^T/\sqrt{1+t_f^2},\\
q_f=\frac{dh_1}{bh_2}\sqrt{\frac{m_2}{m_1}}t_f.
\end{gathered}
$$

| Expression | Strict lower bound | Strict upper bound |
| --- | --- | --- |
| $v_0$ | $0$ | $1/5$ |
| $v^\dagger$ | $1/5$ | $3/10$ |
| $q_f$ | $18/100$ | $22/100$ |
| $\sqrt{\theta q_f^2+\omega}$ | $0$ | $54/1000$ |
| $\Delta C$ | $167/100000$ | $168/100000$ |
| $\eta-\xi q_f$ | $0$ | $14416/10^6$ |
| $4\mathsf b(1/5)$ | $-1$ | $0$ |

For either sign of $x/w$, every nonzero compatible direction
$z=-q_fw$, $x^2=(\theta q_f^2+\omega)w^2$ obeys

$$
\ell(\mathbf c)>w^2/10^4.
\tag{FA.27}
$$

Here compatibility means that the rank-one failure direction $n(\mathbf c)$
is proportional to $M_2^{1/2}e_-$, $M_2=\operatorname{diag}(m_1,m_2)$.
Thus this is a whole compatible-direction assertion, not a sample.

**Proof.** These are inequalities of explicit rational/radical
expressions. A directed integer evaluation sufficient to reproduce the
table is the following. Embed each of the nine rational centre-radius
intervals RC.4 independently in denominator $D=2^{256}$, outward
rounding both endpoints. Use outward endpoint sums, products and
quotients (only positive denominators occur); use integer-square-root
endpoints $[\lfloor\sqrt{aD}\rfloor,\lceil\sqrt{bD}\rceil]/D$ for
$[a/D,b/D]$. Form the three source slack matrices, their first-row
cofactor adjugates, the three positive pivots and amplitudes, then
$m_i,\theta,\omega,N,d_f,z_f,L_f,t_f,q_f$ in the displayed order.
In particular no $\eta_i$ is held at its centre. Besides the table,
the resulting intervals lie strictly inside
$0.01378914<\theta<0.01378916$,
$0.00192116<\omega<0.00192117$,
$0.49685026<m_1<0.49685027$,
$0.34447392<m_2<0.34447394$ and
$0.19893729<q_f<0.19893731$.
These latter rounded intervals are outputs of the full box calculation,
not independent replacements used to assert a source identity. The
arithmetic prescription uses exactly the nine centres in RC.4 and
CG.118's directed square-root rule; integer endpoint comparisons give
the stated rational margins. No determinant or TP equality is imposed
off root, and the construction uses no inverse of a singular source
matrix.

Substitution of $z=-q_fw$ gives

$$
\frac{\ell(\mathbf c)}{w^2}
=\Delta A(\theta q_f^2+\omega)+\Delta Bq_f^2+\Delta C-2\zeta q_f
 \ \pm2(\eta-\xi q_f)\sqrt{\theta q_f^2+\omega}.
$$

The first two terms and $-2\zeta q_f$ are nonnegative, with signs
from JR.49–.52. The table bounds the remainder below by
$0.00167-0.108(0.014416)=0.000113072>10^{-4}$.
This proves FA.27 for both signs. The relation between $z/w$ and
$e_-$ follows by equating the ratio of the last two entries in
$n=(0,dw/h_2,-bz/h_1)$; it includes either common sign.
Here $w=0$ in this compatible line would force the zero vector and
is excluded. At the conditional root $e_\pm$ are precisely the
positive/negative spectral directions of
$\Xi=\begin{psmallmatrix}-d_f&z_f\\z_f&0\end{psmallmatrix}$;
off root they are only the vectors given by the same formulas.
$\square$

**Theorem 74.2 (explicit positive uniform deficit).** For the normalized
circle FA.19 let

$$
\begin{gathered}
q_\pm(\phi)=|e_\pm^TM_2^{-1/2}n(\mathbf c(\phi))|^2,
\quad R_\pm^2=q_\pm(0)+q_\pm(\pi/2)>0,\\
m=\min(\alpha_0,\beta_0),\quad
\mu_\ell=\frac{\delta}{10^4(\theta q_f^2+\omega)},\quad
L_N=2\|N\|\frac{\sqrt{\delta+1/m}}{\sqrt m},\quad
\eta_*=\frac{\mu_\ell R_+}{4L_N},\\
c_{\rm TV}=\min\left\{b_{\rm sp},
 \frac{\min\{\mu_\ell/2,a_{\rm sp}\eta_*^2\}}{R_-^2}\right\}>0.
\tag{FA.28}
\end{gathered}
$$

For every nonempty weak class,

$$
\mathcal T(s)-\mathcal T_A(s)
 \ge\frac{c_{\rm TV}}{1+\mathfrak c_{\max}(e^A-1)}>0.
\tag{FA.29}
$$

The bound is uniform in weak $s$ wherever the class is feasible.
For an explicit conservative constant replace $\|N\|$ in $L_N$
by $\|N\|_F$. The same whole-box directed comparisons give
$c_{\rm TV}>10^{-10}$ even for that replacement; replacing it can
only decrease this lower-bound constant.

**Proof.** Both $q_\pm$ are squares of nonzero real linear
combinations of $\cos\phi,\sin\phi$. Their maximum is exactly
$R_\pm^2$. The zeros of $q_+$ are exactly the compatible negative
spectral lines of Proposition 74.1; at these zeros normalization
$x=s_0$ gives $\ell\ge\mu_\ell$ by FA.27.
Also $\|\mathbf c\|\le\sqrt{\delta+1/m}$ and
$\|\mathbf c'\|\le1/\sqrt m$, so $|\ell'|\le L_N$.
The nearest zero has angular distance
$\arcsin(\sqrt{q_+}/R_+)$. The source bounds imply
$\mu_\ell/(4L_N)<1/2$: for example use $\|N\|\ge\Delta A$,
JR.52 and the table in Proposition 74.1. Thus if
$\sqrt{q_+}\le\eta_*$, the inequality
$\arcsin v\le2v$ for $0\le v\le1/2$ shows that distance is
at most $\mu_\ell/(2L_N)$, giving $\ell\ge\mu_\ell/2$.
Outside that set $a_{\rm sp}q_+>a_{\rm sp}\eta_*^2$.
Using $q_-\le R_-^2$ in the two cases proves

$$
\ell(\phi)_++a_{\rm sp}q_+(\phi)\ge c_{\rm TV}q_-(\phi).
\tag{FA.30}
$$

All constants are positive: $z_f\ne0$, both $m_i>0$, both ellipse
axes are nonzero and $N\ne0$. For specificity, the conservative
whole-box integer evaluation in Proposition 74.1 gives
$0.00063684<\mu_\ell<0.00063686$,
$1.45280<L_N^{(F)}<1.45282$ and
$1.35\cdot10^{-10}<c_{\rm TV}^{(F)}<1.37\cdot10^{-10}$.
These evaluations again use the complete source box; they certify
positivity, not the root or a quantum implementation.

For an actual label with normalized direction $\phi$, coefficient
weight $p$ and failure coefficient $\beta$, its loss relative to the
separated spectral bound, divided by $p$, is

$$
D=\frac{|\ell|+\beta(a_{\rm sp}q_++b_{\rm sp}q_-)
 -|\ell+\beta(a_{\rm sp}q_+-b_{\rm sp}q_-)|}{2}.
$$

For $\ell\ge0$ this equals
$\min\{\ell+\beta a_{\rm sp}q_+,\beta b_{\rm sp}q_-\}$;
for $\ell<0$ it equals
$\min\{\beta a_{\rm sp}q_+,-\ell+\beta b_{\rm sp}q_-\}$.
Both give
$D\ge\frac{\beta}{1+\beta}
\min\{\ell_++a_{\rm sp}q_+,b_{\rm sp}q_-\}
\ge c_{\rm TV}\frac{\beta}{1+\beta}q_-$.
The identity $\sum p_j\beta_jn_jn_j^T=M$ whitens to
$\sum p_j\beta_jq_-(\phi_j)=1$. Since
$\beta_j\le t_A\mathfrak c_{\max}$,
$\sum p_jD_j\ge c_{\rm TV}/(1+t_A\mathfrak c_{\max})$.
The actual binary reports make this low Gram feasible for JR.58, so
$J_s-\sum p_j|\ell(\phi_j)|\ge0$.
Subtracting the actual TV from JR.59 is exactly half this live slack
plus $\sum p_jD_j$: the whitened positive/negative failure totals
are one each, so their separated absolute sum is $L_f$.
This proves FA.29 for every actual label distribution, without making
an analytic Kraus refinement readable or altering any history's error.
$\square$

**Theorem 74.3 (matching finite constructions for every fixed weak $s$).**
Let $B_\pm^{\rm sp}=M_2^{1/2}e_\pm e_\pm^TM_2^{1/2}$, extended by
zero on coordinate zero. Both first coordinates $(e_\pm)_1$ are
nonzero. Choose

$$
\begin{gathered}
r_\pm=\frac{dh_1}{bh_2}\sqrt{\frac{m_2}{m_1}}
 \frac{(e_\pm)_2}{(e_\pm)_1},\quad
\mathbf c_\pm=(\sqrt{\theta r_\pm^2+\omega},-r_\pm,1)^T,\\
a_0=\left(4\sum_\pm\mathbf c_\pm^TL_0^{-1}\mathbf c_\pm\right)^{-1},\qquad
\nu_* =\max_\pm\frac{m_1h_2^2(e_\pm)_1^2}
 {a_0d^2\mathfrak c(\mathbf c_\pm)}>0.
\tag{FA.31}
\end{gathered}
$$

Put $G=L_0^{1/2}NL_0^{1/2}$ and
$\varepsilon_0(s)=(1-s/s_0)/2$. Whenever
$t_A\ge\nu_*/\varepsilon_0(s)$, a finite actual instrument gives

$$
\mathcal T(s)-\mathcal T_A(s)\le
 \frac{\nu_*}{e^A-1}\left(\|G\|_1+\frac{2s}{s_0-s}\right).
\tag{FA.32}
$$

Together with FA.29 this proves

$$
\mathcal T(s)-\mathcal T_A(s)=\Theta(e^{-A})
\quad\text{for each fixed }0\le s<s_0.
\tag{FA.33}
$$

No optimal leading coefficient, uniform endpoint upper estimate or joint
$s\uparrow s_0,A\to\infty$ asymptotic follows from this assertion.

**Proof.** $z_f\ne0$ makes $t_f>0$, so neither first coordinate
vanishes. The displayed ratio ensures $n(\mathbf c_\pm)$ is parallel
to $M_2^{1/2}e_\pm$ with the correct signed ratio. For the two null
vectors,
$L_0-a_0\sum\mathbf c_\pm\mathbf c_\pm^T\succeq3L_0/4$:
whitening bounds the norm of the positive sum by its trace, exactly
$1/4$. Its $Q_0=\operatorname{diag}(1,-\theta,-\omega)$ trace is
zero. Reuse JR.60's support-restricted zero-Rayleigh decomposition
(IR Lemma 10.1) to decompose this remainder into at most three real
null atoms. This produces a fixed finite auxiliary low family with Gram
$L_0$ containing $\sqrt{a_0}\mathbf c_+$ and
$\sqrt{a_0}\mathbf c_-$. Assign fair binary reports to this family.

For fixed $s<s_0$ and $0<\varepsilon\le\varepsilon_0(s)$,
let $s'=s/(1-\varepsilon)<s_0$. Use an attained finite JR45 low
family at $s'$, scaled by $\sqrt{1-\varepsilon}$, and the auxiliary
family scaled by $\sqrt\varepsilon$. Retain every label separately,
keeping the principal reports. Attach the entire effects
$B_+^{\rm sp},B_-^{\rm sp}$ only to the two compatible auxiliary
labels, respectively. Relative to $n(\mathbf c_\pm)n(\mathbf c_\pm)^T$
the coefficient of $B_\pm^{\rm sp}$ is
$m_1h_2^2(e_\pm)_1^2/d^2$; FA.9 gives their activities
$\log(1+\nu_\pm/\varepsilon)$, with maximum
$\log(1+\nu_*/\varepsilon)$. All other low labels are pure live.
Add the same high pair and coherent complement. Fair reports on the
auxiliary labels can be generated by splitting each into two identical
proportional branches; both live and failure effects scale together,
so neither activity nor the full acquired TV changes. Contrast is at
least $(1-\varepsilon)s'=s$, and Theorem 75.1 supplies sharp cost
and all original output equalities.

For completeness the error in TV relative to the unbudgeted value at
$s'$ is at most $\varepsilon\|G\|_1$. Indeed the principal family's
absolute live sum is scaled by $1-\varepsilon$. On the two attached
labels reverse triangle bounds absolute total difference below by
absolute spectral failure difference minus absolute auxiliary live
difference. Other auxiliary labels are pure live. For any decomposition
of $L_0$, its absolute live sum is at most $\|G\|_1$: whiten its
coefficient projectors to a POVM and use
$|\operatorname{tr}(EG)|\le\operatorname{tr}(E|G|)$.
The two possible losses in the absolute sum are each at most
$\varepsilon\|G\|_1$; HALF their sum proves
$\operatorname{TV}_\varepsilon\ge\mathcal T(s')-
\varepsilon\|G\|_1$.

Mix a finite optimizer at $s$ with one at $s_0$, physically retaining
the independent mixing label, to reach contrast at least $s'$.
The common weak cost and output are unchanged. Mixing proportion
$\lambda=(s'-s)/(s_0-s)$ is in $[0,1]$ and gives
$\mathcal T(s)-\mathcal T(s')\le\lambda$, since TV lies in $[0,1]$.
As $\varepsilon\le1/2$, this is at most
$2s\varepsilon/(s_0-s)$, also zero at $s=0$.
Now choose $\varepsilon=\nu_*/t_A$ to obtain FA.32. The lower bound
FA.29 and the finite positive constants for this fixed $s$ give FA.33.
The growing upper constant near $s_0$ is retained, not suppressed.
$\square$

## 75. Complete outputs, original errors and the residual comparison

**Theorem 75.1 (simultaneous whole-output constructor).** Every finite
construction in §§70–74, except the explicitly different free completion
in Proposition 68.2, has the following full five-mode completion.
Fix isometries $W:\mathbb C^2\to V^\perp$ and
$J_0:\mathbb C^2\to\mathbb C^3$. Use one extra acquisition encoder
$W^\dagger$ into a jointly counted dimension-two fibre and its live
isometric decoder $EJ_0$, with rate zero; a fair report may be appended
and retained. Thus a complementary qubit is transmitted coherently.
For every complex $A\in M_5$ and Borel $B\subseteq[0,1]$, forgetting
acquisition labels gives

$$
\begin{aligned}
\Phi^L(A)&=E\left[\Lambda_*(E^\dagger AE)
 +J_0W^\dagger AWJ_0^\dagger\right]E^\dagger,\\
\Phi_\ell^f(A)(B)&=w_\ell\left(\int_Bg(t)dt\right)
 \operatorname{tr}(EME^\dagger A)P_f,
 \qquad\ell\in\{0,1,2,3,13\}.
\end{aligned}
\tag{FA.34}
$$

These identities hold after identity amplification by every passive
reference. In particular all twelve original individual errors are
preserved, with
$e_5=e_{27}=E_*$ and $e_{16}<71/484<37/250<E_*$ as in CG.143.
The maximum is $E_*$. The same construction has original contrast
inequality and sharp worst-history jointly counted cost, simultaneously
with every labelled Borel identity. The complement is free to choose
in the original class and is openly different from the fixed
certain-failure completion CA.10/CG.142.

**Proof.** On a low branch FA.11 gives encoder effect $K^\dagger K+N$.
Its full-fibre decoder is TP by FA.12–.13. A high branch has encoder
effect $H^\dagger H$ and TP live isometry on its whole three-dimensional
fibre. The low/high live coefficient Grams sum to $I_3$ in every
construction: $L_0+\operatorname{diag}(1-\delta,0,0)$ in the weak
regime, and $\operatorname{diag}(u^\dagger,v^\dagger,1)+
\operatorname{diag}(1-u^\dagger,1-v^\dagger,0)$ in the strong regime.
Consequently the sum of live conjugations is $\Lambda_*$ on every
complex matrix, by bilinearity of the coefficient Gram identity.
Its effect plus $M$ is exactly $I_3$ at the conditional root (CG.141).
The attached effects sum to $M$. After precomposition by $E^\dagger$
and addition of $W^\dagger$, the total encoder effect is
$E I_3 E^\dagger+WW^\dagger=I_5$.
Each positive encoder effect is bounded by this sum, proving branchwise
TNI rather than imposing it separately. All ranks/dimensions are whole
payload dimensions. Every other input-bearing dilation system is
permanently inaccessible before the acquisition cut.

Each low branch, after its chronological decoder, has supported live
matrix $K$ and separate failure map
$w_\ell g(t)\operatorname{tr}(N\,\cdot)P_f$.
Summing these maps and the high/complement live maps gives FA.34.
Cross operators between $V$ and $V^\perp$ have zero image in this
completion because the actual acquisition distinguishes those branches;
within the complementary block all complex qubit coherences are kept.
The equality is a finite Kraus identity on complex matrix units, not
merely on real states or twelve selected inputs. Its passive-reference
live map is explicitly

$$
\sum_{K=D,T,S}(EK E^\dagger\otimes I_R)X(EK^\dagger E^\dagger\otimes I_R)
 +(EJ_0W^\dagger\otimes I_R)X(WJ_0^\dagger E^\dagger\otimes I_R).
$$

For each failure label and every Borel $B$, its reference map is

$$
w_\ell\left(\int_Bg(t)dt\right)P_f\otimes
 \operatorname{Tr}_5[(EME^\dagger\otimes I_R)X].
$$

This is the conditional partial trace; using an unconditional reference
marginal would be a different map. The label $13$ is original index
$4$ in CG's five-entry weight vector; it is not a sixth label.
The maps for $0$ and $13$ are zero, separately, on every Borel set.
The other three labels remain separate; no singular component or extra
sector is present. Common fixed metadata are carried in their original
state.

All original inputs are in $V$, so FA.34 equals the CG.135 simulator
on each. Explicitly their four equal errors at height $y$ are

$$
e_y=\frac12\left[\|\Lambda_*(\rho_y)-B_y\|_1
 +\sum_\ell w_\ell\int_0^1
 |\operatorname{tr}(M\rho_y)g(t)-f_y(t)|dt\right].
$$

Covariance under $U_{e,n}$ gives the same value for all four signs.
Here $B_y$ is the ideal live matrix CG.111, not the scalar resource
coefficient JR.23. This is exactly the original full error expression,
so CG Theorem 15.2 gives the unequal height values stated above.
Neither failure probability, $\gamma_f$, nor a TV deficit is added
to these errors. The ideal density remains $f_y$, not $g$.

Only the high branches have dimension at least three; their effect is
$(1-u_s)D^\dagger D+(1-v_s)T^\dagger T$. Thus every original history
at height $y$ has high probability
$P_y(s)=(1-u_s)A_y+(1-v_s)B_y$, independent of signs.
It is maximized at $27$ and is $\mathsf C(s)$ by JR §§34–40.
The weak constructions have $u_s=\delta,v_s=1$; the strong construction
has the dagger parameters. The complement, although coherent and
counted as two, has probability zero on each original history.
The report identity is JR.29: each low branch contributes
$r xz$, no failure effect contributes a $01$ entry, and the high
contribution is as specified in the strong or weak construction.
It proves the original contrast inequality, with no constraint on
unrequested effect entries. Appending a common report coin while
retaining its parent label preserves TV, costs and activities, since
its probabilities multiply both height laws by the same kernel.

FA.13 generates first failures at actual times $6+t$ with the displayed
conditional maps. Only survivors receive terminal isometry; positive
survival is never converted into forced failure. The stopped carrier
has no later positive-carrier action. In Proposition 68.2 replace only
the high/complement part by its specified dimension-five coherent
encoder and decoder; its effect normalization, complex map and time
laws were computed there. On all supported inputs the same CG.135
maps remain, so all twelve errors, reports and costs just proved also
hold for that endpoint pair. These constructors prove conditional
mathematical attainments only. $\square$

**Proposition 75.2 (defined B14 comparison, residual and equality).**
The endpoint TV gain comparison called B14 is the published JR.157–.160
statement, also used with its actual-instrument qualification by RC
Theorem 65.2. Its exact dictionary is as follows. Put
$G=L_0^{1/2}NL_0^{1/2}=
\begin{psmallmatrix}g_0&X&Y\\X&g_1&Z\\Y&Z&g_2\end{psmallmatrix}$,
$\alpha=\alpha_0$, $\beta=\beta_0$, $\gamma=\alpha/\beta$ and
$f_G(u,v)=(1,u,v)G(1,u,v)^T$. Normalize every analytic low coefficient
atom as $\sqrt\pi(s_0,u,v)$. Its coefficient law satisfies

$$
\alpha u^2+\beta v^2=1,\quad
\mathbb E1=\mathbb Eu^2=\mathbb Ev^2=1,\quad
\mathbb Eu=\mathbb Ev=\mathbb Euv=0.
$$

The expectation is $\mathbb Eh=\sum_j\pi_jh(u_j,v_j)$, or its
stipulated coefficient integral; it is never a preparation prior or an
average conditioned on failure. Define

$$
\begin{gathered}
R_1=X-g_1-Z+\alpha(X+Y-g_0),\quad
R_2=Y-Z-g_2+\beta(X+Y-g_0),\\
B_\circ=f_G(-1,-1)=-(R_1+R_2),\quad
m_\circ=2(\gamma R_2-R_1),\\
P_\circ(u,v)=\frac{B_\circ}4(1-u)(1-v)
 +\frac{m_\circ}8(u^2-1),\qquad
\mathfrak r(u,v)=\min\{f_G(u,v),0\}-P_\circ(u,v),\\
T_0=\mathcal T(s_0).
\end{gathered}
$$

For every actual original sharp-cost weak instrument, including every
finite-activity competitor,
$T_{\rm instr}-T_0\le-\mathbb E\mathfrak r$.
Precisely, there is the nonnegative actual-information slack

$$
\begin{gathered}
\mathcal L_{\rm obs}=
\frac{(1-\delta)\Delta A+L_f+\mathbb E|f_G|}{2}-T_{\rm instr}\ge0,\\
T_{\rm instr}-T_0=-\mathbb E\mathfrak r-\mathcal L_{\rm obs}.
\end{gathered}
$$

Equality requires no loss in the physically generated refinement and
optimal spectral failure readout; hidden Kraus indices cannot certify
it. An actually generated separated atom refinement and the spectral
failure rows of JR53.3 attain equality in the unbudgeted class.
No finite-activity equality is inferred for those certain-failure rows.

**Proof.** The moment identities are the low Gram $L_0$ after scaling
its first coordinate to $s_0$ and using the real null equation. They
include all zero coordinates and both signs. They imply
$\mathbb Ef_G=\operatorname{tr}G$ and
$\mathbb EP_\circ=B_\circ/4$.
By JR.51 at $s_0$,
$T_0=((1-\delta)\Delta A+L_f+\operatorname{tr}G)/2-B_\circ/4$.
For an actual acquisition label, splitting its live/failure effect and
analytically resolving its Kraus products only upper-bounds its absolute
height difference. The high differences are positive and have the
fixed total $(1-\delta)\Delta A$. Whiten the failure subeffects to a
POVM on $\operatorname{ran}M$; its absolute height-difference sum is
at most $\|\Xi\|_1=L_f$. These two triangle/spectral inequalities
prove $\mathcal L_{\rm obs}\ge0$ for the actual record. Subtracting
$T_0$ and using $|f|=f-2\min(f,0)$ proves the exact slack identity
and B14's inequality.

The slack is a sum of nonnegative triangle and spectral slacks. Thus
it vanishes exactly when the actual record loses no resolved signed
height difference inside any grouped label and its induced failure
POVM is optimal for $\Xi$. Equivalently all nonzero scalar differences
combined inside each actual label have one sign, and the failure POVM
separates the positive and negative spectral supports (up to splitting
or zero effects). A generated refinement with the separated atom and
spectral labels supplies these conditions. Purely analytic refinement
of an existing instrument supplies only the upper bound, not its
missing record. Coordinate failure rows instead give $d_f<L_f$ and
lose $\gamma_f$ even at the same forgotten supported channel. The
finite-activity strong construction likewise exhibits the persistent
gap of FA.18. This proves both the equality conditions and the absence
of an unconditional equality claim. $\square$

## 76. Source correspondences and conditional boundaries

**Convention 76.1 (mathematical suppliers).** The additional
source-specific results FA.2–.34 and their actual-label bridges are
`repo-derived` ordinary conditional deductions. They do not assert
worldwide novelty. The following are reused suppliers and intermediate
mature tools, with exact scopes.

| Supplier at the immutable revision or fixed literature version | Correspondence used here |
| --- | --- |
| [CG, §§13–17,21][CG] | CG.111–.117, .134, .141–.143, .155–.166, .179–.183: root box, source amplitudes, normalization, all twelve errors, full-class minimax/support certificate, actual-cut and measurable extension premises. No new root or minimax certification is claimed. |
| [JR, §§34–40][JR] | JR.20–.42: original contrast inequality, jointly counted worst-history sharp cost, $v_s,u_s$, reports and common high branches. These results concern the original class, not a fixed-effects substitute. |
| [JR, §§42–45][JR] | JR.44–.48: every-optimizer supported rigidity; JR.49–.53: strong TV and signs; JR.58–.61: weak finite live optimization, compact attainment and support-rank null decomposition. The general unbudgeted weak value is reused, not re-proved. |
| [JR, §55][JR] and [RC, §65][RC] | JR.155, .157–.160 and RC.60–.62 supply the exact B14 normalized residual/averaging comparison. Proposition 75.2 defines every symbol and retains its actual-information slack. |
| [RC, §§58–66][RC] | Complete static residual/contact curve and its own conditional premises. Its normalization is $L=\operatorname{diag}(s_0,1,1)$; $L^2=L_0$, $\chi=\omega/\delta=\beta_0$, $\tau=s/s_0$. Its entire static curve and contact/rank transition stay settled at that supplied conditional scope. No static support cardinality is transferred to finite-budget optimizers. |
| [CA, Lemma 3.1 and Theorem 5.1][CA] | CA.14–.15 excludes nonzero rank-one directions; CA.21 gives the real exposed null face after complex equality. CA.10's prescribed completion and CA.11's full binary effects are not the original comparison class. |
| [IR, Lemmas 4.2 and 10.1][IR] | IR.19–.22 fixed-image compression, IR.57–.58 zero-Rayleigh decomposition, with JR.60's restriction to the support for singular/rank-zero cases. They are intermediate tools in the auxiliary construction. |
| [OC, §5.2][OC] | OC.14–.19c supplies an ideal chronological stopped-instrument framework with its own all-prefix hypotheses. Its geometric control predicates are not acquisition/actuator permissions and do not impose a Schur-only menu. |
| [Coppola–Karevski–Landi, arXiv:2311.05515v1, §II][CKL] | `literature-attested`: no-jump evolution and first-jump/survival calculus, II.3–II.11 and II.17–II.21. It does not supply the prescribed-path minimization or a unit-total finite-deadline failure with positive survival. |
| [Yang–Xie, arXiv:1605.02431v2, §II, Theorem 1][YX] | `literature-attested`: PSD Toeplitz Vandermonde decomposition, including full rank. Uniqueness is restricted to rank-deficient cases and is unused. The eight-block equivalence and actual original instrument correspondence are proved here. |
| [Leppäjärvi–Sedlák, arXiv:2212.11225v2, §§6.1–6.3][LS] | `literature-attested`: Definition 7 postprocessing, Definition 8/Eq.6 dilation, Remark 3 and Proposition 7 compatibility. These are finite-dimensional common-instrument tools, not automatic continuous-time/native bridges. |
| [Sekatski, arXiv:2608.25010v1, §II.1, Eq.2][SEK] | `literature-attested`: Kraus rank/image compression and Schmidt-number correspondence. It grants neither readable discarded flags nor this state-dependent cost, clock law or finite-budget frontier. |

**Definition 76.2 (remaining original scope).** All native services are
`ASSUMED-UNVERIFIED`: lawful acquisition of the sole unknown reached-cut
specimen; D/T/S calibration and controlled encoding/decoding; coherent
joint storage of every later-accessible input-bearing share at the same
cut; one aligned clock including acquisition duration; actual FIRST
absorbing events at $6+t$; terminal live controls with no forced failure;
and original stopped archive, source/epoch, controller and permission
semantics. A fixed matrix, abstract dilation, TP control or permanently
discarded mathematical environment is not a supply of these services.
The probability-changing noncommuting controls cited in JR47 also
remain admitted possibilities; a diagonal or Schur menu is not exhaustive.

The remaining finite-budget mathematical evaluation is the complete weak
scalar $(s,A)$ frontier and threshold values, its contact/optimizer
structure and optimal weak leading coefficient, and joint or uniform
endpoint limits. FA.20 and $t_{\min}$ are exact finite characterizations
and attained bounds, not their scalar evaluation. The static residual
curve already supplied by RC is retained, including its contact/rank
transition; its optimal support pattern need not survive a finite activity
constraint. Full original native/joint-height/clock and broader programme
requirements remain. These conditional finite mathematical results do not
assert completion of the continuing quantum-first programme.

[CG]: https://github.com/the-omega-institute/trureturing/blob/e35db6260a4bd66b11e6b36cbece55650c937e70/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: https://github.com/the-omega-institute/trureturing/blob/e35db6260a4bd66b11e6b36cbece55650c937e70/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[RC]: https://github.com/the-omega-institute/trureturing/blob/e35db6260a4bd66b11e6b36cbece55650c937e70/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md
[CA]: https://github.com/the-omega-institute/trureturing/blob/e35db6260a4bd66b11e6b36cbece55650c937e70/docs/develop/theory/FIB_NATIVE_COMPLEX_ATOMIC_CONE_AND_OPTIMAL_RESOURCE_FACES.md
[IR]: https://github.com/the-omega-institute/trureturing/blob/e35db6260a4bd66b11e6b36cbece55650c937e70/docs/develop/theory/FIB_NATIVE_INTERIOR_RECORD_RESOURCE_REDUCTION.md
[OC]: https://github.com/the-omega-institute/trureturing/blob/e35db6260a4bd66b11e6b36cbece55650c937e70/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md
[CKL]: https://arxiv.org/html/2311.05515v1
[YX]: https://arxiv.org/html/1605.02431v2
[LS]: https://arxiv.org/html/2212.11225v2
[SEK]: https://arxiv.org/html/2608.25010v1

## 追加锚（本行以下为增补区）

## 77. Joint allocation dictionary for the finite activity boundary

**Convention 77.1 (suppliers and comparison class).** Sections 77–86 use
Definition 67.2 without changing the experiment or its comparison class.
The source and minimax premises are [CG, §§13–17][CG42], in the
*Complete continuation distinguishability gap*, with the coefficients of
CA.7–.9 and the original sharp-cost equality data JR.34–.47. The root,
isolation, Jacobian, ranks, normalization and minimax identification remain
inherited conditional premises. A source-box inequality does not certify
any of those premises. The statements here are ordinary conditional
mathematics, without Lean/kernel or native certification.

The path minimum, arbitrary-Kraus double rigidity, capacity and
whole-fibre realization are Theorems 68.1, 69.1–69.2 and Proposition
70.1. The strong value and weak moment representation are Theorems
71.1–71.3 and 72.1. The fixed-strength two-sided deficit bounds are
Theorems 74.2–74.3. These are suppliers, not additional new results below.
RC supplies the complete static residual/contact curve; RH supplies its
static actual-label minima. All uses retain their exact hypotheses.

The published [WE, §§1–6][WE906] uses these same conditional source
operators and exactly Definition 67.2's original comparison class. Its
endpoint constant and universal critical full-record law are reused
below. Its scalar reduction is for feasibility only: generating balanced
sign labels preserves the scalar moments, but need not preserve the TV
of an existing actual record. No TV-preserving symmetrization is assumed.

The published [JS, §§1–9][JSce3], *Joint endpoint records: the evaluated
finite-activity saturation boundary*, supplies the full prescribed
finite-product joint limit, exact finite moment repair and whole-fibre
recovery, explicit spectral saturation boundary with its equality cases,
and continuous strictly increasing middle transition. Its critical
every-instrument law credits WE. These are used as published suppliers,
with the same conditional CG antecedents, all-complex/multi-Kraus
competitors, original contrast inequality, sharp acquired joint cost,
whole-fibre activity and full-record objective. Their finite-product
scope does not include an infinite-product theorem or evaluate the
strict-interior scalar crossover. The correspondences below retain the
additional entire-threshold, boundary-height, coefficient and label
questions of this volume.

Write $a,b,c,d$ for the amplitudes called $a_K,b_K,c_K,d_K$ in RH,
and $a_{\rm src},b_{\rm src},c_{\rm src},d_{\rm src}$ in RC. Put

$$
\begin{gathered}
\alpha=\theta/\delta=\alpha_0,\quad \beta=\omega/\delta=\beta_0,
\quad L=\operatorname{diag}(s_0,1,1),\quad L^2=L_0,\\
Q=\operatorname{diag}(1,-\alpha,-\beta),\quad
Q_0=\operatorname{diag}(1,-\theta,-\omega),\quad
h=(1,z,w)^T,\quad \mathbf c=Lh=(s_0,z,w)^T,\\
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\quad
(K_0,K_1,K_2)=(D,T,S),\quad G=LNL,\\
\ell(\mathbf c)=\mathbf c^TN\mathbf c=h^TGh,\quad
f(\mathbf c)=n(\mathbf c)^T\Delta n(\mathbf c),\quad H_0=(1-\delta)\Delta A.
\tag{FA.35}
\end{gathered}
$$

Thus $G$ is RC.2–.3's normalized height matrix. In all uses of $L$ in
this dictionary it is a coefficient normalization, not a decoder live
effect. When Theorem 68.1 is invoked, denote its terminal live map by
$\mathcal L_{\rm dec}$ and its effect by
$L_{\rm dec}=\mathcal L_{\rm dec}^{\dagger}(I)=S(1)\succ0$.
That effect identity is part of its prescribed-law hypothesis.

On the physical failure support, coordinates $(1,2)$, define

$$
\begin{gathered}
M_2=\operatorname{diag}(m_1,m_2),\quad
\Xi=M_2^{1/2}\Delta_{\{1,2\}}M_2^{1/2}
 =\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},\\
d_f=11m_1/64>0,\quad
z_f=\sqrt{m_1m_2}\Delta_{12}<0,\quad
L_f=\|\Xi\|_1=\sqrt{d_f^2+4z_f^2},\\
\lambda_-=-\frac{L_f+d_f}{2},\quad
\lambda_+=\frac{L_f-d_f}{2},\quad
\Xi e_\epsilon=\lambda_\epsilon e_\epsilon,\quad
B_\epsilon^{\rm sp}=M_2^{1/2}e_\epsilon e_\epsilon^TM_2^{1/2}.
\tag{FA.36}
\end{gathered}
$$

Here $e_\pm$ are the unit vectors of Proposition 74.1, and the physical
$B_\epsilon^{\rm sp}$ are extended by zero in coordinate zero. A failure
effect is whitened by $M_2^{-1/2}$; a physical spectral effect is obtained
by multiplying an eigenprojector by $M_2^{1/2}$ on both sides. In
particular the compatible physical direction is $M_2^{1/2}e_\epsilon$,
not $e_\epsilon$ alone. For example the readout coordinates are
$q_\epsilon(\mathbf c)=|e_\epsilon^TM_2^{-1/2}n(\mathbf c)|^2$.

The complete correspondence with WE.6–.8 and WE.44 is:

| WE symbol | Symbol and meaning here |
| --- | --- |
| $D,T,S,M,\theta,\omega,\delta,s_0,\alpha,\beta$ | The identical source operators and coefficients; $\kappa=h_0a+h_1b$ is the same report normalization. |
| $U,V,W,\mu,r,k$ | $u_m,V_f,W_f,\mu_f,u_f,\sqrt{u_f}$ of FA.38; WE's $W$ is a scalar failure moment, not the complementary isometry. |
| Radial $x$, $w_2(x)$ | $u=z^2$, $(1-\alpha u)/\beta=w^2$; neither is an original height or an elapsed time. |
| $D_c(x),N_c(x),c_*(x)$ | $C_c+D_cu,A_c+B_cu,c_*(u)$ of FA.38. |
| $B_*,C_{\rm end}$ | $\nu=\mu_f/c_f$, $\kappa_0=\nu(1-\sqrt{u_f})^2/2$. |
| $q=1-s/s_0$ | $q_{\rm end}=1-\tau$ in comparisons with WE; FA.43's local $q=\nu/t$ is instead a live coefficient mass. |
| $N,L,G,f(z,w),h(z,w),H(x)$ | $N,L,G,\ell(\mathbf c),f(\mathbf c),d(\mathbf c)$, respectively, with $\mathbf c=(s_0,z,w)$. |
| $d_f,z_f,L_f,\gamma_f,H_\Delta,T_0$ | The identical FA.36 spectral data, $(L_f-d_f)/2,H_0,\mathcal T(s_0)$. |

Thus the physical failure whitening, the full generated-record law and
the capacity domain coincide. WE's prescribed recovery uses FA70/75's
same free coherent completion and FIRST clock; neither its feasibility
reduction nor this dictionary identifies arbitrary full-$M_5$ completions.

The complete JS correspondence used in §81 is:

| JS symbol or object | Symbol and meaning here |
| --- | --- |
| $D,T,S,M,E,\rho_{y,e,n},\Delta,\kappa$, JS.1–.6 | The identical source, twelve specimens, HALF stopped-cq error and report normalization of §§67,77; JS Definition 1.2 is exactly Definition 67.2, including its stipulated extensions. |
| $U,V,W,\mu,r$, JS.6 | $u_m,V_f,W_f,\mu_f,u_f$ of FA.38; JS's radial mean $r=V/\mu$ is **not** its spectral scalar named $u_f$ in JS.38. |
| $x,Y(x),H(x),c_*(x),F_c(x)$, JS.7 | $u=z^2,w^2=(1-\alpha u)/\beta,d(\mathbf c),c_*(u),d(\mathbf c)/\mathfrak c(\mathbf c)$; JS's elapsed $u$ instead means the time variable of FA.13. |
| $N,L,G,h,K(z,w),n(z,w)$, JS.8 | FA.35's $N,L,G,h,K(\mathbf c),n(\mathbf c)$ with $\mathbf c=Lh=(s_0,z,w)$; $L$ is coefficient normalization, not $L_{\rm dec}$. |
| $f(z,w),k(z,w)$, JS.8 | $\ell(\mathbf c),f(\mathbf c)$, respectively: live height and failure height must not be interchanged. |
| $\pi_j,v_j,P,\nu$, JS.9–.12 | $p_j,b_j,p,\sigma$ with $d\sigma=b_jdp$; $\nu$ in FA.38 is instead the scalar $\mu_f/c_f$. Each existing label retains its own $b_j$ in the actual absolute-value objective. |
| $q,t,\lambda$, JS.11,.20,.35 | $q_{\rm end}=1-\tau,t=e^A-1,\zeta=\lim t q_{\rm end}$; JS's $q$ is not FA.43's coefficient mass $q=\nu/t$. |
| $H_{\rm live},S_{\rm corner},T_0,B_0$ | $H_0,j(1)=\tfrac14\sum_{\sigma,\upsilon}|\ell(s_0,\sigma,\upsilon)|,\mathcal T(s_0),\mathcal T(s_0)-\gamma_f$. |
| $C_{\rm end},\Phi(\lambda)$, JS.20 | $\kappa_0,(F_{\rm lim}(\zeta)-d_f)/2$, on the identical covariance and cost domain, including both axes. |
| Spectral $u_f,e_\pm$, JS.38,.41 | $t_f=-2z_f/(d_f+L_f)$ and FA.36's $e_\pm$; this $t_f$ differs from the radial $u_f=V_f/\mu_f$. |
| $a_e,(z_e,w_e)$, JS.42 | $b_\epsilon=a_e$ and $\mathbf c_\epsilon=(s_0,z_e,w_e)$ of FA.59, so $B_\epsilon^{\rm sp}=a_e n(\mathbf c_\epsilon)n(\mathbf c_\epsilon)^T$. |
| $C_{\rm sat}$, JS.38–.43 | $\zeta_{\rm sp}$ of FA.59, including equality at the threshold and the unique total cost of every spectral-optimal failure measure. |
| Rare atom $a_i$, JS.23–.27 | Failure mass $a_i$ at $\mathbf c_i$; actual live weight $p_i=a_i/[t\mathfrak c(\mathbf c_i)]$ and effect $N_i=a_i n_i n_i^T$. The repair matrix is $\mathsf U=\int hh^T/\mathfrak c\,d\sigma$, not the scalar endpoint $u_m$. |
| Four pure repair labels, JS.24–.27 | Exact residual live Gram $I-\mathsf U/t$ in $h$ coordinates, positive weights and squared coordinates for all large $t$, with normalized contrast deficit $e_t=C_\sigma/t+O(t^{-2})$, $C_\sigma=\int d/\mathfrak c\,d\sigma$. |
| JS.30–.34 and Theorem 6.1 | FA.11–.13,.34 and §86: identical whole-qubit factorization, five separate Borel maps, conditional passive-reference trace, free coherent counted complement and FIRST clock. |

In particular $\int f(\mathbf c)d\sigma=\operatorname{tr}(M\Delta)
=-d_f$, so $\int|f|d\sigma=d_f+2\int f_+d\sigma$ on this
whole feasible set. This establishes the objective correspondence, not
just a match of threshold numbers. JS.36–.37 supplies finite strict
contrast margins along every prescribed finite product sequence, even
when the limiting cost is saturated; its construction counts are upper
counts, not the minimum LOW-live-bearing counts of §§82–84.

**Definition 77.2 (actual labels and moment coordinates).** Let
$n_{\rm feas}(s,A)$ be the minimum number of actual low live-bearing
labels in $\mathfrak F_{s,A}$, and $n_{\rm opt}(s,A)$ the minimum among
its height maximizers. They are undefined for the empty class.
A supported-nonzero low label has an entire two-dimensional joint
fibre and one effective supported live product by Theorem 69.1.
At finite activity no supported-nonzero label is failure-only. Normalize
its data as

$$
K_j=\sqrt{p_j}K(s_0,z_j,w_j),\qquad
N_j=p_jb_j n_jn_j^T,\qquad
\alpha z_j^2+\beta w_j^2=1,\quad p_j>0.
$$

The following is the coordinate form of FA.8 and FA.20, used throughout:

$$
\begin{gathered}
\sum_jp_jh_jh_j^T=I_3,\qquad
0\le b_j\le t\mathfrak c(\mathbf c_j),\qquad t=e^A-1,\\
\sum_jp_jb_jz_j^2=V_f,\quad
\sum_jp_jb_jw_j^2=W_f,\quad
\sum_jp_jb_jz_jw_j=0,\\
V_f=\frac{m_2h_1^2}{b^2},\quad W_f=\frac{m_1h_2^2}{d^2},\quad
\mu_f=\alpha V_f+\beta W_f=\sum_jp_jb_j,\\
\tau=s/s_0\le\sum_jp_j|z_j|,\qquad
T_{\rm actual}=\frac{H_0+\sum_jp_j|\ell(\mathbf c_j)+b_jf(\mathbf c_j)|}{2}.
\tag{FA.37}
\end{gathered}
$$

The last equality uses the fixed positive weak high contribution. For
necessity, the available contrast bounds the requested one; for
sufficiency choose the actual report $\operatorname{sgn}z_j$, either
sign at zero. No extra acquired label is needed for that report.
Every finite family satisfying these moments has the common realization
specified in §86. Arbitrary competing time laws have not been fixed to
$g(t)$ in deriving them. Integrals replace sums only in the stipulated
extensions of Convention 67.1.

The $p_j$ are coefficient weights, not source priors or acquisition
probabilities. The latter are
$\operatorname{tr}(E(K_j^\dagger K_j+N_j)E^\dagger\rho)$.
These low-label counts differ from hidden Kraus multiplicity, static
support/rank, total actual alphabet, five terminal failure labels and
joint quantum dimension. A supported-zero complementary qubit does not
enter these counts; its entire fibre still obeys the activity bound.
A positive nonatomic live-bearing record has infinitely many actual
labels; an unacquired integration variable cannot control a decoder.

## 78. Entire scalar feasibility and the common activity floor

**Definition 78.1 (capacity as a scalar function).** For $0\le u\le u_m=1/\alpha$
put

$$
\begin{gathered}
c_*(u)=\mathfrak c\left(s_0,\sqrt u,
 \sqrt{(1-\alpha u)/\beta}\right)
       =\frac{A_c+B_cu}{C_c+D_cu},\\
A_c=h_1^2h_2^2\delta+c^2h_1^2/\beta,\quad
B_c=a^2h_2^2-c^2h_1^2\alpha/\beta,\\
C_c=h_0^2\delta+d^2/\beta,\quad
D_c=b^2-d^2\alpha/\beta,\quad E_c=B_cC_c-A_cD_c,\\
u_f=V_f/\mu_f,\quad c_f=c_*(u_f),\quad
\nu=\mu_f/c_f,\quad q_m=\mu_f/W_f,\quad t_0=W_f/c_f=\nu/q_m,\\
\tau_* =q_m\sqrt{u_f}+\sqrt{(1-q_m)(1-q_mu_f)}.
\tag{FA.38}
\end{gathered}
$$

The variable $u$ here is $z^2$, not a strong-regime coefficient $u_s$.
All denominators are positive. At the conditional source
$0<u_f<1<u_m$, $0<q_m<1$, $B_c>0$, $D_c<0$ and $E_c>0$.

**Lemma 78.2 (strict convexity on the entire scalar domain).** Set
$w_c=1/c_*$. The function $(u_m-u)w_c(u)$ is strictly convex on
$[0,u_m]$. For every $1\le r\le\sqrt{u_m}$ the function

$$
h_r(u)=(\sqrt u-r)^2w_c(u)
\tag{FA.39}
$$

is strictly convex on that same closed interval.

**Proof.** Direct differentiation gives
$w_c'=-E_c/(A_c+B_cu)^2$,
$w_c''=2B_cE_c/(A_c+B_cu)^3$ and

$$
[(u_m-u)w_c]''=
 \frac{2E_c(A_c+B_cu_m)}{(A_c+B_cu)^3}>0.
$$

For $g=(\sqrt u-r)^2$, one has $g''=r/(2u^{3/2})$ for $u>0$.
When $u\le r^2$, every term in
$h_r''=g''w_c+2g'w_c'+gw_c''$ is nonnegative and the first is
positive. When $u>r^2$, bound it below by

$$
\frac{\min w_c}{2u_m^{3/2}}
 -2(1-1/\sqrt{u_m})\frac{E_c}{A_c^2}>1.942-1.639>0.
\tag{FA.40}
$$

The strict rational margins follow on the whole inherited JR.52 amplitude
box. They can be reproduced by taking its seven intervals
$[N_i,N_i+1]/10^6$, using
$m_1=1-h_1^2-a^2$, $m_2=1-h_2^2-c^2$, and substituting into FA.38.
These equalities identify the expressions at the source root only.
Rational endpoint arithmetic with square roots enclosed at denominator
$2^{128}$ gives

| Expression | Strict lower bound | Strict upper bound |
| --- | --- | --- |
| $u_f$ | $.7226$ | $.7228$ |
| $u_m$ | $1.1392$ | $1.1394$ |
| $B_c$ | $.001965$ | $.001967$ |
| $D_c$ | $-.048734$ | $-.048720$ |
| $E_c$ | $.0004846$ | $.0004849$ |
| $\min w_c/(2u_m^{3/2})$ | $1.942$ | $1.946$ |
| $2(1-1/\sqrt{u_m})E_c/A_c^2$ | $1.635$ | $1.639$ |
| $\tau_*$ | $.99448$ | $.99499$ |

For example $\min w_c=w_c(u_m)$ since $w_c'<0$. The interval
operations are ordinary outward rational sums/products/quotients and
$[\lfloor 2^{128}\sqrt a\rfloor,\lceil2^{128}\sqrt b\rceil]/2^{128}$
for a nonnegative interval $[a,b]$. Thus the displayed comparisons are
whole-box inequalities, not sampled root or TP certificates. Continuity
at zero and strict positivity on the interior prove strict convexity on
the closed interval, including its square-root endpoint. $\square$

**Theorem 78.3 (evaluated scalar feasibility).** For $0\le s<s_0$ the
entire exact threshold is

$$
 t_{\min}(s)=
 \begin{cases}
 t_0,&0\le\tau\le\tau_*,\\
 \displaystyle\nu\frac{1+u_f-2\tau\sqrt{u_f}}{1-\tau^2},
       &\tau_*<\tau<1.
 \end{cases}
\qquad
\mathfrak F_{s,A}\ne\varnothing
 \Longleftrightarrow A\ge\log(1+t_{\min}(s)).
\tag{FA.41}
$$

Every threshold is attained. In the remaining original scalar domain
$s\in[s_0,1]$, Theorem 71.1 gives exactly the isolated point
$s=s^\dagger$, $A\ge\log(1+t_0)$, since

$$
v^\dagger=V_f/W_f,\quad
u^\dagger=\theta v^\dagger+\omega=\delta\mu_f/W_f,\quad
\mathfrak c_\dagger=c_f,\quad \nu_\dagger=t_0.
\tag{FA.42}
$$

Here and in every strong formula the substitution is explicitly
$(u,v)=(u^\dagger,v^\dagger)$. The strong $s^\dagger$ is distinct
from the static weak contact $s_\dagger=s_0\tau_\dagger$.
In particular $A=0$, $s=s_0$ and $s=1$ are infeasible at finite
budget; $s=0$ has the positive attained threshold $\log(1+t_0)$.

For comparison with WE Theorem 4.1, on the rising branch write
$q_{\rm end}=1-\tau$. The same exact threshold becomes

$$
t_{\min}(s)=\frac{\kappa_0}{q_{\rm end}}
 +\frac{\nu(1+\sqrt{u_f})^2}{2(2-q_{\rm end})},
\qquad 0<q_{\rm end}\le1-\tau_*.
$$

WE.29 has $p_{\rm cap}=q_m/2$ and
$q_0=1-p_{\rm cap}\sqrt{u_f}
-\sqrt{(1-p_{\rm cap})(1-p_{\rm cap}u_f)}<1-\tau_*$.
Its exact recovery expression WE.30 is therefore this threshold on
$0<q_{\rm end}\le q_0$. WE supplies that restricted recovery and its
endpoint constant, rather than the entire threshold claim. FA.41 also
covers the rest of the rising branch and the attained floor, using the
global convexity of Lemma 78.2.

**Proof.** Use FA.37. Let $p$ be its coefficient probability measure,
$u=z^2$, and let $d\lambda=b_jdp/\mu_f$ be the failure-weighted
probability measure. Its mean $u$ is $u_f$. Capacity makes the measure
$d\pi_{\rm cap}=\mu_fw_c(u)d\lambda/t$ dominated by $p$. Since
$\int(u_m-u)dp=u_m-1$, strict Jensen gives

$$
u_m-1\ge\frac{\mu_f}{t}\int(u_m-u)w_c(u)d\lambda
 \ge\frac{\nu}{t}(u_m-u_f).
$$

Thus $t\ge\nu(u_m-u_f)/(u_m-1)=W_f/c_f=t_0$.
The last identity follows by substituting
$u_f=V_f/\mu_f$, $\mu_f=\alpha V_f+\beta W_f$.
No zero-budget division is needed, since FA.8 already excludes $t=0$.

For $t\ge t_0$ let

$$
q=\nu/t,\qquad u_R=\frac{1-qu_f}{1-q},\qquad r=\sqrt{u_R}.
\tag{FA.43}
$$

Then $0<q\le q_m<1$ and $1<r\le\sqrt{u_m}$. Write
$P=\int d(p-\pi_{\rm cap})$ and
$Q'=\int u\,d(p-\pi_{\rm cap})$. Cauchy–Schwarz and
$\sqrt{PQ'}\le(rP+Q'/r)/2$ imply

$$
\begin{aligned}
\int\sqrt u\,dp
&\le\frac{r+1/r}{2}
 -\frac{\mu_f}{2rt}\int h_r(u)d\lambda\\
&\le q\sqrt{u_f}+\sqrt{(1-q)(1-qu_f)}=:\tau_{\max}(t).
\end{aligned}
\tag{FA.44}
$$

The second inequality is strict Jensen from Lemma 78.2. This is a
universal necessity for the original class, independent of its prescribed
failure-time laws or inaccessible Kraus decomposition.

For equality, put saturated mass $q$ at
$(s_0,\pm\sqrt{u_f},\pm\sqrt{v_f})$,
$v_f=(1-\alpha u_f)/\beta=W_f/\mu_f$, with equal four sign weights
and failure ratio $b=t c_f$. Put pure-live mass $1-q$ at
$(s_0,\pm\sqrt{u_R},\pm\sqrt{v_R})$,
$v_R=(1-\alpha u_R)/\beta$, also sign-balanced. These data have live
Gram $L_0$, failure sum $M$, and available contrast
$s_0\tau_{\max}(t)$. At $t=t_0$ one has $v_R=0$ and the duplicate
signs are merged. Section 86 realizes this same finite family with all
original outputs and cost. It satisfies every smaller requested contrast
as an inequality. The function $\tau_{\max}$ is strictly increasing
from $\tau_*$ to $1$ for $t\ge t_0$. Solving FA.44 for $q$ on that
range gives
$q=(1-\tau^2)/(1+u_f-2\tau\sqrt{u_f})$ and proves FA.41,
including the join and attainment.

Finally $(\sqrt{u^\dagger},\sqrt{v^\dagger},1)$ is the scalar multiple
$\sqrt{\mu_f/W_f}(s_0,\sqrt{u_f},\sqrt{v_f})$.
Capacity is homogeneous of degree zero, proving FA.42. Theorem 71.1
then supplies the rest of the original domain without a new strong-regime
proof. $\square$

## 79. Evaluated height on the entire weak minimum-budget boundary

**Theorem 79.1 (finite absolute-value boundary formula).** Consider either
$t=t_0$, $0\le\tau\le\tau_*$, or $t>t_0$,
$\tau=\tau_{\max}(t)$. These are precisely all weak points with
$A=A_{\min}(s)$. Use $q,u_R,v_f,v_R$ from FA.43–.44 and put
$u_F=u_f$, $v_F=v_f$. For $i=F,R$ define

$$
\begin{gathered}
\mathbf c_{i\sigma\upsilon}=(s_0,\sigma\sqrt{u_i},
 \upsilon\sqrt{v_i}),\quad \sigma,\upsilon\in\{\pm1\},\\
L_{F\sigma\upsilon}
 =|\ell(\mathbf c_{F\sigma\upsilon})+tc_f f(\mathbf c_{F\sigma\upsilon})|,
\quad L_{R\sigma\upsilon}=|\ell(\mathbf c_{R\sigma\upsilon})|,\\
M_i=\tfrac14\sum L_{i\sigma\upsilon},\quad
Z_i=\tfrac14\sum\sigma L_{i\sigma\upsilon},\quad
Y_i=\tfrac14\sum\upsilon L_{i\sigma\upsilon},\\
k_z=\frac{q\sqrt{u_f}}{(1-q)\sqrt{u_R}},\quad
B_z=q\left(Z_F-\sqrt{u_f/u_R}Z_R\right).
\tag{FA.45}
\end{gathered}
$$

For $t>t_0$, also put
$k_w=q\sqrt{v_f}/((1-q)\sqrt{v_R})$ and
$B_w=q(Y_F-\sqrt{v_f/v_R}Y_R)$. Then

$$
\begin{gathered}
\mathcal T_A(s)=\frac{H_0+qM_F+(1-q)M_R+P_{\rm bd}}2,\\
P_{\rm bd}=
\begin{cases}
|B_z|,&t=t_0,\\
\max\{|B_z|,|B_w|\},&t>t_0,\ k_w\le1,\\
\displaystyle\max\left\{|B_z|,\frac{|B_w|}{k_w},
 \frac{|B_z|(k_w-1)+|B_w|(1-k_z)}{k_w-k_z}\right\},
 &t>t_0,\ k_w>1.
\end{cases}
\tag{FA.46}
\end{gathered}
$$

All these are evaluated finite scalar expressions and are attained. They
include both polygon regimes, the whole floor segment and its join,
zero signed differences, ties, and vanishing optimal branch weights.

**Proof.** Equality in the floor Jensen bound forces failure-carrying
labels to $u=u_f$, saturated with $b=tc_f$, and remaining labels to
$u=u_m$. For $t>t_0$, equality in FA.44 forces the first family to
$u_f$ and the residual family to $u_R$: strict convexity fixes the
failure mean, and residual Cauchy equality fixes its $u$. Since
$u_f<1<u_R$, residual mass cannot remain on the failure direction;
hence that direction is saturated. These conclusions are forced on
all supported actual labels, up to proportional subdivision, not just
on the sign-balanced witness.

Zero failure off-diagonal forces the $\sigma\upsilon$ moment in the
first family to vanish. For $v_R>0$, the total live $zw$ moment then
forces it in the second family too. The general merged-ray weights are
therefore

$$
p^F_{\sigma\upsilon}=\frac q4(1+\sigma X+\upsilon Y),\quad
p^R_{\sigma\upsilon}=\frac{1-q}{4}
 (1-\sigma k_zX-\upsilon k_wY).
\tag{FA.47}
$$

The remaining live cross moments give exactly these $k_z,k_w$.
Positivity is precisely
$|X|+|Y|\le1$, $k_z|X|+k_w|Y|\le1$.
One has $k_z<1$: its squared inequality is
$q u_f<1-q$, which follows throughout $q\le q_m$ from FA.38
and the source bounds. The objective's nonconstant part is
$B_zX+B_wY$. Choose their signs to agree, and maximize on the
intersection of the two first-quadrant triangles. If $k_w\le1$,
the relevant vertices are $(1,0),(0,1)$. If $k_w>1$, they are
$(1,0),(0,1/k_w)$ and
$((k_w-1)/(k_w-k_z),(1-k_z)/(k_w-k_z))$.
Their objective values give FA.46. Zero coefficients permit either
sign; ties permit any maximizing edge. Zero weights are omitted.

At $t=t_0$, $v_R=0$ and its two $\upsilon$ directions coincide.
The live $w$ moment forces $Y=0$; there is no division by $v_R$.
The weights become
$q(1+\sigma X)/4$ and $(1-q)(1-\sigma k_zX)/2$ on the two pure
rays, with $-1\le X\le1$. This gives $P_{\rm bd}=|B_z|$ and is
also the collapsed limit of the polygon formulation. Absolute values
in FA.45 are taken before multiplication by the weights, so a zero
height difference causes no missing branch or sign assumption.

A maximizing vertex gives a nonnegative finite family in FA.37 with
contrast $s_0\tau_{\max}(t)$, hence the required inequality, and the
common construction in §86. Proportional subdivisions of a fixed
saturated or pure ray preserve its absolute-difference sum. Thus the
universal equality class just derived has no additional record advantage,
and the displayed maximum is the original-class value. This theorem
does not evaluate height at weak points strictly above their minimum
budget. $\square$

## 80. Existence of the fixed-strength coefficient and its static-dual bound

**Theorem 80.1 (positive finite coefficient for every fixed real strength).**
For each fixed real $0\le s<s_0$, the limit

$$
K(s)=\lim_{A\to\infty}e^A[\mathcal T(s)-\mathcal T_A(s)]
\tag{FA.48}
$$

exists and lies in $(0,\infty)$. This is existence, not an evaluated
coefficient or a claim of continuity in $s$.

**Proof.** Theorem 72.1 expresses the attained value by eight Hermitian
$5\times5$ Toeplitz blocks, with entries represented by real and imaginary
coordinates. Positive semidefiniteness is equivalent to nonnegative
principal minors. All constraints and the objective are polynomial in
these coordinates and $t=e^A-1$, with fixed real source data and fixed
real $s$. The graph of the maximum can be written by the first-order
formula: there exists a feasible tuple with this objective and every
feasible tuple has objective at most this one. Real quantifier elimination
therefore makes the graph semialgebraic. This argument allows arbitrary
fixed real parameters; it does not require $s$ to be algebraic.

Theorems 74.2–74.3 give positive finite constants $c_s,C_s$ and $t_s$
with
$c_s\le t[\mathcal T(s)-\mathcal T_{\log(1+t)}(s)]\le C_s$
for all $t\ge t_s$. The upper construction uses exactly the finite
auxiliary family FA.31: its two specified null vectors
$\mathbf c_\pm$, the weight
$a_0=(4\sum_\pm\mathbf c_\pm^TL_0^{-1}\mathbf c_\pm)^{-1}$,
the at-most-three-atom IR decomposition of
$L_0-a_0\sum_\pm\mathbf c_\pm\mathbf c_\pm^T$, and

$$
\nu_*=\max_\pm
 \frac{m_1h_2^2(e_\pm)_1^2}{a_0d^2\mathfrak c(\mathbf c_\pm)}.
$$

Thus no undefined auxiliary constant is being assumed. The source's
negative spectral positivity FA.27 and FA.29 provide the strict lower
bound. FA.32 supplies the upper bound also at $s=0$, where its contrast
adjustment term is zero.

For completeness, the limit consequence of semialgebraicity needs only
its one-dimensional finiteness property. For any real threshold $a$, the
set where the bounded quotient above exceeds $a$ is semialgebraic, hence
a finite union of points and intervals; it is eventually either empty
or an entire tail. If liminf and limsup differed, a threshold strictly
between them would have infinitely many visits and omissions on every
tail, a contradiction. Hence a limit exists; the two-sided bounds make
it positive and finite. Finally $e^A/t\to1$. No fixed-strength limit
has been interchanged with an endpoint limit. $\square$

**Proposition 80.2 (finite optimal-static-dual lower bound).** Normalize
$\tau=s/s_0<1$. Let $(Y,\lambda)$ be any finite attained optimal static
dual at this parameter, in the convention

$$
D(h):=h^TYh-\lambda|z|\ge|h^TGh|
\quad(h=(1,z,w),\ \alpha z^2+\beta w^2=1),\quad
\lambda\ge0,\quad j(\tau)=\operatorname{tr}Y-\lambda\tau.
\tag{FA.49}
$$

Use RC's finite static dual only at its stated scope. For each physical
spectral line choose $\mathbf c_\epsilon=(s_0,z_\epsilon,w_\epsilon)$
on the ellipse and its unique positive coefficient $b_\epsilon$ such that
$B_\epsilon^{\rm sp}=b_\epsilon n(\mathbf c_\epsilon)n(\mathbf c_\epsilon)^T$.
Its two live orientations are
$h_{\epsilon,+}=(1,z_\epsilon,w_\epsilon)$ and
$h_{\epsilon,-}=(1,-z_\epsilon,-w_\epsilon)$. Then

$$
K(s)\ge\frac12\sum_{\epsilon=\pm}
 \frac{b_\epsilon}{\mathfrak c(\mathbf c_\epsilon)}
 \min_{\iota=\pm}\left
 \{D(h_{\epsilon,\iota})
       -\epsilon h_{\epsilon,\iota}^TGh_{\epsilon,\iota}\right\}>0.
\tag{FA.50}
$$

Here $\epsilon$ in the scalar expression means the sign of the
corresponding eigenvalue. The expression is a bound supplied by the
chosen finite optimal dual. It is not an equality formula for $K(s)$.
At $\tau=1$ RC64 has no finite optimal dual and FA.50 is not asserted.

**Proof.** Use actual endpoint refinements from FA.20 for a maximizing
instrument and write $b_A=1/t$. Let $\nu_L$ be the pure-live coefficient
measure and $\sigma$ the failure coefficient measure of the saturated
labels. Their exact identities and low objective are

$$
\begin{gathered}
\int hh^T d\nu_L+b_A\int\frac{hh^T}{\mathfrak c}d\sigma=I,
\quad \int nn^T d\sigma=M,\\
\int|z|d\nu_L+b_A\int\frac{|z|}{\mathfrak c}d\sigma\ge\tau,\\
\int|\ell|d\nu_L+
 \int|f+b_A\ell/\mathfrak c|d\sigma.
\tag{FA.51}
\end{gathered}
$$

The measures have uniformly bounded mass: the first identity bounds
$\nu_L$; the second bounds $\sigma$ since the minimum of $\|n\|^2$
on the ellipse is positive. Set
$m(n)=n^TM_2^{-1/2}|\Xi|M_2^{-1/2}n$. Twice the height gap is exactly

$$
\begin{aligned}
&\int(D-|\ell|)d\nu_L
 +\lambda\left(\int|z|d\nu_L+
             b_A\int|z|/\mathfrak c\,d\sigma-\tau\right)\\
&\qquad+\int\left[m(n)-|f+b_A\ell/\mathfrak c|
                    +b_AD/\mathfrak c\right]d\sigma.
\tag{FA.52}
\end{aligned}
$$

Every term is nonnegative: $m\ge|f|$ and $D\ge|\ell|$ give the
last one by triangle inequality. The $O(b_A)$ upper bound forces every
limiting optimal failure measure onto the two physical spectral lines,
with their fixed effects $B_\pm^{\rm sp}$; this is precisely equality
in the whitened trace-norm bound. Near either line $f$ is nonzero with
sign $\epsilon$, uniformly for small $b_A$, so
$|f+b_A\ell/\mathfrak c|=|f|+\epsilon b_A\ell/\mathfrak c$.
Drop only nonnegative spectral slack and off-neighborhood terms in
FA.52, divide by $b_A$, and take compact subsequential limits.
The two compatible orientations may divide the fixed effect weight;
minimizing over them gives FA.50. A subsequence argument applies to
every liminf; Theorem 80.1 identifies it with $K(s)$.
For the negative spectral line FA.27 gives strictly positive live
height in both orientations. Thus $D+\ell\ge2\ell>0$ there,
proving strict positivity of the displayed bound. $\square$

**Corollary 80.3 (three distinct transitions).** The feasibility turn
satisfies
$\bar\tau<\tau_*<\tau_\dagger$, where $\bar\tau$ is the static
height plateau endpoint and $\tau_\dagger$ its static contact.

**Proof.** JR50's supplied enclosure gives
$\bar\tau<.993781$, RC63 gives $\tau_\dagger>.9962433511188$,
and Lemma 78.2 gives $.99448<\tau_*<.99499$. Thus the new
feasibility turn is neither static transition. No static contact-support
sufficiency for a finite-budget optimum follows. $\square$

## 81. Joint weak-endpoint layer: supplied finite limits and additional scope

**Definition 81.1 (the supplied limiting failure problem in these coordinates).**
On the normalized ellipse put $d(\mathbf c)=(|z|-1)^2/2$ and write

$$
F_{\rm lim}(\zeta)=\max\left\{
 \int|f(\mathbf c)|d\sigma:\ \sigma\ge0,\quad
 \int nn^T d\sigma=M,\quad
 \int\frac{d(\mathbf c)}{\mathfrak c(\mathbf c)}d\sigma\le\zeta
 \right\}.
\tag{FA.53}
$$

This is exactly JS Definition 4.1 under Convention 77.1:
$F_{\rm lim}(\zeta)=d_f+2\Phi(\zeta)$, with the same covariance,
cost and entire compact ellipse. JS Lemma 4.2 supplies compact
attainment and at-most-five-atom representations preserving covariance,
cost and objective, including axes and zero weights. Its feasibility
domain is exactly $\zeta\ge\kappa_0$. These are reused results,
not an additional limiting optimization or a scalar evaluation.

**Theorem 81.2 (finite feasibility expansion and supplied height limit).** Set

$$
\kappa_0=\frac{\nu(1-\sqrt{u_f})^2}{2}>0,\qquad
\kappa_1=\frac{\nu^2(1-u_f)^2}{8}>0.
\tag{FA.54}
$$

Here $\kappa_0=C_{\rm end}$ is WE.28's credited endpoint constant.
The entire threshold FA.41–.44 gives the more precise expansion

$$
1-\tau_{\max}(t)=\kappa_0/t+\kappa_1/t^2+O(t^{-3}).
\tag{FA.55}
$$

For $t_n\to\infty$, $q_n=1-\tau_n>0$, $q_n\to0$ and
$t_nq_n\to\zeta<\infty$, $\zeta<\kappa_0$ is eventually
infeasible and $\zeta>\kappa_0$ eventually feasible. At equality
the exact condition $\tau_n\le\tau_{\max}(t_n)$ is still required;
in particular $q_n=\kappa_0/t_n$ is eventually infeasible. No
monotonicity of the prescribed sequence is required.

Along every such eventually feasible sequence, with
$s_n=s_0\tau_n$ and $A_n=\log(1+t_n)$, the published finite-product
limit JS Theorem 7.1 and credited critical law give

$$
\mathcal T_{A_n}(s_n)\longrightarrow
 \mathcal T(s_0)-\frac{L_f-F_{\rm lim}(\zeta)}2,
\qquad F_{\rm lim}(\kappa_0)=d_f.
\tag{FA.56}
$$

At $\zeta=\kappa_0$, WE Theorem 6.2, also credited in JS Theorem
9.1, gives this $\mathcal T(s_0)-\gamma_f$ limit for **every**
sequence of admitted actual instruments retaining its full generated
acquisition labels, including nonoptimizers. A coarsened record has
only the upper-limit bound. For $\zeta>\kappa_0$, FA.56 is an
optimal-value statement with a recovering common-instrument sequence;
it is not a universal equality for arbitrary competitors.

**Proof of the additional threshold assertion and application of suppliers.**
Expanding the explicit FA.44 at $q=\nu/t=0$ gives FA.55, with a
bounded third-order remainder. FA.41 then proves the strict-side
feasibility assertions. Positivity of $\kappa_1$ proves the
claimed equality-path exclusion; retaining only the leading product
would not decide this finite feasibility question.

For the supplied limit, the exact normalization identity is

$$
1-\int|z|dp=\int\frac{(|z|-1)^2}{2}dp
\quad\text{when }\int dp=\int z^2dp=1.
\tag{FA.57}
$$

It is JS.11's deficit. Its failure-weighted cost has the supplied
strict lower bound and equality structure of WE.17–.18 / JS.15:

$$
\int d/\mathfrak c\,d\sigma
 =\frac{\mu_f}{2}\int h_1(u)d\lambda\ge\kappa_0,
\quad d\lambda=d\sigma/\mu_f,\quad\int u\,d\lambda=u_f.
\tag{FA.58}
$$

Here $h_1$ is FA.39 with its parameter set to one. Equality forces
$z^2=u_f,w^2=v_f$; the two opposite $zw$ failure lines have
coefficient mass $\mu_f/2$ each, physical effects $W_+/2,W_-/2$
of Theorem 71.1, and both height differences negative. Thus their
absolute failure height is $d_f$, as in JS.18–.19. This identifies
the critical objective and all cost parameters of the supplied law.

For every finite $\zeta>\kappa_0$, apply JS Theorem 7.1 with
$\lambda=\zeta$ and its prescribed $q_n,t_n$. JS Theorems 4.3,
5.1 and 6.1 already provide the whole-class upper bound and exact
finite recovery. In particular JS.23–.27 supplies the four positive
pure-live repair labels for the residual Gram $I-\mathsf U/t$,
with deficit $C_\sigma/t+O(t^{-2})$; JS.36–.37 supplies the
vanishing strict-cost perturbation when the limiting optimizer has
no cost slack. Its failure covariance is exact at every finite index.
The rare atoms have live weights $a_i/[t\mathfrak c(\mathbf c_i)]$
and failure effects $a_i n_i n_i^T$, including their nonvanishing
acquired failure mass. They are actual generated labels, realized
by §86 with the same full-complex, passive-reference, five-Borel,
whole-fibre and FIRST-clock identities. No TV-preserving balancing
or readable discarded Kraus index is used.

The objective map $B_0+\Phi(\zeta)=\mathcal T(s_0)-
[L_f-F_{\rm lim}(\zeta)]/2$ now gives FA.56 directly, including
threshold saturation recovery. At $\zeta=\kappa_0$ apply the
credited every-instrument critical law to the attained maximizers
of Theorem 72.1. This also covers arbitrarily small feasible edge
slack; no new critical-limit proof is needed. $\square$

**Theorem 81.3 (supplied spectral boundary and unbounded-product extension).**
With the compatible $\mathbf c_\epsilon,b_\epsilon$ of Proposition
80.2 put

$$
\zeta_{\rm sp}=\sum_{\epsilon=\pm}
 \frac{b_\epsilon(|z_\epsilon|-1)^2}
      {2\mathfrak c(\mathbf c_\epsilon)}.
\tag{FA.59}
$$

This is the evaluated $C_{\rm sat}$ of JS.38. To give its explicit
radical correspondence without conflating radial and spectral scalars,
put $\upsilon_{\rm sp}=t_f=-2z_f/(d_f+L_f)$ and

$$
\begin{gathered}
a_+=\frac{\alpha V_f+\beta W_f\upsilon_{\rm sp}^2}
              {1+\upsilon_{\rm sp}^2},\qquad
a_-=\frac{\alpha V_f\upsilon_{\rm sp}^2+\beta W_f}
              {1+\upsilon_{\rm sp}^2},\\
x_+=\frac{V_f}{\alpha V_f+\beta W_f\upsilon_{\rm sp}^2},\qquad
x_-=\frac{V_f\upsilon_{\rm sp}^2}
              {\alpha V_f\upsilon_{\rm sp}^2+\beta W_f},\\
\zeta_{\rm sp}=a_+\frac{(\sqrt{x_+}-1)^2}{2c_*(x_+)}
             +a_-\frac{(\sqrt{x_-}-1)^2}{2c_*(x_-)}.
\end{gathered}
$$

JS Theorem 8.2 supplies $\kappa_0<\zeta_{\rm sp}<\infty$ and
$F_{\rm lim}(\zeta)=L_f$ if and only if
$\zeta\ge\zeta_{\rm sp}$. Every failure measure attaining $L_f$
has exactly cost $\zeta_{\rm sp}$; its total physical effects are
$B_\pm^{\rm sp}$, up to proportional splitting and simultaneous
reversal of $z,w$. JS Corollary 8.3 includes genuine common finite
recovery along every prescribed sequence with limiting product
$\zeta=\zeta_{\rm sp}$, not just products strictly above it.

JS Theorem 9.2 also supplies continuity, concavity and strict increase
of $F_{\rm lim}$ on $[\kappa_0,\zeta_{\rm sp}]$, with endpoint
values $d_f,L_f$ and the attained limiting chord bound

$$
F_{\rm lim}(\zeta)\ge d_f+(L_f-d_f)
 \frac{\zeta-\kappa_0}{\zeta_{\rm sp}-\kappa_0}.
$$

Consequently the limiting height is strictly between
$\mathcal T(s_0)-\gamma_f$ and $\mathcal T(s_0)$ in the strict
middle interval, and equals the latter at and above the spectral
threshold. Qualitative strict transition and this lower chord do not
evaluate the middle scalar interpolation, contacts or rates.

There is in addition the following unbounded-product conclusion:
for $q_n\to0$ through positive values and $t_nq_n\to\infty$,
the original classes are eventually feasible and
$\mathcal T_{\log(1+t_n)}(s_0(1-q_n))\to\mathcal T(s_0)$.
This is an optimal-value assertion and is not asserted by JS's
finite-$\lambda$ theorem.

**Correspondence and proof of the additional scope.** For a spectral
unit vector $e=(e_1,e_2)$ set
$a_e=\alpha V_fe_2^2+\beta W_fe_1^2$ and use JS.42's
$z_e=-\sqrt{V_f}e_2/\sqrt{a_e}$,
$w_e=\sqrt{W_f}e_1/\sqrt{a_e}$. Then
$n(\mathbf c_e)=M_2^{1/2}e/\sqrt{a_e}$, so
$b_\epsilon=a_e$, $z_e^2=x_\epsilon$ and
$\mathfrak c(\mathbf c_e)=c_*(x_\epsilon)$.
This proves that FA.59 is precisely JS.38 on the same physical
whitening and full covariance domain. Applying JS.39–.45 with
$F_{\rm lim}=d_f+2\Phi$ supplies the stated spectral equality
cases, saturation recovery and qualitative transition; those proofs
are reused, not repeated here.

For the unbounded-product extension, fix this two-atom spectral
failure measure. Apply JS.23–.27's exact finite repair for all
sufficiently large $t_n$. Its finite cost is the fixed
$\zeta_{\rm sp}$ and its contrast deficit obeys
$t_ne_{t_n}=\zeta_{\rm sp}+O(t_n^{-1})$.
Since $t_nq_n\to\infty$, eventually $e_{t_n}\le q_n$.
The same finite whole-fibre family is therefore admissible and its
height tends to $\mathcal T(s_0)$ by JS.28 / §86. For the reverse
bound, FA.57 forces every competing coefficient law toward the four
corners; the zero cross moments fix their masses to $1/4$.
The live absolute sum tends to $j(1)$, and the whitened spectral
bound gives failure absolute sum at most $L_f$ for every competitor.
The triangle bound on the actual label sum in FA.37 therefore gives
upper limit at most $(H_0+j(1)+L_f)/2=\mathcal T(s_0)$.
This uses no uniform fixed-strength transfer, evaluates no rate and
asserts no universal equality for nonoptimal instruments. $\square$

## 82. Exact low-label regions and the weak endpoint obstruction

**Theorem 82.1 (four labels on the entire activity floor).** At
$A_0=\log(1+t_0)$, $0\le s\le s_0\tau_*$,

$$
n_{\rm feas}(s,A_0)=n_{\rm opt}(s,A_0)=4.
\tag{FA.60}
$$

**Proof.** The equality class from Theorem 79.1 has failure-family mass
$q_m$, pure-family mass $1-q_m$, and, writing $X=k$,

$$
p^F_{\sigma\upsilon}=\frac{q_m}{4}(1+\sigma k),\qquad
p^R_\sigma=\frac{1-q_m}{2}(1-\sigma\zeta_0 k),\qquad
\zeta_0=\frac{\sqrt{\mu_fV_f}}{\sqrt\alpha(W_f-V_f)}=k_z<1,
\quad -1\le k\le1.
\tag{FA.61}
$$

The failure ratio on the first family is $t_0c_f=W_f$; the second
family has zero failure and $w=0$. These are all merged-ray weights,
by the moment equations used in Theorem 79.1. Rank two of $M$ needs
at least two failure-bearing labels. If there were only one pure label,
its $z$ moment would have magnitude $(1-q_m)/\sqrt\alpha$, which
exceeds the entire available opposing failure moment $q_m\sqrt{u_f}$
since $\zeta_0<1$. Thus there must be at least two pure labels too.
At $k=1$ or $-1$, exactly two failure and two pure weights are positive.
These instruments have maximal floor contrast, hence satisfy every
requested contrast on the segment. Their height is affine in $k$;
Theorem 79.1 selects a maximizing endpoint, including a constant
objective or tied endpoints. This proves both counts with the same
actual instrument and includes $s=0$. $\square$

**Definition 82.2 (three-label constants).** Set

$$
\begin{gathered}
d_3=1+\alpha,\quad e_3=1+\beta,\quad D_f=W_f-V_f>0,\quad
T_f=e_3W_f-\beta V_f,\\
R_0=\frac{\beta(\alpha W_f-d_3V_f)}
          {\alpha(e_3W_f-\beta V_f)}>0,\qquad
\widehat\tau_3=\frac{2\sqrt{\alpha+\beta R_0}}{d_3+e_3R_0},\\
\mathscr B_0=\begin{pmatrix}
\mu_f&-V_f/\sqrt{\alpha+\beta R_0}&-W_f\sqrt{R_0}/\sqrt{\alpha+\beta R_0}\\
-V_f/\sqrt{\alpha+\beta R_0}&V_f&0\\
-W_f\sqrt{R_0}/\sqrt{\alpha+\beta R_0}&0&W_f
\end{pmatrix},\\
\mathscr R(\lambda)=
 \frac{\beta(\alpha W_f-d_3V_f+\lambda)}{\alpha(T_f-\lambda)},
\quad c_R(R)=\mathfrak c(\sqrt{\theta+\omega R},1,\sqrt R).
\tag{FA.62}
\end{gathered}
$$

The matrix $\mathscr B_0$ is PSD of rank two. Let
$S_1=\operatorname{tr}\mathscr B_0$,
$S_2=((\operatorname{tr}\mathscr B_0)^2-
\operatorname{tr}(\mathscr B_0^2))/2$ and
$\lambda_+=(S_1+\sqrt{S_1^2-4S_2})/2$ in this paragraph only.
This is its larger nonzero eigenvalue, not the failure spectral eigenvalue
of FA.36. Define the explicit activity

$$
A_3=\log\left(1+\frac{\lambda_+}{c_R(\mathscr R(\lambda_+))}\right).
\tag{FA.63}
$$

**Theorem 82.3 (entire three-label feasibility criterion).** For the
original weak domain,

$$
\text{an implementation with at most three actual low labels exists}
\quad\Longleftrightarrow\quad
A\ge A_3\ \text{and}\ s/s_0\le\widehat\tau_3.
\tag{FA.64}
$$

Both thresholds are attained simultaneously. Moreover
$A_3>A_0$ and
$\widehat\tau_3<.99<\tau_*<\tau_3=2\sqrt\alpha/(1+\alpha)$,
where $\tau_3$ is RH8.3's unbudgeted feasibility threshold. Consequently

$$
n_{\rm feas}(s,A)=
\begin{cases}
3,&A\ge A_3,\quad\tau\le\widehat\tau_3,\\
4,&A\ge A_0,\quad\tau\le\tau_*,
       \quad\text{and the first case does not hold}.
\end{cases}
\tag{FA.65}
$$

This states only these two regions; it is not a global label partition.

**Proof.** Rank of the normalized live Gram requires at least three
labels. With exactly three, its columns
$f_i=\sqrt{p_i}(1,z_i,w_i)^T$ form an orthonormal $Q$-null frame.
The failure matrix in coefficient coordinates is

$$
\mathscr B=\sum_i b_if_if_i^T=
\begin{pmatrix}\mu_f&a_f&b_f\\a_f&V_f&0\\b_f&0&W_f\end{pmatrix}\succeq0.
$$

Nullity of every eigenvector gives
$\operatorname{tr}Q=\operatorname{tr}(Q\mathscr B)=
\operatorname{tr}(Q\mathscr B^2)=0$. The last equation expands to

$$
\beta a_f^2+\alpha b_f^2=\alpha\beta D_f^2.
\tag{FA.66}
$$

Signs of $a_f,b_f$ can be reversed by coordinate reflections, changing
none of the capacities or absolute contrasts. Write
$a_f^2=\alpha D_f^2u$, $b_f^2=\beta D_f^2(1-u)$,
$0\le u\le1$. Expansion gives

$$
\begin{aligned}
p_u(\lambda):=\det(\mathscr B-\lambda I)
 &=(V_f-\lambda)^2(T_f-\lambda)-uD_f^2H_f(\lambda),\\
H_f(\lambda)&=\alpha W_f-\beta V_f-(\alpha-\beta)\lambda,\\
u_e&=\frac{V_f^2T_f}{D_f^2(\alpha W_f-\beta V_f)}\in(0,1).
\tag{FA.67}
\end{aligned}
$$

The PSD parameter interval is exactly $0\le u\le u_e$.
Here are the spectral details needed for this assertion and for the
activity minimum. At $u=0$ the eigenvalues are $V_f,V_f,T_f$.
For $0<u<1$ both arrow entries are nonzero, giving simple strict
interlacing with $V_f<W_f$. Furthermore $T_fI-\mathscr B\succ0$:
its first two leading principal minors are positive, the second is
$D_f^2[(1+\beta)-\alpha u]$, and its determinant is
$2u\beta^2D_f^3>0$. Thus every eigenvalue is below $T_f$ and
$H_f(\lambda)\ge H_f(T_f)=2\beta^2D_f>0$.
Implicit differentiation of FA.67 gives
$\lambda'=D_f^2H_f(\lambda)/p_u'(\lambda)<0$ for its smallest
and largest roots. They decrease continuously from their $u=0$ values.
The smallest reaches zero precisely at $u_e$ by the determinant formula;
the other two remain positive by interlacing. Thereafter the smallest
is negative. This proves the PSD interval and monotonicity of its
largest eigenvalue, including its repeated starting endpoint.

For a unit null eigenvector $f$ with eigenvalue $\lambda$,
the eigen-equations and $f_0^2=\alpha f_1^2+\beta f_2^2$ give
$f_2^2/f_1^2=\mathscr R(\lambda)$. If $f_1=0$, interpret this
as $R=\infty$ at $\lambda=T_f$, with
$c_R(\infty)=\mathfrak c(\sqrt\omega,0,1)$ by continuity. The function $\mathscr R$ is
strictly increasing on $[0,T_f)$, while

$$
2|f_0f_1|=\frac{2\sqrt{\alpha+\beta R}}{d_3+e_3R}
\tag{FA.68}
$$

strictly decreases for $R\ge R_0$ at these source parameters.
The three products $f_{i0}f_{i1}$ sum to zero; their total absolute
sum is twice the largest absolute product. Since $\lambda\ge0$,
FA.68 bounds the available contrast by $\widehat\tau_3$.

The activity ratio for this eigenvector is
$\lambda/c_R(\mathscr R(\lambda))$. Capacity $c_*(u)$ strictly
increases in $u$, and the normalized $z^2$ here is
$1/(\alpha+\beta R)$, so $c_R$ strictly decreases in $R$.
Consequently this ratio strictly increases with $\lambda$.
The largest eigenvalue therefore determines the largest required label
activity. Its minimum over the entire PSD interval occurs at $u=u_e$.
The matrix there, with negative arrow signs, is exactly $\mathscr B_0$.
Its kernel is generated by
$(\sqrt{\alpha+\beta R_0},1,\sqrt{R_0})^T$, which is $Q$-null.
Its other eigenvectors are also null: at simple spectrum the three
trace equations for powers zero, one and two form an invertible
Vandermonde system for $f_i^TQf_i$. At $u=0$ the simple $T_f$
eigenvector is null and the repeated $V_f$ plane has traceless $Q$
compression; an orthonormal null basis in it exists by IR10.1's
zero-Rayleigh argument. No division by a repeated eigenvalue is used.

Take this orthonormal eigenframe of $\mathscr B_0$, use
$K_i=K(Lf_i)$ and $N_i=b_i n(Lf_i)n(Lf_i)^T$.
It has the required live Gram and failure moments; its kernel vector
attains the contrast cap, so the full frame attains
$\widehat\tau_3$. FA.9 makes its maximum activity exactly FA.63.
Section 86 supplies one original-class instrument. It serves all smaller
contrast requirements and all larger budgets. This proves FA.64.

The needed source comparisons are reproducible with Lemma 78.2's
rational interval prescription:
$1/5<V_f/W_f<3/10<\alpha/(1+\alpha)$,
$.1307<u_e<.1309$,
$.9702<\widehat\tau_3<.9704$ and
$.9978<\tau_3<.9980$. They also make the derivative in FA.68
negative and give $\zeta_0<1$ in FA.61.
Since the attained three-label minimum cannot occur on the four-label
floor of Theorem 82.1, $A_3>A_0$. The three-label lower bound,
FA.64 and the floor four-label witness prove FA.65. $\square$

**Theorem 82.4 (strict four-label endpoint obstruction).** There is a
constant $\tau_4^{\rm ub}<1$ such that every finite-budget weak
instrument with at most four actual low labels has available normalized
contrast at most $\tau_4^{\rm ub}$. This is a uniform strict upper
bound, not an evaluated sharp four-label frontier.

**Proof.** Pad to four slots and use compact variables
$(p_j,q_j=p_jb_j,\mathbf c_j)$ with
$\sum p_j=1$, $\sum q_j=\mu_f$. In the closure allow
$p_j=0,q_j>0$; this is essential when the budget tends to infinity.
Keep the live and failure moments FA.37, but drop the capacity inequality.
This closed set is compact. If its contrast were one, equality in
$\sum p_j|z_j|\le\sqrt{\sum p_jz_j^2}=1$ would force
$|z|=|w|=1$ on every positive-live slot. The three zero cross
moments force all four distinct corners to carry mass $1/4$.
All four slots are therefore occupied by positive live mass, leaving
no zero-live slot for a different failure line. Each corner has
$z^2=w^2=1$, so its failure combinations force $V_f=W_f$, contrary
to the source comparison above. Thus one is absent from this compact
set's contrast range, whose maximum defines $\tau_4^{\rm ub}<1$.
Every original finite-budget competitor maps into this set. $\square$

**Proposition 82.5 (five actual labels at explicit finite budgets).**
For $0<\varepsilon<1/(1+\beta)$ define, explicitly,

$$
\begin{gathered}
u=\delta-\varepsilon\omega,\qquad
k=-\frac{\varepsilon\sqrt\omega}{\sqrt{u(1-\varepsilon)}},\qquad
q_{\sigma\upsilon}=\frac{1+\upsilon k}{4}>0,\\
K_{\sigma\upsilon}=\sqrt{q_{\sigma\upsilon}}
 K(\sqrt u,\sigma,\upsilon\sqrt{1-\varepsilon}),\qquad
K_a=\sqrt\varepsilon K(\sqrt\omega,0,1),\\
N_{\sigma\upsilon}=\frac{V_f}{4}
 n(\sqrt u,\sigma,\upsilon\sqrt{1-\varepsilon})
 n(\sqrt u,\sigma,\upsilon\sqrt{1-\varepsilon})^T,\\
N_a=[W_f-V_f(1-\varepsilon)]
 n(\sqrt\omega,0,1)n(\sqrt\omega,0,1)^T,\\
t_5(\varepsilon)=\max\left\{
 \frac{V_f}{(1-|k|)\mathfrak c(\sqrt u,1,\sqrt{1-\varepsilon})},
 \frac{W_f-V_f(1-\varepsilon)}
      {\varepsilon\mathfrak c(\sqrt\omega,0,1)}\right\}.
\tag{FA.69}
\end{gathered}
$$

This five-label family has contrast $s_0\sqrt{1-\beta\varepsilon}$
and required activity exactly $\log(1+t_5(\varepsilon))$. Hence for
every $\tau<1$ it gives a finite five-label realization by taking
$\varepsilon\le(1-\tau^2)/\beta$ in the stated open range.
For $\tau>\tau_4^{\rm ub}$ and
$A\ge\log(1+t_5(\varepsilon))$ this proves
$n_{\rm feas}(s_0\tau,A)=5$.

**Proof.** The open bound on $\varepsilon$ makes $|k|<1$ and
$u>0$, so all five live weights are positive. Every displayed
coefficient is null. Sum the four main coefficient projectors and the
auxiliary one: the diagonal is $(\delta,1,1)$ and the only possible
cross term is $k\sqrt{u(1-\varepsilon)}+
\varepsilon\sqrt\omega=0$. The failure sums have diagonal
moments $V_f$ and
$V_f(1-\varepsilon)+W_f-V_f(1-\varepsilon)=W_f$;
the cross moment cancels. Thus their total effect is $M$.
The main reports $\sigma$ give contrast $\sqrt u$; the auxiliary
$z=0$ needs no report contribution. The failure/live ratios are
$V_f/(1+\upsilon k)$ on the main directions and
$[W_f-V_f(1-\varepsilon)]/\varepsilon$ on the auxiliary one.
FA.9 therefore gives exactly the maximum in FA.69, attained by §86.
The four-label obstruction gives the matching lower count in the stated
region. This is feasibility; it does not assert height optimality of
these five labels, nor five-label sufficiency at every smaller feasible
budget. The zero endpoint $\varepsilon=0$ is excluded and is not a
finite-budget constructor. $\square$

## 83. Attained upper counts, conditional contacts and eventual lower counts

**Theorem 83.1 (eight and nine actual low labels suffice).** In every
nonempty weak finite-budget class,

$$
n_{\rm feas}(s,A)\le8,\qquad n_{\rm opt}(s,A)\le9.
\tag{FA.70}
$$

If an optimal extreme measure has strict contrast slack, eight labels
suffice for its optimal height. These are upper bounds, not asserted
minimum counts or Toeplitz-rank identities.

**Proof.** Use the compact endpoint-measure formulation FA.20.
Its real live Gram ranges in the five-dimensional space
$\operatorname{tr}(Q_0X)=0$, and its failure effect has three real
symmetric entries on $\operatorname{ran}M$. There are eight independent
equalities. To establish feasibility while preserving the requested
inequality, maximize the signed contrast under those equalities and
choose an extreme maximizing measure. It has at most eight atoms.
For height, retain the contrast inequality and choose an extreme
maximizer; an active inequality adds at most one independent constraint,
so at most nine atoms suffice. At an extreme maximizer with strict
slack it adds none.

Here is the extreme-measure count without an identification of atoms
with hidden Kraus indices. If a measure had more than the number of
active constraints worth of disjoint positive-mass sets, their moment
vectors would be linearly dependent. A nonzero bounded signed density,
constant on these sets, could then be added and subtracted with small
coefficient while preserving all active constraints and positivity.
Inactive constraints remain satisfied by their strict slack. This
contradicts extremality. A nonatomic positive component supplies
arbitrarily many such sets and is excluded too. Compactness and
linearity ensure an extreme optimizer exists; the uniform trace mass
bound is the one in Theorem 72.1. Each remaining atom is implemented
as its own generated low label by FA.11–.13 and §86, including zero
slot measures. Reports and objective signs can be chosen per atom.
Thus these are actual label upper bounds. $\square$

**Proposition 83.2 (contact interface under an attained matching dual).**
Use $\mathsf G,\mathsf B$ of FA.19. If an attained dual certificate
$(Y,Z,\lambda)$ matches the primal optimum with zero gap, its slot
slacks are

$$
\begin{aligned}
h_{r,\epsilon,\eta}(\phi)
={}&\operatorname{tr}(Y\mathsf G)
 +\eta t\operatorname{tr}(Z\mathsf B)-\lambda r\mathsf G_{01}\\
 &-\epsilon[\operatorname{tr}(N\mathsf G)
                +\eta t\operatorname{tr}(\Delta\mathsf B)]\ge0,
\qquad\lambda\ge0.
\tag{FA.71}
\end{aligned}
$$

Every positive atom of an optimal measure lies at a zero of its own
slot slack; also $\lambda(\mathrm{contrast}-s)=0$.
A nonzero slack has at most four distinct circle zeros. An identically
zero slot has no such zero-count bound.

**Proof.** Integrate FA.71 and use the primal moment equalities.
Primal-dual equality writes the gap as a sum of these nonnegative
integrals and the nonnegative contrast slack. All must vanish, proving
contact. Each slack is a degree-at-most-four trigonometric polynomial;
a nonnegative nonzero one has even multiplicity at every circle zero.
Multiplication by $e^{4i\phi}$ gives a polynomial of degree at most
eight, hence at most four distinct such zeros. The argument does not
apply to the zero polynomial. This proposition assumes dual attainment
and a matching value; it supplies no universal dual-attainment theorem
at every finite-budget boundary. Static RC contacts alone are not a
certificate for FA.71. $\square$

**Theorem 83.3 (eventual optimal-count obstructions).** Let $k(s)$ be
RH9.5's unbudgeted height-optimal low-label minimum: three through the
static contact, four above it. For each fixed $0\le s<s_0$, there is
a finite budget threshold beyond which

$$
n_{\rm opt}(s,A)\ge k(s)+1.
\tag{FA.72}
$$

If no ray in any static optimal live family at this $s$ is compatible
with the positive physical spectral failure direction and has
nonnegative live height difference, then eventually

$$
n_{\rm opt}(s,A)\ge k(s)+2.
\tag{FA.73}
$$

On the entire fixed static initial height platform this hypothesis
holds, so every fixed parameter there eventually has
$n_{\rm opt}(s,A)\ge5$.

**Proof.** Suppose there were a budget-diverging sequence of optimal
instruments with too few labels. Pad their slots and take convergent
subsequences in the compact variables of Theorem 82.4, now with the
assumed finite number of slots. Theorem 74.3 makes their heights tend
to the unbudgeted optimum. Splitting the gap into static live slack,
failure spectral slack and triangle mixing slack as in Theorem 74.2
shows that each tends to zero. Positive limiting live mass therefore
forms a static height-optimal live family and occupies at least $k(s)$
slots by RH9.5. Spectral equality requires the two fixed physical
failure effects $B_\pm^{\rm sp}$. The negative one cannot occupy a
positive-live slot: its only compatible live orientations have strictly
positive height by FA.27, causing strict opposite-sign mixing loss.
It must occupy an additional slot whose live weight tends to zero.
This proves FA.72 by contradiction, with a finite eventual threshold.

Under the additional hypothesis the positive spectral effect likewise
cannot attach to a positive-live slot without either incompatible
rank-one direction or opposite-sign loss. Its line differs from the
negative spectral line, and one actual low slot has only one failure
line by FA.7. It therefore requires a second additional slot, proving
FA.73. A zero live height is correctly allowed by the nonnegative
condition and does not force a needless split.

On the static plateau the unique live rays are JR50's frame $(v_*,u_*,w_*)$.
Two have negative $z/w$ and the remaining positive ratio is
$1/t_*<20/17$. The positive physical spectral direction instead
requires

$$
\frac zw=-\frac{dh_1}{bh_2}\sqrt{\frac{m_2}{m_1}}
 \frac{z_f}{\lambda_+}>\frac{243}{205}>\frac{20}{17}.
$$

This is physical whitening as in FA.36. The same directed source-box
substitution gives the stronger interval $1.2146<z/w<1.2147$;
JR's plateau enclosure gives $t_*>17/20$. Thus none of its three
rays is compatible and FA.73 applies. In particular at $s=0$,
three labels are merely feasible for $A\ge A_3$, while every sufficiently
large-budget height optimizer needs at least five. These are eventual
lower bounds, not evaluated budget thresholds or matching optimal-count
sufficiency statements. $\square$

## 84. Exact optimal count at the isolated strong point

**Theorem 84.1 (four exactly at two budgets, five otherwise).** Use the
strong substitution explicitly:

$$
\begin{gathered}
v=v^\dagger=V_f/W_f,\quad u=u^\dagger=\theta v^\dagger+\omega,\\
K_{\sigma\upsilon}^{\rm str}
 =\sqrt{u^\dagger}D+\sigma\sqrt{v^\dagger}T+\upsilon S,\quad
 d_{\sigma\upsilon}=
 \operatorname{tr}((K_{\sigma\upsilon}^{\rm str})^\dagger
 K_{\sigma\upsilon}^{\rm str}\Delta),\\
g_\chi=d_f+2\chi z_f,\quad r=t/t_0\ge1.
\tag{FA.74}
\end{gathered}
$$

The superscript $\rm str$ denotes the strong family. These are exactly
the four matrices in Theorem 71.2.
For every feasible budget at $s^\dagger$,

$$
n_{\rm feas}(s^\dagger,A)=4,\qquad
n_{\rm opt}(s^\dagger,A)=
\begin{cases}4,&r=1\ \text{or}\ r=2,\\5,&r>1,\ r\ne2.
\end{cases}
\tag{FA.75}
$$

There is no six-label strong region at this fixed source.

**Proof.** The strong equality class requires four distinct rays of
positive total live mass $1/4$, proving the feasible lower count.
The four labels with failure coefficient $q=1/4$ on each, in FA.15's
normalization, already have activity $A_0$ and prove feasibility with
four at every larger budget.
For optimality use the exact allocation and chord formula FA.17, not
a new strong height calculation. The directed source intervals give

$$
\begin{gathered}
d_{--}<0,\qquad
2.412<d_{++}/g_+<2.414,\\
.0101<d_{+-}/g_-<.0102<.0244<d_{-+}/g_-<.0246.
\tag{FA.76}
\end{gathered}
$$

These follow by evaluating FA.74 on JR.52's coarse box with the
root-normalization expressions for $m_i$, exactly as in Lemma 78.2.
For a ray of positive live height $d$, an interior failure allocation
$0<Q<r/4$ needs two actual endpoint labels to attain its chord exactly
when $r>d/g$. If $r=d/g$, the saturated endpoint has zero height and
the unsplit label already attains the chord. If $d\le0$, no split
is required. These are the equality conditions for the scalar triangle
inequality, and apply to arbitrary hidden multiplicity by Theorem 69.1.

At $1<r<2$, the $\chi=+$ pair puts $r/4$ on the negative ray
and $(2-r)/4$ on the positive one. The latter never needs splitting,
since $r<2<d_{++}/g_+$. In the $\chi=-$ pair the costs are
strictly ordered $d_{+-}/r<d_{-+}/r<g_-$. Optimality uniquely fills
the cheaper ray to $r/4$ and leaves $(2-r)/4$ on the other, strictly
inside its capacity. Its positive live and negative saturated heights
force exactly one split. Thus five labels suffice and are necessary.
At $r=1$ all four rays are saturated. At $r=2$ each pair puts all
failure on one saturated ray and leaves the other pure. Both cases
need exactly four labels, including zero-weight omissions.
For $r>2$ the negative ray carries $Q=1/2$ without a split, and the
strictly cheaper positive ray in the other pair carries $Q=1/2<r/4$.
It necessarily splits, while the remaining rays are pure. This gives
exactly five. Equal marginal costs in an abstract allocation would
allow arbitrary allocation on the tied face; FA.76 shows that no such
additional positive-pair tie or sign threshold changes this fixed-source
count. Every stated endpoint split is actually generated and realized
with §86's strong high pair. $\square$

## 85. Full-component common decoders and actual refinements

**Proposition 85.1 (fixed-implementation aggregation criterion).** Suppose
fine acquired labels $i$ have encoders $\mathcal E_i$ and full-output
decoders $\mathcal R_i$. After fixed identifications of their quantum
fibres, forgetting the fine control label while preserving each original
fine-branch composite output is possible precisely when there is one
admissible full-fibre TP decoder $\mathcal R$ such that

$$
\mathcal R\mathcal E_i=\mathcal R_i\mathcal E_i\quad\text{for every }i.
\tag{FA.77}
$$

Equality is on every complex input matrix and separately on live output
and each of the five labelled Borel CP measures. Passive-reference
identities then follow. The common decoder must satisfy the required
whole-fibre activity and chronological conditions; equality of integrated
effects alone does not supply it.

For supported-nonzero low labels, different real-null rays cannot be
aggregated into a single two-dimensional label in this way. On the same
ray write the supported live composites as $p_i\operatorname{Ad}_K$,
$p_i>0$, and define the supported failure composites

$$
\widehat\Phi^f_{i,\ell}(\mathcal B)
 =\mathcal R_i^f{}_{\ell}(\mathcal B)\mathcal E_i
       \operatorname{Ad}_E:M_3\longrightarrow\text{failure output}.
$$

Up to unitary identifications of the qubit fibres, preserving every fine
composite **on the supported algebra** is equivalent to equality of
$\widehat\Phi^f_{i,\ell}(\mathcal B)/p_i$ for all $i,\ell,\mathcal B$.
This retains the entire time CP measures, not just their integrated
failure/live ratios. In the resulting unitary coordinates the complete
decoders agree on their entire qubit fibres, and therefore satisfy FA.77
even for arbitrary full-$M_5$ encoders. With preassigned fibre coordinates,
the common decoder must instead agree with each given decoder there.
Neither statement identifies the full encoders divided by $p_i$ or
requires equality of their normalized full-$M_5$ failure composites.
FA.77 remains the full-domain criterion, with no restriction on the
encoders' action on $V^\perp$ or cross-support operators.

**Proof.** A common decoder preserving the fine composites necessarily
satisfies FA.77; conversely the equality and an admissible common decoder
suffice after adding the encoders and discarding $i$. This is the
full-instrument postprocessing interface, as in Leppäjärvi–Sedlák,
arXiv:2010.15816v1, §IV Definition 4, Eq.1. Here it is imposed
componentwise also on Borel outputs, not inferred from POVM equality.

For low labels the restriction
$\widehat{\mathcal E}_i:=\mathcal E_i\operatorname{Ad}_E
=\operatorname{Ad}_{C_i}$ has onto $C_i:\mathbb C^3\to\mathbb C^2$.
This restricted linear map has image all $M_2$.
Thus FA.77 determines the common decoder on its entire fibre, rather
than only on selected input states. A common injective live decoder
forces all products onto one coefficient ray by FA.5. For that ray
write its live composite as $p_i\operatorname{Ad}_K$. Injectivity
then gives $C_i/\sqrt{p_i}$ independent of $i$ in common live-decoder
coordinates, after removing irrelevant Kraus phases. Hence precisely
the supported failure composites $\widehat\Phi^f_{i,\ell}/p_i$
coincide. Conversely, if those maps coincide, the supported total
encoder effects $C_i^\dagger C_i/p_i$ coincide, by TP and the common
normalized live composite. Onto factorizations of this rank-two effect
differ only by fibre unitaries. In those coordinates the supported
encoders divided by $p_i$ are the same surjective CP map, so equality
of all its normalized output composites makes the complete decoders
equal on $M_2$. The admissible chronological path of one supplies a
common decoder with the required activity; constant unitary coordinate
changes preserve the norm integral. This proves exactly the supported
normalized equivalence. The equality just established is equality of
decoders on $M_2$, since the restricted encoder is surjective. Composing
those equal decoders with each original full encoder proves FA.77 on
all of $M_5$. It does not extend the identity
$\widehat{\mathcal E}_i/p_i=\widehat{\mathcal E}_j/p_j$ to full
encoders; no such extension is used.

The distinction is necessary within the original comparison class.
Take a nonzero-failure low branch of the floor constructor, with
supported encoder $C$, live coefficient $p$, and decoder $\mathcal R$
whose total failure effect is $F\ne0$. Split it into two equal
supported branches, using that same decoder on both, and on $M_5$ set

$$
\mathcal E_1=\tfrac12\operatorname{Ad}_{CE^\dagger}
                 +\varepsilon\operatorname{Ad}_{W^\dagger},\qquad
\mathcal E_2=\tfrac12\operatorname{Ad}_{CE^\dagger},
\qquad 0<\varepsilon<1.
$$

Reduce the separate complement encoder from
$\operatorname{Ad}_{W^\dagger}$ to
$(1-\varepsilon)\operatorname{Ad}_{W^\dagger}$. Total encoder effect
remains $I_5$. Every fibre is unchanged, and the added Kraus environment
is discarded. The original twelve supported histories, individual
errors, contrast, sharp joint cost, record TV, activity and FIRST clock
are unchanged. FA.77 holds on all $M_5$ with
$\mathcal R_1=\mathcal R_2=\mathcal R$. Yet for
$X=W|v\rangle\langle v|W^\dagger$ with $\langle v|F|v\rangle>0$,
branch 1 has nonzero failure output on some original label and Borel
set, while branch 2 has none. Dividing by the equal supported live
weights $p/2$ cannot make those full-domain maps equal. Their supported
normalized maps do coincide. This is an allowed multi-Kraus free
completion, with no additional specimen or readable Kraus control.

This statement preserves full output instruments, not a particular
unobserved Hamiltonian description. If an internal prescribed path is
also required unchanged, that is an additional equality condition.
Discarding a Kraus index is not a way to arrange FA.77. In the cited
paper Proposition 6 recovers a detailed instrument only under its extra
orthogonality condition $K_{ix}^\dagger K_{jx}=0$ for $i\ne j$;
it supplies no such recovery for the present discarded indices. $\square$

**Proposition 85.2 (redesigned aggregation and record loss).** For the
supported families in §§77–84, with the supported-zero complementary
branch kept separate as in §86, branches on the same ray can be
redesigned as one new encoder-decoder factorization preserving the
forgotten total complete output on all $M_5$. Its live coefficient is
$p=\sum p_i$ and its complete failure CP measures are their sum.
Its failure/live ratio is the live-weighted average
$\bar b=\sum p_ib_i/p$, and its minimum activity is no larger
than the largest original label activity. This is a new realization,
not automatic control-free erasure in the old implementation.
For arbitrary additional action on $V^\perp$, the full-component
factorization criterion below is necessary; equality only on the
supported qutrit does not assert preservation of that action.
The record-height loss for merging any two actual labels with signed
height differences $x_1,x_2$ is exactly

$$
\frac{|x_1|+|x_2|-|x_1+x_2|}{2}.
\tag{FA.78}
$$

Consequently preservation of the forgotten output does not guarantee
preservation of acquisition-record TV.

**Proof.** Sum the live maps and each prescribed Borel failure map.
On the supported qutrit the new rank-one failure effect has ratio
$\bar b$. FA.9 and Theorem 68.1 realize its summed admitted time
law and live map with minimum $\log(1+\bar b/\mathfrak c)$,
bounded by the largest $\log(1+b_i/\mathfrak c)$. Normalize using
FA.11. For §86's supported encoders, precomposition by $E^\dagger$
then proves this equality on every $M_5$, with the separate coherent
complement untouched. This changes the factorization and generated
label; it need not use any old decoder.

Here is the exact additional criterion when the original encoders act
arbitrarily outside $V$. Write their summed full live map in qutrit
output coordinates as $\Phi^L:M_5\to M_3$; its range is supported
on the common two-dimensional $\operatorname{ran}K$. Apply FA.11
to the summed supported data to obtain the injective live decoder $B$
and its complete failure decoder measures $\mathcal F_\ell(\mathcal B)$.
Let $B^+=(B^\dagger B)^{-1}B^\dagger$ and define the CP encoder
$\mathcal E=\operatorname{Ad}_{B^+}\Phi^L$. Exact redesigned
aggregation of the full maps is equivalent to

$$
\Phi^f_\ell(\mathcal B)=
 \mathcal F_\ell(\mathcal B)\mathcal E
\quad\text{on all }M_5,\quad\text{for every }\ell,\mathcal B.
$$

Necessity follows because the injective $B$ fixes the encoder from the
live map. Sufficiency follows by the displayed factorization and
$\operatorname{Ad}_B\mathcal E=\Phi^L$. The TP decoder makes
$\mathcal E^\dagger(I)$ exactly the target branch's total effect,
so it is TNI when that branch is. Any other factorization of the same
supported complete composites is unitarily equivalent by Proposition
85.1's supported equivalence, giving the same full-component criterion.
Its admitted rank-one time law has the activity just computed. Thus no
extra full-$M_5$ equality follows from mere proportionality of supported
effects; the five Borel components must all pass this criterion.

The scalar absolute-value identity proves FA.78, positive exactly when
the two nonzero differences have opposite signs. For more labels apply
the same triangle inequality iteratively. If fine binary report
components must also be preserved, include them in FA.77 or retain
those report sublabels. If only the original contrast inequality is
required, reporting the common ray's $\operatorname{sgn}z$ maximizes
its available contribution and preserves that inequality.

Different rays can always retain their control in an orthogonal direct
sum, but two complete qubit blocks then occupy dimension four and are
high payload. Charge that entire joint fibre on acquisition, including
branches which later fail. Such a sum is no longer a low aggregation
with unchanged sharp low/high allocation. $\square$

**Proposition 85.3 (refinement of the existing encoder versus redesign).**
On a supported-nonzero low label, a CP refinement of the same encoder,
$\mathcal E=\sum_i\mathcal E_i$, with the same decoder has
$\mathcal E_i=q_i\mathcal E$ on the supported qutrit,
$q_i\ge0$, $\sum q_i=1$. These are input-independent generated
splits. They preserve its maximum label activity, capacity and acquired
height TV. Redesigning an intermediate failure ratio into separate
pure-live and saturated labels, as in FA.20, can instead increase TV;
its increase is precisely the sign-separation gain FA.78.

**Proof.** The supported encoder's Choi matrix has rank one by Theorem
69.1. Every positive summand has the same one-dimensional support and
is therefore proportional. Each split multiplies both height laws and
every output component by the same $q_i$; summing their absolute
differences gives the old one. The decoder and whole fibre are unchanged,
so activity and capacity are unchanged. The endpoint redesign generally
changes these Choi matrices: it retains the total live and failure
moments but attaches their different ratios to distinct generated labels.
Triangle equality is strict exactly in FA.78's opposite-sign case.
None of these assertions constrains arbitrary supported-zero
complementary action or turns a hidden Kraus index into a control.
$\square$

## 86. Simultaneous original-class witnesses, suppliers and remaining boundaries

**Proposition 86.1 (one common instrument for every stated attainer).**
Every finite family in Theorems 78.3, 79.1, 82.1, 82.3, 83.1 and
84.1, Proposition 82.5, and the recovery families of Theorems 81.2–81.3
is realized as follows. For each nonzero low live product $K$ and its
attached effect $N$, choose
$J:\mathbb C^2\to\operatorname{ran}K^\dagger$ isometric and use
exactly FA.11's matrices $C,B,F$ on its entire qubit fibre. They have
$BC=K$, $C^\dagger FC=N$, $B^\dagger B+F=I_2$ and $F\prec I$.
Use FA.13's no-jump path and separately labelled current-survivor jumps,
and terminal isometry $B(I-F)^{-1/2}$ on survivors only. Each label's
minimum activity is FA.9. Pure labels have $N=F=0$ and zero activity.
Generate all declared labels before the acquisition cut; permanently
discard every other input-bearing dilation system before that cut.

In the weak regime add $\sqrt{1-\delta}D$ as a whole three-dimensional
high branch, with fair binary report. In the strong regime instead add

$$
H_\sigma=\frac{\sqrt{1-u^\dagger}D+
                 \sigma\sqrt{1-v^\dagger}T}{\sqrt2},
\qquad \sigma=\pm1,
\tag{FA.79}
$$

reporting $\sigma$ on these and on the four corresponding low rays.
Use their entire three-dimensional fibres with live isometry $E$ and
rate zero. Fix isometries
$W:\mathbb C^2\to V^\perp$ and $J_0:\mathbb C^2\to\mathbb C^3$;
add encoder $W^\dagger$ into an entire counted qubit and live decoder
$EJ_0$, with rate zero and a fair report. No supported-nonzero branch
is omitted; a zero coefficient or zero measure atom is omitted before
forming any inverse.

These prescriptions simultaneously give one full complex CPTP
instrument, all original individual errors, contrast inequality, sharp
joint cost and the actual FIRST clock, rather than separate optima for
these requirements.

**Proof.** The weak families were shown to have total low live
Gram $L_0$ and total failure effect $M$. The strong family uses
$\operatorname{diag}(u^\dagger,v^\dagger,1)$ and the same $M$;
FA.79 supplies exactly its complementary high Gram. Hence the total
supported live Gram is $I_3$ in both cases. Each local factorization
satisfies the hypotheses of Proposition 70.1; its positive encoder
effect is $K^\dagger K+N$. Summing and using the source-root TP
identity gives total encoder effect $I_5$ after precomposition by
$E^\dagger$ and addition of $W^\dagger$. Each branch is CP/TNI
because its positive effect is bounded by this sum. The dimension is
the entire subsequently accessible joint fibre; the qubit complement
is coherent and counted even though all twelve specimens have zero
probability in it. This is the JR original-class completion of Theorem
75.1, explicitly different from the fixed certain-failure CA.10.

For clarity, the actual output on every complex $X\in M_5$, forgetting
acquisition labels, is exactly

$$
\begin{aligned}
\Phi^L(X)&=E[\Lambda_*(E^\dagger XE)+
                      J_0W^\dagger XWJ_0^\dagger]E^\dagger,\\
\Phi^f_\ell(\mathcal B)(X)&=
 w_\ell\left(\int_{\mathcal B}\frac{2\,dt}{(1+t)^2}\right)
 \operatorname{tr}(EME^\dagger X)P_f,\qquad
 \ell\in\{0,1,2,3,13\}.
\tag{FA.80}
\end{aligned}
$$

These are the existing FA.34 identities applied to each new moment
family. Their validity on all complex matrices follows from the live
coefficient Gram identity and the positive failure functionals; no
real-state or twelve-state fit is substituted. At a passive reference,
tensor every live Kraus with $I_R$ and replace the failure trace by

$$
P_f\otimes\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X]
$$

with the same scalar Borel coefficient. This is the conditional
reference operator, not an unconditional reference marginal. The
density identity proves every Borel set, separately for all five labels.
The maps at $0$ and $13$ vanish separately; $1,2,3$ retain their
individual weights $1/4,1/2,1/4$. There are no singular, abort,
wrong-support or uncounted extra sectors in these attainers. Necessities
continue to quantify over every admitted competitor time CP law;
the common choice $g(t)=2/(1+t)^2$ is only this explicit attainer.

On an original specimen the complementary term is zero. Thus the
complete output is the credited CG simulator, not the ideal target.
Writing $\rho_y=a_ya_y^T$ and the ideal live matrix as
$B_y^{\rm ideal}=\xi_y\xi_y^T$ with

$$
(\xi_{yi}^2)_i=
 \left(\frac y{128},\frac{y(58-y)}{128(y+6)},\frac y{2(y+6)}\right),
$$

the individual error is exactly

$$
e_y=\frac12\left[\|\Lambda_*(\rho_y)-B_y^{\rm ideal}\|_1
 +\sum_\ell w_\ell\int_0^1
 |\operatorname{tr}(M\rho_y)g(t)-6y/(y+6t)^2|dt\right].
\tag{FA.81}
$$

Covariance gives this value for each of the four sign pairs at the same
height. CG.143 supplies $e_5=e_{27}=E_*$ and
$e_{16}<71/484<37/250<E_*$. Thus all twelve individual values are
preserved; they are not all equal to $E_*$. Height TV loss and
$\gamma_f$ are not additions to this original HALF error.

Let $\mathsf a_y=\operatorname{tr}(D^\dagger D\rho_y)$ and
$\mathsf b_y=\operatorname{tr}(T^\dagger T\rho_y)$.
Only the high branches have joint dimension at least three, and their
supported effect is
$(1-u_s)D^\dagger D+(1-v_s)T^\dagger T$.
Their acquisition probability at every history of height $y$ is
$(1-u_s)\mathsf a_y+(1-v_s)\mathsf b_y$, maximized at $y=27$.
It is exactly the original sharp $\mathsf C(s)$ by JR34–40.
For the weak families $(u_s,v_s)=(\delta,1)$; for the strong families
it is the explicit dagger pair. This counts acquisition even when its
carrier later fails, without expected dimension or uncounted coherent
shares. The complementary qubit has zero original-history probability
but is still included in its whole fibre's rate norm.

Failure effects kill coordinate zero. The weak sign reports therefore
give contrast $s_0\sum p_j|z_j|\ge s$, and the strong high/low
reports give
$\sqrt{u^\dagger v^\dagger}+
 \sqrt{(1-u^\dagger)(1-v^\dagger)}=s^\dagger$.
No other binary-effect coordinate is fixed. Optional report coins have
common input-independent probabilities and may retain their parent
labels; they need not be used to satisfy a smaller contrast inequality.
The TV in FA.37 or the strong allocation is computed from the same
actual acquisition effects, with live and attached failure contributions
combined inside each label before taking the absolute value.

FA.13 is a chronological first-event instrument. Its current-survivor
jump pulls back to $w_\ell g(t)\operatorname{tr}(F\,\cdot)P_f$;
its survivor effect is positive throughout and at the endpoint. The
first executed failure is at absolute time $6+t$. Only survivors
receive terminal isometry; failed carriers receive no later
positive-carrier action and there is no forced deadline absorption.
All choices are fixed before the unknown input, with no postselection,
acceptance division, history oracle, helper, copy, retry or reset.
The uniform resource is exactly the maximum over generated labels of
$\int_0^1\|R_\alpha(t)\|dt$ on each entire joint fibre.
It is not an expectation, instantaneous maximum, integral of a
cross-label maximum or selected-input average. This verifies the common
correspondence for every stated attainer and every finite recovery
family. $\square$

**Convention 86.2 (credited tools and distinct conclusions).** The
additional ordinary conditional `repo-derived` results beyond the
published suppliers are the attained entire scalar threshold FA.41–.44,
entire weak minimum-budget-boundary height FA.45–.47, fixed-strength
positive finite coefficient existence and static-dual lower bound
FA.48–.50, and the finite-activity actual-label and full-component
aggregation/refinement results of §§82–85. WE supplies the endpoint
constant and universal critical law. JS supplies the full finite-product
joint limiting problem and limit, exact finite moment repair and common
whole-fibre recovery, evaluated spectral saturation boundary and equality
cases, and qualitative strict middle transition. These overlapping
conclusions and proofs are reused, not counted as new joint results.
The additional joint scope retained here is the positive second term
FA.55 with the exact finite equality-path feasibility exclusion, and the
optimal-value limit for unbounded product in Theorem 81.3. No worldwide
novelty claim is made. The exact supplier interfaces are:

| Supplier | Use and boundary |
| --- | --- |
| [CG, §§13–17][CG42] | Conditional root, source, ranks, TP and minimax; CG.143's unequal-by-height errors. This is the Distinguishability Gap owner, not the transfer-coherence geometry volume. |
| [JR, §§34–47][JR42] and [CA, §§2–5][CA42] | Original inequality, sharp worst-history joint cost, supported all-optimizer equality, real-null face and amplitude data. Fixed CA.10/CA.11 are not imposed on competitors. |
| [RC, §§58–66][RC42] and [RH, §§8–10][RH42] | Full static residual/contact curve, finite static dual at its valid scope, and distinct static feasible/height-optimal low-label counts; no finite-budget support sufficiency. |
| [IR, Lemma 10.1][IR42] | Zero-Rayleigh finite null decomposition, including singular/rank-zero remainders; a normalized instrument still needs its total effect bound and completion. |
| FA68–70, FA72, FA74–75 | Prescribed-law minimum with terminal effect identity, double rigidity/capacity, full-fibre construction, exact finite moments, strict two-sided deficit bounds and complete output correspondence. These intermediates are reused. |
| [WE, Theorems 2.2, 3.2, 4.1 and 6.2][WE906] | The same original class and feasibility-only scalar reduction; strict tangent WE.17–.18; $C_{\rm end}=\kappa_0$ and $B_*=\nu$, the restricted exact recovery expression, and the critical full-record limit for every admitted actual instrument sequence. The entire threshold FA.41 and boundary height FA.46 require their stated additional arguments; WE's scalar sign construction gives no TV-preserving symmetrization. |
| [JS, Lemma 4.2, Theorems 4.3, 5.1, 6.1, 7.1, 8.2, 9.1–9.2 and Corollary 8.3][JSce3] | Identical full original class and conditional sources, with the complete parameter/objective/recovery map in Convention 77.1: $F_{\rm lim}=d_f+2\Phi$, $\zeta=\lambda$, $\zeta_{\rm sp}=C_{\rm sat}$ and radial $u_f=r$ distinct from spectral $t_f=u_f^{\rm JS}$. Supplies all prescribed finite-product limits, exact finite moment repair and full-output recovery, spectral cost uniqueness/equality and qualitative strict crossover, crediting WE at criticality. Neither a complete strict-interior scalar interpolation nor an infinite-product theorem is asserted there; JS's construction counts do not replace §§82–84's actual LOW-label minima. |
| [Yang–Xie, arXiv:1605.02431v2, §II Theorem 1][YX] | Hermitian PSD $N\times N$ Toeplitz gives rank-many positive circle atoms; uniqueness only at rank deficiency. Applied with $N=5$ in FA72, not a scalar frontier or minimum-label theorem. |
| [Leppäjärvi–Sedlák, arXiv:2010.15816v1, §IV Definition 4, Eq.1 and Proposition 6][POST] | Full quantum-instrument postprocessing; the proposition's detailed-instrument recovery assumes orthogonal Kraus ranges. It grants no discarded-index access or arbitrary continuous disintegration. |
| Real quantifier elimination and one-dimensional semialgebraic finiteness | Applied in Theorem 80.1 to the explicitly polynomial attained-value graph with fixed real parameters; only limit existence follows. No inaccessible supplementary text is a premise. |
| [TA, *Total actual acquisition alphabets at optimal height*][TA42] | Credited unbudgeted TOTAL actual alphabet $6/7/8$ and its selected finite nonempty coincidence set. These count all nonzero acquisition labels, including supported-zero ones. They neither give finite-$A$ LOW-live-bearing counts nor attain $\mathcal T(s)$ at finite $A$. |

The first-event calculus retains the mature monitored-jump interface
already identified in FA76.1. Sekatski arXiv:2608.25010v1 is cited
there in its HTML carrier as §II.1, Eq.2; the PDF carrier labels the
corresponding section II.A. Its finite-dimensional classical-assisted
channel compression/Schmidt-number interface supplies neither this
worst-history cost nor finite activity, label minima or native services.
No locator from one carrier invalidates the other's section label.

The geometric definition in
[OriginalControlComposition][OC42] supplies continuity, range,
variation and AC/finite-$C^1$ control conditions. It is not acquisition,
calibration, joint coherent storage, decoder actuation or clock permission.
The [critical height-projection/cutoff results][HP42] concern their own
analytic source and parameter map; they supply no continuous finite-$A$
FIB quantum, resource or native bridge. The same restriction applies to
APPT and arithmetic conclusions without a proved correspondence.

**Definition 86.3 (remaining mathematical and native programme).** The
entire scalar feasibility set and weak minimum-budget-boundary height
are FA.41–.46. The remaining weak mathematical evaluation is the
height at feasible points strictly above that boundary, all its
finite-budget contacts/optimal decompositions and phase boundaries;
the value of $K(s)$ and its continuity or singular behavior at static
plateau/contact transitions; the scalar interpolation of FA.53 between
$\kappa_0$ and $\zeta_{\rm sp}$, uniform/joint rates and next terms,
and further joint layers near the static transitions. Existence of
$K(s)$ and an attained limiting moment problem do not evaluate these
values. JS's evaluated saturation boundary, equality cases and strict
continuous middle transition retain their supplied status, and its
common recovery includes equality at saturation. The unbounded-product
optimal-value limit above also remains valid. Neither result supplies
the unevaluated middle values, rates, finite-budget interior frontier
or coefficient/contact evaluation. The sharp four-label contrast ceiling
and the remaining weak
finite-budget feasible/height-optimal count partitions are also
unevaluated; the five-label feasibility family and eventual lower bounds
are not global optimal-count sufficiency.

The full original native requirements remain: lawful sole unknown
reached-cut specimen access; source/calibration and coherent joint storage
of every future-accessible input-bearing share; generated classical
records and controlled decoder actuation; acquisition duration and one
aligned clock with actual FIRST failures at $6+t$; positive-survivor
terminal controls without forced absorption; stopped archives,
source/epoch/controller and permission semantics. These are
`ASSUMED-UNVERIFIED` services, not supplied by a CP identity, a geometric
control predicate or a finite source increment. Inherited root and
certificate premises remain conditional. The full quantum-first AURIC
FIB ATOM programme through 2027, its residual/contact/rank and native
requirements, is neither completed nor narrowed by these finite results.

[CG42]: https://github.com/the-omega-institute/trureturing/blob/42c0c311f19d89110016c3b54a29b43ce69d5b6d/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR42]: https://github.com/the-omega-institute/trureturing/blob/42c0c311f19d89110016c3b54a29b43ce69d5b6d/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[CA42]: https://github.com/the-omega-institute/trureturing/blob/42c0c311f19d89110016c3b54a29b43ce69d5b6d/docs/develop/theory/FIB_NATIVE_COMPLEX_ATOMIC_CONE_AND_OPTIMAL_RESOURCE_FACES.md
[RC42]: https://github.com/the-omega-institute/trureturing/blob/42c0c311f19d89110016c3b54a29b43ce69d5b6d/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md
[RH42]: https://github.com/the-omega-institute/trureturing/blob/42c0c311f19d89110016c3b54a29b43ce69d5b6d/docs/develop/theory/FIB_NATIVE_RESIDUAL_HEIGHT_QUADRATIC_DEPARTURE_AND_ACTUAL_LABEL_THRESHOLD.md
[IR42]: https://github.com/the-omega-institute/trureturing/blob/42c0c311f19d89110016c3b54a29b43ce69d5b6d/docs/develop/theory/FIB_NATIVE_INTERIOR_RECORD_RESOURCE_REDUCTION.md
[OC42]: https://github.com/the-omega-institute/trureturing/blob/42c0c311f19d89110016c3b54a29b43ce69d5b6d/D5/S3/Quantum/Fibers/OriginalControlComposition.lean
[TA42]: https://github.com/the-omega-institute/trureturing/blob/42c0c311f19d89110016c3b54a29b43ce69d5b6d/docs/develop/theory/FIB_NATIVE_TOTAL_ACTUAL_ACQUISITION_ALPHABET.md
[HP42]: https://github.com/the-omega-institute/trureturing/blob/42c0c311f19d89110016c3b54a29b43ce69d5b6d/docs/develop/theory/FIB_NATIVE_CRITICAL_HEIGHT_PROJECTION_AND_CUTOFF_OVERLAP_BOUNDS.md
[POST]: https://arxiv.org/html/2010.15816v1
[WE906]: https://github.com/the-omega-institute/trureturing/blob/90649c566145c094ba1acc79b747e82064214fbf/docs/develop/theory/FIB_NATIVE_WEAK_FINITE_ACTIVITY_ENDPOINT_CONSTANT.md
[JSce3]: https://github.com/the-omega-institute/trureturing/blob/ce3eb5de2f708f7b584dd86df8868682fc0fdbe6/docs/develop/theory/FIB_NATIVE_JOINT_ENDPOINT_SATURATION_BOUNDARY.md

## 追加锚（本行以下为增补区）

## 87. Finite activity, attached records, and one complete original-class witness

The following statements use the conditional source dictionary already fixed in
FA.35--FA.37. Let

$$
\begin{gathered}
\theta=ab/(h_0h_1),\qquad \omega=cd/(h_0h_2),\qquad
\delta=\theta+\omega,\qquad s_0=\sqrt\delta,\\
\alpha=\theta/\delta,\qquad \beta=\omega/\delta,\qquad
Q=\operatorname{diag}(1,-\alpha,-\beta),\qquad
L=\operatorname{diag}(s_0,1,1),\\
\mathscr C=\{(1,z,w)^T:\alpha z^2+\beta w^2=1\},\\
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\quad
(K_0,K_1,K_2)=(D,T,S),\quad G=LNL,\\
K_h=s_0D+zT+wS,\quad \ell(h)=h^T Gh,\quad
H_0=(1-\delta)N_{00},\\
n_h=(0,dw/h_2,-bz/h_1)^T,\quad f(h)=n_h^T\Delta n_h,\\
\mathfrak c(h)=
\frac{h_1^2h_2^2\delta+a^2h_2^2z^2+c^2h_1^2w^2}
     {h_0^2\delta+b^2z^2+d^2w^2}.
\end{gathered}
\tag{FA.87}
$$

All source-root, null, rank, TP, minimax and sharp-cost hypotheses in these
formulas remain conditional. The failure covariance is physically whitened by

$$
M_2=\operatorname{diag}(m_1,m_2),\qquad
\Xi=M_2^{1/2}\Delta_{\{1,2\}}M_2^{1/2}
 =\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},
\quad d_f=\frac{11m_1}{64},\quad
z_f=\sqrt{m_1m_2}\,\Delta_{12},\quad
L_f=\sqrt{d_f^2+4z_f^2}.
\tag{FA.88}
$$
The physical spectral effects are
$M_2^{1/2}e_\pm e_\pm^TM_2^{1/2}$, where $e_\pm$ are unit spectral
vectors of $\Xi$; the unwhitened vectors are not physical failure directions.

**Proposition 87.1 (finite activity excludes a nonzero failure-only label).**
Consider one generated actual label whose entire decoder fibre has activity at
most $A<\infty$. If its survivor rate is any measurable positive operator rate
and its terminal processing is trace preserving on survivors, then

$$
L_{\mathrm{dec}}\succeq e^{-A}I.
\tag{FA.89}
$$
Consequently every nonzero positive encoded state has strictly positive terminal
live mass. A nonzero actual label carrying only failure mass is therefore not in
the finite-$A$ class.

**Proof.** For a positive encoded state $Y$, let
$p(u)=\operatorname{tr}\mathcal S_u(Y)$. Trace balance and the operator norm give
$p'(u)\ge-\|R(u)\|p(u)$. Gronwall's inequality and terminal trace preservation
therefore give
$p(1)\ge\exp(-\int_0^1\|R(u)\|du)p(0)\ge e^{-A}p(0)$.
Since this holds for every $Y\succeq0$, the operator inequality follows. A
nonzero failure-only label would have zero terminal live mass on a nonzero
positive input, contradicting the inequality. This argument permits
noncommuting Hamiltonians, unobserved trace-preserving survivor controls and
multiple Kraus operators. $\square$

For example, the scalar failure density $g(u)=2/(1+u)^2$ with total failure one
has survival $(1-u)/(1+u)$ and hazard

$$
r(u)=\frac{2}{1-u^2},\qquad
\int_0^1r(u)\,du=\infty.
\tag{FA.90}
$$
Thus the absence of a terminal failure atom does not make that row finite
activity. The same obstruction applies to a completion that sends the entire
complement to failure.

**Theorem 87.2 (attached finite-$A$ parameterization).** In the weak range
$0\le s<s_0$, index by $j$ exactly the actual low labels that are nonzero on
supported inputs. In the original all-complex, multi-Kraus equality class,
each such label has one normalized direction $h_j\in\mathscr C$ and numbers
$p_j>0$, $0\le b_j\le t\mathfrak c(h_j)$, where $t=e^A-1$, such that

$$
K_j=\sqrt{p_j}K_{h_j},\qquad
N_j=p_jb_jn_{h_j}n_{h_j}^T,
\tag{FA.91}
$$

$$
\sum_jp_jh_jh_j^T=I_3,\qquad
\sum_jp_jb_jn_{h_j}n_{h_j}^T=M.
\tag{FA.92}
$$
The actual contrast and full-label record TV are respectively bounded by

$$
\mathsf V\le s_0\sum_jp_j|z_j|,
\qquad
T_{\mathrm{actual}}=\frac12\left[H_0+
 \sum_jp_j|\ell(h_j)+b_jf(h_j)|\right].
\tag{FA.93}
$$
The contrast bound is attained by the deterministic report
$\operatorname{sgn}(z_j)$, with an arbitrary report at $z_j=0$.
Here $K_j,N_j$ are supported data. A nonzero full-$M_5$ CP acquisition map
can vanish on all supported inputs: the complementary qubit with encoder
$W^\dagger$, rate zero and live decoder $EJ_0$ in Theorem 75.1 is such
a label. It is absent from the indexed sums and contributes zero to supported
contrast and TV, but remains an actual label in the total alphabet; its entire
fibre still obeys the activity bound. Thus nonzero on the full input algebra
is distinct from nonzero on supported inputs. At $t=0$ the class is empty
when $M\ne0$.

**Proof.** Proposition 87.1 supplies a nonzero supported live product in every
indexed label, since its supported encoder is nonzero. The supplied equality
face makes that product a rank-two real-null product. Its common-image and
common-kernel rigidity forces all nonzero supported live Kraus products in
that label onto one normalized direction. Pulling a supported failure effect
through the same factor gives a rank-one effect on $\mathbb Rn_{h_j}$;
the Schur complement of the positive $00$ pivot is exactly
$N_j\preceq tK_j^\dagger K_j$, which is (FA.91). Summing the complete live Gram
and failure covariance gives (FA.92). The report inequality is
$|\sum_jp_jm_jz_j|\le\sum_jp_j|z_j|$ for $|m_j|\le1$, and the stated signs
attain it. If $t=0$, (FA.91) forces every $N_j=0$, contradicting $M\ne0$.
No prescribed noncommuting time law is inferred from these endpoint moments.
$\square$

**Theorem 87.3 (one common original-class output constructor).** Fix a weak
request $0\le s<s_0$ and a finite family satisfying (FA.91)--(FA.92) with
$\sum_jp_j|z_j|\ge\tau:=s/s_0$. Give low label $j$ the deterministic report
$\operatorname{sgn}(z_j)$, arbitrary at zero, and choose isometries
$J_j:\mathbb C^2\to\operatorname{ran}K_j^\dagger$. Put

$$
\begin{gathered}
Q_j=J_j^\dagger(K_j^\dagger K_j+N_j)J_j,\\
C_j=Q_j^{1/2}J_j^\dagger E^\dagger,\qquad
B_j=K_jJ_jQ_j^{-1/2},\\
F_j=Q_j^{-1/2}J_j^\dagger N_jJ_jQ_j^{-1/2},
\end{gathered}
\tag{FA.94}
$$
so that $B_j^\dagger B_j+F_j=I_2$ and
$L_{\mathrm{dec},j}=B_j^\dagger B_j\succ0$. Use

$$
G_{\mathrm{time}}(u)=\frac{2u}{1+u},\qquad
Z_j(u)=\sqrt{I-G_{\mathrm{time}}(u)F_j},\qquad
R_j(u)=2(1+u)^{-2}F_j[I-G_{\mathrm{time}}(u)F_j]^{-1}.
\tag{FA.95}
$$

The current-survivor jump on each of the five labelled Borel components is

$$
Y\longmapsto w_\ell\,\frac{2}{(1+u)^2}
\operatorname{tr}\!\left(F_jZ_j(u)^{-1}YZ_j(u)^{-1}\right)P_f,
\quad w=(0,\tfrac14,\tfrac12,\tfrac14,0),
\tag{FA.96}
$$
and the survivor terminal map uses $EB_j(I-F_j)^{-1/2}$. Its activity is

$$
\int_0^1\|R_j(u)\|du
=\log\left(1+\frac{b_j}{\mathfrak c(h_j)}\right)\le A.
\tag{FA.97}
$$

Choose isometries $W_\perp:\mathbb C^2\to\operatorname{ran}(I-P)$ and
$J_0:\mathbb C^2\to\mathbb C^3$, and use one counted high label

$$
C_H=\begin{pmatrix}\sqrt{1-\delta}\,DE^\dagger\\ W_\perp^\dagger\end{pmatrix}.
\tag{FA.98}
$$
Its rate is zero, its binary report is deterministically $+$, and its two
terminal Kraus indices are hidden. For every $X\in M_5$ and every passive
reference, the resulting full output satisfies

$$
\Phi^L(X)=E\left[\Lambda_*(E^\dagger XE)+
J_0W_\perp^\dagger XW_\perp J_0^\dagger\right]E^\dagger,
\tag{FA.99}
$$

$$
\Phi^f_\ell(\mathcal B)(X)=w_\ell\left(\int_{\mathcal B}\frac{2\,du}{(1+u)^2}\right)
\operatorname{tr}(EME^\dagger X)P_f,
\tag{FA.100}
$$
with conditional reference operator
$w_\ell(\int_{\mathcal B}g)P_f\otimes
\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X]$. The five components include the two
zero components. The total encoder effect is $I_5$; failures occur first at
absolute time $6+u$, only survivors receive the terminal map, and no later
positive-carrier action or forced deadline absorption is introduced. Under the
inherited source identities, the same instrument preserves

$$
e_{5,e,n}=e_{27,e,n}=E_*,\qquad e_{16,e,n}<E_*,\qquad e,n\in\{\pm1\},
\tag{FA.101}
$$
and its whole dimension-five high fibre (supported dimension three plus
coherent complementary dimension two) is charged by the dimension-at-least-three
acquisition event and has the original sharp worst-history joint cost. This
constructor uses the allowed JR free complement and is distinct
from the fixed certain-failure CA10 completion.

**Proof.** The identities in (FA.94) are direct matrix multiplication. Since
$F_j\prec I$, (FA.95) is positive on the whole fibre and integration of the
rank-one eigenvalue gives (FA.97). Equations (FA.99)--(FA.100) follow by
summing the live and failure Kraus components; tensoring the same calculation
with $I_R$ gives the reference identity. The source error and cost identities
are inherited exactly. The low reports attain
$\mathsf V=s_0\sum_jp_j|z_j|\ge s$, while the deterministic high report
contributes no $01$ effect. The moment and capacity identities alone give the
displayed CP outputs; membership at the requested contrast also uses the
stated available-contrast hypothesis. $\square$

**Corollary 87.4 (weak total actual alphabet).** Let $n_{\mathrm{opt}}(s,A)$ be
the minimum number of actual low labels nonzero on supported inputs among
weak height maximizers, and assume the weak finite-$A$ class is nonempty. Then

$$
N_{\mathrm{opt}}^{\mathrm{total}}(s,A)=n_{\mathrm{opt}}(s,A)+1.
\tag{FA.102}
$$
The same equality holds with $n_{\mathrm{feas}}$ and $N_{\mathrm{feas}}$.
Total counts include every nonzero full-$M_5$ acquisition map, including
supported-zero labels; these are excluded only from the supported low count.

**Proof.** Every competitor has its supported-nonzero low labels and at least
one positive-supported high acquisition label. Any additional supported-zero
labels also count, so the total is at least the supported low count plus one.
Starting with a minimum supported-low-label optimum, use (FA.94)--(FA.100),
placing the coherent complement inside the one high fibre. All high differences
are nonnegative and sum to $H_0$ there, and the low TV is unchanged. The low
sign reports attain at least the original contrast, and the deterministic high
report contributes none, so the same inequality request is satisfied. This is
a reconstruction of a common instrument, not an effect-only merge of arbitrary
channels. $\square$

## 88. A strict finite-interior submaximal-height counterexample

Set

$$
V_f=\frac{m_2h_1^2}{b^2},\quad W_f=\frac{m_1h_2^2}{d^2},\quad
\mu_f=\alpha V_f+\beta W_f,\quad
\nu=\frac{\mu_f}{c_*(V_f/\mu_f)},\quad
\nu_f=u_f=V_f/\mu_f,\quad \upsilon_f=W_f/\mu_f.
\tag{FA.103}
$$
Under the supplied source enclosure, $0<\nu_f<1<\upsilon_f<3$ and
$\alpha\nu_f+\beta\upsilon_f=1$. Let

$$
 h^F_{\sigma\upsilon}=(1,\sigma\sqrt{\nu_f},\upsilon\sqrt{\upsilon_f}),\qquad
\Sigma_f=\frac{\mu_f}{4}\sum_{\sigma,\upsilon=\pm1}\delta_{h^F_{\sigma\upsilon}}.
\tag{FA.104}
$$
For $0<q\le10^{-5}$ set $t=\nu/q$ and $A=\log(1+t)$. Four failure-bearing labels have weight $q/4$ and saturated coefficient
$b_F=\mu_f/q$; their total failure covariance is $M$.
The remaining Gram is

$$
B_q=\operatorname{diag}(m,d_1,d_2),\qquad
m=1-q,\quad d_1=1-q\nu_f,\quad d_2=1-q\upsilon_f,
\quad m=\alpha d_1+\beta d_2.
\tag{FA.105}
$$
It is positive definite. The unique maximum-contrast completion is the four
corner measure

$$
h^4_{\sigma\upsilon}=(1,\sigma\sqrt{d_1/m},\upsilon\sqrt{d_2/m}),\qquad
p^4_{\sigma\upsilon}=m/4,
\tag{FA.106}
$$
with height contribution $J_4(q)=\frac m4\sum|\ell(h^4_{\sigma\upsilon})|$.
Indeed, Cauchy--Schwarz gives the upper bound $\sqrt{md_1}$ and equality fixes
both absolute coordinates and then all four cross moments.

A different null decomposition is

$$
\begin{gathered}
\chi_q=m+\alpha d_1,\quad h^0=(1,\alpha^{-1/2},0),\quad
p_0=\frac{m\alpha d_1}{\chi_q},\\
h^\pm=\left(1,-\frac{\sqrt\alpha d_1}{m},
 \pm\frac{\sqrt{d_2\chi_q}}m\right),\quad
p_\pm=\frac{m^2}{2\chi_q}.
\end{gathered}
\tag{FA.107}
$$
All three weights are positive, all three directions lie in $\mathscr C$, and

$$
p_0h^0(h^0)^T+p_+h^+(h^+)^T+p_-h^-(h^-)^T=B_q,
\tag{FA.108}
$$
while their contrast is

$$
\kappa_3(q)=\frac{2m\sqrt\alpha d_1}{m+\alpha d_1}<\sqrt{md_1}.
\tag{FA.109}
$$
Define $J_3(q)=p_0|\ell(h^0)|+p_+|\ell(h^+)|+p_-|\ell(h^-)|$.

**Theorem 88.1 (strict height gain below maximum contrast).** Under the inherited
source-box inequalities, for every $0<q\le10^{-5}$,

$$
J_3(q)>J_4(q).
\tag{FA.110}
$$

**Proof.** Write
$G=(g_{ij})$ and compare the continuous extensions at $q=0$. The source
signs leave only $(1,-1,-1)$ among the four corners and only
$(1,-\sqrt\alpha,-\sqrt{1+\alpha})$ among the three rays with negative
$\ell$. Direct expansion gives

$$
\begin{aligned}
D_0:=J_3(0)-J_4(0)
={}&\frac{\beta(g_1-g_0)}{2(1+\alpha)}-\frac{g_2}{2}
-\frac{g_{01}(1-\sqrt\alpha)^2}{1+\alpha}\\
&+g_{02}\left(\frac2{\sqrt{1+\alpha}}-1\right)
+g_{12}\left(1-2\sqrt{\frac\alpha{1+\alpha}}\right).
\end{aligned}
\tag{FA.111}
$$
The directed source box supplies
$0.8777<\alpha<0.8778$, $g_2<0.001678$,
$g_{01}<0.002371$, $g_{02}>0.002208$,
$\sqrt\alpha>0.936$, $\sqrt{1+\alpha}<1.371$ and
$1+\alpha>1.877$. Therefore

$$
D_0>
\frac{2208}{10^6}\left(\frac{2000}{1371}-1\right)-\frac{1678}{2\cdot10^6}
-\frac{2371}{10^6}\frac{(64/1000)^2}{1877/1000}
>\frac1{6250}.
\tag{FA.112}
$$
On $0\le q\le10^{-5}$, the same enclosure gives $\|G\|<0.006$. The
explicit derivatives of (FA.106)--(FA.107) bound
$|J_4'|\le20\|G\|$ and $|J_3'|\le48\|G\|$, hence
$|(J_3-J_4)(q)-D_0|\le68\|G\|q<q$. Thus
$J_3-J_4>1/6250-q>0$.

For $\tau_3(q)=q\sqrt{\nu_f}+\kappa_3(q)$, every
$0\le\tau\le\tau_3(q)$ is feasible for both completions. Since
$q<1/\upsilon_f$, $t>t_0$, and
$\tau_3(q)<q\sqrt{\nu_f}+\sqrt{(1-q)(1-q\nu_f)}=\tau_{\max}(t)$,
these are strict interior points above the minimum-budget boundary. The
common constructor of Theorem 87.3 gives the same twelve error values, five
Borel components, sharp joint cost and first-event clock. Therefore this is an
original-class attainable height comparison, not a claim of global optimality
or minimum alphabet. It refutes only the substitution of maximum contrast for
height optimization below that contrast. $\square$

## 89. Continuous null roofs and the complete rank-two fixed-allocation branch

Let

$$
\mathcal K_Q=\{B\succeq0:\operatorname{tr}(QB)=0\},\qquad
\mathcal R_\varphi(B)=\max_{\mu\ge0,\ \int hh^T d\mu=B}\int\varphi(h)d\mu,
\tag{FA.113}
$$
for $\varphi\in C(\mathscr C)$. Every $B\in\mathcal K_Q$ has a null
representation: apply the zero-diagonal orthogonal-basis argument to
$B^{1/2}QB^{1/2}$ on its range and pull the basis back by $B^{1/2}$.
The mass of every representing measure is $B_{00}$, and $\mathscr C$ is compact.

**Theorem 89.1 (continuity on the whole PSD cone).**
$\mathcal R_\varphi$ is continuous on all of $\mathcal K_Q$ for every continuous
real payoff $\varphi$. In particular, the available-contrast roof
$\mathcal V_Q(B)=\mathcal R_{|z|}(B)$ is continuous at every rank.

**Proof.** Compactness of the ellipse and fixed mass give attainment and weakly
convergent maximizing subsequences, hence upper semicontinuity. At $B\succ0$,
choose $\varepsilon_n\downarrow0$ with
$B_n\succeq(1-\varepsilon_n)B$ and write
$R_n=B_n-(1-\varepsilon_n)B\in\mathcal K_Q$. Mixing representing measures
for $B$ and $R_n$ gives lower semicontinuity. If $\operatorname{rank}B=2$,
the compression $B^{1/2}QB^{1/2}$ has nonzero eigenvalues $\kappa,-\kappa$:
a real two-plane cannot be totally isotropic for signature $(1,2)$. Its two
null lines are the pullbacks of the vectors
$(a_++a_-)/\sqrt2$ and $(a_+-a_-)/\sqrt2$, and their weights are uniquely
fixed by $B$. Thus every representing measure for $B_n\to B$ converges to
that unique two-atom measure. Rank one has one atom and rank zero has the zero
measure, so the same argument gives lower semicontinuity at all boundary ranks.
$\square$

**Corollary 89.2 (rank-at-most-two fixed-allocation value and count).**
Let $F$ be a finite oriented failure allocation
$\Sigma=\sum_{h\in F}a_h\delta_h$ with
$\sum a_hn_hn_h^T=M$, and let

$$
B=I-\sum_{h\in F}\frac{a_h}{t\mathfrak c(h)}hh^T\succeq0,
\qquad \operatorname{rank}B\le2.
\tag{FA.114}
$$
Write its unique null representation as $B=\sum_{h\in R}r_hhh^T$ and set
$C_h=t\mathfrak c(h)$. The fixed-allocation feasible contrast condition is

$$
\tau\le\sum_{h\in F}\frac{a_h}{C_h}|z_h|+\sum_{h\in R}r_h|z_h|.
\tag{FA.115}
$$
For every such request the fixed-allocation maximum height is

$$
\mathcal H_F(t)=\frac12\left[H_0+
\sum_{h\in F}\frac{a_h}{C_h}|\ell(h)+C_hf(h)|+
\sum_{h\in R}r_h|\ell(h)|\right].
\tag{FA.116}
$$
Its minimum low actual-label count is

$$
|F\cup R|+\#\{h\in F\cap R:\ell(h)[\ell(h)+C_hf(h)]<0\}.
\tag{FA.117}
$$
The total actual alphabet of the constructor is one larger.

**Proof.** Saturating every fixed failure direction leaves the unique residual
measure of (FA.114), independent of the requested contrast. For a common
direction, convexity gives
$|\ell+bf|\le(1-b/C_h)|\ell|+(b/C_h)|\ell+C_hf|$.
Endpoint splitting attains equality. If the two endpoint values have opposite
strict signs and both masses are positive, every interior coefficient has
strict loss and two labels are necessary; equal signs, a zero endpoint or a
zero mass permit one label. Distinct directions cannot share an actual low
label by Theorem 87.2. Axes, coincident directions and zero weights are
removed by the same formula. $\square$

## 90. A nine-coordinate common-attainer bound

**Theorem 90.1 (at most nine low labels).** Every nonempty weak finite-$A$
class has a height maximizer with at most nine actual low labels nonzero on
supported inputs, and Theorem 87.3 then gives a total alphabet of at most ten.
This is an existence
upper bound, not a minimum or a parameter classification.

**Proof.** Use the attained finite family supplied by FA72 and split every atom
into pure-live and saturated endpoints; absolute-value convexity does not lower
height and preserves all original moment constraints. For each resulting atom
$(h_i,p_i,b_i)$ record

$$
\Gamma_i=(1,z_i,w_i,z_i^2,z_iw_i,
 b_i,b_iz_i^2,b_iz_iw_i,|z_i|)\in\mathbb R^9.
\tag{FA.118}
$$
The first five coordinates fix the complete live Gram. The next three fix the
failure covariance because
$\sum p_ib_i=\mu_f$, $\sum p_ib_iz_i^2=V_f$ and
$\sum p_ib_iz_iw_i=0$; the remaining failure second moment follows from the
null ellipse. The last coordinate preserves available contrast. If more than
nine weights are positive, a nonzero dependence $\sum d_i\Gamma_i=0$
allows both small perturbation signs. Height is affine along this segment, so
optimality forces its derivative to vanish. Continue in one sign until a weight
is zero and iterate. The resulting family has at most nine atoms, all moments,
contrast and height unchanged. The common constructor turns them into actual
labels, with deterministic reports and hidden Kraus indices counted only as
specified by the original record. $\square$

## 91. Literature boundaries and the unresolved dual

The following primary results are used only at the stated interfaces. Huang--
Zhang, June 2005 author manuscript, §2 opening and Theorem 2.1, distinguishes
one real quadratic-form equal-trace decomposition from the stronger two-form
complex Hermitian statement. The real transfer fails for
$A=\operatorname{diag}(1,-1)$ and $B=\begin{pmatrix}0&1\\1&0\end{pmatrix}$:
a nonzero real vector cannot satisfy both quadratic equations. Uhlmann,
*Roofs and Convexity*, Propositions 2.2 and 3.5, gives common flat
 decompositions and attainment under compactness and continuous extreme payoff;
it does not retain the present covariance, capacity and joint objective.
Dette--Melas, Theorem 3.1 with (3.2)--(3.4), requires a specified information
matrix and Chebyshev systems. The nine coordinates in (FA.118) do not form
such a system: on the pure-live sheet the three $b$-coordinates vanish.
Xia--Wang--Sheu, Theorem 3, has a separate equality exception whose hypotheses
are not those of the capacity-cleared quartic terms here. Leppäjärvi--Sedlák,
Definition 7 in §6.1, requires equality of each output CP map, which is why
(FA.99)--(FA.100) are stated componentwise. Zhu--Zhang--An--Zeng, (2)--(4),
gives a Stiefel parameterization for a fixed state decomposition but no global
finite-activity certificate. Hsieh--Tavakoli--Ku--Skrzypczyk, Result 1,
defines robustness into non-interactive instruments; that SDP is not the
actual-label integrated-rate resource used here. Pinelis, Theorem 1,
Corollaries 4--5 and Proposition 6, supports finite atomic extreme
representations under its compact cone hypotheses; (FA.118) supplies the
nine-coordinate original-data specialization.

A valid conditional dual upper bound for the still-unsolved global problem is
obtained from matrices $Y,Z$ and $\lambda\ge0$ satisfying, on every
$h\in\mathscr C$,

$$
 h^TYh\ge|\ell(h)|+\lambda|z|,
\qquad
 h^TYh+t\mathfrak c(h)n_h^TZn_h
 \ge|\ell(h)+t\mathfrak c(h)f(h)|+\lambda|z|.
\tag{FA.119}
$$
Integration bounds the unhalved low-label objective
$\sum_jp_j|\ell(h_j)+b_jf(h_j)|$ by
$\operatorname{tr}Y+\operatorname{tr}(ZM)-\lambda\tau$.
Consequently the full record TV is at most
$[H_0+\operatorname{tr}Y+\operatorname{tr}(ZM)-\lambda\tau]/2$.
No all-parameter choice of $Y,Z,\lambda$, common contacts or positive weights
is supplied here; (FA.119) is a precise missing bridge, not an evaluated
frontier.

## 92. Programme boundary and current-source interfaces

When its available-contrast hypothesis holds, the common constructor of
Theorem 87.3 preserves the complete original experiment: one unknown
reached-cut specimen; all twelve histories; one common full-complex CPTP
instrument; live coherences and passive references; five separately labelled
Borel failure maps including zero components; the contrast inequality; the
sharp jointly counted dimension-at-least-three acquisition cost; and the same
FIRST clock at $6+u$. It preserves all individual errors
$e_5=e_{27}=E_*$ and $e_{16}<E_*$. The constructor is conditional on the
source-root, equality-face, TP and minimax antecedents and does not certify
native access, calibration, coherent storage, decoder actuation, aligned clock,
archives, controller or permission semantics.

The complete evaluated $\mathcal T_A(s)$ for every feasible interior point is
still open: global oriented failure allocation, full-rank submaximal live-height
optimization, all contacts and rank transitions, and a universal bound with a
matching evaluated common attainer for that frontier have not been supplied.
The complete precontact and
contact $K(s)$ coefficients, gluing and degeneracies remain open. The exact
finite-$A$ optimizer alphabet partition remains open beyond (FA.102),
(FA.114)--(FA.117), the strong four/five results already supplied by FA, and
the upper bound (FA.118).

The completed conditional JS source supplies global limiting-budget selection
by its unique clamped scalar root and strictly monotone inversion
([JS, Theorem 11.3][JSsel]). Its Proposition 12.2 distinguishes this selection
from the inventory of transition zeros. JS Theorem 14.1 supplies the
quantitative critical strip for every complete actual record, Theorem 14.2
supplies the uniform $O(t^{-1})$ value error on actually feasible sub-spectral
product intervals bounded away from the spectral threshold, and Theorem 16.2
supplies the compact-uniform spectral product/value layer. These supplied
limiting and uniform results are retained at their stated conditional scopes;
they are not exact finite-frontier evaluations.

As specified in JS Definition 18.2, the full source-specific transition-zero
inventory in JS.58, including isolation, ordering, multiplicities and sign
intervals, remains open. The critical five-label and static-contact joint
layers and the other required next terms also remain open. Global selection
of the limiting optimizer does not establish a single support transition or
close these remaining obligations. No static failure-line count is identified
with a finite actual alphabet, hidden Kraus multiplicity or joint quantum
dimension.

The current transition-band source contributes conditional scalar contact,
curvature and selected-branch information at its own source scope; it does not
evaluate the finite-$A$ quantum frontier. The current self-calibration source
proves a finite-record common-gain reconstruction under its own control
contract; it does not provide specimen access, quantum acquisition or native
permission. The current static-compatibility source uses an explicitly added
separator/control contract for its encoded chain; it does not supply the
original quantum acquisition/action bridge. These interfaces therefore leave
the unresolved full-programme obligations just listed unchanged. The
through-2027 quantum-first AURIC
FIB ATOM programme is neither completed nor narrowed by this finite source
increment.

[JSsel]: https://github.com/the-omega-institute/trureturing/blob/f1451cc068cd7e7717629ff6e0c0b171ba91282a/docs/develop/theory/FIB_NATIVE_JOINT_ENDPOINT_SATURATION_BOUNDARY.md

## 追加锚（本行以下为增补区）

## 93. A selected conditional five-contact optimum on a closed strip

**Assumption 93.1 (source, class and identification).** Retain FA Convention
67.1, Definitions 67.2--67.3 and Theorem 87.2; RC Conventions 58.1 and
Definitions 58.2--58.3; CG Definitions 13.1, Proposition 13.2, Theorem 15.1
and Convention 21.3; and JR Theorem 42.1 and its sharp-cost equality face.
The original isolated source root, its existence, uniqueness, isolation,
Jacobian, ranks, exact source-root TP normalization, stopped-cq minimax/error
identification and sharp joint acquisition-cost identification are
`ASSUMED-UNVERIFIED` premises here. The new contact root below is a different
root, and its proof does not discharge those source premises.

**Theorem 93.2 (selected original optimum).** Under Assumption 93.1, assume the original CG isolated root exists in the entire nine-coordinate radius-10^(-24) box of RC58, with the supplied ranks, source-root TP normalization, original HALF stopped-cq minimax/error identification, JR42 supported equality/sharp joint acquisition-cost conclusions, and FA67's admitted original instrument class. Use the free JR coherent full-M5 completion, rather than imposing fixed CA10's certain-failure complement. Only supported-nonzero low labels enter the necessary low-label reduction; supported-zero labels can have nonzero full encoders.

For every

$$
9999/10\le t=e^A-1\le10001/10,\qquad0\le s\le3/25,
$$

the exact original value is

$$
\boxed{\mathcal T_{\log(1+t)}(s)=\tfrac12\{H_0+d_0+\alpha d_3+
 (\mu/t)d_5+(\alpha V/t)d_6\}.} \tag{FA.120}
$$

The eight multipliers $d$, five positive weights and five contact coordinates in (FA.120) form the unique zero of the eighteen equations (FA.123) in the explicit box of §95, for that $t$ and the original source. This is a selected algebraic root with an outward existence/uniqueness and global sign certificate, not a remaining maximization, grid optimum, SDP, or uninstantiated sufficient-certificate condition. The same five supported low atoms attain (FA.120) for every requested s in the displayed interval. Their actual contrast is strictly greater than 0.12421255 on the whole strip, so the original requested contrast inequality has slack. All these points have $t>t_0$; for $0<s<3/25$ they are strictly interior original weak points.

An exact seed is

$$
\boxed{s=1/16,\quad t=1000,\quad A=\log1001.} \tag{FA.121}
$$

At this seed the conditional optimal TV lies in

$$
(0.10283536503869052157453180203846052,
 0.10283536503869071116976210460262283).
$$

The selected family has three pure-live and two saturated low labels, five distinct low projection lines, two nonzero physical failure lines, and one entirely counted dimension-five high fibre. The minimum number of actual supported low labels among all original global height optimizers is five, and the minimum total actual alphabet is six, throughout this strip. This count is restricted to this strip; it is not the global atlas. The supported atom law is unique, and the multipliers are unique in the specified gauge and box; arbitrary full instrument representatives and time laws are not asserted unique.

The selected maps, weights, contacts and multipliers depend real analytically on $t$ in $(999.9,1000.1)$. The value is independent of requested $s$ on this rectangle. The original positive global seed, all contact curvatures, absence of other zeros, strict contrast slack, positive weights, fixed gauge and nonsingular Jacobian required by the implicit-function continuation argument are established in §§96--99.

**Proof.** Sections 94--97 establish the selected root and its complete
circle certificate; §98 proves matching, universal optimality and the actual
alphabet minimum. Section 99 proves regularity, and §100 supplies one
simultaneous original instrument. All statements use Assumption 93.1. $\square$

## 94. Source expressions and the eighteen independent contact equations

**Definition 94.1 (source and contact dictionary).** Use exactly (FA.87)--(FA.88), (FA.103) and RC58:

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad T=ae_0e_1^T+be_1e_0^T,
\quad S=ce_0e_2^T+de_2e_0^T,\quad M=\operatorname{diag}(0,m_1,m_2),\\
\theta=ab/(h_0h_1),\quad\omega=cd/(h_0h_2),\quad\delta=\theta+\omega,
\quad s_0=\sqrt\delta,\quad\alpha=\theta/\delta,\quad\beta=\omega/\delta,\\
L=\operatorname{diag}(s_0,1,1),\quad G=LNL,\quad
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\quad(K_0,K_1,K_2)=(D,T,S),\\
\Delta=\rho_{27,+,+}-\rho_{5,+,+},\quad H_0=(1-\delta)N_{00},\\
V=m_2h_1^2/b^2,\quad W=m_1h_2^2/d^2,\quad\mu=\alpha V+\beta W.
\end{gathered}
$$

Here $u_f=V/\mu$, $c_f=c_*(u_f)$, $\nu=\mu/c_f$ and $t_0=W/c_f$. The inherited scalar $\nu$ and any fixed-strength $\nu_*$ retain their original meanings. Limiting selection in JS does not imply finite optimality.

Put $u=\cos\phi$, $v=\sin\phi$, $z=u/\sqrt\alpha$, $w=v/\sqrt\beta$, $h=(1,z,w)^T$ and

$$
\ell=h^TGh,\quad n=(0,dw/h_2,-bz/h_1)^T,\quad f=n^T\Delta n,
\quad c=\frac{h_1^2h_2^2\delta+a^2h_2^2z^2+c_{\rm src}^2h_1^2w^2}
 {h_0^2\delta+b^2z^2+d^2w^2}.
$$

The source amplitude c_src in this capacity is the c in S; the capacity function c is a different object. Below c always denotes this capacity when it is a function. Define

$$
\Gamma_\eta=(1,u,v,u^2,uv,\eta c,\eta cu^2,\eta cuv),\quad
H_\eta=\ell+\eta tcf,\quad
B(t)=(1,0,0,\alpha,0,\mu/t,\alpha V/t,0).
\tag{FA.122}
$$

The five contacts have sheet indices $\eta=(0,0,0,1,1)$, height signs $\epsilon=(+,+,-,+,-)$, and angular chart bases $b_{\rm chart}=(0,\pi,\pi,0,3\pi/2)$. Their local coordinates satisfy $\phi_i=b_{{\rm chart},i}+2\arctan x_i$. The unknown vector is

$$
X=(x_0,\ldots,x_4,p_0,\ldots,p_4,d_0,\ldots,d_7)\in\mathbb R^{18}.
$$

The equations, ordered with the eight moment equations first and then the value/derivative pair for each contact in increasing index, are

$$
\sum_i p_i\Gamma_{\eta_i}(\phi_i)=B(t),\qquad
P_i(x_i)=0,\qquad P_i'(x_i)=0\quad(i=0,\ldots,4). \tag{FA.123}
$$

The cleared numerator $P_i$ of $d\cdot\Gamma_{\eta_i}-\epsilon_iH_{\eta_i}$ is defined as follows. In any chosen chart let $r=1+x^2$, and let $(U,V)$ be $(1-x^2,2x)$ for base $0$, $(-1+x^2,-2x)$ for base $\pi$, and $(2x,-1+x^2)$ for base $3\pi/2$. In these polynomial displays $V$ is a chart numerator, distinct from the scalar source moment $V=m_2h_1^2/b^2$. Set $Z=U/\sqrt\alpha$, $W_n=V/\sqrt\beta$; write $d_{\rm src}$ for the source amplitude when it could be confused with the multiplier vector. Define

$$
\begin{aligned}
D_c&=h_0^2\delta r^2+b^2Z^2+d_{\rm src}^2W_n^2,\\
N_c&=h_1^2h_2^2\delta r^2+a^2h_2^2Z^2+c_{\rm src}^2h_1^2W_n^2,\\
L_c&=(r,Z,W_n)^TG(r,Z,W_n),\\
F_c&=\Delta_{11}(d_{\rm src}W_n/h_2)^2
 -2\Delta_{12}d_{\rm src}bZW_n/(h_1h_2).
\end{aligned}
$$

$\Delta_{22}=0$ exactly. Pure numerators for $\Gamma$ are

$$
(r^2,rU,rV,U^2,UV,0,0,0),\quad D_0=r^2,\quad H_0^{\rm num}=L_c.
$$

Saturated numerators are

$$
(D_cr^2,D_crU,D_crV,D_cU^2,D_cUV,N_cr^2,N_cU^2,N_cUV),
\quad D_1=D_cr^2,\quad H_1^{\rm num}=D_cL_c+tN_cF_c.
$$

For either sheet $P=d\cdot\Gamma^{\rm num}-\epsilon H^{\rm num}$. The denominators $D_\eta$ are positive everywhere. Derivatives in (FA.123) are polynomial derivatives in the local coordinate. At a zero the value and stationarity equations are exactly those of the original gap; denominator clearing introduces no branch or extra root. Pure degrees are four and saturated degrees eight.

The exact rational decimal centre of X at t=1000 is listed below. It defines an enclosing box, not an assertion that the decimal centre solves the equations.

| coordinate | exact rational decimal centre |
|---|---|
| x0 | 0.0239983886642378607964294310901679274398090903664722197137187518454914256245 |
| x1 | -0.295345657849378476306024301450483432304865657374456698646986628268886428144 |
| x2 | 0.127640893565866832951084082477176300214962315541575619037141303345451632888 |
| x3 | 0.151088636285802408169627202014237321102259249309113798503448321432425648207 |
| x4 | 0.251237409581127356717457548926907910867475688233491094351221514230825083392 |
| p0 | 0.40356105912434429587028385796306861440267440303930150136389554751929146834 |
| p1 | 0.183968107565001260784005926671856498076335410359553001589052683256527679673 |
| p2 | 0.320043755240561323971427131511530770797419136045901918140238020651677504285 |
| p3 | 0.0361481337929972639565176638271383531983401158115725409751968219643484098342 |
| p4 | 0.0562789442770958554177654200264057635252309347436710379316169266081549378682 |
| d0 | 0.0244863499508953549551714115254785990455229653352660072423427775163528545274 |
| d1 | 0.00358535399816408539814614897471262212522535275458846005404812615848843507412 |
| d2 | 0.00715283156818416310756463367571142082407236735174105388329649684474543316655 |
| d3 | -0.0183927422338048386671395313708612800603754221994926300815476732972939276256 |
| d4 | 0.00403186188336576407517441402354141469657869331844789615857271955201630579117 |
| d5 | 21.7811418184010051130038082491418452870010839274827565904191911611069497405 |
| d6 | -17.6924448925415546973374521319795072232789713541765300081920400162650964287 |
| d7 | -11.0558270043314784681815861874335551388404582163945740457886311004049481113 |

For the seed use radius 10^(-16) in each of these 18 coordinates. For the whole $t$ strip use the same centre and the eighteen exact radii in §95. These boxes specify the selected root.

The original source box used in every interval calculation has the following nine exact decimal centres, each with radius 10^(-24):

- lambda_CG: .479508042205945691075728241615
- alpha1: 1.412018697539825943102823246594
- alpha2: 1.185897402486986028204155873343
- beta1: .413330945620125544606320492846
- beta2: .809647491041060318009094562763
- z_CG: .066998926272600209516864472757
- eta0: .279795267654829218213193898783
- eta1: .199570407911600478528148253443
- eta2: .091392615490799158339482855657

The source expressions are (RC.5), (CG.112)--(CG.113), (CG.134).
With the source-box coordinates in the displayed order, form

$$
\begin{gathered}
v_5=(\alpha_1,\alpha_2,-1)^T,\qquad
v_{27}=(\beta_1,\beta_2,1)^T,\\
A_5=\lambda_{\rm CG}\frac{v_5v_5^T}{v_5^Tv_5},\qquad
A_{27}=(1-\lambda_{\rm CG})\frac{v_{27}v_{27}^T}{v_{27}^Tv_{27}},\\
\mathcal N=\sum_{y\in\{5,27\}}A_y\odot(a_ya_y^T),\quad
\zeta=(z_{\rm CG},59\lambda_{\rm CG}/128,\lambda_{\rm CG}/2),\\
S_0=\operatorname{diag}(\zeta)-\mathcal N,\quad
H=1000\eta_0\operatorname{adj}S_0,\quad
Q^{0j}=\eta_j\operatorname{adj}S_{0j},\\
(h_0,h_1,h_2)^T=He_0/\sqrt{H_{00}},\quad
(a,b)^T=Q^{01}e_0/\sqrt{Q^{01}_{00}},\quad
(c_{\rm src},d_{\rm src})^T=Q^{02}e_0/\sqrt{Q^{02}_{00}},\\
m_1=1-h_1^2-a^2,\qquad m_2=1-h_2^2-c_{\rm src}^2.
\end{gathered}
$$

No singular matrix is inverted. All nine coordinates vary, including all
three $\eta_j$. Off-root these define comparison expressions only;
source-root TP, ranks and original optimality identification remain
Assumption 93.1.

For completeness, write $a_y=(\sqrt{y/128},\sqrt{(64-y)/128},1/\sqrt2)^T$
and distinguish the source matrix $\mathcal N=\sum_y A_y\odot(a_ya_y^T)$
from the height matrix $N$ in the first display of this section. Then

$$
S_{0j}=\begin{pmatrix}
\zeta_j-\sum_{y\in\{5,27\}}(A_y)_{00}p_{yj}&-\mathcal N_{0j}\\
-\mathcal N_{0j}&\zeta_0-\sum_{y\in\{5,27\}}(A_y)_{jj}p_{y0}
\end{pmatrix},\quad j=1,2.
$$

All radicals denote positive roots. In interval evaluations one can use
(RC.3) for $G$: its diagonal is
$\delta\sum h_i^2\Delta_{ii}$, $b^2\Delta_{00}+a^2\Delta_{11}$,
$d^2\Delta_{00}+c_{\rm src}^2\Delta_{22}$, and its off-diagonal entries are
$s_0(h_0a+h_1b)\Delta_{01}$, $s_0(h_0c_{\rm src}+h_2d_{\rm src})\Delta_{02}$,
$a c_{\rm src}\Delta_{12}$. This is algebraically the same $LNL$.
The gauge $Y_{22}=0$ is fixed throughout; at report multiplier zero the
two report-sign rows coincide and are included only once.

## 95. Rational boxes and preconditioning witness

**Definition 95.1 (exact rational witness).** All decimal entries in §§94--99
are rational numbers with their displayed digits, not floating point values.
The coordinate order is $(x_0,\ldots,x_4,p_0,\ldots,p_4,d_0,\ldots,d_7)$.
The centre is the eighteen-entry table in §94. The seed radius is $10^{-16}$
in every coordinate. For the strip the radii are:

| Coordinate | Exact radius |
| --- | --- |
| $x_0$ | $0.000006761993587113994445842634178144602240580569310515161143597295$ |
| $x_1$ | $0.00001909166870775727992548294915271800415210011902597737243278185$ |
| $x_2$ | $0.00000576370965544218547669681442936480818216738074780938112826528$ |
| $x_3$ | $0.000000200319989426527288038057603917082547438184668070464553125534$ |
| $x_4$ | $0.0000003072091903292812340727985408350138921392151584905019172839845$ |
| $p_0$ | $0.00000923899159127341094528761555702862378160696139561701848702143$ |
| $p_1$ | $0.000001937612893327679725943882524131604114451510018277767819587495$ |
| $p_2$ | $0.00000655475919025580098848599222483946625113410709916376524851637$ |
| $p_3$ | $0.00000542899914227639280601819134136207227747564613313373355517248$ |
| $p_4$ | $0.000008427238745925139401811533916374413640813969653134532015658865$ |
| $d_0$ | $0.000000800823523742675546667615068988807767441824381899632603186881$ |
| $d_1$ | $0.00000006698602207943754315896825231995631285014150271899353937133275$ |
| $d_2$ | $0.0000002819074118617448006610255852707087950607821094871617531661145$ |
| $d_3$ | $0.0000008549221603182385285786880644213512954941700614053355260208275$ |
| $d_4$ | $0.00000002429556829182523019983292383275904828013799307658752001229685$ |
| $d_5$ | $0.003329062046329244115510966240895051922766518946611688977049175$ |
| $d_6$ | $0.00272214511421723779859411793204890296953793919160356279071039$ |
| $d_7$ | $0.0016555800426521794253570651416496512049639846958807520293175$ |

The rational $18\times18$ matrix $R$ is specified by the following column
blocks, with row and column indices $0,\ldots,17$. These entries define $R$
exactly; no matrix inverse or approximate root is a premise.

| $i$ | $R_{i,0}$ | $R_{i,1}$ | $R_{i,2}$ |
| --- | --- | --- | --- |
| 0 | $-0.20266380172106673378962119192730179168342196305893325930294702695$ | $-0.03640275308156547466525806231498003950091550123606079564077425266$ | $0.61751940181199260697284473548014005160808392189274099946266431962$ |
| 1 | $-2.3551013749237650083986973496189468593318331448646264382872792713$ | $-0.18433695605036703852167133170282893697621695278349495172517585179$ | $0.48136633409620466751070457062809440434500762710801015160627444864$ |
| 2 | $0.67909683105182863077068934076573790549741046245564636585726785811$ | $0.05419116861628247846447361259359256029671855251089830857941506599$ | $-0.16789766197434806132677402097439814685794949366093893370693744421$ |
| 3 | $-0.0068313797247007740837284077235981710549721774310349399984254475379$ | $-0.00057131628229389084526930862160118147734517718288795408601734193497$ | $0.0024232474624184824175186893436438886514964978581663566129457441501$ |
| 4 | $-0.010478371825379589595635436167523663084581875816245068405903601913$ | $-0.00087631850036430746432976162728192914182022243033905342357344488419$ | $0.0037169194159003671348836062977403042670492169085450698337195213415$ |
| 5 | $0.20548537446585590262562193702848632547693518313350246189472976868$ | $0.4975592206426673706991793044943334558735075719377908705959285611$ | $0.027150282715681589734512037431499767211517642964870847052225113519$ |
| 6 | $0.12500869092940291562443388551041191996208608639523243165972082998$ | $-0.17462163358476937976038064757846146115687358336908425256009363861$ | $0.66486175486300981349735825399593448090616022131948590651449436062$ |
| 7 | $0.66923216684949969339364927894105091125157850607536373861322181898$ | $-0.32296048257570546604722626657033341985654620294377367036315487582$ | $-0.69191492586115911524429167759614903586823964634288835048302804307$ |
| 8 | $-0.00022788576822523806389123703020962136358489279534920855533871760175$ | $-0.000019058353529869552606868755401450908990539325062329220781710635565$ | $0.000080836321772068217496943152089390908274383430929988429517988064455$ |
| 9 | $0.00050165352346672642018613555026046467298503737539115562351677440812$ | $0.000041953871337344661034478409862876048892164809422767183503240909175$ | $-0.00017794803930435620507555698337460315772739692896475238196606320507$ |
| 10 | $-0.093671915217622191554282876713122289255183874941526463401504545901$ | $-0.0074978421611010600564239069543386468010204845765849115261115607506$ | $0.023802208509862292341509077650135589155244343285794007595162416156$ |
| 11 | $-0.0074978421611010600564239069543386468010206127045560448247964887235$ | $-0.00061136231851792991944676522638171212491680486621710542025378294415$ | $0.0022195629086588772397734324182519718698873269287948853047545050343$ |
| 12 | $0.023802208509862292341509077650135589155242455807122226220835703168$ | $0.0022195629086588772397734324182519718698875803650745563559538147002$ | $-0.01486485636858955030036958867308780447583784863233045493354215022$ |
| 13 | $0.10062118583265929809170747575215907761891217472714219171846458621$ | $0.0080328012091328630364093000607254121050157821199475054531588330544$ | $-0.02497101233042632250707051000542628367669588394366670157804664477$ |
| 14 | $-0.0077284049583814179482017469003497040815834802165325772792340837613$ | $-0.00025644472709497616039737812018317981795146314907204149109616175388$ | $-0.0081940412134287677530763672568521522281043136593757898563317126592$ |
| 15 | $1.7759050590387228141298322951896467205680336875320892555848076418$ | $0.14745762289101630190791681194379885620129756870592626532759675825$ | $-0.60012870521097127681810872381845695785869373948644006223006803336$ |
| 16 | $-2.0430518522086283908863428022969916484287044951799817242655694327$ | $-0.16926111433519477747312107125780631710273160372816721195178554527$ | $0.67979360478936461139129940998591476825939614828619322373220223835$ |
| 17 | $0.39455616515416135212944735614108647950481926280870441880384109243$ | $0.028122014117387671987570223704336910581987452810859056341570118613$ | $-0.0032212732547290249709966325557934990097057578453511710037378528812$ |

| $i$ | $R_{i,3}$ | $R_{i,4}$ | $R_{i,5}$ |
| --- | --- | --- | --- |
| 0 | $0.17937083227280056075011710374915197188256505661342229847149647932$ | $0.63540341280879351267665707042766942775157248848138152692559605775$ | $13.399441225927841891103212524346828595156711930514046863132145154$ |
| 1 | $2.5377474131624088687045772321379036600166560699090420782357300086$ | $-0.32918537867178386684652966014373168902932199818832649648525634774$ | $42.673149844101304795620485385114912634480275954664297422273280617$ |
| 2 | $-0.72979291512072837420582596045325635970036700411538390556513306191$ | $0.061400210527607131355358396675168547069586174405219301600124860784$ | $-12.796127254989132970238783133638102656576180019586066314578083371$ |
| 3 | $0.0072916357903900495496260298152808555727586983228639491825346898392$ | $0.00022832078239070753106850168062539179907770036679587205679407352718$ | $5.2314202484708977572299576709297630818490242252957574070108784667$ |
| 4 | $0.011184339636499883530918013483814302521352858798189793166446898277$ | $0.00035021183856914154879765018206082085372521765459467504915697980356$ | $-46.240961644466558424653573731836179974029999685764116437121759868$ |
| 5 | $0.29575391641624443450101765915965120472283099354488500181184393053$ | $0.024052196991282917109742371089152152406611572174940470520236896317$ | $-4.5634160586084955868069941883348597107804351972079724696569064988$ |
| 6 | $0.052334626805074245830727972836317655916345591074171281170467069292$ | $-0.7241137503299234354334464595259081325016580006372640768213967465$ | $6.1897856153637803686348033452764652776115936261879765422423646872$ |
| 7 | $-0.34779633068990929258266698726776326029927038659869188568610163664$ | $0.70007070330110623709912940985772369802490448590909154316219574998$ | $-17.106506871827396543807574537107408836681508060929791552131396311$ |
| 8 | $0.0002432393002109776428334873762506938614666467124968362265539926189$ | $0.0000076164785144003747376199503663984027768910117435875971746685089501$ | $1.4348869272632340531082988700485183259018146790355207631833795214$ |
| 9 | $-0.00053545183162036539191213210445629420138373701337912527044470606753$ | $-0.000016766440980119150162941371334116332650088314262221572726796971188$ | $14.045250387808877708871466510117284943948265735199574114186320719$ |
| 10 | $0.1006211858326592980917074757521590776189135643608642132143015807$ | $-0.0077284049583814179482017469003497040815722104920533742831068422977$ | $1.7759050590387228141298322951896467205678217698382158591226331309$ |
| 11 | $0.0080328012091328630364093000607254121050160456076669479862958924028$ | $-0.00025644472709497616039737812018317981795108349375030883955760754954$ | $0.14745762289101630190791681194379885620127507155743744677070493931$ |
| 12 | $-0.024971012330426322507070510005426283676693789576904377804164590168$ | $-0.0081940412134287677530763672568521522281071007529644231898891218432$ | $-0.6001287052109712768181087238184569578585877349683952799098612914$ |
| 13 | $-0.10812643136918434365788612539690256654357541504609841084736493171$ | $0.0089895908019985155935165750030494408990706073009433317044106953782$ | $-1.8975741825950520881210739148714022584102593285222710202549634748$ |
| 14 | $0.0089895908019985155935165750030494408990833273320956205112071000377$ | $-0.012340664497750842674272911578498420936653124024507482284084459874$ | $-0.024992259788489775348175085652527928822179586204336812685218714704$ |
| 15 | $-1.897574182595052088121073914871402258410505113877384041075756556$ | $-0.024992259788489775348175085652527928822390701892758716969493682679$ | $-465.27248114125093496317341199744262899345789499654813883042480182$ |
| 16 | $2.1837420443247241585671823872200706444754082310125637946020226102$ | $0.016526017049720469236505409917998797895684294851860318402163745858$ | $717.94122544968986706237877547432884963809807407958447890688077278$ |
| 17 | $-0.43039802192046280212142507110569081390420271438080003863612176054$ | $0.14434998758340849187066298518241208760726881637943498616485086227$ | $-673.20292262914486026353027095453648106919596408517351760584030956$ |

| $i$ | $R_{i,6}$ | $R_{i,7}$ | $R_{i,8}$ |
| --- | --- | --- | --- |
| 0 | $-14.733845758983852891842919811802812060276356615612750269421363603$ | $-5.3759921005902176494847351251244959590533131166328944081867419218$ | $0.027461439166317756164850424410332757622959378874357862789802226654$ |
| 1 | $-49.233311645589182590098020355619936051209041614052825905766202241$ | $11.208403585922618585577960310580570523796590484106625421750275321$ | $0.34200680760982137369593402082815722870728570056459593776140278324$ |
| 2 | $14.726641138452499284634828180627085367704037634330957714478837032$ | $-2.9117399101108493100513641558222772213716373389163815046762840377$ | $0.15754650567397435016732731466647226505441680922509208266232802018$ |
| 3 | $-8.1867908262313120524684191606654393424733142047405685341243647416$ | $7.9381228379006710934535165844395664882995669960533411186212237224$ | $-0.029907298758115912939219152756663035995585690691403257998875673663$ |
| 4 | $72.996129906005084950678578820090776994538608164709205879174722846$ | $-72.222431509826513258306597234122307601754527997089506673272463222$ | $-0.045873573027588996099970189866742815664296792339821931159035036262$ |
| 5 | $-1.4980545689200794834984758877184249344306364114614103117893530348$ | $2.4163362357093146445613812667690903830555763259145113497357312244$ | $0.0066571610275721903303284902079699080116142068165628796513986130559$ |
| 6 | $-7.9180909622917523833788300646536121687217291069778792175120226067$ | $3.7135020762636046140526415259348664044980525913327075929775413849$ | $0.22069596344838071499809664563953733783377015839011735664433586267$ |
| 7 | $20.762710911623653382934026462740033306110703405217155640576961336$ | $-7.2348775472029636540959045770391725302837152170209738369426017655$ | $-0.2285516604051944289278287789679972179468528508463635983689046905$ |
| 8 | $2.8481834515273188392702084293665396278429112884985004585332164614$ | $4.9648162997794494016774209701877490468281715996172938795935064613$ | $-0.00099766782519668546031513199124758973125811765548936980058249514121$ |
| 9 | $-14.194748831939140355326928939734535830800771764811823866007891313$ | $-3.8597770645494050061955391858525333040981209835840781965358433002$ | $0.0021962037544382090597187751117375618327257541451794212366790094991$ |
| 10 | $-2.0430518522086283908863428022969916484296004891103869416652590099$ | $0.39455616515416135212944735614108647950522319435224514224313049543$ | $0.21308638806341507407240793164092075788486826406587892501812744534$ |
| 11 | $-0.16926111433519477747312107125780631710280163158312587967998992941$ | $0.028122014117387671987570223704336910582026962489309789077571947021$ | $0.49839438612209635870713860716746655587065134487142038870928455064$ |
| 12 | $0.67979360478936461139129940998591476825968022342852625557644090991$ | $-0.0032212732547290249709966325557934990098517013395723888931511687553$ | $0.0032380762874732307320999057249571171273507956139772362110421497762$ |
| 13 | $2.1837420443247241585671823872200706444763414329509835162263954654$ | $-0.43039802192046280212142507110569081390462266641298523801220979171$ | $0.28847684622137110691346782803793497375171171786502942812448654427$ |
| 14 | $0.016526017049720469236505409917998797895481213273022277446540300397$ | $0.14434998758340849187066298518241208760729311800477051015804249685$ | $-0.00054806172086651220482009010090097456300447875220899678366881801941$ |
| 15 | $717.94122544968986706237877547432884963831317562502964508482529003$ | $-673.20292262914486026353027095453648106927957979801292229990696508$ | $-5.0763528665171449600451420526842821026935180308218762136867132872$ |
| 16 | $-1114.0366096340872354999721183843319444441416048240284490497438095$ | $1058.98612536376557311329440433093719360257704453122735098032467$ | $-0.92653727861593611178642302209800757493727246271996338085755706561$ |
| 17 | $1058.9861253637655731132944043309371936027506465909424356024737962$ | $-1040.6727572020745768432742284430353550538321101012299451125377581$ | $2.6214579373098843182049407101011641922019080932415099681470230155$ |

| $i$ | $R_{i,9}$ | $R_{i,10}$ | $R_{i,11}$ |
| --- | --- | --- | --- |
| 0 | $0.070145217734320996929823105345929649994080594208007392549421473284$ | $1.753892761558921060370600967819118261220172510548148150675962867$ | $0.37668757053501149060851900063927069090215062105944181557612798853$ |
| 1 | $0.97564092266843771612634064343003600272969527621925935638930119515$ | $25.421997874509007571904384221490071222510039740941583946439476403$ | $5.437416010796903235517520796591366441732366694760321810044631106$ |
| 2 | $0.47160540529285293092504283302471119727485641574173593662296989208$ | $12.488362867372063485225437984752941020262538738090484406112736856$ | $2.6668839202870513750276432253282053192161302782014155182115245332$ |
| 3 | $-0.023746124493718334089703355372003135307682868635454076059626295979$ | $-0.063739625463967047207228692344337782424897215686104285164952874217$ | $-0.025310137864123673278887428473355818606470051799560930464000492751$ |
| 4 | $-0.036423201737308363299824484140720605731461649140576421348049089527$ | $-0.097767584666234368042526858948025218742965179641977991441140054431$ | $-0.038822177390164509263836817860840889459815796104608304230345907153$ |
| 5 | $0.013798177247358478665413696487519481061988883937965347093712676611$ | $0.31272744227466093810854310475929734791569920534184886704886707502$ | $0.067872918239823058016648873316956152580300223416442762621894632898$ |
| 6 | $0.64067719443947928529978564323656025539222588845989049268116082043$ | $16.793992286201773166795840979279663902821139662660559099287408869$ | $3.5898991873991093280985659606604109139658133319204617521839386481$ |
| 7 | $-0.65542699836553405673544517997542298215590610516687019846615167418$ | $-17.109274095952173832173090473172956259696704068540510092228900274$ | $-3.6587864102021613380643951498146764641380739783813457870149084152$ |
| 8 | $-0.00079213922233845278308210554530542600750840386527423982267039284435$ | $-0.0021262693775789650772069163888484998526169418060730298567600526862$ | $-0.00084431263426878961893522990239983530089141923372086982005678336229$ |
| 9 | $0.0017437659010347455533279457966486717091977571237254661928751509704$ | $0.0046806368533186923459133055228435088124345547816240156401219326012$ | $0.0018586171974977415681155457397092328928415799628048830366435074186$ |
| 10 | $-0.081693093564939425721104858757427245993105431988469051820654167031$ | $-0.29251750001002657515199725783784410800127961053575317535463165045$ | $-0.36653043725700515753625818119315854352579138694491725233039952204$ |
| 11 | $-0.014673826742906627939354460913612769235932802826755757955402078951$ | $-0.17889893343385724816974153401065341435058984729189865042539474861$ | $-0.028688830902641490688330549922715626654606236589794957941677485192$ |
| 12 | $0.24891998394377601252405621520214026592708124807694633810305097674$ | $0.6438608891718916979857648235814007773561736567710403336728072397$ | $0.074916271034317904317085524776756499985789443887627229784857045558$ |
| 13 | $0.07230377629968118844300911638305684704085685896158023403167273242$ | $0.47343296058973906378436606523834019864075050732758767668094105169$ | $0.39495610630534361764918588871974234280137058392492627888514167241$ |
| 14 | $0.25612896833699729215409718619427726880311428425143086431324389303$ | $-0.66825127695361750371825040801631502817762194174768412840089922281$ | $-0.051231960572010378310321535350203896422168587392970979793663969942$ |
| 15 | $5.4012694743298241597964126007998844480326615136945954583193446906$ | $12.452876005330789370903768826333053715703741274427197223828982972$ | $6.641331213183319782367788224804945508923872446677437304231327317$ |
| 16 | $-5.9391634319417539406670810595211601259151846187884310685796498709$ | $-15.024371062874418980496563904897479139496197013871821339797127641$ | $-7.6623059360458923180785929878964328747784415297117673880912240338$ |
| 17 | $-2.1670442474100659834198390514789511208520357477350889689205172545$ | $5.0369886865803690925574992804484935925964840210933121497210297526$ | $1.7443924542034568307199904039736501241649768845069289615994116737$ |

| $i$ | $R_{i,12}$ | $R_{i,13}$ | $R_{i,14}$ |
| --- | --- | --- | --- |
| 0 | $-1.7563919846474781370431439850556727704767210584349771942049680206$ | $0.36252819753860949950559325392496961397757886362161925241099743013$ | $0.071967548655972087834328748982016780797244609078040435463278779586$ |
| 1 | $-25.428940661825385680963567373731764215332439898842890620732081305$ | $5.309771701724622240441909300354297303744774391983105257785110338$ | $0.19867681931698038579790756379276813705421507298064190469990922916$ |
| 2 | $-12.486306530283353287315196542415233597555995189693163743939890367$ | $2.618665444662708569333742786302303937184840954917369551240977088$ | $-0.060059921215999031533035777226039172266499522182590809660534887169$ |
| 3 | $0.078937419277817715746754417390302281716412536099276619765206746296$ | $0.015233644136089732743916814159910013365177399319986656187394222558$ | $-0.43827875999928658269937912287562116218880614214496903119419506305$ |
| 4 | $0.12107885426689419674148592858532696124140488187144941450897104593$ | $0.023366258932481380152268045559949274661604649687710825038721011589$ | $-0.67225772764959051373301364403186176393183125987418713203833164256$ |
| 5 | $-0.31409312131566695104365552696718470624082104594078193889772166716$ | $0.062910346446540539380223801523265701587024431132067895884818618509$ | $0.039365245582453860938164853809655688561549421948025914743259630229$ |
| 6 | $-16.795842239428765479937321074315535516664067321063636649438170419$ | $3.5128272358012844327398524082803323327281598451592815152107641349$ | $0.052330530824956403720466642447740298424889816737212588297298101296$ |
| 7 | $17.113098780280621501788345045601611849706711067462678081206827353$ | $-3.5751270934845952832076788331704372824985552808869417313350828506$ | $-0.10925981136526547613307715099250695661265865839443515456757879412$ |
| 8 | $0.002633247624751403046468409977230444938314025020837493425703054599$ | $0.00050817416637965629337691125291636698856853911151741632969363714531$ | $-0.014620398212985732358622647398948395963993093138811555741823364062$ |
| 9 | $-0.0057966671609404738538368542961220717400890157327132746663805308248$ | $-0.0011186629296093452057742878860771188052072685769307731749093138061$ | $0.032184433170840943833068302134059365590208992129878122797767805645$ |
| 10 | $0.54223257547504616216753750455780120454852235254239400975929994637$ | $0.21042817012873806962437022913189648931411764243846366633483531103$ | $0.0083456766328574788082978916765995549219866296165957340670738830371$ |
| 11 | $-0.32112462100911421828080184433275846761096250414196332479762034991$ | $0.016791932943347688353806514644075447684116917132572636964688873784$ | $0.00069795870516039556294708790848133748816614547678009842802849069853$ |
| 12 | $-0.64377200547253251146095555832618193863685559895016469742095343394$ | $-0.052025567139569020423172901985146991354334921692743640247831147978$ | $-0.0029604033940044139006163335156654575583995778494021233898771797596$ |
| 13 | $-0.22312818735404320584927180599865481525874859360455846407269213339$ | $-0.22613709957078559203611236576120470139550626088198111955230893652$ | $-0.0089079566476347501455451777117694048539837462947586980871590638527$ |
| 14 | $0.66824678851492614331031550335172039257035830510816908369128375801$ | $0.019025760916645432807551322216504782373208351863598594225181151245$ | $-0.00027893214770422220905795624125750711677365389572984280568140450802$ |
| 15 | $-14.570467539683446043985186113484892778024060049995800341452875818$ | $-3.965068779412889435999334815190339751581837326620600322210971725$ | $19.573773329072670734500708839705820928758397163006078629750710616$ |
| 16 | $17.809863812489794123874890468863155361750406281765016047087371661$ | $4.5632669822761218702767909394682917723904046443368887099136277164$ | $74.302793846679627248902950342924278662399341715337607049912148423$ |
| 17 | $-6.5515030001748088754521351340315264855650088356777612009160508366$ | $-0.90224556080822020608156307800535799942999435916057845372704894423$ | $87.126703844763203553189581026417633968393539398936926888198656171$ |

| $i$ | $R_{i,15}$ | $R_{i,16}$ | $R_{i,17}$ |
| --- | --- | --- | --- |
| 0 | $-0.043868788119445715039589006877676681360813746946480727510049165746$ | $0.081345754968962764872706136543900760512781949274878415896380227155$ | $-0.048184403539326629142602178499514284811597775479993076585359299759$ |
| 1 | $-0.12110612982701274271111398632303646052313583844475996977784675307$ | $0.22456671324778883532606965005022930155473435374982295390457194578$ | $-0.13302000991643974412957105005745556824259634315817037578974322479$ |
| 2 | $0.036610333511430833347136851697812485336576078650234820364129284569$ | $-0.06788642556170268704299943946522746840632795147478916527694382458$ | $0.040211894589405516350317138727022490395381005002821824600565031527$ |
| 3 | $0.26715871832139453857777987961248197112535154478151851850106910745$ | $-0.49539156584909306428096381477641482143971234561633124687528139358$ | $0.29344059967184748112295359516643629338708302998051824782006267915$ |
| 4 | $0.40978374790694868232362060792452214447213728436378376338883656801$ | $-0.75986070681368608403063597302146303857770535345104058598743577275$ | $0.45009644258336970294987162697362783316484440835360730949987411964$ |
| 5 | $-0.02399561538467533906849288768404226473402255428908534024164501799$ | $0.044494993663753304418628491286810531413188831712910372501242594591$ | $-0.026356196841397490717371568924340160784659561344560861992088865666$ |
| 6 | $-0.03189877954454452498009079429114934941457199835129763160910419329$ | $0.059149805952566770893393025660097957691818294440038868640399576359$ | $-0.0350368389890632675521110459776780992001404298847056636348497632$ |
| 7 | $0.066600788887029741407578734433575457622521978510808409574404869979$ | $-0.12349763204747477209303265707078094605934462882623872030215757491$ | $0.073152677001980717818935543564534789656697816768469311607668254417$ |
| 8 | $0.0089120605523663372710302655134840167629163378808595078304623366472$ | $-0.016525605676350990973128482977156251849469670795907398548676706776$ | $0.0097887892606676264343442079977160475852618077196021550488841195919$ |
| 9 | $-0.01961845451017621463002531797186786023684161765015240197575910816$ | $0.036378438107505687754139623101028708803803193960659026876300673427$ | $-0.0215484304321875859837971366602325772571572760338292903400712218$ |
| 10 | $-0.0050872195421075046304023897361157630932497751021438196953082423143$ | $0.0094332150963194812665304903114791451460409116835858906800790030544$ | $-0.0055876774768118122652600746071491161722951181904035357926743600293$ |
| 11 | $-0.00042545012473845390646067830254424762287463682634389540773202915078$ | $0.00078891081978961666378975979373872515092090848224076848117265963607$ | $-0.00046730400758819808156263051244563118921760669296039837539693339211$ |
| 12 | $0.0018045537421384805111471130866068104296385943719992799677472119065$ | $-0.0033461782927906509317086049649121300560900216261582747554713115788$ | $0.0019820776786186075627246745425067673677826740955967330595101026395$ |
| 13 | $0.0054299648945993185443647136703636396868372856588136415042770476262$ | $-0.010068766718685614292102134307849643729093749148605244485761222147$ | $0.0059641405860895841100477749941060757652139367534526060497836586742$ |
| 14 | $0.00017002684565278777725440747285378389342706369579066680692000647742$ | $-0.00031528024177368320484581967453691268819577057466378105221581954037$ | $0.0001867533272436394904215101921301897814118088885779734631967848015$ |
| 15 | $3.8957552344469856737107239735412545790566290958425230170602846132$ | $153.73494909784439222733235547264245235134403789465079549290173171$ | $-24.658370994345261964427508034949100775045533192629899884118895531$ |
| 16 | $-6.0965725749017161130527508521082060489218553527014884650440562991$ | $-167.10103928066637686409548040477503144450977489425086519973019941$ | $38.925783296054961435141075674544713705063436850249769065205937805$ |
| 17 | $5.9113934894589715310597530177465321785267007155808869974146172663$ | $-4.3160177507971017274709668823175104177207295603616535672779822195$ | $-38.513202298337234815637630176408907135950964598450187741242014406$ |

## 96. Uniform contraction and exact contact-root inclusion

**Theorem 96.1 (root inclusion and regularity).** For every source point in
RC.4's entire nine-coordinate box, the eighteen equations (FA.123) have a unique
zero in the strip box for every $9999/10\le t\le10001/10$. At $t=1000$ they
also have a unique zero in the seed box, and it is the same zero. The
Jacobian with respect to the eighteen unknowns is nonsingular throughout
both boxes. These are statements about the comparison expressions; TP is
asserted only at the source root under Assumption 93.1.

**Proof.** Let $\mathcal F$ be the ordered left sides of (FA.123), with the targets
subtracted. Denote its centre by $\bar X$, its radii by $r_i$, and its
Jacobian by $J$. All interval endpoints below can be obtained using the
dyadic denominator $D=2^{220}$, with

$$
\operatorname{down}(q)=\lfloor Dq\rfloor/D,\qquad
\operatorname{up}(q)=\lceil Dq\rceil/D.
$$

An interval sum or product takes the extremal endpoint sums or four endpoint
products and rounds outwards. Division uses the outwards reciprocal followed
by multiplication, on intervals excluding zero. For $q=a/b\ge0$, a square
root lower endpoint is $\lfloor\sqrt{\lfloor aD^2/b\rfloor}\rfloor/D$ and
an upper endpoint is that integer plus one, divided by $D$. Squaring an
interval containing zero uses lower endpoint zero. These rules involve
only integer arithmetic and integer square roots.

Evaluate source amplitudes by the positive-pivot adjugate expressions of
§94, then $G$ by its expanded entries there. Evaluate ascending polynomials
by Horner's rule, with coefficient sums and matrix products in increasing
indices. Polynomial differentiation and multiplication are exact coefficient
operations, followed by the stated endpoint rounding. In the following
Jacobian formulas $g_{ij}(x)=\Gamma^{\rm num}_{\eta_i,j}(x)$,
$D_i(x)=D_{\eta_i}(x)$ and $P_i$ use contact $i$'s own chart:

$$
\begin{aligned}
J_{j,i}&=p_i\frac{g'_{ij}D_i-g_{ij}D'_i}{D_i^2},&
J_{j,5+i}&=g_{ij}/D_i&& (0\le j<8),\\
J_{8+2i,i}&=P_i',&J_{9+2i,i}&=P_i'',\\
J_{8+2i,10+j}&=g_{ij},&J_{9+2i,10+j}&=g'_{ij}.
\end{aligned}
$$

Unlisted entries vanish. Put $E_R=I-RJ$ and

$$
q_i=\sum_j\sup|(E_R)_{ij}|\frac{r_j}{r_i},\qquad
\zeta_i=\sup|(R\mathcal F(\bar X,1000))_i|.
$$

For the seed let $e_i=\zeta_i/r_i$. For the strip use

$$
e_i=\frac{\zeta_i+\frac1{10}\sup|(R\partial_t\mathcal F
 (\bar X,[9999/10,10001/10]))_i|}{r_i}.
$$

Precondition before bounding this derivative: $t$ is one common parameter.
The only nonzero moment derivative rows are $\mu/t^2$ and
$\alpha V/t^2$ in rows 5 and 6. At saturated contacts the other derivative
rows are $-\epsilon_i N_cF_c$ and its local derivative. Thus the strip
centre-displacement bound is the scalar mean-value theorem applied to
$R\mathcal F$, with source coordinates held fixed inside their full box.
All occurrences of the source and of $t$ remain over-enclosed; none is
replaced by a root approximation or treated as an independent parameter.

The resulting rational upper bounds are as follows. The seed $q_i$ column
is in units of $10^{-15}$; the other three columns are dimensionless.

| $i$ | Seed $10^{15}q_i<$ | Seed $e_i<$ | Strip $q_i<$ | Strip $e_i<$ |
| --- | --- | --- | --- | --- |
| 0 | 17 | 0.0000193 | 0.00041766 | 0.66740735 |
| 1 | 130 | 0.00009088 | 0.00074404 | 0.66752689 |
| 2 | 58 | 0.00003112 | 0.00094428 | 0.6675121 |
| 3 | 5 | 0.00002838 | 0.00170517 | 0.67794482 |
| 4 | 31 | 0.00007981 | 0.00266087 | 0.73366237 |
| 5 | 5 | 0.00000869 | 0.0001267 | 0.66679263 |
| 6 | 73 | 0.00002567 | 0.00347506 | 0.66792342 |
| 7 | 81 | 0.00004112 | 0.00122273 | 0.66768712 |
| 8 | 2 | 0.00000254 | 0.00000491 | 0.66678763 |
| 9 | 6 | 0.00001148 | 0.00001008 | 0.66726904 |
| 10 | 5 | 0.00000363 | 0.00064514 | 0.66743931 |
| 11 | 2 | 0.00000043 | 0.00114617 | 0.66652024 |
| 12 | 3 | 0.0000014 | 0.00091549 | 0.66724648 |
| 13 | 5 | 0.00000388 | 0.00066279 | 0.66744546 |
| 14 | 3 | 0.00000065 | 0.00831084 | 0.6642485 |
| 15 | 430 | 0.00311194 | 0.00001337 | 0.66672836 |
| 16 | 634 | 0.00430733 | 0.00002173 | 0.66678341 |
| 17 | 518 | 0.00260262 | 0.00001978 | 0.66684789 |

In particular $\max q_i<10^{-12}$ and $\max(e_i+q_i)<1/200$ for the seed;
$\max q_i<1/100$ and $\max(e_i+q_i)<3/4$ for the whole strip. Every entry
in the table follows by the displayed interval substitutions with the exact
rational $R$, centres and radii; strictness also follows directly from the
rounded upper entries.

For the weighted maximum norm $\|v\|_r=\max_i|v_i|/r_i$, the map
$T(X)=X-R\mathcal F(X)$ has Lipschitz constant $\max q_i<1$, and
$|T(\bar X)_i-\bar X_i|\le e_i r_i$. Hence $T$ maps the closed box strictly
into itself. Iterating $T$ gives a Cauchy sequence by the geometric-series
bound on successive differences; its limit is a fixed point, and the same
Lipschitz bound proves uniqueness. For every enclosed Jacobian,
$\|I-RJ\|_r<1$ implies $RJ$ invertible by its Neumann series. In finite equal
dimensions both $R$ and $J$ are therefore invertible, so a fixed point is
exactly $\mathcal F=0$. The seed box lies inside the strip box, so their
zeros at $t=1000$ coincide. $\square$

## 97. Double-root deflation and the complete circle inequalities

**Theorem 97.1 (all eight inequalities and all zeros).** At the selected
root the four distinct capacity/height gap polynomials are nonnegative on
the whole circle, and their zero sets consist exactly of the five stated
contacts. With report multiplier zero they give all eight report/height
inequalities.

**Proof.** At the selected solution the four gap polynomials factor exactly as follows:

| eta,epsilon | angular chart | repeated factors removed | remaining degree |
|---|---|---|---|
| 0,+ | base 0 | (x-x0)^2 (x+1/x1)^2 | 0 |
| 0,- | base pi | (x-x2)^2 | 2 |
| 1,+ | base 0 | (x-x3)^2 | 6 |
| 1,- | base 3pi/2 | (x-x4)^2 | 6 |

These are exact factors because the value and derivative equations in (FA.123) vanish at the exact selected solution. The two pure-positive contacts are distinct; chart changes transform the local root x1 to -1/x1. Synthetic division with the boxes of §95 encloses all coefficients of the exact quotients. Remainders need not be numerically assumed zero: their exact zero follows from (FA.123). No interval residual is silently rounded to zero.

Every remaining quotient q(x)=sum a_k x^k has even degree n and is strictly positive for every real x, including the homogeneous point at infinity. For each sign sigma=+1,-1 the following rational witnesses prove positivity on [0,1] of

$$
(1-y)^nq(\sigma y/(1-y))
=\sum_{k=0}^n a_k\sigma^k y^k(1-y)^{n-k}.
$$

Its initial Bernstein controls are $a_k\sigma^k/\binom nk$. Exact dyadic de Casteljau subdivisions yield strictly positive lower controls on a covering partition. Bernstein basis functions are nonnegative and sum to one, so positivity follows on each entire closed interval. The leading coefficient, also strictly positive, checks y=1/infinity. This proves the circle inequalities, not sampled signs or merely positive curvature at the selected contacts. Consequently the only whole-circle zeros are exactly the two pure-positive, one pure-negative, one saturated-positive and one saturated-negative contacts listed. The report-sign copies give all eight original inequalities: the report multiplier $\lambda=0$ makes the two report signs identical, so their duplicate rows are not counted as independent Jacobian equations. All height and orientation cases, axes and each chart's infinity are included.

For clarity, the original matrix multipliers matching the eight-coordinate dual are the report multiplier $\lambda=0$ and

$$
Y=\begin{pmatrix}
d_0&\sqrt\alpha d_1/2&\sqrt\beta d_2/2\\
\sqrt\alpha d_1/2&\alpha d_3&\sqrt{\alpha\beta}d_4/2\\
\sqrt\beta d_2/2&\sqrt{\alpha\beta}d_4/2&0
\end{pmatrix},
$$

$$
Z_f=\frac1t\begin{pmatrix}
\beta d_5h_2^2/d_{\rm src}^2&
-\sqrt{\alpha\beta}d_7h_1h_2/(2bd_{\rm src})\\
-\sqrt{\alpha\beta}d_7h_1h_2/(2bd_{\rm src})&
\alpha(d_5+d_6)h_1^2/b^2
\end{pmatrix}. \tag{FA.125}
$$

The factor $1/t$ is part of the physical dual. The fixed gauge is $Y_{22}=0$ in zero-based $h$ coordinates. Direct substitution gives, on the entire ellipse,

$$
h^TYh\ge|\ell(h)|,\quad
h^TYh+tc(h)\widehat n_h^TZ_f\widehat n_h
\ge|\ell(h)+tc(h)f(h)|.
\tag{FA.126}
$$

This uses physical n_h. Failure whitening is M2^(-1/2)nn^TM2^(-1/2); the physical spectral effect, when needed, is M2^(1/2)ee^TM2^(1/2), never ee^T itself. No spectral source equality is substituted for the finite contact certificate.

The remaining coefficient intervals below are in ascending powers of the
local chart variable. Each displayed endpoint is rounded outwards from the
$2^{-220}$ calculation of the polynomial coefficients and synthetic divisions.
For division of $\sum_{k=0}^n a_kx^k$ by $x-\xi$, the coefficient recurrence
is $b_{n-1}=a_n$, $b_{k-1}=a_k+\xi b_k$ in descending $k$. Use it twice
per removed root. The exact remainder is zero by the equations, independently
of its interval enclosure. On the positive pure sheet the second root in the
base-zero chart is $-1/x_1$; it is separated from $x_0$ and finite throughout
the box. All other removed roots use their own chart coordinates.

| Sheet, sign | $k$ | Seed quotient coefficient | Strip quotient coefficient |
| --- | --- | --- | --- |
| $(0, 1)$ | 0 | $[0.00297015401014,0.00297015401015]$ | $[0.00296843127843,0.00297187674185]$ |
| $(0, -1)$ | 0 | $[0.12560327735391,0.12560327735392]$ | $[0.1255991906209,0.12560736406896]$ |
| $(0, -1)$ | 1 | $[-0.04144793101512,-0.04144793101511]$ | $[-0.04144920610409,-0.04144665588641]$ |
| $(0, -1)$ | 2 | $[0.01933831323362,0.01933831323363]$ | $[0.01933659050192,0.01934003596534]$ |
| $(1, 1)$ | 0 | $[1.4964217976616,1.49642179766161]$ | $[1.49623139748703,1.49661219790962]$ |
| $(1, 1)$ | 1 | $[0.45325689126271,0.45325689126272]$ | $[0.45319604085388,0.45331774183573]$ |
| $(1, 1)$ | 2 | $[1.42988962848658,1.42988962848659]$ | $[1.42969879526944,1.43008046177866]$ |
| $(1, 1)$ | 3 | $[0.4135255617023,0.41352556170231]$ | $[0.41346324114809,0.41358788242282]$ |
| $(1, 1)$ | 4 | $[1.52858664735452,1.52858664735453]$ | $[1.52839059013532,1.5287827046349]$ |
| $(1, 1)$ | 5 | $[0.45133016947045,0.45133016947046]$ | $[0.45126146716503,0.45139887181646]$ |
| $(1, 1)$ | 6 | $[0.03427654488529,0.0342765448853]$ | $[0.03422592173848,0.03432716803211]$ |
| $(1, -1)$ | 0 | $[0.11207633916492,0.11207633916493]$ | $[0.11173034301084,0.11242233568834]$ |
| $(1, -1)$ | 1 | $[0.06948343855543,0.06948343855544]$ | $[0.0691160560784,0.06985082180826]$ |
| $(1, -1)$ | 2 | $[0.4182865421397,0.41828654213971]$ | $[0.41772175572569,0.41885132887932]$ |
| $(1, -1)$ | 3 | $[0.19322286797197,0.19322286797198]$ | $[0.19301795860816,0.19342777762964]$ |
| $(1, -1)$ | 4 | $[0.13209435653274,0.13209435653275]$ | $[0.13187133828485,0.13231737485947]$ |
| $(1, -1)$ | 5 | $[0.06065944909555,0.06065944909556]$ | $[0.06060365159343,0.06071524663854]$ |
| $(1, -1)$ | 6 | $[0.0108334810251,0.01083348102511]$ | $[0.01080022191544,0.01086674013477]$ |

For the transformed polynomial on each half-line use the Bernstein controls
just specified and restrict them to the following closed dyadic intervals.
The restriction is ordinary de Casteljau subdivision: at parameter $v$ replace
adjacent controls by $(1-v)b_k+vb_{k+1}$ until one remains; the two boundary
chains give the left and right restricted controls. An interval $[a,b]$ is
obtained by first keeping the right part at $a$, then the left part at
$(b-a)/(1-a)$, with the evident conventions at 0 and 1. Each rational lower
bound in the next table bounds every restricted control using the coarsened
coefficient intervals above, so it is itself a sufficient whole-domain
witness. The signs here select the positive or negative real half-line and
are distinct from the height sign.

| Sheet, height sign | Half-line sign | Closed partition | Seed lower control $>$ | Strip lower control $>$ |
| --- | --- | --- | --- | --- |
| $(0, 1)$ | $1$ | $[0,1]$ | 0.00297015401 | 0.002968431278 |
| $(0, 1)$ | $-1$ | $[0,1]$ | 0.00297015401 | 0.002968431278 |
| $(0, -1)$ | $1$ | $[0,1/2], [1/2,3/4], [3/4,1]$ | 0.009322743548 | 0.009321292113 |
| $(0, -1)$ | $-1$ | $[0,1]$ | 0.019338313233 | 0.019336590501 |
| $(1, 1)$ | $1$ | $[0,1]$ | 0.020676278085 | 0.020673162057 |
| $(1, 1)$ | $-1$ | $[0,1/2], [1/2,3/4], [3/4,13/16], [13/16,27/32], [27/32,7/8], [7/8,1]$ | 0.000088860347 | 0.000060458205 |
| $(1, -1)$ | $1$ | $[0,1]$ | 0.008806290435 | 0.008791422552 |
| $(1, -1)$ | $-1$ | $[0,1/2], [1/2,3/4], [3/4,1]$ | 0.000442309136 | 0.000425306464 |

Both partitions start at 0, end at 1 and have identical adjacent endpoints.
Every quotient has even degree and strictly positive leading coefficient,
which also checks the homogeneous point at infinity. Bernstein basis functions
are nonnegative and sum to one, proving positivity over each entire interval.
Thus the removed exact double roots exhaust the circle zeros, including all
axes and chart infinities. The original denominators are positive, and the
squared factors introduce no sign change. This proves the asserted global
gaps and (FA.126). $\square$

## 98. Matching value and the minimum actual alphabet of every optimizer

**Theorem 98.1 (universal matching and count).** Under Assumption 93.1,
for every point of the closed strip the family in §94 is globally optimal
among all stipulated original competitors. Every such optimizer has at
least five supported-nonzero actual low labels and at least six total actual
labels, and the minimum is attained.

**Proof.** Equation (FA.122)'s eight moments are exactly the full live Gram and full physical failure covariance: u²+v²=1 restores the omitted live v² moment; mu=alpha V+beta W restores the omitted failure v² moment. Thus

$$
\sum_i p_ih_ih_i^T=I_3,\quad
\sum_i p_i\eta_i tc(h_i)n_in_i^T=M.
$$

Every weight is strictly positive. The sign checks give epsilon_i H_eta_i>0. The contact equations imply sum p_i |H_eta_i|=d.B(t). For every original competitor, apply (FA.126) to capacity endpoints and the convex chord inequality to its own b in [0,tc]. Integrating its complete live and physical failure moments gives low height <=tr(Y)+tr(Z_fM2)=d.B(t). FA69 and Theorem 87.2's reduction applies only to supported-nonzero low labels, but every supported-zero label has zero height difference and cannot evade this bound. Original competitor time laws have not been fixed to g. Adding the fixed positive high contribution H0 and dividing by two proves the universal upper bound (FA.120), matched by this one original construction. Jointly choosing orientations and failure allocation was allowed in that bound.

The five projection lines are pairwise distinct: their normalized u,v determinant magnitudes exceed 0.04598 at the seed and remain nonzero over the whole strip. The three normalized pure vectors $(1,u_i,v_i)$ have determinant in $(1.5240677,1.5242904)$ on the strip; the invertible diagonal rescaling to $h_i$ preserves independence; the remaining pure live Gram is rank three. Thus this is not a fixed-allocation rank-two or maximum-contrast surrogate. A five-column minor of Gamma, using rows $(1,u,v,\eta\mathfrak c,\eta\mathfrak c u^2)$, lies in

$$
(-0.015477643822831680,-0.015475293534243875)
$$

on the strip. The five weights are therefore uniquely determined by their moments.

For an arbitrary existing supported-nonzero low label let
$C=t\mathfrak c(h)$, $v=b/C\in[0,1]$, and let $g_0,g_1$ denote the
nonnegative pure and saturated absolute-value dual gaps. Its unhalved slack
is exactly

$$
(1-v)g_0(h)+vg_1(h)+
(1-v)|\ell(h)|+v|\ell(h)+Cf(h)|-|\ell(h)+bf(h)|\ge0.
$$

The last three terms are the convex chord loss. Integrating gives the
already matched universal bound. At any optimizer, vanishing total slack
forces vanishing slack in each existing positive outcome (almost everywhere
in the stipulated integral version). A strictly interior b would require zero gaps at BOTH endpoints on the same direction by the convex chord decomposition. The certified pure and saturated zero sets are disjoint, so no such label exists. The only optimal supported directions and endpoint choices are the five listed. The nonzero minor and their positive matching weights require all five. FA69 and Theorem 87.2's actual-label rigidity forbids combining distinct directions into one low label, independently of hidden Kraus multiplicity. Positive high acquired mass requires at least one further actual high label. The construction below has exactly five low plus one high, including the complement, proving the exact minimum six here. This argument does not depend on an optional determinant test for Z_f +/- Delta over a broad interval.

For a convergent countable alphabet the nonnegative slack sum vanishes
only if each positive supported term has zero slack. In CG Convention
21.3's stipulated integral model, the same conclusion holds almost everywhere
for the supplied CP/Kraus densities, by vanishing integral of nonnegative
slack. It restricts their supported directions to the same five rays and
fixes their five aggregate coefficient masses. It does not construct a
disintegration of an arbitrary instrument. A purported actual alphabet with
fewer than five supported outcomes is finite and reduces to its finite
positive CP-mass outcomes; it cannot support the five strictly positive
aggregate masses. Positive nonatomic actual mass already has infinite
alphabet. Hidden Kraus indices cannot replace actual outcomes.

A supported-zero outcome may have a nonzero full-$M_5$ encoder and is admitted
and counted, even though its supported height and contrast are zero. Such
additional outcomes cannot lower these bounds. The complement in §100 is
counted inside the one high outcome. Five low projection lines, two physical
failure lines, the actual alphabet and the joint fibre dimensions
$(2,2,2,2,2,5)$ are different quantities. The minimum statement holds only
on this strip; optimal implementations may split a ray into several actual
labels or add supported-zero outcomes. $\square$

## 99. Strict margins and analytic dependence on the activity parameter

**Theorem 99.1 (closed-strip margins and regular branch).** The family,
its value and a fixed analytic choice of instrument factors depend real
analytically on $t$ for $9999/10<t<10001/10$ and continuously at both
endpoints. The optimum is constant in the requested $s$ on $[0,3/25]$.

**Proof.** All five angular second derivatives of the appropriate gap are strictly positive. Their uniform strip enclosures are

- contact 0: (0.01678263300596134647607184464176762, 0.01678644900066609033089675882945644).
- contact 1: (0.01678141971097141399331153641316915, 0.01678766249897283262877500029544263).
- contact 2: (0.06031133751310846247936672851294927, 0.06031655252590283334925811709277640).
- contact 3: (17.23741444892271443501698377453156460, 17.24184281361076349586024173695675543).
- contact 4: (0.85197496258990452305983215822696129, 0.85709731507883159868282892569297981).

These are computed as P_i''/D_eta times ((1+x_i²)/2)^2 at the exact contact, using P_i=P_i'=0. Positive quotient certificates exhaust every zero; compactness supplies the strictly positive gap away from them. Weights and sign values have strict positive margins; physical contrast exceeds 0.12421255, above every requested s<=0.12. The weighted Jacobian norm bound proves nonsingularity after the gauge and removal of duplicate report constraints. Rational analytic equations with positive denominators and nonsingular Jacobian give analytic dependence on t by the implicit function theorem. Uniform contraction selects the same branch throughout the entire stated interval. Thus all seed, curvature, global-sign and independent-Jacobian hypotheses of the continuation argument hold on the specified branch.

The root coordinates remain strictly inside their fixed boxes by §96.
The equations are real analytic wherever their source radicals and
denominators are positive, and their gauge-fixed Jacobian is invertible.
The implicit function theorem therefore gives local analytic solutions;
uniqueness in the common box identifies them on overlaps. Uniform contraction
gives continuity at both closed endpoints. The sign reports stay fixed
because none of the five $z_i$ crosses zero. Positive square roots in the
constructor and analytic rank-two frame choices give an analytic instrument
representative; this does not assert uniqueness of its full CP completion or
time laws.

The following outward enclosures hold uniformly on the strip:

| Quantity | Strict enclosure |
| --- | --- |
| Physical contrast | $(0.12421255682840184212,0.12422087673167824425)$ |
| Five-column moment minor | $(-0.01547764382283167927,-0.01547529353424387514)$ |
| Pure normalized frame determinant | $(1.5240677194037333283,1.52429036518928477366)$ |
| Every pairwise projection determinant magnitude | $>0.0459$ |
| Original activity floor $t_0$ | $(264.80903138857747844055,264.80903138857747844386)$ |

The positive weights, capacities and signed heights can also be enclosed
without choosing sign branches after evaluation:

| $i$ | $p_i$ | $\mathfrak c(h_i)$ | $\epsilon_iH_{\eta_i}(h_i)$ |
| --- | --- | --- | --- |
| 0 | $(0.403551820132,0.403570298116)$ | $(0.210664559785,0.210666270016)$ | $(0.010253268733,0.010253639963)$ |
| 1 | $(0.183966169952,0.183970045178)$ | $(0.137635731409,0.137662212179)$ | $(0.010558500861,0.010560998242)$ |
| 2 | $(0.320037200481,0.32005031)$ | $(0.190964924576,0.190971375137)$ | $(0.002967133478,0.002967450763)$ |
| 3 | $(0.036142704793,0.036153562793)$ | $(0.183965805294,0.18396605267)$ | $(0.476464351917,0.476694506627)$ |
| 4 | $(0.056270517038,0.056287371516)$ | $(0.080070287785,0.080070450066)$ | $(1.810181210942,1.810558411808)$ |

In particular $p_i>0.03614270$, actual contrast $>0.12421255>3/25$,
and $t_0<9999/10$. Both $s$ endpoints, including zero, and both $t$ endpoints
are included. The smallest requested contrast is an inequality, not a
requirement to alter the common atom law. The case $t=0$ remains empty by
Theorem 87.2 and is outside this strip. $\square$

## 100. One common full-complex instrument with the original outputs

**Theorem 100.1 (simultaneous original realization).** Under Assumption 93.1,
the following one instrument attains the strip value, five-low/six-total
minimum, error and resource conditions for the sole unknown reached-cut
specimen, with no additional input or later carrier action.

**Proof.** For each selected atom put K_i=sqrt(p_i)(s0 D+z_iT+w_iS) and N_i=p_i eta_i tc(h_i)n_in_i^T. Reuse FA70 and Theorem 87.3's row-space constructor: choose J_i:C²->ran K_i^* isometric and define

$$
Q_i=J_i^*(K_i^*K_i+N_i)J_i,\quad
C_i=Q_i^{1/2}J_i^*E^*,\quad B_i=K_iJ_iQ_i^{-1/2},\quad
F_i=Q_i^{-1/2}J_i^*N_iJ_iQ_i^{-1/2}.
$$

Then B_i^*B_i+F_i=I2, B_iC_i=K_iE^*, and the supported acquisition effect is E(K_i^*K_i+N_i)E^*. In particular later failure is included in acquired probabilities. The entire fibre has dimension two. For the chosen attainer take g(u)=2/(1+u)^2, Gtime(u)=2u/(1+u), survivor Z_i(u)=sqrt(I-Gtime F_i) and positive first-event rate R_i(u)=g(u)F_i[I-Gtime F_i]^(-1). For the separately labelled components $\ell\in\{0,1,2,3,13\}$, current-survivor failure maps are

$$
Y\mapsto w_\ell g(u)\operatorname{tr}
(F_i Z_i(u)^{-1}Y Z_i(u)^{-1})P_f.
$$

Terminal processing on survivors only is the isometry EB_i(I-F_i)^(-1/2). The composite live matrix is EB_i. Its prescribed effect is B_i^*B_i=I-F_i, not an arbitrary map inferred from endpoint coercivity. Pure rows have zero rate; saturated rows have exact activity log(1+t), with nonzero failure eigenvalue t/(1+t). At t=1000 the minimum terminal live eigenvalue is exactly 1/1001. All survivors remain positive and there is no forced deadline failure.

Fix Wperp:C²->Pperp and J0:C²->C³ isometric. A single completely counted dimension-five high fibre has encoder

$$
C_H=\begin{pmatrix}\sqrt{1-\delta}DE^*\\W_\perp^*\end{pmatrix},
$$

zero rate, and two hidden terminal Kraus matrices E[I3 0] and EJ0[0 I2]. Its binary report is deterministically plus. Low reports are deterministically sign(z_i). These are functions of actually generated labels; discarded Kraus indices are never read. The complement is coherent and charged within the same high fibre on complementary inputs. It has zero probability on all twelve original specimens, but its full encoder is nonzero. This is the allowed JR completion and differs explicitly from fixed CA10.

Source-root TP and the exact two moment identities prove total encoder effect I5. For EVERY complex X in M5, this same instrument has

$$
\begin{aligned}
\Phi^L(X)&=E[\Lambda_*(E^*XE)+J_0W_\perp^*XW_\perp J_0^*]E^*,\\
\Phi^f_\ell(\mathcal B)(X)&=w_\ell\int_{\mathcal B}g(u)du\;
\operatorname{tr}(EME^*X)P_f,
\quad\ell\in\{0,1,2,3,13\}.
\end{aligned}
$$

The five original weights are separately (0,1/4,1/2,1/4,0). On an arbitrary passive reference the exact failure map is

$$
w_\ell\int_{\mathcal B}g(u)du\;P_f\otimes
\operatorname{Tr}_5[(EME^*\otimes I_R)X],
$$

and live maps tensor their displayed Kraus conjugations with I_R. This is the conditional reference operator, not an unconditional reference marginal. Both zero labels remain separately zero for EVERY Borel set, the three positive components remain separate, and no additional sector is generated.

On each of the twelve histories these are exactly the supplied original simulator outputs, compared against their entire original coherent ideal blocks and ideal density f_y(u)=6y/(y+6u)^2. Thus, conditionally on the original minimax/error identification,

$$
e_{5,e,n}=e_{27,e,n}=E_*,\qquad e_{16,e,n}<E_*\quad(e,n=\pm1).
$$

Only the single high fibre has dimension >=3. Its acquired probability on history y is (1-delta)A_y; its maximum is (1-delta)A27=C(s), the sharp JOINTLY acquired worst-history cost. Every subsequently accessible share is included in the declared fibres; there is no hidden accessible quantum system. The original reported contrast is s0 sum p_i |z_i|. FIRST occurs at absolute 6+u in the chronological FA70 process; only not-yet-failed carriers receive later processing, with no positive-carrier action after absorption. Necessity covers every admitted original time law; the choice of g is only this sufficiency witness. These are mathematical maps under the original control contract; native actuation and permissions remain additional premises.

Indeed $N_i\preceq tK_i^*K_i$ on the rank-two row space, so
$F_i\preceq t(I-F_i)$ and $I-F_i\succeq I/(1+t)$. For saturated
rank-one $N_i$, the extremal ratio is $t$, giving the exact nonzero
failure eigenvalue $t/(1+t)$; pure rows have $F_i=0$. Thus the entire-fibre
rate integral, not an average or postselected rate, is exactly $A$ on the
two saturated rows and zero on the three pure and high rows.
The high terminal Kraus effects sum to $I_5$ on that high fibre, and
$[EB_i(I-F_i)^{-1/2}]^*[EB_i(I-F_i)^{-1/2}]=I_2$ on each low fibre.
The latter is the terminal TP operation; its cumulative no-event map is
$\operatorname{Ad}_{EB_i}$.

On supported inputs, expanding $\sum_i K_i(\cdot)K_i^*$ with the Gram
identity gives $\delta D(\cdot)D^*+T(\cdot)T^*+S(\cdot)S^*$;
the high row adds $(1-\delta)D(\cdot)D^*$. The failure covariance
identity gives the trace-and-prepare functional in every Borel component.
Together with source-root $D^*D+T^*T+S^*S+M=I_3$, this proves total
encoder effect $P+P^\perp=I_5$. Tensoring each Kraus conjugation with
$I_R$ and summing its exact effects proves the conditional partial-trace
formula for every passive reference, including complex entangled inputs.
No real-state or single-Kraus restriction has entered the universal comparison.

The twelve ideal live blocks are the coherent $U_{e,n}B_yU_{e,n}^*$ of
(CG.111), with the original densities $6y/(y+6u)^2$. The comparison norm is
HALF the entire stopped-cq norm, including singular time, wrong-support,
abort and zero-target sectors. Error equality for heights 5 and 27 and
strict inequality for height 16 are inherited at the source root, for all
four sign pairs; they are not inferred from rounded source expressions.
Writing $\kappa=h_0a+h_1b$, the actual reported contrast is
$2|\operatorname{Re}(E^*F_+E)_{01}|/\kappa=s_0\sum_i p_i|z_i|$.
Every acquired probability uses the full encoder effect, hence includes
future failure. With $A_y=\operatorname{tr}(D^*D\rho_{y,e,n})$, the
only dimension-at-least-three outcome has probability $(1-\delta)A_y$
and worst history 27, equal to the inherited sharp weak $\mathsf C(s)$.
All subsequently accessible shares are part of the declared joint fibres;
no discarded Kraus index is a readable report or control. FIRST is the first
jump on the original absolute clock $6+u$, followed by no positive-carrier
action on failed branches; positive terminal survivors forbid forced
deadline absorption. Necessity in §98 permits every admitted original
time law; $g$ specifies only this attainer. $\square$

## 101. Source dependence, literature scope and remaining mathematical boundaries

**Definition 101.1 (dependence and scope).** Sections 93--100 are a
`repo-derived` source-specific synthesis of the original capacity/rigidity,
full-output construction and sharp-cost results in FA68--70, FA72, FA77--79,
FA87 and JR42--44, with the original source in RC58 and CG13--17. The
finite submaximal-height, roof and compression results of §§88--90 retain
their own scopes. The common-dual, finite-contact, orientation, two-line
exclusion and sufficient-continuation results are used at their stated
conditional scopes; the selected five-contact root and its matching whole
circle inequalities are the additional specialization here. No priority
claim is attached to this synthesis.

The contraction proof uses the geometric-series fixed-point argument and
the polynomial sign proof uses the elementary Bernstein convex-hull identity,
both explicitly given above. Dritschel--Rovnyak, *The Operator Fejér--Riesz
Theorem*, arXiv:0903.3639v1, §2 Theorem 2.1, factors a Laurent polynomial
already nonnegative everywhere on the circle, including zeros, into a
same-degree analytic factor. It neither chooses the present unknown dual
multipliers nor proves the present inequalities before their signs are
known. The source-specific quotient bounds in §97 supply those signs directly.
The relative-interior and information-matrix hypotheses discussed in §91
are unchanged; no general support bound is transferred into this local
actual-alphabet theorem. The ordinary real analytic implicit-function theorem
is applied only after §96's nonsingular independent Jacobian and §99's
positive analytic domains have been established.

**Definition 101.2 (unchanged programme boundary).** The local value and
minimum alphabet in Theorem 93.2 apply only to
$9999/10\le e^A-1\le10001/10$, $0\le s\le3/25$ under Assumption 93.1.
Outside this rectangle, the complete evaluated finite-$(s,A)$ frontier,
all jointly chosen oriented failure allocations and full-rank submaximal
live-height decompositions, common contacts, signs, zero-weight and rank
changes, degeneracies and gluing remain required. The complete original
precontact/contact $K(s)$ coefficients, their orientation choices and all
seams remain required beyond supplied postcontact and rank-conditional scopes.
Global minimum actual optimizer alphabets and every count transition outside
this strip are not supplied by its five-low/six-total minimum.

The published JS source identified in §92 supplies its unique clamped scalar
limiting selector and strictly monotone inversion (Theorem 11.3), quantitative
critical strip for complete actual records (Theorem 14.1), uniform
$O(t^{-1})$ sub-spectral product/value estimates on the actually feasible
compact intervals (Theorem 14.2), and compact-uniform spectral product/value
layer (Theorem 16.2). Those results are credited at their conditional limiting
scopes. JS Proposition 12.2 and Definition 18.2 leave the complete source-specific
transition-root inventory, isolation, ordering, multiplicities and sign
intervals in JS.58, remaining next terms, critical five-label/static-contact
joint layers and other required joint scales outside those supplied results
unresolved. Neither limiting three-failure-line structure nor a native state
count is an actual finite quantum acquisition alphabet.

The original source-root/isolation/Jacobian/rank, TP, minimax/error and
sharp-cost/equality identifications remain Assumption 93.1; ordinary source
proofs and rational arithmetic are not Lean/kernel certification. The
conditional CP instrument does not supply lawful specimen access, calibration,
acquisition generation or duration, coherent joint storage and share accounting,
decoder actuation, an aligned absolute FIRST clock, archives, source/epoch,
controller or permissions. The self-calibration, selected-transition and
static separator/control interfaces described in §92 add no common quantum
operation/resource realization bridge; OriginalControl remains geometry.
The through-2027 quantum-first programme is unchanged beyond the local
conditional theorem just stated.

## 追加锚（本行以下为增补区）
