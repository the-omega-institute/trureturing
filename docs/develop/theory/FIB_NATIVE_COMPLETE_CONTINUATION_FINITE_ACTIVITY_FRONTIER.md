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
