# Recursive relational observation: original-control causal programming

> This volume uses the `generic-v1` theory-document convention. Its mathematical
> statements and their following proofs have numbered paragraph leads. Merged
> text is an immutable prefix; corrections and extensions belong after the
> terminal append anchor, under new numbered headings.

## 1. Scope, status and the actual continuation consumer

This is a theory exposition with ordinary proofs, not a Lean certificate,
physical implementation or construction of an original-source sensor. Repository
suppliers are taken at the immutable public snapshot
`11e2a65d554143d0e3f38b37f1b686453451e3c4`. The formal source and composition
declarations, and the existing canonical stopped instrument, remain credited
inputs. This theory is reference input; Lean declarations and their checked
proofs carry the repository's formal mathematical truth. The two writing
conventions are `formal-thinking-and-answer` and
`theory-volume-template`, restricted here to theory authorship. No independent
model diversity or independent-priors assertion accompanies this exposition.

The result concerns one public relative control at two possible current heights.
The height coordinate is nondecreasing; the relative phase is unrestricted
within the original regularity class. All unknown initial phases and signed
prior winding sectors are tested. The initial accessible source-bearing
assistance is a calibrated pure programme pair, jointly independent of those
nuisances. The process must expose the correct live specimen at every cut and
retain the canonical exact first-failure time, original mode and absorbing
successor. A sharp local criterion determines when this is possible.

Its operational consumer is a still-live observer that interrupts a permitted
request, retains its source-bound programme, updates its public catalogue of
possible heights and continues the same original specimen. A terminal
programmable instrument alone does not supply that consumer: Section 8 gives a
finite, positive-margin separation. Sections 9–10 acquire a sufficient coherent
programme through exactly the additional producer phase port already declared
in [Record Acquisition][RA], Definition 13.2. That port, its source binding,
permissions and joint preservation are supplied premises, not constructed here.
The sharp action claim restricts acquisition to protocols for which the old
specimen and archives are spectators and all new source dependence enters
through that port.

An arbitrary nonmonotone control, a readable archive correlated with the unknown
phase or winding, a total guard for requests legal at only one possible height,
and acquisition using the old specimen are outside these theorems. These
restrictions do not replace the full original task. In particular the acquired
joint observer and four-view mutual-recovery programme remain open.

## 2. Positive original source, actual histories and regularity

**Definition 2.1 (the supplied five-mode source and double wall).** In
`FiniteRectangleTransport`, a valid base is $B=(X,Y,Z)$ with
$0<Z<1$, $r=1-Z$ and $0<X,Y<r$. Its strict height interval and probabilities,
in original mode order $(0,1,2,3,13)$, are

$$
J(B)=(\max(0,X+Y-r),\min(X,Y)),\qquad
p_B(k)=(r-X-Y+k,X-k,Z,Y-k,k).
\tag{CP.1}
$$

Index $4$ denotes mode $13$. Put $d=(1,-1,0,-1,1)$ and
$w_i(k)=d_i/(p_B(k)_i\sum_{l\ne2}p_B(k)_l^{-1})$. The present results restrict
to the valid double wall

$$
B=(c,c,Z),\qquad c=r/2,\qquad
p(k)=(k,c-k,Z,c-k,k),\qquad
w(k)=(1/2-k/r,-k/r,0,-k/r,1/2-k/r).
\tag{CP.2}
$$

All heights lie strictly in $(0,c)$. Fix one positive preparation, its source
and epoch, and calibrated preparation phases $\theta_i$ where actually supplied,
with $\theta_2=0$. Use the orthonormal active directions

$$
|+\rangle=(e^{-i\theta_0}e_0+e^{-i\theta_4}e_4)/\sqrt2,\quad
|-\rangle=(e^{-i\theta_1}e_1+e^{-i\theta_3}e_3)/\sqrt2,\quad
|2\rangle=e_2,
\qquad V=\operatorname{span}\{|+\rangle,|-\rangle,|2\rangle\}.
\tag{CP.3}
$$

The unknown live source family at height $x$ is

$$
\psi_{x,\beta,m}=\sqrt Z|2\rangle+e^{-i\beta}
 \bigl(\sqrt{2x}|+\rangle+(-1)^m\sqrt{2(c-x)}|-\rangle\bigr),
\qquad \beta\in\mathbb R,\quad m\in\mathbb Z.
\tag{CP.4}
$$

The real residual is $(\beta,\beta-\pi m,0,\beta-\pi m,\beta)$, with relation
charge $2\pi m$. The specimen depends only on winding parity; the actual
history retains the entire signed integer and real phase lift.

**Proposition 2.2 (credited actual-source realization, with its explicit map).**
Choose $a_0,q\in(0,c)$, $q\ne a_0$, before choosing $x,\beta,m$. A unit
fixed-height phase leg of increment $2\pi m$ at $a_0$, the four unit rectangle
legs with relative vertices

$$
(a_0,0),\ (q,0),\ (q,B_{\beta,m}),\ (a_0,B_{\beta,m}),\ (a_0,0),
\qquad
B_{\beta,m}=\frac{r(\pi m-\beta)-2\pi m a_0}{q-a_0},
\tag{CP.5}
$$

and a unit zero-phase arrival $a_0\to x$ realize (CP.4) from the common
preparation, conditional on the actual live branch. Every earlier canonical
failure retains its first time, mode and absorbing successor. These histories
are the supplied witnesses of [Quantum Carrier Minimum][QCM], Proposition 7.2,
and [Acquired Continuation Limits][AC], Proposition 3.1.

Proof. On the double wall,
$w(q)-w(a_0)=-(q-a_0)(1,1,0,1,1)/r$. Consequently
$2\pi m w(a_0)+B_{\beta,m}(w(q)-w(a_0))$ is exactly the displayed real
residual. The arrival has zero phase velocity. All height legs remain in the
compact interval between $a_0,q,x$, strictly inside $(0,c)$; all pieces join
continuously. The phase variation is $2\pi|m|+2|B_{\beta,m}|$, finite for each
history. The rectangle declaration supplies its lawful transport, and the
signed phase-leg application in its owning Scribe supplies all integer sectors.
`concatenate_original` keeps the literal prefix and translates the real tail.
The finite positive height band gives finite canonical charge and positive
live probability. No extra specimen, retry or observed waveform is involved.
$\square$

**Definition 2.3 (the allowed public future path).** Fix $T\in[0,\infty)$,
$0<x_1<x_2<c$, and real relative controls $a,b$ on $[0,T]$, with
$a(0)=b(0)=0$. The function $a$ is nondecreasing, and

$$
k_j(t)=x_j+a(t)\in(0,c)\quad(j=1,2; 0\le t\le T).
\tag{CP.6}
$$

The controls obey either original alternative: both are absolutely continuous,
or both are continuous finite piecewise $C^1$ with derivative rates continuous
on each closed partition piece. Repeated partition times are allowed, and
$b$ has finite variation. The latter alternative implies absolute continuity:
integrate each continuous rate on its piece, apply the fundamental theorem,
and telescope the endpoint values; empty pieces contribute zero. Thus write
$v=a'\ge0$ and $\omega=b'$ almost everywhere, with both rates integrable.
There is no common speed or derivative-variation bound. Each individual path
has a positive compact support margin.

At actual current lift $\chi_*$ this means $\chi_*+b(t)$, not a supplied
reading of $\chi_*$. The original relative-command domain is
$(0,c-a(T))$ in this monotone case; both catalogue heights must belong to it.
This is the partial-operation convention of [Probability/Phase Transport][PP],
Section 9.1. At a join the height must match and the real phase is translated
as in `concatenate_original`. Zero duration is the matching identity, not an
instantaneous nonzero displacement.

## 3. Whole programme contract and the prescribed canonical cuts

**Definition 3.1 (all accessible assistance).** The initial source-bearing
assistance available to the processor, apart from the specimen, is one
normalized pure state $r_j$ conditional on height $x_j$. Its calibrated pair
is public, independent of $\beta$ and the whole signed $m$, with phases chosen
so that $\langle r_1,r_2\rangle=\mu\in[0,1]$. Inner products are conjugate
linear in the first entry. All other accessible inputs are jointly common
and independent of $j,\beta,m$, and can be absorbed into common blanks.

This includes source-sensitive installed descriptions, controller inputs,
selectors and update data, clocks, calibration tokens, permissions, readable
archives, receiver shares and any later-returned environment. Equal separate
marginals do not establish this joint premise. A source label accessible only
to the producer is not a free observer input. Public catalogue and calibration
data reveal the pair, not its actual index.

An old archive/reference $R$ may remain correlated with the actual history,
but is acted on by identity and cannot supply programming or selection input.
For fixed actual history the pure programme factors from every other system.
The upper constructions below apply also to arbitrary input states
$\rho_{VR}\otimes|r_j\rangle\langle r_j|$ with arbitrary unchanged quantum
references. They do not authorize reading a previously inaccessible archive.

**Definition 3.2 (the canonical interval instrument).** For $s\le t$ put

$$
\begin{aligned}
\lambda_j&=\frac{v}{k_j},&
\gamma_j&=\frac{vc}{k_j(c-k_j)},&
\delta&=\frac{(x_2-x_1)\omega}{r},\\
A_j(t,s)&=\exp\left(-\frac12\int_s^t\lambda_j\right)
           =\sqrt{\frac{k_j(s)}{k_j(t)}},\\
B_j(t,s)&=\exp\left(-\frac12\int_s^t\gamma_j\right)
           =\sqrt{\frac{k_j(s)(c-k_j(t))}{k_j(t)(c-k_j(s))}},\\
\Phi_j(t,s)&=\int_s^t k_j(u)\omega(u)/r\,du.
\end{aligned}
\tag{CP.7}
$$

All functions are integrable. In order $(+,-,2)$, use the gauged successful
operator

$$
\widetilde K_j(t,s)=\operatorname{diag}
 \bigl(e^{-i(b(t)-b(s))/2},\ B_j(t,s),\
            A_j(t,s)e^{-i\Phi_j(t,s)}\bigr).
\tag{CP.8}
$$

The ungauged original operator has entries
$(e^{-i\Delta b/2+i\Phi_j},B_je^{i\Phi_j},A_j)$.
Multiplication by $e^{-i\Phi_j}$ gives (CP.8), without changing its CP map.
This uses the negative state-phase convention and the actual weights (CP.2).
The scalar gauge is only a proof convention, not a source-dependent operation
performed by the controller.

Write $\rho^R_{\alpha\alpha}=\langle\alpha|\rho_{VR}|\alpha\rangle$. The
prescribed failure densities on $[s,t]$, with the exact clock time retained,
are

$$
\begin{aligned}
\mathcal I_{j,2}(du)(\rho_{VR})
 &=\lambda_j(u)A_j(u,s)^2\,|f\rangle\langle f|
       \otimes\rho^R_{22}\,du,\\
\mathcal I_{j,i}(du)(\rho_{VR})
 &=\frac12\gamma_j(u)B_j(u,s)^2\,|f\rangle\langle f|
       \otimes\rho^R_{--}\,du\quad(i=1,3),\\
\mathcal I_{j,0}(du)&=\mathcal I_{j,13}(du)=0.
\end{aligned}
\tag{CP.9}
$$

These are the credited canonical instrument of [Instrument Boundaries][IB],
Section 5.2, and its full five-label restriction to $M_3$ in [QCM], Section 2.
The two minus-mode labels remain separate. A stopped input keeps its old
first-failure record and has only stopped continuation.

On the actual source family, survival from $0$ to $t$ is
$S_j(t)=A_j(t,0)^2=x_j/k_j(t)$. The normalized live target is the state
obtained from $\psi_{k_j(t),\beta,m}$ by its transported original phases.
Its $|2\rangle$ coefficient is $\sqrt Z$; its two other coefficients are
nonzero multiples of $e^{-i\beta}$, with the minus sign $(-1)^m$ retained.
The operator (CP.8) maps the initial specimen to
$\sqrt{S_j(t)}e^{-i\Phi_j(t,0)}$ times this target.

**Definition 3.3 (one causal realization).** One common outcome-retaining
process, independent of the actual $j,\beta,m$, must have these live targets
and survival probabilities at every cut, and the exact marked first-failure
law (CP.9). Every finite checkpoint refinement is a restriction of this same
process. Its interval operations compose on their actual incoming specimen
and memory; independently chosen terminal processors are insufficient.

Arbitrary common live-memory updates, extra common ancillas, measurements and
retained outcome registers are allowed. In a proof dilation all discarded
environments are retained, with later physical operations acting trivially on
inaccessible parts. This grants no environment port to the controller.
Rejections or aborts absent from the target law cannot be hidden by conditioning
on acceptance. A calibrated implementation of the prescribed joint CP operations,
waveform generation, blank resources and exact-time/mode recording are explicit
ideal services, not consequences of geometric transport alone.

## 4. Sharp local necessity and the live overlap invariant

**Theorem 4.1 (causal two-height programming criterion).** For every source,
pure programme pair and monotone original relative control of Definitions
2.1, 2.3 and 3.1, an exact causal realization of Definition 3.3 exists if and
only if, almost everywhere on $[0,T]$,

$$
\boxed{\begin{aligned}
\mu^2\left[\left(\frac{\lambda_1+\lambda_2}{2}\right)^2+\delta^2\right]
   &\le\lambda_1\lambda_2,\\
\mu^2\left(\frac{\gamma_1+\gamma_2}{2}\right)^2
   &\le\gamma_1\gamma_2.
\end{aligned}}
\tag{CP.10}
$$

Necessity requires correctness only on the actual full $\beta,m$ families
(CP.4), with their prescribed canonical survival at every cut. It imposes no
programme-return assumption or finite memory dimension. Sufficiency supplies
the whole exact-time/five-mode CP instrument on every $M_3$ input with every
unchanged reference. The attaining process returns $r_j$ unchanged and
uncorrelated on every live branch. Programme return on failure is not claimed.

The inequalities are undivided: zero rates are included. The proof of necessity
is below, and Section 5 proves sufficiency and the complete joint successor.

**Lemma 4.2 (orbit rigidity at each actual live cut).** In any such realization,
let $W_t$ be its successful dilation contraction from the initial specimen and
programme to the cut specimen and all dilation residues. There are unit vectors
$e_j(t)$, independent of $\beta,m$ and of the specimen input vector, such that

$$
W_t(q\otimes r_j)=\widetilde K_j(t,0)q\otimes e_j(t)
\quad(q\in V),\qquad
\langle e_1(t),e_2(t)\rangle=\mu.
\tag{CP.11}
$$

This statement permits arbitrary memory updates; it concerns their whole
purified residue, not only one selected helper marginal.

Proof. Fix $j,t$. Put $z=e^{-i\beta}$ and $\epsilon=(-1)^m$. The input has
form $d+zv_\epsilon$, where $d=\sqrt Z|2\rangle$ and
$v_\epsilon=\sqrt{2x_j}|+\rangle+\epsilon\sqrt{2(c-x_j)}|-\rangle$.
Purity of the prescribed specimen output makes its successful dilation the
normalized target tensor a residue $u_\epsilon(z)$. The target has a constant
nonzero middle coefficient, so projection onto $|2\rangle$ gives
$u_\epsilon(z)=u_0+zu_{1,\epsilon}$. Its constant $u_0$ comes from the same
input $d\otimes r_j$ for both signs. The target's plus coefficient is a
nonzero constant times $z$. Therefore the plus projection of the tensor product
has a $z^2$ term, whereas the linear map on the input is affine in $z$.
Coefficient comparison on the entire unit circle gives $u_{1,\epsilon}=0$.
Vector-valued comparison follows by applying continuous linear functionals.

The remaining constant and linear coefficients, followed by adding and
subtracting the two sign identities, force
$W_t(q\otimes r_j)=D_j(t)q\otimes u_0$ for all three basis directions,
where $D_j(t)$ maps the initial family to its normalized target. Since the
target has norm one, the prescribed survival probability fixes
$\|u_0\|^2=S_j(t)>0$. Absorb its phase according to (CP.8) and divide by
$\sqrt{S_j(t)}$ to obtain the first identity in (CP.11). This is the
full-orbit rigidity mechanism already used in [IB], Theorem 24.3, here with
the transported target. The artificial basis vectors are tests of one linear
map forced by actual histories, not extra allowed source preparations.

For $q=|+\rangle$, (CP.8) has unit modulus and the same phase for both
indices. Hence $W_t$ preserves the norms of $|+\rangle\otimes r_1$ and
$|+\rangle\otimes r_2$. Positivity of $I-W_t^\dagger W_t$ makes it
annihilate both vectors: zero quadratic form of a positive operator implies
zero square-root image. Their cross inner product is consequently preserved,
giving $\langle e_1(t),e_2(t)\rangle=\langle r_1,r_2\rangle=\mu$.
The argument keeps every success record and discarded environment in the
residue and does not presuppose unchanged accessible memory. $\square$

**Lemma 4.3 (interval Gram constraints after arbitrary live updates).** For
every $s\le t$, any causal realization must satisfy

$$
\begin{aligned}
\mu^2\left|1-A_1(t,s)A_2(t,s)
                   e^{-i(\Phi_2(t,s)-\Phi_1(t,s))}\right|^2
 &\le(1-A_1(t,s)^2)(1-A_2(t,s)^2),\\
\mu^2(1-B_1(t,s)B_2(t,s))^2
 &\le(1-B_1(t,s)^2)(1-B_2(t,s)^2).
\end{aligned}
\tag{CP.12}
$$

Proof. In a consistent proof dilation the interval success contraction $F_{t,s}$
satisfies $F_{t,s}W_s=W_t$. The matrices $\widetilde K_j(s,0)$ are
invertible, since their attenuation factors are strictly positive. Their
phase and attenuation integrals add. Substituting (CP.11) and varying $q$
therefore gives

$$
F_{t,s}(q\otimes e_j(s))
       =\widetilde K_j(t,s)q\otimes e_j(t)
\quad(q\in V).
\tag{CP.13}
$$

Taking the two middle inputs, their input Gram matrix minus output Gram
matrix is positive semidefinite because $F_{t,s}$ is a contraction.
Its diagonal entries are $1-A_1^2,1-A_2^2$; its off-diagonal entry is
$\mu(1-A_1A_2e^{-i(\Phi_2-\Phi_1)})$, since both residue overlaps are
$\mu$. Nonnegative determinant gives the first inequality. The two minus
inputs give the second in the same way. No failure record was discarded to
derive contractivity. Indeed these are necessary even for the weaker task
that forgets the failure time. $\square$

Proof of Theorem 4.1, necessity. At a common Lebesgue point $s$ of the
integrable rates, set $t=s+h$ in (CP.12). Then

$$
\begin{aligned}
1-A_j(s+h,s)^2&=h\lambda_j(s)+o(h),\\
1-A_1A_2e^{-i(\Phi_2-\Phi_1)}
 &=h\left(\frac{\lambda_1(s)+\lambda_2(s)}2+i\delta(s)\right)+o(h),\\
1-B_j(s+h,s)^2&=h\gamma_j(s)+o(h),\\
1-B_1B_2&=h\frac{\gamma_1(s)+\gamma_2(s)}2+o(h).
\end{aligned}
\tag{CP.14}
$$

Here $\Phi_2-\Phi_1=\int_s^{s+h}(x_2-x_1)\omega/r$. Divide the
determinant inequalities by $h^2$ and let $h\downarrow0$. Lebesgue
differentiation gives (CP.10) almost everywhere, including points with zero
rates. No continuity of the updated memory vectors is needed. $\square$

## 5. A common generator and the complete causal construction

**Lemma 5.1 (dissipation in programme Gram coordinates).** Let $0\le\mu<1$
and $H=\operatorname{span}\{r_1,r_2\}$. Given integrable real $l_j,\nu_j$,
define the single operator $C$ by
$Cr_j=(-l_j/2-i\nu_j)r_j$. If $Q=-C-C^\dagger$, its quadratic-form matrix
on this basis is

$$
\bigl(\langle r_j,Qr_k\rangle\bigr)_{j,k=1}^2
=\begin{pmatrix}
l_1&\mu((l_1+l_2)/2+i(\nu_2-\nu_1))\\
\mu((l_1+l_2)/2-i(\nu_2-\nu_1))&l_2
\end{pmatrix}.
\tag{CP.15}
$$

Thus, for $l_j\ge0$, $Q\ge0$ is equivalent to
$l_1l_2\ge\mu^2[((l_1+l_2)/2)^2+(\nu_2-\nu_1)^2]$.

Proof. If $z_j=-l_j/2-i\nu_j$, then
$\langle r_j,Qr_k\rangle=-(z_k+\overline z_j)\langle r_j,r_k\rangle$.
This gives (CP.15). The two vectors are independent, so positivity of this
matrix is positivity of the operator quadratic form by an invertible
congruence, even though the basis is not orthogonal. A Hermitian two by two
matrix is positive exactly when both diagonals and its determinant are
nonnegative. $\square$

**Theorem 5.2 (attaining joint first-failure instrument).** Suppose (CP.10)
holds and $0\le\mu<1$. On $V\otimes H$ define public operators by

$$
\begin{aligned}
C_+(t)r_j&=-i\omega(t)r_j/2,\\
C_-(t)r_j&=-\gamma_j(t)r_j/2,\\
C_2(t)r_j&=(-\lambda_j(t)/2-ik_j(t)\omega(t)/r)r_j,\\
Q_\alpha&=-C_\alpha-C_\alpha^\dagger,\qquad
C=\sum_{\alpha\in\{+,-,2\}}|\alpha\rangle\langle\alpha|\otimes C_\alpha.
\end{aligned}
\tag{CP.16}
$$

These are common operators, not an instruction conditional on reading $j$.
Equivalently, for the known invertible matrix $R_0$ whose columns are $r_1,r_2$,
$C_\alpha=R_0\operatorname{diag}(z_{\alpha1},z_{\alpha2})R_0^{-1}$.
By Lemma 5.1, $Q_+=0$ and $Q_-,Q_2\ge0$. Let $M(t,s)$ be the absolutely
continuous propagator with $\partial_tM=C(t)M$ and $M(s,s)=I$. Set

$$
\begin{aligned}
J_1(t)=J_3(t)&=\frac1{\sqrt2}|f\rangle\langle-|\otimes\sqrt{Q_-(t)},\\
J_2(t)&=|f\rangle\langle2|\otimes\sqrt{Q_2(t)},\\
J_0(t)=J_{13}(t)&=0.
\end{aligned}
\tag{CP.17}
$$

The live map $\rho\mapsto M(t,s)\rho M(t,s)^\dagger$ and the marked
first-failure measures with Kraus fields $J_i(u)M(u,s)$ define one complete
causal instrument. Its successful action is

$$
M(t,s)(q\otimes r_j)=\widetilde K_j(t,s)q\otimes r_j.
\tag{CP.18}
$$

Tracing the programme from its failure outputs gives exactly (CP.9), on every
$M_3$ input and every unchanged reference. Retaining the programme gives the
specific additional successors described in Section 6.

Proof. Strict support bounds $k_j^{-1}$ and $(c-k_j)^{-1}$ on the compact
interval. Thus $C$ is measurable and norm-integrable. The finite-dimensional
integral equation for $M$ has its unique absolutely continuous solution
(successive integral iteration converges with the exponential norm bound).
Alternatively the common eigenvectors in (CP.16) give (CP.18) directly on a
basis. In particular $M(t,u)M(u,s)=M(t,s)$.

The matrix square roots in (CP.17) are measurable; their squared norms are
integrable since the $Q_\alpha$ have integrable norms. At null exceptional
times the rates and jumps may be set to zero. We have

$$
\sum_iJ_i(u)^\dagger J_i(u)=-C(u)-C(u)^\dagger.
\tag{CP.19}
$$

Differentiate $M(u,s)^\dagger M(u,s)$ almost everywhere and integrate to obtain

$$
M(t,s)^\dagger M(t,s)+
\sum_i\int_s^t M(u,s)^\dagger J_i(u)^\dagger J_i(u)M(u,s)\,du=I.
\tag{CP.20}
$$

Each branch is CP and the sum is trace preserving. Integrable finite-dimensional
CP densities give countably additive measures on all Borel time events.
Tensoring the branch formulas with identity proves complete positivity and
normalization for every unchanged reference, including trace-class quantum
archives.

Splitting (CP.20) at a checkpoint gives the early failure measure plus the
late first-failure measure applied to the actual live successor. Propagator
composition gives the same live operation. These identities hold for every
finite partition and every Borel event, establishing consistent restrictions
of this one process. They also deliver the first event at its actual time in
the declared ideal recording service. The branch $f$ is absorbing, with no
new original execution.

Finally $\langle r_j,Q_2r_j\rangle=\lambda_j$ and
$\langle r_j,Q_-r_j\rangle=\gamma_j$. Inserting (CP.18) into each jump
field gives the middle density $\lambda_jA_j^2$ and the two separately
labelled minus densities $\gamma_jB_j^2/2$. Phases cancel within each
rank-one failure CP map. The live CP map is the canonical one because the
gauge changes only a scalar phase. This proves equality on every matrix unit
of $M_3$, hence every joint input, and completes sufficiency for $\mu<1$.
$\square$

**Corollary 5.3 (zero rates, identical programmes and empty time).** For
$\mu=0$, (CP.10) permits every path in Definition 2.3 and Theorem 5.2 uses
orthogonal programmes. For $\mu=1$ and $x_1<x_2$, an exact causal realization
exists exactly when $v=\omega=0$ almost everywhere, hence $a=b=0$ everywhere.
For $0<\mu<1$, a phase-only segment forces $\omega=0$ almost everywhere on
that segment. The interval $T=0$ always has the identity realization.

Proof. At $\mu=1$ the first inequality is
$(\lambda_1-\lambda_2)^2/4+\delta^2\le0$. Since
$\lambda_1-\lambda_2=v(x_2-x_1)/(k_1k_2)$ and $x_2-x_1>0$, it gives
$v=\omega=0$. Absolute continuity and the initial values give $a=b=0$.
The common identity supplies the realization, completing the remaining case
of Theorem 4.1. If $v=0$ and $\mu>0$, the same first inequality gives
$\delta=0$. The zero-overlap and empty-interval claims follow directly from
the construction and its normalization. $\square$

## 6. Full joint successors and the preserved live programme

**Proposition 6.1 (joint law, including the failure programme).** For each
actual history $h$ of index $j$ and every actual input $\rho^h_{VR}$, tensor
its programme $|r_j\rangle\langle r_j|$. Put
$\zeta_{j,2}(u)=\sqrt{Q_2(u)}r_j$ and
$\zeta_{j,-}(u)=\sqrt{Q_-(u)}r_j$. The unnormalized live successor on
$[s,t]$ is

$$
(\widetilde K_j(t,s)\otimes I_R)\rho^h_{VR}
 (\widetilde K_j(t,s)^\dagger\otimes I_R)
       \otimes|r_j\rangle\langle r_j|.
\tag{CP.21}
$$

Up to a fixed ordering of tensor factors, its failure density in mode $2$ is

$$
A_j(u,s)^2|f\rangle\langle f|\otimes(\rho^h)^R_{22}
       \otimes|\zeta_{j,2}(u)\rangle\langle\zeta_{j,2}(u)|\,du,
\tag{CP.22}
$$

and in either mode $1$ or $3$ it is

$$
\frac12B_j(u,s)^2|f\rangle\langle f|\otimes(\rho^h)^R_{--}
       \otimes|\zeta_{j,-}(u)\rangle\langle\zeta_{j,-}(u)|\,du.
\tag{CP.23}
$$

All old classical source/epoch, calibration, permission, clock, controller
and archive fields remain in their actual blocks. Append the actual request,
live or failure flag and, on failure, exact original time and mode. Equations
(CP.21)–(CP.23), integrated against the same actual history measure, are the
joint law, not a product of separately chosen marginals.

If the actual clock at interval start $s$ reads $\tau_s$, a live cut at $t$
has working clock $\tau_s+t-s$, and a first failure at $u$ is recorded at
$\tau_s+u-s$. Past clock entries remain archived; the working clock advances.
On live return the public catalogue becomes
$(k_1(t),k_2(t))$, the actual latent height is its original-index member,
and the real phase lift adds $b(t)-b(s)$ without becoming a readable field.
The specified controller update acts on the actually obtained request and
outcome. Failure latches its first event, cancels the unexecuted native tail
and retains the stopped branch with that same archive and programme successor.
There is no further positive-carrier height update from $f$.

Proof. Apply (CP.18) and (CP.17) to each input matrix block. The middle jump
selects precisely its $22$ block; either minus jump selects its $--$ block.
The programme factors on live success, and its failure vector is the displayed
$\zeta$. Their squared norms are the corresponding rates by (CP.16), giving
(CP.9) after tracing that register. Linearity gives every actual history
mixture, with no invented coupling. $\square$

For the actual pure orbit, $S_j(t)=x_j/k_j(t)>0$. Conditioning on live success
reweights a history distribution by this actual probability. An old archive
marginal need not stay fixed under this conditioning; the unnormalized joint
map is the preservation statement. In particular the returned live programme
is independent of $\beta,m$ conditional on $j$, but a mixed distribution over
$j$ can correlate it with archives and the survival flag.

If a failure rate or reference block has zero mass, its CP density is zero.
No normalized conditional state is assigned at that zero-probability event.
Otherwise the normalized failure programme is its actual $\zeta$ divided by
its norm. It need not equal $r_j$, and there is no original retry from $f$.

Exact time here is a measurable record, with Borel events and density maps.
It is not a finite-bit timestamp or an uncountable orthonormal Hilbert basis.
This distinction retains the [Event Memory][EMA] same-event contract.

## 7. Closed form for a horizontal ramp

**Corollary 7.1 (sharp all-prefix ramp threshold).** Fix $L>0$ and
$0<d<c-x_2$. For $a(t)=dt/L$, $b(t)=0$, put
$q_j(u)=(x_j+u)(c-x_j-u)$. Then the greatest feasible programme overlap for
one causal realization exposing every live cut is

$$
\mu_{\rm causal}=\min\left\{
\frac{2\sqrt{x_1x_2}}{x_1+x_2},\
\frac{2\sqrt{q_1(0)q_2(0)}}{q_1(0)+q_2(0)},\
\frac{2\sqrt{q_1(d)q_2(d)}}{q_1(d)+q_2(d)}\right\}.
\tag{CP.24}
$$

This is an attained threshold for the complete exact-time/five-mode instrument,
not merely a necessary bound on its survival.

Proof. Since $v=d/L>0$, the middle inequality in (CP.10) is
$\mu\le2\sqrt{k_1k_2}/(k_1+k_2)$. Its square is
$1-(x_2-x_1)^2/(k_1+k_2)^2$, increasing with $u=a(t)$, so its minimum is
at $u=0$. The minus inequality is
$\mu\le2\sqrt{q_1q_2}/(q_1+q_2)$. Let
$m=(k_1+k_2)/2$, $h=(x_2-x_1)/2$ and $D=m(c-m)-h^2>0$. Then

$$
\frac{q_2-q_1}{q_1+q_2}=\frac{h(c-2m)}D,\qquad
\frac{d}{dm}\frac{h(c-2m)}D
 =\frac{h[-2D-(c-2m)^2]}{D^2}<0.
\tag{CP.25}
$$

Its absolute value has its largest value at an endpoint. The squared minus
threshold is one minus that squared ratio, so its minimum is at $0$ or $d$.
The functions are continuous; failure of an endpoint bound gives failure on a
positive-length adjacent interval, so an almost-everywhere criterion gives
exactly (CP.24). Theorem 4.1 supplies attainment at equality. $\square$

## 8. A finite terminal-versus-intermediate separation

**Proposition 8.1 (one complete terminal processor without a prescribed live
checkpoint).** Take

$$
c=1/4,\quad Z=r=1/2,\quad
x_1=1/8,\quad x_2=3/16,\quad d=1/32,\quad L=1,\quad \mu=19/20.
\tag{CP.26}
$$

A common terminal processor for the whole exact-time/five-mode ramp instrument
exists under [IB], Theorem 18.1. Nevertheless no exact causal implementation
can expose its canonical live specimen at $t=3/4$ and then the matching
remaining original tail. The obstruction already uses a finite checkpoint
and a finite suffix, with strict positive support throughout.

Proof. The credited terminal threshold is

$$
\mu_{\rm time}=\min\left\{
\frac{\sqrt6\log(15/14)}{1-\sqrt{24/35}},\
\frac{4\sqrt3\log(15/14)}{1-3/\sqrt{35}}\right\}>19/20.
\tag{CP.27}
$$

To verify the strict comparison without relying on decimal rounding, set
$z=1/29$. Then $\log(15/14)=2\operatorname{artanh}z$. With
$L_6=2\sum_{n=0}^5z^{2n+1}/(2n+1)$,

$$
L_6<\log(15/14)<L_6+
\frac{2z^{13}}{13(1-z^2)}.
\tag{CP.28}
$$

The lower bound uses positive omitted terms; the upper bounds each remaining
denominator below by $13$ and sums its geometric series. Rational square-root
brackets in (CP.27) give
$96974/100000<\mu_{\rm time}<96976/100000$.
For example brackets of denominator $10^{30}$ are obtained from
$n=\lfloor\sqrt{p\,10^{60}/q}\rfloor$ for each rational radicand $p/q$:
$n/10^{30}\le\sqrt{p/q}<(n+1)/10^{30}$. Substitution in (CP.28) verifies
both candidates exceed $19/20$. Thus the supplied terminal theorem applies;
it expressly does not supply an intermediate quantum slot.

For comparison, the three squared bounds in (CP.24) are
$24/25$, $48/49$ and $105/121$. Hence
$\mu_{\rm causal}=\sqrt{105}/11<19/20$.

For the stronger finite-checkpoint certificate suppose the claimed prefix and
suffix both exist. At $s=3/4$ the two heights are $19/128$ and $27/128$, with
remaining displacement $1/128$. Lemma 4.2 forces the complete successful
residue overlap still to be $19/20$. The suffix minus squared attenuations
are $B_1^2=57/65$ and $B_2^2=27/35$. Lemma 4.3 requires

$$
\mu\le\frac{\sqrt{(1-B_1^2)(1-B_2^2)}}{1-B_1B_2}
 =\frac{\sqrt{2275}+\sqrt{1539}}{92}
 <\frac{87}{92}<\frac{19}{20}.
\tag{CP.29}
$$

Indeed $2275<(477/10)^2$ and $1539<(393/10)^2$. This contradiction does not
use an infinitesimal suffix, a near-wall limit or an assumed programme-return
condition. $\square$

**Example 8.2 (the same counterexample on actual original histories).** Use
the common six-unit preparation (CP.5) with $a_0=1/8$, $q=1/16$ and
$B_{\beta,m}=8\beta-4\pi m$, arriving at $x_j$. It realizes every
$\beta\in\mathbb R$ and signed $m\in\mathbb Z$, with prefix probability
margin at least $1/16$. The down and up rectangle legs survive with factors
$2/3$ and $1/2$. The arrival factors are $1$ and $2/3$, respectively.
Thus the actual prefix live probabilities are $1/3$ and $2/9$. The future
ramp has probability margin at least $1/32$. All prior failures remain
absorbing. The two programme states can be any supplied calibrated pure pair
of overlap $19/20$; their acquisition is not inferred from this preparation.

This is a mathematical separation between terminal feasibility and causal
refinability. It does not identify an error in the terminal supplier, which
already excludes the extra slot, and it does not compute a full-instrument
minimax error.

## 9. Coherent programme acquisition through the exact supplied RA port

**Definition 9.1 (the unchanged additional port premise).** Use exactly
[RA], Definition 13.2, at the double wall and public catalogue $x_1,x_2$.
During a declared calibration interval the same producer retains its actual
classical setting $k=x_j$. The native specimen makes a constant-height,
zero-relative-phase hold. A blank two-level probe has calibrated basis and
receives the permitted phase action

$$
R_k(A)=|0\rangle\langle0|+e^{ikA/r}|1\rangle\langle1|.
\tag{CP.30}
$$

Conditional on every actual history $h$ and every actual joint old state
$\rho^h_{SAR}$, the full service is
$\operatorname{id}_{SAR}\otimes\operatorname{Ad}_{R_{k(h)}(A)}$,
with old classical boundary fields retained. The source/epoch binding, stable
setting, native hold, probe route, gain $1/r$, coherent preparation, phase
reference, action and clock calibration, permissions and the joint identity
law are all the RA premises. No claim is made for a coherent superposition
of producer settings. The action is a probe action, not an unrecorded
increment of the old original relation phase.

On its promised live domain the RA service has no inconclusive or executed
failure branch. Known permission denial or known interface mismatch gives an
unexecuted rejection with the actual reason; it supplies no certificate.
An already stopped specimen keeps its absorbing successor. No detector for
an unflagged breach of the service promise is supplied here.

**Proposition 9.2 (an actually obtained unmeasured programme).** Prepare one
probe $(|0\rangle+|1\rangle)/\sqrt2$, apply action $A$ and retain it without
measurement. Conditional on height $x_j$ its programme is

$$
r_j(A)=\frac{|0\rangle+e^{ix_jA/r}|1\rangle}{\sqrt2},\qquad
\left|\langle r_1(A),r_2(A)\rangle\right|
 =\cos\frac{(x_2-x_1)A}{2r}
\quad\left(0\le A\le\frac{\pi r}{x_2-x_1}\right).
\tag{CP.31}
$$

For each actual history the full output is

$$
\rho^h_{SAR}\longmapsto
 \rho^h_{SAR}\otimes|r_{j(h)}(A)\rangle\langle r_{j(h)}(A)|.
\tag{CP.32}
$$

Thus this is acquired coherent height dependence, conditional on the supplied
RA port, independent of the unknown $\beta,m$ at each height. It is not an
installed unknown-height bit. When the overlap satisfies (CP.10), the common
processor of Section 5 consumes this programme for the causal original
request and returns it on live success.

Proof. Apply (CP.30) to the prepared probe. The overlap is
$(1+e^{i(x_2-x_1)A/r})/2$, whose modulus is the stated cosine on that interval.
Choose fixed representatives of the two known rays to make their overlap
nonnegative for Section 5. Rephasing a programme ket changes no input state
and no eigenvector-defined operator. Equation (CP.32) is precisely the RA
joint identity law, valid for every conditional old joint state; integrate
against the actual history measure to obtain its correlated mixture. The native
hold adds no survival charge or original phase increment. Clock advancement
and the calibration event are appended to the old archive. $\square$

## 10. Sharp restricted port action for the causal consumer

**Definition 10.1 (the spectator acquisition and action class).** During
acquisition the old specimen and its archives/reference are acted on by
identity. All new source dependence is through the port in Definition 9.1.
Initial probe/ancillary inputs and all controls are jointly common and
independent of $j,\beta,m$. No readable pre-existing source-bearing assistance,
source-sensitive timing input or installed index is permitted. All outcomes
are retained, and acquisition must provide a total implementation of the
subsequent causal target without deleting rejected or unsuccessful branches.

Use the exact charged access class of [RA], Definition 14.1: after dilating
every instrument and retaining its outcomes and environments, the common
implementation has, between finitely many common instantaneous operations,

$$
H_k(t)=H_0(t)-\frac{k}{r}G(t),\qquad
\mathcal A=\int_0^{T_c}\operatorname{diam}(\operatorname{spec}G(t))\,dt.
\tag{CP.33}
$$

Here $T_c<\infty$ is a common terminal time; $H_0,G$ are common bounded
self-adjoint operators, norm-measurable with integrable norms on each piece.
The full coherent implementation includes retained outcomes, controls and
routing. Common mixed inputs may be purified independently of the source.
Finite-dimensional protocols are included. Parallel couplings and coherently
controlled inverse calls pay their full spectral width. Early branches can be
latched and padded with the port off; cost is the whole padded implementation's
action, not its expected cost or a selected branch's cost. Calibration and
execution processors remain supplied ideal services.

**Theorem 10.2 (attained restricted acquisition price).** For the zero-phase
ramp of Corollary 7.1, the minimum action in Definition 10.1 sufficient for its
exact causal consumer is

$$
\boxed{\mathcal A_{\rm causal}
   =\frac{2r}{x_2-x_1}\arccos\mu_{\rm causal}.}
\tag{CP.34}
$$

The unmeasured probe (CP.31) attains it, followed by the complete processor of
Section 5. This is a minimum over the stated spectator acquisition class,
not over protocols interacting with the old specimen or reading additional
correlated archives.

Proof, lower bound. Purify the common initial probe and ancillas and retain
every outcome environment. Because acquisition is spectator and all source
dependence enters through (CP.33), its two complete final vectors $\eta_1,
\eta_2$ are a pure programme pair independent of $\beta,m$. Granting the
subsequent processor all purification residues only enlarges its access;
it can simulate the actual retained-record protocol by common dephasing and
discarding. Thus Theorem 4.1 applies to that enlarged pair, giving
$|\langle\eta_1,\eta_2\rangle|\le\mu_{\rm causal}$. This argument includes
all acquisition outcomes; it does not renormalize an accepted subensemble.

Let $W_j(t)$ be the two dilated unitaries and
$V_{\rm rel}=W_1^\dagger W_2$. On each continuous piece its generator is

$$
i\dot V_{\rm rel}=L(t)V_{\rm rel},\qquad
L(t)=-\frac{x_2-x_1}{r}W_1(t)^\dagger G(t)W_1(t).
\tag{CP.35}
$$

Common instantaneous unitaries cancel in $V_{\rm rel}$. Subtracting the
instantaneous expectation of $L$ from the ray velocity gives projective speed
$\sqrt{\langle L^2\rangle-\langle L\rangle^2}$. If the spectrum of $L$ lies
in $[a,b]$, positivity of $(L-aI)(bI-L)$ bounds its variance by
$(b-\langle L\rangle)(\langle L\rangle-a)\le(b-a)^2/4$.
Hence projective length is at most $(x_2-x_1)\mathcal A/(2r)$.

For completeness the endpoint angle bound holds for these merely integrable
generators. Multiply the absolutely continuous unit path by the phase
$\exp(i\int\langle L\rangle)$ to obtain a horizontal path $w$ of that
variance speed. In the real Hilbert sphere, set
$u(t)=\operatorname{Re}\langle w(0),w(t)\rangle$. Tangency and
Cauchy–Schwarz give $|u'|\le\sqrt{1-u^2}\|w'\|$. Integrating the derivative
of $\arccos u$, with limiting truncations at $u=\pm1$, bounds spherical
endpoint distance by length. Projective angle is no larger, since the absolute
inner product is at least its real part. Therefore

$$
\arccos|\langle\eta_1,\eta_2\rangle|
 \le\frac{(x_2-x_1)\mathcal A}{2r}.
\tag{CP.36}
$$

Combining the required overlap bound with (CP.36) proves (CP.34) from below.
This is the mature query-angle argument used in RA; its different endpoint
here is the necessary causal programme overlap, rather than orthogonal labels.

Proof, attainment. Put $A=\mathcal A_{\rm causal}$ in (CP.31). Since
$0<\mu_{\rm causal}<1$ for distinct heights and $d>0$, this action is between
$0$ and $\pi r/(x_2-x_1)$. Its programme overlap is exactly
$\mu_{\rm causal}$. One positive scalar drive $G(t)=u(t)|1\rangle\langle1|$
with $\int u=A$ has action $A$ and gives (CP.32) without measurement or
acquisition loss. Corollary 7.1 and Section 5 supply the required causal
consumer and all its failure successors. $\square$

**Example 10.3 (priced continuation at the rational catalogue).** For (CP.26),
the coherent programme sufficient for the causal ramp costs
$16\arccos(\sqrt{105}/11)$, whereas the credited exact height-bit acquisition
cost is $8\pi$. The former is strictly smaller because its target overlap
is nonzero; it is not an exact readable height certificate. With its attaining
programme the native ramp survival probabilities are $4/5$ and $6/7$.
Combining with the actual prefix masses of Example 8.2 gives final live masses
$4/15$ and $4/21$. Calibration contributes factor one only under the explicit
RA no-loss joint port premise. If the charged width is bounded by $v_*>0$,
interrogation duration is at least $\mathcal A_{\rm causal}/v_*$, attained by
the scalar constant drive under instantaneous ideal endpoint operations.
Preparation, control, certification and recorder overhead remain additional.

## 11. Executable menu, finite feedback and resource correspondence

**Proposition 11.1 (finite lawful selection and same-live-branch continuation).**
Start with the calibrated pure programme and public candidate pair. At each
reached live cut let a finite selector choose a public relative path using
only actually retained requests, live/stopped flags, common metadata, public
randomness and permitted common controller inputs. Every selected path must
be monotone, legal at both current candidate heights and satisfy (CP.10) for
the retained programme pair. Supply its calibrated Section 5 processor and
its explicit boundary updates. Then every finite such protocol has exactly
the sequential canonical CP law, including all time/mode failures and old
joint spectator correlations. At each live return the programme is unchanged
and the public candidate pair updates by the actual selected displacement.

Proof. For a fixed reached record, (CP.21) is the actual live input to the next
processor; the programme is product conditional on the same actual index.
(CP.22)–(CP.23) give the full stopped successors. CP composition, propagator
composition and (CP.20) show that first-failure branches and the all-live branch
exhaust the original input. Integrate over the same acquired record and public
randomness, then induct over the finite number of selected requests. Real
phase integrals add at each literal chronological join. The actual initial
$\beta,m$ are never controller variables. $\square$

The live overlap invariant of Lemma 4.2 is necessary even for alternative
implementations with arbitrary common memory updates. The attaining feedback
protocol chooses the simple unchanged programme. A measurement or new update
that changes its assistance must establish the next whole-input contract
before another invocation; a numerical overlap alone supplies neither the
actual quantum pair nor a calibrated processor.

The proved service accepts only requests certified in its public menu: legal
on both candidates, with the declared rate inequalities and supplied
permissions. A known permission denial, known interface mismatch or request
outside this service menu has an unexecuted rejection, its actual reason and
the retained state/context. Verification of the waveform and inequality
certificate is a separate supplied computation, not a sensor for the unknown
past. This does not provide a guard that executes at one candidate and rejects
at the other. An unflagged violation of the source or port promise is outside
the service; no universal detector is constructed. Original executed failure
instead keeps its actual first time/mode, programme successor and absorbing
$f$, with no reset, reversal, fresh specimen or post-failure retry.

The map from source to action to observation to resources is explicit:

| Interface | Actual object, output and charged boundary |
| --- | --- |
| Source and preparation | (CP.1)–(CP.5), the same preparation and strict heights, every real $\beta$ and signed $m$, literal original chronological interfaces. Past waveform and lift remain unknown. |
| Acquired extra dependence | Only the exact RA probe route (CP.30)–(CP.32), with same source/epoch, stable setting and old-joint identity law supplied. It yields an unmeasured programme, not a full probability law or height bit. |
| Selected original operation | A public relative monotone path and the common joint generator (CP.16), lawful at both tracked candidates. No source index is read to select its eigenvalue. |
| Complete observation and successor | Live specimen and returned programme (CP.21), or actual exact first time and one of five original mode names with (CP.22)–(CP.23) and absorbing $f$. No hidden Kraus index is exposed. |
| Quantum carrier | Qutrit $V$ and two-dimensional programme span for $\mu<1$, live tensor dimension six before counting all other fields. This is an upper for this component, not a full-observer dimension minimum. |
| Classical and reference retention | Old source/preparation/epoch, permission, calibration, actual clock, requests, selector/controller inputs, acquired archive and stopped status are retained separately and jointly. Exact real timestamps are not finite-state memory. |
| Acquisition cost | Spectral-width action (CP.33) on all retained outcomes; (CP.34) is sharp only in the spectator class. The producer coupling, its authentication and certification are unconstructed services, not zero-cost consequences of the action formula. |
| Execution and descriptions | Known calibrated programme rays, basis and joint CP operations; actual command generation, overlap/inequality certification, timing, arithmetic, precision, recording and hardware are separate resources. General exact real waveforms need not have finite effective descriptions. |

For $\mu<1$ the known programme eigenvector matrix has condition number
$\sqrt{(1+\mu)/(1-\mu)}$. It is invertible, and the ideal generators are
integrable; this does not prove a noise-stable or physically bounded hardware
implementation. All statements are exact and finite-horizon. No finite-noise
clock guarantee, acquired derivative certificate, finite-shot marked-density
estimate or uniform unbounded-horizon approximation is supplied.

## 12. Credited suppliers, primary attribution and the remaining goal

**Literature statement 12.1 (ownership and nonduplication).** The source-specific
local criterion (CP.10), its common causal construction, finite checkpoint
separation and restricted coherent-port consumer are `repo-derived` ordinary
deductions in this volume. Gram positivity, pure-state dilation, dissipative
propagators and projective-angle bounds are mature mechanisms. No worldwide
priority claim is made from a bounded literature comparison.

| Supplier at the stated public snapshot | Exact contribution and retained limit |
| --- | --- |
| [FiniteRectangleTransport][FRT], `ValidBase`, `probability`, `phaseWeight`, `weight_compatible`, `finite_rectangles_realize`, and [its Scribe][FRTB] | The positive geometric source, compatible rectangles and signed phase-leg realization. The rectangle declaration by itself is not an all-winding preparation theorem or a quantum actuator. |
| [OriginalControlComposition][OCC], `FiniteC1Control`, `OriginalControl`, `concatenate_original`, and [its Scribe][OCCB] | Both original regularity alternatives, zero duration, matching heights, literal prefixes, translated real lifts and additive integrals. No unknown old lift is supplied to a controller. |
| [Instrument Boundaries][IB], Sections 4–5, 17–23 and 24–27 | Canonical optimal instrument, terminal overlap threshold, actual-orbit rigidity, supplied finite sequential processors and mixed-programme rank-sum capacity. The local criterion adds one causally refinable running process; its finite ramp does not replace unrestricted-menu orthogonality, and algebraic directness is not orthogonality. |
| [Instrument Stability][IS] and [Sampled Instrument Certificates][SCI], Sections 2–3 and 7–8 | Existing strong error data, finite-table approximation and the extra joint sampler kernel retain their promises. This volume assumes neither that sensor nor acquired loss-rate densities, and adds no approximation-rate claim. |
| [Quantum Carrier Minimum][QCM], Sections 1–3 and 7–9 | Calibrated $M_3$ five-labelled restriction and actual multi-height witnesses; generated finite labels from a known anchor and received-command retention are not unknown-past acquisition. |
| [Event Memory and Coarse Aliasing][EMA], Sections 2 and 4–6 | Actual exact-event retention differs from known-programme marginal resampling. The exact-time recorder here remains an ideal measurable service. |
| [Parity Record Transport][PRT], Sections 3, 9, 12–15 and 17–23 | Additional helper, live-update and source-owned return-record contracts, with their attained yield/error frontier, remain separate. Programme return on live success does not imply return on failure. |
| [Reanchoring Boundaries][RB], Sections 2–3 and 7 | Phase-independent-assistance reanchoring obstruction and additional endpoint service concern a different operation. The present monotone process neither measures height nor reanchors to a common height. |
| [Acquired Continuation Limits][AC], Sections 3, 6–7 and 13 | Actual twelve-history output defect $1/11$, live error lower bound $1/22$, unconditional lower bound $1/99$ and joint necessity $\kappa+2\epsilon\ge D$ remain credited. None is a complete-instrument minimax value. The conditional RA port is additional input, not a specimen-only evasion. |
| [Record Acquisition][RA], Sections 13–17 | Exactly the additional source-bound phase port and charged access class used in Sections 9–10; exact height-bit price $\pi r/(x_2-x_1)$ is reused. The port remains supplied. The smaller coherent-programme price has a different restricted consumer and excludes old-specimen interaction. |
| [Transport–Memory Completion][TM], Sections 2.9–2.12 and 2.18; [Process Geometry][PG], Section 34; [Atlas Stable Core][ATLAS], Theorem 6.3 | Common coherent source, actual ports, acquired aligned readings, nonzero calibrated amplitudes/overlaps, joint success/failure image and each individual view's executable sufficiency remain obligations. The present joint component does not establish those full interfaces. |

The relevant primary literature is used at the following explicit scope:

| Primary text | Mature result and original-source transfer boundary |
| --- | --- |
| A. Chefles, R. Jozsa and A. Winter, [*On the existence of physical transformations between sets of quantum states*, quant-ph/0307227v1](https://arxiv.org/pdf/quant-ph/0307227v1), Theorems 2–3, Sections 2–3 | The pure-family Gram framework and multi-outcome extensions concern given input families and common physical transformations. Lemmas 4.2–5.1 instantiate contractions directly on the actual original orbit and its pure programmes; that framework supplies neither their acquisition nor chronological slots. |
| G. Chiribella, G. M. D'Ariano and P. Perinotti, [*A theoretical framework for quantum networks*, 0904.4483v1](https://arxiv.org/pdf/0904.4483v1), Theorems 5–6, especially the successive normalization identities (40) | A terminal channel and a sequence with accessible causal slots obey different normalization requirements. Here (CP.18)–(CP.20) verify the actual interval restrictions directly; a comb realization theorem does not furnish the original source or its port. |
| L. Leppäjärvi and M. Sedlák, [*Incompatibility of quantum instruments*, 2212.11225v2](https://arxiv.org/pdf/2212.11225v2), Proposition 7, complementary-instrument/postprocessing characterization | Instrument comparison must include state changes and compatible common realizations. A mathematical complementary instrument is not free access to an original hidden environment. No environment access is used in the attaining construction. |
| A. Jenčová, [*Randomization theorems for quantum channels*, 1404.3900v1](https://arxiv.org/pdf/1404.3900v1), abstract and randomization framework | Comparison through common channel pre/postprocessing presupposes the input experiment and access. It is contextual attribution, not an acquisition theorem or an inference from separately matching marginals. |

These primary texts do not, within the inspected scopes, furnish the required
source-bound RA coupling or an acquired original observer. That bounded
comparison is neither an absence theorem nor an originality certificate.
The universal claims here rest on the ordinary proofs, with no Lean compilation
or independent formal certification asserted.

**Verification boundary 12.2 (finite decisive arithmetic).** Rational arithmetic
and integer square-root enclosures verify the three squares in (CP.24) at
(CP.26), the two squared suffix attenuations, the strict radical comparison
(CP.29), both terminal candidates in (CP.27) using (CP.28), and final live
masses $4/15,4/21$. The dissipation determinant and derivative (CP.25) are
algebraic identities proved above. No numerical experiment substitutes for
their universal proofs, and no experiment programme or data file is needed
for these finite exact checks.

**Open boundary 12.3 (the original acquisition and recovery programme).** The
unaugmented original observer still has no constructed and certified route
from an arbitrary unknown past to the RA producer coupling or another
sufficient joint reference. Its missing pieces include actual source/epoch
authentication, stable-setting carrier, permitted nondisturbing probe coupling,
reference/gain/clock calibration, complete acquisition failure behavior and
their physical and informational costs. Installing (CP.30) as an unexplained
oracle would assume that gap away.

Readable phase/winding-correlated archives, arbitrary nonmonotone paths,
changing menus outside (CP.10), exact current-height guards and acquisition
interacting with the old specimen are not characterized by these theorems.
Neither full marked-law acquisition nor the complete-instrument minimax values
left open in AC are obtained. Transport–Memory's acquired interference data
and individual Atlas-view sufficiency remain unsupplied. Full mutual recovery
of space, time, boundary and memory, native memory/cofinality and the separate
fixed-Hamiltonian quantum minimax objectives retain their unresolved scope.
No action, observation or resource law is transferred from the stationary
alpha/beta source, PCA, KBONACCI, NativeLiteralMoore, C114, twisted-ground
lattices, TwoClockKrylovClosure or the independent fixed-Hamiltonian model.

[FRT]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean
[FRTB]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/Blueprint/D5/S3/Quantum/Fibers/FiniteRectangleTransport.scribe.cs
[OCC]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/D5/S3/Quantum/Fibers/OriginalControlComposition.lean
[OCCB]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/Blueprint/D5/S3/Quantum/Fibers/OriginalControlComposition.scribe.cs
[IB]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md
[IS]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md
[QCM]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md
[RA]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_RECORD_ACQUISITION.md
[SCI]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_SAMPLED_INSTRUMENT_CERTIFICATES.md
[EMA]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_EVENT_MEMORY_AND_COARSE_ALIASING.md
[PRT]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_PARITY_RECORD_TRANSPORT.md
[RB]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_REANCHORING_BOUNDARIES.md
[AC]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_ACQUIRED_CONTINUATION_LIMITS.md
[PP]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md
[TM]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[PG]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[ATLAS]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md

## 追加锚（本行以下为增补区）

## 13. Arbitrary original height reversals and the full phase source

The monotonicity restriction in Definition 2.3 and Open boundary 12.3 is
removed below for the same two-height, pure-programme consumer. The source,
canonical survival and complete marked instrument remain those of [Instrument
Boundaries, Section 5.2][NMIB] and [Quantum Carrier Minimum, Section 2][NMQCM].
The additional mathematical step is conservation of the whole purified
live-programme overlap when the lossless direction changes along an arbitrary
absolutely continuous path. The generator, Gram-coordinate test and producer
port are reused from Sections 5 and 9–10. These are ordinary conditional
mathematical results, with no Lean or physical certification asserted.

**Definition 13.1 (the unchanged source and whole-input promise).** Fix the
same preparation, source and epoch, $0<Z<1$, $r=1-Z$ and $c=r/2$.
The five probabilities and calibrated orthonormal directions are (CP.2)–(CP.3),
with arbitrary fixed preparation phases, including unequal phases within
paired modes. Write the full reachable current family as

$$
\psi(k,u,w)=\sqrt{2k}e^{-iu}|+\rangle+
 \sqrt{2(c-k)}e^{-iw}|-\rangle+\sqrt Z|2\rangle,
\qquad (k,u,w)\in(0,c)\times\mathbb T^2,\quad
\mathbb T=\mathbb R/(2\pi\mathbb Z).
\tag{CP.37}
$$

This is exactly [Probability/Phase Transport Continuation, Definition
12.1][NMC], in the calibrated basis, with its $L=c$ and its two phase
coordinates denoted here by $u,w$. Reachability from the one fixed preparation
is the credited original-control synthesis, not a newly available preparation
service. The subfamily $u=\beta$, $w=\beta-\pi m$ is (CP.4); all its signed
real histories remain included. A current ray does not identify the old real
lift, winding, waveform, chronological record or permissions.

The two possible current heights are public numbers $0<x_1<x_2<c$.
Conditional on the actual index $j$, supply the normalized calibrated pure
programme $r_j$, with representatives chosen so that
$\langle r_1,r_2\rangle=\mu\in[0,1]$. It is independent of both unknown
phase coordinates and of the actual producing history conditional on $j$.
All other accessible assistance is jointly common and source independent,
as in Definition 3.1. In particular source-dependent descriptions, clocks,
selectors, permission tokens, receiver shares and readable archives cannot
hide additional height or phase information. The public catalogue reveals
$x_1,x_2$, not $j$. Old history-correlated classical or quantum references
may remain, with identity action and without serving as processor inputs.
For each actual history the programme factors from those old systems.

The target is the prescribed canonical instrument, an additional operation
contract beyond geometric transport. Sufficiency assumes calibrated ability
to implement the common joint operators constructed in Section 15, together
with common ancillary inputs, waveform generation, actual rights, clock and
exact-time/five-mode recording. It does not assume a box already controlled
by the unknown index. Geometric transport alone installs none of these
services. The exact joint laws below apply to arbitrary
$\rho_{VR}\otimes|r_j\rangle\langle r_j|$
with unchanged reference $R$; no accessible history-bearing reference is
silently introduced by this notation.

**Definition 13.2 (the full original command domain).** Let $T<\infty$,
$T\ge0$, and let $a,b:[0,T]\to\mathbb R$ start at zero. Retain both
original regularity alternatives: both controls are absolutely continuous,
or both are continuous finite piecewise $C^1$ with continuous derivative
rates on each closed partition piece, allowing repeated partition times.
The original finite variation of the real phase control is retained. The
second alternative implies absolute continuity by the credited
`OriginalControlComposition.original_ac` argument: integrate the rates on
each piece and telescope, with empty pieces contributing zero. No common
speed bound, finite number of derivative sign changes, bounded variation of
the derivative or finite monotonicity partition is required.

Set $k_j(t)=x_j+a(t)$. The whole request must be legal at both candidates:

$$
-\min_{[0,T]}a<x_j<c-\max_{[0,T]}a\quad(j=1,2).
\tag{CP.38}
$$

This is the original partial-operation guard of [Continuation, Theorem
10.5][NMC], not merely an endpoint test. Compactness gives a positive
interiority margin for each request. At actual initial lift $\chi_*$ the
tail is $\chi_*+b(t)$; $\chi_*$ is not supplied to the controller.
Matching endpoints, literal prefixes, translated real tails and additive
integrals use the credited `concatenate_original`. Zero duration permits
only the matching identity. Requests legal at just one candidate retain
their original legal/invalid distinction; they are outside the common
service characterized here.

**Definition 13.3 (rates and the credited arbitrary-path instrument).** Write
$v=a'$ and $\omega=b'$ almost everywhere, and $v_+=\max(v,0)$,
$v_-=\max(-v,0)$. Put

$$
\begin{aligned}
\lambda_j&=\frac{v_+}{k_j}+\frac{v_-}{c-k_j},&
\Gamma_j&=\frac{|v|c}{k_j(c-k_j)},&
\delta&=\frac{(x_2-x_1)\omega}{r},\\
\ell_{+j}&=\lambda_j-\frac{v}{k_j}
          =\frac{v_-c}{k_j(c-k_j)},&
\ell_{-j}&=\lambda_j+\frac{v}{c-k_j}
          =\frac{v_+c}{k_j(c-k_j)},&
\ell_{2j}&=\lambda_j.
\end{aligned}
\tag{CP.39}
$$

All these nonnegative loss rates are integrable. For $0\le s\le t\le T$ define
$\Lambda_j(t,s)=\int_s^t\lambda_j$,
$E_{\alpha j}(t,s)=\exp(-\frac12\int_s^t\ell_{\alpha j})$ and
$\Phi_j(t,s)=\int_s^t k_j\omega/r$. In order $(+,-,2)$ the gauged live
operator is

$$
\widetilde K_j(t,s)=\operatorname{diag}\left(
 E_{+j}(t,s)e^{-i(b(t)-b(s))/2},\quad
 E_{-j}(t,s),\quad
 E_{2j}(t,s)e^{-i\Phi_j(t,s)}\right).
\tag{CP.40}
$$

Indeed $E_{+j}=e^{-\Lambda_j/2}\sqrt{k_j(t)/k_j(s)}$ and
$E_{-j}=e^{-\Lambda_j/2}\sqrt{(c-k_j(t))/(c-k_j(s))}$, by integrating
(CP.39). Multiplying (CP.40) by $e^{i\Phi_j}$ recovers the original
operator of [NMIB], (OC.19), restricted by [NMQCM], (QC.8)–(QC.10).
The scalar gauge changes no CP map and is not a source-dependent operation.

For $\rho_{VR}$ write $\rho^R_{\alpha\alpha}
=\langle\alpha|\rho_{VR}|\alpha\rangle$. Define
$\alpha(0)=\alpha(13)=+$, $\alpha(1)=\alpha(3)=-$, $\alpha(2)=2$,
and $h_0=h_{13}=h_1=h_3=1/2$, $h_2=1$. The prescribed failure measure is

$$
\mathcal I_{j,i}(d\tau)(\rho_{VR})=
 h_i\ell_{\alpha(i)j}(\tau)E_{\alpha(i)j}(\tau,s)^2
 |f\rangle\langle f|\otimes\rho^R_{\alpha(i)\alpha(i)}\,d\tau,
\quad i\in\{0,1,2,3,13\}.
\tag{CP.41}
$$

Labels $0,13$ and labels $1,3$ remain distinct, even when their density maps
coincide; a zero density is a retained zero-mass alternative. Exact first
time and the absorbing successor $f$ are part of the contract. An already
stopped input retains its old event and has only stopped continuation.
For the actual family (CP.37), survival through $t$ is
$S_j(t)=e^{-\Lambda_j(t,0)}>0$, and the normalized target is exactly
$\psi(k_j(t),u+b(t)/2-\Phi_j(t,0),w-\Phi_j(t,0))$.
Consequently it gives all five original complex edge values, with the
original orientation and signed doubled quadratures. This is equality of
the source state and its supplied read operations, not acquisition of all
noncommuting readings without a measurement service.

## 14. Conserved overlap and the sharp arbitrary-path criterion

**Theorem 14.1 (two-height causal programming on the entire original path
class).** Under Definitions 13.1–13.3, one common exact causal realization
of the canonical instrument at every cut exists if and only if, almost
everywhere,

$$
\boxed{\begin{aligned}
\mu^2\left[\left(\frac{\lambda_1+\lambda_2}{2}\right)^2+\delta^2\right]
 &\le\lambda_1\lambda_2,\\
\mu^2\left(\frac{\Gamma_1+\Gamma_2}{2}\right)^2
 &\le\Gamma_1\Gamma_2.
\end{aligned}}
\tag{CP.42}
$$

These are undivided inequalities, including zero rates. Necessity needs
only the actual original pure families, their prescribed survival at every
cut and causal consistency. It assumes neither programme return nor a
finite-dimensional memory. Sufficiency gives the complete exact-time,
five-labelled instrument on every $M_3$ input with every unchanged reference,
and returns $r_j$ unchanged on live success. Failure has its actual
programme successor and absorbing $f$, as specified in Section 15.

**Lemma 14.2 (one scalar overlap through arbitrary lossless-direction
switching).** In any realization in Theorem 14.1 there are unit purified
live residues $e_j(t)$ such that, for the success contraction $W_t$,

$$
W_t(q\otimes r_j)=\widetilde K_j(t,0)q\otimes e_j(t)
\quad(q\in V),\qquad
\langle e_1(t),e_2(t)\rangle=\mu\quad(0\le t\le T).
\tag{CP.43}
$$

The residue includes every success record and discarded environment; it
need not be accessible memory. No regularity of the individual vectors
$e_j(t)$ is assumed.

Proof. First reuse the coefficient-comparison rigidity of Lemma 4.2, which
does not need monotonicity for its factorization part. More explicitly, at
fixed $j,t$ put $z=e^{-iu}$, $y=e^{-iw}$. The input is
$d+zp+yq$, with the three nonzero vectors along $2,+,-$ respectively.
The exact normalized target is likewise $d_t+zp_t+yq_t$ with nonzero
coefficients. Purity makes the successful dilation that target tensor a
residue. Projection onto $2$ shows that this residue is affine in $z,y$.
Projection onto $+$ then has quadratic coefficients $z^2$ and $zy$;
linearity of $W_t$ makes both vanish. Comparing coefficients on the entire
two-torus therefore makes the residue independent of both phases. Its norm
is fixed by the prescribed survival $S_j(t)$. Comparing the three linear
coefficients and using the scalar convention (CP.40) gives the first
identity in (CP.43) with a unit $e_j(t)$. Vector-valued comparison can be
tested against continuous linear functionals. The same conclusion already
follows from the actual $\beta$/parity subfamily used in Lemma 4.2;
the argument does not posit additional source preparations.

Every $\widetilde K_j(s,0)$ is invertible at a finite cut. Additivity of
its rate and phase integrals and causal consistency give, for the interval
success contraction $F_{t,s}$,

$$
F_{t,s}(q\otimes e_j(s))
 =\widetilde K_j(t,s)q\otimes e_j(t),\qquad q\in V.
\tag{CP.44}
$$

In the dilation retain inaccessible earlier environments and let later
operations act trivially on them. This gives contractivity without supplying
an environment port. Define $g(t)=\langle e_1(t),e_2(t)\rangle$, with
$g(0)=\mu$. For either $\alpha=+$ or $-$ set
$L_{\alpha j}=\int_s^t\ell_{\alpha j}$ and
$d_j=e^{-L_{\alpha j}/2}$. The phase on this direction is common to the
two candidates. The input Gram matrix of the two vectors
$|\alpha\rangle\otimes e_j(s)$ minus their output Gram matrix is positive.
Its determinant gives

$$
|g(s)-d_1d_2g(t)|^2
 \le(1-d_1^2)(1-d_2^2).
\tag{CP.45}
$$

Since $|g(t)|\le1$, $1-e^{-x}\le x$ for $x\ge0$, and
$\sqrt{xy}\le(x+y)/2$, this implies, separately for both directions,

$$
\begin{aligned}
|g(t)-g(s)|
 &\le\sqrt{(1-e^{-L_{\alpha1}})(1-e^{-L_{\alpha2}})}
       +1-e^{-(L_{\alpha1}+L_{\alpha2})/2}\\
 &\le\sqrt{L_{\alpha1}L_{\alpha2}}
       +\frac{L_{\alpha1}+L_{\alpha2}}2
 \le\int_s^t(\ell_{\alpha1}+\ell_{\alpha2}).
\end{aligned}
\tag{CP.46}
$$

Either integrable bound makes the complex scalar $g$ absolutely continuous:
sum (CP.46) over disjoint intervals and use absolute continuity of the
Lebesgue integral. At a common differentiation point of $g$ and Lebesgue
point of both rate sums it also gives
$|g'|\le\ell_{+1}+\ell_{+2}$ and
$|g'|\le\ell_{-1}+\ell_{-2}$. By (CP.39), the first sum vanishes when
$v\ge0$ and the second when $v\le0$. Thus $g'=0$ almost everywhere,
and absolute continuity gives $g(t)=\mu$ at every cut. This excludes singular
variation of $g$; merely asserting a zero derivative without (CP.46) would
not suffice. No partition into monotone legs, finite turn archive or
continuity of the residue vectors enters the proof. $\square$

Proof of Theorem 14.1, necessity. With (CP.43), the interval Gram determinant
for direction $2$ reads

$$
\mu^2\left|1-E_{21}(t,s)E_{22}(t,s)
 e^{-i(\Phi_2(t,s)-\Phi_1(t,s))}\right|^2
 \le(1-E_{21}(t,s)^2)(1-E_{22}(t,s)^2).
\tag{CP.47}
$$

At a common Lebesgue point $s$, put $t=s+h$. The two diagonal deficits
are $h\lambda_j(s)+o(h)$, and the expression inside the absolute value is
$h[(\lambda_1(s)+\lambda_2(s))/2+i\delta(s)]+o(h)$.
Divide by $h^2$ and let $h\downarrow0$ to obtain the first inequality.
For either horizontal direction the same expansion in (CP.45), now with
$g=\mu$, gives
$\mu^2[(\ell_{\alpha1}+\ell_{\alpha2})/2]^2
\le\ell_{\alpha1}\ell_{\alpha2}$. Where $v>0$, choose $\alpha=-$;
where $v<0$, choose $\alpha=+$; these are exactly the two $\Gamma_j$
rates. At $v=0$ both horizontal rates vanish and the second test is $0\le0$.
The argument never divides by a loss rate. It proves necessity even for the
weaker task forgetting failure times, so it applies to the full contract.
Section 15 proves sufficiency. $\square$

**Corollary 14.3 (degenerate cases and the unrestricted menu).** Orthogonal
programmes, $\mu=0$, permit every commonly legal request in Definition 13.2.
For $\mu=1$ and distinct heights, a realization exists exactly for the
identity command $a=b=0$. If $\mu>0$, the first test forces $\omega=0$
almost everywhere on the set $v=0$. Zero duration is the identity.

Proof. At $\mu=1$, the first test is
$(\lambda_1-\lambda_2)^2/4+\delta^2\le0$. Distinct heights imply
$\lambda_1\ne\lambda_2$ wherever $v\ne0$, whether $v$ is positive or
negative. Hence $v=\omega=0$ almost everywhere. Absolute continuity and
the initial values give the identity command, which has its identity
implementation. The other statements follow from (CP.42) and the construction
below. In particular, allowing any nonzero phase-only request forces
orthogonality for a service covering the unrestricted common-legal menu.
That universal-menu boundary is credited prior work; the new result is the
arbitrary-sign extension for a specified request. $\square$

## 15. One common instrument, its references and all five successors

**Proposition 15.1 (attainment with integrable coefficients).** Suppose
$0\le\mu<1$ and (CP.42) holds. On $H=\operatorname{span}\{r_1,r_2\}$
define common operators by their action on the known independent basis:

$$
\begin{aligned}
C_+r_j&=(-\ell_{+j}/2-i\omega/2)r_j,&
C_-r_j&=-\ell_{-j}r_j/2,\\
C_2r_j&=(-\lambda_j/2-ik_j\omega/r)r_j,&
Q_\alpha&=-C_\alpha-C_\alpha^\dagger,\\
C&=\sum_{\alpha\in\{+,-,2\}}
 |\alpha\rangle\langle\alpha|\otimes C_\alpha.
\end{aligned}
\tag{CP.48}
$$

Then each $Q_\alpha\ge0$ almost everywhere. For the propagator
$\partial_tM(t,s)=C(t)M(t,s)$, $M(s,s)=I$, use the five jump fields

$$
J_0=J_{13}=\frac{|f\rangle\langle+|\otimes\sqrt{Q_+}}{\sqrt2},\quad
J_1=J_3=\frac{|f\rangle\langle-|\otimes\sqrt{Q_-}}{\sqrt2},\quad
J_2=|f\rangle\langle2|\otimes\sqrt{Q_2}.
\tag{CP.49}
$$

The live map $\operatorname{Ad}_{M(t,s)}$ and the first-failure measures
with Kraus fields $J_i(\tau)M(\tau,s)$ are one normalized causal CP
instrument. On a live input,

$$
M(t,s)(q\otimes r_j)=\widetilde K_j(t,s)q\otimes r_j.
\tag{CP.50}
$$

Proof. Reuse Lemma 5.1 with losses $\ell_{\alpha j}$ and frequencies
$\omega/2,0,k_j\omega/r$ in the three respective directions. For $2$,
positivity of its Gram-coordinate quadratic form is exactly the first test
in (CP.42). For the currently dissipative horizontal direction, the two
frequencies coincide, its losses are $\Gamma_j$, and positivity is exactly
the second test. The other horizontal direction has $Q=0$. This covers
all signs, including $v=0$. These are single operators on $H$, equivalently
$R_0\operatorname{diag}(z_{\alpha1},z_{\alpha2})R_0^{-1}$ for the
known eigenvector matrix $R_0$; no measurement of $j$ is performed.

Strict support and fixed $R_0^{-1}$ make $C$ norm-integrable. The
finite-dimensional integral equation has its absolutely continuous
propagator. Its fixed eigenvectors give (CP.50) and
$M(t,u)M(u,s)=M(t,s)$ directly. The positive matrix square roots in
(CP.49) are measurable with integrable squared norms. Values on the common
null exceptional set can be set to zero. The same normalization computation
as Theorem 5.2 now uses all five labels:

$$
\begin{aligned}
\sum_iJ_i(\tau)^\dagger J_i(\tau)&=-C(\tau)-C(\tau)^\dagger,\\
M(t,s)^\dagger M(t,s)+\sum_i\int_s^t
 M(\tau,s)^\dagger J_i(\tau)^\dagger J_i(\tau)M(\tau,s)\,d\tau&=I.
\end{aligned}
\tag{CP.51}
$$

Differentiate $M^\dagger M$ almost everywhere and integrate to prove the
second identity. Thus every branch is CP and their total is trace preserving.
Finite-dimensional integrable CP densities give countably additive measures
on Borel time events. Tensoring with identity gives the same statement for
every unchanged quantum reference. Splitting the integral at any checkpoint
and using propagator composition yields all finite checkpoint refinements
of this one process, including the late failure law on the actual live
successor. The stopped sector is absorbing. At $\mu=1$, Corollary 14.3
supplies the identity case, completing sufficiency in Theorem 14.1. $\square$

**Proposition 15.2 (the full joint law and actual programme successor).** For
fixed actual history $h$ of index $j$ and input $\rho^h_{VR}$, put
$\zeta_{\alpha j}(\tau)=\sqrt{Q_\alpha(\tau)}r_j$. Up to a fixed
ordering of tensor factors, the unnormalized live output is

$$
(\widetilde K_j(t,s)\otimes I_R)\rho^h_{VR}
 (\widetilde K_j(t,s)^\dagger\otimes I_R)
 \otimes|r_j\rangle\langle r_j|,
\tag{CP.52}
$$

and the output density with original label $i$ and first time $\tau$ is

$$
h_i E_{\alpha(i)j}(\tau,s)^2|f\rangle\langle f|
 \otimes(\rho^h)^R_{\alpha(i)\alpha(i)}
 \otimes|\zeta_{\alpha(i)j}(\tau)\rangle
             \langle\zeta_{\alpha(i)j}(\tau)|\,d\tau.
\tag{CP.53}
$$

Proof. Apply (CP.49)–(CP.50) to each input matrix block. Each jump selects
its indicated diagonal block, and scalar phases cancel in the CP density.
Moreover $\|\zeta_{\alpha j}\|^2=\langle r_j,Q_\alpha r_j\rangle
=\ell_{\alpha j}$. Tracing the programme gives precisely (CP.41),
including both separate half-strength labels in each pair. The live map is
exactly the credited original map because the gauge is scalar. This proves
equality on every $M_3$ matrix unit and every joint reference input, not
only on the original orbit or on its terminal statistics. $\square$

The actual joint law is (CP.52)–(CP.53) integrated against the same actual
history measure, retaining its source, preparation, epoch, real chronology,
rights, old archive, calibration, controller inputs and references. At
interval-start clock $\tau_s$, live time $t$ is $\tau_s+t-s$ and a failure
time $\tau$ is recorded at $\tau_s+\tau-s$. Past entries remain; the
working clock advances. Append the actual request, flag and, on failure,
its original label and first time. No hidden Kraus outcome is substituted
for those fields. Failure latches $f$, cancels the unexecuted original tail
and retains its displayed programme successor. A zero-mass event has no
assigned normalized successor; otherwise its programme is the actual
$\zeta$ divided by its norm. It need not be $r_j$.

Live return factors the programme conditional on $j$ and every actual history.
It does not force the unconditional programme or old archive marginal to be
independent of $j$ or the flag. Conditioning on survival reweights histories
by $S_j(t)$; identity on $R$ means the unnormalized joint operation, not an
assertion that such conditional marginals remain unchanged. Exact first
time is a measurable classical record, with Borel-event operations. It is
not an uncountable orthonormal basis or finite-state timestamp memory.

## 16. Finite lawful composition and original boundary updates

**Proposition 16.1 (returned-programme composition for arbitrary lawful
paths).** At each reached live cut, let a finite selector choose a public
relative request using only actually retained request/outcome records,
common metadata, public randomness and permitted common controller inputs.
For every reached record, require Definition 13.1's whole-input promise,
a request legal at both current candidates satisfying (CP.42), its calibrated
Section 15 processor and actual execution permissions. Then every finite
such protocol has the exact sequential canonical joint law, including
first times, all five mode names, programme successors and old spectator
correlations. On each live return its programme remains $r_j$ and its public
catalogue updates by the actual request displacement.

Proof. For one request this is Proposition 15.2. At a live endpoint the
public pair is $(x_1+a(T),x_2+a(T))$, with its gap and original index
unchanged. Conditional on that index and each reached record, (CP.52)
provides exactly the product programme needed for the next invocation.
The full phase torus is closed under the phase update in Definition 13.3,
so its phase/history independence remains the same promise. No actual
unknown phase is used by the selector. Fresh common auxiliary systems can
therefore implement the next common processor. Splitting (CP.51) preserves
the complete first-event law; the live maps multiply and the failure branch
is absorbing. Integrate over the same reached records and common random
inputs, then induct on the finite number of selected requests. Literal
original concatenation preserves the prefix and translates the real tail;
the integral phases and survival charges add. The conclusion includes every
finite checkpoint refinement of each request as part of that same process.
$\square$

This extends Proposition 11.1's request class, without adding a new selector,
readable correlated archive or return permission. If an intervention reads
such an archive, changes the programme, or changes the allowed specimen
support, it must establish the next whole-input and closure promises anew.
A numerical overlap by itself supplies neither the quantum input pair nor
an implementation. Each selected control can have arbitrarily many height
reversals; the number of selected controls and the observation horizon here
remain finite. No uniform capacity, unlimited-request termination or infinite
composition theorem is asserted.

**Boundary 16.2 (legal requests, service refusal and executed failure).**
The original guard is (CP.38). A request satisfying that guard may still
violate (CP.42); this is a programming obstruction for the specified
programme, not an original illegality label. The common supplied service
executes only requests certified legal at both candidates, satisfying the
rate tests and accompanied by its actual rights and calibrated processor.
A known permission denial, interface mismatch or request outside that
service menu gives an unexecuted rejection with its actual reason and
retained context. This supplies no total service executing at one candidate
and rejecting at the other. An unflagged breach of the source or interface
promise is outside the theorem; no detector for such a breach is constructed.

The original executed failure instead has exactly (CP.53), its first actual
time, original label, stopped status and failure programme. It does not
return a new live specimen. No tail is executed after $f$, no loss is
deleted by postselection, and no reset or retry is inferred from the live
programme-return identity. Waveform and almost-everywhere inequality
certification are explicit supplied computations, not sensors for an
unknown past. General exact AC functions need not have finite effective
descriptions or decidable finite inequality certificates.

## 17. A returned excursion with a stricter programme requirement

**Theorem 17.1 (exact two-leg return and its sharp overlap).** Take

$$
Z=r=\frac12,\quad c=\frac14,\quad
x_1=\frac1{16},\quad x_2=\frac3{16},\quad d=\frac1{64},\quad T=2,
\qquad b(t)=0,
\tag{CP.54}
$$

and let $a(t)=dt$ on $[0,1]$ and $a(t)=d(2-t)$ on $[1,2]$.
This is an original continuous finite-piecewise-$C^1$ request, legal at
both candidates for every original phase pair and actual history. The
largest feasible pure-programme overlap for its complete causal instrument is

$$
\mu_{\rm return}=\frac{\sqrt{33}}7.
\tag{CP.55}
$$

The programme $\mu=5/6$ permits the whole outward ramp but cannot realize
this returned excursion causally. Conditional on the initial live cut, the
whole-excursion survival probabilities are $11/15$ and $9/13$ respectively.
At live return the specimen ray and attaining programme both return;
chronological records, elapsed time, incurred action and stopped branches
are retained.

Proof, whole-path legality. Here $\min a=0$, $\max a=d$, so (CP.38)
is $0<x_j<15/64$. Both candidates satisfy it. Every original mode
probability is at least $3/64$ along both branches. The two pieces join
continuously at the apex. The height speed has magnitude $d$ almost
everywhere, the phase variation is zero, and all original weights and
integrals are those of the same source. Starting with any actual source
history at $x_j$ merely appends this literal excursion.

Proof, the three determinant bounds. Write $s=a(t)\in[0,d]$. Since
$\delta=0$, the middle test on the upward leg reduces to

$$
\mu^2\le U(s):=
 \frac{4(x_1+s)(x_2+s)}{(x_1+x_2+2s)^2}.
\tag{CP.56}
$$

Its value is $1-(x_2-x_1)^2/(x_1+x_2+2s)^2$, increasing with $s$.
Thus its minimum is $U(0)=3/4$. On the downward leg the complementary
heights give instead

$$
\mu^2\le D(s):=
 \frac{4(c-x_1-s)(c-x_2-s)}{(2c-x_1-x_2-2s)^2}.
\tag{CP.57}
$$

It is $1-(x_2-x_1)^2/(2c-x_1-x_2-2s)^2$, decreasing with $s$;
its minimum is $D(d)=33/49$. The value at the apex is understood as
the continuous limit from the downward leg; changing a derivative at the
single apex time changes no instrument.

For either leg put $q_j(s)=(x_j+s)(c-x_j-s)$. Cancelling the positive
common speed in the horizontal test gives
$\mu^2\le H(s):=4q_1(s)q_2(s)/(q_1(s)+q_2(s))^2$.
In this catalogue

$$
q_1(s)=A(s)+q(s),\quad q_2(s)=A(s)-q(s),\qquad
A(s)=\frac3{256}-s^2,\quad q(s)=\frac{s}{8}.
\tag{CP.58}
$$

The ratio $R(s)=(A-q)/(A+q)$ decreases from one: its derivative has
positive denominator $(A+q)^2$ and numerator
$-3/1024-s^2/4<0$. Since $4R/(1+R)^2$ increases with $R\in(0,1]$,
$H$ is minimized at $d$. There
$q_1(d)=55/4096$, $q_2(d)=39/4096$, giving

$$
\min U=\frac34,\qquad
\min D=\frac{33}{49},\qquad
\min H=\frac{4\cdot55\cdot39}{(55+39)^2}
       =\frac{2145}{2209}.
\tag{CP.59}
$$

The least of these is $33/49$, so Theorem 14.1 proves both the upper
bound and attainment of (CP.55), with the complete marked law. Continuity
also ensures that an excessive overlap fails on a positive-length interval,
not merely at an exceptional endpoint. In particular
$3/4-25/36=1/18>0$, whereas $25/36-33/49=37/1764>0$.
The horizontal bound exceeds $25/36$ everywhere. Thus $5/6$ passes
the entire outward leg and fails on a downward interval adjacent to the apex.

Proof, losses and the meaning of return. Integrating $\lambda_j$ on
the two legs gives

$$
S_j(2)=\frac{x_j}{x_j+d}\frac{c-x_j-d}{c-x_j},\qquad
S_1(2)=\frac45\frac{11}{12}=\frac{11}{15},\quad
S_2(2)=\frac{12}{13}\frac34=\frac9{13}.
\tag{CP.60}
$$

Since $a(2)=b(2)=0$ and $\Phi_j=0$, (CP.40) is
$\widetilde K_j(2,0)=\sqrt{S_j(2)}I_V$. Hence the live specimen
returns even on arbitrary $M_3$ inputs, while its mass has decreased.
The attaining programme returns by (CP.52). The actual clock advances by
two and the request/outcome is appended. Earlier failures, current first
failures and their programme successors remain. Each actual prefix's own
preparation survival multiplies (CP.60); no prefix loss is renormalized
away. The control duration is two, total height variation $1/32$,
essential maximum height speed $1/64$, and phase variation zero. These
are control-coordinate quantities; converting them to physical time,
energy, hardware or total cost requires the corresponding calibration.
Thus return is an identity of live state and programme, not an inverse of
the outcome-retaining channel or an erasure of actions and records. $\square$

## 18. The credited RA port priced for the return consumer

**Definition 18.1 (the supplied spectator acquisition class).** Retain
Definition 9.1 and the exact joint producer port of [Record Acquisition,
Definition 13.2][NMRA]. The same producer has actual stable classical
setting $k=x_j$ during calibration; the old specimen makes a permitted
constant-height, zero-phase hold. The separate probe receives
$R_k(A)=|0\rangle\langle0|+e^{ikA/r}|1\rangle\langle1|$.
For every actual history and conditional old joint state, the service is
identity on the old specimen, archive and quantum reference, tensor this
probe action. Source/epoch binding, gain, coherent blank and phase reference,
clock/action calibration, routing and permissions are supplied. The
functional phase-leg correspondence does not create this separate route.
It promises no coherent superposition of producer settings.

For the sharp price, restrict acquisition to Definition 10.1: all old
systems are spectators, all other accessible inputs and controls are jointly
common, and all new source dependence enters through
$H_k(t)=H_0(t)-(k/r)G(t)$. Charge
$\mathcal A=\int_0^{T_c}\operatorname{diam}(\operatorname{spec}G(t))dt$
on the whole common finite-time, coherently dilated and padded implementation.
The common bounded self-adjoint coefficients are norm-measurable with
integrable norms on each piece between finitely many common instantaneous
operations. Retain all outcomes and environments. Parallel and controlled
inverse couplings pay their full spectral width; early branches may be
latched with the port off. Expected accepted-branch action, free routing
queries, source-sensitive timing and specimen-using acquisition are not
this price contract. The task is a total implementation of the fixed
excursion's canonical causal law, including every acquisition outcome.

**Corollary 18.2 (attained restricted action for the returned excursion).**
Under Definition 18.1, the minimum action sufficient for the complete
consumer of Theorem 17.1 is

$$
\mathcal A_{\rm return}=8\arccos\left(\frac{\sqrt{33}}7\right).
\tag{CP.61}
$$

It is attained by the existing unmeasured single-probe programme and the
Section 15 processor. The credited exact readable height-bit task in this
access class costs $4\pi$. The smaller value (CP.61) does not produce
such a bit and is not a total hardware or acquisition-infrastructure price.

Proof. The acquired probe of Proposition 9.2 is
$r_j(A)=(|0\rangle+e^{ix_jA/r}|1\rangle)/\sqrt2$ and has overlap
$\cos((x_2-x_1)A/(2r))$ on the first discrimination arc. Here
$x_2-x_1=1/8$ and $r=1/2$, so that overlap is $\cos(A/8)$.
Put $A=8\arccos(\sqrt{33}/7)$; the overlap is exactly (CP.55).
The joint port law yields the programme as a product conditional on each
actual history, leaving the old joint state untouched. Theorem 14.1 and
Proposition 15.2 then realize the whole excursion, with all failure
successors retained. This is attainment using the same producer, not a
mathematical choice of a distribution installed as memory.

For the lower bound, purify all common acquisition inputs and retain all
outcomes and environments. Spectator acquisition produces complete pure
vectors $\eta_j$, independent of the original phases/history conditional
on $j$. Granting the subsequent processor these purification residues can
only enlarge its abilities: common dephasing and discarding simulate the
actual protocol. Theorem 14.1 therefore requires
$|\langle\eta_1,\eta_2\rangle|\le\sqrt{33}/7$.
The already established query-angle bound (CP.36), with precisely this
charged access class, gives

$$
\arccos|\langle\eta_1,\eta_2\rangle|\le\mathcal A/8.
\tag{CP.62}
$$

Combining proves (CP.61). This applies before any acceptance conditioning;
no failed acquisition branch is deleted. [NMRA], Theorem 14.2, gives the
readable-bit price $\pi r/(x_2-x_1)=4\pi$, with a spectator attaining
probe. The new value is an application of that existing acquisition method
and (CP.36) to the stricter returned-path consumer. $\square$

The ideal RA hold contributes no canonical native survival charge or
original phase increment, and its promised port has no inconclusive or
executed-failure branch. It still advances the clock, appends its actual
calibration event and incurs its whole paid action and overhead. Known
permission denial or interface mismatch is an unexecuted rejection; an
already stopped input remains stopped. No detector for unflagged promise
breach is supplied. If a width cap $v_*>0$ is imposed, the interrogation
time is at least $\mathcal A_{\rm return}/v_*$ in this access class;
a constant scalar drive attains that component under ideal instantaneous
endpoint operations. The two-unit excursion and every actual prefix are
additional chronology and cost.

## 19. Conditional relation object, resources and unpaid bridges

The sufficient conditional object is the calibrated current qutrit, its
actual source-bound programme, the public shifted height pair and all
mandatory source/request/record fields. The ideal propagator uses (CP.39)
pointwise and its integrals; it needs no extra turning-point archive to
conserve overlap. This is not a finite-description theorem for arbitrary
waveforms or a bound on the memory of a physical waveform generator.

| Component | Supplied object and retained cost or limitation |
| --- | --- |
| Actual source | One fixed positive preparation and its real histories, all original phases, strict five-mode probabilities, source/epoch identity and prefix survival. The catalogue is not a readable actual index. |
| Public command | The whole legal excursion, both original regularity alternatives, real translated lift, actual waveform and almost-everywhere tests. An endpoint signature alone neither certifies legality nor prices loss. |
| Programme | A calibrated normalized pure pair, independent of phase/history conditional on index, with all other accessible assistance jointly source independent. Its physical acquisition and authentication are additional obligations. |
| Attaining processor | The calibrated common Gram-basis operators, coupling, coherent blanks, arithmetic, clocks, gain and actual permissions. Near-dependent programmes have eigenvector condition number $\sqrt{(1+\mu)/(1-\mu)}$; ideal integrability does not certify noise stability. |
| Live/stopped quantum component | For $\mu<1$, qutrit times programme has live dimension six; the stopped programme sector has dimension two. Their classically flagged direct sum has dimension eight before all other fields. Using the unreduced original five-live-mode plus stopped carrier with the programme gives dimension twelve. The reduction itself requires the credited calibrated embedding. |
| Full record and reference | Old chronology, source/preparation/epoch, permissions, calibration, requests, controller inputs, clock and references, with the actual new flags, first times and five original names. No finite-bit exact-time or total observer-memory minimum follows. |
| Acquisition price | (CP.61) charges all source-sensitive action in the spectator port class. Blank preparation, stable producer setting, actual port, calibration, authentication, certification, recorder and execution overhead remain additional. |
| Failure and reuse | Actual failure programme, all lost mass and absorbing $f$ remain. Live-only ray/programme return gives neither inverse execution nor post-failure retry authority. |

The exact iff theorem is sharp for this specified two-element pure-programme
promise and canonical causal instrument. It does not identify a globally
smallest relation object, bit count, total memory, least authority or
Pareto-optimal implementation. It does not characterize a continuum of
unknown heights, readable height/phase-correlated assistance, mixed initial
programmes, source-dependent legality guards or protocols acquiring their
programme by interacting with the old specimen. Approximate hardware,
finite precision, noisy clocks, complete-instrument minimax values and
uniform infinite-horizon operation require separate results. The physical
availability of the stipulated producer route, authentication, joint
spectator identity, actuator and recorder is not verified by these ordinary
proofs.

The unresolved nonmonotone-path clause of Open boundary 12.3 is thus closed
only for Definitions 13.1–13.3 and the exact criterion (CP.42); its other
acquisition and broader recovery boundaries remain. In particular no new
native source sensor, general acquired reference, full marked-law acquisition,
all-four-expression recovery or worldwide minimality is inferred.
No operation is transferred to Native ordered trees or AA by matching names,
cardinalities, encodings or endpoint values.

The separate existing augmented $J_r$ result already supplies all declared
cuts, every finite ordered request forest, four actual received bodies and
selected-body/original owed-action return conditionally: [Atomic Supplier
Substitution II][NMJR], Theorems 65.3, 70.1–70.2 and 75.4. Its premises
include the complete actual entry, closed writers and external inputs,
source laws and gates, current source-bound authority, independently supplied
cut wake, fresh finite material and progress. That proved conditional domain
is reused; it is not reclassified as wholly open. Unaugmented or physical
sources, finer interiors obtained by splitting its atomic primitives,
broader alpha/beta-to-original-consumer bridges and global minimality remain
their own unpaid obligations. This continuous quantum service establishes
none of those correspondences or permissions.

## 20. Precise suppliers, mature tools and the mathematical delta

The operative repository suppliers for Sections 13–19 are the exact public
snapshot `61ab64d2844eb22ed95cd3c9e7fe6cfa343870b9`. Its [Continuation][NMC],
Definition 12.1 and Theorem 10.5, fix the original full phase family, signed
quadratures, whole-excursion guard and endpoint action. [Original Control
Composition][NMOCC], `FiniteC1Control`, `OriginalControl`, `original_ac` and
`concatenate_original`, supplies the unchanged regularity and literal
chronological composition. [Instrument Boundaries][NMIB], (OC.15)–(OC.19c),
and [Quantum Carrier Minimum][NMQCM], Definitions 2.1–2.2 and Theorem 3.1,
supply arbitrary-path canonical survival, calibrated qutrit embedding,
all five labels and the full joint reference law. These are reused results.

Sections 4–6 of the present volume supply the pure-orbit factorization,
programme Gram-coordinate positivity test, generator normalization and
failure-programme bookkeeping. Lemma 14.2's interval integral bounds and
scalar absolute-continuity argument supply the repository-new mathematical
step relative to the monotone theorem: the purified overlap remains fixed
through arbitrary AC sign changes, without assuming programme return.
Theorem 14.1 is its sharp full-path consequence. The returned-excursion
separation and its exact price are applications of that extension. Sections
9–10 and [Record Acquisition][NMRA], Definitions 13.2 and 14.1 and Theorem
14.2, own the additional joint port, unmeasured probe and spectral-width
query-angle mechanism; neither the route nor that mature lower-bound method
is claimed anew.

| Primary source | Credited tool and scope of use |
| --- | --- |
| A. Chefles, R. Jozsa and A. Winter, [*On the existence of physical transformations between sets of quantum states*, quant-ph/0307227v1](https://arxiv.org/pdf/quant-ph/0307227v1), Theorems 2–3 | Pure-family Gram constraints and probabilistic transformation framework. Here the contraction determinants are written for actual orbit-forced linear maps, with all dilation residues retained; no acquisition route follows from the Gram framework. |
| G. Chiribella, G. M. D'Ariano and P. Perinotti, [*A theoretical framework for quantum networks*, 0904.4483v1](https://arxiv.org/pdf/0904.4483v1), Theorems 5–6 and normalization identities (40) | Causal slot consistency differs from terminal channel feasibility. Equation (CP.51) and its interval splitting supply this particular continuous-time realization directly; a network realization theorem supplies no original actuator, source port or current right. |

Absolute continuity, Lebesgue differentiation, positive Gram determinants
and dissipative propagator normalization are standard mathematical tools.
The source-specific combination above is `repo-derived` ordinary theory;
worldwide novelty is unverified. Exact rational arithmetic in the excursion
reduces to the displayed fractions, margins and survival products; it does
not replace the general overlap proof or certify hardware. The supplied
conditional services and the larger recovery programme retain exactly the
boundaries in Sections 16 and 19.

[NMC]: https://github.com/the-omega-institute/trureturing/blob/61ab64d2844eb22ed95cd3c9e7fe6cfa343870b9/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY_CONTINUATION.md
[NMOCC]: https://github.com/the-omega-institute/trureturing/blob/61ab64d2844eb22ed95cd3c9e7fe6cfa343870b9/D5/S3/Quantum/Fibers/OriginalControlComposition.lean
[NMIB]: https://github.com/the-omega-institute/trureturing/blob/61ab64d2844eb22ed95cd3c9e7fe6cfa343870b9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md
[NMQCM]: https://github.com/the-omega-institute/trureturing/blob/61ab64d2844eb22ed95cd3c9e7fe6cfa343870b9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md
[NMRA]: https://github.com/the-omega-institute/trureturing/blob/61ab64d2844eb22ed95cd3c9e7fe6cfa343870b9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_RECORD_ACQUISITION.md
[NMJR]: https://github.com/the-omega-institute/trureturing/blob/61ab64d2844eb22ed95cd3c9e7fe6cfa343870b9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_SUPPLIER_SUBSTITUTION_II.md

## 追加锚（本行以下为增补区）
