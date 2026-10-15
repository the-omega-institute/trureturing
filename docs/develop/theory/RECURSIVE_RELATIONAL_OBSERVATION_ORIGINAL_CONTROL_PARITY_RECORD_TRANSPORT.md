# Recursive relational observation: parity records for original-control transport

> **Machine contract.** This is a `generic-v1` reference volume. Locators are
> determined from its bytes. Merged text and append anchors are preserved;
> corrections and extensions belong in new sections after the terminal append
> anchor. The volume supplies mathematical reference input, not machine status.

## 1. Scope, mathematical provenance and the conditional service

The question is whether an already supplied source-bound parity record can
enable the same height continuation on every unknown phase of an original
positive five-mode specimen. The answer depends on whether that record may
change on success. The results below give sharp one-cut probabilities for
both contracts and a sharp finite-checkpoint memory update when the record
may change. They do not construct the initial record.

These are ordinary finite-dimensional mathematical proofs. They have no new
Lean/kernel verification, independent-review status or physical realization
claim. The geometric source and its exact chronological composition are
credited suppliers. The mature Gram/isometry criterion is also credited;
the deductions here concern its particular original-source inputs and
retained-record constraints. Mathematical authorship is an isolated
delegated `codex-cli` author using the repository's
`formal-thinking-and-answer` and `theory-volume-template` skills. The supplied
prior-stage proposals are fallible inputs, consolidated into the proofs here;
this attribution confers no review or consensus status.

**Convention 1.1 (additional operation class).** The assisted service in this
volume is a common calibrated quantum instrument acting jointly on the live
specimen and one supplied helper. Its success target is the exact specimen
state at a declared endpoint or checkpoint. It keeps the full auxiliary
success output. Its executed failure stops the specimen and retains the
actual failure residue. This service, its coherent helper access, blank
ancillas and implementation permission are additional premises. It is not
the canonical exact-time, five-mode stopped instrument of
[Instrument Boundaries](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md),
(OC.19)–(OC.19b). The two services generally have different probabilities
and different complete failure outputs.

The original scientific consumer is narrow and concrete: implement a common
phase-preserving height leg on one unknown original specimen, then keep
usable actual memory for subsequent declared cuts. Neither a numerical
overlap nor a compact specimen representation is that acquired memory.

## 2. Exact original source and actual signed histories

All repository suppliers in this volume are read at the immutable revision
`5094da88f161741b61de3b6b16dbc3a115a83d63`.

**Definition 2.1 (source and double-wall restriction).** For a valid original
base $b=(X,Y,Z)$, set $r=1-Z$. The conditions are
$0<Z<1$, $0<X<r$, $0<Y<r$, and the strict height interval is
$J(b)=(\max(0,X+Y-r),\min(X,Y))$. In mode order $(0,1,2,3,13)$ the
probabilities are

$$
p_b(x)=(r-X-Y+x,X-x,Z,Y-x,x).
\tag{PR.1}
$$

The signed direction is $d=(1,-1,0,-1,1)$ and the exact source weight is
$w_i(x)=d_i/(p_b(x)_i I_b(x))$, where
$I_b(x)=p_0^{-1}+p_1^{-1}+p_3^{-1}+p_{13}^{-1}$.
The new theorems restrict to the double wall

$$
X=Y=c=r/2,\qquad 0<x<c,
\qquad
w(x)=\left(\frac12-\frac{x}{r},-\frac{x}{r},0,
                 -\frac{x}{r},\frac12-\frac{x}{r}\right).
\tag{PR.2}
$$

No theorem here enlarges this restriction to every valid base.

An original control has arbitrary finite duration $T\geq0$, continuous real
$k,\chi$ with strict $k(t)\in J(b)$, finite variation of $\chi$, and either
absolute continuity of both coordinates or the supplied finite piecewise
$C^1$ regularity with continuous rates on each closed piece. The latter also
implies absolute continuity by finite telescoping of the integral primitives.
The real transported residual is $H_i(t)=\int_0^t w_i(k(s))\chi'(s)\,ds$.
These are the actual definitions of `FiniteRectangleTransport` and
`OriginalControlComposition`, not a waveform-sensing or actuator premise.

Fix the same positive preparation and calibrated phases $\theta_i$, with
$\theta_2=0$. The orthonormal active directions in $\mathbb C^5$ are

$$
U_+=\frac{e^{-i\theta_0}e_0+e^{-i\theta_4}e_4}{\sqrt2},\qquad
U_-=\frac{e^{-i\theta_1}e_1+e^{-i\theta_3}e_3}{\sqrt2},\qquad e_2.
\tag{PR.3}
$$

Here index $4$ denotes original mode $13$. Write

$$
\begin{aligned}
n_\epsilon(x)&=\sqrt{x/c}\,U_+
             +\epsilon\sqrt{1-x/c}\,U_-,\\
\psi_{x,\beta,m}&=\sqrt Z e_2+e^{-i\beta}\sqrt r\,n_{(-1)^m}(x),\\
t_x&=\langle n_+(x),n_-(x)\rangle=2x/c-1,\\
D_x&=r t_x=4x-r.
\end{aligned}
\tag{PR.4}
$$

Inner products are conjugate linear in the first argument. Throughout,
$\beta\in\mathbb R$ and $m\in\mathbb Z$ ranges over every signed integer.
The endpoint depends on its parity $\epsilon=(-1)^m$; the source history
retains the entire real lift

$$
(\beta,\beta-\pi m,0,\beta-\pi m,\beta).
\tag{PR.5}
$$

**Proposition 2.2 (credited reachability, with the explicit source map).**
For each $k\in(0,c)$ choose one auxiliary $a\in(0,c)$, $a\ne k$,
independently of $\beta,m$. Prepend a unit-time fixed-height phase leg of
increment $2\pi m$ at $k$, then use the supplied four-leg rectangle at $a$
with real phase height

$$
B_{\beta,m}
 =\frac{r(\pi m-\beta)-2\pi m k}{a-k}.
\tag{PR.6}
$$

This is an actual original history from the fixed preparation, of duration
five, ending in (PR.5) and hence (PR.4). Every history has the same height
waveform and support margin
$\min\{k,a,c-k,c-a,Z\}>0$. Its phase variation is
$2\pi|m|+2|B_{\beta,m}|$, finite for every pair. No uniform phase-variation
bound over all $\beta,m$ is asserted.

Proof. The exact `finite_rectangles_realize` supplier gives residual
$B(w(a)-w(k))$, zero rectangle phase increment, strict probabilities and
four unit affine legs. Since

$$
w(a)-w(k)=-\frac{a-k}{r}(1,1,0,1,1),
$$

the total residual $2\pi m w(k)+B(w(a)-w(k))$ is (PR.5), coordinate by
coordinate. The fixed-height leg contributes $2\pi|m|$ to variation and
the rectangle contributes $2|B|$. All pieces are affine and join
continuously, so both original regularity alternatives hold. This is the
all-sector application in the owning Blueprint, reused with its original
signs and negative state-phase convention. $\square$

**Convention 2.3 (the same chronological continuation).** For $k,l\in(0,c)$
and any finite $L>0$, the horizontal leg is
$k(s)=k+(l-k)s/L$ with zero relative phase increment. Its absolute lift is
the actual preceding terminal lift. At a join of duration $T$,
`concatenate_original` gives

$$
k(T+s)=k_{\rm tail}(s),\qquad
\chi(T+s)=\chi(T)+\chi_{\rm tail}(s)-\chi_{\rm tail}(0).
\tag{PR.7}
$$

It preserves the old prefix pointwise and adds each continuous weighted
integral and the real phase increment. The target at the new cut is exactly
$\psi_{l,\beta,m}$. The controller specifies the same relative command for
every unknown history; it never receives $\chi(T)$, $\beta$ or $m$.
Zero duration allows the matching identity $l=k$, not a nontrivial
instantaneous height leg. All future signed sectors remain in the original
menu; the theorems select phase-preserving legs as their particular consumer.

## 3. Joint helper, success return and complete failure

**Definition 3.1 (all accessible history assistance).** For each actual
history supply the joint pure input

$$
\psi_{k,\beta,m}\otimes\eta_\epsilon,
\qquad \epsilon=(-1)^m,
\qquad \|\eta_\pm\|=1,
\qquad \langle\eta_+,\eta_-\rangle=\mu\in[0,1].
\tag{PR.8}
$$

The finite-dimensional calibrated pair $\eta_\pm$ is independent of
$\beta$ and of the winding within each parity. A fixed ket gauge makes its
overlap real and nonnegative. The pair represents **all** accessible
history-bearing assistance jointly: no other accessible correlated archive,
controller port, copy, timing channel, receiver entanglement or bypass is
allowed. Knowing $\mu$ alone does not specify the calibrated pair or the
joint operation. The occupied helper span has dimension at most two.

Other actual fields may remain as spectators, acted on by identity: source,
preparation and epoch identity, archives, clock and reference, calibration,
permissions, controller, selectors and update inputs. Their actual joint
correlations are retained. A spectator is unavailable as assistance to this
gate. If a guard, selector or gate reads an additional history-bearing field,
it must be included in the joint assistance and the premise (PR.8) checked
again. Computing $\mu$ from a marginal while using another correlated port
does not satisfy this contract.

**Definition 3.2 (two success contracts).** One common trace-nonincreasing
CP success map, independent of $\beta,m$, must have exact specimen marginal
$p_\epsilon|\psi_{l,\beta,m}\rangle\langle\psi_{l,\beta,m}|$ on every
promised input. The probability may initially depend on history; rigidity
below forces independence of $\beta$ within each parity. Retain all success
auxiliaries, including their dilation residue, as the updated quantum record.

In contract **C**, the helper may change and its complete success residue
is retained. In contract **R**, the original helper must additionally be
returned in the pure state $\eta_\epsilon$ on success; every extra residue
is also retained. This is return **on success only**. Neither contract
requires the original helper unchanged on failure. Requiring unchanged
return on every branch is a different problem, not solved by the R optimum.

**Definition 3.3 (legal, rejected and stopped branches).** A service request
specifies the source/epoch, current calibrated height, target, helper pair,
programme and permissions. A known mismatch or missing permission produces
an unexecuted rejection with its visible label, no specimen successor and
no claimed successful answer. The promised input relation is a theorem
hypothesis; this definition supplies no detector for unflagged promise
violations. A mathematical whole-domain CP extension still exists below.

A legal executed operation keeps either its actual success output or an
executed-failure flag, a stopped specimen $f$ and the complete quantum failure
residue. Failure allows only the declared absorbing/stopped continuation,
with record updates retained. There is no reset, replay, fresh specimen,
post-failure original retry or coherent access to a hidden canonical Kraus
index. The new instrument explicitly supplies and charges its own output
resource registers; these are not hidden ports of the canonical instrument.

## 4. Phase rigidity and one shared Gram feasibility argument

Put $u=t_k$, $v=t_l$, so $|u|,|v|<1$, and let
$G(z)=\left(\begin{smallmatrix}1&z\\\bar z&1\end{smallmatrix}\right)$.
Use input generators

$$
A_\epsilon=e_2\otimes\eta_\epsilon,\qquad
B_\epsilon=n_\epsilon(k)\otimes\eta_\epsilon.
\tag{PR.9}
$$

In order $(A_+,A_-,B_+,B_-)$ their Gram matrix is
$G(\mu)\oplus G(\mu u)$. The actual input is
$\sqrt Z A_\epsilon+z\sqrt r B_\epsilon$, $z=e^{-i\beta}$.

**Lemma 4.1 (full-phase rigidity with retained records).** For either
contract, the successful dilation on each actual input factors as the exact
target specimen times one auxiliary vector independent of $\beta$. In C
write it as $\psi_{l,\beta,m}\otimes a_\epsilon$; in R write it as
$\psi_{l,\beta,m}\otimes\eta_\epsilon\otimes a_\epsilon$.
Thus $p_\epsilon=\|a_\epsilon\|^2$ is phase independent. The same fact
holds for every successful Kraus component and for zero success amplitude.

Proof. Purity of the required specimen output forces every successful Kraus
image into its one-dimensional specimen ray tensored with the auxiliary
space. Project onto any auxiliary basis vector, obtaining a linear map
$K$ whose image of the actual input is collinear with
$\sqrt Z e_2+z\sqrt r n_\epsilon(l)$. In R first regard the specimen and
returned helper together as the required pure output. Its two corresponding
directions are $e_2\otimes\eta_\epsilon$ and
$n_\epsilon(l)\otimes\eta_\epsilon$.

The wedge of the input image with this target is a vector-valued polynomial
of degree at most two in $z$. It vanishes for every $|z|=1$, so its constant,
linear and quadratic coefficients vanish. The constant term makes
$KA_\epsilon$ a scalar times the output reference direction. The quadratic
term makes $KB_\epsilon$ a scalar times the output bottom direction.
The linear term makes these scalars equal, because $Z,r>0$ and the two
directions are independent. Collect all auxiliary components and successful
Kraus labels into $a_\epsilon$. This proves the factorization and probability
claim without a phase estimate or covariance assumption. $\square$

Projection onto auxiliary components is essential here: an output vector
with a retained auxiliary need not itself be collinear with a specimen ket.
The proof applies collinearity only after that projection.

**Theorem 4.2 (one-cut feasibility and complete attainment).** Fix the
source, helper and $k,l$ above. A common success probability $p\in[0,1]$
is attainable in C if and only if some $x\in\mathbb C$ satisfies

$$
|x|\leq p,\qquad |\mu-x|\leq1-p,\qquad
|\mu u-vx|\leq1-p.
\tag{PR.10}
$$

It is attainable in R if and only if some $x\in\mathbb C$ satisfies

$$
|x|\leq p,\qquad |\mu-\mu x|\leq1-p,\qquad
|\mu u-\mu vx|\leq1-p.
\tag{PR.11}
$$

In either criterion real $x$ suffices for the existence of a given $p$.
Every feasible point has a finite-dimensional complete success/failure
instrument with all failure mass and its actual residue retained.

Proof. By Lemma 4.1 put $x=\langle a_+,a_-\rangle$ and
$\|a_\pm\|^2=p$. Their Gram matrix is positive if and only if $|x|\leq p$.
Define $y=x$ in C and $y=\mu x$ in R. The successful images of the
generators have two orthogonal Gram blocks with diagonal $p$ and
off-diagonal $y$ and $vy$. A contraction exists precisely when the two
residual blocks are positive:

$$
H_A=\begin{pmatrix}1-p&\mu-y\\\mu-\bar y&1-p\end{pmatrix},\qquad
H_B=\begin{pmatrix}1-p&\mu u-vy\\\mu u-v\bar y&1-p\end{pmatrix}.
\tag{PR.12}
$$

Their eigenvalues are the diagonal plus or minus the modulus of the
off-diagonal entry. This gives exactly (PR.10) or (PR.11).

For sufficiency realize the success Gram by vectors $a_\pm$ in a space of
dimension at most two. Realize $H_A,H_B$ as Gram matrices of
$F_{A,\pm},F_{B,\pm}$ in two orthogonal failure spaces of dimension at
most two each. Send each generator to its prescribed success image plus
$f$ tensored with the corresponding failure vector, using orthogonal
success/failure sectors. The total output Gram matrix equals the input
Gram matrix. This gives an isometry on their actual span, including
dependent frames: any input linear relation has zero Gram norm and hence
zero assigned output norm.

Equivalently, the prescribed success map $B$ on the frame is a contraction;
extend $B$ by zero on its orthogonal complement. With
$F=(I-B^\dagger B)^{1/2}$, use the whole-domain isometry

$$
\zeta\longmapsto
 (B\zeta)_{\mathsf s}\ \oplus\ (f\otimes F\zeta)_{\mathsf f}.
\tag{PR.13}
$$

Reading the binary flag gives CP operations whose effects sum to identity.
On the promised span the actual failure vector can be written
$\sqrt Z F_{A,\epsilon}+z\sqrt r F_{B,\epsilon}$; its squared norm is
$1-p$. It can retain phase/history information. It is kept with $f$, not
discarded or replaced by a blank failure bit. The complementary construction
need not return $\eta_\epsilon$ unchanged on failure, including in R.

Since $\mu,u,v$ are real, replacing any feasible $x$ by $\operatorname{Re}x$
decreases each displayed modulus and preserves feasibility. This replacement
may change the success record; it establishes existence and optimization,
not equality of two specified complex record outputs. $\square$

**Proposition 4.3 (worst-parity symmetrization).** For both C and R, the
maximum common probability equals the maximum of
$\min(p_+,p_-)$ over arbitrary parity-dependent success probabilities.

Proof. Let $Q$ fix $e_2,U_+$ and negate $U_-$. It exchanges the specimen
parities without changing $\beta$. There is a calibrated helper unitary
$R$ swapping $\eta_+,\eta_-$: for $0\leq\mu<1$ it fixes their normalized
sum and negates their normalized difference; at $\mu=1$ use identity on
their occupied line. Input conjugation by $Q\otimes R$ and output
conjugation by $Q$ exchange the two parity success probabilities and
preserve the required targets. In R also swap the returned helper at output.
Randomly choose the original or exchanged operation with a retained fair
coin. Both probabilities become $(p_++p_-)/2$, at least their original
minimum. This mixing uses the additional calibrated operation permission;
it is not an original-control sensor or a free hidden programme. $\square$

## 5. Sharp probabilities and the price of return on success

**Theorem 5.1 (closed one-cut optima).** For every source and calibrated
pure helper pair in Definitions 2.1–3.2, the sharp common and worst-parity
success probabilities are

$$
\begin{aligned}
p_C&=1-E_C,\\
E_C&=\max\left\{0,\frac{\mu|u-v|}{1+|v|},
                     \frac{\mu|u|-|v|}{1-|v|}\right\},\\[2pt]
p_R&=1-E_R,\\
E_R&=\max\left\{0,\frac{\mu|u-v|}{1+|v|},
                     \frac{\mu(|u|-|v|)}{1-\mu|v|}\right\}.
\end{aligned}
\tag{PR.14}
$$

The denominators are positive and both optima are attained by the complete
instruments of Theorem 4.2. In particular $p_R\leq p_C$.

Proof. Put $e=1-p$. For C and $v\ne0$, the real feasibility conditions
are intersection of three closed intervals:

$$
[-1+e,1-e],\qquad [\mu-e,\mu+e],\qquad
\left[\frac{\mu u}{v}-\frac e{|v|},
      \frac{\mu u}{v}+\frac e{|v|}\right].
\tag{PR.15}
$$

Intervals on a line have common intersection exactly when each pair
intersects: the largest left endpoint cannot exceed any right endpoint.
The first two intersect because $\mu\leq1$. The first and third intersect
exactly when
$\mu|u|\leq |v|+(1-|v|)e$. The second and third intersect exactly when
$\mu|u-v|\leq(1+|v|)e$. Thus the least possible $e\geq0$ is $E_C$.
If $v=0$, the last constraint is simply $e\geq\mu|u|$; the first two
intervals still intersect, yielding the same formula.

For R, $\mu=0$ permits $p=1,x=1$. If $\mu>0$ and $v\ne0$, the
intervals are

$$
[-1+e,1-e],\qquad [1-e/\mu,1+e/\mu],\qquad
\left[\frac u v-\frac e{\mu|v|},
      \frac u v+\frac e{\mu|v|}\right].
\tag{PR.16}
$$

The first two intersect because $1\leq1-e+e/\mu$. Pairwise intersection
with the third gives

$$
\mu(|u|-|v|)\leq(1-\mu|v|)e,\qquad
\mu|u-v|\leq(1+|v|)e.
$$

For $v=0$ again the sole extra condition is $e\geq\mu|u|$.
This proves $E_R$. Strict $|u|,|v|<1$ makes every positive lower bound
strictly below one, so the displayed minima are feasible in $[0,1)$.
Theorem 4.2 gives attainment and Proposition 4.3 gives minimax optimality.
Finally every R instrument is a C instrument if return is not demanded,
so $p_R\leq p_C$. $\square$

**Corollary 5.2 (edge cases).** If $k=l$, then $p_C=p_R=1$ for every
$\mu$. If $k\ne l$, then $p_C=p_R=1$ if and only if $\mu=0$.
At $\mu=1$ both formulas reduce to the credited unassisted value

$$
s_*(k,l)=\min\left\{1,\frac{k}{l},\frac{c-k}{c-l}\right\}.
\tag{PR.17}
$$

Proof. Equality of heights gives $u=v$ and zero maximum in (PR.14).
For unequal heights its first nonzero term is positive whenever $\mu>0$.
For $\mu=0$ the orthogonal helper can control the credited parity-specific
unitaries, retaining that helper. At $\mu=1$, the inequalities
$|x|\leq p$ and $|1-x|\leq1-p$ force $x=p$ by equality in the triangle
inequality. The remaining condition is $|u-vp|\leq1-p$, or
$p\leq(1-u)/(1-v)$ and $p\leq(1+u)/(1+v)$, together with $p\leq1$.
These are (PR.17). $\square$

**Example 5.3 (return costs an exact tenth).** Take the actual source

$$
c=\frac14,\quad Z=\frac12,\quad
k=\frac9{40},\quad l=\frac3{16},\quad
\eta_+=(1,0),\quad \eta_-=(1/2,\sqrt3/2).
\tag{PR.18}
$$

Then $\mu=1/2$, $u=4/5$, $v=1/2$, and

$$
p_C=\frac9{10},\quad x_C=\frac35,
\qquad
p_R=\frac45,\quad x_R=\frac45,
\qquad s_*=\frac25.
\tag{PR.19}
$$

For C the residual moduli are $|\mu-x_C|=1/10$ and
$|\mu u-vx_C|=1/10$, with $x_C\leq p_C$. The normalized success
record overlap is $x_C/p_C=2/3$. For R the two residual moduli are
$1/10$ and $1/5$, both at most $1-p_R=1/5$; here $x_R=p_R$, so the
extra normalized success residue is common and the returned helper's
overlap stays $1/2$. Formula (PR.14) supplies the matching upper bounds.
The helper-return condition therefore has a strict price, even though
return on failure is not imposed.

These are actual original endpoints. Set auxiliary $a=1/8$ in (PR.6).
For $(\beta/\pi,m)=(0,0),(1/2,0),(0,1),(1/2,1)$, respectively,

$$
B/\pi=(0,5/2,-1/2,2),\qquad
\operatorname{TV}(\chi)/\pi=(0,5,3,6).
\tag{PR.20}
$$

The five-unit histories and their common unit-time horizontal tails have
support at least $1/40$. The helper pair is an additional joint source
premise; the rectangle construction does not generate it.

## 6. Actual finite obstruction, mixed helpers and the promised-pair boundary

**Theorem 6.1 (four actual histories force orthogonal pure helpers).** For
$k\ne l$, the four source histories with $m=0,1$ and
$\beta=0,\pi/2$ already prohibit deterministic exact specimen conversion
under (PR.8) unless $\mu=0$. The output helper need not be returned for
this necessity result.

Proof. Dilate the deterministic channel, keeping its environment in the
proof. For each parity, the two same-parity input and target specimen
overlaps both equal $Z-ir\ne0$, independent of height. Isometry therefore
forces the two corresponding unit environment vectors to be equal. Write
$\nu$ for the overlap between the resulting plus and minus environment
vectors, including all output records. Cross-parity comparisons at equal
phase and at phase difference $\pi/2$ give

$$
\mu(Z+ru)=\nu(Z+rv),\qquad
\mu(Z-iru)=\nu(Z-irv).
\tag{PR.21}
$$

Add $i$ times the first equation to the second. Since $Z>0$ this gives
$\mu=\nu$ without dividing by any unknown specimen overlap. Substitution
yields $\mu(u-v)=0$, hence $\mu=0$. Proposition 2.2 realizes all four
inputs at the same preparation, duration and height waveform, and
Convention 2.3 supplies their common legal continuation. $\square$

This finite certificate selects $m=0,1$; the uniform theorems still quantify
over all positive, negative and zero windings. It is a certificate within
the actual source, not an independently postulated four-state ensemble.

**Theorem 6.2 (finite mixed parity-only helper criterion).** Let
$\tau_+,\tau_-$ be calibrated density matrices on a finite-dimensional
helper, independent of $\beta$ and of $m$ within parity, and representing
all accessible assistance. For distinct $k,l$, a common CPTP map has the
exact target specimen marginal on
$|\psi_{k,\beta,m}\rangle\langle\psi_{k,\beta,m}|\otimes\tau_\epsilon$
for every $\beta,m$ if and only if

$$
\operatorname{supp}(\tau_+)\perp\operatorname{supp}(\tau_-).
\tag{PR.22}
$$

Under this condition an attaining operation can leave the helper unchanged
and preserve its correlations with an untouched reference on each promised
support. For $k=l$ identity works without (PR.22).

Proof. Spectrally decompose both helper states into positive-weight pure
components. The channel is TP, so every component has a normalized
specimen output. A convex combination of positive normalized matrices can
be rank one only if every component has that same rank-one output: its
expectation on each orthogonal target vector is a sum of nonnegative terms
equal to zero. This holds for every $\beta$. Hence each plus eigenvector
and each minus eigenvector define a pure helper pair to which Theorem 6.1
applies. Their inner product is zero. Their spans are the two supports,
proving necessity.

Conversely, let $P_\pm$ be the orthogonal support projections. The credited
fixed-parity unitary $W_\epsilon$ fixes $e_2$ and sends
$n_\epsilon(k)$ to $n_\epsilon(l)$. Use the controlled unitary
$\sum_\epsilon W_\epsilon\otimes P_\epsilon$ on these supports and
identity on their joint orthogonal complement. It transfers every phase
exactly and acts identically on the helper within its promised support.
Tensor identity on a reference: any joint helper/reference state supported
on that support is preserved, conditional on the actual history. No
measurement, fresh copy or inferred parity label is required. $\square$

Orthogonal supports provide a perfectly readable parity distinction in
this particular assistance class. The theorem makes no necessity claim
for phase-dependent helpers, accessible extra correlated archives or other
source models. Parity still does not identify signed winding, phase or
past chronology.

**Example 6.3 (fixed-phase pair is a different theorem).** Instrument
Boundaries §6.1 credits deterministic conversion for the promised pair
$\beta=0$, $m=0,1$, at
$c=3/10$, $Z=2/5$, $k=1/4$, $l=1/8$, if and only if $\mu\leq3/8$.
That conclusion uses joint input overlap $(4/5)\mu$, target specimen
overlap $3/10$, and an output environment overlap of modulus at most one.
It is a C contract on two states with fixed phase.

For the full unknown-phase family at the same source, $u=2/3$, $v=-1/6$.
At $\mu=3/8$, Theorem 5.1 instead gives

$$
p_C=p_R=\frac{41}{56}<1.
\tag{PR.23}
$$

For C a feasible success Gram entry is $x=3/28$, giving normalized success
record overlap $6/41$. For R a feasible extra-residue entry is $x=2/7$;
it has a different meaning and includes the returned-helper factor $\mu$
in (PR.11). Thus the identical numerical optimum does not equate their
record outputs. The credited pair threshold is neither contradicted nor
promoted to a full-family observer threshold.

## 7. Exact finite checkpoint recurrence with complete survivor memory

**Definition 7.1 (retained-token checkpoint contract).** Fix a finite public
height programme $k_0,\ldots,k_L\in(0,c)$, with actual horizontal original
legs between consecutive cuts. Start with (PR.8) at $k_0$. Each successful
cut must have exact specimen $\psi_{k_j,\beta,m}$; every auxiliary success
output is retained as the next token and is available coherently under the
additional service permission. This is C continued in time. It need not
return the initial helper unchanged and is not a multi-step R theorem.

The complete coherent survivor vector at cut $j$ has the form

$$
\psi_{k_j,\beta,m}\otimes a_{j,\epsilon},\qquad
\|a_{j,+}\|^2=\|a_{j,-}\|^2=q_j,\qquad
h_j=\langle a_{j,+},a_{j,-}\rangle.
\tag{PR.24}
$$

Here $q_j$ is the unconditional probability of reaching that cut with all
previous successes, not its conditional step probability. Initially
$q_0=1$, $a_{0,\epsilon}=\eta_\epsilon$ and $h_0=\mu$.
The token is the actual vector, not the number $h_j$. Every executed failure
retains its first failed cut, actual quantum residue and absorbing $f$.
Other actual spectator fields remain jointly present and untouched.

**Theorem 7.2 (complex feasibility, real optimization and complete update).**
In Definition 7.1, prescribed numbers $q_j\in\mathbb R$, $h_j\in\mathbb C$
are realizable by complete instruments if and only if, for $1\leq j\leq L$,

$$
\begin{aligned}
0&\leq q_j\leq q_{j-1},& |h_j|&\leq q_j,\\
|h_{j-1}-h_j|&\leq q_{j-1}-q_j,&
|D_{k_{j-1}}h_{j-1}-D_{k_j}h_j|
 &\leq r(q_{j-1}-q_j).
\end{aligned}
\tag{PR.25}
$$

Replacing all $h_j$ by their real parts preserves feasibility and the same
survival schedule $(q_j)$. Consequently real overlaps suffice for maximizing
$q_L$; expanding the absolute values makes that finite optimization a linear
programme. Replacement need not preserve prescribed complex overlaps or
the corresponding joint record states.

Proof. Lemma 4.1 applies to the cumulative successful contraction at every
cut, giving (PR.24). At step $j$ use generators
$e_2\otimes a_{j-1,\epsilon}$ and
$n_\epsilon(k_{j-1})\otimes a_{j-1,\epsilon}$. The two input Gram blocks
have diagonal $q_{j-1}$ and off-diagonal $h_{j-1}$ and
$t_{k_{j-1}}h_{j-1}$. Their successful output blocks have diagonal $q_j$
and off-diagonal $h_j$ and $t_{k_j}h_j$. Their positive differences give
exactly the last two constraints in (PR.25); positivity of the output
token Gram gives $|h_j|\leq q_j$. Trace decrease gives monotonicity.

Conversely, realize each pair $a_{j,\pm}$ by its positive two-by-two Gram
matrix. The same frame argument as Theorem 4.2 gives a well-defined
contraction between the actual consecutive frame spans, even for a singular
Gram matrix. Complete it with the complementary square root and keep the
failure output as in (PR.13). If $q_{j-1}>0$, the conditional step success
probability on either normalized actual survivor is $q_j/q_{j-1}$.
If $q_{j-1}=0$, all later $q,h$ vanish and there is no live branch to
continue; $h_0=\mu$ causes no division problem at a zero later cut.

Compose the complete instruments, stopping at first failure. Let $B_j,F_j$
be the success and failure contractions on the appropriate full cut spaces,
with $B_j^\dagger B_j+F_j^\dagger F_j=I$. The all-success product is
$B_L\cdots B_1$, and the first-failure products are
$F_jB_{j-1}\cdots B_1$. Their effects telescope to identity on the initial
space. Keep the cut label and all quantum output registers in each product.
This proves completeness, actual record succession and absorbing failure,
not only a product of scalar probabilities.

For real initial $h_0$, replacing every $h_j$ by $\operatorname{Re}h_j$
reduces each modulus in (PR.25), because $D_{k_j},r$ are real.
The new feasible sequence is realized by the construction just given.
The $q_j$ are in $[0,1]$ and $|h_j|\leq q_j$, so the finite real feasible
set is compact and nonempty (it contains immediate failure). A maximum
exists. $\square$

For example, take $\mu=0$, $k_0=k_1=c/2$, $q_1=1/2$ and $h_1=i/4$.
These prescribed complex data satisfy (PR.25): the top overlap difference
has modulus $1/4\leq1/2$, and both $D$ values are zero. Replacing $h_1$
by zero preserves the survival schedule but changes nonorthogonal survivor
records into orthogonal ones. No common record isometry can identify those
two Gram matrices. Thus “real overlaps suffice” is an optimization reduction,
not an assertion that a specified complex joint output is preserved.

The theorem is an exact iff for the complete coherent token contract stated.
For an arbitrary instrument that retains mixed records or classical coins,
its dilation can be used for an upper bound: keep every generated
purification in a larger proof system. Every later actual operation extends
by identity on unavailable purifying registers, so the same Gram necessity
still holds. Granting access to these registers only enlarges the class for
an upper bound. It does not grant such access to the actual observer.
The attaining construction above explicitly supplies its own pure residue
and therefore needs no unsupplied purification port. Mixed spectator
archives are never replaced by an accessible purification.

If later choice uses extra classical suboutcomes, their labels and
purifications belong to that enlarged survivor record in the upper-bound
argument. The positive construction generates no such internal suboutcomes:
its live branch has the single recorded success at each public cut and its
actual coherently retained token. Thus a two-vector Gram realization does
not erase an old classical archive or silently turn classical-only access
into coherent access.

**Proposition 7.3 (symmetry at every finite cut).** For a fixed finite height
programme, optimization of the worst final parity survival over arbitrary
finite protocols reduces to equal survivor probabilities at every cut.

Proof. Use the specimen/helper exchanges of Proposition 4.3 on the initial
input, and undo the specimen exchange at each required reported checkpoint.
Before the next internal step undo that output exchange again, so the
conjugated protocol is the original protocol on the exchanged input. It is
a common allowed protocol and exchanges the two parity survivor
probabilities at every cut. Mix it with the original using a retained fair
coin. At cut $j$ both probabilities are the original average; its final
value is at least the original worst value. The exact target at every live
cut is preserved in both coin branches. Purifying the independent coin in
the upper-bound proof leaves initial overlap $\mu$ unchanged. Conditional
on success the complete residue includes the coin and any records; it may
be represented by vectors whose cross overlap is the real part of the
original cross overlap. Theorem 7.2 therefore bounds the symmetrized
protocol. Its attainable equal-probability construction proves the reverse
optimization inclusion. No unknown parity is a controller input. $\square$

## 8. A sharp repeated excursion on the actual rational source

**Theorem 8.1 (finite repeated-excursion optimum).** Take

$$
c=\frac3{10},\quad Z=\frac25,\quad r=\frac35,\qquad
k_H=\frac14,\quad k_L=\frac18.
\tag{PR.26}
$$

For each integer $n\geq0$, perform $n$ prescribed horizontal excursions
$k_H\to k_L\to k_H$, requiring the exact target after every one of the
$2n$ legs, on every initial $\beta\in\mathbb R$ and signed $m\in\mathbb Z$.
Under the complete retained-token contract with initial overlap $\mu$,
the sharp common and worst-parity probability of all checkpoints succeeding
is

$$
P_n^*(\mu)=1-\mu+\mu\,7^{-n}.
\tag{PR.27}
$$

The optimum has complete retained quantum memory at every success and
absorbing retained failure. It is a finite-cut assisted instrument result,
not equality with the canonical exact-time/mode instrument.

Proof. Here $D_H=2/5$, $D_L=-1/10$. Proposition 7.3 permits equal
survivor probabilities $q_j$. Set $A=1-\mu$. The first overlap-difference
constraint in (PR.25), telescoped from $h_0=\mu$, gives

$$
\operatorname{Re}h_j\geq\mu-(1-q_j)=q_j-A.
\tag{PR.28}
$$

If $q_{2n}\leq A$, the claimed upper bound is immediate. Otherwise let
$e_j=q_j-A>0$ for every cut. Consecutive $D$ values have opposite signs.
The modulus of their difference is at least the appropriately signed real
part, and (PR.28) therefore implies

$$
r(e_{j-1}-e_j)
 \geq |D_{k_{j-1}}|e_{j-1}+|D_{k_j}|e_j.
\tag{PR.29}
$$

Consequently

$$
e_j\leq
 \frac{r-|D_{k_{j-1}}|}{r+|D_{k_j}|}\,e_{j-1}.
\tag{PR.30}
$$

The outbound factor is $2/7$ and the return factor is $1/2$. Since
$e_0=\mu$, their product yields
$q_{2n}\leq A+\mu7^{-n}$, including complex survivor overlaps through
their real parts. For $n=0$ the bound is the identity value one.

For attainment define

$$
S_{2a}=7^{-a},\qquad S_{2a+1}=\frac27\,7^{-a},\qquad
q_j=A+\mu S_j,\qquad h_j=\mu S_j.
\tag{PR.31}
$$

Then $0\leq h_j\leq q_j$, and
$q_{j-1}-q_j=h_{j-1}-h_j$. Also the choice of the two factors gives

$$
r(q_{j-1}-q_j)
 =|D_{k_{j-1}}|h_{j-1}+|D_{k_j}|h_j.
\tag{PR.32}
$$

All constraints in (PR.25) hold. Theorem 7.2 constructs the complete
sequence of actual contractions and their retained failure residues.
At a nonzero survivor cut the normalized token overlap is $h_j/q_j$;
the token itself remains a quantum system. The controller advances using
the actually obtained success flag, retained token and public cut index.
It uses no classical $\beta$, winding or parity input. $\square$

**Proposition 8.2 (actual paths and their resources).** Each instance of
Theorem 8.1 uses actual original controls with both original regularity
alternatives. To prepare any quantified initial history at $k_H$, choose
$a=k_L$ in Proposition 2.2. Then

$$
B_{\beta,m}=\frac{24}{5}\beta-\frac45\pi m.
\tag{PR.33}
$$

Append $2n$ unit-time affine horizontal legs with constant relative phase.
Their common support is at least $1/20$, future duration is $2n$, future
phase variation and winding are zero, future height speed is $1/8$ on
each nontrivial leg, and future height variation is $n/4$. The complete
history has duration $5+2n$ and retains its original real winding $m$.

Proof. Formula (PR.33) is (PR.6) at the rational parameters. Every height
lies in $[1/8,1/4]$; the smallest of $x,c-x,Z$ is $1/20$. Each future
leg has height change $1/8$ over one unit and no phase derivative, so its
transported phase increment is zero. Composition (PR.7) preserves the old
prefix and actual signed lift and adds these zero increments. Finite
affine joins satisfy both regularity alternatives. $\square$

Thus $P_n^*(1)=7^{-n}$ reuses the credited unassisted checkpoint product,
and $P_n^*(0)=1$ reuses fixed-parity controlled action. For $\mu=1/2$
and $n=1$ the optimum is $4/7$, with one supplied token on one specimen.
The mathematical limit as $n\to\infty$ is $1-\mu$. This is a limit of
finite optima, not an executed infinite experiment or a finite-state
implementation of indefinite exact dynamics. A fixed duration or total
variation budget does not contain this entire sequence of programmes.

The frontier resembles a mixture of perfectly distinguishing parity
information of weight $1-\mu$ and an unassisted component of weight $\mu$.
The exact proof and attaining operations are the Gram construction above.
Interpreting this resemblance as an actual token-only unambiguous read
would require that read and its inconclusive live successor to be explicitly
permitted. No such read, restart or new canonical failure successor is
needed or granted by the proof.

## 9. Joint boundary, legal continuation and counted resources

**Definition 9.1 (existing menu and the additional menu).** The credited
canonical menu at a live double-wall endpoint comprises every permitted
prescribed `OriginalControl` at the same base and matching current height,
arbitrary finite duration including zero, either regularity alternative,
real relative increments and every signed sector allowed by an explicit
resource promise. Finite policies may use actually acquired records and
matched controller/external inputs. Canonical failure retains exact first
time and one of the five original mode labels, with absorbing $f$ and
only its supplied stopped continuation. No mode labels or exact timestamps
are merged here.

The added menu is the calibrated endpoint/checkpoint instrument of
Definitions 3.1–3.3 and 7.1. Its success/failure events and cut labels
belong to its own complete output. It supplies no canonical first-failure
time or original-mode readout. Its sharper assisted probabilities cannot
be substituted into (OC.19b) while claiming equality of complete laws.
After an assisted success a separately permitted canonical tail may act
on the exact target specimen with all auxiliary records retained. That
conditional continuation is not a proof of all-prefix implementation
between the assisted checkpoints.

The complete observer boundary still includes the actual joint source and
epoch, preparation, clock/units, reference and calibration, full archive,
permissions, programme/pending-controller state, selectors, meters and
external update inputs. Matching separate marginals is insufficient. If a
selector uses a further history field, that field is an additional input,
not something proved available by $h_j$ or $q_j$.

**Proposition 9.2 (precise spectator scope).** On a promised history the
specimen and helper are pure, so any further joint reference has product
form with these two pure marginals, conditional on that history. The common
constructed instrument tensored with identity therefore preserves any
actual mixture of such history-correlated spectator states, along with
their correlations with success/failure and residue.

Proof. A positive matrix with a rank-one marginal has support in that
one-dimensional marginal tensor the other space: expectations on the
orthogonal marginal complement vanish, and positivity removes its cross
blocks. Apply this successively to the pure specimen and pure helper.
Then use linearity of each CP branch and identity on the spectator.
This proves the claimed history-conditioned and mixed-history statement.
It does not identify independently chosen spectator marginals or claim
equality with a canonical instrument on arbitrary entangled inputs.
$\square$

**Resource account 9.3.** The live specimen has the credited active qutrit
support inside the five original modes, plus an absorbing classical sector
when stopped. The pure helper pair occupies at most two joint dimensions
and is an additional resource. A one-step C success residue needs at most
two dimensions; an R construction can use the returned two-dimensional
helper and an extra residue of at most two dimensions. On the promised
frame span failure needs at most four dimensions. On the full
qutrit-times-helper input of dimension at most six, the complementary
square-root completion can keep a failure residue of dimension at most
six. These are sufficient mathematical register counts, not minima for
hardware, implementation environments or total observer memory.

In the coherent checkpoint construction, the two actual success vectors
span at most two dimensions at each cut. This does not remove independently
retained spectator archives or imply they have dimension two. The binary
flag and first-failure-or-all-success field are retained. For $L$ cuts the
latter has $L+1$ possibilities; all success flags before that first failure
are then determined by the fixed programme. Other event payloads, programme
descriptions and actual archives are separately charged. A protocol with
additional outcome labels must retain and count those labels as well.

Exact coefficients require calibrated descriptions of $Z,k,l$, preparation
phases, the helper rays, reference basis and the instruments. Rational base,
heights, durations and a rational/algebraic calibrated helper pair give
finite algebraic descriptions for the finite Gram constructions, including
matrix square roots. The example in (PR.18) has such a description. This
does not give exact physical execution at finite accuracy. Arbitrary real
calibration parameters need not have finite effective descriptions.
Storage widths, arithmetic, programme length, acquisition work, specimen
and helper preparation, gate precision, clocks, timing and physical energy
are distinct resources. None is priced solely by $p_C$, $p_R$ or $P_n^*$.

All new theorems are exact. There is no approximate observation metric,
finite-noise certification or accumulation bound claimed for these new
operations. The stability supplier's TV and strong-derivative conditions
remain conditions for its canonical output, not supplied error data for
these assisted gates.

## 10. Suppliers, primary literature and mathematical boundaries

**Source map 10.1.** The following references specify the reused source,
operation and joint-interface premises. The source links select the immutable
base used throughout this volume.

| Supplier | Exact contribution and boundary |
| --- | --- |
| [FiniteRectangleTransport Lean](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean) and [owning Scribe](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/Blueprint/D5/S3/Quantum/Fibers/FiniteRectangleTransport.scribe.cs) | `ValidBase`, `probability`, signed `phaseWeight`, `weight_compatible` and `finite_rectangles_realize`; the Scribe's real all-sector application supplies (PR.6). The rectangle Lean declaration alone is not attributed the whole ordinary all-sector classification. No helper, source sensor or joint quantum actuator follows. |
| [OriginalControlComposition Lean](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/D5/S3/Quantum/Fibers/OriginalControlComposition.lean) and [owning Scribe](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/Blueprint/D5/S3/Quantum/Fibers/OriginalControlComposition.scribe.cs) | Both original regularity alternatives, finite/zero durations, matching endpoints, literal unchanged prefixes, shifted real tails and additive continuous weighted integrals. These identify the actual continuation; they do not acquire unknown past parameters. |
| [Instrument Boundaries](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md), §§4–6 and 9–15 | Full original endpoint family, unassisted Kraus rigidity and blind success records, fixed-parity rotations, unassisted checkpoint products, canonical stopped instrument, pair threshold, terminal classification and law-level recovery are credited. The assisted joint input and output here are different contracts. |
| [Instrument Stability](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md), §§2–5 | Survival-floor inverse bounds, bounded-speed forward discontinuity, low-survival inverse nonuniformity and sufficient complete-output error data are retained. Exact assisted state recovery supplies none of those acquisition certificates. |
| [Quantum Carrier Minimum](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md), §§2–6 | Exact complete five-labelled $M_3$ correspondence retains supplied correlated archives. Its sharp live block lower bound denies accessible pre-supplied assistance; our helper is excluded by that lower-bound contract. No assisted live-dimension minimum is claimed. |
| [Record Acquisition](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_RECORD_ACQUISITION.md), §§2–9 and 11 | Point-query obstructions, matched bounded-speed order, conditional calibrated area/winding certificate, timing/arithmetic costs and later-loop errors. A correctly acquired winding/parity record could feed controlled action only with that certificate's actual sensor, calibration and joint-source promises. No such record is constructed here. |
| [Transport–Memory Completion](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §§2.9–2.12 and 2.18 | Same coherent source, actual common port, aligned times/records, known nonzero amplitudes and record overlap, and actually acquired readings. The helper overlap here is a new calibrated premise, not an unknown interference factor divided out. Orthogonal parity control and nonzero-overlap interference are distinct consumers. |
| [Process Geometry](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §34; [Atlas Stable Core](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md), §§1–3 | One actual joint image, actual domains/routes, distinct rejection and executed failure, archives, reference, permission and complete selection/update fields. A conditional token recurrence does not instantiate the full observer boundary. |

**Literature statement 10.2.** The following accessible primary texts support
the mature mechanisms or delimit a tempting transfer. The exact source
formulas, return constraint and excursion deductions are `repo-derived`
ordinary consequences proved here. No worldwide priority is asserted.

| Primary source | Precise statement and use |
| --- | --- |
| Chefles, Jozsa and Winter, [On the existence of physical transformations between sets of quantum states, quant-ph/0307227v1](https://arxiv.org/html/quant-ph/0307227v1), Theorems 2–3, Eqs. (7)–(9) | `literature-attested`: pure-family transformations have positive environment Gram factors; probabilistic outcomes have positive Gram contributions, with a positive remainder for omitted failure. This is the mature mechanism in Theorem 4.2. Our actual continuous-phase reduction, two blocks and sharp scalar optimization are proved explicitly rather than attributed to a generic finite-family theorem. |
| Nielsen and Chuang, [Programmable quantum gate arrays, quant-ph/9703032v1](https://arxiv.org/html/quant-ph/9703032v1), stated Result and Eqs. (6)–(10) | `literature-attested`: distinct exact deterministic unitary programmes on arbitrary data require orthogonal programme states. Our correlated phase/parity subfamilies are not arbitrary data for two unitary programmes. Theorem 6.1 supplies four actual source inputs and does not import that missing premise. |
| Chefles and Barnett, [Quantum State Separation, Unambiguous Discrimination and Exact Cloning, quant-ph/9808018v1](https://arxiv.org/html/quant-ph/9808018v1), separation bound and Eq. (18) | `literature-attested`: optimal unambiguous discrimination of a known equiprobable pure pair has conclusive probability $1-|\langle\eta_+,\eta_-\rangle|$. This credits the familiar distinguishability interpretation of $1-\mu$. It does not create the source-owned helper or prove our repeated original-control upper bound. |

Stinespring dilation, positivity of Gram matrices, two-by-two matrix
positivity, interval intersection, spectral decomposition and controlled
unitaries are mature mathematics. They are not claimed as new principles.
The source-specific delta is (PR.10)–(PR.14), the actual full-phase/pair
distinction, the complete finite memory criterion (PR.25), and the sharp
realized excursion frontier (PR.27), with their stated assistance contracts.
Bounded searches of the immutable original-control and fiber suppliers do
not establish an exhaustive absence or a worldwide novelty claim.

The bibliographic leads DOI `10.1063/1.4961516`,
`10.1090/S0025-5718-01-01307-2` and `10.5402/2011/164564` have no verified
primary text in this source's evidence boundary. No theorem premise is
imported from them. The proofs above do not depend on those leads.

**Finite arithmetic 10.3.** Exact rational vertex enumeration agrees with
(PR.14) on 6498 contract/parameter cases:
$\mu=i/8$, $0\leq i\leq8$, and $u,v=j/10$,
$-9\leq j\leq9$, for both C and R. The enumeration minimizes $e=1-p$
over intersections of pairs of boundary lines of (PR.10) or (PR.11),
including $0\leq e\leq1$. It checks both optima and $p_R\leq p_C$.
Exact substitution checks (PR.31)–(PR.32) for 297 finite schedules:
$\mu=i/32$, $0\leq i\leq32$, and $0\leq n\leq8$.
The rational witnesses (PR.19)–(PR.20) are also checked by substitution.
These finite calculations check the displayed arithmetic; the universal
claims rest on the ordinary proofs. No experimental programme or dataset
is part of this volume.

## 11. Application and the remaining acquired-observer bridge

The new relation priced here is an actual calibrated source-bound record
whose two parity states jointly describe every accessible history-bearing
input to a common continuation gate. Within that restricted class,
deterministic nontrivial full-phase height continuation needs orthogonal
records, while partial distinguishability has the sharp success prices
(PR.14). Returning the helper on success can lower attainable probability.
When the helper may update, (PR.25) supplies a complete finite operational
successor rather than a scalar record summary, and (PR.27) prices its
continued use on a genuine original excursion.

The initial source-bound helper remains conditional. No operation here
acquires it from the original unknown specimen, certifies its phase
independence or purity, estimates its overlap, establishes its source/epoch
provenance, calibrates its reference or implements the coherent joint gates.
The supplied original reachability controls construct the specimen histories;
they do not supply a hidden helper-generation port. The existing endpoint
no-imprinting result is credited and does not become a new acquisition
procedure in this volume.

The success-return theorem leaves failure return unrestricted. The checkpoint
theorem allows token change and does not solve repeated immutable-helper
transport. Complete canonical exact-time/five-mode equality, arbitrary
entangled-reference equality with that canonical instrument, arbitrary
phase-dependent/mixed assisted probabilistic optima, general feedback-policy
optimization, all-prefix actuation between cuts and finite-precision
certification remain separate problems. No ideal all-operator canonical
channel has been equated with the new conditional conversion service.

Finally the full archive, common-port acquisition, permissions, controllers
and selector/update inputs must still be obtained and closed in one actual
joint source. A sharp conditional token frontier is partial progress on that
consumer, not a complete acquired internal observer. Both directions of
space/time/boundary/memory recovery, native stationary $\alpha/\beta$
memory-rate/cofinality and the separate fixed-Hamiltonian quantum minimax
task remain active. Neither the exact span identity of
`TwoClockKrylovClosure` nor the AURIC C114 or twisted-ground models supplies
a sensor or a cross-model source/action/resource bridge here.

## 追加锚（本行以下为增补区）
