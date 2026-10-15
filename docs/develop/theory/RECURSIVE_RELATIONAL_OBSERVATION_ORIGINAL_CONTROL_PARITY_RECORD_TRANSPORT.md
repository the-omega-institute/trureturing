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
Lean/kernel verification or physical realization claim. The geometric source
and its exact chronological composition are credited suppliers. The mature
Gram/isometry criterion is also credited; the deductions here concern its
particular original-source inputs and retained-record constraints.

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

## 12. Equal-support mixed assistance and the exact survivor update

The source throughout §§12–15 is Definition 2.1 and (PR.3)–(PR.7), with
one common preparation and calibrated reference. In particular
$0<Z<1$, $c=(1-Z)/2$, $V=\operatorname{span}\{U_+,U_-,e_2\}$, and

$$
\psi_{x,\beta,m}=\sqrt Z e_2+e^{-i\beta}
 \bigl(\sqrt{2x}U_++(-1)^m\sqrt{2(c-x)}U_-\bigr),
\quad 0<x<c,\quad \beta\in\mathbb R,\quad m\in\mathbb Z.
\tag{PR.34}
$$

Every quantified state has the actual five-unit history of Proposition 2.2,
with real residual (PR.5), including every negative winding. Horizontal
continuation means Convention 2.3, on the same specimen and real chronology.
These sections select that consumer within the original menu; they do not
restrict the whole original task without loss. The source regularity still
allows either original alternative and arbitrary finite durations, including
zero for a matching identity. No common bound on past phase variation is added.

**Definition 12.1 (mixed assistance and available ports).** At a cut of
height $k$, supply calibrated finite-dimensional density operators
$\tau_+,\tau_-$ and the accessible joint input

$$
|\psi_{k,\beta,m}\rangle\langle\psi_{k,\beta,m}|
 \otimes\tau_\epsilon,\qquad \epsilon=(-1)^m.
\tag{PR.35}
$$

The helper states are independent of $\beta$ and of the winding within
parity. They include **all accessible history-bearing assistance jointly**:
quantum memory, classical archives and source-bearing programmes, receiver
shares, clock latches, calibration tokens and every input read by a guard,
selector or update. Independent ancillary inputs can be absorbed into the
common operation. An additional accessible purification, noise flag,
programme field or source callback changes this premise.

Actual unread reference/archive fields are retained, with the operation
acting by identity on them. They may be correlated with the mixed helper;
they are unavailable to the continuation protocol. Giving them access later
requires a new joint-input analysis. No equality of independently selected
marginals is used. Conditional on a history, purity of the specimen alone
makes its joint state with all these other fields a product with its pure
specimen projector; the helper and unread fields need not be a product.

The allowed implementation is the additional endpoint/checkpoint CP service
of Definitions 3.2–3.3, with all its declared input/output registers and
permission. Each accepted specimen must be exactly (PR.34) at its requested
height. Retain actual success auxiliaries and all recorded suboutcomes.
Executed failure has absorbing $f$, its flag and full actual residue.
A known source/epoch/height/calibration/permission mismatch instead gives
the unexecuted visible rejection of Definition 3.3, with no specimen
successor or successful answer. There is no detector here for an unflagged
promise violation, no reset or post-failure original retry. This service
supplies neither canonical failure times/modes nor physical gates or sensors.

**Theorem 12.2 (equal-support factorization and sharp one-cut value).**
Fix $k,l\in(0,c)$ and (PR.35). Suppose
$\operatorname{supp}\tau_+=\operatorname{supp}\tau_-=S$. Define the
positive invertible operator on $V$

$$
D U_+=\sqrt{l/k}\,U_+,\qquad
D U_-=\sqrt{(c-l)/(c-k)}\,U_-,\qquad De_2=e_2,
\qquad s=\|D\|^{-2}=s_*(k,l).
\tag{PR.36}
$$

For every common trace-nonincreasing CP success operation satisfying the
exact target requirement for every $\beta,m$, its successful Stinespring
contraction, with all actual auxiliaries and a proof environment included
in $E$, restricts to

$$
B|_{V\otimes S}=D\otimes A,
\qquad A:S\longrightarrow E,\qquad A^\dagger A\leq sI_S.
\tag{PR.37}
$$

Consequently its success probability is phase independent and obeys

$$
p_\epsilon=\operatorname{tr}(A^\dagger A\tau_\epsilon)\leq s.
\tag{PR.38}
$$

No common-probability hypothesis is required; zero success is allowed.
The bound is attained simultaneously for both parities, leaving the helper
and its unread correlations unchanged on success. All these statements are
for exact targets.

Proof. Spectrally decompose $\tau_\epsilon$ on $S$. Every eigenvalue
there is positive. For fixed $\beta,\epsilon$, project each successful
dilation vector onto the orthogonal complement of the required specimen
ray. The squared norms, weighted by those positive eigenvalues, sum to
zero, because the required specimen marginal is rank one or zero.
Each projected vector therefore vanishes. By linearity, for **every**
$u\in S$, $B(\psi_{k,\beta,m}\otimes u)$ lies in
$\mathbb C\psi_{l,\beta,m}\otimes E$. The same $u$ is available for
both parities, since both states are faithful on the same $S$.

Fix $u$ and a bra on $E$. Projecting $B(\,\cdot\,\otimes u)$ onto that
bra gives a linear specimen map which sends both full phase families into
the corresponding target rays. After harmless scalar normalization it is
a contraction. Instrument Boundaries Theorem 4.1, the credited
successful-Kraus rigidity on the active span, says it is a scalar multiple
of $D$. Applying this to a basis of $E$ shows that
$B(v\otimes u)=Dv\otimes A(u)$ for every $v\in V$. The coefficients
are linear in $u$, so $A$ is linear. This reuses the full-family rigidity;
a single fixed-phase pair would not justify the conclusion.

Contractivity on $V\otimes S$ yields
$D^\dagger D\otimes A^\dagger A\leq I$. Evaluating on a unit
eigenvector for the largest eigenvalue of $D^\dagger D$ gives
$A^\dagger A\leq\|D\|^{-2}I$. Also
$D\psi_{k,\beta,m}=\psi_{l,\beta,m}$ is normalized, proving (PR.38).
Spectral vectors and the proof environment are proof devices, not supplied
purification ports.

For attainment use $B=\sqrt{s}D\otimes I_S$ on $V\otimes S$, extended
by zero on its orthogonal complement. With
$F=(I-B^\dagger B)^{1/2}$ the whole-domain isometry is

$$
\zeta\longmapsto(B\zeta)_{\mathsf s}
       \oplus(f\otimes F\zeta)_{\mathsf f}.
\tag{PR.39}
$$

Its two effects sum to identity. Keep the failure flag, residue and $f$;
keep the actual helper on success. Tensoring with identity on unread fields
gives their actual joint output, including correlations with the failure
residue. This is an endpoint completion, not (OC.19b). $\square$

**Corollary 12.3 (finite recorded CP update and its support invariant).**
Under Theorem 12.2, let $r$ range over a finite set of successful recorded
suboutcomes. There are common CP maps $\mathcal T_r$ on the helper such
that the actual accessible output on record $r$ is

$$
|\psi_{l,\beta,m}\rangle\langle\psi_{l,\beta,m}|
 \otimes\mathcal T_r(\tau_\epsilon),\qquad
\sum_r\mathcal T_r^\dagger(I)\leq sI_S.
\tag{PR.40}
$$

The output helper includes every actually accessible success register.
There exist $0<a\leq b<\infty$ with
$a\tau_-\leq\tau_+\leq b\tau_-$, and the same constants satisfy

$$
a\mathcal T_r(\tau_-)\leq\mathcal T_r(\tau_+)
 \leq b\mathcal T_r(\tau_-).
\tag{PR.41}
$$

Every nonzero recorded branch is thus nonzero for both parities and has
equal updated supports. Its normalized states remain phase independent.
If $t_{r,\epsilon}=\operatorname{tr}\mathcal T_r(\tau_\epsilon)>0$,
the actual conditional helper is
$\mathcal T_r(\tau_\epsilon)/t_{r,\epsilon}$; no normalized successor
is assigned when that trace is zero.

Proof. Apply (PR.37) to the success dilation with its recorded outcome
projections, or to its Kraus components. After tracing only unavailable
proof registers, write
$\mathcal T_r(X)=\sum_j A_{rj}XA_{rj}^\dagger$.
Stacking all successful components gives
$\sum_{rj}A_{rj}^\dagger A_{rj}\leq sI$, which is (PR.40).
Finite-dimensional positive definiteness on $S$ supplies $a,b$, for
example the extreme eigenvalues of
$\tau_-^{-1/2}\tau_+\tau_-^{-1/2}$. Positivity preserves their operator
inequalities, proving (PR.41). Positive operators dominating positive
multiples of one another have the same kernel and support. This proves the
remaining assertions. For a joint helper/unread-reference state, the
actual update is $\mathcal T_r\otimes\operatorname{id}$; no accessible
purification or independent replacement of that joint state is inferred.
$\square$

**Theorem 12.4 (finite exact-checkpoint collapse with feedback).** Fix a
finite public height programme $k_0,\ldots,k_L\in(0,c)$. Require the exact
state $\psi_{k_j,\beta,m}$ at every successful checkpoint, for every
initial $\beta\in\mathbb R,m\in\mathbb Z$. Start with equal-support
assistance as in Theorem 12.2. Allow arbitrary finite quantum memory,
finite recorded internal outcomes, common CP updates, and implementation
choices using only the actually retained records. No new history-correlated
input or newly accessible archive is supplied. Then, for each initial
parity separately, the sharp probability of all checkpoints succeeding is

$$
S_L=\prod_{j=1}^L s_*(k_{j-1},k_j),\qquad S_0=1.
\tag{PR.42}
$$

The same protocol attains both values, with complete absorbing failure.

Proof. On a successful recorded branch, (PR.40) gives the exact next
specimen and the actual common CP image of the old helper. Inductively
(PR.41) keeps equal supports on every nonzero branch. Additional
history-independent memory and intermediate processing can be included in
that branch map. Applying (PR.40) to the next chosen implementation bounds
its total conditional success by $s_*(k_{j-1},k_j)$ on either normalized
helper state. Sum over actual branches and induct to obtain (PR.42).
This includes parity-dependent branch probabilities; it never conditions
on a branch possible for only one parity or divides by zero.

For equality use the attaining filter (PR.39) at each cut and leave the
helper untouched on success. Retain all first-failure labels and residues.
The effects of the all-success product and all first-failure products
sum to identity by repeated substitution of $B_j^\dagger B_j+F_j^\dagger
F_j=I$. This is a complete stopped protocol on the original input, without
retry or another specimen. $\square$

This theorem fixes the requested checkpoints. It permits record-dependent
implementations of them, not arbitrary record-dependent changes to the
requested height programme. It is also different from a final-endpoint-only
loop task: deleting intermediate checkpoints can make the endpoint identity
succeed with probability one. No infinite protocol, approximate-target
bound or general mixed-helper optimum is asserted.

## 13. Actual classical reads: exclusive mass and a loss hidden by scalar diagnostics

**Corollary 13.1 (finite acquired record and error-free mass).** Suppose a
finite actually obtained classical record $Y$ has conditional laws
$q_\epsilon(y)$ independent of $\beta$, leaves the specimen unchanged,
and is all accessible history assistance. Its calibrated laws and label
meaning are part of this input promise. Define

$$
a_\epsilon=\sum_{y:q_{-\epsilon}(y)=0}q_\epsilon(y).
\tag{PR.43}
$$

For the fixed programme of Theorem 12.4, the sharp simultaneous survival
pair is

$$
p_\epsilon=a_\epsilon+(1-a_\epsilon)S_L.
\tag{PR.44}
$$

Attainment requires an executable certified distinction between exclusive
and shared labels, and permission for the calibrated fixed-parity endpoint
unitaries of Instrument Boundaries §4.2. Without those extra implementation
premises, (PR.44) is an upper bound and an abstract attainable value in the
added endpoint operation class.

Proof. On a label with both probabilities positive, the one-dimensional
helper promises both complete phase families. Theorem 12.4 bounds its
all-checkpoint survival by $S_L$, regardless of their unequal likelihoods.
An exclusive label has survival at most one. Integration gives the upper
bound. Select the credited parity-specific unitary at every cut on an
exclusive label, and the unassisted optimal filters on a shared label.
The same label-based protocol attains both expressions and has the
complete failure completion already described. Labels of zero probability
for both inputs require no normalized branch. Observed zero counts do not
certify a zero law probability or supply this decoder. $\square$

**Proposition 13.2 (a helper read preserving three scalar diagnostics can
lower exact original continuation).** Use the actual source (PR.26), zero
fixed preparation phases and the **supplied**, source-bound pure helper

$$
\eta_+=\frac{(2,1)}{\sqrt5},\qquad
\eta_-=\frac{(1,2)}{\sqrt5},\qquad \mu=4/5.
\tag{PR.45}
$$

Grant an additional helper-only computational-basis read whose sole
accessible helper output is its classical outcome. No coherent old-helper
bypass, accessible measurement environment or error flag is supplied.
The read channel is
$\rho\mapsto\sum_{y=0}^1\langle y|\rho|y\rangle|y\rangle\langle y|$,
tensored with identity on the specimen and actual unread fields. Thus its
complete source-conditioned output, rather than just a marginal score,
is specified. The resulting accessible helper states are

$$
\tau_+=\operatorname{diag}(4/5,1/5),\qquad
\tau_-=\operatorname{diag}(1/5,4/5).
\tag{PR.46}
$$

Before and after the read, helper-alone trace distance is $3/5$, root
fidelity $\|\sqrt{\rho_+}\sqrt{\rho_-}\|_1$ is $4/5$, and optimal
equal-prior parity guessing probability is $4/5$. Nevertheless:

| Required successful cuts | Supplied coherent helper | Only the acquired basis bit |
| --- | --- | --- |
| $k_H\to k_L$ | $3/7$ | $2/7$ |
| $k_H\to k_L\to k_H$ | $11/35$ | $1/7$ |
| $n$ complete excursions, $n\geq0$ | $1/5+(4/5)7^{-n}$ | $7^{-n}$ |

The coherent column is the credited pure-helper optimum of Theorems 5.1
and 8.1, not a new pure-helper result. The classical column is the sharp
equal-support consequence above. These columns compare endpoint/checkpoint
services, not canonical exact-time/five-mode output equality.

Proof. The pure-density difference already equals
$\operatorname{diag}(3/5,-3/5)$; dephasing leaves it unchanged.
Its positive part has trace $3/5$, giving the stated trace distance and
optimal binary guessing value $(1+3/5)/2$. Pure-state root fidelity is
the modulus of the ket overlap, $4/5$. For (PR.46) it is
$2\sqrt{(4/5)(1/5)}=4/5$ as well.

Here $u=2/3,v=-1/6$. Substitution in the credited (PR.14) gives outbound
value $3/7$ at $\mu=4/5$; (PR.27) gives the excursion column. Both
post-read states are faithful on $\mathbb C^2$, so Theorem 12.4 gives
the other column using $s_*(k_H,k_L)=2/7$ and
$s_*(k_L,k_H)=1/2$. For example the actual $m=0$ and $m=1$ histories
at the same $\beta$ both yield bit zero, with probabilities $4/5$ and
$1/5$. That bit does not certify which exact target is required. Their
specimens are not asserted identical: Theorem 12.2 bounds every common
converter with those specimens present. An unheralded wrong guess cannot
be relabelled as an executed failure. $\square$

**Proposition 13.3 (a permitted error-free read has a different live
successor).** On the same supplied helper, grant instead the helper-only
three-outcome POVM

$$
E_+=\frac19\begin{pmatrix}4&-2\\-2&1\end{pmatrix},\qquad
E_-=\frac19\begin{pmatrix}1&-2\\-2&4\end{pmatrix},\qquad
E_?=\frac19\begin{pmatrix}4&4\\4&4\end{pmatrix}.
\tag{PR.47}
$$

Again retain only the helper outcome as accessible assistance, and keep
the specimen unchanged. All three effects are positive and sum to identity.
Their actual laws in order $(+,-,?)$ are

$$
q_+=(1/5,0,4/5),\qquad q_-=(0,1/5,4/5).
\tag{PR.48}
$$

Thus (PR.44) gives $1/5+(4/5)S_L$. This attains the credited coherent
helper values in Proposition 13.2 for the displayed outbound and excursion
programmes. The helper is consumed; no unchanged-helper-on-success or
on-failure contract is inferred.

Proof. The first two matrices are outer products of $(2,-1)$ and
$(1,-2)$ divided by nine; the third is four times the outer product of
$(1,1)$ divided by nine. Their sum is $I_2$. Direct quadratic forms on
(PR.45) give (PR.48). Each conclusive label selects its calibrated
parity unitary. On $?$, both parities remain possible and the unassisted
checkpoint filters are used. Corollary 13.1 now proves the value with
complete subsequent failure. $\square$

The outcome $?$ is live under this **additional helper-read permission**.
It is neither a canonical specimen failure nor permission to retry a
failed specimen. The mechanism is mature unambiguous discrimination of
an already supplied pair. Neither this POVM nor the basis read constructs
or acquires that initial pair from the original unknown specimen.

**Corollary 13.4 (exact-target support discontinuity).** A supplied binary
classical record with laws $(1-e,e)$ and $(e,1-e)$ has exactly the
unassisted checkpoint optimum for every $0<e<1/2$, while at $e=0$ it
allows deterministic parity-selected endpoint action. The two noisy laws
approach their perfect-label laws in total variation by $e$.

Proof. For every positive $e$ both labels are shared and $a_+=a_-=0$ in
(PR.43). At zero the labels are exclusive and $a_+=a_-=1$.
Apply (PR.44); the total-variation calculation is immediate. $\square$

This is a discontinuity of an **exact conversion** task. It gives no
nonzero-noise lower bound for approximate conversion and no error estimate
for a canonical instrument. Scalar helper diagnostics in Proposition 13.2
are not claimed to be sufficient statistics for the full joint experiment.

## 14. Live calibration records and an uncalibrated orthogonal latch

**Definition 14.1 (one joint source with a latent convention).** Fix distinct
$k,l\in(0,c)$. In addition to (PR.34), the source has a classical
convention $g\in\{0,1\}$ and emits

$$
Y=\pi(m)\mathbin{\oplus}g,\qquad \pi(m)=m\bmod2\in\{0,1\}.
\tag{PR.49}
$$

The source parameter domain includes every $(g,\beta,m)$. This latch is an
explicit added source output port: the source copies and XORs its classical
programme-sector field. It is not a nondisturbing measurement of the
unknown specimen's parity. The programme, $g$ and any source-sensitive
callback are unavailable to the observer unless explicitly delivered.
Granting the latch strengthens the following obstruction.

A fixed acquisition stage, before the requested continuation, has live
record $C$ in a standard Borel space $\mathcal C$. Its actual live
accessible output measure for each source parameter is

$$
\mu_g(dz)\,
 |\psi_{k,\beta,m}\rangle\langle\psi_{k,\beta,m}|
 \otimes|\pi(m)\oplus g\rangle\langle\pi(m)\oplus g|,
\qquad q_g=\mu_g(\mathcal C)\leq1.
\tag{PR.50}
$$

The subprobability $\mu_g$ is independent of $\beta,m$. $C,Y$ include
all accessible history-bearing assistance; no quantum calibration token,
readable programme, additional correlated receiver/reference, timing
side port or archive is omitted. Common history-independent ancillas are
allowed. Other actual fields remain jointly present and unread. Every dead
acquisition outcome retains its actual archive and absorbing $f$.

After the stage one common finite adaptive endpoint protocol may use only
$C,Y$ and common permitted metadata. Equivalently its accepted operations
are a measurable kernel of trace-nonincreasing CP maps selected by the
actual $(z,y)$. Every accepted specimen must be exactly
$\psi_{l,\beta,m}$ for all $g,\beta,m$. A dead branch cannot produce an
accepted live original successor. This contract specifies which ports are
available at this stage; additional observations or interventions during
acquisition are a different acquisition design.

Put $\nu=\mu_0+\mu_1$ and choose Radon–Nikodym densities
$f_g=d\mu_g/d\nu$. Define, up to $\nu$-null sets,

$$
O=\{f_0>0,f_1>0\},\qquad
E_g=\{f_g>0,f_{1-g}=0\},\qquad e_g=\mu_g(E_g).
\tag{PR.51}
$$

Here exclusivity is measure-theoretic, not a statement about topological
supports. The laws and their exclusive sets are analytical objects; their
definition gives the observer neither a law oracle nor an executable decoder.

**Theorem 14.2 (live calibration-support price).** Under Definition 14.1,
let $P_g(\beta,m)$ be the probability, including acquisition survival, of
an accepted exact continuation. With $s=s_*(k,l)<1$,

$$
P_g(\beta,m)\leq s q_g+(1-s)e_g
\quad\text{for every }g,\beta,m.
\tag{PR.52}
$$

In particular any positive gain over $sq_g$ requires

$$
e_g\geq\frac{P_g(\beta,m)-sq_g}{1-s}.
\tag{PR.53}
$$

Calibration obtained only on dead branches contributes no $e_g$.

Proof. Fix a physical latch value $y$. On $O$ both conventions are
possible, with opposite parities $\pi(m)=y\oplus g$, and each parity
still allows every phase. The same acceptance map selected by $(z,y)$
must therefore transform the full two-parity phase family exactly.
Instrument Boundaries Theorem 4.1 bounds its acceptance probability by
$s$, with arbitrary retained success auxiliaries included through their
Kraus components. Unequal nonzero likelihoods for the conventions do not
alter this exact bound. On $E_g$ acceptance is at most one.

There is no uncountable-null-set assumption in that argument. For each
$y,g$, first impose the purity/correctness condition on a countable dense
set of phases and one signed winding of each needed parity. Positivity
of the integrated output implies branchwise correctness almost everywhere
for each such parameter. Take the common conull set of these countably
many conditions. On $O$ the two restricted measures are mutually
absolutely continuous, so this is a common conull set for both. At each
remaining $z$ the selected finite-dimensional CP map is continuous in the
specimen input; the dense phase conditions extend to the full circle.
Thus rigidity applies on that one set and bounds all phases there.
Other signed windings of the same parity have the identical input state
and are not passed to the map. They inherit the same bound.

For the actual input convention $g$, integrate against $\mu_g$.
The overlap contributes at most $s(q_g-e_g)$, and the exclusive part at
most $e_g$. Dead outcomes contribute zero by the absorbing-successor
contract. This proves (PR.52) and rearrangement gives (PR.53).
No failed specimen is replaced by a live one from another run. $\square$

**Proposition 14.3 (the additional premises for sharpness).** If a certified
executable decoder identifies $E_0,E_1$ up to null sets and calibrated
parity-specific endpoint gates are permitted, the bound (PR.52) is
simultaneously attainable for all parameters.

Proof. On $E_g$, compute the parity from the actual latch $y\oplus g$
and use its unitary. On $O$, use the unassisted attaining filter. Complete
its failure with (PR.39). Integrating gives equality. $\square$

Without that decoder, support exclusivity is a necessary resource relation,
not an acquired certificate. Theorem 14.2 addresses classical calibration
assistance exactly as specified. It is not an upper bound with uncounted
quantum calibration assistance or an always-readable source convention.

## 15. Source-realized calibration on absorbing failures

**Definition 15.1 (time-separated canonical acquisition).** Set the actual
rational source parameters to (PR.26), writing $H=1/4$, $L=1/8$ and
$v=H-L=1/8$, with zero fixed preparation phases. Start at a live
$\psi_{H,\beta,m}$ cut and emit (PR.49). For a public integer $n\geq1$,
the source installs and executes a prescribed acquisition of duration $6n$.
For $j=0,\ldots,n-1$, write $t=6j+s$, $0\leq s\leq6$, and set

$$
k_g(6j+s)=
\begin{cases}
H,&0\leq s\leq3g,\\
H-v(s-3g),&3g\leq s\leq3g+1,\\
L+v(s-3g-1),&3g+1\leq s\leq3g+2,\\
H,&3g+2\leq s\leq6.
\end{cases}
\qquad \chi_g(t)=\chi_g(0).
\tag{PR.54}
$$

Execute exactly the canonical instrument (OC.19)–(OC.19b), stopping at
its first failure. Thus, with $p(x)=(x,c-x,Z,c-x,x)$,

$$
\begin{aligned}
\lambda_g&=(k_g')_+/k_g+(-k_g')_+/(c-k_g),&
S_g(t)&=e^{-\int_0^t\lambda_g},\\
K_g(t)&=\operatorname{diag}_i
 \sqrt{S_g(t)p_i(k_g(t))/p_i(H)},&
\gamma_{g,i}&=\lambda_g-(\log p_i(k_g))',\\
J_{g,i}(t)&=\sqrt{\gamma_{g,i}(t)}|f\rangle\langle i|K_g(t).
\end{aligned}
\tag{PR.55}
$$

There is no current phase increment, so the relative phase factors in
$K_g$ are one. Actual failure output is $(\tau,i,f)$ with CP density
$J_{g,i}(\tau)\rho J_{g,i}(\tau)^\dagger$; success retains the live
specimen, latch and no-failure record. Tensor identity on actual unread
reference/archive fields. All five mode names and exact timestamps remain.

This is source-owned **programme execution**, under the already declared
ideal canonical service, before the common continuation. It does not ask
an observer to choose an unknown $g$-dependent waveform. The source has
$g$ and its installed programme; the observer receives neither. During this
prescribed acquisition there is no extra waveform/height read, intermediate
specimen intervention, command-name leak or source callback. Such an added
port could reveal $g$ on live branches and would change (PR.50). The
one-bit latch and the source-owned schedule are explicit parts of the joint
source, rather than secretly inferred services of the original transport law.

**Theorem 15.2 (sharp post-acquisition curve).** For each $n\geq1$ and
every $g,\beta,m$, Definition 15.1 has live mass $q_n=7^{-n}$ and
probability

$$
R_n=1-7^{-n}
\tag{PR.56}
$$

of acquiring a zero-error calibration of $g$ by its actual failure record.
Every such calibrated specimen is already at absorbing $f$. On live
branches $\mu_0=\mu_1=q_n\delta_{\mathrm{live}}$, so $e_0=e_1=0$.
After this stage require the same one-unit phase-preserving height leg
$H\to L$ on that same surviving specimen. Among all common exact
endpoint CP acceptance protocols using the delivered archive and latch,
the sharp unconditional success probability from the initial live cut is

$$
P_n=\frac27\,7^{-n}=\frac{2}{7^{n+1}}
    =\frac27(1-R_n).
\tag{PR.57}
$$

The canonical horizontal instrument attains it, with its own full failure
time/mode law retained. This optimizes continuation after this **fixed
acquisition stage**, not acquisition design or interventions during that
stage.

Proof. The credited monotone-leg factors are
$s_*(H,L)=2/7$ and $s_*(L,H)=1/2$. On a whole zero-phase excursion,
height returns to $H$ and diagonal probability ratios cancel. Hence its
no-failure operator on **all five live modes** is $I_5/\sqrt7$.
Waits give identity. Composition gives

$$
K_g(6n)=7^{-n/2}I_5,
\qquad K_g(6n)^\dagger K_g(6n)
 +\sum_i\int_0^{6n}J_{g,i}^\dagger J_{g,i}\,dt=I_5.
\tag{PR.58}
$$

The second identity is the supplier's complete canonical normalization.
Thus every initial joint specimen/reference state has the actual live
output $q_n\rho$, not merely the same specimen marginal. In particular
all original-family phases and signed sectors have live probability $q_n$.
The live clock/no-failure trace, terminal height, public block count,
permissions and metadata are common for both $g$. The emitted latch is
retained separately as in (PR.50).

Rates vanish on waits. Up to endpoints of zero measure, all first failures
lie respectively in the disjoint sets

$$
A_0=\bigcup_{j=0}^{n-1}(6j,6j+2),\qquad
A_1=\bigcup_{j=0}^{n-1}(6j+3,6j+5).
\tag{PR.59}
$$

There are no failure atoms at the joins. The actual observed $\tau$
therefore determines $g$ with zero error on each failed run. Keep its full
$(\tau,i)$, rather than replacing it by this decoded bit. The calibration
probability is the total failure mass $R_n$, and the live records give the
identical measures stated. No dead record calibrates a surviving specimen
in another run.

Apply Theorem 14.2 at $k=H,l=L$, with $s=2/7$, $q_g=q_n$ and $e_g=0$.
It bounds every allowed endpoint acceptance by (PR.57), including protocols
that use the retained unknown specimen quantum mechanically. Append the
canonical one-unit $H\to L$ instrument on a live branch to attain that
value. It has exactly the original target on success and an absorbing
first failure on the other branch. Old failures keep their old event and
$f$ and never execute this new live leg. $\square$

**Proposition 15.3 (actual prehistory, finite resources and earlier failures).**
Every state quantified in Theorem 15.2 is reached from the same positive
preparation by Proposition 2.2 with auxiliary height $a=L$. Its rectangle
coefficient and phase variation are

$$
B_{\beta,m}=\frac{24}{5}\beta-\frac45\pi m,
\qquad \operatorname{TV}(\chi)=2\pi|m|+2|B_{\beta,m}|.
\tag{PR.60}
$$

The prehistory takes five units. The acquisition (PR.54) and final target
leg satisfy both original regularity alternatives, strict support at least
$1/20$, zero additional phase variation and speed at most $1/8$.
Acquisition alone has height variation $n/4$, coordinate quadratic cost
$\int(k_g')^2=n/32$, and a common BV-velocity bound
$\operatorname{TV}(k_g')\leq n/2$, without artificial exterior jumps.
The target leg adds one time unit and height variation $1/8$.
If the five-unit preparation is itself implemented with the canonical
stopped instrument, its live mass is $1/7$; retaining its failures too,
the all-success probability from that earlier preparation is
$2/7^{n+2}$.

Proof. (PR.60) is the credited source map (PR.33), with all real lifts
retained. Acquisition and target heights lie in $[1/8,1/4]$, where the
smallest $x,c-x,Z$ is $1/20$. They are finite affine pieces and waits,
joined continuously. Each loop travels distance $1/4$ at speed $1/8$
for two time units, giving the variation and quadratic cost. At its
velocity changes the total variation is at most
$1/8+1/4+1/8=1/2$ per block; the initial moving leg for $g=0$ can
only remove the first jump from this upper bound. The preparation has the
same two nontrivial height legs as one loop, while phase-only legs add no
hazard, so its survival is $1/7$. Its canonical failures remain separate
absorbing branches. Conditional on surviving it, the specimen, no-failure
record and terminal clock are precisely the live starting cut used above.
Multiplication by that actual positive live mass proves the last value.
$\square$

The public rational schedule and repeat count have finite descriptions;
$n$ needs $O(\log(n+1))$ bits in a loop programme. The source-side $g$
and emitted latch each cost one classical bit. Source preparation also
carries the actual integer/phase programme. Arbitrary real $\beta$ need
not admit a finite effective encoding. The dense subfamily
$\beta/\pi\in\mathbb Q$, $m\in\mathbb Z$ has finite symbolic
programmes, with separately paid integer/rational bit lengths, and already
forces the same bound by continuity of each common CP map. This observation
does not replace the full real source theorem by a rational-source theorem.
There is no uniform finite past variation or programme width for all histories.

The calibrated clock, source-start alignment, reference, permissions,
installed source executor, selector/update state and actual archives are
separate resources. The exact continuous failure-time archive is the
supplier's ideal recording resource, with no fixed finite-bit implementation
claimed. An observer reading $g$, the installed schedule or any equivalent
source-sensitive port would acquire extra live assistance and leave the
obstruction's premises. The deliberately restricted delivered boundary
here is not asserted to be a complete acquired observer.

As $n\to\infty$, (PR.56) tends to one while (PR.57) tends to zero.
This is a sequence of finite experiments with growing horizon and variation,
not an executed infinite acquisition or a universal acquisition tradeoff.
It proves that a high calibration probability in the complete output can
coexist with zero calibration mass on its usable live branches.

## 16. Sources, operation resources and remaining joint acquisition obligations

**Source map 16.1 (credited results and precise uses).** Repository suppliers
for §§12–15 are their committed public versions at
`773d4d43b91abd515be1059283d79dd6572fc174`. Earlier sections retain their
own stated readings. These references carry no fresh compilation claim.

| Supplier | Use and boundary |
| --- | --- |
| `D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean` and its owning Scribe | `ValidBase`, `probability`, signed `phaseWeight`, `weight_compatible` and `finite_rectangles_realize` supply the positive source and actual rectangles. The Scribe's all-signed-sector application supplies the real lift synthesis; that whole ordinary application is not attributed to the rectangle declaration alone. |
| `D5/S3/Quantum/Fibers/OriginalControlComposition.lean` and its owning Scribe | `OriginalControl`, `FiniteC1Control` and `concatenate_original` preserve both regularity alternatives, literal prefix, matching height, relatively translated real tail, finite/zero durations and additive continuous weighted integrals. No unknown old lift, sensor or actuator is delivered. |
| Instrument Boundaries, Theorem 4.1, §§4.2–5.2, 9–15 | Successful-Kraus rigidity, unassisted $s_*$, fixed-parity rotations, checkpoint products and the complete canonical stopped law are reused. §§12–14 add the equal-support probabilistic/update and live-calibration deductions; §15 specializes canonical scalar loops, without claiming their factors or completeness as new principles. |
| This volume §§4–8 | Pure-helper Gram feasibility, success-return versus consumable optima and the repeated-excursion value are credited. Proposition 13.2 compares those values with an actually specified read; it does not rederive the pure-helper frontier. |
| Instrument Stability; Sampled Instrument Certificates | Marked TV and complete-reference metrics, strong sufficient error data and finite timed-sample certificates keep their exact regularity, sensor and joint-kernel premises. No approximate certificate is imported for the endpoint gates here. |
| Event Memory and Coarse Aliasing; Quantum Carrier Minimum | Actual-event memory and exact-time/coarse-law distinctions remain. The live $M_3$ carrier correspondence preserves supplied correlated archives; its separate lower bound denies accessible assistance. Neither its minimum nor a full archive capacity is inferred for these assisted protocols. |
| Record Acquisition | Finite-query obstructions and conditional area/winding certification are credited. An empirical calibration score does not certify the exclusive zero probabilities in (PR.43) or (PR.51). |
| Transport–Memory Completion §§2.9–2.12/2.18 | Actual common coherent source/port, aligned acquired readings, known nonzero amplitudes and record overlap remain required. An orthogonal parity latch has a different consumer from interference, and an unknown overlap is not divided out. |
| Process Geometry §34, PG.3400b-full/PG.3400c and PG.3402-run-next; Atlas Stable Core Holonomy Theorem 6.3 | One actual source/epoch image and joint acquisition, selection and success/failure update routes are required. Equal helper diagnostics or a static marginal record do not instantiate individual four-view recovery or its response-preserving update hypotheses. |

**Literature statement 16.2 (mature mechanisms and checked scope).**

| Primary source | Exact use and non-transfer |
| --- | --- |
| A. Chefles, R. Jozsa and A. Winter, [On the existence of physical transformations between sets of quantum states, quant-ph/0307227v1](https://arxiv.org/html/quant-ph/0307227v1), Theorems 2–3; *International Journal of Quantum Information* 2(1), 11–21, DOI [10.1142/S0219749904000031](https://doi.org/10.1142/S0219749904000031) | `literature-attested`: finite pure-family transformations are governed by positive environment Gram factors and positive outcome contributions. The dilation can discard source-dependent environments. This mature framework, already credited in §10, supplies no acquired helper or calibration port. Our continuous-family input is handled by the credited rigidity and the explicit support argument, not by silently importing a finite-family acquisition theorem. |
| T. Rudolph, R. W. Spekkens and P. S. Turner, [Unambiguous discrimination of mixed states, quant-ph/0303071v2](https://arxiv.org/html/quant-ph/0303071v2), support/kernel conditions and Eqs. (1)–(3); *Physical Review A* 68, 010301(R), DOI [10.1103/PhysRevA.68.010301](https://doi.org/10.1103/PhysRevA.68.010301) | `literature-attested`: an error-free conclusive effect annihilates the competing support; equal supports preclude such a conclusive label. Classical exclusive-mass reasoning and the unambiguous-read mechanism are mature. The stronger original-source probabilistic conversion factorization and its update application are proved in §§12–14. No general unequal-support mixed optimum is imported. |
| [Classical Sufficiency in Quantum Statistical Experiments, arXiv:2609.29348v1](https://arxiv.org/html/2609.29348v1), abstract and prescribed-measurement/invariant-block formulation | A recent primary scope comparison: sufficiency is relative to a declared admissible measurement class, with classical decision postprocessing. It supplies no operation equality for this full original-source continuation or calibration acquisition. No theorem is transferred. |
| [What Must a Quantum-Memory Decoder Know About Temporally Correlated Noise?, arXiv:2610.03545v1](https://arxiv.org/html/2610.03545v1), §III.1 | A recent primary scope comparison: its calibration analysis fixes a known common system/environment dilation and discusses independently prepared environment copies. Those copies and calibration experiments are absent from this absorbing original source. No cost, sensor or decoder theorem is transferred. |

Positive-operator domination, spectral decomposition, Stinespring dilation,
finite CP composition, Radon–Nikodym decomposition and purity of a convex
positive sum are mature mathematics. The new exposition is `repo-derived`:
Theorem 12.2 and Corollary 12.3, their exact finite continuation consequence,
(PR.44), the actual diagnostic-preserving read comparison, the live-bound
(PR.52), and the source-realized post-stage curve (PR.57). No worldwide
priority or independent-review claim is made. The bounded primary-source
comparisons identify no directly sufficient acquired original observer;
that bounded finding establishes neither absence nor impossibility.

**Resource boundary 16.3.** The supplied coherent helper in (PR.45) has
occupied dimension two; the basis read retains two classical values and
(PR.47) three. These are different accessible algebras and output ports,
not equal hardware prices. The mixed upper bound allows arbitrary finite
memory and counts all accessible joint assistance. An attaining one-cut
endpoint completion can keep a failure residue of dimension at most six
on the active $V\otimes\mathbb C^2$ input, or ten on its full five-mode
extension. The flags and old archives are additional registers. At $L$
fixed cuts the first-failure-or-all-success index has $L+1$ possibilities;
any additional internal labels and payloads must also be retained and paid.

The displayed rational/algebraic helper, POVMs and filters have finite
exact mathematical descriptions. Preparing a source-bound helper,
certifying its state/support and label convention, executing the calibrated
reads and gates, timing, reference precision, arithmetic and programme
storage are separate services/costs. No exact physical execution at finite
precision follows. Theorem 12.2 leaves the helper unchanged on attaining
success but imposes no unchanged return on failure. The helper reads consume
it. Canonical failure retains its exact first time and original mode;
endpoint failure instead retains its declared auxiliary residue and flag.
Their output laws and permissions are kept distinct throughout.

**Open boundary 16.4 (the remaining usable joint relation).** A useful
acquisition route must actually retain a same-source live relation strong
enough for the selected action: here coherent assistance surviving update,
or certified error-free labels with their actual live/inconclusive
successors. It must obtain source/epoch identity, clock/reference and
calibration, retained archives, permissions and every programme/selector/
update input that can affect the declared future. Those must coexist in
one actual implementation, with all executed failure and unexecuted
rejection branches. A supplied helper, support calculation or success
probability does not acquire that relation. Theorem 15.2 rules out the
displayed calibration-on-failure route as a replacement for it, not all
other acquisition designs.

General unequal-support or phase-dependent mixed helpers, newly readable
archives, unknown support certification, approximate targets, arbitrary
record-dependent requested menus, canonical all-prefix exact-time/five-mode
implementation and unbounded execution are not settled here. The complete
original class is not replaced by the double-wall examples or by finite
resource promises. Full space/time/boundary/memory mutual recovery, native
stationary $\alpha/\beta$ rate/cofinality and the separate fixed-Hamiltonian
quantum minimax retain their original objectives. No source/action/resource
bridge to the AURIC C114, twisted-ground, PCA or static arithmetic sources
is asserted. These are ordinary mathematical proofs and explicit service
boundaries, without new Lean verification, physical realization or completion
of the continuing programme.

## 追加锚（本行以下为增补区）

## 17. Finite canonical return acquisition and its promised joint source

The consumer in §§17–23 is the exact phase-preserving height continuation
of §§2 and 12, after an actual canonical acquisition on the same still-live
specimen. The additional result is the attained finite-charge region for
live yield and classical parity-calibration error. Scalar return factors,
full-phase rigidity and the shared-support obstruction are credited
ingredients, rather than new claims.

All repository references in these sections select the immutable public
revision 1f58736f50945c7cfeca93ce160eb9b46a3a7e7e. The results are ordinary
mathematical proofs, without a new Lean certificate or physical implementation.

**Definition 17.1 (source, cut and accessible acquisition records).** Fix
$0<c<1/2$, $Z=1-2c$, and distinct $a,l\in(0,c)$. Use the same positive
preparation, base $(c,c,Z)$, calibrated directions (PR.3), negative
state-phase convention and actual source family (PR.34). At the initial
live cut the specimen is

$$
\psi_{a,\beta,m}=\sqrt Z e_2+e^{-i\beta}
 \bigl(\sqrt{2a}U_++(-1)^m\sqrt{2(c-a)}U_-\bigr),
\qquad \beta\in\mathbb R,\quad m\in\mathbb Z.
\tag{PR.61}
$$

Write $\varepsilon=\pi(m)=m\bmod2\in\{0,1\}$, so that
$(-1)^m=(-1)^\varepsilon$. This bit convention differs from the sign
notation in (PR.8). The entire signed winding and real residual (PR.5)
remain in the actual source history. Neither is an observer input.

After the past and its actual reference/archive have been fixed, draw a
finite public seed $U\in\mathcal U$ with $\nu(u)>0$ and
$\sum_u\nu(u)=1$, independently of that entire past and joint quantum
state. For every $(\varepsilon,u)$ the source executes a prescribed
original control $k_{\varepsilon,u}$ of finite duration $T_u\geq0$,
starting and ending at $a$, remaining strictly in $(0,c)$, and having
constant relative phase. The duration is the same for both parities at
each seed. Either original regularity alternative is allowed. Duration
zero means the matching identity. The source uses the canonical complete
stopped instrument and stops at its first failure.

The dependence of this future programme on the old parity is an
**additional promised joint source relation**. Its executor retains the
source-side bit $\varepsilon$, receives $U$, and selects its installed
path. This constructs an original-history subfamily with a specified
past/future correlation. It does not extract a bit from an arbitrary
unknown old specimen, and is not a common observer-selected waveform
independent of the hidden history.

During acquisition there is no intermediate specimen intervention,
waveform/height read, source-sensitive timing read, readable programme
name, source callback, environment port or supplied helper. At a live
terminal cut all accessible history-bearing calibration assistance is
$U$ and the no-failure flag, together with fixed source-independent
metadata. Seed-dependent terminal times are already determined by $U$.
Any public finite checkpoint flags are all no-failure on this live branch.
Independent controller randomness can be included in $U$.

All actual unread quantum references, archives and source records remain
jointly present; the acquisition acts by identity on them, apart from
the source's declared classical programme control. They are not assistance
to the later observer operation. Making one readable, including the
source-side parity bit or its programme, changes this input contract.
Source/epoch identity, clock/reference, calibration, permissions and pending
request are retained as actual fields, not reconstructed from a marginal.

**Definition 17.2 (charge, yield and calibration score).** For each path put

$$
\begin{aligned}
\lambda_{\varepsilon,u}(t)
 &=\frac{(k'_{\varepsilon,u}(t))_+}{k_{\varepsilon,u}(t)}
  +\frac{(-k'_{\varepsilon,u}(t))_+}{c-k_{\varepsilon,u}(t)},\\
\Lambda_{\varepsilon,u}
 &=\int_0^{T_u}\lambda_{\varepsilon,u}(t)\,dt,\qquad
q_\varepsilon(u)=e^{-\Lambda_{\varepsilon,u}}.
\end{aligned}
\tag{PR.62}
$$

Fix a finite bound $C\geq0$, set $\ell=e^{-C}$, and require
$\Lambda_{\varepsilon,u}\leq C$ for every parity and seed. This is the
canonical survival charge (OC.15), not a physical energy or memory price.

For this binary calibration score only, give the two parities equal prior,
at any fixed $\beta$ and one actual signed winding of each parity. No prior
on the whole original history is asserted. Decoders use the actually
retained classical record, with no specimen measurement or additional
quantum calibration token. Define

$$
\begin{aligned}
P&=\Pr(\mathsf L)=\frac12\sum_u\nu(u)(q_0(u)+q_1(u)),\\
B_*&=\inf_d\Pr(\mathsf L,\ d(U)\ne\varepsilon),\qquad
R_*=\frac{B_*}{P}.
\end{aligned}
\tag{PR.63}
$$

Here $\mathsf L$ is survival of this acquisition, and randomized decoders
are allowed. All these probabilities are measured from the actual
initially live cut. Earlier preparation survival is a separate multiplier;
conditioning on an actually reached cut supplies no reset or extra copy.

## 18. Complete joint CP successor of a return programme

**Proposition 18.1 (scalar live return with every failure retained).**
For every path in Definition 17.1, let $p(x)=(x,c-x,Z,c-x,x)$ and set

$$
\begin{aligned}
S(t)&=\exp\left(-\int_0^t\lambda(s)\,ds\right),\\
K(t)&=\operatorname{diag}_i
       \sqrt{S(t)p_i(k(t))/p_i(a)},\\
\gamma_i(t)&=\lambda(t)-(\log p_i(k(t)))',\\
J_i(t)&=\sqrt{\gamma_i(t)}\,|f\rangle\langle i|K(t).
\end{aligned}
\tag{PR.64}
$$

Path indices are suppressed in this formula. These are precisely
(OC.19)–(OC.19b) with zero phase increment. In particular

$$
K(T)=\sqrt q\,I_5,\qquad
K(T)^\dagger K(T)+\sum_{i=0}^4\int_0^T J_i(t)^\dagger J_i(t)\,dt=I_5.
\tag{PR.65}
$$

For every actual joint specimen/reference input $\rho_{AR}$, conditional
on its actual history and the seed, the unnormalized live successor is
$q\rho_{AR}$. Failure in a Borel event $E$ and mode $i$ has successor

$$
\int_E(J_i(t)\otimes I_R)\rho_{AR}
                 (J_i(t)^\dagger\otimes I_R)\,dt,
\tag{PR.66}
$$

with the same $U$, exact first time, original mode name, old archive and
absorbing $f$ retained. Append $\nu(u)$ for the joint seed/outcome law.
No failure is merged, retried or replaced by a live successor.

Proof. Strict interiority and continuity on a compact interval bound
$k,c-k$ away from zero. Either original regularity alternative makes
$k$ absolutely continuous and $k'$ integrable, so $\Lambda<\infty$ and
$q>0$. The logarithmic derivatives of the two repeated height probabilities
and the middle probability are $k'/k,-k'/(c-k),0$. Their maximum is
$\lambda$, so all $\gamma_i$ are nonnegative and integrable. The squared
$i$th diagonal entry of $K(t)$ has derivative
$-\gamma_i(t)|K_{ii}(t)|^2$ almost everywhere. Integrating this identity
gives (PR.65) entry by entry. A height return cancels the probability
ratios, and the constant phase removes all relative phase factors,
giving its first equality.

The displayed Kraus operations are CP; the same normalization proves
their completeness on every joint input after tensoring with identity.
An already stopped input retains its old event and has the identity
stopped successor. Equations (PR.65)–(PR.66), not separate specimen and
archive marginals, give the full joint operation. $\square$

For clarity about the source correlation, if $h$ is an actual classical
past label with parity $\pi(h)$ and conditional joint state $\rho^h_{AR}$,
its live output, including the seed, is

$$
\Pr(dh)\,\nu(u)\,q_{\pi(h)}(u)\,
 |u,\mathsf L\rangle\langle u,\mathsf L|\otimes\rho^h_{AR}.
\tag{PR.67}
$$

Use the same actual $\Pr(dh)$ in every failure block of (PR.66).
Normalizing the live output reweights this history mixture by its actual
$q_{\pi(h)}(u)$; its unconditional archive marginal need not stay fixed.
The source executor controls (PR.64) by its classical $(\pi(h),u)$.
These are controlled CP operations on that promised joint source,
not a single specimen-only operation that secretly reads $h$. No
coherent superposition of these classical programme labels is assumed.
The formula also covers arbitrary entanglement with $R$ within each
history-conditioned input, before restricting to (PR.61).

## 19. The sharp attained charge, live-yield and live-error region

**Theorem 19.1 (complete finite-charge region).** In Definitions 17.1–17.2
the attainable pairs of live yield and Bayes-optimal live error mass are
exactly

$$
\ell\leq P\leq1,\qquad
\max\left\{\frac{\ell}{2},P-\frac12\right\}
       \leq B_*\leq\frac P2.
\tag{PR.68}
$$

Every point of this region is attained by a uniform binary seed, with
equal live yield $P$ for each parity. Its decoder has the same conditional
error for both parities. In particular the sharp lower boundary is

$$
R_*\geq
\max\left\{\frac{\ell}{2P},1-\frac1{2P}\right\}.
\tag{PR.69}
$$

This is also the optimum worst-parity conditional error among the
specified acquisitions with common per-parity live yield $P$. It is
not a minimax statement over all unknown original sources or all observers.

Proof. Proposition 18.1 makes the two unnormalized live prior weights at
seed $u$ equal to $\nu(u)q_0(u)/2$ and $\nu(u)q_1(u)/2$.
Choosing the more likely parity minimizes error at that record; mixing
decisions cannot reduce its smaller weight. Thus

$$
B_*=\frac12\sum_u\nu(u)\min\{q_0(u),q_1(u)\}.
\tag{PR.70}
$$

The charge promise gives $\ell\leq q_\varepsilon(u)\leq1$, hence
$\ell\leq P\leq1$. For numbers $x,y\in[\ell,1]$,

$$
\min(x,y)\geq\ell,\qquad
\min(x,y)=x+y-\max(x,y)\geq x+y-1,\qquad
\min(x,y)\leq(x+y)/2.
$$

Substitution in (PR.70) proves all inequalities in (PR.68).

Conversely take any $(P,B)$ satisfying (PR.68), and put
$q_{\rm lo}=2B$, $q_{\rm hi}=2P-2B$.
Then $\ell\leq q_{\rm lo}\leq q_{\rm hi}\leq1$.
Draw $U$ fairly in $\{0,1\}$ and prescribe

$$
q_\varepsilon(u)=
\begin{cases}
q_{\rm hi},&u=\varepsilon,\\
q_{\rm lo},&u\ne\varepsilon.
\end{cases}
\tag{PR.71}
$$

Section 20 constructs actual original controls for each of these values.
For each parity the yield is $(q_{\rm hi}+q_{\rm lo})/2=P$.
The rule $d(u)=u$ is Bayes optimal, has error mass $q_{\rm lo}/2=B$
for either parity considered separately, and hence conditional error
$B/P$. In the equal-prior mixture its error mass is also $B$.
For the lower boundary these parameters are equivalently

$$
(q_{\rm lo},q_{\rm hi})=
\begin{cases}
(\ell,2P-\ell),&P\leq(1+\ell)/2,\\
(2P-1,1),&P\geq(1+\ell)/2.
\end{cases}
\tag{PR.72}
$$

If both parity yields equal $P$, the average of their conditional error
probabilities for any decoder is its equal-prior error mass divided by
$P$. Their maximum is at least that average, and (PR.70) bounds the
average from below. The balanced construction attains it for both
parities, proving the stated symmetric minimax claim. $\square$

**Corollary 19.2 (optimal yield and required charge).** For finite $C$,
the smallest conditional error in this class, allowing yield to vary, is

$$
\inf R_*=\frac{\ell}{1+\ell}=\frac1{1+e^C},
\qquad P_{\rm opt}=\frac{1+\ell}{2}.
\tag{PR.73}
$$

For $0<\delta<1/2$, existence of an acquisition with $R_*\leq\delta$
therefore requires and is achieved with

$$
C\geq\log\frac{1-\delta}{\delta}.
\tag{PR.74}
$$

Proof. The first branch of the lower boundary (PR.69) decreases with
$P$, and the second increases. They meet at $(1+\ell)/2$.
The construction (PR.72) attains their intersection. Solving
$1/(1+e^C)\leq\delta$ gives (PR.74). At $C=0$ only
$P=1,B_*=1/2$ occurs. Every finite $C$ has strictly positive
minimum error. $\square$

All scores refer to the stated binary decision and prior. A smaller
$R_*$ is not an exact parity certificate, whole-law identification,
instrument-distance bound or guarantee for every future decision.

## 20. Actual original programmes attaining every point

**Proposition 20.1 (an exact excursion for each survival likelihood).**
For every $q\in(0,1]$, define

$$
b(q)=\frac{ac}{a+q(c-a)},\qquad d(q)=b(q)-a,\qquad
k_q(t)=
\begin{cases}
a+d(q)t,&0\leq t\leq1,\\
b(q)-d(q)(t-1),&1\leq t\leq2.
\end{cases}
\tag{PR.75}
$$

Keep relative phase constant. This is an actual two-unit original control,
with both original regularity alternatives, whose canonical live return
operator is $\sqrt q I_5$. It realizes every entry of (PR.71).

Proof. The denominator in $b(q)$ is positive. Direct subtraction gives
$a\leq b(q)<c$, with equality $b(q)=a$ exactly at $q=1$.
Both affine legs and their join remain strictly positive and continuous.
They are absolutely continuous and finite piecewise $C^1$ with constant
rates on each closed piece. Their phase variation, new winding and
transported phase increment are zero. On the upward leg, integration
of $\lambda=k'/k$ gives survival $a/b$. On the downward leg,
integration of $\lambda=-k'/(c-k)$ gives survival
$(c-b)/(c-a)$. Their product is

$$
\frac ab\,\frac{c-b}{c-a}=q.
\tag{PR.76}
$$

Proposition 18.1 gives the full scalar return and complete failure law,
not just a chosen Bernoulli trial. At $q=1$ both legs are waits, with
no failure. No nontrivial instantaneous excursion is used. $\square$

For an explicit time/mode law on these affine programmes, write
$b=b(q)$, $d=b-a$ and $A=a(c-b)/b$. On the two open legs,

$$
\begin{array}{c|c|c}
 &S(t)&(f_0,f_1,f_2,f_3,f_4)(t)\\ \hline
0<t<1&a/k(t)&
 \dfrac{ad}{k(t)^2}(0,c,Z,c,0)\\[4pt]
1<t<2&A/(c-k(t))&
 \dfrac{Ad}{(c-k(t))^2}(c,0,Z,0,c)
\end{array}
\qquad f_i=(p_i(a)-S p_i(k))'.
\tag{PR.77}
$$

These weights follow by differentiating the actual CP law:
$f_i=S(\lambda p_i-p_i')$. They are not imported from the particular
nonlinear uniform-time example in Event Memory and Coarse Aliasing §3.
For an arbitrary joint input put
$\rho^R_{ii}=\langle i|\rho_{AR}|i\rangle$; its failure CP density is
$[f_i(t)/p_i(a)]|f\rangle\langle f|\otimes\rho^R_{ii}$.
For (PR.61) the actual mode/time probabilities are $f_i(t)\,dt$.
Their total masses on the two legs are $1-a/b$ and $a/b-q$.
There are no atoms at the turn or terminal cut. Together with $q\rho_{AR}$
and the same seed, these formulas specify every successor.

**Proposition 20.2 (common preparation and unchanged original past).**
Fix once an auxiliary height $z\in(0,c)$ distinct from $a$. Starting
from the same positive preparation at $a$, use a unit fixed-height
phase leg of increment $2\pi m$, followed by the four-unit rectangle
at $z$ with phase height

$$
B_{\beta,m}
 =\frac{2c(\pi m-\beta)-2\pi ma}{z-a}.
\tag{PR.78}
$$

Append the selected programme (PR.75), then on survival the prescribed
one-unit horizontal leg $a\to l$. This is an actual common-source
construction for every real $\beta$ and signed $m$.

Proof. The first five units are Proposition 2.2 with $k=a$ and auxiliary
$z$. The signed weights (PR.2) give the real residual (PR.5)
coordinate by coordinate, so every state in (PR.61) is reached from the
same preparation. All its phase variation
$2\pi|m|+2|B_{\beta,m}|$ is finite, without a uniform bound over the
family. The new legs have matching heights and zero relative phase.
At each actual join of duration $T$, the composition supplier gives
$\chi(T+s)=\chi(T)+\chi_{\rm tail}(s)-\chi_{\rm tail}(0)$,
leaves the entire earlier prefix pointwise unchanged, and adds the
weighted integrals and real winding. Thus no old lift is passed to the
observer. Every selected control is positive and piecewise affine and
satisfies both original regularities.

If these first five units also use the canonical instrument, their actual
live mass is
$s_*(a,z)s_*(z,a)>0$, independent of $\beta,m$.
All preceding failures keep their original event and absorbing $f$.
Every yield measured from preparation is multiplied by this live mass;
no failure is retried to manufacture the stated initial cut. $\square$

**Resource statement 20.3 (finite parameters, margin and time).** For the
attainment at charge bound $C$, all its future acquisition heights lie
in $[a,b(\ell)]$. A common probability-support margin is
$\min\{a,c-b(\ell),Z\}>0$. Each programme has duration two, height
speed at most $d(\ell)$, height variation at most $2d(\ell)$,
and zero new phase variation. Its a.e. velocity has essential total
variation $2d(q)$ on the interior two-leg interval. If the velocity is
padded by zero before and after the excursion, the two exterior jumps
increase this to $4d(q)$. Joins to a nonzero earlier or later velocity
must instead count their actual velocity jumps. The tail has duration
one, speed $|l-a|$, height variation $|l-a|$, and margin
$\min\{a,l,c-a,c-l,Z\}$. These are future-stage costs, not bounds
on the arbitrary old phase history.

The charge frontier alone supplies no sharp time/precision tradeoff.
For example the two-unit construction has

$$
c-b(\ell)=\frac{c\ell(c-a)}{a+\ell(c-a)}\longrightarrow0
\quad\text{as }\ell\downarrow0.
\tag{PR.79}
$$

It attains vanishing error with a shrinking margin and unbounded charge,
not with every resource fixed. More generally, if every acquisition path
also has margin at least $\eta>0$, speed at most $v$, and duration at
most $T$, then
$\Lambda\leq\operatorname{TV}(k)/\eta\leq vT/\eta$.
Substituting this upper bound for $C$ in (PR.73) proves the necessary
condition $vT/\eta\geq\log((1-\delta)/\delta)$ for the stated error.
This condition is not asserted sharp in those extra resources.
Repeating a fixed interior excursion can increase charge without losing
its margin, but its time, height variation and velocity variation then
grow with the number of executed excursions.

The seed needs $\lceil\log_2|\mathcal U|\rceil$ classical storage bits
in a binary register; the attaining observer retains one bit. The source
separately retains its old parity bit, its received copy of the seed,
comparison/pending-programme state and the installed path parameters.
It also carries the old signed winding/phase programme. These source
registers and the seed delivery route are resources; they are not newly
acquired observer assistance. The active specimen has the credited live
qutrit representation and a stopped sector, while the seed, flags,
source/epoch tags, permissions, target, clock/reference, calibration,
controller and every actual archive are additional resources.

For rational $c,a,\ell,P,B$ in the allowed region, (PR.71) and (PR.75)
have finite rational descriptions; the exact charge is the specified
logarithm of a rational likelihood. General real frontier points require
their actual exact real constants, which need not have finite effective
descriptions. Old arbitrary $\beta,m$ have no uniform programme-width
bound. Calibrated preparation directions, prescribed waveform execution,
Kraus operations, blanks and exact time/mode recording remain the declared
ideal services. Finite symbolic description is not exact physical
execution at finite precision. No noisy-source certification, finite-time
clock implementation or approximation guarantee follows here.

## 21. Why informative live records do not improve the exact consumer

**Corollary 21.1 (credited rigidity on the acquired shared support).**
After any acquisition in Definition 17.1, allow a common finite endpoint
CP acceptance protocol using the specimen, actual live seed and
source-independent ancillary inputs. It may adapt using its own actually
retained records. There is no new accessible history-bearing assistance.
For every $\beta,m$, each accepted specimen must be exactly
$\psi_{l,\beta,m}$, with all success auxiliaries retained. Then its
unconditional success probability, measured from the initial live cut, is
at most

$$
s_*(a,l)\,Q_\varepsilon,\qquad
Q_\varepsilon=\sum_u\nu(u)q_\varepsilon(u),\qquad
s_*(a,l)=\min\left\{1,\frac al,\frac{c-a}{c-l}\right\}.
\tag{PR.80}
$$

The canonical monotone horizontal tail attains this simultaneously for
both parities and every phase, with its actual exact-time/five-mode
failure law. On the balanced frontier $Q_0=Q_1=P$, so the sharp
value is $s_*(a,l)P$ for each parity. No improvement in conditional
exact-tail success over $s_*(a,l)$ follows from its smaller $R_*$.

Proof. Every seed has positive live likelihood for both parities.
For fixed seed, correctness of the total accepted positive output
therefore forces its specimen marginal into the target ray for both
parities and every phase; a positive summand cannot hide an incorrect
output behind another seed. The effective endpoint success map selected
at this seed has no other history-bearing input.

Apply the credited Instrument Boundaries Theorem 4.1, or equivalently
Theorem 12.2 with classical equal-support assistance. For completeness,
the mechanism is that projecting a successful dilation onto any auxiliary
component gives a linear specimen map. The wedge with
$\sqrt Z e_2+e^{-i\beta}
(\sqrt{2l}U_++(-1)^m\sqrt{2(c-l)}U_-)$
has degree at most two in $e^{-i\beta}$. Its coefficients vanish.
The common nonzero reference direction $e_2$ fixes the same scalar for
both parities. Adding and subtracting the two bottom directions therefore
forces each component to be $\alpha_jD$, where
$D=\operatorname{diag}(\sqrt{l/a},\sqrt{(c-l)/(c-a)},1)$
on $(U_+,U_-,e_2)$. Completeness implies
$\sum_j|\alpha_j|^2D^\dagger D\leq I$, hence its accepted
probability is at most $\|D\|^{-2}=s_*(a,l)$.
Finite internal adaptivity induces a single such CP acceptance map;
its actual suboutcomes and auxiliaries are included in these components.

Multiply this bound by each actual $\nu(u)q_\varepsilon(u)$ and sum.
Old dead branches contribute zero because their successor is absorbing.
The canonical monotone tail has live operator $\sqrt{s_*}D$ on the
active family and the complete canonical failure kernels, proving
attainment with the same joint reference/archive preserved on success.
Its failed branches keep their new exact event; acquisition failures
keep the earlier event and never execute the tail. $\square$

The shared-support/no-improvement principle is the credited result of
§§12–14, now instantiated by an acquired live record with unequal
likelihoods. The added frontier does not rename that rigidity result as
new mathematics. Even without one common finite $C$, every individual
finite original return path has $q_\varepsilon(u)>0$; thus the same
no-exclusive-live-record argument and (PR.80) hold for this finite-seed
class. The quantitative error floor uses the common charge bound.

The permitted original menu after a live return is still the existing
prescribed relative-control menu at the actual matching height, with
both regularities, arbitrary finite durations including a matching
zero-duration identity, real increments and all permitted signed sectors.
For a relative height increment $a_\gamma(t)$ its domain remains
$D_\gamma=(\ell_b-\min a_\gamma,u_b-\max a_\gamma)$, as in the
probability-phase source §9.1. Known illegality or denied permission
gives an unexecuted visible rejection and retains the unchanged specimen
and request context; it is not a fabricated canonical failure. No detector
for an unflagged promise violation or unknown current height is supplied.
After an executed failure only the declared stopped continuation is
available. Updates retain the actual seed, request, outcome and archive,
never an inferred old lift as if it had been observed.

## 22. A rational one-retained-selector-bit instance

**Example 22.1 (informative survival with an exact continuation ceiling).**
Take zero fixed preparation phases and

$$
c=\frac14,\quad Z=\frac12,\quad
a=\frac18,\quad l=\frac3{16},\quad
\ell=\frac17,\quad C=\log7.
\tag{PR.81}
$$

Draw and retain a fair public bit $U$. If $U=\varepsilon$, the source
waits at $a$ for two units. If $U\ne\varepsilon$, it executes
$a\to7/32\to a$, one unit per affine leg and constant relative phase.
This selection is made by the source's explicitly retained old parity
bit and delivered seed; the observer sees neither that bit nor the path.
Here $b=7/32$, $d=3/32$ and $A=1/56$ in (PR.75)–(PR.77).
The loop's upward and downward survival factors are $4/7$ and $1/4$,
so its complete live return is $I_5/\sqrt7$.

The loop's total first-failure mass on each leg is $3/7$.
Its upward mode masses, in the original five-mode order, are
$(0,3/28,3/14,3/28,0)$; its downward masses are
$(3/28,0,3/14,0,3/28)$. Their exact time densities are (PR.77);
their joint reference successors are (PR.66). Waiting has no failure.
Thus the full output is the actual live joint state or the actual
$(U,\tau,i,f)$, with no discarded or repeated failure. Every failure
reveals $\varepsilon=1-U$ in this particular source, but its specimen
is already stopped.

For each parity separately,

$$
Q_\varepsilon=\frac47,\qquad
\Pr(\mathsf L,d(U)\ne\varepsilon)=\frac1{14},\qquad
\Pr(d(U)\ne\varepsilon\mid\mathsf L)=\frac18,
\quad d(U)=U.
\tag{PR.82}
$$

Under the equal prior, $U$ is initially independent of the old history.
The live flag alone carries no parity information because both yields
are $4/7$. Jointly, however,
$\Pr(U=\varepsilon\mid\mathsf L)=7/8$.
Erasing $U$ and retaining only the live flag and common metadata restores
error $1/2$. Within this balanced classical-record-only calibration
contract, a one-valued live record always has error $1/2$; at least
two retained values are necessary for this nontrivial error, and the
one retained bit is sufficient. This is not a lower bound for every
quantum calibration procedure or the whole observer memory.

The next one-unit horizontal leg has
$s_*(a,l)=2/3$. Corollary 21.1 gives the sharp unconditional exact
endpoint probability

$$
\frac23\frac47=\frac8{21}.
\tag{PR.83}
$$

Its remaining probability consists of acquisition failure $3/7$ and
new tail failure $4/21$, with the first actual time/mode preserved.
This is a complete stopped same-specimen construction.

For a fully specified common preparation use $z=1/16$ in (PR.78).
Then $B_{\beta,m}=8\beta-4\pi m$, the prehistory duration is five,
and its canonical live mass is $1/3$ for every $\beta,m$.
From that earlier preparation the final all-success probability is
$8/63$ and the full successful chronology lasts eight units.
The earlier failures remain absorbing. Every signed winding is allowed;
no old-history programme parameter is supplied to the later observer.

Acquisition alone has support margin at least $1/32$, maximum height
speed $3/32$, height variation $3/16$, and interior velocity variation
$3/16$; zero-padded velocity variation is $3/8$. Its duration is two
and its additional phase variation and winding are zero. The tail has
speed $1/16$, height variation $1/16$, duration one and margin at
least $1/16$. The common-preparation history has height margin at least
$1/16$, height speed at most $1/16$, and phase variation
$2\pi|m|+2|8\beta-4\pi m|$. These bounds do not give a uniform
phase budget over all old histories.

All new height/time/probability parameters have finite rational
descriptions, and the active basis and endpoint filter have finite
algebraic descriptions. The exact loss charge is named by $\log7$;
it is not a newly observed real-valued meter reading. Exact calibration,
Kraus execution, source/epoch matching, clock/reference and exact
continuous-time archive storage remain separately charged ideal services.
In particular the retained one-bit live selector does not encode the
failed branch's real timestamp or the full archive.

## 23. Attribution, original interfaces and the remaining acquisition gap

**Source statement 23.1 (what is reused and what is added).**

| Supplier at the public revision of §17 | Precise use and boundary |
| --- | --- |
| [FiniteRectangleTransport](../../../D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Quantum/Fibers/FiniteRectangleTransport.scribe.cs) | Valid base, strict probabilities, signed phase weights, compatibility and actual rectangles; the Scribe's all-signed-sector/common-preparation application supplies the real lift construction. No sensor or physical actuator is inferred. |
| [OriginalControlComposition](../../../D5/S3/Quantum/Fibers/OriginalControlComposition.lean) and its [Scribe](../../../Blueprint/D5/S3/Quantum/Fibers/OriginalControlComposition.scribe.cs) | Original controls, both regularities, finite/zero durations, literal unchanged prefix, matching heights, translated real tail and additive weighted integrals. |
| [Instrument Boundaries](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md), §§4–5.2, 9–15, 17–22; this volume §§12–15 | Full phase/parity source, sharp $s_*$, scalar canonical loops, complete exact-time/five-mode CP kernels, shared-support continuation rigidity and finite joint composition are credited. Supplied programmable processors and the failure-only calibration example are not redelivered as acquisitions. |
| [Instrument Stability](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md); [Record Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_RECORD_ACQUISITION.md); [Sampled Instrument Certificates](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_SAMPLED_INSTRUMENT_CERTIFICATES.md) | Their marked-law metrics, regularity conditions, query limits and conditional sampler/certification contracts remain. A Bayes parity score supplies none of their missing strong error data or extra joint sensor law. |
| [Quantum Carrier Minimum](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md), §§1, 7–10; [Event Memory and Coarse Aliasing](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_EVENT_MEMORY_AND_COARSE_ALIASING.md), §§2–6 | Live carrier and correlated-archive upper correspondence, separately scoped unassisted lower bounds, known-anchor labels, received commands and same-event timestamp costs retain their different contracts. The one selector bit is not a full archive minimum. |
| [Reanchoring Boundaries](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_REANCHORING_BOUNDARIES.md), §§2–7 | Unknown-height reanchoring remains distinct. The known return height here is a promised source invariant, not a newly acquired unknown-height guard. |
| [Transport–Memory Completion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §§2.9–2.12/2.18; [Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §34; [Atlas Stable Core Holonomy](RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md), Theorem 6.3 | Actual common coherent source/port, aligned acquired readings, known nonzero amplitudes and overlap, one source/epoch running image and complete compatible selection/update routes remain required. No individual four-view recovery map is constructed here. |

The source-specific addition is (PR.68)–(PR.74), its actual path
attainment, complete joint successor and retained-selector example.
Binary likelihood decisions, survival filtering and CP calculus are
mature mathematics. The shared-support exact-continuation ceiling is
explicitly reused. This is a repository-derived synthesis, with no
worldwide priority claim.

**Literature statement 23.2 (likelihoods and operational scope).**

| Primary reference | Verified content and use |
| --- | --- |
| S. Gammelmark and K. Mølmer, [Bayesian parameter inference from continuously monitored quantum systems, arXiv:1212.5700v1](https://arxiv.org/html/1212.5700v1), Eqs. (12)–(13) and the jump/counting model | An unnormalized conditional state's trace gives the likelihood relative to a chosen reference measure for a specified instrument. Clicks and no-click evolution both enter. This is mature motivation; (PR.64)–(PR.70) instantiate the actual original CP probabilities directly. The paper supplies no original sensor or black-box calibration certificate. |
| L. Leppäjärvi and M. Sedlák, [Incompatibility of quantum instruments, arXiv:2212.11225v2](https://arxiv.org/html/2212.11225v2), Proposition 7 | The stated compatibility condition is equivalent to postprocessing a complementary instrument from a chosen dilation. No complementary/environment port or implementing postprocessor is granted by that equivalence. None is used here. |
| [Classical Sufficiency in Quantum Statistical Experiments, arXiv:2609.29348v1](https://arxiv.org/html/2609.29348v1), §3.4.2, Definition 7 and comparison with restricted-measurement sufficiency | Recovery of the quantum experiment by one channel is stronger than preservation of the declared classical experiments of a restricted measurement class. No inference from this binary score to full original future-law recovery is made. |

These primary-source comparisons do not provide a directly sufficient
joint acquired original observer under the present absorbing, single-
specimen contract. This bounded comparison is neither an absence theorem
nor an originality argument.

**Boundary 23.3 (what the promised source still does not acquire).**
The positive construction obtains its live record in one actual execution,
but its information uses the extra source-side correlation between old
parity and future programme. It does not obtain, authenticate or implement
that correlation from an arbitrary unknown original past. Removing that
promise removes the displayed acquisition route. Treating a finite-error
guess as an exact parity input also violates the exact consumer: both
parities remain possible on every finite-charge live record.

No arbitrary-history height/domain, waveform, real phase, signed winding,
helper overlap, calibration or reference acquisition is supplied. Richer
observations, phase-dependent or unequal-support assistance and other
lawful acquisition designs are not excluded. A complete-output distance,
approximate continuation, all-prefix feedback theorem, unbounded-horizon
guarantee, finite physical clock or finite-precision implementation does
not follow from the score. The whole original positive-control class,
both regularities, arbitrary finite durations and all signed sectors
retain their original scope; this finite zero-phase return class is a
restricted partial result.

The remaining programme requires actual same-source acquisition and
retention of every domain, calibration, clock/reference, archive,
permission, selector and update input needed by the full legal future
menu, with all rejections and absorbing failure successors in one actual
running image. Full space/time/boundary/memory mutual recovery, native
stationary $\alpha/\beta$ memory rate and effective certification, and
the separate fixed-Hamiltonian quantum minimax remain unresolved here.
No source/action/observation/resource bridge to the preparer/reader,
static arithmetic, mixed-state, lattice or two-clock models is supplied.

## 追加锚（本行以下为增补区）
