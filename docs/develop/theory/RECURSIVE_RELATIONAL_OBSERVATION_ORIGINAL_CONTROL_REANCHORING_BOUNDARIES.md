# Recursive relational observation: original-control reanchoring boundaries

> **Machine contract.** This is a `generic-v1` reference volume. Its locators
> are determined from its own bytes. Merged text and append anchors are
> preserved; corrections and extensions belong after the terminal append
> anchor. Mathematical exposition supplies reference input, not machine state.

## 1. Scope, evidence and the matching-height consumer

This volume concerns an open cut at an uncertain current height. A controller
wants to reach one height selected from its actually retained record, while
preserving the specimen's unknown phase. Three possible heights on one
phase-independent record prohibit every nonzero exact success, even with
arbitrary height-independent parity assistance. With a separately supplied
exact parity label, two possible heights instead have a sharp positive
endpoint success bound. A finite classical record has a corresponding
support-capacity restriction. Nine actual original-control histories realize
the obstruction with a common finite noisy record.

The proofs are ordinary finite-dimensional mathematics and elementary
calculus. This volume supplies no new Lean evidence, physical actuator or
sensor. The positive source, signed rectangle synthesis, chronological joins,
canonical instrument, known-height rigidity and helper transport are credited
suppliers. The new deductions concern simultaneous uncertain-height
reanchoring on their actual source.

All repository readings and source links select the public revision
`773d4d43b91abd515be1059283d79dd6572fc174`. The mathematical authorship is
one Codex CLI author's synthesis of those public suppliers and the cited
primary literature. No independent-review claim is made.

**Convention 1.1 (two operation contracts).** The upper bounds allow any
common trace-nonincreasing CP endpoint operation on the stated accessible
joint input. Every finite adaptive quantum protocol with a recorded success
event induces such an operation. Success must have the exact requested pure
specimen marginal; all its actual auxiliary outputs can be retained.

The attaining operations are additional calibrated endpoint instruments,
with their own success/failure flags, retained failure residues and absorbing
stopped specimen. They are not the canonical exact-time, five-original-mode
instrument (OC.19)–(OC.19b) of
[Instrument Boundaries](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md).
Endpoint feasibility neither reproduces that instrument's failure law nor
implements its intervening successful path. Conversely an implementation of
that stricter task would have to satisfy its endpoint requirement, so an
endpoint impossibility also obstructs that implementation under the same
input restrictions.

The concrete consumer is the interface before a later original tail based at
a declared height. An original tail has an actual matching initial height;
a noisy estimate supplies no equality certificate for that guard.
The exact return guarantee in
[Sampled Instrument Certificates](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_SAMPLED_INSTRUMENT_CERTIFICATES.md),
Definition 2.1 and Proposition 8.4, is a generator promise that supplies such
a match. The present question concerns a cut without that promise. It does
not replace the original task by a known-height task or refute that supplier.

## 2. Original source, real lifts and all accessible inputs

**Definition 2.1 (positive source and the double-wall restriction).** For an
original valid base $b=(X,Y,Z)$ put $r=1-Z$. Thus
$0<Z<1$, $0<X,Y<r$, and

$$
\begin{aligned}
J(b)&=(\max(0,X+Y-r),\min(X,Y)),\\
p_b(x)&=(r-X-Y+x,X-x,Z,Y-x,x),\\
d&=(1,-1,0,-1,1),\\
I_b(x)&=p_0(x)^{-1}+p_1(x)^{-1}+p_3(x)^{-1}+p_4(x)^{-1},\\
w_b(x)_i&=d_i/(p_b(x)_i I_b(x)).
\end{aligned}
\tag{RB.1}
$$

The mode order is $(0,1,2,3,13)$, with index $4$ denoting mode $13$.
An original control has finite duration $T\geq0$, continuous real
$k,\chi$ on $[0,T]$, strict $k(t)\in J(b)$, finite variation of $\chi$,
and either absolute continuity of both coordinates or the supplied finite
piecewise $C^1$ regularity with continuous rates on each closed piece.
The latter implies absolute continuity by finite integration and
telescoping. Its real residual is
$H_i(t)=\int_0^t w_b(k(u))_i\chi'(u)\,du$.
These are the definitions in `FiniteRectangleTransport` and
`OriginalControlComposition`; they grant no waveform read port.

The new results restrict to

$$
X=Y=c=r/2,\qquad 0<x<c,\qquad
p(x)=(x,c-x,Z,c-x,x),
\qquad
w(x)=\left(\frac12-\frac{x}{r},-\frac{x}{r},0,
                    -\frac{x}{r},\frac12-\frac{x}{r}\right).
\tag{RB.2}
$$

No off-wall generalization is asserted. Fix a common positive preparation
and calibrated preparation phases $\theta_i$ where actually supplied, with
$\theta_2=0$. Let

$$
\begin{aligned}
e&=e_2,\\
U_+&=(e^{-i\theta_0}e_0+e^{-i\theta_4}e_4)/\sqrt2,\\
U_-&=(e^{-i\theta_1}e_1+e^{-i\theta_3}e_3)/\sqrt2,\\
\mathcal B&=\operatorname{span}_{\mathbb C}\{U_+,U_-\},\qquad
\mathcal V=\mathbb Ce\oplus\mathcal B,\\
n_s(x)&=\sqrt{x/c}\,U_++s\sqrt{1-x/c}\,U_-,\\
\psi(x,z,m)&=\sqrt Z\,e+z\sqrt r\,n_{(-1)^m}(x),
\qquad |z|=1,\quad m\in\mathbb Z.
\end{aligned}
\tag{RB.3}
$$

The displayed directions are orthonormal and all these specimen vectors
have norm one. Inner products are conjugate linear in the first argument.
Writing $z=e^{-i\beta}$, the real residual is

$$
(\beta,\beta-\pi m,0,\beta-\pi m,\beta).
\tag{RB.4}
$$

The specimen sees parity, but the actual source keeps every signed integer
$m$ and its real lift.

**Proposition 2.2 (credited synthesis with one common preparation).** Fix
$a,q\in(0,c)$ with $a\ne q$ before choosing $x,\beta,m$. From the
preparation at height $a$, prepend a unit-time fixed-height phase leg of
increment $2\pi m$. Follow it by the supplied four unit-leg rectangle
from $a$ to $q$, of signed phase height

$$
B_{\beta,m}=\frac{r(\pi m-\beta)-2\pi m a}{q-a}.
\tag{RB.5}
$$

Finally append a unit horizontal zero-relative-phase leg from $a$ to $x$.
This actual six-unit history ends in (RB.3)–(RB.4). It obeys both original
regularity alternatives. For any finite candidate set of strict heights it
has a common positive probability margin. Its phase variation is
$2\pi|m|+2|B_{\beta,m}|$, finite for each real $\beta$ and signed $m$.

Proof. The rectangle residual from `finite_rectangles_realize` is
$B(w(q)-w(a))$, while the fixed-height leg contributes $2\pi m w(a)$.
Since

$$
w(q)-w(a)=-\frac{q-a}{r}(1,1,0,1,1),
$$

substitution gives (RB.4), coordinate by coordinate. The rectangle has zero
real phase increment. The horizontal leg has $\chi'=0$, so keeps the
entire residual. All controls are continuous with finitely many affine
pieces. Their heights stay between the finitely many strict heights
$a,q,x$, proving strict support and the stated regularity and variation.
`concatenate_original` preserves the literal prefix, translates the tail's
real lift at the actual join, and adds the weighted integrals. This is the
all-sector application in the owning Scribe, reused with its original
signs. No fixed variation budget contains every signed integer. $\square$

**Definition 2.3 (classical record and joint assistance contract).** Fix
distinct candidate current heights $x_1,\ldots,x_M\in(0,c)$, with
$1\leq M<\infty$. The same statements on any finite subset apply to a
larger height family. An actually delivered finite or countable classical
record $Y$ has law $Q_j(y)$ on height $x_j$, independent of $z,m$.
Write

$$
S_y=\{j:Q_j(y)>0\}.
\tag{RB.6}
$$

Conditional on the actual $j,z,m,y$, the entire input accessible to the
processor is exactly

$$
|\psi(x_j,z,m)\rangle\langle\psi(x_j,z,m)|\otimes\tau_{m,y}.
\tag{RB.7}
$$

Here $\tau_{m,y}$ is a normal density operator on the joint assistance
register, independent of $j,z$. It can include any calibrated parity
helper, arbitrarily large fixed blanks, controller systems and even a
perfectly readable parity label. Allowing dependence on the whole signed
$m$, rather than only its parity, also leaves the upper bounds valid.
There is no dimension bound on this assistance in the upper bound.

Every accessible source-bearing classical field is included in $y$ or
explicitly in this assistance contract. All accessible quantum assistance
is included jointly in $\tau_{m,y}$. This includes readable archives,
source and epoch labels, generator/programme descriptions, clock latches,
calibration, references, permissions, controller state, selection inputs,
returned environments, shared-resource registers and bypasses. Independence
of their separate marginals is insufficient: (RB.7) is the joint premise.
A height- or phase-correlated accessible extra token changes the problem.

An inaccessible spectator reference can remain correlated with the actual
history and assistance. The gate acts by identity on it. Since the specimen
is pure conditional on history, it factors from every other register there;
this does not assert that assistance and spectator factor from one another.
No accessible purification of a mixed archive is granted.

**Definition 2.4 (record-selected exact reanchoring).** Using only the
declared accessible inputs, the controller selects a target
$l_y\in(0,c)$ and a proposed finite positive endpoint duration $L_y$.
For every $j\in S_y$, every $|z|=1$ and every signed $m$, the success
specimen must be exactly $\psi(l_y,z,m)$ whenever success has positive
probability. Zero success is allowed, but an incorrect live output is not
called success. The controller has no hidden $j,z,m$ input.

The common success map for each $y$ is CP and trace-nonincreasing on the
joint specimen/assistance input. It may retain arbitrary success auxiliaries
and use any finite adaptive processing. Unknown parameters cannot be passed
to its intermediate selectors. The upper bound even grants exact parity
classically to the processor for free; that is an explicit strengthening
for impossibility, not a record-acquisition construction.

This endpoint task specifies no Hamiltonian, speed or all-prefix gate law
over $L_y$. An attaining abstract CP map does not by itself supply a timed
physical implementation. A permitted executed attempt has success or a
stopped specimen $f$ with its complete actual failure residue and record.
Failure is absorbing. A known mismatch or missing permission gives an
unexecuted visible rejection instead. The joint input promise is not an
algorithm detecting every unflagged promise violation. There is no fresh
specimen, reset, retry after failure or additional source port.

## 3. Phase rigidity and the three-height obstruction

**Lemma 3.1 (three phases fix each successful linear component).** Fix
$0<x,l<c$, a sign $s$ and three distinct complex numbers
$z_1,z_2,z_3$ on the unit circle. Let $K:\mathcal V\to\mathbb C^5$
be linear. If for each of these phases

$$
K(\sqrt Z e+z\sqrt r n_s(x))
\in\mathbb C(\sqrt Z e+z\sqrt r n_s(l)),
\tag{RB.8}
$$

including zero images, then one $\lambda\in\mathbb C$ satisfies

$$
Ke=\lambda e,\qquad Kn_s(x)=\lambda n_s(l).
\tag{RB.9}
$$

Proof. Wedge the image with its required target. The result is a
vector-valued polynomial of degree at most two in $z$ with three distinct
zeros. In any basis all scalar coefficients therefore vanish. The constant
term says $Ke\wedge e=0$, so $Ke=\lambda e$. The quadratic term says
$Kn_s(x)=\nu n_s(l)$. The linear coefficient is then
$\sqrt{Zr}(\lambda-\nu)e\wedge n_s(l)$. Both amplitudes are nonzero
and the two directions are independent, so $\nu=\lambda$. This is the
phase-rigidity argument of Parity Record Transport Lemma 4.1, applied to
the present uncertain-height input. It requires no phase estimate or
covariance assumption. $\square$

**Lemma 3.2 (retained auxiliaries and mixed assistance do not evade
rigidity).** Fix $m,y$. Any success map in Definition 2.4 induces a
trace-nonincreasing CP map from $M(\mathcal V)$ to the specimen matrices
by appending the fixed $\tau_{m,y}$ and tracing its actual successful
auxiliary outputs. Choose Kraus operators $K_\alpha$ for this induced
finite-input, finite-output map. For every $j\in S_y$,

$$
K_\alpha e=\lambda_\alpha e,\qquad
K_\alpha n_{(-1)^m}(x_j)=\lambda_\alpha n_{(-1)^m}(l_y).
\tag{RB.10}
$$

The scalar $\lambda_\alpha$ is common to all these $j$. Thus the branch
success probability is
$p_{m,y}=\sum_\alpha|\lambda_\alpha|^2$, independent of $z$ and of the
actual candidate $j$ within this record.

Proof. A positive sum of rank-one Kraus outputs with a pure specimen
marginal can have no summand outside that specimen ray: its expectation
on any perpendicular vector is a sum of nonnegative numbers equal to
zero. This applies also when the whole sum is zero. Apply Lemma 3.1 to
each $K_\alpha$ and each $j$. The image of the common vector $e$ makes
the scalar common across $j$. On every promised normalized input the
Kraus image is consequently $\lambda_\alpha\psi(l_y,z,m)$; summing
norms proves the probability formula.

Appending a fixed normal state and tracing outputs is CP even for an
unrestricted assistance Hilbert space; the induced map has finite-dimensional
input and output and therefore a finite Kraus representation. Any actual
retained success residue is still present in the original map. A zero
positive specimen marginal has zero total trace and hence zero joint
successful output. Discarding auxiliaries in this necessity argument cannot
hide a nonzero retained success. $\square$

**Theorem 3.3 (three-height exact obstruction with all height-independent
assistance).** Under Definitions 2.3–2.4, if $|S_y|\geq3$, then
$p_{m,y}=0$ on every promised input at this record, for every signed $m$.
This holds with arbitrary assistance satisfying (RB.7), even if exact
parity is additionally revealed. For each fixed $m$ it already holds if
exactness is required only at the same three distinct phases for each of
three distinct heights.

Proof. Fix $m,y$ and one successful $K_\alpha$. In the real coordinates
$(U_+,sU_-)$, $s=(-1)^m$, the vectors $n_s(x)$ lie on the open
positive quadrant of the unit circle. Any three distinct such points are
affinely independent: a real affine line intersects a circle in at most
two points. For three candidate indices $a,b,d$, therefore,

$$
n_s(x_b)-n_s(x_a),\qquad n_s(x_d)-n_s(x_a)
\tag{RB.11}
$$

are independent over $\mathbb R$ and, since their coordinate matrix is
real with nonzero determinant, over $\mathbb C$. They span $\mathcal B$.
Equation (RB.10) sends both differences to zero. Thus $K_\alpha$ is zero
on $\mathcal B$. Applying it to $n_s(x_a)$ now gives
$0=\lambda_\alpha n_s(l_y)$, so $\lambda_\alpha=0$ and $K_\alpha e=0$.
Every successful Kraus component vanishes on all of $\mathcal V$.
Lemma 3.2 proves zero success, including every retained auxiliary output.
Granting a classical parity label only makes the allowed map more general;
the argument fixed that label from the outset. $\square$

This is not indistinguishability of the three specimen density matrices.
They are distinct quantum inputs. The obstruction is to one exact
phase-preserving action on all of them using the stated common record.
It does not prohibit other measurements, other targets, or height-dependent
assistance under a different joint source relation.

## 4. The sharp two-height endpoint bound and complete attainment

**Theorem 4.1 (sharp known-parity branch bound).** Fix a nonempty record
support $S_y$, its target $l_y$, and suppose an exact parity label is
separately supplied to a calibrated endpoint processor. Define

$$
\kappa(S)=
\begin{cases}
1,&|S|=1,\\[2pt]
\dfrac{1+g_{ab}}2,&S=\{a,b\},\\[4pt]
0,&|S|\geq3,
\end{cases}
\qquad
g_{ab}=\frac{\sqrt{x_ax_b}+\sqrt{(c-x_a)(c-x_b)}}c.
\tag{RB.12}
$$

For a pair of distinct heights, $0<g_{ab}<1$. The maximum exact branch
success probability is $\kappa(S_y)$, independent of the unknown phase,
the actual candidate within the support, and the selected strict target.
These optima are attainable simultaneously for every record with complete
endpoint instruments and absorbing retained failure. For arbitrary
height-independent assistance without a readable parity label,
$\kappa(S_y)$ remains an upper bound; its attainment is not asserted.

Proof. Theorem 3.3 covers three or more candidates. For a singleton, the
two orthonormal assignments $e\mapsto e$ and
$n_s(x_j)\mapsto n_s(l_y)$ extend to a unitary, giving probability one.

For a pair put $u=n_s(x_a)$, $v=n_s(x_b)$, $n=n_s(l_y)$ and
$g=\langle u,v\rangle=g_{ab}$. Distinct heights give independent
$u,v$; their positive coordinates give $0<g<1$. The unique vector
$w\in\mathcal B$ with $\langle w,u\rangle=\langle w,v\rangle=1$ is

$$
w=\frac{u+v}{1+g},\qquad \|w\|^2=\frac2{1+g}.
\tag{RB.13}
$$

Lemma 3.2 forces every successful component to equal
$\lambda_\alpha A$ on $\mathcal V$, where

$$
Ae=e,\qquad A|_{\mathcal B}=|n\rangle\langle w|.
\tag{RB.14}
$$

The output reference and bottom directions are orthogonal. Consequently
$A^\dagger A$ is $1$ on $\mathbb Ce$ and
$|w\rangle\langle w|$ on $\mathcal B$. If
$p=\sum_\alpha|\lambda_\alpha|^2$, trace nonincrease gives
$pA^\dagger A\leq I$. Its largest eigenvalue is $2/(1+g)$, so

$$
p\leq\frac{1+g}2.
\tag{RB.15}
$$

For attainment take $p=(1+g)/2$ and $C_s=\sqrt p\,A$, extending it
by zero on the two inactive original directions. Then
$C_s\psi(x_j,z,m)=\sqrt p\,\psi(l_y,z,m)$ for both candidates of
that parity, and $C_s$ is a contraction. With
$F_s=(I-C_s^\dagger C_s)^{1/2}$, the map

$$
\zeta\longmapsto
(C_s\zeta)_{\mathsf s}\ \oplus\ (f\otimes F_s\zeta)_{\mathsf f}
\tag{RB.16}
$$

is an isometry. Reading the flag gives a complete instrument; the entire
$F_s\zeta$ is retained as failure residue. The separately supplied parity
label controls $C_s,F_s$. A singleton uses its unitary and zero failure
on the promised input; three or more candidates can use $C_s=0$ and
retain the input as stopped failure residue. Selecting these constructions
by the actual $y$ attains every branch bound at once. All outputs keep
the old record and actual auxiliary registers. $\square$

The optimal success residue for a pair cannot carry the unknown phase or
candidate label in any projected component, by (RB.10). Failure residues
can carry both. The theorem places no unchanged-return requirement on the
helper on failure. Its failure flag is its own endpoint flag, not an
invented canonical first-time/mode readout.

**Proposition 4.2 (a supplied nonidentical parity pair serves two heights).**
Suppose the assistance is the supplied calibrated pure pair
$\eta_s$, with $\langle\eta_+,\eta_-\rangle=\mu\in[0,1)$, independent
of height and unknown phase, and coherent access and the endpoint service
are permitted. On a two-height branch the common exact success probability

$$
(1-\mu)\frac{1+g_{ab}}2>0
\tag{RB.17}
$$

is attainable. This is a lower bound for that helper contract, not a claim
of its optimum. No such height-independent pair can serve a three-height
branch with positive exact success under (RB.7).

Proof. Unambiguously discriminate the helper by a conclusive contraction
$\eta_s\mapsto\sqrt{1-\mu}\,|s\rangle$. The input Gram matrix minus
the conclusive Gram matrix is
$\mu\left(\begin{smallmatrix}1&1\\1&1\end{smallmatrix}\right)\geq0$.
Thus it has a complete isometric realization with a common inconclusive
helper vector of norm $\sqrt\mu$. This is the mature two-state
unambiguous-discrimination construction, not acquisition of a helper.
On a conclusive label apply Theorem 4.1's pair filter. Retain the label and
every residue. On inconclusive helper readout, or filter failure, stop the
specimen and keep its actual quantum residue and the failed stage label.
The resulting complete instrument has success probability (RB.17) on
both parities and heights. Theorem 3.3 proves the final assertion.
For $\mu=1$ the helpers coincide and this construction gives no conclusive
branch. $\square$

**Corollary 4.3 (unassisted two-height contrast, using credited rigidity).**
If all auxiliary inputs at a fixed $y$ are identical across phase and
parity, every record shared by two distinct candidate heights has zero
exact success on the full unknown phase/parity family.

Proof. Fold those fixed auxiliaries into the success map. Instrument
Boundaries Theorem 4.1 forces each successful component at height $x_j$
to be $\lambda_jD_{x_j,l_y}$, where
$D_{x_j,l_y}e=e$ and
$D_{x_j,l_y}U_+=\sqrt{l_y/x_j}\,U_+$. The common $e$ forces the
same $\lambda$ at both heights. If it were nonzero, their $U_+$ images
would give $\sqrt{l_y/x_a}=\sqrt{l_y/x_b}$, impossible for distinct
strict heights. All success amplitudes vanish. This is an application of
the credited known-height rigidity, rather than a new no-imprinting result.
$\square$

## 5. Finite classical-record support capacity

**Theorem 5.1 (averaged bound on the actual record).** Under
Definitions 2.3–2.4, let $p_j(m)$ be the probability of exact reanchoring
success from height $x_j$, including the actually delivered record. Then
for every signed $m$,

$$
p_j(m)\leq\sum_{y:Q_j(y)>0}Q_j(y)\kappa(S_y).
\tag{RB.18}
$$

In the enlarged calibrated endpoint contract with a separately supplied
exact parity label, equality holds for every $j,m$ simultaneously.
It is an upper bound without an attainment assertion for the stricter
canonical complete-instrument task.

Proof. Conditional on each positive-probability actual $y$, Lemma 3.2
gives the common branch probability and Theorems 3.3–4.1 bound it by
$\kappa(S_y)$. Multiply by that same source's $Q_j(y)$ and sum.
No product of independently chosen record and specimen marginals is used.
The common record-controlled endpoint construction attains each summand
when the exact parity label is supplied. $\square$

**Corollary 5.2 (finite classical capacity with assistance separately
specified).** If the accessible classical record in Definition 2.3 has
at most $A<\infty$ possible values, positive exact success at all $M$
distinct candidate heights requires

$$
A\geq\lceil M/2\rceil.
\tag{RB.19}
$$

Under the uniform prior on those heights, for each fixed signed $m$,

$$
\frac1M\sum_{j=1}^M p_j(m)\leq\min(1,2A/M).
\tag{RB.20}
$$

A $B$-bit bound on that entire accessible classical record consequently
requires $2^B\geq\lceil M/2\rceil$ for positive success everywhere.
With no parity assistance as in Corollary 4.3, replace the necessary
$A$ by $M$, and the average upper bound by $\min(1,A/M)$.

Proof. Only records whose support has at most two heights can contribute
positive success. Their union contains at most $2A$ heights. Each height
with positive success belongs to that union, proving (RB.19). Each
$p_j(m)\leq1$, and heights outside the union have probability zero,
which proves (RB.20). The bit inequality is cardinality. Without parity
assistance, only singleton supports contribute, by Corollary 4.3.
$\square$

The integer threshold in (RB.19) is attained for the task with an already
known fixed parity by partitioning the height list into pairs and a possible
singleton, recording the part, and using Theorem 4.1. With both parities
unknown, a supplied calibrated orthogonal quantum parity token also permits
the same $A$-value height record and coherent control by its two supports.
That token is an extra two-dimensional quantum resource. If parity is
instead delivered as an actual classical bit, its alphabet must also be
charged: the part-plus-parity record has up to $2\lceil M/2\rceil$
values. The free parity grant in the upper bound is not a free real bit
in a claimed total-memory construction. The average bound (RB.20) is a
universal estimate, without a claim of a sharp constant for each prescribed
height list; distinct paired heights have $\kappa<1$.

All readable classical calibration, programme, clock, archive and selector
fields count in the actual alphabet. Fixed fields add no alternatives but
still require descriptions and storage. A separate source-bearing quantum
register cannot be ignored: it must meet the height/phase independence in
(RB.7), or the theorem's premise fails. These are classical-alphabet
bounds with specified assistance, not a bound on total Hilbert dimension,
physical memory or an entanglement-assisted encoding problem. They are not
multiplied by the distinct event-memory bound of Event Memory and Coarse
Aliasing.

**Corollary 5.3 (countable-record boundary).** Under the same independence
and exactness premises, a countable classical record can give positive
exact success at at most countably many distinct heights, even with
height-independent assistance and free parity for the upper bound.

Proof. Every contributing record has support containing at most two
heights, by Theorem 3.3 on any three of its candidates. A countable union
of such finite supports is countable. Positive success at a height
requires membership in one of those supports. $\square$

This concerns positive exact success on every promised phase at a height.
It gives no finite-noise lower bound, no uniform lower bound on success
over an infinite class, and no necessity of literal height identification
for every possible operation. Two-height reanchoring already shows that
exact height identification is not necessary for this endpoint consumer
when the stated parity resource is supplied.

## 6. Nine actual histories with one finite noisy current record

**Theorem 6.1 (a realized source and current-epoch record).** Set

$$
b=(1/4,1/4,1/2),\qquad c=1/4,\quad r=1/2,\quad
a=1/8,\quad q=1/16,\quad \varepsilon=1/64,
\qquad x_-=7/64,\quad x_0=8/64,\quad x_+=9/64.
\tag{RB.21}
$$

Use the same fixed positive preparation, for example $\theta_i=0$ for
all modes. Select the nine histories with

$$
m=0,\qquad \beta\in\{0,2\pi/3,4\pi/3\},\qquad
x\in\{x_-,x_0,x_+\}.
\tag{RB.22}
$$

Prepare the first five units by Proposition 2.2, for which $B=8\beta$,
then use the final unit horizontal leg $a\to x$. They share the source,
preparation, base, clock and permissions. Each satisfies both original
regularity alternatives, with the common finite resource bounds

$$
\min_{t,i}p_i(k(t))\geq1/16,\qquad
\|k'\|_\infty\leq1/16,\qquad
\operatorname{TV}(k')\leq17/64,\qquad
\operatorname{TV}(\chi)\leq64\pi/3.
\tag{RB.23}
$$

Variation of the piecewise constant height velocity is on the open
six-unit interval, with one-sided endpoint traces and no added extension
by zero outside. Start the current recording epoch at time five. For any
fixed finite rational schedule $0=u_0<\cdots<u_N=1$, a recorder reports
the same nominal height $a$, relative phase zero and times $5+u_i$ on
all nine histories. Its pointwise height error is at most $\varepsilon$
and its relative-phase error is zero throughout this current leg. The
recorder can be the deterministic constant report under this promise,
so its joint operation is nondisturbing and independent of the specimen.

Nevertheless no common endpoint processor given only this current record
and any assistance satisfying (RB.7) has nonzero exact success in returning
all nine live inputs to height $a$ while preserving their phase, even when
$m=0$ is revealed for free.

Proof. The original six-unit height waveform has unit-leg velocities

$$
0,\ -1/16,\ 0,\ 1/16,\ 0,\ x-a.
\tag{RB.24}
$$

Every height lies in $[1/16,9/64]$, and every complementary height
$c-k$ is at least $7/64$. The middle probability is $1/2$, so the
support bound follows. The largest velocity magnitude is $1/16$.
The first four velocity jumps total $1/4$; the last is
$|x-a|\leq1/64$, giving $17/64$. The phase variation is
$2|B|=16|\beta|\leq64\pi/3$. Every path is finite piecewise affine.
The residual calculation (RB.5) yields precisely the promised phase
$z=e^{-i\beta}$ at height $x$.

On the last leg, $k(5+u)=a+(x-a)u$ and its real relative phase is
identically zero. Thus the constant report has the stated simultaneous
errors. Appending a fixed classical report to the actual input is exactly
a product operation, not an inference of nondisturbance from marginal
accuracy. Its bounded schedule, rational values and common metadata have
one finite description. It supplies no preinitial phase, past programme
archive or whole probability law.

The three selected $z$ values are distinct. All three heights share the
same current record and the same permitted assistance at fixed $m=0$.
The finite-phase version of Theorem 3.3 therefore applies to these nine
actual inputs and gives zero exact success. $\square$

The record in this theorem is deliberately uninformative but actually
pointwise correct within the displayed error. It is not claimed to sense
arbitrary original waveforms. Making its current sample grid arbitrarily
fine does not add information because the same constant bounded error is
permitted at every current time. A prehistory programme descriptor or an
actually acquired phase-bearing archive would be an additional accessible
input; it is not deleted if supplied. The theorem then needs its joint
premise checked again. All-sector Proposition 2.2 remains valid, while
the finite resource certificate (RB.23) selects only (RB.22).

**Proposition 6.2 (lawful individual tails and retained preparation failures).**
At the cut in Theorem 6.1, each individual actual original tail from $x_j$
back to $a$ with constant relative phase is legal for every finite duration
$L>0$. Its endpoint is $\psi(a,z,0)$. With current height supplied exactly,
the credited canonical instrument has survival probabilities

$$
7/8,\qquad 1,\qquad 7/8
\tag{RB.25}
$$

on the three respective tails. Under canonical execution of the preparation
and arrival paths, the five-unit prefix has survival $1/3$ and the live-cut
probabilities at time six are

$$
8/27,\qquad 1/3,\qquad 8/27.
\tag{RB.26}
$$

They are positive and independent of the chosen $\beta$. Earlier failures
keep their exact first time, original mode and absorbing successor $f$;
no failed specimen is reused.

Proof. For each candidate, take
$k_{\rm tail}(u)=x_j+(a-x_j)u/L$ and zero relative phase on $[0,L]$.
It stays in the strict fiber and has both regularity alternatives.
`concatenate_original` preserves the existing six-unit prefix and gives
the matching real-phase join, keeping its phase residual unchanged.
The middle case is an idle matching leg. Zero duration is legal only
for that matching identity, not an instantaneous nontrivial return.

On a monotone zero-phase leg the credited canonical survival is
$s_*(x,l)=\min\{1,x/l,(c-x)/(c-l)\}$. Substituting the three current
heights and $l=a$ gives (RB.25), independently of $L>0$.
The rectangle's descent $a\to q$ has survival $2/3$, and its return
$q\to a$ has survival $1/2$; constant-height phase legs have survival
one. This gives $1/3$. The arrival legs $a\to x_-$ and $a\to x_+$
each have survival $8/9$, while the middle idle leg has one. Composition
gives (RB.26). The canonical completion retains every earlier first-failure
time and original mode with absorbing $f$. Conditioning the reanchoring
task on an actual live cut does not create a specimen or supply a table:
these are the positive live branches of that complete execution. $\square$

The common live flag and clock coincide, although their source-dependent
probabilities need not coincide. Knowledge of the flag can change prior
weights, but all three heights still have positive support there. The
obstruction does not assert equality of those different arrival laws.

The request “return to $a$” is a proposed reanchoring macro, not an already
supplied primitive that reads its unknown starting height. Each tail in
Proposition 6.2 is individually a legal original waveform; choosing the
correct one still needs a source-bound relation. In particular, their
existence does not give one literal prescribed waveform with three
different initial heights. The impossibility grants the macro the larger
class of common CP endpoint attempts and still rules out its exact success.
It introduces no total legality-rejection oracle for arbitrary requests.

## 7. Successors, resource boundaries and approximation

**Convention 7.1 (the complete menu after an actual success).** The existing
original menu consists of separately permitted prescribed original controls
at the same base, with actual matching initial height, arbitrary finite
duration including zero, both regularity alternatives, real relative phase
increments and all signed sectors compatible with a stated resource promise.
After an endpoint success at $l_y$, a separately supplied tail based there
can act on the exact target specimen. All actual archives, references,
permissions, controller and selector/update inputs remain jointly present.
The real lift is joined as

$$
\chi(T+u)=\chi(T)+\chi_{\rm tail}(u)-\chi_{\rm tail}(0).
\tag{RB.27}
$$

This chronological identity applies to actual matching original controls;
it does not hand $\chi(T)$ to a controller. A tail after an added endpoint
operation belongs to that enlarged operation contract. Its endpoint matrix
alone does not establish that the old original history was continued along
an actual original reanchoring waveform.
Record-based selection occurs only after that record is actually obtained.
A rejected request is unexecuted and retains its visible rejection. A
canonical executed failure retains its original exact time/mode event and
absorbing $f$. An executed added endpoint failure retains that endpoint
instrument's actual flag, old record, helper changes and complete residue,
with the specimen stopped. There is no original positive-carrier retry
from either failure. Failure residue is not an unchanged returned helper.

For the positive constructions, identity on an untouched reference means
applying the displayed CP branch tensored with identity to the actual joint
state. For example, the failure joint state is formed with $F_s\otimes I_R$,
not by substituting an independently chosen reference marginal. Conditional
on each actual history the pure specimen factors from other systems; those
systems can retain their own correlations. Linearity then preserves the
actual mixture and its correlations with the new success/failure label.
Consuming a helper changes its correlations by the actual branch operation;
they are retained rather than claimed unchanged. No equality with the
canonical operation on arbitrary entangled inputs is inferred from pure
family endpoint conversion.

**Resource account 7.2 (conditional operations and finite descriptions).**
The upper bound allows unlimited height-independent assistance, exact
calibrated gates and blanks and even a free parity label. Its conclusion
therefore cannot be repaired solely by enlarging such assistance. A
height- or phase-dependent token, a sensor, or a new source port is a
different premise, with its own acquisition and complete update proof.

Theorem 4.1's attainment requires an installed calibrated candidate list,
the target, the original preparation directions, an exact supplied parity
label or equivalent orthogonal quantum control, the contraction and its
complement, permissions, output flags and failure-residue registers. On the
five-dimensional specimen input (RB.16) can retain a five-dimensional
failure residue; this is a sufficient register count, not a hardware minimum.
Proposition 4.2's helper must already be source-bound, calibrated and available
coherently. Knowledge of a numerical overlap alone does not supply its rays
or a gate, and this volume gives no helper-acquisition protocol.

For rational $Z,c,x_j,l_y$ and a fixed rational/algebraic description of
the preparation directions, the finite endpoint matrices use algebraic
numbers and matrix square roots and admit finite symbolic descriptions.
The rational source (RB.21) with $\theta=0$ has that property. Its three
phase factors in (RB.22) are algebraic; its actual controls additionally
use the finite symbol $\pi$. Arbitrary exact real calibration parameters
need not have finite effective descriptions. Finite symbolic description,
storage width, arithmetic certification, clock accuracy, gate execution
precision, waveform generation, preparation, acquisition work and physical
hardware are separate resources. No finite-accuracy implementation of an
exact gate or exact-time canonical recorder is deduced.

**Boundary 7.3 (exact versus approximate and finite versus unbounded).**
The obstruction and endpoint optima are exact. They do not establish an
approximate reanchoring lower bound. In fact, if $l=a$, the identity
channel on the specimen has the explicitly source-dependent trace-distance
error

$$
\frac12\left\|
|\psi(x,z,m)\rangle\langle\psi(x,z,m)|-
|\psi(a,z,m)\rangle\langle\psi(a,z,m)|\right\|_1
=\sqrt{1-(Z+r g(x,a))^2},
\quad
g(x,a)=\frac{\sqrt{xa}+\sqrt{(c-x)(c-a)}}c.
\tag{RB.28}
$$

The equality is the pure-state trace-distance formula and the direct inner
product from (RB.3). The error tends to zero as $x\to a$, uniformly in
$z,m$. The nine-history construction can use any sufficiently small
positive $\varepsilon$ in place of $1/64$, still with three distinct
heights and zero exact reanchoring probability. Thus zero exact success
does not imply a nonzero uniform approximate error floor. Identity's small
endpoint error neither returns the actual height exactly nor reproduces
the canonical tail's complete time/mode instrument.

No error in (RB.28) is substituted for Instrument Stability's complete
operational metric or Sampled Instrument Certificates' acquired strong
derivative and terminal-character data. No approximate full instrument,
finite-noise certificate, summable accumulation guarantee or unbounded
execution is constructed here. Countability in Corollary 5.3 is an exact
support argument, not a forever finite-state predictor theorem. The original
arbitrary finite-duration class and every signed winding remain intact;
the finite witness and conditional endpoint service are restricted consumers.

## 8. Suppliers, primary literature and remaining acquisition bridges

**Source map 8.1 (credited repository boundaries).** All following paths
refer to the public pin stated in §1. They identify reused mathematics and
interfaces, not a new build or certification of these ordinary proofs.

| Supplier | Exact use and boundary |
| --- | --- |
| [FiniteRectangleTransport](https://github.com/the-omega-institute/trureturing/blob/773d4d43b91abd515be1059283d79dd6572fc174/D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean) and [owning Scribe](https://github.com/the-omega-institute/trureturing/blob/773d4d43b91abd515be1059283d79dd6572fc174/Blueprint/D5/S3/Quantum/Fibers/FiniteRectangleTransport.scribe.cs) | `ValidBase`, signed `phaseWeight`, strict `probability`, `weight_compatible` and `finite_rectangles_realize`. The Scribe's all-sector application supplies the fixed-height winding leg and (RB.5); the rectangle declaration alone is not attributed the whole all-sector classification. No sensor, helper or physical actuator follows. |
| [OriginalControlComposition](https://github.com/the-omega-institute/trureturing/blob/773d4d43b91abd515be1059283d79dd6572fc174/D5/S3/Quantum/Fibers/OriginalControlComposition.lean) and [owning Scribe](https://github.com/the-omega-institute/trureturing/blob/773d4d43b91abd515be1059283d79dd6572fc174/Blueprint/D5/S3/Quantum/Fibers/OriginalControlComposition.scribe.cs) | The exact `OriginalControl` alternatives and `concatenate_original`: arbitrary finite/zero durations, literal unchanged prefix, matching height, translated real-phase tail and additive continuous weighted integrals. |
| [Instrument Boundaries](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md), §§4–5, 9–15 | The actual full unknown phase/parity family, known-height Kraus rigidity, fixed-parity rotations, canonical stopped completion, survival factors, complete terminal classification and matched finite continuation. Corollary 4.3 and Proposition 6.2 reuse these; no marked-law inverse or endpoint classification is redelivered. |
| [Instrument Stability](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md), §§1–5; [Quantum Carrier Minimum](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md), §§3–6 | Complete output metrics and their regularity boundaries; exact labelled live-qutrit correspondence with supplied correlated archives. That upper and the separate unassisted live-dimension lower have different assistance contracts. Neither obtains matching-height data. |
| [Record Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_RECORD_ACQUISITION.md), §§2–9, 11 | Credited adaptive/randomized query obstructions, bounded-speed rates and conditional calibrated area/winding certificates. No duplicate quadrature or general sampling impossibility is proposed. |
| [Sampled Instrument Certificates](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_SAMPLED_INSTRUMENT_CERTIFICATES.md), §§2–3, 7–8 | Finite timed-record complete-instrument prediction under common margin/speed/variation/BV-velocity promises and an explicit extra joint recorder kernel. Exact return height is its generator guarantee. Its law prediction is not an open-cut reanchoring actuator. |
| [Event Memory and Coarse Aliasing](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_EVENT_MEMORY_AND_COARSE_ALIASING.md), §§3–6 | Actual-event total-memory capacity, exact-time versus binning and marginal resampling. Those tasks and dimensions are not identified with our classical uncertain-height support bound. |
| [Parity Record Transport](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_PARITY_RECORD_TRANSPORT.md), Lemma 4.1, §§5–9 | Retained-auxiliary phase rigidity, supplied-helper optima, return-on-success distinction and finite checkpoint updates at known current heights. The present extra uncertainty is current height; no helper construction is inferred. |
| [Transport–Memory Completion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §§2.9–2.12, 2.18 | Same coherent source, actual common port, aligned acquired records, known nonzero amplitudes and known nonzero record overlap. A parity helper and a constant noisy height report do not acquire these. Unknown overlap cannot be divided out. |
| [Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §34; [Atlas Stable Core](RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md), Theorem 6.3 | One actual joint image, full acquisition and successor compatibility, actual routes/domains and individually sufficient views. A CP obstruction on a particular consumer does not instantiate the four-view recovery hypotheses. |
| `TypedFiniteViewKernel.typed_finite_view_kernel`, `DynamicsDescent.dynamics_descends_iff`, `EnvironmentRecords.recordOverlap`, `PhaseRecordRecoveryCriterion.phase_record_recovery_criterion` | Respectively: typed finite-path behavior with illegality distinct from a successor; preservation of fibers for dynamics descent; actual record overlap; and recovery for the specified matching reversal channels. They are interface suppliers, not a hidden height sensor, generic quantum-program obstruction or authorization of an environment port. |

**Literature statement 8.2 (primary metadata and applicability).** The
following primary texts support mature ingredients or a precise comparison.
The source-specific three-height obstruction, pair filter, record-support
capacity and actual-history application are `repo-derived` consequences
proved here. No worldwide priority or complete literature-search claim is
made.

| Primary source | Verified hypotheses, use and non-transfer |
| --- | --- |
| Anthony Chefles, Richard Jozsa and Andreas Winter, [*On the existence of physical transformations between sets of quantum states*, quant-ph/0307227v1](https://arxiv.org/html/quant-ph/0307227v1), Theorems 2–3, Eqs. (7)–(9) | `literature-attested`: finite specified pure families admit deterministic or outcome-dependent probabilistic CP transformations subject to positive environment Gram factors/contributions; omitting failure gives a positive Gram remainder. The environment may depend on the source. This applies to the finite nine-state witness and the complete two-height constructions. It supplies neither an acquired helper/calibration nor a continuous-family phase-rigidity theorem; those source calculations are explicit above. |
| Anthony Chefles and Stephen M. Barnett, [*Quantum State Separation, Unambiguous Discrimination and Exact Cloning*, quant-ph/9808018v1](https://arxiv.org/html/quant-ph/9808018v1), Eq. (18) and its surrounding discrimination conditions | `literature-attested`: the equiprobable known pure pair has maximum unambiguous conclusive probability $1-|\langle\eta_+,\eta_-\rangle|$, with an inconclusive branch. Proposition 4.2 uses its equal-probability construction and keeps the actual inconclusive successor. No helper acquisition or endpoint optimality for a nonorthogonal helper is attributed to it. |
| Kai Liu and Deguang Han, [*Intermediate memory costs of quantum channel synthesis with a protected subsystem*, 2610.20536v1](https://arxiv.org/html/2610.20536v1), §V.1, Theorem 2, Eq. (40) | The stated finite controlled-channel task has a protected subsystem and a prescribed first-stage noncommutative graph. Feasibility requires the identity in every cross-Kraus span and supplies a simultaneous processor with finite nonorthogonal programmes. Its classical control source and programme relation are premises. No map from an unknown original waveform to that control/programme register is supplied here; its dimension or approximation conclusions are not transferred. |

The literature comparison distinguishes a specified finite controlled
channel from an actually acquired source-dependent programme. Source-family
Gram criteria, Kraus/Stinespring representation, positivity of a pure
marginal, circle geometry, matrix square roots and counting are mature
mathematics. The proof does not import deterministic arbitrary-data unitary
programming or sharp-observable programming hypotheses, nor an unconditional
no-information interpretation of Koashi–Imoto. Searches of the pinned
original-control/fiber surfaces for uncertain-height reanchoring and the
public arXiv search for probabilistic pure-state transformations locate
these relevant comparison frameworks; their bounded scope establishes no
absence theorem or novelty claim.

**Arithmetic example 8.3 (bounded exact instances).** Rational arithmetic on
the nine choices (RB.22) verifies (RB.5), the support and velocity bounds,
the prefix/arrival survivals (RB.26) and individual return factors (RB.25).
As a separate exact unit-circle instance, the three bottom-coordinate pairs

$$
(3/5,4/5),\quad(4/5,3/5),\quad(5/13,12/13)
\tag{RB.29}
$$

have affine difference determinant $-6/325$. The first pair has $g=24/25$,
so (RB.15) gives $p=49/50$; its vector $w$ obeys both unit-functional
constraints and $p\|w\|^2=1$. These are original heights
$x=c(3/5)^2,c(4/5)^2,c(5/13)^2$ at any fixed allowed $c$.
The finite checks support the displayed arithmetic. The universal
conclusions rest on the ordinary polynomial, linear-algebra and counting
proofs, without retained experiments.

**Open boundary 8.4 (the missing acquisition and actuation relation).**
The obstruction isolates a joint requirement for this exact consumer:
actual acquisition must yield inputs compatible with a phase-preserving
matching-height action. A generator's exact return invariant can supply
the match; an actually acquired height- or phase-dependent record/token
could instead change (RB.7), but needs its own same-source preparation,
calibration, permission, precision, action and complete successor proof.
A phase-bearing prehistory archive can also change the premise. This
volume does not privilege height measurement as the only possible escape.

Reducing a noisy height error without eliminating the three-height support,
retaining a sampled table, or adding the same supplied parity helper does
not implement this exact reanchoring macro. Conversely the result does not
exclude approximate reanchoring, every alternative live action, an observer
with richer actual correlated data, or a boundary protected by a generator
invariant. Positive endpoint constructions do not close the canonical full
instrument task.

The source-bound helper and its overlap/calibration are not acquired here.
Neither are the common-port observations, unknown joint-overlap estimates,
all legal controller/selector/update inputs, complete archive, spatial or
temporal reconstruction, or a closed observer for the whole original menu.
Full space/time/boundary/memory mutual recovery, native stationary
$\alpha/\beta$ memory-rate/cofinality, and the distinct fixed-Hamiltonian
quantum minimax task retain their original unresolved bridges. The static
arithmetic, C114 mixed-state, twisted-ground and two-clock span models
supply no source/action/observation/resource correspondence for this
reanchoring task merely by sharing terminology or dimensions.

## 追加锚（本行以下为增补区）
