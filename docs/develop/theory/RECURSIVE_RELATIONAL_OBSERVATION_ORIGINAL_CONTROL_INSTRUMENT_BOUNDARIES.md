# Recursive relational observation: original-control instrument boundaries

This volume isolates one operational question for the positive five-mode
fiber.  The geometric source and the chronological composition law are
credited suppliers.  The results below add an explicitly declared quantum
instrument interface and determine what that interface can and cannot do.
They are ordinary mathematical statements about that interface; they do not
assert a physical actuator, a sensor, a waveform oracle, a worldwide recovery
theorem, or a new kernel certificate.

The source model is the one fixed by `FiniteRectangleTransport` and
`OriginalControlComposition`.  A base is $b=(X,Y,Z)$ with `ValidBase` as in
that declaration, $r=1-Z$, and

$$
0<Z<1,\qquad 0<X<r,\qquad 0<Y<r.
$$

Its strict probability interval is

$$
J(b)=(\max\{0,X+Y-r\},\min\{X,Y\}).
$$

For $k\in J(b)$ the five probabilities, in the order $(0,1,2,3,13)$, are

$$
p_b(k)=(r-X-Y+k,\;X-k,\;Z,\;Y-k,\;k),
\tag{OC.1}
$$

and the signed transport direction is $(1,-1,0,-1,1)$.  On the strict
interior of $J(b)$ all five entries are positive.  The supplied weight is

$$
I_b(k)=\sum_{i\in\{0,1,3,4\}}\frac1{p_b(k)_i},\qquad
w_b(k)_i=\frac{d_i}{p_b(k)_i I_b(k)},\qquad d=(1,-1,0,-1,1).
\tag{OC.1a}
$$

The last index $4$ denotes mode $13$.  An original control has finite
$T\ge0$, continuous real $k,\chi$ on $[0,T]$, $k(t)\in J(b)$, finite
variation of $\chi$, and either absolute continuity of both coordinates or
their supplied finite-piecewise-$C^1$ regularity.  Its residual satisfies
$h_i'=w_b(k)_i\chi'$ almost everywhere.

The words *actual history* below mean a history produced from the fixed
positive preparation by an admissible original control.  They do not mean a
chosen endpoint vector with no source path.  The all-sector finite rectangle
and fixed-height constructions in the owning Blueprint supply every signed
integer sector needed below.  `finite_rectangles_realize` supplies the
continuous four-leg rectangles, and `concatenate_original` supplies their
literal chronological prefix, shifted tail, real phase increment, and
additivity of every continuous scalar weighted integral.

## 1. Interfaces, states, and the distinction being tested

Fix initial phases $\theta_i$ with $\theta_2=0$.  For a strict-interior
height $x$ and a real phase lift $h\in\mathbb R^5$, write

$$
\Psi_x(h)_i=\sqrt{p_b(x)_i}\,e^{-i(\theta_i+h_i)}.
\tag{OC.2}
$$

For a residual measured from the fixed preparation, source compatibility is
$h_2=0$ and $h_0-h_1-h_3+h_4=\chi(t)-\chi(0)$.
For the prior loops we choose the initial real control lift $\chi(0)=0$;
an arbitrary initial lift is handled by translation.  The state in (OC.2)
has norm one because the entries in (OC.1)
sum to one.  Distinct real lifts that differ by multiples of $2\pi$ are kept
distinct as source histories even when their endpoint vectors coincide.

The **state-only containment seat** has the following complete input
contract.

* One unknown specimen in $\mathbb C^5$ is supplied in the state
  $\Psi_x(h)$.
* All ancillary states, controller registers, references, and classical
  inputs are the same for every compared history and contain no
  history-correlated information.
* A prescribed continuation is one common CPTP map (or one common finite
  adaptive protocol, which induces a CPTP map) independent of the unknown
  $h$.
* The required output at a cut is the exact pure state
  $\Psi_y(h+\Delta)$, with the known continuation increment $\Delta$.
  There is no expectation-value oracle and no acquired waveform or winding
  record in this contract.

An instrument with a retained success/failure flag is a different contract:
its success operation is trace-nonincreasing, its failure is an executed
event with a declared successor, and every flag is retained.  A source-owned
correlated record is also a different input contract.  These distinctions are
part of the theorem statements and are not supplied by a compact endpoint
coordinate.

The complete future response family used by the RRO transport-memory
contract contains more fields than (OC.2).  Accordingly, an obstruction proved on this
state-only subfamily blocks only a proposed state-only implementation of an
original prefix.  It does not settle the common-source, calibrated
acquisition, record-overlap, closed-predictor, inverse-permission, or full
future-menu obligations in Transport-Memory Completion §§2.9–2.18 or the
single actual joint-history requirements of Process Geometry §34.

Here is a precise response-law connection when a proposed quantum consumer
does contain the relevant reads.  Suppose its identity-cut menu includes the
computational probabilities and both Hermitian coherence quadratures on the
edges $(01),(02),(03),(1\,4),(3\,4)$.  A positive density matrix with the
target positive diagonal and these exact complex entries is the target pure
density matrix.  Indeed, represent it as the Gram matrix of vectors $v_i$.
On every measured edge the target has
$|\rho_{ij}|=\sqrt{\rho_{ii}\rho_{jj}}$, so Cauchy–Schwarz is saturated and
$v_i,v_j$ are parallel.  Connectivity and nonzero diagonals make all the
vectors parallel; the edge phases fix all relative phases and therefore the
whole rank-one matrix.  Thus equality of this identity-cut response law
forces the state-output requirement below.  This implication assumes the
declared calibrated quantum read menu; it neither performs those reads nor
identifies an expectation with physically obtained finite samples.

## 2. Actual histories and chronological cuts

### 2.1 Three source histories at every valid base

Let $b$ be `ValidBase` and let $k$ be strict interior.  Put

$$
h^{(0)}=(0,0,0,0,0),\qquad
h^{(1)}=\frac{\pi}{2}(1,1,0,1,1).
\tag{OC.3}
$$

The third lift is selected by the two symmetry walls.  With
$A=X+Y-r$, use the following table.

| base condition | $h^{(2)}$ | $C_x$ | $q$ |
| --- | --- | --- | --- |
| $A\ne0$, either sign | $(\pi,0,0,0,-\pi)$ | $2X+2Y-r-4x$ | $i$ |
| $A=0$ and $X\ne Y$ | $(0,\pi,0,-\pi,0)$ | $4x-r$ | $i$ |
| $A=0$ and $X=Y=r/2$ | $(\pi,0,0,0,\pi)$ | $r-4x$ | $i$ |

Each displayed vector satisfies $h_2=0$, the equality $h_0=h_4$ when
$A=0$, and the equality $h_1=h_3$ when $X=Y$.  The first two table rows
have real relation phase $0$; the double-wall row has relation phase $2\pi$.
These checks establish the wall hypotheses as well as the charge condition.

Here is the precise use of the credited synthesis.  Let $U_b$ impose zero
middle coordinate and these two conditional wall equalities, and put
$V_b=U_b\cap\ker(d^{\mathsf T})$.  Choose the source's fixed distinct
interior menu consisting of $k$ and $g-1\le3$ auxiliary heights, where
$g=4-\mathbf1_{A=0}-\mathbf1_{X=Y}$.  Its weight differences form a basis
of $V_b$.  For a displayed lift of charge $2\pi m$, synthesize
$h-2\pi m w_b(k)\in V_b$ by those rectangles and prepend a unit-time
fixed-height leg of phase increment $2\pi m$.  This takes at most
$1+4(g-1)\le13$ unit legs.  Idle legs can pad all three histories to duration
$13$, so duration need not reveal the selected history.  Every coefficient
is a finite signed real, and the finite height menu has a positive support
margin.  There is no uniform numerical margin over all valid bases.
Every $m\in\mathbb Z$, including negative $m$, remains in the source domain;
the certificate selects three members of that domain.

For any two strict-interior heights $k,l$, append to each of these histories
the same horizontal original control

$$
k(t)=k+(l-k)t,\qquad \chi(t)=\chi(0),\qquad 0\le t\le1.
\tag{OC.4}
$$

The common public input is the relative command
$((l-k)t,0)$.  The constant $\chi(0)$ in each actual tail is its own prior
endpoint lift; the actuator is not given that unknown number.  Translating
the tail is a source composition identity, not a measurement of the past.

The path stays in the convex interval between $k$ and $l$, has zero phase
variation, and has zero transported phase increment.  The credited
`concatenate_original` theorem says more than endpoint equality: it keeps
the old prefix pointwise, identifies the shifted tail, adds the real phase
increments, and adds each continuous integral.  Thus a contradiction at the
cut $t=1$ is a contradiction about one actual chronological continuation,
not about replacing the history by its endpoint holonomy.

### 2.2 Gram entries for the three histories

Use the convention

$$
G_x(a,b)=\langle\Psi_x(h^{(a)}),\Psi_x(h^{(b)})\rangle.
$$

Direct substitution in (OC.1) gives, for every strict-interior $x$,

$$
G_x(0,1)=Z-ir.
\tag{OC.5}
$$

The entry is nonzero because $Z>0$.  For the third history there is a real
affine function $C_x$ from the table such that

$$
G_x(0,2)=Z+C_x,
\qquad
G_x(1,2)=Z+qC_x,
\tag{OC.6}
$$

where $q=i$ in every row: the factor on each bottom term in $G_x(1,2)$
is $e^{i\pi/2}=i$ times its sign in $G_x(0,2)$.  For example, on the
double wall the signs of modes $0$ and $4$ give
$C_x=r-4x$, while on the $A=0$, $X\ne Y$ wall the signs of modes $1$ and
$3$ give $C_x=4x-r$.  In every row $C_x$ has nonzero slope, so
$k\ne l$ implies $C_k\ne C_l$.

## 3. The containment-seat obstruction

**定理 3.1（每个 `ValidBase` 上的三历史统一确定性障碍）。**
Let $b$ be `ValidBase` and let distinct $k,l$ lie in the strict interior of
$J(b)$.  Under the state-only containment-seat contract, no CPTP map can
send all three actual input states
$\Psi_k(h^{(a)})$ to the corresponding exact output states
$\Psi_l(h^{(a)})$, $a=0,1,2$.  Consequently no endpoint-only deterministic
quantum implementation can realize the common phase-preserving leg (OC.4)
for every actual original history at that base.

**证明。**  Dilate a hypothetical common CPTP map by an isometry $V$.  Exact
pure output on each of the three inputs forces

$$
V\Psi_k(h^{(a)})=\Psi_l(h^{(a)})\otimes\eta_a
$$

for unit environment vectors $\eta_a$.  Inner products therefore obey

$$
G_k(a,b)=G_l(a,b)\langle\eta_a,\eta_b\rangle.
\tag{OC.7}
$$

By (OC.5), the $(0,1)$ equation has the same nonzero value on both sides,
so $\langle\eta_0,\eta_1\rangle=1$ and hence $\eta_0=\eta_1$.  Write
$a=\langle\eta_0,\eta_2\rangle$.  The other two equations and (OC.6) give

$$
Z+C_k=a(Z+C_l),
\qquad Z+qC_k=a(Z+qC_l).
$$

Subtracting $q$ times the first equation from the second yields
$Z(1-q)=aZ(1-q)$.  Since $Z>0$ and $q=i\ne1$, $a=1$.  Returning to
either equation gives $C_k=C_l$, contradicting the nonzero slope of the
selected $C_x$ and $k\ne l$.  The contradiction used three actual histories,
one common map, and no record correlated with the unknown past.  It did not
use a phase estimate or divide by an unknown overlap.  $\square$

The theorem is a containment result: adding a history-correlated actuator
memory, a supplied winding record, a fresh preparation, or a promise to one
parity changes the input family.  Each such change must be named before a
deterministic implementation is claimed.

### 3.1 A rational two-history certificate inside the same family

The three-history proof is uniform in the base.  A small double-wall
certificate also gives a numerical error margin.  Take

$$
b=(1/4,1/4,1/2),\quad r=1/2,\quad
k_0=1/8,\quad k_1=1/16.
\tag{OC.8}
$$

Use the two actual lifts $h^{(0)}=0$ and
$h^{\mathrm{odd}}=(0,-\pi,0,-\pi,0)$, supplied by the signed winding
construction.  Their input overlap at $k_0$ is $1/2$ and the required output
overlap at $k_1$ is $1/4$.  Thus the pure-state trace distances are

$$
D_{\rm in}=\sqrt{1-(1/2)^2}=\frac{\sqrt3}{2},\qquad
D_{\rm out}=\sqrt{1-(1/4)^2}=\frac{\sqrt{15}}4.
$$

Trace-distance contraction rules out the exact common channel.  If two
approximate outputs have trace-distance errors $\varepsilon_0$ and
$\varepsilon_1$ from their prescribed pure targets, the triangle inequality
gives the exact lower bound

$$
\varepsilon_0+\varepsilon_1
\ge \frac{\sqrt{15}-2\sqrt3}{4},
\qquad
\max\{\varepsilon_0,\varepsilon_1\}
\ge \frac{\sqrt{15}-2\sqrt3}{8}.
\tag{OC.9}
$$

The two paths leading to these states have the same fixed preparation.  A
common horizontal tail (OC.4) is legal and has zero phase variation, so the
certificate tests an intermediate chronological action rather than a
completed endpoint loop.

An explicit signed realization fixes auxiliary height $a=k_1$.
The weights at $k_0,k_1$ are respectively
$(1,-1,0,-1,1)/4$ and $(3,-1,0,-1,3)/8$.  Prepend the phase leg of
increment $2\pi m$ at $k_0$ and append a rectangle of phase height
$-4\pi m$ at $a$.  Its residual is
$(0,-\pi m,0,-\pi m,0)$ for every signed $m$, with duration five and
variation $10\pi|m|$.  The cases $m=0,1$ give (OC.8); all probabilities
along these histories and their test leg are at least $1/16$.
These are control-parameter costs, without a physical runtime or energy
calibration.

The mature finite-family Gram and dilation criterion used here is Chefles,
Jozsa and Winter, *On the existence of physical transformations between sets
of quantum states*, quant-ph/0307227, Theorems 2–3.  Equation (OC.9) is the
direct trace-distance specialization for the displayed source states; it is
not a claim about every quantum carrier or every physical actuator.

## 4. The double-wall full family

The full-family result uses a more structured base but a larger, continuous
unknown family.  Let

$$
X=Y=c=\frac{1-Z}{2},\qquad 0<Z<1,\qquad 0<k<c.
$$

Then $p_b(k)=(k,c-k,Z,c-k,k)$.  In the fixed five-mode Hilbert space define

$$
U_+=\frac{e^{-i\theta_0}e_0+e^{-i\theta_4}e_4}{\sqrt2},\qquad
U_- =\frac{e^{-i\theta_1}e_1+e^{-i\theta_3}e_3}{\sqrt2}.
$$

The vectors $U_+,U_-,e_2$ are orthonormal.  The actual all-sector endpoint
family is

$$
\Psi_{k,\beta,m}
=\sqrt Z\,e_2+e^{-i\beta}
 \left(\sqrt{2k}\,U_++(-1)^m\sqrt{2(c-k)}\,U_-\right),
\quad \beta\in\mathbb R,\ m\in\mathbb Z.
\tag{OC.10}
$$

Its real residual is
$h=(\beta,\beta-\pi m,0,\beta-\pi m,\beta)$ and its relation phase is
$2\pi m$.  The integer $m$ is a source-history label; the endpoint state
sees its parity, while the source construction retains every signed integer.

Choose one auxiliary $a\in(0,c)$ distinct from $k$, independently of
$\beta,m$.  The supplied double-wall weights are

$$
w_b(x)=\left(\frac12-\frac{x}{r},-\frac{x}{r},0,
             -\frac{x}{r},\frac12-\frac{x}{r}\right).
$$

Prepend a unit-time fixed-height phase increment $2\pi m$, followed by
the credited rectangle at $a$ with phase height

$$
B_{\beta,m}=\frac{r(\pi m-\beta)-2\pi m k}{a-k}.
\tag{OC.10a}
$$

Its residual $2\pi m w_b(k)+B_{\beta,m}(w_b(a)-w_b(k))$ is the exact
real lift in (OC.10), and its signed area is
$2\pi m k+B_{\beta,m}(a-k)=r(\pi m-\beta)$.
Every history has the same five-unit probability waveform and fixed
preparation, with finite phase variation $2\pi|m|+2|B_{\beta,m}|$.
No uniform variation bound over the full family is asserted.
This reuses the source synthesis; it does not give $\beta,m$ to the later
actuator.

### 4.1 Successful-Kraus rigidity and sharp success

**定理 4.1（全未知双墙族的成功 Kraus 刚性）。**
Fix $k,l\in(0,c)$.  Let a trace-nonincreasing CP success operation have
successful output exactly $\Psi_{l,\beta,m}$ for every $\beta\in\mathbb R$ and
every $m\in\mathbb Z$, with no history-correlated input other than the state
(OC.10).  Precisely, its unnormalized output is
$s(\beta,m)|\Psi_{l,\beta,m}\rangle\langle\Psi_{l,\beta,m}|$ with
$s(\beta,m)\ge0$, allowing a zero-probability success event.
Then every successful Kraus operator $K_j$ restricted to the active
span $\operatorname{span}\{U_+,U_-,e_2\}$ has the form

$$
K_j=\lambda_jD_{k,l},\qquad
D_{k,l}U_+=\sqrt{\frac lk}U_+,\quad
D_{k,l}U_- =\sqrt{\frac{c-l}{c-k}}U_-,\quad
D_{k,l}e_2=e_2.
\tag{OC.11}
$$

Consequently the success probability is independent of $\beta$ and $m$ and
satisfies the sharp bound

$$
s\le s_*(k,l):=\min\left\{1,\frac{k}{l},\frac{c-k}{c-l}\right\}.
\tag{OC.12}
$$

The bound is attained by an explicit complete two-outcome instrument.  A
deterministic uniform phase-preserving operation exists exactly when $l=k$.
Every retained successful record is independent of $\beta$ and $m$; failure
records are not constrained to be blind and must remain part of the response
law.

**证明。** Write $d=\sqrt Z e_2$,
$v_\epsilon(k)=\sqrt{2k}U_++\epsilon\sqrt{2(c-k)}U_-$, and
$z=e^{-i\beta}$.  Purity of the specified conditional output implies, for
each successful Kraus operator, a scalar $a_\epsilon(z)$ with

$$
K_j(d+zv_\epsilon(k))=a_\epsilon(z)(d+zv_\epsilon(l)).
$$

Equivalently, the wedge product of the two sides is zero.  Its coefficients
in $z$ are

$$
K_jd\wedge d=0,\quad
K_jd\wedge v_\epsilon(l)+K_jv_\epsilon(k)\wedge d=0,\quad
K_jv_\epsilon(k)\wedge v_\epsilon(l)=0.
$$

The vector-valued polynomial vanishes at every $z$ on the unit circle, so
all its coefficients vanish.  The first equation gives $K_jd=\lambda_jd$.
The second says that the
bottom-space component of $K_jv_\epsilon(k)$ is
$\lambda_jv_\epsilon(l)$; the last equation removes its possible $e_2$
component.  The same $\lambda_j$ occurs for both signs because the vector
$d$ is common.  Adding and subtracting the $\epsilon=\pm1$ equations gives
(OC.11) on the whole active span.  This argument also covers
$\lambda_j=0$.

The trace-nonincreasing condition is
$\sum_jK_j^*K_j\le I$.  Restricting it to the three orthogonal active
directions gives

$$
\sum_j|\lambda_j|^2\frac lk\le1,\qquad
\sum_j|\lambda_j|^2\frac{c-l}{c-k}\le1,\qquad
\sum_j|\lambda_j|^2\le1,
$$

which is exactly (OC.12), with $s=\sum_j|\lambda_j|^2$.  Equality is
attained by taking one successful Kraus operator

$$
K_s=\operatorname{diag}_{i=0,1,2,3,4}
 \left(\sqrt{s_*\,p_b(l)_i/p_b(k)_i}\right)
$$

in the original mode basis and
$K_f=(I-K_s^*K_s)^{1/2}$.  The two CP maps
$\rho\mapsto K_s\rho K_s^*\otimes|s\rangle\langle s|$ and
$\rho\mapsto K_f\rho K_f^*\otimes|f\rangle\langle f|$ form a complete
instrument.  A known diagonal phase increment is inserted by multiplying
$K_s$ by its fixed diagonal unitary; it does not change (OC.12).

In a Stinespring dilation, each successful Kraus label has amplitude
$\lambda_j$ independent of $\beta,m$.  Hence any retained successful flag,
or any processing of those flags, has a law independent of the hidden phase
and parity.  More strongly, a nonzero normalized successful dilation factors as

$$
\Psi_{l,\beta,m}\otimes
       \frac{1}{\sqrt s}\sum_j\lambda_j|j\rangle.
\tag{OC.11a}
$$

Purify any history-independent ancillary input and include every retained
output component in the dilation record.  The same factorization proves
blindness of the entire successful ancillary state, including coherent
records retained for feedback.  This rules out hidden assistance at the next
cut, as well as an acquired phase or parity readout.
The filter is an exact mathematical instrument; calibrated
hardware, matrix precision, monitoring, and a permission to execute it are
additional resources.  This proves the theorem.  $\square$

The amplitude-filter form is consistent with the mature support-matching
filter results in Chiribella and Yang, *Optimal quantum operations at zero
energy cost*, arXiv:1502.00259, Proposition 5.  Their energy premise is not
imported here; (OC.11) proves the form for this full unknown orbit without an
energy-conservation assumption.

### 4.2 Fixed-parity escape

If a source contract promises one parity $\epsilon=(-1)^m$ in advance, define
the normalized bottom vectors

$$
q_\epsilon(k)=\sqrt{\frac{k}{c}}U_+
             +\epsilon\sqrt{\frac{c-k}{c}}U_-.
$$

There is a unitary $W_\epsilon$ with
$W_\epsilon e_2=e_2$ and
$W_\epsilon q_\epsilon(k)=q_\epsilon(l)$.  Extending these two orthonormal
assignments to a basis gives a unitary, and

$$
W_\epsilon\Psi_{k,\beta,m}=\Psi_{l,\beta,m}
$$

for every $\beta$ of that promised parity.  This is a genuine deterministic
escape from (OC.12), but it consumes a parity promise and a calibrated
coherent gate.  The successful full-family instrument cannot acquire that
parity: its success record is blind, and no parity sensor or reset is supplied
by the original control declaration.

Explicitly, rotate through $\alpha(l)-\alpha(k)$ in the orthonormal plane
$(U_+,\epsilon U_-)$, where $\alpha(x)=\arccos\sqrt{x/c}$, and fix
$e_2$ and the inactive complement.  This maps
$\sqrt Z e_2+e^{-i\beta}\sqrt r\,q_\epsilon(k)$ to the prescribed target.
A previously retained, correct source-bound parity bit can select these two
rotations if the coherent gates are also supplied.  The promise can include
every even winding or every odd winding; it does not identify their actual
real lifts or ordered histories.

### 4.3 Complete records and a concrete full-family filter

For $c=3/10$, $Z=2/5$, $k=1/4$, $l=1/8$, the sharp value is $s_*=2/7$.
An explicit original-mode instrument is

$$
K_s=\operatorname{diag}\left(\frac1{\sqrt7},1,\sqrt{\frac27},
                              1,\frac1{\sqrt7}\right),\qquad
K_f=\operatorname{diag}\left(\sqrt{\frac67},0,\sqrt{\frac57},
                              0,\sqrt{\frac67}\right).
\tag{OC.12a}
$$

The flags have probabilities $2/7,5/7$ on every full-family input.
The failure vector is $K_f\Psi_{k,\beta,m}/\sqrt{5/7}$; it has zero modes
$1$ and $3$ and is independent of parity at each fixed $\beta$.
It remains a quantum successor together with its retained failure flag.
It has left the strict positive-support original carrier, so the positive
original-control future menu cannot simply be continued from it.

Any finite retry protocol acting on the sole original input and any retained
ancillas, whose accepted final system state is exact on the whole family,
induces a single trace-nonincreasing CP acceptance operation.  Theorem 4.1
still bounds its total acceptance probability by $s_*$.  This statement
allows arbitrary processing on failure under a declared enlarged protocol;
it supplies no fresh same-history specimen or reset.  An extra correlated
input would again change its hypothesis.

## 5. Chronological survival rather than endpoint substitution

### 5.1 Finite checkpoints

Let $k_0,k_1,\ldots,k_n\in(0,c)$ be a prescribed finite sequence of double-wall
heights.  The same specimen is required to be in the exact state
(OC.10) at every successful checkpoint.  Past successful flags may be used,
but there is no fresh history-bearing input, copy, reset, or replay of the
unknown past.

**定理 5.1（有限切面的全前缀成功率）。**
For the full family (OC.10), the largest probability that every one of the
$n$ checkpoints succeeds is

$$
S_n^*=\prod_{j=1}^n s_*(k_{j-1},k_j).
\tag{OC.13}
$$

This is a complete finite instrument statement: every success or failure
flag is an event, and the failure successor is retained.  It is not a claim
that one can repeat the attempt after failure.

**证明。** Apply Theorem 4.1 at the first cut.  Every successful record has a
law independent of $\beta,m$, so conditioning on any such record supplies no
additional hidden-history input at the next cut.  The same bound therefore
applies successively, giving the product upper bound.  At each cut use the
diagonal $K_s$ and its complementary $K_f$ from Theorem 4.1, retaining the
ordered flags.  Their composition attains the product and gives the complete
finite law.  $\square$

The phase part of an original control does not alter (OC.13): a known phase
increment is a unitary factor in each successful Kraus operator.  The exact
real increment and all signed winding sectors remain in the chronological
source record, by `concatenate_original`; they are not replaced by an
endpoint phase label.

One explicit finite protocol stops at the first failure.  If $K_j,F_j$ are
the two operators for cut $j$, its terminal Kraus products on the initial
live space are

$$
K_n\cdots K_1,\qquad
F_jK_{j-1}\cdots K_1\quad(1\le j\le n).
$$

Keep the ordered success flags and the first failure index $j$, together
with its quantum successor.  Successive identities
$K_j^*K_j+F_j^*F_j=I$ telescope to completeness of these products.
The failed successor is generally outside the positive original fiber;
this protocol grants it only a stopped continuation, with no reset or new
original trial.  Any different post-failure menu must be supplied explicitly.

### 5.2 Ideal all-prefix limit

Fix one public prescribed original continuation $(k,\chi)$ of finite
duration $T\ge0$ at the double-wall base.  Its waveform is the control
program used to define an instrument; it is not acquired from the unknown
past.  Both original regularity alternatives make $k,\chi$ absolutely
continuous: on a finite-$C^1$ partition, integrating the continuous rates on
each closed piece and telescoping gives the global integral primitive.
This is also the regularity argument in the composition supplier.
Define

$$
H_i(t)=\int_0^t \operatorname{phaseWeight}(b,k(s))_i\,\chi'(s)\,ds.
\tag{OC.14}
$$

Put $U(t)=\operatorname{diag}(e^{-iH_i(t)})$.  The actual target at time
$t$ is
$U(t)\Psi_{k(t),\beta,m}$, for the unknown initial $(\beta,m)$.
At an open prefix its relation phase need not be an integral multiple of
$2\pi$.  Conjugating by the known $U(t)$ brings its family back to (OC.10);
it does not remove, measure, or reveal the initial phase or signed winding.

For a subinterval $[s,t]$ define

$$
\Lambda[s,t]=\int_s^t
 \left(\frac{(k'(u))_+}{k(u)}
 +\frac{(-k'(u))_+}{c-k(u)}\right)du,
\qquad \Lambda(t)=\Lambda[0,t].
\tag{OC.15}
$$

Strict interiority on the compact interval makes the denominators bounded
away from zero and makes this quantity finite.

**定理 5.2（理想连续全前缀生存界）。**
Among ideal CP-divisible instruments that preserve the exact target
$U(t)\Psi_{k(t),\beta,m}$ at every successful prefix for every initial
$\beta\in\mathbb R,m\in\mathbb Z$, allow only history-independent additional
inputs, and retain every failure event, the
optimal probability of surviving all prefixes through time $T$ is

$$
S^*(T)=e^{-\Lambda(T)}.
\tag{OC.16}
$$

For every $t$ the same instrument has survival $e^{-\Lambda(t)}$.  Equivalently,

$$
\Lambda(T)=
\frac12\operatorname{TV}_{[0,T]}
 \left(\log\frac{k}{c-k}\right)
 +\frac12\log\frac{k(T)(c-k(T))}{k(0)(c-k(0))}.
\tag{OC.17}
$$

For a closed probability path the endpoint term in (OC.17) is zero.  Any
nonconstant closed excursion therefore has strictly positive charge even
when its endpoint holonomy, signed area, and winding are all zero.

**证明上界。** For a finite partition $\Pi$ of $[0,T]$, Theorem 5.1 gives

$$
S(T)\le\prod_{[s,t]\in\Pi}s_*(k(s),k(t)).
\tag{OC.18}
$$

Put $u=\log k$ and $v=\log(c-k)$.  The negative logarithm of one factor is

$$
-\log s_*(k(a),k(b))=\max\{0,u(b)-u(a),v(b)-v(a)\}
 =(u(b)-u(a))_+ +(v(b)-v(a))_+.
$$

For either function, positive-increment sums increase under refinement.
Thus one common refinement can approximate both suprema.  The supremum over
finite partitions of the sums of positive increments is
the integral of $u'_++v'_+$ for absolutely continuous $u,v$.  Since
$u'=k'/k$ and $v'=-k'/(c-k)$, refining (OC.18) yields
$S(T)\le e^{-\Lambda(T)}$.

**证明达到。** For $0\le s\le t\le T$, let

$$
K_{t,s}=e^{-\Lambda[s,t]/2}
\operatorname{diag}_{i=0}^4
 \left(\sqrt{\frac{p_b(k(t))_i}{p_b(k(s))_i}}
 e^{-i(H_i(t)-H_i(s))}\right).
\tag{OC.19}
$$

Write $\lambda(t)=\Lambda'(t)$ almost everywhere and

$$
\gamma_i(t)=\lambda(t)-\frac{d}{dt}\log p_b(k(t))_i .
$$

The logarithmic derivatives of the plus, minus and middle probabilities are
$k'/k,-k'/(c-k),0$ respectively.  Hence every $\gamma_i$ is nonnegative
and integrable.  In particular the middle probability is constant and its
attenuation rate is $\gamma_2=\lambda$.
Each diagonal squared modulus in (OC.19) has logarithmic derivative
$-\gamma_i$, so $K_{t,s}^*K_{t,s}\le I$.
On a success input, (OC.19) sends the state at $s$ to
$e^{-\Lambda[s,t]/2}$ times the exact state at $t$.  The diagonal ratios,
the phase integrals, and the exponential factors multiply, so

$$
K_{u,t}K_{t,s}=K_{u,s}.
$$

To give a consistent complete failure law, add one orthogonal stopped state
$f$ to the five-mode live space.  For a finite interval use six Kraus
operators

$$
A_{t,s}=K_{t,s}\oplus1,\qquad
B_{t,s,i}=\sqrt{1-|K_{t,s,ii}|^2}\,|f\rangle\langle i|,
\quad i=0,\ldots,4.
\tag{OC.19a}
$$

Their adjoint products sum to $I_6$.  Keep the success flag or the failure
interval and mode label $i$; the state $f$ has an absorbing successor.
On a live block $\rho$ the forgotten-record channel has live block
$K_{t,s}\rho K_{t,s}^*$ and gains stopped mass
$\operatorname{tr}[(I-K_{t,s}^*K_{t,s})\rho]$.
The loss identity

$$
I-K_{u,s}^*K_{u,s}
=(I-K_{t,s}^*K_{t,s})
  +K_{t,s}^*(I-K_{u,t}^*K_{u,t})K_{t,s}
$$

proves exact composition of these forgotten-record stopped channels.
The refined records retain the first interval of failure and its mode.

For an ideal exact failure time $\tau$ use the CP density on live inputs

$$
J_i(\tau;s)=\sqrt{\gamma_i(\tau)}\,|f\rangle\langle i|K_{\tau,s},
\quad
\mathcal I_{\mathrm{fail},i}(E)(\rho)
  =\int_E J_i(\tau;s)\rho J_i(\tau;s)^*\,d\tau
\tag{OC.19b}
$$

for Borel $E\subset(s,t]$, together with success $K_{t,s}$ and the already
stopped identity.  The fundamental theorem for the absolutely continuous
function $|K_{\tau,s,ii}|^2$ gives

$$
\int_s^t J_i(\tau;s)^*J_i(\tau;s)\,d\tau
 =(1-|K_{t,s,ii}|^2)|i\rangle\langle i|.
$$

Thus (OC.19b) is a complete countably additive instrument with retained
failure time and mode.  Splitting the integral at a cut and using the
cocycle for $K$ proves consistency under chronological refinement.
The no-failure mass from an initial family state is exactly
$\|K_{t,0}\Psi_{k(0),\beta,m}\|^2=e^{-\Lambda(t)}$.
This proves attainment in the stated ideal class.  It does not implement
continuous monitoring or an exact real time register with finite resources.
$\square$

The variation identity (OC.17) follows from

$$
u'_++v'_+=\tfrac12(|u'|+|v'|+u'+v'),
$$

the identities $|u'|+|v'|=|(u-v)'|$ and
$u+v=\log(k(c-k))$.  Phase-only legs contribute no survival charge but keep
their exact phase integrals and elapsed control time.  A prescribed endpoint
identity therefore does not justify deleting an intermediate probability
trajectory.

For two prescribed original controls at the same double-wall base with
matching probability endpoints, their literal source concatenation also has

$$
\Lambda_{\gamma*\delta}
 =\Lambda_\gamma+\Lambda_\delta,\qquad
S^*_{\gamma*\delta}=S^*_\gamma S^*_\delta .
\tag{OC.19c}
$$

Indeed, the pasted $k$ has the first derivative on the prefix and the
translated second derivative on the tail almost everywhere.  Splitting
(OC.15) and changing variables proves the charge identity.  The composition
supplier independently identifies the unchanged prefix, the shifted real
lift and the added phase integrals, so (OC.19) composes with these exact
phase factors on the same chronology.  No reparameterization or deletion of
an odd or negative winding sector is involved.  Zero duration gives the
identity instrument, zero charge, and empty-product survival one.

### 5.3 Exact zero-holonomy witness

Take

$$
b=(2/5,2/5,1/5),\quad c=2/5,\quad
k_0=1/20,\quad k_1=1/10.
\tag{OC.20}
$$

Use the supplied four-leg rectangle with data $(k_1,0)$: move from $k_0$
to $k_1$, hold the real phase height fixed, return to $k_0$, and hold again.
The rectangle has duration four in the supplier's unit-leg convention, zero
phase variation, zero weighted phase integral, zero signed area, zero winding,
and residual vector exactly zero.  It is therefore an actual original control
whose endpoint state and endpoint control coordinates are exactly the initial
ones.

The two nontrivial checkpoint factors are

$$
s_*(k_0,k_1)=\frac12,\qquad
s_*(k_1,k_0)=\frac{c-k_1}{c-k_0}=\frac67,
$$

so every-prefix success is exactly

$$
\frac12\cdot\frac67=\frac37.
\tag{OC.21}
$$

The constant continuation at $k_0$ has survival one.  Thus the identity
endpoint operator and the chronological complete instrument have different
response laws.  The difference is a realized survival record, not a new
holonomy coordinate.  No permission to repeat after failure, no reset, and no
physical speed or energy calibration is inferred from (OC.21).

An equally exact certificate at (OC.8) uses the zero-phase four-leg
rectangle from $k_0=1/8$ to $k_1=1/16$ and back.  Its outgoing and return
maxima are $2/3$ and $1/2$, so its survival is $1/3$ and its charge is
$\log3$.  At (OC.20) the charge is $\log(7/3)$ and the support margin is
$1/20$.  Both rectangles have zero real phase increment, area, residual,
and phase variation.  Waiting for the same four-unit duration at their
starting height has survival one.  Thus neither discrepancy is a change of
elapsed control duration.

## 6. Natural ownership: a promised-pair comparison

The full-family theorem deliberately gives the controller no correlated past
record.  A natural-ownership interface may instead declare a record owned by
the source/control interaction.  The following sharp comparison is only for
one promised pair and must not be read as a full-family implementation.

Use

$$
b=(3/10,3/10,2/5),\quad r=3/5,\quad
k_0=1/4,\quad k_1=1/8.
\tag{OC.22}
$$

The two actual histories have lifts $h^{(0)}=0$ and
$h^{(1)}=(0,-\pi,0,-\pi,0)$, with the same preparation and the same
prescribed continuation.  Their input probability vectors are

$$
(1/4,1/20,2/5,1/20,1/4),
$$

and their target vectors are

$$
(1/8,7/40,2/5,7/40,1/8).
$$

The input overlap is $4/5$ and the target overlap is $3/10$.  These values
are exact consequences of the signed modes; no sampled expectation is being
treated as a state coordinate.

Their actual prior histories can use (OC.10a) with $a=1/8$ and $\beta=0$.
For signed integer $m$ the fixed-height leg has increment $2\pi m$, the
rectangle coefficient is $-4\pi m/5$, and the residual is
$(0,-\pi m,0,-\pi m,0)$.  Its duration is five and its phase variation is
$18\pi|m|/5$.  Every path has the same probability waveform and minimum
support $1/20$.  Select $m=0,1$ for the promised pair.  The common
one-unit horizontal leg reaches $k_1$, and the zero-phase return excursion
would have identity endpoint; the obstruction is already present at the
outbound cut.  In Gram language the no-record deterministic environment
would require overlap $8/3$, whose two-by-two correlation matrix has
determinant $1-(8/3)^2=-55/9$.

### 6.1 Sharp correlated-record threshold

Suppose the source supplies a normalized pure record $\eta_i$ correlated with
history $i$, and put
$\mu=\langle\eta_0,\eta_1\rangle$.  A deterministic operation must output the
target system states on this promised pair; an arbitrary environment may be
retained.  The joint input overlap is $(4/5)\mu$.  An isometric dilation of
the operation has environment overlap $\nu$ on the two outputs, so

$$
\frac45\mu=\frac3{10}\nu,\qquad
\nu=\frac83\mu.
\tag{OC.23}
$$

**命题 6.1（自然所有权的成对阈值）。**
For the promised pure-record pair (OC.22), a deterministic exact conversion
exists if and only if

$$
|\mu|\le\frac38.
\tag{OC.24}
$$

**证明。** Necessity follows from $|\nu|\le1$ in (OC.23).  If (OC.24)
holds, choose two normalized environment vectors with overlap
$\nu=(8/3)\mu$.  The two output vectors
$\Psi_{k_1}(h^{(i)})\otimes\xi_i$ then have the same Gram matrix as the two
joint input vectors.  The Gram isometry on their two-dimensional span extends
to a channel on the whole input space.  $\square$

The threshold is a source-record condition.  Two-dimensional record and
environment spaces suffice: any $z$ with $|z|\le1$ is the overlap of the
normalized vectors $(1,0)$ and $(z,\sqrt{1-|z|^2})$ in the convention
linear in the second argument.  The two joint inputs are linearly
independent since their overlap has modulus at most $4/5$, so their Gram
isometry extends after padding the environment if necessary.  Exact knowledge
of the record states and a calibrated joint operation is an additional
implementation premise.  Arbitrary mixed-record sufficiency is not asserted.

A record produced afterwards by an endpoint-only operation preserving both
original pure endpoints cannot provide this missing distinction.  Its pure
dilation has the form $V\Psi_i=\Psi_i\otimes\xi_i$, so
$(4/5)=(4/5)\langle\xi_0,\xi_1\rangle$ and the total output record is the
same.  Every accessible marginal record is therefore identical.  The useful
record must come from an earlier source/control interaction or another
explicit joint input; its overlap is not inferred from the command name.

### 6.2 Heralded alternative without a correlated record

Keep the same promised pair but remove the source record.  Allow a complete
instrument with a success flag, equal success probability $p$ on the two
histories, exact target system state on success, and an arbitrary retained
failure event.

**命题 6.2（成对 heralded 上界与达到）。**
The sharp common success probability is

$$
p_* = \frac27.
\tag{OC.25}
$$

**证明。** In an isometric dilation, the success contribution to the input
overlap has modulus at most $p(3/10)$ and the failure contribution has modulus
at most $1-p$. Therefore

$$
\frac45\le p\frac3{10}+(1-p),
$$

which gives $p\le2/7$. At equality, map the two input vectors on their span
to

$$
\sqrt{2/7}\,\Psi_{k_1}(h^{(i)})\otimes|s\rangle
 +\sqrt{5/7}\,|f\rangle,
$$

using the same normalized failure vector $|f\rangle$ in an orthogonal
failure-flag sector. Their Gram entry is
$(2/7)(3/10)+5/7=4/5$, so the map is an isometry on the span and extends to
a complete instrument. Failure is a real event and the original state need
not survive it. Repetition would require a separately supplied same-history
preparation or reset contract.  $\square$

The pair thresholds (OC.24) and (OC.25) are concrete ownership comparisons.
They do not supply the full unknown family, a waveform reader, a calibrated
reference, or a closed future predictor.  They also do not turn a
history-dependent actuator into the state-only seat of Theorem 3.1.

## 7. Correspondence with the RRO recovery boundary

The results establish the following exact correspondences.

* **Source.** One fixed positive preparation and actual original histories
  supply the unknown endpoint. Signed real phase lifts and every integer
  winding sector remain source data. The controller receives no hidden lift
  unless a separate record contract says so.
* **Action and legality.** The common tail is the same public relative
  control, and (OC.4) is legal at every point of the strict probability
  interval. `concatenate_original` preserves the old prefix and the shifted
  tail; it does not grant a formal inverse or a repeat permission.
* **Observation.** The target is the complete five-mode pure state in the
  stated instrument contract. Matching only a compact phase label or only an
  endpoint residual is a weaker task. The filter theorems preserve the target
  quantum state on success but do not read its phase or parity into a
  classical record.
* **Records.** Success/failure flags and their order are part of the complete
  instrument law. Successful records are blind in the full double-wall
  family; failure records may carry information and must not be discarded.
  The promised-pair record threshold assumes an actual source-owned record
  is already present. No unknown record overlap is divided out.
* **Chronology.** The charge $\Lambda$ and the cut labels depend on the
  ordered probability path. The zero-holonomy rectangle shows that an
  endpoint identity does not preserve the intermediate instrument response.
  Elapsed time, phase variation, survival charge, storage, and compilation
  precision are separate resources.
* **Recovery scope.** Strict five-mode support and the prescribed successful
  state survive under the displayed conditional instruments. The past
  waveform, exact real winding, elapsed history, calibrated common-port
  reference, finite-sample phase estimate, external archive, and complete
  four-view mutual recovery remain unproved or unavailable under the stated
  contracts.

The primary quantum principles used here are the finite-family Gram/isometry
criterion and probabilistic transformation framework of Chefles, Jozsa and
Winter (quant-ph/0307227), together with the state-preservation/no-imprinting
perspective of Koashi and Imoto (quant-ph/0101144).  Their general results are
credited suppliers; the three-history source realization, the full-orbit
Kraus rigidity, the variation charge, the complete stopped instruments, and
the exact original-control witnesses are the deductions in this volume.

No statement here supplies a physical sensor, an observer acquisition
procedure, a finite-bit implementation, a universal information-conservation
law, or completion of the native $\alpha/\beta$ and fixed-Hamiltonian QMB
frontiers.  The natural next interface must declare the common source,
calibration, record overlap, time alignment, precision, storage, and legal
future menu before any stronger recovery claim is made.

## 8. Suppliers, quantitative resources, and proof boundary

Repository citations here use the immutable revision
`df12d01189bdf8196457773d7f9e8eda168cb3cc`.  Source geometry and the
additional instrument interpretation have distinct ownership.

| Supplier | Exact role and boundary |
| --- | --- |
| [FiniteRectangleTransport Lean](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean) and [Blueprint](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/Blueprint/D5/S3/Quantum/Fibers/FiniteRectangleTransport.md) | `ValidBase`, `probability`, `phaseWeight`, `weight_compatible`, and `finite_rectangles_realize` supply the strict carrier, signed law, gauge/charge, and actual rectangles. The Blueprint's interpolation and all-sector applications supply the particular lifts used here. Those applications are credited ordinary synthesis; the rectangle declaration alone is not attributed the whole classification. |
| [OriginalControlComposition Lean](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/D5/S3/Quantum/Fibers/OriginalControlComposition.lean) and [Blueprint](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/Blueprint/D5/S3/Quantum/Fibers/OriginalControlComposition.md) | `OriginalControl`, `FiniteC1Control` and `concatenate_original` fix finite real durations, regularity, unchanged prefixes, shifted tails, real phase increments and all continuous scalar integral additions. They supply no CPTP actuator or history acquisition. |
| [Probability-phase source](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md), §§3.1–3.3, 3.7, 3.12, 4, 8–9 | Fixed preparation, all signed winding sectors, actual current rays, connected ideal coherence reads, prescribed later loops and relative-command domains. Their source/action identities remain credited; an ideal expectation is not an obtained finite sample. |
| [Transport-Memory Completion](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §§1–2 | Same coherent source, actual common port, known nonzero amplitudes and record overlap, calibration, time alignment, acquisition, future menu and closed-predictor assumptions remain required. Blind successful flags do not close those requirements. |
| [Process Geometry](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §34, and [Atlas Stable Core Holonomy](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md), §§1–8 | One actual joint source, domains, complete events, failure successors, record updates and actual routes are necessary. The present stochastic instrument does not instantiate the entire deterministic four-view recovery contract. |
| [Joint Relations and Clocks](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md), Proposition 1.14 | The existing nearest-point repair obstruction already distinguishes mathematical repair from a common CPTP action on all qubit inputs. Its input family and map differ from the actual five-mode family here. |
| Chefles, Jozsa and Winter, [*On the existence of physical transformations between sets of quantum states*](https://arxiv.org/html/quant-ph/0307227v1), §2, Theorems 2–3 and Eq. (9) | `literature-attested`: finite pure-state conversion uses an environment Gram matrix that is positive semidefinite with unit diagonal; instruments retain outcome-dependent positive Gram contributions. Used for the finite certificates and pair constructions. The continuous-family rigidity is proved in §4. |
| Chiribella and Yang, [*Optimal quantum operations at zero energy cost*](https://arxiv.org/html/1502.00259v5), Proposition 5, Eqs. (52)–(54) | `literature-attested`: matching-support perfect-fidelity conversion under their energy-preserving constraint has a minimum probability-ratio bound and an amplitude filter. That energy constraint is not imported here; §4 proves necessity against all CP successes on the stated unknown family. |
| Koashi and Imoto, [*What is Possible Without Disturbing Partially Known Quantum States?*](https://arxiv.org/html/quant-ph/0101144v2), Theorem 5 and §VIII.2 | `literature-attested`: finite-dimensional faithful transfer and no-imprinting framework. Successful-record blindness here follows directly from (OC.11a). The paper supplies no original-control actuator or archive. |

The specified-state conversion problem in [*Pure State Transformations under
Block Coherence*](https://arxiv.org/html/2605.30588v1), §III, Theorem 3,
assumes PBIO and an explicit active-branch independence condition; its
SBIO/BDCO conversion statements concern those prescribed operation classes.
Those premises are not supplied for a common unknown-family actuator here.
The [multimode Fock-projection postselection
study](https://arxiv.org/html/2603.22122v1) declares phase-encoded linearly
independent coherent-state alphabets, which are a different source from
(OC.10).  Neither supplies the chronological full-family conclusion used in
this volume, and no theorem from either is transferred.  These are bounded
scope comparisons, without an exhaustive literature or priority claim.

The source-specific deductions are `repo-derived`: actual-history
containment in Theorem 3.1; full-family Kraus and record rigidity in Theorem
4.1; finite-cut and ideal all-prefix optima in Theorems 5.1–5.2; exact
zero-holonomy chronological witnesses in §5.3; and the promised-pair
comparison in Propositions 6.1–6.2.  Gram/isometry conversion, amplitude
filtering, Stinespring dilation, integration and total variation remain
credited mature ingredients.  No worldwide priority is asserted.

The finite instruments use one live five-mode specimen, supplied blank
ancillas, calibrated contractions or unitaries, and retained flags.
A two-outcome endpoint filter has a binary flag.  The stopped completion
(OC.19a) uses a six-dimensional live-plus-stopped carrier and at most six
Kraus operators per interval.  A protocol stopping at its first failure has
$n+1$ possible first-failure-or-all-success indices; an optional mode label
adds at most five choices per failure cut.  These are record-alphabet
counts, not minimum hardware memory or physical-storage bounds.
The exact failure time in (OC.19b) is an ideal real-valued record and has no
supplied fixed finite-bit representation.

All square roots, matrix entries and phase integrals in the construction are
exact.  A fixed original path has a positive compact support margin, with no
uniform margin over the original class.  A continuous real control need not
have a finite effective description; existence of (OC.19) neither compiles
an arbitrary waveform nor acquires it from the unknown specimen.
Gate precision, construction work, sampling, calibrated clocks, phase
references, coherent recombination, another same-history copy, archive
access and their costs remain separate obligations.
The active span has dimension three, but its continuum of exact states is
not a finite classical memory.

The ordinary proofs carry the universal conclusions; the rational
certificates are finite arithmetic witnesses.  No new Lean/kernel
verification or physical realization is asserted.  The actual joint observer
interface and all-view recovery remain open.

## 追加锚（本行以下为增补区）

## 9. Exact information in the canonical terminal instrument

The object classified in §§9–15 is precisely (OC.19)–(OC.19b), including its
mode labels and its absorbing successor. The optimum, the existence of this
instrument, its chronological consistency and its survival cocycle are the
credited results of §5.2. The classification below does not classify other
attaining implementations, accessible dilations, coherent failure successors,
or deliberately attenuated completions. It concerns the double wall; no
extension to every `ValidBase` is asserted.

Fix

$$
0<Z<1,\qquad r=1-Z=2c,\qquad b=(c,c,Z),\qquad
0<a<c,\qquad 0\le T<\infty.
\tag{OC.26}
$$

All compared controls start at $k(0)=a$, use the same clock and duration,
and obey `OriginalControl`: continuous real $k,\chi$, strict $0<k<c$,
finite variation of $\chi$, and either the absolute-continuity alternative
or the supplied finite-piecewise-$C^1$ alternative. The latter also implies
absolute continuity, by the truncated-partition fundamental theorem in
`OriginalControlComposition`. Thus both alternatives remain included below;
finite variation alone is not used to justify a derivative primitive.
Each individual path has a positive compact support margin. There is no
common speed, variation, charge or survival bound over this entire class.

Use relative real phase and uncentered area

$$
\begin{aligned}
\xi(t)&=\chi(t)-\chi(0),&
\mathcal A(t)&=\int_0^t k(u)\chi'(u)\,du,\\
H_+(t)&=\xi(t)/2-\mathcal A(t)/r,&
H_-(t)&=-\mathcal A(t)/r,\\
H(t)&=(H_+,H_-,0,H_-,H_+),&
\xi(t)&=2(H_+(t)-H_-(t)).
\end{aligned}
\tag{OC.27}
$$

These are the supplied affine double-wall weights integrated along the
actual control. In particular, real lifts are retained before taking phase
characters. Based phase loops satisfy $\xi(T)=2\pi n$ with any signed
$n\in\mathbb Z$; general open controls need satisfy no such condition.

Write $S(t)=\exp(-\Lambda(t))$ and $\lambda=\Lambda'$ as in (OC.15).
The canonical success operator from time zero is

$$
K_t=\operatorname{diag}_i\left(
 \sqrt{\frac{S(t)p_i(k(t))}{p_i(a)}}e^{-iH_i(t)}\right),
\qquad p(k)=(k,c-k,Z,c-k,k).
\tag{OC.28}
$$

Its complete terminal output is success with its live quantum output, or
first failure at an exact $\tau\in(0,T]$, original mode $i$, and stopped
state $f$. Every such time/mode event is retained. On the supplied
six-dimensional extension the no-new-failure operator is $K_T\oplus1_f$;
the failure operators annihilate an already stopped input. No further
environment port is included in this definition.

For mathematical comparisons, choose any one common coherent pure input
$\psi$ with $|\psi_i|^2=p_i(a)$ and $\psi_2=\sqrt Z$. In particular this
may be any one fixed, unknown member of (OC.10). Calling it common does not
give its phases, $\beta$, or $m$ to a controller. Let

$$
F_i(t)=\Pr(\tau\le t,\ \text{failure mode}=i).
\tag{OC.29}
$$

Here $F_i$ is a cumulative function of the whole terminal probability law.
It is not a value emitted by one execution. A run stopped at $\tau$ has only
its executed original prefix followed by $f$; inversion of the program's
law does not say that this failed run executed its unperformed live tail.

**定理 9.1（累计损失与参数化高度的精确逆）。** For every control above,
every common input just specified and every $0\le t\le T$,

$$
\begin{aligned}
F_i(t)&=p_i(a)-S(t)p_i(k(t)),\\
S(t)&=1-\sum_iF_i(t)=1-F_2(t)/Z,\\
k(t)&=\frac{a-F_0(t)}{1-F_2(t)/Z}.
\end{aligned}
\tag{OC.30}
$$

Every $F_i$ is absolutely continuous and nondecreasing. In particular the
entire marked failure law identifies the height on its original time axis,
including waits and turning points, without differentiating that law.
It is independent of the unknown input phases on the declared input family.

Proof. Put $q_i(t)=S(t)p_i(k(t))$. Compact strict positivity and absolute
continuity make $\log p_i(k)$, $S$ and $q_i$ absolutely continuous, with
$S>0$ throughout. For the nonnegative rate
$\gamma_i=\lambda-(\log p_i(k))'$ of §5.2 the product rule gives

$$
q_i'=-\gamma_iq_i\quad\text{almost everywhere}.
\tag{OC.31}
$$

The rank-one jump in (OC.19b) has on a general live input $\rho$ the density

$$
J_i(t;0)\rho J_i(t;0)^*
 =\frac{\gamma_i(t)q_i(t)}{p_i(a)}\rho_{ii}|f\rangle\langle f|.
\tag{OC.32}
$$

Its scalar phase cancels. Substituting $\rho_{ii}=p_i(a)$ and integrating
(OC.31) proves the first identity at every time. Summing uses
$\sum_i p_i=1$; using the fixed positive middle probability $Z$ gives the
second identity, and mode $0$ gives the last. At zero duration the measures
are empty, $S=1$ and $k(0)=a$. Absolute continuity excludes hidden endpoint
atoms. $\square$

## 10. One signed loss curve and the compatible two-CDF image

**定理 10.1（Jordan 表示及其准确可实现范围）。** Put

$$
P=F_0=F_4,\qquad N=F_1=F_3,\qquad
\ell=P-N,\qquad V(t)=\operatorname{TV}_{[0,t]}(\ell).
$$

For every canonical control of §9,

$$
\begin{aligned}
P+N&=c(1-S),&P'N'&=0\quad\text{almost everywhere},\\
P&=(V+\ell)/2,&N&=(V-\ell)/2,\\
S&=1-V/c,&k&=\frac{a-(V+\ell)/2}{1-V/c},\\
F_2&=ZV/c.
\end{aligned}
\tag{OC.33}
$$

The exact range of the probability-law coordinate $\ell$ is the set of
real absolutely continuous curves on $[0,T]$ such that

$$
\ell(0)=0,\qquad
P(T)<a,\qquad N(T)<c-a,
\quad
P=(V+\ell)/2,\ N=(V-\ell)/2,\ V(t)=\int_0^t|\ell'|.
\tag{OC.34}
$$

Each such curve determines exactly one absolutely continuous height path
starting at $a$, and a lawful original control realizing its canonical
failure law exists, for example with $\chi$ constant. If height closure is
required, impose additionally $k(T)=a$. The range is for the original union
of regularity alternatives; a demand for the finite-piecewise-$C^1$
subclass separately requires the reconstructed height to meet that demand.

Proof. The identities between paired modes and $P+N=c(1-S)$ follow from
(OC.30). If $k'>0$, then $\lambda=k'/k$ and $P'=0$, whereas
$N'=cS\lambda$. If $k'<0$, then $\lambda=-k'/(c-k)$ and
$N'=0$, whereas $P'=cS\lambda$. Where $k'=0$ both vanish. Thus the
nonnegative densities $P',N'$ are disjoint almost everywhere, and
$|\ell'|=P'+N'$. Integrating proves $V=P+N$ and all of (OC.33).
Moreover $a-P(T)=S(T)k(T)>0$ and
$c-a-N(T)=S(T)(c-k(T))>0$, proving necessity of (OC.34).

Conversely, the absolutely continuous Jordan parts in (OC.34) are
nondecreasing, start at zero and have disjoint nonzero derivatives almost
everywhere. Set

$$
R=a-P,\qquad Q=c-a-N,\qquad S=(R+Q)/c,\qquad k=R/S.
$$

The endpoint inequalities bound $R,Q,S$ away from zero at every earlier
time. Hence $k$ is absolutely continuous, $k(0)=a$ and $0<k<c$ with
$c-k=Q/S$. Define $\lambda_0=(P'+N')/(cS)=-S'/S$ almost everywhere.
Where $P'=0$ the quotient rule gives $k'=k\lambda_0\ge0$; where
$N'=0$ it gives $k'=-(c-k)\lambda_0\le0$. If both vanish then $k'=0$.
Consequently

$$
\lambda_0=(k')_+/k+(-k')_+/(c-k).
$$

Together with $S(0)=1$ this proves that $S$ is exactly the canonical
survival. With constant $\chi$, the original absolute-continuity
alternative holds. Formula (OC.30) returns precisely $P,N,F_2$ and hence
$\ell$. The inverse formula makes the height unique. This also proves the
singleton zero-duration case. $\square$

**定理 10.2（两个累计函数的像与共同定义域上的互逆）。** Given real
absolutely continuous functions $u,v$ on $[0,T]$, they are exactly
$(F_0,F_2)$ of some canonical original control if and only if

$$
\begin{gathered}
u(0)=v(0)=0,\qquad v'\ge0\ \text{almost everywhere},\qquad v(T)<Z,\\
S=1-v/Z,\qquad k=(a-u)/S\in(0,c)\ \text{at every time},\\
u'(t)\in\{0,cv'(t)/Z\}\quad\text{almost everywhere}.
\end{gathered}
\tag{OC.35}
$$

On this exact domain the two representations are inverse by

$$
\ell=2u-cv/Z,\qquad V=cv/Z,
\qquad
u=(V+\ell)/2,\qquad v=ZV/c.
\tag{OC.36}
$$

The remaining cumulative functions are
$F_4=u$ and $F_1=F_3=cv/Z-u$. Thus these are two descriptions of the same
law, not independent storage constructions.

Proof. Necessity follows from (OC.30) and the two sign cases in Theorem
10.1. Conversely (OC.35) bounds $S$ away from zero and makes $k$
absolutely continuous. Put $\lambda_0=v'/(ZS)$. Where $u'=0$,
$k'=k\lambda_0$; where $u'=cv'/Z$,
$k'=-(c-k)\lambda_0$. If $v'=0$ these equations coincide. This gives
exactly the canonical rate and survival, and constant $\chi$ supplies an
actual original control with the requested $u,v$.

For the common-domain assertion, (OC.35) gives
$\ell'=\pm cv'/Z$ almost everywhere, so its actual variation is
$V=cv/Z$. Its Jordan parts are $P=u$, $N=cv/Z-u$.
Strict positivity of $k,c-k$ at $T$ gives their endpoint inequalities in
(OC.34). Conversely a curve satisfying (OC.34) yields the $u,v$ in (OC.36),
with $v(T)<Z$ and the two derivative alternatives from the disjoint Jordan
parts. All formulas are then literal inverses. $\square$

Absolute continuity is essential in these statements: an arbitrary
bounded-variation curve may have singular loss and is not included. Nor
can optimality be omitted. For example, adding a positive common attenuation
rate $\eta$ at constant $k=a=c/2$ would give
$S=e^{-\eta t}$, $P=N=a(1-S)$ and $\ell=0$ despite nonzero loss.
This is an enlarged, noncanonical operation, not an instance of (OC.19b).
Even its two CDFs violate the two-choice derivative condition in (OC.35).
Other completions retaining different failure coherences need not satisfy
(OC.32). None of these enlarged classes is classified here.

**命题 10.3（附加终端相位的可实现域）。** For $T>0$ and a fixed admissible
height $k$, the attainable real pairs $(\xi(T),\mathcal A(T))$ under the
absolute-continuity phase alternative are all of $\mathbb R^2$ if $k$ is
nonconstant. If $k\equiv a$, their exact range is
$\{(C,aC):C\in\mathbb R\}$. Thus a nonconstant height allows every
terminal character pair $(e^{-iH_+(T)},e^{-iH_-(T)})\in\mathbb T^2$;
a constant height allows exactly

$$
\left\{\left(e^{-i(1/2-a/r)C},e^{iaC/r}\right):C\in\mathbb R\right\}.
\tag{OC.37}
$$

The actual image is meant here, without replacing it by its closure.
For $T=0$ only the pair $(1,1)$ occurs. Under a specified phase-loop
sector $n$, additionally require $C=2\pi n$; sectors are not discarded.

Proof. For $\alpha=\chi'\in L^1[0,T]$ the two moments are
$(\int\alpha,\int k\alpha)$. A nonconstant continuous $k$ has two
disjoint positive-length intervals with distinct average heights
$\kappa_1\ne\kappa_2$: choose small intervals near two distinct values.
Let $b_j$ be their normalized indicator functions. For
$\alpha=z_1b_1+z_2b_2$ the moments are
$(z_1+z_2,\kappa_1z_1+\kappa_2z_2)$. The determinant is nonzero, so
any two requested moments are attained. Its integral primitive is an
absolutely continuous real phase with finite variation. The constant case
is immediate. Formula (OC.27) is an invertible real linear map from the two
moments to $(H_+,H_-)$; taking its phase characters proves the assertion.
If $k$ satisfies the finite-piecewise-$C^1$ alternative, these piecewise
constant rates also preserve that alternative after finite refinement.
$\square$

The single curve $\ell$, the two entire functions $(u,v)$, and an entire
parameterized $k$ are exact infinite-precision law objects. No one of these
representations is declared a finite memory alphabet or an acquired law.
For example a single trajectory's signed failure indicator is not $\ell$:
a mode-$0$ failure would make that indicator jump by one, and inserting its
variation into $1-V/c$ would yield a negative number because $c<1/2$.
The formulas act on probabilities, never on a substituted sample path.

## 11. Complete terminal classification and unknown initial inputs

**定理 11.1（同一正相干输入、全部输入及参考的分类）。** Let $\gamma$ and
$\widetilde\gamma$ be two controls of §9 at the same $b,a,T$. The following
conditions are equivalent.

1. Their complete terminal classical–quantum output measures agree on one
   common coherent pure input with diagonal $p(a)$ and positive middle
   amplitude. Equality includes the unnormalized success density and every
   Borel failure-time event in every original mode.
2. They agree on every paired same input of (OC.10), for all
   $\beta\in\mathbb R$ and signed $m\in\mathbb Z$.
3. They have the same $k(t)$ for every $t$ and the same two terminal
   characters $z_+=e^{-iH_+(T)}$, $z_-=e^{-iH_-(T)}$.
4. Their instruments are equal as CP-valued measures on every live input,
   and on the supplied six-dimensional stopped extension, including after
   adjoining any finite-dimensional external quantum reference.

Equivalently the exact classification data are
$(u(\cdot),v(\cdot),z_+,z_-)$ on (OC.35), or
$(\ell(\cdot),z_+,z_-)$ on (OC.34), with the phase image specified in
Proposition 10.3 and any stated loop promises. The classified object is the
terminal operation; these data do not replace its actual quantum specimen
and retained events by a classical state.

Proof. From condition 1 the mode/time traces agree. Theorem 9.1 gives the
same height at every time and the same $S$. For any common positive coherent
input, let $x=K_T\psi$ and $\widetilde x=\widetilde K_T\psi$.
They are nonzero and equality of their unnormalized rank-one densities
implies $x=e^{i\omega}\widetilde x$ for some unit scalar. Their middle
coordinates are both exactly $\sqrt{S(T)Z}>0$, so $e^{i\omega}=1$.
All other input components and all diagonal moduli are nonzero. Cancelling
them gives $e^{-iH_i(T)}=e^{-i\widetilde H_i(T)}$ for every $i$, hence
condition 3. This is a comparison proof, not an instruction to read the
unknown input phases.

Conversely, equal height paths have equal almost-everywhere derivatives,
$\lambda,S,q_i$ and loss measures. For every live $\rho$ and Borel
$E\subseteq(0,T]$, (OC.31)–(OC.32) give the full CP map

$$
\mathcal I_{\mathrm{fail},i}(E)(\rho)
 =\frac{\int_E dF_i(t)}{p_i(a)}\rho_{ii}|f\rangle\langle f|.
\tag{OC.38}
$$

Thus equal $k$ gives equal failure CP measures, even when intermediate phases
differ. The terminal characters also make $K_T=\widetilde K_T$ exactly,
so the success maps and $K_T\oplus1_f$ extensions agree. With a reference
$R$, the corresponding formula is

$$
(\mathcal I_{\mathrm{fail},i}(E)\otimes\mathrm{id}_R)(\rho_{LR})
 =\frac{\int_E dF_i(t)}{p_i(a)}
 |f\rangle\langle f|\otimes\langle i|\rho_{LR}|i\rangle.
\tag{OC.39}
$$

Equality therefore preserves reference blocks and not only scalar
probabilities. Success uses the same $K_T\otimes I_R$; the same argument
covers live/stopped coherences of the declared extension. This proves 3
implies 4. Condition 4 implies 2 and 2 implies 1. The zero-duration case
has the identity operation and no failure events. $\square$

This upgrade from one coherent input to all inputs uses the special diagonal
success and rank-one marked jumps just calculated. It is not a claim that
one input generally characterizes a quantum channel, or that arbitrary
preparations and tomography have become legal source actions.

**命题 11.2（未标号未知输入族的不同量词）。** The paired-input comparison in
Theorem 11.1 is different from equality of unlabelled sets of output laws
when the initial $(\beta,m)$ may be reassigned. For general open controls,
these unlabelled sets agree exactly when their $k$ paths agree and

$$
\xi(T)-\widetilde\xi(T)\in2\pi\mathbb Z.
\tag{OC.40}
$$

In particular, among based phase loops with the same height path, the
unlabelled sets agree regardless of terminal area or signed winding.

Proof. The common failure law in each set still gives $k$ by (OC.30).
For a member of the input family the normalized live output is

$$
\sqrt Z e_2+e^{-i(\beta+H_+(T))}
 \left(\sqrt{2k(T)}U_+
 +(-1)^m e^{i\xi(T)/2}\sqrt{2(c-k(T))}U_-\right).
\tag{OC.41}
$$

The freely varying $\beta$ absorbs any $H_+$ shift. Both nonzero bottom
components and the fixed middle component show that the remaining
unlabelled sign set is exactly
$\{e^{i\xi(T)/2},-e^{i\xi(T)/2}\}$.
Equality of these sets is exactly (OC.40). This also proves sufficiency
without giving any relabelled parameter to a controller.

For phase loops write $\xi(T)=2\pi n$ and $B=H_+(T)$.
The success state is $\Psi_{k(T),\beta+B,m+n}$. Given another loop with
$\widetilde B,\widetilde n$, the mathematical relabelling

$$
\widetilde\beta=\beta+B-\widetilde B,\qquad
\widetilde m=m+n-\widetilde n
$$

makes the success states coincide; all failure outputs already coincide.
This is equality of statistical families with nuisance input parameters.
It does not identify $B,n$ from a specimen with an uncalibrated initial
phase and winding. $\square$

## 12. The fixed-height-path phase ambiguity class

Here “fixed height path” means that the entire function $k(t)$ is held
fixed, not necessarily that it is constant in time.

**定理 12.1（完整终点仪器的相位纤维）。** For a fixed admissible $k$ and two
original phase controls, let $\alpha=\chi'-\widetilde\chi'$.
Their canonical terminal instruments agree exactly when

$$
\int_0^T\alpha\in4\pi\mathbb Z,\qquad
\int_0^T k\alpha\in2\pi r\mathbb Z.
\tag{OC.42}
$$

For $T>0$, the common zero-moment subspace

$$
\mathcal N_k=\left\{\alpha\in L^1[0,T]:
 \int\alpha=0,\quad\int k\alpha=0\right\}
\tag{OC.43}
$$

is infinite dimensional. Every $\alpha\in\mathcal N_k$ gives a lawful
phase perturbation $\chi(t)\mapsto\chi(t)+\int_0^t\alpha$ with the
same initial phase, exact terminal real phase increment, signed area and
terminal real residual, hence the same complete instrument. A phase loop
keeps its exact signed winding, not just its parity.

Proof. By (OC.27), equality of the two characters is equivalent to
$\Delta\mathcal A/r\in2\pi\mathbb Z$ and
$\Delta\xi/2-\Delta\mathcal A/r\in2\pi\mathbb Z$.
These are exactly (OC.42); Theorem 11.1 supplies both directions.

Both moments in (OC.43) are bounded linear functionals on $L^1$ because
$k$ is continuous on a compact interval. More explicitly, choose three
disjoint positive-length intervals, normalize their indicators $b_j$, and
write $\kappa_j=\int kb_j$. The two homogeneous equations
$\sum z_j=\sum\kappa_jz_j=0$ have a nonzero real solution in three
unknowns. Disjoint supports make $\sum z_jb_j$ a nonzero element of
$\mathcal N_k$. Arbitrarily many disjoint triples give arbitrarily many
linearly independent such functions. The primitive of any $L^1$ rate is
absolutely continuous with finite variation; strict probability support is
unchanged. Thus the perturbation stays in the original class. For an
original finite-piecewise-$C^1$ path, the displayed finite step-rate
perturbations preserve that alternative on a common finite refinement.
$\square$

The proof identifies the actual whole terminal phase fiber: the inverse
image of the lattice in (OC.42) under the two-moment map, not merely one
example or a dimension count. Even the zero-moment portion contains
arbitrarily many independent lawful perturbations. This does not yet make
any of their phase records acquired or accessible.

## 13. One phase-order witness and one signed-winding consequence

**定理 13.1（同资源、非零失败、异第三签名的实际控制对）。** Take
$b=(2/5,2/5,1/5)$, $c=2/5$, $r=4/5$, $a=1/10$, $T=2$.
Define actual relative controls by

$$
\begin{aligned}
k(t)&=\begin{cases}(1+t)/10,&0\le t\le1,\\
                         (3-t)/10,&1\le t\le2,\end{cases}\\
q(t)&=t-3t^2+2t^3\quad(0\le t\le1),\\
\xi_\pm(t)&=\begin{cases}\pm q(t),&0\le t\le1,\\
                                      0,&1\le t\le2.\end{cases}
\end{aligned}
\tag{OC.44}
$$

Set $\chi_\pm=\chi_0+\xi_\pm$ with the same compatible initial real lift
and preparation. Both are actual original based controls, meet both
regularity alternatives, and have support margin $1/10$. Their complete
terminal instruments are identical on every input and reference, with
success $K_2=I_5/\sqrt3$ and genuine failure probability $2/3$ on the
original input family. They have different third signatures and different
prefix quantum output laws.

Proof. The controls join continuously at time one; their polynomial and
affine pieces have continuous rates on their respective closed pieces.
They return to the same height and real phase, so both winding numbers are
exactly zero. Direct integration gives

$$
q(0)=q(1)=0,\quad \int_0^1q=0,\quad
\int_0^1q'=0,\quad\int_0^1tq'=0,\quad
\int_0^1t^2q'=1/30,\quad\int_0^1(q')^2=1/5.
\tag{OC.45}
$$

Thus $\xi_\pm(2)=\mathcal A_\pm(2)=0$ and $H_\pm(2)=0$ as real
five-vectors. The height path is identical throughout. Theorem 11.1 proves
complete CP-measure equality, including all Borel time/mode events, not
only endpoint states or total loss. The credited survival formula gives
$S(t)=1/(1+t)$ on both legs. For clarity the entire actual-input failure
CDFs are

$$
\begin{aligned}
F_2(t)&=\frac{t}{5(1+t)},\qquad F_4(t)=F_0(t),\quad F_3(t)=F_1(t),\\
(F_0(t),F_1(t))
 &=\begin{cases}
 (0,\,2t/[5(1+t)]),&0\le t\le1,\\
 ((t-1)/[5(1+t)],\,1/5),&1\le t\le2.
 \end{cases}
\end{aligned}
\tag{OC.46}
$$

At $T=2$ the mode masses are
$(1/15,1/5,2/15,1/5,1/15)$, summing to $2/3$, and
$k(2)=a$, $H(2)=0$ gives the asserted $K_2$.
Equation (OC.38) proves equality on arbitrary inputs even though their
failure probabilities need not be those particular masses.

The pair is matched in actual duration, support, pointwise absolute
coordinate speeds and the following coordinate-resource totals:

$$
\begin{aligned}
|k'|&=1/10\ \text{almost everywhere},&|\chi_\pm'|&\le1,\\
\operatorname{TV}(k)&=1/5,&
\operatorname{TV}(\chi_\pm)&=\frac{2}{3\sqrt3},\\
\mathcal Q_\pm&=\int_0^2(k'^2+\chi_\pm'^2)=11/50,\\
\mathcal L_\pm&=1/10+\int_0^1\sqrt{1/100+q'(t)^2}\,dt.
\end{aligned}
\tag{OC.47}
$$

Indeed the two interior extrema of $q$ are $\pm1/(6\sqrt3)$, giving
the displayed variation; (OC.45) gives $\mathcal Q$. The derivative
squares agree pointwise, giving the length identity and identical unsigned
speed-dependent accumulated costs at each cut. These are the mathematical
coordinate costs of the acquisition volume, not calibrated hardware energy.

Define the third signature with increasing chronological order by

$$
S^{k,k,\chi}(\gamma)
 =\int_{0<t_1<t_2<t_3<2}dk(t_1)\,dk(t_2)\,d\xi(t_3)
 =\frac12\int_0^2(k(t)-a)^2\,d\xi(t).
\tag{OC.48}
$$

To justify the second equality, the first two scalar integrals up to $t$
are $\int_0^t(k(s)-a)\,dk(s)=(k(t)-a)^2/2$, by the
absolutely continuous chain rule; integrate that identity against $d\xi$.
Only the first leg contributes, so (OC.45) gives

$$
S^{k,k,\chi}(\gamma_+)=1/6000,\qquad
S^{k,k,\chi}(\gamma_-)=-1/6000.
\tag{OC.49}
$$

The alternative polynomial $f(t)=t(1-t)(2t-1)$ equals $-q(t)$.
If the positive control is defined using $+f$, its coefficient in the same
ordered definition (OC.48) is negative. More generally replacing $k-a=t/10$
by $vt$ and $q$ by $\varepsilon q$ gives
$\pm\varepsilon v^2/60$; using $f$ reverses those signs. There is no
change in the underlying pair of paths. Reversing word or orientation
conventions would have to be stated separately.

Unequal coefficients already prove unequal full signatures. The paths
are also distinct under increasing time reparameterization: $k$ has a unique
maximum at one and is strictly monotone on each side. Any increasing
reparameterization preserving this same height path must fix the maximum
and be the identity on each monotone leg, and so cannot change $q$ to $-q$.
The bounded-variation signature theorem cited in §16 also excludes their
being tree-like equivalent; it is credited, not a new uniqueness theorem.

For an explicit prefix separation, at $t=1/2$ one has

$$
k=3/20,\quad S=2/3,\quad \xi_\pm=0,\quad
\mathcal A_\pm=\mp1/320,\quad
H_+=H_-=\pm1/256
\tag{OC.50}
$$

for the two controls, with zero middle phase in both. On any common input
of (OC.10), the normalized-success coherence
$2\overline\psi_0\psi_2$ consequently differs in complex modulus by

$$
4\sqrt{(3/20)(1/5)}\sin(1/256)
 =\frac{2\sqrt3}{5}\sin(1/256)>0.
\tag{OC.51}
$$

The initial unknown phase contributes only one common unit rotation, so
this separation does not assume it is known. Multiplying by $2/3$ gives
the separation of this linear read in the unnormalized live block; the
prefix failure blocks are identical. Thus the full prefix outputs differ.
A calibrated permitted quadrature measurement could distinguish their
laws. The theorem supplies neither that read nor simultaneous acquisition
of past live states in a single stopped run. $\square$

**命题 13.2（复用有符号合成的绕数后果）。** The credited synthesis (OC.10a)
at $c=3/10$, $Z=2/5$, $a=1/4$, auxiliary height $1/8$ and $\beta=0$
gives two further actual controls, of winding $n=+1$ and $n=-1$, with the
same complete terminal canonical instrument and genuine nonzero failure.

Proof. Use the unit-time fixed-height increment $2\pi n$ followed by
its four-leg rectangle of phase height $B=-4\pi n/5$.
The real residual is the already supplied
$(0,-\pi n,0,-\pi n,0)$. The two terminal characters are therefore
$(1,-1)$ for either sign. The entire five-unit height waveform is common,
so Theorem 11.1 gives equality of the full instrument. Its survival is
$(2/7)(1/2)=1/7$. Both paths have support margin $1/20$, duration five
and phase variation $18\pi/5$; their signed phase rates are opposite
pointwise and their height rates agree, so their coordinate lengths and
quadratic costs also agree. Their signed areas are $3\pi n/5$ and their
real windings are opposite. The synthesis and survival factors are reused
inputs; the consequence here is equality of complete time/mode CP measures
while those real windings differ. $\square$

These are two witnesses for distinct losses of information: Theorem 13.1
keeps the exact winding and area fixed but changes phase chronology and
third signature; Proposition 13.2 isolates signed-winding ambiguity.
The already supplied endpoint and zero-holonomy survival witnesses are not
counted again as additional findings. Both new consequences test ordinary
lawful operation; neither is a claim of a recorded pre-run incident or
physical experiment.

Every signed sector remains in the source and in the quantified theorems.
In particular prepend any one common supplied original loop of signed
winding $m\in\mathbb Z$ ending at $a$ to both controls (OC.44), translating
their actual real phase as `concatenate_original` prescribes. Their complete
terminal instruments still agree, by composition, and their total winding
is exactly $m$. The two suffix prefix-state distinctions persist, with a
common phase rotation and positive common survival multiplier. The prefix
has its own added duration and costs; no fixed finite resource budget is
asserted to contain arbitrarily large $|m|$.

## 14. What equality preserves under lawful forward continuation

**定理 14.1（保留实际联合档案的有限前向续接）。** Suppose Theorem 11.1 holds.
Use a common initial joint state of the live/stopped system and any retained
reference, archive and controller registers. Retain the old time/mode event,
its live or stopped quantum successor, source/preparation/epoch identity,
clock and units, calibration, reference, permissions, every already acquired
record and every actual selection/update input. Any further history-bearing
field generated outside the classified instrument is required to match in
the full joint state or joint output kernel, not merely in its marginal law.

On a live endpoint allow the complete prescribed original tail menu at this
same double-wall base and matching initial height, restricted only by the
same declared permissions and resource promises. Each tail may have any
finite nonnegative duration, including zero, either original regularity
alternative, any real phase increment, and every signed winding permitted
by its explicit promise. The command specifies relative real phase; it does
not query the unknown past lift. On a failed branch retain $f$ and all its
records with only the supplied absorbing/stopped continuation. Illegal
requests and any visible rejection remain distinct from executed failures.

Then every finite common lawful downstream protocol gives the same complete
joint output law in both cases. Its policy may depend on actually retained
records and matched controller inputs. Additional quantum reads or random
seeds are allowed only when separately permitted, with the same operations,
independence contract where needed, records and charged resources.

Proof. Theorem 11.1 and (OC.39) give equality of the full initial
record-conditioned operator measures jointly with every common reference
register, including any common pre-existing quantum/classical archive.
By hypothesis any separately generated archive fields are also retained
and jointly matched. Thus no correlation needed for feedback was replaced
by equality of a marginal failure-time law.

On the success record the endpoint height is common, so every matching
original tail has the same mathematical domain and permission test. If its
controls are $(\kappa,\varphi)$ of duration $L$, the actual source join is

$$
k(T+s)=\kappa(s),\qquad
\chi(T+s)=\chi(T)+\varphi(s)-\varphi(0),\quad 0\le s\le L.
\tag{OC.52}
$$

The supplied composition result keeps the entire old prefix and gives
this translated tail and addition of every continuous weighted integral.
Its derivative and added phase integral are the same in both cases even
when the unknown old real endpoint lifts differ. No controller is handed
$\chi(T)$. The canonical tail therefore has one common success operator
$K_\delta$ and failure kernels $\mathcal I_{\delta,i}$ on the common
live port. Old success followed by new success uses $K_\delta K_T$;
old success followed by a new failure uses
$\mathcal I_{\delta,i}(K_T\rho K_T^*)$ with the old record retained.
Old failures keep their same event and absorbing successor. All these maps
agree. Later timestamps are translated by the same actual terminal clock.

For feedback, condition on the retained classical record and classical
controller fields, keeping quantum registers in the conditional operator.
The common permitted selector supplies the same next operation kernel on
these equal joint inputs. Compose with that kernel, preserve its full label
and successor, and integrate over the old records. Countable additivity and
linearity preserve equality on every joint event. Induction proves equality
for each finite number of such stages. A supplied common quantum instrument
on controller/reference registers is handled by exactly the same CP-map
composition. Branchwise durations and added cost meters agree whenever
computed by these common declared operations; any extra source-sensitive
meter is among the separately matched fields in the hypothesis. $\square$

This is a sufficient boundary for the specified forward operation component
with all other actual fields retained. It does not identify differing full
archives. If a program log, old phase sample, winding sensor, source-bearing
controller state or permission guard distinguishes the histories, that field
must stay in the joint model and the theorem's matching hypothesis must be
checked anew. Neither the equal-resource witness nor a compressed law
coordinate authorizes deleting it. Likewise $F_0=F_4$ does not authorize
merging the actual mode labels: a permitted policy may depend on which mode
actually failed.

The result covers every finite continuation in the declared menu. It proves
no unbounded execution, finite-state implementation, least hardware memory,
archive-acquisition procedure or relative-phase actuator. Exact prescribed
waveforms and calibrated instruments remain named ideal resources of §5.2.
A mathematical relative-command join is not a device for compiling unknown
absolute controls or for recovering the unknown past waveform.

## 15. Calibrated all-prefix laws recover the relative real phase

**定理 15.1（稠密切面上的相对实提升恢复）。** Fix the same input, clock,
$b,a,T$ as in §9. Let $D\subseteq[0,T]$ be dense. Suppose the complete
terminal instruments of the truncated controls agree on that same input
at every cut $t\in D$. Then

$$
k(t)=\widetilde k(t),\qquad
\chi(t)-\chi(0)=\widetilde\chi(t)-\widetilde\chi(0)
\quad(0\le t\le T).
\tag{OC.53}
$$

Conversely these pointwise equalities give equal instruments at all cuts.
The conclusion identifies the exact time-parameterized relative waveform,
not merely a reparameterization class. For a current loop it identifies its
full signed winding.

Proof. Apply Theorem 11.1 to each truncated control. It gives equal heights
and equal characters $e^{-iH_\pm(t)}$ at every cut in $D$.
All these functions are continuous, so the equalities extend to the whole
interval. Each real difference $H_\pm-\widetilde H_\pm$ is continuous,
starts at zero and takes values in the discrete set $2\pi\mathbb Z$.
Connectedness forces it to vanish identically. Formula (OC.27) then gives
(OC.53). Conversely equal $k$ and relative $\chi$ have equal derivatives
almost everywhere, equal integrals and therefore all the same prefix maps.
Zero duration gives the identity as before. $\square$

There is also a constructive law-level reading when the input phase is
calibrated, or the same input's time-zero coherences are supplied. Let
$\sigma_t=K_t|\psi\rangle\langle\psi|K_t^*$ be the unnormalized
successful state at each supplied cut. For $i\ne2$,

$$
e^{-iH_i(t)}=
 \frac{(\sigma_t)_{i2}}
 {S(t)\sqrt{p_i(k(t))Z}\,e^{-i\vartheta_i}},
\qquad \psi_i=\sqrt{p_i(a)}e^{-i\vartheta_i}.
\tag{OC.54}
$$

All denominator factors are nonzero and fixed by the stated preparation
calibration or its time-zero coherence. The two known continuous circle
paths have unique real lifts starting at $H_\pm(0)=0$. For completeness,
uniform continuity on a compact interval gives a finite partition on which
each circle path stays in an open semicircle about its value at the left
endpoint. Choose its local continuous argument there, then successively
adjust by multiples of $2\pi$ to match preceding endpoints. This constructs
the lift. Two such lifts differ continuously in $2\pi\mathbb Z$ and
coincide initially, proving uniqueness. Exact dense-cut values with the
continuous-path promise specify the same paths uniquely; no finite noisy
algorithm or uniform phase-unwrapping error estimate follows from this
uniqueness proof.

This access contract is strictly stronger than a terminal instrument: it
supplies aligned whole cut laws and successful quantum-output coordinates
throughout the interval, with a common input/reference or calibrated
time-zero coherences. Unlabelled independently reselected inputs at each
cut do not meet it. A stopped run does not deliver every one of those
success states; after failure its successor is $f$. Neither all-prefix law
comparison nor (OC.54) is a one-run acquisition theorem, a nondisturbing
measurement service or a grant of repeated same-history specimens.

The recovery begins at time zero with the relative lift set to zero. It
cannot unfold windings accumulated before that initial event which already
coincide in the input ray, such as $m$ and $m+2$ at fixed $\beta$ in
(OC.10). Current all-prefix laws from the same initial density depend on
that density, not on an unsupplied earlier real-lift record. The two claims
are compatible: present relative real phase is identifiable under the
stronger access contract; preinitial winding and actually acquired archives
require their own source-bound information.

## 16. Sources, consumers and the remaining recovery gap

All repository suppliers for §§9–15 are read at immutable revision
`17ef08588473220560adc4a7fb0775a5f7f238a1`. The earlier sections retain
their own stated source revisions. No earlier source byte or mathematical
claim is replaced by this append.

| Supplier and precise hypothesis map | Use and boundary |
| --- | --- |
| `D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean`, `ValidBase`, `probability`, `phaseWeight`, `weight_compatible`, `finite_rectangles_realize`; owning Blueprint and Scribe | The source is the positive five-mode fiber with signed direction $(1,-1,0,-1,1)$. Its double-wall restriction gives (OC.27). Signed rectangles and the Blueprint all-sector synthesis supply the actual controls used in Proposition 13.2 and common signed prefixes. The ordinary all-sector applications are not attributed wholesale to the one rectangle Lean theorem. |
| `D5/S3/Quantum/Fibers/OriginalControlComposition.lean`, `OriginalControl`, `FiniteC1Control`, `concatenate_original`; owning Blueprint and Scribe | Supplies the two regularity alternatives, arbitrary finite durations including zero, unchanged real-time prefix, exactly shifted tail, real increment and every continuous weighted-integral addition. These conditions are retained in §§9, 14–15; they supply no physical actuator or sensor. |
| This volume §§4–5, especially (OC.14)–(OC.19c) | Unknown-phase/parity rigidity, success-record blindness, sharp filters, checkpoint products, optimal ideal all-prefix survival, absorbing time/mode CP completion and cocycle are credited inputs. Theorems 9.1–12.1 classify this specified completion; they neither reprove nor enlarge its optimality class. |
| `RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_RECORD_ACQUISITION.md`, §§1–9, 11–12 | Fixed coherent preparation, ideal coherence sign, finite-query obstructions, rate promises, coordinate costs, conditional area/winding certificates and retained acquisition failures remain credited. A certificate for area and signed winding is not acquisition of the CDFs or of all prefix states. |
| `RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md`, §§2.9–2.12, 2.18 | Interference requires one coherent source, an actual common port, aligned times/records, known nonzero amplitudes and known nonzero record overlap. Unknown overlap leaves a measured product; it cannot be divided out by (OC.54) or by a failure-law inverse. Those physical/acquisition premises remain unsupplied here. |
| `RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md`, §34, and `RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md`, §§1–3 | Complete archive/work-state/reference/permissions belong to one actual joint image with lawful update and failure successors. Theorem 14.1 explicitly retains and matches those fields for its stochastic contract; it does not construct that actual joint image or import a deterministic four-view theorem without its common-implementation premises. |

The following primary sources supply mature mathematics or precise access
comparisons. They do not supply an original-control acquisition interface.

| Primary source and version | Verified statement and correspondence |
| --- | --- |
| B. Hambly and T. Lyons, [*Uniqueness for the Signature of a Path of Bounded Variation and the Reduced Path Group*, math/0507536v2](https://arxiv.org/html/math/0507536v2), Definition 1.4, Theorem 1, Corollary 1.5 | Finite-length real paths have trivial signature exactly when tree-like; two such paths have equal full signatures exactly when their concatenation with the other's reversed path is tree-like. Our controls are absolutely continuous on a compact interval and have finite coordinate variation. This credits the tree-like interpretation after the explicit unequal coefficient (OC.49). It grants neither signature acquisition nor exact clock-parametrized recovery from a signature. The chain rule in (OC.48) is ordinary iterated-integration calculus, not new signature theory. |
| G. Chiribella, G. M. D'Ariano and P. Perinotti, [*A theoretical framework for quantum networks*, 0904.4483v2](https://arxiv.org/html/0904.4483v2), Theorem 3, Eq. (25), Definition 10 | Positive Choi operators with the stated recursive causal trace normalization describe networks; generalized instruments sum to a deterministic comb, with an operator-valued measure for general outcome spaces. This credits operation/record composition and the distinction between terminal outputs and networks with accessible intermediate slots. No such extra slot or tester is granted in §§9–14; their equality proof uses the explicit CP maps. |
| R. van Handel, [*The stability of quantum Markov filters*, 0709.2216v2](https://arxiv.org/html/0709.2216v2), Definition 2.4 and Theorem 2.5 | Observability separates initial states by the full observation algebra; the filter-stability conclusion requires observability and absolute continuity of observation laws in its fixed quantum Markov model. This is not identification of arbitrary unknown time-dependent control waveforms from one absorbing trajectory. No filtering or sensor conclusion is imported. |
| M. Koashi and N. Imoto, [*What is Possible Without Disturbing Partially Known Quantum States?*, quant-ph/0101144v2](https://arxiv.org/pdf/quant-ph/0101144v2), Theorem 5, PDF p.17; Eqs. (85)–(88), PDF p.12 | The faithful-transfer theorem uses finite common support and exact transfer of a possibly infinite state family, including preservation of the redundant-factor state. This is a credited state-preservation framework already used in §8. It supplies no overlap-graph dimension formula, unknown-waveform observer or acquired-law compression. Its asymptotic iid rates do not price the present single stopped history. |
| A. Bluhm, L. Rauber and M. M. Wolf, [*Quantum Compression Relative to a Measurement*, 1708.04898v4](https://arxiv.org/pdf/1708.04898v4), Definition 4.1, PDF p.6; Lemma 5.2, PDF pp.7–8 | The declared finite-$n$ classical register accompanies quantum compression/decompression CPTP maps. The reduction to $n_0\le D^4$ starts from such a finite register and preserves the composite; its individual branches need only be CP. Neither an entire exact real curve nor a continuous-time event archive is thereby finite memory. No compression bound from that different preparation/read contract is used here. |

The new ordinary source-specific deductions are the marked-loss inverse,
the compatible exact Jordan/two-CDF image, the terminal CP-measure
classification including paired-input quantifiers and references, the
fixed-height-path phase fiber, and the realized phase-order/signature
obstruction. Forward composition of equal operations, the fundamental
theorem, Jordan decomposition, circle lifting and generic signature facts
remain credited mature ingredients. The forward and dense-cut consequences
state exactly how those deductions serve the original recovery consumer.
Bounded repository searches in the committed original-control and fiber
sources did not locate these exact inverse/range statements or polynomial
witness values. This is a bounded overlap check, not evidence of worldwide
novelty. Vague citation tokens supply no premise; only the precise sources
and conditions above are used.

No law coordinate here is a received sample, a finite register, a classical
replacement for retained quantum state, or an indefinitely closed predictor.
Actual record acquisition still needs a same-source lawful service,
calibrated clock and mode identities, retained errors/failures, permitted
preparations if statistics are estimated, and charged storage, controller
program and arithmetic precision. Coherence recovery additionally needs
common-port access, a reference and known nonzero gains and record overlap.
All-prefix phase recovery needs its stronger aligned cut-law contract.
A physical realization of the canonical exact operations and monitoring is
also not supplied. No global acquired-boundary minimality, least memory,
finite-shot identification, general off-wall instrument optimum or arbitrary
completion classification is proved.

Exact identifiability alone supplies no uniform approximate observer.
Division by survival in (OC.30) requires a stated positive survival floor
for a uniform error estimate; no such floor holds over the whole original
class. Continuity of the forward law in a waveform metric and stability of
this inverse in a CDF metric are different questions. No conclusion here
negates a survival-floor conditional inverse bound, supplies approximate
phase unwrapping or an unbounded-future error guarantee.

The mathematical gap narrowed here is precise: exact canonical failure laws
retain the full ordered height, while even the complete terminal quantum
instrument loses phase chronology, higher signature and some real winding.
A stronger calibrated all-prefix law retains the current relative real
phase. Turning either law-level statement into an internal observer still
requires actual joint acquisition and update, and both directions of the
same-source space/time/boundary/memory maps. The native $\alpha/\beta$
late-target memory/cofinality task and the separate fixed-Hamiltonian
quantum minimax task remain unresolved; no source/action/resource map to
them is asserted. These are ordinary proofs, without new Lean verification,
a physical realization or completion of the continuing programme.

## 追加锚（本行以下为增补区）
