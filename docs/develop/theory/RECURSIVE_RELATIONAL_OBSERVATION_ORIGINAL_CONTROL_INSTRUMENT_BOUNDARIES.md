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
