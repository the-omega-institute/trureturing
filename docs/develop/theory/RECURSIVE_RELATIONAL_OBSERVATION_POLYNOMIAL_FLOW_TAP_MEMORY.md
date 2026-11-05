# Polynomial-flow observations, integrated memory and the current endpoint

This volume studies one commissioned continuous source with a known nilpotent
generator. A finite receiver replaces its additional ideal weighted integrators
by arithmetic on the taps that the source already supplies. The trajectory,
advanced endpoint and entire declared timing-continuation task are preserved.
The result is a source-specific ordinary synthesis of interpolation,
observability and paid conversion. It asserts neither a new interpolation
principle nor a Lean/kernel verification.

## 1. One source, one performed window and an unchanged timing task

**Definition 1.1 (commissioned source).** Fix integers $d,p,\nu\geq1$, real
matrices $B\in\mathbb R^{d\times d}$ and $C\in\mathbb R^{p\times d}$ with
$B^\nu=0$, and $T>0$. The provider initializes one specimen to an unknown
$x_0\in\mathbb R^d$. Its installed material chart and sensor chart are fixed.
Write

$$
E(t)=\sum_{j=0}^{\nu-1}\frac{t^j}{j!}B^j=e^{tB},\qquad t\in\mathbb R.
\tag{1.1}
$$

During an actual active interval the source evolves as $x(t)=E(t)x_0$.
`Read` returns the vector $Cx(t)$ without disturbing the source. `FlowStart`
begins the prescribed active window; `FlowStop` at $T$ holds the actual
endpoint

$$
z=E(T)x_0.
\tag{1.2}
$$

Hold suspends source evolution while the receiver computes. The formal
identities $E(-t)E(t)=I$ describe an inverse coordinate calculation; they
do not install a legal negative-duration action or restore a source.

The provider supplies $B,C$, the degree promise, charts, source binding,
initialization, synchronized exact clock/origin, nondisturbing timed reads,
start/stop control, serial access rights and enough source backing. The
receiver supplies a source-independent deterministic schedule, local arithmetic,
record backing, parser and actual retained invocation rights. These premises
are paid parts of the installation. Inverting acquired data does not learn
an unknown law, supply the initial state, calibrate an absent clock or grant
authority. All $x_0\in\mathbb R^d$ are in the mathematical domain; no particular
source-dependent choice of observer program is allowed.

**Definition 1.2 (actual acquisition record).** For $\nu\geq2$ fix

$$
0=t_0<t_1<\cdots<t_{\nu-1}=T;
\tag{1.3}
$$

for $\nu=1$ use the single node $t_0=T$. Execute one initialization, one
start, the $\nu$ timed vector reads and one stop. A read at $T$ precedes the
stop, or has the same endpoint under the installed nondisturbing convention.
The acquired numerical payloads are exactly

$$
y_i=CE(t_i)x_0\quad(0\leq i<\nu).
\tag{1.4}
$$

The record retains their actual chronological order, timestamps and complete
fixed protocol framing, including the completed start/stop phase. Source,
port, version, chart, reference, owner and return bindings remain genuine.
This Time record contains state-dependent replies. It is not merely a list
of clock values. Variable initialization journals, unrelated traffic and
unlisted wall-duration metadata are outside this numerical view.

Exact timed reads and real-valued payloads are ideal premises of the real
model. A finite exact representation is specified separately in §6. Local
computation after stop takes resources and wall time while the specimen is
held at (1.2); it is not another active flow interval.

**Definition 1.3 (full continuation task and a finite boundary).** Fix the
original finite action alphabet $\mathcal A$ with declared durations
$s_a\geq0$. A completed action $a$ advances this same specimen for $s_a$
active time, holds its successor, and returns its nondisturbing endpoint
read, together with its complete fixed control/return framing:

$$
z' = E(s_a)z,\qquad \operatorname{reply}(a,z)=Cz'.
\tag{1.5}
$$

An endpoint read without an advance is also permitted; Hold is state
preserving. These controls have state-independent legal framing in the
fixed installed context. The task includes every sufficiently backed finite
word over this alphabet and every adaptive choice based on already acquired
replies, the declared public input and a common external random tape if one
is used. It includes actual source calls and successors, not only forecasts.
No non-timing actuator, unknown law change or additional sensor is added.
An actual selector supplies its code, retained working state, operand packets
and completed local decision computation; these are receiver resources.
The trace theorem does not acquire a selector or compute an unprovided
policy. In the real model its conformance assertion is pointwise for actual
choices; the finite rational implementation covers effective decisions
whose local computation terminates.

Let $\mathcal W\subset\mathcal A^*$ be any fixed finite prefix-closed family
containing the empty word, with a fixed enumeration and reference. Put
$s(w)=\sum_{a\text{ in }w}s_a$. Its endpoint Boundary is the response family

$$
R_{\mathcal W}z=(CE(s(w))z)_{w\in\mathcal W}.
\tag{1.6}
$$

These are lawful responses of the current specimen. The family describes
alternative experiments; it does not assert that all its branches were
performed on this run. Forecasting a branch does not append a read to Time.
The actual hidden successor in (1.5) is part of the common realization.
Its literal full coordinate vector is not an extra disclosed output port.
If that vector is itself made part of the requested output, the full-Space
criterion of §4 applies, rather than a nontrivial behavior quotient.

## 2. Integrated memory without a second measurement apparatus

**Definition 2.1 (finite receiver and independently defined memory).** Let

$$
L_i(t)=\prod_{\substack{0\leq j<\nu\\j\ne i}}
\frac{t-t_j}{t_i-t_j},\qquad
W_{ki}=\int_0^T(t/T)^kL_i(t)\,dt\quad(0\leq k,i<\nu).
\tag{2.1}
$$

The empty product for $\nu=1$ is one. The receiver constructs these known
weights from the nodes and $T$, then, after the actual stop, writes

$$
\mu_k=\sum_{i=0}^{\nu-1}W_{ki}y_i.
\tag{2.2}
$$

The intended Memory meaning is the weighted accumulated output
$\int_0^T(t/T)^kCx(t)\,dt$, rather than an archive or a chosen inverse of
Space. Equation (2.2) is its acquisition implementation using existing
replies. No source integral command is part of the new installation.

There is a finite arithmetic construction of every weight. Expand
$L_i(t)=\sum_{r<\nu}\lambda_{ir}t^r$ by multiplying its displayed linear
factors, dividing only by the nonzero node differences. Then

$$
W_{ki}=\sum_{r=0}^{\nu-1}
\lambda_{ir}\frac{T^{r+1}}{k+r+1}.
\tag{2.3}
$$

Thus the integral in the specification of a weight requires no numerical
integration oracle. Rational nodes and $T$ give rational weights.

**Theorem 2.2 (same-trajectory finite integration refinement).** For every
source of Definition 1.1 and every actual window of Definition 1.2, the
finite receiver returns exactly

$$
\mu_k=\int_0^T(t/T)^kCE(t)x_0\,dt\quad(0\leq k<\nu).
\tag{2.4}
$$

Replacing separate nondisturbing ideal integrators by this receiver leaves
the entire actual field trajectory on $[0,T]$ and the held endpoint $z$
unchanged. It uses no second specimen, replayed source, future read or
state-restoration operation.

Proof. Each coordinate of $CE(t)x_0$ is a polynomial of degree below
$\nu$. Apply the distinct-node Lagrange interpolation identity, component
by component, with $\nu$ nodes, to get
$CE(t)x_0=\sum_iL_i(t)y_i$. This is the standard interpolation supplier,
with its exact degree and node hypotheses; it is not a new generic theorem.
Multiply by $(t/T)^k$ and integrate the finite sum. Equations (2.1) and
(2.2) give (2.4), including $\mu_0=Ty_0$ when $\nu=1$.
The only source operations are the original nondisturbing taps, start and
stop. The removed integrators were nondisturbing by their comparison
contract. Local arithmetic occurs while held. Therefore both installations
have $x(t)=E(t)x_0$ throughout the same active window and end at (1.2). ∎

The refinement is relative to a run which already pays for these sufficient
taps. It does not replace an arbitrary untapped continuous observation by
finite data. Nor does it implement an operation that was required to leave
the entrance $x_0$ unchanged: the actual endpoint is $E(T)x_0$.

For a concrete common run, take $B=J_2$, $C=(1,0)$, $T=1$ and the
actual initialized field $x_0=(2,3)$. Start, read at zero, read at one,
and stop. The two replies are $2,5$ and the actual endpoint is $(5,3)$.
Here $L_0(t)=1-t$, $L_1(t)=t$, so

$$
W=\begin{pmatrix}1/2&1/2\\1/6&1/3\end{pmatrix},\qquad
\mu=(7/2,2).
\tag{2.5}
$$

These are respectively the integrals of $2+3t$ and $t(2+3t)$ over the
performed interval, computed after holding $(5,3)$. If the original
alphabet includes duration two, actually calling it next advances this
same field to $(11,3)$ and returns $11$. The inverse of the moment
matrix first recovers entrance coefficients $(2,3)$; advancing by $T$
is essential to get the current field before that later call. This
example is a substitution into the general identities, not a numerical
experiment or a restriction of their real domain.

## 3. The attained coefficient images and the original moment chart

Put

$$
\mathcal O x=(CB^jx)_{0\leq j<\nu},\quad
K=\ker\mathcal O,\quad A=\operatorname{im}\mathcal O,
\quad a=\mathcal O x_0.
\tag{3.1}
$$

Indices of a block vector run from zero to $\nu-1$, each block in
$\mathbb R^p$. Scalar matrices below act on these blocks, equivalently
by tensoring with $I_p$. Define

$$
V_{ij}=\frac{t_i^j}{j!},\qquad
H_{kj}=\frac{T^{j+1}}{j!(k+j+1)},\qquad
U(t)_{j\ell}=\begin{cases}
t^{\ell-j}/(\ell-j)!,&\ell\geq j,\\
0,&\ell<j.
\end{cases}
\tag{3.2}
$$

Direct expansion gives

$$
y=Va,\qquad \mu=Ha,\qquad
\mathcal O E(t)x=U(t)\mathcal O x,\qquad W=HV^{-1}.
\tag{3.3}
$$

The last identity holds on the whole polynomial coefficient space, not
only on $A$: applying the interpolation formula to each monomial $t^j/j!$
shows $WV=H$.

The known Vandermonde supplier makes $V$ invertible: its determinant is
$\prod_{i<j}(t_j-t_i)/\prod_{j<\nu}j!$. The known Hilbert-moment supplier
makes $H$ invertible. In detail, with $G_{kj}=1/(k+j+1)$,

$$
H=G\operatorname{diag}(T^{j+1}/j!),\qquad
q^{\mathsf T}Gq=\int_0^1\left(\sum_{j<\nu}q_js^j\right)^2ds>0
\quad(q\ne0).
\tag{3.4}
$$

Only $G$ is claimed positive definite here. The scaled matrix $H$ is
generally nonsymmetric; invertibility of its factors does not assert
positivity of $q^{\mathsf T}Hq$. Likewise $W$ is invertible, but need not
have positive entries, preserve independent errors, or improve information.

The matrices $U(t)$ obey $U(t)U(s)=U(t+s)$ and $U(-t)=U(t)^{-1}$.
Equation (3.3), together with invertibility of $E(t)$, shows
$U(t)A=A$ and $E(t)K=K$. These identities follow either from the finite
exponential product or by collecting binomial coefficients. They fix
the phase change between entrance data and current data.

**Definition 3.1 (original orthonormal moment record).** Let
$\ell_0,\ldots,\ell_{\nu-1}$ be the original known orthonormal basis of
the real polynomials of degree below $\nu$ on $[0,1]$. Write

$$
\ell_k(s)=\sum_{j<\nu}D_{kj}s^j,\qquad
m_k=T^{-1/2}\int_0^T\ell_k(t/T)CE(t)x_0\,dt.
\tag{3.5}
$$

Then

$$
m=T^{-1/2}D\mu.
\tag{3.6}
$$

The matrix $D$ is invertible because these polynomials are a basis.
Consequently $m$ and $\mu$ have the same fibers, with exact inverse
$\mu=T^{1/2}D^{-1}m$. If the original numerical $m$ output is requested,
the receiver actually performs (3.6) and retains/exports that array. This
is a change of memory coordinates, not equality of their serialized bytes.
Arbitrary real coefficients of an orthonormal basis are not made finitely
computable by calling them known. The algebraic basis option in §6 supplies
a finite exact version without shrinking the real mathematical theorem.

## 4. Four meanings at the same completed cut

Keep the installation, source binding, charts, schedule, clock and rights
context fixed. The following are numerical views on actual completed-window
images, with their indicated independent meanings:

| View | Meaning at the held cut $z$ |
| --- | --- |
| Space $F_S(z)=z$ | Actual current material-field coordinates; no observation port is inferred. |
| Time $F_T(z)=V\mathcal O E(-T)z$ | Numerical contents of the performed ordered taps and their fixed timestamps/framing. |
| Boundary $F_B(z)=R_{\mathcal W}z$ | Current lawful finite endpoint-response family (1.6), including its original selector/reference. |
| Memory $F_M(z)=H\mathcal O E(-T)z$ | Acquired weighted accumulated output, together with its derived current predictor and retained callable binding. |

The extra predictor in Memory is a deterministic function of $F_M$ and
the fixed context, so it changes no fiber. Actual tap occurrences are
witnessed by the performed record. A numerical conversion recreates its
contents on this image, not a fresh historical occurrence, ACK, owner
grant or Return. No inverse below authenticates an arbitrary submitted
record or transfers another owner's right.

Write $D_{\mathcal W}$ for the block evaluation map

$$
(D_{\mathcal W}b)_w=\sum_{j<\nu}\frac{s(w)^j}{j!}b_j.
\tag{4.1}
$$

At the current cut $b=\mathcal O z=U(T)a$ belongs to $A$. Thus the actual
images are $VU(-T)A$, $HU(-T)A$, and $D_{\mathcal W}A$. They can be proper
subspaces of their ambient arrays; arbitrary arrays are not presumed to
be source records.

**Theorem 4.1 (exact common-cut recovery and its precise failure).** On the
entire real source domain of §1, Time and Memory have exactly kernel $K$
as maps of the current $z$. They mutually recover their numerical views
on their attained images. They always determine Boundary. Boundary recovers
them if and only if

$$
\ker R_{\mathcal W}=K,
\quad\text{equivalently}\quad
D_{\mathcal W}|_A\text{ is injective}.
\tag{4.2}
$$

A sufficient condition for (4.2) is that $\mathcal W$ contain $\nu$ words
with pairwise distinct totals $s(w)$. No necessity of that number is
asserted. Under (4.2), all four numerical views mutually recover if and
only if $K=\{0\}$. When $K\ne\{0\}$, the three equal-kernel views recover
the actual current behavior class $[z]\in\mathbb R^d/K$, and none recovers
full Space on this unrestricted domain.

Proof. The isomorphisms $V,H,U(T)$ in §3 give the explicit decoders

$$
y\longmapsto b=U(T)V^{-1}y,\qquad
\mu\longmapsto b=U(T)H^{-1}\mu.
\tag{4.3}
$$

Both land in $A$ on the specified images. Conversely, encode $b\in A$ as
$y=VU(-T)b$ and $\mu=HU(-T)b$. Their kernels on current states are $K$
because $E(-T)K=K$. Applying $D_{\mathcal W}$ yields Boundary. This
also proves its kernel contains $K$.

If Boundary recovers either other view, two current states with equal
Boundary must have equal $b$, so $\ker R_{\mathcal W}\subseteq K$.
Conversely (4.2) makes its attained-image decoder the unique map sending
$D_{\mathcal W}b$ to $b\in A$. It is computable by an exact finite linear
solve in the known matrices. Selecting $\nu$ distinct totals supplies
an invertible Vandermonde block acting on all coefficient arrays, which
is a sufficient special case. A smaller boundary can still be injective
on the smaller space $A$; the exact test is (4.2).

The map $[z]\mapsto\mathcal O z$ is a bijection from $\mathbb R^d/K$
onto $A$. Hence (4.3) and the Boundary decoder identify that actual class,
without selecting an allegedly actual hidden representative. If $K=0$,
compute a left inverse $L$ of $\mathcal O$ from $B,C$. Then the common
Space decoder is $z=Lb$; equivalently entrance recovery gives
$z=E(T)L a$. If $0\ne h\in K$, $z$ and $z+h$ have the same three
views and different Space, proving failure of full recovery. This is
the standard kernel/factorization supplier applied to these explicit maps,
not a new generic quotient construction. ∎

**Corollary 4.2 (route agreement).** Under (4.2), every conversion between
Time, Boundary and Memory consists of decoding the same $b\in A$ and
re-encoding it. Each conversion and its reverse compose to the identity
on their attained images, and every route between two views agrees. If
$K=0$, the same statement includes Space.

Proof. Each decoder just displayed is inverse to its corresponding
encoder on $A$. Cancelling each intermediate encoder/decoder pair proves
the assertion. For Space use $L\mathcal O=I$ and
$\mathcal O Lb=b$ for $b\in A$. All coordinates are at $z$, not at the
entrance. ∎

Without (4.2) there is still the one-way map from Time or Memory to the
specified finite Boundary; claiming mutual recovery for that Boundary
would silently strengthen its observations. Conversely replacing the
full timing task by only that finite boundary would silently weaken the
original task. Neither replacement is used here.

## 5. Callable continuation on this specimen and the legitimate quotient

**Theorem 5.1 (installed continued use and exact future kernel).** Retain
the acquired data and the current predictor $b=U(T)H^{-1}\mu$. For every
actual legal timing action, use the retained source binding to forward
the action to the same held specimen, consume its complete actual reply,
and commit

$$
b\leftarrow U(s_a)b.
\tag{5.1}
$$

The invariant is $b=\mathcal O z$ at every completed cut. In particular
the predicted reply $b_0$ after the update equals the actual reply $Cz$.
The invariant holds for every sufficiently backed finite adaptive
continuation of Definition 1.3, with its actual source successors.

If some original $s_a>0$, equality of all future output responses is
exactly equality modulo $K$. If all original durations are zero, that
task's kernel is instead $\ker C$; the acquired coefficient quotient
can then be strictly finer than the full timing task needs. These
statements do not require a separating finite $\mathcal W$.

Proof. Before a call suppose $b=\mathcal O z$. The actual successor is
$z'=E(s_a)z$, so (3.3) gives
$\mathcal O z'=U(s_a)b$. Its zeroth block is $Cz'$, proving both the
update and reply assertions. Endpoint Read and Hold have the corresponding
identity update. Serial exclusion and hold ensure no unrepresented source
advance during local processing. Genuine rights and the existing framing
determine the same legal next action and complete fixed control replies.
Induction over completed calls proves the invariant and equality of
replies. Equal earlier replies make a common adaptive policy select the
same next permitted action/input; conditioning on its common tape gives
the same pointwise proof for randomized policies. Pending processing
retains its phase until completion; this theorem's recovery square is
asserted at completed cuts, not at every internal arithmetic microcut.

If $h\in K$, every $CE(s)h$ vanishes and $E(s)h\in K$. Thus the quotient
updates and all permitted replies are well defined for every finite word.
For the converse, if $s_a>0$, compare the readouts after $a^k$ for
$0\leq k<\nu$, using the endpoint read at $k=0$. Equality means the
polynomial $CE(t)h$ vanishes at $\nu$ distinct values $ks_a$; interpolation
makes it identically zero, hence $CB^jh=0$ for all $j<\nu$. If every
$s_a=0$, all successors are the identity and every output is just $Cz$,
giving exactly $\ker C$. ∎

The descended state in the nontrivial case is an actual behavior class,
not a fictional full field. Two different actual representatives remain
different physical successors while their classes and disclosed replies
agree. A task demanding their literal full coordinates, hidden actuator
responses or a different action menu has to retain the missing distinctions.

An installed finite consumer can implement (5.1) by forming the upper
triangular scalar matrix in (3.2), multiplying block vectors and writing
a destination predictor before committing it. In the rational scope of
§6 this is an ordinary terminating exact program, with actual finite
buffers. For example, a common selector can compare a retained rational
read with a supplied rational threshold, choose one of the original
actions, construct its request, forward it, and consume the returned
endpoint. The induction covers both branches without access to $x_0$.
This is a callable use procedure under the installed contract, not merely
an existence statement about a decoder.

After active duration $s$ beyond acquisition the actual state is
$E(T+s)x_0$ and the current predictor is $U(T+s)a$. The original tap
window and $\mu$ remain historical records. A shifted output polynomial
can be calculated, but that calculation is not a new performed window.
For a fresh window one must actually execute the timed reads and stop
again, charge them, and apply Theorems 2.2 and 4.1 to its new entrance
and advanced endpoint. Arbitrary earlier histories are not recoverable
from the later field: inserting extra Hold or endpoint Read operations
leaves that field unchanged and changes the journal.

## 6. Exact implementation scope and the same-run resource difference

**Definition 6.1 (finite rational/algebraic scope).** Restrict $B,C,x_0,T$,
the tap nodes and action durations to rationals, still with $B^\nu=0$,
distinct nodes and $T>0$. One admissible schedule is
$t_i=iT/(\nu-1)$ for $\nu\geq2$. The source replies, weights, moments,
predictors and any requested full-state left inverse are rational.
In this finite representation scope, commission the same sensor to
deliver its exact replies as rational packets, and supply $B,C$, nodes
and durations in that format. This paid serializer is common to both
compared installations; rationality of an abstract real port alone does
not construct it. Represent each rational by a sign, reduced numerator
and positive denominator with self-delimiting integer fields. Parsing, equality,
addition, multiplication, division by checked nonzero entries and exact
elimination terminate on each finite input. Coefficients are constructed
from the supplied matrices/nodes, never private advice about $x_0$.

For an explicit finite version of the original normalized record, apply
Gram--Schmidt in order to $1,s,\ldots,s^{\nu-1}$ with inner product
$\langle s^i,s^j\rangle=1/(i+j+1)$. At step $k$, subtract the projections
onto the preceding normalized polynomials and divide by the positive
square root of the resulting squared norm. The residual still has
degree $k$ and leading coefficient one, so (3.4) makes that norm
strictly positive. All inner products are finite coefficient sums;
successively adjoining these finitely many square roots, and $T^{1/2}$,
gives a finite real algebraic extension in which (3.6) is exact.
The familiar orthonormal basis is a supplier, not new mathematics here.
An already supplied basis with arbitrary real
constants retains the real identity (3.6) but has no automatic finite
encoding. The entire real domain of §§1–5 remains an exact-scalar
mathematical model; it is not reduced to this rational subfamily.

**Proposition 6.2 (apparatus removal with an explicit local bill).** Compare
the following two executions on the same commissioned source and same
actual initial state. Both use Definition 1.2's sufficient taps. The
comparison execution additionally uses $\nu p$ nondisturbing ideal
weighted-integrator channels for (3.5) throughout $[0,T]$ and receives
their $\nu p$ terminal scalars $m$. The receiver execution uses (2.2)
and then (3.6) to deliver that original payload. If the requested memory
interface is instead the revised monomial chart, it stops at $\mu$;
the chart change and the omitted conversion are then explicit.
Both deliver the same requested moment chart, endpoint and all actual
continuation replies. The latter has zero such integrator channels and
zero terminal integrator-source replies. It adds the finite filter's
construction, arithmetic and storage, as follows.

| Same-run coordinate | Common or receiver-specific bill |
| --- | --- |
| Preparation | Same actual initialization, known-law commissioning, clock/origin, bindings, grants, code and source backing; none is assigned zero cost. |
| Acquisition source calls | One FlowStart, $\nu$ vector taps, one FlowStop and active duration $T$, in addition to initialization. A scalar-only sensor pays $\nu p$ scalar transactions with its different framing. |
| Removed apparatus | $\nu p$ active integrator channels, their initialization/support and $\nu p$ separately acquired terminal scalars. |
| Weight setup | Multiply the linear factors in (2.1), divide by their nonzero differences, then use (2.3). Dense coefficient multiplication and the final sums take a sufficient $O(\nu^3)$ scalar-operation budget; their work and stored coefficients are paid. |
| Specified dense filter | Zero $\nu p$ destination scalars; for each $k,i,r$, multiply $W_{ki}y_{ir}$ and add it to that destination, including zero entries. Exactly $\nu^2p$ scalar multiplications and $\nu^2p$ scalar additions, plus the zero writes and actual loads/stores. |
| Original chart output | When $m$ is required, precompute $T^{-1/2}D$ and apply the same dense zero-and-accumulate convention: another $\nu^2p$ multiplies and $\nu^2p$ additions, destination writes and actual loads/stores. Constructing the algebraic coefficients is paid setup. |
| Optional other output | A requested Boundary array or full Space adds its coefficient matrices, solves, arithmetic, destination and export. No such output is silently free. |
| Actual continuation | Same selected action calls, durations and complete source replies; local update work (5.1), buffers, parsing and retained consumer state coexist. |

Proof. Theorem 2.2 gives equality of the moment values and the actual
window endpoint. Equation (3.6) gives the original normalized chart when
requested. Theorem 5.1 gives equality along the actual continuation, by
induction with the same adaptive selectors. The comparison integrators
have no source-disturbing effect, so their removal changes no source call
or transition. The stated filter schedule has one multiply and one add
for each of $\nu^2p$ triples. Constructing each Lagrange numerator by
successive linear-factor multiplication uses $O(\nu^2)$ operations;
doing so for $\nu$ nodes and then the $\nu^3$ weight terms gives the
stated sufficient setup budget. These are arithmetic counts for this
specific receiver, not bounds on bit operations or physical time. ∎

During the filtering, count simultaneously the actual source field and
its update backing; $B,C$; the nodes and $\nu^2$ weights if stored; the
$\nu p$ actual tap payloads; the $\nu p$ moment destinations; current
predictor and destination/scratch; clock/phase; code, parser, references,
rights and communication buffers. If Time and Memory are both retained,
both payload arrays remain charged. An optional Space solve adds its
left-inverse matrix and state buffers. Scratch may be reused after its
last consumer; retained caller copies and still-live exports cannot be
replaced by separate maxima.
When the original $m$ payload is produced out of place, its $\nu p$
destination scalars coexist with $\mu$ until that conversion completes;
if both charts are retained, both survive as additional charged arrays.

For any chosen self-delimiting rational encoding let $\lambda(q)$ be
the length of its actual reduced rational packet. Tap traffic is
$\sum_{i,r}\lambda(y_{ir})$, together with actual requests, node/clock
fields, tags, ACK, End and Return packets. Add commissioning/law handoff,
selector operands, every continuation reply and every actual export with
its copy multiplicity. Moments computed locally are not extra source
responses. Sending them is still traffic. Source, mailbox and receiver
copies coexist whenever the installed channel protocol requires them.
No universal exact finite-binary length is assigned to arbitrary real
replies. Genuine owner/token copying is a premise here; the PR57/PVC
primitive implementations are not asserted to implement this sensor.

Rational and algebraic widths are finite per instance and unbounded
across inputs and continuation lengths. A finite program does not imply
bounded lifetime memory, fixed precision, finite physical exhaustion
margin or a uniform time bound. Local elapsed time, energy, commissioning,
clock realization and source support remain actual resource coordinates;
no numerical values for those physical coordinates are asserted.

For prediction alone, retaining the sufficient taps and using (4.3)
without creating a moment array is the cheaper sufficient alternative
in added filtering work. The purpose of (2.2) is to provide the specified
integrated-memory interface while removing its extra ideal measurement
apparatus. The invertible recoding creates no information. The two full
resource vectors have different apparatus and computation coordinates;
there is no claimed total-cost or Pareto dominance over tap retention.

## 7. Sharp scoped boundaries

The following scalar count applies the standard finite-observability rank
argument to an attained polynomial chain. It delimits the sufficient tap
count; it is not an additional new lower-bound principle.

**Proposition 7.1 (a scalar linear information lower bound).** For
$d=\nu$, let $B=J_\nu$ have ones on the superdiagonal and zeros elsewhere,
and $C=e_0^{\mathsf T}$. Every polynomial of degree below $\nu$ occurs
as $CE(t)x_0$. For this class, fewer than $\nu$ fixed scalar linear
replies cannot recover full Space, or the entire timing task when the
original alphabet contains a positive duration. The $\nu$ taps achieve
this information count.

Proof. The output is $\sum_{j<\nu}t^j(x_0)_j/j!$, so
$\mathcal O=I$ and the polynomial coefficients range freely. Fewer than
$\nu$ fixed linear functionals have a nonzero common kernel. The
endpoint map $E(T)$ is invertible, and Theorem 5.1 makes the full timing
task separate all states when a positive duration exists. A nonzero
kernel therefore prevents either recovery. Distinct-node taps are
invertible by §3. ∎

This lower bound is for fixed scalar linear replies on this unrestricted
class and task. It is not a lower bound for all nonlinear encodings,
adaptive acquisition models, redundant multi-output channels, scalar
packet bit lengths or total costs. In general the dimension of $A$ can
be smaller than $\nu p$.

**Example 7.2 (insufficient actual taps).** With $B=J_3$, $C=e_0^{\mathsf T}$
and entrance difference $h=(0,1,-2)$, the output difference is $t-t^2$.
Taps at $0,1$ agree, while the read at $2$ differs by $-2$. Thus a
receiver given only those two replies cannot compute the complete
degree-below-three moment record or the full timing behavior. This is
not a failure of the sufficient $\nu$-tap protocol.

**Example 7.3 (blind Space and a too-small Boundary).** With $B=0$ and
$C=(1,0)$, every allowed output ignores the second coordinate. The
three output views still interconvert, whereas full Space fails. In
the observable $J_2,e_0^{\mathsf T}$ source, a boundary containing only
zero-total words sees only the first current coordinate, despite the
two acquired taps determining both. This separates the exact criterion
(4.2) from a blanket assertion about every finite boundary. If all
action durations are zero, even the full timing task has that smaller
kernel, as Theorem 5.1 states.

**Example 7.4 (clock and history are not recovered from a field).** In
the source $B=0$, the same field occurs at every elapsed duration. A
state inverse cannot discover an unknown duration. Even with a fixed
known positive duration, arbitrary extra Hold/read histories can have
the same endpoint. Theorem 4.1 instead uses the fixed actually performed
window, its known phase and common installation context. It does not
invert erased arbitrary history or infer event provenance from numbers.

**Example 7.5 (degree and law promises matter).** Outside the declared
nilpotent class, take $B=\operatorname{diag}(0,1)$, $C=(1,1)$, $T=1$.
The one constant moment sends $h=(e-1,-1)$ to zero, whereas its endpoint
output is $-1$. Also the two scalar sources $(B,x_0)=(0,1)$ and
$(1,1/(e-1))$ have the same constant integral one and different endpoint
outputs. These compare stronger proposed promotions, not members of
the theorem's fixed known-$B$ class. Neither a general exponential
trajectory nor an unknown law is supplied by the finite filter.

No ancillary noise theorem is used: all equalities concern the declared
exact replies. If actual taps have errors $\eta$, (2.2) transforms their
error to $W\eta$; it does not supply independent Gaussian moment channels
or any of the accuracy/cost premises of a different instrument.

## 8. Supplier correspondence and the remaining programme

The comparison below concerns definitions, hypotheses and proofs in the
named source scopes. It does not infer novelty from an absent API name,
transport hashes or an unrelated-source census.

| Supplier | Reused content and exact boundary of the transfer |
| --- | --- |
| Berrut and Trefethen, *Barycentric Lagrange Interpolation*, SIAM Review 46 (2004), §2, equations (2.1)–(2.2), pp. 501–503, [primary paper](https://people.maths.ox.ac.uk/trefethen/barycentric.pdf), DOI 10.1137/S0036144502417715 | `literature-attested`: distinct-node interpolation of degree-bounded polynomials and its basis. Applied to the actual output polynomial in Theorem 2.2, then integrated. No new interpolation or quadrature principle, conditioning improvement or physical acquisition theorem is claimed. |
| Pinned mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, [LinearAlgebra/Lagrange.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Lagrange.lean), `basisDivisor`, `Lagrange.basis`, `interpolate`, `eval_interpolate_at_node`, `eq_interpolate` | Finite field-valued basis, evaluation and degree-bounded uniqueness. The hypotheses are injective node indexing and degree below node count. Their proofs supply the polynomial identity; no source ports, stop or rights appear in them. |
| [FiniteVandermondeTomography](../../../D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography.lean), with its owning Blueprint Scribe | `finiteMomentReadout`, distinct-node determinant, injectivity and equality iff amplitudes agree. Its row-vector power-moment map is transposed/scaled to the polynomial coefficient evaluation $V$ here; the invertibility ingredient is reused, not renamed as a new finite tomography theorem. |
| [HilbertMomentCoercivity](../../../D5/S3/Observer/Linear/HilbertMomentCoercivity.lean), with its owning Scribe and polynomial-energy proof helpers | `hilbertMoment`, `hilbertMoment_posDef` and polynomial-energy positivity supply (3.4). The present scaling uses an invertible diagonal factor. No positivity claim is transferred to the nonsymmetric $H$. |
| [FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean), with its owning Scribe | Kernel/rank/Gram equivalence for its finite stacked discrete readout. Here the explicit stack is $(CB^j)_{j<\nu}$ and determines the actual output polynomial. It does not commission the continuous sensor or acquire $B,C$. |
| [ObservableTrajectoryCoordinates](../../../D5/S3/Observer/Linear/ObservableTrajectoryCoordinates.lean), with its owning Scribe | The Lean source's continuous $L^2$ trajectory map, observability hypothesis, actual image and basis-coordinate inverse supply the trajectory-coordinate viewpoint. Its Scribe separately describes finite polynomial moments and their Gramian. Neither is asserted to be a finite-tap receiver theorem. A general exponential trajectory is not a polynomial; its full Gramian is not identified with arbitrary finite monomial moments. |
| [FutureReadoutQuotient](../../../D5/S3/ObserverMemory/Dynamics/FutureReadoutQuotient.lean) and [PredictiveMemoryMinimalQuotient](../../../D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.lean), with their owning Scribes | The all-future kernel quotient, unique descended dynamics, and factorization through attained memory ranges are existing suppliers. The latter has separate readout-factorization and update-factorization premises. Equations (3.3), (4.3) and (5.1) verify those premises for this source; they do not contribute a new generic quotient principle. |
| [Recovery Geometry](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md), §§1.1–1.4 and 2.1–2.2 | Finite evaluation pairing, fiber/kernel factorization, actual-image targets and the full-carrier versus restricted-region distinction already supply the generic recovery criterion. Its weighted coefficient costs and noise-box minimax theorem are not asserted to price the present sensor. Theorem 4.1 instantiates the noiseless fiber criterion on the stated full real carrier. |
| [Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §§1–3 and §37 | Actual partial-process legality, response fibers, compatible successors, adaptive common-source induction, and the fixed-exponent/actual-image limit of history inversion. The continuous field and its tap/stop contract are explicitly different from its ordered-tree reciprocal map. |
| [NCR](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md), §§1–7 | Actually acquired native seed, fixed deterministic controller, paid clocks, actual-image inverses and continued Fetch/copy use. Its full native history is reconstructed only with its own acquired seed and phase. No such seed, tree generator or primitive implementation is borrowed here. |
| [PVC](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md), §§1–7 | Actual retained backing, installed converter, legal imports, complete copies, ACK/return and task-kernel distinctions already supply paid view conversion. Their original owner-approved Ready/installation contract is not eliminated by numerical inversion in this volume. |
| [PR57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §57, especially D5–D9 and T1–T5 | Paid material supply, literal source schedules, causal complete trace, actual copying, whole-fiber verification, consumer and same-execution costs. Its source remains the original capacity-guarded tree with the original $q_H$, not this continuous flow. Its implementation cannot be relabeled as an implementation of an exact real sensor. |
| [Native Callable Storage Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md), §§1–2 and 5–7; [Structural Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md), Definition 13.7 | Genuine retained material, activation/input frontier, actual-history replay, callable acquired package and independently defined structural views. Their selected material is across actual owners, not automatically receiver-readable. No observer-wide scan, installation or authority is obtained here from a numerical coordinate change. |
| [Cyclic Leaf Boundary Ambiguity](RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_LEAF_BOUNDARY_AMBIGUITY.md), §§21–22 | Public unknown-gain acquisition, synchronized complete continuation and completed-Report four-view recovery already establish the phase/endpoint distinction: Report advances the field, a bare forecast supplies no new Report, and arbitrary journals are not recovered. Its symmetric rational native Tick/Add/$Q_g$ service is different. The present result does not earn that law, replace Tick by $e^{tB}$ or strengthen its residual native-recovery class. |
| [Original-source timed release recovery](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_SOURCE_TIMED_RELEASE_RECOVERY.md), §§1–6 | Actual stopping-time arrivals disclose their current points; finite fixed-scale banks retain a diffuse deterministic-cut posterior, and countable same-path refinement is not finite acquisition. Those diffusion/clock/service hypotheses are preserved. Deterministic exact polynomial interpolation is not a proof of that diffusion's finite exact recovery. |

The source-local `repo-derived` content is Theorem 2.2's concrete removal
of the additional integral apparatus from the already-tapped window,
Theorem 4.1's exact current-cut images and deficient-observability case,
their agreement with the entire original timing task in Theorem 5.1,
and Proposition 6.2's coexisting receiver/source/resource account. These
compose the credited ingredients under the stated source contract.
No worldwide originality, exhaustive absence result, new formalization,
required-check result or publication success is asserted.

The result does not construct an unknown-source initialization, a universal
alpha/beta reduction, a native Tick realization, an unknown generator,
a held-entrance moment instrument or a physical continuous apparatus.
Alpha/beta remains a candidate foundation in its own models. Every
fixed-$G_{gc}$/original-$Q$/parked-consumer/unchanged-initialization/
original-terminal/final-no-Ready obligation retains its exact scope and
remains unsettled by this different model. Arbitrary erased chronology,
full Space in a blind sector, independently noisy moment sensors, total
cost optimality and the unchanged full through-2027 common-source
programme are not completed by this conditional refinement.

## 追加锚（本行以下为增补区）
