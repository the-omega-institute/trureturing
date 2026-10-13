# FIB atomic recursive holographic boundary geometry V: exact signed-state renewal obstruction

## 114. Static linear transport across an actual accepted rho step

### 114.1 The original source, comparison class and literal witness

**Definition 114.1 (the unrestricted static linear compatibility question).**
Use the entire finite free ordered source algebra $\mathcal T$, its actual
$\rho$, all occurrence addresses and counting inner products of
[Continuation IV, Definitions 92.1 and 112.1--112.2](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md).
For each current source $s\in\mathcal T$, put

$$
\mathcal V_s=\mathbb R^{V_s},\qquad
(L_sf)(p)=\sum_{q:\{p,q\}\in E_s}(f(p)-f(q)),\qquad
\mathsf c_sf=f(\varepsilon).
\tag{114.1}
$$

Every vertex has mass one, every actual edge has conductance one, and
there is no killing or grounding term. Equal subtree values at different
addresses remain different vertices. In an actual history with immutable
INITIAL $u$, the current value is $s=\rho^e u$, where $e$ counts accepted
updates. The successor in this definition is used only for a genuinely
accepted Apply. The two comparison spaces do not assert two simultaneously
available native registers.

For any fixed $a,b>0$, a compatible pair is a time-independent real-linear
map $T:\mathcal V_s\to\mathcal V_{\rho s}$ and a deterministic function
$\theta:[0,\infty)\to[0,\infty)$ taking finite values, with $\theta(0)=0$,
such that

$$
e^{-b\theta(t)L_{\rho s}}T=T e^{-atL_s}
\qquad\text{for every }t\ge0.
\tag{114.2}
$$

The map and clock may depend on the actual source and history. No locality,
positivity, norm or mass preservation, old-coordinate retention, continuity
or differentiability of the clock is imposed. The clock is one scalar
function for all signed inputs of this pair. Injectivity means injectivity
on the entire all-occurrence space, including constants and every
mean-zero direction. The question is whether such injective pairs can be
assigned to every genuine accepted step on the original domain.

The original operations and permission outputs remain exactly
[Contract 112.1a](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md).
The uncapped native menu is Read at any finite address, serial Apply-$\rho$
on the same root register, and absorbing Stop; every native Apply is
accepted. In a separately declared guarded extension a common total
effective $G(\gamma,e,H)$ returns accepted or refused from the common
parameter, actual accepted epoch and complete chronological history.
Acceptance installs exactly $\rho s$; refusal leaves source and epoch
unchanged. Repeated and absent Reads are actual calls with their actual
four-valued replies. Stop executes no suffix. An attempt is not evidence
of acceptance, and $G$ has no hidden source or occurrence-object input.
Allowing $T$ to depend on a source does not install that source as
controller advice or as a permission oracle.

**Definition 114.2 (the actual branching witness and full matrices).**
Take the actual original values

$$
u=\langle\alpha,\beta\rangle,\qquad
\rho u=\langle\beta,\langle\beta,\alpha\rangle\rangle.
\tag{114.3}
$$

They are connected by one legal accepted Apply under the uncapped native
contract, and under any declared guard that actually accepts this attempt.
Their full addressed labels, masses and edges are

$$
\begin{aligned}
V_u&=(\varepsilon,L,R),&
\lambda_u&=(\mathsf{branch},\alpha,\beta),&N_u&=3,\\
V_{\rho u}&=(\varepsilon,L,R,RL,RR),&
\lambda_{\rho u}&=(\mathsf{branch},\beta,\mathsf{branch},\beta,\alpha),&
N_{\rho u}&=5,\\
E_u&=\{\{\varepsilon,L\},\{\varepsilon,R\}\},\\
E_{\rho u}&=E_u\sqcup\{\{R,RL\},\{R,RR\}\}.
\end{aligned}
\tag{114.4}
$$

In precisely these coordinate orders write $A=L_u$, $B=L_{\rho u}$:

$$
A=\begin{pmatrix}
2&-1&-1\\-1&1&0\\-1&0&1
\end{pmatrix},\qquad
B=\begin{pmatrix}
2&-1&-1&0&0\\
-1&1&0&0&0\\
-1&0&3&-1&-1\\
0&0&-1&1&0\\
0&0&-1&0&1
\end{pmatrix}.
\tag{114.5}
$$

These are the actual birth blocks of (112.9), with beta-parent mask
$H=\operatorname{diag}(0,0,1)$ and child-parent incidence
$C=\begin{pmatrix}0&0\\0&0\\1&1\end{pmatrix}$, a $3\times2$ matrix.
Thus the old principal block is $A+2H$, the two new diagonal entries
are one, and the full zero-parameter old-set Schur complement is $A$.
The degrees are $(2,1,1)$ and $(2,1,3,1,1)$; no incident edge is removed.
Labels remain part of the source even where the old operator alone does
not distinguish them. In particular the reversed labelled source has the
same old matrix but births at $L$, not at $R$, as Proposition 112.4a shows.

### 114.2 Nonexistence without a clock regularity assumption

**Theorem 114.3 (sharp rank and lost mean-zero dimension).** For the
actual pair (114.3), every $a,b>0$ and every compatible $(T,\theta)$ of
Definition 114.1 satisfy

$$
\operatorname{rank}T\le2,\qquad
\dim\bigl(\ker T\cap\mathbf1_3^\perp\bigr)\ge1.
\tag{114.6}
$$

The maximum rank is exactly two. Every rank-two compatible map loses
exactly one of the two old mean-zero dimensions and has a one-dimensional
kernel lying in that mean-zero space. Consequently an assignment of
injective compatible pairs to every original accepted step does not exist,
even when source and history dependence are allowed.

Proof. Use ordinary finite real-symmetric spectral calculus, as already
used for the complete occurrence states in Theorem 103.2. The invariant
spectral-subspace argument is mature: in the stochastic setting see
Avena--Castell--Gaudilliere--Melot,
[*Approximate and exact solutions of intertwining equations through random
spanning forests*, arXiv:1702.05992v1](https://arxiv.org/abs/1702.05992v1),
§2.2, Lemma 10. There the link is a nondegenerate rectangular stochastic
matrix, the original kernel is reversible and irreducible, and the
smaller kernel inherits a subset of its spectrum with bounded
multiplicities. No stochastic-link or positivity hypothesis is imposed
on the present $T$; the spectral calculation below supplies the needed
comparison with the permitted arbitrary scalar clock.

The old eigenbasis is

$$
v_0=(1,1,1),\qquad v_1=(0,1,-1),\qquad v_3=(2,-1,-1),
\qquad Av_\lambda=\lambda v_\lambda.
\tag{114.7}
$$

Suppose $Tv_\lambda\ne0$ for one of $\lambda=1,3$. Expand this image
into the full eigenspaces of $B$. For any nonzero component at a target
eigenvalue $\mu$, (114.2) implies, for every $t\ge0$,

$$
e^{-b\mu\theta(t)}=e^{-a\lambda t}.
\tag{114.8}
$$

At any $t>0$ the right side is strictly less than one, so $\mu>0$.
Injectivity of the real exponential gives

$$
\theta(t)=\frac{a\lambda}{b\mu}\,t\quad(t\ge0),\qquad
Tv_\lambda\in\ker(B-\mu I).
\tag{114.9}
$$

The second assertion follows because the same identity forces every other
nonzero spectral component to have this identical $\mu$. Thus one
retained decaying mode already forces a strictly positive linear clock,
without first differentiating it, assuming additivity, or imposing any
regularity. If both old positive modes survive, their target eigenvalues
must satisfy $\mu_3=3\mu_1$.

For the literal successor matrix, expansion of its characteristic
determinant gives

$$
\det(xI-B)=x(x-1)q(x),\qquad
q(x)=x^3-7x^2+13x-5.
\tag{114.10}
$$

Here $q(1)=2$. Its signs at rational endpoints are

$$
\begin{aligned}
q(1/2)&=-1/8,&q(3/5)&=62/125,\\
q(2)&=1,&q(5/2)&=-5/8,\\
q(4)&=-1,&q(9/2)&=23/8.
\end{aligned}
\tag{114.11}
$$

The three disjoint sign changes exhaust the degree-three polynomial,
so its roots are simple and lie, one each, in
$(1/2,3/5)$, $(2,5/2)$ and $(4,9/2)$. Together with the simple
eigenvalue one these exhaust the positive spectrum of $B$.
Multiplying those four possible locations by three gives
$(3/2,9/5)$, $\{3\}$, $(6,15/2)$ and $(12,27/2)$.
None meets a possible positive spectral location. Hence $B$ has no
positive pair in ratio three. Both old decaying eigenvectors cannot
survive the same clock.

At least one of $v_1,v_3$ is therefore killed, proving both inequalities
in (114.6). If rank is two, the constant vector and exactly one positive
mode must survive: retaining both positive modes is impossible and their
three eigenvectors exhaust the old space. The surviving positive mode
forces (114.9). Applying (114.2) to $v_0$ then places $Tv_0$ in
$\ker B=\mathbb R\mathbf1_5$. Its nonzero constant image and the
positive-eigenvalue image are independent. The remaining old positive
eigenvector spans the full kernel, proving the exact dimension statement.
If neither positive mode survives, rank is at most one, including the
case $\theta\equiv0$; no discarded-clock case permits rank three.
The rank-two construction in Theorem 114.4 below proves attainability.

The witness is itself in the full branch entry fiber (112.1), not a
replacement domain. It is legal in the uncapped original service. Any
purported full-domain assignment must supply a rank-three map for this
step, contradicting (114.6). This refutes the universal assignment,
not the existence of an injective map for each individual different
source. For example a source with no beta leaf has no born edge and
unchanged $L$ at that step; $T=I$, $\theta(t)=at/b$ then works.
$\square$

### 114.3 Complete root response at the sharp rank ceiling

**Theorem 114.4 (root-readout sufficiency and its exact missing direction).**
For each of the three real roots $\mu$ of $q$ in (114.10), define

$$
\begin{aligned}
w_\mu&=(2,\ \mu^2-6\mu+7,\ -\mu^2+4\mu-3,\ \mu-3,\ \mu-3),\\
m(f)&=\frac{f(\varepsilon)+f(L)+f(R)}3,\\
d(f)&=\frac{2f(\varepsilon)-f(L)-f(R)}6,\\
T_\mu f&=m(f)\mathbf1_5+d(f)w_\mu,\qquad
\theta_\mu(t)=\frac{3a}{b\mu}\,t.
\end{aligned}
\tag{114.12}
$$

This is a compatible pair of rank two, with

$$
\ker T_\mu=\mathbb R(0,1,-1),\qquad
T_\mu\mathbf1_3=\mathbf1_5,\qquad
\mathsf c_{\rho u}T_\mu=\mathsf c_u.
\tag{114.13}
$$

It preserves the complete root output for every signed old input and
every comparison time:

$$
\mathsf c_{\rho u}e^{-b\theta_\mu(t)B}T_\mu f
=\mathsf c_u e^{-atA}f
=m(f)+2d(f)e^{-3at}.
\tag{114.14}
$$

Conversely, every compatible pair satisfying this complete root-output
identity for all $f,t$ is one of (114.12). Thus root-output sufficiency
can hold at the sharp rank ceiling while full-state sufficiency fails.

Proof. Direct multiplication in the actual five coordinates gives

$$
Bw_\mu-\mu w_\mu=(0,-q(\mu),q(\mu),0,0)=0,
\qquad \sum_{p\in V_{\rho u}}w_\mu(p)=0,
\qquad w_\mu(\varepsilon)=2.
\tag{114.15}
$$

Every old signed field has the exact decomposition

$$
f=m(f)v_0+\frac{f(L)-f(R)}2v_1+d(f)v_3.
\tag{114.16}
$$

Formula (114.12) sends $v_0$ to $\mathbf1_5$, $v_1$ to zero and
$v_3$ to $w_\mu$. The two nonzero images are independent because one
is constant and the other has positive eigenvalue and nonzero root
coordinate. Hence the rank and kernel in (114.13) are exact. The
successor exponential is constant on the first image and multiplies the
second by $e^{-b\mu\theta_\mu(t)}=e^{-3at}$, proving (114.2).
At the root $m(f)+2d(f)=f(\varepsilon)$, proving (114.13)--(114.14).
The entire killed direction is mean-zero and root-invisible under every
old heat time, rather than a constant-mode discrepancy.

For the converse, the root-output identity at $t=0$ requires
$\mathsf c_{\rho u}T=\mathsf c_u$. In particular $Tv_3$ and $Tv_0$
are nonzero. Theorem 114.3 forces $Tv_1=0$, the linear clock
$\theta(t)=3at/(b\mu)$, and $Tv_0\in\mathbb R\mathbf1_5$.
The root constraint fixes $Tv_0=\mathbf1_5$ and $(Tv_3)(\varepsilon)=2$.
The successor eigenvalue one has eigenspace
$\mathbb R(0,0,0,1,-1)$ and is root-invisible, so it cannot be this
$\mu$. Each other positive eigenspace is simple by (114.10)--(114.11),
and its root-normalized vector is exactly $w_\mu$ of (114.15).
This fixes all three old basis images and proves the converse.
$\square$

**Definition 114.5 (transported input versus the successor's own impulse).**
The complete root-output identity in (114.14) compares the transported
old input $T_\mu f$ with the same old $f$. In particular it gives

$$
\begin{aligned}
T_\mu\delta_\varepsilon&=\tfrac13\mathbf1_5+\tfrac13w_\mu,\\
\mathsf c_{\rho u}e^{-b\theta_\mu(t)B}T_\mu\delta_\varepsilon
&=\tfrac13+\tfrac23e^{-3at}.
\end{aligned}
\tag{114.17}
$$

It does not equate this experiment to the successor's own unit root
impulse. The latter has limiting root weight $1/5$, while the old
unit impulse has limiting root weight $1/3$, by the exact constant-mode
formula (103.5). Under $\theta_\mu(t)\to\infty$ these untransported
responses therefore cannot be equal. More generally
$\sum_p T_\mu f(p)=5m(f)$ whereas $\sum_p f(p)=3m(f)$:
this permitted map preserves constant values, not counting mass or norm.
There is no change of vertex masses to disguise this discrepancy.
No positivity or physical preparation of $T_\mu\delta_\varepsilon$ is
assumed. The distinction concerns precisely the same source-operation
pair, not an unrelated scalar-memory model.

### 114.4 Paid source correspondence, original target and retained boundaries

**Definition 114.6 (acquiring the witness without source advice).**
Use the authentic branch entry and complete access cut of Definition
112.1: the supplied pre-entry record is one actual root Read with reply
branch, the old root-cut row is constant, and the initial fiber is all
branch sources. No count, tree name or beta mask is supplied at entry.
Conditional on that authentic stationary epoch-zero register, reuse the
reply-driven acquisition phase and report-only restoration of §112.5
and Proposition 113.9. Its supplier is
`ActualTreeReadoutAcquisition`, with its own immutable four-valued queries,
distinct-address charge and original Boolean task unchanged; this is a
different consumer of its acquired description.

On the actual witness the root-first phase reads
$\varepsilon,L,R$ and obtains branch, alpha, beta. It does not know
in advance that the size will be three: actual branch replies enqueue
children and actual leaf replies enqueue none. From this acquired ordered
description the controller may calculate the sizes, beta mask, matrices
and source-indexed candidate maps locally. Such calculation grants neither
an actual Apply nor a signed-field operation. The sufficient phase
coordinates, inherited rather than optimized here, are

$$
(q,a,\ell,k_{\rm phase})=(3,0,2,3).
\tag{114.18}
$$

Here $q$ counts raw native Read invocations, $a$ counts Apply attempts,
$\ell$ sums literal Read-address lengths and $k_{\rm phase}$ counts
distinct addresses in this empty supplier phase. Retaining the pre-entry
root event as well gives four raw Reads, total literal length two, and
three cumulative distinct addresses on one immutable-source ledger.
The post-entry distinct increment on that ledger is two. Separate empty
phase ledgers instead have charges one and three. The root was called
twice; these are different raw and distinct-address coordinates, not a
free-call or cache-reset promise.

Issue one actual Apply attempt after this acquisition. Under the native
contract it is accepted, so $a=1$, $e=1$ and the register becomes exactly
(114.3). For a guarded contract this continuation is conditional on
observed acceptance. An observed refusal keeps the three-node register
and $e=0$; it does not install the five-node candidate. A Stop after
either outcome is absorbing. The guard may depend on the preceding
acquired replies, so acquiring the source does not force it to accept.

Computing $\rho u$ from the retained old description uses no additional
Read, but is not fresh acquisition or an actual new-version event. If
the successor is instead actually reacquired by the same root-first
frontier, its five native invocations are at
$\varepsilon,L,R,RL,RR$, with replies in (114.4). Its fresh phase
coordinates are $(q,a,\ell,k_{\rm phase})=(5,0,6,5)$.
Combining pre-entry, old-phase, accepted Apply and successor-phase
chronologies yields nine raw Reads, one Apply attempt, one accepted
update and literal Read length eight. A separately declared lifetime
address-only union contains five addresses; an epoch-address union
contains eight pairs, three at epoch zero and five at epoch one.
Separate empty Read-phase ledgers have charges one, three and five.
The successor repeats three old addresses as fresh invocations with
possibly changed replies. Old-version cached reports are not fresh
successor replies. None of these ledger conventions specifies a tariff,
refund, memory price or physical duration.

The full INITIAL target is still (112.2), here

$$
R_{\{L,R\}}(u)=
\bigl((L,R),\langle\square_1,\square_2\rangle,
\{\{1\},\{2\}\}\bigr),
\tag{114.19}
$$

since the two entire original subtrees are alpha and beta. Both numbered
holes and the exterior are retained. It is a value on INITIAL, not a heat
output or a row evaluated on the substituted register. The same inherited
full acquisition route can recover the whole INITIAL row on every branch
source; the witness's small bill is not a uniform price or an acquired
size promise for that full domain.

**Definition 114.7 (scope of the obstruction and the unpaid bridges).**
The source-indexed matrices and transfer in (114.1)--(114.15) are
mathematical comparison objects. Native four-valued Read acquires tree
constructors at addresses. It does not acquire a signed amplitude,
prepare an arbitrary $f$, actuate $T$, run heat, or read
$\mathsf c_s e^{-tL_s}f$. Such a service would require its own actual
input preparation, actuator, evolution, readout and permission contract.
Source preparation, root/epoch authentication, access isolation, address
generation, archive storage/protection, local calculation, amplitude
encoding, actuator construction and physical duration remain unpriced,
as in §112.5. No real-linear rank is a finite-bit memory or hardware-size
price.

The scalar $t$ and $\theta(t)$ in (114.2) are deterministic semigroup
comparison parameters. The random pathwise old-set occupation inverse
of Theorem 108.2, actual accepted epoch $e$, chronology of paid acquisition
and physical duration have different types. In particular the exact
random old-set trace and the Schur complement in (112.9) do not furnish
a deterministic full-successor heat intertwining. The elapsed-count
criterion of [Native Alpha Recut Memory, §10](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md)
requires two genuinely acquired same-source rows and its uncovered-ray
condition; it recovers an accepted relative count under those premises,
not a heat or physical clock. Its §9 supplement/fresh-invocation frontier
likewise presupposes actually acquired and exported data and a genuine
authenticated update. Neither supplies the missing signed-field service.

The operator and map classes are distinct from
[Continuation I, Proposition 58.3](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md),
which uses the inherited grounded Hamiltonian and its forced
old-coordinate/norm-preserving zero extension, and from IV §§109--110,
which fix the actual centered ancestry pullback and its source-size-scaled
asymptotic comparison. Here the closed occurrence Laplacian has a
constant kernel, the map is completely unrestricted except for static
real linearity, and one literal accepted pair rules out full-domain
injectivity for every positive $a,b$. Those earlier obstructions are
reused with their own hypotheses, not renamed as this result.

Finite spectral calculus, invariant-subspace restrictions, root-visible
modal decomposition and static Schur reduction are mature intermediates.
Doerfler--Bullo,
[*Kron Reduction of Graphs with Applications to Electrical Networks*,
arXiv:1102.2950v1](https://arxiv.org/abs/1102.2950v1), Lemma 2, treats
a symmetric irreducible loopy Laplacian and a proper retained vertex set
of at least two vertices. The present connected five-node loopless graph
and three old retained vertices satisfy those hypotheses; its invertible
eliminated block is $I_2$. Static reduction is not (114.2).
Avena--Castell--Gaudilliere--Melot,
[*Intertwining wavelets or Multiresolution analysis on graphs through
random forests*, arXiv:1707.04616v2](https://arxiv.org/abs/1707.04616v2),
§§2.3 and 4.2.2, uses a finite irreducible reversible weighted graph,
a retained subset, its trace generator, a positive resolvent-filter
parameter and both approximation and detail coefficients for
reconstruction. Its trace, filtering and reconstruction statements do
not install the two prescribed generators here or turn an approximation
link into the requested exact injective pair. These are
`literature-attested` intermediates, not new standalone contributions.
The original accepted-pair rank ceiling, its arbitrary-clock proof and
the exact root-preserving ceiling maps above are `repo-derived`
source-specific consequences; no worldwide priority or exhaustive
literature-search conclusion is attached to them.

The primitive/derived/bridge separation of
[Typed Bridges, §16.1](AURIC_FIB_ATOM_TYPED_BRIDGES_AND_ARITHMETIC_TRIANGLE_RH_PIPELINE.md)
and the finite observability and conditional Mosco machinery of
[its second continuation, §§54--55](AURIC_FIB_ATOM_TYPED_BRIDGES_AND_ARITHMETIC_TRIANGLE_RH_PIPELINE_CONTINUATION_II.md)
retain their stated carriers, operators, maps and hypotheses. The
five-state probability carrier is not the five actual successor
occurrences in (114.4); equal cardinalities identify neither fields nor
operations. Here mean-zero refers to counting mass on actual tree nodes.
No probability-law, spatial metric, continuum or physical-function
correspondence is obtained by borrowing those names.

Only the exact injective, time-independent real-linear,
single-deterministic-scalar-clock class on the unchanged closed
operators is excluded. Approximate or joint-limit transport,
time-dependent or nonlinear lifting, stochastic clocks, extra retained
carriers, release with a different commissioned generator and genuine
native field services remain separate questions. No assertion of their
existence or nonexistence follows from (114.6). Spatial propagation,
ambient dimension, physical time, stable matter, full-spectrum
acquisition and why-three still require their actual typed source,
operation, permission and resource bridges. The ordinary arguments here
are not Lean/kernel verification and do not satisfy the full ongoing
why-three programme.

## 114.99 追加锚（本行以下为增补区）
