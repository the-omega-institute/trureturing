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

## 115. Uniform complete signed-state comparison on every original source

### 115.1 The unchanged sources and the two covariance carriers

**Definition 115.1 (all originals, all nodes and the source boundary).**
Use the full finite ordered algebra $\mathcal T$, actual $\rho$, occurrence
addresses and closed unit-edge counting Laplacian of IV Definitions
112.1--112.2. For every $u\in\mathcal T$ and $n\ge0$, write

$$
\begin{aligned}
s_n&=\rho^n u,& V_n&=V_{s_n},& N_n&=|V_n|,& L_n&=L_{s_n},\\
\mu_n&=N_n^{-1}\sum_{x\in V_n}\delta_x,&
\mathscr E_n&=\ell^2(E_{s_n})\subset\mathscr H,
&\mathscr H&=\ell^2(\{L,R\}^{+}).
\end{aligned}
\tag{115.1}
$$

An edge is indexed by its child address, oriented away from the root.
Let $Q_n$ project onto the actual edges. The path sum $J_n$ and its
centered covariance are those of IV Definition 98.1, with this actual
source and counting probability:

$$
(J_nz)(x)=\sum_{\varepsilon\ne p\preceq x}z_p,
\qquad \Sigma_n=J_n^*J_n-(J_n^*\mathbf1)\otimes(J_n^*\mathbf1).
\tag{115.2}
$$

Every actual root, internal node and terminal has mass $1/N_n$.
Equal subtree values at different addresses remain different occurrences.
Write $W(u)=a(u)+\varphi b(u)$, $\varphi=(1+\sqrt5)/2$, as in IV
Definition 113.1. Retain exactly its boundary measure $\nu_u$:

$$
\nu_u=\sum_{q\in\mathcal L(u)}\frac{\varphi^{j(q)}}{W(u)}
              (\omega\mapsto q\omega)_*M,
\quad M([p])=\varphi^{-\#_L(p)-2\#_R(p)},
\quad j(q)=\begin{cases}0,&u|_q=\alpha,\\1,&u|_q=\beta.\end{cases}
\tag{115.3}
$$

This is a measure value, not extra retained leaf syntax. IV Theorems
113.2 and 113.4 give its exact cylinders and
$\nu_{s_n}=\nu_u$, $W(s_n)=\varphi^nW(u)$. Put
$J_u z(\omega)=\sum_{p\preceq\omega}z_p$ initially for finite support,
$C_u z=J_u z-\int J_u z\,d\nu_u$, and $\Sigma_u=C_u^*C_u$.
The two subscripts have different roles: $\Sigma_n$ is finite counting
covariance, whereas $\Sigma_u$ uses the unchanged original boundary law.
The initial source $u$ may be chosen anew at every $n$.

**Theorem 115.2 (bounded traces sourcewise and a uniform omitted-tail bound).**
For each finite $u$, $J_u$ has a bounded compact extension into
$L^2(\nu_u)$. If $d(u)$ is its maximum original terminal depth, then

$$
\|J_u\|\le\sqrt{d(u)}+\sqrt\varphi,
\qquad
\|J_u(I-Q_n)\|\le t_n:=\varphi^{1-n/2}
\quad(u\in\mathcal T,\ n\ge0).
\tag{115.4}
$$

The tail estimate is source-independent. There is nevertheless no
source-independent upper bound for $\|\Sigma_u\|$, or for
$\|\Sigma_n\|$ at any fixed $n$.

Proof. Above the original terminal antichain, Cauchy--Schwarz along a
path of length at most $d(u)$ bounds the finite-rank part by
$\sqrt{d(u)}$. Below those terminals, the trace is a finite direct sum
of the biased $M$-trace of IV Theorem 98.2. Its depth decomposition
gives $\|J\|^2\le a/(1-a)=\varphi$, where $a=\varphi^{-1}$.
The largest original terminal weight is at most one. This proves
the first bound and compactness: each tail copy of that $J$ is compact,
and the prefix part has finite rank.

For the second bound use the actual current terminal antichain
$\mathcal L(s_n)$, rather than a depth cutoff on $u$. Its cylinder
weights are exactly

$$
\nu_u([q])=\frac{w(q)}{W(s_n)},\qquad
w(q)\in\{1,\varphi\},\qquad
\max_{q\in\mathcal L(s_n)}\nu_u([q])\le\varphi^{1-n}.
\tag{115.5}
$$

Here $W(u)\ge1$ and IV (113.7)--(113.8) apply to $s_n$ itself.
Every omitted edge lies strictly below exactly one current terminal.
The omitted trace is consequently the direct sum of those $M$-traces,
with disjoint input coordinates and squared norms weighted by
$\nu_u([q])$. Its squared norm is at most
$\varphi\max_q\nu_u([q])\le\varphi^{2-n}$. This includes an empty
actual edge set and a terminal at the root.

For unboundedness let $u_m$ be the right comb with $m$ branches and
$m+1$ alpha leaves. Put $z_{R^i}=m^{-1/2}$ for $1\le i\le m$ and
zero elsewhere. Its norm is one. The boundary path sum takes the
values $0,1/\sqrt m,\ldots,m/\sqrt m$ on the $m+1$ original leaf
cylinders, each of weight $1/(m+1)$. Thus

$$
\langle z,\Sigma_{u_m}z\rangle=(m+2)/12\longrightarrow\infty.
\tag{115.6}
$$

For the same comb at any fixed $n$, each original leaf block has
$\Delta_n=2F_{n+1}-1$ nodes, all with the same displayed path-sum
value. Their total counting-probability mass is
$(m+1)\Delta_n/((m+1)\Delta_n+m)\ge1/2$.
Conditional variance on those blocks therefore gives
$\langle z,\Sigma_nz\rangle\ge(m+2)/24$; the other occurrences
are retained in the complementary part of the variance decomposition.

The Hardy trace and its descendant-mass adjoint are mature supplies:
Arcozzi--Rochberg--Sawyer--Wick,
[*Potential theory on trees, graphs and Ahlfors-regular metric spaces*,
arXiv:1010.4788v3, §5.1, (27), and §5.4.1, Theorem 32,
(33)](https://arxiv.org/pdf/1010.4788v3).
The latter is a weighted $\ell^p(\pi)$ to $L^p(\mu)$ trace criterion;
the present $p=2$, unit edge weight and actual biased cylinder bounds
are supplied directly by IV §98 and (115.5). No uniform norm of all
source traces is inferred from that criterion. $\square$

### 115.2 The source-independent relative centered estimate

**Theorem 115.3 (uniform relative covariance control).** Let
$c=\varphi^{-1}$, $\kappa=2\varphi/\sqrt5$, and, for $n\ge4$, define
the following numbers using only the substitution depth:

$$
\begin{aligned}
\Delta_n&=2F_{n+1}-1,&
d_n&=2c^{n+1}/\sqrt5,&
\zeta_n&=(1+d_n)/\Delta_n,\\
\lambda_n&=2^{-\lfloor n/2\rfloor}+d_n+\Delta_n^{-1/2},&
k_n&=27/(2\sqrt{\Delta_n}),\\
a_n&=(\lambda_n+\zeta_n)/(1-\zeta_n),&
b_n&=k_n/(1-\zeta_n),\\
\epsilon_n&=\max\{a_n+t_n,
 b_n+t_n(1+a_n)+2t_n\sqrt{b_n}+t_n^2\}.
\end{aligned}
\tag{115.7}
$$

Then $\zeta_n<1$, $\lambda_n<1$, $\epsilon_n\to0$, and for every
finite original source and every $z\in\mathscr H$,

$$
\left|\langle z,(\Sigma_u-\Sigma_n)z\rangle\right|
 \le\epsilon_n\bigl(\|z\|^2+\langle z,\Sigma_nz\rangle\bigr).
\tag{115.8}
$$

Equivalently, the norm of the self-adjoint relative difference
$`(I+\Sigma_n)^{-1/2}(\Sigma_u-\Sigma_n)(I+\Sigma_n)^{-1/2}`$
is at most $\epsilon_n$. The estimate is on the whole common edge
space, including absent coordinates; it makes no depth, balance, size
or source-entry assumption.

Proof. The exact count supply IV (108.9) gives
$N_n\ge\Delta_n\ell(u)$, where $\ell(u)$ is the number of original
leaves. Retain the $\ell(u)-1$ original internal occurrences and each
actual block $T_{n+j}$ substituted at an original terminal.
On the actual current tree define the charge

$$
q(x)=\kappa w(x)\mathbf1_{\{x\text{ terminal}\}}-1,
\qquad w(x)=\begin{cases}1,&\alpha,\\\varphi,&\beta,\\0,&\text{internal}.\end{cases}
\tag{115.9}
$$

For a block $T_k$, the exact Binet formula in IV (92.12) gives

$$
q_k:=\sum_{x\in T_k}q(x)=\kappa\varphi^k-(2F_{k+1}-1)
       =1+\delta_k,
\qquad \delta_k=2(-c)^{k+1}/\sqrt5.
\tag{115.10}
$$

Construct a potential $h$ on this same finite tree with root value
zero. Give each original skeleton edge increment one. Within a block,
give an edge whose below-edge subtree is the actual $T_k$ increment
$q_k$. Since $|q_k|<2$ for every $k\ge0$, all edge increments have
modulus at most two, independently of the original shape.
The tree flux calculation used in IV (92.9) and (108.12) now yields

$$
q=L_nh+\delta_r+e_n,
\qquad e_n=\sum_{q\in\mathcal L(u)}\delta_{n+j(q)}\delta_q,
\qquad \|e_n\|_\infty\le d_n.
\tag{115.11}
$$

Indeed inside a block $Lh=q-q_{n+j}\delta_q$. A nonroot block root
receives the parent contribution one, leaving just $\delta_{n+j}$.
A nonroot original internal vertex has value $1-2=-1$ under $Lh$;
the original internal root has value $-2=q(r)-1$. If the original
is a singleton, its block root instead leaves the full
$q_{n+j}=1+\delta_{n+j}$. These checks prove the same identity in
all cases, including $T_0,T_1$ with no block edges.

Summing (115.11), with $W(s_n)=\varphi^nW(u)$, gives the exact
normalization discrepancy

$$
\gamma_n:=\kappa W(s_n)/N_n,
\qquad |\gamma_n-1|
 \le\frac{1+d_n\ell(u)}{N_n}\le\zeta_n.
\tag{115.12}
$$

To remove the distinguished root from the squared-field estimate,
put $m=\lfloor n/2\rfloor$ and
$b_m(x)=2^{-\min(|x|,m)}$. Every original's current tree contains
the full binary levels through $m$, by the actual block minimum-depth
bound used in IV (108.15). That same closed-operator calculation gives

$$
L_nb_m=\delta_r-2^{-m}\mathbf1_{\{|x|=m\}},
\qquad
q=L_n(h+b_m)+r_n,
\qquad \|r_n\|_\infty\le2^{-m}+d_n.
\tag{115.13}
$$

All edge increments of $h+b_m$ have modulus at most three. Let $f$
be any real field on **all** current nodes. Define the probability
$\pi_n$ on the current terminals by $\pi_n(q)=w(q)/W(s_n)$; this is
only an intermediate comparison measure. Counting integration by parts
and maximum actual degree three give

$$
\begin{aligned}
\left|\gamma_n\int f^2\,d\pi_n-\int f^2\,d\mu_n\right|
&\le \frac3{N_n}\sum_{\{x,y\}\in E_{s_n}}
             |f(x)-f(y)|\,|f(x)+f(y)|
 +(2^{-m}+d_n)\|f\|_{\mu_n}^2\\
&\le3\sqrt{6/N_n}\,\|D_nf\|\,\|f\|_{\mu_n}
 +(2^{-m}+d_n)\|f\|_{\mu_n}^2\\
&\le\lambda_n\|f\|_{\mu_n}^2+k_n\|D_nf\|^2.
\end{aligned}
\tag{115.14}
$$

The second line uses
$\sum_{\{x,y\}}(f(x)+f(y))^2\le6\sum_xf(x)^2$.
For the last line apply Young's inequality with coefficient
$\Delta_n^{-1/2}$ to the mixed term: its energy coefficient is
$54/(4N_n\Delta_n^{-1/2})\le27/(2\sqrt{\Delta_n})$.
This estimate includes, rather than deletes, the internal-node mass.

Apply the two squared-field inequalities to $f-a\mathbf1$ for every
$a\in\mathbb R$, and take infima. The gradient is unchanged, and
$1-\lambda_n>0$. For $f=J_nz$ this yields, with
$V=\langle z,\Sigma_nz\rangle$ and
$B=\operatorname{Var}_{\nu_u}(J_uQ_nz)$,

$$
(1-\lambda_n)V-k_n\|Q_nz\|^2
 \le\gamma_n B
 \le(1+\lambda_n)V+k_n\|Q_nz\|^2,
\qquad |B-V|\le a_n V+b_n\|z\|^2.
\tag{115.15}
$$

Here $J_uQ_nz$ is constant on each current terminal cylinder with
value $f(q)$. Thus its boundary distribution is exactly $\pi_n$ by
(115.5); the finite field's distribution remains $\mu_n$ throughout.
This is a centering argument, not a subtraction of approximate means.
At $n=4$, $\Delta_4=9$ and
$\lambda_4=1/4+d_4+1/3<1$, $\zeta_4<1$; these upper bounds decrease
for subsequent $n$. This justifies both infima and divisions.

The centered omitted trace has norm at most $t_n\|z\|$ by (115.4),
since centering is an orthogonal contraction in $L^2(\nu_u)$. Hence

$$
\begin{aligned}
|\langle z,\Sigma_uz\rangle-B|
&\le2t_n\sqrt B\,\|z\|+t_n^2\|z\|^2\\
&\le t_n V+
 [t_n(1+a_n)+2t_n\sqrt{b_n}+t_n^2]\|z\|^2.
\end{aligned}
\tag{115.16}
$$

Use $\sqrt B\le\sqrt{1+a_n}\sqrt V+\sqrt{b_n}\|z\|$ and Young's
inequality in the second step. Adding (115.15) proves (115.8).
All traces are bounded for each $u$, so finite-support calculations
extend to $\mathscr H$. Every number in (115.7) is independent of
$u$, and all its vanishing terms tend to zero. The relative operator
bound follows by substituting $(I+\Sigma_n)^{-1/2}z$ and the norm
criterion for bounded self-adjoint operators. $\square$

### 115.3 Uniform positive-time operator comparison without bounded spectra

**Theorem 115.4 (the complete all-source normalized joint comparison).**
For $s>0$, set $F_s(0)=0$, $F_s(x)=e^{-s/x}$ for $x>0$ and
$\mathcal T_u(s)=F_s(\Sigma_u)$. Use the full finite polar maps

$$
U_n=-D_nL_n^{+1/2}:\mathbf1^\perp\subset\ell^2(V_n)
                          \longrightarrow\mathscr E_n,
\qquad e_n=N_n^{-1/2}\mathbf1,
\qquad S_n(s)=e^{-N_nsL_n}.
\tag{115.17}
$$

Extend $U_n$ by zero on constants and $U_n^*$ by zero on absent
edges. Then, for every source and every $n\ge0$,

$$
\Sigma_n|_{\mathscr E_n}=N_n^{-1}(D_nD_n^*)^{-1},
\qquad U_nS_n(s)U_n^*=F_s(\Sigma_n),
\qquad f\longleftrightarrow(\langle e_n,f\rangle,U_nf).
\tag{115.18}
$$

The last map is a counting-norm isometry onto
$\mathbb R\oplus\mathscr E_n$, with inverse $(c,z)\mapsto ce_n+U_n^*z$.
It includes every root-invisible finite eigenspace. On each fixed
$0<\varepsilon\le S<\infty$ there are explicit source-independent
$\eta_n=\eta_n(\varepsilon,S)\to0$ such that

$$
\sup_{u\in\mathcal T}\sup_{s\in[\varepsilon,S]}
 \|F_s(\Sigma_n)-F_s(\Sigma_u)\|\le\eta_n.
\tag{115.19}
$$

Thus arbitrary moving originals $u_n$ and arbitrary unit signed states
on their entire finite occurrence spaces are allowed in this comparison.
Constants are carried by the identity on the $\mathbb R$ summand.

Proof. Apply the finite inverse-gradient and polar supply IV Theorem
103.2 to the actual tree $s_n=\rho^nu$, not to $T_n$ in its place.
Its hypotheses are just a finite connected tree, all-vertex counting
mass and unit edges. On the mean-zero node space, centered path
integration inverts $D_n$, giving
$N_n\Sigma_n=(D_nD_n^*)^{-1}$ on actual edges; its polar map is unitary.
The spectral correspondence in (103.3)--(103.4) gives (115.18), with
the exact factor $N_n$. For a singleton $N_n=1$, $L_n=0$ and
$\mathscr E_n=\{0\}$; inverses and polar maps have zero-dimensional
domains and (115.18) still holds. In particular the alpha-to-beta step
does not create a fictitious edge. The actual $T_{n+j}$ indices in
(115.10), not a common fitted orbit index, supplied the estimates.

For a sourcewise bounded nonnegative covariance $A$ put
$R(A)=A(I+A)^{-1}=I-(I+A)^{-1}$. These are positive contractions
on the **same** $\mathscr H$, regardless of $\|A\|$.
If $\epsilon_n<1$, (115.8) gives

$$
\|R(\Sigma_n)-R(\Sigma_u)\|
 \le\frac{\epsilon_n}{1-\epsilon_n}=:\delta_n^{\rm res}.
\tag{115.20}
$$

Indeed set $A_n=I+\Sigma_n$ and
$`E=A_n^{-1/2}(\Sigma_u-\Sigma_n)A_n^{-1/2}`$.
Then $I+\Sigma_u=A_n^{1/2}(I+E)A_n^{1/2}$ and
$\|E\|\le\epsilon_n$. Conjugating
$(I+E)^{-1}-I$ by $A_n^{-1/2}$ proves (115.20), since
$\|A_n^{-1/2}\|\le1$ and
$\|(I+E)^{-1}-I\|\le\epsilon_n/(1-\epsilon_n)$.

To pass from this resolvent control to the complete operators, define

$$
H_s(r)=\begin{cases}e^{-s(1-r)/r},&0<r\le1,\\0,&r=0.\end{cases}
\qquad F_s(A)=H_s(R(A)).
\tag{115.21}
$$

For $s\in[\varepsilon,S]$ these functions have values in $[0,1]$
and a common scalar Lipschitz bound
$M_{\varepsilon,S}=4Se^S/(e^2\varepsilon^2)$: their derivative is
$sr^{-2}e^se^{-s/r}$, and
$\sup_{r>0}r^{-2}e^{-\varepsilon/r}=4/(e^2\varepsilon^2)$.
This scalar bound alone is not an operator Lipschitz assertion.
Use instead the Bernstein polynomial of degree $k$ with coefficients
$H_s(j/k)$. Its uniform scalar error is at most
$M_{\varepsilon,S}/(2\sqrt k)$, by the binomial variance bound.
Its monomial coefficients have total absolute value at most $3^k$,
by expanding $(1-r)^{k-j}$. For contractions $X,Y$, telescoping powers
therefore bounds the polynomial difference by $k3^k\|X-Y\|$.
Consequently an explicit permissible modulus is

$$
\begin{aligned}
\Omega_{\varepsilon,S}(\delta)
 &=\min\left\{1,\ \inf_{k\ge1}
       \left(\frac{M_{\varepsilon,S}}{\sqrt k}+k3^k\delta\right)\right\},\\
\eta_n&=\begin{cases}
\Omega_{\varepsilon,S}(\delta_n^{\rm res}),&n\ge4,\ \epsilon_n<1,\\
1,&\text{otherwise}.
\end{cases}
\end{aligned}
\tag{115.22}
$$

The cap one is valid for differences of positive contractions.
Fixing $k$ first and then increasing it proves
$\Omega_{\varepsilon,S}(\delta)\to0$ as $\delta\downarrow0$.
Functional calculus applies the scalar approximation separately to
the two positive contractions. Equations (115.20)--(115.22) prove
(115.19) with no common upper bound on covariance spectra.

Spectral calculus and polar decomposition are used with their exact
hypotheses in Teschl,
[*Mathematical Methods in Quantum Mechanics*, Theorem 3.7,
Problem 3.11 and Theorem 6.6](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
The finite operators are symmetric; $\Sigma_u$ is compact self-adjoint
by Theorem 115.2. The general relative-form/resolvent and positive-time
semigroup frame is also described by Mugnolo--Nittka--Post,
[*Norm convergence of sectorial operators on varying Hilbert spaces*,
DOI 10.7153/oam-07-54, Definition 2.3 and Example 3.9](https://files.ele-math.com/articles/oam-07-54.pdf).
Their Definition 2.3 requires bounded elliptic forms and specified
identification maps satisfying all five conditions (2.7); Example 3.9
uses those hypotheses for positive-time compact uniformity, excluding
an automatic zero-time conclusion. Here the carrier is fixed and the
relative resolvent calculation is proved above. No unverified
quasi-unitary comparison of the changing node spaces is substituted
for (115.8). $\square$

### 115.4 An actual consecutive pair with full reverse and readout contracts

**Theorem 115.5 (injective comparison across every accepted step).**
For an actual accepted step $s_n\mapsto s_{n+1}$, let
$I_n^E:\mathscr E_n\to\mathscr E_{n+1}$ be inclusion of the actual
old edges at their unchanged addresses, as in IV (112.7). Define the
static real-linear comparison map

$$
T_n f=\langle e_n,f\rangle e_{n+1}
            +U_{n+1}^*I_n^EU_nf,
\qquad r_n=N_{n+1}/N_n.
\tag{115.23}
$$

This map is defined on the entire old signed-state space, not a root
response quotient. For every original $u$ and every $n\ge0$,

$$
T_n^*T_n=I,\qquad
T_n^*e_{n+1}=e_n,\qquad
T_nT_n^*=P_{\operatorname{ran}T_n},\qquad 1\le r_n\le3.
\tag{115.24}
$$

All adjoints here use counting inner products. Thus every old signed
direction has singular value one, the reverse $T_n^*$ has norm one,
and recovery on the attained range is exact with condition number one.
For $0<\varepsilon\le S<\infty$ the complete operator comparison is

$$
\sup_{u\in\mathcal T}\sup_{s\in[\varepsilon,S]}
 \|S_{n+1}(s)T_n-T_nS_n(s)\|
 \le\eta_{n+1}+\eta_n\longrightarrow0.
\tag{115.25}
$$

In particular
$\|T_n^*S_{n+1}(s)T_n-S_n(s)\|\le\eta_{n+1}+\eta_n$.
For every old readout vector $g$, the complete transferred readout is
$h\mapsto\langle T_ng,h\rangle$ on the successor. It has exactly
the old norm $\|g\|$, agrees on every transported old state, and obeys

$$
\begin{aligned}
\langle T_ng,T_nf\rangle&=\langle g,f\rangle,\\
|\langle T_ng,S_{n+1}(s)T_nf\rangle-
              \langle g,S_n(s)f\rangle|
 &\le(\eta_{n+1}+\eta_n)\|g\|\|f\|.
\end{aligned}
\tag{115.26}
$$

This includes every literal old coordinate readout $g=\delta_p$,
and every root-invisible signed mode. The transferred readout need
not equal the successor's own coordinate evaluation at $p$.

There are three distinct useful normalizations. Put
$A_n=\sqrt{r_n}T_n$ and $B_n=r_n^{-1/2}T_n$. For every old field $f$,
their exact contracts are

| Map | Constant input $\mathbf1$ | Successor counting sum | Counting norm | Counting left inverse |
| --- | --- | --- | --- | --- |
| $T_n$ | $r_n^{-1/2}\mathbf1$ | $\sqrt{r_n}\sum f$ | $\|f\|$ | $T_n^*$ |
| $A_n$ | $\mathbf1$ | $r_n\sum f$ | $\sqrt{r_n}\|f\|$ | $r_n^{-1/2}T_n^*$ |
| $B_n$ | $r_n^{-1}\mathbf1$ | $\sum f$ | $r_n^{-1/2}\|f\|$ | $\sqrt{r_n}T_n^*$ |

In counting norm all three have condition number one on their attained
ranges. Their lower singular values are respectively $1$, $\sqrt{r_n}$
and $r_n^{-1/2}\ge1/\sqrt3$. In counting-probability norm $A_n$ is
an isometry and preserves the mean; its probability adjoint is exactly
$r_n^{-1/2}T_n^*$ and is its norm-one reverse. The other probability
norms are $\|T_nf\|_{\mu_{n+1}}=r_n^{-1/2}\|f\|_{\mu_n}$ and
$\|B_nf\|_{\mu_{n+1}}=r_n^{-1}\|f\|_{\mu_n}$.
The estimate (115.25) is unchanged for $A_n$ in probability operator
norm; for $B_n$ in counting operator norm its right side is multiplied
by $r_n^{-1/2}$.

Proof. Actual rho births add two children at each current beta leaf,
leaving every old edge at its literal address. Hence $I_n^E$ is an
isometry, including when no edge is born. The two summands in (115.23)
are orthogonal. The complete polar isometries (115.18) prove
(115.24) and both projection identities. Actual node counts give
$r_n=1+2b(s_n)/N_n$, and $b(s_n)\le N_n$, proving the stated uniform
bounds without a shape hypothesis. IV Theorem 108.2 supplies the
stronger $\sup_u|r_n-\varphi|\to0$; no new clock theorem is required.

Under the coordinates $(c,z)$ of (115.18), $T_n$ is exactly
$(c,z)\mapsto(c,I_n^Ez)$. The centered defect in (115.25) is therefore
the restriction to $\mathscr E_n$ of

$$
F_s(\Sigma_{n+1})z-F_s(\Sigma_n)z.
\tag{115.27}
$$

The common comparison covariance is $\Sigma_u$ at both epochs by
$\nu_{\rho u}=\nu_u$. The triangle inequality in (115.19) proves
(115.25); constants contribute zero. Applying the reverse and pairing
with arbitrary $g$ proves (115.26). These are simultaneous operator
bounds, not separate scalar estimates at different inputs.

Since $T_n\mathbf1=\sqrt{N_n/N_{n+1}}\mathbf1$, its constant and sum
contracts follow; the other rows follow by their stated scalar factors.
For probability adjoints, multiplying the counting adjoint by
$N_n/N_{n+1}$ is necessary. This gives the reverse of $A_n$ and all
probability norms in the statement. Dividing both input and output
counting norms by their actual square roots of node counts proves
the probability version of (115.25).

Every real-linear old readout is covered: if $\ell(f)=\langle g,f\rangle$
in counting norm, use $\ell'(h)=\langle T_ng,h\rangle$ for $T_n$,
$r_n^{-1/2}\langle T_ng,h\rangle$ for $A_n$, or
$\sqrt{r_n}\langle T_ng,h\rangle$ for $B_n$.
Their counting functional norms are respectively $\|g\|$,
$r_n^{-1/2}\|g\|$ and $\sqrt{r_n}\|g\|$, and each composition with
its transfer is exactly $\ell$. In probability norm the analogous
Riesz readout $\langle g,f\rangle_{\mu_n}$ for $A_n$ is transferred
as $\langle A_ng,h\rangle_{\mu_{n+1}}$, with identical norm.
A literal evaluation has probability functional norm $\sqrt{N_n}$;
its corresponding error bound has that factor. No source-uniform
absolute error for unnormalized point readouts on unit probability
fields is inferred. Counting-unit states and readouts do have the
uniform bound (115.26). None of these maps is asserted positive,
local, or identical to ancestry or literal old-coordinate retention.
$\square$

### 115.5 Endpoint, conditioning and boundary-law scope

**Proposition 115.6 (what the comparison retains and what zero forbids).**
For every fixed $u$, put $\mathscr K_u=(\ker\Sigma_u)^\perp$.
The polar decomposition $C_u=W_u\Sigma_u^{1/2}$ gives a unitary
$W_u:\mathscr K_u\to\mathbf1^\perp\subset L^2(\nu_u)$ and the
boundary comparison generator $(\Sigma_u|_{\mathscr K_u})^{-1}$ on
the edge carrier, with domain $\operatorname{ran}(\Sigma_u|_{\mathscr K_u})$.
This is the same complete polar/spectral construction as IV (111.8),
with $\nu_u$ in place of $M$; it does not replace the biased law by
the fair unit-conductance harmonic law.
There is no identity-at-zero extension of $\mathcal T_u(s)$ on all
$\mathscr H$. There is also no source-uniform conditioning claim
for undoing positive-time heat or reconstructing every finite mode
from a boundary limiting state.

Proof. Centered cylinder indicators belong to $\operatorname{ran}C_u$
and span a dense subspace of the centered $L^2(\nu_u)$ space.
Every cylinder has positive $\nu_u$ mass and the cylinder sigma algebra
is the whole boundary sigma algebra. Teschl's polar decomposition
therefore has precisely the stated initial and final spaces. The
compact positive injective restriction of $\Sigma_u$ has dense range
in $\mathscr K_u$; spectral calculus gives its inverse with the stated
domain. This directly consumes IV §111's polar representation; no
additional boundary-memory or propagation theorem is needed here.

Let $q=\delta_L+\delta_R$. Its boundary trace is identically one
for every original, so $q\ne0$ lies in $\ker\Sigma_u$. For $n\ge2$
both root edges occur in every $s_n$, whereas $J_nq$ is zero at the
root and one at every other actual occurrence. Thus

$$
Q_nq=q,
\qquad \langle q,\Sigma_nq\rangle=(N_n-1)/N_n^2,
\qquad \mathcal T_u(s)q=0\quad(s>0).
\tag{115.28}
$$

The centered finite heat equals $Q_n$ at zero. On $\mathscr K_u$ the
boundary heat tends strongly to identity as $s\downarrow0$, while
on $\mathscr H$ it tends to $P_{\mathscr K_u}$. Since $q\in\mathscr E_n$,
$\|Q_n-P_{\mathscr K_u}\|\ge1$. Uniformity of (115.19) cannot include
zero. Moreover a purely multiplicative relative estimate against
$\langle z,\Sigma_uz\rangle$ alone is false, since (115.28) has zero
boundary variance and strictly positive finite variance. The identity
term in (115.8) is the specified unit-edge energy allowance, not a
claim of multiplicative equivalence of covariance kernels.
The consecutive finite transfer itself still has exact zero-time
defect zero, because both finite node heats equal identity there;
these are different endpoint assertions.

All finite positive eigenspaces were retained by (115.18) and (115.23),
including every direction orthogonal to the root spectral vector.
The positive-time comparison allows fast modes to decay; it does not
invert that decay. Indeed every nontrivial actual tree has
$\lambda_{\max}(L_n)\ge1$, for example by its trace and $N_n-1$
positive eigenvalues. The smallest singular value of $S_n(s)$ is
$e^{-N_ns\lambda_{\max}(L_n)}\le e^{-N_ns}$, and $N_n\ge\Delta_n\to\infty$.
Its inverse norm is unbounded at each fixed $s>0$, even on the
single-alpha orbit. Uniformly well-conditioned transfer is thus
distinct from a uniformly well-conditioned inverse heat experiment.
The finite/infinite address probabilities still have total variation
one as stated in IV Specification 113.11; (115.8) uses a different
relative quadratic topology. $\square$

### 115.6 Acquired inputs, genuine permissions and the unsupplied service

**Definition 115.7 (paid description consumer and unchanged native history).**
The objects above are functions of the actual original ordered source
and its authentic accepted epoch. For their acquired-description
consumer, retain the same-source, same-root, stationary epoch-zero
premise and lawful access isolation of IV Definitions 112.1, 112.9,
Proposition 113.9 and Specification 113.10. Reuse
[ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean)'s
actual four-valued immutable `readout`,
history-only `acquisitionStep`/`frontier`, `acquisitionTrace`, and
report-only `restore`; its original Boolean `Strategy` and
distinct-address payment rule are unchanged. The reply-driven root-first
phase starts from its own empty phase history, requests children only
after a branch report, and supplies the complete ordered original on
every finite source, including alpha and beta. It receives no size,
depth, balanced-shape or tree-index advice.

Its `acquisition_foundation` gives the authentic empty-phase traversal;
the [owning Blueprint](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.scribe.cs)
keeps fuel as a sourcewise termination witness, not controller advice.
Report-only restoration and the separate description consumer have
exactly the scope proved in IV Theorem 112.10 and Proposition 113.9.

With $S(u)=|V_u|$ and $\Lambda(u)=\sum_{p\in V_u}|p|$, its inherited
sufficient phase coordinates are exactly

$$
(q,a,\lambda,k_{\rm phase})=(S(u),0,\Lambda(u),S(u)).
\tag{115.29}
$$

These count raw Read invocations, Apply attempts, literal Read-address
length and distinct addresses in that phase. On the authentic branch
entry of IV (112.1), retaining its pre-entry root event gives $S+1$
raw Reads and literal length $\Lambda$. A single same-immutable-source
paid-address cache charges $S$ cumulatively and $S-1$ incrementally;
separate empty phase ledgers charge $1$ and $S$. The root was actually
called twice. For a singleton the phase itself has $(1,0,0,1)$;
an additional genuine pre-entry root call is counted separately under
the same rules. None is a free or refunded native invocation.

From this genuinely acquired description and the chronological observed
acceptances one can evaluate the exact finite matrices, $N_n$, $W(u)$,
$\nu_u$, polar transfers and their readout vectors. This is local
finite-source evaluation. It requires no additional native Read for
that mathematical evaluation, but is not a freshly acquired current
Read, a field measurement, free source advice, or a price for computing
those matrices. Old-version cached reports are not new-version reports.
If the current version is actually reacquired instead, its stationary
root-first phase has $(N_n,0,\sum_{p\in V_n}|p|,N_n)$ in its own
empty ledger; source-version identity and authentication are still
premises. No new optimal acquisition bound is asserted.

Retain the entire Read/Apply/Stop menu and Contract 112.1a. Under the
uncapped native contract every serial Apply is accepted. Under a
separately declared common guard $G(\gamma,e,H)$, every attempt logs
its actual accepted/refused status. Acceptance installs exactly $\rho s$
and advances $e$; refusal changes neither source nor epoch, and its
comparison transfer is identity on the unchanged space. Every repeated
or absent Read remains a real chronological event with its actual
four-valued reply. Stop is absorbing. The comparison maps cannot grant
acceptance, change the guard's inputs, fabricate Read events from local
evaluation, or execute a suffix after Stop. The source/history metadata
and permission record are carried alongside the comparison, never
replaced by the invariant boundary measure.

The complete INITIAL rows retain their actual reached list, numbered
exterior and full whole-subtree partition. In particular the branch
service's target is still IV (112.2) on INITIAL $u$, and the full-domain
cut classification of IV Theorem 113.7 is unchanged. No heat readout
is substituted for that target, and no changed-cut successor row is
treated as its initial row. The acquired description supplies its row
by the existing report-only consumer; (115.26) concerns signed linear
field readouts, a different type from constructor Read or row equality.

**Mathematical citation 115.8 (consumer, distinctions and remaining bridges).**
The source-specific new estimate is (115.8): the bounded-increment
counting correction, centered infima and current-terminal tail control
hold uniformly over all original skeletons. Relative resolvents and
spectral/polar calculus are literature-attested intermediate supplies.
Their direct consumer is the complete signed-state comparison
(115.19), with the actual consecutive pair (115.23)--(115.26).
These are repo-derived ordinary mathematical deductions; no worldwide
priority or exhaustive literature-absence claim is attached to them.
They settle the analytical uniform comparison requirement in IV
Specification 113.11 with the stated comparison maps and norms.

The exact static-linear arbitrary-clock obstruction of §114 remains
intact: (115.25) is an asymptotic normalized-time estimate, not exact
intertwining at a finite accepted pair. The ancestry obstruction of IV
§109 remains intact as well: $T_n$ is the displayed polar-edge map,
not that ancestry pullback. Its finite inverse and complete transferred
readouts are specified explicitly rather than assuming preservation of
literal amplitudes at old addresses. The comparison does not supply
a physically realizable transport.

[Native Alpha Recut Memory, §§11--12](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md)
already owns delayed-cut retention and the multirecord relative-epoch
criterion. Under its actual acquired whole-row and genuine continuation
premises, Theorem 12.5 recovers all relative epochs exactly iff its
overlap graph is connected, with Lemma 12.4 supplying simultaneous
component-owned whole-row collisions otherwise. Its Proposition 12.8
relates the canonical locally constant density to the right clock;
an arbitrary almost-everywhere representative has no justified point
evaluation. These are reused with their original input and resource
contracts. They supply neither (115.8) nor signed-field actuation.
The conditional finite-state native-operation alternative remains a
separate incomparable route; selection of this comparison refutes
none of its lawful hypotheses.

The integer $e$ counts observed accepted source updates; attempts have
their own count. The real $s$ is normalized comparison time, with old
and successor mathematical heat parameters $N_ns$ and $N_{n+1}s$.
The random old-set occupation inverse of IV §108, acquired chronology,
and physical duration have distinct types. Neither $r_n\to\varphi$,
boundary invariance, nor an acquired native integer identifies those
clocks. Source-dependent counts and matrices have the paid-description
premise above, not an acquired measure oracle.

Native constructor Read does not prepare a signed occurrence field,
implement $T_n$, $A_n$ or $B_n$, actuate the closed heat generator,
or measure the transferred real-linear functional in (115.26).
Field preparation and ingress, transfer permission and execution,
heat actuation and output, amplitude encoding and precision, local
matrix-calculation and execution cost, root/epoch authentication,
storage and isolation, physical clock conversion and spatial
realization remain unsupplied. No stable physical matter, spatial
dimension, physical propagation or complete finite-spectrum recovery
follows from this operator comparison. The ordinary proofs give no
new Lean/kernel verification, registration or freezing. This finite
analytical outcome does not satisfy or terminate the complete active
through-2027 why-three programme.

## 115.99 追加锚（本行以下为增补区）
