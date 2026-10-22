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

## 116. Positive local ingress and the complete successor heat comparison

The occurrence geometry and signed-state comparison of §115 do not by
themselves make its polar transfers positive or local. This section gives
a different pair of positive maps on each authentic accepted rho step.
The reverse is adjoint to literal ancestry, while the conservative ingress
has a different normalization. Their complete positive-time comparison
includes every successor direction, not just ingress states.

### 116.1 Actual carriers and the two endpoint maps

**Definition 116.1 (the original step and its forms).** On every nonempty
finite ordered original $u\in\mathcal T$ of IV Definition 112.1, retain
$s_n=\rho^n u$, every literal occurrence and label, and the closed unit-edge
counting Laplacian $L_n$ of §115.1. The substitution is still
$\rho\alpha=\beta$, $\rho\beta=\langle\beta,\alpha\rangle$, homomorphically
on ordered pairs. For one actual accepted step abbreviate

$$
\begin{aligned}
V&=V_n,& V'&=V_{n+1},& N&=N_n,& N'&=N_{n+1},& r&=N'/N,\\
H&=L^2(V,\mu),& H'&=L^2(V',\mu'),&
\mu&=N^{-1}\sum_{x\in V}\delta_x,&
\mu'&=(N')^{-1}\sum_{y\in V'}\delta_y,\\
A&=NL_n,& A'&=N'L_{n+1},&
S(t)&=e^{-tA},& S'(t)&=e^{-tA'}.
\end{aligned}
\tag{116.1}
$$

Every repeated occurrence remains distinct. Probability normalization
changes the norm and readout convention; it removes no unit counting mass
and changes no literal edge or closed Laplacian. Write $\mathcal E$ and
$\mathcal E'$ for the actual old and successor edge sets. The associated
real bilinear forms are exactly

$$
\begin{aligned}
\mathfrak a(f,g)&=\langle f,Ag\rangle_\mu
 =\sum_{\{x,y\}\in \mathcal E}(f(x)-f(y))(g(x)-g(y)),\\
\mathfrak a'(h,k)&=\langle h,A'k\rangle_{\mu'},\\
\|f\|_1^2&=\|f\|_\mu^2+\mathfrak a(f,f),&
\|h\|_{1'}^2&=\|h\|_{\mu'}^2+\mathfrak a'(h,h).
\end{aligned}
\tag{116.2}
$$

Write $H_1=(H,\|\cdot\|_1)$ and $H'_1=(H',\|\cdot\|_{1'})$.
Let $\mathcal B$ be the actual old beta-leaf set and $\mathcal Z$ its two
born children per parent, as in IV (112.6)--(112.9). The map
$\pi:V'\to V$ fixes old addresses and sends each born child to its actual
parent. Put $m(x)=|\pi^{-1}(x)|=1+2\mathbf1_{\mathcal B}(x)$ and define

$$
E f=f\circ\pi,\qquad
D=E^{*_\mu}=r^{-1}E^{\mathsf T},\qquad
C=r E\operatorname{diag}(m)^{-1},\qquad
F=r^{-1}C.
\tag{116.3}
$$

Here $E^{\mathsf T}$ is the raw counting transpose, while the indicated
adjoint uses the two probability inner products. These names are local
to this section; $D$ here is not the incidence operator of §115.

**Theorem 116.2 (finite positive endpoint contracts).** All four maps in
(116.3) are order-positive and supported within occurrence distance one.
Their exact contracts, for every signed $f,g\in H$ and $h\in H'$, are

$$
\begin{aligned}
E\mathbf1&=\mathbf1,& (Ef)(x)&=f(x)\quad(x\in V),\\
D\mathbf1&=m/r,&
(C\mathbf1)(y)&=r/m(\pi(y)),&
DC&=I_H,\\
\int Dh\,d\mu&=\int h\,d\mu',&
\int Cf\,d\mu'&=\int f\,d\mu,&
\sum_{y\in V'}(Ff)(y)&=\sum_{x\in V}f(x),\\
\langle Eg,Cf\rangle_{\mu'}&=\langle g,f\rangle_\mu,&
\mathfrak a'(Ef,Eg)&=\mathfrak a(f,g).
\end{aligned}
\tag{116.4}
$$

Furthermore $1\le r\le3$ and

$$
\|E\|=\|D\|\le\sqrt3,\qquad
\|C\|\le\sqrt3,\qquad
\|Cf\|_{\mu'}\ge3^{-1/2}\|f\|_\mu.
\tag{116.5}
$$

Thus $D$ reverses $C$ on its attained range. It is not a recovery of
arbitrary successor inputs.

Proof. Every fibre has one old member and either zero or two born
children. Direct summation on these actual fibres gives

$$
E^{\mathsf T}E=\operatorname{diag}(m),\qquad
W:=DE=\operatorname{diag}(m/r),\qquad
\|Ef\|_{\mu'}^2=\frac1N\sum_x\frac{m(x)}r f(x)^2,\qquad
\|Cf\|_{\mu'}^2=\frac1N\sum_x\frac r{m(x)}f(x)^2.
\tag{116.6}
$$

The same summation proves the integrals, pairing and $DC=I$ in (116.4).
All nonzero coefficients are positive and join either equal addresses
or a newborn and its parent. Born-edge differences of $Ef$ vanish;
every old-edge difference is retained, proving the form identity.
The actual count $N'=N+2|\mathcal B|$ gives $1\le r\le3$.
Since $1\le m\le3$, (116.6) proves every norm and lower bound.
No inverse on the additional successor directions follows. $\square$

### 116.2 Source-uniform control of the mass discrepancy

**Lemma 116.3 (a relative bilinear mass estimate).** Put
$c=\varphi^{-1}$, $\Delta_n=2F_{n+1}-1$, and, for $n\ge2$, set

$$
\begin{aligned}
e_n&=\frac{c+2c^{n+1}}{\Delta_n},&
\xi_n&=c\,2^{-\lfloor n/2\rfloor}+2c^{n+1}+e_n,\\
\vartheta_n&=3\sqrt{\frac3{2\Delta_n}}+\xi_n.
\end{aligned}
\tag{116.7}
$$

These numbers depend only on $n$ and tend to zero. On every original
source and every accepted pair,

$$
|\langle (W-I)f,g\rangle_\mu|
 \le\vartheta_n\|f\|_1\|g\|_1
\qquad(f,g\in H).
\tag{116.8}
$$

This is a form estimate. No small operator norm of $W-I$ on $H$ is
asserted.

Proof. Reuse the exact beta-charge corrector in IV (108.10)--(108.12)
on the actual $s_n$, including its full original skeleton. Those
identities supply an actual potential $h$ such that

$$
2\mathbf1_{\mathcal B}-c=L_nh+c\delta_{\mathrm{root}}+\epsilon,
\qquad
|\nabla h|\le2,\qquad
\|\epsilon\|_\infty\le2c^{n+1}.
\tag{116.9}
$$

They also supply $N\ge\Delta_n$ and $|r-\varphi|\le e_n$ uniformly
over all originals. Their hypotheses are precisely the finite ordered
source, literal rho blocks and closed unit-edge operator retained here.
For $j=\lfloor n/2\rfloor$, the actual tree contains every binary level
through $j$. The root-spreading potential of IV (108.15),
$b_j(x)=2^{-\min(|x|,j)}$, obeys

$$
L_nb_j=\delta_{\mathrm{root}}
       -2^{-j}\mathbf1_{\{|x|=j\}}.
\tag{116.10}
$$

Consequently, using $m-r=2\mathbf1_{\mathcal B}-c-(r-\varphi)$,
the potential $v=h+cb_j$ satisfies

$$
m-r=L_nv+\eta,\qquad
|\nabla v|\le3,\qquad
\|\eta\|_\infty\le\xi_n.
\tag{116.11}
$$

The root is included, rather than removed from the carrier.

Counting integration by parts applied to the pointwise product $fg$
now bounds its flux term by

$$
\begin{aligned}
\left|\frac1{rN}\sum_x (L_nv)(x)f(x)g(x)\right|
&\le\frac3{2rN}\sum_{\{x,y\}\in \mathcal E}
 \bigl(|f(x)-f(y)|\,|g(x)+g(y)|\\
&\hspace{42mm}
       +|g(x)-g(y)|\,|f(x)+f(y)|\bigr)\\
&\le\frac3r\sqrt{\frac3{2N}}\,
 \bigl(\sqrt{\mathfrak a(f,f)}\,\|g\|_\mu
       +\|f\|_\mu\sqrt{\mathfrak a(g,g)}\bigr)\\
&\le3\sqrt{\frac3{2\Delta_n}}\|f\|_1\|g\|_1.
\end{aligned}
\tag{116.12}
$$

Here the exact maximum degree is at most three, so
$\sum_{\{x,y\}}(g(x)+g(y))^2\le6N\|g\|_\mu^2$, and likewise for $f$.
The last line uses Cauchy--Schwarz in the two coordinates
$(\sqrt{\mathfrak a(f,f)},\|f\|_\mu)$ and
$(\|g\|_\mu,\sqrt{\mathfrak a(g,g)})$, and $r\ge1$.
The remainder in (116.11) is at most
$\xi_n\|f\|_\mu\|g\|_\mu/r$. Since
$\langle(W-I)f,g\rangle_\mu=(rN)^{-1}\sum_x(m(x)-r)f(x)g(x)$,
this proves (116.8). The exponential growth of $\Delta_n$ and the
displayed vanishing terms prove $\vartheta_n\to0$.
No bound on original depth, balance or size has been used. $\square$

### 116.3 Every successor direction in the resolvent comparison

**Theorem 116.4 (full successor resolvent and compositional bounds).**
Define

$$
R=(I+A)^{-1},\qquad R'=(I+A')^{-1},\qquad
a_n=3\vartheta_n+\frac{1+\sqrt6}{2\sqrt{\Delta_n}},
\qquad d_n=3(a_n+\vartheta_n).
\tag{116.13}
$$

For every original, every accepted pair at $n\ge2$, and every integer
$j\ge1$,

$$
\|R'-ERD\|_{H'\to H'}\le a_n,\qquad
\|R'^j-ER^jD\|_{H'\to H'}\le j d_n.
\tag{116.14}
$$

Both estimates are on the whole successor space.

Proof. Finite self-adjoint nonnegative spectral calculus gives

$$
\|R\|_{H\to H_1}\le1,\qquad
\sqrt{\mathfrak a(Rf,Rf)}\le\tfrac12\|f\|_\mu,
\tag{116.15}
$$

and the corresponding two statements for $R'$.
Indeed the scalar multipliers are $(1+\lambda)^{-1/2}\le1$
and $\sqrt\lambda/(1+\lambda)\le1/2$ for every $\lambda\ge0$.
These facts include the zero eigenvalue.

Take arbitrary $h,k\in H'$, and put
$z=R'k$, $f=RDh$, and $g=z|_V$, the literal old restriction.
The actual born-edge energy gives

$$
\|z-Eg\|_{\mu'}\le\frac{\sqrt{\mathfrak a'(z,z)}}{\sqrt{N'}},
\qquad
\mathfrak a(g,g)\le\mathfrak a'(z,z),\qquad
\|g\|_\mu\le\sqrt r\,\|z\|_{\mu'}.
\tag{116.16}
$$

In particular $\|g\|_1\le\sqrt3\|k\|_{\mu'}$ and
$\|f\|_1\le\sqrt3\|h\|_{\mu'}$.

There is an exact cross-form identity
$\mathfrak a'(Ef,z)=\mathfrak a(f,g)$: $Ef$ has zero born-edge
gradient and its old-edge gradient is precisely that of $f$.
The two resolvent equations and $D=E^{*_\mu}$ therefore give

$$
\begin{aligned}
\langle k,Ef\rangle_{\mu'}
 &=\mathfrak a'(z,Ef)+\langle z,Ef\rangle_{\mu'}\\
 &=\mathfrak a(g,f)+\langle Dz,f\rangle_\mu\\
 &=\langle h,Eg\rangle_{\mu'}+\langle Dz-g,f\rangle_\mu,\\
\langle k,(R'-ERD)h\rangle_{\mu'}
 &=\langle h,z-Eg\rangle_{\mu'}
       -\langle Dz-g,f\rangle_\mu.
\end{aligned}
\tag{116.17}
$$

This equality uses arbitrary inputs and tests, with no ancestry-range
restriction. Summing the actual fibre in $Dz$ gives

$$
Dz-g=(W-I)g+b,\qquad
b(x)=\frac1r\sum_{\substack{y\in\mathcal Z\\\pi(y)=x}}
                        (z(y)-g(x)).
\tag{116.18}
$$

Lemma 116.3 bounds the $(W-I)g$ term in (116.17) by
$3\vartheta_n\|h\|_{\mu'}\|k\|_{\mu'}$. For the remaining term,

$$
\begin{aligned}
|\langle f,b\rangle_\mu|
&=\left|\frac1{N'}\sum_{y\in\mathcal Z}
              f(\pi(y))(z(y)-g(\pi(y)))\right|\\
&\le\sqrt{\frac2r}\,\|f\|_\mu
          \frac{\sqrt{\mathfrak a'(z,z)}}{\sqrt{N'}}\\
&\le\frac{\sqrt6}{2\sqrt{N'}}\|h\|_{\mu'}\|k\|_{\mu'}.
\end{aligned}
\tag{116.19}
$$

The factor two is the actual number of children per beta parent.
The first term of the last line in (116.17) is at most
$\|h\|_{\mu'}\|k\|_{\mu'}/(2\sqrt{N'})$ by (116.15)--(116.16).
Since $N'\ge N\ge\Delta_n$, this proves the first bound in (116.14).

For the powers, (116.15) also gives
$\|R^j\|_{H\to H_1}\le1$ for every $j\ge1$. Applying (116.8) to
$R f$ and $R^j g$ proves the sandwiched discrepancy estimate

$$
\|R(W-I)R^j\|_{H\to H}\le\vartheta_n\qquad(j\ge1).
\tag{116.20}
$$

Let $T_j=R'^j-ER^jD$. Because $DE=W$, there is the exact identity

$$
T_{j+1}
 =R'T_j+(R'-ERD)ER^jD+ER(W-I)R^jD.
\tag{116.21}
$$

The three bounds $\|R'\|\le1$, $\|E\|\|D\|\le3$ and (116.20)
give $\|T_{j+1}\|\le\|T_j\|+3a_n+3\vartheta_n$.
Starting from $\|T_1\|\le a_n$ proves
$\|T_j\|\le a_n+3(j-1)(a_n+\vartheta_n)\le j d_n$.
Thus the nonidentity factor $DE$ has been accounted for explicitly;
the identification maps were not treated as a unitary pair. $\square$

### 116.4 The uniform complete positive-time target

**Theorem 116.5 (positive two-map full-successor comparison).**
Fix $0<\varepsilon\le S<\infty$. Set

$$
M_{\varepsilon,S}=\frac{4Se^S}{e^2\varepsilon^2},\qquad
\omega_n(\varepsilon,S)=
 \min\left\{4,\ \inf_{j\ge1}
       \left(\frac{2M_{\varepsilon,S}}{\sqrt j}
                    +j3^j d_n\right)\right\}
\quad(n\ge2).
\tag{116.22}
$$

Then $\omega_n(\varepsilon,S)\to0$ and, on the complete original domain,

$$
\sup_{u\in\mathcal T}\ \sup_{t\in[\varepsilon,S]}
 \|S_{n+1}(t)-E_n S_n(t)D_n\|_{H_{n+1}\to H_{n+1}}
 \le\omega_n(\varepsilon,S).
\tag{116.23}
$$

The originals, unit signed successor inputs and unit successor linear
tests may all depend on $n$ and $t$. The conclusion does not require a
common upper spectral bound.

Proof. Reuse the elementary positive-contraction polynomial argument of
§115.3 with the resolvents in (116.13), rather than its edge covariances.
For $0<x\le1$ put $G_t(x)=e^{-t(1-x)/x}$ and put $G_t(0)=0$.
Finite spectral calculus gives

$$
G_t(R)=S(t),\qquad G_t(R')=S'(t).
\tag{116.24}
$$

All operators here are finite symmetric nonnegative functions of the
actual closed Laplacians, so the continuous functional calculus applies
also at the spectral endpoints. For the stated $t$ interval,
$0\le G_t\le1$ and
$|G_t'(x)|=t x^{-2}e^t e^{-t/x}\le M_{\varepsilon,S}$.
In particular $G_t$ has a common scalar Lipschitz bound, not an
assumed operator Lipschitz bound.

Its degree-$j$ Bernstein polynomial is

$$
p_{j,t}(x)=\sum_{i=0}^j G_t(i/j)\binom ji x^i(1-x)^{j-i}.
\tag{116.25}
$$

The binomial variance bound proves
$\sup_{x\in[0,1]}|G_t(x)-p_{j,t}(x)|
 \le M_{\varepsilon,S}/(2\sqrt j)$ uniformly in $t$.
Crucially, $p_{j,t}(0)=0$: its monomial expansion has no identity term.
The total absolute monomial coefficient sum is at most $3^j$, by
expanding the displayed powers and using $0\le G_t(i/j)\le1$.
Consequently (116.14) gives

$$
\begin{aligned}
\|S'(t)-ES(t)D\|
&\le\|G_t(R')-p_{j,t}(R')\|
 +\|E(G_t(R)-p_{j,t}(R))D\|\\
&\hspace{9mm}+\|p_{j,t}(R')-Ep_{j,t}(R)D\|\\
&\le\frac{2M_{\varepsilon,S}}{\sqrt j}+j3^j d_n.
\end{aligned}
\tag{116.26}
$$

The first two terms use $\|E\|\|D\|\le3$.
Also $\|S'(t)\|\le1$ and $\|ES(t)D\|\le3$, so four is a valid
uniform cap. Taking the infimum proves (116.23).
First fixing $j$ and letting $n$ grow, then letting $j$ grow, proves
the limit in (116.22).

For an explicit source-independent threshold at accuracy $\delta>0$,
choose an integer $j>(4M_{\varepsilon,S}/\delta)^2$ and take any
$n_0\ge2$ with $j3^j d_n<\delta/2$ for all $n\ge n_0$.
The formulae (116.7), (116.13) are decreasing to zero for $n\ge2$,
so one may choose the first such $n_0$ by their displayed scalar
inequality. Then (116.23) is less than $\delta$ for every original
and every $n\ge n_0$.
This is a universal proof; finite matrix trends are not its premise.
$\square$

### 116.5 Conservative ingress and the different readout endpoints

**Corollary 116.6 (full tests, ingress and positive-time old readouts).**
With $\omega_n=\omega_n(\varepsilon,S)$, for every
$t\in[\varepsilon,S]$,

$$
\begin{aligned}
\|S'(t)C-ES(t)\|_{H\to H'}&\le\sqrt3\,\omega_n,\\
\|S'(t)F-r^{-1}ES(t)\|_{H\to H'}&\le(\sqrt3/r)\,\omega_n,\\
|\langle k,(S'(t)-ES(t)D)h\rangle_{\mu'}|
 &\le\omega_n\|k\|_{\mu'}\|h\|_{\mu'}.
\end{aligned}
\tag{116.27}
$$

For an old readout $g$, let $Qg=r\,\operatorname{zeroext}_V(g)$.
Then

$$
\begin{aligned}
\|Qg\|_{\mu'}&=\sqrt r\,\|g\|_\mu,&
\langle Qg,ES(t)f\rangle_{\mu'}&=\langle g,S(t)f\rangle_\mu,\\
|\langle Qg,S'(t)Cf\rangle_{\mu'}
               -\langle g,S(t)f\rangle_\mu|
 &\le3\omega_n\|g\|_\mu\|f\|_\mu.
\end{aligned}
\tag{116.28}
$$

The exact ingress pairing $\langle Eg,Cf\rangle_{\mu'}=\langle g,f\rangle_\mu$
and the positive-time pairing in (116.28) are different endpoint contracts.

Proof. Multiply (116.23) by $C$ on the right and use $DC=I$,
then divide by $r$ for $F$. Pairing the full norm estimate with arbitrary
$k,h$ proves the third line of (116.27). Literal old zero extension gives
$\|Qg\|_{\mu'}^2=r\|g\|_\mu^2$ and the exact pairing in (116.28).
Pair its error with the first line of (116.27) and use
$\sqrt r\,\sqrt3\le3$. $\square$

No statement that $\langle Eg,S'(t)Cf\rangle_{\mu'}$ uniformly approaches
$\langle g,S(t)f\rangle_\mu$ for every old $g$ is part of this corollary.
Inserting $Eg$ instead of $Qg$ in its limiting expression gives the
different exact quantity
$\langle g,W S(t)f\rangle_\mu$. The estimate (116.8) does not bound this
uniformly by $\langle g,S(t)f\rangle_\mu$ when $g$ is an arbitrary
unsmoothed unit vector. Likewise $D$ is an exact ingress reverse,
not a claimed reverse of the old state after heat.

A literal evaluation at a successor address has probability-functional
norm $\sqrt{N'}$, with Riesz vector $N'\delta_y$. Thus (116.23)
bounds its error on a unit probability input by
$\sqrt{N'}\,\omega_n$, without a source-uniform absolute point guarantee.
For an old point readout in (116.28), the bound carries $\sqrt N$.
All hidden signed modes remain in the operator domain even when a
constructor or a particular point readout does not detect them.

### 116.6 Endpoints, source services and the remaining bridge

**Proposition 116.7 (zero time and exact finite distinctions).**
The finite identities above include both singleton labels and empty
birth blocks. With births, zero time cannot be included in the uniform
full-successor convergence: there is a unit $h\in\ker D$ and

$$
(I-ED)h=h,\qquad \|I-ED\|_{H'\to H'}\ge1.
\tag{116.29}
$$

The conservative ingress $C$ sends uniform old density to $r/m$,
rather than to the new uniform equilibrium whenever $m$ is nonconstant.
The family $ES(t)D$ is positive, but is not in general an exact finite
conservative semigroup on the successor.

Proof. For an alpha singleton the accepted alpha-to-beta step has no
birth, $N=N'=1$, and $E=D=C=I$. For a beta singleton the successor has
three nodes, $r=m=3$, $E$ repeats the old value, $D$ takes the mean,
and $C=E$. These satisfy all displayed finite contracts; no edge or
inverse is inserted into the singleton old carrier.
An empty birth block on a general old source similarly gives
$V'=V$, $r=m=1$ and the same underlying operators and identity maps.

With births $|V'|>|V|$, so $D$ has a nonzero kernel by $DC=I$.
Any unit vector in that kernel proves (116.29). For example opposite
values on two born siblings give such a vector. All sources have births
at sufficiently large accepted epochs, including the alpha orbit, so
this is also a uniform-domain zero-time obstruction.

The constant and integral formulae are already (116.4).
In particular $ED$ need not be the identity at zero. On a pair with
nonconstant $m$, conservation of $ES(t)D$ would require
$S(t)W\mathbf1=\mathbf1$: its successor integral is
$\langle S(t)W\mathbf1,Dh\rangle_\mu$, whereas the integral of $h$ is
$\langle\mathbf1,Dh\rangle_\mu$, and $D$ is onto.
As $S(t)$ is invertible and fixes constants at every finite $t$,
that equality would force $W\mathbf1=\mathbf1$, which fails.
Thus no exact finite conservative-semigroup contract is supplied.
$\square$

**Mathematical citation 116.8 (ordinary synthesis and actual operations).**
IV §108 supplies the literal birth/count identities, uniform ratio and
bounded-gradient beta corrector; IV §112.2 supplies their all-node
accepted-step correspondence. Section 115 already supplies complete
signed-state comparison and consecutive polar transfers. Its compact
positive-time scalar functional calculus argument is reused in
(116.24)--(116.26). Finite self-adjoint spectral calculus has exactly the
hypotheses of the mature supplier cited there, Teschl,
[*Mathematical Methods in Quantum Mechanics*, Theorem 3.7 and Theorem
6.6](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf):
the operators here are finite symmetric nonnegative, and their resolvents
are positive contractions. No covariance norm bound is needed.

The varying-space form/semigroup framework of Mugnolo--Nittka--Post,
[*Norm convergence of sectorial operators on varying Hilbert spaces*,
Definition 2.3 and Example 3.9](https://files.ele-math.com/articles/oam-07-54.pdf),
is context, not a theorem invoked with unverified identification
hypotheses. In particular (116.8) is not a small $H$-operator norm of
$DE-I$, and an automatic multiplication of identification maps would
miss (116.20). The new source-specific ordinary synthesis is the full
successor estimate (116.23), paid by the literal mass discrepancy,
arbitrary successor resolvent tests, and the compositional correction.
The positive local finite identities alone would not settle that target.
These deductions are repo-derived, without an exhaustive novelty or
worldwide priority claim.

The exact arbitrary-clock finite obstruction in §114 remains intact.
The centered ancestry obstruction of IV §109 remains intact: the present
claim compares $S'$ with $ESD$ and uses the different ingress $C$;
it does not assert same-map intertwining $S'E=ES$.
Neither positivity nor locality makes $C$ a positive equilibrium-preserving
isometry with a positive unital reverse. Its norm bounds and attained-range
recovery are (116.5), with $D\mathbf1=m/r$.

The field maps require genuinely acquired source data: actual addresses
and birth-parent incidence, the beta mask, and the actual counts $N,N'$.
Conditional on an authenticated stationary register and lawful access,
the reply-driven full-description acquisition of IV §112.5 and §115.6
allows their finite local calculation. This is a sufficient paid route,
not a free size/index oracle or an optimized uniform acquisition bill.
Computing a successor from a retained description is not a fresh Read
or an executed Apply. Old version records and current version replies,
repeated and absent invocations, and the complete chronological history
retain their existing distinctions.

The native contract is exactly IV Contract 112.1a: four-valued
constructor Read, accepted/refused actual Apply under its declared common
guard, and absorbing Stop on the same original-root register.
A refused attempt leaves the carrier, operator and epoch unchanged;
its comparison uses identity maps on that unchanged carrier.
Stop executes no suffix and has no fictitious successor. The analytic
limit is indexed by accepted epochs, conditional on their being reached;
no guard is assumed to grant infinitely many updates. The uncapped
all-accepted service and every declared lawful guarded history retain
their original scope.

On the branch service the entire INITIAL target remains IV (112.2):
the reached ordered list $(L,R)$, exterior
$\langle\square_1,\square_2\rangle$, and the complete partition according
to equality of the two entire initial ordered subtrees. No heat value,
birth mask or current-row target replaces it. Other original sources,
including the singletons, remain in the mathematical comparison domain.

[Native Birth Provenance §10](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md)
owns its same-$r,q$ joint acquired/exported supplement and fresh-query
reduction on each full actual one-image fibre. Its paid acquisition,
common entry, authentic update, stationary reading and isolation are
assumptions; its class-root experiments are constructor tests.
[Native Alpha Recut Memory §13](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md)
owns its separated-age restricted-menu whole-row conflict graph and
binary retained-code criterion. Neither result supplies an occurrence
amplitude field, a heat actuator or a spatial port. Their source, history,
permission and resource contracts are reused without extending them.

The integer $n$ is an accepted source epoch; $t$ is comparison time,
with unaccelerated heat parameters $Nt$ and $N't$.
Acquisition chronology, old-set occupation time of IV §108 and physical
elapsed time are separate. The modulus (116.22) does not identify them.
There is no zero-time or shrinking-time uniformity, inverse heat,
complete finite-spectrum recovery, automatic point accuracy or physical
clock conversion in this conclusion.

Constructor acquisition and local matrix calculation do not install
signed-amplitude preparation, lawful execution of $C$, $D$, $E$ or $F$,
closed-heat evolution or real-linear readout services. Encoding and
precision, computation/storage/communication prices, authentication,
access isolation, actuation permissions, physical duration, metric,
spatial dimension and stable matter still require their actual bridges.
The result narrows the original-source/operator/transport gap by a
positive, occurrence-local analytical correspondence on the complete
successor space. Native or physical implementation and spatial
propagation remain unsupplied. This is ordinary mathematical source,
with no new Lean/kernel, registration, freezing or physical verification
claim, and no completion of the ongoing through-2027 why-three programme.

## 116.99 追加锚（本行以下为增补区）
## 117. Uniform final heat after literal serial conservative ingress

The positive adjacent maps of §116 have a chronological conservative
product whose unsmoothed norm need not stay bounded. Nevertheless one
final positive dwell compares uniformly with heat on the initial carrier,
over all finite original sources and all finite accepted horizons. The
proof retains the chronological split, including the mass left forever
at each parent when it becomes internal.

### 117.1 The literal products and their cofinal ancestry bounds

**Definition 117.1 (serial ingress on the actual finite history).** For
every original $u\in\mathcal T$ retain exactly $s_j=\rho^ju$, $V_j$,
$N_j$, $\mu_j$, $H_j$, $L_j$ and $A_j=N_jL_j$ of (116.1), with
$S_j(t)=e^{-tA_j}$. Thus every original bracket, order, label and repeated
occurrence is retained, with $\rho\alpha=\beta$,
$\rho\beta=\langle\beta,\alpha\rangle$ and homomorphism on pairs.
The operator is the closed unit-edge counting Laplacian. Its energy is
$\mathfrak a_j(f,f)=\sum_{\{x,y\}\in\mathcal E_j}(f(x)-f(y))^2$,
and $\|f\|_{1,j}^2=\|f\|_{\mu_j}^2+\mathfrak a_j(f,f)$.
No counting occurrence or edge is removed by probability normalization.

Use exactly the adjacent maps (116.3), now writing their actual fibre
size as $b_j=1+2\mathbf1_{\{\text{actual beta leaf of }s_j\}}$:

$$
\begin{aligned}
r_j&=N_{j+1}/N_j,& E_jf&=f\circ\pi_j,&
D_j&=r_j^{-1}E_j^{\mathsf T},&
C_j&=r_jE_j\operatorname{diag}(b_j)^{-1},\\
P_{n,m}&=C_{m-1}\cdots C_n,&
E_{n,m}&=E_{m-1}\cdots E_n,&
D_{n,m}&=D_n\cdots D_{m-1}=E_{n,m}^* .
\end{aligned}
\tag{117.1}
$$

Here and below adjoints use the indicated probability Hilbert spaces.
All empty products are identities. The map $\pi_j$ fixes old addresses
and takes each newborn to its actual beta parent. The product $P_{n,m}$
has no intervening heat. Define its counting kernel and probability
adjoint by

$$
Q_{n,m}=\frac{N_n}{N_m}P_{n,m},\qquad
T_{n,m}=Q_{n,m}^{\mathsf T}=P_{n,m}^*.
\tag{117.2}
$$

These are analytical maps computed from genuine birth relations, not
additional actions in the native menu.

The finite contracts of Theorem 116.2 compose without an approximation:
$P,E,D$ are positive, $E_{n,m}\mathbf1=\mathbf1$,
$D_{n,m}P_{n,m}=I$, and $P_{n,m}$ and $D_{n,m}$ preserve their respective
probability integrals. Also $Q_{n,m}$ preserves the counting sum.
The identity $DP=I$ follows by cancelling each adjacent $D_jC_j$ in
reverse order; integral preservation follows by composing the adjacent
integral identities. It recovers only the attained unheated ingress
range. In general $D_{n,m}\mathbf1\ne\mathbf1$; it is not an inverse
heat or an arbitrary-successor recovery assertion.

**Lemma 117.2 (bounded ancestry and summable mass and restriction errors).**
Put $c=\varphi^{-1}$, $\Delta_j=2F_{j+1}-1$, and, for $n\ge2$, define

$$
B=\sqrt6,\qquad
h_n=\frac{\varphi^{-n/2}}{1-\varphi^{-1/2}},\qquad
a_n=60h_n,\qquad k_n=Bh_n.
\tag{117.3}
$$

For every original $u$, every finite $m\ge n$, and all $f,g\in H_n$,
with $W_{n,m}=D_{n,m}E_{n,m}$,

$$
\begin{aligned}
\|E_{n,m}\|=\|D_{n,m}\|&\le B,\\
\mathfrak a_m(E_{n,m}f,E_{n,m}g)&=\mathfrak a_n(f,g),\\
|\langle(W_{n,m}-I)f,g\rangle_{\mu_n}|
 &\le a_n\|f\|_{1,n}\|g\|_{1,n}.
\end{aligned}
\tag{117.4}
$$

For an arbitrary final field $z\in H_m$, let $z_j=z|_{V_j}$ be its
literal restriction and $g=z_n$. Then

$$
\mathfrak a_n(g,g)\le\mathfrak a_m(z,z),\qquad
\|z-E_{n,m}g\|_{\mu_m}\le k_n\sqrt{\mathfrak a_m(z,z)}.
\tag{117.5}
$$

Proof. Let $\ell$ be the number of leaves of the actual $s_n$, and set
$d=m-n$. Each old internal vertex has a singleton ancestry fibre.
Each old alpha leaf has its entire actual $T_d$ fibre, with $\Delta_d$
vertices; each old beta leaf has its actual $T_{d+1}$ fibre. The count
supply IV (108.9), applied to $s_n$ itself, gives

$$
N_n=2\ell-1,\qquad N_m\ge\ell\Delta_d,\qquad
1\le\Delta_d\le\Delta_{d+1}\le3\Delta_d\quad(d\ge0).
\tag{117.6}
$$

The last inequality follows either from the Fibonacci recurrence or
from the adjacent at-most-three birth factor. If $v(x)$ is the final
fibre size of $x\in V_n$, then

$$
\|E_{n,m}f\|_{\mu_m}^2
 =\frac1{N_n}\sum_{x\in V_n}\frac{v(x)}{N_m/N_n}f(x)^2,
\qquad \frac{v(x)}{N_m/N_n}\le6.
\tag{117.7}
$$

This proves the first bound, including $d=0$. New edges have zero
ancestry-extension gradient, proving the energy identity. In particular
$\|E_{n,j}f\|_{1,j}\le B\|f\|_{1,n}$ at every intermediate $j$.

Reuse the relative adjacent mass estimate (116.8), with its exact
$\vartheta_j$ in (116.7). Telescoping the probability inner products
along this same history gives

$$
\begin{aligned}
\langle(W_{n,m}-I)f,g\rangle_{\mu_n}
 =\sum_{j=n}^{m-1}
 \langle(D_jE_j-I)E_{n,j}f,E_{n,j}g\rangle_{\mu_j}.
\end{aligned}
\tag{117.8}
$$

Its modulus is at most
$6\sum_{j=n}^{m-1}\vartheta_j\|f\|_{1,n}\|g\|_{1,n}$.
For clarity the following geometric bound makes the constants explicit:

$$
\Delta_j\ge\varphi^{j-1},\qquad
\vartheta_j\le10\varphi^{-j/2}\quad(j\ge2),\qquad
\sum_{j=n}^{\infty}\Delta_{j+1}^{-1/2}\le h_n.
\tag{117.9}
$$

Indeed $F_{j+1}\ge\varphi^{j-1}$ by induction and
$\Delta_j\ge F_{j+1}$. In (116.7) the four terms of $\vartheta_j$ are
bounded, respectively, by
$3\sqrt{3\varphi/2}\varphi^{-j/2}$,
$\sqrt2c\varphi^{-j/2}$, $2c\varphi^{-j/2}$ and
$(1+2c^2)\varphi^{-j/2}$. Here the last term is
$(c+2c^{j+1})/\Delta_j$, and $j\ge2$ was used.
Their constants sum to less than ten: $\varphi<5/3$, $c<2/3$ give
respective upper bounds $5,1,2,2$. This proves (117.9) and then
the mass bound in (117.4). It is a form bound, not a small raw
$H_n$-operator norm of $W_{n,m}-I$.

For (117.5), the difference $z_{j+1}-E_jz_j$ vanishes on old vertices
and has exactly one born-edge difference at each newborn. Consequently

$$
\|z_{j+1}-E_jz_j\|_{\mu_{j+1}}
 \le\frac{\sqrt{\mathfrak a_m(z,z)}}{\sqrt{N_{j+1}}},\qquad
z-E_{n,m}g=\sum_{j=n}^{m-1}
 E_{j+1,m}(z_{j+1}-E_jz_j).
\tag{117.10}
$$

Use $\|E_{j+1,m}\|\le B$, $N_{j+1}\ge\Delta_{j+1}$ from
IV (108.9), and (117.9). Restriction retains a subset of the actual
edges, proving the other assertion. No original-size, depth or balance
bound was imposed. $\square$

### 117.2 The actual chronological density after many births

**Lemma 117.3 (bounded averaged displacement of serial ingress).**
For every $n\ge0$, finite $m\ge n$ and final field $z$, with
$g=z|_{V_n}$,

$$
\|T_{n,m}z-g\|_{\mu_n}
 \le\sqrt{\frac2{7N_n}}\sqrt{\mathfrak a_m(z,z)}.
\tag{117.11}
$$

The estimate concerns the literal chronological $P_{n,m}$, even when
its raw Hilbert norm is large.

Proof. After cancelling the global factors $r_j$, the counting kernel
$Q_{n,m}$ is the chronological product of $r_j^{-1}C_j$.
At an actual beta split its mass is divided equally among the retained
parent and its two born children. At an alpha-to-beta step or an
internal vertex it remains at that very address. Once a parent has
become internal its retained third stays there in all later factors.
Every column is therefore a probability supported in its actual
ancestry fibre. An old internal vertex has its point-mass column.

Fix an old leaf $x$. For every actual descendant edge $e$ in its final
fibre, let $d(e)\ge1$ be the depth of its child below $x$. Exactly
$d(e)$ genuine branch splits are needed along that path. Each sends
one third of the incoming mass to the selected child, and no subsequent
split moves mass out of that child's subtree. Hence the total final
column mass below $e$ is exactly $3^{-d(e)}$. Waiting at an alpha
changes the birth epoch but not this coefficient. Finite path summation
therefore gives

$$
(T_{n,m}z)(x)-z(x)
 =\sum_{e\text{ strictly below }x}3^{-d(e)}\nabla_ez,
\qquad
\sum_{e\text{ strictly below }x}3^{-2d(e)}
 \le\sum_{d\ge1}2^d3^{-2d}=\frac27.
\tag{117.12}
$$

The edge sum on the left is finite. The convergent geometric series
only bounds it; no infinite or completed source is introduced.
Cauchy--Schwarz bounds the square of the first expression by
$\frac27\sum_{e\text{ below }x}|\nabla_ez|^2$.
The descendant edge sets of different old leaves are disjoint, while
the difference vanishes at every old internal vertex. Sum over all
old vertices and divide by $N_n$ to obtain (117.11). This also handles
an empty born set and an unchanged singleton. $\square$

For example, start from the beta singleton and take two accepted steps.
The final five addresses are $\varepsilon,L,R,LL,LR$. The one counting
column has weights $1/3,1/9,1/3,1/9,1/9$ in that order. They sum to one
and are not the uniform final-fibre weights $1/5$. Thus (117.12) has
not replaced serial ingress by final-fibre redistribution. At a permanent
old internal root the known raw amplification
$\sqrt{N_m/N_n}$ is compatible with (117.11), which bounds its
energy-tested adjoint rather than the raw ingress norm.

### 117.3 A uniform resolvent bound despite raw amplification

**Theorem 117.4 (cofinal serial resolvent comparison).** Let

$$
q_n=\sqrt{\frac2{7\Delta_n}},\qquad
\rho_n=3a_n+\frac{Bk_n}2+\frac{q_n}2
       =183h_n+\frac{q_n}2.
\tag{117.13}
$$

Choose $n_*\ge2$ so that, for every $n\ge n_*$,
$a_n\le1/2$, $k_n\le1$ and $\rho_n\le1$. These displayed scalar
sequences decrease to zero, so such a source-independent $n_*$ exists.
Write $R_j=(I+A_j)^{-1}$. For every original $u$, finite $m\ge n\ge n_*$
and integer $l\ge1$,

$$
\begin{aligned}
\|R_mP_{n,m}-E_{n,m}R_n\|&\le\rho_n,\\
\|R_mP_{n,m}\|&\le B+\rho_n,\\
\|R_m^lP_{n,m}-E_{n,m}R_n^l\|&\le2l\rho_n.
\end{aligned}
\tag{117.14}
$$

All norms are $H_n\to H_m$; the constants are independent of the horizon.

Proof. Abbreviate the products to $P,E,D,T$ and put $W=DE$.
Take arbitrary $f\in H_n$, $v\in H_m$, and set

$$
z=R_mv,\qquad g=z|_{V_n},\qquad w=R_nf.
\tag{117.15}
$$

The finite nonnegative spectral estimates (116.15), which include the
zero eigenvalue, give
$\|z\|_{\mu_m}\le\|v\|_{\mu_m}$,
$\sqrt{\mathfrak a_m(z,z)}\le\|v\|_{\mu_m}/2$ and
$\|w\|_{1,n}\le\|f\|_{\mu_n}$.
The form estimate (117.4) and (117.5) control the literal restriction
without any bound on $N_m/N_n$:

$$
\begin{aligned}
(1-a_n)\|g\|_{1,n}^2
 &\le\|Eg\|_{\mu_m}^2+\mathfrak a_n(g,g)\\
 &\le(\|z\|_{\mu_m}+k_n\sqrt{\mathfrak a_m(z,z)})^2
           +\mathfrak a_m(z,z),\\
\|g\|_{1,n}&\le\sqrt5\|v\|_{\mu_m}\le3\|v\|_{\mu_m}.
\end{aligned}
\tag{117.16}
$$

The first inequality follows from the lower mass bound
$\|Eg\|^2\ge\|g\|^2-a_n\|g\|_{1,n}^2$; the last uses
$a_n\le1/2$, $k_n\le1$ and the preceding spectral estimates.

Because $Ew$ is constant along every post-$n$ edge,
$\mathfrak a_m(z,Ew)=\mathfrak a_n(g,w)$ exactly.
The two resolvent equations, $P^*=T$ and $E^*=D$ yield

$$
\begin{aligned}
\langle v,(R_mP-ER_n)f\rangle_{\mu_m}
 &=\langle f,Tz-g\rangle_{\mu_n}
                -\langle Dz-g,w\rangle_{\mu_n},\\
Dz-g&=D(z-Eg)+(W-I)g.
\end{aligned}
\tag{117.17}
$$

For completeness, $\langle v,Ew\rangle
=\mathfrak a_n(g,w)+\langle Dz,w\rangle
=\langle g,f\rangle+\langle Dz-g,w\rangle$; subtraction from
$\langle v,R_mPf\rangle=\langle Tz,f\rangle$ proves the first line.
It holds for every signed final test $v$.

Lemma 117.3 bounds the first term in (117.17) by
$q_n\|v\|\|f\|/2$. Equations (117.4)--(117.5) and (117.16) bound
the two parts of the second term, respectively, by
$Bk_n\|v\|\|f\|/2$ and $3a_n\|v\|\|f\|$.
This proves the first line of (117.14); the second follows from
$\|ER_n\|\le B$.

To compare higher powers, let $l\ge1$ and set
$h=R_n^lf$, $w=R_n^{l+1}f$. The same cross-form calculation gives

$$
\langle v,(R_mER_n^l-ER_n^{l+1})f\rangle_{\mu_m}
 =\langle Dz-g,h-w\rangle_{\mu_n}.
\tag{117.18}
$$

Both $R_n^l$ and $R_n^{l+1}$ map $H_n$ to its form space with norm
at most one. Thus $\|h-w\|_{1,n}\le2\|f\|$.
The decomposition in (117.17) now bounds (117.18) by
$2(3a_n+Bk_n/2)\|v\|\|f\|$.
Writing $U_l=R_m^lP-ER_n^l$, the exact recursion is

$$
U_{l+1}=R_mU_l+(R_mER_n^l-ER_n^{l+1}).
\tag{117.19}
$$

Since $\|R_m\|\le1$, it gives
$\|U_l\|\le\rho_n+2(l-1)(3a_n+Bk_n/2)\le2l\rho_n$.
No raw bound on $P$, identification of $DE$ with $I$, or final-fibre
replacement was used. $\square$

### 117.4 The source- and horizon-uniform final-heat theorem

**Theorem 117.5 (literal serial ingress with one final positive dwell).**
Fix $0<\varepsilon\le T<\infty$, and set

$$
\begin{aligned}
K_{\varepsilon,T}&=\frac{e^T}{e\varepsilon},\\
M_{\varepsilon,T}&=e^T\left(\frac4{e^2\varepsilon^2}
                       +\frac{27T}{e^3\varepsilon^3}\right),\\
\eta_n(\varepsilon,T)
 &=\inf_{J\in\mathbb N_{\ge1}}\left\{
 \frac{3M_{\varepsilon,T}}{\sqrt J}
 +2K_{\varepsilon,T}(J+1)3^J\rho_n\right\}
 \quad(n\ge n_*).
\end{aligned}
\tag{117.20}
$$

Then $\eta_n(\varepsilon,T)\to0$, and

$$
\sup_{u\in\mathcal T}\ \sup_{m\ge n,\ m<\infty}\ \sup_{t\in[\varepsilon,T]}
\|S_m(t)P_{n,m}-E_{n,m}S_n(t)\|_{H_n\to H_m}
 \le\eta_n(\varepsilon,T)
 \qquad(n\ge n_*).
\tag{117.21}
$$

Every original source, finite horizon, time, unit signed initial field
and unit signed final linear test may move jointly in this supremum.

Proof. Reuse the finite continuous functional calculus and Bernstein
approximation method of §§115.3 and 116.4. The required scalar function
is different because $P$ has no uniform raw norm. Put

$$
G_t(x)=e^{-t(1-x)/x},\qquad
H_t(x)=x^{-1}G_t(x)\quad(0<x\le1),\qquad
G_t(0)=H_t(0)=0.
\tag{117.22}
$$

For every actual resolvent, $S_j(t)=H_t(R_j)R_j$.
Uniformly in $t\in[\varepsilon,T]$, the scalar bounds are

$$
\|H_t\|_\infty\le K_{\varepsilon,T},\qquad
|H_t'(x)|
 \le e^T(x^{-2}+Tx^{-3})e^{-\varepsilon/x}
 \le M_{\varepsilon,T}.
\tag{117.23}
$$

They follow by maximizing $y^re^{-\varepsilon y}$ for $r=1,2,3$;
the extension at zero is continuous and satisfies the same Lipschitz
bound. Let $p_{J,t}$ be its degree-$J$ Bernstein polynomial on $[0,1]$.
The already used binomial variance estimate and monomial expansion give

$$
\|H_t-p_{J,t}\|_\infty\le\frac{M_{\varepsilon,T}}{2\sqrt J},
\qquad
\sum_{i=0}^J|[x^i]p_{J,t}|\le K_{\varepsilon,T}3^J.
\tag{117.24}
$$

Now apply the polynomial to the already smoothed product $R_mP$:

$$
\begin{aligned}
\|S_m(t)P-ES_n(t)\|
\le{}&\|(H_t-p_{J,t})(R_m)R_mP\|\\
 &+\|E(H_t-p_{J,t})(R_n)R_n\|\\
 &+\|p_{J,t}(R_m)R_mP-Ep_{J,t}(R_n)R_n\|\\
\le{}&\frac{(2B+1)M_{\varepsilon,T}}{2\sqrt J}
       +2K_{\varepsilon,T}(J+1)3^J\rho_n\\
\le{}&\frac{3M_{\varepsilon,T}}{\sqrt J}
       +2K_{\varepsilon,T}(J+1)3^J\rho_n.
\end{aligned}
\tag{117.25}
$$

The first two terms use $\|R_mP\|\le B+1$, $\|E\|\le B$ and
$\|R_n\|\le1$. Every monomial in the last term is a coefficient times
$U_{i+1}$ of (117.14), so (117.24) bounds it as displayed.
The inequality $2B+1<6$ gives the last line. In particular no
approximation error is multiplied by the raw norm of $P$.
Taking the infimum proves (117.21). First fix $J$ and let $n$ tend
to infinity, and then let $J$ tend to infinity; this proves the limit.

A completely scalar accuracy threshold is available. Given $\delta>0$,
choose an integer

$$
J>(6M_{\varepsilon,T}/\delta)^2,
\qquad
n_0\ge n_*\text{ such that }
\rho_{n_0}<\frac{\delta}{4K_{\varepsilon,T}(J+1)3^J}.
\tag{117.26}
$$

The closed decreasing formulae (117.3), (117.13) make this a specified
finite threshold, independent of the original and horizon. For all
$n\ge n_0$, (117.25) is less than $\delta$. The proof uses only finite
actual carriers; no completed endpoint or source-history splicing is
involved. $\square$

### 117.5 Endpoints, mass, readouts and actual service correspondence

**Corollary 117.6 (joint signed tests and finite endpoint distinctions).**
For all $n\ge n_*$, finite $m\ge n$, $t\in[\varepsilon,T]$ and arbitrary
signed $f\in H_n$, $g\in H_m$,

$$
|\langle g,(S_m(t)P_{n,m}-E_{n,m}S_n(t))f\rangle_{\mu_m}|
 \le\eta_n(\varepsilon,T)\|g\|_{\mu_m}\|f\|_{\mu_n}.
\tag{117.27}
$$

For counting-mass ingress the corresponding comparison is

$$
\left\|S_m(t)Q_{n,m}-\frac{N_n}{N_m}E_{n,m}S_n(t)\right\|
 \le\frac{N_n}{N_m}\eta_n(\varepsilon,T).
\tag{117.28}
$$

Proof. Pair (117.21) with $g$ for the first statement, and multiply it
by $N_n/N_m$ for the second. $\square$

The case $m=n$ has exactly zero error for every $t\ge0$.
The alpha singleton's first accepted step has no births and all three
adjacent maps are identities. The beta singleton's first accepted step
has $E=C$ repeating its value and $D$ taking the three-node mean.
These are precisely the endpoint contracts already checked in §116.6;
the chronological argument includes them and every empty birth factor.
They require no deleted root or added edge.

The closed zero-eigenvalue mode is retained throughout:
$R_j\mathbf1=S_j(t)\mathbf1=\mathbf1$ and $H_t(1)=1$.
The exact conserved integral on the left is
$\int S_m(t)P_{n,m}f\,d\mu_m=\int f\,d\mu_n$.
An ancestry extension need not preserve the integral at a finite horizon.
Its mass error after old heat is nevertheless controlled by (117.4):

$$
\left|\int E_{n,m}S_n(t)f\,d\mu_m-\int f\,d\mu_n\right|
 \le a_n\sqrt{1+(2e\varepsilon)^{-1}}\,\|f\|_{\mu_n}.
\tag{117.29}
$$

Indeed the difference is
$\langle(W_{n,m}-I)S_n(t)f,\mathbf1\rangle$, and
$\|S_n(t)f\|_{1,n}^2\le[1+(2et)^{-1}]\|f\|^2$ by the nonnegative
spectral bound $\lambda e^{-2t\lambda}\le(2et)^{-1}$.
Thus mass was neither centered away nor assumed exactly preserved by $E$.
There is no assertion that $E_{n,m}S_n(t)D_{n,m}$ is an exact finite
conservative successor semigroup. Reverse recovery remains $DP=I$
on the unheated attained range, with no inverse heat.

A literal final point evaluation has probability-functional norm
$\sqrt{N_m}$. Therefore (117.27) supplies at most
$\sqrt{N_m}\eta_n\|f\|$ for such a point, not uniform absolute point
accuracy. Independently injected arbitrary later fields in $H_m$ are
not the input domain of (117.21). Every old signed direction and every
final unit linear test are included. Whole-successor cofinal two-map
comparison and interleaved shrinking-dwell products are separate targets;
(117.21) does not settle them or the exact finite clock obstruction of
§114.

**Mathematical citation 117.7 (reused supplies and the actual owner split).**
The ordinary source-specific additions are the cofinal mass/restriction
estimates, the exact chronological $3^{-d}$ displacement bound and the
resulting source- and horizon-uniform final-heat estimate. IV §§108,
112 and 113 and V §§115--116 supply the original occurrence geometry,
counts, adjacent maps and comparison context. The adjacent identities,
beta corrector, acquisition foundation, continuous functional calculus
and Bernstein variance argument are reused. Finite spectral calculus
has precisely the finite symmetric nonnegative hypotheses already
checked in §116.8, with the same mature supplier, Teschl,
[*Mathematical Methods in Quantum Mechanics*, Theorems 3.7 and 6.6](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
No varying-space convergence theorem is invoked with unchecked map
hypotheses. These are repo-derived ordinary deductions without a global
literature-priority, Lean/kernel or physical evidence claim.

[Native Leaf Depth Contact, Definitions 1.1--1.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md)
and [Acquired Relation History, Assumption 1.3](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md)
own the finite free ordered source domain, original entire rows,
authentic entry and same-register Read/ApplyRho/Stop menu.
The source-indexed operator correspondence is IV (112.5)--(112.9):
every accepted update retains precisely the old addresses and adds
precisely the two children of each actual beta parent, with the closed
unit-edge block. The controller records actual replies and acceptances,
and retains Stop. It neither certifies the analytical estimate nor
gains a new field operation from the source-indexed matrices.

The inspected `NativeSerialMachine` declarations `Op`, `nativeStep`,
`Run` and `actual_register_execution` carry one register and its exact
update/read trace; the interpreter receives control, not an unknown
source. The inspected `NativeSerialEffective` declarations
`OriginalState`, `OriginalRun` and `original_service_simulation` retain
unrestricted finite common input, workspace, certified epoch, acquired
history and terminal output. These Lean statements were read, not
compiled here. Their all-accepted API is not a proof of guarded refusal.
The separately declared common history-only guard is IV Contract 112.1a.

Under the uncapped original menu every requested finite block is reached
by actual serial updates. Under a declared common effective
$G(\gamma,e,H)$, permission depends only on the common parameter, actual
accepted epoch and complete chronological history. Each observed
acceptance supplies its exact factor in (117.1); refusal changes neither
carrier nor epoch and contributes identity. Repeated and absent Reads
retain their actual addresses and literal replies; local work is local
work. Stop is absorbing and supplies no suffix. The theorem applies
to every finite endpoint actually reached, without a cofinal-permission
promise for a guarded service. It does not use a source-indexed
permission oracle.

`ActualTreeReadoutAcquisition` and its Scribe own the immutable
four-reply queries, distinct-address charge, reply-driven
`acquisitionStep`/`frontier` and report-only `restore`. Their original
Boolean third-substitution-image `Strategy` remains unchanged. Reuse
only the acquisition/restoration phase on a lawful authenticated
stationary epoch-zero native register, exactly as IV §112.5 and V §115.6
do. Its fuel is a pointwise termination witness, not initial size advice.
The separate acquired-description consumer may retain the full syntax
and compute all actual masks, counts and finite factors from that syntax
and observed accepted records; no finite-alphabet restriction is added.
It does not require the supplier to solve equality, Apply/refusal,
amplitude acquisition, serial field execution or physical timing.

With $S(u)=|V_u|$ and $\Lambda(u)=\sum_{p\in V_u}|p|$, the inherited
phase coordinates are exactly
$(\text{raw Reads},\text{Apply attempts},\text{literal Read length},
\text{phase-distinct addresses})=(S,0,\Lambda,S)$.
They are finite sourcewise and unbounded across the original domain.
On the branch entry the separately paid pre-entry root remains: total
raw Reads $S+1$, literal length $\Lambda$, cumulative distinct addresses
$S$ on one immutable-source cache and incremental post-entry distinct
charge $S-1$. Separate empty phase ledgers charge $1$ and $S$.
No reset, refund or interphase tariff follows. Both singleton acquisition
phases have coordinates $(1,0,0,1)$; any actual pre-entry call is separately
counted. Preparation, authentication and access isolation remain supplied
premises.

The accepted epochs $n,m$, the $m-n$ accepted updates in the comparison
block, and actual Apply attempts are different coordinates. Retained
syntax and genuine acceptance records permit finite matrix calculation
without additional constructor queries. A calculated reply is not a
fresh Read; a calculated successor does not execute Apply. New-version
reacquisition has its own genuine calls and version evidence; old
immutable reports are not cached new-version reports.

The task target is still every original INITIAL row: reached holes in
original order, numbered concrete exterior and the complete whole-subtree
equality partition. On the branch service this is exactly IV (112.2).
The already paid description consumer may return that entire row.
Signed field tests and current successor rows do not replace it.

[Native Birth Provenance §10](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md)
supplies its conditional joint same-$r,q$ acquired/exported supplement
and stationary fresh-query feasibility reduction on each full actual
one-image fibre. Its acquisition, export, isolation and stationary-entry
premises remain its own; the root-type chart is not an arbitrary
occurrence amplitude field, and that existence reduction preserves
neither all native traces nor physical execution cost.
[Native Alpha Recut Memory §13](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md)
supplies its separated-age restricted-future-menu whole-row collisions
and retained-code criteria on its stated source families. Its code
alphabet is not an occurrence amplitude field. Neither owner supplies
an extra serial-heat obligation or actuator. The analytical consumer
owns (117.21); the acquisition producer and native-operation supplier
are used only within their actual supplied contracts.

The integers $n,m$ are observed accepted source counts. The variable
$t$ is normalized comparison time, with mathematical heat parameters
$N_nt$ and $N_mt$. The IV §108 old-set occupation inverse, paid
acquisition chronology and physical duration have different types.
Serial growth followed by one final dwell is not an interleaved heat
schedule, and neither schedule provides a native or physical clock
conversion. The theorem has no zero-time or shrinking-time uniformity.

Signed-amplitude preparation, lawful execution of $C,E,D$, closed-heat
actuation, real-linear amplitude measurement, precision/encoding prices,
matrix work/storage/communication prices, physical clocks, metrics,
spatial dimension and stable matter remain unsupplied. Their physical
realization is ASSUMED-UNVERIFIED. This limits an implementation claim;
it neither blocks nor refutes the conditional analytical theorem.
No new Lean, Blueprint, Reg, ingestion, registration, freezing, judge,
CI or physical verification is asserted. The full ongoing through-2027
why-three programme and its remaining spatial and implementation bridges
are not completed by this finite ordinary theorem.

## 117.99 追加锚（本行以下为增补区）

## 118. Signed INITIAL response and unread leaf cones within one entire-row fibre

### 118.1 Original sources, combined output and finite certificates

**Definition 118.1 (the signed INITIAL consumer and its history fibre).**
Use the authentic entry of [IV Definition 112.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md):
the retained epoch-zero root Read reports branch, the old root-cut row is
the constant one-hole row, and the original-root register is still INITIAL.
The retained relation history is empty and the certified epoch is zero.
The complete accessible state contains only that stipulated retained input
and common code and parameters. Its source
fibre is every finite ordered branch tree
$D=\{\langle v,w\rangle:v,w\in\mathcal T\}$, with no acquired size,
index, shape, archive or source law. Authentication and the complete access
cut remain premises of that entry. Retain the original substitution

$$
\rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,
\qquad \rho\langle v,w\rangle=\langle\rho v,\rho w\rangle.
$$

For INITIAL $u$, keep every occurrence at its original address, with
counting inner product, $N_u=|V_u|$, and the closed unit-edge operator

$$
(L_ug)(p)=\sum_{q\sim p}(g(p)-g(q)),\qquad
\langle g,L_ug\rangle=\sum_{\{p,q\}\in E_u}|g(p)-g(q)|^2.
$$

There is no root killing or boundary grounding. Define exactly

$$
f_u(p)=
\begin{cases}
+1,&p\text{ is an INITIAL alpha leaf},\\
-1,&p\text{ is an INITIAL beta leaf},\\
0,&p\text{ is an INITIAL branch occurrence},
\end{cases}
\qquad
R_u(t)=\bigl[e^{-tN_uL_u}f_u\bigr](\varepsilon).
\tag{118.1}
$$

The constant mode is included in this response. Fix common rationals
$t>0$ and $0<\epsilon<1/2$. The combined task returns, at the same
absorbing Stop, a rational $z$ and the entire INITIAL row

$$
\mathsf{Row}(u)=
\bigl((L,R),\langle\square_1,\square_2\rangle,\pi(u)\bigr),\qquad
\pi(u)=
\begin{cases}
\{\{1,2\}\},&u|_L=u|_R,\\
\{\{1\},\{2\}\},&u|_L\ne u|_R,
\end{cases}
\tag{118.2}
$$

with $|z-R_u(t)|\le\epsilon$. The partition compares entire ordered
subtrees. Actual later updates change neither INITIAL target.

Fix any deterministic effective controller $A$ with the common entry,
unrestricted finite-address four-valued Reads, serial same-register
Apply $\rho$, and Stop, under any fixed common guard of IV Contract 112.1a.
The original guard accepts every Apply without a cap. A separately declared
guard is a total effective $G(\gamma,e,H)$ depending only on the common
parameter, actual accepted epoch and complete chronological native history;
acceptance executes exactly $\rho$ and increments $e$, refusal changes
neither register nor epoch. Every status, repeated or absent Read and its
literal address remain observations. Local effective work uses only common
input and acquired history. There are no further source-dependent status,
timing or scheduler outputs. Sourcewise finite termination imposes no
uniform update, work or stopping-horizon bound.

For an actual finite terminal history $H$ and an entire row $r$, let

$$
\mathcal C_{A,G,H}(r)=
\{v\in D:A\text{ has that same terminal native history on }v,
\ \mathsf{Row}(v)=r\},
\qquad
\operatorname{rad}_t(H,r)=
\inf_{z\in\mathbb R}\sup_{v\in\mathcal C_{A,G,H}(r)}|z-R_v(t)|.
\tag{118.3}
$$

All common parameters are fixed in this definition. Equal histories from
the same entry also give equal local control, local work and terminal
output. Restricting this mathematical fibre to $r$ supplies no row oracle
to $A$. A semantic $\epsilon$ certificate for $(H,r,z)$ means the full
universal inequality in (118.3) for that $z$, together with correctness of
the entire row on the unrestricted history fibre. A leaf cone is covered
iff an actual requested word has that INITIAL leaf address as a prefix;
an absent reply can cover a cone in this sense without identifying its
INITIAL subtree. The separately paid pre-entry root Read covers no leaf
of a branch source.

### 118.2 A fixed-context perfect graft with the original signed field

**Theorem 118.2 (signed perfect-graft response limit).** Let $u\in D$,
let $x$ be any INITIAL leaf, and write $u=C[a]$ with a single hole at
that occurrence. For $\sigma\in\{+1,-1\}$, let $B_m^\sigma$ be the
perfect ordered binary tree of depth $m\ge0$, whose $2^m$ leaves are
alpha for $\sigma=+1$ and beta for $\sigma=-1$. Put
$v_m^\sigma=C[B_m^\sigma]$. Let $O=V_u\setminus\{x\}$ be the fixed
outside vertices, with their unchanged labels, and set

$$
\begin{aligned}
k&=|O|=N_u-1, & b&=\sum_{p\in O}f_u(p),\\
D_C&=\sum_{p\in O}\operatorname{dist}(p,x),
&K_C&=\max(2D_C,2k+6),\\
N_m&=k+2^{m+1}-1,
&c_C&=|b|+(k-1)/2.
\end{aligned}
\tag{118.4}
$$

Distances use the fixed context edges including the attachment to $x$;
$k\ge2$. For every fixed real $t>0$ and either sign,

$$
\left|R_{v_m^\sigma}(t)-\frac{\sigma}{2}\right|
\le \sqrt{N_m}\,e^{-tN_m/K_C}+\frac{c_C}{N_m}
\longrightarrow0.
\tag{118.5}
$$

The context is fixed while $m$ tends to infinity. The field, normalization,
all occurrences and operator in (118.5) are precisely (118.1) on each
finite INITIAL $v_m^\sigma$.

Proof. Graph automorphisms within the perfect graft fix every
outside occurrence and commute with the original closed Laplacian. They
fix $f_{v_m^\sigma}$ too. Thus the heat trajectory belongs to the invariant
subspace $\mathscr S_m$ whose outside values are unrestricted and whose
value $g_i$ is constant on graft level $i$. These are symmetries of a
finite operator used in a proof; no permutation of ordered sources is a
native action. Level $i$ has $2^i$ separate occurrences and the next-level
interface has $2^{i+1}$ separate unit edges. Accordingly write the actual
energy as $E_{\rm out}+E_{\rm rad}$, where $E_{\rm out}$ includes the
parent-to-graft-root attachment edge and

$$
E_{\rm rad}=\sum_{j=0}^{m-1}2^{j+1}|g_j-g_{j+1}|^2.
$$

Set $a_j=2^{(j+1)/2}(g_j-g_{j+1})$ and extend this finite sequence by
zero. Telescoping gives

$$
2^{i/2}(g_i-g_m)=
\sum_{r\ge0}2^{-(r+1)/2}a_{i+r},\qquad 0\le i\le m.
$$

Each shift is an $\ell^2$ contraction. The triangle inequality and
$\sum_{r\ge0}2^{-(r+1)/2}=1+\sqrt2$ therefore give

$$
\sum_{i=0}^m2^i|g_i-g_m|^2
\le(3+2\sqrt2)E_{\rm rad}<6E_{\rm rad}
\quad\text{if }E_{\rm rad}>0.
\tag{118.6}
$$

The non-strict bound with constant six also holds when the energy is zero,
including $m=0$. Weighted Cauchy--Schwarz gives
$|g_0-g_m|^2\le(\sum_{j=0}^{m-1}2^{-(j+1)})E_{\rm rad}\le E_{\rm rad}$.
The unique context path from $p\in O$ to $x$ uses only $E_{\rm out}$
edges. Path Cauchy--Schwarz followed by
$|g(p)-g_m|^2\le2|g(p)-g_0|^2+2|g_0-g_m|^2$ yields

$$
\sum_{p\in O}|g(p)-g_m|^2
\le2D_C E_{\rm out}+2kE_{\rm rad}.
$$

The counting mean $\bar g$ minimizes squared deviation from constants.
Combining these inequalities proves, for every $g\in\mathscr S_m$,

$$
\sum_{p\in V_{v_m^\sigma}}|g(p)-\bar g|^2
\le K_C\langle g,L_{v_m^\sigma}g\rangle.
\tag{118.7}
$$

The restriction of this finite real symmetric nonnegative operator to
$\mathscr S_m$ is self-adjoint, contains constants, and has no further
zero mode because the original graph is connected. Its nonconstant
eigenvalues are consequently at least $1/K_C$. Finite spectral calculus
gives

$$
\|e^{-tN_mL}f-\bar f\mathbf1\|_2
\le e^{-tN_m/K_C}\|f-\bar f\mathbf1\|_2
\le\sqrt{N_m}\,e^{-tN_m/K_C}.
$$

Here $L=L_{v_m^\sigma}$, $f=f_{v_m^\sigma}$, and all norms count
every occurrence. Root evaluation has counting norm one. The retained
constant contribution is exactly

$$
\bar f=\frac{b+\sigma2^m}{N_m},\qquad
\left|\bar f-\frac{\sigma}{2}\right|
=\frac{|b-\sigma(k-1)/2|}{N_m}\le\frac{c_C}{N_m}.
$$

This proves (118.5). It is an invariant-subspace use of the mature
variational and reversible heat-decay method of Levin--Peres,
[*Markov Chains and Mixing Times*, second edition, Lemma 13.7,
Remark 13.8 and Lemma 20.5](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf),
with the displayed actual counting weights and edge multiplicities.
For rational $t$ and any rational $\delta>0$, a wholly finite sufficient
error condition is
$N_m>(2K_C^2/t^2+c_C)/\delta$: the elementary bound
$e^s\ge s^2/2$ gives
$\sqrt{N_m}e^{-tN_m/K_C}\le2K_C^2/(t^2N_m)$.
Thus choosing a witness requires no infinite source.

The sector qualification is essential. For $m\ge1$, take a vector equal
to $+1$ on one child subtree of the graft root, $-1$ on the other, and
zero at that root and outside. It has counting mean zero, energy two
and squared norm $2(2^m-1)$. Its Rayleigh quotient is
$1/(2^m-1)$, bounding the full-tree gap above and tending to zero.
This vector is outside $\mathscr S_m$. No depth-uniform full-tree gap,
uniformity over changing contexts, or shrinking-$t$ limit is asserted.
$\square$

### 118.3 The same terminal history and the same entire unequal row

**Theorem 118.3 (unread-cone certificate radius).** Fix any common rational
$t>0$, controller $A$ and guard $G$ of Definition 118.1. On any actual
finite terminal run on $u\in D$ with unequal root children, if an INITIAL
leaf cone is unread, then

$$
\operatorname{rad}_t(H,\mathsf{Row}(u))\ge\frac12.
\tag{118.8}
$$

This includes every literal address, arbitrary finite serial Apply
histories and every common history-only guard of IV Contract 112.1a.

Proof. Let $x$ be unread and write $u=C[a]$ as above. For any finite
filling $w$ and every accepted epoch $e\ge0$, substitution preserves
the context brackets and acts independently below its original leaf
prefixes. Thus $\rho^e(C[w])$ has the same outside branches and the
same independently substituted outside leaf blocks. At a requested
address $p$ not prefixed by $x$, its actual four-valued reply is independent
of $w$. This includes paths ending above $x$, paths in another leaf
block, repeated calls and paths reporting absent. It extends precisely
the substitution locality of IV Lemma 112.7 from a label flip to a
whole filling in that one cone.

Induct through every actual prefix of the finite run on $u$. The same
complete entry and equal local state choose the same next effective
computation and action. All its Reads lie outside the cone of $x$, so
at the same accepted epoch they give the same actual replies on $C[w]$.
Each Apply attempt has identical $(\gamma,e,H_{\rm prefix})$, hence
identical status under the fixed $G$. Both registers advance by exactly
one $\rho$ or neither advances. The same local state reaches the same
Stop with the same output and no executed suffix. There is no bound on
the number of these updates other than finiteness of this actual run.

Choose $w=B_m^+$ and $B_m^-$ from Theorem 118.2. For all sufficiently
large $m$, the root child containing $x$ has more occurrences than the
unchanged other root child. They are therefore unequal for both signs.
Both resulting finite sources retain exactly the entire row of $u$:
reached list $(L,R)$, numbered exterior
$\langle\square_1,\square_2\rangle$, and the two singleton partition
classes. The count comparison proves a property of competitors; it is
never input advice. Both graft sequences are members of
$\mathcal C_{A,G,H}(\mathsf{Row}(u))$ and, by (118.5), their responses
tend to $+1/2$ and $-1/2$. For every real $z$ it follows that

$$
\sup_{v\in\mathcal C_{A,G,H}(\mathsf{Row}(u))}|z-R_v(t)|
\ge\max(|z-1/2|,|z+1/2|)\ge1/2.
$$

Taking the infimum proves (118.8). This is the ordinary two-compatible-input
half-diameter argument, without assuming an attained supremum or an
infinite admissible source. More explicitly, for each fixed
$0<\epsilon<1/2$ choose a finite common $m$ meeting the row condition
and making (118.5) smaller than $1/2-\epsilon$. The two finite signed
targets differ by more than $2\epsilon$, although their terminal history,
entire INITIAL row and output agree. Grafting is a construction of
alternative INITIAL sources in $D$, not an operation executed on $u$;
$m$ is not its accepted epoch. $\square$

### 118.4 Simultaneous acquisition necessity and the reused finite consumer

**Corollary 118.4 (all-source combined leaf coverage and paid coordinates).**
For every fixed common rational $t>0$, rational $0<\epsilon<1/2$,
and every guard $G$ of IV Contract 112.1a, every deterministic effective
controller terminating correctly on all of $D$ for (118.1)--(118.2)
at the same Stop covers every INITIAL leaf on each actual terminal run.
Writing $l(u)$ for the INITIAL leaf count and
$d_{\rm leaf}(u)=\sum_{x\text{ INITIAL leaf}}|x|$, that one run satisfies
simultaneously

$$
q_A(u)\ge l(u),\qquad \ell_A(u)\ge d_{\rm leaf}(u).
\tag{118.9}
$$

Here $q_A$ counts all post-entry raw Reads, repeated and absent included,
and $\ell_A$ sums their literal word lengths. The genuine pre-entry
root contributes one additional raw Read and zero literal length.

For the unequal sources $u_h=\langle\alpha,B_h^+\rangle$, $h\ge1$,
an all-domain row-only controller can return the entire row after two
post-entry epoch-zero child Reads, with literal length two. Every correct
combined controller instead has, on these same inputs,

$$
q_A(u_h)\ge1+2^h,\qquad
\ell_A(u_h)\ge1+(h+1)2^h.
\tag{118.10}
$$

There is a sourcewise finite sufficient combined controller using the
existing epoch-zero acquisition and description consumer once, with
post-entry $(q,\text{Apply attempts},\ell)=(N_u-1,0,\Lambda_u)$ when
the authentic retained root report supplies the first traversal event,
where $\Lambda_u=\sum_{p\in V_u}|p|$. Its total raw Reads and cumulative
same-immutable-source distinct addresses are both $N_u$. These native
Read and literal-length upper coordinates are within factor two of
(118.9). No matching price is claimed for other resources.

Proof. On an unequal-row input, an unread cone contradicts Theorem 118.3
and correctness on its two finite competitors. On an equal-row input
$u=\langle s,s\rangle$, reuse the one-leaf flip and actual-prefix replay
in the proof of IV Theorem 112.8, with IV Lemma 112.7. Flipping one
unread leaf label changes exactly one ordered child subtree, hence changes
the INITIAL partition while preserving the terminal history. This
argument applies to any finite $s$; the printed numerical statement of
IV Theorem 112.8 is on its equal perfect family $U_h$. The equal-row
case needs no additional heat argument.

INITIAL leaves are prefix-free, so a literal Read belongs to at most
one leaf cone, even after arbitrary serial updates. Select one covering
call for each leaf on this same actual run. They are distinct calls and
each pays length at least $|x|$, proving both (118.9) coordinates together.
Apply attempts, status observations and local work are separate from
Reads; no update combines two INITIAL cones into one Read.

On $u_h$, epoch-zero Read$(L)$ and Read$(R)$ report alpha and branch.
That mismatch certifies unequal entire subtrees, hence every field of
(118.2). A common row-only policy uses this test and the existing genuine
traversal as fallback when the two replies do not already decide equality
or inequality. It is correct on all branch sources without a family
selector. There are $1+2^h$ INITIAL leaves, with depth sum
$1+(h+1)2^h$, giving (118.10) for the combined task. Common choices such
as $t=1,\epsilon=1/4$ work across every $h$ and every lawful guard.

For sufficiency reuse [IV Definition 112.9 and Theorem
112.10](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md)
and Definition 115.7 above,
specifically [ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean)'s
four-valued immutable readout, reply-driven frontier and report-only
restoration. With the authentic retained root branch event as the
already executed first event of that traversal, its pending frontier is
$L,R$. Continue its genuine epoch-zero suffix without Apply, restore
INITIAL from acquired reports, and compare its two ordered children.
Its Boolean third-substitution-image Strategy and distinct-address
tariff retain their original task and scope; this is a separate consumer
of the acquisition phase. The zero-Apply sufficient policy is legal for
every guard and places no restriction on lower-bound competitors.
The owner's unchanged empty-phase root-first schedule is also sufficient;
it actually repeats the root and has $N_u$ post-entry Reads and $N_u+1$
total raw Reads, with cumulative distinct addresses $N_u$. Root reuse
is neither a refund nor a claim that this latter schedule skipped a call.
Old-version reports are not caches for later substituted versions.

The binary-tree identities

$$
N_u=2l(u)-1,\qquad
\Lambda_u=2d_{\rm leaf}(u)-2l(u)+2
\tag{118.11}
$$

follow by structural recursion, counting the added prefix on every child
occurrence or leaf. Thus $N_u-1<2l(u)$ and
$\Lambda_u\le2d_{\rm leaf}(u)$ on $D$. These are coordinates of one
combined acquisition, with no additive second heat traversal.

The restored INITIAL description supplies $N_u,L_u,f_u$ to the paid
finite-matrix consumer of Definition 115.7. For completeness of its
finite error certificate, use the mature Poisson matrix expansion of
[Levin--Peres, §20.1, equations (20.3)--(20.8)](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf).
The actual maximum degree is three, so $P=I-L_u/3$ is nonnegative
row-stochastic and $\|P^jf_u\|_\infty\le1$. With $\theta=3tN_u$,

$$
R_u(t)=e^{-\theta}\sum_{j\ge0}\frac{\theta^j}{j!}
                 (P^jf_u)(\varepsilon).
$$

After acquisition choose finite $J$ with
$\theta/(J+2)\le1/2$ and $2\theta^{J+1}/(J+1)!\le\epsilon/2$.
Let $C_J=\sum_{j=0}^J\theta^j/j!$ and
$y_J=\sum_{j=0}^J(\theta^j/j!)(P^jf_u)(\varepsilon)$.
Successive tail ratios are at most $1/2$, so the omitted contribution
has absolute value at most $\epsilon/2$, using $e^{-\theta}\le1$.
Choose finite $M$ with $\theta/(M+2)\le1/2$ and
$r_M=2\theta^{M+1}/(M+1)!\le\epsilon/(2C_J)$, and put
$T_M=\sum_{j=0}^M\theta^j/j!$. Positive Taylor sums and the same
geometric remainder give the rational enclosure

$$
\frac1{T_M+r_M}\le e^{-\theta}\le\frac1{T_M},\qquad
\frac1{T_M}-\frac1{T_M+r_M}\le r_M.
$$

Since $|y_J|\le C_J$, the rational output $z=y_J/T_M$ has
$|z-R_u(t)|\le\epsilon$. Both searches have rational stopping tests
and terminate because the factorial tails tend to zero for fixed
acquired $\theta$. This is deterministic arithmetic, with no sampling
operation. Compute the full row and this output before the one Stop.
The completed authentic epoch-zero traversal fixes the finite ordered
INITIAL source uniquely on its actual history fibre; its finite reports
and the rational inequalities therefore supply a finite semantic
certificate. Coverage alone, especially by absent or later-epoch Reads,
is only a necessary condition and supplies no such reconstruction.

Sparse matrix-vector evaluation and enclosure construction take
$O(N_u(J+1)+M+1)$ exact rational arithmetic operations after restoration.
This count is not bit work: each numerator, denominator, intermediate,
precision search and output encoding has its actual finite bit cost.
Source acquisition, literal-address generation, report restoration,
ordered comparison, control, retained syntax/history, numerical vectors,
scratch storage and output storage remain paid separate coordinates.
$J,M$ and these widths can grow with the acquired source and required
precision; they are not initial advice. This establishes sourcewise
finite sufficiency, not an optimal work/storage bound, implementation
tariff or physical duration. $\square$

### 118.5 Mathematical scope and supplier correspondence

**Mathematical citation 118.5 (the uncovered relation and its boundaries).**
The repo-derived addition is (118.5) in a fixed original context and
its same-entire-unequal-row history consequence (118.8), giving (118.9)
on every branch source for the combined service. IV Theorem 112.8 owns
the equality-input bill; IV Theorem 112.10 and V Definition 115.7 own
genuine acquisition/restoration and acquired-description evaluation.
Those supplies establish sufficiency after acquisition, while the
unequal two-Read family in (118.10) distinguishes this additional
fixed-accuracy necessity. Path and weighted Cauchy--Schwarz, finite
spectral calculus, compatible-input diameter and Poisson evaluation
are mature intermediate methods, not additional discoveries. No
exhaustive literature-absence or worldwide-priority claim is made.

The hypotheses and source correspondence come from [Native Leaf Depth
Contact, Definition 1.1, Assumption 1.2 and Definition 1.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md),
[Acquired Relation History, Definition 1.1 and Assumption 1.3](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md),
and IV Contract 112.1a. This is a deterministic worst-case certificate
statement over original sources, not an average-error statement for a
supplied probability law. No finite-certificate impossibility on all
histories follows: the paid full traversal supplies one sourcewise.
At $t=0$ every branch-root signed response is zero, and the graft
argument gives no heat acquisition obstruction. The argument makes
no conclusion for $\epsilon\ge1/2$ and proves no globally sharp threshold.

[Pyramid Correlation and Native Continuation, Definition 24.4 and
Theorem 24.5](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)
presuppose a known finite classical law, fixed cut, distinct nonempty
future characters and nonzero coefficients. Their $d$-bit branch record
excludes composition baseline and total machine state. It neither
acquires arbitrary unknown trees nor transfers a storage bound to this
task. [Predictive Quotient, Definition 8.1 and Theorems 8.2--8.3](FIB_LEGAL_EDGE_LOAD_PREDICTIVE_QUOTIENT_UNIFILAR_ERASURE_TAIL_AND_STRICT_SCOPE.md)
fix one twelve-state stochastic law and the target $Q_0$;
[Intrinsic Null Kernel, Definition 1.2 and Theorem 2.2](FIB_LEGAL_EDGE_LOAD_INTRINSIC_NULL_KERNEL_DUAL_RESIDUAL_AND_PRESENTATION_OBSTRUCTION.md)
presuppose a specified finite producer for the collar test. Neither
supplies a tree archive, original-source law, permission or free native
certificate, and neither is a premise of the graft proof.

The normalized real $t$, actual accepted source epoch, native chronology
and physical duration remain different types, as in §117.5. Constructor
Read does not prepare the signed field, actuate closed heat, measure a
real amplitude or authorize transport. Root/epoch authentication, access
isolation, field preparation, actuation/readout, physical clock or metric,
spatial dimension and stable matter require their own realization bridges.
The ordinary mathematical proofs assert no Lean/kernel verification or
physical realization. The analytical transport scope of Theorem 117.5
and its point-functional limitation are unchanged; (118.8) is an
acquisition obstruction, not that theorem's uniform point-readout upgrade.
These results leave the complete source-to-spatial-propagation programme
and its physical obligations unresolved.

## 117.99 追加锚（本行以下为增补区）

## 119. A grouped cube form on one actual whole-rho source

### 119.1 The ordered seed and its declared amplitude constraint

**Definition 119.1 (the thirteen-occurrence cube map).** Use the original
ordered source algebra and whole substitution of IV Definition 112.1:

$$
\begin{aligned}
u&=\langle\alpha,\langle\beta,\langle\alpha,\langle\beta,
       \langle\alpha,\langle\beta,\alpha\rangle\rangle\rangle\rangle\rangle\rangle,\\
\rho\alpha&=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\end{aligned}
\tag{119.1}
$$

Write actual addresses with $0$ left and $1$ right, so that $\varepsilon$
is the empty word. Label the cube vertices $(x,y,z)\in\{0,1\}^3$ by
$4x+2y+z$. The entire map $q_0:V_u\to\{0,\ldots,7\}$ is the table

| Actual address | Constructor in $u$ | $q_0$ |
| --- | --- | --- |
| $\varepsilon$ | branch | 0 |
| $0$ | $\alpha$ | 1 |
| $1$ | branch | 2 |
| $10$ | $\beta$ | 6 |
| $11$ | branch | 3 |
| $110$ | $\alpha$ | 1 |
| $111$ | branch | 7 |
| $1110$ | $\beta$ | 6 |
| $1111$ | branch | 5 |
| $11110$ | $\alpha$ | 1 |
| $11111$ | branch | 4 |
| $111110$ | $\beta$ | 0 |
| $111111$ | $\alpha$ | 6 |

For each finite $n\ge0$ put $V_n=V_{\rho^nu}$. The map $q_n$ fixes
the table values at original internal addresses and takes the constant
value $q_0(p)$ on the entire substituted subtree rooted at each
original leaf $p$. These pieces partition $V_n$. Define

$$
(U_nf)(p)=f(q_n(p)),\qquad
\mathcal C_n=\operatorname{ran}U_n\subset\ell^2(V_n),\qquad
K=L_{Q_3}.
\tag{119.2}
$$

Thus $U_n$ is the indicator pullback, with one column per cube vertex;
$K$ has diagonal $3$ and off-diagonal $-1$ precisely for labels whose
binary triples differ in one bit. Every actual occurrence has counting
mass one. Let $L_{\mathrm{closed},n}$ be the closed unit parent-child
Laplacian on $V_n$. Separately, use exactly the missing-child convention
of [Continuation Definition 55.2, (55.4)](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md):

$$
L_{\mathrm{kill},n}
 =L_{\mathrm{closed},n}
    +2\operatorname{diag}(\mathbf1_{\operatorname{Leaf}(\rho^nu)}).
\tag{119.3}
$$

The equations $g\in\mathcal C_n$ are added equalities of amplitudes.
They identify neither source occurrences nor native rooted fringes.
They add no seam to the source or native operation to IV Contract 112.1a.
All-$n$ statements below concern these finite mathematical domains, or
those finite prefixes actually accepted by a specified history. A fixed
guard or cap is unchanged; refusal changes no domain, and Stop has no
successor. No event after an infinite prefix is defined. Limits refer to
the mathematical family, without assuming one execution reaches it all.

### 119.2 Exact closed form, counting mass and inherited killing

**Proposition 119.2 (the cube application at every finite stage).** Put
$F=F_{n+1}$ and $G=F_{n+2}$, with $F_0=0,F_1=1$. Then

$$
\begin{aligned}
U_n^{\mathsf T}L_{\mathrm{closed},n}U_n&=K,\\
M_n:=U_n^{\mathsf T}U_n
 &=\operatorname{diag}(2G,6F-3,1,1,1,1,4G+2F-3,1),\\
N_n:=|V_n|&=8F+6G-1,\\
D_n&=\operatorname{diag}(2G,6F,0,0,0,0,4G+2F,0),\\
U_n^{\mathsf T}L_{\mathrm{kill},n}U_n&=K+D_n.
\end{aligned}
\tag{119.4}
$$

In particular $N_0=13$ and, in label order $0,\ldots,7$,

$$
\operatorname{diag}M_0=(2,3,1,1,1,1,3,1),\qquad
\operatorname{diag}D_0=(2,6,0,0,0,0,6,0).
\tag{119.5}
$$

Proof. The twelve original parent-child edges have unordered label pairs

$$
01,\ 02,\ 26,\ 23,\ 13,\ 37,\ 67,\ 57,\ 15,\ 45,\ 04,\ 46.
\tag{119.6}
$$

Here, for example, $01$ denotes the pair of cube labels $\{0,1\}$,
not an occurrence address. These are exactly the twelve edges of $Q_3$,
each once, so $U_0^{\mathsf T}L_{\mathrm{closed},0}U_0=K$.
With the ancestry extension of Definition 117.1,
$U_n=E_{0,n}U_0$. Apply the full-horizon ancestry-form identity in
Lemma 117.2, (117.4): old edge differences persist and every born edge
has zero difference. Its energy identity and original-leaf block
decomposition hold also from epoch zero; the $n\ge2$ restriction there
belongs to its quantitative error bounds, none of which is used here.
Equivalently, this is the serial application of
[VI Theorem 115.2, (115.3)](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md).
This supplies the first identity in (119.4), including $n=0$.

For mass, directly reuse IV (108.9) and IV Theorem 113.2: an original
alpha leaf contributes its $T_n$ block, with $2F-1$ nodes and $F$
leaves; an original beta leaf contributes $T_{n+1}$, with $2G-1$ nodes
and $G$ leaves. Original internal nodes remain singleton ancestry fibres.
The table groups one original internal node and one beta block into
class 0, three alpha blocks into class 1, and two beta blocks and one
alpha block into class 6. Each other class contains exactly one original
internal node. This gives $M_n$. There are four original alpha leaves,
three original beta leaves and six internal nodes, giving $N_n$.

Every current leaf has precisely two missing children in (119.3).
Its label does not change this exterior contribution. The class leaf
counts are $G,3F,2G+F$ on classes $0,1,6$, respectively, and zero on
the others. Twice these counts is $D_n$. This proves the killed identity
without substituting a different boundary convention. Taking $F=G=1$
gives (119.5). $\square$

### 119.3 Constrained counting flow and the free-flow witness

**Proposition 119.3 (restriction of energy does not give free descent).**
The counting-metric gradient flow of the energy
$\tfrac12g^{\mathsf T}L_{\mathrm{closed},n}g$, constrained to
$g=U_nf$, is

$$
M_n\dot f=-Kf.
\tag{119.7}
$$

For the inherited killed energy it is instead
$M_n\dot f=-(K+D_n)f$. At every finite $n$, neither free closed heat
nor free killed heat preserves $\mathcal C_n$. The constraint has
algebraic rank $N_n-8$; this number is not a native action count or
physical maintenance price.

Proof. Testing the constrained velocity against $U_nh$ gives
$h^{\mathsf T}M_n\dot f=-h^{\mathsf T}Kf$ for every $h$; use (119.4)
for either boundary choice. In particular $M_n$ cannot be dropped when
the form is written in class-value coordinates. For an explicit failure
of free invariance, take $f=\mathbf1_{\{1\}}$ and $g=U_nf$. The two
actual addresses $\varepsilon$ and $111110$ both lie in class 0, but

$$
(L_{\mathrm{closed},n}g)(\varepsilon)=-1,\qquad
(L_{\mathrm{closed},n}g)(111110)=0.
\tag{119.8}
$$

The root's children have values $1,0$. The beta-block root $111110$
has value zero, its parent is in class 4, and any born children remain
in class 0; every incident difference there is zero. Both tested
amplitudes are zero, so the diagonal killing term also vanishes at
these addresses. This proves the same witness for $L_{\mathrm{kill},n}$.
Differentiating free heat at time zero therefore takes $g$ out of
$\mathcal C_n$. This is the invariant-range distinction already present
in VI Theorems 115.2 and 116.2, now witnessed inside these cube fibres.

For precision about equality maintenance, the orthogonal projection is
$P_n=U_nM_n^{-1}U_n^{\mathsf T}$. Writing $L$ for either stage operator,
the constrained ambient equation is

$$
\dot g=-Lg+R_n,\qquad R_n=(I-P_n)LU_nf,\qquad g=U_nf.
\tag{119.9}
$$

This defines a mathematical reaction; the native menu supplies neither
its actuation permission nor its physical price. Choose one actual
representative of each nonempty fibre. The equations equating each
other amplitude to its representative are independent, numbering
$N_n-8$. Independence is linear algebra and assigns no resource tariff.

The use of the induced norm is the ordinary quadratic-form restriction
principle. For comparison of graph conventions, [Chung, *Spectral Graph
Theory*, Chapter 1, §§1.2 and 1.4](https://fanchung.ucsd.edu/research/cb/ch1.pdf)
keeps the vertex weights in the normalized Rayleigh quotient. Here the
weights are the actual fibre counts $M_n$, rather than cube degrees.
No normalized graph formula replaces these counts. $\square$

### 119.4 Fixed class observables, probability mass and scalar clocks

**Proposition 119.4 (no uniform scalar cube clock in class values).**
Let $A_n=M_n^{-1}K$ on the fixed coordinates
$(f_0,\ldots,f_7)$. There are no positive scalars $c_n$ and $k>0$ with

$$
c_nA_n\longrightarrow kK.
\tag{119.10}
$$

There are likewise no such scalars with the full heat-matrix limit
$e^{-tc_nA_n}\to e^{-tkK}$ on these same eight class-value coordinates
for every fixed $t>0$. In these statements matrix convergence can be
taken in any finite-dimensional operator norm. The normalized mass is

$$
\overline M_n:=\frac{M_n}{N_n}
\longrightarrow
\frac{\operatorname{diag}(\varphi,3,0,0,0,0,1+2\varphi,0)}
     {4+3\varphi},\qquad \varphi=\frac{1+\sqrt5}{2}.
\tag{119.11}
$$

Proof. Class 2 has mass one. Its diagonal in (119.10) would give
$3c_n\to3k$, hence $c_n\to k$. Class 0 has mass $2G\to\infty$,
so its corresponding diagonal tends to zero, contradicting $3k>0$.

For the heat statement, the unique stationary row probability of
$e^{-tA_n}$ is $\pi_n^{\mathsf T}$, where
$\pi_n=N_n^{-1}M_n\mathbf1$. Indeed
$\pi_n^{\mathsf T}A_n=N_n^{-1}\mathbf1^{\mathsf T}K=0$,
and the cube is connected. A positive scalar clock does not change it.
The Fibonacci ratio $G/F\to\varphi$ gives (119.11) and the limiting
probability $\pi_*$. Passing to a proposed heat-matrix limit gives
$\pi_*^{\mathsf T}e^{-tkK}=\pi_*^{\mathsf T}$. For any $t>0$,
the eigenvalues of $e^{-tkK}$ equal one only on $\ker K$, the constants.
Its only stationary probability is therefore uniform. But $\pi_*$
vanishes on five classes, a contradiction. This argument excludes
the full eight-observable heat limit without deducing generator
convergence from semigroup convergence.

Normalization must keep the form and metric paired. If only the metric
is changed to $\overline M_n$ while the form stays $K$, its positive
generator becomes $N_nA_n$; arbitrary scalar clocks still fall under
the same obstruction by absorbing $N_n$ into $c_n$. If both the
counting form and counting inner product are divided by $N_n$, the
generator remains $A_n$. The closed form (119.4) itself is unchanged
only in the first convention. A singular limiting probability metric
does not justify replacing the finite counting dynamics by $K$.
$\square$

### 119.5 Counting isometries and the actual infinite pullback

**Proposition 119.5 (two matrix limits and their vector boundary).**
Put $H=\{0,1,6\}$, $S=\{2,3,4,5,7\}$, and
$W_n=U_nM_n^{-1/2}$. These are counting isometries from Euclidean
$\mathbb R^8$ into $\ell^2(V_n)$. In the ordering $H\sqcup S$,

$$
\begin{aligned}
B_n:=W_n^{\mathsf T}L_{\mathrm{closed},n}W_n
 &=M_n^{-1/2}KM_n^{-1/2}
   \longrightarrow 0_H\oplus K_{SS},\\
B_n^{\mathrm k}:=W_n^{\mathsf T}L_{\mathrm{kill},n}W_n
 &=M_n^{-1/2}(K+D_n)M_n^{-1/2}
   \longrightarrow I_H\oplus K_{SS}.
\end{aligned}
\tag{119.12}
$$

The edges induced on $S$ form the path $2-3-7-5-4$. Here $K_{SS}$
is the principal cube submatrix: in that path order it has diagonal
$3$ throughout and $-1$ on successive neighbours. It retains grounding
to $H$ and is not the closed path Laplacian.

The consistent maps $q_n$ define $q_\infty$ on
$\bigcup_nV_n=\{0,1\}^*$. Its literal counting pullback
$U_\infty f=f\circ q_\infty$ belongs to $\ell^2$ exactly when
$f|_H=0$. With all finite-stage vectors zero extended to this common
address space, $U_nf$ has a strong $\ell^2$ limit exactly under that
condition. For fixed $x\in\mathbb R^8$, $W_nx$ converges weakly to
the vector supported at the five original $S$ addresses with values
$x|_S$, and converges strongly exactly when $x|_H=0$.

Proof. By (119.4), masses on $H$ tend to infinity and masses on $S$
are exactly one. Every entry of $B_n$ touching $H$ tends to zero;
the $S$ block remains $K_{SS}$. Moreover

$$
\frac{(D_n)_{00}}{(M_n)_{00}}=1,\qquad
\frac{(D_n)_{11}}{(M_n)_{11}}=\frac{6F}{6F-3}\to1,\qquad
\frac{(D_n)_{66}}{(M_n)_{66}}
 =\frac{4G+2F}{4G+2F-3}\to1.
\tag{119.13}
$$

The other killing ratios are zero. This proves (119.12). Inspection
of (119.6) gives the asserted path. Equivalently $K_{SS}$ is its
closed path Laplacian plus the diagonal $(2,1,1,1,2)$ in path order.
Finite-dimensional continuity also gives the corresponding heat-matrix
limits $e^{-tB_n}$ and $e^{-tB_n^{\mathrm k}}$ for each fixed $t\ge0$.
These use isometric coordinates $x=M_n^{1/2}f$, which vary with $n$;
they are different coordinates from Proposition 119.4's fixed class values.

The domain union is the address exhaustion of Continuation (55.2),
applied to this seed. Each $H$ fibre has infinitely many occurrences,
whereas each $S$ fibre is a single original internal address. A nonzero
constant amplitude on any $H$ fibre has infinite counting norm. This
proves the exact domain of $U_\infty$. If $f|_H=0$, the zero-extended
$U_nf$ are already the same finitely supported vector for every $n$;
otherwise their squared norms $f^{\mathsf T}M_nf$ diverge.

Each $H$ column of $W_n$ has norm one but tends pointwise to zero,
since its value is the reciprocal square root of its growing fibre
size. Boundedness and density of finitely supported test vectors give
weak convergence to zero. The $S$ columns are fixed point masses.
Thus the weak limit of $W_nx$ has squared norm $\|x|_S\|^2$, while
$\|W_nx\|^2=\|x\|^2$. A strong limit exists exactly when $x|_H=0$.
Consequently the zero block in (119.12) does not exhibit nonzero
strong limiting counting-$\ell^2$ vectors on $H$. On the actual domain
$f|_H=0$, the infinite edge form is exactly
$f_S^{\mathsf T}K_{SS}f_S$, since its support and every incident edge
are already in the original tree. $\square$

### 119.6 Field descent and what selects the cube

**Proposition 119.6 (common field failure and a different persistent form).**
The common source field of Continuation Theorem 55.3 does not factor
through $q_n$ at any stage, nor through $q_\infty$. Compressing an
external force yields a class covector, without supplying field or
source intertwining. Furthermore the same $u,\rho$ admit the exact
persistent thirteen-class original-occurrence form
$L_{\mathrm{closed},0}$, as well as the declared eight-class cube form.
Thus whole-rho energy persistence alone does not select this cube.

Proof. The common field is $\phi(p)=2^{-|p|}$. The two addresses of
(119.8) have the same class but

$$
\phi(\varepsilon)=1,\qquad \phi(111110)=1/64.
\tag{119.14}
$$

This violates fibre constancy. It is exactly the obstruction described
by the existing
[answerability criterion](../../../D5/S0/Rewriting/Quotients/AnswerabilityCriterion.lean);
the adjacent
[dynamics descent criterion](../../../D5/S0/Rewriting/Quotients/DynamicsDescent.lean)
concerns a self-map preserving quotient fibres. For heat on amplitudes,
the explicit invariant-range failure is (119.8), not an identification
of that discrete self-map theorem with a new operator theorem.

For any ambient force $b_n$, testing the constrained equation supplies
the covector $U_n^{\mathsf T}b_n$ and hence the class velocity contribution
$M_n^{-1}U_n^{\mathsf T}b_n$. For example
$U_n^{\mathsf T}\mathbf1_{\{\varepsilon\}}=\mathbf1_{\{0\}}$.
This equality does not say $\phi|_{V_n}=U_n\psi$ or
$L_{\mathrm{closed},n}U_n=U_nA_n$. The field in (119.14) is the
common infinite field restricted to $V_n$, not a newly solved killed
field. In fact (55.3)--(55.4) give the more precise boundary relation

$$
L_{\mathrm{kill},n}(\phi|_{V_n})
 =\mathbf1_{\{\varepsilon\}}
   +\mathbf1_{\operatorname{Leaf}(\rho^nu)}\,\phi|_{V_n},
\tag{119.15}
$$

because the two exterior child values at a leaf sum to its own field
value. Even the forcing in a finite killed equation therefore retains
its stated boundary convention.

For the alternative, give each of the thirteen original occurrences
its own class and copy each original leaf value over its substituted
block. Its indicator pullback is $\widetilde U_n=E_{0,n}$, and the
same supplied ancestry identity gives

$$
\widetilde U_n^{\mathsf T}L_{\mathrm{closed},n}\widetilde U_n
 =L_{\mathrm{closed},0},\qquad U_n=\widetilde U_nU_0.
\tag{119.16}
$$

This is the thirteen-vertex seed-tree form, of rank twelve, whereas
$K$ is an eight-vertex cube form of rank seven. Both persist under
the very same source substitution. The additional grouping $q_0$
supplies the cube. In particular it groups the root with a beta leaf,
and its class 6 groups beta and alpha leaves. These are not equal
rooted fringes under
[ExactSharing's definition of complete labelled ordered subtrees](../../../D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.lean).
The literal constructors, substitution and address meanings remain
those of
[GenealogicalFiberTransport.Source and substitution](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean)
and
[ActualTreeReadoutAcquisition.readout and nodes](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean).

The source-specific deductions (119.4), (119.8), (119.11)--(119.16)
are repo-derived applications of the cited suppliers, without a
worldwide-priority or exhaustive-literature claim. Form restriction
is also distinct from static elimination: the latter replaces an
interior block by its Schur complement, as in
[Dörfler--Bullo, arXiv:1102.2950v1, §2.1](https://arxiv.org/pdf/1102.2950v1)
and the [existing Kron-reduction note](../../../Library/GraphInvariants/dorflerbullo2013kron.md).
Here no interior amplitude is minimized out; the domain is constrained
and its counting metric is retained. The non-singleton fibres in the table are
disconnected, so no connected-fibre coarsening hypothesis is asserted.
These conclusions limit dimension inference from this energy identity.
They neither establish physical spatial dimension three nor rule out
other source-to-space bridges with their own additional relations.
$\square$

## 119.99 追加锚（本行以下为增补区）

## 120. Unit-clock cube approximation and native cyclic heat factors

### 120.1 Actual occurrences, boundaries and the comparison norm

**Definition 120.1 (the source and kinetic comparison contract).** Use the
nonempty finite ordered source algebra of IV Definition 112.1 and the
all-original convention of Definition 115.1:

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle s,v\rangle=\langle\rho s,\rho v\rangle.
\tag{120.1}
$$

For $s\in\mathcal T$, let $V=\operatorname{Pos}(s)$ contain all literal
occurrence addresses, including the root $o=\varepsilon$. Distinct
addresses remain distinct even when their complete ordered subtrees are
equal. The edges are exactly the existing parent--child seams. Thus $V$
is a nonempty finite full binary tree, with $N=|V|$. In the source
[GenealogicalFiberTransport.Source and substitution](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean),
$\mathcal T$ is `FreeMagma Bool`, with true for alpha and false for beta;
in [ActualTreeReadoutAcquisition.readout and nodes](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean),
false and true in an address mean left and right, respectively. Here they
are written $L,R$. These are two different uses of the Boolean alphabet.
The all-original domain includes alpha and beta singletons; it is larger
than the branch-root acquired fibre in IV (112.1).

Give each vertex counting mass one and each seam symmetric conductance
one. On functions on $V$, define

$$
\begin{aligned}
(L_Vh)(x)&=\sum_{y\sim_V x}(h(x)-h(y)),\\
L_V^{\mathrm k}&=L_V+
       2\operatorname{diag}(\mathbf1_{\operatorname{Leaf}(s)}),
& A_V&\in\{L_V,L_V^{\mathrm k}\},\\
\mu_V&=N^{-1}\sum_{x\in V}\delta_x,
& \|h\|_{\mu_V}^2&=N^{-1}\sum_{x\in V}|h(x)|^2.
\end{aligned}
\tag{120.2}
$$

The killed choice is exactly Continuation Definition 55.2, (55.4), and
(119.3): both missing children contribute at every current leaf. It is
the compression of the infinite kinetic Laplacian to zero exterior
values. Its diagonal is two at the root and three at every nonroot
vertex. There is no artificial parent seam at the root. A singleton has
$L_V=[0]$ and $L_V^{\mathrm k}=[2]$. For $N>1$, the closed degrees are
two at the root, three at nonroot internal vertices and one at leaves.

The infinite carrier and its kinetic law are those of
[Continuation Definitions 55.1--55.2](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md):

$$
\begin{aligned}
\mathcal P&=\{L,R\}^{*},&p&\sim pL,quad p\sim pR,\\
(L_\infty h)(p)&=\sum_{z\sim p}(h(p)-h(z)),\\
D_n(u)&=\operatorname{Pos}(\rho^nu),&
\{p:|p|\le\lfloor n/2\rfloor\}&\subseteq D_n(u),
\qquad \bigcup_{n\ge0}D_n(u)=\mathcal P.
\end{aligned}
\tag{120.3}
$$

The domains $D_n(u)$ are the actual, generally irregular domains of that
source; contained balls in (120.3) are only comparison subsets. Root
degree in $\mathcal P$ is two and all other degrees are three.

For the cube take $B=Q_3=\{0,1\}^3$ and $K=L_{Q_3}$, with one unit edge
when exactly one coordinate changes. For a fixed integer $m\ge3$ take
$B=C_m=\mathbb Z/m\mathbb Z$ and
$K_m f(b)=2f(b)-f(b+1)-f(b-1)$, the simple unit cycle Laplacian.
For either target, write $e_c=\mathbf1_{\{c\}}$. Every map
$\pi:V\to B$ defines the observable pullback $U_\pi f=f\circ\pi$ and
the discrepancy

$$
E_{\pi,c}^{A_V,K_B}(t)
 =e^{-tA_V}U_\pi e_c-U_\pi e^{-tK_B}e_c,
\qquad c\in B,\quad t\ge0.
\tag{120.4}
$$

All target indicators are tested, including those of unattained labels.
If $\pi$ is not onto, this pullback is still defined but is not injective;
the map is not called an onto quotient. No inverse fibre-mass matrix is
used, and error is measured over all actual source vertices, rather than
uniformly over attained classes.

The same $t$ in (120.4) is the unit counting heat clock. Using
$\|\cdot\|_{\mu_V}$ does not change $A_V$: its paired energy is the
counting energy divided by $N$, with the analogous division of the
killing energy. Pairing the unscaled edge energy with this probability
inner product instead gives $NL_V$, as in (116.1)--(116.2). That is a
different clock. The operators here are kinetic; $A_V$ does not denote
the potential-bearing $aL-gM_\phi$ of §55.

The source/history projection remains the one in IV Contract 112.1a and
Continuation Definition 55.1: immutable INITIAL, labels, brackets,
left/right order, distinct occurrences, actual versions, original Reads,
acquisition and copy permissions, chronological acceptances and refusals,
and absorbing Stop are retained. An uncapped native menu and a separately
declared guarded menu keep their respective scopes; a refusal changes no
source or epoch. Quantification over $n$ means the mathematical family
or separately legal finite prefixes, without raising a fixed guard or
resuming a stopped history. Neither a limit Read nor an event after an
infinite prefix is defined. Scalar observables, unit conductances and
this heat clock are added mathematical contracts. Their heat laws and
the address readout below grant no native preparation, equality
maintenance, reset, clone, seam alteration or resource tariff.

### 120.2 A uniform finite-time obstruction for every cube map

**Proposition 120.2 (all-map cube-indicator floor).** For every
$s\in\mathcal T$, every map $\pi:\operatorname{Pos}(s)\to Q_3$, either
choice $A_V$ in (120.2), and $0\le t\le2/15$, put
$g_3(t)=t-15t^2/2$. Then

$$
\max_{c\in Q_3}\|E_{\pi,c}^{A_V,K}(t)\|_{\mu_V}
 \ge g_3(t)\sqrt{\frac{N+2}{8N}}.
\tag{120.5}
$$

In particular, simultaneously for every such tree and map,

$$
\max_{c\in Q_3}
 \|e^{-A_V/15}U_\pi e_c-U_\pi e^{-K/15}e_c\|_{\mu_V}
 \ge\frac1{30}\sqrt{\frac{N+2}{8N}}
 \ge\frac1{60\sqrt2}.
\tag{120.6}
$$

This includes every actual $D_n(u)$ and every surjective eight-class
partition when one exists. No graph-homomorphism, connected-fibre or
exact-lumpability hypothesis is imposed.

Proof. The common degree bound gives the nonnegative substochastic
matrix $R_V=I-A_V/3$. It is stochastic for the closed choice. In the
killed case, send each missing row mass to an absorbing cemetery, with
every test function zero there. The standard uniformization identity,
already used in Continuation (55.9), becomes

$$
e^{-tA_V}
 =e^{-3t}\sum_{k=0}^\infty\frac{(3t)^k}{k!}R_V^k.
\tag{120.7}
$$

This is the mature Poisson construction of
[Rao--Teh, *Fast MCMC Sampling for Markov Jump Processes and Extensions*,
arXiv:1208.4818v3, §3.1 and Proposition 1](https://arxiv.org/pdf/1208.4818v3).
Their column-distribution convention is transposed to rows acting on
observables here: the rate matrix is $-A_V$, the dominating rate is
$\Omega=3$, and the discrete matrix is $I-A_V/3$. Cemetery augmentation
handles killing. Formula (120.7) also follows directly from the
convergent exponential series, since $A_V=3(I-R_V)$.

Fix $x\in V$, write $b=\pi(x)$, and let $c$ be a cube neighbour of $b$
that is absent among $\{\pi(y):y\sim_V x\}$. Such a pair $(x,c)$ will be
called a missing pair within this proof. Since $c\ne b$, both
$(U_\pi e_c)(x)$ and $(R_VU_\pi e_c)(x)$ are zero. All later iterates
of this indicator lie between zero and one. Consequently

$$
\begin{aligned}
0\le(e^{-tA_V}U_\pi e_c)(x)
 &\le\mathbb P\{Z\ge2\}
 \le\tfrac12\mathbb E[Z(Z-1)]
 =\tfrac92t^2,\qquad Z\sim\operatorname{Poisson}(3t).
\end{aligned}
\tag{120.8}
$$

In the unit cube chain, the event of exactly one jump, along the
specified edge $b\to c$, has probability $te^{-3t}$. Thus

$$
\begin{aligned}
(e^{-tK}e_c)(b)&\ge te^{-3t}\ge t-3t^2,\\
(U_\pi e^{-tK}e_c)(x)-(e^{-tA_V}U_\pi e_c)(x)
 &\ge t-\tfrac{15}{2}t^2=g_3(t).
\end{aligned}
\tag{120.9}
$$

The last quantity is nonnegative on the stated interval, so its square
is a lower bound for the squared discrepancy at every missing pair.
At $x$, at most $\deg_V(x)$ of the three distinct cube-neighbour labels
can be represented by actual neighbours. The number $M$ of missing
pairs therefore satisfies

$$
M\ge\sum_{x\in V}(3-\deg_V(x))
 =3N-2|E_V|=3N-2(N-1)=N+2.
\tag{120.10}
$$

All these are distinct vertex/test pairs, even when several use the
same target label. Hence

$$
\sum_{c\in Q_3}\|E_{\pi,c}^{A_V,K}(t)\|_{\mu_V}^2
 =\frac1N\sum_{x\in V}\sum_{c\in Q_3}|E_{\pi,c}^{A_V,K}(t)(x)|^2
 \ge\frac{N+2}{N}g_3(t)^2.
\tag{120.11}
$$

The largest of the eight squared norms is at least one eighth of their
sum. This proves (120.5); $g_3(1/15)=1/30$ gives (120.6).

The root is included in (120.10): for $N>1$ its degree is two, so it
contributes at least one missing pair. A singleton has degree zero and
exactly three missing cube-neighbour labels, agreeing with $N+2=3$.
For each of those labels its pullback is identically zero, under either
$[0]$ or $[2]$, and the target one-jump estimate still applies. No onto
map exists when $N<8$; the stronger arbitrary-map statement remains
nonvacuous there. In fact full-tree sizes are odd. Empty fibres never
invalidate a test in (120.4).

The finite set of eight indicators is fixed; a maximizing indicator may
depend on the source and map. Thus no sequence of these finite maps can
make all eight errors tend to zero at $t=1/15$ in this norm and clock.
The argument does not say that every individual observable fails.
It strengthens the chosen-map free-flow failure (119.8) by a whole-vertex
quantitative obstruction independent of the choice of map. The
constrained form and mass identities of §119 are not hypotheses here.
$\square$

### 120.3 A fixed incoming-increment colouring of the actual infinite carrier

**Definition 120.3 (cycle residue and increment memory).** Fix an integer
$m\ge3$. Define $q:\mathcal P\to C_m$ and an auxiliary integer-valued
state $\delta:\mathcal P\to\{-1,0,+1\}$ by
$q(o)=0$, $\delta(o)=0$, and the ordered recursion

$$
\begin{array}{c|cc}
\delta(p)&\delta(pL)&\delta(pR)\\ \hline
0&+1&-1\\
+1&0&+1\\
-1&-1&0
\end{array}
\qquad
q(p\sigma)=q(p)+\delta(p\sigma)\pmod m,
\quad \sigma\in\{L,R\}.
\tag{120.12}
$$

For a nonroot vertex, $\delta(p)$ records its incoming increment, with
the displayed root convention. It is distinct from the retained colour
residue $q(p)$. The recursion retains the pair $(q,\delta)$, with at most
$3m$ possible pairs, rather than computing the colour with only three
states. Both are fixed functions of the literal finite address,
independent of source leaf labels or substitution stage. This $q$ is a
different map from the seed-dependent cube maps of Definition 119.1.
Write $Uf=f\circ q$ on bounded complex observables.

**Proposition 120.4 (native bounded-observable cycle heat and path laws).**
For every fixed $m\ge3$, the map (120.12) is onto with all fibres infinite.
On the displayed supremum-norm spaces it satisfies

$$
\begin{aligned}
U&:\ell^\infty(C_m)\longrightarrow\ell^\infty(\mathcal P),
&\|Uf\|_\infty&=\|f\|_\infty,\\
L_\infty U&=UK_m,
&e^{-tL_\infty}U&=Ue^{-tK_m}\qquad(t\ge0).
\end{aligned}
\tag{120.13}
$$

For every initial probability law on $\mathcal P$, the image under $q$
of the unit-seam continuous-time source chain has exactly the unit
cycle path law, with rate one to each adjacent residue and initial law
the pushforward under $q$. The full-graph colouring is external
equitable, rather than a cover of the full loopless graph. Independently,
no map from this actual rooted $\mathcal P$ into $Q_3$ intertwines all
cube-indicator generators, or their heat laws for all $t\ge0$.

Proof. At the root the children have colours $b+1,b-1$, where $b=q(o)$,
and there is no parent. At a nonroot vertex of colour $b$, its parent
has colour $b-\delta(p)$. The three possibilities in (120.12) give

$$
\begin{array}{c|c|cc}
\delta(p)&q(\operatorname{par}(p))&q(pL)&q(pR)\\ \hline
0&b&b+1&b-1\\
+1&b-1&b&b+1\\
-1&b+1&b-1&b
\end{array}
\tag{120.14}
$$

The residues $b,b+1,b-1$ are distinct for $m\ge3$, including $m=3$.
Every actual vertex therefore has exactly one neighbour in each of
the two adjacent cycle fibres. Each nonroot has one further neighbour
in its own fibre, whereas the root has no such neighbour. In
$L_\infty Uf$ the internal-fibre seam contributes zero, and the two
external seams give

$$
(L_\infty Uf)(p)
 =(f(b)-f(b+1))+(f(b)-f(b-1))=(UK_mf)(p).
\tag{120.15}
$$

For $p_k=LR^{k-1}$, $k\ge1$, the recursion gives
$\delta(p_k)=+1$ and $q(p_k)=k\pmod m$. Each residue occurs infinitely
often along these distinct addresses. This proves surjectivity, the
infinite-fibre assertion and the supremum-norm isometry. On the spaces
in (120.13), $\|L_\infty\|\le6$ and $\|K_m\|\le4$. Iterating (120.15)
and using norm-convergent exponential series proves the heat identity
on every bounded observable, without a counting-$\ell^2$ assumption.

For the full path law set $R_\infty=I-L_\infty/3$. The root has a
virtual holding probability $1/3$; at nonroots each of the three actual
seams has probability $1/3$. In both cases the observed row is

$$
\sum_{q(z)=c}R_\infty(p,z)
 =\overline R(q(p),c),\qquad
\overline R=I-K_m/3,
\tag{120.16}
$$

with probabilities $1/3$ to $b+1$, $b-1$ and $b$. At a nonroot the last
probability is an actual same-fibre transition. Conditional on any
observed past, averaging (120.16) over the possible current source
representatives leaves this same row. Thus the observed discrete chain
is Markov with matrix $\overline R$ for every initial law, not merely
one special or stationary law. Use an independent rate-three Poisson
process for its event times. The source process so constructed has
generator $-L_\infty$ by (120.7)'s bounded-operator version, and its
observed process uses the same event times with matrix $\overline R$.
Its generator is $3(\overline R-I)=-K_m$. Ignoring repeated observed
states gives exactly the unit-cycle jump path. A finite number of
Poisson events on every bounded time interval proves nonexplosion.

Here (120.15) is the source-specific external equitable condition. Its
standard finite-graph formulation is $LH=HL_\pi$ in
[Schaub et al., *Graph partitions and cluster synchronization in networks
of oscillators*, arXiv:1608.04283, §II (1)--(6), Remark 1 and
§III.A (9)--(11)](https://arxiv.org/pdf/1608.04283): their indicator
matrix $H$ corresponds to $U$, and their quotient Laplacian to $K_m$.
The internal-cell cancellation is the same one as in (120.15). Their
finite inverse fibre-count formula is not used for the infinite fibres.
Likewise (120.16) is the observed-row criterion for strong lumpability,
as in [Wolfer--Watanabe, *Geometric Aspects of Data-Processing of Markov
Chains*, arXiv:2203.04575v3, §3.4, Theorem 3.1](https://arxiv.org/pdf/2203.04575v3),
which attributes that criterion to Kemeny--Snell. Their finite source
$Y$, target $X$, map $\kappa$ and kernel $P$ correspond here to
$\mathcal P,C_m,q,R_\infty$; the countable-source extension used here
is justified by the explicit conditional-row and bounded-rate argument
above, not by applying a finite-only assertion without proof. Existing
repository row-factorization suppliers are
[StochasticDescentLumpability.StronglyLumpable and ExactQuotientKernel](../../../D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.lean)
and [StrongLumpabilityDescent.strong_lumpability_descent_tfae](../../../D5/S3/Observer/ProbabilisticClosure/StrongLumpabilityDescent.lean).
The local calculation supplies their representative-independence
condition; it is not a new general lumpability theorem.

Some actual seams have both endpoints in the same fibre, so $q$ is not
a homomorphism of the full simple source graph into the loopless cycle,
and in particular is not a locally bijective cover of that full graph.
For comparison only, deleting the internal-fibre seams leaves exactly
two edges at every vertex, one to each adjacent colour. On each connected
component the restriction is locally bijective, and its nonempty image
is closed under both target neighbours, hence is all of $C_m$. This is
the standard cycle-cover picture; see
[Fiala, *Structure and Complexity of Locally Constrained Graph
Homomorphisms*, §3.1, Definition 3.12](https://kam.mff.cuni.cz/~fiala/papers/habl.pdf)
for the locally bijective universal-cover convention. This comparison
deletes no seam in the actual source or in $L_\infty$. Full adjacency
equitability also fails: the fibre of colour zero contains the root
with zero same-colour neighbours and $p_m$ with one.

Finally, let $\pi:\mathcal P\to Q_3$ be any map. Its root image $b$ has
three distinct target neighbours, and at most two can appear at the two
actual root neighbours. For an absent target-neighbour label $c$,

$$
(L_\infty U_\pi e_c)(o)=0,
\qquad (U_\pi K e_c)(o)=-1.
\tag{120.17}
$$

This excludes generator intertwining. Since both operators on bounded
observables are bounded, differentiating any proposed all-time heat
identity at zero would give that impossible generator identity. The
degree-two root is retained throughout; a different, degree-three root
from a cube universal cover cannot replace it. $\square$

### 120.4 Local convergence and a persistent whole-vertex cycle error

**Proposition 120.5 (actual-domain heat convergence with a Poisson tail).**
Fix $u\in\mathcal T$ and $m\ge3$, and use exactly $D_n(u)$ in (120.3).
Let $q_n=q|_{D_n(u)}$, $U_nf=f\circ q_n$, $N_n=|D_n(u)|$,
$\mu_n=\mu_{D_n(u)}$, and let $A_n$ be either boundary choice in
(120.2). If $R$ is a nonnegative integer and the infinite-graph ball
$B_R(x)$ is contained in $D_n(u)$, then for every bounded complex
$f:C_m\to\mathbb C$ and every $0\le T<\infty$,

$$
\sup_{0\le t\le T}
 \left|(e^{-tA_n}U_nf)(x)-(Ue^{-tK_m}f)(x)\right|
 \le 2\|f\|_\infty\,
       \mathbb P\{\operatorname{Poisson}(3T)>R\}.
\tag{120.18}
$$

In particular heat converges at every fixed address, uniformly on each
bounded time interval and uniformly over any fixed finite set of
addresses, for either finite boundary convention.

Proof. Set $R_n=I-A_n/3$ and retain $R_\infty$ of (120.16).
For the killed choice $R_n$ is the compression of $R_\infty$; the two
omitted child transitions at each leaf go to the zero-valued cemetery.
For the closed choice those transitions become holds at the leaf.
At a singleton the resulting rows are respectively holding $1/3$
with cemetery probability $2/3$, and holding one. Away from the finite
boundary every row agrees with the infinite row, including the actual
root convention.

Put $F=Uf$. For $k\le R$, every transition start in a $k$-step path
from $x$ has distance at most $k-1<R$ from $x$; each neighbour it can
use lies in $B_R(x)$. Thus no changed boundary row is needed, and

$$
(R_n^k(F|_{D_n}))(x)=(R_\infty^kF)(x)
\qquad(0\le k\le R).
\tag{120.19}
$$

For $R=0$ this simply asserts equality of the initial values.
All later evaluations have magnitude at most $\|F\|_\infty$, since
both the stochastic and substochastic matrices are contractions on
bounded functions. Subtracting their common rate-three Poisson series
therefore bounds the difference by
$2\|F\|_\infty\mathbb P\{\operatorname{Poisson}(3t)>R\}$.
Use (120.13), $\|F\|_\infty=\|f\|_\infty$ and monotonicity of the
Poisson tail for $t\le T$ to obtain (120.18).

For a fixed address $x$, (120.3) permits

$$
R=R_n(x):=\lfloor n/2\rfloor-|x|\ge0,
\tag{120.20}
$$

because $B_R(x)\subseteq B_{R+|x|}(o)\subseteq D_n(u)$.
This radius tends to infinity. For fixed $T$ the tail in (120.18) is
explicitly $e^{-3T}\sum_{k>R}(3T)^k/k!$ and tends to zero. For a finite
address set $S$, take $R=\lfloor n/2\rfloor-\max_{x\in S}|x|$ once
nonnegative. The same estimate holds simultaneously at every $x\in S$
and for all $\|f\|_\infty\le1$, in particular all $m$ indicators.
Only the contained-ball inclusion is used: the finite domains remain
the actual $D_n(u)$, not replacement balls. This is a bounded-time,
fixed-address statement, without a claim of convergence uniformly over
the whole growing domain or on time windows growing with $n$.
$\square$

**Proposition 120.6 (cycle-indicator whole-volume floor on every actual cut).**
For the same fixed $u,m$ and every $n\ge0$, either choice $A_n$, and
$0\le t\le2/13$, put $g_2(t)=t-13t^2/2$. Then

$$
\max_{c\in C_m}
 \|e^{-tA_n}U_ne_c-U_ne^{-tK_m}e_c\|_{\mu_n}
 \ge g_2(t)\sqrt{\frac{N_n+1}{2mN_n}}.
\tag{120.21}
$$

In particular

$$
\max_{c\in C_m}
 \|e^{-A_n/13}U_ne_c-U_ne^{-K_m/13}e_c\|_{\mu_n}
 \ge\frac1{26}\sqrt{\frac{N_n+1}{2mN_n}}
 \ge\frac1{26\sqrt{2m}}.
\tag{120.22}
$$

No onto hypothesis on the finite restriction $q_n$ is required.

Proof. Write $N=N_n$ and let $I$ and $\ell$ be the numbers of internal
vertices and leaves. Every internal vertex has two children, so
$N-1=2I$ and $\ell=N-I=(N+1)/2$, including a singleton. At every leaf
$x$, its at-most-one actual neighbour in the finite domain cannot
represent both distinct cycle neighbours of $q_n(x)$. Choose one
absent adjacent colour $c_x$. The pair $(x,c_x)$ satisfies the zero-
and one-event condition of (120.8). Both finite boundary choices
therefore give source heat at most $9t^2/2$. On the cycle, the event
of exactly one jump along the specified edge has probability
$te^{-2t}\ge t-2t^2$. Hence target minus source is at least
$g_2(t)$ at each selected pair. It is nonnegative on the stated
interval. Summing one squared error per leaf yields

$$
\sum_{c\in C_m}
 \|e^{-tA_n}U_ne_c-U_ne^{-tK_m}e_c\|_{\mu_n}^2
 \ge\frac{N+1}{2N}g_2(t)^2.
\tag{120.23}
$$

The largest of the $m$ squared norms is at least $1/m$ of this sum,
proving (120.21). At $t=1/13$, $g_2(t)=1/26$, giving (120.22).
For a singleton $q_n(o)=0$, either adjacent colour is unattained and
its pullback is identically zero. Its source heat is exactly zero for
both $[0]$ and $[2]$, while the same target one-jump bound applies.
Thus the leaf argument includes this case without asserting a
surjection from a singleton.

Initially a cut can omit colours. Nevertheless all tests in (120.21)
are defined on the full fixed $C_m$. The restriction eventually becomes
onto: the addresses $o,p_1,\ldots,p_{m-1}$ have all $m$ residues, and
belong to $B_{m-1}(o)$. By (120.3), $n\ge2(m-1)$ is a sufficient
threshold. This is not an optimized threshold or a claim that any
particular capped or stopped history reaches it.

There is no conflict with Proposition 120.5. For every fixed finite
address set, sufficiently advanced cuts put it strictly inside the
domain, so its vertices are no longer leaves. Meanwhile

$$
N_n\longrightarrow\infty,\qquad
\mu_n(\operatorname{Leaf}(\rho^nu))
 =\frac{N_n+1}{2N_n}\longrightarrow\frac12,
\qquad \mu_n(\{x\})=\frac1{N_n}\longrightarrow0
\tag{120.24}
$$

for each eventually present fixed $x$. The lower-bound witnesses
escape every fixed finite address set but retain a positive part of
the changing whole-vertex probability. Pointwise dominated convergence
with respect to one fixed measure does not establish convergence in
these varying norms. For each $n$ at least one of the same $m$ fixed
indicator tests has the floor (120.22). Finite pigeonhole gives one
fixed colour $c$ and an infinite subsequence of stages with error at
least $1/(26\sqrt{2m})$; neither the maximizing colour at every stage
nor failure of every colour is asserted. The conclusion fixes $m$
before taking $n\to\infty$, and gives no positive floor uniform in
growing $m$. $\square$

### 120.5 Counting vectors, the common field and the separate ray law

**Proposition 120.7 (literal pullback domain and field non-descent).**
For the infinite colouring of Definition 120.3,

$$
\{f:C_m\to\mathbb C:Uf\in\ell^2(\mathcal P,\mathrm{count})\}
 =\{0\}.
\tag{120.25}
$$

The common radial field $\phi(p)=2^{-|p|}$ of Continuation Theorem 55.3
is not $\psi\circ q$ for any function $\psi$ on $C_m$. In particular
the kinetic intertwining (120.13) does not extend, through this same
pullback, to the potential multiplier of that common field. Moreover,
prefix-colour limits do not define a readout on every infinite ray.

Proof. For any nonzero $f$, choose $c$ with $f(c)\ne0$. There are
infinitely many $k\ge1$ with $q(p_k)=c$, so

$$
\sum_{p\in\mathcal P}|f(q(p))|^2
 \ge\sum_{\substack{k\ge1\\k\equiv c\ (\mathrm{mod}\ m)}}|f(c)|^2
 =\infty.
\tag{120.26}
$$

The zero function has zero pullback, proving (120.25). Although
$L_\infty$ separately acts on counting $\ell^2$, no nonzero $Uf$ in
(120.13) lies in that space. This is the fibre-counting distinction
already stated in III Specification 81.5 and Proposition 119.5,
here with every cycle fibre infinite rather than only selected cube
fibres. It is not a general impossibility assertion about other Hilbert
spaces or other correspondences.

For field descent, $q(o)=q(p_m)=0$ but

$$
\phi(o)=1,\qquad \phi(p_m)=2^{-m}.
\tag{120.27}
$$

This violates constancy on a fibre. It also witnesses non-descent on
every finite cut containing these two addresses, in particular for
$n\ge2m$. If $M_\phi U=UM_\psi$ were true on bounded observables,
applying it to the constant one would give $\phi=U\psi$, contradicting
(120.27). Since the kinetic identity already holds, an identity
$(aL_\infty-gM_\phi)U=U(aK_m-gM_\psi)$ with $g>0$ would imply that
same impossible multiplier identity. The source term
$\mathbf1_{\{o\}}$ likewise differs at $o,p_m$ and is not a literal
pullback. A projected force covector, as in §119.6, is a different
relation. Finally, the prefixes of the ray $LRR\cdots$ have colours
$k\pmod m$, $k\ge1$, and are not eventually constant. A convergent
sequence in the finite discrete cycle must be eventually constant,
so this ray has no prefix-colour limit. This neither rules out separately
supplied measurable ray readouts nor asserts positive ray probability
for this single example. $\square$

**Definition 120.8 (ray carrier and the scope of the added laws).** Retain
exactly the original probability $\nu_u$ of (115.3) on infinite rays
$\partial\mathcal P=\{L,R\}^{\mathbb N}$, with its cylinder sigma algebra.
It is not counting measure on occurrence vertices. A ray observable
readout would be a separately specified measurable function on
$\partial\mathcal P$; a ray heat or path quotient would additionally
specify its source law, induced fibre probabilities, generator or
semigroup, domains and a same-map correspondence. These data are not
part of Definition 120.3's finite-address readout.

Neither (120.18) nor vertex normalization constructs an autonomous
ray-boundary law or changes (120.25).

All numerical floors above refer to unit symmetric seam rates and
the unit counting clock, measured in normalized whole-vertex $L^2$.
No transfer of these constants or witness times is made to $NL$,
degree-normalized Laplacians, altered vertex masses, arbitrary
reweightings, other scalar clocks, conditional subvolume norms or
different targets. The exact infinite positive law
concerns bounded observables and the stipulated kinetic heat/path law,
without an operational conversion from heat time to source events or
to physical time. It grants neither field preparation nor an infinite
source execution.

The form/norm/generator distinction of
[VI Theorems 115.2 and 116.2](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md)
and the correspondence obligations of
[III Specification 81.5](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md)
retain their scopes. In particular the recurrence theorem III 81.4
concerns its different one-spine graph $\Gamma_{52}$, not $\mathcal P$.
The grouped cube form, constrained flow, chosen free-flow witness and
counting-coordinate limits of §119 remain their existing results.
Propositions 120.2 and 120.4--120.7 are repo-derived source-specific
deductions using the attributed uniformization, external equitable and
lumpability suppliers, without a worldwide-priority claim or a new
generic covering or lumpability theory. The common source admits the
displayed cycle law for every fixed $m\ge3$; neither that choice, the
cube comparison target, nor the three values of increment memory
select a physical spatial dimension. Metric placement and its measure,
field, boundary, operation and physical-clock correspondences remain
additional mathematical data for any such interpretation.

## 120.99 追加锚（本行以下为增补区）

