# Original passive words and their exact predictive boundary

## 1. The fixed source and representation questions

**Assumption 1.1 (the original endpoint and passive law).** Fix any
original finite $a,\eta,d>0$. Retain [RRO, Definitions 1.1, 7.1 and
8.1][RRO]: the group $G=H^1\times\mathbb R$, identity $e$, Haar
measure $\mu$, unit-source Green field and original $S_{\min}$, with
the original product

$$
(x,y,z,w)(x',y',z',w')
 =(x+x',y+y',z+z',w+w'+xy').
$$

Retain the entire complex self-adjoint endpoint, including the
normalization of its maximal-domain coefficients:

$$
\begin{gathered}
h=\frac{w_*}{\|w_*\|_{L^2(\mu)}},\qquad
\rho=\frac{A(h)}{C(h)},\qquad
D(H_{\rm end})=\{u\in D(S_{\min}^*):A(u)=\rho C(u)\},\\
H_{\rm end}u=S_{\min}^*u,\qquad
m=h^2\mu,\quad m(G)=1,\qquad J_hv=hv,\\
K=J_h^{-1}H_{\rm end}J_h\ge0,\qquad
\ker K=\mathbb C1,\qquad T_t=e^{-tK},\qquad P=T_d=P^*.
\end{gathered}
\tag{1.1}
$$

The inherited source process starts at $Z_0=e$, is conservative, and
has positive-time densities
$\mathbb P_e(Z_t\in dx)=g_t(x)m(dx)$, with
$g_{t+s}=T_sg_t$, $\int g_t\,dm=1$ and $P1=1$.
Write $g=g_{2d}=Pg_d$. These are the owning endpoint and density
supplies, not conclusions about an arbitrary diffusion.

For every permitted repaired bounded Borel representative $b$ of
$g_d$, use exactly

$$
\begin{gathered}
c=\frac1{4(1+\|g_d\|_\infty)},\qquad [b]=g_d,\qquad
0<b\le1+\|g_d\|_\infty,\\
\mathcal L=\{0,1,3,B\},\qquad
f_3=cb,\qquad f_B=\frac14,\qquad
f_0=f_1=\frac{3/4-f_3}{2},\\
X_j=Z_{(j+2)d},\qquad
\mathbb P(Y_j=y\mid (Z_t)_{t\ge0})=f_y(X_j)\quad(j\ge0).
\end{gathered}
\tag{1.2}
$$

The read noise is fresh and conditionally independent given the source
path, and leaves its evolution unchanged. Thus the lead-in is $2d$,
every subsequent gap is $d$, and all four original outcomes remain.
All pairings below are in the real $L^2(m)$ unless stated otherwise;
function identities are $m$-class identities. The full complex
endpoint in (1.1) is unchanged by using real pairings.

**Definition 1.2 (words, residuals and clock cuts).** For finite words,
including the empty word $\varepsilon$, retain the original recursion
and cylinder law [RRO, (8.4)]:

$$
F_\varepsilon=1,\qquad F_{yv}=f_yPF_v,\qquad
p(w)=\mathbb P_e(Y_0\cdots Y_{|w|-1}=w)=\langle g,F_w\rangle_m,
\qquad p(\varepsilon)=1.
\tag{1.3}
$$

Here $uv$ is chronological concatenation. Define

$$
H_p(u,v)=p(uv),\qquad R_u(v)=\frac{p(uv)}{p(u)},\qquad
\mathcal R_p=\operatorname{span}_{\mathbb R}\{H_p(u,\cdot):u\in\mathcal L^*\}.
\tag{1.4}
$$

Every $p(u)>0$: conditional on each source path its finitely many
specified emissions have a strictly positive product. The algebraic
rank of $H_p$ is the supremum of the ranks of its finite evaluation
blocks. A cut $t$ is after $t$ labels and before $Y_t$, whose physical
read time remains $(t+2)d$. Same-cut blocks restrict all histories
to length $t$. No empirical matrix or bounded Hankel operator is part
of this definition.

**Definition 1.3 (the distinct finite representation requirements).**
An autonomous $r$-dimensional linear realization over
$\mathbb F=\mathbb R$ or $\mathbb C$ consists of fixed vectors and
label matrices with

$$
p(w)=\alpha A_{w_0}\cdots A_{w_{n-1}}\beta
\quad\text{for every }w\in\mathcal L^n\text{ and every }n\ge0.
\tag{1.5}
$$

An $r$-state autonomous HMM is the nonnegative subclass with an
initial probability row, nonnegative label kernels $M_y$, stochastic
sum $\sum_yM_y$, and terminal column $\mathbf1$. Emission followed by
transition is an equivalent convention since the last stochastic
transition acts on $\mathbf1$.

A clock-assisted linear boundary of dimension at most $r$ is allowed
arbitrary time-dependent updates and readouts, but at every cut $t$
its unnormalized future responses must factor as

$$
p(uv)=a_t(u)b_t(v),\qquad
a_t(u)\in\mathbb F^{1\times r_t},\quad
b_t(v)\in\mathbb F^{r_t\times1},\quad r_t\le r,
\quad |u|=t.
\tag{1.6}
$$

The same future column at that cut serves every history. This includes
time-inhomogeneous HMMs with uniformly at most $r$ hidden states and
time-dependent finite linear generators. It even permits the dimension
to vary with the clock subject to the stated bound.

A deterministic exact predictive memory assigns a reached state
$s(u)$, updates it after each observed label, and determines every
$R_u(v)$. An autonomous memory has state-dependent rules; a
clock-assisted memory may additionally use the cut $t$. Its cardinality
is distinct from the dimension of the linear span of responses. A
nonlinear state in $\mathbb R^r$ with unlimited precision is a further,
different requirement. A state stored in at most $b$ bits has at most
$2^b$ possible retained values at a given clock cut.
All history-dependent retained context belongs to the state; only the
supplied clock is exempt in the clock-assisted versions.

The generic linear notions are those of
[WordHankelRealization, `residualSpace`, `MatrixRealization` and
`finite_hankel_realization`][WORD]. The corresponding classical
finite-rank equivalence is [Balle--Panangaden--Precup, Theorem 2][WFA],
for arbitrary functions on finite-alphabet words. Its later
absolute-summability and Hankel-SVD hypotheses are not used here:
$\sum_{|w|=n}p(w)=1$ at every length, so $p$ is not summable over
all finite words. The conditional-history matrix is also the
uncontrolled system-dynamics matrix of [Singh--James--Rudary,
§§2--3][PSR], with observation alphabet $\mathcal L$ and no actions.

## 2. The actual observation-to-residual correspondence

**Theorem 2.1 (reachable source densities and the passive predictive
quotient).** Under Assumption 1.1, put

$$
z_\varepsilon=g,\qquad L_yz=P(f_yz),\qquad z_{uy}=L_yz_u.
\tag{2.1}
$$

Then the $z_u$ are nonnegative bounded $L^2(m)$ classes and

$$
p(uv)=\langle z_u,F_v\rangle_m,\qquad
\int z_u\,dm=p(u),\qquad
R_u(v)=\langle \pi_u,F_v\rangle_m,
\quad\pi_u=\frac{z_u}{p(u)}.
\tag{2.2}
$$

The density $\pi_u$ is the conditional density of the same source
at the next read time $(|u|+2)d$ after the original observed history
$u$. If $\mathcal Z=\operatorname{span}_{\mathbb R}\{z_u\}$ and
$\mathcal O(z)(v)=\langle z,F_v\rangle_m$, then

$$
\mathcal O(\mathcal Z)=\mathcal R_p,\qquad
\mathcal Z/\ker(\mathcal O|_{\mathcal Z})\simeq\mathcal R_p,
\qquad \mathcal O(L_yz)(v)=\mathcal O(z)(yv).
\tag{2.3}
$$

In particular the kernel in (2.3) is invariant under each $L_y$;
the quotient retains exactly the reachable linear future responses.

*Proof.* Multiplication by $f_y$ and the Markov operator preserve
nonnegativity and boundedness. The original Markov/read contract,
self-adjointness, and (1.3) give

$$
\langle L_yz,F_v\rangle_m
 =\langle z,f_yPF_v\rangle_m
 =\langle z,F_{yv}\rangle_m.
\tag{2.4}
$$

Starting from $z_\varepsilon=g$, induction on $u$ proves the first
identity in (2.2); $v=\varepsilon$ gives its mass. More specifically,
for every bounded real test $\phi$, the joint integral for a read $y$
and the next hidden state is $\langle\pi_u f_y,P\phi\rangle_m$.
It equals $\langle P(f_y\pi_u),\phi\rangle_m$. Its normalizing
mass is

$$
a_y(\pi_u)=\int f_y\pi_u\,dm=R_u(y)>0,\qquad
\pi_{uy}=\frac{P(f_y\pi_u)}{a_y(\pi_u)}.
\tag{2.5}
$$

This proves the asserted conditional-density meaning and all future
identities without changing the preparation. Equation (2.4) proves
the intertwining in (2.3); the image and quotient identities follow
by linearity and the first isomorphism theorem. The kernel statement
uses $\mathcal O(z)(yv)=0$ for all $v$ whenever $\mathcal O(z)=0$.
This is the original-source correspondence to the existing residual
and shift constructions [WORD], including their private factorization
helpers; it does not assert injectivity on the hidden Hilbert space.
$\square$

## 3. Explicit visible Gram blocks

**Theorem 3.1 (original one-marker words have unbounded Hankel rank).**
For every integer $N\ge1$ and $0\le i,j<N$, the actual original
word block with rows $B^i$ and columns $B^{j+1}3$ satisfies

$$
\begin{aligned}
C_N(i,j)&=p(B^{i+j+1}3)
 =\frac c4\,4^{-i-j}\langle P^ig,P^jg\rangle_m,\\
C_N&=\frac c4D_NG_ND_N,\qquad
D_N=\operatorname{diag}_{0\le i<N}(4^{-i}),\qquad
G_N(i,j)=\langle P^ig,P^jg\rangle_m,\\
\det C_N&=(c/4)^N4^{-N(N-1)}\det G_N>0.
\end{aligned}
\tag{3.1}
$$

Thus $H_p$ has infinite algebraic rank over both $\mathbb R$ and
$\mathbb C$, and $\mathcal R_p$ has countably infinite algebraic
dimension. The original law admits neither a finite autonomous linear
realization nor a finite autonomous HMM.

*Proof.* The constant original emission gives, for every $n\ge0$,

$$
z_{B^n}=4^{-n}P^ng,\qquad
F_{B^n3}=c4^{-n}P^ng_d,\qquad p(B^n)=4^{-n}.
\tag{3.2}
$$

In particular $F_{B^{j+1}3}=c4^{-(j+1)}P^jg$ because
$Pg_d=g$. Substitution into (2.2) proves (3.1). The one additional
$B$ in the suffix is the precise original-time alignment; no
fractional read epoch is introduced.

Reuse [RRO, Theorem 7.2] or [FIB, Lemma 169.1][FIB]:
$g,Pg,\ldots,P^{N-1}g$ are independent. The usual Gram criterion
therefore makes $G_N$ positive definite. Its hypotheses are a finite
independent family in the real Hilbert space $L^2(m)$; the pinned
Mathlib supplier is `Matrix.posDef_gram_of_linearIndependent` in
[GramMatrix][GRAM]. The diagonal factors in (3.1) are invertible.
Real independence also implies complex independence by separating
real and imaginary coefficients, and these real determinants stay
nonzero over $\mathbb C$.

Every finite linear realization factors each such block into an
$N\times r$ forward matrix and an $r\times N$ future matrix, so
its rank is at most $r$. This is the necessary direction of [WORD]
with field $\mathbb F$, alphabet $\mathcal L$ and word function
$p$; taking $N=r+1$ contradicts (3.1). An HMM is a subclass of these
linear realizations, so no positive-realization converse is needed.
The residual span is generated by the countable set of finite words,
and (3.1) supplies arbitrarily large independent subsets. Its
algebraic dimension is consequently exactly countable infinity.

For the unary [SequenceHankelRealization][SEQ] interface, take
$U=Y=\mathbb R$ and the linear map

$$
\mathfrak m(n)(x)=x\,\frac{4^{n+1}}c p(B^{n+1}3)
                =x\langle g,P^ng\rangle_m.
\tag{3.3}
$$

Its scalar Hankel blocks are $G_N$. Thus its existing
`finite_tailSpace_iff_exists_realization` equivalence has an
infinite-dimensional tail space here. Neither that equivalence nor
the hidden-orbit independence is a new claim of this theorem; the
new interface is their identification with the original words in
(3.1)--(3.3). $\square$

## 4. Same-clock histories, including a common retained suffix

**Theorem 4.1 (unbounded original cut rank even after a common finite
suffix).** Fix any integers $k\ge0$ and $N\ge1$. For $0\le i,j<N$
and $\ell\ge0$, use the actual words

$$
u_i^{(\ell)}=B^{\ell+N-1-i}3B^{i+k},\qquad
v_j=B^{j+k+1}3B^{N-1-j}.
\tag{4.1}
$$

Every history has length $t=\ell+N+k$ and ends in the same $k$
labels $B$; every future has length $N+k+1$. Put
$J_{\ell,N,k}(i,j)=p(u_i^{(\ell)}v_j)$ and
$G_{N,k}(i,j)=\langle P^{i+k}g,P^{j+k}g\rangle_m$. Then

$$
4^\ell J_{\ell,N,k}
 \longrightarrow c^2 4^{-(2N+2k-1)}G_{N,k}
\quad\text{entrywise as }\ell\longrightarrow\infty.
\tag{4.2}
$$

The limit is positive definite. There exists a finite
$\ell_0=\ell_0(a,\eta,d,N,k)$ such that for every
$\ell\ge\ell_0$,

$$
\det J_{\ell,N,k}>0,\qquad
\operatorname{rank}\bigl[R_{u_i^{(\ell)}}(v_j)\bigr]_{i,j<N}=N.
\tag{4.3}
$$

Consequently the original law has no uniformly finite-dimensional
clock-assisted linear boundary, no clock-assisted HMM with a
uniformly finite hidden set, and no uniformly finite-cardinality
deterministic exact predictive memory with a supplied clock. It is
not an order-$k$ observed Markov law for any finite $k$, even with
arbitrary clock-dependent transition rules.

*Proof.* Use $q(w)=\int F_w\,dm$ from [RRO, Definition 8.1] only as
a comparison coefficient. The original word recursion gives the
exact bridge, for every fixed word $w$,

$$
4^\ell p(B^\ell w)=\langle P^\ell g,F_w\rangle_m,
\qquad
\bigl|4^\ell p(B^\ell w)-q(w)\bigr|
 \le\|P^\ell g-1\|_2\longrightarrow0.
\tag{4.4}
$$

Here $0\le F_w\le1$, $m(G)=1$, and the strong limit is precisely
[RRO, (8.9)] with $\int g\,dm=1$. Its supplied hypotheses are
$K\ge0$, self-adjointness and $\ker K=\mathbb C1$; no spectral
gap or uniform convergence rate is needed.

For nonnegative integers $a,s,b$, invariance of $m$, (3.2), and
$F_{wB^b}=4^{-b}F_w$ give

$$
q(B^a3B^s3B^b)
 =c^2 4^{-(a+s+b)}\langle g_d,P^{s+1}g_d\rangle_m.
\tag{4.5}
$$

The terminal identity follows first for $w=\varepsilon$ from
$P1=1$, and then for all $w$ by (1.3). In (4.5), set
$a=N-1-i$, $s=i+j+2k+1$, $b=N-1-j$. Then
$a+s+b=2N+2k-1$ and

$$
\langle g_d,P^{i+j+2k+2}g_d\rangle_m
 =\langle P^{i+k}g,P^{j+k}g\rangle_m.
\tag{4.6}
$$

Equations (4.4)--(4.6) prove (4.2). In the actual word the two
specified $3$ reads occur at indices $\ell+N-1-i$ and
$\ell+N+2k+j+1$, hence at the original physical times
$(\ell+N+1-i)d$ and $(\ell+N+2k+j+3)d$. Their gap is exactly
$(i+j+2k+2)d$, as in (4.6).

The family $P^kg,\ldots,P^{k+N-1}g$ is independent by the same
supplied no-polynomial-relation result (or Lemma 169.1 at source time
$(k+2)d$). Thus $G_{N,k}$ is positive definite. Continuity of the
finite determinant makes $\det(4^\ell J_{\ell,N,k})$ positive for
every sufficiently large finite $\ell$. Since its scaling factor is
$4^{\ell N}>0$, the original determinant is positive as well.
The finite-$\ell$ matrix need not be symmetric; no positive-definiteness
claim is made about it. Dividing row $i$ by the positive
$p(u_i^{(\ell)})$ proves the normalized rank assertion.

At this common cut a boundary satisfying (1.6) factors the displayed
block through $r_t$ coordinates. Choosing $N=r+1$ excludes a uniform
bound $r$. For an inhomogeneous HMM these coordinates are the
unnormalized hidden-state probabilities after the prefix, and the
columns are the future word laws from each state at that same clock.
For a deterministic predictor with $r$ states the rows factor through
$p(u)\mathbf1_{\{s(u)=s\}}$ and the $r$ future profiles at that clock.
Both factorizations obey the same rank bound.

Finally an order-$k$ law at a known clock makes all future profiles
equal for histories with the same last $k$ labels, by iterating its
one-step rule. The histories in (4.1) share that suffix. Taking $N=2$
in (4.3) contradicts equality of their future profiles. $\square$

## 5. The economical exact boundary and its resource scope

**Theorem 5.1 (the original predictive quotient and representation
separations).** For this fixed original law, identify histories by
$u\sim u'$ exactly when $R_u=R_{u'}$ on all finite future words.
The coarsest reached autonomous deterministic predictive boundary is

$$
\mathcal B_p=\{R_u:u\in\mathcal L^*\},\qquad
\text{initial state }R_\varepsilon,\qquad
\operatorname{out}_y(R)=R(y),\qquad
U_y(R)(v)=\frac{R(yv)}{R(y)}.
\tag{5.1}
$$

It has exactly countably infinitely many reached states. Every exact
autonomous deterministic sufficient statistic maps uniquely on its
reached image onto this boundary. The normalized filter (2.5) realizes
it through $\pi_u\mapsto(v\mapsto\langle\pi_u,F_v\rangle_m)$.
Even with a supplied clock, the number and the linear span dimension
of reached conditional future profiles are eventually at least $N$
for every fixed finite $N$.

This excludes exact all-word prediction with any fixed bit bound, but
does not exclude a one-real nonlinear encoding with unlimited
precision. For every fixed finite horizon there is a finite exact
history-table representation of the same law. If an autonomous linear
model matches all original words through horizon $H\ge2$, its
dimension is at least $\lfloor H/2\rfloor$.

*Proof.* Positivity and cylinder consistency of the original law give
$\sum_yR(y)=1$, and direct cancellation gives
$R_{uy}(v)=R_u(yv)/R_u(y)$. Thus (5.1) is well defined on reached
profiles. The product of its successive readouts along any word $w$
telescopes to $p(w)$. The source filter supplies the same profiles
by Theorem 2.1. The factorization and uniqueness are the existing
predictive-sufficiency universal property [MIN], with
$\mathrm{Past}=\mathcal L^*$ and
$\mathrm{futureLaw}(u)=R_u$; equality of cylinder coordinates is
equality of the entire future measure on the finite-alphabet sequence
space. The positive-symbol update is the specialization of [UPDATE].
These generic quotient properties are reused here.

There are countably many finite words. For each $N$, dividing row
$i$ in (3.1) by $p(B^i)=4^{-i}$ preserves independence. Hence the
profiles $R_{B^i}$ are infinitely many distinct reached states, proving
the cardinality claim. Similarly (4.3) supplies $N$ independent
normalized profiles at every cut $t\ge\ell_0+N+k$. It supplies
neither an effective threshold nor their exact growth with $t$.
The equality $f_0=f_1$ also gives $R_{u0}=R_{u1}$ from (2.5), so
the quotient already discards genuine redundant history while
retaining the infinite family just exhibited.

For the nonlinear distinction, assign digits
$\delta(0)=1$, $\delta(1)=2$, $\delta(3)=3$, $\delta(B)=4$ and
code each finite history by

$$
x_\varepsilon=1,\qquad x_{uy}=5x_u+\delta(y).
\tag{5.2}
$$

Its base-five representation is a leading sentinel $1$ followed by
the nonzero history digits, so it is injective. On the countable
reached subset of $\mathbb R$, use update (5.2) and readout
$R_{\operatorname{decode}(x)}(y)$. These are Borel maps on that
subset and reproduce all original words by the same telescoping
identity. The readout uses the exact source-defined law and an
unrestricted lookup; no finite description, evaluation algorithm,
finite precision or bounded storage is asserted. Infinite linear
rank therefore does not supply a nonlinear real-coordinate lower
bound beyond excluding a single constant state.

For a horizon $H$, retain the finite prefix tree through depth $H$
and use $R_u(y)$ for $|u|<H$. It reproduces precisely the required
cylinders, with exact real probability entries rather than a promised
finite-precision table, and no assertion about later predictions. Conversely the
block (3.1) uses only words of length at most $2N$; choose
$N=\lfloor H/2\rfloor$ to obtain the finite-horizon linear lower
bound. This is a bound for exact coefficient equality, not for
estimated coefficients or approximation. $\square$

**Definition 5.2 (recovery and unresolved quantitative conditions).**
For the fixed mathematical source, the complete word law determines
all reached profiles by (1.4); the boundary (5.1), its initial state,
updates and readouts recover the complete word law by the proof of
Theorem 5.1. Equation (2.3) identifies this operational boundary's
linear span with a quotient of reachable source densities. It does
not invert that quotient to a hidden point, $G$, $H_{\rm end}$,
$h$, $\rho$ or $d$. Such a spatial, endpoint or clock inverse needs
a separately proved identifiability correspondence for those objects.
The original space and boundary enter the displayed memory through
$P$ and $g$; chronological continuation enters through label append
and their indexed heat moments.

All words in (3.1) and (4.1) are unconditional cylinder coordinates
of the original four-outcome law. They require no reset, selected
outcome, extra label, hidden-coordinate probe or stationary preparation.
The invariant comparison in (4.4) is joined to actual $e$-start words
by that exact identity and its proved limit. Cylinder coordinates,
rare histories, $c$, Gram entries and exact future laws are not new
observation or evaluation ports for the actual observer. In particular
the existence of $\ell_0$ does not provide its numerical value or a
way to force the witnessing histories.

No determinant margin, parameter-uniform bound, finite-data rank
certificate, sampling lower bound, error tolerance or stopping rule
is implied. Exact infinite rank is compatible with finite-horizon
approximation; the latter needs its own error and access assumptions.
[RRO, §§8--9] retains its fixed-word acquisition and conditional
quantitative bounds. Those do not evaluate all reached profiles with
uniform finite resources. Recovery of space, time, boundary and
usable memory under such resources remains an additional problem.

**Definition 5.3 (supplier scopes).** The source-specific deductions
(2.2)--(4.6) and their consequences are `repo-derived` ordinary
mathematics under Assumption 1.1. The thermal independence of [RRO,
Theorems 7.2--7.3] and [FIB, Lemma 169.1], the marked-word identity
[RRO, Theorem 8.2], generic Gram positivity, finite linear realization
equivalences [WORD, SEQ, WFA], and predictive quotient/update properties
[MIN, UPDATE, PSR] are reused suppliers. The rotation-odd kernel of
[FIB, §170] concerns its specified linear successor stack; it is not
used as a theorem about the whole passive-word law. [FIB, §171]
concerns compensation and residual approximation, not all-word
equality. None of these mathematical source correspondences asserts
physical acquisition or literature priority for the displayed application.

[RRO]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md
[FIB]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_IV.md
[WORD]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/D5/S3/Observer/Hankel/WordHankelRealization.lean
[SEQ]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/D5/S3/Observer/Hankel/SequenceHankelRealization.lean
[MIN]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/D5/S3/ObserverMemory/PredictionFactors/PredictiveStateUniversalMinimality.lean
[UPDATE]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/D5/S3/ObserverMemory/ContextUpdates/PredictiveStateUnifilarUpdate.lean
[GRAM]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean
[WFA]: https://arxiv.org/html/1501.06841v3
[PSR]: https://arxiv.org/pdf/1207.4167

## 追加锚（本行以下为增补区）

## 6. First actual B-blocks and simultaneous moving-cut prediction

**Definition 6.1 (one original source and the stopped window).** Retain
Assumption 1.1 in its entirety, for every finite $a,\eta,d>0$ and every
permitted Borel repair. In particular retain $G=H^1\times\mathbb R$,
the normalized $h$, the complete complex non-Friedrichs endpoint
$A=\rho C$ distinct from $C=0$, the operator and form domains and source
trace, and the conservative original process from $e$. Its first read
is at $2d$, subsequent gaps are $d$, and its only emissions remain
$0,1,3,B$ with fresh conditionally independent noise. No operation on
the source is added. Write $\mathscr F_t=\sigma(Y_0,\ldots,Y_{t-1})$.
A cut $t$ is after $t$ labels; the next read is still at $(t+2)d$.

Use $P=T_d$, $g=g_{2d}=Pg_d$ and the original $F_u,p(u)$ of (1.3).
The stationary mathematical comparison has the same transition and
read kernels, with coefficients

$$
 q(u)=\int F_u\,dm,\qquad q(\varepsilon)=1,\qquad
 Q_w^H(v)=\frac{q(wv)}{q(w)}\quad(|v|=H).
 \tag{6.1}
$$

It is [OWGR, Definition 15.1]'s comparison law, not an available
stationary preparation. All $q(u)$ and $p(u)$ are positive by the
original strictly positive finite emission products. Both coefficient
families are consistent under summing extensions.

Fix deterministic integers $S\ge0$, $H\ge1$, $r\ge1$, $L\ge1$.
For $k\ge1$ define

$$
 \begin{aligned}
 U_k&=S+(k-1)L,\\
 C_k&=\{Y_{U_k}\cdots Y_{U_k+L-1}=B^L\},\\
 J&=\inf\{k\ge1:C_k\},\qquad T=S+LJ,\\
 W_j&=Y_T\cdots Y_{T+j-1}\quad(0\le j\le r),\qquad W_0=\varepsilon.
 \end{aligned}
 \tag{6.2}
$$

For any actual cut, the target vector is

$$
 {\bf R}_t^H(v)=R_{Y_{<t}}(v)
   =\frac{p(Y_{<t}v)}{p(Y_{<t})}\quad(|v|=H),\qquad
 Y_{<t}=Y_0\cdots Y_{t-1}.
 \tag{6.3}
$$

At $T+j$ this conditions on the entire prefix through that cut,
including every actual label in $W_j$. The gate and its index are
determined by that prefix. They supply no extra future conditioning.

**Lemma 6.2 (the original word square).** Put $N=H+r$, let
$z^{\mathsf R}$ denote word reversal, and set

$$
 \begin{aligned}
 h_z&=P^L(F_z-q(z)),\\
 A_N(L)&=\frac12\sum_{|z|=N}\|h_z\|_2\\
 &=\frac12\sum_{|z|=N}
 \sqrt{\,4^{2L-1}q(z^{\mathsf R}B^{2L-1}z)-q(z)^2\,}.
 \end{aligned}
 \tag{6.4}
$$

Every radicand is nonnegative. With the full-source defect
$\Theta(\lambda)=(1-d_\lambda)/d_\lambda$ of [DPCR, Definition 9.1],

$$
 A_N(L)\le\frac{4^N}{2}
       \sqrt{\Theta\!\left(\frac1{2Ld}\right)}.
 \tag{6.5}
$$

*Proof.* Self-adjointness of $P$ and the original constant $f_B=1/4$
give, for every integer $b\ge0$,

$$
 q(z^{\mathsf R}B^bz)=4^{-b}\langle F_z,P^{b+1}F_z\rangle_m.
 \tag{6.6}
$$

Indeed, write the cylinder integral as successive multiplication by
$f_y$ and application of $P$. Moving the factors of the reversed left
word across the pairing leaves $F_z$ on the left; the $b$ constant
multipliers leave $P^{b+1}$ between the two copies of $F_z$.
For $b=2L-1$, conservation and $\int F_z\,dm=q(z)$ give

$$
 \|h_z\|_2^2
 =\langle F_z-q(z),P^{2L}(F_z-q(z))\rangle_m
 =4^{2L-1}q(z^{\mathsf R}B^{2L-1}z)-q(z)^2.
 \tag{6.7}
$$

Since $0\le F_z\le1$, the centered function has sup norm at most one.
Apply the supplied centered heat estimate [DPCR, Theorem 9.2] at
$s=2Ld$ to (6.7), then sum over the $4^N$ words. This uses the
full original endpoint defect, with neither a spectral gap nor an
effective uniform rate. $\square$

**Lemma 6.3 (the stopped gate in the actual law).** For any
$M\ge\|g_d\|_\infty$ and any integer $N\ge1$,

$$
 \mathbb E_e\operatorname{TV}({\bf R}_T^N,q|_{\mathcal L^N})
 \le\sqrt M\,A_N(L).
 \tag{6.8}
$$

Here $A_N(L)$ is (6.4) with that $N$, and $S$ is any deterministic
nonnegative cut.

*Proof.* Put $b_L=4^{-L}$ and $E_{k-1}=\bigcap_{i<k}C_i^c$.
A prefix $u$ of length $U_k$ satisfying $E_{k-1}$ has, after the
successful block, precisely the actual posterior

$$
 \pi_{uB^L}=P^L\pi_u,\qquad
 p(uB^L)=b_Lp(u),\qquad
 {\bf R}_{U_k+L}^N(z)-q(z)=\langle\pi_u,h_z\rangle_m,
 \tag{6.9}
$$

by (2.5). Thus $|\langle\pi_u,h_z\rangle|
\le\langle\pi_u,|h_z|\rangle$. Theorem 2.1 identifies $\pi_u$ as
the conditional density of $X_{U_k}=Z_{(U_k+2)d}$ given $u$.
Summing the last inequality over all such prefixes, and then over
the mutually disjoint gate events $\{J=k\}$, bounds the expectation
in (6.8) by

$$
 \frac12\sum_{|z|=N}\sum_{k\ge1}
 b_L\,\mathbb E_e[
       \mathbf1_{E_{k-1}}|h_z(X_{U_k})|].
 \tag{6.10}
$$

Conditional on the entire hidden path, the disjoint blocks have
independent all-$B$ indicators of constant probability $b_L$.
Consequently $E_{k-1}$ has conditional probability
$(1-b_L)^{k-1}$, independent of that path, and (6.10) equals

$$
 \frac12\sum_{|z|=N}\sum_{k\ge1}
 b_L(1-b_L)^{k-1}
 \langle g_{(U_k+2)d},|h_z|\rangle_m.
 \tag{6.11}
$$

The actual, unconditioned density at this read epoch satisfies

$$
 \int g_{(U_k+2)d}\,dm=1,\qquad
 \|g_{(U_k+2)d}\|_\infty\le\|g_d\|_\infty\le M,\qquad
 \|g_{(U_k+2)d}\|_2\le\sqrt M.
 \tag{6.12}
$$

These follow by the original propagation and Markov contraction.
Cauchy--Schwarz bounds each pairing in (6.11) by
$\sqrt M\|h_z\|_2$. The geometric weights sum to one, proving (6.8).
This argument averages the full actual posteriors. It never replaces
them by stationary posteriors, bounds each history's posterior
density by $M$, or conditions the result on a chosen $J$. $\square$

**Lemma 6.4 (consuming the actual suffix).** For strictly positive
joint probability vectors $a(w,v),b(w,v)$, with marginals $a_w,b_w$,

$$
 \sum_w a_w\operatorname{TV}(a(\cdot\mid w),b(\cdot\mid w))
 \le\operatorname{TV}(a,b)+\operatorname{TV}(a_w,b_w)
 \le2\operatorname{TV}(a,b).
 \tag{6.13}
$$

*Proof.* For each coordinate,
$|a(w,v)-a_wb(w,v)/b_w|
\le|a(w,v)-b(w,v)|+|b_w-a_w|b(w,v)/b_w$.
Sum over $v,w$ and divide by two. Marginalization contracts TV,
giving the second inequality. The bound has no inverse minimum
marginal: rare suffixes are weighted by their actual probability.
$\square$

**Theorem 6.5 (simultaneous full-history prediction in the stopped
window).** For every source in Definition 6.1, every deterministic
$S,H,r,L$ as there, every $\epsilon>0$, and $M\ge\|g_d\|_\infty$,

$$
 \begin{aligned}
 &\mathbb P_e\left\{
   \max_{0\le j\le r}
   \operatorname{TV}({\bf R}_{T+j}^H,Q_{W_j}^H)>\epsilon\right\}\\
 &\quad\le
 \min\left\{1,\frac{2(r+1)\sqrt M\,A_{H+r}(L)}{\epsilon}\right\}\\
 &\quad\le
 \min\left\{1,
 \frac{(r+1)4^{H+r}\sqrt{M\Theta(1/(2Ld))}}{\epsilon}\right\}.
 \end{aligned}
 \tag{6.14}
$$

The event is unconditional in the original law. The same numerical
bound holds for each deterministic $S$, without asserting one event
simultaneously over all $S$. It is simultaneous for all $r+1$ cuts and
therefore covers any causal selection among them. It is not a
history-by-history, gate-value-conditional, or selected-branch
conditional guarantee.

*Proof.* Fix any stopped history $u=Y_{<T}$. For $j\le r$ apply
(6.13) to

$$
 a(w,v)=R_u(wv),\qquad b(w,v)=q(wv),\qquad |w|=j,\quad |v|=H.
 \tag{6.15}
$$

Conditioning $a$ on its actual $w$ gives exactly $R_{uw}(v)$,
the full-history target at $T+j$. The comparison conditional is
exactly $Q_w^H(v)$. The two joint vectors are marginals of the
length-$N=H+r$ vectors, so their TV is at most
$e_N(u)=\operatorname{TV}(R_u|_{\mathcal L^N},q|_{\mathcal L^N})$.
It follows that

$$
 \mathbb E_e[
 \operatorname{TV}({\bf R}_{T+j}^H,Q_{W_j}^H)\mid\mathscr F_T]
 \le2e_N(Y_{<T})\qquad(0\le j\le r).
 \tag{6.16}
$$

For $j=0$ even the factor one suffices. Taking expectations in
(6.16), using (6.8), and bounding the maximum by the sum gives

$$
 \mathbb E_e\max_{0\le j\le r}
 \operatorname{TV}({\bf R}_{T+j}^H,Q_{W_j}^H)
 \le2(r+1)\sqrt M\,A_N(L).
 \tag{6.17}
$$

Markov's inequality proves the first bound in (6.14); (6.5) proves
the second. Every conditioning in (6.15)--(6.16) is under the same
actual law, and includes the labels actually consumed after $T$.
$\square$

**Proposition 6.6 (the exact disjoint-block waiting law).** For the
deterministic $S,L$ of Definition 6.1, $T<\infty$ almost surely and

$$
 \begin{gathered}
 \mathbb P_e(T-S>kL)=(1-4^{-L})^k\quad(k\ge0),\\
 \mathbb P_e(J=k)=(1-4^{-L})^{k-1}4^{-L}\quad(k\ge1),\qquad
 \mathbb E_e(T-S)=L4^L.
 \end{gathered}
 \tag{6.18}
$$

*Proof.* Conditional on the hidden path the block indicators are
independent Bernoulli variables with constant parameter $4^{-L}$,
so they have that same joint law unconditionally. The geometric
tail and expectation give (6.18). Positivity of the tail at every
finite $k$ excludes a finite worst-case Read bound. The formula
does not assert the same conditional waiting law after a
data-selected calibration, $S$, or $L$. $\square$

## 7. Acquired rational rows and a computable dynamic certificate

**Definition 7.1 (the finite original-word packet).** Write
$\tau=a^2d/\eta$ only in the analysis; its value and the original
$a,\eta,d$ are not supplied as exact names. Use the earned positive
rational lower clock bound $l=\tau_-\le\tau$ of [SRO, Theorems 21.2--22.1]
and the total, paid fixed-reference computation there. Denote its
defect by

$$
 D_v(l)=d^{\mathrm{ref}}_{1/(vl)}.
 \tag{7.1}
$$

The exact full-domain source scaling gives
$d^{\mathrm{orig}}_{1/(vd)}=D_v(\tau)$. Its retained properties
[SRO, (SRO.150)--(SRO.151)] are

$$
 0<D_v(l)<1,\qquad l\le\tau\Longrightarrow D_v(l)\le D_v(\tau),
 \qquad D_v(l)\longrightarrow1\quad(v\longrightarrow\infty).
 \tag{7.2}
$$

These are mathematical/reference computations, not specimen actions.

For $N=H+r$, choose deterministic $n\ge1$ and rational $t,\beta>0$,
and compute rational lower enclosures

$$
 0<D_0^-\le D_4(l),\qquad 0<D_n^-\le D_n(l),\qquad
 V_{n,N}^+=\frac{2N-1}{4n}
                   +2\frac{1-D_n^-}{D_n^-}.
 \tag{7.3}
$$

Require the rational input test

$$
 4^{2N}V_{n,N}^+\le4\beta^2t^2D_0^-.
 \tag{7.4}
$$

Use all actual length-$N$ original-word counters from [DPCR,
Definition 9.3], with $n$ overlapping windows. They use exactly
$n+N-1$ labels, $Y_0$ through $Y_{n+N-2}$, ending at
$(n+N)d$. Put

$$
 a(x)=\sum_{\substack{|z|=N\\z\text{ starts with }x}}
       \frac{A_{n,N}(z)}n\quad(|x|\le N),\qquad a(\varepsilon)=1.
 \tag{7.5}
$$

All $a(x)$ are rational and consistent prefix marginals of one
probability vector. They are calculated from the retained original
initial record; a later suffix is never reinterpreted as a fresh
$e$-start.

**Lemma 7.2 (the existing sampler on one simultaneous event).**
For a valid deterministic branch $l\le\tau$, the packet in
Definition 7.1 has an event $\mathcal E$ satisfying

$$
 \begin{gathered}
 \mathbb P_e(\mathcal E)\ge1-\beta,\qquad
 \mathcal E=\{\operatorname{TV}(a|_{\mathcal L^N},q|_{\mathcal L^N})
                    \le t\},\\
 \mathcal E\Longrightarrow
 |a(x)-q(x)|\le t\quad(|x|\le N),\qquad |a(3)-c|\le t.
 \end{gathered}
 \tag{7.6}
$$

*Proof.* This is the original nonstationary-start bound [DPCR,
Theorem 9.4, (9.13)] at word length $N$ and window count $n$.
The upper bound (7.3) dominates its variance envelope and $D_0^-$
is a valid lower bound for $d^{\mathrm{orig}}_{1/(4d)}$ by
(7.2). Its failure bound is at most

$$
 \frac{4^N}{2t}\sqrt{\frac{V_{n,N}^+}{D_0^-}}\le\beta
 \tag{7.7}
$$

by (7.4). Every prefix event is an event of the same length-$N$
vector, so its probability error is at most TV, simultaneously.
Finally $q(3)=\int cg_d\,dm=c$. This uses the existing dependent,
overlapping-window estimate, not independent samples or the
transient raw frequency as a new exact law. $\square$

**Proposition 7.3 (generated normalization and row-TV errors).**
Let $\mathcal W_r=\bigcup_{j=0}^r\mathcal L^j$, and define

$$
 \ell_x=\max\{0,a(x)-t\},\qquad u_x=\min\{1,a(x)+t\}
 \quad(x\ne\varepsilon),\qquad
 \ell_\varepsilon=u_\varepsilon=1.
 \tag{7.8}
$$

Check $\ell_w>0$ for every $w\in\mathcal W_r$. When these guards
pass, form the rational probability rows

$$
 \widehat Q_w^H(v)=\frac{a(wv)}{a(w)}\quad(|v|=H),\qquad
 I_{w,v}=\left[\frac{\ell_{wv}}{u_w},
                       \frac{u_{wv}}{\ell_w}\right].
 \tag{7.9}
$$

No guard on a numerator is needed. Generate the rational error

$$
 \zeta_w^{\mathrm{gen}}
 =\frac12\sum_{|v|=H}
 \max\left\{\left|\widehat Q_w^H(v)-\frac{\ell_{wv}}{u_w}\right|,
             \left|\widehat Q_w^H(v)-\frac{u_{wv}}{\ell_w}\right|\right\},
 \qquad \zeta^{\mathrm{gen}}=\max_{w\in\mathcal W_r}
                         \zeta_w^{\mathrm{gen}}.
 \tag{7.10}
$$

On the single event $\mathcal E$ of (7.6), these rows satisfy

$$
 \operatorname{TV}(Q_w^H,\widehat Q_w^H)
 \le\zeta_w^{\mathrm{gen}}\quad(w\in\mathcal W_r).
 \tag{7.11}
$$

For fixed finite $H,r$ and a refining sequence of these packets
with $t_s\to0$, all the guards and any prescribed rational
$\zeta^{\mathrm{gen}}\le\zeta$ with $\zeta>0$ eventually pass on
their common event.

*Proof.* Prefix consistency gives
$\sum_{|v|=H}a(wv)=a(w)>0$ and nonnegative entries, so each row in
(7.9) is exactly a rational probability row. In particular the
normalization uses the acquired marginal, not a rounded or
inconsistently fitted denominator. On $\mathcal E$, both true
coefficients lie in (7.8), so $Q_w^H(v)\in I_{w,v}$; summing the
endpoint bounds gives (7.11). For the final claim, (7.6) implies
$a_s(x)\to q(x)$ on the common event. Every one of the finitely
many $q(w)$ is strictly positive. Thus their lower bounds are
eventually positive, both endpoints of every $I_{w,v}$ converge
to $Q_w^H(v)$, and $\widehat Q_w^H(v)$ has the same limit.
The finite sum and maximum in (7.10) tend to zero. $\square$

**Proposition 7.4 (an earned rational dynamic guard).** For a fixed
deterministic branch, let positive rationals $c_-,l$ satisfy
$c_-\le c$, $l\le\tau$, and set $M_0=1/(4c_-)$. For an integer $L\ge1$
compute a rational enclosure

$$
 0<D_L^-\le D_{2L}(l)
        =d^{\mathrm{ref}}_{1/(2Ll)}.
 \tag{7.12}
$$

For positive rational $\epsilon,\delta_0$, the wholly rational
test

$$
 M_0\frac{1-D_L^-}{D_L^-}
 <\left[\frac{\epsilon\delta_0}
                    {(r+1)4^{H+r}}\right]^2
 \tag{7.13}
$$

implies that the second failure bound in (6.14) is at most
$\delta_0$. For every fixed positive $c_-,l,H,r,\epsilon,\delta_0$
the reference computation finds finite $L$ and precision for which
(7.12)--(7.13) pass.

*Proof.* The original exact calibration gives

$$
 \|g_d\|_\infty=\frac1{4c}-1\le M_0,\qquad
 \Theta(1/(2Ld))\le\frac{1-D_L^-}{D_L^-}.
 \tag{7.14}
$$

The second inequality follows from the original-domain scaling
and (7.2), since $(1-x)/x$ decreases for $x>0$. Substitution in
(6.14) proves sufficiency. For termination, $D_{2L}(l)\to1$;
the reference algorithm supplies arbitrarily close lower
enclosures. Enumerating $L$ and refining the enclosures therefore
crosses the strictly positive right side of (7.13) at finite
values. Each reference call and rational test is finite; fair
finite-precision interleaving avoids an unresolved equality
blocking the search. This proves finite success, without a
numerical name of an original parameter or an exact-law query.
$\square$

## 8. Selection, finite stopping and the actual execution boundary

**Theorem 8.1 (common-event composition, including selected starts).**
Predeclare an effectively enumerated countable family of deterministic
candidate descriptions $\kappa$. Each description specifies rational branch bounds
$l_\kappa,c_\kappa>0$, integers $S_\kappa,H_\kappa,r_\kappa$ in
the ranges of Definition 6.1, positive rational tolerances
$\epsilon_\kappa,\zeta_\kappa$, and an allowance $\delta_\kappa>0$.
Generate $L_\kappa$ from (7.12)--(7.13) with these deterministic
values and $\delta_0=\delta_\kappa$. Require
$\sum_\kappa\delta_\kappa\le\delta$.

Use predeclared acquisition/refinement packets, including startup,
whose common validity event $\mathcal A_\tau$ has probability
at least $1-\alpha$. On it, every selected description has
$l_\kappa\le\tau$, $c_\kappa\le c$ certified by its acquired
outputs, and its rows pass Proposition 7.3 with
$\zeta^{\mathrm{gen}}\le\zeta_\kappa$. Packets for the branch
$l_\kappa$ have deterministic inputs and summable allowances as
in [SRO, Theorem 22.1]. Then one original-law event of probability
at least $1-\alpha-\delta$ covers all selected descriptions and,
within each, all their actual cuts:

$$
 \operatorname{TV}({\bf R}_{T_\kappa+j}^{H_\kappa},
                  \widehat Q_{W_{\kappa,j}}^{H_\kappa})
 \le\epsilon_\kappa+\zeta_\kappa
 \qquad(0\le j\le r_\kappa).
 \tag{8.1}
$$

Selection may use the acquired record, and may include the start cut
or tolerances, provided it is from this predeclared family with its
generated lengths and common budgets. It does not require statistical
independence between calibration, acquisition and the gates.

*Proof.* Fix the true source for the proof, without supplying its
parameters to the program. For every deterministic candidate satisfying
$l_\kappa\le\tau$ and $c_\kappa\le c$, Proposition 7.4 and Theorem 6.5
give an unconditional event $\mathcal D_\kappa$ on which all its
dynamic errors are at most $\epsilon_\kappa$, with failure at most
$\delta_\kappa$. Form on this same record

$$
 \mathcal G_\tau=\mathcal A_\tau\cap
  \bigcap_{\kappa:\ l_\kappa\le\tau,\ c_\kappa\le c}
                      \mathcal D_\kappa.
 \qquad
 \mathbb P_e(\mathcal G_\tau)\ge1-\alpha-\delta.
 \tag{8.2}
$$

The union bound needs only deterministic candidate events. Invalid
branches are absent from the intersection. On $\mathcal A_\tau$
every actually selected branch is valid, so on $\mathcal G_\tau$
its dynamic error and its row error (7.11) hold together.
Their triangle inequality proves (8.1). The maximum over cuts
already covers any causal choice of $j$.

This constructs a common event before selection. Conditioning (6.14)
on the observed branch, or simply substituting a random $S,L$ into it,
would not be this argument. If an arbitrary finite-precision start
or tolerance is to be selected, enumerate its possible integer or
rational values in the candidate family and allocate its allowance
there. Unselected descriptions need not be computed. No conclusion
here bounds failure conditional on each selected history, calibration
output, or gate value. $\square$

**Theorem 8.2 (finite successful certification with the existing
suppliers).** Fix a deterministic $S$, finite $H,r\ge1$, rational
$\epsilon,\zeta>0$, and rational $\alpha,\delta>0$ with
$\alpha+\delta<1$. In the paid retained-record and finite-computation
setting of [SRO, Definition 21.1], the original earned startup,
reference defect and finite-word suppliers suffice for a finite
successful certificate as in (8.1), on an event of probability at
least $1-\alpha-\delta$. The certificate includes a generated finite
$L$, every rational row (7.9), all positive normalization guards,
the row error (7.10), the dynamic test (7.13), and all $r$ actual
labels after the reached gate. No exact original parameter or
stationary-law oracle is input.

*Proof.* Split $\alpha=\alpha_{\rm st}+\alpha_{\rm acq}$ positively.
Run [SRO, Theorem 21.2]'s startup. Its possible returned positive
clock bounds $l_i$, $i\ge1$, form a deterministic list. For every
branch $i$, predeclare packets of Definition 7.1 at the fixed
$N=H+r$, with $t_s=2^{-s}$ and allowances
$\beta_{i,s}=\alpha_{\rm acq}2^{-i-s}$, $i,s\ge1$.
Choose $D_{0,i}^->0$ below $D_4(l_i)$ once. The other reference
names and (7.2) allow deterministic increasing $n_{i,s}$ and
refined $D_{n_{i,s}}^-$ satisfying (7.4). Indeed both terms of
$V_{n,N}^+$ tend to zero as $n$ and reference precision grow.
Each search terminates with any prescribed lower bound on $n$.
This is the same packet-generation argument as [SRO,
(SRO.152)], now using the existing unmarked word-vector bound.

Intersect startup's common validity/termination event with every
packet event in the deterministic branches for which $l_i\le\tau$.
The probability is at least $1-\alpha$. Execute only the selected
branch. On this event its packet marginals converge to $q$ by
(7.6), and $a_s(3)-t_s\to c>0$. Proposition 7.3 therefore gives
a finite stage with every normalization guard positive and
$\zeta^{\mathrm{gen}}\le\zeta$. Stop the packet search at its
first such stage with $a_s(3)-t_s>0$. Choose a dyadic
$c_m=2^{-m}$, $m\ge1$, with $c_m\le a_s(3)-t_s$ by a finite
integer search. This is an earned $c_-=c_m>0$ on the same event.

For every deterministic pair $(i,m)$, predeclare
$\delta_{i,m}=\delta2^{-i-m}$. Generate $L_{i,m}$ and its reference
enclosure using Proposition 7.4 with $l_i,c_m,\epsilon,\delta_{i,m}$.
This terminates for every positive rational branch input.
Theorem 8.1 applies to these candidates, with the fixed $S,H,r$
and tolerances and the total dynamic allowance at most $\delta$.
Thus the data selection of $(i,m)$ does not consume an unbudgeted
conditional use of (6.14).

For the selected finite $L$, scan the retained original labels from
$S$ in the prescribed disjoint blocks, extending the same record
as needed. Proposition 6.6 makes its gate finite almost surely.
The countable collection of candidate gates is simultaneously finite
on a probability-one event, so selecting a candidate does not change
this finiteness statement. Obtain and retain every next label through
cut $T+r$ without discarding any intervening labels. Only finitely
many reached finite computations and reads are needed on the common
event. All strict guards above have positive slack eventually,
so this is finite successful certification, not just a limiting
statistical assertion.

The certificate can finish after a tested prefix or even after the
forecast cuts: the retained original record is used throughout.
Actual completion includes every intervening read and its storage.
No assertion that computation finishes by $T$ or catches up during
$[T,T+r]$ is used in the finite-stopping proof. $\square$

**Definition 8.3 (the complete paid bill).** The forecast catalogue has

$$
 R_r=\sum_{j=0}^r4^j=\frac{4^{r+1}-1}{3}
 \quad\hbox{rows, and}\quad
 R_r4^H\quad\hbox{rational forecast entries}.
 \tag{8.3}
$$

Each packet actually retains or computes its $4^{H+r}$ full counters
of width $\lceil\log_2(n+1)\rceil$, the length-$H+r$ word buffer,
and its requested prefix marginals. Startup, all reached packets
and refinements, their complete original prefixes, reference lower
defect names, rational precisions, powers and comparisons are paid.
The normalizations and error certificates cost all
$R_r4^H$ divisions/endpoint comparisons and sums in their actual
rational bit widths; neither arithmetic nor real scalars receive
unit or zero cost. The gate scanner pays for every read, block
counter, failed block, comparison, lookup, suffix update and output.
For fixed deterministic $S,L$ its source waiting bill is exactly
(6.18), followed by $r$ Reads. There is no finite worst-case waiting,
no source-uniform expected bill, and no inference of the same expected
bill for a selected branch.

A full retained archive through a completed cut $C$ contains $C$
original labels, hence $2C$ label bits under the two-bit coding,
in addition to addresses, handles, counters, tables and other records.
Scanning may reuse that archive; it does not delete existing acquired
rows, permissions, legal menus or records. All observations arriving
during reference or processor work, their buffering, retained prefixes,
working space, rescan work and real completion latency remain charged
as in [SRO, Definition 21.1] and [OWGR, §21]. Only finitely many
branches are actually executed, but every reached unsuccessful or
inconclusive finite test is included. No practical efficiency,
throughput, processor deadline, or finite expected total work follows
from the sourcewise finite certificate.

**Definition 8.4 (the reduced interface and the residual bridges).**
The new relation is the simultaneous finite-window forecast after the
first actually observed disjoint $B$ block, with the whole prefix
conditioned at each moving cut. The comparison word square (6.7)
and its actual stopped averaging (6.10)--(6.17) reduce the quantitative
prediction error side of the live continuation interface. The
finite rows in §7 are acquired coordinates for this comparison.
They do not reconstruct the exact filter, hidden point, source
space, endpoint, clock or full future law.

An actual-current consumer still needs a lawful executor that
processes and retains every label through its actual completion
$C$, generates any accumulated additional error, pays its work and
storage, and proves a completion/catch-up condition putting
$C\in\{T,\ldots,T+r\}$ for the chosen certificate. Neither the
finite tables nor the $L4^L$ waiting expectation supplies this
condition. No physical Return, reset, point-feature supplier,
control, extra sensor, native/diffusion/AURIC correspondence, or
infinite-horizon all-law forecast is established. In particular the
unbounded family of finite ordered native trees and its actual
$\rho$ and root/address reads retain their own contracts; these
rows supply no executor for that source. Any use of AURIC still
requires its original $E$, positive evaluations, exact cone,
A1--A3, all P2/PB and original domain, with no map furnished here.

**Definition 8.5 (mathematical attribution).** Reversible word
pairings, conditional probability, positive-form Cauchy--Schwarz,
TV contraction, interval arithmetic and countable union bounds
are mature intermediates. The reused original-source suppliers
are (2.2)--(2.5), [DPCR, §§8--9], the static B-prefix/complete-future
comparisons [OWGR, §§15--16], the earned startup, reference names
and common-event composition [SRO, §§21--22], and the paid
retention/completion boundaries [OWGR, §§20--21] and
[FEA, Definitions 16.2 and 18.3]. The stopped, actual-label,
full-history finite-window relation and its generated finite
certificate are a repo-derived composite of those suppliers.
These are conditional mathematical statements in prose, with no
fresh Lean verification or independently checked worldwide
novelty claim.

[OWGR]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_WORD_GEOMETRY_RECOVERY.md
[DPCR]: RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md
[SRO]: RECURSIVE_RELATIONAL_OBSERVATION_SOURCE_RELATIVE_ORDER.md
[FEA]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_FINITE_ENERGY_ACQUISITION.md

## 追加锚（本行以下为增补区）

## 9. Effective original-source contact certificates at every later cut

**Definition 9.1 (the retained source, complete future and gate).**
Retain Assumption 1.1 and Definitions 6.1 and 7.1 in full, for every
original finite $a,\eta,d>0$ and every permitted repaired Borel
emission. In particular the group, unit-source normalization,
complete complex non-Friedrichs endpoint, operator and form domains,
source trace, $e$-start, first read at $2d$, subsequent gaps $d$,
four labels and fresh conditional noise are unchanged. Write
$P_t=T_t$, so that the discrete operator remains $P=P_d$.
Use exactly the properly associated conservative process of
[CONTACT, Theorem 116.3][CONTACT], with its properly exceptional
set $\mathcal N$ satisfying $e\notin\mathcal N$; $m(\mathcal N)=0$.
Its contact time is $\tau_e=\inf\{s\ge0:Z_s=e\}$.
Contact is an analytic stopping time of this process, not a
detectable label, sensor, available Return or operation on the source.

On $\Omega=\mathcal L^{\mathbb N}$ use the whole product sigma algebra
$\mathscr Y=\bigotimes_{n\ge0}2^{\mathcal L}$. For a word $v$ let
$[v]$ be its initial cylinder. Reuse the common future kernel
$\mathcal K(x,E)$ of [OWGR, Definition 15.1]: it starts at the
next hidden read state $x$, emits with the original $f_y$, then
repeats $P_d$ and the original independent conditional noise.
It is a probability kernel on all of $\mathscr Y$, with
$\mathcal K(x,[v])=F_v(x)$ as $m$-classes. For every history $u$
put

$$
\begin{gathered}
R_u^\infty(E)=\int_G\pi_u(x)\mathcal K(x,E)m(dx),\qquad
Q_\emptyset^\infty(E)=\int_G\mathcal K(x,E)m(dx),\\
R_u^\infty([v])=\frac{p(uv)}{p(u)},\qquad
Q_\emptyset^\infty([v])=q(v),\\
Q_w^\infty(E)=
 \frac{Q_\emptyset^\infty([w]\cap\theta^{-|w|}E)}{q(w)},\qquad
R_t^\infty=R_{Y_{<t}}^\infty .
\end{gathered}
\tag{9.1}
$$

Here $\theta$ is the left shift and $\pi_u$ is the actual next-read
posterior of (2.2), conditioned on the entire history $u$.
All $p(u),q(u)>0$ by Definition 6.1, so every finite conditioning
in (9.1) is defined. Cylinder uniqueness extends the identities
from (2.2) to the full product law. The superscript $H$ below
denotes the marginal on the first $H$ future labels, agreeing with
(6.1)--(6.3). The comparison $Q_\emptyset^\infty$ is mathematical;
it supplies no stationary specimen preparation or exact-law query.

Fix deterministic integers $S\ge0$ and $k\ge2$. Take precisely the
disjoint-block gate (6.2) with $L=2k$:

$$
\begin{gathered}
U_i=S+(i-1)2k,\qquad
C_i=\{Y_{[U_i,U_i+2k)}=B^{2k}\},\\
J=\inf\{i\ge1:C_i\},\qquad T=S+2kJ,\qquad
W_j=Y_{[T,T+j)}\quad(j\ge0).
\end{gathered}
\tag{9.2}
$$

In particular $W_0=\emptyset$. The cut $T+j$ remains immediately
before the read at physical time $(T+j+2)d$.

**Theorem 9.2 (contact envelope and one complete-future event for all
later actual cuts).** For every source and deterministic $S,k$ of
Definition 9.1, every $M\ge\|g_d\|_\infty$ and every $\epsilon>0$,
let $d_\lambda$ be the original defect of [DPCR, Definition 9.1]
and put

$$
\eta_k=M\left[
 \frac{1-d_{1/(kd)}}{1-\exp(-1)}
 +\frac12\sqrt{
       \frac{1-d_{1/[2(k-1)d]}}{d_{1/[2(k-1)d]}}}\right].
\tag{9.3}
$$

Then $T<\infty$ almost surely and

$$
\mathbb E_e\operatorname{TV}(\pi_{Y_{<T}}m,m)\le\eta_k,
\tag{9.4}
$$

where $\operatorname{TV}(\pi m,m)=\tfrac12\int|\pi-1|\,dm$.
On the full product sigma algebra of (9.1),

$$
\mathbb P_e\left\{
 \sup_{j\ge0}\operatorname{TV}
       (R_{T+j}^\infty,Q_{W_j}^\infty)>\epsilon\right\}
 \le\min\{1,2\eta_k/\epsilon\}.
\tag{9.5}
$$

On the complement of the failure event in (9.5),
$\operatorname{TV}({\bf R}_{T+j}^H,Q_{W_j}^H)\le\epsilon$
holds for every integer $j\ge0$ and every finite $H\ge1$ simultaneously.
This is an unconditional event in the original law, not a bound
conditional on each reached history, gate index, calibration
output or selected branch.

*Proof.* First obtain an original-clock transition estimate using
the actual contact law. Since $g_d$ is a nonnegative probability
density, $\|g_d\|_\infty\ge1$. Thus $u=g_d-1$ has mean zero and
$\|u\|_\infty\le M$. For every $t\ge kd$, propagation and
$L^2$ contraction, followed by [DPCR, Theorem 9.2, (9.3)], give

$$
\begin{aligned}
\operatorname{TV}(g_t m,m)
 &\le\frac12\|g_t-1\|_2
 \le\frac12\|P_{(k-1)d}u\|_2\\
 &=\frac12\sqrt{\langle u,P_{2(k-1)d}u\rangle_m}\\
 &\le\frac M2\sqrt{\Theta(1/[2(k-1)d])}
 =:\gamma_k .
\end{aligned}
\tag{9.6}
$$

The offset is $k-1$, because the positive-time density used at the
start of this estimate is $g_d$. No zero-time density or numerical
physical time name is assumed.

For legitimate starting points $x$ put
$a_k(x)=\mathbb P_x(\tau_e>kd)=P_{kd}^01(x)$, using the killed
transition version of [CONTACT, (116.9)] and any Borel extension
on the exceptional null set. The hitting transform and its integral in
[CONTACT, (116.9), (116.14)] imply

$$
\begin{aligned}
(1-\exp(-1))\int a_k\,dm
 &\le\int_G\mathbb E_x[1-\exp(-\tau_e/(kd))]m(dx)\\
 &=1-d_{1/(kd)}.
\end{aligned}
\tag{9.7}
$$

For this inequality $\exp(-\infty)=0$; it also follows directly
on $\{\tau_e>kd\}$. The integral identity is precisely
$\int b_\lambda\,dm=d_\lambda$, with the original clock and
the full source trace. It is not the contact transform of a
different process with a similar differential expression.

At time $2kd$, split the transition from $x$ into
$\{\tau_e>kd\}$ and $\{\tau_e\le kd\}$. The first piece has mass
$a_k(x)$. By the strong Markov property, the second is a mixture
of source-start laws $g_{2kd-s}m$, $0\le s\le kd$.
Every such remaining time is at least $kd$ and satisfies (9.6).
Subtract the corresponding masses of $m$ from both pieces.
The first signed piece has TV at most $a_k(x)$; the second has
TV at most $\gamma_k(1-a_k(x))$. Therefore, for every probability
density $\pi$ relative to $m$,

$$
\begin{aligned}
\operatorname{TV}(P_{2kd}(x,\cdot),m)&\le a_k(x)+\gamma_k
                   \quad(x\notin\mathcal N),\\
\operatorname{TV}((P_{2kd}\pi)m,m)
 &\le \langle\pi,a_k\rangle_m+\gamma_k .
\end{aligned}
\tag{9.8}
$$

Symmetry identifies the propagated measure's density with
$P_{2kd}\pi$. The mixtures are Borel transition mixtures of the
properly associated process. TV can be taken over a countable
generating algebra of the standard Borel state space $G$, so its
kernel supremum is measurable. No observation of $\tau_e$ is
made. All posterior densities are absolutely continuous with
respect to $m$ and hence avoid $\mathcal N$.

We next average at the actual first successful block. Let
$b_L=4^{-L}$, $L=2k$, and
$E_{i-1}=\bigcap_{h<i}C_h^c$. For a prefix $u$ of length $U_i$
satisfying $E_{i-1}$, (2.5) gives exactly

$$
p(uB^L)=b_Lp(u),\qquad
\pi_{uB^L}=P^L\pi_u=P_{2kd}\pi_u .
\tag{9.9}
$$

These are full-history posteriors; the failed blocks and every
other preceding label remain in $u$. Theorem 2.1 identifies
$\langle\pi_{Y_{<U_i}},a_k\rangle_m$ with
$\mathbb E_e[a_k(X_{U_i})\mid\mathscr F_{U_i}]$.
Summing (9.8)--(9.9) over these prefixes yields

$$
\begin{aligned}
\mathbb E_e\operatorname{TV}(\pi_{Y_{<T}}m,m)
 &\le\sum_{i\ge1}b_L
       \mathbb E_e[\mathbf1_{E_{i-1}}a_k(X_{U_i})]
       +\gamma_k .
\end{aligned}
\tag{9.10}
$$

Here Proposition 6.6 supplies $J<\infty$ almost surely, so the
weights multiplying the constant $\gamma_k$ sum to one.
Conditional on the entire hidden path, each disjoint all-$B$
block has probability $b_L$, and their indicators are independent.
Thus the sum in (9.10) is

$$
\begin{aligned}
&\sum_{i\ge1}b_L(1-b_L)^{i-1}
       \int g_{(U_i+2)d}(x)a_k(x)m(dx)\\
&\hspace{2em}\le M\int a_k\,dm ,
\end{aligned}
\tag{9.11}
$$

because $\|g_{(U_i+2)d}\|_\infty\le\|g_d\|_\infty\le M$
and the geometric weights sum to one. Nonnegativity justifies the
countable sums. Equations (9.6)--(9.7) now prove (9.4).
Only the contact-tail integral in (9.11) uses this density bound;
$\gamma_k$ was integrated against probability measures in (9.8).
Consequently (9.3) has a single factor $M$, not a second density
factor multiplying its square-root term. No individual posterior
$\pi_u$ has been bounded by $M$.

For completeness, the passage to all later cuts uses a finite
measure on the entire future space, rather than a horizon-by-horizon
union bound. Fix one possible stopped history $u=Y_{<T}$. Put
$A=R_u^\infty$, $B=Q_\emptyset^\infty$ and
$e(u)=\operatorname{TV}(A,B)$. The common kernel in (9.1) contracts
TV on the full product sigma algebra, giving

$$
e(u)\le\operatorname{TV}(\pi_u m,m).
\tag{9.12}
$$

Let $\nu=|A-B|$ be the Jordan total-variation measure of the signed
measure $A-B$, so $\nu(\Omega)=2e(u)$. For a word $w$ of length
$j$, write $a_w=A([w])>0$, $b_w=B([w])>0$, and define the
conditional tail probabilities

$$
A_w(E)=A([w]\cap\theta^{-j}E)/a_w,\qquad
B_w(E)=B([w]\cap\theta^{-j}E)/b_w .
\tag{9.13}
$$

The map taking a sequence in $[w]$ to its tail is a measurable
bijection with measurable inverse (prefixing by $w$). Restrict
$A-B$ to $[w]$, normalize first by $a_w$, and then correct the
$B$ normalization from $a_w$ to $b_w$. The triangle inequality
for the total mass of a signed measure's variation gives

$$
\begin{aligned}
2\operatorname{TV}(A_w,B_w)
 &\le\frac{\nu([w])+|b_w-a_w|}{a_w}
 \le\frac{2\nu([w])}{a_w}.
\end{aligned}
\tag{9.14}
$$

The factor two on the left is valid because the two normalized
conditional measures have equal mass one. This derivation
does not assume absolute continuity between their infinite
future laws.

Under $A$, let $\omega_{<j}$ be the first $j$ future labels and set

$$
N_j(\omega)=\frac{\nu([\omega_{<j}])}
                       {A([\omega_{<j}])},\qquad N_0=2e(u).
\tag{9.15}
$$

This is a finite nonnegative martingale for the increasing
finite-prefix sigma algebras. Indeed, on $[w]$ its conditional
next-step expectation is

$$
\sum_{y\in\mathcal L}
 \frac{a_{wy}}{a_w}\frac{\nu([wy])}{a_{wy}}
 =\frac{\nu([w])}{a_w}.
\tag{9.16}
$$

All denominators are positive and the child cylinders partition
$[w]$. No Radon--Nikodym derivative on $\mathscr Y$ is needed:
the ratios in (9.15) are only at finite positive cylinders.
In particular positivity of cylinders is not being used to infer
absolute continuity of full product measures, which does not
follow from that positivity alone.

Ville's nonnegative-martingale maximal inequality, as stated by
Howard--Ramdas--McAuliffe--Sekhon in *Exponential line-crossing
inequalities* [VILLE, §2.3, Lemma 1, (18)][VILLE], and (9.14) imply

$$
A\left\{\sup_{j\ge0}
  \operatorname{TV}(A_{\omega_{<j}},B_{\omega_{<j}})
       >\epsilon\right\}
 \le\min\{1,2e(u)/\epsilon\}.
\tag{9.17}
$$

This use of Ville can also be obtained by stopping $N_j$ at its
first crossing of $\epsilon$ up to a finite index $n$:
nonnegativity and bounded stopping give crossing probability at
most $N_0/\epsilon$; increasing $n$ covers all $j$. The martingale
and its variation measure are mathematical proof objects, not
supplied numerical services.

The event in (9.17) is measurable on the full product. For any two
probabilities on $\Omega$, their event-TV is the supremum of their
finite-prefix TVs. This is the finite-alphabet specialization of
[THREAD, total_variation_eq_iSup_level][THREAD]: take levels
$\mathcal L^n$, truncation bonding maps and one thread.
The measurable identification with $\Omega$ preserves the product
sigma algebra. Equivalently, finite cylinder unions approximate
every product-measurable event in the sum of the two finite
measures. Thus every TV in (9.17) is a countable supremum of
finite sums of cylinder probabilities. The supremum over $j$
is countable too. There is no extension to a larger sigma algebra
or inference from convergence on each individual cylinder alone.

Given $\mathscr F_T$, the conditional law of the actual future is
$A=R_u^\infty$, and after its actual prefix $w=W_j$ its tail law
$A_w$ is precisely $R_{uw}^\infty=R_{T+j}^\infty$.
The comparison conditional is $B_w=Q_w^\infty$. The gate value
is already determined by $u$ and adds no future conditioning.
The countably many stopped histories therefore allow (9.17)
to be averaged in the original law. Using (9.12) and (9.4),

$$
\mathbb P_e\left\{\sup_{j\ge0}
 \operatorname{TV}(R_{T+j}^\infty,Q_{W_j}^\infty)>\epsilon\right\}
 \le\frac2\epsilon\,\mathbb E_e e(Y_{<T})
 \le\frac{2\eta_k}{\epsilon}.
\tag{9.18}
$$

The bound by one gives (9.5). Projection contracts TV and proves
the simultaneous assertion for every finite $H$. In particular
neither $H$ nor an advance expiry $r$ appears in this event.
$\square$

**Proposition 9.3 (a finite rational guard from earned bounds and
the fixed reference).** Let earned positive rationals $c_-,l$
satisfy $c_-\le c$ and $l\le\tau=a^2d/\eta$, and put
$M_0=1/(4c_-)$. Use only the paid fixed-reference defect service
at coefficients $1,1$ in [SRO, §§21--22] and (7.1).
For $k\ge2$ obtain rational lower enclosures and a rational $u\ge0$
such that

$$
\begin{gathered}
0<A^-\le D_k(l),\qquad 0<B^-\le D_{2(k-1)}(l),\qquad
A^-,B^-<1,\\
u^2\ge(1-B^-)/B^-,\qquad
\eta_k^+=M_0[\,2(1-A^-)+u/2\,].
\end{gathered}
\tag{9.19}
$$

Then (9.4)--(9.5) hold with $\eta_k$ replaced by $\eta_k^+$.
For any positive rational $\epsilon,\delta$, fair search over
$k$ and reference precision, with rational upper-square-root
refinement, terminates with

$$
2\eta_k^+<\epsilon\delta.
\tag{9.20}
$$

The resulting all-cut failure bound is strictly smaller than
$\delta$. The generated certificate is (9.19)--(9.20), not an
algorithm evaluating any of the complete future laws.

*Proof.* From the original calibration and (7.2),

$$
\begin{gathered}
\|g_d\|_\infty=\frac1{4c}-1\le M_0,\qquad
d_{1/(kd)}=D_k(\tau)\ge A^-,\\
d_{1/[2(k-1)d]}=D_{2(k-1)}(\tau)\ge B^- .
\end{gathered}
\tag{9.21}
$$

The function $(1-x)/x$ decreases on $(0,1]$ and
$(1-\exp(-1))^{-1}<2$. Apply Theorem 9.2 with $M=M_0$:
its $\eta_k$ is at most the rational expression $\eta_k^+$.
This proves sufficiency, including the strict failure assertion
under (9.20).

Here is a finite search using exactly the authorized names.
For each integer $k\ge2$ and precision index $s\ge1$, request
certified rational intervals of width tending to zero with $s$
for $D_k(l)$ and $D_{2(k-1)}(l)$. These are the total
[DPCR, (11.30)] reference calls described in
[SRO, (SRO.150)--(SRO.151)], at rational discounts $1/(kl)$
and $1/[2(k-1)l]$. If either lower endpoint is nonpositive,
this pair $(k,s)$ is inconclusive. Otherwise lower it, if necessary,
to at most $1-2^{-s}$ to obtain $A^-,B^-$ in (9.19).
For each fixed $k$, these lower enclosures converge to the strictly
positive values $D_k(l),D_{2(k-1)}(l)$ and remain below one.

For the rational $x=(1-B^-)/B^-\ge0$, rational bisection on
$[0,1+x]$, comparing squares to $x$, gives a rational upper
endpoint $u$ with
$0\le u-\sqrt x\le2^{-s}$ after finitely many comparisons.
The initial interval is valid since $(1+x)^2\ge x$.
Thus every tested pair uses finitely many reference operations
and rational operations. Enumerating the pairs in increasing
$k+s$ is fair and never waits for an equality test to resolve.

For fixed $k$, the values $\eta_k^+$ along increasing precision
converge to

$$
M_0\left[2(1-D_k(l))+
 \frac12\sqrt{\frac{1-D_{2(k-1)}(l)}{D_{2(k-1)}(l)}}\right].
\tag{9.22}
$$

By (7.2), this expression tends to zero as $k\to\infty$.
Choose a finite $k$ for which twice (9.22) is strictly below
$\epsilon\delta$, and then a finite precision preserving that
strict slack. Fair search reaches such a pair and terminates.
This uses no numerical name of the physical $a,\eta,d$.
In particular [DPCR, Theorem 12.4] cannot be called at those
unknown coefficients: its total coefficient/time names remain
required there. The selected route needs no global heat-norm
call, even at the reference; the original centered heat bound
and the two paid reference defects suffice. $\square$

**Corollary 9.4 (selection on one event and the conditional
actual-current consumer).** Predeclare a countable effectively
enumerated family of deterministic descriptions $\kappa$,
specifying positive rational $c_\kappa,l_\kappa,
\epsilon_\kappa,\delta_\kappa$ and integer $S_\kappa\ge0$.
Let $\sum_\kappa\delta_\kappa<\infty$. Generate a deterministic
$k_\kappa$ and guard (9.19)--(9.20) from each description.
Use the inherited predeclared acquisition packets and their
common event $\mathcal A_\tau$ of probability at least $1-\alpha$,
as in Theorem 8.1 and [SRO, Theorem 22.1]. On this event,
each selected description has earned
$c_\kappa\le c$ and $l_\kappa\le\tau$; every row/certificate
actually supplied by those packets retains its original finite
domain and validity.

There is an original-law event $\mathcal G$ with

$$
\mathbb P_e(\mathcal G)\ge1-\alpha-\sum_\kappa\delta_\kappa
\tag{9.23}
$$

on which every selected description obeys the dynamic comparison
of Theorem 9.2 at every later integer cut and every finite horizon.
Suppose a lawful executor for one such description actually
completes at a finite causal cut $C\ge T_\kappa$, retains and
processes every actual label through $C$, and genuinely supplies
a probability row $\rho_C$ at a finite horizon $H$ with a
same-event generated error certificate

$$
\operatorname{TV}(\rho_C,Q_{W_{\kappa,C-T_\kappa}}^H)
 \le\zeta_C+\xi_C .
\tag{9.24}
$$

Here $\zeta_C,\xi_C\ge0$ include the acquired row error and all
additional update, rounding and output error, respectively.
On $\mathcal G$, wherever these executor conditions hold,

$$
\operatorname{TV}({\bf R}_C^H,\rho_C)
 \le\epsilon_\kappa+\zeta_C+\xi_C .
\tag{9.25}
$$

An extra row supplier with its own confidence event must have
that event included in $\mathcal A_\tau$ and its failure charged
to $\alpha$; (9.24) is not automatically a new acquired row.

*Proof.* Fix the original source only for the analysis. For each
deterministic description with $c_\kappa\le c,l_\kappa\le\tau$,
Theorem 9.2 and Proposition 9.3 give an unconditional dynamic
event $\mathcal D_\kappa$, with failure less than
$\delta_\kappa$, covering all $j$ and $H$. Define

$$
\mathcal G=\mathcal A_\tau\cap
 \bigcap_{\kappa:\ c_\kappa\le c,\ l_\kappa\le\tau}
                  \mathcal D_\kappa .
\tag{9.26}
$$

The intersection is over the deterministic valid descriptions,
not a random list after calibration. A countable union bound
proves (9.23); the intersection of their almost-sure finite-gate
events costs no probability. On $\mathcal A_\tau$ every selected
description belongs to this intersection. No independence of
calibration, gates, row acquisition or branch selection is used.
Data-selected integer starts and rational tolerances are handled
by their predeclared descriptions, as in Theorem 8.1, not by
substituting random values into a deterministic probability bound.
There is no further union budget over $j$ or $H$.

On $\mathcal G$, substitute the actual finite index
$j=C-T_\kappa$ into its pathwise all-cut event, project to $H$,
and apply the triangle inequality with (9.24).
This proves (9.25), including selection of a horizon from an
actually available certified menu. Causality and actual availability
are executor premises, not consequences of this substitution.
If an executor never completes, this argument supplies no row
and makes no finiteness claim about its completion. $\square$

**Definition 9.5 (paid domain, execution boundary and recovery
scope).** The dynamic comparison in Definition 8.4 can now use
(9.25) without its advance restriction $C\le T+r$. This removes
only that restriction from analytic comparison validity.
The acquired catalogue of Proposition 7.3 still has exactly its
finite domain $\bigcup_{j=0}^r\mathcal L^j$ and finite horizons.
An actual suffix $W_{C-T}$ can exceed every acquired catalogue.
Neither (9.5) nor a short description of a mathematical law
supplies its numerical row, the legality of a new query, a
generated error certificate for it, or its completed output.

The guard alone uses two fixed-reference defect enclosures per
tested $k$ and precision, rational upper-square-root refinement,
integer search and exact rational comparisons. Charge every
reached call, refinement, failed or inconclusive test, rational
bit width and working bit. This guard does not enumerate
$4^{H+r}$ words; all existing word acquisition, counting,
normalization, row and certificate work remains charged under
Definition 8.3. No measured speed advantage, numerical runtime
bound or finite expected total work follows.

For a fixed deterministic description its source waiting bill,
by Proposition 6.6, is

$$
\mathbb E_e(T-S)=2k\,4^{2k},\qquad
\mathbb P_e(T-S>2kn)=(1-4^{-2k})^n\quad(n\ge0).
\tag{9.27}
$$

There is no finite worst-case gate bound. This expectation is
not transferred to a data-selected description. The rational
guard search is finite at every positive rational branch input,
and each fixed gate is almost surely finite. These facts do not
establish a finite actual end-to-end executor completion, a
capture/write service or a processor that catches up.

A retained archive through $C$ contains all $C$ actual labels,
hence $2C$ payload bits in the inherited coding, plus addresses,
gate registers, counters, reference descriptions and replies,
precision data and working storage. Preserve all previously
acquired rows, permissions, legal menus and records. Count shared
backing once and every distinct buffer, queue and copy.
All arrivals during reference computation, row updates and output
are included through the actual completion cut $C$; output for
an earlier cut is not relabelled as current. Storage, write
bandwidth, buffering, arithmetic, reference work, rescan work
and elapsed completion latency remain separate paid coordinates.
No bounded storage, installed throughput, deadline, atomic output,
or accepted pointer/backing interface is supplied. Actual
serialization of requested entries, or an already accepted backed
representation with its full contract, remains required.

The unpaid executor bridges are lossless capture during all work,
assimilation of the entire growing suffix, an actually available
current row and generated accumulated error, lawful output, and
finite actual completion. The contact time used in the proof
does not add point detection, reset, source delay, control,
extra read, physical Return or a new specimen. Exact filtering,
the hidden current point, original space and endpoint recovery,
and physical clock/parameter identification remain outside this
certificate. The event gives high-probability approximate
future comparison; it gives neither exact all-law recovery nor
an effective complete-future-law service.

The original unbounded finite ordered native $\alpha/\beta$ trees,
actual $\rho$ replacements, literal root/address reads, acquired
rows and service rights retain their own domains. The later
access and actual $S$-to-$C$ assimilation exclusions of
[NCO, Definition 10.6][NCO] remain. No native/diffusion/AURIC
identification is supplied. Any AURIC correspondence still owes
the same $E$, positive evaluations, accurate cone, A1--A3, every
P2/PB and original domain; a preselected bottom space or standard
matrix example does not supply the original native source.
Mutual recovery and minimality of space, lawful continuation,
boundary and memory therefore retain these distinct gaps.

**Definition 9.6 (source correspondence and attribution).**
The analytic contact and clock inputs are
[CONTACT, Theorems 116.3--116.4, (116.8)--(116.14)] for this
properly associated process, and its positive-time source law
[CONTACT, Theorem 117.2, (117.2)--(117.3)].
The full-versus-killed domain distinction (116.11) is retained:
the hitting argument uses the full non-Friedrichs process, whose
killed part is the original Friedrichs operator, not a replacement
full source. [DPCR, Definition 9.1 and Theorem 9.2] supplies the
defect and centered heat estimate in (9.6). The actual posterior
and B updates are (2.2)--(2.5); stopped weighting and waiting use
§6 without changing its full-history meaning.

The complete product future kernel and static tail/past distinction
are [OWGR, Definitions 15.1 and Proposition 16.3]; its Theorem 5.2,
(5.2)--(5.3), transports the entire endpoint, source, domains
and clock used in (9.21).
[SRO, Definition 21.1 and Theorem 22.1,
(SRO.150)--(SRO.151)] authorizes only the paid fixed-reference
calls and the common-event branch argument; [DPCR, (11.30)]
supplies their certified defects. [DPCR, Definition 12.1 and
Theorem 12.4] retains its stronger total-name requirements.
No unknown-source heat evaluator has been inferred from an
abstract parameter name. The resource and actual-return boundaries
of [FEA, Definitions 16.2 and 18.3] persist.

Strong Markov conditioning, signed-measure variation, kernel
contraction, finite-prefix martingales, Ville's maximal inequality
[VILLE], rational interval arithmetic and countable union bounds
are established intermediates, not new general theorems here.
[THREAD] supplies the existing level/event-TV framework; citing
its statement does not assert a fresh application compiled in
Lean. The source-specific composition (9.3)--(9.5), its earned
finite guard (9.19)--(9.20), and the conditional consumer
(9.23)--(9.25) are repo-derived ordinary mathematical deductions.
They do not claim fresh Lean verification or worldwide novelty.

[CONTACT]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md
[THREAD]: ../../../D5/S3/Estimation/DataProcessing/InverseLimitEventTotalVariation.lean
[VILLE]: https://arxiv.org/html/1808.03204v5#S2.SS3
[NCO]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATION_ORDER_ACQUISITION.md

## 追加锚（本行以下为增补区）

## 10. Conditional original-source current-row supply from a generated one-gap dependence guard

§9 的全后续切面接触证书与固定参考服务生成的原始源一间隔依赖上界共同用于独立于后门标签串的有限实际完成。§9 的动态事件、原始源、门、行域以及全部资源与服务要求均保持适用。

**Definition 10.1 (one-gap coefficient and reference names).** Retain the source of Definition 9.1 and write

$$
\beta_d=\int_G \operatorname{TV}\bigl(P_d(x,\cdot),m\bigr)\,m(dx),
\qquad P_d=T_d,
\tag{10.1}
$$

where event-TV is normalized as
$\operatorname{TV}(\nu,\nu')=\sup_A|\nu(A)-\nu'(A)|$, equivalently one half of the $L^1$ distance when both measures have densities. This is a source property, not a new label query.

Use the full-domain scaling of [OWGR, Theorem 5.2, (5.2)--(5.3)], in the invariant-time form of [FEA, Theorem 2.1], to identify the actual source with the coefficient-one reference source at

$$
\tau=\frac{a^2d}{\eta}.
\tag{10.2}
$$

Reference quantities carry a superscript ${\rm ref}$: $m_{\rm ref}$, $T^{\rm ref}_t$, $P^{\rm ref}_t=T^{\rm ref}_t$, the contact defect $d^{\rm ref}_r$ of [DPCR, Definition 9.1], the normalized zero state $h_{\rm ref}$, and the raw source density

$$
v^{\rm ref}_t=h_{\rm ref}g^{\rm ref}_t .
\tag{10.3}
$$

The same scaling transports the complete endpoint, form, source trace, clock and invariant measure. In particular the row-TV integral (10.1) equals the reference row-TV integral at time $\tau$. Let $0<l\le\tau$ be an earned rational lower clock bound. A fixed-reference computation is allowed to return rational numbers $A^-$ and $s^+$ satisfying

$$
0<A^-\le d^{\rm ref}_{2/l},
\qquad
s^+\ge\bigl\|v^{\rm ref}_{l/2}-h_{\rm ref}\bigr\|_{L^2(\mu_{\rm ref})}.
\tag{10.4}
$$

The calls producing (10.4) use only the known reference coefficients $(1,1)$, the global raw $L^2$ names and the positive rational time $l/2$ supplied by [DPCR, Theorems 11.4, 12.3 and 12.4]. They do not query the unknown actual $a,\eta,d$. Define the generated guard

$$
b^+(A^-,s^+)=2(1-A^-)+\frac{s^+}{2}.
\tag{10.5}
$$

**Theorem 10.2 (contact-to-one-gap dependence bound).** Under Definitions 9.1 and 10.1, every original source for which the earned inequalities $0<l\le\tau$ and (10.4) hold satisfies

$$
\beta_d\le b^+(A^-,s^+).
\tag{10.6}
$$

*Proof.* Work first in the coefficient-one reference source. Let $\sigma=\tau_e$ be the contact time with the original endpoint. The contact identity [CONTACT, (116.14)], used with the full non-Friedrichs process exactly as in (9.7), gives

$$
\int_G\mathbb E_x\!\left[1-\exp\!\left(-\frac{2\sigma}{l}\right)\right]m_{\rm ref}(dx)
 =1-d^{\rm ref}_{2/l}.
\tag{10.7}
$$

On $\{\sigma>l/2\}$, the integrand on the left is at least $1-e^{-1}$. Hence

$$
\int_G\mathbb P_x(\sigma>l/2)m_{\rm ref}(dx)
 \le \frac{1-d^{\rm ref}_{2/l}}{1-e^{-1}}
 <2(1-d^{\rm ref}_{2/l})
 \le2(1-A^-).
\tag{10.8}
$$

Fix $x$. Split the transition law at time $\tau$ according to $\{\sigma>l/2\}$ and $\{\sigma\le l/2\}$. The first subprobability has mass $r_x=\mathbb P_x(\sigma>l/2)$, and its distance from the subprobability $r_xm_{\rm ref}$ is at most $r_x$. On the second event, the strong Markov property gives a mixture, over contact times $s\le l/2$, of the source-start laws

$$
g^{\rm ref}_{\tau-s}m_{\rm ref},
\qquad \tau-s\ge l/2.
\tag{10.9}
$$

For every $t\ge l/2$, the raw density relation (10.3), $\|h_{\rm ref}\|_{L^2(\mu_{\rm ref})}=1$, and Cauchy--Schwarz give

$$
\begin{aligned}
\operatorname{TV}(g^{\rm ref}_tm_{\rm ref},m_{\rm ref})
 &=\frac12\int |v^{\rm ref}_t-h_{\rm ref}|h_{\rm ref}\,d\mu_{\rm ref}\\
 &\le\frac12\|v^{\rm ref}_t-h_{\rm ref}\|_{L^2(\mu_{\rm ref})}.
\end{aligned}
\tag{10.10}
$$

The source semigroup identity $g_{t+s}^{\rm ref}=T_s^{\rm ref}g_t^{\rm ref}$ and $T_s^{\rm ref}1=1$ show, for $t\ge l/2$,

$$
\|v^{\rm ref}_t-h_{\rm ref}\|_{L^2(\mu_{\rm ref})}
\le \|v^{\rm ref}_{l/2}-h_{\rm ref}\|_{L^2(\mu_{\rm ref})}
\le s^+.
\tag{10.11}
$$

Thus the hit subprobability differs from its equal-mass copy of $m_{\rm ref}$ by at most $s^+/2$. Adding the two subprobability comparisons gives, for every $x$,

$$
\operatorname{TV}\bigl(P^{\rm ref}_\tau(x,\cdot),m_{\rm ref}\bigr)
\le r_x+\frac{s^+}{2}.
\tag{10.12}
$$

Integrate (10.12), use (10.8), and then use (10.2) and the scaling correspondence. This is (10.6). The contact time is used only as a proof stopping time; no label, point sensor, reset, source delay or physical Return is introduced. $\square$

**Proposition 10.3 (cofinal finite rational guards from the reference).** For every rational target $\theta>0$, a finite search over positive integer reference times $L$ and reference precisions can return rational $A^-,s^+$ with $l=L$ and

$$
b^+(A^-,s^+)<\theta.
\tag{10.13}
$$

Consequently the passing sources form a nonempty cofinal class in the earned lower-clock coordinate: a source passes the guard whenever it earns $L\le\tau$ and the strict inequalities in (10.4) and (10.13) are certified. This does not say that a fixed source passes every requested $\theta$, and it never enlarges the actual read gap $d$.

*Proof.* The reference defect satisfies $d^{\rm ref}_r\to1$ as $r\downarrow0$ by [DPCR, Definition 9.1]. Also, by the exact source-vector representation in [DPCR, Theorem 12.3],

$$
v^{\rm ref}_t=(H_{\rm ref}+1)e^{-tH_{\rm ref}}z_{\rm ref}.
\tag{10.14}
$$

The normalized source law has $\langle h_{\rm ref},v^{\rm ref}_t\rangle=1$, while $\ker H_{\rm ref}=\mathbb C h_{\rm ref}$. The spectral theorem therefore gives $v^{\rm ref}_t\to h_{\rm ref}$ in global $L^2(\mu_{\rm ref})$: on the zero eigenspace the projection is exactly $h_{\rm ref}$, and on its orthogonal complement the multiplier $(\lambda+1)e^{-t\lambda}$ tends to zero and is uniformly bounded, so dominated convergence applies to the spectral measure of $z_{\rm ref}$.

It follows that

$$
2(1-d^{\rm ref}_{2/L})
 +\frac12\|v^{\rm ref}_{L/2}-h_{\rm ref}\|_2\longrightarrow0
\qquad(L\to\infty).
\tag{10.15}
$$

Choose a finite $L$ for which (10.15) has strict margin below $\theta$. The fixed-reference services produce certified intervals of arbitrarily small width for $d^{\rm ref}_{2/L}$ and the global vectors in (10.14). Refine until a positive lower endpoint $A^-$ and an upper norm bound $s^+$ preserve the strict margin. A fair enumeration of $L$ and precisions reaches this pair after finitely many calls. Every call, failed test, precision and rational operation is charged under the existing reference contract. $\square$

**Lemma 10.4 (stationary posterior transfer through one gap).** Let $Q_\emptyset$ be the stationary complete future law of Definition 9.1 and let $D_{j,H}(w)=\operatorname{TV}(Q_w^H,Q_\emptyset^H)$ for a word $w\in\mathcal L^j$. For every deterministic $j\ge0$ and $H\ge1$,

$$
\mathbb E_{Q_\emptyset}\bigl[D_{j,H}(W_j)\bigr]\le\beta_d.
\tag{10.16}
$$

*Proof.* Let $X$ be the hidden state at the cut before the one-gap transition, and let $\nu_w$ be its stationary conditional law given $W_j=w$. The next-read posterior is $\pi_w=\nu_wP_d$. The future-label kernel $\mathcal K_H$ of Definition 9.1 is a Markov kernel, so TV contraction gives

$$
D_{j,H}(w)
\le\operatorname{TV}(\pi_w,m).
\tag{10.17}
$$

Convexity of TV under the mixture $\pi_w=\int P_d(x,\cdot)\nu_w(dx)$ gives

$$
\operatorname{TV}(\pi_w,m)
\le\int_G\operatorname{TV}(P_d(x,\cdot),m)\,\nu_w(dx).
\tag{10.18}
$$

The posterior barycentre identity $\int\nu_wQ_\emptyset^j(dw)=m$ now yields (10.16) after integration. This argument keeps the one-gap transition and the original emission kernel; it does not identify two sources merely because their labels have the same alphabet. $\square$

**Theorem 10.5 (independent finite completion transfers the row).** Fix a deterministic gate description $\kappa$, its stopped cut $T_\kappa$, and a finite horizon $H_\kappa$. Let $J_\kappa\in\mathbb N_0\cup\{\infty\}$ be the actual serialization-completion index after that gate. Assume, as an explicit runtime premise, that conditional on $\mathcal F_{T_\kappa}$ and on all pre-gate service randomness or state carrying no source information beyond the stopped label history, $J_\kappa$ is independent of the entire post-gate label sequence. The independence includes the event $J_\kappa=\infty$; ordinary causality, independence of one service component, or conditioning on a successful Return does not imply it. Suppose the earned guard gives $\beta_d\le b^+_\kappa$, and OPPM9's gate estimate gives

$$
\mathbb E_e\operatorname{TV}(\pi_{Y_{<T_\kappa}}m,m)\le\eta^+_\kappa.
\tag{10.19}
$$

Then, for every $\chi_\kappa>0$,

$$
\mathbb P_e\!\left\{
J_\kappa<\infty\ \text{and}\ D_{J_\kappa,H_\kappa}(W_{J_\kappa})>\chi_\kappa
\right\}
\le\frac{b^+_\kappa+\eta^+_\kappa}{\chi_\kappa}.
\tag{10.20}
$$

*Proof.* Condition on a stopped history and the allowed pre-gate service state. By the independence premise, the conditional law of $J_\kappa$ is a fixed probability law on $\mathbb N_0\cup\{\infty\}$, independent of the future labels. Set the summand at $J_\kappa=\infty$ to zero. Under the stationary comparison, Lemma 10.4 bounds the expectation of each finite-index summand by $\beta_d$, hence also their mixture by $b^+_\kappa$.

For the actual future, Definition 9.1 and kernel contraction give, for the same stopped history $u$,

$$
\operatorname{TV}(R_u^\infty,Q_\emptyset^\infty)
\le\operatorname{TV}(\pi_um,m).
\tag{10.21}
$$

Any measurable function of the future labels bounded by one changes its conditional expectation by at most the right side of (10.21). Apply this to the mixture of the functions $D_{j,H_\kappa}(W_j)$ with the fixed completion law. Average over stopped histories and use (10.19). Thus

$$
\mathbb E_e\!\left[\mathbf1_{\{J_\kappa<\infty\}}
 D_{J_\kappa,H_\kappa}(W_{J_\kappa})\right]
\le b^+_\kappa+\eta^+_\kappa.
\tag{10.22}
$$

Markov's inequality proves (10.20). No probability of finite completion is inferred, and no completion index is selected after inspecting the post-gate suffix. $\square$

**Corollary 10.6 (one common event and the conditional current-row consumer).** Predeclare a countable family of deterministic descriptions $\kappa$. Each description fixes $H_\kappa\ge1$, rational $\chi_\kappa,\epsilon_\kappa,\delta_{{\rm row},\kappa},\delta_{{\rm dyn},\kappa}>0$, rational $c_{-,\kappa},l_\kappa>0$, an integer gate start $S_\kappa$, and the complete execution rule, including the possible completion index. The inherited paid acquisition event $\mathcal A_\tau$, with probability at least $1-\alpha$, includes the genuinely acquired normalized row $\rho_\kappa$ on its finite horizon and its readiness by the actual gate, with

$$
\operatorname{TV}(\rho_\kappa,Q_\emptyset^{H_\kappa})\le\zeta_\kappa.
\tag{10.23}
$$

Choose the allowances with $\sum_\kappa(\delta_{{\rm dyn},\kappa}+\delta_{{\rm row},\kappa})<\infty$. All row packets, records and readiness tests in (10.23) are existing lawful paid operations; their storage, precision and service costs are retained in $\mathcal A_\tau$. On $\mathcal A_\tau$, an eligible description has $c_{-,\kappa}\le c$ and $l_\kappa\le\tau$. Generate the OPPM9 rational guard $\eta^+_\kappa$ and the present guard $b^+_\kappa$, and retain only descriptions satisfying the strict tests

$$
b^+_\kappa+\eta^+_\kappa
 <\chi_\kappa\delta_{{\rm row},\kappa},
\qquad
2\eta^+_\kappa<\epsilon_\kappa\delta_{{\rm dyn},\kappa}.
\tag{10.24}
$$

For every deterministic source-valid description, include its dynamic event and its row event in one intersection. The resulting original-law event has probability at least

$$
1-\alpha-
\sum_\kappa\bigl(\delta_{{\rm dyn},\kappa}+\delta_{{\rm row},\kappa}\bigr).
\tag{10.25}
$$

On this event, suppose a selected executor actually completes at a finite causal cut $C=T_\kappa+J_\kappa$, has captured, retained and assimilated every original label through $C$, and emits a normalized row $\rho_{\rm out}$ with a genuinely generated additional error certificate $\operatorname{TV}(\rho_{\rm out},\rho_\kappa)\le\xi_{\rm actual}$. Then

$$
\begin{aligned}
\operatorname{TV}(Q_{W_{J_\kappa}}^{H_\kappa},\rho_{\rm out})
 &\le \chi_\kappa+\zeta_\kappa+\xi_{\rm actual},\\
\operatorname{TV}(R_C^{H_\kappa},\rho_{\rm out})
 &\le \epsilon_\kappa+\chi_\kappa+\zeta_\kappa+\xi_{\rm actual}.
\end{aligned}
\tag{10.26}
$$

*Proof.* The OPPM9 all-cut event has failure below $\delta_{{\rm dyn},\kappa}$ by the second inequality in (10.24). Theorem 10.5 and the first inequality give the row-event failure below $\delta_{{\rm row},\kappa}$. Countable union over the deterministic descriptions, together with $\mathcal A_\tau$, proves (10.25). The selected description was present before the suffix and therefore is covered by this intersection.

At a finite actual completion, the first inequality in (10.26) is the triangle inequality through (10.23) and the row event. The second is the triangle inequality through the OPPM9 dynamic comparison at the actual index $J_\kappa$. The hypotheses that every label through $C$ was captured, retained and assimilated, and that $\xi_{\rm actual}$ was generated, are conjunctive premises. An unprocessed archive, a retrospective row, or a service that never completes does not satisfy them. $\square$

**Definition 10.7 (paid boundary and remaining source obligations).** The new guard removes the additional suffix-indexed numerical-row acquisition only for the nonempty guarded class certified by (10.4), (10.13) and (10.24), and only under the independent-completion premise of Theorem 10.5. The row event is a joint original-law statement for the selected completion index; it is not conditioned on completion and is not a pathwise guarantee for every index $j$. It supplies no executor, throughput, buffer, write service, atomic output, accepted pointer interface, source delay, reset, clock, point sensor or completion probability. Every arriving label, the full growing suffix, all prior rows, permissions, menus, backing, copies, arithmetic, latency and output costs remain in force. Sources outside the guard, completion rules whose stopping law depends on later labels, and a finite row that is not ready at the actual gate remain unresolved. The native unbounded finite ordered $\alpha/\beta$ trees, actual $\rho$ replacements and literal root/address operations retain their own domains; no native/diffusion/AURIC identification is asserted. The full space/continuation/boundary/memory mutual-recovery objective therefore remains open beyond this conditional row-interface reduction.

**Definition 10.8 (source correspondence and attribution).** The contact identity and full-versus-killed distinction are [CONTACT, Theorems 116.3--116.4, (116.8)--(116.14), and Theorem 117.2]. The defect limit and exact rank-one resolvent are [DPCR, Definition 9.1 and Theorems 11.4, 12.3--12.4]. The source scaling, complete endpoint and original clock are [OWGR, Theorem 5.2, (5.2)--(5.3)]. OPPM9, Theorem 9.2 and Proposition 9.3 supply the stopped gate estimate and its rational $\eta^+$ guard.

The event-TV normalization agrees with the joint-versus-product total-variation definition of absolute regularity in McDonald, Shalizi and Schervish, [*Estimating beta-mixing coefficients*](https://arxiv.org/html/1109.5998v3), §2.1; their stationary-sample estimator is not used. Ornee and Sun, [*Sampling and Remote Estimation for the Ornstein--Uhlenbeck Process through Queues*](https://arxiv.org/html/1902.03552v4), assumes an Ornstein--Uhlenbeck source and an installed FCFS channel with iid service times; neither source nor service is transferred. Strong Markov conditioning, TV contraction and convexity, Cauchy--Schwarz, spectral dominated convergence, Markov's inequality and countable union bounds are mature intermediates. The contact-to-one-gap composition (10.6), the generated guard (10.13), and the independent-completion row transfer (10.20)--(10.26) are source-specific ordinary deductions and have no fresh Lean verification or worldwide novelty claim.

## 追加锚（本行以下为增补区）

## 11. Maximal single-read neutral recoding and B-mask-adapted current-row transfer

**Definition 11.1 (the same source and the single-read relation).** Retain
Assumption 1.1 and Definitions 1.2, 6.1, 9.1 and 10.1 in full. Thus the original
$G=H^1\times\mathbb R$, unit source, normalized $h$, complex endpoint
$A=\rho C$, full operator/form domains and source trace, conservative
$e$-start, lead-in $2d$, gap $d$, four strictly positive emissions,
original masses and fresh nondisturbing read noises are unchanged.
The stationary law $Q=Q_\emptyset^\infty$ is only the mathematical
comparison of (9.1). No stationary preparation is made.

For $A\subseteq\mathcal L$ put $f_A=\sum_{y\in A}f_y$.
Call $A$ neutral when $f_A$ is constant as an $m$-class. A deterministic
single-read recoding $\gamma:\mathcal L\to\mathcal A$ has finite
discrete image and is neutral when every inverse image of an output
event is neutral. This is a relation between the original emission
kernel and a recoding, not a new observation port. Put
$B(y)=\mathbf1_{\{y=B\}}$.

**Theorem 11.2 (the maximal deterministic single-read neutral quotient).**
For every original finite $a,\eta,d>0$ and every permitted Borel repair,
the neutral subsets are exactly

$$
\varnothing,\qquad\{B\},\qquad\{0,1,3\},\qquad\mathcal L.
\tag{11.1}
$$

Consequently a deterministic single-read recoding is neutral if and
only if $\gamma=\psi\circ B$ for some map $\psi$ on $\{0,1\}$.
In this precise order of deterministic single-read recodings, $B$ is
maximal, up to relabelling. Constant recodings are included.

*Proof.* Reuse the nonconstancy of $g_t$ at every positive time proved
in [OWGR, Theorem 5.3, proof of (5.8)–(5.11)]; no new nonconstancy
assertion is needed. Since $c>0$ and $[b]=g_d$, $f_3$ is nonconstant.
The actual emission identities (1.2) give

$$
f_A=\frac{\mathbf1_{\{B\in A\}}}{4}
 +\frac38\bigl(\mathbf1_{\{0\in A\}}+\mathbf1_{\{1\in A\}}\bigr)
 +\left[\mathbf1_{\{3\in A\}}
 -\frac{\mathbf1_{\{0\in A\}}+\mathbf1_{\{1\in A\}}}{2}\right]f_3.
\tag{11.2}
$$

Thus neutrality is equivalent to vanishing of the bracket. If $3$
is absent, both $0,1$ must be absent; if $3$ is present, both must
be present. Membership of $B$ is free. This proves (11.1).
Every fibre of a neutral recoding belongs to (11.1), so $0,1,3$
must have one common image. This gives $\psi$; the converse follows
from the same four subsets. These statements concern $m$-classes,
not pointwise values at a repaired null set. All actual sampled epochs
are positive and absolutely continuous with respect to $m$; the
stationary epochs have law $m$. A countable union of their null
exceptions is null. No emission at time zero is substituted. $\square$

**Definition 11.3 (full prefixes, allowed service state and timing).**
Fix a deterministic gate description as in §9 and write its stopped
cut as $T$. For a reached stopped history $u=Y_{<T}$, write

$$
W_j=Y_T\cdots Y_{T+j-1},\qquad
B_i=\mathbf1_{\{Y_{T+i}=B\}},\qquad W_0=\emptyset.
\tag{11.3}
$$

The actual hidden read at local index $i$ is still
$Z_{(T+i+2)d}$. Conditional on $u$, any allowed pre-gate service
state $V$ carries no additional information about the joint future
hidden trajectory and fresh emission noises. Conditional on $u,V=v$,
a service seed $R$ has a fixed law $\lambda_{u,v}$ independent of
that entire joint future. More precisely, with $\mathsf H,\mathsf E$
denoting that hidden trajectory and those fresh noises, require

$$
\mathop{\rm Law}(\mathsf H,\mathsf E\mid u,V=v)
 =\mathop{\rm Law}(\mathsf H,\mathsf E\mid u),\qquad
\mathop{\rm Law}(R,\mathsf H,\mathsf E\mid u,V=v)
 =\lambda_{u,v}\otimes\mathop{\rm Law}(\mathsf H,\mathsf E\mid u).
$$

A singleton seed is allowed. Standard Borel service spaces suffice
for these conditional kernels. Independent
future service choices may be represented by such a seed; its existence
does not grant an executable sampler, processor or source control.

A rule $J\in\mathbb N_0\cup\{\infty\}$ is B-mask adapted when,
for each $j<\infty$, $\{J=j\}$ belongs to
$\sigma(R,B_0,\ldots,B_{j-1})$, using the same rule at fixed $u,v$
in the actual and comparison laws. The $j=0$ event uses only $R$;
the infinite event is the complement of all finite events.
The rule is predeclared and causal on the actual label prefix.
Non-B label content is not an allowed timing input. This is an
explicit timing restriction, not a claim that all causal completion
rules satisfy it. Whenever it is an actual completion, its cut is
$C=T+J$; every label through that cut still belongs to the actual
record and must be captured, retained and assimilated.

Under $Q$, let $\widetilde X_i$ denote the stationary hidden read
states with transition $P_d$ and the original emissions. For $j\ge1$
and every full word $w\in\mathcal L^j$, define

$$
\nu_w=\mathop{\rm Law}_Q(\widetilde X_{j-1}\mid W_j=w),\qquad
r_d(x)=\operatorname{TV}(P_d(x,\cdot),m),\qquad
D_j^\infty(w)=\operatorname{TV}(Q_w^\infty,Q),\qquad D_0^\infty=0.
\tag{11.4}
$$

All word probabilities $q(w)$ are positive. The posterior $\nu_w$
conditions on every original label, not merely its mask. It is
absolutely continuous with respect to $m$, since
$q(w)\nu_w(A)\le Q(\widetilde X_{j-1}\in A)=m(A)$.
Use any Borel extension of $r_d\in[0,1]$ on the properly exceptional
null set of Definition 9.1. Measurability follows from a countable
generating algebra for $G$. Also $D_j^\infty$ is measurable: by §9
full-product event-TV is the supremum of its finite-prefix TVs.
Write $Q_\lambda$ for this stationary comparison with its independent
seed, and $p_j=Q_\lambda(J=j)$ at the fixed $u,v$.

**Theorem 11.4 (selected-cut stationary barycentre and complete-future
transfer).** For every B-mask-adapted rule of Definition 11.3, every
Borel $A\subseteq G$ and $j\ge1$,

$$
\mathbb E_{Q_\lambda}[\mathbf1_{\{J=j\}}\nu_{W_j}(A)]
   =p_jm(A).
\tag{11.5}
$$

In particular, summing measures over all finite positive indices gives
$m\,Q_\lambda(1\le J<\infty)$, without conditioning on completion.
The complete-future error satisfies

$$
\begin{aligned}
\mathbb E_{Q_\lambda}
 [\mathbf1_{\{J<\infty\}}D_J^\infty(W_J)]
 &\le\beta_d Q_\lambda(1\le J<\infty)\le\beta_d,\\
\mathbb E_e
 [\mathbf1_{\{J<\infty\}}D_J^\infty(W_J)]
 &\le\beta_d+\mathbb E_e\operatorname{TV}(\pi_{Y_{<T}}m,m).
\end{aligned}
\tag{11.6}
$$

The summand at infinity is defined to be zero; the event $J=\infty$
and its probability remain in the law. Therefore, under the earned
guards $\beta_d\le b^+$ and (10.19), for every $\chi>0$,

$$
\mathbb P_e\{J<\infty,\ D_J^\infty(W_J)>\chi\}
 \le\min\{1,(b^++\eta^+)/\chi\}.
\tag{11.7}
$$

One event controls all finite future horizons by marginalization.
There is no assertion of a finite packet containing an infinite row.

*Proof.* The source-to-mark binary relation is exactly $f_B(x)=1/4$.
Together with the original fresh conditional noises, it gives, for
any finite set of read indices and every mask pattern $b_1,\ldots,b_n$,

$$
\mathbb P(B_{i_1}=b_1,\ldots,B_{i_n}=b_n
       \mid\hbox{entire hidden trajectory})
 =\prod_{h=1}^n(1/4)^{b_h}(3/4)^{1-b_h}.
\tag{11.8}
$$

Thus the entire mask is iid Bernoulli$(1/4)$ and independent of the
entire hidden trajectory, by cylinder uniqueness. This is the same
source independence already used in Lemma 6.3 and Proposition 6.6,
not a second independence theorem. For two reads (11.8) is its binary
product; for three reads it is the exact finite triple lift on the
same hidden realization. It is a joint conditional identity, not a
product of separately attainable marginals. At a stopped $u$, fresh
future noises give that same identity conditional on $u$ and its
future hidden path. The allowed $V,R$ do not change it. Under the
stationary comparison, $(R,(B_i)_{i\ge0})$ is consequently independent
of $(\widetilde X_i)_{i\ge0}$.

For each finite $j$, mask adaptation gives a measurable function
$a_j:\{0,1\}^j\to[0,1]$, the probability over $\lambda_{u,v}$ of
$J=j$ for that mask prefix. Independence of $R$ from the whole
label and hidden sequence gives, for any bounded Borel $h$,

$$
\begin{aligned}
\mathbb E_{Q_\lambda}[\mathbf1_{\{J=j\}}\nu_{W_j}(h)]
 &=\sum_{w\in\mathcal L^j}q(w)a_j(B(w))\nu_w(h)\\
 &=\mathbb E_Q[a_j(B(W_j))h(\widetilde X_{j-1})]\\
 &=\mathbb E_{Q_\lambda}
       [\mathbf1_{\{J=j\}}h(\widetilde X_{j-1})]
 =p_j\int h\,dm.
\end{aligned}
\tag{11.9}
$$

The second equality is the full-prefix posterior tower identity;
the last uses (11.8) and stationarity at the deterministic index
$j-1$. Taking $h=\mathbf1_A$ proves (11.5). In particular the
posterior was never replaced by a mask-only posterior. Moreover,
on a finite $J=j$, conditioning additionally on the seed and this
completion event adds no information about the hidden state or future
beyond the full $W_j$: the event is already decided by its mask and
seed, and the independent seed itself adds no source information.
The same statement under the actual law uses the full prefix $uW_j$.

After the last consumed read there is exactly the original one-gap
transition. The next-read stationary posterior is $\nu_wP_d$;
$mP_d=m$. With the full future probability kernel $\mathcal K$ of
(9.1), the Markov/read contract and cylinder uniqueness give

$$
Q_w^\infty=(\nu_wP_d)\mathcal K,\qquad Q=m\mathcal K,\qquad
D_j^\infty(w)\le\operatorname{TV}(\nu_wP_d,m)
 \le\int r_d\,d\nu_w.
\tag{11.10}
$$

Contraction here acts on the whole product sigma algebra. It is not
an inference from convergence of individual cylinders. Integrate
(11.10) on $J=j$, use (11.9) with $h=r_d$, and sum nonnegative
terms over $j\ge1$. Since $\int r_d\,dm=\beta_d$, this proves
the first line of (11.6). No bounded stopping or uniform mixing
hypothesis is used, and no mass is divided by $Q_\lambda(J<\infty)$.

Finally fix an actual stopped history $u$ and allowed state $v$.
The actual next-read law is $\pi_um$, by (2.2)–(2.5); the stopping
gate is already determined by $u$. Apply the same future kernel and
independent seed law to $\pi_um$ and $m$. Product extension and TV
contraction give

$$
\operatorname{TV}(R_u^\infty\otimes\lambda_{u,v},
                  Q\otimes\lambda_{u,v})
 \le\operatorname{TV}(\pi_um,m).
\tag{11.11}
$$

On this common label-and-seed space,
$F=\mathbf1_{\{J<\infty\}}D_J^\infty(W_J)$ is measurable and
lies in $[0,1]$. Its expectation changes by at most (11.11).
The stationary estimate applies to each fixed $u,v$ with its own
seed law and causal rule. Average the resulting inequality over
actual stopped histories and allowed service states. There are only
countably many stopped words; regular conditional kernels handle
$V$. This proves the second line of (11.6). Theorem 9.2 and the
generated guard (9.19) give (10.19), while Theorem 10.2 gives
$\beta_d\le b^+$. Markov's inequality proves (11.7). $\square$

**Proposition 11.5 (a strict causal example on the actual labels).**
After any fixed gate use no extra seed and put

$$
J_B=\inf\{j\ge1:Y_{T+j-1}=B\}.
\tag{11.12}
$$

This B-mask-adapted index is finite almost surely and satisfies
(11.6)–(11.7), but is not independent of the entire post-gate label
sequence, even conditional on a stopped history.

*Proof.* The waiting law is precisely the already proved $L=1$
case of (6.18), applied to the fresh masks after the stopped history
using (11.8): its tail is $(3/4)^n$ and its mean is four labels.
The events $\{J_B=1\}$ and $\{Y_T=B\}$ coincide and have probability
$1/4$, so their joint probability is $1/4$, whereas independence
would give $1/16$. This refutes full-label independence, not the
source-to-mask independence. Theorem 11.4 applies. The index is a
mathematical function of actual labels; it installs no serializer,
executor or new physical Return. $\square$

**Corollary 11.6 (the unchanged finite-output contract with weaker timing).**
In Corollary 10.6 keep the predeclared countable descriptions, acquired
normalized finite rows, readiness by the actual gate, common acquisition
event, allowances, earned guards and both strict tests (10.24).
Replace only Theorem 10.5's full-label-independent completion premise
by Definition 11.3's B-mask-adapted rule and allowed service-state/seed
conditions. Then the common-event probability (10.25) and both
finite-output inequalities (10.26) hold for these rules. The row
comparison event may be taken to be $D_{J_\kappa}^\infty\le\chi_\kappa$
on finite completion, so its marginal comparison covers all finite
horizons simultaneously; an actual output still uses only its acquired,
ready finite horizon $H_\kappa$.

*Proof.* For each deterministic source-valid description, (11.7) and
the first strict test (10.24) give a row-event failure below
$\delta_{{\rm row},\kappa}$. Keep exactly §9's all-cut, all-future
dynamic event and the second test (10.24). Intersect these events over
the deterministic valid descriptions with $\mathcal A_\tau$. The
countable union bound gives (10.25), without independence of calibration,
acquisition or branch selection. The theorem applies to every allowed
stopped state of each predeclared rule before selection. At any actual
finite completion $C=T_\kappa+J_\kappa$, contract (11.7)'s successful
comparison to $H_\kappa$ and use the acquired row bound (10.23),
$\operatorname{TV}(\rho_{\rm out},\rho_\kappa)\le\xi_{\rm actual}$,
and §9's dynamic event. The two triangle inequalities are exactly
(10.26). Capture, retention and assimilation of every actual label
through $C$, actual normalized output, genuinely generated
$\xi_{\rm actual}$ and row readiness remain conjunctive premises.
The infinite-completion branch produces no row and is not removed
by conditioning. $\square$

**Definition 11.7 (retained source contracts and quantum consumers).**
The precise removed premise is independence of $J$ from the entire
post-gate label sequence in the row-transfer route of §10, for the
B-mask-adapted class only. The maximality in Theorem 11.2 concerns
only deterministic single-read recodings. It classifies neither all
neutral history codes nor all source-blind stopping rules, and gives
no optimal service or physical cost claim. Completion depending on
non-B content remains unpaid. Sources outside the earned guard are
not included by (11.7); Proposition 10.3 does not make every fixed
source pass every tolerance.

All of Definitions 8.3, 9.5 and 10.7's other requirements remain:
every arriving label through actual $C$, including arrivals during
reference work, arithmetic and serialization; the full growing suffix,
failed gates, prior rows, permissions, legal menus, backing and every
distinct copy; actual capture/write bandwidth, buffering, storage,
assimilation, bit widths, output work, throughput and completion latency.
A ready row and a finite label index supply neither catch-up nor an
atomic output or accepted pointer interface. The first-B rule proves
an actual-source timing relation, not finite execution of this bill.
No hidden point, exact $q$ query, gap enlargement, uniform spectral
gap, sensor, source delay, reset or preparation is introduced.

The original full $\Omega$ quantum-origin objective is retained.
In particular the static results [SC, §§126–134], [SF, §§98–107]
and [ZC, §§2–12] remain achieved conditional results on their own
original domains. Their entire source contracts, including [SC,
132.1–132.2], [SF, 105.1] and [ZC, §11], are jointly retained,
with all incorporated upstream quantifiers, rather than replaced
by this passive-source lemma. Their seven consumers still require:
(1) the same original Hilbert/observable correspondence, native and
full-word identities, parent/ready, controls and actual coherent
preparations; (2) original evaluations, all zero, unequal and
subnormalized masses, original events, actual complete Born menus,
fixed-support/full-$S$ and every already quantified intermediate cut;
(3) actual correlated joints, faithful commuting local legs, shared
orientation, multiplicities, copies and all correlated positive inputs;
(4) each whole typed arrow with its entire environment, every output,
failure, fine record and port and each still-legal future, legal
pre/postcomposition and every needed depth of actual recursive
same-source references, with CP and Kraus used only on their paid
domains; (5) complete instruments, acceptance, unit partitions and
mass conservation for TP, positive-mass normalization for updates,
true grouping/forgetting and the additional calibration for Lüders;
(6) every legal history, flag, ready state, failure, refusal, stop,
destruction, leak, record and future, genuine two-sided/inverse Return,
CountRead on the same whole post-read active input, and the original
normality, predual, additivity and convergence conditions for infinite
records; (7) actual domain-preserving dynamics and inverses, physical
clock/units, energy, generator domains, common instruments and the
same positive action scale. No new Born, CP or coherent-control law
is derived here. The actual old full-menu/menu-context binding,
whole-active-input CountRead/Return, native/diffusion/AURIC identity
and source preparations are still the specific bridges of [SC, §133],
not consequences of probability-law comparison.

**Definition 11.8 (intuition and mathematical attribution).** 普通白话是：
原来的四种标签里，只有“是不是B”这盏灯在任何隐藏状态下都以四分之一
点亮。把它分成三个时刻来看，三盏灯在同一条隐藏路径上仍按原噪声独立；
并没有另换一份世界。若要把一次读数改成完全不透露隐藏状态的确定性记号，
就不能再把另外三种颜色拆开。这只是单次读数的最大划分，不限制更长历史
能怎样编码。

现在允许完成时刻等到这盏灯亮，或按灯的历史和独立服务种子来决定。
首次B规则确实依赖标签，不能再声称整串独立；但它没有按隐藏状态挑选时刻。
每次仍必须保留另外三种颜色的全部实际内容：它们会改变那一次的后验，
不能当作没有看见。证明把这些完整后验按同一选择规则加回去，重心恰好
回到平稳比较分布。原来的一个时间间隔再把这个关系送到整个未来的概率律，
接上门后原源与比较源的误差。无限等待也留在账内，没有偷偷只挑成功。

这只省去一条过强的时间独立前提。它不让机器免费记住、写入、处理或输出
不断到来的标签；拿到一张有限行，也没有把无限未来装进那张表。二元灯关系、
三时刻共同实现和选择后的重心接到的是原被动源预测接口，尚不是具名量子
分析器、完整菜单或读后同一活动输入的真实返回；完整量子起源目标不变。

Conditional expectation/tower identities, probability-kernel TV
contraction and convexity, Markov's inequality and countable union
bounds are mature intermediates. The one-gap coefficient retains the
absolute-regularity convention and primary reference in Definition
10.8 (McDonald–Shalizi–Schervish, §2.1); no estimator or queue model
is transferred. Reused source-specific inputs are the original
emissions/posteriors (1.2), (2.2)–(2.5), the mask independence and
waiting proof in §6, [OWGR, Theorem 5.3]'s nonconstancy, §9's complete
future kernel and dynamic event, and §10's generated dependence
guard and acquired-row contract. The exact single-read quotient
(11.1), selected-cut identity (11.5) and their full-future completion
composition (11.6)–(11.7) are repo-derived ordinary paper deductions.
They are not fresh Lean verification, a strict global axiom-simplicity
or physical-dimension result, or a worldwide novelty claim.

[SC]: AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES_CONTINUATION.md
[SF]: AURIC_SEMIFINITE_ORIGINAL_RESPONSE_AND_CENTRAL_POLAR_GEOMETRY.md
[ZC]: AURIC_ZERO_DIMENSIONAL_CENTER_SQUARE_ORBIT_RECONSTRUCTION.md

## 追加锚（本行以下为增补区）

## 12. Original no-3 survival and full-label adaptive current-row separation

**Definition 12.1 (the same source and the two prediction laws).**
Fix any original finite $a,\eta,d>0$ and any permitted Borel repair
in Assumption 1.1. Retain its entire complex non-Friedrichs endpoint
$A=\rho C$, maximal operator domain, full form and source trace,
$G=H^1\times\mathbb R$, Haar measure, unit-source Green field,
normalized zero state $h$, $m=h^2\mu$, $K$, and $P=T_d=e^{-dK}$.
The actual source still starts at $e$, first reads at $2d$, and
thereafter reads at the fixed gap $d$, with all four original
emissions (1.2) and their conditionally fresh noise. In particular
$f_3=cb$, $[b]=g_d$, $q(3)=c>0$, and $0<f_3\le1/4$.

Write $Q=Q_\emptyset^\infty$, $Q_w=Q_w^\infty$ and $R_u=R_u^\infty$
for the complete laws of (9.1), and $W_j=Y_0\cdots Y_{j-1}$ on
their common output sequence space. Under $R_u$ these coordinates
are the continuation after the fixed original authentic history
$u$, rather than a new $e$-start. Then

$$
Q_{W_j}^1(3)=\frac{q(W_j3)}{q(W_j)},\qquad
R_{uW_j}^1(3)=\frac{p(uW_j3)}{p(uW_j)}.
\tag{12.1}
$$

The first expression uses a stationary initial comparison density
and the whole continuation prefix. The second uses the entire
actual history $uW_j$. They are not identified. Define

$$
\begin{gathered}
r=1-f_3,\quad s=\sqrt r,\quad
\mathsf A=M_sPM_s,\qquad
S_0=1,\quad
S_n=Q\{Y_0,\ldots,Y_{n-1}\ne3\}\quad(n\ge1),
\end{gathered}
\tag{12.2}
$$

where $M_s$ is multiplication by $s$. Stationarity and any two-sided
extension below are proof comparisons only, with no preparation,
additional trajectory, exact $q$ query or change in the source.

**Theorem 12.2 (source-specific survival edge and its three limits).**
For every source and repair of Definition 12.1,

$$
S_n=\langle s,\mathsf A^{n-1}s\rangle_m>0\quad(n\ge1),\qquad
S_n\longrightarrow0,\qquad
S_n^{1/n}\longrightarrow1,\qquad
\frac{S_{n+1}}{S_n}\longrightarrow1.
\tag{12.3}
$$

In particular the conditional next-3 probability after observing
only the event of $n$ consecutive non-3 labels tends to zero.
This event-conditioned probability is not the posterior after any
specified full word.

*Proof.* The original read product, summed over $\{0,1,B\}$ at
each position, gives
$S_n=\langle1,M_r(PM_r)^{n-1}1\rangle_m$.
Splitting the end multipliers into square roots gives (12.3)'s
first identity. Positivity also follows from $r\ge3/4$, which gives
$S_n\ge(3/4)^n$. The spectral theorem for the nonnegative $K$
shows $0\le P\le I$ in quadratic-form order. Thus $\mathsf A$ is
self-adjoint, $0\le\mathsf A\le I$, and positivity preserving.
For a nonzero $v\in L^2(m)$,

$$
\langle v,\mathsf A v\rangle_m
 \le\|sv\|_2^2
 =\|v\|_2^2-\int f_3|v|^2\,dm<\|v\|_2^2.
\tag{12.4}
$$

Strictness uses $f_3>0$ almost everywhere, not a positive uniform
lower bound. Hence $1$ is not an eigenvalue of $\mathsf A$.
If $\sigma_s$ is its scalar spectral measure at $s$, then

$$
S_n=\int_{[0,1]}\lambda^{n-1}\,d\sigma_s(\lambda),\qquad
\sigma_s(\{1\})=0.
\tag{12.5}
$$

Dominated convergence already proves $S_n\to0$.

We prove that the upper support edge in (12.5) is exactly $1$
from the original source inputs. Use the original group dilations
$\delta_R(x,y,z,w)=(Rx,Ry,Rz,R^2w)$, whose Haar Jacobian is $R^5$.
Choose nonnegative $\chi\in C_c^\infty(G\setminus\{e\})$, with
$\|\chi\|_{L^2(\mu)}=1$, supported in a fixed annulus
$1<\varrho<2$ for the gauge of [DPCR, Definition 14.1]. Set

$$
\phi_R(p)=R^{-5/2}\chi(\delta_{1/R}p),\qquad v_R=\phi_R/h.
\tag{12.6}
$$

The positive smooth $h$ on punctured compact sets makes $v_R$ a
nonnegative bounded smooth punctured test with $\|v_R\|_{L^2(m)}=1$.
The exact full-domain correspondence [CONTACT, Theorem 115.3,
(115.15)–(115.18)] puts it in the actual form domain and gives

$$
\begin{aligned}
0\le\mathscr E[v_R]=q_H[\phi_R]
 &=aR^{-2}\sum_{i=1}^3\|X_i\chi\|_{L^2(\mu)}^2
   +\eta R^{-4}\|\partial_w\chi\|_{L^2(\mu)}^2\\
 &\quad-16\sqrt{a\eta}\,R^{-3}
                  \int\Gamma|\chi|^2\,d\mu
 \le C_1R^{-2}+C_2R^{-4}.
\end{aligned}
\tag{12.7}
$$

Here $X_1=\partial_x$, $X_2=\partial_y+x\partial_w$,
$X_3=\partial_z$, and $\Gamma$ has its original degree $-3$.
All integrals in this calculation have compact support away from
the source. The nonnegative lower bound is that of the actual
$H$, not a replacement by its Friedrichs extension. The constants
$C_1,C_2$ depend on the fixed source and $\chi$.

[DPCR, Theorem 14.3] gives
$\epsilon_R:=\operatorname{ess\,sup}_{\operatorname{supp}\phi_R}f_3
\to0$ as $R\to\infty$. The spectral inequality
$1-e^{-d\lambda}\le d\lambda$ and
$0\le1-s=f_3/(1+s)\le f_3$ therefore give

$$
\begin{aligned}
\langle v_R,Pv_R\rangle_m&\ge1-d\mathscr E[v_R],\\
\langle v_R,\mathsf A v_R\rangle_m
 &\ge\langle v_R,Pv_R\rangle_m-2\|(1-s)v_R\|_2\\
 &\ge1-d(C_1R^{-2}+C_2R^{-4})-2\epsilon_R
 \longrightarrow1.
\end{aligned}
\tag{12.8}
$$

The second line follows by replacing the two occurrences of $v_R$
in the pairing with $sv_R$ one at a time, using the contraction
bounds for $P,M_s$. This proves the source-specific spectral edge;
no spectral hypothesis has been appended.

For completeness the edge must also be visible to the survival
vector $s$. For each fixed $R$, boundedness of $v_R$ and
$s\ge\sqrt{3}/2$ give a finite $C_R$ with $0\le v_R\le C_Rs$.
Positivity preservation of every integer power of $\mathsf A$
and the spectral Jensen inequality for the unit vector $v_R$ give,
for every integer $k\ge1$,

$$
C_R^2\langle s,\mathsf A^ks\rangle_m
 \ge\langle v_R,\mathsf A^kv_R\rangle_m
 \ge\langle v_R,\mathsf A v_R\rangle_m^k.
\tag{12.9}
$$

The last inequality is the ordinary scalar Jensen inequality for
$\lambda\mapsto\lambda^k$ on $[0,1]$. First taking $n$th roots
with $k=n-1$, then using (12.8), proves
$\liminf S_n^{1/n}\ge1$; the reverse bound is $S_n\le1$.
This also verifies the support-edge assertion directly without an
irreducibility assumption for a new killed continuous-time model.

Cauchy–Schwarz in (12.5) gives
$S_{n+1}^2\le S_nS_{n+2}$ for $n\ge1$. Thus
$S_{n+1}/S_n$ is increasing and at most one. If its limit were
less than one, the products of these ratios would force
$\limsup S_n^{1/n}<1$, contrary to the preceding limit.
Finally

$$
Q(Y_n=3\mid Y_0,\ldots,Y_{n-1}\ne3)
 =1-S_{n+1}/S_n\longrightarrow0.
\tag{12.10}
$$

The scalar spectral-measure argument is a mature intermediate:
compare Keller–Lenz–Vogt–Wojciechowski,
[*Note on basic features of large time behaviour of heat kernels*,
arXiv:1101.0373v2, Theorem 1.1(b) and Theorem 2.1][EDGE].
Their statements concern heat semigroups; the bounded-operator
moment calculation needed here was given explicitly in
(12.5), (12.9). Bounded spectral calculus and its dominated
convergence are as in Teschl, [*Mathematical Methods in Quantum
Mechanics*, §3.1, Theorem 3.1, (3.20)–(3.21)][SPCALC].
The source-specific input to the edge is (12.6)–(12.8).
All these integrals and exterior bounds are $m$-class statements.
For each permitted repair its exceptional set is $m$-null. The
stationary skeleton has marginal $m$, and the actual positive-time
skeleton has marginals $g_{(j+2)d}m$; their countably many sampled
states therefore avoid that set simultaneously almost surely.
Conditioning on any positive finite history preserves this null
statement. Thus the proof applies to every permitted repair,
without an assertion about avoidance by the entire continuous path.
$\square$

**Theorem 12.3 (full-prefix low predictions and actual-posterior
low predictions in their own laws).** The following hold:

$$
\begin{aligned}
\liminf_{j\to\infty}Q_{W_j}^1(3)&=0
 &&Q\text{-almost surely},\\
\liminf_{j\to\infty}Q_{W_j}^1(3)&=0
 &&R_u\text{-almost surely},\\
\liminf_{j\to\infty}R_{uW_j}^1(3)&=0
 &&R_u\text{-almost surely}
 \quad\text{for every fixed finite original }u.
\end{aligned}
\tag{12.11}
$$

All finite authentic histories, including $\varepsilon$, are
included. On one conull event in each of these laws every threshold
$0<t<c$ is crossed at a finite label index, and is crossed
infinitely often. In particular each of the respective rows has
TV distance strictly greater than $c-t$ from $Q_\emptyset^H$ at
its selected low-prediction indices, for every $H\ge1$.
The same statements hold for the continuation conditional on any
finite original label-stopped history. They do not condition away
an infinite stopping branch.

*Proof.* First work in a two-sided stationary extension of $Q$,
with shift $\theta$. Its finite-block laws are the stationary
original laws, so Kolmogorov consistency gives such an extension.
[DPCR, Theorem 8.2, (8.9)–(8.10)] proves mixing for separated
finite cylinders. Shifting two finite two-sided cylinders to
nonnegative indices proves the same limit there. Approximation
by finite cylinders, with shift-invariant approximation error,
extends mixing to its entire sigma algebra. Thus this two-sided
extension is ergodic. This construction changes no actual source.

Put

$$
h_k=\mathbb E_Q[\mathbf1_{\{Y_0=3\}}
                    \mid Y_{-k},\ldots,Y_{-1}],\qquad
h_\infty=\mathbb E_Q[\mathbf1_{\{Y_0=3\}}
                    \mid\sigma(Y_i:i<0)].
\tag{12.12}
$$

The upward conditional-expectation theorem gives
$h_k\to h_\infty$ almost surely and in $L^1$.
This is the mature martingale result of Durrett,
[*Probability: Theory and Examples*, Theorem 4.6.8][UPWARD],
with the increasing finite-past sigma fields and bounded variable
$\mathbf1_{\{Y_0=3\}}$. For
$E_n=\{Y_{-n},\ldots,Y_{-1}\ne3\}$, the tower property,
stationarity, and (12.10) give

$$
Q(E_n)=S_n>0,\qquad
\frac{\mathbb E_Q[h_\infty\mathbf1_{E_n}]}{S_n}
 =1-S_{n+1}/S_n\longrightarrow0.
\tag{12.13}
$$

For every $b>0$ it follows that $Q(h_\infty<b)>0$:
otherwise $h_\infty\ge b$ almost surely and every conditional
mean in (12.13) would be at least $b$.

One must still return from the infinite past to the full forward
prefix. Choose the versions in (12.12) supplied by the positive
finite-cylinder ratios. Stationarity then gives exactly
$Q_{W_j}^1(3)=h_j\circ\theta^j$ for $j\ge1$.
Set $G_k=\sup_{j\ge k}|h_j-h_\infty|$. These measurable bounded
functions decrease to zero almost surely. For each fixed $k$,
Birkhoff's theorem and ergodicity give

$$
\limsup_{N\to\infty}\frac1N\sum_{j=1}^N
 |h_j-h_\infty|\circ\theta^j
 \le\mathbb E_QG_k.
\tag{12.14}
$$

Indeed the finitely many $j<k$ have vanishing average and each
remaining summand is at most $G_k\circ\theta^j$. Taking the
countable intersection of these ergodic events and letting
$k\to\infty$ proves that the average in (12.14) tends to zero.
For any $t>0$, the indices with
$h_\infty\circ\theta^j<t/2$ have asymptotic frequency
$Q(h_\infty<t/2)>0$. Among them, those with
$h_j\circ\theta^j\ge t$ have density zero by (12.14), since each
would contribute more than $t/2$ to that average. Consequently
$Q_{W_j}^1(3)<t$ at a positive lower frequency. A countable
intersection over positive rational $t$ proves the first line of
(12.11), simultaneously for all real positive thresholds. This
also explains why (12.10) alone is not a full-history proof.
Birkhoff is used only in its ordinary integrable-observable form,
with precisely the stationary ergodicity supplied above.

For the actual law fix a finite original $u$. Theorem 2.1 gives
$0\le\pi_u\le M_u<\infty$, where one can take
$M_u=\|g_{2d}\|_\infty/p(u)$. The same complete future kernel
in (9.1) yields, on the full product sigma algebra,

$$
A:=R_u\ll Q,\qquad A(D)\le M_uQ(D),\qquad
\operatorname{TV}(A,Q)\le
 e(u):=\operatorname{TV}(\pi_um,m).
\tag{12.15}
$$

These follow by integrating $\mathcal K(x,D)$ against the two
initial densities. Absolute continuity of entire future laws,
not merely positivity of each finite cylinder, transfers the
first conull assertion to $A$. This proves the second line.

Here is the separate martingale argument for the third line.
Let $L=dA/dQ$, $\mathscr F_j=\sigma(Y_0,\ldots,Y_{j-1})$ and
$L_j=\mathbb E_Q[L\mid\mathscr F_j]$. These sigma fields generate
the complete output sigma algebra. Durrett's same theorem gives
$L_j\to L$ almost surely and in $L^1$. For $j\ge k$,
conditional Jensen and the triangle inequality give

$$
\begin{aligned}
V_j&:=\mathbb E_Q[|L-L_j|\mid\mathscr F_j]\\
 &\le2\mathbb E_Q[|L-L_k|\mid\mathscr F_j].
\end{aligned}
\tag{12.16}
$$

For fixed $k$ the last conditional expectation tends almost surely
to $|L-L_k|$. Taking a countable intersection in $k$, then letting
$k\to\infty$, proves $V_j\to0$ almost surely. Also $L>0$
$A$-almost surely, since $A\{L=0\}=0$, and $L_j\to L$ there.
On a prefix $w$ the conditional likelihood ratio is $L/L_j$.
For any remaining-future event $D$ this gives

$$
\begin{aligned}
|A(D\mid\mathscr F_j)-Q(D\mid\mathscr F_j)|
 &\le V_j/L_j,\\
\operatorname{TV}(R_{uW_j}^\infty,Q_{W_j}^\infty)
 &\le V_j/L_j\longrightarrow0\quad A\text{-almost surely}.
\end{aligned}
\tag{12.17}
$$

The second inequality follows either by the conditional variation
measure or by the countable finite-cylinder TV representation
used in §9. All finite prefix probabilities are positive, so the
conditional laws there are exactly the displayed $R$ and $Q$
kernels. Projecting to the next-3 event and combining with the
second line of (12.11) proves the third. This is an application
of mature conditional-expectation merging, with its needed proof
included; it does not rename $Q$ as an actual posterior and gives
no effective merging rate.

Finally, for a finite label-stopping time $T$, on
$\{T=|u|,Y_{<T}=u\}$ the original conditional future is exactly
$R_u$. Countably many such stopped words transfer the assertions
on $\{T<\infty\}$. A pre-gate service state can be included under
Definition 11.3's complete joint source-information and seed
conditions; in particular its conditional output future remains
$R_u$. Arbitrary extra source information is not covered.
For either row at its own threshold
crossing, the event that the first future label is $3$ has
probability less than $t$, while $Q_\emptyset^H$ assigns it $c$.
The defining supremum of event-TV proves the separation.
$\square$

**Proposition 12.4 (finite prefix-free witnesses of high cylinder
mass).** For every fixed original source, $0<t<c$ and $0<\delta<1$,
there are a finite $N\ge1$ and a finite prefix-free family
$\mathcal F\subset\bigcup_{j=1}^N\mathcal L^j$ such that

$$
Q_w^1(3)<t\quad(w\in\mathcal F),\qquad
\sum_{w\in\mathcal F}q(w)>1-\delta.
\tag{12.18}
$$

They may be chosen with strict margins in both inequalities.
No common $N$ for different sources, effective decay rate, deadline
or finite expected work is asserted.

*Proof.* Choose $0<t_0<t$. Under $Q$ let
$\tau_0=\inf\{j\ge1:Q_{W_j}^1(3)<t_0\}$.
Theorem 12.3 gives $Q(\tau_0<\infty)=1$. The finite words at
which this rule first hits by $N$ form a prefix-free family
$\mathcal F_N$, and their disjoint cylinder union is
$\{\tau_0\le N\}$. Its mass increases to one. Choose a finite
$N$ with mass greater than $1-\delta/2$. Every row in this finite
family is strictly below $t_0<t$ and its mass has positive slack
above $1-\delta$. There is no requirement to test equality or
non-strict exclusion at the earlier prefixes in the certificate
construction below. $\square$

**Theorem 12.5 (genuine finite acquisition certifies the witnesses
on one event).** Fix rational $0<\alpha<1$. The witnesses in
Proposition 12.4 admit the following finite rational certificate using exactly the original
finite-word suppliers of §7 and the paid retained-record setting
of §8. Declare one common validity event $\mathcal A$ with
$\mathbb P_e(\mathcal A)\ge1-\alpha$ by budgeting startup and all
predeclared acquisition/refinement packets. On that event a fair
finite search returns a prefix-free $\mathcal F$, its maximum
length $N$, the acquired normalized rows needed for it, and strict
rational tests proving (12.18) and $t<c$ whenever the requested
thresholds have the declared rational margins below. A sourcewise
finite successful certificate is meant; readiness at a future
actual gate is a separate condition.

Specifically, for real thresholds choose declared rational margins

$$
0<t_-<t<t_+<c,\qquad 0<\delta_0<\delta.
\tag{12.19}
$$

For rational $t,\delta$ one can instead test $t<c$ directly and
use any rational $0<t_-<t$, $0<\delta_0<\delta$.
The numerical procedure takes rational margins as inputs, not
an unnamed real or an exact $c$ oracle. For a packet at length
$r+1$ write its error radius as $e_s\downarrow0$ and form
$\ell_x,u_x$ by (7.8), with $t$ there replaced by $e_s$.
At this finite stage collect all nonempty $w$ of length at most
$r$ passing

$$
\ell_w>0,\qquad \frac{u_{w3}}{\ell_w}<t_-.
\tag{12.20}
$$

Keep only the words with no proper prefix also in this collected
set, obtaining $\mathcal F$. Accept a packet only if

$$
\ell_3>t_+,\qquad
\sum_{w\in\mathcal F}\ell_w>1-\delta_0.
\tag{12.21}
$$

These are all strict rational comparisons, with no test of a
stationary law unavailable to the original menu. For a rational
$t$ the first comparison may be $\ell_3>t$.

*Proof.* Use Lemma 7.2 at $H=1$, $r$ as above. Its TV event
simultaneously encloses all masses at length at most $r+1$,
including $q(3)=c$. For every accepted $w$ it gives
$Q_w^1(3)=q(w3)/q(w)\le u_{w3}/\ell_w<t_-<t$.
Pruning preserves the cylinder union: every deleted word extends
a retained accepted prefix, and finitely descending through
proper prefixes reaches one. The retained cylinders are disjoint,
so (12.21) proves their total true mass greater than
$1-\delta_0>1-\delta$. The same event gives $c\ge\ell_3>t_+>t$.
No statistical independence between these tests is used.

If full rational rows are wanted, require the finite positive
normalization guards of Proposition 7.3 and return
$\widehat Q_w^1(y)=a(wy)/a(w)$ with its generated error and
entry enclosures (7.9)–(7.11). The consistent acquired marginals
make these rows exactly normalized. Any prescribed positive
row-error tolerance is attainable by the same finite refinement;
these rows and tests are on $\mathcal A$, rather than separate
confidence events chosen after observing success.

Here is why the stated certificate search succeeds on that event.
Use Proposition 12.4 at threshold $t_-/2$ and mass error
$\delta_0/2$ to choose, for this existence argument, one finite
family with maximum length $r_0$. Refine packets at this fixed
$r_0$. All its finitely many words eventually pass (12.20), since
their true probabilities are positive and their true row entries
are less than $t_-/2$. Hence the pruned set covers a cylinder
union of mass greater than $1-\delta_0/2$. There are at most
$\sum_{j=1}^{r_0}4^j$ retained words, and on the packet event
$0\le q(w)-\ell_w\le2e_s$. Thus the sum of its lower endpoints
exceeds $1-\delta_0$ once $e_s$ is sufficiently small, even if
the particular accepted set changes with the refinement.
Also $\ell_3\to c>t_+$, and all finitely many normalization
and row-error guards eventually pass by Proposition 7.3.

To justify this after source/data selection, give the original
startup allowance $\alpha/2$. Predeclare its countably many
rational clock branches $l_i$, $i\ge1$, all positive integer
$r$, and all packet precision indices $s\ge1$. Give the packet
$(i,r,s)$ allowance $\beta_{i,r,s}=(\alpha/2)2^{-i-r-s}$.
For each valid deterministic branch, §7 generates its finite
packet lengths and enclosures at radius $e_s=2^{-s}$. With
$\mathcal E_{i,r,s}$ its Lemma 7.2 event, declare explicitly

$$
\mathcal A=\mathcal A_{\rm startup}\cap
 \bigcap_{i:\,l_i\le\tau}\ \bigcap_{r,s\ge1}\mathcal E_{i,r,s},
\qquad \mathbb P_e(\mathcal A)\ge1-\alpha.
$$

This is the intersection before choosing any packet or family,
exactly as in Theorem 8.2. Only the selected valid branch is executed.
A fair enumeration of $(r,s)$ reaches the successful finite pair
above. Each reached packet uses a finite retained original prefix
and finite reference work; the last reached pair is finite on
$\mathcal A$. The declared family of rational margins can also
be countable, with the same budgeting, if margins are selected
from acquired data. Existence for arbitrary real $t,\delta$
means the rational sandwiches (12.19), not a claim that arbitrary
real inputs have been supplied as finite names.

All actual labels, overlapping-window counters, failed tests,
reference calls, precisions, divisions, pruning comparisons,
row tables and copies remain charged as in Definitions 8.3 and
[OWGR, Definition 21.1 and Proposition 21.2]. In particular the
labels arriving during those operations remain part of the
same chronological record. The finite certificate can be
retrospective. It supplies no capture/write bandwidth, catch-up,
whole-growing-suffix assimilation, readiness deadline or lawful
output service. $\square$

**Definition 12.6 (the bounded selector and its non-hit branch).**
For a fixed finite acquired family of (12.18) that is ready before
the continuation starts, let $N=\max_{w\in\mathcal F}|w|$.
Compare the full original prefix with $\mathcal F$ and define

$$
J=\begin{cases}
j,&W_j\in\mathcal F\text{ for some }1\le j\le N,\\
N,&\text{no such prefix occurs},
\end{cases}
\qquad
I=\mathbf1_{\{\exists j\le N:W_j\in\mathcal F\}}.
\tag{12.22}
$$

Prefix-freeness makes the hit unique. Thus $J$ is a bounded
full-label stopping index; $I=0$ is an explicit non-hit result,
not a low-prediction certificate. A hit at $N$ is distinguished
from a non-hit at $N$ by $I$. Under $Q$,

$$
Q(I=1)=\sum_{w\in\mathcal F}q(w)>1-\delta,\qquad
I=1\Longrightarrow Q_{W_J}^1(3)<t.
\tag{12.23}
$$

This is a label-index rule only. Physical noncompletion of any
operation implementing it is a separate possible outcome and
produces no claimed completed row. In particular the bound $J\le N$
is not a bound on real computation, serialization or arrivals
during that work.

**Theorem 12.7 (ready-row separation, actual-law transfer and all
error terms).** Fix a deterministic original gate $T$ of
Definition 9.1, with its generated bound
$\mathbb E_e e(Y_{<T})\le\eta^+$, and use §9's one all-later-cut
comparison event $\mathcal D$ with
$\mathbb P_e(\mathcal D^c)\le\gamma$ and

$$
\operatorname{TV}(R_{T+j}^\infty,Q_{W_j}^\infty)\le\epsilon
\quad\text{for every }j\ge0\text{ on }\mathcal D.
\tag{12.24}
$$

Let $\mathcal A$, of failure at most $\alpha$, include the valid
finite witness certificate and an actually acquired normalized
ready row $\rho$ on some finite horizon $H\ge1$, with

$$
\operatorname{TV}(\rho,Q_\emptyset^H)\le\zeta.
\tag{12.25}
$$

Let $\mathsf E$ be the event of eligibility at the gate: the
finite table, $\rho$ and the selector's finite description are
actually ready then. Selection can use the stopped original
history $u$ and a pre-gate service state $V$ only when the complete
joint future hidden trajectory and fresh emission noises,
conditional on $u,V$, have their original conditional law given
$u$. In particular the output future has law $R_u$. Conditional
on $u,V=v$, any selector seed has a fixed law $\lambda_{u,v}$
independent of that entire joint future. Use the same seed law
and rule under the comparison kernel. These are exactly the
source-information and seed conditions of Definition 11.3,
without imposing its B-mask restriction on the present full-label
rule. Thresholds,
error bounds and mass allowances here are fixed; source/data
selection among countably many descriptions is covered below.

For any fixed ready valid family, (12.15) gives the more precise
conditional transfer

$$
\begin{aligned}
R_u(I=0)&\le\min\{1,\delta+e(u),M_u\delta\},\\
\mathbb P_e(\mathsf E\cap\mathcal A\cap\{I=0\})
 &\le\delta+\eta^+.
\end{aligned}
\tag{12.26}
$$

It also holds for a family chosen from the allowed pre-gate state
and history, with its own finite $N$, when its certificate has the
same $t,\delta$. Consequently

$$
\mathbb P_e(\mathsf E\cap\mathcal A\cap\mathcal D\cap\{I=1\})
 \ge\mathbb P_e(\mathsf E)-\alpha-\gamma-\delta-\eta^+.
\tag{12.27}
$$

On this common event, suppose an actual completed normalized output
$\rho_{\rm out}$ targets precisely the cut $C=T+J$, has captured,
retained and assimilated every original label through that cut,
and has separately charged, genuinely generated output error
$\operatorname{TV}(\rho_{\rm out},\rho)\le\xi_{\rm actual}$.
Then the necessary lower bounds are

$$
\begin{aligned}
\operatorname{TV}(Q_{W_J}^H,\rho_{\rm out})
 &>c-t-\zeta-\xi_{\rm actual},\\
\operatorname{TV}(R_C^H,\rho_{\rm out})
 &>c-t-\epsilon-\zeta-\xi_{\rm actual}.
\end{aligned}
\tag{12.28}
$$

They are strictly positive whenever the corresponding displayed
right side is nonnegative. In particular a current-row accuracy
claim below these bounds fails on the indicated hit event.
No assertion is made on a non-hit, on physical noncompletion, or
for an output whose actual target has moved beyond $T+J$ without
further analysis of that actual cut.

*Proof.* For a fixed family its non-hit event is a measurable
function of a finite prefix, with stationary probability less
than $\delta$. Comparing the complete laws by (12.15) changes
this probability by at most $e(u)$; domination by $M_u$ supplies
the other bound. For allowed $u,V$ and any fixed selected valid
family, the same calculation applies to its own prefix length.
Integrating an independent allowed seed preserves the bound.
In particular no assertion of independence of $J$ from the full
label sequence is needed or true here.

For clarity one cannot condition a confidence event on a successful
acquisition and substitute its data into a new-law estimate.
Instead, among possible pre-gate outputs call a family valid if
its true stationary inequalities (12.18) hold. This is a property
of that finite description for the fixed source. On $\mathcal A$
every eligible selected family is valid. Conditional on $u,V$,
restrict to eligible valid choices and apply the preceding bound
before imposing $\mathcal A$. Integrating gives at most
$\delta+\mathbb E_e e(Y_{<T})\le\delta+\eta^+$.
Intersecting also with $\mathcal A$ can only decrease this
non-hit probability. This proves the second line of (12.26).
The union bound with $\mathcal A^c,\mathcal D^c$ proves (12.27).
It does not assert a lower bound for $\mathbb P_e(\mathsf E)$.
A certificate which is never ready has no eligibility guarantee.

On a hit the first-future-label event $\{3\}$ has probability
less than $t$ under $Q_{W_J}^H$ and probability $c$ under
$Q_\emptyset^H$. Event-TV and the triangle inequality through
(12.25) and the actual output error prove the first line of
(12.28). The reverse triangle inequality through (12.24) proves
the second. An actually generated certificate $c_-\le c$ gives
the entirely certified weaker lower bound
$c_--t-\epsilon-\zeta-\xi_{\rm actual}$; the strict rational test
$c_->t+\epsilon+\zeta+\xi_{\rm actual}$ certifies its positivity.
The acquisition event can include the corresponding lower
endpoint for $c$ and all approximation certificates, so this
introduces no exact probability query.

For countably many predeclared descriptions $\kappa$, retain each
fixed gate, horizons, rational margins, finite selector and allowed
service-state rules. Give its acquisition, dynamic and non-hit
terms the common budgets $\alpha$, $\gamma_\kappa$ and
$\delta_\kappa+\eta_\kappa^+$, respectively. Intersect the
acquisition event with the dynamic events and the complements
of the valid-eligible non-hit events for every deterministic
source-valid description. Its probability is at least

$$
1-\alpha-\sum_\kappa
 (\gamma_\kappa+\delta_\kappa+\eta_\kappa^+).
\tag{12.29}
$$

On that event any eligible selected description hits and has
(12.28), subject to the actual output premises. Invalid branches
are omitted before the union bound, as in §9. This is the required
common-event way to select a gate or tolerance from acquired
data; an individual bound for a deterministic gate cannot simply
be asserted for an arbitrarily selected gate.

The Q statement in Theorem 12.3 supplies the stationary finite
witness table and its law-transfer calculation. Its separate R
statement says that the actual current posterior itself has
arbitrarily low next-3 values almost surely after every authentic
history, even without the numerical contact event. The latter
is qualitative: it supplies neither acquired exact R rows nor
a certified actual-R stopping interface. Equations (12.24)–(12.28)
are the finite acquired Q-table consumer for the actual target.
Neither use erases any of the actual execution premises.
$\square$

**Theorem 12.8 (cofinal amplification against a universal one-gap
multiple).** No finite constant $C\ge0$ can replace the timing
conditions of §§10–11 by arbitrary full-label stopping while
bounding the selected stationary row deviation by $C\beta_d$
for every original source. This failure holds both for a
pathwise uniform bound and for a uniform expectation bound over
bounded label-stopping indices. It also holds in the actual
original law for deviations of the actual current posterior from
the stationary empty-history row. The comparison can use the
arbitrarily small generated cofinal guards $b^+$ of Proposition
10.3, rather than an unacquired numerical value of $\beta_d$.

*Proof.* Use the coefficient-one original family $a=\eta=1$,
with positive integer gaps $d=L\ge1$. Each choice is a separate
original source. Once chosen, its gap, $g_L$, $c_L$ and emissions
remain fixed throughout its entire run. Markov contraction and
the source semigroup identity give

$$
\|g_L\|_\infty\le\|g_1\|_\infty<\infty,\qquad
c_L=\frac1{4(1+\|g_L\|_\infty)}\ge
c_*:=\frac1{4(1+\|g_1\|_\infty)}>0.
\tag{12.30}
$$

Proposition 10.3, with exactly its fixed-coefficient reference
services, gives a cofinal sequence of finite integers $L_n$ and
rational passing guards $b_n^+\downarrow0$, with $l=L_n=\tau$
and $\beta_{L_n}\le b_n^+$. To ensure cofinality explicitly,
require $L_n\ge n$ in its fair search. At the first stage use
guard target $1/2$; at stage $n>1$ use the rational target
$\min(2^{-n},b_{n-1}^+/2)$. Formula (10.15) tends to zero on
every such tail, so these restrictions still terminate and give
the asserted decreasing guards.
It is not an adjustment of a gap during any run, nor a claim
that any one fixed source passes every tolerance.
Here $l=L_n\le\tau$ is checked mathematically for the comparison
family. The numerical guard uses only its fixed-reference calls.
If used as an actual acquired guard, its original earned-clock
premise must still be met; no claim that startup returns exactly
$L_n$, and no exact actual coefficient or clock query, is made.

Set $t=c_*/2$ and fix $\delta=1/4$. Proposition 12.4 gives for
each source a finite prefix-free family and bounded selector
$(J_n,I_n)$ of Definition 12.6. For every $H\ge1$,

$$
\begin{aligned}
Q_n(I_n=1)&>3/4,\\
I_n=1\quad&\Longrightarrow\quad
D_{J_n,H}(W_{J_n})>c_{L_n}-t\ge c_*/2,\\
\mathbb E_{Q_n}D_{J_n,H}(W_{J_n})&>3c_*/8.
\end{aligned}
\tag{12.31}
$$

At the non-hit branch $J_n=N_n$ the deviation is still
nonnegative; that branch was retained in the expectation.
For any proposed $C$ choose $n$ with
$Cb_n^+<3c_*/8$. Then (12.31) is greater than
$Cb_n^+\ge C\beta_{L_n}$. This contradicts a universal
expectation bound; its positive-probability hit separation also
contradicts a pathwise bound when $Cb_n^+<c_*/2$.
Every finite family admits the genuine certificates of Theorem
12.5 with rational margins, but (12.31) needs no physical claim
that the selector has been executed.

For the actual-law assertion, in each of these same sources
start from the original $e$-start, and let

$$
K_n=\inf\{j\ge1:R_{W_j}^1(3)<c_*/2\}.
\tag{12.32}
$$

The $u=\varepsilon$ case of Theorem 12.3 says that $K_n$ is
finite almost surely in that actual law. Choose a finite $M_n$
with actual probability $\mathbb P_e(K_n\le M_n)>3/4$ and
use the bounded rule $\bar K_n=K_n\wedge M_n$, retaining the
non-hit flag on $\{K_n>M_n\}$. On its hit event,

$$
\operatorname{TV}(R_{W_{\bar K_n}}^H,Q_{\emptyset,n}^H)>c_*/2,
\qquad
\mathbb E_e\operatorname{TV}
 (R_{W_{\bar K_n}}^H,Q_{\emptyset,n}^H)>3c_*/8.
\tag{12.33}
$$

This is an actual-source mathematical stopping rule defined by
its true posterior, not an available exact-posterior query.
It proves the asserted actual-law failure for arbitrary
mathematical full-label stopping. The finite acquired substitute
is (12.22) with the actual stopped-law transfer and error terms
of Theorem 12.7, conditional on its genuine readiness and lawful
output premises. In particular neither (12.32) nor the finite
table invents an executor. The reference to $c_*$ is a
mathematical lower bound for the comparison family; no exact
$c_*$ or $\|g_1\|_\infty$ is added to an actual menu.

The contradiction concerns a constant uniform over timing and
over the cofinal original source family. It does not assert an
unbounded ratio for every fixed source or every acquired guard.
The deterministic-index expectation bound (10.16), its fully
independent-completion consumer, and the B-mask-adapted bounds
of §11 remain unchanged: none of their timing premises authorizes
the selection in (12.22) or (12.32). $\square$

**Definition 12.9 (source, resource and attribution boundaries).**
The additional source-specific relation is the survival edge
(12.6)–(12.9) together with its full-history and actual-posterior
consequences (12.11), high-mass finite acquired witnesses
(12.18)–(12.21), and ready-row obstruction (12.28), (12.31)–(12.33).
These are ordinary `repo-derived` paper deductions. Spectral
calculus, the positive-vector edge principle, log-convexity of
moments, conditional-expectation convergence and merging,
Birkhoff's theorem, total-variation contraction and triangle
inequalities are mature intermediates, not separate new
contributions. The primary spectral and martingale references
are [EDGE], [SPCALC] and [UPWARD]; stationary ergodicity,
complete-path transfer and the exact marked-source identity are
[DPCR, Theorem 8.2]. The crucial qualitative exterior order
bound is [DPCR, Theorem 14.3], used for this same $g_d$.
The endpoint and form correspondence is [CONTACT, Definition 115.1,
Theorems 115.2–115.3 and Definition 115.4],
including the full source summand, rather than a Friedrichs
substitution. Sections 7, 9, 10 and 11 supply respectively the
finite acquired rows/common event, the complete-future contact
comparison, the fixed-reference cofinal guard, and the retained
allowed service-state conditioning.

The reduced gap is a source-faithful obstruction to unrestricted
content-dependent ready-row reuse, together with finite acquired
certificates of substantial hit probability. It is not a
classification of all neutral histories, B-mask inevitability,
an impossibility theorem for all executors, or a negation of
§§9–11. In particular bounded label stopping and sourcewise
finite certificate search supply no actual capture/write
bandwidth, storage service, whole-growing-suffix assimilation,
catch-up, serialization, atomic output, accepted pointer
interface or finite expected execution cost. Every actual
record, failed gate, acquired row, original permission/menu,
reference call, rational precision, arithmetic step, distinct
storage/copy cost, and label arriving during work remains part
of Definitions 8.3 and 11.7 and [OWGR, §21]. No stationary
preparation, hidden-point sensor, reset, exact law query, source
delay, enlarged live gap or installed throughput is included.

The native nonempty finite ordered alpha/beta trees with no
uniform height bound, their actual rho substitutions and
literal-root operations retain the distinct source and service
contracts of [NCO, §10]. The full original AURIC consumers and
all their precise source, evaluation, cone, domain, menu and
quantum-operation assumptions remain those retained in
Definition 11.7; no native/diffusion/AURIC operational identity
is supplied. The persistent space/continuation/boundary/memory
mutual-recovery goal therefore retains its remaining actual
execution and source-bridge obligations. No fresh Lean
verification or worldwide novelty claim accompanies these
ordinary proofs.

[EDGE]: https://arxiv.org/pdf/1101.0373v2
[SPCALC]: https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf
[UPWARD]: https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf
[NCO]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATION_ORDER_ACQUISITION.md

## 追加锚（本行以下为增补区）

## 13. Same-source predictive packing and bounded classical handoff

**Definition 13.1 (fixed source, waiting windows and the handoff domain).**
Fix one source of Assumption 1.1 and Definition 12.1, including its
permitted repaired emission, before choosing any packing size or
accuracy. Its finite positive $a,\eta,d$, full complex non-Friedrichs
endpoint, maximal domain, form and source trace, original
$G=H^1\times\mathbb R$, $e$-start, first read at $2d$, subsequent
gaps $d$, four labels and conditionally fresh read noises remain
unchanged. Use exactly $p,R_u,Q_w,q$ of §§1–2 and 12. In particular
$R_u^H$ conditions on the entire original history $u$, and the first
coordinate of its future is $Y_{|u|}$ at time $(|u|+2)d$.

For a word $v\in\mathcal L^H$, let

$$
\begin{gathered}
T_3(v)=\min\{j\in\{1,\ldots,H\}:v_{j-1}=3\},
\qquad \min\varnothing=\infty,\\
E^H(L,U)=\{v\in\mathcal L^H:L<T_3(v)\le U\},
\qquad 0\le L<U\le H.
\end{gathered}
\tag{13.1}
$$

Thus the waiting index counts future reads, not physical time since
source initialization. These are finite unions of full length-$H$
cylinders. For probability rows on $\mathcal L^H$, use event-TV,
equivalently half the $\ell^1$ distance, with range $[0,1]$.

At a common cut $t$ and requested horizon $H$, an $M$-value classical
predictive handoff has a single bank of normalized rows
$\nu_{t,H,s}$, $1\le s\le M$, and may have arbitrary conditional
encoding probabilities $\lambda_u(s)$. Its marginalized reported law is

$$
\mu_u^{t,H}=\sum_{s=1}^M\lambda_u(s)\nu_{t,H,s},
\qquad \lambda_u(s)\ge0,\qquad \sum_s\lambda_u(s)=1.
\tag{13.2}
$$

The bank and encoding weights may depend on this fixed source, the
common cut/clock and the requested horizon. No compatibility between
different horizons, finite online updating rule, effective bank
construction or affordable bank storage is required for this
mathematical comparison. Decoder
randomness after receiving $s$ is already included in its normalized
row. The probabilities $\lambda_u(s)$ describe the distribution of
the transmitted configuration; the decoder receives its realized
value, not a numerical description of these probabilities.

Here $M$ bounds complete distinguishable history-bearing handoff
configurations. All such pointer values, selected banks, program and
control phases, reference replies or handles, allocation/address
choices, retained precision data and other side registers used by
decoding belong to that configuration. Separate component bounds
multiply when their combinations are distinguishable; they do not
each receive the allowance $M$. A $b$-bit complete carrier has at most
$2^b$ values. Unlimited-precision real registers have no finite value
bound merely because they have a fixed number of coordinates.
The supplied clock is common to the histories being compared.
A history-dependent completion-time signal, output length or
reference selection used by decoding is additional history-bearing
state or input, not that common clock.

The entire actual archive, all acquired rows, references, permissions
and legal menus remain retained and paid. This handoff domain allows
no additional history-bearing decoder input. Reaccess to that archive,
to history-dependent backing through a pointer, or to an external
history-dependent controller is an additional input. It remains a
legal route with its original costs, outside the stated bounded
handoff. Supplying the vector $\lambda_u$ to the decoder would also
be an additional history-bearing message; it is not free in (13.2).

**Theorem 13.2 (arbitrarily large near-disjoint actual rows at one cut).**
For each source fixed in Definition 13.1, every integer $K\ge2$ and
every positive rational $\epsilon$, there exist finite integers
$t,H\ge1$, distinct words $u_1,\ldots,u_K\in\mathcal L^t$ with
$p(u_i)>0$, and integer endpoints

$$
\begin{gathered}
L_1=0,\qquad L_i<U_i\quad(1\le i\le K),\\
U_i=L_{i+1}\quad(1\le i<K),\qquad U_K=H.
\end{gathered}
\tag{13.3}
$$

such that, with $E_i=E^H(L_i,U_i)$,

$$
R_{u_i}^H(E_i)>1-\epsilon\qquad(1\le i\le K).
\tag{13.4}
$$

The $E_i$ are disjoint first-3 waiting-time windows. Every row is
an actual full-history posterior of the original $e$-start source;
no stationary preparation or event-only posterior replaces it.

*Proof.* Choose a rational
$0<\theta<\min\{\epsilon/4,1/16\}$. Reuse precisely Theorem 12.2:
$S_n>0$, $S_n\to0$ and $S_{n+1}/S_n\to1$ for this fixed source.
For every fixed integer $L\ge0$ these imply

$$
\frac{S_{n+L}}{S_n}\longrightarrow1\quad(n\longrightarrow\infty),
\qquad
\frac{S_{n+U}}{S_n}\longrightarrow0\quad(U\longrightarrow\infty)
\quad\hbox{for each fixed }n.
\tag{13.5}
$$

The first is the product of $L$ successive ratios, with empty product
one. The second divides the supplied limit $S_{n+U}\to0$ by a fixed
positive denominator. No rate or uniformity is used.

Construct the endpoints and positive integers $n_i$ successively.
Start with $L_1=0$. Having chosen $L_i$, choose $n_i$ larger than
the preceding $n_j$ and so large that
$S_{n_i+L_i}/S_{n_i}>1-\theta$. Then choose finite $U_i>L_i$ with
$S_{n_i+U_i}/S_{n_i}<\theta$. If $i<K$, set $L_{i+1}=U_i$.
This is possible by (13.5), and finally set $H=U_K$.

For the proof only, condition the stationary comparison law $Q$ on
its first $n$ labels all lying in $D=\{0,1,B\}$, an event of
probability $S_n>0$. Denote its length-$H$ continuation law by
$C_n^H$. Directly from the same no-3 events,

$$
\begin{aligned}
C_n^H(T_3>j)&=\frac{S_{n+j}}{S_n}\quad(0\le j\le H),\\
C_{n_i}^H(E_i)
 &=\frac{S_{n_i+L_i}-S_{n_i+U_i}}{S_{n_i}}>1-2\theta.
\end{aligned}
\tag{13.6}
$$

This calculation neither asserts that the labels form a renewal
process nor conditions on a complete word. The latter distinction
is removed by the finite exact decomposition

$$
C_{n_i}^H
 =\sum_{w\in D^{n_i}}\frac{q(w)}{S_{n_i}}Q_w^H,
\qquad \sum_{w\in D^{n_i}}q(w)=S_{n_i}.
\tag{13.7}
$$

All weights are positive and sum to one. Hence some full word
$w_i\in D^{n_i}$ has $Q_{w_i}^H(E_i)>1-2\theta$; otherwise their
weighted average could not exceed that number. Retain these finitely
many words and the already chosen common windows and horizon.

To obtain actual rows at one actual cut, take $t\ge\max_i n_i$ and
the complete original words

$$
u_i(t)=B^{t-n_i}w_i.
\tag{13.8}
$$

Equation (4.4), applied to $w_i$ and each $w_iv$, gives

$$
R_{u_i(t)}^H(v)
 =\frac{\langle P^{t-n_i}g,F_{w_iv}\rangle_m}
        {\langle P^{t-n_i}g,F_{w_i}\rangle_m}
 \longrightarrow\frac{q(w_iv)}{q(w_i)}=Q_{w_i}^H(v).
\tag{13.9}
$$

The limiting denominator is strictly positive. There are only
$K4^H$ entries, so the convergence is also simultaneous in TV.
Choose one finite $t$ large enough that all these TV errors are
less than $\theta$. Then

$$
R_{u_i(t)}^H(E_i)>1-3\theta>1-\epsilon.
\tag{13.10}
$$

These masses also exceed $1/2$. Two of the words $u_i(t)$ cannot
coincide, since their one common probability row would then put
more than $1/2$ on each of two disjoint events. Each has positive
original probability by Definition 1.2. The prefix $B^{t-n_i}$ is
part of the full actual word; it is not forgotten or provided by
resetting the source. The stationary law and the event-conditioned
laws were only intermediates in obtaining (13.9). $\square$

**Theorem 13.3 (bounded-bank obstruction, including convex encoding).**
Take the actual rows and windows of Theorem 13.2 with
$0<\epsilon<1$. For every integer $M\ge1$, every common bank of
$M$ normalized rows $\nu_s$ on $\mathcal L^H$, and every choice
of probability vectors $\lambda_i$,

$$
\max_{1\le i\le K}
 \operatorname{TV}\left(R_{u_i}^H,
                 \sum_{s=1}^M\lambda_i(s)\nu_s\right)
 >1-\epsilon-\frac MK.
\tag{13.11}
$$

In particular, for every fixed source and every handoff family of
Definition 13.1 with a uniform finite bound $M$,

$$
\sup_{t\ge1}\ \sup_{u\in\mathcal L^t}\ \sup_{H\ge1}
 \operatorname{TV}(R_u^H,\mu_u^{t,H})=1.
\tag{13.12}
$$

All these histories have positive source probability. This is a
supremum over finite histories and finite requested horizons, not
an assertion that some finite query attains error one.

*Proof.* Put $b_{is}=\nu_s(E_i)$. Normalization and disjointness
give $\sum_i b_{is}\le1$ for every $s$. For
$\mu_i=\sum_s\lambda_i(s)\nu_s$, finite nonnegative summation yields

$$
\sum_{i=1}^K\mu_i(E_i)
 =\sum_{s=1}^M\sum_{i=1}^K\lambda_i(s)b_{is}
 \le\sum_{s=1}^M\sum_{i=1}^Kb_{is}\le M.
\tag{13.13}
$$

Consequently some $i$ has $\mu_i(E_i)\le M/K$. Its event-TV
distance is at least
$R_{u_i}^H(E_i)-\mu_i(E_i)>1-\epsilon-M/K$, proving (13.11).
This elementary stochastic-channel counting bound is an intermediate;
the source-specific content is the common-cut packing that makes it
applicable here. No restriction to deterministic encoders or bank
rows drawn from the actual predictive family was used.

For any $0<\delta<1$, choose a rational $0<\epsilon<\delta/2$
and an integer $K>2M/\delta$. Theorem 13.2 supplies a common
$t,H$ before the bank at that $t,H$ is compared. Equation (13.11)
then gives an actual finite-history error greater than $1-\delta$.
The universal upper bound on TV is one, proving (13.12) even when
the bank changes arbitrarily with $t,H$. Also, if error at most
$\delta$ is required on a given packing, necessarily

$$
M>K(1-\epsilon-\delta).
\tag{13.14}
$$

For randomized retention the law error used here is the more
favorable order of averaging: convexity gives
$\sum_s\lambda_i(s)\operatorname{TV}(R_{u_i}^H,\nu_s)
\ge\operatorname{TV}(R_{u_i}^H,\mu_i)$. Thus an expected
per-configuration row-error guarantee cannot evade the bound.
Even if a common source-independent random seed $Z$ is granted
to both encoder and decoder, the same conclusion holds for the
marginalized law: condition on $Z=z$, apply (13.13) to its bank
and encoding weights, and integrate. The sum of the $K$ resulting
event masses is still at most $M$, so one fixed $i$ has marginal
mass at most $M/K$. This grants independent randomization, not a
history-dependent bank selector disguised as an independent seed.
Any actual retained seed or auxiliary storage keeps its material
charge, and every history-bearing part remains within the
configuration accounting of Definition 13.1. $\square$

**Theorem 13.4 (one-event acquired retrospective packing certificates).**
Fix rational $0<\alpha<1$. In the original paid retained-record and
total fixed-reference setting of Definition 7.1 and [SRO, §§21–22],
there is one predeclared original-law event $\mathcal A$ with
$\mathbb P_e(\mathcal A)\ge1-\alpha$ on which the following holds
for every finite request

$$
K\ge2,\qquad \epsilon,\zeta\in\mathbb Q,
\qquad 0<\epsilon<1,\quad \zeta>0.
\tag{13.15}
$$

A fair finite-packet search attains a finite retrospective certificate
for some common $t,H$, distinct original histories $u_i$ of length
$t$, disjoint windows $E_i$ as in (13.3), and genuinely acquired
normalized rational rows $\widehat R_i$ and rational errors $z_i$.
It certifies, with strict rational slack,

$$
\begin{gathered}
p(u_i)>0,\qquad
\operatorname{TV}(R_{u_i}^H,\widehat R_i)\le z_i
 <\min\{\zeta,\epsilon/16\},\\
\widehat R_i(E_i)-z_i>1-\epsilon/2.
\end{gathered}
\tag{13.16}
$$

Thus the actual rows, not only stationary comparison rows, satisfy
(13.4) and the stronger bank lower bound
$1-\epsilon/2-M/K$. A finite certificate need not be ready at its
target cut $t$ or concern the actual current row when it is ready.
The attainment is sourcewise, with no uniform deadline or expected
work bound, under precisely these inherited acquisition interfaces.

*Proof: the exact actual-row supplier.* Reuse the marked identity
[DPCR, Theorem 8.2, (8.6)–(8.8), and Proposition 8.6, (8.20)].
With the notation of this volume it says

$$
q(3u)=c\,p(u),\qquad q(3)=c>0,\qquad
R_u^H(v)=\frac{q(3uv)}{q(3u)}=Q_{3u}^H(v).
\tag{13.17}
$$

Its indexing is essential: the single original $d$-transition after
the marked emission propagates $[f_3]=cg_d$ to $cPg_d=cg_{2d}$,
the actual first-read density. This is the supplied cylinder identity,
not a newly prepared stationary source or an actual reset at a
naturally observed $3$. The marker in (13.17) is included in the
acquisition word length and every count.

*Proof: the confidence event before selection.* Give startup allowance
$\alpha/2$, and let $l_j$, $j\ge1$, enumerate its possible positive
rational lower-clock outputs. Predeclare packets for every triple
$(j,N,s)$ of positive integers, using word length $N$, radius
$e_s=2^{-s}$ and allowance

$$
\beta_{j,N,s}=\frac\alpha2\,2^{-j-N-s}.
\tag{13.18}
$$

For each such deterministic input, generate the finite window count
$n_{j,N,s}$ and reference enclosures by (7.3)–(7.4); only the packet
length $N$ matters there. The termination argument of Theorem 8.2
applies at every fixed $N,s,l_j>0$. Indeed $D_n(l_j)\to1$, its
total paid reference name supplies refined lower enclosures, and
both terms of $V_{n,N}^+$ can be made arbitrarily small. All packet
sizes are determined without consulting their label values.

Let $\mathcal E_{j,N,s}$ be the Lemma 7.2 TV event for this packet,
viewed as a function of its finite initial original record. Declare

$$
\mathcal A=\mathcal A_{\rm startup}\cap
 \bigcap_{j:\,l_j\le\tau}\ \bigcap_{N,s\ge1}
                 \mathcal E_{j,N,s},
\qquad \tau=a^2d/\eta.
\tag{13.19}
$$

Here $\mathcal A_{\rm startup}$ includes finite startup termination
and validity of its returned bound. The source is fixed for this
probability statement; $\tau$ is not an exact input to the procedure.
The sum of (13.18) is $\alpha/2$, so the union bound gives
$\mathbb P_e(\mathcal A)\ge1-\alpha$. Only the selected startup
branch is executed. Invalid deterministic branches are not used in
the intersection. No independence of packets, startup, overlapping
windows or data-selected certificates is asserted or needed.

Every finite request (13.15), every finite candidate tuple and every
rational row-error test below uses these same packet events. Thus
the event is common to all of them without selecting a confidence
statement after observing a successful certificate.

*Proof: finite rational tests.* For a candidate $(t,H)$ use
$N=t+H+1$. Its acquired length-$N$ empirical probability vector
and prefix marginals $a(x)$ are exactly (7.5), on one retained
initial record. At radius $e_s$ put
$\ell_x=\max\{0,a(x)-e_s\}$ and
$b_x=\min\{1,a(x)+e_s\}$. For each candidate original word
$u_i\in\mathcal L^t$, require $\ell_{3u_i}>0$ and form

$$
\begin{gathered}
\widehat R_i(v)=\frac{a(3u_iv)}{a(3u_i)}\quad(v\in\mathcal L^H),\\
I_{i,v}=
 \left[\frac{\ell_{3u_iv}}{b_{3u_i}},
       \frac{b_{3u_iv}}{\ell_{3u_i}}\right],\\
z_i=\frac12\sum_{v\in\mathcal L^H}
 \max\left\{
 \left|\widehat R_i(v)-\frac{\ell_{3u_iv}}{b_{3u_i}}\right|,
 \left|\widehat R_i(v)-\frac{b_{3u_iv}}{\ell_{3u_i}}\right|
 \right\}.
\end{gathered}
\tag{13.20}
$$

These are Proposition 7.3's per-row construction and generated error,
restricted to the needed prefixes $3u_i$; no new estimator is used.
Prefix consistency gives $\sum_v a(3u_iv)=a(3u_i)>0$, so each
$\widehat R_i$ is exactly normalized and nonnegative. On
$\mathcal A$, the true numerator and denominator lie in their
respective intervals. Equation (13.17) therefore places every
$R_{u_i}^H(v)$ in $I_{i,v}$, and summing the endpoint errors proves
the TV bound in (13.16). The positive denominator guard also gives
the entirely acquired positive lower bound

$$
p(u_i)=\frac{q(3u_i)}{q(3)}
 \ge\frac{\ell_{3u_i}}{b_3}>0.
\tag{13.21}
$$

One can require $\ell_3>0$ as a further strict guard; it eventually
passes. The numerator is a prefix event of the same length-$N$
packet, so its error bound is simultaneous with all other tests.
The search verifies distinctness of the $u_i$, integer endpoint
ordering (13.3), and the two strict rational inequalities in
(13.16), using (13.20). An accepted certificate hence implies
the stated actual-row bounds on $\mathcal A$. In particular its
positive rational slack

$$
\sigma=\min_i\{
 \widehat R_i(E_i)-z_i-(1-\epsilon/2)\}>0
\tag{13.22}
$$

can be returned along with the rows, enclosures and packet indices.
This implies the certified strict version of (13.11), or (13.14)
with the certified mass lower bounds substituted. Bank probabilities
and convex weights need not be numerically available to certify
this universal lower bound.

*Proof: attainment with no exact-law oracle.* On the selected valid
branch, enumerate $(N,s)$ fairly, with $N\ge3$. For each packet,
there are finitely many decompositions $N=t+H+1$ with $t,H\ge1$,
finitely many distinct $K$-tuples of length-$t$ words, and finitely
many ordered integer windows within $H$. Skip a decomposition
with $K>4^t$. All its tests are finite rational arithmetic. A
diagonal enumeration that tests all $N,s\le m$ by finite stage
$m$ is one possible fair order; already computed packets may be
reused from their paid retained records.

For the termination proof only, invoke Theorem 13.2 with accuracy
$\epsilon/4$. It supplies a finite candidate tuple with actual
masses greater than $1-\epsilon/4$ and some finite
$N_0=t+H+1$. For this fixed tuple, all $q(3u_i)>0$. As the
packets at $N_0$ refine on $\mathcal A$, their prefix marginals
converge to $q$, all denominator guards pass, and Proposition 7.3
gives $z_i\to0$ and $\widehat R_i\to R_{u_i}^H$ in TV.
Consequently both tests (13.16), including the stronger mass
threshold $1-\epsilon/2$, pass with positive slack at some finite
$s$. Fair enumeration reaches that finite pair after finitely many
finite packets and comparisons. The theoretical tuple and its
exact probabilities were used to prove termination, never as
program inputs. Arbitrarily small positive $q(3u_i)$ can force
arbitrarily fine precision and long records; they do not invalidate
this fixed finite-tuple argument.

This proves simultaneous sourcewise finite attainment for all
finite requests on (13.19), in the inherited retained-record and
paid-reference model. The acquired table describes $K$ possible
full histories at the same original cut, not $K$ simultaneously
realized initial histories on one trajectory. It is acquired from
the one continuing original record through (13.17). No label is
discarded, no later segment is renamed a fresh $e$-start, and no
claim identifies its retrospective target with an unbounded
arriving current suffix. $\square$

**Definition 13.5 (retrospective acquisition and the full resource bill).**
For a reached packet of length $N$ and $n$ overlapping windows,
the indexed acquisition uses exactly $n+N-1$ original labels,
$Y_0$ through $Y_{n+N-2}$, with final read at $(n+N)d$.
Its literal full histogram has $4^N$ counters of
$\lceil\log_2(n+1)\rceil$ bits each, a $2N$-bit word buffer,
and its window, address and loop registers. Initializing that
histogram pays $4^N$ field writes; processing its windows pays
$n$ counter increments, plus buffer updates, index work and
record accesses at their actual bit widths. These quantities
are not bounded independently of the requested packing.

For a returned tuple, the rational row arrays have $K4^H$ entries;
the retained interval endpoints, generated errors and probability
guards require their own backing. Each row entry and its interval
in (13.20) pays its exact rational divisions, endpoint comparisons,
sums and bit widths. Enumerating full histories and windows pays
every reached candidate, comparison and failed test. The chosen
words themselves cost $2Kt$ bits if copied literally; windows,
cut/horizon integers, packet identifiers and refinements are also
retained finite data. A reference or shared representation can
replace a literal copy only with its actual accepted backing and
access contract. Choosing the reference is not a memory-free
operation.

Startup, all reached packet-size searches, fixed-reference calls,
precision queries and replies, rational lower defect names,
refinements and unsuccessful tests keep their charges. In the
bit model of [OWGR, Definition 21.1], reference work, reference
peak space and retained names/replies remain separate
$C_{\rm cap},M_{\rm cap},B_{\rm cap}$ coordinates. Ordinary
arithmetic is charged at actual integer/rational widths, not as
unit-cost operations on exact real source parameters. A fair
enumeration stores its indices and control state explicitly.

Nested packets may rescan one retained initial archive. Through
any actual completed acquisition cut $C$, that archive has $C$
labels and exactly $2C$ payload bits in the inherited coding,
plus its lengths, addresses, handles, acquisition/control state,
references, rows and scratch. Physical reads shared by several
packets are counted once; each rescan and distinct retained copy
is counted separately. Peak storage counts all simultaneously
live backing once and adds every distinct buffer or copy.
Total work adds all reached scans, counter work, numerical work
and certificate arithmetic, as in [OWGR, §21] and Definition 8.3.

If labels continue arriving during any reference computation,
enumeration, refinement, copying or serialization, they remain
original labels with their fixed $d$ gaps. Every such arrival,
capture/write, queued label, index update, retained payload and
subsequent rescan adds to the actual bill through $C$. An overrun
of $J$ labels adds $J$ reads and $2J$ payload bits before its
addresses, buffer/control and work costs. Previously acquired
rows, source references and lawful menus remain available at
their original costs. The certificate can use its declared
earlier finite record even when $C$ is later.

Sourcewise finite indexed attainment in Theorem 13.4 supplies
neither a processor/capture rate relative to $d$ nor a bound on
those additional arrivals. It installs no lossless capture
service, bounded queue, completion/catch-up theorem, accepted
pointer output or atomic serialization. Physical implementation
must supply each such service in its original legal domain.
Definitions 9.5 and 11.7 retain the obligations to assimilate
the whole growing suffix, acquire a row for the actual target,
generate its accumulated error and complete lawful output.

**Proposition 13.6 (the changed predictive-memory route and its limits).**
For the unchanged original source, uniformly bounded classical
handoff without extra history-bearing decoder input cannot give
any uniform error guarantee $\delta<1$ for all finite actual
histories and all finite requested horizons, even with a supplied
common clock and randomized encoding. This obstructs a lossy
bounded-handoff route in addition to the exact finite-rank route.
It does not obstruct all executors or supply a source-law
failure-probability lower bound, a fixed-$H$ impossibility, a
uniform witness/acquisition deadline or an execution rate.

*Proof and correspondence.* Sections 3–4 exclude exact finite
linear dimension and exact finite predictive cardinality by
actual word rank. Infinite exact rank alone does not rule out
arbitrarily accurate finite approximations. Theorem 13.2 adds
arbitrarily large almost disjoint actual-row packings; (13.13)
then controls the entire convex hull of every $M$-row bank, not
just equalities or deterministic state collisions. Taking $K$
large and $\epsilon$ small gives (13.12). This is the additional
approximate, randomized obstruction.

Theorem 12.2's survival limits are reused, not reproved. The
one-gap/timing results of §12 compare selected low predictions
with a specified ready comparison row, under their own eligibility
and error terms. Here the bank is arbitrary, may be redesigned
for the common source/cut/horizon, and can mix its rows using
arbitrary history-dependent encoding probabilities. The new
source-specific steps are (13.6)–(13.10), which move from the
supplied survival limits to many full actual histories at one
cut, followed by their same-row marked acquisition in
(13.17)–(13.22). No one-gap multiple or source-and-timing-uniform
estimate is restored.

For each comparison the source was fixed before $K,\epsilon$.
The finite cut and horizon may grow with them; no bound keeps
$H$ fixed while $K$ tends to infinity. The finitely witnessed
words can have arbitrarily small positive original probabilities.
Neither their existence nor a high-confidence estimate of their
conditional rows bounds how frequently a running source visits
an offending history. In particular the artificial equal weight
$1/K$ used in the counting argument is not the source distribution
of the histories. The confidence level $1-\alpha$ in (13.19)
concerns correctness and finite indexed acquisition of retrospective
certificates, not a probability of prediction failure. These
distinctions prove the stated limitations of the inference.

Archive reaccess, growing history-bearing state, restricted query
domains or a separately proved source-law risk criterion are
different possible routes. All original lawful access rights
remain. A decoder that consults the retained archive receives
additional history information, and the full system retaining
that archive has no asserted uniform finite configuration bound.
The bounded-handoff obstruction therefore is not an all-executor
impossibility or a completion theorem. It furnishes neither a
current row for an unbounded suffix nor physical capture/output
service. The native unbounded finite ordered $\alpha/\beta$ trees,
their actual $\rho$ replacements and literal-root reads, and the
original AURIC $E$, positive evaluations, accurate cone, A1–A3,
all P2/PB and original domains keep their separate correspondence
obligations. No native/diffusion/AURIC operational bridge or full
space/time/boundary/memory mutual recovery follows. $\square$

**Definition 13.7 (mathematical suppliers and attribution).**
The unchanged original source, strict positivity and full-history
meaning are §§1–2; the actual/stationary B-prefix bridge is
(4.4); the survival limits are Theorem 12.2; the marked original
conditional identity is [DPCR, §8]; and the generated finite rows,
common-event acquisition and chronological resource interfaces
are §§7–8, Theorem 12.5, [SRO, §§21–22] and [OWGR, §21].
They are suppliers, not additional results of §13. The finite
word-Hankel results [WORD] concern exact algebraic realization.
The separate five-mode source in
[Finite-start predictive memory, §§1–3][FSM] has its own actual
posterior family and approximation geometry; its shared label
alphabet gives no source correspondence to the present diffusion.
The finite binary edge-emission presentations of the repository's
`MarkedPredictiveQuotient` and the perfect quantum discrimination
bound `FiniteMemoryHistoryCapacity.finite_memory_history_capacity`
likewise do not instantiate this original source or its approximate
classical-bank claim. Source inspection is not a Lean check.

The residual-waiting viewpoint has a primary-literature antecedent
in Marzen–Crutchfield, [*Informational and Causal Architecture of
Discrete-Time Renewal Processes*, §III and Appendix A][REN].
Their renewal-source assumption makes successive interevent counts
iid, and their causal-state classification concerns that source.
No such iid gap structure or age-only predictive sufficiency is
assumed here; (13.7) keeps the full-word distinctions. Their result
is background, not a substitute proof of (13.9).
Marzen–Crutchfield's [*Circumventing the Curse of Dimensionality
in Prediction: Causal Rate-Distortion for Infinite-Order Markov
Processes*, §§II and IV][CRD] supplies the established lossy
predictive-feature and stochastic-encoding context. Its
source-weighted rate/distortion objectives are distinct from
the worst-history finite-horizon supremum in (13.12). No numerical
rate-distortion value or theorem about this diffusion is imported.

Finite conditioning, convex decomposition, normalization,
event-TV bounds, stochastic-channel counting and summable union
bounds are mature intermediate arguments. The same-source
common-cut packing, its arbitrary-bank consequence and its
acquired actual-row certificate are `repo-derived` ordinary
theory deductions with the hypotheses and limits above. They
carry no worldwide originality claim, fresh Lean verification,
implemented physical executor or finite-completion claim.

[FSM]: RECURSIVE_RELATIONAL_OBSERVATION_FINITE_START_PREDICTIVE_MEMORY.md
[REN]: https://doi.org/10.3390/e17074891
[CRD]: https://arxiv.org/abs/1412.2859

## 追加锚（本行以下为增补区）

## 14. Original-law risk at every sufficiently late deterministic cut

**Definition 14.1 (the original risk and the complete bounded handoff).**
Fix one source of Assumption 1.1 and Definition 13.1, including its
permitted Borel repair, before choosing any capacity. Retain its finite
positive $a,\eta,d$, original $G=H^1\times\mathbb R$, unit-source
normalization, full complex non-Friedrichs endpoint, maximal operator
domain, full form and source trace. The running process starts at $e$,
first reads at $2d$, and subsequently reads at gaps $d$, with all
original $0,1,3,B$ emissions and conditionally fresh noise. Write
$g=g_{2d}$, $P=T_d$ and $\mathscr F_t=\sigma(Y_0,\ldots,Y_{t-1})$.
The next label at cut $t$ remains $Y_t$ at physical time $(t+2)d$.

Use exactly Definition 13.1's normalized $M$-row banks and arbitrary
randomized encoders, with its entire configuration accounting. Thus
source, common clock and horizon may determine the bank; no online
update rule, cross-time or cross-horizon consistency, effective bank
construction or numerical representation bound is imposed. All
history-bearing pointers, bank selectors, program phases, references,
precision data, handles and side registers used by decoding count
toward the one complete bound $M$. Define the marginalized-law risk

$$
\begin{aligned}
\mathcal E_{t,H}(\nu,\lambda)
 &=\mathbb E_e\operatorname{TV}
       (R_{Y_{<t}}^H,\mu_{Y_{<t}}^{t,H})\\
 &=\sum_{u\in\mathcal L^t}p(u)
       \operatorname{TV}(R_u^H,\mu_u^{t,H}),\qquad
\mu_u^{t,H}=\sum_{s=1}^M\lambda_u(s)\nu_{t,H,s}.
\end{aligned}
\tag{14.1}
$$

The target conditions on every label in the authentic prefix $u$,
and the weights are its original $e$-start probabilities. Encoder
randomness is averaged inside the second argument of TV. This is
more favorable than averaging the loss of the realized decoded row.

The independently shared seed extension is exactly that of Theorem
13.3: a common seed $Z$ has law $\zeta$ independent of the original
source/read record, and may select banks $\nu_{t,H,s,z}$ and encoding
probabilities $\lambda_{u,z}(s)$. Its fully marginalized law is

$$
\mu_u^{t,H}
 =\int\sum_{s=1}^M\lambda_{u,z}(s)\nu_{t,H,s,z}\,\zeta(dz).
\tag{14.2}
$$

All kernels are measurable; the finite output alphabet makes the
integral coordinatewise. The independence and material charges of
Theorem 13.3 remain in force. A history-dependent selector is counted
as history-bearing configuration or additional decoder input, rather
than included in this independent seed. No additional history-bearing
decoder input is allowed in the bounded comparison.

**Theorem 14.2 (positive original-law risk at every late deterministic
cut).** For each fixed source of Definition 14.1 and every finite
integer $M\ge1$, there exist a finite horizon $H\ge1$, a number
$\varepsilon>0$ and a finite deterministic integer $t_0$ such that

$$
\inf_{\substack{\nu_{t,H,s}\text{ normalized}\\
                 \lambda_u\text{ arbitrary probability vectors}}}
 \mathbb E_e\operatorname{TV}
       (R_{Y_{<t}}^H,\mu_{Y_{<t}}^{t,H})
 \ge\varepsilon
 \qquad\text{for every deterministic }t\ge t_0.
\tag{14.3}
$$

The same $H,\varepsilon,t_0$ work for the independently shared seed
extension (14.2), even with the seed averaged before TV. The bank may
be redesigned separately at every $t,H$ for this particular source.
None of these three constants depends on that bank or its encoders.

*Proof.* Apply the existing Theorem 13.2 with $N=2M$ and packing
accuracy $1/8$. It supplies finite integers $r,H\ge1$, distinct
$u_1,\ldots,u_N\in\mathcal L^r$, and disjoint first-3 windows
$E_i\subseteq\mathcal L^H$ with

$$
p(u_i)>0,\qquad R_{u_i}^H(E_i)>7/8\quad(1\le i\le N).
\tag{14.4}
$$

Keep this one finite packing fixed. Reuse the exact marked-word
identity (13.17), supplied by [DPCR, Theorem 8.2, (8.6)–(8.8), and
Proposition 8.6, (8.20)]. Put

$$
w_i=3u_i,\qquad n=r+1,\qquad
b_i=q(w_i)=c\,p(u_i)>0,\qquad b_* =\min_{1\le i\le N}b_i>0.
\tag{14.5}
$$

Then $Q_{w_i}^H=R_{u_i}^H$. This is a stationary comparison-cylinder
identity. It does not assert an actual reset after a marker.

For every deterministic $t\ge n$ define, under the original law,

$$
\begin{gathered}
A_i(t)=\{Y_{t-n}\cdots Y_{t-1}=w_i\},\qquad
 a_i(t)=\mathbb P_e(A_i(t))>0,\\
 C_i(t)=\mathop{\rm Law}_e
       (Y_t\cdots Y_{t+H-1}\mid A_i(t)).
\end{gathered}
\tag{14.6}
$$

The events $A_i(t)$ are disjoint because the $w_i$ are distinct and
have the same length. Only this intermediate law $C_i(t)$ conditions
on a suffix alone. The prediction target in (14.1) still conditions
on the entire history.

For a finite word $w$ and $E\subseteq\mathcal L^H$ write
$F_{w,E}=\sum_{v\in E}F_{wv}$. The original future kernel gives
$0\le F_{w,E}\le F_w\le1$ as $m$-classes. At the first read in
$A_i(t)$, namely physical time $(t-n+2)d$, the unconditional original
hidden density is $P^{t-n}g$. The unchanged Markov/read contract and
word recursion therefore give the exact marginal identities

$$
\begin{aligned}
a_i(t)&=\langle P^{t-n}g,F_{w_i}\rangle_m,\\
a_i(t)C_i(t)(E_i)&=\langle P^{t-n}g,F_{w_i,E_i}\rangle_m,\\
b_iR_{u_i}^H(E_i)&=q(w_iE_i)
                  =\langle1,F_{w_i,E_i}\rangle_m.
\end{aligned}
\tag{14.7}
$$

Here $q(w_iE_i)$ denotes the finite sum $\sum_{v\in E_i}q(w_iv)$.
The earlier authentic prefix has been integrated out in these
marginals, using its original distribution; it has not been deleted
from any target conditional law or supplied by a new preparation.

Use the qualitative strong $L^2$ convergence to the constant
projection already proved in [DPCR, Theorem 8.2, proof (8.9)]. With
$\int g\,dm=1$, it gives

$$
\delta_k:=\|P^kg-1\|_2\longrightarrow0.
\tag{14.8}
$$

Its hypotheses are precisely the retained nonnegative self-adjoint
$K$ and $\ker K=\mathbb C1$. There is no spectral-gap or rate premise.
Since $m(G)=1$, the bounded functions in (14.7) have $L^2$ norm at
most one. Cauchy–Schwarz yields

$$
\begin{aligned}
|a_i(t)-b_i|&\le\delta_{t-n},\\
|a_i(t)C_i(t)(E_i)-b_iR_{u_i}^H(E_i)|
 &\le\delta_{t-n}.
\end{aligned}
\tag{14.9}
$$

Choose one finite deterministic $t_0\ge n$ such that
$\delta_{t-n}<b_*/32$ for every $t\ge t_0$. For all these $t$,
finite conditioning in (14.9) gives

$$
\begin{aligned}
a_i(t)&>b_i/2\ge b_*/2,\\
|C_i(t)(E_i)-R_{u_i}^H(E_i)|
 &\le\frac{2\delta_{t-n}}{a_i(t)}<1/8,\\
C_i(t)(E_i)&>3/4.
\end{aligned}
\tag{14.10}
$$

Indeed the numerator of the conditional difference is the second
error in (14.9) plus $(b_i-a_i(t))R_{u_i}^H(E_i)$, whose absolute
value is at most the first error. All denominators are positive.
The threshold $t_0$ was chosen before comparing any bank.

Fix any such $t$ and any bank and encoder in Definition 13.1. Let
$\mathcal U_i(t)$ be the full length-$t$ histories ending in $w_i$.
Define the conditional averages

$$
\begin{aligned}
\overline\lambda_i(s)
 &=\frac1{a_i(t)}\sum_{u\in\mathcal U_i(t)}p(u)\lambda_u(s),\\
\overline\mu_i
 &=\frac1{a_i(t)}\sum_{u\in\mathcal U_i(t)}p(u)\mu_u^{t,H}
   =\sum_{s=1}^M\overline\lambda_i(s)\nu_{t,H,s},\\
C_i(t)
 &=\frac1{a_i(t)}\sum_{u\in\mathcal U_i(t)}p(u)R_u^H.
\end{aligned}
\tag{14.11}
$$

The last equality is the full-history tower identity, coordinate by
coordinate. Each $\overline\lambda_i$ is a probability vector.
The existing joint convexity of TV, equivalently the triangle
inequality for this finite weighted half-$\ell^1$ sum, now gives

$$
\begin{aligned}
\mathcal E_{t,H}(\nu,\lambda)
 &\ge\sum_{i=1}^N a_i(t)
        \operatorname{TV}(C_i(t),\overline\mu_i)\\
 &\ge\frac{b_*}{2}\sum_{i=1}^N
        \operatorname{TV}(C_i(t),\overline\mu_i).
\end{aligned}
\tag{14.12}
$$

The first inequality discards only nonnegative loss outside the
disjoint events $A_i(t)$. Thus it retains the authentic conditional
rows and the original history weights rather than assigning equal
probabilities to the packing witnesses.

Apply exactly the counting estimate (13.13) to the averaged encoding
vectors in (14.11): normalization and disjointness imply
$\sum_i\overline\mu_i(E_i)\le M$. Consequently

$$
\begin{aligned}
\mathcal E_{t,H}(\nu,\lambda)
 &\ge\frac{b_*}{2}\sum_{i=1}^N
       [C_i(t)(E_i)-\overline\mu_i(E_i)]\\
 &>\frac{b_*}{2}\left(\frac{3N}{4}-M\right)
   =\frac{Mb_*}{4}.
\end{aligned}
\tag{14.13}
$$

Set $\varepsilon=Mb_*/4>0$. Since the $w_i$ are distinct words of
one length, $\sum_i b_i\le1$, so $\varepsilon\le1/8$. Everything
used to choose $H,\varepsilon,t_0$ depends only on the fixed source,
$M$ and the fixed witnesses from Theorem 13.2. Taking the infimum
proves (14.3).

For the extension (14.2), independence of $Z$ from the original
record leaves the conditional weights $p(u)/a_i(t)$ in (14.11)
unchanged for each seed value. Define $\overline\lambda_{i,z}$ by
that same finite average of $\lambda_{u,z}$. The averaged report is
$\overline\mu_i=\int\sum_s\overline\lambda_{i,z}(s)
\nu_{t,H,s,z}\,\zeta(dz)$. The seedwise counting argument gives

$$
\sum_{i=1}^N\overline\mu_i(E_i)
 =\int\sum_{i=1}^N\sum_{s=1}^M
     \overline\lambda_{i,z}(s)\nu_{t,H,s,z}(E_i)\,\zeta(dz)
 \le M.
\tag{14.14}
$$

Joint convexity still gives (14.12) for these fully marginalized
reports. Equations (14.10), (14.13) therefore apply unchanged.
This proves the claimed extension without interchanging infima
with limits or requiring a common bank across cuts. $\square$

**Corollary 14.3 (larger horizons, realized loss and the consumer
constraint).** Fix $M$ and $H,\varepsilon,t_0$ from Theorem 14.2.
At every deterministic $t\ge t_0$, every comparison of Definition
14.1 at any finite horizon $H'\ge H$ has marginalized-law risk at
least $\varepsilon$. Its expected realized-row loss is also at least
$\varepsilon$. For either loss random variable $L_t\in[0,1]$ and
every $0\le\gamma<\varepsilon$,

$$
\mathbb P\{L_t>\gamma\}
 \ge\frac{\varepsilon-\gamma}{1-\gamma}>0.
\tag{14.15}
$$

For marginalized-law loss this probability is under the original
record law; for realized-row loss it includes the encoder and any
independently shared seed. In particular a guarantee of loss at most
$\gamma$ with probability at least $1-\alpha$ requires
$\alpha\ge(\varepsilon-\gamma)/(1-\gamma)$ at these cuts. A complete
$b$-bit handoff is included by taking $M=2^b$.

*Proof.* Project any normalized horizon-$H'$ bank onto its first $H$
coordinates. It is still an $M$-row bank, using the same encoder;
(14.2) commutes with this finite marginalization. The target projects
to $R_u^H$, and TV contracts. Theorem 14.2 gives the larger-horizon
claim even when the original bank was independently redesigned for
$H'$. For realized output $S$, conditional convexity gives

$$
\operatorname{TV}(R_u^{H'},\mu_u^{t,H'})
 \le\int\sum_{s=1}^M\lambda_{u,z}(s)
       \operatorname{TV}(R_u^{H'},\nu_{t,H',s,z})\,\zeta(dz),
\tag{14.16}
$$

with a singleton seed in the unseeded case. Average under $p(u)$.
These are two different loss criteria, ordered as displayed rather
than identified. Finally any $[0,1]$-valued loss satisfies
$\mathbb E L_t\le\gamma+(1-\gamma)\mathbb P(L_t>\gamma)$.
Its expectation lower bound proves (14.15) and the confidence
constraint. The bit statement uses Definition 13.1's complete
configuration count. $\square$

**Definition 14.4 (scope of the risk obstruction and retained
operations).** Theorem 14.2 supplies the source-law, fixed-horizon,
every-late-deterministic-cut obstruction not supplied by Proposition
13.6. It is a constraint on the bounded handoff route to prediction
of this same original source. It does not exclude arbitrary executors.
The entire original archive, every acquired row, menu and permission,
and all paid reaccess routes remain legal. Consulting additional
history-bearing backing or a controller is additional decoder input
outside this comparison. It is not a globally forbidden operation.

The statement is a risk lower bound separately at each deterministic
cut. It gives neither one pathwise failure event at all late cuts nor
a bound for arbitrary selected stopping cuts. The horizon depends on
the source and $M$; there is no horizon asserted to work for all
capacities. At a prescribed finite $H$, the $4^H$ point-mass rows
on $\mathcal L^H$, with mathematical weights $\lambda_u(v)=R_u^H(v)$,
give an exact marginalized law. This observation concerns only the
generous comparison class: it does not supply those exact weights to
an observer or equate marginalized law with realized-row accuracy.

The stationary comparison is used only in the marked identity and
finite-block limits (14.7)–(14.10). The actual source is never
stationarily prepared, reset, delayed, controlled or supplemented
with a point sensor. No exact posterior, hidden point, original
parameter, physical clock name, effective mixing or recurrence rate,
observed witness frequency, affordable positive lower constant,
current-row output or finite physical execution is furnished by the
existence of $H,\varepsilon,t_0$. Their displayed mathematical
specification is not an acquired numerical certificate. No new
acquisition or certificate result is asserted here.

All retention, reference, computation, precision, rescan, buffering,
capture/write, output and completion costs remain those of
Definitions 8.3, 9.5, 11.7 and 13.5 and [SRO, Definition 21.1 and
Theorem 22.1]. Every label arriving during any paid work remains in
the authentic record through its actual completion. The source has
its original fixed $d$ and first-read offset; no processor rate,
affordable representation, accepted pointer output, atomic output,
finite completion or installed storage service follows from a risk
inequality. The conditional consumers in §§9–11 retain their own
source, timing, acquired-row, readiness and common-event premises.

The original native source remains the nonempty finite ordered
$\alpha/\beta$ trees without a uniform depth or size bound, with
actual $\rho$ replacements and literal root/address operations.
Its already acquired rows and service contracts are preserved.
Any AURIC use retains the same original $E$, positive evaluations,
accurate cone, A1–A3, every P2/PB and the original domains; neither
a standard matrix example nor a preselected bottom space identifies
that source. No native/diffusion/AURIC source or operation
correspondence is proved by (14.3). Exact spatial or endpoint
reconstruction, lawful current execution and full mutual recovery
of space, continuation, boundary and memory remain separate
obligations.

**Definition 14.5 (suppliers and mathematical attribution).** The
packing and its source-specific survival construction are reused
from Theorem 13.2 and Theorem 12.2. The exact original filter and
full-history conditional meaning are Theorem 2.1. The marked identity
is (13.17) and [DPCR, Theorem 8.2, (8.6)–(8.8), Proposition 8.6,
(8.20)]; the strong $L^2$ convergence in (14.8) is the supplied
proof equation [DPCR, (8.9)], not an additional convergence theorem.
Its spectral-calculus antecedent is Teschl, [*Mathematical Methods
in Quantum Mechanics*, §3.1, Theorem 3.1, (3.18)–(3.21)][SPCALC].
The full domain, form and source trace retain [DPCR, Definition 1.1]
and [CONTACT, Theorem 115.3 and Theorem 116.2].

Finite conditional averaging, joint convexity of TV and disjoint-event
counting are established intermediates. The binary finite-mixture
convexity statement is already
[TotalVariation.Convexity.total_variation_joint_convex](../../../D5/S3/TotalVariation/Convexity.lean);
its finite weighted version follows by iteration, or the same
half-$\ell^1$ triangle inequality. The required counting is exactly
(13.13), also used seedwise in Theorem 13.3. The exact word-Hankel
realization and predictive quotient suppliers [WORD, MIN] do not
alone control approximation risk. The separate finite five-mode
source [FSM, §§1–3], finite binary edge-emission presentations in
MarkedPredictiveQuotient, and the perfect quantum discrimination
bound in FiniteMemoryHistoryCapacity retain their distinct source
and loss domains; none is identified with this diffusion.

Marzen–Crutchfield, [*Circumventing the Curse of Dimensionality in
Prediction: Causal Rate-Distortion for Infinite-Order Markov
Processes*, arXiv:1412.2859v1, §§II.4 and IV](https://arxiv.org/html/1412.2859v1),
provides the primary source-weighted lossy prediction and stochastic
encoding context. Its predictive rate-distortion objectives and
conditional-law reductions are not the original diffusion theorem
(14.3); in particular (14.1) averages encoder randomness before TV,
whereas a distortion assigned to a realized predictive feature is
averaged afterwards. No value of a rate-distortion function, renewal
assumption or theorem about this original source is imported.

The additional source-specific deduction is the transfer of one
existing actual packing to fixed-length marked blocks with positive
limiting original probabilities at every late deterministic cut,
followed by full-history averaging in (14.11)–(14.14). That
composition, (14.3) and its consumer constraint are `repo-derived`
ordinary mathematical deductions under the owning source assumptions.
No new abstract packing, spectral, conditioning or counting result,
or worldwide literature-priority claim, is attached to them.

## 追加锚（本行以下为增补区）
